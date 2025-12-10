use std::{collections::HashMap, rc::Rc};

use crate::{
    ast::{File, Func, Item, Member, Param, Stmt, Type},
    checker::{
        solver::{SmtBackend, backend_from_config, check_with_solver},
        symbolic::{
            context::Context,
            execute::SymbolicExecutor,
            expr::BoolExpr,
            state::{MemoryEvent, MemoryEventKind, StoreNode, SymState},
        },
    },
    utils::{SetConfig, module_resolver::VmWorkspace},
};

#[derive(Clone)]
struct ChipSpec {
    name: String,
    populate: Func,
    eval: Func,
}

fn type_ref_id(ty: &Type) -> Option<i64> {
    match ty {
        Type::Path {
            ref_id: Some(id), ..
        } => Some(*id),
        _ => None,
    }
}

fn pick_executor(mods: &[File]) -> Result<Func, String> {
    for f in mods {
        for item in &f.items {
            if let Item::Component { name, members, .. } = item {
                let lname = name.to_ascii_lowercase();
                if !lname.contains("executor") && !lname.contains("builder") {
                    continue;
                }

                if let Some(Member::Computation(fun)) =
                    members.iter().find(|m| matches!(m, Member::Computation(_)))
                {
                    return Ok(fun.clone());
                }
            }
        }
    }
    Err("no executor component (with a Computation member) found in VM workspace".to_string())
}

fn collect_chips(mods: &[File], executor_name: &str) -> Vec<ChipSpec> {
    let mut chips = Vec::new();

    for f in mods {
        for item in &f.items {
            if let Item::Component { name, members, .. } = item {
                if name == executor_name {
                    continue;
                }

                let populate = members.iter().find_map(|m| match m {
                    Member::Computation(fun) => Some(fun.clone()),
                    _ => None,
                });
                let eval = members.iter().find_map(|m| match m {
                    Member::Constraint(fun) => Some(fun.clone()),
                    _ => None,
                });

                if let (Some(populate), Some(eval)) = (populate, eval) {
                    chips.push(ChipSpec {
                        name: name.clone(),
                        populate,
                        eval,
                    });
                }
            }
        }
    }

    chips
}

fn collect_param_nodes_by_type(state: &SymState, func: &Func) -> HashMap<i64, StoreNode> {
    let mut out = HashMap::new();
    for p in &func.params {
        if let Param::Typed { id, ty, .. } = p {
            if let (Some(vid), Some(tid)) = (id, type_ref_id(ty)) {
                if let Some(node) = state.store.get(*vid) {
                    out.insert(tid, node.clone());
                }
            }
        }
    }
    out
}

fn find_event_node(func: &Func, st: &SymState, ty_id: i64) -> Option<StoreNode> {
    for p in &func.params {
        if let Param::Typed { id, ty, .. } = p {
            if type_ref_id(ty) == Some(ty_id) {
                if let Some(vid) = id {
                    if let Some(node) = st.store.get(*vid) {
                        return Some(node.clone());
                    }
                }
            }
        }
    }

    for stmt in &func.body {
        if let Stmt::VarDecl {
            id: Some(vid), ty, ..
        } = stmt
        {
            if type_ref_id(ty) == Some(ty_id) {
                if let Some(node) = st.store.get(*vid) {
                    return Some(node.clone());
                }
            }
        }
    }
    None
}

fn build_send_receive_equalities(events: &[MemoryEvent]) -> Result<Vec<BoolExpr>, String> {
    let sends: Vec<_> = events
        .iter()
        .filter(|e| e.kind == MemoryEventKind::Send)
        .collect();
    let recvs: Vec<_> = events
        .iter()
        .filter(|e| e.kind == MemoryEventKind::Receive)
        .collect();

    if sends.len() != recvs.len() {
        return Err(format!(
            "send/receive event count mismatch ({} sends vs {} receives)",
            sends.len(),
            recvs.len()
        ));
    }

    let mut eqs = Vec::new();
    for (s, r) in sends.into_iter().zip(recvs.into_iter()) {
        eqs.push(BoolExpr::Eq(s.clk.clone(), r.clk.clone()));
        eqs.push(BoolExpr::Eq(s.addr.clone(), r.addr.clone()));
        eqs.push(BoolExpr::Eq(s.value.clone(), r.value.clone()));
    }
    Ok(eqs)
}

pub fn check_vm_workspace(
    ws: VmWorkspace,
    ctx: Rc<Context>,
    config: SetConfig,
) -> Result<(), String> {
    if ws.modules.is_empty() {
        return Err("VM workspace is empty".to_string());
    }

    let backend = backend_from_config(&config);

    let files: Vec<File> = ws.modules.iter().map(|m| m.file.clone()).collect();
    let executor_func = pick_executor(&files)?;
    let executor_name = executor_func.name.clone();

    let chips = collect_chips(&files, &executor_name);
    if chips.is_empty() {
        return Err("no chip components (with populate/eval) found in VM workspace".to_string());
    }

    let event_type_id = executor_func
        .ret
        .as_ref()
        .and_then(type_ref_id)
        .ok_or_else(|| "executor populate must return a struct event type".to_string())?;

    let exec_self_struct = executor_func.id.and_then(|fid| ctx.method_owner(fid));

    // Prepare executor initial state.
    let mut exec_state_init = SymState::new(Rc::clone(&ctx));
    exec_state_init.init_params_for_func(&executor_func, exec_self_struct);
    let base_inputs = collect_param_nodes_by_type(&exec_state_init, &executor_func);

    let exec_terms = executor_func.clone().execute(exec_state_init);
    if exec_terms.is_empty() {
        return Err("executor produced no terminal states".to_string());
    }

    for (ti, (_ret, exec_state)) in exec_terms.into_iter().enumerate() {
        let event_node =
            find_event_node(&executor_func, &exec_state, event_type_id).ok_or_else(|| {
                "executor must materialize an event (parameter or local) matching its return type"
                    .to_string()
            })?;

        for chip in chips.iter() {
            let chip_struct_id = chip.populate.id.and_then(|fid| ctx.method_owner(fid));

            // Bind populate parameters: reuse executor inputs + event.
            let mut bindings = HashMap::new();
            for p in &chip.populate.params {
                match p {
                    Param::SelfParam { .. } => {}
                    Param::Typed { name, ty, .. } => {
                        if type_ref_id(ty) == Some(event_type_id) {
                            bindings.insert(name.clone(), event_node.clone());
                        } else if let Some(tid) = type_ref_id(ty) {
                            if let Some(src) = base_inputs.get(&tid) {
                                bindings.insert(name.clone(), src.clone());
                            }
                        }
                    }
                }
            }

            let pop_state_start =
                exec_state
                    .clone()
                    .bind_params_for_func(&chip.populate, &bindings, chip_struct_id);
            let pop_terms = chip.populate.clone().execute(pop_state_start);
            if pop_terms.is_empty() {
                return Err(format!(
                    "chip `{}` populate produced no terminal states (executor path {})",
                    chip.name, ti
                ));
            }

            for (pi, (_pop_ret, pop_state)) in pop_terms.into_iter().enumerate() {
                // Try to capture row/cols from populate self.
                let cols_node = pop_state.param_node(&chip.populate, "self").cloned();

                let mut eval_bindings = HashMap::new();
                for p in &chip.eval.params {
                    match p {
                        Param::SelfParam { .. } => {
                            if let Some(cols) = cols_node.clone() {
                                eval_bindings.insert("self".to_string(), cols);
                            }
                        }
                        Param::Typed { name, ty, .. } => {
                            if type_ref_id(ty) == Some(event_type_id) {
                                eval_bindings.insert(name.clone(), event_node.clone());
                            } else if let Some(cid) = chip_struct_id {
                                if type_ref_id(ty) == Some(cid) {
                                    if let Some(cols) = cols_node.clone() {
                                        eval_bindings.insert(name.clone(), cols);
                                        continue;
                                    }
                                }
                            }
                            if let Some(tid) = type_ref_id(ty) {
                                if let Some(src) = base_inputs.get(&tid) {
                                    eval_bindings.insert(name.clone(), src.clone());
                                }
                            }
                        }
                    }
                }

                let eval_self_struct = chip.eval.id.and_then(|fid| ctx.method_owner(fid));
                let eval_state_start = pop_state.clone().bind_params_for_func(
                    &chip.eval,
                    &eval_bindings,
                    eval_self_struct,
                );
                let eval_terms = chip.eval.clone().execute(eval_state_start);
                if eval_terms.is_empty() {
                    return Err(format!(
                        "chip `{}` eval produced no terminal states (executor path {}, populate path {})",
                        chip.name, ti, pi
                    ));
                }

                for (ei, (_eval_ret, eval_state)) in eval_terms.into_iter().enumerate() {
                    let mut constraints: Vec<BoolExpr> = vec![eval_state.pc()];
                    let extra = build_send_receive_equalities(eval_state.memory_trace())?;
                    if !extra.is_empty() {
                        constraints.extend(extra);
                    }
                    let phi = BoolExpr::and(constraints);
                    let sat = check_with_solver(&phi, backend.clone())?;
                    if !sat {
                        return Err(format!(
                            "chip `{}` constraints are unsatisfiable (executor path {}, populate path {}, eval path {})",
                            chip.name, ti, pi, ei
                        ));
                    }
                }
            }
        }
    }

    Ok(())
}
