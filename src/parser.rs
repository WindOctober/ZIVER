use crate::ast::*;
use anyhow::{Result, anyhow};
use pest::{
    Parser,
    iterators::{Pair, Pairs},
};
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "dsl.pest"]
pub struct DSLParser;

/// Parse an entire source file into an AST.
pub fn parse_file(src: &str) -> Result<File> {
    // pest returns a single top-level `file` pair; we must descend into its children.
    let mut pairs = DSLParser::parse(Rule::file, src)?;
    let root = pairs
        .next()
        .ok_or_else(|| anyhow!("parser produced no root `file` node"))?;

    let mut items = Vec::new();
    for p in root.into_inner() {
        if p.as_rule() == Rule::item {
            items.push(parse_item(p)?);
        }
    }
    Ok(File { items })
}

/// Dispatch a top-level item by its concrete rule.
fn parse_item(p: Pair<Rule>) -> Result<Item> {
    let inner = p.into_inner().next().unwrap();
    Ok(match inner.as_rule() {
        Rule::import => parse_import(inner)?,
        Rule::const_decl => parse_const(inner)?,
        Rule::struct_decl => parse_struct(inner)?,
        Rule::component => parse_component(inner)?,
        _ => unreachable!("unexpected item rule"),
    })
}

/// `import path;`
fn parse_import(p: Pair<Rule>) -> Result<Item> {
    let mut it = p.into_inner();
    let path = parse_path(it.next().unwrap());
    Ok(Item::Import { path })
}

/// `const <type> <name> = <expr>;`
fn parse_const(p: Pair<Rule>) -> Result<Item> {
    let mut it = p.into_inner();
    let ty = parse_type(it.next().unwrap())?;
    let name = it.next().unwrap().as_str().to_string();
    let value = parse_expr(it.next().unwrap())?;
    Ok(Item::Const { ty, name, value })
}

/// `Struct Name { field: Type, ... }`
fn parse_struct(p: Pair<Rule>) -> Result<Item> {
    let mut it = p.into_inner();
    let name = it.next().unwrap().as_str().to_string();
    let mut fields = Vec::new();
    for f in it {
        if f.as_rule() == Rule::field {
            let mut fi = f.into_inner();
            let fname = fi.next().unwrap().as_str().to_string();
            let fty = parse_type(fi.next().unwrap())?;
            fields.push(Field {
                name: fname,
                ty: fty,
            });
        }
    }
    Ok(Item::Struct { name, fields })
}

/// `Component Name { member* }`
fn parse_component(p: Pair<Rule>) -> Result<Item> {
    let mut it = p.into_inner();
    let name = it.next().unwrap().as_str().to_string();
    let mut members = Vec::new();
    for m in it {
        members.push(match m.as_rule() {
            Rule::computation => Member::Computation(parse_func(m.into_inner())?),
            Rule::constraint => Member::Constraint(parse_func(m.into_inner())?),
            _ => unreachable!("unexpected component member"),
        });
    }
    Ok(Item::Component { name, members })
}

/// Parse a function-like member: signature + block.
fn parse_func(mut it: Pairs<Rule>) -> Result<Func> {
    // func_sig := ident "(" param_list? ")" ( "->" type_ref )?
    let sig = it.next().unwrap();
    assert_eq!(sig.as_rule(), Rule::func_sig);

    let mut s = sig.into_inner();
    let name = s.next().unwrap().as_str().to_string();

    // Optional: param_list, then optional: return type.
    let mut params = Vec::new();
    let mut ret_ty: Option<Type> = None;

    if let Some(next) = s.next() {
        match next.as_rule() {
            Rule::param_list => {
                // Collect parameters.
                for p in next.into_inner() {
                    params.push(parse_param(p)?);
                }
                // Check if a return type follows.
                if let Some(ret) = s.next() {
                    ret_ty = Some(parse_type(ret)?);
                }
            }
            Rule::type_ref => {
                // No parameters, directly a return type.
                ret_ty = Some(parse_type(next)?);
            }
            _ => unreachable!("unexpected token in func_sig"),
        }
    }

    // Parse function body block.
    let body_pair = it.next().unwrap();
    let body = parse_block(body_pair)?;

    Ok(Func {
        name,
        params,
        ret: ret_ty,
        body,
    })
}

/// Parse a single parameter: either `self` (literal) or `ident : type`.
fn parse_param(p: Pair<Rule>) -> Result<Param> {
    // `param = { "self" | ident ~ ":" ~ type_ref }`
    // When matched via the literal `"self"` alternative, `p.into_inner()` is empty.
    // When matched via `ident ~ ":" ~ type_ref`, children are [ident, type_ref].
    let mut it = p.clone().into_inner();

    if let Some(first) = it.next() {
        match first.as_rule() {
            Rule::ident => {
                let name = first.as_str();
                if name == "self" {
                    // Case B: grammar reduced `self` as an identifier (edge but possible in some grammars)
                    return Ok(Param::SelfParam);
                }
                // Case C: regular `ident : type_ref`
                let ty_pair = it
                    .next()
                    .ok_or_else(|| anyhow!("missing type after parameter '{}'", name))?;
                let ty = parse_type(ty_pair)?;
                Ok(Param::Typed {
                    name: name.to_string(),
                    ty,
                })
            }
            _ => Err(anyhow!(
                "invalid parameter: unexpected token {:?}",
                first.as_rule()
            )),
        }
    } else {
        // No children: accept as literal `self`
        if p.as_str() == "self" {
            Ok(Param::SelfParam)
        } else {
            Err(anyhow!(
                "invalid parameter: expected `self` or `ident : type`"
            ))
        }
    }
}

/// Parse a block `{ stmt* }` into a vector of statements.
fn parse_block(p: Pair<Rule>) -> Result<Vec<Stmt>> {
    let mut out = Vec::new();
    for s in p.into_inner() {
        out.push(match s.as_rule() {
            Rule::var_decl => {
                // var_decl := type_ref ident "=" expr ";"
                let mut it = s.into_inner();
                let ty = parse_type(it.next().unwrap())?;
                let name = it.next().unwrap().as_str().to_string();
                let init = parse_expr(it.next().unwrap())?;
                Stmt::VarDecl { ty, name, init }
            }
            Rule::assign => {
                // assign := lvalue "=" expr ";"
                let mut it = s.into_inner();
                let lv = parse_lvalue(it.next().unwrap())?;
                let rhs = parse_expr(it.next().unwrap())?;
                Stmt::Assign {
                    target: lv,
                    value: rhs,
                }
            }
            Rule::and_assign => {
                // and_assign := lvalue "&=" expr ";"
                let mut it = s.into_inner();
                let lv = parse_lvalue(it.next().unwrap())?;
                let rhs = parse_expr(it.next().unwrap())?;
                Stmt::AndAssign {
                    target: lv,
                    value: rhs,
                }
            }
            Rule::for_loop => {
                // for_loop := "for" ident "in" range block
                let mut it = s.into_inner();
                let var = it.next().unwrap().as_str().to_string(); // ident
                let range = it.next().unwrap(); // range
                let (start, end) = {
                    let mut ri = range.into_inner();
                    let start = parse_expr(ri.next().unwrap())?;
                    let end = parse_expr(ri.next().unwrap())?;
                    (start, end)
                };
                let body = parse_block(it.next().unwrap())?;
                Stmt::For {
                    var,
                    start,
                    end,
                    body,
                }
            }
            Rule::assert_stmt => {
                // assert_bool(expr);  |  assert_eq(expr, expr);
                // We inspect the number of `expr` children to disambiguate.
                let mut exprs = Vec::new();
                for c in s.clone().into_inner() {
                    if c.as_rule() == Rule::expr {
                        exprs.push(parse_expr(c)?);
                    } else if c.as_rule() == Rule::arg_list {
                        // This branch is not used by current `assert_stmt` rule,
                        // but kept for robustness in case of future refactoring.
                        let mut al = Vec::new();
                        for e in c.into_inner() {
                            al.push(parse_expr(e)?);
                        }
                        exprs = al;
                    }
                }
                match exprs.len() {
                    1 => Stmt::AssertBool(exprs.remove(0)),
                    2 => {
                        let rhs = exprs.pop().unwrap();
                        let lhs = exprs.pop().unwrap();
                        Stmt::AssertEq(lhs, rhs)
                    }
                    _ => return Err(anyhow!("invalid assert statement")),
                }
            }
            Rule::call_stmt => {
                // call_stmt := call ";"
                let call = s.into_inner().next().unwrap();
                parse_call_stmt(call)?
            }
            Rule::return_stmt => {
                // return_stmt := "return" expr ";"
                let e = parse_expr(s.into_inner().next().unwrap())?;
                Stmt::Return(e)
            }
            _ => unreachable!("unexpected statement"),
        });
    }
    Ok(out)
}

/// Parse a call statement `lvalue call_tail`.
fn parse_call_stmt(call: Pair<Rule>) -> Result<Stmt> {
    let mut it = call.into_inner();
    let lv = parse_lvalue(it.next().unwrap())?;

    let mut args = Vec::new();
    // call_tail := "(" arg_list? ")"
    if let Some(tail) = it.next() {
        if tail.as_rule() == Rule::call_tail {
            if let Some(maybe_args) = tail.into_inner().next() {
                if maybe_args.as_rule() == Rule::arg_list {
                    for e in maybe_args.into_inner() {
                        args.push(parse_expr(e)?);
                    }
                }
            }
        } else {
            return Err(anyhow!("expected call_tail"));
        }
    } else {
        return Err(anyhow!("missing call_tail"));
    }

    Ok(Stmt::Call { callee: lv, args })
}

/// Parse a type: either an array type or a path.
fn parse_type(p: Pair<Rule>) -> Result<Type> {
    Ok(match p.as_rule() {
        Rule::type_ref => parse_type(p.into_inner().next().unwrap())?,
        Rule::array_ty => {
            // array_ty := "[" type_ref ";" expr "]"
            let mut it = p.into_inner();
            let inner = parse_type(it.next().unwrap())?;
            let size = parse_expr(it.next().unwrap())?;
            Type::Array(Box::new(inner), size)
        }
        Rule::path => Type::Path(parse_path(p)),
        _ => unreachable!("unexpected type rule"),
    })
}

/// Convert a `path` into a vector of segments.
fn parse_path(p: Pair<Rule>) -> Vec<String> {
    p.into_inner().map(|s| s.as_str().to_string()).collect()
}

/// Parse an lvalue: `path ( field_tail | index_tail )*`
/// Grammar-aligned implementation that assumes named tails only.
/// This function will error if an unexpected tail appears, enforcing grammar consistency.
fn parse_lvalue(p: Pair<Rule>) -> Result<LValue> {
    let mut it = p.into_inner();
    let head = parse_path(
        it.next()
            .ok_or_else(|| anyhow!("lvalue missing head path"))?,
    );
    let mut tails = Vec::new();

    for t in it {
        match t.as_rule() {
            Rule::field_tail => {
                // field_tail := "." ~ ident
                let seg = t
                    .into_inner()
                    .next()
                    .ok_or_else(|| anyhow!("field_tail missing ident"))?;
                tails.push(LvTail::Field(seg.as_str().to_string()));
            }
            Rule::index_tail => {
                // index_tail := "[" ~ expr ~ "]"
                let idx = t
                    .into_inner()
                    .next()
                    .ok_or_else(|| anyhow!("index_tail missing expr"))?;
                tails.push(LvTail::Index(parse_expr(idx)?));
            }
            // Only named tails are valid under the current grammar.
            other => {
                return Err(anyhow!(
                    "unexpected lvalue tail: {:?} with text `{}`",
                    other,
                    t.as_str()
                ));
            }
        }
    }

    Ok(LValue { head, tails })
}

/// Parse an expression in the simplified left-associative form:
/// `expr := postfix ( op ~ postfix )*`
/// The operator `op` is a visible rule (non-silent) to ensure it appears in the parse tree.
fn parse_expr(p: Pair<Rule>) -> Result<Expr> {
    match p.as_rule() {
        Rule::expr => {
            let mut it = p.into_inner();
            let mut left = parse_postfix(it.next().ok_or_else(|| anyhow!("expr missing lhs"))?)?;

            while let Some(op_pair) = it.next() {
                if op_pair.as_rule() != Rule::op {
                    return Err(anyhow!(
                        "expected operator, found {:?} `{}`",
                        op_pair.as_rule(),
                        op_pair.as_str()
                    ));
                }
                let op = match op_pair.as_str() {
                    "==" => BinOp::Eq,
                    "*" => BinOp::Mul,
                    "+" => BinOp::Add,
                    "-" => BinOp::Sub,
                    "&" => BinOp::BitAnd,
                    other => return Err(anyhow!("unknown operator: {}", other)),
                };

                let rhs_postfix = it.next().ok_or_else(|| {
                    anyhow!("expr missing rhs after operator `{}`", op_pair.as_str())
                })?;
                if rhs_postfix.as_rule() != Rule::postfix {
                    return Err(anyhow!(
                        "expected postfix after operator `{}`, found {:?}",
                        op_pair.as_str(),
                        rhs_postfix.as_rule()
                    ));
                }
                let rhs = parse_postfix(rhs_postfix)?;
                left = Expr::Binary {
                    op,
                    lhs: Box::new(left),
                    rhs: Box::new(rhs),
                };
            }

            Ok(left)
        }
        Rule::postfix => parse_postfix(p),
        Rule::primary => parse_primary(p),
        other => Err(anyhow!("unexpected rule in parse_expr: {:?}", other)),
    }
}
/// Parse a primary expression: integer, boolean, path, or parenthesized expression.
fn parse_primary(p: Pair<Rule>) -> Result<Expr> {
    let inner = p.into_inner().next().unwrap();
    Ok(match inner.as_rule() {
        Rule::int => Expr::Int(inner.as_str().parse()?),
        Rule::bool => Expr::Bool(inner.as_str() == "true"),
        Rule::path => Expr::Path(parse_path(inner)),
        Rule::expr => Expr::Paren(Box::new(parse_expr(inner)?)),
        _ => unreachable!("unexpected primary"),
    })
}

/// Parse a postfix expression: `primary ( call_tail | index_tail | field_tail )*`
/// This function strictly expects named tails, matching the grammar one-to-one.
fn parse_postfix(p: Pair<Rule>) -> Result<Expr> {
    let mut it = p.into_inner();
    let mut e = parse_primary(
        it.next()
            .ok_or_else(|| anyhow!("postfix missing primary"))?,
    )?;

    for tail in it {
        match tail.as_rule() {
            Rule::call_tail => {
                // call_tail := "(" arg_list? ")"
                let mut args = Vec::new();
                // If there is an `arg_list`, it will appear as the single child of call_tail.
                if let Some(maybe_args) = tail.into_inner().next() {
                    if maybe_args.as_rule() != Rule::arg_list {
                        return Err(anyhow!("malformed call_tail: expected arg_list"));
                    }
                    for a in maybe_args.into_inner() {
                        args.push(parse_expr(a)?);
                    }
                }
                e = Expr::Call(Box::new(e), args);
            }
            Rule::index_tail => {
                // index_tail := "[" expr "]"
                let idx_expr = tail
                    .into_inner()
                    .next()
                    .ok_or_else(|| anyhow!("index_tail missing expr"))?;
                e = Expr::Index(Box::new(e), Box::new(parse_expr(idx_expr)?));
            }
            Rule::field_tail => {
                // field_tail := "." ident
                let name = tail
                    .into_inner()
                    .next()
                    .ok_or_else(|| anyhow!("field_tail missing ident"))?;
                e = Expr::Field(Box::new(e), name.as_str().to_string());
            }
            other => {
                return Err(anyhow!(
                    "unexpected postfix tail: {:?} with text `{}`",
                    other,
                    tail.as_str()
                ));
            }
        }
    }

    Ok(e)
}
