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
    let mut pairs = match DSLParser::parse(Rule::file, src) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("parse error: {}", e);
            return Err(e.into());
        }
    };
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
    Ok(Item::Import { id: None, path })
}

/// `const <type> <name> = <expr>;`
fn parse_const(p: Pair<Rule>) -> Result<Item> {
    let mut it = p.into_inner();
    let ty = parse_type(it.next().unwrap())?;
    let name = it.next().unwrap().as_str().to_string();
    let value = parse_expr(it.next().unwrap())?;
    Ok(Item::Const {
        id: None,
        ty,
        name,
        value,
    })
}

/// `Struct Name { field* }`
fn parse_struct(p: Pair<Rule>) -> Result<Item> {
    let mut it = p.into_inner();
    let name = it.next().unwrap().as_str().to_string();
    let mut fields = Vec::new();
    for f in it {
        if f.as_rule() == Rule::field {
            fields.push(parse_field(f)?);
        }
    }
    Ok(Item::Struct {
        id: None,
        name,
        fields,
    })
}

/// field := io_prefix? ident ":" type_ref ","
fn parse_field(p: Pair<Rule>) -> Result<Field> {
    let mut it = p.into_inner();

    // First token: maybe io_prefix, else ident
    let first = it.next().ok_or_else(|| anyhow!("empty field"))?;

    let (io, name_pair) = match first.as_rule() {
        Rule::io_prefix => {
            let io = parse_io_prefix(first)?;
            let name_pair = it.next().ok_or_else(|| anyhow!("missing ident"))?;
            (io, name_pair)
        }
        Rule::ident => (IOType::Input, first), // default to Input
        other => return Err(anyhow!("unexpected token in field: {:?}", other)),
    };

    if name_pair.as_rule() != Rule::ident {
        return Err(anyhow!("field name must be ident"));
    }
    let fname = name_pair.as_str().to_string();

    // Next must be type_ref
    let ty_pair = it.next().ok_or_else(|| anyhow!("missing type_ref"))?;
    if ty_pair.as_rule() != Rule::type_ref {
        return Err(anyhow!("expected type_ref after ident"));
    }
    let fty = parse_type(ty_pair)?;

    Ok(Field {
        id: None,
        io,
        name: fname,
        ty: fty,
    })
}

/// io_prefix -> IOType
fn parse_io_prefix(p: Pair<Rule>) -> Result<IOType> {
    match p.as_str() {
        "input" | "Input" => Ok(IOType::Input),
        "output" | "Output" => Ok(IOType::Output),
        _ => Err(anyhow!("unknown io_prefix")),
    }
}

/// `Component Name { member* }`
fn parse_component(p: Pair<Rule>) -> Result<Item> {
    let mut it = p.into_inner();
    let name = it.next().unwrap().as_str().to_string();
    let mut members = Vec::new();
    let mut query: Option<Query> = None;

    for m in it {
        match m.as_rule() {
            Rule::computation => {
                members.push(Member::Computation(parse_func(m.into_inner())?));
            }
            Rule::constraint => {
                members.push(Member::Constraint(parse_func(m.into_inner())?));
            }
            Rule::query_stmt => {
                if query.is_some() {
                    return Err(anyhow!("duplicate Query clause in component `{}`", name));
                }
                query = Some(parse_query_stmt(m)?);
            }
            _ => unreachable!("unexpected component member"),
        }
    }

    Ok(Item::Component {
        id: None,
        name,
        members,
        query,
    })
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
        id: None,
        name,
        params,
        ret: ret_ty,
        body,
    })
}

/// query_stmt := ^"Query" "(" query_side ";" query_side ")"
fn parse_query_stmt(p: Pair<Rule>) -> Result<Query> {
    let mut it = p.into_inner();
    let lhs = parse_query_side(it.next().ok_or_else(|| anyhow!("missing LHS in Query"))?)?;
    let rhs = parse_query_side(it.next().ok_or_else(|| anyhow!("missing RHS in Query"))?)?;
    Ok(Query { lhs, rhs })
}

/// query_side := path ("," path)* (",")?
fn parse_query_side(p: Pair<Rule>) -> Result<Vec<Vec<String>>> {
    let mut out = Vec::new();
    for n in p.into_inner() {
        match n.as_rule() {
            Rule::path => out.push(parse_path(n)),
            _ => return Err(anyhow!("unexpected rule in query_side: {:?}", n.as_rule())),
        }
    }
    Ok(out)
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
                    return Ok(Param::SelfParam { id: None });
                }
                // Case C: regular `ident : type_ref`
                let ty_pair = it
                    .next()
                    .ok_or_else(|| anyhow!("missing type after parameter '{}'", name))?;
                let ty = parse_type(ty_pair)?;
                Ok(Param::Typed {
                    id: None,
                    name: name.to_string(),
                    ty,
                    io: IOType::Input,
                })
            }
            Rule::io_prefix => {
                // Case: [io_prefix, ident, type_ref]
                let io = parse_io_prefix(first)?;
                let name_pair = it
                    .next()
                    .ok_or_else(|| anyhow!("missing ident after io_prefix in parameter"))?;
                if name_pair.as_rule() != Rule::ident {
                    return Err(anyhow!("parameter name must be ident"));
                }
                let name = name_pair.as_str().to_string();
                let ty_pair = it
                    .next()
                    .ok_or_else(|| anyhow!("missing type after parameter '{}'", name))?;
                let ty = parse_type(ty_pair)?;
                Ok(Param::Typed {
                    id: None,
                    name,
                    ty,
                    io,
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
            Ok(Param::SelfParam { id: None })
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
                Stmt::VarDecl {
                    id: None,
                    ty,
                    name,
                    init,
                }
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
                    id: None,
                    var,
                    start,
                    end,
                    body,
                }
            }
            Rule::if_stmt => parse_if_stmt(s)?,
            Rule::assert_stmt => parse_assert_stmt(s)?,
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

/// Parse an if-then-else statement:
/// if <cond_expr> <then_block> (else <else_block>)?
fn parse_if_stmt(p: Pair<Rule>) -> Result<Stmt> {
    let mut it = p.into_inner();

    // First child: condition expression.
    let cond_pair = it
        .next()
        .ok_or_else(|| anyhow!("missing condition in if-statement"))?;
    let cond = parse_expr(cond_pair)?;

    // Second child: then-block.
    let then_block_pair = it
        .next()
        .ok_or_else(|| anyhow!("missing then-block in if-statement"))?;
    let then_block = parse_block(then_block_pair)?;

    // Optional third child: else-block.
    let else_block = if let Some(else_block_pair) = it.next() {
        parse_block(else_block_pair)?
    } else {
        Vec::new()
    };

    Ok(Stmt::If {
        cond,
        then_branch: then_block,
        else_branch: else_block,
    })
}

/// Parse an assertion statement with multiple builtin variants.
fn parse_assert_stmt(s: Pair<Rule>) -> Result<Stmt> {
    // Collect expressions and optional trailing type.
    let mut exprs = Vec::new();
    let mut ty: Option<Type> = None;

    for c in s.clone().into_inner() {
        match c.as_rule() {
            Rule::expr => exprs.push(parse_expr(c)?),
            Rule::type_ref => ty = Some(parse_type(c)?),
            Rule::arg_list => {
                let mut al = Vec::new();
                for e in c.into_inner() {
                    al.push(parse_expr(e)?);
                }
                exprs = al;
            }
            _ => {}
        }
    }

    let head = s.as_str().trim_start();
    if head.starts_with("assert_range") {
        if exprs.len() != 1 {
            return Err(anyhow!("assert_range expects exactly one value"));
        }
        let ty = ty.ok_or_else(|| anyhow!("assert_range missing range type"))?;
        return Ok(Stmt::AssertRange {
            value: exprs.remove(0),
            ty,
        });
    }

    if head.starts_with("assert_zero") {
        if exprs.len() != 1 {
            return Err(anyhow!("assert_zero expects exactly one argument"));
        }
        return Ok(Stmt::AssertZero(exprs.remove(0)));
    }

    match exprs.len() {
        1 => Ok(Stmt::AssertBool(exprs.remove(0))),
        2 => {
            let rhs = exprs.pop().unwrap();
            let lhs = exprs.pop().unwrap();
            Ok(Stmt::AssertEq(lhs, rhs))
        }
        _ => Err(anyhow!("invalid assert statement")),
    }
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

    // Builtin lookup dispatch: `lookup(ByteChip, opcode, ...)`.
    if lv.head.len() == 1 && lv.head[0].eq_ignore_ascii_case("lookup") && lv.tails.is_empty() {
        if args.len() < 2 {
            return Err(anyhow!("lookup requires at least a chip and opcode"));
        }

        let mut iter = args.into_iter();
        let chip_expr = iter.next().unwrap();
        let opcode = iter.next().unwrap();
        let rest: Vec<_> = iter.collect();

        let chip_path = match chip_expr {
            Expr::Path { segments, .. } => segments,
            other => {
                return Err(anyhow!(
                    "lookup first argument must be a chip identifier path, got {:?}",
                    other
                ));
            }
        };

        return Ok(Stmt::Lookup {
            chip: chip_path,
            opcode,
            args: rest,
        });
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
        Rule::map_ty => {
            // map_ty := "map" "<" type_ref "," type_ref "," type_ref ">"
            let mut it = p.into_inner();
            let ts = parse_type(it.next().unwrap())?;
            let key = parse_type(it.next().unwrap())?;
            let val = parse_type(it.next().unwrap())?;
            Type::Map {
                timestamp: Box::new(ts),
                key: Box::new(key),
                value: Box::new(val),
            }
        }
        Rule::tuple_ty => {
            // tuple_ty := "(" ~ type_ref ~ ("," ~ type_ref)+ ~ ")"
            let elems: Vec<Type> = p
                .into_inner()
                .map(parse_type)
                .collect::<Result<Vec<_>>>()?;
            Type::Tuple(elems)
        }
        Rule::path => Type::Path {
            segments: parse_path(p),
            ref_id: None,
        },
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
                // field_tail := "." ~ (ident | int)
                let seg = t
                    .into_inner()
                    .next()
                    .ok_or_else(|| anyhow!("field_tail missing selector"))?;
                tails.push(LvTail::Field {
                    name: seg.as_str().to_string(),
                });
            }
            Rule::map_index_tail => {
                let mut inner = t.into_inner();
                let k1 = parse_expr(inner.next().unwrap())?;
                let k2 = parse_expr(inner.next().unwrap())?;
                tails.push(LvTail::MapIndex(k1, k2));
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

    Ok(LValue {
        ref_id: None,
        head,
        tails,
    })
}

/// Parse an expression with precedence:
/// `*` > `+`/`-` > `&` > `==`, all left-associative.
fn parse_expr(p: Pair<Rule>) -> Result<Expr> {
    match p.as_rule() {
        Rule::expr => {
            let mut it = p.into_inner();

            // First operand must be a postfix expression.
            let first_postfix = it.next().ok_or_else(|| anyhow!("expr missing lhs"))?;
            if first_postfix.as_rule() != Rule::postfix {
                return Err(anyhow!(
                    "expected postfix as lhs in expr, found {:?}",
                    first_postfix.as_rule()
                ));
            }
            let mut values: Vec<Expr> = vec![parse_postfix(first_postfix)?];
            let mut ops: Vec<BinOp> = Vec::new();

            // Then: (op, postfix)*.
            while let Some(op_pair) = it.next() {
                if op_pair.as_rule() != Rule::op {
                    return Err(anyhow!(
                        "expected operator in expr, found {:?} `{}`",
                        op_pair.as_rule(),
                        op_pair.as_str()
                    ));
                }

                // Map token text to BinOp.
                let bin_op = match op_pair.as_str() {
                    "==" => BinOp::Eq,
                    "!=" => BinOp::Ne,
                    "<" => BinOp::Lt,
                    "<=" => BinOp::Le,
                    ">" => BinOp::Gt,
                    ">=" => BinOp::Ge,
                    "&&" => BinOp::And,
                    "||" => BinOp::Or,
                    "*" => BinOp::Mul,
                    "+" => BinOp::Add,
                    "-" => BinOp::Sub,
                    "&" => BinOp::BitAnd,
                    other => return Err(anyhow!("unknown operator: {}", other)),
                };
                ops.push(bin_op);

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
                values.push(parse_postfix(rhs_postfix)?);
            }

            // No operators: degenerate expression with a single operand.
            if ops.is_empty() {
                debug_assert_eq!(values.len(), 1);
                Ok(values.pop().unwrap())
            } else {
                Ok(build_bin_expr_with_precedence(values, ops))
            }
        }

        // Allow re-entry from other rules if needed.
        Rule::postfix => parse_postfix(p),
        Rule::primary => parse_primary(p),

        other => Err(anyhow!(
            "unexpected rule in parse_expr dispatch: {:?}",
            other
        )),
    }
}

/// Parse a primary expression: integer, boolean, path, or parenthesized expression.
fn parse_primary(p: Pair<Rule>) -> Result<Expr> {
    let inner = p.into_inner().next().unwrap();
    Ok(match inner.as_rule() {
        Rule::int => Expr::Int(inner.as_str().parse()?),
        Rule::bool => Expr::Bool(inner.as_str() == "true"),
        Rule::path => Expr::Path {
            segments: parse_path(inner),
            ref_id: None,
        },
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
            Rule::map_index_tail => {
                let mut inner = tail.into_inner();
                let k1 = parse_expr(inner.next().unwrap())?;
                let k2 = parse_expr(inner.next().unwrap())?;
                e = Expr::MapIndex {
                    base: Box::new(e),
                    keys: vec![k1, k2],
                };
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
                e = Expr::Field {
                    base: Box::new(e),
                    name: name.as_str().to_string(),
                    ref_id: None,
                };
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

/// Return precedence of a binary operator (larger is tighter).
fn binop_precedence(op: &BinOp) -> u8 {
    match op {
        BinOp::Mul => 5,
        BinOp::Add | BinOp::Sub => 4,
        BinOp::BitAnd => 3,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => 2,
        BinOp::And => 1,
        BinOp::Or => 0,
    }
}

/// Build a left-associative binary expression tree with precedence.
/// `values` has length `n`, `ops` has length `n-1`.
fn build_bin_expr_with_precedence(mut values: Vec<Expr>, mut ops: Vec<BinOp>) -> Expr {
    assert!(!values.is_empty());
    assert!(values.len() == ops.len() + 1);

    let mut val_stack: Vec<Expr> = Vec::new();
    let mut op_stack: Vec<BinOp> = Vec::new();

    // Seed with first value.
    val_stack.push(values.remove(0));

    while !values.is_empty() {
        let v = values.remove(0);
        let op = ops.remove(0);

        // Reduce while the top operator has higher or equal precedence.
        while let Some(top) = op_stack.last().cloned() {
            if binop_precedence(&top) >= binop_precedence(&op) {
                op_stack.pop();
                let rhs = val_stack.pop().expect("rhs missing in value stack");
                let lhs = val_stack.pop().expect("lhs missing in value stack");
                val_stack.push(Expr::Binary {
                    op: top,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                });
            } else {
                break;
            }
        }

        op_stack.push(op);
        val_stack.push(v);
    }

    // Flush remaining operators.
    while let Some(op) = op_stack.pop() {
        let rhs = val_stack.pop().expect("rhs missing in final reduction");
        let lhs = val_stack.pop().expect("lhs missing in final reduction");
        val_stack.push(Expr::Binary {
            op,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        });
    }

    assert_eq!(val_stack.len(), 1);
    val_stack.pop().unwrap()
}
