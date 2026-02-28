use crate::checker::symbolic::expr::{FIELD_MODULUS, SymExpr, SymType};

/// Returns an inclusive numeric interval for a symbolic type, if it is bounded.
pub fn symtype_range(sty: &SymType) -> Option<(i128, i128)> {
    match *sty {
        SymType::Bool => Some((0, 1)),
        SymType::Uint(w) if w > 0 && w < 127 => {
            let max = 1_i128.checked_shl(w as u32)?.saturating_sub(1);
            Some((0, max))
        }
        SymType::Int(w) if w > 0 && w < 127 => {
            let hi = 1_i128.checked_shl((w - 1) as u32)?.saturating_sub(1);
            let lo = -(1_i128.checked_shl((w - 1) as u32)?);
            Some((lo, hi))
        }
        SymType::F => Some((0, FIELD_MODULUS - 1)),
        _ => None,
    }
}

/// Returns the declared bit width for integer-like symbolic types.
pub fn symtype_bit_width(sty: &SymType) -> Option<usize> {
    match *sty {
        SymType::Bool => Some(1),
        SymType::Uint(w) if w > 0 && w < 127 => Some(w),
        SymType::Int(w) if w > 0 && w < 127 => Some(w),
        _ => None,
    }
}

fn range_add(a: (i128, i128), b: (i128, i128)) -> Option<(i128, i128)> {
    a.0.checked_add(b.0)
        .and_then(|lo| a.1.checked_add(b.1).map(|hi| (lo, hi)))
}

fn range_sub(a: (i128, i128), b: (i128, i128)) -> Option<(i128, i128)> {
    a.0.checked_sub(b.1)
        .and_then(|lo| a.1.checked_sub(b.0).map(|hi| (lo, hi)))
}

fn range_mul(a: (i128, i128), b: (i128, i128)) -> Option<(i128, i128)> {
    let cands = [
        a.0.checked_mul(b.0)?,
        a.0.checked_mul(b.1)?,
        a.1.checked_mul(b.0)?,
        a.1.checked_mul(b.1)?,
    ];
    let lo = *cands.iter().min()?;
    let hi = *cands.iter().max()?;
    Some((lo, hi))
}

/// Conservative range inference for a symbolic expression using a caller-provided
/// variable hint function. The hint is consulted first for variables, then falls
/// back to the type-derived interval if available.
pub fn symexpr_range<F>(e: &SymExpr, mut hint_for: F) -> Option<(i128, i128)>
where
    F: FnMut(&str, &SymType) -> Option<(i128, i128)>,
{
    fn go<F>(e: &SymExpr, hint_for: &mut F) -> Option<(i128, i128)>
    where
        F: FnMut(&str, &SymType) -> Option<(i128, i128)>,
    {
        match e {
            SymExpr::Int(k) => Some((*k, *k)),
            SymExpr::Var(name, sty) => hint_for(name, sty).or_else(|| symtype_range(sty)),
            SymExpr::Neg(inner) => {
                let (lo, hi) = go(inner, hint_for)?;
                Some((-hi, -lo))
            }
            SymExpr::Add(xs) => {
                let mut acc = Some((0_i128, 0_i128));
                for x in xs {
                    let xr = go(x, hint_for)?;
                    acc = acc.and_then(|a| range_add(a, xr));
                }
                acc
            }
            SymExpr::Mul(xs) => {
                let mut it = xs.iter();
                let first = go(it.next()?, hint_for)?;
                let mut acc = first;
                for x in it {
                    let xr = go(x, hint_for)?;
                    acc = range_mul(acc, xr)?;
                }
                Some(acc)
            }
            SymExpr::Sub(a, b) => {
                let ra = go(a, hint_for)?;
                let rb = go(b, hint_for)?;
                range_sub(ra, rb)
            }
            SymExpr::Div(a, b) => {
                // If the divisor range includes 0 or is unknown, bail out.
                let ra = go(a, hint_for)?;
                let rb = go(b, hint_for)?;
                if rb.0 <= 0 && rb.1 >= 0 {
                    return None;
                }
                let cands = [
                    ra.0.checked_div(rb.0)?,
                    ra.0.checked_div(rb.1)?,
                    ra.1.checked_div(rb.0)?,
                    ra.1.checked_div(rb.1)?,
                ];
                let lo = *cands.iter().min()?;
                let hi = *cands.iter().max()?;
                Some((lo, hi))
            }
            SymExpr::Ite(_, t, e) => {
                let rt = go(t, hint_for)?;
                let re = go(e, hint_for)?;
                Some((std::cmp::min(rt.0, re.0), std::cmp::max(rt.1, re.1)))
            }
            SymExpr::Mod(_, m) => {
                if let SymExpr::Int(k) = **m
                    && k > 0 {
                        return Some((0, k - 1));
                    }
                None
            }
        }
    }

    go(e, &mut hint_for)
}
