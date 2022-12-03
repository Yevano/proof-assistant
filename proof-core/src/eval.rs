use std::{
    borrow::{Borrow, Cow},
    collections::hash_set::HashSet,
};

use crate::expr::{Binder, Expression, Variable};

pub fn free_variables(expr: &Expression) -> HashSet<Variable> {
    match expr {
        Expression::Hole => HashSet::new(),
        Expression::Sort(_) => HashSet::new(),
        Expression::Variable(v) => {
            let v = v.to_owned();
            let mut set = HashSet::<Variable>::new();
            set.insert(v);
            set
        }
        Expression::Binder(_, box Binder(v, t, e)) => {
            let mut set = free_variables(t);
            set.extend(free_variables(e));
            set.remove(v);
            set
        }
        Expression::Application(box e1, box e2) => {
            let mut set = free_variables(e1);
            set.extend(free_variables(e2));
            set
        }
    }
}

/// Perform the substitution t\[y := u\]
pub fn substitute(t: &Expression, y: Variable, u: &Expression) -> Expression {
    match t {
        // ?[y := u] := ?
        Expression::Hole => Expression::Hole,

        // s[y := u] := s
        Expression::Sort(i) => Expression::Sort(*i),

        // x[y := u] := if x = y then u else x
        Expression::Variable(x) => {
            if x == &y {
                u.to_owned()
            } else {
                t.to_owned()
            }
        }

        // x ≠ y, x ∉ FV(u)
        // (βx:a.b)[y := u] := βx:a[y:=u].b[y := u]
        Expression::Binder(binder_type, box Binder(x, a, b)) => {
            let a = substitute(a, y.clone(), u);

            if *x == y {
                Expression::binder(*binder_type, x.to_owned(), a, b.to_owned())
            } else {
                let fvu = free_variables(&u);
                if fvu.contains(&x) {
                    // Since x is free in u, we need to rename it.
                    let x1 = x.freshen(&fvu);
                    let b = substitute(b, x.to_owned(), &Expression::Variable(x1.clone()));
                    Expression::binder(*binder_type, x1, a, substitute(&b, y, u))
                } else {
                    Expression::binder(*binder_type, x.to_owned(), a, substitute(b, y, u))
                }
            }
        }

        // (a b)[y := u] := (a[y := u]) (b[y := u])
        Expression::Application(box a, box b) => {
            Expression::application(substitute(a, y.clone(), u), substitute(b, y, u))
        }
    }
}

#[test]
fn it_substitutes_hole() {
    assert_eq!(
        substitute(
            &Expression::Hole,
            Variable::new("x"),
            &Expression::variable("y")
        ),
        Expression::Hole
    );
}

#[test]
fn it_substitutes_sort() {
    assert_eq!(
        substitute(&Expression::sort(0), Variable::new("x"), &Expression::Hole),
        Expression::sort(0)
    );
    assert_eq!(
        substitute(&Expression::sort(1), Variable::new("x"), &Expression::Hole),
        Expression::sort(1)
    );
}

#[test]
fn it_substitutes_variable() {
    assert_eq!(
        substitute(
            &Expression::variable("x"),
            Variable::new("x"),
            &Expression::Hole
        ),
        Expression::Hole
    );
    assert_eq!(
        substitute(
            &Expression::variable("y"),
            Variable::new("x"),
            &Expression::Hole
        ),
        Expression::variable("y")
    );
}

#[test]
fn it_substitutes_product() {
    assert_eq!(
        substitute(
            &Expression::product("x".into(), "a".into(), "b".into(),),
            "x".into(),
            &"y".into()
        ),
        Expression::product("x".into(), "a".into(), "b".into(),)
    );

    assert_eq!(
        substitute(
            &Expression::product("x".into(), "x".into(), "b".into()),
            "x".into(),
            &"y".into()
        ),
        Expression::product("x".into(), "y".into(), "b".into())
    );

    assert_eq!(
        substitute(
            &Expression::product("x".into(), "a".into(), "b".into()),
            "b".into(),
            &"y".into()
        ),
        Expression::product("x".into(), "a".into(), "y".into())
    );

    assert_eq!(
        substitute(
            &Expression::product(
                "x".into(),
                "a".into(),
                Expression::application("y".into(), "x".into())
            ),
            "y".into(),
            &"x".into()
        ),
        Expression::product(
            Variable::new_with_ss("x", 1),
            "a".into(),
            Expression::application("x".into(), Expression::variable_ss("x", 1))
        )
    );
}

#[test]
fn it_substitutes_abstraction() {
    assert_eq!(
        substitute(
            &Expression::abstraction("x".into(), "a".into(), "b".into()),
            "x".into(),
            &"y".into()
        ),
        Expression::abstraction("x".into(), "a".into(), "b".into())
    );

    assert_eq!(
        substitute(
            &Expression::abstraction("x".into(), "x".into(), "b".into()),
            "x".into(),
            &"y".into()
        ),
        Expression::abstraction("x".into(), "y".into(), "b".into())
    );

    assert_eq!(
        substitute(
            &Expression::abstraction("x".into(), "a".into(), "b".into()),
            "b".into(),
            &"y".into()
        ),
        Expression::abstraction("x".into(), "a".into(), "y".into())
    );

    assert_eq!(
        substitute(
            &Expression::abstraction(
                "x".into(),
                "a".into(),
                Expression::application("y".into(), "x".into())
            ),
            "y".into(),
            &"x".into()
        ),
        Expression::abstraction(
            Variable::new_with_ss("x", 1),
            "a".into(),
            Expression::application("x".into(), Expression::variable_ss("x", 1))
        )
    );
}

#[test]
fn it_substitutes_application() {
    assert_eq!(
        substitute(
            &Expression::application("a".into(), "b".into()),
            "x".into(),
            &"y".into()
        ),
        Expression::application("a".into(), "b".into())
    );

    assert_eq!(
        substitute(
            &Expression::application("x".into(), "b".into()),
            "x".into(),
            &"y".into()
        ),
        Expression::application("y".into(), "b".into())
    );

    assert_eq!(
        substitute(
            &Expression::application("a".into(), "x".into()),
            "x".into(),
            &"y".into()
        ),
        Expression::application(Expression::variable("a"), Expression::variable("y"))
    );
}

pub fn beta_reduce_step(expression: &Expression) -> Expression {
    match expression {
        Expression::Binder(binder_type, box Binder(x, a, b)) => {
            if !is_normal_form(a) {
                Expression::binder(
                    binder_type.to_owned(),
                    x.clone(),
                    beta_reduce_step(a),
                    b.to_owned(),
                )
            } else if !is_normal_form(b) {
                Expression::binder(
                    binder_type.to_owned(),
                    x.clone(),
                    a.to_owned(),
                    beta_reduce_step(b),
                )
            } else {
                Expression::binder(
                    binder_type.to_owned(),
                    x.clone(),
                    a.to_owned(),
                    b.to_owned(),
                )
            }
        }
        Expression::Application(box Expression::Binder(_, box Binder(x, _, b)), u) => {
            substitute(b, x.to_owned(), u)
        }
        Expression::Application(f, a) => {
            if !is_normal_form(f) {
                Expression::application(beta_reduce_step(f), *a.to_owned())
            } else if !is_normal_form(a) {
                Expression::application(*f.to_owned(), beta_reduce_step(a))
            } else {
                Expression::application(*f.to_owned(), *a.to_owned())
            }
        }
        _ => expression.clone(),
    }
}

pub fn beta_reduce(expression: &Expression) -> Expression {
    let mut expression = expression.clone();
    while !is_normal_form(&expression) {
        expression = beta_reduce_step(&expression);
    }
    expression
}

pub fn is_normal_form(expression: &Expression) -> bool {
    match expression {
        Expression::Hole => true,
        Expression::Sort(_) => true,
        Expression::Variable(_) => true,
        Expression::Binder(_, box Binder(_, a, b)) => is_normal_form(&a) && is_normal_form(&b),
        Expression::Application(box Expression::Binder(_, _), _) => false,
        Expression::Application(a, b) => is_normal_form(&a) && is_normal_form(&b),
    }
}

pub fn get_compatible_bound_variable(
    x1: &Variable,
    y1: &Expression,
    x2: &Variable,
    y2: &Expression,
) -> Variable {
    let combined_free_variables: HashSet<Variable> = free_variables(y1)
        .union(&free_variables(y2))
        .cloned()
        .collect();
    if !combined_free_variables.contains(x1) {
        x1.clone()
    } else if !combined_free_variables.contains(x2) {
        x2.clone()
    } else {
        x1.freshen(&combined_free_variables)
    }
}

pub fn adapt_binder_variables(binder1: &Binder, binder2: &Binder) -> (Binder, Binder) {
    let binders: (&Binder, &Binder) = (binder1, binder2);
    let (
        Binder(binder1_variable, binder1_variable_type, binder1_body),
        Binder(binder2_variable, binder2_variable_type, binder2_body),
    ) = binders;
    {
        let compatible_variable: Cow<'_, Variable> = Cow::Owned(get_compatible_bound_variable(
            binder1_variable,
            binder1_body,
            binder2_variable,
            binder2_body,
        ));

        let binder1_body = substitute(binder1_body, binder1_variable.clone(), &Expression::Variable(compatible_variable.clone().into_owned()));
        let binder2_body = substitute(binder2_body, binder2_variable.clone(), &Expression::Variable(compatible_variable.clone().into_owned()));

        (Binder(compatible_variable.clone().into_owned(), binder1_variable_type.clone(), binder1_body), Binder(compatible_variable.clone().into_owned(), binder2_variable_type.clone(), binder2_body))
    }
}

/// Test for α-equivalence of two expressions.
pub fn alpha_eq(a: &Expression, b: &Expression) -> bool {
    match (a, b) {
        (Expression::Hole, Expression::Hole) => true,
        (Expression::Sort(i), Expression::Sort(j)) => i == j,
        (Expression::Variable(x), Expression::Variable(y)) => x == y,
        (Expression::Application(f, x), Expression::Application(g, y)) => {
            alpha_eq(f.borrow(), g.borrow()) && alpha_eq(x.borrow(), y.borrow())
        }

        (
            Expression::Binder(a_binder_type, a_binder),
            Expression::Binder(b_binder_type, b_binder),
        ) => {
            if a_binder_type != b_binder_type {
                return false;
            }

            let (box Binder(a_x, a_x_type, a_body), box Binder(b_x, b_x_type, b_body)) =
                (a_binder, b_binder);

            if !alpha_eq(&a_x_type, &b_x_type) {
                return false;
            }

            let fresh_variable = get_compatible_bound_variable(&a_x, &a_body, &b_x, &b_body);

            let a_body = substitute(
                &a_body,
                a_x.clone(),
                &Expression::Variable(fresh_variable.clone()),
            );
            let b_body = substitute(&b_body, b_x.clone(), &Expression::Variable(fresh_variable));
            alpha_eq(&a_body, &b_body)
        }
        _ => false,
    }
}

/// A convenience function for testing if two expressions normalize to α-equivalent expressions.
pub fn eq_after_beta_reduction(a: &Expression, b: &Expression) -> bool {
    alpha_eq(&beta_reduce(a), &beta_reduce(b))
}
