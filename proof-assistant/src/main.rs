use std::{borrow::Cow};

use proof_core::{
    expr::{Expression, Variable},
    goals::{find_goals, Constraint, TypeConstraint},
    result::ResultExt,
    types::resolve_type,
    types::Context,
};

fn main() {
    
}

fn type_check_test_2() {
    /* let t = Expression::product(
        "α".into(), Expression::sort(0),
        Expression::abstraction()
    ) */
}

fn type_check_test() {
    let prop = &Expression::sort(0);
    let bottom = &Expression::product("α".into(), prop.clone(), "α".into());
    let bottom_type = &resolve_type(bottom, &Context::Empty).unwrap_chain();
    println!("⊥ : {} = {}", bottom_type, bottom);
    let id = &Expression::abstraction(
        "α".into(),
        prop.clone(),
        Expression::abstraction("x".into(), "α".into(), "x".into()),
    );
    let id_type = &resolve_type(id, &Context::Empty).unwrap_chain();
    println!("id : {} = {}", id_type, id);
    let eq = &Expression::abstraction(
        "α".into(),
        prop.clone(),
        Expression::abstraction(
            "x".into(),
            "α".into(),
            Expression::abstraction(
                "y".into(),
                "α".into(),
                Expression::product(
                    "p".into(),
                    Expression::arrow("α".into(), prop.clone()),
                    Expression::arrow(
                        Expression::application("p".into(), "x".into()),
                        Expression::application("p".into(), "y".into()),
                    ),
                ),
            ),
        ),
    );
    let eq_type = &resolve_type(eq, &Context::Empty).unwrap_chain();
    println!("eq : {} = {}", eq_type, eq);
    let refl = Expression::abstraction(
        "α".into(),
        prop.clone(),
        Expression::abstraction(
            "x".into(),
            "α".into(),
            Expression::abstraction(
                "p".into(),
                Expression::arrow("α".into(), prop.clone()),
                Expression::application(
                    id.clone(),
                    Expression::application("p".into(), "x".into()),
                ),
            ),
        ),
    );
    let refl_type = &resolve_type(&refl, &Context::Empty).unwrap_chain();
    println!("refl : {} = {}", refl_type, refl);

    let refl_id =
        Expression::application(Expression::application(refl, id_type.clone()), id.clone());
    println!("refl_id = {}", refl_id);
    let refl_id_type = resolve_type(&refl_id, &Context::Empty).unwrap_chain();
    println!("refl id_type id : {} = {}", refl_id_type, refl_id,);
}

fn goal_test() {
    let fun_id = Expression::abstraction(
        "α".into(),
        Expression::sort(0),
        Expression::abstraction("x".into(), "α".into(), "x".into()),
    );
    let fun_false = Expression::abstraction(
        "α".into(),
        Expression::sort(0),
        Expression::abstraction(
            "x".into(),
            "α".into(),
            Expression::abstraction("y".into(), "α".into(), "y".into()),
        ),
    );
    let fun_true = Expression::abstraction(
        "α".into(),
        Expression::sort(0),
        Expression::abstraction(
            "x".into(),
            "α".into(),
            Expression::abstraction("y".into(), "α".into(), "x".into()),
        ),
    );

    let ctx = Context::Empty;
    let type_id = resolve_type(&fun_id, &ctx).unwrap();
    let ctx = ctx.extend("id".into(), Cow::Borrowed(&type_id));
    let type_false = resolve_type(&fun_false, &ctx).unwrap();
    let ctx = ctx.extend("false".into(), Cow::Borrowed(&type_false));
    let type_true = resolve_type(&fun_true, &ctx).unwrap();
    let ctx = ctx.extend("true".into(), Cow::Borrowed(&type_true));

    // nat := Πα:*.(α ⭆ α) ⭆ α ⭆ α
    let nat = Cow::Owned(Expression::product(
        "α".into(),
        Expression::sort(0),
        Expression::arrow(
            Expression::arrow("α".into(), "α".into()),
            Expression::arrow("α".into(), "α".into()),
        ),
    ));

    // println!("nat = {}", fun_nat);

    let type_nat = resolve_type(&nat, &ctx).unwrap_chain();
    let ctx = ctx.extend(Variable::new("𝐍"), Cow::Borrowed(&type_nat));

    // zero := λα:*.λf:α⭆α.λx:α.x
    let fun_zero = Expression::abstraction(
        "α".into(),
        Expression::sort(0),
        Expression::abstraction(
            "f".into(),
            Expression::arrow("α".into(), "α".into()),
            Expression::abstraction("x".into(), "α".into(), "x".into()),
        ),
    );

    // println!("zero = {}", fun_zero);

    let type_zero = resolve_type(&fun_zero, &ctx).unwrap_chain();
    let ctx = ctx.extend(Variable::new("zero"), Cow::Borrowed(&type_zero));

    println!("id = {}", fun_id);
    println!("false = {}", fun_false);
    println!("true = {}", fun_true);
    println!("𝐍 = {}", nat);

    println!();

    let fun_succ = Expression::abstraction("n".into(), Expression::Hole, Expression::Hole);
    println!("succ = {}", fun_succ);
    let constraint = Constraint::HasType(TypeConstraint {
        expression: fun_succ,
        expected_type: Expression::arrow(nat.clone().into_owned(), nat.clone().into_owned()),
    });
    let succ_goals = find_goals(ctx.clone(), &constraint).unwrap_chain();

    println!("{} goals", succ_goals.len());
    for goal in succ_goals {
        println!("{}\n", goal);
    }

    let fun_succ = Expression::abstraction(
        "n".into(),
        nat.clone().into_owned(),
        Expression::abstraction("α".into(), Expression::sort(0), Expression::Hole),
    );
    println!("succ = {}", fun_succ);
    let constraint = Constraint::HasType(TypeConstraint {
        expression: fun_succ,
        expected_type: Expression::arrow(nat.clone().into_owned(), nat.clone().into_owned()),
    });
    let succ_goals = find_goals(ctx.clone(), &constraint).unwrap_chain();

    println!("{} goals", succ_goals.len());
    for goal in succ_goals {
        println!("{}\n", goal);
    }

    let fun_succ = Expression::abstraction(
        "n".into(),
        nat.clone().into_owned(),
        Expression::abstraction(
            "α".into(),
            Expression::sort(0),
            Expression::abstraction(
                "f".into(),
                Expression::arrow("α".into(), "α".into()),
                Expression::Hole,
            ),
        ),
    );
    println!("succ = {}", fun_succ);
    let constraint = Constraint::HasType(TypeConstraint {
        expression: fun_succ,
        expected_type: Expression::arrow(nat.clone().into_owned(), nat.clone().into_owned()),
    });
    let succ_goals = find_goals(ctx.clone(), &constraint).unwrap_chain();

    println!("{} goals", succ_goals.len());
    for goal in succ_goals {
        println!("{}\n", goal);
    }

    let fun_succ = Expression::abstraction(
        "n".into(),
        nat.clone().into_owned(),
        Expression::abstraction(
            "α".into(),
            Expression::sort(0),
            Expression::abstraction(
                "f".into(),
                Expression::arrow("α".into(), "α".into()),
                Expression::abstraction("x".into(), "α".into(), Expression::Hole),
            ),
        ),
    );
    println!("succ = {}", fun_succ);
    let constraint = Constraint::HasType(TypeConstraint {
        expression: fun_succ,
        expected_type: Expression::arrow(nat.clone().into_owned(), nat.clone().into_owned()),
    });
    let succ_goals = find_goals(ctx.clone(), &constraint).unwrap_chain();

    println!("{} goals", succ_goals.len());
    for goal in succ_goals {
        println!("{}\n", goal);
    }

    let fun_succ = Expression::abstraction(
        "n".into(),
        nat.clone().into_owned(),
        Expression::abstraction(
            "α".into(),
            Expression::sort(0),
            Expression::abstraction(
                "f".into(),
                Expression::arrow("α".into(), "α".into()),
                Expression::abstraction(
                    "x".into(),
                    "α".into(),
                    Expression::application("f".into(), Expression::Hole),
                ),
            ),
        ),
    );
    println!("succ = {}", fun_succ);
    let constraint = Constraint::HasType(TypeConstraint {
        expression: fun_succ,
        expected_type: Expression::arrow(nat.clone().into_owned(), nat.clone().into_owned()),
    });
    let succ_goals = find_goals(ctx.clone(), &constraint).unwrap_chain();

    println!("{} goals", succ_goals.len());
    for goal in succ_goals {
        println!("{}\n", goal);
    }

    let fun_succ = Expression::abstraction(
        "n".into(),
        nat.clone().into_owned(),
        Expression::abstraction(
            "α".into(),
            Expression::sort(0),
            Expression::abstraction(
                "f".into(),
                Expression::arrow("α".into(), "α".into()),
                Expression::abstraction(
                    "x".into(),
                    "α".into(),
                    Expression::application(
                        "f".into(),
                        Expression::application(Expression::Hole, "x".into()),
                    ),
                ),
            ),
        ),
    );
    println!("succ = {}", fun_succ);
    let constraint = Constraint::HasType(TypeConstraint {
        expression: fun_succ,
        expected_type: Expression::arrow(nat.clone().into_owned(), nat.clone().into_owned()),
    });
    let succ_goals = find_goals(ctx.clone(), &constraint).unwrap_chain();

    println!("{} goals", succ_goals.len());
    for goal in succ_goals {
        println!("{}\n", goal);
    }
}
