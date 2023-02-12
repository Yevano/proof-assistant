use proof_core::{
    expr::Expression,
    goals::{find_goals, Constraint, TypeConstraint},
    result::ResultExt,
    types::Context,
};
use proof_impl::{expr, char_slice_from_str};

fn report_goals(expression: Expression, expected_type: Expression) {
    let constraint = Constraint::HasType(TypeConstraint {
        expression,
        expected_type,
    });
    let goals = find_goals(Context::Empty, &constraint).unwrap_chain();

    println!();
    println!("{} goals", goals.len());
    for (i, goal) in goals.iter().enumerate() {
        println!("{}.\n{}", i + 1, goal);
        println!();
    }
}

macro_rules! goals {
    ([$($xs:tt)+] : [$($ys:tt)+]) => {
        report_goals(expr!($($xs)+), expr!($($ys)+))
    };
}

#[test]
fn test_goal_finder() {
    // goals!([?] : [A]);
    // goals!([fun x : A. ?] : [A => B]);
    // goals!([fun x : ?. ?] : [A => B]);

    // FIXME: This should report an error about x not being bound to the correct type to receive B
    // goals!([(fun x : A. x) ?] : [B]);

    // goals!();
}

#[test]
fn test_prettify() {
    // Πγ:*.((A ⭆ B) ⭆ (B ⭆ A) ⭆ γ) ⭆ γ
    // let expr = expr!(for γ : *. ((A => B) => (B => A) => γ) => γ);
    // println!("{}", expr);
}

#[cfg(test)]
mod term_writer_tests {
    use proof_core::{term_writer::*, term::Term};

    #[test]
    fn create_terms() {
        // let mut term_writer = TermWriter::new();

        // let mut t0 = 
        // let t1 = term_writer.write_binder(BinderType::Abstraction, Variable::from("𝐍").into(), Universe::zero().into(), Atom::default());

        // println!("{}", term);
    }
}

#[test]
fn test_string_slice_macro() {
    let bs: [char; 0] = char_slice_from_str!("");
    let cs: [char; 0] = [];
    assert_eq!(&bs, &cs)
}