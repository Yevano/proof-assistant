#![allow(mixed_script_confusables)]
use std::borrow::Cow;

use proof_core::{
    eval::beta_reduce,
    expr::{Expression, Variable},
    goals::{find_goals, Constraint, Goal, TypeConstraint},
    result::ResultExt,
    scope::DefinitionScope,
    types::Context,
    types::{resolve_type, types_match},
};
use proof_impl::expr;

fn main() {
    scope_test();
}

fn scope_test() {
    let mut scope = DefinitionScope::new();

    scope
        .add_definition("Bot".into(), expr!(for α : *. α))
        .unwrap_chain();

    scope
        .add_definition("id".into(), expr!(fun α : *. fun x : α. x))
        .unwrap_chain();

    scope
        .add_definition("Id".into(), expr!(for α : *. for x : α. α))
        .unwrap_chain();

    scope
        .add_definition(
            "Eq".into(),
            expr!(fun α : *. fun x : α. fun y : α. for p : α => *. p x => p y),
        )
        .unwrap_chain();

    scope
        .add_definition(
            "refl".into(),
            expr!(fun α : *. fun x : α. fun p : α => *. id (p x)),
        )
        .unwrap_chain();

    scope
        .add_definition("id_eq_id".into(), expr!(refl Id id))
        .unwrap_chain();

    scope
        .show_type_check("id_eq_id".into(), expr!(Eq Id id id))
        .unwrap_chain();

    scope
        .add_definition("Nat".into(), expr!(for α : *. (α => α) => α => α))
        .unwrap_chain();

    scope
        .add_definition(
            "zero".into(),
            expr!(fun α : *. fun f : α => α. fun x : α. x),
        )
        .unwrap_chain();

    scope
        .show_type_check(expr!(zero), expr!(Nat))
        .unwrap_chain();

    scope
        .add_definition(
            "succ".into(),
            expr!(fun n : Nat. fun α : *. fun f : α => α. fun x : α. f (n α f x)),
        )
        .unwrap_chain();

    scope.show(expr!(succ zero)).unwrap_chain();

    scope
        .show_type_check(expr!(succ zero), expr!(Nat))
        .unwrap_chain();

    scope
        .add_definition("Not".into(), expr!(fun α : *. for τ : *. α => τ))
        .unwrap_chain();
    scope
        .add_definition(
            "And".into(),
            expr!(fun α : *. fun β : *. for τ : *. (α => β => τ) => τ),
        )
        .unwrap_chain();
    scope
        .add_definition(
            "Or".into(),
            expr!(fun α : *. fun β : *. for τ : *. (α => τ) => (β => τ) => τ),
        )
        .unwrap_chain();

    scope
        .add_definition("NatEq".into(), expr!(Eq Nat))
        .unwrap_chain();

    // if a = b, S a = S b
    scope
        .add_definition(
            "TheoremSuccEq".into(),
            expr!(for m : Nat. for n : Nat. NatEq m n => NatEq (succ m) (succ n)),
        )
        .unwrap_chain();

    scope.show_all().unwrap_chain();
    println!();

    scope
        .add_definition(
            "succ_eq".into(),
            expr!(
                fun m : Nat. ?
            ),
        )
        .unwrap_chain();

    /* let constraint = Constraint::HasType(TypeConstraint {
        expression: scope.substitute(&expr!(succ_eq)),
        expected_type: scope.substitute(&expr!(TheoremSuccEq)),
    });
    let goals = find_goals(scope.context(), &constraint).unwrap_chain();

    println!();
    println!("{} goals", goals.len());
    for goal in goals.iter() {
        println!("{}.\n{}", goals.len(), goal);
        println!();
    } */

    scope.show_type_check(expr!(succ_eq), expr!(TheoremSuccEq)).unwrap_chain();
}
