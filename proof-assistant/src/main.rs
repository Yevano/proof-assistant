#![allow(mixed_script_confusables)]
use std::borrow::Cow;

use proof_core::{
    eval::beta_reduce,
    expr::{Expression, Variable},
    goals::{find_goals, Constraint, Goal, TypeConstraint},
    result::ResultExt,
    scope::DefinitionScope,
    types::resolve_type,
    types::Context,
};
use proof_impl::expr;

macro_rules! check {
    ($scope:expr, ($($lhs:tt)+) : ($($rhs:tt)+)) => {
        $scope.show_type_check(expr!($($lhs)+), expr!($($rhs)+)).chain_error(|| proof_core::error!("type check failed")).unwrap_chain()
    };
}

macro_rules! def {
    ($scope:expr, $lhs:ident := $($rhs:tt)+) => {
        $scope.add_definition(stringify!($lhs).into(), expr!($($rhs)+)).chain_error(|| proof_core::error!("could not define {}", stringify!($lhs))).unwrap_chain()
    };
}

macro_rules! show_type {
    ($scope:expr, $($value:tt)+) => {
        $scope.show_type(expr!($($value)+)).chain_error(|| proof_core::error!("type resolution failed")).unwrap_chain()
    };
}

macro_rules! show {
    ($scope:expr, $($value:tt)+) => {
        $scope.show(expr!($($value)+)).chain_error(|| proof_core::error!("failed to show value")).unwrap_chain()
    };
}

fn main() {
    scope_test();
}

fn scope_test() {
    let mut scope = DefinitionScope::new();

    def!(scope, Bot := for α : *. α);

    def!(scope, id := fun α : *. fun x : α. x);

    def!(scope, Id := for α : *. for x : α. α);

    def!(scope, Void := Id => Id);
    show!(scope, Void);

    def!(scope, void := id Id);

    check!(scope, (void) : (Void));

    def!(scope, Value := fun α : *. (α => α) => α);
    show!(scope, Value);

    def!(scope, value := fun α : *. fun v : α. fun h : α => α. h v);

    check!(scope, (value) : (for α : *. α => (Value α)));

    def!(scope, extract := fun α : *. fun k : Value α. k (id α));
    show_type!(scope, extract);

    // match_value α : Value α => for β : *. (α => β) => β
    def!(scope, match_value := fun α : *. fun v : Value α. fun β : *. fun f : α => β. f (extract α v));
    show!(scope, match_value);

    // map_value : for α : *. for β : *. Value α => (α => β) => Value β
    def!(scope, map_value := fun α : *. fun β : *. fun v : Value α. fun f : α => β. value β (f (extract α v)));
    show!(scope, map_value);

    def!(scope, const := fun α : *. fun β : *. fun u : α. β);

    def!(scope, Eq := fun α : *. fun x : α. fun y : α. for p : α => *. p x => p y);

    def!(scope, refl := fun α : *. fun x : α. fun p : α => *. id (p x));

    def!(scope, id_eq_id := refl Id id);

    check!(scope, (id_eq_id) : (Eq Id id id));

    def!(scope, Nat := for α : *. (α => α) => α => α);

    def!(scope, zero := fun α : *. fun f : α => α. fun x : α. x);

    check!(scope, (zero) : (Nat));

    def!(scope, succ := fun n : Nat. fun α : *. fun f : α => α. fun x : α. f (n α f x));

    /* def!(scope, pred :=
        fun n : Nat.
        fun α : *.
        fun f : α => α.
        fun x : α.

    ); */

    scope.show(expr!(succ zero)).unwrap_chain();

    check!(scope, (succ zero) : (Nat));

    def!(scope, Not := fun α : *. α => Bot);

    def!(scope, And := fun α : *. fun β : *. for τ : *. (α => β => τ) => τ);

    def!(scope, pair :=
        fun α : *.
        fun β : *.
        fun x : α.
        fun y : β.
        fun τ : *.
        fun pair1 : (α => β => τ). pair1 x y
    );

    def!(scope, fst := fun α : *. fun β : *. fun x : And α β. x α (fun a : α. fun b : β. a));

    def!(scope, snd := fun α : *. fun β : *. fun x : And α β. x β (fun a : α. fun b : β. b));

    def!(scope, Or := fun α : *. fun β : *. for τ : *. (α => τ) => (β => τ) => τ);

    def!(scope, left :=
        fun α : *.
        fun β : *.
        fun x : α.
        fun τ : *.
        fun left1 : α => τ.
        fun right1 : β => τ.
            left1 x
    );

    def!(scope, right :=
        fun α : *.
        fun β : *.
        fun y : β.
        fun τ : *.
        fun left1 : α => τ.
        fun right1 : β => τ.
            right1 y
    );

    // def!(scope, ValueNat := fun ValueNatK : *(1). fun ValueNat : ValueNatK. Or Void (ValueNat));
    // show!(scope, ValueNat1);

    // def!(scope, ValueNat := ValueNat1 ValueNat1);
    // show!(scope, ValueNat);

    // show_type!(scope, E * Void void);

    def!(scope, value_zero := fun α : *. left Void (Value α) void);

    // def!(scope, value_succ := fun n : ValueNat. fun α : *. right Void (Value α) (value α n));

    def!(scope, NatEq := Eq Nat);

    check!(scope, (left) : (for α : *. for β : *. α => Or α β));

    def!(scope, Lte := fun m : Nat. fun n : Nat. fun Lte : Nat => Nat => * => *. for τ : *. (NatEq m zero => τ) => (Lte (pred m) (pred n)) => τ);

    // def!(scope, intro_lte_zero := fun n : Nat. fun τ : *. fun intro_lte_zero1 : NatEq n zero => τ. fun intro_lte_pred : Lte (pred m) (pred n). refl n zero);

    // if a = b, S a = S b
    def!(scope, TheoremSuccEq := for m : Nat. for n : Nat. NatEq m n => NatEq (succ m) (succ n));

    // scope.show_all().unwrap_chain();
    println!();

    def!(scope, succ_eq := fun m : Nat. fun n : Nat. fun m_eq_n : NatEq m n. m_eq_n (fun x : Nat. Nat));

    def!(scope, TheoremLEM := for α : *. α => Or α (Not α));
    def!(scope, lem := fun α : *. fun x : α. left α (Not α) x);
    check!(scope, (lem) : (TheoremLEM));
    show!(scope, lem);

    def!(scope, TheoremPOE := for α : *. Bot => α);
    def!(scope, poe := fun α : *. fun bottom : Bot. bottom α);
    check!(scope, (poe) : (TheoremPOE));
    show!(scope, poe);

    def!(scope, TheoremDoubleNeg := for α : *. α => Not (Not α));
    def!(scope, double_neg := fun α : *. fun p : α. fun not_p : Not α. not_p p);
    check!(scope, (double_neg) : (TheoremDoubleNeg));
    show!(scope, double_neg);

    def!(scope, TheoremLNC := for α : *. Not (And α (Not α)));
    def!(scope, lnc := fun α : *. fun p_and_not_p : And α (Not α). p_and_not_p Bot (fun p : α. fun not_p : Not α. not_p p));
    check!(scope, (lnc) : (TheoremLNC));
    show!(scope, lnc);

    def!(scope, one := succ zero);
    def!(scope, two := succ (succ zero));
    check!(scope, (refl Nat ?) : (Eq Nat one two));

    def!(scope, TheoremEqSymm := for α : *. for x : α. for y : α. Eq α x y => Eq α y x);
    def!(scope, eq_symm :=
        fun α : *. fun x : α. fun y : α. fun eq : (for p : α => *. p x => p y). fun q : α => *. ?
    );

    let constraint = Constraint::HasType(TypeConstraint {
        expression: scope.substitute(&expr!(eq_symm)),
        expected_type: scope.substitute(&expr!(TheoremEqSymm)),
    });
    let goals = find_goals(scope.context(), &constraint).unwrap_chain();

    println!();
    println!("{} goals", goals.len());
    for goal in goals.iter() {
        println!("{}.\n{}", goals.len(), goal);
        println!();
    }
}
