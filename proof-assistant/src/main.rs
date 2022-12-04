#![allow(mixed_script_confusables)]
#![allow(confusable_idents)]

#[cfg(test)]
mod tests;

use proof_core::{
    goals::{find_goals, Constraint, TypeConstraint},
    result::ResultExt,
    scope::DefinitionScope,
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

    check!(scope, (void): (Void));

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

    def!(scope, Nat := for α : *. (α => α) => α => α);

    def!(scope, zero := fun α : *. fun f : α => α. fun x : α. x);

    check!(scope, (zero): (Nat));

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

    def!(scope, And := fun α : *. fun β : *. for γ : *. (α => β => γ) => γ);

    def!(scope, pair :=
        fun α : *.
        fun β : *.
        fun x : α.
        fun y : β.
        fun γ : *.
        fun arg : (α => β => γ). arg x y
    );

    def!(scope, fst := fun P : *. fun Q : *. fun x : And P Q. x P (fun a : P. fun b : Q. a));

    def!(scope, snd := fun P : *. fun Q : *. fun x : And P Q. x Q (fun a : P. fun b : Q. b));

    def!(scope, swap_pair := fun P : *. fun Q : *. fun x : And P Q. pair Q P (snd P Q x) (fst P Q x));
    check!(scope, (swap_pair) : (for P : *. for Q : *. And P Q => And Q P));

    def!(scope, Or := fun α : *. fun β : *. for γ : *. (α => γ) => (β => γ) => γ);

    def!(scope, left :=
        fun α : *.
        fun β : *.
        fun x : α.
        fun γ : *.
        fun left1 : α => γ.
        fun right1 : β => γ.
            left1 x
    );

    def!(scope, right :=
        fun α : *.
        fun β : *.
        fun y : β.
        fun γ : *.
        fun left1 : α => γ.
        fun right1 : β => γ.
            right1 y
    );

    def!(scope, Iff := fun P : *. fun Q : *. And (P => Q) (Q => P));
    def!(scope, intro_iff := fun P : *. fun Q : *. pair (P => Q) (Q => P));
    check!(scope, (intro_iff) : (for P : *. for Q : *. (P => Q) => (Q => P) => Iff P Q));

    def!(scope, Eq := fun α : *. fun x : α. fun y : α. for P : α => *. Iff (P x) (P y));

    def!(scope, refl := fun α : *. fun x : α. fun P : α => *. intro_iff (P x) (P x));

    def!(scope, EqNat := Eq Nat);

    check!(scope, (left) : (for α : *. for β : *. α => Or α β));

    // scope.show_all().unwrap_chain();
    println!();

    def!(scope, TheoremLEM := for α : *. α => Or α (Not α));
    def!(scope, lem := fun α : *. fun x : α. left α (Not α) x);
    check!(scope, (lem): (TheoremLEM));
    show!(scope, lem);

    def!(scope, TheoremPOE := for α : *. Bot => α);
    def!(scope, poe := fun α : *. fun bottom : Bot. bottom α);
    check!(scope, (poe): (TheoremPOE));
    show!(scope, poe);

    def!(scope, TheoremDoubleNeg := for α : *. α => Not (Not α));
    def!(scope, double_neg := fun α : *. fun p : α. fun not_p : Not α. not_p p);
    check!(scope, (double_neg): (TheoremDoubleNeg));
    show!(scope, double_neg);

    def!(scope, TheoremLNC := for α : *. Not (And α (Not α)));
    def!(scope, lnc := fun α : *. fun p_and_not_p : And α (Not α). p_and_not_p Bot (fun p : α. fun not_p : Not α. not_p p));
    check!(scope, (lnc): (TheoremLNC));
    show!(scope, lnc);

    show!(scope, Eq);

    def!(scope, TheoremEqSymm := for α : *. for x : α. for y : α. Eq α x y => Eq α y x);
    def!(scope, eq_symm :=
        fun α : *.
        fun x : α.
        fun y : α.
        fun x_eq_y : Eq α x y.
        fun P : (α => *).
        swap_pair (P x => P y) (P y => P x) (x_eq_y P)
    );
    // TODO: Add tree walking to expression tree so that we can match to expressions for displaying pretty stuff like P <=> Q and x = y
    check!(scope, (eq_symm): (TheoremEqSymm));
    show!(scope, eq_symm);

    def!(scope, TheoremSuccEq := for m : Nat. for n : Nat. EqNat m n => EqNat (succ m) (succ n));
    def!(scope, succ_eq :=
        fun m : Nat.
        fun n : Nat.
        fun m_eq_n : EqNat m n.
        fun P : Nat => *.
        ?
    );

    let constraint = Constraint::HasType(TypeConstraint {
        expression: scope.substitute(&expr!(succ_eq)),
        expected_type: scope.substitute(&expr!(TheoremSuccEq)),
    });
    let goals = find_goals(scope.context(), &constraint).unwrap_chain();

    println!();
    println!("{} goals", goals.len());
    for goal in goals.iter() {
        println!("{}.\n{}", goals.len(), goal);
        println!();
    }
}
