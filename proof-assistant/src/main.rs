#![allow(mixed_script_confusables)]
#![allow(confusable_idents)]
#![feature(const_trait_impl)]
#![feature(box_patterns)]

#[cfg(test)]
mod tests;

use console::Term;
use proof_core::{
    error,
    expr::{Expression, ExpressionPath},
    goals::{find_goals, Constraint, TypeConstraint},
    result::{Result, ResultExt},
    scope::DefinitionScope, repl::Repl, eval::free_variables, types::{InferenceSolver, PathContext, map_path_type_constraint_from_paths},
};

use proof_impl::expr;

macro_rules! check {
    ($scope:expr, ($($lhs:tt)+) : ($($rhs:tt)+)) => {
        $scope.show_type_check(expr!($($lhs)+), expr!($($rhs)+)).chain_error(|| proof_core::error!("type check failed")).unwrap_chain()
    };
}

macro_rules! check_eq {
    ($scope:expr, ($($lhs:tt)+) = ($($rhs:tt)+)) => {
        $scope.show_eq_check(expr!($($lhs)+), expr!($($rhs)+)).chain_error(|| proof_core::error!("equality check failed")).unwrap_chain()
    };
}

macro_rules! def {
    ($scope:expr, $lhs:ident := $($rhs:tt)+) => {
        $scope.add_definition(stringify!($lhs).into(), expr!($($rhs)+)).chain_error(|| proof_core::error!("could not define {}", stringify!($lhs))).unwrap_chain()
    };

    ($scope:expr, $lhs:literal := $($rhs:tt)+) => {
        $scope.add_definition($lhs.into(), expr!($($rhs)+)).chain_error(|| proof_core::error!("could not define {}", $lhs)).unwrap_chain()
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

trait GoalReporter {
    fn report_goals(&self, expression: Expression, expected_type: Expression);
}

impl<'a> GoalReporter for DefinitionScope<'a> {
    fn report_goals(&self, expression: Expression, expected_type: Expression) {
        let expression = self.substitute(&expression);
        let expected_type = self.substitute(&expected_type);
        let constraint = Constraint::HasType(TypeConstraint {
            expression,
            expected_type,
        });
        let goals = find_goals(self.context().clone(), &constraint).unwrap_chain();

        if goals.is_empty() {
            println!("Success, no goals left!");
            return;
        }
        println!();
        println!("{} goals", goals.len());
        for (i, goal) in goals.iter().enumerate() {
            println!("{}.\n{}", i + 1, goal);
            println!();
        }
    }
}

macro_rules! goals {
    ($scope:expr, [$($xs:tt)+] : [$($ys:tt)+]) => {
        $scope.report_goals(expr!($($xs)+), expr!($($ys)+))
    };
}

fn main() {
    let mut repl = Repl::new(Term::stdout());
    repl.run_repl().unwrap();
}

#[test]
fn scope_test() {
    let mut scope = DefinitionScope::new();

    def!(scope, Bot := for α : *. α);

    def!(scope, Id := for α : *. for x : α. α);
    def!(scope, id := fun α : *. fun x : α. x);

    def!(scope, let :=
        fun α : *.
        fun x : α.
        fun β : *.
        fun f : α => β.
        f x
    );

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

    def!(scope, Bool := for α : *. α => α => α);
    show!(scope, Bool);

    def!(scope, bool_true := fun α : *. fun x : α. fun y : α. x);
    check!(scope, (bool_true): (Bool));
    show!(scope, bool_true);

    def!(scope, bool_false := fun α : *. fun x : α. fun y : α. y);
    check!(scope, (bool_false): (Bool));
    show!(scope, bool_false);

    def!(scope, bool_not := fun α : *. fun x : Bool α. fun y : α. fun z : α. x z y);
    show!(scope, bool_not);

    def!(scope, Not := fun α : *. α => Bot);
    show!(scope, Not);

    def!(scope, TheoremNotBot := Not Bot);
    show!(scope, TheoremNotBot);

    def!(scope, not_bot := id Bot);
    check!(scope, (not_bot): (TheoremNotBot));

    def!(scope, And := fun α : *. fun β : *. for γ : *. (α => β => γ) => γ);
    show!(scope, And);

    def!(scope, pair :=
        fun α : *.
        fun β : *.
        fun x : α.
        fun y : β.
        fun γ : *.
        fun arg : (α => β => γ). arg x y
    );
    show!(scope, pair);

    def!(scope, fst := fun P : *. fun Q : *. fun x : And P Q. x P (fun a : P. fun b : Q. a));
    show!(scope, fst);

    def!(scope, snd := fun P : *. fun Q : *. fun x : And P Q. x Q (fun a : P. fun b : Q. b));
    show!(scope, snd);

    def!(scope, swap_pair := fun P : *. fun Q : *. fun x : And P Q. pair Q P (snd P Q x) (fst P Q x));
    check!(scope, (swap_pair) : (for P : *. for Q : *. And P Q => And Q P));

    def!(scope, Or := fun α : *. fun β : *. for γ : *. (α => γ) => (β => γ) => γ);

    def!(scope, left :=
        fun α : *.
        fun β : *.
        fun x : α.
        fun γ : *.
        fun l : α => γ.
        fun r : β => γ.
            l x
    );

    def!(scope, right :=
        fun α : *.
        fun β : *.
        fun y : β.
        fun γ : *.
        fun l : α => γ.
        fun r : β => γ.
            r y
    );

    def!(scope, Iff := fun P : *. fun Q : *. And (P => Q) (Q => P));
    def!(scope, intro_iff := fun P : *. fun Q : *. pair (P => Q) (Q => P));
    check!(scope, (intro_iff) : (for P : *. for Q : *. (P => Q) => (Q => P) => Iff P Q));

    def!(scope, Eq :=
        fun α : *.
        fun x : α.
        fun y : α.
        for P : α => *. Iff (P x) (P y)
    );
    show!(scope, Eq);

    def!(scope, refl := fun α : *. fun x : α. fun P : α => *. intro_iff (P x) (P x));

    // def!(scope, EqNat := Eq Nat);

    check!(scope, (left) : (for α : *. for β : *. α => Or α β));

    // scope.show_all().unwrap_chain();
    println!();

    // A => A ∨ ¬A
    def!(scope, TheoremLEM := for A : *. A => Or A (Not A));
    def!(scope, lem :=
        fun A : *.
        fun x : A.
        left A (Not A) x
    );
    check!(scope, (lem): (TheoremLEM));
    show!(scope, lem);

    // ⊥ => A
    def!(scope, TheoremPOE := for A : *. (for α : *. α) => A);
    def!(scope, poe :=
        fun A : *.
        fun bottom : (for α : *. α).
        bottom A
    );
    check!(scope, (poe): (TheoremPOE));
    show!(scope, poe);

    // A => ¬¬A
    def!(scope, TheoremDoubleNeg := for A : *. A => Not (Not A));
    def!(scope, double_neg :=
        fun A : *.
        fun a : A.
        fun not_a : Not A.
        not_a a
    );
    check!(scope, (double_neg): (TheoremDoubleNeg));
    show!(scope, double_neg);

    // ¬(A ∧ ¬A)
    def!(scope, TheoremLNC := for A : *. Not (And A (Not A)));
    def!(scope, lnc :=
        fun A : *.
        fun p_and_not_p : And A (Not A).
        p_and_not_p Bot (
            fun p : A.
            fun not_p : Not A.
            not_p p
        )
    );
    check!(scope, (lnc): (TheoremLNC));
    show!(scope, lnc);

    // P ∧ Q => Q ∧ P
    def!(scope, TheoremAndSymm :=
        for P : *. for Q : *. And P Q => And Q P
    );
    show!(scope, TheoremAndSymm);
    def!(scope, and_symm :=
        fun P : *.
        fun Q : *.
        fun p_and_q : And P Q.
        pair Q P (snd P Q p_and_q) (fst P Q p_and_q)
    );
    check!(scope, (and_symm): (TheoremAndSymm));

    // P ∨ Q => Q ∨ P
    def!(scope, TheoremOrSymm :=
        for P : *. for Q : *. Or P Q => Or Q P
    );
    show!(scope, TheoremOrSymm);
    def!(scope, or_symm :=
        fun P : *.
        fun Q : *.
        fun pq : Or P Q.
        pq (Or Q P)
            (fun p : P. right Q P p)
            (fun q : Q. left Q P q)
    );
    check!(scope, (or_symm): (TheoremOrSymm));

    // P ∧ (Q ∧ R) => (P ∧ Q) ∧ R
    def!(scope, TheoremAndAssoc :=
        for P : *. for Q : *. for R : *. And P (And Q R) => And (And P Q) R
    );
    show!(scope, TheoremAndAssoc);
    def!(scope, and_assoc :=
        fun P : *. fun Q : *. fun R : *.
        fun h : And P (And Q R).
        pair (And P Q) R
            (pair P Q
                (fst P (And Q R) h)
                (fst Q R (snd P (And Q R) h))
            )
            (snd Q R (snd P (And Q R) h))
    );
    check!(scope, (and_assoc): (TheoremAndAssoc));

    // P ∨ (Q ∨ R) => (P ∨ Q) ∨ R
    def!(scope, TheoremOrAssoc :=
        for P : *. for Q : *. for R : *. Or P (Or Q R) => Or (Or P Q) R
    );
    show!(scope, TheoremOrAssoc);
    def!(scope, or_assoc :=
        fun P : *. fun Q : *. fun R : *.
        fun h : Or P (Or Q R).
        fun γ : *.
        fun case_p_or_q : Or P Q => γ.
        fun case_r : R => γ.
        h γ
            (fun p : P. case_p_or_q (left P Q p))
            (fun q_or_r : Or Q R. q_or_r γ
                (fun q : Q. case_p_or_q (right P Q q))
                (fun r : R. case_r r)
            )
    );
    check!(scope, (or_assoc): (TheoremOrAssoc));

    // (P <=> Q) => P => Q
    def!(scope, TheoremIffForward := for P : *. for Q : *. Iff P Q => P => Q);
    show!(scope, TheoremIffForward);
    def!(scope, iff_forward :=
        fun P : *. fun Q : *.
        ?
    );
    goals!(scope, [iff_forward]: [TheoremIffForward]);

    /* let e = &expr!(
        fun n : for α : *. (α => α) => α => α.
        fun β : *.
        fun f : β => β.
        fun x : β.
        n A (fun g : G. fun h : H. h (g f)) (fun y : Y. x) (fun y : Z. y)
    ); */
    let e = &expr!(
        fun id : (for α : *. α => α). fun U : *. fun x : U. id A x
    );

    /* let mut equations = vec![];
    e.solve_equations(scope.context(), &mut equations).unwrap_chain();
    println!("Solving...");
    for eq in equations.iter() {
        println!("{}", eq);
    } */

    /* let mut paths = vec![];
    e.collect_paths_into(&ExpressionPath::new(&[]), &mut paths);
    for path in paths.iter() {
        println!("{}: {}", &path, e.path_ref(path).unwrap());
    } */

    println!("Unknowns...");
    let fvs = free_variables(e);
    for fv in fvs.iter() {
        println!("{}", fv);
    }

    println!("Solving constraints...");
    let mut constraints = vec![];
    e.init_constraints(
        &mut PathContext::new(),
        &ExpressionPath::new(&[]),
        &mut constraints,
    );
    for constraint in constraints.iter() {
        // println!("{}", constraint);
        /* match constraint {
            PathTypeConstraint::TermInhabitsType { term, type_of_term } => println!(
                "\"{}\" -> \"{}\"",
                term, type_of_term
            ),
            PathTypeConstraint::TermInhabitsProductType {
                term,
                inhabited_product_argument_type,
                inhabited_product_return_type,
            } => {
                println!("\"{}\" -> \"{}\" [arrowhead=\"diamond\" ]", term, inhabited_product_argument_type);
                println!("\"{}\" -> \"{}\" [arrowhead=\"ediamond\" ]", term, inhabited_product_return_type);
            }
            PathTypeConstraint::TermsAreEqual { term_lhs, term_rhs } => println!("\"{}\" -> \"{}\" [dir=\"both\" arrowhead=\"box\" arrowtail=\"box\"]", term_lhs, term_rhs),
            PathTypeConstraint::TermsInhabitSameType { term_lhs, term_rhs } => println!("\"{}\" -> \"{}\" [dir=\"both\" arrowhead=\"obox\" arrowtail=\"obox\"]", term_lhs, term_rhs),
            PathTypeConstraint::TermInhabitsUnknownType(_) => {},
            PathTypeConstraint::TermIsIllFormed(_) => {},
            PathTypeConstraint::TermIsProductType(_) => {},
            PathTypeConstraint::TermIsSort(term, sort_rank) => { println!("\"{}\" -> \"{}\" [dir=\"both\" arrowhead=\"box\" arrowtail=\"box\"]", term, Expression::Sort(*sort_rank)) },
        } */
        println!("{}", map_path_type_constraint_from_paths(e, constraint))
    }

    def!(scope, TheoremNegConj := for P : *. for Q : *. Iff (Not (And P Q)) (Or (Not P) (Not Q)));
    /* def!(scope, neg_conj :=
        fun P : *.
        fun Q : *.
        pair
            ((Not (And P Q)) => (Or (Not P) (Not Q)))
            ((Or (Not P) (Not Q)) => (Not (And P Q)))
            (
                // goal : (Not (And P Q)) => (Or (Not P) (Not Q))
                fun h : Not (And P Q).
                // h    : And P Q => Bot
                //      : (ΠR : *. (P => Q => R) => R) => Bot
                //
                // goal : (Or (Not P) (Not Q))
                //      : ΠR : *. (Not P => R) => (Not Q => R) => R
                //
                fun
            )
    ); */

    def!(scope, Symm := fun Op : (for α : *. α => α => *). for α : *. for x : α. for y : α. Op α x y => Op α y x);
    def!(scope, SymmT := fun Op : * => * => *. for α : *. for β : *. Op α β => Op β α);

    def!(scope, TheoremEqSymm := Symm Eq);
    def!(scope, eq_symm :=
        fun α : *.
        fun x : α.
        fun y : α.
        fun x_eq_y : Eq α x y.
        fun P : (α => *).
        swap_pair (P x => P y) (P y => P x) (x_eq_y P)
    );
    check!(scope, (eq_symm): (TheoremEqSymm));
    show!(scope, eq_symm);

    def!(scope, Nat := for α : *. (α => α) => α => α);
    def!(scope, nat_zero := fun α : *. fun f : α => α. fun x : α. x);
    check!(scope, (nat_zero): (Nat));
    def!(scope, nat_one := fun α : *. fun f : α => α. fun x : α. f x);
    def!(scope, nat_succ := fun n : Nat. fun α : *. fun f : α => α. fun x : α. f (n α f x));
    check!(scope, (nat_succ) : (Nat => Nat));

    def!(scope, nat_pred :=
        fun n : Nat.
        fun α : *.
        fun f : α => α.
        fun x : α.
        n ((α => α) => α) (fun g : (α => α) => α. fun h : α => α. h (g f)) (fun y : α => α. x) (fun y : α. y)
    );
    check!(scope, (nat_pred) : (Nat => Nat));

    // Note: n α f : α => α which applies f n-times.
    // Example: 3 α f x = f (f (f x))

    def!(scope, nat_add :=
        fun m : Nat.
        fun n : Nat.
        n Nat nat_succ m
    );

    def!(scope, nat_sub :=
        fun m : Nat.
        fun n : Nat.
        n Nat nat_pred m
    );

    // check_eq!(scope, (nat_pred nat_zero) = (nat_zero));
    // check_eq!(scope, (nat_pred (nat_succ nat_zero)) = (nat_zero));
    // check_eq!(scope, (nat_pred (nat_succ (nat_succ nat_zero))) = (nat_succ nat_zero));

    def!(scope, nat_is_zero :=
        fun n : Nat.
        fun α : *.
            n (α => α => α)
                (fun x : α => α => α. bool_false α)
                (bool_true α)
    );

    check!(scope, (nat_is_zero) : (Nat => Bool));

    show!(scope, Bot);
    show!(scope, Not);
    show!(scope, And);
    show!(scope, Or);

    show!(scope, left);
    show!(scope, right);

    // The integers
    def!(scope, Int := for γ : *. (Id => γ) => (Nat => γ) => (Nat => γ) => γ);
    show!(scope, Int);
    def!(scope, int_zero :=
        fun γ : *.
        fun zero : Id => γ.
        fun _ : Nat => γ.
        fun _ : Nat => γ.
        zero id
    );
    check!(scope, (int_zero): (Int));

    def!(scope, int_one :=
        fun γ : *.
        fun zero : Id => γ.
        fun pos : Nat => γ.
        fun neg : Nat => γ.
        pos nat_zero
    );
    check!(scope, (int_one): (Int));

    def!(scope, int_neg_one :=
        fun γ : *.
        fun zero : Id => γ.
        fun pos : Nat => γ.
        fun neg : Nat => γ.
        neg nat_zero
    );
    check!(scope, (int_neg_one): (Int));

    def!(scope, int_neg :=
        fun n : Int.
        fun γ : *.
        n ((Id => γ) => (Nat => γ) => (Nat => γ) => γ)
            // If n = 0
            (fun n_zero : Id. int_zero γ)

            // If n > 0
            (fun n_pos : Nat.
                fun zero : Id => γ.
                fun pos : Nat => γ.
                fun neg : Nat => γ.
                neg n_pos
            )

            // If n < 0
            (fun n_neg : Nat.
                fun zero : Id => γ.
                fun pos : Nat => γ.
                fun neg : Nat => γ.
                pos n_neg
            )
    );

    check!(scope, (int_neg) : (Int => Int));

    def!(scope, int_is_zero :=
        fun n : Int.
        fun γ : *.
        n (γ => γ => γ)
            // If n = 0
            (fun n_zero : Id. bool_true γ)

            // If n > 0
            (fun n_pos : Nat. bool_false γ)

            // If n < 0
            (fun n_neg : Nat. bool_false γ)
    );

    check!(scope, (int_is_zero) : (Int => Bool));

    def!(scope, int_is_neg :=
        fun n : Int.
        fun γ : *.
        n (γ => γ => γ)
            // If n = 0
            (fun n_zero : Id. bool_false γ)

            // If n > 0
            (fun n_pos : Nat. bool_false γ)

            // If n < 0
            (fun n_neg : Nat. bool_true γ)
    );

    check!(scope, (int_is_neg) : (Int => Bool));

    def!(scope, int_is_pos :=
        fun n : Int.
        fun γ : *.
        n (γ => γ => γ)
            // If n = 0
            (fun n_zero : Id. bool_false γ)

            // If n > 0
            (fun n_pos : Nat. bool_false γ)

            // If n < 0
            (fun n_neg : Nat. bool_true γ)
    );

    check!(scope, (int_is_pos) : (Int => Bool));

    check_eq!(scope, (int_neg int_zero) = (int_zero));
    check_eq!(scope, (int_neg int_one) = (int_neg_one));
    check_eq!(scope, (int_neg int_neg_one) = (int_one));

    // The successor function
    def!(scope, int_succ :=
        fun n : Int.
        fun γ : *.
        n ((Id => γ) => (Nat => γ) => (Nat => γ) => γ)
            // If n = 0
            (fun n_zero : Id. int_one γ)

            // If n > 0
            (
                fun n_pos : Nat.
                fun zero : Id => γ.
                fun pos : Nat => γ.
                fun neg : Nat => γ.
                pos (nat_succ n_pos)
            )

            // If n < 0
            (
                fun n_neg : Nat.
                (nat_is_zero n_neg) ((Id => γ) => (Nat => γ) => (Nat => γ) => γ)
                    // If n_neg = 0
                    (int_zero γ)

                    // If n_neg > 0
                    (
                        fun zero : Id => γ.
                        fun pos : Nat => γ.
                        fun neg : Nat => γ.
                        neg (nat_pred n_neg)
                    )
            )
    );

    check!(scope, (int_succ) : (Int => Int));

    def!(scope, int_pred :=
        fun n : Int.
        fun γ : *.
        n ((Id => γ) => (Nat => γ) => (Nat => γ) => γ)
            // If n = 0
            (fun n_zero : Id. int_neg_one γ)

            // If n > 0
            (
                fun n_pos : Nat.
                (nat_is_zero n_pos) ((Id => γ) => (Nat => γ) => (Nat => γ) => γ)
                    // If n_pos = 0
                    (int_zero γ)

                    // If n_pos > 0
                    (
                        fun zero : Id => γ.
                        fun pos : Nat => γ.
                        fun neg : Nat => γ.
                        pos (nat_pred n_pos)
                    )
            )

            // If n < 0
            (
                fun n_neg : Nat.
                fun zero : Id => γ.
                fun pos : Nat => γ.
                fun neg : Nat => γ.
                neg (nat_succ n_neg)
            )
    );

    check!(scope, (int_pred) : (Int => Int));

    def!(scope, int_match :=
        fun n : Int.
        fun γ : *.
        fun zero : γ.
        fun pos : γ.
        fun neg : γ.
        n γ
            (fun _ : Id. zero)
            (fun _ : Nat. pos)
            (fun _ : Nat. neg)
    );

    def!(scope, int_abs_as_nat :=
        fun n : Int.
        n Nat
            // If n = 0
            (fun n_zero : Id. nat_zero)

            // If n > 0
            (fun n_pos : Nat. nat_succ n_pos)

            // If n < 0
            (fun n_neg : Nat. nat_succ n_neg)
    );

    // Helper function to be more explicit about the intention to repeatedly apply a function.
    def!(scope, repeat :=
        fun α : *.
        fun f : α => α.
        fun n : Nat.
        n α f
    );

    check!(scope, (repeat) : (for α : *. (α => α) => Nat => (α => α)));

    def!(scope, int_add :=
        fun m : Int.
        fun n : Int.
        int_match n Int
            // n = 0
            m

            // n > 0
            (repeat Int int_succ (int_abs_as_nat n) m) // apply int_succ n-times to m

            // n < 0
            (repeat Int int_pred (int_abs_as_nat n) m) // apply int_pred |n|-times to m
    );

    def!(scope, "+" := int_add);

    def!(scope, int_sub :=
        fun m : Int.
        fun n : Int.
        int_add m (int_neg n)
    );

    def!(scope, int_mul :=
        fun m : Int.
        fun n : Int.
        ?
    );

    def!(scope, TotalOrder :=
        for α : *.
        for R : α => α => *.
        (for a : α. R a a) =>
        (for a : α. for b : α. for c : α. And (R a b) (R b c) => (R a c)) =>
        (for a : α. for b : α. for c : α. And (R a b) (R b a) => Eq α a b) =>
        (for a : α. for b : α. Or (R a b) (R b a))
    );

    def!(scope, Ind :=
        for P : Nat => *. P nat_zero => (for x : Nat. P x => P (nat_succ x)) => for x : Nat. P x
    );
    show!(scope, Ind);

    def!(scope, EqNat :=
        fun m : Nat.
        fun n : Nat.
        Eq Nat m n
    );

    def!(scope, LTNat :=
        fun m : Nat.
        fun n : Nat.
        // m < n <=> ∃x : 𝐍. m - x = 0 ∧ n - x = 1
        for C : *. (
            for x : Nat.
            And
                (EqNat (nat_sub m x) (nat_zero))
                (EqNat (nat_sub n x) nat_one)
            => C
        ) => C
    );
    show!(scope, LTNat);

    def!(scope, ind_ge_zero :=
        fun zero_case : ?.
        fun ind_case : ?.
        fun x : Nat.
        ?
    );

    def!(scope, inter :=
        fun A : *.
        fun α : (A => *) => *.
        fun x : A.
        for P : A => *.
        α P => P x
    );
    show!(scope, inter);

    def!(scope, inter_ex :=
        inter Bool (fun P : Bool => *. P bool_true) bool_false
    );
    show!(scope, inter_ex);
}

fn expr_to_int(scope: &DefinitionScope, expr: &Expression) -> Result<i32> {
    let is_int = scope.is_of_type(expr, &expr!(Int))?;
    if !is_int {
        return error!("Expected an Int").into();
    }

    if scope.is_eq(expr, &expr!(int_zero)) {
        return Ok(0);
    }

    if scope.is_eq(
        &scope.eval(&Expression::application(expr!(int_is_neg), expr.clone())),
        &expr!(bool_true),
    ) {
        let expr_plus_one = scope.eval(&Expression::application(expr!(int_succ), expr.clone()));
        expr_to_int(scope, &expr_plus_one).map(|x| x - 1)
    } else {
        let expr_minus_one = scope.eval(&Expression::application(expr!(int_pred), expr.clone()));
        expr_to_int(scope, &expr_minus_one).map(|x| x + 1)
    }
}
