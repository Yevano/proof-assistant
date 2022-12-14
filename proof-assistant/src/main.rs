#![allow(mixed_script_confusables)]
#![allow(confusable_idents)]
#![feature(const_trait_impl)]
#![feature(box_patterns)]

#[cfg(test)]
mod tests;

use proof_core::{
    error,
    expr::{Binder, BinderType, Expression, SortRank},
    goals::{find_goals, Constraint, TypeConstraint},
    result::{Result, ResultExt},
    scope::DefinitionScope,
    types::Context,
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
        let goals = find_goals(self.context(), &constraint).unwrap_chain();

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
    scope_test();
}

fn scope_test() {
    let mut scope = DefinitionScope::new();

    def!(scope, Bot := for ?? : *. ??);

    def!(scope, Id := for ?? : *. for x : ??. ??);
    def!(scope, id := fun ?? : *. fun x : ??. x);

    def!(scope, let :=
        fun ?? : *.
        fun x : ??.
        fun ?? : *.
        fun f : ?? => ??.
        f x
    );

    def!(scope, Value := fun ?? : *. (?? => ??) => ??);
    show!(scope, Value);

    def!(scope, value := fun ?? : *. fun v : ??. fun h : ?? => ??. h v);

    check!(scope, (value) : (for ?? : *. ?? => (Value ??)));

    def!(scope, extract := fun ?? : *. fun k : Value ??. k (id ??));
    show_type!(scope, extract);

    // match_value ?? : Value ?? => for ?? : *. (?? => ??) => ??
    def!(scope, match_value := fun ?? : *. fun v : Value ??. fun ?? : *. fun f : ?? => ??. f (extract ?? v));
    show!(scope, match_value);

    // map_value : for ?? : *. for ?? : *. Value ?? => (?? => ??) => Value ??
    def!(scope, map_value := fun ?? : *. fun ?? : *. fun v : Value ??. fun f : ?? => ??. value ?? (f (extract ?? v)));
    show!(scope, map_value);

    def!(scope, const := fun ?? : *. fun ?? : *. fun u : ??. ??);

    def!(scope, Bool := for ?? : *. ?? => ?? => ??);
    show!(scope, Bool);
    
    def!(scope, bool_true := fun ?? : *. fun x : ??. fun y : ??. x);
    check!(scope, (bool_true): (Bool));
    show!(scope, bool_true);
    
    def!(scope, bool_false := fun ?? : *. fun x : ??. fun y : ??. y);
    check!(scope, (bool_false): (Bool));
    show!(scope, bool_false);

    def!(scope, bool_not := fun ?? : *. fun x : Bool ??. fun y : ??. fun z : ??. x z y);
    show!(scope, bool_not);

    def!(scope, Not := fun ?? : *. ?? => Bot);
    show!(scope, Not);

    def!(scope, TheoremNotBot := Not Bot);
    show!(scope, TheoremNotBot);

    def!(scope, not_bot := id Bot);
    check!(scope, (not_bot) : (TheoremNotBot));

    def!(scope, And := fun ?? : *. fun ?? : *. for ?? : *. (?? => ?? => ??) => ??);
    show!(scope, And);

    def!(scope, pair :=
        fun ?? : *.
        fun ?? : *.
        fun x : ??.
        fun y : ??.
        fun ?? : *.
        fun arg : (?? => ?? => ??). arg x y
    );
    show!(scope, pair);

    def!(scope, fst := fun P : *. fun Q : *. fun x : And P Q. x P (fun a : P. fun b : Q. a));
    show!(scope, fst);

    def!(scope, snd := fun P : *. fun Q : *. fun x : And P Q. x Q (fun a : P. fun b : Q. b));
    show!(scope, snd);

    def!(scope, swap_pair := fun P : *. fun Q : *. fun x : And P Q. pair Q P (snd P Q x) (fst P Q x));
    check!(scope, (swap_pair) : (for P : *. for Q : *. And P Q => And Q P));

    def!(scope, Or := fun ?? : *. fun ?? : *. for ?? : *. (?? => ??) => (?? => ??) => ??);

    def!(scope, left :=
        fun ?? : *.
        fun ?? : *.
        fun x : ??.
        fun ?? : *.
        fun l : ?? => ??.
        fun r : ?? => ??.
            l x
    );

    def!(scope, right :=
        fun ?? : *.
        fun ?? : *.
        fun y : ??.
        fun ?? : *.
        fun l : ?? => ??.
        fun r : ?? => ??.
            r y
    );

    def!(scope, Iff := fun P : *. fun Q : *. And (P => Q) (Q => P));
    def!(scope, intro_iff := fun P : *. fun Q : *. pair (P => Q) (Q => P));
    check!(scope, (intro_iff) : (for P : *. for Q : *. (P => Q) => (Q => P) => Iff P Q));

    def!(scope, Eq :=
        fun ?? : *.
        fun x : ??.
        fun y : ??.
        for P : ?? => *. Iff (P x) (P y)
    );
    show!(scope, Eq);

    def!(scope, refl := fun ?? : *. fun x : ??. fun P : ?? => *. intro_iff (P x) (P x));

    // def!(scope, EqNat := Eq Nat);

    check!(scope, (left) : (for ?? : *. for ?? : *. ?? => Or ?? ??));

    // scope.show_all().unwrap_chain();
    println!();

    // A => A ??? ??A
    def!(scope, TheoremLEM := for A : *. A => Or A (Not A));
    def!(scope, lem :=
        fun A : *.
        fun x : A.
        left A (Not A) x
    );
    check!(scope, (lem): (TheoremLEM));
    show!(scope, lem);

    // ??? => A
    def!(scope, TheoremPOE := for A : *. (for ?? : *. ??) => A);
    def!(scope, poe :=
        fun A : *.
        fun bottom : (for ?? : *. ??).
        bottom A
    );
    check!(scope, (poe): (TheoremPOE));
    show!(scope, poe);

    // A => ????A
    def!(scope, TheoremDoubleNeg := for A : *. A => Not (Not A));
    def!(scope, double_neg :=
        fun A : *.
        fun a : A.
        fun not_a : Not A.
        not_a a
    );
    check!(scope, (double_neg): (TheoremDoubleNeg));
    show!(scope, double_neg);

    // ??(A ??? ??A)
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

    // P ??? Q => Q ??? P
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
    check!(scope, (and_symm) : (TheoremAndSymm));

    // P ??? Q => Q ??? P
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
    check!(scope, (or_symm) : (TheoremOrSymm));

    // P ??? (Q ??? R) => (P ??? Q) ??? R
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
    check!(scope, (and_assoc) : (TheoremAndAssoc));

    // P ??? (Q ??? R) => (P ??? Q) ??? R
    def!(scope, TheoremOrAssoc :=
        for P : *. for Q : *. for R : *. Or P (Or Q R) => Or (Or P Q) R
    );
    show!(scope, TheoremOrAssoc);
    def!(scope, or_assoc :=
        fun P : *. fun Q : *. fun R : *.
        fun h : Or P (Or Q R).
        fun ?? : *.
        fun case_p_or_q : Or P Q => ??.
        fun case_r : R => ??.
        h ??
            (fun p : P. case_p_or_q (left P Q p))
            (fun q_or_r : Or Q R. q_or_r ??
                (fun q : Q. case_p_or_q (right P Q q))
                (fun r : R. case_r r)
            )
    );
    check!(scope, (or_assoc) : (TheoremOrAssoc));

    // (P <=> Q) => P => Q
    def!(scope, TheoremIffForward := for P : *. for Q : *. Iff P Q => P => Q);
    show!(scope, TheoremIffForward);
    def!(scope, iff_forward :=
        fun P : *. fun Q : *.
        ?
    );
    goals!(scope, [iff_forward] : [TheoremIffForward]);

    // ??(P ??? Q) => ??P ??? ??Q
    def!(scope, TheoremNegConjToDisj :=
        for P : *. for Q : *. Not (And P Q) => Or (Not P) (Not Q)
    );
    show!(scope, TheoremNegConjToDisj);
    /* def!(scope, neg_conj_to_disj :=
        fun P : *. fun Q : *.
        fun not_p_and_q : Not (And P Q).
        fun ?? : *.
        fun case_not_p : Not P => ??.
        fun case_not_q : Not Q => ??.
        (
            fun h : Or (Not (And P Q)) (Not (Not (And P Q))).
            h ??
                (fun _ : Not (And P Q). ?)
                (
                    fun _ : Not (Not (And P Q)).
                    double_neg
                )
        )
        (lem (Not (And P Q)) not_p_and_q)
    ); */
    return ();

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
                //      : (??R : *. (P => Q => R) => R) => Bot
                //
                // goal : (Or (Not P) (Not Q))
                //      : ??R : *. (Not P => R) => (Not Q => R) => R
                //
                fun 
            )
    ); */

    def!(scope, Symm := fun Op : (for ?? : *. ?? => ?? => *). for ?? : *. for x : ??. for y : ??. Op ?? x y => Op ?? y x);
    def!(scope, SymmT := fun Op : * => * => *. for ?? : *. for ?? : *. Op ?? ?? => Op ?? ??);

    def!(scope, TheoremEqSymm := Symm Eq);
    def!(scope, eq_symm :=
        fun ?? : *.
        fun x : ??.
        fun y : ??.
        fun x_eq_y : Eq ?? x y.
        fun P : (?? => *).
        swap_pair (P x => P y) (P y => P x) (x_eq_y P)
    );
    check!(scope, (eq_symm): (TheoremEqSymm));
    show!(scope, eq_symm);

    def!(scope, Nat := for ?? : *. (?? => ??) => ?? => ??);
    def!(scope, nat_zero := fun ?? : *. fun f : ?? => ??. fun x : ??. x);
    check!(scope, (nat_zero): (Nat));
    def!(scope, nat_one := fun ?? : *. fun f : ?? => ??. fun x : ??. f x);
    def!(scope, nat_succ := fun n : Nat. fun ?? : *. fun f : ?? => ??. fun x : ??. f (n ?? f x));
    check!(scope, (nat_succ) : (Nat => Nat));

    def!(scope, nat_pred :=
        fun n : Nat.
        fun ?? : *.
        fun f : ?? => ??.
        fun x : ??.
        n ((?? => ??) => ??) (fun g : (?? => ??) => ??. fun h : ?? => ??. h (g f)) (fun y : ?? => ??. x) (fun y : ??. y)
    );
    check!(scope, (nat_pred) : (Nat => Nat));

    // Note: n ?? f : ?? => ?? which applies f n-times.
    // Example: 3 ?? f x = f (f (f x))

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
        fun ?? : *.
            n (?? => ?? => ??)
                (fun x : ?? => ?? => ??. bool_false ??)
                (bool_true ??)
    );

    check!(scope, (nat_is_zero) : (Nat => Bool));

    show!(scope, Bot);
    show!(scope, Not);
    show!(scope, And);
    show!(scope, Or);

    show!(scope, left);
    show!(scope, right);

    // The integers
    def!(scope, Int := for ?? : *. (Id => ??) => (Nat => ??) => (Nat => ??) => ??);
    show!(scope, Int);
    def!(scope, int_zero :=
        fun ?? : *.
        fun zero : Id => ??.
        fun _ : Nat => ??.
        fun _ : Nat => ??.
        zero id
    );
    check!(scope, (int_zero): (Int));

    def!(scope, int_one :=
        fun ?? : *.
        fun zero : Id => ??.
        fun pos : Nat => ??.
        fun neg : Nat => ??.
        pos nat_zero
    );
    check!(scope, (int_one): (Int));

    def!(scope, int_neg_one :=
        fun ?? : *.
        fun zero : Id => ??.
        fun pos : Nat => ??.
        fun neg : Nat => ??.
        neg nat_zero
    );
    check!(scope, (int_neg_one): (Int));

    def!(scope, int_neg :=
        fun n : Int.
        fun ?? : *.
        n ((Id => ??) => (Nat => ??) => (Nat => ??) => ??)
            // If n = 0
            (fun n_zero : Id. int_zero ??)

            // If n > 0
            (fun n_pos : Nat.
                fun zero : Id => ??.
                fun pos : Nat => ??.
                fun neg : Nat => ??.
                neg n_pos
            )

            // If n < 0
            (fun n_neg : Nat.
                fun zero : Id => ??.
                fun pos : Nat => ??.
                fun neg : Nat => ??.
                pos n_neg
            )
    );

    check!(scope, (int_neg) : (Int => Int));

    def!(scope, int_is_zero :=
        fun n : Int.
        fun ?? : *.
        n (?? => ?? => ??)
            // If n = 0
            (fun n_zero : Id. bool_true ??)

            // If n > 0
            (fun n_pos : Nat. bool_false ??)

            // If n < 0
            (fun n_neg : Nat. bool_false ??)
    );

    check!(scope, (int_is_zero) : (Int => Bool));

    def!(scope, int_is_neg :=
        fun n : Int.
        fun ?? : *.
        n (?? => ?? => ??)
            // If n = 0
            (fun n_zero : Id. bool_false ??)

            // If n > 0
            (fun n_pos : Nat. bool_false ??)

            // If n < 0
            (fun n_neg : Nat. bool_true ??)
    );

    check!(scope, (int_is_neg) : (Int => Bool));

    def!(scope, int_is_pos :=
        fun n : Int.
        fun ?? : *.
        n (?? => ?? => ??)
            // If n = 0
            (fun n_zero : Id. bool_false ??)

            // If n > 0
            (fun n_pos : Nat. bool_false ??)

            // If n < 0
            (fun n_neg : Nat. bool_true ??)
    );

    check!(scope, (int_is_pos) : (Int => Bool));

    check_eq!(scope, (int_neg int_zero) = (int_zero));
    check_eq!(scope, (int_neg int_one) = (int_neg_one));
    check_eq!(scope, (int_neg int_neg_one) = (int_one));

    // The successor function
    def!(scope, int_succ :=
        fun n : Int.
        fun ?? : *.
        n ((Id => ??) => (Nat => ??) => (Nat => ??) => ??)
            // If n = 0
            (fun n_zero : Id. int_one ??)

            // If n > 0
            (
                fun n_pos : Nat.
                fun zero : Id => ??.
                fun pos : Nat => ??.
                fun neg : Nat => ??.
                pos (nat_succ n_pos)
            )

            // If n < 0
            (
                fun n_neg : Nat.
                (nat_is_zero n_neg) ((Id => ??) => (Nat => ??) => (Nat => ??) => ??)
                    // If n_neg = 0
                    (int_zero ??)

                    // If n_neg > 0
                    (
                        fun zero : Id => ??.
                        fun pos : Nat => ??.
                        fun neg : Nat => ??.
                        neg (nat_pred n_neg)
                    )
            )
    );

    check!(scope, (int_succ) : (Int => Int));

    def!(scope, int_pred :=
        fun n : Int.
        fun ?? : *.
        n ((Id => ??) => (Nat => ??) => (Nat => ??) => ??)
            // If n = 0
            (fun n_zero : Id. int_neg_one ??)

            // If n > 0
            (
                fun n_pos : Nat.
                (nat_is_zero n_pos) ((Id => ??) => (Nat => ??) => (Nat => ??) => ??)
                    // If n_pos = 0
                    (int_zero ??)

                    // If n_pos > 0
                    (
                        fun zero : Id => ??.
                        fun pos : Nat => ??.
                        fun neg : Nat => ??.
                        pos (nat_pred n_pos)
                    )
            )

            // If n < 0
            (
                fun n_neg : Nat.
                fun zero : Id => ??.
                fun pos : Nat => ??.
                fun neg : Nat => ??.
                neg (nat_succ n_neg)
            )
    );

    check!(scope, (int_pred) : (Int => Int));

    def!(scope, int_match :=
        fun n : Int.
        fun ?? : *.
        fun zero : ??.
        fun pos : ??.
        fun neg : ??.
        n ??
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
        fun ?? : *.
        fun f : ?? => ??.
        fun n : Nat.
        n ?? f
    );

    check!(scope, (repeat) : (for ?? : *. (?? => ??) => Nat => (?? => ??)));

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
        for ?? : *.
        for R : ?? => ?? => *.
        (for a : ??. R a a) =>
        (for a : ??. for b : ??. for c : ??. And (R a b) (R b c) => (R a c)) =>
        (for a : ??. for b : ??. for c : ??. And (R a b) (R b a) => Eq ?? a b) =>
        (for a : ??. for b : ??. Or (R a b) (R b a))
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
        // m < n <=> ???x : ????. m - x = 0 ??? n - x = 1
        for C : *. (
            for x : Nat.
            And
                (EqNat (nat_sub m x) (nat_zero))
                (EqNat (nat_sub n x) nat_one)
            => C
        ) => C
    );
    show!(scope, LTNat);

    def!(scope, GENat :=
        fun m : Nat.
        fun n : Nat.
        Not (LTNat m n)
    );
    show!(scope, GENat);

    // ???m n : ????. m = n => m >= n
    def!(scope, TheoremNatEqThenGE :=
        for m : Nat. for n : Nat. EqNat m n => GENat m n
    );

    def!(scope, nat_eq_then_ge :=
        fun m : Nat. fun n : Nat.
        // goal : m = n => m >= n
        fun m_eq_n : EqNat m n.
        // goal : m >= n
        //      : ??(m < n)
        //      : m < n => ???
        fun m_lt_n : LTNat m n.
        // m_lt_n : for C : *. (
        //     for x : Nat.
        //     And
        //         (EqNat (nat_sub m x) (nat_zero))
        //         (EqNat (nat_sub n x) nat_one)
        //     => C
        // ) => C
        // goal : ???
        m_lt_n
            (Bot)
            (
                // goal: (
                //     for x : Nat.
                //     And
                //         (EqNat (nat_sub m x) (nat_zero))
                //         (EqNat (nat_sub n x) nat_one)
                //     => Bot
                // ) => Bot
                fun _ : // ???x : ????. ??((m - x = 0) ??? (n - x = 1))
                    for x : Nat.
                    Not (
                        And
                            (EqNat (nat_sub m x) (nat_zero))
                            (EqNat (nat_sub n x) nat_one)
                    ).
                    // goal : ???
                    
            )
    );
    // check!(scope, (nat_eq_then_ge) : (TheoremNatEqThenGE));

    /* def!(scope, zero_ge_zero :=
        fun 
    );
    check!() */

    def!(scope, ind_ge_zero :=
        fun zero_case : ?.
        fun ind_case : ?.
        fun x : Nat.
        ?
    );
    // check!(scope, (ind_ge_zero) : (Ind ));

/*     def!(scope, Set := for ?? : *. ?? => *);
    show!(scope, Set);

    def!(scope, EmptySet := fun ?? : *. fun x : ??. Bot);
    show!(scope, EmptySet);
    check!(scope, (EmptySet) : (Set));

    def!(scope, UniversalSet := fun ?? : *. fun x : ??. Id);
    show!(scope, UniversalSet);
    check!(scope, (UniversalSet) : (Set));

    def!(scope, ElementOf :=
        fun ?? : *.
        fun x : ??.
        fun S : Set.
        S ?? x
    );
    show!(scope, ElementOf);
    check!(scope, (ElementOf) : (for ?? : *. ?? => Set => *));

    def!(scope, Subset :=
        fun A : Set.
        fun B : Set.
        for ?? : *.
        for x : ??.
        ElementOf ?? x A => ElementOf ?? x B
    );
    show!(scope, Subset);
    check!(scope, (Subset) : (Set => Set => *));
    
    // The empty set is a subset of all sets.
    def!(scope, TheoremEmptySetSubsetAll := for S : Set. Subset EmptySet S);
    show!(scope, TheoremEmptySetSubsetAll);

    def!(scope, empty_set_subset_all :=
        fun S : Set.
        fun ?? : *.
        fun x : ??.
        poe (S ?? x)
    );
    check!(scope, (empty_set_subset_all) : (TheoremEmptySetSubsetAll));

    // Every set is a subset of the universal set.
    def!(scope, TheoremAllSubsetUniversal := for S : Set. Subset S UniversalSet);
    show!(scope, TheoremAllSubsetUniversal);

    def!(scope, all_subset_universal :=
        fun S : Set.
        fun ?? : *.
        fun x : ??.
        fun P : S ?? x.
        id
    );
    check!(scope, (all_subset_universal) : (TheoremAllSubsetUniversal));

    // Every set is a subset of itself.
    def!(scope, TheoremSetSubsetSelf := for S : Set. Subset S S);
    show!(scope, TheoremSetSubsetSelf);

    def!(scope, set_subset_self :=
        fun S : Set.
        fun ?? : *.
        fun x : ??.
        id (S ?? x)
    );
    check!(scope, (set_subset_self) : (TheoremSetSubsetSelf));

    def!(scope, SetEq :=
        fun A : Set.
        fun B : Set.
        And (Subset A B) (Subset B A)
    );

    def!(scope, ComplementSet :=
        fun A : Set.
        fun ?? : *.
        fun x : ??.
        Not (ElementOf ?? x A)
    );
    check!(scope, (ComplementSet) : (Set => Set));

    // There are no elements in ???
    def!(scope, TheoremNothingInEmptySet := for ?? : *. for x : ??. Not (ElementOf ?? x EmptySet));
    show!(scope, TheoremNothingInEmptySet);

    def!(scope, nothing_in_empty_set := fun ?? : *. fun x : ??. not_bot);

    // ???' = U
    def!(scope, TheoremComplementEmptyEqUniversal := SetEq (ComplementSet EmptySet) UniversalSet);
    show!(scope, TheoremComplementEmptyEqUniversal);

    def!(scope, complement_empty_eq_universal :=
        // Since A = B => A ??? B ??? B ??? A
        // We start by constructing the pair (???' ??? U, U ??? ???')
        pair
            (Subset (ComplementSet EmptySet) UniversalSet)
            (Subset UniversalSet (ComplementSet EmptySet))

            // S ??? U for all S, so ???' ??? U
            (all_subset_universal (ComplementSet EmptySet))

            // U ??? ???'
            (
                fun ?? : *.
                fun x : ??.
                fun _ : Id.
                not_bot
            )
    );
    check!(scope, (complement_empty_eq_universal) : (TheoremComplementEmptyEqUniversal));

    def!(scope, SetIntersection :=
        fun A : Set.
        fun B : Set.
        fun ?? : *.
        fun x : ??.
        And (ElementOf ?? x A) (ElementOf ?? x B)
    );
    show!(scope, SetIntersection);
    check!(scope, (SetIntersection) : (Set => Set => Set));

    def!(scope, SetUnion :=
        fun A : Set.
        fun B : Set.
        fun ?? : *.
        fun x : ??.
        Or (ElementOf ?? x A) (ElementOf ?? x B)
    );
    show!(scope, SetUnion);
    check!(scope, (SetUnion) : (Set => Set => Set));

    def!(scope, SmallSet :=
        fun ?? : *. ?? => *
    );
    show!(scope, SmallSet);

    def!(scope, Comprehension :=
        fun A : Set.
        fun ?? : *.
        fun ?? : ?? => *.
        for x : ??.
        ElementOf ?? x A => ?? x
    );
    show!(scope, Comprehension);
    // check!(scope, (Comprehension) : (Set => for ?? : *. SmallSet ??));

    show!(scope, Comprehension UniversalSet Int (fun x : Int. Eq Int x x));

    def!(scope, PairSet :=
        fun ?? : *.
        fun x : ??.
        fun y : ??.
        fun z : ??.
        ?
    );

    def!(scope, NonZeroInt :=
        for ?? : *. (for z : Int. Not (Eq Int z int_zero)) => ??
    );
    show!(scope, NonZeroInt); */

    /* def!(scope, Rational :=
        for ?? : *.
        ()
    ); */

    def!(scope, inter :=
        fun A : *.
        fun ?? : (A => *) => *.
        fun x : A.
        for P : A => *.
        ?? P => P x
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
