(* Proof By Case Analysis
 *
 * Of course, not everything can be proved by simple calculation and rewriting: In
 * general, unknown, hypothetical values can block simplification.
 *)

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => leb n' m'
            end
  end.

Definition ltb (n m : nat) : bool :=
  (leb n m) && (negb (eqb n m)).

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

(* In the following example we need to consider the possible forms of n
 * separately. If n is O, then we can calculate the final result of (n+1) =? 0
 * and check that it is, indeed, false. And if n = S n' for some n', then,
 * although we don't know exactly what number n+1 represents, we can calculate
 * that, at least, it will begin with one S, and this is enough to calculate
 * that, again, (n+1) =? 0 will yield false.
 *
 * The tactic that tells Coq to consider, separately, the cases where n = O and
 * where n = S n' is called `destruct`.
 *
 * The destruct generates two subgoals, which we must then prove, separately, in
 * order to get Coq to accept the theorem.
 *
 * The annotation "as [| n']" is called an intro pattern. It tells Coq what variable
 * names to introduce in each subgoal. In general, what goes between the square
 * brackets is a list of lists of names, separated by |. In this case, the first
 * component is empty, since the O constructor is nullary.
 *
 * In each subgoal, Coq remembers the assumption about n that is relevant for this
 * subgoal -- eiter n = O or n = S n' for some n'. The `eqn:E` annotation tells
 * destruct to give the name E to this equation. Leaving off the eqn:E annotation
 * causes Coq to elide these assumptions in the subgoals.
 *
 * The - signs on the second and thir lines are called bullets, and they mark the
 * parts of the proof that correspond to the two generated subgoals. The part of
 * the proof script that comes after a bullet is the entire proof for the corresponding
 * subgoal.
 *)
Theorem plus_1_neq_0 : forall n : nat,
    (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.

(* It is sometimes useful to invoke destruct inside a subgoal, generating yet
 * more proof obligations. In this case, we use different kinds of bullets to
 * mark goals on different "levels".
 *
 * Besides - and +, we can use * or any repetition of a bullet symbol (e.g.,
 * -- or *** ) as a bullet. We can also enclose sub-proofs in curly braces.
 *)
Theorem andb_commutative : forall b c,
    andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative' : forall b c,
    andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
   { reflexivity. }
   { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.

(* Since curly braces mark both the beginning and the end of a proof, they can
 * be used for multiple subgoal levels, as this example shows.
 *)
Theorem andb3_exchange : forall b c d,
    andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.


(* Exercise *)
Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + intros H. rewrite <- H. reflexivity.
    + intros H. rewrite <- H. reflexivity.
  - destruct c eqn:Ec.
    + intros H. rewrite <- H. reflexivity.
    + intros H. rewrite <- H. reflexivity.
Qed.


