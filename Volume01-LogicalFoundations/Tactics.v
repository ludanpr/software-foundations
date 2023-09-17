(* Tactics
 *
 * More Basic Tactics
 *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Poly.
Import Datatypes.

(* The apply tactic
 *
 * We often encounter situations where the goal to be proved is exactly the same as
 * some hyphotesis in the context of some previously proved lemma.
 *)

(* Here, we could finish with "rewrite -> eq. reflexivity."as we have done several
 * times before. Alternatively, we can finish in a single step by using the [apply]
 * tactic.
 *)
Theorem silly1 : forall (n m : nat),
    n = m -> n = m.
Proof.
  intros n m eq.
  apply eq. Qed.

(* The [apply] tactic also works with conditional hyphoteses and lemmas: if the statement
 * being applied is an implication, then the premises of this implication will be added
 * to the list of subgoals needing to be proved.
 *)
Theorem silly2 : forall (n m o p : nat),
    n = m -> (n = m -> [n;o] = [m;p]) -> [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.

(* Typically, when we use [apply H], the statement [H] will begin with a [forall] that
 * introduces some universally quantified variables. When Coq matches the current goal
 * against the conclusion of [H], it will try to find appropriate values for these
 * variables. For example, when we do [apply eq2] in the following proof, the universal
 * variable q in [eq2] gets instantiated with n, and r gets instantited with m.
 *)
Theorem silly2a : forall (n m : nat),
    (n, n) = (m, m) ->
    (forall (q r : nat), (q, q) = (r, r) -> [q] = [r]) ->
    [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.


Theorem silly_ex : forall p,
    (forall n, even n = true -> even (S n) = false) ->
    (forall n, even n = false -> odd n = true) ->
    even p = true -> odd (S p) = true.
Proof.
  intros p eq1 eq2 eq3.
  (* `even n = false` added to subgoals, variables in conclusion matched with current goal
   * `odd (S p) = true` turns into subgoal `even (S p) = false` *)
  apply eq2.
  (* `even n = true` added to subgoals, variables matched with current subgoal
   * `even (S p) = false` turns into subgoal `even p = true` *)
  apply eq1.
  (* apply premise `even p = true` *)
  apply eq3. Qed.

(* To use the [apply] tactic, the (conclusion of the) fact begin applied must match the goal
 * exactly (perhaps after simplification) -- for example, [apply] will not work if the left
 * and right sides of the equality are swapped.
 *)
Theorem silly3 : forall (n m : nat),
    n = m -> m = n.
Proof.
  intros n m H.
  (* We cannot use apply directly, but we can use the [symmetry] tactic, which
   * switches the left and right sides of an equality in the goal. *)
  symmetry. apply H. Qed.


(* TODO: fix
 * Error: The reference _ was not found in the current environment.
 *)
Theorem rev_injective': forall X (l1 l2 : Poly.list X),
    rev l1 = rev l2 -> l1 = l2.
Proof.
  intros X l1 l2 H.
  simpl.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive. reflexivity. Qed.
(* We can use [apply] with previously defined theorems, not just hypotheses in the context.
 *)
Theorem rev_exercise1 : forall X (l l' : Poly.list X),
    l = rev l' -> l' = rev l.
Proof.
  intros X l l' H.
  (* `rev l1 = rev l2` added to subgols, variables in conclusion `l1 = l2` matched
   * with current goal `l' = rev l`, turning into `rev l' = rev rev l` *)
  apply rev_injective'.
  rewrite -> rev_involutive.
  symmetry. apply H. Qed.

(*                         *)
(* The [apply with] Tactic *)
(*                         *)

