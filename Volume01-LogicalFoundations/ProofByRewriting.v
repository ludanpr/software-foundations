(* Proof by Rewriting
 *
 * Instead of making a universal claim about all numbers `n` and `m`, it talks about
 * a more specialized property that only holds when `n = m`. The arrow symbol is
 * pronounced "imples".
 *)

(* As before, we need to be able to reason by assuming we are given such numbers n and
 * m. We also need to assume the hypothesis n = m. The intros tactic will serve to move
 * all three of these from the goal into assumptions in the current context.
 *
 * Since n and m are arbitrary numbers, we can't just use simplification to prove this
 * theorem. Instead, we prove it by observing that, if we are assuming n = m, then we
 * can replace n with m in the goal statement and obtain an equality with the same
 * expression on both sides. The tactic that tells Coq to perform this replacement is
 * called rewrite.
 *
 * The first line of the proof moves the universally quantified variables n and m into
 * the context. The second moves the hypothesis n = m into the context and gives it
 * the name H. The third tells Coq to rewrite the current goal (n + n = m + m) by replacing
 * the left side of the equality hypothesis H with the right side:
 *
 *   m = m ->
 *   m + m = m + m.
 *
 *)
Theorem plus_id_example : forall n m : nat,
    n = m ->
    n + n = m + m.
Proof.
  intros n m.    (* move both quantifiers into the context *)
  intros H.      (* move the hypothesis into the context *)
  rewrite -> H.  (* rewrite the goal using the hypothesis *)
  reflexivity. Qed.


Theorem plus_id_exercise : forall n m o : nat,
    n = m ->
    m = o ->
    n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity. Qed.

(* The Check command can also be used to examine the statements of previously
 * declared lemmas and theorems.
 *)
Check mult_n_O.
Check mult_n_Sm.  (* n * m + n = n * S m  <=> n * m + n = n * (m + 1) *)

(* We can use the rewriting tactic with a previously proved theorem instead of
 * a hypothesis from the context. If the statement of the previously proved
 * theorem involves quantified variables, Coq tries to instantiate them by
 * matching with the current goal.
 *)
Theorem mult_n_0_m_0 : forall p q : nat,
    (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.


Theorem mult_n_1 : forall p : nat,
    p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity. Qed.
