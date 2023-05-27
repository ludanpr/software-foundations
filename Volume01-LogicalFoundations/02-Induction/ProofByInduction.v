(* Proof By Induction
 *
 * For the `Require Export` commands to work, Coq needs to be able to find a
 * compiled version of the *.v files needed, called *.vo, in a directory
 * associated with the prefix LF.
 *
 * First create a file named _CoqProject containing the following line:
 *
 *   -Q ../01-Basics/ LF
 *
 * This maps the directory ../01-Basics/ to the prefix LF. If we want to
 * be able to compile from command-line, generate a Makefile using the
 * coq_makefile utility:
 *
 *   coq_makefile -f _CoqProject ../01-Basics/*.v *.v -o Makefile
 *)
From LF Require Export BinaryNumerals.
From LF Require Export Booleans.
From LF Require Export DataAndFunctions.
From LF Require Export Numbers.
From LF Require Export Tuples.
From LF Require Export Types.

Theorem add_0_l : forall n : nat,
    0 + n = n.
Proof. simpl. reflexivity. Qed.

(* We can prove that 0 is a neutral element for + on the left using
 * just reflexivity. But the proof that it is also a neutral element
 * on the right can't be done in the same simple way. Just applying
 * reflexivity doesn't work, since the n in n+0 is an arbitrary unknown
 * number, so the match in the definition of + can't be simplified.
 *
 * And reasoning by cases using `destruct n` doesn't get us much further:
 * the branch of the case analysis where we assume n = 0 goes through
 * fine, but in the branch where n = S n' for some n' we get stuck in
 * exactly the same way.
 *
 * To prove interesting fact about numbers, lists, and other inductively
 * defined sets, we often need a more powerful reasoning principle: induction.
 *
 * Recall the principle of induction over natural numbers: If P(n) is
 * some proposition involving a natural number n and we want to show that
 * P holds for all numbers n, we can reason like this:
 *
 *  - show that P(O) holds;
 *  - show that, for any n', if P(n') holds, then so does P(S n');
 *  - conclude that P(n) holds for all n.
 *
 * In Coq, the steps are the same: we begin with the goal of proving P(n)
 * for all n and break it down (by applying the induction tactic) into two
 * separate subgoals: one where we must show P(O) and another where we must
 * show P(n') -> P(S n').
 *
 * In the first subgoal, n is replaced by 0. No new variables are introduced
 * (so the first part of the as... is empty), and the goal becomes 0 = 0 + 0,
 * which follows by simplification.
 *
 * In the second subgoal, n is replaced by S n', and the assumption n' + 0 = n'
 * is added to the context with the name IHn' (i.e., the Induction Hypothesis
 * for n'). These two names are specified in the second part of the as... clause.
 * The goal in this case becomes S n' = (S n') + 0 which simplifies to S n' =
 * S (n' + 0), which in turn follows from IHn'.
 *)
Theorem add_0_r: forall n : nat,
    n + 0 = n.
Proof.
  intros n. induction n as [|n' IHn'].
  reflexivity. (* n = 0 branch *)
  simpl.       (* n = S n' branch *)
  rewrite -> IHn'. reflexivity.
Qed.


Theorem minus_n_n: forall n : nat,
    minus n n = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  (* n = 0 *)
  reflexivity.
  (* n = S n' , so minus (S n') (S n') = 0, assumption is minus n' n' = 0 *)
  simpl.             (* minus n' n' *)
  rewrite -> IHn'.   (* minus n' n' = 0 *)
  reflexivity.
Qed.


Theorem mul_0_r: forall n : nat,
    n * 0 = 0.
Proof.
  induction n as [|n' IHn'].
  reflexivity.
  simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm: forall n m : nat,
    S (n + m) = n + (S m).
Proof.
  induction n as [|n' IHn'].
  induction m as [|m' IHm'].
  (* n and m are 0 *)
  reflexivity.
  (* n is 0, m is S m' *)
  simpl. reflexivity.
  induction m as [|m' IHm'].
  (* n is S n', m is 0 *)
  simpl. rewrite -> IHn'. reflexivity.
  (* n is S n', m is S m' *)
  (* n = S n', m = S m' => *)
  (*  * S (S n' + S m') = S n' + S (S m') *)
  simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comm: forall n m : nat,
    n + m = m + n.
Proof.
  induction n as [|n' IHn'].
  induction m as [|m' IHm'].
  (* 0 + 0 = 0 + 0 *)
  reflexivity.
  (* 0 + m = m + 0 *)
  rewrite -> add_0_l. rewrite -> add_0_r. reflexivity.
  induction m as [|m' IHm'].
  (* n + 0 = 0 + m *)
  rewrite -> add_0_r. rewrite -> add_0_l. reflexivity.
  (* n + m = m + n *)
  (* n = S n', m = S m' => S n' + S m' = S m' + S n' *)
  simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem add_assoc: forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  Admitted.
