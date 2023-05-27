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
  induction n as [|n' IHn'].

  induction m as [|m' IHm'].
  induction p as [|p' IHp'].
  simpl. reflexivity.
  rewrite -> add_0_l. simpl. reflexivity.

  induction p as [|p' IHp'].
  rewrite -> add_0_l. simpl. reflexivity.
  rewrite -> add_0_l. simpl. reflexivity.

  induction m as [|m' IHm'].
  induction p as [|p' IHp'].
  simpl. rewrite -> add_0_r. rewrite -> add_0_r. reflexivity.
  rewrite <- add_0_l. simpl. rewrite -> add_0_r. reflexivity.

  induction p as [|p' IHp'].
  rewrite <- add_0_r. simpl. rewrite -> add_0_r.
  rewrite -> add_0_r. rewrite -> add_0_r. reflexivity.
  simpl. rewrite <- IHn'. reflexivity.
Qed.


Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus: forall n,
    double n = n + n.
Proof.
  induction n as [|n' IHn'].
  simpl. reflexivity.
  (* double S n' = S n' + S n' *)
  simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem eqb_refl: forall n : nat,
    (n =? n) = Datatypes.true.
Proof.
  induction n as [|n' IHn'].
  simpl. reflexivity.
  (* eqb n' n' = true *)
  simpl. rewrite -> IHn'. reflexivity.
Qed.

(* In Coq, as in informal mathematics, large proofs are often broken into se
 * sequence of theorems, with later proofs referring to earlier theorems. But
 * sometimes a proof will involve some miscellaneous fact that is too trivial
 * and of too little general interest to bother giving it its own top-level
 * name. In such cases, it is convenient to be able to simply state and prove
 * the needed "sub-theorem" right at the point where it is used.
 *
 * The assert tactic introduces two sub-goals. The first is the assertion itself;
 * by prefixing it with H: we name the assertion H. The second goal is the same
 * as the one at the point where we invoke assert except that, in the context,
 * we now have the assumption H that n + 0 + 0 = n. That is, assert generates
 * one subgoal where we must prove the asserted fact and a second subgoal where
 * we can use the asserted fact to make progress on whatever we were trying to
 * prove in the first place.
 *)
Theorem mult_0_plus': forall n m : nat,
    (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
  { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_rearrange: forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (n + m = m + n) as H.    (* for the particular n and m we need *)
  { rewrite -> add_comm. reflexivity. }
  rewrite -> H. reflexivity. Qed.

Theorem add_assoc': forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [|n' IHn'].
  reflexivity.
  simpl. rewrite -> IHn'. reflexivity. Qed.
