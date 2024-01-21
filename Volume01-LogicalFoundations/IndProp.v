(** IndProp

 Inductively Defined Propositions
 *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.

(* Example: The Collatz Conjecture

 The Collatz Conjecture is a famous open problem in number theory.

 Its statement is quite simple. First, we define a function f on numbers, as follows:
 *)
Fixpoint div2 (n : nat) :=
  match n with
    O => O
  | 1 => O
  | S (S n) => S (div2 n)
  end.

Definition f (n : nat) :=
  if even n then div2 n
  else (3 * n) + 1.

(* Next, we look at what happens when we repeatedly apply f to some given starting number. For example, f 12
 is 6, and f 6 is 3, so by repeatedly applying f we get the sequence 12, 6, 3, 10, 5, 16, 8, 4, 2, 1.

 The question posed by Collatz was: is the sequence starting from any natural number guaranteed to reach 1
 eventually?

 To formalize this question in Coq, we might try to define a recursive function that calculates the total number
 of steps that it takes for such a sequence to reach 1.
 *)
Fail Fixpoint reaches_1_in (n : nat) :=
  if n =? 1 then true
  else 1 + reaches_1_in (f n).

(* This definition is rejected by Coq's termination checker, since the argument to the recursive call, f n,
 is not "obviously smaller" than n.

 Indeed, this isn't just a pointless limitation: functions in Coq are required to be total, to ensure logical
 consistency.

 Moreover, we can't fix it by devising a more clever termination checker: deciding whether this particular function
 is total would be equivalent to settling the Collatz conjecture!

 Fortunately, there is another way to do it: We can express the concept "reaches 1 eventually" as an inductively
 defined property of numbers:
 *)
Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_done : Collatz_holds_for 1
  | Chf_more (n : nat) : Collatz_holds_for (f n) -> Collatz_holds_for n.

(* What we've done here is to use Coq's `Inductive` definition mechanism to characterize the property "Collatz
 holds for ..." by stating two different ways in which it can hold: (1) Collatz holds for 1 and (2) if Collatz
 holds for f n then it holds for n.

 For particular numbers, we can now argue that the Collatz sequence reaches 1 like this (again, we'll go through
 the details of how it works a bit later in the chapter):
 *)
Example Collatz_holds_for_12 : Collatz_holds_for 12.
Proof.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_done. Qed.

(* The Collatz conjecture then states that the sequence beginning from any number reaches 1:
 *)
Conjecture collatz : forall n, Collatz_holds_for n.


(* Example: Ordering

 A binary relation on a set X is a family of propositions parameterized by two elements of X -- i.e., a proposition
 about pairs of elements of X.

 For example, one familiar binary relation on `nat` is `le`, the less-than-or-equal-to relation. We've already seen
 how to define it as a boolean computation. Here is a "direct" propositional definition.

 The following definition says that there are two ways to show that one number is less than or equal to another: either
 observe that they are the same number, or, if the second has the form `S m`, give evidence that the first is less than
 or equal to `m`.
 *)
Module LePlayground.

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).

Notation "n <= m" := (le n m) (at level 70).

Example le_3_5 : 3 <= 5.
Proof.
  apply le_S. apply le_S. apply le_n. Qed.

End LePlayground.

Module LePlaygroundRes.
(* By "reserving" the notation before defining the `Inductive`, we can use it in the definition
 *)
Reserved Notation "n <= m" (at level 70).

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : n <= n
  | le_S (n m : nat) : n <= m -> n <= (S m)
  where "n <= m" := (le n m).

End LePlaygroundRes.


(* Example: Transitive Closure

 As another example, the transitive closure of a relation R is the smallest relation that contains R and that is transitive.
 *)
Inductive clos_trans {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | t_step (x y : X) : R x y -> clos_trans R x y
  | t_trans (x y z : X) : clos_trans R x y -> clos_trans R y z -> clos_trans R x z.

(* For example, suppose we define a "parent of" relation on a group of people...
 *)
Inductive Person : Type := Sage | Cleo | Ridley | Moss.

Inductive parent_of : Person -> Person -> Prop :=
    po_SC : parent_of Sage Cleo
  | po_SR : parent_of Sage Ridley
  | po_CM : parent_of Cleo Moss.

(* Then we can define "ancestor of" as its transitive closure:
 *)
Definition ancestor_of : Person -> Person -> Prop :=
  clos_trans parent_of.

Example ancestor_of_1 : ancestor_of Sage Moss.
Proof.
  unfold ancestor_of.
  apply t_trans with Cleo.
  - apply t_step. apply po_SC.
  - apply t_step. apply po_CM. Qed.

(* Reflexive and transitive *)
Inductive clos_refl_trans {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | t_refl' (x : X) : R x x -> clos_refl_trans R x x
  | t_step' (x y : X) : R x y -> clos_refl_trans R x y
  | t_trans' (x y z : X) : clos_refl_trans R x y ->
                           clos_refl_trans R y z ->
                           clos_refl_trans R x z.

Inductive bloodline_S : Person -> Person -> Prop :=
    bl_SS : bloodline_S Sage Sage
  | bl_SC : bloodline_S Sage Cleo
  | bl_SR : bloodline_S Sage Ridley.

Definition ancestor_of' : Person -> Person -> Prop :=
  clos_refl_trans bloodline_S.

Example ancestor_of_2 : ancestor_of' Sage Sage.
Proof.
  unfold ancestor_of'.
  apply t_refl'. apply bl_SS. Qed.


(* Example: Permutations

 The familiar mathematical concept of permutation also has an elegant formulation as an inductive relation. For simplicitly,
 let's focus on permutations of lists with exactly three elements.
 *)
Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) : Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) : Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) : Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.

(* This definition says:

    - If `l2` can be obtained from `l1` by swapping the first and second elements, then `l2` is a permutation of `l1`.
    - If `l2` can be obtained from `l1` by swapping the second and third elements, then `l2` is a permutation of `l1`.
    - If `l2` is permutation  of `l1` and `l3` is a permutation of `l2`, then `l3` is a permutation of `l1`.
 *)
Example Perm3_example1 : Perm3 [1;2;3] [2;3;1].
Proof.
  apply perm3_trans with [2;1;3].
  - apply perm3_swap12.
  - apply perm3_swap23. Qed.

(* Example: Evenness (yet again)

 We've already seen two ways of stating a proposition that a number n is even: We can say

    (1) even n = true, or
    (2) exists k, n = double k.

 A third possibility, which we'll use as a running example for the rest of this chapter, is to say that n is even if
 we can establish its evenness from the following rules:

    - The number 0 is even.
    - If n is even, then S (S n) is even.

 To illustrate how this new definition of evenness works, let's imagine using it to show that 4 is even. First, we
 give the rules names for easy reference:

    - Rule ev_0: The number 0 is even.
    - Rule ev_SS: If n is even, then S (S n) is even.

 Now, by rule ev_SS, it suffices to show that 2 is even. This, in turn, is again guaranteed by rule ev_SS as long as
 we can show that 0 is even. But this last fact follows directly from the ev_0 rule.

 We can translate the informal definition of evenness from above into a forma `Inductive` declaration, where each "way
 that a number can be even" corresponds to a separate constructor:
 *)
Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
(* This definition is interestingly different from previous uses of `Inductive`. For one thing, we are defining not a
 `Type` or a function yielding a `Type`, but rather a function from `nat` to `Prop` -- that is, a property of numbers.
 But what is really new is that, because the `nat` argument of `ev` appears to the right of the colon on the first line,
 it is allowed to take different values in the types of different constructors: 0 in the type of ev_0 and S (S n) in the
 type of ev_SS. Accordingly, the type of each constructor must be specified explicitly, and each constructor's type must
 have the form `ev n` for some natural number `n`.

 In contrast, recall the definition of `list`:

       Inductive list (X : Type) : Type :=
          | nil
          | cons (x : X) (l : list X).

  or equivalently:

       Inductive list (X : Type) : Type :=
         | nil : list X
         | cons (x : X) (l : list X) : list X.

 This definition introduces the `X` parameter globally, to the left of the colon, forcing the result of `nil` and `cons`
 to be the same type (i.e., `list X`). But if we had tried to bring `nat` to the left of the colon in defining `ev`, we
 would havbe seen an error:
 *)
Fail Inductive wrong_ev (n : nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS (H : wrong_ev n) : wrong_ev (S (S n)).

(* In an `Inductive` definition, an argument to the type constructor on the left of the colon is called a "parameter",
 whereas an argument on the right is called an "index" or "annotation".

 We can think of this as defining a Coq property `ev : nat -> Prop`, together with "evidence constructors" `ev_0 : ev 0`
 and `ev_SS : forall n, ev n -> ev (S (S n))`.

 These evidence constructors can be though of as "primitive evidence of evenness", and they can be used just like proven
 theorems. In particular, we can use Coq's [apply] tactic with the constructor names to obtain evidence for `ev` of particular
 numbers...
 *)
Theorem ev_4 : ev 4.
Proof.
  apply ev_SS. apply ev_SS.
  apply ev_0. Qed.
(* ... or we can use function application syntax to combine several constructors.
 *)
Theorem ev_4' : ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(* In this way, we can also prove theorems that have hypotheses involving `ev`.
 *)
Theorem ev_plus4 : forall n,
    ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn. Qed.

Theorem ev_double : forall n,
    ev (double n).
Proof.
  intros n. unfold double. induction n as [| n' IHn'].
  - apply ev_0.
  - apply ev_SS. apply IHn'. Qed.

(** Using Evidence in Proofs

 Besides constructing evidence that numbers are even, we can also destruct such evidence, reasoning about how it could have
 been built.

 Defining `ev` with an `Inductive` declaration tells Coq not only that the constructors `ev_0` and `ev_SS` are valid ways to
 build evidence that some number is `ev`, but also that these two constructors are the only ways to build evidence that numbers
 are `ev`.

 In other words, if someone gives us evidence `E` for the assertion `ev n`, then we know that E must be one of two things:

    - E is ev_0 (and n is O), or
    - E is ev_SS n' E' (and n is S (S n'), where E' is evidence for ev n').

 This suggests that it should be possible to analyze a hypothesis of the form `ev n` much as we do inductively defined data
 structures; in particular, it should be possible to argue by case analysis or by induction on such evidence.

 ** Inversion on Evidence

 Suppose we are proving some fact involving a number `n`, and we are given `ev n` as a hypothesis. We already know how to
 perform case analysis on n using [destruct] or [induction], generating separate subgoals for the case where `n = O` and the
 case where `n = S n'` for some n'. But for some proofs we may instead want to analyze the evidence for `ev n` directly.

 As a tool for such proofs, we can formalize the intuitive characterization that we gave above for evidence of `ev n`, using
 [destruct].
 *)
Theorem ev_inversion : forall (n : nat),
    ev n -> (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E. destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0 : ex 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split.
    + reflexivity.
    + apply E'. Qed.

(* Facts like this are often called "inversion lemmas" because they allow us to "invert" some given information to reason about
 all the different ways it could have been derived.

 Here, there two ways to prove `ev n`, and the inversion lemma makes it explicit.

 We can use the inversion lemma that we proved above to help structure proofs:
 *)
Theorem evSS_ev : forall n,
    ev (S (S n)) -> ev n.
Proof.
  intros n H. apply ev_inversion in H.
  destruct H as [H | H].
  - discriminate H.
  - destruct H as [n' [E1 E2]].
    injection E1 as E1'. rewrite E1'. apply E2. Qed.
(* Note how the inversion lemma produces two subgoals, which correspond to the two ways of proving `ev`. The first subgoal is a
 contradiction that is discharged with [discriminate]. The second subgoal makes use of [injection] and [rewrite].

 Coq provides a handy tactic called [inversion] that factors out this common pattern, saving us the trouble of explicitly stating
 and proving an inversion lemma for every `Inductive` definition we make.

 Here, the [inversion] tactic can detect (1) that the first case, where n = 0, does not apply and (2) that the n' that appears
 in the ev_SS case must be the same as n. It includes an "as" annotation similar to [destruct], allowing us to assign names rather
 than have Coq choose them.
 *)
Theorem evSS_ev' : forall n,
    ev (S (S n)) -> ev n.
Proof.
  intros n E. inversion E as [| n' E' Heq].
  apply E'. Qed.

(* The [inversion] tactic can apply the principle of explosion to "obviously contradictory" hypotheses involving inductively defined
 properties, something that takes a bit more work using our inversion lemma. Compare:
 *)
Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [| [m [Hm _]]].
  - discriminate H.
  - discriminate Hm. Qed.

Theorem one_not_even' : ~ ev 1.
Proof.
  intros H. inversion H. Qed.


Theorem SSSSev__even : forall n,
    ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H. apply ev_inversion in H.
  destruct H as [H | H].
  - discriminate H.
  - destruct H as [n' [H1 H2]].
    injection H1 as H1'. rewrite <- H1' in H2.
    apply evSS_ev. apply H2. Qed.

Theorem SSSSev__even' : forall n,
    ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E. inversion E as [| n' E' Heq].
  inversion E' as [| n'' E'' Heq']. apply E''. Qed.

Theorem ev5_nonsense : ev 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H as [| n' H' Heq].
  inversion H' as [| n'' H'' Heq'].
  inversion H'' as [| n''' H''' Heq''].
  Qed.

(* The [inversion] tactic does quite a bit of work. For example, when applied to an equality assumption, it does
 the work of both [discriminate] and [injection]. In addition, it carries out the [intros] and [rewrite] that are
 typically necessary in the case of [injection]. It can also be applied to analyze evidence for arbitrary inductively
 defined propositions, not just equality. As examples, we'll use it to re-prove some theorems from chapter `Tactics`.
 *)
Theorem inversion_ex1 : forall (n m o : nat),
    [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H. inversion H as [[H1 H2]].
  reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
    S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(* Here's how [inversion] works in general:

    - Suppose that name `H` refers to an assumption `P` in the current context, where P has been defined by an
      `Inductive` declaration.
    - Then, for each of the constructors of `P`, [inversion H] generates a subgoal in which `H` has been replaced
      by the specific conditions under which this constructor could have been used to prove `P`.
    - Some of these subgoals will be self-contradictory; [inversion] throws these away.
    - The ones that are left represent the cases that must be proved to establish the original goal. For those
      [inversion] adds to the proof context all equations that must hold of the arguments given to P -- e.g., n'=n
      in the proof evSS_ev.

 The `ev_double` exercise above shows that our new notion of evenness is implied by the two earlier ones (since, by
 `even_bool_prop` in chapter `Logic`, we already know that those are equivalent to each other). To show that all three
 coincide, we just need the following lemma.

 We could try to proceed by case analysis or induction on n. But since ev is mentioned in a premise, this strategy seems
 unpromising, because (as we've noted before) the induction hypothesis will talk about n-1 (which is not even!). Thus,
 it seems better to first try inversion on the evidence for ev. Indeed, the first case can be solved trivially. And we
 can seemingly make progress on the second case with a helper lemma.

 Unfortunately, the second case is harder. We need to show `exists n0, S (S n') = double n0`, but the only available
 assumption is `E'`, which states that `ev n'` holds. Since this isn't directly useful, it seems that we are stuck and
 that performing case analysis on `E` was a waste of time.

 If we look more closely at our second goal, however, we can see that something interesting happened: By performing case
 on `E`, we were able to reduce the original result to a similar one that involves a different piece of evidence for `ev`:
 namely `E'`. More formally, we could finish our proof if we could show that

    exists k', n' = double k',

 which is the same as the original statement, but with `n'` instead of `n`. Indeed, it is not difficult to convince Coq that
 this intermediate result would suffice.
 *)
Lemma ev_Even_firsttry : forall n,
    ev n -> Even n.
Proof.
  unfold Even. intros n E.
  inversion E as [EQ' | n' E' EQ'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *)
    assert (H: (exists k', n' = double k') -> (exists n0, S (S n') = double n0)).
    { intros [k' EQ'']. exists (S k'). simpl.
      rewrite <- EQ''. reflexivity. }
    apply H.
    (* Unfortunately, now we are stuck. To see this clearly, let's move `E'` back into the goal from the hypotheses. *)
    generalize dependent E'.
    (* Now it is obvious that we are trying to prove another instance of the same theorem we set out to prove -- only
     here we are talking about `n'` instead of `n`.
     *)
    Abort.

(** Induction on Evidence

 If this story feels familiar, it is no coincidence: We encountered similar problems in the `Induction` chapter,
 when trying to use case analysis to prove results that required induction. And once again the solution is ...
 induction.

 The behavior of [induction] on evidence is the same as its behavior on data: it causes Coq to generate one subgoal
 for each constructor that could have used to build that evidence, while providing an induction hypothesis for each
 recursive occurrence of the property in question.

 To prove that a property of `n` holds for all even numbers (i.e., those for which `ev n` holds), we can use induction
 on `ev n`. This requires us to prove two things, corresponding to the two ways in which `ev n` could have been constructed.
 If it was constructed by `ev_0`, then `n=0` and the property must hold for 0. If it was constructed by `ev_SS`, then
 the evidence of `ev n` is of the form `ev_SS n' E'`, where `n = S (S n')` and `E'` is evidence for `ev n'`.

 Here, we can see that Coq produced an `IH` that corresponds to `E'`, the single recursive occurrence of `ev` in
 its own definition. Since `E'` mentions `n'`, the induction hypothesis talks about `n'`, as opposed to `n` or some
 other number.
 *)
Lemma ev_Even : forall n,
    ev n -> Even n.
Proof.
  intros n E. induction E as [| n' E' IH].
  - (* E = ev_0 *)
    unfold Even. exists 0. reflexivity.
  - (* E = ev_SS n' E' with IH : Even n' *)
    unfold Even in IH. destruct IH as [k Hk].
    rewrite Hk. unfold Even. exists (S k).
    simpl. reflexivity. Qed.

(* The equivalence between the second and third definitions of evenness now follows *)
Theorem ev_Even_iff : forall n,
    ev n <-> Even n.
Proof.
  intros n. split.
  - apply ev_Even.
  - unfold Even. intros [k Hk].
    rewrite Hk. apply ev_double. Qed.


Theorem ev_sum : forall n m,
    ev n -> ev m -> ev (n + m).
Proof.
  intros n m En. induction En as [| n' En' IH].
  - simpl. intros EQ. apply EQ.
  - simpl. intros H.
    apply ev_SS. apply IH. apply H. Qed.

(* In general, there may be multiple ways of defining a property inductively. For example, here's a (slightly
 contrived) alternative definition of `ev`:
 *)
Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev'_ev : forall n,
    ev' n <-> ev n.
Proof.
  intros n. split.
  - intros E. induction E.
    + apply ev_0.
    + apply (ev_SS 0 ev_0).
    + apply ev_sum. apply IHE1. apply IHE2.
  - intros E. induction E as [| n' E' IH].
    + apply ev'_0.
    + assert (H: S (S n') = 2 + n').
      { simpl. reflexivity. }
      rewrite H. apply ev'_sum.
      * apply ev'_2.
      * apply IH. Qed.

Theorem ev_ev__ev : forall n m,
    ev (n + m) -> ev n -> ev m.
Proof.
  intros n m Emn En. generalize dependent Emn.
  induction En as [| n' En' IH].
  - simpl. intros H. apply H.
  - simpl. intros H. apply (evSS_ev (n' + m)) in H.
    apply IH. apply H. Qed.

(** Inductive Relations

 A proposition parameterized by a number (such as `ev`) can be thought of as a property -- i.e., it defines a
 subset of `nat`, namely those numbers for which the proposition is provable. In the same way, a two-argument
 proposition can be thought of as a relation -- i.e., it defines a set of pairs for which the proposition is
 provable.
 *)
Module Playground.

(* Just like properties, relations can be defined inductively.
 *)
Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).

(* Proofs of facts about <= using the constructors `le_n` and `le_S` follow the same patterns as proofs about
 properties, like `ev` above. We can [apply] the constructors to prove <= goals, and we can use tactics like
 [inversion] to extract information <= hypothesis in the context.

 Here are some sanity checks on the definition. (Notice that, although these are the same kind of simple "unit
 tests" as we gave for the testing functions we wrote in the first few lectures, we must construct their proofs
 explicitly -- simpl and reflexivity don't do the job, because the proofs aren't just a matter of simplifying
 computations.)
 *)
Theorem test_le1 : 3 <= 3.
Proof.
  apply le_n. Qed.

Theorem test_le2 : 3 <= 6.
Proof.
  apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 : (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros H. inversion H. inversion H2. Qed.

(* The "strictly less than" relation n < m can now be defined in terms of `le`
 *)
Definition lt (n m : nat) := lt (S n) m.

Notation "n < m" := (lt n m).

End Playground.

Inductive total_relation : nat -> nat -> Prop :=
  | tot (n m : nat) (H : True) : total_relation n m.

Theorem total_relation_is_total : forall n m,
    total_relation n m.
Proof.
  intros n m. apply tot. reflexivity. Qed.


