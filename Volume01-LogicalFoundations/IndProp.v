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

 *)
