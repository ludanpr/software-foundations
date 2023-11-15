(** * Equiv: Program Equivalence *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Logic.FunctionalExtensionality.
From PLF Require Export Imp.
Set Default Goal Selector "!".

(* In an earlier chapter, we investigated the correctness of a very simple program transformation: the
 `optimize_0plus` function.  The programming language we were considering was the first version of the
 language of arithmetic expressions -- with no variables -- so in that setting it was very easy to define
 what it means for a program transformation to be correct: it should always yield a program that evaluates
 to the same number as the original.

 To talk about the correctness of program transformations for the full Imp language -- in particular,
 assignment -- we need to consider the role of mutable state and develop a more sophisticated notion of
 correctness, which we'll call behavioral equivalence..
 *)

(* For `aexp`'s and `bexp`'s with variables, the definition we want is clear: Two `aexp`'s or `bexp`'s
 are "behaviorally equivalent" if they evaluate to the same result in every state.
 *)
Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.

(* Here are some examples of equivalences of arithmetic and boolean expressions *)
Theorem aequiv_example :
  aequiv <{ X - X }> <{ 0 }>.
Proof.
  intros st. simpl. lia. Qed.

Theorem bequiv_example :
  bequiv <{ X - X = 0 }> <{ true }>.
Proof.
  intros st. unfold beval.
  rewrite aequiv_example. reflexivity. Qed.

(* For commands, the situation is a little more subtle. We can't simply say "two commands are behaviorally
 equivalent if they evaluate to the same ending state whenever they are started in the same initial state,"
 because some commands, when run in some starting states, don't terminate in any final state at all!

 What we need instead is this: two commands are behaviorally equivalent if, for any given starting state,
 they either (1) both diverge or (2) both terminate in the same final state. A compact way to express this
 is "if the first one terminates in a particular state then so does the second, and vice versa."
 *)
Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

Definition refines (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') -> (st =[ c2 ]=> st').


Theorem skip_left : forall c,
    cequiv <{ skip; c }> c.
Proof.
  intros c st st'.
  split; intros H.
  - (* -> *)
    inversion H. Show. subst.
    Show. Abort.
