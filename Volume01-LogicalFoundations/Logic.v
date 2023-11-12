(* Logic

 Logic in Coq
*)
Set Warnings "-notation-overriden,-parsing".
Set Warnings "-deprecated-hint-without-locality".
Require Nat.
From LF Require Export Tactics.

(* In this chapter, we will see how Coq can be used to carry out other familiar forms
 of logical reasoning.

 Before diving into details, we should talk a bit about the status of mathematical statements
 in Coq. Recall that Coq is a typed language, which means that every sensible expression has
 an associated type. Logical claims are no exception: any statement we might try to prove in
 Coq has a type, namely `Prop`, the type of propositions.
 *)
Check (forall n m : nat, n + m = m + n) : Prop.
(* Note that all syntactically well-formed propositions have type `Prop` in Coq, regardless of
 whether they are true. Simply being a proposition is one thing: being provable is a different
 thing!
 *)
Check 2 = 2 : Prop.
Check 3 = 2 : Prop.
Check forall n : nat, n = 2 : Prop.
(* Indeed, propositions don't just have types -- they are first-class entities that can be manipulated
 in all the same ways as any of the other things in Coq's world.

 So far, we've seen one primary place that propositions can appear: in Theorem (and Lemma and Example)
 declarations.
 *)
Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof.
  reflexivity. Qed.
(* But propositions can be used in other ways. For example, we can give a name to a proposition using
 a `Definition`, just as we give names to other kinds of expressions.
 *)
Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.
(* We can later use this name in any situation where a proposition is expected.
 *)
Theorem plus_claim_is_true :
  plus_claim.
Proof.
  reflexivity. Qed.
(* We can also write parameterized propositions -- that is, functions that take arguments of some type
 and return a proposition.
 *)
Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.
(* In Coq, functions that return propositions are said to define properties of their arguments. For
 instance, here's a (polymorphic) property defining the familiar notion of an injective function.
 *)
Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj :
  injective S.
Proof.
  intros n m H.
  injection H as H'. apply H'. Qed.

(* The familiar equality operator `=` is a (binary) function that returns a `Prop`. The expression
 `n = m` is syntactic sugar for `eq n m` (defined in Coq's standard library using the Notation mechanism).
 Because `eq` can be used with elements of any type, it is also polymorphic:
 *)
Check @eq : forall A : Type, A -> A -> Prop.
(* (Notice that we wrote `@eq` instead of `eq`: The type argument `A` to `eq` is declared as implicit,
 and we need to turn off the inference of this implicit argument to see the full type of `eq`.)
 *)

(** Logical Connectives *)

(* Conjunction

 The conjunction, or logical and, of propositions `A` and `B` is written `A /\ B`; it represents the claim
 that both `A` and `B` are true.

 To prove a conjunction, use the [split] tactic. This will generate two subgoals, one for each part of
 the statement.
 *)
Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.  (* 3 + 4 = 7 *)
  - reflexivity.  (* 2 * 2 = 4 *)
Qed.

(* For any propositions `A` and `B`, if we assume that `A` is true and that `B` is true, we can conclude
 that `A /\ B` is also true. The Coq library provides a function [conj] that does this.
 *)
Check @conj : forall A B : Prop, A -> B -> A /\ B.

(* Since applying a theorem with hypotheses to some goal has the effect of generating as many subgoals
 as there are hypotheses for that theorem, we can apply [conj] to achieve the same effect as [split]
 *)
Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply conj.
  - reflexivity.   (* 3 + 4 = 7 *)
  - reflexivity.   (* 2 * 2 = 4 *)
Qed.

Example and_exercise : forall n m : nat,
    n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m eq.
  apply conj.
  - induction n as [|n' IHn'].
    + reflexivity.
    + discriminate eq.
  - induction m as [|m' IHm'].
    + reflexivity.
    + rewrite add_comm in eq. discriminate eq. Qed.

(* So much for proving conjunctive statements. To go in the other direction -- i.e., to use a conjunctive
 hypothesis to help prove something else -- we employ the destruct tactic.

 When the current proof context contains a hypotheses `H` of the form `A /\ B`, writing [destruct H as [HA HB]]
 will remove `H` from the context and replace it with two new hypotheses: `HA`, stating that `A` is true, and `HB`
 stating that `B` is true.
 *)
Lemma and_example2 : forall n m : nat,
    n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn.
  rewrite Hm.
  reflexivity. Qed.

(* As usual, we can also destruct `H` right when we introduce it, instead of introducing and then destructing it
 *)
Lemma and_example2' : forall n m : nat,
    n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity. Qed.

(* It's important to understand how to work with conjunctive hypotheses because conjunctions often arise from
 intermediate steps in proofs, especially in larger developments.
 *)
Lemma and_example3 : forall n m : nat,
    n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  apply and_exercise in H.
  destruct H as [Hn Hm].
  rewrite Hn.
  reflexivity. Qed.

(* Another common situation is that we know `A /\ B` but in some context we need just `A` or just `B`. In such
 cases we can do a [destruct] (possibly as part of an [intros]) and use an underscore pattern to indicate that
 te unneeded conjunct should just be thrown away.
 *)
Lemma proj1 : forall P Q : Prop,
    P /\ Q -> P.
Proof.
  intros P Q [HP _].
  apply HP. Qed.

Lemma proj2 : forall P Q : Prop,
    P /\ Q -> Q.
Proof.
  intros P Q [_ HQ].
  apply HQ. Qed.

(* Finally, we sometimes need to rearrange the order of conjunctions and/or the grouping of multi-way conjunctions.
 The following commutativity and associativity theorems can be handy in such cases.
 *)
Theorem and_commut : forall P Q : Prop,
    P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - apply HQ.
  - apply HP. Qed.

Theorem and_assoc : forall P Q R : Prop,
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split. split.
  - apply HP.
  - apply HQ.
  - apply HR. Qed.


(** Disjunction

 Another important connective is the disjunction, or logical or, of two propositions: A \/ B is true when either `A`
 or `B` is.

 To use a disjunctive hypothesis in a proof, we proceed by case analysis -- which, as with other data types like `nat`,
 can be done explicitly with [destruct] or implicitly with an [intros] pattern:
 *)
Lemma factor_is_O : forall n m : nat,
    n = 0 \/ m = 0 -> n * m = 0.
Proof.
  (* This pattern implicitly does case analysis on `n = 0 \/ m = 0` *)
  intros n m [Hn | Hm].
  - (* n = 0 *)
    rewrite Hn. reflexivity.
  - (* m = 0 *)
    rewrite mul_comm. rewrite Hm.
    reflexivity. Qed.

(* Conversely, to show that a disjunction holds, it suffices to show that one of its sides holds. This can be done via
 the tactics [left] and [right]. As their names imply, the first one requires proving the left side of the disjunction,
 while the second requires proving the right side.
 *)
Lemma or_intro_1 : forall A B : Prop,
    A -> A \/ B.
Proof.
  intros A B HA.
  left. apply HA. Qed.

Lemma zero_or_succ : forall n : nat,
    n = 0 \/ n = S (pred n).
Proof.
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity. Qed.


Lemma mult_is_O : forall n m,
    n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros [|n'] m H.
  - left. reflexivity.
  - simpl in H. apply and_exercise in H.
    right. apply H. Qed.

Theorem or_commut : forall P Q : Prop,
    P \/ Q -> Q \/ P.
Proof.
  intros P Q [| H].
  - right. apply H.
  - left. apply H. Qed.

(** Falsehood and Negation

 
 *)
