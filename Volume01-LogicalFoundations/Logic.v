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

 Up to this point, we have mostly been concerned with proving "positive" statements -- addition is commutative, appending
 lists is associative, etc. Of course, we are sometimes also interested in negative results, demonstrating that some given
 proposition is not true. Such statements are expressed with the logical negation operator ¬.

 To see how negations work, recall the principle of explosion from the [Tactics] chapter, which asserts that, if we assume
 a contradiction, then any other proposition can be derived.

 Following this intuition, we could define ¬ P ("not P") as ∀ Q, P → Q.

 Coq actually makes a slightly different but equivalent choice, defining ¬ P as P → False, where False is a specific un-
 provable proposition defined in the standard library.
 *)
Check not : Prop -> Prop.

(* Since `False` is a contradictory proposition, the principle of explosion also applies to it. If we can get `False` into
 the context, we can use [destruct] on it to complete any goal:
 *)
Theorem ex_falso_quodlibet : forall (P : Prop),
    False -> P.
Proof.
  intros P contra.
  destruct contra. Qed.

Theorem not_implies_our_not : forall (P : Prop),
    ~ P -> (forall (Q : Prop), P -> Q).
Proof.
  intros P. unfold not.
  intros contra Q HP.
  apply contra in HP.
  destruct HP. Qed.

(* Inequality is a very common form of negated statement, so there is a special notation for it:

 ```
 Notation "x <> y" := (~(x = y)).
 ```

 The proposition `0 <> 1` is exactly the same as `~(0 = 1)` -- that is, `not (0 = 1)` -- which unfolds to `(0 = 1) -> False`.
 (We use `unfold not` explicitly here, but generally it can be omitted.)

 To prove an inequality, we may assune the opposite equality and deduce a contradiction from it. Here, the equality `O = S O`
 contradicts the disjointness of constructors `O` and `S`, so [discriminate] takes care of it.
 *)
Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not.
  intros contra.
  discriminate contra. Qed.

(* It takes a little practice to get used to working with negation in Coq. Even though you can see perfectly well why a statement
 involving negation is true, it can be a little tricky at first to see how to make Coq understand it!
 *)

Theorem not_False :
  ~ False.
Proof.
  unfold not.
  intros H. destruct H. Qed.

Theorem contradiction_imples_anything : forall P Q : Prop,
    (P /\ ~ P) -> Q.
Proof.
  unfold not.
  intros P Q [H Hnot].
  apply Hnot in H.
  destruct H. Qed.

Theorem double_neg : forall P : Prop,
    P -> ~ ~ P.
Proof.
  unfold not.
  intros P HP contra.
  apply contra in HP.
  destruct HP. Qed.

Theorem double_neg' : forall P : Prop,
    P -> ~ ~ P.
Proof.
  intros P H. unfold not.
  intros G. apply G.
  apply H. Qed.


Theorem contrapositive : forall (P Q : Prop),
    (P -> Q) -> (~Q -> ~P).
Proof.
  unfold not.
  intros P Q H Qcontra HP.
  apply H in HP.
  apply Qcontra.
  apply HP. Qed.

Theorem not_both_true_and_false : forall P : Prop,
    ~ (P /\ ~P).
Proof.
  unfold not.
  intros P [H Hcontra].
  apply Hcontra. apply H. Qed.

(* De Morgan's Laws, named for Augustus De Morgan, describe how negation interacts with conjunction and disjunction. The following
 law says that "the negation of a disjunction is the conjunction of the negations." There is a corresponding law `de_morgan_not_and_not`
 that we will return to at the end of this chapter.
 *)
Theorem de_morgan_not_or : forall (P Q : Prop),
    ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros P Q. unfold not.
  intros H.
  apply conj.
  - intros HP. apply H. left. apply HP.
  - intros HQ. apply H. right. apply HQ. Qed.

(* Since inequality involves a negation, it also requires a little practice to be able to work with it fluently. Here is one useful
 trick.

 If you are trying to prove a goal that is nonsensical (e.g., the goal state is `false = true`), apply [ex_falso_quodlibet] to change
 the goal to `False`.

 This makes it easier to use assumptions of the form `~P` that may be available in the context -- in particular, assumptions of the
 form `x <> y`.
 *)
Theorem not_true_is_false : forall b : bool,
    b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn:HE.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity. Qed.

(* Since reasoning with [ex_falso_quodlibet] is quite common, Coq provides a built-in tactic, [exfalso], for applying it
 *)
Theorem not_true_is_false' : forall b : bool,
    b <> true -> b = false.
Proof.
  intros [] H.
  - (* true branch *)
    unfold not in H.
    exfalso. apply H.
    reflexivity.
  - (* false branch *)
    reflexivity. Qed.

(** Truth

 Besides `False`, Coq's standard library also defines `True`, a proposition that is trivially true. To prove it, we use
 the constant `I : True`, which is also defined in the standard library:
 *)
Lemma True_is_true : True.
Proof. apply I. Qed.

(* For now, let's take a look at how we can use `True` and `False` to achieve an effect similar to that of the [discriminate]
 tactic, without literally using [discriminate].

 Pattern-matching lets us do different things for different constructors. If the result of applying two different
 constructors were hypothetically equal, then we could use `match` to convert an unprovable statement (like `False`)
 to one that is provable (like `True`).

 To generalize this to other constructors, we simply have to provide an appropriate variant of `disc_fn`. To generalize it
 to other conclusions, we can use [exfalso] to replace them with `False`. The built-in [discriminate] tactic takes care of
 all of this for us!
 *)
Definition disc_fn (n : nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc_example : forall n,
    ~ (O = S n).
Proof.
  intros n H1.
  assert (H2: disc_fn O).
  { simpl. apply I. }
  rewrite H1 in H2. simpl in H2.
  apply H2. Qed.

(** Logical Equivalence

 The handy "is and only if" connective, which asserts that two propositions have the same truth value, is simply the conjunction
 of two implications.
 *)
Module IffPlayground.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q)
                        (at level 95, no associativity)
                        : type_scope.

End IffPlayground.

Theorem iff_sym : forall P Q : Prop,
    (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HPQ HQP].
  split.
  - (* -> *)
    apply HQP.
  - (* <- *)
    apply HPQ. Qed.

Lemma not_true_iff_false : forall b,
    b <> true <-> b = false.
Proof.
  intros b.
  split.
  - (* -> *)
    apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H.
    intros H'. discriminate H'. Qed.

(* The [apply] tactic can also be used with `<->`. We can use [apply] on an <-> in either direction, without explicitly thinking
 about the fact that it is really an `and` underneath
 *)
Lemma apply_iff_example1 : forall P Q R : Prop,
    (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R HPiffQ HQR HP.
  apply HPiffQ in HP.
  apply HQR in HP.
  apply HP. Qed.

Lemma apply_iff_example1' : forall P Q R : Prop,
    (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R HPiffQ HQR HP.
  apply HQR.
  apply HPiffQ.
  apply HP. Qed.

Lemma apply_iff_example2 : forall P Q R : Prop,
    (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
  intros P Q R HPiffQ HPR HQ.
  apply HPR.
  apply HPiffQ.
  apply HQ. Qed.


Theorem or_distributes_over_and : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros [HP | HQandR].
    + apply conj.
      * left. apply HP.
      * left. apply HP.
    + apply conj.
      * right. apply HQandR.
      * right. apply HQandR.
  - intros [[HP | HQ] [HP' | HR]].
    + left. apply HP.
    + left. apply HP.
    + left. apply HP'.
    + right.
      apply conj.
      * apply HQ.
      * apply HR. Qed.

(** Setoids and Logical Equivalence

 Some of Coq's tactics treat iff statements specially, avoiding some low-level proof-state manipulation. In
 particular, [rewrite] and [reflexivity] can be used with iff statements, not just equalities. To enable this
 behavior, we have to import the Coq library that supports it:
 *)
From Coq Require Import Setoids.Setoid.

(* A "setoid" is a set equipped with an equivalence relation -- that is, a relation that is reflexive, symmetric,
 and transitive. When two elements of a set are equivalent according to the relation, [rewrite] can be used to
 replace one by the other.

 We've seen this already with the equality relation `=` in Coq: when `x = y`, we can use [rewrite] to replace
 x with y or vice-versa.

 Similarly, the logical equivalence relation `<->` is reflexive, symmetric, and transitive, so we can use it to
 replace one part of a proposition with another: If `P <-> Q`, then we can use [rewrite] to replace P with Q, or
 vice-versa.

 Here is a simple example demonstrating how these tactics work with iff. First, let's prove a couple of basic
 iff equivalences.
 *)
Lemma mul_eq_0 : forall n m,
    n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O. Qed.

Theorem or_assoc : forall P Q R : Prop,
    P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [HP | [HQ | HR]].
    + left. left. apply HP.
    + left. right. apply HQ.
    + right. apply HR.
  - intros [[HP | HQ] | HR].
    + left. apply HP.
    + right. left. apply HQ.
    + right. right. apply HR. Qed.

(* We can now use these facts with [rewrite] and [reflexivity] to give smooth proofs of statements involving
 equivalences.
 *)
Lemma mul_eq_0_ternary : forall n m p,
    n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros.
  rewrite or_assoc.
  rewrite <- mul_eq_0.
  rewrite mul_eq_0.
  reflexivity. Qed.

(** Existential Quantification

 Another basic logical connective is existential quantification. To say that there is some x of type T such
 that some property P holds on x, we write ∃ x : T, P. As with ∀, the type annotation : T can be omitted if
 Coq is able to infer from the context what the type of x should be.

 To prove a statement of the form ∃ x, P, we must show that P holds for some specific choice for x, known as
 the witness of the existential. This is done in two steps: First, we explicitly tell Coq which witness t we
 have in mind by invoking the tactic [exists t]. Then we prove that P holds after all occurrences of x are
 replaced by `t`.
 *)
Definition Even x := exists n : nat, x = double n.

Lemma four_is_Even : Even 4.
Proof.
  unfold Even. exists 2.
  reflexivity. Qed.

(* Conversely, if we have an existential hypothesis ∃ x, P in the context, we can destruct it to obtain a
 witness x and a hypothesis stating that P holds of x.
 *)
Theorem exists_example_2 : forall n,
    (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm. Qed.

Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
    (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H Hnot.
  destruct Hnot as [x E].
  apply E. apply H. Qed.

Theorem dist_exists_or : forall (X : Type) (P Q : X -> Prop),
    (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - intros [x [HP | HQ]].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [[x HP] | [x HQ]].
    + exists x. left. apply HP.
    + exists x. right. apply HQ. Qed.

(** Programming with Propositions

 )
