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
  (* `rev l1 = rev l2` added to subgoals, variables in conclusion `l1 = l2` matched
   * with current goal `l' = rev l`, turning into `rev l' = rev rev l` *)
  apply rev_injective'.
  rewrite -> rev_involutive.
  symmetry. apply H. Qed.

(*                         *)
(* The [apply with] Tactic *)
(*                         *)

(* The following silly example uses two rewrites in a row to get from [a;b] to [e;f]. *)
Example trans_eq_example : forall (a b c d e f : nat),
    [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

(* Since this is a common pattern, we might like to pull it out as a lemma that records,
 * once and for all, the fact that equality is transitive.
 *)
Theorem trans_eq : forall (X : Type) (n m o : X),
    n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

(* Now we should be able to use [trans_eq] to prove the above example. However, to do this
 * we need a slight refinement of the [apply] tactic.
 *
 * If we simply tell Coq [apply trans_eq] at this point, it can tell (by matching the goal
 * against the conclusion of the lemma) that it should instantiate X with [nat], n with
 * [a, b], and o with [e, f]. However, the matching process doesn't determine an instantiation
 * for m: we have to supply one explicitly by adding "with (m := [c,d])" to the invocation
 * of apply.
 *
 * Actually, the name m in the with clause is not required, since Coq is often smart enough
 * to figure out which variable we are instantiating. We could instead simply write
 *    apply trans_eq with [c;d].
 *)
Example trans_eq_example' : forall (a b c d e f : nat),
    [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m := [c;d]).
  apply eq1. apply eq2. Qed.

(* Coq also has a built-in tactic [transitivity] that accomplishes the same purpose as applying
 * [trans_eq]. The tactic requires us to state the instantiation we want, just like [apply with]
 * does.
 *)
Example trans_eq_example'' : forall (a b c d e f : nat),
    [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2. Qed.


Example trans_eq_exercise : forall (n m o p : nat),
    m = (minustwo o) -> (n + p) = m -> (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  transitivity m.  (* adds `m = minustwo o` subgoal *)
  apply eq2. apply eq1. Qed.


(*                                            *)
(* The [injection] and [discriminate] Tactics *)
(*                                            *)

(* Recall the definition of natural numbers:
     Inductive nat : Type :=
       | O
       | S (n : nat).
   It is obvious from this definition that every number has one of two forms: either it is the
   constructor O or it is built by applying the constructor S to another number. But there is
   more here than meets the eye: implicit in the definition are two additional facts:
     - The constructor S is injective (or one-to-one). That is, if S n = S m, it must
       be that n = m.
     - The constructors O and S are disjoint. That is, O is not equal to S n for any n.

   Similar principles apply to every inductively defined type: all constructors are injective,
   and the values built from distinct constructors are never equal.

   We can prove the injectivity of S by using the pred function defined in Numbers.v:
 *)
Theorem S_injective : forall (n m : nat),
    S n = S m -> n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite -> H2. rewrite -> H1.
  simpl. reflexivity. Qed.

(* This technique can be generalized to any constructor by writing the equivalent of [pred] -- i.e.,
   writing a function that "undoes" one application of the constructor.

   As a more convenient alternative, Coq provides a tactic called [injection] that allows us to
   exploit the injectivity of any constructor.
 *)
Theorem S_injective' : forall (n m : nat),
    S n = S m -> n = m.
Proof.
  intros n m H.
  (* By writing injection H as Hmn at this point, we are asking Coq
   * to generate all equations that it can infer from H using the
   * injectivity of constructors (in the present example, the equation
   * n = m). Each such equation is added as a hypothesis (with the name
   * Hmn in this case) into the context.
   *)
  injection H as Hmn. apply Hmn. Qed.

(* Here is a more interesting example that shows how [injection] can derive multiple equations at
 * once.
 *)
Theorem injection_ex1 : forall (n m o : nat),
    [n;m] = [o;o] -> n = m.
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite -> H1. rewrite -> H2.
  reflexivity. Qed.

Lemma cons_eq : forall (X : Type) (x y : X) (l : Poly.list X),
    x :: l = y :: l -> x = y.
Proof.
  intros X x y l H.
  injection H as H'. apply H'. Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : Poly.list X),
    x :: y :: l = z :: j -> j = z :: l -> x = y.
Proof.
  intros X x y z l j H1 H2.
  injection H1 as H1' H1''. rewrite -> H1'.
  apply cons_eq with (l := l).
  rewrite -> H1''. symmetry. apply H2. Qed.

(* *)
