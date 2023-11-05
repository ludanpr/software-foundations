(* Tactics
 *
 * More Basic Tactics
 *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Poly.

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
  (* `even n = false` added to subgoals, variables in conclusion matched with current goal *)
(*    * `odd (S p) = true` turns into subgoal `even (S p) = false` *)
  apply eq2.
  (* `even n = true` added to subgoals, variables matched with current subgoal *)
(*    * `even (S p) = false` turns into subgoal `even p = true` *)
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
Theorem rev_injective': forall X (l1 l2 : list X),
    rev l1 = rev l2 -> l1 = l2.
Proof.
  intros X l1 l2 H.
  simpl.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive. reflexivity. Qed.
(* We can use [apply] with previously defined theorems, not just hypotheses in the context.
 *)
Theorem rev_exercise1 : forall X (l l' : list X),
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

Lemma cons_eq : forall (X : Type) (x y : X) (l : list X),
    x :: l = y :: l -> x = y.
Proof.
  intros X x y l H.
  injection H as H'. apply H'. Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j -> j = z :: l -> x = y.
Proof.
  intros X x y z l j H1 H2.
  injection H1 as H1' H1''. rewrite -> H1'.
  apply cons_eq with (l := l).
  rewrite -> H1''. symmetry. apply H2. Qed.

(* The principle of disjointness says that two terms beginning with different constructors (like
 * O and S, or true and false) can never be equal. This means that, any time we find ourselves
 * in a context where we've assumed that two such terms are equal, we are justified in concluding
 * anything we want, since the assumption is nonsensical.
 *
 * The [discriminate] tactic embodies this principle: It is used on a hypothesis involving an
 * equality between different constructors, and it solves the current goal immediately.
 *
 * The following examples are instances of a logical principle known as the principle of explosion,
 * which asserts that a contradictory hypothesis entails anything (even manifestly false things!).
 *)
Theorem discriminate_ex1 : forall (n m : nat),
    false = true -> n = m.
Proof.
  intros n m contra.
  discriminate contra. Qed.

Theorem discriminate_ex2 : forall (n : nat),
    S n = O -> 2 + 2 = 5.
Proof.
  intros n contra.
  discriminate contra. Qed.


Example discriminate_ex3 : forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] -> x = z.
Proof.
  intros X x y z l j contra.
  discriminate contra. Qed.

(* For a slightly more involved example, we can use discriminate to make a connection between the
 * two different notions of equality (= and =?) on natural numbers.
 *)
Theorem eqb_0_1 : forall n,
    0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - (* n = O *)
    intros H. reflexivity.
  - (* n = S n' *)
    intros H. simpl. discriminate H. Qed.

(* The injectivity of constructors allows us to reason that forall (n m : nat), S n = S m -> n = m.
 * The converse of this imṕlication is an instance of a more general fact about both constructors
 * and functions, which we will find convenient in a few places below:
 *)
Theorem f_equal : forall (A B : Type) (f : A -> B) (x y : A),
    x = y -> f x = f y.
Proof.
  intros A B f x y eq.
  rewrite -> eq. reflexivity. Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
    n = m -> S n = S m.
Proof.
  intros n m eq.
  apply f_equal. apply eq. Qed.

(* There is also a tactic named `f_equal` that can prove such theorems directly. Given a goal of
 * the form f a1 ... an = g b1 ... bn, the tactic f_equal will produce subgoals of the form
 * f = g, a1 = b1, ..., an = bn. At the same time, any of these subgoals that are simple enough
 * (e.g., immediately provable by reflexivity) will be automatically discharged by f_equal.
 *)
Theorem eq_implies_succ_equal' : forall (n m : nat),
    n = m -> S n = S m.
Proof.
  intros n m eq. f_equal. apply eq. Qed.

(*                             *)
(* Using Tactics on Hypotheses *)
(*                             *)

(* By default, most tactics work on the goal formula and leave the context unchanged. However,
 * most tactics also have a variant that performs a similar operation on a statement in the context.
 *
 * For example, the tactic [simpl in H] performs simplification on the hypothesis [H] in the context.
 *)
Theorem S_inj : forall (n m : nat) (b : bool),
    ((S n) =? (S m)) = b -> (n =? m) = b.
Proof.
  intros n m b H.
  simpl in H. apply H. Qed.

(* Similarly, [apply L in H] matches some conditional statement [L] (of the form X -> Y, say) against
 * a hypothesis [H] in the context. However, unlike ordinary [apply] (which rewrites a goal matching
 * Y into a subgoal X), [apply L in H] matches [H] against X and, if successful, replaces it with Y.
 *
 * In other words, [apply L in H] gives us a form of "forward reasoning": given X -> Y and a hypothesis
 * matching X, it produces a hypothesis matching Y.
 *
 * By contrast, [apply L] is "backward reasoning": it says that if we know X -> Y and we are trying
 * to prove Y, it suffices to prove X.
 *
 * Forward reasoning starts from what is given (premises, previously proven theorems) and iteratively
 * draws conclusions from them until the goal is reached. Backward reasoning starts from the goal and
 * iteratively reasons about what would imply the goal, until premises or previously proven theorems
 * are reached.
 *)
Theorem silly4 : forall (n m p q : nat),
    (n = m -> p = q) -> m = n -> q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H. apply EQ in H.
  symmetry. apply H. Qed.

(*                                  *)
(* Varying the Induction Hypothesis *)
(*                                  *)

(* Sometimes it is important to control the exact form of the induction hypothesis when carrying out
 * inductive proofs in Coq. In particular, we somtimes need to be careful about which of the assumptions
 * we move (using [intros]) from the goal to the context before invoking the [induction] tactic.
 *
 * For example, suppose we want to show that double is injective -- i.e., that it maps different
 * arguments to different results:
 *
 *     Theorem double_injective: ∀ n m,
 *       double n = double m → n = m.
 *
 * The way we start this proof is a bit delicate: if we begin it with
 *
 *     intros n. induction n.
 *
 * then all is well. But if we begin it with introducing both variables
 *
 *      intros n m. induction n.
 *
 * we get stuck in the middle of the inductive case...
 *)
Theorem double_injective_FAILED : forall n m,
    double n = double m -> n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = O *)
    simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *)
      reflexivity.
    + (* m = S m' *)
      discriminate eq.
  - (* n = S n' *)
    intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *)
      discriminate eq.
    + (* m = S m' *)
      apply f_equal.
      (* At this point, the induction hypotesis (IHn') does not give us n' = m' --
       * there is an extra S in the way -- so the goal is not provable.
       *
       * The problem is that, at the point we invoke the induction hypothesis, we
       * have already introduced m into the context.
       *)
      Abort.

(* Trying to carry out this proof by induction on n when m is already in the context doesn't work
 * because we are then trying to prove a statement involving every n but just a single m. A successful
 * proof of double_injective leaves m universally quantified in the goal statement at the point
 * where the induction tactic is invoked on n:
 *)
Theorem double_injective : forall n m,
    double n = double m -> n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. intros m eq. destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - simpl. intros m eq. destruct m as [| m'] eqn:E.
    + discriminate eq.
    + apply f_equal. apply IHn'. (* apply in universally quantified conditional *)
      simpl in eq. injection eq as eq'. apply eq'. Qed.


Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - intros m eq. destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros m eq. destruct m as [| m'] eqn:E.
    + discriminate eq.
    + simpl in eq. f_equal. apply IHn'. apply eq. Qed.

Theorem plus_n_n_injective : forall n m,
    n + n = m + m -> n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - intros m eq. destruct m as [| m'] eqn:E.
    + reflexivity.
    + simpl in eq. discriminate eq.
  - intros m eq. destruct m as [| m'] eqn:E.
    + simpl in eq. discriminate eq.
    + simpl in eq. injection eq as eq'.
      rewrite <- plus_n_Sm in eq'.
      symmetry in eq'.
      rewrite <- plus_n_Sm in eq'.
      symmetry in eq'.
      injection eq' as eq''. apply IHn' in eq''.
      f_equal. apply eq''. Qed.

(* The strategy of doing fewer [intros] before an [induction] to obtain a more general IH
 * doesn't always work by itself; sometimes some rearrangement of quantified variables is
 * needed.
 *
 * Suppose, for example, that we wanted to prove double_injective by induction on m instead
 * of n. In the following theorem, we get stuck again. The problem is that, to do induction
 * on m, we must first introduce n. (And if we simply say induction m without introducing
 * anything first, Coq will automatically introduce n for us!).
 *)
Theorem double_injective_take2_FAILED : forall n m,
    double n = double m -> n = m.
Proof.
  intros n m. induction m as [| m' IHm'].
  - (* m = O *)
    simpl. intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *)
      reflexivity.
    + (* n = S n' *)
      discriminate eq.
  - (* m = S m' *)
    intros eq. destruct n as [| n'] eqn:E.
    + (* n = O *)
      discriminate eq.
    + (* n = S n' *)
      apply f_equal.
      Abort.

(* What can we do about this? One possibility is to rewrite the statement of the lemma so
 * that m is quantified before n. This works, but it's not nice: We don't want to have to
 * twist the statements of lemmas to fit the needs of a particular strategy for proving
 * them! Rather we want to state them in the clearest and most natural way.
 *
 * What we can do instead is to first introduce all the quantified variables and then
 * re-generalize one or more of them, selectively taking variables out of the context and
 * putting them back at the beginning of the goal. The [generalize dependent] tactic does this.
 *)
Theorem double_injective_take2 : forall n m,
    double n = double m -> n = m.
Proof.
  intros n m.              (* `n` and `m` are both in the context *)
  generalize dependent n.  (* Now `n` is back in the goal and we can do induction
                              on `m` and get a sufficiently general IH *)
  induction m as [| m' IHm'].
  - simpl. intros n eq. destruct n as [| n'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros n eq. destruct n as [| n'] eqn:E.
    + discriminate eq.
    + apply f_equal. apply IHm'. injection eq as eq'. apply eq'. Qed.


Theorem nth_error_after_last : forall (n : nat) (X : Type) (l : list X),
    length l = n -> nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| h l' IHl'].
  - intros n eq. destruct n as [| n'] eqn:E.
    + reflexivity.
    + simpl in eq. discriminate eq.
  - intros n eq. destruct n as [| n'] eqn:E.
    + simpl in eq. discriminate eq.
    + simpl in eq. simpl. injection eq as eq'. apply IHl'. apply eq'. Qed.

(*                       *)
(* Unfolding Definitions *)
(*                       *)

(* It sometimes happens that we need to manually unfold a name that has been introduced by
 * a [Definition] so that we can manipulate the expression it denotes. For example, if we
 * define `square` and try to prove a simple fact about it...
 *)
Definition square n := n * n.

Lemma square_mult_FAIL : forall n m,
    square (n * m) = square n * square m.
Proof.
  intros n m.
  (* ...we appear to be stuck: [simpl] doesn't simplify anything *)
  simpl. Abort.

(* To make progress, we can manually `unfold` the definition of `square`: *)
Lemma square_mult : forall n m,
    square (n * m) = square n * square m.
Proof.
  intros n m.
  unfold square.
  rewrite -> mult_assoc.
  assert (H: n * m * n = n * n * m).
  { rewrite -> mul_comm. rewrite -> mult_assoc. reflexivity. }
  rewrite -> H. rewrite -> mult_assoc. reflexivity. Qed.

(* At this point, some deeper discussion of unfolding and simplification is in order. We
 * already have observed that tactics like simpl, reflexivity, and apply will often unfold
 * the definitions of functions automatically when this allows them to make progress.
 * For example, if we define foo m to be the constant 5...
 *)
Definition foo (x : nat) := 5.
(* ... then the [simpl] in the following proof (of the [reflexivity], if we omit the [simpl])
 * will unfold `foo m` to `(fun x => 5) m` and further simplify this expression to just `5`
 *)
Fact silly_fact_1 : forall m,
    foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity. Qed.

(* But this automatic unfolding is somewhat convervative. For example, if we define a slightly
 * more complicated function involving a pattern match...
 *)
Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.
(* ...then the analogous proof will get stuck: *)
Fact silly_fact_2_FAILED : forall m,
    bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* does nothing *)
  Abort.

(* The reason that [simpl] doesn't make progress here is that it notices that, after tentatively
 * unfolding `bar m`, it is left with a match whose scrutinee, `m`, is a variable, so the `match`
 * cannot be simplified further. It is not smart enough to notice that the two branches of the
 * `match` are identical, so it gives up on unfolding `bar m` and leaves it alone.
 *
 * Similarly, tentatively unfolding bar (m+1) leaves a match whose scrutinee is a function application
 * (that cannot itself be simplified, even after unfolding the definition of +), so simpl leaves it
 * alone.
 *
 * At this point, there are two ways to make progress. One is to use destruct m to break the proof
 * into two cases, each focusing on a more concrete choice of m (O vs S _). In each case, the match
 * inside of bar can now make progress, and the proof is easy to complete.
 *)
Fact silly_fact_2 : forall m,
    bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m. destruct m as [| m'] eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity. Qed.

(* This approach works, but it depends on our recognizing that the `match` hidden inside `bar` is
 * what was preventing us from making progress.
 *
 * A more straightforward way forward is to explicitly tell Coq to unfold `bar`:
 *)
Fact silly_fact_2' : forall m,
    bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m as [| m'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

(*                                        *)
(* Using destruct on Compound Expressions *)
(*                                        *)

(* We have seen many examples where [destruct] is used to perform case analysis of the value of
 * some variable. Sometimes we need to reason by cases on the result of some expression. We can
 * also do this with [destruct].
 *
 * After unfolding sillyfun in the above proof, we find that we are stuck on
 *
 *      if (n =? 3) then ... else ....
 *
 * But either n is equal to 3 or it isn't, so we can use destruct (eqb n 3) to let us reason about
 * the two cases.
 *
 * In general, the destruct tactic can be used to perform case analysis of the results of arbitrary
 * computations. If e is an expression whose type is some inductively defined type T, then, for each
 * constructor c of T, `destruct e` generates a subgoal in which all occurrences of e (in the goal
 * and in the context) are replaced by c.
 *)
Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
    sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
  - (* n =? 3 = true *)
    reflexivity.
  - (* n =? 3 = false *)
    destruct (n =? 5) eqn:E2.
    + reflexivity.
    + reflexivity. Qed.


Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
    split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y l l1 l2.
  unfold split.
  induction l as [| h l' IHl'].
  - intros eq. injection eq as eq' eq''.
    rewrite <- eq'. rewrite <- eq''. reflexivity.
  - intros eq. destruct (h :: l') eqn:E.
    + discriminate E.
    + Abort.

(* The `eqn` part of the `destruct` tactic is optional. However, when destructing compound expressions,
 the information recorded by the `eqn:` can actually be critical.
 *)
Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

(* Now suppose that we want to convince Coq that `sillyfun1 n` yields `true` only when `n` is odd. If we
 start the proof like this (with no `eqn:` on the `destruct`)...
 *)
Theorem sillyfun1_odd_FAILED : forall (n : nat),
    sillyfun1 n = true -> odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
  (* stuck... *)
Abort.
(* ... then we are stuck at this point because the context does not contain enough information to prove the
 goal! The problem is that the substitution performed by `destruct` is quite brutal -- in this case, it throws
 away every occurrence of `n =? 3`, but we need to keep some memory of this expression and how it was destructed,
 because we need to be able to reason that, since we are assuming `n =? 3 = true` in this branch of the case
 analysis, it must be that `n = 3`, from which it follows that `n` is odd.

 What we want here is to substitute away all existing occurrences of `n =? 3`, but at the same time add an
 equation to the context that records which case we are in.
 *)
Theorem sillyfun1_odd : forall (n : nat),
    sillyfun1 n = true -> odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  - (* e3 = true *)
    apply eqb_true in Heqe3.
    rewrite -> Heqe3. reflexivity.
  - (* e3 = false *)
    destruct (n =? 5) eqn:Heqe5.
    + (* e5 = true *)
      apply eqb_true in Heqe5.
      rewrite -> Heqe5. reflexivity.
    + (* e5 = false *)
      discriminate eq. Qed.

Theorem bool_fn_applied_thrice : forall (f : bool -> bool) (b : bool),
    f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b eqn:HE1.
  - destruct (f true) eqn:HE2.
    + rewrite HE2. apply HE2.
    + destruct (f false) eqn:HE3.
      * apply HE2.
      * apply HE3.
  - destruct (f false) eqn:HE2.
    + destruct (f true) eqn:HE3.
      * apply HE3.
      * apply HE2.
    + rewrite HE2. apply HE2. Qed.

(** Review

 We've now seen many of Coq's most fundamental tactics. Here are the ones we've seen:

 - [intros]: move hypothesis/variables from goal to context.
 - [reflexivity]: finish the proof (when the goal looks like `e = e`
 - [apply]: prove goal using a hypothesis, lemma, or constructor
 - [apply ... in H]: apply a hypothesis, lemma, or constructor to a
   hypothesis in the context (forward reasoning)
 - [apply ... with ...]: explicitly specify values for variables that
   cannot be determined by pattern matching
 - [simpl]: simplify computations in general
 - [simpl in H]: ... or a hypothesis
 - [rewrite]: use an equality hypothesis (or lemma) to rewrite the goal
 - [rewrite ... in H]: ... or a hypothesis
 - [symmetry]: changes a goal of the form `t = u` into `u = t`
 - [symmetry in H]: changes a hypothesis of the form `t = u` into `u = t`
 - [transitivity y]: prove a goal `x = z` by proving two new subgoals,
   `x = y` and `y = z`
 - [unfold]: replace a defined constant by its right-hand side in the goal
 - [unfold ... in H]: ... or a hypothesis
 - [destruct ... as ...]: case analysis on values of inductively defined types
 - [destruct ... eqn: ...]: specify the name of an equation to be added to
   the context, recording the result of the case analysis
 - [induction ... as ...]: induction on values of inductively defined types
 - [injection ... as ...]: reason by injectivity on equalities between values
   of inductively defined types
 - [discriminate]: reason by disjointness of constructors on equalities between
   values of inductively defined types
 - [assert (H : e)] (or [assert (e) as H]): introduce a "local lemma" `e` and
   call it `H`
 - [generalize dependent x]: move the variable `x` (and anything else that depends
   on it) from the context back to an explicit hypothesis in the goal formula
 - [f_equal]: change a goal of the form `f x = f y` into `x = y`.
 *)


Theorem eqb_sym : forall (n m : nat),
    (n =? m) = (m =? n).
Proof.
  intros n.
  induction n as [|n' IHl'].
  - intros m. destruct m as [|m'] eqn:Em.
    + reflexivity.
    + simpl. reflexivity.
  - intros m. destruct m as [|m'] eqn:Em.
    + simpl. reflexivity.
    + apply IHl'. Qed.

