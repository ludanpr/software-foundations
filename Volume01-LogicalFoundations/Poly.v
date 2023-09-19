(* Polymorphism and Higher-Order Functions
 *
 *)
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Lists.

(* Coq supports polymorphic inductive type definitions.
 *
 * A good way of thinking about `list` is that the definition of `list` is
 * a function from `Type`'s to `Inductive` definitions; or, to put it more
 * concisely, `list` is a function from `Type`'s to `Type`'s. For any particular
 * type `X`, the type `list X` is the `Inductive`'ly defined set of lists
 * whose elements are of type `X`.
 *)
Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check list : Type -> Type.

(* The `X` in the definition of `list` automatically becomes a parameter to the
 * constructors `nil` and `cons` -- that is, `nil` and `cons` are now polymorphic
 * constructors; when we use them, we must now provide a first argument that is
 * the type of the list they are building.
 *)
Check (nil nat) : list nat.

(* Similarly, `cons nat` adds an element of type `nat` to a list of type `list nat`.
 *)
Check (cons nat 3 (nil nat)) : list nat.

(* What might the type of `nil` be? We can read off the type `list X` from the
 * definition, but this omits the binding for `X` which is the parameter to `list`.
 * `Type -> list X` does not explain the meaning of `X`. `(X : Type) -> list X` comes
 * closer. Coq's notation for this situation is `forall X : Type, list X`
 *)
Check nil : forall X : Type, list X.

(* Similarly, the type of `cons` from the definition looks like `X -> list X -> list X`,
 * but using this convention to explain the meaning of `X` results in the type
 * `forall X, X -> list X -> list X`
 *)
Check cons : forall X : Type, X -> list X -> list X.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat X x count')
  end.

Example test_repeat1: repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.
Example test_repeat2: repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

(* Type Annotation Inference
 *
 * Let's write the definition of `repeat` again, but this time we won't specify the
 * types of any of the arguments.
 *)
Fixpoint repeat' X x count : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat' : forall X : Type, X -> nat -> list X.
Check repeat : forall X : Type, X -> nat -> list X.

(* Type Argument Synthesis
 *
 * To use a polymorphic function, we need to pass it one or more types in addition to its
 * other arguments. For example, the recursive call in the body of the `repeat` function
 * above must pass along the type `X`. But since the second argument to `repeat` is an
 * element of `X`, it seems entirely obvious that the first argument can only be `X`.
 *
 * Fortunately, Coq permits us to avoid this kind of redundancy. In place of any type
 * argument we can write a "hole" _. When Coq encounters a `_`, it will attempt to unify
 * all locally available information -- the type of the function being applied, the types
 * of the other arguments, and the type expected by the context in which the application
 * appears -- to determine what concrete type should replace the _.
 *
 * This may sound similar to type annotation inference -- and, indeed, the two procedures
 * rely on the same underlying mechanisms, instead of simply omitting the types of some
 * arguments to a function, like
 *
 *    repeat' X x count : list X :=
 *
 * we can also replace the types with holes
 *
 *    repeat' (X : _) (x : _) (count : _) : list X :=
 *
 * to tell Coq to attempt to infer the missing information.
 *)
Fixpoint repeat'' X x count : list X :=
  match count with
  | O => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Example test_repeat''1: repeat'' nat 0 0 = nil nat.
Proof. reflexivity. Qed.
Example test_repeat''2: repeat'' nat 0 3 = cons _ 0 (cons _ 0 (cons _ 0 (nil _))).
Proof. reflexivity. Qed.

(* Implicit Arguments
 *
 * In fact, we can go further and even avoid writing _'s in most cases by telling Coq always
 * to infer the type argument(s) of a given function. The `Arguments` directive specifies the
 * name of the function (or constructor) and then list the (leading) argument names to be
 * treated as implicit, each surrounded by curly braces.
 *)
Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.
(* Now we don't have to supply any type arguments at all in the example:
 *)
Definition list123 := cons 1 (cons 2 (cons 3 nil)).

(* Alternatively, we can declare an argument to be implicit when defining the function itself,
 * by surrounding it in curly braces instead of parens.
 *)
Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | O => nil
  | S count' => cons x (repeat''' x count')
  end.

Example test_repeat'''1: repeat''' 0 0 = nil.
Proof. reflexivity. Qed.
Example test_repeat'''2: repeat''' 0 3 = cons 0 (cons 0 (cons 0 nil)).
Proof. reflexivity. Qed.

(* (Note that we didn't even have to provide a type argument to the
   recursive call to [repeat'''].  Indeed, it would be invalid to
   provide one, because Coq is not expecting it.)

   We will use the latter style whenever possible, but we will
   continue to use explicit [Argument] declarations for [Inductive]
   constructors.  The reason for this is that marking the parameter
   of an inductive type as implicit causes it to become implicit for
   the type itself, not just for its constructors.  For instance,
   consider the following alternative definition of the [list]
   type: *)
Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').


Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => O
  | cons _ l' => S (length l')
  end.

Example test_rev1: rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.
Example test_rev2: rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

(* Supplying Type Arguments Explicitly
 *
 * One small problem with declaring arguments to be implicit is that, once in a while, Coq
 * does not have enough local information to determine a type argument; in such cases, we
 * need to tell Coq that we want to give the argument explicitly just this time. For example,
 * suppose we write this:
 *)
Fail Definition mynil := nil.
(* The `Fail` qualifier that appears before `Definition` can be used with any command, and is
 * used to ensure that that command indeed fails when executed.
 *
 * Here, Coq gives us an error because it doesn't know what type argument to supply to `nil`.
 * We can help it by providing an explicit type declaration:
 *)
Definition mynil : list nat := nil.
(* Alternatively, we can force the implicit arguments to be explicit by prefixing the function
 * name with `@`.
 *)
Check @nil : forall X : Type, list X.
Definition mynil' := @nil nat.

(* Since we have made the constructor type arguments implicit, Coq will know to automatically
 * infer these when we use the notations.
 *)
Notation "x :: y" := (cons x y)
                       (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                       (at level 60, right associativity).


Theorem app_nil_r: forall (X : Type), forall l : list X,
    l ++ [] = l.
Proof.
  intros X l. induction l as [| n l' IHl'].
  - (* l = nil X *)
    reflexivity.
  - (* l = cons X n l' *)
    simpl. rewrite -> IHl'. reflexivity. Qed.

Theorem app_assoc: forall A (l m n : list A),
    l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n. induction l as [| h l' IHl'].
  - (* l = nil A *)
    reflexivity.
  - (* l = cons A n l' *)
    simpl. rewrite -> IHl'. reflexivity. Qed.

Lemma app_length: forall (X : Type) (l1 l2 : list X),
    length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2. induction l1 as [| n l' IHl'].
  - (* l1 = nil X *)
    reflexivity.
  - (* l1 = cons X n l1' *)
    simpl. rewrite -> IHl'. reflexivity. Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil X *)
    simpl. rewrite -> app_nil_r. reflexivity.
  - (* l1 = cons X n l1' *)
    simpl. rewrite -> IHl1'. rewrite -> app_assoc. reflexivity. Qed.

Theorem rev_involutive: forall X : Type, forall l : list X,
    rev (rev l) = l.
Proof.
  intros X l. induction l as [| n l' IHl'].
  - (* l = nil X *)
    reflexivity.
  - (* l = cons X n l' *)
    simpl. rewrite -> rev_app_distr.
    simpl. rewrite -> IHl'. reflexivity. Qed.

(* Polymorphic Pairs
 *
 * Following the same pattern, the definition for pairs of numbers that we gave in the last
 * chapter can be generalized to polymorphic pairs, often called products.
 *)
Inductive prod (X Y : Type) : Type :=
  | pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).
(* The annotation `: type_scope` tells Coq that this abbreviation should only be used when
 * parsing types, not when parsing expressions. This avoids a clash with the multiplication
 * symbol.
 *
 * It is easy at first to get (x,y) and X*Y confused. Remember that (x,y) is a value built
 * from two other values, while X*Y is a type built from two other types. If `x` has type
 * `X` and `y` has type `Y`, then `(x,y)` has type `X*Y`.
 *)
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst (X Y : Type) (p : X*Y) : X :=
  match p with
  | (x, _) => x
  end.

Definition snd (X Y : Type) (p : X * Y) : Y :=
  match p with
  | (_, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(* Takes a list of pairs and returns a pair of lists.
 *)
Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x,y) :: t => match split t with
                  | (t1, t2) => (x :: t1, y :: t2)
                  end
  end.

Example test_split1: @split nat nat [] = ([], []).
Proof. reflexivity. Qed.
Example test_split: split [(1, false);(2, false)] = ([1;2], [false;false]).
Proof. reflexivity. Qed.

(* Polymorphic Options *)
Module OptionPlayground.

Inductive option (X : Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X}.
Arguments None {X}.

End OptionPlayground.


Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Example test_nth_error1: nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2: nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3: nth_error [true] 2 = None.
Proof. reflexivity. Qed.


Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Check @hd_error : forall X : Type, list X -> option X.

Example test_hd_error1: hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2: hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

(*                   *)
(* Functions as Data *)
(*                   *)

(* Functions that manipulate other functions are often called higher-order functions *)
Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

Check @doit3times : forall X : Type, (X -> X) -> X -> X.

Example test_doit3times_1: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.
Example test_doit3times_2: doit3times negb true = false.
Proof. reflexivity. Qed.

(* Filter
 *
 * Takes a list of X's and a predicate on X and "filters" the list, returning
 * a new list containing just those elements for which the predicate returns
 * true.
 *)
Fixpoint filter {X : Type} (test : X -> bool) (l : list X) : list X :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
              else (filter test t)
  end.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example test_filter1: filter even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.
Example test_filter2: filter length_is_1 [[1;2];[3];[4];[5;6;7];[8]] = [[3];[4];[8]].
Proof. reflexivity. Qed.

(* Anonymous Functions
 *
 * We can construct a function "on the fly" without declaring it at the top level
 * or giving it a names.
 *)

Example test_anon_fun': doit3times (fun n => n*n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2': filter (fun l => (length l) =? 1) [[1;2];[3];[4];[5;6;7];[8]]
                              = [[3];[4];[8]].
Proof. reflexivity. Qed.

(* Given a set X, a predicate of type X → bool and a list X, partition should
 * return a pair of lists. The first member of the pair is the sublist of the
 * original list containing the elements that satisfy the test, and the second
 * is the sublist containing those that fail the test. The order of elements
 * in the two sublists should be the same as their order in the original list.
 *)
Definition partition {X : Type} (test : X -> bool) (l : list X) : list X * list X :=
  (filter test l, filter (fun x => negb (test x)) l).

Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

(* Map
 *
 * Another handy higher-order function is called `map`
 *)
Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
Example test_map2: map odd [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.
Example test_map3: map (fun n => [even n; odd n]) [2;1;2;5] = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

Lemma map_assoc: forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
    (map f l1) ++ (map f l2) = map f (l1 ++ l2).
Proof.
  intros X Y f l1 l2. induction l1 as [| n l1 IHl1'].
  - (* l1 = nil X *)
    reflexivity.
  - (* l1 = cons X n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem map_rev: forall (X Y : Type) (f : X -> Y) (l : list X),
    map f (rev l) = rev (map f l).
Proof.
  intros X Y f l. induction l as [| n l' IHl'].
  - (* l = nil X *)
    reflexivity.
  - (* l = cons X n l' *)
    simpl. rewrite <- IHl'.
    simpl. rewrite <- map_assoc. reflexivity. Qed.

(* The function map maps a list X to a list Y using a function of type X → Y.
 * We can define a similar function, flat_map, which maps a list X to a list Y
 * using a function f of type X → list Y. Your definition should work by
 * 'flattening' the results of f.
 *)
Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => app (f h) (flat_map f t)
  end.

Example test_flat_map1: flat_map (fun n => [n;n;n]) [1;5;4] = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.
Example test_flat_map2: flat_map (fun n => [n;n+1;n+2]) [1;5;10] = [1;2;3;5;6;7;10;11;12].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

(* Fold
 *
 * An even more powerful higher-order function is called `fold`. Intuitively, the
 * behavior of the `fold` operator is to insert a given binary operator `f` between
 * every pair of elements in a given list.
 *)
Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Check (fold andb) : list bool -> bool -> bool.

Example test_fold1: fold plus [1;2;3;4] 0 = 10.
Proof. reflexivity. Qed.
Example test_fold2: fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.
Example test_fold3: fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.
Example test_fold4: fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(* Functions That Construct Functions
 *
 * Most of the higher-order functions we have talked about so far take functions as arguments.
 * Let's look at some examples that involve returning functions as the results of other functions.
 *)

Definition constfun {X : Type} (x : X) : nat -> X :=
  fun (k : nat) => x.

Definition ftrue := constfun true.

Example constfun_example1: ftrue 0 = true.
Proof. reflexivity. Qed.
Example constfun_example2: (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(* In fact, the multiple-argument functions we have already seen are also examples of passing
 * functions as data. To see why, recall the type of plus.
 *
 * Each → in this expression is actually a binary operator on types. This operator is right-
 * associative, so the type of plus is really a shorthand for nat → (nat → nat) -- i.e., it
 * can be read as saying that "plus is a one-argument function that takes a nat and returns
 * a one-argument function that takes another nat and returns a nat."
 *)
Check plus : nat -> nat -> nat.

Definition plus3 := plus 3.
Check plus3 : nat -> nat.

Example test_plus3_1: plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3_2: doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3_3: doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

(*                      *)
(* Additional Exercises *)
(*                      *)
Module Exercises.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l O.

Example test_fold_length1: @fold_length nat [] = 0.
Proof. reflexivity. Qed.
Example test_fold_length2: fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct: forall X (l : list X),
    fold_length l = length l.
Proof.
  intros X l. induction l as [| n l' IHl'].
  - (* l = nil X *)
    reflexivity.
  - (* l = cons X n l' *)
    simpl. rewrite <- IHl'. reflexivity. Qed.


Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x y => (f x) :: y) l [].

Example test_fold_map1: fold_map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.
Example test_fold_map2: fold_map odd [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.
Example test_fold_map3: fold_map (fun n => [even n; odd n]) [2;1;2;5]
                        = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.
Example test_fold_map4: fold_map (fun x => x) [] = @nil nat.
Proof. reflexivity. Qed.

Theorem fold_map_correct: forall X Y (f : X -> Y) (l : list X),
    fold_map f l = map f l.
Proof.
  intros X Y f l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite <- IHl'. reflexivity. Qed.

(* Currying
 *
 * The type X → Y → Z can be read as describing functions that take two arguments, one of
 * type X and another of type Y, and return an output of type Z. Strictly speaking, this
 * type is written X → (Y → Z) when fully parenthesized. That is, if we have f : X → Y → Z,
 * and we give f an input of type X, it will give us as output a function of type Y → Z. If
 * we then give that function an input of type Y, it will return an output of type Z. That is,
 * every function in Coq takes only one input, but some functions return a function as output.
 * This is precisely what enables partial application.
 *
 * By contrast, functions of type X × Y → Z -- which when fully parenthesized is written (X × Y)
 * → Z -- require their single input to be a pair. Both arguments must be given at once; there is
 * no possibility of partial application. It is possible to convert a function between these two
 * types. Converting from X × Y → Z to X → Y → Z is called currying, in honor of the logician
 * Haskell Curry. Converting from X → Y → Z to X × Y → Z is called uncurrying.
 *)

Definition prod_curry {X Y Z : Type} (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).
Definition prod_uncurry {X Y Z : Type} (f : X -> Y -> Z) (p : X * Y) : Z :=
  match p with
  | (x, y) => (f x) y
  end.

(* As a (trivial) example of the usefulness of currying, we can use it to shorten one of the
 * examples that we saw above:
 *)
Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Check @prod_curry.    (* forall X Y Z : Type, (X * Y -> Z) -> X -> Y -> Z *)
Check @prod_uncurry.  (* forall X Y Z : Type, (X -> Y -> Z) -> X * Y -> Z *)

Theorem uncurry_curry: forall (X Y Z : Type) (f : X -> Y -> Z) x y,
    prod_curry (prod_uncurry f) x y = f x y.
Proof.
  simpl. reflexivity. Qed.

Theorem curry_uncurry: forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y),
    prod_uncurry (prod_curry f) p = f p.
Proof.
  intros. destruct p.
  simpl. reflexivity. Qed.

(* Churchu Numerals
 *
 * The following exercises explore an alternative way of defining natural numbers using the Church
 * numerals. We can represent a natural number n as a function that takes a function f as a parameter
 * and returns f iterated n times.
 *)
Module Church.

Definition cnat := forall X : Type, (X -> X) -> X -> X.

Definition one : cnat := fun (X : Type) (f : X -> X) (x : X) => f x.
Definition two : cnat := fun (X : Type) (f : X -> X) (x : X) => f (f x).
Definition three : cnat := fun (X : Type) (f : X -> X) (x : X) => f (f (f x)).
Definition zero : cnat := fun (X : Type) (f : X -> X) (x : X) => x.

(* More generally, a number n can be written as fun X f x ⇒ f (f ... (f x) ...), with n occurrences
 * of f. Let's informally notate that as fun X f x ⇒ f^n x, with the convention that f^0 x is just x.
 *
 * Another way to think about the Church representation is that function f represents the successor
 * operation on X, and value x represents the zero element of X. We could even rewrite with those names
 * to make it clearer:
 *)
Definition zero' : cnat := fun (X : Type) (succ : X -> X) (zero : X) => zero.
Definition one' : cnat := fun (X : Type) (succ : X -> X) (zero : X) => succ zero.
Definition two' : cnat := fun (X : Type) (succ : X -> X) (zero : X) => succ (succ zero).

(* If we passed in `S` as `succ` and `O` as `zero`, we'd even get the Peano naturals as a result
 *)
Example zero_church_peano : zero nat S O = 0.
Proof. reflexivity. Qed.
Example one_church_peano : one nat S O = 1.
Proof. reflexivity. Qed.
Example two_church_peano : two nat S O = 2.
Proof. reflexivity. Qed.

End Church.

End Exercises.
