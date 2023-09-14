(* Working with Structured Data - Lists
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
From LF Require Export ProofByInduction.
Module NatList.

(* In an `Inductive` definition, each constructor can take any number
 * of arguments.
 *
 * The following declaration can be read: "The one and only way to
 * construct a pair of numbers is by applying the constructor pair
 * to two arguments of type nat."
 *)
Inductive natprod : Type :=
  | pair (n1 n2 : nat).

Check (pair 3 5) : natprod.

Definition fst (p : natprod) : nat :=
  match p with
    | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
    | pair x y => y
  end.

Compute (fst (pair 3 5)).
Compute (snd (pair 3 5)).

Notation "( x , y )" := (pair x y).

Compute (fst (3, 5)).

Definition fst' (p : natprod) : nat :=
  match p with
    | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
    | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
    | (x,y) => (y,x)
  end.


(* If we state properties of pairs in a slightly peculiar way, we can sometimes
 * complete their proofs with just reflexivity.
 *)
Theorem surjective_pairing' : forall (n m : nat),
    (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.

(* But just `reflexivity` is not enough if we state the lemma in the most natural
 * way. Instead, we need to expose the structure of `p` so that `simpl` can perform
 * the pattern match in `fst` and `snd`. We can do this with destruct.
 *
 * Notice that, unlike its behavior with `nat`'s, where it generates two subgoals,
 * `destruct` generates just one subgoal here. That's because `natprod`'s can only
 * be constructed in one way.
 *)
Theorem surjective_pairing : forall (p : natprod),
    p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m].
  simpl. reflexivity. Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
    (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m].
  simpl. reflexivity. Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
    fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p as [n m].
  simpl. reflexivity. Qed.

(*                  *)
(* Lists of Numbers *)
(*                  *)

(* Generalizing the definition of pairs, we can describe the type of lists of numbers
 * like this: "A list is either the empty list or else a pair of a number and another
 * list."
 *)
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                       (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* Takes a number `n` and a `count` and returns a list of length `count` in which
 * every element is `n`.
 *)
Fixpoint repeat (n count : nat) : natlist :=
  match count with
    | O => nil
    | S count' => n :: (repeat n count')
  end.

(* Calculates the length of a list.
 *)
Fixpoint length (l : natlist) : nat :=
  match l with
    | nil => O
    | h :: t => S (length t)
  end.

(* Concatenates two lists.
 *)
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                       (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

(* Returns the first element of the list *)
Definition hd (default : nat) (l : natlist) : nat :=
  match l with
    | nil => default
    | h :: _ => h
  end.

(* Returns everything but the first element. *)
Definition tl (l : natlist) : natlist :=
  match l with
    | nil => nil
    | _ :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl1: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => match h with
                  | O => nonzeros t
                  | S _ => h :: (nonzeros t)
                end
    end.

Example test_nonzeros1: nonzeros nil = nil.
Proof. reflexivity. Qed.
Example test_nonzeros2: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.


Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => match (odd h) with
                  | Datatypes.true => h :: (oddmembers t)
                  | Datatypes.false => oddmembers t
                end
  end.

Example test_oddmembers1: oddmembers [] = [].
Proof. reflexivity. Qed.
Example test_oddmembers2: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.


Definition countoddmembers (l : natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.


(* Interleaves two lists into one, alternating between elements taken from
 * the first list and elements from the second.
 *)
Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
    | nil, _ => l2
    | _, nil => l1
    | h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
  end.

Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4: alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

(*                *)
(* Bags via Lists *)
(*                *)

(* A bag (or multiset) is like a set, except that each element can appear multiple
 * times rather than just once.
 *)
Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
    | nil => O
    | h :: t => match v =? h with
                  | Datatypes.true => 1 + (count v t)
                  | Datatypes.false => count v t
                end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

(* Multiset sum is similar to set union: `sum a b` contains all the elements of `a`
 * and of `b`.
 *)
Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.


Definition add (v : nat) (s : bag) : bag :=
  v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.


Definition member (v : nat) (s : bag) : bool :=
  match (count v s) with
    | O => false
    | S _ => true
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.


(* When `remove_one` is applied to a bag without the number to remove, it should return
 * the same bag unchanged.
 *)
Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
    | nil => nil
    | h :: t => if v =? h then t else h :: (remove_one v t)
  end.

Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.


Fixpoint remove_all (v : nat) (s : bag) : bag :=
  match s with
    | nil => nil
    | h :: t => if h =? v then (remove_all v t) else h :: (remove_all v t)
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

(* Adding a value to a bag should increase the value's count by one. We state
 * this in the following theorem.
 *)
Theorem add_inc_count: forall (v : nat) (s : bag),
    count v (add v s) = (count v s) + 1.
Proof.
  intros v s.
  assert (H: v =? v = Datatypes.true).
  { induction v as [|v' IHv'].
    simpl. reflexivity.
    simpl. rewrite -> IHv'. reflexivity. }
  simpl. rewrite -> H. rewrite -> add_comm. reflexivity. Qed.

Theorem add_inc_count': forall (v : nat) (s : bag),
    count v (add v s) = (count v s) + 1.
Proof.
  intros v s.
  simpl. rewrite -> eqb_refl. rewrite -> add_comm.
  reflexivity. Qed.


(*                       *)
(* Reasoning About Lists *)
(*                       *)

Theorem nil_app: forall l : natlist,
    [] ++ l = l.
Proof.
  reflexivity. Qed.

(* Here, the `nil` case works because we've chosen to define `tl nil = nil`. Notice
 * that the `as` annotation on the `destruct` tactic here introduces two names, `n`
 * and `l'`, corresponding to the fact that the `cons` constructor for lists takes
 * two arguments (the head and tail of the list it is constructing)
 *)
Theorem tl_length_pred: forall l : natlist,
    pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.

(* Induction on Lists
 *
 * Proofs by induction over datatypes like `natlist` are a little less familiar than
 * standard natural number induction, but the idea is equally simple. Each `Inductive`
 * declaration defines a set of data values that can be built up using the declared
 * constructors. For example, a boolean can be either `true` or `false`; a number can
 * be either `O` or `S` applied to another number; and a list can be either `nil` or
 * `cons` applied to a number and a list. Moreover, applications of the declared
 * constructors to one another are the only possible shapes that elements of an
 * inductively defined set can have.
 *
 * This last fact directly gives rise to a way of reasoning about inductively defined
 * sets: a number is either O or else it is `S` applied to some smaller number; a list
 * is either `nil` or else it is `cons` applied to some number and some smaller list;
 * etc. So, if we have in mind some proposition P that mentions a list `l` and we want
 * to argue that P holds for all lists, we can reason as follows:
 *
 *  * First, show that P is true of `l` when `l` is `nil`.
 *  * Then show that P is true of `l` when `l` is `cons n l'` for some number
 *    `n` and some smaller list `l'`, assuming that P is true for `l'`.
 *
 * For comparison, here is an informal proof of the same theorem.
 *
 * Theorem: For all lists l1, l2, and l3, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
 * Proof: By induction on l1.
 *
 *   First, suppose l1 = []. We must show
 *         ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),
 *   which follows directly from the definition of ++.
 *   Next, suppose l1 = n::l1', with
 *         (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)
 *   (the induction hypothesis). We must show
 *         ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).
 *   By the definition of ++, this follows from
 *         n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),
 *   which is immediate from the induction hypothesis. ☐
 *
 *)
Theorem app_assoc: forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.


(* Reverses a list *)
Fixpoint rev (l : natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => rev t ++ [h]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

(* For something a bit more challenging than the proofs we've seen so far, let's
 * prove that reversing a list does not change its length.
 *
 * For comparison, here are informal proofs of these two theorems:
 *
 * Theorem: For all lists l1 and l2, length (l1 ++ l2) = length l1 + length l2.
 * Proof: By induction on l1.
 *
 *   First, suppose l1 = []. We must show
 *           length ([] ++ l2) = length [] + length l2,
 *   which follows directly from the definitions of length, ++, and plus.
 *   Next, suppose l1 = n::l1', with
 *           length (l1' ++ l2) = length l1' + length l2.
 *   We must show
 *           length ((n::l1') ++ l2) = length (n::l1') + length l2.
 *   This follows directly from the definitions of length and ++ together with the induction hypothesis. ☐
 *
 * Theorem: For all lists l, length (rev l) = length l.
 * Proof: By induction on l.
 *
 *   First, suppose l = []. We must show
 *             length (rev []) = length [],
 *   which follows directly from the definitions of length and rev.
 *   Next, suppose l = n::l', with
 *             length (rev l') = length l'.
 *   We must show
 *             length (rev (n :: l')) = length (n :: l').
 *   By the definition of rev, this follows from
 *             length ((rev l') ++ [n]) = S (length l')
 *   which, by the previous lemma, is the same as
 *             length (rev l') + length [n] = S (length l').
 *   This follows directly from the induction hypothesis and the definition of length. ☐
 *
 *)
Theorem app_length: forall l1 l2 : natlist,
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem rev_length: forall l : natlist,
    length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = n :: l' *)
    simpl. rewrite -> app_length.
    simpl. rewrite -> IHl'.
    rewrite -> add_comm. reflexivity. Qed.

(* Search
 *
 * We've seen that proofs can make use of other theorems we've already proved, e.g., using
 * rewrite. But in order to refer to a theorem, we need to know its name! Indeed, it is often
 * hard even to remember what theorems have been proven, much less what they are called.
 * Coq's Search command is quite helpful with this. Let's say you've forgotten the name of a
 * theorem about rev. The command Search rev will cause Coq to display a list of all theorems
 * involving rev.
 *
Search rev.
 *
 * Or say you've forgotten the name of the theorem showing that plus is commutative. You can
 * use a pattern to search for all theorems involving the equality of two additions.
 *
Search (_ + _ = _ + _).
 *
 * You'll see a lot of results there, nearly all of them from the standard library. To restrict
 * the results, you can search inside a particular module:
 *
Search (_ + _ = _ + _) inside Induction.
 *
 * You can also make the search more precise by using variables in the search pattern instead of
 * wildcards:
 *
Search (?x + ?y = ?y + ?x).
 *
 *)


Theorem app_nil_r: forall l : natlist,
    l ++ [] = l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = n :: l' *)
    simpl. rewrite -> IHl'. reflexivity. Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    simpl. rewrite -> app_nil_r. reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'.
    rewrite -> app_assoc. reflexivity. Qed.

(* An involution is a function that is its own inverse. That is, applying the function
 * twice yield the original input.
 *)
Theorem rev_involutive: forall l : natlist,
    rev (rev l) = l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    simpl. reflexivity.
  - (* l = cons n l' *)
    simpl. rewrite -> rev_app_distr.
    rewrite -> IHl'. reflexivity. Qed.

Theorem app_assoc4: forall l1 l2 l3 l4 : natlist,
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    simpl. rewrite -> app_assoc. reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> app_assoc.
    simpl. rewrite -> app_assoc.
    reflexivity. Qed.

Lemma nonzeros_app: forall l1 l2 : natlist,
    nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    destruct n as [| n'].
    * (* n = O *)
      simpl. rewrite -> IHl1'. reflexivity.
    * (* n = S n' *)
      simpl. rewrite -> IHl1'. reflexivity. Qed.


Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
    | nil, nil => true
    | nil, _ => false
    | _, nil => false
    | h1 :: t1, h2 :: t2 => match h1 =? h2 with
                              | Datatypes.false => false
                              | _ => eqblist t1 t2
                            end
  end.

Example test_eqblist1: (eqblist nil nil = true).
Proof. reflexivity. Qed.
Example test_eqblist2: eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_eqblist3: eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem eqblist_refl: forall l : natlist,
    true = eqblist l l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    simpl. rewrite -> eqb_refl.
    rewrite -> IHl'. reflexivity. Qed.


Theorem count_member_nonzero: forall (s : bag),
    1 <=? (count 1 (1 :: s)) = Datatypes.true.
Proof.
  simpl. reflexivity. Qed.

Theorem leb_n_Sn: forall n,
    n <=? (S n) = Datatypes.true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem remove_does_not_increase_count: forall (s : bag),
    (count 0 (remove_one 0 s)) <=? (count 0 s) = Datatypes.true.
Proof.
  intros s. induction s as [| n s' IHs'].
  - (* s = nil *)
    simpl. reflexivity.
  - (* s = cons n s' *)
    simpl. destruct n as [| n'].
    * (* n = O *)
      simpl. rewrite -> leb_n_Sn. reflexivity.
    * (* n = S n' *)
      simpl. rewrite -> IHs'. reflexivity. Qed.

Theorem involution_injective: forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
  intros f H1 n1 n2 H2.
  simpl.
  rewrite -> H1.
  rewrite <- H2.
  rewrite <- H1. reflexivity. Qed.

Theorem rev_injective: forall (l1 l2 : natlist),
    rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H.
  simpl.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive. reflexivity. Qed.

(*         *)
(* Options *)
(*         *)

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l : natlist) (n : nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Example test_nth_error1: nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2: nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3: nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(* Pulls the `nat` out of a `natoption`, returning a supplied default
 * in the `None` case. *)
Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.


(* Using the same idea, fix the `hd` function from earlier so we don't
 * have to pass a default element for the `nil` case. *)
Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Example test_hd_error1: hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2: hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3: hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.


Theorem option_elim_hd: forall (l : natlist) (default : nat),
    hd default l = option_elim default (hd_error l).
Proof.
  intros l default. induction l as [| n l' IHl'].
  - (* l = nil *)
    simpl. reflexivity.
  - (* l = cons n l' *)
    simpl. reflexivity. Qed.


(*              *)
(* Partial Maps *)
(*              *)

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_id_refl: forall x,
    eqb_id x x = Datatypes.true.
Proof.
  intros x. destruct x.
  simpl. rewrite -> eqb_refl. reflexivity. Qed.

End NatList.


Module PartialMap.
Export NatList.

(* There are two ways to construct a partial_map: either using the constructor
 * empty to represent an empty partial map, or applying the constructor record
 * to a key, a value, and an existing partial_map to construct a partial_map
 * with an additional key-to-value mapping.
 *)
Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map) (x : id) (value : nat) : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y then Some v else find x d'
  end.


Theorem update_eq: forall (d : partial_map) (x : id) (v : nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v.
  simpl. rewrite -> eqb_id_refl. reflexivity. Qed.

Theorem update_neq: forall (d : partial_map) (x y : id) (o : nat),
    eqb_id x y = Datatypes.false -> find x (update d y o) = find x d.
Proof.
  intros d x y o H.
  simpl. rewrite -> H. reflexivity. Qed.

End PartialMap.

