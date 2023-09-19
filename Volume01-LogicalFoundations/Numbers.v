From LF Require Export Booleans.
Module NatPlayground.

(* There is a representation of numbers that is even simpler than binary,
 * namely unary (base 1), in which only a single digit is used. To represent
 * unary numbers with Coq datatype, we use two constructors. The capital-
 * letter O constructor represents zero. When the S constructor is applied
 * to the representation of the natural number n, the result is the representation
 * of n+1, where S stands for "successor" (or "scratch").
 *)

(* With this definition, 0 is represented by `O`, 1 by `S O`, 2 by `S (S O)`,
 * and so on.
 *)
Inductive nat : Type :=
  | O
  | S (n : nat).

(* Predecessor *)
Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

End NatPlayground.


Check (S (S (S (S O)))).

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).

Check S : nat -> nat.
Check pred : nat -> nat.
Check minustwo : nat -> nat.


(* For most interesting computations involving numbers, simple pattern matching
 * is not enough: we also need recursion. For example, to check that a number `n`
 * is even, we may need to recursively check whether `n-2` is even.
 *
 * Such functions are introduced with the keyword `Fixpoint` instead of `Definition`.
 *)
Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n : nat) : bool :=
  negb (even n).

Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_odd2: odd 2 = false.
Proof. simpl. reflexivity. Qed.

Example test_odd3: odd 3 = true.
Proof. simpl. reflexivity. Qed.

Example test_odd4: odd 4 = false.
Proof. simpl. reflexivity. Qed.


Module NatPlayground2.

  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => (plus (mult n' m) m)
    end.

  Fixpoint minus (n m : nat) : nat :=
    match n,m with
    | O, _ => O
    | S _, O => n
    | S n', S m' => (minus n' m')
    end.

  Compute (plus 3 2).

  Compute (mult 0 1).
  Compute (mult 2 3).
  Compute (mult 7 5).
  Compute (mult 2 5).
  Compute (mult 11 10).

  Compute (minus 1 1).
  Compute (minus 0 1).   (* only Naturals *)
  Compute (minus 12 5).

End NatPlayground2.


Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S n => mult base (exp base n)
  end.

Compute (exp 1 0).
Compute (exp 2 8).


Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.


Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                      : nat_scope.
Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                      : nat_scope.
Notation "x * y" := (mult x y)
                      (at level 40, left associativity)
                      : nat_scope.

Check ((0 + 1) + 1) : nat.


(* When we say that Coq comes with almost nothing built-in, we really mean it: even
 * equality tests is a user-defined operation.
 *)

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => leb n' m'
            end
  end.

Definition ltb (n m : nat) : bool :=
  (leb n m) && (negb (eqb n m)).

Definition gtb (n m : nat) : bool :=
  negb (leb n m).

Definition geb (n m : nat) : bool :=
  negb (ltb n m).

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Notation "x >? y" := (gtb x y) (at level 70) : nat_scope.
Notation "x >=? y" := (geb x y) (at level 70) : nat_scope.

Example test_eqb1: (eqb 0 0) = true.
Proof. simpl. reflexivity. Qed.
Example test_eqb2: (eqb 12 12) = true.
Proof. simpl. reflexivity. Qed.
Example test_eqb3: (eqb 2 5) = false.
Proof. simpl. reflexivity. Qed.
Example test_eqb1': (0 =? 0) = true.
Proof. simpl. reflexivity. Qed.
Example test_eqb2': (12 =? 12) = true.
Proof. simpl. reflexivity. Qed.
Example test_eqb3': (2 =? 5) = false.
Proof. simpl. reflexivity. Qed.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_leb1': (2 <=? 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2': (2 <=? 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb1': (2 <? 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2': (2 <? 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3': (4 <? 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_gtb1: (gtb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_gtb2: (gtb 2 4) = false.
Proof. simpl. reflexivity. Qed.
Example test_gtb3: (gtb 4 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_gtb1': (2 >? 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_gtb2': (2 >? 4) = false.
Proof. simpl. reflexivity. Qed.
Example test_gtb3': (4 >? 2) = true.
Proof. simpl. reflexivity. Qed.

Example test_geb1: (geb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_geb2: (geb 2 4) = false.
Proof. simpl. reflexivity. Qed.
Example test_geb3: (geb 4 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_geb1': (2 >=? 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_geb2': (2 >=? 4) = false.
Proof. simpl. reflexivity. Qed.
Example test_geb3': (4 >=? 2) = true.
Proof. simpl. reflexivity. Qed.
