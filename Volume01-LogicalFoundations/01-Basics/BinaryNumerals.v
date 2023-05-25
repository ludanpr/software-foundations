(* Binary Numerals
 *
 * We can generalize our unary representation of natural numbers to the more
 * efficient binary representation by treating a binary number as a sequence
 * of constructors B0 and B1, terminated by a Z.
 *)

(* Note that the low-order bit is on the left and the high-order
 * bit is on the right -- the opposite of the way binary numbers
 * are usually written.
 *)
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m : bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 m' => B1 m'
  | B1 m' => B0 (incr m')
  end.

Fixpoint bin_to_nat (m : bin) : nat :=
  match m with
  | Z => O
  | B0 m' => 2 * (bin_to_nat m')
  | B1 m' => 1 + 2 * (bin_to_nat m')
  end.

Example test_bin_incr0 : (incr Z) = (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr4 : (incr (B0 (B0 (B1 Z)))) = B1 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr5 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr6 : bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr7 : bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.
