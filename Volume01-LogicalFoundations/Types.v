(* Types
 *
 * Every expression in Coq has a type, describing what sort of thing it
 * computes. The Check command asks Coq to print the type of an expression.
 *)

Check true.

(* If the expression after Check is followed by a colon and a type, Coq will
 * verify that the type of the expression matches the given type and halt with
 * an error if not. *)
Check true : bool.
Check (negb true) : bool.

Check negb : bool -> bool.

(* New type from Old
 *
 * The types we have defined so far are examples of "enumerated types": their
 * definitions explicitly enumerate a finite set of elements, called constructors.
 *
 * An `Inductive` definition does two things:
 *   1. It defines a set of new constructors. E.g., red, primary, true, false, etc.
 *      are constructors.
 *   2. It groups them into a new named type, like bool, rgb, or color.
 *
 * Constructor expressions are formed by applying a constructor to zero or more
 * other constructors or constructor expressions, obeying the declared number and
 * types of the constructor arguments.
 *
 * In particular, the definitions of `rgb` and `color` say which constructor expressions
 * belong to the sets `rgb` and `color`:
 *
 *  - red, green, and blue belong to the set rgb;
 *  - black and white belong to the set color;
 *  - If p is a constructor expressions belonging to the set rgb, then primary p
 *    is a constructor expressions belonging to the set color; and
 *  - constructor expressions formed in these ways are the only ones belonging
 *    to the sets rgb and color.
 *)
Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).


Definition monochrome (c:color) : bool :=
  match c with
  | black => true
  | white => true
  | primary _ => false
  end.

Definition isred (c:color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Example test_monochrome1: (monochrome black) = true.
Proof. simpl. reflexivity. Qed.

Example test_monochrome2: (monochrome white) = true.
Proof. simpl. reflexivity. Qed.

Example test_monochrome3: (monochrome (primary red)) = false.
Proof. simpl. reflexivity. Qed.

Example test_monochrome4: (monochrome (primary blue)) = false.
Proof. simpl. reflexivity. Qed.

Example test_monochrome5: (monochrome (primary green)) = false.
Proof. simpl. reflexivity. Qed.

Example test_isred1: (isred black) = false.
Proof. simpl. reflexivity. Qed.

Example test_isred2: (isred white) = false.
Proof. simpl. reflexivity. Qed.

Example test_isred3: (isred (primary red)) = true.
Proof. simpl. reflexivity. Qed.

Example test_isred4: (isred (primary green)) = false.
Proof. simpl. reflexivity. Qed.

Example test_isred5: (isred (primary blue)) = false.
Proof. simpl. reflexivity. Qed.
