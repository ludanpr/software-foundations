(* Course Late Policies Formalized
 *
 * Suppose that a course has a grading policy based on late days such that a student's
 * final letter grade is lowered if they submit too many homework assignments late.
 *)
Module LateDays.

Inductive letter : Type :=
  | A | B | C | D | F.

Inductive modifier : Type :=
  | Plus | Natural | Minus.

Inductive grade : Type :=
  Grade (l : letter) (m : modifier).

Inductive comparison : Set :=
  | Eq : comparison  (* "equal" *)
  | Lt : comparison  (* "less than" *)
  | Gt : comparison. (* "greater than" *)

Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, F => Eq
  | F, _ => Lt
  end.

Compute letter_comparison B A.
Compute letter_comparison D D.
Compute letter_comparison B F.

Theorem letter_comparison_Eq : forall l,
    letter_comparison l l = Eq.
Proof.
  intros l. destruct l eqn:El.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.


Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, (Plus | Natural) => Lt
  | Minus, Minus => Eq
  end.

Definition grade_comparison (g1 g2 : grade) : comparison :=
  match g1, g2 with
  | Grade l1 m1, Grade l2 m2 =>
      match (letter_comparison l1 l2) with
      | Eq => match (modifier_comparison m1 m2) with
              | Eq => Eq
              | Gt => Gt
              | Lt => Lt
              end
      | Gt => Gt
      | Lt => Lt
      end
  end.

Example test_grade_comparison1 : (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison2 : (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison3 : (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
Proof. simpl. reflexivity. Qed.
Example test_grade_comparison4 : (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
Proof. simpl. reflexivity. Qed.


Definition lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F
  end.

(* Lower letter theorem
 *
 * We state and prove that the result of the function lower_letter will be lower
 *
 * First, we prove the edge case.
 *)
Theorem lower_letter_F_is_F :
  lower_letter F = F.
Proof.
  simpl. reflexivity.
Qed.

Theorem lower_letter_lowers : forall (l : letter),
    letter_comparison F l = Lt -> letter_comparison (lower_letter l) l = Lt.
Proof.
  intros [].
  - intros H. rewrite <- H. simpl. reflexivity.
  - intros H. rewrite <- H. simpl. reflexivity.
  - intros H. rewrite <- H. simpl. reflexivity.
  - intros H. rewrite <- H. simpl. reflexivity.
  - intros H. rewrite <- H. rewrite -> lower_letter_F_is_F. reflexivity.
Qed.


Definition lower_grade (g : grade) : grade :=
  match g with
  | Grade l m =>
      match l, m with
      | F, Minus => Grade F Minus
      | _, Minus => Grade (lower_letter l) Plus
      | _, Natural => Grade l Minus
      | _, Plus => Grade l Natural
      end
  end.

Example lower_grade_A_Plus : lower_grade (Grade A Plus) = (Grade A Natural).
Proof. simpl. reflexivity. Qed.
Example lower_grade_A_Natural : lower_grade (Grade A Natural) = (Grade A Minus).
Proof. simpl. reflexivity. Qed.
Example lower_grade_A_Minus : lower_grade (Grade A Minus) = (Grade B Plus).
Proof. simpl. reflexivity. Qed.
Example lower_grade_B_Plus : lower_grade (Grade B Plus) = (Grade B Natural).
Proof. simpl. reflexivity. Qed.
Example lower_grade_F_Natural : lower_grade (Grade F Natural) = (Grade F Minus).
Proof. simpl. reflexivity. Qed.
Example lower_grade_twice : lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof. simpl. reflexivity. Qed.
Example lower_grade_thrice : lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof. simpl. reflexivity. Qed.

(* We'll use this in later proofs. *)
Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof. simpl. reflexivity. Qed.

End LateDays.
