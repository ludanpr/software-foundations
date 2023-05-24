(* Proof by Simplification
 *
 * We can use the same sort of "proof by simplification" that we've seen can
 * be used to prove more insteresting properties.
 *)

(* This is a good place to mention that `reflexivity` is a bit more powerful
 * than we have acknowledged. In the examples we have seen, the calls to `simpl`
 * were actually not needed, because `reflexivity` can perform some simplification
 * automatically when checking that two sides are equal; `simpl` was just added
 * so that we could see the intermediate state -- after simplification but before
 * finishing the proof.
 *
 * Moreover, it will be useful to know that `reflexivity` does somewhat more
 * simplification than `simpl` does -- for example, it tries "unfolding" defined
 * terms, replacing them with their right-hand sides. The reason for this difference
 * is that, if reflexivity succeeds, the whole goal is finished and we don't need
 * to look at whatever expanded expressions `reflexivity` has created by all this
 * simplification and unfolding; by contrast, `simpl` is used in situations where
 * we may have to read and understand the new goal that it creates, so we sould not
 * want it blindly expanding definitions and leaving the goal in a messy state.
 *
 * The form of the theorem we just stated and its proof are almost exactly the same
 * as the simpler examples we saw earlier; there are just a few differences. First,
 * we've used the keyword Theorem instead of Example. This difference is mostly a
 * matter of style; the keywords Example and Theorem (and a few others, including
 * Lemma, Fact, and Remark) mean pretty much the same thing to Coq.
 *
 * Second, we've added the quantifier ∀ n:nat, so that our theorem talks about all
 * natural numbers n. Informally, to prove theorems of this form, we generally start
 * by saying "Suppose n is some number..." Formally, this is achieved in the proof
 * by intros n, which moves n from the quantifier in the goal to a context of current
 * assumptions. Note that we could have used another identifier instead of n in the
 * intros clause.
 *
 * The keywords intros, simpl, and reflexivity are examples of tactics. A tactic is
 * a command that is used between Proof and Qed to guide the process of checking
 * some claim we are making.
 *)
Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

(* Other similar theorems can be proved with the same pattern.
 * The `_l` suffix in the names of these theorems is pronounced
 * "on the left".
 *)
Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n. simpl. reflexivity. Qed.
