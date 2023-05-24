(* Modules
 *
 * Coq provides a module system to aid in organizing large developments.
 *
 * If we enclose collection of declarations between `Module X` and `End X`
 * markers, then, in the remainder of the file after the `End`, these
 * definitions are referred to by names like `X.foo` instead of just `foo`.
 *)
Inductive rgb : Type :=
  | red
  | green
  | blue.


Module Playground.
  Definition myblue : rgb := blue.
End Playground.

Definition myblue : bool := true.

Check Playground.myblue : rgb.
Check myblue : bool.
