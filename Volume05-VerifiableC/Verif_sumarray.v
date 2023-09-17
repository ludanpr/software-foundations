(** * Verif_sumarray: Introduction to Verifiable C *)

(* ================================================================= *)
(** ** Verified Software Toolchain *)

(** The Verified Software Toolchain is a toolset for proving the functional
  correctness of C programs, with
  - a _program logic_ called Verifiable C, based on separation logic.
  - a _proof automation system_ called VST-Floyd that assists you in applying
    the program logic to your program.
  - a soundness proof in Coq, guaranteeing that whatever properties you
    prove about your program will actually hold in any execution of the
    C source-language operational semantics. And this proof _composes_
    with the correctness proof of the CompCert verified optimizing C compiler,
    so you can also get a guarantee about the behavior of the assembly
    language program.

  To verify a C program, such as [sumarray.c], use the CompCert front end to parse
  it into an Abstract Syntax Tree (AST). Generally, what we'd do is,

    clightgen -normalize sumarray.c

  The output of [clightgen] would be a file [sumarray.v] that contains the Coq
  inductive data structure describing the syntax trees of the source program.

  This file, [Verif_sumarray.v], contains a specification of the functional
  correctness of the program [sumarray.c], followed by a proof that the program
  satisfies its specification.

  For larger programs, one would typically break this down into three or more
  files:
  - Functional model (often in the form of a Coq function)
  - API specification
  - Function-body correctness proofs, one per file.
*)
Require VC.Preface.

(* Every API specification begins with the same standard boilerplate the only
   thing that changes is the name of the program -- in this case, [sumarray]

   The first line imports Verifiable C and its Floyd proof-automation library.
   The second line imports the AST of the program to be verified. The third
   line processes all the struct and union definitions in the AST, and the
   fourth line processes global variable declarations. *)
Require Import VST.floyd.proofauto.
Require Import VC.sumarray.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* To prove correctness of [sumarray.c], we start by writing a functional model
   of adding up a sequence. We can use a list-fold to express the sum of all the
   elements in a list of integers:
 *)
Definition sum_Z : list Z -> Z := fold_right Z.add 0.

(* Then we prove propertiers of the functional model: in this case, how [sum_Z]
   interacts with list append.

   The data types used in a functional model can be any kind of mathematics at all,
   as long as we have a way to relate them to the integers, tuples, and sequences
   used in a C program. But the mathematical integers Z and the 32-bit modular
   integers Int.int are often relevant. Notice that this functional specification
   does not depend on sumarray.v or on anything in the Verifiable C libraries.
   This is typical, and desirable: the functional model is about mathematics,
   not about C programming.
 *)
Lemma sum_Z_app : forall a b,
    sum_Z (a ++ b) = sum_Z a + sum_Z b.
Proof.
  intros. induction a;
  simpl; lia. Qed.


(* API Spec for the sumarray.c program
 *)
