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

End NatList.
