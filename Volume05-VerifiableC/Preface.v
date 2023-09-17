(*** Check for the right version of VST *)
Require Import Coq.Strings.String.
Open Scope string.
Require Import VST.veric.version.  (* If this line fails, VST is not installed *)

Definition release_needed := "2.11.1".
Goal release = release_needed.
reflexivity ||
let need := constr:(release_needed) in let need := eval hnf in need in
let rel := constr:(release) in let rel := eval hnf in rel in
fail "The wrong version of VST is installed.
You have VST version"
rel "but this version of 'Software Foundations Volume 5: Verifiable C'
demands version" need ". If possible, install VST version" need
"using the Coq Platform or using opam. Or, if not from Coq Platform or opam,"
"for instructions about building VST from source and accessing that version,
see the README file in this directory."
"Or, instead of installing VST" need ","
"if you want to proceed using VST version" rel ","
"then edit the Definition release_needed in Preface.v".
Abort.

Require Import ZArith.
Local Open Scope Z_scope.

(* Require VC.stack. (* If this line fails, do 'make stack.vo' *) *)
(* Goal VC.stack.Info.bitsize = VST.veric.version.bitsize. *)
(* reflexivity || *)
(* let b1 := constr:(VST.veric.version.bitsize) in let b1 := eval compute in b1 in *)
(* let b2 := constr:(VC.stack.Info.bitsize) in let b2 := eval compute in b2 in *)
(* fail "Your installed VST is configured to verify C programs compiled with" *)
(*   b1 "bit pointers," *)
(*  "but the .c files in the local directory have been clightgen'ed as if compiled with" *)
(*  b2 "bit pointers." *)
(* "You can fix this by executing the shell command, *)
(* " *)
(* "bash cfiles-bitsize" b1 " *)
(* to install the properly configured clightgen outputs." *)
(* "It is not necessary to have clightgen installed". *)
(* Abort. *)

