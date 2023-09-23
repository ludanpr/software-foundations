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

   The Application Programmer Interface (API) of a C program is expressed in its
   header file: function prototypes and data-structure definitions. In Verifiable C,
   an API specification is written as a series of function specifications (`funspec`'s)
   corresponding to the function prototypes.

   This `DECLARE` statement has type `ident * funspec`. That is, it associates the name
   of a function (the identifier `_sumarray`) with a function-specification. The identifier
   `_sumarray` comes directly from the C program, as parsed by `clightgen`.

   A function is specified by its precondition and its postcondition. The `WITH` clause
   quantifies over Coq values that may appear in both the precondition and the postcondition.
   The precondition has access to the function parameters (in this case `a` and `size`) and
   the postcondition has access to the return value (`sum_Z contents`).

   Function preconditions, postconditions, and loop invariants are assertions about the state
   of variables and memory at a particular program point. In an assertion

             PROP (P) LOCAL(Q) SEP (R)

   the propositions in the sequence `P` are all of Coq type `Prop`. They describe things that
   are true independent of program state. In the precondition above, the statement

             0 <= size <= Int.max_signed

   is true just within the scope of the quantification of the variable `size`; that variable
   is bound by `WITH`, and spans the `PRE` and `POST` assertions.

   The `LOCAL` clause, describing what's in C local variables, takes different forms depending
   on context:

      - In a function-precondition, we write PROP/PARAMS/SEP, that is, the PARAMS lists
        the values of C function parameters (in order).
      - In a function-postcondition, we write RETURN(v) to indicate the return value of
        the function.
      - Within a function body (in assertions and invariants) we write LOCAL to describe
        the values of local variables (including parameters).
 *)
Definition sumarray_spec : ident * funspec :=
DECLARE _sumarray
 WITH a : val, sh : share, contents : list Z, size : Z
 PRE [ tptr tuint, tint ]
  PROP (readable_share sh; 0 <= size <= Int.max_signed;
         Forall (fun x => 0 <= x <= Int.max_unsigned) contents)
  PARAMS (a; Vint (Int.repr size))
  SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)
 POST [ tuint ]
  PROP () RETURN (Vint (Int.repr (sum_Z contents)))
  SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a).
(* Whether it is PARAMS or RETURN or LOCAL, we are talking about the values contained in parameters
  or local variables. In general, a C scalar variable holds something of type `val`; this type is
  defined by CompCert as,
 *)
Print val.

(* In an assertion `PROP(P) LOCAL(Q) SEP(R)`, the `SEP` conjuncts `R` are spatial assertions in
   separation logic. In our example precondition, there's just one `SEP` conjunct, a `data_at`
   assertion saying that at address `a` in memory, there is a data structure of type

             array[size] of unsigned int;

   with access-permission `sh`, and the contents of that array is the sequence

             map Vint (map Int.repr contents)

   The postcondition is introduced by `POST [ tuint ]`, indicating that this function returns a value
   of type `unsigned int`. There are no `PROP` statements in this postcondition -- no forever-true facts
   hold now, that weren't already true on entry to the function.

   `RETURN(v)` gives the return value `v`; `RETURN()` for void functions.

   The postcondition's `SEP` clause mentions all the spatial resources from the precondition, minus ones
   that have been freed (deallocated), plus ones that have been malloc'd (allocated).

   So, overall, the specification for sumarray is this: "At any call to sumarray, there exist values a, sh,
   contents, size such that sh gives at least read-permission; `size` is representable as a nonnegative 32-bit
   signed integer; function-parameter `_a` contains value `a` and `_n` contains the 32-bit representation of `size`;
   and there's an array in memory at address `a` with permission `sh` containing contents. The function returns
   a value equal to `sum_int(contents)`, and leaves the array in memory unaltered."
 *)

(* Function specification for main()

   The function-spec for `main` has a special form.

   This postcondition says we have indeed added up the global array `four`.
 *)
Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE [] main_pre prog tt gv
  POST [ tint ]
     PROP()
     RETURN (Vint (Int.repr (1+2+3+4)))
     SEP(TT).

(* Integer overflow

   In Verifiable C's signed integer arithmetic, you must prove (if the system cannot prove automatically) that no
   overflow occurs. For unsigned integers, arithmetic is treated as modulo-2^n (where n is typically 32 or 64),
   and overflow is not an issue. The function Int.repr: Z → int truncates mathematical integers into 32-bit integers
   by taking the (sign-extended) low-order 32 bits. Int.signed: int → Z injects back into the signed integers.

   The sumarray program uses unsigned arithmetic for s and the array contents; it uses signed arithmetic for i.

   The postcondition guarantees that the value returned is Int.repr (sum_Z contents). But what if the sum of all the
   s is larger than 2^32, so the sum doesn't fit in a 32-bit signed integer? Then Int.unsigned(Int.repr (sum_Z contents))
   ≠ sum_Z contents. In general, for a claim about Int.repr(x) to be useful one also needs to know that 0 ≤ x ≤ Int.max_unsigned
   or Int.min_signed ≤ x ≤ Int.max_signed. The caller of sumarray will probably need to prove 0 ≤ sum_Z contents ≤ Int.max_unsigned
   in order to make much use of the postcondition.
 *)


(* Packaging the Gprog and Vprog

   To prove the correctness of a whole program,

      - 1. Collect the function-API specs together into `Gprog`.
      - 2. Prove that each function satisfies its own API spec (with a `semax_body` proof).
      - 3. Tie everything together with a `semax_func` proof.

   The first step is easy:
 *)
Definition Gprog := [sumarray_spec; main_spec].
(* What's in Gprog are the funspecs that we built using DECLARE. (In multi-module programs we would also include imported funspecs.)

   In addition to Gprog, the API spec contains Vprog, the list of global-variable type-specs. This was computed automatically by the
   mk_varspecs tactic, in the "boilerplate" code above.
 *)
Print Vprog.         (*   = (_four, tarray tuint 4)  : varspecs *)
Print varspecs.      (*   = list (ident * type) *)


(* Proof of the sumarray program

   Now comes the proof that f_sumarray, the body of the sumarray() function, satisfies sumarray_spec, in global context (Vprog,Gprog).

   Here, `f_sumarray` is the actual function body (AST of the C code) as parsed by `clightgen`. We can read `body_sumarray` as claiming:
   in the context of `Vprog` and `Gprog`, the function body `f_sumarray` satisfies its specification `sumarray_spec`. We need the context
   in case the sumarray function refers to a global variable (`Vprog` provides the variable's type) or calls a globa function (`Gprog`
   provides the function's API spec).

 *)
Lemma body_sumarray : semax_body Vprog Gprog f_sumarray sumarray_spec.
Proof.
  (** start function

   The predicate [semax_body] states the Hoare triple of the function body,
   [Delta |- {Pre} c {Post}], where [Pre] and [Post] are taken from the
   [funspec], [c] is the body of the function, and the type-context [Delta]
   is calculated from the global type-context overlaid with the parameter-
   and local-types of the function.

   To prove this, we begin with the tactic [start_function],  which takes care
   of some simple bookkeeping and expresses the Hoare triple to be proved.
   *)
  start_function. (* always do this at the beginning of a `semax_body` proof *)

  (** Some of the assumptions you now see above the line are,
  - [a, sh, contents, size], taken directly from the WITH clause
       of [sumarray_spec];
  - [Delta_specs], the context in which Floyd's proof tactics will look up
       the specifications of global functions;
  - [Delta], the context in which Floyd will look up the types of
       local and global variables;
  - [SH,H,H0], taken exactly from the [PROP] clauses of [sumarray_spec]'s
       precondition.

  There are also two abbreviations above the line, POSTCONDITION and MORE_COMMANDS
  *)

  (** Forward symbolic execution

  We do Hoare logic proof by forward symbolic execution.  At the beginning
  of this function body, our proof goal is a Hoare triple about the statement
  [(i=0; ...more commands...)]. In a forward Hoare logic proof of
  [{P}(i=0;...more...){R}] we might first apply the sequence rule,

    {P}(i=0;){Q}  {Q}(...more...){R}
    ---------------------------------
    {P}(i=0;...more...){R}

  assuming we could derive some appropriate assertion [Q].
  For many kinds of statements (assignments, return, break,
  continue) [Q] is derived automatically by the [forward] tactic,
  which applies a strongest-postcondition style of proof rule.
  Let us now apply the [forward] tactic: *)
  forward. (* i = 0; *)
  (** Look at the precondition of the current proof goal, that is, the second
   argument of `semax`; it has the form `PROP(...) LOCAL(...) SEP(...)`. That
   precondition is also the postcondition of `i = 0;`. It's much like the
   precondition of `i = 0;` except for one change: we now know that `i` is
   equal to `0`, which is expressed in the `LOCAL` part as `temp _i (Vint (Int.repr 0))`
  *)
  Check 0.                              (* : Z, the mathematical integer zero *)
  Check (Int.repr 0).                   (* : int, the 32-bit integer representing 0 *)
  Check (Vint (Int.repr 0)).            (* : val, the type of CompCert values *)
  Check (temp _i (Vint (Int.repr 0))).  (* : localdef, the type of `LOCAL` assertions *)

  (** abbreviate, MORE_COMMANDS, POSTCONDITION

   When doing forward symbolic execution (forward Floyd/Hoare proof) through a large function,
   you don't usually want to see the entire function-body in your proof subgoal. Therefore the
   system abbreviates some things for you, using the magic of Coq's implicit arguments.
   *)
  Check @abbreviate.      (* : forall A : Type, A -> A *)
  About abbreviate.       (* Arguments A, x are implicit and maximally inserted ... *)
  (* We see here that `abbreviate` is just the identity function, with both of its arguments
   implicit.

   To examinate the actual contents of `MORE_COMMANDS`, just do this:
   *)
  unfold abbreviate in MORE_COMMANDS.
  (* or alternatively, *)

  subst MORE_COMMANDS; unfold abbreviate.

  (* Similarly, to see the `POSTCONDITION`, just do,
   *)
  unfold abbreviate in POSTCONDITION.

  (* Hint

   In any VST proof state, the [hint] tactic will print a suggestion (if it can) that will help
   you make progress in the proof. In stepping through the case study in this chapter, insert
   [hint] at any point to see what it says.
   *)
  hint.
  (* Then delete the hints! (They slow down replay of your proof.)

   The hint here suggests using `abbreviate_semax`, which will undo the [unfold abbreviate] that
   we did above. Really this is optional; if we don't do [abbreviate_semax], the next [forward]
   tactic will do it for us.
   *)
  abbreviate_semax.
  hint.

  (** Forward through another assignment statement

   The [forward] tactic works on assignment statements, break, continue, and return.
   *)
  forward.  (* s = 0; *)

  (** While loops, forward_while

   To do symbolic execution through a `while` loop, use the [forward_while] tactic; you must
   supply a loop invariant.

   A loop invariant is an assertion, almost always in the form of an existential quantifier,

            EX...PROP(...)LOCAL(...)SEP(...)

   Each iteration of the loop has a state characterized by a different value of some iteration
   variable(s), the EX binds that value.
   *)
  forward_while
    (EX i: Z,
      PROP (0 <= i <= size)
      LOCAL (temp _a a;
             temp _i (Vint (Int.repr i));
             temp _n (Vint (Int.repr size));
             temp _s (Vint (Int.repr (sum_Z (sublist 0 i contents)))))
      SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) a)).

  (* [forward_while] leaves four subgoals; here we label them with the - bullet.

   The first subgoal is to prove that the current assertion (precondition) entails the loop
   invariant.
   *)
  - hint.

  (** Proving separation-logic entailments

   This proof goal is an entailment, [ENTAIL Delta, P |-- Q], meaning "in context `Delta`, any
   state that satisfies `P` will also satisfy `Q`."

   In this case, the right-hand-side of this entailment is existentially quantified; it says:
   there exists a value `i` such that (among other things) `temp _i (Vint (Int.repr i))`, that
   is, the C variable `_i` contains the value `i`. But the left-hand-side of the entailment
   says `temp _i (Vint (Int.repr 0))`, that is, the C variable `_i` contains 0.

   This is analogous to the following situation; and to prove such a goal, one uses Coq's "exists"
   tactic to demonstrate a value for `i`.
   *)
  Set Nested Proofs Allowed.
  Goal forall (f: Z -> Z) (x: Z), f(x)=0 -> exists i:Z, f(x) = i.
    intros.
    exists 0. auto. Qed.

  (* In a separation logic entailment, one can prove an [EX] on the right-hand side by using the
   [Exists] tactic to demonstrate a value for the quantified variable:
   *)
  Exists 0.     (* Instantiate the existential on the right-side of |-- *)
  (* Notice that `i` has now been replaced with `0` on the right side.

   To prove entailments, we usually use the [entailer!] tactic to simplify the entailment as much
   as possible -- or in many cases, to prove it entirely.
   *)
  entailer!.

  (** Type-checking the loop test

   The second subgoal of [forward_while] is always to prove that the loop-test expression can
   evaluate without crashing -- that is, all the variables it references exist and are initialized,
   it doesn't divide by zero, et cetera.

   We call this a "type-checking condition", the predicate `tc_expr`. In this case, it's the while-
   loop test `i < n` that must execute, so we see `tc_expr Delta (!(_i < _n))` on the right-hand
   side of the entailment.

   Very often, these `tc_expr` goals solve automatically by `entailer!`.
   *)
  - hint.
  entailer!.

  (** Proving that the loop body preserves the loop invariant

   
   *)
  - hint.

