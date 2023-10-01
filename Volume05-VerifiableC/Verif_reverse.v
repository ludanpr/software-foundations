(** Linked List in Verifiable C

 To generate the program AST:

    clightgen -normalize reverse.c

 *)
Require VC.Preface.

Require Import VST.floyd.proofauto.
Require Import VC.reverse.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** Inductive definition of linked lists

 `Tstruct _list noattr` is the AST (abstract syntax tree) description of the C-language type struct
 list. We will be using this a lot, so we make an abbreviation for it, t_list:
 *)
Definition t_list := Tstruct _list noattr.

(* We will define a separation-logic predicate, `listrep sigma p`, to describe the concept that the
 address `p` in memory is a linked list that represents the mathematical sequence `sigma`. Here,
 `sigma` is a list of `val`, which is C's "value" type: integers, pointers, floats, etc.

 The following says, if `sigma` has head `h` and tail `hs`, then there is a cons cell at address `p`
 with components `(h,y)`. This cons cell is described by `data_at Tsh t_list (h,y) p`. Separate from
 that, at address `y`, there is the representation of the rest of the list, `listrep hs y`. The memory
 footprint for `listrep (h::hs) p` contains the first cons cell at address `p`, and the rest of the
 cons cells in the list starting at address `y`.

 But if `sigma` is `nil`, then `p` is the null pointer, and the memory footprint is empty (`emp`). The
 fact `p=nullval` is a pure proposition (Coq `Prop`); we inject this into the assertion language (Coq
 `mpred`) using the `!!` operator.

 Because !!P (for a proposition P) does not specify any footprint (whether empty or otherwise), we do
 not use the separating conjunction `*` to combine it with `emp`; !!P has no spatial specification to
 separate from. Instead, we use the ordinary conjunction `&&`.
 *)
Fixpoint listrep (sigma : list val) (p : val) : mpred :=
  match sigma with
  | h :: hs => EX y:val, data_at Tsh t_list (h,y) p * listrep hs y
  | nil => !!(p = nullval) && emp
  end.

(* Now we want to prevent the `simpl` tactic from automatically unfolding `listrep`. This is a design
 choice that you might make differently, in which case, leave out the `Arguments` command.
 *)
Arguments listrep sigma p : simpl never.

(** Hint databases for spatial operators

 Whenever you define a new spatial operator -- a definition of type `mpred` such as `lisrep` -- it's
 useful to populate two hint databases.

   - The [saturate_local] hint is a lemma that extracts pure propositional facts from a
     spatial fact.
   - The [valid_pointer] hint is a lemma that extracts a valid-pointer fact from a spatial
     lemma.

 Consider this proof goal:
 *)
Lemma data_at_isptr_example1 : forall (h y p : val),
    data_at Tsh t_list (h,y) p |-- !! isptr p.
Proof.
  intros.
  (* `isptr p` means `p` is a non-null pointer, not NULL or Vundef or a floating-point number:
   *)
  Print isptr.  (* = fun v : val => match v with Vptr __ => True | _ => False end *)
  (* The goal solves automatically, using [entailer!]
   *)
  entailer!. Qed.

(* Let's look more closely at how entailer! solves this goal.
 *)
Lemma data_at_isptr_example2 : forall (h y p : val),
    data_at Tsh t_list (h,y) p |-- !! isptr p.
Proof.
  intros.
  (* First, it finds all the pure propositions `Prop` that it can deduce from the `mpred` conjuncts
   on the left-hand side, and puts them above the line.

   The [saturate_local] tactic uses a Hint database to look up the individual conjuncts on the left-
   hand side (this particular entailment has just one conjuncts).
   *)
  saturate_local.
  Print HintDb saturate_local.
  (* In this case, the new propositions above the line are labeled `H` and `H0`. Next, if the proof
   goal has just a proposition !!P on the right, [entailer!] throws away the left-hand-side and tries
   to prove P. (This is rather aggressive, and can sometimes lose information, that is, sometimes
   [entailer!] will turn a provable goal into an unprovable goal.)
   *)
  apply prop_right.
  (* It happens that `field_compatible _ _ p` implies `isptr p`,
   *)
  Check field_compatible_isptr.
  (* So therefore, [field_compatible_isptr] solves the goal
   *)
  eapply field_compatible_isptr; eauto. Qed.

(* But when you define a new spatial precidate `mpred` such as `listrep`, the [saturate_local] tactic
 does not know how to reduce `Prop` facts from the `listrep` conjunect
 *)
Lemma listrep_facts_example : forall sigma p,
    listrep sigma p |-- !! (isptr p \/ p=nullval).
Proof.
  intros.
  entailer!.
  (* Here [entailer!] threw away the left-hand side and left an unprovable goal.

   First, [entailer!] would use [saturate_local] to see (from the Hint database) what can be deduced
   from `listrep sigma p`. But [saturate_local] did not add anything above the line. That's because
   there's no Hint in the Hint database for `listrep`. Therefore we must add one. The conventional
   name for such a lemma is `f_local_facts`, if your new predicate is named `f`.
   *)
  Abort.

(* For each spatial precidate `Definition f(_) : mpred`, there should be one "local fact", a lemma
 of the form `f(_) |-- !! _`. On the right hand side, put all the propositions you can derive from
 f(_). In this case, we know:
    - `p` is either a pointer or null (it's never `Vundef`, or `Vfloat`, or a nonzero `Vint`).
    - `p` is null, if and only if `sigma` is nil.
 *)
Lemma listrep_local_facts : forall sigma p,
    listrep sigma p |-- !! (is_pointer_or_null p /\ (p=nullval <-> sigma=nil)).
Proof.
  intros.
  revert p; induction sigma; intros p.
  - (* sigma = nil *)
    unfold listrep.
    (* Now we have an entailment with a proposition p=nullval on the left.
      To move that proposition above the line, we could do Intros, but it's
      easier just to call on entailer! to see how it can simplify (and perhaps
      partially solve) this entailment goal:
     *)
    entailer!. (* The [entailer!] has left an ordinary proposition, which is easy to solve. *)
    split; auto.
  - (* sigma = a :: sigma'

     In the inductive case, we can again unfold the definition of `listrep (a::sigma)`;
     but then it's good to fold `listrep sigma`. Replace the semicolon with a period in
     the next line, to see why.
     *)
    unfold listrep; fold listrep.
    (* Warning! Sometimes [entailer!] is too aggressive. If we use it here, it will throw
     away the left-hand side because it doesn't understand how to look inside an EXistential
     quantitier. The exclamation point ! is a warning that entailer! can turn a provable
     goal into an unprovable goal.

     The preferred way to handle `EX y:t` on the left-hand-side of an entailment is to use
     `Intros y`.

     A less agressive entailment-reducer is entailer without the exclamation point. This
     one never turns a provable goal into an unprovable goal. Here it will Intro the EX-bound
     variable y.
     *)
    entailer.
    (* Should you use [entailer!] or [entailer] in ordinary proofs? Usually [entailer!] is best:
     it's faster, and it does more work for you. Only if you find that [entailer!] has gone into
     a dead end, should you use [entailer] instead.

     Here it is safe to use entailer!
     *)
    entailer!.
    (* Notice that entailer! has put several facts above the line: `field_compatible t_list [] p`
     and `value_fits t_list (a,y)` come from the [saturate_local] hint database, from the `data_at`
     conjunct; and `is_pointer_or_null y` and `y=nullval ↔ sigma=[]` come from the the `listrep`
     conjunct, using the induction hypothesis `IHsigma`.

     Now, let's split the goal and take the two cases separately.
     *)
    split; intro.
    + clear - H H2.
      subst p.
      (* it happens that `field_compatible _ _ p` implies `isptr p` *)
      Check field_compatible_isptr. (* : forall (t : type) (path : list gfield) (p : val),
                                             field_compatible t path p -> isptr p *)
      (* The predicate `isptr` excludes the null pointer *)
      Print isptr.   (* = fun v : val => match v with Vptr _ _ => True | _ => False end *)
      Print nullval. (* = if Archi.ptr64 then Vlong Int64.zero else Vint Int.zero *)
      (* Therefore H is a contradiction *)
      Check field_compatible_nullval. (* = forall (CS : compspecs) (t : type) (f : list gfield) (P : Type),
                                               field_compatible t f nullval -> P *)
      eapply field_compatible_nullval; eauto.
    + (*The case  a::sigma=[] → p=nullval is easy, by inversion: *)
      inversion H2. Qed.

(* Now we add this lemma to the Hint database called [saturate_local] *)
#[export] Hint Resolve listrep_local_facts : saturate_local.

(** Valid pointers, and the [valid_pointer] Hint database

 In the C language, you can do a pointer comparison such as `p != NULL` or `p == q` only if `p` is a
 valid pointer, that is, either `NULL` or actually pointing within an allocated object. One way to
 prove that `p` is valid is if, for example, `data_at Tsh t_list (h,y) p`, meaning that `p` is pointing
 at a list cell. There is a hint database [valid_pointer] from which the predicate `valid_pointer p` can
 be proved automatically.
 *)
Lemma struct_list_valid_pointer_example : forall h y p,
    data_at Tsh t_list (h,y) p |-- valid_pointer p.
Proof.
  intros.
  auto with valid_pointer. Qed.

(* However, the hint database does not know about user-defined separation-logic predicates (`mpred`)
 such as `listrep`:
 *)
Lemma listrep_valid_pointer_example : forall sigma p,
    listrep sigma p |-- valid_pointer p.
Proof.
  intros.
  (* In this case, `auto with...` would not solve the proof goal. *)
  auto with valid_pointer.
  Abort.

(* Therefore, we should prove the appropriate lemma, and add it to the hint database.
 *)
Lemma listrep_valid_pointer : forall sigma p,
    listrep sigma p |-- valid_pointer p.
Proof.
  intros.
  unfold listrep.
  (* Now we can do case analysis on `sigma` *)
  destruct sigma; simpl.
  - (* sigma = nil *)
    hint.
    entailer!.
  - (* sigma = cons a sigma' *)
    Intros y.
    (* Now this solves using the Hint database [valid_pointer], because the
     `data_at Tsh t_list (v,y) p` on the left is enough to prove the goal.
     *)
    auto with valid_pointer. Qed.

(*  Now we add this lemma to the Hint database *)
#[export] Hint Resolve listrep_valid_pointer : valid_pointer.


(** Specification of the reverse function

 A `funspec` characterizes the precondition required for calling the function and the postcondition
 guaranteed by the function.

 - The `WITH` clause says, there is a value `sigma: list val` and a value `p: val`, visible in both
   the precondition and the postcondition.
 - The PREcondition says,
       + There is one function-parameter, whose C type is "pointer to struct list"
       + PARAMS: The parameter contains the Coq value `p`
       + SEP: in memory at address `p` there is a linked list representing `sigma`.
 - The POSTcondition says,
       + the function returns a value whose C type is "pointer to struct list"; and
       + there exists a value `q : val`, such that
       + RETURN: the function's return value is `q`
       + SEP: in memory at address `q` there is a linked list representing `rev sigma`.
 *)
Definition reverse_spec : ident * funspec :=
 DECLARE _reverse
  WITH sigma : list val, p : val
  PRE [ tptr t_list ]
     PROP () PARAMS (p) SEP (listrep sigma p)
  POST [ (tptr t_list) ]
    EX q:val,
     PROP () RETURN (q) SEP (listrep(rev sigma) q).

(* The global function spec characterizes the preconditions/postconditions of all the functions that
 your proved-correct program will call. Normally you include all the functions here, but in this
 tutorial example we include only one.
 *)
Definition Gprog : funspecs := [ reverse_spec ].

(** Proof of the `reverse` function

 For each function definition in the C program, prove that the function-body (in this case, f_reverse)
 satisfies its specification (in this case, `reverse_spec`).
 *)
Lemma body_reverse : semax_body Vprog Gprog f_reverse reverse_spec.
Proof.
  start_function.
  (* As usual, the current assertion (precondition) is derived from the `PRE`
   clause of the function specification, `reverse_spec`, and the current command
   `w = 0; ... more ...` is the function body of `f_reverse`
   *)
  Show. forward.  (* w = NULL; *)
  (* The new `semax` judgement is for the rest of the function body after the
   command `w = NULL`. The precondition of this `semax` is actually the postcondition
   of the `w = NULL`, but contains the additional `LOCAL` fact,

           temp _w (Vint (Int.repr 0))

   , that is, the variable `_w` contains `nullval`.
   *)
  forward.  (* v = p; *)
  (* We cannot take the next step using forward because the next command is a while loop.
   *)
  (** The loop invariant

   To prove a while-loop, we must supply a loop invariant, such as

         (EX s1 ... PROP (...) LOCAL (...) SEP (...).
   *)
  forward_while
    (EX s1 : list val, EX s2 : list val,
     EX w : val, EX v : val,
      PROP (sigma = rev s1 ++ s2)
      LOCAL (temp _w w; temp _v v)
      SEP (listrep s1 w; listrep s2 v)).
  (* The forward_while tactic leaves four subgoals, which we mark with - (the Coq "bullet")
   *)
  - (* Prove that (current) precondition implies the loop invariant. *)
    hint.
    (* On the left-hand side of this entailment is the precondition (that we had already
     established by forward symbolic execution to this point) for the entire while-loop.
     On the right-hand side is the loop invariant, that we just gave to the [forward_while]
     tactic. Because the right-hand side has four existentials, a good proof strategy is
     to choose values for them, using the Exists tactic.
     *)
    Exists (@nil val) sigma nullval p.
    (* Now we have a quantifier-free proof goal; let us see whether entailer! can solve some
     parts of it.
     *)
    entailer!.
    unfold listrep.
    (* Now that the user-defined predicate is unfolded, entailer! can solve the residual
     entailment.
     *)
    entailer!.
  - (* Prove that loop invariant implies typechecking of loop condition *)
    hint.
    (* The second subgoal of [forward_while] is to prove that the loop-test condition can
     execute 
     *)
    Show. Abort.

