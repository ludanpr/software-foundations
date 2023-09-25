(** Linked List in Verifiable C

 To generate the program AST:

    clighgen -normalize reverse.c

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

 
 *)
