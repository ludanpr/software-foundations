Module TuplePlayground.

  Inductive bit : Type :=
    | B0
    | B1.

  Inductive nybble : Type :=
    | bits (b0 b1 b2 b3 : bit).

  Check (bits B1 B0 B1 B0) : nybble.


  Definition all_zero (nb : nybble) : bool :=
    match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
    end.

  Compute (all_zero (bits B1 B0 B1 B0)).

  Compute (all_zero (bits B0 B0 B0 B0)).

End TuplePlayground.
