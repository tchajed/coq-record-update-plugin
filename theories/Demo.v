From RecordUpdate Require Import Loader.

Record X := { A : nat; B : nat; C : bool; }.

Inductive X' := mkX' (A: nat) (B: nat) (C: bool).

Theorem eta_X : X -> X.
Proof.
  Fail solve_with_eta A.
  Fail solve_with_eta option.
  Fail solve_with_eta X'.
  solve_with_eta X.
Defined.
