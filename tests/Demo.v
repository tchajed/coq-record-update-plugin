From RecordUpdate Require Import RecordUpdatePlugin.

Module basic_tests.
  Record X := mkX { A : nat; B : nat; C : bool; }.

  Definition setA a x := set A (fun _ => a) x.
  #[local] Instance setB_wf : SetterWf B := _.
  #[local] Instance etaX : Settable X := _.
  Definition setA2 a x := set A (fun _ => a) x.
  #[local] Instance setA_wf : SetterWf A := _.
End basic_tests.

Module errors.
  Record X := mkX { A : nat; _ : bool;  }.
  Inductive Y := mkY (A:nat) (B:bool).

  Goal X -> X.
  Proof.
    (* error message (missing projection) *)
    Fail EtaExpansion.solve_with_eta X.

    Fail EtaExpansion.solve_with_eta Y.
    Fail EtaExpansion.solve_with_eta option.
  Abort.
End errors.
