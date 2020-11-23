From RecordUpdate Require Import RecordUpdatePlugin.

Record X := { A : nat; B : nat; C : bool; }.
Definition setA a x := set A (fun _ => a) x.
