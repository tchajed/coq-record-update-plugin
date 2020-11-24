From RecordUpdate Require Import RecordUpdatePlugin.

Record X := mkX { A : nat; B : nat; C : bool; }.
Definition setA a x := set A (fun _ => a) x.

(* we can imagine a different way for the plugin to work, which would expose a
generic way to iterate over the record's constructor and fields: *)
(* this tactic is specialized to X, but in general [from_constructor]
initializes an accumulator with the constructor, then [t] is called on the
accumulator and the next projection function for each field of the record, and
finally the continuation [k] is called on the final accumulator value. *)
Tactic Notation "X_fold_fields"
       tactic(from_constructor) tactic(t) tactic(k) :=
  let x0 := from_constructor mkX in
  let x1 := t x0 A in
  let x2 := t x1 B in
  let x3 := t x2 C in
  k x3.

Lemma etaX : X -> X.
Proof.
  intros x.
  X_fold_fields
    ltac:(fun mk => mk)
    ltac:(fun r proj => constr:(r (proj x)))
    ltac:(fun k => exact k).
Qed.

Module test.
  Record X := mkX { A : nat; _ : bool;  }.
  Inductive Y := mkY (A:nat) (B:bool).

  Goal X -> X.
  Proof.
    (* error message (missing projection) *)
    Fail EtaExpansion.solve_with_eta X.

    (* TODO: these raise Not_found *)
    Fail EtaExpansion.solve_with_eta Y.
    Fail EtaExpansion.solve_with_eta option.
  Abort.
End test.
