Record X := mkX { A : nat; B : nat; C : bool; }.

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
