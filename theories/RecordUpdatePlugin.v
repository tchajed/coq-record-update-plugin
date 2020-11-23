Declare ML Module "record_update_plugin".
From RecordUpdate Require Export RecordSet.

Ltac solve_settable :=
  match goal with
  | |- Settable ?R =>
    unshelve refine (Build_Settable _ _);
    [ solve_with_eta R
    | solve [ let x := fresh "x" in
              intro x; destruct x; reflexivity ] ]
  end.

Global Hint Extern 1 (Settable _) => solve_settable : typeclass_instances.
