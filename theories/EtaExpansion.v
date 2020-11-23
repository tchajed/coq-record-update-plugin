Declare ML Module "record_update_plugin".

Ltac eta_expansion R :=
  let eta := eval cbn zeta in
               (ltac:(solve_with_eta R) : R -> R) in
  eta.
