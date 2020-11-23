open Pp

let mkApp1 f arg = EConstr.mkApp (f, Array.of_list [arg])

let solve_with_eta (r: EConstr.t) =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  match EConstr.kind sigma r with
  | Constr.Ind ((i, i_index), u) ->
    let ((i, i_index), u) = EConstr.destInd sigma r in

    (* TODO: check if r has multiple constructors (can't be treated as a record) -
       0 is the constructor index here *)
    let r_constructor = EConstr.mkConstructU (((i, i_index), 0 + 1), u) in

    let accessor_opts = Recordops.lookup_projections (i, i_index) in
    let accessor_constrs = List.map (fun a_o -> EConstr.mkConst (Option.get a_o)) accessor_opts in
    let body = List.fold_left
        (fun acc proj ->
           (* acc (proj x) *)
           mkApp1 acc (mkApp1 proj (EConstr.mkRel 1)))
        r_constructor accessor_constrs in
    let eta_expansion = EConstr.mkLambda (Context.anonR, r, body) in
    Tactics.exact_check eta_expansion
  | _ ->
    let _ = CErrors.user_err (str "eta expansion:" ++ spc () ++
                              Printer.pr_econstr_env env sigma r ++ spc () ++
                              str "is not an inductive") in
    Proofview.tclUNIT ()
