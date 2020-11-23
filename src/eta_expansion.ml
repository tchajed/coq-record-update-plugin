open Pp

(* let intern env sigma t : Evd.evar_map * EConstr.t =
   Constrintern.interp_constr_evars env sigma t *)

let mkAppl1 f arg = Constr.mkApp (f, Array.of_list [arg])

let solve_with_eta r =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let r_econstr = r in
  (* let (sigma, r) = intern env sigma r in *)
  let r = EConstr.to_constr sigma r in
  match Constr.kind r with
  | Constr.Ind ((i, i_index), u) ->
    let ((i, i_index), u) = Constr.destInd r in

    (* TODO: check if r has multiple constructors (can't be treated as a record) -
       0 is the constructor index here *)
    let r_constructor = Constr.mkConstructU (((i, i_index), 0 + 1), u) in

    let accessor_opts = Recordops.lookup_projections (i, i_index) in
    let accessor_constrs = List.map (fun a_o -> Constr.mkConst (Option.get a_o)) accessor_opts in
    let body = List.fold_left
        (fun acc proj ->
           (* acc (proj x) *)
           mkAppl1 acc (mkAppl1 proj (Constr.mkRel 1)))
        r_constructor accessor_constrs in
    let eta_expansion = Constr.mkLambda (Context.anonR, r, body) in
    Tactics.exact_check (EConstr.of_constr eta_expansion)
  | _ ->
    let _ = CErrors.user_err (str "eta expansion:" ++ spc () ++
                              Printer.pr_econstr_env env sigma r_econstr ++ spc () ++
                              str "is not an inductive") in
    Proofview.tclUNIT ()
