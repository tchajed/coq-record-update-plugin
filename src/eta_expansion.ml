open Pp
open Structures

let mkApp1 f arg = EConstr.mkApp (f, Array.of_list [arg])

let lookup_projections_opt ind =
  try Some (Structure.find_projections ind)
  with Not_found -> None

let traverse_list_opt (x: 'a option list) : 'a list option =
  try Some (List.map Option.get x)
  with Option.IsNone -> None

let solve_with_eta (r: EConstr.t) =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  match EConstr.kind sigma r with
  | Constr.Ind (ind, u) ->
    (* TODO: check if r has multiple constructors (can't be treated as a record) -
       0 is the constructor index here *)
    let r_constructor = EConstr.mkConstructU ((ind, 0 + 1), u) in
    (match lookup_projections_opt ind with
     | None -> let _ = CErrors.user_err (str "eta expansion: inductive" ++ spc () ++
                                         Printer.pr_econstr_env env sigma r ++ spc () ++
                                         str "is not a record") in
       Proofview.tclUNIT ()
     | Some projs ->
       match traverse_list_opt projs with
       | None -> let _ = CErrors.user_err (str "eta expansion: inductive" ++ spc () ++
                                           Printer.pr_econstr_env env sigma r ++ spc () ++
                                           str "does not have projection functions for all fields") in
         Proofview.tclUNIT ()
       | Some accessors ->
         let accessor_constrs = List.map EConstr.mkConst accessors in
         let body = List.fold_left
             (fun acc proj ->
                (* acc (proj x) *)
                mkApp1 acc (mkApp1 proj (EConstr.mkRel 1)))
             r_constructor accessor_constrs in
         let eta_expansion = EConstr.mkLambda (Context.anonR, r, body) in
         Tactics.exact_check eta_expansion)
  | _ ->
    let _ = CErrors.user_err (str "eta expansion:" ++ spc () ++
                              Printer.pr_econstr_env env sigma r ++ spc () ++
                              str "is not an inductive") in
    Proofview.tclUNIT ()
