
open Common
type env = Env.t
type parsed_pb = env

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Problem parser for Quip" "quip.parse-pb"))
module K = Kernel

exception E of string
let error e = raise (E e)
let errorf fmt = Fmt.kasprintf error fmt

module Mk_smtlib(Env : Env.S) = struct
  module SA = Smtlib_utils.V_2_6.Ast
  module E = K.Expr
  let ctx = Env.ctx

  let conv_ty ~ty_vars ty : K.expr =
    Log.debug (fun k->k"(@[conv-ty@ %a@])" SA.pp_ty ty);
    let rec loop ty = match ty with
      | SA.Ty_bool -> E.bool ctx
      | SA.Ty_real -> Error.fail "not supported: type Real"
      | SA.Ty_arrow (args, ret) ->
        let args = List.map loop args in
        let ret = loop ret in
        E.arrow_l ctx args ret
      | SA.Ty_app (s, []) when List.exists (fun v -> v.K.v_name=s) ty_vars ->
        let v = List.find (fun v->v.K.v_name=s) ty_vars in
        E.var ctx v
      | SA.Ty_app (s, l) ->
        begin match Env.find_ty_const_by_name s with
          | None -> Error.failf "unknown type constructor '%s'" s
          | Some c ->
            E.const ctx c (List.map loop l)
        end
    in
    loop ty

  let find_b_ b = match Env.find_builtin b with
    | Some x -> x
    | None -> errorf "cannot find builtin %a" Builtin.pp b

  let find_const_ c = match Env.find_const_by_name c with
    | Some x -> x
    | None -> errorf "unknown constant '%s'" c

  let conv_expr e : E.t =
    let app_str c l =
      let c, _is_b = find_const_ c in
      match _is_b, l with
      | Some b, a::tl when Builtin.is_assoc b ->
        List.fold_left
          (fun acc e ->
             E.app_l ctx (E.const ctx c[]) [acc; e])
          a tl
      | _ ->
        E.app_l ctx (E.const ctx c[]) l
    in

    (* apply an associative operator to a list *)
    let app_assoc c cneutral l =
      let c = app_str c [] in
      let rec loop = function
        | [] -> app_str cneutral []
        | [x] -> x
        | x:: tl -> E.app_l ctx c [x; loop tl]
      in
      loop l
    in

    let rec loop (subst:E.t Str_map.t) e =
      let loop' = loop subst in
      match e with
      | SA.Eq (a,b) -> E.app_eq ctx (loop' a) (loop' b)
      | SA.True ->
        E.const ctx (find_b_ Builtin.True) []
      | SA.False ->
        E.const ctx (find_b_ Builtin.False) []
      | SA.Const c when Str_map.mem c subst ->
        Str_map.find c subst
      | SA.Const c ->
        let c, _ = find_const_ c in
        E.const ctx c []
      | SA.App (f, l) ->
        app_str f (List.map loop' l)
      | SA.HO_app (f, a) ->
        E.app ctx (loop' f) (loop' a)
      | SA.Let (bs, body) ->
        let subst2 =
          List.fold_left
            (fun subst2 (x,t) ->
               Str_map.add x (loop' t) subst2)
            subst bs
        in
        loop subst2 body
      | SA.Not u -> app_str "not" [loop' u]
      | SA.Imply (a,b) -> app_str "=>" [loop' a; loop' b]
      | SA.And l -> app_assoc "and" "true" (List.map loop' l)
      | SA.Or l -> app_assoc "or" "false" (List.map loop' l)
      | SA.If (a,b,c) ->
        let a = loop' a in
        let b = loop' b in
        let c = loop' c in
        let ty_b = E.ty_exn b in
        let c_if = E.const ctx (find_b_ Builtin.If) [ty_b] in
        E.app_l ctx c_if [a; b; c]
      | SA.Distinct l ->
        (* translate to [/\_{i<j} l_i /= l_j] *)
        let l = List.map loop' l in
        let l2 =
          CCList.diagonal l
          |> List.rev_map (fun (a,b) ->
              app_str "not" [E.app_eq ctx a b])
        in
        app_assoc "and" "true" l2

      | SA.Arith (_, _)|SA.Match
          (_, _)|SA.Is_a (_, _)|SA.Fun (_, _)
      |SA.Cast (_, _)|SA.Forall (_, _)|SA.Exists (_, _)|SA.Attr (_, _) ->
        errorf "problem parser: unhandled expr: %a" SA.pp_term e
        (* TODO *)
    in
    loop Str_map.empty e

  let add_stmt (stmt:SA.statement) : unit =
    Log.debug (fun k->k"(@[process-stmt@ %a@])" SA.pp_stmt stmt);
    let _loc = stmt.SA.loc in (* TODO: convert *)
    begin match stmt.SA.stmt with

      | SA.Stmt_decl_sort (name, n) ->
        let c = E.new_ty_const ctx name n in
        Log.debug (fun k->k"(@[declare-ty-const@ %a :arity %d@])" K.Const.pp c n);
        Env.decl_ty_const name c;

      | SA.Stmt_decl { fun_ty_vars; fun_name; fun_args; fun_ret } ->
        let ty_vars =
          List.map (fun s -> K.Var.make s (K.Expr.type_ ctx))
            fun_ty_vars
        in
        let ty =
          let tr_ty ty = conv_ty ~ty_vars ty in
          E.arrow_l ctx
            (List.map tr_ty fun_args) (tr_ty fun_ret)
        in
        let c = E.new_const ctx fun_name ty_vars ty in
        Log.debug (fun k->k"(@[declare-const@ %a@])" K.Const.pp c);
        Env.decl_const fun_name c

      | SA.Stmt_assert t ->
        let t = conv_expr t in
        let th = Clause.singleton (Lit.make ctx true t) in
        Log.info (fun k->k"(@[assert@ `%a`@])" Clause.pp th);
        Env.add_assumption th;

      | SA.Stmt_fun_def _ | SA.Stmt_fun_rec _
      | SA.Stmt_funs_rec _ ->
        error "cannot handle function definition yet"
      | SA.Stmt_data _ -> error "cannot handle datatype declaration yet"

      | SA.Stmt_set_logic _|SA.Stmt_set_info (_, _)|SA.Stmt_set_option _
      | SA.Stmt_get_assertions | SA.Stmt_get_assignment | SA.Stmt_get_info _
      | SA.Stmt_get_model | SA.Stmt_get_option _
      | SA.Stmt_get_proof | SA.Stmt_get_unsat_assumptions | SA.Stmt_get_unsat_core
      | SA.Stmt_get_value _ | SA.Stmt_check_sat | SA.Stmt_check_sat_assuming _
      | SA.Stmt_pop _ | SA.Stmt_push _
      | SA.Stmt_reset | SA.Stmt_reset_assertions | SA.Stmt_exit -> ()
    end
end

module Smtlib = struct
  module SA = Smtlib_utils.V_2_6.Ast
  module E = K.Expr

  let create ctx : env = Env.make_new_smt2 ~ctx ()

  type input =
    [ `File of string
    | `Str of string
    ]

  let parse_ ctx (i:input) : parsed_pb =
    let pb =
      match i with
      | `File filename ->
        begin
          try Smtlib_utils.V_2_6.parse_file_exn filename
          with e ->
            errorf "cannot parse smtlib file '%s':@.%s@." filename (Printexc.to_string e)
          end
      | `Str s ->
        try Smtlib_utils.V_2_6.parse_string_exn s
        with e ->
          errorf "cannot parse string:@.%s@." (Printexc.to_string e)
    in
    Log.info (fun k->k"parsed %d statements" (List.length pb));
    Log.debug (fun k->k"@[<v2>problem:@ %a@]@." SA.(pp_list pp_stmt) pb);

    let ((module Env) as env) = create ctx in
    let module S = Mk_smtlib(Env) in
    List.iter S.add_stmt pb;
    env

  let parse_file_exn ctx filename =
    Log.debug (fun k->k"parse SMTLIB file '%s'" filename);
    parse_ ctx (`File filename)

  let parse_file ctx file =
    try Ok (parse_file_exn ctx file)
    with E s -> Error s

  let parse_string ctx s =
    try Ok (parse_ ctx (`Str s))
    with E s -> Error s
end

type syn =
  | Smt2
  [@@deriving show, eq]

let parse_string ctx ~syn s : _ result =
  Profile.with_ "problem.parse-string" @@ fun () ->
  match syn with
  | Smt2 -> Smtlib.parse_string ctx s

let parse_file ctx filename : _ result =
  Profile.with_ "problem.parse-file" @@ fun () ->
  match Filename.extension filename with
  | ".smt2" ->
    Smtlib.parse_file ctx filename
  | ext ->
    Error.failf "unknown problem extension '%s'" ext

let parse_file_exn ctx filename =
  match parse_file ctx filename with
  | Ok x -> x
  | Error e -> Error.fail e
