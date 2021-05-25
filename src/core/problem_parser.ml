
open Common
type pb = Parsed_pb.t

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Problem parser for Quip" "quip.parse-pb"))

module Smtlib = struct
  module SA = Smtlib_utils.V_2_6.Ast
  module E = K.Expr

  type ('a,'b) tbl =
    ('a,'b) Hashtbl.t
    [@polyprinter Fmt.(CCHashtbl.pp ~pp_start:(return "{@[") ~pp_stop:(return "@]})"))]
  [@@deriving show]

  type 'a vec =
    'a CCVector.vector
    [@polyprinter Fmt.(CCVector.pp ~pp_start:(return "[@[") ~pp_stop:(return "@]]"))]
  [@@deriving show]

  type env = {
    ctx: K.ctx [@opaque];
    consts: (string, K.const [@printer K.Const.pp]) tbl;
    ty_consts: (string, K.ty_const [@printer K.Const.pp]) tbl;
    named_terms: (string, K.Expr.t) tbl;
    builtins: (K.const [@printer K.Const.pp]) Builtin.Tbl.t;
    assms: (K.Thm.t [@printer K.Thm.pp_quoted]) vec;
  } [@@deriving show {with_path=false}]

  let create ctx : env =
    let self = {
      ctx;
      consts=Hashtbl.create 32;
      ty_consts=Hashtbl.create 32;
      builtins=Builtin.Tbl.create 16;
      named_terms=Hashtbl.create 32;
      assms=CCVector.create();
    } in

    (* pre-populate with some builtins *)
    begin
      let bool = E.bool ctx in
      Hashtbl.add self.ty_consts "Bool" (K.Const.bool ctx);
      let (@->) a b = E.arrow_l ctx a b in
      let mkc s b ty =
        let c =  E.new_const ctx s [] ty in
        Hashtbl.add self.consts s c;
        Builtin.Tbl.add self.builtins b c;
      in
      mkc "true" Builtin.True @@ bool;
      mkc "false" Builtin.False @@ bool;
      mkc "not" Builtin.Not @@ [bool] @-> bool;
      mkc "and" Builtin.And @@ [bool;bool] @-> bool;
      mkc "or" Builtin.Or @@ [bool;bool] @-> bool;
      mkc "xor" Builtin.Xor @@ [bool;bool] @-> bool;
      mkc "=>" Builtin.Imply @@ [bool;bool] @-> bool;
    end;
    self

  let conv_ty ~ty_vars (self:env) ty : K.expr =
    Log.debug (fun k->k"(@[conv-ty@ %a@])" SA.pp_ty ty);
    let rec loop ty = match ty with
      | SA.Ty_bool -> E.bool self.ctx
      | SA.Ty_real -> errorf "not supported: type Real"
      | SA.Ty_arrow (args, ret) ->
        let args = List.map loop args in
        let ret = loop ret in
        E.arrow_l self.ctx args ret
      | SA.Ty_app (s, []) when List.exists (fun v -> v.K.v_name=s) ty_vars ->
        let v = List.find (fun v->v.K.v_name=s) ty_vars in
        E.var self.ctx v
      | SA.Ty_app (s, l) ->
        begin match Hashtbl.find self.ty_consts s with
          | exception Not_found -> errorf "unknown type constructor '%s'" s
          | c ->
            E.const self.ctx c (List.map loop l)
        end
    in
    loop ty

  let conv_expr (self:env) e : E.t =
    let find_const_ c =
      try Hashtbl.find self.consts c
      with Not_found -> errorf "unknown constant '%s'" c
    in
    let app_str c l =
      let c = find_const_ c in
      E.app_l self.ctx (E.const self.ctx c[]) l
    in

    (* apply an associative operator to a list *)
    let app_assoc c cneutral l =
      let c = app_str c [] in
      let rec loop = function
        | [] -> app_str cneutral []
        | [x] -> x
        | x:: tl -> E.app_l self.ctx c [x; loop tl]
      in
      loop l
    in

    let rec loop (subst:E.t Str_map.t) e =
      let loop' = loop subst in
      match e with
      | SA.Eq (a,b) -> E.app_eq self.ctx (loop' a) (loop' b)
      | SA.True ->
        E.const self.ctx (Hashtbl.find self.consts "true") []
      | SA.False ->
        E.const self.ctx (Hashtbl.find self.consts "false") []
      | SA.Const c when Str_map.mem c subst ->
        Str_map.find c subst
      | SA.Const c ->
        let c = find_const_ c in
        E.const self.ctx c []
      | SA.App (f, l) ->
        app_str f (List.map loop' l)
      | SA.HO_app (f, a) ->
        E.app self.ctx (loop' f) (loop' a)
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
      | SA.If _
      | SA.Arith (_, _)|SA.Match
          (_, _)|SA.Is_a (_, _)|SA.Fun (_, _)
      | SA.Distinct _|SA.Cast (_, _)|SA.Forall
        (_, _)|SA.Exists (_, _)|SA.Attr (_, _) ->
        errorf "unhandled expr: %a" SA.pp_term e
        (* TODO *)
    in
    loop Str_map.empty e

  let add_stmt (self:env) (stmt:SA.statement) : unit =
    Log.debug (fun k->k"(@[process-stmt@ %a@])" SA.pp_stmt stmt);
    let _loc = stmt.SA.loc in (* TODO: convert *)
    begin match stmt.SA.stmt with

      | SA.Stmt_decl_sort (name, n) ->
        let c = E.new_ty_const self.ctx name n in
        Log.debug (fun k->k"(@[declare-ty-const@ %a :arity %d@])" K.Const.pp c n);
        Hashtbl.replace self.ty_consts name c;

      | SA.Stmt_decl { fun_ty_vars; fun_name; fun_args; fun_ret } ->
        let ty_vars =
          List.map (fun s -> K.Var.make s (K.Expr.type_ self.ctx))
            fun_ty_vars
        in
        let ty =
          let tr_ty ty = conv_ty ~ty_vars self ty in
          E.arrow_l self.ctx
            (List.map tr_ty fun_args) (tr_ty fun_ret)
        in
        let c = E.new_const self.ctx fun_name ty_vars ty in
        Log.debug (fun k->k"(@[declare-const@ %a@])" K.Const.pp c);
        Hashtbl.replace self.consts fun_name c

      | SA.Stmt_assert t ->
        let t = conv_expr self t in
        let th = K.Thm.axiom self.ctx t in
        Log.info (fun k->k"(@[assert@ %a@])" K.Thm.pp_quoted th);
        CCVector.push self.assms th;

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

  let parse_file_exn ctx filename : pb =
    Log.debug (fun k->k"parse SMTLIB file '%s'" filename);
    let pb =
      try Smtlib_utils.V_2_6.parse_file_exn filename
      with e ->
        errorf "cannot parse smtlib file '%s':@.%s@." filename (Printexc.to_string e)
    in
    Log.info (fun k->k"parsed %d statements" (List.length pb));
    Log.debug (fun k->k"@[<v2>problem:@ %a@]@." SA.(pp_list pp_stmt) pb);

    let env = create ctx in
    List.iter (add_stmt env) pb;

    let module PB = struct
      let ctx = env.ctx
      let find_const_by_name n = CCHashtbl.get env.consts n
      let find_ty_const_by_name n = CCHashtbl.get env.ty_consts n
      let find_builtin b = Builtin.Tbl.get env.builtins b
      let assumptions () = CCVector.to_seq env.assms
      let pp_debug out () = pp_env out env
    end in
    (module PB)

  let parse_file ctx file =
    try Ok (parse_file_exn ctx file)
    with Error s -> Error s
end

let parse_file ctx filename : _ result =
  match Filename.extension filename with
  | ".smt2" ->
    Smtlib.parse_file ctx filename
  | ext ->
    errorf "unknown problem extension '%s'" ext

let parse_file_exn ctx filename =
  match parse_file ctx filename with
  | Ok x -> x
  | Error e -> error e
