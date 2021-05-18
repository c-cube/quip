
open Common

module A = Ast

(*
type env = {
  ctx: K.ctx;
  tys: (string, K.ty_const) Hashtbl.t;
  consts: (string, K.const) Hashtbl.t;
  named_terms: (string, E.t) Hashtbl.t;
  proof: P.t;
  mutable axioms: K.thm list;
}

let create_env ctx : env =
  let self = {
    ctx;
    tys=Hashtbl.create 32;
    consts=Hashtbl.create 32;
    named_terms=Hashtbl.create 8;
    axioms=[];
    proof=P.create();
  } in
  let bool = E.bool ctx in
  Hashtbl.add self.tys "Bool" (K.Const.bool ctx);
  let (@->) a b = E.arrow_l ctx a b in
  let mkc s ty =
    Hashtbl.add self.consts s (E.new_const ctx s [] ty);
  in
  mkc "true" @@ [bool] @-> bool;
  mkc "false" @@ [bool] @-> bool;
  mkc "not" @@ [bool] @-> bool;
  mkc "and" @@ [bool;bool] @-> bool;
  mkc "or" @@ [bool;bool] @-> bool;
  mkc "xor" @@ [bool;bool] @-> bool;
  mkc "=>" @@ [bool;bool] @-> bool;
  self
   *)

(* TODO: parse problems into trustee terms?
module Pb = struct
  module Smtlib = Smtlib_utils.V_2_6
  module A = Smtlib.Ast

  let conv_ty ~ty_vars (self:env) ty : E.t =
    Log.debugf 5 (fun k->k"(@[conv-ty@ %a@])" A.pp_ty ty);
    let rec loop ty = match ty with
      | A.Ty_bool -> E.bool self.ctx
      | A.Ty_real -> errorf (fun k->k"not supported: type Real");
      | A.Ty_arrow (args, ret) ->
        let args = List.map loop args in
        let ret = loop ret in
        E.arrow_l self.ctx args ret
      | A.Ty_app (s, []) when List.exists (fun v -> v.K.v_name=s) ty_vars ->
        let v = List.find (fun v->v.K.v_name=s) ty_vars in
        E.var self.ctx v
      | A.Ty_app (s, l) ->
        begin match Hashtbl.find self.tys s with
          | exception Not_found -> errorf (fun k->k"unknown type constructor '%s'" s)
          | c ->
            E.const self.ctx c (List.map loop l)
        end
    in
    loop ty

  let conv_expr (self:env) e : E.t =
    let find_const_ c =
      try Hashtbl.find self.consts c
      with Not_found -> errorf (fun k->k"unknown constant '%s'" c)
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
      | A.Eq (a,b) -> E.app_eq self.ctx (loop' a) (loop' b)
      | A.True ->
        E.const self.ctx (Hashtbl.find self.consts "true") []
      | A.False ->
        E.const self.ctx (Hashtbl.find self.consts "false") []
      | A.Const c when Str_map.mem c subst ->
        Str_map.find c subst
      | A.Const c ->
        let c = find_const_ c in
        E.const self.ctx c []
      | A.App (f, l) ->
        app_str f (List.map loop' l)
      | A.HO_app (f, a) ->
        E.app self.ctx (loop' f) (loop' a)
      | A.Let (bs, body) ->
        let subst2 =
          List.fold_left
            (fun subst2 (x,t) ->
               Str_map.add x (loop' t) subst2)
            subst bs
        in
        loop subst2 body
      | A.Not u -> app_str "not" [loop' u]
      | A.Imply (a,b) -> app_str "=>" [loop' a; loop' b]
      | A.And l -> app_assoc "and" "true" (List.map loop' l)
      | A.Or l -> app_assoc "or" "false" (List.map loop' l)
      | A.Arith (_, _)|A.Match
          (_, _)|A.If (_, _, _)|A.Is_a (_, _)|A.Fun (_, _)
      | A.Distinct _|A.Cast (_, _)|A.Forall
        (_, _)|A.Exists (_, _)|A.Attr (_, _) ->
        errorf (fun k->k"unhandled expr: %a" A.pp_term e)
        (* TODO *)
    in
    loop Str_map.empty e

  let process_stmt (self:env) (stmt:A.statement) : unit =
    Log.debugf 5 (fun k->k"(@[process-stmt@ %a@])" A.pp_stmt stmt);
    let _loc = stmt.A.loc in (* TODO: convert *)
    begin match stmt.A.stmt with

      | A.Stmt_decl_sort (name, n) ->
        let c = E.new_ty_const self.ctx name n in
        Log.debugf 2 (fun k->k"(@[declare-ty-const@ %a :arity %d@])" K.Const.pp c n);
        Hashtbl.replace self.tys name c;

      | A.Stmt_decl { fun_ty_vars; fun_name; fun_args; fun_ret } ->
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
        Log.debugf 2 (fun k->k"(@[declare-const@ %a@])" K.Const.pp c);
        Hashtbl.replace self.consts fun_name c

      | A.Stmt_assert t ->
        let t = conv_expr self t in
        let th = K.Thm.axiom self.ctx t in
        Log.debugf 1 (fun k->k"(@[assert@ %a@])" K.Thm.pp_quoted th);
        self.axioms <- th :: self.axioms

      | A.Stmt_fun_def _ | A.Stmt_fun_rec _
      | A.Stmt_funs_rec _ ->
        errorf (fun k->k"cannot handle function definition yet")
      | A.Stmt_data _ -> errorf (fun k->k"cannot handle datatype declaration yet")

      | A.Stmt_set_logic _|A.Stmt_set_info (_, _)|A.Stmt_set_option _
      | A.Stmt_get_assertions | A.Stmt_get_assignment | A.Stmt_get_info _
      | A.Stmt_get_model | A.Stmt_get_option _
      | A.Stmt_get_proof | A.Stmt_get_unsat_assumptions | A.Stmt_get_unsat_core
      | A.Stmt_get_value _ | A.Stmt_check_sat | A.Stmt_check_sat_assuming _
      | A.Stmt_pop _ | A.Stmt_push _
      | A.Stmt_reset | A.Stmt_reset_assertions | A.Stmt_exit -> ()
    end

  let parse_chan ?(filename="<unknown>") (self:env) (ic:in_channel) : unit =
    match Smtlib.parse_chan ~filename ic with
    | Error e -> errorf (fun k->k"parse error for problem %S:@ %s" filename e)
    | Ok stmts ->
      List.iter (process_stmt self) stmts;
      ()
end
   *)

module Proof = struct
  module P = A.Proof
  module T = A.Term

  type sexp = {
    loc: Loc.t option;
    s: sexp_view;
  }
  and sexp_view =
    | Atom of string
    | List of sexp list

  (* custom sexp parser *)
  module SP = CCSexp.Make(struct
      type t = sexp
      type loc = Loc.t option
      let make_loc = Some (fun (x1,x2) (x3,x4) s -> Some (Loc.mk s x1 x2 x3 x4))
      let atom_with_loc ~loc s = {loc; s=Atom s}
      let list_with_loc ~loc l = {loc; s=List l}
      let atom = atom_with_loc ~loc:None
      let list = list_with_loc ~loc:None
      let match_ self ~atom ~list =
        match self.s with
        | Atom s -> atom s
        | List l -> list l
      end)

  (* truncate the sexp so it's small, for reasonably concise error reporting *)
  let rec truncate_sexp_ ~d (s:sexp) : sexp =
    match s.s with
    | Atom _ | List [] -> s
    | List _ when d<=0 -> {s with s=Atom "..."}
    | List l ->
      {s with s=List (List.map (truncate_sexp_ ~d:(d-1)) l)}

  let parse_errorf s fmt =
    Fmt.kasprintf (fun s -> error s)
      ("@[<v>at %a@ in %a:@ " ^^ fmt ^^ "@]")
      Loc.pp_opt s.loc SP.pp (truncate_sexp_ ~d:2 s)

  let ty_of_sexp _s : A.Ty.t = assert false

  let t_of_sexp (sexp:sexp) : T.t =
    let rec loop s : T.t =
      let loc = s.loc in
      match s.s with
      | Atom name -> T.const ~loc name
      | List [{s=Atom "=";_}; a; b] -> T.eq ~loc (loop a) (loop b)
                                         (*
      | List [{s=Atom "!";_}; a; {s=Atom ":named";_}; {s=Atom name;_}] ->
        let u = loop a in
        Hashtbl.add self.named_terms name u;
        u
      | List ({s=Atom "!";_} :: _) ->
        parse_errorf s "unimplemented `!`" (* TODO: named expr *)
                                            *)
      | List [{s=Atom "let";_}; {s=List l;_}; bod] ->
        let l = List.map (function
            | {s=List [{s=Atom v;_}; t];_} -> A.Var.make ~ty:() v, loop t
            | s -> parse_errorf s "expected `(<var> <term>)`")
            l
        in
        T.let_ ~loc l @@ loop bod
      | List [{s=Atom "ite";_}; a; b; c] ->
        T.ite ~loc (loop a) (loop b) (loop c)
      | List [{s=Atom "lambda";_}; {s=List[{s=Atom v; _}; ty];_}; bod] ->
        let v = A.Var.make ~ty:(ty_of_sexp ty) v in
        T.fun_ ~loc v (loop bod)
      | List ({s=Atom f;_} :: args) ->
        let args = List.map loop args in
        T.app_name ~loc f args
      | _ -> parse_errorf s "expected term"
    in loop sexp

  let lit_of_sexp (sexp:sexp) : A.lit =
    match sexp.s with
    | List [{s=Atom "+";_}; t] -> A.Lit.a (t_of_sexp t)
    | List [{s=Atom "-";_}; t] -> A.Lit.na (t_of_sexp t)
    | _ -> parse_errorf sexp "expected `(± <term>)`"

  let cl_of_sexp (s:sexp) : A.clause =
    match s.s with
    | List ({s=Atom "cl";_} :: lits) ->
      let c_lits = List.map lit_of_sexp lits in
      c_lits
    | _ -> parse_errorf s "expected a clause `(cl t1 t2 … tn)`"

  (*
  let rules =
    let open P in
    [ "res", Pr_resolution;
      "cc", Pr_congruence;
      "cleq", Pr_clause_eq;
      "assume", Pr_assume;
      "thl", Pr_theory_lemma;
    ] |> CCHashtbl.of_list

  (* find a keyword argument in a sexp *)
  let rec find_kw k = function
    | [] -> None
    | {s=Atom x;_} :: y :: _ when x=k -> Some y
    | _ :: _ :: tl -> find_kw k tl
    | s :: _ -> parse_errorf s "invalid keyword list"

  let premises_of_sexp self s =
    match s.s with
    | List l ->
      List.map
        (function
          | {s=Atom name;_} -> P.find_step self.proof name
          | s -> parse_errorf s "expected a previous step")
        l
    | _ -> parse_errorf s "expected a list of premises"

  let rule_of_sexp s =
    match s.s with
    | Atom name ->
      (try Hashtbl.find rules name
       with Not_found -> parse_errorf s "expected rule, unknown rule %S" name)
    | List _ -> parse_errorf s "expected rule"

  let step_of_sexp (self:env) (s:sexp) : P.step =
    match s.s with
    | List [{s=Atom "assume";_}; {s=Atom name;_}; t] ->
      let c = {P.c_lits=[t_of_sexp self t]} in
      {P.ps_name=name; ps_clause=c; ps_rule=P.Pr_assume; ps_premises=[]; }
    | List ({s=Atom "step";_} :: {s=Atom name;_} :: c :: kw) ->
      let c = cl_of_sexp self c in
      let ps_premises =
        find_kw ":premises" kw
        |> CCOpt.map (premises_of_sexp self) |> CCOpt.get_or ~default:[]
      and ps_rule =
        find_kw ":rule" kw
        |> CCOpt.map rule_of_sexp
        |> CCOpt.get_lazy (fun () -> parse_errorf s "missing rule")
      in
      {P.ps_name=name; ps_clause=c; ps_rule; ps_premises; }
    | _ -> parse_errorf s "expected a proof step, got %a" SP.pp s

  let add_step (self:env) (s:sexp) : unit =
    Log.debugf 1 (fun k->k"(@[proof.add-step@ %a@])" SP.pp s);
    let s = step_of_sexp self s in
    P.add_step self.proof s
     *)

  let asm_of_sexp s =
    match s.s with
    | List [{s=Atom name;_}; lit] ->
      let lit = lit_of_sexp lit in
      name, lit
    | _ -> parse_errorf s "expected an assumption `(<name> <lit>)`"

  let rec p_of_sexp (s:sexp) : P.t =
    match s.s with
    | List [{s=Atom "steps";_}; {s=List asms;_}; {s=List steps;_}] ->
      let assms = List.map asm_of_sexp asms in
      let steps = List.map step_of_sexp steps in
      P.composite_l ~assms steps

    | List [{s=Atom "cc-lemma";_}; cl] ->
      let cl = cl_of_sexp cl in
      P.cc_lemma cl

    | List [{s=Atom "bool-c";_}; cl] ->
      let cl = cl_of_sexp cl in
      P.bool_c cl

    | List ({s=Atom "hres";_} ::
            {s=List [{s=Atom "init";_}; init];_} :: steps) ->
      let pstep s = match s.s with
        | List [{s=Atom "p1";_}; sub_p] -> P.p1 (p_of_sexp sub_p)
        | List [{s=Atom "p";_}; lhs; rhs; sub_p] ->
          let lhs = t_of_sexp lhs in
          let rhs = t_of_sexp rhs in
          let sub_p = p_of_sexp sub_p in
          P.p sub_p ~lhs ~rhs
        | List [{s=Atom "r1";_}; sub_p] -> P.r1 (p_of_sexp sub_p)
        | List [{s=Atom "r";_}; {s=List [{s=Atom "pivot";_}; piv];_}; sub_p] ->
          let pivot = t_of_sexp piv in
          let sub_p = p_of_sexp sub_p in
          P.r ~pivot sub_p
        | _ ->
          parse_errorf s "expected a step for `hres` (hint: p1|r1|p|r)"
      in
      let init = p_of_sexp init in
      P.hres_l init (CCList.map pstep steps)

    | List [{s=Atom "assert";_}; t] ->
      P.assertion (t_of_sexp t)

    | List [{s=Atom "refl";_}; t] ->
      P.refl (t_of_sexp t)

    | List [{s=Atom "ref";_}; {s=Atom name;_}] ->
      P.ref_by_name name

    | _ -> parse_errorf s "expected a proof"

  and step_of_sexp (s:sexp) : P.composite_step =
    match s.s with
    | List [{s=Atom "deft";_}; {s=Atom name;loc=loc_name}; t] ->
      let t = t_of_sexp t in
      P.deft (T.const ~loc:loc_name name) t
    | List [{s=Atom "stepc";_}; {s=Atom name;_}; cl; sub_pr] ->
      let cl = cl_of_sexp cl in
      let sub_pr = p_of_sexp sub_pr in
      P.stepc ~name cl sub_pr
    | _ -> parse_errorf s "expected a composite step (`deft` or `stepc`)"

  let parse_sexp_ (s:sexp) : P.t =
    match s.s with
    | List [{s=Atom "quip";_}; {s=Atom "1";_}; bod] -> p_of_sexp bod
    | _ -> parse_errorf s "expected `(quip 1 <proof>)`"

  let parse_lexbuf_ ~filename lexbuf : P.t =
    Loc.set_file lexbuf filename;
    let dec = SP.Decoder.of_lexbuf lexbuf in
    let s =
      match SP.Decoder.next dec with
      | SP.Yield s ->
        begin match SP.Decoder.next dec with
          | SP.End -> s
          | _ -> errorf "expected file to end after first expression"
        end
      | SP.Fail e -> errorf "parse error in %s: %s" filename e
      | SP.End -> error "unexpected end of file, expected sexp"
    in
    parse_sexp_ s

  let parse_string ?(filename="<string>") (s:string) : P.t =
    let lexbuf = Lexing.from_string s in
    parse_lexbuf_ ~filename lexbuf

  let parse_chan ?(filename="<channel>") (ic:in_channel) : P.t =
    let lexbuf = Lexing.from_channel ic in
    parse_lexbuf_ ~filename lexbuf
end

