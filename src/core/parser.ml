
open Common

module A = Ast

module Proof = struct
  module P = A.Proof
  module T = A.Term

  module type ARG = sig
    val filename : string
    val input : Loc.Input.t
    val str : string
    val ast_ctx : A.Small_loc.ctx
  end

  type token = Sexp_lex.token =
    | ATOM of string
    | LIST_OPEN
    | LIST_CLOSE
    | EOI
  [@@deriving show]

  module Make_parser(PA:ARG)() : sig
    val loc : unit -> A.Small_loc.t
    val loc_since : A.Small_loc.t -> A.Small_loc.t
    val cur : unit -> token
    val cur_consume : unit -> token
    val atom : msg:string -> unit -> string
    val consume: unit -> unit
    val expect : ?msg:string -> token -> unit
  end = struct
    let lexbuf = Lexing.from_string ~with_positions:true PA.str
    let() = Loc.set_file lexbuf PA.filename
    let ctx = {Loc.input=PA.input; file=PA.filename}
    let make_loc () = A.Small_loc.of_lexbuf PA.ast_ctx lexbuf

    let cur_ = ref (Sexp_lex.token lexbuf)
    let loc_ = ref (make_loc())

    let[@inline] cur() = !cur_
    let[@inline] loc() = !loc_
    let loc_since l0 = A.Small_loc.union l0 (loc())
    let[@inline] consume() =
      let t = Sexp_lex.token lexbuf in
      cur_ := t;
      loc_ := make_loc();
      ()

    let cur_consume() = let t = cur() in consume(); t

    let trsloc loc = Ast.Small_loc.to_loc PA.ast_ctx loc

    let[@inline] atom ~msg () = match cur() with
      | ATOM s -> consume(); s
      | t ->
        Error.failf ~loc:(trsloc !loc_) "expected %s (<atom>), got %a" msg pp_token t

    let expect ?msg tok =
      let t = cur() in
      if t = tok then consume()
      else (
        let loc = trsloc !loc_ in
        match msg with
        | None ->
          Error.failf ~loc "expected %a, got %a" pp_token tok pp_token t
        | Some msg ->
          Error.failf ~loc "expected %s@ starting with %a,@ got %a" msg pp_token tok pp_token t
      )
  end

  (* custom sexp parser *)
  module Parse(PA : ARG)() = struct
    open Make_parser(PA)()
    let trsloc loc = Ast.Small_loc.to_loc PA.ast_ctx loc

    (** [list_args p] parses instances of [p], followed by ')',
        but does not consume ')' *)
    let list_args p =
      let rec loop acc = match cur() with
        | LIST_CLOSE -> List.rev acc
        | _ ->
          let x = p() in
          loop (x::acc)
      in loop []

    (** [list_of p] parses '(', many [p], then ')' *)
    let list_of p =
      expect LIST_OPEN;
      let l = list_args p in
      expect LIST_CLOSE;
      l

    let rec parse_ty () : A.Ty.t =
      let loc = loc() in
      match cur_consume() with
      | ATOM name -> A.Ty.constr ~loc name []
      | LIST_OPEN ->
        let res =
          match cur_consume() with
          | ATOM "->" ->
            let args = list_args parse_ty in
            begin match List.rev args with
              | ret :: l -> A.Ty.arrow ~loc (List.rev l) ret
              | [] -> assert false
            end
          | ATOM name ->
            let args = list_args parse_ty in
            A.Ty.constr ~loc name args
          | _ -> Error.failf ~loc:(trsloc loc) "expected atom"
        in
        expect LIST_CLOSE;
        res
      | _t ->
        Error.failf ~loc:(trsloc loc) "expected a type, got %a" pp_token _t

    (** Parse term *)
    let rec parse_term () : T.t =
      let loc0 = loc() in
      match cur_consume () with
      | ATOM name ->
        let loc = loc_since loc0 in
        T.const ~loc name
      | LIST_OPEN ->
        let res =
          match cur_consume() with
          | ATOM "=" ->
            let a = parse_term () in
            let b = parse_term () in

            let loc = loc_since loc0 in
            T.eq ~loc a b

          | ATOM "not" ->
            let a = parse_term () in

            let loc = loc_since loc0 in
            T.not ~loc a

          | ATOM "?" ->
            let name = atom ~msg:"name" () in
            let ty = parse_ty() in

            let loc = loc_since loc0 in
            T.var ~loc (A.Var.make ~ty:(Some ty) name)

          | ATOM "let" ->
            let p_pair () =
              expect ~msg:"pair (<variable> <term>)" LIST_OPEN;
              let v = atom ~msg:"variable" () in
              let t = parse_term() in
              expect ~msg:"close let binding" LIST_CLOSE;
              A.Var.make ~ty:() v, t
            in
            let l = list_of p_pair in
            let bod = parse_term () in

            let loc = loc_since loc0 in
            T.let_ ~loc l bod

          | ATOM ("@" | "ref") ->
            let name = atom ~msg:"name of term" () in

            let loc = loc_since loc0 in
            T.ref ~loc name

          | ATOM "ite" ->
            let a = parse_term () in
            let b = parse_term () in
            let c = parse_term () in

            let loc = loc_since loc0 in
            T.ite ~loc a b c

          | ATOM "lambda" ->
            expect ~msg:"lambda argument list" LIST_OPEN;
            let v = atom ~msg:"variable"() in
            let ty = parse_ty() in
            let v = A.Var.make ~ty v in
            expect ~msg:"close lambda argument list" LIST_CLOSE;
            let bod = parse_term () in

            let loc = loc_since loc0 in
            T.fun_ ~loc v bod

          | LIST_OPEN ->
            expect ~msg:"(_ is <cstor>)" (ATOM "_");
            expect (ATOM "is");
            let c = atom ~msg:"constructor" () in
            expect LIST_CLOSE;
            let u = parse_term () in

            let loc = loc_since loc0 in
            T.is_a ~loc c u

          | ATOM f ->
            let args = list_args parse_term in

            let loc = loc_since loc0 in
            T.app_name ~loc f args

        (*
        | List [{s=Atom "!";_}; a; {s=Atom ":named";_}; {s=Atom name;_}] ->
          let u = loop a in
          Hashtbl.add self.named_terms name u;
          u
        | List ({s=Atom "!";_} :: _) ->
          parse_errorf s "unimplemented `!`" (* TODO: named expr from input problem? *)
        *)

          | _t -> Error.failf ~loc:(trsloc loc0) "expected a term, got %a" pp_token _t
        in
        expect LIST_CLOSE;
        res
      | _t -> Error.failf ~loc:(trsloc loc0) "unexpected %a, expected a term" pp_token _t

    (** Parse substitution *)
    let parse_subst () : A.Subst.t =
      let loc0 = loc() in
      match cur_consume() with
      | LIST_OPEN ->
        let rec loop acc = match cur() with
          | LIST_CLOSE -> consume(); List.rev acc
          | _ ->
            let v = atom ~msg:"variable" () in
            let v = Ast.Var.make ~ty:() v in
            let t = parse_term () in
            loop ((v,t) :: acc)
        in
        loop []

      | _t ->
        Error.failf ~loc:(trsloc loc0)
          "unexpected %a, expected substitution of shape `(<var> <term> …)`"
          pp_token _t

    let parse_lits () : A.term list =
      expect ~msg:"clause (cl t1…tn)" LIST_OPEN;
      expect (ATOM "cl");
      let l = list_args parse_term in
      expect ~msg:"closing clause" LIST_CLOSE;
      l

    (** Parse clause *)
    let parse_clause () : A.clause =
      let loc0 = loc() in
      expect ~msg:"clause (cl …) or (@ <name>)" LIST_OPEN;
      let res =
        match cur() with
        | ATOM ("@" | "ref") ->
          consume();
          let name = atom ~msg:"name" () in

          let loc = loc_since loc0 in
          A.Clause.(mk ~loc @@ Clause_ref name)

        | ATOM "cl" ->
          consume();
          let c_lits = list_args parse_term in

          let loc = loc_since loc0 in
          A.Clause.(mk ~loc @@ Clause c_lits)

        | _t ->
          Error.failf ~loc:(trsloc loc0)
            "unexpected %a, expected a clause `(cl t1 t2 … tn)` or `(@ <name>)`"
            pp_token _t
      in
      expect ~msg:"closing clause" LIST_CLOSE;
      res

    let parse_assumption() =
      expect LIST_OPEN;
      let name = atom ~msg:"name" () in
      let lit = parse_term() in
      expect LIST_CLOSE;
      name, lit

    (** Parse proof *)
    let rec parse_proof () : P.t =
      let loc0 = loc() in
      match cur_consume() with
      | ATOM "t-ne-f" -> P.true_neq_false ~loc:loc0
      | ATOM "t-is-t" -> P.true_is_true ~loc:loc0

      | LIST_OPEN ->
        let res =
          match cur_consume() with
          | ATOM "steps" ->
            let assms = list_of parse_assumption in
            let steps = list_of parse_step in

            let loc = loc_since loc0 in
            P.composite_l ~loc ~assms steps

          | ATOM "with" ->
            let parse_binding () =
              expect ~msg:"(<name> <term>)" LIST_OPEN;
              let name = atom ~msg:"variable" () in
              let t = parse_term () in
              expect LIST_CLOSE;
              name, t
            in

            let bs = list_of parse_binding in
            let p1 = parse_proof () in

            let loc = loc_since loc0 in
            P.with_ ~loc bs p1

          | ATOM "ccl" ->
            let cl = parse_clause() in

            let loc = loc_since loc0 in
            P.cc_lemma ~loc cl

          | ATOM "ccli" ->
            let prs = list_of parse_proof in
            let t = parse_term () in
            let u = parse_term () in

            let loc = loc_since loc0 in
            P.cc_imply_l ~loc prs t u

          | ATOM "bool-c" ->
            let name = atom ~msg:"name of rule" () in
            let name_loc = loc() in
            let ts = list_args parse_term in

            let name = P.(match name with
              | "and-i" -> And_i
              | "and-e" -> And_e
              | "or-i" -> Or_i
              | "or-e" -> Or_e
              | "not-i" -> Not_i
              | "not-e" -> Not_e
              | "imp-i" -> Imp_i
              | "imp-e" -> Imp_e
              | "xor-i" -> Xor_i
              | "xor-e" -> Xor_e
              | "eq-i" -> Eq_i
              | "eq-e" -> Eq_e
              | _ -> Error.failf ~loc:(trsloc name_loc) "unknown bool-c rule: '%s'" name
            ) in

            let loc = loc_since loc0 in
            P.bool_c ~loc name ts

          | ATOM "clause-rw" ->
            let cl = parse_clause () in
            let p = parse_proof () in
            let using = list_of parse_proof in

            let loc = loc_since loc0 in
            P.clause_rw ~loc ~res:cl p ~using

          | ATOM "rup" ->
            let cl = parse_clause () in
            let using = list_of parse_proof in

            let loc = loc_since loc0 in
            P.rup_res ~loc cl using

          | ATOM "p1" ->
            let rw_with = parse_proof () in
            let p = parse_proof () in

            let loc = loc_since loc0 in
            P.paramod1 ~loc ~rw_with p

          | ATOM "ite-true" ->
            let t = parse_term() in
            let loc = loc_since loc0 in
            P.ite_true ~loc t

          | ATOM "ite-false" ->
            let t = parse_term() in
            let loc = loc_since loc0 in
            P.ite_false ~loc t

          | ATOM "r" ->
            let pivot = parse_term() in
            let p1 = parse_proof() in
            let p2 = parse_proof() in
            let loc = loc_since loc0 in
            P.res ~loc ~pivot p1 p2

          | ATOM "r1" ->
            let p1 = parse_proof() in
            let p2 = parse_proof() in
            let loc = loc_since loc0 in
            P.res1 ~loc p1 p2

          | ATOM "hres" ->

            let pstep () =
              let loc0 = loc() in
              expect ~msg:"hres_step" LIST_OPEN;
              match cur_consume() with
              | ATOM "p1" ->
                let sub_p = parse_proof () in
                let loc = loc_since loc0 in
                P.p1 ~loc sub_p

              | ATOM "p" ->
                let lhs = parse_term() in
                let rhs = parse_term() in
                let sub_p = parse_proof() in
                let loc = loc_since loc0 in
                P.p ~loc sub_p ~lhs ~rhs

              | ATOM "r1" ->
                let sub_p = parse_proof() in
                let loc = loc_since loc0 in
                P.r1 ~loc sub_p

              | ATOM "r" ->
                let pivot = parse_term () in
                let sub_p = parse_proof() in
                let loc = loc_since loc0 in
                P.r ~loc ~pivot sub_p

              | _t ->
                Error.failf ~loc:(trsloc loc0)
                  "unexpected %a, expected a step for `hres` (hint: p1|r1|p|r)"
                  pp_token _t
            in

            let init = parse_proof() in
            let steps = list_of pstep in
            let loc = loc_since loc0 in
            P.hres_l ~loc init steps

          | ATOM "subst" ->
            let subst = parse_subst() in
            let p = parse_proof() in
            let loc = loc_since loc0 in
            P.subst ~loc subst p

          | ATOM "assert" ->
            let t = parse_term() in
            let loc = loc_since loc0 in
            P.assertion ~loc t

          | ATOM "assert-c" ->
            let cl = parse_clause() in
            let loc = loc_since loc0 in
            P.assertion_c ~loc cl

          | ATOM "refl" ->
            let t = parse_term() in
            let loc = loc_since loc0 in
            P.refl ~loc t

          | ATOM ("@" | "ref") ->
            let name = atom ~msg:"step name" () in
            let loc = loc_since loc0 in
            P.ref_by_name ~loc name

          | _t ->
            Error.failf ~loc:(trsloc loc0) "unexpected %a, expected a proof"
              pp_token _t

        in
        expect ~msg:"closing ')' for proof" LIST_CLOSE;
        res

      | _t ->
        Error.failf ~loc:(trsloc loc0)
          "unexpected %a, expected a proof" pp_token _t

    (** Parse a composite step *)
    and parse_step () : _ P.composite_step =
      let loc0 = loc() in
      expect ~msg:"composite step" LIST_OPEN;
      let res =
        match cur_consume() with
        | ATOM "deft" ->
          let name = atom ~msg:"term name" () in
          let t = parse_term () in
          let loc = loc_since loc0 in
          P.deft name ~loc t

        | ATOM "stepc" ->
          let name = atom ~msg:"clause name" () in
          let cl = parse_lits() in
          let sub_pr = parse_proof() in
          let loc = loc_since loc0 in
          P.stepc ~loc ~name cl sub_pr

        | ATOM "step" ->
          let name = atom ~msg:"clause name" () in
          let sub_pr = parse_proof() in
          let loc = loc_since loc0 in
          P.step ~loc ~name sub_pr

        | ATOM "ty_decl" ->
          let name = atom ~msg:"type name" () in
          let loc_n = loc() in
          let n = atom ~msg:"arity" () in
          let n = try int_of_string n
            with _ -> Error.failf ~loc:(trsloc loc_n) "expect arity (a number)" in
          let loc = loc_since loc0 in
          P.decl_ty_const ~loc name n

        | ATOM "decl" ->
          let name = atom ~msg:"symbol name" () in
          let ty = parse_ty() in
          let loc = loc_since loc0 in
          P.decl_const ~loc name ty

        | ATOM "def" ->
          let name = atom ~msg:"defined term name" () in
          let ty = parse_ty() in
          let rhs = parse_term() in
          let loc = loc_since loc0 in
          P.define_const ~loc name ty rhs

        | _t ->
          Error.failf ~loc:(trsloc loc0)
            "unexpected %a,@ expected a composite step (`deft` or `stepc`)"
            pp_token _t
      in
      expect ~msg:"closing proof step" LIST_CLOSE;
      res

    let parse_sexp_l_ () : P.t =
      expect LIST_OPEN;
      expect (ATOM "quip");
      expect (ATOM "1");

      begin match cur() with
        | LIST_CLOSE ->
          consume();

          let loc0 = loc() in
          (* toplevel steps *)
          let rec loop acc =
            match cur() with
            | EOI ->
              let loc = loc_since loc0 in
              let steps = List.rev acc in
              P.composite_l ~loc ~assms:[] steps
            | _ ->
              let p = parse_step() in
              loop (p::acc)
          in
          loop []

        | _ ->
          let p = parse_proof () in
          expect ~msg:"closing top proof" LIST_CLOSE;
          p
      end

    let parse_top () : P.t =
      try
        parse_sexp_l_ ()
      with Sexp_lex.Error (line,col,msg) ->
        Error.failf "Invalid syntax at %d:%d:\n%s" line col msg
  end

  let parse_string ?(filename="<string>") (str:string) : P.t * _ =
    Profile.with_ "parse-proof" @@ fun () ->
    let input = Loc.Input.string str in
    let ast_ctx = A.Small_loc.create ~filename str in
    let module P = Parse(struct
        let filename=filename
        let input = input
        let str = str
        let ast_ctx = ast_ctx
      end) () in
    P.parse_top (), ast_ctx
end

