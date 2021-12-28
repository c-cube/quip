
open Common

module A = Ast

module Proof = struct
  module P = A.Proof
  module T = A.Term

  type sexp = {
    loc: Loc.t;
    s: sexp_view;
  }
  and sexp_view =
    | Atom of string
    | List of sexp list

  module type ARG = sig
    val filename : string
    val input : Loc.Input.t
  end

  (* custom sexp parser *)
  module Parse(PA : ARG)() = struct
    module S_arg = struct
      type t = sexp
      type loc = Loc.t
      let make_loc = Some (fun (x1,x2) (x3,x4) _ ->
          Loc.mk ~input:PA.input ~filename:PA.filename x1 x2 x3 x4)
      let atom_with_loc ~loc s = {loc; s=Atom s}
      let list_with_loc ~loc l = {loc; s=List l}
      let atom = atom_with_loc ~loc:Loc.none
      let list = list_with_loc ~loc:Loc.none
      let match_ self ~atom ~list =
        match self.s with
        | Atom s -> atom s
        | List l -> list l
    end

    include CCSexp.Make(S_arg)

    let rec ty_of_sexp s : A.Ty.t =
      let loc = s.loc in
      match s.s with
      | Atom name -> A.Ty.constr ~loc name []
      | List ({s=Atom "->";_} :: (_::_ as args)) ->
        let rargs = List.rev_map ty_of_sexp args in
        begin match rargs with
          | ret :: l -> A.Ty.arrow ~loc (List.rev l) ret
          | [] -> assert false
        end
      | List ({s=Atom name;_} :: args) ->
        let args = List.map ty_of_sexp args in
        A.Ty.constr ~loc name args
      | _ ->
        Error.failf ~loc "expected a type"

    (** Parse term *)
    let t_of_sexp (sexp:sexp) : T.t =
      let rec loop s : T.t =
        let loc = s.loc in
        match s.s with
        | Atom name -> T.const ~loc name
        | List [{s=Atom "=";_}; a; b] -> T.eq ~loc (loop a) (loop b)
        | List [{s=Atom "not";_}; a] -> T.not ~loc (loop a)

        | List [{s=Atom "?";_}; {s=Atom name;_}; ty] ->
          let ty = ty_of_sexp ty in
          T.var ~loc (A.Var.make ~ty:(Some ty) name)

        | List [{s=Atom "let";_}; {s=List l;_}; bod] ->
          let l = List.map (function
              | {s=List [{s=Atom v;_}; t];_} -> A.Var.make ~ty:() v, loop t
              | _ -> Error.failf ~loc "expected `(<var> <term>)`")
              l
          in
          T.let_ ~loc l @@ loop bod

        | List [{s=Atom ("@" | "ref");_}; {s=Atom name;_}] ->
          T.ref ~loc name

        | List [{s=Atom "ite";_}; a; b; c] ->
          T.ite ~loc (loop a) (loop b) (loop c)

        | List [{s=Atom "lambda";_}; {s=List[{s=Atom v; _}; ty];_}; bod] ->
          let v = A.Var.make ~ty:(ty_of_sexp ty) v in
          T.fun_ ~loc v (loop bod)

        | List ({s=Atom f;_} :: args) ->
          let args = List.map loop args in
          T.app_name ~loc f args

        (*
        | List [{s=Atom "!";_}; a; {s=Atom ":named";_}; {s=Atom name;_}] ->
          let u = loop a in
          Hashtbl.add self.named_terms name u;
          u
        | List ({s=Atom "!";_} :: _) ->
          parse_errorf s "unimplemented `!`" (* TODO: named expr from input problem? *)
        *)

        | _ -> Error.failf ~loc "expected a term"
      in loop sexp

    (** Parse substitution *)
    let s_of_sexp (sexp:sexp) : A.Subst.t =
      let rec of_l = function
        | [] -> []
        | {s=Atom v;_} :: t :: tl ->
          let v = Ast.Var.make ~ty:() v in
          let t = t_of_sexp t in
          (v,t) :: of_l tl
        | {loc;_} :: _ :: _ ->
          Error.failf ~loc "expected a variable"
        | [{loc;_}] ->
          Error.failf ~loc "substitution must have even number of arguments"
      in
      match sexp.s with
      | List l -> of_l l
      | Atom _ ->
        Error.failf ~loc:sexp.loc "expected substitution of shape `(<var> <term> …)`"

    let lits_of_sexp s : A.term list =
      let loc = s.loc in
      match s.s with
      | List ({s=Atom "cl";_} :: lits) -> List.map t_of_sexp lits
      | _ -> Error.failf ~loc "expected a clause `(cl t1 t2 … tn)`"

    (** Parse clause *)
    let cl_of_sexp (s:sexp) : A.clause =
      let loc = s.loc in
      match s.s with
      | List [{s=Atom ("@"|"ref");_}; {s=Atom name;_}] ->
        A.Clause.(mk ~loc @@ Clause_ref name)
      | List ({s=Atom "cl";_} :: lits) ->
        let c_lits = List.map t_of_sexp lits in
        A.Clause.(mk ~loc @@ Clause c_lits)
      | _ -> Error.failf ~loc "expected a clause `(cl t1 t2 … tn)` or `(@ <name>)`"

    let asm_of_sexp s =
      let loc = s.loc in
      match s.s with
      | List [{s=Atom name;_}; lit] ->
        let lit = t_of_sexp lit in
        name, lit
      | _ -> Error.failf ~loc "expected an assumption `(<name> <lit>)`"

    (** Parse proof *)
    let rec p_of_sexp (s:sexp) : P.t =
      let loc = s.loc in
      match s.s with
      | List [{s=Atom "steps";_}; {s=List asms;_}; {s=List steps;_}] ->
        let assms = List.map asm_of_sexp asms in
        let steps = List.map step_of_sexp steps in
        P.composite_l ~loc ~assms steps

      | List [{s=Atom "with";_}; {s=List bs;_}; p1] ->
        let bs = List.map (function
            | {s=List [{s=Atom name;_}; t];_} ->
              let t = t_of_sexp t in
              name, t
            | {loc;_} ->
              Error.failf ~loc "expected pair `(<name> <term>)`")
            bs
        in
        let p1 = p_of_sexp p1 in
        P.with_ ~loc bs p1

      | List [{s=Atom "ccl";_}; cl] ->
        let cl = cl_of_sexp cl in
        P.cc_lemma ~loc cl

      | List [{s=Atom "ccli";_}; {s=List prs;_}; t; u] ->
        let t = t_of_sexp t in
        let u = t_of_sexp u in
        let prs = List.map p_of_sexp prs in
        P.cc_imply_l ~loc prs t u

      | List ({s=Atom "bool-c";_} :: {s=Atom name;loc=name_loc} :: ts) ->
        let ts = List.map t_of_sexp ts in
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
          | _ -> Error.failf ~loc:name_loc "unknown bool-c rule: '%s'" name
        ) in
        P.bool_c ~loc name ts

      | List [{s=Atom "clause-rw";_}; cl; p; {s=List using;_}] ->
        let cl = cl_of_sexp cl in
        let p = p_of_sexp p in
        let using = List.map p_of_sexp using in
        P.clause_rw ~loc ~res:cl p ~using

      | List [{s=Atom "rup";_}; cl; {s=List using;_}] ->
        let cl = cl_of_sexp cl in
        let using = List.map p_of_sexp using in
        P.rup_res ~loc cl using

      | List [{s=Atom "p1";_}; rw_with; p] ->
        let rw_with = p_of_sexp rw_with in
        let p = p_of_sexp p in
        P.paramod1 ~loc ~rw_with p

      | Atom "t-ne-f" -> P.true_neq_false ~loc
      | Atom "t-is-t" -> P.true_is_true ~loc

      | List [{s=Atom "ite-true";_}; t] ->
        let t = t_of_sexp t in
        P.ite_true ~loc t
      | List [{s=Atom "ite-false";_}; t] ->
        let t = t_of_sexp t in
        P.ite_false ~loc t

      | List [{s=Atom "r";_}; pivot; p1; p2] ->
        let pivot = t_of_sexp pivot in
        let p1 = p_of_sexp p1 in
        let p2 = p_of_sexp p2 in
        P.res ~loc ~pivot p1 p2

      | List [{s=Atom "r1";_}; p1; p2] ->
        let p1 = p_of_sexp p1 in
        let p2 = p_of_sexp p2 in
        P.res1 ~loc p1 p2

      | List [{s=Atom "hres";_}; init; {s=List steps;_}] ->
        let pstep s =
          let loc = s.loc in
          match s.s with
          | List [{s=Atom "p1";_}; sub_p] -> P.p1 ~loc (p_of_sexp sub_p)
          | List [{s=Atom "p";_}; lhs; rhs; sub_p] ->
            let lhs = t_of_sexp lhs in
            let rhs = t_of_sexp rhs in
            let sub_p = p_of_sexp sub_p in
            P.p ~loc sub_p ~lhs ~rhs
          | List [{s=Atom "r1";_}; sub_p] -> P.r1 ~loc (p_of_sexp sub_p)
          | List [{s=Atom "r";_}; pivot; sub_p] ->
            let pivot = t_of_sexp pivot in
            let sub_p = p_of_sexp sub_p in
            P.r ~loc ~pivot sub_p
          | _ ->
            Error.failf ~loc "expected a step for `hres` (hint: p1|r1|p|r)"
        in
        let init = p_of_sexp init in
        P.hres_l ~loc init (CCList.map pstep steps)

      | List [{s=Atom "subst";_}; subst; p] ->
        let subst = s_of_sexp subst in
        let p = p_of_sexp p in
        P.subst ~loc subst p

      | List [{s=Atom "assert";_}; t] ->
        P.assertion ~loc (t_of_sexp t)

      | List [{s=Atom "assert-c";_}; c] ->
        P.assertion_c ~loc (cl_of_sexp c)

      | List [{s=Atom "refl";_}; t] ->
        P.refl ~loc (t_of_sexp t)

      | List [{s=Atom ("@" | "ref");_}; {s=Atom name;_}] ->
        P.ref_by_name ~loc name

      | _ -> Error.failf ~loc "expected a proof"

    (** Parse a composite step *)
    and step_of_sexp (s:sexp) : _ P.composite_step =
      let loc = s.loc in
      match s.s with
      | List [{s=Atom "deft";_}; {s=Atom name;loc=_}; t] ->
        let t = t_of_sexp t in
        P.deft name ~loc t
      | List [{s=Atom "stepc";_}; {s=Atom name;_}; cl; sub_pr] ->
        let cl = lits_of_sexp cl in
        let sub_pr = p_of_sexp sub_pr in
        P.stepc ~loc ~name cl sub_pr
      | List [{s=Atom "ty_decl";_}; {s=Atom name;loc=_}; {s=Atom n;loc=loc_n}] ->
        let n = try int_of_string n
          with _ -> Error.failf ~loc:loc_n "expect arity (a number)" in
        P.decl_ty_const ~loc name n
      | List [{s=Atom "decl";_}; {s=Atom name;loc=_}; ty] ->
        let ty = ty_of_sexp ty in
        P.decl_const ~loc name ty
      | List [{s=Atom "def";_}; {s=Atom name;loc=_}; ty; rhs] ->
        let ty = ty_of_sexp ty in
        let rhs = t_of_sexp rhs in
        P.define_const ~loc name ty rhs
      | _ -> Error.failf ~loc "expected a composite step (`deft` or `stepc`)"

    let parse_sexp_l_ (l:sexp list) : P.t =
      match l with
      | [{s=List [{s=Atom "quip";_}; {s=Atom "1";_}; bod];_}] -> p_of_sexp bod
      | {s=List [{s=Atom "quip";loc=loc1}; {s=Atom "1";_}];_} :: steps ->
        let loc = Loc.union_l (loc1 :: List.rev_map (fun s->s.loc) steps)
                  |> CCOpt.get_or ~default:loc1
        in
        let steps = List.map step_of_sexp steps in
        P.composite_l ~loc ~assms:[] steps
      | s1 :: _ -> Error.failf ~loc:s1.loc "expected `(quip 1 <proof>)` or `(quip 1) <steps>"
      | [] -> Error.failf ~loc:Loc.none "expected `(quip 1 <proof>)` or `(quip 1) <steps>"

    let parse_top lexbuf : P.t =
      let dec = Decoder.of_lexbuf lexbuf in
      match Decoder.to_list dec with
      | Ok l -> parse_sexp_l_ l
      | Error e -> Error.failf ~loc:Loc.none "expected proof (list of S-expressions), but:@ %s" e
  end

  let parse_lexbuf_ ~input ~filename lexbuf : P.t =
    Profile.with_ "parse-proof" @@ fun () ->
    let module P = Parse(struct
        let filename=filename
        let input = input
      end) () in
    Loc.set_file lexbuf filename;
    P.parse_top lexbuf

  let parse_string ?(filename="<string>") (s:string) : P.t =
    let lexbuf = Lexing.from_string s in
    let input = Loc.Input.string s in
    parse_lexbuf_ ~input ~filename lexbuf

  let parse_chan ?(filename="<channel>") ~input (ic:in_channel) : P.t =
    let lexbuf = Lexing.from_channel ic in
    parse_lexbuf_ ~filename ~input lexbuf

  let parse_file filename =
    CCIO.with_in filename @@ fun ic ->
    let input = Loc.Input.file filename in
    parse_chan ~filename ~input ic
end

