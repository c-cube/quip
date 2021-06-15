
open Common

module A = Ast

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

    | List [{s=Atom "ccl";_}; cl] ->
      let cl = cl_of_sexp cl in
      P.cc_lemma cl

    | List [{s=Atom "ccli";_}; {s=List prs;_}; t; u] ->
      let t = t_of_sexp t in
      let u = t_of_sexp u in
      let prs = List.map p_of_sexp prs in
      P.cc_imply_l prs t u

    | List [{s=Atom "nn";_}; p] ->
      let p = p_of_sexp p in
      P.nn p

    | List ({s=Atom "bool-c";_} :: ({s=Atom name;_} as s_name) :: ts) ->
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
        | _ -> parse_errorf s_name "unknown bool-c rule: '%s'" name
      ) in
      P.bool_c name ts

    | Atom "t-ne-f" -> P.true_neq_false
    | Atom "t-is-t" -> P.true_is_true

    | List [{s=Atom "r";_}; pivot; p1; p2] ->
      let pivot = t_of_sexp pivot in
      let p1 = p_of_sexp p1 in
      let p2 = p_of_sexp p2 in
      P.res ~pivot p1 p2

    | List [{s=Atom "r1";_}; p1; p2] ->
      let p1 = p_of_sexp p1 in
      let p2 = p_of_sexp p2 in
      P.res1 p1 p2

    | List [{s=Atom "hres";_}; init; {s=List steps;_}] ->
      let pstep s = match s.s with
        | List [{s=Atom "p1";_}; sub_p] -> P.p1 (p_of_sexp sub_p)
        | List [{s=Atom "p";_}; lhs; rhs; sub_p] ->
          let lhs = t_of_sexp lhs in
          let rhs = t_of_sexp rhs in
          let sub_p = p_of_sexp sub_p in
          P.p sub_p ~lhs ~rhs
        | List [{s=Atom "r1";_}; sub_p] -> P.r1 (p_of_sexp sub_p)
        | List [{s=Atom "r";_}; pivot; sub_p] ->
          let pivot = t_of_sexp pivot in
          let sub_p = p_of_sexp sub_p in
          P.r ~pivot sub_p
        | _ ->
          parse_errorf s "expected a step for `hres` (hint: p1|r1|p|r)"
      in
      let init = p_of_sexp init in
      P.hres_l init (CCList.map pstep steps)

    | List [{s=Atom "assert";_}; t] ->
      P.assertion (t_of_sexp t)

    | List [{s=Atom "assert-c";_}; c] ->
      P.assertion_c (cl_of_sexp c)

    | List [{s=Atom "refl";_}; t] ->
      P.refl (t_of_sexp t)

    | List [{s=Atom ("@" | "ref");_}; {s=Atom name;_}] ->
      P.ref_by_name name

    | _ -> parse_errorf s "expected a proof"

  and step_of_sexp (s:sexp) : P.composite_step =
    match s.s with
    | List [{s=Atom "deft";_}; {s=Atom name;loc=_}; t] ->
      let t = t_of_sexp t in
      P.deft name t
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

