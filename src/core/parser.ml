
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

