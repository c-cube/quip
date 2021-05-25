
open Common
module K = Trustee_core.Kernel
module E = K.Expr
module Ast = Quip_core.Ast
module Parsed_pb = Quip_core.Parsed_pb

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Proof checker" "quip.check"))

(** {2 Negated form clause}

    We represent a clause [a1 \/ … \/ an] by the theorem
    [¬a1, …, ¬an |- false]
*)
type n_clause = {
  as_th: K.thm [@printer K.Thm.pp_quoted];
} [@@deriving show]

module type S = sig
  val check_proof : Ast.Proof.t -> bool
end

type t = (module S)

module type ARG = sig
  val ctx : K.ctx
  val problem : Parsed_pb.t
end

module Make(A : ARG) : S = struct
  open A
  module Problem = (val A.problem)

  type st = {
    checked: (string, n_clause) Hashtbl.t;
    named_terms: (string, K.expr) Hashtbl.t;
    mutable all_ok: bool;
  }

  let st : st = {
    checked = Hashtbl.create 32;
    named_terms = Hashtbl.create 32;
    all_ok = true;
  }

  let unwrap_or_ msg = function
    | Some x -> x
    | None -> error msg

  (* TODO: a bunch of axioms for translation *)

  let rec conv_term (t: Ast.term) : K.expr =
    let module T = Ast.Term in
    begin match T.view t with
      | T.App (f, l) ->
        let f = conv_term f in
        let l = List.map conv_term l in
        K.Expr.app_l ctx f l
      | _ ->
        (* TODO *)
        errorf (fun k->k"todo: conv term %a" T.pp t)
    end

  let false_ : K.expr =
    let c =
      Problem.find_builtin Quip_core.Builtin.False
      |> unwrap_or_ "cannot find `false`" in
    K.Expr.const ctx c []

  let clausify_thm_ (th:K.thm) : n_clause =
    Log.debug (fun k->k"clausify-thm %a" K.Thm.pp_quoted th);
    {as_th=th} (* TODO *)

  (* the empty clause, as an axiom (!) *)
  let empty_clause_ax : n_clause =
    let (module PB) = problem in
    {as_th=K.Thm.axiom ctx false_}

  let conv_clause (c: Ast.clause) : n_clause =
    assert false (* TODO *)

  let rec check_step (_self:t) (step: Ast.Proof.composite_step) : unit =
    Log.debug (fun k->k"checking step %a" Ast.Proof.pp_composite_step step);
    assert false (* TODO *)

  (* check proof [p], returns the clause it returns *)
  and check_proof_rec_ (p: Ast.Proof.t) : n_clause =
    let module P = Ast.Proof in
    Log.debug (fun k->k"(@[check-proof-rec@ %a@])" P.pp p);
    begin match P.view p with
      | P.Sorry ->
        (* return `|- false` by default, we do not know what else to return *)
        Log.warn (fun k->k"met a sorry step");
        st.all_ok <- false;
        empty_clause_ax (* yikes *)

      | P.Sorry_c c ->
        st.all_ok <- false;
        conv_clause c

      | P.Refl t ->
        let t = conv_term t in
        clausify_thm_ (K.Thm.refl ctx t)

      | P.Assert t ->
        (* TODO: lookup in problem? *)
        (* assume: [¬t \/ t] *)
        let t = conv_term t in
        clausify_thm_ (K.Thm.assume ctx t)

      | P.Composite {assumptions; steps} ->
        (* composite proof: check each step *)
        assert false (* TODO *)

      | P.Assert_c _
        (* TODO: lookup in problem? *)

      | P.Named _
      | P.CC_lemma_imply (_, _, _)
      | P.CC_lemma _
      | P.Hres (_, _)
      | P.DT_isa_split (_, _)
      | P.DT_isa_disj (_, _, _)
      | P.DT_cstor_inj (_, _, _, _)
      | P.Bool_true_is_true
      | P.Bool_true_neq_false
      | P.Bool_eq (_, _)
      | P.Bool_c _
      | P.Ite_true _
      | P.Ite_false _
      | P.LRA _
        ->
        Log.warn (fun k->k"unimplemented: checking %a" P.pp p);
        st.all_ok <- false;
        empty_clause_ax (* TODO *)
    end

  let check_proof p =
    Log.debug (fun k->k"checking proof");
    let _c = check_proof_rec_ p in
    (* TODO: should it return the empty clause? *)
    st.all_ok
end

let create ctx pb : t =
  let module M = Make(struct let ctx=ctx let problem=pb end) in
  (module M)

let check_proof (self: t) (p: Ast.Proof.t) : bool =
  let (module Self) = self in
  Self.check_proof p
