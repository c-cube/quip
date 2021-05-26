
open Common
module K = Trustee_core.Kernel
module E = K.Expr
module Ast = Quip_core.Ast
module Parsed_pb = Quip_core.Parsed_pb

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Proof checker" "quip.check"))


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

  let unwrap_or_ msg = function
    | Some x -> x
    | None -> error msg

  (** {2 Some constants} *)
  module Cst = struct
    let find_ name builtin =
      let c =
        Problem.find_builtin builtin
        |> unwrap_or_ ("cannot find builtin " ^ name)
      in
      K.Expr.const ctx c []

    let false_ : K.expr = find_ "false" Quip_core.Builtin.False
    let not_ : K.expr = find_ "not" Quip_core.Builtin.Not
    let bool = E.bool ctx
  end

  (** {2 Literal} *)
  module Lit : sig
    type t [@@deriving show]
    val neg : t -> t
    val to_expr : t -> E.t
    val make : ?sign:bool -> E.t -> t
  end = struct
    type t = {
      sign: bool;
      expr: K.expr;
    }

    let pp out (self:t) =
      let s = if self.sign then "+" else "-" in
      Fmt.fprintf out "(@[%s@ %a@])" s K.Expr.pp self.expr
    let show = Fmt.to_string pp

    let make ?(sign=true) expr = {sign;expr}
    let[@inline] neg (self:t) : t = {self with sign=not self.sign}

    let to_expr (self:t) : K.expr =
      if self.sign then self.expr
      else E.app ctx Cst.not_ self.expr
  end

  (** {2 Direct form clause} *)
  module Clause : sig
    type t [@@deriving show]
    val empty : t
    val make : Lit.t list -> t
    val lits : t -> Lit.t list
  end = struct
    type t = Lit.t list
    let pp out self = Fmt.fprintf out "(@[cl@ %a@])" (Fmt.list Lit.pp) self
    let show = Fmt.to_string pp
    let empty = []
    let make x = x
    let lits x = x
  end

  (* turn [not e] into [Some e], any other term into [None] *)
  let open_not_ (e:E.t) : E.t option =
    match E.view e with
    | E.E_app (f, u) when E.equal f Cst.not_ -> Some u
    | _ -> None

  (** {2 Negated form clause}

      We represent a clause [a1 \/ … \/ an] by the theorem
      [¬a1, …, ¬an |- false]
  *)
  module N_clause : sig
    type t [@@deriving show]
    val equal : t -> t -> bool
    val equal_to_clause : t -> Clause.t -> bool
    val of_thm: K.thm -> t
    val of_clause_axiom : Clause.t -> t
  end = struct
    type t = {
      as_th: K.thm [@printer K.Thm.pp_quoted];
    }

    let pp out (self:t) =
      Fmt.fprintf out "(@[n-clause@ %a@])" K.Thm.pp_quoted self.as_th
    let show = Fmt.to_string pp

    let equal (a:t) (b:t): bool =
      CCList.equal E.equal
        (K.Thm.hyps_sorted_l a.as_th)
        (K.Thm.hyps_sorted_l b.as_th)

    let equal_to_clause (self:t) (c:Clause.t) : bool =
      let c_lits =
        Clause.lits c
        |> List.rev_map (fun l -> Lit.to_expr @@ Lit.neg l)
        |> CCList.sort_uniq ~cmp:E.compare
      in
      CCList.equal E.equal
        (K.Thm.hyps_sorted_l self.as_th)
        c_lits

    (* axiom: [¬a, a |- false] *)
    let _var_a = K.Var.make "a" Cst.bool
    let ax_prove_false =
      K.Thm.axiom ctx
        [ E.var ctx _var_a;
          E.app ctx Cst.not_ (E.var ctx _var_a);
        ]
        Cst.false_

    (* move conclusion to the left, to get a negated clause *)
    let of_thm (th:K.thm) : t =
      Log.debug (fun k->k"clausify-thm %a" K.Thm.pp_quoted th);
      let concl = K.Thm.concl th in
      let th =
        if E.equal concl Cst.false_ then th
        else (
          match open_not_ concl with
          | None ->
            (* C1: G |- a
               C2: a, ¬a |- false (ax)
               C3: G, ¬a |- false (cut C1 C2) *)
            let ax_false =
              K.Thm.subst ~recursive:false ctx ax_prove_false
                (K.Subst.of_list [_var_a, concl]) in
            K.Thm.cut ctx th ax_false
          | Some u ->
            (* C1: G |- ¬a
               C2: a, ¬a |- false (ax)
               C3: G, a |- false (cut C1 C2) *)
            let ax_false =
              K.Thm.subst ~recursive:false ctx ax_prove_false
                (K.Subst.of_list [_var_a, u]) in
            K.Thm.cut ctx th ax_false
        )
      in
      {as_th=th}

    (* convert [c] into a negated clause, using an axiom. *)
    let of_clause_axiom (c:Clause.t) : t =
      let c_lits =
        Clause.lits c
        |> List.rev_map (fun l -> Lit.to_expr @@ Lit.neg l)
        |> CCList.sort_uniq ~cmp:E.compare
      in
      {as_th=K.Thm.axiom ctx c_lits Cst.false_}
  end

  type st = {
    checked: (string, N_clause.t) Hashtbl.t;
    named_terms: (string, K.expr) Hashtbl.t;
    mutable all_ok: bool;
  }

  let st : st = {
    checked = Hashtbl.create 32;
    named_terms = Hashtbl.create 32;
    all_ok = true;
  }

  (* TODO: a bunch of axioms for translation *)

  let rec conv_term (t: Ast.term) : K.expr =
    let module T = Ast.Term in
    begin match T.view t with
      | T.App (f, l) ->
        let l = List.map conv_term l in
        begin match T.view f, l with
          | T.Var {name="=";_}, [a;b] ->
            (* special case so we handle the polymorphism directly *)
            K.Expr.app_l ctx (K.Expr.eq ctx (K.Expr.ty_exn a)) [a; b]
          | _ ->
            let f = conv_term f in
            K.Expr.app_l ctx f l
        end
      | T.Var v ->
        begin match Hashtbl.find_opt st.named_terms v.name with
          | Some u -> u
          | None ->
            begin match Problem.find_const_by_name v.name with
              | Some c -> K.Expr.const ctx c []
              | None ->
                errorf(fun k->k"cannot convert unknown term@ `%a`" T.pp t)
            end
        end
      | _ ->
        (* TODO *)
        errorf (fun k->k"todo: conv term `%a`" T.pp t)
    end

  (* the empty clause, as an axiom (!) *)
  let empty_clause_ax : N_clause.t =
    let (module PB) = problem in
    (* TODO: find another way of doing that, or just remove "sorry" *)
    N_clause.of_clause_axiom Clause.empty

  let conv_clause (c: Ast.clause) : Clause.t =
    Log.debug (fun k->k"conv-clause %a" Ast.Clause.pp c);
    let lits =
      List.rev_map
        (fun {Ast.Lit.sign;atom} -> Lit.make ~sign (conv_term atom))
        c
    in
    Clause.make lits

  module P = Ast.Proof

  let rec check_step (_self:t) (step: Ast.Proof.composite_step) : unit =
    Log.debug (fun k->k"checking step %a" Ast.Proof.pp_composite_step step);
    assert false (* TODO *)

  (* check proof [p], returns the clause it returns *)
  and check_proof_rec_ (p: Ast.Proof.t) : N_clause.t =
    Log.debug (fun k->k"(@[check-proof-rec@ %a@])" P.pp p);
    begin match P.view p with
      | P.Sorry ->
        (* return `|- false` by default, we do not know what else to return *)
        Log.warn (fun k->k"met a sorry step");
        st.all_ok <- false;
        empty_clause_ax (* yikes *)

      | P.Sorry_c c ->
        st.all_ok <- false;
        conv_clause c |> N_clause.of_clause_axiom

      | P.Refl t ->
        let t = conv_term t in
        N_clause.of_thm (K.Thm.refl ctx t)

      | P.Assert t ->
        (* TODO: lookup in problem? *)
        (* TODO: use theory mechanism to track asserts *)

        (* assume: [¬t \/ t] *)
        let t = conv_term t in
        N_clause.of_thm (K.Thm.axiom ctx [] t)

      | P.Composite {assumptions; steps} ->
        (* composite proof: check each step *)

        (* TODO: put assumptions in names *)

        let r =
          Array.fold_left
            (fun prev step ->
               match check_composite_step_ step with
               | Some c -> Some c
               | None -> prev)
            None steps
        in
        begin match r with
          | None -> errorf (fun k->k"composite proof returns no clause")
          | Some c -> c
        end

      | P.Named name ->
        begin match Hashtbl.find_opt st.checked name with
          | Some c -> c
          | None ->
            errorf (fun k->k"cannot find step with name '%s'" name)
        end

      | P.Assert_c _
        (* TODO: lookup in problem? *)

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

  and check_composite_step_ (step: Ast.Proof.composite_step) : N_clause.t option =
   begin match step with
    | P.S_define_t (name, u) ->
      let u = conv_term u in
      Hashtbl.add st.named_terms name u;
      None

    | P.S_step_c { name; res; proof } ->

      let c = check_proof_rec_ proof in
      Hashtbl.add st.checked name c;

      let expected_res = conv_clause res in

      if not (N_clause.equal_to_clause c expected_res) then (
        Log.err (fun k->k"step '%s'@ should yield %a@ but proof returns %a"
                    name Clause.pp expected_res N_clause.pp c);
        st.all_ok <- false;
      );

      Some c
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
