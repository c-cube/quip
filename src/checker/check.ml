
open Common
module K = Trustee_core.Kernel
module E = K.Expr
module Ast = Quip_core.Ast
module Parsed_pb = Quip_core.Parsed_pb

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Proof checker" "quip.check"))

type stats = {
  n_valid: int;
  n_invalid: int;
  n_steps: int;
} [@@deriving show {with_path=false}]

module type S = sig
  val check_proof : Ast.Proof.t -> bool * stats
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
    val sign : t -> bool
    val atom : t -> E.t
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

    let[@inline] sign self = self.sign
    let[@inline] atom self = self.expr
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
  let unfold_not_ (e:E.t) : E.t option =
    match E.view e with
    | E.E_app (f, u) when E.equal f Cst.not_ -> Some u
    | _ -> None

  let is_not_ e = CCOpt.is_some (unfold_not_ e)

  (** {2 Negated form clause}

      We represent a clause [a1 \/ … \/ an] by the theorem
      [¬a1, …, ¬an |- false]
  *)
  module N_clause : sig
    type t [@@deriving show]

    val equal : t -> t -> bool

    val equal_to_clause : t -> Clause.t -> bool

    val as_th : t -> K.thm
    (** [as_th c] returns a theorem of the shape [l1, …, ln |- false] *)

    val of_thm: K.thm -> t
    (** Turn the theorem into one with [|- false] as conclusion *)

    val of_clause_axiom : Clause.t -> t
    (** Make an axiom of this clause, in the negative form. *)

    val iter_lits : t -> E.t Iter.t
    (** Iterate on literals. Remember that the literals are negated wrt.
        the actual clause this represents. *)

    val find_lit_by_term : t -> E.t -> (bool * E.t) option
    (** [find_lit_by_term c t] finds the literal in [c] with given atom,
        along with the sign of this literal wrt [t].
        The sign is [true] iff [t] and the literal are the same. *)

    val find_uniq_lit : t -> E.t option
    (** [find_uniq_lit c] returns [Some a] if [c] is the theorem [a |- false],
        otherwise it returns None *)

    val move_lit_to_rhs : t -> E.t -> K.thm
    (** Assuming the clause contains this literal,
        move it to the right to obtain a "normal" theorem *)

    val move_uniq_lit_to_rhs : t -> K.thm
    (** Assuming the clause has only one literal (on the left),
        move it to the right to obtain a "normal" theorem *)
  end = struct
    type t = {
      as_th: K.thm [@printer K.Thm.pp_quoted];
    }

    let pp out (self:t) =
      Fmt.fprintf out "(@[n-clause@ %a@])" K.Thm.pp_quoted self.as_th
    let show = Fmt.to_string pp

    let as_th self = self.as_th
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

    let _var_a = K.Var.make "a" Cst.bool

    (* axiom: [¬a, a |- false] *)
    let ax_prove_false =
      K.Thm.axiom ctx
        [ E.var ctx _var_a;
          E.app ctx Cst.not_ (E.var ctx _var_a);
        ]
        Cst.false_

    (* axiom: [false |- a] *)
    let ax_ex_falso =
      K.Thm.axiom ctx [Cst.false_] (E.var ctx _var_a)

    (* axiom: [|- ¬a = (a=false)] *)
    let ax_not_is_eq_false =
      let a = E.var ctx _var_a in
      let t = E.(app_eq ctx (app ctx Cst.not_ a) (app_eq ctx a Cst.false_)) in
      K.Thm.axiom ctx [] t

    (* axiom: [| ¬¬a = a] *)
    let ax_not_not_ =
      let a = E.var ctx _var_a in
      let t = E.(app_eq ctx (app ctx Cst.not_ (app ctx Cst.not_ a)) a) in
      K.Thm.axiom ctx [] t

    (* move conclusion to the left, to get a negated clause *)
    let of_thm (th:K.thm) : t =
      Log.debug (fun k->k"clausify-thm %a" K.Thm.pp_quoted th);
      let concl = K.Thm.concl th in
      let th =
        if E.equal concl Cst.false_ then th
        else (
          (* C1: G |- a
             C2: a, ¬a |- false (ax)
             C3: G, ¬a |- false (cut C1 C2) *)
          let ax_false =
            K.Thm.subst ~recursive:false ctx ax_prove_false
              (K.Subst.of_list [_var_a, concl]) in
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

    let iter_lits (self:t) : _ Iter.t =
      K.Thm.hyps_iter self.as_th

    (* goes from [G, ¬a |- false] to [G |- a].

       C1: G, ¬a |- false
       C2: false |- ¬a
       C3: G |- ¬a=false (bool-eq-intro C1 C2)
       C4: |- ¬¬a = (¬a=false) (ax subst with ¬a)
       C5: |- (¬a=false) = ¬¬a (sym C4)
       C6: G |- ¬¬a (bool-eq C3 C5)
       C7: |- ¬¬a = a (ax)
       C8: G |- a (bool-eq C6 C7)
    *)
    let move_lit_to_rhs (self:t) (e:E.t) : K.thm =
      let a = match unfold_not_ e with
        | Some a -> a
        | None -> errorf (fun k->k"move_lit_to_rhs: expect a negation,@ got %a" E.pp e)
      in
      assert (iter_lits self |> Iter.exists (E.equal e));
      let th2 =
        K.Thm.subst ~recursive:false ctx ax_ex_falso
          (K.Subst.of_list [_var_a, e])
      in
      let th3 = K.Thm.bool_eq_intro ctx th2 self.as_th in
      let th5 =
        K.Thm.subst ~recursive:false ctx ax_not_is_eq_false
          (K.Subst.of_list [_var_a, e])
        |> K.Thm.sym ctx
      in
      let th6 = K.Thm.bool_eq ctx th3 th5 in
      let th7 =
        K.Thm.subst ctx ~recursive:false ax_not_not_
          (K.Subst.of_list [_var_a, a]) in
      let th8 = K.Thm.bool_eq ctx th6 th7 in
      th8

    let find_lit_by_term (self:t) (t: E.t) : (bool * E.t) option =
      K.Thm.hyps_iter self.as_th
      |> Iter.find_map
        (fun e ->
           if E.equal t e then Some (true, e)
           else (
             match unfold_not_ e with
             | Some u when E.equal t u -> Some (false, e)
             | _ -> None
           ))

    let find_uniq_lit self : _ option =
      match K.Thm.hyps_l self.as_th with
      | [e] -> Some e
      | _ -> None

    let move_uniq_lit_to_rhs (self:t) : K.thm =
      match K.Thm.hyps_l self.as_th with
      | [e] -> move_lit_to_rhs self e
      | _ ->
        errorf
          (fun k->k"n-clause.move_lit_to_rhs:@ expected single literal in %a" pp self)
  end

  type st = {
    checked: (string, N_clause.t) Hashtbl.t;
    named_terms: (string, K.expr) Hashtbl.t;
    mutable n_valid: int;
    mutable n_invalid: int;
    mutable n_steps: int;
  }

  let st : st = {
    checked = Hashtbl.create 32;
    named_terms = Hashtbl.create 32;
    n_valid=0; n_invalid=0; n_steps=0;
  }

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

  (* check [p], returns its resulting clause.
     In case of error this returns the empty clause. *)
  and check_proof_or_empty_ p : N_clause.t =
    st.n_steps <- 1 + st.n_steps;
    try
      let ok, c = check_proof_rec_exn p in
      if ok then (
        st.n_valid <- 1 + st.n_valid;
      ) else (
        st.n_invalid <- 1 + st.n_invalid;
      );
      c
    with
    | Error e ->
      Log.err (fun k->k"proof failed with %s" e);
      st.n_invalid <- 1 + st.n_invalid;
      empty_clause_ax
    | Trustee_error.E e ->
      Log.err (fun k->k"proof failed with %a" Trustee_error.pp e);
      st.n_invalid <- 1 + st.n_invalid;
      empty_clause_ax

  (* check proof [p], returns the clause it returns *)
  and check_proof_rec_exn (p: Ast.Proof.t) : bool * N_clause.t =
    Log.debug (fun k->k"(@[check-proof-rec@ %a@])" P.pp p);
    begin match P.view p with
      | P.Sorry ->
        (* return `|- false` by default, we do not know what else to return *)
        false, empty_clause_ax

      | P.Sorry_c c ->
        false, conv_clause c |> N_clause.of_clause_axiom

      | P.Refl t ->
        let t = conv_term t in
        true, N_clause.of_thm (K.Thm.refl ctx t)

      | P.Assert t ->
        Log.warn (fun k->k"TODO: find assert in assumptions");
        (* FIXME: lookup in problem? *)
        (* TODO: use theory mechanism to track asserts *)

        (* assume: [¬t \/ t] *)
        let t = conv_term t in
        true, N_clause.of_thm (K.Thm.axiom ctx [] t)

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
          | Some c -> true, c
        end

      | P.Named name ->
        begin match Hashtbl.find_opt st.checked name with
          | Some c -> true, c
          | None ->
            errorf (fun k->k"cannot find step with name '%s'" name)
        end

      | P.CC_lemma_imply (ps, t, u) ->
        (* prove [ps |- t=u] *)
        let t = conv_term t in
        let u = conv_term u in

        (* check sub-proofs, and turn them into positive equations *)
        let ps =
          ps
          |> List.rev_map check_proof_or_empty_
          |> List.rev_map N_clause.move_uniq_lit_to_rhs
        in

        let module CC = Trustee_core.Congruence_closure in
        begin match CC.prove_cc ctx ps t u with
          | None ->
            errorf (fun k->k"failed to prove CC-lemma@ %a" P.pp p)
          | Some thm ->
            true, N_clause.of_thm thm
        end

      | P.CC_lemma c ->
        let c = conv_clause c in

        let pos, negs = List.partition Lit.sign (Clause.lits c) in
        begin match pos with
          | [l1] ->
            let t, u = match E.unfold_eq (Lit.to_expr l1) with
              | Some p -> p
              | None ->
                errorf (fun k->k"cc-lemma: positive literal must be an equation")
            in

            let ps = List.map (fun l -> K.Thm.assume ctx (Lit.atom l)) negs in

            (* prove [negs |- t=u] *)
            Log.debug
              (fun k->k"cc-lemma@ :ps %a@ :t %a@ :u %a"
                      (Fmt.Dump.list K.Thm.pp_quoted) ps E.pp t E.pp u);

            let module CC = Trustee_core.Congruence_closure in
            begin match CC.prove_cc ctx ps t u with
              | None ->
                errorf (fun k->k"failed to prove CC-lemma@ %a" P.pp p)
              | Some thm ->
                true, N_clause.of_thm thm
            end
          | _ ->
            errorf
              (fun k->k"cc-lemma: expected exactly one positive literal@ in %a" P.pp p)
          end

      | P.Hres (init, steps) ->

        let init = check_proof_or_empty_ init in
        let c = List.fold_left check_hres_step_ init steps in
        true, c

      | P.Assert_c _
        (* TODO: lookup in problem? *)

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
        false, empty_clause_ax (* TODO *)
    end

  and check_hres_step_ (c1: N_clause.t) (step:P.hres_step) : N_clause.t =

    (* do resolution between [c1] and [c2] *)
    let res_on_ ~pivot c2 =
      Log.debug (fun k->k "(@[resolve@ :c1 %a@ :c2 %a@ :pivot %a@])"
                    N_clause.pp c1 N_clause.pp c2 E.pp pivot);
      (* find the polarity of [pivot] in [c1] *)
      match N_clause.find_lit_by_term c1 pivot with
      | Some (false, lit) ->
        (* C1: G1, ¬lit |- false
           C2: G2, lit |- false
           C3: G1 |- lit (from C1)
           C4: G1, G2 |- false (res C2 C3) *)
        let th3 = N_clause.move_lit_to_rhs c1 lit in
        let th = K.Thm.cut ctx th3 (N_clause.as_th c2) in
        N_clause.of_thm th

      | Some (true, lit) ->
        (* C1: G1, lit |- false
           C2: G2, ¬lit |- false
           C3: G2 |- lit (from C2)
           C4: G1, G2 |- false (res C1 C3) *)
        let th3 = N_clause.move_lit_to_rhs c2 lit in
        let th = K.Thm.cut ctx (N_clause.as_th c1) th3 in
        N_clause.of_thm th

      | None ->
        errorf (fun k->k"cannot resolve %a@ on pivot `%a`" N_clause.pp c1 E.pp pivot)
    in

    (* do bool paramodulation between [c1] and [c2],
       where [c2] must contain [lhs = rhs] and [c1] must contain [lhs] *)
    let bool_param_on_ ~lhs ~rhs c2 =
      Log.debug (fun k->k "(@[bool-param@ :c1 %a@ :c2 %a@ :lhs `%a`@ :rhs `%a`@])"
                    N_clause.pp c1 N_clause.pp c2 E.pp lhs E.pp rhs);
      (* find if [c2] contains [lhs=rhs] or [rhs=lhs] *)
      match
        N_clause.iter_lits c2
        |> Iter.find_map
          (fun e ->
             match unfold_not_ e with
             | None -> None
             | Some e' ->
               match E.unfold_eq e' with
               | Some (t1, t2) when E.equal t1 lhs && E.equal t2 rhs ->
                 Some (e, true)
               | Some (t1, t2) when E.equal t2 lhs && E.equal t1 rhs ->
                 Some (e, false)
               | _ -> None)
      with
      | Some (e, true) ->
        let th1 = N_clause.move_lit_to_rhs c1 (E.app ctx Cst.not_ lhs) in
        let th2 = N_clause.move_lit_to_rhs c2 e in
        let th = K.Thm.bool_eq ctx th1 th2 in
        N_clause.of_thm th

      | Some (e, false) ->
        (* same, but we need to apply symmetry on [c2] after moving
           [rhs = lhs] to the right *)
        let th1 = N_clause.move_lit_to_rhs c1 (E.app ctx Cst.not_ lhs) in
        let th2 = K.Thm.sym ctx @@ N_clause.move_lit_to_rhs c2 e in
        let th = K.Thm.bool_eq ctx th1 th2 in
        N_clause.of_thm th

      | None ->
        errorf (fun k->k"cannot do unit-paramod on %a" N_clause.pp c2)
    in

    begin match step with
      | P.R {pivot; p} ->
        let pivot = conv_term pivot in
        let c2 = check_proof_or_empty_ p in
        res_on_ ~pivot c2

      | P.R1 p ->
        let c2 = check_proof_or_empty_ p in
        let pivot = match N_clause.find_uniq_lit c2 with
          | None -> errorf (fun k->k"r1: clause is not unit@ %a" N_clause.pp c2)
          | Some t -> t
        in
        res_on_ ~pivot c2

      | P.P { lhs; rhs; p } ->
        let lhs = conv_term lhs in
        let rhs = conv_term rhs in
        let c2 = check_proof_or_empty_ p in
        bool_param_on_ ~lhs ~rhs c2

      | P.P1 p ->
        let c2 = check_proof_or_empty_ p in
        let fail() =
          errorf (fun k->k"cannot do p1 on %a" N_clause.pp c2);
        in
        match N_clause.find_uniq_lit c2 with
        | Some e ->
          begin match unfold_not_ e with
            | Some e' ->
              begin match E.unfold_eq e' with
                | Some (lhs, rhs) -> bool_param_on_ ~lhs ~rhs c2
                | None -> fail()
              end
            | None -> fail()
          end
        | None -> fail()
    end

  and check_composite_step_ (step: Ast.Proof.composite_step) : N_clause.t option =
   begin match step with
    | P.S_define_t (name, u) ->
      let u = conv_term u in
      Hashtbl.add st.named_terms name u;
      None

    | P.S_step_c { name; res; proof } ->

      Log.info (fun k->k"check step '%s'" name);
      let c = check_proof_or_empty_ proof in
      Log.debug (fun k->k"step '%s'@ yields %a" name N_clause.pp c);

      let expected_res = conv_clause res in

      let c =
        if N_clause.equal_to_clause c expected_res then c
        else (
          Log.err (fun k->k"step '%s'@ should yield %a@ but proof returns %a"
                      name Clause.pp expected_res N_clause.pp c);
          st.n_invalid <- 1 + st.n_invalid;
          (* use the expected clause instead *)
          N_clause.of_clause_axiom expected_res
        )
      in

      Hashtbl.add st.checked name c;

      Some c
   end

  let check_proof p =
    Log.debug (fun k->k"checking proof");
    let _c = check_proof_or_empty_ p in
    (* TODO: should it return the empty clause? *)
    let ok = st.n_invalid=0 in
    ok, {n_invalid=st.n_invalid; n_valid=st.n_valid; n_steps=st.n_steps}
end

let create ctx pb : t =
  let module M = Make(struct let ctx=ctx let problem=pb end) in
  (module M)

let check_proof (self: t) (p: Ast.Proof.t) : bool * stats =
  let (module Self) = self in
  Self.check_proof p
