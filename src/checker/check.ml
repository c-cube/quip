
open Common
module Ast = Quip_core.Ast
module Env = Quip_core.Env
module CC = Trustee_core.Congruence_closure

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
  val problem : Env.t
end

module Make(A : ARG) : S = struct
  open A
  module Problem = (val A.problem)
  module B = Quip_core.Builtin

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

    let not_ : K.expr = find_ "not" Quip_core.Builtin.Not
  end

  (* always normalize equations so that the order in which they were
     input does not matter *)
  let normalize_expr_ e =
    match E.unfold_eq e with
    | Some (a,b) when E.compare a b < 0 ->
      E.app_eq ctx b a
    | _ -> e

  [@@@ocaml.warning "-32"]

  (** {2 Literal} *)
  module Lit : sig
    type t [@@deriving show, eq, ord]
    val neg : t -> t
    val sign : t -> bool
    val atom : t -> E.t
    val to_expr : t -> E.t
    val as_eqn : t -> (E.t * E.t) option
    val make : bool -> E.t -> t
  end = struct
    type t = {
      sign: bool;
      expr: K.Expr.t;
    } [@@deriving eq, ord]

    let pp out (self:t) =
      let s = if self.sign then "+" else "-" in
      Fmt.fprintf out "(@[%s@ %a@])" s K.Expr.pp self.expr
    let show = Fmt.to_string pp

    let[@inline] sign self = self.sign
    let[@inline] atom self = self.expr
    let[@inline] neg (self:t) : t = {self with sign=not self.sign}

    let[@inline] make sign expr =
      let expr = normalize_expr_ expr in
      {sign;expr}

    let to_expr (self:t) : K.expr =
      if self.sign then self.expr
      else E.app ctx Cst.not_ self.expr

    let as_eqn self : _ option =
      if self.sign then E.unfold_eq self.expr
      else None
  end

  (** {2 Direct form clause} *)
  module Clause : sig
    type t [@@deriving show, eq]
    val empty : t
    val of_list : Lit.t list -> t
    val of_iter : Lit.t Iter.t -> t
    val add : Lit.t -> t -> t
    val singleton : Lit.t -> t
    val remove : Lit.t -> t -> t
    val size : t -> int
    val mem : Lit.t -> t -> bool
    val subset : t -> t -> bool
    val union : t -> t -> t
    val to_iter : t -> Lit.t Iter.t

    val subst : recursive:bool -> t -> K.Subst.t -> t
    val lits : t -> Lit.t Iter.t

    val pos_lits : t -> Lit.t Iter.t
    val neg_lits : t -> Lit.t Iter.t
    val pos_lits_list : t -> Lit.t list
    val neg_lits_list : t -> Lit.t list

    val find_lit_by_term : K.expr -> t -> Lit.t option
    (** [find_lit_by_term e c] finds a literal of [c] with atom [e],
        or [None] *)

    val of_thm : K.thm -> t
    (** Turn a theorem into a (Horn) clause. *)

    val as_singleton : t -> Lit.t option
    (** [as_singleton (singleton lit)] is [Some lit]. For non unary
        clauses it returns [None]. *)

    val uniq_pos_lit : t -> Lit.t option
    (** [uniq_pos_lit c] returns the unique positive literal of [c] if
        [c] contains exactly one positive literal. Otherwise, returns [None] *)

    val uniq_neg_lit : t -> Lit.t option

    val lits_list : t -> Lit.t list
  end = struct
    module ESet = K.Expr.Set
    type t = {
      neg: ESet.t;
      pos: ESet.t;
    } [@@deriving eq, ord]
    let lits self k =
      ESet.iter (fun t -> k (Lit.make false t)) self.neg;
      ESet.iter (fun t -> k (Lit.make true t)) self.pos

    let pp out self =
      Fmt.fprintf out "(@[cl@ %a@])" (Fmt.iter Lit.pp) (lits self)

    let show = Fmt.to_string pp

    let mem x self =
      if Lit.sign x
      then ESet.mem (Lit.atom x) self.pos
      else ESet.mem (Lit.atom x) self.neg

    let empty = {pos=ESet.empty; neg=ESet.empty}
    let mk_ pos neg = {pos; neg}

    let singleton lit =
      if Lit.sign lit
      then mk_ (ESet.singleton (Lit.atom lit)) ESet.empty
      else mk_ ESet.empty (ESet.singleton (Lit.atom lit))

    let size a = ESet.cardinal a.pos + ESet.cardinal a.neg

    let add lit self =
      if Lit.sign lit
      then {self with pos=ESet.add (Lit.atom lit) self.pos}
      else {self with neg=ESet.add (Lit.atom lit) self.neg}

    let add' s x = add x s

    let of_list = List.fold_left add' empty
    let of_iter = Iter.fold add' empty

    let subset c1 c2 = ESet.subset c1.pos c2.pos && ESet.subset c1.neg c2.neg

    let remove lit self =
      if Lit.sign lit
      then {self with pos=ESet.remove (Lit.atom lit) self.pos}
      else {self with neg=ESet.remove (Lit.atom lit) self.neg}

    let lits_list self = lits self |> Iter.to_rev_list

    let union c1 c2 =
      {pos=ESet.union c1.pos c2.pos; neg=ESet.union c1.neg c2.neg}

    let as_singleton_e_ eset = match ESet.choose_opt eset with
      | Some e ->
        if ESet.is_empty (ESet.remove e eset) then Some e else None
      | None -> None

    let as_singleton self =
      match ESet.is_empty self.neg, ESet.is_empty self.pos with
      | true, false ->
        as_singleton_e_ self.pos |> CCOpt.map (Lit.make true)
      | false, true ->
        as_singleton_e_ self.neg |> CCOpt.map (Lit.make false)
      | _ -> None

    let to_iter = lits

    let pos_lits self =
      ESet.to_iter self.pos |> Iter.map (Lit.make true)

    let neg_lits self =
      ESet.to_iter self.neg |> Iter.map (Lit.make false)

    let pos_lits_list self = pos_lits self |> Iter.to_rev_list
    let neg_lits_list self = neg_lits self |> Iter.to_rev_list

    let find_lit_by_term e (self:t) : Lit.t option =
      let e = normalize_expr_ e in
      if ESet.mem e self.pos then Some (Lit.make true e)
      else if ESet.mem e self.neg then Some (Lit.make false e)
      else None

    let uniq_lit_of_sign_ sign self =
      if sign
      then as_singleton_e_ self.pos |> CCOpt.map (Lit.make true)
      else as_singleton_e_ self.neg |> CCOpt.map (Lit.make false)

    let uniq_pos_lit self = uniq_lit_of_sign_ true self
    let uniq_neg_lit self = uniq_lit_of_sign_ false self

    let subst ~recursive self subst : t =
      if K.Subst.is_empty subst then self
      else (
        to_iter self
        |> Iter.map
          (fun lit ->
            let sign = Lit.sign lit in
            let e = E.subst ~recursive ctx (Lit.atom lit) subst in
            Lit.make sign e)
        |> of_iter
      )

    let of_thm th =
      let concl = K.Thm.concl th in
      let c = singleton (Lit.make true concl) in
      Iter.fold
        (fun c t ->
           let lit = Lit.make false t in
           add lit c)
        c
        (K.Thm.hyps_iter th)
  end

  [@@@ocaml.warning "+32"]

  (* if [e] the builtin [b]? *)
  let is_builtin_const_ b (e:E.t) : bool =
    match E.view e with
    | E.E_const (c, _) ->
      begin match Problem.find_builtin b with
        | Some c' -> K.Const.equal c c'
        | None -> false
      end
    | _ -> false

  (* turn [not e] into [Some e], any other term into [None] *)
  let unfold_not_ (e:E.t) : E.t option =
    match E.view e with
    | E.E_app (f, u) when E.equal f Cst.not_ -> Some u
    | _ -> None

  (* find builtin [b] *)
  let get_builtin_ b =
    match Problem.find_builtin b with
    | Some c -> c
    | None -> errorf "cannot find builtin %a" B.pp b

  (* unfold builtin application. *)
  let unfold_builtin b e : _ list option =
    let cb = get_builtin_ b in
    let rec aux e =
      let f, args = E.unfold_app e in
      match E.view f with
      | E.E_const (c, _) when K.Const.equal c cb ->
        if B.is_assoc b then (
          let args' =
            List.fold_left (fun acc e' ->
                match aux e' with
                | Some args -> List.rev_append args acc
                | None -> e' :: acc)
              [] args
          in
          Some args'
        ) else (
          Some args
        )
      | _ -> None
    in
    aux e

  type st = {
    checked: (string, Clause.t) Hashtbl.t;
    named_terms: (string, K.expr) Hashtbl.t;
    named_clauses: (string, Clause.t) Hashtbl.t;
    mutable n_valid: int;
    mutable n_invalid: int;
    mutable n_steps: int;
    dummy_e: K.expr;
  }

  let st : st =
    let _c = K.Expr.new_ty_const ctx " <dummy>" 0 in
    {
      checked = Hashtbl.create 32;
      named_terms = Hashtbl.create 16;
      named_clauses = Hashtbl.create 16;
      n_valid=0; n_invalid=0; n_steps=0;
      dummy_e = K.Expr.const ctx _c [];
    }

  let rec conv_ty (ty: Ast.ty) : K.ty =
    match ty with
    | Ast.Ty.Arrow (args, ret) ->
      let args = List.map conv_ty args in
      let ret = conv_ty ret in
      E.arrow_l ctx args ret
    | Ast.Ty.Constr (s, args) ->
      (* FIXME: type variables *)
      begin match Problem.find_ty_const_by_name s with
        | None ->
          errorf "cannot convert unknown type constant `%s`" s
        | Some c ->
          let args = List.map conv_ty args in
          E.const ctx c args
      end

  let rec conv_term (t: Ast.term) : K.expr =
    let module T = Ast.Term in
    (* Log.debug (fun k->k"(@[conv-t %a@])" T.pp t); *)
    begin match T.view t with
      | T.App (f, l) ->
        let l = List.map conv_term l in
        begin match T.view f, l with
          | T.Var {name="=";_}, [a;b] ->
            (* special case so we handle the polymorphism directly *)
            K.Expr.app_l ctx (K.Expr.eq ctx (K.Expr.ty_exn a)) [a; b]
          | T.Var {name;_}, l ->
            begin match Problem.find_const_by_name name, l with
              | Some (c, Some b), e1 :: tl
                when Quip_core.Builtin.is_assoc b ->
                (* associative operator *)
                List.fold_left
                  (fun e1 e2 -> K.Expr.app_l ctx (K.Expr.const ctx c []) [e1;e2])
                  e1 tl

              | _ ->
               let f = conv_term f in
               K.Expr.app_l ctx f l
            end
          | _ ->
            let f = conv_term f in
            K.Expr.app_l ctx f l
        end
      | T.Var v ->
        begin match Hashtbl.find_opt st.named_terms v.name with
          | Some u -> u
          | None ->
            begin match Problem.find_const_by_name v.name with
              | Some (c,_) -> K.Expr.const ctx c []
              | None ->
                begin match v.ty with
                  | Some ty ->
                    let ty = conv_ty ty in
                    E.var_name ctx v.name ty
                  | None ->
                    errorf"cannot convert unknown identifier@ `%a`" T.pp t
                end
            end
        end
      | T.Ite (a,b,c) ->
        let ite = get_builtin_ B.If in
        let a = conv_term a in
        let b = conv_term b in
        let c = conv_term c in
        E.app_l ctx (E.const ctx ite [E.ty_exn b]) [a;b;c]

      | T.Ref name ->
        begin match Hashtbl.find_opt st.named_terms name with
          | Some u -> u
          | None ->
            errorf "reference to unknown term %S" name
        end

      | T.Fun _ ->
        errorf "todo: conv lambda term `%a`" T.pp t
      | T.Let _ ->
        errorf "todo: conv let term `%a`" T.pp t

      | _ ->
        (* TODO *)
        errorf "todo: conv term `%a`" T.pp t
    end

  let conv_subst (s:Ast.Subst.t) : K.Subst.t =
    List.fold_left
      (fun s (v,t) ->
         let t = conv_term t in
         let v = K.Var.make v.Ast.Var.name (E.ty_exn t) in
         K.Subst.bind s v t)
      K.Subst.empty s

  let conv_lit (lit: Ast.lit) : Lit.t =
    let {Ast.Lit.sign; atom} = lit in
    Lit.make sign (conv_term atom)

  let conv_lits (lits: Ast.lit list) : Clause.t =
    Log.debug (fun k->k"conv-lits %a" (Fmt.Dump.list Ast.Lit.pp) lits);
    let cl = Clause.empty in
    List.fold_left
      (fun c lit -> Clause.add (conv_lit lit) c)
      cl lits

  let conv_clause (c: Ast.clause) : Clause.t =
    Log.debug (fun k->k"conv-clause %a" Ast.Clause.pp c);
    match c with
    | Ast.Clause.Clause lits -> conv_lits lits
    | Ast.Clause.Clause_ref name ->
      begin match Hashtbl.find st.named_clauses name with
        | exception Not_found ->
          errorf "cannot find reference to clause %S" name
        | c -> c
      end

  module P = Ast.Proof

  (* check [p], returns its resulting clause.
     In case of error this returns the empty clause. *)
  let rec check_proof_or_empty_ p : Clause.t =
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
      Log.err (fun k->k"proof failed with:@ %s" e);
      st.n_invalid <- 1 + st.n_invalid;
      Clause.empty

  (* check proof [p], returns the clause it returns *)
  and check_proof_rec_exn (p: Ast.Proof.t) : bool * Clause.t =
    Log.debug (fun k->k"(@[check-proof-rec@ %a@])" P.pp p);
    begin match P.view p with
      | P.Sorry ->
        (* return `|- false` by default, we do not know what else to return *)
        false, Clause.empty

      | P.Sorry_c c ->
        false, conv_clause c

      | P.Refl t ->
        let t = conv_term t in
        true, Clause.of_thm (K.Thm.refl ctx t)

      | P.Assert t ->
        Log.warn (fun k->k"TODO: find assert in assumptions");
        (* FIXME: lookup in problem? *)
        (* TODO: use theory mechanism to track asserts *)

        (* assume: [¬t \/ t] *)
        let t = conv_term t in
        true, Clause.singleton (Lit.make true t)

      | P.Assert_c c ->
        (* FIXME: lookup in problem? *)
        let c = conv_clause c in
        true, c

      | P.Composite {assumptions; steps} ->
        (* composite proof: check each step *)

        (* locally push [name -> {lit}] for each assumption *)
        let asms = List.map (fun (name,lit) -> name, conv_lit lit) assumptions in
        List.iter
          (fun (name, lit) ->
            Hashtbl.add st.checked name (Clause.singleton lit))
          asms;

        let r =
          Array.fold_left
            (fun prev step ->
               match check_composite_step_ step with
               | Some c -> Some c
               | None -> prev)
            None steps
        in

        (* remove assumptions *)
        List.iter (fun (name,_) -> Hashtbl.remove st.checked name) asms;

        begin match r with
          | None -> errorf "composite proof returns no clause"
          | Some c -> true, c
        end

      | P.Named name ->
        begin match Hashtbl.find_opt st.checked name with
          | Some c -> true, c
          | None ->
            Log.err (fun k->k"cannot find step with name '%s'" name);
            false, Clause.empty
        end

      | P.CC_lemma_imply (ps, t, u) ->
        (* prove [ps |- t=u] *)
        let t = conv_term t in
        let u = conv_term u in

        (* check sub-proofs, and turn them into positive equations *)
        let ps = List.rev_map (fun p -> snd @@ check_proof_rec_exn p) ps in

        let hyps =
          ps
          |> List.rev_map
            (fun c -> match Clause.uniq_pos_lit c with
               | Some lit -> K.Thm.assume ctx (Lit.atom lit)
               | None ->
                 errorf
                   "lemma-imply: hypothesis yields %a@ \
                    but must have exactly one positive literal" Clause.pp c)
        in

        (* FIXME:
           - the CC lemma might ignore some hyps, so add these back
           - then do resolution with [ps], which might be Horn clauses,
              not just equalities *)

        begin match CC.prove_cc_eqn ctx hyps t u with
          | None ->
            Log.err (fun k->k"hyps: %a;@ concl: `@[%a@ = %a@]`"
                          Fmt.(Dump.list K.Thm.pp_quoted) hyps
                          E.pp t E.pp u);
            errorf "failed to prove CC-lemma@ %a" P.pp p
          | Some thm ->
            true, Clause.of_thm thm
        end

      | P.CC_lemma c ->
        let c = conv_clause c in

        let pos = Clause.pos_lits_list c in
        let negs = Clause.neg_lits_list c in
        begin match pos with
          | [goal] ->

            let goal = Lit.atom goal in
            let ps = List.map (fun l -> K.Thm.assume ctx (Lit.atom l)) negs in

            (* prove [negs |- goal] *)
            Log.debug
              (fun k->k"cc-lemma@ :ps %a@ :goal %a"
                      (Fmt.Dump.list K.Thm.pp_quoted) ps E.pp goal);

            let module CC = Trustee_core.Congruence_closure in
            begin match CC.prove_cc_bool ctx ps goal with
              | None ->
                Log.err (fun k->k"clause: %a" Clause.pp c);
                errorf "failed to prove@ %a" P.pp p
              | Some thm ->
                true, Clause.of_thm thm
            end
          | _ ->
            errorf
              "cc-lemma: expected exactly one positive literal@ in %a"
              Fmt.(Dump.list Lit.pp) (Clause.lits_list c)
          end

      | P.Paramod1 { rw_with; p=passive } ->
        let rw_with = check_proof_or_empty_ rw_with in
        let passive = check_proof_or_empty_ passive in
        Log.debug (fun k->k"(@[paramod1@ :rw-with %a@ :p %a@])"
                      Clause.pp rw_with Clause.pp passive);

        (* decompose [rw_with] into an equation [t=u] *)
        let t, u =
          match Clause.lits_list rw_with |> List.map Lit.as_eqn with
          | [Some (a,b)] -> a,b
          | _ ->
            errorf "expected (@[rw-with@ %a@])@ to be an equation" Clause.pp rw_with
        in

        let candidates =
          Clause.lits passive
          |> Iter.filter_map
            (fun lit ->
               let sign = Lit.sign lit in
               let a = Lit.atom lit in
               if E.equal a t then Some (a, sign, u)
               else if E.equal a u then Some (a, sign, t)
               else None)
          |> Iter.to_rev_list
        in

        begin match candidates with
          | [(a, _sign, into)] ->
            Log.debug (fun k->k"(@[paramodulation@ :of %a@ :with %a@ :pivot %a@])"
                          Clause.pp passive Clause.pp rw_with E.pp a);

            (* TODO: do the paramodulation *)
            let res = bool_param_on_ ~lhs:a ~rhs:into ~rw_with passive in
            true, res

          | (a1,_,_) :: (a2,_,_) :: _ ->
            errorf "ambiguous paramodulation %a by %a:@ \
                    possible candidates include %a@ and %a"
              P.pp p Clause.pp rw_with E.pp a1 E.pp a2

          | [] ->
            errorf "no candidate found for paramodulation %a" P.pp p
        end

      | P.Clause_rw { res; c0; using } ->
        let res = conv_clause res in
        let c0 = check_proof_or_empty_ c0 in
        let using = List.map check_proof_or_empty_ using in

        Log.debug (fun k->k"(@[clause-rw@ :res %a@ :c0 %a@ :using %a@])"
                      Clause.pp res Clause.pp c0 (Fmt.Dump.list Clause.pp) using);

        if using = [] then (
          if not (Clause.equal c0 res) then (
            errorf "clause rw failed (empty :using but distinct clauses)@ \
                   for %a" P.pp p
          );

          true, res
        ) else (

          let hyps_using =
            using
            |> Iter.of_list
            |> Iter.filter_map
              (fun c ->
                 match Clause.uniq_pos_lit c with
                 | Some lit -> Some (K.Thm.assume ctx (Lit.atom lit))
                 | None -> None)
          and hyps_neg_res =
            res
            |> Clause.lits
            |> Iter.map Lit.neg
            |> Iter.map (fun lit -> K.Thm.assume ctx (Lit.to_expr lit))
          in

          (* hypotheses common to each subproof *)
          let common_hyps =
            Iter.append hyps_using hyps_neg_res
            |> Iter.to_rev_list
          in

          (* check if [false] can be proven from [lit] and
             the common hypotheses ("using" side conditions,
             and the negated conclusion of [p]) *)
          let false_provable_with lit : bool =
            let hyp_lit =
              K.Thm.assume ctx (Lit.to_expr lit)
            in

            let hyps = hyp_lit :: common_hyps in
            let false_ = E.const ctx (get_builtin_ B.False) [] in

            begin match CC.prove_cc_bool ctx hyps false_ with
              | Some _ -> true
              | None ->
                Log.err
                  (fun k->k"(@[clause-rw: cannot prove@ :lit %a@ :from-hyps %a@])"
                      Lit.pp lit Fmt.(Dump.list K.Thm.pp) common_hyps);
                false
            end
          in

          let bad =
            Clause.lits c0
            |> Iter.map Lit.neg
            |> Iter.find_pred (fun l -> not (false_provable_with l))
          in
          begin match bad with
            | None ->
              (* valid *)
              Log.debug (fun k->k"valid: %a" P.pp p);
              true, res

            | Some bad ->
              Log.err (fun k->k"cannot validate %a@ because of literal %a"
                          P.pp p Lit.pp bad);
              false, res
          end
        )

      | P.Rup_res (c, hyps) ->
        Log.debug (fun k->k"check step %a" P.pp p);

        (* instantiate RUP checker *)
        let module D = Rup_check.Make(struct
            include K.Expr
            let dummy = st.dummy_e
          end) in

        let c = conv_clause c in
        let hyps = List.map check_proof_or_empty_ hyps in

        let cstore = D.Clause.create() in
        let checker = D.Checker.create cstore in

        let lit_to_atom (lit:Lit.t) =
          let t = Lit.atom lit in
          let sign = Lit.sign lit in
          D.Atom.make ~sign t
        in

        List.iter
          (fun hyp ->
             let c =
               Clause.lits hyp
               |> Iter.map lit_to_atom
               |> Iter.to_rev_list
             in
             D.Checker.add_clause_l checker c)
          hyps;

        (* the goal clause [c] *)
        let goal =
          Clause.lits c
          |> Iter.map lit_to_atom
          |> D.Clause.of_iter cstore
        in

        let ok = D.Checker.is_valid_drup checker goal in
        Log.debug (fun k->k"RUP check@ for %a:@ %B" Clause.pp c ok);
        ok, c

      | P.Res {pivot; p1; p2} ->
        let pivot = conv_term pivot in
        let c1 = check_proof_or_empty_ p1 in
        let c2 = check_proof_or_empty_ p2 in
        true, res_on_ ~pivot c1 c2

      | P.Res1 {p1; p2} ->
        let c1 = check_proof_or_empty_ p1 in
        let c2 = check_proof_or_empty_ p2 in
        begin match Clause.as_singleton c1, Clause.as_singleton c2 with
          | Some lit, _
          | None, Some lit ->
            true, res_on_ ~pivot:(Lit.atom lit) c1 c2
          | None, None ->
            errorf
              "res1: expected one of the clauses to be unit@ \
               where c1=`%a`,@ c2=`%a`"
              Clause.pp c1 Clause.pp c2
        end

      | P.Subst (subst, p1) ->
        let ok, p1 = check_proof_rec_exn p1 in
        if ok then (
          let subst = conv_subst subst in
          true, Clause.subst ~recursive:false p1 subst
        ) else ok, p1

      | P.Hres (init, steps) ->

        let init = check_proof_or_empty_ init in
        let c = List.fold_left check_hres_step_ init steps in
        true, c

      | P.Bool_c (name, ts) ->
        let ts = List.map conv_term ts in
        check_bool_c p name ts

      | P.Nn p ->
        let c = check_proof_or_empty_ p in

        let c =
          Clause.lits c
          |> Iter.map
            (fun lit ->
               match unfold_not_ (Lit.atom lit) with
               | Some u -> Lit.make (not (Lit.sign lit)) u
               | None -> lit)
          |> Clause.of_iter
        in
        true, c

      | P.Bool_true_is_true ->
        let true_ = E.const ctx (get_builtin_ B.True) [] in
        true, Clause.singleton @@ Lit.make true true_

      | P.Bool_true_neq_false ->
        let true_ = E.const ctx (get_builtin_ B.True) [] in
        let false_ = E.const ctx (get_builtin_ B.False) [] in
        let eq = E.app_eq ctx true_ false_ in
        true, Clause.singleton @@ Lit.make false eq

      | P.Ite_true t_ite ->
        (* clause [(cl (- a) (+ (= (ite a b c) b)))] *)
        let t_ite = conv_term t_ite in
        begin match E.unfold_app t_ite with
          | ite, [a;b;_c] when is_builtin_const_ B.If ite ->
            true, Clause.of_list [Lit.make false a; Lit.make true (E.app_eq ctx t_ite b)]
          | _ -> errorf "expected a `ite` term,@ got `%a`" E.pp t_ite
        end

      | P.Ite_false t_ite ->
        (* clause [(cl (- ¬a) (+ (= (ite a b c) c)))] *)
        let t_ite = conv_term t_ite in
        begin match E.unfold_app t_ite with
          | ite, [a;_b;c] when is_builtin_const_ B.If ite ->
            let c =
              Clause.of_list [
                Lit.make false (E.app ctx Cst.not_ a);
                Lit.make true (E.app_eq ctx t_ite c)
              ] in
            true, c
          | _ -> errorf "expected a `ite` term,@ got `%a`" E.pp t_ite
        end

      | P.With (bs, p) ->
        (* locally define [bs], check [p], then remove bindings *)
        List.iter
          (fun (v,t) ->
            let t = conv_term t in
            Hashtbl.add st.named_terms v t)
          bs;
        CCFun.finally1
          ~h:(fun () -> List.iter (fun (n,_) -> Hashtbl.remove st.named_terms n) bs)
          check_proof_rec_exn p

      | P.DT_isa_split (_, _)
      | P.DT_isa_disj (_, _, _)
      | P.DT_cstor_inj (_, _, _, _)
      | P.Bool_eq (_, _)
      | P.LRA _
        ->
        Log.warn (fun k->k"unimplemented: checking %a" P.pp p);
        false, Clause.empty (* TODO *)
    end

  and check_bool_c p name (ts:K.expr list) : bool * Clause.t =
    let module B = Quip_core.Builtin in

    let get1 = function [t] -> Some t | _ -> None in
    let get2 = function [t;u] -> Some (t,u) | _ -> None in

    begin match name with
      | P.And_i ->
        (* [¬a1 \/ ¬a2 \/ … \/ (and a1...an)] *)

        begin
          let open CCOpt.Infix in
          match
            let* and_ = get1 ts in
            let* args = unfold_builtin B.And and_ in
            let c =
              Clause.of_list
                (Lit.make true and_ :: List.map (Lit.make false) args)
            in
            Some c
          with
          | Some c -> true, c
          | None ->
            Log.err (fun k->k"cannot check %a" P.pp p);
            false, Clause.empty
        end

      | P.And_e ->
        (* [¬(and a1…an  \/ a_i] *)

        begin
          let open CCOpt.Infix in
          match
            let* and_, u = get2 ts in
            let* args = unfold_builtin B.And and_ in
            let ok = CCList.mem ~eq:E.equal u args in
            let c =
              if ok then Clause.of_list [Lit.make false and_; Lit.make true u]
              else Clause.empty
            in
            Some (ok, c)
          with
          | Some tup -> tup
          | None ->
            Log.err (fun k->k"cannot check %a" P.pp p);
            false, Clause.empty
        end

      | P.Or_i ->
        (* [¬a \/ (or a1…an)] *)

        begin
          let open CCOpt.Infix in
          match
            let* or_, u = get2 ts in
            let* args = unfold_builtin B.Or or_ in
            let ok = CCList.mem ~eq:E.equal u args in
            let c =
              if ok then Clause.of_list [Lit.make false u; Lit.make true or_]
              else Clause.empty
            in
            Some (ok, c)
          with
          | Some tup -> tup
          | None ->
            Log.err (fun k->k"cannot check %a" P.pp p);
            false, Clause.empty
        end

      | P.Or_e ->
        (* [¬(or a1…an) \/ a1 \/ … \/ an] *)

        begin
          let open CCOpt.Infix in
          match
            let* or_ = get1 ts in
            let* args = unfold_builtin B.Or or_ in
            let c =
              Clause.of_list
                (Lit.make false or_ :: List.map (Lit.make true) args)
            in
            Some c
          with
          | Some c -> true, c
          | None ->
            Log.err (fun k->k"cannot check %a" P.pp p);
            false, Clause.empty
        end

      | P.Not_i
      | P.Not_e
      | P.Imp_i
      | P.Imp_e
      | P.Eq_i
      | P.Eq_e
      | P.Xor_i
      | P.Xor_e ->
        false, Clause.empty (* TODO *)
    end

  (* do resolution between [c1] and [c2] *)
  and res_on_ ~pivot c1 c2 : Clause.t =
    Log.debug (fun k->k "(@[resolve@ :c1 %a@ :c2 %a@ :pivot %a@])"
                  Clause.pp c1 Clause.pp c2 E.pp pivot);
    (* find the polarity of [pivot] in [c1] *)
    match Clause.find_lit_by_term pivot c1 with
    | Some lit ->
      let lit' = Lit.neg lit in
      if Clause.mem lit' c2 then (
        Clause.(union (remove lit c1) (remove lit' c2))
      ) else (
        errorf "cannot resolve: pivot `%a`@ does not occur in `%a`"
          E.pp pivot Clause.pp c2
      )

    | None ->
      errorf "cannot resolve %a@ on pivot `%a`" Clause.pp c1 E.pp pivot

  (* do bool paramodulation between [c1] and [c2],
       where [c2] must contain [lhs = rhs] and [c1] must contain [lhs] *)
  and bool_param_on_ ~lhs ~rhs c1 ~rw_with:c2 : Clause.t =
    Log.debug (fun k->k "(@[bool-param@ :c1 %a@ :c2 %a@ :lhs `%a`@ :rhs `%a`@])"
                  Clause.pp c1 Clause.pp c2 E.pp lhs E.pp rhs);
    (* find if [c2] contains [lhs=rhs] or [rhs=lhs] *)
    match
      Clause.find_lit_by_term lhs c1,
      (Clause.lits c2
       |> Iter.filter Lit.sign
       |> Iter.find_map
         (fun lit ->
            let e = Lit.atom lit in
            match E.unfold_eq e with
            | Some (t1, t2) when E.equal t1 lhs && E.equal t2 rhs ->
              Some lit
            | Some (t1, t2) when E.equal t2 lhs && E.equal t1 rhs ->
              Some lit
            | _ -> None))
    with
    | None, _ ->
      errorf
        "cannot perform bool paramod@ in `%a`:@ it does not contain `%a`"
        Clause.pp c1 K.Expr.pp lhs

    | _, None ->
      errorf "cannot do unit-paramod on %a" Clause.pp c2

    | Some lit_lhs, Some lit_eqn ->
      assert (Lit.sign lit_eqn);
      (* preserve sign of the rewritten literal *)
      let new_lit = Lit.make (Lit.sign lit_lhs) rhs in
      Clause.(
        add new_lit @@
        union
          (remove (Lit.make true lhs) c1)
          (remove lit_eqn c2)
      )

  and check_hres_step_ (c1: Clause.t) (step:P.hres_step) : Clause.t =
    begin match step with
      | P.R {pivot; p} ->
        let pivot = conv_term pivot in
        let c2 = check_proof_or_empty_ p in
        res_on_ ~pivot c1 c2

      | P.R1 p ->
        let c2 = check_proof_or_empty_ p in
        let pivot = match Clause.as_singleton c2 with
          | None ->
            errorf "r1: clause `%a`@ does not have a unique positive literal"
              Clause.pp c2
          | Some t -> Lit.atom t
        in
        res_on_ ~pivot c1 c2

      | P.P { lhs; rhs; p } ->
        let lhs = conv_term lhs in
        let rhs = conv_term rhs in
        let c2 = check_proof_or_empty_ p in
        bool_param_on_ ~lhs ~rhs c1 ~rw_with:c2

      | P.P1 p ->
        let c2 = check_proof_or_empty_ p in
        let fail() = errorf "cannot do p1 on %a" Clause.pp c2 in
        match Clause.uniq_pos_lit c2 with
        | Some lit ->
          assert (Lit.sign lit);
          begin match E.unfold_eq (Lit.atom lit) with
            | Some (lhs, rhs) -> bool_param_on_ ~lhs ~rhs c1 ~rw_with:c2
            | None -> fail()
          end
        | None -> fail()
    end

  and check_composite_step_ (step: Ast.Proof.composite_step) : Clause.t option =
   begin match step with
    | P.S_define_t (name, u) ->
      let u = conv_term u in
      Hashtbl.add st.named_terms name u;
      None

    | P.S_step_c { name; res; proof } ->

      (* first, convert clause declared with this step.
         It is named [name] in [proof]. *)
      let expected_c = conv_lits res in
      Hashtbl.add st.named_clauses name expected_c;

      Log.info (fun k->k"check step '%s'" name);

      let c = check_proof_or_empty_ proof in
      Log.debug (fun k->k"step '%s'@ yields %a" name Clause.pp c);

      (* named clause goes out of scope *)
      Hashtbl.remove st.named_clauses name;

      let c =
        if Clause.subset c expected_c then (
          (* [c subset expected_c] is valid, we just use [expected_c]
             in the rest of the proof to avoid drift *)
          expected_c
        ) else (
          Log.err (fun k->k"step '%s'@ should yield %a@ but proof returns %a"
                      name Clause.pp expected_c Clause.pp c);
          st.n_invalid <- 1 + st.n_invalid;
          (* use the expected clause instead *)
          expected_c
        )
      in

      Hashtbl.add st.checked name c;

      Some c

    | P.S_declare_ty_const {name; arity} ->
      let c = E.new_ty_const ctx name arity in
      Problem.decl_ty_const name c;
      None

    | P.S_declare_const {name; ty} ->
      let ty = conv_ty ty in
      (* TODO: polymorphic types *)
      let c = E.new_const ctx name [] ty in
      Problem.decl_const name c;
      None

    | P.S_define_const {name; ty; rhs} ->
      let ty = conv_ty ty in
      let rhs = conv_term rhs in

      (* [(name:ty) = rhs] as defining equation *)
      let defe = E.app_eq ctx (E.var_name ctx name ty) rhs in
      let th, c = K.Thm.new_basic_definition ctx defe in
      Problem.def_const name c th;
      Some (Clause.of_thm th)

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
