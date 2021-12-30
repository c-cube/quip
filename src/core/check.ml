
open Common

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Proof checker" "quip.check"))

module CC = Congruence_closure

module K = Kernel
module E = K.Expr

type bad = string
type stats = {
  n_valid: int;
  n_invalid: int;
  n_steps: int;
} [@@deriving show {with_path=false}]

module type S = sig
  val check_proof : Ast.Proof.t -> bool * bad list * Error.t list * stats
end

type t = (module S)

module type ARG = sig
  val ctx : K.ctx
  val problem : Env.t
  val ast_ctx : Ast.Small_loc.ctx
end

module Make(A : ARG) : S = struct
  open A
  module Problem = (val A.problem)
  module B = Builtin

  let trsloc loc = Ast.Small_loc.to_loc A.ast_ctx loc

  let unwrap_or_ msg = function
    | Some x -> x
    | None -> Error.raise (msg ())

  (** {2 Some constants} *)
  module Cst = struct
    let find_ ~loc name builtin =
      let c =
        Problem.find_builtin builtin
        |> unwrap_or_ (fun() -> Error.makef ~loc "cannot find builtin %s" name)
      in
      K.Expr.const ctx c []
  end

  (* if [e] the builtin [b]? *)
  let is_builtin_const_ b (e:E.t) : bool =
    match E.view e with
    | E.E_const (c, _) ->
      begin match Problem.find_builtin b with
        | Some c' -> K.Const.equal c c'
        | None -> false
      end
    | _ -> false

  (* find builtin [b] *)
  let get_builtin_ ~loc b =
    match Problem.find_builtin b with
    | Some c -> c
    | None ->
      Error.failf ~loc:(trsloc loc) "cannot find builtin %a" B.pp b

  (* unfold builtin application. *)
  let unfold_builtin ~loc b e : _ list option =
    let cb = get_builtin_ ~loc b in
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

  (** A custom error list, with a cap on storage *)
  module Error_list : sig
    type t
    val create : ?max:int -> unit -> t
    val push : t -> Error.t -> unit
    val get_l : t -> Error.t list
  end = struct
    type t = {
      mutable n: int;
      mutable errs: Error.t list;
      max: int;
    }

    let create ?(max=10) () : t =
      { errs=[]; max; n=0 }

    let push self e =
      self.n <- self.n + 1;
      if self.n < self.max then (
        self.errs <- e :: self.errs
      )

    let get_l self = List.rev self.errs
  end

  type st = {
    checked: (string, (Clause.t, Error.t) result) Hashtbl.t;
    named_terms: (string, K.expr) Hashtbl.t;
    named_clauses: (string, Clause.t) Hashtbl.t;
    errors: Error_list.t;
    mutable bad: bad list;
    mutable n_valid: int;
    mutable n_invalid: int;
    mutable n_steps: int;
    dummy_e: K.expr;
  }

  let st : st =
    let _c = K.Expr.new_ty_const ctx " <dummy>" 0 in
    {
      checked = Hashtbl.create 32;
      errors=Error_list.create();
      named_terms = Hashtbl.create 16;
      named_clauses = Hashtbl.create 16;
      bad=[];
      n_valid=0; n_invalid=0; n_steps=0;
      dummy_e = K.Expr.const ctx _c [];
    }

  let rec conv_ty (ty: Ast.ty) : K.ty =
    let loc = ty.loc in
    match ty.view with
    | Ast.Ty.Arrow (args, ret) ->
      let args = List.map conv_ty args in
      let ret = conv_ty ret in
      E.arrow_l ctx args ret
    | Ast.Ty.Constr (s, args) ->
      (* FIXME: type variables *)
      begin match Problem.find_ty_const_by_name s with
        | None ->
          Error.failf ~loc:(trsloc loc) "cannot convert unknown type constant `%s`" s
        | Some c ->
          let args = List.map conv_ty args in
          E.const ctx c args
      end

  let rec conv_term (t: Ast.term) : K.expr =
    let module T = Ast.Term in
    (* Log.debug (fun k->k"(@[conv-t %a@])" T.pp t); *)
    let loc = T.loc t in
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
                when Builtin.is_assoc b ->
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
                    Error.failf ~loc:(trsloc loc) "cannot convert unknown identifier@ `%a`" T.pp t
                end
            end
        end
      | T.Not u ->
        let u = conv_term u in
        E.not_ ctx u
      | T.Ite (a,b,c) ->
        let ite = get_builtin_ ~loc B.If in
        let a = conv_term a in
        let b = conv_term b in
        let c = conv_term c in
        E.app_l ctx (E.const ctx ite [E.ty_exn b]) [a;b;c]

      | T.Ref name ->
        begin match Hashtbl.find_opt st.named_terms name with
          | Some u -> u
          | None ->
            Error.failf ~loc:(trsloc loc) "reference to unknown term %S" name
        end

      | T.Is_a (c,t) ->
        let c = match Problem.find_cstor c with
          | None -> Error.failf ~loc:(trsloc loc) "unknown constructor '%s'" c
          | Some c -> c
        in
        let t = conv_term t in
        E.app ctx (E.const ctx c.c_isa []) t

      | T.Fun _ ->
        Error.failf ~loc:(trsloc loc) "todo: conv lambda term `%a`" T.pp t
      | T.Let _ ->
        Error.failf ~loc:(trsloc loc) "todo: conv let term `%a`" T.pp t

      | T.As _ ->
        (* TODO *)
        Error.failf ~loc:(trsloc loc) "todo: conv term `%a`" T.pp t
    end

  let conv_subst (s:Ast.Subst.t) : K.Subst.t =
    List.fold_left
      (fun s (v,t) ->
         let t = conv_term t in
         let v = K.Var.make v.Ast.Var.name (E.ty_exn t) in
         K.Subst.bind s v t)
      K.Subst.empty s

  let conv_lit (t: Ast.term) : Lit.t =
    let t = conv_term t in
    match E.unfold_not t with
    | Some u -> Lit.make ctx false u
    | None -> Lit.make ctx true t

  let conv_lits (lits: Ast.term list) : Clause.t =
    Log.debug (fun k->k"conv-lits %a" (Fmt.Dump.list Ast.Term.pp) lits);
    let cl = Clause.empty in
    List.fold_left
      (fun c lit -> Clause.add (conv_lit lit) c)
      cl lits

  let conv_clause (c: Ast.clause) : Clause.t =
    Log.debug (fun k->k"conv-clause %a" Ast.Clause.pp c);
    let loc = c.loc in
    match c.view with
    | Ast.Clause.Clause lits -> conv_lits lits
    | Ast.Clause.Clause_ref name ->
      begin match Hashtbl.find st.named_clauses name with
        | exception Not_found ->
          Error.failf ~loc:(trsloc loc) "cannot find reference to clause %S" name
        | c -> c
      end

  module P = Ast.Proof

  let register_error (e:Error.t) =
    st.n_invalid <- 1 + st.n_invalid;
    Error_list.push st.errors e

  (* check [p], returns its resulting clause. *)
  let rec check_proof_rec (p:P.t) : Clause.t =
    st.n_steps <- 1 + st.n_steps;
    let c = check_proof_rec_ p in
    Log.debug (fun k->k"(@[check-proof.res@ :for %a@])" P.pp p);
    st.n_valid <- 1 + st.n_valid;
    c

  (* check [p], returns its clause. *)
  and check_proof_rec_ (p: Ast.Proof.t) : Clause.t =
    Profile.with_ "check-proof-rec" @@ fun () ->
    Log.debug (fun k->k"(@[check-proof-rec@ %a@])" P.pp p);

    let loc = P.loc p in
    begin match P.view p with
      | P.Sorry ->
        (* return `|- false` by default, we do not know what else to return *)
        Error.failf ~loc:(trsloc loc) "met a 'sorry' step"

      | P.Sorry_c _c ->
        Error.failf ~loc:(trsloc loc) "met a 'sorry' step"

      | P.Refl t ->
        let t = conv_term t in
        Clause.singleton (Lit.make ctx true (E.app_eq ctx t t))

      | P.Assert t ->
        Log.warn (fun k->k"TODO: find assert in assumptions");
        (* FIXME: lookup in problem? *)
        (* TODO: use theory mechanism to track asserts *)

        (* assume: [t] *)
        let t = conv_term t in
        Clause.singleton (Lit.make ctx true t)

      | P.Assert_c c ->
        (* FIXME: lookup in problem? *)
        let c = conv_clause c in
        c

      | P.Composite {assumptions; steps} ->
        (* composite proof: check each step *)
        Profile.with_ "check.composite" @@ fun () ->

        (* locally push [name -> {lit}] for each assumption *)
        let asms = List.map (fun (name,lit) -> name, conv_lit lit) assumptions in
        List.iter
          (fun (name, lit) ->
            Hashtbl.add st.checked name (Ok (Clause.singleton lit)))
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
          | None -> Error.failf ~loc:(trsloc loc) "composite proof returns no clause"
          | Some c -> c
        end

      | P.Named name ->
        begin match Hashtbl.find_opt st.checked name with
          | Some (Ok c) -> c
          | Some (Error err) ->
            Error.raise (Error.wrapf ~loc:(trsloc loc) "dereferencing '%s'" name @@ err)
          | None ->
            Error.failf ~loc:(trsloc loc) "cannot find step with name '%s'" name
        end

      | P.CC_lemma_imply (ps, t, u) ->
        Profile.with_ "check.cc-lemma-imply" @@ fun () ->

        (* prove [ps |- t=u] *)
        let t = conv_term t in
        let u = conv_term u in

        (* check sub-proofs *)
        let ps = List.rev_map check_proof_rec ps in

        let hyp_lits =
          ps
          |> List.rev_map
            (fun c -> match Clause.uniq_pos_lit c with
               | Some lit -> lit
               | None ->
                 Error.failf ~loc:(trsloc loc)
                   "lemma-imply: hypothesis yields %a@ \
                    but must have exactly one positive literal" Clause.pp c)
        in

        (* [hyps /\ t ≠ u] *)
        let neg_lits = Lit.make ctx false (E.app_eq ctx t u) :: hyp_lits in

        let ok = check_absurd_by_cc ~loc neg_lits in
        if ok then (
          let c = [Lit.make ctx true (E.app_eq ctx t u)] in
          Clause.of_list c
        ) else (
          Error.failf ~loc:(trsloc loc)
            "failed to prove CC-lemma-imply@ :negated-literals %a@ :step %a"
            (Fmt.Dump.list @@ Lit.pp_depth ~max_depth:4) neg_lits P.pp p
        )

      | P.CC_lemma c ->
        Profile.with_ "check.cc-lemma" @@ fun () ->
        let c = conv_clause c in

        (* check that [¬C] is absurd *)
        let neg_lits =
          Clause.lits c
          |> Iter.map Lit.neg
          |> Iter.to_rev_list
        in

        let ok = check_absurd_by_cc ~loc neg_lits in
        if ok then (
          c
        ) else (
          Error.failf ~loc:(trsloc loc)
            "failed to prove CC-lemma@ :negated-literals %a@ \
             :expected-clause %a@ :step %a"
            (Fmt.Dump.list @@ Lit.pp_depth ~max_depth:4) neg_lits
            Clause.pp c P.pp p
        )

      | P.Paramod1 { rw_with; p=passive } ->
        Profile.with_ "check.paramod1" @@ fun () ->

        let rw_with = check_proof_rec rw_with in
        let passive = check_proof_rec passive in
        Log.debug (fun k->k"(@[paramod1@ :rw-with %a@ :p %a@])"
                      Clause.pp rw_with Clause.pp passive);

        (* decompose [rw_with] into an equation [t=u] *)
        let t, u =
          match Clause.lits_list rw_with |> List.map Lit.as_eqn with
          | [Some (a,b)] -> a,b
          | _ ->
            Error.failf ~loc:(trsloc loc)
              "expected (@[rw-with@ %a@])@ to be an equation" Clause.pp rw_with
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

            let res = bool_param_on_ ~loc ~lhs:a ~rhs:into ~rw_with passive in
            res

          | (a1,_,_) :: (a2,_,_) :: _ ->
            Error.failf ~loc:(trsloc loc)
              "ambiguous paramodulation %a by %a:@ \
               possible candidates include %a@ and %a"
              P.pp p Clause.pp rw_with E.pp a1 E.pp a2

          | [] ->
            Error.failf ~loc:(trsloc loc)
              "@[<2>no candidate found for paramodulation@ \
               @[<2>passive clause: %a@]@ \
               @[<2>rewrite with: %a@]@ \
               @[<2>step: %a@]@]"
              Clause.pp passive Clause.pp rw_with P.pp p
        end

      | P.Clause_rw { res; c0; using } ->
        Profile.with_ "check.clause-rw" @@ fun () ->

        let res = conv_clause res in
        let c0 = check_proof_rec c0 in
        let using = List.map check_proof_rec using in

        Log.debug (fun k->k"(@[clause-rw@ :res %a@ :c0 %a@ :using %a@])"
                      Clause.pp res Clause.pp c0 (Fmt.Dump.list Clause.pp) using);

        if using = [] then (
          if not (Clause.equal c0 res) then (
            Error.failf ~loc:(trsloc loc)
              "clause rw failed (empty :using but distinct clauses)@ \
               for %a" P.pp p
          );

          res
        ) else (

          let hyps_using =
            using
            |> Iter.of_list
            |> Iter.filter_map Clause.uniq_pos_lit
          and hyps_neg_res =
            res
            |> Clause.lits
            |> Iter.map Lit.neg
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
            let hyps = lit :: common_hyps in

            let valid = check_absurd_by_cc ~loc hyps in
            if not valid then (
              Log.err
                (fun k->k"(@[clause-rw: cannot prove@ :lit %a@ :from-hyps %a@])"
                    (Lit.pp_depth ~max_depth:4) lit
                    Fmt.(Dump.list @@ within "`" "`" @@
                         Lit.pp_depth ~max_depth:4) common_hyps);
              Log.debug (fun k->k"(@[all-hyps: %a@])"
                            (Fmt.Dump.list @@ Lit.pp_depth ~max_depth:4)
                            hyps);

            );
            valid
          in

          let bad =
            Clause.lits c0
            |> Iter.find_pred (fun l -> not (false_provable_with l))
          in
          begin match bad with
            | None ->
              (* valid *)
              Log.debug (fun k->k"valid: %a" P.pp p);
              res

            | Some bad ->
              Error.failf ~loc:(trsloc loc)
                "cannot validate %a@ because of literal %a"
                P.pp p (Lit.pp_depth ~max_depth:5) bad
          end
        )

      | P.Rup_res (c, hyps) ->
        Log.debug (fun k->k"check step %a" P.pp p);

        let c = conv_clause c in
        let hyps = List.map check_proof_rec hyps in

        let ok =
          Profile.with_ "check.rup-res" @@ fun () ->

          (* instantiate RUP checker *)
          let module D = Rup_check.Make(struct
              include K.Expr
              let dummy = st.dummy_e
            end) in

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

          D.Checker.is_valid_drup checker goal
        in

        Log.debug (fun k->k"(@[RUP-check.res@ :res %B@ :for %a@ :hyps %a@])"
                      ok Clause.pp c (Fmt.Dump.list Clause.pp) hyps);
        if ok then c else (
          Error.failf ~loc:(trsloc loc)
            "RUP step failed@ \
             @[<v2>expected result clause is:@ %a@]@ \
             @[<v2>clauses are:@ %a@]"
            Clause.pp c
            (Fmt.list Clause.pp) hyps
        )

      | P.Res {pivot; p1; p2} ->
        Profile.with_ "check.res" @@ fun () ->

        let pivot = conv_term pivot in
        let c1 = check_proof_rec p1 in
        let c2 = check_proof_rec p2 in
        res_on_ ~loc ~pivot c1 c2

      | P.Res1 {p1; p2} ->
        Profile.with_ "check.res1" @@ fun () ->

        let c1 = check_proof_rec p1 in
        let c2 = check_proof_rec p2 in
        begin match Clause.as_singleton c1, Clause.as_singleton c2 with
          | Some lit, _
          | None, Some lit ->
            res_on_ ~loc ~pivot:(Lit.atom lit) c1 c2
          | None, None ->
            Error.failf ~loc:(trsloc loc)
              "res1: expected one of the clauses to be unit@ \
               where c1=`%a`,@ c2=`%a`"
              Clause.pp c1 Clause.pp c2
        end

      | P.Subst (subst, p1) ->
        Profile.with_ "check.subst" @@ fun () ->

        let p1 = check_proof_rec p1 in
        let subst = conv_subst subst in
        Clause.subst ctx ~recursive:false p1 subst

      | P.Hres (init, steps) ->
        Profile.with_ "check.hres" @@ fun () ->

        let init = check_proof_rec init in
        let c = List.fold_left check_hres_step_ init steps in
        c

      | P.Bool_c (name, ts) ->
        Profile.with_ "check.bool-c" @@ fun () ->

        let ts = List.map conv_term ts in
        check_bool_c ~loc p name ts

      | P.Bool_true_is_true ->
        let true_ = E.const ctx (get_builtin_ ~loc B.True) [] in
        Clause.singleton @@ Lit.make ctx true true_

      | P.Bool_true_neq_false ->
        let true_ = E.const ctx (get_builtin_ ~loc B.True) [] in
        let false_ = E.const ctx (get_builtin_ ~loc B.False) [] in
        let eq = E.app_eq ctx true_ false_ in
        Clause.singleton @@ Lit.make ctx false eq

      | P.Ite_true t_ite ->
        (* clause [(cl (- a) (+ (= (ite a b c) b)))] *)
        let t_ite = conv_term t_ite in
        begin match E.unfold_app t_ite with
          | ite, [a;b;_c] when is_builtin_const_ B.If ite ->
            Clause.of_list [Lit.make ctx false a; Lit.make ctx true (E.app_eq ctx t_ite b)]
          | _ ->
            Error.failf ~loc:(trsloc loc)
              "expected a `ite` term,@ got `%a`" E.pp t_ite
        end

      | P.Ite_false t_ite ->
        (* clause [(cl (- ¬a) (+ (= (ite a b c) c)))] *)
        let t_ite = conv_term t_ite in
        begin match E.unfold_app t_ite with
          | ite, [a;_b;c] when is_builtin_const_ B.If ite ->
            let c =
              Clause.of_list [
                Lit.make ctx false (E.not_ ctx a);
                Lit.make ctx true (E.app_eq ctx t_ite c)
              ] in
            c
          | _ ->
            Error.failf ~loc:(trsloc loc)
              "expected a `ite` term,@ got `%a`" E.pp t_ite
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
          check_proof_rec p

      | P.DT_isa_split (_, _)
      | P.DT_isa_disj (_, _, _)
      | P.DT_cstor_inj (_, _, _, _)
      | P.Bool_eq (_, _)
      | P.LRA _
        ->
        Error.failf ~loc:(trsloc loc) "unimplemented: checking %a" P.pp p
    end

  and check_bool_c ~loc p name (ts:K.expr list) : Clause.t =
    let module B = Builtin in

    let get1 = function [t] -> Some t | _ -> None in
    let get2 = function [t;u] -> Some (t,u) | _ -> None in

    begin match name with
      | P.And_i ->
        (* [¬a1 \/ ¬a2 \/ … \/ (and a1...an)] *)

        begin
          let open CCOpt.Infix in
          match
            let* and_ = get1 ts in
            let* args = unfold_builtin ~loc B.And and_ in
            let c =
              Clause.of_list
                (Lit.make ctx true and_ :: List.map (Lit.make ctx false) args)
            in
            Some c
          with
          | Some c -> c
          | None ->
            Error.failf ~loc:(trsloc loc) "cannot check %a" P.pp p
        end

      | P.And_e ->
        (* [¬(and a1…an  \/ a_i] *)

        begin
          let open CCOpt.Infix in
          match
            let* and_, u = get2 ts in
            let* args = unfold_builtin ~loc B.And and_ in
            let ok = CCList.mem ~eq:E.equal u args in
            let c =
              if ok then Clause.of_list [Lit.make ctx false and_; Lit.make ctx true u]
              else Error.failf ~loc:(trsloc loc)
                  "%a does not occur in %a" E.pp u Fmt.(Dump.list E.pp) args
            in
            Some c
          with
          | Some c -> c
          | None ->
            Error.failf ~loc:(trsloc loc) "Cannot check %a" P.pp p
        end

      | P.Or_i ->
        (* [¬a \/ (or a1…an)] *)

        begin
          let open CCOpt.Infix in
          match
            let* or_, u = get2 ts in
            let* args = unfold_builtin ~loc B.Or or_ in
            let ok = CCList.mem ~eq:E.equal u args in
            let c =
              if ok then Clause.of_list [Lit.make ctx false u; Lit.make ctx true or_]
              else Error.failf ~loc:(trsloc loc) "%a does not occur in %a" E.pp u Fmt.(Dump.list E.pp) args
            in
            Some c
          with
          | Some c -> c
          | None ->
            Error.failf ~loc:(trsloc loc) "Cannot check %a" P.pp p
        end

      | P.Or_e ->
        (* [¬(or a1…an) \/ a1 \/ … \/ an] *)

        begin
          let open CCOpt.Infix in
          match
            let* or_ = get1 ts in
            let* args = unfold_builtin ~loc B.Or or_ in
            let c =
              Clause.of_list
                (Lit.make ctx false or_ :: List.map (Lit.make ctx true) args)
            in
            Some c
          with
          | Some c -> c
          | None ->
            Error.failf ~loc:(trsloc loc) "Cannot check %a" P.pp p
        end


      | P.Imp_e ->
        (* [¬(=> a1…an b) \/ ¬a1 \/ … ¬an \/ b] *)

        begin
          let open CCOpt.Infix in
          match
            let* imp = get1 ts in
            let* args = unfold_builtin ~loc B.Imply imp in
            let args, ret = match args with
              | [] -> Error.failf ~loc:(trsloc loc) "empty implication"
              | r :: l -> l, r
            in
            let c =
              Clause.of_list
                (Lit.make ctx false imp ::
                 Lit.make ctx true ret ::
                 List.map (Lit.make ctx false) args)
            in
            Some c
          with
          | Some c -> c
          | None ->
            Error.failf ~loc:(trsloc loc) "Cannot check %a" P.pp p
        end

      | P.Eq_e ->
        (* [¬ (a=b) \/ ¬a \/ b] *)
        begin
          let open CCOpt.Infix in
          match
            let* eq, t = get2 ts in
            let* a, b = E.unfold_eq eq in
            if E.equal t a then
              Some (Clause.of_list [Lit.make ctx false eq; Lit.make ctx false t; Lit.make ctx true b])
            else if E.equal t b then
              Some (Clause.of_list [Lit.make ctx false eq; Lit.make ctx false t; Lit.make ctx true a])
            else
              None
          with
          | Some c -> c
          | None ->
            Error.failf ~loc:(trsloc loc) "Cannot check %a" P.pp p
        end


      | P.Imp_i
      | P.Not_i
      | P.Not_e
      | P.Eq_i
      | P.Xor_i
      | P.Xor_e ->
        Error.failf ~loc:(trsloc loc) "TODO: check bool-c@ %a" P.pp p
    end

  (** [check_absurd_by_cc lits] returns [true] if the conjunction of [lits]
      is proven false by congruence closure + basic boolean reasoning
      (mostly equating [a] with [a=true], and [¬a] with [a=false]) *)
  and check_absurd_by_cc ~loc (lits: Lit.t list) : bool =
    let true_ = E.const ctx (get_builtin_ ~loc B.True) [] in
    let false_ = E.const ctx (get_builtin_ ~loc B.False) [] in
    begin match
        CC.is_absurd ctx lits ~true_ ~false_
      with
      | Some proof ->
        Log.debug (fun k->k"cc.check-absurd: yields@ `%a`" CC.Proof.pp proof);
        true
      | None ->
        Log.debug (fun k->k"cc.check-absurd: fails to prove unsat@ `%a`"
                      (Fmt.Dump.list Lit.pp) lits);
        false
    end

  (* do resolution between [c1] and [c2] *)
  and res_on_ ~loc ~pivot c1 c2 : Clause.t =
    Log.debug (fun k->k "(@[resolve@ :c1 %a@ :c2 %a@ :pivot %a@])"
                  Clause.pp c1 Clause.pp c2 E.pp pivot);
    (* find the polarity of [pivot] in [c1] *)
    match Clause.find_lit_by_term ctx pivot c1 with
    | Some lit ->
      let lit' = Lit.neg lit in
      if Clause.mem lit' c2 then (
        Clause.(union (remove lit c1) (remove lit' c2))
      ) else (
        Error.failf ~loc:(trsloc loc)
          "cannot resolve: pivot `%a`@ does not occur in `%a`"
          E.pp pivot Clause.pp c2
      )

    | None ->
      Error.failf ~loc:(trsloc loc)
        "cannot resolve %a@ on pivot `%a`" Clause.pp c1 E.pp pivot

  (* do bool paramodulation between [c1] and [c2],
       where [c2] must contain [lhs = rhs] and [c1] must contain [lhs] *)
  and bool_param_on_ ~loc ~lhs ~rhs c1 ~rw_with:c2 : Clause.t =
    Log.debug (fun k->k "(@[bool-param@ :c1 %a@ :c2 %a@ :lhs `%a`@ :rhs `%a`@])"
                  Clause.pp c1 Clause.pp c2 E.pp lhs E.pp rhs);
    (* find if [c2] contains [lhs=rhs] or [rhs=lhs] *)
    match
      Clause.find_lit_by_term ctx lhs c1,
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
      Error.failf ~loc:(trsloc loc)
        "cannot perform bool paramod@ in `%a`:@ it does not contain `%a`"
        Clause.pp c1 K.Expr.pp lhs

    | _, None ->
      Error.failf ~loc:(trsloc loc)
        "cannot do unit-paramod on %a" Clause.pp c2

    | Some lit_lhs, Some lit_eqn ->
      assert (Lit.sign lit_eqn);
      (* preserve sign of the rewritten literal *)
      let new_lit = Lit.make ctx (Lit.sign lit_lhs) rhs in
      Clause.(
        add new_lit @@
        union
          (remove (Lit.make ctx true lhs) c1)
          (remove lit_eqn c2)
      )

  and check_hres_step_ (c1: Clause.t) (step:_ P.hres_step) : Clause.t =
    Profile.with_ "check-hres-step" @@ fun () ->
    let loc = step.loc in
    begin match step.view with
      | P.R {pivot; p} ->
        let pivot = conv_term pivot in
        let c2 = check_proof_rec p in
        res_on_ ~loc ~pivot c1 c2

      | P.R1 p ->
        let c2 = check_proof_rec p in
        let pivot = match Clause.as_singleton c2 with
          | None ->
            Error.failf ~loc:(trsloc loc)
              "r1: clause `%a`@ does not have a unique positive literal"
              Clause.pp c2
          | Some t -> Lit.atom t
        in
        res_on_ ~loc ~pivot c1 c2

      | P.P { lhs; rhs; p } ->
        let lhs = conv_term lhs in
        let rhs = conv_term rhs in
        let c2 = check_proof_rec p in
        bool_param_on_ ~loc ~lhs ~rhs c1 ~rw_with:c2

      | P.P1 p ->
        let c2 = check_proof_rec p in
        let fail() = Error.failf ~loc:(trsloc loc) "cannot do p1 on %a" Clause.pp c2 in
        match Clause.uniq_pos_lit c2 with
        | Some lit ->
          assert (Lit.sign lit);
          begin match E.unfold_eq (Lit.atom lit) with
            | Some (lhs, rhs) -> bool_param_on_ ~loc ~lhs ~rhs c1 ~rw_with:c2
            | None -> fail()
          end
        | None -> fail()
    end

  and check_composite_step_ (step: _ Ast.Proof.composite_step) : Clause.t option =
    let loc = step.loc in
    (* TODO: progress bar *)

    begin match step.view with
    | P.S_define_t (name, u) ->
      let u = conv_term u in
      Hashtbl.add st.named_terms name u;
      None

    | P.S_step_anon { name; proof } ->
      Profile.with_ "check-step" @@ fun () ->

      let@@ () = Error.guard (fun e -> Error.wrapf ~loc:(trsloc loc) "checking step `%s`" name e) in

      begin
        try
          let c = check_proof_rec proof in
          Log.debug (fun k->k"step '%s'@ yields %a" name Clause.pp c);
          Hashtbl.add st.checked name (Ok c);

          Some c
        with
        | Error.E err as exn ->
          Hashtbl.add st.checked name (Error err);
          raise exn
      end

    | P.S_step_c { name; res; proof } ->
      Profile.with_ "check-stepc" @@ fun () ->

      (* first, convert clause declared with this step.
         It is named [name] in [proof]. *)
      let expected_c = conv_lits res in
      Hashtbl.add st.named_clauses name expected_c;

      Log.debug (fun k->k"check step '%s'" name);

      (* check proof, catching errors. We know the expected result
         of this step. *)
      begin
        try
          let@@ () =
            Error.guard
              (fun e ->
                 Error.wrapf ~loc:(trsloc loc) "checking step `%s`@ expected result: %a"
                 name Clause.pp expected_c e)
          in

          let c = check_proof_rec proof in
          Log.debug (fun k->k"step '%s'@ yields %a" name Clause.pp c);

          if not @@ Clause.subset c expected_c then (
            Error.failf ~loc:(trsloc loc)
              "step '%s'@ should yield %a@ but proof returns %a"
              name Clause.pp expected_c Clause.pp c
          );
        with Error.E e ->
          st.bad <- name :: st.bad;
          register_error e
      end;

      (* named clause goes out of scope *)
      Hashtbl.remove st.named_clauses name;
      Hashtbl.add st.checked name (Ok expected_c);

      Some expected_c

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
      let c = E.new_const ctx name [] ty in
      let defe = E.app_eq ctx (E.const ctx c []) rhs in
      let clause = Clause.singleton (Lit.make ctx true defe) in
      Problem.def_const name c clause;
      Some clause
    end

  let check_proof p =
    Profile.with_ "check-proof" @@ fun () ->
    Log.debug (fun k->k"checking proof");
    begin
      try
        let@@ () = Error.guard (Error.wrap "Checking toplevel proof") in
        (* TODO: should it return the empty clause? *)
        ignore (check_proof_rec p: Clause.t);
      with Error.E e ->
        register_error e
    end;
    let ok = st.n_invalid=0 in
    let bad = List.sort String.compare st.bad in
    let errors = Error_list.get_l st.errors in
    ok, bad, errors, {n_invalid=st.n_invalid; n_valid=st.n_valid; n_steps=st.n_steps}
end

let create ctx pb ast_ctx : t =
  let module M = Make(struct let ctx=ctx let problem=pb let ast_ctx = ast_ctx end) in
  (module M)

let check_proof (self: t) (p: Ast.Proof.t) : bool * _ * _ * stats =
  let (module Self) = self in
  Self.check_proof p
