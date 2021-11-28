
open Common

module Name = struct
  type t = string
  let pp out s = Fmt.string out s
  let show s = s
end

module Ty = struct
  type t =
    | Constr of Name.t * t list
    | Arrow of t list * t
  [@@deriving show]

  let constr name args : t = Constr(name,args)
  let arrow args ret : t = Arrow (args,ret)
end

type ty = Ty.t [@@deriving show]

module Var = struct
  type 'ty t = {
    name: Name.t [@main];
    ty: 'ty;
  }
  [@@deriving make, map, fold, iter]

  let pp pp_ty out v = Fmt.fprintf out "(@[%a : %a@])" Name.pp v.name pp_ty v.ty
  let show pp_ty v = Fmt.to_string (pp pp_ty) v
  let pp_name out v = Name.pp out v.name
end

let pp_l pp out l = Fmt.(list ~sep:(return "@ ") pp) out l

module Term = struct
  type ('t,'ty) view =
    | App of 't * 't list
    | Fun of 'ty Var.t * 't
    | Var of 'ty option Var.t
    | Ite of 't * 't * 't
    | Not of 't
    | As of 't * Ty.t (* cast *)
    | Let of (unit Var.t * 't) list * 't
    | Ref of string
  [@@deriving show, map, fold, iter]

  type t = {
    view: (t, Ty.t) view;
    loc: Loc.t option;
  }

  let[@inline] mk_ ~loc view : t = {loc; view}
  let[@inline] view t = t.view
  let[@inline] loc t = t.loc

  let map_shallow f t =
    {t with view=map_view f (fun ty->ty) t.view}

  let var ~loc v = mk_ ~loc (Var v)
  let app_var ~loc v l : t =
    let v = var ~loc v in
    if l=[] then v else mk_ ~loc (App (v, l))
  let app_name ~loc v l : t = app_var ~loc (Var.make ~ty:None v) l
  let const ~loc c = app_name ~loc c []
  let not ~loc u = match u.view with
    | Not v -> v
    | _ -> mk_ ~loc (Not u)
  let eq ~loc a b : t = app_name ~loc "=" [a;b]
  let let_ ~loc bs bod : t = mk_ ~loc (Let (bs,bod))
  let fun_ ~loc v bod : t = mk_ ~loc (Fun (v,bod))
  let ite ~loc a b c : t = mk_ ~loc (Ite (a,b,c))
  let ref ~loc s : t = mk_ ~loc (Ref s)

  let rec rw ~(rule:t -> t option) (self:t) : t =
    match rule self with
    | Some u -> rw ~rule u
    | None ->
      {self with view=map_view (rw ~rule) (fun ty->ty) self.view}

  let rec pp out t = match t.view with
    | Var v -> Var.pp_name out v
    | App (f, l) ->
      Fmt.fprintf out "(@[%a@ %a@])" pp f (pp_l pp) l
    | Ite (a,b,c) -> Fmt.fprintf out "(@[ite@ %a@ %a@ %a@])" pp a pp b pp c
    | Not u -> Fmt.fprintf out "(@[@<1>¬@ %a@])" pp u
    | Let (bs, bod) ->
      let ppb out (v,t) = Fmt.fprintf out "(@[%a@ %a@])" Var.pp_name v pp t in
      Fmt.fprintf out "(@[let@ (@[%a@]@ %a@])" (pp_l ppb) bs pp bod
    | Fun (v,t) ->
      Fmt.fprintf out "(@[lambda %a@ %a@])" (Var.pp Ty.pp) v pp t
    | As (t,ty) -> Fmt.fprintf out "(@[as@ %a@ %a@])" pp t Ty.pp ty
    | Ref s -> Fmt.fprintf out "(@[@@ %s@])" s

  let show = Fmt.to_string pp
end

type term = Term.t [@@deriving show]

type with_bindings = (Name.t * term) list [@@deriving show]

module Subst = struct
  type t = (unit Var.t * Term.t) list
  [@@deriving show]
end

module Clause = struct
  type t =
    | Clause of term list
    | Clause_ref of Name.t
  let pp out (c:t) =
    match c with
    | Clause lits ->
      Fmt.fprintf out "(@[cl@ %a@])" Fmt.(list ~sep:(return "@ ") Term.pp) lits
    | Clause_ref n -> Fmt.fprintf out "(@[@@ %s@])" n
  let show = Fmt.to_string pp
end

type clause = Clause.t [@@deriving show]

module Proof = struct
  type bool_c_name =
    | And_i
    | And_e
    | Or_i
    | Or_e
    | Not_i
    | Not_e
    | Imp_i
    | Imp_e
    | Eq_i
    | Eq_e
    | Xor_i
    | Xor_e
  [@@deriving show {with_path=false}]

  type 'proof hres_step =
    | R of { pivot: term; p: 'proof}
    | R1 of 'proof
    | P of { lhs: term; rhs: term; p: 'proof}
    | P1 of 'proof
  [@@deriving show {with_path=false}, map, iter]

  type 'proof composite_step =
    | S_step_c of {
        name: string; (* name *)
        res: term list; (* result of [proof] *)
        proof: 'proof; (* sub-proof *)
      }
    | S_define_t of string * term (* [const := t] *)
    | S_declare_ty_const of {
        name: string;
        arity: int;
      }
    | S_declare_const of {
        name: string;
        ty: Ty.t;
      }
    | S_define_const of {
        name: string;
        ty: Ty.t;
        rhs: term;
      }
  [@@deriving show {with_path=false}, map, iter]

  type ('term, 'clause, 'proof) view =
    | Sorry (* NOTE: v. bad as we don't even specify the return *)
    | Sorry_c of 'clause (* TODO: also specify parents, so we still know the DAG *)
    | Named of string (* refers to previously defined 'clause *)
    | Refl of 'term
    | CC_lemma_imply of 'proof list * 'term * 'term
    | CC_lemma of 'clause
    | Clause_rw of {
        res: 'clause;
        c0: 'proof;
        using: 'proof list; (** the rewriting equations/atoms *)
      }
    | Assert of 'term
    | Assert_c of 'clause
    | Rup_res of 'clause * 'proof list
    | Hres of 'proof * 'proof hres_step list
    | Res of { pivot: 'term; p1: 'proof; p2: 'proof }
    | Res1 of { p1: 'proof; p2: 'proof }
    | Paramod1 of { rw_with: 'proof; p: 'proof}
    | Subst of Subst.t * 'proof
    | DT_isa_split of ty * 'term list
    | DT_isa_disj of ty * 'term * 'term
    | DT_cstor_inj of Name.t * int * 'term list * 'term list (* [c 'proof…=c u… |- t_i=u_i] *)
    | Bool_true_is_true
    | Bool_true_neq_false
    | Bool_eq of 'term * 'term (* equal by pure boolean reasoning *)
    | Bool_c of bool_c_name * 'term list (* boolean tautology *)
    | Ite_true of 'term (* given [if a b c] returns [a=T |- if a b c=b] *)
    | Ite_false of 'term
    | LRA of 'clause
    | With of with_bindings * 'proof
    | Composite of {
        (* some named (atomic) assumptions *)
        assumptions: (string * 'term) list;
        steps: 'proof composite_step array; (* last step is the proof *)
      }
  [@@deriving show {with_path=false}, map, iter]

  type t = {view: (term, clause, t) view}
  [@@unboxed]
  [@@deriving show {with_path=false} ]

  let[@inline] view p = p.view

  let r p ~pivot : _ hres_step = R { pivot; p }
  let r1 p = R1 p
  let p p ~lhs ~rhs : _ hres_step = P { p; lhs; rhs }
  let p1 p = P1 p

  let stepc ~name res proof : _ composite_step = S_step_c {proof;name;res}
  let deft c rhs : _ composite_step = S_define_t (c,rhs)
  let decl_const name ty : _ composite_step = S_declare_const {name;ty}
  let decl_ty_const name arity : _ composite_step = S_declare_ty_const {name;arity}
  let define_const name ty rhs : _ composite_step = S_define_const {name;ty;rhs}

  let is_trivial_refl = function
    | {view=Refl _;_} -> true
    | _ -> false

  let[@inline] mk view : t = {view}
  let sorry_c c : t = mk @@ Sorry_c c
  let sorry = mk @@ Sorry
  let refl t : t = mk @@ Refl t
  let ref_by_name name : t = mk @@ Named name
  let cc_lemma c : t = mk @@ CC_lemma c
  let cc_imply_l l t u : t = mk @@ CC_lemma_imply (l, t, u)
  let cc_imply2 h1 h2 t u : t = mk @@ CC_lemma_imply ([h1; h2], t, u)
  let assertion t = mk @@ Assert t
  let assertion_c c = mk @@ Assert_c c
  let composite_l ?(assms=[]) steps : t =
    mk @@ Composite {assumptions=assms; steps=Array.of_list steps}

  let with_ bs p : t = mk @@ With (bs,p)

  let isa_split ty l = mk @@ DT_isa_split (ty, l)
  let isa_disj ty t u = mk @@ DT_isa_disj (ty, t, u)
  let cstor_inj c i t u = mk @@ DT_cstor_inj (c, i, t, u)

  let ite_true t = mk @@ Ite_true t
  let ite_false t = mk @@ Ite_false t
  let true_is_true : t = mk @@ Bool_true_is_true
  let true_neq_false : t = mk @@ Bool_true_neq_false
  let bool_eq a b : t = mk @@ Bool_eq (a,b)
  let bool_c name c : t = mk @@ Bool_c (name, c)

  let rup_res c hyps : t = mk @@ Rup_res (c, hyps)
  let clause_rw ~res ~using c0 : t = mk @@ Clause_rw {res; using; c0}
  let paramod1 ~rw_with p : t = mk @@ Paramod1 {rw_with; p}

  let hres_l c l : t = mk @@ Hres (c,l)
  let res ~pivot p1 p2 : t = mk @@ Res{pivot;p1;p2}
  let res1 p1 p2 : t = mk @@ Res1{p1;p2}
  let subst s p : t = mk @@ Subst(s,p)

  let lra_l c : t = mk @@ LRA c

  let pp_debug = pp
end
