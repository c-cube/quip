
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
    | As of 't * Ty.t (* cast *)
    | Let of (unit Var.t * 't) list * 't
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
  let eq ~loc a b : t = app_name ~loc "=" [a;b]
  let let_ ~loc bs bod : t = mk_ ~loc (Let (bs,bod))
  let fun_ ~loc v bod : t = mk_ ~loc (Fun (v,bod))
  let ite ~loc a b c : t = mk_ ~loc (Ite (a,b,c))

  let rec pp out t = match t.view with
    | Var v -> Var.pp_name out v
    | App (f, l) ->
      Fmt.fprintf out "(@[%a@ %a@])" pp f (pp_l pp) l
    | Ite (a,b,c) -> Fmt.fprintf out "(@[ite@ %a@ %a@ %a@])" pp a pp b pp c
    | Let (bs, bod) ->
      let ppb out (v,t) = Fmt.fprintf out "(@[%a@ %a@])" Var.pp_name v pp t in
      Fmt.fprintf out "(@[let@ (@[%a@]@ %a@])" (pp_l ppb) bs pp bod
    | Fun (v,t) ->
      Fmt.fprintf out "(@[lambda %a@ %a@])" (Var.pp Ty.pp) v pp t
    | As (t,ty) -> Fmt.fprintf out "(@[as@ %a@ %a@])" pp t Ty.pp ty

  let show = Fmt.to_string pp
end

type term = Term.t [@@deriving show]

type with_bindings = (Name.t * term) list [@@deriving show]

module Subst = struct
  type t = (unit Var.t * Term.t) list
  [@@deriving show]
end

module Lit = struct
  type t = {
    sign: bool [@default true];
    atom: term [@main];
  } [@@deriving make]

  let not l = {l with sign=not l.sign}

  let pp out l =
    let s = if l.sign then "+" else "-" in
    Fmt.fprintf out "(@[%s %a@])" s Term.pp l.atom
  let show = Fmt.to_string pp

  let a t = make ~sign:true t
  let na t = make ~sign:false t
end

type lit = Lit.t [@@deriving show]

module Clause = struct
  type t =
    | Clause of lit list
    | Clause_ref of Name.t
  let pp out (c:t) =
    match c with
    | Clause lits ->
      Fmt.fprintf out "(@[cl@ %a@])" Fmt.(list ~sep:(return "@ ") Lit.pp) lits
    | Clause_ref n -> Fmt.fprintf out "(@[@@ %s@])" n
  let show = Fmt.to_string pp
end

type clause = Clause.t [@@deriving show]

module Proof = struct
  type view =
    | Sorry (* NOTE: v. bad as we don't even specify the return *)
    | Sorry_c of clause (* TODO: also specify parents, so we still know the DAG *)
    | Named of string (* refers to previously defined clause *)
    | Refl of term
    | CC_lemma_imply of t list * term * term
    | CC_lemma of clause
    | Assert of term
    | Assert_c of clause
    | Hres of t * hres_step list
    | Res of { pivot: term; p1: t; p2: t }
    | Res1 of { p1: t; p2: t }
    | Subst of Subst.t * t
    | DT_isa_split of ty * term list
    | DT_isa_disj of ty * term * term
    | DT_cstor_inj of Name.t * int * term list * term list (* [c t…=c u… |- t_i=u_i] *)
    | Bool_true_is_true
    | Bool_true_neq_false
    | Bool_eq of term * term (* equal by pure boolean reasoning *)
    | Bool_c of bool_c_name * term list (* boolean tautology *)
    | Nn of t
    | Ite_true of term (* given [if a b c] returns [a=T |- if a b c=b] *)
    | Ite_false of term
    | LRA of clause
    | With of with_bindings * t
    | Composite of {
        (* some named (atomic) assumptions *)
        assumptions: (string * lit) list;
        steps: composite_step array; (* last step is the proof *)
      }
  [@@deriving show {with_path=false}]

  and bool_c_name =
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

  and t=view

  and composite_step =
    | S_step_c of {
        name: string; (* name *)
        res: lit list; (* result of [proof] *)
        proof: t; (* sub-proof *)
      }
    | S_define_t of string * term (* [const := t] *)
  [@@deriving show {with_path=false}]

    (* TODO: be able to name clauses, to be expanded at parsing.
       note that this is not the same as [S_step_c] which defines an
       explicit step with a conclusion and proofs that can be exploited
       separately.

       We could introduce that in Compress.rename…

    | S_define_c of string * clause (* [name := c] *)
     *)

  and hres_step =
    | R of { pivot: term; p: t}
    | R1 of t
    | P of { lhs: term; rhs: term; p: t}
    | P1 of t
  [@@deriving show]

  let[@inline] view p = p

  let r p ~pivot : hres_step = R { pivot; p }
  let r1 p = R1 p
  let p p ~lhs ~rhs : hres_step = P { p; lhs; rhs }
  let p1 p = P1 p

  let stepc ~name res proof : composite_step = S_step_c {proof;name;res}
  let deft c rhs : composite_step = S_define_t (c,rhs)

  let is_trivial_refl = function
    | Refl _ -> true
    | _ -> false

  let sorry_c c = Sorry_c c
  let sorry = Sorry
  let refl t : t = Refl t
  let ref_by_name name : t = Named name
  let cc_lemma c : t = CC_lemma c
  let cc_imply_l l t u : t = CC_lemma_imply (l, t, u)
  let cc_imply2 h1 h2 t u : t = CC_lemma_imply ([h1; h2], t, u)
  let assertion t = Assert t
  let assertion_c c = Assert_c c
  let composite_a ?(assms=[]) steps : t =
    Composite {assumptions=assms; steps}
  let composite_l ?(assms=[]) steps : t =
    Composite {assumptions=assms; steps=Array.of_list steps}

  let with_ bs p : t = With (bs,p)

  let isa_split ty l = DT_isa_split (ty, l)
  let isa_disj ty t u = DT_isa_disj (ty, t, u)
  let cstor_inj c i t u = DT_cstor_inj (c, i, t, u)

  let ite_true t = Ite_true t
  let ite_false t = Ite_false t
  let true_is_true : t = Bool_true_is_true
  let true_neq_false : t = Bool_true_neq_false
  let bool_eq a b : t = Bool_eq (a,b)
  let bool_c name c : t = Bool_c (name, c)
  let nn p : t = Nn p

  let hres_l c l : t = Hres (c,l)
  let res ~pivot p1 p2 : t = Res{pivot;p1;p2}
  let res1 p1 p2 : t = Res1{p1;p2}
  let subst s p : t = Subst(s,p)

  let lra_l c : t = LRA c

  (* TODO: expose? *)
  let iter_lit ~f_t lit = f_t lit.Lit.atom

  (* TODO: expose? *)
  let iter_p (p:t) ~f_t ~f_step ~f_clause ~f_p : unit =
    match p with
    | Sorry -> ()
    | Sorry_c c -> f_clause c
    | Named _ -> ()
    | Refl t -> f_t t
    | CC_lemma_imply (ps, t, u) -> List.iter f_p ps; f_t t; f_t u
    | CC_lemma c | Assert_c c -> f_clause c
    | Assert t -> f_t t
    | Hres (i, l) ->
      f_p i;
      List.iter
        (function
          | R1 p -> f_p p
          | P1 p -> f_p p
          | R {pivot;p} -> f_p p; f_t pivot
          | P {lhs;rhs;p} -> f_p p; f_t lhs; f_t rhs)
        l
    | Res {pivot;p1;p2} -> f_t pivot; f_p p1; f_p p2
    | Res1 {p1;p2} -> f_p p1; f_p p2
    | Subst (s,p) -> List.iter (fun (_v,t) -> f_t t) s; f_p p;
    | DT_isa_split (_, l) -> List.iter f_t l
    | DT_isa_disj (_, t, u) -> f_t t; f_t u
    | DT_cstor_inj (_, _c, ts, us) -> List.iter f_t ts; List.iter f_t us
    | Bool_true_is_true | Bool_true_neq_false -> ()
    | Bool_eq (t, u) -> f_t t; f_t u
    | Bool_c (_, ts) -> List.iter f_t ts
    | Nn p -> f_p p
    | Ite_true t | Ite_false t -> f_t t
    | LRA c -> f_clause c
    | With (bs,p) -> List.iter (fun (_,t) -> f_t t) bs; f_p p
    | Composite { assumptions; steps } ->
      List.iter (fun (_,lit) -> iter_lit ~f_t lit) assumptions;
      Array.iter f_step steps;
      ()

  let pp_debug = pp
end
