
open Common

module Name = struct
  type t = string
  [@@deriving show]
end

module Ty = struct
  type t =
    | Constr of Name.t * t list
    | Arrow of t list * t
  [@@deriving show]
end

type ty = Ty.t [@@deriving show]

module Var = struct
  type 'ty t = {
    name: Name.t [@main];
    ty: 'ty;
  }
  [@@deriving show, make]
end

module Term = struct
  type t =
    | App of t * t list
    | Fun of Ty.t Var.t * t
    | Var of unit Var.t
    | Ite of t * t * t
    | As of t * Ty.t (* cast *)
    | Let of (unit Var.t * t) list * t
  [@@deriving show]

  let app_var v l : t = App (Var v, l)
  let app_name v l : t = app_var (Var.make ~ty:() v) l
  let eq a b : t = app_name "=" [a;b]
end

type term = Term.t [@@deriving show]

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
  let eq t u = a (Term.eq t u)
  let neq t u = na (Term.eq t u)
end

type lit = Lit.t [@@deriving show]

module Clause = struct
  type t = lit list
  let pp out (c:t) =
    Fmt.fprintf out "(@[cl@ %a@])" Fmt.(list ~sep:(return "@ ") Lit.pp) c
  let show = Fmt.to_string pp
end

type clause = Clause.t [@@deriving show]

type t =
  | Unspecified
  | Sorry (* NOTE: v. bad as we don't even specify the return *)
  | Sorry_c of clause
  | Named of string (* refers to previously defined clause *)
  | Refl of term
  | CC_lemma_imply of t list * term * term
  | CC_lemma of clause
  | Assertion of term
  | Assertion_c of clause
  | Hres of t * hres_step list
  | DT_isa_split of ty * term list
  | DT_isa_disj of ty * term * term
  | DT_cstor_inj of Name.t * int * term list * term list (* [c t…=c u… |- t_i=u_i] *)
  | Bool_true_is_true
  | Bool_true_neq_false
  | Bool_eq of term * term (* equal by pure boolean reasoning *)
  | Bool_c of clause (* boolean tautology *)
  | Ite_true of term (* given [if a b c] returns [a=T |- if a b c=b] *)
  | Ite_false of term
  | LRA of clause
  | Composite of {
      (* some named (atomic) assumptions *)
      assumptions: (string * lit) list;
      steps: composite_step array; (* last step is the proof *)
    }
[@@deriving show]

and composite_step =
  | S_step_c of {
      name: string; (* name *)
      res: clause; (* result of [proof] *)
      proof: t; (* sub-proof *)
    }
  | S_define_t of term * term (* [const := t] *)
  | S_define_t_name of string * term (* [const := t] *)
[@@deriving show]

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

let r p ~pivot : hres_step = R { pivot; p }
let r1 p = R1 p
let p p ~lhs ~rhs : hres_step = P { p; lhs; rhs }
let p1 p = P1 p

let stepc ~name res proof : composite_step = S_step_c {proof;name;res}
let deft c rhs : composite_step = S_define_t (c,rhs)
let deft_name c rhs : composite_step = S_define_t_name (c,rhs)

let is_trivial_refl = function
  | Refl _ -> true
  | _ -> false

let default=Unspecified
let sorry_c c = Sorry_c c
let sorry = Sorry
let refl t : t = Refl t
let ref_by_name name : t = Named name
let cc_lemma c : t = CC_lemma c
let cc_imply_l l t u : t = CC_lemma_imply (l, t, u)
let cc_imply2 h1 h2 t u : t = CC_lemma_imply ([h1; h2], t, u)
let assertion t = Assertion t
let assertion_c c = Assertion_c c
let composite_a ?(assms=[]) steps : t =
  Composite {assumptions=assms; steps}
let composite_l ?(assms=[]) steps : t =
  Composite {assumptions=assms; steps=Array.of_list steps}

let isa_split ty l = DT_isa_split (ty, l)
let isa_disj ty t u = DT_isa_disj (ty, t, u)
let cstor_inj c i t u = DT_cstor_inj (c, i, t, u)

let ite_true t = Ite_true t
let ite_false t = Ite_false t
let true_is_true : t = Bool_true_is_true
let true_neq_false : t = Bool_true_neq_false
let bool_eq a b : t = Bool_eq (a,b)
let bool_c c : t = Bool_c c

let hres_l c l : t = Hres (c,l)

let lra_l c : t = LRA c

(* TODO: expose? *)
let iter_lit ~f_t lit = f_t lit.Lit.atom

(* TODO: expose? *)
let iter_p (p:t) ~f_t ~f_step ~f_clause ~f_p : unit =
  match p with
  | Unspecified | Sorry -> ()
  | Sorry_c c -> f_clause c
  | Named _ -> ()
  | Refl t -> f_t t
  | CC_lemma_imply (ps, t, u) -> List.iter f_p ps; f_t t; f_t u
  | CC_lemma c | Assertion_c c -> f_clause c
  | Assertion t -> f_t t
  | Hres (i, l) ->
    f_p i;
    List.iter
      (function
        | R1 p -> f_p p
        | P1 p -> f_p p
        | R {pivot;p} -> f_p p; f_t pivot
        | P {lhs;rhs;p} -> f_p p; f_t lhs; f_t rhs)
      l
  | DT_isa_split (_, l) -> List.iter f_t l
  | DT_isa_disj (_, t, u) -> f_t t; f_t u
  | DT_cstor_inj (_, _c, ts, us) -> List.iter f_t ts; List.iter f_t us
  | Bool_true_is_true | Bool_true_neq_false -> ()
  | Bool_eq (t, u) -> f_t t; f_t u
  | Bool_c c -> f_clause c
  | Ite_true t | Ite_false t -> f_t t
  | LRA c -> f_clause c
  | Composite { assumptions; steps } ->
    List.iter (fun (_,lit) -> iter_lit ~f_t lit) assumptions;
    Array.iter f_step steps;
    ()

let pp_debug = pp
