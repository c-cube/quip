
open Common

(* TODO: structured name? like SMTLIB's composite identifiers *)
module Name : sig
  type t = string
  [@@deriving show]
end

module Ty : sig
  type t =
    | Constr of Name.t * t list
    | Arrow of t list * t
  [@@deriving show]

  val constr : Name.t -> t list -> t
  val arrow : t list -> t -> t
end

type ty = Ty.t

module Var : sig
  type 'ty t = {
    name: Name.t [@main];
    ty: 'ty;
  }
  [@@deriving show, make]
  val pp_name : _ t Fmt.printer
end

module Term : sig
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

  type t
  [@@deriving show]

  val view : t -> (t, Ty.t) view
  val loc : t -> Loc.t
  val map_shallow : (t -> t) -> t -> t

  (** Rewrite a term with the given function *)
  val rw : rule:(t -> t option) -> t -> t

  val ref : loc:Loc.t -> string -> t
  val var : loc:Loc.t -> Ty.t option Var.t -> t
  val eq : loc:Loc.t -> t -> t -> t
  val not: loc:Loc.t -> t -> t
  val app_var : loc:Loc.t -> Ty.t option Var.t -> t list -> t
  val app_name : loc:Loc.t -> Name.t -> t list -> t
  val const : loc:Loc.t -> Name.t -> t
  val let_ : loc:Loc.t -> (unit Var.t * t) list -> t -> t
  val fun_ : loc:Loc.t -> Ty.t Var.t -> t -> t
  val ite : loc:Loc.t -> t -> t -> t -> t
end

type term = Term.t

type with_bindings = (Name.t * term) list

module Subst : sig
  type t = (unit Var.t * Term.t) list
  [@@deriving show]
end

module Clause : sig
  type t =
    | Clause of term list
    | Clause_ref of Name.t
  [@@deriving show]
end

type clause = Clause.t

module Proof : sig
  type t [@@deriving show]

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

  val view : t -> (term,clause,t) view

  val r : t -> pivot:term -> t hres_step
  (** Resolution step on given pivot term *)

  val r1 : t -> t hres_step
  (** Unit resolution; pivot is obvious *)

  val p : t -> lhs:term -> rhs:term -> t hres_step
  (** Paramodulation using proof whose conclusion has a literal [lhs=rhs] *)

  val p1 : t -> t hres_step
  (** Unit paramodulation *)

  val stepc : name:string -> term list -> t -> t composite_step

  val deft : string -> term -> t composite_step (** define a (new) atomic term *)

  val decl_const : string -> Ty.t -> t composite_step

  val decl_ty_const : string -> int -> t composite_step

  val define_const : string -> Ty.t -> term -> t composite_step

  val is_trivial_refl : t -> bool
  (** is this a proof of [|- t=t]? This can be used to remove
      some trivial steps that would build on the proof (e.g. rewriting
      using [refl t] is useless). *)

  val assertion : term -> t
  val ref_by_name : string -> t (* named clause, see {!defc} *)
  val assertion_c : Clause.t -> t
  val hres_l : t -> t hres_step list -> t (* hyper-res *)
  val res : pivot:term -> t -> t -> t
  val res1 : t -> t -> t
  val subst : Subst.t -> t -> t
  val refl : term -> t (* proof of [| t=t] *)
  val true_is_true : t (* proof of [|- true] *)
  val true_neq_false : t (* proof of [|- not (true=false)] *)
  val cc_lemma : Clause.t -> t
  val cc_imply2 : t -> t -> term -> term -> t (* tautology [p1, p2 |- t=u] *)
  val cc_imply_l : t list -> term -> term -> t (* tautology [hyps |- t=u] *)
  val composite_l : ?assms:(string * term) list -> t composite_step list -> t
  val rup_res : clause -> t list -> t
  val paramod1 : rw_with:t -> t -> t
  val clause_rw : res:clause -> using:t list -> t -> t
  val sorry : t
  val sorry_c : Clause.t -> t

  val with_ : with_bindings -> t -> t

  val pp_debug : t Fmt.printer

  val isa_split : ty -> term list -> t
  val isa_disj : ty -> term -> term -> t
  val cstor_inj : Name.t -> int -> term list -> term list -> t

  val bool_eq : term -> term -> t
  val bool_c : bool_c_name -> term list -> t
  val ite_true : term -> t
  val ite_false : term -> t

  val lra_l : Clause.t -> t
end
