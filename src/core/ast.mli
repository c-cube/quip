
open Common

module Name : sig
  type t = string
  [@@deriving show]
end

module Ty : sig
  type t =
    | Constr of Name.t * t list
    | Arrow of t list * t
  [@@deriving show]
end

type ty = Ty.t

module Var : sig
  type 'ty t = {
    name: Name.t [@main];
    ty: 'ty;
  }
  [@@deriving show, make]
end

module Term : sig
  type t =
    | App of t * t list
    | Fun of Ty.t Var.t * t
    | Var of unit Var.t
    | Ite of t * t * t
    | As of t * Ty.t (* cast *)
    | Let of (unit Var.t * t) list * t
  [@@deriving show]

  val eq : t -> t -> t
  val app_var : unit Var.t -> t list -> t
  val app_name : Name.t -> t list -> t
end

type term = Term.t

module Lit : sig
  type t = {
    sign: bool [@default true];
    atom: term [@main];
  } [@@deriving show, make]

  val a : term -> t
  val na : term -> t
  val eq : term -> term -> t
  val neq : term -> term -> t
  val not : t -> t
end

type lit = Lit.t

module Clause : sig
  type t = lit list [@@deriving show]
end

type clause = Clause.t

type t [@@deriving show]

type hres_step [@@deriving show]
(** hyper-resolution steps: resolution, unit resolution;
    bool paramodulation, unit bool paramodulation *)

val r : t -> pivot:term -> hres_step
(** Resolution step on given pivot term *)

val r1 : t -> hres_step
(** Unit resolution; pivot is obvious *)

val p : t -> lhs:term -> rhs:term -> hres_step
(** Paramodulation using proof whose conclusion has a literal [lhs=rhs] *)

val p1 : t -> hres_step
(** Unit paramodulation *)

type composite_step
val stepc : name:string -> lit list -> t -> composite_step
val deft : term -> term -> composite_step (** define a (new) atomic term *)

val is_trivial_refl : t -> bool
(** is this a proof of [|- t=t]? This can be used to remove
    some trivial steps that would build on the proof (e.g. rewriting
    using [refl t] is useless). *)

val assertion : term -> t
val ref_by_name : string -> t (* named clause, see {!defc} *)
val assertion_c : lit list -> t
val hres_l : t -> hres_step list -> t (* hyper-res *)
val refl : term -> t (* proof of [| t=t] *)
val true_is_true : t (* proof of [|- true] *)
val true_neq_false : t (* proof of [|- not (true=false)] *)
val cc_lemma : lit list -> t
val cc_imply2 : t -> t -> term -> term -> t (* tautology [p1, p2 |- t=u] *)
val cc_imply_l : t list -> term -> term -> t (* tautology [hyps |- t=u] *)
val composite_l : ?assms:(string * lit) list -> composite_step list -> t
val sorry : t
val sorry_c : lit list -> t

val pp_debug : t Fmt.printer

val isa_split : ty -> term list -> t
val isa_disj : ty -> term -> term -> t
val cstor_inj : Name.t -> int -> term list -> term list -> t

val bool_eq : term -> term -> t
val bool_c : lit list -> t
val ite_true : term -> t
val ite_false : term -> t

val lra_l : lit list -> t
