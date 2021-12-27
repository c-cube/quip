
(** {1 Kernel of trust} *)

open Common

type ctx
type expr
type ty = expr
type const
type ty_const = const

type location = Loc.t

type var = {
  v_name: string;
  v_ty: ty;
}
type ty_var = var

type bvar = {
  bv_idx: int;
  bv_ty: ty;
}

type expr_view =
  | E_kind
  | E_type
  | E_var of var
  | E_bound_var of bvar
  | E_const of const * expr list
  | E_app of expr * expr
  | E_lam of string * expr * expr
  | E_not of expr
  | E_arrow of expr * expr

module Name : sig
  type t
  val equal_str : t -> string -> bool
  include EQ with type t := t
  include COMPARE with type t := t
  include HASH with type t := t
  include PP with type t := t
end

module Const : sig
  type t = const
  include EQ with type t := t
  include PP with type t := t

  val def_loc : t -> location option

  type args =
    | C_ty_vars of ty_var list
    | C_arity of int

  val name : t -> Name.t
  val args : t -> args
  val ty : t -> ty

  val pp_args : args Fmt.printer
  val pp_with_ty : t Fmt.printer

  val eq : ctx -> t
  val bool : ctx -> t
  val select : ctx -> t
  (** Choice constant *)

  val is_eq_to_bool : t -> bool
  val is_eq_to_eq : t -> bool
end

(** {2 Free Variables} *)
module Var : sig
  type t = var

  val name : t -> string
  val ty : t -> ty
  val make : string -> ty -> t
  val makef : ('a, Format.formatter, unit, t) format4 -> ty -> 'a
  val map_ty : t -> f:(ty -> ty) -> t

  include EQ with type t := t
  include HASH with type t := t
  include COMPARE with type t := t
  include PP with type t := t
  val pp_with_ty : t Fmt.printer

  module Set : CCSet.S with type elt = t
  module Map : CCMap.S with type key = t
  module Tbl : CCHashtbl.S with type key = t
end

(** Bound variables *)
module BVar : sig
  type t = bvar
  val make : int -> ty -> t
  include PP with type t := t
end

(** Substitutions *)
module Subst : sig
  type t
  include PP with type t := t
  val find_exn : var -> t -> expr
  val empty : t
  val is_empty : t -> bool
  val is_renaming : t -> bool
  val mem : var -> t -> bool
  val bind : t -> var -> expr -> t
  val bind' : var -> expr -> t -> t
  val size : t -> int
  val to_iter : t -> (var * expr) Iter.t
  val of_list : (var * expr) list -> t
  val of_iter : (var * expr) Iter.t -> t
end

(** {2 Expressions and Types} *)

(** Expression API.

    This module type is parametrized by a ['a with_ctx] type
    which is typically either [ctx -> 'a] (when the context is explicit)
    or just ['a] (when the context is in scope). Intuitively ['a with_ctx]
    is just how we express that a function depends on the context. *)
module type EXPR = sig
  type t = expr

  type view = expr_view =
    | E_kind
    | E_type
    | E_var of var
    | E_bound_var of bvar
    | E_const of const * t list
    | E_app of t * t
    | E_lam of string * expr * expr
    | E_not of expr
    | E_arrow of expr * expr

  include EQ with type t := t
  include HASH with type t := t
  include COMPARE with type t := t
  include PP with type t := t

  val pp_depth : max_depth:int -> t Fmt.printer
  (** Print the term and insert ellipsis in subterms above given depth.
      Useful to print very deep terms *)

  val view : t -> view
  val ty : t -> ty option
  val ty_exn : t -> ty
  val is_closed : t -> bool
  val is_eq_to_type : t -> bool
  val is_eq_to_bool : t -> bool
  val is_a_bool : t -> bool
  val is_a_type : t -> bool
  (** Is the type of [e] equal to [Type]? *)

  val iter : f:(bool -> t -> unit) -> t -> unit
  (** [iter ~f e] calls [f] on immediate subterms of [e].
      It calls [f true u] if [u] is an immediate subterm under a binder,
      and [f false u] otherwise. *)

  val exists : f:(bool -> t -> bool) -> t -> bool
  val for_all : f:(bool -> t -> bool) -> t -> bool

  val contains : t -> sub:t -> bool
  val free_vars : ?init:Var.Set.t -> t -> Var.Set.t
  val free_vars_iter : t -> var Iter.t

  val unfold_app : t -> t * t list
  val unfold_eq : t -> (t * t) option
  val unfold_arrow : t -> t list * t
  val unfold_not : t -> t option

  val return_ty : t -> t
  val as_const : t -> (Const.t * ty list) option
  val as_const_exn : t -> Const.t * ty list

  module Set : CCSet.S with type elt = t
  module Map : CCMap.S with type key = t
  module Tbl : CCHashtbl.S with type key = t

  val iter_dag : f:(t -> unit) -> t -> unit
  (** [iter_dag ~f e] calls [f] once on each unique subterm of [e]. *)

  type 'a with_ctx

  val subst : (recursive:bool -> t -> Subst.t -> t) with_ctx

  val type_ : t with_ctx
  val bool : t with_ctx
  val eq : (ty -> t) with_ctx
  val select : (ty -> t) with_ctx
  val var : (var -> t) with_ctx
  val const : (const -> ty list -> t) with_ctx
  val new_const : (?def_loc:location -> string -> ty_var list -> ty -> const) with_ctx
  val new_ty_const : (?def_loc:location -> string -> int -> const) with_ctx
  val var_name : (string -> ty -> t) with_ctx
  val bvar : (int -> ty -> t) with_ctx
  val app : (t -> t -> t) with_ctx
  val app_l : (t -> t list -> t) with_ctx
  val app_eq : (t -> t -> t) with_ctx
  val lambda : (var -> t -> t) with_ctx
  val lambda_l : (var list -> t -> t) with_ctx
  val lambda_db : (name:string -> ty_v:ty -> t -> t) with_ctx
  val arrow : (t -> t -> t) with_ctx
  val arrow_l : (t list -> t -> t) with_ctx
  val not_ : (t -> t) with_ctx

  val map : (f:(bool -> t -> t) -> t -> t) with_ctx

  val db_shift: (t -> int -> t) with_ctx

  val open_lambda : (t -> (var * t) option) with_ctx
  (** [open_lambda (\x. t)] introduces a new free variable [y],
      and returns [Some (y, t[x := y])]. Otherwise it returns [None] *)

  val open_lambda_exn : (t -> var * t) with_ctx
  (** Unsafe version of {!open_lambda}.
      @raise Error.Error if the term is not a lambda. *)
end

(** Explicit expression API with context *)
module Expr : EXPR with type 'a with_ctx := (ctx -> 'a)


(** {2 Context}

    The context is storing the term state, list of axioms,
    and other parameters.
    Terms from distinct contexts must never be mixed. *)
module Ctx : sig
  type t = ctx

  val create : unit -> t
end


(**/**)
val __pp_ids: bool ref
(**/**)
