
open Common

module K = Kernel
module E = K.Expr

type t [@@deriving show, eq]
val pp_depth: max_depth:int -> t Fmt.printer

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

val subst : K.ctx -> recursive:bool -> t -> K.Subst.t -> t
val lits : t -> Lit.t Iter.t

val pos_lits : t -> Lit.t Iter.t
val neg_lits : t -> Lit.t Iter.t
val pos_lits_list : t -> Lit.t list
val neg_lits_list : t -> Lit.t list

val find_lit_by_term : K.ctx -> E.t -> t -> Lit.t option
(** [find_lit_by_term e c] finds a literal of [c] with atom [e],
    or [None] *)

val as_singleton : t -> Lit.t option
(** [as_singleton (singleton lit)] is [Some lit]. For non unary
    clauses it returns [None]. *)

val uniq_pos_lit : t -> Lit.t option
(** [uniq_pos_lit c] returns the unique positive literal of [c] if
    [c] contains exactly one positive literal. Otherwise, returns [None] *)

val uniq_neg_lit : t -> Lit.t option

val lits_list : t -> Lit.t list
