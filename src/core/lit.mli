(** Literals *)

open Common

module K = Kernel
module E = Kernel.Expr

type t [@@deriving show, eq, ord]
val pp_depth : ?max_depth:int -> t Fmt.printer
val neg : t -> t
val sign : t -> bool
val atom : t -> E.t
val to_expr : K.ctx -> t -> E.t
val as_eqn : t -> (E.t * E.t) option
val make : K.ctx -> bool -> E.t -> t

module Set : CCSet.S with type elt = t
