
(** {1 Positions}

    A position in a string. Line and column are 1-based, so that compatibility
    with LSP is easier. *)

open Common

type t = {
  line: int;
  col: int;
} [@@deriving show]

val none : t
val make : line:int -> col:int -> t

val (<=) : t -> t -> bool
val (<) : t -> t -> bool
val (=) : t -> t -> bool
val min : t -> t -> t
val max : t -> t -> t
