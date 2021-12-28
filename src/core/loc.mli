
(** {1 Locations}

    A location is a range between two positions in a string (a source file).
*)

module Fmt = CCFormat

module Input : sig
  type t
  val string : string -> t
  val file : string -> t
end

type ctx = {
  file: string;
  input: Input.t;
} [@@deriving show]

type t = {
  ctx: ctx;
  start: Position.t;
  stop: Position.t;
} [@@deriving show]

val mk : ctx:ctx -> int -> int -> int -> int -> t
val mk_pair : ctx:ctx -> int*int -> int*int -> t

val of_lexbuf : input:Input.t -> Lexing.lexbuf -> t

val pp_compact : t Fmt.printer
val pp_opt : t option Fmt.printer
val none : t

val union : t -> t -> t
val union_l : t list -> t option

val contains : t -> Position.t -> bool

val pp_l : t list Fmt.printer
(** Print list of locations *)

(**/**)
val set_file : Lexing.lexbuf -> string -> unit
(**/**)
