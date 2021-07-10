
(** {1 Parse a problem} *)

open Common

type env = Env.t
type parsed_pb = env

(** {2 Parse a SMTLIB problem} *)
module Smtlib : sig
  val parse_string : K.ctx -> string -> (parsed_pb, string) result

  val parse_file : K.ctx -> string -> (parsed_pb, string) result

  val parse_file_exn : K.ctx -> string -> parsed_pb
end

type syn =
  | Smt2
  [@@deriving show, eq]

(* TODO: parse .cnf files *)

val parse_string : K.ctx -> syn:syn -> string -> (parsed_pb, string) result
(** parse string using given syntax *)

val parse_file : K.ctx -> string -> (parsed_pb, string) result
(** Parse a file, guessing the format based on its extension *)

val parse_file_exn : K.ctx -> string -> parsed_pb
