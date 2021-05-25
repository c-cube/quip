
(** {1 Parse a problem} *)

open Common
type pb = Parsed_pb.t

(** {2 Parse a SMTLIB problem} *)
module Smtlib : sig
  val parse_file : K.ctx -> string -> (pb, string) result

  val parse_file_exn : K.ctx -> string -> pb
end

val parse_file : K.ctx -> string -> (pb, string) result
(** Parse a file, guessing the format based on its extension *)

val parse_file_exn : K.ctx -> string -> pb
