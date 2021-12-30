
open Common

module A = Ast

module Proof : sig
  val parse_string : ?filename:string -> string -> A.Proof.t
end
