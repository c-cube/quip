
open Common

module A = Ast

type env

module Proof : sig
  val parse_string : ?filename:string -> env -> string -> A.proof

  val parse_chan : ?filename:string -> env -> in_channel -> A.proof
end
