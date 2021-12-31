
open Common

module A = Ast

module Proof : sig
  val parse_string : ?filename:string -> string -> A.Proof.t * Small_loc.ctx
end
