
open Common

module A = Ast

(* TODO: use in conversion to real, Trustee based proofs  in checker
type env
*)

module Proof : sig
  val parse_string : ?filename:string -> string -> A.Proof.t

  val parse_chan : ?filename:string -> in_channel -> A.Proof.t
end
