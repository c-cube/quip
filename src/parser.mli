
open Common
module P = Proof

type env

val create_env : K.ctx -> env

module Pb : sig
(*   val parse_string : ?filename:string -> env -> string -> unit *)
  val parse_chan : ?filename:string -> env -> in_channel -> unit
end

module Proof : sig
  val parse_string : ?filename:string -> env -> string -> P.t

  val parse_chan : ?filename:string -> env -> in_channel -> P.t
end
