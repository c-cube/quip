
open Common

module type S = sig
  val ctx : K.ctx

  val find_const_by_name : string -> K.const option

  val find_ty_const_by_name : string -> K.ty_const option

  (* TODO: named terms? *)

  val assumptions : unit -> K.thm Seq.t

  val pp_debug : unit Fmt.printer
  (** Print the environment, assumptions, etc. for debug. Can be verbose. *)
end

type t = (module S)

let pp_debug out (module M:S) = M.pp_debug out ()
