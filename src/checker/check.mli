
(** {1 Proof Checker} *)

module K = Trustee_core.Kernel
module E = K.Expr
module P = Quip_core.Ast.Proof

type t

val create : K.ctx -> t

val check_step : t -> P.composite_step -> unit

val check_proof : t -> P.t -> bool
