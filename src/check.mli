
(** {1 Proof Checker} *)

module K = Trustee_core.Kernel
module E = K.Expr

type t

val create : K.ctx -> t

val check_step : t -> Proof.step -> unit

val check_proof : t -> Proof.t -> bool
