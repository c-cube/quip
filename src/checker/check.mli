
(** {1 Proof Checker} *)

module K = Trustee_core.Kernel
module E = K.Expr

type t

val create : K.ctx -> Quip_core.Parsed_pb.t -> t

val check_proof : t -> Quip_core.Ast.Proof.t -> bool
