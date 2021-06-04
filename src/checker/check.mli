
(** {1 Proof Checker} *)

module K = Trustee_core.Kernel
module E = K.Expr

type t

val create : K.ctx -> Quip_core.Parsed_pb.t -> t

type stats = {
  n_valid: int;
  n_invalid: int;
  n_steps: int;
} [@@deriving show]

val check_proof : t -> Quip_core.Ast.Proof.t -> bool * stats
