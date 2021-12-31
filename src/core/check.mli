
(** {1 Proof Checker} *)

open Common

module K = Kernel
module E = K.Expr

type t

val create : K.ctx -> Env.t -> Small_loc.ctx -> t

type stats = {
  n_valid: int;
  n_invalid: int;
  n_steps: int;
} [@@deriving show]

type bad = string

val check_proof : t -> Ast.Proof.t -> bool * bad list * Error.t list * stats
