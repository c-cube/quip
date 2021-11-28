
(** {1 Proof Checker} *)

open Common

type t

val create : K.ctx -> Quip_core.Env.t -> t

type stats = {
  n_valid: int;
  n_invalid: int;
  n_steps: int;
} [@@deriving show]

type bad = string

val check_proof : t -> Quip_core.Ast.Proof.t -> bool * bad list * stats
