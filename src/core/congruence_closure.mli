

(** {1 Congruence closure} *)

module K = Kernel
module E = Kernel.Expr

module Proof : sig
  type t [@@deriving show]
end

val is_absurd :
  K.ctx ->
  true_:E.t ->
  false_:E.t ->
  Lit.t list -> Proof.t option
(** [is_absurd ctx hyps]
    tries to prove [false] from the literals in [hyps], i.e. proves
    that [\/_i ¬lit_i] is a theorem of QF_UF.
    @param true_ the constant true
    @param false_ the constant false
*)
