

module K = Trustee_core.Kernel
module E = K.Expr
module Log = Trustee_core.Log
module P = Proof

type t = {
  ctx: K.ctx;
  checked: (string, bool) Hashtbl.t;
}

let create ctx : t =
  { ctx; checked=Hashtbl.create 32}

let check_step (self:t) (step:P.step) : unit =
  Log.debugf 1 (fun k->k"checking step %a" P.pp_step step);
  assert false (* TODO *)

let check_proof (self:t) (p:P.t) : bool =
  Log.debugf 1 (fun k->k"checking proof");
  false (* TODO: check each step, and glue all steps together *)
