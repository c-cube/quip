

module K = Trustee_core.Kernel
module E = K.Expr
module P = Quip_core.Ast.Proof

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Proof checker" "quip.check"))

type t = {
  ctx: K.ctx;
  checked: (string, bool) Hashtbl.t;
}

let create ctx : t =
  { ctx; checked=Hashtbl.create 32; }

let check_step (_self:t) (step:P.composite_step) : unit =
  Log.debug (fun k->k"checking step %a" P.pp_composite_step step);
  assert false (* TODO *)

let check_proof (_self:t) (p:P.t) : bool =
  Log.debug (fun k->k"checking proof");
  false (* TODO: check each step, and glue all steps together *)
