
open Common

type term = E.t

type rule =
  | Pr_assume
  | Pr_resolution
  | Pr_congruence
  | Pr_clause_eq
  | Pr_theory_lemma

type clause = {
  c_lits: term list;
}

type step = {
  ps_name: string;
  ps_clause: clause;
  ps_rule: rule;
  ps_premises: step list;
}

type t = {
  steps: (string, step) Hashtbl.t;
}

let pp_clause out (c:clause) =
  Fmt.fprintf out "(@[cl@ %a@])"
    Fmt.(list ~sep:(return " @<1>∨@ ") E.pp) c.c_lits

let pp_step_name out s = Fmt.string out s.ps_name

let pp_step out (self:step) : unit =
  (* TODO print rule*)
  Fmt.fprintf out "{@[name=%S;@ clause=%a;@ premises=[@[%a@]]@]}"
    self.ps_name pp_clause self.ps_clause
    Fmt.(list ~sep:(return "@ ") pp_step_name) self.ps_premises

let pp out (self:t) : unit =
  Fmt.fprintf out "(@[<hv>proof@ %a@])"
    Fmt.(iter ~sep:(return "@ ") pp_step)
    (CCHashtbl.values self.steps)

let create () : t =
  {steps=Hashtbl.create 32}

let find_step (self:t) s : step =
  try Hashtbl.find self.steps s
  with Not_found -> errorf (fun k->k"cannot find proof step named %S" s)

let add_step (self:t) (s:step) : unit =
  if Hashtbl.mem self.steps s.ps_name then (
    errorf (fun k->k"duplicate proof step name %S" s.ps_name)
  );
  Hashtbl.add self.steps s.ps_name s
