
open Common

type term = E.t

type lit = bool * term

type clause = {
  c_lits: lit list;
}

type t =
  | Pr_assume of clause
  | Pr_hres of {
      init: t;
      steps: hres_step list;
    }
  | Pr_cc_lemma of clause
  | Pr_cc_imply of t list * term * term
  | Pr_clause_eq
  | Pr_theory_lemma
  | Pr_composite of {
      assumptions: lit list;
      steps: step list;
    }

and hres_step =
  | P of {lhs: term; rhs: term; p: t}
  | P1 of t
  | R of {pivot: term; p: t}
  | R1 of t

and step =
  | S_step_c of {
      name: string;
      concl: clause;
      proof: t
    }
  | S_def_t of {
      name: string;
      t: term
    }

let pp_lit out (b,t : lit) =
  Fmt.fprintf out "(@[%s %a@])" (if b then "+" else "-") E.pp t

let pp_clause out (c:clause) =
  Fmt.fprintf out "(@[cl@ %a@])"
    Fmt.(list ~sep:(return "@ ") pp_lit) c.c_lits

let rec pp out (self:t) : unit =
  Fmt.fprintf out "(@[<hv>proof@ %a@])"
    Fmt.(iter ~sep:(return "@ ") pp_step)
    (CCHashtbl.values self.steps)

and pp_step out (self:step) : unit =
  match self with
  | S_def_t {name; t} ->
    Fmt.fprintf out "(@[deft %s@ %a@])" name E.pp t
  | S_step_c {name; concl; proof=p} ->
    Fmt.fprintf out "(@[stepc %s@ %a@ %a@])" name pp_clause concl pp p

let add_step (self:t) (s:step) : unit =
  if Hashtbl.mem self.steps s.ps_name then (
    errorf (fun k->k"duplicate proof step name %S" s.ps_name)
  );
  Hashtbl.add self.steps s.ps_name s
