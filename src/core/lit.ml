
open Common

module K = Kernel
module E = Kernel.Expr

type t = {
  sign: bool;
  expr: E.t;
} [@@deriving eq, ord]

let pp_depth ?max_depth out (self:t) =
  let pp_t = match max_depth with
    | None -> E.pp
    | Some max_depth -> E.pp_depth ~max_depth in
  if self.sign then pp_t out self.expr
  else Fmt.fprintf out "(@[not@ %a@])" pp_t self.expr
let pp = pp_depth ?max_depth:None
let show = Fmt.to_string pp

let[@inline] sign self = self.sign
let[@inline] atom self = self.expr
let[@inline] neg (self:t) : t = {self with sign=not self.sign}

(* always normalize equations so that the order in which they were
   input does not matter. Also normalize under [not] because we might open it. *)
let rec normalize_expr_ ctx e =
  match E.unfold_not e with
  | Some u ->
    E.not_ ctx @@ normalize_expr_ ctx u
  | None ->
    match E.unfold_eq e with
    | Some (a,b) ->
      let a = normalize_expr_ ctx a in
      let b = normalize_expr_ ctx b in
      if E.compare a b < 0 then E.app_eq ctx b a else E.app_eq ctx a b
    | _ -> e

let[@inline] make ctx sign expr =
  let expr = normalize_expr_ ctx expr in
  let expr, sign = match E.unfold_not expr with
    | Some u -> u, not sign
    | _ -> expr, sign
  in
  {sign;expr}

let to_expr ctx (self:t) : K.expr =
  if self.sign then self.expr
  else E.not_ ctx self.expr

let as_eqn self : _ option =
  if self.sign then E.unfold_eq self.expr
  else None

module As_key = struct
  type nonrec t = t
  let compare = compare
end
module Set = CCSet.Make(As_key)
