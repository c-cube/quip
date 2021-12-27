
open Common
module K = Kernel
module E = K.Expr

module ESet = K.Expr.Set

type t = {
  lits: Lit.Set.t;
} [@@unboxed][@@deriving eq]

let lits self k = Lit.Set.iter k self.lits

let pp out self =
  Fmt.fprintf out "(@[<hv>cl@ %a@])"
    Fmt.(iter ~sep:(return "@ ") Lit.pp) (lits self)

let pp_depth ~max_depth out self =
  Fmt.fprintf out "(@[<hv>cl@ %a@])"
    Fmt.(iter ~sep:(return "@ ") @@ Lit.pp_depth ~max_depth) (lits self)

let show = Fmt.to_string pp

let mem x self = Lit.Set.mem x self.lits

let empty = {lits=Lit.Set.empty}

let singleton lit = {lits=Lit.Set.singleton lit}

let size self = Lit.Set.cardinal self.lits

let add lit self = {lits=Lit.Set.add lit self.lits}
let add' s x = add x s

let of_list = List.fold_left add' empty
let of_iter = Iter.fold add' empty

let subset c1 c2 = Lit.Set.subset c1.lits c2.lits

let remove lit self = {lits=Lit.Set.remove lit self.lits}
let lits_list self = lits self |> Iter.to_rev_list

let union c1 c2 = {lits=Lit.Set.union c1.lits c2.lits}

let as_singleton self = match Lit.Set.choose_opt self.lits with
  | Some lit ->
    if Lit.Set.is_empty (Lit.Set.remove lit self.lits) then Some lit else None
  | None -> None

let to_iter = lits

let pos_lits self = lits self |> Iter.filter Lit.sign
let neg_lits self = lits self |> Iter.filter (fun l -> not (Lit.sign l))

let pos_lits_list self = pos_lits self |> Iter.to_rev_list
let neg_lits_list self = neg_lits self |> Iter.to_rev_list

let find_lit_by_term ctx e (self:t) : Lit.t option =
  let lit = Lit.make ctx true e in
  if mem lit self then Some lit
  else if mem (Lit.neg lit) self then Some (Lit.neg lit)
  else None

let uniq_lit_of_sign_ sign self =
  match
    lits self |> Iter.filter (fun lit -> Lit.sign lit = sign)
    |> Iter.take 2 |> Iter.to_rev_list
  with
  | [l] -> Some l
  | _ -> None

let uniq_pos_lit self = uniq_lit_of_sign_ true self
let uniq_neg_lit self = uniq_lit_of_sign_ false self

let subst ctx ~recursive self subst : t =
  if K.Subst.is_empty subst then self
  else (
    to_iter self
    |> Iter.map
      (fun lit ->
        let sign = Lit.sign lit in
        let e = E.subst ~recursive ctx (Lit.atom lit) subst in
        Lit.make ctx sign e)
    |> of_iter
  )

