
type t =
  | True
  | False
  | And
  | Or
  | Imply
  | Not
  | Xor
  | Eq
  | Bool
  | If
[@@deriving show {with_path=false}, eq, enum]

let hash (x:t) : int = CCHash.int (to_enum x)

(** [is_assoc b] returns [true] iff [b] is an associative function symbol,
    which enables the syntax [b t1…tn] as a shortcut for [(((b t1 t2) t3) …) tn] *)
let is_assoc = function
  | And | Or | Imply -> true
  | True | False | Not | Xor | Eq | Bool | If -> false

module As_key = struct
  type nonrec t = t
  let equal = equal
  let hash = hash
end

module Tbl = struct
  let _pp_b = pp
  include CCHashtbl.Make(As_key)
  let pp ppv = pp _pp_b ppv
end
