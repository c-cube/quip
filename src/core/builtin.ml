
type t =
  | True
  | False
  | And
  | Or
  | Imply
  | Not
  | Xor
[@@deriving show {with_path=false}, eq, enum]

let hash (x:t) : int = CCHash.int (to_enum x)

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
