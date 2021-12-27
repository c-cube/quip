
module Fmt = CCFormat

module Str_tbl = CCHashtbl.Make(CCString)
module Str_map = CCMap.Make(CCString)
module Str_set = CCSet.Make(CCString)

module CCOpt = CCOpt

module Loc = Loc
module Error = Error

type 'a iter = ('a -> unit) -> unit

let pp_l ppx out l =
  Fmt.(list ~sep:(return "@ ") ppx) out l
let pp_iter ?(sep=" ") ppx out iter =
  Fmt.iter ~sep:(fun out () -> Fmt.fprintf out "%s@," sep) ppx out iter

let (let@@) f1 f2 = f1 f2

module type EQ = sig
  type t
  val equal : t -> t -> bool
end

module type COMPARE = sig
  type t
  val compare : t -> t -> int
end

module type HASH = sig
  type t
  val hash : t -> int
end

module type PP = sig
  type t
  val pp : t Fmt.printer
  val to_string : t -> string
end

