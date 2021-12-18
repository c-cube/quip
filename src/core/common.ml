
module Fmt = CCFormat
module K = Trustee_core.Kernel
module Str_map = CCMap.Make(String)

module CCOpt = CCOpt

module Loc = Loc
module Error = Error

let pp_l ppx out l =
  Fmt.(list ~sep:(return "@ ") ppx) out l

let (let@@) f1 f2 = f1 f2
