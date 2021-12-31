
type t
val file : string -> t
val string : string -> t

val to_pp_loc_input : t -> Pp_loc.Input.t
