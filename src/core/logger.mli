
(** Log reporter *)

type t

val create : unit -> t

val as_reporter : t -> Logs.reporter

val log_to_chan : t -> out_channel -> unit
