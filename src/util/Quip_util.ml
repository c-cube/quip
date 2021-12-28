
open Quip_core
open Common

module Logger = Logger
module Loc = Loc
module Error = Error

(** Setup a logger at given level *)
let setup_log lvl : unit =
  let quip_logger = Logger.create() in
  Logger.log_to_chan quip_logger stdout;
  Logs.set_reporter (Logger.as_reporter quip_logger);
  Logs.set_level ~all:true (Some lvl)

(** Open files, including compressed ones *)
let with_file_in (file:string) f =
  if Filename.extension file = ".gz" then (
    let p = Unix.open_process_in
        (Printf.sprintf "gzip --keep -d -c \"%s\"" (String.escaped file))
    in
    CCFun.finally1
      ~h:(fun () -> Unix.close_process_in p)
      f p
  ) else CCIO.with_in file f

module Chrono : sig
  type t
  val start : unit -> t
  val elapsed: t -> float
end = struct
  type t = float
  let start () = Unix.gettimeofday()
  let elapsed self = Unix.gettimeofday() -. self
end
