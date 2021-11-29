
open Quip_core
open Common

module Logger = Logger

(** Setup a logger at given level *)
let setup_log lvl : unit =
  let quip_logger = Logger.create() in
  Logger.log_to_chan quip_logger stdout;
  Trustee_core.Log.(
    let module Log = (val Logs.src_log (Logs.Src.create "trustee")) in
    set_level 50;
    set_logger {
      log=fun lvl k ->
        let m : _ Logs.msgf = fun logger -> k (fun fmt -> logger ?header:None ?tags:None fmt)in
        match lvl with
        | 0 -> Log.app m
        | 1 -> Log.info m
        | _ -> Log.debug m
    });
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
