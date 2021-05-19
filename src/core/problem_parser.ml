
open Common
type pb = Parsed_pb.t

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Problem parser for Quip" "quip.parse-pb"))

module Smtlib = struct
  module SA = Smtlib_utils.V_2_6.Ast

  let parse_file filename : _ result =
    Log.debug (fun k->k"parse SMTLIB file '%s'" filename);
    let pb =
      try Smtlib_utils.V_2_6.parse_file_exn filename
      with e ->
        errorf "cannot parse smtlib file '%s':@.%s@." filename (Printexc.to_string e)
    in
    Log.info (fun k->k"parsed %d statements" (List.length pb));
    Log.debug (fun k->k"@[<v2>problem:@ %a@]@." SA.(pp_list pp_stmt) pb);
    (* TODO *)
    assert false

  let parse_file_exn file =
    match parse_file file with
    | Ok x -> x
    | Error e -> error e
end

let parse_file filename : _ result =
  match Filename.extension filename with
  | ".smt2" ->
    Smtlib.parse_file filename
  | ext ->
    errorf "unknown problem extension '%s'" ext
