
(** {1 Proof checker} *)

open Quip_core
open Common

module Log = (val Logs.src_log (Logs.Src.create "quip.main"))

let setup_log lvl : unit =
  Trustee_core.Log.(
    let module Log = (val Logs.src_log (Logs.Src.create "trustee")) in
    set_logger {
      log=fun lvl k ->
        let m : _ Logs.msgf = fun logger -> k (fun fmt -> logger ?header:None ?tags:None fmt)in
        match lvl with
        | 0 -> Log.app m
        | 1 -> Log.info m
        | _ -> Log.debug m
    });
  Logs.set_reporter (Logs.format_reporter ());
  Logs.set_level ~all:true (Some lvl)

(* check proof for problem, then exits *)
let main ~quiet ~problem proof : 'a =
  Log.info (fun k->k"process proof '%s' with problem '%s'" proof problem);
  let proof = CCIO.with_in proof (Parser.Proof.parse_chan ~filename:proof) in
  if not quiet then (
    Log.debug (fun k->k"parsed proof");
    Fmt.printf "parsed proof:@ %a@." Ast.Proof.pp proof;
  );
  let ctx = K.Ctx.create() in
  let problem = Problem_parser.parse_file_exn ctx problem in
  Log.debug (fun k->k"parsed problem:@ %a" Parsed_pb.pp_debug problem);

  let checker = Quip_check.Check.create ctx problem in

  Fmt.printf "checking proof…@.";
  let proof_valid = Quip_check.Check.check_proof checker proof in
  if proof_valid then (
    Fmt.printf "@{<Green>OK@}@.";
  ) else (
    Fmt.printf "@{<Green>FAIL@}@.";
  );
  exit (if proof_valid then 0 else 1)

let () =
  let files = ref [] in
  let color = ref true in
  let quiet = ref false in

  let log_level = ref Logs.Error in

  let opts = [
    "--info", Arg.Unit (fun() -> log_level := Logs.Info), " set log level to info";
    "--debug", Arg.Unit (fun() -> log_level := Logs.Debug), " set log level to debug";
    "-nc", Arg.Clear color, " disable color";
    "-q", Arg.Set quiet, " quiet mode";
  ] |> Arg.align in
  Arg.parse opts (fun f -> files := f :: !files) "quip [opt]* problem proof.quip";

  setup_log !log_level;

  Fmt.set_color_default !color;
  match List.rev !files with
  | [problem; proof] ->
    begin
      try main ~quiet:!quiet ~problem proof
      with
      | Error msg ->
        Log.err (fun k->k "error: %s" msg);
        Fmt.eprintf "@{<Red>Error@}: %s" msg; exit 3
      | e ->
        let msg = Printexc.to_string e in
        Log.err (fun k->k "error: %s" msg);
        Fmt.eprintf "@{<Red>Error@}: %s" msg; exit 3
    end
  | _ -> Fmt.eprintf "expected <problem> <proof>@."; exit 2
