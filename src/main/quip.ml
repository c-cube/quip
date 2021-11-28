
(** {1 Proof checker} *)

module Log = (val Logs.src_log (Logs.Src.create "quip.main"))

(* check proof for problem, then exits *)
let main ~quiet ~problem proof : 'a =
  Log.info (fun k->k"process proof '%s' with problem %a" proof (Fmt.opt Fmt.string_quoted) problem);
  let proof = with_file_in proof (Parser.Proof.parse_chan ~filename:proof) in
  if not quiet then (
    Log.info (fun k->k"parsed proof");
    Log.debug (fun k->k"parsed proof:@ %a" Ast.Proof.pp proof);
  );
  let ctx = K.Ctx.create() in
  let env = match problem with
    | None -> Env.make_new_smt2 ~ctx ()
    | Some pb ->
      let env = Problem_parser.parse_file_exn ctx pb in
      Log.info (fun k->k"parsed problem from '%s'" pb);
      Log.debug (fun k->k"parsed problem:@ %a" Env.pp_debug env);
      env
  in

  let checker = Quip_check.Check.create ctx env in

  Fmt.printf "checking proof…@.";
  let proof_valid, bad_steps, stats = Quip_check.Check.check_proof checker proof in
  Fmt.printf "; @[<h>%a@]@." Quip_check.Check.pp_stats stats;
  if proof_valid then (
    Fmt.printf "@{<Green>OK@}@.";
  ) else (
    Fmt.printf "@{<Red>FAIL@}@.";
    Fmt.printf "; bad steps: %s@." (String.concat ", " bad_steps);
  );
  exit (if proof_valid then 0 else 1)

let () =
  Printexc.record_backtrace true;
  let files = ref [] in
  let color = ref true in
  let quiet = ref false in
  let problem = ref None in

  let log_level = ref Logs.Warning in

  let opts = [
    "--info", Arg.Unit (fun() -> log_level := Logs.Info), " set log level to info";
    "--debug", Arg.Unit (fun() -> log_level := Logs.Debug), " set log level to debug";
    "-d", Arg.Unit (fun() -> log_level := Logs.Debug), " set log level to debug";
    "--problem", Arg.String (fun s->problem := Some s), " parse context from this problem file";
    "-nc", Arg.Clear color, " disable color";
    "-q", Arg.Set quiet, " quiet mode";
  ] |> Arg.align in
  Arg.parse opts (fun f -> files := f :: !files) "quip [opt]* proof.quip";

  setup_log !log_level;

  Fmt.set_color_default !color;
  match List.rev !files with
  | [proof] ->
    begin
      try main ~quiet:!quiet ~problem:!problem proof
      with
      | Error msg ->
        Fmt.eprintf "@{<Red>Error@}: %s@." msg; exit 3
      | e ->
        let bt = Printexc.get_backtrace() in
        let msg = Printexc.to_string e in
        Fmt.eprintf "@{<Red>Error@}: %s@.%s@." msg bt; exit 3
    end
  | _ -> Fmt.eprintf "expected [opt]* <proof>@."; exit 2
