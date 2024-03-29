
(** {1 Proof checker} *)

module Log = (val Logs.src_log (Logs.Src.create "quip.main"))
module K = Kernel

let hrule = String.make 60 '='

module Opts = struct
  type t = {
    color: bool;
    quiet: bool;
    log_level: Logs.level;
    gc_stats: bool;
  } [@@deriving show]

  let cmd : t Cmdliner.Term.t =
    let open Cmdliner in
    let color = Arg.(value & opt bool true & info ["color"] ~doc:"enable/disable colors")
    and quiet = Arg.(value & opt bool false & info ["q";"quiet"] ~doc:"quiet mode")
    and gc_stats = Arg.(value & flag & info ["gc-stats"] ~doc:"print GC stats")
    and log_level =
      Arg.(value &
           opt (enum ["info", Logs.Info;
                      "debug", Logs.Debug;
                      "warning", Logs.Warning])
             Logs.Warning &
           info ["log"] ~doc:"debug level")
    in
    let mk color quiet gc_stats log_level = {color;quiet;log_level;gc_stats} in
    Term.(pure mk $ color $ quiet $ gc_stats $ log_level)

  let apply self : unit =
    let {color; quiet=_; log_level; gc_stats} = self in
    Fmt.set_color_default color;
    setup_log log_level;
    if gc_stats then at_exit (fun () ->
        let stat = Gc.stat() in
        Printf.printf
          "; gc stats:\n; - minor gc: %d\n; - major gc: %d\n\
           ; - minor heap: %.2fMB\n; - major heap: %.2fMB\n\
           ; - promoted: %.2fMB\n; - top heap: %.2fMB\n\
           %!"
          stat.minor_collections stat.major_collections
          (stat.minor_words *. 8e-6)
          (stat.major_words *. 8e-6)
          (stat.promoted_words *. 8e-6)
          (float stat.top_heap_words *. 8e-6)
      );
    ()
end

(** Wrap [f()] in an exception printer that returns an error code. *)
let wrap_err f =
  try f()
  with
  | Error.E e ->
    Fmt.eprintf "%a@." Error.pp e; 3
  | e ->
    let bt = Printexc.get_backtrace() in
    let msg = Printexc.to_string e in
    Fmt.eprintf "@{<Red>Error@}: %s@.%s@." msg bt; 4

module Check = struct
  (* check proof for problem, then exits *)
  let run opts problem proof : int =
    wrap_err @@ fun () ->
    Opts.apply opts;
    let quiet = opts.Opts.quiet in
    let chrono = Chrono.start() in
    Log.app (fun k->k"process proof '%s' with problem %a" proof (Fmt.opt Fmt.string_quoted) problem);
    let proof, ast_ctx =
      let content = with_file_in proof CCIO.read_all in
      if not quiet then (
        Log.app (fun k->k"proof size: %d bytes" (String.length content));
      );
      Parser.Proof.parse_string ~filename:proof content
    in
    if not quiet then (
      Log.app (fun k->k"parsed proof (in %.3fs)" @@ Chrono.elapsed chrono);
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

    let checker = Check.create ctx env ast_ctx in

    Fmt.printf "checking proof…@.";
    let proof_valid, bad_steps, errors, stats = Check.check_proof checker proof in
    if proof_valid then (
      Fmt.printf "@{<Green>OK@}@.";
    ) else (
      List.iter (Fmt.printf "%s@.%a@." hrule Error.pp) errors;
      Fmt.printf "; bad steps: %s@." (String.concat ", " bad_steps);
      Fmt.printf "@{<Red>FAIL@}@.";
    );
    Fmt.printf "; @[<h>%a@]@." Check.pp_stats stats;
    Fmt.printf "; done in %.3fs@." (Chrono.elapsed chrono);
    if proof_valid then 0 else 1

  let cmd =
    let open Cmdliner in
    let opts = Opts.cmd
    and proof =
      Arg.(required & pos 0 (some string) None &
           info [] ~docv:"PROOF" ~doc:"proof to process")
    and problem =
      Arg.(value & opt (some string) None & info ["problem"] ~doc:"problem file")
    in
    Term.(pure run $ opts $ problem $ proof),
    Term.info ~doc:"check proof" "check"
end

module Dot = struct
  let run opts proof_file out : int =
    wrap_err @@ fun () ->
    Opts.apply opts;

    let proof, _ast_ctx =
      let content = with_file_in proof_file CCIO.read_all in
      Parser.Proof.parse_string ~filename:proof_file content
    in

    if not opts.quiet then (
      Log.info (fun k->k"parsed proof");
      Log.debug (fun k->k"parsed proof:@ %a" Ast.Proof.pp proof);
    );

    CCIO.with_out out (fun oc ->
        let dot_repr = Dot.pr_proof proof in
        Log.debug (fun k->k"dot repr of proof:@ %s" dot_repr);
        output_string oc dot_repr);
    0

  let cmd =
    let open Cmdliner in
    let opts = Opts.cmd
    and out = Arg.(value & opt string "proof.dot" & info ["o";"out"] ~doc:"output file")
    and proof =
      Arg.(required & pos 0 (some string) None &
           info [] ~docv:"PROOF" ~doc:"proof to process")
    in
    Term.(pure run $ opts $ proof $ out),
    Term.info ~doc:"produce a graph visualization of the proof" "dot"
end

let parse_opt () : int Cmdliner.Term.result =
  let open Cmdliner in
  let help =
    let doc = "Toolkit to process Quip proofs" in
    let man = [
      `S "DESCRIPTION";
      `P "$(b,benchpress) is a tool to run tests and compare different \
          results obtained with distinct tools or versions of the same tool";
      `S "COMMANDS";
      `S "OPTIONS"; (* TODO: explain config file *)
    ] in
    Term.(ret (pure (fun () -> `Help (`Pager, None)) $ pure ())),
    Term.info ~version:"dev" ~man ~doc "benchpress"
  in

  Cmdliner.Term.eval_choice help [
    Check.cmd;
    Dot.cmd;
  ]

let main() =
  match parse_opt () with
  | `Error `Parse | `Error `Term | `Error `Exn -> exit 2
  | `Ok n -> exit n
  | `Version | `Help -> ()

let () =
  Printexc.record_backtrace true;
  TEF.setup();
  at_exit TEF.teardown;
  main()
