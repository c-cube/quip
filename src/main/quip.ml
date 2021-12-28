
(** {1 Proof checker} *)

module Log = (val Logs.src_log (Logs.Src.create "quip.main"))
module K = Kernel

let hrule = String.make 60 '='

module Opts = struct
  type t = {
    color: bool;
    quiet: bool;
    log_level: Logs.level;
  } [@@deriving show]

  let cmd : t Cmdliner.Term.t =
    let open Cmdliner in
    let color = Arg.(value & opt bool true & info ["color"] ~doc:"enable/disable colors")
    and quiet = Arg.(value & opt bool false & info ["q";"quiet"] ~doc:"quiet mode")
    and log_level =
      Arg.(value &
           opt (enum ["info", Logs.Info;
                      "debug", Logs.Debug;
                      "warning", Logs.Warning])
             Logs.Warning &
           info ["log"] ~doc:"debug level")
    in
    let mk color quiet log_level = {color;quiet;log_level} in
    Term.(pure mk $ color $ quiet $ log_level)

  let apply self : unit =
    let {color; quiet=_; log_level} = self in
    Fmt.set_color_default color;
    setup_log log_level;
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
    let proof =
      let content = with_file_in proof CCIO.read_all in
      if not quiet then (
        Log.info (fun k->k"proof size: %d bytes" (String.length content));
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

    let checker = Check.create ctx env in

    Fmt.printf "checking proof…@.";
    let proof_valid, bad_steps, errors, stats = Check.check_proof checker proof in
    Fmt.printf "; @[<h>%a@]@." Check.pp_stats stats;
    if proof_valid then (
      Fmt.printf "@{<Green>OK@}@.";
    ) else (
      List.iter (Fmt.printf "%s@.%a@." hrule Error.pp) errors;
      Fmt.printf "; bad steps: %s@." (String.concat ", " bad_steps);
      Fmt.printf "@{<Red>FAIL@}@.";
    );
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
  open Ast.Proof
  module T = Ast.Term

  type name = string (** node name *)

  type state = {
    terms: (string, Ast.Term.t) Hashtbl.t;
    clauses: (string, T.t array) Hashtbl.t;
    printed: (string, unit) Hashtbl.t;
    out: string CCVector.vector;
    mutable n: int;
  }

  let add_line (state:state) (s:string) : unit = CCVector.push state.out s
  let add_linef state fmt = Fmt.kasprintf (add_line state) fmt

  let cleanup_str s =
    CCString.flat_map
      (function
        | '\n' -> "\\l"
        | '"' -> "'"
        | c -> String.make 1 c)
      s

  (** Expand definitions in term *)
  let norm_term (st:state) (t:T.t) : T.t =
    let rule t = match T.view t with
      | T.Ref name -> CCHashtbl.get st.terms name
      | T.Var {name;_} -> CCHashtbl.get st.terms name
      | _ -> None
    in
    T.rw ~rule t

  let norm_clause st (c:Ast.Clause.t) : T.t array =
    match c.view with
    | Ast.Clause.Clause_ref n ->
      (try Hashtbl.find st.clauses n
       with Not_found ->
         Log.err (fun k->k"cannot find clause %S" n);
         [||])
    | Ast.Clause.Clause lits ->
      Array.of_list lits |> Array.map (norm_term st)

  (** A different type for proofs *)
  type normalized_proof = {
    p: (T.t, T.t array, normalized_proof) view;
  }

  let rec norm_proof (st:state) (p:t) : normalized_proof =
    {p=
      (view p)
      |> map_view (norm_term st) (norm_clause st) (norm_proof st)
    }

  let pp_lits out (c:T.t array) =
    Fmt.fprintf out "cl {@[<hv>%a@]}" Fmt.(array ~sep:(return "@ ∨ ") T.pp) c

  (* allocate new name *)
  let new_name (st:state): name =
    let s = Printf.sprintf "a_%d" st.n in
    st.n <- 1 + st.n;
    s

  (* return the node name *)
  let rec pp_proof_itself ?name state (self:t) : string =
    match name with
    | Some n -> n
    | None ->
      let p' = norm_proof state self in
      pp_proof_normalized state p'

  and pp_proof_normalized (state:state) (p:normalized_proof) : string =
    let name = new_name state in
    let links = ref [] in (* outgoing edges *)

    let label =
      Fmt.asprintf "%a"
        (Ast.Proof.pp_view
           T.pp
           pp_lits
           (fun out p' ->
              let n' =
                match p'.p with
                | Named n' -> n'
                | _ -> pp_proof_normalized state p'
              in
              links := n' :: !links;
              Fmt.string out n'))
        p.p
      |> cleanup_str
    in

    (* define *)
    add_linef state
      {|@[%s [label="%s", shape="box", style="filled", fillcolor="lavenderblush1"];@]|}
      name label;

    (* add edges *)
    List.iter (fun n' -> add_linef state {|@[%s -> %s [label="%s"]@]|} name n' n') !links;
    name

  and pp_step (state:state) (self:_ composite_step) : unit =
    match self.view with
    | S_define_t (name,t) ->
      Hashtbl.replace state.terms name t
    | S_declare_ty_const _ -> ()
    | S_declare_const _ -> ()
    | S_define_const { name; ty=_; rhs } ->
      Hashtbl.replace state.terms name rhs
    | S_step_c {name; res; proof} ->
      if not (Hashtbl.mem state.printed name) then (
        let res = Array.of_list res |> Array.map (norm_term state) in
        Hashtbl.add state.printed name ();
        Hashtbl.add state.clauses name res;

        let label =
          Fmt.asprintf "%a" pp_lits res |> cleanup_str
        in

        add_linef state
          {|@[%s [label="%s",shape="box",fillcolor="%s",style="filled"]@]|}
          name label (if res=[||] then "red" else "cyan");
        let p = pp_proof_itself state proof in
        add_linef state {|@[%s -> %s [label="proof(%s)"]@]|} name p name;
      );
      ()

  let pp_top (state:state) (self:t) : unit =
    match view self with
    | Composite {assumptions=_; steps} ->
      Array.iter
        (fun step ->
           pp_step state step)
        steps;
    | _ ->
      ()

  let dot_of_proof p =
    let st = {
      terms=Hashtbl.create 32;
      printed=Hashtbl.create 32;
      clauses=Hashtbl.create 32;
      out=CCVector.create();
      n=0;
    } in
    pp_top st p;
    Fmt.asprintf "@[<v2>digraph proof {@,%a@,}@]@."
      Fmt.(iter ~sep:(return "@ ") string) (CCVector.to_iter st.out)

  let run opts proof_file out : int =
    wrap_err @@ fun () ->
    Opts.apply opts;

    let proof =
      let content = with_file_in proof_file CCIO.read_all in
      Parser.Proof.parse_string ~filename:proof_file content
    in

    if not opts.quiet then (
      Log.info (fun k->k"parsed proof");
      Log.debug (fun k->k"parsed proof:@ %a" Ast.Proof.pp proof);
    );

    CCIO.with_out out (fun oc ->
        let dot_repr = dot_of_proof proof in
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
