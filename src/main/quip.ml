
(** {1 Proof checker} *)

open Quip_core
open Common

let main ~quiet ~problem:_ proof : unit =
  let proof = CCIO.with_in proof (Parser.Proof.parse_chan ~filename:proof) in
  if not quiet then (
    Fmt.printf "parsed proof:@ %a@." Ast.Proof.pp proof;
  );
  (*
  let ctx = K.Ctx.create() in
  let env = Parser.create_env ctx in
  Fmt.printf "parsing problem from '%s'…@." pb;
  let pb = CCIO.with_in pb (Parser.Pb.parse_chan ~filename:pb env) in
  Fmt.printf "parsing proof from '%s'…@." proof;
  let proof = CCIO.with_in proof (Parser.Proof.parse_chan ~filename:proof env) in
  Fmt.printf "checking proof…@.";
  let checker = Check.create ctx in
  if Check.check_proof checker proof then (
    Fmt.printf "@{<Green>OK@}@.";
  ) else (
    Fmt.printf "@{<Green>FAIL@}@.";
  );
     *)
  ()

let () =
  let files = ref [] in
  let color = ref true in
  let pb = ref "" in
  let quiet = ref false in
  let opts = [
    "-d", Arg.Int Trustee_core.Log.set_level, " set log level";
    "-nc", Arg.Clear color, " disable color";
    "--problem", Arg.Set_string pb, " <file> set problem file";
    "-q", Arg.Set quiet, " quiet mode";
  ] |> Arg.align in
  Arg.parse opts (fun f -> files := f :: !files) "quip [opt]* proof.quip";

  Fmt.set_color_default !color;
  match List.rev !files with
  | [proof] ->
    let problem = if !pb="" then None else Some !pb in
    begin
      try main ~quiet:!quiet ~problem proof
      with Error e -> Fmt.eprintf "@{<Red>Error@}: %s" e; exit 1
    end
  | _ -> Fmt.eprintf "expected <problem> <proof>@."; exit 1
