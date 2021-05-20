
open Common
type pb = Parsed_pb.t

module Log = (val Logs.src_log (Logs.Src.create ~doc:"Problem parser for Quip" "quip.parse-pb"))

module Smtlib = struct
  module SA = Smtlib_utils.V_2_6.Ast

  type ('a,'b) tbl = ('a,'b) Hashtbl.t [@polyprinter CCHashtbl.pp] [@@deriving show]
  type 'a vec = 'a CCVector.vector [@polyprinter CCVector.pp] [@@deriving show]

  type env = {
    ctx: K.ctx [@opaque];
    consts: (string, K.const [@printer K.Const.pp]) tbl;
    ty_consts: (string, K.ty_const [@printer K.Const.pp]) tbl;
    assms: K.Thm.t vec;
  } [@@deriving show {with_path=false}]

  let create() : env = {
    ctx= K.Ctx.create();
    consts=Hashtbl.create 32;
    ty_consts=Hashtbl.create 32;
    assms=CCVector.create();
  }

  let add_stmt (env:env) (st:SA.statement) : unit =
    (* TODO *)
    ()

  let parse_file_exn filename : pb =
    Log.debug (fun k->k"parse SMTLIB file '%s'" filename);
    let pb =
      try Smtlib_utils.V_2_6.parse_file_exn filename
      with e ->
        errorf "cannot parse smtlib file '%s':@.%s@." filename (Printexc.to_string e)
    in
    Log.info (fun k->k"parsed %d statements" (List.length pb));
    Log.debug (fun k->k"@[<v2>problem:@ %a@]@." SA.(pp_list pp_stmt) pb);

    let env = create() in
    List.iter (add_stmt env) pb;

    let module PB = struct
      let ctx = env.ctx
      let find_const_by_name n = CCHashtbl.get env.consts n
      let find_ty_const_by_name n = CCHashtbl.get env.ty_consts n
      let assumptions () = CCVector.to_seq env.assms
      let pp_debug out () = pp_env out env
    end in
    (module PB)

  let parse_file file =
    try Ok (parse_file_exn file)
    with Error s -> Error s
end

let parse_file filename : _ result =
  match Filename.extension filename with
  | ".smt2" ->
    Smtlib.parse_file filename
  | ext ->
    errorf "unknown problem extension '%s'" ext

let parse_file_exn filename =
  match parse_file filename with
  | Ok x -> x
  | Error e -> error e
