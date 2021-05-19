
module Fmt = CCFormat
module K = Trustee_core.Kernel

exception Error of string
let error msg = raise (Error msg)
let errorf fmt = Fmt.kasprintf (fun s -> error s) fmt

let () = Printexc.register_printer
    (function
      | Error s -> Some s
      | _ -> None)

