
module Fmt = CCFormat

type t = {
  buf: Buffer.t;
  fmt: Format.formatter;
  mutable chans: out_channel list;
}

let create () : t =
  let buf = Buffer.create 128 in
  let fmt = Format.formatter_of_buffer buf in
  { buf; fmt; chans=[]; }

let log_to_chan self oc : unit =
  self.chans <- oc :: self.chans

let as_reporter self : Logs.reporter =
  let output_all () =
    let s = Buffer.contents self.buf in
    List.iter
      (fun oc -> output_string oc s; flush oc) self.chans
  in
  { Logs.report =
      fun src lvl ~over k msg ->
        if self.chans <> [] then (
          Buffer.clear self.buf;
          Fmt.fprintf self.fmt "(@[%s[%a" (Logs.Src.name src) Logs.pp_level lvl;
          msg (fun ?header ?(tags=Logs.Tag.empty) fmt ->
              CCOpt.iter (fun s -> Fmt.fprintf self.fmt ",%s" s) header;
              if not (Logs.Tag.is_empty tags) then Logs.Tag.pp_set self.fmt tags;
              Fmt.fprintf self.fmt "]@ ";
              Fmt.kfprintf
                (fun _ ->
                   Fmt.fprintf self.fmt "@])@.";
                   output_all(); (* output content of [self.buf] *)
                   over();
                   k())
                self.fmt fmt
            )
        ) else k()
  }
