
open Quip_core.Common
open OUnit2
module K = Trustee_core.Kernel
module Check = Quip_check.Check

module Make() = struct
  let ctx = K.Ctx.create()
  module E = (val K.make_expr ctx)
  module Th = (val K.make_thm ctx)

  let _src = Logs.Src.create "quip.test"
  module Log = (val Logs.src_log _src)

  let parse_pb_str line s =
    match
      Quip_core.Problem_parser.(parse_string ~syn:Smt2) ctx s
    with
    | Ok x -> x
    | Error e -> errorf "cannot parse problem at line %d:@ %s" line e

  let parse_proof_str line s =
    try Quip_core.Parser.Proof.parse_string s
    with e -> errorf "cannot parse proof at line %d:@ %a" line Fmt.exn e

  let _debug = try Sys.getenv "DEBUG"="1" with _ -> false
  let () =
    Logs.set_reporter (Logs.format_reporter());
    Logs.set_level ~all:true (if _debug then Some Logs.Debug else None);
    Logs.Src.set_level _src (Some (if _debug then Logs.Debug else Logs.Info))

  let test_proof ~expect line pb proof =
    let pb = parse_pb_str line pb in
    let proof = parse_proof_str line proof in
    let checker = Check.create ctx pb in
    let ok, _stats = Check.check_proof checker proof in
    Logs.info (fun k->k"line %d: res %b, stats %a@." line ok Check.pp_stats _stats);
    assert_equal ~msg:(Printf.sprintf "expect %B on line %d" expect line)
      ~printer:Fmt.(to_string bool) expect ok;
    ()

  (* a SMT2 prelude *)
  let prelude0 = {|
    (declare-sort U 0)
    (declare-fun a () U)
    (declare-fun b () U)
    (declare-fun c () U)
    (declare-fun f1 (U) U)
    (declare-fun g1 (U) U)
    (declare-fun f2 (U U) U)
    (declare-fun g2 (U U) U)
    (declare-fun p1 (U) Bool)
  |}

  let l = [
    (* basic CC *)
    (__LINE__, true, prelude0,
    {|(quip 1 (steps () (
        (stepc c0 (cl (+ (p1 a))) (assert-c (@ c0)))
        (stepc c1 (cl (- (p1 b))) (assert-c (@ c1)))
        (stepc c2 (cl (+ (= a b))) (assert-c (@ c2)))
        (stepc c3 (cl (- (= a b)) (- (p1 a)) (+ (p1 b))) (ccl (@ c3)))
        (stepc c4 (cl) (hres (@ c3) ((r1 (@ c0)) (r1 (@ c1)) (r1 (@ c2))))))))
        |});
    (* basic CC with bool *)
    (__LINE__, true, prelude0,
     {|(quip 1 (steps () (
        (stepc c0 (cl (+ (= (f1 b) a))) (assert-c (@ c0)))
        (stepc c1 (cl (+ (p1 (f1 a)))) (assert-c (@ c1)))
        (stepc c2 (cl (+ (= b a))) (assert-c (@ c2)))
        (stepc c3 (cl (- (p1 b))) (assert-c (@ c3)))
        (stepc lemma
         (cl (- (p1 (f1 a))) (- (= (f1 b) a)) (- (= b a)) (+ (p1 b)))
         (ccl (@ lemma)))
        (stepc c4 (cl) (hres (@ lemma) ((r1 (@ c3)) (r1 (@ c2)) (r1 (@ c1)) (r1 (@ c0)))))
    )))|});
    (* bad CC lemma *)
    (__LINE__, false, prelude0,
     {|(quip 1 (steps () (
        (stepc lemma
         (cl (- (p1 (f1 a))) (- (= (f1 b) a)) (- (= c a)) (+ (p1 b)))
         (ccl (@ lemma)))
       )))|});
    (* basic subst *)
    (__LINE__, true, prelude0,
     {|(quip 1 (steps () (
        (stepc c0 (cl (+ (= (f2 (? x U) b) (? x U)))) (assert-c (@ c0)))
        (stepc c2 (cl (+ (p1 (f2 a b)))) (assert-c (@ c2)))
        (stepc c3 (cl (- (p1 a))) (assert-c (@ c3)))
        (stepc c4 (cl (+ (= (f2 a b) a))) (subst (x a) (ref c0)))
        (stepc c5
          (cl (- (= (f2 a b) a)) (- (p1 (f2 a b))) (+ (p1 a))) (ccl (@ c5)))
        (stepc c6 (cl)
          (hres (@ c5) ((r1 (@ c4)) (r1 (@ c3)) (r1 (@ c2)))))
    )))|});
  ]

  let suite =
    let l =
      List.map
        (fun (line,expect,pb,proof) ->
           (Printf.sprintf "line %d" line) >:: fun _ctx ->
               test_proof ~expect line pb proof) l
    in
    "quip" >::: l
end


let () =
  let module M = Make() in
  OUnit2.run_test_tt_main M.suite
