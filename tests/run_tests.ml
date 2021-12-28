
open Quip_core
open Quip_core.Common
open OUnit2

module K = Kernel
module E = K.Expr

module Make() = struct
  let ctx = K.Ctx.create()

  let _src = Logs.Src.create "quip.test"
  module Log = (val Logs.src_log _src)

  let parse_pb_str line s =
    match
      Quip_core.Problem_parser.(parse_string ~syn:Smt2) ctx s
    with
    | Ok x -> x
    | Error e -> Error.failf "cannot parse problem at line %d:@ %s" line e

  let parse_proof_str line s =
    try Quip_core.Parser.Proof.parse_string s
    with e -> Error.failf "cannot parse proof at line %d:@ %a" line Fmt.exn e

  let _debug = try Sys.getenv "DEBUG"="1" with _ -> false
  let () =
    Logs.set_reporter
      (Logs.format_reporter ~app:Format.err_formatter ~dst:Format.err_formatter ());
    Logs.set_level ~all:true (if _debug then Some Logs.Debug else None);
    Logs.Src.set_level _src (Some (if _debug then Logs.Debug else Logs.Info))

  let mk_test_ line k = Printf.sprintf "line %d" line >:: k

  let test_proof ~expect line pb proof =
    mk_test_ line @@ fun _ctx ->
    let pb = parse_pb_str line pb in
    let proof = parse_proof_str line proof in
    let checker = Check.create ctx pb in
    let ok, _, errs, _stats = Check.check_proof checker proof in
    Logs.info (fun k->k"line %d: res %b, stats %a@." line ok Check.pp_stats _stats);
    if expect && errs<> [] then (
      List.iter (fun e -> Log.err (fun k->k"got err: %a" Error.pp e)) errs;
    );
    assert_equal ~msg:(Printf.sprintf "expect %B on line %d" expect line)
      ~printer:Fmt.(to_string bool) expect ok;
    ()

  (* a SMT2 prelude *)
  let prelude0 = {|
    (declare-sort U 0)
    (declare-fun a () U)
    (declare-fun b () U)
    (declare-fun c () U)
    (declare-fun d () U)
    (declare-fun f1 (U) U)
    (declare-fun g1 (U) U)
    (declare-fun f2 (U U) U)
    (declare-fun g2 (U U) U)
    (declare-fun p0 () Bool)
    (declare-fun q0 () Bool)
    (declare-fun p1 (U) Bool)
    (declare-fun q1 (U) Bool)
  |}

  let l = [
    (* test resolution + toplevel-style proof *)
    test_proof ~expect:true __LINE__ prelude0
    {|(quip 1)
      (stepc c0 (cl p0) (assert-c (@ c0)))
      (stepc c1 (cl (not p0) q0) (assert-c (@ c1)))
      (stepc c2 (cl (not q0)) (assert-c (@ c2)))
      (stepc c3 (cl) (hres (@ c0) ((r p0 (@ c1)) (r1 (@ c2)))))
    |};
    (* basic CC *)
    test_proof ~expect:true __LINE__ prelude0
    {|(quip 1)
        (stepc c0 (cl (p1 a)) (assert-c (@ c0)))
        (stepc c1 (cl (not (p1 b))) (assert-c (@ c1)))
        (stepc c2 (cl (= a b)) (assert-c (@ c2)))
        (stepc c3 (cl (not (= a b)) (not (p1 a)) (p1 b)) (ccl (@ c3)))
        (stepc c4 (cl) (hres (@ c3) ((r1 (@ c0)) (r1 (@ c1)) (r1 (@ c2)))))
        |};
    (* basic CC with bool *)
    test_proof ~expect:true __LINE__ prelude0
     {|(quip 1
        (with ((fa (f1 a)))
        (steps () (
        (stepc c0 (cl (= (f1 b) a)) (assert-c (@ c0)))
        (stepc c1 (cl (p1 fa)) (assert-c (@ c1)))
        (stepc c2 (cl (= b a)) (assert-c (@ c2)))
        (stepc c3 (cl (not (p1 b))) (assert-c (@ c3)))
        (stepc lemma
         (cl (not (p1 fa)) (not (= (f1 b) a)) (not (= b a)) (p1 b))
         (ccl (@ lemma)))
        (stepc c4 (cl) (hres (@ lemma) ((r1 (@ c3)) (r1 (@ c2)) (r1 (@ c1)) (r1 (@ c0)))))
    ))))|};
    (* more CC *)
    test_proof ~expect:true __LINE__ prelude0
      {|
      (quip 1
      (steps()(
      (stepc c0
        (cl
          (not (= (f2 a b) c))
          (not (= d (f2 a b)))
          (= d c))
        (ccl (@ c0)))
      )))
      |};
    (* more CC *)
    test_proof ~expect:true __LINE__ prelude0
      {|
      (quip 1
      (steps()(
      (stepc c0
        (cl
          (= c b)
          (not (= (f2 a b) b))
          (not (= c (f2 a b))))
        (ccl (@ c0)))
      )))
      |};
    (* bad CC lemma *)
    test_proof ~expect:false __LINE__ prelude0
     {|(quip 1 (steps () (
        (stepc lemma
         (cl (- (p1 (f1 a))) (- (= (f1 b) a)) (- (= c a)) (+ (p1 b)))
         (ccl (@ lemma)))
       )))|};
    (* big CC lemma *)
    test_proof ~expect:true __LINE__ {|
      (declare-sort U 0)
      (declare-fun c2 () U)
      (declare-fun c3 () U)
      (declare-fun c4 () U)
      (declare-fun f1 (U U) U)
      (declare-fun c_0 () U)
      (declare-fun c_4 () U)
      (declare-fun c_1 () U)
      (declare-fun c_2 () U)
      (declare-fun c_3 () U)
      |}
      {|
      (quip 1 (steps () (
      (stepc lemma
      (cl
        (= (f1 c2 (f1 c3 (f1 c2 c4))) (f1 (f1 (f1 c4 c3) c3) c2))
        (not (= c4 c_3))
        (not (= c3 c_2))
        (not (= c2 c_1))
        (not (= (f1 c_3 c_3) c_0))
        (not (= (f1 c_3 c_2) c_1))
        (not (= (f1 c_3 c_1) c_0))
        (not (= (f1 c_3 c_0) c_1))
        (not (= (f1 c_2 c_0) c_1))
        (not (= (f1 c_1 c_2) c_1))
        (not (= (f1 (f1 c_3 (f1 c_3 (f1 c_3 c_3))) (f1 c_3 (f1 c_3 c_2))) c_3))
        (not (= (f1 (f1 c_3 (f1 c_3 (f1 c_0 c_0))) (f1 c_0 (f1 c_3 c_3))) c_0))
      )
      (ccl (@ lemma))))))
      |};
    (* basic subst *)
    test_proof ~expect:true __LINE__ prelude0
     {|(quip 1 (steps () (
        (stepc c0 (cl (= (f2 (? x U) b) (? x U))) (assert-c (@ c0)))
        (stepc c2 (cl (p1 (f2 a b))) (assert-c (@ c2)))
        (stepc c3 (cl (not (p1 a))) (assert-c (@ c3)))
        (stepc c4 (cl (= (f2 a b) a)) (subst (x a) (ref c0)))
        (stepc c5
          (cl (not (= (f2 a b) a)) (not (p1 (f2 a b))) (p1 a)) (ccl (@ c5)))
        (stepc c6 (cl)
          (hres (@ c5) ((r1 (@ c4)) (r1 (@ c3)) (r1 (@ c2)))))
    )))|};
    (* self contained proof *)
    test_proof ~expect:true __LINE__ ""
    {|(quip 1)
      (ty_decl u 0)
      (decl a u)
      (decl b u)
      (decl c u)
      (decl p1 (-> u Bool))
      (decl f1 (-> u u))
      (stepc lemma
       (cl (not (p1 (f1 a))) (not (= (f1 a) c)) (not (= c b)) (p1 b))
       (ccl (@ lemma)))
    |}
  ]

  let suite =
    "quip" >::: l
end


let () =
  let module M = Make() in
  OUnit2.run_test_tt_main M.suite
