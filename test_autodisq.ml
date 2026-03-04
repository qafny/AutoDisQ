(* test_autodisq.ml
   OUnit2 unit tests for your extracted AutoDisQ code.

   Install:
     opam install ounit2

   Build (no dune):
     ocamlfind ocamlc -package ounit2 -linkpkg autodisq_extract.ml test_autodisq.ml -o test_autodisq
   Run:
     ./test_autodisq
*)

open OUnit2
open Autodisq_extract

(* ---------- Helpers: config/memb inspection (no printing) ---------- *)

let cfg2 : config = [Memb (0, []); Memb (1, [])]

let memb_id = function
  | Memb (id, _) -> id
  | LockMemb (id, _, _) -> id

let memb_processes = function
  | Memb (_, ps) -> ps
  | LockMemb (_, _, ps) -> ps

let cfg_ids (cfg:config) : int list =
  List.map memb_id cfg

let get_memb (id:int) (cfg:config) =
  try Some (List.find (fun m -> memb_id m = id) cfg)
  with Not_found -> None

let count_procs_in_memb (id:int) (cfg:config) : int =
  match get_memb id cfg with
  | None -> 0
  | Some m -> List.length (memb_processes m)

let total_procs (cfg:config) : int =
  List.fold_left (fun acc m -> acc + List.length (memb_processes m)) 0 cfg

let is_finite_cost (z:int) : bool =
  (* fit is nat in Coq, extracted as int >= 0 in practice; we just check nonneg here. *)
  z >= 0

(* ---------- Shared compiler settings (as you had) ---------- *)

let seq0 : seq_relation = fun _ -> 0
let moQ0 : qubit_mem_assign = fun _ -> 0
let moO_const (k:int) : op_mem_assign = fun _ -> k

(* ---------- Unit tests ---------- *)

(* Alg2: gen_prog_paper returns a config whose membrane IDs should match cfg2's IDs
   IF you post-process into the same 2-membrane universe.
   Since gen_prog_paper itself returns a distributed_prog, and in your harness
   you treat it like a config, we can at least check it is a list of membs
   and IDs are consistent when mem is 0 or 1. *)
let test_alg2_preserves_ids (pname:string) (p:op_list) =
  (pname ^ " preserves memb ids") >:: (fun _ ->
    let prog0 = gen_prog_paper seq0 moQ0 (moO_const 0) p in
    let prog1 = gen_prog_paper seq0 moQ0 (moO_const 1) p in
    assert_bool "prog0 ids should include 0" (List.mem 0 (cfg_ids prog0));
    assert_bool "prog1 ids should include 1" (List.mem 1 (cfg_ids prog1))
  )

(* Alg2: if we force all ops to membrane k, then membrane k should have >= 1 process
   (assuming p is non-empty). This is a reasonable regression check. *)
let test_alg2_places_something_on_mem (pname:string) (p:op_list) (mem:int) =
  (Printf.sprintf "%s places ops on mem%d" pname mem) >:: (fun _ ->
    let prog = gen_prog_paper seq0 moQ0 (moO_const mem) p in
    assert_bool "forced membrane should contain at least one process"
      (count_procs_in_memb mem prog > 0)
  )

(* Alg2: cost should be non-negative *)
let test_alg2_cost_nonneg (pname:string) (p:op_list) (mem:int) =
  (Printf.sprintf "%s alg2 cost >= 0 on mem%d" pname mem) >:: (fun _ ->
    let prog = gen_prog_paper seq0 moQ0 (moO_const mem) p in
    assert_bool "fit(prog) should be >= 0" (is_finite_cost (fit prog))
  )

(* Alg1: auto_disq_alg1_paper should return a config with the same membrane IDs as input cfg2
   (this is a typical invariant for a compiler/placer: it uses available membranes). *)
let test_alg1_preserves_cfg_ids (pname:string) (p:op_list) (kseq:int) (kmem:int) =
  (Printf.sprintf "%s alg1 preserves cfg2 ids" pname) >:: (fun _ ->
    let prog = auto_disq_alg1_paper kseq kmem p cfg2 in
    assert_equal
      ~msg:"returned config should keep same membrane ids as cfg2"
      (List.sort compare (cfg_ids cfg2))
      (List.sort compare (cfg_ids prog))
  )

(* Alg1: cost should be non-negative *)
let test_alg1_cost_nonneg (pname:string) (p:op_list) (kseq:int) (kmem:int) =
  (Printf.sprintf "%s alg1 cost >= 0" pname) >:: (fun _ ->
    let prog = auto_disq_alg1_paper kseq kmem p cfg2 in
    assert_bool "fit(prog) should be >= 0" (is_finite_cost (fit prog))
  )

(* Optional: Alg1 should produce *some* processes for non-empty programs (regression check). *)
let test_alg1_nonempty_output (pname:string) (p:op_list) (kseq:int) (kmem:int) =
  (Printf.sprintf "%s alg1 produces some processes" pname) >:: (fun _ ->
    let prog = auto_disq_alg1_paper kseq kmem p cfg2 in
    assert_bool "total processes should be > 0" (total_procs prog > 0)
  )

(* ---------- Build the suite (matches your harness coverage) ---------- *)

let suite =
  "AutoDisQ_Extracted_Tests" >::: [

    (* -------- Algorithm 2: fixed placement tests -------- *)
    test_alg2_preserves_ids "P_1" p_1;
    test_alg2_places_something_on_mem "P_1" p_1 0;
    test_alg2_places_something_on_mem "P_1" p_1 1;
    test_alg2_cost_nonneg "P_1" p_1 0;
    test_alg2_cost_nonneg "P_1" p_1 1;

    (* P_3 *)
    test_alg2_preserves_ids "P_3" p_3;
    test_alg2_places_something_on_mem "P_3" p_3 0;
    test_alg2_places_something_on_mem "P_3" p_3 1;
    test_alg2_cost_nonneg "P_3" p_3 0;
    test_alg2_cost_nonneg "P_3" p_3 1;

    (* P_4 *)
    test_alg2_preserves_ids "P_4" p_4;
    test_alg2_places_something_on_mem "P_4" p_4 0;
    test_alg2_places_something_on_mem "P_4" p_4 1;
    test_alg2_cost_nonneg "P_4" p_4 0;
    test_alg2_cost_nonneg "P_4" p_4 1;
    test_alg2_cost_nonneg "P_4" p_4 5;

    (* P_5 (Grover) *)
    test_alg2_preserves_ids "P_5" p_5;
    test_alg2_cost_nonneg "P_5" p_5 0;
    test_alg2_cost_nonneg "P_5" p_5 5;

    (* P_6 (Teleport) *)
    test_alg2_preserves_ids "P_6" p_6;
    test_alg2_cost_nonneg "P_6" p_6 0;
    test_alg2_cost_nonneg "P_6" p_6 5;

    (* -------- Algorithm 1: auto search tests -------- *)
    (* Keep kseq/kmem small as you said (3,3). *)
    test_alg1_preserves_cfg_ids "P_1" p_1 3 3;
    test_alg1_cost_nonneg        "P_1" p_1 3 3;
    test_alg1_nonempty_output    "P_1" p_1 3 3;

    test_alg1_preserves_cfg_ids "P_3" p_3 3 3;
    test_alg1_cost_nonneg        "P_3" p_3 3 3;
    test_alg1_nonempty_output    "P_3" p_3 3 3;

    test_alg1_preserves_cfg_ids "P_4" p_4 3 3;
    test_alg1_cost_nonneg        "P_4" p_4 3 3;
    test_alg1_nonempty_output    "P_4" p_4 3 3;

    test_alg1_preserves_cfg_ids "P_5" p_5 3 3;
    test_alg1_cost_nonneg        "P_5" p_5 3 3;
    test_alg1_nonempty_output    "P_5" p_5 3 3;

    test_alg1_preserves_cfg_ids "P_6" p_6 3 3;
    test_alg1_cost_nonneg        "P_6" p_6 3 3;
    test_alg1_nonempty_output    "P_6" p_6 3 3;
  ]

let () =
  run_test_tt_main suite

