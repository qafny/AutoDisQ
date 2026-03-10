
From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt.
From Coq Require Import List.
From Coq Require Import QArith.              (* <-- ADD *)
From Coq Require Import ExtrOcamlZInt.       (* <-- ADD (useful for Z / bigints) *)

Extraction Language OCaml.

Require Import DisQ.BasicUtility.
Require Import DisQ.DisQSyntax.
Require Import DisQ.AUTO.
Require Import DisQ.AUTO_Test.

Extraction Blacklist List String Bool.

Set Extraction AutoInline.
Set Extraction Optimize.
Unset Extraction KeepSingleton.

(* ============================================================ *)
(* CRITICAL FIX: map nat to OCaml int + replace Nat operations   *)
(* ============================================================ *)

Extract Constant Nat.gcd => "Stdlib.gcd".
Extract Constant Nat.modulo => "( mod )".
Extract Constant Nat.div => "( / )".
Extract Constant Nat.odd => "(fun n -> (n land 1) = 1)".
Extract Constant Nat.even => "(fun n -> (n land 1) = 0)".
Extract Constant Nat.pow => "(fun a b -> int_of_float ((float_of_int a) ** (float_of_int b)))".

(* Map Coq nat to OCaml int *)
Extract Inductive nat => "int"
  [ "0" "Stdlib.succ" ]
  "(fun fO fS n -> if n = 0 then fO () else fS (n - 1))".

(* Map Nat ops to OCaml int ops *)
Extract Constant Nat.add => "( + )".
Extract Constant Nat.mul => "( * )".
(* Saturating subtraction is safer for nat semantics *)
Extract Constant Nat.sub =>
  "(fun a b -> let d = a - b in if d < 0 then 0 else d)".
Extract Constant Nat.leb => "( <= )".
Extract Constant Nat.ltb => "( < )".
Extract Constant Nat.eqb => "( = )".

(* ============================================================ *)
(* NEW: Q (rationals) extraction to Zarith.Q.t                   *)
(* ============================================================ *)
Require Import QArith.
From Coq Require Import Extraction.

Extract Inductive Q =>
  "Q.t"
  [ "Q.make" ].


(* Arithmetic *)
Extract Constant Qplus  => "Zarith.Q.add".
Extract Constant Qmult  => "Zarith.Q.mul".
Extract Constant Qminus => "Zarith.Q.sub".
Extract Constant Qopp   => "Zarith.Q.neg".
Extract Constant Qdiv   => "Zarith.Q.div".
Extract Constant Qinv   => "Zarith.Q.inv".

(* Boolean comparisons *)
Extract Constant Qeq_bool => "Zarith.Q.equal".

Require Import QArith.
Require Import QMicromega.

(* Boolean comparisons *)
Extract Constant Qeq_bool => "Q.equal".
Extract Constant Qlt_bool => "Q.lt".
Extract Constant Qle_bool => "Q.le".

(* Define these in Coq, then extract them *)
Definition Qgtb (x y : Q) : bool := Qlt_bool y x.
Definition Qgeb (x y : Q) : bool := Qle_bool y x.

Extract Constant Qgtb => "Q.gt".
Extract Constant Qgeb => "Q.ge".

(* Total order compare *)
Extract Constant Qcompare => "Q.compare".

(* Integer -> rational *)
Extract Constant inject_Z => "Q.of_bigint".

(* Total order compare (handy for sorting) *)
Extract Constant Qcompare => "Zarith.Q.compare".

(* Optional conversions (ONLY keep if you actually use them) *)
Extract Constant inject_Z => "Zarith.Q.of_bigint".

(* ============================================================ *)
(* Extraction targets                                            *)
(* ============================================================ *)

Extraction
  "autodisq_extract.ml"

    list_eqb
  aexp_eqb
  cbexp_eqb
  range_eqb
  locus_eqb
  exp_eqb
  nat_range_inter
  nat_range_sub
  range_intersect
  same_name
  intersect'
  intersect
  get_locus
  get_loci
  get_vars_cexp
  get_vars_aexp
  get_vars_bexp
  is_inter
  inter_vars
  opListOrder
  gen_hb_single
  gen_next
  empty_hp
  gen_hb'
  gen_hb_a
  gen_hb
  sim_exp
  sim_cexp
  sim_myop
  insert_op
  partition_op
  insert_all
  permutations
  car_concat'
  car_concat
  get_first
  grab_related'
  grab_related
  grab_nums
  in_list'
  in_list
  up_qubits
  cutToQubits
  get_locus_in_op
  get_nlocus
  insert_back
  assign_each
  gen_seq
  count_a
  gen_mem_new
  sub_locus'
  sub_locus
  split_nat_range
  assemble_range
  sublist_posi
  set_inter
  sub_locus_i
  isSend
  no_send_check
  search_hb
  search_mem
  max_one
  search_good_mem
  find_least_q'
  find_least_q
  subtract_aux
  subtract_posi
  subtract_all
  add_posi_true'
  add_true
  add_posi_true
  turn_true_aux
  turn_true
  find_all_in
  search_all_mem
  gen_comm'
  gen_comm
  assign_mem_s
  assign_mem'
  assign_mem_more
  turn_new
  gen_mem
  insert_mem_id
  distribute_op
  get_op
  turn_cexp_to_proc
  turn_op_to_proc
  to_process
  to_prog
  gen_prog
  count_send_in_process
  count_send_in_memb
  count_comm_ops
  process_size
  memb_load
  max_load
  fit
  best_prog_aux
  best_prog
  autodisq_all
  autodisq_best
  auto_disq_loop
  autodisq_best_1
  GHZ8_prog
  GHZ16_prog
  SHOR8_prog
  SHOR16_prog
  QFT8_prog
  QFT16_prog
  QFTAdder8_prog
  QFTAdder16_prog
  QFT32_prog
  QFTAdder32_prog
  GHZ32_prog.


















(*
From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt.
From Coq Require Import List.

Extraction Language OCaml.

Require Import DisQ.BasicUtility.
Require Import DisQ.DisQSyntax.
Require Import DisQ.AUTO.
Require Import DisQ.AUTO_Test.

Extraction Blacklist List String Bool.

Set Extraction AutoInline.
Set Extraction Optimize.
Unset Extraction KeepSingleton.

(* ============================================================ *)
(* CRITICAL FIX: map nat to OCaml int + replace Nat operations   *)
(* ============================================================ *)

Extract Constant Nat.gcd => "Stdlib.gcd".
Extract Constant Nat.modulo => "( mod )".
Extract Constant Nat.div => "( / )".
Extract Constant Nat.odd => "(fun n -> (n land 1) = 1)".
Extract Constant Nat.even => "(fun n -> (n land 1) = 0)".
Extract Constant Nat.pow => "(fun a b -> int_of_float ((float_of_int a) ** (float_of_int b)))".

(* Map Coq nat to OCaml int *)
Extract Inductive nat => "int"
  [ "0" "Stdlib.succ" ]
  "(fun fO fS n -> if n = 0 then fO () else fS (n - 1))".

(* Map Nat ops to OCaml int ops *)
Extract Constant Nat.add => "( + )".
Extract Constant Nat.mul => "( * )".
(* Saturating subtraction is safer for nat semantics *)
Extract Constant Nat.sub =>
  "(fun a b -> let d = a - b in if d < 0 then 0 else d)".
Extract Constant Nat.leb => "( <= )".
Extract Constant Nat.ltb => "( < )".
Extract Constant Nat.eqb => "( = )".

(* ============================================================ *)
(* Extraction targets                                            *)
(* ============================================================ *)

Extraction
  "autodisq_extract.ml"
  qubits_of_range
  qubits_of_locus
  qubits_of_cexp
  qubits_of_myOp
  auto_disq_alg1_paper
  gen_prog_alg2
  gen_prog_loop_alg2
  gen_prog_paper
  auto_parallelize_alg3
  auto_parallelize_alg3_layers
  gen_hp
  gen_mem_seed
  gen_seq_many
  fit
  order_by_seq
  insert_send_recv
  place_operation
  place_reloc
  diff_mem
  mem_up_smap
  scc_partition_fuel
  scc_partition
  remove_ops
  has_pred
  ready
  pick_ready
  layer_partition_fuel
  layer_partition
  alg3_loop
  alg3_loop_fold
  find_period_exact
  shor_factors_from_r
  pow_mod
  qubits_of_exp
  qubits_of_cdexp
  qubits_of_ops
  shares_any_qubit
  P_1 P_3 P_4 P_5 P_6
  Shor_Qprog_64
  phase_qubits64
  appRQFT64
  phase_bits64
  apply_H_all_from
  alloc_qubits_from
  Shor_Qprog
  QFT32_dist0
  GHZ32_best
  GHZ32_prog
  QFT64_prog
  Shor_Qprog32.





























*)









