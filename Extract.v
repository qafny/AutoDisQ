
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

(* Make sure the extracted OCaml is linked with Zarith. *)
Extract Constant Q => "Zarith.Q.t".

(* Base constants *)
Extract Constant QArith_base.Q0 => "Zarith.Q.zero".
Extract Constant QArith_base.Q1 => "Zarith.Q.one".

(* Arithmetic *)
Extract Constant Qplus  => "Zarith.Q.add".
Extract Constant Qmult  => "Zarith.Q.mul".
Extract Constant Qminus => "Zarith.Q.sub".
Extract Constant Qopp   => "Zarith.Q.neg".
Extract Constant Qdiv   => "Zarith.Q.div".
Extract Constant Qinv   => "Zarith.Q.inv".

(* Boolean comparisons *)
Extract Constant Qeq_bool => "Zarith.Q.equal".
Extract Constant Qlt_bool => "Zarith.Q.lt".
Extract Constant Qle_bool => "Zarith.Q.le".
Extract Constant Qgt_bool => "Zarith.Q.gt".
Extract Constant Qge_bool => "Zarith.Q.ge".

(* Total order compare (handy for sorting) *)
Extract Constant Qcompare => "Zarith.Q.compare".

(* Optional conversions (ONLY keep if you actually use them) *)
Extract Constant inject_Z => "Zarith.Q.of_bigint".

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









