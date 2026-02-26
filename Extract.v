From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
From Coq Require Import List.
Extraction Language OCaml.
Require Import DisQ.BasicUtility.
Require Import DisQ.DisQSyntax.

Extraction Blacklist List String Bool.


Set Extraction AutoInline.
Set Extraction Optimize.
Unset Extraction KeepSingleton.

Require Import DisQ.AUTO.
Require Import DisQ.AUTO_Test.

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
qubits_of_range
qubits_of_locus
 qubits_of_exp
 qubits_of_cexp
qubits_of_cdexp
qubits_of_myOp
qubits_of_ops
 shares_any_qubit
 P_1 P_3 P_4 P_5 P_6
Shor_Qprog_64 
 phase_qubits64
appRQFT64
phase_bits64 
apply_H_all_from
alloc_qubits_from
Shor_Qprog.






















