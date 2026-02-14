From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
From Coq Require Import List.
Extraction Language OCaml.
Require Import DisQ.BasicUtility.
Require Import DisQ.DisQSyntax.

Extraction Blacklist List String Nat Bool.

Set Extraction AutoInline.
Set Extraction Optimize.
Unset Extraction KeepSingleton.

Require Import AUTO.

Extraction
  "autodisq_extract.ml"
  auto_disq_alg1_paper
  gen_prog_alg2
  gen_prog_loop_alg2
  auto_parallelize_alg3
  gen_hp
  gen_mem_seed
  gen_seq_many
  fit
  order_by_seq
  place_operation
  place_reloc
  insert_send
  insert_rev
  diff_mem
  mem_up_smap
  alg3_loop
scc_partition_fuel
  scc_partition.





















(*

From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
From Coq Require Import List.
Import ListNotations.

(* Import your algorithm file *)
Require Import AUTO.

(* If DisQ modules define extra stuff, import them too (optional) *)
Require Import DisQ.BasicUtility.
Require Import DisQ.DisQSyntax.

(* Make extracted OCaml cleaner/faster *)
Set Extraction Optimize.
Set Extraction AutoInline.

(* Optional: avoid name clashes with OCaml stdlib identifiers *)
Extraction Blacklist List String Nat Bool.
Search "auto_disq".
Locate "auto_disq_alg1_paper".
(* Extract ONLY the executable entry point(s) you want *)
Extraction "autodisq_alg1_paper.ml"
auto_disq_alg1_paper
  gen_hp
  gen_seq_many
  gen_mem_seed
  gen_prog
  fit.
*)

(*
From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt.

(* Import the file that defines the algorithm *)
Require Import AUTO.

Extraction Language OCaml.

(* Improve extraction quality *)
Set Extraction AutoInline.


(* Extract top-level executable functions *)
Extraction "autodisq.ml"
  AUTO.auto_disq
  AUTO.auto_disq_search
  AUTO.gen_prog
  AUTO.gen_prog_core
  AUTO.parallelize_in_membrane.


*)




