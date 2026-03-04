
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















(*


(* ExtractSingle.v *)

From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt.

(* Import the whole executable pipeline *)
Require Import BasicUtility.
Require Import DisQSyntax.
Require Import Auto_1.

Extraction Language OCaml.

(* Avoid re-extracting Coq stdlib *)
Extraction Blacklist String List Nat Bool.

(* SINGLE FILE extraction *)
Extraction "autodisq_5.ml"
  auto_disq
  auto_disq_search
  gen_prog
  gen_prog_core
  parallelize_in_membrane.
Print insert_teleport_sends.
Print place_operation.
Print vars_of_exp.
Print compute_scc.

(*
(* SINGLE FILE extraction *)
Extraction "autodisq_4.ml"
  auto_disq
  auto_disq_search
  gen_prog
  gen_prog_core
  parallelize_in_membrane.




From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt.

Extraction Language OCaml.
Extraction Blacklist String List Nat Bool.

Extraction Language OCaml.
Set Extraction Optimize.
Set Extraction AutoInline.

Require Import AUTO.
Cd "extracted".
Extraction "autodisq.ml"
  AUTO.auto_disq
  AUTO.auto_disq_search
 AUTO.gen_prog
AUTO.gen_prog_core
AUTO.parallelize_in_membrane.
*)

