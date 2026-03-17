
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

  myOp myOpAux
  opListOrder
  gen_hb
  gen_seq
  gen_mem
  gen_prog
  fit
  best_prog
  autodisq_all
  autodisq_best
  assign_mem_s
  assign_mem_more
  gen_mem_new
  scored_candidates
  gen_comm
  post_dec
  lower_solution_distributed_go
  lower_solution_distributed
  autodisq_first
  autodisq_best_1.






























