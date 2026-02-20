From Coq Require Import List Arith Bool Nat.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DisQ.BasicUtility.   (* var := nat *)
Require Import DisQ.DisQSyntax.     (* exp, process, memb, config, ... *)
Require Import DisQ.AUTO.
Require Import Coq.Program.Wf.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.


Definition cfg1 : config := [Memb 0 []; Memb 1 []].

Definition op1 : myOp := OpAP (CNew 0 1).
Definition op2 : myOp := OpAP (CMeas 0 ([] : locus)).
Definition R1  : op_list := [op1; op2].

Definition P1 : distributed_prog :=
  auto_disq_alg1_paper 2 2 R1 cfg1.

Compute P1.

Compute fit P1.

Definition cfg_test : config := [Memb 0 []; Memb 1 []].

Definition S_empty : Smap := [].

Definition T1 :=
  insert_send_recv cfg_test S_empty 1 0.

Compute T1.

Definition S_one : Smap := [(0, 0)].

Definition T2 :=
  insert_send_recv cfg_test S_one 1 0.

Compute T2.


Definition S_two : Smap := [(0,0); (1,0)].
Definition T3 := insert_send_recv cfg_test S_two 1 0.
Compute T3.
Definition memb_procs (m : memb) : list process :=
  match m with
  | Memb _ ps => ps
  | LockMemb _ _ ps => ps
  end.

Fixpoint flatten_config (cfg : config) : list process :=
  match cfg with
  | [] => []
  | m :: tl => memb_procs m ++ flatten_config tl
  end.

Compute flatten_config (fst T2).
Definition opAP1 : myOp := OpAP (CNew 0 1).

Definition moQ0 : var -> membrane_id := fun _ => 0.
Definition moO_to_1 : myOp -> membrane_id := fun _ => 1.

Definition TB :=
  gen_prog_loop_alg2 ([opAP1] : list myOp) moQ0 moO_to_1 empty_config 0.

Compute TB.
Compute flatten_config TB.

Definition cond0 : cbexp := CEq (BA 0) (Num 0).

Definition p_then : process := AP (CNew 0 1) PNil.
Definition p_else : process := PNil.

Definition opIF1 : myOp := OpIf cond0 p_then p_else.

Definition TC :=
  gen_prog_loop_alg2 ((opIF1 :: nil) : list myOp) moQ0 moO_to_1 empty_config 0.


Compute TC.
Compute flatten_config TC.

Definition opAP2 : myOp := OpAP (CMeas 0 ([] : locus)).
Definition seq2 : list myOp := [opAP1; opAP2].

Definition TD :=
  gen_prog_alg2 seq2 moQ0 moO_to_1.

Compute TD.
Compute flatten_config TD.
Compute diff_mem moQ0 (locus_myOp opAP1) 1.
Compute diff_mem (mem_up_smap moQ0 (diff_mem moQ0 (locus_myOp opAP1) 1) 1)
                (locus_myOp opAP2) 1.

(* ============================================================ *)
(* Tests for Algorithm 1                                         *)
(* ============================================================ *)

Definition cfgA : config := [Memb 0 []; Memb 1 []].

(* Simple: two ops share qubit 0 *)
Definition Aop1 : myOp := OpAP (CNew 0 1).
Definition Aop2 : myOp := OpAP (CMeas 0 ([] : locus)).
Definition AR1  : op_list := [Aop1; Aop2].

Definition AP1 : distributed_prog :=
  auto_disq_alg1_paper 2 2 AR1 cfgA.

Compute AP1.
Compute fit AP1.

Definition Aop3 : myOp := OpAP (CNew 1 1).
Definition Aop4 : myOp := OpDP (NewCh 7 1).
Definition AR2  : op_list := [Aop1; Aop3; Aop4; Aop2].

Definition AP2 : distributed_prog :=
  auto_disq_alg1_paper 3 3 AR2 cfgA.

Compute AP2.
Compute fit AP2.

(* ============================================================ *)
(* Tests for Algorithm 2                                         *)
(* ============================================================ *)

Definition seq0 : seq_relation := fun _ => 0.

Definition moO_all0 : op_mem_assign := fun _ => 0.
Definition moQ_all0 : qubit_mem_assign := fun _ => 0.

Definition P2A : distributed_prog :=
  gen_prog_paper seq0 moQ_all0 moO_all0 AR1.

Compute P2A.
Compute fit P2A.  

Definition moO_all1 : op_mem_assign := fun _ => 1.
Definition moQ_all0_again : qubit_mem_assign := fun _ => 0.

Definition P2B : distributed_prog :=
  gen_prog_paper seq0 moQ_all0_again moO_all1 AR1.

Compute P2B.
Compute fit P2B.  

Fixpoint flat_cfg (cfg : config) : list process :=
  match cfg with
  | [] => []
  | Memb _ ps :: tl => ps ++ flat_cfg tl
  | LockMemb _ _ ps :: tl => ps ++ flat_cfg tl
  end.

Compute flat_cfg P2A.
Compute flat_cfg P2B.




(* ============================================================ *)
(* Tests for Algorithm 3                                         *)
(* ============================================================ *)

Definition B1 : myOp := OpAP (CNew 0 1).
Definition B2 : myOp := OpAP (CMeas 0 ([] : locus)).
Definition B3 : myOp := OpAP (CNew 1 1).

Definition Bops : list myOp := [B1; B2; B3].

(* A custom hp that creates a cycle B1 <-> B2, and B2 -> B3 *)
Definition hpB : hb_relation :=
  fun a b =>
    orb
      (orb (andb (myOp_eqb a B1) (myOp_eqb b B2))
           (andb (myOp_eqb a B2) (myOp_eqb b B1)))
      (andb (myOp_eqb a B2) (myOp_eqb b B3)).

(* A seq that orders B1 then B2 then B3 *)
Definition seqB : seq_relation :=
  fun o =>
    if myOp_eqb o B1 then 0
    else if myOp_eqb o B2 then 1
    else 2.

Definition Rpar : list process :=
  auto_parallelize_alg3 myOp_eqb Bops hpB seqB.

Compute Rpar.


(* --------------------------------------------- *)
(* Example quantum program in your input format  *)
(* --------------------------------------------- *)

Definition q0 : var := 0.
Definition q1 : var := 1.

(* empty locus for “apply U on these qubits” — depends on your DisQSyntax meaning *)
Definition L : locus := ([] : locus).

(* exp programs (unitary-ish) *)
Definition eH_q0 : exp := H q0 (Num 0).
Definition eX_q1 : exp := X q1 (Num 0).

(* “Controlled-X on q1 controlled by q0”  *)
Definition eCX : exp := CU q0 (Num 0) eX_q1.

(* Wrap into cexp actions: CAppU locus exp *)
Definition appH_q0 : cexp := CAppU L eH_q0.
Definition appCX   : cexp := CAppU L eCX.

(* Allocate 1-qubit registers (your CNew takes x and n) *)
Definition new_q0 : cexp := CNew q0 1.
Definition new_q1 : cexp := CNew q1 1.

(* Measure q0 and q1 into classical x0 and x1 *)
Definition x0 : var := 10.
Definition x1 : var := 11.

Definition meas_q0 : cexp := CMeas x0 L.
Definition meas_q1 : cexp := CMeas x1 L.

(* Now the program as op_list *)
Definition Qprog : op_list :=
  [ OpAP new_q0;
    OpAP new_q1;
    OpAP appH_q0;
    OpAP appCX;
    OpAP meas_q0;
    OpAP meas_q1
  ].

Definition cfg2 : config := [Memb 0 []; Memb 1 []].
Definition Pbest : distributed_prog :=
  auto_disq_alg1_paper 3 3 Qprog cfg2.

Compute Pbest.
Compute fit Pbest.


Definition P_alg2 : distributed_prog :=
  gen_prog_paper seq0 moQ_all0 moO_all0 Qprog.

Compute P_alg2.
Compute fit P_alg2.

Definition moQ_start0 : qubit_mem_assign := fun _ => 0.


Definition P_reloc : distributed_prog :=
  gen_prog_paper seq0 moQ_start0 moO_all1 Qprog.

Compute P_reloc.
Compute fit P_reloc.


Definition P1_q : var := 0.
Definition P1_x : var := 10.

Definition P_1 : op_list :=
  [ OpAP (CNew P1_q 1);
    OpAP (CAppU L (H P1_q 0));
    OpAP (CMeas P1_x L)
  ].


(* Test harness *)


Definition moO0 : op_mem_assign := fun _ => 0.

Definition P_1_dist0 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO0 P_1.

Compute P_1_dist0.
Compute fit P_1_dist0.

Definition moO1 : op_mem_assign := fun _ => 1.

Definition P_1_dist1 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO1 P_1.

Compute P_1_dist1.
Compute fit P_1_dist1.

Definition P_2_q : var := 0.
Definition P_2_x : var := 10.

Definition P_2 : op_list :=
  [ OpAP (CNew P_2_q 1);
    OpAP (CAppU L (H P_2_q 0));
    OpAP (CAppU L (RZ 0 P_2_q 0));
    OpAP (CMeas P_2_x L)
  ].

Definition P_2_dist0 :=
  gen_prog_paper seq0 moQ0 moO0 P_2.

Compute P_2_dist0.
Compute fit P_2_dist0.

(* 6 membranes available *)
Definition cfg6 : config :=
  [ Memb 0 []; Memb 1 []; Memb 2 []; Memb 3 []; Memb 4 []; Memb 5 [] ].

(* initial location: all qubits start on membrane 0 *)


(* send all operations to a chosen membrane *)
Definition moO2 : op_mem_assign := fun _ => 2.
Definition moO3 : op_mem_assign := fun _ => 3.
Definition moO4 : op_mem_assign := fun _ => 4.
Definition moO5 : op_mem_assign := fun _ => 5.

(* Algorithm 2 placement tests for P_1 *)
Definition P_1_dist2 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO2 P_1.
Compute P_1_dist2.
Compute fit P_1_dist2.

Definition P_1_dist3 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO3 P_1.
Compute P_1_dist3.
Compute fit P_1_dist3.

Definition P_1_dist4 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO4 P_1.
Compute P_1_dist4.
Compute fit P_1_dist4.

Definition P_1_dist5 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO5 P_1.
Compute P_1_dist5.
Compute fit P_1_dist5.

Definition P_3_q0 : var := 0.
Definition P_3_q1 : var := 1.
Definition P_3_q2 : var := 2.

Definition P_3_x0 : var := 10.
Definition P_3_x1 : var := 11.
Definition P_3_x2 : var := 12.

(* CNOT-like: control P_3_q0, apply X on target *)
Definition CX_01 : exp := CU P_3_q0 0 (X P_3_q1 0).
Definition CX_02 : exp := CU P_3_q0 0 (X P_3_q2 0).

Definition P_3 : op_list :=
  [ OpAP (CNew P_3_q0 1);
    OpAP (CNew P_3_q1 1);
    OpAP (CNew P_3_q2 1);

    OpAP (CAppU L (H P_3_q0 0));
    OpAP (CAppU L CX_01);
    OpAP (CAppU L CX_02);

    OpAP (CMeas P_3_x0 L);
    OpAP (CMeas P_3_x1 L);
    OpAP (CMeas P_3_x2 L)
  ].


Definition P_3_dist0 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO0 P_3.

Compute P_3_dist0.
Compute fit P_3_dist0.


Definition P_3_dist1 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO1 P_3.

Compute P_3_dist1.
Compute fit P_3_dist1.

(* QFT *)

Definition P_4_q : var := 0.
Definition P_4_n : nat := 3.
Definition P_4_x : var := 10.

Definition P_4 : op_list :=
  [ OpAP (CNew P_4_q 1);
    OpAP (CAppU L (H P_4_q 0));
    OpAP (CAppU L (QFT P_4_q P_4_n));
    OpAP (CAppU L (RQFT P_4_q P_4_n));
    OpAP (CMeas P_4_x L)
  ].



Definition P_4_dist0 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO0 P_4.

Compute P_4_dist0.
Compute fit P_4_dist0.


Definition P_4_dist1 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO1 P_4.

Compute P_4_dist1.
Compute fit P_4_dist1.


Definition P_4_dist5 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO5 P_4.

Compute P_4_dist5.
Compute fit P_4_dist5.

(* ============================================================ *)
(* P_5 : 2-qubit Grover (one iteration)                          *)
(* ============================================================ *)

Definition P_5_q0 : var := 0.
Definition P_5_q1 : var := 1.
Definition P_5_x0 : var := 10.
Definition P_5_x1 : var := 11.

(* a symbolic “pi phase” parameter  *)
Definition theta_pi : nat := 1.

(* Controlled phase-like oracle: control q0, apply RZ on q1 *)
Definition ORACLE_01 : exp := CU P_5_q0 0 (RZ 0 P_5_q1 theta_pi).

(* Diffusion (in the usual circuit form): H,H; X,X; controlled-phase; X,X; H,H *)
Definition P_5 : op_list :=
  [ OpAP (CNew P_5_q0 1);
    OpAP (CNew P_5_q1 1);

    (* Prepare uniform superposition *)
    OpAP (CAppU L (H P_5_q0 0));
    OpAP (CAppU L (H P_5_q1 0));

    (* Oracle (phase flip on marked state, here approximated by ORACLE_01) *)
    OpAP (CAppU L ORACLE_01);

    (* Diffusion *)
    OpAP (CAppU L (H P_5_q0 0));
    OpAP (CAppU L (H P_5_q1 0));
    OpAP (CAppU L (X P_5_q0 0));
    OpAP (CAppU L (X P_5_q1 0));
    OpAP (CAppU L ORACLE_01);
    OpAP (CAppU L (X P_5_q0 0));
    OpAP (CAppU L (X P_5_q1 0));
    OpAP (CAppU L (H P_5_q0 0));
    OpAP (CAppU L (H P_5_q1 0));

    (* Measure *)
    OpAP (CMeas P_5_x0 L);
    OpAP (CMeas P_5_x1 L)
  ].


Definition P_5_dist0 := gen_prog_paper seq0 moQ0 moO0 P_5.
Compute P_5_dist0.
Compute fit P_5_dist0.

Definition P_5_dist5 := gen_prog_paper seq0 moQ0 moO5 P_5.
Compute P_5_dist5.
Compute fit P_5_dist5.


(* ============================================================ *)
(* P_6 : Quantum teleportation                                  *)
(* ============================================================ *)

Definition P_6_qs : var := 0.   (* source qubit to teleport *)
Definition P_6_qa : var := 1.   (* Alice half of EPR *)
Definition P_6_qb : var := 2.   (* Bob half of EPR (target) *)

Definition P_6_m1 : var := 10.  (* classical measurement bit from qs *)
Definition P_6_m2 : var := 11.  (* classical measurement bit from qa *)

(* Build the usual CNOTs  *)
Definition CNOT_a_b : exp := CU P_6_qa 0 (X P_6_qb 0).
Definition CNOT_s_a : exp := CU P_6_qs 0 (X P_6_qa 0).

(* “Z correction” approximated via RZ(pi) on qb *)
Definition Zcorr_qb : exp := RZ 0 P_6_qb theta_pi.
Definition Xcorr_qb : exp := X  P_6_qb 0.

(* Processes used in OpIf branches *)
Definition proc_Xcorr : process := AP (CAppU L Xcorr_qb) PNil.
Definition proc_Zcorr : process := AP (CAppU L Zcorr_qb) PNil.

Definition P_6 : op_list :=
  [ (* Allocate qubits *)
    OpAP (CNew P_6_qs 1);
    OpAP (CNew P_6_qa 1);
    OpAP (CNew P_6_qb 1);

    (* Prepare an example “unknown” state on qs *)
    OpAP (CAppU L (H P_6_qs 0));

    (* Create EPR pair between qa and qb *)
    OpAP (CAppU L (H P_6_qa 0));
    OpAP (CAppU L CNOT_a_b);

    (* Bell measurement on (qs, qa) *)
    OpAP (CAppU L CNOT_s_a);
    OpAP (CAppU L (H P_6_qs 0));

    OpAP (CMeas P_6_m1 L);
    OpAP (CMeas P_6_m2 L);

    OpIf (CEq (BA P_6_m2) (Num 1)) proc_Xcorr PNil;
    OpIf (CEq (BA P_6_m1) (Num 1)) proc_Zcorr PNil

  ].

Definition P_6_dist0 := gen_prog_paper seq0 moQ0 moO0 P_6.
Compute P_6_dist0.
Compute fit P_6_dist0.

Definition P_6_dist5 := gen_prog_paper seq0 moQ0 moO5 P_6.
Compute P_6_dist5.
Compute fit P_6_dist5.

(* ============================================================ *)
(* FULL TEST: Shor-like period finding + factor extraction test  *)
(* ============================================================ *)

From Coq Require Import List Arith Bool Nat.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DisQ.BasicUtility.
Require Import DisQ.DisQSyntax.



Inductive myOp : Type :=
| OpAP  (a : cexp)
| OpDP  (a : cdexp)
| OpIf  (b : cbexp) (p q : process).

Definition op_list : Type := list myOp.

(* ------------------------------------------------------------ *)
(* Test instance: N=15, a=2                        *)
(* ------------------------------------------------------------ *)
Definition N : nat := 15.
Definition a : nat := 2.

(* Use t=8 phase bits like your earlier Shor skeleton *)
Definition t_phase : nat := 8.

(* Work register: we will use only 2 qubits (mod 4 period oracle) *)
Definition w0 : var := 20.
Definition w1 : var := 21.
Definition work_qubits : list var := [w0; w1].

(* Phase qubits: 0..7 contiguous so RQFT q0 8 works *)
Definition q2 : var := 2.  Definition q3 : var := 3.
Definition q4 : var := 4.  Definition q5 : var := 5.
Definition q6 : var := 6.  Definition q7 : var := 7.
Definition phase_qubits : list var := [q0;q1;q2;q3;q4;q5;q6;q7].

(* Classical measurement outputs for the phase register *)
Definition c0 : var := 100. Definition c1 : var := 101.
Definition c2 : var := 102. Definition c3 : var := 103.
Definition c4 : var := 104. Definition c5 : var := 105.
Definition c6 : var := 106. Definition c7 : var := 107.
Definition phase_bits : list var := [c0;c1;c2;c3;c4;c5;c6;c7].

(* ------------------------------------------------------------ *)
(* Helpers: allocation / H / measurement                         *)
(* ------------------------------------------------------------ *)
Fixpoint alloc_qubits (qs : list var) : op_list :=
  match qs with
  | [] => []
  | q :: tl => OpAP (CNew q 1) :: alloc_qubits tl
  end.

Fixpoint apply_H_all (qs : list var) : op_list :=
  match qs with
  | [] => []
  | q :: tl => OpAP (CAppU L (H q (Num 0))) :: apply_H_all tl
  end.

Fixpoint meas_all (xs : list var) : op_list :=
  match xs with
  | [] => []
  | x :: tl => OpAP (CMeas x L) :: meas_all tl
  end.

(* ------------------------------------------------------------ *)
(* A REAL, EXECUTABLE oracle : INC mod 4 on (w1 w0)         *)
(* Period is exactly 4.                                         *)
(*   INC: flip LSB (w0), then if w0==0 (i.e. carry) flip MSB.    *)
(* Using your CU + X, a standard reversible incrementer is:      *)
(*   X w0 ; CU w0 (Num 0) (X w1 (Num 0))                         *)
(* This gives a 4-cycle on 2-bit states -> period 4.             *)
(* ------------------------------------------------------------ *)

Definition INC_mod4 : exp :=
  Seq (X w0 (Num 0))
      (CU w0 (Num 0) (X w1 (Num 0))).

Fixpoint repeat_exp (n : nat) (e : exp) : exp :=
  match n with
  | 0 => SKIP 0 (Num 0) (* harmless no-op in your exp grammar *)
  | S n' => Seq e (repeat_exp n' e)
  end.

Definition pow2 (k : nat) : nat := Nat.pow 2 k.

(* “U^(2^k)” for our toy U = INC_mod4 *)
Definition UModExpPow (a N k : nat) (_ws : list var) : exp :=
  repeat_exp (pow2 k) INC_mod4.

Definition controlled_pow (control : var) (k : nat) : op_list :=
  [ OpAP (CAppU L (CU control (Num 0) (UModExpPow a N k work_qubits))) ].

Fixpoint qpe_controlled_pows (qs : list var) (k : nat) : op_list :=
  match qs with
  | [] => []
  | q :: tl => controlled_pow q k ++ qpe_controlled_pows tl (S k)
  end.

Definition inv_qft_phase : op_list :=
  [ OpAP (CAppU L (RQFT q0 t_phase)) ].

(* ------------------------------------------------------------ *)
(* The “Shor/QPE program” we will test structurally              *)
(* ------------------------------------------------------------ *)
Definition Shor_QPE_prog : op_list :=
  alloc_qubits phase_qubits ++
  alloc_qubits work_qubits ++
  apply_H_all phase_qubits ++
  qpe_controlled_pows phase_qubits 0 ++
  inv_qft_phase ++
  meas_all phase_bits.

(* ------------------------------------------------------------ *)
(* Structural tests              *)
(* ------------------------------------------------------------ *)

(* Count how many controlled powers were generated: should be t_phase = 8. *)
Fixpoint count_controlled (ops : op_list) : nat :=
  match ops with
  | [] => 0
  | OpAP (CAppU _ (CU _ _ _)) :: tl => S (count_controlled tl)
  | _ :: tl => count_controlled tl
  end.

Example test_controlled_count :
  count_controlled Shor_QPE_prog = t_phase.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------ *)
(* Classical postprocessing test             *)
(* ------------------------------------------------------------ *)



Program Fixpoint gcd (x y : nat) {measure y} : nat :=
  match y with
  | 0 => x
  | _ => gcd y (Nat.modulo x y)
  end.
Next Obligation.
  apply Nat.mod_upper_bound.
  lia.
Qed.

(* pow_mod (small, fine for this test) *)
Fixpoint pow_mod (a e n : nat) : nat :=
  match e with
  | 0 => 1 mod n
  | S e' => Nat.modulo (a * pow_mod a e' n) n
  end.


Definition two_pow (t : nat) : nat := Nat.pow 2 t.

Fixpoint find_period_exact_from (m t r fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
      if Nat.eqb (Nat.modulo (m * r) (two_pow t)) 0
      then r
      else find_period_exact_from m t (S r) fuel'
  end.

Definition find_period_exact (m t Rmax : nat) : nat :=
  find_period_exact_from m t 1 Rmax.


Definition shor_factors_from_r (a N r : nat) : (nat * nat) :=
  if Nat.even r then
    let x := pow_mod a (Nat.div r 2) N in
    let f1 := Nat.gcd (Nat.sub x 1) N in
    let f2 := Nat.gcd (x + 1) N in
    (f1, f2)
  else (1, N).



(* Ideal Shor test case for N=15,a=2:
   The true order is r=4, and QPE ideally can output m = 2^t / 4 = 256/4 = 64 (for s=1).
*)
Definition m_ideal : nat := 64.

Example test_period_is_4 :
  find_period_exact m_ideal t_phase 16 = 4.
Proof. reflexivity. Qed.

Example test_factors_are_3_and_5 :
  shor_factors_from_r a N 4 = (3, 5).
Proof. reflexivity. Qed.


(* ============================================================ *)
(* Shor period-finding ( N=15, a=2, r=4)                     *)
(* Written exactly in op_list style like Qprog                  *)
(* ============================================================ *)


(* ---------------------------- *)
(* Qubit ids                    *)
(* ---------------------------- *)

(* Phase register (3 qubits for demo) *)
Definition p0 : var := 0.
Definition p1 : var := 1.
Definition p2 : var := 2.

(* Work register (2 qubits → period 4 oracle) *)


(* Classical measurement outputs *)
Definition m0 : var := 100.
Definition m1 : var := 101.
Definition m2 : var := 102.

(* ---------------------------- *)
(* Allocate qubits              *)
(* ---------------------------- *)

Definition new_p0 : cexp := CNew p0 1.
Definition new_p1 : cexp := CNew p1 1.
Definition new_p2 : cexp := CNew p2 1.

Definition new_w0 : cexp := CNew w0 1.
Definition new_w1 : cexp := CNew w1 1.

(* ---------------------------- *)
(* Hadamards on phase register  *)
(* ---------------------------- *)

Definition appH_p0 : cexp := CAppU L (H p0 (Num 0)).
Definition appH_p1 : cexp := CAppU L (H p1 (Num 0)).
Definition appH_p2 : cexp := CAppU L (H p2 (Num 0)).

(* ---------------------------- *)
(* Toy oracle: INC mod 4        *)
(* Period = 4                   *)
(* ---------------------------- *)


(* Controlled powers U^(2^k) *)

Definition CU_p0 : cexp :=
  CAppU L (CU p0 (Num 0) INC_mod4).

Definition CU_p1 : cexp :=
  CAppU L (CU p1 (Num 0)
            (Seq INC_mod4 INC_mod4)).   (* U^2 *)

Definition CU_p2 : cexp :=
  CAppU L (CU p2 (Num 0)
            (Seq INC_mod4
                 (Seq INC_mod4
                      (Seq INC_mod4 INC_mod4)))).  (* U^4 *)

(* ---------------------------- *)
(* Inverse QFT on phase register *)
(* ---------------------------- *)

Definition appRQFT : cexp :=
  CAppU L (RQFT p0 3).

(* ---------------------------- *)
(* Measurements                 *)
(* ---------------------------- *)

Definition meas_p0 : cexp := CMeas m0 L.
Definition meas_p1 : cexp := CMeas m1 L.
Definition meas_p2 : cexp := CMeas m2 L.

Require Import DisQ.AUTO.
Import AUTO.

(* ============================================================ *)
(* The program as op_list   *)
(* ============================================================ *)

Definition Shor_Qprog : op_list :=
  [ OpAP new_p0;
    OpAP new_p1;
    OpAP new_p2;

    OpAP new_w0;
    OpAP new_w1;

    OpAP appH_p0;
    OpAP appH_p1;
    OpAP appH_p2;

    OpAP CU_p0;
    OpAP CU_p1;
    OpAP CU_p2;

    OpAP appRQFT;

    OpAP meas_p0;
    OpAP meas_p1;
    OpAP meas_p2
  ].

(* ============================================================ *)
(* Tests for Shor_Qprog              *)
(* ============================================================ *)

(* --- All qubits and operations on membrane 0 --- *)

Definition Shor_dist0 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO0 Shor_Qprog.

Compute Shor_dist0.
Compute fit Shor_dist0.


(* --- All operations forced to membrane 1 --- *)

Definition Shor_dist1 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO1 Shor_Qprog.

Compute Shor_dist1.
Compute fit Shor_dist1.


(* --- Force everything to membrane 2 --- *)

Definition Shor_dist2 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO2 Shor_Qprog.

Compute Shor_dist2.
Compute fit Shor_dist2.


(* --- Force everything to membrane 3 --- *)

Definition Shor_dist3 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO3 Shor_Qprog.

Compute Shor_dist3.
Compute fit Shor_dist3.


(* --- Force everything to membrane 5 --- *)

Definition Shor_dist5 : distributed_prog :=
  gen_prog_paper seq0 moQ0 moO5 Shor_Qprog.

Compute Shor_dist5.
Compute fit Shor_dist5.

























