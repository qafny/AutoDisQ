Require Import Reals.
Require Import Psatz.
Require Import Complex.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat Permutation. 
Require Import Dirac.
Require Import QPE.
Require Import BasicUtility.
Require Import Classical_Prop.
Require Import MathSpec.
Require Import DisQSyntax.
Require Import DisQDef.
Require Import DisQKind.
Require Import DisQSem.
Require Import DisQType.

From Coq Require Import List.
Import ListNotations.
(**********************)
(** Unitary Programs **)
(**********************)

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Declare Scope pexp_scope.
Delimit Scope pexp_scope with pexp.
Local Open Scope pexp_scope.
Local Open Scope nat_scope.

Definition l : var := 1.
Definition u : var := 2.
Definition r : var := 3.
Definition n : nat := 8.
Definition b : nat := 7.
Definition q : nat := 2.
Definition x : var := 10.
Definition y : var := 11.
Definition c  : var := 100.
Definition c1 : var := 101.
Definition w  : var := 1001.
Definition z  : var := 1002.

(* Left membrane: first do H^⊗n on x, then a single (NewCh; Send) *)
Fixpoint cat_process (p q : process) : process :=
  match p with
  | PNil        => q
  | AP a p'     => AP a (cat_process p' q)
  | DP d p'     => DP d (cat_process p' q)
  | PIf b p1 p2 => PIf b (cat_process p1 q) (cat_process p2 q)
  end.

Definition shor_disq_process_l : process :=
  let fix nH (i:nat) :=
    match i with
    | 0 => PNil
    | S k =>
        AP (CAppU ((x, BNum 0, BNum n)::[]) (H x (S k))) (nH k)
    end in
  DP (NewCh c 1)
     (DP (Send c (Num 0))
         (nH n)).

(* Upper membrane: a single (NewCh; Recv), then one CU *)
Definition shor_disq_process_u : process :=
  DP (NewCh c 1)
    (DP (Recv c w)
      (AP (CAppU ((y, BNum 0, BNum n)::[]) (CU w (BA w) (RZ q y (BA y))))
          PNil)).

(* Right membrane: one QFT *)
Definition shor_disq_process_r : process :=
  AP (CAppU ((x, BNum 0, BNum n)::[]) (QFT x b)) PNil.

Definition shor_disq : config :=
  Memb l [shor_disq_process_l]::
  Memb u [shor_disq_process_u]::
  Memb r [shor_disq_process_r]::[].

Definition shor_seq : config :=
  let proces :=
    AP (CAppU ((y, BNum 0, BNum n)::[]) (CU w (BA w) (RZ q y (BA y))))
       (AP (CAppU ((x, BNum 0, BNum n)::[]) (QFT x b)) PNil)
  in
  let fix nH (k : nat) :=
    match k with
    | 0   => proces
    | S j => AP (CAppU ((x, BNum 0, BNum n)::[]) (H x (Num k))) (nH j)
    end
  in
  [Memb l [nH n]].

Definition shor_comm_nf : config :=
   Memb l
      [ let fix nH (i:nat) :=
          match i with
          | 0 => PNil
          | S k => AP (CAppU ((x, BNum 0, BNum n)::[]) (H x (Num (S k)))) (nH k)
          end in
        nH n
      ]
  :: Memb u [ AP (CAppU ((y, BNum 0, BNum n)::[]) (CU w (BA w) (RZ q y (BA y)))) PNil ]
  :: Memb r [ AP (CAppU ((x, BNum 0, BNum n)::[]) (QFT x b)) PNil ]
  :: [].

Set Implicit Arguments.
Local Open Scope nat_scope.

(* Multi-step closure of m_step (reflexive–transitive). *)
Inductive m_steps (rmax:nat) (aenv:aenv)
  : gqstate -> config -> gqstate -> config -> Prop :=
| ms_refl : forall s c, m_steps rmax aenv s c s c
| ms_step : forall s c r lv ls s' c' s'' c'',
    m_step (rmax:=rmax) aenv s c (r,lv) ls s' c' ->
    m_steps rmax aenv s' c' s'' c'' ->
    m_steps rmax aenv s c s'' c''.

Definition seq_of_list (ps : list process) : process :=
  fold_right cat_process PNil ps.

Fixpoint memb_processes (m : memb) : list process :=
  match m with
  | Memb _ ps        => ps
  | LockMemb _ hd tl => hd :: tl
  end.

Definition collapse_only (c : config) : config :=
  match c with
  | [] => []
  | m0 :: cs =>
      match m0 with
      | Memb l ps =>
          let rest := concat (map memb_processes cs) in
          [Memb l [seq_of_list (ps ++ rest)]]
      | LockMemb l hd tl =>
          let ps := hd :: tl in
          let rest := concat (map memb_processes cs) in
          [Memb l [seq_of_list (ps ++ rest)]]
      end
  end.

Lemma shor_disq_tau_normalizes :
  forall rmax aenv s0, exists s1,
    m_steps rmax aenv s0 shor_disq s1 shor_comm_nf.
Proof.
  intros rmax aenv s0.
  eexists.
  (* 1) lock left (head) *)
  eapply ms_step.
  - eapply mem_step_ctx. apply mem_step.
  - (* 2) lock upper (second element) via tail context *)
    eapply ms_step.
    + eapply step_ctx_cons.
      eapply mem_step_ctx. apply mem_step.
      eapply ms_step.
      * apply newchan_step.
      * (* 4) lock left again to expose Send *)
        eapply ms_step.
        eapply mem_step_ctx. apply mem_step.
        (* 5) lock upper again to expose Recv (tail context) *)
        eapply ms_step.
        eapply step_ctx_cons.
        eapply mem_step_ctx. apply mem_step.
        (* 6) Perform Send/Recv handshake *)
        eapply ms_step.
        eapply commc_sem with (n := 0).
        change (simp_aexp (Num 0) = Some 0).
        cbn [simp_aexp]. reflexivity.
        (* 7) Done — reach shor_comm_nf; finish with reflexive closure *)
        apply ms_refl.
Qed.


Theorem Dis_Shors_refines_Shors_tau :
  forall rmax aenv s0, exists s1,
    m_steps rmax aenv s0 shor_disq s1 shor_comm_nf /\
    collapse_only shor_comm_nf = shor_seq.
Proof.
  intros rmax aenv s0.
  destruct (shor_disq_tau_normalizes rmax aenv s0) as [s1 Hτ].
  exists s1. split; [exact Hτ|].
  unfold collapse_only, shor_comm_nf, shor_seq; simpl; reflexivity.
Qed.
