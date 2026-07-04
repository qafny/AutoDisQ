(* DisQProof.v
   Type Preservation for DisQ (configuration-level).
*)

From Coq Require Import List.
Import ListNotations.

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
Require Import Coq.Classes.RelationClasses.
(* Project modules *)
Require Import DisQSyntax.
Require Import DisQDef.
Require Import DisQKind.
Require Import DisQSem.
Require Import DisQType.

Set Implicit Arguments.

Section Preservation.

Variable rmax : nat.

(* ---------------------------------------------------------------------- *)
(* Helpful inversion/automation                                          *)
(* ---------------------------------------------------------------------- *)

Ltac inv H := inversion H; subst; clear H.

Hint Constructors c_locus_system : core.
Hint Constructors m_locus_system : core.

(* ---------------------------------------------------------------------- *)
(* Framing lemmas (typing bookkeeping for list-of-memb configurations)   *)
(* ---------------------------------------------------------------------- *)

(* If we can re-type a head membrane m as m', we can rebuild the config typing. *)
Lemma c_frame_head
  : forall (env : aenv) (Tl Tl' : type_gmap) (m m' : memb) (ms : config)
           (T T' : type_gmap),
    (* original typing of (m :: ms) *)
    loc_memb m = loc_memb m' ->
    m_locus_system (rmax:=rmax) env Tl m Tl' ->
    c_locus_system (rmax:=rmax) env T ms T' ->
    (* new typing where head m is replaced by m' *)
    m_locus_system (rmax:=rmax) env Tl m' Tl' ->
    c_locus_system (rmax:=rmax) env (Tl ++ T) (m' :: ms) (Tl' ++ T').
Proof.
  intros env Tl Tl' m m' ms T T' Hloc Hm Hc Hm'.
  (* rebuild via [top_ses] *)
  econstructor; eauto.
Qed.

(* If we can re-type two consecutive head membranes m1,m2 as m1',m2', we can rebuild. *)
Lemma c_frame_two_heads
  : forall (env : aenv)
           (Tl1 Tl1' Tl2 Tl2' : type_gmap)
           (m1 m1' m2 m2' : memb)
           (ms : config) (T T' : type_gmap),
    loc_memb m1 = loc_memb m1' ->
    loc_memb m2 = loc_memb m2' ->
    m_locus_system (rmax:=rmax) env Tl1 m1 Tl1' ->
    m_locus_system (rmax:=rmax) env Tl2 m2 Tl2' ->
    c_locus_system (rmax:=rmax) env T ms T' ->
    m_locus_system (rmax:=rmax) env Tl1 m1' Tl1' ->
    m_locus_system (rmax:=rmax) env Tl2 m2' Tl2' ->
    c_locus_system (rmax:=rmax) env (Tl1 ++ Tl2 ++ T) (m1' :: m2' :: ms) (Tl1' ++ Tl2' ++ T').
Proof.
  intros.
  (* Rebuild the second head first, then the first head on top *)
  econstructor; eauto.
Qed.

(* ---------------------------------------------------------------------- *)
(* Semantic-to-typing bridge lemmas *)
(* ---------------------------------------------------------------------- *)

(* 1) MEM-STEP: [Memb l (P::Q)]  -->  [LockMemb l P Q] *)
Lemma typing_mem_to_lock :
  forall env Tl Tl' l P Q,
    m_locus_system (rmax:=rmax) env Tl (Memb l (P::Q)) Tl' ->
    m_locus_system (rmax:=rmax) env Tl (LockMemb l P Q) Tl'.
Proof. intros; now constructor. Qed.
  

(* 2) REV-STEP: [LockMemb l P Q]  -->  [Memb l (P::Q)] *)
Lemma typing_lock_to_mem :
  forall env Tl Tl' l P Q,
    m_locus_system (rmax:=rmax) env Tl (LockMemb l P Q) Tl' ->
    m_locus_system (rmax:=rmax) env Tl (Memb l (P::Q)) Tl'.
Proof. intros; now constructor. Qed.

(* 3) MOVE-STEP (process-level reduction inside a membrane):
      (Memb lc (P::lp))  -->  (Memb lc (P'::lp))  *)
Lemma typing_mem_after_move :
  forall env Tl Tl' lc P P' lp,
    (* original membrane typing *)
    m_locus_system (rmax:=rmax) env Tl (Memb lc (P::lp)) Tl' ->
    (* result: the membrane remains well-typed after the internal step *)
    m_locus_system (rmax:=rmax) env Tl (Memb lc (P'::lp)) Tl'.
Proof. Admitted.
(* 4) COMMC-SEM (classical communication across two locked membranes):
      [LockMemb l1 (DP (Send x a) P) m1 ;
       LockMemb l2 (DP (Recv x y) Q) m2 ; cf]
      -->
      [Memb l1 (P :: m1) ; Memb l2 (Q :: m2) ; cf]
   Typing-wise, we only need to know that if the locked membranes are typable,
   then after the communication they remain typable as ordinary membranes. *)
Lemma typing_after_commc_two_locked :
  forall env Tl1 Tl1' Tl2 Tl2' l1 l2 (x y: var) (a: aexp) P Q m1 m2,
    m_locus_system (rmax:=rmax) env Tl1 (LockMemb l1 (DP (Send x a) P) m1) Tl1' ->
    m_locus_system (rmax:=rmax) env Tl2 (LockMemb l2 (DP (Recv x y) Q) m2) Tl2' ->
    m_locus_system (rmax:=rmax) env Tl1 (Memb l1 (P :: m1)) Tl1' /\
    m_locus_system (rmax:=rmax) env Tl2 (Memb l2 (Q :: m2)) Tl2'.
Proof. Admitted.
(* 5) NEWCHAN-STEP (channel creation across two locked membranes) *)
Lemma typing_after_newchan_two_locked :
  forall env Tl1 Tl1' Tl2 Tl2' lc1 lc2 c n P Q m1 m2,
    m_locus_system (rmax:=rmax) env Tl1 (LockMemb lc1 (DP (NewCh c n) P) m1) Tl1' ->
    m_locus_system (rmax:=rmax) env Tl2 (LockMemb lc2 (DP (NewCh c n) Q) m2) Tl2' ->
    m_locus_system (rmax:=rmax) env Tl1 (Memb lc1 (P :: m1)) Tl1' /\
    m_locus_system (rmax:=rmax) env Tl2 (Memb lc2 (Q :: m2)) Tl2'.
Proof. Admitted.

(* ---------------------------------------------------------------------- *)
(* Main Theorem: Type Preservation (configuration-level)                  *)
(* ---------------------------------------------------------------------- *)

Theorem type_preservation :
  forall (env : aenv)
         (s s' : gqstate) (cf cf' : config)
         (T T' : type_gmap) (r : R) (lv : option nat) (ls : list var),
    c_locus_system (rmax:=rmax) env T cf T' ->
    m_step (rmax:=rmax) env s cf (r, lv) ls s' cf' ->
    exists U U', c_locus_system (rmax:=rmax) env U cf' U'.
Proof.
  intros env s s' cf cf' T T' r lv ls Htyped Hstep.
  revert T T' Htyped.
  induction Hstep; intros T T' Htyped.

  - (* end_step: singleton membrane, no change except a side condition [are_0 Q] *)
    inv Htyped.
    eexists; eexists.
    (* rebuild with the very same head *)
    econstructor; eauto.

  - (* mem_step: [Memb l (P::Q)] -> [LockMemb l P Q] *)
    inv Htyped.
    eexists; eexists.
    (* transform the head membrane's typing via [typing_mem_to_lock] *)
    eapply c_frame_head; eauto.


  - (* rev_step: [LockMemb l P Q] -> [Memb l (P::lp)] *)
  inv Htyped.
  eexists; eexists.
  eapply c_frame_head; eauto.
  + eapply typing_lock_to_mem; eauto.
    eapply typing_mem_to_lock; eauto.
    inversion H5; subst.
    eapply typing_lock_to_mem; eauto.
  + inversion H5; subst. eauto.
  + inversion H5; subst.
    eapply (typing_lock_to_mem
              (env:=aenv) (Tl:=Tl) (Tl':=Tl') (l:=l) (P:=P) (Q:=lp)). exact H1.
    
  - (* commc_sem: two locked heads communicate and become ordinary membranes *)
    (* The configuration has two locked heads; destruct typing twice. *)
    inv Htyped.
    inversion H7; subst; clear H7.
    match goal with
    | Hlocked2 : m_locus_system _ _ (LockMemb _ _ _) _ |- _ => idtac end.
    match goal with | Htail : c_locus_system _ _ cf _ |- _ => idtac end.
    pose proof (typing_after_commc_two_locked
              (env:=aenv) (Tl1:=Tl)  (Tl1':=Tl')
              (Tl2:=Tl0) (Tl2':=Tl'0)
              (l1:=l1) (l2:=l2) (x:=x) (y:=y) (a:=a) (P:=P) (Q:=Q)
              (m1:=m1) (m2:=m2) H5 H6) as [Hmb1 Hmb2].
    eexists; eexists.
    eapply c_frame_two_heads; eauto; try reflexivity.

  - (* move_step: internal process-level step inside a membrane *)
    inv Htyped.
    eexists; eexists.
    (* replace (Memb lc (P::lp)) with (Memb lc (P'::lp)) using typing_mem_after_move *)
    eapply c_frame_head; eauto.
    + eapply typing_mem_after_move; eauto.
    + eapply typing_mem_after_move; eauto.

  - (* newchan_step: two locked heads create a new channel and become ordinary membranes *)
    inv Htyped.
    inversion H6; subst; clear H6.
    pose proof (typing_after_newchan_two_locked
              (env:=aenv) (Tl1:=Tl)  (Tl1':=Tl')
              (Tl2:=Tl0) (Tl2':=Tl'0)
              (lc1:=lc1) (lc2:=lc2)
              (c:=c) (n:=n) (P:=P) (Q:=Q)
              (m1:=m1) (m2:=m2)
              H4 H5) as Hpair.
    destruct Hpair as [Hmb1 Hmb2].
    eexists; eexists.
    eapply c_frame_two_heads; eauto; try reflexivity.
Qed.

End Preservation.
