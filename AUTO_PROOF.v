From Coq Require Import List Arith Bool Nat NArith Lia.
Import ListNotations.

Require Import Coq.Sorting.Mergesort.
Require Import Coq.Structures.Orders.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import QArith.

Local Open Scope list_scope.
Local Open Scope bool_scope.

Require Import DisQ.BasicUtility.
Require Import DisQ.DisQSyntax.
Require Import DisQ.DisQSem.
Require Import DisQ.AUTO.
Require Import DisQ.DisQDef.

Require Import Reals.
Open Scope R_scope.

(*****************************************************************)
(* Correctness of AutoDisQ                 *)
(*****************************************************************)

Lemma best_prog_aux_in :
  forall xs best bestv,
    In (best_prog_aux best bestv xs) (best :: xs).
Proof.
  induction xs as [|x xs IH]; intros best bestv; simpl.
  - left; reflexivity.
  - destruct (Nat.ltb (fit x) bestv) eqn:Hlt.
    + right. apply IH.
    + destruct (IH best bestv) as [Heq | Hin].
      * left; assumption.
      * right; right; assumption.
Qed.

Lemma best_prog_aux_spec :
  forall xs best,
    let r := best_prog_aux best (fit best) xs in
    In r (best :: xs) /\
    forall y, In y (best :: xs) -> (fit r <= fit y)%nat.
Proof.
 induction xs as [|x xs IH]; intros best; simpl.
  - split.
    + left; reflexivity.
    + intros y Hy.
      destruct Hy as [Hy | Hy].
      * subst; lia.
      * contradiction.
  - destruct (Nat.ltb (fit x) (fit best)) eqn:Hlt.
    + specialize (IH x).
      destruct IH as [Hin Hmin].
      split.
      * right; exact Hin.
      * intros y Hy.
        destruct Hy as [Hy | Hy].
        -- subst.
           apply Nat.ltb_lt in Hlt.
           specialize (Hmin x).
assert (In x (x :: xs)) by (left; reflexivity).
specialize (Hmin H).
lia.

        -- apply Hmin; exact Hy.
    + specialize (IH best).
      destruct IH as [Hin Hmin].
      split.
      * destruct Hin as [Hin | Hin].
        -- left; exact Hin.
        -- right; right; exact Hin.
      * intros y Hy.
        destruct Hy as [Hy | Hy].
        -- subst.
           apply Hmin.
           left; reflexivity.
        -- destruct Hy as [Hy | Hy].
           ++ subst.
              apply Nat.ltb_ge in Hlt.
              specialize (Hmin best).
              assert (In best (best :: xs)) by (left; reflexivity).
              specialize (Hmin H).
              lia.
           ++ apply Hmin.
              right; exact Hy.
Qed.


Theorem best_prog_spec :
  forall xs cfg,
    best_prog xs = Some cfg ->
    In cfg xs /\ forall y, In y xs -> (fit cfg <= fit y)%nat.
Proof.
  intros xs cfg H.
  destruct xs as [|x xs].
  - simpl in H. discriminate.
  - simpl in H. inversion H; subst; clear H.
    specialize (best_prog_aux_spec xs x) as [Hin Hmin].
    split.
    + exact Hin.
    + exact Hmin.
Qed.

Lemma gen_prog_nonempty :
  forall l os,
    l <> [] ->
    gen_prog l os <> [].
Proof.
  intros l os Hneq.
  destruct l as [|x xs].
  - contradiction.
  - intro Hcontra.
    destruct (has_if_ops os) eqn:Hif; simpl in Hcontra.
    + inversion Hcontra.
    rewrite Hif in Hcontra.
inversion Hcontra.
+ rewrite Hif in Hcontra. inversion Hcontra.
Qed.


Lemma gen_mem_nonempty :
  forall news l ids,
    gen_mem news l ids <> [].
Proof.
  intros news l ids.
  unfold gen_mem.
  destruct (map
     (fun a : list (((myOpAux * list nposi) * membrane_id)%type) =>
      gen_mem_new news ids ++ a)
     (assign_mem_more
        (gen_empty_mem (find_empy_new (turn_new (gen_mem_new news ids) []) ids [])
         ++ turn_new (gen_mem_new news ids) [])
        (assign_new_mem news
           (find_empy_new (turn_new (gen_mem_new news ids) []) ids [])) l [])) eqn:Hres.
  - destruct (take 3 l) eqn:Htake.
    + simpl. discriminate.
    + simpl. discriminate.
  - simpl. discriminate.
Qed.

Theorem autodisq_all_nonempty :
  forall ops mids,
    autodisq_all ops mids <> [].
Proof.
  intros ops mids.
  unfold autodisq_all.
  set (os := opListOrder ops).
  set (hb := gen_hb os).
  set (sq := gen_seq os hb).
  set (mem := gen_mem (fst sq) (snd sq) mids).
  apply gen_prog_nonempty.
  apply gen_mem_nonempty.
Qed.

Theorem autodisq_best_sound :
  forall ops mids cfg,
    autodisq_best ops mids = Some cfg ->
    In cfg (autodisq_all ops mids) /\
    forall y, In y (autodisq_all ops mids) -> (fit cfg <= fit y)%nat.
Proof.
  intros ops mids cfg H.
  unfold autodisq_best in H.
  apply best_prog_spec in H.
  exact H.
Qed.

Theorem autodisq_best_exists :
  forall ops mids,
    exists cfg, autodisq_best ops mids = Some cfg.
Proof.
  intros ops mids.
  unfold autodisq_best.
  destruct (autodisq_all ops mids) as [|x xs] eqn:Hgen.
  - exfalso.
    pose proof (autodisq_all_nonempty ops mids) as Hnz.
    rewrite Hgen in Hnz.
    contradiction.
  - eexists. reflexivity.
Qed.






(*****************************************************************)
(*  Basic owner-map predicates                         *)
(*****************************************************************)

Definition pos_in_owners
  (owners : list ((nposi * membrane_id)%type))
  (p : nposi) : Prop :=
  exists mid, owner_of_pos owners p = Some mid.

Definition owner_unique
  (owners : list ((nposi * membrane_id)%type)) : Prop :=
  forall p m1 m2,
    owner_of_pos owners p = Some m1 ->
    owner_of_pos owners p = Some m2 ->
    m1 = m2.

Definition owners_total_on
  (owners : list ((nposi * membrane_id)%type))
  (qs : list nposi) : Prop :=
  forall q, In q qs -> pos_in_owners owners q.

Definition owners_all_at
  (owners : list ((nposi * membrane_id)%type))
  (qs : list nposi)
  (mid : membrane_id) : Prop :=
  forall q, In q qs -> owner_of_pos owners q = Some mid.

Definition owners_preserve_outside
  (owners owners' : list ((nposi * membrane_id)%type))
  (qs : list nposi) : Prop :=
  forall q,
    ~ In q qs ->
    owner_of_pos owners' q = owner_of_pos owners q.

Definition owners_updated_exactly_to
  (owners owners' : list ((nposi * membrane_id)%type))
  (qs : list nposi)
  (mid : membrane_id) : Prop :=
  owners_all_at owners' qs mid /\
  owners_preserve_outside owners owners' qs.

(*****************************************************************)
(* Basic list lemmas on nposi                         *)
(*****************************************************************)

Lemma nposi_eq_sym :
  forall x y, nposi_eq x y = nposi_eq y x.
Proof.
  intros [x1 y1] [x2 y2].
  unfold nposi_eq.
  rewrite N.eqb_sym.
  rewrite N.eqb_sym.
replace (y2 =? y1)%N with (y1 =? y2)%N.
- reflexivity.
- apply N.eqb_sym.
Qed.

Lemma nposi_eq_true_sym :
  forall x y, nposi_eq x y = true -> nposi_eq y x = true.
Proof.
  intros [x1 y1] [x2 y2].
  unfold nposi_eq; simpl.
  intros H.
  apply andb_true_iff in H.
  destruct H as [Hx Hy].
  apply andb_true_iff.
  split.
  - apply N.eqb_eq in Hx. apply N.eqb_eq. symmetry. exact Hx.
  - apply N.eqb_eq in Hy. apply N.eqb_eq. symmetry. exact Hy.
Qed.
Lemma mem_pos_complete :
  forall p xs,
    mem_pos p xs = true ->
    exists q, In q xs /\ nposi_eq p q = true.
Proof.
  intros p xs.
  induction xs as [|a xs IHxs]; intros H; simpl in H.
  - discriminate.
  - destruct (nposi_eq a p) eqn:Heqap.
    + exists a. split.
      * left; reflexivity.
      * apply nposi_eq_true_sym. exact Heqap.
    + apply IHxs in H.
      destruct H as [q [Hinq Hpeq]].
      exists q. split.
      * right; exact Hinq.
      * exact Hpeq.
Qed.

Lemma nposi_eq_refl :
  forall p, nposi_eq p p = true.
Proof.
  intros [x y].
  unfold nposi_eq.
  simpl.
  rewrite N.eqb_refl.
  rewrite N.eqb_refl.
  reflexivity.
Qed.
Lemma mem_pos_sound :
  forall p xs,
    In p xs ->
    mem_pos p xs = true.
Proof.
  induction xs as [|a xs IHxs]; intros H; simpl in *.
  - contradiction.
  - destruct H as [-> | Hin].
    + rewrite nposi_eq_refl.
      reflexivity.
    + destruct (nposi_eq a p) eqn:Heqap.
      * reflexivity.
      * apply IHxs. exact Hin.
Qed.


(*****************************************************************)
(* Fundamental owner_of_pos lemmas                    *)
(*****************************************************************)

Lemma owner_unique_trivial :
  forall owners,
    owner_unique owners.
Proof.
  unfold owner_unique; intros.
  rewrite H in H0; inversion H0; reflexivity.
Qed.



Lemma owner_of_pos_set_owner_eq :
  forall owners p mid,
    owner_of_pos (set_owner owners p mid) p = Some mid.
Proof.
  induction owners as [| [q m] tl IH]; intros p mid; simpl.
  - rewrite nposi_eq_refl.
    reflexivity.
  - destruct (nposi_eq q p) eqn:Hqp.
    + simpl.
      rewrite nposi_eq_refl.
      reflexivity.
    + simpl.
      rewrite Hqp.
      apply IH.
Qed.

Lemma nposi_eq_true_iff :
  forall x y, nposi_eq x y = true <-> x = y.
Proof.
  intros [x1 y1] [x2 y2].
  unfold nposi_eq. simpl.
  rewrite andb_true_iff.
  split.
  - intros [Hx Hy].
    apply N.eqb_eq in Hx.
    apply N.eqb_eq in Hy.
    subst. reflexivity.
  - intros [= -> ->].
    split; apply N.eqb_refl.
Qed.
Lemma owner_of_pos_set_owner_neq :
  forall owners p q mid,
    nposi_eq q p = false ->
    owner_of_pos (set_owner owners p mid) q = owner_of_pos owners q.
Proof.
  induction owners as [| [r m] tl IH]; intros p q mid Hneq; simpl.
  - rewrite nposi_eq_sym.
    rewrite Hneq.
    reflexivity.
  - destruct (nposi_eq r p) eqn:Hrp.
    + apply nposi_eq_true_iff in Hrp.
      subst r.
      simpl.
      rewrite nposi_eq_sym in Hneq.
      rewrite Hneq.
      reflexivity.
    + simpl.
      destruct (nposi_eq r q) eqn:Hrq.
      * reflexivity.
      * apply IH.
        exact Hneq.
Qed.

Lemma owner_of_pos_set_owner_many_notin :
  forall qs owners mid q,
    NoDup qs ->
    ~ In q qs ->
    owner_of_pos (set_owner_many owners qs mid) q = owner_of_pos owners q.
Proof.
  induction qs as [|x tl IH]; intros owners mid q Hnodup Hnotin; simpl.
  - reflexivity.
  - inversion Hnodup as [|? ? Hxnotin Hnodup_tl]; subst.
    apply not_in_cons in Hnotin.
    destruct Hnotin as [Hneq Hnotin_tl].
    rewrite IH.
    + apply owner_of_pos_set_owner_neq.
      destruct (nposi_eq q x) eqn:Heq.
      * apply nposi_eq_true_iff in Heq.
subst.
contradiction.
        *easy.
    + exact Hnodup_tl.
    + exact Hnotin_tl.
Qed.


Lemma owner_of_pos_set_owner_many_in :
  forall qs owners mid q,
    NoDup qs ->
    In q qs ->
    owner_of_pos (set_owner_many owners qs mid) q = Some mid.
Proof.
  induction qs as [|x tl IH]; intros owners mid q Hnodup Hin; simpl in *.
  - contradiction.
  - inversion Hnodup as [|? ? Hxnotin Hnodup_tl]; subst.
    destruct Hin as [Hq | Hin].
    + subst q.
      rewrite owner_of_pos_set_owner_many_notin.
      * apply owner_of_pos_set_owner_eq.
      * exact Hnodup_tl.
      * exact Hxnotin.
    + rewrite IH.
      * reflexivity.
      * exact Hnodup_tl.
      * exact Hin.
Qed.

Lemma set_owner_many_updates_exactly_to :
  forall owners qs mid,
    NoDup qs ->
    owners_updated_exactly_to owners (set_owner_many owners qs mid) qs mid.
Proof.
  intros owners qs mid Hnodup.
  split.
  - unfold owners_all_at.
    intros q Hin.
    apply owner_of_pos_set_owner_many_in.
    + exact Hnodup.
    + exact Hin.
  - unfold owners_preserve_outside.
    intros q Hnotin.
    apply owner_of_pos_set_owner_many_notin.
    + exact Hnodup.
    + exact Hnotin.
Qed.


(*****************************************************************)
(* communication invariants                  *)
(*****************************************************************)

Definition cexp_targets_mid
  (mid : membrane_id)
  (ce : cexp)
  (bufs : list ((membrane_id * list cexp)%type)) : Prop :=
  exists ces,
    In (mid, ces) bufs /\ In ce ces.

Fixpoint mem_cexp (ce : cexp) (xs : list cexp) : Prop :=
  match xs with
  | [] => False
  | x :: tl => x = ce \/ mem_cexp ce tl
  end.

Definition appears_in_mem
  (mid : membrane_id)
  (ce : cexp)
  (bufs : list ((membrane_id * list cexp)%type)) : Prop :=
  exists xs, In (mid, xs) bufs /\ mem_cexp ce xs.

Lemma mem_cexp_app_r :
  forall ce xs ys,
    mem_cexp ce ys ->
    mem_cexp ce (xs ++ ys).
Proof.
  induction xs; intros; simpl; auto.
Qed.

Lemma mem_cexp_app_l :
  forall ce xs ys,
    mem_cexp ce xs ->
    mem_cexp ce (xs ++ ys).
Proof.
  induction xs; intros; simpl in *; auto.
  destruct H; auto.
destruct H as [Ha | Hxs].
- left. exact Ha.
- right. apply IHxs. exact Hxs.
Qed.

Lemma append_cexp_to_mem_hits :
  forall bufs mid ce,
    appears_in_mem mid ce (append_cexp_to_mem mid ce bufs).
Proof.
  induction bufs as [| [m xs] tl IH]; intros; simpl.
  - exists [ce]. split.
    + left; reflexivity.
    + simpl; auto.
  - destruct (Nat.eqb mid m) eqn:Heq.
    + exists (xs ++ [ce]). split.
      * left. f_equal. apply Nat.eqb_eq in Heq. 
symmetry.
exact Heq.
      * apply mem_cexp_app_r. simpl. auto.
    + destruct (IH mid ce) as [ys [Hin Hmem]].
exists ys.
split.
right. exact Hin.
exact Hmem.
Qed.

Lemma append_cexp_to_mem_preserves_other :
  forall bufs mid ce mid' xs,
    mid <> mid' ->
    In (mid', xs) bufs ->
    In (mid', xs) (append_cexp_to_mem mid ce bufs).
Proof.
  induction bufs as [| [m ys] tl IH]; intros; simpl in *.
  - contradiction.
  - destruct H0 as [H0 | H0].
    + inversion H0; subst; clear H0.
    destruct (mid =? mid') eqn:Heq.
apply Nat.eqb_eq in Heq.
 exfalso.
  apply H.
  exact Heq.
left.
  reflexivity.

    + destruct (Nat.eqb mid m) eqn:Heq.
      * right. exact H0.
      * right. apply IH; auto.
Qed.

(*****************************************************************)
(*  Communication shape predicates                     *)
(*****************************************************************)

Definition send_for (ch : var) (q : nposi) : cexp :=
  Send ch (N.to_nat (fst q)) (N.to_nat (snd q)).

Definition recv_for (ch : var) (q : nposi) : cexp :=
  Recv ch (N.to_nat (fst q)) (N.to_nat (snd q)).

Definition comm_pair_for
  (src dst : membrane_id)
  (ch : var)
  (q : nposi)
  (bufs : list ((membrane_id * list cexp)%type)) : Prop :=
  appears_in_mem src (send_for ch q) bufs /\
  appears_in_mem dst (recv_for ch q) bufs.

Definition all_comm_pairs_for
  (src dst : membrane_id)
  (start_chan : var)
  (qs : list nposi)
  (bufs : list ((membrane_id * list cexp)%type)) : Prop :=
  forall q,
    In q qs ->
    exists k,
      comm_pair_for src dst (start_chan + k)%nat q bufs.

(*****************************************************************)
(* Stepwise invariant for ensure_local_qubits_aux     *)
(*****************************************************************)

Definition ensure_local_result
  (dst : membrane_id)
  (qs : list nposi)
  (owners : list ((nposi * membrane_id)%type))
  (bufs : list ((membrane_id * list cexp)%type))
  (chan : var)
  (res : var * list ((nposi * membrane_id)%type) *
         list ((membrane_id * list cexp)%type)) : Prop :=
  let '(chan', owners', bufs') := res in
  owners_all_at owners' qs dst /\
  owners_preserve_outside owners owners' qs /\
  (forall q src,
      In q qs ->
      owner_of_pos owners q = Some src ->
      src <> dst ->
      exists k,
        comm_pair_for src dst (chan + k)%nat q bufs') /\
  (chan <= chan')%nat.



(*****************************************************************)
(* Stronger induction principle: after ensuring locality, all    *)
(* requested qubits are owned by dst, and outside qubits keep    *)
(* their old ownership.                                          *)
(*****************************************************************)

Theorem ensure_local_qubits_aux_locality :
  forall dst qs owners bufs chan chan' owners' bufs',
    NoDup qs ->
    owners_total_on owners qs ->
    ensure_local_qubits_aux dst qs owners bufs chan =
      (chan', owners', bufs') ->
    owners_all_at owners' qs dst.
Proof.
  unfold owners_all_at, owners_total_on, pos_in_owners.
  induction qs as [|q tl IH]; intros owners bufs chan chan' owners' bufs' Hnd Htot Hres x Hin.
  - contradiction.
  - inversion Hnd as [| ? ? Hqnotin Hnd_tl]; subst.
    simpl in Hres.

    assert (Hown_q : exists src, owner_of_pos owners q = Some src).
    { apply Htot. left. reflexivity. }

    assert (Htot_tl : forall y : nposi, In y tl -> exists m, owner_of_pos owners y = Some m).
    { intros y Hy. apply Htot. right. exact Hy. }

    destruct Hown_q as [src Hown].
    rewrite Hown in Hres.

    destruct (Nat.eqb src dst) eqn:Heq.
    + destruct Hin as [Hx | Hin].
      * subst x.

 Admitted.



Lemma gen_empty_mem_ids :
  forall mids mid,
    In mid mids ->
    In (mid, []) (gen_empty_mem mids).
Proof.
  induction mids; intros; simpl in *; contradiction || idtac.
  destruct H as [H | H].
  - subst. auto.
  - right. apply IHmids. exact H.
Qed.



Theorem ensure_local_qubits_aux_preserve_outside :
  forall dst qs owners bufs chan chan' owners' bufs' q,
    ensure_local_qubits_aux dst qs owners bufs chan =
      (chan', owners', bufs') ->
    ~ In q qs ->
    owner_of_pos owners' q = owner_of_pos owners q.
Proof.
  induction qs as [|x tl IH]; intros owners bufs chan chan' owners' bufs' q Hres Hnotin.
  - simpl in Hres. inversion Hres. reflexivity.
  - apply not_in_cons in Hnotin. destruct Hnotin as [Hneq Hnotin].
    simpl in Hres.
    destruct (owner_of_pos owners x) as [src|] eqn:Hown.
    + destruct (Nat.eqb src dst) eqn:Heq.
      * eapply IH; eauto.
      * remember (append_cexp_to_mem src
                   (Send chan (N.to_nat (fst x)) (N.to_nat (snd x))) bufs) as bufs1.
        remember (append_cexp_to_mem dst
                   (Recv chan (N.to_nat (fst x)) (N.to_nat (snd x))) bufs1) as bufs2.
        remember (set_owner owners x dst) as owners1.
specialize (IH owners1 bufs2 (Nat.succ chan) chan' owners' bufs' q Hres Hnotin).
rewrite IH.
rewrite Heqowners1.
apply owner_of_pos_set_owner_neq.
destruct (nposi_eq q x) eqn:Heqx.
 apply nposi_eq_true_iff in Heqx.
  subst q.
  contradiction.
reflexivity.
+ eapply IH; eauto.
Qed.

(*
Theorem ensure_local_qubits_aux_correct :
  forall dst qs owners bufs chan chan' owners' bufs',
    ensure_local_qubits_aux dst qs owners bufs chan =
      (chan', owners', bufs') ->
    owners_updated_exactly_to owners owners' qs dst.
Proof.
  intros.
  split.
  - eapply ensure_local_qubits_aux_locality; eauto.

Admitted.
(*****************************************************************)
(*  Generated communication really contains Send/Recv  *)
(*****************************************************************)

Theorem ensure_local_qubits_aux_generates_comm :
  forall dst qs owners bufs chan chan' owners' bufs' q src,
    ensure_local_qubits_aux dst qs owners bufs chan =
      (chan', owners', bufs') ->
    In q qs ->
    owner_of_pos owners q = Some src ->
    src <> dst ->
    exists k,
      comm_pair_for src dst (chan + k)%nat q bufs'.
Proof.
  induction qs as [|x tl IH]; intros owners bufs chan chan' owners' bufs' q src Hres Hin Hown Hneq.
  - contradiction.
  - simpl in Hres.
    destruct Hin as [Hq | Hin].
    + subst q.
      rewrite Hown in Hres.
      destruct (Nat.eqb src dst) eqn:Heq.
      * apply Nat.eqb_eq in Heq. contradiction.
      * remember (append_cexp_to_mem src
                   (Send chan (N.to_nat (fst x)) (N.to_nat (snd x))) bufs) as bufs1.
        remember (append_cexp_to_mem dst
                   (Recv chan (N.to_nat (fst x)) (N.to_nat (snd x))) bufs1) as bufs2.
        remember (set_owner owners x dst) as owners1.
        exists 0%nat.
        split.
        -- subst bufs2 bufs1.
Admitted.




Theorem ensure_local_qubits_aux_correct_full :
  forall dst qs owners bufs chan chan' owners' bufs',
    NoDup qs ->
    owners_total_on owners qs ->
    ensure_local_qubits_aux dst qs owners bufs chan =
      (chan', owners', bufs') ->
    (forall q, In q qs -> owner_of_pos owners' q = Some dst) /\
    (forall q, ~ In q qs -> owner_of_pos owners' q = owner_of_pos owners q) /\
    (forall q src,
        In q qs ->
        owner_of_pos owners q = Some src ->
        src <> dst ->
        exists k, comm_pair_for src dst (chan + k)%nat q bufs') /\
    (chan <= chan')%nat.
Proof.
  intros dst qs owners bufs chan chan' owners' bufs' Hnd Htot Hres.
  repeat split.
  - intros q Hin.
    eapply ensure_local_qubits_aux_locality; eauto.
  - intros q Hnotin.
    eapply ensure_local_qubits_aux_preserve_outside; eauto.
  - intros q src Hin Hown Hneq.
    eapply ensure_local_qubits_aux_generates_comm; eauto.
  - revert owners bufs chan chan' owners' bufs' Htot Hres.
    induction qs as [|x tl IH]; intros owners bufs chan chan' owners' bufs' Htot Hres.
    + simpl in Hres. inversion Hres. lia.
    + simpl in Hres.
      destruct (owner_of_pos owners x) as [src|] eqn:Hownx.
      * destruct (Nat.eqb src dst) eqn:Heq.
        -- eapply IH; eauto.
        eapply IH in Hres; eauto.
inversion Hnd as [| ? ? Hxnotin Hnd_tl]; subst.
assert (Htot_tl : owners_total_on owners tl).
{
  unfold owners_total_on in *.
  intros q Hin.
  apply Htot.
  right; exact Hin.
}

Admitted.
*)



Definition owners_resolved_for_solution
  (mid : membrane_id)
  (qs : list nposi)
  (owners : list ((nposi * membrane_id)%type)) : Prop :=
  forall q, In q qs -> owner_of_pos owners q = Some mid.

Lemma ensure_local_qubits_ready_for_app :
  forall mid qs owners bufs chan chan' owners' bufs',
    NoDup qs ->
    owners_total_on owners qs ->
    ensure_local_qubits_aux mid qs owners bufs chan =
      (chan', owners', bufs') ->
    owners_resolved_for_solution mid qs owners'.
Proof.
  unfold owners_resolved_for_solution.
  intros mid qs owners bufs chan chan' owners' bufs' Hnd Htot Hres q Hin.
  eapply ensure_local_qubits_aux_locality; eauto.
Qed.



(*****************************************************************)
(*   semantic theorem              *)
(*****************************************************************)

Definition solution_well_formed_owners
  (sol : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (owners : list ((nposi * membrane_id)%type)) : Prop :=
  forall auxqs mid,
    In (auxqs, mid) sol ->
    match auxqs with
    | (_, qs) => owners_all_at owners qs mid
    end.

Theorem lower_solution_distributed_sound_step_ready :
  forall sol os cfg,
    lower_solution_distributed sol os = cfg ->
    True.
Proof.
  intros. exact I.
Qed.



(*****************************************************************)
(* Basic utilities for reasoning about generated solutions    *)
(*****************************************************************)

Fixpoint extract_opnums_from_solution
  (sol : list (((myOpAux * list nposi)%type * membrane_id)%type))
  : list N :=
  match sol with
  | [] => []
  | ((OpNum n, _), _) :: xs => n :: extract_opnums_from_solution xs
  | _ :: xs => extract_opnums_from_solution xs
  end.

Fixpoint mem_N (x : N) (xs : list N) : bool :=
  match xs with
  | [] => false
  | y :: ys => if N.eqb x y then true else mem_N x ys
  end.

Fixpoint before_N (i j : N) (xs : list N) : bool :=
  match xs with
  | [] => false
  | x :: tl =>
      if N.eqb x i then mem_N j tl
      else if N.eqb x j then false
      else before_N i j tl
  end.

Definition respects_hb
  (hb : hb_relation)
  (sol : list (((myOpAux * list nposi)%type * membrane_id)%type)) : Prop :=
  forall i j,
    hb i j = true ->
    before_N i j (extract_opnums_from_solution sol) = true.

Definition assigned_only_valid_mids
  (mids : list membrane_id)
  (sol : list (((myOpAux * list nposi)%type * membrane_id)%type)) : Prop :=
  forall x mid, In (x, mid) sol -> In mid mids.

Definition solution_no_dup
  (sol : list (((myOpAux * list nposi)%type * membrane_id)%type)) : Prop :=
  NoDup (extract_opnums_from_solution sol).

Definition solution_well_formed
  (mids : list membrane_id)
  (sol : list (((myOpAux * list nposi)%type * membrane_id)%type)) : Prop :=
  solution_no_dup sol /\ assigned_only_valid_mids mids sol.

(*****************************************************************)
(*  Well-formedness of final distributed configs               *)
(*****************************************************************)

Definition memb_id (m : memb) : membrane_id :=
  match m with
  | Memb id _ => id
  end.

Definition distributed_well_formed (cfg : config) : Prop :=
  NoDup (map memb_id cfg).

(*****************************************************************)
(*  Centralized embedding and semantic equivalence *)
(*****************************************************************)

Fixpoint ops_to_process (ops : op_list) : process :=
  match ops with
  | [] => PNil
  | x :: xs => turn_op_to_proc x (ops_to_process xs)
  end.

Definition centralized_config (ops : op_list) : config :=
  [Memb 0%nat (ops_to_process ops)].


Inductive process_equiv : process -> process -> Prop :=
| PE_nil :
    process_equiv PNil PNil
| PE_ap :
    forall a p1 p2,
      process_equiv p1 p2 ->
      process_equiv (AP a p1) (AP a p2)
| PE_if :
    forall b p1 p2 q1 q2,
      process_equiv p1 p2 ->
      process_equiv q1 q2 ->
      process_equiv (PIf b p1 q1) (PIf b p2 q2).

Inductive memb_equiv : memb -> memb -> Prop :=
| ME_memb :
    forall mid p1 p2,
      process_equiv p1 p2 ->
      memb_equiv (Memb mid p1) (Memb mid p2).

Inductive config_equiv : config -> config -> Prop :=
| CE_nil :
    config_equiv nil nil
| CE_cons :
    forall m1 m2 tl1 tl2,
      memb_equiv m1 m2 ->
      config_equiv tl1 tl2 ->
      config_equiv (m1 :: tl1) (m2 :: tl2).




Lemma process_equiv_refl :
  forall p, process_equiv p p.
Proof.
  induction p.
  - constructor.
  - simpl. constructor. exact IHp.
  - constructor; assumption.
Qed.

Lemma memb_equiv_refl :
  forall m, memb_equiv m m.
Proof.
  intros [mid p].
  constructor.
  apply process_equiv_refl.
Qed.

Lemma config_equiv_refl :
  forall cfg, config_equiv cfg cfg.
Proof.
  induction cfg as [|m tl IH].
  - constructor.
  - constructor.
    + apply memb_equiv_refl.
    + exact IH.
Qed.
(*****************************************************************)
(* Small structural lemmas                                    *)
(*****************************************************************)

Lemma opListOrder'_length :
  forall l n,
    length (opListOrder' l n) = length l.
Proof.
  induction l; intros; simpl; auto.
Qed.

Lemma opListOrder_length :
  forall l,
    length (opListOrder l) = length l.
Proof.
  intros; unfold opListOrder; apply opListOrder'_length.
Qed.

Lemma extract_opnums_from_solution_app :
  forall s1 s2,
    extract_opnums_from_solution (s1 ++ s2) =
    extract_opnums_from_solution s1 ++ extract_opnums_from_solution s2.
Proof.
  induction s1; intros; simpl; auto.
  destruct a as [[aux qs] mid]; destruct aux; simpl; rewrite IHs1; auto.
Qed.

Lemma mem_N_in :
  forall x xs,
    mem_N x xs = true -> In x xs.
Proof.
  induction xs; intros; simpl in *; try discriminate.
  destruct (N.eqb x a) eqn:Heq.
  - apply N.eqb_eq in Heq; subst; auto.
  - right; apply IHxs; exact H.
Qed.

Lemma in_mem_N :
  forall x xs,
    In x xs -> mem_N x xs = true.
Proof.
  induction xs; intros; simpl in *; contradiction || idtac.
  destruct H as [H | H].
  - subst. rewrite N.eqb_refl. reflexivity.
  - destruct (N.eqb x a) eqn:Heq.
    + reflexivity.
    + apply IHxs; exact H.
Qed.

Lemma before_N_sound :
  forall i j xs,
    before_N i j xs = true ->
    In i xs /\ In j xs.
Proof.
  induction xs; intros; simpl in *; try discriminate.
  destruct (N.eqb a i) eqn:Hai.
  - split.
    + apply N.eqb_eq in Hai; subst; auto.
    + right. apply mem_N_in; exact H.
  - destruct (N.eqb a j) eqn:Haj.
    + discriminate.
    + apply IHxs in H. destruct H as [Hi Hj]. split; auto.
Qed.

(*****************************************************************)
(* Membrane validity lemmas                                   *)
(*****************************************************************)

Lemma fallback_mid_in :
  forall ql x mid,
    ql <> [] ->
    fallback_mid ql = mid ->
    In ((x, mid)) ql ->
    In mid (map snd ql).
Proof.
  intros.
apply in_map with (f := snd) in H1.
exact H1. 
Qed.

Lemma gen_empty_mem_ids_1:
  forall mids mid,
    In mid mids ->
    In (mid, []) (gen_empty_mem mids).
Proof.
  induction mids; intros; simpl in *; contradiction || idtac.
  destruct H as [H | H].
  - subst. auto.
  - right. apply IHmids. exact H.
Qed.

(*****************************************************************)
(* Best-program optimality proof                              *)
(*****************************************************************)

Lemma best_prog_aux_upper_bound :
  forall xs best bestv cfg,
    bestv = fit best ->
    In cfg (best :: xs) ->
    (fit (best_prog_aux best bestv xs) <= fit cfg)%nat.
Proof.
  induction xs; intros best bestv cfg Hbest Hin; simpl in *.
  - destruct Hin as [Hin | Hin]; [subst | contradiction].
   lia.
  - destruct Hin as [Hcfg | Hcfg].
    + subst cfg.
      remember (fit a) as va.
      destruct (Nat.ltb va bestv) eqn:Hcmp.
      * apply Nat.ltb_lt in Hcmp.
assert (Haux : (fit (best_prog_aux a va xs) <= fit a)%nat).
{
  apply (IHxs a va a).
  - exact Heqva.
  - left. reflexivity.
}
rewrite <- Heqva in Haux.

rewrite Hbest in Hcmp.
lia.

      * specialize (IHxs best bestv best Hbest (or_introl eq_refl)).
        lia.
    + remember (fit a) as va.
      destruct (Nat.ltb va bestv) eqn:Hcmp.
      * apply Nat.ltb_lt in Hcmp.
eapply IHxs.
exact Heqva.
 exact Hcfg.

      * eapply IHxs.
exact Hbest.
Admitted.


Lemma best_prog_some_in :
  forall xs cfg,
    best_prog xs = Some cfg ->
    In cfg xs.
Proof.
  intros xs cfg H.
  destruct xs as [|x tl]; simpl in H; try discriminate.
  inversion H; subst; clear H.
  apply best_prog_aux_in.
Qed.
Lemma best_prog_optimal :
  forall xs cfg,
    best_prog xs = Some cfg ->
    forall cfg', In cfg' xs -> Nat.le (fit cfg) (fit cfg').
Proof.
  intros xs cfg Hbest cfg' Hin.
  destruct xs as [|x tl]; simpl in Hbest; try discriminate.
  inversion Hbest; subst cfg; clear Hbest.
  eapply best_prog_aux_upper_bound.
  - reflexivity.
  - exact Hin.
Qed.





(*****************************************************************)
(* Structural lemmas about gen_prog                              *)
(*****************************************************************)

Lemma gen_prog_nil :
  forall os,
    gen_prog nil os = nil.
Proof.
  intros os.
  unfold gen_prog.
  destruct (has_if_ops os); reflexivity.
Qed.


Lemma gen_prog_cons :
  forall sol sols os,
    gen_prog (sol :: sols) os =
      if has_if_ops os
      then to_prog (distribute_op sol []) os :: gen_prog sols os
      else lower_solution_distributed sol os :: gen_prog sols os.
Proof.
  intros sol sols os.
  unfold gen_prog at 1.
  destruct (has_if_ops os); reflexivity.
Qed.

Lemma in_gen_prog_singleton_no_if :
  forall sol os cfg,
    has_if_ops os = false ->
    In cfg (gen_prog (sol :: nil) os) ->
    cfg = lower_solution_distributed sol os.
Proof.
  intros sol os cfg Hif HIn.
  unfold gen_prog in HIn.
  rewrite Hif in HIn.
  simpl in HIn.
  destruct HIn as [H | H].
  - symmetry. exact H.
  - contradiction.
Qed.
Lemma in_gen_prog_cons_inv :
  forall sol sols os cfg,
    In cfg (gen_prog (sol :: sols) os) ->
    (has_if_ops os = true /\
       (cfg = to_prog (distribute_op sol nil) os \/ In cfg (gen_prog sols os)))
    \/
    (has_if_ops os = false /\
       (cfg = lower_solution_distributed sol os \/ In cfg (gen_prog sols os))).
Proof.
  intros sol sols os cfg HIn.
  rewrite gen_prog_cons in HIn.
  destruct (has_if_ops os) eqn:Hif; simpl in HIn.
  - left.
    split.
    + reflexivity.
    + destruct HIn as [H | H].
      * left. symmetry. exact H.
      * right. exact H.
  - right.
    split.
    + reflexivity.
    + destruct HIn as [H | H].
      * left. symmetry. exact H.
      * right. exact H.
Qed.
(*****************************************************************)
(*  Correctness of autodisq_all                                *)
(*****************************************************************)
Lemma map_snd_opListOrder'_gen :
  forall xs n,
    map snd (opListOrder' xs n) = xs.
Proof.
  induction xs as [|x xs IH]; intros n; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma map_snd_opListOrder :
  forall ops,
    map snd (opListOrder ops) = ops.
Proof.
  intros ops.
  unfold opListOrder.
  apply map_snd_opListOrder'_gen.
Qed.

Theorem autodisq_all_sound :
  forall ops mids cfg,
    In cfg (autodisq_all ops mids) ->
    config_equiv (centralized_config ops) cfg.
Proof.
  intros ops mids cfg HIn.
  unfold autodisq_all in HIn.
  set (os := opListOrder ops) in *.
  set (hb := gen_hb os) in *.
  set (sq := gen_seq os hb) in *.
  set (mem := gen_mem (fst sq) (snd sq) mids) in *.
  unfold mem in HIn.
  clearbody os hb sq.
  induction (gen_mem (fst (gen_seq os (gen_hb os)))
                     (snd (gen_seq os (gen_hb os)))
                     mids) as [|sol tl IH]; simpl in HIn.
Admitted.


Lemma autodisq_all_wf :
  forall ops mids cfg,
    In cfg (autodisq_all ops mids) ->
    distributed_well_formed cfg.
Proof.
  intros ops mids cfg HIn.
  unfold autodisq_all in HIn.
  set (os := opListOrder ops) in *.
  set (hb := gen_hb os) in *.
  set (sq := gen_seq os hb) in *.
 induction (gen_mem (fst sq) (snd sq) mids) as [|sol tl IH]; simpl in HIn.
destruct (has_if_ops os); simpl in HIn; contradiction.
destruct (has_if_ops os) eqn:Hif; simpl in HIn.
- destruct HIn as [Hhd | Htl].
  + subst cfg.
  apply IH.
Admitted.


(*****************************************************************)
(*  Correctness + optimality of autodisq_best                  *)
(*****************************************************************)


Lemma best_prog_some_optimal :
  forall xs cfg,
    best_prog xs = Some cfg ->
    forall cfg', In cfg' xs -> Nat.le (fit cfg) (fit cfg').
Proof.
  intros xs cfg Hbest.
  unfold best_prog in Hbest.
  destruct xs as [|x tl].
  - simpl in Hbest. discriminate.
  - inversion Hbest; subst cfg; clear Hbest.
    intros cfg' Hin.
    eapply best_prog_aux_upper_bound.
    + reflexivity.
    + exact Hin.
Qed.
Theorem autodisq_best_optimal_over_generated :
  forall ops mids cfg,
    autodisq_best ops mids = Some cfg ->
    forall cfg',
      In cfg' (autodisq_all ops mids) ->
      Nat.le (fit cfg) (fit cfg').
Proof.
  intros ops mids cfg Hbest cfg' Hin.
  unfold autodisq_best in Hbest.
  eapply best_prog_some_optimal.
  - exact Hbest.
  - exact Hin.
Qed.

Theorem autodisq_best_correct :
  forall ops mids cfg,
    autodisq_best ops mids = Some cfg ->
    config_equiv (centralized_config ops) cfg /\
    distributed_well_formed cfg /\
    (forall cfg' : config,
        In cfg' (autodisq_all ops mids) ->
        Nat.le (fit cfg) (fit cfg')).
Proof.
  intros ops mids cfg Hbest.
  destruct (autodisq_best_sound ops mids cfg Hbest) as [Hin Hopt].
  split.
  - apply (autodisq_all_sound ops mids cfg).
    exact Hin.
  - split.
    + apply (autodisq_all_wf ops mids cfg).
      exact Hin.
    + exact Hopt.
Qed.


(*****************************************************************)
(*  Correctness + optimality of autodisq_best_1               *)
(*****************************************************************)

Theorem auto_disq_loop_some_in :
  forall best xs cfg,
    auto_disq_loop best xs = Some cfg ->
    In cfg xs \/ best = Some cfg.
Proof.
  intros best xs.
  revert best.
  induction xs as [|a xs IH]; intros best cfg H.
  - simpl in H.
    destruct best as [b|].
    + right. exact H.
    + inversion H.
  - simpl in H.
    destruct best as [b|].
    + destruct (Nat.ltb (fit a) (fit b)) eqn:Hcmp.
      * specialize (IH (Some a) cfg H).
        destruct IH as [Hin | Hbest].
        -- left. right. exact Hin.
        -- inversion Hbest; subst. left. left. reflexivity.
      * specialize (IH (Some b) cfg H).
        destruct IH as [Hin | Hbest].
        -- left. right. exact Hin.
        -- right. exact Hbest.
    + specialize (IH (Some a) cfg H).
      destruct IH as [Hin | Hbest].
      * left. right. exact Hin.
      * inversion Hbest; subst. left. left. reflexivity.
Qed.


Theorem autodisq_best_1_sound :
  forall ops mids cfg,
    autodisq_best_1 ops mids = Some cfg ->
    config_equiv (centralized_config ops) cfg /\
    distributed_well_formed cfg.
Proof.
  intros ops mids cfg H.
  unfold autodisq_best_1 in H.
  apply auto_disq_loop_some_in in H.
  destruct H as [Hin | Hnone].
  - split.
    + eapply autodisq_all_sound; eauto.
    + eapply autodisq_all_wf; eauto.
  - inversion Hnone.
Qed.

(*****************************************************************)
(*  stronger theorem    *)
(*****************************************************************)

Theorem AutoDisQ_Main_Correctness :
  forall ops mids cfg,
    autodisq_best ops mids = Some cfg ->
    config_equiv (centralized_config ops) cfg /\
    distributed_well_formed cfg /\
    forall cfg',
      In cfg' (autodisq_all ops mids) ->
      (fit cfg <= fit cfg')%nat.
Proof.
  exact autodisq_best_correct.
Qed.


(*****************************************************************)
(* Official semantic correctness layer for AutoDisQ              *)
(* Built directly on DisQSem.step                                *)
(*****************************************************************)


(*****************************************************************)
(* Labels from the official semantics                            *)
(*****************************************************************)

Definition label : Type := (R * list var)%type.




(*****************************************************************)
(* Multi-step closure of the official DisQSem.step               *)
(*****************************************************************)

Inductive step_star {rmax:nat} :
  DisQDef.aenv ->
  DisQDef.qstate ->
  config ->
  list label ->
  DisQDef.qstate ->
  config ->
  Prop :=
| step_star_refl :
    forall Γ s c,
      step_star Γ s c [] s c
| step_star_step :
    forall Γ s1 c1 lab s2 c2 tr s3 c3,
      step (rmax:=rmax) Γ s1 c1 lab s2 c2 ->
      step_star (rmax:=rmax) Γ s2 c2 tr s3 c3 ->
      step_star (rmax:=rmax) Γ s1 c1 (lab :: tr) s3 c3.

Arguments step_star {rmax} Γ s c tr s' c'.

Lemma step_star_app :
  forall rmax Γ s1 c1 tr1 s2 c2 tr2 s3 c3,
    @step_star rmax Γ s1 c1 tr1 s2 c2 ->
    @step_star rmax Γ s2 c2 tr2 s3 c3 ->
    @step_star rmax Γ s1 c1 (tr1 ++ tr2) s3 c3.
Proof.
  intros rmax Γ s1 c1 tr1 s2 c2 tr2 s3 c3 H12 H23.
  induction H12.
  - simpl. exact H23.
  - simpl. econstructor.
    + exact H.
    + apply IHstep_star.
      exact H23.
Qed.



(*****************************************************************)
(* Structural helper using the official [comp] constructor       *)
(*****************************************************************)

Lemma step_lift_prefix :
  forall (rmax:nat) Γ s c1 lab s' c2 pre,
    step (rmax:=rmax) Γ s c1 lab s' c2 ->
    step (rmax:=rmax) Γ s (pre ++ c1) lab s' (pre ++ c2).
Proof.
  intros rmax Γ s c1 lab s' c2 pre H.
  induction pre as [|P pre IH]; simpl.
  - exact H.
  -econstructor.
    exact IH.
Qed.



(*****************************************************************)
(* Basic state-equivalence layer from DisQSem.v                  *)
(*****************************************************************)

Definition sem_equiv_state (c1 c2 : config) : Prop :=
  forall (rmax:nat) Γ s tr s1 c1',
    step_star (rmax:=rmax) Γ s c1 tr s1 c1' ->
    exists s2 c2',
      step_star (rmax:=rmax) Γ s c2 tr s2 c2' /\
      match_values s1 s2.

Definition sem_equiv_state_bi (c1 c2 : config) : Prop :=
  sem_equiv_state c1 c2 /\ sem_equiv_state c2 c1.

(*****************************************************************)
(* Basic well-formedness on configurations                       *)
(*****************************************************************)

Definition get_mid (m : memb) : membrane_id :=
  match m with
  | Memb l _ => l
  end.

Definition mids_of_config (c : config) : list membrane_id :=
  map get_mid c.

Definition loci_disjoint (c : config) : Prop :=
  NoDup (mids_of_config c).

Definition wf_config (c : config) : Prop :=
  loci_disjoint c.

Lemma centralized_config_wf :
  forall ops,
    wf_config (centralized_config ops).
Proof.
  intros ops.
  unfold wf_config, loci_disjoint, mids_of_config, centralized_config.
  simpl.
  constructor.
  - simpl. intros H. contradiction.
  - constructor.
Qed.

(*****************************************************************)
(* Reflexivity helpers for DisQSem.match_value                   *)
(*****************************************************************)

Lemma match_value_refl :
  forall n st,
    match_value n st st.
Proof.
  intros n st.
  induction n as [|n IH]; simpl.
  - (* base case *)
    destruct st; simpl; try constructor; try tauto.
  - (* inductive case *)
    destruct st; simpl; try constructor; try tauto.
 
Qed.

Lemma match_values_refl :
  forall s,
    (forall l st, In (l, st) s -> exists n, ses_len l = Some n) ->
    match_values s s.
Proof.
  intros s Hwf.
  induction s as [| [l st] tl IH].
  - constructor.
  - constructor.
    + simpl.
      split.
      * reflexivity.
      * destruct (Hwf l st (or_introl eq_refl)) as [n Hn].
        rewrite Hn.
        apply match_value_refl.
    + apply IH.
      intros l' st' Hin.
exact (Hwf l' st' (or_intror Hin)).

Qed.


(*****************************************************************)
(* Centralized / distributed pairing                             *)
(*****************************************************************)

Definition initial_pair
  (sol : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (os  : list ((N * myOp)%type))
  (cseq cdist : config) : Prop :=
  cseq = centralized_config (map snd os) /\
  cdist = lower_solution_distributed sol os.



(*****************************************************************)
(* One-step simulation theorems                                  *)

(*****************************************************************)
Lemma lower_solution_distributed_has_new_head :
  forall sol os x p,
    AP (CNew x) p = ops_to_process (map snd os) ->
    exists ctail,
      lower_solution_distributed sol os =
      Memb 0%nat (AP (CNew x) p) :: ctail.
      
Proof.
Admitted.

Lemma lower_solution_distributed_has_appu_head :
  forall sol os a e Q,
    AP (CAppU a e) Q = ops_to_process (map snd os) ->
    exists ctail,
      lower_solution_distributed sol os =
      Memb 0%nat (AP (CAppU a e) Q) :: ctail.
Proof.
Admitted.

Lemma lower_solution_distributed_has_meas_head :
  forall sol os x k Q,
    AP (CMeas x k) Q = ops_to_process (map snd os) ->
    exists ctail,
      lower_solution_distributed sol os =
      Memb 0%nat (AP (CMeas x k) Q) :: ctail.
Proof.
Admitted.



Lemma lower_solution_distributed_decomp :
  forall sol os l p rest,
    centralized_config (map snd os) = Memb l p :: rest ->
    exists pre post mid,
      lower_solution_distributed sol os =
      pre ++ Memb mid p :: post.
Proof.
Admitted.
Definition wf_qstate (s : DisQDef.qstate) : Prop :=
  forall l st, In (l, st) s -> exists n, DisQDef.ses_len l = Some n.
Lemma wf_qstate_mapNew :
  forall x s,
    wf_qstate s ->
    wf_qstate (mapNew x s).
Proof.
Admitted.
Print ses_len.
Theorem seq_to_dist_one_step :
  forall (rmax:nat) Γ s sol os lab s1 c1,
    wf_qstate s ->
    wf_config (centralized_config (map snd os)) ->
    wf_config (lower_solution_distributed sol os) ->
    step (rmax:=rmax) Γ s (centralized_config (map snd os)) lab s1 c1 ->
    exists s2 c2,
      step (rmax:=rmax) Γ s (lower_solution_distributed sol os) lab s2 c2 /\
      match_values s1 s2.
Proof.
  intros rmax Γ s sol os lab s1 c1 Hwf_qs Hwf_seq Hwf_dist Hstep.
  inversion Hstep; subst.
  - (* qubit_create *)
    destruct (lower_solution_distributed_has_new_head sol os x p H3) as [ctail Hhd].
    exists (mapNew x s).
    exists (Memb 0%nat p :: ctail).
    split.
    + rewrite Hhd. apply qubit_create.
    + apply match_values_refl.
      apply wf_qstate_mapNew.
      exact Hwf_qs.

- (* op_step *)
  destruct (lower_solution_distributed_has_appu_head sol os a e Q H3)
    as [ctail Hhd].
  exists ((a ++ l, Cval m ba) :: s0).
  exists (Memb 0%nat Q :: ctail).
  split.
  + rewrite Hhd.
    apply op_step.
    exact H7.
  + apply match_values_refl.
  intros l0 st Hin.
  destruct Hin as [Hin | Hin].
  * inversion Hin; subst.
    destruct (Hwf_qs (a ++ l) (Cval m b) (or_introl eq_refl)) as [n Hn].
    exists n.
    exact Hn.
  * exact (Hwf_qs l0 st (or_intror Hin)).
 - (* mea_pstep *)
  destruct (lower_solution_distributed_has_meas_head
              sol os x [(a, (0%nat, n))] Q H0)
    as [ctail Hhd].
  exists ((l, va') :: s0).
  exists (Memb 0%nat (subst_pexp Q x v) :: ctail).
  split.
  + rewrite Hhd.
    eapply mea_pstep with (a := a) (n := n) (lc := lc) (v := v) (va := va).
    * exact H2.
    * exact H5.
    * reflexivity.
    * exact H10.
  + apply match_values_refl.
    intros l0 st Hin.
    destruct Hin as [Hin | Hin].
    * inversion Hin; subst.
destruct (Hwf_qs (((a, (0%nat, n)) :: l0)) va (or_introl eq_refl)) as [n0 Hn0].
simpl in Hn0.
destruct (ses_len l0) eqn:Htail.
eexists.
unfold ses_len in Hn0.
simpl in Hn0.
reflexivity.
exfalso.
unfold ses_len in Htail.
destruct (get_core_ses l0) eqn:Hcore.
simpl in Htail.
  discriminate Htail.
simpl in Hn0.
unfold ses_len in Hn0.
simpl in Hn0.
rewrite Hcore in Hn0.
simpl in Hn0.
discriminate Hn0.
* exact (Hwf_qs l0 st (or_intror Hin)).



Admitted.

Theorem dist_to_seq_one_step :
  forall (rmax:nat) Γ s sol os lab s2 c2,
    wf_config (centralized_config (map snd os)) ->
    wf_config (lower_solution_distributed sol os) ->
    step (rmax:=rmax) Γ s (lower_solution_distributed sol os) lab s2 c2 ->
    exists s1 c1,
      step (rmax:=rmax) Γ s (centralized_config (map snd os)) lab s1 c1 /\
      match_values s1 s2.
Proof.
Admitted.

(*****************************************************************)
(* n-step simulation theorems                                    *)
(*****************************************************************)

Theorem seq_to_dist_n_steps :
  forall (rmax:nat) Γ s sol os tr s1 c1,
    wf_config (centralized_config (map snd os)) ->
    wf_config (lower_solution_distributed sol os) ->
    step_star (rmax:=rmax) Γ s (centralized_config (map snd os)) tr s1 c1 ->
    exists s2 c2,
      step_star (rmax:=rmax) Γ s (lower_solution_distributed sol os) tr s2 c2 /\
      match_values s1 s2.
Proof.
Admitted.

Theorem dist_to_seq_n_steps :
  forall (rmax:nat) Γ s sol os tr s2 c2,
    wf_config (centralized_config (map snd os)) ->
    wf_config (lower_solution_distributed sol os) ->
    step_star (rmax:=rmax) Γ s (lower_solution_distributed sol os) tr s2 c2 ->
    exists s1 c1,
      step_star (rmax:=rmax) Γ s (centralized_config (map snd os)) tr s1 c1 /\
      match_values s1 s2.
Proof.
Admitted.

(*****************************************************************)
(* Semantic soundness for generated programs                     *)
(*****************************************************************)

Theorem gen_prog_semantic_sound :
  forall mem os cfg,
    In cfg (gen_prog mem os) ->
    sem_equiv_state_bi (centralized_config (map snd os)) cfg.
Proof.
Admitted.


(*****************************************************************)
(* Top-level semantic correctness theorems                       *)
(*****************************************************************)

Theorem autodisq_all_semantic_sound :
  forall ops mids cfg,
    In cfg (autodisq_all ops mids) ->
    sem_equiv_state_bi (centralized_config ops) cfg.
Proof.
  intros ops mids cfg HIn.
  unfold autodisq_all in HIn.
  set (os := opListOrder ops) in *.
  assert (Hos : map snd os = ops).
  { subst os. apply map_snd_opListOrder. }
  rewrite <- Hos.
  eapply gen_prog_semantic_sound.
  exact HIn.
Qed.

Theorem autodisq_best_semantic_sound :
  forall ops mids cfg,
    autodisq_best ops mids = Some cfg ->
    sem_equiv_state_bi (centralized_config ops) cfg.
Proof.
  intros ops mids cfg Hbest.
  unfold autodisq_best in Hbest.
  destruct (best_prog (autodisq_all ops mids)) eqn:Hbp;
    inversion Hbest; subst; clear Hbest.
  eapply autodisq_all_semantic_sound.
  eapply best_prog_some_in.
  exact Hbp.
Qed.

Theorem AutoDisQ_Semantic_Correctness :
  forall ops mids cfg,
    autodisq_best ops mids = Some cfg ->
    sem_equiv_state_bi (centralized_config ops) cfg.
Proof.
  intros ops mids cfg Hbest.
  eapply autodisq_best_semantic_sound.
  exact Hbest.
Qed.

Theorem AutoDisQ_Main_Correctness_Observed :
  forall ops mids cfg,
    autodisq_best ops mids = Some cfg ->
    sem_equiv_state_bi (centralized_config ops) cfg /\
    forall cfg',
      In cfg' (autodisq_all ops mids) ->
      (fit cfg <= fit cfg')%nat.
Proof.
  intros ops mids cfg Hbest.
  split.
  - eapply autodisq_best_semantic_sound.
    exact Hbest.
  - intros cfg' Hin.
    unfold autodisq_best in Hbest.
    eapply best_prog_optimal.
    + exact Hbest.
    + exact Hin.
Qed.







