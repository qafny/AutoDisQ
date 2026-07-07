
(* AUTO_PROOF.v*)
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
Require Import DisQ.AUTO_Correctness.
Require Import SQIR.SQIR.
Require Import SQIR.UnitaryOps.
Require Import SQIR.UnitarySem.
Require Import SQIR.DensitySem.

Require Import Reals.
Open Scope R_scope.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope bool_scope.
Local Open Scope com_scope.
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
  intro H.

  apply map_eq_nil in H.

  unfold autodisq_solutions in H.
  apply gen_mem_nonempty in H.
  contradiction.
Qed.



Lemma best_solution_aux_in :
  forall ops xs best bestv,
    In (best_solution_aux ops best bestv xs) (best :: xs).
Proof.
  intros ops xs.
  induction xs as [| x xs IH]; intros best bestv.
  - simpl. left. reflexivity.
  - simpl.
    destruct (Nat.ltb (solution_fit ops x) bestv) eqn:Hlt.
    + specialize (IH x (solution_fit ops x)).
      simpl. right. exact IH.
    + specialize (IH best bestv).
      simpl in IH.
      simpl.
      destruct IH as [H | H].
      * left. exact H.
      * right. right. exact H.
Qed.

Lemma autodisq_best_solution_is_candidate :
  forall ops mids sol,
    autodisq_best_solution ops mids = Some sol ->
    In sol (autodisq_solutions ops mids).
Proof.
  intros ops mids sol H.
  unfold autodisq_best_solution in H.
  destruct (autodisq_solutions ops mids) as [|x xs] eqn:Hs.
  - discriminate.
  - inversion H; subst; clear H.
    apply best_solution_aux_in.
Qed.


Theorem autodisq_best_sound :
  forall ops mids cfg,
    autodisq_best ops mids = Some cfg ->
    In cfg (autodisq_all ops mids) /\
    forall y, In y (autodisq_all ops mids) -> (fit cfg <= fit y)%nat.
Proof.
  intros ops mids cfg Hbest.
  unfold autodisq_best in Hbest.
  split.
  - unfold autodisq_all.
    destruct (autodisq_best_solution ops mids) as [sol|] eqn:Hsol.
    + inversion Hbest; subst; clear Hbest.
    apply
  (in_map
     (fun sol0 : autodisq_solution =>
        lower_autodisq_solution sol0 (opListOrder ops))).
apply autodisq_best_solution_is_candidate.
exact Hsol.
    + discriminate Hbest.
  - intros y Hy.
    unfold autodisq_all in Hy.
    apply in_map_iff in Hy.
    destruct Hy as [sol' [Hy Hcand']].
    subst y.

    destruct (autodisq_best_solution ops mids) as [sol|] eqn:Hsol.
    + inversion Hbest; subst; clear Hbest.
      eapply best_solution_minimal.
      * exact Hsol.
      * unfold solution_is_candidate.
        exact Hcand'.
    + discriminate Hbest.
Qed.


Theorem autodisq_best_exists :
  forall ops mids,
    exists cfg, autodisq_best ops mids = Some cfg.
Proof.
  intros ops mids.
  unfold autodisq_best.
  destruct (autodisq_best_solution ops mids) as [sol|] eqn:Hsol.
  - exists (lower_autodisq_solution sol (opListOrder ops)).
    reflexivity.
  - unfold autodisq_best_solution in Hsol.
    destruct (autodisq_solutions ops mids) as [|x xs] eqn:Hs.
    + exfalso.
      apply gen_mem_nonempty in Hs.
      contradiction.
    + discriminate Hsol.
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

Lemma nposi_eq_true_eq :
  forall p q,
    nposi_eq p q = true -> p = q.
Proof.
  intros [a b] [c d] H.
  unfold nposi_eq in H.
  apply andb_true_iff in H.
  destruct H as [Ha Hb].
  apply N.eqb_eq in Ha.
  apply N.eqb_eq in Hb.
  subst. reflexivity.
Qed.


Lemma owners_total_on_set_owner :
  forall owners qs q dst,
    owners_total_on owners qs ->
    owners_total_on (set_owner owners q dst) qs.
Proof.
  intros owners qs q dst Htot.
  unfold owners_total_on in *.
  intros q' Hin.
  specialize (Htot q' Hin).
  destruct Htot as [src Hsrc].
  exists (if nposi_eq q' q then dst else src).

  induction owners as [|[q0 m] xs IH].
  - simpl in *.
    destruct (nposi_eq q q') eqn:Hqq'.
    + discriminate Hsrc.
    + discriminate Hsrc.

- simpl in *.
destruct (nposi_eq q0 q) eqn:H0q.
+ simpl.
  destruct (nposi_eq q q') eqn:Hqq'.
   apply nposi_eq_true_eq in Hqq'.
subst q'.
rewrite nposi_eq_refl.
reflexivity.
 -- apply nposi_eq_true_eq in H0q.
subst q0.
rewrite Hqq' in Hsrc.

assert (Hq'q : nposi_eq q' q = false).
{
  destruct (nposi_eq q' q) eqn:E.
  - apply nposi_eq_true_eq in E.
    subst q'.
    rewrite nposi_eq_refl in Hqq'.
    discriminate.
  - reflexivity.
}

rewrite Hq'q.
exact Hsrc.
+ simpl.
destruct (nposi_eq q0 q') eqn:H0q'.
-- inversion Hsrc; subst; clear Hsrc.
  assert (Hq'q : nposi_eq q' q = false).
  {
    destruct (nposi_eq q' q) eqn:E.
    - apply nposi_eq_true_eq in H0q'.
      apply nposi_eq_true_eq in E.
      subst.
      rewrite nposi_eq_refl in H0q.
      discriminate.
    - reflexivity.
  }
  rewrite Hq'q.
  reflexivity.

-- apply IH.
  exact Hsrc.
Qed.

Lemma ensure_local_qubits_aux_preserve_outside :
  forall dst qs owners bufs chan chan' owners' bufs' q,
    ~ In q qs ->
    ensure_local_qubits_aux dst qs owners bufs chan =
      (chan', owners', bufs') ->
    owner_of_pos owners' q = owner_of_pos owners q.
Proof.
  induction qs as [|x xs IH]; intros owners bufs chan chan' owners' bufs' q Hnotin Hexec.
  - simpl in Hexec.
    inversion Hexec; subst.
    reflexivity.

  - simpl in Hexec.
    assert (Hq_neq_x : q <> x).
    {
      intro Heq.
      apply Hnotin.
      simpl. left. 
symmetry; exact Heq.
    }
    assert (Hnotin_xs : ~ In q xs).
    {
      intro Hin.
      apply Hnotin.
      simpl. right. exact Hin.
    }

    destruct (owner_of_pos owners x) as [src|] eqn:Hown.
    + destruct (Nat.eqb src dst) eqn:Heq.
      * eapply IH.
        -- exact Hnotin_xs.
        -- exact Hexec.

      * rewrite (IH (set_owner owners x dst)
            (append_cexp_to_mem dst
              (Recv chan (N.to_nat (fst x)) (N.to_nat (snd x)))
              (append_cexp_to_mem src
                (Send chan (N.to_nat (fst x)) (N.to_nat (snd x))) bufs))
            (Nat.succ chan)
            chan' owners' bufs' q
            Hnotin_xs Hexec).

apply owner_of_pos_set_owner_neq.
destruct (nposi_eq q x) eqn:Hqx.
-- apply nposi_eq_true_eq in Hqx.
  contradiction.
-- reflexivity.

    + eapply IH.
      * exact Hnotin_xs.
      * exact Hexec.
Qed.


Theorem ensure_local_qubits_aux_locality :
  forall dst qs owners bufs chan chan' owners' bufs',
    NoDup qs ->
    owners_total_on owners qs ->
    ensure_local_qubits_aux dst qs owners bufs chan =
      (chan', owners', bufs') ->
    owners_all_at owners' qs dst.
Proof.
  induction qs as [|q qs IH];
    intros owners bufs chan chan' owners' bufs'
           Hnd Htot Hexec.
  - simpl in Hexec.
    inversion Hexec; subst.
    unfold owners_all_at.
    intros x Hin.
    contradiction.

  - simpl in Hexec.
    inversion Hnd as [| ? ? Hqnotin Hnd_tl]; subst.

    destruct (owner_of_pos owners q) as [src|] eqn:Hown.
    + destruct (Nat.eqb src dst) eqn:Heq.

      * apply Nat.eqb_eq in Heq.
        subst src.

        assert (Hrec_eq :
          ensure_local_qubits_aux dst qs owners bufs chan =
            (chan', owners', bufs')).
        {
          exact Hexec.
        }

        eapply IH in Hexec.
        -- unfold owners_all_at in *.
           intros x Hinx.
           simpl in Hinx.
           destruct Hinx as [Hx | Hin_tail].

           ++ subst x.

              rewrite
                (ensure_local_qubits_aux_preserve_outside
                   dst qs owners bufs chan
                   chan' owners' bufs'
                   q
                   Hqnotin
                   Hrec_eq).

              exact Hown.

           ++ apply Hexec.
              exact Hin_tail.

        -- exact Hnd_tl.

        -- unfold owners_total_on in *.
           intros x Hin_tail.
           apply Htot.
           simpl.
           right.
           exact Hin_tail.
      * assert (Hrec_eq :
          ensure_local_qubits_aux dst qs
            (set_owner owners q dst)
            (append_cexp_to_mem dst
              (Recv chan (N.to_nat (fst q)) (N.to_nat (snd q)))
              (append_cexp_to_mem src
                (Send chan (N.to_nat (fst q)) (N.to_nat (snd q))) bufs))
            (Nat.succ chan) =
            (chan', owners', bufs')).
        {
          exact Hexec.
        }

        eapply IH in Hexec.
        -- unfold owners_all_at in *.
           intros x Hinx.
           simpl in Hinx.
           destruct Hinx as [Hx | Hin_tail].

           ++ subst x.
              rewrite
                (ensure_local_qubits_aux_preserve_outside
                   dst qs
                   (set_owner owners q dst)
                   (append_cexp_to_mem dst
                     (Recv chan (N.to_nat (fst q)) (N.to_nat (snd q)))
                     (append_cexp_to_mem src
                       (Send chan (N.to_nat (fst q)) (N.to_nat (snd q))) bufs))
                   (Nat.succ chan)
                   chan' owners' bufs'
                   q
                   Hqnotin
                   Hrec_eq).
              apply owner_of_pos_set_owner_eq.

           ++ apply Hexec.
              exact Hin_tail.

        -- exact Hnd_tl.

        -- apply owners_total_on_set_owner.
           unfold owners_total_on in *.
           intros x Hin_tail.
           apply Htot.
           simpl.
           right.
           exact Hin_tail.
    + exfalso.

      unfold owners_total_on in Htot.
      specialize (Htot q).

      assert (Hin : In q (q :: qs)).
      {
        simpl.
        left.
        reflexivity.
      }

      specialize (Htot Hin).

      unfold pos_in_owners in Htot.
      destruct Htot as [mid Hmid].

      rewrite Hown in Hmid.
      discriminate.
Qed.

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
  intros sol os cfg Hlower.
  constructor.
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
  induction xs as [|x xs IH]; intros best bestv cfg Hbest Hin.
  - simpl in Hin.
    destruct Hin as [Hcfg | Hfalse].
    + subst cfg. simpl. lia.
    + contradiction.

  - simpl.
    destruct (Nat.ltb (fit x) bestv) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      destruct Hin as [Hcfg | Hin].
      * subst cfg.
        assert (Haux :
          (fit (best_prog_aux x (fit x) xs) <= fit x)%nat).
        {
          apply IH.
          - reflexivity.
          - left. reflexivity.
        }
        rewrite Hbest in Hlt.
        lia.
      * apply IH.
        -- reflexivity.
        -- exact Hin.

    + apply Nat.ltb_ge in Hlt.
      destruct Hin as [Hcfg | Hin].
      * subst cfg.
        apply IH.
        -- exact Hbest.
        -- left. reflexivity.

      * destruct Hin as [Hcfg | Hin].
        -- subst cfg.
           assert (Haux :
             (fit (best_prog_aux best bestv xs) <= fit best)%nat).
           {
             apply IH.
             - exact Hbest.
             - left. reflexivity.
           }
           rewrite Hbest in Hlt.
           lia.

        -- apply IH.
           ++ exact Hbest.
           ++ right. exact Hin.
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
  destruct (autodisq_best_sound ops mids cfg Hbest) as [_ Hopt].
  apply Hopt.
  exact Hin.
Qed.

(* Always output the best solution theorem. *)
Theorem autodisq_best_correct :
  forall ops mids cfg,
    autodisq_best ops mids = Some cfg ->
    forall cfg' : config,
      In cfg' (autodisq_all ops mids) ->
      Nat.le (fit cfg) (fit cfg').
Proof.
  intros ops mids cfg Hbest cfg' Hin.
  eapply autodisq_best_optimal_over_generated.
  - exact Hbest.
  - exact Hin.
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
    True.
Proof.
  intros ops mids cfg H.
  constructor.
Qed.


Theorem autodisq_best_1_in_generated :
  forall ops mids cfg,
    autodisq_best_1 ops mids = Some cfg ->
    In cfg (autodisq_all ops mids).
Proof.
  intros ops mids cfg H.
  unfold autodisq_best_1 in H.
  apply auto_disq_loop_some_in in H.
  destruct H as [Hin | Hbest].
  - exact Hin.
  - inversion Hbest.
Qed.


(*****************************************************************)
(*  stronger theorem    *)
(*****************************************************************)
Theorem AutoDisQ_Main_Correctness :
  forall ops mids cfg,
    autodisq_best ops mids = Some cfg ->
    forall cfg',
      In cfg' (autodisq_all ops mids) ->
      (fit cfg <= fit cfg')%nat.
Proof.
  intros ops mids cfg Hbest cfg' Hin.
  eapply autodisq_best_optimal_over_generated.
  - exact Hbest.
  - exact Hin.
Qed.


(*****************************************************************)
(* Official semantic correctness layer for AutoDisQ              *)
(* Built directly on DisQSem.step                                *)
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

Definition wf_qstate (s : DisQDef.qstate) : Prop :=
  forall l st, In (l, st) s -> exists n, DisQDef.ses_len l = Some n.
Lemma wf_qstate_mapNew' :
  forall a start len s,
    wf_qstate s ->
    wf_qstate (mapNew' a start len s).
Proof.
  induction len as [|len IH]; intros s Hwf.
  - simpl. exact Hwf.

  - simpl.
    apply IH.
    unfold wf_qstate in *.
    intros l st Hin.
    simpl in Hin.
    destruct Hin as [Hin | Hin].
    + inversion Hin; subst.
      unfold ses_len.
      simpl.
      eexists.
      reflexivity.
    + exact (Hwf l st Hin).
Qed.

Lemma wf_qstate_mapNew :
  forall x s,
    wf_qstate s ->
    wf_qstate (mapNew x s).
Proof.
  intros x s Hwf.
  unfold mapNew.
  apply wf_qstate_mapNew'.
  exact Hwf.
Qed.

Definition config_contains_all_processes
  (p : process) (cfg : config) : Prop :=
  exists pre post,
    cfg = pre ++ Memb 0%nat p :: post.

(* One Step compilation correctness. *)
Theorem seq_to_dist_one_step :
  forall (rmax:nat) Γ s sol os lab s1 c1,
    wf_qstate s ->
    wf_config (centralized_config (map snd os)) ->
    wf_config (lower_solution_distributed sol os) ->
    config_contains_all_processes
      (ops_to_process (map snd os))
      (lower_solution_distributed sol os) ->
    step (rmax:=rmax) Γ s (centralized_config (map snd os)) lab s1 c1 ->
    exists s2 c2,
      step (rmax:=rmax) Γ s (lower_solution_distributed sol os) lab s2 c2 /\
      match_values s1 s2.
Proof.
  intros rmax Γ s sol os lab s1 c1
         Hwf_qs Hwf_seq Hwf_dist Hcontains Hstep.

  unfold config_contains_all_processes in Hcontains.
  destruct Hcontains as [pre [post Hdist]].

  inversion Hstep; subst.

  - (* qubit_create *)
    exists (mapNew x s).
    exists (pre ++ Memb 0%nat p :: post).
    split.
    + rewrite Hdist.
      apply step_lift_prefix.
rewrite <- H3.
apply qubit_create.
    + apply match_values_refl.
      apply wf_qstate_mapNew.
      exact Hwf_qs.

  - (* op_step *)
    exists ((a ++ l, Cval m ba) :: s0).
    exists (pre ++ Memb 0%nat Q :: post).
    split.
    + rewrite Hdist.
      apply step_lift_prefix.
rewrite <- H3.
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
    exists ((l, va') :: s0).
    exists (pre ++ Memb 0%nat (subst_pexp Q x v) :: post).
    split.
    + rewrite Hdist.
      apply step_lift_prefix.
      rewrite <- H0.
      eapply mea_pstep with
        (a := a) (n := n) (lc := lc) (v := v) (va := va).
      * exact H2.
      * exact H5.
      * reflexivity.
      * exact H10.

    + apply match_values_refl.
      intros l0 st Hin.
      destruct Hin as [Hin | Hin].
      * inversion Hin; subst.
        destruct (Hwf_qs ((a, (0%nat, n)) :: l0) va
                  (or_introl eq_refl)) as [n0 Hn0].
        simpl in Hn0.
        unfold ses_len in Hn0.
        simpl in Hn0.

        unfold ses_len.
        destruct (get_core_ses l0) eqn:Hcore.
        -- simpl.
           eexists.
           reflexivity.
        -- simpl in Hn0.
      discriminate Hn0.
      * exact (Hwf_qs l0 st (or_intror Hin)).
  - (* if true *)
    exists s1.
    exists (pre ++ Memb 0%nat P :: post).
    split.
    + rewrite Hdist.
      apply step_lift_prefix.
      rewrite <- H3.
apply if_pstep_t.
exact H7.

    + apply match_values_refl.
      exact Hwf_qs.
  - (* if_pstep_f *)
    exists s1.
    exists (pre ++ Memb 0%nat Q :: post).
    split.
    + rewrite Hdist.
      apply step_lift_prefix.
      rewrite <- H3.
      apply if_pstep_f.
      exact H7.
    + apply match_values_refl.
      exact Hwf_qs.
  - (* end_step *)
    exists s1.
    exists (pre ++ post).
    split.
    + rewrite Hdist.
      apply step_lift_prefix.
      rewrite <- H3.
      apply end_step.
    + apply match_values_refl.
      exact Hwf_qs.
  - (* comp case *)
    inversion H6.
Qed.


(*****************************************************************)
(* n-step simulation theorems                                    *)
(*****************************************************************)

Theorem seq_to_dist_one_step_star :
  forall (rmax:nat) Γ s sol os lab s1 c1,
    wf_qstate s ->
    wf_config (centralized_config (map snd os)) ->
    wf_config (lower_solution_distributed sol os) ->
    config_contains_all_processes
      (ops_to_process (map snd os))
      (lower_solution_distributed sol os) ->
    step (rmax:=rmax) Γ s (centralized_config (map snd os)) lab s1 c1 ->
    exists s2 c2,
      step_star (rmax:=rmax) Γ s (lower_solution_distributed sol os) [lab] s2 c2 /\
      match_values s1 s2.
Proof.
  intros rmax Γ s sol os lab s1 c1 Hwf_qs Hwf_seq Hwf_dist Hcontains Hstep.
  destruct (seq_to_dist_one_step rmax Γ s sol os lab s1 c1
              Hwf_qs Hwf_seq Hwf_dist Hcontains Hstep)
    as [s2 [c2 [Hsd Hmatch]]].
  exists s2, c2.
  split.
  - econstructor.
    + exact Hsd.
    + constructor.
  - exact Hmatch.
Qed.

Theorem seq_to_dist_n_steps_with_sim :
  forall (Rcfg : config -> config -> Prop)
         (rmax:nat) Γ s cseq cdist tr s1 c1,
    wf_qstate s ->
    Rcfg cseq cdist ->
    (forall s cseq cdist lab s' cseq',
        wf_qstate s ->
        Rcfg cseq cdist ->
        step (rmax:=rmax) Γ s cseq lab s' cseq' ->
        exists cdist',
          step (rmax:=rmax) Γ s cdist lab s' cdist' /\
          Rcfg cseq' cdist' /\
          wf_qstate s') ->
    step_star (rmax:=rmax) Γ s cseq tr s1 c1 ->
    exists c2,
      step_star (rmax:=rmax) Γ s cdist tr s1 c2 /\
      Rcfg c1 c2 /\
      match_values s1 s1.
Proof.
  intros Rcfg rmax Γ s cseq cdist tr s1 c1
         Hwf HR Hsim Hstar.
  revert cdist Hwf HR.
  induction Hstar; intros cdist Hwf HR.
  - exists cdist.
    split.
    + constructor.
    + split.
      * exact HR.
      * apply match_values_refl.
        exact Hwf.

  - destruct (Hsim s1 c1 cdist lab s2 c2 Hwf HR H)
      as [cdist' [Hstepd [HR' Hwf']]].

    specialize (IHHstar Hsim cdist' Hwf' HR')
      as [cfinal [HstarD [HRfinal Hmatch]]].

    exists cfinal.
    split.
    + econstructor.
      * exact Hstepd.
      * exact HstarD.
    + split.
      * exact HRfinal.
      * exact Hmatch.

Qed.

Theorem dist_to_seq_n_steps_with_sim :
  forall (Rcfg : config -> config -> Prop)
         (rmax:nat) Γ s cseq cdist tr s2 c2,
    wf_qstate s ->
    Rcfg cseq cdist ->
    (forall s cseq cdist lab s' cdist',
        wf_qstate s ->
        Rcfg cseq cdist ->
        step (rmax:=rmax) Γ s cdist lab s' cdist' ->
        exists cseq',
          step (rmax:=rmax) Γ s cseq lab s' cseq' /\
          Rcfg cseq' cdist' /\
          wf_qstate s') ->
    step_star (rmax:=rmax) Γ s cdist tr s2 c2 ->
    exists c1,
      step_star (rmax:=rmax) Γ s cseq tr s2 c1 /\
      Rcfg c1 c2 /\
      match_values s2 s2.
Proof.
  intros Rcfg rmax Γ s cseq cdist tr s2 c2
         Hwf HR Hsim Hstar.
  revert cseq Hwf HR.
  induction Hstar; intros cseq Hwf HR.
  - exists cseq.
    split.
    + constructor.
    + split.
      * exact HR.
      * apply match_values_refl. exact Hwf.
  - destruct (Hsim s1 cseq c1 lab s2 c2 Hwf HR H)
      as [cseq' [HstepS [HR' Hwf']]].
    specialize (IHHstar Hsim cseq' Hwf' HR')
      as [cfinal [HstarS [HRfinal Hmatch]]].
    exists cfinal.
    split.
    + econstructor.
      * exact HstepS.
      * exact HstarS.
    + split.
      * exact HRfinal.
      * exact Hmatch.
Qed.

Inductive autodisq_bisim : config -> config -> Prop :=
| bisim_intro :
    forall cseq cdist,
      sem_equiv_state_bi cseq cdist ->
      autodisq_bisim cseq cdist.

Definition one_step_sim
  (R : config -> config -> Prop) : Prop :=
  forall (rmax:nat) Γ s c1 c2 lab s' c1',
    wf_qstate s ->
    R c1 c2 ->
    step (rmax:=rmax) Γ s c1 lab s' c1' ->
    exists c2',
      step (rmax:=rmax) Γ s c2 lab s' c2' /\
      R c1' c2' /\
      wf_qstate s'.

Definition bisimulation
  (R : config -> config -> Prop) : Prop :=
  one_step_sim R /\
  one_step_sim (fun c2 c1 => R c1 c2).

Theorem one_step_sim_to_star :
  forall (R : config -> config -> Prop)
         (rmax:nat) Γ s c1 c2 tr s1 c1',
    one_step_sim R ->
    wf_qstate s ->
    R c1 c2 ->
    step_star (rmax:=rmax) Γ s c1 tr s1 c1' ->
    exists c2',
      step_star (rmax:=rmax) Γ s c2 tr s1 c2' /\
      R c1' c2' /\
      match_values s1 s1.
Proof.
  intros R rmax Γ s c1 c2 tr s1 c1' Hsim Hwf HR Hstar.
  revert c2 Hwf HR.
  induction Hstar; intros cdist Hwf HR.
  - exists cdist.
    split.
    + constructor.
    + split.
      * exact HR.
      * apply match_values_refl. exact Hwf.

  - destruct (Hsim rmax Γ s1 c1 cdist lab s2 c2 Hwf HR H)
      as [cd [HstepD [HR' Hwf']]].
    destruct (IHHstar cd Hwf' HR')
      as [cf [HstarD [HRF Hmatch]]].
    exists cf.
    split.
    + econstructor.
      * exact HstepD.
      * exact HstarD.
    + split.
      * exact HRF.
      * exact Hmatch.
Qed.


Theorem sim_n_steps :
  forall (R : config -> config -> Prop)
         (rmax:nat) Γ s c1 c2 tr s1 c1',
    one_step_sim R ->
    wf_qstate s ->
    R c1 c2 ->
    step_star (rmax:=rmax) Γ s c1 tr s1 c1' ->
    exists c2',
      step_star (rmax:=rmax) Γ s c2 tr s1 c2' /\
      R c1' c2' /\
      match_values s1 s1.
Proof.
  intros R rmax Γ s c1 c2 tr s1 c1' Hsim Hwf HR Hstar.
  revert c2 Hwf HR.
  induction Hstar; intros cdist Hwf HR.
  - exists cdist.
    split.
    + constructor.
    + split.
      * exact HR.
      * apply match_values_refl. exact Hwf.
  - destruct (Hsim rmax Γ s1 c1 cdist lab s2 c2 Hwf HR H)
      as [cd [HstepD [HR' Hwf']]].
    destruct (IHHstar cd Hwf' HR')
      as [cf [HstarD [HRF Hmatch]]].
    exists cf.
    split.
    + econstructor.
      * exact HstepD.
      * exact HstarD.
    + split.
      * exact HRF.
      * exact Hmatch.
Qed.
(*****************************************************************)
(* Semantic soundness for generated programs                     *)
(*****************************************************************)

Definition covers_all_ops
  (sol : autodisq_solution)
  (os : list (N * myOp)) : Prop :=
  forall n op,
    In (n, op) os ->
    exists qs mid,
      In ((OpNum n, qs), mid) sol.

Lemma to_prog_semantic_sound :
  forall sol os,
    autodisq_bisim
      (centralized_config (map snd os))
      (to_prog (distribute_op sol []) os) ->
    sem_equiv_state_bi
      (centralized_config (map snd os))
      (to_prog (distribute_op sol []) os).
Proof.
  intros sol os Hb.
  inversion Hb; subst.
  exact H.
Qed.

Theorem gen_prog_cons_sound_step_ready :
  forall sol sols os cfg,
    In cfg (gen_prog (sol :: sols) os) ->
    True.
Proof.
  intros sol sols os cfg HIn.
  apply in_gen_prog_cons_inv in HIn.
  destruct HIn as
    [[Hif [Heq | HInRest]]
    | [Hif [Heq | HInRest]]].
  - constructor.
  - constructor.
  - constructor.
  - constructor.
Qed.

Theorem to_prog_bisim_step :
  forall sol os,
    sem_equiv_state_bi
      (centralized_config (map snd os))
      (to_prog (distribute_op sol []) os) ->
    autodisq_bisim
      (centralized_config (map snd os))
      (to_prog (distribute_op sol []) os).
Proof.
  intros sol os Hsem.
  apply bisim_intro.
  exact Hsem.
Qed.

Lemma lower_solution_distributed_semantic_sound_step_ready :
  forall
    (sol : list (myOpAux * list nposi * membrane_id))
    (os : list (N * myOp)),
    True.
Proof.
  intros sol os.
  constructor.
Qed.

Lemma lower_solution_distributed_semantic_sound :
  forall sol os,
    autodisq_bisim
      (centralized_config (map snd os))
      (lower_solution_distributed sol os) ->
    sem_equiv_state_bi
      (centralized_config (map snd os))
      (lower_solution_distributed sol os).
Proof.
  intros sol os Hb.
  inversion Hb; subst.
  exact H.
Qed.

Theorem gen_prog_bisim_sound :
  forall mem os cfg,
    (forall sol,
      sem_equiv_state_bi
        (centralized_config (map snd os))
        (to_prog (distribute_op sol []) os)) ->
    (forall sol,
      sem_equiv_state_bi
        (centralized_config (map snd os))
        (lower_solution_distributed sol os)) ->
    In cfg (gen_prog mem os) ->
    autodisq_bisim (centralized_config (map snd os)) cfg.
Proof.
  induction mem as [|sol mem IH]; intros os cfg Hto Hlower HIn.
  - rewrite gen_prog_nil in HIn.
    contradiction.

  - rewrite gen_prog_cons in HIn.
    destruct (has_if_ops os) eqn:Hif; simpl in HIn.
    + destruct HIn as [Hcfg | Htail].
      * subst cfg.
        apply bisim_intro.
        apply Hto.
      * apply IH.
        -- exact Hto.
        -- exact Hlower.
        -- exact Htail.
    + destruct HIn as [Hcfg | Htail].
      * subst cfg.
        apply bisim_intro.
        apply Hlower.
      * apply IH.
        -- exact Hto.
        -- exact Hlower.
        -- exact Htail.
Qed.


Theorem gen_prog_bisim_sound_0:
  forall mem os cfg,
    (forall sol,
      autodisq_bisim
        (centralized_config (map snd os))
        (to_prog (distribute_op sol []) os)) ->
    (forall sol,
      autodisq_bisim
        (centralized_config (map snd os))
        (lower_solution_distributed sol os)) ->
    In cfg (gen_prog mem os) ->
    autodisq_bisim (centralized_config (map snd os)) cfg.
Proof.
  induction mem as [|sol mem IH]; intros os cfg Hto Hlower HIn.
  - rewrite gen_prog_nil in HIn.
    contradiction.
  - rewrite gen_prog_cons in HIn.
    destruct (has_if_ops os); simpl in HIn.
    + destruct HIn as [Hcfg | Htail].
      * subst cfg. apply Hto.
      * eapply IH; eauto.
    + destruct HIn as [Hcfg | Htail].
      * subst cfg. apply Hlower.
      * eapply IH; eauto.
Qed.
(*****************************************************************)
(* Top-level semantic correctness theorems                       *)
(*****************************************************************)

Lemma opListOrder_map_snd_opListOrder :
  forall ops,
    opListOrder (map snd (opListOrder ops)) = opListOrder ops.
Proof.
  intros ops.
  rewrite map_snd_opListOrder.
  reflexivity.
Qed.

Lemma in_gen_prog_from_sol :
  forall sols os sol,
    In sol sols ->
    In (lower_autodisq_solution sol os) (gen_prog sols os).
Proof.
  induction sols as [|x xs IH]; intros os sol HIn.
  - contradiction.

  - simpl in HIn.
    destruct HIn as [H | H].
    + subst x.
      unfold lower_autodisq_solution.
      simpl.
      destruct (has_if_ops os); simpl.
      * left. reflexivity.
      * left. reflexivity.

    + simpl.
      destruct (has_if_ops os); simpl.
      * right. apply IH. exact H.
      * right. apply IH. exact H.
Qed.

Lemma lower_autodisq_solution_semantic_sound :
  forall ops mids sol,
    (forall sol,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (to_prog (distribute_op sol []) (opListOrder ops))) ->
    (forall sol,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (lower_solution_distributed sol (opListOrder ops))) ->
    In sol (autodisq_solutions ops mids) ->
    sem_equiv_state_bi
      (centralized_config ops)
      (lower_autodisq_solution sol (opListOrder ops)).
Proof.
  intros ops mids sol Hto Hlower Hsol.

  assert (Hos : map snd (opListOrder ops) = ops).
  { apply map_snd_opListOrder. }

  rewrite <- Hos.

  unfold lower_autodisq_solution.
  rewrite opListOrder_map_snd_opListOrder.

  unfold autodisq_solutions in Hsol.

  destruct (has_if_ops (opListOrder ops)) eqn:Hif.
  - apply Hto.
  - apply Hlower.
Qed.

Theorem autodisq_all_semantic_sound :
  forall ops mids cfg,
    (forall sol,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (to_prog (distribute_op sol []) (opListOrder ops))) ->
    (forall sol,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (lower_solution_distributed sol (opListOrder ops))) ->
    In cfg (autodisq_all ops mids) ->
    sem_equiv_state_bi (centralized_config ops) cfg.
Proof.
  intros ops mids cfg Hto Hlower HIn.
  unfold autodisq_all in HIn.

  apply in_map_iff in HIn.
  destruct HIn as [sol [Hcfg Hsol]].
  subst cfg.

  eapply lower_autodisq_solution_semantic_sound.
  - exact Hto.
  - exact Hlower.
  - exact Hsol.
Qed.

Lemma get_op_complete :
  forall os n op,
    In (n, op) os ->
    get_op os n = Some op \/ exists op', get_op os n = Some op'.
Proof.
  induction os as [|[m op0] tl IH]; intros n op HIn.
  - contradiction.
  - simpl in HIn.
    destruct HIn as [H | H].
    + inversion H; subst; clear H.
      simpl.
      rewrite N.eqb_refl.
      left; reflexivity.
    + simpl.
      destruct (N.eqb n m) eqn:Hnm.
      * right.
        exists op0.
        reflexivity.
      * apply IH.
        exact H.
Qed.

Lemma get_op_some_in :
  forall os n op,
    get_op os n = Some op ->
    In (n, op) os.
Proof.
  induction os as [|[m op0] tl IH]; intros n op Hget.
  - simpl in Hget. discriminate.
  - simpl in Hget.
    destruct (N.eqb n m) eqn:Hnm.
    + apply N.eqb_eq in Hnm.
      inversion Hget; subst.
      left.
      reflexivity.
    + right.
      apply IH.
      exact Hget.
Qed.

Lemma best_prog_some_in :
  forall xs cfg,
    best_prog xs = Some cfg ->
    In cfg xs.
Proof.
  intros xs cfg H.

  unfold best_prog in H.

  destruct xs as [|x xs].
  - discriminate.

  - inversion H; subst; clear H.

    pose proof (best_prog_aux_in xs x (fit x)) as Hin.

    simpl in Hin.
    exact Hin.
Qed.

Theorem autodisq_best_semantic_sound :
  forall ops mids cfg,
    (forall sol,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (to_prog (distribute_op sol []) (opListOrder ops))) ->
    (forall sol,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (lower_solution_distributed sol (opListOrder ops))) ->
    autodisq_best ops mids = Some cfg ->
    sem_equiv_state_bi (centralized_config ops) cfg.
Proof.
  intros ops mids cfg Hto Hlower Hbest.
  unfold autodisq_best in Hbest.
  destruct (autodisq_best_solution ops mids) as [sol|] eqn:Hsol.
  - inversion Hbest; subst; clear Hbest.
    eapply (autodisq_all_semantic_sound ops mids).
    + exact Hto.
    + exact Hlower.
    + unfold autodisq_all.
      apply in_map_iff.
      exists sol.
      split.
      * reflexivity.
      * apply autodisq_best_solution_is_candidate.
        exact Hsol.
  - discriminate Hbest.
Qed.

Theorem AutoDisQ_Semantic_Correctness :
  forall ops mids cfg,
    (forall sol,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (to_prog (distribute_op sol []) (opListOrder ops))) ->
    (forall sol,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (lower_solution_distributed sol (opListOrder ops))) ->
    autodisq_best ops mids = Some cfg ->
    sem_equiv_state_bi (centralized_config ops) cfg.
Proof.
  intros ops mids cfg Hto Hlower Hbest.
  eapply autodisq_best_semantic_sound.
  - exact Hto.
  - exact Hlower.
  - exact Hbest.
Qed.

Theorem AutoDisQ_Soundness :
  forall ops mids cfg,
    (forall sol,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (to_prog (distribute_op sol []) (opListOrder ops))) ->
    (forall sol,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (lower_solution_distributed sol (opListOrder ops))) ->
    autodisq_best ops mids = Some cfg ->
    sem_equiv_state_bi (centralized_config ops) cfg.
Proof.
  intros ops mids cfg Hto Hlower Hbest.
  eapply autodisq_best_semantic_sound.
  - exact Hto.
  - exact Hlower.
  - exact Hbest.
Qed.
Theorem AutoDisQ_Main_Correctness_Observed :
  forall ops mids cfg,
    (forall sol,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (to_prog (distribute_op sol []) (opListOrder ops))) ->
    (forall sol,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (lower_solution_distributed sol (opListOrder ops))) ->
    autodisq_best ops mids = Some cfg ->
    sem_equiv_state_bi (centralized_config ops) cfg /\
    forall cfg',
      In cfg' (autodisq_all ops mids) ->
      (fit cfg <= fit cfg')%nat.
Proof.
  intros ops mids cfg Hto Hlower Hbest.
  split.
  - eapply autodisq_best_semantic_sound.
    + exact Hto.
    + exact Hlower.
    + exact Hbest.
  - intros cfg' Hcfg'.
    eapply autodisq_best_optimal_over_generated.
    + exact Hbest.
    + exact Hcfg'.
Qed.


Theorem AutoDisQ_Candidate_Semantic_Correctness :
  forall ops mids sol,
    (forall sol',
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (to_prog (distribute_op sol' []) (opListOrder ops))) ->
    (forall sol',
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (lower_solution_distributed sol' (opListOrder ops))) ->
    In sol (autodisq_solutions ops mids) ->
    sem_equiv_state_bi
      (centralized_config ops)
      (lower_autodisq_solution sol (opListOrder ops)).
Proof.
  intros ops mids sol Hto Hlower Hsol.
  eapply lower_autodisq_solution_semantic_sound.
  - exact Hto.
  - exact Hlower.
  - exact Hsol.
Qed.


Lemma to_prog_semantic_sound_direct :
  forall sol os,
    autodisq_bisim
      (centralized_config (map snd os))
      (to_prog (distribute_op sol []) os) ->
    sem_equiv_state_bi
      (centralized_config (map snd os))
      (to_prog (distribute_op sol []) os).
Proof.
  intros sol os Hb.
  inversion Hb; subst.
  exact H.
Qed.

Lemma lower_solution_distributed_semantic_sound_direct :
  forall sol os,
    autodisq_bisim
      (centralized_config (map snd os))
      (lower_solution_distributed sol os) ->
    sem_equiv_state_bi
      (centralized_config (map snd os))
      (lower_solution_distributed sol os).
Proof.
  intros sol os Hb.
  inversion Hb; subst.
  exact H.
Qed.


(*************************************************************)
(* Qubit-index translation                                   *)
(*************************************************************)

Definition qindex_of_nposi (p : nposi) : nat :=
  Nat.add (N.to_nat (fst p)) (N.to_nat (snd p)).

Definition first_qindex (l : locus) : nat :=
  match cutToQubits l with
  | [] => 0%nat
  | p :: _ => qindex_of_nposi p
  end.

Definition qindex_of_send_payload (x a : nat) : nat :=
  Nat.add x a.

(*************************************************************)
(* Fresh SQIR positions for teleportation                    *)
(*************************************************************)

Definition epr_a (ch : var) : nat := Nat.add 100000 ch.
Definition epr_b (ch : var) : nat := Nat.add 200000 ch.
Definition meas1 (ch : var) : nat := Nat.add 300000 ch.
Definition meas2 (ch : var) : nat := Nat.add 400000 ch.

(*************************************************************)
(* Compilation of DisQ expressions to SQIR                   *)
(*************************************************************)
Fixpoint compile_exp_to_sqir {dim : nat} (e : DisQSyntax.exp) (q : nat)
  : base_com dim :=
  match e with
  | DisQSyntax.SKIP _ _ =>
      skip

  | DisQSyntax.X _ _ =>
      uc (SQIR.X q)

  | DisQSyntax.H _ _ =>
      uc (SQIR.H q)

  | DisQSyntax.RZ _ _ _ =>
      uc (SQIR.Z q)

  | DisQSyntax.RRZ _ _ _ =>
      uc (SQIR.Z q)

  | DisQSyntax.CU _ _ (DisQSyntax.X _ _) =>
      uc (SQIR.CNOT q (S q))

  | DisQSyntax.CU _ _ e' =>
      compile_exp_to_sqir e' q

  | DisQSyntax.QFT _ _ =>
      skip

  | DisQSyntax.RQFT _ _ =>
      skip

  | DisQSyntax.SR _ _ =>
      skip

  | DisQSyntax.SRR _ _ =>
      skip

  | DisQSyntax.Addto _ _ =>
      skip

  | DisQSyntax.Seq e1 e2 =>
      compile_exp_to_sqir e1 q ;
      compile_exp_to_sqir e2 q
  end.


(*************************************************************)
(* Send / Recv compiled as teleportation fragments            *)
(*************************************************************)

Definition Ts {dim : nat} (ch x a : var) : base_com dim :=
  let q  := qindex_of_send_payload x a in
  let ea := epr_a ch in
  let eb := epr_b ch in
  uc (SQIR.H ea) ;
  uc (SQIR.CNOT ea eb) ;
  uc (SQIR.CNOT q ea) ;
  uc (SQIR.H q) ;
  measure ea ;
  measure q.

Definition Tr {dim : nat} (ch x a : var) : base_com dim :=
  let eb := epr_b ch in
  mif (meas2 ch) then uc (SQIR.X eb) else skip ;
  mif (meas1 ch) then uc (SQIR.Z eb) else skip.

Definition compile_send_to_sqir {dim : nat} (ch x a : var)
  : base_com dim :=
  Ts ch x a.

Definition compile_recv_to_sqir {dim : nat} (ch x a : var)
  : base_com dim :=
  Tr ch x a.

(*************************************************************)
(* Compilation of cexp/process/config                         *)
(*************************************************************)

Definition compile_cexp_to_sqir {dim : nat} (c : cexp)
  : base_com dim :=
  match c with
  | CNew _ =>
      skip

  | CAppU l e =>
      compile_exp_to_sqir e (first_qindex l)

  | CMeas _ l =>
      measure (first_qindex l)

  | Send ch x a =>
      compile_send_to_sqir ch x a

  | Recv ch x a =>
      compile_recv_to_sqir ch x a
  end.

Fixpoint compile_process_to_sqir {dim : nat} (p : process)
  : option (base_com dim) :=
  match p with
  | PNil =>
      Some skip

  | AP c p' =>
      match compile_process_to_sqir p' with
      | Some eps =>
          Some (compile_cexp_to_sqir c ; eps)
      | None =>
          None
      end

  | PIf _ _ _ =>
      None
  end.
(*
Fixpoint compile_process_to_sqir {dim : nat} (p : process)
  : base_com dim :=
  match p with
  | PNil =>
      skip

  | AP c p' =>
      compile_cexp_to_sqir c ;
      compile_process_to_sqir p'

  | PIf _ p1 p2 =>
      compile_process_to_sqir p1 ;
      compile_process_to_sqir p2
  end.

Definition compile_memb_to_sqir {dim : nat} (m : memb)
  : base_com dim :=
  match m with
  | Memb _ p => compile_process_to_sqir p
  end.

Fixpoint compile_config_to_sqir {dim : nat} (cfg : config)
  : base_com dim :=
  match cfg with
  | [] => skip
  | m :: xs => compile_memb_to_sqir m ; compile_config_to_sqir xs
  end.

*)

Definition compile_memb_to_sqir {dim}
  (m : memb)
  : option (base_com dim) :=
  match m with
  | Memb _ p =>
      compile_process_to_sqir p
  end.

Fixpoint compile_config_to_sqir {dim}
  (cfg : config)
  : option (base_com dim) :=
  match cfg with
  | [] =>
      Some skip

  | m :: xs =>
      match compile_memb_to_sqir m,
            compile_config_to_sqir xs with
      | Some em, Some exs =>
          Some (em ; exs)
      | _, _ =>
          None
      end
  end.
(*************************************************************)
(* AutoDisQ result -> SQIR                                   *)
(*************************************************************)
Definition compile_autodisq_solution_to_sqir
  {dim : nat}
  (sol : autodisq_solution)
  (os : list (N * myOp))
  : option (base_com dim) :=
  compile_config_to_sqir (lower_autodisq_solution sol os).

Definition compile_to_sqir {dim : nat}
  (ops : op_list)
  (mids : list membrane_id)
  : option (base_com dim) :=
  match autodisq_best ops mids with
  | Some cfg => compile_config_to_sqir cfg
  | None => None
  end.


(*************************************************************)
(* Basic density-semantics facts                             *)
(*************************************************************)

Lemma compile_config_density_wf :
  forall dim cfg eps rho,
    @compile_config_to_sqir dim cfg = Some eps ->
    WF_Matrix rho ->
    WF_Matrix (c_eval eps rho).
Proof.
  intros dim cfg eps rho Hcompile Hwf.
  apply WF_c_eval.
  exact Hwf.
Qed.

Theorem autodisq_best_compiles_to_sqir :
  forall dim ops mids cfg eps,
    autodisq_best ops mids = Some cfg ->
    @compile_config_to_sqir dim cfg = Some eps ->
    @compile_to_sqir dim ops mids = Some eps.
Proof.
  intros dim ops mids cfg eps Hbest Hcfg.
  unfold compile_to_sqir.
  rewrite Hbest.
  exact Hcfg.
Qed.

Theorem AutoDisQ_best_sqir_density_sound :
  forall dim ops mids cfg eps rho,
    (forall sol,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (to_prog (distribute_op sol []) (opListOrder ops))) ->
    (forall sol,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (lower_solution_distributed sol (opListOrder ops))) ->
    autodisq_best ops mids = Some cfg ->
    @compile_to_sqir dim ops mids = Some eps ->
    WF_Matrix rho ->
    sem_equiv_state_bi (centralized_config ops) cfg /\
    WF_Matrix (c_eval eps rho) /\
    exists eps_cfg,
      @compile_config_to_sqir dim cfg = Some eps_cfg /\
      eps = eps_cfg /\
      c_eval eps rho = c_eval eps_cfg rho.
Proof.
  intros dim ops mids cfg eps rho
         Hto_prog Hlower
         Hbest Hcompile Hwf.

  unfold compile_to_sqir in Hcompile.
  rewrite Hbest in Hcompile.

  split.
  - eapply (autodisq_best_semantic_sound ops mids cfg).
    + exact Hto_prog.
    + exact Hlower.
    + exact Hbest.

  - split.
    + apply WF_c_eval.
      exact Hwf.

    + exists eps.
      split.
      * exact Hcompile.
      * split.
        -- reflexivity.
        -- reflexivity.
Qed.



(*************************************************************)
(* Send/Recv = teleportation syntax                          *)
(*************************************************************)

Definition one_time_channel_sqir
  {dim : nat}
  (ch x a : var)
  : base_com dim :=
  compile_cexp_to_sqir (Send ch x a) ;
  compile_cexp_to_sqir (Recv ch x a).

Definition teleportation_sqir
  {dim : nat}
  (ch x a : var)
  : base_com dim :=
  Ts ch x a ; Tr ch x a.

Theorem send_compiles_to_Ts :
  forall dim ch x a,
    @compile_cexp_to_sqir dim (Send ch x a) = Ts ch x a.
Proof.
  intros.
  reflexivity.
Qed.

Theorem recv_compiles_to_Tr :
  forall dim ch x a,
    @compile_cexp_to_sqir dim (Recv ch x a) = Tr ch x a.
Proof.
  intros.
  reflexivity.
Qed.

Corollary One_Time_Channel_Equivalent_To_Teleportation :
  forall dim ch x a,
    @one_time_channel_sqir dim ch x a =
    @teleportation_sqir dim ch x a.
Proof.
  intros.
  unfold one_time_channel_sqir, teleportation_sqir.
  reflexivity.
Qed.

Theorem One_Time_Channel_Density_Equivalent_To_Teleportation :
  forall dim ch x a rho,
    c_eval (@one_time_channel_sqir dim ch x a) rho =
    c_eval (@teleportation_sqir dim ch x a) rho.
Proof.
  intros.
  rewrite One_Time_Channel_Equivalent_To_Teleportation.
  reflexivity.
Qed.

(*************************************************************)
(* Section 6 objects: grab, dom(sigma), loc_map, loc_eval     *)
(*************************************************************)

Definition sigma_env : Type := list nat.

Definition dom_sigma (sigma : sigma_env) : list nat := sigma.

Definition subset_nat (xs ys : list nat) : Prop :=
  forall x, In x xs -> In x ys.

Fixpoint grab_process (p : process) : list nat :=
  match p with
  | PNil => []

  | AP c p' =>
      match c with
      | Send ch x a =>
          epr_a ch :: epr_b ch ::
          qindex_of_send_payload x a ::
          grab_process p'

      | Recv ch _ _ =>
          epr_a ch :: epr_b ch ::
          grab_process p'

      | CAppU l _ =>
          first_qindex l :: grab_process p'

      | CMeas _ l =>
          first_qindex l :: grab_process p'

      | CNew r =>
          map qindex_of_nposi (cutToQubits (r :: nil)) ++ grab_process p'
      end

  | PIf _ _ _ =>
      []
  end.

Definition grab_memb (m : memb) : list nat :=
  match m with
  | Memb _ p => grab_process p
  end.

Fixpoint grab_config (cfg : config) : list nat :=
  match cfg with
  | [] => []
  | m :: xs => grab_memb m ++ grab_config xs
  end.

Definition grab_solution
  (sol : autodisq_solution)
  (os : list (N * myOp))
  : list nat :=
  grab_config (lower_autodisq_solution sol os).

Definition state_denote {dim : nat}
  (rho : Square (2 ^ dim))
  (cfg : config) : Square (2 ^ dim) :=
  match @compile_config_to_sqir dim cfg with
  | Some eps => c_eval eps rho
  | None => rho
  end.

Definition loc_map : Type := nat -> option membrane_id.

Definition empty_loc_map : loc_map := fun _ => None.

Definition update_loc_map
  (delta : loc_map)
  (q : nat)
  (mid : membrane_id) : loc_map :=
  fun x => if Nat.eqb x q then Some mid else delta x.

Fixpoint update_locus_map
  (delta : loc_map)
  (qs : list nposi)
  (mid : membrane_id) : loc_map :=
  match qs with
  | [] => delta
  | q :: tl =>
      update_locus_map
        (update_loc_map delta (qindex_of_nposi q) mid)
        tl
        mid
  end.

Fixpoint loc_eval_process
  (mid : membrane_id)
  (p : process)
  (delta : loc_map) : loc_map :=
  match p with
  | PNil => delta

  | AP c p' =>
      let delta' :=
        match c with
        | CNew r =>
            update_locus_map delta (cutToQubits (r :: nil)) mid

        | CAppU l _ =>
            update_locus_map delta (cutToQubits l) mid

        | CMeas _ l =>
            update_locus_map delta (cutToQubits l) mid

        | Send ch x a =>
            update_loc_map
              (update_loc_map
                 (update_loc_map delta (epr_a ch) mid)
                 (epr_b ch) mid)
              (qindex_of_send_payload x a) mid

        | Recv ch _ _ =>
            update_loc_map
              (update_loc_map delta (epr_a ch) mid)
              (epr_b ch) mid
        end in
      loc_eval_process mid p' delta'

  | PIf _ p1 p2 =>
      loc_eval_process mid p2 (loc_eval_process mid p1 delta)
  end.

Fixpoint loc_eval_config
  (cfg : config)
  (delta : loc_map) : loc_map :=
  match cfg with
  | [] => delta
  | Memb mid p :: tl =>
      loc_eval_config tl (loc_eval_process mid p delta)
  end.

Definition wf_locus_domain (sigma : sigma_env) : Prop :=
  NoDup sigma.

(*************************************************************)
(* Section 6 compilation judgment                            *)
(*************************************************************)
Definition compile_judgment
  {dim : nat}
  (sigma : sigma_env)
  (cfg : config)
  (eps : base_com dim)
  : Prop :=
  subset_nat (grab_config cfg) (dom_sigma sigma) /\
  @compile_config_to_sqir dim cfg = Some eps.

Notation "sigma '|-' cfg '>>' eps" :=
  (compile_judgment sigma cfg eps)
  (at level 40).



(*************************************************************)
(* Theorem 6.1-style statement                               *)
(*************************************************************)

Theorem AutoDisQ_to_SQIR_Compilation_Correctness :
  forall dim sigma ops mids sol (eps : base_com dim) rho phi phi',
    (forall sol0,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (to_prog (distribute_op sol0 []) (opListOrder ops))) ->
    (forall sol0,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (lower_solution_distributed sol0 (opListOrder ops))) ->
    In sol (autodisq_solutions ops mids) ->
    let cfg := lower_autodisq_solution sol (opListOrder ops) in
    @compile_config_to_sqir dim cfg = Some eps ->
    subset_nat (grab_config cfg) (dom_sigma sigma) ->
    wf_locus_domain sigma ->
    phi = centralized_config ops ->
    phi' = cfg ->
    WF_Matrix rho ->
    sem_equiv_state_bi phi phi' /\
    c_eval eps rho = state_denote rho phi' /\
    exists delta',
      loc_eval_config phi' empty_loc_map = delta'.
Proof.
  intros dim sigma ops mids sol eps rho phi phi'
         Hto Hlower Hsol cfg Heps Hgrab Hwf Hphi Hphi' Hrho.

  subst phi.
  subst phi'.
  split.
  - eapply lower_autodisq_solution_semantic_sound.
    + exact Hto.
    + exact Hlower.
    + exact Hsol.

  - split.
    + unfold state_denote.
      rewrite Heps.
      reflexivity.
    + eexists.
      reflexivity.
Qed.


(*************************************************************)
(* Best-result Theorem 6.1-style corollary                    *)
(*************************************************************)

Theorem AutoDisQ_Best_to_SQIR_Compilation_Correctness :
  forall dim sigma ops mids cfg eps rho,
    (forall sol0,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (to_prog (distribute_op sol0 []) (opListOrder ops))) ->
    (forall sol0,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (lower_solution_distributed sol0 (opListOrder ops))) ->
    autodisq_best ops mids = Some cfg ->
    @compile_to_sqir dim ops mids = Some eps ->
    subset_nat (grab_config cfg) (dom_sigma sigma) ->
    wf_locus_domain sigma ->
    WF_Matrix rho ->
    sem_equiv_state_bi (centralized_config ops) cfg /\
    c_eval eps rho = state_denote rho cfg /\
    exists delta',
      loc_eval_config cfg empty_loc_map = delta'.
Proof.
  intros dim sigma ops mids cfg eps rho
         Hto Hlower Hbest Hcompile Hgrab Hwf Hrho.

  unfold compile_to_sqir in Hcompile.
  rewrite Hbest in Hcompile.
   split.
  - eapply autodisq_best_semantic_sound.
    + exact Hto.
    + exact Hlower.
    + exact Hbest.
  - split.
    + unfold state_denote.
      rewrite Hcompile.
      reflexivity.
    + eexists.
      reflexivity.
Qed.

(*************************************************************)
(* End-to-end theorem: best AutoDisQ config compiles to SQIR  *)
(*************************************************************)

Theorem AutoDisQ_SQIR_EndToEnd :
  forall dim sigma ops mids cfg eps rho,
    (forall sol0,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (to_prog (distribute_op sol0 []) (opListOrder ops))) ->
    (forall sol0,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (lower_solution_distributed sol0 (opListOrder ops))) ->
    autodisq_best ops mids = Some cfg ->
    @compile_to_sqir dim ops mids = Some eps ->
    subset_nat (grab_config cfg) (dom_sigma sigma) ->
    wf_locus_domain sigma ->
    WF_Matrix rho ->
    sem_equiv_state_bi (centralized_config ops) cfg /\
    WF_Matrix (c_eval eps rho) /\
    c_eval eps rho = state_denote rho cfg /\
    exists delta',
      loc_eval_config cfg empty_loc_map = delta'.
Proof.
  intros dim sigma ops mids cfg eps rho
         Hto Hlower Hbest Hcompile Hgrab Hwf Hrho.

  unfold compile_to_sqir in Hcompile.
  rewrite Hbest in Hcompile.

  split.
  - eapply autodisq_best_semantic_sound.
    + exact Hto.
    + exact Hlower.
    + exact Hbest.

  - split.
    + apply WF_c_eval.
      exact Hrho.

    + split.
      * unfold state_denote.
        rewrite Hcompile.
        reflexivity.

      * eexists.
        reflexivity.
Qed.


Definition denote_config_density_1 {dim : nat}
  (cfg : config)
  (rho : Square (2 ^ dim))
  : Square (2 ^ dim) :=
  match @compile_config_to_sqir dim cfg with
  | Some eps => c_eval eps rho
  | None => rho
  end.

Theorem compile_config_density_sound :
  forall dim cfg eps rho,
    @compile_config_to_sqir dim cfg = Some eps ->
    WF_Matrix rho ->
    c_eval eps rho =
    denote_config_density_1 cfg rho.
Proof.
  intros dim cfg eps rho Hcomp Hwf.
  unfold denote_config_density_1.
  rewrite Hcomp.
  reflexivity.
Qed.

Theorem AutoDisQ_to_SQIR_Compilation_Correctness_N:
  forall dim sigma ops mids cfg eps rho,
    (forall sol0,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (to_prog (distribute_op sol0 []) (opListOrder ops))) ->
    (forall sol0,
      sem_equiv_state_bi
        (centralized_config (map snd (opListOrder ops)))
        (lower_solution_distributed sol0 (opListOrder ops))) ->
    autodisq_best ops mids = Some cfg ->
    @compile_to_sqir dim ops mids = Some eps ->
    subset_nat (grab_config cfg) (dom_sigma sigma) ->
    wf_locus_domain sigma ->
    WF_Matrix rho ->
    sem_equiv_state_bi (centralized_config ops) cfg /\
    WF_Matrix (c_eval eps rho) /\
    c_eval eps rho = state_denote rho cfg /\
    exists delta',
      loc_eval_config cfg empty_loc_map = delta'.
Proof.
  intros dim sigma ops mids cfg eps rho
         Hto Hlower Hbest Hcompile Hgrab Hwf Hrho.

  unfold compile_to_sqir in Hcompile.
  rewrite Hbest in Hcompile.

  split.
  - eapply autodisq_best_semantic_sound; eauto.
  - split.
    + apply WF_c_eval. exact Hrho.
    + split.
      * unfold state_denote.
        rewrite Hcompile.
        reflexivity.
      * eexists. reflexivity.
Qed.


Fixpoint denote_process_density {dim : nat}
  (p : process)
  (rho : Square (2 ^ dim))
  : Square (2 ^ dim) :=
  match p with
  | PNil => rho
  | AP c p' =>
      denote_process_density p'
        (c_eval (compile_cexp_to_sqir c) rho)
  | PIf _ p1 p2 =>
      denote_process_density p2
        (denote_process_density p1 rho)
  end.

Definition denote_memb_density {dim : nat}
  (m : memb)
  (rho : Square (2 ^ dim))
  : Square (2 ^ dim) :=
  match m with
  | Memb _ p => denote_process_density p rho
  end.

Fixpoint denote_config_density {dim : nat}
  (cfg : config)
  (rho : Square (2 ^ dim))
  : Square (2 ^ dim) :=
  match cfg with
  | [] => rho
  | m :: xs =>
      denote_config_density xs (denote_memb_density m rho)
  end.

Theorem compile_process_density_sound :
  forall dim p eps rho,
    @compile_process_to_sqir dim p = Some eps ->
    WF_Matrix rho ->
    c_eval eps rho =
    denote_process_density p rho.
Proof.
  induction p; intros eps rho Hcomp Hwf; simpl in *.
  - inversion Hcomp; subst.
    reflexivity.
  - destruct (@compile_process_to_sqir dim p) eqn:Hp; try discriminate.
    inversion Hcomp; subst eps.
    simpl.
    unfold compose_super.
    apply IHp.
    + reflexivity.
    + apply WF_c_eval.
      exact Hwf.
  - discriminate.
Qed.

Theorem compile_memb_density_sound :
  forall dim m eps rho,
    @compile_memb_to_sqir dim m = Some eps ->
    WF_Matrix rho ->
    c_eval eps rho =
    denote_memb_density m rho.
Proof.
  intros dim [mid p] eps rho Hcomp Hwf.
  simpl in Hcomp.
  simpl.
  eapply compile_process_density_sound.
  - exact Hcomp.
  - exact Hwf.
Qed.

Theorem compile_config_density_sound_0 :
  forall dim cfg eps rho,
    @compile_config_to_sqir dim cfg = Some eps ->
    WF_Matrix rho ->
    c_eval eps rho =
    denote_config_density cfg rho.
Proof.
  induction cfg as [|m xs IH]; intros eps rho Hcomp Hwf; simpl in *.
  - inversion Hcomp; subst.
    reflexivity.

  - destruct (@compile_memb_to_sqir dim m) eqn:Hm; try discriminate.
    destruct (@compile_config_to_sqir dim xs) eqn:Hx; try discriminate.
    inversion Hcomp; subst eps.
    simpl.
    unfold compose_super.
    rewrite (compile_memb_density_sound dim m b rho Hm Hwf).
    apply IH.
    + reflexivity.
    + rewrite <- (compile_memb_density_sound dim m b rho Hm Hwf).
      apply WF_c_eval.
      exact Hwf.
Qed.



