


(* AUTO_Correctness.v *)

From Coq Require Import List Arith Bool Nat NArith Lia.
Import ListNotations.

Require Import DisQ.BasicUtility.
Require Import DisQ.DisQSyntax.
Require Import DisQ.AUTO.

Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope bool_scope.

(*************************************************************)
(* Dependency relation                                       *)
(*************************************************************)

Definition dependent_ops (ops : op_list) (i j : N) : Prop :=
  gen_hb (opListOrder ops) i j = true.

Theorem hb_sound :
  forall ops i j,
    gen_hb (opListOrder ops) i j = true ->
    dependent_ops ops i j.
Proof.
  intros ops i j H.
  unfold dependent_ops.
  exact H.
Qed.

Theorem hb_complete :
  forall ops i j,
    dependent_ops ops i j ->
    gen_hb (opListOrder ops) i j = true.
Proof.
  intros ops i j H.
  unfold dependent_ops in H.
  exact H.
Qed.

(*************************************************************)
(* Solution-level predicates                                 *)
(*************************************************************)

Definition solution_is_candidate
  (ops : op_list)
  (mids : list membrane_id)
  (sol : autodisq_solution) : Prop :=
  In sol (autodisq_solutions ops mids).

Definition generated_solution
  (ops : op_list)
  (mids : list membrane_id)
  (sol : autodisq_solution) : Prop :=
  solution_is_candidate ops mids sol.

Definition solution_lowers_to
  (ops : op_list)
  (sol : autodisq_solution)
  (cfg : config) : Prop :=
  lower_autodisq_solution sol (opListOrder ops) = cfg.

Definition lowered_solution
  (ops : op_list)
  (sol : autodisq_solution)
  (cfg : config) : Prop :=
  solution_lowers_to ops sol cfg.

Definition best_generated_solution
  (ops : op_list)
  (mids : list membrane_id)
  (sol : autodisq_solution) : Prop :=
  autodisq_best_solution ops mids = Some sol.

(*************************************************************)
(* Indices extracted from solution                           *)
(*************************************************************)

Fixpoint indices_of_solution
  (sol : autodisq_solution) : list N :=
  match sol with
  | [] => []
  | ((OpNum n, _), _) :: xs => n :: indices_of_solution xs
  | ((OpExp _, _), _) :: xs => indices_of_solution xs
  end.

Fixpoint appears_before
  (i j : N)
  (xs : list N) : bool :=
  match xs with
  | [] => false
  | x :: tl =>
      if N.eqb x i
      then existsb (N.eqb j) tl
      else appears_before i j tl
  end.

Definition preserves_hb_order_solution
  (ops : op_list)
  (sol : autodisq_solution) : Prop :=
  forall i j,
    dependent_ops ops i j ->
    appears_before i j (indices_of_solution sol) = true.

Definition valid_solution
  (ops : op_list)
  (mids : list membrane_id)
  (sol : autodisq_solution) : Prop :=
  solution_is_candidate ops mids sol.

Theorem every_generated_solution_is_valid :
  forall ops mids sol,
    In sol (autodisq_solutions ops mids) ->
    valid_solution ops mids sol.
Proof.
  intros ops mids sol H.
  unfold valid_solution, solution_is_candidate.
  exact H.
Qed.

(*************************************************************)
(* Best solution is a generated solution                     *)
(*************************************************************)

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

Theorem autodisq_best_solution_is_candidate :
  forall ops mids sol,
    autodisq_best_solution ops mids = Some sol ->
    solution_is_candidate ops mids sol.
Proof.
  intros ops mids sol H.
  unfold autodisq_best_solution in H.
  unfold solution_is_candidate.
  destruct (autodisq_solutions ops mids) as [| x xs] eqn:Hs.
  - discriminate.
  - inversion H; subst; clear H.
    simpl.
    apply best_solution_aux_in.
Qed.

(*************************************************************)
(* Best solution optimality                                  *)
(*************************************************************)

Lemma best_solution_aux_optimal :
  forall ops xs best bestv,
    bestv = solution_fit ops best ->
    forall y,
      In y (best :: xs) ->
      (solution_fit ops (best_solution_aux ops best bestv xs)
       <= solution_fit ops y)%nat.
Proof.
  intros ops xs.
  induction xs as [| x xs IH]; intros best bestv Hbestv y Hy.
  - simpl in Hy.
    destruct Hy as [Hy | Hy].
    + subst. simpl. lia.
    + contradiction.
  - simpl.
    destruct (Nat.ltb (solution_fit ops x) bestv) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      destruct Hy as [Hy | Hy].
      * subst y.
        specialize (IH x (solution_fit ops x) eq_refl x).
        assert (Hin : In x (x :: xs)) by (left; reflexivity).
        specialize (IH Hin).
        rewrite Hbestv in Hlt.
        lia.
      * eapply IH.
        -- reflexivity.
        -- exact Hy.
    + apply Nat.ltb_ge in Hlt.
      destruct Hy as [Hy | Hy].
      * subst y.
        eapply IH.
        -- exact Hbestv.
        -- left. reflexivity.
      * destruct Hy as [Hy | Hy].
        -- subst y.
           specialize (IH best bestv Hbestv best).
           assert (Hin : In best (best :: xs)) by (left; reflexivity).
           specialize (IH Hin).
           rewrite Hbestv in Hlt.
           lia.
        -- eapply IH.
           ++ exact Hbestv.
           ++ right. exact Hy.
Qed.

Theorem autodisq_best_solution_optimal :
  forall ops mids sol,
    autodisq_best_solution ops mids = Some sol ->
    forall sol',
      In sol' (autodisq_solutions ops mids) ->
      (solution_fit ops sol <= solution_fit ops sol')%nat.
Proof.
  intros ops mids sol Hbest sol' Hin.
  unfold autodisq_best_solution in Hbest.
  destruct (autodisq_solutions ops mids) as [| x xs] eqn:Hs.
  - simpl in Hin. contradiction.
  - inversion Hbest; subst; clear Hbest.
    apply best_solution_aux_optimal with
      (best := x)
      (bestv := solution_fit ops x).
    + reflexivity.
    + rewrite <- Hs.
    rewrite Hs.
assumption.

Qed.

(*************************************************************)
(* Lowering bridge                                           *)
(*************************************************************)

Theorem autodisq_best_lowers_selected_solution :
  forall ops mids sol cfg,
    autodisq_best_solution ops mids = Some sol ->
    cfg = lower_autodisq_solution sol (opListOrder ops) ->
    autodisq_best ops mids = Some cfg.
Proof.
  intros ops mids sol cfg Hbest Hcfg.
  unfold autodisq_best.
  rewrite Hbest.
  subst cfg.
  reflexivity.
Qed.

Theorem selected_solution_lowers_to_best_config :
  forall ops mids sol cfg,
    autodisq_best_solution ops mids = Some sol ->
    autodisq_best ops mids = Some cfg ->
    solution_lowers_to ops sol cfg.
Proof.
  intros ops mids sol cfg Hsol Hcfg.
  unfold autodisq_best in Hcfg.
  rewrite Hsol in Hcfg.
  inversion Hcfg; subst.
  unfold solution_lowers_to.
  reflexivity.
Qed.

Theorem autodisq_correct_solution_level :
  forall ops mids cfg,
    autodisq_best ops mids = Some cfg ->
    exists sol,
      autodisq_best_solution ops mids = Some sol /\
      solution_is_candidate ops mids sol /\
      solution_lowers_to ops sol cfg.
Proof.
  intros ops mids cfg Hbest.
  unfold autodisq_best in Hbest.
  destruct (autodisq_best_solution ops mids) as [a|] eqn:Hsol.
  - inversion Hbest; subst; clear Hbest.
    exists a.
    split.
    + reflexivity.
    + split.
      * apply autodisq_best_solution_is_candidate.
        exact Hsol.
      * unfold solution_lowers_to.
        reflexivity.
  - inversion Hbest.
Qed.

(*************************************************************)
(* Optimality over generated configs                         *)
(*************************************************************)
Definition optimal_generated_config ops mids cfg :=
  exists sol,
    autodisq_best_solution ops mids = Some sol /\
    solution_lowers_to ops sol cfg /\
    forall sol',
      solution_is_candidate ops mids sol' ->
      fit cfg <= fit (lower_autodisq_solution sol' (opListOrder ops)).

Lemma solution_fit_lowering :
  forall ops sol,
    solution_fit ops sol =
    fit (lower_autodisq_solution sol (opListOrder ops)).
Proof.
  intros ops sol.
  unfold solution_fit.
  reflexivity.
Qed.

Lemma best_solution_minimal :
  forall ops mids sol sol',
    autodisq_best_solution ops mids = Some sol ->
    solution_is_candidate ops mids sol' ->
    fit (lower_autodisq_solution sol (opListOrder ops))
    <= fit (lower_autodisq_solution sol' (opListOrder ops)).
Proof.
  intros ops mids sol sol' Hbest Hcand.
  unfold solution_is_candidate in Hcand.
  rewrite <- solution_fit_lowering.
  rewrite <- solution_fit_lowering.
  eapply autodisq_best_solution_optimal.
  - exact Hbest.
  - exact Hcand.
Qed.


Theorem autodisq_best_optimal_over_generated :
  forall ops mids cfg,
    autodisq_best ops mids = Some cfg ->
    optimal_generated_config ops mids cfg.
Proof.
  intros ops mids cfg Hbest.
  unfold autodisq_best in Hbest.
  unfold optimal_generated_config.

  destruct (autodisq_best_solution ops mids) as [sol|] eqn:Hbestsol.
  - inversion Hbest; subst; clear Hbest.
    exists sol.
    split.
    + reflexivity.
    + split.
      * unfold lowered_solution.
        unfold solution_lowers_to.
        reflexivity.
      * intros sol' Hcand'.
        (* This is the missing optimality part. *)
        eapply best_solution_minimal.
        -- exact Hbestsol.
        -- exact Hcand'.
  - discriminate Hbest.
Qed.


(*************************************************************)
(*                                                           *)
(*************************************************************)
Theorem AutoDisQ_Main_Correctness :
  forall ops mids cfg,
    autodisq_best ops mids = Some cfg ->
    exists sol,
      generated_solution ops mids sol /\
      best_generated_solution ops mids sol /\
      lowered_solution ops sol cfg /\
      optimal_generated_config ops mids cfg.
Proof.
  intros ops mids cfg Hbest.

  destruct (autodisq_correct_solution_level ops mids cfg Hbest)
    as [sol [Hbestsol [Hcand Hlow]]].

  exists sol.
  repeat split.
  - unfold generated_solution.
    exact Hcand.
  - unfold best_generated_solution.
    exact Hbestsol.
  - unfold lowered_solution.
    exact Hlow.
  - apply autodisq_best_optimal_over_generated.
    exact Hbest.
Qed.





















































































































