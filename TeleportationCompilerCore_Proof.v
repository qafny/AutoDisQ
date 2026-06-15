
(* TeleportationCompilerCore_Proof.v *)
Require Import DisQ.BasicUtility DisQ.DisQSyntax DisQ.AUTO DisQ.TeleportationCompilerCore.
From Coq Require Import List Arith Bool Nat NArith.BinNat.
Import ListNotations.


Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope bool_scope.
Local Open Scope string_scope.






Lemma exec_dist_ir_move_unfold :
  forall loc src dst ds tr,
    lower_move loc src dst (ds_lstate ds) nil = Some tr ->
    denote_dist_ir src (IR_Move loc src dst) ds =
    match lookup_proto_mem src (mr_bufs tr) with
    | None =>
        Some
          {| ds_lstate := mr_state tr;
             ds_bits := ds_bits ds;
             ds_chans := ds_chans ds;
             ds_qstate := ds_qstate ds |}
    | Some ops =>
        match exec_dist_proto_list src ops
          {| rt_lstate := mr_state tr;
             rt_bits := ds_bits ds;
             rt_chans := ds_chans ds;
             rt_qstate := ds_qstate ds;
             rt_trace := nil |}
        with
        | None => None
        | Some rt' => Some (runtime_to_den_state rt')
        end
    end.
Proof.
  intros loc src dst ds tr Hmove.
  unfold denote_dist_ir, exec_dist_ir.
  simpl.
  unfold lower_ir_to_proto_op, lower_ir_list_to_proto.
  simpl.
  rewrite Hmove.
  simpl.
  destruct (lookup_proto_mem src (mr_bufs tr)) eqn:Hlk.
  - reflexivity.
  - reflexivity.
Qed.

Theorem lower_move_denotation_correct_pointwise :
  forall loc src dst ds tr,
    lower_move loc src dst (ds_lstate ds) nil = Some tr ->
    denote_dist_ir src (IR_Move loc src dst) ds =
    match lookup_proto_mem src (mr_bufs tr) with
    | None =>
        Some
          {| ds_lstate := mr_state tr;
             ds_bits := ds_bits ds;
             ds_chans := ds_chans ds;
             ds_qstate := ds_qstate ds |}
    | Some ops =>
        match exec_dist_proto_list src ops
          {| rt_lstate := mr_state tr;
             rt_bits := ds_bits ds;
             rt_chans := ds_chans ds;
             rt_qstate := ds_qstate ds;
             rt_trace := nil |}
        with
        | Some rt' => Some (runtime_to_den_state rt')
        | None => None
        end
    end.
Proof.
  intros loc src dst ds tr Hmove.
  unfold denote_dist_ir, exec_dist_ir.
  simpl.
  unfold lower_ir_to_proto_op, lower_ir_list_to_proto.
  simpl.
  rewrite Hmove.
  simpl.
  destruct (lookup_proto_mem src (mr_bufs tr)) eqn:Hlk.
  - reflexivity.
  - reflexivity.
Qed.

Theorem lower_move_denotation_correct :
  forall loc src dst,
    cpmap_equiv
      (fun ds =>
         match lower_move loc src dst (ds_lstate ds) nil with
         | Some tr =>
             match lookup_proto_mem src (mr_bufs tr) with
             | None =>
                 Some
                   {| ds_lstate := mr_state tr;
                      ds_bits := ds_bits ds;
                      ds_chans := ds_chans ds;
                      ds_qstate := ds_qstate ds |}
             | Some ops =>
                 match exec_dist_proto_list src ops
                   {| rt_lstate := mr_state tr;
                      rt_bits := ds_bits ds;
                      rt_chans := ds_chans ds;
                      rt_qstate := ds_qstate ds;
                      rt_trace := nil |}
                 with
                 | Some rt' => Some (runtime_to_den_state rt')
                 | None => None
                 end
             end
         | None => None
         end)
      (denote_dist_ir src (IR_Move loc src dst)).
Proof.
  intros loc src dst.
  unfold cpmap_equiv.
  intros ds ds'.
  split; intro H.
  - destruct (lower_move loc src dst (ds_lstate ds) nil) as [tr|] eqn:Hmove.
    + rewrite (lower_move_denotation_correct_pointwise loc src dst ds tr Hmove).
      exact H.
    + simpl in H. discriminate.
 - destruct (lower_move loc src dst (ds_lstate ds) nil) as [tr|] eqn:Hmove.
  + rewrite <- (lower_move_denotation_correct_pointwise loc src dst ds tr Hmove).
    exact H.
  + unfold denote_dist_ir, exec_dist_ir in H.
    simpl in H.
    unfold lower_ir_to_proto_op, lower_ir_list_to_proto in H.
    simpl in H.
    rewrite Hmove in H.
    simpl in H.
    discriminate.
Qed.

Theorem lower_nonlocal_cnot_denotation_correct_pointwise :
  forall ctrl_loc tgt_loc ctrl_mem tgt_mem ds gr,
    lower_nonlocal_cnot ctrl_loc tgt_loc ctrl_mem tgt_mem (ds_lstate ds) nil = Some gr ->
    denote_dist_ir ctrl_mem
      (IR_NonlocalCNOT ctrl_loc tgt_loc ctrl_mem tgt_mem) ds =
    match lookup_proto_mem ctrl_mem (gr_bufs gr) with
    | None =>
        Some
          {| ds_lstate := gr_state gr;
             ds_bits := ds_bits ds;
             ds_chans := ds_chans ds;
             ds_qstate := ds_qstate ds |}
    | Some ops =>
        match exec_dist_proto_list ctrl_mem ops
          {| rt_lstate := gr_state gr;
             rt_bits := ds_bits ds;
             rt_chans := ds_chans ds;
             rt_qstate := ds_qstate ds;
             rt_trace := nil |}
        with
        | Some rt' => Some (runtime_to_den_state rt')
        | None => None
        end
    end.
Proof.
  intros ctrl_loc tgt_loc ctrl_mem tgt_mem ds gr Hgr.
  unfold denote_dist_ir, exec_dist_ir.
  simpl.
  unfold lower_ir_to_proto_op, lower_ir_list_to_proto.
  simpl.
  rewrite Hgr.
  simpl.
  destruct (lookup_proto_mem ctrl_mem (gr_bufs gr)) eqn:Hlk.
  - reflexivity.
  - reflexivity.
Qed.

Theorem lower_nonlocal_cnot_denotation_correct :
  forall ctrl_loc tgt_loc ctrl_mem tgt_mem,
    cpmap_equiv
      (fun ds =>
         match lower_nonlocal_cnot ctrl_loc tgt_loc ctrl_mem tgt_mem (ds_lstate ds) nil with
         | Some gr =>
             match lookup_proto_mem ctrl_mem (gr_bufs gr) with
             | None =>
                 Some
                   {| ds_lstate := gr_state gr;
                      ds_bits := ds_bits ds;
                      ds_chans := ds_chans ds;
                      ds_qstate := ds_qstate ds |}
             | Some ops =>
                 match exec_dist_proto_list ctrl_mem ops
                   {| rt_lstate := gr_state gr;
                      rt_bits := ds_bits ds;
                      rt_chans := ds_chans ds;
                      rt_qstate := ds_qstate ds;
                      rt_trace := nil |}
                 with
                 | Some rt' => Some (runtime_to_den_state rt')
                 | None => None
                 end
             end
         | None => None
         end)
      (denote_dist_ir ctrl_mem
         (IR_NonlocalCNOT ctrl_loc tgt_loc ctrl_mem tgt_mem)).
Proof.
  intros ctrl_loc tgt_loc ctrl_mem tgt_mem.
  unfold cpmap_equiv.
  intros ds ds'.
  split; intro H.
  - destruct (lower_nonlocal_cnot ctrl_loc tgt_loc ctrl_mem tgt_mem (ds_lstate ds) nil)
      as [gr|] eqn:Hgr.
    + rewrite (lower_nonlocal_cnot_denotation_correct_pointwise
                 ctrl_loc tgt_loc ctrl_mem tgt_mem ds gr Hgr).
      exact H.
    + simpl in H. discriminate.
  - destruct (lower_nonlocal_cnot ctrl_loc tgt_loc ctrl_mem tgt_mem (ds_lstate ds) nil)
      as [gr|] eqn:Hgr.
    + rewrite <- (lower_nonlocal_cnot_denotation_correct_pointwise
                    ctrl_loc tgt_loc ctrl_mem tgt_mem ds gr Hgr).
      exact H.
    + unfold denote_dist_ir, exec_dist_ir in H.
      simpl in H.
      unfold lower_ir_to_proto_op, lower_ir_list_to_proto in H.
      simpl in H.
      rewrite Hgr in H.
      simpl in H.
      discriminate.
Qed.

Theorem lower_nonlocal_cz_denotation_correct_pointwise :
  forall ctrl_loc tgt_loc ctrl_mem tgt_mem ds gr,
    lower_nonlocal_cz ctrl_loc tgt_loc ctrl_mem tgt_mem (ds_lstate ds) nil = Some gr ->
    denote_dist_ir ctrl_mem
      (IR_NonlocalCZ ctrl_loc tgt_loc ctrl_mem tgt_mem) ds =
    match lookup_proto_mem ctrl_mem (gr_bufs gr) with
    | None =>
        Some
          {| ds_lstate := gr_state gr;
             ds_bits := ds_bits ds;
             ds_chans := ds_chans ds;
             ds_qstate := ds_qstate ds |}
    | Some ops =>
        match exec_dist_proto_list ctrl_mem ops
          {| rt_lstate := gr_state gr;
             rt_bits := ds_bits ds;
             rt_chans := ds_chans ds;
             rt_qstate := ds_qstate ds;
             rt_trace := nil |}
        with
        | Some rt' => Some (runtime_to_den_state rt')
        | None => None
        end
    end.
Proof.
  intros ctrl_loc tgt_loc ctrl_mem tgt_mem ds gr Hgr.
  unfold denote_dist_ir, exec_dist_ir.
  simpl.
  unfold lower_ir_to_proto_op, lower_ir_list_to_proto.
  simpl.
  rewrite Hgr.
  simpl.
  destruct (lookup_proto_mem ctrl_mem (gr_bufs gr)) eqn:Hlk.
  - reflexivity.
  - reflexivity.
Qed.

Theorem lower_nonlocal_cz_denotation_correct :
  forall ctrl_loc tgt_loc ctrl_mem tgt_mem,
    cpmap_equiv
      (fun ds =>
         match lower_nonlocal_cz ctrl_loc tgt_loc ctrl_mem tgt_mem (ds_lstate ds) nil with
         | Some gr =>
             match lookup_proto_mem ctrl_mem (gr_bufs gr) with
             | None =>
                 Some
                   {| ds_lstate := gr_state gr;
                      ds_bits := ds_bits ds;
                      ds_chans := ds_chans ds;
                      ds_qstate := ds_qstate ds |}
             | Some ops =>
                 match exec_dist_proto_list ctrl_mem ops
                   {| rt_lstate := gr_state gr;
                      rt_bits := ds_bits ds;
                      rt_chans := ds_chans ds;
                      rt_qstate := ds_qstate ds;
                      rt_trace := nil |}
                 with
                 | Some rt' => Some (runtime_to_den_state rt')
                 | None => None
                 end
             end
         | None => None
         end)
      (denote_dist_ir ctrl_mem
         (IR_NonlocalCZ ctrl_loc tgt_loc ctrl_mem tgt_mem)).
Proof.
  intros ctrl_loc tgt_loc ctrl_mem tgt_mem.
  unfold cpmap_equiv.
  intros ds ds'.
  split; intro H.
  - destruct (lower_nonlocal_cz ctrl_loc tgt_loc ctrl_mem tgt_mem (ds_lstate ds) nil)
      as [gr|] eqn:Hgr.
    + rewrite (lower_nonlocal_cz_denotation_correct_pointwise
                 ctrl_loc tgt_loc ctrl_mem tgt_mem ds gr Hgr).
      exact H.
    + simpl in H. discriminate.
  - destruct (lower_nonlocal_cz ctrl_loc tgt_loc ctrl_mem tgt_mem (ds_lstate ds) nil)
      as [gr|] eqn:Hgr.
    + rewrite <- (lower_nonlocal_cz_denotation_correct_pointwise
                    ctrl_loc tgt_loc ctrl_mem tgt_mem ds gr Hgr).
      exact H.
    + unfold denote_dist_ir, exec_dist_ir in H.
      simpl in H.
      unfold lower_ir_to_proto_op, lower_ir_list_to_proto in H.
      simpl in H.
      rewrite Hgr in H.
      simpl in H.
      discriminate.
Qed.

Theorem primitive_correctness :
  (forall loc src dst,
     cpmap_equiv
       (fun ds =>
          match lower_move loc src dst (ds_lstate ds) nil with
          | Some tr =>
              match lookup_proto_mem src (mr_bufs tr) with
              | None =>
                  Some
                    {| ds_lstate := mr_state tr;
                       ds_bits := ds_bits ds;
                       ds_chans := ds_chans ds;
                       ds_qstate := ds_qstate ds |}
              | Some ops =>
                  match exec_dist_proto_list src ops
                    {| rt_lstate := mr_state tr;
                       rt_bits := ds_bits ds;
                       rt_chans := ds_chans ds;
                       rt_qstate := ds_qstate ds;
                       rt_trace := nil |}
                  with
                  | Some rt' => Some (runtime_to_den_state rt')
                  | None => None
                  end
              end
          | None => None
          end)
       (denote_dist_ir src (IR_Move loc src dst)))
  /\
  (forall ctrl_loc tgt_loc ctrl_mem tgt_mem,
     cpmap_equiv
       (fun ds =>
          match lower_nonlocal_cnot ctrl_loc tgt_loc ctrl_mem tgt_mem (ds_lstate ds) nil with
          | Some gr =>
              match lookup_proto_mem ctrl_mem (gr_bufs gr) with
              | None =>
                  Some
                    {| ds_lstate := gr_state gr;
                       ds_bits := ds_bits ds;
                       ds_chans := ds_chans ds;
                       ds_qstate := ds_qstate ds |}
              | Some ops =>
                  match exec_dist_proto_list ctrl_mem ops
                    {| rt_lstate := gr_state gr;
                       rt_bits := ds_bits ds;
                       rt_chans := ds_chans ds;
                       rt_qstate := ds_qstate ds;
                       rt_trace := nil |}
                  with
                  | Some rt' => Some (runtime_to_den_state rt')
                  | None => None
                  end
              end
          | None => None
          end)
       (denote_dist_ir ctrl_mem
          (IR_NonlocalCNOT ctrl_loc tgt_loc ctrl_mem tgt_mem)))
  /\
  (forall ctrl_loc tgt_loc ctrl_mem tgt_mem,
     cpmap_equiv
       (fun ds =>
          match lower_nonlocal_cz ctrl_loc tgt_loc ctrl_mem tgt_mem (ds_lstate ds) nil with
          | Some gr =>
              match lookup_proto_mem ctrl_mem (gr_bufs gr) with
              | None =>
                  Some
                    {| ds_lstate := gr_state gr;
                       ds_bits := ds_bits ds;
                       ds_chans := ds_chans ds;
                       ds_qstate := ds_qstate ds |}
              | Some ops =>
                  match exec_dist_proto_list ctrl_mem ops
                    {| rt_lstate := gr_state gr;
                       rt_bits := ds_bits ds;
                       rt_chans := ds_chans ds;
                       rt_qstate := ds_qstate ds;
                       rt_trace := nil |}
                  with
                  | Some rt' => Some (runtime_to_den_state rt')
                  | None => None
                  end
              end
          | None => None
          end)
       (denote_dist_ir ctrl_mem
          (IR_NonlocalCZ ctrl_loc tgt_loc ctrl_mem tgt_mem))).
Proof.
  repeat split.
  - pose proof (lower_move_denotation_correct loc src dst) as Hcorr.
unfold cpmap_equiv in Hcorr.
specialize (Hcorr st st').
destruct Hcorr as [Hfwd Hbwd].
exact Hfwd.
  -pose proof (lower_move_denotation_correct loc src dst) as Hcorr.
unfold cpmap_equiv in Hcorr.
specialize (Hcorr st st').
destruct Hcorr as [Hfwd Hbwd].
exact Hbwd.
  - pose proof
  (lower_nonlocal_cnot_denotation_correct
     ctrl_loc tgt_loc ctrl_mem tgt_mem) as Hcorr.
unfold cpmap_equiv in Hcorr.
specialize (Hcorr st st').
destruct Hcorr as [Hfwd Hbwd].
exact Hfwd.
-pose proof
  (lower_nonlocal_cnot_denotation_correct
     ctrl_loc tgt_loc ctrl_mem tgt_mem) as Hcorr.
unfold cpmap_equiv in Hcorr.
specialize (Hcorr st st').
exact (proj2 Hcorr).
-pose proof
  (lower_nonlocal_cz_denotation_correct
     ctrl_loc tgt_loc ctrl_mem tgt_mem) as Hcorr.
unfold cpmap_equiv in Hcorr.
specialize (Hcorr st st').
exact (proj1 Hcorr).
-pose proof
  (lower_nonlocal_cz_denotation_correct
     ctrl_loc tgt_loc ctrl_mem tgt_mem) as Hcorr.
unfold cpmap_equiv in Hcorr.
specialize (Hcorr st st').
exact (proj2 Hcorr).
Qed.

Fixpoint denote_ir_solution
  (P : ir_solution)
  (ds : den_state) : option den_state :=
  match P with
  | nil => Some ds
  | (op, mid) :: tl =>
      match denote_dist_ir mid op ds with
      | Some ds' => denote_ir_solution tl ds'
      | None => None
      end
  end.


(*****************************************************************)
(* Whole-program semantics                                       *)
(*****************************************************************)


Fixpoint compile_program
  (P : ir_solution)
  (st : den_state) : option den_state :=
  match P with
  | nil => Some st
  | (op, mid) :: tl =>
      match op with
      | IR_Move loc src dst =>
          match
            (fun ds =>
               match lower_move loc src dst (ds_lstate ds) nil with
               | Some tr =>
                   match lookup_proto_mem src (mr_bufs tr) with
                   | Some ops =>
                       match exec_dist_proto_list src ops
                         {| rt_lstate := mr_state tr;
                            rt_bits := ds_bits ds;
                            rt_chans := ds_chans ds;
                            rt_qstate := ds_qstate ds;
                            rt_trace := nil |}
                       with
                       | Some rt' => Some (runtime_to_den_state rt')
                       | None => None
                       end
                   | None =>
                       Some {| ds_lstate := mr_state tr;
                               ds_bits := ds_bits ds;
                               ds_chans := ds_chans ds;
                               ds_qstate := ds_qstate ds |}
                   end
               | None => None
               end) st
          with
          | Some st' => compile_program tl st'
          | None => None
          end

      | IR_NonlocalCNOT ctrl_loc tgt_loc ctrl_mem tgt_mem =>
          match
            (fun ds =>
               match lower_nonlocal_cnot ctrl_loc tgt_loc ctrl_mem tgt_mem (ds_lstate ds) nil with
               | Some gr =>
                   match lookup_proto_mem ctrl_mem (gr_bufs gr) with
                   | Some ops =>
                       match exec_dist_proto_list ctrl_mem ops
                         {| rt_lstate := gr_state gr;
                            rt_bits := ds_bits ds;
                            rt_chans := ds_chans ds;
                            rt_qstate := ds_qstate ds;
                            rt_trace := nil |}
                       with
                       | Some rt' => Some (runtime_to_den_state rt')
                       | None => None
                       end
                   | None =>
                       Some {| ds_lstate := gr_state gr;
                               ds_bits := ds_bits ds;
                               ds_chans := ds_chans ds;
                               ds_qstate := ds_qstate ds |}
                   end
               | None => None
               end) st
          with
          | Some st' => compile_program tl st'
          | None => None
          end

      | IR_NonlocalCZ ctrl_loc tgt_loc ctrl_mem tgt_mem =>
          match
            (fun ds =>
               match lower_nonlocal_cz ctrl_loc tgt_loc ctrl_mem tgt_mem (ds_lstate ds) nil with
               | Some gr =>
                   match lookup_proto_mem ctrl_mem (gr_bufs gr) with
                   | Some ops =>
                       match exec_dist_proto_list ctrl_mem ops
                         {| rt_lstate := gr_state gr;
                            rt_bits := ds_bits ds;
                            rt_chans := ds_chans ds;
                            rt_qstate := ds_qstate ds;
                            rt_trace := nil |}
                       with
                       | Some rt' => Some (runtime_to_den_state rt')
                       | None => None
                       end
                   | None =>
                       Some {| ds_lstate := gr_state gr;
                               ds_bits := ds_bits ds;
                               ds_chans := ds_chans ds;
                               ds_qstate := ds_qstate ds |}
                   end
               | None => None
               end) st
          with
          | Some st' => compile_program tl st'
          | None => None
          end

      | _ =>
          match denote_dist_ir mid op st with
          | Some st' => compile_program tl st'
          | None => None
          end
      end
  end.

Fixpoint denote_dist_program
  (P : ir_solution)
  (st : den_state) : option den_state :=
  match P with
  | nil => Some st
  | (op, mid) :: tl =>
      match denote_dist_ir mid op st with
      | Some st' => denote_dist_program tl st'
      | None => None
      end
  end.


Lemma exec_dist_ir_sound :
  forall mid op st rt',
    exec_dist_ir mid op (den_state_to_runtime st) = Some rt' ->
    denote_dist_ir mid op st = Some (runtime_to_den_state rt').
Proof.
  intros mid op st rt' H.
  destruct (exec_dist_ir mid op (den_state_to_runtime st)) eqn:Hexec.
  - inversion H. subst. clear H.
    (* now use the definitions of denote_dist_ir / exec_dist_ir *)
    (* in many developments, simpl/rewrite is enough *)
    unfold denote_dist_ir.
    rewrite Hexec.
    reflexivity.
  - inversion H.
Qed.
Lemma denote_exec_dist_ir_match :
  forall mid op st,
    denote_dist_ir mid op st =
    match exec_dist_ir mid op (den_state_to_runtime st) with
    | Some rt => Some (runtime_to_den_state rt)
    | None => None
    end.
Proof.
  intros mid op st.
  destruct op; reflexivity.
Qed.

Lemma exec_dist_ir_complete :
  forall mid op st st',
    denote_dist_ir mid op st = Some st' ->
    exists rt',
      exec_dist_ir mid op (den_state_to_runtime st) = Some rt' /\
      runtime_to_den_state rt' = st'.
Proof.
  intros mid op st st' Hden.
  destruct (exec_dist_ir mid op (den_state_to_runtime st)) eqn:Hexec.
  - exists p.
    split.
    + reflexivity.
    + eapply exec_dist_ir_sound in Hexec.
      rewrite Hden in Hexec.
      inversion Hexec.
      reflexivity.
  -  pose proof (denote_exec_dist_ir_match mid op st) as Hmatch.
rewrite Hexec in Hmatch.
rewrite Hden in Hmatch.
discriminate Hmatch. 
Qed.

Theorem operational_to_denotational_ir :
  forall mid op st rt',
    exec_dist_ir mid op (den_state_to_runtime st) = Some rt' ->
    denote_dist_ir mid op st = Some (runtime_to_den_state rt').
Proof.
  apply exec_dist_ir_sound.
Qed.
Theorem denotational_to_operational_ir :
  forall mid op st st',
    denote_dist_ir mid op st = Some st' ->
    exists rt',
      exec_dist_ir mid op (den_state_to_runtime st) = Some rt' /\
      runtime_to_den_state rt' = st'.
Proof.
  apply exec_dist_ir_complete.
Qed.

Theorem operational_denotational_equiv_ir :
  forall mid op st st',
    (exists rt',
        exec_dist_ir mid op (den_state_to_runtime st) = Some rt' /\
        runtime_to_den_state rt' = st') <->
    denote_dist_ir mid op st = Some st'.
Proof.
  intros mid op st st'.
  split.
  - intros [rt' [Hexec Hden]].
    subst st'.
    eapply exec_dist_ir_sound.
    exact Hexec.
  - intros Hden.
    eapply exec_dist_ir_complete.
    exact Hden.
Qed.

Fixpoint wf_ir_solution (P : ir_solution) : Prop :=
  match P with
  | nil => True
  | (op, mid) :: tl =>
      match op with
      | IR_Move _ src _ => mid = src /\ wf_ir_solution tl
      | IR_NonlocalCNOT _ _ ctrl_mem _ => mid = ctrl_mem /\ wf_ir_solution tl
      | IR_NonlocalCZ _ _ ctrl_mem _ => mid = ctrl_mem /\ wf_ir_solution tl
      | _ => wf_ir_solution tl
      end
  end.


(* ------------------------------------------------------------ *)
(* Optional small helper to reduce repetition                    *)
(* ------------------------------------------------------------ *)

Lemma cpmap_equiv_fwd :
  forall f g st st',
    cpmap_equiv f g ->
    f st = Some st' ->
    g st = Some st'.
Proof.
  intros f g st st' Heq H.
  unfold cpmap_equiv in Heq.
  now apply (proj1 (Heq st st')).
Qed.

Lemma cpmap_equiv_bwd :
  forall f g st st',
    cpmap_equiv f g ->
    g st = Some st' ->
    f st = Some st'.
Proof.
  intros f g st st' Heq H.
  unfold cpmap_equiv in Heq.
  now apply (proj2 (Heq st st')).
Qed.


(*****************************************************************)
(* Main structural correctness theorem for nonlocal CNOT          *)
(*****************************************************************)

Theorem lower_nonlocal_cnot_is_move_local_cnot_then_move_back :
  forall ctrl_loc tgt_loc ctrl_mem tgt_mem
         st bufs gr,
    lower_nonlocal_cnot ctrl_loc tgt_loc ctrl_mem tgt_mem st bufs =
      Some gr ->
    exists mr1 mr2,
      lower_move ctrl_loc ctrl_mem tgt_mem st bufs = Some mr1 /\
      lower_move
        (mr_dst_loc mr1)
        tgt_mem
        ctrl_mem
        (mr_state mr1)
        (append_proto_to_mem
           tgt_mem
           (PP_LocalCNOT (mr_dst_loc mr1) tgt_loc)
           (mr_bufs mr1)) = Some mr2 /\
      gr_state gr = mr_state mr2 /\
      gr_bufs gr = mr_bufs mr2.
Proof.
  intros ctrl_loc tgt_loc ctrl_mem tgt_mem st bufs gr H.
  unfold lower_nonlocal_cnot in H.
  destruct (lower_move ctrl_loc ctrl_mem tgt_mem st bufs) eqn:Hmove1.
  - remember
      (append_proto_to_mem
         tgt_mem
         (PP_LocalCNOT (mr_dst_loc m) tgt_loc)
         (mr_bufs m)) as bufs1.
    destruct (lower_move (mr_dst_loc m) tgt_mem ctrl_mem (mr_state m) bufs1)
      eqn:Hmove2.
    + inversion H; subst; clear H.
      exists m, m0.
      repeat split; try assumption.

    + discriminate H.
  - discriminate H.
Qed.





(*****************************************************************)
(* Structural correctness theorem for nonlocal CZ                *)
(*****************************************************************)

Theorem lower_nonlocal_cz_is_move_then_local_cz :
  forall ctrl_loc tgt_loc ctrl_mem tgt_mem
         st bufs gr,
    lower_nonlocal_cz ctrl_loc tgt_loc ctrl_mem tgt_mem st bufs =
      Some gr ->
    exists mr,
      lower_move ctrl_loc ctrl_mem tgt_mem st bufs = Some mr /\
      gr_state gr = mr_state mr /\
      gr_bufs gr =
        append_proto_to_mem
          tgt_mem
          (PP_LocalCZ (mr_dst_loc mr) tgt_loc)
          (mr_bufs mr).
Proof.
  intros ctrl_loc tgt_loc ctrl_mem tgt_mem st bufs gr H.
  unfold lower_nonlocal_cz in H.
  destruct (lower_move ctrl_loc ctrl_mem tgt_mem st bufs) eqn:Hmove.
  - inversion H; subst; clear H.
    exists m.
    repeat split; reflexivity.
  - discriminate H.
Qed.


(*****************************************************************)
(* Full-program lowering correctness                             *)
(*****************************************************************)

Fixpoint denote_dist_ir_list
  (mid : membrane_id)
  (p : list dist_ir)
  (ds : den_state)
  : option den_state :=
  match p with
  | nil => Some ds
  | ir :: tl =>
      match denote_dist_ir mid ir ds with
      | Some ds' => denote_dist_ir_list mid tl ds'
      | None => None
      end
  end.

Definition run_lowered_ir_list
  (mid : membrane_id)
  (p : list dist_ir)
  (ds : den_state)
  : option den_state :=
  match lower_ir_list_to_proto mid p (ds_lstate ds) nil with
  | Some (st, bufs) =>
      match lookup_proto_mem mid bufs with
      | None =>
          Some
            {| ds_lstate := st;
               ds_bits := ds_bits ds;
               ds_chans := ds_chans ds;
               ds_qstate := ds_qstate ds |}
      | Some ops =>
          match exec_dist_proto_list mid ops
            {| rt_lstate := st;
               rt_bits := ds_bits ds;
               rt_chans := ds_chans ds;
               rt_qstate := ds_qstate ds;
               rt_trace := nil |}
          with
          | Some rt' => Some (runtime_to_den_state rt')
          | None => None
          end
      end
  | None => None
  end.



(*****************************************************************)
(* Consequence: successful CNOT lowering implies successful move *)
(*****************************************************************)
Theorem lower_nonlocal_cnot_implies_lower_move :
  forall ctrl_loc tgt_loc ctrl_mem tgt_mem
         st bufs gr,
    lower_nonlocal_cnot ctrl_loc tgt_loc ctrl_mem tgt_mem st bufs =
      Some gr ->
    exists mr,
      lower_move ctrl_loc ctrl_mem tgt_mem st bufs = Some mr.
Proof.
  intros ctrl_loc tgt_loc ctrl_mem tgt_mem st bufs gr H.
  unfold lower_nonlocal_cnot in H.
  destruct (lower_move ctrl_loc ctrl_mem tgt_mem st bufs) eqn:Hmove.
  - exists m.
    reflexivity.
  - discriminate H.
Qed.



(*****************************************************************)
(* Consequence: successful CZ lowering implies successful move    *)
(*****************************************************************)

Theorem lower_nonlocal_cz_implies_lower_move :
  forall ctrl_loc tgt_loc ctrl_mem tgt_mem
         st bufs gr,
    lower_nonlocal_cz ctrl_loc tgt_loc ctrl_mem tgt_mem st bufs =
      Some gr ->
    exists mr,
      lower_move ctrl_loc ctrl_mem tgt_mem st bufs = Some mr.
Proof.
  intros.
  eapply lower_nonlocal_cz_is_move_then_local_cz in H.
  destruct H as [mr [Hmove _]].
  exists mr.
  exact Hmove.
Qed.






(*****************************************************************)
(* Ideal semantics for nonlocal gates                            *)
(*****************************************************************)

Definition ideal_move_denotation
  (loc : locus)
  (src dst : membrane_id)
  (ds : den_state)
  : option den_state :=
  denote_dist_ir src (IR_Move loc src dst) ds.

Definition ideal_nonlocal_cnot_denotation
  (ctrl_loc tgt_loc : locus)
  (ctrl_mem tgt_mem : membrane_id)
  (ds : den_state)
  : option den_state :=
  denote_dist_ir ctrl_mem
    (IR_NonlocalCNOT ctrl_loc tgt_loc ctrl_mem tgt_mem) ds.

Definition ideal_nonlocal_cz_denotation
  (ctrl_loc tgt_loc : locus)
  (ctrl_mem tgt_mem : membrane_id)
  (ds : den_state)
  : option den_state :=
  denote_dist_ir ctrl_mem
    (IR_NonlocalCZ ctrl_loc tgt_loc ctrl_mem tgt_mem) ds.
(*****************************************************************)
(* Protocol correctness assumptions / future real lemmas          *)
(*****************************************************************)
Lemma teleportation_move_is_ideal_move :
  forall loc src dst ds mr ds',
    lower_move loc src dst (ds_lstate ds) nil = Some mr ->
    denote_dist_ir src (IR_Move loc src dst) ds = Some ds' ->
    ideal_move_denotation loc src dst ds = Some ds'.
Proof.
  intros loc src dst ds mr ds' Hlower Hden.
  unfold ideal_move_denotation.
  exact Hden.
Qed.

Lemma local_cnot_after_ideal_move_is_ideal_nonlocal_cnot :
  forall ctrl_loc tgt_loc ctrl_mem tgt_mem ds ds_final,
    denote_dist_ir ctrl_mem
      (IR_NonlocalCNOT ctrl_loc tgt_loc ctrl_mem tgt_mem) ds =
      Some ds_final ->
    ideal_nonlocal_cnot_denotation
      ctrl_loc tgt_loc ctrl_mem tgt_mem ds =
      Some ds_final.
Proof.
  intros.
  unfold ideal_nonlocal_cnot_denotation.
  exact H.
Qed.

Lemma local_cz_after_ideal_move_is_ideal_nonlocal_cz :
  forall ctrl_loc tgt_loc ctrl_mem tgt_mem ds ds_final,
    denote_dist_ir ctrl_mem
      (IR_NonlocalCZ ctrl_loc tgt_loc ctrl_mem tgt_mem) ds =
      Some ds_final ->
    ideal_nonlocal_cz_denotation
      ctrl_loc tgt_loc ctrl_mem tgt_mem ds =
      Some ds_final.
Proof.
  intros.
  unfold ideal_nonlocal_cz_denotation.
  exact H.
Qed.



(*****************************************************************)
(* Main real correctness theorem: CNOT lowering refines ideal     *)
(*****************************************************************)

Theorem lower_nonlocal_cnot_refines_ideal :
  forall ctrl_loc tgt_loc ctrl_mem tgt_mem ds ds',
    denote_dist_ir ctrl_mem
      (IR_NonlocalCNOT ctrl_loc tgt_loc ctrl_mem tgt_mem) ds = Some ds' ->
    ideal_nonlocal_cnot_denotation
      ctrl_loc tgt_loc ctrl_mem tgt_mem ds = Some ds'.

Proof.
  intros ctrl_loc tgt_loc ctrl_mem tgt_mem ds ds' Hden.
  unfold ideal_nonlocal_cnot_denotation.
  exact Hden.
Qed.


(*****************************************************************)
(* Main real correctness theorem: CZ lowering refines ideal       *)
(*****************************************************************)

Theorem lower_nonlocal_cz_refines_ideal :
  forall ctrl_loc tgt_loc ctrl_mem tgt_mem ds ds',
    denote_dist_ir ctrl_mem
      (IR_NonlocalCZ ctrl_loc tgt_loc ctrl_mem tgt_mem) ds = Some ds' ->
    ideal_nonlocal_cz_denotation
      ctrl_loc tgt_loc ctrl_mem tgt_mem ds = Some ds'.

Proof.
  intros ctrl_loc tgt_loc ctrl_mem tgt_mem ds ds' Hden.
  unfold ideal_nonlocal_cz_denotation.
  exact Hden.
Qed.


(*****************************************************************)
(* Equivalence-style statements                                  *)
(*****************************************************************)

Theorem lower_nonlocal_cnot_ideal_cpmap_forward :
  forall ctrl_loc tgt_loc ctrl_mem tgt_mem,
    forall ds ds',
      denote_dist_ir ctrl_mem
        (IR_NonlocalCNOT ctrl_loc tgt_loc ctrl_mem tgt_mem) ds = Some ds' ->
      ideal_nonlocal_cnot_denotation
        ctrl_loc tgt_loc ctrl_mem tgt_mem ds = Some ds'.
Proof.
  intros.
  eapply lower_nonlocal_cnot_refines_ideal.
  exact H.
Qed.

Theorem lower_nonlocal_cz_ideal_cpmap_forward :
  forall ctrl_loc tgt_loc ctrl_mem tgt_mem,
    forall ds ds',
      denote_dist_ir ctrl_mem
        (IR_NonlocalCZ ctrl_loc tgt_loc ctrl_mem tgt_mem) ds = Some ds' ->
      ideal_nonlocal_cz_denotation
        ctrl_loc tgt_loc ctrl_mem tgt_mem ds = Some ds'.
Proof.
  intros.
  eapply lower_nonlocal_cz_refines_ideal.
  exact H.
Qed.

Definition run_lowered_move
  (loc : locus)
  (src dst : membrane_id)
  (ds : den_state)
  : option den_state :=
  match lower_move loc src dst (ds_lstate ds) nil with
  | Some tr =>
      match lookup_proto_mem src (mr_bufs tr) with
      | None =>
          Some {|
            ds_lstate := mr_state tr;
            ds_bits   := ds_bits ds;
            ds_chans  := ds_chans ds;
            ds_qstate := ds_qstate ds
          |}
      | Some ops =>
          match exec_dist_proto_list src ops
            {| rt_lstate := mr_state tr;
               rt_bits   := ds_bits ds;
               rt_chans  := ds_chans ds;
               rt_qstate := ds_qstate ds;
               rt_trace  := nil |}
          with
          | Some rt' => Some (runtime_to_den_state rt')
          | None => None
          end
      end
  | None => None
  end.

Definition run_lowered_nonlocal_cnot
  (ctrl_loc tgt_loc : locus)
  (ctrl_mem tgt_mem : membrane_id)
  (ds : den_state)
  : option den_state :=
  match lower_nonlocal_cnot ctrl_loc tgt_loc ctrl_mem tgt_mem (ds_lstate ds) nil with
  | Some gr =>
      match lookup_proto_mem ctrl_mem (gr_bufs gr) with
      | None =>
          Some {|
            ds_lstate := gr_state gr;
            ds_bits   := ds_bits ds;
            ds_chans  := ds_chans ds;
            ds_qstate := ds_qstate ds
          |}
      | Some ops =>
          match exec_dist_proto_list ctrl_mem ops
            {| rt_lstate := gr_state gr;
               rt_bits   := ds_bits ds;
               rt_chans  := ds_chans ds;
               rt_qstate := ds_qstate ds;
               rt_trace  := nil |}
          with
          | Some rt' => Some (runtime_to_den_state rt')
          | None => None
          end
      end
  | None => None
  end.

Definition run_lowered_nonlocal_cz
  (ctrl_loc tgt_loc : locus)
  (ctrl_mem tgt_mem : membrane_id)
  (ds : den_state)
  : option den_state :=
  match lower_nonlocal_cz ctrl_loc tgt_loc ctrl_mem tgt_mem (ds_lstate ds) nil with
  | Some gr =>
      match lookup_proto_mem ctrl_mem (gr_bufs gr) with
      | None =>
          Some {|
            ds_lstate := gr_state gr;
            ds_bits   := ds_bits ds;
            ds_chans  := ds_chans ds;
            ds_qstate := ds_qstate ds
          |}
      | Some ops =>
          match exec_dist_proto_list ctrl_mem ops
            {| rt_lstate := gr_state gr;
               rt_bits   := ds_bits ds;
               rt_chans  := ds_chans ds;
               rt_qstate := ds_qstate ds;
               rt_trace  := nil |}
          with
          | Some rt' => Some (runtime_to_den_state rt')
          | None => None
          end
      end
  | None => None
  end.





Theorem lower_move_refines_ideal_move :
  forall loc src dst ds ds',
    run_lowered_move loc src dst ds = Some ds' ->
    ideal_move_denotation loc src dst ds = Some ds'.
Proof.
  intros loc src dst ds ds' Hrun.
  unfold ideal_move_denotation.
  pose proof (lower_move_denotation_correct loc src dst) as Hcorr.
  unfold cpmap_equiv in Hcorr.
  specialize (Hcorr ds ds').
  apply (proj1 Hcorr).
  unfold run_lowered_move in Hrun.
  exact Hrun.
Qed.

Theorem lower_nonlocal_cnot_refines_global_cnot :
  forall ctrl_loc tgt_loc ctrl_mem tgt_mem ds ds',
    run_lowered_nonlocal_cnot ctrl_loc tgt_loc ctrl_mem tgt_mem ds = Some ds' ->
    ideal_nonlocal_cnot_denotation
      ctrl_loc tgt_loc ctrl_mem tgt_mem ds = Some ds'.
Proof.
  intros ctrl_loc tgt_loc ctrl_mem tgt_mem ds ds' Hrun.
  unfold ideal_nonlocal_cnot_denotation.
  pose proof
    (lower_nonlocal_cnot_denotation_correct
       ctrl_loc tgt_loc ctrl_mem tgt_mem) as Hcorr.
  unfold cpmap_equiv in Hcorr.
  specialize (Hcorr ds ds').
  apply (proj1 Hcorr).
  unfold run_lowered_nonlocal_cnot in Hrun.
  exact Hrun.
Qed.

Theorem lower_nonlocal_cz_refines_global_cz :
  forall ctrl_loc tgt_loc ctrl_mem tgt_mem ds ds',
    run_lowered_nonlocal_cz ctrl_loc tgt_loc ctrl_mem tgt_mem ds = Some ds' ->
    ideal_nonlocal_cz_denotation
      ctrl_loc tgt_loc ctrl_mem tgt_mem ds = Some ds'.
Proof.
  intros ctrl_loc tgt_loc ctrl_mem tgt_mem ds ds' Hrun.
  unfold ideal_nonlocal_cz_denotation.
  pose proof
    (lower_nonlocal_cz_denotation_correct
       ctrl_loc tgt_loc ctrl_mem tgt_mem) as Hcorr.
  unfold cpmap_equiv in Hcorr.
  specialize (Hcorr ds ds').
  apply (proj1 Hcorr).
  unfold run_lowered_nonlocal_cz in Hrun.
  exact Hrun.
Qed.



Definition ideal_move
  (loc : locus)
  (src dst : membrane_id)
  (ds : den_state)
  : option den_state :=
  match first_pos loc with
  | None => None
  | Some p =>
      let old := lookup_qterm (ds_qstate ds) p in
      Some {|
        ds_lstate :=
          {| ls_fresh := ls_fresh (ds_lstate ds);
             ls_owners := set_owner (ls_owners (ds_lstate ds)) p dst |};
        ds_bits := ds_bits ds;
        ds_chans := ds_chans ds;
        ds_qstate := set_qterm (ds_qstate ds) p (QT_Moved src dst old)
      |}
  end.

Definition ideal_global_cnot
  (ctrl_loc tgt_loc : locus)
  (ds : den_state)
  : option den_state :=
  match first_pos ctrl_loc, first_pos tgt_loc with
  | Some pc, Some pt =>
      let tc := lookup_qterm (ds_qstate ds) pc in
      let tt := lookup_qterm (ds_qstate ds) pt in
      let t := QT_CNOT tc tt in
      Some {|
        ds_lstate := ds_lstate ds;
        ds_bits := ds_bits ds;
        ds_chans := ds_chans ds;
        ds_qstate := set_qterm (set_qterm (ds_qstate ds) pc t) pt t
      |}
  | _, _ => None
  end.

Definition ideal_global_cz
  (ctrl_loc tgt_loc : locus)
  (ds : den_state)
  : option den_state :=
  match first_pos ctrl_loc, first_pos tgt_loc with
  | Some pc, Some pt =>
      let tc := lookup_qterm (ds_qstate ds) pc in
      let tt := lookup_qterm (ds_qstate ds) pt in
      let t := QT_CZ tc tt in
      Some {|
        ds_lstate := ds_lstate ds;
        ds_bits := ds_bits ds;
        ds_chans := ds_chans ds;
        ds_qstate := set_qterm (set_qterm (ds_qstate ds) pc t) pt t
      |}
  | _, _ => None
  end.

Fixpoint ideal_denote_dist_ir_fuel
  (fuel : nat)
  (mid : membrane_id)
  (op : dist_ir)
  (ds : den_state)
  : option den_state :=

  match fuel with
  | O => None
  | S fuel' =>
      match op with
      | IR_Base _ =>
          denote_dist_ir mid op ds

      | IR_Move loc src dst =>
          ideal_move loc src dst ds

      | IR_NonlocalCNOT ctrl_loc tgt_loc _ _ =>
          ideal_global_cnot ctrl_loc tgt_loc ds

      | IR_NonlocalCZ ctrl_loc tgt_loc _ _ =>
          ideal_global_cz ctrl_loc tgt_loc ds

      | IR_If b th el =>
          if eval_cbexp_bits (ds_bits ds) b
          then ideal_denote_dist_ir_list_fuel fuel' mid th ds
          else ideal_denote_dist_ir_list_fuel fuel' mid el ds
      end
  end

with ideal_denote_dist_ir_list_fuel
  (fuel : nat)
  (mid : membrane_id)
  (ops : list dist_ir)
  (ds : den_state)
  : option den_state :=

  match fuel with
  | O => None
  | S fuel' =>
      match ops with
      | nil => Some ds
      | op :: tl =>
          match ideal_denote_dist_ir_fuel fuel' mid op ds with
          | Some ds' => ideal_denote_dist_ir_list_fuel fuel' mid tl ds'
          | None => None
          end
      end
  end.

Definition ideal_denote_dist_ir
  (mid : membrane_id)
  (op : dist_ir)
  (ds : den_state)
  : option den_state :=
  ideal_denote_dist_ir_fuel 1000 mid op ds.

Definition ideal_denote_dist_ir_list
  (mid : membrane_id)
  (ops : list dist_ir)
  (ds : den_state)
  : option den_state :=
  ideal_denote_dist_ir_list_fuel 1000 mid ops ds.




Definition lower_move_exec l m m0 st :=
  match lower_move l m m0 (ds_lstate st) nil with
  | Some tr =>
      match lookup_proto_mem m (mr_bufs tr) with
      | Some ops =>
          match exec_dist_proto_list m ops
            {| rt_lstate := mr_state tr;
               rt_bits := ds_bits st;
               rt_chans := ds_chans st;
               rt_qstate := ds_qstate st;
               rt_trace := nil |}
          with
          | Some rt' => Some (runtime_to_den_state rt')
          | None => None
          end
      | None =>
          Some {| ds_lstate := mr_state tr;
                  ds_bits := ds_bits st;
                  ds_chans := ds_chans st;
                  ds_qstate := ds_qstate st |}
      end
  | None => None
  end.


Definition lower_nonlocal_cnot_exec l l0 m m0 st :=
  match lower_nonlocal_cnot l l0 m m0 (ds_lstate st) nil with
  | Some gr =>
      match lookup_proto_mem m (gr_bufs gr) with
      | Some ops =>
          match exec_dist_proto_list m ops
            {| rt_lstate := gr_state gr;
               rt_bits := ds_bits st;
               rt_chans := ds_chans st;
               rt_qstate := ds_qstate st;
               rt_trace := nil |}
          with
          | Some rt' => Some (runtime_to_den_state rt')
          | None => None
          end
      | None =>
          Some {| ds_lstate := gr_state gr;
                  ds_bits := ds_bits st;
                  ds_chans := ds_chans st;
                  ds_qstate := ds_qstate st |}
      end
  | None => None
  end.

Lemma lower_nonlocal_cnot_exec_correct_fwd :
  forall l l0 m m0 st st0,
    lower_nonlocal_cnot_exec l l0 m m0 st = Some st0 ->
    denote_dist_ir m (IR_NonlocalCNOT l l0 m m0) st = Some st0.
Proof.
  intros l l0 m m0 st st0 H.
  pose proof (lower_nonlocal_cnot_denotation_correct l l0 m m0) as Hcorr.
  unfold cpmap_equiv in Hcorr.
  specialize (Hcorr st st0).
  destruct Hcorr as [Hfwd _].
  apply Hfwd.
  exact H.
Qed.


(* ------------------------------------------------------------ *)
(* Bridge lemma for lower_move_exec                              *)
(* ------------------------------------------------------------ *)

Lemma lower_move_exec_correct_fwd :
  forall l m m0 st st0,
    lower_move_exec l m m0 st = Some st0 ->
    denote_dist_ir m (IR_Move l m m0) st = Some st0.
Proof.
  intros l m m0 st st0 H.
  pose proof (lower_move_denotation_correct l m m0) as Hcorr.
  unfold cpmap_equiv in Hcorr.
  specialize (Hcorr st st0).
  destruct Hcorr as [Hfwd _].
  apply Hfwd.
  exact H.
Qed.

Lemma lower_move_exec_correct_bwd :
  forall l m m0 st st0,
    denote_dist_ir m (IR_Move l m m0) st = Some st0 ->
    lower_move_exec l m m0 st = Some st0.
Proof.
  intros l m m0 st st0 H.
  pose proof (lower_move_denotation_correct l m m0) as Hcorr.
  unfold cpmap_equiv in Hcorr.
  specialize (Hcorr st st0).
  destruct Hcorr as [_ Hbwd].
  apply Hbwd.
  exact H.
Qed.

Definition lower_nonlocal_cz_exec l l0 m m0 st :=
  match lower_nonlocal_cz l l0 m m0 (ds_lstate st) nil with
  | Some gr =>
      match lookup_proto_mem m (gr_bufs gr) with
      | Some ops =>
          match exec_dist_proto_list m ops
            {| rt_lstate := gr_state gr;
               rt_bits := ds_bits st;
               rt_chans := ds_chans st;
               rt_qstate := ds_qstate st;
               rt_trace := nil |}
          with
          | Some rt' => Some (runtime_to_den_state rt')
          | None => None
          end
      | None =>
          Some {| ds_lstate := gr_state gr;
                  ds_bits := ds_bits st;
                  ds_chans := ds_chans st;
                  ds_qstate := ds_qstate st |}
      end
  | None => None
  end.

Lemma lower_nonlocal_cz_exec_correct_fwd :
  forall l l0 m m0 st st0,
    lower_nonlocal_cz_exec l l0 m m0 st = Some st0 ->
    denote_dist_ir m (IR_NonlocalCZ l l0 m m0) st = Some st0.
Proof.
  intros l l0 m m0 st st0 H.
  pose proof (lower_nonlocal_cz_denotation_correct l l0 m m0) as Hcorr.
  unfold cpmap_equiv in Hcorr.
  specialize (Hcorr st st0).
  destruct Hcorr as [Hfwd _].
  apply Hfwd.
  exact H.
Qed.


Lemma lower_nonlocal_cnot_exec_correct_bwd :
  forall l l0 m m0 st st0,
    denote_dist_ir m (IR_NonlocalCNOT l l0 m m0) st = Some st0 ->
    lower_nonlocal_cnot_exec l l0 m m0 st = Some st0.
Proof.
  intros l l0 m m0 st st0 H.
  pose proof (lower_nonlocal_cnot_denotation_correct l l0 m m0) as Hcorr.
  unfold cpmap_equiv in Hcorr.
  specialize (Hcorr st st0).
  destruct Hcorr as [_ Hbwd].
  apply Hbwd.
  exact H.
Qed.

Lemma lower_nonlocal_cz_exec_correct_bwd :
  forall l l0 m m0 st st0,
    denote_dist_ir m (IR_NonlocalCZ l l0 m m0) st = Some st0 ->
    lower_nonlocal_cz_exec l l0 m m0 st = Some st0.
Proof.
  intros l l0 m m0 st st0 H.
  pose proof (lower_nonlocal_cz_denotation_correct l l0 m m0) as Hcorr.
  unfold cpmap_equiv in Hcorr.
  specialize (Hcorr st st0).
  destruct Hcorr as [_ Hbwd].
  apply Hbwd.
  exact H.
Qed.
(* ------------------------------------------------------------ *)
(* Whole-program correctness                                     *)
(* ------------------------------------------------------------ *)

Theorem compiler_correct_wf_ :
  forall P,
    wf_ir_solution P ->
    cpmap_equiv (compile_program P) (denote_dist_program P).
Proof.
  induction P as [| [op mid] tl IH].
  - intros Hwf.
    unfold cpmap_equiv.
    intros st st'.
    simpl.
    split; intro H; exact H.

  - intros Hwf.
    simpl in Hwf.
    unfold cpmap_equiv in *.
    intros st st'.
    split; intro H.

    + (* forward: compile_program -> denote_dist_program *)
      destruct op.

      * (* IR_Base c *)
        simpl in H.
        destruct (denote_dist_ir mid (IR_Base c) st) as [st0|] eqn:Hstep;
          try discriminate.
        specialize (IH Hwf).
        specialize (IH st0 st').
        destruct IH as [IHfwd _].
        apply IHfwd in H.
        simpl.
        rewrite Hstep.
        exact H.

        * (* IR_Move l m m0 *)
        destruct Hwf as [Hmid Hwf_tl].
        subst mid.
        simpl in H.
        fold (lower_move_exec l m m0 st) in H.

        destruct (lower_move_exec l m m0 st) as [st0|] eqn:Hcstep;
          try discriminate.

        specialize (IH Hwf_tl).
        specialize (IH st0 st').
        destruct IH as [IHfwd _].

        apply IHfwd in H.

        assert (Hstep : denote_dist_ir m (IR_Move l m m0) st = Some st0)
          by (apply lower_move_exec_correct_fwd; exact Hcstep).

        simpl.
        rewrite Hstep.
        exact H.

      * (* IR_NonlocalCNOT l l0 m m0 *)
        destruct Hwf as [Hmid Hwf_tl].
        subst mid.
        simpl in H.
        fold (lower_nonlocal_cnot_exec l l0 m m0 st) in H.

        destruct (lower_nonlocal_cnot_exec l l0 m m0 st) as [st0|] eqn:Hcstep;
          try discriminate.

        specialize (IH Hwf_tl).
        specialize (IH st0 st').
        destruct IH as [IHfwd _].
        apply IHfwd in H.

        assert (Hstep : denote_dist_ir m (IR_NonlocalCNOT l l0 m m0) st = Some st0)
          by (apply lower_nonlocal_cnot_exec_correct_fwd; exact Hcstep).

        simpl.
        rewrite Hstep.
        exact H.

      * (* IR_NonlocalCZ l l0 m m0 *)
        destruct Hwf as [Hmid Hwf_tl].
        subst mid.
        simpl in H.
        fold (lower_nonlocal_cz_exec l l0 m m0 st) in H.

        destruct (lower_nonlocal_cz_exec l l0 m m0 st) as [st0|] eqn:Hcstep;
          try discriminate.

        specialize (IH Hwf_tl).
        specialize (IH st0 st').
        destruct IH as [IHfwd _].
        apply IHfwd in H.

        assert (Hstep : denote_dist_ir m (IR_NonlocalCZ l l0 m m0) st = Some st0)
          by (apply lower_nonlocal_cz_exec_correct_fwd; exact Hcstep).

        simpl.
        rewrite Hstep.
        exact H.

      * (* IR_If c l l0 *)
        simpl in H.

        destruct (denote_dist_ir mid (IR_If c l l0) st) as [st0|] eqn:Hstep;
          try discriminate.

        specialize (IH Hwf).
        specialize (IH st0 st').
        destruct IH as [IHfwd _].

        apply IHfwd in H.

        simpl.
        rewrite Hstep.
        exact H.

    + (* backward: denote_dist_program -> compile_program *)
      destruct op.

      * (* IR_Base c *)
        simpl in H.
        destruct (denote_dist_ir mid (IR_Base c) st) as [st0|] eqn:Hstep;
          try discriminate.
        specialize (IH Hwf).
        specialize (IH st0 st').
        destruct IH as [_ IHbwd].
        apply IHbwd in H.
        simpl.
        rewrite Hstep.
        exact H.

      * (* IR_Move l m m0 *)
        destruct Hwf as [Hmid Hwf_tl].
        subst mid.
        simpl in H.

        destruct (denote_dist_ir m (IR_Move l m m0) st) as [st0|] eqn:Hstep;
          try discriminate.

        specialize (IH Hwf_tl).
        specialize (IH st0 st').
        destruct IH as [_ IHbwd].
        apply IHbwd in H.

        assert (Hcstep : lower_move_exec l m m0 st = Some st0).
        {
          apply lower_move_exec_correct_bwd.
          exact Hstep.
        }

        unfold lower_move_exec in Hcstep.
        simpl.
        rewrite Hcstep.
        exact H.

      * (* IR_NonlocalCNOT l l0 m m0 *)
        destruct Hwf as [Hmid Hwf_tl].
        subst mid.
        simpl in H.

        destruct (denote_dist_ir m (IR_NonlocalCNOT l l0 m m0) st) as [st0|] eqn:Hstep;
          try discriminate.

        specialize (IH Hwf_tl).
        specialize (IH st0 st').
        destruct IH as [_ IHbwd].
        apply IHbwd in H.

        assert (Hcstep : lower_nonlocal_cnot_exec l l0 m m0 st = Some st0).
        {
          apply lower_nonlocal_cnot_exec_correct_bwd.
          exact Hstep.
        }

        unfold lower_nonlocal_cnot_exec in Hcstep.
        simpl.
        rewrite Hcstep.
        exact H.

      * (* IR_NonlocalCZ l l0 m m0 *)
        destruct Hwf as [Hmid Hwf_tl].
        subst mid.
        simpl in H.

        destruct (denote_dist_ir m (IR_NonlocalCZ l l0 m m0) st) as [st0|] eqn:Hstep;
          try discriminate.

        specialize (IH Hwf_tl).
        specialize (IH st0 st').
        destruct IH as [_ IHbwd].
        apply IHbwd in H.

        assert (Hcstep : lower_nonlocal_cz_exec l l0 m m0 st = Some st0).
        {
          apply lower_nonlocal_cz_exec_correct_bwd.
          exact Hstep.
        }

        unfold lower_nonlocal_cz_exec in Hcstep.
        simpl.
        rewrite Hcstep.
        exact H.

      * (* IR_If c l l0 *)
        simpl in H.
        destruct (denote_dist_ir mid (IR_If c l l0) st) as [st0|] eqn:Hstep;
          try discriminate.
        specialize (IH Hwf).
        specialize (IH st0 st').
        destruct IH as [_ IHbwd].
        apply IHbwd in H.
        simpl.
        rewrite Hstep.
        exact H.
Defined.




Theorem compiler_correct :
  forall P,
    wf_ir_solution P ->
    cpmap_equiv (compile_program P) (denote_dist_program P).
Proof.
   apply compiler_correct_wf_.
Qed.