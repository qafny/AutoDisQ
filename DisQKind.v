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
(**********************)
(** Locus Definitions **)
(**********************)

Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Local Open Scope nat_scope.

(* Kind checking rules to determine if an expression has a certain kind. *)

Inductive union_f : (ktype * locus) -> (ktype * locus) -> (ktype * locus) -> Prop :=
 | union_cl_1: union_f (CT,nil) (CT,nil) (CT, nil)
 |  union_sl: forall a l1 l2 lc, union_f (QT lc a,l1) (CT,l2) (QT lc a, l1)
 | union_sr: forall b l1 l2 lc, union_f (CT,l1) (QT lc b,l2) (QT lc b, l1)
 | union_two: forall a b l1 l2 lc, ses_dis (l1++l2) -> union_f (QT lc a,l1) (QT lc b,l2) (QT lc (a+b), l1++l2). 

Inductive type_aexp : aenv -> aexp -> (ktype*locus) -> Prop :=
   | ba_type : forall env b, AEnv.MapsTo b CT env -> type_aexp env (BA b) (CT,[])
   | ba_type_q : forall env b n lc, AEnv.MapsTo b (QT lc n) env -> type_aexp env (BA b) (QT lc n,[(b,BNum 0,BNum n)])
   | num_type : forall env n, type_aexp env (Num n) (CT,[])
   | plus_type : forall env e1 e2 t1 t2 t3, 
                   type_aexp env e1 t1 -> type_aexp env e2 t2 -> union_f t1 t2 t3 -> 
                     type_aexp env (APlus e1 e2) t3
   | mult_type : forall env e1 e2 t1 t2 t3, type_aexp env e1 t1 -> type_aexp env e2 t2 -> union_f t1 t2 t3 -> 
                     type_aexp env (AMult e1 e2) t3.


Inductive type_vari : aenv -> varia -> (ktype*locus) -> Prop :=
   | aexp_type : forall env a t, type_aexp env a t -> type_vari env a t
   | index_type : forall env x n v lc,
       AEnv.MapsTo x (QT lc n) env -> 0 <= v < n -> type_vari env (Index x (Num v)) (QT lc 1,[(x,BNum v,BNum (S v))]).


Inductive type_cbexp : aenv -> cbexp -> ktype -> Prop :=
  | ceq_type : forall env a b, type_aexp env a (CT,nil) -> type_aexp env b (CT,nil) ->
                     type_cbexp env (CEq a b) CT
  | clt_type : forall env a b, type_aexp env a (CT,nil) -> type_aexp env b (CT,nil) ->
                     type_cbexp env (CLt a b) CT.

Inductive type_bexp : aenv -> bexp -> (ktype*locus) -> Prop :=
   | cb_type: forall env b t, type_cbexp env b t -> type_bexp env (CB b) (t,nil)

   | beq_type_1 : forall env a b x m n v lc, AEnv.MapsTo a (QT lc m) env -> 
             AEnv.MapsTo x (QT lc n) env -> 0 <= v < n -> 
           type_bexp env (BEq (BA a) ((Num b)) x (Num v)) (QT lc (m+1),((a,BNum 0,BNum m)::[(x,BNum v,BNum (S v))]))
   | beq_type_2 : forall env a b x m n v lc, AEnv.MapsTo a (QT lc m) env -> 
             AEnv.MapsTo x (QT lc n) env -> 0 <= v < n -> 
           type_bexp env (BEq ((Num b)) (BA a) x (Num v)) (QT lc (m+1),((a,BNum 0,BNum m)::[(x,BNum v,BNum (S v))]))
   | blt_type_1 : forall env a b x m n v lc, AEnv.MapsTo a (QT lc m) env -> 
             AEnv.MapsTo x (QT lc n) env -> 0 <= v < n -> 
           type_bexp env (BLt (BA a) ((Num b)) x (Num v)) (QT lc (m+1),((a,BNum 0,BNum m)::[(x,BNum v,BNum (S v))]))
   | blt_type_2 : forall env a b x m n v lc, AEnv.MapsTo a (QT lc m) env -> 
             AEnv.MapsTo x (QT lc n) env -> 0 <= v < n -> 
           type_bexp env (BLt ((Num b)) (BA a) x (Num v)) (QT lc (m+1),((a,BNum 0,BNum m)::[(x,BNum v,BNum (S v))]))
   | btest_type : forall env x n v lc, AEnv.MapsTo x (QT lc n) env -> 0 <= v < n 
            -> type_bexp env (BTest x (Num v)) (QT lc 1,[((x,BNum v,BNum (S v)))])
   | bneg_type : forall env b t, type_bexp env b t -> type_bexp env (BNeg b) t.


Inductive type_exp : aenv -> exp -> (ktype*locus) -> Prop :=
   | skip_fa : forall env x v n lc, AEnv.MapsTo x (QT lc n) env -> 0 <= v < n -> type_exp env (SKIP x (Num v)) (QT lc 1,([(x,BNum v, BNum (S v))]))
   | x_fa : forall env x v n lc, AEnv.MapsTo x (QT lc n) env -> 0 <= v < n -> type_exp env (X x (Num v)) (QT lc 1,([(x,BNum v, BNum (S v))]))
   | rz_fa : forall env q x v n lc, AEnv.MapsTo x (QT lc n) env -> 0 <= v < n -> type_exp env (RZ q x (Num v)) (QT lc 1, ([(x,BNum v, BNum (S v))]))
   | rrz_fa : forall env q x v n lc, AEnv.MapsTo x (QT lc n) env -> 0 <= v < n -> type_exp env (RRZ q x (Num v)) (QT lc 1, ([(x,BNum v, BNum (S v))]))
   | sr_fa : forall env q x n lc, AEnv.MapsTo x (QT lc n) env -> q < n -> type_exp env (SR q x) (QT lc n, ([(x,BNum 0, BNum n)]))
   | srr_fa : forall env q x n lc,  AEnv.MapsTo x (QT lc n) env -> q < n -> type_exp env (SRR q x) (QT lc n, ([(x,BNum 0, BNum n)]))
   | qft_fa : forall env q x n lc,  AEnv.MapsTo x (QT lc n) env -> q <= n -> 0 < n -> type_exp env (QFT x q) (QT lc n, ([(x,BNum 0, BNum n)]))
   | rqft_fa : forall env q x n lc,  AEnv.MapsTo x (QT lc n) env -> q <= n -> 0 < n -> type_exp env (RQFT x q) (QT lc n, ([(x,BNum 0, BNum n)]))
   | cu_fa : forall env x v n e t1 t2 lc, AEnv.MapsTo x (QT lc n) env -> 0 <= v < n -> 
            type_exp env e t1 -> union_f (QT lc 1, ([(x,BNum v, BNum (S v))])) t1 t2 -> type_exp env (CU x (Num v) e) t2
   | seq_fa : forall env e1 t1 e2 t2 t3, type_exp env e1 t1 -> type_exp env e2 t2 -> union_f t1 t2 t3 ->
                 type_exp env (Seq e1 e2) t3.

Inductive fv_su : aenv -> single_u -> locus -> Prop :=
   fv_su_h : forall env a n s lc, type_vari env a (QT lc n, s) -> fv_su env (RH a) s
  | fv_su_qft : forall env x n lc, AEnv.MapsTo x (QT lc n) env -> fv_su env (SQFT x) ([(x,BNum 0,BNum n)])
  | fv_su_rqft : forall env x n lc, AEnv.MapsTo x (QT lc n) env -> fv_su env (SRQFT x) ([(x,BNum 0,BNum n)]).

Inductive fv_cexp : aenv -> cexp -> locus -> Prop :=
  | cmeas : forall env x l, fv_cexp env (CMeas x l) l
  | cappu_fa : forall env l e, fv_cexp env (CAppU l e) l.

Inductive fv_cdexp : aenv -> cdexp -> locus -> Prop :=
  | csend_fa : forall env c a, fv_cdexp env (Send c a) nil
  | crecv_fa : forall env c a,  fv_cdexp env (Recv c a) nil.                                    

Fixpoint freeVarsAExp (a:aexp) := match a with BA x => ([x]) | Num n => nil
            | APlus e1 e2 => (freeVarsAExp e1)++(freeVarsAExp e2)
            | AMult e1 e2 => (freeVarsAExp e1)++(freeVarsAExp e2)
  end.
Definition freeVarsVari (a:varia) := match a with AExp x => freeVarsAExp x
            | Index x v => (x::freeVarsAExp v)
  end.
Definition freeVarsCBexp (a:cbexp) := match a with CEq x y => (freeVarsAExp x)++(freeVarsAExp y)
         | CLt x y => (freeVarsAExp x)++(freeVarsAExp y)
  end.
Fixpoint freeVarsBexp (a:bexp) := match a with CB b => (freeVarsCBexp b)
         | BEq x y i a => i::((freeVarsVari x)++(freeVarsVari y)++(freeVarsAExp a))
         | BLt x y i a => i::((freeVarsVari x)++(freeVarsVari y)++(freeVarsAExp a))
         | BTest i a => i::(freeVarsAExp a)
         | BNeg b => freeVarsBexp b
  end.
Definition freeVarsMAExp (m:maexp) := match m with AE n => freeVarsAExp n | Meas x => ([x]) end.

Fixpoint list_sub (s:list var) (b:var) :=
   match s with nil => nil
              | a::al => if a =? b then list_sub al b else a::list_sub al b
   end.

Lemma list_sub_not_in : forall l x xa, xa <> x -> In xa l -> In xa (list_sub l x).
Proof.
  induction l;intros;simpl in *. easy.
  bdestruct (a =? x); subst. destruct H0; subst. easy.
  apply IHl. easy. easy. destruct H0; subst. simpl. left. easy.
  simpl. right. apply IHl; try easy.
Qed.

Lemma list_sub_not_in_r : forall l x xa, xa <> x -> In xa (list_sub l x) -> In xa l.
Proof.
  induction l;intros;simpl in *. easy.
  bdestruct (a =? x); subst. apply IHl in H0. right. easy.
  easy. simpl in *. destruct H0. subst. left. easy.
  apply IHl in H0. right. easy. easy.
Qed.

Lemma list_sub_not_same: forall x l, ~ In x (list_sub l x).
Proof.
  intros. induction l; intros;simpl in *; try easy.
  bdestruct (a =? x); subst. easy.
  intros R. simpl in *. destruct R. easy.
  easy.
Qed.
(*
Fixpoint freeVarsCExp (p:cexp) := 
   match p with CAppU l e => freeVarsCExp e               
              | _ => nil
   end.
*)
Definition freeVarsNotCAExp (env:aenv) (a:aexp) :=
   forall x t, In x (freeVarsAExp a) -> AEnv.MapsTo x t env -> t <> CT.

Definition freeVarsNotCBExp (env:aenv) (a:bexp) :=
   forall x t, In x (freeVarsBexp a) -> AEnv.MapsTo x t env -> t <> CT.
(*
Definition freeVarsNotCCExp (env:aenv) (a:cexp) :=
   forall x t, In x (freeVarsCExp a) -> AEnv.MapsTo x t env -> t <> CT.
*)

Fixpoint simp_aexp (a:aexp) :=
   match a with BA y => None
             | Num a => Some a
             | APlus c d => match (simp_aexp c,simp_aexp d) with (Some v1,Some v2) => Some (v1+v2)
                                | (_,_) => None
                            end
             | AMult c d => match (simp_aexp c,simp_aexp d) with (Some v1,Some v2) => Some (v1*v2)
                                | (_,_) => None
                            end
   end.

Fixpoint simp_bexp (a:bexp) :=
   match a with CB (CEq x y) => match (simp_aexp x,simp_aexp y) with (Some v1,Some v2) => Some (v1 =? v2)
                                                                   | _ => None
                                end
              | CB (CLt x y) => match (simp_aexp x,simp_aexp y) with (Some v1,Some v2) => Some (v1 <? v2)
                                                                   | _ => None
                                end
              | BNeg b => match simp_bexp b with None => None | Some b' => Some (negb b') end
              | _ => None
   end.

Definition simp_cbexp (a:cbexp) :=
   match a with (CEq x y) => match (simp_aexp x,simp_aexp y) with (Some v1,Some v2) => Some (v1 =? v2)
                                                                   | _ => None
                                end
              | (CLt x y) => match (simp_aexp x,simp_aexp y) with (Some v1,Some v2) => Some (v1 <? v2)
                                                                   | _ => None
                                end
   end.


Inductive eval_aexp : stack -> aexp -> nat -> Prop :=
    | var_sem : forall s x n, AEnv.MapsTo x n s -> eval_aexp s (BA x) n
    | mnum_sem: forall s n, eval_aexp s (Num n) n
    | aplus_sem: forall s e1 e2 n1 n2, eval_aexp s e1 n1 -> eval_aexp s e2 n2 -> eval_aexp s (APlus e1 e2) (n1 + n2)
    | amult_sem: forall s e1 e2 n1 n2, eval_aexp s e1 n1 -> eval_aexp s e2 n2 -> eval_aexp s (AMult e1 e2) (n1 * n2).

Inductive eval_cbexp : stack -> bexp -> bool -> Prop :=
    | ceq_sem : forall s x y n1 n2, eval_aexp s x (n1) -> eval_aexp s y (n2) -> eval_cbexp s (CB (CEq x y)) (n1 =? n2)
    | clt_sem : forall s x y n1 n2, eval_aexp s x (n1) -> eval_aexp s y (n2) -> eval_cbexp s (CB (CLt x y)) (n1 <? n2)
    | bneq_sem: forall s e b, eval_cbexp s e b -> eval_cbexp s (BNeg e) (negb b).
(*
Inductive simp_varia : aenv -> varia -> range -> Prop :=
    | aexp_sem : forall env x n, AEnv.MapsTo x (QT n) env -> simp_varia env (AExp (BA x)) (x,BNum 0, BNum n)
    | index_sem : forall env x v, simp_varia env (Index x (Num v)) (x,BNum v,BNum (v+1)).
*)
(*
Lemma kind_aexp_class_empty: forall env a t l, type_aexp env a (Mo t, l) -> t = CT \/ t = MT -> l = [].
Proof.
  intros. remember (Mo t, l) as e. induction H; simpl in *; try easy.
  inv Heqe. destruct H. inv H. easy. easy. inv Heqe. easy. inv Heqe. easy.
  subst. destruct H0; subst. inv H2. easy.
  inv H2. easy. easy.
  destruct H0; subst. inv H2. easy. inv H2; easy.
  inv Heqe. easy.
Qed.
*)

Lemma simp_aexp_empty: forall a v, simp_aexp a = Some v -> freeVarsAExp a = [].
Proof.
  induction a;intros;simpl in *; try easy.
  destruct (simp_aexp a1) eqn:eq1.
  destruct (simp_aexp a2) eqn:eq2. inv H. erewrite IHa1; try easy. erewrite IHa2; try easy.
  inv H. inv H.
  destruct (simp_aexp a1) eqn:eq1.
  destruct (simp_aexp a2) eqn:eq2. inv H. erewrite IHa1; try easy. erewrite IHa2; try easy.
  inv H. inv H.
Qed.

Lemma subst_aexp_not_eq: forall e x v, subst_aexp e x v <> x.
Proof.
  induction e; intros; simpl in *; try easy.
  bdestruct (x0 =? x); subst; try easy. intros R. inv R. easy.
Qed.

Lemma freeVarsAExpNotIn: forall n x v, ~ In x (freeVarsAExp (subst_aexp n x v)).
Proof.
  induction n; intros; simpl in *; try easy.
  bdestruct (x0 =? x). simpl in *; try easy. simpl in *. intros R.
  destruct R; try easy.
  rewrite H0 in *. easy.
  destruct (subst_aexp n1 x v) eqn:eq1.
  simpl in *. intros R. destruct R; subst.
  specialize (subst_aexp_not_eq n1 x v) as X1. rewrite eq1 in X1. easy.
  specialize (IHn2 x v). easy.
  destruct (subst_aexp n2 x v) eqn:eq2.
  simpl in *. intros R. destruct R; subst.
  specialize (subst_aexp_not_eq n2 x v) as X1. rewrite eq2 in X1. easy.
  easy. simpl in *. easy.
  specialize (IHn2 x v). rewrite eq2 in IHn2. simpl in *. easy.
  specialize (IHn2 x v). rewrite eq2 in IHn2. simpl in *. easy.
  specialize (IHn1 x v). rewrite eq1 in IHn1. simpl in *.
  intros R. apply in_app_iff in R.
  destruct R. easy.
  specialize (IHn2 x v). easy.
  specialize (IHn1 x v). rewrite eq1 in IHn1. simpl in *.
  intros R. apply in_app_iff in R.
  destruct R. easy.
  specialize (IHn2 x v). easy.
  destruct (subst_aexp n1 x v) eqn:eq1.
  simpl in *. intros R. destruct R; subst.
  specialize (subst_aexp_not_eq n1 x v) as X1. rewrite eq1 in X1. easy.
  specialize (IHn2 x v). easy.
  destruct (subst_aexp n2 x v) eqn:eq2.
  simpl in *. intros R. destruct R; subst.
  specialize (subst_aexp_not_eq n2 x v) as X1. rewrite eq2 in X1. easy.
  easy. simpl in *. easy.
  specialize (IHn2 x v). rewrite eq2 in IHn2. simpl in *. easy.
  specialize (IHn2 x v). rewrite eq2 in IHn2. simpl in *. easy.
  specialize (IHn1 x v). rewrite eq1 in IHn1. simpl in *.
  intros R. apply in_app_iff in R.
  destruct R. easy.
  specialize (IHn2 x v). easy.
  specialize (IHn1 x v). rewrite eq1 in IHn1. simpl in *.
  intros R. apply in_app_iff in R.
  destruct R. easy.
  specialize (IHn2 x v). easy.
Qed.

Lemma freeVarsCBExpNotIn: forall n x v, ~ In x (freeVarsCBexp (subst_cbexp n x v)).
Proof.
  induction n; intros; simpl in *; try easy.
  intros R. apply in_app_iff in R. destruct R.
  specialize (freeVarsAExpNotIn x x0 v) as X1. easy.
  specialize (freeVarsAExpNotIn y x0 v) as X1. easy.
  intros R. apply in_app_iff in R. destruct R.
  specialize (freeVarsAExpNotIn x x0 v) as X1. easy.
  specialize (freeVarsAExpNotIn y x0 v) as X1. easy.
Qed.

Lemma freeVarsAExp_subst: forall n y x v, In y (freeVarsAExp (subst_aexp n x v))
       -> In y (freeVarsAExp n).
Proof.
  induction n; intros; simpl in *; try easy.
  bdestruct (x0 =? x); subst; simpl in *; try easy.
  apply in_app_iff in H. destruct H.
  apply in_app_iff. left. apply IHn1 in H. easy.
  apply IHn2 in H. apply in_app_iff. right. easy.
  apply in_app_iff in H. destruct H.
  apply in_app_iff. left. apply IHn1 in H. easy.
  apply IHn2 in H. apply in_app_iff. right. easy.
Qed.

Lemma freeVarsMAExp_subst: forall n y x v, In y (freeVarsMAExp (subst_mexp n x v))
       -> In y (freeVarsMAExp n).
Proof.
  induction n; intros; simpl in *; try easy.
  simpl in *. eapply freeVarsAExp_subst. apply H.
Qed.

Lemma freeVarsVari_subst: forall n y x v, In y (freeVarsVari (subst_varia n x v))
       -> In y (freeVarsVari n).
Proof.
  induction n; intros; simpl in *; try easy.
  apply freeVarsAExp_subst in H. easy. destruct H.
  left. easy. right.
  apply freeVarsAExp_subst in H. easy.
Qed.

Lemma freeVarsCBExp_subst: forall n y x v, In y (freeVarsCBexp (subst_cbexp n x v))
       -> In y (freeVarsCBexp n).
Proof.
  induction n; intros; simpl in *; try easy.
  apply in_app_iff in H. apply in_app_iff.
  destruct H. left. apply freeVarsAExp_subst in H. easy.
  right. apply freeVarsAExp_subst in H. easy. 
  apply in_app_iff in H. apply in_app_iff.
  destruct H. left. apply freeVarsAExp_subst in H. easy.
  right. apply freeVarsAExp_subst in H. easy. 
Qed.

Lemma freeVarsBExp_subst: forall n y x v, In y (freeVarsBexp (subst_bexp n x v))
       -> In y (freeVarsBexp n).
Proof.
  induction n; intros; simpl in *; try easy.
  apply freeVarsCBExp_subst in H. easy.
  destruct H. left. easy.
  right.
  apply in_app_iff in H. apply in_app_iff.
  destruct H.
  apply freeVarsVari_subst in H. left. easy.
  apply in_app_iff in H. right. apply in_app_iff.
  destruct H.
  apply freeVarsVari_subst in H. left. easy.
  right.
  apply freeVarsAExp_subst in H. easy.
  destruct H. left. easy.
  right.
  apply in_app_iff in H. apply in_app_iff.
  destruct H.
  apply freeVarsVari_subst in H. left. easy.
  apply in_app_iff in H. right. apply in_app_iff.
  destruct H.
  apply freeVarsVari_subst in H. left. easy.
  right.
  apply freeVarsAExp_subst in H. easy.
  destruct H. left. easy.
  right. apply freeVarsAExp_subst in H. easy.
  apply IHn in H. easy.
Qed.

Lemma type_cbexp_no_qt: forall b env t n lc, type_cbexp env b t -> t <> QT lc n.
Proof.
 induction b;intros;simpl in *; try easy. inv H. easy.
 inv H. easy.
Qed.

Lemma type_bexp_ses_len : forall b l env n lc, type_bexp env b (QT lc n, l) -> ses_len l = Some n.
Proof.
  induction b;intros;simpl in *; try easy.
  inv H. remember (QT lc n) as a. apply type_cbexp_no_qt with (n := n)(lc := lc) in H3. subst. easy.
  inv H. unfold ses_len in *;simpl in *. destruct v. simpl in *.
  replace (m - 0 + 1) with (m+1) by lia. easy.
  replace (m - 0 + (S v - v + 0)) with (m+1) by lia. easy.
  unfold ses_len in *;simpl in *. destruct v. simpl in *.
  replace (m - 0 + 1) with (m+1) by lia. easy.
  replace (m - 0 + (S v - v + 0)) with (m+1) by lia. easy.
  inv H. unfold ses_len in *;simpl in *. destruct v. simpl in *.
  replace (m - 0 + 1) with (m+1) by lia. easy.
  replace (m - 0 + (S v - v + 0)) with (m+1) by lia. easy.
  unfold ses_len in *;simpl in *. destruct v. simpl in *.
  replace (m - 0 + 1) with (m+1) by lia. easy.
  replace (m - 0 + (S v - v + 0)) with (m+1) by lia. easy.
  inv H. unfold ses_len in *;simpl in *. destruct v. simpl in *. easy.
  replace (S v - v + 0) with 1 by lia. easy.
  inv H. apply IHb in H2. easy.
Qed.

Lemma type_bexp_ses_len_gt : forall b l env n lc, type_bexp env b (QT lc n, l) -> ses_len l = Some n -> 0 < n.
Proof.
  induction b;intros;simpl in *; try easy.
  inv H. remember (QT lc n) as a. apply type_cbexp_no_qt with (n := n)(lc := lc) in H4. subst. easy.
  inv H. lia. lia.
  inv H. lia. lia. inv H. lia. inv H. apply IHb in H3. easy. easy.
Qed.

