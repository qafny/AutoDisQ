Require Import Reals.
Require Import Psatz.
Require Import Complex.
Require Import SQIR.
Require Import VectorStates UnitaryOps Coq.btauto.Btauto Coq.NArith.Nnat Permutation. 
Require Import Dirac.
Require
  Import QPE.
Require Import BasicUtility.
Require Import OQASM.
Require Import OQASMProof.
Require Import Classical_Prop.
Require Import MathSpec.
Require Import DisQSyntax.
Require Import DisQDef.
Require Import DisQKind.
(**********************)
(** Unitary Programs **)
(**********************)


Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.OrderedTypeEx.
Declare Scope cexp_scope.
Delimit Scope cexp_scope with cexp.
Local Open Scope cexp_scope.
Local Open Scope nat_scope.


(* This is the semantics for basic gate set of the language. *)

Fixpoint compile_range_state (n st i:nat) (x:var) (b: rz_val) (f:posi -> val) :=
    match n with 0 => f
            | S m => (compile_range_state m st i x b f)[(x,st+m) |-> (nval (b (i+m)) allfalse)]
    end.

Fixpoint compile_ses_state' (i:nat) (l:locus) (b:rz_val) :=
   match l with nil => (fun _ => nval false allfalse)
           | ((x,BNum l,BNum r)::xl) => compile_range_state (r-l) l i x b (compile_ses_state' (i+(r-l)) xl b)
           | (_::xl) => compile_ses_state' i xl b
   end.
Definition compile_ses_state (l:locus) (b:rz_val) := compile_ses_state' 0 l b.

Fixpoint turn_oqasm_range (rmax n st i:nat) (x:var) (f:posi -> val) (r:rz_val) (b: rz_val) : option (rz_val * rz_val) :=
    match n with 0 => Some (r,b)
            | S m => match (turn_oqasm_range rmax m st i x f r b)
         with None => None
         | Some (r',b') => match f (x,st+m) with nval ba ra => Some (n_rotate rmax ra r', update b' (i+m) ba)
                                             | _ => None
                            end
               end
    end.

Fixpoint turn_oqasm_ses' (rmax i:nat) (l:locus) (f:posi -> val) (b:rz_val) :=
   match l with nil => Some (allfalse, b)
           | ((x,BNum l,BNum r)::xl) => 
               match turn_oqasm_ses' rmax (i+(r-l)) xl f b with None => None
               | Some (ra,ba) => turn_oqasm_range rmax (r-l) l i x f ra ba
               end
           | _ => None
   end.
Definition turn_oqasm_ses rmax (l:locus) (f:posi -> val) b  := turn_oqasm_ses' rmax 0 l f b.

Definition cover_n (f:rz_val) (n:nat) := fun i => if i <? n then false else f i.

Inductive match_value : nat -> state_elem -> state_elem -> Prop :=
   match_nval : forall n p r1 r2, (forall i, i < n -> r1 i = r2 i) -> match_value n (Nval p r1) (Nval p r2)
 | match_hval: forall n r1 r2, (forall i, i < n -> r1 i = r2 i) -> match_value n (Hval r1) (Hval r2)
 | match_cval: forall n m r1 r2, (forall j, j < m -> fst (r1 j) = fst (r2 j) /\
               (forall i, i < n -> (snd (r1 j)) i = (snd (r2 j)) i)) -> match_value n (Cval m r1) (Cval m r2).


Definition match_values (S1 S2: qstate) :=
  Forall2 (fun s1 s2 =>
           (match (s1,s2) with ((l,s), (l',s')) =>
             l = l' /\
            (match ses_len l with Some n => match_value n s s'
                                | None => False
            end) end)) S1 S2.

Definition eval_nor (rmax:nat) (env:aenv) (l:locus) (r:C) (b:rz_val) (e:exp) :=
   match compile_ses_qenv env l with (f,ss) =>
       match compile_exp_to_oqasm e with
                None => None
              | Some e' => 
       match ses_len l with None => None
            | Some na => 
           match turn_oqasm_ses rmax l (exp_sem f e' (compile_ses_state l b)) (cover_n b na)
                with None => None
                  | Some (ra,ba) => Some ((r* (Cexp (2*PI * (turn_angle ra rmax))))%C, ba)
           end
            end
       end
     end.

Fixpoint eval_ch (rmax:nat) (env:aenv) (l:locus) (m:nat) f (e:exp) :=
   match m with 0 => Some (fun _ => (C0 , allfalse))
          | S n => match eval_nor rmax env l (fst (f n)) (snd (f n)) e with None => None
              | Some (ra,ba) => match eval_ch rmax env l n f e with None => None
                 | Some fa => Some (update fa n (ra , ba))
            end
          end
   end.

Definition eval_to_had (n:nat) (b:rz_val) := (fun i => if i <? n then (update allfalse 0 (b i)) else allfalse).

Definition eval_to_nor (n:nat) (b:nat -> rz_val) := (fun i => if i <? n then b i 0 else false).

Definition all_nor_mode (f:posi -> val) := forall x n, right_mode_val OQASM.Nor (f (x,n)).

(* functions for defining boolean. *)

Fixpoint eval_eq_bool (f:nat -> C * rz_val) (m size v:nat) :=
  match m with 0 => f
           | S m' => update (eval_eq_bool f m' size v) m' 
                   (fst (f m'),update (snd (f m')) size (xorb ((a_nat2fb (snd (f m')) size) =? v) ((snd (f m')) size)))
  end.

Fixpoint eval_lt_bool (f:nat -> C * rz_val) (m size v:nat) :=
  match m with 0 => f
           | S m' => update (eval_lt_bool f m' size v) m' 
                   (fst (f m'),update (snd (f m')) size (xorb ((a_nat2fb (snd (f m')) size) <? v) ((snd (f m')) size)))
  end.

Fixpoint eval_rlt_bool (f:nat -> C * rz_val) (m size v:nat) :=
  match m with 0 => f
           | S m' => update (eval_rlt_bool f m' size v) m' 
                   (fst (f m'),update (snd (f m')) size (xorb (v <? (a_nat2fb (snd (f m')) size)) ((snd (f m')) size)))
  end.

Fixpoint grab_bool_elem (f:nat -> C * rz_val) (m size:nat) :=
  match m with 0 => (0,(fun _ => (C0,allfalse)))
           | S m' => if (snd (f m')) size then 
                  match grab_bool_elem f m' size with (i,acc) => (i+1,update acc i (f m')) end
                else grab_bool_elem f m' size
   end.
Definition grab_bool f m size := grab_bool_elem f m (size - 1).


Definition get_core_bexp (b:bexp) := match b with (BEq x y z a)
            => Some (BTest z a) | BLt x y z a => Some (BTest z a)  | _ => None end.

Inductive eval_bexp : qstate -> bexp -> qstate -> Prop :=
    | beq_sem_1 : forall s x a y z i l n m f, simp_aexp a = Some y ->
                     eval_bexp (((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l,Cval m f)::s)
                         (BEq (BA x) (a) z (Num i)) 
                            (((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l,Cval m (eval_eq_bool f m n y))::s)
    | beq_sem_2 : forall s x a y z i l n m f,
               simp_aexp a = Some y ->
                eval_bexp (((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l,Cval m f)::s)
                         (BEq (a) (BA x) z (Num i))
                            (((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l,Cval m (eval_eq_bool f m n y))::s)
    | blt_sem_1 : forall s x a y z i l n m f, 
               simp_aexp a = Some y ->
                eval_bexp ((((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l),Cval m f)::s)
                       (BLt (BA x) (a) z (Num i)) 
                         ((((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l),(Cval m (eval_lt_bool f m n y)))::s)

    | blt_sem_2 : forall s x a y z i l n m f, 
               simp_aexp a = Some y ->
                 eval_bexp ((((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l),Cval m f)::s)
                        (BLt (a) (BA x) z (Num i))
                       ((((x,BNum 0,BNum n)::(z,BNum i,BNum (S i))::l),(Cval m (eval_rlt_bool f m n y)))::s).

Inductive find_basis_elems (n n':nat) (f:rz_val) (fc:nat -> C*rz_val): 
            nat -> nat -> (nat -> C * rz_val) -> Prop :=
  find_basis_empty: find_basis_elems n n' f fc 0 0 (fun _ => (C0,allfalse))
 | find_basis_many_1: forall i m acc, find_basis_elems n n' f fc i m acc -> 
            f = cut_n (lshift_fun (snd (fc i)) n') n 
         -> find_basis_elems n n' f fc (S i) (S m) (update acc m (fc i))
 | find_basis_many_2: forall i m acc, find_basis_elems n n' f fc i m acc -> 
            f <> cut_n (lshift_fun (snd (fc i)) n') n -> find_basis_elems n n' f fc (S i) m acc.

Inductive assem_elem : nat -> nat -> rz_val -> (nat-> C * rz_val) -> list nat -> Prop :=
    assem_elem_0 : forall size c f, assem_elem 0 size c f nil
  | assem_elem_st : forall size c f m l, assem_elem m size c f l -> cut_n (snd (f m)) size = c
                 -> assem_elem (S m) size c f (m::l)
  | assem_elem_sf : forall size c f m l, assem_elem m size c f l -> cut_n (snd (f m)) size <> c
                 -> assem_elem (S m) size c f l.

Definition combine_two (n:nat) (f:rz_val) (g:rz_val) :=
    (fun x => if x <? n then f x else g (x-n)).

Fixpoint assem_list (m base n:nat) (f:rz_val) (fc: nat -> C * rz_val) (acc:nat -> C*rz_val) :=
    match m with 0 => (base, acc)
               | S m' => match assem_list m' base n f fc acc with (mv, fv) => 
                           (S mv, (update fv mv (fst (fc m'), combine_two n f (snd (fc m')))))
                        end
    end.

(* first n is length of l and second is length of l1. third is num of elements *)
Inductive assem_bool (n n':nat): nat -> (nat-> C * rz_val) -> state_elem -> state_elem -> Prop :=
    assem_bool_empty: forall f fc, assem_bool n n' 0 f fc (Cval 0 (fun _ => (C0,allfalse)))
  | assem_bool_many_1: forall i m m' f fc acc fv, assem_bool n n' i f (Cval m fc) (Cval m' acc) ->
        find_basis_elems n n' (cut_n (snd (f i)) n) fc m 0 fv ->
               assem_bool n n' (S i) f (Cval m fc) (Cval (S m') (update acc m' (f i)))
  | assem_bool_many_2: forall i m m' f fc acc mv fv ma fa, assem_bool n n' i f (Cval m fc) (Cval m' acc) ->
        0 < mv -> find_basis_elems n n' (cut_n (snd (f i)) n) fc m mv fv ->
        assem_list mv m' n (cut_n (snd (f i)) n) fv acc = (ma, fa) -> 
               assem_bool n n' (S i) f (Cval m fc) (Cval ma fa).

Fixpoint subst_qstate (l:qstate) (x:var) (n:nat) :=
  match l with nil => nil
          | (y,v)::yl => (subst_locus y x n,v)::(subst_qstate yl x n)
  end.
Definition subst_state (l:state) (x:var) n := (fst l,subst_qstate (snd l) x n).

Definition loc_memb (m: memb) :=
  match m with Memb l lp => l
          | LockMemb l p lp => l
  end.

Definition alltrue := fun (_:nat) => true.

(************* DisQ Semantics ****************)
(** We define the semantics in two levels: process-level and membrane-level **)

(** Process-level semantics. **)
Inductive p_step {rmax:nat}
  : aenv -> qstate -> process -> (R * option nat) -> qstate -> process -> Prop :=
  | self_pstep : forall aenv s, p_step aenv s PNil (1%R, None) s PNil  
  | if_pstep_t : forall aenv s b P Q, simp_cbexp b = Some true -> p_step aenv s (PIf b P Q) (1%R, None) s P
  | if_pstep_f : forall aenv s b P Q, simp_cbexp b = Some false -> p_step aenv s (PIf b P Q) (1%R, None) s Q
  | op_pstep   : forall aenv s a l m b e ba Q, eval_ch rmax aenv a m b e = Some ba ->
                   p_step aenv ((a++l, Cval m b)::s) (AP (CAppU a e) Q) (1%R, None) ((a++l, Cval m ba)::s) Q
  | mea_pstep   : forall aenv s l x a n v r va va' lc Q k, AEnv.MapsTo a (QT lc n) aenv -> @pick_mea n va (r,v) ->
                                                   k = [(a, BNum 0, BNum n)] -> build_state_ch n v va = Some va' ->
                                                   p_step aenv (((a,BNum 0, BNum n)::l, va)::s) (AP (CMeas x k) Q) (r, Some v) ((l, va')::s) (subst_pexp Q x v)
 | new_pstep : forall aenv s x n Q, p_step aenv s (AP (CNew x n) Q) (1%R, None) (([(x, BNum 0, BNum n)], Cval 1 (fun _ => (C0,allfalse)))::s) Q.

Fixpoint are_0 (l:list process) :=
   match l with [] => True
              | (PNil::xl) => are_0 xl
              | _::_ => False
   end.

Fixpoint same_l (l:glocus) (lv:var) :=
  match l with [] => True
             | ((x,a,b),r)::xl => if r =? lv then same_l xl lv else False
  end.

Fixpoint cut_l (l:glocus) :=
  match l with [] => [] | (((x,a,b),r)::xl) => (x,a,b)::(cut_l xl) end.

Definition inv_sqrt2 : R := / sqrt 2.
Definition cinv_sqrt2: C := inv_sqrt2%C.

(** Membrance-level semantics **)
Inductive m_step {rmax:nat}
  : aenv -> gqstate -> config -> R * option nat -> list var -> gqstate -> config -> Prop :=
  | end_step : forall aenv s l Q, are_0 Q -> m_step aenv s ([Memb l Q]) (1%R, None) [l] s ([Memb l Q])
  | mem_step : forall aenv s l P Q, m_step aenv s ([Memb l (P::Q)]) (Rdiv 1%R (INR (length (P::Q))), None) [l] s ([LockMemb l P Q])
  | rev_step : forall aenv s m l P lp, m = ([LockMemb l P lp]) -> m_step aenv s m (1%R, None) [l] s ([Memb l (P::lp)])
  | commc_sem : forall aenv s x y l1 l2 n m1 m2 cf a P Q, simp_aexp a = Some n -> 
             m_step aenv s ((LockMemb l1 (DP (Send x a) P) m1)::(LockMemb l2 (DP (Recv x y) Q) m2)::cf) 
             (1%R, None) (l1::[l2]) s ((Memb l1 (P::m1))::(Memb l2 (Q::m2))::cf)
  | move_step : forall aenv s a l lp P P' r n n' m v va lv lc fc fca, n = (length lp)+1 -> 
               gses_len a = Some n' -> gses_len l = Some m -> same_l a lc -> mut_state 0 n' m v fc
               -> @p_step rmax aenv [(cut_l a,fc)] P (r,lv) [(cut_l a,va)] P' -> mut_state 0 m n' va fca ->
            m_step aenv ((a++l, v)::s) ([Memb lc (P::lp)]) ((r / INR n)%R, lv) [lc] ((a++l, fc)::s) ([Memb lc (P'::lp)])
  | newchan_step : forall aenv lc1 lc2 c n m1 m2 P Q cf s,
                   m_step aenv s ((LockMemb lc1 (DP (NewCh c n) P) m1)::(LockMemb lc2 (DP (NewCh c n) Q) m2)::cf) (1%R, None) (lc1::[lc2]) 
                   ((([((c,BNum 0, BNum n),lc1)]++[((c,BNum 0,BNum n),lc2)]), 
                      Cval (2^n) (fun i => if i =? 0 then (cinv_sqrt2,allfalse) else (cinv_sqrt2,alltrue)))::s) ((Memb lc1 (P::m1))::(Memb lc2 (Q::m2))::cf)
  | mem_step_ctx : forall  aenv s l P Q cf,
        m_step aenv s [Memb l (P::Q)]
             (Rdiv 1%R (INR (length (P::Q))), None) [l]
             s [LockMemb l P Q] ->
      m_step  aenv s (Memb l (P::Q) :: cf)
             (Rdiv 1%R (INR (length (P::Q))), None) [l]
             s (LockMemb l P Q :: cf)
  | step_ctx_cons :
    forall aenv s m c r lv ls s' c',
      m_step  aenv s c (r,lv) ls s' c' ->
      m_step  aenv s (m :: c) (r,lv) ls s' (m :: c').
