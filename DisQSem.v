Require Import Reals.
Require Import Psatz.
Require Import QuantumLib.Complex.
Require Import SQIR.SQIR.
Require Import QuantumLib.VectorStates.
Require Import SQIR.UnitaryOps.
Require Import Coq.btauto.Btauto Coq.NArith.Nnat. 
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
           | ((x, (l, r))::xl) => compile_range_state (r-l) l i x b (compile_ses_state' (i+(r-l)) xl b)
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
           | ((x,(l,r))::xl) => 
               match turn_oqasm_ses' rmax (i+(r-l)) xl f b with None => None
               | Some (ra,ba) => turn_oqasm_range rmax (r-l) l i x f ra ba
               end
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
                     eval_bexp (((x,(0,n))::(z,(i,(S i)))::l,Cval m f)::s)
                         (BEq (BA x) (a) z (Num i)) 
                            (((x,(0,n))::(z,(i,(S i)))::l,Cval m (eval_eq_bool f m n y))::s)
    | beq_sem_2 : forall s x a y z i l n m f,
               simp_aexp a = Some y ->
                eval_bexp (((x,(0,n))::(z,(i, (S i)))::l,Cval m f)::s)
                         (BEq (a) (BA x) z (Num i))
                            (((x,(0,n))::(z,(i,(S i)))::l,Cval m (eval_eq_bool f m n y))::s)
    | blt_sem_1 : forall s x a y z i l n m f, 
               simp_aexp a = Some y ->
                eval_bexp ((((x,(0,n))::(z,(i,(S i)))::l),Cval m f)::s)
                       (BLt (BA x) (a) z (Num i)) 
                         ((((x,(0,n))::(z,(i,(S i)))::l),(Cval m (eval_lt_bool f m n y)))::s)

    | blt_sem_2 : forall s x a y z i l n m f, 
               simp_aexp a = Some y ->
                 eval_bexp ((((x, (0,n))::(z,(i,(S i)))::l),Cval m f)::s)
                        (BLt (a) (BA x) z (Num i))
                       ((((x,(0,n))::(z,(i,(S i)))::l),(Cval m (eval_rlt_bool f m n y)))::s).

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

(*
Fixpoint subst_qstate (l:qstate) (x:var) (n:nat) :=
  match l with nil => nil
          | (y,v)::yl => (subst_locus y x n,v)::(subst_qstate yl x n)
  end.
Definition subst_state (l:state) (x:var) n := (fst l,subst_qstate (snd l) x n).
*)

Definition alltrue := fun (_:nat) => true.

(************* DisQ Semantics ****************)
(** We define the semantics in two levels: process-level and membrane-level **)

Fixpoint mapNew' (x:var) (i:nat) (n:nat) (q:qstate) :=
   match n with 0 => q
             | S m => mapNew' x i m (([(x,(m,m+1))],Nval C1 (fun _ => false))::q)
   end.
Definition mapNew (x: var * (nat * nat)) q := mapNew' (fst x) (fst (snd x)) ((snd (snd x)) - fst (snd x)) q.

(** Process-level semantics. **)
Inductive step {rmax:nat}
  : aenv -> qstate -> config -> (R * list var) -> qstate -> config -> Prop :=
  | qubit_create : forall aenv s l x p m, step aenv s (Memb l (AP (CNew x) p)::m) (1%R, [l]) (mapNew x s) (Memb l p::m)
  | op_step : forall aenv s a l la m ma b e ba Q, eval_ch rmax aenv a m b e = Some ba ->
                   step aenv ((a++l, Cval m b)::s) (Memb la (AP (CAppU a e) Q)::ma) (1%R, [la]) ((a++l, Cval m ba)::s) (Memb la Q::ma)
  | mea_pstep   : forall aenv s l la ma x a n v r va va' lc Q k, AEnv.MapsTo a (QT lc n) aenv -> @pick_mea n va (r,v) ->
                                                   k = [(a,(0, n))] -> build_state_ch n v va = Some va' ->
              step aenv (((a,(0, n))::l, va)::s) (Memb la (AP (CMeas x k) Q)::ma) (r,[la]) ((l, va')::s) (Memb la (subst_pexp Q x v)::ma)
  | if_pstep_t : forall aenv s b P Q l m, simp_cbexp b = Some true -> step aenv s (Memb l (PIf b P Q)::m) (1%R, [l]) s (Memb l P::m)
  | if_pstep_f : forall aenv s b P Q l m, simp_cbexp b = Some false -> step aenv s (Memb l (PIf b P Q)::m) (1%R, [l]) s (Memb l Q::m)
  | end_step : forall aenv s l m, step aenv s (Memb l PNil::m) (1%R, [l]) s m
  | commc_step : forall aenv s x l1 l2 cf c a P Q, 
             step aenv s ((Memb l1 (AP (Send c x a) P))::(Memb l2 (AP (Recv c x a) Q))::cf) 
             (1%R, (l1::l2::[])) s ((Memb l1 P)::(Memb l2 Q)::cf)
  | comp : forall aenv s s' P m m' l,  step aenv s m l s' m' -> step aenv s (P::m) l s' (P::m').



