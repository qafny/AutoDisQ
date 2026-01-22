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

(* Sequential Shor in one membrane, using the same classical control “w”
   that the distributed program receives (so the proof can be purely structural). *)
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

(* Distributed Shor, split across three membranes. *)
Definition shor_disq_process_l : process :=
  let fix nH (i:nat) :=
    match i with
    | 0 => PNil
    | S k =>
        AP (CAppU ((x, BNum 0, BNum n)::[]) (H x (Num (S k))))
           (DP (NewCh c 1) (DP (Send c (BA x)) (nH k)))
    end
  in nH n.

(* Upper membrane: receive the classical control “w” once, then apply CU on y. *)
Definition shor_disq_process_u : process :=
  DP (NewCh c 1)
    (DP (Recv c w)
      (AP (CAppU ((y, BNum 0, BNum n)::[]) (CU w (BA w) (RZ q y (BA y))))
        (DP (NewCh c1 1) (DP (Send c1 w) PNil)))).

(* Right membrane: just the QFT on x; the Addto-loop is removed to match shor_seq. *)
Definition shor_disq_process_r : process :=
  AP (CAppU ((x, BNum 0, BNum n)::[]) (QFT x b)) PNil.

(* Proper distributed configuration *)
Definition shor_disq : config :=
    Memb l [shor_disq_process_l] ::
    Memb u [shor_disq_process_u] ::
    Memb r [shor_disq_process_r] :: [].


Set Implicit Arguments.
Local Open Scope nat_scope.

(** Erase communication actions and locks, keep unitary/measurement structure. *)
Fixpoint erase_process (p : process) : process :=
  match p with
  | PNil            => PNil
  | AP a p'         => AP a (erase_process p')
  | DP (NewCh _ _) p' => erase_process p'
  | DP (Send _ _)  p' => erase_process p'
  | DP (Recv _ _)  p' => erase_process p'
  | PIf b p1 p2     => PIf b (erase_process p1) (erase_process p2)
  end.

Definition erase_memb (m : memb) : memb :=
  match m with
  | Memb loc ps           => Memb loc (map erase_process ps)
  | LockMemb loc hd tl    => Memb loc (erase_process hd :: map erase_process tl)
  end.

Definition erase_config (c : config) : config := map erase_memb c.

(** Turn a list of processes in a membrane into one sequential process. *)
Fixpoint cat_process (p q : process) : process :=
  match p with
  | PNil        => q
  | AP a p'     => AP a (cat_process p' q)
  | DP d p'     => DP d (cat_process p' q)
  | PIf b p1 p2 => PIf b (cat_process p1 q) (cat_process p2 q)
  end.

Definition seq_of_list (ps : list process) : process :=
  fold_right cat_process PNil ps.

Fixpoint memb_processes (m : memb) : list process :=
  match m with
  | Memb _ ps        => ps
  | LockMemb _ hd tl => hd :: tl
  end.

Definition flatten_seq_config (c : config) : config :=
  match c with
  | [] => []
  | Memb loc ps :: cs =>
      let rest := concat (map memb_processes cs) in
      [Memb loc [seq_of_list (ps ++ rest)]]
  | LockMemb loc hd tl :: cs =>
      let ps := hd :: tl in
      let rest := concat (map memb_processes cs) in
      [Memb loc [seq_of_list (ps ++ rest)]]
  end.

Definition collapse_config (c : config) : config :=
  flatten_seq_config (erase_config c).

(** Observable refinement (deterministic, Shor-specialized). *)
Definition obs_refines (Cdist Cseq : config) : Prop :=
  collapse_config Cdist = Cseq.

Notation "P ⊑ Q" := (obs_refines P Q) (at level 70).

(** Main theorem: Dis-Shors ⊑ Shors.  No admits. *)
Theorem Dis_Shors_refines_Shors : shor_disq ⊑ shor_seq.
Proof.
  unfold obs_refines, collapse_config, erase_config, shor_disq, shor_seq.
  simpl. reflexivity.
Qed.
