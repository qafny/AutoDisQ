From Coq Require Import List Arith Bool Nat.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DisQ.BasicUtility.   (* var := nat *)
Require Import DisQ.DisQSyntax.     (* exp, process, memb, config, ... *)

Definition membrane    : Type := memb.
Definition membranes   : Type := config.
Definition membrane_id : Type := var.

Inductive myOp : Type :=
| OpAP  (a : cexp)                         
| OpDP  (a : cdexp)                       
| OpIf  (b : cbexp) (p q : process). 

Definition op_list : Type := list myOp.
Definition hb_relation : Type := myOp -> myOp -> bool.
Definition rank         : Type := nat.
Definition seq_relation : Type := myOp -> rank.
Definition op_mem_assign : Type := myOp -> membrane_id.

Fixpoint list_eqb {A : Type} (beq : A -> A -> bool) (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x::xs', y::ys' => andb (beq x y) (list_eqb beq xs' ys')
  | _, _ => false
  end.

Fixpoint aexp_eqb (e1 e2 : aexp) : bool :=
  match e1, e2 with
  | BA x1, BA x2 => Nat.eqb x1 x2
  | Num n1, Num n2 => Nat.eqb n1 n2
  | APlus a1 b1, APlus a2 b2 =>
      andb (aexp_eqb a1 a2) (aexp_eqb b1 b2)
  | AMult a1 b1, AMult a2 b2 =>
      andb (aexp_eqb a1 a2) (aexp_eqb b1 b2)
  | _, _ => false
  end.

Definition cbexp_eqb (b1 b2 : cbexp) : bool :=
  match b1, b2 with
  | CEq x1 y1, CEq x2 y2 =>
      andb (aexp_eqb x1 x2) (aexp_eqb y1 y2)
  | CLt x1 y1, CLt x2 y2 =>
      andb (aexp_eqb x1 x2) (aexp_eqb y1 y2)
  | _, _ => false
  end.

Definition bound_eqb (b1 b2 : bound) : bool :=
  match b1, b2 with
  | BVar v1 n1, BVar v2 n2 =>
      andb (Nat.eqb v1 v2) (Nat.eqb n1 n2)
  | BNum n1, BNum n2 =>
      Nat.eqb n1 n2
  | _, _ => false
  end.

Definition range_eqb (r1 r2 : range) : bool :=
  match r1, r2 with
  | (x1, lo1, hi1), (x2, lo2, hi2) =>
      andb (Nat.eqb x1 x2)
           (andb (bound_eqb lo1 lo2)
                 (bound_eqb hi1 hi2))
  end.

Definition locus_eqb (l1 l2 : locus) : bool :=
  list_eqb range_eqb l1 l2.

Fixpoint exp_eqb (e1 e2 : exp) : bool :=
  match e1, e2 with
  | SKIP x1 a1, SKIP x2 a2 =>
      andb (Nat.eqb x1 x2) (aexp_eqb a1 a2)
  | X x1 a1, X x2 a2 =>
      andb (Nat.eqb x1 x2) (aexp_eqb a1 a2)
  | CU x1 a1 e1', CU x2 a2 e2' =>
      andb (Nat.eqb x1 x2) (andb (aexp_eqb a1 a2) (exp_eqb e1' e2'))
  | RZ q1 x1 a1, RZ q2 x2 a2 =>
      andb (Nat.eqb q1 q2) (andb (Nat.eqb x1 x2) (aexp_eqb a1 a2))
  | RRZ q1 x1 a1, RRZ q2 x2 a2 =>
      andb (Nat.eqb q1 q2) (andb (Nat.eqb x1 x2) (aexp_eqb a1 a2))
  | SR q1 x1, SR q2 x2 =>
      andb (Nat.eqb q1 q2) (Nat.eqb x1 x2)
  | SRR q1 x1, SRR q2 x2 =>
      andb (Nat.eqb q1 q2) (Nat.eqb x1 x2)
  | QFT x1 b1, QFT x2 b2 =>
      andb (Nat.eqb x1 x2) (Nat.eqb b1 b2)
  | RQFT x1 b1, RQFT x2 b2 =>
      andb (Nat.eqb x1 x2) (Nat.eqb b1 b2)
  | H x1 a1, H x2 a2 =>
      andb (Nat.eqb x1 x2) (aexp_eqb a1 a2)
  | Addto x1 q1, Addto x2 q2 =>
      andb (Nat.eqb x1 x2) (Nat.eqb q1 q2)
  | Seq s1 t1, Seq s2 t2 =>
      andb (exp_eqb s1 s2) (exp_eqb t1 t2)
  | _, _ => false
  end.

Definition cexp_eqb (c1 c2 : cexp) : bool :=
  match c1, c2 with
  | CNew x1 n1, CNew x2 n2 =>
      andb (Nat.eqb x1 x2) (Nat.eqb n1 n2)
  | CAppU l1 e1, CAppU l2 e2 =>
      andb (locus_eqb l1 l2) (exp_eqb e1 e2)
  | CMeas x1 k1, CMeas x2 k2 =>
      andb (Nat.eqb x1 x2) (locus_eqb k1 k2)
  | _, _ => false
  end.

Definition cdexp_eqb (d1 d2 : cdexp) : bool :=
  match d1, d2 with
  | NewCh c1 n1, NewCh c2 n2 =>
      andb (Nat.eqb c1 c2) (Nat.eqb n1 n2)
  | Send c1 a1, Send c2 a2 =>
      andb (Nat.eqb c1 c2) (aexp_eqb a1 a2)
  | Recv c1 x1, Recv c2 x2 =>
      andb (Nat.eqb c1 c2) (Nat.eqb x1 x2)
  | _, _ => false
  end.

Fixpoint process_eqb (p1 p2 : process) : bool :=
  match p1, p2 with
  | PNil, PNil => true
  | AP a1 p1', AP a2 p2' =>
      andb (cexp_eqb a1 a2) (process_eqb p1' p2')
  | DP a1 p1', DP a2 p2' =>
      andb (cdexp_eqb a1 a2) (process_eqb p1' p2')
  | PIf b1 p1a p1b, PIf b2 p2a p2b =>
      andb (cbexp_eqb b1 b2)
           (andb (process_eqb p1a p2a) (process_eqb p1b p2b))
  | _, _ => false
  end.



Definition myOp_eqb (x y : myOp) : bool :=
  match x, y with
  | OpAP a1, OpAP a2 => cexp_eqb a1 a2
  | OpDP a1, OpDP a2 => cdexp_eqb a1 a2
  | OpIf b1 p1 q1, OpIf b2 p2 q2 =>
      andb (cbexp_eqb b1 b2)
           (andb (process_eqb p1 p2) (process_eqb q1 q2))
  | _, _ => false
  end.

Definition qubit_mem_assign : Type := var -> membrane_id.

Definition fitness_value    : Type := nat.
Definition distributed_prog : Type := config.



(* ------------------------------------------------------------------------- *)
(* Basic list helpers                                                        *)
(* ------------------------------------------------------------------------- *)

Definition var_eqb (x y : var) : bool := Nat.eqb x y.

Fixpoint mem_var (x : var) (xs : list var) : bool :=
  match xs with
  | [] => false
  | y :: tl => if var_eqb x y then true else mem_var x tl
  end.

Fixpoint uniq (xs : list var) : list var :=
  match xs with
  | [] => []
  | x :: tl => if mem_var x tl then uniq tl else x :: uniq tl
  end.

Fixpoint intersect (xs ys : list var) : list var :=
  match xs with
  | [] => []
  | x :: tl => if mem_var x ys then x :: intersect tl ys else intersect tl ys
  end.

(* ------------------------------------------------------------------------- *)
(* vars_of_exp                                                               *)
(* ------------------------------------------------------------------------- *)

Fixpoint vars_of_exp (e : exp) : list var :=
  match e with
  | SKIP _ _ => []
  | X x _ => [x]
  | H x _ => [x]
  | RZ _ x _ => [x]
  | RRZ _ x _ => [x]
  | SR _ x => [x]
  | SRR _ x => [x]
  | QFT x _ => [x]
  | RQFT x _ => [x]
  | Addto x q => [x; q]
  | CU x _ e1 => x :: vars_of_exp e1
  | Seq e1 e2 => vars_of_exp e1 ++ vars_of_exp e2
  end.

Definition share_qubit (e1 e2 : exp) : bool :=
  negb (Nat.eqb (length (intersect (uniq (vars_of_exp e1)) (uniq (vars_of_exp e2)))) 0).

Scheme Equality for exp.

Fixpoint mem_exp (x : exp) (xs : list exp) : bool :=
  match xs with
  | [] => false
  | y :: tl => if exp_eqb x y then true else mem_exp x tl
  end.

Fixpoint remove_exp (x : exp) (xs : list exp) : list exp :=
  match xs with
  | [] => []
  | y :: tl => if exp_eqb x y then tl else y :: remove_exp x tl
  end.

(* ------------------------------------------------------------------------- *)
(*                     os <- gen_os(R)                                  *)
(* ------------------------------------------------------------------------- *)
Definition gen_os (R : op_list) : op_list := R.

(* ------------------------------------------------------------------------- *)
(* Paper Algorithm 1 line 3: hp <- gen_hp(R)                                  *)
(* You used: order-in-R + share_qubit => dependency.                          *)
(* ------------------------------------------------------------------------- *)

Fixpoint index_of_exp (x : exp) (xs : list exp) : nat :=
  match xs with
  | [] => 0
  | y :: tl => if exp_eqb x y then 0 else S (index_of_exp x tl)
  end.

Fixpoint vars_of_aexp (a : aexp) : list var :=
  match a with
  | BA x => [x]
  | Num _ => []
  | APlus a1 a2 => vars_of_aexp a1 ++ vars_of_aexp a2
  | AMult a1 a2 => vars_of_aexp a1 ++ vars_of_aexp a2
  end.

Definition vars_of_cbexp (b : cbexp) : list var :=
  match b with
  | CEq a1 a2 => vars_of_aexp a1 ++ vars_of_aexp a2
  | CLt a1 a2 => vars_of_aexp a1 ++ vars_of_aexp a2
  end.


Definition vars_of_myOp (op : myOp) : list var :=
  match op with
  | OpAP a =>
      match a with
      | CAppU _ e => vars_of_exp e
      | CNew x _ => [x]
      | CMeas x _ => [x]
      end
  | OpDP a =>
      match a with
      | NewCh c _ => [c]
      | Send c e => c :: vars_of_aexp e
      | Recv c x => [c; x]
      end
  | OpIf b _ _ =>
      vars_of_cbexp b
  end.

Definition share_qubit_myOp (o1 o2 : myOp) : bool :=
  negb (Nat.eqb
          (length
             (intersect
                (uniq (vars_of_myOp o1))
                (uniq (vars_of_myOp o2))))
          0).

Fixpoint index_of_myOp (x : myOp) (xs : list myOp) : nat :=
  match xs with
  | [] => 0
  | y :: tl =>
      if myOp_eqb x y
      then 0
      else S (index_of_myOp x tl)
  end.

Definition gen_hp (R : op_list) : hb_relation :=
  fun o1 o2 =>
    let i := index_of_myOp o1 R in
    let j := index_of_myOp o2 R in
    andb (Nat.ltb i j) (share_qubit_myOp o1 o2).


(* ------------------------------------------------------------------------- *)
(*                         MANY schedules                                    *)
(* ------------------------------------------------------------------------- *)
Definition has_incoming_from
  (hp : hb_relation)
  (nodes : list myOp)
  (x : myOp) : bool :=
  existsb (fun y => hp y x) nodes.

Definition available
  (hp : hb_relation)
  (nodes : list myOp) : list myOp :=
  filter (fun x => negb (has_incoming_from hp nodes x)) nodes.

Fixpoint nth_default {A} (d : A) (xs : list A) (n : nat) : A :=
  match n with
  | 0 =>
      match xs with
      | [] => d
      | x :: _ => x
      end
  | S n' =>
      match xs with
      | [] => d
      | _ :: tl => nth_default d tl n'
      end
  end.



(* ---------------- Permutations ---------------- *)

Fixpoint insert_all (x : myOp) (xs : list myOp) : list (list myOp) :=
  match xs with
  | [] => [[x]]
  | y :: tl =>
      (x :: y :: tl) :: map (fun zs => y :: zs) (insert_all x tl)
  end.

Fixpoint permutations (xs : list myOp) : list (list myOp) :=
  match xs with
  | [] => [[]]
  | x :: tl => concat (map (insert_all x) (permutations tl))
  end.


(* ---------------- Check if an order respects hp ---------------- *)

(* "order respects hp" iff there is no edge from a later op to an earlier op.
   Equivalent: for each x, no y in the suffix has hp y x = true. *)

Fixpoint respects_hp (hp : hb_relation) (order : list myOp) : bool :=
  match order with
  | [] => true
  | x :: tl =>
      let ok_x := forallb (fun y => negb (hp y x)) tl in
      andb ok_x (respects_hp hp tl)
  end.
(* ---------------- Return at most k valid schedules ---------------- *)

Definition topo_orders_k
  (hp : hb_relation)
  (nodes : list myOp)
  (k : nat)
  : list (list myOp) :=
  let perms := permutations nodes in
  let good  := filter (respects_hp hp) perms in
  firstn k good.

Definition seq_from_order (order : list myOp) : seq_relation :=
  fun o => index_of_myOp o order.


(*  seq <- gen_seq(S,hp) *)

Definition gen_seq_many
  (Kseq : nat)
  (schedule_index : nat)
  (hp : hb_relation)
  (os : op_list)
  : seq_relation :=
  let schedules := topo_orders_k hp os Kseq in
  let n := length schedules in
  match n with
  | 0 => fun _ => 0
  | _ =>
      let idx := Nat.modulo schedule_index n in
      let order := nth_default ([] : list myOp) schedules idx in
      seq_from_order order
  end.

(* ------------------------------------------------------------------------- *)
(* Membrane ids from config                                                   *)
(* ------------------------------------------------------------------------- *)

Definition default_mid : membrane_id := 0%nat.

Definition first_mid (cfg : config) : membrane_id :=
  match cfg with
  | [] => default_mid
  | Memb l _ :: _ => l
  | LockMemb l _ _ :: _ => l
  end.

Definition mem_count (cfg : config) : nat :=
  length cfg.

Definition nth_mid_default (cfg : config) (i : nat) : membrane_id :=
  match cfg with
  | [] => default_mid
  | _ =>
      match nth_error cfg i with
      | Some (Memb l _) => l
      | Some (LockMemb l _ _) => l
      | None => first_mid cfg
      end
  end.


(* ------------------------------------------------------------------------- *)
(* A total “hash” for exp (for deterministic membrane choice tables)          *)
(* ------------------------------------------------------------------------- *)


Fixpoint sum_vars (xs : list var) : nat :=
  match xs with
  | [] => 0
  | x :: tl => x + sum_vars tl
  end.

Definition myOp_tag (o : myOp) : nat :=
  match o with
  | OpAP a =>
      match a with
      | CNew _ _ => 1
      | CAppU _ _ => 2
      | CMeas _ _ => 3
      end
  | OpDP a =>
      match a with
      | NewCh _ _ => 4
      | Send _ _  => 5
      | Recv _ _  => 6
      end
  | OpIf _ _ _ => 7
  end.

(* Hash for myOp *)
Definition myOp_hash (o : myOp) : nat :=
  myOp_tag o + sum_vars (vars_of_myOp o).

(* ------------------------------------------------------------------------- *)
(*                        gen_mem                                           *)
(* ------------------------------------------------------------------------- *)
Definition subset_vars (xs ys : list var) : bool :=
  forallb (fun x => mem_var x ys) xs.

Definition overlap_big (xs ys : list var) : bool :=
  let xs' := uniq xs in
  let ys' := uniq ys in
  let inter := length (intersect xs' ys') in
  let denom := Nat.max 1 (Nat.max (length xs') (length ys')) in
  Nat.leb (Nat.div denom 2) inter. (* >= half overlap *)

Fixpoint insert_by_seq (seq : seq_relation) (op : myOp) (ops : list myOp) : list myOp :=
  match ops with
  | [] => [op]
  | x :: tl =>
      if Nat.leb (seq op) (seq x) then op :: x :: tl
      else x :: insert_by_seq seq op tl
  end.

Fixpoint sort_by_seq (seq : seq_relation) (ops : list myOp) : list myOp :=
  match ops with
  | [] => []
  | x :: tl => insert_by_seq seq x (sort_by_seq seq tl)
  end.

Definition order_by_seq (seq : seq_relation) (ops : op_list) : op_list :=
  sort_by_seq seq ops.

Definition choose_mid (cfg : config) (seed k : nat) : membrane_id :=
  let m := mem_count cfg in
  let idx :=
    match m with
    | 0 => 0
    | S m' => Nat.modulo (k + seed) (S m')
    end
  in nth_mid_default cfg idx.

Fixpoint build_moO
  (cfg : config) (seed : nat) (ops_sorted : list myOp)
  (prev : option (myOp * membrane_id))
  (tbl : list (nat * membrane_id)) : list (nat * membrane_id) :=
  match ops_sorted with
  | [] => tbl
  | op :: tl =>
      let mid :=
        match prev with
        | None => choose_mid cfg seed (myOp_hash op)
        | Some (op_prev, mid_prev) =>
            let vars := uniq (vars_of_myOp op) in
            let vars_prev := uniq (vars_of_myOp op_prev) in
            if orb (subset_vars vars vars_prev) (overlap_big vars vars_prev)
            then mid_prev
            else choose_mid cfg seed (myOp_hash op)
        end
      in
      build_moO cfg seed tl (Some (op, mid)) ((myOp_hash op, mid) :: tbl)
  end.

Fixpoint lookup_mid (h : nat) (tbl : list (nat * membrane_id)) : membrane_id :=
  match tbl with
  | [] => default_mid
  | (k,v) :: tl => if Nat.eqb k h then v else lookup_mid h tl
  end.

Definition moO_of_tbl (tbl : list (nat * membrane_id)) : op_mem_assign :=
  fun op => lookup_mid (myOp_hash op) tbl.

Fixpoint first_use_mid
  (ops_sorted : list myOp) (moO : op_mem_assign) (q : var) : membrane_id :=
  match ops_sorted with
  | [] => default_mid
  | op :: tl =>
      if mem_var q (vars_of_myOp op) then moO op else first_use_mid tl moO q
  end.

Definition gen_mem_seed
  (seed : nat)
  (cfg  : config)
  (seq  : seq_relation)
  (os   : op_list)
  : op_mem_assign * qubit_mem_assign :=
  let ops_sorted := order_by_seq seq os in
  let moO_tbl := build_moO cfg seed ops_sorted None [] in
  let moO := moO_of_tbl moO_tbl in
  let moQ : qubit_mem_assign := fun q => first_use_mid ops_sorted moO q in
  (moO, moQ).


(* ------------------------------------------------------------------------- *)
(*                              gen_prog                             *)
(* ------------------------------------------------------------------------- *)
Definition mk_reloc (src dst : membrane_id) : exp :=
  SKIP src (Num dst).

(* Convert a myOp into a process we can store in a membrane *)
Definition myOp_to_process (op : myOp) : process :=
  match op with
  | OpAP a => AP a PNil
  | OpDP a => DP a PNil
  | OpIf b p q => PIf b p q
  end.

(* Relocation step is encoded as a local action that applies SKIP src (Num dst) *)
Definition reloc_process (src dst : membrane_id) : process :=
  AP (CAppU ([] : locus) (mk_reloc src dst)) PNil.

Fixpoint place_operation (cfg : config) (mid : membrane_id) (op : myOp) : config :=
  match cfg with
  | [] => [Memb mid [myOp_to_process op]]
  | (Memb l ps) :: tl =>
      if var_eqb l mid
      then Memb l (ps ++ [myOp_to_process op]) :: tl
      else Memb l ps :: place_operation tl mid op
  | (LockMemb l r ps) :: tl =>
      if var_eqb l mid
      then LockMemb l r (ps ++ [myOp_to_process op]) :: tl
      else LockMemb l r ps :: place_operation tl mid op
  end.

Fixpoint place_reloc (cfg : config) (mid : membrane_id) (src dst : membrane_id) : config :=
  match cfg with
  | [] => [Memb mid [reloc_process src dst]]
  | (Memb l ps) :: tl =>
      if var_eqb l mid
      then Memb l (ps ++ [reloc_process src dst]) :: tl
      else Memb l ps :: place_reloc tl mid src dst
  | (LockMemb l r ps) :: tl =>
      if var_eqb l mid
      then LockMemb l r (ps ++ [reloc_process src dst]) :: tl
      else LockMemb l r ps :: place_reloc tl mid src dst
  end.

Definition qloc_tbl : Type := list (var * membrane_id).

Fixpoint qloc_lookup (q : var) (tbl : qloc_tbl) (d : membrane_id) : membrane_id :=
  match tbl with
  | [] => d
  | (k,v) :: tl => if var_eqb k q then v else qloc_lookup q tl d
  end.

Fixpoint qloc_update (q : var) (mid : membrane_id) (tbl : qloc_tbl) : qloc_tbl :=
  match tbl with
  | [] => [(q, mid)]
  | (k,v) :: tl =>
      if var_eqb k q then (k, mid) :: tl else (k, v) :: qloc_update q mid tl
  end.

Fixpoint init_qloc (qs : list var) (moQ : qubit_mem_assign) : qloc_tbl :=
  match qs with
  | [] => []
  | q :: tl => (q, moQ q) :: init_qloc tl moQ
  end.

Fixpoint all_qubits (ops : list myOp) : list var :=
  match ops with
  | [] => []
  | op :: tl => vars_of_myOp op ++ all_qubits tl
  end.

Fixpoint ensure_qubits
  (qs : list var) (target : membrane_id) (qloc : qloc_tbl) (acc : config)
  : (qloc_tbl * config) :=
  match qs with
  | [] => (qloc, acc)
  | q :: tl =>
      let cur := qloc_lookup q qloc default_mid in
      if var_eqb cur target
      then ensure_qubits tl target qloc acc
      else
        let acc'  := place_reloc acc target cur target in
        let qloc' := qloc_update q target qloc in
        ensure_qubits tl target qloc' acc'
  end.

Fixpoint gen_prog_core
  (moO : op_mem_assign) (moQ : qubit_mem_assign)
  (ops_sorted : list myOp)
  (qloc : qloc_tbl)
  (acc  : config) : config :=
  match ops_sorted with
  | [] => acc
  | op :: tl =>
      let target := moO op in
      let qs := uniq (vars_of_myOp op) in
      let '(qloc1, acc1) := ensure_qubits qs target qloc acc in
      let acc2 := place_operation acc1 target op in
      gen_prog_core moO moQ tl qloc1 acc2
  end.

Definition gen_prog
  (seq : seq_relation) (moO : op_mem_assign) (moQ : qubit_mem_assign) (os : op_list)
  : distributed_prog :=
  let ops_sorted := order_by_seq seq os in
  let qs := uniq (all_qubits ops_sorted) in
  let qloc0 := init_qloc qs moQ in
  gen_prog_core moO moQ ops_sorted qloc0 [].




(* ------------------------------------------------------------------------- *)
(* fit: relocation-aware cost                                         *)
(* ------------------------------------------------------------------------- *)

Fixpoint count_comm_proc (p : process) : nat :=
  match p with
  | PNil => 0
  | AP _ p' => count_comm_proc p'
  | DP d p' =>
      match d with
      | Send _ _ => S (count_comm_proc p')
      | Recv _ _ => S (count_comm_proc p')
      | _ => count_comm_proc p'
      end
  | PIf _ p1 p2 => count_comm_proc p1 + count_comm_proc p2
  end.

Fixpoint count_comm_cfg (cfg : config) : nat :=
  match cfg with
  | [] => 0
  | Memb _ ps :: tl =>
      fold_right (fun p acc => count_comm_proc p + acc) 0 ps + count_comm_cfg tl
  | LockMemb _ _ ps :: tl =>
      fold_right (fun p acc => count_comm_proc p + acc) 0 ps + count_comm_cfg tl
  end.

Definition fit (P : distributed_prog) : fitness_value :=
  count_comm_cfg P.

Definition INF_SCORE : fitness_value := Nat.pow 10 9.

(* ============================================================ *)
(*      S-loop encoding                                   *)
(* ============================================================ *)

Definition case : Type := (nat * nat)%type.  (* (schedule_index, mem_seed) *)

Definition case_eqb (c d : case) : bool :=
  andb (Nat.eqb (fst c) (fst d)) (Nat.eqb (snd c) (snd d)).

Fixpoint mem_case (c : case) (cs : list case) : bool :=
  match cs with
  | [] => false
  | d :: tl => if case_eqb c d then true else mem_case c tl
  end.


(* ------------------------------------------------------------ *)
(* Finite universe of cases (schedule_index × mem_seed)        *)
(* ------------------------------------------------------------ *)

Fixpoint range_from (start count : nat) : list nat :=
  match count with
  | 0 => []
  | S k => start :: range_from (S start) k
  end.

Definition mk_cases (Kseq Kmem : nat) : list case :=
  let scheds := range_from 0 Kseq in
  let seeds  := range_from 0 Kmem in
  concat (map (fun si => map (fun sd => (si, sd)) seeds) scheds).

(* Keep only cases not already in S *)
Fixpoint filter_fresh (all : list case) (seen : list case) : list case :=
  match all with
  | [] => []
  | c :: tl =>
      if mem_case c seen then filter_fresh tl seen
      else c :: filter_fresh tl seen
  end.
(* candidate element stores: id + the actual functions (seq, mo) *)
Definition candidate : Type :=
  (case * (seq_relation * (op_mem_assign * qubit_mem_assign)))%type.

Definition seen_cases (S : list candidate) : list case :=
  map fst S.

(* are_still_cases(S) *)
Definition are_still_cases_cases (seen : list case) (ALL : list case) : bool :=
  match filter_fresh ALL seen with
  | [] => false
  | _  => true
  end.

Definition pick_case (S : list case) (ALL : list case) : option case :=
  match filter_fresh ALL S with
  | [] => None
  | c :: _ => Some c
  end.

(* gen_seq(S,hp) *)
Definition gen_seq
  (Kseq : nat)
  (hp   : hb_relation)
  (os   : op_list)
  (ALL  : list case)
  (S    : list candidate)
  : option (case * seq_relation) :=
  match pick_case (seen_cases S) ALL with
  | None => None
  | Some c =>
      let sched_i := fst c in
      let seq := gen_seq_many Kseq sched_i hp os in
      Some (c, seq)
  end.

(* gen_mem(S,L,seq) *)
Definition gen_mem
  (cfg  : config)  
  (seq  : seq_relation)
  (os   : op_list)
  (c    : case)     
  : op_mem_assign * qubit_mem_assign :=
  let seed := snd c in
  gen_mem_seed seed cfg seq os.



Definition Smap : Type := list (var * membrane_id).
Definition locus_myOp (op : myOp) : list var := vars_of_myOp op.

Definition diff_mem
  (mo_cur : var -> membrane_id)
  (qs : list var)
  (l  : membrane_id)
  : Smap :=
  fold_right
    (fun q acc =>
       let src := mo_cur q in
       if var_eqb src l then acc else (q, src) :: acc)
    [] qs.

Fixpoint mem_up_smap
  (mo_cur : var -> membrane_id)
  (S : Smap)
  (l : membrane_id)
  : var -> membrane_id :=
  match S with
  | [] => mo_cur
  | (q,_) :: tl =>
      let mo_cur' := fun x => if var_eqb x q then l else mo_cur x in
      mem_up_smap mo_cur' tl l
  end.

Fixpoint insert_send_recv
  (P : config)
  (Sp : Smap)
  (l  : membrane_id)
  (name : nat)
  : config * nat :=
  match Sp with
  | [] => (P, name)
  | (q, src) :: tl =>
      let c     : var := name in
      let alias : var := name + 1 in
      let P0 := place_operation P src (OpDP (NewCh c 1)) in
      let P1 := place_operation P0 src (OpDP (Send c (BA q))) in
      let P2 := place_operation P1 l (OpDP (Recv c alias)) in
      insert_send_recv P2 tl l (name + 2)
  end.


Fixpoint mem_up (mo_cur : qubit_mem_assign) (qs : list var) (l : membrane_id) : qubit_mem_assign :=
  match qs with
  | [] => mo_cur
  | q :: qs' =>
      let mo_cur' := fun x => if Nat.eqb x q then l else mo_cur x in
      mem_up mo_cur' qs' l
  end.

Definition place
  (P    : config)
  (op   : myOp)
  (l    : membrane_id)
  (name : nat)
  : config :=
  place_operation P l op.

Fixpoint gen_prog_loop_alg2
  (seq    : list myOp)
  (mo_cur : var -> membrane_id)
  (moO    : myOp -> membrane_id)
  (P      : config)
  (name   : nat)
  : config :=
  match seq with
  | [] => P
  | op :: seq' =>
      let l : membrane_id := moO op in
      let S : Smap := diff_mem mo_cur (locus_myOp op) l in

      let '(P1, name1) :=
        match S with
        | [] => (P, name)
        | _  => insert_send_recv P S l name
        end in

      let mo_cur' : var -> membrane_id := mem_up_smap mo_cur S l in
      let P2 : config := place P1 op l name1 in
      gen_prog_loop_alg2 seq' mo_cur' moO P2 name1
  end.

Definition empty_config : config := [].

Definition gen_prog_alg2
  (seq : list myOp)
  (moQ : var -> membrane_id)
  (moO : myOp -> membrane_id)
  : config :=
  gen_prog_loop_alg2 seq moQ moO empty_config 0.

Definition gen_prog_paper
  (seq : seq_relation)
  (moQ : qubit_mem_assign)
  (moO : op_mem_assign)
  (os  : op_list)
  : distributed_prog :=
  let ops_sorted : list myOp := order_by_seq seq os in
  gen_prog_alg2 ops_sorted moQ moO.

(*  while-loop:
   S ← ∅
   while are_still_cases(S) do ... S ← {(seq,mo)} ∪ S *)
Fixpoint auto_disq_loop
  (Kseq : nat)
  (hp   : hb_relation)
  (os   : op_list)
  (cfg  : config)
  (ALL  : list case)
  (S    : list candidate)
  (Qbest: distributed_prog)
  (zmin : fitness_value)
  (fuel : nat)
  : distributed_prog :=
  match fuel with
  | 0 => Qbest
  | S fuel' =>
      if are_still_cases_cases (seen_cases S) ALL then
        match gen_seq Kseq hp os ALL S with
        | None => Qbest
        | Some (c, seq) =>
            let '(moO, moQ) := gen_mem cfg seq os c in
            let P := gen_prog_paper seq moQ moO os in
            let z := fit P in
            let S' : list candidate := (c, (seq, (moO, moQ))) :: S in
            if Nat.ltb z zmin
            then auto_disq_loop Kseq hp os cfg ALL S' P z fuel'
            else auto_disq_loop Kseq hp os cfg ALL S' Qbest zmin fuel'
        end
      else
        Qbest
  end.

Definition auto_disq_alg1_paper
  (Kseq : nat)
  (Kmem : nat)
  (R    : op_list)
  (cfg  : config)
  : distributed_prog :=
  let hp := gen_hp R in
  let os := gen_os R in
  let ALL := mk_cases Kseq Kmem in
  (* S ← ∅ *)
  auto_disq_loop Kseq hp os cfg ALL [] ([] : config) INF_SCORE (length ALL).



Fixpoint mem_op (eqb : myOp -> myOp -> bool) (x : myOp) (xs : list myOp) : bool :=
  match xs with
  | [] => false
  | y :: tl => if eqb x y then true else mem_op eqb x tl
  end.

Fixpoint uniq_ops (eqb : myOp -> myOp -> bool) (xs : list myOp) : list myOp :=
  match xs with
  | [] => []
  | x :: tl => if mem_op eqb x tl then uniq_ops eqb tl else x :: uniq_ops eqb tl
  end.

Fixpoint remove_ops (eqb : myOp -> myOp -> bool) (xs rem : list myOp) : list myOp :=
  match xs with
  | [] => []
  | x :: tl => if mem_op eqb x rem then remove_ops eqb tl rem else x :: remove_ops eqb tl rem
  end.

Definition opt_hp (hp_l : hb_relation) (seq_l : seq_relation) : hb_relation :=
  fun a b => andb (hp_l a b) (Nat.ltb (seq_l a) (seq_l b)).

Definition succs (hp : hb_relation) (nodes : list myOp) (x : myOp) : list myOp :=
  filter (fun y => hp x y) nodes.

Fixpoint reachable_fuel
  (eqb : myOp -> myOp -> bool)
  (hp : hb_relation)
  (nodes : list myOp)
  (fuel : nat)
  (seen : list myOp)
  (x target : myOp) : bool :=
  if eqb x target then true else
  match fuel with
  | 0 => false
  | S fuel' =>
      if mem_op eqb x seen then false
      else
        let seen' := x :: seen in
        existsb (fun y => reachable_fuel eqb hp nodes fuel' seen' y target)
                (succs hp nodes x)
  end.

Definition reachable
  (eqb : myOp -> myOp -> bool)
  (hp : hb_relation)
  (nodes : list myOp)
  (x y : myOp) : bool :=
  reachable_fuel eqb hp nodes (length nodes) [] x y.

Definition scc_of
  (eqb : myOp -> myOp -> bool)
  (hp : hb_relation)
  (nodes : list myOp)
  (x : myOp) : list myOp :=
  filter
    (fun y =>
       andb (reachable eqb hp nodes x y)
            (reachable eqb hp nodes y x))
    nodes.

Fixpoint scc_partition_fuel
  (fuel : nat)
  (eqb  : myOp -> myOp -> bool)
  (hp   : hb_relation)
  (nodes : list myOp)
  : list (list myOp) :=
  match fuel with
  | 0 => []  
  | S fuel' =>
      match nodes with
      | [] => []
      | x :: _ =>
          let comp := scc_of eqb hp nodes x in
          let rest := remove_ops eqb nodes comp in
          comp :: scc_partition_fuel fuel' eqb hp rest
      end
  end.

Definition scc_partition
  (eqb  : myOp -> myOp -> bool)
  (hp   : hb_relation)
  (nodes : list myOp)
  : list (list myOp) :=
  scc_partition_fuel (length nodes) eqb hp nodes.

Definition gen_ops (seq_l : seq_relation) (sbar : list myOp) : list process :=
  map myOp_to_process (sort_by_seq seq_l sbar).

Fixpoint alg3_loop
  (seq_l : seq_relation)
  (S     : list (list myOp))
  (Rbar  : list process)
  : list process :=
  match S with
  | [] =>
      Rbar
  | sbar :: S' =>
      let R := gen_ops seq_l sbar in
      let Rbar' := Rbar ++ R in
      alg3_loop seq_l S' Rbar'
  end.


Definition auto_parallelize_alg3
  (eqb  : myOp -> myOp -> bool)   
  (ops_l : list myOp)            
  (hp_l  : hb_relation)
  (seq_l : seq_relation)
  : list process :=
  let hp_l' := opt_hp hp_l seq_l in  
  let S := scc_partition eqb hp_l' (uniq_ops eqb ops_l) in  
  alg3_loop seq_l S ([] : list process).



Definition cfg1 : config := [Memb 0 []; Memb 1 []].

Definition op1 : myOp := OpAP (CNew 0 1).
Definition op2 : myOp := OpAP (CMeas 0 ([] : locus)).
Definition R1  : op_list := [op1; op2].

Definition P1 : distributed_prog :=
  auto_disq_alg1_paper 2 2 R1 cfg1.

Compute P1.

Compute fit P1.

Definition cfg_test : config := [Memb 0 []; Memb 1 []].

Definition S_empty : Smap := [].

Definition T1 :=
  insert_send_recv cfg_test S_empty 1 0.

Compute T1.

Definition S_one : Smap := [(0, 0)].

Definition T2 :=
  insert_send_recv cfg_test S_one 1 0.

Compute T2.


Definition S_two : Smap := [(0,0); (1,0)].
Definition T3 := insert_send_recv cfg_test S_two 1 0.
Compute T3.
Definition memb_procs (m : memb) : list process :=
  match m with
  | Memb _ ps => ps
  | LockMemb _ _ ps => ps
  end.

Fixpoint flatten_config (cfg : config) : list process :=
  match cfg with
  | [] => []
  | m :: tl => memb_procs m ++ flatten_config tl
  end.

Compute flatten_config (fst T2).
Definition opAP1 : myOp := OpAP (CNew 0 1).

Definition moQ0 : var -> membrane_id := fun _ => 0.
Definition moO_to_1 : myOp -> membrane_id := fun _ => 1.

Definition TB :=
  gen_prog_loop_alg2 ([opAP1] : list myOp) moQ0 moO_to_1 empty_config 0.

Compute TB.
Compute flatten_config TB.

Definition cond0 : cbexp := CEq (BA 0) (Num 0).

Definition p_then : process := AP (CNew 0 1) PNil.
Definition p_else : process := PNil.

Definition opIF1 : myOp := OpIf cond0 p_then p_else.

Definition TC :=
  gen_prog_loop_alg2 ((opIF1 :: nil) : list myOp) moQ0 moO_to_1 empty_config 0.


Compute TC.
Compute flatten_config TC.

Definition opAP2 : myOp := OpAP (CMeas 0 ([] : locus)).
Definition seq2 : list myOp := [opAP1; opAP2].

Definition TD :=
  gen_prog_alg2 seq2 moQ0 moO_to_1.

Compute TD.
Compute flatten_config TD.
Compute diff_mem moQ0 (locus_myOp opAP1) 1.
Compute diff_mem (mem_up_smap moQ0 (diff_mem moQ0 (locus_myOp opAP1) 1) 1)
                (locus_myOp opAP2) 1.



