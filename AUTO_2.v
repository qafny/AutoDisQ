
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
Definition candidate : Type :=
  (seq_relation * (op_mem_assign * qubit_mem_assign))%type.

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
(*                       hp <- gen_hp(R)                                  *)
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

Definition is_reloc (e : exp) : bool :=
  match e with
  | SKIP _ (Num _) => true
  | _ => false
  end.

Definition reloc_pair (e : exp) : (membrane_id * membrane_id) :=
  match e with
  | SKIP a (Num b) => (a, b)
  | _ => (0, 0)
  end.

Fixpoint mem_pair (p : membrane_id * membrane_id) (ps : list (membrane_id * membrane_id)) : bool :=
  match ps with
  | [] => false
  | q :: tl =>
      if andb (var_eqb (fst p) (fst q)) (var_eqb (snd p) (snd q))
      then true else mem_pair p tl
  end.

Fixpoint uniq_pairs (ps : list (membrane_id * membrane_id)) : list (membrane_id * membrane_id) :=
  match ps with
  | [] => []
  | p :: tl => if mem_pair p tl then uniq_pairs tl else p :: uniq_pairs tl
  end.

(* Extract all exp that appear in local actions CAppU inside a process *)
Fixpoint extract_exps_from_proc (p : process) : list exp :=
  match p with
  | PNil => []
  | AP a p' =>
      match a with
      | CAppU _ e => e :: extract_exps_from_proc p'
      | _ => extract_exps_from_proc p'
      end
  | DP _ p' => extract_exps_from_proc p'
  | PIf _ p1 p2 => extract_exps_from_proc p1 ++ extract_exps_from_proc p2
  end.

Fixpoint extract_all_exps (cfg : config) : list exp :=
  match cfg with
  | [] => []
  | Memb _ ps :: tl =>
      concat (map extract_exps_from_proc ps) ++ extract_all_exps tl
  | LockMemb _ _ ps :: tl =>
      concat (map extract_exps_from_proc ps) ++ extract_all_exps tl
  end.

Fixpoint count_relocs (es : list exp) : nat :=
  match es with
  | [] => 0
  | e :: tl => (if is_reloc e then 1 else 0) + count_relocs tl
  end.

Fixpoint collect_pairs (es : list exp) : list (membrane_id * membrane_id) :=
  match es with
  | [] => []
  | e :: tl =>
      if is_reloc e then reloc_pair e :: collect_pairs tl else collect_pairs tl
  end.

Definition fit (P : distributed_prog) : fitness_value :=
  let es := extract_all_exps P in
  let reloc := count_relocs es in
  let pairs := length (uniq_pairs (collect_pairs es)) in
  reloc + 5 * pairs.


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

(* are_still_cases(S) *)
Definition are_still_cases (S : list case) (ALL : list case) : bool :=
  match filter_fresh ALL S with
  | [] => false
  | _  => true
  end.


Definition pick_case (S : list case) (ALL : list case) : option case :=
  match filter_fresh ALL S with
  | [] => None
  | c :: _ => Some c
  end.

(* gen_seq(S,hp) *)
Definition gen_seq_paper
  (Kseq : nat)
  (hp   : hb_relation)
  (os   : op_list)
  (S    : list case)
  (ALL  : list case)
  : option (case * seq_relation) :=
  match pick_case S ALL with
  | None => None
  | Some c =>
      let sched_i := fst c in
      let seq := gen_seq_many Kseq sched_i hp os in
      Some (c, seq)
  end.

(* gen_mem(S,L,seq) *)
Definition gen_mem_paper
  (cfg  : config)   (* L in the paper: available membranes *)
  (seq  : seq_relation)
  (os   : op_list)
  (c    : case)
  : op_mem_assign * qubit_mem_assign :=
  let seed := snd c in
  gen_mem_seed seed cfg seq os.


(*  while-loop:
   S ← ∅
   while are_still_cases(S) do ... S ← {(seq,mo)} ∪ S *)

Fixpoint auto_disq_loop_paper
  (Kseq : nat)
  (hp   : hb_relation)
  (os   : op_list)
  (cfg  : config)
  (ALL  : list case)          
  (Sseen: list case)          
  (Qbest: distributed_prog)
  (zmin : fitness_value)
  (fuel : nat)               
  : distributed_prog :=
  match fuel with
  | 0 => Qbest
  | S fuel' =>
      match gen_seq_paper Kseq hp os Sseen ALL with
      | None => Qbest
      | Some (c, seq) =>
         
          if are_still_cases Sseen ALL then
            let '(moO, moQ) := gen_mem_paper cfg seq os c in
            let P := gen_prog seq moO moQ os in
            let z := fit P in
            let Sseen' := c :: Sseen in
            if Nat.ltb z zmin
            then auto_disq_loop_paper Kseq hp os cfg ALL Sseen' P z fuel'
            else auto_disq_loop_paper Kseq hp os cfg ALL Sseen' Qbest zmin fuel'
          else Qbest
      end
  end.

(* Full Algorithm 1 *)

Definition auto_disq_alg1_paper
  (Kseq : nat)
  (Kmem : nat)
  (R    : op_list)
  (cfg  : config)
  : distributed_prog :=
  let hp := gen_hp R in
  let os := gen_os R in
  let ALL := mk_cases Kseq Kmem in
  auto_disq_loop_paper Kseq hp os cfg ALL [] ([] : config) INF_SCORE (length ALL).







(*
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
            let P := gen_prog seq moO moQ os in
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
*)












































From Coq Require Import List Arith Bool Nat.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DisQ.BasicUtility.   (* var := nat *)
Require Import DisQ.DisQSyntax.     (* exp, process, memb, config, ... *)

Definition membrane    : Type := memb.
Definition membranes   : Type := config.
Definition membrane_id : Type := var.

Definition hb_relation : Type := exp -> exp -> bool.

Definition op_list     : Type := list exp.

Definition rank         : Type := nat.
Definition seq_relation : Type := exp -> rank.

Definition op_mem_assign    : Type := exp -> membrane_id.
Definition qubit_mem_assign : Type := var -> membrane_id.

Definition fitness_value    : Type := nat.
Definition distributed_prog : Type := config.

Definition candidate : Type :=
  (seq_relation * (op_mem_assign * qubit_mem_assign))%type.

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

(* ------------------------------------------------------------------------- *)
(*                        exp equality                                      *)
(* ------------------------------------------------------------------------- *)

Scheme Equality for exp.

Definition exp_eqb (a b : exp) : bool :=
  if exp_beq a b then true else false.

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
(*                          os <- gen_os(R)                                  *)                                        
(* ------------------------------------------------------------------------- *)
Definition gen_os (R : op_list) : op_list := R.

(* ------------------------------------------------------------------------- *)
(*                          hp <- gen_hp(R)                                  *)
(* ------------------------------------------------------------------------- *)

Fixpoint index_of_exp (x : exp) (xs : list exp) : nat :=
  match xs with
  | [] => 0
  | y :: tl => if exp_eqb x y then 0 else S (index_of_exp x tl)
  end.

Definition gen_hp (R : op_list) : hb_relation :=
  fun e1 e2 =>
    let i := index_of_exp e1 R in
    let j := index_of_exp e2 R in
    andb (Nat.ltb i j) (share_qubit e1 e2).

(* ------------------------------------------------------------------------- *)
(*                          MANY schedules                                   *)
(* ------------------------------------------------------------------------- *)

Definition has_incoming_from (hp : hb_relation) (nodes : list exp) (x : exp) : bool :=
  existsb (fun y => hp y x) nodes.

Definition available (hp : hb_relation) (nodes : list exp) : list exp :=
  filter (fun x => negb (has_incoming_from hp nodes x)) nodes.

Fixpoint nth_default {A} (d : A) (xs : list A) (n : nat) : A :=
  match xs, n with
  | [], _ => d
  | x :: _, 0 => x
  | _ :: tl, S n' => nth_default d tl n'
  end.


(* ---------------- Permutations  ---------------- *)

Fixpoint insert_all (x : exp) (xs : list exp) : list (list exp) :=
  match xs with
  | [] => [[x]]
  | y :: tl =>
      (x :: y :: tl) :: map (fun zs => y :: zs) (insert_all x tl)
  end.

Fixpoint permutations (xs : list exp) : list (list exp) :=
  match xs with
  | [] => [[]]
  | x :: tl => concat (map (insert_all x) (permutations tl))
  end.

(* ---------------- Check if an order respects hp ---------------- *)

Fixpoint respects_hp (hp : hb_relation) (order : list exp) : bool :=
  match order with
  | [] => true
  | x :: tl =>
      let ok_x := forallb (fun y => negb (hp y x)) tl in
      andb ok_x (respects_hp hp tl)
  end.

(* ---------------- Return at most k valid schedules ---------------- *)

Definition topo_orders_k (hp : hb_relation) (nodes : list exp) (k : nat)
  : list (list exp) :=
  let perms := permutations nodes in
  let good  := filter (respects_hp hp) perms in
  firstn k good.

Definition seq_from_order (order : list exp) : seq_relation :=
  fun e => index_of_exp e order.

(* Paper line 9: seq <- gen_seq(S,hp)
   Here we pick different valid schedules by taking schedule_index mod #schedules. *)

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
      let order := nth_default ([] : list exp) schedules idx in
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

Definition mem_count (cfg : config) : nat := length cfg.

Definition nth_mid_default (cfg : config) (i : nat) : membrane_id :=
  match nth_error cfg i with
  | Some (Memb l _) => l
  | Some (LockMemb l _ _) => l
  | None => first_mid cfg
  end.

Fixpoint exp_tag (e : exp) : nat :=
  match e with
  | SKIP _ _ => 1
  | X _ _ => 2
  | CU _ _ e1 => 3 + exp_tag e1
  | RZ q _ _ => 10 + q
  | RRZ q _ _ => 20 + q
  | SR q _ => 30 + q
  | SRR q _ => 40 + q
  | QFT _ b => 50 + b
  | RQFT _ b => 60 + b
  | H _ _ => 70
  | Addto _ _ => 80
  | Seq e1 e2 => 90 + exp_tag e1 + exp_tag e2
  end.

Fixpoint sum_vars (xs : list var) : nat :=
  match xs with
  | [] => 0
  | x :: tl => x + sum_vars tl
  end.

Definition exp_hash (e : exp) : nat :=
  exp_tag e + sum_vars (vars_of_exp e).

(* ------------------------------------------------------------------------- *)
(* gen_mem: parameterized by seed so different candidates differ              *)
(* ------------------------------------------------------------------------- *)

Definition subset_vars (xs ys : list var) : bool :=
  forallb (fun x => mem_var x ys) xs.

Definition overlap_big (xs ys : list var) : bool :=
  let xs' := uniq xs in
  let ys' := uniq ys in
  let inter := length (intersect xs' ys') in
  let denom := Nat.max 1 (Nat.max (length xs') (length ys')) in
  Nat.leb (Nat.div denom 2) inter. (* >= half overlap *)

Fixpoint insert_by_seq (seq : seq_relation) (op : exp) (ops : list exp) : list exp :=
  match ops with
  | [] => [op]
  | x :: tl =>
      if Nat.leb (seq op) (seq x) then op :: x :: tl
      else x :: insert_by_seq seq op tl
  end.

Fixpoint sort_by_seq (seq : seq_relation) (ops : list exp) : list exp :=
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
  (cfg : config) (seed : nat) (ops_sorted : list exp)
  (prev : option (exp * membrane_id))
  (tbl : list (nat * membrane_id)) : list (nat * membrane_id) :=
  match ops_sorted with
  | [] => tbl
  | op :: tl =>
      let mid :=
        match prev with
        | None => choose_mid cfg seed (exp_hash op)
        | Some (op_prev, mid_prev) =>
            let vars := uniq (vars_of_exp op) in
            let vars_prev := uniq (vars_of_exp op_prev) in
            if orb (subset_vars vars vars_prev) (overlap_big vars vars_prev)
            then mid_prev
            else choose_mid cfg seed (exp_hash op)
        end
      in
      build_moO cfg seed tl (Some (op, mid)) ((exp_hash op, mid) :: tbl)
  end.

Fixpoint lookup_mid (h : nat) (tbl : list (nat * membrane_id)) : membrane_id :=
  match tbl with
  | [] => default_mid
  | (k,v) :: tl => if Nat.eqb k h then v else lookup_mid h tl
  end.

Definition moO_of_tbl (tbl : list (nat * membrane_id)) : op_mem_assign :=
  fun op => lookup_mid (exp_hash op) tbl.

Fixpoint first_use_mid
  (ops_sorted : list exp) (moO : op_mem_assign) (q : var) : membrane_id :=
  match ops_sorted with
  | [] => default_mid
  | op :: tl =>
      if mem_var q (vars_of_exp op) then moO op else first_use_mid tl moO q
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
(*                          gen_prog                                         *)
(* ------------------------------------------------------------------------- *)

Definition mk_reloc (src dst : membrane_id) : exp :=
  SKIP src (Num dst).

Definition op_to_process (op : exp) : process :=
  AP (CAppU ([] : locus) op) PNil.

Fixpoint place_operation (cfg : config) (mid : membrane_id) (op : exp) : config :=
  match cfg with
  | [] => [Memb mid [op_to_process op]]
  | (Memb l ps) :: tl =>
      if var_eqb l mid
      then Memb l (ps ++ [op_to_process op]) :: tl
      else Memb l ps :: place_operation tl mid op
  | (LockMemb l r ps) :: tl =>
      if var_eqb l mid
      then LockMemb l r (ps ++ [op_to_process op]) :: tl
      else LockMemb l r ps :: place_operation tl mid op
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

Fixpoint all_qubits (ops : list exp) : list var :=
  match ops with
  | [] => []
  | op :: tl => vars_of_exp op ++ all_qubits tl
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
        let acc' := place_operation acc target (mk_reloc cur target) in
        let qloc' := qloc_update q target qloc in
        ensure_qubits tl target qloc' acc'
  end.

Fixpoint gen_prog_core
  (moO : op_mem_assign) (moQ : qubit_mem_assign)
  (ops_sorted : list exp)
  (qloc : qloc_tbl)
  (acc  : config) : config :=
  match ops_sorted with
  | [] => acc
  | op :: tl =>
      let target := moO op in
      let qs := uniq (vars_of_exp op) in
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
(*             fit: relocation-aware cost                                    *)
(* ------------------------------------------------------------------------- *)

Definition is_reloc (e : exp) : bool :=
  match e with
  | SKIP _ (Num _) => true
  | _ => false
  end.

Definition reloc_pair (e : exp) : (membrane_id * membrane_id) :=
  match e with
  | SKIP a (Num b) => (a, b)
  | _ => (0, 0)
  end.

Fixpoint mem_pair (p : membrane_id * membrane_id) (ps : list (membrane_id * membrane_id)) : bool :=
  match ps with
  | [] => false
  | q :: tl =>
      if andb (var_eqb (fst p) (fst q)) (var_eqb (snd p) (snd q))
      then true else mem_pair p tl
  end.

Fixpoint uniq_pairs (ps : list (membrane_id * membrane_id)) : list (membrane_id * membrane_id) :=
  match ps with
  | [] => []
  | p :: tl => if mem_pair p tl then uniq_pairs tl else p :: uniq_pairs tl
  end.

Fixpoint extract_exps_from_proc (p : process) : list exp :=
  match p with
  | PNil => []
  | AP c tl =>
      match c with
      | CAppU _ e => e :: extract_exps_from_proc tl
      | _ => extract_exps_from_proc tl
      end
  | DP _ tl => extract_exps_from_proc tl
  | PIf _ p1 p2 => extract_exps_from_proc p1 ++ extract_exps_from_proc p2
  end.

Fixpoint extract_all_exps (cfg : config) : list exp :=
  match cfg with
  | [] => []
  | Memb _ ps :: tl =>
      (concat (map extract_exps_from_proc ps)) ++ extract_all_exps tl
  | LockMemb _ _ ps :: tl =>
      (concat (map extract_exps_from_proc ps)) ++ extract_all_exps tl
  end.

Fixpoint count_relocs (es : list exp) : nat :=
  match es with
  | [] => 0
  | e :: tl => (if is_reloc e then 1 else 0) + count_relocs tl
  end.

Fixpoint collect_pairs (es : list exp) : list (membrane_id * membrane_id) :=
  match es with
  | [] => []
  | e :: tl =>
      if is_reloc e then reloc_pair e :: collect_pairs tl else collect_pairs tl
  end.

Definition fit (P : distributed_prog) : fitness_value :=
  let es := extract_all_exps P in
  let reloc := count_relocs es in
  let pairs := length (uniq_pairs (collect_pairs es)) in
  reloc + 5 * pairs.


Definition INF_SCORE : fitness_value := Nat.pow 10 9.

(* ============================================================ *)
(*      S-loop encoding                                   *)
(* ============================================================ *)

(* A finite identifier for a candidate (seq,mo). *)

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

Fixpoint filter_fresh (all : list case) (seen : list case) : list case :=
  match all with
  | [] => []
  | c :: tl =>
      if mem_case c seen then filter_fresh tl seen
      else c :: filter_fresh tl seen
  end.

(* are_still_cases(S) *)
Definition are_still_cases (S : list case) (ALL : list case) : bool :=
  negb (Nat.eqb (length (filter_fresh ALL S)) 0).

(* gen_seq(S,hp) — pick a not-yet-seen case and build seq from it *)
Definition pick_case (S : list case) (ALL : list case) : option case :=
  match filter_fresh ALL S with
  | [] => None
  | c :: _ => Some c
  end.

Definition gen_seq_paper
  (Kseq : nat)
  (hp   : hb_relation)
  (os   : op_list)
  (S    : list case)
  (ALL  : list case)
  : option (case * seq_relation) :=
  match pick_case S ALL with
  | None => None
  | Some c =>
      let sched_i := fst c in
      let seq := gen_seq_many Kseq sched_i hp os in
      Some (c, seq)
  end.

(* gen_mem(S,L,seq) — use chosen case’s seed to build mo *)
Definition gen_mem_paper
  (cfg  : config)   (* this plays the role of L (available membranes) *)
  (seq  : seq_relation)
  (os   : op_list)
  (c    : case)
  : op_mem_assign * qubit_mem_assign :=
  let seed := snd c in
  gen_mem_seed seed cfg seq os.

(*  while-loop:
   S ← ∅
   while are_still_cases(S) do ... S ← {(seq,mo)} ∪ S *)
Fixpoint auto_disq_loop_paper
  (Kseq : nat)
  (hp   : hb_relation)
  (os   : op_list)
  (cfg  : config)
  (ALL  : list case)          (* finite set of possible cases *)
  (S    : list case)
  (Qbest: distributed_prog)
  (zmin : fitness_value)
  (fuel : nat)                (* only for Coq termination; set to |ALL| *)
  : distributed_prog :=
  match fuel with
  | 0 => Qbest
  | S fuel' =>
      if are_still_cases S ALL then
        match gen_seq_paper Kseq hp os S ALL with
        | None => Qbest
        | Some (c, seq) =>
            let '(moO, moQ) := gen_mem_paper cfg seq os c in
            let P := gen_prog seq moO moQ os in
            let z := fit P in
            let S' := c :: S in  (* S ← {(seq,mo)} ∪ S, represented by case id *)
            if Nat.ltb z zmin
            then auto_disq_loop_paper Kseq hp os cfg ALL S' P z fuel'
            else auto_disq_loop_paper Kseq hp os cfg ALL S' Qbest zmin fuel'
        end
      else Qbest
  end.

(* Full Algorithm 1  *)
Definition auto_disq_alg1_paper
  (Kseq : nat)
  (Kmem : nat)
  (R    : op_list)
  (cfg  : config)
  : distributed_prog :=
  let hp := gen_hp R in
  let os := gen_os R in
  let ALL := mk_cases Kseq Kmem in
  auto_disq_loop_paper Kseq hp os cfg ALL [] ([] : config) INF_SCORE (length ALL).





(* ExtractSingle.v — Algorithm 1 (paper-faithful, extractable, NO Parameters)
   Goal: match the *meaning* of the paper images:
   - hp is generated from qubit-dependencies (shared qubits) + list order (acyclic).
   - seq is a rank assignment consistent with hp, with Optimization #1 (fix ranks for
     “similar independent operations” by preserving their list order as tie-break).
   - gen_mem uses Optimization #2 (co-locate related operations with strong overlap /
     subset qubit-sets) and produces (moO, moQ).
   - Optimization #3: moQ assigns initial qubit locations based on *first use* in seq.
   - gen_prog uses moQ and inserts “relocation/communication” markers when an op’s
     qubits are not on the chosen membrane.
   - fit measures communication/relocation cost (not just #processes).
*)

From Coq Require Import List Arith Bool Nat.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DisQ.BasicUtility.   (* var := nat *)
Require Import DisQ.DisQSyntax.     (* exp, process, memb, config, locus, ... *)

(* ------------------------------------------------------------------------- *)
(* Types (as in the paper)                                                   *)
(* ------------------------------------------------------------------------- *)

Definition membrane    : Type := memb.
Definition membranes   : Type := config.
Definition membrane_id : Type := var.

Definition hb_relation : Type := exp -> exp -> bool.

Definition op_list     : Type := list exp.

Definition rank        : Type := nat.
Definition seq_relation: Type := exp -> rank.

Definition op_mem_assign    : Type := exp -> membrane_id.
Definition qubit_mem_assign : Type := var -> membrane_id.

Definition fitness_value    : Type := nat.
Definition distributed_prog : Type := config.

Definition candidate : Type :=
  (seq_relation * (op_mem_assign * qubit_mem_assign))%type.

(* ------------------------------------------------------------------------- *)
(* Basic decidable equality                                                  *)
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
(* vars_of_exp (structural; used by hp/heuristics)                            *)
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


(* ------------------------------------------------------------------------- *)
(* Helper: membrane ids from config                                           *)
(* ------------------------------------------------------------------------- *)

Definition default_mid : membrane_id := 0%nat.

Definition first_mid (cfg : config) : membrane_id :=
  match cfg with
  | [] => default_mid
  | Memb l _ :: _ => l
  | LockMemb l _ _ :: _ => l
  end.

Definition mem_count (cfg : config) : nat := length cfg.

Definition nth_mid_default (cfg : config) (i : nat) : membrane_id :=
  match nth_error cfg i with
  | Some (Memb l _) => l
  | Some (LockMemb l _ _) => l
  | None => first_mid cfg
  end.

(* ------------------------------------------------------------------------- *)
(* A total “hash” for exp (extractable)                                       *)
(* ------------------------------------------------------------------------- *)

Fixpoint exp_tag (e : exp) : nat :=
  match e with
  | SKIP _ _ => 1
  | X _ _ => 2
  | CU _ _ e1 => 3 + exp_tag e1
  | RZ q _ _ => 10 + q
  | RRZ q _ _ => 20 + q
  | SR q _ => 30 + q
  | SRR q _ => 40 + q
  | QFT _ b => 50 + b
  | RQFT _ b => 60 + b
  | H _ _ => 70
  | Addto _ _ => 80
  | Seq e1 e2 => 90 + exp_tag e1 + exp_tag e2
  end.

Fixpoint sum_vars (xs : list var) : nat :=
  match xs with
  | [] => 0
  | x :: tl => x + sum_vars tl
  end.

Definition exp_hash (e : exp) : nat :=
  exp_tag e + sum_vars (vars_of_exp e).

(* ------------------------------------------------------------------------- *)
(* Paper Algorithm 1 line 4: os ← gen_os(R)                                   *)
(* Here R already is an operation list.                                       *)
(* ------------------------------------------------------------------------- *)

Definition gen_os (R : op_list) : op_list := R.

(* ------------------------------------------------------------------------- *)
(* Paper Algorithm 1 line 3: hp ← gen_hp(R)                                   *)
(* Paper: “traditional hp generation”;                                        *)
(* Here: list-order + shared-qubit dependency to keep hp acyclic.             *)
(* hp(e_i,e_j) iff i<j AND share qubit(s).                                    *)
(* ------------------------------------------------------------------------- *)

Fixpoint index_of (x : exp) (xs : list exp) : nat :=
  match xs with
  | [] => 0
  | y :: tl => if Nat.eqb (exp_hash x) (exp_hash y) then 0 else S (index_of x tl)
  end.

Definition gen_hp (R : op_list) : hb_relation :=
  fun e1 e2 =>
    let i := index_of e1 R in
    let j := index_of e2 R in
    andb (Nat.ltb i j) (share_qubit e1 e2).

(*
Definition gen_hp (R : op_list) : hb_relation :=
  fun e1 e2 =>
    let i := index_of e1 R in
    let j := index_of e2 R in
    (Nat.ltb i j = true) /\ (share_qubit e1 e2 = true).
*)



(* ------------------------------------------------------------------------- *)
(* Optimization #1 (paper): fix ranks for “similar independent ops” by order. *)
(* Implementation: seq ranks must respect hp.                                 *)
(* Since hp only points forward in R, we can compute ranks by a single scan:  *)
(*   rank(e_i) = 1 + max{ rank(e_j) | hp(e_j,e_i) }                           *)
(* Tie-break among independent ops is the original list order (fixed).        *)
(* We still keep exploration by adding a seed bump to the base rank, but only *)
(* as a *secondary* component that does NOT violate hp.                       *)
(* ------------------------------------------------------------------------- *)


Fixpoint max_pred_rank
  (hp : hb_relation) (R : op_list) (rank_of : exp -> nat) (e : exp) : nat :=
  match R with
  | [] => 0
  | x :: tl =>
      let m := max_pred_rank hp tl rank_of e in
      if hp x e
      then Nat.max (rank_of x) m
      else m
  end.

(*
Fixpoint max_pred_rank
  (hp : hb_relation) (R : op_list) (rank_of : exp -> nat) (e : exp) : nat :=
  match R with
  | [] => 0
  | x :: tl =>
      let m := max_pred_rank hp tl rank_of e in
      if andb (share_qubit x e) true (* cheap guard; hp implies share_qubit anyway *)
      then
        match hp x e with
        | conj h1 h2 =>
            (* hp uses list indices, so safe; if true, consider predecessor *)
            Nat.max (rank_of x) m
        end
      else m
  end.
*)
(* We store computed ranks in an association list keyed by exp_hash. *)
Definition rank_table : Type := list (nat * nat).  (* (exp_hash, rank) *)

Fixpoint lookup_rank (h : nat) (tbl : rank_table) : nat :=
  match tbl with
  | [] => 0
  | (k,v) :: tl => if Nat.eqb k h then v else lookup_rank h tl
  end.

Definition rank_of_tbl (tbl : rank_table) : exp -> nat :=
  fun e => lookup_rank (exp_hash e) tbl.

Fixpoint build_ranks_scan
  (hp : hb_relation) (R : op_list) (tbl : rank_table) : rank_table :=
  match R with
  | [] => tbl
  | e :: tl =>
      let r_of := rank_of_tbl tbl in
      (* base rank: 1 + max predecessor rank *)
      let base := S (max_pred_rank hp R r_of e) in
      (* fixed-order tie-break: add 0 (keeps order stable). *)
      let tbl' := (exp_hash e, base) :: tbl in
      build_ranks_scan hp tl tbl'
  end.

Definition gen_seq (seen : list candidate) (hp : hb_relation) (R : op_list) : seq_relation :=
  let seed := length seen in
  let tbl  := build_ranks_scan hp R [] in
  fun e =>
    let base := lookup_rank (exp_hash e) tbl in
    (* secondary seed bump: does NOT change relative order imposed by base,
       but lets “cases” differ in absolute rank numbers (paper uses rank numbers). *)
    base + seed.

(* ------------------------------------------------------------------------- *)
(* Optimization #2 (paper): place related ops in same membrane                 *)
(* Heuristic: if κ2 ⊆ κ1 (subset) or overlap ratio is “large”, co-locate.     *)
(* We implement greedy moO over ops ordered by seq.                            *)
(* ------------------------------------------------------------------------- *)

Definition subset_vars (xs ys : list var) : bool :=
  forallb (fun x => mem_var x ys) xs.

Definition overlap_big (xs ys : list var) : bool :=
  let xs' := uniq xs in
  let ys' := uniq ys in
  let inter := length (intersect xs' ys') in
  let denom := Nat.max 1 (Nat.max (length xs') (length ys')) in
  (* “large” = at least half overlap *)
  Nat.leb (Nat.div denom 2) inter.

(* sort ops by seq (stable insertion sort) *)
Fixpoint insert_by_seq (seq : seq_relation) (op : exp) (ops : list exp) : list exp :=
  match ops with
  | [] => [op]
  | x :: tl =>
      if Nat.leb (seq op) (seq x) then op :: x :: tl
      else x :: insert_by_seq seq op tl
  end.

Fixpoint sort_by_seq (seq : seq_relation) (ops : list exp) : list exp :=
  match ops with
  | [] => []
  | x :: tl => insert_by_seq seq x (sort_by_seq seq tl)
  end.

Definition order_by_seq (seq : seq_relation) (ops : op_list) : op_list :=
  sort_by_seq seq ops.

(* deterministic membrane choice from cfg + seed + op hash *)
Definition choose_mid (cfg : config) (seed k : nat) : membrane_id :=
  let m := mem_count cfg in
  let idx :=
    match m with
    | 0 => 0
    | S m' => Nat.modulo (k + seed) (S m')
    end
  in nth_mid_default cfg idx.

(* Greedy moO: follow seq order, reuse previous mid if “related” *)
Fixpoint build_moO
  (cfg : config) (seed : nat) (ops_sorted : list exp)
  (prev : option (exp * membrane_id))
  (tbl : list (nat * membrane_id)) : list (nat * membrane_id) :=
  match ops_sorted with
  | [] => tbl
  | op :: tl =>
      let vars := uniq (vars_of_exp op) in
      let mid :=
        match prev with
        | None => choose_mid cfg seed (exp_hash op)
        | Some (op_prev, mid_prev) =>
            let vars_prev := uniq (vars_of_exp op_prev) in
            if orb (subset_vars vars vars_prev) (overlap_big vars vars_prev)
            then mid_prev
            else choose_mid cfg seed (exp_hash op)
        end
      in
      build_moO cfg seed tl (Some (op, mid)) ((exp_hash op, mid) :: tbl)
  end.

Fixpoint lookup_mid (h : nat) (tbl : list (nat * membrane_id)) : membrane_id :=
  match tbl with
  | [] => default_mid
  | (k,v) :: tl => if Nat.eqb k h then v else lookup_mid h tl
  end.

Definition moO_of_tbl (tbl : list (nat * membrane_id)) : op_mem_assign :=
  fun op => lookup_mid (exp_hash op) tbl.

(* ------------------------------------------------------------------------- *)
(* Optimization #3 (paper): initial qubit assignment via first use in seq     *)
(* For each qubit q, find its first op in seq order, and set moQ(q)=moO(op).  *)
(* ------------------------------------------------------------------------- *)

Fixpoint first_use_mid
  (ops_sorted : list exp) (moO : op_mem_assign) (q : var) : membrane_id :=
  match ops_sorted with
  | [] => default_mid
  | op :: tl =>
      if mem_var q (vars_of_exp op) then moO op else first_use_mid tl moO q
  end.

Definition gen_mem
  (seen : list candidate)
  (cfg  : config)
  (seq  : seq_relation)
  (os   : op_list)
  : op_mem_assign * qubit_mem_assign :=
  let seed := length seen in
  let ops_sorted := order_by_seq seq os in
  let moO_tbl := build_moO cfg seed ops_sorted None [] in
  let moO := moO_of_tbl moO_tbl in
  let moQ : qubit_mem_assign :=
    fun q => first_use_mid ops_sorted moO q
  in
  (moO, moQ).

(* ------------------------------------------------------------------------- *)
(* gen_prog(seq, moO, moQ) — paper line 11 conceptually uses moQ too          *)
(* We model relocations/communications by inserting special “Reloc” markers.  *)
(* Since we don’t assume extra syntax constructors exist in DisQSyntax, we    *)
(* encode relocation as a SKIP src dst (a marker only).                        *)
(* ------------------------------------------------------------------------- *)
Definition mk_reloc (src dst : membrane_id) : exp :=
  SKIP src (Num dst).


Definition op_to_process (op : exp) : process :=
  AP (CAppU ([] : locus) op) PNil.

Fixpoint place_operation (cfg : config) (mid : membrane_id) (op : exp) : config :=
  match cfg with
  | [] => [Memb mid [op_to_process op]]
  | (Memb l ps) :: tl =>
      if var_eqb l mid
      then Memb l (ps ++ [op_to_process op]) :: tl
      else Memb l ps :: place_operation tl mid op
  | (LockMemb l r ps) :: tl =>
      if var_eqb l mid
      then LockMemb l r (ps ++ [op_to_process op]) :: tl
      else LockMemb l r ps :: place_operation tl mid op
  end.

(* Current qubit locations as an association list *)
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

Fixpoint all_qubits (ops : list exp) : list var :=
  match ops with
  | [] => []
  | op :: tl => vars_of_exp op ++ all_qubits tl
  end.

(* For an op on target mid, relocate each needed qubit if not already there *)
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
        (* insert relocation marker into target membrane, then update location *)
        let acc' := place_operation acc target (mk_reloc cur target) in
        let qloc' := qloc_update q target qloc in
        ensure_qubits tl target qloc' acc'
  end.

Fixpoint gen_prog_core
  (moO : op_mem_assign) (moQ : qubit_mem_assign)
  (ops_sorted : list exp)
  (qloc : qloc_tbl)
  (acc  : config) : config :=
  match ops_sorted with
  | [] => acc
  | op :: tl =>
      let target := moO op in
      let qs := uniq (vars_of_exp op) in
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
(* fit(P) — communication/relocation-aware (paper objective proxy)            *)
(* We count:                                                                 *)
(*  - relocations = number of SKIP src dst markers                            *)
(*  - distinct pairs (src,dst) among those markers (proxy for comm pairs)     *)
(* Total cost = relocations + 5 * distinct_pairs                              *)
(* ------------------------------------------------------------------------- *)

Definition is_reloc (e : exp) : bool :=
  match e with
  | SKIP _ (Num _) => true
  | _ => false
  end.
Definition reloc_pair (e : exp) : (membrane_id * membrane_id) :=
  match e with
  | SKIP a (Num b) => (a, b)
  | _ => (0, 0)
  end.


Fixpoint mem_pair (p : membrane_id * membrane_id) (ps : list (membrane_id * membrane_id)) : bool :=
  match ps with
  | [] => false
  | q :: tl => if andb (var_eqb (fst p) (fst q)) (var_eqb (snd p) (snd q)) then true else mem_pair p tl
  end.

Fixpoint uniq_pairs (ps : list (membrane_id * membrane_id)) : list (membrane_id * membrane_id) :=
  match ps with
  | [] => []
  | p :: tl => if mem_pair p tl then uniq_pairs tl else p :: uniq_pairs tl
  end.
Print process.
Print cexp.
Print cdexp.

Fixpoint extract_exps_from_proc (p : process) : list exp :=
  match p with
  | PNil => []
  | AP c tl =>
      match c with
      | CAppU _ e => e :: extract_exps_from_proc tl
      | _ => extract_exps_from_proc tl
      end
  | DP _ tl =>
      extract_exps_from_proc tl
  | PIf _ p1 p2 =>
      extract_exps_from_proc p1 ++ extract_exps_from_proc p2
  end.


Fixpoint extract_all_exps (cfg : config) : list exp :=
  match cfg with
  | [] => []
  | Memb _ ps :: tl =>
      (concat (map extract_exps_from_proc ps)) ++ extract_all_exps tl
  | LockMemb _ _ ps :: tl =>
      (concat (map extract_exps_from_proc ps)) ++ extract_all_exps tl
  end.

Fixpoint count_relocs (es : list exp) : nat :=
  match es with
  | [] => 0
  | e :: tl => (if is_reloc e then 1 else 0) + count_relocs tl
  end.

Fixpoint collect_pairs (es : list exp) : list (membrane_id * membrane_id) :=
  match es with
  | [] => []
  | e :: tl =>
      if is_reloc e then reloc_pair e :: collect_pairs tl else collect_pairs tl
  end.

Definition fit (P : distributed_prog) : fitness_value :=
  let es := extract_all_exps P in
  let reloc := count_relocs es in
  let pairs := length (uniq_pairs (collect_pairs es)) in
  reloc + 5 * pairs.

(* ------------------------------------------------------------------------- *)
(* Stop condition and main loop — matches paper Algorithm 1 structure          *)
(* Paper line 5 uses a set S; we use a list “seen” (accumulating).            *)
(* ------------------------------------------------------------------------- *)

Definition INF_SCORE : fitness_value := Nat.pow 10 9.

Fixpoint auto_disq_loop
  (fuel : nat)
  (hp   : hb_relation)
  (os   : op_list)
  (cfg  : config)
  (seen : list candidate)
  (Qbest: distributed_prog)
  (zmin : fitness_value)
  : distributed_prog :=
  match fuel with
  | 0 => Qbest
  | S fuel' =>
      (* line 9 *)
      let seq := gen_seq seen hp os in
      (* line 10 *)
      let '(moO, moQ) := gen_mem seen cfg seq os in
      (* line 11 *)
      let P := gen_prog seq moO moQ os in
      (* line 12 *)
      let seen' := (seq, (moO, moQ)) :: seen in
      (* line 13 *)
      let z := fit P in
      (* line 14–17 *)
      if Nat.ltb z zmin
      then auto_disq_loop fuel' hp os cfg seen' P z
      else auto_disq_loop fuel' hp os cfg seen' Qbest zmin
  end.

Definition auto_disq (max_cases : nat) (R : op_list) (cfg : config) : distributed_prog :=
  let hp := gen_hp R in       (* line 3 *)
  let os := gen_os R in       (* line 4 *)
  auto_disq_loop max_cases hp os cfg ([] : list candidate) ([] : config) INF_SCORE.






(* A case is (schedule_index, mem_seed). This is FINITE, so "no cases left"
   is meaningful and matches paper's are_still_cases(S) stopping behavior. *)
(*
Definition case : Type := (nat * nat)%type.

Fixpoint range_from (start count : nat) : list nat :=
  match count with
  | 0 => []
  | S k => start :: range_from (S start) k
  end.

Definition mk_cases (Kseq Kmem : nat) : list case :=
  let scheds := range_from 0 Kseq in
  let seeds  := range_from 0 Kmem in
  concat (map (fun si => map (fun sd => (si, sd)) seeds) scheds).

Definition are_still_cases (cases : list case) : bool :=
  negb (Nat.eqb (length cases) 0).

Fixpoint auto_disq_loop_alg1
  (Kseq  : nat)
  (hp    : hb_relation)
  (os    : op_list)
  (cfg   : config)
  (S     : list case)            (* examined set, paper line 5/12 *)
  (cases : list case)            (* remaining cases => stop when empty *)
  (Qbest : distributed_prog)
  (zmin  : fitness_value)
  : distributed_prog :=
  match cases with
  | [] => Qbest
  | (sched_i, seed) :: cases' =>
      (* paper line 9 *)
      let seq := gen_seq_many Kseq sched_i hp os in
      (* paper line 10 *)
      let '(moO, moQ) := gen_mem_seed seed cfg seq os in
      (* paper line 11 *)
      let P := gen_prog seq moO moQ os in
      (* paper line 12 *)
      let S' := (sched_i, seed) :: S in
      (* paper line 13 *)
      let z := fit P in
      (* paper line 14–17 *)
      if Nat.ltb z zmin
      then auto_disq_loop_alg1 Kseq hp os cfg S' cases' P z
      else auto_disq_loop_alg1 Kseq hp os cfg S' cases' Qbest zmin
  end.

(* Full Algorithm 1 *)
Definition auto_disq_alg1
  (Kseq  : nat)        (* max schedules to enumerate *)
  (Kmem  : nat)        (* number of different mem seeds to try *)
  (R     : op_list)
  (cfg   : config)
  : distributed_prog :=
  let hp := gen_hp R in          (* line 3 *)
  let os := gen_os R in          (* line 4 *)
  let cases := mk_cases Kseq Kmem in
  auto_disq_loop_alg1 Kseq hp os cfg [] cases ([] : config) INF_SCORE.



*)





































(* 

From Coq Require Import List Arith Bool.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.

Require Import DisQ.BasicUtility.   (* var := nat *)
Require Import DisQ.DisQSyntax.     (* exp, process, memb, config, locus, ... *)

(* ------------------------------------------------------------------------- *)
(* Types as in DisQSyntax                                                     *)
(* ------------------------------------------------------------------------- *)

(* Membrane object *)
Definition membrane : Type := memb.

(* Configuration (distributed program) *)
Definition membranes : Type := config.

(* Membrane identifier: the label 'l:var' inside Memb/LockMemb *)
Definition membrane_id : Type := var.

Definition hb_relation : Type := exp -> exp -> Prop.
Definition op_list : Type := list exp.

(* seq is “rank numbers”; lower rank = earlier *)
Definition rank : Type := nat.
Definition seq_relation : Type := exp -> rank.

(* moO maps an operation to a membrane *id* (label); moQ maps qubits to initial membrane id *)
Definition op_mem_assign : Type := exp -> membrane_id.
Definition qubit_mem_assign : Type := var -> membrane_id.

Definition fitness_value : Type := nat.
Definition distributed_prog : Type := config.

Definition candidate : Type :=
  (seq_relation * (op_mem_assign * qubit_mem_assign))%type.

(* ------------------------------------------------------------------------- *)
(* Basic decidable equality on var                                            *)
(* ------------------------------------------------------------------------- *)

Definition var_eqb (x y : var) : bool := Nat.eqb x y.

(* ------------------------------------------------------------------------- *)
(* vars_of_exp (needed by gen_prog & heuristics)                              *)
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

(* ------------------------------------------------------------------------- *)
(* Algorithm 1 line 3: hp ← gen_hp(R)                                         *)
(* total placeholder: no constraints                                          *)
(* ------------------------------------------------------------------------- *)

Definition gen_hp (_R : op_list) : hb_relation :=
  fun _ _ => False.

(* ------------------------------------------------------------------------- *)
(* Algorithm 1 line 4: os ← gen_os(R)                                         *)
(* identity                                                                    *)
(* ------------------------------------------------------------------------- *)

Definition gen_os (R : op_list) : op_list := R.

(* ------------------------------------------------------------------------- *)
(* Helper: choose a “default” membrane id                                    *)
(* ------------------------------------------------------------------------- *)

Definition default_mid : membrane_id := 0%nat.

Definition first_mid (cfg : config) : membrane_id :=
  match cfg with
  | [] => default_mid
  | Memb l _ :: _ => l
  | LockMemb l _ _ :: _ => l
  end.

Definition mem_count (cfg : config) : nat := length cfg.

(* Get the nth membrane-id from a config; fallback to first_mid *)
Definition nth_mid_default (cfg : config) (i : nat) : membrane_id :=
  match nth_error cfg i with
  | Some (Memb l _) => l
  | Some (LockMemb l _ _) => l
  | None => first_mid cfg
  end.

(* ------------------------------------------------------------------------- *)
(* A simple “hash” of an exp to nat (total, extractable)                      *)
(* ------------------------------------------------------------------------- *)

Fixpoint exp_tag (e : exp) : nat :=
  match e with
  | SKIP _ _ => 1
  | X _ _ => 2
  | CU _ _ e1 => 3 + exp_tag e1
  | RZ q _ _ => 10 + q
  | RRZ q _ _ => 20 + q
  | SR q _ => 30 + q
  | SRR q _ => 40 + q
  | QFT _ b => 50 + b
  | RQFT _ b => 60 + b
  | H _ _ => 70
  | Addto _ _ => 80
  | Seq e1 e2 => 90 + exp_tag e1 + exp_tag e2
  end.

Fixpoint sum_vars (xs : list var) : nat :=
  match xs with
  | [] => 0
  | x :: tl => x + sum_vars tl
  end.

Definition exp_hash (e : exp) : nat :=
  exp_tag e + sum_vars (vars_of_exp e).

(* ------------------------------------------------------------------------- *)
(* Algorithm 1 line 9: seq ← gen_seq(S,hp)                                    *)
(* deterministic “pseudo-random” seq using seed = |S|                         *)
(* ------------------------------------------------------------------------- *)

Definition gen_seq (_S : list candidate) (_hp : hb_relation) : seq_relation :=
  let seed := length _S in
  fun e => exp_hash e + seed.

(* ------------------------------------------------------------------------- *)
(* Algorithm 1 line 10: mo ← gen_mem(S, cfg, seq)                             *)
(* choose membrane-id by hashing into indices of config                       *)
(* ------------------------------------------------------------------------- *)

Definition gen_mem
  (seen : list candidate)
  (cfg : config)
  (_seq : seq_relation)
  : op_mem_assign * qubit_mem_assign :=
  let seed := length seen in
  let m := mem_count cfg in
  let choose_index (k : nat) : nat :=
    match m with
    | 0 => 0
    | S m' => Nat.modulo k (S m')
    end
  in
  let moO : op_mem_assign :=
    fun op => nth_mid_default cfg (choose_index (exp_hash op + seed))
  in
  let moQ : qubit_mem_assign :=
    fun q => nth_mid_default cfg (choose_index (q + seed))
  in
  (moO, moQ).


(* ------------------------------------------------------------------------- *)
(* gen_prog(seq, moO) — Algorithm 1 line 11                                   *)
(* Build config by placing each op into its chosen membrane-id                 *)
(* ------------------------------------------------------------------------- *)

Definition op_to_process (op : exp) : process :=
  AP (CAppU ([] : locus) op) PNil.

Fixpoint place_operation (cfg : config) (mid : membrane_id) (op : exp) : config :=
  match cfg with
  | [] => [Memb mid [op_to_process op]]
  | (Memb l ps) :: tl =>
      if var_eqb l mid
      then Memb l (ps ++ [op_to_process op]) :: tl
      else Memb l ps :: place_operation tl mid op
  | (LockMemb l r ps) :: tl =>
      LockMemb l r ps :: place_operation tl mid op
  end.

(* ordering by seq: insertion sort (total, extractable) *)
Fixpoint insert_by_seq (seq : seq_relation) (op : exp) (ops : list exp) : list exp :=
  match ops with
  | [] => [op]
  | x :: tl =>
      if Nat.leb (seq op) (seq x)
      then op :: x :: tl
      else x :: insert_by_seq seq op tl
  end.

Fixpoint sort_by_seq (seq : seq_relation) (ops : list exp) : list exp :=
  match ops with
  | [] => []
  | x :: tl => insert_by_seq seq x (sort_by_seq seq tl)
  end.

Definition order_by_seq (seq : seq_relation) (ops : op_list) : op_list :=
  sort_by_seq seq ops.

Definition empty_config : config := [].

Fixpoint gen_prog_core (moO : op_mem_assign) (ops : list exp) (acc : config) : config :=
  match ops with
  | [] => acc
  | op :: tl =>
      let mid := moO op in
      gen_prog_core moO tl (place_operation acc mid op)
  end.

Definition gen_prog (seq : seq_relation) (moO : op_mem_assign) (os : op_list)
  : distributed_prog :=
  gen_prog_core moO (order_by_seq seq os) empty_config.

(* ------------------------------------------------------------------------- *)
(* Algorithm 1 line 13: z ← fit(P)                                            *)
(* simple cost: total number of processes in the config                        *)
(* ------------------------------------------------------------------------- *)

Fixpoint count_procs (ps : list process) : nat :=
  match ps with [] => 0 | _ :: tl => S (count_procs tl) end.

Fixpoint fit (P : distributed_prog) : fitness_value :=
  match P with
  | [] => 0
  | m :: tl =>
      match m with
      | Memb _ ps => count_procs ps + fit tl
      | LockMemb _ _ ps => count_procs ps + fit tl
      end
  end.

(* ------------------------------------------------------------------------- *)
(* Loop stop condition                                                        *)
(* ------------------------------------------------------------------------- *)

Definition INF_SCORE : fitness_value := Nat.pow 10 6.

Definition are_still_cases (max_cases : nat) (S : list candidate) : bool :=
  Nat.ltb (length S) max_cases.

(* ------------------------------------------------------------------------- *)
(* Algorithm 1: AutoDisQ                                                      *)
(* ------------------------------------------------------------------------- *)

Fixpoint auto_disq_loop
  (fuel : nat)
  (hp : hb_relation)
  (os : op_list)
  (cfg : config)
  (seen : list candidate)
  (Qbest : distributed_prog)
  (zmin : fitness_value)
  : distributed_prog :=
  match fuel with
  | 0 => Qbest
  | S fuel' =>
      let seq := gen_seq seen hp in
      let '(moO, moQ) := gen_mem seen cfg seq in
      let P := gen_prog seq moO os in
      let seen' := (seq, (moO, moQ)) :: seen in
      let z := fit P in
      if Nat.ltb z zmin
      then auto_disq_loop fuel' hp os cfg seen' P z
      else auto_disq_loop fuel' hp os cfg seen' Qbest zmin
  end.

Definition auto_disq (max_cases : nat) (R : op_list) (cfg : config) : distributed_prog :=
  let hp := gen_hp R in
  let os := gen_os R in
  auto_disq_loop max_cases hp os cfg ([] : list candidate) empty_config INF_SCORE.


*)





(*



(* ------------------------------------------------------------------------- *)
(* Extraction                                                                 *)
(* ------------------------------------------------------------------------- *)

From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt.

Extraction Language OCaml.
Extraction Blacklist String List Nat Bool.

Extraction "AAautodisq_0.ml" auto_disq.




From Coq Require Import List Arith Bool.
Import ListNotations.
Local Open Scope list_scope.

Require Import Reals Psatz.
Require Import SQIR.SQIR.
Require Import QuantumLib.VectorStates.
Require Import SQIR.UnitaryOps.

Require Import Coq.btauto.Btauto Coq.NArith.Nnat.
Require Import Classical_Prop.

Require Import BasicUtility.
Require Import MathSpec.
Require Import DisQSyntax.

From Coq Require Import List Arith Bool.
Import ListNotations.
Local Open Scope nat_scope.

(* ------------------------------------------------------------------------- *)
(* Types as in the paper                                                     *)
(* ------------------------------------------------------------------------- *)

Definition var := nat.

Definition membrane_id := var.
Definition membranes : Type := config.

Definition var_eqb (x y : var) : bool := Nat.eqb x y.

Definition hb_relation : Type := exp -> exp -> Prop.
Definition op_list : Type := list exp.

(* seq is “rank numbers”; lower rank = earlier *)
Definition rank : Type := nat.
Definition seq_relation : Type := exp -> rank.

(* Assignments now return membrane *IDs* (nat), not memb objects *)
Definition op_mem_assign := exp -> membrane_id.
Definition qubit_mem_assign := var -> membrane_id.
Definition current_qubit_loc := var -> membrane_id.


Definition fitness_value := nat.
Definition distributed_prog := config.

Definition candidate : Type :=
  (seq_relation * (op_mem_assign * qubit_mem_assign))%type.

(* ------------------------------------------------------------------------- *)
(* vars_of_exp (needed by gen_prog & heuristics)                              *)
(* ------------------------------------------------------------------------- *)



Fixpoint vars_of_exp (e : exp) : list var :=
  match e with
  | SKIP _ _ => []
  | X x _ => x :: nil
  | H x _ => x :: nil
  | RZ _ x _ => x :: nil
  | RRZ _ x _ => x :: nil
  | SR _ x => x :: nil
  | SRR _ x => x :: nil
  | QFT x _ => x :: nil
  | RQFT x _ => x :: nil
  | Addto x q => x :: q :: nil
  | CU x _ e1 => x :: vars_of_exp e1
  | Seq e1 e2 => vars_of_exp e1 ++ vars_of_exp e2
  end.

Definition vars_of_exp_nodup (e : exp) : list var :=
  nodup Nat.eq_dec (vars_of_exp e).

(* ------------------------------------------------------------------------- *)
(* Algorithm 1 line 3: hp ← gen_hp(R)                                         *)
(* For now: simplest, total hp = False (no constraints). You can refine later *)
(* ------------------------------------------------------------------------- *)

Definition gen_hp (_R : op_list) : hb_relation :=
  fun _ _ => False.

(* ------------------------------------------------------------------------- *)
(* Algorithm 1 line 4: os ← gen_os(R)                                         *)
(* If R is already an op_list, gen_os is identity.                            *)
(* ------------------------------------------------------------------------- *)

Definition gen_os (R : op_list) : op_list := R.

(* ------------------------------------------------------------------------- *)
(* Helper: choose a “default” membrane                                       *)
(* ------------------------------------------------------------------------- *)

Definition default_mem : membrane := 0%nat.

Definition first_mem (L : membranes) : membrane :=
  match L with
  | [] => default_mem
  | m :: _ => m
  end.

Definition mem_count (L : membranes) : nat :=
  length L.

(* ------------------------------------------------------------------------- *)
(* A simple “hash” of an exp to nat (total, extractable)                      *)
(* ------------------------------------------------------------------------- *)

Fixpoint exp_tag (e : exp) : nat :=
  match e with
  | SKIP _ _ => 1
  | X _ _ => 2
  | CU _ _ e1 => 3 + exp_tag e1
  | RZ q _ _ => 10 + q
  | RRZ q _ _ => 20 + q
  | SR q _ => 30 + q
  | SRR q _ => 40 + q
  | QFT _ b => 50 + b
  | RQFT _ b => 60 + b
  | H _ _ => 70
  | Addto _ _ => 80
  | Seq e1 e2 => 90 + exp_tag e1 + exp_tag e2
  end.

Fixpoint sum_vars (xs : list var) : nat :=
  match xs with
  | [] => 0
  | x :: tl => x + sum_vars tl
  end.

Definition exp_hash (e : exp) : nat :=
  exp_tag e + sum_vars (vars_of_exp e).

(* ------------------------------------------------------------------------- *)
(* Algorithm 1 line 9: seq ← gen_seq(S,hp)                                    *)
(* The paper says “randomly produce seq”.                                    *)
(* We implement a deterministic “pseudo-random” seq using seed = |S|.         *)
(* ------------------------------------------------------------------------- *)

Definition gen_seq (_S : list candidate) (_hp : hb_relation) : seq_relation :=
  let seed := length _S in
  fun e => exp_hash e + seed.

(* ------------------------------------------------------------------------- *)
(* Algorithm 1 line 10: mo ← gen_mem(S, L, seq)                               *)
(* We generate two assignments: moO and moQ.                                  *)
(* - moO(op) chooses a membrane from L using (hash op + seed) mod |L|          *)
(* - moQ(q) chooses initial membrane similarly                                *)
(* ------------------------------------------------------------------------- *)

Definition nth_mem_default (L : membranes) (i : nat) : membrane :=
  nth i L (first_mem L).

Definition gen_mem
  (S : list candidate)
  (L : membranes)
  (_seq : seq_relation)
  : op_mem_assign * qubit_mem_assign :=
  let seed := length S in
  let m := mem_count L in
  let choose_index (k : nat) : nat :=
    match m with
    | 0 => 0
    | S m' => Nat.modulo k (S m')
    end
  in
  let moO : op_mem_assign :=
    fun op => nth_mem_default L (choose_index (exp_hash op + seed))
  in
  let moQ : qubit_mem_assign :=
    fun q => nth_mem_default L (choose_index (q + seed))
  in
  (moO, moQ).

(* ------------------------------------------------------------------------- *)
(* gen_prog(seq, mo) — Algorithm 1 line 11                                   *)
(* We build a DisQ configuration (list memb).                                 *)
(* For each operation, we place it into the membrane chosen by moO.           *)
(* We ignore teleportation here (paper inserts comm pairs). You can add later. *)
(* ------------------------------------------------------------------------- *)

Definition op_to_process (op : exp) : process :=
  AP (CAppU ([] : locus) op) PNil.

Fixpoint memb_exists (cfg : config) (mid : membrane) : bool :=
  match cfg with
  | [] => false
  | m :: tl =>
      match m with
      | Memb l _ => if var_eqb l mid then true else memb_exists tl mid
      | LockMemb l _ _ => if var_eqb l mid then true else memb_exists tl mid
      end
  end.

Fixpoint place_operation (cfg : config) (mid : membrane) (op : exp) : config :=
  match cfg with
  | [] => [Memb mid [op_to_process op]]
  | (Memb l ps) :: tl =>
      if var_eqb l mid
      then Memb l (ps ++ [op_to_process op]) :: tl
      else Memb l ps :: place_operation tl mid op
  | (LockMemb l r ps) :: tl =>
      (* keep locks; still allow placing in other membranes *)
      LockMemb l r ps :: place_operation tl mid op
  end.

(* ordering by seq: insertion sort (total, extractable) *)
Fixpoint insert_by_seq (seq : seq_relation) (op : exp) (ops : list exp) : list exp :=
  match ops with
  | [] => [op]
  | x :: tl =>
      if Nat.leb (seq op) (seq x)
      then op :: x :: tl
      else x :: insert_by_seq seq op tl
  end.

Fixpoint sort_by_seq (seq : seq_relation) (ops : list exp) : list exp :=
  match ops with
  | [] => []
  | x :: tl => insert_by_seq seq x (sort_by_seq seq tl)
  end.

Definition order_by_seq (seq : seq_relation) (ops : op_list) : op_list :=
  sort_by_seq seq ops.

Definition empty_config : config := [].

Fixpoint gen_prog_core (moO : op_mem_assign) (ops : list exp) (acc : config) : config :=
  match ops with
  | [] => acc
  | op :: tl =>
      let mid := moO op in
      gen_prog_core moO tl (place_operation acc mid op)
  end.

Definition gen_prog (seq : seq_relation) (moO : op_mem_assign) (os : op_list) : distributed_prog :=
  gen_prog_core moO (order_by_seq seq os) empty_config.

(* ------------------------------------------------------------------------- *)
(* Algorithm 1 line 13: z ← fit(P)                                            *)
(* A simple cost: total number of processes in the config                     *)
(* (You can change this to teleport count etc.)                               *)
(* ------------------------------------------------------------------------- *)

Fixpoint count_procs (ps : list process) : nat :=
  match ps with [] => 0 | _ :: tl => S (count_procs tl) end.

Fixpoint fit (P : distributed_prog) : fitness_value :=
  match P with
  | [] => 0
  | m :: tl =>
      match m with
      | Memb _ ps => count_procs ps + fit tl
      | LockMemb _ _ ps => count_procs ps + fit tl
      end
  end.

(* ------------------------------------------------------------------------- *)
(* Algorithm 1 loop stop condition: while are_still_cases(S)                  *)
(* The paper: “until no more possible seq cases”.                             *)
(* Executable Coq: stop after max_cases candidates.                            *)
(* ------------------------------------------------------------------------- *)

Definition INF_SCORE : fitness_value := 1000000%nat.

Definition are_still_cases (max_cases : nat) (S : list candidate) : bool :=
  Nat.ltb (length S) max_cases.

(* ------------------------------------------------------------------------- *)
(* Algorithm 1: AutoDisQ                                                      *)
(* Input: R, L   Output: Q                                                    *)
(* ------------------------------------------------------------------------- *)

Fixpoint auto_disq_loop
  (max_cases : nat)
  (hp : hb_relation)
  (os : op_list)
  (L : membranes)
  (S : list candidate)
  (Qbest : distributed_prog)
  (zmin : fitness_value)
  : distributed_prog :=
  if are_still_cases max_cases S then
    (* line 9 *)
    let seq := gen_seq S hp in
    (* line 10 *)
    let '(moO, _moQ) := gen_mem S L seq in
    (* line 11 *)
    let P := gen_prog seq moO os in
    (* line 12 *)
    let S' := (seq, (moO, (fun _ => first_mem L))) :: S in
    (* line 13 *)
    let z := fit P in
    (* line 14-16 *)
    if Nat.ltb z zmin
    then auto_disq_loop max_cases hp os L S' P z
    else auto_disq_loop max_cases hp os L S' Qbest zmin
  else
    (* line 19 *)
    Qbest.

Definition auto_disq (max_cases : nat) (R : op_list) (L : membranes) : distributed_prog :=
  (* line 3 *) let hp := gen_hp R in
  (* line 4 *) let os := gen_os R in
  (* line 5 *) let S := ([] : list candidate) in
  (* line 6 *) let zmin := INF_SCORE in
  (* line 7 *) let Q := empty_config in
  (* lines 8-19 *) auto_disq_loop max_cases hp os L S Q zmin.

(* ------------------------------------------------------------------------- *)
(* Extraction                                                                 *)
(* ------------------------------------------------------------------------- *)

From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlNatInt.

Extraction Language OCaml.
Extraction Blacklist String List Nat Bool.

Extraction "AAautodisq_0.ml" auto_disq.
*)