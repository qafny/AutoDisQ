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









(*
From Coq Require Import List Arith Bool.
Import ListNotations.
Require Import List.
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

(* ========================================================================= *)
(* Mapping                                                                   *)
(* ========================================================================= *)
Definition var := nat.

Definition membrane_id := var.
Definition membranes : Type := config.

Definition var_eqb (x y : var) : bool := Nat.eqb x y.

(* ========================================================================= *)
(* vars_of_exp                                        *)
(* ========================================================================= *)

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



(* ========================================================================= *)
(* Core aliases                                                               *)
(* ========================================================================= *)

Definition hb_relation : Type := exp -> exp -> Prop.
Definition op_list := list exp.


Definition op_mem_assign := exp -> membrane_id.
Definition qubit_mem_assign := var -> membrane_id.
Definition current_qubit_loc := var -> membrane_id.

Definition rank := nat.
Definition seq_relation := exp -> rank.

Definition fitness_value := nat.
Definition distributed_prog := config.


(* ========================================================================= *)
(* Config utilities                                                           *)
(* ========================================================================= *)

Definition memb_id (m : memb) : var :=
  match m with
  | Memb l _ => l
  | LockMemb l _ _ => l
  end.

Definition memb_procs (m : memb) : list process :=
  match m with
  | Memb _ lp => lp
  | LockMemb _ _ lp => lp
  end.

Definition rebuild_memb (m : memb) (lp' : list process) : memb :=
  match m with
  | Memb l _ => Memb l lp'
  | LockMemb l r _ => LockMemb l r lp'
  end.

Fixpoint memb_exists (cfg : config) (mid : var) : bool :=
  match cfg with
  | [] => false
  | m :: tl =>
      if var_eqb (memb_id m) mid then true else memb_exists tl mid
  end.
Definition is_locked (m : memb) : bool :=
  match m with
  | Memb _ _ => false
  | LockMemb _ _ _ => true
  end.
Definition ensure_memb (cfg : config) (mid : var) : config :=
  if memb_exists cfg mid then cfg else Memb mid [] :: cfg.

Fixpoint update_memb_procs
  (cfg : config) (mid : var) (f : list process -> list process) : config :=
  match cfg with
  | [] => []
  | m :: tl =>
      if var_eqb (memb_id m) mid
      then rebuild_memb m (f (memb_procs m)) :: tl
      else m :: update_memb_procs tl mid f
  end.

Fixpoint flatten_config (cfg : config) : list process :=
  match cfg with
  | [] => []
  | m :: tl => memb_procs m ++ flatten_config tl
  end.

Definition memb_exists_prop (cfg : config) (mid : var) : Prop :=
  exists m, In m cfg /\ memb_id m = mid.
(* ========================================================================= *)
(* Operation → process                                                        *)
(* ========================================================================= *)


Definition op_to_process (op : exp) : process :=
  AP (CAppU (nil : locus) op) PNil.

(*  place_operation takes membrane_id (nat), and builds/updates memb *)
Fixpoint place_operation (cfg : config) (mid : membrane_id) (op : exp) : config :=
  match cfg with
  | [] => [Memb mid [op_to_process op]]
  | (Memb l ps) :: tl =>
      if Nat.eqb l mid
      then (Memb l (ps ++ [op_to_process op])) :: tl
      else (Memb l ps) :: place_operation tl mid op
  | (LockMemb l r ps) :: tl =>
     
      (LockMemb l r ps) :: place_operation tl mid op
  end.

(* ========================================================================= *)
(* Teleport insertion                                        *)
(* ========================================================================= *)


(* target is membrane_id; loc maps qubit -> membrane_id *)
Definition insert_teleport_sends
  (cfg : config) (_qs : list var) (fresh : nat) (_target : membrane_id)
  : config * nat :=
  (cfg, fresh).

Definition insert_teleport_receives
  (cfg : config) (_qs : list var) (fresh : nat) (_target : membrane_id)
  (loc : var -> membrane_id)
  : config * nat * (var -> membrane_id) :=
  (cfg, fresh, loc).

Definition empty_config : config := nil.


(* ========================================================================= *)
(* Algorithm 1 helpers — trivial but total                                    *)
(* ========================================================================= *)

Definition candidate : Type :=
  (seq_relation * (op_mem_assign * qubit_mem_assign))%type.

Definition INF_SCORE : fitness_value := Nat.pow 10 6.


(* Generate happens-before relation *)
Definition gen_hp (_ops : op_list) : hb_relation := fun _ _ => False.
(*
Definition gen_seq (_S : list candidate) (_hp : hb_relation) : seq_relation :=
  let seed := length _S in
  fun e => exp_hash e + seed.
*)
(* Generate schedule*)
Definition gen_seq (_seen : list candidate) (_hp : hb_relation) : seq_relation :=
  fun _ => 0%nat.

(* Generate assignments: map everything to membrane 0 *)
Definition gen_mem
  (_seen : list candidate)
  (_cfg : membranes)
  (_seq : seq_relation)
  : op_mem_assign * qubit_mem_assign :=
  ( (fun _ : exp => 0%nat),
    (fun _ : var => 0%nat) ).

Definition fit (_ : distributed_prog) : fitness_value := 0%nat.


Definition order_by_seq (_ : seq_relation) (ops : op_list) : op_list := ops.

(* ========================================================================= *)
(* Algorithm 2 — program generation                                           *)
(* ========================================================================= *)


Definition update_loc_for
  (loc : current_qubit_loc) (qs : list var) (target : membrane_id)
  : current_qubit_loc :=
  fun q => if existsb (fun x => var_eqb x q) qs then target else loc q.

Definition qubits_to_move
  (loc : current_qubit_loc) (target : membrane_id) (qs : list var)
  : list var :=
  filter (fun q => negb (var_eqb (loc q) target)) qs.

Fixpoint gen_prog_core
  (moO : op_mem_assign)
  (remaining : list exp)
  (current_loc : current_qubit_loc)
  (acc : config)
  (fresh : nat)
  : config * nat * current_qubit_loc :=
  match remaining with
  | [] => (acc, fresh, current_loc)
  | op :: tl =>
      let target := moO op in
      let qs := vars_of_exp op in
      let to_move := qubits_to_move current_loc target qs in
      let '(acc1, fresh1, loc1) :=
        match to_move with
        | [] => (acc, fresh, current_loc)
        | _ =>
            let '(cfg1, f1) := insert_teleport_sends acc to_move fresh target in
            let '(cfg2, f2, loc2) :=
              insert_teleport_receives cfg1 to_move f1 target current_loc in
            (cfg2, f2, update_loc_for loc2 to_move target)
        end
      in
      gen_prog_core moO tl loc1 (place_operation acc1 target op) fresh1
  end.

Definition gen_prog
  (seq : seq_relation)
  (moQ : qubit_mem_assign)
  (moO : op_mem_assign)
  (ops : op_list)
  : distributed_prog :=
  let '(cfg, _, _) :=
    gen_prog_core moO (order_by_seq seq ops) moQ empty_config 0
  in cfg.



(* ========================================================================= *)
(* Algorithm 1 — main AutoDisQ loop                                           *)
(* ========================================================================= *)


Fixpoint auto_disq_search
  (ops : op_list)
  (avail : membranes)
  (hp : hb_relation)
  (seen : list candidate)
  (best : distributed_prog)
  (_ : fitness_value)
  (fuel : nat) : distributed_prog :=
  match fuel with
  | 0%nat => best
  | S n =>
      let seq := gen_seq seen hp in
      let '(moO, moQ) := gen_mem seen avail seq in
      let prog := gen_prog seq moQ moO ops in
      auto_disq_search ops avail hp ((seq,(moO,moQ))::seen) prog 0%nat n
  end.



Definition fuel_from_ops (ops : op_list) : nat :=
  length ops * length ops.

Definition auto_disq (ops : op_list) (avail : membranes) : distributed_prog :=
  auto_disq_search ops avail (gen_hp ops) [] empty_config 0%nat (fuel_from_ops ops).


Definition auto_disq_as_processes (ops : op_list) (avail : membranes) : list process :=
  flatten_config (auto_disq ops avail).

(* ========================================================================= *)
(* Algorithm 3 — parallelization                                  *)
(* ========================================================================= *)

Definition overlaps (e1 e2 : exp) : bool :=
  existsb
    (fun x => existsb (fun y => var_eqb x y) (vars_of_exp e2))
    (vars_of_exp e1).


Definition fits_block (op : exp) (block : list exp) : bool :=
  existsb (fun e => overlaps op e) block.

Fixpoint insert_first_fit (op : exp) (blocks : list (list exp)) : list (list exp) :=
  match blocks with
  | [] => [[op]]
  | b :: bs =>
      if fits_block op b
      then (op :: b) :: bs
      else b :: insert_first_fit op bs
  end.


Fixpoint compute_scc (_hp : hb_relation) (ops : list exp) : list (list exp) :=
  match ops with
  | [] => []
  | op :: tl => insert_first_fit op (compute_scc _hp tl)
  end.

Definition opt_hp (hp : hb_relation) (_seq : seq_relation) : hb_relation := hp.

Definition order_ops_in_scc (ops : list exp) : list exp := ops.

Definition parallelize_in_membrane
  (hp : hb_relation)
  (seq : seq_relation)
  (ops : list exp)
  : list (list exp) :=
  compute_scc (opt_hp hp seq) ops.

Definition example_sequential_shor : op_list := nil.
Definition example_membranes : membranes := nil.

Definition distributed_shor : distributed_prog :=
  auto_disq example_sequential_shor example_membranes.


Definition my_vars_of_exp := vars_of_exp.
Definition my_place_operation := place_operation.
Definition my_insert_teleport_sends := insert_teleport_sends.
Definition my_insert_teleport_receives := insert_teleport_receives.
Definition my_empty_config : config := empty_config.
Definition my_gen_seq := gen_seq.
Definition my_gen_mem := gen_mem.
Definition my_fit := fit.
Definition my_order_by_seq := order_by_seq.

Check my_vars_of_exp.

Set Extraction AutoInline.
Extraction Inline
  my_vars_of_exp my_place_operation
  my_insert_teleport_sends my_insert_teleport_receives
  my_empty_config my_gen_seq my_gen_mem
  my_fit my_order_by_seq.

*)
