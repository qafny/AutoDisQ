From Coq Require Import List Arith Bool Nat NArith Lia.
Import ListNotations.

Require Import Coq.Sorting.Mergesort.
Require Import Coq.Structures.Orders.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import QArith.

Local Open Scope list_scope.
Local Open Scope bool_scope.

Require Import QuantumLib.Prelim.
Require Import DisQ.BasicUtility.
Require Import DisQ.DisQSyntax.

Definition membrane    : Type := memb.
Definition membranes   : Type := config.
Definition membrane_id : Type := var.

Inductive myOp : Type :=
| OpAP  (a : cexp)
| OpIf  (b : cbexp) (p q : list cexp).

Definition op_list : Type := list myOp.
Definition hb_relation : Type := N -> N -> bool.
Definition rank : Type := N.
Definition seq_relation : Type := myOp -> rank.
Definition op_mem_assign : Type := myOp -> membrane_id.

Inductive myOpAux : Type :=
| OpNum (n : N)
| OpExp (a : cexp).

Definition qubit_mem_assign : Type := var -> membrane_id.
Definition fitness_value : Type := nat.
Definition distributed_prog : Type := config.

Definition scored_cand : Type :=
  (nat * membrane_id * ((list (N * N)%type * list (N * N)%type)%type))%type.

Definition nposi : Type := (N * N)%type.

Fixpoint list_eqb {A : Type} (beq : A -> A -> bool) (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => andb (beq x y) (list_eqb beq xs' ys')
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
  | AModMult a1 b1 c1, AModMult a2 b2 c2 =>
      andb (aexp_eqb a1 a2)
           (andb (aexp_eqb b1 b2) (aexp_eqb c1 c2))
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

Definition range_eqb (r1 r2 : range) : bool :=
  match r1, r2 with
  | (x1, (lo1, hi1)), (x2, (lo2, hi2)) =>
      andb (Nat.eqb x1 x2)
           (andb (Nat.eqb lo1 lo2) (Nat.eqb hi1 hi2))
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
      andb (Nat.eqb x1 x2)
           (andb (aexp_eqb a1 a2) (exp_eqb e1' e2'))
  | RZ q1 x1 a1, RZ q2 x2 a2 =>
      andb (Nat.eqb q1 q2)
           (andb (Nat.eqb x1 x2) (aexp_eqb a1 a2))
  | RRZ q1 x1 a1, RRZ q2 x2 a2 =>
      andb (Nat.eqb q1 q2)
           (andb (Nat.eqb x1 x2) (aexp_eqb a1 a2))
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

Module RangeOrder <: TotalLeBool'.
  Definition t := range.

  Definition leb (x y : range) : bool :=
    if Nat.ltb (fst x) (fst y) then true
    else if Nat.eqb (fst x) (fst y) then
           if Nat.ltb (fst (snd x)) (fst (snd y)) then true
           else if Nat.eqb (fst (snd x)) (fst (snd y))
                then Nat.leb (snd (snd x)) (snd (snd y))
                else false
    else false.

  Infix "[<=]" := leb (at level 50).

  Theorem leb_total : forall x y, (x [<=] y) = true \/ (y [<=] x) = true.
  Proof.
    intros [vx [lx hx]] [vy [ly hy]].
    unfold leb; simpl.
    destruct (Nat.ltb vx vy) eqn:Hvxy.
    - left; reflexivity.
    - destruct (Nat.eqb vx vy) eqn:Heqv.
      + apply Nat.eqb_eq in Heqv; subst.
        destruct (Nat.ltb lx ly) eqn:Hlxy.
        * left; reflexivity.
        * destruct (Nat.eqb lx ly) eqn:Heql.
          -- apply Nat.eqb_eq in Heql; subst.
             destruct (Nat.leb hx hy) eqn:Hh.
             ++ left; reflexivity.
             ++ right.
                rewrite Nat.ltb_irrefl, Nat.eqb_refl, Nat.ltb_irrefl, Nat.eqb_refl.
                apply Nat.leb_gt in Hh.
                apply Nat.leb_le; lia.
          -- apply Nat.eqb_neq in Heql.
             right.
             rewrite Nat.ltb_irrefl, Nat.eqb_refl.
             destruct (Nat.ltb ly lx) eqn:Hlyx.
             ++ reflexivity.
             ++ apply Nat.ltb_ge in Hlxy.
                apply Nat.ltb_ge in Hlyx.
                exfalso; lia.
      + apply Nat.eqb_neq in Heqv.
        right.
        destruct (Nat.ltb vy vx) eqn:Hvyx.
        * reflexivity.
        * apply Nat.ltb_ge in Hvyx.
          apply Nat.ltb_ge in Hvxy.
          exfalso; lia.
  Qed.
End RangeOrder.

Module SortRange := Sort(RangeOrder).

Definition nat_range_inter (x y : (nat * nat)%type) : bool :=
      (Nat.leb (fst x) (fst y) && Nat.ltb (fst y) (snd x))
  ||  (Nat.ltb (fst y) (fst x) && Nat.ltb (fst x) (snd y)).

Definition range_intersect (x y : range) : bool :=
  Nat.eqb (fst x) (fst y) && nat_range_inter (snd x) (snd y).

Definition same_name (x y : range) : bool :=
  Nat.eqb (fst x) (fst y).

Fixpoint intersect' (x : range) (y : locus) : bool :=
  match y with
  | [] => false
  | a :: yas =>
      if (same_name x a) && (nat_range_inter (snd x) (snd a))
      then true
      else intersect' x yas
  end.

Fixpoint intersect (x y : locus) : bool :=
  match x with
  | [] => false
  | a :: xas => if intersect' a y then true else intersect xas y
  end.

Definition get_locus (x : cexp) : locus :=
  match x with
  | CNew a => [a]
  | CAppU l _ => l
  | CMeas _ k => k
  | Send _ x a => [(x, (a, Nat.succ a))]
  | Recv _ x y => [(x, (y, Nat.succ y))]
  end.

Definition get_loci (x : list cexp) : locus :=
  fold_left (fun a b => get_locus b ++ a) x [].

Definition get_vars_cexp (x : cexp) : list var :=
  match x with
  | CMeas x _ => [x]
  | _ => []
  end.

Fixpoint get_vars_aexp (x : aexp) : list var :=
  match x with
  | BA a => [a]
  | Num _ => []
  | APlus e1 e2 => get_vars_aexp e1 ++ get_vars_aexp e2
  | AMult e1 e2 => get_vars_aexp e1 ++ get_vars_aexp e2
  | AModMult e1 e2 e3 => get_vars_aexp e1 ++ get_vars_aexp e2 ++ get_vars_aexp e3
  end.

Definition get_vars_bexp (x : cbexp) : list var :=
  match x with
  | CEq a b => get_vars_aexp a ++ get_vars_aexp b
  | CLt a b => get_vars_aexp a ++ get_vars_aexp b
  end.

Definition is_inter (x y : cexp) : bool :=
  intersect (get_locus x) (get_locus y).

Definition inter_vars (xs ys : list var) : bool :=
  match Coq.Lists.ListSet.set_inter Nat.eq_dec xs ys with
  | [] => false
  | _ => true
  end.

Definition gen_hb_single (x y : (N * myOp)%type) (acc : N -> N -> bool) : N -> N -> bool :=
  match snd x, snd y with
  | OpAP xa, OpAP ya =>
      fun i j =>
        if (N.eqb i (fst x)) && (N.eqb j (fst y))
        then is_inter xa ya
        else acc i j
  | OpAP xa, OpIf ya la ra =>
      fun i j =>
        if (N.eqb i (fst x)) && (N.eqb j (fst y))
        then intersect (get_locus xa) (get_loci (la ++ ra))
             || inter_vars (get_vars_cexp xa) (get_vars_bexp ya)
        else acc i j
  | OpIf ya la ra, OpAP xa =>
      fun i j =>
        if (N.eqb i (fst y)) && (N.eqb j (fst x))
        then intersect (get_locus xa) (get_loci (la ++ ra))
             || inter_vars (get_vars_cexp xa) (get_vars_bexp ya)
        else acc i j
  | OpIf xa la ra, OpIf ya lb rb =>
      fun i j =>
        if (N.eqb i (fst y)) && (N.eqb j (fst x))
        then intersect (get_loci (la ++ ra)) (get_loci (lb ++ rb))
             || inter_vars (get_vars_bexp xa) (get_vars_bexp ya)
        else acc i j
  end.

Fixpoint opListOrder' (l : op_list) (n : N) : list ((N * myOp)%type) :=
  match l with
  | [] => []
  | x :: xs => (n, x) :: opListOrder' xs (N.succ n)
  end.

Definition opListOrder (l : op_list) : list ((N * myOp)%type) :=
  opListOrder' l 0%N.

Definition empty_hp : hb_relation := fun _ _ => false.

Fixpoint gen_hb' (x : (N * myOp)%type) (l : list ((N * myOp)%type)) (acc : hb_relation) : hb_relation :=
  match l with
  | [] => acc
  | a :: xas => gen_hb_single x a (gen_hb' x xas acc)
  end.

Fixpoint gen_hb_a (R : list ((N * myOp)%type)) (acc : hb_relation) : hb_relation :=
  match R with
  | [] => acc
  | a :: xas => gen_hb_a xas (gen_hb' a xas acc)
  end.

Definition trans_closure (n : N) (x : N) (acc : hb_relation) : hb_relation :=
  fun a b =>
    if (N.ltb a x) && (N.ltb x b) && (N.ltb b n) && acc a x && acc x b
    then true
    else acc a b.

Fixpoint gen_hb_trans (size : N) (n : nat) (acc : hb_relation) : hb_relation :=
  match n with
  | O => acc
  | S m => gen_hb_trans size m (trans_closure size (N.of_nat m) acc)
  end.

Definition gen_hb (R : list ((N * myOp)%type)) : hb_relation :=
  gen_hb_trans (N.of_nat (length R)) (length R) (gen_hb_a R empty_hp).

Fixpoint sim_exp (x y : exp) : bool :=
  match x, y with
  | SKIP _ _, SKIP _ _ => true
  | X _ _, X _ _ => true
  | CU _ _ x1, CU _ _ y1 => sim_exp x1 y1
  | RZ _ _ _, RZ _ _ _ => true
  | RRZ _ _ _, RRZ _ _ _ => true
  | SR _ _, SR _ _ => true
  | SRR _ _, SRR _ _ => true
  | QFT _ _, QFT _ _ => true
  | RQFT _ _, RQFT _ _ => true
  | H _ _, H _ _ => true
  | Addto _ _, Addto _ _ => true
  | Seq x1 x2, Seq y1 y2 => sim_exp x1 y1 && sim_exp x2 y2
  | _, _ => false
  end.

Definition sim_cexp (x y : cexp) : bool :=
  match x, y with
  | CNew _, CNew _ => true
  | CAppU _ a, CAppU _ b => sim_exp a b
  | CMeas _ _, CMeas _ _ => true
  | Send _ _ _, Send _ _ _ => true
  | Recv _ _ _, Recv _ _ _ => true
  | _, _ => false
  end.

Definition insert_op (a : (N * myOp)%type) (acc : list (list ((N * myOp)%type))) :=
  match acc with
  | [] => [[a]]
  | [] :: xl => [a] :: xl
  | ((i, OpAP b) :: xl) :: al =>
      match a with
      | (j, OpAP q) =>
          if sim_cexp q b
          then ((i, OpAP b) :: xl ++ [(j, OpAP q)]) :: al
          else [(j, OpAP q)] :: acc
      | (j, OpIf c d e) => [(j, OpIf c d e)] :: (((i, OpAP b) :: xl) :: al)
      end
  | ((i, OpIf c d e) :: xl) :: al => [a] :: ((i, OpIf c d e) :: xl) :: al
  end.

Fixpoint partition_op' (l : list ((N * myOp)%type)) (acc : list (list ((N * myOp)%type))) :=
  match l with
  | [] => acc
  | x :: xl => partition_op' xl (insert_op x acc)
  end.

Definition partition_op (l : list ((N * myOp)%type)) :=
  rev (partition_op' l []).

Definition nposi_eq (r1 r2 : nposi) : bool :=
  match r1, r2 with
  | (x1, y1), (x2, y2) => (N.eqb x1 x2) && (N.eqb y1 y2)
  end.

Fixpoint insert_all
  (x : (myOpAux * list nposi)%type)
  (xs : list ((myOpAux * list nposi)%type))
  : list (list ((myOpAux * list nposi)%type)) :=
  match xs with
  | [] => [[x]]
  | y :: tl => (x :: y :: tl) :: map (fun zs => y :: zs) (insert_all x tl)
  end.

Fixpoint permutations
  (xs : list ((myOpAux * list nposi)%type))
  : list (list ((myOpAux * list nposi)%type)) :=
  match xs with
  | [] => [[]]
  | x :: tl => concat (map (insert_all x) (permutations tl))
  end.

Definition permutations_one
  (l : list ((myOpAux * list nposi)%type))
  : list (list ((myOpAux * list nposi)%type)) :=
  [l].

Fixpoint car_concat'
  (x : list ((myOpAux * list nposi)%type))
  (y : list (list ((myOpAux * list nposi)%type)))
  : list (list ((myOpAux * list nposi)%type)) :=
  match y with
  | [] => []
  | a :: ys => (x ++ a) :: car_concat' x ys
  end.

Fixpoint car_concat
  (x y : list (list ((myOpAux * list nposi)%type)))
  : list (list ((myOpAux * list nposi)%type)) :=
  match x with
  | [] => []
  | a :: xs => car_concat' a y ++ car_concat xs y
  end.

Fixpoint get_first (l : list (list ((N * myOp)%type))) : list ((N * myOp)%type) :=
  match l with
  | [] => []
  | [] :: xs => get_first xs
  | (a :: _) :: ys => a :: get_first ys
  end.

Fixpoint in_list_a (x : (N * myOp)%type) (l : list ((N * myOp)%type)) : bool :=
  match l with
  | [] => false
  | a :: xs => if N.eqb (fst x) (fst a) then true else in_list_a x xs
  end.

Fixpoint remove_first
  (l : list (list ((N * myOp)%type)))
  (x : list ((N * myOp)%type))
  : list (list ((N * myOp)%type)) :=
  match l with
  | [] => []
  | [] :: xs => [] :: remove_first xs x
  | (a :: xs) :: ys =>
      if in_list_a a x
      then xs :: remove_first ys x
      else (a :: xs) :: remove_first ys x
  end.

Fixpoint grab_related'
  (x : (N * myOp)%type)
  (l : list ((N * myOp)%type))
  (re : hb_relation)
  (acc : list ((N * myOp)%type))
  : list ((N * myOp)%type) :=
  match l with
  | [] => acc
  | a :: xs =>
      if re (fst x) (fst a)
      then grab_related' x xs re acc
      else grab_related' x xs re (acc ++ [a])
  end.

Fixpoint up_qubits (x : var) (i : nat) (n : nat) (acc : list nposi) : list nposi :=
  match n with
  | O => acc
  | S m =>
      up_qubits x i m
        (acc ++ [(N.of_nat x, N.add (N.of_nat i) (N.of_nat m))])
  end.

Fixpoint cutToQubits' (l : list range) : list nposi :=
  match l with
  | [] => []
  | (x, (l0, r)) :: xs => up_qubits x l0 (Nat.sub r l0) [] ++ cutToQubits' xs
  end.

Definition cutToQubits (l : list range) : list nposi :=
  cutToQubits' (SortRange.sort l).

Fixpoint get_locus_in_op (l : list ((N * myOp)%type)) : list range :=
  match l with
  | [] => []
  | (_, OpAP y) :: la =>
      match get_locus y with
      | [] => get_locus_in_op la
      | re => re ++ get_locus_in_op la
      end
  | (_, OpIf _ _ _) :: la => get_locus_in_op la
  end.

Fixpoint get_nlocus
  (l : list ((N * myOp)%type))
  : list ((myOpAux * list nposi)%type) :=
  match l with
  | [] => []
  | x :: xs =>
      (OpNum (fst x), cutToQubits (get_locus_in_op (x :: nil))) :: get_nlocus xs
  end.

Fixpoint assign_each
  (n : nat)
  (l : list (list ((N * myOp)%type)))
  (re : hb_relation)
  (acc : list (list ((myOpAux * list nposi)%type)))
  : list (list ((myOpAux * list nposi)%type)) :=
  match n with
  | O => acc
  | S m =>
      match get_first l with
      | [] => acc
      | p :: l0 =>
          let good := grab_related' p l0 re [p] in
          let next_acc := car_concat acc (permutations_one (get_nlocus good)) in
          assign_each m (remove_first l good) re next_acc
      end
  end.

Definition gen_seq
  (l : list ((N * myOp)%type))
  (re : hb_relation)
  : ((list ((myOpAux * list nposi)%type) *
      list (list ((myOpAux * list nposi)%type)))%type) :=
  let can := partition_op l in
  match can with
  | [] => ([], [])
  | x :: xs => (get_nlocus x, assign_each (Nat.sub (length l) (length x)) xs re [[]])
  end.

Fixpoint count_a
  (new0 : list ((myOpAux * list nposi)%type))
  (l : list membrane_id)
  (acc : list (((myOpAux * list nposi)%type * membrane_id)%type))
  : (list (((myOpAux * list nposi)%type * membrane_id)%type) *
     list ((myOpAux * list nposi)%type))%type :=
  match l with
  | [] => (acc, new0)
  | a :: ys =>
      match new0 with
      | [] => (acc, [])
      | x :: xs => count_a xs ys ((x, a) :: acc)
      end
  end.

Fixpoint gen_mem_new'
  (t : nat)
  (news : list ((myOpAux * list nposi)%type))
  (l : list membrane_id)
  (acc : list (((myOpAux * list nposi)%type * membrane_id)%type))
  : list (((myOpAux * list nposi)%type * membrane_id)%type) :=
  match t with
  | O => acc
  | S m =>
      let '(re, next) := count_a news l [] in
      gen_mem_new' m next l (acc ++ re)
  end.

Definition gen_mem_new
  (news : list ((myOpAux * list nposi)%type))
  (l : list membrane_id)
  : list (((myOpAux * list nposi)%type * membrane_id)%type) :=
  match l with
  | [] => []
  | _ =>
      let v := Nat.add (Nat.div (length news) (length l)) 1%nat in
      gen_mem_new' v news l []
  end.

Fixpoint insert_posis
  (l : list ((membrane_id * list nposi)%type))
  (a : membrane_id)
  (x : list nposi)
  : list ((membrane_id * list nposi)%type) :=
  match l with
  | [] => []
  | (n, y) :: ys =>
      if Nat.eqb a n then (n, y ++ x) :: ys else (n, y) :: insert_posis ys a x
  end.

Fixpoint turn_new
  (l : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (acc : list ((membrane_id * list nposi)%type))
  : list ((membrane_id * list nposi)%type) :=
  match l with
  | [] => acc
  | (x, y) :: xs => turn_new xs (insert_posis acc y (snd x))
  end.

Fixpoint posi_set_in (a : nposi) (l : list nposi) : bool :=
  match l with
  | [] => false
  | x :: xs => if nposi_eq a x then true else posi_set_in a xs
  end.

Fixpoint set_inter0
  (x y : list nposi)
  (acc : (list nposi * list nposi)%type)
  : (list nposi * list nposi)%type :=
  match x with
  | [] => acc
  | a :: xs =>
      if posi_set_in a y
      then set_inter0 xs y (a :: fst acc, snd acc)
      else set_inter0 xs y (fst acc, a :: snd acc)
  end.

Fixpoint dec_mem (l : list ((list nposi * membrane_id)%type)) (x : nposi) : option membrane_id :=
  match l with
  | [] => None
  | (y, i) :: ys => if posi_set_in x y then Some i else dec_mem ys x
  end.

Fixpoint search_mem
  (new0 : list ((membrane_id * list nposi)%type))
  (x : list nposi)
  (acc : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  : list ((membrane_id * ((list nposi * list nposi)%type))%type) :=
  match new0 with
  | [] => acc
  | (i, y) :: ys =>
      let inter := set_inter0 x y ([], []) in
      search_mem ys x ((i, inter) :: acc)
  end.

Fixpoint all_no_mem
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type)) : bool :=
  match l with
  | [] => true
  | (_, ([], _)) :: ys => all_no_mem ys
  | _ :: _ => false
  end.

Fixpoint is_one_mem
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type)) : bool :=
  match l with
  | [] => false
  | (_, ([], _)) :: ys => is_one_mem ys
  | _ :: ys => all_no_mem ys
  end.

Fixpoint get_one
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  : option membrane_id :=
  match l with
  | [] => None
  | (a, ([], _)) :: ys => get_one ys
  | (a, _) :: _ => Some a
  end.

Fixpoint grab_good
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (acc : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  : list ((membrane_id * ((list nposi * list nposi)%type))%type) :=
  match l with
  | [] => acc
  | (a, ([], _)) :: ys => grab_good ys acc
  | (a, (ha, hb)) :: ys => grab_good ys ((a, (ha, hb)) :: acc)
  end.

Fixpoint nlength {A : Type} (l : list A) : N :=
  match l with
  | [] => 0%N
  | _ :: xs => N.add 1%N (nlength xs)
  end.

Fixpoint max_one
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (v : N)
  (acc : (membrane_id * ((list nposi * list nposi)%type))%type)
  (accb : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  : ((membrane_id * ((list nposi * list nposi)%type))%type *
     list ((membrane_id * ((list nposi * list nposi)%type))%type))%type :=
  match l with
  | [] => (acc, accb)
  | (i, y) :: ys =>
      if N.ltb v (nlength (fst y))
      then max_one ys (nlength (fst y)) (i, y) (acc :: accb)
      else max_one ys v acc ((i, y) :: accb)
  end.

Fixpoint max_mem_id
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (v : membrane_id)
  (acc : (list nposi * list nposi)%type)
  (accb : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  : (((membrane_id * ((list nposi * list nposi)%type))%type) *
     (list ((membrane_id * ((list nposi * list nposi)%type))%type)))%type :=
  match l with
  | [] => ((v, acc), accb)
  | (i, y) :: ys =>
      if Nat.ltb v i
      then max_mem_id ys i y ((v, acc) :: accb)
      else max_mem_id ys v acc ((i, y) :: accb)
  end.

Fixpoint gen_comm'
  (i j : membrane_id)
  (l : list nposi)
  (chan : var)
  (acc : list (((myOpAux * list nposi)%type * membrane_id)%type))
  : list (((myOpAux * list nposi)%type * membrane_id)%type) :=
  match l with
  | [] => acc
  | x :: xs =>
      gen_comm' i j xs (Nat.succ chan)
        ((((OpExp (Recv chan (N.to_nat (fst x)) (N.to_nat (snd x)))), [x]), j) ::
         (((OpExp (Send chan (N.to_nat (fst x)) (N.to_nat (snd x)))), [x]), i) :: acc)
  end.

Fixpoint gen_comm
  (j : membrane_id)
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (chan : var)
  (acc accb : list (((myOpAux * list nposi)%type * membrane_id)%type))
  : (var *
     (list (((myOpAux * list nposi)%type * membrane_id)%type) *
      list (((myOpAux * list nposi)%type * membrane_id)%type)))%type :=
  match l with
  | [] => (chan, (acc, accb))
  | (i, (x, _)) :: xs =>
      gen_comm j xs (Nat.add chan (Nat.mul 2%nat (length x)))
        (gen_comm' j i x chan acc)
        (gen_comm' i j x chan accb)
  end.

Definition gen_comm_insert
  (j : membrane_id)
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (chan : var)
  (acc : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (v : (((myOpAux * list nposi)%type * membrane_id)%type))
  : (var * list (((myOpAux * list nposi)%type * membrane_id)%type))%type :=
  let mid := gen_comm j l chan acc [] in
  (fst mid, snd (snd mid) ++ v :: fst (snd mid)).

Fixpoint gen_comm_b
  (j : membrane_id)
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (chan : var)
  (acc : list (((myOpAux * list nposi)%type * membrane_id)%type))
  : (var * list (((myOpAux * list nposi)%type * membrane_id)%type))%type :=
  match l with
  | [] => (chan, acc)
  | (i, (x, _)) :: xs =>
      gen_comm_b j xs (Nat.add chan (length x)) (gen_comm' j i x chan acc)
  end.

Fixpoint collect_all_posi
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (acc : list nposi)
  : list nposi :=
  match l with
  | [] => acc
  | (_, (x, _)) :: xs => collect_all_posi xs (x ++ acc)
  end.

Fixpoint push_to_mem_i
  (i j : membrane_id)
  (v : list nposi)
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (acc : list ((membrane_id * list nposi)%type))
  : list ((membrane_id * list nposi)%type) :=
  match l with
  | [] => acc
  | (k, (x, y)) :: xs =>
      if Nat.eqb i k
      then push_to_mem_i i j v xs ((k, v ++ y) :: acc)
      else if Nat.eqb j k
           then push_to_mem_i i j v xs ((k, x ++ y) :: acc)
           else push_to_mem_i i j v xs ((k, y) :: acc)
  end.

Definition post_dec
  (i : membrane_id)
  (new0 : list ((membrane_id * list nposi)%type))
  (dc : list ((list nposi * membrane_id)%type))
  (xnum : N)
  (xset : list nposi)
  (chan : var)
  (rea input : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (acc : list (((myOpAux * list nposi)%type * membrane_id)%type))
  : (var *
     list ((list (((myOpAux * list nposi)%type * membrane_id)%type) *
            list ((membrane_id * list nposi)%type))%type))%type :=
  let v := collect_all_posi rea [] in
  match v with
  | [] => (chan, [])
  | y :: _ =>
      match dec_mem dc y with
      | Some j =>
          let mid := gen_comm_insert i rea chan acc ((OpNum xnum, xset), i) in
          let pre_gen := gen_comm_b i rea (fst mid) acc in
          let post_gen :=
            gen_comm' i j v (fst pre_gen) (((OpNum xnum, xset), i) :: snd pre_gen) in
          (Nat.add (fst pre_gen) (length v),
           [((((OpNum xnum, xset), i) :: snd mid), new0);
            (post_gen, push_to_mem_i j i v input [])])
      | None =>
          let pre_gen := gen_comm_insert i rea chan acc ((OpNum xnum, xset), i) in
          (fst pre_gen, [(snd pre_gen, new0)])
      end
  end.

Fixpoint mem_pos (p : nposi) (xs : list nposi) : bool :=
  match xs with
  | [] => false
  | y :: ys => if nposi_eq y p then true else mem_pos p ys
  end.

Fixpoint add_nodup (xs ys : list nposi) : list nposi :=
  match xs with
  | [] => ys
  | x :: tl => if mem_pos x ys then add_nodup tl ys else add_nodup tl (x :: ys)
  end.

Fixpoint add_qubits_to_mem
  (i : membrane_id)
  (xs : list nposi)
  (new0 : list ((membrane_id * list nposi)%type))
  : list ((membrane_id * list nposi)%type) :=
  match new0 with
  | [] => []
  | (j, ys) :: tl =>
      if Nat.eqb i j
      then (j, add_nodup xs ys) :: add_qubits_to_mem i xs tl
      else (j, ys) :: add_qubits_to_mem i xs tl
  end.

Fixpoint assoc_opt_mem
  (i : membrane_id)
  (new0 : list ((membrane_id * list nposi)%type))
  : option (list nposi) :=
  match new0 with
  | [] => None
  | (j, xs) :: tl => if Nat.eqb i j then Some xs else assoc_opt_mem i tl
  end.

Definition mem_qubit_load (new0 : list ((membrane_id * list nposi)%type)) (i : membrane_id) : nat :=
  match assoc_opt_mem i new0 with
  | Some xs => length xs
  | None => 0%nat
  end.

Definition membrane_capacity : nat := 8%nat.
Definition op_capacity : nat := 6%nat.

Definition mem_has_capacity
  (new0 : list ((membrane_id * list nposi)%type))
  (i : membrane_id)
  (xset : list nposi) : bool :=
  let current := mem_qubit_load new0 i in
  Nat.leb (Nat.add current (length xset)) membrane_capacity.

Fixpoint op_load_in_partial
  (l : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (mid : membrane_id) : nat :=
  match l with
  | [] => 0%nat
  | (((_, _), m)) :: xs =>
      if Nat.eqb m mid
      then Nat.succ (op_load_in_partial xs mid)
      else op_load_in_partial xs mid
  end.

Definition overlap_size (x y : list nposi) : nat :=
  length (fst (set_inter0 x y ([], []))).

Definition import_cost (xset local_qs : list nposi) : nat :=
  Nat.sub (length xset) (overlap_size xset local_qs).

Definition score_mem_for_op
  (partial : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (xset : list nposi)
  (mid : membrane_id)
  (local_qs : list nposi) : nat :=
  let imports := import_cost xset local_qs in
  let opl := op_load_in_partial partial mid in
  Nat.add (Nat.mul 4%nat imports) (Nat.mul 5%nat opl).

Definition over_op_capacity
  (partial : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (mid : membrane_id) : bool :=
  Nat.ltb op_capacity (op_load_in_partial partial mid).

Fixpoint insert_scored_candidate
  (cand : scored_cand)
  (scored : list scored_cand) : list scored_cand :=
  match scored with
  | [] => [cand]
  | ((s1, m1, d1) as c1) :: tl =>
      let '(s, _, _) := cand in
      if Nat.ltb s s1 then cand :: scored else c1 :: insert_scored_candidate cand tl
  end.

Fixpoint take_scored (n : nat) (xs : list scored_cand) : list scored_cand :=
  match n, xs with
  | O, _ => []
  | _, [] => []
  | S n', x :: tl => x :: take_scored n' tl
  end.

Fixpoint scored_candidates
  (new0 : list ((membrane_id * list nposi)%type))
  (partial : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (xset : list nposi)
  (candidates : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  : list scored_cand :=
  match candidates with
  | [] => []
  | (mid, (local_qs, rest_qs)) :: tl =>
      if orb (over_op_capacity partial mid)
             (negb (mem_has_capacity new0 mid xset))
      then scored_candidates new0 partial xset tl
      else
        let s := score_mem_for_op partial xset mid local_qs in
        insert_scored_candidate (s, mid, (local_qs, rest_qs))
          (scored_candidates new0 partial xset tl)
  end.

Fixpoint scored_candidates_nocap
  (partial : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (xset : list nposi)
  (candidates : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  : list scored_cand :=
  match candidates with
  | [] => []
  | (mid, (local_qs, rest_qs)) :: tl =>
      if over_op_capacity partial mid
      then scored_candidates_nocap partial xset tl
      else
        let s := score_mem_for_op partial xset mid local_qs in
        insert_scored_candidate (s, mid, (local_qs, rest_qs))
          (scored_candidates_nocap partial xset tl)
  end.

Fixpoint build_choices
  (cs : list scored_cand)
  (re : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (new0 : list ((membrane_id * list nposi)%type))
  (dc : list ((list nposi * membrane_id)%type))
  (xnum : N)
  (xset : list nposi)
  (l : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (chan : var)
  (acc :
     list ((list (((myOpAux * list nposi)%type * membrane_id)%type) *
            list ((membrane_id * list nposi)%type))%type))
  : list ((list (((myOpAux * list nposi)%type * membrane_id)%type) *
           list ((membrane_id * list nposi)%type))%type) :=
  match cs with
  | [] => acc
  | (_, chosen_mid, _) :: tl =>
      if is_one_mem re then
        let choice := (((((OpNum xnum), xset), chosen_mid) :: l), new0) in
        build_choices tl re new0 dc xnum xset l chan (choice :: acc)
      else
        let others := filter (fun p => negb (Nat.eqb (fst p) chosen_mid)) re in
        let mid_res := post_dec chosen_mid new0 dc xnum xset chan others re l in
        let choices := snd mid_res in
        build_choices tl re new0 dc xnum xset l chan (choices ++ acc)
  end.

Definition assign_mem_s
  (new0 : list ((membrane_id * list nposi)%type))
  (dc : list ((list nposi * membrane_id)%type))
  (x : (N * list nposi)%type)
  (l : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (chan : var)
  : (var *
     list ((list (((myOpAux * list nposi)%type * membrane_id)%type) *
            list ((membrane_id * list nposi)%type))%type))%type :=
  let xset := snd x in
  let re :=
    search_mem new0 xset
      ([] : list ((membrane_id * ((list nposi * list nposi)%type))%type)) in
  match re with
  | [] => (chan, [])
  | _ =>
      let ranked :=
        match scored_candidates new0 l xset re with
        | [] => scored_candidates_nocap l xset re
        | ys => ys
        end in
      let top := take_scored 3%nat ranked in
      (chan,
       build_choices top re new0 dc (fst x) xset l chan
         ([] :
           list ((list (((myOpAux * list nposi)%type * membrane_id)%type) *
                  list ((membrane_id * list nposi)%type))%type)))
  end.

Definition channel : var := 6%nat.

Fixpoint assign_mem'
  (dc : list ((list nposi * membrane_id)%type))
  (l : list ((myOpAux * list nposi)%type))
  (acc :
     (var *
      list ((list (((myOpAux * list nposi)%type * membrane_id)%type) *
             list ((membrane_id * list nposi)%type))%type))%type)
  : (var *
     list ((list (((myOpAux * list nposi)%type * membrane_id)%type) *
            list ((membrane_id * list nposi)%type))%type))%type :=
  match l with
  | [] => acc
  | (OpNum x, y) :: xs =>
      assign_mem' dc xs
        (fold_left
           (fun a b =>
              let mid := assign_mem_s (snd b) dc (x, y) (fst b) (fst a) in
              (fst mid, snd a ++ snd mid))
           (snd acc) (fst acc, []))
  | _ :: xs => assign_mem' dc xs acc
  end.

Fixpoint assign_mem_more
  (new0 : list ((membrane_id * list nposi)%type))
  (dc : list ((list nposi * membrane_id)%type))
  (l : list (list ((myOpAux * list nposi)%type)))
  (acc : list (list (((myOpAux * list nposi)%type * membrane_id)%type)))
  : list (list (((myOpAux * list nposi)%type * membrane_id)%type)) :=
  match l with
  | [] => acc
  | x :: xs =>
      let seed :=
        (channel,
         [ (([] : list (((myOpAux * list nposi)%type * membrane_id)%type)), new0) ]) in
      assign_mem_more new0 dc xs
        (map (fun l0 => rev l0)
             (fst (split (snd (assign_mem' dc x seed))))
         ++ acc)
  end.

Fixpoint find_empty_new'
  (l : list ((membrane_id * list nposi)%type))
  (m : membrane_id)
  (acc : list membrane_id)
  : list membrane_id :=
  match l with
  | [] => m :: acc
  | (x, _) :: xs => if Nat.eqb x m then acc else find_empty_new' xs m acc
  end.

Fixpoint find_empy_new
  (l : list ((membrane_id * list nposi)%type))
  (al acc : list membrane_id)
  : list membrane_id :=
  match al with
  | [] => acc
  | x :: xs => find_empy_new l xs (find_empty_new' l x acc)
  end.

Fixpoint assign_new_mem
  (l : list ((myOpAux * list nposi)%type))
  (al : list membrane_id)
  : list ((list nposi * membrane_id)%type) :=
  match al with
  | [] => []
  | x :: xs =>
      match l with
      | [] => []
      | y :: ys => (snd y, x) :: assign_new_mem ys xs
      end
  end.

Fixpoint gen_empty_mem (m : list membrane_id) : list ((membrane_id * list nposi)%type) :=
  match m with
  | [] => []
  | a :: xl => (a, []) :: gen_empty_mem xl
  end.

Fixpoint take {A : Type} (n : nat) (xs : list A) : list A :=
  match n, xs with
  | O, _ => []
  | _, [] => []
  | S n', x :: tl => x :: take n' tl
  end.

Definition fallback_mid
  (ql : list (((myOpAux * list nposi)%type * membrane_id)%type)) : membrane_id :=
  match ql with
  | [] => 0%nat
  | (_, mid) :: _ => mid
  end.

Definition gen_mem
  (news : list ((myOpAux * list nposi)%type))
  (l : list (list ((myOpAux * list nposi)%type)))
  (ids : list membrane_id)
  : list (list (((myOpAux * list nposi)%type * membrane_id)%type)) :=
  let ql := gen_mem_new news ids in
  let vl := turn_new (gen_mem_new news ids) [] in
  let al := find_empy_new vl ids [] in
  let dc := assign_new_mem news al in
  let base_new0 := gen_empty_mem al ++ vl in
  let res := map (fun a => ql ++ a) (assign_mem_more base_new0 dc l []) in
  match res with
  | [] =>
      let mid := fallback_mid ql in
      match take 3%nat l with
      | [] => [ql]
      | xs => map (fun x => ql ++ map (fun y => (y, mid)) x) xs
      end
  | _ => res
  end.

Fixpoint insert_mem_id
  (i : membrane_id)
  (x : (myOpAux * list nposi)%type)
  (acc : list ((membrane_id * list ((myOpAux * list nposi)%type))%type))
  : list ((membrane_id * list ((myOpAux * list nposi)%type))%type) :=
  match acc with
  | [] => [(i, [x])]
  | (a, b) :: xs =>
      if Nat.eqb i a
      then (a, b ++ [x]) :: xs
      else (a, b) :: insert_mem_id i x xs
  end.

Fixpoint distribute_op
  (l : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (acc : list ((membrane_id * list ((myOpAux * list nposi)%type))%type))
  : list ((membrane_id * list ((myOpAux * list nposi)%type))%type) :=
  match l with
  | [] => acc
  | x :: xs => distribute_op xs (insert_mem_id (snd x) (fst x) acc)
  end.

Fixpoint get_op (l : list ((N * myOp)%type)) (i : N) : option myOp :=
  match l with
  | [] => None
  | (x, y) :: xs => if N.eqb i x then Some y else get_op xs i
  end.

Fixpoint turn_cexp_to_proc (l : list cexp) (p : process) : process :=
  match l with
  | [] => p
  | x :: xs => AP x (turn_cexp_to_proc xs p)
  end.

Definition turn_op_to_proc (x : myOp) (p : process) : process :=
  match x with
  | OpAP a => AP a p
  | OpIf b l r => PIf b (turn_cexp_to_proc l p) (turn_cexp_to_proc r p)
  end.

Fixpoint to_process
  (l : list ((myOpAux * list nposi)%type))
  (os : list ((N * myOp)%type))
  : option process :=
  match l with
  | [] => Some PNil
  | (OpNum n, _) :: xs =>
      match get_op os n, to_process xs os with
      | Some x, Some p => Some (turn_op_to_proc x p)
      | _, _ => None
      end
  | (OpExp a, _) :: xs =>
      match to_process xs os with
      | Some p => Some (AP a p)
      | None => None
      end
  end.

Fixpoint to_prog
  (l : list ((nat * list ((myOpAux * list nposi)%type))%type))
  (os : list ((N * myOp)%type))
  : list memb :=
  match l with
  | [] => []
  | x :: xs =>
      match to_process (snd x) os with
      | None => []
      | Some a => Memb (fst x) a :: to_prog xs os
      end
  end.

Fixpoint has_if_ops (os : list ((N * myOp)%type)) : bool :=
  match os with
  | [] => false
  | (_, OpIf _ _ _) :: _ => true
  | _ :: xs => has_if_ops xs
  end.

Fixpoint owner_of_pos
  (owners : list ((nposi * membrane_id)%type))
  (p : nposi) : option membrane_id :=
  match owners with
  | [] => None
  | (q, mid) :: xs =>
      if nposi_eq q p then Some mid else owner_of_pos xs p
  end.

Fixpoint set_owner
  (owners : list ((nposi * membrane_id)%type))
  (p : nposi)
  (mid : membrane_id)
  : list ((nposi * membrane_id)%type) :=
  match owners with
  | [] => [(p, mid)]
  | (q, m) :: xs =>
      if nposi_eq q p
      then (p, mid) :: xs
      else (q, m) :: set_owner xs p mid
  end.

Fixpoint set_owner_many
  (owners : list ((nposi * membrane_id)%type))
  (ps : list nposi)
  (mid : membrane_id)
  : list ((nposi * membrane_id)%type) :=
  match ps with
  | [] => owners
  | p :: xs => set_owner_many (set_owner owners p mid) xs mid
  end.

Fixpoint append_cexp_to_mem
  (mid : membrane_id)
  (ce : cexp)
  (acc : list ((membrane_id * list cexp)%type))
  : list ((membrane_id * list cexp)%type) :=
  match acc with
  | [] => [(mid, [ce])]
  | (m, xs) :: tl =>
      if Nat.eqb mid m
      then (m, xs ++ [ce]) :: tl
      else (m, xs) :: append_cexp_to_mem mid ce tl
  end.

Fixpoint add_initial_owners_from_solution
  (sol : list ((((myOpAux * list nposi)%type) * membrane_id)%type))
  (os : list ((N * myOp)%type))
  (owners : list ((nposi * membrane_id)%type))
  : list ((nposi * membrane_id)%type) :=
  match sol with
  | [] => owners
  | ((aux, qs), mid) :: xs =>
      let owners' :=
        match aux with
        | OpNum n =>
            match get_op os n with
            | Some (OpAP (CNew r)) =>
                set_owner_many owners (cutToQubits (r :: nil)) mid
            | _ => owners
            end
        | OpExp (CNew r) =>
            set_owner_many owners (cutToQubits (r :: nil)) mid
        | _ => owners
        end
      in
      add_initial_owners_from_solution xs os owners'
  end.



Fixpoint ensure_local_qubits_aux
  (dst : membrane_id)
  (qs : list nposi)
  (owners : list ((nposi * membrane_id)%type))
  (bufs : list ((membrane_id * list cexp)%type))
  (chan : var)
  : (var * list ((nposi * membrane_id)%type) * list ((membrane_id * list cexp)%type))%type :=
  match qs with
  | [] => (chan, owners, bufs)
  | q :: tl =>
      match owner_of_pos owners q with
      | Some src =>
          if Nat.eqb src dst then
            ensure_local_qubits_aux dst tl owners bufs chan
          else
            let v := N.to_nat (fst q) in
            let idx := N.to_nat (snd q) in
            let bufs1 := append_cexp_to_mem src (Send chan v idx) bufs in
            let bufs2 := append_cexp_to_mem dst (Recv chan v idx) bufs1 in
            let owners' := set_owner owners q dst in
            ensure_local_qubits_aux dst tl owners' bufs2 (Nat.succ chan)
      | None =>
          ensure_local_qubits_aux dst tl owners bufs chan
      end
  end.

Definition ensure_local_qubits := ensure_local_qubits_aux.

Fixpoint to_prog_from_cexps
  (grouped : list ((membrane_id * list cexp)%type)) : config :=
  match grouped with
  | [] => []
  | (mid, ces) :: xs => Memb mid (turn_cexp_to_proc ces PNil) :: to_prog_from_cexps xs
  end.

Fixpoint lower_solution_distributed_go
  (xs : list ((((myOpAux * list nposi)%type) * membrane_id)%type))
  (os : list ((N * myOp)%type))
  (owners : list ((nposi * membrane_id)%type))
  (bufs : list ((membrane_id * list cexp)%type))
  (chan : var)
  : config :=
  match xs with
  | [] => to_prog_from_cexps bufs
  | ((aux, qs), mid) :: tl =>
      match aux with
      | OpExp ce =>
          match ce with
          | CNew r =>
              let owners' := set_owner_many owners (cutToQubits (r :: nil)) mid in
              let bufs' := append_cexp_to_mem mid ce bufs in
              lower_solution_distributed_go tl os owners' bufs' chan
          | Recv _ x y =>
              let owners' := set_owner owners (N.of_nat x, N.of_nat y) mid in
              let bufs' := append_cexp_to_mem mid ce bufs in
              lower_solution_distributed_go tl os owners' bufs' chan
          | _ =>
              let bufs' := append_cexp_to_mem mid ce bufs in
              lower_solution_distributed_go tl os owners bufs' chan
          end
      | OpNum n =>
          match get_op os n with
          | Some (OpAP ce) =>
              match ce with
              | CNew r =>
                  let owners' := set_owner_many owners (cutToQubits (r :: nil)) mid in
                  let bufs' := append_cexp_to_mem mid ce bufs in
                  lower_solution_distributed_go tl os owners' bufs' chan
              | CAppU loc e =>
                  let qbs := cutToQubits loc in
                  let tmp := ensure_local_qubits mid qbs owners bufs chan in
                  let p1 := fst tmp in
                  let chan' := fst p1 in
                  let owners' := snd p1 in
                  let bufs' := snd tmp in
                  let bufs'' := append_cexp_to_mem mid (CAppU loc e) bufs' in
                  lower_solution_distributed_go tl os owners' bufs'' chan'
              | CMeas x loc =>
                  let qbs := cutToQubits loc in
                  let tmp := ensure_local_qubits mid qbs owners bufs chan in
                  let p1 := fst tmp in
                  let chan' := fst p1 in
                  let owners' := snd p1 in
                  let bufs' := snd tmp in
                  let bufs'' := append_cexp_to_mem mid (CMeas x loc) bufs' in
                  lower_solution_distributed_go tl os owners' bufs'' chan'
              | Send _ _ _ =>
                  let bufs' := append_cexp_to_mem mid ce bufs in
                  lower_solution_distributed_go tl os owners bufs' chan
              | Recv _ _ _ =>
                  let bufs' := append_cexp_to_mem mid ce bufs in
                  lower_solution_distributed_go tl os owners bufs' chan
              end
          | _ =>
              lower_solution_distributed_go tl os owners bufs chan
          end
      end
  end.



Definition lower_solution_distributed
  (sol : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (os : list ((N * myOp)%type))
  : config :=
  let owners0 := add_initial_owners_from_solution sol os [] in
  lower_solution_distributed_go sol os owners0 [] 100000%nat.

Fixpoint gen_prog
  (l : list (list (((myOpAux * list nposi)%type * membrane_id)%type)))
  (os : list ((N * myOp)%type))
  : list config :=
  if has_if_ops os then
    match l with
    | [] => []
    | x :: xs => to_prog (distribute_op x []) os :: gen_prog xs os
    end
  else
    match l with
    | [] => []
    | x :: xs => lower_solution_distributed x os :: gen_prog xs os
    end.

Fixpoint count_send_in_process (p : process) : nat :=
  match p with
  | PNil => 0%nat
  | AP a p' =>
      match a with
      | Send _ _ _ => Nat.succ (count_send_in_process p')
      | Recv _ _ _ => Nat.succ (count_send_in_process p')
      | _ => count_send_in_process p'
      end
  | PIf _ p1 p2 => Nat.add (count_send_in_process p1) (count_send_in_process p2)
  end.

Definition count_send_in_memb (m : memb) : nat :=
  match m with
  | Memb _ p => count_send_in_process p
  end.

Fixpoint count_comm_ops (cfg : config) : nat :=
  match cfg with
  | [] => 0%nat
  | m :: xs => Nat.add (count_send_in_memb m) (count_comm_ops xs)
  end.

Fixpoint process_size (p : process) : nat :=
  match p with
  | PNil => 0%nat
  | AP _ p' => Nat.succ (process_size p')
  | PIf _ p1 p2 => Nat.add (process_size p1) (process_size p2)
  end.

Definition memb_load (m : memb) : nat :=
  match m with
  | Memb _ p => process_size p
  end.

Fixpoint max_load (cfg : config) : nat :=
  match cfg with
  | [] => 0%nat
  | m :: xs => Nat.max (memb_load m) (max_load xs)
  end.

Definition alpha : nat := 10%nat.

Definition fit (cfg : config) : fitness_value :=
  Nat.add (Nat.mul alpha (count_comm_ops cfg)) (max_load cfg).

Fixpoint best_prog_aux
  (best : config)
  (bestv : nat)
  (xs : list config)
  : config :=
  match xs with
  | [] => best
  | x :: tl =>
      let vx := fit x in
      if Nat.ltb vx bestv
      then best_prog_aux x vx tl
      else best_prog_aux best bestv tl
  end.

Definition best_prog (xs : list config) : option config :=
  match xs with
  | [] => None
  | x :: tl => Some (best_prog_aux x (fit x) tl)
  end.

Definition autodisq_all
  (ops : op_list)
  (mids : list membrane_id)
  : list config :=
  let os := opListOrder ops in
  let hb := gen_hb os in
  let sq := gen_seq os hb in
  let mem := gen_mem (fst sq) (snd sq) mids in
  gen_prog mem os.

Definition autodisq_best
  (ops : op_list)
  (mids : list membrane_id)
  : option config :=
  best_prog (autodisq_all ops mids).

Fixpoint auto_disq_loop
  (best : option config)
  (cands : list config)
  : option config :=
  match cands with
  | [] => best
  | P :: xs =>
      match best with
      | None => auto_disq_loop (Some P) xs
      | Some B =>
          if Nat.ltb (fit P) (fit B)
          then auto_disq_loop (Some P) xs
          else auto_disq_loop best xs
      end
  end.

Definition autodisq_first
  (ops : list ((N * myOp)%type))
  (mids : list membrane_id)
  : option config :=
  let nl := get_nlocus ops in
  let init := gen_mem_new nl mids in
  let new0 := turn_new init [] in
  let dc := ([] : list ((list nposi * membrane_id)%type)) in
  let sols := assign_mem_more new0 dc (map (fun x => [x]) nl) [] in
  match sols with
  | [] => None
  | sol :: _ => Some (lower_solution_distributed sol ops)
  end.

Definition autodisq_best_1
  (ops : op_list)
  (mids : list membrane_id)
  : option config :=
  auto_disq_loop None (autodisq_all ops mids).










(**
From Coq Require Import List Arith Bool Nat NArith Lia.
Import ListNotations.

Require Import Coq.Sorting.Mergesort.
Require Import Coq.Structures.Orders.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import QArith.

Local Open Scope nat_scope.
Local Open Scope list_scope.
Local Open Scope N_scope.

Require Import QuantumLib.Prelim.
Require Import DisQ.BasicUtility.
Require Import DisQ.DisQSyntax.

Definition membrane    : Type := memb.
Definition membranes   : Type := config.
Definition membrane_id : Type := var.

Inductive myOp : Type :=
| OpAP  (a : cexp)
| OpIf  (b : cbexp) (p q : list cexp).

Definition op_list : Type := list myOp.
Definition hb_relation : Type := N -> N -> bool.
Definition rank : Type := N.
Definition seq_relation : Type := myOp -> rank.
Definition op_mem_assign : Type := myOp -> membrane_id.

Inductive myOpAux : Type :=
| OpNum (n : N)
| OpExp (a : cexp).

Definition qubit_mem_assign : Type := var -> membrane_id.
Definition fitness_value : Type := nat.
Definition distributed_prog : Type := config.

(* ------------------------------------------------------------------------- *)
(* Equality helpers                                                          *)
(* ------------------------------------------------------------------------- *)

Fixpoint list_eqb {A : Type} (beq : A -> A -> bool) (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => andb (beq x y) (list_eqb beq xs' ys')
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
  | AModMult a1 b1 c1, AModMult a2 b2 c2 =>
      andb (aexp_eqb a1 a2)
           (andb (aexp_eqb b1 b2) (aexp_eqb c1 c2))
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

Definition range_eqb (r1 r2 : range) : bool :=
  match r1, r2 with
  | (x1, (lo1, hi1)), (x2, (lo2, hi2)) =>
      andb (Nat.eqb x1 x2)
           (andb (Nat.eqb lo1 lo2) (Nat.eqb hi1 hi2))
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
      andb (Nat.eqb x1 x2)
           (andb (aexp_eqb a1 a2) (exp_eqb e1' e2'))
  | RZ q1 x1 a1, RZ q2 x2 a2 =>
      andb (Nat.eqb q1 q2)
           (andb (Nat.eqb x1 x2) (aexp_eqb a1 a2))
  | RRZ q1 x1 a1, RRZ q2 x2 a2 =>
      andb (Nat.eqb q1 q2)
           (andb (Nat.eqb x1 x2) (aexp_eqb a1 a2))
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

(* ------------------------------------------------------------------------- *)
(* Sorting ranges                                                            *)
(* ------------------------------------------------------------------------- *)

Module RangeOrder <: TotalLeBool'.
  Definition t := range.

  Definition leb (x y : range) : bool :=
    if Nat.ltb (fst x) (fst y) then true
    else if Nat.eqb (fst x) (fst y) then
           if Nat.ltb (fst (snd x)) (fst (snd y)) then true
           else if Nat.eqb (fst (snd x)) (fst (snd y))
                then Nat.leb (snd (snd x)) (snd (snd y))
                else false
    else false.

  Infix "[<=]" := leb (at level 50).

  Theorem leb_total : forall x y, (x [<=] y) = true \/ (y [<=] x) = true.
  Proof.
    intros [vx [lx hx]] [vy [ly hy]].
    unfold leb; simpl.
    destruct (Nat.ltb vx vy) eqn:Hvxy.
    - left; reflexivity.
    - destruct (Nat.eqb vx vy) eqn:Heqv.
      + apply Nat.eqb_eq in Heqv; subst.
        destruct (Nat.ltb lx ly) eqn:Hlxy.
        * left; reflexivity.
        * destruct (Nat.eqb lx ly) eqn:Heql.
          -- apply Nat.eqb_eq in Heql; subst.
             destruct (Nat.leb hx hy) eqn:Hh.
             ++ left; reflexivity.
             ++ right.
                rewrite Nat.ltb_irrefl, Nat.eqb_refl, Nat.ltb_irrefl, Nat.eqb_refl.
                apply Nat.leb_gt in Hh.
                apply Nat.leb_le; lia.
          -- apply Nat.eqb_neq in Heql.
             right.
             rewrite Nat.ltb_irrefl, Nat.eqb_refl.
             destruct (Nat.ltb ly lx) eqn:Hlyx.
             ++ reflexivity.
             ++ apply Nat.ltb_ge in Hlxy.
                apply Nat.ltb_ge in Hlyx.
                exfalso; lia.
      + apply Nat.eqb_neq in Heqv.
        right.
        destruct (Nat.ltb vy vx) eqn:Hvyx.
        * reflexivity.
        * apply Nat.ltb_ge in Hvyx.
          apply Nat.ltb_ge in Hvxy.
          exfalso; lia.
  Qed.
End RangeOrder.

Module SortRange := Sort(RangeOrder).

(* ------------------------------------------------------------------------- *)
(* Locus / dependency utilities                                              *)
(* ------------------------------------------------------------------------- *)


Definition nat_range_inter (x y : (nat * nat)%type) : bool :=
      ((Nat.leb (fst x) (fst y)) && (Nat.ltb (fst y) (snd x)))
  ||  ((Nat.ltb (fst y) (fst x)) && (Nat.ltb (fst x) (snd y))).

Definition range_intersect (x y : range) : bool :=
  (Nat.eqb (fst x) (fst y)) && nat_range_inter (snd x) (snd y).

Definition same_name (x y : range) : bool :=
  Nat.eqb (fst x) (fst y).

Fixpoint intersect' (x : range) (y : locus) : bool :=
  match y with
  | [] => false
  | a :: yas =>
      if ((same_name x a) && (nat_range_inter (snd x) (snd a)))
      then true
      else intersect' x yas
  end.

Fixpoint intersect (x y : locus) : bool :=
  match x with
  | [] => false
  | a :: xas =>
      if intersect' a y then true else intersect xas y
  end.




Definition get_locus (x : cexp) : locus :=
  match x with
  | CNew a => [a]
  | CAppU l _ => l
  | CMeas _ k => k
  | Send _ x a => [(x, (a, S a))]
  | Recv _ x y => [(x, (y, S y))]
  end.

Definition get_loci (x : list cexp) : locus :=
  fold_left (fun a b => get_locus b ++ a) x [].

Definition get_vars_cexp (x : cexp) : list var :=
  match x with
  | CMeas x _ => [x]
  | _ => []
  end.

Fixpoint get_vars_aexp (x : aexp) : list var :=
  match x with
  | BA a => [a]
  | Num _ => []
  | APlus e1 e2 => get_vars_aexp e1 ++ get_vars_aexp e2
  | AMult e1 e2 => get_vars_aexp e1 ++ get_vars_aexp e2
  | AModMult e1 e2 e3 =>
      get_vars_aexp e1 ++ get_vars_aexp e2 ++ get_vars_aexp e3
  end.

Definition get_vars_bexp (x : cbexp) : list var :=
  match x with
  | CEq a b => get_vars_aexp a ++ get_vars_aexp b
  | CLt a b => get_vars_aexp a ++ get_vars_aexp b
  end.

Definition is_inter (x y : cexp) : bool :=
  intersect (get_locus x) (get_locus y).

Definition inter_vars (xs ys : list var) : bool :=
  match Coq.Lists.ListSet.set_inter Nat.eq_dec xs ys with
  | [] => false
  | _ => true
  end.

Definition gen_hb_single (x y : N * myOp) (acc : N -> N -> bool) : N -> N -> bool :=
  match snd x, snd y with
  | OpAP xa, OpAP ya =>
      fun i j =>
        if (N.eqb i (fst x)) && (N.eqb j (fst y))
        then is_inter xa ya
        else acc i j
  | OpAP xa, OpIf ya la ra =>
      fun i j =>
        if (N.eqb i (fst x)) && (N.eqb j (fst y))
        then intersect (get_locus xa) (get_loci (la ++ ra))
             || inter_vars (get_vars_cexp xa) (get_vars_bexp ya)
        else acc i j
  | OpIf ya la ra, OpAP xa =>
      fun i j =>
        if (N.eqb i (fst y)) && (N.eqb j (fst x))
        then intersect (get_locus xa) (get_loci (la ++ ra))
             || inter_vars (get_vars_cexp xa) (get_vars_bexp ya)
        else acc i j
  | OpIf xa la ra, OpIf ya lb rb =>
      fun i j =>
        if (N.eqb i (fst y)) && (N.eqb j (fst x))
        then intersect (get_loci (la ++ ra)) (get_loci (lb ++ rb))
             || inter_vars (get_vars_bexp xa) (get_vars_bexp ya)
        else acc i j
  end.

Fixpoint opListOrder' (l : op_list) (n : N) : list (N * myOp) :=
  match l with
  | [] => []
  | x :: xs => (n, x) :: opListOrder' xs (N.succ n)
  end.

Definition opListOrder (l : op_list) : list (N * myOp) := opListOrder' l 0%N.

Definition empty_hp : hb_relation := fun _ _ => false.

Fixpoint gen_hb' (x : N * myOp) (l : list (N * myOp)) (acc : hb_relation) : hb_relation :=
  match l with
  | [] => acc
  | a :: xas => gen_hb_single x a (gen_hb' x xas acc)
  end.

Fixpoint gen_hb_a (R : list (N * myOp)) (acc : hb_relation) : hb_relation :=
  match R with
  | [] => acc
  | a :: xas => gen_hb_a xas (gen_hb' a xas acc)
  end.

Definition trans_closure (n : N) (x : N) (acc : hb_relation) : hb_relation :=
  fun a b =>
    if (N.ltb a x) && (N.ltb x b) && (N.ltb b n) && acc a x && acc x b
    then true
    else acc a b.

Fixpoint gen_hb_trans (size : N) (n : nat) (acc : hb_relation) : hb_relation :=
  match n with
  | O => acc
  | S m => gen_hb_trans size m (trans_closure size (N.of_nat m) acc)
  end.

Definition gen_hb (R : list (N * myOp)) : hb_relation :=
  gen_hb_trans (N.of_nat (length R)) (length R) (gen_hb_a R empty_hp).

(* ------------------------------------------------------------------------- *)
(* gen_seq                                                                   *)
(* ------------------------------------------------------------------------- *)

Fixpoint sim_exp (x y : exp) : bool :=
  match x, y with
  | SKIP _ _, SKIP _ _ => true
  | X _ _, X _ _ => true
  | CU _ _ x1, CU _ _ y1 => sim_exp x1 y1
  | RZ _ _ _, RZ _ _ _ => true
  | RRZ _ _ _, RRZ _ _ _ => true
  | SR _ _, SR _ _ => true
  | SRR _ _, SRR _ _ => true
  | QFT _ _, QFT _ _ => true
  | RQFT _ _, RQFT _ _ => true
  | H _ _, H _ _ => true
  | Addto _ _, Addto _ _ => true
  | Seq x1 x2, Seq y1 y2 => sim_exp x1 y1 && sim_exp x2 y2
  | _, _ => false
  end.

Definition sim_cexp (x y : cexp) : bool :=
  match x, y with
  | CNew _, CNew _ => true
  | CAppU _ a, CAppU _ b => sim_exp a b
  | CMeas _ _, CMeas _ _ => true
  | Send _ _ _, Send _ _ _ => true
  | Recv _ _ _, Recv _ _ _ => true
  | _, _ => false
  end.

Definition insert_op (a : N * myOp) (acc : list (list (N * myOp))) :=
  match acc with
  | [] => [[a]]
  | [] :: xl => [a] :: xl
  | ((i, OpAP b) :: xl) :: al =>
      match a with
      | (j, OpAP q) =>
          if sim_cexp q b
          then ((i, OpAP b) :: xl ++ [(j, OpAP q)]) :: al
          else [(j, OpAP q)] :: acc
      | (j, OpIf c d e) => [(j, OpIf c d e)] :: (((i, OpAP b) :: xl) :: al)
      end
  | ((i, OpIf c d e) :: xl) :: al => [a] :: ((i, OpIf c d e) :: xl) :: al
  end.

Fixpoint partition_op' (l : list (N * myOp)) (acc : list (list (N * myOp))) :=
  match l with
  | [] => acc
  | x :: xl => partition_op' xl (insert_op x acc)
  end.

Definition partition_op l := rev (partition_op' l []).

Definition nposi : Type := N * N.

Definition nposi_eq (r1 r2 : nposi) : bool :=
  match r1, r2 with
  | (x1, y1), (x2, y2) => (N.eqb x1 x2) && (N.eqb y1 y2)
  end.

Fixpoint insert_all
  (x : myOpAux * list nposi)
  (xs : list (myOpAux * list nposi))
  : list (list (myOpAux * list nposi)) :=
  match xs with
  | [] => [[x]]
  | y :: tl =>
      (x :: y :: tl) :: map (fun zs => y :: zs) (insert_all x tl)
  end.

Fixpoint permutations
  (xs : list (myOpAux * list nposi))
  : list (list (myOpAux * list nposi)) :=
  match xs with
  | [] => [[]]
  | x :: tl => concat (map (insert_all x) (permutations tl))
  end.

(* bounded behavior: exactly like the OCaml helper *)
Definition permutations_one
  (l : list (myOpAux * list nposi))
  : list (list (myOpAux * list nposi)) :=
  [l].

Fixpoint car_concat'
  (x : list (myOpAux * list nposi))
  (y : list (list (myOpAux * list nposi)))
  : list (list (myOpAux * list nposi)) :=
  match y with
  | [] => []
  | a :: ys => (x ++ a) :: car_concat' x ys
  end.

Fixpoint car_concat
  (x y : list (list (myOpAux * list nposi)))
  : list (list (myOpAux * list nposi)) :=
  match x with
  | [] => []
  | a :: xs => car_concat' a y ++ car_concat xs y
  end.

Fixpoint get_first (l : list (list (N * myOp))) : list (N * myOp) :=
  match l with
  | [] => []
  | [] :: xs => get_first xs
  | (a :: _) :: ys => a :: get_first ys
  end.

Fixpoint in_list_a (x : N * myOp) (l : list (N * myOp)) : bool :=
  match l with
  | [] => false
  | a :: xs => if N.eqb (fst x) (fst a) then true else in_list_a x xs
  end.

Fixpoint remove_first
  (l : list (list (N * myOp)))
  (x : list (N * myOp))
  : list (list (N * myOp)) :=
  match l with
  | [] => []
  | [] :: xs => [] :: remove_first xs x
  | (a :: xs) :: ys =>
      if in_list_a a x
      then xs :: remove_first ys x
      else (a :: xs) :: remove_first ys x
  end.

Fixpoint grab_related'
  (x : N * myOp)
  (l : list (N * myOp))
  (re : hb_relation)
  (acc : list (N * myOp))
  : list (N * myOp) :=
  match l with
  | [] => acc
  | a :: xs =>
      if re (fst x) (fst a)
      then grab_related' x xs re acc
      else grab_related' x xs re (acc ++ [a])
  end.

Definition grab_related (l : list (N * myOp)) (re : hb_relation) :=
  match l with
  | [] => []
  | x :: xs => grab_related' x xs re [x]
  end.

Fixpoint up_qubits (x : var) (i : nat) (n : nat) (acc : list (N * N)) :=
  match n with
  | O => acc
  | S m => up_qubits x i m (acc ++ [(N.of_nat x, N.add (N.of_nat i) (N.of_nat m))])
  end.

Fixpoint cutToQubits' (l : list range) :=
  match l with
  | [] => []
  | (x, (l0, r)) :: xs => up_qubits x l0 (r - l0) [] ++ cutToQubits' xs
  end.

Definition cutToQubits l := cutToQubits' (SortRange.sort l).

Fixpoint get_locus_in_op (l : list (N * myOp)) :=
  match l with
  | [] => []
  | (_, OpAP y) :: la =>
      match get_locus y with
      | [] => get_locus_in_op la
      | re => re ++ get_locus_in_op la
      end
  | (_, OpIf _ _ _) :: la => get_locus_in_op la
  end.

Fixpoint get_nlocus (l : list ((N * myOp)%type))
  : list ((myOpAux * list nposi)%type) :=
  match l with
  | [] => []
  | x :: xs =>
      (OpNum (fst x), cutToQubits (get_locus_in_op (x :: nil))) :: get_nlocus xs
  end.


Fixpoint assign_each
  (n : nat)
  (l : list (list (N * myOp)))
  (re : hb_relation)
  (acc : list (list (myOpAux * list nposi)))
  : list (list (myOpAux * list nposi)) :=
  match n with
  | O => acc
  | S m =>
      match get_first l with
      | [] => acc
      | p :: l0 =>
          let good := grab_related' p l0 re [p] in
          let next_acc := car_concat acc (permutations_one (get_nlocus good)) in
          assign_each m (remove_first l good) re next_acc
      end
  end.

Definition gen_seq
  (l : list (N * myOp))
  (re : hb_relation)
  : list (myOpAux * list nposi) * list (list (myOpAux * list nposi)) :=
  let can := partition_op l in
  match can with
  | [] => ([], [])
  | x :: xs => (get_nlocus x, assign_each (length l - length x) xs re [[]])
  end.

(* ------------------------------------------------------------------------- *)
(* gen_mem                                                                   *)
(* ------------------------------------------------------------------------- *)

Fixpoint count_a
  (new0 : list (myOpAux * list nposi))
  (l : list membrane_id)
  (acc : list ((myOpAux * list nposi) * membrane_id))
  : list ((myOpAux * list nposi) * membrane_id) * list (myOpAux * list nposi) :=
  match l with
  | [] => (acc, new0)
  | a :: ys =>
      match new0 with
      | [] => (acc, [])
      | x :: xs => count_a xs ys ((x, a) :: acc)
      end
  end.

Fixpoint gen_mem_new'
  (t : nat)
  (news : list (myOpAux * list nposi))
  (l : list membrane_id)
  (acc : list ((myOpAux * list nposi) * membrane_id))
  : list ((myOpAux * list nposi) * membrane_id) :=
  match t with
  | O => acc
  | S m =>
      let '(re, next) := count_a news l [] in
      gen_mem_new' m next l (acc ++ re)
  end.

Definition gen_mem_new
  (news : list ((myOpAux * list nposi)%type))
  (l : list membrane_id)
  : list (((myOpAux * list nposi)%type * membrane_id)%type) :=
  match l with
  | [] => []
  | _ =>
      let v := Nat.add (Nat.div (length news) (length l)) 1 in
      gen_mem_new' v news l []
  end.

Fixpoint insert_posis
  (l : list (membrane_id * list nposi))
  (a : membrane_id)
  (x : list nposi)
  : list (membrane_id * list nposi) :=
  match l with
  | [] => []
  | (n, y) :: ys =>
      if Nat.eqb a n
      then (n, y ++ x) :: ys
      else (n, y) :: insert_posis ys a x
  end.

Fixpoint turn_new
  (l : list ((myOpAux * list nposi) * membrane_id))
  (acc : list (membrane_id * list nposi))
  : list (membrane_id * list nposi) :=
  match l with
  | [] => acc
  | (x, y) :: xs => turn_new xs (insert_posis acc y (snd x))
  end.

Fixpoint posi_set_in (a : nposi) (l : list nposi) : bool :=
  match l with
  | [] => false
  | x :: xs => if nposi_eq a x then true else posi_set_in a xs
  end.

Fixpoint set_inter0
  (x y : list nposi)
  (acc : list nposi * list nposi)
  : list nposi * list nposi :=
  match x with
  | [] => acc
  | a :: xs =>
      if posi_set_in a y
      then set_inter0 xs y (a :: fst acc, snd acc)
      else set_inter0 xs y (fst acc, a :: snd acc)
  end.

Fixpoint dec_mem (l : list (list nposi * membrane_id)) (x : nposi) :=
  match l with
  | [] => None
  | (y, i) :: ys => if posi_set_in x y then Some i else dec_mem ys x
  end.

Fixpoint search_mem
  (new0 : list (membrane_id * list nposi))
  (x : list nposi)
  (acc : list (membrane_id * (list nposi * list nposi)))
  : list (membrane_id * (list nposi * list nposi)) :=
  match new0 with
  | [] => acc
  | (i, y) :: ys =>
      let inter := set_inter0 x y ([], []) in
      search_mem ys x ((i, inter) :: acc)
  end.

Fixpoint all_no_mem (l : list (membrane_id * (list nposi * list nposi))) :=
  match l with
  | [] => true
  | (_, ([], _)) :: ys => all_no_mem ys
  | _ :: _ => false
  end.

Fixpoint is_one_mem (l : list (membrane_id * (list nposi * list nposi))) :=
  match l with
  | [] => false
  | (_, ([], _)) :: ys => is_one_mem ys
  | _ :: ys => all_no_mem ys
  end.

Fixpoint get_one (l : list (membrane_id * (list nposi * list nposi))) :=
  match l with
  | [] => None
  | (a, ([], _)) :: ys => get_one ys
  | (a, _) :: _ => Some a
  end.

Fixpoint grab_good
  (l : list (membrane_id * (list nposi * list nposi)))
  (acc : list (membrane_id * (list nposi * list nposi)))
  : list (membrane_id * (list nposi * list nposi)) :=
  match l with
  | [] => acc
  | (a, ([], _)) :: ys => grab_good ys acc
  | (a, (ha, hb)) :: ys => grab_good ys ((a, (ha, hb)) :: acc)
  end.

Fixpoint nlength {A : Type} (l : list A) : N :=
  match l with
  | [] => N.zero
  | _ :: xs => N.add N.one (nlength xs)
  end.

Fixpoint max_one
  (l : list (membrane_id * (list nposi * list nposi)))
  (v : N)
  (acc : membrane_id * (list nposi * list nposi))
  (accb : list (membrane_id * (list nposi * list nposi)))
  : (membrane_id * (list nposi * list nposi)) *
    list (membrane_id * (list nposi * list nposi)) :=
  match l with
  | [] => (acc, accb)
  | (i, y) :: ys =>
      if N.ltb v (nlength (fst y))
      then max_one ys (nlength (fst y)) (i, y) (acc :: accb)
      else max_one ys v acc ((i, y) :: accb)
  end.

Fixpoint max_mem_id
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (v : membrane_id)
  (acc : (list nposi * list nposi)%type)
  (accb : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  : ((membrane_id * ((list nposi * list nposi)%type))%type *
     list ((membrane_id * ((list nposi * list nposi)%type))%type))%type :=
  match l with
  | [] => ((v, acc), accb)
  | (i, y) :: ys =>
      if Nat.ltb v i
      then max_mem_id ys i y ((v, acc) :: accb)
      else max_mem_id ys v acc ((i, y) :: accb)
  end.



Fixpoint gen_comm'
  (i j : membrane_id)
  (l : list nposi)
  (chan : var)
  (acc : list ((myOpAux * list nposi) * membrane_id))
  : list ((myOpAux * list nposi) * membrane_id) :=
  match l with
  | [] => acc
  | x :: xs =>
      gen_comm' i j xs (S chan)
        ((((OpExp (Recv chan (N.to_nat (fst x)) (N.to_nat (snd x)))), [x]), j) ::
         (((OpExp (Send chan (N.to_nat (fst x)) (N.to_nat (snd x)))), [x]), i) :: acc)
  end.

Fixpoint gen_comm
  (j : membrane_id)
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (chan : var)
  (acc accb : list (((myOpAux * list nposi)%type * membrane_id)%type))
  : (var *
     (list (((myOpAux * list nposi)%type * membrane_id)%type) *
      list (((myOpAux * list nposi)%type * membrane_id)%type)))%type :=
  match l with
  | [] => (chan, (acc, accb))
  | (i, (x, _)) :: xs =>
      gen_comm j xs (Nat.add chan (Nat.mul 2 (length x)))
        (gen_comm' j i x chan acc)
        (gen_comm' i j x chan accb)
  end.



Definition gen_comm_insert
  (j : membrane_id)
  (l : list (membrane_id * (list nposi * list nposi)))
  (chan : var)
  (acc : list ((myOpAux * list nposi) * membrane_id))
  (v : (myOpAux * list nposi) * membrane_id)
  : var * list ((myOpAux * list nposi) * membrane_id) :=
  let mid := gen_comm j l chan acc [] in
  (fst mid, snd (snd mid) ++ v :: fst (snd mid)).

Fixpoint gen_comm_b
  (j : membrane_id)
  (l : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (chan : var)
  (acc : list (((myOpAux * list nposi)%type * membrane_id)%type))
  : (var * list (((myOpAux * list nposi)%type * membrane_id)%type))%type :=
  match l with
  | [] => (chan, acc)
  | (i, (x, _)) :: xs =>
      gen_comm_b j xs (Nat.add chan (length x)) (gen_comm' j i x chan acc)
  end.


Fixpoint collect_all_posi
  (l : list (membrane_id * (list nposi * list nposi)))
  (acc : list nposi)
  : list nposi :=
  match l with
  | [] => acc
  | (_, (x, _)) :: xs => collect_all_posi xs (x ++ acc)
  end.

Fixpoint push_to_mem_i
  (i j : membrane_id)
  (v : list nposi)
  (l : list (membrane_id * (list nposi * list nposi)))
  (acc : list (membrane_id * list nposi))
  : list (membrane_id * list nposi) :=
  match l with
  | [] => acc
  | (k, (x, y)) :: xs =>
      if Nat.eqb i k
      then push_to_mem_i i j v xs ((k, v ++ y) :: acc)
      else if Nat.eqb j k
           then push_to_mem_i i j v xs ((k, x ++ y) :: acc)
           else push_to_mem_i i j v xs ((k, y) :: acc)
  end.

Definition post_dec
  (i : membrane_id)
  (new0 : list ((membrane_id * list nposi)%type))
  (dc : list ((list nposi * membrane_id)%type))
  (xnum : N)
  (xset : list nposi)
  (chan : var)
  (rea input : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (acc : list (((myOpAux * list nposi)%type * membrane_id)%type))
  : (var *
     list ((list (((myOpAux * list nposi)%type * membrane_id)%type) *
            list ((membrane_id * list nposi)%type))%type))%type :=
  let v := collect_all_posi rea [] in
  match v with
  | [] => (chan, [])
  | y :: _ =>
      match dec_mem dc y with
      | Some j =>
          let mid := gen_comm_insert i rea chan acc ((OpNum xnum, xset), i) in
          let pre_gen := gen_comm_b i rea (fst mid) acc in
          let post_gen :=
            gen_comm' i j v (fst pre_gen) (((OpNum xnum, xset), i) :: snd pre_gen) in
          (Nat.add (fst pre_gen) (length v),
           [((((OpNum xnum, xset), i) :: snd mid), new0);
            (post_gen, push_to_mem_i j i v input [])])
      | None =>
          let pre_gen := gen_comm_insert i rea chan acc ((OpNum xnum, xset), i) in
          (fst pre_gen, [(snd pre_gen, new0)])
      end
  end.

(* ------------------------------------------------------------------------- *)
(* Extra OCaml behaviors: capacity-aware placement                           *)
(* ------------------------------------------------------------------------- *)

Fixpoint mem_pos (p : nposi) (xs : list nposi) : bool :=
  match xs with
  | [] => false
  | y :: ys => if nposi_eq y p then true else mem_pos p ys
  end.

Fixpoint add_nodup (xs ys : list nposi) : list nposi :=
  match xs with
  | [] => ys
  | x :: tl =>
      if mem_pos x ys
      then add_nodup tl ys
      else add_nodup tl (x :: ys)
  end.

Fixpoint add_qubits_to_mem
  (i : membrane_id)
  (xs : list nposi)
  (new0 : list (membrane_id * list nposi))
  : list (membrane_id * list nposi) :=
  match new0 with
  | [] => []
  | (j, ys) :: tl =>
      if Nat.eqb i j
      then (j, add_nodup xs ys) :: add_qubits_to_mem i xs tl
      else (j, ys) :: add_qubits_to_mem i xs tl
  end.

Fixpoint assoc_opt_mem
  (i : membrane_id)
  (new0 : list (membrane_id * list nposi))
  : option (list nposi) :=
  match new0 with
  | [] => None
  | (j, xs) :: tl => if Nat.eqb i j then Some xs else assoc_opt_mem i tl
  end.

Definition mem_qubit_load (new0 : list (membrane_id * list nposi)) (i : membrane_id) : nat :=
  match assoc_opt_mem i new0 with
  | Some xs => length xs
  | None => 0
  end.

Definition membrane_capacity : nat := 8.
Definition op_capacity : nat := 6.

Definition mem_has_capacity
  (new0 : list (membrane_id * list nposi))
  (i : membrane_id)
  (xset : list nposi) : bool :=
  let current := mem_qubit_load new0 i in
  Nat.leb (current + length xset) membrane_capacity.

Fixpoint op_load_in_partial
  (l : list ((myOpAux * list nposi) * membrane_id))
  (mid : membrane_id) : nat :=
  match l with
  | [] => 0
  | (((_, _), m)) :: xs =>
      if Nat.eqb m mid
      then S (op_load_in_partial xs mid)
      else op_load_in_partial xs mid
  end.

Definition overlap_size (x y : list nposi) : nat :=
  length (fst (set_inter0 x y ([], []))).

Definition import_cost (xset local_qs : list nposi) : nat :=
  length xset - overlap_size xset local_qs.

Definition score_mem_for_op
  (partial : list ((myOpAux * list nposi) * membrane_id))
  (xset : list nposi)
  (mid : membrane_id)
  (local_qs : list nposi) : nat :=
  let imports := import_cost xset local_qs in
  let opl := op_load_in_partial partial mid in
  4 * imports + 5 * opl.

Definition over_op_capacity
  (partial : list ((myOpAux * list nposi) * membrane_id))
  (mid : membrane_id) : bool :=
  Nat.ltb op_capacity (op_load_in_partial partial mid).

Definition scored_cand : Type := nat * membrane_id * (list nposi * list nposi).

Fixpoint insert_scored_candidate
  (cand : scored_cand)
  (scored : list scored_cand) : list scored_cand :=
  match scored with
  | [] => [cand]
  | ((s1, m1, d1) as c1) :: tl =>
      let '(s, _, _) := cand in
      if Nat.ltb s s1
      then cand :: scored
      else c1 :: insert_scored_candidate cand tl
  end.

Fixpoint take_scored (n : nat) (xs : list scored_cand) : list scored_cand :=
  match n, xs with
  | O, _ => []
  | _, [] => []
  | S n', x :: tl => x :: take_scored n' tl
  end.

Fixpoint scored_candidates
  (new0 : list ((membrane_id * list nposi)%type))
  (partial : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (xset : list nposi)
  (candidates : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  : list scored_cand :=
  match candidates with
  | [] => []
  | (mid, (local_qs, rest_qs)) :: tl =>
      if orb (over_op_capacity partial mid)
             (negb (mem_has_capacity new0 mid xset))
      then scored_candidates new0 partial xset tl
      else
        let s := score_mem_for_op partial xset mid local_qs in
        insert_scored_candidate (s, mid, (local_qs, rest_qs))
          (scored_candidates new0 partial xset tl)
  end.


Fixpoint scored_candidates_nocap
  (partial : list ((myOpAux * list nposi) * membrane_id))
  (xset : list nposi)
  (candidates : list (membrane_id * (list nposi * list nposi)))
  : list scored_cand :=
  match candidates with
  | [] => []
  | (mid, (local_qs, rest_qs)) :: tl =>
      let s := score_mem_for_op partial xset mid local_qs in
      insert_scored_candidate (s, mid, (local_qs, rest_qs))
        (scored_candidates_nocap partial xset tl)
  end.



Fixpoint build_choices
  (cs : list scored_cand)
  (re : list ((membrane_id * ((list nposi * list nposi)%type))%type))
  (new0 : list ((membrane_id * list nposi)%type))
  (dc : list ((list nposi * membrane_id)%type))
  (x : (N * list nposi)%type)
  (l : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (chan : var)
  (acc :
     list ((list (((myOpAux * list nposi)%type * membrane_id)%type) *
            list ((membrane_id * list nposi)%type))%type))
  : list ((list (((myOpAux * list nposi)%type * membrane_id)%type) *
          list ((membrane_id * list nposi)%type))%type) :=
  match cs with
  | [] => acc
  | (_, chosen_mid, _) :: tl =>
      if is_one_mem re then
        let choice :=
          (((((OpNum (fst x)), snd x), chosen_mid) :: l), new0) in
        build_choices tl re new0 dc x l chan (choice :: acc)
      else
        let others :=
          filter (fun p => negb (Nat.eqb (fst p) chosen_mid)) re in
        let mid_res :=
          post_dec chosen_mid new0 dc (fst x) (snd x) chan others re l in
        let choices := snd mid_res in
        build_choices tl re new0 dc x l chan (choices ++ acc)
  end.

Definition assign_mem_s
  (new0 : list ((membrane_id * list nposi)%type))
  (dc : list ((list nposi * membrane_id)%type))
  (x : (N * list nposi)%type)
  (l : list (((myOpAux * list nposi)%type * membrane_id)%type))
  (chan : var)
  : (var *
     list ((list (((myOpAux * list nposi)%type * membrane_id)%type) *
            list ((membrane_id * list nposi)%type))%type))%type :=
  let xset := snd x in
  let re :=
    search_mem new0 xset
      ([] : list ((membrane_id * ((list nposi * list nposi)%type))%type)) in
  match re with
  | [] => (chan, [])
  | _ =>
      let ranked :=
        match scored_candidates new0 l xset re with
        | [] =>
            scored_candidates
              ([] : list ((membrane_id * list nposi)%type))
              l xset re
        | ys => ys
        end in
      let top := take_scored 3 ranked in
      (chan,
       build_choices top re new0 dc x l chan
         ([] :
           list ((list (((myOpAux * list nposi)%type * membrane_id)%type) *
                  list ((membrane_id * list nposi)%type))%type)))
  end.


Definition channel : var := 6.

Fixpoint assign_mem'
  (dc : list (list nposi * membrane_id))
  (l : list (myOpAux * list nposi))
  (acc : var *
         list (list ((myOpAux * list nposi) * membrane_id) * list (membrane_id * list nposi)))
  : var *
    list (list ((myOpAux * list nposi) * membrane_id) * list (membrane_id * list nposi)) :=
  match l with
  | [] => acc
  | (OpNum x, y) :: xs =>
      assign_mem' dc xs
        (fold_left
           (fun a b =>
              let mid := assign_mem_s (snd b) dc (x, y) (fst b) (fst a) in
              (fst mid, snd a ++ snd mid))
           (snd acc) (fst acc, []))
  | _ :: xs => assign_mem' dc xs acc
  end.

Fixpoint assign_mem_more
  (new0 : list (membrane_id * list nposi))
  (dc : list (list nposi * membrane_id))
  (l : list (list (myOpAux * list nposi)))
  (acc : list (list ((myOpAux * list nposi) * membrane_id)))
  : list (list ((myOpAux * list nposi) * membrane_id)) :=
  match l with
  | [] => acc
  | x :: xs =>
      assign_mem_more new0 dc xs
        (map rev (fst (split (snd (assign_mem' dc x (channel, [([], new0)]))))) ++ acc)
  end.

Fixpoint find_empty_new'
  (l : list (membrane_id * list nposi))
  (m : membrane_id)
  (acc : list membrane_id)
  : list membrane_id :=
  match l with
  | [] => m :: acc
  | (x, _) :: xs => if Nat.eqb x m then acc else find_empty_new' xs m acc
  end.

Fixpoint find_empy_new
  (l : list (membrane_id * list nposi))
  (al acc : list membrane_id)
  : list membrane_id :=
  match al with
  | [] => acc
  | x :: xs => find_empy_new l xs (find_empty_new' l x acc)
  end.

Fixpoint assign_new_mem
  (l : list (myOpAux * list nposi))
  (al : list membrane_id)
  : list (list nposi * membrane_id) :=
  match al with
  | [] => []
  | x :: xs =>
      match l with
      | [] => []
      | y :: ys => (snd y, x) :: assign_new_mem ys xs
      end
  end.

Fixpoint gen_empty_mem (m : list membrane_id) : list (membrane_id * list nposi) :=
  match m with
  | [] => []
  | a :: xl => (a, []) :: gen_empty_mem xl
  end.

Fixpoint take {A : Type} (n : nat) (xs : list A) : list A :=
  match n, xs with
  | O, _ => []
  | _, [] => []
  | S n', x :: tl => x :: take n' tl
  end.

Definition fallback_mid
  (ql : list ((myOpAux * list nposi) * membrane_id)) : membrane_id :=
  match ql with
  | [] => 0
  | (_, mid) :: _ => mid
  end.

Definition gen_mem
  (news : list (myOpAux * list nposi))
  (l : list (list (myOpAux * list nposi)))
  (ids : list membrane_id)
  : list (list ((myOpAux * list nposi) * membrane_id)) :=
  let ql := gen_mem_new news ids in
  let vl := turn_new (gen_mem_new news ids) [] in
  let al := find_empy_new vl ids [] in
  let dc := assign_new_mem news al in
  let base_new0 := gen_empty_mem al ++ vl in
  let res := map (fun a => ql ++ a) (assign_mem_more base_new0 dc l []) in
  match res with
  | [] =>
      let mid := fallback_mid ql in
      match take 3 l with
      | [] => [ql]
      | xs =>
          map (fun x => ql ++ map (fun y => (y, mid)) x) xs
      end
  | _ => res
  end.

(* ------------------------------------------------------------------------- *)
(* Program reconstruction                                                     *)
(* ------------------------------------------------------------------------- *)

Fixpoint insert_mem_id
  (i : membrane_id)
  (x : myOpAux * list nposi)
  (acc : list (membrane_id * list (myOpAux * list nposi)))
  : list (membrane_id * list (myOpAux * list nposi)) :=
  match acc with
  | [] => [(i, [x])]
  | (a, b) :: xs =>
      if Nat.eqb i a
      then (a, b ++ [x]) :: xs
      else (a, b) :: insert_mem_id i x xs
  end.

Fixpoint distribute_op
  (l : list ((myOpAux * list nposi) * membrane_id))
  (acc : list (membrane_id * list (myOpAux * list nposi)))
  : list (membrane_id * list (myOpAux * list nposi)) :=
  match l with
  | [] => acc
  | x :: xs => distribute_op xs (insert_mem_id (snd x) (fst x) acc)
  end.

Fixpoint get_op (l : list (N * myOp)) (i : N) : option myOp :=
  match l with
  | [] => None
  | (x, y) :: xs => if N.eqb i x then Some y else get_op xs i
  end.

Fixpoint turn_cexp_to_proc (l : list cexp) (p : process) : process :=
  match l with
  | [] => p
  | x :: xs => AP x (turn_cexp_to_proc xs p)
  end.

Definition turn_op_to_proc (x : myOp) (p : process) :=
  match x with
  | OpAP a => AP a p
  | OpIf b l r => PIf b (turn_cexp_to_proc l p) (turn_cexp_to_proc r p)
  end.

Fixpoint to_process
  (l : list (myOpAux * list nposi))
  (os : list (N * myOp))
  : option process :=
  match l with
  | [] => Some PNil
  | (OpNum n, _) :: xs =>
      match get_op os n, to_process xs os with
      | Some x, Some p => Some (turn_op_to_proc x p)
      | _, _ => None
      end
  | (OpExp a, _) :: xs =>
      match to_process xs os with
      | Some p => Some (AP a p)
      | None => None
      end
  end.

Fixpoint to_prog
  (l : list (nat * list (myOpAux * list nposi)))
  (os : list (N * myOp))
  : list memb :=
  match l with
  | [] => []
  | x :: xs =>
      match to_process (snd x) os with
      | None => []
      | Some a => Memb (fst x) a :: to_prog xs os
      end
  end.

(* ------------------------------------------------------------------------- *)
(* Extra OCaml behavior: lower_solution_distributed                          *)
(* ------------------------------------------------------------------------- *)

Fixpoint has_if_ops (os : list (N * myOp)) : bool :=
  match os with
  | [] => false
  | (_, OpIf _ _ _) :: _ => true
  | _ :: xs => has_if_ops xs
  end.

Fixpoint owner_of_pos
  (owners : list (nposi * membrane_id))
  (p : nposi) : option membrane_id :=
  match owners with
  | [] => None
  | (q, mid) :: xs =>
      if nposi_eq q p then Some mid else owner_of_pos xs p
  end.

Fixpoint set_owner
  (owners : list (nposi * membrane_id))
  (p : nposi)
  (mid : membrane_id)
  : list (nposi * membrane_id) :=
  match owners with
  | [] => [(p, mid)]
  | (q, m) :: xs =>
      if nposi_eq q p
      then (p, mid) :: xs
      else (q, m) :: set_owner xs p mid
  end.

Fixpoint set_owner_many
  (owners : list (nposi * membrane_id))
  (ps : list nposi)
  (mid : membrane_id)
  : list (nposi * membrane_id) :=
  match ps with
  | [] => owners
  | p :: xs => set_owner_many (set_owner owners p mid) xs mid
  end.

Fixpoint append_cexp_to_mem
  (mid : membrane_id)
  (ce : cexp)
  (acc : list (membrane_id * list cexp))
  : list (membrane_id * list cexp) :=
  match acc with
  | [] => [(mid, [ce])]
  | (m, xs) :: tl =>
      if Nat.eqb mid m
      then (m, xs ++ [ce]) :: tl
      else (m, xs) :: append_cexp_to_mem mid ce tl
  end.

Fixpoint add_initial_owners_from_solution
  (sol : list ((myOpAux * list nposi) * membrane_id))
  (os : list (N * myOp))
  (owners : list (nposi * membrane_id))
  : list (nposi * membrane_id) :=
  match sol with
  | [] => owners
  | (((aux, qs), mid)) :: xs =>
      let owners' :=
        match aux with
        | OpNum n =>
            match get_op os n with
            | Some (OpAP (CNew r)) =>
                set_owner_many owners (cutToQubits [r]) mid
            | _ => owners
            end
        | OpExp (CNew r) =>
            set_owner_many owners (cutToQubits [r]) mid
        | _ => owners
        end in
      add_initial_owners_from_solution xs os owners'
  end.

Fixpoint ensure_local_qubits_aux
  (dst : membrane_id)
  (qs : list nposi)
  (owners : list (nposi * membrane_id))
  (bufs : list (membrane_id * list cexp))
  (chan : var)
  : var * list (nposi * membrane_id) * list (membrane_id * list cexp) :=
  match qs with
  | [] => (chan, owners, bufs)
  | q :: tl =>
      match owner_of_pos owners q with
      | Some src =>
          if Nat.eqb src dst then
            ensure_local_qubits_aux dst tl owners bufs chan
          else
            let v := N.to_nat (fst q) in
            let idx := N.to_nat (snd q) in
            let bufs1 := append_cexp_to_mem src (Send chan v idx) bufs in
            let bufs2 := append_cexp_to_mem dst (Recv chan v idx) bufs1 in
            let owners' := set_owner owners q dst in
            ensure_local_qubits_aux dst tl owners' bufs2 (S chan)
      | None =>
          ensure_local_qubits_aux dst tl owners bufs chan
      end
  end.

Definition ensure_local_qubits := ensure_local_qubits_aux.

Fixpoint to_prog_from_cexps
  (grouped : list (membrane_id * list cexp))
  : config :=
  match grouped with
  | [] => []
  | (mid, ces) :: xs => Memb mid (turn_cexp_to_proc ces PNil) :: to_prog_from_cexps xs
  end.

Fixpoint lower_solution_distributed_go
  (xs : list ((myOpAux * list nposi) * membrane_id))
  (os : list (N * myOp))
  (owners : list (nposi * membrane_id))
  (bufs : list (membrane_id * list cexp))
  (chan : var)
  : config :=
  match xs with
  | [] => to_prog_from_cexps bufs
  | (((aux, _qs), mid)) :: tl =>
      match aux with
      | OpExp ce =>
          match ce with
          | CNew r =>
              let owners' := set_owner_many owners (cutToQubits [r]) mid in
              let bufs' := append_cexp_to_mem mid ce bufs in
              lower_solution_distributed_go tl os owners' bufs' chan
          | Recv _ x y =>
              let owners' := set_owner owners (N.of_nat x, N.of_nat y) mid in
              let bufs' := append_cexp_to_mem mid ce bufs in
              lower_solution_distributed_go tl os owners' bufs' chan
          | _ =>
              let bufs' := append_cexp_to_mem mid ce bufs in
              lower_solution_distributed_go tl os owners bufs' chan
          end
      | OpNum n =>
          match get_op os n with
          | Some (OpAP ce) =>
              match ce with
              | CNew r =>
                  let owners' := set_owner_many owners (cutToQubits [r]) mid in
                  let bufs' := append_cexp_to_mem mid ce bufs in
                  lower_solution_distributed_go tl os owners' bufs' chan
              | CAppU loc e =>
                  let qbs := cutToQubits loc in
                  let '(chan', owners', bufs') :=
                      ensure_local_qubits mid qbs owners bufs chan in
                  let bufs'' := append_cexp_to_mem mid (CAppU loc e) bufs' in
                  lower_solution_distributed_go tl os owners' bufs'' chan'
              | CMeas x loc =>
                  let qbs := cutToQubits loc in
                  let '(chan', owners', bufs') :=
                      ensure_local_qubits mid qbs owners bufs chan in
                  let bufs'' := append_cexp_to_mem mid (CMeas x loc) bufs' in
                  lower_solution_distributed_go tl os owners' bufs'' chan'
              | Send _ _ _ =>
                  let bufs' := append_cexp_to_mem mid ce bufs in
                  lower_solution_distributed_go tl os owners bufs' chan
              | Recv _ _ _ =>
                  let bufs' := append_cexp_to_mem mid ce bufs in
                  lower_solution_distributed_go tl os owners bufs' chan
              end
          | _ =>
              lower_solution_distributed_go tl os owners bufs chan
          end
      end
  end.

Definition lower_solution_distributed
  (sol : list ((myOpAux * list nposi) * membrane_id))
  (os : list (N * myOp))
  : config :=
  let owners0 := add_initial_owners_from_solution sol os [] in
  lower_solution_distributed_go sol os owners0 [] 100000.

Fixpoint gen_prog
  (l : list (list ((myOpAux * list nposi) * membrane_id)))
  (os : list (N * myOp))
  : list config :=
  if has_if_ops os then
    match l with
    | [] => []
    | x :: xs => to_prog (distribute_op x []) os :: gen_prog xs os
    end
  else
    match l with
    | [] => []
    | x :: xs => lower_solution_distributed x os :: gen_prog xs os
    end.

(* ------------------------------------------------------------------------- *)
(* Fitness / best candidate                                                  *)
(* ------------------------------------------------------------------------- *)

Fixpoint count_send_in_process (p : process) : nat :=
  match p with
  | PNil => 0
  | AP a p' =>
      match a with
      | Send _ _ _ => S (count_send_in_process p')
      | Recv _ _ _ => S (count_send_in_process p')
      | _ => count_send_in_process p'
      end
  | PIf _ p1 p2 => count_send_in_process p1 + count_send_in_process p2
  end.

Definition count_send_in_memb (m : memb) : nat :=
  match m with
  | Memb _ p => count_send_in_process p
  end.

Fixpoint count_comm_ops (cfg : config) : nat :=
  match cfg with
  | [] => 0
  | m :: xs => count_send_in_memb m + count_comm_ops xs
  end.

Fixpoint process_size (p : process) : nat :=
  match p with
  | PNil => 0
  | AP _ p' => S (process_size p')
  | PIf _ p1 p2 => process_size p1 + process_size p2
  end.

Definition memb_load (m : memb) : nat :=
  match m with
  | Memb _ p => process_size p
  end.

Fixpoint max_load (cfg : config) : nat :=
  match cfg with
  | [] => 0
  | m :: xs => Nat.max (memb_load m) (max_load xs)
  end.

Definition alpha : nat := 10.

Definition fit (cfg : config) : fitness_value :=
  alpha * count_comm_ops cfg + max_load cfg.

Fixpoint best_prog_aux
  (best : config)
  (bestv : nat)
  (xs : list config)
  : config :=
  match xs with
  | [] => best
  | x :: tl =>
      let vx := fit x in
      if vx <? bestv
      then best_prog_aux x vx tl
      else best_prog_aux best bestv tl
  end.

Definition best_prog (xs : list config) : option config :=
  match xs with
  | [] => None
  | x :: tl => Some (best_prog_aux x (fit x) tl)
  end.

(* ------------------------------------------------------------------------- *)
(* Top-level algorithms                                                      *)
(* ------------------------------------------------------------------------- *)

Definition autodisq_all
  (ops : op_list)
  (mids : list membrane_id)
  : list config :=
  let os := opListOrder ops in
  let hb := gen_hb os in
  let sq := gen_seq os hb in
  let mem := gen_mem (fst sq) (snd sq) mids in
  gen_prog mem os.

Definition autodisq_best
  (ops : op_list)
  (mids : list membrane_id)
  : option config :=
  best_prog (autodisq_all ops mids).

Fixpoint auto_disq_loop
  (best : option config)
  (cands : list config)
  : option config :=
  match cands with
  | [] => best
  | P :: xs =>
      match best with
      | None => auto_disq_loop (Some P) xs
      | Some B =>
          if fit P <? fit B
          then auto_disq_loop (Some P) xs
          else auto_disq_loop best xs
      end
  end.

Definition autodisq_best_1
  (ops : op_list)
  (mids : list membrane_id)
  : option config :=
  auto_disq_loop None (autodisq_all ops mids).


**)


(**
From Coq Require Import List Arith Bool Nat.
Import ListNotations.
Require Import Coq.Sorting.Mergesort.
Require Import Coq.Structures.Orders.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import QArith.
Local Open Scope nat_scope.
Local Open Scope list_scope.
 
Require Import QuantumLib.Prelim.
Require Import DisQ.BasicUtility.   (* var := nat *)
Require Import DisQ.DisQSyntax.     (* exp, process, memb, config, ... *)

Definition membrane    : Type := memb.
Definition membranes   : Type := config.
Definition membrane_id : Type := var.

Inductive myOp : Type :=
| OpAP  (a : cexp)                         
| OpIf  (b : cbexp) (p q : list cexp). 

Definition op_list : Type := list myOp.
Definition hb_relation : Type := N -> N -> bool.
Definition rank         : Type := N.
Definition seq_relation : Type := myOp -> rank.
Definition op_mem_assign : Type := myOp -> membrane_id.

Inductive myOpAux : Type :=
   | OpNum (n:N) | OpExp (a:cexp).

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

(*
Definition bound_eqb (b1 b2 : bound) : bool :=
  match b1, b2 with
  | BVar v1 n1, BVar v2 n2 =>
      andb (Nat.eqb v1 v2) (Nat.eqb n1 n2)
  | BNum n1, BNum n2 =>
      Nat.eqb n1 n2
  | _, _ => false
  end.
*)

Definition range_eqb (r1 r2 : range) : bool :=
  match r1, r2 with
  | (x1, (lo1, hi1)), (x2, (lo2, hi2)) =>
      andb (Nat.eqb x1 x2)
           (andb (Nat.eqb lo1 lo2)
                 (Nat.eqb hi1 hi2))
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


(*
Definition cexp_eqb (c1 c2 : cexp) : bool :=
  match c1, c2 with
  | CNew x1 n1, CNew x2 n2 =>
      andb (Nat.eqb x1 x2) (Nat.eqb n1 n2)
  | CAppU l1 e1, CAppU l2 e2 =>
      andb (locus_eqb l1 l2) (exp_eqb e1 e2)
  | CMeas x1 k1, CMeas x2 k2 =>
      andb (Nat.eqb x1 x2) (locus_eqb k1 k2)
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
  | PIf b1 p1a p1b, PIf b2 p2a p2b =>
      andb (cbexp_eqb b1 b2)
           (andb (process_eqb p1a p2a) (process_eqb p1b p2b))
  | _, _ => false
  end.
*)
(*
Definition myOp_eqb (x y : myOp) : bool :=
  match x, y with
  | OpAP a1, OpAP a2 => cexp_eqb a1 a2
  | OpIf b1 p1 q1, OpIf b2 p2 q2 =>
      andb (cbexp_eqb b1 b2)
           (andb (process_eqb p1 p2) (process_eqb q1 q2))
  | _, _ => false
  end.
*)

Definition qubit_mem_assign : Type := var -> membrane_id.

Definition fitness_value    : Type := nat.
Definition distributed_prog : Type := config.


(*
 locus lib
*)

Module RangeOrder <: TotalLeBool'.
  Definition t := range.
  Definition leb (x y:range) := if Nat.ltb (fst x) (fst y) then true
    else if Nat.eqb (fst x) (fst y) then 
         (if (Nat.ltb (fst (snd x)) (fst (snd y))) then true
          else if (Nat.eqb (fst (snd x)) (fst (snd y))) then (Nat.leb (snd (snd x)) (snd (snd y))) else false) else false.   
  Infix "[<=]" := leb (at level 50). 
  Theorem leb_total : forall x y, (x [<=] y) = true \/ (y [<=] x) = true.
  Proof.
  intros.
  unfold leb.
  destruct x; simpl in *.
  destruct y; simpl in *.
  destruct p; simpl in *.
  destruct p0; simpl in *.
  bdestruct (v <? v0). left. easy.
  bdestruct (v =? v0).
  bdestruct (n <? n1). left. easy.
  bdestruct (n =? n1).
  bdestruct (n0 <=? n2). left. easy.
  bdestruct (v0 <? v). right. easy.
  bdestruct (v0 =? v).
  bdestruct (n1 <? n). right. easy.
  subst. bdestruct (n1 =? n1).
  bdestruct (n2 <=? n0). right. easy.
  1-3: lia.
  subst. bdestruct (v0 <? v0). right. easy.
  bdestruct (v0 =? v0).
  bdestruct (n1 <? n). right. easy. assert (n = n1) by lia. subst.
  bdestruct (n1 =? n1). 1 - 3: lia.
  right.
  bdestruct (v0 <? v). easy.
  bdestruct (v0 =? v). subst. 1 - 2: lia.
  Qed.
End RangeOrder.

(* 2. Instantiate the Sort module with your order *)
Module SortRange := Sort(RangeOrder).


(*
Define intersect of two locus.
*)
Definition nat_range_inter (x y : (nat * nat)) :=
      ((fst x <=? fst y) && (fst y <? snd x))
  ||  ((fst y <? fst x) && (fst x <? snd y)).

Definition nat_range_sub (x y : (nat * nat)) := ((fst y <=? fst x) && (snd x <? snd y)).

Definition range_intersect (x y : range) := ((fst x) =? (fst y)) && nat_range_inter (snd x) (snd y).

Definition same_name (x y:range) := fst x =? fst y.

Fixpoint intersect' (x:range) (y:locus) :=
   match y with nil => false
              | a::yas => if (same_name x a) && (nat_range_inter (snd x) (snd a)) then true else intersect' x yas
   end.

Fixpoint intersect (x y:locus) :=
   match x with nil => false 
             | a::xas => if intersect' a y then true else intersect xas y end.

Definition get_locus (x:cexp) :=
  match x with CNew a => [a]
             | CAppU l e => l
             | CMeas x k => k
             | Send c x a => [(x,(a,S a))]
             | Recv c x y => [(x,(y,S y))]
  end.

Definition get_loci (x : list cexp) := fold_left (fun a b => get_locus b ++ a) x nil.

Definition get_vars_cexp (x:cexp) :=
  match x with CNew a => nil
             | CAppU l e => nil
             | CMeas x k => [x]
             | Send c x a => nil
             | Recv c x y => nil
  end.

Fixpoint get_vars_aexp (x:aexp) :=
  match x with BA a => [a]
             | Num n => nil
             | APlus e1 e2 => get_vars_aexp e1 ++ get_vars_aexp e2
             | AMult e1 e2 => get_vars_aexp e1 ++ get_vars_aexp e2
             | AModMult e1 e2 e3 => get_vars_aexp e1 ++ get_vars_aexp e2 ++ get_vars_aexp e3
  end.

Definition get_vars_bexp (x:cbexp) :=
  match x with CEq a b => get_vars_aexp a ++ get_vars_aexp b
             | CLt a b =>  get_vars_aexp a ++ get_vars_aexp b
  end.

Definition is_inter (x y: cexp) :=
  match get_locus x, get_locus y with la,lb => intersect la lb end.

Definition inter_vars (xs ys : list var) : bool :=
   match set_inter Nat.eq_dec xs ys with nil => false | _ => true end.

Definition gen_hb_single (x y: N * myOp) acc : N -> N -> bool :=
   match snd x, snd y
    with OpAP xa, OpAP ya => fun i j => if (N.eqb i (fst x)) && (N.eqb j (fst y)) then is_inter xa ya else acc i j
       | OpAP xa, OpIf ya la ra => 
             fun i j => if (N.eqb i (fst x)) && (N.eqb j (fst y)) 
                    then intersect (get_locus xa) (get_loci (la++ra)) || inter_vars (get_vars_cexp xa) (get_vars_bexp ya) else acc i j
       | OpIf ya la ra, OpAP xa =>
             fun i j => if (N.eqb i (fst y)) && (N.eqb j (fst x))
                    then intersect (get_locus xa) (get_loci (la++ra)) || inter_vars (get_vars_cexp xa) (get_vars_bexp ya) else acc i j
       | OpIf xa la ra, OpIf ya lb rb =>
             fun i j => if (N.eqb i (fst y)) && (N.eqb j (fst x))
                    then intersect (get_loci (la++ra)) (get_loci (lb++rb)) || inter_vars (get_vars_bexp xa) (get_vars_bexp ya) else acc i j
   end.

Definition gen_next (n:N) (x y: N * myOp) (r:N -> N -> bool) :=
  fun a b => if (N.eqb a (fst x)) && (N.ltb (fst y) b) && (N.ltb b n) then r (fst y) b else r a b.

(* --- corrected hp --- *)
Fixpoint opListOrder' (l : op_list) (n:N) :=
  match l with nil => nil
             | x::xs => (n,x)::opListOrder' xs (N.succ n)
  end.
Definition opListOrder l := opListOrder' l 0.

Definition empty_hp := fun (x y:N) => false.


(* hp relation is transitive closure. *)
Fixpoint gen_hb' (x: N * myOp) l acc := 
  match l with nil => acc
             | a::xas => (gen_hb_single x a (gen_hb' x xas acc))
  end.

Fixpoint gen_hb_a (R : list (N * myOp)) acc :=
   match R with nil => acc
             | a::xas => gen_hb_a xas (gen_hb' a xas acc)
   end.


Definition trans_closure (n:N) (x:N) acc :=
  fun a b => if (N.ltb a x) && (N.ltb x b) && (N.ltb b n) 
             && acc a x && acc x b then true else acc a b.

Fixpoint gen_hb_trans size n acc :=
  match n with 0 => acc | S m => gen_hb_trans size m (trans_closure size (N.of_nat m) acc) end.

Definition gen_hb (R : list (N * myOp)) := gen_hb_trans (N.of_nat (length R)) (length R) (gen_hb_a R empty_hp).



(* ------------------------------------------------------------------------- *)
(* gen_seq                                                            *)
(* ------------------------------------------------------------------------- *)

(* eq exp *)
Fixpoint sim_exp (x y :exp) :=
  match x,y with SKIP a b, SKIP c d => true
               | X a b, X c d => true
               | CU a b x1, CU c d y1 => sim_exp x1 y1
               | RZ a b c, RZ e f g => true
               | RRZ a b c, RRZ e f g => true
               | SR a b, SR c d => true
               | SRR a b, SRR c d => true
               | QFT a b, QFT c d => true
               | RQFT a b, RQFT c d => true
               | H a b, H c d => true
               | Addto a b, Addto c d => true
               | Seq x1 x2, Seq y1 y2 => sim_exp x1 y1 && sim_exp x2 y2
               | _, _ => false
  end.

Definition sim_cexp (x y: cexp) :=
  match x,y with CNew a, CNew b => true
               | CAppU l1 a, CAppU l2 b => sim_exp a b
               | CMeas a b, CMeas c d => true
               | Send a b c, Send e f g => true
               | Recv a b c, Recv e f g => true
               | _, _ => false
  end.

Definition sim_myop (x y: myOp) :=
   match x,y with OpAP a, OpAP b => sim_cexp a b
                | _, _ => false
   end.

Definition insert_op (a:N *myOp) acc :=
  match acc with nil => [[a]]
               | []::xl => [a]::xl
               | ((i,OpAP b)::xl)::al => 
         match a with (j,OpAP q) => if sim_cexp q b then ((i,OpAP b)::xl++[(j,OpAP q)])::al else [(j,OpAP q)]::acc
                    | (i,OpIf c d e) => [(i,OpIf c d e)]::(((i,OpAP b)::xl)::al)
         end
               | ((i,OpIf c d e)::xl)::al => [a]::((i,OpIf c d e)::xl)::al
  end.

Fixpoint partition_op' (l:list (N * myOp)) acc :=
  match l with nil => acc
                | x::xl => partition_op' xl (insert_op x acc)
  end.
Definition partition_op l := rev (partition_op' l []).

Definition nposi : Type := (N * N).

Definition nposi_eq (r1 r2 : nposi) : bool := 
                match r1 with (x1,y1)
                            => match r2
                               with (x2,y2) => (N.eqb x1 x2) && (N.eqb y1 y2)
                               end
                end.

Fixpoint insert_all (x : myOpAux * list nposi) (xs : list (myOpAux * list nposi)) : list (list (myOpAux * list nposi)) :=
  match xs with
  | [] => [[x]]
  | y :: tl =>
      (x :: y :: tl) :: map (fun zs => y :: zs) (insert_all x tl)
  end.



Fixpoint permutations (xs : list (myOpAux * list nposi)) : list (list (myOpAux * list nposi)) :=
  match xs with
  | [] => [[]]
  | x :: tl => concat (map (insert_all x) (permutations tl))
  end.

Fixpoint car_concat' (x:list (myOpAux * list nposi)) (y : list (list (myOpAux * list nposi))) := 
  match y with nil => nil
            | a::ys => (x++a)::(car_concat' x ys)
  end.

Fixpoint car_concat (x y:  list (list (myOpAux * list nposi))) :=
   match x with nil => nil
              | a::xs => (car_concat' a y) ++ car_concat xs y
   end.

Fixpoint get_first (l:list (list (N * myOp))) := 
   match l with nil => nil
              | []::xs => get_first xs
              | (a::xs)::ys => a::get_first ys
   end.

Fixpoint in_list_a (x: (N * myOp)) (l:list (N * myOp)) :=
  match l with nil => false | a::xs => if N.eqb (fst x) (fst a) then true else in_list_a x xs end.

Fixpoint remove_first (l:list (list (N * myOp))) (x:(list (N * myOp))) :=
  match l with nil => nil
             | []::xs => []::remove_first xs x
             | (a::xs)::ys => if in_list_a a x then xs::remove_first ys x else (a::xs)::remove_first ys x
  end.

Fixpoint grab_related' (x: N* myOp) (l:list (N * myOp)) (re:hb_relation) acc :=
  match l with nil => acc
             | a::xs => if re (fst x) (fst a) then grab_related' x xs re acc else grab_related' x xs re (acc++[a])
  end.
Definition grab_related l re := match l with nil => nil | x::xs => grab_related' x xs re ([x]) end.

Definition grab_nums (l:(list (N * myOp))) := fst (split l).

Fixpoint in_list' (x:N) (l:list N) :=
  match l with nil => false | a::xs => if N.eqb x a then true else in_list' x xs end.
Definition in_list (x:myOpAux) (l:list N) :=
  match x with OpNum v => in_list' v l | _ => false end.


Fixpoint up_qubits (x:var) (i:nat) (n:nat) acc :=
  match n with 0 => acc
           | S m => up_qubits x i m (acc++[(N.of_nat x,N.add (N.of_nat i) (N.of_nat m))])
  end.

Fixpoint cutToQubits' (l:list range) :=
  match l with nil => nil
            | (x,(l,r))::xs => (up_qubits x l (r -l) []) ++ cutToQubits' xs
  end.
Definition cutToQubits l := cutToQubits' (SortRange.sort l).

Fixpoint get_locus_in_op (l: list (N * myOp)) := 
   match l with nil => nil
             | (x,OpAP y)::la => match get_locus y with nil => get_locus_in_op la | re => re ++ get_locus_in_op la end
             | (x,OpIf a b c)::la => get_locus_in_op la
   end.

Fixpoint get_nlocus (l: list (N * myOp)) :=
  match l with nil => nil | x::xs => (OpNum (fst x), cutToQubits (get_locus_in_op ([x])))::get_nlocus xs end.

Fixpoint insert_back (x:(list (N * myOp))) (l: (list (list (N * myOp)))) (re:list N) :=
   match x with nil => nil
             | a::xs =>
           match l with nil => nil
                     | la::ls => if in_list' (fst a) re then la::(insert_back xs ls re) else (a::la)::(insert_back xs ls re)
           end
   end.

Fixpoint assign_each (n:nat) (l:list (list (N * myOp))) (re:hb_relation) acc :=
  match n with 0 => acc
             | S m =>
      match get_first l with nil => acc
                           | a => let good := (grab_related a re) in
                         assign_each m (remove_first l good) re (car_concat acc (permutations (get_nlocus good)))
      end
  end.

Definition gen_seq (l:list (N * myOp)) (re: hb_relation) := 
   let can := partition_op l in
   match can with nil => (nil,nil)
                | x::xs => (get_nlocus x,assign_each (length l - length x) xs re [nil])
   end.

Check gen_seq.
(* ------------------------------------------------------------------------- *)
(* gen_mem                                                           *)
(* ------------------------------------------------------------------------- *)

Fixpoint count_a (new: list (myOpAux * list nposi)) (l: list membrane_id) acc :=
  match l with nil => (acc,new)
            | a::ys => 
   match new with nil => (acc,nil)
               | x::xs => count_a xs ys ((x,a)::acc) 
   end
  end.

Fixpoint gen_mem_new' (t:nat) (news: list (myOpAux * list nposi)) (l:list membrane_id) acc :=
  match t with 0 => acc
               | S m => let (re,next) := count_a news l nil in
                        gen_mem_new' m next l (acc++re)
  end.

Definition gen_mem_new (news: list (myOpAux * list nposi)) (l:list membrane_id) :=
  let v := ((length news) / (length l)) + 1 in gen_mem_new' v news l [].

Fixpoint gen_new_mem_ids (l: list membrane_id) :(list (membrane_id * list nposi)) :=
  match l with nil => nil | x::xs => (x,nil)::(gen_new_mem_ids xs) end.

Fixpoint insert_posis (l:list (membrane_id * list nposi)) (a:membrane_id) (x:list nposi) :=
  match l with nil => nil | (n,y)::ys => if a =? n then (n,y++x)::ys else (n,y)::insert_posis ys a x end.

Fixpoint turn_new (l:list (myOpAux * list nposi * membrane_id)) acc :=
  match l with nil => acc
             | (x,y)::xs => turn_new xs (insert_posis acc y (snd x))
end.

Check gen_mem_new.
Check turn_new.


Fixpoint posi_set_in (a:nposi) (l:list nposi) :=
  match l with nil => false | x::xs => if nposi_eq a x then true else posi_set_in a xs end.

Fixpoint set_inter (x y : (list nposi)) acc :=
  match  x with nil => acc
              | a::xs => if posi_set_in a y then set_inter xs y (a::fst acc,snd acc) else set_inter xs y (fst acc,a::snd acc)
  end.

Fixpoint dec_mem (l: list (list nposi * membrane_id)) (x:nposi) := 
  match l with nil => None | ((y,i)::ys) => if posi_set_in x y then Some i else dec_mem ys x end.


Fixpoint sub_locus' (x y: locus) :=
  match x with nil => true
            | (na,(la,ra))::xs =>
     match y with nil => false
               | (nb,(lb,rb))::ys =>
                 (na =? nb) && (la <=? lb) && (rb <=? ra) && sub_locus' xs ys
     end
  end.
Definition sub_locus x y := sub_locus' (SortRange.sort x) (SortRange.sort y).

Definition split_nat_range (x y: (nat * nat)) :=
   if fst x =? fst y then [(snd x, snd y)]
   else if snd x =? snd y then [(fst y, fst x)] else (fst y, fst x):: (snd x, snd y)::[].

Fixpoint assemble_range (l:list (nat * nat)) (x:var) :=
  match l with nil => nil
            | a::xs => (x,a)::(assemble_range xs x)
  end.

Fixpoint sublist_posi (l r : list posi) :=
  match l with nil => true | x::xs => set_mem posi_eq_dec x r && sublist_posi xs r end.

(*
Fixpoint insert_mem  (a: posi * membrane_id * list nat)  (l:list (list posi * membrane_id * list nat)) :=
  match l with nil => [([fst (fst a)], snd (fst a),snd a)]
            | (x,y, ids)::xs => if snd (fst a) =? y then ((fst (fst a))::x,y,snd a ++ ids)::xs else (x,y, ids) :: insert_mem a xs
  end.
*)


(*
Definition isSend a := match a with Send q p u => true | _ => false end.

Fixpoint no_send_check (i:membrane_id) (l:list (myOpAux * list posi * membrane_id)) :=
  match l with nil => true 
       | (OpExp u,v,w)::xs =>
       if (i =? w) && (isSend u) then false else no_send_check i xs
       | a::xs => no_send_check i xs 
  end.

Fixpoint search_hb (x:list posi) (n:N) (hb:hb_relation) (l : (list (myOpAux * list posi * membrane_id))) checker :=
  match l with nil => None
            | (OpNum u,v,w)::xs => 
          if hb n u && no_send_check w checker then
          match set_inter x v nil
          with nil => search_hb x n hb xs checker
             | next => Some (w, next)
          end
          else search_hb x n hb xs checker
            | a::xs => search_hb x n hb xs (a::checker)
  end.
*)

Fixpoint search_mem (new:list (membrane_id * list nposi)) (x:list nposi) acc :=
  match new with nil => acc
              | (i,y)::ys => search_mem ys x ((i,set_inter x y (nil,nil))::acc)
  end.

Check search_mem.

Fixpoint all_no_mem (l:list (membrane_id * (list nposi * list nposi))) :=
   match l with nil => true | (a,(nil,hb))::ys => all_no_mem ys | _::_ => false end.

Fixpoint is_one_mem (l:list (membrane_id * (list nposi * list nposi))) :=
   match l with nil => false | (a,(nil,hb))::ys => is_one_mem ys | _::ys => all_no_mem ys end.

Fixpoint get_one (l:list (membrane_id * (list nposi * list nposi))) :=
   match l with nil => None | (a,(nil,hb))::ys => get_one ys | (a,b)::ys => Some a end.

Fixpoint grab_good (l:list (membrane_id * (list nposi * list nposi))) acc :=
   match l with nil => acc | (a,(nil,hb))::ys => grab_good ys acc | (a,(ha,hb))::ys => grab_good ys ((a,(ha,hb))::acc) end.

Fixpoint nlength {A:Type} (l:list A) : N := match l with nil => N.zero | x::xs => N.add (N.one) (nlength xs) end.

Fixpoint max_one (l:list (membrane_id * (list nposi * list nposi))) v acc accb :=
  match l with nil => (acc,accb) | (i,y)::ys => 
             if N.ltb v (nlength (fst y)) 
             then max_one ys (nlength (fst y)) (i,y) (acc::accb) 
             else max_one ys v acc ((i,y)::accb) end.

Fixpoint max_mem_id (l:list (membrane_id * (list nposi * list nposi))) v acc accb :=
  match l with nil => ((v,acc),accb)
            | (i,y)::ys => 
                if v <? i then max_mem_id ys i y ((v,acc)::accb) else max_mem_id ys v acc ((i,y)::accb)
  end.


Fixpoint gen_comm' (i:membrane_id) (j:membrane_id) (l: list nposi) (chan:var) acc :=
  match l with nil => acc
            | x::xs => gen_comm' i j xs (S chan) 
          ((OpExp (Recv chan (N.to_nat (fst x)) (N.to_nat (snd x))),[x], j)::
                    (OpExp (Send chan (N.to_nat (fst x)) (N.to_nat (snd x))),[x],i)::acc)
  end.

Fixpoint gen_comm j (l:list (membrane_id * (list nposi * list nposi))) (chan : var) acc accb :=
  match l with nil => (chan,(acc,accb))
            | (i,(x,y))::xs =>
        gen_comm j xs (chan + 2 * length x) (gen_comm' j i x chan acc) (gen_comm' i j x chan accb) 
  end.

Definition gen_comm_insert j l chan acc v := let mid := gen_comm j l chan acc nil in
                 (fst mid, (snd (snd mid))++v::(fst (snd mid))).

Fixpoint gen_comm_b j (l:list (membrane_id * (list nposi * list nposi))) (chan : var) acc :=
  match l with nil => (chan,acc)
            | (i,(x,y))::xs =>
        gen_comm_b j xs (chan + length x) (gen_comm' j i x chan acc)
  end.

Fixpoint collect_all_posi (l:list (membrane_id * (list nposi * list nposi))) acc :=
  match l with nil => acc | (i,(x,y))::xs =>  collect_all_posi xs (x++acc) end.

Fixpoint subtract_posi' (l: list nposi) (x:nposi) := 
  match l with nil => nil | y::ys => if nposi_eq y x then subtract_posi' ys x else y::subtract_posi' ys x end.

Fixpoint subtract_posi (l : list nposi) (y: list nposi) :=
  match y with nil => l | x::xs => subtract_posi (subtract_posi' l x) xs end.

Fixpoint push_to_mem_i i j v (l:list (membrane_id * (list nposi * list nposi))) acc :=
  match l with nil => acc | (k,(x,y))::xs =>
        if i =? k then push_to_mem_i i j v xs ((j,v++y)::acc)
        else if j =? k then push_to_mem_i i j v xs ((j,x++y)::acc) 
                  else push_to_mem_i i j v xs ((j,y)::acc)
  end.

Definition post_dec i (new:list (membrane_id * list (nposi))) (dc:list (list nposi * membrane_id)) xnum xset chan rea input acc :=
  let v := collect_all_posi rea nil in
   match v with nil => (chan,nil) 
             | y::ys => 
    match dec_mem dc y with None => 
       let pre_gen := gen_comm_insert i rea chan acc (OpNum xnum,xset,i) in
          (fst pre_gen, [(snd pre_gen,new)])
                      | Some j =>
       let mid := gen_comm_insert i rea chan acc (OpNum xnum,xset,i) in
       let pre_gen := gen_comm_b i rea (fst mid) acc in
          let post_gen := gen_comm' i j v (fst pre_gen) ((OpNum xnum,xset,i)::(snd pre_gen)) in
          (fst pre_gen + length v, ((OpNum xnum,xset,i)::(snd mid),new)::(post_gen, push_to_mem_i j i v input nil)::[])
     end
  end.


Definition assign_mem_s (new:list (membrane_id * list (nposi))) (dc:list (list nposi * membrane_id))
          (x:(N * list nposi)) (l : (list (myOpAux * list nposi * membrane_id))) (chan:var) := 
  let xset := snd x in
  match search_mem new xset nil with re => 
    if is_one_mem re then
         match get_one re with None => (chan,nil)
                                  | Some i => (chan,[((OpNum (fst x),xset,i)::l, new)])
         end
    else
       match grab_good re nil with nil => (chan, nil)
           | y::ys => 
         match max_one ys 0 y nil with ((i,(v,va)),rea) =>
           if N.ltb (5%N) (N.div (N.mul (nlength v) (10%N)) (nlength xset))
           then post_dec i new dc (fst x) xset chan rea re l
           else
             match max_mem_id ys (fst y) (snd y) nil with ((i',(v',va')),rea') =>
                   post_dec i' new dc (fst x) xset chan rea' re l
             end
          end
      end
  end.

Definition channel := 6.

Fixpoint assign_mem' dc (l : (list (myOpAux * list nposi))) acc :=
   match l with nil => acc
                | (OpNum x, y)::xs =>
   assign_mem' dc xs (fold_left (fun a b => let mid := assign_mem_s (snd b) dc (x,y) (fst b) (fst a) in
                                          (fst mid, snd a ++ snd mid)) (snd acc) (fst acc,nil))
                | a::xs => assign_mem' dc xs acc
   end.



Fixpoint assign_mem_more (new:list (membrane_id * list (nposi))) dc (l : list (list (myOpAux * list nposi))) acc :=
   match l with nil => acc 
            | x::xs => assign_mem_more new dc xs 
           (map (fun l => rev l) (fst (split (snd (assign_mem' dc x (channel,[([],new)])))))++acc)
   end.


Fixpoint find_empty_new' (l:list (membrane_id * list nposi)) (m: membrane_id) acc :=
  match l with nil => (m::acc) | (x,y)::xs => if x =? m then acc else find_empty_new' xs m acc end.
Fixpoint find_empy_new (l:list (membrane_id * list nposi)) (al: list membrane_id) acc :=
  match al with nil => acc | x::xs => find_empy_new l xs (find_empty_new' l x acc) end.

Fixpoint assign_new_mem (l:list (myOpAux * list nposi)) (al:list membrane_id) :=
   match al with nil => nil
            | x::xs => 
    match l with nil => nil
            | y::ys => (snd y,x)::assign_new_mem ys xs
    end
   end.

Fixpoint gen_empty_mem (m: list membrane_id) : list (membrane_id * list nposi) :=
   match m with nil => nil | (a::xl) => (a,nil)::gen_empty_mem xl end.

Definition gen_mem (news: list (myOpAux * list nposi)) (l:list (list (myOpAux * list nposi))) (ids:list membrane_id) :=
  let ql := (gen_mem_new news ids) in
  let vl := (turn_new (gen_mem_new news ids) nil) in 
   let al := find_empy_new vl ids nil in
     let dc := assign_new_mem news al in
       map (fun a => ql ++ a) (assign_mem_more (gen_empty_mem al ++ vl) dc l nil).
(* maintain the following. *)
(* ------------------------------------------------------------------------- *)
(* Basic list helpers                                                        *)
(* ------------------------------------------------------------------------- *)

(*
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
*)




(* ------------------------------------------------------------------------- *)
(* vars_of_exp                                                               *)
(* ------------------------------------------------------------------------- *)

(*
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
(*             hp <- gen_hp(R)                                  *)
(*        order-in-R + share_qubit => dependency.                          *)
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
  | AModMult a1 a2 a3 =>  vars_of_aexp a1 ++ vars_of_aexp a2 ++ vars_of_aexp a3
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
      | Send x _ => [x]
      | Recv x _ => [x]
      end
  | OpIf b _ _ =>
      vars_of_cbexp b
  end.

(* --- extract qubits touched by an op --- *)
Definition qubits_of_range (r : range) : nat :=
  let '(q,(_,_)) := r in q.

Definition qubits_of_locus (k : locus) : list nat :=
  map qubits_of_range k.

Check SKIP.
Print exp.
Fixpoint qubits_of_exp (e : exp) : list nat :=
  match e with
  | SKIP _x _a => []
  | X q _a     => [q]
  | H q _a     => [q]
  | QFT q _n   => [q]
  | RQFT q _n  => [q]
  | RZ _k q _a   => [q]
  | RRZ _k q _a  => [q]
  | SR _k q      => [q]
  | SRR _k q     => [q]
  | Addto _x q   => [q]
  | CU c _a e1   => c :: qubits_of_exp e1
  | Seq e1 e2    => qubits_of_exp e1 ++ qubits_of_exp e2
  end.

Definition qubits_of_cexp (c : cexp) : list nat :=
  match c with
  | CNew q _n      => [q]
  | CAppU k e      => qubits_of_locus k ++ qubits_of_exp e
  | CMeas _x k     => qubits_of_locus k
  end.


Definition qubits_of_cdexp (_d : cdexp) : list nat := [].

Definition qubits_of_myOp (o : myOp) : list nat :=
  match o with
  | OpAP a      => qubits_of_cexp a
  | OpDP d      => qubits_of_cdexp d
  | OpIf _b p q => []
  end.

Fixpoint qubits_of_ops (ops : op_list) : list nat :=
  match ops with
  | [] => []
  | o :: ops' => qubits_of_myOp o ++ qubits_of_ops ops'
  end.

Definition shares_any_qubit (o1 o2 : myOp) : bool :=
  existsb (fun q => existsb (Nat.eqb q) (qubits_of_myOp o2))
          (qubits_of_myOp o1).

Definition is_empty_meas (o : myOp) : bool :=
  match o with
  | OpAP (CMeas x k) =>
      match k with
      | [] => true
      | _  => false
      end
  | _ => false
  end.

Definition touches_program_qubit (all : list nat) (o : myOp) : bool :=
  existsb (fun q => existsb (Nat.eqb q) all) (qubits_of_myOp o).










(*
Definition qubits_of_range (r : range) : list var :=
  match r with
  | (q, _lo, _hi) => [q]
  end.

Definition qubits_of_locus (L : locus) : list var :=
  concat (map qubits_of_range L).


Definition qubits_of_cexp (c : cexp) : list var :=
  match c with
  | CNew q _     => [q]
  | CAppU _ e    => vars_of_exp e
  | CMeas _ k    => qubits_of_locus k   (* NOT vars_of_locus *)
  end.
*)
(* Extract qubits touched by a locus *)
Definition vars_of_bound (b : bound) : list var :=
  match b with
  | BVar v _ => [v]
  | BNum _ => []
  end.

Definition vars_of_range (r : range) : list var :=
  match r with
  | (x, lo, hi) => x :: vars_of_bound lo ++ vars_of_bound hi
  end.

Definition vars_of_locus (L : locus) : list var :=
  concat (map vars_of_range L).

(*
Definition qubits_of_myOp (o : myOp) : list var :=
  match o with
  | OpAP a => qubits_of_cexp a
  | OpDP _ => []          (* DP are classical comm ops, not “qubit sharing” *)
  | OpIf _ _ _ => []      (* guard is classical *)
  end.
*)
Definition share_qubit_myOp (o1 o2 : myOp) : bool :=
  negb (Nat.eqb
          (length (intersect (uniq (qubits_of_myOp o1))
                             (uniq (qubits_of_myOp o2))))
          0).

Fixpoint index_of_myOp (x : myOp) (xs : list myOp) : nat :=
  match xs with
  | [] => 0
  | y :: tl =>
      if myOp_eqb x y
      then 0
      else S (index_of_myOp x tl)
  end.


(*

Definition gen_hp (R : op_list) : hb_relation :=
  fun o1 o2 =>
    let i := index_of_myOp o1 R in
    let j := index_of_myOp o2 R in
    andb (Nat.ltb i j) (share_qubit_myOp o1 o2).

*)
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
(* ------------------------------------------------------------ *)
(* Safe topological ordering without permutations (Kahn-style)   *)
(* ------------------------------------------------------------ *)

Fixpoint remove_one (eqb : myOp -> myOp -> bool) (x : myOp) (xs : list myOp) : list myOp :=
  match xs with
  | [] => []
  | y :: tl => if eqb x y then tl else y :: remove_one eqb x tl
  end.

Definition has_incoming_from_nodes
  (hp : hb_relation) (nodes : list myOp) (x : myOp) : bool :=
  existsb (fun y => hp y x) nodes.

Definition available_nodes (hp : hb_relation) (nodes : list myOp) : list myOp :=
  filter (fun x => negb (has_incoming_from_nodes hp nodes x)) nodes.

Fixpoint nth_default_myOp (d : myOp) (xs : list myOp) (n : nat) : myOp :=
  match n with
  | 0 =>
      match xs with
      | [] => d
      | x :: _ => x
      end
  | S n' =>
      match xs with
      | [] => d
      | _ :: tl => nth_default_myOp d tl n'
      end
  end.

(* choose an available node based on schedule_index (tie-break) *)
Definition pick_available
  (schedule_index : nat) (avs : list myOp) : option myOp :=
  match avs with
  | [] => None
  | _ =>
      let idx := Nat.modulo schedule_index (length avs) in
      Some (nth_default_myOp (hd (OpAP (CNew 0 0)) avs) avs idx)
  end.

Fixpoint topo_kahn_fuel
  (hp : hb_relation)
  (schedule_index : nat)
  (nodes : list myOp)
  (fuel : nat)
  (acc  : list myOp)
  : option (list myOp) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match nodes with
      | [] => Some (rev acc)
      | _  =>
          let avs := available_nodes hp nodes in
          match pick_available schedule_index avs with
          | None => None (* cycle or inconsistent hp *)
          | Some x =>
              topo_kahn_fuel hp (S schedule_index)
                             (remove_one myOp_eqb x nodes)
                             fuel' (x :: acc)
          end
      end
  end.

Definition topo_kahn
  (hp : hb_relation)
  (schedule_index : nat)
  (nodes : list myOp)
  : option (list myOp) :=
  topo_kahn_fuel hp schedule_index nodes (S (length nodes)) [].

(*

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
*)
Definition seq_from_order (order : list myOp) : seq_relation :=
  fun o => index_of_myOp o order.


(*  seq <- gen_seq(S,hp) *)
Definition gen_seq_many
  (Kseq : nat)
  (schedule_index : nat)
  (hp : hb_relation)
  (os : op_list)
  : seq_relation :=
  (* Instead of enumerating Kseq different schedules, we generate one topo order
     and vary tie-breaking using schedule_index. *)
  match topo_kahn hp schedule_index os with
  | None => fun _ => 0
  | Some order => seq_from_order order
  end.

(*
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
*)
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
*)

(* ------------------------------------------------------------------------- *)
(*                              gen_prog                             *)
(* ------------------------------------------------------------------------- *)

Check gen_seq.
Check gen_mem.

Fixpoint insert_mem_id (i:membrane_id) (x:myOpAux * list nposi) acc := 
   match acc with nil => ([(i,[x])])
                | (a,b)::xs => if i =? a then (a,b++[x])::xs else (a,b)::(insert_mem_id i x xs)
   end.

Fixpoint distribute_op (l:list (myOpAux * list nposi * membrane_id)) acc :=
  match l with nil => acc
             | x::xs => distribute_op xs (insert_mem_id (snd x) (fst x) acc)
  end.

Fixpoint get_op (l: list (N * myOp)) i :=
  match l with nil => None | (x,y)::xs => if N.eqb i x then Some y else get_op xs i end.

Fixpoint turn_cexp_to_proc l p :=
   match l with nil => p | x::xs => AP x (turn_cexp_to_proc xs p) end.

Definition turn_op_to_proc x (p:process) :=
  match x with OpAP a => AP a p
             | OpIf b l r => PIf b (turn_cexp_to_proc l p) (turn_cexp_to_proc r p)
  end.

Fixpoint to_process (l:list (myOpAux * list nposi)) os :=
  match l with nil => Some PNil
            | (OpNum n, a)::xs =>
      match get_op os n with None => None
                           | Some x => 
          match to_process xs os with None => None
                                   | Some p => Some (turn_op_to_proc x p)
          end
      end
           | (OpExp a, b)::xs => 
          match to_process xs os with None => None
                                   | Some p => Some (AP a p)
          end
  end.

Check distribute_op.

Fixpoint to_prog (l:list (nat * list (myOpAux * list nposi))) os :=
  match l with nil => nil
            | x::xs => 
    match to_process (snd x) os with None => nil
                                 | Some a => (Memb (fst x) a)::to_prog xs os
    end
  end.


(* you might need the following functions to wirte the final algorithm. 
   os is generted from opListOrder. *)
Check opListOrder.
Check gen_hb.
Check gen_seq.
Check gen_mem.

Fixpoint gen_prog (l:list (list (myOpAux * list nposi * membrane_id))) os :=
  match l with nil => nil | x::xs => to_prog (distribute_op x nil) os::gen_prog xs os end.




(* ------------------------------------------------------------------------- *)
(* fitness / best candidate                                                  *)
(* ------------------------------------------------------------------------- *)
Fixpoint count_send_in_process (p:process) : nat :=
  match p with
  | PNil => 0
  | AP a p' =>
      match a with
      | Send _ _ _ => S (count_send_in_process p')
      | Recv _ _ _ => S (count_send_in_process p')
      | _ => count_send_in_process p'
      end
  | PIf _ p1 p2 =>
      count_send_in_process p1 + count_send_in_process p2
  end.
Definition count_send_in_memb (m:memb) : nat :=
  match m with
  | Memb _ p => count_send_in_process p
  end.
Print memb.

Fixpoint count_comm_ops (cfg:config) : nat :=
  match cfg with
  | nil => 0
  | m::xs => count_send_in_memb m + count_comm_ops xs
  end.
Fixpoint process_size (p:process) : nat :=
  match p with
  | PNil => 0
  | AP _ p' => S (process_size p')
  | PIf _ p1 p2 => process_size p1 + process_size p2
  end.

Definition memb_load (m:memb) : nat :=
  match m with
  | Memb _ p => process_size p
  end.
Fixpoint max_load (cfg:config) : nat :=
  match cfg with
  | nil => 0
  | m::xs => Nat.max (memb_load m) (max_load xs)
  end.
(* Weight for communication cost *)
Definition alpha : nat := 10.

(* Fitness function: minimize communication and load imbalance *)
Definition fit (cfg : config) : fitness_value :=
  (alpha * count_comm_ops cfg) + max_load cfg.

Fixpoint best_prog_aux
  (best:config)
  (bestv:nat)
  (xs:list config)
  : config :=
  match xs with
  | nil => best
  | x::tl =>
      let vx := fit x in
      if vx <? bestv
      then best_prog_aux x vx tl
      else best_prog_aux best bestv tl
  end.

Definition best_prog (xs:list config) : option config :=
  match xs with
  | nil => None
  | x::tl => Some (best_prog_aux x (fit x) tl)
  end.

(* ------------------------------------------------------------------------- *)
(*                          ALGO1                                            *)
(* ------------------------------------------------------------------------- *)

Definition autodisq_all
  (ops : op_list)
  (mids : list membrane_id)
  : list config :=
  let os := opListOrder ops in
  let hb := gen_hb os in
  let sq := gen_seq os hb in
  let mem := gen_mem (fst sq) (snd sq) mids in
  gen_prog mem os.

Definition autodisq_best
  (ops : op_list)
  (mids : list membrane_id)
  : option config :=
  best_prog (autodisq_all ops mids).

(* ------------------------------------------------------------------------- *)
(*                SAME   :      ALGO1                                        *)
(* ------------------------------------------------------------------------- *)



Fixpoint auto_disq_loop
  (best : option config)
  (cands : list config)
  : option config :=
  match cands with
  | [] => best
  | P :: xs =>
      match best with
      | None => auto_disq_loop (Some P) xs
      | Some B =>
          if fit P <? fit B
          then auto_disq_loop (Some P) xs
          else auto_disq_loop best xs
      end
  end.

Definition autodisq_best_1
  (ops : op_list)
  (mids : list membrane_id)
  : option config :=
  auto_disq_loop None (autodisq_all ops mids).




**)





