
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
              | a::yas => if same_name x a then (if nat_range_inter (snd x) (snd a) then true else intersect' x yas) else false
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
             | x::xs => (n,x)::opListOrder' xs (n+1)
  end.
Definition opListOrder l := opListOrder' l 0.

Definition empty_hp := fun (x y:N) => false.


(* hp relation is transitive closure. *)
Fixpoint gen_hb' (n:N) (x: N * myOp) l := 
  match l with nil => empty_hp
             | a::xas => gen_next n x a (gen_hb_single x a (gen_hb' n x xas))
  end.

Fixpoint gen_hb_a (n:N) (R : list (N * myOp)) acc :=
   match R with nil => acc
             | a::xas => gen_hb_a n xas (gen_hb' n a xas)
   end.
Definition gen_hb (R : list (N * myOp)) := gen_hb_a (N.of_nat (length R)) R empty_hp.



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
         match a with (j,OpAP q) => if sim_cexp q b then ((i,OpAP b)::xl++[(j,OpAP q)])::al else [(j,OpAP q)]::(((i,OpAP b)::xl)::al)
                    | (i,OpIf c d e) => [(i,OpIf c d e)]::(((i,OpAP b)::xl)::al)
         end
               | ((i,OpIf c d e)::xl)::al => [a]::((i,OpIf c d e)::xl)::al
  end.

Fixpoint partition_op' (l:list (N * myOp)) acc :=
  match l with nil => acc
                | x::xl => partition_op' xl (insert_op x acc)
  end.
Definition partition_op l := rev (partition_op' l []).


Fixpoint insert_all (x : myOpAux * list posi) (xs : list (myOpAux * list posi)) : list (list (myOpAux * list posi)) :=
  match xs with
  | [] => [[x]]
  | y :: tl =>
      (x :: y :: tl) :: map (fun zs => y :: zs) (insert_all x tl)
  end.

Fixpoint permutations (xs : list (myOpAux * list posi)) : list (list (myOpAux * list posi)) :=
  match xs with
  | [] => [[]]
  | x :: tl => concat (map (insert_all x) (permutations tl))
  end.

Fixpoint car_concat' (x:list (myOpAux * list posi)) (y : list (list (myOpAux * list posi))) := 
  match y with nil => nil
            | a::ys => (x++a)::(car_concat' x ys)
  end.

Fixpoint car_concat (x y:  list (list (myOpAux * list posi))) :=
   match x with nil => nil
              | a::xs => (car_concat' a y) ++ car_concat xs y
   end.

Fixpoint get_first (l:list (list (N * myOp))) acc := 
   match l with nil => acc
              | []::xs => get_first xs acc
              | (a::xs)::ys => get_first ys (match acc with (c,d) => (c++[a],d++[xs]) end)
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
           | S m => up_qubits x i m (acc++[(x,i+m)])
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
      match get_first l (nil,nil) with (nil,nil) => acc
                           | (a,b) => let good := (grab_related a re) in
                         assign_each m (insert_back a b
                               (fst (split good))) re (car_concat acc (permutations (get_nlocus good)))
      end
  end.

Definition gen_seq (l:list (N * myOp)) (re: hb_relation) := 
   let can := partition_op l in
   match can with nil => (nil,nil)
                | x::xs => (get_nlocus x,assign_each (length l - length x) xs re [nil])
   end.

(* ------------------------------------------------------------------------- *)
(* gen_mem                                                           *)
(* ------------------------------------------------------------------------- *)

Fixpoint count_a (t:nat) (new: list (myOpAux * list posi)) (a:membrane_id) acc :=
  match t with 0 => (acc,new)
            | S m => 
   match new with nil => (acc,nil)
               | x::xs => count_a m xs a (acc ++[(x,a)]) 
   end
  end.

Fixpoint gen_mem_new' (size:nat) (news: list (myOpAux * list posi)) (l:list membrane_id) (t:nat) acc :=
  match size with 0 => acc
               | S m =>
    match l with nil => acc | x::xs => 
       let (re,next) := (count_a t news x []) in
         gen_mem_new' m next xs t (acc++re)
    end
  end.
Definition gen_mem_new (news: list (myOpAux * list posi)) (l:list membrane_id) :=
  let v := ((length news) / (length l)) + 1 in gen_mem_new' (length news) news l v [].

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


Fixpoint insert_mem  (a: posi * membrane_id * list nat)  (l:list (list posi * membrane_id * list nat)) :=
  match l with nil => [([fst (fst a)], snd (fst a),snd a)]
            | (x,y, ids)::xs => if snd (fst a) =? y then ((fst (fst a))::x,y,snd a ++ ids)::xs else (x,y, ids) :: insert_mem a xs
  end.

Fixpoint set_inter (x y : (list posi)) :=
  match  x with nil => nil
              | a::xs => if set_mem posi_eq_dec a y then a::set_inter xs y else set_inter xs y
  end.

Fixpoint sub_locus_i (x: posi) (l:locus) :=
  match l with nil => false
   | (y,b)::xs => if ((fst x) =? y) && (fst b <=? snd x) && (snd x <? snd b)
                  then true else sub_locus_i x xs
  end.

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
          match set_inter x v
          with nil => search_hb x n hb xs checker
             | next => Some (w, next)
          end
          else search_hb x n hb xs checker
            | a::xs => search_hb x n hb xs (a::checker)
  end.

Fixpoint search_mem (new:list (membrane_id * list (posi * bool))) (x:list posi) acc :=
  match new with nil => acc
              | (i,y)::ys =>
   match set_inter x (fst (split y)) 
    with nil => search_mem ys x acc
       | next => search_mem ys x ((i,next)::acc)
   end
  end.


Fixpoint max_one (new:list (membrane_id * list posi)) a acc :=
  match new with nil => acc
             | x::xs => 
         if length (snd a) <? length  (snd x) then max_one xs x ([fst x])
         else if length (snd a) =? length (snd x) then max_one xs a (fst x::acc)
         else max_one xs a acc
  end.

Definition search_good_mem (new:list (membrane_id * list (posi * bool))) (x:list posi) :=
  match search_mem new x nil
    with nil => nil
      | y::ys => max_one ys y ([fst y])
  end.

Fixpoint find_least_q' (new:list (membrane_id * list (posi * bool))) a :=
  match new with nil => a 
    | x::xs => 
     if length (snd x) <? length (snd a) then find_least_q' xs x else find_least_q' xs a 
  end.
Definition find_least_q (new :list (membrane_id * list (posi * bool))) :=
  match new with nil => None | x::xs => Some (find_least_q' xs x) end.


Fixpoint subtract_aux (x: posi) (l:list (posi * bool)) (acc : list (posi * bool)) :=
  match l with nil => acc | y::ys => if posi_eq x (fst y) then subtract_aux x ys acc else subtract_aux x ys (y::acc) end.

Fixpoint subtract_posi (x: list posi) (l:list (posi * bool)) acc :=
  match x with nil => acc | y::ys => subtract_posi ys l (subtract_aux y l acc) end.

Fixpoint subtract_all (x: list posi) (new :list (membrane_id * list (posi * bool))) acc :=
    match new with nil => acc | (i,y)::ys =>  subtract_all x ys ((i,subtract_posi x y nil)::acc) end.

Fixpoint add_posi_true' (i:membrane_id) (x: list (posi*bool)) (new :list (membrane_id * list (posi * bool))) :=
   match new with nil => nil | (j,y)::ys => if i =? j then (j,x++y)::ys else (j,y)::add_posi_true' i x ys end.

Fixpoint add_true (x:list posi) := match x with nil => nil | y::ys => (y,true)::add_true ys end.

Definition add_posi_true i (x:list posi) new := add_posi_true' i (add_true x) new.

Definition turn_true_aux (x:list posi) (y:list (posi * bool)) :=
  let v := subtract_posi x y nil in add_true x++v.

Fixpoint turn_true i (x:list posi) (new :list (membrane_id * list (posi * bool))) :=
  match new with nil => nil | (j,y)::ys => if i =? j then (j, turn_true_aux x y)::ys else (j,y)::turn_true i x ys end.

Fixpoint find_all_in (l: list posi) (new:list (membrane_id * list (posi * bool))) :=
  match new with nil => None
              | (i,la)::xs => 
          if sublist_posi l (fst (split la)) then Some (i,la) else find_all_in l xs
  end.
(*basd on the above, it is enough. also find the prior instruction that has a hb relation for this one,
   if they have similar qubits, then put in the same place, 
   otherwise, the instruction can be placed same as initial qubit places or an least qubit membrane. *)

Fixpoint search_all_mem (i:membrane_id) (x:list posi) (new :list (membrane_id * list (posi * bool))) :=
  match new with nil => nil
              | (a,b)::xs =>
        if i =? a
        then search_all_mem i x xs
        else
       match set_inter x (fst (split b))
          with nil => search_all_mem i x xs
             | next => (a,next)::search_all_mem i x xs
       end
  end.

Fixpoint gen_comm' (i:membrane_id) (j:membrane_id) (l: list posi) (chan:var) :=
  match l with nil => nil
            | x::xs => (OpExp (Send chan (fst x) (snd x)),[x],i)::(OpExp (Recv chan (fst x) (snd x)),[x], j)::gen_comm' i j xs (S chan)
  end.

Fixpoint gen_comm j l (chan : var) acc :=
  match l with nil => (chan,acc)
            | (i,x)::xs => gen_comm j xs (chan + length x) (gen_comm' j i x chan++acc)
  end.

Definition assign_mem_s (new:list (membrane_id * list (posi * bool))) (hb:hb_relation)
          (x:(N * list posi)) (l : (list (myOpAux * list posi * membrane_id))) (chan:var) := 
  let xset := snd x in
  match find_all_in xset new
    with None => 
     match search_hb xset (fst x) hb (rev l) nil
        with None => 
         match search_good_mem new xset
           with nil => (chan,[]) (* error *)
              | next => fold_left (fun a b => let mid := gen_comm b (search_all_mem b (snd x) new) (fst a) nil in
               (fst mid,(l++(OpNum (fst x),snd x,b)::(snd mid), add_posi_true b xset (subtract_all xset new nil))::snd a)) next (chan,nil)
         end
           | Some (i, re) => 
           if 5 <? ((length re) * 10) / (length xset)
           then let mid := gen_comm i (search_all_mem i (snd x) new) chan nil in
            (fst mid, [(l++(OpNum (fst x),snd x,i)::(snd mid), add_posi_true i xset (subtract_all xset new nil))])
           else 
      match search_good_mem new xset
        with nil => (chan,[]) (* error *)
           | next => 
        match find_least_q new
              with None => (chan,[]) (* error *)
                 | Some na =>
      fold_left (fun a b => let mid := gen_comm b (search_all_mem b (snd x) new) (fst a) nil in
               (fst mid,(l++(OpNum (fst x),snd x,b)::(snd mid), add_posi_true b xset (subtract_all xset new nil))::snd a))
                   (fst na :: next) (chan,nil)
        end
      end
     end
       | Some (i,la) => (chan,[(l++[(OpNum (fst x),snd x,i)], turn_true i xset new)])
  end.

Definition channel := 1000.

Fixpoint assign_mem' (hb:hb_relation) (l : (list (myOpAux * list posi))) acc :=
   match l with nil => acc
                | (OpNum x, y)::xs =>
   assign_mem' hb xs (fold_left (fun a b => let mid := assign_mem_s (snd b) hb (x,y) (fst b) (fst a) in
                                          (fst mid, snd a ++ snd mid)) (snd acc) (fst acc,nil))
                | a::xs => assign_mem' hb xs acc
   end.
Fixpoint assign_mem_more (new:list (membrane_id * list (posi * bool))) (hb: hb_relation) (l : list (list (myOpAux * list posi))) acc :=
   match l with nil => acc 
            | x::xs => assign_mem_more new hb xs (fst (split (snd (assign_mem' hb x (channel,[([],new)]))))++acc)
   end.

Fixpoint turn_new (l:list (myOpAux * list posi * membrane_id)) acc :=
  match l with nil => acc
             | (x,y)::xs => turn_new xs ((y,add_true (snd x))::acc)
end.

Definition gen_mem (news: list (myOpAux * list posi)) (l:list (list (myOpAux * list posi))) (ids:list membrane_id) (hb: hb_relation) := 
  map (fun a => (gen_mem_new news ids)++a) (assign_mem_more (turn_new (gen_mem_new news ids) nil) hb l nil).

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

Fixpoint insert_mem_id (i:membrane_id) (x:myOpAux * list posi) acc := 
   match acc with nil => ([(i,[x])])
                | (a,b)::xs => if i =? a then (a,b++[x])::xs else (a,b)::(insert_mem_id i x xs)
   end.

Fixpoint distribute_op (l:list (myOpAux * list posi * membrane_id)) acc :=
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

Fixpoint to_process (l:list (myOpAux * list posi)) os :=
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

Fixpoint to_prog (l:list (nat * list (myOpAux * list posi))) os :=
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

Fixpoint gen_prog (l:list (list (myOpAux * list posi * membrane_id))) os :=
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
  let mem := gen_mem (fst sq) (snd sq) mids hb in
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











(*
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

Definition INF_SCORE : fitness_value := 1000000000%nat.


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
Definition locus_myOp (op : myOp) : list var := qubits_of_myOp op.

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


(* ---------- membership for myOp ---------- *)
Fixpoint mem_myOp (x : myOp) (xs : list myOp) : bool :=
  match xs with
  | [] => false
  | y :: tl => if myOp_eqb x y then true else mem_myOp x tl
  end.

Fixpoint remove_myOp (x : myOp) (xs : list myOp) : list myOp :=
  match xs with
  | [] => []
  | y :: tl => if myOp_eqb x y then tl else y :: remove_myOp x tl
  end.

(* outgoing edges *)
Definition succs (hp : hb_relation) (nodes : list myOp) (x : myOp) : list myOp :=
  filter (fun y => hp x y) nodes.

(* DFS: returns true iff a cycle is found reachable from x *)
Fixpoint dfs_cycle_fuel
  (hp : hb_relation)
  (nodes : list myOp)
  (fuel : nat)
  (visiting visited : list myOp)
  (x : myOp)
  : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
      if mem_myOp x visiting then true          (* back-edge => cycle *)
      else if mem_myOp x visited then false     (* already done *)
      else
        let visiting' := x :: visiting in
        let nxt := succs hp nodes x in
        if existsb (dfs_cycle_fuel hp nodes fuel' visiting' visited) nxt
        then true
        else false
  end.

(* Outer loop: check all nodes (graph may be disconnected) *)
Fixpoint has_cycle_from_all_fuel
  (hp : hb_relation)
  (nodes todo : list myOp)
  (fuel : nat)
  (visited : list myOp)
  : bool :=
  match fuel with
  | 0 => false
  | S fuel' =>
      match todo with
      | [] => false
      | x :: tl =>
          if mem_myOp x visited then
            has_cycle_from_all_fuel hp nodes tl fuel' visited
          else
            if dfs_cycle_fuel hp nodes (length nodes + 1) [] visited x
            then true
            else
              (* mark x visited to avoid restarting from it again *)
              has_cycle_from_all_fuel hp nodes tl fuel' (x :: visited)
      end
  end.

Definition hp_has_cycle_dfs (hp : hb_relation) (nodes : list myOp) : bool :=
  has_cycle_from_all_fuel hp nodes nodes (length nodes + 1) [].

Definition hp_acyclic (hp : hb_relation) (nodes : list myOp) : bool :=
  negb (hp_has_cycle_dfs hp nodes).





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
(*
Definition opt_hp (hp_l : hb_relation) (seq_l : seq_relation) : hb_relation :=
  fun a b => andb (hp_l a b) (Nat.ltb (seq_l a) (seq_l b)).
*)
Definition opt_hp (hp_l : hb_relation) (seq_l : seq_relation) : hb_relation :=
  fun a b =>
    if Nat.eqb (seq_l a) (seq_l b)
    then hp_l a b          (* keep edge when tied *)
    else andb (hp_l a b) (Nat.ltb (seq_l a) (seq_l b)).

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

Definition has_pred (eqb: myOp -> myOp -> bool)
                   (hp : hb_relation) (nodes : list myOp) (x : myOp) : bool :=
  existsb (fun y => andb (negb (eqb y x)) (hp y x)) nodes.

Definition ready (eqb: myOp -> myOp -> bool)
                (hp : hb_relation) (nodes : list myOp) (x : myOp) : bool :=
  negb (has_pred eqb hp nodes x).

Definition pick_ready (eqb: myOp -> myOp -> bool)
                     (hp : hb_relation) (nodes : list myOp) : list myOp :=
  filter (ready eqb hp nodes) nodes.

Fixpoint layer_partition_fuel
  (fuel  : nat)
  (eqb   : myOp -> myOp -> bool)
  (hp    : hb_relation)
  (nodes : list myOp)
  : list (list myOp) :=
  match fuel with
  | 0 => []
  | S fuel' =>
      match nodes with
      | [] => []
      | _ =>
          let layer := pick_ready eqb hp nodes in
          if Nat.eqb (length layer) 0 then
            [] 
          else
            let rest := remove_ops eqb nodes layer in
            layer :: layer_partition_fuel fuel' eqb hp rest
      end
  end.

Definition layer_partition
  (eqb  : myOp -> myOp -> bool)
  (hp   : hb_relation)
  (nodes : list myOp)
  : list (list myOp) :=
  layer_partition_fuel (length nodes) eqb hp nodes.

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
Definition alg3_loop_fold (seq_l : seq_relation) (S : list (list myOp)) : list process :=
  concat (map (fun sbar => gen_ops seq_l sbar) S).

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
  (eqb   : myOp -> myOp -> bool)
  (ops_l : list myOp)
  (hp_l  : hb_relation)
  (seq_l : seq_relation)
  : list process :=
  let hp_l' := opt_hp hp_l seq_l in
  let S := scc_partition  eqb hp_l' (uniq_ops eqb ops_l) in
  alg3_loop seq_l S ([] : list process).

Definition auto_parallelize_alg3_layers
  (eqb   : myOp -> myOp -> bool)
  (ops_l : list myOp)
  (hp_l  : hb_relation)
  (seq_l : seq_relation)
  : list process :=
  let hp_l' := opt_hp hp_l seq_l in
  let S := layer_partition eqb hp_l' (uniq_ops eqb ops_l) in
  alg3_loop seq_l S ([] : list process).










*)
