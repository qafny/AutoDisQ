
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

module Coq__1 = struct
 (** val add : int -> int -> int **)let rec add = (+)
end
include Coq__1

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

module type TotalLeBool' =
 sig
  type t

  val leb : t -> t -> bool
 end

module Nat =
 struct
  (** val eqb : int -> int -> bool **)

  let rec eqb = ( = )

  (** val leb : int -> int -> bool **)

  let rec leb = ( <= )

  (** val ltb : int -> int -> bool **)

  let ltb = ( < )

  (** val max : int -> int -> int **)

  let rec max n0 m =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> m)
      (fun n' ->
      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
        (fun _ -> n0)
        (fun m' -> Stdlib.succ (max n' m'))
        m)
      n0

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q u =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> (q, u))
      (fun x' ->
      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
        (fun _ -> divmod x' y (Stdlib.succ q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val div : int -> int -> int **)

  let div = ( / )
 end

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of int
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : int -> int **)

  let rec succ = Pervasives.succ

  (** val add : int -> int -> int **)

  let rec add = (+)

  (** val add_carry : int -> int -> int **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (add_carry p q))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun _ -> (fun p->1+2*p) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->2*p) (add_carry p q))
        (fun q -> (fun p->1+2*p) (add p q))
        (fun _ -> (fun p->2*p) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> (fun p->1+2*p) (succ q))
        (fun q -> (fun p->2*p) (succ q))
        (fun _ -> (fun p->1+2*p) 1)
        y)
      x

  (** val pred_double : int -> int **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> (fun p->1+2*p) ((fun p->2*p) p))
      (fun p -> (fun p->1+2*p) (pred_double p))
      (fun _ -> 1)
      x

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos 1
  | IsPos p -> IsPos ((fun p->1+2*p) p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos ((fun p->2*p) p)
  | x0 -> x0

  (** val double_pred_mask : int -> mask **)

  let double_pred_mask x =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p -> IsPos ((fun p->2*p) ((fun p->2*p) p)))
      (fun p -> IsPos ((fun p->2*p) (pred_double p)))
      (fun _ -> IsNul)
      x

  (** val sub_mask : int -> int -> mask **)

  let rec sub_mask x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double_mask (sub_mask p q))
        (fun q -> succ_double_mask (sub_mask p q))
        (fun _ -> IsPos ((fun p->2*p) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> IsNeg)
        (fun _ -> IsNeg)
        (fun _ -> IsNul)
        y)
      x

  (** val sub_mask_carry : int -> int -> mask **)

  and sub_mask_carry x y =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun q -> double_mask (sub_mask p q))
        (fun _ -> IsPos (pred_double p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q -> double_mask (sub_mask_carry p q))
        (fun q -> succ_double_mask (sub_mask_carry p q))
        (fun _ -> double_pred_mask p)
        y)
      (fun _ -> IsNeg)
      x

  (** val mul : int -> int -> int **)

  let rec mul = ( * )

  (** val compare_cont : comparison -> int -> int -> comparison **)

  let rec compare_cont = fun c x y -> if x=y then c else if x<y then Lt else Gt

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val eqb : int -> int -> bool **)

  let rec eqb p q =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun p0 -> op a (iter_op op p0 (op a a)))
      (fun p0 -> iter_op op p0 (op a a))
      (fun _ -> a)
      p

  (** val to_nat : int -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Stdlib.succ 0)

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n0 =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n0
 end

module N =
 struct
  (** val zero : int **)

  let zero =
    0

  (** val one : int **)

  let one =
    1

  (** val succ_double : int -> int **)

  let succ_double x =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 1)
      (fun p -> ((fun p->1+2*p) p))
      x

  (** val double : int -> int **)

  let double n0 =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> ((fun p->2*p) p))
      n0

  (** val succ : int -> int **)

  let succ = Pervasives.succ

  (** val add : int -> int -> int **)

  let add = (+)

  (** val sub : int -> int -> int **)

  let sub = fun n m -> Pervasives.max 0 (n-m)

  (** val mul : int -> int -> int **)

  let mul = ( * )

  (** val compare : int -> int -> comparison **)

  let compare = fun x y -> if x=y then Eq else if x<y then Lt else Gt

  (** val eqb : int -> int -> bool **)

  let eqb n0 m =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> true)
        (fun _ -> false)
        m)
      (fun p ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> false)
        (fun q -> Coq_Pos.eqb p q)
        m)
      n0

  (** val leb : int -> int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val pos_div_eucl : int -> int -> int * int **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = double r in
      if leb b r' then ((succ_double q), (sub r' b)) else ((double q), r'))
      (fun _ ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> (0, 1))
        (fun p ->
        (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
          (fun _ -> (0, 1))
          (fun _ -> (0, 1))
          (fun _ -> (1, 0))
          p)
        b)
      a

  (** val div_eucl : int -> int -> int * int **)

  let div_eucl a b =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> (0, 0))
      (fun na ->
      (fun f0 fp n -> if n=0 then f0 () else fp n)
        (fun _ -> (0, a))
        (fun _ -> pos_div_eucl na b)
        b)
      a

  (** val div : int -> int -> int **)

  let div = fun a b -> if b=0 then 0 else a/b

  (** val to_nat : int -> int **)

  let to_nat a =
    (fun f0 fp n -> if n=0 then f0 () else fp n)
      (fun _ -> 0)
      (fun p -> Coq_Pos.to_nat p)
      a

  (** val of_nat : int -> int **)

  let of_nat n0 =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> 0)
      (fun n' -> (Coq_Pos.of_succ_nat n'))
      n0
 end

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| [] -> []
| x :: l0 -> app x (concat l0)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t0 -> (f a) :: (map f t0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t0 -> fold_left f t0 (f a0 b)

(** val split : ('a1 * 'a2) list -> 'a1 list * 'a2 list **)

let rec split = function
| [] -> ([], [])
| p :: tl ->
  let (x, y) = p in
  let (left, right) = split tl in ((x :: left), (y :: right))

type var = int

type range = var * (int * int)

type locus = range list

type aexp =
| BA of var
| Num of int
| APlus of aexp * aexp
| AMult of aexp * aexp
| AModMult of aexp * aexp * aexp

type cbexp =
| CEq of aexp * aexp
| CLt of aexp * aexp

type exp =
| SKIP of var * aexp
| X of var * aexp
| CU of var * aexp * exp
| RZ of int * var * aexp
| RRZ of int * var * aexp
| SR of int * var
| SRR of int * var
| QFT of var * int
| RQFT of var * int
| H of var * aexp
| Addto of var * var
| Seq of exp * exp

type cexp =
| CNew of range
| CAppU of locus * exp
| CMeas of var * locus
| Send of var * var * int
| Recv of var * var * int

type process =
| PNil
| AP of cexp * process
| PIf of cbexp * process * process

type memb =
| Memb of var * process

type config = memb list

module Sort =
 functor (X:TotalLeBool') ->
 struct
  (** val merge : X.t list -> X.t list -> X.t list **)

  let rec merge l1 l2 =
    let rec merge_aux l3 =
      match l1 with
      | [] -> l3
      | a1 :: l1' ->
        (match l3 with
         | [] -> l1
         | a2 :: l2' ->
           if X.leb a1 a2 then a1 :: (merge l1' l3) else a2 :: (merge_aux l2'))
    in merge_aux l2

  (** val merge_list_to_stack :
      X.t list option list -> X.t list -> X.t list option list **)

  let rec merge_list_to_stack stack l =
    match stack with
    | [] -> (Some l) :: []
    | y :: stack' ->
      (match y with
       | Some l' -> None :: (merge_list_to_stack stack' (merge l' l))
       | None -> (Some l) :: stack')

  (** val merge_stack : X.t list option list -> X.t list **)

  let rec merge_stack = function
  | [] -> []
  | y :: stack' ->
    (match y with
     | Some l -> merge l (merge_stack stack')
     | None -> merge_stack stack')

  (** val iter_merge : X.t list option list -> X.t list -> X.t list **)

  let rec iter_merge stack = function
  | [] -> merge_stack stack
  | a :: l' -> iter_merge (merge_list_to_stack stack (a :: [])) l'

  (** val sort : X.t list -> X.t list **)

  let sort =
    iter_merge []

  (** val flatten_stack : X.t list option list -> X.t list **)

  let rec flatten_stack = function
  | [] -> []
  | o :: stack' ->
    (match o with
     | Some l -> app l (flatten_stack stack')
     | None -> flatten_stack stack')
 end

type 'a set = 'a list

(** val set_mem : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> bool **)

let rec set_mem aeq_dec a = function
| [] -> false
| a1 :: x1 -> if aeq_dec a a1 then true else set_mem aeq_dec a x1

(** val set_inter : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set **)

let rec set_inter aeq_dec x y =
  match x with
  | [] -> []
  | a1 :: x1 ->
    if set_mem aeq_dec a1 y
    then a1 :: (set_inter aeq_dec x1 y)
    else set_inter aeq_dec x1 y

type membrane_id = var

type myOp =
| OpAP of cexp
| OpIf of cbexp * cexp list * cexp list

type op_list = myOp list

type hb_relation = int -> int -> bool

type myOpAux =
| OpNum of int
| OpExp of cexp

type fitness_value = int

module RangeOrder =
 struct
  type t = range

  (** val leb : range -> range -> bool **)

  let leb x y =
    if Nat.ltb (fst x) (fst y)
    then true
    else if Nat.eqb (fst x) (fst y)
         then if Nat.ltb (fst (snd x)) (fst (snd y))
              then true
              else if Nat.eqb (fst (snd x)) (fst (snd y))
                   then Nat.leb (snd (snd x)) (snd (snd y))
                   else false
         else false
 end

module SortRange = Sort(RangeOrder)

(** val nat_range_inter : (int * int) -> (int * int) -> bool **)

let nat_range_inter x y =
  (||) ((&&) (Nat.leb (fst x) (fst y)) (Nat.ltb (fst y) (snd x)))
    ((&&) (Nat.ltb (fst y) (fst x)) (Nat.ltb (fst x) (snd y)))

(** val same_name : range -> range -> bool **)

let same_name x y =
  Nat.eqb (fst x) (fst y)

(** val intersect' : range -> locus -> bool **)

let rec intersect' x = function
| [] -> false
| a :: yas ->
  if (&&) (same_name x a) (nat_range_inter (snd x) (snd a))
  then true
  else intersect' x yas

(** val intersect : locus -> locus -> bool **)

let rec intersect x y =
  match x with
  | [] -> false
  | a :: xas -> if intersect' a y then true else intersect xas y

(** val get_locus : cexp -> range list **)

let get_locus = function
| CNew a -> a :: []
| CAppU (l, _) -> l
| CMeas (_, k) -> k
| Send (_, x0, a) -> (x0, (a, (Stdlib.succ a))) :: []
| Recv (_, x0, y) -> (x0, (y, (Stdlib.succ y))) :: []

(** val get_loci : cexp list -> range list **)

let get_loci x =
  fold_left (fun a b -> app (get_locus b) a) x []

(** val get_vars_cexp : cexp -> var list **)

let get_vars_cexp = function
| CMeas (x0, _) -> x0 :: []
| _ -> []

(** val get_vars_aexp : aexp -> var list **)

let rec get_vars_aexp = function
| BA a -> a :: []
| Num _ -> []
| APlus (e1, e2) -> app (get_vars_aexp e1) (get_vars_aexp e2)
| AMult (e1, e2) -> app (get_vars_aexp e1) (get_vars_aexp e2)
| AModMult (e1, e2, e3) ->
  app (get_vars_aexp e1) (app (get_vars_aexp e2) (get_vars_aexp e3))

(** val get_vars_bexp : cbexp -> var list **)

let get_vars_bexp = function
| CEq (a, b) -> app (get_vars_aexp a) (get_vars_aexp b)
| CLt (a, b) -> app (get_vars_aexp a) (get_vars_aexp b)

(** val is_inter : cexp -> cexp -> bool **)

let is_inter x y =
  intersect (get_locus x) (get_locus y)

(** val inter_vars : var list -> var list -> bool **)

let inter_vars xs ys =
  match set_inter (=) xs ys with
  | [] -> false
  | _ :: _ -> true

(** val gen_hb_single :
    (int * myOp) -> (int * myOp) -> (int -> int -> bool) -> int -> int -> bool **)

let gen_hb_single x y acc i j =
  match snd x with
  | OpAP xa ->
    (match snd y with
     | OpAP ya ->
       if (&&) (N.eqb i (fst x)) (N.eqb j (fst y))
       then is_inter xa ya
       else acc i j
     | OpIf (ya, la, ra) ->
       if (&&) (N.eqb i (fst x)) (N.eqb j (fst y))
       then (||) (intersect (get_locus xa) (get_loci (app la ra)))
              (inter_vars (get_vars_cexp xa) (get_vars_bexp ya))
       else acc i j)
  | OpIf (xa, la, ra) ->
    (match snd y with
     | OpAP xa0 ->
       if (&&) (N.eqb i (fst y)) (N.eqb j (fst x))
       then (||) (intersect (get_locus xa0) (get_loci (app la ra)))
              (inter_vars (get_vars_cexp xa0) (get_vars_bexp xa))
       else acc i j
     | OpIf (ya, lb, rb) ->
       if (&&) (N.eqb i (fst y)) (N.eqb j (fst x))
       then (||) (intersect (get_loci (app la ra)) (get_loci (app lb rb)))
              (inter_vars (get_vars_bexp xa) (get_vars_bexp ya))
       else acc i j)

(** val opListOrder' : op_list -> int -> (int * myOp) list **)

let rec opListOrder' l n0 =
  match l with
  | [] -> []
  | x :: xs -> (n0, x) :: (opListOrder' xs (N.succ n0))

(** val opListOrder : op_list -> (int * myOp) list **)

let opListOrder l =
  opListOrder' l 0

(** val gen_hb' :
    (int * myOp) -> (int * myOp) list -> (int -> int -> bool) -> int -> int
    -> bool **)

let rec gen_hb' x l acc =
  match l with
  | [] -> acc
  | a :: xas -> gen_hb_single x a (gen_hb' x xas acc)

(** val gen_hb_a :
    (int * myOp) list -> (int -> int -> bool) -> int -> int -> bool **)

let rec gen_hb_a r acc =
  match r with
  | [] -> acc
  | a :: xas -> gen_hb_a xas (gen_hb' a xas acc)

(** val trans_closure :
    int -> int -> (int -> int -> bool) -> int -> int -> bool **)

let trans_closure n0 x acc a b =
  if (&&) ((&&) ((&&) ((&&) (N.ltb a x) (N.ltb x b)) (N.ltb b n0)) (acc a x))
       (acc x b)
  then true
  else acc a b

(** val gen_hb_trans :
    int -> int -> (int -> int -> bool) -> int -> int -> bool **)

let rec gen_hb_trans size n0 acc =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> acc)
    (fun m -> gen_hb_trans size m (trans_closure size (N.of_nat m) acc))
    n0

(** val gen_hb : (int * myOp) list -> int -> int -> bool **)

let gen_hb r =
  gen_hb_trans (N.of_nat (length r)) (length r)
    (gen_hb_a r (fun _ _ -> false))

(** val sim_exp : exp -> exp -> bool **)

let rec sim_exp x y =
  match x with
  | SKIP (_, _) -> (match y with
                    | SKIP (_, _) -> true
                    | _ -> false)
  | X (_, _) -> (match y with
                 | X (_, _) -> true
                 | _ -> false)
  | CU (_, _, x1) ->
    (match y with
     | CU (_, _, y1) -> sim_exp x1 y1
     | _ -> false)
  | RZ (_, _, _) -> (match y with
                     | RZ (_, _, _) -> true
                     | _ -> false)
  | RRZ (_, _, _) -> (match y with
                      | RRZ (_, _, _) -> true
                      | _ -> false)
  | SR (_, _) -> (match y with
                  | SR (_, _) -> true
                  | _ -> false)
  | SRR (_, _) -> (match y with
                   | SRR (_, _) -> true
                   | _ -> false)
  | QFT (_, _) -> (match y with
                   | QFT (_, _) -> true
                   | _ -> false)
  | RQFT (_, _) -> (match y with
                    | RQFT (_, _) -> true
                    | _ -> false)
  | H (_, _) -> (match y with
                 | H (_, _) -> true
                 | _ -> false)
  | Addto (_, _) -> (match y with
                     | Addto (_, _) -> true
                     | _ -> false)
  | Seq (x1, x2) ->
    (match y with
     | Seq (y1, y2) -> (&&) (sim_exp x1 y1) (sim_exp x2 y2)
     | _ -> false)

(** val sim_cexp : cexp -> cexp -> bool **)

let sim_cexp x y =
  match x with
  | CNew _ -> (match y with
               | CNew _ -> true
               | _ -> false)
  | CAppU (_, a) -> (match y with
                     | CAppU (_, b) -> sim_exp a b
                     | _ -> false)
  | CMeas (_, _) -> (match y with
                     | CMeas (_, _) -> true
                     | _ -> false)
  | Send (_, _, _) -> (match y with
                       | Send (_, _, _) -> true
                       | _ -> false)
  | Recv (_, _, _) -> (match y with
                       | Recv (_, _, _) -> true
                       | _ -> false)

(** val insert_op :
    (int * myOp) -> (int * myOp) list list -> (int * myOp) list list **)

let insert_op a acc = match acc with
| [] -> (a :: []) :: []
| y :: al ->
  (match y with
   | [] -> (a :: []) :: al
   | p :: xl ->
     let (i, m) = p in
     (match m with
      | OpAP b ->
        let (i0, m0) = a in
        (match m0 with
         | OpAP q ->
           if sim_cexp q b
           then ((i, (OpAP b)) :: (app xl ((i0, (OpAP q)) :: []))) :: al
           else ((i0, (OpAP q)) :: []) :: acc
         | OpIf (c, d, e) ->
           ((i0, (OpIf (c, d, e))) :: []) :: (((i0, (OpAP b)) :: xl) :: al))
      | OpIf (c, d, e) -> (a :: []) :: (((i, (OpIf (c, d, e))) :: xl) :: al)))

(** val partition_op' :
    (int * myOp) list -> (int * myOp) list list -> (int * myOp) list list **)

let rec partition_op' l acc =
  match l with
  | [] -> acc
  | x :: xl -> partition_op' xl (insert_op x acc)

(** val partition_op : (int * myOp) list -> (int * myOp) list list **)

let partition_op l =
  rev (partition_op' l [])

type nposi = int * int

(** val nposi_eq : nposi -> nposi -> bool **)

let nposi_eq r1 r2 =
  let (x1, y1) = r1 in let (x2, y2) = r2 in (&&) (N.eqb x1 x2) (N.eqb y1 y2)

(** val insert_all :
    (myOpAux * nposi list) -> (myOpAux * nposi list) list -> (myOpAux * nposi
    list) list list **)

let rec insert_all x = function
| [] -> (x :: []) :: []
| y :: tl -> (x :: (y :: tl)) :: (map (fun zs -> y :: zs) (insert_all x tl))

(** val permutations :
    (myOpAux * nposi list) list -> (myOpAux * nposi list) list list **)

let rec permutations = function
| [] -> [] :: []
| x :: tl -> concat (map (insert_all x) (permutations tl))

(** val car_concat' :
    (myOpAux * nposi list) list -> (myOpAux * nposi list) list list ->
    (myOpAux * nposi list) list list **)

let rec car_concat' x = function
| [] -> []
| a :: ys -> (app x a) :: (car_concat' x ys)

(** val car_concat :
    (myOpAux * nposi list) list list -> (myOpAux * nposi list) list list ->
    (myOpAux * nposi list) list list **)

let rec car_concat x y =
  match x with
  | [] -> []
  | a :: xs -> app (car_concat' a y) (car_concat xs y)

(** val get_first : (int * myOp) list list -> (int * myOp) list **)

let rec get_first = function
| [] -> []
| l0 :: ys ->
  (match l0 with
   | [] -> get_first ys
   | a :: _ -> a :: (get_first ys))

(** val in_list_a : (int * myOp) -> (int * myOp) list -> bool **)

let rec in_list_a x = function
| [] -> false
| a :: xs -> if N.eqb (fst x) (fst a) then true else in_list_a x xs

(** val remove_first :
    (int * myOp) list list -> (int * myOp) list -> (int * myOp) list list **)

let rec remove_first l x =
  match l with
  | [] -> []
  | l0 :: ys ->
    (match l0 with
     | [] -> [] :: (remove_first ys x)
     | a :: xs ->
       if in_list_a a x
       then xs :: (remove_first ys x)
       else (a :: xs) :: (remove_first ys x))

(** val grab_related' :
    (int * myOp) -> (int * myOp) list -> hb_relation -> (int * myOp) list ->
    (int * myOp) list **)

let rec grab_related' x l re acc =
  match l with
  | [] -> acc
  | a :: xs ->
    if re (fst x) (fst a)
    then grab_related' x xs re acc
    else grab_related' x xs re (app acc (a :: []))

(** val up_qubits :
    var -> int -> int -> (int * int) list -> (int * int) list **)

let rec up_qubits x i n0 acc =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> acc)
    (fun m ->
    up_qubits x i m
      (app acc (((N.of_nat x), (N.add (N.of_nat i) (N.of_nat m))) :: [])))
    n0

(** val cutToQubits' : range list -> (int * int) list **)

let rec cutToQubits' = function
| [] -> []
| r0 :: xs ->
  let (x, p) = r0 in
  let (l0, r) = p in app (up_qubits x l0 (sub r l0) []) (cutToQubits' xs)

(** val cutToQubits : range list -> (int * int) list **)

let cutToQubits l =
  cutToQubits' (SortRange.sort l)

(** val get_locus_in_op : (int * myOp) list -> range list **)

let rec get_locus_in_op = function
| [] -> []
| p :: la ->
  let (_, m) = p in
  (match m with
   | OpAP y ->
     (match get_locus y with
      | [] -> get_locus_in_op la
      | r :: l0 -> app (r :: l0) (get_locus_in_op la))
   | OpIf (_, _, _) -> get_locus_in_op la)

(** val get_nlocus :
    (int * myOp) list -> (myOpAux * (int * int) list) list **)

let rec get_nlocus = function
| [] -> []
| x :: xs ->
  ((OpNum (fst x)),
    (cutToQubits (get_locus_in_op (x :: [])))) :: (get_nlocus xs)
    
(* ============================================================ *)
(* Bounded permutation helper                                   *)
(* ============================================================ *)

let permutations_one (l : (myOpAux * nposi list) list)
  : (myOpAux * nposi list) list list =
  [l]



(** val assign_each :
    int -> (int * myOp) list list -> hb_relation -> (myOpAux * nposi list)
    list list -> (myOpAux * nposi list) list list **)

(* ============================================================ *)
(* Modified assign_each                                         *)
(* ============================================================ *)

let rec assign_each n0 l re acc =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> acc)
    (fun m ->
      match get_first l with
      | [] -> acc
      | p :: l0 ->
          let good = grab_related' p l0 re (p :: []) in
          let next_acc =
            car_concat acc (permutations_one (get_nlocus good))
          in
          assign_each m (remove_first l good) re next_acc)
    n0

(** val gen_seq :
    (int * myOp) list -> hb_relation -> (myOpAux * (int * int) list)
    list * (myOpAux * nposi list) list list **)

let gen_seq l re =
  let can = partition_op l in
  (match can with
   | [] -> ([], [])
   | x :: xs ->
     ((get_nlocus x),
       (assign_each (sub (length l) (length x)) xs re ([] :: []))))

(** val count_a :
    (myOpAux * nposi list) list -> membrane_id list -> ((myOpAux * nposi
    list) * membrane_id) list -> ((myOpAux * nposi list) * membrane_id)
    list * (myOpAux * nposi list) list **)

let rec count_a new0 l acc =
  match l with
  | [] -> (acc, new0)
  | a :: ys ->
    (match new0 with
     | [] -> (acc, [])
     | x :: xs -> count_a xs ys ((x, a) :: acc))

(** val gen_mem_new' :
    int -> (myOpAux * nposi list) list -> membrane_id list ->
    ((myOpAux * nposi list) * membrane_id) list -> ((myOpAux * nposi
    list) * membrane_id) list **)

let rec gen_mem_new' t0 news l acc =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> acc)
    (fun m ->
    let (re, next) = count_a news l [] in gen_mem_new' m next l (app acc re))
    t0

(** val gen_mem_new :
    (myOpAux * nposi list) list -> membrane_id list -> ((myOpAux * nposi
    list) * membrane_id) list **)

let gen_mem_new news l =
  let v = add (Nat.div (length news) (length l)) (Stdlib.succ 0) in
  gen_mem_new' v news l []

(** val insert_posis :
    (membrane_id * nposi list) list -> membrane_id -> nposi list ->
    (membrane_id * nposi list) list **)

let rec insert_posis l a x =
  match l with
  | [] -> []
  | p :: ys ->
    let (n0, y) = p in
    if Nat.eqb a n0
    then (n0, (app y x)) :: ys
    else (n0, y) :: (insert_posis ys a x)

(** val turn_new :
    ((myOpAux * nposi list) * membrane_id) list -> (membrane_id * nposi list)
    list -> (membrane_id * nposi list) list **)

let rec turn_new l acc =
  match l with
  | [] -> acc
  | p :: xs -> let (x, y) = p in turn_new xs (insert_posis acc y (snd x))

(** val posi_set_in : nposi -> nposi list -> bool **)

let rec posi_set_in a = function
| [] -> false
| x :: xs -> if nposi_eq a x then true else posi_set_in a xs

(** val set_inter0 :
    nposi list -> nposi list -> (nposi list * nposi list) -> nposi
    list * nposi list **)

let rec set_inter0 x y acc =
  match x with
  | [] -> acc
  | a :: xs ->
    if posi_set_in a y
    then set_inter0 xs y ((a :: (fst acc)), (snd acc))
    else set_inter0 xs y ((fst acc), (a :: (snd acc)))

(** val dec_mem :
    (nposi list * membrane_id) list -> nposi -> membrane_id option **)

let rec dec_mem l x =
  match l with
  | [] -> None
  | p :: ys ->
    let (y, i) = p in if posi_set_in x y then Some i else dec_mem ys x

(** val search_mem :
    (membrane_id * nposi list) list -> nposi list -> (membrane_id * (nposi
    list * nposi list)) list -> (membrane_id * (nposi list * nposi list)) list **)

let rec search_mem new0 x acc =
  match new0 with
  | [] -> acc
  | p :: ys ->
    let (i, y) = p in search_mem ys x ((i, (set_inter0 x y ([], []))) :: acc)

(** val all_no_mem :
    (membrane_id * (nposi list * nposi list)) list -> bool **)

let rec all_no_mem = function
| [] -> true
| p :: ys ->
  let (_, p0) = p in
  let (l0, _) = p0 in (match l0 with
                       | [] -> all_no_mem ys
                       | _ :: _ -> false)

(** val is_one_mem :
    (membrane_id * (nposi list * nposi list)) list -> bool **)

let rec is_one_mem = function
| [] -> false
| p :: ys ->
  let (_, p0) = p in
  let (l0, _) = p0 in
  (match l0 with
   | [] -> is_one_mem ys
   | _ :: _ -> all_no_mem ys)

(** val get_one :
    (membrane_id * (nposi list * nposi list)) list -> membrane_id option **)

let rec get_one = function
| [] -> None
| p :: ys ->
  let (a, b) = p in
  let (l0, _) = b in (match l0 with
                      | [] -> get_one ys
                      | _ :: _ -> Some a)

(** val grab_good :
    (membrane_id * (nposi list * nposi list)) list -> (membrane_id * (nposi
    list * nposi list)) list -> (membrane_id * (nposi list * nposi list)) list **)

let rec grab_good l acc =
  match l with
  | [] -> acc
  | p :: ys ->
    let (a, p0) = p in
    let (ha, hb) = p0 in
    (match ha with
     | [] -> grab_good ys acc
     | _ :: _ -> grab_good ys ((a, (ha, hb)) :: acc))

(** val nlength : 'a1 list -> int **)

let rec nlength = function
| [] -> N.zero
| _ :: xs -> N.add N.one (nlength xs)

(** val max_one :
    (membrane_id * (nposi list * nposi list)) list -> int ->
    (membrane_id * (nposi list * nposi list)) -> (membrane_id * (nposi
    list * nposi list)) list -> (membrane_id * (nposi list * nposi
    list)) * (membrane_id * (nposi list * nposi list)) list **)

let rec max_one l v acc accb =
  match l with
  | [] -> (acc, accb)
  | p :: ys ->
    let (i, y) = p in
    if N.ltb v (nlength (fst y))
    then max_one ys (nlength (fst y)) (i, y) (acc :: accb)
    else max_one ys v acc ((i, y) :: accb)

(** val max_mem_id :
    (membrane_id * (nposi list * nposi list)) list -> int -> (nposi
    list * nposi list) -> (int * (nposi list * nposi list)) list ->
    (int * (nposi list * nposi list)) * (int * (nposi list * nposi list)) list **)

let rec max_mem_id l v acc accb =
  match l with
  | [] -> ((v, acc), accb)
  | p :: ys ->
    let (i, y) = p in
    if Nat.ltb v i
    then max_mem_id ys i y ((v, acc) :: accb)
    else max_mem_id ys v acc ((i, y) :: accb)

(** val gen_comm' :
    membrane_id -> membrane_id -> nposi list -> var -> ((myOpAux * nposi
    list) * membrane_id) list -> ((myOpAux * nposi list) * membrane_id) list **)

let rec gen_comm' i j l chan acc =
  match l with
  | [] -> acc
  | x :: xs ->
    gen_comm' i j xs (Stdlib.succ chan) ((((OpExp (Recv (chan,
      (N.to_nat (fst x)), (N.to_nat (snd x))))), (x :: [])), j) :: ((((OpExp
      (Send (chan, (N.to_nat (fst x)), (N.to_nat (snd x))))), (x :: [])),
      i) :: acc))

(** val gen_comm :
    membrane_id -> (membrane_id * (nposi list * nposi list)) list -> var ->
    ((myOpAux * nposi list) * membrane_id) list -> ((myOpAux * nposi
    list) * membrane_id) list -> var * (((myOpAux * nposi
    list) * membrane_id) list * ((myOpAux * nposi list) * membrane_id) list) **)

let rec gen_comm j l chan acc accb =
  match l with
  | [] -> (chan, (acc, accb))
  | p :: xs ->
    let (i, p0) = p in
    let (x, _) = p0 in
    gen_comm j xs (add chan (mul (Stdlib.succ (Stdlib.succ 0)) (length x)))
      (gen_comm' j i x chan acc) (gen_comm' i j x chan accb)

(** val gen_comm_insert :
    membrane_id -> (membrane_id * (nposi list * nposi list)) list -> var ->
    ((myOpAux * nposi list) * membrane_id) list -> ((myOpAux * nposi
    list) * membrane_id) -> var * ((myOpAux * nposi list) * membrane_id) list **)

let gen_comm_insert j l chan acc v =
  let mid = gen_comm j l chan acc [] in
  ((fst mid), (app (snd (snd mid)) (v :: (fst (snd mid)))))

(** val gen_comm_b :
    membrane_id -> (membrane_id * (nposi list * nposi list)) list -> var ->
    ((myOpAux * nposi list) * membrane_id) list -> var * ((myOpAux * nposi
    list) * membrane_id) list **)

let rec gen_comm_b j l chan acc =
  match l with
  | [] -> (chan, acc)
  | p :: xs ->
    let (i, p0) = p in
    let (x, _) = p0 in
    gen_comm_b j xs (add chan (length x)) (gen_comm' j i x chan acc)

(** val collect_all_posi :
    (membrane_id * (nposi list * nposi list)) list -> nposi list -> nposi list **)

let rec collect_all_posi l acc =
  match l with
  | [] -> acc
  | p :: xs ->
    let (_, p0) = p in let (x, _) = p0 in collect_all_posi xs (app x acc)

(** val push_to_mem_i :
    int -> int -> nposi list -> (membrane_id * (nposi list * nposi list))
    list -> (int * nposi list) list -> (int * nposi list) list **)

let rec push_to_mem_i i j v l acc =
  match l with
  | [] -> acc
  | (k, (x, y)) :: xs ->
      if Nat.eqb i k
      then push_to_mem_i i j v xs ((k, app v y) :: acc)
      else if Nat.eqb j k
      then push_to_mem_i i j v xs ((k, app x y) :: acc)
      else push_to_mem_i i j v xs ((k, y) :: acc)

(** val post_dec :
    membrane_id -> (membrane_id * nposi list) list -> (nposi
    list * membrane_id) list -> int -> nposi list -> var ->
    (membrane_id * (nposi list * nposi list)) list -> (membrane_id * (nposi
    list * nposi list)) list -> ((myOpAux * nposi list) * membrane_id) list
    -> var * (((myOpAux * nposi list) * membrane_id)
    list * (membrane_id * nposi list) list) list **)

let post_dec i new0 dc xnum xset chan rea input acc =
  let v = collect_all_posi rea [] in
  (match v with
   | [] -> (chan, [])
   | y :: _ ->
     (match dec_mem dc y with
      | Some j ->
        let mid = gen_comm_insert i rea chan acc (((OpNum xnum), xset), i) in
        let pre_gen = gen_comm_b i rea (fst mid) acc in
        let post_gen =
          gen_comm' i j v (fst pre_gen) ((((OpNum xnum), xset),
            i) :: (snd pre_gen))
        in
        ((add (fst pre_gen) (length v)), ((((((OpNum xnum), xset),
        i) :: (snd mid)), new0) :: ((post_gen,
        (push_to_mem_i j i v input [])) :: [])))
      | None ->
        let pre_gen = gen_comm_insert i rea chan acc (((OpNum xnum), xset), i)
        in
        ((fst pre_gen), (((snd pre_gen), new0) :: []))))
        
let rec mem_pos p xs =
  match xs with
  | [] -> false
  | y :: ys -> y = p || mem_pos p ys

let rec add_nodup xs ys =
  match xs with
  | [] -> ys
  | x :: tl ->
      if mem_pos x ys then add_nodup tl ys
      else add_nodup tl (x :: ys)

let rec add_qubits_to_mem i xs new0 =
  match new0 with
  | [] -> []
  | (j, ys) :: tl ->
      if i = j
      then (j, add_nodup xs ys) :: add_qubits_to_mem i xs tl
      else (j, ys) :: add_qubits_to_mem i xs tl

(** val assign_mem_s :
    (membrane_id * nposi list) list -> (nposi list * membrane_id) list ->
    (int * nposi list) -> ((myOpAux * nposi list) * membrane_id) list -> var
    -> var * (((myOpAux * nposi list) * membrane_id)
    list * (membrane_id * nposi list) list) list **)
    
(* ============================================================ *)
(* Capacity control                                             *)
(* ============================================================ *)

let mem_qubit_load (new0 : (membrane_id * nposi list) list) (i : membrane_id) : int =
  match List.assoc_opt i new0 with
  | Some xs -> List.length xs
  | None -> 0

(* Small capacity to force distributed placement and Send/Recv *)
let membrane_capacity = 8

let mem_has_capacity (new0 : (membrane_id * nposi list) list) (i : membrane_id) (xset : nposi list) : bool =
  let current = mem_qubit_load new0 i in
  current + List.length xset <= membrane_capacity

let rec set_inter0 x y (acc_common, acc_rest) =
  match x with
  | [] -> (List.rev acc_common, List.rev acc_rest)
  | a :: xs ->
      if List.mem a y
      then set_inter0 xs y (a :: acc_common, acc_rest)
      else set_inter0 xs y (acc_common, a :: acc_rest)

let rec search_mem new0 x acc =
  match new0 with
  | [] -> acc
  | (i, y) :: ys ->
      let inter = set_inter0 x y ([], []) in
      search_mem ys x ((i, inter) :: acc)
      
 (* ============================================================ *)
(* Force remote placement helpers                               *)
(* ============================================================ *)

let rec pick_other_membrane (src : membrane_id) (new0 : (membrane_id * nposi list) list)
  : membrane_id option =
  match new0 with
  | [] -> None
  | (j, _) :: tl -> if j = src then pick_other_membrane src tl else Some j

let force_remote_insert
    (src : membrane_id)
    (dst : membrane_id)
    (xnum : int)
    (xset : nposi list)
    (l : ((myOpAux * nposi list) * membrane_id) list)
    (chan : int)
    (new0 : (membrane_id * nposi list) list)
  : int * ((((myOpAux * nposi list) * membrane_id) list * (membrane_id * nposi list) list) list) =
  let comm = gen_comm' src dst xset chan [] in
  let next_chan = chan + (2 * List.length xset) in
  let new0' = add_qubits_to_mem dst xset new0 in
  (next_chan, [((app comm [(((OpNum xnum), xset), dst)]), new0')])
  
(* ============================================================ *)
(* Operation-load-aware placement                               *)
(* ============================================================ *)

let rec op_load_in_partial l mid =
  match l with
  | [] -> 0
  | (((_aux, _qs), m)) :: xs ->
      if Nat.eqb m mid
      then Stdlib.succ (op_load_in_partial xs mid)
      else op_load_in_partial xs mid

let overlap_size x y =
  length (fst (set_inter0 x y ([], [])))

let import_cost xset local_qs =
  sub (length xset) (overlap_size xset local_qs)

let score_mem_for_op partial xset mid local_qs =
  let imports = import_cost xset local_qs in
  let op_load = op_load_in_partial partial mid in
  add (mul 4 imports) (mul 5 op_load)

let op_capacity = 6

let over_op_capacity partial mid =
  Nat.ltb op_capacity (op_load_in_partial partial mid)

let rec best_mem_by_score partial xset candidates current_best current_score =
  match candidates with
  | [] -> current_best
  | (mid, (local_qs, _rest)) :: xs ->
      if over_op_capacity partial mid then
        best_mem_by_score partial xset xs current_best current_score
      else
        let s = score_mem_for_op partial xset mid local_qs in
        if Nat.ltb s current_score
        then best_mem_by_score partial xset xs mid s
        else best_mem_by_score partial xset xs current_best current_score
        
let rec insert_scored_candidate cand scored =
  match scored with
  | [] -> [cand]
  | ((s1, _, _) as c1) :: tl ->
      let (s, _, _) = cand in
      if Nat.ltb s s1 then cand :: scored
      else c1 :: insert_scored_candidate cand tl

let rec take_scored n xs =
  match n, xs with
  | 0, _ -> []
  | _, [] -> []
  | n, x :: tl -> x :: take_scored (n - 1) tl

let scored_candidates partial xset candidates =
  let rec aux cs acc =
    match cs with
    | [] -> acc
    | (mid, (local_qs, rest_qs)) :: tl ->
        if over_op_capacity partial mid then
          aux tl acc
        else
          let s = score_mem_for_op partial xset mid local_qs in
          aux tl (insert_scored_candidate (s, mid, (local_qs, rest_qs)) acc)
  in
  aux candidates []
let assign_mem_s new0 dc x l chan =
  let xset = snd x in
  let re = search_mem new0 xset [] in
  match re with
  | [] -> (chan, [])
  | _ ->
      let ranked =
        match scored_candidates l xset re with
        | [] ->
            (* fallback: allow all if capacity filtered everything *)
            scored_candidates [] xset re
        | ys -> ys
      in
      let top = take_scored 3 ranked in

      let rec build_choices cs acc =
        match cs with
        | [] -> acc
        | (_score, chosen_mid, _data) :: tl ->
            if is_one_mem re
            then
              let choice =
                (((((OpNum (fst x)), xset), chosen_mid) :: l), new0)
              in
              build_choices tl (choice :: acc)
            else
              let others =
                List.filter (fun (m, _) -> not (Nat.eqb m chosen_mid)) re
              in
              let mid_res =
                post_dec chosen_mid new0 dc (fst x) xset chan others re l
              in
              let choices = snd mid_res in
              build_choices tl (app choices acc)
      in
      (chan, build_choices top [])  

(**
let assign_mem_s new0 dc x l chan =
  let xset = snd x in
  let re = search_mem new0 xset [] in
  if is_one_mem re
  then
    match get_one re with
    | None -> (chan, [])
    | Some i ->
        (chan, [(((((OpNum (fst x)), xset), i) :: l), new0)])
  else
    match grab_good re [] with
    | [] -> (chan, [])
    | y :: ys ->
        let (p, rea) = max_one ys 0 y [] in
        let (i, _) = p in
        post_dec i new0 dc (fst x) xset chan rea re l
        
        
        **)
(** val channel : int **)

let channel =
  Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ 0)))))

(** val assign_mem' :
    (nposi list * membrane_id) list -> (myOpAux * nposi list) list ->
    (var * (((myOpAux * nposi list) * membrane_id)
    list * (membrane_id * nposi list) list) list) -> var * (((myOpAux * nposi
    list) * membrane_id) list * (membrane_id * nposi list) list) list **)

let rec assign_mem' dc l acc =
  match l with
  | [] -> acc
  | a :: xs ->
    let (m, y) = a in
    (match m with
     | OpNum x ->
       assign_mem' dc xs
         (fold_left (fun a0 b ->
           let mid = assign_mem_s (snd b) dc (x, y) (fst b) (fst a0) in
           ((fst mid), (app (snd a0) (snd mid)))) (snd acc) ((fst acc), []))
     | OpExp _ -> assign_mem' dc xs acc)

(** val assign_mem_more :
    (membrane_id * nposi list) list -> (nposi list * membrane_id) list ->
    (myOpAux * nposi list) list list -> ((myOpAux * nposi
    list) * membrane_id) list list -> ((myOpAux * nposi list) * membrane_id)
    list list **)

let rec assign_mem_more new0 dc l acc =
  match l with
  | [] -> acc
  | x :: xs ->
    assign_mem_more new0 dc xs
      (app
        (map rev
          (fst (split (snd (assign_mem' dc x (channel, (([], new0) :: [])))))))
        acc)

(** val find_empty_new' :
    (membrane_id * nposi list) list -> membrane_id -> membrane_id list ->
    membrane_id list **)

let rec find_empty_new' l m acc =
  match l with
  | [] -> m :: acc
  | p :: xs ->
    let (x, _) = p in if Nat.eqb x m then acc else find_empty_new' xs m acc

(** val find_empy_new :
    (membrane_id * nposi list) list -> membrane_id list -> membrane_id list
    -> membrane_id list **)

let rec find_empy_new l al acc =
  match al with
  | [] -> acc
  | x :: xs -> find_empy_new l xs (find_empty_new' l x acc)

(** val assign_new_mem :
    (myOpAux * nposi list) list -> membrane_id list -> (nposi
    list * membrane_id) list **)

let rec assign_new_mem l = function
| [] -> []
| x :: xs ->
  (match l with
   | [] -> []
   | y :: ys -> ((snd y), x) :: (assign_new_mem ys xs))

(** val gen_empty_mem :
    membrane_id list -> (membrane_id * nposi list) list **)

let rec gen_empty_mem = function
| [] -> []
| a :: xl -> (a, []) :: (gen_empty_mem xl)

(* ============================================================ *)
(* Small take helper                                            *)
(* ============================================================ *)

  let rec take n xs =
  match n, xs with
  | 0, _ -> []
  | _, [] -> []
  | n, x :: tl -> x :: take (n - 1) tl

let fallback_mid ql =
  match ql with
  | [] -> 0
  | (_, mid) :: _ -> mid



(** val gen_mem :
    (myOpAux * nposi list) list -> (myOpAux * nposi list) list list ->
    membrane_id list -> ((myOpAux * nposi list) * membrane_id) list list **)

(* ============================================================ *)
(* Modified gen_mem                                             *)
(* ============================================================ *)
let gen_mem news l ids =
  let ql = gen_mem_new news ids in
  let vl = turn_new (gen_mem_new news ids) [] in
  let al = find_empy_new vl ids [] in
  let dc = assign_new_mem news al in
  let base_new0 = app (gen_empty_mem al) vl in
  let res =
    map
      (fun a -> app ql a)
      (assign_mem_more base_new0 dc l [])
  in
  match res with
  | [] ->
      let mid = fallback_mid ql in
      (match take 3 l with
       | [] -> [ql]
       | xs ->
           map
             (fun x -> app ql (map (fun y -> (y, mid)) x))
             xs)
  | _ -> res
  
(** val insert_mem_id :
    membrane_id -> (myOpAux * nposi list) -> (int * (myOpAux * nposi list)
    list) list -> (membrane_id * (myOpAux * nposi list) list) list **)

let rec insert_mem_id i x = function
| [] -> (i, (x :: [])) :: []
| y :: xs ->
  let (a, b) = y in
  if Nat.eqb i a
  then (a, (app b (x :: []))) :: xs
  else (a, b) :: (insert_mem_id i x xs)

(** val distribute_op :
    ((myOpAux * nposi list) * membrane_id) list -> (int * (myOpAux * nposi
    list) list) list -> (int * (myOpAux * nposi list) list) list **)

let rec distribute_op l acc =
  match l with
  | [] -> acc
  | x :: xs -> distribute_op xs (insert_mem_id (snd x) (fst x) acc)

(** val get_op : (int * myOp) list -> int -> myOp option **)

let rec get_op l i =
  match l with
  | [] -> None
  | p :: xs -> let (x, y) = p in if N.eqb i x then Some y else get_op xs i

(** val turn_cexp_to_proc : cexp list -> process -> process **)

let rec turn_cexp_to_proc l p =
  match l with
  | [] -> p
  | x :: xs -> AP (x, (turn_cexp_to_proc xs p))

(** val turn_op_to_proc : myOp -> process -> process **)

let turn_op_to_proc x p =
  match x with
  | OpAP a -> AP (a, p)
  | OpIf (b, l, r) ->
    PIf (b, (turn_cexp_to_proc l p), (turn_cexp_to_proc r p))

(** val to_process :
    (myOpAux * nposi list) list -> (int * myOp) list -> process option **)

let rec to_process l os =
  match l with
  | [] -> Some PNil
  | p :: xs ->
    let (m, _) = p in
    (match m with
     | OpNum n0 ->
       (match get_op os n0 with
        | Some x ->
          (match to_process xs os with
           | Some p0 -> Some (turn_op_to_proc x p0)
           | None -> None)
        | None -> None)
     | OpExp a ->
       (match to_process xs os with
        | Some p0 -> Some (AP (a, p0))
        | None -> None))

(** val to_prog :
    (int * (myOpAux * nposi list) list) list -> (int * myOp) list -> memb list **)

let rec to_prog l os =
  match l with
  | [] -> []
  | x :: xs ->
    (match to_process (snd x) os with
     | Some a -> (Memb ((fst x), a)) :: (to_prog xs os)
     | None -> [])
     
     
     (* ============================================================ *)
(* True distributed lowering helpers                            *)
(* ============================================================ *)

let rec has_if_ops = function
  | [] -> false
  | (_, OpIf _) :: _ -> true
  | _ :: xs -> has_if_ops xs

let rec assoc_opt_mem k = function
  | [] -> None
  | (k', v) :: xs -> if Nat.eqb k k' then Some v else assoc_opt_mem k xs

let rec owner_of_pos owners p =
  match owners with
  | [] -> None
  | (q, mid) :: xs -> if nposi_eq q p then Some mid else owner_of_pos xs p

let rec set_owner owners p mid =
  match owners with
  | [] -> [(p, mid)]
  | (q, m) :: xs ->
      if nposi_eq q p
      then (p, mid) :: xs
      else (q, m) :: set_owner xs p mid

let rec set_owner_many owners ps mid =
  match ps with
  | [] -> owners
  | p :: xs -> set_owner_many (set_owner owners p mid) xs mid

let rec append_cexp_to_mem mid ce acc =
  match acc with
  | [] -> [(mid, [ce])]
  | (m, xs) :: tl ->
      if Nat.eqb mid m
      then (m, app xs [ce]) :: tl
      else (m, xs) :: append_cexp_to_mem mid ce tl

let rec add_initial_owners_from_solution sol os owners =
  match sol with
  | [] -> owners
  | (((aux, qs), mid)) :: xs ->
      let owners' =
        match aux with
        | OpNum n ->
            (match get_op os n with
             | Some (OpAP (CNew r)) ->
                 set_owner_many owners (cutToQubits [r]) mid
             | _ -> owners)
        | OpExp (CNew r) ->
            set_owner_many owners (cutToQubits [r]) mid
        | _ -> owners
      in
      add_initial_owners_from_solution xs os owners'

let rec max_explicit_chan_in_cexp = function
  | CNew _ -> 0
  | CAppU (_, _) -> 0
  | CMeas (_, _) -> 0
  | Send (c, _, _) -> c
  | Recv (c, _, _) -> c

let rec max_explicit_chan_in_process = function
  | PNil -> 0
  | AP (ce, p') -> Nat.max (max_explicit_chan_in_cexp ce) (max_explicit_chan_in_process p')
  | PIf (_, p1, p2) ->
      Nat.max (max_explicit_chan_in_process p1) (max_explicit_chan_in_process p2)

let rec max_explicit_chan_in_config = function
  | [] -> 0
  | Memb (_, p) :: xs ->
      Nat.max (max_explicit_chan_in_process p) (max_explicit_chan_in_config xs)

let ensure_local_qubits dst qs owners bufs chan =
  let rec go qs owners bufs chan =
    match qs with
    | [] -> (chan, owners, bufs)
    | q :: tl ->
        (match owner_of_pos owners q with
         | Some src when not (Nat.eqb src dst) ->
             let v = N.to_nat (fst q) in
             let idx = N.to_nat (snd q) in
             let bufs1 = append_cexp_to_mem src (Send (chan, v, idx)) bufs in
             let bufs2 = append_cexp_to_mem dst (Recv (chan, v, idx)) bufs1 in
             let owners' = set_owner owners q dst in
             go tl owners' bufs2 (Stdlib.succ chan)
         | _ ->
             go tl owners bufs chan)
  in
  go qs owners bufs chan

let to_prog_from_cexps grouped =
  let rec aux = function
    | [] -> []
    | (mid, ces) :: xs -> Memb (mid, turn_cexp_to_proc ces PNil) :: aux xs
  in
  aux grouped
  
  
 let lower_solution_distributed sol os =
  let owners0 = add_initial_owners_from_solution sol os [] in

  let rec go xs owners bufs chan =
    match xs with
    | [] ->
        to_prog_from_cexps bufs

    | (((aux, _qs), mid)) :: tl ->

        begin
          match aux with

          | OpExp ce ->
              let owners', bufs', chan' =
                match ce with
                | CNew r ->
                    (set_owner_many owners (cutToQubits [r]) mid,
                     append_cexp_to_mem mid ce bufs,
                     chan)

                | Recv (_, x, y) ->
                    (set_owner owners ((N.of_nat x),(N.of_nat y)) mid,
                     append_cexp_to_mem mid ce bufs,
                     chan)

                | _ ->
                    (owners,
                     append_cexp_to_mem mid ce bufs,
                     chan)
              in
              go tl owners' bufs' chan'

          | OpNum n ->
              begin
                match get_op os n with

                | Some (OpAP ce) ->
                    begin
                      match ce with

                      | CNew r ->
                          let owners' =
                            set_owner_many owners (cutToQubits [r]) mid
                          in
                          let bufs' =
                            append_cexp_to_mem mid ce bufs
                          in
                          go tl owners' bufs' chan

                      | CAppU (loc,e) ->
                          let qbs = cutToQubits loc in
                          let (chan',owners',bufs') =
                            ensure_local_qubits mid qbs owners bufs chan
                          in
                          let bufs'' =
                            append_cexp_to_mem mid (CAppU(loc,e)) bufs'
                          in
                          go tl owners' bufs'' chan'

                      | CMeas (x,loc) ->
                          let qbs = cutToQubits loc in
                          let (chan',owners',bufs') =
                            ensure_local_qubits mid qbs owners bufs chan
                          in
                          let bufs'' =
                            append_cexp_to_mem mid (CMeas(x,loc)) bufs'
                          in
                          go tl owners' bufs'' chan'

                      | Send _ | Recv _ ->
                          let bufs' =
                            append_cexp_to_mem mid ce bufs
                          in
                          go tl owners bufs' chan

                    end

                | _ ->
                    go tl owners bufs chan

              end

        end

  in
  go sol owners0 [] 100000
(** val gen_prog :
    ((myOpAux * nposi list) * membrane_id) list list -> (int * myOp) list ->
    memb list list **)

let rec gen_prog l os =
  if has_if_ops os
  then
    (* Fallback to old behavior if OpIf exists *)
    match l with
    | [] -> []
    | x :: xs -> (to_prog (distribute_op x []) os) :: (gen_prog xs os)
  else
    match l with
    | [] -> []
    | x :: xs -> (lower_solution_distributed x os) :: (gen_prog xs os)

(** val count_send_in_process : process -> int **)

let rec count_send_in_process = function
| PNil -> 0
| AP (a, p') ->
  (match a with
   | Send (_, _, _) -> Stdlib.succ (count_send_in_process p')
   | Recv (_, _, _) -> Stdlib.succ (count_send_in_process p')
   | _ -> count_send_in_process p')
| PIf (_, p1, p2) -> add (count_send_in_process p1) (count_send_in_process p2)

(** val count_send_in_memb : memb -> int **)

let count_send_in_memb = function
| Memb (_, p) -> count_send_in_process p

(** val count_comm_ops : config -> int **)

let rec count_comm_ops = function
| [] -> 0
| m :: xs -> add (count_send_in_memb m) (count_comm_ops xs)

(** val process_size : process -> int **)

let rec process_size = function
| PNil -> 0
| AP (_, p') -> Stdlib.succ (process_size p')
| PIf (_, p1, p2) -> add (process_size p1) (process_size p2)

(** val memb_load : memb -> int **)

let memb_load = function
| Memb (_, p) -> process_size p

(** val max_load : config -> int **)

let rec max_load = function
| [] -> 0
| m :: xs -> Nat.max (memb_load m) (max_load xs)

(** val alpha : int **)

let alpha =
  Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    0)))))))))

(** val fit : config -> fitness_value **)

let fit cfg =
  add (mul alpha (count_comm_ops cfg)) (max_load cfg)

(** val best_prog_aux : config -> int -> config list -> config **)

let rec best_prog_aux best bestv = function
| [] -> best
| x :: tl ->
  let vx = fit x in
  if Nat.ltb vx bestv
  then best_prog_aux x vx tl
  else best_prog_aux best bestv tl

(** val best_prog : config list -> config option **)

let best_prog = function
| [] -> None
| x :: tl -> Some (best_prog_aux x (fit x) tl)

(** val autodisq_all : op_list -> membrane_id list -> config list **)

let autodisq_all ops mids =
  let os = opListOrder ops in
  let hb = gen_hb os in
  let sq = gen_seq os hb in
  let mem = gen_mem (fst sq) (snd sq) mids in gen_prog mem os

(** val autodisq_best : op_list -> membrane_id list -> config option **)

let autodisq_best ops mids =
  best_prog (autodisq_all ops mids)

(** val auto_disq_loop : config option -> config list -> config option **)

let rec auto_disq_loop best = function
| [] -> best
| p :: xs ->
  (match best with
   | Some b ->
     if Nat.ltb (fit p) (fit b)
     then auto_disq_loop (Some p) xs
     else auto_disq_loop best xs
   | None -> auto_disq_loop (Some p) xs)

(** val autodisq_best_1 : op_list -> membrane_id list -> config option **)

let autodisq_best_1 ops mids =
  auto_disq_loop None (autodisq_all ops mids)
