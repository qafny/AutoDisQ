
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

let rec app l0 m =
  match l0 with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val add : int -> int -> int **)

let rec add = (+)

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

type reflect =
| ReflectT
| ReflectF

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

  (** val of_succ_nat : int -> int **)

  let rec of_succ_nat n0 =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> 1)
      (fun x -> succ (of_succ_nat x))
      n0
 end

module N =
 struct
  (** val add : int -> int -> int **)

  let add = (+)

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
        (fun q -> Pos.eqb p q)
        m)
      n0

  (** val ltb : int -> int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val of_nat : int -> int **)

  let of_nat n0 =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> 0)
      (fun n' -> (Pos.of_succ_nat n'))
      n0
 end

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| [] -> []
| x :: l1 -> app x (concat l1)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t0 -> (f a) :: (map f t0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l0 a0 =
  match l0 with
  | [] -> a0
  | b :: t0 -> fold_left f t0 (f a0 b)

(** val split : ('a1 * 'a2) list -> 'a1 list * 'a2 list **)

let rec split = function
| [] -> ([], [])
| p :: tl ->
  let (x, y) = p in
  let (left, right) = split tl in ((x :: left), (y :: right))

(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> [])
    (fun len0 -> start :: (seq (Stdlib.succ start) len0))
    len

type var = int

type posi = var * int

(** val posi_eq : posi -> posi -> bool **)

let posi_eq r1 r2 =
  let (x1, y1) = r1 in
  let (x2, y2) = r2 in (&&) (Nat.eqb x1 x2) (Nat.eqb y1 y2)

(** val posi_eq_reflect : posi -> posi -> reflect **)

let posi_eq_reflect r1 r2 =
  let b = posi_eq r1 r2 in if b then ReflectT else ReflectF

(** val posi_eq_dec : posi -> posi -> bool **)

let posi_eq_dec x y =
  let h = posi_eq_reflect x y in
  (match h with
   | ReflectT -> true
   | ReflectF -> false)

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

  let rec merge_list_to_stack stack l0 =
    match stack with
    | [] -> (Some l0) :: []
    | y :: stack' ->
      (match y with
       | Some l' -> None :: (merge_list_to_stack stack' (merge l' l0))
       | None -> (Some l0) :: stack')

  (** val merge_stack : X.t list option list -> X.t list **)

  let rec merge_stack = function
  | [] -> []
  | y :: stack' ->
    (match y with
     | Some l0 -> merge l0 (merge_stack stack')
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
     | Some l0 -> app l0 (flatten_stack stack')
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

(** val list_eqb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eqb beq xs ys =
  match xs with
  | [] -> (match ys with
           | [] -> true
           | _ :: _ -> false)
  | x :: xs' ->
    (match ys with
     | [] -> false
     | y :: ys' -> (&&) (beq x y) (list_eqb beq xs' ys'))

(** val aexp_eqb : aexp -> aexp -> bool **)

let rec aexp_eqb e1 e2 =
  match e1 with
  | BA x1 -> (match e2 with
              | BA x2 -> Nat.eqb x1 x2
              | _ -> false)
  | Num n1 -> (match e2 with
               | Num n2 -> Nat.eqb n1 n2
               | _ -> false)
  | APlus (a1, b1) ->
    (match e2 with
     | APlus (a2, b2) -> (&&) (aexp_eqb a1 a2) (aexp_eqb b1 b2)
     | _ -> false)
  | AMult (a1, b1) ->
    (match e2 with
     | AMult (a2, b2) -> (&&) (aexp_eqb a1 a2) (aexp_eqb b1 b2)
     | _ -> false)
  | AModMult (_, _, _) -> false

(** val cbexp_eqb : cbexp -> cbexp -> bool **)

let cbexp_eqb b1 b2 =
  match b1 with
  | CEq (x1, y1) ->
    (match b2 with
     | CEq (x2, y2) -> (&&) (aexp_eqb x1 x2) (aexp_eqb y1 y2)
     | CLt (_, _) -> false)
  | CLt (x1, y1) ->
    (match b2 with
     | CEq (_, _) -> false
     | CLt (x2, y2) -> (&&) (aexp_eqb x1 x2) (aexp_eqb y1 y2))

(** val range_eqb : range -> range -> bool **)

let range_eqb r1 r2 =
  let (x1, p) = r1 in
  let (lo1, hi1) = p in
  let (x2, p0) = r2 in
  let (lo2, hi2) = p0 in
  (&&) (Nat.eqb x1 x2) ((&&) (Nat.eqb lo1 lo2) (Nat.eqb hi1 hi2))

(** val locus_eqb : locus -> locus -> bool **)

let locus_eqb l1 l2 =
  list_eqb range_eqb l1 l2

(** val exp_eqb : exp -> exp -> bool **)

let rec exp_eqb e1 e2 =
  match e1 with
  | SKIP (x1, a1) ->
    (match e2 with
     | SKIP (x2, a2) -> (&&) (Nat.eqb x1 x2) (aexp_eqb a1 a2)
     | _ -> false)
  | X (x1, a1) ->
    (match e2 with
     | X (x2, a2) -> (&&) (Nat.eqb x1 x2) (aexp_eqb a1 a2)
     | _ -> false)
  | CU (x1, a1, e1') ->
    (match e2 with
     | CU (x2, a2, e2') ->
       (&&) (Nat.eqb x1 x2) ((&&) (aexp_eqb a1 a2) (exp_eqb e1' e2'))
     | _ -> false)
  | RZ (q1, x1, a1) ->
    (match e2 with
     | RZ (q2, x2, a2) ->
       (&&) (Nat.eqb q1 q2) ((&&) (Nat.eqb x1 x2) (aexp_eqb a1 a2))
     | _ -> false)
  | RRZ (q1, x1, a1) ->
    (match e2 with
     | RRZ (q2, x2, a2) ->
       (&&) (Nat.eqb q1 q2) ((&&) (Nat.eqb x1 x2) (aexp_eqb a1 a2))
     | _ -> false)
  | SR (q1, x1) ->
    (match e2 with
     | SR (q2, x2) -> (&&) (Nat.eqb q1 q2) (Nat.eqb x1 x2)
     | _ -> false)
  | SRR (q1, x1) ->
    (match e2 with
     | SRR (q2, x2) -> (&&) (Nat.eqb q1 q2) (Nat.eqb x1 x2)
     | _ -> false)
  | QFT (x1, b1) ->
    (match e2 with
     | QFT (x2, b2) -> (&&) (Nat.eqb x1 x2) (Nat.eqb b1 b2)
     | _ -> false)
  | RQFT (x1, b1) ->
    (match e2 with
     | RQFT (x2, b2) -> (&&) (Nat.eqb x1 x2) (Nat.eqb b1 b2)
     | _ -> false)
  | H (x1, a1) ->
    (match e2 with
     | H (x2, a2) -> (&&) (Nat.eqb x1 x2) (aexp_eqb a1 a2)
     | _ -> false)
  | Addto (x1, q1) ->
    (match e2 with
     | Addto (x2, q2) -> (&&) (Nat.eqb x1 x2) (Nat.eqb q1 q2)
     | _ -> false)
  | Seq (s1, t1) ->
    (match e2 with
     | Seq (s2, t2) -> (&&) (exp_eqb s1 s2) (exp_eqb t1 t2)
     | _ -> false)

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

(** val nat_range_sub : (int * int) -> (int * int) -> bool **)

let nat_range_sub x y =
  (&&) (Nat.leb (fst y) (fst x)) (Nat.ltb (snd x) (snd y))

(** val range_intersect : range -> range -> bool **)

let range_intersect x y =
  (&&) (Nat.eqb (fst x) (fst y)) (nat_range_inter (snd x) (snd y))

(** val same_name : range -> range -> bool **)

let same_name x y =
  Nat.eqb (fst x) (fst y)

(** val intersect' : range -> locus -> bool **)

let rec intersect' x = function
| [] -> false
| a :: yas ->
  if same_name x a
  then if nat_range_inter (snd x) (snd a) then true else intersect' x yas
  else false

(** val intersect : locus -> locus -> bool **)

let rec intersect x y =
  match x with
  | [] -> false
  | a :: xas -> if intersect' a y then true else intersect xas y

(** val get_locus : cexp -> range list **)

let get_locus = function
| CNew a -> a :: []
| CAppU (l0, _) -> l0
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

(** val gen_next :
    int -> (int * myOp) -> (int * myOp) -> (int -> int -> bool) -> int -> int
    -> bool **)

let gen_next n0 x y r a b =
  if (&&) ((&&) (N.eqb a (fst x)) (N.ltb (fst y) b)) (N.ltb b n0)
  then r (fst y) b
  else r a b

(** val opListOrder' : op_list -> int -> (int * myOp) list **)

let rec opListOrder' l0 n0 =
  match l0 with
  | [] -> []
  | x :: xs -> (n0, x) :: (opListOrder' xs (N.add n0 1))

(** val opListOrder : op_list -> (int * myOp) list **)

let opListOrder l0 =
  opListOrder' l0 0

(** val empty_hp : int -> int -> bool **)

let empty_hp _ _ =
  false

(** val gen_hb' :
    int -> (int * myOp) -> (int * myOp) list -> int -> int -> bool **)

let rec gen_hb' n0 x = function
| [] -> (fun _ _ -> false)
| a :: xas -> gen_next n0 x a (gen_hb_single x a (gen_hb' n0 x xas))

(** val gen_hb_a :
    int -> (int * myOp) list -> (int -> int -> bool) -> int -> int -> bool **)

let rec gen_hb_a n0 r acc =
  match r with
  | [] -> acc
  | a :: xas -> gen_hb_a n0 xas (gen_hb' n0 a xas)

(** val gen_hb : (int * myOp) list -> int -> int -> bool **)

let gen_hb r =
  gen_hb_a (N.of_nat (length r)) r (fun _ _ -> false)

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

(** val sim_myop : myOp -> myOp -> bool **)

let sim_myop x y =
  match x with
  | OpAP a -> (match y with
               | OpAP b -> sim_cexp a b
               | OpIf (_, _, _) -> false)
  | OpIf (_, _, _) -> false

(** val insert_op :
    (int * myOp) -> (int * myOp) list list -> (int * myOp) list list **)

let insert_op a = function
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
           else ((i0, (OpAP q)) :: []) :: (((i, (OpAP b)) :: xl) :: al)
         | OpIf (c, d, e) ->
           ((i0, (OpIf (c, d, e))) :: []) :: (((i0, (OpAP b)) :: xl) :: al))
      | OpIf (c, d, e) -> (a :: []) :: (((i, (OpIf (c, d, e))) :: xl) :: al)))

(** val partition_op' :
    (int * myOp) list -> (int * myOp) list list -> (int * myOp) list list **)

let rec partition_op' l0 acc =
  match l0 with
  | [] -> acc
  | x :: xl -> partition_op' xl (insert_op x acc)

(** val partition_op : (int * myOp) list -> (int * myOp) list list **)

let partition_op l0 =
  rev (partition_op' l0 [])

(** val insert_all :
    (myOpAux * posi list) -> (myOpAux * posi list) list -> (myOpAux * posi
    list) list list **)

let rec insert_all x = function
| [] -> (x :: []) :: []
| y :: tl -> (x :: (y :: tl)) :: (map (fun zs -> y :: zs) (insert_all x tl))

(** val permutations :
    (myOpAux * posi list) list -> (myOpAux * posi list) list list **)

let rec permutations = function
| [] -> [] :: []
| x :: tl -> concat (map (insert_all x) (permutations tl))

(** val car_concat' :
    (myOpAux * posi list) list -> (myOpAux * posi list) list list ->
    (myOpAux * posi list) list list **)

let rec car_concat' x = function
| [] -> []
| a :: ys -> (app x a) :: (car_concat' x ys)

(** val car_concat :
    (myOpAux * posi list) list list -> (myOpAux * posi list) list list ->
    (myOpAux * posi list) list list **)

let rec car_concat x y =
  match x with
  | [] -> []
  | a :: xs -> app (car_concat' a y) (car_concat xs y)

(** val get_first :
    (int * myOp) list list -> ((int * myOp) list * (int * myOp) list list) ->
    (int * myOp) list * (int * myOp) list list **)

let rec get_first l0 acc =
  match l0 with
  | [] -> acc
  | l1 :: ys ->
    (match l1 with
     | [] -> get_first ys acc
     | a :: xs ->
       get_first ys
         (let (c, d) = acc in ((app c (a :: [])), (app d (xs :: [])))))

(** val grab_related' :
    (int * myOp) -> (int * myOp) list -> hb_relation -> (int * myOp) list ->
    (int * myOp) list **)

let rec grab_related' x l0 re acc =
  match l0 with
  | [] -> acc
  | a :: xs ->
    if re (fst x) (fst a)
    then grab_related' x xs re acc
    else grab_related' x xs re (app acc (a :: []))

(** val grab_related :
    (int * myOp) list -> hb_relation -> (int * myOp) list **)

let grab_related l0 re =
  match l0 with
  | [] -> []
  | x :: xs -> grab_related' x xs re (x :: [])

(** val grab_nums : (int * myOp) list -> int list **)

let grab_nums l0 =
  fst (split l0)

(** val in_list' : int -> int list -> bool **)

let rec in_list' x = function
| [] -> false
| a :: xs -> if N.eqb x a then true else in_list' x xs

(** val in_list : myOpAux -> int list -> bool **)

let in_list x l0 =
  match x with
  | OpNum v -> in_list' v l0
  | OpExp _ -> false

(** val up_qubits :
    var -> int -> int -> (var * int) list -> (var * int) list **)

let rec up_qubits x i n0 acc =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> acc)
    (fun m -> up_qubits x i m (app acc ((x, (add i m)) :: [])))
    n0

(** val cutToQubits' : range list -> (var * int) list **)

let rec cutToQubits' = function
| [] -> []
| r0 :: xs ->
  let (x, p) = r0 in
  let (l1, r) = p in app (up_qubits x l1 (sub r l1) []) (cutToQubits' xs)

(** val cutToQubits : range list -> (var * int) list **)

let cutToQubits l0 =
  cutToQubits' (SortRange.sort l0)

(** val get_locus_in_op : (int * myOp) list -> range list **)

let rec get_locus_in_op = function
| [] -> []
| p :: la ->
  let (_, m) = p in
  (match m with
   | OpAP y ->
     (match get_locus y with
      | [] -> get_locus_in_op la
      | r :: l1 -> app (r :: l1) (get_locus_in_op la))
   | OpIf (_, _, _) -> get_locus_in_op la)

(** val get_nlocus :
    (int * myOp) list -> (myOpAux * (var * int) list) list **)

let rec get_nlocus = function
| [] -> []
| x :: xs ->
  ((OpNum (fst x)),
    (cutToQubits (get_locus_in_op (x :: [])))) :: (get_nlocus xs)

(** val insert_back :
    (int * myOp) list -> (int * myOp) list list -> int list -> (int * myOp)
    list list **)

let rec insert_back x l0 re =
  match x with
  | [] -> []
  | a :: xs ->
    (match l0 with
     | [] -> []
     | la :: ls ->
       if in_list' (fst a) re
       then la :: (insert_back xs ls re)
       else (a :: la) :: (insert_back xs ls re))

(** val assign_each :
    int -> (int * myOp) list list -> hb_relation -> (myOpAux * posi list)
    list list -> (myOpAux * posi list) list list **)

let rec assign_each n0 l0 re acc =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> acc)
    (fun m ->
    let (a, b) = get_first l0 ([], []) in
    (match a with
     | [] ->
       (match b with
        | [] -> acc
        | _ :: _ ->
          let good =
            match a with
            | [] -> []
            | x :: xs -> grab_related' x xs re (x :: [])
          in
          assign_each m (insert_back a b (fst (split good))) re
            (car_concat acc (permutations (get_nlocus good))))
     | _ :: _ ->
       let good =
         match a with
         | [] -> []
         | x :: xs -> grab_related' x xs re (x :: [])
       in
       assign_each m (insert_back a b (fst (split good))) re
         (car_concat acc (permutations (get_nlocus good)))))
    n0

(** val gen_seq :
    (int * myOp) list -> hb_relation -> (myOpAux * (var * int) list)
    list * (myOpAux * posi list) list list **)

let gen_seq l0 re =
  let can = partition_op l0 in
  (match can with
   | [] -> ([], [])
   | x :: xs ->
     ((get_nlocus x),
       (assign_each (sub (length l0) (length x)) xs re ([] :: []))))

(** val count_a :
    int -> (myOpAux * posi list) list -> membrane_id -> ((myOpAux * posi
    list) * membrane_id) list -> ((myOpAux * posi list) * membrane_id)
    list * (myOpAux * posi list) list **)

let rec count_a t0 new0 a acc =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> (acc, new0))
    (fun m ->
    match new0 with
    | [] -> (acc, [])
    | x :: xs -> count_a m xs a (app acc ((x, a) :: [])))
    t0

(** val gen_mem_new' :
    int -> (myOpAux * posi list) list -> membrane_id list -> int ->
    ((myOpAux * posi list) * membrane_id) list -> ((myOpAux * posi
    list) * membrane_id) list **)

let rec gen_mem_new' size news l0 t0 acc =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> acc)
    (fun m ->
    match l0 with
    | [] -> acc
    | x :: xs ->
      let (re, next) = count_a t0 news x [] in
      gen_mem_new' m next xs t0 (app acc re))
    size

(** val gen_mem_new :
    (myOpAux * posi list) list -> membrane_id list -> ((myOpAux * posi
    list) * membrane_id) list **)

let gen_mem_new news l0 =
  let v = add (Nat.div (length news) (length l0)) (Stdlib.succ 0) in
  gen_mem_new' (length news) news l0 v []

(** val sub_locus' : locus -> locus -> bool **)

let rec sub_locus' x y =
  match x with
  | [] -> true
  | r :: xs ->
    let (na, p) = r in
    let (la, ra) = p in
    (match y with
     | [] -> false
     | r0 :: ys ->
       let (nb, p0) = r0 in
       let (lb, rb) = p0 in
       (&&) ((&&) ((&&) (Nat.eqb na nb) (Nat.leb la lb)) (Nat.leb rb ra))
         (sub_locus' xs ys))

(** val sub_locus : range list -> range list -> bool **)

let sub_locus x y =
  sub_locus' (SortRange.sort x) (SortRange.sort y)

(** val split_nat_range : (int * int) -> (int * int) -> (int * int) list **)

let split_nat_range x y =
  if Nat.eqb (fst x) (fst y)
  then ((snd x), (snd y)) :: []
  else if Nat.eqb (snd x) (snd y)
       then ((fst y), (fst x)) :: []
       else ((fst y), (fst x)) :: (((snd x), (snd y)) :: [])

(** val assemble_range :
    (int * int) list -> var -> (var * (int * int)) list **)

let rec assemble_range l0 x =
  match l0 with
  | [] -> []
  | a :: xs -> (x, a) :: (assemble_range xs x)

(** val sublist_posi : posi list -> posi list -> bool **)

let rec sublist_posi l0 r =
  match l0 with
  | [] -> true
  | x :: xs -> (&&) (set_mem posi_eq_dec x r) (sublist_posi xs r)

(** val insert_mem :
    ((posi * membrane_id) * int list) -> ((posi list * membrane_id) * int
    list) list -> ((posi list * membrane_id) * int list) list **)

let rec insert_mem a = function
| [] -> ((((fst (fst a)) :: []), (snd (fst a))), (snd a)) :: []
| p :: xs ->
  let (p0, ids) = p in
  let (x, y) = p0 in
  if Nat.eqb (snd (fst a)) y
  then ((((fst (fst a)) :: x), y), (app (snd a) ids)) :: xs
  else ((x, y), ids) :: (insert_mem a xs)

(** val set_inter0 : posi list -> posi list -> posi list **)

let rec set_inter0 x y =
  match x with
  | [] -> []
  | a :: xs ->
    if set_mem posi_eq_dec a y
    then a :: (set_inter0 xs y)
    else set_inter0 xs y

(** val sub_locus_i : posi -> locus -> bool **)

let rec sub_locus_i x = function
| [] -> false
| r :: xs ->
  let (y, b) = r in
  if (&&) ((&&) (Nat.eqb (fst x) y) (Nat.leb (fst b) (snd x)))
       (Nat.ltb (snd x) (snd b))
  then true
  else sub_locus_i x xs

(** val isSend : cexp -> bool **)

let isSend = function
| Send (_, _, _) -> true
| _ -> false

(** val no_send_check :
    membrane_id -> ((myOpAux * posi list) * membrane_id) list -> bool **)

let rec no_send_check i = function
| [] -> true
| a :: xs ->
  let (p, w) = a in
  let (m, _) = p in
  (match m with
   | OpNum _ -> no_send_check i xs
   | OpExp u ->
     if (&&) (Nat.eqb i w) (isSend u) then false else no_send_check i xs)

(** val search_hb :
    posi list -> int -> hb_relation -> ((myOpAux * posi list) * membrane_id)
    list -> ((myOpAux * posi list) * membrane_id) list -> (membrane_id * posi
    list) option **)

let rec search_hb x n0 hb l0 checker =
  match l0 with
  | [] -> None
  | a :: xs ->
    let (p, w) = a in
    let (m, v) = p in
    (match m with
     | OpNum u ->
       if (&&) (hb n0 u) (no_send_check w checker)
       then (match set_inter0 x v with
             | [] -> search_hb x n0 hb xs checker
             | p0 :: l1 -> Some (w, (p0 :: l1)))
       else search_hb x n0 hb xs checker
     | OpExp _ -> search_hb x n0 hb xs (a :: checker))

(** val search_mem :
    (membrane_id * (posi * bool) list) list -> posi list ->
    (membrane_id * posi list) list -> (membrane_id * posi list) list **)

let rec search_mem new0 x acc =
  match new0 with
  | [] -> acc
  | p :: ys ->
    let (i, y) = p in
    (match set_inter0 x (fst (split y)) with
     | [] -> search_mem ys x acc
     | p0 :: l0 -> search_mem ys x ((i, (p0 :: l0)) :: acc))

(** val max_one :
    (membrane_id * posi list) list -> (membrane_id * posi list) ->
    membrane_id list -> membrane_id list **)

let rec max_one new0 a acc =
  match new0 with
  | [] -> acc
  | x :: xs ->
    if Nat.ltb (length (snd a)) (length (snd x))
    then max_one xs x ((fst x) :: [])
    else if Nat.eqb (length (snd a)) (length (snd x))
         then max_one xs a ((fst x) :: acc)
         else max_one xs a acc

(** val search_good_mem :
    (membrane_id * (posi * bool) list) list -> posi list -> membrane_id list **)

let search_good_mem new0 x =
  match search_mem new0 x [] with
  | [] -> []
  | y :: ys -> max_one ys y ((fst y) :: [])

(** val find_least_q' :
    (membrane_id * (posi * bool) list) list -> (membrane_id * (posi * bool)
    list) -> membrane_id * (posi * bool) list **)

let rec find_least_q' new0 a =
  match new0 with
  | [] -> a
  | x :: xs ->
    if Nat.ltb (length (snd x)) (length (snd a))
    then find_least_q' xs x
    else find_least_q' xs a

(** val find_least_q :
    (membrane_id * (posi * bool) list) list -> (membrane_id * (posi * bool)
    list) option **)

let find_least_q = function
| [] -> None
| x :: xs -> Some (find_least_q' xs x)

(** val subtract_aux :
    posi -> (posi * bool) list -> (posi * bool) list -> (posi * bool) list **)

let rec subtract_aux x l0 acc =
  match l0 with
  | [] -> acc
  | y :: ys ->
    if posi_eq x (fst y)
    then subtract_aux x ys acc
    else subtract_aux x ys (y :: acc)

(** val subtract_posi :
    posi list -> (posi * bool) list -> (posi * bool) list -> (posi * bool)
    list **)

let rec subtract_posi x l0 acc =
  match x with
  | [] -> acc
  | y :: ys -> subtract_posi ys l0 (subtract_aux y l0 acc)

(** val subtract_all :
    posi list -> (membrane_id * (posi * bool) list) list ->
    (membrane_id * (posi * bool) list) list -> (membrane_id * (posi * bool)
    list) list **)

let rec subtract_all x new0 acc =
  match new0 with
  | [] -> acc
  | p :: ys ->
    let (i, y) = p in subtract_all x ys ((i, (subtract_posi x y [])) :: acc)

(** val add_posi_true' :
    membrane_id -> (posi * bool) list -> (membrane_id * (posi * bool) list)
    list -> (membrane_id * (posi * bool) list) list **)

let rec add_posi_true' i x = function
| [] -> []
| p :: ys ->
  let (j, y) = p in
  if Nat.eqb i j
  then (j, (app x y)) :: ys
  else (j, y) :: (add_posi_true' i x ys)

(** val add_true : posi list -> (posi * bool) list **)

let rec add_true = function
| [] -> []
| y :: ys -> (y, true) :: (add_true ys)

(** val add_posi_true :
    membrane_id -> posi list -> (membrane_id * (posi * bool) list) list ->
    (membrane_id * (posi * bool) list) list **)

let add_posi_true i x new0 =
  add_posi_true' i (add_true x) new0

(** val turn_true_aux :
    posi list -> (posi * bool) list -> (posi * bool) list **)

let turn_true_aux x y =
  let v = subtract_posi x y [] in app (add_true x) v

(** val turn_true :
    int -> posi list -> (membrane_id * (posi * bool) list) list ->
    (membrane_id * (posi * bool) list) list **)

let rec turn_true i x = function
| [] -> []
| p :: ys ->
  let (j, y) = p in
  if Nat.eqb i j
  then (j, (turn_true_aux x y)) :: ys
  else (j, y) :: (turn_true i x ys)

(** val find_all_in :
    posi list -> (membrane_id * (posi * bool) list) list ->
    (membrane_id * (posi * bool) list) option **)

let rec find_all_in l0 = function
| [] -> None
| p :: xs ->
  let (i, la) = p in
  if sublist_posi l0 (fst (split la)) then Some (i, la) else find_all_in l0 xs

(** val search_all_mem :
    membrane_id -> posi list -> (membrane_id * (posi * bool) list) list ->
    (membrane_id * posi list) list **)

let rec search_all_mem i x = function
| [] -> []
| p :: xs ->
  let (a, b) = p in
  if Nat.eqb i a
  then search_all_mem i x xs
  else (match set_inter0 x (fst (split b)) with
        | [] -> search_all_mem i x xs
        | p0 :: l0 -> (a, (p0 :: l0)) :: (search_all_mem i x xs))

(** val gen_comm' :
    membrane_id -> posi list -> var -> ((myOpAux * posi list) * membrane_id)
    list **)

let rec gen_comm' i l0 chan =
  match l0 with
  | [] -> []
  | x :: xs ->
    (((OpExp (Send (chan, (fst x), (snd x)))), (x :: [])), i) :: ((((OpExp
      (Recv (chan, (fst x), (snd x)))), (x :: [])),
      i) :: (gen_comm' i xs (Stdlib.succ chan)))

(** val gen_comm :
    (membrane_id * posi list) list -> var -> ((myOpAux * posi
    list) * membrane_id) list -> var * ((myOpAux * posi list) * membrane_id)
    list **)

let rec gen_comm l0 chan acc =
  match l0 with
  | [] -> (chan, acc)
  | y :: xs ->
    let (i, x) = y in
    gen_comm xs (add chan (length x)) (app (gen_comm' i x chan) acc)

(** val assign_mem_s :
    (membrane_id * (posi * bool) list) list -> hb_relation -> (int * posi
    list) -> ((myOpAux * posi list) * membrane_id) list -> var ->
    var * (((myOpAux * posi list) * membrane_id)
    list * (membrane_id * (posi * bool) list) list) list **)

let assign_mem_s new0 hb x l0 chan =
  let xset = snd x in
  (match find_all_in xset new0 with
   | Some p ->
     let (i, _) = p in
     (chan, (((app l0 ((((OpNum (fst x)), (snd x)), i) :: [])),
     (turn_true i xset new0)) :: []))
   | None ->
     (match search_hb xset (fst x) hb (rev l0) [] with
      | Some p ->
        let (i, re) = p in
        if Nat.ltb (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
             (Stdlib.succ 0)))))
             (Nat.div
               (mul (length re) (Stdlib.succ (Stdlib.succ (Stdlib.succ
                 (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                 (Stdlib.succ (Stdlib.succ (Stdlib.succ 0)))))))))))
               (length xset))
        then let mid = gen_comm (search_all_mem i (snd x) new0) chan [] in
             ((fst mid),
             (((app l0
                 (app (snd mid) ((((OpNum (fst x)), (snd x)), i) :: []))),
             (add_posi_true i xset (subtract_all xset new0 []))) :: []))
        else (match search_good_mem new0 xset with
              | [] -> (chan, [])
              | m :: l1 ->
                (match find_least_q new0 with
                 | Some na ->
                   fold_left (fun a b ->
                     let mid =
                       gen_comm (search_all_mem b (snd x) new0) (fst a) []
                     in
                     ((fst mid),
                     (((app l0
                         (app (snd mid) ((((OpNum (fst x)), (snd x)),
                           b) :: []))),
                     (add_posi_true b xset (subtract_all xset new0 []))) :: 
                     (snd a)))) ((fst na) :: (m :: l1)) (chan, [])
                 | None -> (chan, [])))
      | None ->
        (match search_good_mem new0 xset with
         | [] -> (chan, [])
         | m :: l1 ->
           fold_left (fun a b ->
             let mid = gen_comm (search_all_mem b (snd x) new0) (fst a) [] in
             ((fst mid),
             (((app l0
                 (app (snd mid) ((((OpNum (fst x)), (snd x)), b) :: []))),
             (add_posi_true b xset (subtract_all xset new0 []))) :: (snd a))))
             (m :: l1) (chan, []))))

(** val channel : int **)

let channel =
  Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val assign_mem' :
    hb_relation -> (myOpAux * posi list) list -> (var * (((myOpAux * posi
    list) * membrane_id) list * (membrane_id * (posi * bool) list) list)
    list) -> var * (((myOpAux * posi list) * membrane_id)
    list * (membrane_id * (posi * bool) list) list) list **)

let rec assign_mem' hb l0 acc =
  match l0 with
  | [] -> acc
  | a :: xs ->
    let (m, y) = a in
    (match m with
     | OpNum x ->
       assign_mem' hb xs
         (fold_left (fun a0 b ->
           let mid = assign_mem_s (snd b) hb (x, y) (fst b) (fst a0) in
           ((fst mid), (app (snd a0) (snd mid)))) (snd acc) ((fst acc), []))
     | OpExp _ -> assign_mem' hb xs acc)

(** val assign_mem_more :
    (membrane_id * (posi * bool) list) list -> hb_relation -> (myOpAux * posi
    list) list list -> ((myOpAux * posi list) * membrane_id) list list ->
    ((myOpAux * posi list) * membrane_id) list list **)

let rec assign_mem_more new0 hb l0 acc =
  match l0 with
  | [] -> acc
  | x :: xs ->
    assign_mem_more new0 hb xs
      (app
        (fst (split (snd (assign_mem' hb x (channel, (([], new0) :: []))))))
        acc)

(** val turn_new :
    ((myOpAux * posi list) * membrane_id) list ->
    (membrane_id * (posi * bool) list) list -> (membrane_id * (posi * bool)
    list) list **)

let rec turn_new l0 acc =
  match l0 with
  | [] -> acc
  | p :: xs -> let (x, y) = p in turn_new xs ((y, (add_true (snd x))) :: acc)

(** val gen_mem :
    (myOpAux * posi list) list -> (myOpAux * posi list) list list ->
    membrane_id list -> hb_relation -> ((myOpAux * posi list) * membrane_id)
    list list **)

let gen_mem news l0 ids hb =
  map (fun a -> app (gen_mem_new news ids) a)
    (assign_mem_more (turn_new (gen_mem_new news ids) []) hb l0 [])

(** val insert_mem_id :
    membrane_id -> (myOpAux * posi list) -> (int * (myOpAux * posi list)
    list) list -> (membrane_id * (myOpAux * posi list) list) list **)

let rec insert_mem_id i x = function
| [] -> (i, (x :: [])) :: []
| y :: xs ->
  let (a, b) = y in
  if Nat.eqb i a
  then (a, (app b (x :: []))) :: xs
  else (a, b) :: (insert_mem_id i x xs)

(** val distribute_op :
    ((myOpAux * posi list) * membrane_id) list -> (int * (myOpAux * posi
    list) list) list -> (int * (myOpAux * posi list) list) list **)

let rec distribute_op l0 acc =
  match l0 with
  | [] -> acc
  | x :: xs -> distribute_op xs (insert_mem_id (snd x) (fst x) acc)

(** val get_op : (int * myOp) list -> int -> myOp option **)

let rec get_op l0 i =
  match l0 with
  | [] -> None
  | p :: xs -> let (x, y) = p in if N.eqb i x then Some y else get_op xs i

(** val turn_cexp_to_proc : cexp list -> process -> process **)

let rec turn_cexp_to_proc l0 p =
  match l0 with
  | [] -> p
  | x :: xs -> AP (x, (turn_cexp_to_proc xs p))

(** val turn_op_to_proc : myOp -> process -> process **)

let turn_op_to_proc x p =
  match x with
  | OpAP a -> AP (a, p)
  | OpIf (b, l0, r) ->
    PIf (b, (turn_cexp_to_proc l0 p), (turn_cexp_to_proc r p))

(** val to_process :
    (myOpAux * posi list) list -> (int * myOp) list -> process option **)

let rec to_process l0 os =
  match l0 with
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
    (int * (myOpAux * posi list) list) list -> (int * myOp) list -> memb list **)

let rec to_prog l0 os =
  match l0 with
  | [] -> []
  | x :: xs ->
    (match to_process (snd x) os with
     | Some a -> (Memb ((fst x), a)) :: (to_prog xs os)
     | None -> [])

(** val gen_prog :
    ((myOpAux * posi list) * membrane_id) list list -> (int * myOp) list ->
    memb list list **)

let rec gen_prog l0 os =
  match l0 with
  | [] -> []
  | x :: xs -> (to_prog (distribute_op x []) os) :: (gen_prog xs os)

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
  let mem = gen_mem (fst sq) (snd sq) mids hb in gen_prog mem os

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

(** val one_qubit_range : var -> range **)

let one_qubit_range q =
  (q, (0, (Stdlib.succ 0)))

(** val l : locus **)

let l =
  []

(** val alloc_qubits_from : var list -> op_list **)

let rec alloc_qubits_from = function
| [] -> []
| q :: tl -> (OpAP (CNew (one_qubit_range q))) :: (alloc_qubits_from tl)

(** val cnot_from : var -> var list -> op_list **)

let rec cnot_from ctrl = function
| [] -> []
| q :: tl ->
  (OpAP (CAppU (l, (CU (ctrl, (Num 0), (X (q, (Num
    0)))))))) :: (cnot_from ctrl tl)

(** val meas_all_from : var list -> op_list **)

let rec meas_all_from = function
| [] -> []
| c :: tl -> (OpAP (CMeas (c, l))) :: (meas_all_from tl)

(** val ghz8_n : int **)

let ghz8_n =
  Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ 0)))))))

(** val ghz8_qs : var list **)

let ghz8_qs =
  seq 0 ghz8_n

(** val ghz8_outs : var list **)

let ghz8_outs =
  seq (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    ghz8_n

(** val gHZ8_prog : op_list **)

let gHZ8_prog =
  app (alloc_qubits_from ghz8_qs)
    (app ((OpAP (CAppU (l, (H (0, (Num 0)))))) :: [])
      (app (cnot_from 0 (seq (Stdlib.succ 0) (sub ghz8_n (Stdlib.succ 0))))
        (meas_all_from ghz8_outs)))

(** val ghz16_n : int **)

let ghz16_n =
  Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ 0)))))))))))))))

(** val ghz16_qs : var list **)

let ghz16_qs =
  seq 0 ghz16_n

(** val ghz16_outs : var list **)

let ghz16_outs =
  seq (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    ghz16_n

(** val gHZ16_prog : op_list **)

let gHZ16_prog =
  app (alloc_qubits_from ghz16_qs)
    (app ((OpAP (CAppU (l, (H (0, (Num 0)))))) :: [])
      (app (cnot_from 0 (seq (Stdlib.succ 0) (sub ghz16_n (Stdlib.succ 0))))
        (meas_all_from ghz16_outs)))

(** val apply_H_all_from : var list -> op_list **)

let rec apply_H_all_from = function
| [] -> []
| q :: tl -> (OpAP (CAppU (l, (H (q, (Num 0)))))) :: (apply_H_all_from tl)

(** val controlled_x_chain_from : var list -> var list -> op_list **)

let rec controlled_x_chain_from ctrls tgts =
  match ctrls with
  | [] -> []
  | c :: ctrls' ->
    (match tgts with
     | [] -> []
     | t0 :: tgts' ->
       (OpAP (CAppU (l, (CU (c, (Num 0), (X (t0, (Num
         0)))))))) :: (controlled_x_chain_from ctrls' tgts'))

(** val shor8_qs : var list **)

let shor8_qs =
  seq 0 (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))))))

(** val shor8_ctrls : var list **)

let shor8_ctrls =
  seq 0 (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))

(** val shor8_tgts : var list **)

let shor8_tgts =
  seq (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ 0)))) (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))

(** val shor8_outs : var list **)

let shor8_outs =
  seq (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))))))

(** val sHOR8_prog : op_list **)

let sHOR8_prog =
  app (alloc_qubits_from shor8_qs)
    (app (apply_H_all_from shor8_ctrls)
      (app (controlled_x_chain_from shor8_ctrls shor8_tgts)
        (app ((OpAP (CAppU (l, (QFT (0, (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ 0))))))))) :: [])
          (meas_all_from shor8_outs))))

(** val shor16_qs : var list **)

let shor16_qs =
  seq 0 (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ 0))))))))))))))))

(** val shor16_ctrls : var list **)

let shor16_ctrls =
  seq 0 (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))))))

(** val shor16_tgts : var list **)

let shor16_tgts =
  seq (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ 0)))))))) (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ 0))))))))

(** val shor16_outs : var list **)

let shor16_outs =
  seq (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ 0))))))))))))))))

(** val sHOR16_prog : op_list **)

let sHOR16_prog =
  app (alloc_qubits_from shor16_qs)
    (app (apply_H_all_from shor16_ctrls)
      (app (controlled_x_chain_from shor16_ctrls shor16_tgts)
        (app ((OpAP (CAppU (l, (QFT (0, (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ 0))))))))))))) :: []) (meas_all_from shor16_outs))))

(** val qft8_n : int **)

let qft8_n =
  Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ 0)))))))

(** val qft8_q0 : var **)

let qft8_q0 =
  0

(** val qft8_qubits : var list **)

let qft8_qubits =
  seq qft8_q0 qft8_n

(** val qft8_outs : var list **)

let qft8_outs =
  seq (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    qft8_n

(** val qFT8_prog : op_list **)

let qFT8_prog =
  app (alloc_qubits_from qft8_qubits)
    (app ((OpAP (CAppU (l, (QFT (qft8_q0, qft8_n))))) :: ((OpAP (CAppU (l,
      (RQFT (qft8_q0, qft8_n))))) :: [])) (meas_all_from qft8_outs))

(** val qft16_n : int **)

let qft16_n =
  Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ 0)))))))))))))))

(** val qft16_q0 : var **)

let qft16_q0 =
  0

(** val qft16_qubits : var list **)

let qft16_qubits =
  seq qft16_q0 qft16_n

(** val qft16_outs : var list **)

let qft16_outs =
  seq (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    qft16_n

(** val qFT16_prog : op_list **)

let qFT16_prog =
  app (alloc_qubits_from qft16_qubits)
    (app ((OpAP (CAppU (l, (QFT (qft16_q0, qft16_n))))) :: ((OpAP (CAppU (l,
      (RQFT (qft16_q0, qft16_n))))) :: [])) (meas_all_from qft16_outs))

(** val qadd8_n : int **)

let qadd8_n =
  Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ 0)))))))

(** val qadd8_q0 : var **)

let qadd8_q0 =
  0

(** val qadd8_qubits : var list **)

let qadd8_qubits =
  seq qadd8_q0 qadd8_n

(** val qadd8_outs : var list **)

let qadd8_outs =
  seq (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    qadd8_n

(** val qadd8_x : var **)

let qadd8_x =
  Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val qFTAdder8_prog : op_list **)

let qFTAdder8_prog =
  app (alloc_qubits_from qadd8_qubits)
    (app ((OpAP (CAppU (l, (QFT (qadd8_q0, (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ 0))))))))) :: ((OpAP (CAppU (l, (Addto
      (qadd8_x, qadd8_q0))))) :: ((OpAP (CAppU (l, (RQFT (qadd8_q0,
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))))))))) :: [])))
      (meas_all_from qadd8_outs))

(** val qadd16_n : int **)

let qadd16_n =
  Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ 0)))))))))))))))

(** val qadd16_q0 : var **)

let qadd16_q0 =
  0

(** val qadd16_qubits : var list **)

let qadd16_qubits =
  seq qadd16_q0 qadd16_n

(** val qadd16_outs : var list **)

let qadd16_outs =
  seq (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    qadd16_n

(** val qadd16_x : var **)

let qadd16_x =
  Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val qFTAdder16_prog : op_list **)

let qFTAdder16_prog =
  app (alloc_qubits_from qadd16_qubits)
    (app ((OpAP (CAppU (l, (QFT (qadd16_q0, (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ 0))))))))))))) :: ((OpAP (CAppU (l, (Addto (qadd16_x,
      qadd16_q0))))) :: ((OpAP (CAppU (l, (RQFT (qadd16_q0, (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ 0))))))))))))) :: [])))
      (meas_all_from qadd16_outs))

(** val qft32_n : int **)

let qft32_n =
  Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ 0)))))))))))))))))))))))))))))))

(** val qft32_q0 : var **)

let qft32_q0 =
  0

(** val qft32_qubits : var list **)

let qft32_qubits =
  seq qft32_q0 qft32_n

(** val qft32_outs : var list **)

let qft32_outs =
  seq (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    qft32_n

(** val qFT32_prog : op_list **)

let qFT32_prog =
  app (alloc_qubits_from qft32_qubits)
    (app ((OpAP (CAppU (l, (QFT (qft32_q0, qft32_n))))) :: ((OpAP (CAppU (l,
      (RQFT (qft32_q0, qft32_n))))) :: [])) (meas_all_from qft32_outs))

(** val qadd32_n : int **)

let qadd32_n =
  Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ 0)))))))))))))))))))))))))))))))

(** val qadd32_q0 : var **)

let qadd32_q0 =
  0

(** val qadd32_qubits : var list **)

let qadd32_qubits =
  seq qadd32_q0 qadd32_n

(** val qadd32_outs : var list **)

let qadd32_outs =
  seq (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    qadd32_n

(** val qadd32_x : var **)

let qadd32_x =
  Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val qFTAdder32_prog : op_list **)

let qFTAdder32_prog =
  app (alloc_qubits_from qadd32_qubits)
    (app ((OpAP (CAppU (l, (QFT (qadd32_q0, (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      0))))))))))))))))))))) :: ((OpAP (CAppU (l, (Addto (qadd32_x,
      qadd32_q0))))) :: ((OpAP (CAppU (l, (RQFT (qadd32_q0, (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
      0))))))))))))))))))))) :: []))) (meas_all_from qadd32_outs))

(** val ghz32_n : int **)

let ghz32_n =
  Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ 0)))))))))))))))))))))))))))))))

(** val ghz32_qs : var list **)

let ghz32_qs =
  seq 0 ghz32_n

(** val ghz32_outs : var list **)

let ghz32_outs =
  seq (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    ghz32_n

(** val gHZ32_prog : op_list **)

let gHZ32_prog =
  app (alloc_qubits_from ghz32_qs)
    (app ((OpAP (CAppU (l, (H (0, (Num 0)))))) :: [])
      (app (cnot_from 0 (seq (Stdlib.succ 0) (sub ghz32_n (Stdlib.succ 0))))
        (meas_all_from ghz32_outs)))
