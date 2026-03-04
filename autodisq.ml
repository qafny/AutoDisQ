
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val add : int -> int -> int **)

let rec add = (+)

(** val mul : int -> int -> int **)

let rec mul = ( * )

module Nat =
 struct
  (** val add : int -> int -> int **)

  let rec add n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun p -> Stdlib.Int.succ (add p m))
      n

  (** val mul : int -> int -> int **)

  let rec mul n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> 0)
      (fun p -> add m (mul p m))
      n

  (** val sub : int -> int -> int **)

  let rec sub n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n)
      (fun k ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n)
        (fun l -> sub k l)
        m)
      n

  (** val ltb : int -> int -> bool **)

  let ltb n m =
    (<=) (Stdlib.Int.succ n) m

  (** val max : int -> int -> int **)

  let rec max n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> m)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n)
        (fun m' -> Stdlib.Int.succ (max n' m'))
        m)
      n

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Stdlib.Int.succ 0)
      (fun m0 -> mul n (pow n m0))
      m

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q u =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (q, u))
      (fun x' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> divmod x' y (Stdlib.Int.succ q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val div : int -> int -> int **)

  let div x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> y)
      (fun y' -> fst (divmod x y' 0 y'))
      y

  (** val modulo : int -> int -> int **)

  let modulo x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> x)
      (fun y' -> sub y' (snd (divmod x y' 0 y')))
      y
 end

(** val nth_error : 'a1 list -> int -> 'a1 option **)

let rec nth_error l n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l with
              | [] -> None
              | x :: _ -> Some x)
    (fun n0 -> match l with
               | [] -> None
               | _ :: l0 -> nth_error l0 n0)
    n

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| [] -> []
| x :: l0 -> app x (concat l0)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l0 -> (&&) (f a) (forallb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

(** val firstn : int -> 'a1 list -> 'a1 list **)

let rec firstn n l =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n0 -> match l with
               | [] -> []
               | a :: l0 -> a :: (firstn n0 l0))
    n

type var = int

type bound =
| BVar of var * int
| BNum of int

type range = (var * bound) * bound

type locus = range list

type aexp =
| BA of var
| Num of int
| APlus of aexp * aexp
| AMult of aexp * aexp

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
| CNew of var * int
| CAppU of locus * exp
| CMeas of var * locus

type cdexp =
| NewCh of var * int
| Send of var * aexp
| Recv of var * var

type process =
| PNil
| AP of cexp * process
| DP of cdexp * process
| PIf of cbexp * process * process

type memb =
| Memb of var * process list
| LockMemb of var * process * process list

type config = memb list

type membrane_id = var

type hb_relation = exp -> exp -> bool

type op_list = exp list

type rank = int

type seq_relation = exp -> rank

type op_mem_assign = exp -> membrane_id

type qubit_mem_assign = var -> membrane_id

type fitness_value = int

type distributed_prog = config

(** val var_eqb : var -> var -> bool **)

let var_eqb =
  (=)

(** val mem_var : var -> var list -> bool **)

let rec mem_var x = function
| [] -> false
| y :: tl -> if var_eqb x y then true else mem_var x tl

(** val uniq : var list -> var list **)

let rec uniq = function
| [] -> []
| x :: tl -> if mem_var x tl then uniq tl else x :: (uniq tl)

(** val intersect : var list -> var list -> var list **)

let rec intersect xs ys =
  match xs with
  | [] -> []
  | x :: tl ->
    if mem_var x ys then x :: (intersect tl ys) else intersect tl ys

(** val vars_of_exp : exp -> var list **)

let rec vars_of_exp = function
| SKIP (_, _) -> []
| X (x, _) -> x :: []
| CU (x, _, e1) -> x :: (vars_of_exp e1)
| RZ (_, x, _) -> x :: []
| RRZ (_, x, _) -> x :: []
| SR (_, x) -> x :: []
| SRR (_, x) -> x :: []
| QFT (x, _) -> x :: []
| RQFT (x, _) -> x :: []
| H (x, _) -> x :: []
| Addto (x, q) -> x :: (q :: [])
| Seq (e1, e2) -> app (vars_of_exp e1) (vars_of_exp e2)

(** val share_qubit : exp -> exp -> bool **)

let share_qubit e1 e2 =
  negb
    ((=) (length (intersect (uniq (vars_of_exp e1)) (uniq (vars_of_exp e2))))
      0)

(** val internal_nat_beq : int -> int -> bool **)

let rec internal_nat_beq x y =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun _ -> false)
      y)
    (fun x0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun x1 -> internal_nat_beq x0 x1)
      y)
    x

(** val internal_nat_beq0 : int -> int -> bool **)

let rec internal_nat_beq0 x y =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun _ -> false)
      y)
    (fun x0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun x1 -> internal_nat_beq0 x0 x1)
      y)
    x

(** val internal_aexp_beq : aexp -> aexp -> bool **)

let rec internal_aexp_beq x y =
  match x with
  | BA x0 -> (match y with
              | BA x1 -> internal_nat_beq0 x0 x1
              | _ -> false)
  | Num n -> (match y with
              | Num n0 -> internal_nat_beq0 n n0
              | _ -> false)
  | APlus (e1, e2) ->
    (match y with
     | APlus (e3, e4) ->
       (&&) (internal_aexp_beq e1 e3) (internal_aexp_beq e2 e4)
     | _ -> false)
  | AMult (e1, e2) ->
    (match y with
     | AMult (e3, e4) ->
       (&&) (internal_aexp_beq e1 e3) (internal_aexp_beq e2 e4)
     | _ -> false)

(** val exp_beq : exp -> exp -> bool **)

let rec exp_beq x y =
  match x with
  | SKIP (x0, a) ->
    (match y with
     | SKIP (x1, a0) -> (&&) (internal_nat_beq x0 x1) (internal_aexp_beq a a0)
     | _ -> false)
  | X (x0, a) ->
    (match y with
     | X (x1, a0) -> (&&) (internal_nat_beq x0 x1) (internal_aexp_beq a a0)
     | _ -> false)
  | CU (x0, a, e) ->
    (match y with
     | CU (x1, a0, e0) ->
       (&&) (internal_nat_beq x0 x1)
         ((&&) (internal_aexp_beq a a0) (exp_beq e e0))
     | _ -> false)
  | RZ (q, x0, a) ->
    (match y with
     | RZ (q0, x1, a0) ->
       (&&) (internal_nat_beq q q0)
         ((&&) (internal_nat_beq x0 x1) (internal_aexp_beq a a0))
     | _ -> false)
  | RRZ (q, x0, a) ->
    (match y with
     | RRZ (q0, x1, a0) ->
       (&&) (internal_nat_beq q q0)
         ((&&) (internal_nat_beq x0 x1) (internal_aexp_beq a a0))
     | _ -> false)
  | SR (q, x0) ->
    (match y with
     | SR (q0, x1) -> (&&) (internal_nat_beq q q0) (internal_nat_beq x0 x1)
     | _ -> false)
  | SRR (q, x0) ->
    (match y with
     | SRR (q0, x1) -> (&&) (internal_nat_beq q q0) (internal_nat_beq x0 x1)
     | _ -> false)
  | QFT (x0, b) ->
    (match y with
     | QFT (x1, b0) -> (&&) (internal_nat_beq x0 x1) (internal_nat_beq b b0)
     | _ -> false)
  | RQFT (x0, b) ->
    (match y with
     | RQFT (x1, b0) -> (&&) (internal_nat_beq x0 x1) (internal_nat_beq b b0)
     | _ -> false)
  | H (x0, a) ->
    (match y with
     | H (x1, a0) -> (&&) (internal_nat_beq x0 x1) (internal_aexp_beq a a0)
     | _ -> false)
  | Addto (x0, q) ->
    (match y with
     | Addto (x1, q0) -> (&&) (internal_nat_beq x0 x1) (internal_nat_beq q q0)
     | _ -> false)
  | Seq (s1, s2) ->
    (match y with
     | Seq (s3, s4) -> (&&) (exp_beq s1 s3) (exp_beq s2 s4)
     | _ -> false)

(** val exp_eqb : exp -> exp -> bool **)

let exp_eqb =
  exp_beq

(** val gen_os : op_list -> op_list **)

let gen_os r =
  r

(** val index_of_exp : exp -> exp list -> int **)

let rec index_of_exp x = function
| [] -> 0
| y :: tl -> if exp_eqb x y then 0 else Stdlib.Int.succ (index_of_exp x tl)

(** val gen_hp : op_list -> hb_relation **)

let gen_hp r e1 e2 =
  let i = index_of_exp e1 r in
  let j = index_of_exp e2 r in (&&) (Nat.ltb i j) (share_qubit e1 e2)

(** val nth_default : 'a1 -> 'a1 list -> int -> 'a1 **)

let rec nth_default d xs n =
  match xs with
  | [] -> d
  | x :: tl ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> x)
       (fun n' -> nth_default d tl n')
       n)

(** val insert_all : exp -> exp list -> exp list list **)

let rec insert_all x = function
| [] -> (x :: []) :: []
| y :: tl -> (x :: (y :: tl)) :: (map (fun zs -> y :: zs) (insert_all x tl))

(** val permutations : exp list -> exp list list **)

let rec permutations = function
| [] -> [] :: []
| x :: tl -> concat (map (insert_all x) (permutations tl))

(** val respects_hp : hb_relation -> exp list -> bool **)

let rec respects_hp hp = function
| [] -> true
| x :: tl ->
  let ok_x = forallb (fun y -> negb (hp y x)) tl in
  (&&) ok_x (respects_hp hp tl)

(** val topo_orders_k : hb_relation -> exp list -> int -> exp list list **)

let topo_orders_k hp nodes k =
  let perms = permutations nodes in
  let good = filter (respects_hp hp) perms in firstn k good

(** val seq_from_order : exp list -> seq_relation **)

let seq_from_order order e =
  index_of_exp e order

(** val default_mid : membrane_id **)

let default_mid =
  0

(** val first_mid : config -> membrane_id **)

let first_mid = function
| [] -> default_mid
| m :: _ -> (match m with
             | Memb (l, _) -> l
             | LockMemb (l, _, _) -> l)

(** val mem_count : config -> int **)

let mem_count =
  length

(** val nth_mid_default : config -> int -> membrane_id **)

let nth_mid_default cfg i =
  match nth_error cfg i with
  | Some m -> (match m with
               | Memb (l, _) -> l
               | LockMemb (l, _, _) -> l)
  | None -> first_mid cfg

(** val exp_tag : exp -> int **)

let rec exp_tag = function
| SKIP (_, _) -> Stdlib.Int.succ 0
| X (_, _) -> Stdlib.Int.succ (Stdlib.Int.succ 0)
| CU (_, _, e1) ->
  add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) (exp_tag e1)
| RZ (q, _, _) ->
  add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) q
| RRZ (q, _, _) ->
  add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))) q
| SR (q, _) ->
  add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))))))))) q
| SRR (q, _) ->
  add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))))))))))) q
| QFT (_, b) ->
  add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))) b
| RQFT (_, b) ->
  add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) b
| H (_, _) ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| Addto (_, _) ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
| Seq (e1, e2) ->
  add
    (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      (exp_tag e1)) (exp_tag e2)

(** val sum_vars : var list -> int **)

let rec sum_vars = function
| [] -> 0
| x :: tl -> add x (sum_vars tl)

(** val exp_hash : exp -> int **)

let exp_hash e =
  add (exp_tag e) (sum_vars (vars_of_exp e))

(** val subset_vars : var list -> var list -> bool **)

let subset_vars xs ys =
  forallb (fun x -> mem_var x ys) xs

(** val overlap_big : var list -> var list -> bool **)

let overlap_big xs ys =
  let xs' = uniq xs in
  let ys' = uniq ys in
  let inter = length (intersect xs' ys') in
  let denom = Nat.max (Stdlib.Int.succ 0) (Nat.max (length xs') (length ys'))
  in
  (<=)
    (let y = Stdlib.Int.succ (Stdlib.Int.succ 0) in
     (fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> y)
       (fun y' -> fst (Nat.divmod denom y' 0 y'))
       y) inter

(** val insert_by_seq : seq_relation -> exp -> exp list -> exp list **)

let rec insert_by_seq seq op = function
| [] -> op :: []
| x :: tl ->
  if (<=) (seq op) (seq x)
  then op :: (x :: tl)
  else x :: (insert_by_seq seq op tl)

(** val sort_by_seq : seq_relation -> exp list -> exp list **)

let rec sort_by_seq seq = function
| [] -> []
| x :: tl -> insert_by_seq seq x (sort_by_seq seq tl)

(** val order_by_seq : seq_relation -> op_list -> op_list **)

let order_by_seq =
  sort_by_seq

(** val build_moO :
    config -> int -> exp list -> (exp * membrane_id) option ->
    (int * membrane_id) list -> (int * membrane_id) list **)

let rec build_moO cfg seed ops_sorted prev tbl =
  match ops_sorted with
  | [] -> tbl
  | op :: tl ->
    let mid =
      match prev with
      | Some p ->
        let (op_prev, mid_prev) = p in
        let vars = uniq (vars_of_exp op) in
        let vars_prev = uniq (vars_of_exp op_prev) in
        if (||) (subset_vars vars vars_prev) (overlap_big vars vars_prev)
        then mid_prev
        else let m = mem_count cfg in
             let idx =
               (fun fO fS n -> if n=0 then fO () else fS (n-1))
                 (fun _ -> 0)
                 (fun m' ->
                 Nat.modulo (add (exp_hash op) seed) (Stdlib.Int.succ m'))
                 m
             in
             nth_mid_default cfg idx
      | None ->
        let m = mem_count cfg in
        let idx =
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> 0)
            (fun m' ->
            Nat.modulo (add (exp_hash op) seed) (Stdlib.Int.succ m'))
            m
        in
        nth_mid_default cfg idx
    in
    build_moO cfg seed tl (Some (op, mid)) (((exp_hash op), mid) :: tbl)

(** val lookup_mid : int -> (int * membrane_id) list -> membrane_id **)

let rec lookup_mid h = function
| [] -> default_mid
| p :: tl -> let (k, v) = p in if (=) k h then v else lookup_mid h tl

(** val moO_of_tbl : (int * membrane_id) list -> op_mem_assign **)

let moO_of_tbl tbl op =
  lookup_mid (exp_hash op) tbl

(** val first_use_mid : exp list -> op_mem_assign -> var -> membrane_id **)

let rec first_use_mid ops_sorted moO q =
  match ops_sorted with
  | [] -> default_mid
  | op :: tl ->
    if mem_var q (vars_of_exp op) then moO op else first_use_mid tl moO q

(** val gen_mem_seed :
    int -> config -> seq_relation -> op_list ->
    op_mem_assign * qubit_mem_assign **)

let gen_mem_seed seed cfg seq os =
  let ops_sorted = order_by_seq seq os in
  let moO_tbl = build_moO cfg seed ops_sorted None [] in
  let moO = moO_of_tbl moO_tbl in
  let moQ = fun q -> first_use_mid ops_sorted moO q in (moO, moQ)

(** val mk_reloc : membrane_id -> membrane_id -> exp **)

let mk_reloc src dst =
  SKIP (src, (Num dst))

(** val op_to_process : exp -> process **)

let op_to_process op =
  AP ((CAppU ([], op)), PNil)

(** val place_operation : config -> membrane_id -> exp -> config **)

let rec place_operation cfg mid op =
  match cfg with
  | [] -> (Memb (mid, ((op_to_process op) :: []))) :: []
  | m :: tl ->
    (match m with
     | Memb (l, ps) ->
       if var_eqb l mid
       then (Memb (l, (app ps ((op_to_process op) :: [])))) :: tl
       else (Memb (l, ps)) :: (place_operation tl mid op)
     | LockMemb (l, r, ps) ->
       if var_eqb l mid
       then (LockMemb (l, r, (app ps ((op_to_process op) :: [])))) :: tl
       else (LockMemb (l, r, ps)) :: (place_operation tl mid op))

type qloc_tbl = (var * membrane_id) list

(** val qloc_lookup : var -> qloc_tbl -> membrane_id -> membrane_id **)

let rec qloc_lookup q tbl d =
  match tbl with
  | [] -> d
  | p :: tl -> let (k, v) = p in if var_eqb k q then v else qloc_lookup q tl d

(** val qloc_update : var -> membrane_id -> qloc_tbl -> qloc_tbl **)

let rec qloc_update q mid = function
| [] -> (q, mid) :: []
| p :: tl ->
  let (k, v) = p in
  if var_eqb k q then (k, mid) :: tl else (k, v) :: (qloc_update q mid tl)

(** val init_qloc : var list -> qubit_mem_assign -> qloc_tbl **)

let rec init_qloc qs moQ =
  match qs with
  | [] -> []
  | q :: tl -> (q, (moQ q)) :: (init_qloc tl moQ)

(** val all_qubits : exp list -> var list **)

let rec all_qubits = function
| [] -> []
| op :: tl -> app (vars_of_exp op) (all_qubits tl)

(** val ensure_qubits :
    var list -> membrane_id -> qloc_tbl -> config -> qloc_tbl * config **)

let rec ensure_qubits qs target qloc acc =
  match qs with
  | [] -> (qloc, acc)
  | q :: tl ->
    let cur = qloc_lookup q qloc default_mid in
    if var_eqb cur target
    then ensure_qubits tl target qloc acc
    else let acc' = place_operation acc target (mk_reloc cur target) in
         let qloc' = qloc_update q target qloc in
         ensure_qubits tl target qloc' acc'

(** val gen_prog_core :
    op_mem_assign -> qubit_mem_assign -> exp list -> qloc_tbl -> config ->
    config **)

let rec gen_prog_core moO moQ ops_sorted qloc acc =
  match ops_sorted with
  | [] -> acc
  | op :: tl ->
    let target = moO op in
    let qs = uniq (vars_of_exp op) in
    let (qloc1, acc1) = ensure_qubits qs target qloc acc in
    let acc2 = place_operation acc1 target op in
    gen_prog_core moO moQ tl qloc1 acc2

(** val gen_prog :
    seq_relation -> op_mem_assign -> qubit_mem_assign -> op_list ->
    distributed_prog **)

let gen_prog seq moO moQ os =
  let ops_sorted = order_by_seq seq os in
  let qs = uniq (all_qubits ops_sorted) in
  let qloc0 = init_qloc qs moQ in gen_prog_core moO moQ ops_sorted qloc0 []

(** val is_reloc : exp -> bool **)

let is_reloc = function
| SKIP (_, a) -> (match a with
                  | Num _ -> true
                  | _ -> false)
| _ -> false

(** val reloc_pair : exp -> membrane_id * membrane_id **)

let reloc_pair = function
| SKIP (a, a0) -> (match a0 with
                   | Num b -> (a, b)
                   | _ -> (0, 0))
| _ -> (0, 0)

(** val mem_pair :
    (membrane_id * membrane_id) -> (membrane_id * membrane_id) list -> bool **)

let rec mem_pair p = function
| [] -> false
| q :: tl ->
  if (&&) (var_eqb (fst p) (fst q)) (var_eqb (snd p) (snd q))
  then true
  else mem_pair p tl

(** val uniq_pairs :
    (membrane_id * membrane_id) list -> (membrane_id * membrane_id) list **)

let rec uniq_pairs = function
| [] -> []
| p :: tl -> if mem_pair p tl then uniq_pairs tl else p :: (uniq_pairs tl)

(** val extract_exps_from_proc : process -> exp list **)

let rec extract_exps_from_proc = function
| PNil -> []
| AP (c, tl) ->
  (match c with
   | CAppU (_, e) -> e :: (extract_exps_from_proc tl)
   | _ -> extract_exps_from_proc tl)
| DP (_, tl) -> extract_exps_from_proc tl
| PIf (_, p1, p2) ->
  app (extract_exps_from_proc p1) (extract_exps_from_proc p2)

(** val extract_all_exps : config -> exp list **)

let rec extract_all_exps = function
| [] -> []
| m :: tl ->
  (match m with
   | Memb (_, ps) ->
     app (concat (map extract_exps_from_proc ps)) (extract_all_exps tl)
   | LockMemb (_, _, ps) ->
     app (concat (map extract_exps_from_proc ps)) (extract_all_exps tl))

(** val count_relocs : exp list -> int **)

let rec count_relocs = function
| [] -> 0
| e :: tl ->
  add (if is_reloc e then Stdlib.Int.succ 0 else 0) (count_relocs tl)

(** val collect_pairs : exp list -> (membrane_id * membrane_id) list **)

let rec collect_pairs = function
| [] -> []
| e :: tl ->
  if is_reloc e
  then (reloc_pair e) :: (collect_pairs tl)
  else collect_pairs tl

(** val fit : distributed_prog -> fitness_value **)

let fit p =
  let es = extract_all_exps p in
  let reloc = count_relocs es in
  let pairs = length (uniq_pairs (collect_pairs es)) in
  add reloc
    (mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))) pairs)

(** val iNF_SCORE : fitness_value **)

let iNF_SCORE =
  Nat.pow (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))

type case = int * int

(** val case_eqb : case -> case -> bool **)

let case_eqb c d =
  (&&) ((=) (fst c) (fst d)) ((=) (snd c) (snd d))

(** val mem_case : case -> case list -> bool **)

let rec mem_case c = function
| [] -> false
| d :: tl -> if case_eqb c d then true else mem_case c tl

(** val range_from : int -> int -> int list **)

let rec range_from start count =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun k -> start :: (range_from (Stdlib.Int.succ start) k))
    count

(** val mk_cases : int -> int -> case list **)

let mk_cases kseq kmem =
  let scheds = range_from 0 kseq in
  let seeds = range_from 0 kmem in
  concat (map (fun si -> map (fun sd -> (si, sd)) seeds) scheds)

(** val filter_fresh : case list -> case list -> case list **)

let rec filter_fresh all seen =
  match all with
  | [] -> []
  | c :: tl ->
    if mem_case c seen
    then filter_fresh tl seen
    else c :: (filter_fresh tl seen)

(** val are_still_cases : case list -> case list -> bool **)

let are_still_cases s aLL =
  negb ((=) (length (filter_fresh aLL s)) 0)

(** val pick_case : case list -> case list -> case option **)

let pick_case s aLL =
  match filter_fresh aLL s with
  | [] -> None
  | c :: _ -> Some c

(** val gen_mem_paper :
    config -> seq_relation -> op_list -> case ->
    op_mem_assign * qubit_mem_assign **)

let gen_mem_paper cfg seq os c =
  let seed = snd c in gen_mem_seed seed cfg seq os

(** val auto_disq_loop_paper :
    int -> hb_relation -> op_list -> config -> case list -> case list ->
    distributed_prog -> fitness_value -> int -> distributed_prog **)

let rec auto_disq_loop_paper kseq hp os cfg aLL s qbest zmin fuel =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> qbest)
    (fun fuel' ->
    if are_still_cases s aLL
    then (match match pick_case s aLL with
                | Some c ->
                  let sched_i = fst c in
                  let seq =
                    let schedules = topo_orders_k hp os kseq in
                    let n = length schedules in
                    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
                       (fun _ _ -> 0)
                       (fun _ ->
                       let idx = Nat.modulo sched_i n in
                       let order = nth_default [] schedules idx in
                       seq_from_order order)
                       n)
                  in
                  Some (c, seq)
                | None -> None with
          | Some p ->
            let (c, seq) = p in
            let (moO, moQ) = gen_mem_paper cfg seq os c in
            let p0 = gen_prog seq moO moQ os in
            let z = fit p0 in
            let s' = c :: s in
            if Nat.ltb z zmin
            then auto_disq_loop_paper kseq hp os cfg aLL s' p0 z fuel'
            else auto_disq_loop_paper kseq hp os cfg aLL s' qbest zmin fuel'
          | None -> qbest)
    else qbest)
    fuel

(** val auto_disq_alg1_paper :
    int -> int -> op_list -> config -> distributed_prog **)

let auto_disq_alg1_paper kseq kmem r cfg =
  let hp = gen_hp r in
  let os = gen_os r in
  let aLL = mk_cases kseq kmem in
  auto_disq_loop_paper kseq hp os cfg aLL [] [] iNF_SCORE (length aLL)
