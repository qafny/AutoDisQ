
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

let rec app l0 m =
  match l0 with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type uint0 =
| Nil0
| D10 of uint0
| D11 of uint0
| D12 of uint0
| D13 of uint0
| D14 of uint0
| D15 of uint0
| D16 of uint0
| D17 of uint0
| D18 of uint0
| D19 of uint0
| Da of uint0
| Db of uint0
| Dc of uint0
| Dd of uint0
| De of uint0
| Df of uint0

type uint1 =
| UIntDecimal of uint
| UIntHexadecimal of uint0

(** val add : int -> int -> int **)

let rec add = (+)

(** val mul : int -> int -> int **)

let rec mul = ( * )

(** val sub : int -> int -> int **)

let rec sub = fun n m -> Stdlib.max 0 (n-m)

(** val tail_add : int -> int -> int **)

let rec tail_add n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> m)
    (fun n0 -> tail_add n0 (Stdlib.Int.succ m))
    n

(** val tail_addmul : int -> int -> int -> int **)

let rec tail_addmul r n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> r)
    (fun n0 -> tail_addmul (tail_add m r) n0 m)
    n

(** val tail_mul : int -> int -> int **)

let tail_mul n m =
  tail_addmul 0 n m

(** val of_uint_acc : uint -> int -> int **)

let rec of_uint_acc d acc =
  match d with
  | Nil -> acc
  | D0 d0 ->
    of_uint_acc d0
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)
  | D1 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))
  | D2 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)))
  | D3 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))))
  | D4 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)))))
  | D5 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))))))
  | D6 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)))))))
  | D7 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))))))))
  | D8 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc)))))))))
  | D9 d0 ->
    of_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))) acc))))))))))

(** val of_uint : uint -> int **)

let of_uint d =
  of_uint_acc d 0

(** val of_hex_uint_acc : uint0 -> int -> int **)

let rec of_hex_uint_acc d acc =
  match d with
  | Nil0 -> acc
  | D10 d0 ->
    of_hex_uint_acc d0
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)
  | D11 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))
  | D12 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))
  | D13 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))
  | D14 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))))
  | D15 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))))
  | D16 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))))))
  | D17 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))))))
  | D18 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))))))))
  | D19 d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))))))))
  | Da d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))))))))))
  | Db d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))))))))))
  | Dc d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))))))))))))
  | Dd d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))))))))))))
  | De d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc)))))))))))))))
  | Df d0 ->
    of_hex_uint_acc d0 (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (tail_mul (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0)))))))))))))))) acc))))))))))))))))

(** val of_hex_uint : uint0 -> int **)

let of_hex_uint d =
  of_hex_uint_acc d 0

(** val of_num_uint : uint1 -> int **)

let of_num_uint = function
| UIntDecimal d0 -> of_uint d0
| UIntHexadecimal d0 -> of_hex_uint d0

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

(** val modulo : int -> int -> int **)

let modulo x y =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> x)
    (fun y' -> sub y' (snd (divmod x y' 0 y')))
    y

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
        (fun l0 -> sub k l0)
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

  (** val even : int -> bool **)

  let rec even n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n0 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun n' -> even n')
        n0)
      n

  (** val pow : int -> int -> int **)

  let rec pow n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Stdlib.Int.succ 0)
      (fun m3 -> mul n (pow n m3))
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

  (** val gcd : int -> int -> int **)

  let rec gcd a b =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> b)
      (fun a' -> gcd (modulo b (Stdlib.Int.succ a')) (Stdlib.Int.succ a'))
      a
 end

(** val nth_error : 'a1 list -> int -> 'a1 option **)

let rec nth_error l0 n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l0 with
              | [] -> None
              | x :: _ -> Some x)
    (fun n0 -> match l0 with
               | [] -> None
               | _ :: l1 -> nth_error l1 n0)
    n

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
| a :: t -> (f a) :: (map f t)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t -> f b (fold_right f a0 t)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| [] -> false
| a :: l1 -> (||) (f a) (existsb f l1)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l1 -> (&&) (f a) (forallb f l1)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l1 -> if f x then x :: (filter f l1) else filter f l1

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

type myOp =
| OpAP of cexp
| OpDP of cdexp
| OpIf of cbexp * process * process

type op_list = myOp list

type hb_relation = myOp -> myOp -> bool

type rank = int

type seq_relation = myOp -> rank

type op_mem_assign = myOp -> membrane_id

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
              | BA x2 -> (=) x1 x2
              | _ -> false)
  | Num n1 -> (match e2 with
               | Num n2 -> (=) n1 n2
               | _ -> false)
  | APlus (a1, b1) ->
    (match e2 with
     | APlus (a2, b2) -> (&&) (aexp_eqb a1 a2) (aexp_eqb b1 b2)
     | _ -> false)
  | AMult (a1, b1) ->
    (match e2 with
     | AMult (a2, b2) -> (&&) (aexp_eqb a1 a2) (aexp_eqb b1 b2)
     | _ -> false)

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

(** val bound_eqb : bound -> bound -> bool **)

let bound_eqb b1 b2 =
  match b1 with
  | BVar (v1, n1) ->
    (match b2 with
     | BVar (v2, n2) -> (&&) ((=) v1 v2) ((=) n1 n2)
     | BNum _ -> false)
  | BNum n1 -> (match b2 with
                | BVar (_, _) -> false
                | BNum n2 -> (=) n1 n2)

(** val range_eqb : range -> range -> bool **)

let range_eqb r1 r2 =
  let (p, hi1) = r1 in
  let (x1, lo1) = p in
  let (p3, hi2) = r2 in
  let (x2, lo2) = p3 in
  (&&) ((=) x1 x2) ((&&) (bound_eqb lo1 lo2) (bound_eqb hi1 hi2))

(** val locus_eqb : locus -> locus -> bool **)

let locus_eqb l1 l2 =
  list_eqb range_eqb l1 l2

(** val exp_eqb : exp -> exp -> bool **)

let rec exp_eqb e1 e2 =
  match e1 with
  | SKIP (x1, a1) ->
    (match e2 with
     | SKIP (x2, a2) -> (&&) ((=) x1 x2) (aexp_eqb a1 a2)
     | _ -> false)
  | X (x1, a1) ->
    (match e2 with
     | X (x2, a2) -> (&&) ((=) x1 x2) (aexp_eqb a1 a2)
     | _ -> false)
  | CU (x1, a1, e1') ->
    (match e2 with
     | CU (x2, a2, e2') ->
       (&&) ((=) x1 x2) ((&&) (aexp_eqb a1 a2) (exp_eqb e1' e2'))
     | _ -> false)
  | RZ (q1, x1, a1) ->
    (match e2 with
     | RZ (q2, x2, a2) -> (&&) ((=) q1 q2) ((&&) ((=) x1 x2) (aexp_eqb a1 a2))
     | _ -> false)
  | RRZ (q1, x1, a1) ->
    (match e2 with
     | RRZ (q2, x2, a2) ->
       (&&) ((=) q1 q2) ((&&) ((=) x1 x2) (aexp_eqb a1 a2))
     | _ -> false)
  | SR (q1, x1) ->
    (match e2 with
     | SR (q2, x2) -> (&&) ((=) q1 q2) ((=) x1 x2)
     | _ -> false)
  | SRR (q1, x1) ->
    (match e2 with
     | SRR (q2, x2) -> (&&) ((=) q1 q2) ((=) x1 x2)
     | _ -> false)
  | QFT (x1, b1) ->
    (match e2 with
     | QFT (x2, b2) -> (&&) ((=) x1 x2) ((=) b1 b2)
     | _ -> false)
  | RQFT (x1, b1) ->
    (match e2 with
     | RQFT (x2, b2) -> (&&) ((=) x1 x2) ((=) b1 b2)
     | _ -> false)
  | H (x1, a1) ->
    (match e2 with
     | H (x2, a2) -> (&&) ((=) x1 x2) (aexp_eqb a1 a2)
     | _ -> false)
  | Addto (x1, q1) ->
    (match e2 with
     | Addto (x2, q2) -> (&&) ((=) x1 x2) ((=) q1 q2)
     | _ -> false)
  | Seq (s1, t1) ->
    (match e2 with
     | Seq (s2, t2) -> (&&) (exp_eqb s1 s2) (exp_eqb t1 t2)
     | _ -> false)

(** val cexp_eqb : cexp -> cexp -> bool **)

let cexp_eqb c1 c2 =
  match c1 with
  | CNew (x1, n1) ->
    (match c2 with
     | CNew (x2, n2) -> (&&) ((=) x1 x2) ((=) n1 n2)
     | _ -> false)
  | CAppU (l1, e1) ->
    (match c2 with
     | CAppU (l2, e2) -> (&&) (locus_eqb l1 l2) (exp_eqb e1 e2)
     | _ -> false)
  | CMeas (x1, k1) ->
    (match c2 with
     | CMeas (x2, k2) -> (&&) ((=) x1 x2) (locus_eqb k1 k2)
     | _ -> false)

(** val cdexp_eqb : cdexp -> cdexp -> bool **)

let cdexp_eqb d1 d2 =
  match d1 with
  | NewCh (c1, n1) ->
    (match d2 with
     | NewCh (c2, n2) -> (&&) ((=) c1 c2) ((=) n1 n2)
     | _ -> false)
  | Send (c1, a1) ->
    (match d2 with
     | Send (c2, a2) -> (&&) ((=) c1 c2) (aexp_eqb a1 a2)
     | _ -> false)
  | Recv (c1, x1) ->
    (match d2 with
     | Recv (c2, x2) -> (&&) ((=) c1 c2) ((=) x1 x2)
     | _ -> false)

(** val process_eqb : process -> process -> bool **)

let rec process_eqb p3 p4 =
  match p3 with
  | PNil -> (match p4 with
             | PNil -> true
             | _ -> false)
  | AP (a1, p1') ->
    (match p4 with
     | AP (a2, p2') -> (&&) (cexp_eqb a1 a2) (process_eqb p1' p2')
     | _ -> false)
  | DP (a1, p1') ->
    (match p4 with
     | DP (a2, p2') -> (&&) (cdexp_eqb a1 a2) (process_eqb p1' p2')
     | _ -> false)
  | PIf (b1, p1a, p1b) ->
    (match p4 with
     | PIf (b2, p2a, p2b) ->
       (&&) (cbexp_eqb b1 b2)
         ((&&) (process_eqb p1a p2a) (process_eqb p1b p2b))
     | _ -> false)

(** val myOp_eqb : myOp -> myOp -> bool **)

let myOp_eqb x y =
  match x with
  | OpAP a1 -> (match y with
                | OpAP a2 -> cexp_eqb a1 a2
                | _ -> false)
  | OpDP a1 -> (match y with
                | OpDP a2 -> cdexp_eqb a1 a2
                | _ -> false)
  | OpIf (b1, p3, q1) ->
    (match y with
     | OpIf (b2, p4, q2) ->
       (&&) (cbexp_eqb b1 b2) ((&&) (process_eqb p3 p4) (process_eqb q1 q2))
     | _ -> false)

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

(** val gen_os : op_list -> op_list **)

let gen_os r =
  r

(** val vars_of_aexp : aexp -> var list **)

let rec vars_of_aexp = function
| BA x -> x :: []
| Num _ -> []
| APlus (a1, a2) -> app (vars_of_aexp a1) (vars_of_aexp a2)
| AMult (a1, a2) -> app (vars_of_aexp a1) (vars_of_aexp a2)

(** val vars_of_cbexp : cbexp -> var list **)

let vars_of_cbexp = function
| CEq (a1, a2) -> app (vars_of_aexp a1) (vars_of_aexp a2)
| CLt (a1, a2) -> app (vars_of_aexp a1) (vars_of_aexp a2)

(** val vars_of_myOp : myOp -> var list **)

let vars_of_myOp = function
| OpAP a ->
  (match a with
   | CNew (x, _) -> x :: []
   | CAppU (_, e) -> vars_of_exp e
   | CMeas (x, _) -> x :: [])
| OpDP a ->
  (match a with
   | NewCh (c, _) -> c :: []
   | Send (c, e) -> c :: (vars_of_aexp e)
   | Recv (c, x) -> c :: (x :: []))
| OpIf (b, _, _) -> vars_of_cbexp b

(** val qubits_of_range : range -> var list **)

let qubits_of_range = function
| (p, _) -> let (q, _) = p in q :: []

(** val qubits_of_locus : locus -> var list **)

let qubits_of_locus l0 =
  concat (map qubits_of_range l0)

(** val qubits_of_cexp : cexp -> var list **)

let qubits_of_cexp = function
| CNew (q, _) -> q :: []
| CAppU (_, e) -> vars_of_exp e
| CMeas (_, k) -> qubits_of_locus k

(** val qubits_of_myOp : myOp -> var list **)

let qubits_of_myOp = function
| OpAP a -> qubits_of_cexp a
| _ -> []

(** val share_qubit_myOp : myOp -> myOp -> bool **)

let share_qubit_myOp o1 o2 =
  negb
    ((=)
      (length
        (intersect (uniq (qubits_of_myOp o1)) (uniq (qubits_of_myOp o2)))) 0)

(** val index_of_myOp : myOp -> myOp list -> int **)

let rec index_of_myOp x = function
| [] -> 0
| y :: tl -> if myOp_eqb x y then 0 else Stdlib.Int.succ (index_of_myOp x tl)

(** val gen_hp : op_list -> hb_relation **)

let gen_hp r o1 o2 =
  let i = index_of_myOp o1 r in
  let j = index_of_myOp o2 r in (&&) (Nat.ltb i j) (share_qubit_myOp o1 o2)

(** val remove_one :
    (myOp -> myOp -> bool) -> myOp -> myOp list -> myOp list **)

let rec remove_one eqb x = function
| [] -> []
| y :: tl -> if eqb x y then tl else y :: (remove_one eqb x tl)

(** val has_incoming_from_nodes : hb_relation -> myOp list -> myOp -> bool **)

let has_incoming_from_nodes hp nodes x =
  existsb (fun y -> hp y x) nodes

(** val available_nodes : hb_relation -> myOp list -> myOp list **)

let available_nodes hp nodes =
  filter (fun x -> negb (has_incoming_from_nodes hp nodes x)) nodes

(** val nth_default_myOp : myOp -> myOp list -> int -> myOp **)

let rec nth_default_myOp d xs n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match xs with
              | [] -> d
              | x :: _ -> x)
    (fun n' -> match xs with
               | [] -> d
               | _ :: tl -> nth_default_myOp d tl n')
    n

(** val topo_kahn_fuel :
    hb_relation -> int -> myOp list -> int -> myOp list -> myOp list option **)

let rec topo_kahn_fuel hp schedule_index nodes fuel acc =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun fuel' ->
    match nodes with
    | [] -> Some (rev acc)
    | _ :: _ ->
      let avs = available_nodes hp nodes in
      (match match avs with
             | [] -> None
             | _ :: _ ->
               let idx = Nat.modulo schedule_index (length avs) in
               Some
               (nth_default_myOp
                 (match avs with
                  | [] -> OpAP (CNew (0, 0))
                  | x :: _ -> x) avs idx) with
       | Some x ->
         topo_kahn_fuel hp (Stdlib.Int.succ schedule_index)
           (remove_one myOp_eqb x nodes) fuel' (x :: acc)
       | None -> None))
    fuel

(** val topo_kahn : hb_relation -> int -> myOp list -> myOp list option **)

let topo_kahn hp schedule_index nodes =
  topo_kahn_fuel hp schedule_index nodes (Stdlib.Int.succ (length nodes)) []

(** val seq_from_order : myOp list -> seq_relation **)

let seq_from_order order o =
  index_of_myOp o order

(** val gen_seq_many :
    int -> int -> hb_relation -> op_list -> seq_relation **)

let gen_seq_many _ schedule_index hp os =
  match topo_kahn hp schedule_index os with
  | Some order -> seq_from_order order
  | None -> (fun _ -> 0)

(** val default_mid : membrane_id **)

let default_mid =
  0

(** val first_mid : config -> membrane_id **)

let first_mid = function
| [] -> default_mid
| m :: _ -> (match m with
             | Memb (l0, _) -> l0
             | LockMemb (l0, _, _) -> l0)

(** val mem_count : config -> int **)

let mem_count =
  length

(** val sum_vars : var list -> int **)

let rec sum_vars = function
| [] -> 0
| x :: tl -> add x (sum_vars tl)

(** val myOp_tag : myOp -> int **)

let myOp_tag = function
| OpAP a ->
  (match a with
   | CNew (_, _) -> Stdlib.Int.succ 0
   | CAppU (_, _) -> Stdlib.Int.succ (Stdlib.Int.succ 0)
   | CMeas (_, _) -> Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
| OpDP a ->
  (match a with
   | NewCh (_, _) ->
     Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))
   | Send (_, _) ->
     Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))
   | Recv (_, _) ->
     Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
| OpIf (_, _, _) ->
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))

(** val myOp_hash : myOp -> int **)

let myOp_hash o =
  add (myOp_tag o) (sum_vars (vars_of_myOp o))

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

(** val insert_by_seq : seq_relation -> myOp -> myOp list -> myOp list **)

let rec insert_by_seq seq op = function
| [] -> op :: []
| x :: tl ->
  if (<=) (seq op) (seq x)
  then op :: (x :: tl)
  else x :: (insert_by_seq seq op tl)

(** val sort_by_seq : seq_relation -> myOp list -> myOp list **)

let rec sort_by_seq seq = function
| [] -> []
| x :: tl -> insert_by_seq seq x (sort_by_seq seq tl)

(** val order_by_seq : seq_relation -> op_list -> op_list **)

let order_by_seq =
  sort_by_seq

(** val build_moO :
    config -> int -> myOp list -> (myOp * membrane_id) option ->
    (int * membrane_id) list -> (int * membrane_id) list **)

let rec build_moO cfg seed ops_sorted prev tbl =
  match ops_sorted with
  | [] -> tbl
  | op :: tl ->
    let mid =
      match prev with
      | Some p ->
        let (op_prev, mid_prev) = p in
        let vars = uniq (vars_of_myOp op) in
        let vars_prev = uniq (vars_of_myOp op_prev) in
        if (||) (subset_vars vars vars_prev) (overlap_big vars vars_prev)
        then mid_prev
        else let m = mem_count cfg in
             let idx =
               (fun fO fS n -> if n=0 then fO () else fS (n-1))
                 (fun _ -> 0)
                 (fun m' ->
                 Nat.modulo (add (myOp_hash op) seed) (Stdlib.Int.succ m'))
                 m
             in
             (match cfg with
              | [] -> default_mid
              | _ :: _ ->
                (match nth_error cfg idx with
                 | Some m3 ->
                   (match m3 with
                    | Memb (l0, _) -> l0
                    | LockMemb (l0, _, _) -> l0)
                 | None -> first_mid cfg))
      | None ->
        let m = mem_count cfg in
        let idx =
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> 0)
            (fun m' ->
            Nat.modulo (add (myOp_hash op) seed) (Stdlib.Int.succ m'))
            m
        in
        (match cfg with
         | [] -> default_mid
         | _ :: _ ->
           (match nth_error cfg idx with
            | Some m3 ->
              (match m3 with
               | Memb (l0, _) -> l0
               | LockMemb (l0, _, _) -> l0)
            | None -> first_mid cfg))
    in
    build_moO cfg seed tl (Some (op, mid)) (((myOp_hash op), mid) :: tbl)

(** val lookup_mid : int -> (int * membrane_id) list -> membrane_id **)

let rec lookup_mid h = function
| [] -> default_mid
| p :: tl -> let (k, v) = p in if (=) k h then v else lookup_mid h tl

(** val moO_of_tbl : (int * membrane_id) list -> op_mem_assign **)

let moO_of_tbl tbl op =
  lookup_mid (myOp_hash op) tbl

(** val first_use_mid : myOp list -> op_mem_assign -> var -> membrane_id **)

let rec first_use_mid ops_sorted moO q =
  match ops_sorted with
  | [] -> default_mid
  | op :: tl ->
    if mem_var q (vars_of_myOp op) then moO op else first_use_mid tl moO q

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

(** val myOp_to_process : myOp -> process **)

let myOp_to_process = function
| OpAP a -> AP (a, PNil)
| OpDP a -> DP (a, PNil)
| OpIf (b, p, q) -> PIf (b, p, q)

(** val reloc_process : membrane_id -> membrane_id -> process **)

let reloc_process src dst =
  AP ((CAppU ([], (mk_reloc src dst))), PNil)

(** val place_operation : config -> membrane_id -> myOp -> config **)

let rec place_operation cfg mid op =
  match cfg with
  | [] -> (Memb (mid, ((myOp_to_process op) :: []))) :: []
  | m :: tl ->
    (match m with
     | Memb (l0, ps) ->
       if var_eqb l0 mid
       then (Memb (l0, (app ps ((myOp_to_process op) :: [])))) :: tl
       else (Memb (l0, ps)) :: (place_operation tl mid op)
     | LockMemb (l0, r, ps) ->
       if var_eqb l0 mid
       then (LockMemb (l0, r, (app ps ((myOp_to_process op) :: [])))) :: tl
       else (LockMemb (l0, r, ps)) :: (place_operation tl mid op))

(** val place_reloc :
    config -> membrane_id -> membrane_id -> membrane_id -> config **)

let rec place_reloc cfg mid src dst =
  match cfg with
  | [] -> (Memb (mid, ((reloc_process src dst) :: []))) :: []
  | m :: tl ->
    (match m with
     | Memb (l0, ps) ->
       if var_eqb l0 mid
       then (Memb (l0, (app ps ((reloc_process src dst) :: [])))) :: tl
       else (Memb (l0, ps)) :: (place_reloc tl mid src dst)
     | LockMemb (l0, r, ps) ->
       if var_eqb l0 mid
       then (LockMemb (l0, r, (app ps ((reloc_process src dst) :: [])))) :: tl
       else (LockMemb (l0, r, ps)) :: (place_reloc tl mid src dst))

(** val count_comm_proc : process -> int **)

let rec count_comm_proc = function
| PNil -> 0
| AP (_, p') -> count_comm_proc p'
| DP (d, p') ->
  (match d with
   | NewCh (_, _) -> count_comm_proc p'
   | _ -> Stdlib.Int.succ (count_comm_proc p'))
| PIf (_, p3, p4) -> add (count_comm_proc p3) (count_comm_proc p4)

(** val count_comm_cfg : config -> int **)

let rec count_comm_cfg = function
| [] -> 0
| m :: tl ->
  (match m with
   | Memb (_, ps) ->
     add (fold_right (fun p acc -> add (count_comm_proc p) acc) 0 ps)
       (count_comm_cfg tl)
   | LockMemb (_, _, ps) ->
     add (fold_right (fun p acc -> add (count_comm_proc p) acc) 0 ps)
       (count_comm_cfg tl))

(** val fit : distributed_prog -> fitness_value **)

let fit =
  count_comm_cfg

(** val iNF_SCORE : fitness_value **)

let iNF_SCORE =
  of_num_uint (UIntDecimal (D1 (D0 (D0 (D0 (D0 (D0 (D0 (D0 (D0 (D0
    Nil)))))))))))

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

type candidate = case * (seq_relation * (op_mem_assign * qubit_mem_assign))

(** val seen_cases : candidate list -> case list **)

let seen_cases s =
  map fst s

(** val are_still_cases_cases : case list -> case list -> bool **)

let are_still_cases_cases seen aLL =
  match filter_fresh aLL seen with
  | [] -> false
  | _ :: _ -> true

(** val pick_case : case list -> case list -> case option **)

let pick_case s aLL =
  match filter_fresh aLL s with
  | [] -> None
  | c :: _ -> Some c

(** val gen_mem :
    config -> seq_relation -> op_list -> case ->
    op_mem_assign * qubit_mem_assign **)

let gen_mem cfg seq os c =
  let seed = snd c in gen_mem_seed seed cfg seq os

type smap = (var * membrane_id) list

(** val locus_myOp : myOp -> var list **)

let locus_myOp =
  vars_of_myOp

(** val diff_mem : (var -> membrane_id) -> var list -> membrane_id -> smap **)

let diff_mem mo_cur qs l0 =
  fold_right (fun q acc ->
    let src = mo_cur q in if var_eqb src l0 then acc else (q, src) :: acc) []
    qs

(** val mem_up_smap :
    (var -> membrane_id) -> smap -> membrane_id -> var -> membrane_id **)

let rec mem_up_smap mo_cur s l0 =
  match s with
  | [] -> mo_cur
  | p :: tl ->
    let (q, _) = p in
    let mo_cur' = fun x -> if var_eqb x q then l0 else mo_cur x in
    mem_up_smap mo_cur' tl l0

(** val insert_send_recv :
    config -> smap -> membrane_id -> int -> config * int **)

let rec insert_send_recv p sp l0 name =
  match sp with
  | [] -> (p, name)
  | p3 :: tl ->
    let (q, src) = p3 in
    let alias = add name (Stdlib.Int.succ 0) in
    let p4 = place_operation p src (OpDP (NewCh (name, (Stdlib.Int.succ 0))))
    in
    let p5 = place_operation p4 src (OpDP (Send (name, (BA q)))) in
    let p6 = place_operation p5 l0 (OpDP (Recv (name, alias))) in
    insert_send_recv p6 tl l0 (add name (Stdlib.Int.succ (Stdlib.Int.succ 0)))

(** val gen_prog_loop_alg2 :
    myOp list -> (var -> membrane_id) -> (myOp -> membrane_id) -> config ->
    int -> config **)

let rec gen_prog_loop_alg2 seq mo_cur moO p name =
  match seq with
  | [] -> p
  | op :: seq' ->
    let l0 = moO op in
    let s = diff_mem mo_cur (locus_myOp op) l0 in
    let (p3, name1) =
      match s with
      | [] -> (p, name)
      | _ :: _ -> insert_send_recv p s l0 name
    in
    let mo_cur' = mem_up_smap mo_cur s l0 in
    let p4 = place_operation p3 l0 op in
    gen_prog_loop_alg2 seq' mo_cur' moO p4 name1

(** val empty_config : config **)

let empty_config =
  []

(** val gen_prog_alg2 :
    myOp list -> (var -> membrane_id) -> (myOp -> membrane_id) -> config **)

let gen_prog_alg2 seq moQ moO =
  gen_prog_loop_alg2 seq moQ moO empty_config 0

(** val gen_prog_paper :
    seq_relation -> qubit_mem_assign -> op_mem_assign -> op_list ->
    distributed_prog **)

let gen_prog_paper seq moQ moO os =
  let ops_sorted = order_by_seq seq os in gen_prog_alg2 ops_sorted moQ moO

(** val auto_disq_loop :
    int -> hb_relation -> op_list -> config -> case list -> candidate list ->
    distributed_prog -> fitness_value -> int -> distributed_prog **)

let rec auto_disq_loop kseq hp os cfg aLL s qbest zmin fuel =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> qbest)
    (fun fuel' ->
    if are_still_cases_cases (seen_cases s) aLL
    then (match match pick_case (seen_cases s) aLL with
                | Some c ->
                  let sched_i = fst c in
                  let seq =
                    match topo_kahn hp sched_i os with
                    | Some order -> seq_from_order order
                    | None -> (fun _ -> 0)
                  in
                  Some (c, seq)
                | None -> None with
          | Some p ->
            let (c, seq) = p in
            let (moO, moQ) = gen_mem cfg seq os c in
            let p3 = gen_prog_paper seq moQ moO os in
            let z = fit p3 in
            let s' = (c, (seq, (moO, moQ))) :: s in
            if Nat.ltb z zmin
            then auto_disq_loop kseq hp os cfg aLL s' p3 z fuel'
            else auto_disq_loop kseq hp os cfg aLL s' qbest zmin fuel'
          | None -> qbest)
    else qbest)
    fuel

(** val auto_disq_alg1_paper :
    int -> int -> op_list -> config -> distributed_prog **)

let auto_disq_alg1_paper kseq kmem r cfg =
  let hp = gen_hp r in
  let os = gen_os r in
  let aLL = mk_cases kseq kmem in
  auto_disq_loop kseq hp os cfg aLL [] [] iNF_SCORE (length aLL)

(** val succs : hb_relation -> myOp list -> myOp -> myOp list **)

let succs hp nodes x =
  filter (fun y -> hp x y) nodes

(** val mem_op : (myOp -> myOp -> bool) -> myOp -> myOp list -> bool **)

let rec mem_op eqb x = function
| [] -> false
| y :: tl -> if eqb x y then true else mem_op eqb x tl

(** val uniq_ops : (myOp -> myOp -> bool) -> myOp list -> myOp list **)

let rec uniq_ops eqb = function
| [] -> []
| x :: tl ->
  if mem_op eqb x tl then uniq_ops eqb tl else x :: (uniq_ops eqb tl)

(** val remove_ops :
    (myOp -> myOp -> bool) -> myOp list -> myOp list -> myOp list **)

let rec remove_ops eqb xs rem =
  match xs with
  | [] -> []
  | x :: tl ->
    if mem_op eqb x rem
    then remove_ops eqb tl rem
    else x :: (remove_ops eqb tl rem)

(** val opt_hp : hb_relation -> seq_relation -> hb_relation **)

let opt_hp hp_l seq_l a b =
  (&&) (hp_l a b) (Nat.ltb (seq_l a) (seq_l b))

(** val reachable_fuel :
    (myOp -> myOp -> bool) -> hb_relation -> myOp list -> int -> myOp list ->
    myOp -> myOp -> bool **)

let rec reachable_fuel eqb hp nodes fuel seen x target =
  if eqb x target
  then true
  else ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> false)
          (fun fuel' ->
          if mem_op eqb x seen
          then false
          else let seen' = x :: seen in
               existsb (fun y ->
                 reachable_fuel eqb hp nodes fuel' seen' y target)
                 (succs hp nodes x))
          fuel)

(** val reachable :
    (myOp -> myOp -> bool) -> hb_relation -> myOp list -> myOp -> myOp -> bool **)

let reachable eqb hp nodes x y =
  reachable_fuel eqb hp nodes (length nodes) [] x y

(** val scc_of :
    (myOp -> myOp -> bool) -> hb_relation -> myOp list -> myOp -> myOp list **)

let scc_of eqb hp nodes x =
  filter (fun y ->
    (&&) (reachable eqb hp nodes x y) (reachable eqb hp nodes y x)) nodes

(** val scc_partition_fuel :
    int -> (myOp -> myOp -> bool) -> hb_relation -> myOp list -> myOp list
    list **)

let rec scc_partition_fuel fuel eqb hp nodes =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun fuel' ->
    match nodes with
    | [] -> []
    | x :: _ ->
      let comp = scc_of eqb hp nodes x in
      let rest = remove_ops eqb nodes comp in
      comp :: (scc_partition_fuel fuel' eqb hp rest))
    fuel

(** val scc_partition :
    (myOp -> myOp -> bool) -> hb_relation -> myOp list -> myOp list list **)

let scc_partition eqb hp nodes =
  scc_partition_fuel (length nodes) eqb hp nodes

(** val gen_ops : seq_relation -> myOp list -> process list **)

let gen_ops seq_l sbar =
  map myOp_to_process (sort_by_seq seq_l sbar)

(** val alg3_loop :
    seq_relation -> myOp list list -> process list -> process list **)

let rec alg3_loop seq_l s rbar =
  match s with
  | [] -> rbar
  | sbar :: s' ->
    let r = gen_ops seq_l sbar in
    let rbar' = app rbar r in alg3_loop seq_l s' rbar'

(** val auto_parallelize_alg3 :
    (myOp -> myOp -> bool) -> myOp list -> hb_relation -> seq_relation ->
    process list **)

let auto_parallelize_alg3 eqb ops_l hp_l seq_l =
  let hp_l' = opt_hp hp_l seq_l in
  let s = scc_partition eqb hp_l' (uniq_ops eqb ops_l) in alg3_loop seq_l s []

(** val l : locus **)

let l =
  []

(** val p1_q : var **)

let p1_q =
  0

(** val p1_x : var **)

let p1_x =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))

(** val p_1 : op_list **)

let p_1 =
  (OpAP (CNew (p1_q, (Stdlib.Int.succ 0)))) :: ((OpAP (CAppU (l, (H (p1_q,
    (Num 0)))))) :: ((OpAP (CMeas (p1_x, l))) :: []))

(** val p_3_q0 : var **)

let p_3_q0 =
  0

(** val p_3_q1 : var **)

let p_3_q1 =
  Stdlib.Int.succ 0

(** val p_3_q2 : var **)

let p_3_q2 =
  Stdlib.Int.succ (Stdlib.Int.succ 0)

(** val p_3_x0 : var **)

let p_3_x0 =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))

(** val p_3_x1 : var **)

let p_3_x1 =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))

(** val p_3_x2 : var **)

let p_3_x2 =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))

(** val cX_01 : exp **)

let cX_01 =
  CU (p_3_q0, (Num 0), (X (p_3_q1, (Num 0))))

(** val cX_02 : exp **)

let cX_02 =
  CU (p_3_q0, (Num 0), (X (p_3_q2, (Num 0))))

(** val p_3 : op_list **)

let p_3 =
  (OpAP (CNew (p_3_q0, (Stdlib.Int.succ 0)))) :: ((OpAP (CNew (p_3_q1,
    (Stdlib.Int.succ 0)))) :: ((OpAP (CNew (p_3_q2, (Stdlib.Int.succ
    0)))) :: ((OpAP (CAppU (l, (H (p_3_q0, (Num 0)))))) :: ((OpAP (CAppU (l,
    cX_01))) :: ((OpAP (CAppU (l, cX_02))) :: ((OpAP (CMeas (p_3_x0,
    l))) :: ((OpAP (CMeas (p_3_x1, l))) :: ((OpAP (CMeas (p_3_x2,
    l))) :: []))))))))

(** val p_4_q : var **)

let p_4_q =
  0

(** val p_4_n : int **)

let p_4_n =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))

(** val p_4_x : var **)

let p_4_x =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))

(** val p_4 : op_list **)

let p_4 =
  (OpAP (CNew (p_4_q, (Stdlib.Int.succ 0)))) :: ((OpAP (CAppU (l, (H (p_4_q,
    (Num 0)))))) :: ((OpAP (CAppU (l, (QFT (p_4_q, p_4_n))))) :: ((OpAP
    (CAppU (l, (RQFT (p_4_q, p_4_n))))) :: ((OpAP (CMeas (p_4_x,
    l))) :: []))))

(** val p_5_q0 : var **)

let p_5_q0 =
  0

(** val p_5_q1 : var **)

let p_5_q1 =
  Stdlib.Int.succ 0

(** val p_5_x0 : var **)

let p_5_x0 =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))

(** val p_5_x1 : var **)

let p_5_x1 =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))

(** val theta_pi : int **)

let theta_pi =
  Stdlib.Int.succ 0

(** val oRACLE_01 : exp **)

let oRACLE_01 =
  CU (p_5_q0, (Num 0), (RZ (0, p_5_q1, (Num theta_pi))))

(** val p_5 : op_list **)

let p_5 =
  (OpAP (CNew (p_5_q0, (Stdlib.Int.succ 0)))) :: ((OpAP (CNew (p_5_q1,
    (Stdlib.Int.succ 0)))) :: ((OpAP (CAppU (l, (H (p_5_q0, (Num
    0)))))) :: ((OpAP (CAppU (l, (H (p_5_q1, (Num 0)))))) :: ((OpAP (CAppU
    (l, oRACLE_01))) :: ((OpAP (CAppU (l, (H (p_5_q0, (Num 0)))))) :: ((OpAP
    (CAppU (l, (H (p_5_q1, (Num 0)))))) :: ((OpAP (CAppU (l, (X (p_5_q0, (Num
    0)))))) :: ((OpAP (CAppU (l, (X (p_5_q1, (Num 0)))))) :: ((OpAP (CAppU
    (l, oRACLE_01))) :: ((OpAP (CAppU (l, (X (p_5_q0, (Num 0)))))) :: ((OpAP
    (CAppU (l, (X (p_5_q1, (Num 0)))))) :: ((OpAP (CAppU (l, (H (p_5_q0, (Num
    0)))))) :: ((OpAP (CAppU (l, (H (p_5_q1, (Num 0)))))) :: ((OpAP (CMeas
    (p_5_x0, l))) :: ((OpAP (CMeas (p_5_x1, l))) :: [])))))))))))))))

(** val p_6_qs : var **)

let p_6_qs =
  0

(** val p_6_qa : var **)

let p_6_qa =
  Stdlib.Int.succ 0

(** val p_6_qb : var **)

let p_6_qb =
  Stdlib.Int.succ (Stdlib.Int.succ 0)

(** val p_6_m1 : var **)

let p_6_m1 =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))

(** val p_6_m2 : var **)

let p_6_m2 =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))

(** val cNOT_a_b : exp **)

let cNOT_a_b =
  CU (p_6_qa, (Num 0), (X (p_6_qb, (Num 0))))

(** val cNOT_s_a : exp **)

let cNOT_s_a =
  CU (p_6_qs, (Num 0), (X (p_6_qa, (Num 0))))

(** val zcorr_qb : exp **)

let zcorr_qb =
  RZ (0, p_6_qb, (Num theta_pi))

(** val xcorr_qb : exp **)

let xcorr_qb =
  X (p_6_qb, (Num 0))

(** val proc_Xcorr : process **)

let proc_Xcorr =
  AP ((CAppU (l, xcorr_qb)), PNil)

(** val proc_Zcorr : process **)

let proc_Zcorr =
  AP ((CAppU (l, zcorr_qb)), PNil)

(** val p_6 : op_list **)

let p_6 =
  (OpAP (CNew (p_6_qs, (Stdlib.Int.succ 0)))) :: ((OpAP (CNew (p_6_qa,
    (Stdlib.Int.succ 0)))) :: ((OpAP (CNew (p_6_qb, (Stdlib.Int.succ
    0)))) :: ((OpAP (CAppU (l, (H (p_6_qs, (Num 0)))))) :: ((OpAP (CAppU (l,
    (H (p_6_qa, (Num 0)))))) :: ((OpAP (CAppU (l, cNOT_a_b))) :: ((OpAP
    (CAppU (l, cNOT_s_a))) :: ((OpAP (CAppU (l, (H (p_6_qs, (Num
    0)))))) :: ((OpAP (CMeas (p_6_m1, l))) :: ((OpAP (CMeas (p_6_m2,
    l))) :: ((OpIf ((CEq ((BA p_6_m2), (Num (Stdlib.Int.succ 0)))),
    proc_Xcorr, PNil)) :: ((OpIf ((CEq ((BA p_6_m1), (Num (Stdlib.Int.succ
    0)))), proc_Zcorr, PNil)) :: [])))))))))))

(** val w0 : var **)

let w0 =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))

(** val w1 : var **)

let w1 =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))

(** val iNC_mod4 : exp **)

let iNC_mod4 =
  Seq ((X (w0, (Num 0))), (CU (w0, (Num 0), (X (w1, (Num 0))))))

(** val pow_mod : int -> int -> int -> int **)

let rec pow_mod a e n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> modulo (Stdlib.Int.succ 0) n)
    (fun e' -> Nat.modulo (mul a (pow_mod a e' n)) n)
    e

(** val two_pow : int -> int **)

let two_pow t =
  Nat.pow (Stdlib.Int.succ (Stdlib.Int.succ 0)) t

(** val find_period_exact_from : int -> int -> int -> int -> int **)

let rec find_period_exact_from m t r fuel =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> 0)
    (fun fuel' ->
    if (=) (Nat.modulo (mul m r) (two_pow t)) 0
    then r
    else find_period_exact_from m t (Stdlib.Int.succ r) fuel')
    fuel

(** val find_period_exact : int -> int -> int -> int **)

let find_period_exact m t rmax =
  find_period_exact_from m t (Stdlib.Int.succ 0) rmax

(** val shor_factors_from_r : int -> int -> int -> int * int **)

let shor_factors_from_r a n r =
  if Nat.even r
  then let x =
         pow_mod a
           (let y = Stdlib.Int.succ (Stdlib.Int.succ 0) in
            (fun fO fS n -> if n=0 then fO () else fS (n-1))
              (fun _ -> y)
              (fun y' -> fst (Nat.divmod r y' 0 y'))
              y) n
       in
       let f1 = Nat.gcd (Nat.sub x (Stdlib.Int.succ 0)) n in
       let f2 = Nat.gcd (add x (Stdlib.Int.succ 0)) n in (f1, f2)
  else ((Stdlib.Int.succ 0), n)

(** val p0 : var **)

let p0 =
  0

(** val p1 : var **)

let p1 =
  Stdlib.Int.succ 0

(** val p2 : var **)

let p2 =
  Stdlib.Int.succ (Stdlib.Int.succ 0)

(** val m0 : var **)

let m0 =
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
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val m1 : var **)

let m1 =
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
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val m2 : var **)

let m2 =
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
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val new_p0 : cexp **)

let new_p0 =
  CNew (p0, (Stdlib.Int.succ 0))

(** val new_p1 : cexp **)

let new_p1 =
  CNew (p1, (Stdlib.Int.succ 0))

(** val new_p2 : cexp **)

let new_p2 =
  CNew (p2, (Stdlib.Int.succ 0))

(** val new_w0 : cexp **)

let new_w0 =
  CNew (w0, (Stdlib.Int.succ 0))

(** val new_w1 : cexp **)

let new_w1 =
  CNew (w1, (Stdlib.Int.succ 0))

(** val appH_p0 : cexp **)

let appH_p0 =
  CAppU (l, (H (p0, (Num 0))))

(** val appH_p1 : cexp **)

let appH_p1 =
  CAppU (l, (H (p1, (Num 0))))

(** val appH_p2 : cexp **)

let appH_p2 =
  CAppU (l, (H (p2, (Num 0))))

(** val cU_p0 : cexp **)

let cU_p0 =
  CAppU (l, (CU (p0, (Num 0), iNC_mod4)))

(** val cU_p1 : cexp **)

let cU_p1 =
  CAppU (l, (CU (p1, (Num 0), (Seq (iNC_mod4, iNC_mod4)))))

(** val cU_p2 : cexp **)

let cU_p2 =
  CAppU (l, (CU (p2, (Num 0), (Seq (iNC_mod4, (Seq (iNC_mod4, (Seq (iNC_mod4,
    iNC_mod4)))))))))

(** val appRQFT : cexp **)

let appRQFT =
  CAppU (l, (RQFT (p0, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))

(** val meas_p0 : cexp **)

let meas_p0 =
  CMeas (m0, l)

(** val meas_p1 : cexp **)

let meas_p1 =
  CMeas (m1, l)

(** val meas_p2 : cexp **)

let meas_p2 =
  CMeas (m2, l)

(** val shor_Qprog : op_list **)

let shor_Qprog =
  (OpAP new_p0) :: ((OpAP new_p1) :: ((OpAP new_p2) :: ((OpAP
    new_w0) :: ((OpAP new_w1) :: ((OpAP appH_p0) :: ((OpAP appH_p1) :: ((OpAP
    appH_p2) :: ((OpAP cU_p0) :: ((OpAP cU_p1) :: ((OpAP cU_p2) :: ((OpAP
    appRQFT) :: ((OpAP meas_p0) :: ((OpAP meas_p1) :: ((OpAP
    meas_p2) :: []))))))))))))))
