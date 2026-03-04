module Nat = struct
  let add (n:int) (m:int) : int = n + m
  let mul (n:int) (m:int) : int = n * m
  let sub (n:int) (m:int) : int = if n - m < 0 then 0 else n - m
  let ltb (n:int) (m:int) : bool = n < m
  let max (n:int) (m:int) : int = if n < m then m else n
  let even (n:int) : bool = (n land 1) = 0

  (* integer pow: fast exponentiation *)
  let pow (a:int) (e:int) : int =
    let rec go acc a e =
      if e <= 0 then acc
      else if (e land 1) = 1 then go (acc * a) (a * a) (e lsr 1)
      else go acc (a * a) (e lsr 1)
    in
    if e <= 0 then 1 else go 1 a e

  (* div/mod behave like nat-div/mod (assume y>0) *)
  let div (x:int) (y:int) : int =
    if y <= 0 then 0 else x / y

  let modulo (x:int) (y:int) : int =
    if y <= 0 then 0 else x mod y

  let rec gcd (a:int) (b:int) : int =
    if a < 0 then gcd (-a) b
    else if b < 0 then gcd a (-b)
    else if a = 0 then b
    else gcd (b mod a) a
end
