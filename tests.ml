open Autodisq_extract

(* ============================================================ *)
(* Config / locus                                                *)
(* ============================================================ *)

let cfg1 : config = [Memb (0, []); Memb (1, [])]
let l : locus = []   (* locus = range list *)

(* ============================================================ *)
(* Ripple-adder subcircuits (MAJ / UMA)                          *)
(* ============================================================ *)

let maj_at (a:var) (ai:aexp) (b:var) (bi:aexp) (c:var) (ci:aexp) : exp =
  Seq (
    CU (c, ci, X (b, bi)),
    Seq (
      CU (c, ci, X (a, ai)),
      CU (a, ai, CU (b, bi, X (b, bi)))
    )
  )

let uma_at (a:var) (ai:aexp) (b:var) (bi:aexp) (c:var) (ci:aexp) : exp =
  Seq (
    CU (a, ai, CU (b, bi, X (c, ci))),
    Seq (
      CU (c, ci, X (a, ai)),
      CU (a, ai, X (b, bi))
    )
  )

let rec majseq' (n:int) (t:var) (y:var) (x:var) : exp =
  if n <= 0 then
    maj_at x (Num 0) y (Num 0) t (Num 0)
  else
    let m = n - 1 in
    Seq (
      majseq' m t y x,
      maj_at x (Num m) y (Num n) x (Num n)
    )

let majseq (n:int) (t:var) (y:var) (x:var) : exp =
  if n <= 0 then SKIP (0, Num 0) else majseq' (n - 1) t y x

let rec umaseq' (n:int) (t:var) (y:var) (x:var) : exp =
  if n <= 0 then
    uma_at x (Num 0) y (Num 0) t (Num 0)
  else
    let m = n - 1 in
    Seq (
      uma_at t (Num m) y (Num n) t (Num n),
      umaseq' m t y x
    )

let umaseq (n:int) (t:var) (y:var) (x:var) : exp =
  if n <= 0 then SKIP (0, Num 0) else umaseq' (n - 1) t y x

(* ============================================================ *)
(* Variables / sizes                                             *)
(* ============================================================ *)

let nbits : int = 2
let t : var = 0
let y : var = 10
let x : var = 20

(* ============================================================ *)
(* ops list                                                      *)
(* ============================================================ *)

let ops : op_list =
  [
    OpAP (CNew (t, nbits));
    OpAP (CNew (y, nbits));
    OpAP (CNew (x, nbits));
    OpAP (CAppU (l, majseq nbits t y x));
    OpAP (CAppU (l, umaseq nbits t y x));
  ]

(* ============================================================ *)
(* Pretty printers                                               *)
(* ============================================================ *)

let pp_list (pp:'a -> string) (xs:'a list) : string =
  "[" ^ String.concat "; " (List.map pp xs) ^ "]"

let pp_var (v:var) : string = string_of_int v

let pp_bound (b:bound) : string =
  match b with
  | BNum n -> "BNum(" ^ string_of_int n ^ ")"
  (* add other bound constructors if your extraction has them *)

let pp_range (r:range) : string =
  let ((v, lo), hi) = r in
  "((" ^ pp_var v ^ "," ^ pp_bound lo ^ ")," ^ pp_bound hi ^ ")"

let pp_locus (loc:locus) : string =
  pp_list pp_range loc

let rec pp_aexp (a:aexp) : string =
  match a with
  | Num n -> "Num(" ^ string_of_int n ^ ")"
  | BA x  -> "BA(" ^ string_of_int x ^ ")"
  | APlus (a,b) -> "APlus(" ^ pp_aexp a ^ "," ^ pp_aexp b ^ ")"
  | AMult (a,b) -> "AMult(" ^ pp_aexp a ^ "," ^ pp_aexp b ^ ")"

let rec pp_exp (e:exp) : string =
  match e with
  | SKIP (v, i) -> "SKIP(" ^ pp_var v ^ "," ^ pp_aexp i ^ ")"
  | Seq (e1,e2) -> "Seq(" ^ pp_exp e1 ^ "," ^ pp_exp e2 ^ ")"
  | X (v,i)     -> "X(" ^ pp_var v ^ "," ^ pp_aexp i ^ ")"
  | CU (v,i,e1) -> "CU(" ^ pp_var v ^ "," ^ pp_aexp i ^ "," ^ pp_exp e1 ^ ")"
  (* add other exp constructors if needed *)

let pp_cexp (c:cexp) : string =
  match c with
  | CNew (v,n)      -> "CNew(" ^ pp_var v ^ "," ^ string_of_int n ^ ")"
  | CMeas (v,loc)   -> "CMeas(" ^ pp_var v ^ "," ^ pp_locus loc ^ ")"
  | CAppU (loc,e)   -> "CAppU(" ^ pp_locus loc ^ "," ^ pp_exp e ^ ")"
  (* add other cexp constructors if needed *)

let pp_myOp (op:myOp) : string =
  match op with
  | OpAP c -> "AP(" ^ pp_cexp c ^ ")"
  (* add other myOp constructors if needed *)

(* ============================================================ *)
(* process + config printing (THIS is where AP(...); PNil lives) *)
(* ============================================================ *)

(* You must match your real process constructors from autodisq_extract.mli.
   Most common in your earlier outputs: PNil + (op ; rest).
   Replace PCons with PSeq if your .mli uses PSeq, etc.
*)
let rec pp_process (p:process) : string =
  match p with
  | PNil -> "PNil"
  | PCons (op, rest) -> pp_myOp op ^ "; " ^ pp_process rest

(* memb printer: most common is Memb (membrane_id, process) *)
let pp_memb (m:memb) : string =
  match m with
  | Memb (mid, p) ->
      "Memb(" ^ pp_var mid ^ ", " ^ pp_process p ^ ")"

let pp_config (cfg:config) : string =
  pp_list pp_memb cfg

(* ============================================================ *)
(* partitions printers (sizes only, always safe)                 *)
(* ============================================================ *)

let pp_hp (hp:hp) : string = "hp_size=" ^ string_of_int (List.length hp)
let pp_os (os:os) : string = "os_size=" ^ string_of_int (List.length os)
let pp_cases (cs:case list) : string = "cases_size=" ^ string_of_int (List.length cs)

(* ============================================================ *)
(* Main                                                          *)
(* ============================================================ *)

let () =
  Printexc.record_backtrace true;

  print_endline "Input ops:";
  List.iter (fun op -> Printf.printf "  %s\n%!" (pp_myOp op)) ops;

  print_endline "Before generation...";
  flush stdout;

  let hp0 = gen_hp ops in
  let os  = gen_os ops in
  let all = mk_cases 2 2 in

  Printf.printf "Partition hp0: %s\n%!" (pp_hp hp0);
  Printf.printf "Partition os : %s\n%!" (pp_os os);
  Printf.printf "Cases ALL    : %s\n%!" (pp_cases all);

  try
    let dist : distributed_prog = auto_disq_alg1_paper 2 2 ops cfg1 in
    print_endline "Program generated.";
    Printf.printf "Cost = %d\n%!" (fit dist);

    (* distributed_prog = config, so print it as config *)
    Printf.printf "Distributed config:\n%s\n%!" (pp_config dist);

  with e ->
    Printf.eprintf "ERROR: %s\n%!" (Printexc.to_string e);
    Printf.eprintf "BACKTRACE:\n%s\n%!" (Printexc.get_backtrace ());
    exit 1
