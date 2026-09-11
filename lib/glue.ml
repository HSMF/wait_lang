let rec nat_of_int n =
  if n <= 0 then Extracted.O else Extracted.S (nat_of_int (n - 1))

let int_of_nat n =
  let rec aux acc n =
    match n with Extracted.O -> acc | Extracted.S n -> aux (acc + 1) n
  in
  aux 0 n

(** rocq list of list *)
let rec rlist_of_list l =
  match l with
  | [] -> Extracted.Nil
  | x :: xs -> Extracted.Cons (x, rlist_of_list xs)

(** list of rocq list *)
let rec list_of_rlist l =
  match l with
  | Extracted.Nil -> []
  | Extracted.Cons (x, xs) -> x :: list_of_rlist xs

open Extracted
open Ast

let ( ++ ) = String.cat

let rec nat_to_string x =
  match x with O -> "O" | S i0 -> "S" ++ " " ++ nat_to_string i0

let rec list_to_string a_to_string x =
  match x with
  | Nil -> "Nil"
  | Cons (i0, i1) ->
      "Cons" ++ " (" ++ a_to_string i0 ++ ", "
      ++ list_to_string a_to_string i1
      ++ ")"

let option_to_string a_to_string x =
  match x with Some i0 -> "Some" ++ " " ++ a_to_string i0 | None -> "None"

module Ast = struct
  let binop_to_string x =
    match x with
    | BAdd -> "BAdd"
    | BSub -> "BSub"
    | BMul -> "BMul"
    | BDiv -> "BDiv"
    | BEq -> "BEq"
    | BLess -> "BLess"
    | BLessEq -> "BLessEq"
    | BGreater -> "BGreater"
    | BGreaterEq -> "BGreaterEq"

  let unop_to_string x = match x with Neg -> "Neg"

  let rec expr_to_string x =
    match x with
    | EInteger i0 -> "EInteger" ++ " " ++ nat_to_string i0
    | EVar i0 -> "EVar" ++ " " ++ nat_to_string i0
    | EBinop (i0, i1, i2) ->
        "EBinop" ++ " (" ++ expr_to_string i0 ++ ", " ++ binop_to_string i1
        ++ ", " ++ expr_to_string i2 ++ ")"
    | EUnop (i0, i1) ->
        "EUnop" ++ " (" ++ unop_to_string i0 ++ ", " ++ expr_to_string i1 ++ ")"

  let typ_to_string x =
    match x with TVar i0 -> "TVar" ++ " " ++ nat_to_string i0 | TNil -> "TNil"

  let statement_to_string x =
    match x with
    | SDeclare (i0, i1) ->
        "SDeclare" ++ " (" ++ nat_to_string i0 ++ ", " ++ typ_to_string i1
        ++ ")"
    | SAssign (i0, i1) ->
        "SAssign" ++ " (" ++ nat_to_string i0 ++ ", " ++ expr_to_string i1
        ++ ")"
    | SReturn i0 -> "SReturn" ++ " " ++ option_to_string expr_to_string i0

  let item_to_string x =
    match x with
    | Func (i0, i1, i2) ->
        "Func" ++ " (" ++ nat_to_string i0 ++ ", " ++ typ_to_string i1 ++ ", "
        ++ list_to_string statement_to_string i2
        ++ ")"
end

module Ir = struct
  open Ir

  let label_to_string = nat_to_string
  let ident_to_string = nat_to_string

  let binop_kind_to_string x =
    match x with
    | BAdd -> "BAdd"
    | BSub -> "BSub"
    | BMul -> "BMul"
    | BDiv -> "BDiv"
    | BEq -> "BEq"
    | BLess -> "BLess"
    | BLessEq -> "BLessEq"
    | BGreater -> "BGreater"
    | BGreaterEq -> "BGreaterEq"

  let unop_kind_to_string x = match x with Neg -> "Neg"

  let rec typ_to_string x =
    match x with
    | Int64 -> "Int64"
    | Uint64 -> "Uint64"
    | Ptr i0 -> "Ptr" ++ " " ++ typ_to_string i0

  let operand_to_string x =
    match x with
    | Ident i0 -> "Ident" ++ " " ++ ident_to_string i0
    | Int i0 -> "Int" ++ " " ++ nat_to_string i0

  let term_to_string x =
    match x with
    | Jump i0 -> "Jump" ++ " " ++ label_to_string i0
    | Return i0 -> "Return" ++ " " ++ operand_to_string i0
    | CondJump (i0, i1, i2) ->
        "CondJump" ++ " (" ++ operand_to_string i0 ++ ", " ++ label_to_string i1
        ++ ", " ++ label_to_string i2 ++ ")"

  let operation_to_string x =
    match x with
    | Binop (i0, i1, i2) ->
        "Binop" ++ " (" ++ operand_to_string i0 ++ ", "
        ++ binop_kind_to_string i1 ++ ", " ++ operand_to_string i2 ++ ")"
    | Unop (i0, i1) ->
        "Unop" ++ " (" ++ unop_kind_to_string i0 ++ ", " ++ operand_to_string i1
        ++ ")"
    | Alloca i0 -> "Alloca" ++ " " ++ typ_to_string i0
    | Load i0 -> "Load" ++ " " ++ operand_to_string i0
    | Store (i0, i1) ->
        "Store" ++ " (" ++ ident_to_string i0 ++ ", " ++ operand_to_string i1
        ++ ")"

  let instr_to_string x =
    match x with
    | Instr (i0, i1) ->
        "Instr" ++ " (" ++ ident_to_string i0 ++ ", " ++ operation_to_string i1
        ++ ")"

  let basic_block_to_string x =
    match x with
    | BasicBlock (i0, i1, i2) ->
        "BasicBlock" ++ " (" ++ label_to_string i0 ++ ", "
        ++ list_to_string instr_to_string i1
        ++ ", " ++ term_to_string i2 ++ ")"

  let func_to_string x =
    match x with
    | Func (i0, i1, i2) ->
        "Func" ++ " (" ++ nat_to_string i0 ++ ", " ++ basic_block_to_string i1
        ++ ", "
        ++ list_to_string basic_block_to_string i2
        ++ ")"
end
