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
      "SDeclare" ++ " (" ++ nat_to_string i0 ++ ", " ++ typ_to_string i1 ++ ")"
  | SAssign (i0, i1) ->
      "SAssign" ++ " (" ++ nat_to_string i0 ++ ", " ++ expr_to_string i1 ++ ")"
  | SReturn i0 -> "SReturn" ++ " " ++ option_to_string expr_to_string i0

let item_to_string x =
  match x with
  | Func (i0, i1, i2) ->
      "Func" ++ " (" ++ nat_to_string i0 ++ ", " ++ typ_to_string i1 ++ ", "
      ++ list_to_string statement_to_string i2
      ++ ")"
