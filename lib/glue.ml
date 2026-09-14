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

let string_of_rstring rs =
  let o b = match b with True -> 1 | False -> 0 in
  let ( << ) = Int.shift_left in
  let ( + ) = Int.logor in
  let ascii_to_char a =
    match a with
    | Ascii (b0, b1, b2, b3, b4, b5, b6, b7) ->
        (o b0 << 7)
        + (o b1 << 6)
        + (o b2 << 5)
        + (o b3 << 4)
        + (o b4 << 3)
        + (o b5 << 2)
        + (o b6 << 1)
        + o b7
        |> Char.chr
  in
  let buf = Buffer.create 0 in
  let rec aux s =
    match s with
    | EmptyString -> ()
    | String (x, xs) ->
        Buffer.add_char buf (ascii_to_char x);
        aux xs
  in
  aux rs;
  Buffer.contents buf

let rstring_of_string (s : String.t) =
  let ( >> ) = Int.shift_right_logical in
  let ( & ) = Int.logand in
  let char_to_ascii ch =
    let code = Char.code ch in
    let b n = if (code >> n & 1) == 0 then False else True in
    Ascii (b 7, b 6, b 5, b 4, b 3, b 2, b 1, b 0)
  in
  String.fold_right (fun ch a -> String (char_to_ascii ch, a)) s EmptyString

let ( ++ ) = String.cat
let nat_to_string = Fun.compose Int.to_string int_of_nat

let list_to_string a_to_string x =
  let rec inner lst =
    match lst with
    | Nil -> ""
    | Cons (i0, Nil) -> a_to_string i0
    | Cons (x, xs) -> a_to_string x ++ ", " ++ inner xs
  in
  "[" ++ inner x ++ "]"

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
        "Func" ++ " (" ++ string_of_rstring i0 ++ ", " ++ typ_to_string i1
        ++ ", "
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
    | ReturnNil -> "ReturnNil"
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
        "Func" ++ " (" ++ string_of_rstring i0 ++ ", "
        ++ basic_block_to_string i1 ++ ", "
        ++ list_to_string basic_block_to_string i2
        ++ ")"
end

module Pretty = struct
  module Ir = struct
    open! Ir
    open Extracted.Ir
    open Printf

    let nat_to_string = Fun.compose Int.to_string int_of_nat
    let label_to_string = nat_to_string
    let ident_to_string x = String.cat "%" (nat_to_string x)

    let rec map f = function
      | Extracted.Nil -> []
      | Extracted.Cons (x, xs) -> f x :: map f xs

    let instr_to_string x =
      match x with
      | Instr (dst, op) ->
          ident_to_string dst ++ " = " ++ operation_to_string op

    let basic_block_to_string x =
      match x with
      | BasicBlock (i0, i1, i2) ->
          let instr = map instr_to_string i1 in
          let instr = List.map (String.cat "  ") instr in
          let instr = List.map (Fun.flip String.cat "\n") instr in
          let instr = String.concat "" instr in
          label_to_string i0 ++ ":\n" ++ instr ++ "  " ++ term_to_string i2
          ++ "\n"

    let func_to_string names x =
      match x with
      | Func (name, entry, i2) ->
          "define @" ++ string_of_rstring name ++ "() {\n"
          ++ basic_block_to_string entry
          ++ String.concat "\n" (map basic_block_to_string i2)
          ++ "}"
  end
end
