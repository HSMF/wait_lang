module Names : Map.S with type key = string
module NameMap : Map.S with type key = int

type token =
  | Ident of int
  | Func
  | Var
  | Return
  | If
  | Else
  | OpenParen
  | CloseParen
  | OpenBrace
  | CloseBrace
  | Semicolon
  | Colon
  | Dot
  | Comma
  | LessEq
  | Less
  | GreaterEq
  | Greater
  | Eq
  | EqEq
  | Integer of int64
  | Plus
  | Minus
  | Star
  | Slash

type resolution_ctx
type name_map

val empty_ctx : resolution_ctx
val empty_names : name_map
val string_of_tok : name_map -> token -> string
val build_name_map : resolution_ctx -> name_map
val get_name : int -> name_map -> string

type chars

val new_chars : String.t -> chars
val guard : ('a -> 'a * 'b option) -> 'a * 'b option -> 'a * 'b option

val next_token :
  resolution_ctx -> chars -> resolution_ctx * chars * token option
