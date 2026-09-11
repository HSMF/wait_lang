type parse_error = string

val parse :
  string -> (Lex.name_map * Extracted.Ast.item list, parse_error) Stdlib.result
