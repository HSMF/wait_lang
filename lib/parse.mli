type parse_error = string

val parse :
  string -> (Lex.name_map * Extracted.item list, parse_error) Stdlib.result
