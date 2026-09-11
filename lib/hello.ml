open Lex

let all_tokens s =
  let rec aux acc ctx chars =
    match Lex.next_token ctx chars with
    | ctx, chars, None -> (acc, ctx)
    | ctx, chars, Some tok -> begin aux (tok :: acc) ctx chars end
  in
  let ret, ctx = aux [] Lex.empty_ctx (Lex.new_chars s) in
  (Lex.build_name_map ctx, List.rev ret)

