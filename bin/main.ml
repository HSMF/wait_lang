let src = {|
func foo() {
  var x : int;
  x = 1;
  var y : int;
  y = x;
}
|}

let () = print_endline src
let names, tokens = Wait.Hello.all_tokens src

let () =
  List.iter
    (fun tok ->
      print_endline (String.cat "- " @@ Wait.Lex.string_of_tok names tok))
    tokens

let () =
  match Wait.Parse.parse src with
  | Error e -> print_endline e
  | Ok (names, ast) ->
      List.iter
        (fun item -> print_endline @@ Wait.Glue.Ast.item_to_string item)
        ast
