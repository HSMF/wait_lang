let src =
  {|
func foo() {
  var x : int;
  x = 1;
  var y : int;
  y = x;
  return x;
}
|}

let () = print_endline src
let names, tokens = Wait.Hello.all_tokens src

let () =
  List.iter
    (fun tok ->
      print_endline (String.cat "- " @@ Wait.Lex.string_of_tok names tok))
    tokens

let names, ast =
  match Wait.Parse.parse src with
  | Error e ->
      print_endline e;
      raise (Failure e)
  | Ok (names, ast) -> (names, ast)

let () =
  List.iter (fun item -> print_endline @@ Wait.Glue.Ast.item_to_string item) ast

let compiled = List.map Wait.Extracted.compile ast

let () =
  List.iter
    (fun item -> print_endline @@ Wait.Glue.Ir.func_to_string item)
    compiled

let () =
  List.iter
    (fun item -> print_endline @@ Wait.Glue.Pretty.Ir.func_to_string names item)
    compiled

let f =
  List.map Wait.Extracted.Lower.lower compiled
  |> List.map Wait.Glue.list_of_rlist
  |> List.flatten

let () = print_endline (Wait.Hello.asm_to_string f)
