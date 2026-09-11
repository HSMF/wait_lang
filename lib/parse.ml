type ctx = {
  names : Lex.resolution_ctx;
  chars : Lex.chars;
  last_tok : Lex.token option;
}

type parse_error = string
type 'a result = (ctx * 'a, parse_error) Result.t

module Ast = Extracted.Ast

let unexpected_token expected tok : 'a result =
  Error
    (Printf.sprintf "unexpected token: %s (expected %s)"
       (Lex.string_of_tok Lex.empty_names tok)
       expected)

let unexpected_eof : 'a result = Error (Printf.sprintf "unexpected eof")
let ( >>= ) = Result.bind

let new_parser s =
  let chars = Lex.new_chars s in
  let names = Lex.empty_ctx in
  { names; chars; last_tok = None }

let peek ctx =
  match ctx.last_tok with
  | None ->
      let names, chars, tok = Lex.next_token ctx.names ctx.chars in
      ({ names; chars; last_tok = tok }, tok)
  | Some t -> (ctx, Some t)

let next ctx =
  match ctx.last_tok with
  | None ->
      let names, chars, tok = Lex.next_token ctx.names ctx.chars in
      ({ names; chars; last_tok = None }, tok)
  | Some t -> ({ ctx with last_tok = None }, Some t)

let accept pat fn ctx =
  match peek ctx with
  | ctx, Some x when pat x -> (ctx, Some x)
  | ctx, _ -> (ctx, None)

let expect expected pat ctx =
  match next ctx with
  | ctx, Some tok ->
      begin match pat tok with
      | Some a -> Ok (ctx, a)
      | None -> unexpected_token expected tok
      end
  | ctx, None -> Error "unexpected eof"

let ident tok = match tok with Lex.Ident i -> Some i | _ -> None
let const which tok = if tok = which then Some () else None
let expect_ident = expect "ident" ident

let expect_const tok =
  expect (Lex.string_of_tok Lex.empty_names tok) (const tok)

let typ ctx =
  expect "ident" ident ctx
  |> Result.map (fun (ctx, id) -> (ctx, Ast.TVar (Glue.nat_of_int id)))

let parse_binop child map ctx =
  child ctx >>= fun (ctx, lhs) ->
  let rec loop lhs ctx =
    let ctx, tok = peek ctx in
    let tok = Option.bind tok map in
    match tok with
    | None -> Ok (ctx, lhs)
    | Some op ->
        child ctx >>= fun (ctx, rhs) -> loop (Ast.EBinop (lhs, op, rhs)) ctx
  in
  loop lhs ctx

let map_tok = Fun.flip List.assoc_opt

let rec term ctx =
  match next ctx with
  | ctx, Some (Lex.Integer i) ->
      Ok (ctx, Ast.EInteger (Glue.nat_of_int (Int64.to_int i)))
  | ctx, Some (Lex.Ident i) -> Ok (ctx, Ast.EVar (Glue.nat_of_int i))
  | ctx, Some Lex.OpenParen ->
      expr ctx >>= fun (ctx, e) ->
      expect_const Lex.CloseParen ctx >>= fun (ctx, ()) -> Ok (ctx, e)
  | ctx, Some tok -> unexpected_token "int or ident or `(`" tok
  | ctx, None -> unexpected_eof

and div_or_mul ctx =
  parse_binop term (map_tok [ (Lex.Slash, Ast.BDiv); (Lex.Star, Ast.BMul) ]) ctx

and add_or_sub ctx =
  parse_binop div_or_mul
    (map_tok [ (Lex.Plus, Ast.BAdd); (Lex.Minus, Ast.BSub) ])
    ctx

and cmps ctx =
  let open Ast in
  let open Lex in
  parse_binop add_or_sub
    (map_tok
       [
         (EqEq, BEq);
         (Less, BLess);
         (LessEq, BLessEq);
         (Greater, BGreater);
         (GreaterEq, BGreaterEq);
       ])
    ctx

and expr ctx = cmps ctx

let rec statement ctx =
  match next ctx with
  | ctx, Some Lex.Var ->
      expect_ident ctx >>= fun (ctx, id) ->
      expect_const Lex.Colon ctx >>= fun (ctx, ()) ->
      typ ctx >>= fun (ctx, t) ->
      expect_const Lex.Semicolon ctx >>= fun (ctx, ()) ->
      Ok (ctx, Ast.SDeclare (Glue.nat_of_int id, t))
  | ctx, Some (Lex.Ident id) ->
      expect_const Lex.Eq ctx >>= fun (ctx, ()) ->
      expr ctx >>= fun (ctx, e) ->
      expect_const Lex.Semicolon ctx >>= fun (ctx, ()) ->
      Ok (ctx, Ast.SAssign (Glue.nat_of_int id, e))
  | ctx, Some Lex.Return ->
      begin match peek ctx with
      | ctx, Some Lex.Semicolon ->
          let ctx, _ = next ctx in
          Ok (ctx, Extracted.None)
      | ctx, _ ->
          expr ctx >>= fun (ctx, e) ->
          expect_const Lex.Semicolon ctx >>= fun (ctx, ()) ->
          Ok (ctx, Extracted.Some e)
      end
      >>= fun (ctx, expr) -> Ok (ctx, Ast.SReturn expr)
  | ctx, Some Lex.If -> begin
      expr ctx >>= fun (ctx, cond) ->
      block ctx >>= fun (ctx, on_true) ->
      begin match peek ctx with
      | ctx, Some Lex.Else ->
          block ctx |> Result.map (fun (ctx, x) -> (ctx, Extracted.Some x))
      | ctx, _ -> Ok (ctx, None)
      end
      >>= fun (ctx, on_false) ->
      Error "if not implemented, no branching yet please"
      (* Ok (ctx, Ast.SIf (cond, on_true, on_false)) *)
    end
  | _, Some tok -> unexpected_token "var, ident, return, if" tok
  | _, None -> unexpected_eof

(** `'{' <statements> '}'` *)
and block ctx =
  let rec aux acc ctx =
    match peek ctx with
    | ctx, Some Lex.CloseBrace -> Ok (ctx, acc)
    | ctx, _ -> statement ctx >>= fun (ctx, stmt) -> aux (stmt :: acc) ctx
  in
  expect_const Lex.OpenBrace ctx >>= fun (ctx, ()) ->
  aux [] ctx >>= fun (ctx, s) ->
  expect_const Lex.CloseBrace ctx >>= fun (ctx, ()) -> Ok (ctx, List.rev s)

let argspec ctx = Ok (ctx, []) (* TODO *)

(** `'func' fname '(' <argspec> ')' '{' <statements> '}' `*)
let item ctx =
  match next ctx with
  | ctx, Some Lex.Func -> begin
      expect_ident ctx >>= fun (ctx, name) ->
      expect_const Lex.OpenParen ctx >>= fun (ctx, ()) ->
      argspec ctx >>= fun (ctx, args) ->
      expect_const Lex.CloseParen ctx >>= fun (ctx, ()) ->
      begin
        let ctx, tok = peek ctx in
        match tok with Some Lex.OpenBrace -> Ok (ctx, Ast.TNil) | _ -> typ ctx
      end
      >>= fun (ctx, ret_ty) ->
      block ctx >>= fun (ctx, body) ->
      Ok (ctx, Ast.Func (Glue.nat_of_int name, ret_ty, Glue.rlist_of_list body))
    end
  | _ -> Error "unexpected token"

let top ctx : Ast.item list result =
  let rec loop acc ctx =
    match peek ctx with
    | ctx, None -> Ok (ctx, acc)
    | ctx, Some _ -> item ctx >>= fun (ctx, i) -> loop (i :: acc) ctx
  in
  loop [] ctx >>= fun (ctx, items) -> Ok (ctx, List.rev items)

let parse s =
  let ctx = new_parser s in
  top ctx
  |> Result.map (fun (ctx, items) -> (Lex.build_name_map ctx.names, items))
