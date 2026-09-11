module Names = Map.Make (String)
module NameMap = Map.Make (Int)

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

type resolution_ctx = int Names.t * int
type name_map = string NameMap.t

let empty_ctx = (Names.empty, 0)
let empty_names = NameMap.empty

let string_of_tok (ctx : name_map) tok =
  match tok with
  | Ident int ->
      let s =
        NameMap.find_opt int ctx |> Option.value ~default:"<illegal ident>"
      in
      String.cat "Ident " s
  | Func -> "`func`"
  | Var -> "`var`"
  | Return -> "`return`"
  | If -> "`if`"
  | Else -> "`else`"
  | OpenParen -> "`(`"
  | CloseParen -> "`)`"
  | OpenBrace -> "`{`"
  | CloseBrace -> "`}`"
  | Semicolon -> "`;`"
  | Colon -> "`:`"
  | Dot -> "`.`"
  | Comma -> "`,`"
  | LessEq -> "`<=`"
  | Less -> "`<`"
  | GreaterEq -> "`>=`"
  | Greater -> "`>`"
  | Eq -> "`=`"
  | EqEq -> "`==`"
  | Integer i -> String.cat "Int " @@ Int64.to_string i
  | Plus -> "`+`"
  | Minus -> "`-`"
  | Star -> "`*`"
  | Slash -> "`/`"

let ident (ctx : resolution_ctx) s =
  match s with
  | "func" -> (ctx, Func)
  | "var" -> (ctx, Var)
  | "if" -> (ctx, If)
  | "else" -> (ctx, Else)
  | s -> begin
      let names, next = ctx in
      let i = Names.find_opt s names in
      match i with
      | Some x -> (ctx, Ident x)
      | None ->
          let ctx = (Names.add s next names, next + 1) in
          (ctx, Ident next)
    end

let build_name_map ((ctx, _) : resolution_ctx) : name_map =
  Names.bindings ctx |> List.map (fun (a, b) -> (b, a)) |> NameMap.of_list

type chars = { chars : (int * char) Seq.t; peek : (int * char) list }

let dbg_chars c =
  let peek =
    List.map
      (fun (i, ch) -> Printf.sprintf "(%d,'%s')" i (Char.escaped ch))
      c.peek
  in
  let peek = String.concat ", " peek in
  let s = Printf.sprintf "(chars=<...>; peek=%s)" peek in
  print_endline s;
  c

let new_chars s = { chars = String.to_seqi s; peek = [] }

let rec take n (s : (int * char) Seq.t) =
  if n <= 0 then ([], s)
  else
    match Seq.uncons s with
    | None -> ([], s)
    | Some (x, xs) ->
        let tail, rest = take (n - 1) xs in
        (x :: tail, rest)

let prefix_with_length len (s : chars) =
  let have = List.length s.peek in
  if have >= len then (s, List.take len s.peek)
  else begin
    let rest, chars = take (len - have) s.chars in
    let peek = s.peek @ List.rev rest in
    ({ peek; chars }, peek)
  end

let next_char (s : chars) =
  let ret =
    match s.peek with
    | x :: xs -> ({ s with peek = xs }, Some x)
    | [] ->
        begin match Seq.uncons s.chars with
        | Some (x, xs) -> ({ chars = xs; peek = [] }, Some x)
        | None -> (s, None)
        end
  in
  let chars, ret = ret in
  (chars, ret)

let consume_char s =
  let s, _ = next_char s in
  s

let peek_char (s : chars) =
  match s.peek with
  | x :: _ -> (s, Some x)
  | [] ->
      begin match Seq.uncons s.chars with
      | Some (x, xs) -> ({ chars = xs; peek = [ x ] }, Some x)
      | None -> (s, None)
      end

let is_ident_start ch =
  ('a' <= ch && ch <= 'z') || ('A' <= ch && ch <= 'Z') || ch == '_'

let is_digit ch = '0' <= ch && ch <= '9'
let is_ident ch = is_ident_start ch || is_digit ch
let is_whitespace ch = ch == ' ' || ch == '\n' || ch == '\t' || ch == '\r'
let is_some_and pred opt = match opt with None -> false | Some x -> pred x

let rec trim_leading_spaces (s : chars) =
  let s, head = peek_char s in
  if is_some_and is_whitespace (Option.map snd head) then
    let s, _ = next_char s in
    trim_leading_spaces s
  else s

let rec list_equals cmp a b =
  match (a, b) with
  | [], [] -> true
  | x :: xs, y :: ys -> if cmp x y then list_equals cmp xs ys else false
  | _ -> false

let has_prefix (prefix : char list) (s : chars) =
  let len = List.length prefix in
  let s, pre = prefix_with_length len s in
  let f = Fun.compose Char.equal snd in
  (s, list_equals f pre prefix)

let rec skip n (s : chars) = if n <= 0 then s else skip (n - 1) (consume_char s)

let rec take_while pred (chars : chars) =
  let chars, next = peek_char chars in
  match next with
  | Some (_, next) when pred next ->
      let chars, rest = chars |> consume_char |> take_while pred in
      (chars, Seq.cons next rest)
  | _ -> (chars, Seq.empty)

let guard f (state, prev) =
  match prev with None -> f state | Some x -> (state, Some x)

let const_tok prefix tok chars =
  let open Continuation in
  let chars, b = has_prefix prefix chars in
  if b then Return (skip (List.length prefix) chars, tok)
  else Continue (chars, ())

type state = { chars : chars; ctx : resolution_ctx }

let next_token ctx (s : chars) =
  let open Continuation in
  let s = trim_leading_spaces s in
  let initial_state = { chars = s; ctx } in

  let const_tok prefix (tok : token) =
   fun state _ : (_, _, token option) continuation ->
    let ret = const_tok prefix tok state.chars in
    map_gstate (fun chars -> { state with chars }) ret |> map_ret Option.some
  in

  let var_len_tok first cont builder state ch =
    if first ch then begin
      let chars, suffix = take_while cont state.chars in
      let id = String.of_seq @@ Seq.cons ch suffix in
      let state, ret = builder { state with chars } id in
      Return (state, Some ret)
    end
    else Continue (state, ch)
  in

  let cont =
    Continue (initial_state, ())
    >>= const_tok [ '(' ] OpenParen
    >>= const_tok [ ')' ] CloseParen
    >>= const_tok [ '{' ] OpenBrace
    >>= const_tok [ '}' ] CloseBrace
    >>= const_tok [ ';' ] Semicolon
    >>= const_tok [ ',' ] Comma (* *)
    >>= const_tok [ ':' ] Colon (* *)
    >>= const_tok [ '.' ] Dot
    >>= const_tok [ '<'; '=' ] LessEq
    >>= const_tok [ '>'; '=' ] GreaterEq
    >>= const_tok [ '='; '=' ] EqEq
    >>= const_tok [ '<' ] Less (* *)
    >>= const_tok [ '>' ] Greater (* *)
    >>= const_tok [ '=' ] Eq (* .... *)
    >>= const_tok [ '+' ] Plus (* .. *)
    >>= const_tok [ '-' ] Minus (* . *)
    >>= const_tok [ '*' ] Star (* .. *)
    >>= const_tok [ '/' ] Slash
    >>= fun state () ->
    begin match next_char state.chars with
    | chars, None -> Return ({ state with chars }, None)
    | chars, Some (_, ch) -> Continue ({ state with chars }, ch)
    end
    >>= fun state ch ->
    Continue (state, ch)
    >>= var_len_tok is_ident_start is_ident (fun state id ->
        let ctx, id = ident state.ctx id in
        ({ state with ctx }, id))
    >>= var_len_tok is_digit is_digit (fun state id ->
        let id = Int64.of_string id in
        (state, Integer id))
  in
  match cont with
  | Continue (_, ch) -> raise (Failure (Printf.sprintf "unexpected char %c" ch))
  | Return ({ ctx; chars }, r) -> (ctx, chars, r)
