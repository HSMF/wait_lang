open Lex

let all_tokens s =
  let rec aux acc ctx chars =
    match Lex.next_token ctx chars with
    | ctx, chars, None -> (acc, ctx)
    | ctx, chars, Some tok -> begin aux (tok :: acc) ctx chars end
  in
  let ret, ctx = aux [] Lex.empty_ctx (Lex.new_chars s) in
  (Lex.build_name_map ctx, List.rev ret)

let asm_to_string (s : Extracted.Asm.stmt list) =
  let open Extracted.Asm in
  let open Printf in
  let ( ++ ) = String.cat in
  let reg_short which size =
    match size with
    | Byte -> sprintf "%%%cl" which
    | Word -> sprintf "%%%cx" which
    | Long -> sprintf "%%e%cx" which
    | Quad -> sprintf "%%r%cx" which
  in
  let reg_med which size =
    match size with
    | Byte -> sprintf "%%%sl" which
    | Word -> sprintf "%%%s" which
    | Long -> sprintf "%%e%s" which
    | Quad -> sprintf "%%r%s" which
  in
  let reg_num which size =
    match size with
    | Byte -> sprintf "%%r%db" which
    | Word -> sprintf "%%r%dw" which
    | Long -> sprintf "%%r%dd" which
    | Quad -> sprintf "%%r%d" which
  in
  let reg_to_string size r =
    match r with
    | A -> reg_short 'a' size
    | B -> reg_short 'b' size
    | C -> reg_short 'c' size
    | D -> reg_short 'd' size
    | SI -> reg_med "si" size
    | DI -> reg_med "di" size
    | RSP -> reg_med "sp" size
    | RBP -> reg_med "bp" size
    | R8 -> reg_num 8 size
    | R9 -> reg_num 9 size
    | R10 -> reg_num 10 size
    | R11 -> reg_num 11 size
    | R12 -> reg_num 12 size
    | R13 -> reg_num 13 size
    | R14 -> reg_num 14 size
    | R15 -> reg_num 15 size
  in
  let operand_to_string size = function
    | Reg r -> reg_to_string size r
    | Imm i -> sprintf "$%d" (Glue.int_of_nat i)
    | MemOff (o, r) ->
        sprintf "%d(%s)" (Glue.int_of_nat o) (reg_to_string size r)
  in
  let buf = Buffer.create 0 in
  let line s =
    Buffer.add_string buf s;
    Buffer.add_char buf '\n'
  in
  let code s =
    Buffer.add_char buf '\t';
    Buffer.add_string buf s;
    Buffer.add_char buf '\n'
  in
  let size s =
    match s with Byte -> "b" | Word -> "w" | Long -> "l" | Quad -> "q"
  in
  let ins2 mnem s o1 o2 =
    code
      (sprintf "%s%s %s, %s" mnem (size s) (operand_to_string s o1)
         (operand_to_string s o2))
  in
  let ins1 mnem s o1 =
    code (sprintf "%s%s %s" mnem (size s) (operand_to_string s o1))
  in
  let ll gl id =
    let id = Glue.int_of_nat id in
    sprintf ".%s.%d:" gl id
  in
  let stmt gl s =
    match s with
    | GLabel s ->
        let s = Glue.string_of_rstring s in
        line (".globl " ++ s);
        line (s ++ ":")
    | LocLabel id -> line (ll gl id)
    | Mov (s, o1, o2) -> ins2 "mov" s o1 o2
    | Pop (s, o1) -> ins1 "pop" s o1
    | Push (s, o1) -> ins1 "push" s o1
    | Add (s, o1, o2) -> ins2 "add" s o1 o2
    | Ret -> code "ret"
    | Jump target -> code ("jump " ++ ll gl target)
    | Err -> code "; error"
    | TraceIns ins -> code (sprintf "; %s" (Glue.Ir.instr_to_string ins))
  in
  let rec loop gl s =
    match s with
    | [] -> ()
    | GLabel label :: xs ->
        stmt gl (GLabel label);
        let s = Glue.string_of_rstring label in
        loop s xs
    | x :: xs ->
        stmt gl x;
        loop gl xs
  in
  loop "" s;
  Buffer.contents buf
