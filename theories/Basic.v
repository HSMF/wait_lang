From Stdlib.Strings Require Import String.
From Stdlib.Lists Require Import List.
From Stdlib Require Import Utf8_core.

Import List.ListNotations.

Require Import Stdlib.FSets.FMapList.
Require Import Stdlib.Structures.OrderedTypeEx.
Module Import NatMap := FMapList.Make(Nat_as_OT).


(* Inductive option (A: Type) : Type :=
  | Some : A → option A
  | None : option A
. *)

Definition op_bind {A B : Type} (lhs: option A) (rhs : A → option B) :=
  match lhs with
  | Some x => rhs x
  | None => None
  end.
Notation "'do' X <- A ; B" := (op_bind A (fun X => B)) (at level 200, X ident, A at level 100, B at level 200).

Definition or_default {A : Type} (default: A) (l : option A) :=
  match l with
  | Some x => x
  | None => default
  end.

Module Ast.
  Inductive binop : Set :=
    | BAdd : binop
    | BSub : binop
    | BMul : binop
    | BDiv : binop
    | BEq : binop
    | BLess : binop
    | BLessEq : binop
    | BGreater : binop
    | BGreaterEq : binop
  .

  Inductive unop : Set :=
    Neg : unop
  .

  Inductive expr : Set :=
    | EInteger : nat → expr
    | EVar : nat → expr
    | EBinop : expr → binop → expr → expr
    | EUnop : unop → expr → expr
  .

  Inductive typ : Set :=
    | TVar : nat → typ
    | TNil : typ
  .

  Inductive statement : Set :=
    (* var <name> <typ> *)
    | SDeclare : nat → typ → statement
    (* <name> = <expr> *)
    | SAssign : nat → expr → statement
    (* return <expr>; | return; *)
    | SReturn : option expr → statement
  .

  Inductive item : Set :=
    (* name, ret, body *)
    Func : string → typ → list statement → item
  .

End Ast.

Module AstInterp.

  Inductive value : Set :=
    | VInt : nat → value
    | VPoison : value
    | VNil : value
  .

  Record ctx := {
    scope : NatMap.t value;
  }.

  Definition set_var ctx v value :=
    let s := (NatMap.add v value (scope ctx)) in
    {| scope := s |}
  .

  Definition get_var ctx v :=
    match (NatMap.find v (scope ctx)) with
    | Some x => x
    | None => VPoison
    end
  .



  Inductive controlflow : Type :=
    | Continue : ctx → controlflow
    | Return : value → controlflow
  .

  Definition cf_bind lhs rhs :=
    match lhs with
    | Continue c => rhs c
    | Return v => Return v
    end
  .


  Infix "<|>" := cf_bind (at level 80, right associativity).

  Definition no_poison ctx v :=
    match v with
    | VPoison => Return VPoison
    | v => Continue ctx
  end.

  Definition int v :=
    match v with
    | VInt i => Some i
    | _ => None
    end.


  Definition eval_binop lhs (op: Ast.binop) rhs :=
    let ret := match op with
    | Ast.BAdd => do lhs <- int lhs ;
                  do rhs <- int rhs ;
                  Some (VInt (lhs + rhs))
    | _ => None
    end in
    match ret with
    | Some x => x
    | None => VPoison
    end
  .

  Fixpoint eval_expr ctx (e: Ast.expr) :=
    match e with
    | Ast.EInteger n => VInt n
    | Ast.EVar v => get_var ctx v
    | Ast.EBinop lhs op rhs =>
      let lhs := eval_expr ctx lhs in
      let rhs := eval_expr ctx rhs in
      eval_binop lhs op rhs
    | Ast.EUnop op e => VPoison (* TODO *)
    end
  .

  Definition eval_statement ctx (statement: Ast.statement) :=
    match statement with
    | Ast.SDeclare v t => Continue (set_var ctx v VPoison)
    | Ast.SAssign v e =>
      let e := eval_expr ctx e in
      no_poison ctx e <|> fun ctx =>
      let ctx := set_var ctx v e in
      Continue ctx
    | Ast.SReturn None => Return VNil
    | Ast.SReturn (Some e) =>
      let e := eval_expr ctx e in
      no_poison ctx e <|> fun ctx =>
      Return e
    end
  .

  Fixpoint eval_scope ctx scope :=
    match scope with
    | [] => Continue ctx
    | x :: xs => eval_statement ctx x <|> fun ctx =>
                   eval_scope ctx xs
    end.

  Definition eval_item ctx item :=
    match item with
    | Ast.Func name r body =>
        eval_scope ctx body <|> fun _ => Return VNil
    end
  .
End AstInterp.

Module Ir.
  Inductive label : Set :=
    Label : nat → label
  .

  Inductive ident : Set :=
    Local : nat → ident
  .

  Definition label_to_nat l := match l with Label l => l end.
  Definition ident_to_nat i := match i with Local i => i end.

  Inductive binop_kind : Set :=
    | BAdd : binop_kind
    | BSub : binop_kind
    | BMul : binop_kind
    | BDiv : binop_kind
    | BEq : binop_kind
    | BLess : binop_kind
    | BLessEq : binop_kind
    | BGreater : binop_kind
    | BGreaterEq : binop_kind
  .

  Inductive unop_kind : Set :=
    Neg : unop_kind
  .

  Inductive typ : Set :=
    | Int64 : typ
    | Uint64 : typ
    | Ptr : typ → typ
  .

  Inductive operand : Set :=
    | Ident : ident → operand
    | Int : nat → operand
  .

  Inductive term : Set :=
    | Jump : label → term
    | Return : operand → term
    | ReturnNil : term
    | CondJump : operand → label → label → term
  .

  Inductive operation : Set :=
    | Binop : operand → binop_kind → operand → operation
    | Unop : unop_kind → operand → operation
    | Alloca : typ → operation
    | Load : operand → operation
    | Store : ident → operand → operation
  .

  Inductive instr : Set :=
    (* dst, operation *)
    | Instr : ident → operation → instr
  .

  Definition i_dst ins :=
    match ins with
    | Instr dst _ => dst
    end.

  Inductive basic_block : Set :=
    BasicBlock : label → list instr → term → basic_block
  .

  Definition instrs bb :=
    match bb with
    | BasicBlock _ i _ => i
    end.

  Inductive func : Set :=
    Func : string → basic_block → list basic_block → func
  .
End Ir.

Module Compile.


Inductive names : Set :=
  (* label, ident *)
  Names : nat → nat → names
.

Inductive func_state : Set :=
  FuncState : names → list Ir.basic_block → func_state
.

Inductive blocks : Set :=
  | WithoutEntry : blocks
  | WithEntry : Ir.basic_block → list Ir.basic_block → blocks
.

Inductive partial_basic_block : Set :=
  | PartialBasicBlock : Ir.label → list Ir.instr → partial_basic_block
.

Definition add_instr ( self : partial_basic_block ) (i : Ir.instr) :=
  match self with
  | PartialBasicBlock l ins => PartialBasicBlock l (cons i ins)
  end
.

Record ctx := {
  name_ctx : names;
  scope : NatMap.t Ir.ident;
  block_store : blocks;
}.

Definition set_name_ctx (c : ctx) (n : names) :=
  {| name_ctx := n; scope := scope c; block_store := block_store c |}
  .

Definition set_scope (c : ctx) (s : NatMap.t Ir.ident) :=
  {| name_ctx := name_ctx c; scope := s; block_store := block_store c|}
  .

Definition set_block_store (c : ctx) (bs : blocks) :=
  {| name_ctx := name_ctx c; scope := scope c; block_store := bs |}
  .




Definition empty_bb (l : Ir.label) := PartialBasicBlock l nil.
Definition empty_blocks := WithoutEntry.
Definition empty_ctx : ctx :=
  {| name_ctx := Names 0 0; scope := (NatMap.empty Ir.ident); block_store := empty_blocks |}.

Definition finish_bb (part : partial_basic_block) (t : Ir.term) :=
  match part with
  | PartialBasicBlock l body => Ir.BasicBlock l (List.rev body) t
  end.


Definition add_block ( self : ctx ) ( b : Ir.basic_block ) :=
  let bs := match block_store self with
  | WithoutEntry => WithEntry b nil
  | WithEntry entry bs => WithEntry entry (cons b bs)
     end in
  set_block_store self bs
.

Definition add_binding ( self : ctx ) ( var : nat ) ( ident : Ir.ident ) :=
  set_scope self (NatMap.add var ident (scope self))
.

Definition label ( n : names ) : prod names Ir.label :=
  match n with
  | Names l i => pair (Names (S l) i) (Ir.Label l)
  end.

Definition ident ( n : names ) : prod names Ir.ident :=
  match n with
  | Names l i => pair (Names l (S i)) (Ir.Local i)
  end.

Definition get_label ( self : ctx ) :=
  let (names, ret) := label (name_ctx self) in
  (set_name_ctx self names, ret)
.

Definition get_ident ( self : ctx ) :=
  let (names, ret) := ident (name_ctx self) in
  (set_name_ctx self names, ret)
.

Definition compile_expr
  (c : ctx)
  (cur : partial_basic_block)
  ( e : Ast.expr ) :=
  match e with
  | Ast.EInteger v => (c, cur, Ir.Int v )
  | Ast.EVar v =>
    let (c, tmp) := get_ident c in
    match NatMap.find v (scope c) with
    | Some v =>
        let v := Ir.Ident v in
        let cur := add_instr cur (Ir.Instr tmp (Ir.Load v)) in
        (c, cur, Ir.Ident tmp)
    | None => (c, cur, Ir.Int 0) (* kinda bad error handling *)
    end
  | Ast.EBinop lhs op rhs => (c, cur, Ir.Int 0)
  | Ast.EUnop op e => (c, cur, Ir.Int 0)
  end
.

Definition compile_statement
  (c : ctx)
  (cur : partial_basic_block)
  ( s : Ast.statement ) :=
  match s with
  | Ast.SDeclare v t =>
    let (c, x) := get_ident c in
    let typ := Ir.Int64 in (* TODO *)
    let c := add_binding c v x in
    let cur := add_instr cur (Ir.Instr x (Ir.Alloca typ)) in
    (c, cur)
  | Ast.SAssign v e =>
    let '(c, cur, e) := compile_expr c cur e in
    let (c, tmp) := get_ident c in
    match NatMap.find v (scope c) with
    | Some dst =>
        let cur := add_instr cur (Ir.Instr tmp (Ir.Store dst e))
        in (c, cur)
    | None => (c, cur)
    end
  | Ast.SReturn e =>
    let '(c, cur, term) := match e with
             | Some e =>
                 let '(c, cur, e) := compile_expr c cur e in
                 (c, cur, Ir.Return e)
             | None => (c, cur, Ir.ReturnNil)
             end in
    let cur := finish_bb cur term in
    let c := add_block c cur in
    let (c, l) := get_label c in
    let cur := (empty_bb l) in
    (c, cur)
  end.


Fixpoint compile_scope
  ( c : ctx )
  (cur : partial_basic_block)
  ( body : list Ast.statement ) :=
  match body with
  | nil => (c, cur)
  | cons x xs =>
      let (c, cur) := compile_statement c cur x in
      compile_scope c cur xs
  end.

Definition compile_func ( name : string ) (ret : Ast.typ) ( body : list Ast.statement ) : Ir.func :=
  let ctx := empty_ctx in
  let (ctx, entry_label) := get_label ctx in
  let cur := (empty_bb entry_label) in
  let (ctx, cur) := compile_scope
    ctx cur
    body
  in
  let t := Ir.ReturnNil in
  let cur := finish_bb cur t in
  let (entry, rest) := match block_store ctx with
  | WithEntry e bs => (e, cons cur bs)
  | WithoutEntry => (cur, nil)
  end in
  Ir.Func name entry rest
.

End Compile.

Module Asm.
  Inductive reg : Set :=
  | A | B | C | D | SI | DI
  | RSP | RBP
  | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15
  .


  Inductive operand : Set :=
    | Reg : reg → operand
    | Imm : nat → operand
    (* <off>(<reg>) *)
    | MemOff : nat → reg → operand
  .

  Inductive size : Set :=
    | Byte
    | Word
    | Long
    | Quad
  .


  Inductive stmt : Set :=
  | LocLabel : nat → stmt
  | GLabel : string → stmt
  | Jump : nat → stmt
  | Mov : size → operand → operand → stmt
  | Push : size → operand → stmt
  | Pop : size → operand → stmt
  | Ret : stmt

  | Add : size → operand → operand → stmt
  | Err : stmt
  | TraceIns : Ir.instr → stmt
  .
End Asm.

(** lower IR to assembly *)
Module Lower.
  Import Asm.

  Inductive var_loc : Set :=
    | LocStack : nat → var_loc
    | LocReg : reg → var_loc
  .

  Record ctx := {
    alloc : NatMap.t var_loc
  }.

  Definition get_alloc ctx i :=
    NatMap.find (Ir.ident_to_nat i) (alloc ctx)
  .

  Definition reg_alloc (f : Ir.func) :=
    match f with
    | Ir.Func _ entry more =>
      let instrs := List.flat_map (Ir.instrs) ([entry] ++ more) in
      let dsts := List.map (Ir.i_dst) instrs in
      let (alloc, _) := List.fold_left
        (fun '(acc, off) dst =>
          (NatMap.add (Ir.ident_to_nat dst) (LocStack off) acc , off + 8))
        dsts (NatMap.empty var_loc, 8) in
      alloc
    end
  .

  Definition new_ctx (f : Ir.func) :=
    {| alloc := reg_alloc f |}.

  Definition fn_entry : list stmt :=
    [Push Quad (Reg RBP); Mov Quad (Reg RSP) (Reg RBP)]
  .

  Definition fn_exit : list stmt :=
    [ Pop Quad (Reg RBP); Ret ]
  .

  Definition to_reg (loc : var_loc) :=
    match loc with
    | LocStack off => ([ Mov Quad (MemOff off RBP) (Reg A) ], Reg A)
    | LocReg r => ([], Reg r)
    end
  .

  Definition or_err := or_default [Err].


  Definition var_loc_op ( v : var_loc ) :=
    match v with
    | LocReg r => Reg r
    | LocStack off => MemOff off RBP
    end.


  Definition compile_ir_op (ctx : ctx) (op : Ir.operand) :=
    match op with
    | Ir.Int n => Some (Imm n)
    | Ir.Ident i =>
      do alloc <- get_alloc ctx i;
      Some (var_loc_op alloc)
  end.

  Definition ir_op_to_reg_or_lit (ctx : ctx) ( op : Ir.operand ) :=
    match op with
    | Ir.Int n => Some ([], Imm n)
    | Ir.Ident i =>
        do i <- get_alloc ctx i;
        Some (to_reg i)
    end.


  Definition mov size src dst :=
    match (src, dst) with
    | (Asm.MemOff _ _, LocStack _) =>
        let (load, dst) := to_reg dst in
        load ++ [Mov size src dst]
    | _ =>
        let dst := var_loc_op dst in
        [Mov size src dst]
    end.

  Definition compile_ins_inner ( ctx: ctx ) (ins: Ir.instr) : option (list stmt) :=
    match ins with
    | Ir.Instr dst op =>
        do dst <- get_alloc ctx dst;
        match op with
        | Ir.Alloca t => Some []
        | Ir.Load addr =>
          do addr <- ir_op_to_reg_or_lit ctx addr;
          let (load, addr) := addr in
          Some (load ++ mov Quad addr dst )
        | Ir.Store dst v =>
          do dst <- get_alloc ctx dst;
          do src <- ir_op_to_reg_or_lit ctx v;
          let (load, src) := src in
          Some (load ++ mov Quad src dst)
        | _ => Some [] (* TODO *)
        end
    end
  .

  Definition compile_ins ( ctx: ctx ) (ins: Ir.instr) : option (list stmt) :=
    do i <- compile_ins_inner ctx ins;
    Some (i ++ [TraceIns ins])
  .

  Definition compile_term ( ctx: ctx ) (term: Ir.term) : list stmt :=
    match term with
    | Ir.Jump l => [ Jump (Ir.label_to_nat l) ]
    | Ir.ReturnNil => fn_exit
    | Ir.Return v =>
    let ret :=
      do v <- compile_ir_op ctx v;
      Some (mov Quad v (LocReg A) ++ fn_exit)
    in
    or_err ret
    | _ => [ Err (* TODO *) ]
    end
  .

  Definition compile_bb ( ctx: ctx ) ( bb : Ir.basic_block ) :=
    match bb with
    | Ir.BasicBlock lbl ins term =>
      let ins := List.map (compile_ins ctx) ins in
      let ins := List.map (or_err) ins in
      let ins := List.concat ins in
    [ LocLabel (Ir.label_to_nat lbl) ]
    ++ ins
    ++ compile_term ctx term
    end.

  Definition lower (f: Ir.func) : list stmt :=
    let ctx := new_ctx f in
    match f with
    | Ir.Func name entry blocks =>
    [ GLabel name ]
      ++ fn_entry
      ++ List.flat_map (compile_bb ctx) ([entry] ++ blocks)
    end
    .


End Lower.

Definition compile ( e : Ast.item ) : Ir.func :=
  match e with
  | Ast.Func name ret body => Compile.compile_func name ret body
  end.

Definition foo ( e : Ir.func ) : nat :=
  17
.

Require Extraction.
Extraction Language OCaml.
Extraction "extracted.ml" plus compile foo Lower.lower.

