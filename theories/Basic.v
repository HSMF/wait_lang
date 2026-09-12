From Stdlib.Strings Require Import String.
From Stdlib.Lists Require Import List.
From Stdlib Require Import Utf8_core.

Require Import Stdlib.FSets.FMapList.
Require Import Stdlib.Structures.OrderedTypeEx.
Module Import NatMap := FMapList.Make(Nat_as_OT).


(* Inductive option (A: Type) : Type :=
  | Some : A → option A
  | None : option A
. *)

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
    Func : nat → typ → list statement → item
  .

End Ast.

Module Ir.
  Inductive label : Set :=
    Label : nat → label
  .

  Inductive ident : Set :=
    Local : nat → ident
  .

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

  Inductive basic_block : Set :=
    BasicBlock : label → list instr → term → basic_block
  .

  Inductive func : Set :=
    Func : nat → basic_block → list basic_block → func
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

Record ctx := mkCtx {
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
    (c, cur) (* TODO *)
  | Ast.SAssign v e =>
    let '(c, cur, e) := compile_expr c cur e in
    let (c, tmp) := get_ident c in
    match NatMap.find v (scope c) with
    | Some dst =>
        let cur := add_instr cur (Ir.Instr tmp (Ir.Store dst e))
        in (c, cur) (* TODO *)
    | None => (c, cur)
    end
  | Ast.SReturn None => (c, cur) (* TODO *)
  | Ast.SReturn (Some e) => (c, cur) (* TODO *)
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

Definition compile_func ( name : nat ) (ret : Ast.typ) ( body : list Ast.statement ) : Ir.func :=
  let ctx := empty_ctx in
  let (ctx, entry_label) := get_label ctx in
  let cur := (empty_bb entry_label) in
  let (ctx, cur) := compile_scope
    ctx cur
    body
  in
  let t := Ir.Return (Ir.Int O) in
  let cur := finish_bb cur t in
  let (entry, rest) := match block_store ctx with
  | WithEntry e bs => (e, cons cur bs)
  | WithoutEntry => (cur, nil)
  end in
  Ir.Func name entry rest
.

End Compile.

Definition compile ( e : Ast.item ) : Ir.func :=
  match e with
  | Ast.Func name ret body => Compile.compile_func name ret body
  end.

Definition foo ( e : Ir.func ) : nat :=
  17
.

Require Extraction.
Extraction Language OCaml.
Extraction "extracted.ml" plus compile foo.

