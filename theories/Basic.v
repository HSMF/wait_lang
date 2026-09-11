From Stdlib.Strings Require Import String.
From Stdlib.Lists Require Import List.
From Stdlib Require Import Utf8_core.

Inductive option (A: Type) : Type :=
  | Some : A → option A
  | None : option A
.

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

Definition compile ( e : item ) : nat :=
  match e with
  | Func name ret body => name
  end.

Definition foo ( e : Ir.func ) : nat :=
  0
.

Require Extraction.
Extraction Language OCaml.
Extraction "extracted.ml" plus compile foo.

