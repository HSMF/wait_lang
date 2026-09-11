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

Definition compile ( e : item ) : nat :=
  match e with
  | Func name ret body => name
  end.


Require Extraction.
Extraction Language OCaml.
Extraction "extracted.ml" plus compile.

