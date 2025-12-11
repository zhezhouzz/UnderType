(** * This file defines the primitives of the core language. *)
Inductive constant : Type :=
| cbool: bool -> constant
| cnat : nat -> constant.

Global Hint Constructors constant: core.

(** * basic types *)
Inductive base_ty : Type :=
| TNat   : base_ty
| TBool  : base_ty.

Global Hint Constructors base_ty: core.

Inductive ty : Type :=
| TBase : base_ty -> ty
| TArrow : ty -> ty -> ty.

Global Hint Constructors ty: core.

Coercion TBase : base_ty >-> ty.
Coercion cbool : bool >-> constant.
Coercion cnat : nat >-> constant.

(* notation for function type: \rightbkarrow. *)
Notation " t1 '⤍' t2" := (TArrow t1 t2) (at level 18, right associativity).

(** * effectful operators (op in Fig. 4) *)
(** pure operators (e.g., [op_plus_one]) are treated as effectful operators,
  whose return value is independent of the context trace, and will not interfere
  the result of other operators. *)
Inductive effop : Type :=
| op_plus_one
| op_eq_zero
| op_rannat.

Global Hint Constructors effop: core.

(** This file defines the basic type system of λᴱ. *)

Definition ty_of_const (c: constant): base_ty :=
  match c with
  | cnat _ => TNat
  | cbool _ => TBool
  end.

Definition ret_ty_of_op (op: effop): base_ty :=
  match op with
  | op_plus_one => TNat
  | op_eq_zero => TBool
  | op_rannat => TNat
  end.

Definition ty_of_op (op: effop): ty := TNat ⤍ (ret_ty_of_op op).