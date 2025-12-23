From stdpp Require Import mapset.
From CT Require Import Syntax.Lang.
From CT Require Import BaseDef.
From CT Require Import Syntax.Primitives.

Import BaseDef.
Import Lang.
Import Primitives.

Definition tyctx := amap ty.
#[global]
Instance tyctx_stale : Stale tyctx := dom.
Arguments tyctx_stale /.

(** Basic typing rules  *)
Inductive tm_has_type : tyctx -> tm -> ty -> Prop :=
| BtErr: forall Γ T, tm_has_type Γ (terr T) T
| BtValue : forall Γ v T, value_has_type Γ v T -> tm_has_type Γ (treturn v) T
| BtLetE : forall Γ e1 e2 T1 T2 (L: aset),
    tm_has_type Γ e1 T1 ->
    (forall (x: atom), x ∉ L -> tm_has_type (<[ x := T1]> Γ) (e2 ^^ (vfvar x)) T2) ->
    tm_has_type Γ (tlete e1 e2) T2
| BtEffOp : forall Γ (op: effop) v1 e (T1 Tx: base_ty) T (L: aset),
    value_has_type Γ v1 T1 ->
    (ty_of_op op) = T1 ⤍ Tx ->
    (forall (x: atom), x ∉ L -> tm_has_type (<[x := TBase Tx]> Γ) (e ^^ (vfvar x)) T) ->
    tm_has_type Γ (tleteffop op v1 e) T
| BtApp : forall Γ v1 v2 e T1 Tx T (L: aset),
    value_has_type Γ v1 (T1 ⤍ Tx) ->
    value_has_type Γ v2 T1 ->
    (forall (x: atom), x ∉ L -> tm_has_type (<[x := Tx]> Γ) (e ^^ (vfvar x)) T) ->
    tm_has_type Γ (tletapp v1 v2 e) T
| BtMatchb: forall Γ v e1 e2 T,
    value_has_type Γ v TBool ->
    tm_has_type Γ e1 T ->
    tm_has_type Γ e2 T ->
    tm_has_type Γ (tmatchb v e1 e2) T
with value_has_type : tyctx -> value -> ty -> Prop :=
| BtConst : forall Γ (c: constant), value_has_type Γ (vconst c) (ty_of_const c)
| BtVar : forall Γ (x: atom) T,
    Γ !! x = Some T -> value_has_type Γ (vfvar x) T
| BtFun : forall Γ Tx T e (L: aset),
    (forall (x: atom), x ∉ L -> tm_has_type (<[x := Tx]> Γ) (e ^^ (vfvar x)) T) ->
    value_has_type Γ (vlam Tx e) (Tx ⤍ T)
| BtFix : forall Γ (Tx: base_ty) T e (L: aset),
    (forall (x: atom), x ∉ L -> value_has_type (<[x := TBase Tx]>Γ) (vlam (Tx ⤍ T) e ^^ (vfvar x)) ((Tx ⤍ T) ⤍ T)) ->
    value_has_type Γ (vfix (Tx ⤍ T) (treturn (vlam (Tx ⤍ T) e))) (Tx ⤍ T).

Scheme value_has_type_mutual_rec := Induction for value_has_type Sort Prop
    with tm_has_type_mutual_rec := Induction for tm_has_type Sort Prop.

Global Hint Constructors tm_has_type: core.
Global Hint Constructors value_has_type: core.

#[global]
Instance has_normal_type_tm_instance : Typing tyctx tm ty := tm_has_type.
Arguments has_normal_type_tm_instance /.

#[global]
Instance has_normal_type_value_instance : Typing tyctx value ty := value_has_type.
Arguments has_normal_type_value_instance /.