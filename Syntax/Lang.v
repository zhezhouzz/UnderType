From CT Require Import BaseDef.
From CT Require Import Syntax.Primitives.
From stdpp Require Import stringmap mapset.

(** * This file defines the core language. *)

Inductive value : Type :=
| vconst (c: constant)
| vfvar (atom: atom)
| vbvar (bn: nat)
| vlam (T: ty) (e: tm)
| vfix (Tf: ty) (e: tm)
(** expressions (computations) (e in Fig. 2) *)
with tm : Type :=
(* We explicitly connect values and expressions (computation) using a standard
return syntax, while in the paper values are implicitly expressions. *)
| terr (ty: ty)
| treturn (v: value)
| tlete (e1: tm) (e2: tm)
| tleteffop (op: effop) (v1: value) (e: tm)
| tletapp (v1: value) (v2: value) (e: tm)
| tmatchb (v: value) (e1: tm) (e2: tm).

Scheme value_mutual_rec := Induction for value Sort Type
    with tm_mutual_rec := Induction for tm Sort Type.

Coercion vconst : constant >-> value.
Coercion vfvar : atom >-> value.
Coercion treturn : value >-> tm.

(** * Locally nameless representation related definitions *)

(** open *)
Fixpoint open_value (k : nat) (s : value) (v : value): value :=
  match v with
  | vconst _ => v
  | vfvar _ => v
  | vbvar n => if decide (k = n) then s else v
  | vlam T e => vlam T (open_tm (S k) s e)
  | vfix Tf e => vfix Tf (open_tm (S k) s e)
  end
with open_tm (k : nat) (s : value) (e : tm): tm :=
       match e with
       | terr ty => terr ty
       | treturn v => treturn (open_value k s v)
       | tlete e1 e2 => tlete (open_tm k s e1) (open_tm (S k) s e2)
       | tletapp v1 v2 e =>
           tletapp (open_value k s v1) (open_value k s v2) (open_tm (S k) s e)
       | tleteffop op v1 e =>
           tleteffop op (open_value k s v1) (open_tm (S k) s e)
       | tmatchb v e1 e2 => tmatchb (open_value k s v) (open_tm k s e1) (open_tm k s e2)
       end.

(* Instances for the generic [Open] class.  We want to be able to open both
   with a value (the locally nameless payload) and directly with an atom,
   which gets coerced to a value via [vfvar]. *)

(* Opening values/terms with a value *)
#[global]
Instance open_value_with_value : Open value value := open_value.
Arguments open_value_with_value /.

#[global]
Instance open_tm_with_value : Open value tm := open_tm.
Arguments open_tm_with_value /.

(* Opening values/terms with an atom binder (used in [lc] definitions) *)
#[global]
Instance open_value_with_atom : Open atom value :=
  fun k (a : atom) (v : value) => open_value k (vfvar a) v.
Arguments open_value_with_atom /.

#[global]
Instance open_tm_with_atom : Open atom tm :=
  fun k (a : atom) (e : tm) => open_tm k (vfvar a) e.
Arguments open_tm_with_atom /.

(** close *)
Fixpoint close_value (x : atom) (s : nat) (v : value): value :=
  match v with
  | vconst _ => v
  | vfvar y => if decide (x = y) then vbvar s else v
  | vbvar _ => v
  | vlam T e => vlam T (close_tm x (S s) e)
  | vfix Tf e => vfix Tf (close_tm x (S s) e)
  end
with close_tm (x : atom) (s : nat) (e : tm): tm :=
       match e with
       | terr ty => terr ty
       | treturn v => treturn (close_value x s v)
       | tlete e1 e2 => tlete (close_tm x s e1) (close_tm x (S s) e2)
       | tletapp v1 v2 e =>
           tletapp (close_value x s v1) (close_value x s v2) (close_tm x (S s) e)
       | tleteffop op v1 e =>
           tleteffop op (close_value x s v1) (close_tm x (S s) e)
       | tmatchb v e1 e2 =>
           tmatchb (close_value x s v) (close_tm x s e1) (close_tm x s e2)
       end.

#[global]
Instance close_value_instance : Close value := close_value.
Arguments close_value_instance /.

#[global]
Instance close_tm_instance : Close tm := close_tm.
Arguments close_tm_instance /.

(** locally closed *)
(* TODO: define lc mutually recursively *)

Inductive lc_value: tm -> Prop :=
  | lc_vconst: forall (c: constant), lc_value c
  | lc_vfvar: forall (a: atom), lc_value (vfvar a)
  | lc_vbvar: forall (n: nat), lc_value (vbvar n)
  | lc_vlam: forall T e (L: aset), (forall (x: atom), x ∉ L -> lc_value (e ^^ x)) -> lc_value (vlam T e)
  | lc_vfix: forall Tf e (L: aset),
      (forall (f:atom), f ∉ L -> lc_value ({0 ~> f} e)) -> lc_value (vfix Tf e)
with lc_tm: tm -> Prop :=
  | lc_terr: forall (t: ty), lc_tm (terr t)
  | lc_tlete: forall (e1 e2: tm) (L: aset),
    lc_value e1 -> (forall (x: atom), x ∉ L -> lc_tm (e2 ^^ x)) -> lc_tm (tlete e1 e2)
  | lc_tletapp: forall (v1 v2: value) e (L: aset),
    lc_value v1 -> lc_value v2 -> (forall (x: atom), x ∉ L -> lc_tm (e ^^ x)) -> lc_tm (tletapp v1 v2 e)
  | lc_tleteffop: forall op (v1: value) e (L: aset),
    lc_value v1 -> (forall (x: atom), x ∉ L -> lc_tm (e ^^ x)) -> lc_tm (tleteffop op v1 e)
  | lc_tmatchb: forall (v: value) e1 e2, lc_value v -> lc_tm e1 -> lc_tm e2 -> lc_tm (tmatchb v e1 e2).

Global Hint Constructors lc_value lc_tm: core.

#[global]
Instance locally_closed_value_instance : Lc value := lc_value.
Arguments locally_closed_value_instance /.

#[global]
Instance locally_closed_tm_instance : Lc tm := lc_tm.
Arguments locally_closed_tm_instance /.

(** free variables *)
Fixpoint fv_value (v : value): aset :=
  match v with
  | vconst _ => ∅
  | vfvar y => {[ y ]}
  | vbvar _ => ∅
  | vlam T e => fv_tm e
  | vfix Tf e => fv_tm e
  end
with fv_tm (e : tm): aset :=
       match e with
       | terr _ => ∅
       | treturn v => fv_value v
       | tlete e1 e2 => (fv_tm e1) ∪ (fv_tm e2)
       | tletapp v1 v2 e => (fv_value v1) ∪ (fv_value v2) ∪ (fv_tm e)
       | tleteffop op v1 e => (fv_value v1) ∪ (fv_tm e)
       | tmatchb v e1 e2 => (fv_value v) ∪ (fv_tm e1) ∪ (fv_tm e2)
       end.

#[global]
Instance stale_value_instance : @Stale aset value := fv_value.
Arguments stale_value_instance /.

#[global]
Instance stale_tm_instance : @Stale aset tm := fv_tm.
Arguments stale_tm_instance /.

Definition closed_value (v: value) := fv_value v ≡ ∅.
Definition closed_tm (e: tm) := fv_tm e ≡ ∅.

Definition body (e: tm) := exists (L: aset), forall (x: atom), x ∉ L -> lc (e ^^ x).

(** substitution *)
Fixpoint value_subst (x : atom) (s : value) (v : value): value :=
  match v with
  | vconst _ => v
  | vfvar y => if decide (x = y) then s else v
  | vbvar _ => v
  | vlam T e => vlam T (tm_subst x s e)
  | vfix Tf e => vfix Tf (tm_subst x s e)
  end
with tm_subst (x : atom) (s : value) (e : tm): tm :=
       match e with
       | terr ty => terr ty
       | treturn v => treturn (value_subst x s v)
       | tlete e1 e2 => tlete (tm_subst x s e1) (tm_subst x s e2)
       | tletapp v1 v2 e => tletapp (value_subst x s v1) (value_subst x s v2) (tm_subst x s e)
       | tleteffop op v1 e => tleteffop op (value_subst x s v1) (tm_subst x s e)
       | tmatchb v e1 e2 => tmatchb (value_subst x s v) (tm_subst x s e1) (tm_subst x s e2)
       end.

#[global]
Instance subst_value_with_value : Subst value value := value_subst.
Arguments subst_value_with_value /.

#[global]
Instance subst_tm_with_value : Subst value tm := tm_subst.
Arguments open_tm_with_value /.

#[global]
Instance subst_value_with_atom : Subst atom value :=
  fun x (a : atom) (v : value) => value_subst x (vfvar a) v.
Arguments subst_value_with_atom /.

#[global]
Instance subst_tm_with_atom : Subst atom tm :=
  fun k (a : atom) (e : tm) => tm_subst k (vfvar a) e.
Arguments subst_tm_with_atom /.

(* Syntax Suger *)
Definition mk_app (e: tm) (v: tm) :=
  tlete e (tlete v (tletapp (vbvar 1) (vbvar 0) (vbvar 0))).


(* Well-founded constraint of base type for fixed point. *)
Definition constant_measure (c : constant) :=
match c with
| cnat n => n
| cbool b => Nat.b2n b
end.

Definition constant_lt := ltof _ constant_measure.

Notation " a '≺' b " := (constant_lt a b) (at level 20, a constr, b constr).

Lemma constant_lt_well_founded : well_founded constant_lt.
Proof.
apply well_founded_ltof.
Qed.