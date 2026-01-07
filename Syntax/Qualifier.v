From stdpp Require Import mapset.
From stdpp Require Import natmap.
From stdpp Require Import fin vector.
From CT Require Import BaseDef.
From CT Require Import Syntax.Primitives.
From CT Require Import Syntax.Lang.

Import BaseDef.
Import Primitives.
Import Lang.

(** This file defines the qualifiers used in refinement types, corresponding to
  ϕ in Fig. 4. In contrast to the syntactic presentation in paper, propositions
  are encoded as shallowly embedded Coq propositions. *)

(** A qualifier is defined as a Coq proposition [prop], with closed arguments
  corresponding to the possibly open [vals]. [vals] captures the variables that
  are referred to in [prop]. We use length-indexed list [vec] to make sure
  [prop] arguments and [vals] match exactly. *)
Inductive qualifier : Type :=
| qual {n : nat} (vals : vec value n) (prop : vec constant n -> Prop).

(** For example, a qualifier may be: (with notation from stdpp)
<<
qual [# vbvar 0; vbvar 1; vfvar "x"]
   (fun v => v !!! 0 = v !!! 1 /\ v !!! 2 = cnat 1)%fin
>>

It means the first and second bound variables are equal, and the free variable
[x] is [1].
*)

(** Conjunction of two qualifiers *)
Definition qualifier_and (q1 q2 : qualifier) : qualifier :=
  match q1, q2 with
  | qual vals1 prop1, qual vals2 prop2 =>
      qual (vals1 +++ vals2)
        (fun v =>
           let (v1, v2) := Vector.splitat _ v
           in prop1 v1 /\ prop2 v2)
  end.

(** * Qualifier denotation *)

Fixpoint denote_vals {n} (vals : vec value n) : option (vec constant n) :=
  match vals with
  | [#] => Some [#]
  | x ::: v =>
      match x with
      | vconst c =>
          match denote_vals v with
          | Some v' => Some (c ::: v')
          | None => None
          end
      | _ => None
      end
  end.

(** Denote a _closed_ qualifier to a Coq proposition. The result is [False] if the
qualifier mentions functions. *)
#[global] Instance Denotation_qualifier: Denotation qualifier Prop :=
  fun ϕ =>
  match ϕ with
  | qual vals prop =>
      match denote_vals vals with
      | Some v => prop v
      | None => False
      end
  end.

Hint Unfold Denotation_qualifier: qual_class_simpl.

(** * Notations *)

Definition mk_q_bvar_eq_val n v :=
  qual [# vbvar n; v] (fun v => v !!! 0 = v !!! 1)%fin.
Definition mk_q_under_bot := qual [#] (fun _ => False).
Definition mk_q_under_top := qual [#] (fun _ => True).

Notation " 'b0:v=' v " := (mk_q_bvar_eq_val 0 v)
                            (at level 5, format "b0:v= v", v constr).
Notation " 'b0:x=' y " := (mk_q_bvar_eq_val 0 (vfvar y))
                            (at level 5, format "b0:x= y", y constr).
Notation " 'b0:c=' c " := (mk_q_bvar_eq_val 0 (vconst c))
                            (at level 5, format "b0:c= c", c constr).
Notation " 'b1:v=' v " := (mk_q_bvar_eq_val 1 v)
                            (at level 5, format "b1:v= v", v constr).
Notation " 'b1:x=' y " := (mk_q_bvar_eq_val 1 (vfvar y))
                            (at level 5, format "b1:x= y", y constr).
Notation " 'b1:c=' c " := (mk_q_bvar_eq_val 1 (vconst c))
                            (at level 5, format "b1:c= c", c constr).
Notation " ϕ1 '&' ϕ2 " := (qualifier_and ϕ1 ϕ2)
                             (at level 5, format "ϕ1  &  ϕ2").

(** * Naming related definitions and lemmas *)

(** free variables *)
Definition fv_qualifier ϕ : aset :=
  match ϕ with
  | qual vals _ => Vector.fold_right (fun v s => fv_value v ∪ s) vals ∅
  end.

#[global]
Instance qualifier_stale : Stale qualifier := fv_qualifier.
Arguments qualifier_stale /.

Definition open_qualifier (k: nat) (s: value) (ϕ: qualifier) : qualifier :=
  match ϕ with
  | qual vals prop =>
      qual (vmap (open_value k s) vals) prop
  end.

#[global]
Instance open_qualifier_with_value : Open value qualifier := open_qualifier.
Arguments open_qualifier_with_value /.

Definition subst_qualifier (x: atom) (v: value) (ϕ: qualifier) : qualifier :=
  match ϕ with
  | qual vals prop =>
      qual (vmap (subst_value x v) vals) prop
  end.

#[global]
Instance subst_qualifier_with_value : Subst value qualifier := subst_qualifier.
Arguments subst_qualifier_with_value /.

Inductive lc_qualifier : qualifier -> Prop :=
| lc_qual n vals prop :
  Vector.Forall (fun v => lc v) vals ->
  lc_qualifier (@qual n vals prop)
.

Global Hint Constructors lc_qualifier: core.

#[global]
Instance locally_closed_qualifier_instance : Lc qualifier := lc_qualifier.
Arguments locally_closed_qualifier_instance /.

(** * Well-founded relation in qualifiers *)

Notation " 'b0≺b1'" :=
  (qual [# vbvar 0; vbvar 1] (fun v => (v !!! 0) ≺ (v !!! 1))%fin)
    (at level 5).

Notation " 'b0:x≺' x " :=
  (qual [# vbvar 0; vfvar x] (fun v => (v !!! 0) ≺ (v !!! 1))%fin)
    (at level 5, x constr).

Notation " 'b0:v≺' v " :=
  (qual [# vbvar 0; v] (fun v => (v !!! 0) ≺ (v !!! 1))%fin)
    (at level 5).

Notation " 'b0:c≺' c " :=
  (qual [# vbvar 0; vconst c] (fun v => (v !!! 0) ≺ (v !!! 1))%fin)
    (at level 5).