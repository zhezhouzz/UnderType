From stdpp Require Import stringmap mapset.
From Stdlib Require Import Strings.String.

(** This file defines atom, i.e., variable names, and its related concepts. *)

(** We use strings as variables in the core langauge. *)
Definition atom := string.
Definition amap := stringmap.
Definition aset := stringset.

Definition atom_dec: ∀ s1 s2 : atom, {s1 = s2} + {s1 ≠ s2} := string_dec.
Definition atom_eqb: atom → atom → bool := String.eqb.
Definition atom_eqb_spec (s1 s2 : atom): reflect (s1 = s2) (atom_eqb s1 s2) := String.eqb_spec s1 s2.

(** Locally Nameless Functions: *)

Definition fv_of_set (s: aset): atom := fresh_string_of_set "x" s.
Lemma fv_of_set_fresh (s: aset) : (fv_of_set s) ∉ s.
Proof.
  apply fresh_string_of_set_fresh.
Qed.

(** This Stale class gathers all free variables in type context, values, terms,
  etc. *)
Class Stale {D} A := stale : A -> D.

#[global]
Instance atom_stale : @Stale aset atom := singleton.
Arguments atom_stale /.
#[global]
Instance aset_stale : Stale aset := id.
Arguments aset_stale /.

Notation "x # s" := (x ∉ stale s) (at level 40).

Class Subst V A := subst : atom -> V -> A -> A.

Notation "'{' x ':=' s '}' t" := (subst x s t) (at level 0).

Class Open V A := open : nat -> V -> A -> A.

Notation "'{' k '~>' v '}' e" := (open k v e) (at level 0, k constr).

Notation "e '^^' s" := (open 0 s e) (at level 20).

Class Close A := close : atom -> nat -> A -> A.

Notation "'{' x '<~' k '}' e" := (close k x e) (at level 0, k constr).

Notation "x '\\' e" := (close x 0 e) (at level 20).

Class Lc A := lc : A -> Prop.

Class Typing G E T := has_type : G -> E -> T -> Prop.

Notation "Γ '⊢' e '⋮' T" := (has_type Γ e T) (at level 20, e constr, T constr, Γ constr).

Hint Unfold open close subst stale : class_simpl.