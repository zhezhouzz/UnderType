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

From stdpp Require Import gmap.
Definition restrict_keys {V} (s : aset) (m : amap V) : amap V :=
  filter (λ kx : atom * V, kx.1 ∈ s) m.

Definition restrict_keys_compl {V} (s : aset) (m : amap V) : amap V :=
filter (λ kx : atom * V, kx.1 ∉ s) m.

Lemma restrict_keys_union_compl {V} (s : aset) (m : amap V) :
  restrict_keys s m ∪ restrict_keys_compl s m = m.
Proof.
  unfold restrict_keys, restrict_keys_compl.
  rewrite (map_filter_union_complement (λ kx : atom * V, kx.1 ∈ s) m).
  reflexivity.
Qed.

Lemma restrict_keys_split {V} (s : aset) (m : amap V) :
  m = restrict_keys s m ∪ restrict_keys_compl s m.
Proof. symmetry; apply restrict_keys_union_compl. Qed.

Lemma dom_restrict_keys {V} (s : aset) (m : amap V) :
  dom (restrict_keys s m) ≡ dom m ∩ s.
Proof.
  unfold restrict_keys.
  eapply (dom_filter (K:=atom) (M:=amap) (D:=aset) (A:=V)
           ).
  intro i. split.
  - intros H.
    assert (i ∈ dom m) as Hs by set_solver.
    rewrite elem_of_dom in Hs. destruct Hs as [x Hlookup].
    exists x. split; eauto. set_solver.
  - intros (x & Hdom & Hs).
    assert (is_Some (m !! i)) as HSome by eauto.
    rewrite <- elem_of_dom in HSome.
    set_solver.
Qed.

Lemma dom_restrict_keys_compl {V} (s : aset) (m : amap V) :
  dom (restrict_keys_compl s m) ≡ dom m ∖ s.
Proof.
  unfold restrict_keys_compl.
  eapply (dom_filter (K:=atom) (M:=amap) (D:=aset) (A:=V)).
  intro i. split.
  - intros Hdom.
    assert (i ∈ dom m) as Hs by set_solver.
    rewrite elem_of_dom in Hs. destruct Hs as [x Hlookup].
    exists x. split; eauto. set_solver.
  - intros (x & Hdom & Hs).
    assert (is_Some (m !! i)) as HSome by eauto.
    rewrite <- elem_of_dom in HSome.
    set_solver.
Qed.

Notation " '[D' s ']' " := (restrict_keys s) (at level 20, format "[D s ]", s constr).
Notation " '[D~' s ']' " := (restrict_keys_compl s) (at level 20, format "[D~ s ]", s constr).

(** Locally Nameless Functions: *)

Definition fv_of_set (s: aset): atom := fresh_string_of_set "x" s.
Lemma fv_of_set_fresh (s: aset) : (fv_of_set s) ∉ s.
Proof.
  apply fresh_string_of_set_fresh.
Qed.

(** This Stale class gathers all free variables in type context, values, terms,
  etc. *)
Class Stale A := stale : A -> aset.

#[global]
Instance atom_stale : Stale atom := singleton.
Arguments atom_stale /.
#[global]
Instance aset_stale : Stale aset := id.
Arguments aset_stale /.
#[global]
Instance amap_stale {A} : Stale (amap A) := dom.
Arguments amap_stale /.

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

Class Denotation (A: Type) (B: Type) := denote: A -> B.

Notation "'⟦' τ '⟧' " := (denote τ) (at level 20, format "⟦ τ ⟧", τ constr).

Hint Unfold open close subst stale lc has_type denote amap_stale: class_simpl.

Lemma stale_restrict_keys_ {V} (s : aset) (m : amap V) :
  stale (restrict_keys s m) ≡ stale m ∩ s.
Proof.
  unfold stale, amap_stale.
  rewrite dom_restrict_keys. eauto.
Qed.

Lemma stale_restrict_keys_compl_ {V} (s : aset) (m : amap V) :
  stale (restrict_keys_compl s m) ≡ stale m ∖ s.
Proof.
  unfold stale, amap_stale.
  rewrite dom_restrict_keys_compl. eauto.
Qed.

Lemma stale_restrict_keys {V} (s : aset) (m : amap V) :
  stale (restrict_keys s m) = stale m ∩ s.
Proof.
  apply leibniz_equiv.
  rewrite stale_restrict_keys_. set_solver.
Qed.

Lemma stale_restrict_keys_compl {V} (s : aset) (m : amap V) :
  stale (restrict_keys_compl s m) = stale m ∖ s.
Proof.
  apply leibniz_equiv.
  rewrite stale_restrict_keys_compl_. set_solver.
Qed.