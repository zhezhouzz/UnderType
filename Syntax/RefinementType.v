Require Import Stdlib.Program.Wf.
From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import ListCtx.
From CT Require Import Syntax.Qualifier.

Import BaseDef.
Import Lang.
Import Tactics.
Import Primitives.
(* Import OperationalSemantics. *)
(* Import BasicTyping. *)
Import Qualifier.
Import ListCtx.
Import List.

(** Refinement types (t in Fig. 4) *)
Inductive rty : Type :=
| rtyOver (b: base_ty) (ϕ: qualifier)
| rtyUnder (b: base_ty) (ϕ: qualifier)
| rtyArr (ρ: rty) (τ: rty).

Global Hint Constructors rty: core.

Notation "'{:' b '|' ϕ '}'" := (rtyOver b ϕ) (at level 5, format "{: b | ϕ }", b constr, ϕ constr).
Notation "'[:' b '|' ϕ ']' " := (rtyUnder b ϕ) (at level 5, format "[: b | ϕ ]", b constr, ϕ constr).
Notation "ρ '⇨' τ" :=
  (rtyArr ρ τ) (at level 80, format "ρ ⇨ τ", right associativity, ρ constr, τ constr).

(* NOTE: \rightwhitearrow: ⇨ *)

Definition is_under_base_rty (τ: rty) :=
  match τ with
  | [: _ | _ ] => False
  | _ => True
  end.

Definition is_over_base_rty (τ: rty) :=
  match τ with
  | {: _ | _ } => False
  | _ => True
  end.

(* This measure function is used to guarantee termination of the denotation.
Instead of addtion, we can also use [max] for the subterms. *)
Fixpoint rty_measure (ρ: rty) : nat :=
  match ρ with
  | rtyOver _ _ | rtyUnder _ _ => 1
  | ρ ⇨ τ => 1 + rty_measure ρ + rty_measure τ
  end.

Inductive is_coverage_rty: rty -> Prop :=
| is_coverage_rty_base: forall b ϕ, is_coverage_rty [:b|ϕ]
| is_coverage_rty_over_arr: forall b ϕ τ,
    is_coverage_rty τ -> is_coverage_rty ({:b|ϕ} ⇨ τ)
| is_coverage_rty_under_arr: forall b ϕ τ,
    is_coverage_rty τ -> is_coverage_rty ([:b|ϕ] ⇨ τ)
| is_coverage_rty_arr_arr: forall ρ1 ρ2 τ,
    is_coverage_rty (ρ1 ⇨ ρ2) -> is_coverage_rty τ -> is_coverage_rty ((ρ1 ⇨ ρ2) ⇨ τ).

Global Hint Constructors is_coverage_rty: core.

Definition fine_rty (τ: rty) :=
  match τ with
  | {: _ | _ } => True
  | [: _ | _ ] => True
  | _ => is_coverage_rty τ
  end.

Definition flip_rty (τ: rty) :=
  match τ with
  | [: b | ϕ ] => {: b | ϕ }
  | {: b | ϕ } => [: b | ϕ ]
  | ρ ⇨ τ => ρ ⇨ τ
  end.

(** Type erasure (Fig. 5) *)

Fixpoint erase_rty ρ : ty :=
  match ρ with
  | {: b | ϕ } => b
  | [: b | ϕ ] => b
  | ρ ⇨ τ => (erase_rty ρ) ⤍ (erase_rty τ)
  end.

Notation " '⌊' ty '⌋' " := (erase_rty ty) (at level 5, format "⌊ ty ⌋", ty constr).

Definition erase_ctx (Γ: listctx rty) :=
  ⋃ ((List.map (fun e => {[e.1 := erase_rty e.2]}) Γ): list (amap ty)).

Notation " '⌊' Γ '⌋*' " := (erase_ctx Γ) (at level 5, format "⌊ Γ ⌋*", Γ constr).

(** * Naming related definitions *)

Fixpoint fv_rty ρ : aset :=
  match ρ with
  | {: _ | ϕ } => fv_qualifier ϕ
  | [: _ | ϕ ] => fv_qualifier ϕ
  | ρ ⇨ τ => fv_rty ρ ∪ fv_rty τ
  end.

#[global]
  Instance rty_stale : Stale rty := fv_rty.
Arguments rty_stale /.

Fixpoint open_rty (k: nat) (s: value) (ρ: rty) : rty :=
  match ρ with
  | {: b | ϕ } => {: b | open_qualifier (S k) s ϕ }
  | [: b | ϕ ] => [: b | open_qualifier (S k) s ϕ ]
  | ρ ⇨ τ => (open_rty k s ρ) ⇨ (open_rty (S k) s τ)
  end.

#[global]
Instance open_rty_with_value : Open value rty := open_rty.
Arguments open_rty_with_value /.

Fixpoint subst_rty (k: atom) (s: value) (ρ: rty) : rty :=
  match ρ with
  | {: b | ϕ} => {: b | subst_qualifier k s ϕ}
  | [: b | ϕ] => [: b | subst_qualifier k s ϕ]
  | ρ ⇨ τ => (subst_rty k s ρ) ⇨ (subst_rty k s τ)
  end.

#[global]
Instance subst_rty_with_value : Subst value rty := subst_rty.
Arguments subst_rty_with_value /.

(** Local closure *)
(** NOTE: To alaign with denotation, we assume the function type doesn't appear in transduce. *)
(** NOTE: all (L: aset) should be the first hypothesis. *)
Inductive lc_rty : rty -> Prop :=
| lc_rtyOver: forall b ϕ, body ϕ -> fine_rty {: b | ϕ} -> lc_rty {: b | ϕ}
| lc_rtyUnder: forall b ϕ, body ϕ -> fine_rty [: b | ϕ] -> lc_rty [: b | ϕ]
| lc_rtyArr: forall ρ τ (L : aset),
    (forall x : atom, x ∉ L -> lc_rty (τ ^^ (vfvar x))) ->
    fine_rty (ρ ⇨ τ) -> lc_rty ρ ->
    lc_rty (ρ ⇨ τ).

Global Hint Constructors lc_rty: core.

#[global]
Instance locally_closed_rty_instance : Lc rty := lc_rty.
Arguments locally_closed_rty_instance /.
    
Lemma lc_rty_fine: forall τ, lc τ -> fine_rty τ.
Proof.
  induction 1; eauto.
Qed.

(** Closed under free variable set *)

(* Inductive closed_rty (d : aset) (ρ: rty): Prop :=
| closed_rty_: lc ρ -> stale ρ ⊆ d -> closed_rty d ρ.

Lemma closed_rty_fine: forall d τ, closed_rty d τ -> fine_rty τ.
Proof.
  pose lc_rty_fine.
  induction 1; eauto.
Qed. *)

(** Well-formedness of type context. All terms and types are alpha-converted to
  have unique names.
  all rty in ctx are pure.
 *)
Inductive ok_ctx: listctx rty -> Prop :=
| ok_ctx_nil: ok_ctx []
| ok_ctx_cons: forall (Γ: listctx rty)(x: atom) (ρ: rty),
    ok_ctx Γ ->
    lc ρ ->
    stale ρ ⊆ stale Γ ->
    fine_rty ρ ->
    x ∉ stale Γ ->
    ok_ctx (Γ ++ [(x, ρ)]).

Lemma ok_ctx_regular Γ:
  ok_ctx Γ -> ok Γ /\ (forall x ρ, ctxfind Γ x = Some ρ -> fine_rty ρ /\ lc ρ /\ stale ρ ⊆ stale Γ /\ x # ρ).
Proof.
  induction 1; intuition; simpl in *; eauto; try hauto.
  - destruct (atom_dec x x0); subst.
    + rewrite ctxfind_last_eq in H6 by auto. hauto.
    + rewrite ctxfind_last_neq in H6 by auto. set_solver. 
  - destruct (atom_dec x x0); subst.
    + rewrite ctxfind_last_eq in H6 by auto. hauto.
    + rewrite ctxfind_last_neq in H6 by auto. set_solver.
  - destruct (atom_dec x x0); subst.
    + rewrite ctxfind_last_eq in H6 by auto. simp_hyps.
      intros; subst.
      autounfold with class_simpl in *.
      listctx_set_simpl. MyTactics.my_set_solver. 
    + rewrite ctxfind_last_neq in H6 by auto.
      apply H5 in H6.
      autounfold with class_simpl in *.
      listctx_set_simpl.
      MyTactics.my_set_solver. 
  - destruct (atom_dec x x0); subst.
    + rewrite ctxfind_last_eq in H6 by auto. hauto.
    + rewrite ctxfind_last_neq in H6 by auto. set_solver.
Qed.

(** Shorthands, used in typing rules *)
Definition mk_eq_constant c := [: ty_of_const c | b0:c= c ].
Definition mk_eq_constant_over c := {: ty_of_const c | b0:c= c }.
Definition mk_bot ty := [: ty | mk_q_under_bot ].
Definition mk_top ty := [: ty | mk_q_under_top ].
Definition mk_eq_var ty (x: atom) := [: ty | b0:x= x ].

Lemma empty_closed_rty_stale: forall τ, stale τ ⊆ ∅ -> stale τ = ∅.
Proof.
  intros. set_solver.
Qed.

Global Hint Resolve empty_closed_rty_stale: core.
Global Hint Resolve lc_rty_fine: core.