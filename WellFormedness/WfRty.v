Require Import Stdlib.Program.Wf.
From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import Syntax.RefinementType.

Import BaseDef.
Import Lang.
Import Tactics.
Import Primitives.
(* Import OperationalSemantics. *)
(* Import BasicTyping. *)
Import Qualifier.
Import ListCtx.
Import List.

Lemma ok_ctx_ok: forall Γ, ok_ctx Γ -> ok Γ.
Proof.
  induction 1; eauto.
Qed.

Lemma is_over_base_open_rty: forall τ k (v_x: value), is_over_base_rty ({ k ~> v_x} τ) <-> is_over_base_rty τ.
Proof.
  split; induction τ; simpl; intros; inversion H; subst; eauto.
Qed.

Lemma is_over_base_rty_subst: forall τ x (v_x: value), is_over_base_rty ({ x := v_x} τ) <-> is_over_base_rty τ.
Proof.
  split; induction τ; simpl; intros; inversion H; subst; eauto.
Qed.

Lemma is_under_base_open_rty: forall τ k (v_x: value), is_under_base_rty ({ k ~> v_x} τ) <-> is_under_base_rty τ.
Proof.
  split; induction τ; simpl; intros; inversion H; subst; eauto.
Qed.

Lemma is_under_base_rty_subst: forall τ x (v_x: value), is_under_base_rty ({ x := v_x} τ) <-> is_under_base_rty τ.
Proof.
  split; induction τ; simpl; intros; inversion H; subst; eauto.
Qed.

Lemma rty_measure_gt_0 ρ : rty_measure ρ > 0.
Proof.
  induction ρ; simpl; lia.
Qed.

Lemma rty_measure_S ρ : exists n, rty_measure ρ = S n.
Proof.
  destruct (Nat.lt_exists_pred 0 (rty_measure ρ)).
  pose proof (rty_measure_gt_0 ρ). lia.
  intuition eauto.
Qed.

Lemma open_preserves_rty_measure ρ: forall k t,
    rty_measure ρ = rty_measure ({k ~> t} ρ).
Proof.
  induction ρ; simpl; eauto.
Qed.

Lemma subst_preserves_rty_measure ρ: forall x t,
    rty_measure ρ = rty_measure ({x:=t} ρ).
Proof.
  induction ρ; simpl; eauto.
Qed.

Lemma is_coverage_open_rty_aux n: forall τ, rty_measure τ <= n -> forall k (v_x: value), is_coverage_rty ({ k ~> v_x} τ) <-> is_coverage_rty τ.
Proof.
  induction n; split; intros HH.
  - destruct τ; sinvert H.
  - destruct τ; sinvert H.
  - destruct τ.
    + sinvert HH; eauto.
    + sinvert HH; eauto.
    + destruct τ1; sinvert HH; eauto; econstructor; rewrite <- IHn; eauto; simpl in *; lia.
  - destruct τ.
    + sinvert HH; eauto.
    + simpl. eauto.
    + destruct τ1; sinvert HH; eauto; simpl; econstructor; try solve [rewrite IHn; eauto; simpl in *; lia].
      * rewrite <- IHn in H2; eauto; simpl in *; lia.
Qed.

Lemma is_coverage_open_rty: forall τ, forall k (v_x: value), is_coverage_rty ({ k ~> v_x} τ) <-> is_coverage_rty τ.
Proof. eauto using is_coverage_open_rty_aux. Qed.

Lemma is_coverage_rty_subst_aux n: forall τ, rty_measure τ <= n -> forall x (v_x: value), is_coverage_rty ({ x := v_x} τ) <-> is_coverage_rty τ.
Proof.
  induction n; split; intros HH.
  - destruct τ; sinvert H.
  - destruct τ; sinvert H.
  - destruct τ.
    + sinvert HH; eauto.
    + sinvert HH; eauto.
    + destruct τ1; sinvert HH; eauto; econstructor; rewrite <- IHn; eauto; simpl in *; lia.
  - destruct τ.
    + sinvert HH; eauto.
    + simpl. eauto.
    + destruct τ1; sinvert HH; eauto; simpl; econstructor; try solve [rewrite IHn; eauto; simpl in *; lia].
      * rewrite <- IHn in H2; eauto; simpl in *; lia.
Qed.

Lemma is_coverage_rty_subst: forall τ x (v_x: value), is_coverage_rty ({ x := v_x} τ) <-> is_coverage_rty τ.
Proof. eauto using is_coverage_rty_subst_aux. Qed.

Lemma open_rty_arr_rev: forall ρ τ k v, (({k ~> v} ρ) ⇨ ({S k ~> v} τ)) = {k ~> v} (ρ ⇨ τ).
Proof. eauto. Qed.

Lemma rty_subst_arr_rev: forall ρ τ x v, (({x := v} ρ) ⇨ ({x := v} τ)) = {x := v} (ρ ⇨ τ).
Proof. eauto. Qed.

Ltac fine_rty_aux_simp_aux :=
  match goal with
  | [H: context [ (({?k ~> ?v} _) ⇨ ({S ?k ~> ?v} _)) ] |- _ ] =>
      setoid_rewrite open_rty_arr_rev in H
  | [H: context [ (({?x := ?v} _) ⇨ ({?x := ?v} _)) ] |- _ ] =>
      setoid_rewrite rty_subst_arr_rev in H
  | [H: _ |- context [ (({?k ~> ?v} _) ⇨ ({S ?k ~> ?v} _)) ]] =>
      setoid_rewrite open_rty_arr_rev
  | [H: _ |- context [ (({?x := ?v} _) ⇨ ({?x := ?v} _)) ] ] =>
      setoid_rewrite rty_subst_arr_rev
  | [H: context [ is_over_base_rty ({_ ~> _} ?τ) ] |- _ ] => setoid_rewrite is_over_base_open_rty in H
  | [H: context [ is_over_base_rty ({_ := _} ?τ) ] |- _ ] => setoid_rewrite is_over_base_rty_subst in H
  | [H: _ |- context [ is_over_base_rty ({_ ~> _} ?τ) ] ] => setoid_rewrite is_over_base_open_rty
  | [H: _ |- context [ is_over_base_rty ({_ := _} ?τ) ] ] => setoid_rewrite is_over_base_rty_subst
  | [H: context [ is_under_base_rty ({_ ~> _} ?τ) ] |- _ ] => setoid_rewrite is_under_base_open_rty in H
  | [H: context [ is_under_base_rty ({_ := _} ?τ) ] |- _ ] => setoid_rewrite is_under_base_rty_subst in H
  | [H: _ |- context [ is_under_base_rty ({_ ~> _} ?τ) ] ] => setoid_rewrite is_under_base_open_rty
  | [H: _ |- context [ is_under_base_rty ({_ := _} ?τ) ] ] => setoid_rewrite is_under_base_rty_subst
  | [H: context [ is_coverage_rty ({_ ~> _} ?τ) ] |- _ ] => setoid_rewrite is_coverage_open_rty in H
  | [H: context [ is_coverage_rty ({_ := _} ?τ) ] |- _ ] => setoid_rewrite is_coverage_rty_subst in H
  | [H: _ |- context [ is_coverage_rty ({_ ~> _} ?τ) ] ] => setoid_rewrite is_coverage_open_rty
  | [H: _ |- context [ is_coverage_rty ({_ := _} ?τ) ] ] => setoid_rewrite is_coverage_rty_subst
  end.

Lemma fine_open_rty τ: forall k (v_x: value), fine_rty ({ k ~> v_x} τ) <-> fine_rty τ.
Proof.
  split; intros; destruct τ; simpl in *; repeat fine_rty_aux_simp_aux; eauto.
Qed.

Lemma fine_rty_subst: forall τ x (v_x: value), fine_rty ({ x := v_x} τ) <-> fine_rty τ.
Proof.
  split; intros; destruct τ; simpl in *; repeat fine_rty_aux_simp_aux; eauto.
Qed.

Ltac fine_rty_simp_aux :=
  match goal with
  | [H: context [ (({?k ~> ?v} _) ⇨ ({S ?k ~> ?v} _)) ] |- _ ] =>
      setoid_rewrite open_rty_arr_rev in H
  | [H: context [ (({?x := ?v} _) ⇨ ({?x := ?v} _)) ] |- _ ] =>
      setoid_rewrite rty_subst_arr_rev in H
  | [H: _ |- context [ (({?k ~> ?v} _) ⇨ ({S ?k ~> ?v} _)) ]] =>
      setoid_rewrite open_rty_arr_rev
  | [H: _ |- context [ (({?x := ?v} _) ⇨ ({?x := ?v} _)) ] ] =>
      setoid_rewrite rty_subst_arr_rev
  | [H: context [ fine_rty ({_ ~> _} ?τ) ] |- _ ] => setoid_rewrite fine_open_rty in H
  | [H: context [ fine_rty ({_ := _} ?τ) ] |- _ ] => setoid_rewrite fine_rty_subst in H
  | [H: _ |- context [ fine_rty ({_ ~> _} ?τ) ] ] => setoid_rewrite fine_open_rty
  | [H: _ |- context [ fine_rty ({_ := _} ?τ) ] ] => setoid_rewrite fine_rty_subst
  | _ => fine_rty_aux_simp_aux
  end.

Lemma lc_rty_under_base_q: forall b ϕ, lc_rty ([:b|ϕ]) <-> lc_phi1 ϕ.
Proof.
  split; intros; sinvert H; eauto.
  econstructor; eauto. exists x. eauto. simpl; eauto.
Qed.

Lemma lc_rty_over_base_q: forall b ϕ, lc_rty ({:b|ϕ}) <-> lc_phi1 ϕ.
Proof.
  split; intros; sinvert H; eauto.
  econstructor; eauto. exists x. eauto. simpl; eauto.
Qed.

Lemma lc_rty_base_flip: forall b ϕ, lc_rty {:b|ϕ} <-> lc_rty [:b|ϕ].
Proof.
  split; intros; sinvert H; econstructor; eauto.
Qed.

Lemma closed_rty_base_flip: forall L b ϕ, closed_rty L {:b|ϕ} <-> closed_rty L [:b|ϕ].
Proof.
  split; intros; sinvert H; econstructor; eauto;
  rewrite lc_rty_base_flip in *; eauto.
Qed.

Lemma lc_rty_arr: forall ρ τ, lc_rty (ρ ⇨ τ) <-> fine_rty (ρ ⇨ τ) /\ lc_rty ρ /\ body_rty τ.
Proof.
  split; intros; sinvert H.
  - intuition. auto_exists_L.
  - unfold body_rty in H1. simp_hyps. auto_exists_L; eauto.
Qed.

Lemma closed_rty_arr:
  ∀ (L : aset) (ρ τ : rty),
    closed_rty L (ρ⇨τ) ↔ (fine_rty (ρ⇨τ)) /\ closed_rty L ρ ∧ body_rty τ /\ (rty_fv τ ⊆ L).
Proof.
  split; intros.
  - sinvert H. rewrite lc_rty_arr in H0. intuition.
    + econstructor; eauto. my_set_solver.
    + my_set_solver.
  - simp_hyps. sinvert H1. econstructor; eauto.
    + rewrite lc_rty_arr. intuition.
    + my_set_solver.
Qed.

Ltac fine_rty_simp := simpl in *; repeat fine_rty_simp_aux.

Ltac fine_rty_solver := fine_rty_simp; eauto.
