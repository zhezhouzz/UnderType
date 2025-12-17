From stdpp Require Import mapset.
From stdpp Require Import natmap.
From stdpp Require Import fin vector.
From Stdlib Require Classical_Prop.
From CT.Syntax Require Import Syntax.
From CT.LocallyNameless Require Import LangLc.
From CT.LocallyNameless Require Import QualifierLc.

Import BaseDef.
Import Lang.
Import Primitives.
Import Qualifier.
Import MyTactics.
Import ListCtx.
Import List.
Import RefinementType.
Import LangLc.
Import QualifierLc.

(** * Naming properties of refinement type syntax *)

(** * erase *)

Lemma rty_erase_open_eq τ : forall k s, ⌊τ⌋ = ⌊{k ~> s} τ⌋.
Proof.
  induction τ; intros; simpl; eauto; f_equal; eauto.
Qed.

Lemma rty_erase_subst_eq ρ x s : ⌊ρ⌋ = ⌊{x := s} ρ⌋.
Proof.
  induction ρ; simpl; eauto; f_equal; eauto.
Qed.

Lemma ctx_erase_lookup Γ x ρ :
  ctxfind Γ x = Some ρ ->
  ⌊Γ⌋* !! x = Some ⌊ρ⌋.
Proof.
  induction Γ; simpl; intros; try easy.
  destruct a. case_decide. simplify_eq.
  cbn. simplify_map_eq. reflexivity.
  simp_hyps.
  cbn. rewrite insert_empty. rewrite <- insert_union_singleton_l.
  simplify_map_eq. reflexivity.
Qed.

Lemma ctx_erase_app Γ Γ':
  ⌊Γ ++ Γ'⌋* = ⌊Γ⌋* ∪ ⌊Γ'⌋*.
Proof.
  induction Γ; simpl.
  - cbn. by rewrite map_empty_union.
  - destruct a. unfold erase_ctx in *. cbn. rewrite IHΓ.
    by rewrite map_union_assoc.
Qed.

Lemma ctx_erase_dom Γ :
  dom ⌊Γ⌋* ≡ ctxdom Γ.
Proof.
  induction Γ; simpl.
  - cbn. apply dom_empty.
  - destruct a. cbn in *.
    rewrite insert_empty.
    setoid_rewrite dom_union.
    rewrite dom_singleton.
    f_equiv. eauto.
Qed.

Lemma ctx_erase_app_r Γ x ρ :
  x # Γ ->
  ⌊Γ ++ [(x, ρ)]⌋* = <[x:=⌊ρ⌋]> ⌊Γ⌋*.
Proof.
  intros H.
  rewrite ctx_erase_app.
  cbn. rewrite map_union_empty. rewrite insert_empty.
  rewrite <- insert_union_singleton_r. auto.
  ln_simpl. rewrite <- ctx_erase_dom in H.
  by apply not_elem_of_dom.
Qed.

(** * commute *)

#[global] Instance SubstCommute_rty: SubstCommute rty.
Proof.
  unfold SubstCommute.
  induction e; ln_simpl; intros; f_equal; eauto.
  all: rewrite subst_commute; eauto.
Qed.
Arguments SubstCommute_rty /.

#[global] Instance SubstFresh_rty: SubstFresh rty.
Proof.
  unfold SubstFresh.
  intros τ.
  induction τ; ln_simpl; intros; f_equal; eauto;
    solve [ auto_apply; my_set_solver
          | apply subst_fresh; my_set_solver ].
Qed.
Arguments SubstFresh_rty /.

#[global] Instance OpenFv_rty: OpenFv rty.
Proof.
  unfold OpenFv.
  intros τ.
  induction τ; ln_simpl; intros; eauto; try solve [apply open_fv; eauto].
  - etrans. repeat apply union_mono; eauto. my_set_solver. 
Qed.
Arguments OpenFv_rty /.

#[global] Instance OpenFvPrime_rty: OpenFvPrime rty.
Proof.
  unfold OpenFvPrime.
  intros τ.
  induction τ; ln_simpl; intros; eauto; try solve [apply open_fv'; eauto].
  - etrans. repeat apply union_mono; eauto. my_set_solver. 
Qed.
Arguments OpenFvPrime_rty /.

#[global] Instance OpenSubstSame_rty: OpenSubstSame rty.
Proof.
  unfold OpenSubstSame.
  intros x y τ.
  induction τ; ln_simpl; intros; f_equal; eauto;
  try (rewrite open_subst_same; eauto; my_set_solver).
  all: auto_apply; my_set_solver.
Qed.
Arguments OpenSubstSame_rty /.

#[global] Instance SubstOpen_rty: SubstOpen rty.
Proof.
  unfold SubstOpen.
  intros τ.
  induction τ; ln_simpl; intros; f_equal; eauto;
  try (rewrite subst_open; eauto).
Qed.
Arguments SubstOpen_rty /.

(* #[global] Instance SubstOpenVar_rty: SubstOpenVar rty.
Proof. exact subst_open_var. Qed.
Arguments SubstOpenVar_rty /. *)

#[global] Instance SubstLc_rty: SubstLc rty.
Proof.
  unfold SubstLc.
  induction 1; intros; ln_simpl; eauto;
  try solve [econstructor; eauto; apply subst_body; eauto].
  - fold_syntax_class. auto_exists_L.
    + intros. setoid_rewrite <- (subst_open_var (A := rty)); eauto.
      auto_apply; my_set_solver. my_set_solver.
    + simpl.  in *. intuition. fine_rty_simp_aux. fine_rty_solver.
  pose (subst_open_var (A := rty)) as zz.
  setoid_rewrite <- zz.
  
  eauto.
  rewrite <- (subst_open_var (A := rty)). eauto.

Qed.
Arguments SubstLc_rty /.

Lemma subst_lc_rty : forall x (u: value) (τ: rty),
    lc_rty τ -> lc u -> lc_rty ({x := u} τ).
Proof.
  pose subst_lc_phi1.
  all: induction 1; intros; simpl in *.
  - econstructor; simpl; eauto.
  - auto_exists_L.
  - auto_exists_L; intros. rewrite <- subst_open_var_rty; eauto.
    auto_apply; eauto. my_set_solver. my_set_solver.
    simpl. intuition. fine_rty_simp_aux. fine_rty_solver.
Qed.

Lemma fv_of_subst_rty_closed:
  forall x (u : value) (τ: rty),
    closed_value u ->
    rty_fv ({x := u } τ) = (rty_fv τ ∖ {[x]}).
Proof.
  induction τ; simpl; intros; eauto using fv_of_subst_qualifier_closed;
  try (rewrite !fv_of_subst_td_closed by eauto); my_set_solver.
Qed.

Lemma open_not_in_eq_rty (x : atom) (τ : rty) k :
  x # {k ~> x} τ ->
  forall e, τ = {k ~> e} τ.
Proof.
  pose open_not_in_eq_qualifier.
  generalize k; induction τ; intros; simpl in *; f_equal; eauto;
    try (auto_apply; my_set_solver).
Qed.

Lemma subst_intro_rty: forall (ρ: rty) (x:atom) (w: value) (k: nat),
    x # ρ ->
    lc w -> {x := w} ({k ~> x} ρ) = ({k ~> w} ρ).
Proof.
  intros.
  specialize (subst_open_rty ρ x x w k) as J.
  simpl in J. rewrite decide_True in J; auto.
  rewrite J; auto. rewrite subst_fresh_rty; auto.
Qed.


Lemma lc_subst_rty: forall x (u: value) (τ: rty), lc_rty ({x := u} τ) -> lc u -> lc_rty τ.
Proof.
  pose lc_subst_phi1.
  pose lc_subst_phi2.
  pose lc_rty_fine.
  intros.
  remember (({x:=u}) τ).
  generalize dependent τ.
  induction H.
  - intros τ **; destruct τ; inversion Heqr; simpl in *; subst; econstructor; eauto.
  - intros τ1 **; destruct τ1; inversion Heqr; simpl; subst.
    auto_exists_L.
  - intros τ1 **; destruct τ1; inversion Heqr; simpl; subst.
    auto_exists_L.
    intros. repeat specialize_with x0.
    apply H1.
    rewrite <- subst_open_var_rty; eauto. my_set_solver. fine_rty_solver.
Qed.

Lemma open_rty_idemp: forall u (v: value)  (τ: rty) (k: nat),
    lc v ->
    {k ~> u} ({k ~> v} τ) = {k ~> v} τ.
Proof.
  pose open_qualifier_idemp.
  induction τ; intros; simpl; f_equal; eauto.
Qed.

Lemma closed_rty_subseteq_proper s1 s2 ρ :
  closed_rty s1 ρ ->
  s1 ⊆ s2 ->
  closed_rty s2 ρ.
Proof.
  intros. sinvert H. split. eauto.
  my_set_solver.
Qed.

Lemma fact1_rty: forall (u v: value) (A: rty) i j,
    i <> j -> {i ~> u} ({j ~> v} A) = {j ~> v} A -> {i ~> u} A = A.
Proof.
  pose fact1_value.
  pose fact1_qualifier.
  intros u v. induction A; simpl; intros; eauto; f_equal; simp_hyps; eauto.
Qed.

Lemma open_rec_lc_rty: ∀ (u : value) τ (k : nat), lc_rty τ -> {k ~> u} τ = τ.
Proof.
  pose open_rec_lc_phi1.
  intros. generalize dependent k.
  induction H; simpl; intros; auto; f_equal; eauto;
    try (rewrite open_rec_lc_value; eauto).
  - auto_pose_fv x. apply fact1_rty with (j := 0) (v := x); eauto.
    rewrite H0; eauto. my_set_solver.
Qed.

Lemma body_rty_open_lc: forall (v: value) τ,
    lc v -> (body_rty τ) -> lc_rty (τ ^r^ v).
Proof.
  unfold body_rty. intros. simp_hyps.
  auto_pose_fv x.
  erewrite <- open_subst_same_rty. instantiate (1:= x).
  apply subst_lc_rty; eauto.
  apply H0.
  all: my_set_solver.
Qed.

Lemma flip_rty_open τ k v: {k ~> v} (flip_rty τ) = flip_rty ({k ~> v} τ).
Proof.
  destruct τ; simpl; intros; intuition.
Qed.

Lemma flip_rty_subst τ x v: {x:=v} (flip_rty τ) = flip_rty ({x:=v} τ).
Proof.
  destruct τ; simpl; intros; intuition.
Qed.
