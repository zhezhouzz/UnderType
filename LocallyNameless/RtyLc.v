From stdpp Require Import mapset.
From stdpp Require Import natmap.
From stdpp Require Import fin vector.
From Stdlib Require Classical_Prop.
From CT.Syntax Require Import Syntax.
From CT.LocallyNameless Require Import FineRty LangLc QualifierLc.

Import BaseDef Lang MyTactics Primitives Qualifier ListCtx List RefinementType Syntax LangLc QualifierLc FineRty.

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
  destruct a. case_decide; simplify_eq.
  - cbn. eapply lookup_union_Some_l.
    simplify_map_eq; auto.
  - cbn. rewrite lookup_union. rewrite lookup_insert. simplify_map_eq; auto.
Qed.

Lemma ctx_erase_app Γ Γ':
  ⌊Γ ++ Γ'⌋* = ⌊Γ⌋* ∪ ⌊Γ'⌋*.
Proof.
  induction Γ; simpl.
  - cbn. by rewrite map_empty_union.
  - destruct a. unfold erase_ctx in *. cbn. rewrite IHΓ.
    by rewrite map_union_assoc.
Qed.

Lemma ctx_erase_dom' Γ :
  stale ⌊Γ⌋* ≡ stale Γ.
Proof.
  induction Γ; ln_simpl; cbn; my_set_solver.
Qed.

Lemma ctx_erase_dom Γ :
  stale ⌊Γ⌋* = stale Γ.
Proof.
  pose ctx_erase_dom'. my_set_solver.
Qed.

Lemma ctx_erase_cons Γ x ρ :
  x # Γ ->
  ⌊(x, ρ) :: Γ⌋* = <[x:=⌊ρ⌋]> ⌊Γ⌋*.
Proof.
  intros H.
  assert ((x, ρ) :: Γ = [(x, ρ)] ++ Γ) as HT by listctx_set_simpl.
  rewrite HT.
  rewrite ctx_erase_app.
  cbn. simplify_map_eq. rewrite map_union_empty. rewrite insert_empty.
  rewrite <- insert_union_singleton_l. auto.
Qed.

Lemma ctx_erase_app_r Γ x ρ :
  x # Γ ->
  ⌊Γ ++ [(x, ρ)]⌋* = <[x:=⌊ρ⌋]> ⌊Γ⌋*.
Proof.
  intros H.
  rewrite ctx_erase_app.
  cbn. rewrite map_union_empty. rewrite insert_empty.
  rewrite <- insert_union_singleton_r. auto.
  rewrite <- ctx_erase_dom in H.
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

#[global] Instance SubstOpenVar_rty: SubstOpenVar rty.
Proof.
  apply SubstOpenVar_all. all: typeclasses eauto.
Qed.
Arguments SubstOpenVar_rty /.

#[global] Instance SubstLc_rty: SubstLc rty.
Proof.
  unfold SubstLc.
  induction 1; intros; ln_simpl; eauto.
  - econstructor; eauto. destruct H as [L H].
    auto_exists_L. intros. rewrite <- subst_open_var; eauto.
    apply subst_lc; eauto. apply H.
    all: my_set_solver.
  - econstructor; eauto. destruct H as [L H].
    auto_exists_L. intros. rewrite <- subst_open_var; eauto.
    apply subst_lc; eauto. apply H.
    all: my_set_solver.
  - auto_exists_L; fold_syntax_class; eauto.
    + intros. rewrite <- subst_open_var; eauto.
      auto_apply; my_set_solver. my_set_solver.
    + simpl in *. fine_rty_solver.
Qed.
Arguments SubstLc_rty /.

#[global] Instance SubstBody_rty: SubstBody rty.
Proof.
  apply SubstBody_all. all: typeclasses eauto.
Qed.

#[global] Instance FvOfSubstClosed_rty: FvOfSubstClosed rty.
Proof.
  unfold FvOfSubstClosed.
  induction e; ln_simpl; intros; try solve [rewrite fv_of_subst_closed; eauto].
  - my_set_solver.
Qed.
Arguments FvOfSubstClosed_rty /.

#[global] Instance OpenNotInEq_rty: OpenNotInEq rty.
Proof.
  unfold OpenNotInEq.
  induction e; intros; ln_simpl; f_equal; eauto;
    try (auto_apply; my_set_solver).
  all: apply open_not_in_eq; eauto.
Qed.
Arguments OpenNotInEq_rty /.

#[global] Instance SubstIntro_rty: SubstIntro rty.
Proof.
    apply SubstIntro_all; typeclasses eauto.
Qed.
Arguments SubstIntro_rty /.

#[global] Instance LcSubst_rty: LcSubst rty.
Proof.
    unfold LcSubst.
  intros x u τ Hlc Hu.
  remember ({x:=u} τ).
  generalize dependent τ.
  induction Hlc.
  - intros τ **; destruct τ; inversion Heqr; simpl in *; subst; econstructor; eauto. eapply body_subst; eauto.
  - intros τ1 **; destruct τ1; inversion Heqr; simpl; subst.
    auto_exists_L; eapply body_subst; eauto.
  - intros τ1 **; destruct τ1; inversion Heqr; simpl; subst.
    auto_exists_L.
    + intros y Hy. repeat specialize_with y.
     apply H0.
     fold_syntax_class. rewrite subst_open_var; eauto. set_solver.
    + fold_syntax_class. fine_rty_solver. 
    + hauto.
Qed.
Arguments LcSubst_rty /.

#[global] Instance OpenIdemp_rty: OpenIdemp rty.
Proof.
  unfold OpenIdemp.
  induction t; intros; ln_simpl; f_equal; eauto.
  all: rewrite open_idemp; eauto.
Qed.
Arguments OpenIdemp_rty /.

(* Lemma closed_rty_subseteq_proper s1 s2 ρ :
  closed_rty s1 ρ ->
  s1 ⊆ s2 ->
  closed_rty s2 ρ.
Proof.
  intros. sinvert H. split. eauto.
  my_set_solver.
Qed. *)

#[global] Instance Fact1_rty: Fact1 rty.
Proof.
  unfold Fact1.
  intros u v. induction e; ln_simpl; intros; eauto; f_equal; simp_hyps; eauto.
  all: apply fact1 with (j := S j) (v := v); eauto.
Qed.
Arguments Fact1_rty /.

#[global] Instance OpenRecLc_rty: OpenRecLc rty.
Proof.
  unfold OpenRecLc.
  intros. generalize dependent k.
  induction H; ln_simpl; intros; auto; f_equal; eauto;
  try (apply open_rec_body; eauto).
  - auto_pose_fv x. apply fact1 with (j := 0) (v := x); eauto.
    rewrite H0; eauto. my_set_solver.
Qed.
Arguments OpenRecLc_rty /.

#[global] Instance OpenLc: OpenLc rty.
Proof.
  apply OpenLc_all with (substA := subst_rty). all: typeclasses eauto.
Qed.
Arguments OpenLc /.

Lemma flip_rty_open τ k v: {k ~> v} (flip_rty τ) = flip_rty ({k ~> v} τ).
Proof.
  destruct τ; simpl; intros; intuition.
Qed.

Lemma flip_rty_subst τ x v: {x:=v} (flip_rty τ) = flip_rty ({x:=v} τ).
Proof.
  destruct τ; simpl; intros; intuition.
Qed.

Lemma flip_rty_stale τ: stale (flip_rty τ) = stale τ.
Proof.
  destruct τ; simpl; intros; intuition.
Qed.
