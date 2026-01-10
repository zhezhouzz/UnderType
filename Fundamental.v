From stdpp Require Import mapset.
From stdpp Require Import natmap.
From Stdlib.Program Require Import Wf.
From CT Require Import Syntax Lc OperationalSemantics BasicTypingProp Instantiation Denotation Typing InstantiationProp DenotationProp.

Import BaseDef Lang MyTactics Primitives OperationalSemantics BasicTyping Qualifier RefinementType Instantiation ListCtx List LangLc Lc QualifierLc Denotation Typing InstantiationProp DenotationProp.

(** * Main metatheoretic results *)

Ltac simpl_fv :=
  do_hyps (fun H => try match type of H with
                    | _ ∉ _ =>
                        simpl in H; rewrite ?ctxEnv_dom in H by eassumption
                    end).

(** Fundamental theorem for event operator typing *)
Lemma builtin_fundamental:
  well_formed_builtin_typing ->
  forall (Γ: listctx rty) (op: effop) (ρ : rty),
    Γ ⊢r op ⋮ ρ ->
    forall σ2, ⟦ Γ ⟧ σ2 -> ⟦ m{ σ2 } ρ ⟧ (treturn (value_of_op op)).
Proof.
  intros HWF Γ op ρ Hop.
  sinvert Hop.
  (* apply HWF in H0. *)
  intros σ1 Hσ1.
  sinvert H2. simp_hyps. ospecialize * H5; eauto.
  destruct H5 as (σ2 & Hσ2 & Hσ12 & H5).
  apply H5.
  unfold well_formed_builtin_typing in HWF.
  apply HWF.
  rewrite msubst_fresh by misc_solver.
  eauto.
Qed.

(* At some point the proof is very slow without marking [msubst] opaque. *)
Opaque msubst.

Ltac ctx_erase_tac :=
  repeat match goal with
  | [H: context [ ⌊_ ++ [(_, _)]⌋* ] |- _ ] => rewrite ctx_erase_app_r in H by my_set_solver
  | [H: _ |- context [ ⌊_ ++ [(_, _)]⌋* ] ] => rewrite ctx_erase_app_r by my_set_solver
  end.

Ltac restructure_typing HOrg :=
  match goal with
  | [H: ctxEnv ?Γ _, HJ: _ ⊢ _ ⋮merge _ ⋮= _ |- (⟦(m{ _ }) ?τ⟧) ((m{ _ }) ?e)] =>
      assert (Γ ⊢ e ⋮ τ) as HOrg by (eapply TMerge in HJ; eauto)
  | [H: ctxEnv ?Γ _ |- (⟦(m{ _ }) ?τ⟧) ((m{ _ }) ?e)] =>
      assert (Γ ⊢ e ⋮ τ) as HOrg by
        (solve [eapply TValue; eauto] ||
           solve [eapply TSub; eauto] ||
             solve [eapply TMerge; eauto] ||
               solve [eapply TLetE; eauto] ||
                   solve [eapply TAppOverParam; eauto] ||
                     solve [eapply TAppFuncParam; eauto] ||
                       solve [eapply TAppOp; eauto] ||
                         solve [eapply TMatchbTrue; eauto] ||
                           solve [eapply TMatchbFalse; eauto]
        )
  | [H: ctxEnv ?Γ _ |- (⟦(m{ _ }) ?τ⟧) (treturn (m{_} ?e))] =>
      assert (Γ ⊢ e ⋮ τ) as HOrg by
        (solve [eapply TSubPP; eauto] ||
           solve [eapply TConst; eauto] ||
             solve [eapply TBaseVar; eauto] ||
               solve [eapply TFuncVar; eauto] ||
                 solve [eapply TFun; eauto] ||
                   solve [eapply TFix; eauto]
        )
  end.

(* Ltac restructure_typing_regular :=
  let HOrg := fresh "HOrg" in
  restructure_typing HOrg;
  match goal with
  | [H: ctxEnv ?Γ _, HOrg: ?Γ ⊢ ?e ⋮ ?τ |- (⟦(m{ _ }) ?τ⟧) ((m{_} ?e))] =>
      pose (refinement_typing_regular_basic_typing _ _ _ HOrg) as HBTOrg;
      pose (msubst_preserves_basic_typing_tm_empty _ _  H _ _ HBTOrg) as HBTOrgMsubst
  | [H: ctxEnv ?Γ _, HOrg: ?Γ ⊢ ?e ⋮ ?τ |- (⟦(m{ _ }) ?τ⟧) (treturn (m{_} ?e))] =>
      pose (refinement_typing_regular_basic_typing _ _ _ HOrg) as HBTOrg;
      pose (msubst_preserves_basic_typing_value_empty _ _  H _ _ HBTOrg) as HBTOrgMsubst
  end. *)

Ltac auto_exists_env :=
match goal with
| [H: exists w, _ |- exists _, _] =>
  let σ := fresh "σ" in
  destruct H as (σ & H);
  exists σ; intuition
end. 

Lemma empty_env_denote_empty_env: ∀ σ, (⟦[]⟧) σ -> σ = ∅.
Proof.
  intros σ H. sinvert H; eauto.
  destruct Γ; listctx_set_simpl; sinvert H0.
Qed.

Lemma mk_eq_constant_lc c : lc (mk_eq_constant c).
Proof.
  econstructor. unshelve (repeat econstructor). exact ∅.
  my_set_solver.
Qed.

Lemma mk_eq_constant_denote_rty c:
  ⟦ mk_eq_constant c ⟧ (treturn (vconst c)).
Proof.
  unfold mk_eq_constant. ln_simpl.
  repeat split; eauto.
  + misc_solver.
  + apply mk_eq_constant_lc.
  + intros. 
    pose value_reduction_any_ctx.
    destruct v; ln_simpl; try hauto.
    auto_apply. lc_solver.
Qed.

(** Combined fundamental theorem for value typing (refinemnet types) and term
  typing (Hoare automata types) *)
Theorem fundamental_combined:
  well_formed_builtin_typing ->
  (forall (Γ: listctx rty) (v: value) (ρ: rty),
      Γ ⊢r v ⋮ ρ -> ⟦ ρ ⟧{ Γ } (treturn v)) /\
    (forall (Γ: listctx rty) (e: tm) (τ: rty),
        Γ ⊢r e ⋮ τ -> ⟦ τ ⟧{ Γ } e).
Proof.
  (* pose value_reduction_any_ctx as HPureStep. *)
  intros HWFbuiltin.
  apply value_term_type_check_mutind.
  (* [TSubPP] *)
  - intros Γ v ρ1 ρ2 HWFρ2 _ HDρ1 Hsub σ Hσ. exists σ.
    repeat split; eauto.
    sinvert Hsub. mydestr.
    ospecialize (H3 ∅ _). { econstructor. }
    destruct H3 as (σ1 & Hσ1 & Heq1 & H3).
    ospecialize (HDρ1 ∅ _). { econstructor. }
    destruct HDρ1 as (σ2 & Hσ2 & Heq2 & HDρ1).
    apply empty_env_denote_empty_env in Hσ1; subst.
    apply empty_env_denote_empty_env in Hσ2; subst.
    assert (stale v = ∅) as Hstale by misc_solver.
    assert (stale ρ2 = ∅) as Hstale2 by misc_solver.
    simp_tac; eauto.
    rewrite msubst_fresh by my_set_solver.
    apply H3.
    rewrite msubst_fresh by my_set_solver.
    eauto.
  (* [TConst] *)
  - intros Γ c HWF σ Hσ. exists σ.
    repeat split; eauto.
    simp_tac; eauto.
    apply mk_eq_constant_denote_rty.
  (* [TBaseVar] *)
  - intros Γ x b ϕ Hwf Hfind σ Hσ. exists σ.
    repeat split; eauto.
    Check ctxEnv_ctxfind.
    Search ctxfind.
    dup_hyp Hσ (fun H => eapply ctxEnv_ctxfind in H; eauto). simp_hyps.
    repeat msubst_simp. rewrite H0.
    destruct H1 as [H _].
    sinvert H. cbn in H3.
    dup_hyp H3 (fun H => apply basic_typing_base_canonical_form in H).
    simp_hyps. subst. sinvert H3.
    eauto using mk_eq_constant_denote_rty. misc_solver.
  (* [TFuncVar] *)
  - intros Γ x ρ τ Hwf Hfind σ Hσ. exists σ. intuition. admit.
    (* dup_hyp Hσ (fun H => eapply ctxEnv_ctxfind in H; eauto).
    { simp_hyps. repeat msubst_simp. by rewrite H0. }
    misc_solver. *)
  (* [TFun] *)
  - intros Γ Tx ρ e τ L HWF Ht HDe He σ Hσ. exists σ. intuition. admit.
    (* restructure_typing_regular.
    repeat msubst_simp. subst.
    eapply denotation_application_lam; eauto.
    + misc_solver.
    + simpl. simp_tac; eauto.
    + eapply_eq msubst_preserves_closed_rty_empty; eauto.
      msubst_simp.
    + intros v_x Hv_x.
      auto_ctx_letbinding v_x.
      ospecialize* HDe; eauto.
      rewrite <- msubst_intro_tm in HDe by
          (eauto using ctxEnv_closed_env, ctxEnv_lc, rtyR_closed_value;
           simpl_fv; my_set_solver).
      rewrite <- msubst_intro_rty in HDe by
          (eauto using ctxEnv_closed_env, ctxEnv_lc, rtyR_closed_value;
           simpl_fv; my_set_solver).
      eauto. *)
  (* [TFix] *)
  - intros Γ Tx ϕ e τ T L HWF Hlam HDlam He σ Hσ. admit.
    (* restructure_typing_regular.
    repeat msubst_simp.
    eapply denotation_application_fixed; eauto.
    + misc_solver.
    + by rewrite <- rty_erase_msubst_eq.
    + assert (Γ ⊢ vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e) ⋮ ({:Tx|ϕ}⇨τ))
        by eauto using value_type_check.
      eapply value_typing_regular_basic_typing in H.
      eapply msubst_preserves_basic_typing_value_empty in H; eauto.
      repeat msubst_simp.
      apply_eq H. cbn. subst. eauto.
    + eapply_eq msubst_preserves_closed_rty_empty; eauto.
      repeat msubst_simp.
    + intros v_x Hv_x.
      auto_ctx_letbinding v_x.
      ospecialize* HDlam; eauto.
      rewrite <- msubst_intro_value in HDlam by
          (eauto using ctxEnv_closed_env, ctxEnv_lc, rtyR_closed_value;
           simpl_fv; my_set_solver).
      repeat msubst_simp.
      rewrite <- msubst_intro_rty in HDlam by
          (eauto using ctxEnv_closed_env, ctxEnv_lc, rtyR_closed_value;
           simpl_fv; my_set_solver).
      rewrite msubst_insert_fresh_rty in HDlam by
          (eauto using ctxEnv_closed_env, rtyR_closed_value; simpl_fv; my_set_solver).
      rewrite_msubst msubst_qualifier in HDlam.
      rewrite msubst_insert_fresh_qualifier in HDlam by
          (eauto using ctxEnv_closed_env, rtyR_closed_value; simpl_fv; my_set_solver).
      apply_eq HDlam.
      simpl. repeat msubst_simp.
      clear. simplify_map_eq. eauto. *)
  (* [TErr] *)
  - intros Γ b Hwf σ Hσ. exists σ. intuition. admit.
  (* [TEPur] *)
  - intros Γ v ρ Hv HDv σ Hσ. specialize (HDv _ Hσ).
    auto_exists_env. 
    (* admit.
    restructure_typing_regular.
    repeat msubst_simp.
    split; [| split].
    + simp_tac; eauto.
    + eapply_eq msubst_preserves_closed_rty_empty; eauto.
      repeat msubst_simp.
    + finerty_destruct ρ; intros.
      * simpl in *. simp_hyps; subst. repeat auto_apply.
        intros. apply value_reduction_any_ctx. misc_solver.
      * exists ((m{σ}) v). simpl in *. simp_hyps; subst. intuition.
        { exists ((m{σ}) v). intuition. apply value_reduction_any_ctx. misc_solver. }
        { apply value_reduction_any_ctx. misc_solver. } *)
  (* [TSub] *)
  - admit.
   (* intros Γ e τ1 τ2 HWFτ2 _ HDτ1 Hsub σ Hσ. specialize (HDτ1 _ Hσ).
    apply Hsub in HDτ1; auto. *)
  (* [TMerge] *)
  - unfold join. intros Γ e τ1 τ2 τ3 HWFτ3 _ HDτ1 _ HDτ2 (_ & _ & _ & _ & Hjoin) He σ Hσ.
    specialize (HDτ1 _ Hσ). specialize (HDτ2 _ Hσ).
    destruct HDτ1 as (σ1 & Hσ1 & Heq1 & HDτ1).
    destruct HDτ2 as (σ2 & Hσ2 & Heq2 & HDτ2).
    exists σ. intuition.
    rewrite Hjoin by auto. split.
    + admit.
    + admit.
  (* [TLetE] *)
  - intros Γ e_x e ρ1 ρ' L HTe_x HDe_x HWF HTe HDe σ Hσ.
    auto_pose_fv x. repeat specialize_with x.
    assert (exists v_x, ⟦m{σ} (flip_rty ρ1)⟧ (treturn v_x)) as Hv_x by admit.
    destruct Hv_x as (v_x & Hv_x).
    ospecialize* (HDe_x (<[x := v_x]>σ) _). admit.
    destruct HDe_x as (σ1 & Hσ1 & Heq1 & HDe_x).
    exists ([D~ {[x]}] σ1). intuition.
    + admit.
    + admit.
    + admit.
    (* restructure_typing_regular.
    repeat msubst_simp.
    eapply denotation_application_tlete; simp_tac.
    + ospecialize* HDe; eauto. repeat msubst_simp.
    + intros v_x Hv_x.
      auto_ctx_letbinding v_x.
      by (apply tm_typing_regular_wf in HTe; finerty_destruct ρ1; simpl; eauto).
      ospecialize* HDe_x; eauto.
      rewrite msubst_insert_fresh_rty in HDe_x. repeat msubst_simp.
      rewrite open_rec_lc_rty.
      erewrite msubst_intro_tm; eauto.
      all: rtyR_regular_simp; misc_solver. *)
  (* [TAppOverParam] *)
  - intros Γ v1 v2 e b ϕ ρ1 ρ2 L HTe HDe HWF HTv2 HDv2 HTv1 HDv1 σ Hσ.
    admit.
  (* restructure_typing_regular.
  assert (lc v2) as Hlcv2. {
    apply value_typing_regular_basic_typing in HTv2.
    lc_solver_plus.
  }
  assert (⌊ Γ ⌋* ⊢t (mk_app_e_v v1 v2) ⋮ ⌊ ρ2 ⌋) as HBTMkApp. {
    eapply mk_app_e_v_has_type; basic_typing_simp; eauto.
  }
  ospecialize* HDv1; eauto. ospecialize* HDv2; eauto. repeat msubst_simp.
  rewrite msubst_open_td by simp_tac. repeat msubst_simp.
  eapply denotation_application_tletapp; eauto.
  all: try solve [simp_tac].
  + eapply_eq msubst_preserves_closed_rty_empty; eauto.
    repeat msubst_simp. rewrite msubst_open_td; simp_tac.
  + intros v_x Hv_x.
    auto_ctx_letbinding v_x.
    by (rewrite msubst_open_rty; simp_tac).
    by (apply value_typing_regular_wf in HTv1;
        rewrite closed_rty_arr in HTv1;
        finerty_destruct ρ2; simpl in *; intuition).
    ospecialize* HDe; eauto.
    rewrite msubst_insert_fresh_rty in HDe. repeat msubst_simp.
    rewrite open_rec_lc_rty.
    erewrite msubst_intro_tm; eauto.
    all: rtyR_regular_simp; misc_solver. *)
  (* [TAppFuncParam] *)
  - admit.
   (* intros Γ v1 v2 e ρ1 ρ2 A ρ B L HTe HDe HWF HTv2 HDv2 HTv1 HDv1 σ Hσ.
    restructure_typing_regular.
    assert (lc v2) as Hlcv2. {
      apply value_typing_regular_basic_typing in HTv2.
      lc_solver_plus.
    }
    assert (⌊ Γ ⌋* ⊢t (mk_app_e_v v1 v2) ⋮ ⌊ ρ2 ⌋) as HBTMkApp. {
      eapply mk_app_e_v_has_type; basic_typing_simp; eauto.
    }
    ospecialize* HDv1; eauto. ospecialize* HDv2; eauto. repeat msubst_simp.
    rewrite msubst_open_td by simp_tac. repeat msubst_simp.
    eapply denotation_application_tletapp; eauto.
    all: try solve [simp_tac].
    + eapply_eq msubst_preserves_closed_rty_empty; eauto.
      repeat msubst_simp. rewrite msubst_open_td; simp_tac.
    + intros v_x Hv_x.
      auto_ctx_letbinding v_x.
      by (rewrite msubst_open_rty; simp_tac).
      by (apply value_typing_regular_wf in HTv1;
          rewrite closed_rty_arr in HTv1;
          finerty_destruct ρ2; simpl in *; intuition).
      ospecialize* HDe; eauto.
      rewrite msubst_insert_fresh_rty in HDe. repeat msubst_simp.
      rewrite open_rec_lc_rty.
      erewrite msubst_intro_tm; eauto.
      all: rtyR_regular_simp; misc_solver. *)
  (* [TEOpApp] *)
  - admit.
    (* intros Γ op v2 e ρ2 b1 ϕ1 A1 τ2 A2 L HTe HDe HWF HTv2 HDv2 HTop σ Hσ.
    restructure_typing_regular.
    assert (lc v2) as Hlcv2. {
      apply value_typing_regular_basic_typing in HTv2.
      lc_solver_plus.
    }
    sinvert HTop. apply HWFbuiltin in H0. destruct H1 as (_ & _ & Hsub).
    ospecialize* (Hsub _ Hσ).
    { assert (closed_rty ∅ ρ_op) as HClosedOp by simp_tac. simp_tac. }
    repeat msubst_simp.
    rewrite msubst_open_td by simp_tac. repeat msubst_simp.
    eapply denotation_application_tletopapp; eauto.
    all: try solve [simp_tac].
    + eapply msubst_preserves_closed_rty_empty in HWF; eauto. repeat msubst_simp.
      rewrite msubst_open_td in HWF; eauto; simp_tac.
    + intros v_x Hv_x.
      auto_ctx_letbinding v_x.
      { rewrite msubst_open_rty; simp_tac. }
      ospecialize* HDe; eauto.
      rewrite msubst_insert_fresh_rty in HDe. repeat msubst_simp.
      rewrite open_rec_lc_rty.
      erewrite msubst_intro_tm; eauto.
      all: rtyR_regular_simp; misc_solver. *)
  (* [TMatchb1] *)
  - intros Γ v e1 e2 ϕ τ L HWF HTv HDv HNTe1 HTe2 HDe2 σ Hσ.
    auto_pose_fv x. repeat specialize_with x.
    ospecialize* (HDe2 (<[x := vconst true]> σ) _). admit.
    destruct HDe2 as (σ1 & Hσ1 & Heq1 & HDe2).
    exists ([D~ {[x]}] σ1). intuition.
    + admit.
    + admit.
    + admit.
    (* restructure_typing_regular.
    assert (is_tm_rty τ) as HisTmRty by (eapply value_tm_typing_regular_is_tm_rty; eauto).
    auto_pose_fv x. repeat specialize_with x.
    ospecialize* HDv; eauto.
    repeat msubst_simp.
    assert (exists (b : bool), m{σ} v = b) as [b He] by
        qauto using value_typing_regular_basic_typing,
                    msubst_preserves_basic_typing_value_empty,
                    basic_typing_bool_canonical_form.
    rewrite He in *.
    assert (ctxEnv
              (Γ ++ [(x, {:TBool|(b0:c=b) & ((b0:v=v) & ϕ)})])
              (<[x:=vconst b]>σ)) as Hσ'. {
      apply ctxEnv_insert_easy; eauto. my_set_solver.
      repeat msubst_simp.
      repeat apply denote_base_rty_qualifier_and; eauto.
      apply_eq mk_eq_constant_over_denote_rty. clear - Hσ.
      rewrite_msubst msubst_qualifier. simpl. repeat msubst_simp.
      apply_eq mk_eq_constant_over_denote_rty. clear - He Hσ.
      rewrite_msubst msubst_qualifier. simpl. rewrite He. repeat msubst_simp.
      fine_solver.
    }
    destruct b.
    + ospecialize* HDe1; eauto.
      rewrite msubst_insert_fresh_tm in HDe1 by
          (eauto using ctxEnv_closed_env; simpl_fv; my_set_solver).
      rewrite msubst_insert_fresh_rty in HDe1 by
          (eauto using ctxEnv_closed_env; simpl_fv; my_set_solver).
      eapply rtyR_refine; eauto. misc_solver.
      sinvert HBTOrgMsubst. eapply tm_refine_tmatchb_true; eauto.
    + ospecialize* HDe2; eauto.
      rewrite msubst_insert_fresh_tm in HDe2 by
          (eauto using ctxEnv_closed_env; simpl_fv; my_set_solver).
      rewrite msubst_insert_fresh_rty in HDe2 by
          (eauto using ctxEnv_closed_env; simpl_fv; my_set_solver).
      eapply rtyR_refine; eauto. misc_solver.
      sinvert HBTOrgMsubst. eapply tm_refine_tmatchb_false; eauto. *)
  - admit.
Admitted.

(** Fundamental theorem for value typing *)
Theorem fundamental_value:
  well_formed_builtin_typing ->
  forall (Γ: listctx rty) (v: value) (ρ: rty),
    Γ ⊢ v ⋮ ρ ->
    forall epr, ctxEnv Γ epr -> forall σ, eprR epr σ -> ⟦ m{σ} ρ ⟧ (m{σ} v).
Proof.
  qauto using fundamental_combined.
Qed.

(** Fundamental theorem (Theorem 4.8) *)
Theorem fundamental:
  well_formed_builtin_typing ->
  forall (Γ: listctx rty) (e: tm) (τ: rty),
    Γ ⊢ e ⋮ τ ->
    forall epr σ, ctxEnv Γ epr -> eprR epr σ -> ⟦ m{ σ } τ ⟧ (m{ σ } e).
Proof.
  qauto using fundamental_combined.
Qed.

Transparent msubst.

(** A general type soundness theorem *)
(* Corollary soundness :
  well_formed_builtin_typing ->
  forall (e : tm) b (ϕ : qualifier) (A : transducer),
    [] ⊢ e ⋮ ([:b|ϕ]!<[ A ]>) ->
    forall (v : value) α β,
      ⟦ {:b|ϕ} ⟧ v ->
      a⟦ A ^a^ v ⟧ α β ->
      α ⊧ e ↪*{ β } v.
Proof.
  intros HWF * HT * HDα Hstepv.
  eapply fundamental in HT; eauto using ctxEnv.
  unfold msubst in HT. rewrite !map_fold_empty in HT.
  qauto using HT.
Qed. *)

(* Print Assumptions soundness. *)
