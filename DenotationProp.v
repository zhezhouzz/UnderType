From stdpp Require Import mapset.
From stdpp Require Import natmap.
From Stdlib.Program Require Import Wf.
From CT Require Import Syntax Lc.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import Denotation.
From CT Require Import InstantiationProp.

Import BaseDef Lang MyTactics Primitives OperationalSemantics BasicTyping Qualifier RefinementType Instantiation ListCtx List LangLc Lc QualifierLc Denotation InstantiationProp.

(* Ltac is_tm_rty_tac := *)
(*   match goal with *)
(*   | [H: _ |- is_tm_rty _ ] => *)
(*       (repeat match goal with *)
(*          | [H: _ |- is_tm_rty (_ ^r^ _) ] => rewrite is_tm_rty_open; eauto *)
(*          | [H: _ |- is_tm_rty ((m{ _ }r) _) ] => rewrite is_tm_rty_msubst; eauto *)
(*          | [H: _ |- is_tm_rty (({ _ := _ }r) _) ] => rewrite is_tm_rty_subst; eauto *)
(*          | [H: closed_rty _ (_ ⇨ ?τ) |- is_tm_rty ?τ] => eauto using is_tm_rty_retrty *)
(*          end) *)
(*   end. *)

Lemma rtyR_refine_aux n: forall τ e1 e2,
    rty_measure τ <= n ->
    is_coverage_rty τ ->
    e1 ⊑{ ⌊ τ ⌋ } e2 ->
    rtyR n τ e1 ->
    rtyR n τ e2.
Proof.
  induction n; intros τ e1 e2 Hm Hunder [Ht Hr] H; simpl in *;
    destruct τ; simpl in *; eauto; try easy.
  intuition.
  - mydestr. repeat split; my_set_solver.
Qed.

Lemma rtyR_refine: forall τ e1 e2,
    is_coverage_rty τ ->
    e1 ⊑{ ⌊ τ ⌋ } e2 ->
    ⟦ τ ⟧ e1 ->
    ⟦ τ ⟧ e2.
Proof.
  intros τ e1 e2 Hunder Hrefine Hdenote.
  eapply rtyR_refine_aux with (n := rty_measure τ); eauto.
Qed.

Lemma denot_const_overrty (c: constant) (b: base_ty) ϕ:
    (⟦{:b|ϕ}⟧) (treturn (vconst c)) <-> 
    stale {:b|ϕ} = ∅ /\ lc {:b|ϕ} /\ ∅ ⊢ (vconst c) ⋮ (TBase b) /\ ⟦ϕ ^^ (vconst c)⟧.
Proof.
  split; intros.
  - sinvert H. ln_simpl. simp_hyps. repeat split; eauto.
    basic_typing_solver.
  - simp_hyps. econstructor; eauto.
    basic_typing_solver.
Qed.

Lemma ctxEnv_ctxfind Γ σ x ρ :
  ctxEnv Γ σ ->
  ctxfind Γ x = Some ρ ->
  (* fine_rty ρ -> *)
  exists (v : value), σ !! x = Some v /\ ⟦ m{ σ } (flip_rty ρ) ⟧ (treturn v).
Proof.
  intros.
  assert (fine_rty ρ) as Hrefine by (misc_solver).
  assert (ok_ctx Γ) as Hok by (misc_solver).
  assert (x # ρ) as Hxρ. { misc_solver. }
  revert_all.
  induction 1.
  - easy.
  - intros.
    destruct (atom_dec x x0); subst.
    + rewrite ctxfind_last_eq in H2 by misc_solver.
      simp_hyps. intros; subst.
      exists v. split; eauto.
      * misc_solver.
      * rewrite msubst_destruct_rev; misc_solver.
        rewrite subst_fresh; misc_solver.
        rewrite <- H3. my_set_solver.
    + rewrite ctxfind_last_neq in H2 by misc_solver.
      destruct IHctxEnv as (v' & Hv' & Hdenote'); eauto. misc_solver.
      assert (x0 # σ) as Hx0σ. {
        misc_solver.
        rewrite <- H4. eauto.
      }
      exists v'. split; eauto; try solve [misc_solver].
      * rewrite msubst_destruct_rev by misc_solver.
        rewrite subst_fresh. misc_solver.
        { simp_tac.
          assert (stale ρ ∖ stale σ ≡ ∅) as HH by my_set_solver.
          eapply empty_difference_subseteq in HH.
          misc_solver.
        }
Qed.