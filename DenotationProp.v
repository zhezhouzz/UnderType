From stdpp Require Import mapset.
From stdpp Require Import natmap.
From Stdlib.Program Require Import Wf.
From CT Require Import Syntax Lc.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import Denotation.

Import BaseDef Lang MyTactics Primitives OperationalSemantics BasicTyping Qualifier RefinementType Instantiation ListCtx List LangLc Lc QualifierLc Denotation.

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

(* Lemma ctxRst_insert_easy Γ P (x: atom) ρ P': *)
(*     ctxRst Γ P -> *)
(*     x ∉ ctxdom Γ -> *)
(*     (forall env (v: value), ⟦ m{ env }r ρ ⟧ v -> P env <-> P' (<[ x := v ]> env)) -> *)
(*     ctxRst (Γ ++ [(x, ρ)]) P'. *)
(* Proof. *)
(*   intros. econstructor; eauto. *)
(*   econstructor; eauto using ctxRst_ok_ctx. *)
(*   apply rtyR_typed_closed in H1. simp_hyps. *)
(*   (* This should be a lemma similar to [msubst_preserves_closed_rty_empty], or *)
(*   we should strenghthen this lemma. But don't bother now as it is only used *)
(*   here. *) *)
(*   sinvert H3. *)
(*   econstructor. eauto using lc_msubst_rty, ctxRst_lc. *)
(*   rewrite fv_of_msubst_rty_closed in H5 by eauto using ctxRst_closed_env. *)
(*   rewrite ctxRst_dom in * by eauto. *)
(*   my_set_solver. *)
(* Qed. *)

(* Lemma ctxRst_ctxfind Γ Γv x ρ : *)
(*   ctxRst Γ Γv -> *)
(*   ctxfind Γ x = Some ρ -> *)
(*   fine_rty ρ -> *)
(*   exists (v : value), Γv !! x = Some v /\ ⟦ m{ Γv }r ρ ⟧ v. *)
(* Proof. *)
(*   induction 1. *)
(*   - easy. *)
(*   - intros. *)
(*     select (ctxfind (_ ++ _) _ = _) *)
(*       (fun H => apply ctxfind_app in H; eauto using ok_ctx_ok). *)

(*     assert (forall (v' : value), (⟦(m{env}r) ρ⟧) v' -> *)
(*                             (⟦(m{<[x0:=v]> env}r) ρ⟧) v'). { *)
(*       select (⟦ _ ⟧ _) (fun H => apply rtyR_typed_closed in H). simp_hyps. *)
(*       intros. *)
(*       apply rtyR_msubst_insert_eq; eauto using ctxRst_closed_env. *)
(*       select (_ ⊢ _ ⋮ _) *)
(*         (fun H => apply basic_typing_contains_fv_tm in H; simpl in H). *)
(*       my_set_solver. *)
(*       select (ok_ctx _) (fun H => apply ok_ctx_ok in H; apply ok_post_destruct in H). *)
(*       srewrite ctxRst_dom. *)
(*       simp_hyps. *)
(*       apply not_elem_of_dom. eauto. *)
(*     } *)
(*     destruct_or!; simp_hyps. *)
(*     + eexists. split; eauto. *)
(*       assert (x <> x0). { *)
(*         select (ok_ctx _) (fun H => sinvert H); listctx_set_simpl. *)
(*         select (ctxfind _ _ = _) (fun H => apply ctxfind_some_implies_in_dom in H). *)
(*         my_set_solver. *)
(*       } *)
(*       by simplify_map_eq. *)
(*     + simpl in *. *)
(*       case_decide; try easy. simplify_eq. *)
(*       eexists. split; eauto. by simplify_map_eq. *)
(* Qed. *)
