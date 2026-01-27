From stdpp Require Import mapset.
From stdpp Require Import natmap.
From Stdlib.Program Require Import Wf.
From CT Require Import Syntax Lc.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.

Import BaseDef Lang MyTactics Primitives OperationalSemantics BasicTyping Qualifier RefinementType ListCtx List LangLc Lc QualifierLc.



(** This file defines type denotations in λᴱ (Fig. 7). *)

(** Type Denotation *)

(** Refinement type and Hoare automata type denotation (Fig. 7) *)
(* The first argument is an overapproximation of the "size" of [ρ] or [τ]. In
other words, it is the "fuel" to get around Coq's termination checker. As long
as it is no less than [rty_measure] and [rty_measure], the denotation will not
hit bottom. Note that this is _different_ from the step used in step-indexed
logical relation. *)

(* Definition pure_tm (e: tm) := forall e' α β, α ⊧ e ↪*{β} e' -> α = β. *)

Fixpoint rtyR (gas: nat) (ρ: rty) (e: tm) : Prop :=
  match gas with
  | 0 => False
  | S gas' =>
      ∅ ⊢ e ⋮ ⌊ ρ ⌋ /\ stale ρ = ∅ /\ lc ρ /\
        match ρ with
        | {: b | ϕ} => exists (v: value), e = treturn v /\ ⟦ ϕ ^^ v ⟧
        | [: b | ϕ] => forall (v: value), ⟦ ϕ ^^ v ⟧ -> e ↪* (treturn v)
        | ρx ⇨ τ =>
            exists (v: value),
            e ↪* (treturn v) /\
                  (forall (v_x: value), rtyR gas' ρx (treturn v_x) -> rtyR gas' (τ ^^ v_x) (tletapp_arg_value v v_x))
        end
  end.

#[global] Instance Denotation_rty: Denotation rty (tm -> Prop) :=
fun τ => rtyR (rty_measure τ) τ.

Hint Unfold Denotation_rty: class_simpl.

(** We first define the normal denotation of a context, e.g., substitution of a context. *)
Inductive ctxEnv: listctx rty -> env -> Prop :=
| ctxEnvEmp: ctxEnv [] ∅
| ctxEnvInd: forall Γ (x: atom) τ σ (v: value),
  ctxEnv Γ σ ->
  ok_ctx (Γ ++ [(x, τ)]) ->
  ⟦ m{ σ } (flip_rty τ)⟧ (treturn v) ->
  ctxEnv (Γ ++ [(x, τ)]) (<[x:=v]> σ).

Global Hint Constructors ctxEnv: core.

Fixpoint ctxOverBindings (Γ: listctx rty): aset :=
  match Γ with
  | [] => ∅
  | (x, {: _ | _}) :: Γ => {[x]} ∪ ctxOverBindings Γ
  | (x, [: _ | _]) :: Γ => ctxOverBindings Γ
  | (x, _ ⇨ _) :: Γ => {[x]} ∪ ctxOverBindings Γ
  end.

#[global] Instance Denotation_rtyctx: Denotation (listctx rty) (env ->Prop) := ctxEnv.

Hint Unfold Denotation_rtyctx: class_simpl.

Inductive wfEnv: listctx rty -> Prop :=
| wfEnv_nil: wfEnv []
| wfEnv_cons1: forall Γ (x: atom) (ρ: rty),
  is_under_base_rty ρ ->
  wfEnv Γ ->
  ok_ctx (Γ ++ [(x, ρ)]) ->
  (forall σ, ⟦Γ⟧ σ -> exists v, ⟦m{σ} (flip_rty ρ)⟧ (treturn v)) ->
  wfEnv (Γ ++ [(x, ρ)])
| wfEnv_cons2: forall Γ (x: atom) (ρ: rty),
  ~ (is_under_base_rty ρ) ->
  stale ρ ⊆ (ctxOverBindings Γ) ->
  wfEnv Γ ->
  ok_ctx (Γ ++ [(x, ρ)]) ->
  wfEnv (Γ ++ [(x, ρ)]).

Global Hint Constructors wfEnv: core.

Inductive rtyR_env (L: aset) : listctx rty -> (env -> env -> Prop) -> Prop :=
| rtyR_env_nil: forall (P: env -> env -> Prop),
  P ∅ ∅ ->
  rtyR_env L [] P
| rtyR_env_cons1: forall Γ (x: atom) (ρ: rty) (P: env -> env -> Prop),
  ~ (is_under_base_rty ρ /\ x ∉ L) ->
  rtyR_env L Γ (fun σ1 σ2 => 
    forall v, 
      ⟦m{σ1 ∪ σ2} (flip_rty ρ)⟧ (treturn v) ->
      P (<[x:=v]> σ1) σ2
  ) ->
  rtyR_env L (Γ ++ [(x, ρ)]) P
| rtyR_env_cons2: forall Γ (x: atom) (ρ: rty) (P: env -> env -> Prop),
  is_under_base_rty ρ /\ x ∉ L ->
  rtyR_env L Γ (fun σ1 σ2 => 
    exists v, 
      ⟦m{σ1 ∪ σ2} (flip_rty ρ)⟧ (treturn v) /\ P σ1 (<[x:=v]> σ2)
  ) ->
  rtyR_env L (Γ ++ [(x, ρ)]) P.

Global Hint Constructors rtyR_env: core.

Notation " '⟦' Γ '⟧{' L '}'" := (rtyR_env L Γ) (at level 20, format "⟦ Γ ⟧{ L }", Γ constr, L constr).

Lemma rtyR_env_proper:
  forall L Γ P1 P2,
  (forall σ1 σ2, P1 σ1 σ2 -> P2 σ1 σ2) ->
  rtyR_env L Γ P1 ->
  rtyR_env L Γ P2.
Proof.
  intros L.
  apply (rev_ind (fun Γ => forall P1 P2,
    (forall σ1 σ2, P1 σ1 σ2 -> P2 σ1 σ2) ->
    rtyR_env L Γ P1 ->
    rtyR_env L Γ P2
  )); intros; eauto.
  - sinvert H0; eauto; listctx_set_simpl.
  - destruct x as (x, ρ).
    sinvert H1; eauto; listctx_set_simpl.
    + apply rtyR_env_cons1; eauto.
      eapply H; hauto.
    + apply rtyR_env_cons2; eauto.
      eapply H; hauto.
Qed.

Lemma stale_ctxOverBindings_tail_under: forall Γ x ρ,
is_under_base_rty ρ ->
stale (ctxOverBindings (Γ ++ [(x, ρ)])) = stale (ctxOverBindings Γ).
Proof.
  induction Γ; intros; listctx_set_simpl.
  - destruct ρ; simpl in *; hauto.
  - destruct r; simpl in *; eauto.
    all: ln_simpl; my_set_solver.
Qed.

Lemma stale_ctxOverBindings_tail_over: forall Γ x ρ,
~ is_under_base_rty ρ ->
stale (ctxOverBindings (Γ ++ [(x, ρ)])) = stale (ctxOverBindings Γ ∪ {[x]}).
Proof.
  induction Γ; intros; listctx_set_simpl.
  - destruct ρ; simpl in *; hauto.
  - destruct r; simpl in *; eauto.
    all: ln_simpl; my_set_solver.
Qed.

Lemma stale_ctxOverBindings_subset: forall Γ,
stale (ctxOverBindings Γ) ⊆ stale Γ.
Proof.
  induction Γ; intros; listctx_set_simpl.
  - hauto.
  - destruct r; ln_simpl; my_set_solver.
Qed.

Lemma wfEnv_ok_ctx: forall Γ,
wfEnv Γ ->
ok_ctx Γ.
Proof.
  induction 1; eauto. econstructor.
Qed.

(** * Properties of denotation *)

Lemma rtyR_typed_closed gas τ e :
  rtyR gas τ e ->
  ∅ ⊢ e ⋮ ⌊ τ ⌋ /\ stale τ = ∅ /\ lc τ.
Proof.
  destruct gas; hauto.
Qed.

Lemma rtyR_basic_typing gas ρ e :
  rtyR gas ρ e -> ∅ ⊢ e ⋮ ⌊ ρ ⌋.
Proof.
  destruct gas; hauto.
Qed.

Lemma rtyR_closed_tm gas ρ e :
  rtyR gas ρ e -> stale e = ∅.
Proof.
  intros H. apply rtyR_basic_typing in H.
  basic_typing_regular_simp. lc_set_solver.
Qed.

Lemma rtyR_lc gas ρ e :
  rtyR gas ρ e -> lc e.
Proof.
  intros H. apply rtyR_basic_typing in H.
  basic_typing_regular_simp.
Qed.

Lemma rtyR_regular gas ρ e : rtyR gas ρ e -> ∅ ⊢ e ⋮ ⌊ ρ ⌋ /\ stale e = ∅ /\ stale ρ = ∅ /\ lc ρ.
Proof.
  intuition.
  - apply rtyR_basic_typing in H; eauto.
  - apply rtyR_closed_tm in H; eauto.
  - apply rtyR_typed_closed in H. mydestr. set_solver.
  - apply rtyR_typed_closed in H. hauto.
Qed.

Lemma ctxEnv_domain Γ σ : ctxEnv Γ σ -> stale Γ = stale σ.
Proof.
  induction 1; ln_simpl; eauto.
  - ln_simpl. autounfold with class_simpl. 
  set_solver.
Qed.

Lemma ctxEnv_closed_env Γ σ : ctxEnv Γ σ -> closed_env σ.
Proof.
  induction 1.
  - apply map_Forall_empty.
  - apply ok_ctx_destruct_tail in H0; mydestr.
    apply map_Forall_insert; eauto.
    + apply ctxEnv_domain in H.
      assert (x # stale σ) by my_set_solver.
      ln_simpl. my_set_solver.
    + split; eauto.
      { apply rtyR_closed_tm in H1. ln_simpl; eauto. }
Qed.

Lemma ctxEnv_dom Γ σ : ctxEnv Γ σ -> stale Γ = stale σ.
Proof.
  intros H. induction H; subst; eauto.
  - ln_simpl. listctx_set_simpl. 
    rewrite IHctxEnv. lc_set_solver.
Qed.

Lemma ctxEnv_ok_ctx Γ Γv :
  ctxEnv Γ Γv -> ok_ctx Γ.
Proof.
  induction 1; eauto. econstructor.
Qed.

Lemma ctxEnv_regular Γ σ:
  ctxEnv Γ σ -> ok_ctx Γ /\ stale Γ = stale σ /\ closed_env σ.
Proof.
  pose ctxEnv_ok_ctx. pose ctxEnv_dom. pose ctxEnv_closed_env. intuition; eauto.
Qed.

Ltac denotation_regular_simp :=
  repeat match goal with
  | [H: ctxEnv _ _ |- _ ] => apply ctxEnv_regular in H; simp_hyp H
  | [H: rtyR _ _ _ |- _ ] => apply rtyR_regular in H; simp_hyp H
  end.

Lemma mk_top_lc b : lc (mk_top b).
Proof.
  econstructor. unshelve (repeat econstructor). exact ∅.
  my_set_solver.
Qed.

Lemma mk_top_denote_rty (b : base_ty) (v : value) :
  ∅ ⊢ v ⋮ (TBase b) ->
  ⟦ {: b | mk_q_under_top } ⟧ (treturn v).
Proof.
   assert (lc mk_q_under_top) by hauto.
   intros. split; [| split]; ln_simpl; eauto.
   basic_typing_solver.
   - econstructor; eauto. econstructor; eauto; simpl; eauto.
   lc_solver.
Qed.

(* Lemma mk_eq_constant_over_closed_rty c : closed_rty ∅ (mk_eq_constant_over c).
Proof.
  econstructor. unshelve (repeat econstructor). exact ∅.
  my_set_solver.
Qed. *)

(* 
Lemma mk_eq_constant_over_denote_rty c:
  ⟦ mk_eq_constant_over c ⟧ c.
Proof.
  simpl. split; [| split]; cbn; eauto using mk_eq_constant_over_closed_rty.
  exists c. intuition.
Qed. *)

Lemma closed_base_rty_qualifier_and B ϕ1 ϕ2 L:
  stale {: B | ϕ1 } ⊆ L ->
  stale {: B | ϕ2 } ⊆ L ->
  stale {: B | ϕ1 & ϕ2} ⊆ L.
Proof.
  intros. ln_simpl.
  rewrite qualifier_and_fv. my_set_solver.
Qed.

Lemma closed_base_rty_qualifier_and_eq B ϕ1 ϕ2 L:
  stale {: B | ϕ1 } = L ->
  stale {: B | ϕ2 } = L ->
  stale {: B | ϕ1 & ϕ2} = L.
Proof.
  intros. ln_simpl.
  rewrite qualifier_and_fv. my_set_solver.
Qed.

Lemma lc_rty_qualifier_and b ϕ1 ϕ2 :
  lc {: b | ϕ1 } ->
  lc {: b | ϕ2 } ->
  lc {: b | ϕ1 & ϕ2}.
Proof.
  intros Hlc1 Hlc2. sinvert Hlc1. sinvert Hlc2.
  econstructor; eauto.
  apply lc_phi1_and; eauto.
Qed.

Lemma denote_base_rty_qualifier_and B ϕ1 ϕ2 ρ:
  ⟦ {: B | ϕ1 } ⟧ ρ ->
  ⟦ {: B | ϕ2 } ⟧ ρ ->
  ⟦ {: B | ϕ1 & ϕ2} ⟧ ρ.
Proof.
  intros (?&?&?) (?&?&?).
  split; [| split]; eauto using closed_base_rty_qualifier_and_eq.
  simp_hyps; subst.
  split. 
  + apply lc_rty_qualifier_and; eauto.
  +
  exists v. intuition.
  rewrite qualifier_and_open.
  rewrite denote_qualifier_and.
  qauto.
Qed.

Ltac lia_simp :=
  repeat match goal with
    | [H: S _ = S _ |- _ ] => sinvert H
    end.

Ltac lia_tac :=
  repeat match goal with
  | [H: _ |- context [rty_measure (_ ^^ _)] ] => rewrite <- open_preserves_rty_measure
  | [H: _ |- _ <= _ ] => ln_simpl; lia
  end; eauto.

Ltac exist_tac :=
  match goal with
  | [H: exists x, _ |- exists _, _ ] =>
      let x := fresh x in
      destruct H as (x & H); exists x; intuition
  end.

Lemma rty_measure_flip: forall ρ, rty_measure (flip_rty ρ) = rty_measure ρ.
Proof.
  destruct ρ; eauto.
Qed.

Lemma rtyR_measure_irrelevant_aux: forall k ρ m n e,
    rty_measure ρ <= k ->
    k <= n ->
    k <= m ->
    rtyR n ρ e <-> rtyR m ρ e.
Proof.
  induction k; destruct ρ; intros m n e Hk Hn Hm;
    split; intro H; destruct m, n;
    try solve [sinvert Hm; sinvert Hn; sinvert Hk; eauto];
    try solve [lia_tac].
  - destruct H as (HT & Hclosed & H). simpl; intuition.
    exist_tac.
    destruct ρ1; intuition; do 2 rewrite <- (IHk _ _ n) in *; try lia_tac.
  - destruct H as (HT & Hclosed & H). simpl; intuition.
    exist_tac.
    destruct ρ1; intuition; do 2 rewrite (IHk _ m) in *; try lia_tac.
Qed.

(* The conclusion has to be strengthened to an equivalence to get around
termination checker. *)
Lemma rtyR_measure_irrelevant m n ρ e :
  rty_measure ρ <= n ->
  rty_measure ρ <= m ->
  rtyR n ρ e <-> rtyR m ρ e.
Proof.
  intros. eapply (rtyR_measure_irrelevant_aux (rty_measure ρ)); eauto.
Qed.

Lemma rtyR_measure_irrelevant' n ρ e :
  rty_measure ρ <= n ->
  rtyR n ρ e <-> ⟦ ρ ⟧ e.
Proof.
  intros. autounfold with class_simpl. unfold Denotation_rty. rewrite rtyR_measure_irrelevant; eauto.
Qed.

Ltac rewrite_measure_irrelevant :=
  let t := (rewrite <- ?open_preserves_rty_measure;
            simpl; lia) in
  match goal with
  | H : context [rtyR _ _ _] |- _ =>
      setoid_rewrite rtyR_measure_irrelevant' in H; [ | t .. ]
  | |- context [rtyR _ _ _] =>
      setoid_rewrite rtyR_measure_irrelevant'; [ | t .. ]
  end.

(* Ltac lc_solver_plus :=
  repeat (lc_solver_simp_aux || lc_basic_typing_simp_aux); eauto;
  (repeat lc_solver_plus_aux); eauto. *)

(* A machinery to simplify certain proofs *)
Definition tm_refine (T: ty) (e e': tm) :=
  ∅ ⊢ e' ⋮ T /\ ∅ ⊢ e ⋮ T /\ (forall (v : value), e ↪* (treturn v) -> e' ↪* (treturn v)).

Notation "e '⊑{' T '}' e'" := (tm_refine T e e') (at level 70, format "e ⊑{ T } e'", T constr, e constr, e' constr).

Hint Unfold Denotation_rty: class_simpl.

Lemma tm_refine_value_term (T: ty) (v: value) (e: tm) :
  (treturn v) ⊑{ T } e -> ∅ ⊢ e ⋮ T /\ e ↪* (treturn v).
Proof.
  unfold tm_refine. intros. ln_simpl. split; auto.
  assert (treturn v ↪* treturn v). {
    apply value_reduction_any_ctx.
    basic_typing_regular_simp. lc_solver.
  }
  hauto.
Qed.

Lemma tm_refine_value_value (T: ty) (v1 v2: value) :
  (treturn v1) ⊑{ T } (treturn v2) -> ∅ ⊢ v2 ⋮ T /\ v1 = v2.
Proof.
  intros H.
  apply tm_refine_value_term in H. mydestr.
  split; auto.
  - basic_typing_solver.
  - apply value_reduction_refl in H0. hauto.
Qed.

(* Semantic refinement preserves denotation. *)
Lemma tm_refine_denote_underbase_rty b ϕ (e e': tm) :
  e ⊑{ TBase b } e' ->
  ⟦ [: b | ϕ] ⟧ e ->
  ⟦ [: b | ϕ] ⟧ e'.
Proof.
  unfold tm_refine. intros. ln_simpl.
  split; [| split]; eauto.
Qed.

Ltac syntax_solver :=
  match goal with
  | [|- _ ⊢ _ ⋮ _] => denotation_regular_simp; basic_typing_solver
  | [|- lc _ ] => denotation_regular_simp; basic_typing_regular_simp; lc_set_solver
  | [|- body _ ] => denotation_regular_simp; basic_typing_regular_simp; lc_set_solver
  end.

Lemma tm_refine_tmatchb_true: forall (e1 e2: tm) T,
    ∅ ⊢ e1 ⋮ T ->
    ∅ ⊢ e2 ⋮ T ->
    e1 ⊑{ T } (tmatchb true e1 e2).
Proof.
  repeat split; eauto; try syntax_solver.
  - intros.
    repeat (econstructor; eauto); syntax_solver.
Qed.

Lemma tm_refine_tmatchb_false: forall e1 e2 T,
    ∅ ⊢ e1 ⋮ T ->
    ∅ ⊢ e2 ⋮ T ->
    e2 ⊑{ T } (tmatchb false e1 e2).
Proof.
  repeat split; eauto; try syntax_solver.
  - intros.
    repeat (econstructor; eauto); syntax_solver.
Qed.

(* Lemma tm_refine_mk_app (e1 e2 e_x: tm) T:
  tm_refine e1 e2 ->
  lc e_x ->
  ∅ ⊢ mk_app e2 e_x ⋮ T ->
  tm_refine (mk_app e1 e_x) (mk_app e2 e_x).
Proof.
  intros. destruct H as ((Te & HTe1 & HTe2) & H).
  split.
  - exists T. intuition.
    apply mk_app_has_type_inv in H1; auto.
    simp_hyps.
    eapply mk_app_has_type; eauto. unique_basic_type. auto.
  - intros.
    rewrite reduction_mk_app_iff in H2 by auto.
    simp_hyps.
    rewrite reduction_mk_app_iff by auto.
    repeat eexists; eauto.
Qed. *)

Lemma rtyR_env_ground_truth: forall L Γ,
  wfEnv Γ ->
  rtyR_env L Γ (fun σ1 σ2 => ⟦ Γ ⟧ (σ1 ∪ σ2) /\ stale σ1 = stale Γ ∩ (ctxOverBindings Γ ∪ L) /\ stale σ2 = stale Γ ∖ (ctxOverBindings Γ ∪ L)).
Proof.
  intros L.
  apply (rev_ind (fun Γ => wfEnv Γ -> rtyR_env L Γ (fun σ1 σ2 => ⟦ Γ ⟧ (σ1 ∪ σ2) /\ stale σ1 = stale Γ ∩ (ctxOverBindings Γ ∪ L) /\ stale σ2 = stale Γ ∖ (ctxOverBindings Γ ∪ L)))); intros; eauto.
  - econstructor. repeat split; eauto.
    + econstructor. 
    + ln_simpl. my_set_solver.
    + ln_simpl. my_set_solver.
  - destruct x as (x, ρ).
    assert (ok_ctx (l ++ [(x, ρ)])) by eauto using wfEnv_ok_ctx.
    assert (x ∉ stale l). {
      apply ok_ctx_destruct_tail in H1; mydestr; eauto.
    }
    pose proof (stale_ctxOverBindings_subset l).
    sinvert H0; eauto; listctx_set_simpl.
    destruct (decide (x ∉ L)).
    + apply rtyR_env_cons2; eauto.
      eapply (rtyR_env_proper); eauto.
      intros σ1 σ2 (HH1 & HH2 & HH3).
      assert (σ1 !! x = None). {
        apply ctxEnv_regular in HH1.
        ln_simpl. my_set_solver.
      }
      ospecialize (H8 _ HH1); eauto.
      destruct H8 as (v & HH8).
      eexists. repeat split; eauto.
      rewrite <- insert_union_r; eauto.
        econstructor; eauto.
      all: ln_simpl; setoid_rewrite stale_ctxOverBindings_tail_under; eauto;
      my_set_solver.
    + apply rtyR_env_cons1; eauto. hauto.
      eapply (rtyR_env_proper); eauto.
      intros σ1 σ2 (HH1 & HH2 & HH3) v Hv.
      assert (σ1 !! x = None). {
        apply ctxEnv_regular in HH1.
        ln_simpl. my_set_solver.
      }
      repeat split; eauto.
      rewrite <- insert_union_l; eauto.
      econstructor; eauto.
      all: ln_simpl; setoid_rewrite stale_ctxOverBindings_tail_under; eauto;
      destruct (decide (x ∈ L)); my_set_solver.
    + apply rtyR_env_cons1; eauto. hauto.
      eapply (rtyR_env_proper); eauto.
      intros σ1 σ2 (HH1 & HH2 & HH3) v Hv.
      assert (σ1 !! x = None). {
        apply ctxEnv_regular in HH1.
        ln_simpl. my_set_solver.
      }
      repeat split; eauto.
      rewrite <- insert_union_l; eauto.
      econstructor; eauto.
      all: ln_simpl; setoid_rewrite stale_ctxOverBindings_tail_over; eauto;
      ln_simpl; my_set_solver.
Qed.

Lemma rtyR_env_with_assumption: forall L Γ P,
  wfEnv Γ ->
  (forall σ1 σ2,
  ⟦ Γ ⟧ (σ1 ∪ σ2) ->
  stale σ1 = stale Γ ∩ (ctxOverBindings Γ ∪ L) ->
  stale σ2 = stale Γ ∖ (ctxOverBindings Γ ∪ L) ->
  (* stale σ1 ∩ stale σ2 = ∅ -> *)
  P σ1 σ2) ->
  rtyR_env L Γ P.
Proof.
  intros.
  eapply rtyR_env_proper.
  2: apply rtyR_env_ground_truth; eauto.
  hauto.
Qed.

Lemma rtyR_env_ground_truth_P: forall L Γ P,
  wfEnv Γ ->
  rtyR_env L Γ (fun σ1 σ2 => 
  ⟦ Γ ⟧ (σ1 ∪ σ2) ->
  stale σ1 = stale Γ ∩ (ctxOverBindings Γ ∪ L) ->
  stale σ2 = stale Γ ∖ (ctxOverBindings Γ ∪ L) ->
  P σ1 σ2) ->
  rtyR_env L Γ P.
Proof.
    intros L.
    apply (rev_ind 
    (fun Γ => forall P, wfEnv Γ -> 
    rtyR_env L Γ (fun σ1 σ2 => 
    ⟦ Γ ⟧ (σ1 ∪ σ2) ->
    stale σ1 = stale Γ ∩ (ctxOverBindings Γ ∪ L) ->
    stale σ2 = stale Γ ∖ (ctxOverBindings Γ ∪ L) ->
    P σ1 σ2) ->
    rtyR_env L Γ P)); intros; eauto.
    - sinvert H0; eauto; listctx_set_simpl. econstructor.
      apply H1. 
      + econstructor. 
      + ln_simpl. my_set_solver.
      + ln_simpl. my_set_solver.
    - destruct x as (x, ρ).
      assert (ok_ctx (l ++ [(x, ρ)])) by eauto using wfEnv_ok_ctx.
      assert (x ∉ stale l). {
        apply ok_ctx_destruct_tail in H2; mydestr; eauto.
      }
      pose proof (stale_ctxOverBindings_subset l).
      sinvert H1; eauto; listctx_set_simpl;
      destruct (decide (x ∉ L));
      sinvert H0; eauto; listctx_set_simpl.
      + hauto.
      + apply rtyR_env_cons1; eauto.
        eapply H; eauto. clear H.
        eapply rtyR_env_proper; eauto. clear H7.
        simpl.
        intros σ1 σ2 HH HHD HH1 HH2 v Hv. 
        assert (σ1 !! x = None). {
          apply ctxEnv_regular in HHD.
          mydestr. setoid_rewrite H0 in H3.
          autounfold with class_simpl in *.
          my_set_solver.
        }
        apply HH; eauto; clear HH.
        rewrite <- insert_union_l; eauto.
          econstructor; eauto.
        all: ln_simpl; setoid_rewrite stale_ctxOverBindings_tail_over; eauto;
        ln_simpl; my_set_solver.
      + apply rtyR_env_cons1; eauto.
        eapply H; eauto. clear H.
        eapply rtyR_env_proper; eauto. clear H7.
        simpl.
        intros σ1 σ2 HH HHD HH1 HH2 v Hv. 
        assert (σ1 !! x = None). {
          apply ctxEnv_regular in HHD.
          mydestr. setoid_rewrite H0 in H3.
          autounfold with class_simpl in *.
          my_set_solver.
        }
        apply HH; eauto; clear HH.
        rewrite <- insert_union_l; eauto.
          econstructor; eauto.
        all: ln_simpl; setoid_rewrite stale_ctxOverBindings_tail_under; eauto;
        destruct (decide (x ∈ L)); my_set_solver.
      + apply rtyR_env_cons1; eauto.
        eapply H; eauto. clear H.
        eapply rtyR_env_proper; eauto. clear H7.
        simpl.
        intros σ1 σ2 HH HHD HH1 HH2 v Hv. 
        assert (σ1 !! x = None). {
          apply ctxEnv_regular in HHD.
          mydestr. setoid_rewrite H0 in H3.
          autounfold with class_simpl in *.
          my_set_solver.
        }
        apply HH; eauto; clear HH.
        rewrite <- insert_union_l; eauto.
          econstructor; eauto.
        all: ln_simpl; setoid_rewrite stale_ctxOverBindings_tail_over; eauto;
        ln_simpl; my_set_solver. 
      + apply rtyR_env_cons2; eauto.
        eapply H; eauto. clear H.
        eapply rtyR_env_proper; eauto. clear H7.
        simpl.
        intros σ1 σ2 HH HHD HH1 HH2.
        assert (σ1 !! x = None). {
          apply ctxEnv_regular in HHD.
          mydestr. setoid_rewrite H0 in H3.
          autounfold with class_simpl in *.
          my_set_solver.
        }
        destruct HH as (v & Hv & HH). exists v.
        split; eauto.
        apply HH; eauto; clear HH.
        rewrite <- insert_union_r; eauto.
          econstructor; eauto.
        all: ln_simpl; setoid_rewrite stale_ctxOverBindings_tail_under; eauto;
        my_set_solver.
      + hauto.
      + hauto.
      + hauto.  
Qed.

Lemma rtyR_env_proper_plus: forall L Γ P1 P2,
  wfEnv Γ ->
  rtyR_env L Γ P1 ->
  (forall σ1 σ2, 
  ⟦ Γ ⟧ (σ1 ∪ σ2) ->
  stale σ1 = stale Γ ∩ (ctxOverBindings Γ ∪ L) ->
  stale σ2 = stale Γ ∖ (ctxOverBindings Γ ∪ L) ->
  P1 σ1 σ2 -> P2 σ1 σ2) ->
  rtyR_env L Γ P2.
Proof.
  intros.
  apply rtyR_env_ground_truth_P; eauto.
  eapply rtyR_env_proper.
  2: apply H0.
  hauto.
Qed.

Notation " Γ ⊨⟦ τ ⟧ e " := (rtyR_env (stale τ) Γ (fun σ1 σ2 => ⟦ m{ σ1 } τ ⟧ (m{ σ1 ∪ σ2 } e) )) (at level 20, format "Γ ⊨⟦ τ ⟧ e", Γ constr, τ constr, e constr).