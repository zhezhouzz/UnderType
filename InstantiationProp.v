From stdpp Require Import mapset.
From CT Require Import Syntax.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp Lc Denotation Typing.

Import BaseDef MyTactics Primitives Lang LangLc Qualifier OperationalSemantics BasicTyping BasicTypingProp Instantiation RtyLc Lc Denotation ListCtx Typing InstantiationLc.

Class MsubstPreservesClosed A `{Stale A} `{Subst value A} := msubst_preserves_closed :
forall Γ Γ' (ρ: A) (σ: env),
  ctxEnv Γ σ ->
  stale ρ ⊆ stale (Γ ++ Γ') ->
  stale (m{σ} ρ) ⊆ stale (Γ').
  
Lemma MsubstPreservesClosed_all
(A : Type)
(staleA : Stale A)
(substA : Subst value A)
(fv_of_msubst_closedA : @FvOfMsubstClosed A staleA substA)
: @MsubstPreservesClosed A staleA substA.
Proof.
  unfold MsubstPreservesClosed.
  intros Γ Γ' ρ σ HΓ Hρ.
  rewrite fv_of_msubst_closedA by eauto using ctxEnv_closed_env.
  ln_simpl.
  apply ctxEnv_dom in HΓ. rewrite HΓ in *.
  my_set_solver.
Qed.

#[global] Instance MsubstPreservesClosed_tm: MsubstPreservesClosed tm.
Proof.
  eapply MsubstPreservesClosed_all; typeclasses eauto.
Qed.

#[global] Instance MsubstPreservesClosed_value: MsubstPreservesClosed value.
Proof.
  eapply MsubstPreservesClosed_all; typeclasses eauto.
Qed.

#[global] Instance MsubstPreservesClosed_qualifier: MsubstPreservesClosed qualifier.
Proof.
  eapply MsubstPreservesClosed_all; typeclasses eauto.
Qed.

#[global] Instance MsubstPreservesClosed_rty: MsubstPreservesClosed rty.
Proof.
  eapply MsubstPreservesClosed_all; typeclasses eauto.
Qed.

Class MsubstPreservesClosedEmpty A `{Stale A} `{Subst value A} := msubst_preserves_closed_empty :
forall Γ (ρ: A) (σ: env),
  ctxEnv Γ σ ->
  stale ρ ⊆ stale Γ ->
  stale (m{σ} ρ) = ∅.
  
Lemma MsubstPreservesClosedEmpty_all
(A : Type)
(staleA : Stale A)
(substA : Subst value A)
(msubst_preserves_closedA : @MsubstPreservesClosed A staleA substA)
: @MsubstPreservesClosedEmpty A staleA substA.
Proof.
  unfold MsubstPreservesClosedEmpty.
  intros Γ ρ σ HΓ Hρ.
  pose proof (msubst_preserves_closedA Γ [] ρ σ HΓ) as H; eauto.
  listctx_set_simpl. ln_simpl. my_set_solver.
Qed.

#[global] Instance MsubstPreservesClosedEmpty_tm: MsubstPreservesClosedEmpty tm.
Proof.
  eapply MsubstPreservesClosedEmpty_all; typeclasses eauto.
Qed.

#[global] Instance MsubstPreservesClosedEmpty_value: MsubstPreservesClosedEmpty value.
Proof.
  eapply MsubstPreservesClosedEmpty_all; typeclasses eauto.
Qed.

#[global] Instance MsubstPreservesClosedEmpty_qualifier: MsubstPreservesClosedEmpty qualifier.
Proof.
  eapply MsubstPreservesClosedEmpty_all; typeclasses eauto.
Qed.

#[global] Instance MsubstPreservesClosedEmpty_rty: MsubstPreservesClosedEmpty rty.
Proof.
  eapply MsubstPreservesClosedEmpty_all; typeclasses eauto.
Qed.

Lemma msubst_preserves_rty_measure ρ: forall σ: env,
  rty_measure ρ = rty_measure (m{σ} ρ).
Proof.
  msubst_tac. qauto using subst_preserves_rty_measure.
Qed.

Lemma rtyR_msubst_insert_eq (σ: env) (ρ: rty) (v: tm) (x: atom) (u: value):
  closed_env σ ->
  stale u = ∅ ->
  σ !! x = None ->
  (⟦(m{ σ }) ρ⟧) v ->
  (⟦(m{ <[x:=u]> σ }) ρ⟧) v.
Proof.
  intros. rewrite_msubst_insert.
  rewrite subst_fresh. auto.
  select (⟦_⟧ _) (fun H => apply rtyR_typed_closed in H).
  simp_hyps.
  my_set_solver.
Qed.

Lemma ctx_erase_not_fv {A: Type} Γ (x y: atom) (r: A): x # ((y, r) :: Γ) -> x ≠ y /\ x ∉ stale Γ.
Proof.
  intros. ln_simpl. my_set_solver.
Qed.

Lemma ctx_erase_empty: ⌊[]⌋* = ∅.
Proof.
  unfold erase_ctx. simplify_map_eq. reflexivity.
Qed.

Lemma flip_rty_erase_msubst_eq τ: ⌊flip_rty τ⌋ = ⌊τ⌋.
Proof.
  induction τ; simpl; eauto.
Qed.

Ltac simplify_erase_aux1 :=
  match goal with
  | [H: context [ ⌊ flip_rty _ ⌋ ] |- _ ] => setoid_rewrite ->flip_rty_erase_msubst_eq in H
  | [H: _ |- context [ ⌊ flip_rty _ ⌋ ]] => setoid_rewrite ->  flip_rty_erase_msubst_eq
  | [H: context [ ⌊ m{_} _ ⌋ ] |- _ ] => setoid_rewrite <- rty_erase_msubst_eq in H 
    | [H: _ |- context [ ⌊ m{_} _ ⌋ ]] => setoid_rewrite <- rty_erase_msubst_eq
  | [H: context [ ⌊[]⌋* ] |- _ ] => rewrite ctx_erase_empty in H
  | [|- ⌊[]⌋* = _ ] => rewrite ctx_erase_empty
  | [|- _ !! _ = None] => apply not_elem_of_dom; fold_syntax_class
  | [H: context [ stale (⌊ _ ⌋*) ] |- _ ] => rewrite ctx_erase_dom in H
  | [|- context [ stale (⌊ _ ⌋*) ] ] => rewrite ctx_erase_dom
  | [H: context [ _ # (⌊ _ ⌋*) ] |- _ ] => 
    rewrite ctx_erase_dom in H by eauto
  | [|- context [ _ # (⌊ _ ⌋*) ] ] => rewrite ctx_erase_dom by eauto
  | [H: context [ ⌊_ :: ?Γ⌋* ] |- _ ] => rewrite ctx_erase_cons in H by eauto
  | [|- context [ ⌊_ :: ?Γ⌋* ] ] => rewrite ctx_erase_cons by eauto
  | [H: context [ ⌊?Γ ++ [_]⌋* ] |- _ ] => rewrite ctx_erase_app_r in H by eauto
  | [|- context [ ⌊?Γ ++ [_]⌋* ] ] => rewrite ctx_erase_app_r by eauto
  | [H: context [ ⌊?Γ ++ ?Γ'⌋* ] |- _ ] => rewrite ctx_erase_app in H by eauto
  | [|- context [ ⌊?Γ ++ ?Γ'⌋* ] ] => rewrite ctx_erase_app by eauto
  | _ => my_map_simpl_aux
  end.

Ltac simplify_erase1 :=
  mydestr;
  repeat (simplify_erase_aux1; eauto).

Lemma ctx_erase_lookup_none:
forall (Γ : listctx rty) (x : atom), x # Γ -> ⌊Γ⌋* !! x = None.
Proof.
  induction Γ; intros; simpl; try easy.
  simplify_erase1.
Qed.

(* Ltac simplify_erase_aux2 :=
  match goal with
  (* | [H: ?x # ((_, _) :: _) |- ?x # _] => apply ctx_erase_not_fv in H; mydestr *)
  end. *)

(* Ltac simplify_erase :=
  listctx_set_simpl;
  repeat simplify_erase_aux. *)

Ltac apply_rev_ind :=
    intros_until (listctx rty);
    lazymatch goal with
    | |- forall Γ : listctx rty, ?body =>
        let P := constr:(fun Γ : listctx rty => body) in
        apply (List.rev_ind P); intros
    end.

Lemma ctxEnv_destruct_tail Γ (σ: env) x r:
  ctxEnv (Γ ++ [(x, r)]) σ ->
  exists (v: value) (σ': env), σ = <[x:=v]> σ' /\ ctxEnv Γ σ' /\ (⟦(m{σ'}) (flip_rty r)⟧) (treturn v) /\ ok_ctx (Γ ++ [(x, r)]).
Proof.
  intros. sinvert H.
  - listctx_set_solver.
  - listctx_set_simpl. exists v, σ0. intuition.
Qed.

Ltac set_simp_aux :=
  match goal with
     | [H: ⟦ _ ⟧ _ |- stale _ = _ ] => apply rtyR_typed_closed in H; simp_hyp H
     | [H: ⟦ _ ⟧ _ |- _ !! _ = _ ] => apply rtyR_typed_closed in H; simp_hyp H
     | [H: ⟦ _ ⟧ _ |- _ # _ ] => apply rtyR_typed_closed in H; simp_hyp H
     | [H: _ ⊢r _ ⋮ _ |- stale _ = _ ] => apply refinement_typing_regular in H
     | [H: _ ⊢ _ ⋮ _ |- stale _ = _ ] => apply fv_subset_gamma in H
     end.

Ltac set_simp := repeat set_simp_aux.

Ltac rtyR_regular_simp_aux :=
  match goal with
     | [H: _ ⊢r _ ⋮ _ |- _ ⊢ _ ⋮ _ ] => apply refinement_typing_regular_basic_typing in H
     | [H: ctxEnv _ _ |- lc _ ] => apply ctxEnv_regular in H; simp_hyp H
     | [H: ctxEnv _ _ |- closed_env _ ] => apply ctxEnv_regular in H; simp_hyp H
     | [H: ctxEnv _ _ |- ok_ctx _ ] => apply ctxEnv_regular in H; simp_hyp H; eauto
     | [H: ctxEnv _ _ |- _ ∉ _ ] => apply ctxEnv_regular in H; simp_hyp H; eauto
     | [H: ctxEnv _ _ |- _ # _ ] => apply ctxEnv_regular in H; simp_hyp H; eauto
     | [H: ctxEnv _ _ |- _ ⊆ _ ] => apply ctxEnv_regular in H; eauto; simp_hyp H
     | [H: ctxEnv _ _ |- fine_rty _ ] => apply ctxEnv_regular in H; eauto; simp_hyp H
     | [H: ctxEnv _ _ |- stale _ = _ ] => apply ctxEnv_regular in H; eauto; simp_hyp H
     | [H: ctxEnv _ _ |- _ !! _ = _ ] => apply ctxEnv_regular in H; eauto; simp_hyp H
     | [H: ctxEnv _ ?Γv |- map_Forall _ ?Γv] => apply ctxEnv_regular in H; eauto
     | [H: ok_ctx _ |- ok _ ] => apply ok_ctx_regular in H; simp_hyp H; eauto
     | [H: ok_ctx _ |- _ !! _ = _ ] => apply ok_ctx_regular in H; simp_hyp H; eauto
     | [H: ok_ctx _ |- _ # _ ] => apply ok_ctx_regular in H; simp_hyp H; eauto
     | [H: ok_ctx _ |- _ ⊆ _ ] => apply ok_ctx_regular in H; simp_hyp H; eauto
     | [H: ok_ctx _ |- fine_rty _ ] => apply ok_ctx_regular in H; simp_hyp H; eauto
     | [H: ok_ctx _ |- stale _ = _ ] => apply ok_ctx_regular in H; simp_hyp H; eauto
     | [H: ⟦ _ ⟧ _  |- lc _ ] => 
       try apply rtyR_regular in H; try apply ctxEnv_regular in H; simp_hyp H
     | [H: ⟦ _ ⟧ _  |- _ ⊆ _ ] => 
       try apply rtyR_regular in H; try apply ctxEnv_regular in H; eauto; simp_hyp H
     | [H: ⟦ _ ⟧ _  |- stale _ = _ ] => 
       try apply rtyR_regular in H; try apply ctxEnv_regular in H; eauto; simp_hyp H
     | [H: ⟦ _ ⟧ _  |- _ !! _ = _ ] => 
       try apply rtyR_regular in H; try apply ctxEnv_regular in H; eauto; simp_hyp H
     | [H: ⟦ _ ⟧ _  |- ok_ctx _ ] => 
       try apply rtyR_regular in H; try apply ctxEnv_regular in H; eauto; simp_hyp H
     | [H: ⟦ _ ⟧ _  |- _ ∉ _ ] => 
       try apply rtyR_regular in H; try apply ctxEnv_regular in H; eauto; simp_hyp H
     | [H: ⟦ _ ⟧ _  |- _ ⊆ _ ] => 
       try apply rtyR_regular in H; try apply ctxEnv_regular in H; eauto; simp_hyp H
     | [H: ⟦ _ ⟧ _  |- stale _ = _ ] => 
       try apply rtyR_regular in H; try apply ctxEnv_regular in H; eauto; simp_hyp H
     | [H: ⟦ _ ⟧ _  |- _ # _ ] => 
       try apply rtyR_regular in H; try apply ctxEnv_regular in H; eauto; simp_hyp H
     | [H: ⟦ _ ⟧ _  |- closed_env _ ] => 
       try apply rtyR_regular in H; try apply ctxEnv_regular in H; eauto; simp_hyp H
     | [H: ⟦ _ ⟧ _  |- ok_ctx _ ] => 
       try apply rtyR_regular in H; try apply ctxEnv_regular in H; eauto; simp_hyp H
     | [H: ⟦ _ ⟧ _  |- _ ⊢ _ ⋮ _ ] => apply rtyR_typed_closed in H; simp_hyp H
     end.

Ltac rtyR_regular_simp :=
  repeat rtyR_regular_simp_aux.

Class MsubstPreservesBasicTyping A `{Stale A} `{Subst value A} `{Typing (amap ty) A ty} := msubst_preserves_basic_typing :
  forall Γ (σ: env),
    ctxEnv Γ σ ->
    forall Γ' (e: A) T,
      (⌊Γ⌋* ∪ Γ') ⊢ e ⋮ T ->
      Γ' ⊢ m{σ} e ⋮ T.

Lemma MsubstPreservesBasicTyping_all
(A : Type)
(staleA : Stale A)
(substA : Subst value A)
(typingA : @Typing (amap ty) A ty)
(msubst_insertA : @MsubstInsert A substA)
(basic_typing_substA : @BasicTypingSubst A typingA substA)
: @MsubstPreservesBasicTyping A staleA substA typingA.
Proof.
  unfold MsubstPreservesBasicTyping.
  induction 1; intros; eauto.
  - simplify_erase1.
  - apply ok_ctx_destruct_tail in H0. mydestr.
    simplify_erase1.
  rewrite_msubst_insert.
  apply basic_typing_substA with (U := ⌊τ⌋); eauto.
  apply rtyR_regular in H1. mydestr.
  + rtyR_regular_simp. simplify_erase1. basic_typing_solver.
  + 
  apply IHctxEnv; eauto.
  rewrite insert_union_singleton_r in H2.
  setoid_rewrite insert_union_singleton_l.
  rewrite map_union_assoc. 
  eauto.
  simplify_erase1.
  + rtyR_regular_simp; eauto.
  + rtyR_regular_simp. lc_set_solver.
  + rtyR_regular_simp. simplify_erase1. 
    autounfold with class_simpl in *. hauto. 
Qed.

#[global] Instance MsubstPreservesBasicTyping_tm: MsubstPreservesBasicTyping tm.
Proof.
  eapply MsubstPreservesBasicTyping_all; typeclasses eauto.
Qed.

#[global] Instance MsubstPreservesBasicTyping_value: MsubstPreservesBasicTyping value.
Proof.
  eapply MsubstPreservesBasicTyping_all; typeclasses eauto.
Qed.

Class MsubstPreservesBasicTypingEmpty A `{Stale A} `{Subst value A} `{Typing (amap ty) A ty} := msubst_preserves_basic_typing_empty :
  forall Γ (σ: env),
    ctxEnv Γ σ ->
    forall e T,
    ( ⌊Γ⌋* ) ⊢ e ⋮ T ->
    ∅ ⊢ m{σ} e ⋮ T.

Lemma MsubstPreservesBasicTypingEmpty_all
(A : Type)
(staleA : Stale A)
(substA : Subst value A)
(typingA : @Typing (amap ty) A ty)
(msubst_preserves_basic_typingA : @MsubstPreservesBasicTyping A staleA substA typingA)
: @MsubstPreservesBasicTypingEmpty A staleA substA typingA.
Proof.
  unfold MsubstPreservesBasicTypingEmpty.
  intros. eapply msubst_preserves_basic_typingA; eauto.
  my_map_simpl; eauto.
Qed.

#[global] Instance MsubstPreservesBasicTypingEmpty_tm: MsubstPreservesBasicTypingEmpty tm.
Proof.
  eapply MsubstPreservesBasicTypingEmpty_all; typeclasses eauto.
Qed.

#[global] Instance MsubstPreservesBasicTypingEmpty_value: MsubstPreservesBasicTypingEmpty value.
Proof.
  eapply MsubstPreservesBasicTypingEmpty_all; typeclasses eauto.
Qed.

From Stdlib Require Import Logic.ClassicalFacts.
From Stdlib Require Import Classical.
From Stdlib Require Import Arith.Compare_dec.

Lemma msubst_fvar_inv v (x : atom): forall (σ : env),
  closed_env σ ->
  m{σ} v = (treturn (vfvar x)) ->
  v = (treturn (vfvar x)) /\ x ∉ dom σ.
Proof.
  msubst_tac; fold_msubst. set_solver.
  rewrite <- H0 in H3.
  destruct v; repeat msubst_simp; inversion H3; subst.
  destruct v; repeat msubst_simp; inversion H3; subst.
  - destruct (<[i:=x0]> m !! atom) eqn: Hx.
    + exfalso. unfold closed_env in H2.
      eapply map_Forall_lookup_1 in H2; eauto.
      ln_simpl. simplify_map_eq.
    + split; auto. inversion H3. subst. apply not_elem_of_dom in Hx. eauto.
Qed.

Class MsubstDestructRev A `{Stale A} `{Subst value A} := msubst_destruct_rev :
  forall (σ: env) (x: atom) (v_x: value) (e: A),
    closed_env σ -> 
    stale v_x = ∅ -> 
    x # σ ->
    (m{<[x:=v_x]> σ}) e = m{σ} ({ x:=v_x } e).

Lemma MsubstDestructRev_all
(A : Type)
(staleA : Stale A)
(substA : Subst value A)
(msubst_insertA : @MsubstInsert A substA)
(subst_commuteA : @SubstCommute A staleA substA)
: @MsubstDestructRev A staleA substA.
Proof.
  unfold MsubstDestructRev.
  intros.
  rewrite_msubst_insert.
  2 : { my_set_solver. }
  revert_all.
  msubst_tac.
  setoid_rewrite <- H1; eauto.
  2: { my_set_solver. }
  rewrite subst_commuteA by my_set_solver; eauto.
Qed.

#[global] Instance MsubstDestructRev_tm: MsubstDestructRev tm.
Proof.
  eapply MsubstDestructRev_all; typeclasses eauto.
Qed.

#[global] Instance MsubstDestructRev_value: MsubstDestructRev value.
Proof.
  eapply MsubstDestructRev_all; typeclasses eauto.
Qed.

#[global] Instance MsubstDestructRev_qualifier: MsubstDestructRev qualifier.
Proof.
  eapply MsubstDestructRev_all; typeclasses eauto.
Qed.

#[global] Instance MsubstDestructRev_rty: MsubstDestructRev rty.
Proof.
  eapply MsubstDestructRev_all; typeclasses eauto.
Qed.

Lemma is_coverage_rty_msubst_aux n : forall τ, rty_measure τ <= n ->
                                         forall σ, closed_env σ -> is_coverage_rty (m{ σ } τ) <-> is_coverage_rty τ.
Proof.
  induction n; split; intros Hm; simpl; intros; repeat msubst_simp; simp_hyps; eauto;
  try solve [pose (rty_measure_gt_0 τ); lia].
  - destruct τ; eauto; repeat msubst_simp; simp_hyps; sinvert Hm; eauto;
  destruct τ1; eauto; repeat msubst_simp; simp_hyps; eauto; econstructor;
  try solve [eapply H2; eauto; simpl in *; repeat msubst_simp; eauto; hauto].
  - destruct τ; eauto; repeat msubst_simp; simp_hyps; sinvert Hm; eauto;
  repeat msubst_simp; simp_hyps; eauto; econstructor; repeat msubst_simp;
  try solve [auto_apply; eauto; simpl in *; repeat msubst_simp; eauto; hauto].
  rewrite <- msubst_arrrty by eauto. apply H1; eauto. simpl in *. lia.
Qed.

Lemma is_coverage_rty_msubst: forall τ σ, closed_env σ -> is_coverage_rty (m{ σ } τ) <-> is_coverage_rty τ.
Proof. eauto using is_coverage_rty_msubst_aux. Qed.

Lemma fine_rty_msubst: forall τ σ, closed_env σ -> fine_rty (m{ σ } τ) <-> fine_rty τ.
Proof.
  split; destruct τ; intros; repeat msubst_simp; simp_hyps; eauto; simpl in *.
  - erewrite <- is_coverage_rty_msubst; eauto. repeat msubst_simp; simp_hyps; eauto.
  - erewrite <- is_coverage_rty_msubst in H0; eauto. repeat msubst_simp; simp_hyps; eauto.
Qed.

(* Lemma closed_rty_base_flip: forall L b ϕ, closed_rty L {:b|ϕ} <-> closed_rty L [:b|ϕ].
Proof.
  split; intros; sinvert H; econstructor; eauto;
  rewrite lc_base_flip in *; eauto.
Qed. *)


Ltac msubst_simp_tac_aux :=
  match goal with
          | [H: context [ stale (m{_} ?τ) ] |- _ ] => rewrite fv_of_msubst_closed in H by eauto
          | [H: _ |- context [ stale (m{_} ?τ) ] ] => rewrite fv_of_msubst_closed by eauto
          | [H: context [ fine_rty (m{_} ?τ) ] |- _ ] => setoid_rewrite fine_rty_msubst in H
          | [H: _ |- context [ fine_rty (m{_} ?τ) ] ] => setoid_rewrite fine_rty_msubst
          | [H: context [ is_coverage_rty (m{_} ?τ) ] |- _ ] => setoid_rewrite is_coverage_rty_msubst in H
          | [H: _ |- context [ is_coverage_rty (m{_} ?τ) ] ] => setoid_rewrite is_coverage_rty_msubst
          | _ => msubst_simp
          end.

Ltac simp_tac_aux :=
match goal with
| [|- closed_env _ ] =>
first [rtyR_regular_simp_aux | lc_basic_typing_simp_aux | set_simp_aux | simplify_erase_aux1 ]
| _ =>
first [rtyR_regular_simp_aux | msubst_simp_tac_aux | lc_basic_typing_simp_aux | set_simp_aux |simplify_erase_aux1 ]
end.

Ltac simp_tac := repeat simp_tac_aux.

Ltac misc_solver :=
  simp_tac;
  ln_simpl;
  simplify_map_eq;
  eauto;
  try solve [try basic_typing_solver; try fine_rty_solver; try ok_solver; try lc_set_solver].