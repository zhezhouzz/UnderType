From stdpp Require Import mapset.
From stdpp Require Import natmap.
From Stdlib.Program Require Import Wf.
From CT Require Import Syntax Lc.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import Denotation.

Import BaseDef Lang MyTactics Primitives OperationalSemantics BasicTyping Qualifier RefinementType Instantiation ListCtx List LangLc Lc QualifierLc Denotation.


(** This file formalizes the type system of λᴱ and the main metatheoretic
  results. *)

(** Well-formedness (Fig. 5) *)


Notation " Γ '⊢WF' τ " := (lc τ /\ stale τ ⊆ stale Γ /\ is_coverage_rty τ) (at level 20, τ constr, Γ constr).

(** Semantic subtyping *)
(* Instead of the syntactic subtyping relation presented in the paper, we use
semantic subtyping in the mechanization. *)
(* Definition subtyping (Γ: listctx rty) (ρ1 ρ2: rty) : Prop :=
  (* Assume [ρ1] and [ρ2] are valid [rty]s. *)
  ⌊ ρ1 ⌋ = ⌊ ρ2 ⌋ /\ (is_coverage_rty ρ1 <-> is_coverage_rty ρ2) /\
    forall (σ1: env), ⟦ Γ ⟧ σ1 ->
    exists (σ2: env), ⟦ Γ ⟧ σ2 /\ σ1 ={ ctxOverBindings Γ } σ2 /\
      (forall (e: tm), ⟦m{ σ1 } ρ1⟧ e -> ⟦m{ σ2 } ρ2⟧ e). *)

Definition subtyping (Γ: listctx rty) (ρ1 ρ2: rty) : Prop :=
      (* Assume [ρ1] and [ρ2] are valid [rty]s. *)
      ⌊ ρ1 ⌋ = ⌊ ρ2 ⌋ /\ 
      (is_coverage_rty ρ1 <-> is_coverage_rty ρ2) /\
        forall (σ2: env), ⟦ Γ ⟧ σ2 ->
        exists (σ1: env), ⟦ Γ ⟧ σ1 /\ 
        [D ctxOverBindings Γ ∪ stale ρ2 ] σ1 = [D ctxOverBindings Γ ∪ stale ρ2 ] σ2 /\
          (forall (e: tm), ⟦m{ σ1 } ρ1⟧ e -> ⟦m{ σ2 } ρ2⟧ e).

Notation " Γ '⊢' τ1 '<⋮' τ2 " := (subtyping Γ τ1 τ2) (at level 20, τ1 constr, τ2 constr, Γ constr).

Definition join (Γ: listctx rty) (ρ1 ρ2 ρ3: rty) : Prop :=
  (* Assume [ρ1] and [ρ2] are valid [rty]s. *)
  ⌊ ρ1 ⌋ = ⌊ ρ2 ⌋ /\ ⌊ ρ1 ⌋ = ⌊ ρ3 ⌋ /\
    (is_coverage_rty ρ1 <-> is_coverage_rty ρ2) /\ 
    (is_coverage_rty ρ1 <-> is_coverage_rty ρ3) /\
    forall (e: tm) (σ: env), ⟦ Γ ⟧ σ -> ⟦m{ σ } ρ3⟧ e <-> ⟦m{ σ } ρ1⟧ e /\ ⟦m{ σ } ρ2⟧ e.

Notation " Γ '⊢' τ1 '⋮merge' τ2 '⋮=' τ3" := (join Γ τ1 τ2 τ3) (at level 20, τ1 constr, τ2 constr, τ3 constr, Γ constr).

(* The builtin typing relation (Δ) that our type system is parameterized over. *)
Parameter builtin_typing_relation : effop -> rty -> Prop.

Class TypingRefinement G E T := has_refinement_type : G -> E -> T -> Prop.

Notation "Γ '⊢r' e '⋮' T" := (has_refinement_type Γ e T) (at level 20, e constr, T constr, Γ constr).

(** * Typing rules (Fig. 6) *)

Inductive effop_type_check : listctx rty -> effop -> rty -> Prop :=
| TEOp : forall Γ op ρ_op ρ,
    Γ ⊢WF ρ ->
    builtin_typing_relation op ρ_op ->
    stale ρ_op = ∅ ->
    (* [TSubEOp] is inlined here. Consecutive applications of subtyping is just
    one subtyping. *)
    Γ ⊢ ρ_op <⋮ ρ ->
    ⌊ ρ ⌋ = ty_of_op op ->
    Γ ⊢ op ⋮ ρ.

#[global] Instance TypingRefinement_effop: TypingRefinement (listctx rty) effop rty := effop_type_check.

(** Typing rules for values and terms. Values always have refinement types, while
  terms always have Hoare automata types. *)
Inductive term_type_check : listctx rty -> tm -> rty -> Prop :=
| TErr: forall Γ (b: base_ty), 
  Γ ⊢WF (mk_bot b) -> term_type_check Γ (terr b) (mk_bot b)
| TValue: forall Γ v τ,
  value_type_check Γ v τ -> Γ ⊢r (treturn v) ⋮ τ
| TSub: forall Γ (e: tm) (τ1 τ2: rty),
    Γ ⊢WF τ2 ->
    term_type_check [] e τ1 ->
    [] ⊢ τ1 <⋮ τ2 ->
    term_type_check Γ e τ2
| TMerge: forall Γ e (τ1 τ2 τ3: rty),
    Γ ⊢WF τ3 ->
    term_type_check Γ e τ1 ->
    term_type_check Γ e τ2 ->
    Γ ⊢ τ1 ⋮merge τ2 ⋮= τ3 ->
    stale e ⊆ ctxOverBindings Γ ->
    term_type_check Γ e τ3
| TLetE: forall Γ e1 e2 τ1 τ2 (L: aset),
    (forall x, x ∉ L -> term_type_check (Γ ++ [(x, τ1)]) (e2 ^^ (vfvar x)) τ2) ->
    Γ ⊢WF τ2 ->
    term_type_check Γ e1 τ1 ->
    term_type_check Γ (tlete e1 e2) τ2
| TAppOverParam: forall Γ (v1 v2: value) e b ϕ τ1 τ2 (L: aset),
    (forall x, x ∉ L -> 
      term_type_check (Γ ++ [(x, τ1 ^^ v2)]) (e ^^ (vfvar x)) τ2) ->
    Γ ⊢WF τ2 ->
    value_type_check Γ v2 [:b | ϕ] ->
    value_type_check Γ v1 ({:b | ϕ} ⇨ τ1) ->
    term_type_check Γ (tletapp v1 v2 e) τ2
| TAppFuncParam: forall Γ (v1 v2: value) e ρ1 ρ2 τ1 τ2 (L: aset),
    (forall x, x ∉ L -> 
      term_type_check (Γ ++ [(x, τ1 ^^ v2)]) (e ^^ (vfvar x)) τ2) ->
    Γ ⊢WF τ2 ->
    value_type_check Γ v2 (ρ1 ⇨ ρ2) ->
    value_type_check Γ v1 ((ρ1 ⇨ ρ2) ⇨ τ1) ->
    term_type_check Γ (tletapp v1 v2 e) τ2
| TAppOp: forall Γ (op: effop) (v2: value) e b ϕ b1 ϕ1 τ2 (L: aset),
    (forall x, x ∉ L -> 
      term_type_check (Γ ++ [(x, [: b1 | ϕ1] ^^ v2)]) (e ^^ (vfvar x)) τ2) ->
    Γ ⊢WF τ2 ->
    value_type_check Γ v2 [: b | ϕ] ->
    Γ ⊢r op ⋮ ({: b | ϕ} ⇨ [: b1 | ϕ1]) ->
    term_type_check Γ (tleteffop op v2 e) τ2
| TMatchbTrue: forall Γ (v: value) e1 e2 ϕ τ (L : aset),
    Γ ⊢WF τ ->
    value_type_check Γ v [:TBool | ϕ] ->
    ⌊ Γ ⌋* ⊢ e2 ⋮ ⌊τ⌋ ->
    (forall x, x ∉ L -> 
      term_type_check (Γ ++ [(x, [: TBool | b0:c=true & b0:v= v & ϕ])]) e1 τ) ->
    term_type_check Γ (tmatchb v e1 e2) τ
| TMatchbFalse: forall Γ (v: value) e1 e2 ϕ τ (L : aset),
    Γ ⊢WF τ ->
    value_type_check Γ v [:TBool | ϕ] ->
    ⌊ Γ ⌋* ⊢ e1 ⋮ ⌊τ⌋ ->
    (forall x, x ∉ L -> 
      term_type_check (Γ ++ [(x, [: TBool | b0:c=false & b0:v= v & ϕ])]) e2 τ) ->
    term_type_check Γ (tmatchb v e1 e2) τ
with value_type_check : listctx rty -> value -> rty -> Prop :=
| TSubPP: forall Γ (v: value) (ρ1 ρ2: rty),
    Γ ⊢WF ρ2 ->
    value_type_check [] v ρ1 ->
    [] ⊢ ρ1 <⋮ ρ2 ->
    value_type_check Γ v ρ2
| TConst: forall Γ (c: constant),
    Γ ⊢WF (mk_eq_constant c) ->
    value_type_check Γ (vconst c) (mk_eq_constant c)
| TBaseVar: forall Γ (x: atom) b ϕ,
    Γ ⊢WF (mk_eq_var b x) ->
    ctxfind Γ x = Some {: b | ϕ} ->
    value_type_check Γ (vfvar x) (mk_eq_var b x)
| TFuncVar: forall Γ (x: atom) ρ τ,
    Γ ⊢WF (ρ ⇨ τ) ->
    ctxfind Γ x = Some (ρ ⇨ τ) ->
    value_type_check Γ (vfvar x) (ρ ⇨ τ)
| TFun: forall Γ Tx ρ e τ (L: aset),
    Γ ⊢WF (ρ ⇨ τ) ->
    (forall x, x ∉ L -> 
      term_type_check (Γ ++ [(x, ρ)]) (e ^^ (vfvar x)) (τ ^^ (vfvar x))) ->
    Tx = ⌊ ρ ⌋ ->
    value_type_check Γ (vlam Tx e) (ρ ⇨ τ)
| TFix: forall Γ (Tx : base_ty) ϕ e τ T (L: aset),
    Γ ⊢WF ({: Tx | ϕ} ⇨ τ) ->
    (* NOTE: should not open the whole type, because the first argument (bound *)
(*     variable 0) of the return type is not the fixed point function but [{: Tx | *)
(*     ϕ}]. The return type should be opened by [x]. *)
    (forall x, x ∉ L ->
          value_type_check (Γ ++ [(x, {: Tx | ϕ})]) ((vlam (Tx ⤍ T) e) ^^ (vfvar x)) (({: Tx | b0:x≺ x & ϕ} ⇨ τ) ⇨ (τ ^^ (vfvar x)))) ->
    T = ⌊ τ ⌋ ->
    value_type_check Γ (vfix (Tx ⤍ T) (treturn (vlam (Tx ⤍ T) e))) ({: Tx | ϕ} ⇨ τ).

Scheme value_term_type_check_ind := Minimality for value_type_check Sort Prop
    with term_value_type_check_ind := Minimality for term_type_check Sort Prop.
Combined Scheme value_term_type_check_mutind from
  value_term_type_check_ind, term_value_type_check_ind.

#[global] Instance TypingRefinement_value: TypingRefinement (listctx rty) value rty := value_type_check.

#[global] Instance TypingRefinement_tm: TypingRefinement (listctx rty) tm rty := term_type_check.

(** * Properties of the type system *)

Lemma subtyping_preserves_basic_typing Γ τ1 τ2 :
  Γ ⊢ τ1 <⋮ τ2 ->
  ⌊τ1⌋ = ⌊τ2⌋.
Proof.
  qauto.
Qed.

Lemma rty_subtyping_preserves_basic_typing Γ ρ1 ρ2 :
  Γ ⊢ ρ1 <⋮ ρ2 ->
  ⌊ρ1⌋ = ⌊ρ2⌋.
Proof.
  qauto.
Qed.

Lemma subtyping_preserves_is_coverage_rty Γ τ1 τ2 :
  Γ ⊢ τ1 <⋮ τ2 -> is_coverage_rty τ1 <-> is_coverage_rty τ2.
Proof.
  qauto.
Qed.


Lemma effop_typing_preserves_basic_typing Γ ρ op :
  Γ ⊢r op ⋮ ρ ->
  ⌊ρ⌋ = ty_of_op op.
Proof.
  inversion 1; subst. eauto.
Qed.

Lemma value_typing_regular_wf : forall (Γ: listctx rty) (v: value) (ρ: rty),
    Γ ⊢r v ⋮ ρ -> Γ ⊢WF ρ
with tm_typing_regular_wf : forall (Γ: listctx rty) (e: tm) (τ: rty),
    Γ ⊢r e ⋮ τ -> Γ ⊢WF τ.
Proof.
  all: destruct 1; eauto.
Qed.

Lemma value_tm_typing_regular_is_coverage_rty:
  (forall (Γ: listctx rty) (v: value) (ρ: rty),
      Γ ⊢r v ⋮ ρ -> is_coverage_rty ρ) /\
    (forall (Γ: listctx rty) (e: tm) (τ: rty),
        Γ ⊢r e ⋮ τ -> is_coverage_rty τ).
Proof.
  split; intros.
  - apply value_typing_regular_wf in H; intuition.
  - apply tm_typing_regular_wf in H; intuition.
Qed.

Lemma value_tm_typing_regular_basic_typing:
  (forall (Γ: listctx rty) (v: value) (ρ: rty),
    Γ ⊢r v ⋮ ρ -> ⌊ Γ ⌋* ⊢ v ⋮ ⌊ ρ ⌋) /\
  (forall (Γ: listctx rty) (e: tm) (τ: rty),
    Γ ⊢r e ⋮ τ -> ⌊ Γ ⌋* ⊢ e ⋮ ⌊ τ ⌋).
Proof.
  apply value_term_type_check_mutind; intros; cbn; subst; eauto.
  - apply rty_subtyping_preserves_basic_typing in H2. rewrite H2 in *.
    unfold erase_ctx in H1. simplify_map_eq.
    basic_typing_solver.
  - (* TConst *) econstructor.
  - (* TBaseVar *) econstructor. qauto using ctx_erase_lookup.
  - (* TFuncVar *) econstructor. qauto using ctx_erase_lookup.
  - (* TFun *) econstructor.
    instantiate_atom_listctx.
    rewrite ctx_erase_app_r in H1 by my_set_solver.
    rewrite <- rty_erase_open_eq in H1.
    eauto.
  - (* TFix *) econstructor.
    instantiate_atom_listctx.
    rewrite ctx_erase_app_r in H1 by my_set_solver.
    cbn in H1.
    rewrite <- rty_erase_open_eq in H1.
    eauto.
  - hauto using subtyping_preserves_basic_typing.
  - econstructor. eauto. 
  - apply rty_subtyping_preserves_basic_typing in H2. rewrite H2 in *.
    unfold erase_ctx in H1. simplify_map_eq.
    basic_typing_solver.
  - (* TMerge *) unfold join in *. mydestr. hauto.
  - (* TLetE *) econstructor; eauto.
    instantiate_atom_listctx. fold_typing_class.
    rewrite ctx_erase_app_r in H0 by my_set_solver. eauto.
  - destruct τ1; simpl in *.
    all: econstructor; eauto;
      instantiate_atom_listctx;
      rewrite ctx_erase_app_r in H0 by my_set_solver; eauto.
    ln_simpl. repeat rewrite <- rty_erase_open_eq in H0. eauto.
  - destruct τ1; simpl in *.
  all: econstructor; eauto;
    instantiate_atom_listctx;
    rewrite ctx_erase_app_r in H0 by my_set_solver; eauto.
  ln_simpl. repeat rewrite <- rty_erase_open_eq in H0. eauto.  
  - apply effop_typing_preserves_basic_typing in H4.
    cbn in H4. sinvert H4.
    econstructor; eauto.
    instantiate_atom_listctx.
    rewrite ctx_erase_app_r in H0 by my_set_solver.
    rewrite <- rty_erase_open_eq in H0; eauto.
  - (* TMatchbTrue *) econstructor; eauto.
    all: 
    auto_pose_fv x; repeat specialize_with x;
    rewrite ctx_erase_app_r in H4 by my_set_solver; ln_simpl;
    eapply basic_typing_strengthen_tm; eauto; my_set_solver.
  - (* TMatchbFalse *) econstructor; eauto.
    all: 
    auto_pose_fv x; repeat specialize_with x;
    rewrite ctx_erase_app_r in H4 by my_set_solver; ln_simpl;
    eapply basic_typing_strengthen_tm; eauto; my_set_solver.
Qed.

Class RefinementTypingRegularBasicTyping (E: Type) `{Typing tyctx E ty} `{TypingRefinement (listctx rty) E rty} := refinement_typing_regular_basic_typing: forall (Γ: listctx rty) (e: E) (T: rty), Γ ⊢r e ⋮ T -> ⌊ Γ ⌋* ⊢ e ⋮ ⌊ T ⌋.

#[global] Instance RefinementTypingRegularBasicTyping_value: RefinementTypingRegularBasicTyping value.
Proof.
  unfold RefinementTypingRegularBasicTyping.
  eapply value_tm_typing_regular_basic_typing; eauto.
Qed.

#[global] Instance RefinementTypingRegularBasicTyping_tm: RefinementTypingRegularBasicTyping tm.
Proof.
  unfold RefinementTypingRegularBasicTyping.
  eapply value_tm_typing_regular_basic_typing; eauto.
Qed.

Class RefinementTypingRegular (E: Type) 
`{Stale E}
`{Typing tyctx E ty} `{TypingRefinement (listctx rty) E rty} `{RefinementTypingRegularBasicTyping E} := refinement_typing_regular: forall (Γ: listctx rty) (e: E) (T: rty), Γ ⊢r e ⋮ T -> 
⌊ Γ ⌋* ⊢ e ⋮ ⌊ T ⌋ /\ Γ ⊢WF T.

#[global] Instance RefinementTypingRegular_value: RefinementTypingRegular value.
Proof.
  unfold RefinementTypingRegular.
  split.
  - apply refinement_typing_regular_basic_typing; eauto.
  - apply value_typing_regular_wf in H; eauto.
Qed.

#[global] Instance RefinementTypingRegular_tm: RefinementTypingRegular tm.
Proof.
  unfold RefinementTypingRegular.
  split.
  - apply refinement_typing_regular_basic_typing; eauto.
  - apply tm_typing_regular_wf in H; eauto.
Qed.

(** Convert an event operator to a value:
  [op] is [fun x => leteffop y = op x in y] *)
Definition value_of_op op : value :=
  vlam TNat (tleteffop op (vbvar 0) (treturn (vbvar 0))).

(** Well-formed built-in operator typing context (Definition 4.7) *)
(* We simply treat the event operator as a value. This is equivalent to the
definition in the paper (if we expand the denotation of this value). *)
Definition well_formed_builtin_typing :=
  forall op ρ,
    builtin_typing_relation op ρ ->
    ⟦ ρ ⟧ (treturn (value_of_op op)).