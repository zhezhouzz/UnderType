From stdpp Require Import mapset.
From CT.Syntax Require Import Syntax.
From CT Require Import BasicTyping.
From CT Require Import OperationalSemantics.

Import BaseDef MyTactics Primitives Lang Lc.
Import LangLc.
Import BasicTyping.
Import OperationalSemantics.

(* NOTE:
   Using [change ... in *] with shared evars (the [?Γ ?e ?T] placeholders)
   often fails when there are multiple [value_has_type]/[tm_has_type]
   occurrences with different parameters in the context/goal.
   We instead rewrite each occurrence one-by-one by first pattern-matching to
   bind fresh [Γ e T] for that specific occurrence. *)
Ltac fold_typing_class :=
  change (value_has_type ?Γ ?v ?T) with (Γ ⊢ v ⋮ T) in *;
  change (tm_has_type ?Γ ?e ?T) with (Γ ⊢ e ⋮ T) in *;
  repeat (
    first
      [ progress match goal with
        | H : context [value_has_type ?Γ ?v ?T] |- _ =>
            change (value_has_type Γ v T) with (Γ ⊢ v ⋮ T) in H
        | |- context [value_has_type ?Γ ?v ?T] =>
            change (value_has_type Γ v T) with (Γ ⊢ v ⋮ T)
        end
      | progress match goal with
        | H : context [tm_has_type ?Γ ?e ?T] |- _ =>
            change (tm_has_type Γ e T) with (Γ ⊢ e ⋮ T) in H
        | |- context [tm_has_type ?Γ ?e ?T] =>
            change (tm_has_type Γ e T) with (Γ ⊢ e ⋮ T)
        end
      ]).

(** * Naming related properties of the basic type system *)

Lemma basic_typing_contains_fv_tm: forall Γ (e: tm) T, Γ ⊢ e ⋮ T -> stale e ⊆ dom Γ
with basic_typing_contains_fv_value: forall Γ (e: value) T, Γ ⊢ e ⋮ T -> stale e ⊆ dom Γ.
Proof.
  all:
  destruct 1; simpl; eauto;
  try select (forall x, _ ∉ _ -> _) (fun H => auto_pose_fv x; repeat specialize_with x);
  repeat select (tm_has_type _ _ _) (fun H => apply basic_typing_contains_fv_tm in H);
  repeat select (value_has_type _ _ _) (fun H => apply basic_typing_contains_fv_value in H);
  ln_simpl;
  repeat
    match goal with
    | H : stale ({_ ~> _} _) ⊆ _ |- _ ⊆ _ =>
        setoid_rewrite <- open_fv' in H
    | H : _ ⊆ dom (<[_:=_]>_) |- _ ⊆ _ =>
        setoid_rewrite dom_insert in H
    | H : _ !! _ = _ |- _ ⊆ _ =>
        apply elem_of_dom_2 in H; simp_hyps
    end;
  my_set_solver.
Qed.

Class FvSubsetGamma (G E T: Type) `{staleG: Stale G} `{staleE: Stale E} `{Typing G E T} := fv_subset_gamma: forall (Γ: G) (e: E) (T: T), Γ ⊢ e ⋮ T -> staleE e ⊆ staleG Γ.

#[global] Instance FvSubsetGamma_tm: FvSubsetGamma (amap ty) tm ty.
Proof.
  unfold FvSubsetGamma.
  eapply basic_typing_contains_fv_tm; eauto.
Qed.
Arguments FvSubsetGamma_tm /.

#[global] Instance FvSubsetGamma_value: FvSubsetGamma (amap ty) value ty.
Proof.
  unfold FvSubsetGamma.
  eapply basic_typing_contains_fv_value; eauto.
Qed.
Arguments FvSubsetGamma_value /.

Lemma basic_typing_closed_tm: forall e T, ∅ ⊢ e ⋮ T -> stale e = ∅.
Proof.
  intros.
  apply fv_subset_gamma in H. my_set_solver.
Qed.

Lemma basic_typing_closed_value: forall v T, ∅ ⊢ v ⋮ T -> stale v = ∅.
Proof.
  intros.
  apply fv_subset_gamma in H. my_set_solver.
Qed.

Lemma basic_typing_regular_value: forall Γ (v: value) t, Γ ⊢ v ⋮ t -> lc v
with basic_typing_regular_tm: forall Γ (e: tm) t, Γ ⊢ e ⋮ t -> lc e.
Proof.
  all: destruct 1; ln_simpl; lc_solver;
  try solve [try (auto_exists_L; intros y Hy; specialize_with y);
  repeat match goal with
  | [H: tm_has_type _ _ _ |- lc _] => apply basic_typing_regular_tm in H
  | [H: value_has_type _ _ _ |- lc _] => apply basic_typing_regular_value in H
  | [H: _ ⊢ ?e ⋮ _ |- lc _] =>
    lazymatch type of e with
    | tm => apply basic_typing_regular_tm in H
    | value => apply basic_typing_regular_value in H
    end
  end; lc_solver].
Qed.

Class TypingLc (G E T: Type) `{Lc E} `{Typing G E T}  := typing_lc: forall (Γ: G) (e: E) (T: T), Γ ⊢ e ⋮ T -> lc e.

#[global] Instance TypingLc_tm: TypingLc (amap ty) tm ty.
Proof.
  unfold TypingLc.
  eapply basic_typing_regular_tm; eauto.
Qed.
Arguments TypingLc_tm /.

#[global] Instance TypingLc_value: TypingLc (amap ty) value ty.
Proof.
  unfold TypingLc.
  eapply basic_typing_regular_value; eauto.
Qed.
Arguments TypingLc_value /.

Ltac lc_basic_typing_simp_aux :=
  match goal with
  | [H: _ ⊢ _ ⋮ _ |- lc _] => apply typing_lc in H
  | [H: _ ⊢ _ ⋮ _ |- body _] => apply typing_lc in H
  | [H: _ ⊢ _ ⋮ _ |- context [stale _]] => apply fv_subset_gamma in H
  end.

Ltac basic_typing_regular_simp :=
  repeat lc_basic_typing_simp_aux; eauto.

(** This file proves properties of the basic type system. *)

(** * Canonical forms *)

Lemma basic_typing_bool_canonical_form: forall (v: value), ∅ ⊢ v ⋮ (TBase TBool) -> v = (vconst true) \/ v = (vconst false).
Proof.
  inversion 1; subst; simpl in *.
  destruct c; simplify_eq. destruct b; eauto.
  simplify_map_eq.
Qed.

Lemma basic_typing_nat_canonical_form: forall (v: value), ∅ ⊢ v ⋮ (TBase TNat) -> (exists (i: nat), v = vconst (cnat i)).
Proof.
  inversion 1; subst; simpl in *.
  destruct c; simplify_eq. eauto.
  simplify_map_eq.
Qed.

Lemma basic_typing_base_canonical_form: forall (v: value) (B: base_ty), ∅ ⊢ v ⋮ (TBase B) -> (exists (c: constant), v = vconst c).
Proof.
  inversion 1; subst. eauto. simplify_map_eq.
Qed.

Lemma basic_typing_arrow_canonical_form:
  forall (v: value) T1 T2, ∅ ⊢ v ⋮ T1 ⤍ T2 ->
                      (exists e, v = vlam T1 e) \/ (exists e, v = vfix (T1 ⤍ T2) (treturn (vlam (T1 ⤍ T2) e))).
Proof.
  inversion 1; subst. simplify_map_eq.
  - left. eauto.
  - right. eexists. f_equal.
Qed.

(** * Weakening lemmas *)

Lemma basic_typing_weaken_tm: forall Γ Γ' (v: tm) T,
    Γ ⊆ Γ' -> Γ ⊢ v ⋮ T -> Γ' ⊢ v ⋮ T
with basic_typing_weaken_value: forall Γ Γ' (v: value) T,
    Γ ⊆ Γ' -> Γ ⊢ v ⋮ T -> Γ' ⊢ v ⋮ T.
Proof.
  all : intros * Hs; destruct 1;
  try solve [econstructor; eauto using lookup_weaken].
  all:
    auto_exists_L; eauto;
    fold_typing_class;
  eauto;
    intros x Hx; specialize_with x;
    auto_eapply;
    try lazymatch goal with
      | |- _ ⊆ _ => apply insert_mono; eauto
      | _ => eauto
      end.
Qed.

Class BasicTypingWeaken (E: Type) `{Typing (amap ty) E ty} := basic_typing_weaken: forall (Γ Γ': (amap ty)) (e: E) (T: ty), Γ ⊆ Γ' -> Γ ⊢ e ⋮ T -> Γ' ⊢ e ⋮ T.

#[global] Instance BasicTypingWeaken_tm: BasicTypingWeaken tm.
Proof.
  unfold BasicTypingWeaken.
  eapply basic_typing_weaken_tm; eauto.
Qed.
Arguments BasicTypingWeaken_tm /.

#[global] Instance BasicTypingWeaken_value: BasicTypingWeaken value.
Proof.
  unfold BasicTypingWeaken.
  eapply basic_typing_weaken_value; eauto.
Qed.
Arguments BasicTypingWeaken_value /.

Class BasicTypingWeakenInsert (E: Type) `{Typing (amap ty) E ty} := basic_typing_weaken_insert: forall (Γ: (amap ty)) (e: E) (T: ty) (x: atom) (U: ty), x # Γ -> Γ ⊢ e ⋮ T -> <[x := U]> Γ ⊢ e ⋮ T.

#[global] Instance BasicTypingWeakenInsert_tm: BasicTypingWeakenInsert tm.
Proof.
  unfold BasicTypingWeakenInsert.
  intros. eapply basic_typing_weaken_tm. 2: eauto.
  apply insert_subseteq. apply not_elem_of_dom. my_set_solver.
Qed.
Arguments BasicTypingWeakenInsert_tm /.

#[global] Instance BasicTypingWeakenInsert_value: BasicTypingWeakenInsert value.
Proof.
  unfold BasicTypingWeakenInsert.
  intros. eapply basic_typing_weaken_value. 2: eauto.
  apply insert_subseteq. apply not_elem_of_dom. my_set_solver.
Qed.
Arguments BasicTypingWeakenInsert_value /.

(** * Substitution lemmas *)

Class BasicTypingSubst (E: Type) `{Typing (amap ty) E ty} `{Subst value E} := basic_typing_subst: forall (Γ: (amap ty)) (z: atom) (u: value) (U: ty) (e: E) (T: ty), Γ ⊢ u ⋮ U -> <[z := U]> Γ ⊢ e ⋮ T -> Γ ⊢ {z := u} e ⋮ T.

#[global] Instance BasicTypingSubst_tm: BasicTypingSubst tm.
Proof.
  unfold BasicTypingSubst.
  intros * Hu Ht; remember (<[z:=U]> Γ) as Γ'; generalize dependent Γ.
  revert Γ' e T Ht.
  apply (tm_has_type_mutual_rec
           (fun c e T _ => ∀ Γ, Γ ⊢ u ⋮ U → c = <[z:=U]> Γ → Γ ⊢ {z := u } e ⋮ T)
           (fun c e T _ => ∀ Γ, Γ ⊢ u ⋮ U → c = <[z:=U]> Γ → Γ ⊢ {z := u } e ⋮ T));
  (* [context] should be defined as a notation which helps resolving typeclass
  instances for, e.g., rewriting. *)
    intros; subst; ln_simpl; simplify_map_eq; eauto; try auto_exists_L; intros x Hx; specialize_with x; eauto;
    ln_simpl;
    fold_syntax_class; 
    fold_typing_class;
    eauto.
  all: rewrite <- subst_open_var;
  try match goal with
  | [ |- _ ≠ _ ] => my_set_solver
  | [H: _ ⊢ ?e ⋮ _ |- lc ?e ] => apply typing_lc in H; eauto
  end; auto_eapply; fold_typing_class;
  try match goal with
  | [|- _ ∉ _ ] => my_set_solver
  | [|- _ ⊢ _ ⋮ _ ] => eapply basic_typing_weaken_insert; eauto; my_set_solver
  | _ => apply insert_commute; my_set_solver 
  end.
Qed.
Arguments BasicTypingSubst_tm /.

#[global] Instance BasicTypingSubst_value: BasicTypingSubst value.
Proof.
  unfold BasicTypingSubst.
  intros * Hu Ht; remember (<[z:=U]> Γ) as Γ'; generalize dependent Γ.
  revert Γ' e T Ht.
  apply (value_has_type_mutual_rec
           (fun c e T _ => ∀ Γ, Γ ⊢ u ⋮ U → c = <[z:=U]> Γ → Γ ⊢ {z := u } e ⋮ T)
           (fun c e T _ => ∀ Γ, Γ ⊢ u ⋮ U → c = <[z:=U]> Γ → Γ ⊢ {z := u } e ⋮ T));
  intros; subst; ln_simpl; simplify_map_eq; eauto; try auto_exists_L; intros x Hx; specialize_with x; eauto;
  ln_simpl;
  fold_syntax_class; 
  fold_typing_class;
    eauto.
  all: rewrite <- subst_open_var;
  try match goal with
  | [ |- _ ≠ _ ] => my_set_solver
  | [H: _ ⊢ ?e ⋮ _ |- lc ?e ] => apply typing_lc in H; eauto
  end; auto_eapply; fold_typing_class;
  try match goal with
  | [|- _ ∉ _ ] => my_set_solver
  | [|- _ ⊢ _ ⋮ _ ] => eapply basic_typing_weaken_insert; eauto; my_set_solver
  | _ => apply insert_commute; my_set_solver 
  end.
Qed.
Arguments BasicTypingSubst_value /.

Ltac smart_ln_simpl :=
repeat match goal with
| [H: lc ?e |- context [{_ ~> _} ?e]] => rewrite open_rec_lc by eauto
| [H: lc ?e, H': context [{_ ~> _} ?e] |- _ ] => rewrite open_rec_lc in H' by eauto
end.

Class BasicTypingOpen (E: Type) `{Stale E} `{Typing (amap ty) E ty} `{Open value E} := basic_typing_open: forall (Γ: (amap ty)) (z: atom) (u: value) (U: ty) (e: E) (T: ty), z # e -> Γ ⊢ u ⋮ U -> <[z := U]> Γ ⊢ e ^^ (vfvar z) ⋮ T -> Γ ⊢ e ^^ u ⋮ T.

#[global] Instance BasicTypingOpen_tm: BasicTypingOpen tm.
Proof.
  unfold BasicTypingOpen.
  intros. rewrite <- subst_intro with (x:=z); eauto.
  eapply basic_typing_subst in H1; eauto.
  basic_typing_regular_simp.
Qed.
Arguments BasicTypingOpen_tm /.

#[global] Instance BasicTypingOpen_value: BasicTypingOpen value.
Proof.
  unfold BasicTypingOpen.
  intros. rewrite <- subst_intro with (x:=z); eauto.
  eapply basic_typing_subst in H1; eauto.
  basic_typing_regular_simp.
Qed.
Arguments BasicTypingOpen_value /.

(** * Type uniqueness lemmas *)

Class BasicTypingUnique (E: Type) `{Typing (amap ty) E ty} := basic_typing_unique: forall (Γ: (amap ty)) (e: E) (T1 T2: ty), Γ ⊢ e ⋮ T1 -> Γ ⊢ e ⋮ T2 -> T1 = T2.

#[global] Instance BasicTypingUnique_tm: BasicTypingUnique tm.
Proof.
  unfold BasicTypingUnique.
  intros * H. revert T2. revert_all.
  apply (tm_has_type_mutual_rec
           (fun Γ v T1 _ => ∀ T2, Γ ⊢ v ⋮ T2 → T1 = T2)
           (fun Γ e T1 _ => ∀ T2, Γ ⊢ e ⋮ T2 → T1 = T2));
    intros;
    try match goal with
      | H : _ ⊢ _ ⋮ _ |- _ => sinvert H
      end; simplify_map_eq; eauto; fold_typing_class;
    try solve [ auto_pose_fv x; repeat specialize_with x; hauto ].
Qed.
Arguments BasicTypingUnique_tm /.

#[global] Instance BasicTypingUnique_value: BasicTypingUnique value.
Proof.
  unfold BasicTypingUnique.
  intros * H. revert T2. revert_all.
  apply (value_has_type_mutual_rec
           (fun Γ v T1 _ => ∀ T2, Γ ⊢ v ⋮ T2 → T1 = T2)
           (fun Γ e T1 _ => ∀ T2, Γ ⊢ e ⋮ T2 → T1 = T2));
    intros;
    try match goal with
      | H : _ ⊢ _ ⋮ _ |- _ => sinvert H
      | H : _ ⊢ _ ⋮ _ |- _ => sinvert H
      end; simplify_map_eq; eauto; fold_typing_class;
    try solve [ auto_pose_fv x; repeat specialize_with x; hauto ].
Qed.
Arguments BasicTypingUnique_value /.
(** * Strengthening lemmas *)

Ltac aset_solver :=
try match goal with
  | [H: <[?x:=_]> ?Γ !! ?y = _ |- ?Γ !! ?y = _ ] =>
        solve [rewrite lookup_insert_ne in * by fast_set_solver!!; eauto]
end;
repeat match goal with
| [H:  <[?x:=_]> _ !! ?x = _ |- _ ] =>
  setoid_rewrite lookup_insert in H; eauto; simplify_eq
| [H: <[?y:=_]> _ !! ?x = _ |- _ ] =>
  assert (x ≠ y) by fast_set_solver!!;
  setoid_rewrite lookup_insert_ne in H; eauto; simplify_eq
| [|- <[?x:=_]> _ !! ?x = _ ] =>
  setoid_rewrite lookup_insert; eauto
| [|- <[?y:=_]> _ !! ?x = _ ] =>
  assert (x ≠ y) by fast_set_solver!!;
  setoid_rewrite lookup_insert_ne; eauto
| [ |- ∅ ⊆ ?M ] =>
  match type of M with
  | amap _ => apply map_empty_subseteq
  end
end.

Ltac lc_set_solver :=
  lc_solver;
  match goal with
  | [ |- ?x # {_ ~> _} _] =>
        solve [eapply not_elem_of_weaken; [ | apply open_fv ]; ln_simpl; fast_set_solver!!]
  | [ |- _ !! _ = _ ] => aset_solver
  | [ |- _ ⊆ ?M ] =>
    match type of M with
    | amap _ => aset_solver
    | _ => fast_set_solver!!
    end
  | _ => fast_set_solver!!
  end. 

(* This statement can be generalized to taking a union of the context and a
disjoint new context. *)
Lemma basic_typing_strengthen_tm: forall Γ x Tx (v: tm) T,
    (<[x:=Tx]>Γ) ⊢ v ⋮ T -> x # v -> Γ ⊢ v ⋮ T
with basic_typing_strengthen_value: forall Γ x Tx (v: value) T,
    (<[x:=Tx]>Γ) ⊢ v ⋮ T -> x # v -> Γ ⊢ v ⋮ T.
Proof.
  all : intros * H Hfresh; remember (<[x:=Tx]>Γ);
    generalize dependent Γ;
    destruct H; intros; subst.
    econstructor_L; ln_simpl; fold_typing_class.
    all:
      econstructor_L; auto_specialization; ln_simpl; fold_typing_class;
      try rewrite insert_commute in * by my_set_solver;
      match goal with
      | [ |-  _ !! _ = _ ] => lc_set_solver
      | H: <[ ?x := ?Tx]> ?Γ ⊢ ?e ⋮ _ |- ?Γ ⊢ ?e ⋮ _ => 
        auto_eapply; eauto; lc_set_solver
      end.
Qed.

Class BasicTypingStrengthen (E: Type) `{Typing (amap ty) E ty} `{Stale E} := basic_typing_strengthen: forall (Γ: (amap ty)) (x: atom) (Tx: ty) (e: E) (T: ty), (<[x:=Tx]>Γ) ⊢ e ⋮ T -> x # e -> Γ ⊢ e ⋮ T.

#[global] Instance BasicTypingStrengthen_tm: BasicTypingStrengthen tm.
Proof.
  unfold BasicTypingStrengthen.
  eapply basic_typing_strengthen_tm; eauto.
Qed.
Arguments BasicTypingStrengthen_tm /.

#[global] Instance BasicTypingStrengthen_value: BasicTypingStrengthen value.
Proof.
  unfold BasicTypingStrengthen.
  eapply basic_typing_strengthen_value; eauto.
Qed.
Arguments BasicTypingStrengthen_value /.

(** * Type properties of syntax sugar *)

Ltac auto_specialization :=
  try lazymatch goal with
  | |- forall y, y ∉ _ -> _ =>
    let y := fresh "y" in
    let Hy := fresh "Hy" in
    intros y Hy;
    repeat specialize_with y
  end;
  eauto.

Ltac L_econstructor_specialized :=
  econstructor_L; auto_specialization; ln_simpl.

Lemma value_of_op_regular_basic_typing op:
  ∅ ⊢ value_of_op op ⋮ ty_of_op op.
Proof.
  econstructor.
  simpl. instantiate (1:=∅). intros.
  econstructor. econstructor. simplify_map_eq. reflexivity. reflexivity.
  instantiate_atom_listctx.
  simpl. econstructor. econstructor. simplify_map_eq. reflexivity.
Qed.

Ltac basic_typing_solver :=
fold_typing_class;
repeat
 (match goal with
| [H: ?g ⊢ (treturn ?v) ⋮ ?t |- _ ⊢ ?v ⋮ _ ] => sinvert H; eauto
| [ H: ?g ⊢ ?e ⋮ ?T, H': ?g ⊢ ?e ⋮ ?T |- _ ] => clear H'
| [ H: ?g ⊢ ?e ⋮ ?T, H': ?g ⊢ ?e ⋮ ?T |- _ ] => clear H'
| [ H: ?g ⊢ ?e ⋮ ?T, H': ?g ⊢ ?e ⋮ ?T' |- _ ] =>
     assert (T = T') by eauto using basic_typing_unique; subst
| [H: ∅ ⊢ ?e ⋮ _ |- _ ⊢ ?e ⋮ _ ] =>
  eapply basic_typing_weaken in H; eauto; try lc_set_solver
| [|- _ ⊢ value_of_op ?op ⋮ _ ] =>
  let Hop := fresh "Hop" in
  pose proof (value_of_op_regular_basic_typing op) as Hop;
  eapply basic_typing_weaken in Hop; eauto; try lc_set_solver
| [H: ?Γ ⊢ ?e ⋮ _ |- <[ _ := _ ]> ?Γ ⊢ ?e ⋮ _ ] =>
  apply basic_typing_weaken_insert; eauto; lc_set_solver
| [H: <[ _ := _ ]> ?Γ ⊢ ?e ⋮ _ |-  ?Γ ⊢ ?e ⋮ _ ] =>
  apply basic_typing_strengthen in H; eauto; lc_set_solver
| [H: _ ⊢ ?e ^^ (vfvar ?z) ⋮ _ |- _ ⊢ ?e ^^ _ ⋮ _ ] =>
  eapply basic_typing_open in H; eauto; try lc_set_solver
| |- _ ⊢ (vfvar ?x) ⋮ _ =>
  econstructor; aset_solver
| |- _ ⊢ _ ⋮ _ =>
  L_econstructor_specialized; smart_ln_simpl
end; fold_typing_class; eauto).

Lemma mk_app_has_type Γ e v T1 T2 :
  Γ ⊢ e ⋮ T1 ⤍ T2 ->
  Γ ⊢ v ⋮ T1 ->
  Γ ⊢ mk_app e v ⋮ T2.
Proof.
  intros.
  assert (lc e) by basic_typing_regular_simp.
  assert (lc v) by basic_typing_regular_simp.
  basic_typing_solver.
Qed.

Ltac basic_typing_destruct :=
fold_typing_class;
repeat (match goal with
| [H: _ ⊢ tlete _ _ ⋮ ?T2 |- _ ] =>
  sinvert H; ln_simpl;
  let x := fresh "x" in
  auto_pose_fv x; repeat specialize_with x; smart_ln_simpl
| [H: _ ⊢ tletapp _ _ _ ⋮ ?T2 |- _ ] =>
  sinvert H; ln_simpl;
  let x := fresh "x" in
  auto_pose_fv x; repeat specialize_with x; smart_ln_simpl
| [H: _ ⊢ (vfvar ?x) ⋮ _ |- _ ] =>
  sinvert H; ln_simpl; aset_solver
| [H: _ ⊢ (treturn _) ⋮ _ |- _ ] =>
  sinvert H; ln_simpl
end; fold_typing_class; eauto).

Lemma mk_app_has_type_inv Γ e v T2 :
  Γ ⊢ mk_app e v ⋮ T2 ->
  lc v ->
  exists T1, Γ ⊢ e ⋮ T1 ⤍ T2 /\ Γ ⊢ v ⋮ T1.
Proof.
  unfold mk_app. intros.
  basic_typing_destruct.
  eexists; split; eauto. basic_typing_solver.
Qed.

(** * Type preservation *)

Lemma tr_reduction_sound op c1 c :
  ⇓{op~c1}{c} ->
  ty_of_const c = ret_ty_of_op op.
Proof.
  induction 1; eauto.
Qed.

Lemma eval_op_typing (op: effop) (c1 c: constant) :
  ⇓{op~c1}{c} ->
  exists T1 T2, ty_of_op op = T1 ⤍ T2 /\
  ∅ ⊢ (vconst c1) ⋮ T1 /\ ∅ ⊢ (vconst c) ⋮ T2.
Proof.
  intros * H. invclear H.
  - eexists TNat, TNat. repeat split; eauto; econstructor.
  - eexists TNat, TBool. repeat split; eauto; econstructor.
  - eexists TNat, TNat. repeat split; eauto; econstructor.
Qed.

(** perservation *)
Lemma preservation: forall Γ T (e e': tm), e ↪ e' -> Γ ⊢ e ⋮ T -> Γ ⊢ e' ⋮ T.
Proof.
  intros * Hstep HT. move HT at top. revert_all.
  induction 1; intros; sinvert Hstep;
  (* auto_pose_fv x; repeat specialize_with x; *)
  eauto; basic_typing_solver.
  - basic_typing_destruct; 
    auto_pose_fv x; repeat specialize_with x;
    basic_typing_solver.
  - auto_pose_fv x; repeat specialize_with x.
    basic_typing_solver.
    apply eval_op_typing in H10; simp_hyps. 
    rewrite H4 in H0. simp_hyps.
    basic_typing_solver.
  - sinvert H; ln_simpl.
    auto_pose_fv x; repeat specialize_with x.
    basic_typing_solver.
  - sinvert H; ln_simpl.
    auto_pose_fv x; repeat specialize_with x.
    (* ln_simpl has evaluated the terms too much **)
    rewrite open_vlam_rev in *;
    basic_typing_solver.
Qed.

(** multi preservation *)
Lemma multi_preservation: forall Γ T (e e': tm),e ↪* e' -> Γ ⊢ e ⋮ T -> Γ ⊢ e' ⋮ T.
Proof.
  induction 1; eauto using preservation.
Qed.

Ltac pure_multistep_tac :=
  match goal with
  | [H: _ |- (treturn ?v) ↪* (treturn _) ] =>
      apply (value_reduction_any_ctx v); eauto
  end; basic_typing_regular_simp.
