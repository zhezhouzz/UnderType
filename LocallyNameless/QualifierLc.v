From stdpp Require Import mapset.
From stdpp Require Import natmap.
From stdpp Require Import fin vector.
From Stdlib Require Classical_Prop.
From CT.Syntax Require Import Syntax.
From CT.LocallyNameless Require Import LangLc.

Import BaseDef.
Import Lang.
Import Primitives.
Import Qualifier.
Import MyTactics.

#[global] Instance SubstCommute_qualifier: SubstCommute qualifier.
Proof.
  unfold SubstCommute.
  intros x u_x y u_y ϕ Hxy Hxuy Hyux.
  destruct ϕ.
  ln_simpl.
  f_equal.
  rewrite !Vector.map_map.
  apply Vector.map_ext. ln_simpl.
  intros; rewrite subst_commute; eauto.
Qed.
Arguments subst_commute /.

#[global] Instance SubstFresh_qualifier: SubstFresh qualifier.
Proof.
  unfold SubstFresh.
  intros ϕ x u Hx.
  destruct ϕ.
  ln_simpl.
  f_equal.
  clear prop.
  induction vals; simpl in *; eauto.
  f_equal.
  apply subst_fresh. my_set_solver.
  auto_apply. my_set_solver.
Qed.
Arguments SubstFresh_qualifier /.

#[global] Instance OpenFv_qualifier: OpenFv qualifier.
Proof.
  unfold OpenFv.
  intros ϕ v k.
  destruct ϕ.
  ln_simpl. clear. induction vals; ln_simpl. easy.
  etrans. apply union_mono. apply open_fv.
  reflexivity. my_set_solver.
Qed.
Arguments OpenFv_qualifier /.

#[global] Instance OpenFvPrime_qualifier: OpenFvPrime qualifier.
Proof.
  unfold OpenFvPrime.
  intros ϕ v k.
  destruct ϕ.
  ln_simpl. clear. induction vals; ln_simpl. easy.
  apply union_mono; eauto. apply open_fv'.
Qed.
Arguments OpenFvPrime_qualifier /.

Lemma lc_qualifier_and q1 q2 :
  lc_qualifier q1 -> lc_qualifier q2 ->
  lc_qualifier (q1 & q2).
Proof.
  inversion 1. inversion 1. subst.
  simpl. constructor.
  rewrite Vector.to_list_Forall in *.
  rewrite Vector.to_list_append.
  apply Forall_app. eauto.
Qed.

Lemma vector_map_app {A B: Type} (f: A -> B) {n1 n2: nat} (vec1: vec A n1) (vec2: vec A n2):
  vmap f (vec1 +++ vec2) = vmap f vec1 +++ vmap f vec2.
Proof.
  induction vec1; simpl; eauto.
  f_equal. eauto.
Qed.

Lemma qualifier_and_open k v q1 q2 :
  {k ~> v} (q1 & q2) = ({k ~> v} q1) & ({k ~> v} q2).
Proof.
  destruct q1, q2. ln_simpl. f_equal. apply vector_map_app.
Qed.

Lemma qualifier_and_subst x v q1 q2 :
  {x := v} (q1 & q2) = ({x := v} q1) & ({x := v} q2).
Proof.
  destruct q1, q2. ln_simpl. f_equal. apply vector_map_app.
Qed.

Lemma qualifier_and_fv q1 q2 :
  stale (q1 & q2) = stale q1 ∪ stale q2.
Proof.
  destruct q1, q2. ln_simpl.
  clear.
  induction vals; ln_simpl. my_set_solver.
  rewrite IHvals. my_set_solver.
Qed.

Lemma denote_vals_app {n1 n2} (vals1 : vec value n1) (vals2 : vec value n2) :
  denote_vals (vals1 +++ vals2) =
    match denote_vals vals1, denote_vals vals2 with
    | Some v1, Some v2 => Some (v1 +++ v2)
    | _, _ => None
    end.
Proof.
  induction vals1; simpl; qauto.
Qed.

Lemma denote_qualifier_and q1 q2 :
  denote (q1 & q2) <-> denote q1 /\ denote q2.
Proof.
  destruct q1, q2. ln_simpl.
  rewrite denote_vals_app.
  case_split; try qauto.
  case_split; try qauto.
  rewrite Vector.splitat_append. eauto.
Qed.

#[global] Instance OpenSubstSame_qualifier: OpenSubstSame qualifier.
Proof.
  unfold OpenSubstSame.
  intros x y ϕ k H.
  destruct ϕ. ln_simpl.
  f_equal. clear - H.
  induction vals; cbn; eauto.
  cbn in H.
  f_equal. fold_syntax_class. apply open_subst_same. my_set_solver.
  apply IHvals. my_set_solver.
Qed.
Arguments OpenSubstSame_qualifier /.

#[global] Instance SubstOpen_qualifier: SubstOpen qualifier.
Proof.
  unfold SubstOpen.
  intros ϕ x u w k H.
  destruct ϕ. cbn. intros.
  f_equal.
  rewrite !Vector.map_map.
  apply Vector.map_ext. fold_syntax_class.
  intros.  
  rewrite subst_open; eauto.
Qed.
Arguments SubstOpen_qualifier /.

#[global] Instance SubstLc_qualifier: SubstLc qualifier.
Proof.
  unfold SubstLc.
  (* intros ϕ Hlc x u Hu. *)
  destruct 1. intros Hu.
  econstructor.
  srewrite Vector.to_list_Forall.
  rewrite Vector.to_list_map.
  rewrite Forall_map.
  eapply Forall_impl; eauto.
  simpl. intros. fold_syntax_class. lc_solver1. fold_syntax_class. apply subst_lc; eauto.
Qed.
Arguments SubstLc_qualifier /.

#[global] Instance FvOfSubstClosed_qualifier: FvOfSubstClosed qualifier.
Proof.
  unfold FvOfSubstClosed.
  intros x u ϕ Hx.
  destruct ϕ; ln_simpl. clear prop. induction vals; simpl; intros.
  my_set_solver. fold_syntax_class.
  rewrite fv_of_subst_closed; eauto.
  setoid_rewrite IHvals; eauto. my_set_solver.
Qed.
Arguments FvOfSubstClosed_qualifier /.

#[global] Instance OpenNotInEq_qualifier: OpenNotInEq qualifier.
Proof.
  unfold OpenNotInEq.
  intros x ϕ k H.
  destruct ϕ; ln_simpl.
  f_equal.
  clear - H.
  induction vals; simpl; eauto.
  f_equal. apply open_not_in_eq. my_set_solver.
  auto_apply. my_set_solver.
Qed.
Arguments OpenNotInEq_qualifier /.

#[global] Instance LcSubst_qualifier: LcSubst qualifier.
Proof.
  unfold LcSubst.
  intros x u ϕ Hlc Hu.
  sinvert Hlc.
  destruct ϕ. ln_simpl.
  simplify_eq.
  econstructor.
  srewrite Vector.to_list_Forall.
  srewrite Vector.to_list_map.
  srewrite Forall_map.
  eapply Forall_impl; eauto.
  simpl. intros. fold_syntax_class. lc_solver1. fold_syntax_class. eapply lc_subst; eauto.
Qed.

#[global] Instance OpenRecLc_qualifier: OpenRecLc qualifier.
Proof.
  unfold OpenRecLc.
  destruct 1. intros. ln_simpl.
  f_equal.
  rewrite <- Vector.map_id.
  apply Vector.map_ext_in.
  rewrite Vector.Forall_forall in H.
  intros. fold_syntax_class. rewrite open_rec_lc; eauto.
Qed.
Arguments OpenRecLc_qualifier /.

#[global] Instance OpenIdemp_qualifier: OpenIdemp qualifier.
Proof.
  unfold OpenIdemp.
  destruct t; intros. ln_simpl.
  f_equal.
  rewrite Vector.map_map.
  apply Vector.map_ext_in.
  intros. do 2 fold_syntax_class. rewrite open_idemp; eauto.
Qed.
Arguments OpenIdemp_qualifier /.

#[global] Instance OpenSwap_qualifier: OpenSwap qualifier.
Proof.
  unfold OpenSwap.
  destruct t; intros. ln_simpl.
  f_equal. rewrite !Vector.map_map.
  apply Vector.map_ext.
  intros. do 2 fold_syntax_class. rewrite open_swap; eauto.
Qed.
Arguments OpenSwap_qualifier /.

#[global] Instance OpenLcRespect_qualifier: OpenLcRespect qualifier.
Proof.
  unfold OpenLcRespect.
  intros ϕ u v k H. sinvert H.
  destruct ϕ. ln_simpl. simplify_eq.
  econstructor.
  srewrite Vector.to_list_Forall.
  srewrite Vector.to_list_map.
  srewrite Forall_map.
  eapply Forall_impl; eauto.
  simpl. intros. fold_syntax_class. lc_solver1. fold_syntax_class. eapply open_lc_respect; eauto.
Qed.
Arguments OpenLcRespect_qualifier /.

Arguments qualifier_and : simpl never.

#[global] Instance SubstOpenVar_qualifier: SubstOpenVar qualifier.
Proof.
  apply SubstOpenVar_all. all: typeclasses eauto.
Qed.
Arguments SubstOpenVar_qualifier /.

Class SubstBody2 A `{Stale A} `{open: Open value A} `{Subst value A} `{lc : Lc A}:= subst_body2 :
forall x (u: value) (e: A), body2 e -> lc_value u -> body2 ({x := u} e).

#[global] Instance SubstBody2_qualifier: SubstBody2 qualifier.
Proof.
  unfold SubstBody2.
  unfold body2.
  destruct 1. intros Hu.
  auto_exists_L. intros y1 Hy1 y2 Hy2.
  specialize_with y1.
  specialize_with y2.
  repeat rewrite <- (subst_open_var); eauto.
  apply subst_lc; eauto.
  all: my_set_solver.
Qed.
Arguments SubstBody2_qualifier /.

Class BodySubst A `{Stale A} `{Open value A} `{Subst value A} `{Lc A} := body_subst :
forall (x: atom) (u: value) (e: A), body ({x := u} e) -> lc_value u -> body e.

#[global] Instance BodySubst_qualifier: BodySubst qualifier.
Proof.
  unfold BodySubst.
  unfold body.
  destruct 1. intros Hu.
  auto_exists_L. intros y Hy.
  specialize_with y.
  eapply lc_subst; eauto.
  rewrite -> !subst_open_var; eauto. my_set_solver.
Qed.
Arguments BodySubst_qualifier /.

Class Body2Subst A `{Stale A} `{Open value A} `{Subst value A} `{Lc A} := body2_subst:
forall (x: atom) (u: value) (e: A), body2 ({x := u} e) -> lc_value u -> body2 e.

#[global] Instance Body2Subst_qualifier: Body2Subst qualifier.
Proof.
  unfold Body2Subst.
  unfold body2.
  destruct 1. intros Hu.
  auto_exists_L. intros y1 Hy1 y2 Hy2.
  specialize_with y1. specialize_with y2.
  eapply lc_subst; eauto.
  rewrite -> !subst_open_var; eauto; my_set_solver.
Qed.
Arguments Body2Subst_qualifier /.

Lemma lc_phi1_and ϕ1 ϕ2:
  body ϕ1 -> body ϕ2 -> body (ϕ1 & ϕ2).
Proof.
  intros. unfold body in *. simp_hyps.
  auto_exists_L. intros y1 Hy1.
  specialize_with y1. specialize_with y1.
  setoid_rewrite qualifier_and_open.
  apply lc_qualifier_and; eauto.
Qed.

Lemma lc_phi2_and ϕ1 ϕ2:
  body2 ϕ1 -> body2 ϕ2 -> body2 (ϕ1 & ϕ2).
Proof.
  intros. unfold body2 in *. simp_hyps.
  auto_exists_L. intros y1 Hy1 y2 Hy2.
  specialize_with y1. specialize_with y2.
  specialize_with y1. specialize_with y2.
  setoid_rewrite qualifier_and_open. setoid_rewrite qualifier_and_open.
  apply lc_qualifier_and; eauto.
Qed.

Lemma lc_phi1_body: ∀ n vals prop,
    body (@qual n vals prop) -> Vector.Forall (fun v => body v) vals.
Proof.
  intros. subst. sinvert H.
  rewrite Vector.Forall_forall. intros.
  auto_exists_L. intros.
  ospecialize * (H0 x0). my_set_solver.
  sinvert H0.
  apply Classical_Prop.EqdepTheory.inj_pair2 in H4.
  apply Classical_Prop.EqdepTheory.inj_pair2 in H5.
  subst.
  rewrite VectorSpec.Forall_map in H3.
  rewrite Vector.Forall_forall in H3. eauto.
Qed.

Lemma lc_phi2_body: ∀ n vals prop,
    body2 (@qual n vals prop) ->
    Vector.Forall (fun v => body2 v) vals.
Proof.
  unfold body2. intros. subst. sinvert H.
  rewrite Vector.Forall_forall. intros.
  auto_exists_L. intros.
  ospecialize * (H0 x0 _ y). my_set_solver. my_set_solver.
  sinvert H0.
  apply Classical_Prop.EqdepTheory.inj_pair2 in H5.
  apply Classical_Prop.EqdepTheory.inj_pair2 in H6.
  subst.
  repeat rewrite VectorSpec.Forall_map in H4.
  rewrite Vector.Forall_forall in H4. eauto.
Qed.

(* NOTE: Very very annoying, a reverse version of map_ext, using classical logic *)
Lemma vector_map_ext_in' {A B: Type} (f g: A -> B) {n: nat} (vec: vec A n):
  vmap f vec = vmap g vec -> (forall x, @Vector.In A x n vec -> f x = g x).
Proof.
  induction vec; simpl; intros.
  - inversion H0.
  - sinvert H.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H3.
    sinvert H0; eauto.
    apply Classical_Prop.EqdepTheory.inj_pair2 in H5. subst.
    eapply IHvec in H3; eauto.
Qed.

#[global] Instance Fact1_qualifier: Fact1 qualifier.
Proof.
    unfold Fact1.
    intros u v ϕ i j Hij Hijuv.
  destruct ϕ. ln_simpl. f_equal.
  rewrite <- Vector.map_id.
  apply Vector.map_ext_in.
  simplify_eq.
  (* apply Classical_Prop.EqdepTheory.inj_pair2 in Hij. *)
  rewrite Vector.map_map in Hijuv.
  intros.
  eapply vector_map_ext_in' in Hijuv; eauto.
  do 2 fold_syntax_class.
  eapply fact1; eauto.
Qed.

Class Fact1Twice A `{Stale A} `{Open value A} := fact1_twice :
forall (u v1 v2: value) (e: A) i j1 j2,
    i <> j1 -> i <> j2 -> j1 <> j2 ->
    {i ~> u} ({j1 ~> v1} ({j2 ~> v2} e)) = {j1 ~> v1} ({j2 ~> v2} e) -> {i ~> u} e = e.

Lemma Fact1Twice_all 
  (A : Type)
  (staleA : Stale A)
  (openA  : Open value A)
  (fact1A : @Fact1 A staleA openA)
  : @Fact1Twice A staleA openA.
Proof.
  unfold Fact1Twice.
  intros u v1 v2 e i j1 j2 Hij1 Hij2 Hj1j2 Hij1v2v1.
  assert ({i ~> u} ({j2 ~> v2} e) = {j2 ~> v2} e).
  eapply fact1 with (j := j1) (v:= v1); eauto.
  eapply fact1 with (j := j2) (v:= v2); eauto.
Qed.

#[global] Instance Fact1Twice_value: Fact1Twice value.
Proof.
  apply Fact1Twice_all. all: typeclasses eauto.
Qed.
Arguments Fact1Twice_value /.

#[global] Instance Fact1Twice_qualifier: Fact1Twice qualifier.
Proof.
  apply Fact1Twice_all. all: typeclasses eauto.
Qed.
Arguments Fact1Twice_qualifier /.



Class OpenRecBody A `{Stale A} `{Open value A} `{Lc A} := open_rec_body :
forall (e: A), body e -> forall (k: nat) (v: value), {S k ~> v} e = e.

#[global] Instance OpenRecBody_qualifier: OpenRecBody qualifier.
Proof.
  unfold OpenRecBody.
  intros ϕ Hlc k v. destruct ϕ. apply lc_phi1_body in Hlc.
  ln_simpl. f_equal.
  rewrite <- Vector.map_id.
  apply Vector.map_ext_in.
  intros.
  rewrite Vector.Forall_forall in Hlc.
  ospecialize * Hlc; eauto.
  destruct Hlc.
  auto_pose_fv y.
  apply fact1 with (j := 0) (v:= y). lia.
  rewrite open_rec_lc; eauto. auto_apply. my_set_solver.
Qed.
Arguments OpenRecBody_qualifier /.

Class OpenRecBody2 A `{Stale A} `{Open value A} `{Lc A} := open_rec_body2 :
forall (e: A), body2 e -> forall (k: nat) (v: value), {S (S k) ~> v} e = e.

(* NOTE: Very very annoying, when qualifier has builtin 1 or 2 arguments. *)

#[global] Instance OpenRecBody2_qualifier: OpenRecBody2 qualifier.
Proof.
  unfold OpenRecBody2.
  intros ϕ Hlc k v. destruct ϕ. apply lc_phi2_body in Hlc.
  ln_simpl. f_equal.
  rewrite <- Vector.map_id.
  apply Vector.map_ext_in.
  intros.
  rewrite Vector.Forall_forall in Hlc.
  ospecialize * Hlc; eauto.
  destruct Hlc.
  auto_pose_fv y1.
  auto_pose_fv y2.
  ospecialize * (H0 y1 _ y2); eauto. my_set_solver. my_set_solver.
  fold_syntax_class.
  eapply (fact1_twice _ y2 y1 _ _ 0 1); eauto.
  rewrite open_rec_lc; eauto.
Qed.
Arguments OpenRecBody2_qualifier /.

#[global] Instance LcImpliesBody_qualifier: LcImpliesBody qualifier.
Proof.
  eapply LcImpliesBody_all. all: typeclasses eauto.
Qed.