From stdpp Require Import mapset.
From CT.Syntax Require Import Syntax.
From CT.LocallyNameless Require Import Lc.

Import BaseDef MyTactics Primitives Lang Lc.
Import LangLc.

Inductive eval_op: effop -> constant -> constant -> Prop :=
| eval_op_plus_one: forall (a: nat), eval_op op_plus_one a (1 + a)
| eval_op_eq_zero: forall (a: nat), eval_op op_eq_zero a (Nat.eqb a 0)
| eval_op_rannat: forall (a b: nat), eval_op op_rannat a b.

Global Hint Constructors eval_op: core.

Notation "'⇓{' op '~' c1 '}{' c '}' " := (eval_op op c1 c)
                                           (at level 30, format "⇓{ op ~ c1 }{ c }", c1 constr, c constr).

(** This file defines the operational semantics of the core language. *)

Reserved Notation "t1 '↪' t2" (at level 60, t1 constr, t2 constr).

Inductive step : tm -> tm -> Prop :=
| STEffOp: forall op (c1 c: constant) e,
    body e -> lc (vconst c1) -> lc (vconst c) ->
    ⇓{op ~ c1}{c} -> (tleteffop op c1 e) ↪ (e ^^ (vconst c))
| STLetE1: forall e1 e1' e,
    body e ->
    e1 ↪ e1' ->
    (tlete e1 e) ↪ (tlete e1' e)
| STLetE2: forall (v1: value) e,
    lc v1 -> body e ->
    (tlete (treturn v1) e) ↪ (e ^^ v1)
| STLetAppLam: forall T (v_x: value) e1 e,
    body e1 -> body e -> lc v_x ->
    (tletapp (vlam T e1) v_x e) ↪ tlete (e1 ^^ v_x) e
| STLetAppFix: forall T_f (v_x: value) (e1: tm) e,
    body (vlam T_f e1) -> lc v_x -> body e ->
    tletapp (vfix T_f (treturn (vlam T_f e1))) v_x e ↪
      tletapp ((vlam T_f e1) ^^ v_x) (vfix T_f (treturn (vlam T_f e1))) e
| STMatchbTrue: forall e1 e2,
    lc e1 -> lc e2 ->
    (tmatchb true e1 e2) ↪ e1
| STMatchbFalse: forall e1 e2,
    lc e1 -> lc e2 ->
    (tmatchb false e1 e2) ↪ e2
where "t1 '↪' t2" := (step t1 t2).

Inductive multistep : tm -> tm -> Prop :=
| multistep_refl : forall (e : tm),
    lc e -> multistep e e
| multistep_step : forall (x y z: tm),
    x ↪ y ->
    multistep y z ->
    multistep x z.

Notation " t1 '↪*' t2" := (multistep t1 t2) (at level 60, t1 constr, t2 constr).

Global Hint Constructors multistep : core.

(** * Properties of operational semantics *)

Lemma body_vbvar: forall bn, body (vbvar bn) <-> bn = 0.
Proof.
  split; intros.
  - invclear H. auto_pose_fv y. specialize_with y. ln_simpl; eauto.
    inversion H0.
  - hauto. 
Qed.

Ltac lc_solver_aux2 :=
  match goal with
  | [H: lc (treturn ?v) |- lc ?v ] => sinvert H; auto
  | [H: lc ?v |- lc (treturn ?v) ] => econstructor; eauto
  | [H: body (vlam _ _) |- _ ] => rewrite body_abs_iff_body2 in H; mydestr; auto
  | [H: body2 ?e |- body (vlam _ ?e) ] => rewrite body_abs_iff_body2; auto
  | [H: body2 ?e |- body ({1 ~> ?u} ?e) ] => apply open_body; auto
  | [H: body ?e |- lc ({0 ~> ?u} ?e) ] => apply open_lc; auto
  | [H: body (vbvar _) |- _ ] => rewrite body_vbvar in H; subst; auto
  | [ |- body (vbvar _) ] => apply body_vbvar; auto
  | [H: lc ?e |- lc ({?i ~> ?u} ?e) ] => rewrite open_rec_lc; auto
  | _ => lc_solver_aux1
  end.

Ltac lc_solver:= 
autounfold with class_simpl; simpl; mydestr; auto; fold_syntax_class;
repeat (lc_solver_aux2; auto); fold_syntax_class.

Lemma step_regular: forall e1 e2, e1 ↪ e2 -> lc e1 /\ lc e2.
Proof.
  intros.
  induction H; split; auto; lc_solver.
Qed.

Lemma step_regular1: forall e1 e2, e1 ↪ e2 -> lc e1.
Proof.
  intros. apply step_regular in H. hauto.
Qed.

Lemma step_regular2: forall e1 e2, e1 ↪ e2 -> lc e2.
Proof.
  intros. apply step_regular in H. hauto.
Qed.

Global Hint Resolve step_regular1: core.
Global Hint Resolve step_regular2: core.

Theorem multistep_trans: forall (x y z : tm), x ↪* y -> y ↪* z -> x ↪* z.
Proof.
  intros. generalize dependent z.
  induction H; eauto.
Qed.

Theorem multistep_R : forall (x y : tm),
    x ↪ y -> x ↪* y.
Proof. eauto. Qed.

Lemma multi_step_regular: forall e1 e2, e1 ↪* e2 -> lc e1 /\ lc e2.
Proof.
  induction 1; intuition eauto.
Qed.

Lemma multi_step_regular1: forall e1 e2, e1 ↪* e2 -> lc e1.
Proof.
  intros. apply multi_step_regular in H. destruct H; auto.
Qed.

Lemma multi_step_regular2: forall e1 e2, e1 ↪* e2 ->  lc e2.
Proof.
  intros. apply multi_step_regular in H. destruct H; auto.
Qed.

Lemma value_reduction_refl: forall (v1: value) v2, (treturn v1) ↪* (treturn v2) -> v2 = v1.
Proof.
  intros * H. sinvert H; easy.
Qed.

Lemma reduction_tlete:  forall e_x e (v : value),
    tlete e_x e ↪* (treturn v) -> (exists (v_x: value), e_x ↪* (treturn v_x) /\ (e ^^ v_x) ↪* (treturn v)).
Proof.
  intros.
  remember (tlete e_x e). remember (treturn v).
  generalize dependent e_x.
  induction H; intros; subst. easy.
  sinvert H.
  - ospecialize* IHmultistep; eauto.
    simp_hyps. repeat esplit; eauto.
  - repeat esplit. econstructor; eauto. lc_solver. eauto.
Qed.

Lemma reduction_tlete':  forall e_x e (v_x v : value),
    (* NOTE: This condition is unnecessary as it should be implied by the
    regularity lemma. Remove later when we bother proving a few more naming
    lemmas. *)
    body e ->
    e_x ↪* (treturn v_x) ->
    (e ^^ v_x) ↪* (treturn v) ->
    tlete e_x e ↪* (treturn v).
Proof.
  intros * Hb H. remember (treturn v_x).
  induction H; intros; subst.
  - lc_solver. econstructor; eauto using STLetE2.
  - simp_hyps.
    simplify_list_eq.
    econstructor.
    econstructor; eauto.
    eauto.
Qed.

Lemma reduction_tlete_iff:
  ∀ (e_x e : tm) (v : value),
    tlete e_x e ↪* (treturn v)
    <-> (body e /\ ∃ (v_x : value),
          e_x ↪* (treturn v_x) ∧ e ^^ v_x ↪* (treturn v)).
Proof.
  split.
  - split. apply multi_step_regular in H. simp_hyps. lc_solver.
    apply reduction_tlete; eauto.
  - intros. simp_hyps. eapply reduction_tlete'; eauto.
Qed.

Lemma reduction_mk_app_v_v (f v_x v : value) :
  lc v_x ->
  mk_app (treturn f) (treturn v_x) ↪* (treturn v) ->
  tletapp f v_x (treturn (vbvar 0)) ↪* (treturn v).
Proof.
  intros Hlc H.
  sinvert H. sinvert H0. easy.
  sinvert H1. sinvert H. easy.
  ln_simpl. 
  repeat rewrite open_rec_lc in * by eauto. eauto.
Qed.

Lemma body_mk_app_aux2 (f: value): lc f -> body (tletapp f (vbvar 0) (treturn (vbvar 0))).
Proof.
  intros Hlc. auto_exists_L. intros x Hx.
  ln_simpl.
  apply letapp_lc_body. repeat split; lc_solver. 
Qed.

Lemma body_mk_app_aux v_x:
  lc v_x ->
  body (tlete v_x (tletapp (vbvar 1) (vbvar 0) (treturn (vbvar 0)))).
Proof.
  intros Hlc. auto_exists_L. intros x Hx.
  ln_simpl.
  apply lete_lc_body. repeat split; lc_solver.
  apply body_mk_app_aux2; lc_solver.
Qed.

Lemma reduction_mk_app_v_v' (f v_x v : value) :
  tletapp f v_x (treturn (vbvar 0)) ↪* (treturn v) ->
  mk_app (treturn f) (treturn v_x) ↪* (treturn v).
Proof.
  intros H.
  assert (lc v_x). {
    apply multi_step_regular1 in H. sinvert H. eauto.
  }
  assert (lc f). {
    apply multi_step_regular1 in H. sinvert H. eauto.
  }
  eapply_eq multistep_step.
  eapply STLetE2; eauto.
  - apply body_mk_app_aux; eauto. lc_solver.
  - ln_simpl. rewrite open_rec_lc; eauto.
    eapply_eq multistep_step.
    eapply STLetE2; eauto.
    ln_simpl. by rewrite open_rec_lc.
Qed.

Lemma open_vlam_rev k Tb e (v: value): vlam Tb ({S k ~> v} e) = {k ~> v} (vlam Tb e).
Proof. eauto. Qed.

Lemma reduction_mk_app_lam Tb e (v_x : value) (v : value) :
  lc v_x ->
  mk_app (treturn (vlam Tb e)) (treturn v_x) ↪* (treturn v) ->
  (e ^^ v_x) ↪* (treturn v).
Proof.
  unfold mk_app. intros Hlc H.
  assert (lc (vlam Tb e)) as Haux. {
    apply multi_step_regular1 in H. sinvert H. lc_solver. 
  }
  apply reduction_tlete in H. simp_hyps. ln_simpl.
  rewrite open_rec_lc in H1; eauto.
  apply value_reduction_refl in H0; sinvert H0.
  apply reduction_tlete in H1. simp_hyps. ln_simpl.
  apply value_reduction_refl in H1; sinvert H1.
  rewrite open_vlam_rev in H2.
  rewrite open_rec_lc in H2; eauto.
  sinvert H2. sinvert H0.
  apply reduction_tlete in H1.
  simp_hyps. ln_simpl.
  eapply multistep_trans; eauto.
Qed.

Lemma reduction_mk_app_lam' Tb e (v_x : value) (v : value) :
  lc v_x ->
  (* NOTE: This condition is unnecessary as it should be implied by the
  regularity lemma. *)
  body e ->
  e ^^ v_x ↪* (treturn v) ->
  mk_app (treturn (vlam Tb e)) (treturn v_x) ↪* (treturn v).
Proof.
  unfold mk_app. intros Hlc Hb H.
  assert (lc (treturn v_x)) as Hlc_tm by lc_solver.
  assert (lc (vlam Tb e)) as Haux by lc_solver.
  assert (lc (treturn (vlam Tb e))) as Haux_tm by lc_solver.
  assert (lc v) as Hlc_v. { apply multi_step_regular in H. lc_solver. }
  assert (lc (treturn v)) as Hlc_v_tm by lc_solver.
  apply reduction_tlete' with (v_x := vlam Tb e); eauto.
  apply body_mk_app_aux; lc_solver.
  ln_simpl. rewrite open_rec_lc; eauto.
  apply reduction_tlete' with (v_x := v_x); eauto.
  ln_simpl. rewrite open_vlam_rev; rewrite open_rec_lc; eauto.
  eapply_eq multistep_step. econstructor; eauto. lc_solver.
  apply reduction_tlete' with (v_x := v); eauto. lc_solver.
Qed.

Lemma reduction_tletapp:  forall v1 v2 e (v : value),
    tletapp v1 v2 e ↪* (treturn v) ->
    (exists (v_x: value), tletapp v1 v2 (treturn (vbvar 0)) ↪* (treturn v_x) /\ (e ^^ v_x) ↪* (treturn v)).
Proof.
  intros.
  remember (tletapp v1 v2 e). remember (treturn v).
  generalize dependent v2.
  generalize dependent v1.
  induction H; intros; subst. easy.
  simp_hyps. sinvert H.
  - eapply reduction_tlete in H0. simp_hyps.
    assert (lc (treturn v_x)) as Hlc_tm by solve [apply multi_step_regular2 in H0; eauto].
    simplify_list_eq.
    eexists _. repeat split; eauto using reduction_mk_app_lam'.
    eapply_eq multistep_step. econstructor; eauto. lc_solver.
    eapply reduction_tlete'; eauto. lc_solver.
  - simplify_list_eq.
    ospecialize* H1; eauto. simp_hyps.
    eexists _.
    repeat split; cycle 1; eauto.
    eapply_eq multistep_step. econstructor; eauto. lc_solver.
    ln_simpl. eauto.
Qed.

Lemma reduction_tletapp':  forall v1 v2 e (v : value),
    (body e /\ exists (v_x: value), tletapp v1 v2 (treturn (vbvar 0)) ↪* (treturn v_x) /\ (e ^^ v_x) ↪* (treturn v)) -> tletapp v1 v2 e ↪* (treturn v).
Proof.
  intros. destruct H as (He & (v_x & Hv_x & H)).
  remember (tletapp v1 v2 (treturn (vbvar 0))). remember (treturn v_x).
  generalize dependent v2.
  generalize dependent v1.
  generalize dependent v_x.
  induction Hv_x; intros; subst. easy.
  simp_hyps. sinvert H.
  - clear IHHv_x.
    eapply reduction_tlete in Hv_x. simp_hyps. ln_simpl.
    apply value_reduction_refl in H2; invclear H2. clear H.
    eapply_eq multistep_step. econstructor; eauto.
    eapply reduction_tlete'; eauto.
  - ospecialize* IHHv_x; eauto.
    eapply_eq multistep_step. econstructor; eauto.
    ln_simpl. eauto.
Qed.

Lemma reduction_tletapp_iff:  forall v1 v2 e (v : value),
    tletapp v1 v2 e ↪* (treturn v) <-> (body e /\ exists (v_x: value), tletapp v1 v2 (treturn (vbvar 0)) ↪* (treturn v_x) /\ (e ^^ v_x) ↪* (treturn v)).
Proof.
  split; intros.
  - split. apply multi_step_regular1 in H. lc_solver.
    apply reduction_tletapp; eauto.
  - apply reduction_tletapp'; eauto.
Qed.

Lemma value_reduction_any_ctx: forall (v1: value), lc v1 -> (treturn v1) ↪* (treturn v1).
Proof.
  intros. econstructor; eauto. lc_solver.
Qed.

Lemma reduction_tleteffop:  forall op v2 e (v : value),
    (tleteffop op v2 e) ↪* (treturn v) ->
    exists (c2 c_x: constant),
      v2 = c2 /\ ⇓{op ~ c2}{ c_x } /\ (e ^^ (vconst c_x)) ↪* (treturn v).
Proof.
  intros.
  sinvert H. sinvert H0.
  eauto 10.
Qed.

Lemma reduction_tleteffop_iff:  forall op v2 e (v : value),
    (tleteffop op v2 e) ↪* (treturn v) <->
      body e /\ exists (c2 c_x: constant),
        v2 = c2 /\ ⇓{op ~ c2}{ c_x } /\ (e ^^ (vconst c_x)) ↪* (treturn v).
Proof.
  split.
  - intuition.
    + apply multi_step_regular in H. simp_hyps. rewrite leteffop_lc_body in H. intuition.
    + apply reduction_tleteffop; eauto.
  - intros. simp_hyps. subst. repeat (econstructor; eauto).
Qed.

Lemma reduction_matchb_true:  forall e1 e2 (v : value),
    tmatchb true e1 e2 ↪* (treturn v) -> e1 ↪* (treturn v).
Proof.
  intros.
  sinvert H.
  sinvert H0. simplify_list_eq. eauto.
Qed.

Lemma reduction_matchb_false:  forall e1 e2 (v : value),
    tmatchb false e1 e2 ↪* (treturn v) -> e2 ↪* (treturn v).
Proof.
  intros.
  sinvert H.
  sinvert H0. simplify_list_eq. eauto.
Qed.

Ltac step_regular_simp :=
  repeat match goal with
    | [H: _ ↪* _ |- _ ] =>
      first
        [ lazymatch goal with
          | |- lc _ => idtac
          | |- body _ => idtac
          | |- body2 _ => idtac
          end;
          apply multi_step_regular in H; destruct H; auto
        | fail 1 ]
    | [H: _ ↪ _ |- _ ] =>
      first
        [ lazymatch goal with
          | |- lc _ => idtac
          | |- body _ => idtac
          | |- body2 _ => idtac
          end;
          apply step_regular in H; destruct H; auto
        | fail 1 ]
    | H: (treturn _) ↪* (treturn _)  |- _ =>
      apply value_reduction_refl in H; simp_hyps; simplify_eq
    | [|- ?e ↪ ?e ] => econstructor; eauto
    end.

(** NOTE: reduction lemmas for underapproximation *)

Ltac lc_solver_aux3 :=
  match goal with
  | [H: lc (tlete _ _) |- lc _] => rewrite lete_lc_body in H; simp_hyps
  | [H: lc (tlete _ _) |- body _] => rewrite lete_lc_body in H; simp_hyps
  | _ => lc_solver_aux2
  end.

Ltac lc_solver3 :=
  ln_simpl;
  step_regular_simp; eauto;
  repeat (lc_solver_aux3; auto); fold_syntax_class.

(* Lemma reduction_tlete: forall (v1: value) e2,
  forall (v: value), tlete v1 e2 ↪* v <-> (lc v1 /\ body e2 /\ e2 ^^ v1 ↪* v).
Proof.
  split; intros.
  - assert (lc v1) by lc_solver_plus.
    assert (body e2) by lc_solver_plus. intuition.
    apply reduction_tlete in H. simp_hyps.
    apply value_reduction_refl in H2. simp_hyps. subst; intuition.
  - simp_hyps. eapply reduction_tlete'; eauto.
Qed. *)

Lemma reduction_nest_tlete: forall e,
  forall (v: value), tlete e (treturn (vbvar 0)) ↪* (treturn v) <-> e ↪* (treturn v).
Proof.
  intros e. split; intros.
  - apply reduction_tlete in H. lc_solver3.
  - eapply reduction_tlete'; lc_solver3.
    econstructor. lc_solver3.
Qed.

Lemma reduction_tletapp_lam:  forall T e1 v2 e (v : value),
    tletapp (vlam T e1) v2 e ↪* (treturn v) <->
      (lc v2 /\ lc (vlam T e1) /\ tlete (e1 ^^ v2) e ↪* (treturn v)).
Proof.
  split; intros.
  - invclear H. invclear H0. repeat split; lc_solver3.
  - simp_hyps. eapply_eq multistep_step; eauto.
    apply multi_step_regular1 in H2; eauto.
    rewrite lete_lc_body in H2; simp_hyps; eauto.
    econstructor; eauto. lc_solver.
Qed.

Lemma reduction_tletapp_fix:  forall T_f (v_x: value) (e1: tm) e (v : value),
      tletapp (vfix T_f (treturn (vlam T_f e1))) v_x e ↪* (treturn v) <->
        (lc v_x /\ tletapp ((vlam T_f e1) ^^ v_x) (vfix T_f (treturn (vlam T_f e1))) e ↪* (treturn v)).
Proof.
  split; intros.
  - inversion H; subst. inversion H0; subst; eauto.
  - simp_hyps. eapply_eq multistep_step; eauto.
    apply multi_step_regular in H0; simp_hyps; eauto.
    econstructor; eauto. rewrite letapp_lc_body in H0. simp_hyps.
    lc_solver. lc_solver.
Qed.

Lemma reduction_mk_app_iff:  forall e e_x (v : value),
    lc e_x ->
    mk_app e e_x ↪* (treturn v) <->
      (exists (f v_x: value), e ↪* (treturn f) /\ e_x ↪* (treturn v_x) /\ tletapp f v_x (treturn (vbvar 0)) ↪* (treturn v)).
Proof.
  intros e e_x v Hlc.
  unfold mk_app.
  split; intros.
  - apply reduction_tlete in H. destruct H as (f & Hf & H).
    ln_simpl. rewrite open_rec_lc in H by eauto.
    apply reduction_tlete in H. destruct H as (v_x & Hv_x & H).
    ln_simpl. rewrite open_rec_lc in H by lc_solver3.
    exists f, v_x. intuition.
  - destruct H as (f & v_x & Hf & Hv_x & H).
    eapply reduction_tlete'; eauto. apply body_mk_app_aux; eauto.
    ln_simpl. rewrite open_rec_lc; eauto.
    eapply reduction_tlete'; eauto. apply body_mk_app_aux2. by lc_solver3.
    ln_simpl. rewrite open_rec_lc; eauto.
    lc_solver3.
Qed.
