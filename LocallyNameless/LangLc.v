From stdpp Require Import mapset.
From CT Require Import Syntax.Syntax.
From CT Require Import MyTactics.
Import Primitives.
Import BaseDef.
From Hammer Require Import Tactics.

(** This file provides the infrastructure for reasoning about locally nameless
  representation for the core language. Most lemmas in this file are inspired by
  Arthur Chargu´eraud's paper "The Locally Nameless Representation" :
  https://chargueraud.org/research/2009/ln/main.pdf *)

Lemma constant_eqb_spec: forall (c c': constant), c = c' \/ c <> c'.
Proof with eauto.
  destruct c, c'...
  - destruct b, b0; firstorder.
  - destruct (Nat.eq_dec n n0); firstorder.
    right. intro HH. inversion HH...
Qed.

Ltac specialize_L :=
  match goal with
  | [ H : forall (x: atom), x ∉ ?L -> _ |- _] => specialize (H (fv_of_set L) (fv_of_set_fresh L))
  end.

Lemma lc_exfalso: forall bn, ~ lc (vbvar bn).
Proof.
  intros bn HF. inversion HF.
Qed.

Lemma body_exfalso1: forall bn, ~ body (vbvar (S bn)).
Proof.
  intros bn HF. inversion HF. specialize_L. inversion H.
Qed.

Lemma body_exfalso: forall bn, ~ body (treturn (vbvar (S bn))).
Proof.
  intros bn HF. inversion HF. specialize_L. inversion H. inversion H1.
Qed.

Ltac solve_lc_exfalso :=
  match goal with
    | [ H: lc (treturn (vbvar ?n)) |- _ ] => exfalso; apply (lc_exfalso n); auto
    | [ H: body (treturn (vbvar (S ?n))) |- _ ] => exfalso; apply (body_exfalso n); auto
  end.

Lemma lc_abs_iff_body: forall T e, lc (vlam T e) <-> body e.
Proof.
  split; unfold body; intros.
  - inversion H; subst. exists L. auto.
  - destruct H as (L & HL). eapply lc_vlam. apply HL.
Qed.

Lemma lc_return_iff_lc_value: forall v, lc (treturn v) <-> lc v.
Proof.
  split; intros.
  - inversion H; subst. auto.
  - constructor. auto.
Qed.

Lemma body_return_iff_body_value: forall v, body (treturn v) <-> body v.
Proof.
  unfold body;
  split; intros.
  - mydestr. auto_exists_L. intros y Hy. specialize_with y.
    ln_simpl; eauto.
    rewrite <- lc_return_iff_lc_value; eauto.
  - mydestr. auto_exists_L. intros y Hy. specialize_with y.
    ln_simpl; eauto.
    rewrite lc_return_iff_lc_value; eauto.
Qed.

Ltac rewrite_by_set_solver :=
  repeat
  match goal with
  | H: context [ _ ->  _ = _ ]  |- _ => erewrite H; eauto; fast_set_solver!!
  end; auto.

(* Ltac dec_tf := try (subst; rewrite decide_True; auto; fast_set_solver); try (rewrite decide_False; auto; fast_set_solver). *)

(* We keep [Stale], [Open] and [Close] as explicit class parameters so that
   the definition is well-typed for arbitrary [A], but in all our concrete
   uses (e.g. [A = tm]) these parameters are instantiated with the canonical
   global instances from [Syntax.Lang]. *)
Class CloseOpenVar A `{Stale A} `{Open value A} `{Close A} := close_open_var :
  forall (e: A) (x: atom) (k: nat), x # e -> {k <~ x} ({k ~> (vfvar x)} e) = e.

#[global] Instance CloseOpenVar_tm : CloseOpenVar tm.
Proof.
  unfold CloseOpenVar.
  apply (tm_mutual_rec
           (fun (v: value) => forall (x: atom) (k: nat), x # v -> {k <~ x} ({k ~> (vfvar x)} v) = v)
           (fun (e: tm) => forall (x: atom) (k: nat), x # e -> {k <~ x} ({k ~> (vfvar x)} e) = e)
        ); autounfold with class_simpl; simpl; intros; mydestr; try f_equal; rewrite_by_set_solver.
  - my_set_solver.
  - hauto.
Qed.
Arguments CloseOpenVar_tm /.

#[global] Instance CloseOpenVar_value : CloseOpenVar value.
Proof.
  unfold CloseOpenVar.
  apply (value_mutual_rec
           (fun (v: value) => forall (x: atom) (k: nat), x # v -> {k <~ x} ({k ~> (vfvar x)} v) = v)
           (fun (e: tm) => forall (x: atom) (k: nat), x # e -> {k <~ x} ({k ~> (vfvar x)} e) = e)
        ); autounfold with class_simpl; simpl; intros; mydestr; try f_equal; rewrite_by_set_solver.
  - my_set_solver.
  - hauto.
Qed.
Arguments CloseOpenVar_value /.

Class OpenFv A `{Stale A} `{Open value A} := open_fv :
   forall (v: A) (u: value) (k: nat), 
   stale ({k ~> u} v) ⊆ stale u ∪ stale v.

#[global] Instance OpenFv_value : OpenFv value.
Proof.
  unfold OpenFv.
  apply (value_mutual_rec
           (fun (v: value) => forall (u: value) (k: nat), fv_value ({k ~> u} v) ⊆ fv_value u ∪ fv_value v)
           (fun (e: tm) => forall (u: value) (k: nat), fv_tm ({k ~> u} e) ⊆ fv_value u ∪ fv_tm e)
        ); autounfold with class_simpl; simpl; intros; mydestr;
    try (intros; repeat rewrite_by_set_solver; auto);
    set_solver.
Qed.
Arguments OpenFv_value /.

#[global] Instance OpenFv_tm : OpenFv tm.
Proof.
  unfold OpenFv.
  apply (tm_mutual_rec
           (fun (v: value) => forall (u: value) (k: nat), stale ({k ~> u} v) ⊆ stale u ∪ stale v)
           (fun (e: tm) => forall (u: value) (k: nat), stale ({k ~> u} e) ⊆ stale u ∪ stale e)
        ); autounfold with class_simpl; simpl; intros; mydestr;
    try (intros; repeat rewrite_by_set_solver; auto); set_solver.
Qed.
Arguments OpenFv_tm /.

Class OpenFvPrime A `{Stale A} `{Open value A} := open_fv' :
forall (v: A) (u: value) (k: nat), stale v ⊆ stale ({k ~> u} v).

#[global] Instance OpenFvPrime_value : OpenFvPrime value.
Proof.
  unfold OpenFvPrime.
  apply (value_mutual_rec
           (fun (v: value) => forall (u: value) (k: nat), stale v ⊆ stale ({k ~> u} v))
           (fun (e: tm) => forall (u: value) (k: nat), stale e ⊆ stale ({k ~> u} e))
        ); autounfold with class_simpl; simpl; intros; mydestr;
    try (intros; repeat rewrite_by_set_solver; auto); set_solver.
Qed.
Arguments OpenFvPrime_value /.

#[global] Instance OpenFvPrime_tm : OpenFvPrime tm.
Proof.
  unfold OpenFvPrime.
  apply (tm_mutual_rec
           (fun (v: value) => forall (u: value) (k: nat), stale v ⊆ stale ({k ~> u} v))
           (fun (e: tm) => forall (u: value) (k: nat), stale e ⊆ stale ({k ~> u} e))
        ); autounfold with class_simpl; simpl; intros; mydestr;
    try (intros; repeat rewrite_by_set_solver; auto); set_solver.
Qed.
Arguments OpenFvPrime_tm /.

Class CloseVarFv A `{Stale A} `{Close A} := close_var_fv :
forall (v: A) (x: atom) (k: nat), stale ({k <~ x} v) = (stale v) ∖ {[x]}.

#[global] Instance CloseVarFv_value : CloseVarFv value.
Proof.
  unfold CloseVarFv.
  apply (value_mutual_rec
           (fun (v: value) => forall (x: atom) (k: nat), stale ({k <~ x} v) = (stale v) ∖ {[x]})
           (fun (e: tm) => forall (x: atom) (k: nat), stale ({k <~ x} e) = (stale e) ∖ {[x]})
        ); autounfold with class_simpl; simpl; intros; mydestr; rewrite_by_set_solver.
        all: my_set_solver.
Qed.
Arguments CloseVarFv_value /.

#[global] Instance CloseVarFv_tm : CloseVarFv tm.
Proof.
  unfold CloseVarFv.
  apply (tm_mutual_rec
           (fun (v: value) => forall (x: atom) (k: nat), stale ({k <~ x} v) = (stale v) ∖ {[x]})
           (fun (e: tm) => forall (x: atom) (k: nat), stale ({k <~ x} e) = (stale e) ∖ {[x]})
        ); autounfold with class_simpl; simpl; intros; mydestr; rewrite_by_set_solver.
        all: my_set_solver.
Qed.
Arguments CloseVarFv_tm /.

Class SubstFresh A `{Stale A} `{Subst value A} := subst_fresh :
forall (v: A) (x:atom) (u: value), x # v -> {x := u} v = v.

#[global] Instance SubstFresh_value : SubstFresh value.
Proof.
  unfold SubstFresh.
  apply (value_mutual_rec
           (fun (v: value) => forall (x:atom) (u: value), x # v -> {x := u} v = v)
           (fun (e: tm) => forall (x:atom) (u: value), x # e -> {x := u} e = e)
        ); autounfold with class_simpl; simpl; intros; mydestr; try f_equal; rewrite_by_set_solver.
        - my_set_solver.
Qed.
Arguments SubstFresh_value /.

#[global] Instance SubstFresh_tm : SubstFresh tm.
Proof.
  unfold SubstFresh.
  apply (tm_mutual_rec
           (fun (v: value) => forall (x:atom) (u: value), x ∉ (fv_value v) -> {x := u} v = v)
           (fun (e: tm) => forall (x:atom) (u: value), x ∉ (fv_tm e) -> {x := u} e = e)
        ); autounfold with class_simpl; simpl; intros; mydestr; try f_equal; rewrite_by_set_solver.
        - my_set_solver.
Qed.
Arguments SubstFresh_tm /.

Ltac ex_specialize_L :=
  match goal with
  | [ H : ex (fun (L: aset) => _) |- _] => destruct H; specialize_L
  end.

(** There is a typo in the paper *)
Class Fact1 A `{Stale A} `{Open value A} := fact1 :
forall (u v: value) (e: A) i j,
    i <> j -> {i ~> u} ({j ~> v} e) = {j ~> v} e -> {i ~> u} e = e.

#[global] Instance Fact1_tm : Fact1 tm.
Proof.
  unfold Fact1.
  intros u v.
  apply (tm_mutual_rec
  (fun (e: value) => forall i j, i <> j -> {i ~> u} ({j ~> v} e) = {j ~> v} e -> {i ~> u} e = e)
  (fun (e: tm) => forall i j, i <> j -> {i ~> u} ({j ~> v} e) = {j ~> v} e -> {i ~> u} e = e)
); autounfold with class_simpl; simpl; intros; mydestr; rewrite_by_set_solver; try hauto.
Qed.
Arguments Fact1_tm /.

#[global] Instance Fact1_value : Fact1 value.
Proof.
  unfold Fact1.
  intros u v.
  apply (value_mutual_rec
           (fun (e: value) => forall i j, i <> j -> {i ~> u} ({j ~> v} e) = {j ~> v} e -> {i ~> u} e = e)
           (fun (e: tm) => forall i j, i <> j -> {i ~> u} ({j ~> v} e) = {j ~> v} e -> {i ~> u} e = e)
        ); autounfold with class_simpl; simpl; intros; mydestr; rewrite_by_set_solver; try hauto.
Qed.
Arguments Fact1_value /.

Ltac solve_let_lc_body H :=
  split; intros; try repeat split; auto;
    inversion H; subst; auto;
    try destruct_hyp_conj; try match goal with
    | [ H: body _ |- _ ] => inversion H; subst; clear H
    (* | [ H: lc _ |- _ ] => inversion H; subst; clear H *)
    end;
    auto_exists_L; intros; repeat split; auto;
    auto_apply; my_set_solver.

Lemma lete_lc_body: forall e1 e, lc (tlete e1 e) <-> lc e1 /\ body e.
Proof.
  solve_let_lc_body H.
Qed.

Lemma letapp_lc_body: forall (v1 v2: value) e, lc (tletapp v1 v2 e) <-> lc v1 /\ lc v2 /\ body e.
Proof.
  solve_let_lc_body H.
Qed.

Lemma leteffop_lc_body: forall op (v1: value) e, lc (tleteffop op v1 e) <-> lc v1 /\ body e.
Proof.
  solve_let_lc_body H.
Qed.

Lemma match_lc_body: forall (v: value) e1 e2, lc (tmatchb v e1 e2) <-> lc v /\ lc e1 /\ lc e2.
Proof.
  solve_let_lc_body H.
Qed.

Lemma lc_fix_iff_body: forall T e, lc (vfix T e) <-> body e.
Proof.
  split; unfold body; intros.
  - inversion H; subst. exists L. auto.
  - destruct H as (L & HL). econstructor. apply HL.
Qed.

Ltac lc_solver_aux1:=
  match goal with
    | [H: lc (vbvar _) |- _ ] => inversion H
    | [H: lc (treturn _) |- _ ] => rewrite lc_return_iff_lc_value in H; auto
    | [H: body (treturn _) |- _ ] => rewrite body_return_iff_body_value in H; auto
    | [H: lc (tlete _ _) |- body _ ] => rewrite lete_lc_body in H; mydestr; auto
    | [H: lc (tletapp _ _ _) |- body _ ] => rewrite letapp_lc_body in H; mydestr; auto
    | [H: lc (tleteffop _ _ _) |- body _ ] => rewrite leteffop_lc_body in H; mydestr; auto
    | [H: lc (vlam _ _) |- body _ ] => rewrite lc_abs_iff_body in H; mydestr; auto
    | [H: lc (vfix _ _) |- body _ ] => rewrite lc_fix_iff_body in H; mydestr; auto
    | [H: lc (tlete _ _) |- lc _ ] => rewrite lete_lc_body in H; mydestr; auto
    | [H: lc (tletapp _ _ _) |- lc _ ] => rewrite letapp_lc_body in H; mydestr; auto
    | [H: lc (tleteffop _ _ _) |- lc _ ] => rewrite leteffop_lc_body in H; mydestr; auto
    | [H: lc (tmatchb _ _ _) |- lc _ ] => rewrite match_lc_body in H; mydestr; auto
    | [H: lc (vlam _ _) |- lc _ ] => rewrite lc_abs_iff_body in H; mydestr; auto
    | [H: lc (vfix _ _) |- lc _ ] => rewrite lc_fix_iff_body in H; mydestr; auto
    | [ |- lc (treturn _)] => apply lc_treturn; auto
    | [ |- lc (terr _)] => apply lc_terr; auto
    | [ |- lc (vconst _)] => apply lc_vconst; auto
    | [ |- lc (vfvar _)] => constructor
    | [ |- lc (tmatchb _ _ _)] => apply lc_tmatchb; (repeat split; auto)
    | [ |- lc (tletapp _ _ _)] => rewrite letapp_lc_body; (repeat split; auto)
    | [ |- lc (tleteffop _ _ _)] => rewrite leteffop_lc_body; (repeat split; auto)
    | [ |- lc (tlete _ _)] => rewrite lete_lc_body; split; auto
    | [ |- lc (vfix _ _)] => rewrite lc_fix_iff_body; auto
    | [ |- lc (vlam _ _)] => rewrite lc_abs_iff_body; auto
    | [ |- lc (treturn _)] => rewrite lc_return_iff_lc_value; auto
    | [ |- body (treturn _)] => rewrite body_return_iff_body_value; auto
    | [ |- lc (tmatchb _ _ _)] => rewrite match_lc_body; (repeat split; auto)
    end.

Ltac lc_solver1:= 
  autounfold with class_simpl; simpl; mydestr; auto;
  repeat (lc_solver_aux1; auto); fold_syntax_class; eauto.

(* Lemma treturn_eq: forall (v1 v2: value), treturn v1 = treturn v2 -> v1 = v2.
Proof.
  intros. inversion H. auto.
Qed. *)

Class OpenRecLc A `{Stale A} `{Open value A} `{Lc A} := open_rec_lc :
forall (e: A), lc e -> forall (k: nat) (v: value), {k ~> v} e = e.

#[global] Instance OpenRecLc_tm : OpenRecLc tm.
Proof.
  unfold OpenRecLc.
  apply (lc_tm_mutual_rec
  (fun (e: value) _ => forall k (v: value), {k ~> v} e = e)
  (fun (e: tm) _ => forall k (v: value), {k ~> v} e = e)
  ); autounfold with class_simpl; simpl; intros; mydestr; f_equal; rewrite_by_set_solver; try hauto.   
  all:
    pose_fresh_fv y;
    apply fact1 with (j := 0) (v:= y); auto; auto_apply; my_set_solver.
Qed.
Arguments OpenRecLc_tm /.

#[global] Instance OpenRecLc_value : OpenRecLc value.
Proof.
  unfold OpenRecLc.
  apply (lc_value_mutual_rec
  (fun (e: value) _ => forall k (v: value), {k ~> v} e = e)
  (fun (e: tm) _ => forall k (v: value), {k ~> v} e = e)
  ); autounfold with class_simpl; simpl; intros; mydestr; f_equal; rewrite_by_set_solver; try hauto.   
  all:
    pose_fresh_fv y;
    apply fact1 with (j := 0) (v:= y); auto; auto_apply; my_set_solver.
Qed.
Arguments OpenRecLc_value /.

Class SubstOpen A `{Stale A} `{Open value A} `{Subst value A}  `{Lc A} := subst_open :
forall (e: A) (u: value) (w: value) (x:atom) (k: nat),
    lc w -> {x := w} ({k ~> u} e) = ({k ~> {x := w} u} ({x := w} e)).

#[global] Instance SubstOpen_tm : SubstOpen tm.
Proof.
  unfold SubstOpen.
  apply (tm_mutual_rec
  (fun (e: value) => forall (u: value) (w: value) (x:atom) (k: nat), lc w -> {x := w} ({k ~> u} e) = ({k ~> {x := w} u} ({x := w} e)))
  (fun (e: tm) => forall (u: value) (w: value) (x:atom) (k: nat), lc w -> {x := w} ({k ~> u} e) = ({k ~> {x := w} u} ({x := w} e)))
); autounfold with class_simpl; simpl; intros; mydestr; try f_equal; auto.
  - fold_syntax_class. repeat rewrite open_rec_lc; lc_solver1.
Qed.
Arguments SubstOpen_tm /.

#[global] Instance SubstOpen_value : SubstOpen value.
Proof.
  unfold SubstOpen.
  apply (value_mutual_rec
           (fun (e: value) => forall (u: value) (w: value) (x:atom) (k: nat), lc w -> {x := w} ({k ~> u} e) = ({k ~> {x := w} u} ({x := w} e)))
           (fun (e: tm) => forall (u: value) (w: value) (x:atom) (k: nat), lc w -> {x := w} ({k ~> u} e) = ({k ~> {x := w} u} ({x := w} e)))
        ); autounfold with class_simpl; simpl; intros; mydestr; try f_equal; auto.
  - fold_syntax_class. repeat rewrite open_rec_lc; lc_solver1.
Qed.
Arguments SubstOpen_value /.

Class CloseVarRename A `{Stale A} `{Close A} `{Subst value A} := close_var_rename :
forall (e: A) (x:atom) (y:atom) (k: nat),
    y # e -> {k <~ x} e = {k <~ y} ({x := vfvar y} e).

#[global] Instance CloseVarRename_tm : CloseVarRename tm.
Proof.
  unfold CloseVarRename.
  apply (tm_mutual_rec
           (fun (e: value) => forall (x:atom) (y:atom) (k: nat), y # e -> {k <~ x} e = {k <~ y} ({x := vfvar y} e))
           (fun (e: tm) => forall (x:atom) (y:atom) (k: nat), y # e -> {k <~ x} e = {k <~ y} ({x := vfvar y} e))
        ); autounfold with class_simpl; simpl; intros; mydestr; try f_equal; try (repeat rewrite_by_set_solver; auto).
  - hauto.
  - simpl; mydestr; auto. set_solver.
Qed.
Arguments CloseVarRename_tm /.

#[global] Instance CloseVarRename_value : CloseVarRename value.
Proof.
  unfold CloseVarRename.
  apply (value_mutual_rec
           (fun (e: value) => forall (x:atom) (y:atom) (k: nat), y # e -> {k <~ x} e = {k <~ y} ({x := vfvar y} e))
           (fun (e: tm) => forall (x:atom) (y:atom) (k: nat), y # e -> {k <~ x} e = {k <~ y} ({x := vfvar y} e))
        ); autounfold with class_simpl; simpl; intros; mydestr; try f_equal; try (repeat rewrite_by_set_solver; auto).
  - hauto.
  - simpl; mydestr; auto. set_solver.
Qed.
Arguments CloseVarRename_value /.

(* The second class of lemmas *)

Ltac rewrite_by_set_solver2 :=
  repeat match goal with
          | H: context [ _ ->  _ = _ ]  |- _ => erewrite H by (eauto; my_set_solver)
          end; auto.

Class Fact2 A `{Stale A} `{Open value A} `{Close A} := fact2 :
forall (e: A) (x y z: atom) (i j: nat),
    x <> y -> i <> j -> y # e ->
    {i ~> vfvar y} ({j ~> vfvar z} ({j <~ x} e)) = {j ~> vfvar z} ({j <~ x} ({i ~> vfvar y} e)).

#[global] Instance Fact2_tm : Fact2 tm.
Proof.
  unfold Fact2.
  apply (tm_mutual_rec
           (fun (e: value) => forall (x:atom) (y:atom) (z:atom) (i j: nat), x <> y -> i <> j -> y # e -> {i ~> vfvar y} ({j ~> vfvar z} ({j <~ x} e)) = {j ~> vfvar z} ({j <~ x} ({i ~> vfvar y} e)))
           (fun (e: tm) => forall (x:atom) (y:atom) (z:atom) (i j: nat), x <> y -> i <> j -> y # e -> {i ~> vfvar y} ({j ~> vfvar z} ({j <~ x} e)) = {j ~> vfvar z} ({j <~ x} ({i ~> vfvar y} e)))
        ); autounfold with class_simpl; simpl; intros; mydestr; auto; 
        rewrite_by_set_solver2.
        all: simpl; mydestr; hauto.
Qed.

#[global] Instance Fact2_value : Fact2 value.
Proof.
  unfold Fact2.
  apply (value_mutual_rec
           (fun (e: value) => forall (x:atom) (y:atom) (z:atom) (i j: nat), x <> y -> i <> j -> y # e -> {i ~> vfvar y} ({j ~> vfvar z} ({j <~ x} e)) = {j ~> vfvar z} ({j <~ x} ({i ~> vfvar y} e)))
           (fun (e: tm) => forall (x:atom) (y:atom) (z:atom) (i j: nat), x <> y -> i <> j -> y # e -> {i ~> vfvar y} ({j ~> vfvar z} ({j <~ x} e)) = {j ~> vfvar z} ({j <~ x} ({i ~> vfvar y} e)))
        ); autounfold with class_simpl; simpl; intros; mydestr; auto; 
        rewrite_by_set_solver2.
        all: simpl; mydestr; hauto.
Qed.
Arguments Fact2_value /.

Class SubstLc A `{Stale A} `{Subst value A} `{Lc A} := subst_lc :
forall (e: A), lc e -> forall (x:atom) (u: value), lc u -> lc ({x := u} e).

#[global] Instance SubstLc_tm : SubstLc tm.
Proof.
  unfold SubstLc.
  apply (lc_tm_mutual_rec
           (fun (e: value) _ => forall (x:atom) (u: value), lc u -> lc ({x := u} e))
           (fun (e: tm) _ => forall (x:atom) (u: value), lc u -> lc ({x := u} e))
        ); ln_simpl; intros; auto;
        try solve [lc_solver1; hauto].
  all: auto_exists_L; intros; repeat split; fold_syntax_class; auto;
    repeat match goal with
      | [ H : forall z, z ∉ ?L -> _ |- lc (_ _ (vfvar ?y) _)] =>
      assert (Hy : y ∉ L) by set_solver;
      specialize (H y Hy)
      | [ H : forall x u, _ -> lc _ , H1 : lc ?u |- context [ subst ?x ?u _ ]] =>
      specialize (H x u H1);
      rewrite subst_open in H; ln_simpl; set_solver
    end.
Qed.
Arguments SubstLc_tm /.

#[global] Instance SubstLc_value : SubstLc value.
Proof.
  unfold SubstLc.
  apply (lc_value_mutual_rec
           (fun (e: value) _ => forall (x:atom) (u: value), lc u -> lc ({x := u} e))
           (fun (e: tm) _ => forall (x:atom) (u: value), lc u -> lc ({x := u} e))
        ); ln_simpl; intros; auto;
        try solve [lc_solver1; hauto].
  all: auto_exists_L; intros; repeat split; fold_syntax_class; auto;
    repeat match goal with
      | [ H : forall z, z ∉ ?L -> _ |- lc (_ _ (vfvar ?y) _)] =>
      assert (Hy : y ∉ L) by set_solver;
      specialize (H y Hy)
      | [ H : forall x u, _ -> lc _ , H1 : lc ?u |- context [ subst ?x ?u _ ]] =>
      specialize (H x u H1);
      rewrite subst_open in H; ln_simpl; set_solver
    end.
Qed.
Arguments SubstLc_value /.

Class OpenCloseVarAux A `{Stale A} `{Open value A} `{Close A} := open_close_var_aux :
forall (e: A) (x: atom) (k: nat),
    {k ~> (vfvar x)} e = e -> {k ~> (vfvar x)} ({k <~ x} e) = e.

#[global] Instance OpenCloseVarAux_tm : OpenCloseVarAux tm.
Proof.
  unfold OpenCloseVarAux.
  apply (tm_mutual_rec
           (fun (e: value) => forall (x:atom) (k: nat), {k ~> (vfvar x)} e = e -> {k ~> (vfvar x)} ({k <~ x} e) = e)
           (fun (e: tm) => forall (x:atom) (k: nat), {k ~> (vfvar x)} e = e -> {k ~> (vfvar x)} ({k <~ x} e) = e));
    ln_simpl; intros; auto; f_equal_hyp;
    try hauto.
  - repeat ln_simpl; hauto.
Qed.
Arguments OpenCloseVarAux_tm /.

#[global] Instance OpenCloseVarAux_value : OpenCloseVarAux value.
Proof.
  unfold OpenCloseVarAux.
  apply (value_mutual_rec
           (fun (e: value) => forall (x:atom) (k: nat), {k ~> (vfvar x)} e = e -> {k ~> (vfvar x)} ({k <~ x} e) = e)
           (fun (e: tm) => forall (x:atom) (k: nat), {k ~> (vfvar x)} e = e -> {k ~> (vfvar x)} ({k <~ x} e) = e));
    ln_simpl; intros; auto; f_equal_hyp;
    try hauto.
  - repeat ln_simpl; hauto.
Qed.
Arguments OpenCloseVarAux_value /.

Class OpenCloseVar A `{Stale A} `{Open value A} `{Close A} `{Lc A} := open_close_var :
forall (e: A) (x: atom), lc e -> {0 ~> (vfvar x)} ({0 <~ x} e) = e.

Lemma OpenCloseVar_all
  (A : Type)
  (staleA : Stale A)
  (openA  : Open value A)
  (closeA : Close A)
  (lcA    : Lc A)
  (openCloseVarAuxA : @OpenCloseVarAux A staleA openA closeA)
  (openRecLcA       : @OpenRecLc       A staleA openA lcA)
  : @OpenCloseVar A staleA openA closeA lcA.
Proof.
  unfold OpenCloseVar. intros e x Hlc.
  apply open_close_var_aux.
  apply open_rec_lc; auto.
Qed.

#[global] Instance OpenCloseVar_tm : OpenCloseVar tm.
Proof. apply OpenCloseVar_all; typeclasses eauto. Qed.
Arguments OpenCloseVar_tm /.

#[global] Instance OpenCloseVar_value : OpenCloseVar value.
Proof. apply OpenCloseVar_all; typeclasses eauto. Qed.
Arguments OpenCloseVar_value /.

(* The third class of lemmas *)

Class SubstIntro A `{Stale A} `{Open value A} `{Subst value A} `{Lc A} := subst_intro :
forall (e: A) (x:atom) (w: value) (k: nat),
    x # e ->
    lc w -> {x := w} ({k ~> (vfvar x)} e) = ({k ~> w} e).

Lemma SubstIntro_all
  (A : Type)
  (staleA : Stale A)
  (openA  : Open value A)
  (substA : Subst value A)
  (lcA    : Lc A)
  (substOpenA  : @SubstOpen  A staleA openA substA lcA)
  (substFreshA : @SubstFresh A staleA substA)
  : @SubstIntro A staleA openA substA lcA.
Proof.
  unfold SubstIntro. intros e x w k Hx Hlc.
  rewrite subst_open; auto.
  ln_simpl; f_equal; hauto.
Qed.

#[global] Instance SubstIntro_tm : SubstIntro tm.
Proof. apply SubstIntro_all; typeclasses eauto. Qed.
Arguments SubstIntro_tm /.

#[global] Instance SubstIntro_value : SubstIntro value.
Proof. apply SubstIntro_all; typeclasses eauto. Qed.
Arguments SubstIntro_value /.

Class SubstOpenVar A `{Stale A} `{Open value A} `{Subst value A} `{Lc A} := subst_open_var :
forall x y (u: value) (e: A) (k: nat),
    x <> y -> lc u -> {x := u} ({k ~> (vfvar y)} e) = ({k ~> (vfvar y)} ({x := u} e)).

Lemma SubstOpenVar_all
(A : Type)
(staleA : Stale A)
(openA  : Open value A)
(substA : Subst value A)
(lcA    : Lc A)
(subst_openA : @SubstOpen A staleA openA substA lcA)
: @SubstOpenVar A staleA openA substA lcA.
Proof.
  unfold SubstOpenVar. intros x y u e k Hxy Hlc.
  rewrite subst_open; auto. ln_simpl; f_equal; hauto.
Qed.

#[global] Instance SubstOpenVar_tm: SubstOpenVar tm.
Proof.
  apply SubstOpenVar_all. all: typeclasses eauto.
Qed.
Arguments SubstOpenVar_tm /.
#[global] Instance SubstOpenVar_value: SubstOpenVar value.
Proof. apply SubstOpenVar_all. all: typeclasses eauto. Qed.
Arguments SubstOpenVar_value /.

Class SubstBody A `{Stale A} `{open: Open value A} `{Subst value A} `{lc : Lc A}:= subst_body :
forall x (u: value) (e: A), body e -> lc_value u -> body ({x := u} e).

Lemma SubstBody_all
  (A : Type)
  (staleA : Stale A)
  (openA  : Open value A)
  (substA : Subst value A)
  (lcA    : Lc A)
  (substOpenVarA : @SubstOpenVar A staleA openA substA lcA)
  (substLcA      : @SubstLc      A staleA substA lcA)
  : @SubstBody A staleA openA substA lcA.
Proof.
  unfold SubstBody. intros x u e Hbody Hlc.
  destruct Hbody as [L Hbody].
  auto_exists_L; intros y Hy; repeat split; auto.
  rewrite <- subst_open_var by set_solver.
  apply subst_lc; auto. apply Hbody; my_set_solver.
Qed.

#[global] Instance SubstBody_tm : SubstBody tm.
Proof. apply SubstBody_all; typeclasses eauto. Qed.
Arguments SubstBody_tm /.

#[global] Instance SubstBody_value : SubstBody value.
Proof. apply SubstBody_all; typeclasses eauto. Qed.
Arguments SubstBody_value /.

Class OpenLc A `{Stale A} `{Open value A} `{Lc A} := open_lc :
forall (e: A) (u: value), body e -> lc u -> lc ({0 ~> u} e).

Lemma OpenLc_all
  (A : Type)
  (staleA : Stale A)
  (openA  : Open value A)
  (substA : Subst value A)
  (lcA    : Lc A)
  (substIntroA : @SubstIntro A staleA openA substA lcA)
  (substLcA    : @SubstLc    A staleA substA lcA)
  : @OpenLc A staleA openA lcA.
Proof.
  intros e u Hbody Hlc. destruct Hbody as [L Hbody].
  pose_fresh_fv y.
  erewrite <- subst_intro; auto. instantiate (1:= y).
  apply subst_lc; auto. apply Hbody; my_set_solver.
  my_set_solver.
Qed.

#[global] Instance OpenLc_tm : OpenLc tm.
Proof.
  apply OpenLc_all with (staleA := stale) (openA := open) (substA := subst) (lcA := lc); typeclasses eauto. Qed.
Arguments OpenLc_tm /.

#[global] Instance OpenLc_value : OpenLc value.
Proof. apply OpenLc_all with (staleA := stale) (openA := open) (substA := subst) (lcA := lc); typeclasses eauto. Qed.
Arguments OpenLc_value /.

Class OpenWithFreshIncludeFv A `{Stale A} `{Open value A} `{Lc A} := open_with_fresh_include_fv :
forall (x: atom) (e: A) (k: nat),
    x # e -> ({[x]} ∪ stale e) ⊆ ({[x]} ∪ stale ({k ~> (vfvar x)} e)).

#[global] Instance OpenWithFreshIncludeFv_tm : OpenWithFreshIncludeFv tm.
Proof.
  unfold OpenWithFreshIncludeFv.
  intros x.
  apply (tm_mutual_rec
           (fun (e: value) => forall k, x # e -> ({[x]} ∪ stale e) ⊆ ({[x]} ∪ stale ({k ~> (vfvar x)} e)))
           (fun (e: tm) => forall k, x # e -> ({[x]} ∪ stale e) ⊆ ({[x]} ∪ stale ({k ~> (vfvar x)} e)))
        ); simpl; intros; auto; ln_simpl.
    all:
    repeat match goal with
           | [H: context [{_ ~> _} ?e] |- context [{?k ~> _} ?e]] => specialize (H k)
           | [H: context [{_ ~> _} ?e] |- context [{?k ~> _} ?e]] => specialize (H k)
           | [H: ?P -> _ ⊆ _ |- _] => assert P as Htmp by fast_set_solver; specialize (H Htmp); try clear Htmp
           end; repeat my_set_solver.
Qed.
Arguments OpenWithFreshIncludeFv_tm /.

#[global] Instance OpenWithFreshIncludeFv_value : OpenWithFreshIncludeFv value.
Proof.
  unfold OpenWithFreshIncludeFv.
  intros x.
  apply (value_mutual_rec
           (fun (e: value) => forall k, x # e -> ({[x]} ∪ stale e) ⊆ ({[x]} ∪ stale ({k ~> (vfvar x)} e)))
           (fun (e: tm) => forall k, x # e -> ({[x]} ∪ stale e) ⊆ ({[x]} ∪ stale ({k ~> (vfvar x)} e)))
        ); simpl; intros; auto; ln_simpl.
    all:
    repeat match goal with
           | [H: context [{_ ~> _} ?e] |- context [{?k ~> _} ?e]] => specialize (H k)
           | [H: context [{_ ~> _} ?e] |- context [{?k ~> _} ?e]] => specialize (H k)
           | [H: ?P -> _ ⊆ _ |- _] => assert P as Htmp by fast_set_solver; specialize (H Htmp); try clear Htmp
           end; repeat my_set_solver.
Qed.
Arguments OpenWithFreshIncludeFv_value /.

(* Lemma for MNF *)

Class LcImpliesBody A `{Open value A} `{Lc A} := lc_implies_body :
forall (e: A), lc e -> body e.

Lemma LcImpliesBody_all
  (A : Type)
  (staleA : Stale A)
  (openA  : Open value A)
  (lcA    : Lc A)
  (openRecLcA : @OpenRecLc A staleA openA lcA)
  : @LcImpliesBody A openA lcA.
Proof.
  unfold LcImpliesBody.
  intros. exists ∅; intros; rewrite open_rec_lc; auto.
Qed.
Arguments LcImpliesBody_all /.

#[global] Instance LcImpliesBody_tm : LcImpliesBody tm.
Proof. apply LcImpliesBody_all with (staleA := stale) (openA := open) (lcA := lc); typeclasses eauto. Qed.
Arguments LcImpliesBody_tm /.

#[global] Instance LcImpliesBody_value : LcImpliesBody value.
Proof. apply LcImpliesBody_all with (staleA := stale) (openA := open) (lcA := lc); typeclasses eauto. Qed.
Arguments LcImpliesBody_value /.

(* Ltac lc_solver :=
  repeat match goal with
    | [ |- lc (treturn (vfvar _))] => constructor
    | [ |- lc (tmatchb _ _ _)] => apply lc_tmatchb; (repeat split; auto)
    | [ |- lc (tletapp _ _ _)] => rewrite letapp_lc_body; (repeat split; auto)
    | [ |- lc (tleteffop _ _ _)] => rewrite leteffop_lc_body; (repeat split; auto)
    | [ |- lc (tlete _ _)] => rewrite lete_lc_body; split; auto
    | [ |- lc (treturn (vfix _ _))] => rewrite lc_fix_iff_body; auto
    | [ |- lc (treturn (vlam _ _))] => rewrite lc_abs_iff_body; auto
    | [H: lc (tlete _ ?e) |- body ?e ] => rewrite lete_lc_body in H; mydestr; auto
    | [H: lc (tletapp _ _ ?e) |- body ?e ] => rewrite letapp_lc_body in H; mydestr; auto
    | [H: lc (treturn (vlam _ ?e)) |- body ?e ] => rewrite lc_abs_iff_body in H; mydestr; auto
    | [H: lc (treturn (vfix _ ?e)) |- body ?e ] => rewrite lc_fix_iff_body in H; mydestr; auto
    | [H: lc (tletapp ?e _ _) |- lc (treturn ?e) ] => rewrite letapp_lc_body in H; mydestr; auto
    | [H: lc (tletapp _ ?e _) |- lc (treturn ?e) ] => rewrite letapp_lc_body in H; mydestr; auto
    | [H: lc ?e |- body ?e] => apply lc_implies_body_tm; auto
    | [H: lc ?e |- lc (?e ^t^ _)] => rewrite open_rec_lc_tm; auto
    | [|- body _ ] => eexists; auto_exists_L_intros
    end. *)

Class SubstAsCloseOpenAux A `{Stale A} `{Open value A} `{Close A} `{Subst value A} := subst_as_close_open_aux :
forall (x: atom) (u: value) (e: A) (k: nat),
    {k ~> u} e = e ->
    {k ~> u} ({k <~ x} e) = {x := u} e.

#[global] Instance SubstAsCloseOpenAux_tm : SubstAsCloseOpenAux tm.
Proof.
  unfold SubstAsCloseOpenAux.
  intros x u.
  apply (tm_mutual_rec
           (fun (e: value) => forall k, {k ~> u} e = e -> {k ~> u} ({k <~ x} e) = {x := u} e)
           (fun (e: tm) => forall k, {k ~> u} e = e -> {k ~> u} ({k <~ x} e) = {x := u} e)
        ); ln_simpl; intros; rewrite_by_set_solver2; eauto. 
  - repeat ln_simpl; hauto.
Qed.
Arguments SubstAsCloseOpenAux_tm /.

#[global] Instance SubstAsCloseOpenAux_value : SubstAsCloseOpenAux value.
Proof.
  unfold SubstAsCloseOpenAux.
  intros x u.
  apply (value_mutual_rec
           (fun (e: value) => forall k, {k ~> u} e = e -> {k ~> u} ({k <~ x} e) = {x := u} e)
           (fun (e: tm) => forall k, {k ~> u} e = e -> {k ~> u} ({k <~ x} e) = {x := u} e)
        ); ln_simpl; intros; rewrite_by_set_solver2; eauto. 
  - repeat ln_simpl; hauto.
Qed.
Arguments SubstAsCloseOpenAux_value /.

Class SubstAsCloseOpen A `{Stale A} `{Open value A} `{Close A} `{Subst value A} `{Lc A} := subst_as_close_open :
forall (x: atom) (u: value) (e: A),
    lc e -> {0 ~> u} ({0 <~ x} e) = {x := u} e.

Lemma SubstAsCloseOpen_all
  (A : Type)
  (staleA : Stale A)
  (openA  : Open value A)
  (closeA : Close A)
  (substA : Subst value A)
  (lcA    : Lc A)
  (substAsCloseOpenAuxA : @SubstAsCloseOpenAux A staleA openA closeA substA)
  (openRecLcA           : @OpenRecLc           A staleA openA lcA)
  : @SubstAsCloseOpen A staleA openA closeA substA lcA.
Proof.
  unfold SubstAsCloseOpen.
  intros x u e Hlc. eapply subst_as_close_open_aux; auto.
Qed.
Arguments SubstAsCloseOpen_all /.

#[global] Instance SubstAsCloseOpen_tm : SubstAsCloseOpen tm.
Proof. apply SubstAsCloseOpen_all; typeclasses eauto. Qed.
Arguments SubstAsCloseOpen_tm /.

#[global] Instance SubstAsCloseOpen_value : SubstAsCloseOpen value.
Proof. apply SubstAsCloseOpen_all; typeclasses eauto. Qed.
Arguments SubstAsCloseOpen_value /.

Class CloseFreshRec A `{Stale A} `{Close A} := close_fresh_rec :
forall (x: atom) (e: A) (k: nat), x # e -> { k <~ x} e = e.

#[global] Instance CloseFreshRec_tm : CloseFreshRec tm.
Proof.
  unfold CloseFreshRec.
  intros x.
  apply (tm_mutual_rec
           (fun (v: value) => forall (k: nat), x # v -> { k <~ x} v = v)
           (fun (e: tm) => forall (k: nat), x # e -> { k <~ x} e = e)
        ); simpl; intros; auto; ln_simpl; rewrite_by_set_solver2; auto.
  - my_set_solver.
Qed.
Arguments CloseFreshRec_tm /.

#[global] Instance CloseFreshRec_value : CloseFreshRec value.
Proof.
  unfold CloseFreshRec.
  intros x.
  apply (value_mutual_rec
           (fun (v: value) => forall (k: nat), x # v -> { k <~ x} v = v)
           (fun (e: tm) => forall (k: nat), x # e -> { k <~ x} e = e)
        ); simpl; intros; auto; ln_simpl; rewrite_by_set_solver2; auto.
  - my_set_solver.
Qed.
Arguments CloseFreshRec_value /.

Class SubstClose A `{Stale A} `{Open value A} `{Close A} `{Subst value A} := subst_close :
∀ (x y: atom) (u: value), x # u -> x <> y ->
                        forall (e: A) k, {k <~ x} ({y := u } e) = {y := u } ({k <~ x} e).

#[global] Instance SubstClose_tm: SubstClose tm.
Proof.
  unfold SubstClose.
  intros x y u Hux Hxy. apply (tm_mutual_rec
           (fun (e: value) => forall (k: nat), {k <~ x} ({y := u } e) = {y := u } ({k <~ x} e))
           (fun (e: tm) => forall (k: nat), {k <~ x} ({y := u } e) = {y := u } ({k <~ x} e))
        ); simpl; intros; auto; ln_simpl; rewrite_by_set_solver2; auto;
  try (ln_simpl; hauto).
  - ln_simpl; try rewrite close_fresh_rec; hauto.
Qed.
Arguments SubstClose_tm /.

#[global] Instance SubstClose_value: SubstClose value.
Proof.
  unfold SubstClose.
  intros x y u Hux Hxy. apply (value_mutual_rec
           (fun (e: value) => forall (k: nat), {k <~ x} ({y := u } e) = {y := u } ({k <~ x} e))
           (fun (e: tm) => forall (k: nat), {k <~ x} ({y := u } e) = {y := u } ({k <~ x} e))
        ); simpl; intros; auto; ln_simpl; rewrite_by_set_solver2; auto;
  try (ln_simpl; hauto).
  - ln_simpl; try rewrite close_fresh_rec; hauto.
Qed.
Arguments SubstClose_value /.

Class SubstCommute A `{Stale A} `{Subst value A} := subst_commute :
forall (x y: atom) (u_x u_y: value) (e: A),
    x <> y -> x # u_y -> y # u_x ->
    {x := u_x } ({y := u_y } e) = {y := u_y } ({x := u_x } e).

#[global] Instance SubstCommute_tm: SubstCommute tm.
Proof.
  unfold SubstCommute.
  intros x y u_x u_y e Hxy Hxuy Hyux. 
  apply (tm_mutual_rec
           (fun (e: value) => {x := u_x } ({y := u_y } e) = {y := u_y } ({x := u_x } e))
           (fun (e: tm) => {x := u_x } ({y := u_y } e) = {y := u_y } ({x := u_x } e))
        ); simpl; intros; auto; ln_simpl; auto;
  try solve [f_equal; auto];
  try solve [ln_simpl; try hauto; rewrite subst_fresh; auto].
Qed.
Arguments SubstCommute_tm /.

#[global] Instance SubstCommute_value: SubstCommute value.
Proof.
  unfold SubstCommute.
  intros x y u_x u_y e Hxy Hxuy Hyux. 
  apply (value_mutual_rec
           (fun (e: value) => {x := u_x } ({y := u_y } e) = {y := u_y } ({x := u_x } e))
           (fun (e: tm) => {x := u_x } ({y := u_y } e) = {y := u_y } ({x := u_x } e))
        ); simpl; intros; auto; ln_simpl; auto;
  try solve [f_equal; auto];
  try solve [ln_simpl; try hauto; rewrite subst_fresh; auto].
Qed.
Arguments SubstCommute_value /.

Class SubstShadow A `{Stale A} `{Open value A} `{Close A} `{Subst value A} := subst_shadow :
forall (x z: atom) (u: value) (e: A),
    x # e -> {x := u } ({z := (vfvar x) } e) = {z := u } e.

#[global] Instance SubstShadow_tm: SubstShadow tm.
Proof.
  unfold SubstShadow.
  intros x z u e Hx. apply (tm_mutual_rec
           (fun (e: value) => x # e -> {x := u } ({z := (vfvar x) } e) = {z := u } e)
           (fun (e: tm) => x # e -> {x := u } ({z := (vfvar x) } e) = {z := u } e)
        ); intros; auto; ln_simpl; rewrite_by_set_solver2; eauto;
  try solve [f_equal; ln_simpl; my_set_solver].
Qed.
Arguments SubstShadow_tm /.

#[global] Instance SubstShadow_value: SubstShadow value.
Proof.
  unfold SubstShadow.
  intros x z u e Hx. apply (value_mutual_rec
           (fun (e: value) => x # e -> {x := u } ({z := (vfvar x) } e) = {z := u } e)
           (fun (e: tm) => x # e -> {x := u } ({z := (vfvar x) } e) = {z := u } e)
        ); intros; auto; ln_simpl; rewrite_by_set_solver2; eauto;
  try solve [f_equal; ln_simpl; my_set_solver].
Qed.
Arguments SubstShadow_value /.

Class SubstSubst A `{Stale A} `{Open value A} `{Close A} `{Subst value A} := subst_subst :
forall (x : atom) (u_x : value) (y : atom) (u_y: value) (e: A),
    x ≠ y → y # u_x →
    {x := u_x } ({y := u_y } e) = {y := {x := u_x } u_y } ({x := u_x } e).

#[global] Instance SubstSubst_tm: SubstSubst tm.
Proof.
  unfold SubstSubst.
  intros x u_x y u_y e Hxy Hyux. apply (tm_mutual_rec
           (fun (e: value) => {x := u_x } ({y := u_y } e) = {y := {x := u_x } u_y } ({x := u_x } e))
           (fun (e: tm) => {x := u_x } ({y := u_y } e) = {y := {x := u_x } u_y } ({x := u_x } e))
        ); intros; ln_simpl; auto; rewrite_by_set_solver2; auto; fold_syntax_class;
  try solve [ln_simpl; hauto].
  - ln_simpl; try hauto. rewrite subst_fresh; auto.
Qed.
Arguments SubstSubst_tm /.

#[global] Instance SubstSubst_value: SubstSubst value.
Proof.
  unfold SubstSubst.
  intros x u_x y u_y e Hxy Hyux. apply (value_mutual_rec
           (fun (e: value) => {x := u_x } ({y := u_y } e) = {y := {x := u_x } u_y } ({x := u_x } e))
           (fun (e: tm) => {x := u_x } ({y := u_y } e) = {y := {x := u_x } u_y } ({x := u_x } e))
        ); intros; ln_simpl; auto; rewrite_by_set_solver2; auto; fold_syntax_class;
  try solve [ln_simpl; hauto].
  - ln_simpl; try hauto. rewrite subst_fresh; auto.
Qed.
Arguments SubstSubst_value /.

Class FvOfSubst A `{Stale A} `{Subst value A} := fv_of_subst :
forall x (u: value) (e: A), stale ({x := u } e) ⊆ (stale e ∖ {[x]}) ∪ stale u.

#[global] Instance FvOfSubst_tm: FvOfSubst tm.
Proof.
  unfold FvOfSubst.
  intros x u e. apply (tm_mutual_rec
           (fun (e: value) => stale ({x := u } e) ⊆ stale e ∖ {[x]} ∪ stale u)
           (fun (e: tm) => stale ({x := u } e) ⊆ stale e ∖ {[x]} ∪ stale u)
        ); intros; ln_simpl; auto; rewrite_by_set_solver2; auto; fold_syntax_class;
  try solve [ln_simpl; set_solver].
Qed.
Arguments FvOfSubst_tm /.

#[global] Instance FvOfSubst_value: FvOfSubst value.
Proof.
  unfold FvOfSubst.
  intros x u e. apply (value_mutual_rec
           (fun (e: value) => stale ({x := u } e) ⊆ stale e ∖ {[x]} ∪ stale u)
           (fun (e: tm) => stale ({x := u } e) ⊆ stale e ∖ {[x]} ∪ stale u)
        ); intros; ln_simpl; auto; rewrite_by_set_solver2; auto; fold_syntax_class;
  try solve [ln_simpl; set_solver].
Qed.
Arguments FvOfSubst_value /.

Class FvOfSubstClosed A `{Stale A} `{Subst value A} := fv_of_subst_closed :
forall x (u: value) (e: A),
    stale u = ∅ ->
    stale ({x := u } e) = (stale e ∖ {[x]}).

#[global] Instance FvOfSubstClosed_tm: FvOfSubstClosed tm.
Proof.
  unfold FvOfSubstClosed.
  intros x u.
  apply (tm_mutual_rec
           (fun (e: value) =>
              fv_value u = ∅ -> fv_value ({x := u } e) = fv_value e ∖ {[x]})
           (fun (e: tm) =>
              fv_value u = ∅ -> fv_tm ({x := u } e) = fv_tm e ∖ {[x]})
        ); simpl; intros; auto; repeat ln_simpl; my_set_solver.
Qed.
Arguments FvOfSubstClosed_tm /.

#[global] Instance FvOfSubstClosed_value: FvOfSubstClosed value.
Proof.
  unfold FvOfSubstClosed.
  intros x u.
  apply (value_mutual_rec
           (fun (e: value) =>
              fv_value u = ∅ -> fv_value ({x := u } e) = fv_value e ∖ {[x]})
           (fun (e: tm) =>
              fv_value u = ∅ -> fv_tm ({x := u } e) = fv_tm e ∖ {[x]})
        ); simpl; intros; auto; repeat ln_simpl; my_set_solver.
Qed.
Arguments FvOfSubstClosed_value /.

Lemma lc_tletapp: forall (v x: value), lc v -> lc x -> lc (tletapp v x (treturn (vbvar 0))).
Proof.
  intros. auto_exists_L; ln_simpl; intros; lc_solver1.
Qed.

Global Hint Resolve lc_tletapp: core.

Lemma body_tletapp_0: forall (v: value), lc v -> body (tletapp v (vbvar 0) (treturn (vbvar 0))).
Proof.
  intros. auto_exists_L; intros. ln_simpl.
  rewrite open_rec_lc; eauto.
  apply lc_tletapp; hauto.
Qed.

Global Hint Resolve body_tletapp_0: core.

Class OpenSubstSame A `{Stale A} `{Open value A} `{Subst value A} := open_subst_same :
forall (x: atom) (y: value) (e: A) (k: nat), x # e -> {x := y } ({k ~> (vfvar x)} e) = {k ~> y} e.

#[global] Instance OpenSubstSame_tm: OpenSubstSame tm.
Proof.
  unfold OpenSubstSame.
  intros x y. apply (tm_mutual_rec
  (fun (e: value) => forall k,
     x # e -> {x := y } ({k ~> (vfvar x)} e) = {k ~> y} e)
  (fun (e: tm) => forall k,
     x # e -> {x := y } ({k ~> (vfvar x)} e) = {k ~> y} e)
); intros; ln_simpl; auto; rewrite_by_set_solver2; auto; fold_syntax_class;
  try solve [ln_simpl; hauto].
  - set_solver.
Qed.
Arguments OpenSubstSame_tm /.

#[global] Instance OpenSubstSame_value: OpenSubstSame value.
Proof.
  unfold OpenSubstSame.
  intros x y. apply (value_mutual_rec
                   (fun (e: value) => forall k,
                      x # e -> {x := y } ({k ~> (vfvar x)} e) = {k ~> y} e)
                   (fun (e: tm) => forall k,
                      x # e -> {x := y } ({k ~> (vfvar x)} e) = {k ~> y} e)
                ); intros; ln_simpl; auto; rewrite_by_set_solver2; auto; fold_syntax_class;
  try solve [ln_simpl; hauto].
  - set_solver.
Qed.
Arguments OpenSubstSame_value /.

Lemma body_vlam_eq: forall e T1 T2,
    body (vlam T1 e) <-> body (vlam T2 e).
Proof.
  apply (tm_mutual_rec
                   (fun (e: value) => forall T1 T2, body (vlam T1 (treturn e)) <-> body (vlam T2 (treturn e)))
                   (fun (e: tm) => forall T1 T2, body (vlam T1 e) <-> body (vlam T2 e))
                ); split; ln_simpl; intros; auto;
    repeat match goal with
    | [H: body ( (vlam _ _)) |- _ ] => invclear H
    | [|- body ( (vlam _ _))] => auto_exists_L; intros a; intros; specialize_with a
    | [H: context [( (vlam _ _)) ^^ _] |- _ ] => ln_simpl
    | [|- context [( (vlam _ _)) ^^ _] ] => ln_simpl
    | [H: lc ( (vlam _ _)) |- _ ] => rewrite lc_abs_iff_body in H; auto
    | [|- lc ( (vlam _ _))] => rewrite lc_abs_iff_body; auto
    end.
Qed.

Class CloseRmFv A `{Stale A} `{Close A} := close_rm_fv :
forall (x: atom) (e: A) (k: nat), x # ({k <~ x} e).

#[global] Instance CloseRmFv_tm: CloseRmFv tm.
Proof.
  unfold CloseRmFv.
  intros x. apply (tm_mutual_rec
                   (fun (e: value) => forall k, x # ({k <~ x} e))
                   (fun (e: tm) => forall k, x # ({k <~ x} e))
                ); intros; ln_simpl; auto; rewrite_by_set_solver2; auto; fold_syntax_class;
  try solve [ln_simpl; my_set_solver].
Qed.
Arguments CloseRmFv_tm /.

#[global] Instance CloseRmFv_value: CloseRmFv value.
Proof.
  unfold CloseRmFv.
  intros x.
  apply (value_mutual_rec
                   (fun (e: value) => forall (k: nat), x # ({k <~ x} e))
                   (fun (e: tm) => forall (k: nat), x # ({k <~ x} e))
                ); intros; ln_simpl; auto; rewrite_by_set_solver2; auto; fold_syntax_class;
  try solve [ln_simpl; my_set_solver].
Qed.
Arguments CloseRmFv_value /.

Class CloseThenSubstSame A `{Stale A} `{Close A} `{Subst value A} := close_then_subst_same :
forall (x: atom) (v_x: value) (e: A), ({x := v_x } (x \\ e)) = (x \\ e).

Lemma CloseThenSubstSame_all
  (A : Type)
  (staleA : Stale A)
  (closeA : Close A)
  (substA : Subst value A)
  (substFreshA : @SubstFresh   A staleA substA)
  (closeRmFvA  : @CloseRmFv    A staleA closeA)
  : @CloseThenSubstSame A staleA closeA substA.
Proof.
  unfold CloseThenSubstSame. hauto.
Qed.
Arguments CloseThenSubstSame_all /.

#[global] Instance CloseThenSubstSame_tm : CloseThenSubstSame tm.
Proof. apply CloseThenSubstSame_all; typeclasses eauto. Qed.
Arguments CloseThenSubstSame_tm /.

#[global] Instance CloseThenSubstSame_value : CloseThenSubstSame value.
Proof. apply CloseThenSubstSame_all; typeclasses eauto. Qed.
Arguments CloseThenSubstSame_value /.

Class SubstOpenClosed A `{Stale A} `{Open value A} `{Subst value A} `{Lc A} := subst_open_closed :
forall (e :A) (x : atom) (u w : value) (k : nat),
    stale u = ∅ ->
    lc w → {x := w } ({k ~> u} e) = {k ~> u} ({x := w } e).

Lemma SubstOpenClosed_all
  (A : Type)
  (staleA : Stale A)
  (openA  : Open value A)
  (substA : Subst value A)
  (lcA    : Lc A)
  (substOpenA : @SubstOpen A staleA openA substA lcA)
  : @SubstOpenClosed A staleA openA substA lcA.
Proof.
  unfold SubstOpenClosed. intros. 
  rewrite subst_open; auto.
  rewrite SubstFresh_value; eauto. set_solver.
Qed.
Arguments SubstOpenClosed_all /.

#[global] Instance SubstOpenClosed_tm : SubstOpenClosed tm.
Proof. apply SubstOpenClosed_all; typeclasses eauto. Qed.
Arguments SubstOpenClosed_tm /.

#[global] Instance SubstOpenClosed_value : SubstOpenClosed value.
Proof. apply SubstOpenClosed_all; typeclasses eauto. Qed.
Arguments SubstOpenClosed_value /.

Class BodyLcAfterClose A `{Stale A} `{Open value A} `{Close A} `{Lc A} := body_lc_after_close :
forall (x: atom) (e: A), lc e -> body ({0 <~ x} e).

Lemma BodyLcAfterClose_all
  (A : Type)
  (staleA : Stale A)
  (openA  : Open value A)
  (closeA : Close A)
  (substA : Subst value A)
  (lcA    : Lc A)
  (substAsCloseOpenA : @SubstAsCloseOpen A staleA openA closeA substA lcA)
  (substLcA          : @SubstLc         A staleA substA lcA)
  : @BodyLcAfterClose A staleA openA closeA lcA.
Proof.
  unfold BodyLcAfterClose. 
  intros. unfold body. auto_exists_L. intros.
  rewrite subst_as_close_open; auto.
  apply subst_lc; hauto.
Qed.
Arguments BodyLcAfterClose_all /.

#[global] Instance BodyLcAfterClose_tm : BodyLcAfterClose tm.
Proof. apply BodyLcAfterClose_all with (staleA := stale) (openA := open) (closeA := close) (substA := subst) (lcA := lc); typeclasses eauto. Qed.
Arguments BodyLcAfterClose_tm /.

#[global] Instance BodyLcAfterClose_value : BodyLcAfterClose value.
Proof. apply BodyLcAfterClose_all with (staleA := stale) (openA := open) (closeA := close) (substA := subst) (lcA := lc); typeclasses eauto. Qed.
Arguments BodyLcAfterClose_value /.

Class LcFreshVarImpliesBody A `{Stale A} `{Open value A} `{Close A} `{Lc A} := lc_fresh_var_implies_body :
forall (e: A) (x: atom), x # e -> lc (e ^^ (vfvar x)) -> body e.

Lemma LcFreshVarImpliesBody_all
  (A : Type)
  (staleA : Stale A)
  (openA  : Open value A)
  (closeA : Close A)
  (lcA    : Lc A)
  (bodyLcAfterCloseA : @BodyLcAfterClose A staleA openA closeA lcA)
  (closeOpenVarA     : @CloseOpenVar     A staleA openA closeA)
  : @LcFreshVarImpliesBody A staleA openA closeA lcA.
Proof.
  unfold LcFreshVarImpliesBody. intros x e Hx Hlc.
  eapply (body_lc_after_close) in Hlc; eauto. rewrite close_open_var in Hlc; auto.
Qed.
Arguments LcFreshVarImpliesBody_all /.

#[global] Instance LcFreshVarImpliesBody_tm : LcFreshVarImpliesBody tm.
Proof. apply LcFreshVarImpliesBody_all; typeclasses eauto. Qed.
Arguments LcFreshVarImpliesBody_tm /.

#[global] Instance LcFreshVarImpliesBody_value : LcFreshVarImpliesBody value.
Proof. apply LcFreshVarImpliesBody_all; typeclasses eauto. Qed.
Arguments LcFreshVarImpliesBody_value /.

Class OpenNotInEq A `{Stale A} `{Open value A} := open_not_in_eq :
forall (x: atom) (e: A) (k: nat), x # ({k ~> (vfvar x)} e) -> {k ~> (vfvar x)} e = e.

#[global] Instance OpenNotInEq_tm: OpenNotInEq tm.
Proof.
  unfold OpenNotInEq. intros x.
  apply (tm_mutual_rec
                   (fun (e: value) => forall k, x # ({k ~> (vfvar x)} e) -> {k ~> (vfvar x)} e = e)
                   (fun (e: tm) => forall k, x # ({k ~> (vfvar x)} e) -> {k ~> (vfvar x)} e = e)
                ); intros; ln_simpl; auto; rewrite_by_set_solver2; auto; fold_syntax_class;
  try solve [ln_simpl; my_set_solver].
Qed.
Arguments OpenNotInEq_tm /.

#[global] Instance OpenNotInEq_value: OpenNotInEq value.
Proof.
  unfold OpenNotInEq. intros x.
  apply (value_mutual_rec
                   (fun (e: value) => forall k, x # ({k ~> (vfvar x)} e) -> {k ~> (vfvar x)} e = e)
                   (fun (e: tm) => forall k, x # ({k ~> (vfvar x)} e) -> {k ~> (vfvar x)} e = e)
                ); intros; ln_simpl; auto; rewrite_by_set_solver2; auto; fold_syntax_class;
  try solve [ln_simpl; my_set_solver].
Qed.
Arguments OpenNotInEq_value /.

Class LcSubst A `{Stale A} `{Subst value A} `{Lc A} := lc_subst :
forall (x: atom) (u: value) (e: A), lc ({x := u} e) -> lc_value u -> lc e.

#[global] Instance LcSubst_tm : LcSubst tm.
Proof.
  pose SubstOpenVar_all.
  pose SubstOpen_tm. 
  pose SubstOpen_value.
  unfold LcSubst. intros x u e Hlc Hu.
  remember ({x := u} e) as e'.
  generalize dependent e.
  generalize dependent e'.
  apply (lc_tm_mutual_rec
           (fun (e': value) _ => ∀ e : value, e' = {x := u} (e) → lc e)
           (fun (e': tm) _ => ∀ e : tm, e' = {x := u} (e) → lc e)
        ); intros; fold_syntax_class;
      match goal with
      | H : _ = {_:=_} ?e |- _ => destruct e; ln_simpl; simplify_eq
      end;
  try solve [ lc_solver1; hauto].
all:
econstructor; eauto; lc_solver1; eauto;
let x := fresh "x" in
let acc := collect_stales tt in instantiate (1 := acc); intros x **; simpl;
repeat specialize_with x;
rewrite <- @subst_open_var with (H := stale) (H2:= lc) in *; eauto; my_set_solver.
Qed.
Arguments LcSubst_tm /.

#[global] Instance LcSubst_value : LcSubst value.
Proof.
  pose SubstOpenVar_all.
  pose SubstOpen_tm. 
  pose SubstOpen_value.
  unfold LcSubst. intros x u e Hlc Hu.
  remember ({x := u} e) as e'.
  generalize dependent e.
  generalize dependent e'.
  apply (lc_value_mutual_rec
           (fun (e': value) _ => ∀ e : value, e' = {x := u} (e) → lc e)
           (fun (e': tm) _ => ∀ e : tm, e' = {x := u} (e) → lc e)
        ); intros;
      match goal with
      | H : _ = {_:=_} ?e |- _ => destruct e; ln_simpl; simplify_eq
      end;
  try solve [ lc_solver1; hauto].
all: econstructor; lc_solver1; eauto;
let x := fresh "x" in
let acc := collect_stales tt in instantiate (1 := acc); intros x **; simpl;
repeat specialize_with x;
rewrite <- @subst_open_var with (H := stale) (H2:= lc) in *; eauto; my_set_solver.
Qed.
Arguments LcSubst_value /.

Class OpenSwap A `{Stale A} `{Open value A} := open_swap :
forall (t: A) i j (u v: value),
    lc u ->
    lc v ->
    i <> j ->
    {i ~> v} ({j ~> u} t) = {j ~> u} ({i ~> v} t).

#[global] Instance OpenSwap_tm: OpenSwap tm.
Proof.
  unfold OpenSwap.
  apply (tm_mutual_rec
                   (fun (t: value) => forall i j (u v: value),
                      lc u ->
                      lc v ->
                      i <> j ->
                      {i ~> v} ({j ~> u} t) = {j ~> u} ({i ~> v} t))
                   (fun (t: tm) => forall i j (u v: value),
                      lc u ->
                      lc v ->
                      i <> j ->
                      {i ~> v} ({j ~> u} t) = {j ~> u} ({i ~> v} t))
                ); intros; ln_simpl; auto; fold_syntax_class;
  try solve [ln_simpl; f_equal; hauto].
  all: ln_simpl; try hauto; rewrite open_rec_lc; hauto.
Qed.
Arguments OpenSwap_tm /.

#[global] Instance OpenSwap_value: OpenSwap value.
Proof.
  unfold OpenSwap.
  apply (value_mutual_rec
                   (fun (t: value) => forall i j (u v: value),
                      lc u ->
                      lc v ->
                      i <> j ->
                      {i ~> v} ({j ~> u} t) = {j ~> u} ({i ~> v} t))
                   (fun (t: tm) => forall i j (u v: value),
                      lc u ->
                      lc v ->
                      i <> j ->
                      {i ~> v} ({j ~> u} t) = {j ~> u} ({i ~> v} t))
                ); intros; ln_simpl; auto; fold_syntax_class;
  try solve [ln_simpl; f_equal; hauto].
  all: ln_simpl; try hauto; rewrite open_rec_lc; hauto.
Qed.
Arguments OpenSwap_value /.

Class OpenLcRespect A `{Stale A} `{Open value A} `{Lc A} := open_lc_respect :
forall (t: A) (u v : value) (k: nat),
    lc ({k ~> u} t) ->
    lc u ->
    lc v ->
    lc ({k ~> v} t).

#[global] Instance OpenLcRespect_tm: OpenLcRespect tm.
Proof.
  unfold OpenLcRespect.
  intros * H. remember ({k ~> u} t) as t'.
  generalize dependent t. revert k.
  apply (lc_tm_mutual_rec
           (fun (t': value) _ => ∀ (k : nat) (t : value), t' = {k ~> u} t → lc u → lc v → lc {k ~> v} (t))
           (fun (t': tm) _ => ∀ (k : nat) (t : tm), t' = {k ~> u} t → lc u → lc v → lc {k ~> v} t)
        ); intros;
      repeat match goal with
      | H : _ = {_ ~> _} ?t |- _ => destruct t; ln_simpl; simplify_eq
      end;
  try solve [ lc_solver1; hauto].
all: econstructor; lc_solver1; eauto;
let x := fresh "x" in
let acc := collect_stales tt in instantiate (1 := acc); intros x **; simpl;
repeat specialize_with x; fold_syntax_class;
rewrite open_swap in *; eauto; lc_solver1.
Qed.
Arguments OpenLcRespect_tm /.

#[global] Instance OpenLcRespect_value: OpenLcRespect value.
Proof.
  unfold OpenLcRespect.
  intros * H. remember ({k ~> u} t) as t'.
  generalize dependent t. revert k.
  apply (lc_value_mutual_rec
           (fun (t': value) _ => ∀ (k : nat) (t : value), t' = {k ~> u} t → lc u → lc v → lc {k ~> v} t)
           (fun (t': tm) _ => ∀ (k : nat) (t : tm), t' = {k ~> u} t → lc u → lc v → lc {k ~> v} t)
        ); intros;
      repeat match goal with
      | H : _ = {_ ~> _} ?t |- _ => destruct t; ln_simpl; simplify_eq
      end;
  try solve [ lc_solver1; hauto].
all: econstructor; lc_solver1; eauto;
let x := fresh "x" in
let acc := collect_stales tt in instantiate (1 := acc); intros x **; simpl;
repeat specialize_with x; fold_syntax_class;
rewrite open_swap in *; eauto; lc_solver1.
Qed.
Arguments OpenLcRespect_value /.

Class OpenIdemp A `{Stale A} `{Open value A} := open_idemp :
forall (t: A) (u v: value) (k: nat),
    lc v ->
    {k ~> u} ({k ~> v} t) = ({k ~> v} t).

#[global] Instance OpenIdemp_tm: OpenIdemp tm.
Proof.
  unfold OpenIdemp.
  apply (tm_mutual_rec
                   (fun (t: value) => forall (u v: value) (k: nat),
                      lc v ->
                      {k ~> u} ({k ~> v} t) = ({k ~> v} t))
                   (fun (t: tm) => forall (u v: value) (k: nat),
                      lc v ->
                      {k ~> u} ({k ~> v} t) = ({k ~> v} t))
                ); intros; ln_simpl; f_equal; auto; fold_syntax_class;
  try solve [ln_simpl; f_equal; hauto].
  - rewrite open_rec_lc; hauto.
Qed.
Arguments OpenIdemp_tm /.

#[global] Instance OpenIdemp_value: OpenIdemp value.
Proof.
  unfold OpenIdemp.
  apply (value_mutual_rec
                   (fun (t: value) => forall (u v: value) (k: nat),
                      lc v ->
                      {k ~> u} ({k ~> v} t) = ({k ~> v} t))
                   (fun (t: tm) => forall (u v: value) (k: nat),
                      lc v ->
                      {k ~> u} ({k ~> v} t) = ({k ~> v} t))
                ); intros; ln_simpl; f_equal; auto; fold_syntax_class;
  try solve [ln_simpl; f_equal; hauto].
  - rewrite open_rec_lc; hauto.
Qed.
Arguments OpenIdemp_value /.

Global Hint Resolve lc_fresh_var_implies_body: core.
