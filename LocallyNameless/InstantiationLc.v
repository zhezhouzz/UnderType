From stdpp Require Import mapset.
From CT Require Import Syntax.
Import BaseDef MyTactics Primitives Lang Instantiation.
From CT.LocallyNameless Require Import LangLc QualifierLc RtyLc.

(** This file proves auxiliary lemmas about multi-substitution and provides handy tactics. *)

Lemma closed_env_insert env x v :
  env !! x = None ->
  closed_env (<[x:=v]>env) ->
  stale v = ∅ /\ closed_env env.
Proof.
  intro.
  unfold closed_env.
  rewrite map_Forall_insert; eauto.
Qed.

Ltac gen_closed_env :=
  repeat
    match goal with
    | H : closed_env (<[?i:=_]> ?m), H' : ?m !! ?i = None |- _ =>
        let H1 := fresh "H" in
        let H2 := fresh "H" in
        destruct (closed_env_insert _ _ _ H' H) as [H1 H2];
        uniq_hyp H1; uniq_hyp H2
    | H : closed_env ?m, H' : ?m !! _ = Some ?v |- _ =>
        let T := fresh "H" in
        assert (stale v = ∅) as T by eauto;
        uniq_hyp T
    end.

Class MsubstInsert A `{Subst value A} := msubst_insert: forall (σ: env) (x: atom) (v_x: value) (e: A),
    closed_env σ ->
    stale v_x = ∅ ->
    σ !! x = None ->
    msubst (<[x:=v_x]> σ) e = subst x v_x (msubst σ e).

Lemma MsubstInsert_all
    (A : Type)
    (staleA : Stale A)
    (substA : Subst value A)
    (subst_commuteA : @SubstCommute A staleA substA)
    : @MsubstInsert A substA.
Proof.
  unfold MsubstInsert.
  intros.
  apply map_fold_insert_L; eauto.
  intros.
  assert (closed_env (<[x:=v_x]>σ)). {
    apply map_Forall_insert; eauto.
  }
  gen_closed_env.
  apply subst_commute; eauto; my_set_solver.
Qed.

#[global] Instance MsubstInsert_tm: MsubstInsert tm.
Proof.
  eapply MsubstInsert_all; typeclasses eauto.
Qed.

#[global] Instance MsubstInsert_value: MsubstInsert value.
Proof.
  eapply MsubstInsert_all; typeclasses eauto.
Qed.

#[global] Instance MsubstInsert_qualifier: MsubstInsert qualifier.
Proof.
  eapply MsubstInsert_all; typeclasses eauto.
Qed.

#[global] Instance MsubstInsert_rty: MsubstInsert rty.
Proof.
  eapply MsubstInsert_all; typeclasses eauto.
Qed.

Ltac fold_forward :=
  repeat match goal with
    | H : map_fold ?f ?x ?m = _ |- context [ map_fold ?f ?x ?m ] => setoid_rewrite H
    | H : forall _ _ _ _, map_fold _ _ (<[?i:= _]> _) = _ ?i _ (map_fold _ _ _) |-
                       context [map_fold _ _ (<[?i:= _]> _) ] =>
        rewrite H
    | H : forall _ _ _ _, map_fold _ _ (<[?i:= _]> _) = _ ?i _ (map_fold _ _ _), H': context [map_fold _ _ (<[?i:= _]> _) ] |- _ =>
        rewrite H in H'
    end; eauto.

(* Ltac apply_msubst_ind :=
    unfold msubst;
    match goal with
    | |- ?T =>
        match T with
        | context [map_fold ?a ?b ?m] =>
            match eval pattern (map_fold a b m) in T with
            | ?P _ =>
                match eval pattern m in P with
                | ?P _ =>
                    (* let P := eval simpl in (fun r m => P m r) in *)
                    let P := eval simpl in (fun m => P m (msubst m b)) in
                      apply (fin_maps.map_fold_ind P); unfold msubst
                end
            end
        end
    end. *)

Ltac apply_msubst_ind :=
  intros_until (amap value);
  lazymatch goal with
  | |- forall σ : env, ?body =>
      let P := constr:(fun σ : env => body) in
      apply (fin_maps.map_fold_ind P)
  end; unfold msubst.

(* Ltac apply_msubst_ind :=
intros *;
  match goal with
    | |- context [msubst ?m _] =>
          generalize dependent m
    end;
  lazymatch goal with
  | |- forall σ : env, ?body =>
      let P := constr:(fun σ : env => body) in
      idtac P;
      apply (fin_maps.map_fold_ind P); intros *
  end; unfold msubst. *)

Ltac msubst_tac :=
  apply_msubst_ind; intros; subst; simpl; eauto;
  gen_closed_env; simp_hyps; subst; fold_forward.

(* Ltac msubst_tac' :=
  intros *; apply_msubst_ind; intros; subst; simpl; eauto;
  gen_closed_env; simp_hyps; subst; fold_forward. *)

Ltac fold_msubst := change (map_fold ?s ?e ?m) with (@msubst m _ e s) in *.

Ltac rewrite_msubst_insert :=
  cbn; fold_msubst; rewrite !msubst_insert;
  eauto using subst_commute.

Lemma rty_erase_msubst_eq ρ: forall σ,
  erase_rty ρ = erase_rty (m{σ} ρ).
Proof.
  msubst_tac.
  qauto using rty_erase_subst_eq.
Qed.

Ltac msubst_hyp_rewrite :=
  match goal with
  | H : (msubst ?f ?m ?x) = _ |-
      context [(msubst ?f ?m ?x) ] =>
      rewrite H
  end.

Lemma msubst_qualifier: forall ϕ σ,
    closed_env σ ->
    (m{σ}) ϕ =
      match ϕ with
      | qual vals prop =>
          qual (vmap (fun v => m{σ} v) vals) prop
      end.
Proof.
  msubst_tac.
  - destruct ϕ. erewrite Vector.map_ext.
    by rewrite Vector.map_id.
    intros. simpl.
    by rewrite map_fold_empty.
  - destruct ϕ.
    ln_simpl.
    f_equal. rewrite Vector.map_map.
    apply Vector.map_ext.
    intros; rewrite_msubst_insert.
Qed.

Lemma msubst_qualifier_and q1 q2: forall σ,
  closed_env σ ->
  m{σ} (q1 & q2) = (m{σ} q1) & (m{σ} q2).
Proof.
  msubst_tac. apply qualifier_and_subst.
Qed.

Lemma msubst_constant (c: constant): forall σ, (m{σ}) (vconst c) = vconst c.
Proof.
  msubst_tac.
Qed.

Lemma msubst_bvar: forall n σ, (m{σ}) (vbvar n) = vbvar n.
Proof.
  msubst_tac.
Qed.

Ltac class_simpl := autounfold with class_simpl; simpl; simplify_map_eq.

Lemma msubst_fvar: forall (x : atom) σ,
    closed_env σ ->
    (m{σ}) (vfvar x) = match σ !! x with
                 | Some v => v
                 | None => vfvar x
                 end.
Proof.
  msubst_tac.
  destruct (decide (x = i)); subst; simplify_map_eq.
  + class_simpl. reflexivity.
  + case_match.
    - apply subst_fresh. gen_closed_env. my_set_solver.
    - class_simpl; eauto.
Qed.

Lemma msubst_lam: forall T e σ,
    closed_env σ ->
    ((m{σ}) (vlam T e)) = (vlam T ((m{σ}) e)).
Proof.
  msubst_tac.
Qed.

Lemma msubst_fix: forall T e σ,
    closed_env σ ->
    ((m{σ}) (vfix T e)) = (vfix T ((m{σ}) e)).
Proof.
  msubst_tac.
Qed.

Lemma msubst_value: forall (v:value) σ,
    closed_env σ -> (m{σ}) (treturn v) = treturn ((m{σ}) v).
Proof.
  msubst_tac.
Qed.

Lemma msubst_err: forall (v:ty) σ,
    closed_env σ -> (m{σ}) (terr v) = terr v.
Proof.
  msubst_tac.
Qed.

Lemma msubst_match: forall (v: value) e1 e2 σ,
    closed_env σ ->
    ((m{σ}) (tmatchb v e1 e2)) = tmatchb (m{σ} v) (m{σ} e1) (m{σ} e2).
Proof.
  msubst_tac.
Qed.

Lemma msubst_lete: forall e_x e (σ: env),
    closed_env σ ->
    (m{σ} (tlete e_x e) = tlete ((m{σ}) e_x) ((m{σ}) e)).
Proof.
  msubst_tac.
Qed.

Lemma msubst_tleteffop: forall op (v2: value) e σ,
    closed_env σ ->
    (m{σ}) (tleteffop op v2 e) = (tleteffop op (m{σ} v2) (m{σ} e)).
Proof.
  msubst_tac.
Qed.

Lemma msubst_tletapp: forall (v1 v2: value) e σ,
    closed_env σ ->
    (m{σ}) (tletapp v1 v2 e) = (tletapp (m{σ} v1) (m{σ} v2) (m{σ} e)).
Proof.
  msubst_tac.
Qed.

Lemma msubst_overrty: forall b ϕ σ,
    closed_env σ ->
    (m{σ}) {:b|ϕ} = {:b| (m{σ}) ϕ}.
Proof.
  msubst_tac.
Qed.

Lemma msubst_underrty: forall b ϕ σ,
    closed_env σ ->
    ((m{σ}) ([:b|ϕ])) = ([:b|(m{σ}) ϕ]).
Proof.
  msubst_tac.
Qed.

Lemma msubst_arrrty: forall ρ τ σ,
    closed_env σ ->
    ((m{σ}) (ρ⇨τ)) = ((m{σ} ρ)⇨(m{σ} τ)).
Proof.
  msubst_tac.
Qed.

Lemma msubst_flip_rty: forall (τ: rty) σ,
    closed_env σ ->
    m{σ} (flip_rty τ) = flip_rty (m{σ} τ).
Proof.
  destruct τ; simpl flip_rty; intros; eauto.
  - rewrite msubst_overrty by eauto.
    rewrite msubst_underrty; eauto.
  - rewrite msubst_overrty by eauto.
    rewrite msubst_underrty; eauto.
  - repeat rewrite msubst_arrrty; eauto.
Qed.

(* Tactic Notation "rewrite_msubst" constr(lem) "in" hyp(H) := *)
(*   rewrite lem in H; eauto using ctxEnv_closed_env. *)

(* Tactic Notation "rewrite_msubst" constr(lem) := *)
(*   rewrite lem in *; eauto using ctxEnv_closed_env. *)

Class MsubstFresh (A: Type) `{Stale A} `{Subst value A} := msubst_fresh: forall (σ: env) (e: A),
    stale σ ∩ stale e = ∅ ->
    (m{σ}) e = e.

Lemma MsubstFresh_all
  (A : Type)
  (staleA : Stale A)
  (substA : Subst value A)
  (subst_freshA : @SubstFresh A staleA substA)
  : @MsubstFresh A staleA substA.
Proof.
  unfold MsubstFresh.
  msubst_tac.
  setoid_rewrite H1.
  + rewrite subst_freshA; eauto.
    ln_simpl. my_set_solver.
  + ln_simpl. my_set_solver. 
Qed.

#[global] Instance MsubstFresh_tm: MsubstFresh tm.
Proof.
  eapply MsubstFresh_all; typeclasses eauto.
Qed.

#[global] Instance MsubstFresh_value: MsubstFresh value.
Proof.
  eapply MsubstFresh_all; typeclasses eauto.
Qed.

#[global] Instance MsubstFresh_qualifier: MsubstFresh qualifier.
Proof.
  eapply MsubstFresh_all; typeclasses eauto.
Qed.

#[global] Instance MsubstFresh_rty: MsubstFresh rty.
Proof.
  eapply MsubstFresh_all; typeclasses eauto.
Qed.

Lemma msubst_mk_top: forall (σ: env) b,
    closed_env σ ->
    m{σ} (mk_top b) = mk_top b.
Proof.
  intros.
  rewrite msubst_fresh; eauto.
  unfold mk_top, mk_q_under_top. ln_simpl. my_set_solver.
Qed.

Lemma msubst_mk_eq_constant: forall (σ: env) c,
    closed_env σ ->
    (m{σ}) (mk_eq_constant c) = (mk_eq_constant c).
Proof.
  intros.
  rewrite msubst_fresh; eauto.
  unfold mk_eq_constant, mk_q_bvar_eq_val.
  ln_simpl. my_set_solver.
Qed.

Lemma msubst_mk_eq_var: forall (σ: env) b x v,
    closed_env σ ->
    σ !! x = Some v ->
    (m{σ}) (mk_eq_var b x) = [:b | b0:v= v].
Proof.
  intros.
  unfold mk_eq_var; eauto.
  repeat rewrite msubst_underrty; eauto.
  repeat rewrite msubst_qualifier; eauto.
  simpl.
  repeat rewrite msubst_bvar; eauto.
  repeat rewrite msubst_fvar; eauto.
  rewrite H0.
  eauto.
Qed.

Lemma msubst_empty {A: Type} `{Subst value A} : forall (e: A), m{∅} e = e.
Proof.
  intros. unfold msubst.
  rewrite map_fold_empty. auto.
Qed.

Lemma msubst_value_of_op Γv op :
  m{Γv} (value_of_op op) = value_of_op op.
Proof.
  rewrite msubst_fresh. eauto.
  my_set_solver.
Qed.

Ltac subst_simp :=
  match goal with
  | |- context [ {_:=_} (flip_rty _) ] => rewrite flip_rty_subst by eauto
  | H: context [ {_:=_} (flip_rty _) ] |- _ => rewrite flip_rty_subst in H by eauto
  | |- context [ stale (flip_rty _) ] => rewrite flip_rty_stale by eauto
  | H: context [ stale (flip_rty _) ] |- _ => rewrite flip_rty_stale in H by eauto
  | |- context [ ({_ ~> _} (flip_rty _)) ] => rewrite flip_rty_open by eauto
  | H: context [ ({_ ~> _} (flip_rty _)) ] |- _ => rewrite flip_rty_open in H by eauto
  end.

Ltac msubst_simp :=
  match goal with
  | |- context [ m{∅} _ ] => rewrite msubst_empty by eauto
  | H: context [ m{∅} _ ] |- _ => rewrite msubst_empty in H by eauto
  | H: context [ m{ _ } (tlete _ _) ] |- _ => rewrite msubst_lete in H by eauto
  | |- context [ m{ _ } (tlete _ _) ] => rewrite msubst_lete by eauto
  | H: context [ m{ _ } (tleteffop _ _ _) ] |- _ => rewrite msubst_tleteffop in H by eauto
  | |- context [ m{ _ } (tleteffop _ _ _) ] => rewrite msubst_tleteffop by eauto
  | H: context [ m{ _ } (tletapp _ _ _) ] |- _ => rewrite msubst_tletapp in H by eauto
  | |- context [ m{ _ } (tletapp _ _ _) ] => rewrite msubst_tletapp by eauto
  | H: context [ m{ _ } (vfix _ _) ] |- _ => rewrite msubst_fix in H by eauto
  | |- context [ m{ _ } (vfix _ _) ] => rewrite msubst_fix by eauto
  | H: context [ m{ _ } (treturn _) ] |- _ => rewrite msubst_value in H by eauto
  | |- context [ m{ _ } (treturn _) ] => rewrite msubst_value by eauto
  | H: context [ m{ _ } (vlam _ _) ] |- _ => rewrite msubst_lam in H by eauto
  | |- context [ m{ _ } (vlam _ _) ] => rewrite msubst_lam by eauto
  | H: context [ m{ _ } (terr _) ] |- _ => rewrite msubst_err in H by eauto
  | |- context [ m{ _ } (terr _) ] => rewrite msubst_err by eauto
  | H: context [ m{ _ } (tmatchb _ _ _) ] |- _ => rewrite msubst_match in H by eauto
  | |- context [ m{ _ } (tmatchb _ _ _) ] => rewrite msubst_match by eauto
  | H: context [ m{ _ } (vbvar _) ] |- _ => rewrite msubst_bvar in H by eauto
  | |- context [ m{ _ } (vbvar _) ] => rewrite msubst_bvar by eauto
  | H: context [ m{ _ } (vfvar _) ] |- _ => rewrite msubst_fvar in H by eauto
  | |- context [ m{ _ } (vfvar _) ] => rewrite msubst_fvar by eauto
  | H: context [ m{ _ } (vconst _) ] |- _ => rewrite msubst_constant in H by eauto
  | |- context [ m{ _ } (vconst _) ] => rewrite msubst_constant by eauto
  (* NOTE: don't unfold qualifier definition *)
  (* | H: context [ m{ _ } _ ] |- _ => rewrite msubst_qualifier in H *)
  (* | |- context [ m{ _ } _ ] => rewrite msubst_qualifier *)
  | H: context [ m{ _ } (_ & _) ] |- _ => rewrite msubst_qualifier_and in H by eauto
  | |- context [ m{ _ } (_ & _) ] => rewrite msubst_qualifier_and by eauto
  | H: context [ m{ _ } {: _ | _ } ] |- _ => rewrite msubst_overrty in H by eauto
  | |- context [ m{ _ } {: _ | _ } ] => rewrite msubst_overrty by eauto
  | H: context [ m{ _ } [: _ | _ ] ] |- _ => rewrite msubst_underrty in H by eauto
  | |- context [ m{ _ } [: _ | _ ] ] => rewrite msubst_underrty by eauto
  | H: context [ m{ _ } (_ ⇨ _) ] |- _ => rewrite msubst_arrrty in H by eauto
  | |- context [ m{ _ } (_ ⇨ _ ) ] => rewrite msubst_arrrty by eauto
  | H: context [ m{ _ } (mk_top _) ] |- _ => rewrite msubst_mk_top in H by eauto
  | |- context [ m{ _ } (mk_top _) ] => rewrite msubst_mk_top by eauto
  | H: context [ m{ _ } (mk_eq_constant _) ] |- _ => rewrite msubst_mk_eq_constant in H by eauto
  | |- context [ m{ _ } (mk_eq_constant _) ] => rewrite msubst_mk_eq_constant by eauto
  | H: context [ m{ _ } (flip_rty _) ] |- _ => rewrite msubst_flip_rty in H by eauto
  | |- context [ m{ _ } (flip_rty _) ] => rewrite msubst_flip_rty by eauto
  | H: context [ m{ _ } (mk_eq_var _ ?x) ], H': _ !! ?x = Some ?v |- _ => rewrite msubst_mk_eq_var with (v:=v) in H by eauto
  | H': _ !! ?x = Some ?v |- context [ m{ _ } (mk_eq_var _ ?x) ] => rewrite msubst_mk_eq_var with (v:=v) by eauto
  | _ => subst_simp
  end; eauto.

(* Most lemmas here are generalization of the corresponding lemmas about
single-substitution. *)

Class MsubstOpenVar A `{Stale A} `{Open value A} `{Subst value A} `{Lc A} := msubst_open_var :
forall e k (x: atom) (σ: env),
    closed_env σ ->
    map_Forall (fun _ v => lc (treturn v)) σ ->
    x ∉ dom σ ->
    (m{σ}) ({k ~> (vfvar x)} e) = {k ~> (vfvar x)} ((m{σ}) e).

Lemma MsubstOpenVar_all
(A : Type)
(staleA : Stale A)
(openA : Open value A)
(substA : Subst value A)
(lcA : Lc A)
(* (subst_openA : @SubstOpenVar A staleA openA substA lcA) *)
(subst_open_varA : @SubstOpenVar A staleA openA substA lcA)
: @MsubstOpenVar A staleA openA substA lcA.
Proof.
  unfold MsubstOpenVar.
  msubst_tac.
  apply map_Forall_insert in H3; eauto.
    setoid_rewrite H7; eauto.
    apply subst_open_var.
    all: lc_solver1; my_set_solver.
Qed.

#[global] Instance MsubstOpenVar_tm: MsubstOpenVar tm.
Proof.
  eapply MsubstOpenVar_all; typeclasses eauto.
Qed.

#[global] Instance MsubstOpenVar_value: MsubstOpenVar value.
Proof.
  eapply MsubstOpenVar_all; typeclasses eauto.
Qed.

#[global] Instance MsubstOpenVar_rty: MsubstOpenVar rty.
Proof.
  eapply MsubstOpenVar_all; typeclasses eauto.
Qed.

#[global] Instance MsubstOpenVar_qualifier: MsubstOpenVar qualifier.
Proof.
  eapply MsubstOpenVar_all; typeclasses eauto.
Qed.

Class MsubstOpen A `{Stale A} `{Open value A} `{Subst value A}  `{Lc A} := msubst_open :
forall (ρ: A) k (v_x: value) (σ: env),
    closed_env σ ->
    map_Forall (fun _ v => lc (treturn v)) σ ->
    (m{σ}) ({k ~> v_x} ρ) = {k ~> (m{σ} v_x)} (m{σ} ρ).

Lemma MsubstOpen_all
(A : Type)
(staleA : Stale A)
(openA : Open value A)
(substA : Subst value A)
(lcA : Lc A)
(subst_openA : @SubstOpen A staleA openA substA lcA)
: @MsubstOpen A staleA openA substA lcA.
Proof.
  unfold MsubstOpen.
  msubst_tac.
  apply map_Forall_insert in H3; eauto. simp_hyps.
  fold_forward.
  rewrite subst_openA; auto. 
  lc_solver1; my_set_solver.
Qed.

#[global] Instance MsubstOpen_tm: MsubstOpen tm.
Proof.
  apply MsubstOpen_all; typeclasses eauto.
Qed.

#[global] Instance MsubstOpen_value: MsubstOpen value.
Proof.
  eapply MsubstOpen_all; typeclasses eauto.
Qed.

#[global] Instance MsubstOpen_rty: MsubstOpen rty.
Proof.
  eapply MsubstOpen_all; typeclasses eauto.
Qed.

#[global] Instance MsubstOpen_qualifier: MsubstOpen qualifier.
Proof.
  eapply MsubstOpen_all; typeclasses eauto.
Qed.

Class MsubstFv A `{Stale A} `{Subst value A} := msubst_fv :
forall (σ: env) (e: A),
    closed_env σ ->
    stale (m{σ} e) ⊆ stale e.

Lemma MsubstFv_all
(A : Type)
(staleA : Stale A)
(openA : Open value A)
(substA : Subst value A)
(fv_of_subst_closedA : @FvOfSubstClosed A staleA substA)
: @MsubstFv A staleA substA.
Proof.
  unfold MsubstFv.
  msubst_tac.
  rewrite fv_of_subst_closedA; my_set_solver.
Qed.

#[global] Instance MsubstFv_tm: MsubstFv tm.
Proof.
  eapply MsubstFv_all; typeclasses eauto.
Qed.

#[global] Instance MsubstFv_value: MsubstFv value.
Proof.
  eapply MsubstFv_all; typeclasses eauto.
Qed.

#[global] Instance MsubstFv_qualifier: MsubstFv qualifier.
Proof.
  eapply MsubstFv_all; typeclasses eauto.
Qed.

#[global] Instance MsubstFv_rty: MsubstFv rty.
Proof.
  eapply MsubstFv_all; typeclasses eauto.
Qed.

Class MsubstIntro A `{Stale A} `{Open value A} `{Subst value A} `{Lc A} := msubst_intro :
forall (e: A) k (v_x: value) (x: atom) (σ: env),
    closed_env σ ->
    stale v_x = ∅ ->
    lc v_x ->
    map_Forall (fun _ v => lc (treturn v)) σ ->
    x ∉ dom σ ∪ stale e ->
    {k ~> v_x} ((m{σ}) e) = (m{<[x:=v_x]> σ}) ({k ~> (vfvar x)} e).

Lemma MsubstIntro_all
(A : Type)
(staleA : Stale A)
(openA : Open value A)
(substA : Subst value A)
(lcA : Lc A)
(msubst_openA : @MsubstOpen A staleA openA substA lcA)
(subst_freshA : @SubstFresh A staleA substA)
(msubst_insertA : @MsubstInsert A substA)
(msubst_fvA : @MsubstFv A staleA substA)
: @MsubstIntro A staleA openA substA lcA.
Proof.
  unfold MsubstIntro.
  intros.
  assert (stale σ ∩ stale x = ∅) by my_set_solver.
  assert (σ !! x = None). {
     apply not_elem_of_dom. my_set_solver.
  }
  rewrite msubst_openA; auto.
  rewrite_msubst_insert.
  f_equal.
  - rewrite msubst_fresh; eauto. 
    autounfold with class_simpl in *. hauto.
  - rewrite subst_freshA; eauto.
    assert (stale ((m{σ}) e) ⊆ stale e) by eauto using msubst_fvA. my_set_solver. 
  - apply map_Forall_insert; eauto.
  - apply map_Forall_insert; eauto.
    intuition. lc_solver1; my_set_solver.
Qed. 

#[global] Instance MsubstIntro_tm: MsubstIntro tm.
Proof.
  eapply MsubstIntro_all; typeclasses eauto.
Qed.

#[global] Instance MsubstIntro_value: MsubstIntro value.
Proof.
  eapply MsubstIntro_all; typeclasses eauto.
Qed.

#[global] Instance MsubstIntro_qualifier: MsubstIntro qualifier.
Proof.
  eapply MsubstIntro_all; typeclasses eauto.
Qed.

#[global] Instance MsubstIntro_rty: MsubstIntro rty.
Proof.
  eapply MsubstIntro_all; typeclasses eauto.
Qed.

Class MsubstInsertFresh A `{Stale A} `{Subst value A} := msubst_insert_fresh :
forall (e: A) (x: atom) (v_x: value) (σ: env),
    closed_env σ ->
    stale v_x = ∅ ->
    x ∉ dom σ ∪ stale e ->
    (m{<[x:=v_x]> σ}) e = (m{σ}) e.

Lemma MsubstInsertFresh_all
(A : Type)
(staleA : Stale A)
(substA : Subst value A)
(subst_freshA : @SubstFresh A staleA substA)
(msubst_insertA : @MsubstInsert A substA)
(msubst_fvA : @MsubstFv A staleA substA)
: @MsubstInsertFresh A staleA substA.
Proof.
  unfold MsubstInsertFresh.
  intros. rewrite_msubst_insert.
  - apply subst_freshA.
    pose proof (msubst_fvA σ e H).
    eapply not_elem_of_weaken; eauto. my_set_solver.
  - apply not_elem_of_dom; my_set_solver.
Qed.

#[global] Instance MsubstInsertFresh_tm: MsubstInsertFresh tm.
Proof.
  eapply MsubstInsertFresh_all; typeclasses eauto.
Qed.

#[global] Instance MsubstInsertFresh_value: MsubstInsertFresh value.
Proof.
  eapply MsubstInsertFresh_all; typeclasses eauto.
Qed.

#[global] Instance MsubstInsertFresh_qualifier: MsubstInsertFresh qualifier.
Proof.
  eapply MsubstInsertFresh_all; typeclasses eauto.
Qed.

#[global] Instance MsubstInsertFresh_rty: MsubstInsertFresh rty.
Proof.
  eapply MsubstInsertFresh_all; typeclasses eauto.
Qed.

Class MsubstLc A `{Stale A} `{Subst value A} `{Lc A} := msubst_lc :
forall (e: A) (σ: env),
    lc e ->
    map_Forall (fun _ v => lc (treturn v)) σ ->
    lc (m{σ} e).

Lemma MsubstLc_all
(A : Type)
(staleA : Stale A)
(substA : Subst value A)
(lcA : Lc A)
(subst_lcA : @SubstLc A staleA substA lcA)
: @MsubstLc A staleA substA lcA.
Proof.
  unfold MsubstLc.
  msubst_tac.
  apply map_Forall_insert in H3; eauto.
  apply subst_lcA. hauto. lc_solver1; my_set_solver.
Qed.

#[global] Instance MsubstLc_tm: MsubstLc tm.
Proof.
  eapply MsubstLc_all; typeclasses eauto.
Qed.

#[global] Instance MsubstLc_value: MsubstLc value.
Proof.
  eapply MsubstLc_all; typeclasses eauto.
Qed.

#[global] Instance MsubstLc_qualifier: MsubstLc qualifier.
Proof.
  eapply MsubstLc_all; typeclasses eauto.
Qed.

#[global] Instance MsubstLc_rty: MsubstLc rty.
Proof.
  eapply MsubstLc_all; typeclasses eauto.
Qed.

Class LcMsubst A `{Stale A} `{Subst value A} `{Lc A} := lc_msubst :
forall (e: A) (σ: env),
    lc (m{σ} e) ->
    map_Forall (fun _ v => lc (treturn v)) σ ->
    lc e.

Lemma LcMsubst_all
(A : Type)
(staleA : Stale A)
(substA : Subst value A)
(lcA : Lc A)
(lc_substA : @LcSubst A staleA substA lcA)
: @LcMsubst A staleA substA lcA.
Proof.
  unfold LcMsubst.
  msubst_tac.
  apply map_Forall_insert in H3; eauto. simp_hyps.
  assert (lc x) by lc_solver1; my_set_solver.
Qed.

#[global] Instance LcMsubst_tm: LcMsubst tm.
Proof.
  eapply LcMsubst_all; typeclasses eauto.
Qed.

#[global] Instance LcMsubst_value: LcMsubst value.
Proof.
  eapply LcMsubst_all; typeclasses eauto.
Qed.

#[global] Instance LcMsubst_qualifier: LcMsubst qualifier.
Proof.
  eapply LcMsubst_all; typeclasses eauto.
Qed.

#[global] Instance LcMsubst_rty: LcMsubst rty.
Proof.
  eapply LcMsubst_all; typeclasses eauto.
Qed.

Class FvOfMsubstClosed A `{Stale A} `{Subst value A} := fv_of_msubst_closed :
forall (e: A) (σ: env),
    closed_env σ ->
    stale (m{σ} e) = stale e ∖ stale σ.

Lemma FvOfMsubstClosed_all
(A : Type)
(staleA : Stale A)
(substA : Subst value A)
(fv_of_subst_closedA : @FvOfSubstClosed A staleA substA)
: @FvOfMsubstClosed A staleA substA.
Proof.
  unfold FvOfMsubstClosed.
  msubst_tac.
  - rewrite map_fold_empty. my_set_solver.
  - rewrite fv_of_subst_closedA.
    + setoid_rewrite H5. my_set_solver.
    + hauto.
Qed.

#[global] Instance FvOfMsubstClosed_tm: FvOfMsubstClosed tm.
Proof.
  eapply FvOfMsubstClosed_all; typeclasses eauto.
Qed.

#[global] Instance FvOfMsubstClosed_value: FvOfMsubstClosed value.
Proof.
  eapply FvOfMsubstClosed_all; typeclasses eauto.
Qed.

#[global] Instance FvOfMsubstClosed_qualifier: FvOfMsubstClosed qualifier.
Proof.
  eapply FvOfMsubstClosed_all; typeclasses eauto.
Qed.

#[global] Instance FvOfMsubstClosed_rty: FvOfMsubstClosed rty.
Proof.
  eapply FvOfMsubstClosed_all; typeclasses eauto.
Qed.

Ltac rewrite_msubst_insert_in H :=
  cbn in H; 
  change (map_fold ?s ?e ?m) with (@msubst m _ e s) in H;
  rewrite !msubst_insert in H;
  eauto using subst_commute.

Class MsubstUnion (A: Type) `{Stale A} `{Subst value A} := msubst_union :
forall (σ: env) (e: A),
closed_env (σ) ->
forall (σ1 σ2: env), 
σ1 ∪ σ2 = σ ->
dom σ1 ∩ dom σ2 = ∅ ->
m{σ1 ∪ σ2} e = m{σ1} (m{σ2} e).

Lemma elem_of_dom_implies_in_union (A: Type) (x: atom) (v: A) (σ: amap A):
σ !! x = Some v -> x ∈ dom σ.
Proof.
  intros.
  rewrite elem_of_dom. exists v. eauto.
Qed.

Lemma MsubstUnion_all
(A: Type) 
(staleA: Stale A) 
(substA: Subst value A)
(subst_commuteA: @SubstCommute A staleA substA)
: @MsubstUnion A staleA substA.
Proof.
  unfold MsubstUnion. intros. unfold msubst.
  apply map_fold_union_strong.
  - constructor; eauto.
    intros x y z Hxy Hyz; subst; eauto.
  - intros. unfold Proper, respectful.
    intros a a0 Ha. subst. reflexivity.
  - intros.
    apply elem_of_dom_implies_in_union in H2, H3.
    my_set_solver.
  - intros.
    rewrite <- H0 in H.
    apply map_Forall_union in H.
    mydestr. 
    destruct H3, H4;
    eapply map_Forall_lookup_1 in H3; eauto;
    eapply map_Forall_lookup_1 in H4; eauto;
    simpl in *;
    rewrite subst_commuteA; eauto; my_set_solver.
    rewrite map_disjoint_dom. my_set_solver.
Qed.

#[global] Instance MsubstUnion_tm: MsubstUnion tm.
Proof.
  eapply MsubstUnion_all; typeclasses eauto.
Qed.

#[global] Instance MsubstUnion_value: MsubstUnion value.
Proof.
  eapply MsubstUnion_all; typeclasses eauto.
Qed.

#[global] Instance MsubstUnion_qualifier: MsubstUnion qualifier.
Proof.
  eapply MsubstUnion_all; typeclasses eauto.
Qed.

#[global] Instance MsubstUnion_rty: MsubstUnion rty.
Proof.
  eapply MsubstUnion_all; typeclasses eauto.
Qed.

Class MsubstFilterSame (A: Type) `{Stale A} `{Subst value A} := msubst_filter_same :
forall (σ1 σ2: env) (L: aset),
closed_env σ1 ->
closed_env σ2 ->
[D L ] σ1 = [D L ] σ2 -> 
forall (e: A), stale e ⊆ L -> m{σ1} e = m{σ2} e.

Lemma MsubstFilterSame_all
(A: Type) 
(staleA: Stale A) 
(substA: Subst value A) 
(msubst_freshA: @MsubstFresh A staleA substA)
(msubst_unionA: @MsubstUnion A staleA substA)
: @MsubstFilterSame A staleA substA.
Proof.
  unfold MsubstFilterSame.
  intros σ1 σ2 L Hclosed1 Hclosed2 H e Hstale.
  rewrite (restrict_keys_split L σ1).
  rewrite (restrict_keys_split L σ2).
  pose proof (restrict_keys_union_compl L σ1) as Hunion1.
  pose proof (restrict_keys_union_compl L σ2) as Hunion2.
  eapply msubst_unionA in Hunion1.
  rewrite Hunion1.
  eapply msubst_unionA in Hunion2.
  rewrite Hunion2.
  rewrite H.
  f_equal.
  rewrite msubst_freshA.
  rewrite msubst_freshA. eauto.
  all: fold_syntax_class;
       try rewrite stale_restrict_keys_compl;
       try rewrite stale_restrict_keys; eauto; my_set_solver.
Qed.

#[global] Instance MsubstFilterSame_tm: MsubstFilterSame tm.
Proof.
  eapply MsubstFilterSame_all; typeclasses eauto.
Qed.

#[global] Instance MsubstFilterSame_value: MsubstFilterSame value.
Proof.
  eapply MsubstFilterSame_all; typeclasses eauto.
Qed.

#[global] Instance MsubstFilterSame_qualifier: MsubstFilterSame qualifier.
Proof.
  eapply MsubstFilterSame_all; typeclasses eauto.
Qed.

#[global] Instance MsubstFilterSame_rty: MsubstFilterSame rty.
Proof.
  eapply MsubstFilterSame_all; typeclasses eauto.
Qed.