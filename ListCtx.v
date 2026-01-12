From stdpp Require Import mapset.
From CT Require Import BaseDef.
From CT Require Import MyTactics.
From Stdlib Require Import Lists.List.
Import BaseDef.
Import List.
From Hammer Require Import Tactics.

(** This file defines an ordered type context used in refinement typing. *)

(** Type Context Definition (Γ in Fig. 4) *)
(** We use list instead of set since the type context in the refinement typing has dependency. *)
Definition listctx (A: Type) := list (atom * A).

Fixpoint ctxdom {A: Type} (Γ: listctx A) : aset :=
  match Γ with
  | [] => ∅
  | (x, _) :: Γ => {[x]} ∪ ctxdom Γ
  end.

#[global]
Instance listctx_stale {A:Type} : Stale (listctx A) := ctxdom.
Arguments listctx_stale /. 

Lemma app_one_eq_nil {A: Type}: forall (x: atom) (tau:A) Γ, ~ ([] = Γ ++ [(x, tau)]).
Proof. destruct Γ; sauto. Qed.

Lemma app_one_is_cons {A: Type}: forall (x: A) l, (x::nil) ++ l = x :: l.
Proof. hauto. Qed.

Lemma app_list_unit_eq_unit {A: Type}: forall (x y: A) l, l ++ [x] = [y] -> x = y /\ l = [].
Proof. intros. apply app_eq_unit in H. sauto. Qed.

Ltac list_app_simpl_aux1 :=
  match goal with
    | [a: prod _ _ |- _] => destruct a
    | [H: [_] = [] |- _ ] => sinvert H
    | [H: [] = [_] |- _ ] => sinvert H
    | [H: [] = ?l1 ++ [_] |- _ ] =>
      apply app_cons_not_nil in H; sinvert H 
    | [H: ?l1 ++ ?l2 = [] |- _ ] =>
      rewrite (app_nil l1 l2) in H; simp_hyp H; subst
    | [H: ?Γ1 ++ [(?x1, ?t1)] = ?Γ2 ++ [(?x2, ?t2)] |- _ ] => apply app_inj_tail in H; destruct H; subst
    | [H: (?x1, ?t1) = (?x2, ?t2) |- _ ] => inversion H; subst; clear H
    | [H: context [ ?a ++ []] |- _ ] => rewrite app_nil_r in H
    | [ |- context [ ?a ++ []] ] => rewrite app_nil_r
    | [H: context [ [] ++ ?a] |- _ ] => rewrite app_nil_l in H
    | [ |- context [ [] ++ ?a] ] => rewrite app_nil_l
    | [H: context [(_ :: _) ++ _] |- _ ] => rewrite <- app_comm_cons in H
    | [ |- context [(_ :: _) ++ _]] => rewrite <- app_comm_cons
    | [H: context [(_ ++ _) ++ _] |- _ ] => rewrite <- app_assoc in H
    | [ |- context [(_ ++ _) ++ _]] => rewrite <- app_assoc
  end.

Ltac list_app_simpl :=
  repeat list_app_simpl_aux1; auto.

Lemma ctxdom_app_union {A: Type}: forall (Γ1 Γ2: listctx A), ctxdom (Γ1 ++ Γ2) = (ctxdom Γ1) ∪ (ctxdom Γ2).
Proof.
  induction Γ1; simpl; intros; auto.
  - set_solver.
  - list_app_simpl. rewrite IHΓ1. set_solver.
Qed.

(** Definition of non-duplicate. *)
Inductive ok {A: Type} : (listctx A) -> Prop :=
| ok_nil: ok nil
| ok_cons: forall Γ (x: atom) (t: A), ok Γ -> x ∉ ctxdom Γ -> ok (Γ ++ [(x, t)]).

Global Hint Constructors ok: core.

Lemma ok_post_destruct {A: Type}: forall Γ (x: atom) (t: A), ok (Γ ++ [(x, t)]) <-> ok Γ /\ x ∉ ctxdom Γ.
Proof.
  intros. split.
  - split; inversion H; subst; list_app_simpl;
    destruct Γ; sauto.
  - sauto.
Qed.

Lemma ok_pre_destruct {A: Type}: forall Γ (x: atom) (t: A), ok ((x, t) :: Γ) <-> ok Γ /\ x ∉ ctxdom Γ.
Proof.
  split; generalize dependent t. generalize dependent x. generalize dependent Γ.
  - apply (rev_ind (fun Γ => forall (x: atom) (t: A), ok ((x, t) :: Γ) -> ok Γ /\ x ∉ ctxdom Γ));
      simpl; split; intros; list_app_simpl; auto; try set_solver.
    + rewrite app_comm_cons in H0. rewrite ok_post_destruct in H0. destruct H0.
      specialize (H x0 t H0). destruct H.
      constructor; auto. set_solver.
    + rewrite app_comm_cons in H0. rewrite ok_post_destruct in H0. destruct H0.
      specialize (H x0 t H0). destruct H. rewrite ctxdom_app_union. set_solver.
  - apply (rev_ind (fun Γ => forall (x: atom) (t: A), ok Γ /\ x ∉ ctxdom Γ -> ok ((x, t) :: Γ)));
      simpl; intros.
    + destruct H. rewrite <- app_nil_l. constructor; auto.
    + list_app_simpl. destruct H0.
      rewrite ok_post_destruct in H0. destruct H0. rewrite ctxdom_app_union in H1.
      rewrite app_comm_cons. constructor; auto. apply H; auto. split; auto. set_solver. set_solver.
Qed.

(** another ok definition *)
Inductive ok_forward {A: Type} : (listctx A) -> Prop :=
| ok_nil_forward: ok_forward nil
| ok_cons_forward: forall Γ (x: atom) (t: A), ok_forward Γ -> x ∉ ctxdom Γ -> ok_forward ((x, t) :: Γ).

Global Hint Constructors ok_forward: core.

(** two definitions is equal *)
Lemma ok_iff_of_ok_forward {A: Type}: forall (Γ: listctx A), ok Γ <-> ok_forward Γ.
Proof.
  split; induction Γ; intros; auto; list_app_simpl.
  - apply ok_pre_destruct in H. hauto.
  - rewrite ok_pre_destruct. invert H; hauto.
Qed.

Lemma ok_weak_pre {A: Type}: forall (Γ1 Γ2: listctx A),
    ok (Γ1 ++ Γ2) -> ok Γ1.
Proof.
  intros Γ1.
  apply (rev_ind (fun Γ2 => ok (Γ1 ++ Γ2) -> ok Γ1)); intros; list_app_simpl.
  - apply H. 
    rewrite app_assoc in *.
    rewrite ok_post_destruct in *. hauto.
Qed.

Lemma ok_weak_post {A: Type}: forall (Γ2 Γ1: listctx A),
    ok (Γ1 ++ Γ2) -> ok Γ2.
Proof.
  intros Γ2. induction Γ1; intros; list_app_simpl.
  - apply IHΓ1. rewrite ok_iff_of_ok_forward in *.
    invert H; hauto.
Qed.

(** ctxfind *)
Fixpoint ctxfind {A: Type} (Γ: listctx A) (x: atom): option A :=
  match Γ with
  | [] => None
  | (y, t) :: Γ => if decide (x = y) then Some t else ctxfind Γ x
  end.

Lemma ctxfind_none_iff_not_in_dom {A: Type}: forall (Γ: listctx A) x,
    ctxfind Γ x = None <-> x ∉ ctxdom Γ.
Proof with auto.
  split; generalize dependent x; induction Γ; simpl; intros; list_app_simpl.
  set_solver.
  all: mydestr; set_solver.
Qed.

Lemma ctxfind_some_spec1 {A: Type}: forall (Γ: listctx A) x (a: A),
    ctxfind Γ x = Some a -> ∃ l1 l2, Γ = l1 ++ (x, a) :: l2 /\ x ∉ ctxdom l1.
Proof.
  induction Γ; simpl; intros; list_app_simpl.
  + hauto.
  + mydestr; auto.
    - invert H; subst. exists [], Γ. split. hauto. set_solver.
    - apply IHΓ in H. destruct H as (l1 & l2 & H1 & H2). subst.
      exists ((a, a1) :: l1), l2. split. hauto. set_solver.
Qed.

Lemma ctxfind_some_spec2 {A: Type}: forall (Γ: listctx A) x (a: A),
    (∃ l1 l2, Γ = l1 ++ (x, a) :: l2 /\ x ∉ ctxdom l1) -> ctxfind Γ x = Some a.
Proof.
  induction Γ; simpl; intros; list_app_simpl; destruct H as (l1 & l2 & H1 & H2); subst.
  + destruct l1; hauto.
  + mydestr; list_app_simpl.
    - destruct l1. hauto. set_solver.
    - destruct l1. hauto. set_solver.
Qed.

Lemma ctxfind_some_spec {A: Type}: forall (Γ: listctx A) x (a: A),
    ctxfind Γ x = Some a <-> ∃ l1 l2, Γ = l1 ++ (x, a) :: l2 /\ x ∉ ctxdom l1.
Proof.
  split. apply ctxfind_some_spec1. apply ctxfind_some_spec2.
Qed.

Lemma ctxfind_some_implies_in_dom {A: Type}: forall (Γ: listctx A) x (a: A),
    ctxfind Γ x = Some a -> x ∈ ctxdom Γ.
Proof.
  intros. rewrite ctxfind_some_spec in H. destruct H as (l1 & l2 & H1 & H2). subst. rewrite ctxdom_app_union. set_solver.
Qed.

Ltac listctx_set_simpl_aux :=
  match goal with
    | [H: ctxfind _ _ = Some _ |- _ ⊆ _ ] => apply ctxfind_some_implies_in_dom in H
    | [H: ctxfind _ _ = Some _ |- _ ∉ _ ] => apply ctxfind_some_implies_in_dom in H
    | [H: ctxfind _ _ = Some _ |- _ ∈ _ ] => apply ctxfind_some_implies_in_dom in H
    | [H: ctxfind _ _ = None |- _ ] => rewrite ctxfind_none_iff_not_in_dom in H
    | [|- ctxfind _ _ = None ] => rewrite ctxfind_none_iff_not_in_dom
    | [H: ok (((?x, _) :: _) ++ [(?y, _)]) |- _ ] =>
        rewrite <- app_comm_cons in H
    | [H: ok ((?x, _) :: _) |- _ ] =>
        rewrite ok_pre_destruct in H; destruct H
    | [H: ok (_ ++ [(_, _)]) |- _ ] =>
        rewrite ok_post_destruct in H; destruct H
    | [H: context [ctxdom (_ ++ _)] |- _ ] =>
        rewrite ctxdom_app_union in H; simpl in H
    | [H: context [stale (_ ++ _)] |- _ ] =>
        rewrite ctxdom_app_union in H; simpl in H
    | [|- context [ctxdom (_ ++ _)] ] =>
        rewrite ctxdom_app_union; simpl
    end.

Ltac listctx_set_simpl' := 
  repeat (first [list_app_simpl_aux1 | listctx_set_simpl_aux ]); auto.

Lemma ctxfind_none_neq_hd {A: Type}: forall (Γ: listctx A) x tx a,
    ctxfind ((x, tx):: Γ) a = None -> x <> a.
Proof with auto.
  intros. rewrite ctxfind_none_iff_not_in_dom in H. set_solver.
Qed.

Ltac ok_list_simpl :=
  match goal with
    | [H: ok (_ :: _) |- _ ] => apply ok_pre_destruct in H
    | [H: ok (_ ++ [_]) |- _ ] => apply ok_post_destruct in H
  end; auto.

Lemma ctxfind_app {A: Type}: forall Γ1 Γ2 x (T: A),
    ok (Γ1 ++ Γ2) ->
    ctxfind (Γ1 ++ Γ2) x = Some T <-> ctxfind Γ1 x = Some T \/ ctxfind Γ2 x = Some T.
Proof.
  induction Γ1; split; intros; listctx_set_simpl'.
  - hauto.
  - hauto.
  - simpl in *; mydestr; auto.
    + intuition. apply ctxfind_some_implies_in_dom in H2. set_solver. 
    + hauto.
Qed.  

Lemma ctxfind_app_exclude {A: Type}: forall (Γ1 Γ2: listctx A), ok (Γ1 ++ Γ2) -> (ctxdom Γ1) ∩ (ctxdom Γ2) = ∅.
Proof.
  induction Γ1; intros; simpl; listctx_set_simpl'; set_solver.
Qed.

Lemma ctxfind_app_weaken {A: Type}: forall Γ1 Γ2 Γ3 x (T: A),
    ok (Γ1 ++ Γ2 ++ Γ3) ->
    ctxfind (Γ1 ++ Γ3) x = Some T -> ctxfind (Γ1 ++ Γ2 ++ Γ3) x = Some T.
Proof.
  induction Γ1; simpl; intros; listctx_set_simpl'.
  - rewrite ctxfind_app; auto.
  - hauto.
Qed.

Lemma ok_app_weaken {A: Type}: forall (Γ1 Γ2: listctx A) x (Tx :A),
    ok (Γ1 ++ (x, Tx) :: Γ2) -> ok (Γ1 ++ Γ2).
Proof.
  induction Γ1; simpl; intros; listctx_set_simpl'; auto.
  - apply IHΓ1 in H. rewrite ok_pre_destruct. listctx_set_simpl'. set_solver.
Qed.

Lemma ctxfind_find_mid_eq {A: Type}: forall (Γ1 Γ3: listctx A) x (U T:A),
    ok (Γ1 ++ (x, U) :: Γ3) ->
    ctxfind (Γ1 ++ (x, U) :: Γ3) x = Some T -> U = T.
Proof.
  intros. rewrite ctxfind_app in H0; auto. destruct H0; auto.
  + apply ctxfind_app_exclude in H. 
    apply ctxfind_some_implies_in_dom in H0. set_solver.
  + hauto. 
Qed.

Lemma ctxfind_find_mid_neq {A: Type}: forall (Γ1 Γ3: listctx A) x y (U T:A),
    x <> y ->
    ok (Γ1 ++ (x, U) :: Γ3) ->
    ctxfind (Γ1 ++ (x, U) :: Γ3) y = Some T -> ctxfind (Γ1 ++ Γ3) y = Some T.
Proof.
  induction Γ1; simpl; intros; listctx_set_simpl'; hauto.
Qed.

Lemma find_mid_eq_singleton_simp {A: Type} : forall (x1 x2: atom) (τ1 τ2: A) Γ1 Γ2,
    [(x1, τ1)] = Γ1 ++ (x2, τ2) :: Γ2 -> x1 = x2 /\ τ1 = τ2 /\ Γ1 = [] /\ Γ2 = [].
Proof.
  intros.
  destruct Γ1; invert H; listctx_set_simpl'.
  destruct Γ1; hauto.
Qed.

Lemma find_mid_eq_cons_simp {A: Type} : forall (x1 x2: atom) (τ1 τ2: A) Γ1 Γ2 Γ,
    (x1, τ1) :: Γ = Γ1 ++ (x2, τ2) :: Γ2 ->
    (x1 = x2 /\ τ1 = τ2 /\ Γ1 = [] /\ Γ2 = Γ) \/
      (exists Γ1', Γ = Γ1' ++ (x2, τ2) ::  Γ2 /\ Γ1 = (x1, τ1) :: Γ1').
Proof.
  intros.
  destruct Γ1; (invert H; listctx_set_simpl'); hauto.
Qed.

Ltac listctx_set_simpl_aux2 :=
  match goal with
  | [H: context [ctxfind [] _] |- _ ] => progress simpl in H
  | [|- context [ctxfind [] _]] => progress simpl
  | [H1: ok (?Γ1 ++ (?x, ?U) :: ?Γ3), H: ctxfind (?Γ1 ++ (?x, ?U) :: ?Γ3) ?x = Some ?T |- _ ] => 
    assert (U = T) as Htmp by (apply (ctxfind_find_mid_eq _ _ _ _ T) in H1; auto); subst; try clear Htmp
  | [H: ctxfind (?Γ1 ++ (?z, _) :: ?Γ3) ?x = Some ?T
 |- ctxfind (?Γ1 ++ ?Γ3) ?x = Some ?T ] => 
    apply ctxfind_find_mid_neq in H
  | [H: (_, _) :: _ = (_, _):: _ |- _ ] => invclear H
  | [H: [(_, _)] = _ ++ (_, _) :: _ |- _ ] => 
    apply find_mid_eq_singleton_simp in H; subst
  | [H: (_, _) :: _ = _ ++ (_, _) :: _ |- _ ] => 
    apply find_mid_eq_cons_simp in H; destruct H; subst
  | [H: (_, _) :: _ = (_, _):: _ |- _ ] => invclear H
  | [H: [(_, _)] = _ ++ (_, _) :: _ |- _ ] => 
    apply find_mid_eq_singleton_simp in H; subst
  | [H: (_, _) :: _ = _ ++ (_, _) :: _ |- _ ] => 
    apply find_mid_eq_cons_simp in H; destruct H; subst
  | [H: _ ++ [_] = [_] |- _ ] => apply elt_eq_unit in H; subst
  | [H: _ ++ [_] = _ :: _ ++ [_] |- _ ] => rewrite app_comm_cons in H
  | [H: _ ++ [_] = _ ++ _ ++ [_] |- _ ] =>
    rewrite app_assoc in H;
    apply app_inj_tail in H; subst
end.

Ltac listctx_set_simpl := 
  repeat (first [list_app_simpl_aux1 | listctx_set_simpl_aux | listctx_set_simpl_aux2 ]; auto).

Ltac listctx_set_solver_aux1 :=
  match goal with
    | [|- _ <> _] => fast_set_solver !!
    | [|- _ = _] => fast_set_solver !!
    | [|- _ ∉ _] => fast_set_solver !!
    | [|- _ ∈ _] => fast_set_solver !!
    | [|- _ ⊆ _] => fast_set_solver !!
    | [H: ctxfind (?Γ1 ++ ?Γ3) ?x = Some ?T |- ctxfind (?Γ1 ++ ?Γ2 ++ ?Γ3) ?x = Some ?T ] => apply ctxfind_app_weaken; auto
    | [H: ok (?Γ1 ++ _ :: ?Γ2) |- ok (?Γ1 ++ ?Γ2) ] => apply ok_app_weaken in H; exact H
    | [H: ok (_ ++ (?x, _) :: ?Γ) |- ?x ∉ ctxdom ?Γ ] =>
        apply ok_weak_post in H; rewrite ok_pre_destruct in H; destruct H; auto
    | [H: ok (?a ++ ?b ++ ?c) |- ok ((?a ++ ?b) ++ ?c) ] => rewrite <- app_assoc; exact H
    | [H: ok (?a ++ ?b ++ ?c) |- ok (?a ++ ?b ++ ?c ++ [(?x, _)]) ] =>
        rewrite -> app_assoc; rewrite -> app_assoc; constructor
    | [|- ok ((_, _) :: _) ] => rewrite ok_pre_destruct; split; auto
  end.

Ltac listctx_set_solver1 :=
  listctx_set_simpl; listctx_set_solver_aux1; fast_set_solver !!.

(* Ltac listctx_set_solver1 :=
  repeat (listctx_set_simpl;
          match goal with
          | [|- _ <> _] => fast_set_solver !!
          | [|- _ = _] => fast_set_solver !!
          | [|- _ ∉ _] => fast_set_solver !!
          | [|- _ ∈ _] => fast_set_solver !!
          | [|- _ ⊆ _] => fast_set_solver !!
          | [H: ctxfind (?Γ1 ++ ?Γ3) ?x = Some ?T |- ctxfind (?Γ1 ++ ?Γ2 ++ ?Γ3) ?x = Some ?T ] => apply ctxfind_app_weaken; auto
          | [H: ok (?Γ1 ++ _ :: ?Γ2) |- ok (?Γ1 ++ ?Γ2) ] => apply ok_app_weaken in H; exact H
          | [H: ok (_ ++ (?x, _) :: ?Γ) |- ?x ∉ ctxdom ?Γ ] =>
              apply ok_weak_post in H; rewrite ok_pre_destruct in H; destruct H; auto
          | [H: ok (?a ++ ?b ++ ?c) |- ok ((?a ++ ?b) ++ ?c) ] => rewrite <- app_assoc; exact H
          | [H: ok (?a ++ ?b ++ ?c) |- ok (?a ++ ?b ++ ?c ++ [(?x, _)]) ] =>
              rewrite -> app_assoc; rewrite -> app_assoc; constructor
          | [|- ok ((_, _) :: _) ] => rewrite ok_pre_destruct; split; auto
          end); listctx_set_simpl; fast_set_solver !!. *)

Lemma ctxfind_none_neq_tl {A: Type}: forall (Γ: listctx A) x tx a,
    ctxfind ((x, tx):: Γ) a = None -> ctxfind Γ a = None.
Proof. intros; listctx_set_solver1. Qed.

Lemma ctxfind_weak_pre {A: Type}: forall (Γ1 Γ2 : listctx A) a,
    ctxfind (Γ1 ++ Γ2) a = None ->
    ctxfind Γ1 a = None.
Proof. intros; listctx_set_solver1. Qed.

Lemma ctxfind_weak_post {A: Type}: forall (Γ1  Γ2: listctx A) a,
    ctxfind (Γ1 ++ Γ2) a = None ->
    ctxfind Γ2 a = None.
Proof. intros; listctx_set_solver1. Qed.

Lemma ctxfind_weak_unit {A: Type}: forall x (tau_x: A) a,
    ctxfind ((x, tau_x)::nil) a = None -> a <> x.
Proof. intros; listctx_set_solver1. Qed.

Lemma l_find_implies_in {A:Type}: forall (ctx: listctx A) (x: atom) (t: A),
      ctxfind ctx x = Some t -> In (x, t) ctx.
Proof.
  induction ctx; simpl; intros; listctx_set_simpl; hauto.
Qed.

Lemma ctxfind_some_spec_aux {A:Type}: forall (ctx: list (prod atom A)) (name: atom) (tau: A),
  ctxfind ctx name = Some tau ->
  (exists ctx1 ctx2,
      ctx = ctx1 ++ ((name, tau)::nil) ++ ctx2
  ).
Proof with auto.
  intros.
  apply l_find_implies_in in H. apply in_split in H. destruct H as (G1 & G2 & HG12).
  exists G1, G2. subst. split...
Qed.

Lemma ok_first_not_equal_hd {A:Type}: forall (Γ: list (prod atom A)) (x y: atom) (a b: A),
    ok ((x, a) :: Γ ++ [(y, b)]) -> x <> y.
Proof.
  intros. listctx_set_simpl. listctx_set_solver1.
Qed.

Ltac auto_exfalso_ok :=
  try match goal with
    | [H: ctxfind [] _ = Some _ |- _ ] => inversion H
    | [H: ok (((?x, _) :: ?Γ) ++ [(?x, _)]) |- _ ] =>
        rewrite <- app_comm_cons in H; apply ok_first_not_equal_hd in H; exfalso; auto
    | [H: ok ((?x, _) :: ?Γ ++ [(?x, _)]) |- _ ] =>
        apply ok_first_not_equal_hd in H; exfalso; auto
    end;
  auto_exfalso.

Ltac listctx_set_solver_aux2 :=
  match goal with
  | [H: ok ?Γ |- ok [(?x, _); (?y, _)]] => 
    rewrite <- app_one_is_cons; constructor; auto
  | [H: ok ?Γ |- ok (?Γ ++ [(?x, _); (?y, _)])] => 
    rewrite <- app_one_is_cons in H; rewrite app_assoc in H; constructor; auto
  | [H: ok ?Γ |- ok (?Γ ++ [(?x, _)])] => econstructor; eauto
  end.

Ltac listctx_set_solver2 :=
  listctx_set_simpl;
  repeat (first [listctx_set_solver_aux2 | listctx_set_solver_aux1]; auto);
  (auto_exfalso_ok || fast_set_solver !!).

Lemma ctxfind_last_eq {A:Type}: forall (ctx: list (prod atom A)) name tau,
    ok (ctx ++ [(name, tau)]) ->
    ctxfind (ctx ++ [(name, tau)]) name = Some tau.
Proof with eauto.
  induction ctx; intros; listctx_set_simpl.
  - hauto.
  - simpl. mydestr. set_solver. hauto. 
Qed.

Lemma ctxfind_last_neq_none {A:Type}: forall (ctx: list (prod atom A)) name tau a,
    name <> a ->
    ctxfind (ctx ++ [(name, tau)]) a = None <->
      ctxfind ctx a = None.
Proof. split; intros; listctx_set_solver2. Qed.

Lemma ctxfind_last_neq {A:Type}: forall (ctx: list (prod atom A)) name tau a tau_a,
    ok (ctx ++ [(name, tau)]) ->
    name <> a ->
    ctxfind (ctx ++ [(name, tau)]) a = Some tau_a <->
      ctxfind ctx a = Some tau_a.
Proof.
  intros. induction ctx; listctx_set_simpl; hauto. 
Qed.

Lemma find_none_append {A: Type}: forall Γ a (tau_x: A) x,
    ctxfind Γ a = None ->
    x <> a ->
    ctxfind (Γ ++ ((x,tau_x)::nil)) a = None.
Proof.
  intros. listctx_set_solver2.
Qed.

Lemma ok_single {A: Type}: forall (x: atom) (T: A), ok [(x, T)].
Proof.
  intros.
  rewrite ok_pre_destruct; split; auto; fast_set_solver.
Qed.

Ltac listctx_set_solver_aux3 :=
  match goal with
    | [|- ok [(_, _)]] => apply ok_single
    | [H: ok (_ ++ ?Γ) |- ok ?Γ] => apply ok_weak_post in H; auto
    | [H: ok (?Γ ++ _) |- ok ?Γ] => apply ok_weak_pre in H; auto
    | [|- _ ∉ _ ] => listctx_set_solver2
    | [ |- ok [(_, _); (?x, ?T); (_, _)]] => rewrite <- app_one_is_cons; rewrite <- (app_one_is_cons (x, T)); rewrite app_assoc; constructor; auto
    | [H: ok ?Γ |- ok [(_, _); (?x, ?T); (_, _)]] =>
        rewrite <- app_one_is_cons;
        rewrite app_assoc; rewrite <- (app_one_is_cons (x, T));
        rewrite app_assoc; constructor; auto
    | [H: ok ?Γ |- ok [(?x, _); (?y, _)]] => rewrite <- app_one_is_cons; constructor; auto
    | [|- ok [(_, _)]] => rewrite <- app_nil_l; constructor; auto
    | [|- ok (?Γ ++ [(?x, _)])] => econstructor; eauto
    | [H: ok ?Γ |- ok (?Γ ++ [(?x, _); (?y, _)])] => rewrite <- app_one_is_cons; rewrite app_assoc; constructor; auto
    | [H: ok ?Γ |- ok (?Γ ++ [(_, _); (?x, ?T); (_, _)])] =>
        rewrite <- app_one_is_cons;
        rewrite app_assoc; rewrite <- (app_one_is_cons (x, T));
        rewrite app_assoc; constructor; auto
  end.

Ltac listctx_set_solver3 :=
  listctx_set_simpl;
  repeat (first [listctx_set_solver_aux3; listctx_set_solver_aux2 | listctx_set_solver_aux1]; auto);
  (auto || auto_exfalso_ok || fast_set_solver !!).

Lemma ctxfind_in {A: Type}: forall Γv1 (x: atom) (u: A) Γv2,
    ok (Γv1 ++ (x, u) :: Γv2) ->
    ctxfind (Γv1 ++ (x, u) :: Γv2) x = Some u.
Proof.
  induction Γv1; simpl; intros; mydestr; auto; listctx_set_simpl.
  - hauto.
  - set_solver.
Qed.

Lemma ok_mid_insert {A: Type} : forall Γ1 (x: atom) (T: A) Γ2,
    (x ∉ ctxdom Γ1 ∪ ctxdom Γ2 /\ ok (Γ1 ++ Γ2)) <-> ok (Γ1 ++ (x, T) :: Γ2).
Proof.
  induction Γ1; split; simpl; intros; mydestr; repeat split; auto; try listctx_set_solver3.
  - rewrite ok_pre_destruct. split.
    + apply IHΓ1; repeat split; listctx_set_solver3.
    + listctx_set_solver3.
  - rewrite ok_pre_destruct in H; mydestr. rewrite <- IHΓ1 in H; mydestr. listctx_set_solver3.
Qed.

Lemma ok_app_swap {A: Type} : forall (Γ1: listctx A) Γ2, ok (Γ1 ++ Γ2) <-> ok (Γ2 ++ Γ1).
Proof.
  induction Γ1; split; simpl; intros; mydestr; try listctx_set_solver3.
  - rewrite ok_pre_destruct in H; mydestr. rewrite IHΓ1 in H.
    rewrite <- ok_mid_insert; split; listctx_set_solver3.
  - rewrite <- ok_mid_insert in H; mydestr. rewrite <- IHΓ1 in H0.
    rewrite ok_pre_destruct; split; auto; listctx_set_solver3.
Qed.

Lemma ok_app_swap3 {A: Type} : forall (Γ1: listctx A) Γ2 Γ3, ok (Γ1 ++ Γ2 ++ Γ3) <-> ok (Γ2 ++ Γ1 ++ Γ3).
Proof.
  induction Γ1; split; simpl; intros; mydestr; try listctx_set_solver3; auto.
  - rewrite ok_pre_destruct in H; mydestr. rewrite IHΓ1 in H.
    rewrite <- ok_mid_insert; split; listctx_set_solver3.
  - rewrite <- ok_mid_insert in H; mydestr. rewrite <- IHΓ1 in H0.
    rewrite ok_pre_destruct; split; auto; listctx_set_solver3.
Qed.

Ltac listctx_set_solver_aux5 :=
  match goal with
  | [H: ok (?a ++ ?b) |- ok (?b ++ ?a)] => rewrite ok_app_swap; auto
  | [H: ok (?a ++ ?b ++ ?c) |- ok (?b ++ ?a ++ ?c)] => rewrite ok_app_swap3; auto
  | [H: ok (?Γ1 ++ ?Γ2 ++ ?Γ3) |- ok (?Γ1 ++ ?Γ3)] =>
         rewrite ok_app_swap3 in H; listctx_set_solver3
  end.

Ltac listctx_set_solver5 :=
  listctx_set_simpl;
  repeat (first [listctx_set_solver_aux5; listctx_set_solver_aux3; listctx_set_solver_aux2 | listctx_set_solver_aux1]; auto);
  (auto || auto_exfalso_ok || fast_set_solver !!).

Ltac listctx_set_solver := listctx_set_solver5.

Lemma ok_find_same {A: Type}: forall (a: atom) (τ1 τ2: A) Γ1 Γ2 Γ1' Γ2',
    ok (Γ1 ++ ((a, τ1) :: Γ2)) -> (Γ1 ++ ((a, τ1) :: Γ2)) = (Γ1' ++ (a, τ2) :: Γ2') ->
    Γ1 = Γ1' /\ τ1 = τ2 /\ Γ2 = Γ2'.
Proof.
  intros a τ1 τ2.
  induction Γ1; intros; mydestr; listctx_set_simpl; mydestr; subst; try listctx_set_solver3.
  apply IHΓ1 in H0; auto. mydestr; subst. hauto.
Qed.

Lemma ok_find_neq_head {A: Type}: forall (x a: atom) (τ_x τ_a: A) Γ1' Γ2 Γ2',
    x <> a ->
    ok ((x, τ_x) :: Γ2) -> ((x, τ_x) :: Γ2) = (Γ1' ++ (a, τ_a) :: Γ2') ->
    (exists Γ1'', Γ1' = (x, τ_x) :: Γ1'' /\ Γ2 = (Γ1'' ++ (a, τ_a) :: Γ2')).
Proof.
  intros x a τ_x τ_a Γ1'.
  induction Γ1'; intros; listctx_set_simpl; hauto.
Qed.
