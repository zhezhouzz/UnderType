From CT.LocallyNameless Require Export FineRty LangLc QualifierLc RtyLc InstantiationLc.

Import BaseDef MyTactics Primitives Lang LangLc Syntax.

(* There are some more lemmas for better lc solver. *)

Lemma body_abs_iff_body2: forall T e, body (vlam T e) <-> body2 e.
Proof.
  split; unfold body; unfold body2; intros.
  - mydestr. 
    auto_exists_L. intros y Hy. specialize_with y.
    intros z Hz.
    ln_simpl; eauto.
    rewrite -> lc_abs_iff_body in H; eauto.
    apply open_lc; eauto. lc_solver1.
  - mydestr.
    auto_exists_L; intros y Hy. specialize_with y.
    ln_simpl; eauto.
    rewrite -> lc_abs_iff_body; eauto.
    auto_exists_L; eauto.
Qed.

Class OpenBody A `{Stale A} `{Open value A} `{Lc A} := open_body :
forall (e: A) (u: value), body2 e -> lc u -> body ({1 ~> u} e).

Lemma OpenBody_all
  (A : Type)
  (staleA : Stale A)
  (openA  : Open value A)
  (substA : Subst value A)
  (lcA    : Lc A)
  (substIntroA : @SubstIntro A staleA openA substA lcA)
  (substBodyA    : @SubstBody A staleA openA substA lcA)
  : @OpenBody A staleA openA lcA.
Proof.
  intros e u Hbody Hlc. destruct Hbody as [L Hbody].
  pose_fresh_fv y. specialize_with y.
  erewrite <- subst_intro; auto. instantiate (1:= y).
  eapply subst_body; eauto. 
  auto_exists_L; intros z Hz. my_set_solver.
Qed.

#[global] Instance OpenBody_tm : OpenBody tm.
Proof. apply OpenBody_all with (staleA := stale) (openA := open) (substA := subst) (lcA := lc); typeclasses eauto. Qed.
Arguments OpenBody_tm /.

#[global] Instance OpenBody_value : OpenBody value.
Proof. apply OpenBody_all with (staleA := stale) (openA := open) (substA := subst) (lcA := lc); typeclasses eauto. Qed.
Arguments OpenBody_value /.

Lemma ok_ctx_destruct_tail : forall Γ (x: atom) (t: rty), ok_ctx (Γ ++ [(x, t)]) ->
lc t /\ stale t ⊆ stale Γ /\ x # Γ /\ ok_ctx Γ.
Proof.
  intros. invclear H; eauto.
  - ListCtx.listctx_set_solver.
  - repeat split; eauto; ListCtx.listctx_set_simpl.
Qed.

Ltac ok_solver_aux :=
  match goal with
  | [H: ok_ctx (?Γ ++ [(?x, ?t)]) |- ?G ] => 
    match G with
    | [lc _] => apply ok_ctx_destruct_tail in H; destruct H; auto
    | [_ ⊆ _] => apply ok_ctx_destruct_tail in H; destruct H; auto
    | [_ # _] => apply ok_ctx_destruct_tail in H; destruct H; auto
    | [ok_ctx _] => apply ok_ctx_destruct_tail in H; destruct H; auto
    end
  | [H: ok_ctx ?Γ |- ok_ctx (?Γ ++ [(_, _)]) ] => econstructor; eauto
  end.

Ltac ok_solver :=
  repeat (ok_solver_aux || ListCtx.listctx_set_solver).

Ltac lc_solver_aux2 :=
  match goal with
  | [H: lc ?e |- body ?e] => apply lc_implies_body; auto
  | [H: body (vlam _ _) |- _ ] => rewrite body_abs_iff_body2 in H; mydestr; auto
  | [H: body2 ?e |- body (vlam _ ?e) ] => rewrite body_abs_iff_body2; auto
  | [H: body2 ?e |- body ({1 ~> ?u} ?e) ] => apply open_body; auto
  | _ => lc_solver_aux1
  end.

Ltac lc_solver:= 
autounfold with class_simpl; simpl; mydestr; auto; fold_syntax_class;
repeat (lc_solver_aux2; auto); fold_syntax_class.