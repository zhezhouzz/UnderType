From stdpp Require Import stringmap.
From CT Require Import BaseDef ListCtx .
From CT.Syntax Require Export Lang Qualifier RefinementType BasicTyping Instantiation.

Hint Unfold listctx_stale: class_simpl.
(* Hint Unfold env_stale: class_simpl. *)

Ltac fold_syntax_class :=
  (* NOTE:
   Using [change ... in *] with shared evars (the [?Γ ?e ?T] placeholders)
   often fails when there are multiple [value_has_type]/[tm_has_type]
   occurrences with different parameters in the context/goal.
   We instead rewrite each occurrence one-by-one by first pattern-matching to
   bind fresh [Γ e T] for that specific occurrence. *)
  repeat (
    first
      [ progress match goal with
        | H : value_has_type ?Γ ?v ?T |- _ =>
            change (value_has_type Γ v T) with (Γ ⊢ v ⋮ T) in H
        | |- context [value_has_type ?Γ ?v ?T] =>
            change (value_has_type Γ v T) with (Γ ⊢ v ⋮ T)
        end
      | progress match goal with
        | H : tm_has_type ?Γ ?e ?T |- _ =>
            change (tm_has_type Γ e T) with (Γ ⊢ e ⋮ T) in H
        | |- context [tm_has_type ?Γ ?e ?T] =>
            change (tm_has_type Γ e T) with (Γ ⊢ e ⋮ T)
        end
      ]);
  change (subst_tm ?x ?w ?e) with ({x := w} e) in *;
  change (subst_value ?x ?w ?v) with ({x := w} v) in *;
  change (subst_qualifier ?x ?w ?q) with ({x := w} q) in *;
  change (subst_rty ?x ?w ?r) with ({x := w} r) in *;
  change (open_value ?k ?v ?e) with ({k ~> v} e) in *;
  change (open_qualifier ?k ?v ?q) with ({k ~> v} q) in *;
  change (open_rty ?k ?v ?r) with ({k ~> v} r) in *;
  change (open_tm ?k ?v ?e) with ({k ~> v} e) in *;
  change (close_value ?x ?k ?e) with ({k <~ x} e) in *;
  change (close_tm ?x ?k ?e) with ({k <~ x} e) in *;
  change (fv_value ?v) with (stale v) in *;
  change (fv_tm ?e) with (stale e) in *;
  change (fv_qualifier ?q) with (stale q) in *;
  change (fv_rty ?r) with (stale r) in *;
  change (ctxdom ?Γ) with (stale Γ) in *;
  change (dom ?Γ) with (stale Γ) in *;
  change (lc_tm ?e) with (lc e) in *;
  change (lc_value ?v) with (lc v) in *;
  change (lc_qualifier ?q) with (lc q) in *;
  change (lc_rty ?r) with (lc r) in *;

  (* Class instances that may appear after [autounfold with class_simpl] *)
  change (subst_tm_with_value ?x ?w ?e) with ({x := w} e) in *;
  change (subst_value_with_value ?x ?w ?v) with ({x := w} v) in *;
  change (subst_qualifier_with_value ?x ?w ?q) with ({x := w} q) in *;
  change (subst_rty_with_value ?x ?w ?r) with ({x := w} r) in *;
  change (open_value_with_value ?k ?v ?e) with ({k ~> v} e) in *;
  change (open_tm_with_value ?k ?v ?e) with ({k ~> v} e) in *;
  change (open_qualifier_with_value ?k ?v ?q) with ({k ~> v} q) in *;
  change (open_rty_with_value ?k ?v ?r) with ({k ~> v} r) in *;
  change (close_value_instance ?x ?k ?e) with ({k <~ x} e) in *;
  change (close_tm_instance ?x ?k ?e) with ({k <~ x} e) in *.

Ltac my_map_simpl_aux :=
  match goal with
  | [H: context [ ∅ ∪ _ ] |- _ ] => rewrite map_empty_union in H
  | [|- context [ ∅ ∪ _ ] ] => rewrite map_empty_union
  | [H: context [ _ ∪ ∅ ] |- _ ] => rewrite map_union_empty in H
  | [|- context [ _ ∪ ∅ ] ] => rewrite map_union_empty
  end.

Ltac my_map_simpl :=
  repeat my_map_simpl_aux.

Ltac ln_simpl :=
  autounfold with class_simpl in *; simpl in *; MyTactics.mydestr;
  MyTactics.my_set_simpl;
  my_map_simpl;
  listctx_set_simpl;
  simplify_map_eq;
  do 3 fold_syntax_class.