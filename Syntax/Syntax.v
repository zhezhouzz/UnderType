From CT Require Import BaseDef.
From CT.Syntax Require Export Lang Qualifier RefinementType.

Ltac fold_syntax_class :=
  (* Direct syntax functions *)
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
  change (lc_tm ?e) with (lc e) in *;
  change (lc_value ?v) with (lc v) in *;

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
