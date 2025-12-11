Lemma subst_commute_qualifier : forall x u_x y u_y ϕ,
    x <> y -> x ∉ fv_value u_y -> y ∉ fv_value u_x ->
    {x := u_x }q ({y := u_y }q ϕ) = {y := u_y }q ({x := u_x }q ϕ).
Proof.
  intros.
  destruct ϕ.
  simpl.
  f_equal.
  rewrite !Vector.map_map.
  apply Vector.map_ext.
  eauto using subst_commute_value.
Qed.

Lemma subst_fresh_qualifier: forall (ϕ: qualifier) (x:atom) (u: value),
    x ∉ (qualifier_fv ϕ) -> {x := u}q ϕ = ϕ.
Proof.
  intros.
  destruct ϕ.
  simpl in *.
  f_equal.
  clear prop.
  induction vals; simpl in *; eauto.
  f_equal.
  apply subst_fresh_value. my_set_solver.
  auto_apply. my_set_solver.
Qed.

Lemma open_fv_qualifier (ϕ : qualifier) (v : value) k :
  qualifier_fv ({k ~q> v} ϕ) ⊆ qualifier_fv ϕ ∪ fv_value v.
Proof.
  destruct ϕ.
  simpl. clear. induction vals; simpl. easy.
  etrans. apply union_mono. apply open_fv_value.
  reflexivity. my_set_solver.
Qed.

Lemma open_fv_qualifier' (ϕ : qualifier) (v : value) k :
  qualifier_fv ϕ ⊆ qualifier_fv ({k ~q> v} ϕ).
Proof.
  intros. destruct ϕ.
  simpl. clear. induction vals; simpl. easy.
  apply union_mono; eauto using open_fv_value'.
Qed.

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

Lemma qualifier_and_open k v q1 q2 :
  {k ~q> v} (q1 & q2) = ({k ~q> v} q1) & ({k ~q> v} q2).
Proof.
  destruct q1, q2. simpl. f_equal.
  (* Need a lemma [map_app] for vector. *)
  clear.
  induction vals; eauto.
  simpl. f_equal. eauto.
Qed.

Lemma qualifier_and_subst x v q1 q2 :
  {x := v}q (q1 & q2) = ({x := v}q q1) & ({x := v}q q2).
Proof.
  destruct q1, q2. simpl. f_equal.
  (* Need a lemma [map_app] for vector. *)
  clear.
  induction vals; eauto.
  simpl. f_equal. eauto.
Qed.

Lemma qualifier_and_fv q1 q2 :
  qualifier_fv (q1 & q2) = qualifier_fv q1 ∪ qualifier_fv q2.
Proof.
  destruct q1, q2. simpl.
  clear.
  induction vals; simpl. my_set_solver.
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
  denote_qualifier (q1 & q2) <-> denote_qualifier q1 /\ denote_qualifier q2.
Proof.
  destruct q1, q2. simpl.
  rewrite denote_vals_app.
  case_split; try qauto.
  case_split; try qauto.
  rewrite Vector.splitat_append. eauto.
Qed.

Lemma open_subst_same_qualifier: forall x y (ϕ : qualifier) k,
    x # ϕ ->
    {x := y }q ({k ~q> x} ϕ) = {k ~q> y} ϕ.
Proof.
  destruct ϕ. cbn. intros.
  f_equal. clear - H.
  (* A better proof should simply reduce to vector facts. Don't bother yet. *)
  induction vals; cbn; eauto.
  cbn in H.
  f_equal. apply open_subst_same_value. my_set_solver.
  apply IHvals. my_set_solver.
Qed.

Lemma subst_open_qualifier: forall (ϕ: qualifier) (x:atom) (u: value) (w: value) (k: nat),
    lc w -> {x := w}q ({k ~q> u} ϕ) = ({k ~q> {x := w}v u} ({x := w}q ϕ)).
Proof.
  destruct ϕ. cbn. intros.
  f_equal.
  rewrite !Vector.map_map.
  apply Vector.map_ext.
  eauto using subst_open_value.
Qed.

Lemma subst_open_qualifier_closed:
  ∀ (ϕ : qualifier) (x : atom) (u w : value) (k : nat),
    closed_value u ->
    lc w → {x := w }q ({k ~q> u} ϕ) = {k ~q> u} ({x := w }q ϕ).
Proof.
  intros. rewrite subst_open_qualifier; auto.
  rewrite (subst_fresh_value); eauto. set_solver.
Qed.

Lemma subst_lc_qualifier : forall x (u: value) (ϕ: qualifier),
    lc_qualifier ϕ -> lc u -> lc_qualifier ({x := u}q ϕ).
Proof.
  destruct 1. intros Hu.
  econstructor.
  srewrite Vector.to_list_Forall.
  rewrite Vector.to_list_map.
  rewrite Forall_map.
  eapply Forall_impl; eauto.
  simpl. eauto using subst_lc_value.
Qed.

Lemma subst_open_var_qualifier: forall x y (u: value) (ϕ: qualifier) (k: nat),
    x <> y -> lc u -> {x := u}q ({k ~q> y} ϕ) = ({k ~q> y} ({x := u}q ϕ)).
Proof.
  intros.
  rewrite subst_open_qualifier; auto. simpl. rewrite decide_False; auto.
Qed.

Lemma fv_of_subst_qualifier_closed:
  forall x (u : value) (ϕ: qualifier),
    closed_value u ->
    qualifier_fv ({x := u }q ϕ) = qualifier_fv ϕ ∖ {[x]}.
Proof.
  destruct ϕ; simpl. clear. induction vals; simpl; intros.
  my_set_solver.
  rewrite fv_of_subst_value_closed by eauto.
  my_set_solver.
Qed.

Lemma open_not_in_eq_qualifier (x : atom) (ϕ : qualifier) k :
  x # {k ~q> x} ϕ ->
  forall e, ϕ = {k ~q> e} ϕ.
Proof.
  destruct ϕ. simpl. intros.
  f_equal.
  clear - H.
  induction vals; simpl; eauto.
  f_equal. apply open_not_in_eq_value with x. my_set_solver.
  auto_apply. my_set_solver.
Qed.

Lemma lc_subst_qualifier:
  forall x (u: value) (ϕ: qualifier), lc_qualifier ({x := u}q ϕ) -> lc u -> lc_qualifier ϕ.
Proof.
  intros.
  sinvert H.
  destruct ϕ. simpl in *. simplify_eq.
  econstructor.
  srewrite Vector.to_list_Forall.
  srewrite Vector.to_list_map.
  srewrite Forall_map.
  eapply Forall_impl; eauto.
  simpl. eauto using lc_subst_value.
Qed.

Lemma open_rec_lc_qualifier: forall (v: value) (ϕ: qualifier) (k: nat),
    lc_qualifier ϕ -> {k ~q> v} ϕ = ϕ.
Proof.
  destruct 1. simpl. f_equal.
  rewrite <- Vector.map_id.
  apply Vector.map_ext_in.
  rewrite Vector.Forall_forall in H.
  eauto using open_rec_lc_value.
Qed.

Lemma open_qualifier_idemp: forall u (v: value) (ϕ: qualifier) (k: nat),
    lc v ->
    {k ~q> u} ({k ~q> v} ϕ) = ({k ~q> v} ϕ).
Proof.
  destruct ϕ; intros. simpl.
  f_equal.
  rewrite Vector.map_map.
  apply Vector.map_ext_in.
  eauto using open_value_idemp.
Qed.

Lemma subst_intro_qualifier: forall (ϕ: qualifier) (x:atom) (w: value) (k: nat),
    x # ϕ ->
    lc w -> {x := w}q ({k ~q> x} ϕ) = ({k ~q> w} ϕ).
Proof.
  intros.
  specialize (subst_open_qualifier ϕ x x w k) as J.
  simpl in J. rewrite decide_True in J; auto.
  rewrite J; auto. rewrite subst_fresh_qualifier; auto.
Qed.

Lemma open_lc_qualifier: forall (u: value) (ϕ: qualifier),
    (* don't body defining body yet. *)
    (exists L : aset, forall x : atom, x ∉ L -> lc_qualifier (ϕ ^q^ x)) ->
    lc u ->
    lc_qualifier ({0 ~q> u} ϕ).
Proof.
  intros. destruct H.
  let acc := collect_stales tt in pose acc.
  pose (Atom.fv_of_set a).
  assert (a0 ∉ a). apply Atom.fv_of_set_fresh.
  erewrite <- subst_intro_qualifier; auto. instantiate (1:= a0).
  apply subst_lc_qualifier; auto. apply H.
  my_set_solver. my_set_solver.
Qed.

Lemma open_swap_qualifier: forall (ϕ: qualifier) i j (u v: value),
    lc u ->
    lc v ->
    i <> j ->
    {i ~q> v} ({j ~q> u} ϕ) = {j ~q> u} ({i ~q> v} ϕ).
Proof.
  destruct ϕ. intros. simpl.
  f_equal. rewrite !Vector.map_map.
  apply Vector.map_ext.
  eauto using open_swap_value.
Qed.

Lemma open_lc_respect_qualifier: forall (ϕ: qualifier) (u v : value) k,
    lc_qualifier ({k ~q> u} ϕ) ->
    lc u ->
    lc v ->
    lc_qualifier ({k ~q> v} ϕ).
Proof.
  intros. sinvert H.
  destruct ϕ. simpl in *. simplify_eq.
  econstructor.
  srewrite Vector.to_list_Forall.
  rewrite Vector.to_list_map in *.
  rewrite Forall_map in *.
  eapply Forall_impl; eauto.
  simpl. eauto using open_lc_respect_value.
Qed.

Arguments qualifier_and : simpl never.

Lemma subst_lc_phi1 : forall x (u: value) (ϕ: qualifier),
    lc_phi1 ϕ -> lc u -> lc_phi1 ({x := u}q ϕ).
Proof.
  unfold lc_phi1.
  destruct 1. intros Hu.
  auto_exists_L. intros y Hy.
  specialize_with y.
  rewrite <- !subst_open_var_qualifier by (eauto; my_set_solver).
  eauto using subst_lc_qualifier.
Qed.

Lemma subst_lc_phi2 : forall x (u: value) (ϕ: qualifier),
    lc_phi2 ϕ -> lc u -> lc_phi2 ({x := u}q ϕ).
Proof.
  unfold lc_phi2.
  destruct 1. intros Hu.
  auto_exists_L. intros y1 Hy1 y2 Hy2.
  specialize_with y1.
  specialize_with y2.
  rewrite <- !subst_open_var_qualifier by (eauto; my_set_solver).
  eauto using subst_lc_qualifier.
Qed.

Lemma lc_subst_phi1 : forall x (u: value) (ϕ: qualifier),
    lc_phi1 ({x := u}q ϕ) -> lc u -> lc_phi1 ϕ.
Proof.
  unfold lc_phi1.
  destruct 1. intros Hu.
  auto_exists_L. intros y Hy.
  specialize_with y.
  eapply lc_subst_qualifier; eauto.
  rewrite -> !subst_open_var_qualifier; eauto. my_set_solver.
Qed.

Lemma lc_subst_phi2 : forall x (u: value) (ϕ: qualifier),
    lc_phi2 ({x := u}q ϕ) -> lc u -> lc_phi2 ϕ.
Proof.
  unfold lc_phi2.
  destruct 1. intros Hu.
  auto_exists_L. intros y1 Hy1 y2 Hy2.
  specialize_with y1.
  specialize_with y2.
  eapply lc_subst_qualifier; eauto.
  rewrite -> !subst_open_var_qualifier; eauto; my_set_solver.
Qed.

Lemma lc_phi1_and ϕ1 ϕ2:
  lc_phi1 ϕ1 -> lc_phi1 ϕ2 -> lc_phi1 (ϕ1 & ϕ2).
Proof.
  intros. unfold lc_phi1 in *. simp_hyps.
  auto_exists_L. intros y1 Hy1.
  specialize_with y1. specialize_with y1.
  rewrite qualifier_and_open.
  eauto using lc_qualifier_and.
Qed.

Lemma lc_phi2_and ϕ1 ϕ2:
  lc_phi2 ϕ1 -> lc_phi2 ϕ2 -> lc_phi2 (ϕ1 & ϕ2).
Proof.
  intros. unfold lc_phi2 in *. simp_hyps.
  auto_exists_L. intros y1 Hy1 y2 Hy2.
  specialize_with y1. specialize_with y2.
  specialize_with y1. specialize_with y2.
  rewrite qualifier_and_open. rewrite qualifier_and_open.
  eauto using lc_qualifier_and.
Qed.

Lemma lc_phi1_body: ∀ n vals prop,
    lc_phi1 (@qual n vals prop) -> Vector.Forall (fun v => body (treturn v)) vals.
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
    lc_phi2 (@qual n vals prop) ->
    Vector.Forall (fun v =>
                     exists (L : aset), (forall (x : atom), x ∉ L -> forall (y : atom), y ∉ L -> lc ({0 ~v> y} ({1 ~v> x} v)))) vals.
Proof.
  intros. subst. sinvert H.
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

Lemma fact1_value_twice: forall (u v1 v2: value) (e: value) i j1 j2,
    i <> j1 -> i <> j2 -> j1 <> j2 ->
    {i ~v> u} ({j1 ~v> v1} ({j2 ~v> v2} e)) = {j1 ~v> v1} ({j2 ~v> v2} e) -> {i ~v> u} e = e.
Proof.
  intros.
  assert ({i ~v> u} ({j2 ~v> v2} e) = {j2 ~v> v2} e).
  apply fact1_value with (j := j1) (v:= v1); eauto.
  apply fact1_value with (j := j2) (v:= v2); eauto.
Qed.

Lemma fact1_qualifier: forall (u v: value) (ϕ: qualifier) i j,
    i <> j -> {i ~q> u} ({j ~q> v} ϕ) = {j ~q> v} ϕ -> {i ~q> u} ϕ = ϕ.
Proof.
  intros.
  destruct ϕ. simpl. f_equal.
  rewrite <- Vector.map_id.
  apply Vector.map_ext_in.
  simpl in H0. sinvert H0.
  apply Classical_Prop.EqdepTheory.inj_pair2 in H2.
  rewrite Vector.map_map in H2.
  intros.
  eapply vector_map_ext_in' in H2; eauto.
  pose fact1_value; eauto.
Qed.

Lemma fact1_qualifier_twice: forall (u v1 v2: value) (ϕ: qualifier) i j1 j2,
    i <> j1 -> i <> j2 -> j1 <> j2 ->
    {i ~q> u} ({j1 ~q> v1} ({j2 ~q> v2} ϕ)) = {j1 ~q> v1} ({j2 ~q> v2} ϕ) -> {i ~q> u} ϕ = ϕ.
Proof.
  intros.
  assert ({i ~q> u} ({j2 ~q> v2} ϕ) = {j2 ~q> v2} ϕ).
  apply fact1_qualifier with (j := j1) (v:= v1); eauto.
  apply fact1_qualifier with (j := j2) (v:= v2); eauto.
Qed.

Lemma open_rec_lc_phi1: ∀ (u : value) ϕ (k : nat), lc_phi1 ϕ -> {S k ~q> u} ϕ = ϕ.
Proof.
  intros. destruct ϕ. apply lc_phi1_body in H.
  simpl. f_equal.
  rewrite <- Vector.map_id.
  apply Vector.map_ext_in.
  intros.
  rewrite Vector.Forall_forall in H.
  ospecialize * H; eauto.
  destruct H.
  auto_pose_fv y.
  apply fact1_value with (j := 0) (v:= y). lia.
  rewrite open_rec_lc_value; eauto. apply H. my_set_solver.
Qed.

(* NOTE: Very very annoying, when qualifier has builtin 1 or 2 arguments. *)
Lemma open_rec_lc_phi2: ∀ (u : value) ϕ (k : nat), lc_phi2 ϕ -> {S (S k) ~q> u} ϕ = ϕ.
Proof.
  intros. destruct ϕ. apply lc_phi2_body in H.
  simpl. f_equal.
  rewrite <- Vector.map_id.
  apply Vector.map_ext_in.
  intros.
  rewrite Vector.Forall_forall in H.
  ospecialize * H; eauto.
  destruct H.
  auto_pose_fv y1. auto_pose_fv y2.
  ospecialize * (H y1 _ y2); eauto. my_set_solver. my_set_solver.
  eapply (fact1_value_twice _ y1 y2 _ _ 0 1); eauto.
  rewrite open_rec_lc_value; eauto.
Qed.
