From CT Require Import BaseDef.
From stdpp Require Export prelude fin_maps fin_map_dom.
From Hammer Require Export Tactics.

Import BaseDef.

(** * Some tactics in the file is inspired by OADT: https://github.com/ccyip/oadt *)
(** * Fold over hypotheses *)

Ltac revert_all :=
  repeat match goal with
         | H : _ |- _ => revert H
         end.

(** This cool trick to fold over hypotheses is inspired by
https://sympa.inria.fr/sympa/arc/coq-club/2014-12/msg00034.html *)
Ltac get_hyps :=
  constr:(ltac:(revert_all; constructor) : True).

(** Run [tac] on each hypothesis. *)
Tactic Notation "do_hyps" tactic3(tac) :=
  let hs := get_hyps in
  let rec go hs :=
      lazymatch hs with
      | ?hs ?H => tac H; go hs
      | _ => idtac
      end in
  go hs.

(** Run [tac] on each hypothesis matching [pat]. *)
Tactic Notation "select" "!" open_constr(pat) tactic3(tac) :=
  let T := lazymatch goal with
           | H : pat |- _ => type of H
           end in
  do_hyps (fun H => lazymatch type of H with
                  | pat => tac H
                  | _ => idtac
                  end);
  (* Clear the shelved. *)
  unify T pat.

(** Fold over hypotheses and return the [constr] result. Run [tac] on each
hypothesis with the accumulator. [acc] is the initial accumulator. *)
Ltac fold_hyps acc tac :=
  let hs := get_hyps in
  let rec go hs acc :=
      lazymatch hs with
      | ?hs ?H => let acc' := tac H acc in go hs acc'
      | _ => acc
      end in
  go hs acc.

(** Fold over hypotheses with continuation. [acc] and [tac] are the same as in
[fold_hyps_nok]. [ktac] is the continuation run on the final result. *)
Tactic Notation "fold_hyps_cont" constr(acc) tactic3(tac) tactic3(ktac) :=
  let x := fold_hyps acc tac in
  ktac x.

(** * General purpose tactics  *)

(** Check [a] contains [pat]. *)
Tactic Notation "contains" constr(a) open_constr(pat) :=
  lazymatch a with
  | context g [pat] => let a' := context g [pat] in
                       unify a a'
  end.

(** Check goal matches pattern [pat]. *)
Tactic Notation "goal_is" open_constr(pat) :=
  lazymatch goal with
  | |- pat => lazymatch goal with
              | |- ?T => unify T pat
              end
  end.

(** Check goal contains [pat]. *)
Tactic Notation "goal_contains" open_constr(pat) :=
  lazymatch goal with
  | |- ?T => contains T pat
  end.

(** Intros until the first variable of type [T]. *)
Ltac intros_until T :=
  match goal with
  | [ |- forall (x : ?A), _ ] =>
      tryif unify A T then idtac else (let H := fresh x in intro H; intros_until T)
  | _ => idtac
  end.

Ltac higher_order_reflexivity :=
  match goal with
  | |- (?f ?a) = ?b =>
    match eval pattern a in b with
    | ?f' _ => unify f f'; reflexivity
    end
  end.

(** Substitute [s] for subterm [t] in term [T]. *)
Ltac subst_pattern T t s :=
  match eval pattern t in T with
  | ?f _ => let T' := eval cbv beta in (f s) in T'
  end.

(** ** Set solving *)

(** Much faster set solving tactic, with less solving strength. *)
Tactic Notation "fast_set_solver" :=
  solve [try fast_done; repeat (set_unfold; subst; intuition)].

(** Faster set solving tactic. Stronger than [fast_set_solver], but also
slower. *)
Tactic Notation "fast_set_solver" "*" :=
  try fast_done; set_unfold; set_unfold; firstorder; auto.

Ltac set_fold_not :=
  change (?x ∈ ?v -> False) with (x ∉ v) in *;
  change (?x = ?v -> False) with (x <> v) in *.

(** Pruning the hypotheses before set solving can _dramatically_ improve
performance. The following pruning tactics are based on heuristics, and they can
make the goal unprovable. While they are unsound, they still work fine in our
cases. A better approach is probably similar to finding a transitive closure of
hypotheses against some "potentially needed" criteria. *)

(** This pruning tactic is conservative, hence the name "safe". However, it can
still make the goal unprovable. For example, it does not consider, say, that the
set relations may appear in a conjunction. *)
(* TODO: is there a way to check if the conclusion of a hypothesis has certain
"head"? I am using [context [_ -> _]] for now, which has some false
negatives. *)
Ltac set_prune_hyps_safe :=
  simpl;
  set_fold_not;
  repeat
    match goal with
    | H : ?T |- _ =>
      lazymatch T with
      | _ ⊆ _ => fail
      | _ ≡ ∅ => rewrite H in *; clear H
      | _ ≡ _ => fail
      | _ ∈ _ => fail
      | _ ∉ _ => fail
      | _ <> _ => fail
      | context [_ -> _ ⊆ _] => fail
      | context [_ -> _ ≡ _] => fail
      | context [_ -> _ ∈ _] => fail
      | context [_ -> _ ∉ _] => fail
      | context [_ -> _ <> _] => fail
      | _ => clear H
      end
    end;
  repeat
    match goal with
    | H : _ ∉ {[_]} |- _ => apply not_elem_of_singleton_1 in H
    end;
  (* Clear a subset relation if it is subsumed by another hypothesis. This
  simple heuristic can result in ~50x faster set solving in some cases. *)
  repeat
    match goal with
    | H : ?S ⊆ ?U, H' : ?S ⊆ ?V |- _ =>
      let rec go U :=
          lazymatch U with
          | ?U1 ∪ ?U2 => go U1; go U2
          | _ =>
            lazymatch V with
            | context [U] => idtac
            end
          end in go U; clear H'
    end.

(** [set_hyp_filter] filters a hypothesis in continuation style, so we can
thread a few filters. *)
Tactic Notation "set_hyp_filter" constr(T) ">>=" tactic3(tac) :=
  lazymatch T with
  | _ ⊆ _ => fail
  | _ ≡ _ => fail
  | context [_ -> _ ⊆ _] => fail
  | context [_ -> _ ≡ _] => fail
  | _ => tac T
  end.

Tactic Notation "set_hyp_filter" constr(T) constr(x) ">>=" tactic3(tac) :=
  lazymatch T with
  | context [x] =>
    lazymatch T with
    | _ ∈ _ => fail
    | _ ∉ _ => fail
    | _ <> _ => fail
    | context [_ -> _ ∈ _] => fail
    | context [_ -> _ ∉ _] => fail
    | context [_ -> _ <> _] => fail
    | _ => tac T
    end
  | _ => tac T
  end.

(** This pruning tactic is more radical. It is more likely to destroy the
goal, but it also offers better performance in certain cases. *)
Ltac set_prune_hyps :=
  set_prune_hyps_safe;
  try
    lazymatch goal with
    | |- _ ⊆ _ =>
      repeat
        match goal with
        | H : ?T |- _ =>
          set_hyp_filter T >>= (fun _ => clear H)
        end
    | |- ?y ∉ _ =>
      repeat
        match goal with
        | H : ?T |- _ =>
          set_hyp_filter T >>= (fun T =>
            set_hyp_filter T y >>= (fun _ => clear H))
        end
    | |- ?x <> ?y =>
      repeat
        match goal with
        | H : ?T |- _ =>
          set_hyp_filter T >>= (fun T =>
            set_hyp_filter T x >>= (fun T =>
              set_hyp_filter T y >>= (fun _ => clear H)))
        end
    end.

Tactic Notation "set_solver" "!" :=
  set_prune_hyps_safe; set_solver.
Tactic Notation "set_solver" "!!" :=
  set_prune_hyps; set_solver.

Tactic Notation "fast_set_solver" "!" :=
  set_prune_hyps_safe; fast_set_solver.
Tactic Notation "fast_set_solver" "!!" :=
  set_prune_hyps; fast_set_solver.

Tactic Notation "fast_set_solver" "*" "!" :=
  set_prune_hyps_safe; fast_set_solver*.
Tactic Notation "fast_set_solver" "*" "!!" :=
  set_prune_hyps; fast_set_solver*.

(** ** Forward reasoning *)

(** Duplicate hypothesis [H] and continue with [tac]. *)
Tactic Notation "dup_hyp" hyp(H) tactic3(tac) :=
  let H' := fresh "H" in
  pose proof H as H'; tac H'.

(** Check if [p] is not in the hypothesis context. *)
Ltac no_hyp p :=
  match type of p with
  | ?T =>
    lazymatch goal with
    | H : T |- _ => fail "hypothesis exists"
    | _ => idtac
    end
  end.

(** Add hypothesis [p] if it is not in the context already. *)
Ltac add_hyp p := no_hyp p; pose proof p.

(** Check if there is another hypothesis that is the same as [H]. *)
Ltac exists_same_hyp H :=
  match type of H with
  | ?X =>
    match goal with
    | H' : X |- _ =>
      lazymatch H with
      | H' => fail
      | _ => idtac
      end
    end
  end.

(** Check if [H] is unique in the context. *)
Ltac uniq_hyp H :=
  tryif exists_same_hyp H then fail "hypothesis is not unique" else idtac.

(** Blocking and unblocking hypotheses. They are used as markers. *)
Ltac block_hyp H :=
  match type of H with
  | ?T => change (block T) in H
  end.
Ltac unblock_hyp H := unfold block in H.
Ltac unblock_hyps := unfold block in *.
Ltac clear_blocked := try select! (block _) (fun H => clear H).
Ltac not_blocked_hyp H :=
  lazymatch type of H with
  | block _ => fail
  | _ => idtac
  end.

(** [dup_hyp!] tactics allow we to implement forward reasoning tactics a la
saturation. Currently, our saturation is naive, ad-hoc and quite fragile. It
also requires a few boilerplates. *)
(** Duplicate [H] and continue with [tac]. We check if [tac] produces something
that is already in the context, and fail in this case to avoid divergence. This
tactic also continues with [ktac] after checking, in case [ktac] destroys the
hypothesis completely, e.g., by [destruct]. We use blocking to mark a hypothesis
has been produced before, and we need to clear the blocked hypotheses after
saturation. It would be better if we can create and access another global
context in ltac, so we can thread a few tactics together without messing with
the hypothesis context. *)
Tactic Notation "dup_hyp" "!" hyp(H) tactic3(tac) "with" tactic3(ktac) :=
  dup_hyp H (fun H => tac H;
                    dup_hyp H (fun H => block_hyp H; uniq_hyp H);
                    ktac H).

Tactic Notation "dup_hyp" "!" hyp(H) tactic3(tac) :=
  dup_hyp! H tac with (fun _ => idtac).

(** ** Hypothesis application *)

Ltac curry_tac f p :=
  let rec go p :=
      lazymatch p with
      | (?a, ?p) =>
        curry_tac (f a) p
      | tt => f
      end in go p.

(** [apply_eq] applies hypothesis [H], and generates equality subgoals for the
arguments if the arguments can not be unified. Note that this tactic only
generates equality subgoals from the last argument to the first argument that
can not be substituted, most likely due to dependent type. *)
Tactic Notation "apply_eq" uconstr(H) "by" tactic3(tac) :=
  let rec go R p :=
      match R with
      | ?R ?a =>
          let e := fresh "e" in
          let f := constr:(fun e =>
                             ltac:(let g := curry_tac (R e) p in
                                   exact g)) in
          let T := type of a in
          let a := mk_evar T in
          refine (eq_ind a f _ _ _); [ go R constr:((a, p)) | ]
      | _ => idtac
      end in
    match goal with
    | |- ?T => go T constr:(tt)
    end; [ tac H | .. ]; try reflexivity.

Tactic Notation "apply_eq" uconstr(H) := apply_eq H by (fun H => apply H).
Tactic Notation "eapply_eq" uconstr(H) := apply_eq H by (fun H => eapply H).

(** [auto_apply] applies the first appliable hypothesis of the same shape. It is
useful for applying induction hypotheses automatically. *)
Tactic Notation "auto_apply" "by" tactic3(tac) :=
  try eassumption;
  match goal with
  | H : context [_ -> ?C] |- ?C => tac H
  | H : context [_ -> ?C _] |- ?C _ => tac H
  | H : context [_ -> ?C _ _] |- ?C _ _ => tac H
  | H : context [_ -> ?C _ _ _] |- ?C _ _ _ => tac H
  | H : context [_ -> ?C _ _ _ _] |- ?C _ _ _ _ => tac H
  | H : context [_ -> ?C _ _ _ _ _] |- ?C _ _ _ _ _ => tac H
  | H : context [_ -> ?C _ _ _ _ _ _] |- ?C _ _ _ _ _ _ => tac H
  | H : context [_ -> ?C _ _ _ _ _ _ _] |- ?C _ _ _ _ _ _ _ => tac H
  end.

Tactic Notation "auto_apply" := auto_apply by (fun H => apply H).
Tactic Notation "auto_eapply" := auto_apply by (fun H => eapply H).
Tactic Notation "auto_apply_eq" := auto_apply by (fun H => apply_eq H).
Tactic Notation "auto_eapply_eq" := auto_apply by (fun H => eapply_eq H).

(** ** General solvers *)

Tactic Notation "equiv_naive_solver" "by" tactic3(tac) :=
  solve [ reflexivity
        | tac
        | symmetry; tac
        | etrans; solve [tac | symmetry; tac] ].

Ltac equiv_naive_solver :=
  equiv_naive_solver by eauto.

#[export]
Hint Extern 1 (_ ≡ _) => equiv_naive_solver : equiv_naive_solver.

Ltac destruct_hyp_conj :=
  match goal with
  | [H: ?P /\ ?Q |- _ ] =>
      destruct H; repeat match goal with
                    | [ H' : P /\ Q |- _ ] => clear H'
                    end
  | [H: atom * _ |- _ ] => destruct H
  | [ H: ex _ |- _ ] => destruct H
  | [H: context [decide (?a = ?b) ] |- _ ] => destruct (decide (a = b)); subst
  | [|- context [decide (?a = ?b) ] ] => destruct (decide (a = b)); subst
  end.

Ltac destruct_hyp_disj :=
  repeat (simpl in *; match goal with
    | [H: _ \/ _ |- _ ] => destruct H
    end).

Ltac mydestr := repeat destruct_hyp_conj.

Ltac invclear H := inversion H; subst; clear H.

Lemma setunion_cons_cons: forall (x: atom) (s1 s2: aset), {[x]} ∪ s1 ∪ ({[x]} ∪ s2) = ({[x]} ∪ s1 ∪ s2).
Proof. fast_set_solver. Qed.

Lemma setunion_empty_left: forall (s: aset), ∅ ∪ s = s.
Proof. fast_set_solver. Qed.

Lemma setunion_empty_right: forall (s: aset), s ∪ ∅ = s.
Proof. fast_set_solver. Qed.

Lemma subseteq_substract_both: forall (x: atom) (s1 s2: aset), x ∉ s1 -> x ∉ s2 -> {[x]} ∪ s1 ⊆ {[x]} ∪ s2 -> s1 ⊆ s2.
Proof.
  intros.
  apply (difference_mono _ _ {[x]} {[x]}) in H1; auto.
  repeat rewrite difference_union_distr_l in H1.
  repeat rewrite difference_diag in H1.
  repeat rewrite setunion_empty_left in H1.
  rewrite difference_disjoint in H1.
  rewrite difference_disjoint in H1; fast_set_solver.
  fast_set_solver.
Qed.

Lemma setunion_cons_right: forall x (s2: aset), (s2 ∪ ({[x]} ∪ ∅)) = ({[x]} ∪ s2).
Proof. fast_set_solver. Qed.

Ltac mmy_set_simpl1 :=
  (repeat match goal with
     | [H: context [({[?x]} ∪ ?s ∪ ({[?x]} ∪ _))] |- _] => rewrite (setunion_cons_cons x s _) in H
     | [H: context [(?s2 ∪ ({[?x]} ∪ ∅))] |- _ ] => setoid_rewrite (setunion_cons_right x s2) in H
     end).

Lemma subseteq_substract_both': forall (x: atom) (s1 s2: aset), x ∉ s1 -> x ∉ s2 -> {[x]} ∪ s1 ⊆ s2 ∪ ({[x]} ∪ ∅) -> s1 ⊆ s2.
Proof.
  intros. mmy_set_simpl1.
  apply subseteq_substract_both in H1; auto.
Qed.

Ltac mmy_set_solver1 :=
  mmy_set_simpl1;
  match goal with
  | [H: ?s1 ∪ ?s2 ∪ ?s3 ⊆ ?s4 ∪ ?s5 ∪ ?s6 |- ?s1 ∪ (?s2 ∪ ?s3) ⊆ ?s4 ∪ (?s5 ∪ ?s6)] =>
      assert (forall (ss1 ss2 ss3: aset), ss1 ∪ (ss2 ∪ ss3) = (ss1 ∪ ss2 ∪ ss3)) as Htmp by fast_set_solver;
      do 2 rewrite Htmp; try clear Htmp; exact H
  | [H: {[?x]} ∪ ?s1 ⊆ {[?x]} ∪ ?s2 |- ?s1 ⊆ ?s2] => apply (subseteq_substract_both x); auto; fast_set_solver
  end.

Lemma setunion_mono_cons: forall (x: atom) (s1 s2 s3 s4: aset),
    {[x]} ∪ s1 ⊆ {[x]} ∪ s2 -> {[x]} ∪ s3 ⊆ {[x]} ∪ s4 -> {[x]} ∪ (s1 ∪ s3) ⊆ {[x]} ∪ (s2 ∪ s4).
Proof.
  intros.
  apply (union_mono ({[x]} ∪ s1) ({[x]} ∪ s2) ({[x]} ∪ s3) ({[x]} ∪ s4)) in H; auto.
   mmy_set_solver1.
Qed.

Ltac mmy_set_solver2 :=
  mmy_set_simpl1;
  match goal with
  | [ |- {[?x]} ∪ (?s1 ∪ ?s3) ⊆ {[?x]} ∪ (?s2 ∪ ?s4)] => apply setunion_mono_cons; auto
  | [H: ?s1 ∪ ?s2 ∪ ?s3 ⊆ ?s4 ∪ ?s5 ∪ ?s6 |- ?s1 ∪ (?s2 ∪ ?s3) ⊆ ?s4 ∪ (?s5 ∪ ?s6)] =>
      assert (forall (ss1 ss2 ss3: aset), ss1 ∪ (ss2 ∪ ss3) = (ss1 ∪ ss2 ∪ ss3)) as Htmp by fast_set_solver;
      do 2 rewrite Htmp; try clear Htmp; exact H
  end.

Ltac my_set_simpl_aux :=
  match goal with
  | [ |- _ !! _ = None ] => rewrite <- not_elem_of_dom
  | [H: context [∅ ∪ ?d] |- _ ] =>
      setoid_rewrite setunion_empty_left in H
  | [ |- context [∅ ∪ ?d] ] =>
      setoid_rewrite setunion_empty_left
  | [H: context [ ?s ∪ ∅ ] |- _ ] =>
      setoid_rewrite setunion_empty_right in H
  | [ |- context [ ?s ∪ ∅ ] ] =>
      setoid_rewrite setunion_empty_right
  end.

Ltac my_set_simpl :=
  repeat my_set_simpl_aux.

Ltac my_set_solver :=
my_set_simpl; eauto;
    (mmy_set_solver2 || fast_set_solver!! || set_solver).

(* Locally Nameless Tactics *)

Ltac collect_one_stale e acc :=
  match goal with
  | _ =>
      lazymatch acc with
      | tt => constr:(stale e)
      | _ => constr:(acc ∪ stale e)
      end
  | _ => acc
  end.

(** Return all stales in the context. *)
Ltac collect_stales S :=
  let stales := fold_hyps S collect_one_stale in
  lazymatch stales with
  | tt => fail "no stale available"
  | _ => stales
  end.

Ltac auto_exists_L :=
  let acc := collect_stales tt in econstructor; eauto; try instantiate (1 := acc).

Ltac auto_pose_fv a :=
  let acc := collect_stales tt in
  pose (fv_of_set acc) as a;
  assert (a ∉ acc) by (apply fv_of_set_fresh; auto);
  clearbody a.

(* list of atoms *)

Ltac simpl_union H :=
  let rec go H :=
      lazymatch type of H with
      | _ ∉ _ ∪ _ =>
        rewrite not_elem_of_union in H;
          let H1 := fresh "Hfresh" in
          let H2 := fresh "Hfresh" in
          destruct H as [H1 H2]; go H1; go H2
      | _ => idtac
  end in go H.

Ltac instantiate_atom_listctx :=
  let acc := collect_stales tt in
  instantiate (1 := acc); intros;
  repeat (match goal with
          | [H: forall (x: atom), x ∉ ?L -> _, H': ?a ∉ _ ∪ (stale _) |- _ ] =>
              assert (a ∉ L) as Htmp by fast_set_solver;
              specialize (H a Htmp); clear Htmp; repeat destruct_hyp_conj; auto
          end; simpl).

Lemma empty_eq_app_exfalso {A: Type}: forall Γ1 (x: atom) (t: A) Γ2, ~ ([] = Γ1 ++ [(x, t)] ++ Γ2).
  Proof.
    intros. intro H.
    symmetry in H. apply app_eq_nil in H. mydestr.
    apply app_eq_nil in H0. mydestr. inversion H0.
Qed.

Ltac auto_exfalso :=
  match goal with
  | [H: [] = _ ++ [(_, _)] ++ _ |- _] => apply empty_eq_app_exfalso in H; inversion H
  | [H: _ ++ [(_, _)] ++ _ = [] |- _] => symmetry in H; apply empty_eq_app_exfalso in H; inversion H
  | [H: ?a <> ?a |- _ ] => exfalso; auto
  | [H: False |- _] => inversion H
  | [H: Some _ = None |- _ ] => inversion H
  | [H: None = Some _ |- _ ] => inversion H
  | [H1: [] = _ ++ _ |- _ ] => symmetry in H1; apply app_eq_nil in H1; destruct H1 as (_ & H1); inversion H1
  end || (exfalso; fast_set_solver !!).

Ltac specialize_with x :=
  match goal with
  | [H: forall x, (x ∈ ?L → False) -> _ |- _] =>
      let Htmp := fresh "Htmp" in
      assert (x ∉ L) as Htmp by fast_set_solver; specialize (H x Htmp); try clear Htmp
  | [H: forall x, x ∉ ?L -> _ |- _] =>
      let Htmp := fresh "Htmp" in
      assert (x ∉ L) as Htmp by fast_set_solver; specialize (H x Htmp); try clear Htmp
  end.

Ltac pose_fresh_fv name :=
  auto_pose_fv name.

Ltac f_equal_hyp :=
  repeat match goal with
         | [ |- ?a ?e1 = ?a ?e2 ] =>
             assert (e1 = e2) as HH; try (rewrite HH; auto)
         | [|- ?a ?b ?e1 = ?a ?b ?e2 ] =>
             assert (e1 = e2) as HH; try (rewrite HH; auto)
         | [|- ?a ?b ?c ?e1 = ?a ?b ?c ?e2 ] =>
             assert (e1 = e2) as HH; try (rewrite HH; auto)
         | [ |- ?a ?b ?c1 = ?a ?b ?c2 ] =>
             assert (c1 = c2); auto
         | [ H: ?a _ = ?a _ |- _ ] =>
             inversion H; subst; clear H; auto
         | [ H: ?a _ _ = ?a _ _ |- _ ] =>
             inversion H; subst; clear H; auto
         | [ H: ?a _ _ _ = ?a _ _ _ |- _ ] =>
             inversion H; subst; clear H; auto
         end.

(* When constructor contains an aset, we automatically collect the stales and instantiate the aset. *)
Ltac econstructor_L :=
  unshelve econstructor;
  try lazymatch goal with
  | |- aset =>
      let acc := collect_stales tt in exact acc
  | |- ?G =>
      try lazymatch type of G with
      | Prop => fail 1               (* This is the main proof goal: do not touch it *)
      | _ => shelve        (* This is some other evar goal: shelve it for now *)
      end
  end; eauto.

Ltac auto_specialization :=
  try lazymatch goal with
  | |- forall y, y ∉ _ -> _ =>
    let y := fresh "y" in
    let Hy := fresh "Hy" in
    intros y Hy;
    specialize_with y
  end;
  eauto.

Ltac econstructor_L_specialized :=
  econstructor_L; auto_specialization.

Ltac cut_premise H :=
  lazymatch type of H with
  | ?A -> _ => cut A
  end.