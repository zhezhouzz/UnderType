From stdpp Require Import mapset.
From CT Require Import Syntax.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.

Import BaseDef MyTactics Primitives Lang LangLc Qualifier OperationalSemantics BasicTyping BasicTypingProp.

(** This file defines valuation environment, i.e., substitution (σ), and
  multi-substitution operation. *)

(** Environment (substitution) *)
Notation env := (amap value).
(** A world is a set of substitutions that satisfies a proposition.
    π ⊧ P iff ∀ σ ∈ π, σ ⊧ P.
    If π ⊧ P and P -> Q, then π ⊧ Q.
    A world can also be treated as an abstraction of a set of propositions P (closed under implication).
    The denotation of a type context is the set of propositions that are satisfied under the type context—a set of worlds (not a single world, because it may not be closed under implication).
    ⟦Γ⟧ := { π | Γ ⊧ P ∧ π ⊧ P }
    Γ ⊧ P iff there exists a world π in ⟦Γ⟧.
    Assume mkWorld(P) is the minimal set of substitutions that satisfies P.
    mkWorld(P) := {σ ∈ E | σ ⊧ P}
    ⟦Γ⟧ := { mkWorld(P) | Γ ⊧ P }, closed with respect to the subset relation.
    For example, mkWorld(x = y) :=
      {[x := True, y := True], [x := False, y := False]}
    For a world π = {[x := True, y := True]}, π ⊧ x = y.
    For a type context x:{bool | v = True}, y:{bool | top },
    its denotation contains all worlds including 
    [x := True, y := True] and [x := True, y := False].
    ⟦Γ⟧ = {
      {[x := True, y := True], [x := True, y := False]}, 
      {[x := True, y := True], [x := True, y := False], [x := False, y := False]},
      ..., 
    }
    This means that it is free to pick any world from the denotation; if the world can entail the proposition P, it is sufficient to prove the proposition P.
    For a type context x:{bool | v = True}, y:[bool | top ],
    its denotation contains all worlds including 
    [x := True, y := True] or [x := True, y := False].
    ⟦Γ⟧ = {
      {[x := True, y := True]}, 
      {[x := True, y := False]},
      {[x := True, y := False], [x := False, y := False]},
      ..., 
    }
    For a type context x:[bool | top], y:[bool | v = x ],
    its denotation contains all worlds including 
    [x := True, y := True] or [x := False, y := False].
    For a type context x:{bool | top}, y:[bool | v = x ],
    its denotation contains all worlds including 
    [x := True, y := True] and [x := False, y := False].
*)
Inductive world : Type :=
| World (L: aset) (π: env -> Prop).
(* Technically, we require the domain of all substitutions in the world to be the same (i.e., L). *)

Definition closed_env (env : env) := map_Forall (fun _ v => stale v ≡ ∅) env.

Inductive closed_world: world -> Prop :=
| ClosedWorld: forall L π,
    (forall σ, π σ -> dom σ ≡ L /\ closed_env σ) ->
    closed_world (World L π).

#[global] Instance world_stale : Stale world := 
  fun w => match w with
  | World L π => L
  end.
Arguments world_stale /.

Definition emp_world : world := World ∅ (fun σ => σ = ∅).

Lemma emp_world_closed: closed_world emp_world.
Proof.
  econstructor; eauto. split; eauto. my_set_solver. subst.
  apply map_Forall_empty.
Qed.

Global Hint Resolve emp_world_closed: core.

(* x is not in L *)
Definition world_insert (x: atom) (vset: env -> value -> Prop) (w: world): world :=
  match w with
  | World L π => World (L ∪ {[x]}) 
    (fun σ' => exists σ v, σ' = <[x:=v]> σ /\ π σ /\ vset σ v)
  end.

Lemma world_insert_stale x vset w :
  stale (world_insert x vset w) = stale w ∪ {[x]}.
Proof.
  destruct w. ln_simpl; eauto.
Qed.

Definition world_models (w: world) (P: env -> Prop) :=
  match w with
  | World L π => forall σ, π σ -> P σ
  end.
  
Notation "w '⊨' P " := (world_models w P) (at level 20, format "w ⊨ P", w constr, P constr).

Lemma closed_world_closed_env w: closed_world w -> w ⊨ (fun σ => closed_env σ).
Proof.
  intros H.
  inversion H; subst; eauto.
  simpl. hauto.
Qed.

Definition world_models_implies (w: world) (P Q: env -> Prop) :
  w ⊨ P -> (forall σ, P σ -> Q σ) -> w ⊨ Q.
Proof.
  intros Hmodels Himplies.
  destruct w. hauto.
Qed.

Definition world_models_iff (w: world) (P Q: env -> Prop) :
w ⊨ (fun σ => P σ <-> Q σ) <-> (w ⊨ (fun σ => P σ -> Q σ)) /\ (w ⊨ (fun σ => Q σ -> P σ)).
Proof.
  split; intros; destruct w; hauto.
Qed.

Definition world_models_and (w: world) (P Q: env -> Prop) :
  (w ⊨ P /\ w ⊨ Q) <-> w ⊨ (fun σ => P σ /\ Q σ).
Proof.
  split; intros.
  - mydestr. destruct w. hauto.
  - destruct w. hauto. 
Qed.

Definition world_join (w1 w2: world) : world :=
  match w1, w2 with
  | World L1 π1, World L2 π2 => World (L1 ∪ L2) (fun σ => π1 σ \/ π2 σ)
  end.

Lemma world_join_models_left w1 w2 (P: env -> Prop):
  w1 ⊨ (fun σ => P σ) -> (world_join w1 w2) ⊨ (fun σ => P σ).
Proof.
  intros Hmodels1; destruct w1, w2; simpl in *; eauto.
  intros σ Hπ. apply Hmodels1 in Hπ. apply H. apply Hπ.
  destruct w1, w2. hauto.
Qed.

(** Multi-substitution, i.e., σ(⋅) operation. The definition is parameterized by
  any substitution. *)
Definition msubst (env : env) {A: Type} (a : A) `{Subst value A} : A :=
  map_fold subst a env.

Notation "'m{' x '}'" := (msubst x) (at level 20, format "m{ x }", x constr).
