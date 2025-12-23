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
    forall σ, π σ -> dom σ ≡ L /\ closed_env σ ->
    closed_world (World L π).

#[global] Instance world_stale {A:Type} : Stale world := 
  fun w => match w with
  | World L π => L
  end.
Arguments world_stale /.

(** Multi-substitution, i.e., σ(⋅) operation. The definition is parameterized by
  any substitution. *)
Definition msubst {A: Type} (a : A) `{Subst value A}  (env : env)  : A :=
  map_fold subst a env.

Notation "'m{' x '}'" := (msubst x) (at level 20, format "m{ x }", x constr).
