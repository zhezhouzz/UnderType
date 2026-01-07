From stdpp Require Import mapset.
From CT Require Import BaseDef MyTactics Primitives Lang.

(** This file defines valuation environment, i.e., substitution (σ), and
  multi-substitution operation. *)

(** Environment (substitution) *)
Notation env := (amap value).
#[global] Instance env_stale : Stale env := 
  fun env => dom env.
Arguments env_stale /.

Definition closed_env (env : env) := map_Forall (fun _ v => stale v = ∅) env.

(* Definition sync_envs (L: aset) (σ1 σ2: env) : Prop :=
  forall x, x ∈ L -> σ1 !! x = σ2 !! x.

Notation "σ1 '={' L '}' σ2" := (sync_envs L σ1 σ2) (at level 20, format "σ1 ={ L } σ2", σ1 constr, σ2 constr, L constr). *)

(** Multi-substitution, i.e., σ(⋅) operation. The definition is parameterized by
  any substitution. *)
Definition msubst (env : env) {A: Type} (a : A) `{Subst value A} : A :=
  map_fold subst a env.

Notation "'m{' x '}'" := (msubst x) (at level 20, format "m{ x }", x constr).
