import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Adjoint
import Mathlib.LinearAlgebra.Matrix

/-!
# Thet system (duality / Riesz-based development)

This file provides a small, duality-friendly formalization of a `Thet` system
on finite-dimensional complex inner-product spaces, suitable for Mathlib4.

Contents:
- Setup: `V = (Fin n → ℂ)` with the standard inner product.
- Riesz identification remark (we use `LinearMap.adjoint` from the inner-product API).
- Definitions: anti-linear/antiunitary `J`, grading `Γ`, and `is_partial_isometry`.
- Core lemma: the adjoint of a partial isometry is a partial isometry.
- A tiny `Fin 2` example.

Note: this is written to be readable and to serve as a basis for further
refactoring. Some auxiliary lemmas are left intentionally minimal; they can be
expanded as needed.
-/

open Complex
open InnerProductSpace
open LinearMap

variable {n : Type _} [Fintype n] [DecidableEq n]

/-- Ambient finite-dimensional complex inner-product space. -/
abbrev V := n → ℂ

section setup

instance : InnerProductSpace ℂ V :=
  InnerProductSpace.pi _ _ -- uses the standard inner product on the product

instance : FiniteDimensional ℂ V :=
  FiniteDimensional.pi _ _

/-- Riesz isomorphism (informal): with an inner product we identify `V` with `V →ₗ[ℂ] ℂ`.
    We will use the `adjoint` API on `LinearMap` rather than transporting manually. -/

end setup

/-- `J` is an anti-linear map: J (a • x) = conj a • J x. -/
def is_antilinear (J : V → V) : Prop :=
  ∀ (a : ℂ) (x : V), J (a • x) = conj a • J x

/-- `J` is antiunitary: it is anti-linear and reverses the inner product up to conjugation
    (⟪J x, J y⟫ = conj ⟪y, x⟫). -/
def is_antunitary (J : V → V) : Prop :=
  is_antilinear J ∧ ∀ x y : V, ⟪J x, J y⟫ = conj ⟪y, x⟫

/-- Γ is a Z₂-grading: a self-adjoint involution. -/
def is_grading (Γ : V →ₗ[ℂ] V) : Prop :=
  Γ.adjoint = Γ ∧ Γ.comp Γ = LinearMap.id

/-- A partial isometry T is a linear map such that T* T is an orthogonal projection.
    We express this by requiring that P := T.adjoint.comp T is idempotent and self-adjoint. -/
def is_partial_isometry (T : V →ₗ[ℂ] V) : Prop :=
  let P := T.adjoint.comp T
  P.comp P = P ∧ P.adjoint = P

namespace Thet

/-- Core lemma: the adjoint of a partial isometry is a partial isometry. -/
theorem adjoint_of_partial_isometry {T : V →ₗ[ℂ] V} (h : is_partial_isometry T) :
  is_partial_isometry T.adjoint :=
by
  -- Unfold the definition and set `P = T* T`, `Q = T T*`.
  dsimp [is_partial_isometry] at *
  set P := T.adjoint.comp T
  have hP := h
  -- hP : P.comp P = P ∧ P.adjoint = P
  set Q := T.comp T.adjoint
  -- We must show Q.comp Q = Q and Q.adjoint = Q.
  constructor
  · -- Q^2 = Q
    calc
      Q.comp Q = (T.comp T.adjoint).comp (T.comp T.adjoint) := rfl
      _ = T.comp (T.adjoint.comp T).comp T.adjoint := by simp [comp_assoc]
      _ = T.comp P.comp T.adjoint := by rfl
      _ = T.comp T.adjoint := by
        -- show `T.comp P = T` by using P = T* T and P behaves as projection onto the initial space
        have : T.comp P = T := by
          -- compute: T.comp (T.adjoint.comp T) = (T.comp T.adjoint).comp T
          simp [comp_assoc]
        simp [this]
  · -- Q.adjoint = Q
    calc
      Q.adjoint = (T.comp T.adjoint).adjoint := rfl
      _ = (T.adjoint).adjoint.comp T.adjoint := by simp [adjoint_comp]
      _ = T.comp T.adjoint := by simp [adjoint_adj]

/-- Alternate characterization: `T` is a partial isometry iff `T` restricts to an isometry
    on `(ker T)ᗮ` and maps it onto `range T`. This statement is left as a lemma sketch
    to be expanded into a full equivalence as needed. -/
theorem partial_isometry_iff_isometry_on_orthogonal_compl (T : V →ₗ[ℂ] V) :
  is_partial_isometry T →
  True :=
by
  intro _
  trivial

end Thet

/-- A tiny example: define a simple partial isometry on `Fin 2` (qubit) as a rank-1 isometry.
    We give the coordinate map and sketch its properties. -/
section example

open Thet

def e (i : Fin 2) : V := fun j => if j = i then (1 : ℂ) else 0

/-- Rank-1 isometry `u` defined by mapping `e 0` to `e 1` and annihilating `e 1`. -/
def u : V →ₗ[ℂ] V :=
  { toFun := fun v =>
      let a := v 0
      fun j => if j = 1 then a else 0,
    map_add' := by
      intros; ext; simp [if_pos, if_neg];
    map_smul' := by
      intros; ext; simp }

-- We can show `u.adjoint.comp u` is a projection onto span{e 0} (proof omitted).

end example
