import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Eigenvalues
import Mathlib.Data.Complex.Basic
import Unity.Spectral.Colours

namespace Unity.Spectral

open Complex
open PillarColour

/-- A spectral datum: eigenvalue + pillar colour. -/
structure SpectralDatum :=
  (λ : ℂ)
  (colour : PillarColour)
deriving Repr

/--
Colour assignment based on the argument of an eigenvalue.
This matches the Unity Theory pillar palette.
-/
def colourOfEigenvalue (λ : ℂ) : PillarColour :=
  let θ := Complex.arg λ
  if θ < -π/3 then red
  else if θ < 0 then orange
  else if θ < π/3 then green
  else if θ < 2*π/3 then cyan
  else blue

/--
Finite-dimensional spectral functor:
Given a matrix representation of a Thet operator,
compute its eigenvalues and colour them.
-/
noncomputable def SpectralFunctorMatrix
    {n : Nat} (A : Matrix (Fin n) (Fin n) ℂ) :
    List SpectralDatum :=
  let λs := A.eigenvalues.toList
  λs.map (fun λ => { λ := λ, colour := colourOfEigenvalue λ })

/--
General spectral functor:
For now, we require a finite-dimensional representation.
Later, this can be extended to bounded operators on Hilbert spaces.
-/
noncomputable def SpectralFunctor
    {n : Nat} (θ : Matrix (Fin n) (Fin n) ℂ) :
    List SpectralDatum :=
  SpectralFunctorMatrix θ

/-- SpectralFunctor is invariant under unitary conjugation (statement). -/
lemma SpectralFunctor_unitary_invariant
    {n : Nat} (U θ : Matrix (Fin n) (Fin n) ℂ)
    (hU : Uᴴ ⬝ U = 1 ∧ U ⬝ Uᴴ = 1) :
    SpectralFunctor (Uᴴ ⬝ θ ⬝ U) = SpectralFunctor θ := by
  -- This will be provable once we use mathlib's eigenvalue invariance lemmas.
  sorry

end Unity.Spectral
