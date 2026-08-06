import Mathlib.Data.Complex.Basic
import Unity.Thet.Main

namespace Unity.Gravity

open Unity.Thet

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/--
Gravity in Unity Theory measures the "attraction" or coupling
between two Thet operators based on their commutation relations.
-/
def gravity (θ₁ θ₂ : Op H) : ℝ :=
  ‖Commutator θ₁ θ₂‖

/-- Gravity is symmetric. -/
lemma gravity_symm (θ₁ θ₂ : Op H) :
    gravity θ₁ θ₂ = gravity θ₂ θ₁ := by
  simp [gravity, Commutator]
  ring_nf

/-- Gravity vanishes iff operators commute. -/
lemma gravity_zero_iff (θ₁ θ₂ : Op H) :
    gravity θ₁ θ₂ = 0 ↔ Commutes θ₁ θ₂ := by
  simp [gravity, Commutes, norm_eq_zero]

/--
Gravity matrix: pairwise gravities among a system of Thet operators.
-/
noncomputable def gravityMatrix (θs : ℕ → Op H) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of_apply (fun i j => gravity (θs i) (θs j))

end Unity.Gravity
