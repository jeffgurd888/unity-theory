import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Data.Complex.Basic

namespace Unity.Thet

/-- A Thet operator is a bounded linear operator on a complex Hilbert space. -/
abbrev Op (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  H →L[ℂ] H

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Thet commutator: [θ, A] = θA - Aθ. -/
def Commutator (θ A : Op H) : Op H :=
  θ.comp A - A.comp θ

notation "[" θ "," A "]" => Commutator θ A

/-- A Thet operator commutes with another if their commutator vanishes. -/
def Commutes (θ A : Op H) : Prop :=
  Commutator θ A = 0

/-- The identity Thet operator. -/
def id : Op H :=
  ContinuousLinearMap.id ℂ H

/-- Thet operator composition. -/
def comp (θ₁ θ₂ : Op H) : Op H :=
  θ₁.comp θ₂

lemma commutator_anticomm (θ A : Op H) :
    Commutator θ A = -(Commutator A θ) := by
  ext x
  simp [Commutator]
  ring

lemma commutator_bilinear (θ A B : Op H) :
    Commutator θ (A + B) = Commutator θ A + Commutator θ B := by
  ext x
  simp [Commutator]

end Unity.Thet
