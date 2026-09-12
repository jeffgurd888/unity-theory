import CGurd.Spectral
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Exponential

open Matrix

/-- Standard non-trivial coupling matrix for inter-sector bridges. -/
def couplingOp : C2Mat :=
  ![![0, 1],
    ![1, 0]]

/-- Time-evolved boundary link: XY(t) = U_Y(t) * XY -/
def evolvedXY (t : ℝ) (omega1 omega2 : ℝ) : C2Mat :=
  UY t omega1 omega2 * couplingOp

/-- The complete ternary chain operator T(t) = YZ(t) * XY(t). -/
def ternaryChain (t : ℝ) (omega1 omega2 : ℝ) : C2Mat :=
  evolvedXY t omega1 omega2 * evolvedXY t omega1 omega2

/-- Theorem: Trace of the ternary operator factorizes into the sum of frequencies. -/
theorem ternary_trace_theorem (t : ℝ) (omega1 omega2 : ℝ) :
  Matrix.trace (ternaryChain t omega1 omega2) =
  2 * Complex.exp (-Complex.I * t * (omega1 + omega2)) := by
  -- Unfold definitions down to matrix components
  dsimp [ternaryChain, evolvedXY, UY, couplingOp, Matrix.mul, Matrix.trace, Fin.sum_univ_two]
  -- Simplify complex exponential products using exp addition laws
  have h_exp : Complex.exp (-Complex.I * t * omega1) * Complex.exp (-Complex.I * t * omega2) =
                Complex.exp (-Complex.I * t * (omega1 + omega2)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [h_exp]
  ring
