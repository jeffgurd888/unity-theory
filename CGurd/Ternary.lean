import CGurd.Spectral
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Exponential

open Matrix

/-- Standard non-trivial coupling matrix for inter-sector bridges. -/
def couplingOp : C2Mat :=
  ![![0, 1],
    ![1, 0]]

/-- Time-evolved boundary link: XY(t) = U_Y(t) * C. -/
def evolvedXY (t : ℝ) (omega1 omega2 : ℝ) : C2Mat :=
  UY t omega1 omega2 * couplingOp

/-- The minimal ternary chain operator T(t) = XY(t)². -/
def ternaryChain (t : ℝ) (omega1 omega2 : ℝ) : C2Mat :=
  evolvedXY t omega1 omega2 * evolvedXY t omega1 omega2

/-- Trace factorization for the minimal XY chain:
    Tr[(U_Y(t) · C)²] = 2 · exp(-i t (ω₁ + ω₂)). -/
theorem ternary_trace_theorem (t : ℝ) (omega1 omega2 : ℝ) :
    Matrix.trace (ternaryChain t omega1 omega2) =
    2 * Complex.exp ((-Complex.I : ℂ) * (t : ℂ) * ((omega1 + omega2 : ℝ) : ℂ)) := by
  simp only [ternaryChain, evolvedXY, couplingOp, UY, Matrix.mul_apply,
             Matrix.trace, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
             Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const]
  have h_exp_12 :
      Complex.exp (-Complex.I * t * omega1) * Complex.exp (-Complex.I * t * omega2) =
      Complex.exp ((-Complex.I : ℂ) * (t : ℂ) * ((omega1 + omega2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h_exp_21 :
      Complex.exp (-Complex.I * t * omega2) * Complex.exp (-Complex.I * t * omega1) =
      Complex.exp ((-Complex.I : ℂ) * (t : ℂ) * ((omega1 + omega2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h_exp_12, h_exp_21]
  ring
