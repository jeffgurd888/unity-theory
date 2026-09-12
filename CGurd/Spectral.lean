import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

/-- The 2×2 complex matrix algebra used throughout CGURD. -/
abbrev C2Mat := Matrix (Fin 2) (Fin 2) ℂ

/-- Diagonal modular flow on the thermal (Y) sector.
    UY(t) = diag(exp(-i t ω₁), exp(-i t ω₂)). -/
def UY (t : ℝ) (omega1 omega2 : ℝ) : C2Mat :=
  ![![Complex.exp (-Complex.I * t * omega1), 0],
    ![0, Complex.exp (-Complex.I * t * omega2)]]
