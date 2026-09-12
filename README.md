# CGurd · Ternary Chain Dynamics

A Lean 4 formalization of the trace dynamics of a minimal ternary chain operator
built from diagonal modular evolution and an off-diagonal coupling matrix.

## Overview

This module formalizes the algebraic backbone of a two-sector model in the
CGURD framework: a thermal (Y) sector whose modular flow acts diagonally on
two frequencies `ω₁, ω₂`, coupled to a boundary link modeled by the exchange
matrix `[[0,1],[1,0]]`. The ternary chain operator is the square of the
evolved link, and its trace factorizes cleanly into the sum of the two
modular frequencies.

The full chain is proved end-to-end in Lean 4 with no `sorry` placeholders.

## Main Result

```lean
theorem ternary_trace_theorem (t : ℝ) (omega1 omega2 : ℝ) :
    Matrix.trace (ternaryChain t omega1 omega2) =
    2 * Complex.exp (-Complex.I * t * (omega1 + omega2))