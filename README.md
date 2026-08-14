# Thet Algebra / Thet Project

**A machine-checked derivation of the Standard Model gauge algebra from an off-diagonal mass operator.**

[![Lean 4](https://img.shields.io/badge/Lean-4-blue)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib4-stable-green)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

**Author:** Jeffrey Michael Gurd  
**Affiliation:** Nexus Research Institute (independent researcher), Schoolcraft, Michigan  

> I pledge to deploy my skills with rigor and responsibility, ensuring that the systems and knowledge I create empower humanity, protect privacy, and prioritize safety above convenience or profit.

With this pledge the work is free to share under the MIT License.

---

## Core Result

This repository proves a unique structural inevitability theorem (`Thet_Unification_Theorem`) using the Lean 4 proof assistant:

> The Standard Model gauge algebra \(SU(3)_c \times SU(2)_L \times U(1)_Y\) (dimension 12) is **not assumed**.  
> It is the *exact, maximal commutant* (symmetry group) of a mass-gap operator (\(\theta\)) acting on a 32-dimensional Left ⊕ Right fermion space.

## The Methodology: "No Forced Emergence"

This project is built on a strict foundational rule:

> **No retroactive assumptions. No parameter insertion to obtain a desired result.**

We did not tell Lean to "prove SU(5)". Instead, we defined the physical constraints (charge conservation, chirality-flipping, color preservation) and asked Lean to compute the algebra that necessarily emerges.  
If the algebra had been \(SU(2)\) instead, we would have accepted that result. The proof that it is the Standard Model algebra is strictly derived, not engineered.

## Key Discoveries

1. **Unique Mass Structure**: Applying the above constraints to all 240 possible transitions in the 16-state SM generation forces *exactly* the 8 known physical mass pairs. No tuning, no cherry-picking.
2. **Exact Commutant**: The 32-dimensional off-diagonal mass operator \(\theta\) has a simultaneous commutant that is strictly 12-dimensional—matching \(8+3+1\) for \(SU(3) \times SU(2) \times U(1)\).
3. **Lean Verified**: All arithmetic, trace identities, and Lie algebra decomposition proofs are fully formalized in the `Unity/Thet/` directory.
4. **Block-matrix formulation**: `Unity/Thet/BlockKrajewski.lean` proves that the Krajewski \(\theta\) operator is self-adjoint and anticommutes with the grading operator \(\gamma\) using an explicit left/right block decomposition.

## A Note on the Name "Thet"

**We explicitly reject any etymological or numerological claims.**  
The name "Thet" is a contracted mnemonic for the physics symbol \(\theta\) (standard for angle-like gauge parameters). It is a creative label for a mathematical object, *not* a hidden lineage connecting ancient Phoenician letters to complexity theory or physics.

## Is this a Millennium Prize solution?

**No.**  
This is NOT a solution to the Yang–Mills mass gap problem (which requires proving a non-perturbative spectral gap on \(\mathbb{R}^4\) satisfying Wightman axioms).  
However, this *is* a breakthrough in structural inevitability—a fully formal proof that the defining symmetries of the Standard Model are mathematically forced by the existence of a mass-gap operator, leaving zero room for arbitrary assumptions.

## Getting Started (For Lean 4 Users)

```bash
lake build Thet
lake env lean Unity/Thet/Main.lean