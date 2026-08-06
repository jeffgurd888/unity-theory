# unity-theory

Formalization of **Thet systems** in Lean 4 / Mathlib4 — a duality-based approach using Riesz representation on finite-dimensional complex inner-product spaces.

This repository contains an early development that explores how certain dual-cone and orthogonality relations can be captured in a formally verified setting. The feature branch `feature/thet-duality` carries the first formal file `src/ThetSystem.lean` together with sponsorship documentation.

## What is a Thet system?

A *Thet system* (over a finite-dimensional complex Hilbert space) consists of two families of vectors together with constraints that express a mutual “dual” relationship, often phrased in terms of Riesz representation, orthocomplements, and polar sets. The Lean formalisation in this repo builds the basic definitions, proves elementary properties, and sets up the algebraic structures needed for further study.

## Quick links

- Branch with current work: [`feature/thet-duality`](https://github.com/jeffgurd888/unity-theory/tree/feature%2Fthet-duality)
- Main formal file: [`src/ThetSystem.lean`](https://github.com/jeffgurd888/unity-theory/blob/feature%2Fthet-duality/src/ThetSystem.lean)
- Issue tracker: [Issue #1](https://github.com/jeffgurd888/unity-theory/issues/1)

## Build

1. Install the Lean toolchain (`elan`) and Lake (see the [Lean 4 setup guide](https://leanprover-community.github.io/lean4/doc/)).
2. Clone the repository and check out the feature branch:
   ```bash
   git clone https://github.com/jeffgurd888/unity-theory
   cd unity-theory
   git checkout feature/thet-duality