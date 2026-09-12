# C GURD: Thermal Clocks & Ternary Relational Dynamics

[![Lean 4 CI](https://github.com/jeffgurd888/unity-theory/actions/workflows/lean.yml/badge.svg)](https://github.com/jeffgurd888/unity-theory/actions)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

## Overview

**C GURD** is a formal theoretical physics framework exploring how observable temporal dynamics and relational geometry emerge from thermodynamic states. Rather than treating time as an external background parameter, this framework derives internal temporal evolution from the modular flow of a designated thermal sector ($\rho_Y$).

This repository contains both the analytical derivations and the formal verification proofs written in **Lean 4** utilizing `Mathlib`.

---

## Mathematical Architecture

### 1. The Thermal Clock
Given a finite-dimensional thermal subsystem $Y$ with spectral decomposition:
$$\rho_Y = \sum_a p_a \vert{}a\rangle\langle a\vert{}, \quad p_a > 0, \quad \sum_a p_a = 1$$

The modular Hamiltonian is defined via the negative logarithm of the state:
$$H_Y = -\log \rho_Y = \sum_a (-\log p_a) \vert{}a\rangle\langle a\vert{}$$

This generates the internal unitary time-evolution operator:
$$U_Y(t) = e^{-it H_Y} = \sum_a e^{-it \omega_a} \vert{}a\rangle\langle a\vert{}, \quad \omega_a = -\log p_a$$

### 2. The $\mathbb{C}^2$ Minimal Model
To test the dynamics explicitly, we restrict the sectors to two-level systems ($\mathcal{H}_X = \mathcal{H}_Y = \mathcal{H}_Z = \mathbb{C}^2$). Taking a thermal density matrix:
$$\rho_Y = \begin{pmatrix} 0.8 & 0 \\ 0 & 0.2 \end{pmatrix}$$

Yields the fundamental frequency splitting (the "breathing" rate):
$$\Delta\omega = \omega_2 - \omega_1 = \log(0.2) - \log(0.8) = \log(4) \approx 1.38629$$

### 3. The Ternary Chain $\mathcal{T}(t)$
Coupling $X$ to $Y$ and $Y$ to $Z$ via boundary operators $XY$ and $YZ$, the complete ternary propagation operator is:
$$\mathcal{T}(t) = YZ(t) \cdot XY(t)$$

Under modular flow, the individual links exhibit local interference oscillations governed by $\Delta\omega$, while the composed chain invariant projects out the global frequency sum $\omega_1 + \omega_2$.

---

## Repository Structure

```text
unity-theory/
├── CGurd/
│   └── Basic.lean       # Formal definitions of rho_Y, HY, UY, and trace theorems
├── lakefile.lean        # Lake package configuration for Lean 4
├── lean-toolchain       # Lean version specifier (v4.14.0)
└── README.md            # Documentation and theoretical overview
