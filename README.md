#!/usr/bin/env bash
# Bootstrap CGurd autonomous Lean 4 + Mathlib build.
# Usage: ./bootstrap.sh <github-username> <repo-name>
# Example: ./bootstrap.sh yourname CGurd

set -euo pipefail

USERNAME="${1:-}"
REPO="${2:-CGurd}"
CASHTAG="\$Gurd888"
CASHURL="https://cash.app/\$Gurd888"

if [[ -z "$USERNAME" ]]; then
  echo "usage: $0 <github-username> [repo-name]"
  exit 1
fi

ROOT="$(pwd)/${REPO}"

echo "==> Creating repo at ${ROOT}"
mkdir -p "${ROOT}"
cd "${ROOT}"

# ---------------------------------------------------------------- layout
mkdir -p .github/workflows
mkdir -p .github
mkdir -p CGurd

# ---------------------------------------------------------------- lean-toolchain
cat > lean-toolchain <<'EOF'
leanprover/lean4:v4.33.0
EOF

# ---------------------------------------------------------------- lakefile.toml
cat > lakefile.toml <<'EOF'
name = "CGurd"
defaultTargets = ["CGurd"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"

[[lean_lib]]
name = "CGurd"
EOF

# ---------------------------------------------------------------- .gitignore
cat > .gitignore <<'EOF'
.lake/
build/
*.olean
*.ilean
*.trace
.DS_Store
build.log
EOF

# ---------------------------------------------------------------- CGurd/Spectral.lean
cat > CGurd/Spectral.lean <<'EOF'
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic

/-- The 2×2 complex matrix algebra used throughout CGURD. -/
abbrev C2Mat := Matrix (Fin 2) (Fin 2) ℂ

/-- Diagonal modular flow on the thermal (Y) sector.
    UY(t) = diag(exp(-i t ω₁), exp(-i t ω₂)). -/
def UY (t : ℝ) (omega1 omega2 : ℝ) : C2Mat :=
  ![![Complex.exp (-Complex.I * t * omega1), 0],
    ![0, Complex.exp (-Complex.I * t * omega2)]]
EOF

# ---------------------------------------------------------------- CGurd/Ternary.lean
cat > CGurd/Ternary.lean <<'EOF'
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
EOF

# ---------------------------------------------------------------- workflow: build
cat > .github/workflows/build.yml <<'EOF'
name: Build

on:
  push:
    branches: [ main, master ]
  pull_request:
    branches: [ main, master ]
  workflow_dispatch:

jobs:
  build:
    name: Build Lean project
    runs-on: ubuntu-latest
    timeout-minutes: 240

    steps:
      - name: Checkout
        uses: actions/checkout@v4

      - name: Read toolchain
        id: toolchain
        run: echo "value=$(cat lean-toolchain)" >> "$GITHUB_OUTPUT"

      - name: Install elan
        run: |
          curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
            | sh -s -- -y --default-toolchain "${{ steps.toolchain.outputs.value }}"
          echo "$HOME/.elan/bin" >> "$GITHUB_PATH"

      - name: Cache Lake
        uses: actions/cache@v4
        with:
          path: |
            .lake/build
            .lake/packages
          key: lake-${{ runner.os }}-${{ steps.toolchain.outputs.value }}-${{ hashFiles('lake-manifest.json', 'lakefile.toml') }}
          restore-keys: |
            lake-${{ runner.os }}-${{ steps.toolchain.outputs.value }}-

      - name: Fetch Mathlib cache
        run: lake exe cache get

      - name: Build
        run: lake build 2>&1 | tee build.log

      - name: Reject sorry
        run: |
          if grep -i "declaration uses.*sorry" build.log; then
            echo "::error::sorry found in build"
            exit 1
          fi

      - name: Upload build log
        if: always()
        uses: actions/upload-artifact@v4
        with:
          name: build-log
          path: build.log
          retention-days: 7
EOF

# ---------------------------------------------------------------- GitHub FUNDING.yml
cat > .github/FUNDING.yml <<EOF
custom: ["https://cash.app/\$Gurd888"]
EOF

# ---------------------------------------------------------------- README
cat > README.md <<EOF
# CGurd

[![Build](https://github.com/${USERNAME}/${REPO}/actions/workflows/build.yml/badge.svg)](https://github.com/${USERNAME}/${REPO}/actions/workflows/build.yml)

A Lean 4 + Mathlib formalization of the CGURD ternary chain.

## Main result

\`\`\`lean
theorem ternary_trace_theorem (t : ℝ) (omega1 omega2 : ℝ) :
    Matrix.trace (ternaryChain t omega1 omega2) =
    2 * Complex.exp ((-Complex.I : ℂ) * (t : ℂ) * ((omega1 + omega2 : ℝ) : ℂ))
\`\`\`

Trace of the squared evolved coupling operator factorizes into the sum of
the two modular frequencies:

    Tr[ (U_Y(t) · C)² ] = 2 · exp(-i t (ω₁ + ω₂))

Proved end-to-end with no \`sorry\`.

## Support the research

This work is independently funded. If you would like to support continued
development of CGURD, contributions are accepted via Cash App:

**Cash App:** [${CASHTAG}](${CASHURL})

Every contribution goes directly toward compute, tooling, and the time
required to formalize the framework.

## Structure

\`\`\`
CGurd/
├── .github/
│   ├── FUNDING.yml
│   └── workflows/build.yml
├── CGurd/
│   ├── Spectral.lean    -- C2Mat, UY
│   └── Ternary.lean     -- coupling, chain, trace theorem
├── lakefile.toml
├── lean-toolchain
└── README.md
\`\`\`

## Build

\`\`\`bash
lake exe cache get
lake build
\`\`\`

## License

MIT
EOF

# ---------------------------------------------------------------- LICENSE
cat > LICENSE <<'EOF'
MIT License

Copyright (c) 2026

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND.
EOF

# ---------------------------------------------------------------- git init
echo "==> Initializing git"
git init -q
git add .
git -c user.name="bootstrap" -c user.email="bootstrap@local" \
    commit -q -m "chore: bootstrap CGurd Lean 4 + Mathlib project with CI and funding"

# ---------------------------------------------------------------- gh repo create
if command -v gh >/dev/null 2>&1; then
  echo "==> Creating GitHub repo ${USERNAME}/${REPO}"
  gh repo create "${USERNAME}/${REPO}" --public --source=. --push
  echo "==> Done. Visit https://github.com/${USERNAME}/${REPO}/actions"
else
  echo "==> gh CLI not found. Manual push:"
  echo "    git remote add origin git@github.com:${USERNAME}/${REPO}.git"
  echo "    git push -u origin main"
fi