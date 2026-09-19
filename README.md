Unity Theory: Standard Model Finite Spectral Triple in Lean 4
Formalized verification of the Standard Model finite spectral triple (\mathcal{A}_F, \mathcal{H}_F, \mathcal{D}_F, J_F, \gamma_F) in Lean 4 using Mathlib.
Quickstart: Automated Setup & Full Build
Run this one-liner in your terminal to automatically install elan (Lean toolchain manager), clone the repository, fetch cached Mathlib dependencies, and execute a full clean build:
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y && \
source "$HOME/.elan/env" && \
git clone https://github.com/jeffgurd888/unity-theory.git && \
cd unity-theory && \
lake exe cache get && \
lake build

Manual Installation & Build Steps
1. Prerequisites
Ensure you have git and curl installed. Install the Lean toolchain manager (elan):
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source "$HOME/.elan/env"

2. Clone & Build
git clone https://github.com/jeffgurd888/unity-theory.git
cd unity-theory

# Download pre-compiled Mathlib oleans to skip multi-hour mathlib compilation
lake exe cache get

# Compile the finite spectral triple module
lake build

Automated Verification Protocol
After building, verify that no temporary proofs (sorry or admit) remain and that core definitions are intact:
# Check build exit status (must return 0)
lake build
echo "Exit code: $?"

# Search for any remaining placeholder tactics (should return empty)
grep -RIn --exclude-dir=build --exclude-dir=.git "sorry\|admit" src/ || true

# Verify definitional regression check for piOp conjugation
grep -n "piOp_def_check" src/FiniteSpectralTriple.lean

Formalized Axioms & Theorems Summary
The module src/FiniteSpectralTriple.lean establishes the core algebraic and spectral properties of the 32-state Standard Model representation \mathcal{A}_F = \mathbb{C} \oplus \mathbb{H} \oplus M_3(\mathbb{C}):
| Axiom / Property | Theorem Name | Description |
|---|---|---|
| Definitional Conjugation Guard | piOp_def_check | Proves definitionally (rfl) that \pi^\circ(a) = U_J a^T U_J. |
| Partner Involution | partner_involutive | Establishes J_F particle-antiparticle index mapping involution. |
| Sector Disjointness | pi_zero_of_ge_16, piOp_zero_of_lt_16 | Enforces particle (\mathcal{H}_P) vs antiparticle (\mathcal{H}_A) support orthogonality. |
| Self-Adjoint Dirac Operator | buildDirac_self_adjoint | Proves \mathcal{D}_F^\dagger = \mathcal{D}_F across all block sectors. |
| Grading Anti-commutation | buildDirac_gamma_odd | Enforces odd grading condition \gamma_F \mathcal{D}_F + \mathcal{D}_F \gamma_F = 0. |
| Real Structure Involution | UJ_mul_self | Proves U_J^2 = \mathbb{I}_{32}, guaranteeing J_F^2 = I. |
| Order-Zero Condition | order_zero_condition | Proves [\pi(a), \pi^\circ(b)] = 0 for all a, b \in \mathcal{A}_F. |
| Spectral Triple Bundle | partialStandardModelFiniteTriple | Bundles operator definitions and verified proofs into PartialSMFiniteSpectralTriple. |
Repository Structure
unity-theory/
├── lean-toolchain           # Pinpoints Lean 4 toolchain version
├── lakefile.lean            # Lake project build configuration
├── lake-manifest.json       # Mathlib4 dependency lockfile
└── src/
    └── FiniteSpectralTriple.lean  # Core SM finite spectral triple formalization

Contributing & Branch Workflow
When submitting PRs or verification patches:
 * Push targeted edits to feature/claim-setup.
 * Run lake build locally to confirm zero build errors and zero standard library warnings.
 * Verify rg -n "sorry|admit" yields zero matches before merging into main.
