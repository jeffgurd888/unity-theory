# Contributing to unity-theory

Thanks for your interest in contributing! Below are quick steps to set up a local dev environment and ways to help.

Getting started
1. Install Lean toolchain (elan): https://leanprover-community.github.io/lean4/doc/installation.html
2. Install Lake: follow Lean 4 / Lake docs.
3. Clone the repo and switch to the feature branch:
   git clone https://github.com/jeffgurd888/unity-theory.git
   cd unity-theory
   git checkout feature/thet-duality
4. Build:
   lake build

Run tests / checks
- The project uses Lake + Mathlib4. Use `lake build` to compile the Lean files.
- If you add examples or tests, include them under `test/` and add CI entries if needed.

How to contribute
- Pick a starter task from STARTER_TASKS.md or comment on issue #1 to claim work.
- Fork -> branch -> PR targeting branch `feature/thet-duality` (I'll merge into that branch and then open a PR to `main`).

Communication
- Ask questions by commenting on issue #1 or open a new issue referring to a specific starter task.
- If you're on Zulip/Discord, mention your GitHub handle so I can assign tasks.

Coding style / guidelines
- Prefer Mathlib4 types and idioms (LinearAlgebra, InnerProductSpace, SemilinearMap) over ad-hoc matrix gymnastics.
- Keep proofs explicit and add doc comments for new lemmas.

Acknowledgements
- Sponsors will be listed in SPONSORS.md and the README per tiers.
