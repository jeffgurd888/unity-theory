# unity-theory

Formalization of "Thet systems" in Lean 4 / Mathlib4 (Riesz / duality approach).

This repository contains an initial development exploring duality-based constructions
on finite-dimensional complex inner-product spaces. The feature branch
`feature/thet-duality` contains the first formal file `src/ThetSystem.lean` and
sponsorship documentation.

Quick links
- Branch with current work: https://github.com/jeffgurd888/unity-theory/tree/feature%2Fthet-duality
- File added: `src/ThetSystem.lean`
- Issue: https://github.com/jeffgurd888/unity-theory/issues/1

Build
- Install Lean toolchain (elan) and Lake (see https://leanprover-community.github.io/lean4/doc/).
- Run `lake build` (requires Mathlib4; the lakefile in the branch points at the Mathlib4 `main` branch).

Sponsorship
If you find this project useful, please consider sponsoring development. Ways to sponsor:
- GitHub Sponsors: https://github.com/sponsors/jeffgurd888
- Cash App: https://cash.app/$Gurd888

See `SPONSORS.md` and `FUNDING.yml` for details.

Contributing
Contributions are welcome — please open issues or pull requests. For development notes and TODOs see the comments in `src/ThetSystem.lean`.
