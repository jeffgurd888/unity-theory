# CGurd

[![Build](https://github.com/jeffgurd888/unity-theory/actions/workflows/build.yml/badge.svg)](https://github.com/jeffgurd888/unity-theory/actions/workflows/build.yml)

A Lean 4 + Mathlib formalization of the CGURD ternary chain.

## Main result

```
theorem ternary_trace_theorem (t : ℝ) (omega1 omega2 : ℝ) :
    Matrix.trace (ternaryChain t omega1 omega2) =
    2 * Complex.exp ((-Complex.I : ℂ) * (t : ℂ) * ((omega1 + omega2 : ℝ) : ℂ))
```

Trace of the squared evolved coupling operator factorizes into the sum of
the two modular frequencies:

    Tr[ (U_Y(t) · C)² ] = 2 · exp(-i t (ω₁ + ω₂))

Proved end-to-end with no `sorry`.

## Support the research

This work is independently funded. If you would like to support continued
development of CGURD, contributions are accepted via Cash App:

**Cash App:** [$Gurd888](https://cash.app/$Gurd888)

Every contribution goes directly toward compute, tooling, and the time
required to formalize the framework.

## Structure

```
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
```

## Build

```
lake exe cache get
lake build
```

## License

MIT
