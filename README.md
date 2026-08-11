git commit -m "chore(methodology): enshrine 'no forced emergence' as Thet's core axiom

Establishes the formal evaluation convention for the Thet project.

- Codified the separation of Thet (concept) from θ (math) in `Thet/Foundation.lean`.
- Banned backward-reasoning: The algebra must be derived forward from the
  defined Thet structure, not retroactively adjusted to fit desired outputs.
- Replaced the `SU5_Weinberg_angle` theorem with an `Investigation` module.
  The final proof is now a conditional: `sin^2 theta_W = 3/8 IFF` specific
  trace normalizations hold. If they do not emerge naturally from Thet,
  Lean will report a failure to prove the theorem, which is a valid
  scientific result.
- Added a `METHODOLOGY.md` explaining that Lean is used as an unbiased
  evaluator, not a black-box theorem prover for a pre-cooked theory.

The project is now robust enough to survive being contradicted by its own
formal code.
"