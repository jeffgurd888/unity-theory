git add CGurd/Ternary.lean
git commit -m "Feat(CGurd/Ternary): prove trace factorization for the minimal XY chain

Adds the trace identity for the squared evolved coupling operator

  Tr[ (U_Y(t) · C)² ] = 2 · exp( -i t (ω₁ + ω₂) )

for the diagonal modular flow U_Y(t) = diag(e^{-i t ω₁}, e^{-i t ω₂}) and
the exchange matrix C = [[0,1],[1,0]]. Proved end-to-end with no sorry.

Interpretation: the trace is the sum of the two closed two-step loops
1 → 2 → 1 and 2 → 1 → 2, each contributing the combined phase
exp(-i t (ω₁ + ω₂)). The factor of 2 counts the two distinct paths."

git push origin main
