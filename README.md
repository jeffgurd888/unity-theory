lake build 2>&1 | tee build.log

rg -nw "sorry|admit" CGurd/ || echo "PASS: Zero placeholders."

cat > CGurd/_Check.lean <<'EOF'
import CGurd.FiniteSpectralTriple

#check @CGurd.piOp_def_check
#check @CGurd.order_zero_condition
#check @CGurd.buildDirac_self_adjoint
#check @CGurd.buildDirac_gamma_odd
#check @CGurd.UJ_mul_self
#check @CGurd.UJ_gamma_anticomm
EOF

lake build
rm CGurd/_Check.lean
