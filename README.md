#!/usr/bin/env bash
set -euo pipefail

echo "=== 1. Checking / Installing Elan Toolchain ==="
if ! command -v elan &> /dev/null; then
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y[span_1](start_span)[span_1](end_span)
    source "$HOME/.elan/env[span_2](start_span)"[span_2](end_span)
fi

export PATH="$HOME/.elan/bin:$PATH"

echo "=== 2. Fetching Mathlib Cache ==="
lake exe cache get[span_3](start_span)[span_3](end_span)

echo "=== 3. Building Lean Target ==="
lake build[span_4](start_span)[span_4](end_span)

echo "=== 4. Placeholder Verification ==="
grep -RIn --exclude-dir=build --exclude-dir=.git "sorry\|admit" src/ || true[span_5](start_span)[span_5](end_span)
