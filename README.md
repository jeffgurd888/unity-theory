#!/usr/bin/env bash
set -euo pipefail

echo "=== Setting up Lean 4 toolchain and environment ==="
if ! command -v elan &> /dev/null; then
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y[span_1](start_span)[span_1](end_span)
    source "$HOME/.elan/env[span_2](start_span)"[span_2](end_span)
fi

export PATH="$HOME/.elan/bin:$PATH"

echo "=== Fetching Mathlib dependencies ==="
lake exe cache get[span_3](start_span)[span_3](end_span)

echo "=== Building Lean 4 target ==="
lake build[span_4](start_span)[span_4](end_span)

echo "=== Verification ==="
lake build
grep -RIn --exclude-dir=build --exclude-dir=.git "sorry\|admit" src/ CGurd/ || true[span_5](start_span)[span_5](end_span)

#### Automated Installation from Commit

To clone, checkout a specific commit, and perform an automated build in one command[span_7](start_span)[span_7](end_span):

```bash
git clone [https://github.com/jeffgurd888/unity-theory.git](https://github.com/jeffgurd888/unity-theory.git) && \
cd unity-theory && \
git checkout <COMMIT_HASH> && \
chmod +x install.sh && \
./install.sh

