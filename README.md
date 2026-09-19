## Quickstart: Automated Installation & Build

Run this single command in your terminal to automatically install the `elan` toolchain, clone the repository, download cached Mathlib binaries, and execute the full build[span_7](start_span)[span_7](end_span):

```bash
curl -sSfL [https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh](https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh) | sh -s -- -y && \
source "$HOME/.elan/env" && \
git clone [https://github.com/jeffgurd888/unity-theory.git](https://github.com/jeffgurd888/unity-theory.git) && \
cd unity-theory && \
lake exe cache get && \
lake build[span_8](start_span)[span_8](end_span)
