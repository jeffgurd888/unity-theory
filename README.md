name: Build

on:
  push:
    branches: [ main, master ]
  pull_request:
    branches: [ main, master ]
  workflow_dispatch:

jobs:
  build:
    name: Build Lean project
    runs-on: ubuntu-latest
    timeout-minutes: 240

    steps:
      - name: Checkout repository
        uses: actions/checkout@v4

      - name: Read Lean toolchain
        id: toolchain
        run: |
          if [ -f lean-toolchain ]; then
            echo "value=$(cat lean-toolchain)" >> "$GITHUB_OUTPUT"
          else
            echo "::error::lean-toolchain file not found"
            exit 1
          fi

      - name: Install elan
        run: |
          curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
            | sh -s -- -y --default-toolchain "${{ steps.toolchain.outputs.value }}"
          echo "$HOME/.elan/bin" >> "$GITHUB_PATH"

      - name: Cache Lake build artifacts
        uses: actions/cache@v4
        with:
          path: |
            .lake/build
            .lake/packages
          key: lake-${{ runner.os }}-${{ steps.toolchain.outputs.value }}-${{ hashFiles('lake-manifest.json', 'lakefile.lean', 'lakefile.toml') }}
          restore-keys: |
            lake-${{ runner.os }}-${{ steps.toolchain.outputs.value }}-

      - name: Fetch Mathlib cache
        run: lake exe cache get

      - name: Build
        run: lake build

      - name: Check for sorry warnings
        run: |
          set -o pipefail
          if lake build 2>&1 | tee build.log | grep -i 'declaration uses.*sorry'; then
            echo "::error::Build contains sorry declarations"
            exit 1
          fi

      - name: Upload build log
        if: always()
        uses: actions/upload-artifact@v4
        with:
          name: build-log
          path: build.log
          retention-days: 7