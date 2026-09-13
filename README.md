#!/usr/bin/env bash
set -e

echo "==> Building PDF"
pdflatex -interaction=nonstopmode main.tex
pdflatex -interaction=nonstopmode main.tex

echo "==> Converting to EPUB"
pandoc main.tex \
  --from=latex \
  --to=epub3 \
  --toc --toc-depth=2 \
  --metadata title="The Theoretical Foundations of the Correspondence" \
  --metadata author="Jeffrey Michael Gurd" \
  --metadata lang="en" \
  --metadata publisher="Correspondence Press" \
  --epub-cover-image=cover/front.png \
  -o correspondence.epub

echo "==> Done: main.pdf and correspondence.epub"