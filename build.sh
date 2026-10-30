#!/bin/sh
# Build the notes if a TeX toolchain exists; otherwise skip (exit 0).
set -e
cd "$(dirname "$0")/notes"
for tex in poset_jks_research_note.tex poset_jks_theorem.tex; do
    if command -v latexmk >/dev/null 2>&1; then
        latexmk -pdf -interaction=nonstopmode -halt-on-error "$tex"
    elif command -v pdflatex >/dev/null 2>&1; then
        pdflatex -interaction=nonstopmode -halt-on-error "$tex"
        pdflatex -interaction=nonstopmode -halt-on-error "$tex"
    else
        echo "build.sh: no TeX toolchain (latexmk/pdflatex) found; skipping"
        exit 0
    fi
done
