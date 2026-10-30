#!/bin/sh
# Build the note if a TeX toolchain exists; otherwise skip (exit 0).
set -e
cd "$(dirname "$0")/notes"
if command -v latexmk >/dev/null 2>&1; then
    latexmk -pdf -interaction=nonstopmode -halt-on-error poset_jks_research_note.tex
elif command -v pdflatex >/dev/null 2>&1; then
    pdflatex -interaction=nonstopmode -halt-on-error poset_jks_research_note.tex
    pdflatex -interaction=nonstopmode -halt-on-error poset_jks_research_note.tex
else
    echo "build.sh: no TeX toolchain (latexmk/pdflatex) found; skipping"
fi
