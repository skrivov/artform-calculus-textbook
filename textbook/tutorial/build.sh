#!/usr/bin/env bash
# Build the guide "Lean through Artform Calculus".
#   bash textbook/tutorial/build.sh [--png]
# 1. Lean checks the guide's files (lake build Tutorial). Every answer of
#    Lean that the guide quotes is pinned there with #guard_msgs.
# 2. tools/extract_listings.py cuts the printed listings from those files and
#    from the library, and scripts/status.py writes the appendix, the status
#    of every statement (tex/generated/status.tex, not committed).
# 3. pdflatex runs three passes, with bibtex after the first, in the book's
#    style (tex/book/). The book's numbers come from
#    tex/generated/book-labels-<n>.tex, which is appended to the .aux
#    before each pass.
# 4. On success the PDF is copied to textbook/lean-through-artform-calculus.pdf,
#    and the hash of every input is stored in tex/generated/inputs.sha256.
#    extract_listings.py --check compares that hash with the current sources.
# It fails on a LaTeX error, an overfull box or an undefined reference.
# --png also writes one PNG per page to build/guide-pages/.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
export PATH="$HOME/.elan/bin:$PATH"

cd "$ROOT"
lake build --wfail Tutorial
python3 -B "$HERE/tools/extract_listings.py"
mkdir -p build
lake env lean --run scripts/Report.lean > build/report.json
python3 -B scripts/status.py --tex "$HERE/tex/generated/status.tex"

cd "$HERE/tex"
N=guide
LABELS=$(ls generated/book-labels-*.tex)
export TEXINPUTS=".:book//:"
rm -f $N.aux
for pass in 1 2 3; do
  if [ -f $N.aux ]; then grep -h '^\\newlabel' "$LABELS" >> $N.aux; fi
  pdflatex -interaction=nonstopmode $N.tex > console.txt 2>&1 || true
  if [ $pass = 1 ]; then bibtex $N > bibtex.txt 2>&1 || true; fi
done

errors=$(grep -c '^!' $N.log || true)
overfull=$(grep -c '^Overfull' $N.log || true)
undefined=$(grep -c -E 'LaTeX Warning: (Reference|Citation).*undefined|There were undefined references' $N.log || true)
pages=$(pdfinfo $N.pdf | awk '/^Pages:/{print $2}')
echo "errors: $errors  overfull: $overfull  undefined: $undefined  pages: $pages"
if [ "$errors" != 0 ] || [ "$overfull" != 0 ] || [ "$undefined" != 0 ]; then
  grep -E -A3 '^!|^Overfull|undefined' $N.log | head -40
  exit 1
fi

cp $N.pdf "$ROOT/textbook/lean-through-artform-calculus.pdf"
python3 -B "$HERE/tools/extract_listings.py" --hash > generated/inputs.sha256
echo "wrote textbook/lean-through-artform-calculus.pdf ($pages pages)"

if [ "${1:-}" = "--png" ]; then
  mkdir -p "$ROOT/build/guide-pages"
  rm -f "$ROOT/build/guide-pages"/page-*.png
  pdftoppm -r 110 -png $N.pdf "$ROOT/build/guide-pages/page"
  echo "wrote build/guide-pages/"
fi
