#!/usr/bin/env bash
# Read the paper. Printed page numbers equal PDF page numbers.
#   scripts/paper.sh 59 62         pages 59 to 62 from the transcription (Markdown, formulas in LaTeX)
#   scripts/paper.sh --png 63      render page 63 (or a range) to .agent/pages/ and print the paths
#   scripts/paper.sh --raw 59 62   the old `pdftotext -layout` extraction of those pages
# The transcription (transcription/, contributed by @aadrianvv) keeps subscripts, accents, primes
# and bars, which the raw extraction drops. It is a reading aid, not an exact copy: spot checks
# found it right on almost every formula but not all. The PDF decides; look at the page image
# before you formalize a formula.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
pdf="$root/paper/the-music-of-the-primes.pdf"
case "${1:-}" in
  --png)
    first=${2:?first page}; last=${3:-$first}
    mkdir -p "$root/.agent/pages"
    pdftoppm -png -r 130 -f "$first" -l "$last" "$pdf" "$root/.agent/pages/p"
    ls "$root"/.agent/pages/p-*.png | awk -F'p-|[.]png' -v a="$first" -v b="$last" '$(NF-1)+0>=a && $(NF-1)+0<=b' ;;
  --raw)
    first=${2:?usage: paper.sh [--png|--raw] FIRST [LAST]}; last=${3:-$first}
    pdftotext -layout -f "$first" -l "$last" "$pdf" - ;;
  *)
    first=${1:?usage: paper.sh [--png|--raw] FIRST [LAST]}; last=${2:-$first}
    if ! ls "$root"/transcription/chapters/*.md >/dev/null 2>&1; then
      pdftotext -layout -f "$first" -l "$last" "$pdf" -; exit
    fi
    # Each chapter file marks its pages with `## PDF page N`. Print the pages asked for, in order.
    awk -v a="$first" -v b="$last" '
      /^## PDF page [0-9]+[ \t]*$/ { page = $4 + 0 }
      page >= a && page <= b { text[page] = text[page] $0 "\n" }
      END { for (p = a; p <= b; p++) if (p in text) printf "%s", text[p]; else printf "## PDF page %d\n\n(not in the transcription; use --raw or --png)\n\n", p }
    ' "$root"/transcription/chapters/*.md ;;
esac
