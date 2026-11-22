# Transcription (reading aid)

A readable transcription of A. M. Masullo, *The Music of the Primes*, one file per chapter, with
the physical PDF page markers kept (`## PDF page N`; printed page number = PDF page number).

- Source: `paper/the-music-of-the-primes.pdf`, sha256
  `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5` (see `paper/README.md`).
  940 physical pages, including 11 blank pages (2, 8, 10, 56, 116, 154, 286, 380, 654, 822, 932).
- The manuscript belongs to its author. This transcription is **not** covered by this repository's
  Apache-2.0 license, exactly like `paper/`.
- **The PDF is the reference.** Before formalizing a statement, check it against the page image
  (`scripts/paper.sh --png N`). This text is for reading and searching; see *Status* below for what
  has and has not been verified.

## Status

| Check | Scope | Result |
|---|---|---|
| Page markers | all 940 pages | every page present once, in order |
| Prose text | all pages, word-aligned against the PDF text layer | every remaining difference of 2 or more words was checked: they are words set in math mode (`id`, `map`, `for all`), chapter titles and the figure placeholders |
| Math, glyph by glyph | all pages: every math glyph of the PDF (font, size, baseline) aligned with the LaTeX tokens | 97.3% of the 318,492 PDF math glyphs align one-to-one; every remaining alphabet / sub-superscript / glyph flag was compared with the page image and is listed in `tools/reviewed_flags.txt` |
| Math delimiters, LaTeX | all pages | every `$`/`$$` balanced; every formula outside the diagram blocks parses (KaTeX) |
| Footnotes, equation tags | all pages | every footnote and every `(X.Y.Z)` tag is under the page it is printed on |
| Bars and underlines | all pages, from the rules drawn in the PDF | present where printed, absent where not |
| Symbol counts | every page outside the diagrams: count of each maths symbol in the PDF and in the transcription | equal, apart from words set in maths and running heads; catches extra or missing symbols the alignment misses |
| Sub/superscript levels | every page's maths compiled; each glyph's size and raised/lowered position compared with the PDF | no glyph on the wrong level; notation such as `dt/t` vs `\frac{dt}{t}` and display vs inline style follows the print |
| Accents | every hat, tilde and check glyph of the PDF | same kind and same count on every page |
| φ/ϕ, ε/ϵ | every aligned glyph | the printed shape (the paper uses both phis) |
| ⇒ and ⇉ | every double-arrow glyph of the PDF (the text layer reports both as ⇒; the font tells them apart) | 136 `\Rightarrow` and 131 `\rightrightarrows`, same count on every page |
| ∅ shapes | every empty-set glyph of the PDF, by font | `\varnothing` and `\emptyset` as printed, same count on every page |
| Commutative diagrams | all 84 `latex` blocks | compared with the page image at 200 dpi; every block compiles with pdflatex + tikz-cd (`tools/diagrams.py`) |
| Page-by-page visual review | all 940 pages | every page read against its image at 200–300 dpi by AI reviewers (Claude, and Gemini on 485 pages; 420 pages read by both); ≈ 1,030 corrections on 354 pages, then all the checks above run again |
| Random sample | 45 tagged equations drawn at random before the visual review (43 exact), 50 more drawn after all corrections, then 100 more tagged equations and 40 untagged displays, each compiled and compared with the page image | second sample: 49 exact, the wrong one (an extra square) corrected; third sample: 140 of 140 agree. Over the last 190 equations that is 1 error, about 0.5% per equation (95% interval roughly 0.01–3%) |

**Not verified:** a symbol-by-symbol reading of every page by a person. The page-by-page review was
done by AI models, not by a person, and reviewers can miss things. About 3% of the
PDF's math glyphs do not align one-to-one with the transcription; most of those differences are
harmless (reading order of limits and fractions, words set in math, footnote numbers). Every
difference of one to three glyphs, at any level, and every run of three or more was looked at on the
page image (see `CHANGELOG.md` §10).

**How reliable it is.** The formulas have been compared with the PDF glyph by glyph in several
independent ways: the symbol counts on every page, the size and height of every
glyph, the alphabet of every letter, the limits of every operator, every arrow, accent and bar, and
every cross-reference number; the 88 diagrams too, by compiling each one and matching its glyphs
(letter, alphabet) against the glyphs of the page that the rest of the transcription does not
account for. Each kind of error found was then searched for on every page. After
the last corrections, 236 formulas drawn at random were compared by eye with the page image and all
were right. That bounds the error rate at about 1.3% per formula (95% confidence); the exhaustive
checks above suggest it is well below that. What could plausibly still be wrong:

- two symbols swapped where the PDF stores its glyphs in a different order from the LaTeX (limits
  of sums and integrals, numerators and denominators), so that the alignment reads the swap as a
  difference in reading order;
- in a diagram, two nodes or labels swapped with each other: the diagram check matches the glyphs,
  not their places (the diagrams were also compared with the page image twice, and the side of
  every label was checked against the PDF);
- the paper's own **misprints**, which are kept as printed on purpose (a formula can be wrong
  because the paper is).

Check any formula you formalize against the page image. Prose typography is collapsed except for italic paragraphs and italic section titles, which
follow the print; the four contour figures (pp. 596, 602, 605, 798) are redrawn in TikZ.

Run the checks yourself (from the repository root, needs `pip install pymupdf`):

```sh
python3 transcription/tools/check.py          # summary; "new" flags should be 0
python3 transcription/tools/check.py --list   # any flag not already reviewed
python3 transcription/tools/diagrams.py       # every diagram block compiles (needs pdflatex, tikz-cd)
```

Corrections made since the first version are listed in [`CHANGELOG.md`](CHANGELOG.md).
Errors found in the transcription go to `CHANGELOG.md` and the tracking issue — **never** to
`ERRATA.md`, which records errors in the paper and in the Lean formalization.

## Conventions

The text is verbatim: printed errors, placeholders, typos and unfinished passages are kept as
printed (for example "logy" on p. 648). Typography is mostly not reproduced, with two exceptions
that carry meaning: a paragraph set in italic in the print (the statement of a theorem, lemma,
proposition or corollary) is in `*…*`, and a paragraph set upright (a proof, a remark, a
definition in this paper) is not; and a formula displayed on its own line in the print is a
`$$` block. Mathematics is LaTeX:

| Print | LaTeX | Notes |
|---|---|---|
| Euler script (𝒮, 𝒟, 𝒪, 𝒰, …) | `\mathcal` | |
| formal script (ℰ, ℒ, ℋ, 𝒪 in the rsfs font, …) | `\mathscr` | the paper uses both scripts for the **same** letters with different meanings (O, L, E, H, B, M, …); they are kept apart |
| fraktur | `\mathfrak` | |
| bold upright (𝐑, 𝐂, 𝐀, category names such as **CGWH**) | `\mathbf` | |
| upright roman (H in H₀,cont, d in dx, PV, …) | `\mathrm` | |
| ∐ / ∏ / ⊗ / ⊕ | `\coprod` / `\prod` / `\otimes` / `\oplus` | never substituted for one another |
| overline, underline | `\overline`, `\underline` | |
| restriction χ\|_{C¹_F} | `\chi|_{C^1_F}` | |

Recurring symbols, for orientation: `G^1` is the kernel of the module (superscript 1),
`\mathcal S_{00}` has a subscript 00, `\mathcal S_{\mathrm E}` is 𝒮 with subscript roman E.

- **Commutative diagrams** are written as `tikzcd` in a fenced block, preceded by the equation tag
  on its own line, e.g.

  ````
  (4.4.1.3)

  ```latex
  \begin{tikzcd} ... \end{tikzcd}
  ```
  ````

  Nodes, arrows, directions, labels, `=`/`≃` marks, curved arrows and 2-cells follow the print.
  The side of its arrow that a label sits on follows the print where the PDF shows it (checked
  by matching label positions in the PDF against the compiled diagram). Every block must
  compile with pdflatex and tikz-cd (`tools/diagrams.py`): brace a label that contains a comma
  (`"{(a,b)}"`) and wrap a cell that starts with `[` in braces (`{[X/G]}`). GitHub does not render
  `tikzcd`; read the source, compile it, or look at the PDF.
- **Figures** (the contour pictures on pp. 596, 602, 605, 798) are redrawn as `tikzpicture` blocks
  (points, labels and the direction of each edge as printed), after the line
  `*[Figure, redrawn from the PDF, p. N:]*`.
- **Footnotes** are written `$^{n}$text` at the end of the page on which they are printed; the
  marker in the text is `$^{n}$` (separated from a preceding formula by one space).
- A sentence that runs across a page break is split at the break.
- Running heads are kept as the first line of each page.

## Contents

See [`chapters/README.md`](chapters/README.md) for the page range of each file.
