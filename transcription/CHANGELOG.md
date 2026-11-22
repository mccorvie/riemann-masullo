# Transcription corrections

Corrections to `chapters/*.md` after the first version (commits `bcd3f26`, `4de5bc7`). Every
correction was made against the pinned PDF: either mechanically from the PDF's own data (glyph
fonts, glyph baselines, drawn rules, text layer) or by comparing with the page image. Nothing here
corrects the paper itself: printed errors are kept verbatim. Errors in the paper (and in the Lean
formalization) are recorded in `ERRATA.md`; this file only records errors in the transcription.

585 of 940 pages changed in total (sections 1–6: first audit round, 559 pages; section 7: second round). Totals are approximate where many small edits were made by script.

## 1. Text placement and content

- Sentences crossing a page break had been finished on the earlier page (now split at the break):
  pp. 222→223, 500→501, 652→653.
- Passages duplicated across a page break (removed from the earlier page): pp. 428, 430, 592, 687,
  726, 791.
- Dropped text restored: p. 249 (the sentence "then 𝒮_I(𝐑) is the 𝐂-linear space of smooth
  functions … hence the lexicon *I*-exponential decay"), p. 818 (Remark D.3.5.2 was cut off
  mid-word).
- Footnotes filed under the wrong page: 14 → p. 805, 17–20 → p. 809, 21 → p. 810 (all had been
  under p. 811).
- Text not in the print, removed: "for the finite places" (p. 632), "[ing is ...]" (p. 641; the
  print breaks off at "The follow"), "[continues on p. 403]" (p. 402), "[page continues beyond
  418]" (p. 418), invented table headers (pp. 3–5, 9, 58, 587–588).
- Math delimiters: 19 unclosed `$` on pp. 71, 97, 107, 212, 340, 374, 379, 402, 461, 697, 762, 766,
  773, 779, 797; an unclosed `$$` on p. 792; four formulas that did not parse (pp. 288, 440, 445,
  491). Footnote syntax unified to `$^{n}$` (pp. 795, 797, 894, 926).

## 2. Subscripts and superscripts (≈ 470 corrections)

Checked against the baselines of the printed glyphs. Main patterns:

- `G^1` (the kernel of the module) had been written `G_1`: Ch. 9 (pp. 399–431), App. D (pp. 811–820),
  pp. 249, 403, 624 and others; likewise `g^1`, `\widehat{G^1}`.
- `\mathcal S_{00}` had been written `\mathcal S^{00}`: pp. 267–273, 335, 390–393.
- `\mathrm{Sets}_{\le\kappa}`, `\mathcal{CH}_{\le\kappa}`, `\mathbf C_{\le\nu}` (pp. 869–873);
  `\mathcal U^{\le(\underline n,\underline p)}` (pp. 271–273, 365); `X^{\mathrm{set}}` (pp. 852–853);
  `G^K`, `G^{[1/\Lambda,\Lambda]}` (p. 427); `\mathbf T^S` (p. 634); `H^0`/`H_0` (pp. 241, 284, 294);
  `L^1`, `L^2`, `H^p`, `H^2`, `S_p`, `S_2`, `E^2_{p,q}`, `D^m_t`, `C^j_m`, `z^m`, `c_n`.
- Structural: `\mathrm{PV}_{S_i}` had been `P_{V^{S_i}}` (pp. 481–482); `A\mathcal S^p(\mathbf C)` had
  been `A_{S_p}(C)` (pp. 368–372); `\mathcal S_{-1+I}` had been `\mathcal S^{-1+}_I` (pp. 345–348,
  361); `E^1_F` had been `E^{F'}_P` (p. 353); `C_F^{>1}` had been `C^1_{>1}` (p. 228); the
  restriction subscript in `\chi|_{J^1_{F,S}}` was missing (pp. 388–394).

## 3. Letter alphabets (≈ 3,400 glyphs)

Taken from the fonts of the PDF glyphs: plain letters that are script, calligraphic, fraktur, bold
or upright in print, and the reverse. The largest groups: 𝒮, 𝒰, ℰ, ℋ, ℒ written as plain letters
(Ch. 7 throughout, pp. 419–426, 456–472, 548–554); formal-script letters (rsfs) merged with Euler
script; script letters written as fraktur (pp. 333–339); `\mathcal{SE}` for `\mathcal S_{\mathrm E}`
(11 pages); `\mathcal{AS}` / `\mathcal{A_S(C)}` for `A\mathcal S(\mathbf C)`; upright `d`, `H`, `PV`
written italic; bold category names written roman.

## 4. Misread symbols (≈ 190, each checked against the page image)

Concentrated in pp. 240–263 (χ for ω throughout pp. 240–242, φ for ψ and ι, → for ≃, p for π, = for
≤ or ≥, d for δ, s for σ, 𝒯 for 𝓕), pp. 340–356 (X for χ, P for F, S_F for Σ_F, ≥ for ≤), pp.
475–512 (W^{s,2}_0 for W^{s,2}_a, ⊗ for ∏, φ for ρ, p for π, `k=0…∞` for `k≥0`; p. 505
re-transcribed), p. 574 (E^b_F for E^1_F). Single corrections: ∐ written as ∏ (p. 20) and as
`\widehat{\bigotimes}` (p. 293); p. 350 (a garbled exponent and three wrong letters); p. 645 (a
garbled chain of inequalities); p. 648 (signs in (B.7.1.16)); p. 652 (two sums merged into one);
p. 798 (limits of two integrals in (D.3.1.3) reversed); pp. 190, 216, 245, 262–263, 349, 369, 509,
683, 812, 821, 906.

## 5. Bars and underlines

502 overlines and 233 underlines added where the print has them (read from the rules drawn in the
PDF): χ̄ (≈ 190), μ̄, ⊗̄, π̄, γ̄, Ī, Ē, ω̄, Ū, the underlined tuples (n̲, p̲) and k̲. Bars that the print
does not have were removed or replaced by the printed accent (hat or tilde) on pp. 191, 194, 227,
233, 262–263, 270, 288, 301, 469, 530, 532, 553, 610, 634, 691, 778.

## 6. Diagrams and figures

- All 83 commutative diagrams (60 pages) are now `tikzcd` in fenced blocks (they had been in five
  formats: `tikzcd` inside `$$`, `tikzcd` in code fences, `array`, `CD`, and stacked `$$` blocks).
- Rebuilt from the page image: (7.3.1.20) p. 347 and (11.2.0.7) p. 486 had been flattened into lists
  of nodes (on p. 486 the pairings "→ 𝐂" had become "/ 𝐂"); (7.3.3.15) p. 361; (9.2.1.6) p. 405;
  (9.2.1.22) p. 408; (D.3.3.4) p. 806; the 2-cell diagrams on pp. 901, 903, 911–912.
- Arrows corrected: direction (pp. 201, 441, 486, 769), missing equality (pp. 441, 486), diagonal
  2-cell (p. 695), ∐ for ∏ (pp. 20, 390–393), 𝒮_E (p. 375), labels (pp. 709, 795, 891, 926).
- The four contour figures (pp. 596, 602, 605, 798) are replaced by a placeholder listing their labels.

## 7. Second audit round

Checks that the first round did not have, each run on every page against the PDF. 156 more pages
changed (585 of 940 in total since the first version).

- **Accents.** The kind of every accent in the PDF (hat, tilde, check, from the CMEX/MSBM/CMR
  glyphs) was compared with the transcription page by page, and every mismatch was checked on the
  page image (≈ 60 corrections):
  - the paper writes the *chosen set of representatives* with a tilde (G̃¹, C̃¹_F, J̃¹_{F,S},
    C̃_F) and the dual with a hat; about 25 tildes had been written as hats (pp. 135, 193, 203–207,
    266, 350, 440, 445, 453–455, 819);
  - accent glyphs that had been misread as letters: `{}^{b}\!\otimes` for ⊗̂ (pp. 198, 205, 207),
    `e\phi`, `e_a`, `e\mathrm{H}`, `\mathfrak{F}_{G^1}` for tildes (pp. 329, 611, 735, 736, 819);
  - hats that the print does not have (pp. 63, 181, 190, 256, 259, 261–262, 281, 290, 368,
    403–404, 416, 771, 791, 796) and hats it has that were missing (pp. 192, 226, 262, 349, 351, 749);
  - `\dot\gamma` for γ′ (p. 257).
- **Letters on the baseline written as subscripts, and the reverse.** `A_{\mathcal S}` for
  A𝒮 (≈ 100, pp. 304–409); vertical strips `\mathbf C(a,b)` for `\mathbf C_{(a,b)}`
  (pp. 321–330); `0+` for `0^+` (pp. 257–318, 608); `K(\gamma_1)`, `c(\rho,m)`, `F(g,x)`,
  `M(1/\Lambda,+\infty)`, `\mathcal S\mathrm{SE}`, `\mathscr B\mathrm{SOT}`, `\chi|J^1_{F,S}`,
  `\widetilde{E(U)}`, `C(1,\dots)` for the subscripted or superscripted forms (pp. 79, 219, 321–325,
  363, 367, 443, 475, 494–495, 593–594, 686); `Z_H`, `t^{s_c(\tau(t))}`, `3^p`, `F^\times g`
  for the printed `ZH`, `t^s c(\tau(t))`, `3p`, `F\times g` (pp. 327, 331, 477, 567, 624).
- **φ and ϕ, ε and ϵ.** The paper uses both shapes of phi (`\phi` ≈ 2,270 times, `\varphi`
  ≈ 1,670 times); 345 had the wrong one (55 pages, mostly Ch. 4, 9, 11 and App. B); 46 `\epsilon`
  for `\varepsilon`.
- **Strong duals and orthogonals** (pp. 240–249, 487): `\mathcal S(\mathbf R)'` for
  `\mathcal S(\mathbf R)'_\beta` (≈ 50) and `^\circ` or `'` for `^\perp` (≈ 20).
- **Formulas that differed from the print** (found from the glyphs that did not align): (B.7.2.14)
  had been rewritten rather than transcribed (p. 651); a missing `\sum_{m\ge 1}` in (B.7.2.6)
  (p. 650); a missing outer union in p. 272; the Tor map on p. 293; (7.3.2.5) and the
  O^×_{F,Σ_F−S′} subscripts (pp. 324, 351–355); a sentence on p. 353; p. 350
  (`H_{0,cont}(F^×,…)`); p. 816; `\mathrm{PV}_{S_0}` (p. 339); `\mathrm{HS}_{\Lambda_0}` (p. 488);
  `+\\infty` (p. 114).
- **Diagrams**, all 83 compared again with the page image at 200 dpi: a wrong node (p. 858: the
  print has Y), labels that the print does not have or has differently (pp. 769, 863, 891, 910,
  928), and the 2-cells φ that had been left out of the diagrams on pp. 910 and 913.
- **Random sample.** 45 tagged equations drawn at random after these corrections: 43 exact; the
  two wrong ones ((5.3.2.8) p. 246, (12.2.2.31) p. 513) are corrected.

## 8. Page-by-page visual review

Every one of the 940 pages was read against its page image (200 dpi, with 300–400 dpi crops of
small print) by AI reviewers: Claude on all pages and, independently, Gemini on 485 of them (420
pages were read by both, and their corrections were merged and compared). ≈ 1,030 corrections on
354 pages (663 of 940 pages changed in total since the first version, including the spot check below). Each correction was checked
against the PDF glyphs where they align (258 improved the alignment; the 16 that lowered it were
looked at on the image; 3 edits contradicted by the PDF fonts were reverted), word changes in prose against the PDF text layer,
and a random sample by eye. All the checks in the README were run again afterwards.

- **Sub- and superscripts** (≈ 200): exponents written on the baseline (`|S|-1` for `^{|S|-1}`,
  p. 325), indices dropped or added (`L^2` vs `L^2_\omega`, p. 178; `O_v` vs `O_{F_v}`, p. 65),
  `H^0_{\mathrm{cont}}` for the printed `H_{0,\mathrm{cont}}` (p. 181), `\Phi_{\gamma\mathbf Z}`
  for `\Phi_{\gamma^{\mathbf Z}}` (p. 209).
- **Letter alphabets** (≈ 190): calligraphic, script, bold, blackboard and upright letters that
  differed from the print, e.g. the upright d in `\mathrm{d}x`, `\mathcal A` vs `\mathscr A`.
- **Bars, hats, tildes and underlines** (≈ 160), e.g. the overlined (inductive) tensor product
  (pp. 198–200), `\bar n` for `\underline n` (p. 272), a bar over ω(g) and not over g (p. 178).
- **Arrows and signs** (≈ 110): `\hookrightarrow` and `\to` (pp. 246, 257), `\coprod` and
  `\bigsqcup`/`\sqcup` (pp. 388–391), `-` for `\setminus` (pp. 240, 243), missing minus signs
  (p. 194); and ⇉ (`\rightrightarrows`) for the groupoid brackets [𝒢 ⇉ X] and pairs of maps,
  which the PDF text layer reports as ⇒ (Appendix E, ≈ 100 places). After this, every
  double-arrow glyph of the PDF was matched by font (MSAM ⇉, CMSY ⇒) against the transcription:
  the same count on every page.
- **Primes** (≈ 30): `g'g` for `g''` (pp. 182, 187), primes added or dropped (pp. 203, 240–244,
  431, 928–929).
- **Prose** (≈ 100): typographic quotes for LaTeX backtick quotes (pp. 39–42), missing or extra
  words and spaces, and misprints of the paper kept as printed (e.g. "reflexivty", p. 662;
  "L’Hopital", p. 648; "7,5" in a citation, p. 757).
- **Citations and footnotes** (≈ 80): doubled opening brackets `[[` (pp. 195–207), bold citation
  keys, and footnote markers written as HTML `<sup>` instead of the `$^{1}$` convention.
- **Diagrams**: a 2-cell drawn as ⇔ in the print (p. 911) and arrows in Appendix E.
- **Empty-set sign.** The paper uses both empty-set signs (round `\varnothing` from the AMS font, 44 times;
  `\emptyset`, 4 times). 22 `\emptyset` for `\varnothing` on 15 pages, and the reverse on p. 832;
  now matched by font on every page.
- **Spot check.** 15 pages drawn at random (pp. 7, 81, 90, 172, 182, 186, 193, 296, 354, 365, 367,
  379, 552, 636, 824) were then read again against the image: no formula was wrong. Fixed on them:
  four displayed formulas that had been run into the text (pp. 365, 367, 379, 552), the italic
  of Proposition B.6.1.1 running on into the next paragraph (p. 636), and italics and punctuation
  on pp. 354, 824.

## 9. After the merge

From the maintainers' spot check in #2471 and the checks it suggested.

- **Hat over a subscripted symbol.** The print has $\widehat{\mathbf Q_p}$ (the hat over all of
  Q_p) where the transcription had `\widehat{\mathbf{Q}}_p`: p. 558 (twice) and p. 557 (once;
  the other `\widehat{\mathbf{Q}}_p` on p. 557 is as printed).
- **Misprints kept as printed.** p. 634: the print ends `1-\chi_v(\pi_v)q_v^{-s}|` with one
  stray bar, not `|\cdot|`; p. 733: the glyph after x in the excluded point is a ß (CMR), not a
  β, so `\{x\text{ß}_0\}`.
- **Diagrams that did not compile.** Every `latex` block was compiled with pdflatex and tikz-cd
  (`tools/diagrams.py`): 11 of 84 failed, because of commas inside arrow labels (pp. 276, 899,
  904) or a cell starting with `[`, which tikz-cd reads as options (pp. 20, 390, 391, 393, 930).
  Such labels are now braced (`"{(a,b)}"`), and such cells are wrapped in `{…}`. All 84 compile.
  The 11 were compared with the page image after rendering: labels drawn on the wrong side of
  their arrow are fixed (pp. 276, 899, 904).
- **Label sides.** For every diagram, the side of its arrow that each label is on was read from
  the PDF (the arrows are drawn as line segments, the labels are small text beside them) and
  compared with the compiled tikz-cd, with every arrow drawn in its own colour so that each
  label could be traced back to its `\arrow`. 34 labels were on the other side and are moved
  (pp. 200, 218, 236, 239, 270, 358, 415, 418, 437, 465, 546, 795, 812, 858, 863, 901, 911, 912);
  the diagrams with changes were compared with the page image after rendering.
- **Displayed formulas.** A formula displayed on its own line in the print had sometimes been
  run into the sentence. Display lines were found in the PDF (centred, made of maths glyphs, with
  extra space above and below) and matched with the transcription; 50 that were inline are now
  `$$` blocks (pp. 148–852), each checked on the page image first. Punctuation after the formula
  moves into the display, as printed.
- **Italic paragraphs.** Each paragraph was aligned word by word with the PDF text and its font
  (italic SFTI or upright SFRM) read off: 825 statement paragraphs that are italic in the print
  are now in `*…*`, and 157 paragraphs that were in `*…*` but are upright in the print (whole
  proofs on pp. 258–263, 796–800 and elsewhere) are not. 98.7% of paragraphs now agree with the
  print; the rest mix italic and upright. Literal `(*)` in citations is escaped as `(\*)`.


## 10. Follow-up checks

- **More displayed formulas.** A looser search for run-in displays, with every candidate checked on
  the page image, found 18 more: pp. 328, 334, 340, 363, 371, 422, 443, 446, 476 (two), 543, 549,
  553 (two), 637, 638, 728, 873.
- **More italic paragraphs.** Theorems whose numbers start with a letter (THEOREM A.5.1.3, Lemma
  D.3.6.1, …) had been skipped by the italics pass: 12 more statements are now in `*…*`. 8 more
  paragraphs that were in `*…*` but are upright in the print, mostly definitions (pp. 542, 593,
  600, 619, 685, 704), are not. 98.9% of paragraphs now agree with the print.
- **Unaligned math glyphs.** Every run of 3 or more PDF math glyphs that does not align with the
  transcription, outside the diagrams, was looked at. Apart from the display on p. 873, they are
  differences in how the glyphs are read, not in the formulas: words set in math ("for all",
  "holomorphic over"), `\varinjlim`/`\varprojlim`, limits and subscripts read in a different order,
  footnote numbers, and figure labels.
- **Small accents.** The print uses only the wide accents (`\widehat`, `\widetilde`, from the CMEX
  font; it has no CMR accent glyph at all). 244 `\hat` and 163 `\tilde` are now `\widehat` and
  `\widetilde`; with this, the number of hats and of tildes on every page matches the PDF, apart
  from accents inside diagrams.
- **Hat or tilde over a subscripted symbol.** TeX picks the widest accent that fits what it covers,
  so the size of the printed hat (small, medium or large CMEX glyph) tells whether it covers the
  letter alone or the letter with its subscript. Each of the 680 accents over a one-letter base
  with a subscript was paired with its PDF glyph: 495 agree with the transcription, 167 cannot be
  told apart this way (both readings give the same hat), and the 5 that disagreed were looked at
  on the page image: 2 are fixed (`\widehat{F}_v`, p. 619), the other 3 (pp. 391, 558) are right
  as they are.
- **Section titles.** Sub-subsection titles (four-part numbers such as 9.3.3.2 or B.5.3.4) are
  italic in the print: 40 that were upright and 39 that were bold are now `*…*`, like the other
  132. One statement on p. 493 that the print italicizes after a colon is marked too.
- **Figures.** The four contour figures (pp. 596, 602, 605, 798) are redrawn as TikZ pictures, with
  the points, labels and direction of every edge as printed, instead of a placeholder;
  `tools/diagrams.py` now compiles them with the diagrams (88 blocks).
- **Accents in diagrams.** With the diagram blocks included, the number of hats and of tildes
  matches the PDF on every page.
- **Second random sample.** 50 tagged equations drawn at random from the 2,261 (seed 20261122)
  after all the corrections above, each compiled and compared with the page image symbol by
  symbol: 49 exact. The wrong one, (9.2.1.15) p. 407, had `|\phi(t)(\log t)^k|^2` where the print
  has no square: a misprint of the paper silently "corrected" in the transcription, now as
  printed. One displayed formula ((B.4.4.9), p. 621) had its tag on the second line instead of the
  first. Read this as a residual error rate of about 2% per equation (95% interval roughly
  0.05–11%).
- **What the sample suggested.** The glyph alignment never flagged a single extra or missing glyph
  (it only reports substitutions), which is how the square in (9.2.1.15) got through. All
  one- and two-glyph insertions and deletions in the alignment were therefore listed and those
  in sub- and superscripts and the operators (−, +, ′, ×, ⊂, …) were reviewed: apart from
  (9.2.1.15), they are reading order, `≠`/`∉` read as `=`/`∈`, footnote numbers and numbers set
  in text, except `S\setminus S_0` for the printed `S-S_0` (p. 242), now fixed. Tags on the
  continuation line of a multi-line display were also listed: two more ((B.4.2.4) p. 615,
  (B.4.4.8) p. 621), now on the first line as printed.

- **Symbol counts per page.** Each maths symbol was counted on every page of the PDF and of the
  transcription (running heads and diagram pages left out), which catches an extra or missing
  symbol whatever the reading order. Two formulas had more than the print: on p. 244 the Mackey
  dual was written `F_\tau'=F_{\tau(F',F)}'` where the print has only `F'_{\tau(F',F)}`, and on
  p. 354 a trailing `\subset \mathbf A_{F,S}` had been added to the definition of
  `\widetilde{Q}_Y`. Both are now as printed.
- **Third random sample.** 100 more tagged equations (seed 777) and 40 untagged displays (seed
  2026112202), each compiled and compared with the page image: all 140 agree with the print,
  apart from where a multi-line display breaks its lines.
- **Sub- and superscript levels.** Every page's maths was compiled and each glyph's size (normal,
  script, scriptscript) and position (raised or lowered) compared with the same glyph in the PDF.
  This finds structure the glyph alignment cannot see, such as an exponent ending one symbol
  early. No formula had a glyph on the wrong level. It did find notation that differs from the
  print: `\frac{\mathrm d t}{t}` where the print has `\mathrm dt/t` (pp. 178–180, 16 places)
  and the other way round (pp. 400, 424, 428, 5 places); `[F:\mathbf Q]/2` and
  `|a_m|/(m^{\sigma+c}\ldots)` printed as fractions (pp. 642, 644, 645). All now as printed.
- **Displays run into the text, third pass.** The same comparison showed formulas set in display
  style in the print but inline in the transcription, so the search for run-in displays was redone
  on every centred line of maths in the PDF, matched glyph by glyph with the transcription. Every
  candidate was checked on the page image: 89 more formulas displayed in the print are now `$$`
  blocks (pp. 74–854, most of them in Chapters 5–7 and 9). Where one printed display holds two
  formulas separated by a comma (pp. 363, 473), they are one block.
- **Limits of operators.** For every big operator (∑, ∏, ∫, ⋃, ⨁, …) and every lim, sup, inf,
  max, min and det, the glyphs set as its limits were read off the PDF and off the compiled
  transcription and compared page by page. Two inductive limits had a subscript the print does not
  have: `\varinjlim_i` twice on p. 685 and `\varinjlim_m` on p. 816, now plain `\varinjlim` as
  printed. With the big operators read from their font codes (4,254 operators in all), three
  more differ in notation only: `\prod_j z_j^{a_j}` on p. 628 is `\prod z_j^{a_j}`, inline, in the
  print; the print has a small `\otimes_{v\notin S}` on p. 39 and a large `\bigotimes_{v\notin S'}`
  on p. 352, the other way round from the transcription. All three now as printed. The rest agree.
  The reverse check, formulas displayed in the transcription but run into the text in the print,
  found only p. 628.
- **Cross-references.** Every dotted number in the text (equation, theorem and section numbers,
  and the numbers in citations such as `[DE, Thm. 3.6.3]`) was compared page by page with the PDF
  text: they all agree. The only differences are footnote marks that the PDF text runs into the
  preceding number.
- **Inline formulas.** 96 inline formulas of 40 or more characters, drawn at random (seed 4242),
  were compiled and compared with the page image: all 96 agree with the print.
- **Small differences at every level.** With every page's maths compiled, each glyph of the PDF
  was aligned with the compiled transcription (same fonts on both sides), and every insertion,
  deletion or replacement of up to three glyphs was listed, on the baseline as well as in scripts
  (the earlier pass had only looked at scripts and operators). After removing what is set as text
  in one and as maths in the other (footnote marks, `§`, `id`, punctuation, running heads), each
  remaining case was checked on the page image. Fixed:
  - p. 349: `\sigma(E', E)` where the print has `\sigma(E, E')` (the prime was on the wrong
    argument of the weak topology);
  - p. 353: `|\tau(t)|_{v_0}` where the print has `|\xi\tau(t)|_{v_0}`;
  - p. 553: `\to` where the print has `\hookrightarrow`;
  - p. 449: `m'_{k',j'}` (twice) where the print has `m_{k',j'}`;
  - p. 244: `(F_k)'_\beta` where the print has `(F'_k)_\beta` (one of four places; the other
    three are as printed);
  - p. 327: the prime on the restricted product now on the `\prod`, as printed;
  - pp. 540, 556: `\sqcup` where the print has `\coprod`;
  - p. 631: `\mathrm dx_1\cdot\ldots\cdot\mathrm dx_N` where the print has `\mathrm dx_1\cdots\mathrm dx_N`.
- **Following up each kind of error.** Every kind found was searched for across the whole
  transcription. Insertions of four or more glyphs in the transcription that are not in the print
  (the kind on pp. 244 and 354): none apart from text set as maths, and the two equation numbers
  on p. 22 that were written into the formula as `\mathrm{(1.3.1.1)}` instead of `\tag`, now
  tags. Arrows (`\hookrightarrow`, `\mapsto`, `\to` and the others), counted on every page: they
  agree outside the diagrams. `\sqcup`: no other occurrence.
- **Diagrams, glyph by glyph.** Each of the 88 diagram blocks was compiled on its own (on a page
  wide enough for the widest one) and its glyphs, with their alphabet, were matched against the
  glyphs of the PDF page that the rest of the transcription does not account for. Every glyph of
  every diagram is in the print, and every print glyph left over is accounted for: running heads,
  numbers set in maths in the text ("2-morphism", "1-parameter"), `\mathrm{id}`/`\mathrm{Hom}`
  set in the text font in the print. The three diagrams where a glyph count was off by one
  (pp. 273, 276, 361) were compared with the page image again and agree.
- **Punctuation at the end of displays.** The same pass showed two displays on p. 270 without the
  full stop that ends them in the print. Every display was then checked for a trailing full stop
  or comma, against the print: also fixed, p. 371 (`,` for the printed `.`) and p. 650 (a comma
  that is not in the print).
