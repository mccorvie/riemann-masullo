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

