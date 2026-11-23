# Changes to the pinned zeta-lab sources

The source map records each file's original and ported SHA-256 hashes and the corresponding unchanged line ranges. Paths below are relative to this directory. The upstream revisions, copyright holders, and licenses are listed in [README.md](README.md).

- Selected the import closure for `RHHeight.Main`. Redirected local module imports to `RiemannMasullo.External.ZetaLab`, added provenance headers, and enabled upstream implicit-binder settings where needed. Declaration names are unchanged outside the Hardy Z namespace adjustment below.
- Replaced whole-library Mathlib imports with individual modules for complex powers, logarithmic derivatives, exponential estimates, and arithmetic tactics. Added the complex p-series import to `HardyFirstZero/EulerMaclaurin.lean`.
- Scoped the definitions and lemmas in `ZetaLean/HardyZ.lean` under `RiemannMasullo.External.ZetaLab` so the port can be imported alongside Mathlib’s `hardyZ` and `continuous_hardyZ`. Qualified the port’s gamma-conjugation lemma and updated the Hardy Z references in `HardyFirstZero/Spine.lean`.
- In `Zeta23/FromPNTPlus/ResidueCalcOnRectangles.lean`, expressed the additive combination using Mathlib’s `linear_combination` and `abel`. This removes the dependency on the upstream custom tactic.
- Rewrapped one sentence in the module comment in `Zeta23/Hypotheses.lean` so the project linter recognizes it as prose.
- In `Zeta23/Analytic/RectangleLogDeriv.lean`, unfolded set difference before applying the filter-intersection lemma.
- In `Zeta23/RvM/MainTerm.lean`, retained upstream lines 37–196 and 490, omitting the instance attribute for the removed Lie algebra import. In `Backlund.lean`, retained lines 32–35, 43–46, 59–104, 286, 349–398, and 419–420. In `ZetaGrowth.lean`, retained lines 35–53, 154–199, and 239–240. Adjusted their imports to the selected declarations. These excerpts avoid bringing in the unrelated growth and prime number theorem developments.

The strengthened cutoff statement adapted from `HardyTenZeros.ten_zeros_on_line_below_fifty` lives in the Chapter 10 proof file. Its source is credited in the project’s [attribution table](../ATTRIBUTION.md).
