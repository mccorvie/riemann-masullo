# Tau Ceti

- **Source** — [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti)
- **Pinned commit** — [`8794ab329bb60340fa690a2902cf995f0571721b`](https://github.com/TauCetiProject/TauCeti/tree/8794ab329bb60340fa690a2902cf995f0571721b), built upstream with Lean v4.37.0-rc1
- **License** — Apache-2.0. [Upstream license](LICENSE)
- **Authors** — The Tau Ceti contributors, as credited in the source headers.
- **Intended use** — `introTrace_montel_of_bounded` in §1.4.3 ([#5655](https://github.com/mccorvie/riemann-masullo/issues/5655)). It applies Montel's theorem into `ℂ × ℂ` to select a common subsequence for two holomorphic families.

## Files taken

The upstream paths are the same as the paths below, prefixed by `TauCeti/`.
[Source map](SOURCE_MAP.json)

| File | Used for |
|---|---|
| [`Analysis/Normed/Group/LocallyBounded.lean`](Analysis/Normed/Group/LocallyBounded.lean) | `IsLocallyBoundedOn` and its bound lemmas, including the passage from a single bound to bounds on compact subsets. |
| [`Analysis/Complex/Conformal/NormalFamilies.lean`](Analysis/Complex/Conformal/NormalFamilies.lean) | Cauchy's estimates and the mean-value inequality give equicontinuity of locally bounded holomorphic families. |
| [`Topology/ContinuousMap/Ascoli.lean`](Topology/ContinuousMap/Ascoli.lean) | `ArzelaAscoli.isCompact_closure_range_of_equicontinuous` gives compact closure in the compact-open topology. |
| [`Analysis/Complex/Conformal/Montel/Precompact.lean`](Analysis/Complex/Conformal/Montel/Precompact.lean) | `isCompact_closure_range_of_isLocallyBoundedOn` combines equicontinuity and properness of the target to get compact closure. |
| [`Analysis/Complex/Conformal/Montel/Basic.lean`](Analysis/Complex/Conformal/Montel/Basic.lean) | `montel` selects a locally uniformly convergent subsequence and proves that its limit is holomorphic. |

The Montel and local-boundedness declarations are in `RiemannMasullo.External.TauCeti`.
The compact-open lemma retains its upstream namespace `ArzelaAscoli`.
[Modifications](MODIFICATIONS.md), [vendoring convention](../README.md)
