module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Uniform summability from a summable majorant

Mathlib's `SummableUniformlyOn` lacks a Weierstrass M-test entry point.  This file
records one: if the summands are dominated, pointwise on a set, by a summable
family of constants, then the series is uniformly summable on that set.
-/

public section

namespace RiemannMasullo

/-- Weierstrass M-test: if `g ξ p` is dominated by the summable family `u ξ`
for every `p ∈ K`, then `∑' ξ, g ξ p` converges uniformly on `K`. -/
theorem summableUniformlyOn_of_ge {ι : Type*} {X : Type*} {g : ι → X → ℝ} {u : ι → ℝ}
    {K : Set X} (hu : Summable u) (h : ∀ ξ (p : X), p ∈ K → ‖g ξ p‖ ≤ u ξ) :
    SummableUniformlyOn g K :=
  ⟨UniformOnFun.ofFun {K} (fun p ↦ ∑' ξ, g ξ p),
    hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr (tendstoUniformlyOn_tsum hu h)⟩

end RiemannMasullo
