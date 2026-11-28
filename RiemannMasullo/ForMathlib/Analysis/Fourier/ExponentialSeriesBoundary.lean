module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-! # Boundary frequencies of an absolutely convergent exponential series

For coefficients with summable norms, the frequencies strictly to the left of the
normalizing line give a contribution tending to zero. Their real parts may accumulate at
the line. The terms on the line retain their oscillating phases. -/

public section

open Filter
open scoped Topology

namespace RiemannMasullo

/-- After exponential normalization, the sum differs from its boundary Fourier series
by a function tending to zero. Only indices with nonzero coefficient require a real-part bound. -/
theorem tendsto_normalizedExpSeries_sub_boundary {ι : Type*} (a z : ι → ℂ) (b : ℝ)
    (ha : Summable fun i ↦ ‖a i‖) (hz : ∀ i, a i ≠ 0 → (z i).re ≤ b) :
    Tendsto (fun t : ℝ ↦ (∑' i, a i * Complex.exp ((z i - b) * t)) -
      ∑' i : {j // (z j).re = b}, a i * Complex.exp (Complex.I * (z i).im * t)) atTop (𝓝 0) := by
  let s : Set ι := {i | (z i).re = b}
  let f (t : ℝ) (i : ι) := a i * Complex.exp ((z i - b) * t)
  have hnorm (t : ℝ) (i : ι) :
      ‖f t i‖ = ‖a i‖ * Real.exp (((z i).re - b) * t) := by
    simp [f, Complex.norm_exp]
  have hbound {t : ℝ} (ht : 0 ≤ t) (i : ι) : ‖f t i‖ ≤ ‖a i‖ := by
    by_cases hi : a i = 0
    · simp [f, hi]
    · rw [hnorm]
      exact mul_le_of_le_one_right (norm_nonneg _)
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hz i hi)) ht))
  have hinterior (i : ↑sᶜ) : Tendsto (fun t : ℝ ↦ f t i) atTop (𝓝 0) := by
    by_cases hi : a i = 0
    · simp [f, hi]
    · have hne : (z i).re ≠ b := i.property
      have hneg : (z i).re - b < 0 := sub_neg.mpr (lt_of_le_of_ne (hz _ hi) hne)
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simp_rw [hnorm]
      simpa [Function.comp_def] using
        (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hneg)).const_mul ‖a i‖
  have hlim : Tendsto (fun t : ℝ ↦ ∑' i : ↑sᶜ, f t i) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (f := fun t (i : ↑sᶜ) ↦ f t i)
      (g := fun _ ↦ 0) (ha.subtype (· ∈ sᶜ)) hinterior
      ((eventually_ge_atTop (0 : ℝ)).mono fun _ ht i ↦ hbound ht i)
    simpa only [tsum_zero] using h
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hsum : Summable (f t) := ha.of_norm_bounded (hbound ht)
  have hline (i : s) : f t i = a i * Complex.exp (Complex.I * (z i).im * t) := by
    have hre : (z i).re = b := i.property
    have heq : z i - b = Complex.I * (z i).im := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hre]
    simp only [f, heq]
  change (∑' i : ↑sᶜ, f t i) = (∑' i, f t i) -
    ∑' i : s, a i * Complex.exp (Complex.I * (z i).im * t)
  rw [← hsum.tsum_subtype_add_tsum_subtype_compl s, tsum_congr hline]
  abel

/-- Taking real parts preserves the normalized boundary extraction. -/
theorem tendsto_re_normalizedExpSeries_sub_boundary {ι : Type*} (a z : ι → ℂ) (b : ℝ)
    (ha : Summable fun i ↦ ‖a i‖) (hz : ∀ i, a i ≠ 0 → (z i).re ≤ b) :
    Tendsto (fun t : ℝ ↦ (∑' i, a i * Complex.exp ((z i - b) * t)).re -
      (∑' i : {j // (z j).re = b}, a i * Complex.exp (Complex.I * (z i).im * t)).re)
      atTop (𝓝 0) := by
  simpa [Function.comp_def, Complex.sub_re] using
    (Complex.continuous_re.tendsto _).comp (tendsto_normalizedExpSeries_sub_boundary a z b ha hz)

end RiemannMasullo
