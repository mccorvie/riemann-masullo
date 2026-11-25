module

public import RiemannMasullo.ForMathlib.Analysis.Complex.ExpSumGrowth
import Mathlib.Tactic

/-! # Coefficientwise lower growth of exponential sums on a half-line

A nonzero coefficient forces arbitrarily late values exceeding every fixed multiple
of an exponential with smaller real exponent. Only a common upper bound on the
real parts of the frequencies is needed.
-/

public section

open Filter Set Topology

namespace RiemannMasullo

private theorem expSum_discrete_sub_real {ι : Type*} (w : ι → ℂ) (M : ℝ)
    (hd : ∀ z : ℂ, ∀ᶠ u in 𝓝[≠] z, u ∉ range w) (z : ℂ) :
    ∀ᶠ u in 𝓝[≠] z, u ∉ range (fun i ↦ w i - (M : ℂ)) := by
  have ht : Tendsto (fun u : ℂ ↦ u + M) (𝓝[≠] z) (𝓝[≠] (z + M)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨((continuous_id.add continuous_const).tendsto z).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu using fun he ↦ hu (add_right_cancel he)
  filter_upwards [ht.eventually (hd (z + M))] with u hu
  rintro ⟨i, rfl⟩
  exact hu ⟨i, (sub_add_cancel (w i) (M : ℂ)).symm⟩

/-- Every nonzero coefficient of an absolutely convergent exponential sum forces
arbitrarily late values above every multiple of `exp (c * y)` when `c` is smaller
than the real part of its frequency. The frequencies may be bounded above by any
real number. -/
theorem frequently_exp_lt_norm_of_hasSum_exp {ι : Type*} (w b : ι → ℂ)
    (hw : Function.Injective w) (hd : ∀ z : ℂ, ∀ᶠ u in 𝓝[≠] z, u ∉ range w)
    {M : ℝ} (hM : ∀ i, (w i).re ≤ M) (S : ℝ → ℂ)
    (hS : ∀ y : ℝ, 0 ≤ y → HasSum (fun i ↦ b i * Complex.exp (w i * y)) (S y))
    {i : ι} (hi : b i ≠ 0) {c : ℝ} (hc : c < (w i).re) (C : ℝ) :
    ∃ᶠ y in atTop, C * Real.exp (c * y) < ‖S y‖ := by
  by_contra hf
  have htail : ∀ᶠ y : ℝ in atTop, ‖S y‖ ≤ C * Real.exp (c * y) := by
    simpa only [not_lt] using not_frequently.mp hf
  obtain ⟨T, hT⟩ := eventually_atTop.mp htail
  let A := max T 0
  have hA : 0 ≤ A := le_max_right _ _
  have hAT : T ≤ A := le_max_left _ _
  let v := fun j ↦ w j - (M : ℂ)
  let a := fun j ↦ b j * Complex.exp (w j * A)
  let G := fun y : ℝ ↦ S (A + y) * Complex.exp (-(M : ℂ) * y)
  have hG (y : ℝ) (hy : 0 ≤ y) : HasSum (fun j ↦ a j * Complex.exp (v j * y)) (G y) := by
    convert (hS (A + y) (add_nonneg hA hy)).mul_right (Complex.exp (-(M : ℂ) * y)) using 1
    ext j
    dsimp only [a, v]
    simp only [mul_assoc, ← Complex.exp_add, Complex.ofReal_add]
    congr 2
    ring
  have hbound (y : ℝ) (hy : 0 ≤ y) :
      ‖G y‖ ≤ (C * Real.exp (c * A)) * Real.exp ((c - M) * y) := by
    calc
      ‖G y‖ = ‖S (A + y)‖ * Real.exp (-M * y) := by
        simp [G, Complex.norm_exp, Complex.mul_re]
      _ ≤ (C * Real.exp (c * (A + y))) * Real.exp (-M * y) :=
        mul_le_mul_of_nonneg_right (hT _ (hAT.trans (le_add_of_nonneg_right hy))) (Real.exp_pos _).le
      _ = _ := by
        simp only [mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hv : Function.Injective v := fun _ _ he ↦ hw (sub_left_inj.mp he)
  have hvM (j : ι) : (v j).re ≤ 1 / 2 := by
    change (w j - (M : ℂ)).re ≤ 1 / 2
    rw [Complex.sub_re, Complex.ofReal_re]
    linarith [hM j]
  have hai := eq_zero_of_hasSum_exp_of_norm_le v a hv (expSum_discrete_sub_real w M hd)
    hvM (hS A hA).summable G hG hbound i (by simpa only [v, Complex.sub_re, Complex.ofReal_re,
      sub_lt_sub_iff_right] using hc)
  exact (mul_ne_zero hi (Complex.exp_ne_zero _)) hai

/-- For summable coefficients the exponential sum itself exceeds
`C * exp (c * y)` arbitrarily late at each exponent below a contributing frequency. -/
theorem frequently_exp_lt_norm_tsum_exp {ι : Type*} (w b : ι → ℂ)
    (hw : Function.Injective w) (hd : ∀ z : ℂ, ∀ᶠ u in 𝓝[≠] z, u ∉ range w)
    {M : ℝ} (hM : ∀ i, (w i).re ≤ M) (hb : Summable b)
    {i : ι} (hi : b i ≠ 0) {c : ℝ} (hc : c < (w i).re) (C : ℝ) :
    ∃ᶠ y : ℝ in atTop, C * Real.exp (c * y) < ‖∑' j, b j * Complex.exp (w j * y)‖ := by
  apply frequently_exp_lt_norm_of_hasSum_exp w b hw hd hM _ _ hi hc C
  intro y hy
  apply Summable.hasSum
  apply (hb.norm.mul_right (Real.exp (M * y))).of_norm_bounded
  intro j
  rw [norm_mul, Complex.norm_exp, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hM j) hy))
    (norm_nonneg _)

end RiemannMasullo
