module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Exponential sums in a logarithmic zero-free region

For frequencies satisfying Re z ≤ 1 − c/(1 + log(1 + |Im z|)), half-twisted
exponential sums have explicit savings on positive translates. The estimates
retain a summable weight before using decay in the height.
-/

public section

open Filter MeasureTheory Set

namespace RiemannMasullo

private theorem endpoint_height_balance {c K : ℝ} (hc : 0 < c) :
    ∃ n : ℕ, ∀ {x β y : ℝ}, 1 ≤ x → 0 ≤ y → β ≤ 1 - c / (1 + Real.log x) →
      Real.exp ((β - 1 / 2) * y) ≤
        Real.exp (n : ℝ) * x ^ n * Real.exp (y / 2 - K * Real.sqrt y) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (K ^ 2 / (4 * c))
  refine ⟨n, ?_⟩
  intro x β y hx hy hβ
  have hn' : K ^ 2 ≤ 4 * c * (n : ℝ) := by
    have h := (div_le_iff₀ (show 0 < 4 * c by positivity)).mp hn
    linarith
  let r := 1 + Real.log x
  have hr : 0 < r := by dsimp only [r]; linarith [Real.log_nonneg hx]
  have hnr := mul_le_mul_of_nonneg_right hn' (sq_nonneg r)
  have hq : K * Real.sqrt y * r ≤ c * y + (n : ℝ) * r ^ 2 := by
    calc
      _ ≤ c * Real.sqrt y ^ 2 + (n : ℝ) * r ^ 2 := by
        apply (mul_le_mul_iff_right₀ (show 0 < 4 * c by positivity)).mp
        nlinarith [sq_nonneg (2 * c * Real.sqrt y - K * r)]
      _ = _ := by rw [Real.sq_sqrt hy]
  have hbal : K * Real.sqrt y - (n : ℝ) * r ≤ c * y / r :=
    (le_div_iff₀ hr).mpr (by linarith [hq])
  have hxpow : x ^ n = Real.exp ((n : ℝ) * Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans_le hx)]
  rw [hxpow, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hzero := mul_le_mul_of_nonneg_right hβ hy
  change β * y ≤ (1 - c / r) * y at hzero
  rw [sub_mul, one_mul, div_mul_eq_mul_div] at hzero
  calc
    (β - 1 / 2) * y ≤ y / 2 - c * y / r := by linarith
    _ ≤ _ := by dsimp only [r] at hbal; linarith

/-- Rapid polynomial decay of the coefficients and a logarithmic right-edge gap give
every fixed square-root saving in the positive translation variable. -/
theorem expSum_norm_le_exp_sub_sqrt {ι : Type*} (z a : ι → ℂ) (w : ι → ℝ)
    (hw : Summable w) (hw₀ : ∀ i, 0 ≤ w i) {c : ℝ} (hc : 0 < c)
    (hz : ∀ i, (z i).re ≤ 1 - c / (1 + Real.log (1 + |(z i).im|)))
    (ha : ∀ n : ℕ, ∃ C > (0 : ℝ), ∀ i, ‖a i‖ * (1 + |(z i).im|) ^ n ≤ C * w i)
    (K : ℝ) :
    ∃ D ≥ (0 : ℝ), ∀ {y : ℝ}, 0 ≤ y → ∀ {L : ℂ},
      HasSum (fun i ↦ a i * Complex.exp ((z i - 1 / 2) * y)) L →
        ‖L‖ ≤ D * Real.exp (y / 2 - K * Real.sqrt y) := by
  obtain ⟨n, hn⟩ := endpoint_height_balance (K := K) hc
  obtain ⟨C, hC, hbound⟩ := ha n
  refine ⟨(∑' i, w i) * (C * Real.exp (n : ℝ)), mul_nonneg (tsum_nonneg hw₀) (mul_nonneg hC.le (Real.exp_pos _).le), ?_⟩
  intro y hy L hL
  let E := Real.exp (y / 2 - K * Real.sqrt y)
  have hterm (i : ι) : ‖a i * Complex.exp ((z i - 1 / 2) * y)‖ ≤
      w i * (C * Real.exp (n : ℝ)) * E := by
    have hn' := hn (le_add_of_nonneg_right (abs_nonneg (z i).im)) hy (hz i)
    rw [norm_mul, Complex.norm_exp, show (((z i - 1 / 2) * y : ℂ)).re = ((z i).re - 1 / 2) * y by
      simp [Complex.mul_re]]
    calc
      _ ≤ ‖a i‖ * (Real.exp n * (1 + |(z i).im|) ^ n * E) :=
        mul_le_mul_of_nonneg_left hn' (norm_nonneg _)
      _ = (‖a i‖ * (1 + |(z i).im|) ^ n) * (Real.exp n * E) := by ring
      _ ≤ (C * w i) * (Real.exp n * E) :=
        mul_le_mul_of_nonneg_right (hbound i) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      _ = _ := by ring
  rw [← hL.tsum_eq, ← tsum_mul_right, ← tsum_mul_right]
  exact (norm_tsum_le_tsum_norm hL.summable.norm).trans
    (hL.summable.norm.tsum_le_tsum hterm ((hw.mul_right _).mul_right _))

/-- A fixed share of the square-root decay absorbs the height weight. -/
private theorem sqrtHeight_polynomial (q : ℝ) (hq : 0 < q) :
    ∃ B > (0 : ℝ), ∀ t : ℝ, 0 ≤ t →
      (1 + t) ^ 2 ≤ B * Real.exp (q * Real.sqrt t) := by
  refine ⟨2 + 2 * (24 / q ^ 4), by positivity, ?_⟩
  intro t ht
  let p := Real.sqrt t
  have hp : 0 ≤ p := Real.sqrt_nonneg _
  have hp2 : p ^ 2 = t := Real.sq_sqrt ht
  have hpow := Real.pow_div_factorial_le_exp (q * p) (mul_nonneg hq.le hp) 4
  norm_num [Nat.factorial] at hpow
  have hp4 : p ^ 4 ≤ (24 / q ^ 4) * Real.exp (q * p) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hq 4)]
    calc
      p ^ 4 * q ^ 4 = (q * p) ^ 4 := by ring
      _ ≤ 24 * Real.exp (q * p) := by linarith
  have hone : 1 ≤ Real.exp (q * p) := Real.one_le_exp (mul_nonneg hq.le hp)
  calc
    (1 + t) ^ 2 = (1 + p ^ 2) ^ 2 := by rw [hp2]
    _ ≤ 2 + 2 * p ^ 4 := by nlinarith [sq_nonneg (p ^ 2 - 1)]
    _ ≤ 2 * Real.exp (q * p) + 2 * ((24 / q ^ 4) * Real.exp (q * p)) := by linarith
    _ = _ := by ring

/-- Either the logarithmic gap or the height decay pays the full translation cost. -/
private theorem sqrtHeight_cost (c q : ℝ) (hc : 0 < c) (hq : 0 < q)
    {t y : ℝ} (ht : 0 ≤ t) (hy : 0 ≤ y) :
    min (c / 4) (q / 2) * y / Real.log (2 + y) ≤
      c * y / (1 + Real.log (1 + t)) + q * Real.sqrt t := by
  let s := Real.log (2 + y)
  let r := 1 + Real.log (1 + t)
  have hs₂ : 1 / 2 ≤ s := by
    calc
      (1 / 2 : ℝ) ≤ Real.log 2 := by
        have h := Real.one_sub_inv_le_log_of_pos (by norm_num : 0 < (2 : ℝ))
        norm_num at h ⊢
        exact h
      _ ≤ s := Real.log_le_log (by norm_num) (by linarith)
  have hs : 0 < s := by linarith
  have hr : 0 < r := by
    have h := Real.log_nonneg (show 1 ≤ 1 + t by linarith)
    dsimp only [r]
    linarith
  by_cases htlow : Real.sqrt t ≤ 1 + y
  · have ht2 : t ≤ (1 + y) ^ 2 := by
      rw [← Real.sq_sqrt ht]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) htlow 2
    have hlog : Real.log (1 + t) ≤ 2 * s := by
      calc
        Real.log (1 + t) ≤ Real.log ((2 + y) ^ 2) :=
          Real.log_le_log (by positivity) (by nlinarith)
        _ = 2 * s := by rw [Real.log_pow]; norm_num [s]
    have hr' : r ≤ 4 * s := by dsimp only [r]; linarith
    calc
      min (c / 4) (q / 2) * y / s ≤ (c / 4) * y / s :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hy) hs.le
      _ = c * y / (4 * s) := by ring
      _ ≤ c * y / r := div_le_div_of_nonneg_left (mul_nonneg hc.le hy) hr hr'
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg hq.le (Real.sqrt_nonneg _))
  · have hq' : min (c / 4) (q / 2) ≤ q * s :=
      (min_le_right _ _).trans (by nlinarith [mul_le_mul_of_nonneg_left hs₂ hq.le])
    calc
      min (c / 4) (q / 2) * y / s ≤ q * y := by
        apply (div_le_iff₀ hs).mpr
        calc
          _ ≤ (q * s) * y := mul_le_mul_of_nonneg_right hq' hy
          _ = _ := by ring
      _ ≤ q * Real.sqrt t := mul_le_mul_of_nonneg_left (by linarith) hq.le
      _ ≤ _ := le_add_of_nonneg_left (div_nonneg (mul_nonneg hc.le hy) hr.le)

/-- A family of frequencies with a logarithmic zero-free gap and square-root height
decay gives a uniform subexponential saving at the right edge of the half-twisted strip. -/
theorem expSum_norm_le_exp_sub_div_log {ι : Type*} (z a : ι → ℂ) (w : ι → ℝ)
    (hw : Summable w) (hw₀ : ∀ i, 0 ≤ w i) {c κ A : ℝ}
    (hc : 0 < c) (hκ : 0 < κ) (hA : 0 < A)
    (hz : ∀ i, (z i).re ≤ 1 - c / (1 + Real.log (1 + |(z i).im|)))
    (ha : ∀ i, ‖a i‖ ≤ A * w i * (1 + |(z i).im|) ^ 2 *
      Real.exp (-κ * Real.sqrt |(z i).im|)) :
    ∃ d > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ y : ℝ, 0 ≤ y → ∀ L : ℂ,
      HasSum (fun i ↦ a i * Complex.exp ((z i - 1 / 2) * y)) L →
      ‖L‖ ≤ C * Real.exp (y / 2 - d * y / Real.log (2 + y)) := by
  let q := κ / 2
  have hq : 0 < q := half_pos hκ
  let d := min (c / 4) (q / 2)
  obtain ⟨B, hB, hpol⟩ := sqrtHeight_polynomial q hq
  refine ⟨d, lt_min (by positivity) (by positivity), A * B * (∑' i, w i),
    mul_nonneg (mul_nonneg hA.le hB.le) (tsum_nonneg hw₀), ?_⟩
  intro y hy L hsum
  let P := Real.exp (y / 2 - d * y / Real.log (2 + y))
  have hb (i : ι) : ‖a i * Complex.exp ((z i - 1 / 2) * y)‖ ≤ w i * (A * B * P) := by
    let t := |(z i).im|
    let R := ((z i).re - 1 / 2) * y
    have ht : 0 ≤ t := abs_nonneg _
    have hR : R ≤ y / 2 - c * y / (1 + Real.log (1 + t)) := by
      calc
        R ≤ ((1 - c / (1 + Real.log (1 + t))) - 1 / 2) * y :=
          mul_le_mul_of_nonneg_right (sub_le_sub_right (hz i) _) hy
        _ = _ := by ring
    have hcost := sqrtHeight_cost c q hc hq ht hy
    change d * y / Real.log (2 + y) ≤ _ at hcost
    have hex : q * Real.sqrt t + -κ * Real.sqrt t + R ≤ y / 2 - d * y / Real.log (2 + y) := by
      dsimp only [q] at hcost ⊢
      linarith
    rw [norm_mul, Complex.norm_exp]
    change ‖a i‖ * Real.exp (((z i - 1 / 2) * y).re) ≤ _
    have hre : (((z i - 1 / 2) * y).re) = R := by simp [R, Complex.mul_re]
    rw [hre]
    calc
      ‖a i‖ * Real.exp R ≤ (A * w i * (1 + t) ^ 2 * Real.exp (-κ * Real.sqrt t)) * Real.exp R :=
        mul_le_mul_of_nonneg_right (ha i) (Real.exp_pos _).le
      _ ≤ (A * w i * (B * Real.exp (q * Real.sqrt t)) * Real.exp (-κ * Real.sqrt t)) *
          Real.exp R :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpol t ht) (mul_nonneg hA.le (hw₀ i)))
            (Real.exp_pos _).le) (Real.exp_pos _).le
      _ = (w i * (A * B)) * Real.exp (q * Real.sqrt t + -κ * Real.sqrt t + R) := by
        rw [Real.exp_add, Real.exp_add]
        ring
      _ ≤ (w i * (A * B)) * P :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hex) (mul_nonneg (hw₀ i) (mul_nonneg hA.le hB.le))
      _ = _ := by ring
  have hmaj := hw.mul_right (A * B * P)
  have habs : Summable (fun i ↦ ‖a i * Complex.exp ((z i - 1 / 2) * y)‖) :=
    hmaj.of_nonneg_of_le (fun i ↦ norm_nonneg _) hb
  calc
    ‖L‖ = ‖∑' i, a i * Complex.exp ((z i - 1 / 2) * y)‖ := by rw [hsum.tsum_eq]
    _ ≤ ∑' i, ‖a i * Complex.exp ((z i - 1 / 2) * y)‖ := norm_tsum_le_tsum_norm habs
    _ ≤ ∑' i, w i * (A * B * P) := habs.tsum_le_tsum hb hmaj
    _ = _ := by rw [tsum_mul_right]; dsimp only [P]; ring

/-- Weighted endpoint integrability for a half-twisted exponential sum. Uniform
convergence after rescaling supplies measurability of the represented function. -/
theorem integrableOn_expSum_exp_sqrt_of_bounds {ι : Type*} (z a : ι → ℂ) (L : ℝ → ℂ)
    (hz : ∀ i, (z i).re ≤ 1) (ha : Summable (fun i ↦ ‖a i‖))
    (hL : ∀ y : ℝ, 0 ≤ y → HasSum (fun i ↦ a i * Complex.exp ((z i - 1 / 2) * y)) (L y))
    (hB : ∀ K : ℝ, ∃ D ≥ (0 : ℝ), ∀ y : ℝ, 0 ≤ y →
      ‖L y‖ ≤ D * Real.exp (y / 2 - K * Real.sqrt y)) (k : ℝ) :
    IntegrableOn (fun y : ℝ ↦ ‖L y‖ * Real.exp (-y / 2 + k * Real.sqrt y)) (Ici 0) := by
  let f (i : ι) (y : ℝ) := a i * Complex.exp ((z i - 1) * (max y 0 : ℝ))
  have hf (i : ι) : Continuous (f i) := by dsimp only [f]; fun_prop
  have hbound (i : ι) (y : ℝ) : ‖f i y‖ ≤ ‖a i‖ := by
    simp only [f, norm_mul, Complex.norm_exp]
    apply mul_le_of_le_one_right (norm_nonneg _)
    apply Real.exp_le_one_iff.mpr
    simpa [Complex.mul_re] using mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hz i)) (le_max_right y 0)
  have hcont := continuous_tsum hf ha hbound
  have heq (y : ℝ) (hy : 0 ≤ y) : (∑' i : ι, f i y) = L y * (Real.exp (-y / 2) : ℂ) := by
    rw [← (hL y hy).tsum_eq, ← tsum_mul_right]
    apply tsum_congr
    intro i
    rw [show f i y = a i * Complex.exp ((z i - 1) * y) by simp [f, max_eq_left hy],
      mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hm : AEStronglyMeasurable (fun y : ℝ ↦ ‖L y‖ * Real.exp (-y / 2 + k * Real.sqrt y))
      (volume.restrict (Ici 0)) := by
    apply (hcont.norm.mul (Real.continuous_exp.comp (continuous_const.mul Real.continuous_sqrt))).aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ici] with y hy
    change ‖∑' i : ι, f i y‖ * Real.exp (k * Real.sqrt y) = _
    simp only [heq y hy, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [mul_assoc, ← Real.exp_add]
  have he : IntegrableOn (fun y : ℝ ↦ Real.exp (-Real.sqrt y)) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    simpa only [Real.rpow_zero, one_mul, ← Real.sqrt_eq_rpow] using
      integrableOn_rpow_mul_exp_neg_rpow (s := 0) (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨D, hD, hb⟩ := hB (k + 1)
  apply (he.const_mul D).mono' hm
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ici] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
  calc
    _ ≤ (D * Real.exp (y / 2 - (k + 1) * Real.sqrt y)) *
        Real.exp (-y / 2 + k * Real.sqrt y) :=
      mul_le_mul_of_nonneg_right (hb y hy) (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

end RiemannMasullo
