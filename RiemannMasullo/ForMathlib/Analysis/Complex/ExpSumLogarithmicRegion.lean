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

/-- The product of log and iterated-log powers in the Coleman decay rate. -/
@[expose] noncomputable def colemanLogWeight (a x : ℝ) : ℝ :=
  Real.log (a + x) ^ (2 / 3 : ℝ) * Real.log (Real.log (16 + x)) ^ (1 / 3 : ℝ)

private theorem twoThirds_mul_oneThird {u : ℝ} (hu : 0 < u) :
    u ^ (2 / 3 : ℝ) * u ^ (1 / 3 : ℝ) = u := by
  rw [← Real.rpow_add hu]
  norm_num

private theorem half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h
  exact h

private theorem two_le_log_sixteen_add {x : ℝ} (hx : 0 ≤ x) :
    2 ≤ Real.log (16 + x) := by
  calc
    (2 : ℝ) ≤ 4 * Real.log 2 := by linarith [half_le_log_two]
    _ = Real.log 16 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
      norm_num
    _ ≤ _ := Real.log_le_log (by norm_num) (by linarith)

/-- Both logarithmic denominators are bounded away from zero, uniformly for nonnegative height. -/
theorem half_le_colemanLogWeight {a x : ℝ} (ha : 2 ≤ a) (hx : 0 ≤ x) :
    (1 / 2 : ℝ) ≤ colemanLogWeight a x := by
  have h₁ : (1 / 2 : ℝ) ≤ Real.log (a + x) :=
    half_le_log_two.trans (Real.log_le_log (by norm_num) (by linarith))
  have h₂ : (1 / 2 : ℝ) ≤ Real.log (Real.log (16 + x)) :=
    half_le_log_two.trans (Real.log_le_log (by norm_num) (two_le_log_sixteen_add hx))
  calc
    (1 / 2 : ℝ) = (1 / 2 : ℝ) ^ (2 / 3 : ℝ) * (1 / 2 : ℝ) ^ (1 / 3 : ℝ) :=
      (twoThirds_mul_oneThird (by norm_num)).symm
    _ ≤ _ := mul_le_mul (Real.rpow_le_rpow (by norm_num) h₁ (by norm_num))
      (Real.rpow_le_rpow (by norm_num) h₂ (by norm_num)) (by positivity)
      (Real.rpow_nonneg (by linarith) _)

private theorem log_le_twice {v u : ℝ} (hu : 0 < u) (h : u ≤ v ^ (2 : ℕ)) :
    Real.log u ≤ 2 * Real.log v := by
  simpa [Real.log_pow] using Real.log_le_log hu h

private theorem colemanLogWeight_le_twice {t y : ℝ} (ht : 0 ≤ t) (hy : 0 ≤ y) (hty : t ≤ y ^ 2) :
    colemanLogWeight 3 t ≤ 2 * colemanLogWeight 2 y := by
  have h₁ : Real.log (3 + t) ≤ 2 * Real.log (2 + y) :=
    log_le_twice (by linarith) (by nlinarith)
  have h₁t : 0 ≤ Real.log (3 + t) := Real.log_nonneg (by linarith)
  have h₁y : 0 ≤ Real.log (2 + y) := Real.log_nonneg (by linarith)
  have hLy := two_le_log_sixteen_add hy
  have hLt := two_le_log_sixteen_add ht
  have hL : Real.log (16 + t) ≤ 2 * Real.log (16 + y) :=
    log_le_twice (by linarith) (by nlinarith)
  have h₂ : Real.log (Real.log (16 + t)) ≤ 2 * Real.log (Real.log (16 + y)) := by
    apply log_le_twice (by linarith)
    exact hL.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hLy) (by linarith : 0 ≤ Real.log (16 + y))])
  have h₂t : 0 ≤ Real.log (Real.log (16 + t)) := Real.log_nonneg (by linarith)
  have h₂y : 0 ≤ Real.log (Real.log (16 + y)) := Real.log_nonneg (by linarith)
  calc
    colemanLogWeight 3 t ≤ (2 * Real.log (2 + y)) ^ (2 / 3 : ℝ) *
        (2 * Real.log (Real.log (16 + y))) ^ (1 / 3 : ℝ) :=
      mul_le_mul (Real.rpow_le_rpow h₁t h₁ (by norm_num)) (Real.rpow_le_rpow h₂t h₂ (by norm_num))
        (Real.rpow_nonneg h₂t _) (Real.rpow_nonneg (by positivity) _)
    _ = ((2 : ℝ) ^ (2 / 3 : ℝ) * 2 ^ (1 / 3 : ℝ)) * colemanLogWeight 2 y := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) h₁y, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) h₂y]
      unfold colemanLogWeight
      ring
    _ = _ := by rw [twoThirds_mul_oneThird (by norm_num : (0 : ℝ) < 2)]

/-- A square-root exponential in the height absorbs the polynomial loss and transfers a
logarithmic rate in the height to the corresponding rate in the translation parameter. -/
theorem colemanLogWeight_exp_sqrt_bound (c κ : ℝ) (hc : 0 < c) (hκ : 0 < κ) :
    ∃ d > (0 : ℝ), ∃ C > (0 : ℝ), ∀ t ≥ (0 : ℝ), ∀ y ≥ (0 : ℝ),
      (1 + t) ^ 2 * Real.exp (-κ * Real.sqrt t) *
        Real.exp (-c * y / colemanLogWeight 3 t) ≤
      C * Real.exp (-d * y / colemanLogWeight 2 y) := by
  let d := min (c / 2) (κ / 4)
  obtain ⟨C, hC, hpoly⟩ := sqrtHeight_polynomial (κ / 2) (half_pos hκ)
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  refine ⟨d, hd, C, hC, fun t ht y hy ↦ ?_⟩
  have hD : 0 < colemanLogWeight 3 t := lt_of_lt_of_le (by norm_num) (half_le_colemanLogWeight (by norm_num) ht)
  have hE₀ := half_le_colemanLogWeight (a := 2) (by norm_num) hy
  have hE : 0 < colemanLogWeight 2 y := lt_of_lt_of_le (by norm_num) hE₀
  have hrate : d * y / colemanLogWeight 2 y ≤ (κ / 2) * Real.sqrt t + c * y / colemanLogWeight 3 t := by
    by_cases hty : t ≤ y ^ 2
    · have hdD : d * colemanLogWeight 3 t ≤ c * colemanLogWeight 2 y := calc
        d * colemanLogWeight 3 t ≤ (c / 2) * (2 * colemanLogWeight 2 y) :=
          mul_le_mul (min_le_left _ _) (colemanLogWeight_le_twice ht hy hty) hD.le (by positivity)
        _ = _ := by ring
      have hstep := mul_le_mul_of_nonneg_right ((div_le_div_iff₀ hE hD).mpr hdD) hy
      calc
        d * y / colemanLogWeight 2 y = (d / colemanLogWeight 2 y) * y := by ring
        _ ≤ (c / colemanLogWeight 3 t) * y := hstep
        _ ≤ _ := by
          rw [show (c / colemanLogWeight 3 t) * y = c * y / colemanLogWeight 3 t by ring]
          exact le_add_of_nonneg_left (by positivity)
    · have hyd : y ≤ Real.sqrt t := Real.le_sqrt_of_sq_le (le_of_not_ge hty)
      have hde : d ≤ (κ / 2) * colemanLogWeight 2 y := calc
        d ≤ κ / 4 := min_le_right _ _
        _ = (κ / 2) * (1 / 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hE₀ (by positivity)
      calc
        d * y / colemanLogWeight 2 y = (d / colemanLogWeight 2 y) * y := by ring
        _ ≤ (κ / 2) * y := mul_le_mul_of_nonneg_right ((div_le_iff₀ hE).mpr hde) hy
        _ ≤ (κ / 2) * Real.sqrt t := mul_le_mul_of_nonneg_left hyd (by positivity)
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
  calc
    _ ≤ (C * Real.exp ((κ / 2) * Real.sqrt t)) * Real.exp (-κ * Real.sqrt t) *
        Real.exp (-c * y / colemanLogWeight 3 t) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hpoly t ht)
        (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = C * Real.exp (-((κ / 2) * Real.sqrt t + c * y / colemanLogWeight 3 t)) := by
      simp only [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ C * Real.exp (-d * y / colemanLogWeight 2 y) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ -(d * y / colemanLogWeight 2 y) := neg_le_neg hrate
        _ = _ := by ring

private theorem colemanLogWeight_le_sqrt {y : ℝ} (hy : 0 ≤ y) :
    colemanLogWeight 2 y ≤ 8 * (1 + Real.sqrt y) := by
  let L := Real.log (16 + y)
  have hL : 2 ≤ L := two_le_log_sixteen_add hy
  have hLp : 0 < L := by linarith
  have h₁ : Real.log (2 + y) ≤ L := Real.log_le_log (by linarith) (by linarith)
  have h₂ : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hLp).trans (by linarith)
  have h₂₀ : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hs : Real.sqrt (16 + y) ≤ 4 + Real.sqrt y := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith [Real.sq_sqrt hy, Real.sqrt_nonneg y]⟩
  calc
    colemanLogWeight 2 y ≤ L ^ (2 / 3 : ℝ) * L ^ (1 / 3 : ℝ) :=
      mul_le_mul (Real.rpow_le_rpow (Real.log_nonneg (by linarith)) h₁ (by norm_num))
        (Real.rpow_le_rpow h₂₀ h₂ (by norm_num)) (Real.rpow_nonneg h₂₀ _) (Real.rpow_nonneg hLp.le _)
    _ = L := twoThirds_mul_oneThird hLp
    _ ≤ (16 + y) ^ (1 / 2 : ℝ) / (1 / 2) := Real.log_le_rpow_div (by linarith) (by norm_num)
    _ = 2 * Real.sqrt (16 + y) := by rw [Real.sqrt_eq_rpow]; ring
    _ ≤ _ := by linarith [Real.sqrt_nonneg y]

/-- The Coleman profile of any positive exponential rate is integrable on the nonnegative
half-line. It is dominated globally by a constant times a stretched exponential. -/
theorem integrableOn_exp_neg_div_colemanLogWeight (δ : ℝ) (hδ : 0 < δ) :
    IntegrableOn (fun y : ℝ ↦ Real.exp (-δ * y / colemanLogWeight 2 y)) (Ici 0) := by
  have he : IntegrableOn (fun y : ℝ ↦ Real.exp (-(δ / 8) * Real.sqrt y)) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    simpa only [Real.rpow_zero, one_mul, ← Real.sqrt_eq_rpow] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (p := (1 / 2 : ℝ))
        (b := δ / 8) (by norm_num) (by norm_num) (by positivity)
  have hm : Measurable (fun y : ℝ ↦ Real.exp (-δ * y / colemanLogWeight 2 y)) := by
    unfold colemanLogWeight
    fun_prop
  apply (he.const_mul (Real.exp (δ / 8))).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ici] with y hy
  have hy₀ : 0 ≤ y := hy
  have hw : 0 < colemanLogWeight 2 y :=
    lt_of_lt_of_le (by norm_num) (half_le_colemanLogWeight (by norm_num) hy₀)
  have hrate : Real.sqrt y / 8 - 1 / 8 ≤ y / colemanLogWeight 2 y := calc
    _ ≤ y / (8 * (1 + Real.sqrt y)) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith [Real.sq_sqrt hy₀])
    _ ≤ _ := div_le_div_of_nonneg_left hy₀ hw (colemanLogWeight_le_sqrt hy₀)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    -δ * y / colemanLogWeight 2 y = -(δ * (y / colemanLogWeight 2 y)) := by ring
    _ ≤ -(δ * (Real.sqrt y / 8 - 1 / 8)) :=
      neg_le_neg (mul_le_mul_of_nonneg_left hrate hδ.le)
    _ = _ := by ring

/-- For a fixed Coleman region, square-root exponential decay of the coefficients
gives a uniform saving on every positive translate of the half-twisted sum.
The summable weight may include the full multiplicity of each frequency. -/
theorem expSum_norm_le_exp_sub_coleman {ι : Type*} (z a : ι → ℂ) (w : ι → ℝ)
    (hw : Summable w) (hw₀ : ∀ i, 0 ≤ w i) {c κ A : ℝ}
    (hc : 0 < c) (hκ : 0 < κ) (hA : 0 ≤ A)
    (hz : ∀ i, (z i).re ≤ 1 - c / colemanLogWeight 3 |(z i).im|)
    (ha : ∀ i, ‖a i‖ ≤ A * w i * (1 + |(z i).im|) ^ 2 *
      Real.exp (-κ * Real.sqrt |(z i).im|)) :
    ∃ d > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ y : ℝ, 0 ≤ y → ∀ L : ℂ,
      HasSum (fun i ↦ a i * Complex.exp ((z i - 1 / 2) * y)) L →
      ‖L‖ ≤ C * Real.exp (y / 2 - d * y / colemanLogWeight 2 y) := by
  obtain ⟨d, hd, B, hB, hbalance⟩ := colemanLogWeight_exp_sqrt_bound c κ hc hκ
  refine ⟨d, hd, (∑' i, w i) * (A * B), mul_nonneg (tsum_nonneg hw₀) (mul_nonneg hA hB.le), ?_⟩
  intro y hy L hL
  let E := Real.exp (y / 2 - d * y / colemanLogWeight 2 y)
  have hterm (i : ι) : ‖a i * Complex.exp ((z i - 1 / 2) * y)‖ ≤ w i * (A * B) * E := by
    let t := |(z i).im|
    have hrez : ((z i).re - 1 / 2) * y ≤ -c * y / colemanLogWeight 3 t + y / 2 := by
      have h := mul_le_mul_of_nonneg_right (hz i) hy
      change (z i).re * y ≤ (1 - c / colemanLogWeight 3 t) * y at h
      rw [sub_mul, one_mul, div_mul_eq_mul_div] at h
      calc
        ((z i).re - 1 / 2) * y = (z i).re * y - y / 2 := by ring
        _ ≤ (y - c * y / colemanLogWeight 3 t) - y / 2 := sub_le_sub_right h _
        _ = _ := by ring
    rw [norm_mul, Complex.norm_exp, show (((z i - 1 / 2) * y : ℂ)).re =
      ((z i).re - 1 / 2) * y by simp [Complex.mul_re]]
    calc
      _ ≤ (A * w i * (1 + t) ^ 2 * Real.exp (-κ * Real.sqrt t)) *
          Real.exp (-c * y / colemanLogWeight 3 t + y / 2) :=
        mul_le_mul (ha i) (Real.exp_le_exp.mpr hrez) (Real.exp_pos _).le ((norm_nonneg _).trans (ha i))
      _ = (A * w i * Real.exp (y / 2)) *
          ((1 + t) ^ 2 * Real.exp (-κ * Real.sqrt t) * Real.exp (-c * y / colemanLogWeight 3 t)) := by
        rw [Real.exp_add]
        ring
      _ ≤ (A * w i * Real.exp (y / 2)) * (B * Real.exp (-d * y / colemanLogWeight 2 y)) :=
        mul_le_mul_of_nonneg_left (hbalance t (abs_nonneg _) y hy)
          (mul_nonneg (mul_nonneg hA (hw₀ _)) (Real.exp_pos _).le)
      _ = _ := by
        dsimp only [E]
        rw [show y / 2 - d * y / colemanLogWeight 2 y = y / 2 + (-d * y / colemanLogWeight 2 y) by ring, Real.exp_add]
        ring
  rw [← hL.tsum_eq, ← tsum_mul_right, ← tsum_mul_right]
  exact (norm_tsum_le_tsum_norm hL.summable.norm).trans
    (hL.summable.norm.tsum_le_tsum hterm ((hw.mul_right _).mul_right _))

/-- Every positive integral moment of a nonnegative function with the Coleman
pointwise bound remains integrable after a strictly smaller exponential tilt.
Only measurability on the positive half-line is needed. -/
theorem integrableOn_pow_mul_exp_coleman_of_bound {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (Ici 0))) (hg₀ : ∀ y, 0 ≤ g y)
    {C d : ℝ}
    (hB : ∀ y ≥ (0 : ℝ), g y ≤ C * Real.exp (y / 2 - d * y / colemanLogWeight 2 y))
    (n : ℕ) (hn : 0 < n) (k : ℝ) (hk : k < d) :
    IntegrableOn (fun y : ℝ ↦ g y ^ n *
      Real.exp ((n : ℝ) * (-y / 2 + k * y / colemanLogWeight 2 y))) (Ici 0) := by
  have hδ : 0 < (n : ℝ) * (d - k) := mul_pos (by exact_mod_cast hn) (sub_pos.mpr hk)
  have he := integrableOn_exp_neg_div_colemanLogWeight _ hδ
  have hm : Measurable (fun y : ℝ ↦ Real.exp ((n : ℝ) * (-y / 2 + k * y / colemanLogWeight 2 y))) := by
    unfold colemanLogWeight
    fun_prop
  apply (he.const_mul (C ^ n)).mono' ((hg.pow n).mul hm.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ici] with y hy
  change ‖g y ^ n * Real.exp ((n : ℝ) * (-y / 2 + k * y / colemanLogWeight 2 y))‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (hg₀ _) _) (Real.exp_pos _).le)]
  calc
    _ ≤ (C * Real.exp (y / 2 - d * y / colemanLogWeight 2 y)) ^ n *
        Real.exp ((n : ℝ) * (-y / 2 + k * y / colemanLogWeight 2 y)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hg₀ _) (hB y hy) n) (Real.exp_pos _).le
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      congr 2
      ring

end RiemannMasullo
