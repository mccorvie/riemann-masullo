module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Compact smooth interpolation of Fourier samples on a lattice -/

public noncomputable section
open Filter Function MeasureTheory Set Topology
open scoped ContDiff Interval
namespace RiemannMasullo

private def samplingWave (n : ℤ) (x : ℝ) : ℂ := fourier n (x : AddCircle (1 : ℝ))

private theorem samplingWave_smooth (n : ℤ) : ContDiff ℝ ∞ (samplingWave n) := by
  change ContDiff ℝ ∞ (fun x : ℝ ↦ fourier n (x : AddCircle (1 : ℝ)))
  simp_rw [fourier_coe_apply, Complex.ofReal_one, div_one]
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff : ContDiff ℝ ∞ ((↑) : ℝ → ℂ))).cexp

private theorem samplingWave_norm (n : ℤ) (x : ℝ) : ‖samplingWave n x‖ = 1 :=
  Circle.norm_coe _

private theorem samplingWave_periodic (n : ℤ) : Periodic (samplingWave n) 1 := by
  intro x
  simp [samplingWave]

private theorem samplingWave_weighted_deriv (b : ℂ) (n : ℤ) (k : ℕ) :
    iteratedDeriv k (fun x ↦ b * samplingWave n x) =
      (fun x ↦ b * (2 * (Real.pi : ℂ) * Complex.I * n) ^ k * samplingWave n x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h := (hasDerivAt_fourier (1 : ℝ) n x).const_mul (b * (2 * (Real.pi : ℂ) * Complex.I * n) ^ k)
    simpa only [Complex.ofReal_one, div_one, pow_succ, mul_assoc, samplingWave] using h.deriv

private theorem sampling_summable_weight (b : ℤ → ℂ)
    (hb : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℤ, (1 + |(n : ℝ)|)^k * ‖b n‖ ≤ C) (k : ℕ) :
    Summable (fun n : ℤ ↦ (1 + |(n : ℝ)|)^k * ‖b n‖) := by
  have hnat : Summable (fun n : ℕ ↦ 1 / (1 + (n : ℝ)) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow.mpr (show 1 < 2 by decide)).comp_injective Nat.succ_injective
    exact h.congr (fun n ↦ by simp [add_comm])
  have hint : Summable (fun n : ℤ ↦ 1 / (1 + |(n : ℝ)|) ^ 2) := by
    rw [summable_int_iff_summable_nat_and_neg]
    constructor <;> exact hnat.congr (fun n ↦ by simp)
  obtain ⟨C, hC⟩ := hb (k+2)
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) (hint.mul_left C)
  rw [mul_one_div, le_div_iff₀ (by positivity)]
  simpa only [pow_add, mul_right_comm, mul_assoc, mul_left_comm, mul_comm] using hC n

private theorem samplingSeries_smooth (b : ℤ → ℂ)
    (hb : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℤ, (1 + |(n : ℝ)|)^k * ‖b n‖ ≤ C) :
    ContDiff ℝ ∞ (fun x ↦ ∑' n : ℤ, b n * samplingWave (-n) x) := by
  let v (k : ℕ) (n : ℤ) := (2 * Real.pi)^k * ((1 + |(n : ℝ)|)^k * ‖b n‖)
  apply contDiff_tsum (v := v) (fun n ↦ contDiff_const.mul (samplingWave_smooth (-n)))
    (fun k _ ↦ (sampling_summable_weight b hb k).mul_left _)
  intro k n x _
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, samplingWave_weighted_deriv,
    norm_mul, samplingWave_norm, mul_one, norm_mul, norm_pow]
  have hc : ‖2 * (Real.pi : ℂ) * Complex.I * ((-n : ℤ) : ℂ)‖ = 2 * Real.pi * |(n : ℝ)| := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hc, mul_pow]
  dsimp [v]
  calc
    _ = (2 * Real.pi)^k * (|(n : ℝ)|^k * ‖b n‖) := by ring
    _ ≤ _ := by
      gcongr
      linarith

private theorem samplingWave_orthogonal (m n : ℤ) :
    ∫ x in (0 : ℝ)..1, samplingWave m x * samplingWave (-n) x = if n = m then 1 else 0 := by
  let _ : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have h := congrFun (fourierCoeff_fourier (T := 1) (-n)) (-m)
  rw [fourierCoeff_eq_intervalIntegral _ _ 0] at h
  simpa [samplingWave, Pi.single_apply, eq_comm, smul_eq_mul] using h

private theorem samplingSeries_integral (b : ℤ → ℂ)
    (hb : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℤ, (1 + |(n : ℝ)|)^k * ‖b n‖ ≤ C) (m : ℤ) :
    ∫ x in (0 : ℝ)..1, (∑' n : ℤ, b n * samplingWave (-n) x) * samplingWave m x = b m := by
  let G (n : ℤ) (x : ℝ) := b n * (samplingWave m x * samplingWave (-n) x)
  have hs : Summable (fun n ↦ ‖b n‖) := by simpa using sampling_summable_weight b hb 0
  have hi (n : ℤ) : IntegrableOn (G n) (Ioc 0 1) := by
    have hc : Continuous (G n) :=
      continuous_const.mul ((samplingWave_smooth m).continuous.mul (samplingWave_smooth (-n)).continuous)
    exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hnorm (n : ℤ) : ∫ x in Ioc (0 : ℝ) 1, ‖G n x‖ = ‖b n‖ := by
    simp [G, samplingWave_norm]
  have hint (n : ℤ) : ∫ x in (0 : ℝ)..1, G n x = if n = m then b m else 0 := by
    dsimp only [G]
    rw [intervalIntegral.integral_const_mul, samplingWave_orthogonal]
    split <;> simp_all
  have hsum (x : ℝ) : (∑' n : ℤ, b n * samplingWave (-n) x) * samplingWave m x = ∑' n, G n x := by
    rw [← tsum_mul_right]
    exact tsum_congr (fun n ↦ by dsimp [G]; ring)
  simp_rw [hsum]
  rw [intervalIntegral.integral_of_le zero_le_one,
    ← integral_tsum_of_summable_integral_norm hi (by simpa only [hnorm] using hs)]
  simp_rw [← intervalIntegral.integral_of_le zero_le_one, hint]
  simp

/-- The difference of two translates of the smooth step is a compactly supported function
whose adjacent translates sum to one on the unit interval. It is the smoothed interval
window in mccorvie's interpolation argument on issue #7279, comment 7125686485. -/
private def samplingWindow (x : ℝ) : ℂ :=
  (Real.smoothTransition x - Real.smoothTransition (x-1) : ℝ)

private theorem samplingWindow_smooth : ContDiff ℝ ∞ samplingWindow :=
  Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.sub
    (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)))

private theorem samplingWindow_zero {x : ℝ} (hx : x ∉ Ioc 0 2) : samplingWindow x = 0 := by
  rcases le_or_gt x 0 with hx0 | hx0
  · simp [samplingWindow, Real.smoothTransition.zero_of_nonpos hx0,
      Real.smoothTransition.zero_of_nonpos (by linarith : x - 1 ≤ 0)]
  · have hx2 : 2 < x := lt_of_not_ge (fun h ↦ hx ⟨hx0, h⟩)
    simp [samplingWindow, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x),
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x - 1)]

private theorem samplingWindow_integral {F : ℝ → ℂ} (hF : Continuous F) (hp : Periodic F 1) :
    (∫ x : ℝ, samplingWindow x * F x) = ∫ x in (0 : ℝ)..1, F x := by
  let g (x : ℝ) := samplingWindow x * F x
  have hg : Continuous g := samplingWindow_smooth.continuous.mul hF
  have hw (x : ℝ) (hx : x ∈ Icc 0 1) : samplingWindow x + samplingWindow (x+1) = 1 := by
    simp [samplingWindow, Real.smoothTransition.zero_of_nonpos (by linarith [hx.2] : x-1 ≤ 0),
      Real.smoothTransition.one_of_one_le (by linarith [hx.1] : 1 ≤ x+1)]
  have hshift : (∫ x in (0 : ℝ)..1, g (x+1)) = ∫ x in (1:ℝ)..2, g x := by
    rw [intervalIntegral.integral_comp_add_right]
    norm_num
  change (∫ x : ℝ, g x) = _
  calc
    _ = ∫ x in (0:ℝ)..2, g x := by
      rw [intervalIntegral.integral_of_le (by norm_num)]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx ↦ by dsimp [g]; rw [samplingWindow_zero hx, zero_mul])).symm
    _ = (∫ x in (0:ℝ)..1, g x) + ∫ x in (1:ℝ)..2, g x :=
      (intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)).symm
    _ = ∫ x in (0:ℝ)..1, g x + g (x+1) := by
      rw [← hshift]
      symm
      apply intervalIntegral.integral_add (hg.intervalIntegrable _ _)
      exact (show Continuous (fun x : ℝ ↦ g (x+1)) from hg.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le zero_le_one] at hx
      dsimp only [g]
      rw [hp x, ← add_mul, hw x hx, one_mul]

/-- Every rapidly decreasing sequence is the full set of equally spaced Fourier samples of
one smooth function supported in the fixed interval `[0, 2L]`. The frequency sign matches the Mellin transform
on the imaginary axis. Construction from mccorvie, issue #7279, comment 7125686485. -/
theorem exists_compactSmooth_logFourier_samples (L : ℝ) (hL : 0 < L) (b : ℤ → ℂ)
    (hb : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℤ, (1 + |(n : ℝ)|)^k * ‖b n‖ ≤ C) :
    ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧ Function.support h ⊆ Icc 0 (2 * L) ∧ ∀ m : ℤ,
      (∫ x : ℝ, h x * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * m / L) * x)) = b m := by
  let G (x : ℝ) := ∑' n : ℤ, b n * samplingWave (-n) x
  have hG := samplingSeries_smooth b hb
  have hper : Periodic G 1 := fun x ↦ tsum_congr (fun n ↦ congrArg (b n * ·) (samplingWave_periodic (-n) x))
  let H (x : ℝ) := samplingWindow x * G x
  have hHs : ContDiff ℝ ∞ H := samplingWindow_smooth.mul hG
  have hunit (m : ℤ) : (∫ x : ℝ, H x * samplingWave m x) = b m := by
    change (∫ x : ℝ, (samplingWindow x * G x) * samplingWave m x) = b m
    simp only [mul_assoc]
    rw [samplingWindow_integral (F := fun x ↦ G x * samplingWave m x)
      (hG.continuous.mul (samplingWave_smooth m).continuous) (hper.mul (samplingWave_periodic m))]
    exact samplingSeries_integral b hb m
  refine ⟨fun x ↦ (L : ℂ)⁻¹ * H (x/L), contDiff_const.mul (hHs.comp (contDiff_id.div_const _)), ?_, ?_⟩
  · intro x hx
    by_contra hout
    have hscaled : x / L ∉ Ioc 0 2 := by
      intro hx'
      exact hout ⟨(div_pos_iff_of_pos_right hL).mp hx'.1 |>.le, (div_le_iff₀ hL).mp hx'.2⟩
    exact hx (by simp [H, samplingWindow_zero hscaled])
  · intro m
    have he (x : ℝ) : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * m / L) * x) = samplingWave m (x/L) := by
      rw [samplingWave, fourier_coe_apply, Complex.ofReal_one, div_one, Complex.ofReal_div]
      congr 1
      ring
    simp_rw [he, mul_assoc]
    rw [integral_const_mul, Measure.integral_comp_div (fun x ↦ H x * samplingWave m x) L, hunit,
      abs_of_pos hL, Complex.real_smul, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hL.ne'), one_mul]

end RiemannMasullo
