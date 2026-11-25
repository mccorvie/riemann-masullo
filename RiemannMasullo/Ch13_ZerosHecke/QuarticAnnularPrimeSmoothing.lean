module

public import RiemannMasullo.Ch13_ZerosHecke.AnnularKernelCrossings
public import RiemannMasullo.Ch13_ZerosHecke.QuarticAnnularPrimeSums
public import RiemannMasullo.Ch13_ZerosHecke.QuarticAnnularCrossingMass
public import RiemannMasullo.Ch13_ZerosHecke.ThreeMomentCrossingComparison
public import RiemannMasullo.Ch13_ZerosHecke.CompensatedGaussianDensity
import Mathlib.MeasureTheory.Function.Floor

/-!
# Compensated smoothing of the quartic annular prime sum

Only the primes crossing one of the two knots of the fixed annular kernel
contribute to the compensated smoothing error of the real arithmetic row.
The moving cutoff is the one in the original prime sum, including its zero
at the ramified prime five. The annular comparison concerns the finite
arithmetic statistics associated with Theorem 12.5.1.1, pp. 519–520.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped NNReal

public noncomputable section

namespace RiemannMasullo

/-- The prime sum with the branch of the kernel at each unshifted prime held
fixed. Every summand is a combination of the three preserved moments. -/
@[expose] def quarticAnnularFrozenPrimeSum (y h : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊y⌋₊, (quarticCharacterFive (p : ZMod 5)).re * Real.log p *
    annularKernelFrozen (Real.log ((p : ℝ) / y)) h

private theorem sum_primesLE_extend {z m : ℝ} (hz : 0 < z) (hm : z ≤ m) (f : ℕ → ℝ)
    (hs : ∀ p : ℕ, p.Prime → z < (p : ℝ) → f p = 0) :
    ∑ p ∈ Nat.primesLE ⌊z⌋₊, f p = ∑ p ∈ Nat.primesLE ⌊m⌋₊, f p := by
  apply sum_subset (Nat.primesLE_mono (Nat.floor_mono hm))
  intro p hp hsmall
  have hprime := Nat.prime_of_mem_primesLE hp
  apply hs p hprime
  by_contra! h
  exact hsmall (Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hz.le).mpr h, hprime⟩)

/-- Freezing at increment zero recovers the true real prime statistic. -/
theorem quarticAnnularFrozenPrimeSum_zero (y : ℝ) (hy : 0 < y) :
    quarticAnnularFrozenPrimeSum y 0 = (quarticAnnularPrimeStatistic y).re := by
  rw [quarticAnnularFrozenPrimeSum, quarticAnnularPrimeStatistic_re]
  apply sum_congr rfl
  intro p hp
  have hp' : 0 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
  rw [annularKernelFrozen_zero, Real.exp_log (div_pos hp' hy)]

private theorem quarticAnnularFrozenPrimeSum_three_moments (y : ℝ) :
    ∃ a b c : ℝ, ∀ h : ℝ, quarticAnnularFrozenPrimeSum y h =
      a + b * Real.exp h + c * Real.exp (-h) := by
  let w (p : ℕ) := (quarticCharacterFive (p : ZMod 5)).re * Real.log p
  let s := Nat.primesLE ⌊y⌋₊
  choose a b c hrep using fun p : ℕ ↦ annularKernelFrozen_three_moments (Real.log ((p : ℝ) / y))
  refine ⟨∑ p ∈ s, w p * a p, ∑ p ∈ s, w p * b p, ∑ p ∈ s, w p * c p, fun h ↦ ?_⟩
  change (∑ p ∈ s, w p * annularKernelFrozen (Real.log ((p : ℝ) / y)) h) = _
  simp only [hrep, mul_add, ← mul_assoc, sum_add_distrib, sum_mul]

/-- The genuine moving prime sum deviates from its frozen branches only at
primes within `|h|` in logarithmic distance of `y/2` or `y`. -/
theorem quarticAnnularPrimeStatistic_crossing_bound (y : ℝ) (hy : 0 < y) (h : ℝ) :
    |(quarticAnnularPrimeStatistic (y * Real.exp (-h))).re - quarticAnnularFrozenPrimeSum y h| ≤
      quarticAnnularPrimeCrossingMass y h := by
  let w (p : ℕ) := (quarticCharacterFive (p : ZMod 5)).re * Real.log p
  let z := y * Real.exp (-h)
  let m := y * Real.exp |h|
  have hz : 0 < z := mul_pos hy (Real.exp_pos _)
  have hzm : z ≤ m := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_abs h)) hy.le
  have hym : y ≤ m := by
    exact le_mul_of_one_le_right hy.le (Real.one_le_exp (abs_nonneg h))
  rw [quarticAnnularPrimeStatistic_re, quarticAnnularFrozenPrimeSum]
  change |(∑ p ∈ Nat.primesLE ⌊z⌋₊, w p * annularPrimeKernel ((p : ℝ) / z)) -
    ∑ p ∈ Nat.primesLE ⌊y⌋₊, w p * annularKernelFrozen (Real.log ((p : ℝ) / y)) h| ≤ _
  rw [sum_primesLE_extend hz hzm (fun p ↦ w p * annularPrimeKernel ((p : ℝ) / z)) (by
    intro p _ hp
    rw [annularPrimeKernel_eq_zero_of_one_le ((one_le_div hz).mpr hp.le), mul_zero]),
    sum_primesLE_extend hy hym (fun p ↦ w p * annularKernelFrozen (Real.log ((p : ℝ) / y)) h)
      (by
        intro p _ hp
        rw [annularKernelFrozen_eq_zero_of_pos (Real.log_pos ((one_lt_div hy).mpr hp)), mul_zero]),
    ← sum_sub_distrib, quarticAnnularPrimeCrossingMass, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p hp ↦ ?_)
  have hprime := Nat.prime_of_mem_primesLE hp
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hprime.one_le)
  have hex : Real.exp (Real.log ((p : ℝ) / y) + h) = p / z := by
    rw [Real.exp_add, Real.exp_log (div_pos hp' hy)]
    dsimp [z]
    rw [Real.exp_neg]
    field_simp
  have htwo : Real.log ((p : ℝ) / y) + Real.log 2 = Real.log (2 * p / y) := by
    rw [← Real.log_mul (div_pos hp' hy).ne' (by norm_num)]
    congr 1
    ring
  have hc := annularPrimeKernel_crossing_bound (Real.log ((p : ℝ) / y)) h
  rw [hex, htwo] at hc
  rw [← mul_sub, abs_mul]
  calc _ ≤ |w p| * _ := mul_le_mul_of_nonneg_left hc (abs_nonneg _)
       _ = _ := by
         dsimp [w]
         rw [abs_mul, abs_of_nonneg hlog]
         ring

private theorem quarticAnnularPrimeStatistic_threeMoment_approximation (y : ℝ) (hy : 0 < y) :
    ∃ a b c : ℝ, (quarticAnnularPrimeStatistic y).re = a + b + c ∧
      ∀ h, |(quarticAnnularPrimeStatistic (y * Real.exp (-h))).re -
        (a + b * Real.exp h + c * Real.exp (-h))| ≤ quarticAnnularPrimeCrossingMass y h := by
  obtain ⟨a, b, c, hb⟩ := quarticAnnularFrozenPrimeSum_three_moments y
  refine ⟨a, b, c, ?_, fun h ↦ ?_⟩
  · simpa only [quarticAnnularFrozenPrimeSum_zero y hy, Real.exp_zero, neg_zero, mul_one] using hb 0
  · rw [← hb h]
    exact quarticAnnularPrimeStatistic_crossing_bound y hy h

private theorem measurable_quarticAnnularPrimeStatistic_shift (y : ℝ) :
    Measurable (fun h : ℝ ↦ (quarticAnnularPrimeStatistic (y * Real.exp (-h))).re) := by
  simp_rw [quarticAnnularPrimeStatistic_re]
  apply measurable_sum_primesLE_of_measurable (Nat.measurable_floor.comp (by fun_prop))
  intro p
  have hk : Measurable annularPrimeKernel := by
    unfold annularPrimeKernel
    apply Measurable.ite (measurableSet_le measurable_id measurable_const) (by fun_prop)
    apply Measurable.ite (measurableSet_le measurable_id measurable_const) (by fun_prop) measurable_const
  exact measurable_const.mul (hk.comp (by fun_prop))

/-- Any signed increment represented by an integrable real density with mass
and both unit exponential moments equal to one changes the actual quartic
arithmetic row by at most its absolute density integrated against the two
crossing neighborhoods. -/
theorem quarticAnnularPrimeStatistic_threeMoment_smoothing (y : ℝ) (hy : 0 < y)
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    (hp : Integrable (fun h ↦ w h * Real.exp h) μ)
    (hn : Integrable (fun h ↦ w h * Real.exp (-h)) μ)
    (hE : Integrable (fun h ↦ |w h| * quarticAnnularPrimeCrossingMass y h) μ)
    (hm : (∫ h, w h ∂μ) = 1) (hmpos : (∫ h, w h * Real.exp h ∂μ) = 1)
    (hmneg : (∫ h, w h * Real.exp (-h) ∂μ) = 1) :
    |(∫ h, w h * (quarticAnnularPrimeStatistic (y * Real.exp (-h))).re ∂μ) -
      (quarticAnnularPrimeStatistic y).re| ≤ ∫ h, |w h| * quarticAnnularPrimeCrossingMass y h ∂μ := by
  obtain ⟨a, b, c, hzero, hbound⟩ := quarticAnnularPrimeStatistic_threeMoment_approximation y hy
  rw [hzero]
  apply threeMoment_integral_sub_le μ w _ _ a b c
    (measurable_quarticAnnularPrimeStatistic_shift y).aestronglyMeasurable hw hp hn hE hm hmpos hmneg
  exact hbound

/-- The compensated Gaussian smoothing, at any variance including zero, is
controlled by Gaussian averages of only the two prime crossing neighborhoods.
The variance parameter is `δ²` in the logarithmic-increment convention. -/
theorem quarticAnnularPrimeStatistic_compensatedGaussian_smoothing (y : ℝ) (hy : 0 < y) (v : ℝ≥0) :
    |compensatedGaussianIncrement v (fun h ↦ (quarticAnnularPrimeStatistic (y * Real.exp (-h))).re) -
      (quarticAnnularPrimeStatistic y).re| ≤
      (1 + Real.exp (-(v : ℝ) / 2)) * (∫ h, quarticAnnularPrimeCrossingMass y h ∂gaussianReal 0 v) +
        Real.exp (-(v : ℝ) / 2) * (∫ h, quarticAnnularPrimeCrossingMass y h ∂gaussianReal 0 (2*v)) := by
  obtain ⟨a, b, c, hzero, hbound⟩ := quarticAnnularPrimeStatistic_threeMoment_approximation y hy
  rw [hzero]
  apply compensatedGaussianIncrement_sub_le v _ _ a b c
    (measurable_quarticAnnularPrimeStatistic_shift y)
    (quarticAnnularPrimeCrossingMass_integrable_gaussian y hy v)
    (quarticAnnularPrimeCrossingMass_integrable_gaussian y hy (2*v))
  exact hbound

/-- At positive variance the cancellation in the signed Gaussian density is
retained inside its absolute value before the crossing neighborhoods are
integrated. -/
theorem quarticAnnularPrimeStatistic_compensatedGaussian_density (y : ℝ) (hy : 0 < y)
    (v : ℝ≥0) (hv : v ≠ 0) :
    |compensatedGaussianIncrement v (fun h ↦ (quarticAnnularPrimeStatistic (y * Real.exp (-h))).re) -
      (quarticAnnularPrimeStatistic y).re| ≤
      ∫ h, |compensatedGaussianDensity v h| * quarticAnnularPrimeCrossingMass y h := by
  obtain ⟨a, b, c, hzero, hbound⟩ := quarticAnnularPrimeStatistic_threeMoment_approximation y hy
  rw [hzero]
  apply compensatedGaussianIncrement_sub_le_density v hv _ _ a b c
    (measurable_quarticAnnularPrimeStatistic_shift y) (quarticAnnularPrimeCrossingMass_measurable y)
    (quarticAnnularPrimeCrossingMass_integrable_gaussian y hy v)
    (quarticAnnularPrimeCrossingMass_integrable_gaussian y hy (2*v))
  exact hbound

end RiemannMasullo
