module

public import RiemannMasullo.Ch12_TraceGeometric.Sec1a
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Chapter 12.1.1: statements that are false as printed
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped NNReal InnerProductSpace Pointwise

namespace RiemannMasullo

/-- Paper: Theorem 12.1.1.2(2), p. 499. For every compactly supported continuous
multiplier in the target variable, smoothening the multiplied kernel gives the
pointwise product of the multiplier with the smoothened kernel. -/
def Printed.dSequenceKernelSmoothening_mul_continuous : Prop :=
  ∀ {G : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ ν : Measure G) [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts ν] [ν.InnerRegular]
    (U : ℕ → Set G) (f : G → ℝ≥0),
    IsDPrimeSequence μ U → (∀ n, MeasurableSet (U n)) →
    Continuous f → (∀ x, 0 < f x) → ν = μ.withDensity (fun x ↦ ↑(f x)) →
    ∀ (k : Lp ℂ 2 (ν.prod ν)), IsNuclearOperator (integralKernelOperator ν k).val →
    ∀ (κ : G × G → ℂ), κ =ᵐ[ν.prod ν] k →
    ∀ (ρ : G → ℂ), Continuous ρ → HasCompactSupport ρ →
    dSequenceKernelSmoothening μ U (fun p ↦ ρ p.1 * κ p) =
      fun p ↦ ρ p.1 * dSequenceKernelSmoothening μ U κ p

/-- Haar measure on the multiplicative real line, transported from Lebesgue measure. -/
private abbrev mulRealHaar : Measure (Multiplicative ℝ) :=
  Measure.map MeasurableEquiv.multiplicative volume

private theorem mulRealHaar_apply (s : Set (Multiplicative ℝ)) :
    mulRealHaar s = volume (Multiplicative.ofAdd ⁻¹' s) :=
  MeasurableEquiv.multiplicative.map_apply s

private theorem mulRealHaar_isHaarMeasure : mulRealHaar.IsHaarMeasure where
  map_mul_left_eq_self g := by
    ext s hs
    rw [Measure.map_apply (measurable_const_mul g) hs, mulRealHaar_apply, mulRealHaar_apply]
    exact measure_preimage_add volume (Multiplicative.toAdd g) (Multiplicative.ofAdd ⁻¹' s)
  lt_top_of_isCompact K hK := by
    rw [mulRealHaar_apply]
    have hK' : IsCompact (Multiplicative.ofAdd ⁻¹' K : Set ℝ) := hK
    exact hK'.measure_lt_top
  open_pos U hU hne := by
    rw [mulRealHaar_apply]
    have hU' : IsOpen (Multiplicative.ofAdd ⁻¹' U : Set ℝ) := hU
    exact hU'.measure_ne_zero (volume : Measure ℝ) hne

/-- The averaging sets: the logarithmic intervals `[−2⁻ⁿ, 2⁻ⁿ]`. -/
private abbrev mulRealBall (n : ℕ) : Set (Multiplicative ℝ) :=
  Multiplicative.toAdd ⁻¹' Icc (-(1 / 2 : ℝ) ^ n) ((1 / 2 : ℝ) ^ n)

private theorem mulRealBall_measure (r : ℝ) :
    mulRealHaar (Multiplicative.toAdd ⁻¹' Icc (-r) r) = ENNReal.ofReal (2 * r) := by
  rw [mulRealHaar_apply]
  change volume (Icc (-r) r) = _
  rw [Real.volume_Icc]
  ring_nf

private theorem mulRealBall_isDPrimeSequence : IsDPrimeSequence mulRealHaar mulRealBall := by
  have hr (n : ℕ) : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hpos (n : ℕ) : 0 < mulRealHaar (mulRealBall n) := by
    rw [mulRealBall_measure]
    exact ENNReal.ofReal_pos.mpr (by linarith [hr n])
  have hsub (n : ℕ) : mulRealBall n * (mulRealBall n)⁻¹ ⊆
      Multiplicative.toAdd ⁻¹' Icc (-(2 * (1 / 2 : ℝ) ^ n)) (2 * (1 / 2 : ℝ) ^ n) := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have hy' : Multiplicative.toAdd y⁻¹ ∈ Icc (-(1 / 2 : ℝ) ^ n) ((1 / 2 : ℝ) ^ n) := hy
    have hx' : Multiplicative.toAdd x ∈ Icc (-(1 / 2 : ℝ) ^ n) ((1 / 2 : ℝ) ^ n) := hx
    rw [toAdd_inv] at hy'
    change Multiplicative.toAdd x + Multiplicative.toAdd y ∈ Icc _ _
    constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2]
  refine ⟨⟨fun n ↦ ⟨?_, ?_, hpos n, ?_⟩, ?_, 3, by norm_num, fun n ↦ ⟨?_, ?_⟩⟩, ?_⟩
  · change (0 : ℝ) ∈ Icc _ _
    constructor <;> linarith [hr n]
  · exact (measurableSet_Icc.preimage measurable_toAdd).nullMeasurableSet
  · rw [mulRealBall_measure]
    exact ENNReal.ofReal_lt_top
  · intro n m hnm
    refine preimage_mono (Icc_subset_Icc ?_ ?_)
    · exact neg_le_neg (pow_le_pow_of_le_one (by norm_num) (by norm_num) hnm)
    · exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hnm
  · exact (hpos n).trans_le (measure_mono (subset_mul_left _ (by
      change Multiplicative.toAdd (1 : Multiplicative ℝ)⁻¹ ∈ Icc _ _
      rw [inv_one, toAdd_one]
      constructor <;> linarith [hr n])))
  · refine (measure_mono (hsub n)).trans_lt ?_
    rw [mulRealBall_measure, mulRealBall_measure, ← ENNReal.ofReal_mul (by norm_num)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [hr n])).mpr (by linarith [hr n])
  · intro W hW
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hW
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨k, fun x hx ↦ hball ?_⟩
    have hx' : Multiplicative.toAdd x ∈ Icc (-(1 / 2 : ℝ) ^ k) ((1 / 2 : ℝ) ^ k) := hx
    change dist (Multiplicative.toAdd x) 0 < ε
    rw [Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [hx'.1, hx'.2]

/-- The multiplier `|t|^(1/4)` near the identity, cut off to compact support. -/
private abbrev mulRealMultiplier (x : Multiplicative ℝ) : ℂ :=
  ((max 0 (min (|Multiplicative.toAdd x| ^ (1 / 4 : ℝ)) (2 - |Multiplicative.toAdd x|)) : ℝ) : ℂ)

/-- The square-integrable singular factor `|t|^(-1/4)` on the ball of radius two. -/
private abbrev mulRealSingular (x : Multiplicative ℝ) : ℂ :=
  ((Metric.ball (0 : ℝ) 2).indicator (fun t ↦ |t| ^ (-(1 / 4) : ℝ)) (Multiplicative.toAdd x) : ℝ)

/-- The indicator of the ball of radius two. -/
private abbrev mulRealCutoff (x : Multiplicative ℝ) : ℂ :=
  ((Metric.ball (0 : ℝ) 2).indicator (fun _ ↦ (1 : ℝ)) (Multiplicative.toAdd x) : ℝ)

private theorem mulRealSingular_measurable : Measurable mulRealSingular :=
  Complex.measurable_ofReal.comp (((Measurable.pow_const continuous_abs.measurable _).indicator
    measurableSet_ball).comp measurable_toAdd)

private theorem mulRealCutoff_measurable : Measurable mulRealCutoff :=
  Complex.measurable_ofReal.comp ((measurable_const.indicator measurableSet_ball).comp
    measurable_toAdd)

/-- A function of the multiplicative line is integrable for `mulRealHaar` when its pullback to
the real line is integrable on the ball of radius two and vanishes outside it. -/
private theorem mulRealHaar_integrable_indicator (h : ℝ → ℝ)
    (hh : IntegrableOn h (Metric.ball (0 : ℝ) 2)) :
    Integrable (fun x : Multiplicative ℝ ↦ (Metric.ball (0 : ℝ) 2).indicator h
      (Multiplicative.toAdd x)) mulRealHaar :=
  (integrable_map_equiv MeasurableEquiv.multiplicative _).mpr
    ((integrable_indicator_iff measurableSet_ball).mpr hh)

private theorem mulRealSingular_memLp : MemLp mulRealSingular 2 mulRealHaar := by
  refine (memLp_two_iff_integrable_sq_norm mulRealSingular_measurable.aestronglyMeasurable).mpr ?_
  have hint : IntegrableOn (fun t : ℝ ↦ |t| ^ (-(1 / 2) : ℝ)) (Metric.ball (0 : ℝ) 2) := by
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := 1 / 2) (by simp)
      (by simp only [Module.finrank_self]; norm_num) (Eventually.of_forall fun t ↦ ?_)
      ((Measurable.pow_const continuous_abs.measurable _).aestronglyMeasurable)
    rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _),
      Real.norm_eq_abs]
  refine (mulRealHaar_integrable_indicator _ hint).congr (Eventually.of_forall fun x ↦ ?_)
  simp only [mulRealSingular, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  by_cases hx : Multiplicative.toAdd x ∈ Metric.ball (0 : ℝ) 2
  · simp only [indicator_of_mem hx]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    norm_num
  · simp [indicator_of_notMem hx]

private theorem mulRealCutoff_memLp : MemLp mulRealCutoff 2 mulRealHaar := by
  refine (memLp_two_iff_integrable_sq_norm mulRealCutoff_measurable.aestronglyMeasurable).mpr ?_
  have hint : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Metric.ball (0 : ℝ) 2) :=
    integrableOn_const (measure_ball_lt_top).ne
  refine (mulRealHaar_integrable_indicator _ hint).congr (Eventually.of_forall fun x ↦ ?_)
  simp only [mulRealCutoff, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  by_cases hx : Multiplicative.toAdd x ∈ Metric.ball (0 : ℝ) 2 <;> simp [hx]

/-- The rank-one kernel `conj (cutoff y) * singular x`. -/
private abbrev mulRealKernel (p : Multiplicative ℝ × Multiplicative ℝ) : ℂ :=
  starRingEnd ℂ (mulRealCutoff p.2) * mulRealSingular p.1

private theorem mulRealKernel_memLp : MemLp mulRealKernel 2 (mulRealHaar.prod mulRealHaar) := by
  have hm : Measurable mulRealKernel :=
    ((Complex.continuous_conj.measurable.comp mulRealCutoff_measurable).comp measurable_snd).mul
      (mulRealSingular_measurable.comp measurable_fst)
  refine (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr ?_
  have h := Integrable.mul_prod
    ((memLp_two_iff_integrable_sq_norm mulRealSingular_measurable.aestronglyMeasurable).mp
      mulRealSingular_memLp)
    ((memLp_two_iff_integrable_sq_norm mulRealCutoff_measurable.aestronglyMeasurable).mp
      mulRealCutoff_memLp)
  refine h.congr (Eventually.of_forall fun p ↦ ?_)
  simp only [mulRealKernel, norm_mul, RCLike.norm_conj, mul_pow]
  ring

/-- A kernel that is almost everywhere a rank-one product gives the rank-one operator. -/
private theorem mulRealKernel_outerProduct {X : Type} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] [Measure.InnerRegular μ] {K : Lp ℂ 2 (μ.prod μ)} {u v : Lp ℂ 2 μ}
    (hK : (K : X × X → ℂ) =ᵐ[μ.prod μ] fun p ↦ ⟪v p.2, u p.1⟫_ℂ) :
    (integralKernelOperator μ K).val = (innerSL ℂ v).smulRight u := by
  ext f : 1
  apply Lp.ext
  filter_upwards [integralKernelOperator_apply μ K f, Measure.ae_ae_of_ae_prod hK,
    Lp.coeFn_smul ⟪v, f⟫_ℂ u] with x hx hxy hsmul
  have h : (fun y ↦ K (x, y) * f y) =ᵐ[μ] fun y ↦ u x * ⟪v y, f y⟫_ℂ := by
    filter_upwards [hxy] with y hy
    rw [show K (x, y) = ⟪v y, u x⟫_ℂ from hy, RCLike.inner_apply, RCLike.inner_apply]
    ring
  change (integralKernelOperator μ K).val f x = (⟪v, f⟫_ℂ • u : Lp ℂ 2 μ) x
  rw [hx.2, integral_congr_ae h, integral_const_mul, hsmul]
  change u x * (∫ y, ⟪v y, f y⟫_ℂ ∂μ) = ⟪v, f⟫_ℂ * u x
  rw [L2.inner_def, mul_comm]

private theorem mulRealMultiplier_continuous : Continuous mulRealMultiplier :=
  Complex.continuous_ofReal.comp (continuous_const.max
    ((continuous_toAdd.abs.rpow_const fun _ ↦ Or.inr (by norm_num)).min
      (continuous_const.sub continuous_toAdd.abs)))

private theorem mulRealMultiplier_hasCompactSupport : HasCompactSupport mulRealMultiplier := by
  refine HasCompactSupport.intro ((isCompact_Icc (a := (-2 : ℝ)) (b := 2)).image
    continuous_ofAdd) fun x hx ↦ ?_
  have h2 : 2 < |Multiplicative.toAdd x| := by
    by_contra hle
    exact hx ⟨Multiplicative.toAdd x, abs_le.mp (not_lt.mp hle), rfl⟩
  have hmin : min (|Multiplicative.toAdd x| ^ (1 / 4 : ℝ)) (2 - |Multiplicative.toAdd x|) ≤ 0 :=
    (min_le_right _ _).trans (by linarith)
  simp only [mulRealMultiplier, max_eq_left hmin, Complex.ofReal_zero]

private theorem mulRealMultiplier_one : mulRealMultiplier 1 = 0 := by
  simp [mulRealMultiplier]

/-- Near the identity the weighted kernel is one off the null line through the identity. -/
private theorem mulRealWeighted_ae :
    ∀ᵐ p ∂(mulRealHaar.prod mulRealHaar), p ∈ mulRealBall 0 ×ˢ mulRealBall 0 →
      mulRealMultiplier p.1 * mulRealKernel p = 1 := by
  have h0 : ∀ᵐ x ∂mulRealHaar, x ≠ 1 := by
    rw [ae_iff]
    simp only [not_not, ofPred_eq_eq_singleton]
    rw [mulRealHaar_apply, show Multiplicative.ofAdd ⁻¹' ({1} : Set (Multiplicative ℝ)) = {0} by
      ext t
      simp, Real.volume_singleton]
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h0] with p hp hmem
  have ht : Multiplicative.toAdd p.1 ∈ Icc (-(1 / 2 : ℝ) ^ 0) ((1 / 2 : ℝ) ^ 0) := hmem.1
  have hs : Multiplicative.toAdd p.2 ∈ Icc (-(1 / 2 : ℝ) ^ 0) ((1 / 2 : ℝ) ^ 0) := hmem.2
  simp only [pow_zero] at ht hs
  have ht1 : |Multiplicative.toAdd p.1| ≤ 1 := abs_le.mpr ht
  have hs1 : |Multiplicative.toAdd p.2| ≤ 1 := abs_le.mpr hs
  have ht0 : 0 < |Multiplicative.toAdd p.1| := abs_pos.mpr fun h ↦ hp (by
    rw [← ofAdd_toAdd p.1, h, ofAdd_zero])
  have hball (y : Multiplicative ℝ) (hy : |Multiplicative.toAdd y| ≤ 1) :
      Multiplicative.toAdd y ∈ Metric.ball (0 : ℝ) 2 := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    linarith
  have hle : |Multiplicative.toAdd p.1| ^ (1 / 4 : ℝ) ≤ 2 - |Multiplicative.toAdd p.1| :=
    (Real.rpow_le_one (abs_nonneg _) ht1 (by norm_num)).trans (by linarith)
  simp only [mulRealKernel, mulRealMultiplier, mulRealCutoff, mulRealSingular,
    indicator_of_mem (hball _ hs1), indicator_of_mem (hball _ ht1), min_eq_left hle,
    max_eq_right (Real.rpow_nonneg (abs_nonneg _) _), Complex.ofReal_one, map_one, one_mul,
    ← Complex.ofReal_mul]
  rw [Real.rpow_neg (abs_nonneg _), mul_inv_cancel₀ (Real.rpow_pos_of_pos ht0 _).ne',
    Complex.ofReal_one]

/-- The weighted kernel smoothens to one at the identity. -/
private theorem mulRealWeighted_smoothening :
    dSequenceKernelSmoothening mulRealHaar mulRealBall
      (fun p ↦ mulRealMultiplier p.1 * mulRealKernel p) 1 = 1 := by
  have hU := mulRealBall_isDPrimeSequence
  have havg (n : ℕ) : dSequenceAverage (mulRealHaar.prod mulRealHaar)
      (mulRealBall n ×ˢ mulRealBall n) (fun p ↦ mulRealMultiplier p.1 * mulRealKernel p) 1 = 1 := by
    have hm : MeasurableSet (mulRealBall n) := measurableSet_Icc.preimage measurable_toAdd
    have hsub : mulRealBall n ⊆ mulRealBall 0 := hU.1.2.1 (Nat.zero_le n)
    unfold dSequenceAverage
    rw [one_smul, setAverage_congr_fun (hm.prod hm) (g := fun _ ↦ (1 : ℂ))
      (by
        filter_upwards [mulRealWeighted_ae] with p hp hmem
        exact hp ⟨hsub hmem.1, hsub hmem.2⟩)]
    apply setAverage_const <;> rw [Measure.prod_prod]
    · exact mul_ne_zero (hU.1.1 n).2.2.1.ne' (hU.1.1 n).2.2.1.ne'
    · exact ENNReal.mul_ne_top (hU.1.1 n).2.2.2.ne (hU.1.1 n).2.2.2.ne
  have hlim : Tendsto (fun n ↦ dSequenceAverage (mulRealHaar.prod mulRealHaar)
      (mulRealBall n ×ˢ mulRealBall n) (fun p ↦ mulRealMultiplier p.1 * mulRealKernel p) 1)
      atTop (nhds 1) := by
    simpa only [havg] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (nhds 1))
  have hp : (1 : Multiplicative ℝ × Multiplicative ℝ) ∈ dSequenceRegularSet
      (mulRealHaar.prod mulRealHaar) (fun n ↦ mulRealBall n ×ˢ mulRealBall n)
      (fun p ↦ mulRealMultiplier p.1 * mulRealKernel p) := ⟨1, hlim⟩
  simpa only [dSequenceKernelSmoothening, dSequenceSmootheningOrZero, dite_eq_left hp,
    dSequenceSmoothening] using hlim.limUnder_eq

/-- Paper: Theorem 12.1.1.2(2), p. 499. On the additive real line use Lebesgue
measure, density one, and the intervals `[−2⁻ⁿ, 2⁻ⁿ]`. Let `χ(t) = max(0, min(1, 2 − |t|))`,
`g(t) = χ(t) sgn(t) |t|⁻¹⁄⁴` with `g(0) = 0`, and use the rank-one kernel
`k(x,y) = g(x) χ(y)`. The continuous compactly supported multiplier
`ρ(t) = χ(t) sgn(t) |t|¹⁄⁴` gives a weighted kernel equal to one almost
everywhere on the averaging squares at the origin. The unweighted kernel
averages are zero by oddness, so the asserted pointwise identity gives
`1 = 0` at the regular point `(0,0)`. -/
theorem Printed.dSequenceKernelSmoothening_mul_continuous_false :
    ¬ Printed.dSequenceKernelSmoothening_mul_continuous := by
  intro h
  have : mulRealHaar.IsHaarMeasure := mulRealHaar_isHaarMeasure
  have hν : mulRealHaar = mulRealHaar.withDensity
      (fun x ↦ (((fun _ : Multiplicative ℝ ↦ (1 : ℝ≥0)) x : ℝ≥0) : ENNReal)) := by
    simp only [ENNReal.coe_one]
    exact (withDensity_one).symm
  have hK : (mulRealKernel_memLp.toLp mulRealKernel : _ → ℂ) =ᵐ[mulRealHaar.prod mulRealHaar]
      fun p ↦ ⟪(mulRealCutoff_memLp.toLp mulRealCutoff : Lp ℂ 2 mulRealHaar) p.2,
        (mulRealSingular_memLp.toLp mulRealSingular : Lp ℂ 2 mulRealHaar) p.1⟫_ℂ := by
    filter_upwards [mulRealKernel_memLp.coeFn_toLp,
      Measure.quasiMeasurePreserving_fst.ae mulRealSingular_memLp.coeFn_toLp,
      Measure.quasiMeasurePreserving_snd.ae mulRealCutoff_memLp.coeFn_toLp] with p hp h1 h2
    rw [hp, RCLike.inner_apply, h1, h2]
    exact mul_comm _ _
  have hnuc : IsNuclearOperator
      (integralKernelOperator mulRealHaar (mulRealKernel_memLp.toLp mulRealKernel)).val := by
    rw [mulRealKernel_outerProduct hK]
    exact isNuclearOperator_smulRight _ _
  have e := congrFun (h mulRealHaar mulRealHaar mulRealBall (fun _ ↦ 1)
    mulRealBall_isDPrimeSequence (fun n ↦ measurableSet_Icc.preimage measurable_toAdd)
    continuous_const (fun _ ↦ one_pos) hν _ hnuc mulRealKernel
    mulRealKernel_memLp.coeFn_toLp.symm mulRealMultiplier mulRealMultiplier_continuous
    mulRealMultiplier_hasCompactSupport) 1
  rw [mulRealWeighted_smoothening] at e
  change (1 : ℂ) = mulRealMultiplier 1 * _ at e
  rw [mulRealMultiplier_one, zero_mul] at e
  exact one_ne_zero e

end RiemannMasullo
