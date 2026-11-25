module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelOperator
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedBandDiagonal
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealOddBandOperator

/-! # The weighted band of the rational real-place model: the rank-one term

Paper: Theorem 12.4.1.1, pp. 514–519, and the value used on p. 520.

In the picture of `Sec4_WeightedBandKernel` the weighted band is the space of the odd functions
of the band `[-Y, Y]` that vanish at `ζ = e ^ (i π / 4)`. That space is the odd band less the
line of the reproducing vector `k` of the odd band at `ζ`, so the trace of a compression to it
is the trace of the compression to the odd band minus `⟪k, T k⟫ / ‖k‖ ^ 2`. This file computes
that correction for `T = r_g D_g`, the dilation with its multiplier.

* `complexBandVector Y u`: the vector of `L²(ℝ)` with frequency data `1_[-Y, Y] (ξ) e ^ (2 π u ξ)`
  for a complex rate `u`. Pairing with it evaluates the two-sided Laplace transform
  `bandLaplace` of the frequency data at `conj u` (`inner_complexBandVector_fourier`).
* `integral_fourier_complexBandExp_mul_lorentz_mul_fourier`: the pairing of such a vector with
  a Lorentzian times a function of the band, by two applications of Fubini and the Fourier
  transform of the Lorentzian.
* `inner_weightedEvalVector_multiplier_mul_fourier`: for an odd function `F` of the band, the
  band projection of `r_g F` has value `√g E (Y) F (g ζ)` at `ζ`. The contribution of `F (ζ)`
  cancels because `r_g ζ = 0`.
* `weightedKernelVector Y`: the reproducing vector `k`, with `weightedKernelVector_mem` and
  `weightedKernelVector_ne_zero`.
* `inner_weightedKernelVector_multiplier_dilation`: **`⟪k, r_g D_g k⟫ = E (Y) ⟪k, k⟫`**, with
  `E (Y) = weightedBandDefect Y g`, the term that also appears in the limit of the trace over
  the odd band (`Sec4_WeightedBandDiagonal`).
* `tendsto_inner_realCutoff`: the pairing with a cutoff vector tends to the pairing with the
  vector.
-/

open MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate InnerProductSpace ENNReal

@[expose] public noncomputable section

namespace RiemannMasullo

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

/-! ### Band exponentials with a complex rate -/

/-- The band exponential with a complex rate: `ξ ↦ 1_[-Y, Y] (ξ) exp (2 π u ξ)`. -/
def complexBandExp (Y : ℝ) (u : ℂ) : ℝ → ℂ :=
  (Icc (-Y) Y).indicator fun ξ ↦ Complex.exp (2 * π * u * ξ)

/-- The band exponential with a complex rate is integrable. -/
theorem integrable_complexBandExp (Y : ℝ) (u : ℂ) : Integrable (complexBandExp Y u) := by
  unfold complexBandExp
  rw [integrable_indicator_iff measurableSet_Icc]
  exact Continuous.integrableOn_Icc (by fun_prop)

/-- The band exponential with a complex rate is bounded. -/
theorem exists_norm_complexBandExp_le (Y : ℝ) (u : ℂ) : ∃ C, ∀ ξ, ‖complexBandExp Y u ξ‖ ≤ C := by
  have hc : Continuous fun ξ : ℝ ↦ Complex.exp (2 * π * u * ξ) := by fun_prop
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-Y) Y) hc.continuousOn
  refine ⟨max C 0, fun ξ ↦ ?_⟩
  unfold complexBandExp
  by_cases h : ξ ∈ Icc (-Y) Y
  · rw [indicator_of_mem h]
    exact (hC ξ h).trans (le_max_left _ _)
  · rw [indicator_of_notMem h, norm_zero]
    exact le_max_right _ _

/-- The band exponential with a complex rate is measurable. -/
theorem measurable_complexBandExp (Y : ℝ) (u : ℂ) : Measurable (complexBandExp Y u) := by
  unfold complexBandExp
  exact Measurable.indicator (by fun_prop) measurableSet_Icc

/-- The band exponential with a complex rate is square-integrable. -/
theorem memLp_complexBandExp (Y : ℝ) (u : ℂ) : MemLp (complexBandExp Y u) 2 := by
  obtain ⟨C, hC⟩ := exists_norm_complexBandExp_le Y u
  have h : MemLp ((Icc (-Y) Y).indicator fun _ : ℝ ↦ (C : ℝ)) 2 := by
    rw [memLp_indicator_iff_restrict
      (measurableSet_Icc : MeasurableSet (Icc (-Y) Y)).nullMeasurableSet]
    have : IsFiniteMeasure (volume.restrict (Icc (-Y) Y)) :=
      ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
    exact memLp_const C
  refine h.mono (measurable_complexBandExp Y u).aestronglyMeasurable
    (Eventually.of_forall fun ξ ↦ ?_)
  by_cases hξ : ξ ∈ Icc (-Y) Y
  · rw [indicator_of_mem hξ, Real.norm_eq_abs]
    exact (hC ξ).trans (le_abs_self C)
  · simp [complexBandExp, hξ]

/-- The band exponential vanishes outside the band. -/
theorem complexBandExp_of_notMem {Y : ℝ} {u : ℂ} {ξ : ℝ} (h : ξ ∉ Icc (-Y) Y) :
    complexBandExp Y u ξ = 0 := by
  simp only [complexBandExp, indicator_of_notMem h]

/-- The band exponential on the band. -/
theorem complexBandExp_of_mem {Y : ℝ} {u : ℂ} {ξ : ℝ} (h : ξ ∈ Icc (-Y) Y) :
    complexBandExp Y u ξ = Complex.exp (2 * π * u * ξ) := by
  simp only [complexBandExp, indicator_of_mem h]

private theorem neg_mem_band {Y ξ : ℝ} : -ξ ∈ Icc (-Y) Y ↔ ξ ∈ Icc (-Y) Y := by
  constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩

/-- Reflecting the frequency of a band exponential negates its rate. -/
theorem complexBandExp_neg (Y : ℝ) (u : ℂ) (ξ : ℝ) :
    complexBandExp Y u (-ξ) = complexBandExp Y (-u) ξ := by
  by_cases h : ξ ∈ Icc (-Y) Y
  · rw [complexBandExp_of_mem (neg_mem_band.mpr h), complexBandExp_of_mem h]
    congr 1
    push_cast
    ring
  · rw [complexBandExp_of_notMem (mt neg_mem_band.mp h), complexBandExp_of_notMem h]

/-- Conjugating a band exponential conjugates its rate. -/
theorem conj_complexBandExp (Y : ℝ) (u : ℂ) (ξ : ℝ) :
    conj (complexBandExp Y u ξ) = complexBandExp Y (conj u) ξ := by
  by_cases h : ξ ∈ Icc (-Y) Y
  · rw [complexBandExp_of_mem h, complexBandExp_of_mem h, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, map_ofNat]
  · rw [complexBandExp_of_notMem h, complexBandExp_of_notMem h, map_zero]

/-- The two-sided Laplace transform `u ↦ ∫ b ξ exp (2 π u ξ) dξ` of a function on the frequency
side. For `b` supported in the band it is the entire function whose restriction to the
imaginary axis is the Fourier transform of `b`. -/
def bandLaplace (b : ℝ → ℂ) (u : ℂ) : ℂ := ∫ ξ, b ξ * Complex.exp (2 * π * u * ξ)

/-- The vector of `L²(ℝ)` with frequency data the band exponential of rate `u`. Pairing with it
evaluates the two-sided Laplace transform of the frequency data at `conj u`. -/
def complexBandVector (Y : ℝ) (u : ℂ) : H :=
  𝓕 ((memLp_complexBandExp Y u).toLp (complexBandExp Y u))

/-- The conjugate of the Fourier integral of a band exponential. -/
theorem conj_fourier_complexBandExp (Y : ℝ) (u : ℂ) (x : ℝ) :
    conj (𝓕 (complexBandExp Y u) x) = 𝓕 (complexBandExp Y (-conj u)) x := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_conj, ← integral_neg_eq_self _ volume]
  refine integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_)
  simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, conj_complexBandExp, complexBandExp_neg,
    Complex.conj_ofReal, Complex.conj_I]
  congr 2
  push_cast
  ring

/-- **Pairing in space.** The pairing of the vector of rate `u` with any vector `V` is the
integral of `V` against the Fourier integral of the band exponential of rate `-conj u`. -/
theorem inner_complexBandVector_eq_integral (Y : ℝ) (u : ℂ) (V : H) :
    ⟪complexBandVector Y u, V⟫_ℂ = ∫ x, 𝓕 (complexBandExp Y (-conj u)) x * V x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [fourier_ae_eq_fourier_toLp (integrable_complexBandExp Y u)
    (memLp_complexBandExp Y u)] with x hx
  rw [complexBandVector, ← hx, RCLike.inner_apply, conj_fourier_complexBandExp, mul_comm]

/-- **Pairing in frequency.** The pairing of the vector of rate `u` with the vector of frequency
data `b` supported in the band is the two-sided Laplace transform of `b` at `conj u`. -/
theorem inner_complexBandVector_fourier {Y : ℝ} (u : ℂ) {b : ℝ → ℂ} (hb : MemLp b 2)
    (hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → b ξ = 0) :
    ⟪complexBandVector Y u, (𝓕 (hb.toLp b) : H)⟫_ℂ = bandLaplace b (conj u) := by
  rw [complexBandVector, Lp.inner_fourier_eq, L2.inner_def, bandLaplace]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_complexBandExp Y u).coeFn_toLp, hb.coeFn_toLp] with ξ h1 h2
  rw [h1, h2, RCLike.inner_apply, conj_complexBandExp]
  by_cases h : ξ ∈ Icc (-Y) Y
  · rw [complexBandExp_of_mem h]
  · rw [hsupp ξ h, zero_mul, zero_mul]

/-! ### The Fourier transform is self-adjoint -/

/-- The Fourier transform on the line satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`. -/
theorem integral_fourier_mul_eq_real {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x := by
  simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.mul ℂ ℂ)
    (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hf hg

/-- The Fourier transform of `m * 𝓕 c` is the correlation of `c` with `𝓕 m`. -/
theorem fourier_mul_fourier_eq {m c : ℝ → ℂ} (hm : Integrable m) (hc : Integrable c) (ξ : ℝ) :
    𝓕 (fun x ↦ m x * 𝓕 c x) ξ = ∫ η, c η * 𝓕 m (ξ + η) := by
  have hf : Integrable fun x : ℝ ↦ Complex.exp (((-2 * π * x * ξ : ℝ) : ℂ) * Complex.I) * m x := by
    refine hm.bdd_mul (c := 1) (by fun_prop) (Eventually.of_forall fun x ↦ ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  have h := integral_fourier_mul_eq_real hc hf
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h1 : ∫ x, Complex.exp (((-2 * π * x * ξ : ℝ) : ℂ) * Complex.I) • (m x * 𝓕 c x) =
      ∫ x, 𝓕 c x * (Complex.exp (((-2 * π * x * ξ : ℝ) : ℂ) * Complex.I) * m x) := by
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [smul_eq_mul]
    ring
  rw [h1, h]
  refine integral_congr_ae (Eventually.of_forall fun η ↦ ?_)
  dsimp only
  congr 1
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-! ### The Lorentzian against a band exponential -/

/-- The Fourier integral of the Lorentzian `x ↦ 1 / (x ^ 2 + a ^ 2)`. -/
theorem fourier_inv_sq_add_sq {a : ℂ} (ha : 0 < a.re) (τ : ℝ) :
    𝓕 (fun x : ℝ ↦ ((x : ℂ) ^ 2 + a ^ 2)⁻¹) τ =
      π / a * Complex.exp (-(2 * π * a) * (|τ| : ℝ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h := integral_cexp_div_sq_add_sq ha (-τ)
  rw [abs_neg] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [smul_eq_mul, div_eq_mul_inv]
  congr 2
  push_cast
  ring

/-- The Fourier integral of an integrable function is measurable. -/
theorem aestronglyMeasurable_fourier_real {c : ℝ → ℂ} (hc : Integrable c) :
    AEStronglyMeasurable (𝓕 c) volume :=
  (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (L := innerₗ ℝ) continuous_inner hc).aestronglyMeasurable

/-- A function supported in the band times an exponential of complex rate is integrable. -/
theorem integrable_mul_cexp_of_band {Y : ℝ} {c : ℝ → ℂ} (hc : Integrable c)
    (hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → c ξ = 0) (v : ℂ) :
    Integrable fun ξ : ℝ ↦ c ξ * Complex.exp (2 * π * v * ξ) := by
  obtain ⟨C, hC⟩ := exists_norm_complexBandExp_le Y v
  have h := hc.mul_bdd (measurable_complexBandExp Y v).aestronglyMeasurable
    (Eventually.of_forall hC)
  refine h.congr (Eventually.of_forall fun ξ ↦ ?_)
  dsimp only
  by_cases hξ : ξ ∈ Icc (-Y) Y
  · rw [complexBandExp_of_mem hξ]
  · rw [hsupp ξ hξ, zero_mul, zero_mul]

/-- The integral over the band of an exponential against a two-sided exponential centred at a
point `-s` of the band. -/
theorem integral_cexp_mul_cexp_abs_add {Y s : ℝ} (hs : s ∈ Icc (-Y) Y) {u a : ℂ}
    (h1 : a - u ≠ 0) (h2 : u + a ≠ 0) :
    ∫ ξ in (-Y)..Y, Complex.exp (-(2 * π * u) * ξ) *
        Complex.exp (-(2 * π * a) * (|ξ + s| : ℝ)) =
      (Complex.exp (2 * π * u * s) -
          Complex.exp (2 * π * a * s) * Complex.exp (-(2 * π * (a - u)) * Y)) /
        (2 * π * (a - u)) +
      (Complex.exp (2 * π * u * s) -
          Complex.exp (-(2 * π * a * s)) * Complex.exp (-(2 * π * (u + a)) * Y)) /
        (2 * π * (u + a)) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hint : ∀ p q : ℝ, IntervalIntegrable (fun ξ : ℝ ↦ Complex.exp (-(2 * π * u) * ξ) *
      Complex.exp (-(2 * π * a) * (|ξ + s| : ℝ))) volume p q := fun p q ↦
    (by fun_prop : Continuous fun ξ : ℝ ↦ Complex.exp (-(2 * π * u) * ξ) *
      Complex.exp (-(2 * π * a) * (|ξ + s| : ℝ))).intervalIntegrable p q
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-Y) (-s)) (hint (-s) Y)]
  have hA : ∫ ξ in (-Y)..(-s), Complex.exp (-(2 * π * u) * ξ) *
        Complex.exp (-(2 * π * a) * (|ξ + s| : ℝ)) =
      ∫ ξ in (-Y)..(-s), Complex.exp (2 * π * a * s) *
        Complex.exp (2 * π * (a - u) * ξ) := by
    refine intervalIntegral.integral_congr fun ξ hξ ↦ ?_
    rw [uIcc_of_le (by linarith [hs.2])] at hξ
    have habs : |ξ + s| = -(ξ + s) := abs_of_nonpos (by linarith [hξ.2])
    rw [habs, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hB : ∫ ξ in (-s)..Y, Complex.exp (-(2 * π * u) * ξ) *
        Complex.exp (-(2 * π * a) * (|ξ + s| : ℝ)) =
      ∫ ξ in (-s)..Y, Complex.exp (-(2 * π * a * s)) *
        Complex.exp (-(2 * π * (u + a)) * ξ) := by
    refine intervalIntegral.integral_congr fun ξ hξ ↦ ?_
    rw [uIcc_of_le (by linarith [hs.1])] at hξ
    have habs : |ξ + s| = ξ + s := abs_of_nonneg (by linarith [hξ.1])
    rw [habs, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hc1 : 2 * π * (a - u) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hπ) h1
  have hc2 : -(2 * π * (u + a)) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero hπ) h2)
  rw [hA, hB, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_exp_mul_complex hc1, integral_exp_mul_complex hc2]
  have e1 : Complex.exp (2 * π * a * s) * Complex.exp (2 * π * (a - u) * ((-s : ℝ) : ℂ)) =
      Complex.exp (2 * π * u * s) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e2 : Complex.exp (2 * π * (a - u) * ((-Y : ℝ) : ℂ)) =
      Complex.exp (-(2 * π * (a - u)) * Y) := by
    congr 1
    push_cast
    ring
  have e3 : Complex.exp (-(2 * π * a * s)) * Complex.exp (-(2 * π * (u + a)) * ((-s : ℝ) : ℂ)) =
      Complex.exp (2 * π * u * s) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e2, div_neg]
  linear_combination (1 / (2 * π * (a - u))) * e1 + (1 / (2 * π * (u + a))) * e3

/-- The integral of a band exponential against the two-sided exponential centred at a point
`-s` of the band. -/
theorem integral_complexBandExp_mul_cexp_abs_add {Y s : ℝ} (hs : s ∈ Icc (-Y) Y) {u a : ℂ}
    (h1 : a - u ≠ 0) (h2 : u + a ≠ 0) :
    ∫ ξ, complexBandExp Y (-u) ξ * (π / a * Complex.exp (-(2 * π * a) * (|ξ + s| : ℝ))) =
      π / a * ((Complex.exp (2 * π * u * s) -
          Complex.exp (2 * π * a * s) * Complex.exp (-(2 * π * (a - u)) * Y)) /
        (2 * π * (a - u)) +
      (Complex.exp (2 * π * u * s) -
          Complex.exp (-(2 * π * a * s)) * Complex.exp (-(2 * π * (u + a)) * Y)) /
        (2 * π * (u + a))) := by
  have hYY : -Y ≤ Y := hs.1.trans hs.2
  rw [← integral_cexp_mul_cexp_abs_add hs h1 h2, ← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le hYY, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  refine integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_)
  dsimp only
  by_cases hξ : ξ ∈ Icc (-Y) Y
  · rw [complexBandExp_of_mem hξ, indicator_of_mem hξ]
    have : Complex.exp (2 * π * -u * ξ) = Complex.exp (-(2 * π * u) * ξ) := by
      congr 1
      ring
    rw [this]
    ring
  · rw [complexBandExp_of_notMem hξ, indicator_of_notMem hξ, zero_mul]

/-- The two-sided Laplace transform of an odd function is odd. -/
theorem bandLaplace_neg_of_odd {c : ℝ → ℂ} (hodd : ∀ ξ, c (-ξ) = -c ξ) (v : ℂ) :
    bandLaplace c (-v) = -bandLaplace c v := by
  unfold bandLaplace
  rw [← integral_neg_eq_self _ volume, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_)
  dsimp only
  rw [hodd, neg_mul]
  congr 2
  push_cast
  ring_nf

/-- **The Lorentzian against a band exponential.** For `c` integrable and supported in the
band, the integral of the Fourier integral of the band exponential of rate `-u` against the
Lorentzian of parameter `a` times the Fourier integral of `c` is a combination of the two-sided
Laplace transform of `c` at `u`, `a` and `-a`. -/
theorem integral_fourier_complexBandExp_mul_lorentz_mul_fourier {Y : ℝ} {u a : ℂ}
    (ha : 0 < a.re) (h1 : a - u ≠ 0) (h2 : u + a ≠ 0) {c : ℝ → ℂ} (hc : Integrable c)
    (hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → c ξ = 0) :
    ∫ x, 𝓕 (complexBandExp Y (-u)) x * (((x : ℂ) ^ 2 + a ^ 2)⁻¹ * 𝓕 c x) =
      π / a * ((bandLaplace c u - bandLaplace c a * Complex.exp (-(2 * π * (a - u)) * Y)) /
          (2 * π * (a - u)) +
        (bandLaplace c u - bandLaplace c (-a) * Complex.exp (-(2 * π * (u + a)) * Y)) /
          (2 * π * (u + a))) := by
  have hmi : Integrable fun x : ℝ ↦ ((x : ℂ) ^ 2 + a ^ 2)⁻¹ := integrable_inv_sq_add_sq ha
  have hFc : AEStronglyMeasurable (𝓕 c) volume := aestronglyMeasurable_fourier_real hc
  have hG : Integrable fun x : ℝ ↦ ((x : ℂ) ^ 2 + a ^ 2)⁻¹ * 𝓕 c x :=
    hmi.mul_bdd hFc (Eventually.of_forall fun x ↦ Real.norm_fourier_le_integral_norm c x)
  rw [integral_fourier_mul_eq_real (integrable_complexBandExp Y (-u)) hG]
  set lam : ℝ → ℂ := fun τ ↦ π / a * Complex.exp (-(2 * π * a) * (|τ| : ℝ)) with hlam
  have hstep : ∀ ξ, 𝓕 (fun x : ℝ ↦ ((x : ℂ) ^ 2 + a ^ 2)⁻¹ * 𝓕 c x) ξ =
      ∫ η, c η * lam (ξ + η) := fun ξ ↦ by
    rw [fourier_mul_fourier_eq hmi hc]
    refine integral_congr_ae (Eventually.of_forall fun η ↦ ?_)
    dsimp only
    rw [fourier_inv_sq_add_sq ha]
  simp_rw [hstep]
  have hlam_bound : ∀ τ, ‖lam τ‖ ≤ ‖(π : ℂ) / a‖ := fun τ ↦ by
    have hre : (-(2 * π * a) * ((|τ| : ℝ) : ℂ)).re ≤ 0 := by
      have : (-(2 * π * a) * ((|τ| : ℝ) : ℂ)).re = -(2 * π * a.re * |τ|) := by
        simp
      rw [this]
      have := abs_nonneg τ
      have := Real.pi_pos
      nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * π) ha.le) (abs_nonneg τ)]
    calc ‖lam τ‖ = ‖(π : ℂ) / a‖ * Real.exp (-(2 * π * a) * ((|τ| : ℝ) : ℂ)).re := by
          rw [hlam, norm_mul, Complex.norm_exp]
      _ ≤ ‖(π : ℂ) / a‖ * 1 := by
          gcongr
          exact Real.exp_le_one_iff.mpr hre
      _ = ‖(π : ℂ) / a‖ := mul_one _
  have hlam_c : Continuous lam := by
    rw [hlam]
    fun_prop
  have hint : Integrable
      (Function.uncurry fun ξ η : ℝ ↦ complexBandExp Y (-u) ξ * (c η * lam (ξ + η)))
      (volume.prod volume) := by
    have h0 := ((integrable_complexBandExp Y (-u)).mul_prod hc).mul_bdd
      (g := fun p : ℝ × ℝ ↦ lam (p.1 + p.2))
      (hlam_c.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
      (Eventually.of_forall fun p ↦ hlam_bound _)
    refine h0.congr (Eventually.of_forall fun p ↦ ?_)
    simp only [Function.uncurry]
    ring
  have hswap : ∫ ξ, complexBandExp Y (-u) ξ * ∫ η, c η * lam (ξ + η) =
      ∫ η, c η * ∫ ξ, complexBandExp Y (-u) ξ * lam (ξ + η) := by
    simp_rw [← integral_const_mul]
    rw [integral_integral_swap hint]
    refine integral_congr_ae (Eventually.of_forall fun η ↦ ?_)
    refine integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_)
    ring
  rw [hswap]
  have hinner : ∀ η, c η * ∫ ξ, complexBandExp Y (-u) ξ * lam (ξ + η) =
      c η * (π / a * ((Complex.exp (2 * π * u * η) -
          Complex.exp (2 * π * a * η) * Complex.exp (-(2 * π * (a - u)) * Y)) /
        (2 * π * (a - u)) +
      (Complex.exp (2 * π * u * η) -
          Complex.exp (-(2 * π * a * η)) * Complex.exp (-(2 * π * (u + a)) * Y)) /
        (2 * π * (u + a)))) := fun η ↦ by
    by_cases hη : η ∈ Icc (-Y) Y
    · rw [← integral_complexBandExp_mul_cexp_abs_add hη h1 h2]
    · rw [hsupp η hη, zero_mul, zero_mul]
  simp_rw [hinner]
  have iu := integrable_mul_cexp_of_band hc hsupp u
  have ia := integrable_mul_cexp_of_band hc hsupp a
  have ina := integrable_mul_cexp_of_band hc hsupp (-a)
  have hpt : ∀ η : ℝ, c η * (π / a * ((Complex.exp (2 * π * u * η) -
          Complex.exp (2 * π * a * η) * Complex.exp (-(2 * π * (a - u)) * Y)) /
        (2 * π * (a - u)) +
      (Complex.exp (2 * π * u * η) -
          Complex.exp (-(2 * π * a * η)) * Complex.exp (-(2 * π * (u + a)) * Y)) /
        (2 * π * (u + a)))) =
      (π / a * (1 / (2 * π * (a - u)) + 1 / (2 * π * (u + a)))) *
          (c η * Complex.exp (2 * π * u * η)) -
        (π / a * (Complex.exp (-(2 * π * (a - u)) * Y) / (2 * π * (a - u)))) *
          (c η * Complex.exp (2 * π * a * η)) -
        (π / a * (Complex.exp (-(2 * π * (u + a)) * Y) / (2 * π * (u + a)))) *
          (c η * Complex.exp (2 * π * -a * η)) := fun η ↦ by
    have : Complex.exp (-(2 * π * a * η)) = Complex.exp (2 * π * -a * η) := by
      congr 1
      ring
    rw [this]
    ring
  simp_rw [hpt]
  rw [integral_sub, integral_sub, integral_const_mul, integral_const_mul, integral_const_mul]
  · simp only [bandLaplace]
    ring
  · exact iu.const_mul _
  · exact ia.const_mul _
  · exact (iu.const_mul _).sub (ia.const_mul _)
  · exact ina.const_mul _

/-! ### The evaluation at `ζ` and the multiplier of the weighted band -/

/-- The rate `u₀ = -i ζ = e ^ (-i π / 4)`. Evaluating the two-sided Laplace transform of the
frequency data at `u₀` is evaluating the function at `ζ`. -/
def weightedRate : ℂ := -Complex.I * weightedZero

/-- `u₀ ^ 2 = -i`. -/
theorem weightedRate_sq : weightedRate ^ 2 = -Complex.I := by
  rw [weightedRate, mul_pow, weightedZero_sq, neg_sq, Complex.I_sq]
  ring

/-- The real part of `u₀`. -/
theorem weightedRate_re : weightedRate.re = 1 / √2 := by
  simp [weightedRate, weightedZero_im]

/-- The real part of `u₀` is positive. -/
theorem weightedRate_re_pos : 0 < weightedRate.re := by
  rw [weightedRate_re]
  positivity

/-- `u₀` is not zero. -/
theorem weightedRate_ne_zero : weightedRate ≠ 0 := fun h ↦ by
  have := weightedRate_re_pos
  rw [h] at this
  simp at this

/-- The vector of `L²(ℝ)` whose pairing with a function of the band is its value at `ζ`. -/
def weightedEvalVector (Y : ℝ) : H := complexBandVector Y (conj weightedRate)

/-- **The multiplier of the weighted band, evaluated at `ζ` after the band projection.** For
odd frequency data `c` supported in the band, with `F` its Fourier integral, the pairing of the
evaluation vector at `ζ` with `r_g F` is `√g E (Y)` times the value of `F` at `g ζ`. The term
with the value at `ζ` cancels because `r_g` vanishes at `ζ`. -/
theorem inner_weightedEvalVector_multiplier_mul_fourier {Y g : ℝ} (hg : 1 < g) {c : ℝ → ℂ}
    (hc1 : Integrable c) (hc2 : MemLp c 2) (hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → c ξ = 0)
    (hodd : ∀ ξ, c (-ξ) = -c ξ) {V : H}
    (hV : (V : ℝ → ℂ) =ᵐ[volume] fun x ↦ weightedDilationMultiplier g x * 𝓕 c x) :
    ⟪weightedEvalVector Y, V⟫_ℂ =
      ((√g : ℝ) : ℂ) * weightedBandDefect Y g * bandLaplace c (g * weightedRate) := by
  have hg0 : 0 < g := by linarith
  have hgc : (g : ℂ) ≠ 0 := by exact_mod_cast hg0.ne'
  have hgm : (g : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hg.ne')
  have hgp : (g : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : g + 1 ≠ 0)
  have hsg : ((√g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hg0).ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hu0 := weightedRate_ne_zero
  have ha : 0 < ((g : ℂ) * weightedRate).re := by
    rw [Complex.re_ofReal_mul]
    exact mul_pos hg0 weightedRate_re_pos
  have hasq : ((g : ℂ) * weightedRate) ^ 2 = -Complex.I * (g : ℂ) ^ 2 := by
    rw [mul_pow, weightedRate_sq]
    ring
  have h1 : (g : ℂ) * weightedRate - weightedRate ≠ 0 := by
    rw [show (g : ℂ) * weightedRate - weightedRate = ((g : ℂ) - 1) * weightedRate by ring]
    exact mul_ne_zero hgm hu0
  have h2 : weightedRate + (g : ℂ) * weightedRate ≠ 0 := by
    rw [show weightedRate + (g : ℂ) * weightedRate = ((g : ℂ) + 1) * weightedRate by ring]
    exact mul_ne_zero hgp hu0
  rw [weightedEvalVector, inner_complexBandVector_eq_integral, Complex.conj_conj]
  have hpt : ∀ᵐ x, 𝓕 (complexBandExp Y (-weightedRate)) x * V x =
      (g : ℂ) * (𝓕 (complexBandExp Y (-weightedRate)) x * 𝓕 c x) +
        (Complex.I * g * ((g : ℂ) ^ 2 - 1)) * (𝓕 (complexBandExp Y (-weightedRate)) x *
          (((x : ℂ) ^ 2 + ((g : ℂ) * weightedRate) ^ 2)⁻¹ * 𝓕 c x)) := by
    filter_upwards [hV] with x hx
    rw [hx, weightedDilationMultiplier_eq hg0.ne', hasq]
    have : (x : ℂ) ^ 2 + -Complex.I * (g : ℂ) ^ 2 = (x : ℂ) ^ 2 - Complex.I * (g : ℂ) ^ 2 := by
      ring
    rw [this, div_eq_mul_inv]
    ring
  rw [integral_congr_ae hpt]
  have i1 : Integrable fun x ↦ 𝓕 (complexBandExp Y (-weightedRate)) x * 𝓕 c x := by
    have h := L2.integrable_inner (𝕜 := ℂ) (complexBandVector Y (conj weightedRate))
      (𝓕 (hc2.toLp c) : H)
    refine h.congr ?_
    filter_upwards [fourier_ae_eq_fourier_toLp (integrable_complexBandExp Y (conj weightedRate))
      (memLp_complexBandExp Y _), fourier_ae_eq_fourier_toLp hc1 hc2] with x e1 e2
    rw [complexBandVector, ← e1, ← e2, RCLike.inner_apply, conj_fourier_complexBandExp,
      Complex.conj_conj, mul_comm]
  have hT1 : ∫ x, 𝓕 (complexBandExp Y (-weightedRate)) x * 𝓕 c x =
      bandLaplace c weightedRate := by
    have h := inner_complexBandVector_eq_integral Y (conj weightedRate) (𝓕 (hc2.toLp c) : H)
    rw [Complex.conj_conj, inner_complexBandVector_fourier _ hc2 hsupp, Complex.conj_conj] at h
    rw [h]
    refine integral_congr_ae ?_
    filter_upwards [fourier_ae_eq_fourier_toLp hc1 hc2] with x hx
    rw [hx]
  have i2 : Integrable fun x : ℝ ↦ 𝓕 (complexBandExp Y (-weightedRate)) x *
      (((x : ℂ) ^ 2 + ((g : ℂ) * weightedRate) ^ 2)⁻¹ * 𝓕 c x) := by
    have hG := (integrable_inv_sq_add_sq ha).mul_bdd (aestronglyMeasurable_fourier_real hc1)
      (Eventually.of_forall fun x ↦ Real.norm_fourier_le_integral_norm c x)
    exact hG.bdd_mul (aestronglyMeasurable_fourier_real (integrable_complexBandExp Y _))
      (Eventually.of_forall fun x ↦ Real.norm_fourier_le_integral_norm _ x)
  rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    hT1, integral_fourier_complexBandExp_mul_lorentz_mul_fourier ha h1 h2 hc1 hsupp,
    bandLaplace_neg_of_odd hodd]
  have hE1 : Complex.exp (-(2 * π * ((g : ℂ) * weightedRate - weightedRate)) * Y) =
      Complex.exp (2 * π * Complex.I * Y * (g - 1) * weightedZero) := by
    congr 1
    rw [weightedRate]
    ring
  have hE2 : Complex.exp (-(2 * π * (weightedRate + (g : ℂ) * weightedRate)) * Y) =
      Complex.exp (2 * π * Complex.I * Y * (g + 1) * weightedZero) := by
    congr 1
    rw [weightedRate]
    ring
  rw [hE1, hE2, weightedBandDefect]
  generalize Complex.exp (2 * π * Complex.I * Y * (g - 1) * weightedZero) = E1
  generalize Complex.exp (2 * π * Complex.I * Y * (g + 1) * weightedZero) = E2
  generalize bandLaplace c weightedRate = B0
  generalize bandLaplace c ((g : ℂ) * weightedRate) = Ba
  have key : (Complex.I * g * ((g : ℂ) ^ 2 - 1)) * (π / ((g : ℂ) * weightedRate) *
      ((B0 - Ba * E1) / (2 * π * ((g : ℂ) * weightedRate - weightedRate)) +
        (B0 - -Ba * E2) / (2 * π * (weightedRate + (g : ℂ) * weightedRate)))) =
      (Complex.I * (weightedRate ^ 2)⁻¹) *
        ((((g : ℂ) + 1) * (B0 - Ba * E1) + ((g : ℂ) - 1) * (B0 + Ba * E2)) / 2) := by
    rw [show (g : ℂ) * weightedRate - weightedRate = ((g : ℂ) - 1) * weightedRate by ring,
      show weightedRate + (g : ℂ) * weightedRate = ((g : ℂ) + 1) * weightedRate by ring]
    field_simp
    ring
  rw [key, weightedRate_sq, inv_neg, Complex.inv_I, neg_neg, Complex.I_mul_I]
  push_cast
  field_simp
  ring

/-! ### The reproducing vector of the odd band at `ζ` -/

/-- The frequency data of the reproducing vector of the odd band at `ζ`: the odd part of the
band exponential of rate `conj u₀`. -/
def weightedKernelExp (Y : ℝ) (ξ : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (complexBandExp Y (conj weightedRate) ξ -
    complexBandExp Y (-conj weightedRate) ξ)

/-- The frequency data of the reproducing vector is integrable. -/
theorem integrable_weightedKernelExp (Y : ℝ) : Integrable (weightedKernelExp Y) :=
  ((integrable_complexBandExp Y _).sub (integrable_complexBandExp Y _)).const_mul _

/-- The frequency data of the reproducing vector is square-integrable. -/
theorem memLp_weightedKernelExp (Y : ℝ) : MemLp (weightedKernelExp Y) 2 :=
  ((memLp_complexBandExp Y _).sub (memLp_complexBandExp Y _)).const_mul _

/-- The frequency data of the reproducing vector vanishes outside the band. -/
theorem weightedKernelExp_of_notMem {Y ξ : ℝ} (h : ξ ∉ Icc (-Y) Y) :
    weightedKernelExp Y ξ = 0 := by
  rw [weightedKernelExp, complexBandExp_of_notMem h, complexBandExp_of_notMem h, sub_zero,
    mul_zero]

/-- The frequency data of the reproducing vector is odd. -/
theorem weightedKernelExp_neg (Y ξ : ℝ) : weightedKernelExp Y (-ξ) = -weightedKernelExp Y ξ := by
  simp only [weightedKernelExp, complexBandExp_neg, neg_neg]
  ring

/-- The reproducing vector of the odd band at `ζ`: pairing with it evaluates an odd function
of the band at `ζ`. -/
def weightedKernelVector (Y : ℝ) : H :=
  𝓕 ((memLp_weightedKernelExp Y).toLp (weightedKernelExp Y))

/-- The reproducing vector is the class of the Fourier integral of its frequency data. -/
theorem coeFn_weightedKernelVector (Y : ℝ) :
    (weightedKernelVector Y : ℝ → ℂ) =ᵐ[volume] 𝓕 (weightedKernelExp Y) :=
  (fourier_ae_eq_fourier_toLp (integrable_weightedKernelExp Y) (memLp_weightedKernelExp Y)).symm

/-- The Fourier integral of an odd function is odd. -/
theorem fourier_neg_of_odd {c : ℝ → ℂ} (hodd : ∀ ξ, c (-ξ) = -c ξ) (x : ℝ) :
    𝓕 c (-x) = -𝓕 c x := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_neg_eq_self _ volume, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_)
  simp only [smul_eq_mul, hodd, mul_neg]
  congr 3
  push_cast
  ring

/-- Negating the rate of a band exponential reflects its Fourier integral. -/
theorem fourier_complexBandExp_neg (Y : ℝ) (u : ℂ) (x : ℝ) :
    𝓕 (complexBandExp Y (-u)) x = 𝓕 (complexBandExp Y u) (-x) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_neg_eq_self _ volume]
  refine integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_)
  simp only [smul_eq_mul, complexBandExp_neg, neg_neg]
  congr 2
  push_cast
  ring

/-- Against a vector that is odd, the vector of rate `-u` pairs to minus the pairing of the
vector of rate `u`. -/
theorem inner_complexBandVector_neg_of_odd (Y : ℝ) (u : ℂ) {V : H}
    (hV : ∀ᵐ x, (V : ℝ → ℂ) (-x) = -(V : ℝ → ℂ) x) :
    ⟪complexBandVector Y (-u), V⟫_ℂ = -⟪complexBandVector Y u, V⟫_ℂ := by
  rw [inner_complexBandVector_eq_integral, inner_complexBandVector_eq_integral, map_neg, neg_neg,
    ← integral_neg_eq_self _ volume, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hV] with x hx
  rw [hx, ← fourier_complexBandExp_neg, mul_neg]

/-- The reproducing vector is half the difference of the evaluation vectors at `ζ` and
`-ζ`. -/
theorem weightedKernelVector_eq (Y : ℝ) :
    weightedKernelVector Y =
      (1 / 2 : ℂ) • (weightedEvalVector Y - complexBandVector Y (-conj weightedRate)) := by
  have hlin : ∀ (c : ℂ) (u v : H), (𝓕 (c • (u - v)) : H) = c • ((𝓕 u : H) - (𝓕 v : H)) :=
    fun c u v ↦ by
      change Lp.fourierTransformₗᵢ ℝ ℂ (c • (u - v)) = _
      rw [map_smul, map_sub]
      rfl
  have hβ : (memLp_weightedKernelExp Y).toLp (weightedKernelExp Y) =
      (1 / 2 : ℂ) • ((memLp_complexBandExp Y (conj weightedRate)).toLp _ -
        (memLp_complexBandExp Y (-conj weightedRate)).toLp _) := by
    refine Lp.ext ?_
    filter_upwards [(memLp_weightedKernelExp Y).coeFn_toLp,
      Lp.coeFn_smul (1 / 2 : ℂ) ((memLp_complexBandExp Y (conj weightedRate)).toLp _ -
        (memLp_complexBandExp Y (-conj weightedRate)).toLp _),
      Lp.coeFn_sub ((memLp_complexBandExp Y (conj weightedRate)).toLp _)
        ((memLp_complexBandExp Y (-conj weightedRate)).toLp _),
      (memLp_complexBandExp Y (conj weightedRate)).coeFn_toLp,
      (memLp_complexBandExp Y (-conj weightedRate)).coeFn_toLp] with ξ e1 e2 e3 e4 e5
    rw [e1, e2, Pi.smul_apply, e3, Pi.sub_apply, e4, e5]
    rfl
  rw [weightedKernelVector, hβ, hlin]
  rfl

/-- Against a vector that is odd, the reproducing vector pairs like the evaluation vector at
`ζ`. -/
theorem inner_weightedKernelVector_of_odd (Y : ℝ) {V : H}
    (hV : ∀ᵐ x, (V : ℝ → ℂ) (-x) = -(V : ℝ → ℂ) x) :
    ⟪weightedKernelVector Y, V⟫_ℂ = ⟪weightedEvalVector Y, V⟫_ℂ := by
  rw [weightedKernelVector_eq, inner_smul_left, inner_sub_left,
    inner_complexBandVector_neg_of_odd Y _ hV, weightedEvalVector]
  simp only [map_div₀, map_one, map_ofNat]
  ring

/-- The reproducing vector is odd. -/
theorem weightedKernelVector_neg_ae (Y : ℝ) :
    ∀ᵐ x, (weightedKernelVector Y : ℝ → ℂ) (-x) = -(weightedKernelVector Y : ℝ → ℂ) x := by
  have h := coeFn_weightedKernelVector Y
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)
    ).quasiMeasurePreserving.ae_eq_comp
    h
  filter_upwards [h, hneg] with x h1 h2
  have h3 : (weightedKernelVector Y : ℝ → ℂ) (-x) = 𝓕 (weightedKernelExp Y) (-x) := h2
  rw [h3, h1, fourier_neg_of_odd (weightedKernelExp_neg Y)]

/-- The square of the norm of the reproducing vector is its value at `ζ`. -/
theorem inner_weightedKernelVector_self (Y : ℝ) :
    ⟪weightedKernelVector Y, weightedKernelVector Y⟫_ℂ =
      bandLaplace (weightedKernelExp Y) weightedRate := by
  rw [inner_weightedKernelVector_of_odd Y (weightedKernelVector_neg_ae Y), weightedEvalVector,
    weightedKernelVector,
    inner_complexBandVector_fourier _ _ (fun ξ h ↦ weightedKernelExp_of_notMem h),
    Complex.conj_conj]

/-- The reproducing vector lies in the odd band. -/
theorem weightedKernelVector_mem (Y : ℝ) : weightedKernelVector Y ∈ realOddBand Y := by
  rw [mem_realOddBand_iff, mem_realOddBandFourier_iff, weightedKernelVector, lp_fourier_fourier]
  have h1 := Lp.coeFn_compMeasurePreserving
    ((memLp_weightedKernelExp Y).toLp (weightedKernelExp Y))
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  have h2 := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
    (memLp_weightedKernelExp Y).coeFn_toLp
  have hco : (realReflection ((memLp_weightedKernelExp Y).toLp (weightedKernelExp Y)) : ℝ → ℂ)
      =ᵐ[volume] fun ξ ↦ weightedKernelExp Y (-ξ) := by
    filter_upwards [h1, h2] with ξ e1 e2
    exact e1.trans e2
  refine ⟨?_, ?_⟩
  · filter_upwards [hco] with ξ h hξ
    rw [h, weightedKernelExp_of_notMem (mt neg_mem_band.mp hξ)]
  · have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)
      ).quasiMeasurePreserving.ae_eq_comp hco
    filter_upwards [hco, hneg] with ξ e1 e2
    have e3 : (realReflection ((memLp_weightedKernelExp Y).toLp (weightedKernelExp Y)) :
        ℝ → ℂ) (-ξ) = weightedKernelExp Y (- -ξ) := e2
    rw [e1, e3, neg_neg, weightedKernelExp_neg, neg_neg]

/-- The reproducing vector is not zero. -/
theorem weightedKernelVector_ne_zero {Y : ℝ} (hY : 0 < Y) : weightedKernelVector Y ≠ 0 := by
  intro h
  have h0 : (memLp_weightedKernelExp Y).toLp (weightedKernelExp Y) = 0 := by
    change Lp.fourierTransformₗᵢ ℝ ℂ _ = 0 at h
    exact (LinearIsometryEquiv.map_eq_zero_iff _).mp h
  have hae : weightedKernelExp Y =ᵐ[volume] 0 := by
    have h1 := (memLp_weightedKernelExp Y).coeFn_toLp
    rw [h0] at h1
    exact h1.symm.trans (Lp.coeFn_zero ℂ 2 volume)
  have hsub : Ioc 0 Y ⊆ {ξ | ¬ weightedKernelExp Y ξ = (0 : ℝ → ℂ) ξ} := by
    intro ξ hξ hzero
    have hmem : ξ ∈ Icc (-Y) Y := ⟨by linarith [hξ.1], hξ.2⟩
    have hzero' : weightedKernelExp Y ξ = 0 := hzero
    rw [weightedKernelExp, complexBandExp_of_mem hmem, complexBandExp_of_mem hmem] at hzero'
    have heq : Complex.exp (2 * π * conj weightedRate * ξ) =
        Complex.exp (2 * π * -conj weightedRate * ξ) := by
      have := (mul_eq_zero.mp hzero').resolve_left (by norm_num)
      exact sub_eq_zero.mp this
    have hn := congrArg norm heq
    rw [Complex.norm_exp, Complex.norm_exp] at hn
    have hre : (2 * π * conj weightedRate * ξ).re = 2 * π * weightedRate.re * ξ := by
      simp
    have hre' : (2 * π * -conj weightedRate * ξ).re = -(2 * π * weightedRate.re * ξ) := by
      simp
    rw [hre, hre'] at hn
    have := Real.exp_injective hn
    have hpos : 0 < 2 * π * weightedRate.re * ξ :=
      mul_pos (mul_pos (by positivity) weightedRate_re_pos) hξ.1
    linarith
  have hnull : volume (Ioc 0 Y) = 0 := measure_mono_null hsub (ae_iff.mp hae)
  rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at hnull
  linarith

/-! ### The dilate of the reproducing vector and the rank-one term -/

/-- A bounded measurable function that vanishes outside the band is square-integrable. -/
theorem memLp_of_norm_le_of_band {Y : ℝ} {c : ℝ → ℂ} (hm : Measurable c) {C : ℝ}
    (hC : ∀ ξ, ‖c ξ‖ ≤ C) (hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → c ξ = 0) : MemLp c 2 := by
  have h : MemLp ((Icc (-Y) Y).indicator fun _ : ℝ ↦ (C : ℝ)) 2 := by
    rw [memLp_indicator_iff_restrict
      (measurableSet_Icc : MeasurableSet (Icc (-Y) Y)).nullMeasurableSet]
    have : IsFiniteMeasure (volume.restrict (Icc (-Y) Y)) :=
      ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
    exact memLp_const C
  refine h.mono hm.aestronglyMeasurable (Eventually.of_forall fun ξ ↦ ?_)
  by_cases hξ : ξ ∈ Icc (-Y) Y
  · rw [indicator_of_mem hξ, Real.norm_eq_abs]
    exact (hC ξ).trans (le_abs_self C)
  · simp [hsupp ξ hξ, hξ]

/-- The Fourier integral of the rescaled frequency data `η ↦ √g b (g η)` is the unitary dilate
of the Fourier integral of `b`. -/
theorem fourier_sqrt_mul_comp_mul {g : ℝ} (hg : 0 < g) (b : ℝ → ℂ) (x : ℝ) :
    𝓕 (fun η : ℝ ↦ ((√g : ℝ) : ℂ) * b (g * η)) x = (((√g)⁻¹ : ℝ) : ℂ) * 𝓕 b (x / g) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  have h := Measure.integral_comp_mul_left (fun ξ : ℝ ↦
    ((√g : ℝ) : ℂ) * (Complex.exp (((-2 * π * ξ * (x / g) : ℝ) : ℂ) * Complex.I) • b ξ)) g
  have hl : ∫ η : ℝ, Complex.exp (((-2 * π * η * x : ℝ) : ℂ) * Complex.I) •
        (((√g : ℝ) : ℂ) * b (g * η)) =
      ∫ η : ℝ, ((√g : ℝ) : ℂ) *
        (Complex.exp (((-2 * π * (g * η) * (x / g) : ℝ) : ℂ) * Complex.I) • b (g * η)) := by
    refine integral_congr_ae (Eventually.of_forall fun η ↦ ?_)
    have : -2 * π * (g * η) * (x / g) = -2 * π * η * x := by
      field_simp
    simp only [smul_eq_mul, this]
    ring
  rw [hl, h, abs_of_pos (inv_pos.mpr hg), integral_const_mul, Complex.real_smul, ← mul_assoc]
  congr 1
  have hs : (√g) ^ 2 = g := Real.sq_sqrt hg.le
  have hs0 : √g ≠ 0 := (Real.sqrt_pos.mpr hg).ne'
  rw [← Complex.ofReal_mul]
  congr 1
  field_simp
  rw [hs]

/-- The two-sided Laplace transform of the rescaled frequency data. -/
theorem bandLaplace_sqrt_mul_comp_mul {g : ℝ} (hg : 0 < g) (b : ℝ → ℂ) (v : ℂ) :
    bandLaplace (fun η : ℝ ↦ ((√g : ℝ) : ℂ) * b (g * η)) (g * v) =
      (((√g)⁻¹ : ℝ) : ℂ) * bandLaplace b v := by
  unfold bandLaplace
  have h := Measure.integral_comp_mul_left (fun ξ : ℝ ↦
    ((√g : ℝ) : ℂ) * (b ξ * Complex.exp (2 * π * v * ξ))) g
  have hl : ∫ η : ℝ, ((√g : ℝ) : ℂ) * b (g * η) * Complex.exp (2 * π * (g * v) * η) =
      ∫ η : ℝ, ((√g : ℝ) : ℂ) * (b (g * η) * Complex.exp (2 * π * v * ((g * η : ℝ) : ℂ))) := by
    refine integral_congr_ae (Eventually.of_forall fun η ↦ ?_)
    have : 2 * π * (g * v) * η = 2 * π * v * ((g * η : ℝ) : ℂ) := by
      push_cast
      ring
    dsimp only
    rw [this]
    ring
  rw [hl, h, abs_of_pos (inv_pos.mpr hg), integral_const_mul, Complex.real_smul, ← mul_assoc]
  congr 1
  have hs : (√g) ^ 2 = g := Real.sq_sqrt hg.le
  have hs0 : √g ≠ 0 := (Real.sqrt_pos.mpr hg).ne'
  rw [← Complex.ofReal_mul]
  congr 1
  field_simp
  rw [hs]

/-- **The rank-one term.** Let `k` be the reproducing vector of the odd band at `ζ` and `V` the
class of `r_g D_g k`. Then `⟪k, V⟫ = E (Y) ⟪k, k⟫`, with `E (Y) = weightedBandDefect Y g`: the
same term as in the limit of the trace over the odd band. -/
theorem inner_weightedKernelVector_multiplier_dilation {Y g : ℝ} (hY : 0 ≤ Y) (hg : 1 < g)
    {V : H} (hV : (V : ℝ → ℂ) =ᵐ[volume] fun x ↦
      weightedDilationMultiplier g x * (realDilation g (weightedKernelVector Y) : H) x) :
    ⟪weightedKernelVector Y, V⟫_ℂ =
      weightedBandDefect Y g * ⟪weightedKernelVector Y, weightedKernelVector Y⟫_ℂ := by
  have hg0 : 0 < g := by linarith
  have hsg : ((√g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hg0).ne'
  have hsupp : ∀ η, η ∉ Icc (-Y) Y →
      ((√g : ℝ) : ℂ) * weightedKernelExp Y (g * η) = 0 := fun η hη ↦ by
    have : g * η ∉ Icc (-Y) Y := by
      intro h
      apply hη
      constructor
      · rcases le_or_gt 0 η with h0 | h0
        · linarith
        · nlinarith [h.1]
      · rcases le_or_gt η 0 with h0 | h0
        · linarith
        · nlinarith [h.2]
    rw [weightedKernelExp_of_notMem this, mul_zero]
  have hodd : ∀ η, ((√g : ℝ) : ℂ) * weightedKernelExp Y (g * -η) =
      -(((√g : ℝ) : ℂ) * weightedKernelExp Y (g * η)) := fun η ↦ by
    rw [mul_neg, weightedKernelExp_neg, mul_neg]
  have hc1 : Integrable fun η : ℝ ↦ ((√g : ℝ) : ℂ) * weightedKernelExp Y (g * η) :=
    ((integrable_weightedKernelExp Y).comp_mul_left' hg0.ne').const_mul _
  have hmeas : Measurable fun η : ℝ ↦ ((√g : ℝ) : ℂ) * weightedKernelExp Y (g * η) := by
    unfold weightedKernelExp
    exact measurable_const.mul (measurable_const.mul
      (((measurable_complexBandExp Y _).comp (measurable_const.mul measurable_id)).sub
        ((measurable_complexBandExp Y _).comp (measurable_const.mul measurable_id))))
  obtain ⟨C1, hC1⟩ := exists_norm_complexBandExp_le Y (conj weightedRate)
  obtain ⟨C2, hC2⟩ := exists_norm_complexBandExp_le Y (-conj weightedRate)
  have hc2 : MemLp (fun η : ℝ ↦ ((√g : ℝ) : ℂ) * weightedKernelExp Y (g * η)) 2 := by
    refine memLp_of_norm_le_of_band hmeas (C := ‖((√g : ℝ) : ℂ)‖ * (‖(1 / 2 : ℂ)‖ * (C1 + C2)))
      (fun η ↦ ?_) hsupp
    rw [norm_mul, weightedKernelExp, norm_mul]
    gcongr
    exact (norm_sub_le _ _).trans (add_le_add (hC1 _) (hC2 _))
  have hVc : (V : ℝ → ℂ) =ᵐ[volume] fun x ↦ weightedDilationMultiplier g x *
      𝓕 (fun η : ℝ ↦ ((√g : ℝ) : ℂ) * weightedKernelExp Y (g * η)) x := by
    have hk := (quasiMeasurePreserving_div_const_real hg0).ae_eq_comp
      (coeFn_weightedKernelVector Y)
    filter_upwards [hV, coeFn_realDilation hg0 (weightedKernelVector Y), hk] with x h1 h2 h3
    have h3' : (weightedKernelVector Y : ℝ → ℂ) (x / g) = 𝓕 (weightedKernelExp Y) (x / g) := h3
    rw [h1, h2, h3', fourier_sqrt_mul_comp_mul hg0]
  have hVodd : ∀ᵐ x, (V : ℝ → ℂ) (-x) = -(V : ℝ → ℂ) x := by
    have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)
      ).quasiMeasurePreserving.ae_eq_comp hVc
    filter_upwards [hVc, hneg] with x h1 h2
    have h3 : (V : ℝ → ℂ) (-x) = weightedDilationMultiplier g (-x) *
        𝓕 (fun η : ℝ ↦ ((√g : ℝ) : ℂ) * weightedKernelExp Y (g * η)) (-x) := h2
    rw [h3, h1, weightedDilationMultiplier_neg, fourier_neg_of_odd hodd, mul_neg]
  rw [inner_weightedKernelVector_of_odd Y hVodd,
    inner_weightedEvalVector_multiplier_mul_fourier hg hc1 hc2 hsupp hodd hVc,
    bandLaplace_sqrt_mul_comp_mul hg0, inner_weightedKernelVector_self]
  push_cast
  field_simp

/-- The pairing with a cutoff vector tends to the pairing with the vector as the cutoff is
removed. -/
theorem tendsto_inner_realCutoff (f V : H) :
    Tendsto (fun L : ℝ ↦ ⟪f, realCutoff L V⟫_ℂ) atTop (𝓝 ⟪f, V⟫_ℂ) := by
  have hint : Integrable fun x ↦ ⟪f x, V x⟫_ℂ := L2.integrable_inner f V
  have h := MeasureTheory.intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot
    tendsto_id
  rw [L2.inner_def]
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with L hL
  symm
  rw [L2.inner_def, id, intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_realCutoff L V] with x hx
  rw [hx]
  by_cases hmem : x ∈ Icc (-L) L
  · rw [indicator_of_mem hmem, indicator_of_mem hmem]
  · rw [indicator_of_notMem hmem, indicator_of_notMem hmem, inner_zero_right]

end RiemannMasullo
