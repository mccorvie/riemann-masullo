module

public import RiemannMasullo.Ch12_TraceGeometric.Sec1b

/-! # Absolute bounds for the smoothed diagonal of a nuclear kernel -/

@[expose] public noncomputable section

namespace RiemannMasullo.Isolated

open Filter MeasureTheory
open scoped ComplexConjugate ENNReal NNReal

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {μ ν : Measure G} [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts ν] [ν.InnerRegular]
  {U : ℕ → Set G} {w : G → ℝ≥0} {k : Lp ℂ 2 (ν.prod ν)} {κ : G × G → ℂ}

/-- Paper: Theorem 12.1.1.2(2), p. 499. Testing the multiplier trace identity
with the conjugate phase of the diagonal bounds its weighted L¹ norm by the
trace norm of the operator.
Deviation: This is an absolute bound derived from the printed multiplier trace identity. -/
theorem integral_norm_dSequenceKernelSmoothening_diagonal_le_traceNorm
    (hκ : κ =ᵐ[ν.prod ν] k) (hU : IsDPrimeSequence μ U)
    (hBorel : ∀ n, MeasurableSet (U n)) (hw : Continuous w) (hwpos : ∀ x, 0 < w x)
    (hν : ν = μ.withDensity (fun x ↦ ↑(w x)))
    (hT : IsNuclearOperator (integralKernelOperator ν k).val) :
    (∫ x, ‖dSequenceKernelSmoothening μ U κ (x, x)‖ ∂ν) ≤
      traceNorm ⟨(integralKernelOperator ν k).val, hT⟩ := by
  let d (x : G) := dSequenceKernelSmoothening μ U κ (x, x)
  have hd : Integrable d ν :=
    (integral_dSequenceKernelSmoothening_diagonal hκ hU hBorel hw hwpos hν hT).1
  let phase (x : G) := conj (d x) / (‖d x‖ : ℂ)
  have hphase_meas : AEMeasurable phase ν := by
    have hm := hd.aestronglyMeasurable.aemeasurable
    exact (Complex.continuous_conj.measurable.comp_aemeasurable hm).div
      (Complex.continuous_ofReal.measurable.comp_aemeasurable hm.norm)
  have hphase_bound (x : G) : ‖phase x‖ ≤ 1 := by
    dsimp only [phase]
    rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    by_cases h : ‖d x‖ = 0
    · simp [h]
    · rw [div_self h]
  have hphase := memLp_top_of_bound hphase_meas.aestronglyMeasurable 1
    (ae_of_all _ hphase_bound)
  let ρ := hphase.toLp phase
  have hρ : ‖ρ‖ ≤ 1 := by
    change ‖hphase.toLp phase‖ ≤ 1
    rw [Lp.norm_toLp, eLpNorm_exponent_top hphase.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (eLpNormEssSup_le_of_ae_bound (ae_of_all _ hphase_bound))
  have hphase_mul (x : G) : phase x * d x = (‖d x‖ : ℂ) := by
    by_cases h : d x = 0
    · simp [phase, h]
    have hn : (‖d x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
    dsimp only [phase]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff hn).mpr
    rw [mul_comm (conj (d x)), Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.ofReal_pow, pow_two]
  let M := (ContinuousLinearMap.mul ℂ ℂ).holderL ν ∞ 2 2 ρ
  have hM : ‖M‖ ≤ 1 := by
    calc
      _ ≤ ‖(ContinuousLinearMap.mul ℂ ℂ).holderL ν ∞ 2 2‖ * ‖ρ‖ :=
        ((ContinuousLinearMap.mul ℂ ℂ).holderL ν ∞ 2 2).le_opNorm ρ
      _ ≤ 1 * 1 := mul_le_mul
        ((ContinuousLinearMap.mul ℂ ℂ).norm_holderL_le.trans (ContinuousLinearMap.opNorm_mul_le ℂ ℂ))
        hρ (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _
  let T : nuclearEndomorphisms (Lp ℂ 2 ν) := ⟨(integralKernelOperator ν k).val, hT⟩
  let N : nuclearEndomorphisms (Lp ℂ 2 ν) := ⟨M * T.val, mul_mem_nuclearEndomorphisms_left M T⟩
  have htrace : (∫ x, ρ x * d x ∂ν) = hilbertTrace N :=
    (integral_mul_dSequenceKernelSmoothening_diagonal hκ hU hBorel hw hwpos hν hT ρ).2
  have hreal : (↑(∫ x, ‖d x‖ ∂ν) : ℂ) = hilbertTrace N := by
    rw [← integral_complex_ofReal (μ := ν) (f := fun x ↦ ‖d x‖)]
    refine (integral_congr_ae ?_).trans htrace
    filter_upwards [hphase.coeFn_toLp] with x hx
    rw [hx, hphase_mul]
  calc
    (∫ x, ‖d x‖ ∂ν) = ‖(↑(∫ x, ‖d x‖ ∂ν) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    _ = ‖hilbertTrace N‖ := congrArg norm hreal
    _ ≤ traceNorm N := norm_hilbertTrace_le _
    _ ≤ ‖M‖ * traceNorm T := traceNorm_mul_left_le M T
    _ ≤ traceNorm T := mul_le_of_le_one_left
      ((norm_nonneg _).trans (norm_hilbertTrace_le T)) hM

/-- Paper: Theorem 12.1.1.2, p. 499, and Definition 10.4.3.7, p. 473.
Putting the input density into the kernel transfers the diagonal's weighted
L¹ estimate to the Haar measure.
Deviation: The conclusion bounds the absolute Haar integral of the converted diagonal. -/
theorem integral_norm_dSequenceKernelSmoothening_haar_diagonal_le_traceNorm
    (hκ : κ =ᵐ[ν.prod ν] k) (hU : IsDPrimeSequence μ U)
    (hBorel : ∀ n, MeasurableSet (U n)) (hw : Continuous w) (hwpos : ∀ x, 0 < w x)
    (hν : ν = μ.withDensity (fun x ↦ ↑(w x)))
    (hT : IsNuclearOperator (integralKernelOperator ν k).val) :
    let dH (x : G) :=
      dSequenceKernelSmoothening μ U (fun p ↦ (w p.2 : ℂ) * κ p) (x, x)
    Integrable dH μ ∧ (∫ x, ‖dH x‖ ∂μ) ≤ traceNorm ⟨(integralKernelOperator ν k).val, hT⟩ := by
  intro dH
  let d (x : G) := dSequenceKernelSmoothening μ U κ (x, x)
  have hregular := dSequenceKernelSmoothening_mul_continuous_snd_diagonal hU hBorel hw hwpos hν hκ hT
    (fun x ↦ (w x : ℂ)) (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hw))
  have hd : (fun x ↦ w x • d x) =ᵐ[μ] dH := by
    filter_upwards [hregular] with x hx
    change (w x : ℝ) • d x = dH x
    rw [Complex.real_smul]
    exact hx.2.symm
  have hint : Integrable d ν :=
    (integral_dSequenceKernelSmoothening_diagonal hκ hU hBorel hw hwpos hν hT).1
  have hint' := hint
  rw [hν, integrable_withDensity_iff_integrable_smul hw.measurable] at hint'
  refine ⟨hint'.congr hd, ?_⟩
  calc
    (∫ x, ‖dH x‖ ∂μ) = ∫ x, w x • ‖d x‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards [hd] with x hx
      rw [← hx]
      change ‖(w x : ℝ) • d x‖ = (w x : ℝ) * ‖d x‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (w x).coe_nonneg]
    _ = ∫ x, ‖d x‖ ∂ν := by
      rw [hν, integral_withDensity_eq_integral_smul hw.measurable]
    _ ≤ _ := integral_norm_dSequenceKernelSmoothening_diagonal_le_traceNorm
      hκ hU hBorel hw hwpos hν hT

section StripSpectralKernel

open NumberField

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s
local notation "nonnegOrder(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "AP(" a ", " hα ", " hs ", " φ ")" =>
  ContinuousLinearMap.comp (hardySobolevTestAction μ𝔽 m𝔽 _ _ _ (neg_le_self hα) (nonnegOrder(hs)) φ)
    (spectralProjection (F := F) a hα (nonnegOrder(hs)))

/-- Paper: Definition 10.4.3.7, p. 473, and (12.5.1.4), p. 520.
The actual global spectral kernel has a smoothed Haar diagonal whose absolute
integral is bounded by the trace norm of convolution after projection.
Deviation: This bound applies to any representing tensor and prescribed measurable
D′-sequence, at every nonnegative half-width and Sobolev order greater than one. -/
theorem integral_norm_smoothenedStripSpectralKernel_diagonal_le_traceNorm
    {a α s : ℝ} (ha : 0 < a) (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽)
    (hK : ∃ K, sobolevProjectiveKernelOperator (F := F) hα (nonnegOrder(hs)) K =
      AP(a, hα, hs, φ))
    (N : nuclearEndomorphisms W(α, s)) (hN : N.val = AP(a, hα, hs, φ))
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    let d (x : C𝔽) := dSequenceKernelSmoothening μ𝔽 U
      (globalStripSpectralKernel (F := F) a hα hs φ hK) (x, x)
    Integrable d μ𝔽 ∧ (∫ x, ‖d x‖ ∂μ𝔽) ≤ traceNorm N := by
  let w (x : C𝔽) := intervalSobolevDensity (-α) α s (logIdeleClassNorm F x)
  let ν := (μ𝔽).withDensity (fun x ↦ ENNReal.ofReal (w x))
  let K := (globalStripSpectralKernel (F := F) a hα hs φ hK : C𝔽 × C𝔽 → ℂ)
  let κ (p : C𝔽 × C𝔽) := (w p.2)⁻¹ • K p
  have hdensity : Continuous (intervalSobolevDensity (-α) α s) := by
    unfold intervalSobolevDensity
    refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun t ↦ Or.inl ?_)
    positivity
  have hw : Continuous w :=
    hdensity.comp
      ((NNReal.continuous_coe.comp (Units.continuous_val.comp (map_continuous m𝔽))).log
        fun g ↦ NNReal.coe_ne_zero.mpr (m𝔽 g).ne_zero)
  have hwpos (x) : 0 < w x := by
    dsimp only [w, intervalSobolevDensity]
    positivity
  let wNN (x : C𝔽) : ℝ≥0 := ⟨w x, (hwpos x).le⟩
  have hwNN : Continuous wNN := hw.subtype_mk _
  have hν : ν = (μ𝔽).withDensity (fun x ↦ (wNN x : ℝ≥0∞)) :=
    congrArg (μ𝔽).withDensity (funext fun x ↦ ENNReal.ofReal_eq_coe_nnreal (hwpos x).le)
  let : IsLocallyFiniteMeasure ν := sobolevKernelWeight_locallyFinite (F := F) α s
  obtain ⟨hm, hop⟩ := spectralStripKernel_hilbertSchmidt (F := F) a hα hs φ ha hK
  have hmem : MemLp κ 2 (ν.prod ν) := hm
  let k := hmem.toLp κ
  have hop' : (integralKernelOperator ν k).val = N.val := hop.trans hN.symm
  have hn : IsNuclearOperator (integralKernelOperator ν k).val := by rw [hop']; exact N.property
  have hK' (p : C𝔽 × C𝔽) : (wNN p.2 : ℂ) * κ p = K p := by
    change ((w p.2 : ℝ) : ℂ) * ((w p.2)⁻¹ • K p) = K p
    rw [Complex.real_smul, Complex.ofReal_inv,
      mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (hwpos p.2).ne')]
  have hdiag := integral_norm_dSequenceKernelSmoothening_haar_diagonal_le_traceNorm
    hmem.coeFn_toLp.symm hU hBorel hwNN hwpos hν hn
  dsimp only at hdiag ⊢
  rw [funext hK'] at hdiag
  exact ⟨hdiag.1, hdiag.2.trans_eq (congrArg traceNorm
    (Subtype.ext hop' : (⟨_, hn⟩ : nuclearEndomorphisms W(α, s)) = N))⟩

end StripSpectralKernel

end RiemannMasullo.Isolated
