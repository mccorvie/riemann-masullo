module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.L2Synthesis
public import RiemannMasullo.ForMathlib.Analysis.Fourier.FractionalEmbedding
public import Mathlib.Analysis.InnerProductSpace.Dual

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform InnerProductSpace
namespace RiemannMasullo

/-- Multiplication by the reciprocal fractional half-weight preserves ordinary `L²`. -/
theorem memLp_fractionalFourierDensity {θ : ℝ} (hθ : 0 ≤ θ)
    (v : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (fun ξ : ℝ ↦ ((1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ / 2) : ℝ) • v ξ) 2 := by
  have hw : MemLp (fun ξ : ℝ ↦ (1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ / 2)) ⊤ := by
    apply memLp_top_of_bound (by apply Measurable.aestronglyMeasurable; fun_prop) 1
    exact .of_forall fun ξ ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg (2 * Real.pi * ξ)])
        (by linarith)
  exact hw.smul (Lp.memLp v)

/-- Above the evaluation threshold every reciprocal-half-weight density is integrable. -/
theorem integrable_fractionalFourierDensity {θ : ℝ} (hθ : 1 / 2 < θ)
    (v : Lp ℂ 2 (volume : Measure ℝ)) :
    Integrable (fun ξ : ℝ ↦ ((1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ / 2) : ℝ) • v ξ) := by
  have hi := (memLp_two_reciprocal_fractionalHalfWeight hθ).ofReal.integrable_mul (Lp.memLp v)
  apply hi.congr
  exact .of_forall fun ξ ↦ by
    change (((1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ / 2) : ℝ) : ℂ) * v ξ =
      ((1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ / 2) : ℝ) • v ξ
    exact Complex.real_smul.symm

/-- The normalized Fourier synthesis model of the fractional Sobolev space. -/
def fractionalSynthesis (θ : ℝ) (v : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ :=
  𝓕⁻ (fun ξ : ℝ ↦ ((1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ / 2) : ℝ) • v ξ)

/-- Every synthesized profile is continuous above the point-evaluation threshold. -/
theorem continuous_fractionalSynthesis {θ : ℝ} (hθ : 1 / 2 < θ)
    (v : Lp ℂ 2 (volume : Measure ℝ)) : Continuous (fractionalSynthesis θ v) := by
  change Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (-(innerₗ ℝ))
    (fun ξ : ℝ ↦ ((1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ / 2) : ℝ) • v ξ))
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner.neg
    (integrable_fractionalFourierDensity hθ v)

/-- Synthesized profiles also belong to ordinary `L²`. -/
theorem memLp_fractionalSynthesis {θ : ℝ} (hθ : 1 / 2 < θ)
    (v : Lp ℂ 2 (volume : Measure ℝ)) : MemLp (fractionalSynthesis θ v) 2 :=
  memLp_fourierInv_of_integrable (memLp_fractionalFourierDensity (by linarith) v)
    (integrable_fractionalFourierDensity hθ v)

/-- The weighted Fourier transform of a synthesized profile recovers its model vector. -/
theorem fractionalSynthesis_weighted_fourier {θ : ℝ} (hθ : 1 / 2 < θ)
    (v : Lp ℂ 2 (volume : Measure ℝ)) :
    (fun ξ : ℝ ↦ ((1 + (2 * Real.pi * ξ) ^ 2) ^ (θ / 2) : ℝ) •
      (𝓕 ((memLp_fractionalSynthesis hθ v).toLp (fractionalSynthesis θ v)) :
        Lp ℂ 2 (volume : Measure ℝ)) ξ) =ᵐ[volume] v := by
  have he := fourier_toLp_fourierInv (memLp_fractionalFourierDensity (show 0 ≤ θ by linarith) v)
    (integrable_fractionalFourierDensity hθ v)
  change 𝓕 ((memLp_fractionalSynthesis hθ v).toLp (fractionalSynthesis θ v)) = _ at he
  rw [he]
  filter_upwards [(memLp_fractionalFourierDensity (show 0 ≤ θ by linarith) v).coeFn_toLp] with ξ hξ
  rw [hξ, smul_smul, ← Real.rpow_add (by positivity),
    show θ / 2 + -θ / 2 = 0 by ring, Real.rpow_zero, one_smul]

/-- The synthesized profile has finite fractional Fourier energy. -/
theorem memLp_fractionalWeight_fractionalSynthesis {θ : ℝ} (hθ : 1 / 2 < θ)
    (v : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (fun ξ : ℝ ↦ ((1 + (2 * Real.pi * ξ) ^ 2) ^ (θ / 2) : ℝ) •
      (𝓕 ((memLp_fractionalSynthesis hθ v).toLp (fractionalSynthesis θ v)) :
        Lp ℂ 2 (volume : Measure ℝ)) ξ) 2 :=
  (Lp.memLp v).ae_eq (fractionalSynthesis_weighted_fourier hθ v).symm


/-- Every continuous finite-energy profile has a preimage in the Fourier model. -/
theorem exists_fractionalSynthesis_eq {θ : ℝ} (hθ : 1 / 2 < θ)
    {f : ℝ → ℂ} (hf : Continuous f) (hf₂ : MemLp f 2)
    (hweight : MemLp (fun ξ : ℝ ↦ ((1 + (2 * Real.pi * ξ) ^ 2) ^ (θ / 2) : ℝ) •
      (𝓕 (hf₂.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) ξ) 2) :
    ∃ v : Lp ℂ 2 (volume : Measure ℝ), fractionalSynthesis θ v = f := by
  let F : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 (hf₂.toLp f)
  let v := hweight.toLp (fun ξ : ℝ ↦ ((1 + (2 * Real.pi * ξ) ^ 2) ^ (θ / 2) : ℝ) • F ξ)
  have he : (fun ξ : ℝ ↦ ((1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ / 2) : ℝ) • v ξ) =ᵐ[volume] F := by
    filter_upwards [hweight.coeFn_toLp] with ξ hξ
    change v ξ = _ at hξ
    rw [hξ, smul_smul, ← Real.rpow_add (by positivity),
      show -θ / 2 + θ / 2 = 0 by ring, Real.rpow_zero, one_smul]
  refine ⟨v, ?_⟩
  have hfInv := fractionalSobolev_eq_fourierInv hθ hf hf₂ hweight
  rw [hfInv]
  funext x
  rw [fractionalSynthesis, Real.fourierInv_eq', Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards [he] with ξ hξ
  rw [hξ]

/-- The unbundled evaluation vector in the ordinary Fourier `L²` model. -/
def fractionalProbeRaw (θ t ξ : ℝ) : ℂ :=
  star (Real.fourierChar (ξ * t) : ℂ) *
    (((1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ / 2) : ℝ) : ℂ)

/-- Evaluation vectors belong to the model Hilbert space above the Sobolev threshold. -/
theorem memLp_fractionalProbeRaw {θ : ℝ} (hθ : 1 / 2 < θ) (t : ℝ) :
    MemLp (fractionalProbeRaw θ t) 2 := by
  have hchar : Measurable (fun ξ : ℝ ↦ (Real.fourierChar (ξ * t) : ℂ)) :=
    (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      (continuous_id.mul continuous_const))).measurable
  have hm : AEStronglyMeasurable (fractionalProbeRaw θ t) volume := by
    exact hchar.aestronglyMeasurable.star.mul (by
      apply Measurable.aestronglyMeasurable; fun_prop)
  apply (memLp_two_reciprocal_fractionalHalfWeight hθ).mono' hm
  exact .of_forall fun ξ ↦ by
    change ‖fractionalProbeRaw θ t ξ‖ ≤ (1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ / 2)
    simp only [fractionalProbeRaw, norm_mul, norm_star, Circle.norm_coe, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]

/-- The Riesz vector for point evaluation in the fractional Fourier model. -/
def fractionalProbe (θ : ℝ) (hθ : 1 / 2 < θ) (t : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_fractionalProbeRaw hθ t).toLp (fractionalProbeRaw θ t)

/-- Inner product with the model evaluation vector is exactly the synthesized profile. -/
theorem fractionalProbe_inner {θ : ℝ} (hθ : 1 / 2 < θ) (t : ℝ)
    (v : Lp ℂ 2 (volume : Measure ℝ)) :
    ⟪fractionalProbe θ hθ t, v⟫_ℂ = fractionalSynthesis θ v t := by
  rw [L2.inner_def, fractionalSynthesis, Real.fourierInv_eq]
  apply integral_congr_ae
  filter_upwards [(memLp_fractionalProbeRaw hθ t).coeFn_toLp] with ξ hξ
  change fractionalProbe θ hθ t ξ = fractionalProbeRaw θ t ξ at hξ
  rw [hξ]
  change v ξ * star (fractionalProbeRaw θ t ξ) =
    (Real.fourierChar (inner ℝ ξ t) : ℂ) *
      (((1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ / 2) : ℝ) • v ξ)
  rw [fractionalProbeRaw, star_mul, star_star, Complex.star_def, Complex.conj_ofReal,
    Complex.real_smul]
  have hr : inner ℝ ξ t = ξ * t := by simp [RCLike.inner_apply, mul_comm]
  rw [hr]
  ring

/-- Evaluation at every real point separates the ordinary `L²` model vectors. -/
theorem fractionalProbe_separates {θ : ℝ} (hθ : 1 / 2 < θ)
    (v : Lp ℂ 2 (volume : Measure ℝ))
    (hv : ∀ t, ⟪fractionalProbe θ hθ t, v⟫_ℂ = 0) : v = 0 := by
  have hfun : fractionalSynthesis θ v = 0 := by
    funext t
    exact (fractionalProbe_inner hθ t v).symm.trans (hv t)
  have hLp : (memLp_fractionalSynthesis hθ v).toLp (fractionalSynthesis θ v) = 0 := by
    apply Lp.ext
    filter_upwards [(memLp_fractionalSynthesis hθ v).coeFn_toLp,
      Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))] with x hx h0
    rw [hx, h0, hfun]
  have he := fractionalSynthesis_weighted_fourier hθ v
  rw [hLp, FourierTransform.fourier_zero] at he
  apply Lp.ext
  filter_upwards [he, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))] with ξ hξ h0
  simpa only [h0, Pi.zero_apply, smul_zero] using hξ.symm


/-- The evaluation Gram kernel is the inverse Fourier integral of the reciprocal weight. -/
theorem fractionalProbe_gram {θ : ℝ} (hθ : 1 / 2 < θ) (s t : ℝ) :
    ⟪fractionalProbe θ hθ s, fractionalProbe θ hθ t⟫_ℂ =
      ∫ ξ : ℝ, (Real.fourierChar (ξ * (s - t)) : ℂ) *
        (((1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ) : ℝ) : ℂ) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_fractionalProbeRaw hθ s).coeFn_toLp,
    (memLp_fractionalProbeRaw hθ t).coeFn_toLp] with ξ hs ht
  change fractionalProbe θ hθ s ξ = _ at hs
  change fractionalProbe θ hθ t ξ = _ at ht
  rw [hs, ht]
  change fractionalProbeRaw θ t ξ * star (fractionalProbeRaw θ s ξ) = _
  have hc : (Real.fourierChar (ξ * s) : ℂ) * star (Real.fourierChar (ξ * t) : ℂ) =
      (Real.fourierChar (ξ * (s - t)) : ℂ) := by
    rw [Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul,
      ← div_eq_mul_inv, ← AddChar.map_sub_eq_div, mul_sub]
  have hw : (((1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ / 2) : ℝ) : ℂ) *
      (((1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ / 2) : ℝ) : ℂ) =
        (((1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity)]
    congr 2
    ring
  rw [fractionalProbeRaw, fractionalProbeRaw, star_mul, star_star,
    Complex.star_def, Complex.conj_ofReal]
  calc
    _ = ((Real.fourierChar (ξ * s) : ℂ) * star (Real.fourierChar (ξ * t) : ℂ)) *
        ((((1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ / 2) : ℝ) : ℂ) *
          (((1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ / 2) : ℝ) : ℂ)) := by
      simp only [Complex.star_def]
      ring
    _ = _ := by rw [hc, hw]

/-- In the angular-frequency convention the model Gram integral has the factor `1/(2π)`. -/
theorem fractionalProbe_gram_angular {θ : ℝ} (hθ : 1 / 2 < θ) (s t : ℝ) :
    ⟪fractionalProbe θ hθ s, fractionalProbe θ hθ t⟫_ℂ =
      ((2 * Real.pi)⁻¹ : ℝ) •
        ∫ x : ℝ, Complex.exp (↑((s - t) * x) * Complex.I) *
          (((1 + x ^ 2) ^ (-θ) : ℝ) : ℂ) := by
  rw [fractionalProbe_gram hθ]
  let f (x : ℝ) := Complex.exp (↑((s - t) * x) * Complex.I) *
    (((1 + x ^ 2) ^ (-θ) : ℝ) : ℂ)
  have he : (∫ ξ : ℝ, (Real.fourierChar (ξ * (s - t)) : ℂ) *
      (((1 + (2 * Real.pi * ξ) ^ 2) ^ (-θ) : ℝ) : ℂ)) =
      ∫ ξ : ℝ, f (2 * Real.pi * ξ) := by
    apply integral_congr_ae
    exact .of_forall fun ξ ↦ by
      dsimp only [f]
      rw [Real.fourierChar_apply]
      congr 2
      push_cast
      ring
  rw [he, Measure.integral_comp_mul_left, abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹)]


/-- Point evaluations at different centers have the same norm in the Fourier model. -/
theorem fractionalProbe_norm_eq {θ : ℝ} (hθ : 1 / 2 < θ) (t : ℝ) :
    ‖fractionalProbe θ hθ t‖ = ‖fractionalProbe θ hθ 0‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have he : ⟪fractionalProbe θ hθ t, fractionalProbe θ hθ t⟫_ℂ =
      ⟪fractionalProbe θ hθ 0, fractionalProbe θ hθ 0⟫_ℂ := by
    rw [fractionalProbe_gram hθ, fractionalProbe_gram hθ, sub_self, sub_self]
  exact ((inner_self_eq_norm_sq (𝕜 := ℂ) _).symm.trans (congrArg Complex.re he)).trans
    (inner_self_eq_norm_sq (𝕜 := ℂ) _)

end RiemannMasullo
