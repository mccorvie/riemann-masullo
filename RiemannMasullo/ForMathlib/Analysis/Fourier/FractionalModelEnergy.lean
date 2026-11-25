module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.FractionalModel
public import RiemannMasullo.ForMathlib.Analysis.Fourier.FractionalPairing

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform InnerProductSpace
namespace RiemannMasullo

/-- Fractional model profiles have finite jump energy below exponent one. -/
theorem memLp_jump_fractionalSynthesis {θ : ℝ} (hθ : 1 / 2 < θ) (hθ₁ : θ < 1)
    (v : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (fun p : ℝ × ℝ ↦ fractionalSynthesis θ v p.1 - fractionalSynthesis θ v p.2) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ)) :=
  (memLp_fractionalWeight_iff_memLp_jump (by linarith) hθ₁
    (continuous_fractionalSynthesis hθ v).measurable (memLp_fractionalSynthesis hθ v)).mp
      (memLp_fractionalWeight_fractionalSynthesis hθ v)

/-- Every continuous profile of finite jump energy is represented in the Fourier model. -/
theorem exists_fractionalSynthesis_eq_of_memLp_jump {θ : ℝ}
    (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) {f : ℝ → ℂ} (hf : Continuous f) (hf₂ : MemLp f 2)
    (hJ : MemLp (fun p : ℝ × ℝ ↦ f p.1 - f p.2) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ))) :
    ∃ v : Lp ℂ 2 (volume : Measure ℝ), fractionalSynthesis θ v = f :=
  exists_fractionalSynthesis_eq hθ hf hf₂
    ((memLp_fractionalWeight_iff_memLp_jump (by linarith) hθ₁ hf.measurable hf₂).mpr hJ)

/-- The real part of the nonlocal pairing is the Hilbert inner product in the model. -/
theorem fractionalSynthesis_pairing_re {θ : ℝ} (hθ : 1 / 2 < θ) (hθ₁ : θ < 1)
    (v w : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫ x : ℝ, (star (fractionalSynthesis θ v x) * fractionalSynthesis θ w x).re) +
      (1 / 2 : ℝ) * (∫ p : ℝ × ℝ,
        (star (fractionalSynthesis θ v p.1 - fractionalSynthesis θ v p.2) *
          (fractionalSynthesis θ w p.1 - fractionalSynthesis θ w p.2)).re
          ∂realJumpPairMeasure (fractionalJumpMeasure θ)) = (⟪v, w⟫_ℂ).re := by
  rw [nonlocalPairing_re_eq_fractionalFourierPairing_re (by linarith) hθ₁
    (continuous_fractionalSynthesis hθ v).measurable
    (continuous_fractionalSynthesis hθ w).measurable
    (memLp_fractionalSynthesis hθ v) (memLp_fractionalSynthesis hθ w)
    (memLp_jump_fractionalSynthesis hθ hθ₁ v) (memLp_jump_fractionalSynthesis hθ hθ₁ w)]
  rw [L2.inner_def]
  have hre := Complex.reCLM.integral_comp_comm (L2.integrable_inner v w)
  simp only [Complex.reCLM_apply] at hre
  rw [← hre]
  apply integral_congr_ae
  filter_upwards [fractionalSynthesis_weighted_fourier hθ v,
    fractionalSynthesis_weighted_fourier hθ w] with ξ hv hw
  rw [← hv, ← hw]
  simp only [RCLike.inner_apply, Complex.real_smul,
    Complex.star_def, map_mul, Complex.conj_ofReal]
  rw [show ((1 + (2 * Real.pi * ξ) ^ 2) ^ θ) =
    ((1 + (2 * Real.pi * ξ) ^ 2) ^ (θ / 2)) *
      ((1 + (2 * Real.pi * ξ) ^ 2) ^ (θ / 2)) by
        rw [← Real.rpow_add (by positivity)]; congr 1; ring]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The exact energy norm identifies the model with the fractional Sobolev space. -/
theorem fractionalSynthesis_energy {θ : ℝ} (hθ : 1 / 2 < θ) (hθ₁ : θ < 1)
    (v : Lp ℂ 2 (volume : Measure ℝ)) :
    nonlocalEnergy volume (realJumpPairMeasure (fractionalJumpMeasure θ))
      (fractionalSynthesis θ v) = ‖v‖ ^ 2 := by
  have he := fractionalSynthesis_pairing_re hθ hθ₁ v v
  rw [show (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) v] at he
  have hsq (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.sq_norm, Complex.normSq_apply]
    ring
  simpa only [nonlocalEnergy, hsq] using he

end RiemannMasullo
