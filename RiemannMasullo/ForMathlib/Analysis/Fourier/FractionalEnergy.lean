module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.FractionalJump
public import RiemannMasullo.ForMathlib.Analysis.Fourier.L2Translation
public import RiemannMasullo.ForMathlib.Analysis.FunctionalSpaces.RealJumpEnergy
import Mathlib.Analysis.Complex.Norm

/-! # Fractional Sobolev energy as a positive jump form

For every `L²` function and `0 ≤ θ < 1`, the Fourier weight `(1 + (2πξ)²)^θ` equals
the local squared norm plus half the squared differences against the positive jump measure.
The equality is proved in extended nonnegative integrals, including infinite energy.
Consequently it can be used to prove finite-energy closure under truncations without
assuming the integrability or decay that a subsequent comparison argument establishes.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform Real
open scoped FourierTransform
namespace RiemannMasullo

private theorem enorm_sq_L2_eq_lintegral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : Lp ℂ 2 μ) : ‖f‖ₑ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [Lp.eNorm_def, eLpNorm_eq_lintegral_rpow_eNorm_toReal
    two_ne_zero ENNReal.ofNat_ne_top (Lp.aestronglyMeasurable f)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

private theorem norm_phase_sub_one_sq (t : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ^ 2 = 2 * (1 - Real.cos t) := by
  rw [Complex.norm_sub_one_sq_eq_of_norm_eq_one (by simp [Complex.norm_exp]),
    Complex.exp_ofReal_mul_I_re]

/-- Translation Plancherel in nonnegative form, valid for every `L²` function. -/
theorem lintegral_enorm_sq_translation_sub_L2 (f : Lp ℂ 2 (volume : Measure ℝ)) (r : ℝ) :
    (∫⁻ x : ℝ, ‖f (x + r) - f x‖ₑ ^ 2) =
      ∫⁻ ξ : ℝ, ENNReal.ofReal (2 * (1 - Real.cos (2 * Real.pi * r * ξ))) *
        ‖(𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) ξ‖ₑ ^ 2 := by
  calc
    _ = ‖realL2Translation r f - f‖ₑ ^ 2 := by
      rw [enorm_sq_L2_eq_lintegral]
      apply lintegral_congr_ae
      filter_upwards [Lp.coeFn_sub (realL2Translation r f) f, coeFn_realL2Translation r f] with x hx ht
      simp only [hx, Pi.sub_apply, ht]
    _ = ‖𝓕 (realL2Translation r f - f)‖ₑ ^ 2 := by
      simp only [← ofReal_norm, Lp.norm_fourier_eq]
    _ = ‖realL2Modulation r (𝓕 f) - 𝓕 f‖ₑ ^ 2 := by
      rw [fourier_sub, fourier_realL2Translation]
    _ = _ := by
      rw [enorm_sq_L2_eq_lintegral]
      apply lintegral_congr_ae
      filter_upwards [Lp.coeFn_sub (realL2Modulation r (𝓕 f)) (𝓕 f),
        coeFn_realL2Modulation r (𝓕 f)] with ξ hsub hmod
      simp only [hsub, Pi.sub_apply, hmod]
      have he (z : ℂ) : ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      rw [he, he, ← sub_one_mul, norm_mul, mul_pow, norm_phase_sub_one_sq,
        ENNReal.ofReal_mul (mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.cos_le_one _)))]

/-- The singular jump form has exactly the fractional Bessel Fourier multiplier on `L²`.
The equality is an identity of extended nonnegative integrals, including infinite energy. -/
theorem lintegral_fractionalJump_energy_L2 {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫⁻ r : ℝ, ∫⁻ x : ℝ, ‖f (x + r) - f x‖ₑ ^ 2 ∂volume ∂fractionalJumpMeasure θ) =
      ∫⁻ ξ : ℝ, ENNReal.ofReal (2 * ((1 + (2 * Real.pi * ξ) ^ 2) ^ θ - 1)) *
        ‖(𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) ξ‖ₑ ^ 2 := by
  have hm : Measurable ((𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := (Lp.stronglyMeasurable (𝓕 f)).measurable
  simp_rw [lintegral_enorm_sq_translation_sub_L2 f]
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro ξ
  rw [lintegral_mul_const _ (by fun_prop)]
  congr 1
  have he (r : ℝ) : 2 * Real.pi * r * ξ = (2 * Real.pi * ξ) * r := by ring
  simp_rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((integrable_one_sub_cos_fractionalJumpMeasure hθ₀ hθ₁ (2 * Real.pi * ξ)).const_mul 2)
    (.of_forall fun r ↦ mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.cos_le_one _))),
    integral_const_mul, integral_one_sub_cos_fractionalJumpMeasure hθ₀ hθ₁]

/-- The fractional Bessel-potential norm is exactly the local `L²` energy plus half the
positive jump energy. The formula holds for every `L²` class, before assuming finite
fractional energy or choosing a continuous representative. -/
theorem lintegral_fractionalSobolev_energy_L2 {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) + ENNReal.ofReal (1 / 2 : ℝ) *
      (∫⁻ r : ℝ, ∫⁻ x : ℝ, ‖f (x + r) - f x‖ₑ ^ 2 ∂volume ∂fractionalJumpMeasure θ) =
      ∫⁻ ξ : ℝ, ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ θ) *
        ‖(𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) ξ‖ₑ ^ 2 := by
  have hm : Measurable ((𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := (Lp.stronglyMeasurable (𝓕 f)).measurable
  have hF : (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) =
      ∫⁻ ξ : ℝ, ‖(𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) ξ‖ₑ ^ 2 := by
    rw [← enorm_sq_L2_eq_lintegral, ← enorm_sq_L2_eq_lintegral]
    simp only [← ofReal_norm, Lp.norm_fourier_eq]
  rw [lintegral_fractionalJump_energy_L2 hθ₀ hθ₁ f, hF,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_add_left (by fun_prop)]
  apply lintegral_congr
  intro ξ
  have hw : 0 ≤ (1 + (2 * Real.pi * ξ) ^ 2) ^ θ - 1 :=
    sub_nonneg.mpr (Real.one_le_rpow (by nlinarith [sq_nonneg (2 * Real.pi * ξ)]) hθ₀)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    show (1 / 2 : ℝ) * (2 * ((1 + (2 * Real.pi * ξ) ^ 2) ^ θ - 1)) =
      (1 + (2 * Real.pi * ξ) ^ 2) ^ θ - 1 by ring,
    ← one_add_mul, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) hw]
  congr 2
  ring

/-- Normal contractions preserve and decrease fractional Sobolev energy. In particular,
positive-part truncation is legitimate before a comparison proof supplies decay. -/
theorem lintegral_fractionalSobolev_energy_compLp_le {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) {Φ : ℂ → ℂ} (hΦ : LipschitzWith 1 Φ)
    (hΦ₀ : Φ 0 = 0) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ θ) *
      ‖(𝓕 (hΦ.compLp hΦ₀ f) : Lp ℂ 2 (volume : Measure ℝ)) ξ‖ₑ ^ 2) ≤
      ∫⁻ ξ : ℝ, ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ θ) *
        ‖(𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) ξ‖ₑ ^ 2 := by
  have hnorm (z : ℂ) : ‖Φ z‖ₑ ≤ ‖z‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    simpa only [hΦ₀, sub_zero, NNReal.coe_one, one_mul] using hΦ.norm_sub_le z 0
  have hdiff (z w : ℂ) : ‖Φ z - Φ w‖ₑ ≤ ‖z - w‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    simpa only [NNReal.coe_one, one_mul] using hΦ.norm_sub_le z w
  have he := hΦ.coeFn_compLp hΦ₀ f
  have hl : (∫⁻ x : ℝ, ‖(hΦ.compLp hΦ₀ f) x‖ₑ ^ 2) ≤ ∫⁻ x : ℝ, ‖f x‖ₑ ^ 2 := by
    apply lintegral_mono_ae
    filter_upwards [he] with x hx
    simpa only [hx, Function.comp_apply] using pow_le_pow_left' (hnorm (f x)) 2
  have hj : (∫⁻ r : ℝ, ∫⁻ x : ℝ,
      ‖(hΦ.compLp hΦ₀ f) (x + r) - (hΦ.compLp hΦ₀ f) x‖ₑ ^ 2
        ∂volume ∂fractionalJumpMeasure θ) ≤
      ∫⁻ r : ℝ, ∫⁻ x : ℝ, ‖f (x + r) - f x‖ₑ ^ 2 ∂volume ∂fractionalJumpMeasure θ := by
    apply lintegral_mono
    intro r
    apply lintegral_mono_ae
    have hs := (measurePreserving_add_right (volume : Measure ℝ) r).quasiMeasurePreserving.ae he
    filter_upwards [he, hs] with x hx hsx
    simpa only [hx, hsx, Function.comp_apply] using pow_le_pow_left' (hdiff (f (x + r)) (f x)) 2
  rw [← lintegral_fractionalSobolev_energy_L2 hθ₀ hθ₁ (hΦ.compLp hΦ₀ f),
    ← lintegral_fractionalSobolev_energy_L2 hθ₀ hθ₁ f]
  exact add_le_add hl (mul_le_mul' le_rfl hj)

/-- Finite Fourier-defined fractional energy is equivalent to square-integrability of
the point differences against the actual jump-pair measure. -/
theorem fractionalSobolev_energy_lt_top_iff_memLp_jump {θ : ℝ}
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫⁻ ξ : ℝ, ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ θ) *
      ‖(𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) ξ‖ₑ ^ 2) < ⊤ ↔
      MemLp (fun p : ℝ × ℝ ↦ f p.1 - f p.2) 2
        (realJumpPairMeasure (fractionalJumpMeasure θ)) := by
  have hm : Measurable (f : ℝ → ℂ) := (Lp.stronglyMeasurable f).measurable
  have hd : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ f p.1 - f p.2)
      (realJumpPairMeasure (fractionalJumpMeasure θ)) := by fun_prop
  rw [memLp_iff,
    eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hd]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [lintegral_realJumpPairMeasure _ _ (by fun_prop),
    ← lintegral_fractionalSobolev_energy_L2 hθ₀ hθ₁ f, ENNReal.add_lt_top]
  have hl : (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) < ⊤ := by
    rw [← enorm_sq_L2_eq_lintegral]
    finiteness
  rw [and_iff_right hl]
  constructor
  · intro h
    exact ENNReal.lt_top_of_mul_ne_top_right h.ne (by norm_num)
  · intro h
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

end RiemannMasullo
