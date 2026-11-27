module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import RiemannMasullo.ForMathlib.Analysis.Fourier.TemperedJumpMeasure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Comparison and cancellation for a jump energy

These are the two form arguments in the zero-width, fractional-order estimate
for the geometric blocks of Theorem 10.4.3.5(2), pp. 471–473. The pair measure
is arbitrary, so the proofs do not depend on a construction of the Bessel kernel.
-/

public noncomputable section

open MeasureTheory
open scoped ComplexConjugate ENNReal FourierTransform SchwartzMap

namespace RiemannMasullo

variable {X : Type*} [MeasurableSpace X]

/-- The real part of a mass and jump pairing. The measure on pairs includes the jump kernel. -/
def jumpPairing (μ : Measure X) (ν : Measure (X × X)) (f g : X → ℂ) : ℝ :=
  (∫ x, (conj (f x) * g x).re ∂μ) +
    (1 / 2) * ∫ p, (conj (f p.1 - f p.2) * (g p.1 - g p.2)).re ∂ν

private theorem jumpPairing_ofReal (μ : Measure X) (ν : Measure (X × X))
    (f g : X → ℝ) :
    jumpPairing μ ν (fun x ↦ (f x : ℂ)) (fun x ↦ (g x : ℂ)) =
      (∫ x, f x * g x ∂μ) + (1 / 2) * ∫ p, (f p.1 - f p.2) * (g p.1 - g p.2) ∂ν := by
  simp [jumpPairing, Complex.mul_re, Complex.sub_re, Complex.sub_im]

private theorem jumpPairing_posPart_sq_le (a b : ℝ) :
    (max a 0 - max b 0) ^ 2 ≤ (a - b) * (max a 0 - max b 0) := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · simp [max_eq_right ha, max_eq_right hb]
  · simp only [max_eq_right ha, max_eq_left hb]
    nlinarith only [mul_nonneg (neg_nonneg.mpr ha) hb]
  · simp only [max_eq_left ha, max_eq_right hb]
    nlinarith only [mul_nonneg ha (neg_nonneg.mpr hb)]
  · simp [max_eq_left ha, max_eq_left hb, pow_two]

/-- A real function with zero pairing against its positive part is nonpositive almost
everywhere for the mass measure. Apply this to the difference of two interpolants. -/
theorem ae_nonpos_of_jumpPairing_posPart_eq_zero (μ : Measure X) (ν : Measure (X × X))
    (u : X → ℝ)
    (hMass : Integrable (fun x ↦ u x * max (u x) 0) μ)
    (horth : jumpPairing μ ν (fun x ↦ (u x : ℂ)) (fun x ↦ ((max (u x) 0 : ℝ) : ℂ)) = 0) :
    ∀ᵐ x ∂μ, u x ≤ 0 := by
  let v (x : X) := max (u x) 0
  have hm (x : X) : u x * v x = v x ^ 2 := by
    rcases le_total (u x) 0 with hx | hx
    · simp [v, max_eq_right hx]
    · simp [v, max_eq_left hx, pow_two]
  have hv : Integrable (fun x ↦ v x ^ 2) μ := hMass.congr (ae_of_all _ hm)
  have hj : 0 ≤ ∫ p, (u p.1 - u p.2) * (v p.1 - v p.2) ∂ν :=
    integral_nonneg fun p ↦ (sq_nonneg _).trans (jumpPairing_posPart_sq_le (u p.1) (u p.2))
  rw [jumpPairing_ofReal, integral_congr_ae (ae_of_all _ hm)] at horth
  have hzero : (∫ x, v x ^ 2 ∂μ) = 0 := by
    have hnonneg : 0 ≤ ∫ x, v x ^ 2 ∂μ := integral_nonneg fun _ ↦ sq_nonneg _
    linarith only [hnonneg, hj, horth]
  filter_upwards [(integral_eq_zero_iff_of_nonneg (fun _ ↦ sq_nonneg _) hv).mp hzero] with x hx
  have hx' : v x ^ 2 = 0 := hx
  have hvx : v x = 0 := by simpa using hx'
  exact hvx ▸ le_max_left (u x) 0

private theorem jumpPairing_mul_identity (a c : ℝ) (b d : ℂ) :
    (conj (b * a - d * c) * (b * a - d * c)).re -
      (conj ((a : ℂ) - c) * ((Complex.normSq b * a : ℝ) - (Complex.normSq d * c : ℝ))).re =
      a * c * Complex.normSq (b - d) := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  ring

/-- If a real interpolant is orthogonal to its product with the squared modulus of a
multiplier, the energy of the multiplied interpolant depends only on multiplier differences. -/
theorem jumpPairing_mul_self_eq_of_orthogonal (μ : Measure X) (ν : Measure (X × X))
    (h : X → ℝ) (b : X → ℂ)
    (hEnergy : Integrable (fun p ↦ (conj (b p.1 * h p.1 - b p.2 * h p.2) *
      (b p.1 * h p.1 - b p.2 * h p.2)).re) ν)
    (hCross : Integrable (fun p ↦ (conj ((h p.1 : ℂ) - h p.2) *
      (((Complex.normSq (b p.1) * h p.1 : ℝ) : ℂ) -
        ((Complex.normSq (b p.2) * h p.2 : ℝ) : ℂ))).re) ν)
    (horth : jumpPairing μ ν (fun x ↦ (h x : ℂ))
      (fun x ↦ (Complex.normSq (b x) * h x : ℝ)) = 0) :
    jumpPairing μ ν (fun x ↦ b x * h x) (fun x ↦ b x * h x) =
      (1 / 2) * ∫ p, h p.1 * h p.2 * Complex.normSq (b p.1 - b p.2) ∂ν := by
  have hm (x : X) :
      (conj (b x * h x) * (b x * h x)).re =
        (conj (h x : ℂ) * (Complex.normSq (b x) * h x : ℝ)).re := by
    simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  unfold jumpPairing at horth ⊢
  rw [integral_congr_ae (ae_of_all _ hm)]
  have hj :
      (∫ p, (conj (b p.1 * h p.1 - b p.2 * h p.2) * (b p.1 * h p.1 - b p.2 * h p.2)).re ∂ν) -
        (∫ p, (conj ((h p.1 : ℂ) - h p.2) *
          (((Complex.normSq (b p.1) * h p.1 : ℝ) : ℂ) -
            ((Complex.normSq (b p.2) * h p.2 : ℝ) : ℂ))).re ∂ν) =
        ∫ p, h p.1 * h p.2 * Complex.normSq (b p.1 - b p.2) ∂ν := by
    rw [← integral_sub hEnergy hCross]
    exact integral_congr_ae (ae_of_all _ fun p ↦ jumpPairing_mul_identity (h p.1) (h p.2) (b p.1) (b p.2))
  dsimp only at horth ⊢
  linarith only [horth, hj]

/-- The displacement measure on ordered pairs of spatial arguments. -/
def temperedJumpPairMeasure (s : ℝ) : Measure (ℝ × ℝ) :=
  ((temperedJumpMeasure s).prod volume).map (fun hx : ℝ × ℝ ↦ (hx.2 + hx.1, hx.2))

private theorem lintegral_norm_sq_temperedJumpPair (s : ℝ)
    (f : ℝ → ℂ) (hf : Measurable f) :
    (∫⁻ z, ENNReal.ofReal (‖f z.1 - f z.2‖ ^ 2) ∂temperedJumpPairMeasure s) =
      ∫⁻ h, (∫⁻ x, ENNReal.ofReal (‖f (x + h) - f x‖ ^ 2)) ∂temperedJumpMeasure s := by
  have hm : Measurable (fun z : ℝ × ℝ ↦ ENNReal.ofReal (‖f z.1 - f z.2‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (((hf.comp measurable_fst).sub
      (hf.comp measurable_snd)).norm.pow_const 2)
  have hmap : Measurable (fun hx : ℝ × ℝ ↦ (hx.2 + hx.1, hx.2)) := by fun_prop
  unfold temperedJumpPairMeasure
  rw [lintegral_map hm hmap]
  exact lintegral_prod _ (hm.comp hmap).aemeasurable

private theorem integrable_schwartz_fractional_weight (g : 𝓢(ℝ, ℂ))
    {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) :
    Integrable (fun ξ : ℝ ↦ (1 + (2 * Real.pi * ξ) ^ 2) ^ s * ‖g ξ‖ ^ 2) := by
  let C := SchwartzMap.seminorm ℝ 0 0 g
  have hC (ξ : ℝ) : ‖g ξ‖ ≤ C := by
    simpa [C] using SchwartzMap.le_seminorm ℝ 0 0 g ξ
  have h2 : Integrable (fun ξ : ℝ ↦ ξ ^ 2 * ‖g ξ‖) := by
    simpa [Real.norm_eq_abs, sq_abs] using g.integrable_pow_mul volume 2
  have hdom : Integrable (fun ξ : ℝ ↦ (1 + (2 * Real.pi * ξ) ^ 2) * ‖g ξ‖ * C) := by
    refine ((g.integrable.norm.add (h2.const_mul ((2 * Real.pi) ^ 2))).mul_const C).congr ?_
    exact ae_of_all _ fun ξ ↦ by simp only [Pi.add_apply]; ring
  have hc : Continuous (fun ξ : ℝ ↦ (1 + (2 * Real.pi * ξ) ^ 2) ^ s * ‖g ξ‖ ^ 2) := by
    fun_prop
  refine hdom.mono' hc.aestronglyMeasurable (ae_of_all _ fun ξ ↦ ?_)
  have hw : 1 ≤ 1 + (2 * Real.pi * ξ) ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (1 + (2 * Real.pi * ξ) ^ 2) * ‖g ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le hw hs') (sq_nonneg _)
    _ = ((1 + (2 * Real.pi * ξ) ^ 2) * ‖g ξ‖) * ‖g ξ‖ := by
      rw [pow_two ‖g ξ‖, ← mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hC ξ) (by positivity)

private theorem re_conj_mul_self_eq_norm_sq (z : ℂ) : (conj z * z).re = ‖z‖ ^ 2 := by
  simp [Complex.mul_re, Complex.normSq_apply, Complex.sq_norm]

private theorem jumpPairing_tempered_self_eq_of_lintegral
    (f g : ℝ → ℂ) (s : ℝ) (hf : Measurable f)
    (hf2 : Integrable (fun x ↦ ‖f x‖ ^ 2))
    (hg : Integrable (fun ξ ↦ (1 + (2 * Real.pi * ξ) ^ 2) ^ s * ‖g ξ‖ ^ 2))
    (he : (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) + (2 : ℝ≥0∞)⁻¹ *
        (∫⁻ h, (∫⁻ x, ENNReal.ofReal (‖f (x + h) - f x‖ ^ 2)) ∂temperedJumpMeasure s) =
      ∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ s) *
        ENNReal.ofReal (‖g ξ‖ ^ 2)) :
    jumpPairing volume (temperedJumpPairMeasure s) f f =
      ∫ ξ, (1 + (2 * Real.pi * ξ) ^ 2) ^ s * ‖g ξ‖ ^ 2 := by
  let w (ξ : ℝ) := (1 + (2 * Real.pi * ξ) ^ 2) ^ s * ‖g ξ‖ ^ 2
  let j (z : ℝ × ℝ) := ‖f z.1 - f z.2‖ ^ 2
  have hg0 : ∀ ξ, 0 ≤ w ξ := fun _ ↦ by dsimp [w]; positivity
  have hj0 : ∀ z, 0 ≤ j z := fun _ ↦ sq_nonneg _
  have heF (ξ : ℝ) : ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ s) *
      ENNReal.ofReal (‖g ξ‖ ^ 2) = ENNReal.ofReal (w ξ) :=
    (ENNReal.ofReal_mul (by positivity : 0 ≤ (1 + (2 * Real.pi * ξ) ^ 2) ^ s)).symm
  simp_rw [heF] at he
  rw [← lintegral_norm_sq_temperedJumpPair s f hf,
    ← ofReal_integral_eq_lintegral_ofReal hg (ae_of_all _ hg0)] at he
  have hjfinite : (∫⁻ z, ENNReal.ofReal (j z) ∂temperedJumpPairMeasure s) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (by simp), add_top] at he
    exact ENNReal.ofReal_ne_top he.symm
  have hj : Integrable j (temperedJumpPairMeasure s) := by
    have hjm : Measurable j := ((hf.comp measurable_fst).sub
      (hf.comp measurable_snd)).norm.pow_const 2
    refine ⟨hjm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hj0)]
    exact lt_top_iff_ne_top.mpr hjfinite
  rw [← ofReal_integral_eq_lintegral_ofReal hf2 (ae_of_all _ fun _ ↦ sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hj (ae_of_all _ hj0)] at he
  have hhalf : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos zero_lt_two, ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div]
  rw [hhalf, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.ofReal_add (integral_nonneg fun _ ↦ sq_nonneg _) (by positivity)] at he
  unfold jumpPairing
  simp_rw [re_conj_mul_self_eq_norm_sq]
  have hm0 : 0 ≤ ∫ x, ‖f x‖ ^ 2 := integral_nonneg fun _ ↦ sq_nonneg _
  have hj0' : 0 ≤ ∫ z, j z ∂temperedJumpPairMeasure s := integral_nonneg hj0
  exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) (integral_nonneg hg0)).mp he

/-- The abstract jump pairing agrees on Schwartz functions with the squared
fractional Sobolev norm built from the Fourier weight. -/
theorem jumpPairing_tempered_self_eq_fourier (f : 𝓢(ℝ, ℂ)) {s : ℝ}
    (hs : 0 < s) (hs' : s < 1) :
    jumpPairing volume (temperedJumpPairMeasure s) f f =
      ∫ ξ, (1 + (2 * Real.pi * ξ) ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2 := by
  have hf2 : Integrable (fun x ↦ ‖f x‖ ^ 2) := by
    simpa using (f.memLp (2 : ℝ≥0∞) volume).integrable_norm_rpow (by norm_num) (by simp)
  exact jumpPairing_tempered_self_eq_of_lintegral f (𝓕 f : 𝓢(ℝ, ℂ)) s
    f.continuous.measurable hf2 (integrable_schwartz_fractional_weight (𝓕 f) hs.le hs'.le)
    (schwartz_fractional_energy_eq_tempered_jump f hs hs')

/-- On the fractional Sobolev domain in logarithmic L², the real-valued jump pairing
agrees with the squared Fourier Sobolev norm. -/
theorem lineL2_jumpPairing_tempered_self_eq_fourier
    (f : Lp ℂ 2 (volume : Measure ℝ)) {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (henergy : Integrable (fun ξ ↦ (1 + (2 * Real.pi * ξ) ^ 2) ^ s * ‖(𝓕 f) ξ‖ ^ 2)) :
    jumpPairing volume (temperedJumpPairMeasure s) f f =
      ∫ ξ, (1 + (2 * Real.pi * ξ) ^ 2) ^ s * ‖(𝓕 f) ξ‖ ^ 2 := by
  have hf2 : Integrable (fun x ↦ ‖f x‖ ^ 2) := by
    simpa using (Lp.memLp f).integrable_norm_rpow (by norm_num) (by simp)
  exact jumpPairing_tempered_self_eq_of_lintegral f (𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) s
    (Lp.stronglyMeasurable f).measurable hf2 henergy
    (lineL2_fractional_energy_eq_tempered_jump f hs hs')

end RiemannMasullo
