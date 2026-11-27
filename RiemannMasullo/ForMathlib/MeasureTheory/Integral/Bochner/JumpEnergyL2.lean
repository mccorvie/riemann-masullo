module

public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.Bochner.JumpEnergy
public import RiemannMasullo.ForMathlib.Analysis.Fourier.L2TranslationJump
public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.Bochner.JumpEnergyRepresentatives
import Mathlib.MeasureTheory.Group.Prod

/-! # Tempered fractional jump energy on the actual real L² domain

The exact identity extends past the Schwartz core. It holds for extended
energies without a domain assumption and for the ordinary real pairing on
the finite Fourier energy domain. -/

public noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform ComplexConjugate

namespace RiemannMasullo

local notation "J₂" => Lp ℂ 2 (volume : Measure ℝ)
local notation "F₂(" u ")" => (Lp.fourierTransformₗᵢ ℝ ℂ) u

private theorem lp_sq_integrable (u : J₂) : Integrable (fun x ↦ ‖u x‖ ^ 2) := by
  simpa using (Lp.memLp u).integrable_norm_rpow (by norm_num) (by simp)

private theorem lp_mass_plancherel (u : J₂) :
    (∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2)) = ∫⁻ ξ, ENNReal.ofReal (‖F₂(u) ξ‖ ^ 2) := by
  rw [l2_lintegral_norm_sq, l2_lintegral_norm_sq]
  change ‖u‖ₑ ^ 2 = ‖(𝓕 u : J₂)‖ₑ ^ 2
  simp only [← ofReal_norm, Lp.norm_fourier_eq]

/-- The closed form identity as an equality of extended energies, without a domain assumption. -/
theorem lp_fractional_energy_eq_tempered_pair (u : J₂) {s : ℝ}
    (hs : 0 < s) (hs' : s < 1) :
    (∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2)) + (2 : ℝ≥0∞)⁻¹ *
      (∫⁻ z, ENNReal.ofReal (‖u z.1 - u z.2‖ ^ 2) ∂temperedJumpPairMeasure s) =
      ∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ s) * ENNReal.ofReal (‖F₂(u) ξ‖ ^ 2) := by
  let : SFinite (temperedJumpMeasure s) := sFinite_temperedJumpMeasure s
  let a (ξ : ℝ) := ENNReal.ofReal (‖F₂(u) ξ‖ ^ 2)
  let b (h ξ : ℝ) := ENNReal.ofReal (‖(𝐞 (h * ξ) : ℂ) - 1‖ ^ 2)
  let w (ξ : ℝ) := (1 + (2 * Real.pi * ξ) ^ 2) ^ s
  have hu := (Lp.stronglyMeasurable u).measurable
  have ha : Measurable a := ENNReal.measurable_ofReal.comp ((Lp.stronglyMeasurable F₂(u)).measurable.norm.pow_const 2)
  have hb : Measurable (Function.uncurry b) := ENNReal.measurable_ofReal.comp
    (by fun_prop : Continuous (fun z : ℝ × ℝ ↦ ‖(𝐞 (z.1 * z.2) : ℂ) - 1‖ ^ 2)).measurable
  have hm : Measurable (fun z : ℝ × ℝ ↦ ENNReal.ofReal (‖u z.1 - u z.2‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (((hu.comp measurable_fst).sub (hu.comp measurable_snd)).norm.pow_const 2)
  have hT : Measurable (fun z : ℝ × ℝ ↦ (z.2 + z.1, z.2)) := by fun_prop
  have hj : (∫⁻ z, ENNReal.ofReal (‖u z.1 - u z.2‖ ^ 2) ∂temperedJumpPairMeasure s) =
      ∫⁻ ξ, (∫⁻ h, b h ξ ∂temperedJumpMeasure s) * a ξ := by
    rw [temperedJumpPairMeasure_eq_map, lintegral_map hm hT]
    change (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (‖u (z.2 + z.1) - u z.2‖ ^ 2)
      ∂(temperedJumpMeasure s).prod volume) = _
    have hprod := lintegral_prod (μ := temperedJumpMeasure s) (ν := (volume : Measure ℝ))
      (fun z : ℝ × ℝ ↦ ENNReal.ofReal (‖u (z.2 + z.1) - u z.2‖ ^ 2)) (hm.comp hT).aemeasurable
    rw [hprod]
    simp_rw [l2_lintegral_sq_translate_sub]
    change (∫⁻ h, (∫⁻ ξ, b h ξ * a ξ) ∂_) = _
    rw [lintegral_lintegral_swap (f := fun h ξ ↦ b h ξ * a ξ) (hb.mul (ha.comp measurable_snd)).aemeasurable]
    exact lintegral_congr fun ξ ↦ lintegral_mul_const' (a ξ) (b · ξ) ENNReal.ofReal_ne_top
  rw [lp_mass_plancherel, hj, ← lintegral_const_mul' _ _ (by simp)]
  have hhalf (ξ : ℝ) : (2 : ℝ≥0∞)⁻¹ * ((∫⁻ h, b h ξ ∂temperedJumpMeasure s) * a ξ) =
      ENNReal.ofReal (w ξ - 1) * a ξ := by
    rw [← mul_assoc, temperedJumpMeasure_symbol hs hs' ξ]
  simp_rw [hhalf]
  rw [← lintegral_add_left ha]
  refine lintegral_congr fun ξ ↦ ?_
  have h1 : 1 ≤ w ξ := Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg _)) hs.le
  change a ξ + ENNReal.ofReal (w ξ - 1) * a ξ = ENNReal.ofReal (w ξ) * a ξ
  rw [← one_add_mul, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (sub_nonneg.mpr h1)]
  congr 2
  ring

/-- For any measurable representative in the finite weighted domain (in particular a finite
frequency cutoff), the normalized real pairing is the ordinary weighted Fourier integral. -/
theorem jumpPairing_tempered_lp_self_eq_fourier (u : J₂) {s : ℝ}
    (hs : 0 < s) (hs' : s < 1) {f : ℝ → ℂ}
    (hf : Measurable f) (he : f =ᵐ[volume] u)
    (hfinite : (∫⁻ ξ, ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ s) *
      ENNReal.ofReal (‖F₂(u) ξ‖ ^ 2)) ≠ ⊤) :
    jumpPairing volume (temperedJumpPairMeasure s) f f =
      ∫ ξ, (1 + (2 * Real.pi * ξ) ^ 2) ^ s * ‖F₂(u) ξ‖ ^ 2 := by
  let g (ξ : ℝ) := (1 + (2 * Real.pi * ξ) ^ 2) ^ s * ‖F₂(u) ξ‖ ^ 2
  let j (z : ℝ × ℝ) := ‖f z.1 - f z.2‖ ^ 2
  have hf' := (Lp.stronglyMeasurable F₂(u)).measurable
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hj : Measurable j := ((hf.comp measurable_fst).sub (hf.comp measurable_snd)).norm.pow_const 2
  have hg0 : ∀ ξ, 0 ≤ g ξ := fun _ ↦ by dsimp [g]; positivity
  have hj0 : ∀ z, 0 ≤ j z := fun _ ↦ sq_nonneg _
  have hmul (ξ : ℝ) : ENNReal.ofReal ((1 + (2 * Real.pi * ξ) ^ 2) ^ s) *
      ENNReal.ofReal (‖F₂(u) ξ‖ ^ 2) = ENNReal.ofReal (g ξ) :=
    (ENNReal.ofReal_mul (by positivity : 0 ≤ (1 + (2 * Real.pi * ξ) ^ 2) ^ s)).symm
  have h := lp_fractional_energy_eq_tempered_pair u hs hs'
  have hm : (∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2)) = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) := by
    apply lintegral_congr_ae; filter_upwards [he] with x hx; rw [hx]
  have hp : (∫⁻ z, ENNReal.ofReal (‖u z.1 - u z.2‖ ^ 2) ∂temperedJumpPairMeasure s) =
      ∫⁻ z, ENNReal.ofReal (j z) ∂temperedJumpPairMeasure s := by
    apply lintegral_congr_ae
    filter_upwards [temperedJumpPairMeasure_sub_congr_ae s he] with z hz
    change f z.1 - f z.2 = u z.1 - u z.2 at hz
    simp only [j, hz]
  simp_rw [hmul] at h hfinite
  rw [hm, hp] at h
  have hjfin : (∫⁻ z, ENNReal.ofReal (j z) ∂temperedJumpPairMeasure s) ≠ ⊤ := by
    intro ht'; rw [ht', ENNReal.mul_top (by simp), add_top] at h; exact hfinite h.symm
  have hmfin : (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) ≠ ⊤ := by
    intro ht'; rw [ht', top_add] at h; exact hfinite h.symm
  have hR := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add hmfin (ENNReal.mul_ne_top (by simp) hjfin), ENNReal.toReal_mul] at hR
  rw [jumpPairing_apply]
  have hsq (z : ℂ) : (conj z * z).re = ‖z‖ ^ 2 := by
    simp [Complex.mul_re, Complex.normSq_apply, Complex.sq_norm]
  simp_rw [hsq]
  change (∫ x, ‖f x‖ ^ 2) + (1 / 2) * (∫ z, j z ∂temperedJumpPairMeasure s) = ∫ ξ, g ξ
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ sq_nonneg ‖f x‖)
      (hf.norm.pow_const 2).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hj0) hj.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hg.aestronglyMeasurable]
  simpa [one_div] using hR

/-- A finite frequency cutoff is automatically in the finite weighted domain. -/
theorem jumpPairing_tempered_lp_frequency_cutoff (u : J₂) {s : ℝ}
    (hs : 0 < s) (hs' : s < 1) {K : Set ℝ} (hK : IsCompact K)
    (hcut : ∀ᵐ ξ ∂volume, ξ ∉ K → F₂(u) ξ = 0) :
    jumpPairing volume (temperedJumpPairMeasure s) u u =
      ∫ ξ, (1 + (2 * Real.pi * ξ) ^ 2) ^ s * ‖F₂(u) ξ‖ ^ 2 := by
  apply jumpPairing_tempered_lp_self_eq_fourier u hs hs' (Lp.stronglyMeasurable u).measurable
    (Filter.EventuallyEq.rfl)
  let w (ξ : ℝ) := (1 + (2 * Real.pi * ξ) ^ 2) ^ s
  have hw : Continuous w := by dsimp [w]; fun_prop
  obtain ⟨C, hC⟩ := hK.bddAbove_image hw.continuousOn
  have hm : (∫⁻ ξ, ENNReal.ofReal (‖F₂(u) ξ‖ ^ 2)) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal (lp_sq_integrable F₂(u))
      (ae_of_all _ fun _ ↦ sq_nonneg _)]
    exact ENNReal.ofReal_ne_top
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top (show ENNReal.ofReal C ≠ ⊤ from ENNReal.ofReal_ne_top) hm)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hcut] with ξ hξ
  by_cases h : ξ ∈ K
  · exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (hC ⟨ξ, h, rfl⟩)) (by positivity)
  · simp [hξ h]

end RiemannMasullo
