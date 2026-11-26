module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.WeightedPaleyWienerBand
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Reciprocal-density packets for weighted real Paley–Wiener evaluation -/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform InnerProductSpace

namespace RiemannMasullo.RealPWBand

/-- The reciprocal-density packet, with its representative, exact energy and pairing.
Only positivity and integrability of the reciprocal energy are needed. -/
private theorem exists_reciprocalPacket {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w : X → ℝ} (hw : Measurable w) (hwpos : ∀ t, 0 < w t) {k : X → ℂ}
    (hk : AEStronglyMeasurable k μ) (hE : Integrable (fun t ↦ ‖k t‖ ^ 2 / w t) μ) :
    ∃ r : Lp ℂ 2 (μ.withDensity fun t ↦ ENNReal.ofReal (w t)),
      (∀ᵐ t ∂μ, r t = star (k t) / (w t : ℂ)) ∧
      ‖r‖ ^ 2 = (∫ t, ‖k t‖ ^ 2 / w t ∂μ) ∧
      ∀ f : Lp ℂ 2 (μ.withDensity fun t ↦ ENNReal.ofReal (w t)),
        inner ℂ r f = ∫ t, f t * k t ∂μ := by
  let d (t : X) := ENNReal.ofReal (w t)
  have hd : Measurable d := hw.ennreal_ofReal
  have hfin : ∀ᵐ t ∂μ, d t < ∞ := .of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hbase : μ ≪ μ.withDensity d := withDensity_absolutelyContinuous' hd.aemeasurable
    (.of_forall fun t ↦ (ENNReal.ofReal_pos.mpr (hwpos t)).ne')
  let u (t : X) := star (k t) / (w t : ℂ)
  have hu : AEStronglyMeasurable u (μ.withDensity d) :=
    (hk.mono_ac (withDensity_absolutelyContinuous _ _)).star.div₀
      (Complex.measurable_ofReal.comp hw).aestronglyMeasurable
  have energy (t : X) : ‖u t‖ ^ 2 * (d t).toReal = ‖k t‖ ^ 2 / w t := by
    dsimp only [u, d]
    rw [norm_div, norm_star, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hwpos t),
      ENNReal.toReal_ofReal (hwpos t).le]
    field_simp [(hwpos t).ne']
  have hmem : MemLp u 2 (μ.withDensity d) := by
    apply (memLp_two_iff_integrable_sq_norm hu).2
    exact (integrable_withDensity_iff hd hfin).2 (hE.congr (.of_forall fun t ↦ (energy t).symm))
  let r := hmem.toLp u
  have hr : (r : X → ℂ) =ᵐ[μ] u := hbase.ae_eq hmem.coeFn_toLp
  refine ⟨r, hr, ?_, ?_⟩
  · rw [← L2.integral_sq_norm (𝕜 := ℂ) r, integral_withDensity_eq_integral_toReal_smul hd hfin]
    apply integral_congr_ae
    filter_upwards [hr] with t ht
    simpa only [ht, smul_eq_mul, mul_comm (d t).toReal] using energy t
  · intro f
    rw [L2.inner_def, integral_withDensity_eq_integral_toReal_smul hd hfin]
    apply integral_congr_ae
    filter_upwards [hr] with t ht
    have hne : (w t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hwpos t).ne'
    rw [ht, RCLike.inner_apply, starRingEnd_apply]
    change (ENNReal.ofReal (w t)).toReal • (f t * star (star (k t) / (w t : ℂ))) = _
    rw [ENNReal.toReal_ofReal (hwpos t).le, star_div₀, star_star,
      show star (w t : ℂ) = (w t : ℂ) from Complex.conj_ofReal _, Complex.real_smul]
    field_simp [hne]

/-- Lebesgue specialization to the translate `k(t) = φ(t-x)`. The lower bound on the
weight makes the reciprocal energy finite for every `L²` window. -/
private theorem exists_weightedPWReciprocalPacket {w : ℝ → ℝ} (hw : Measurable w)
    (hw1 : ∀ t, 1 ≤ w t) {φ : ℝ → ℂ} (hφ : MemLp φ 2 volume) (x : ℝ) :
    ∃ r : Lp ℂ 2 (volume.withDensity fun t ↦ ENNReal.ofReal (w t)),
      (∀ᵐ t ∂volume, r t = star (φ (t-x)) / (w t : ℂ)) ∧
      ‖r‖ ^ 2 = (∫ t, ‖φ (t-x)‖ ^ 2 / w t) ∧
      ∀ f : Lp ℂ 2 (volume.withDensity fun t ↦ ENNReal.ofReal (w t)),
        inner ℂ r f = ∫ t, f t * φ (t-x) := by
  have hk : MemLp (fun t ↦ φ (t-x)) 2 volume := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      hφ.comp_measurePreserving (measurePreserving_add_right volume (-x))
  apply exists_reciprocalPacket hw (fun t ↦ zero_lt_one.trans_le (hw1 t)) hk.aestronglyMeasurable
  refine ((memLp_two_iff_integrable_sq_norm hk.aestronglyMeasurable).1 hk).mono'
    ((hk.aestronglyMeasurable.norm.pow 2).div₀ hw.aestronglyMeasurable) ?_
  refine .of_forall fun t ↦ ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (zero_le_one.trans (hw1 t)))]
  exact div_le_self (sq_nonneg _) (hw1 t)

/-- Projecting any ambient representative of the reciprocal-weight kernel gives the
Riesz vector of band evaluation. No construction of the ambient vector is needed. -/
private theorem evaluationVector_eq_projected_reproducer (Y x : ℝ) {w : ℝ → ℝ}
    (hμ : volume ≤ volume.withDensity (fun t ↦ ENNReal.ofReal (w t)))
    {φ : ℝ → ℂ} (hφ : Integrable φ) (hone : ∀ ξ ∈ Icc (-Y) Y, 𝓕⁻ φ ξ = 1)
    (r : Lp ℂ 2 (volume.withDensity (fun t ↦ ENNReal.ofReal (w t))))
    (hpair : ∀ u : Lp ℂ 2 (volume.withDensity (fun t ↦ ENNReal.ofReal (w t))),
      inner ℂ r u = ∫ t, u t * φ (t - x)) :
    evaluationVector Y hμ x = (space Y hμ).orthogonalProjectionOnto r := by
  apply ext_inner_right ℂ
  intro f
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    ← InnerProductSpace.toDual_apply_apply, toDual_evaluationVector,
    evaluation_reproduces Y hμ f hφ hone x, hpair]
  let F (t : ℝ) := evaluation Y hμ t f * φ (t - x)
  have hshift : (∫ t, evaluation Y hμ (x + t) f * φ t) = ∫ t, F t := by
    simpa only [F, add_sub_cancel_left] using integral_add_left_eq_self F x
  rw [hshift]
  have hac := Measure.absolutelyContinuous_of_le hμ
  have hf := evaluation_ae Y hμ (withDensity_absolutelyContinuous _ _) f
  apply integral_congr_ae
  filter_upwards [hac.ae_eq hf] with t hft
  simp only [F, hft]

/-- The canonical evaluation vector is the band projection of the translated
Schwartz reproducer divided by the physical weight. Its ambient energy uses
the reciprocal density, even when the physical density is singular at zero. -/
theorem exists_evaluationVector_eq_projected_reproducer (Y x : ℝ) {w : ℝ → ℝ}
    (hw : Measurable w) (hw₁ : ∀ t, 1 ≤ w t)
    (hμ : volume ≤ volume.withDensity (fun t ↦ ENNReal.ofReal (w t)))
    {φ : ℝ → ℂ} (hφ : Integrable φ) (hφ₂ : MemLp φ 2 volume)
    (hone : EqOn (𝓕⁻ φ) 1 (Icc (-Y) Y)) :
    ∃ r : Lp ℂ 2 (volume.withDensity fun t ↦ ENNReal.ofReal (w t)),
      (∀ᵐ t ∂volume, r t = star (φ (t - x)) / (w t : ℂ)) ∧
      evaluationVector Y hμ x = (space Y hμ).orthogonalProjectionOnto r ∧
      ‖r‖ ^ 2 = (∫ t, ‖φ (t - x)‖ ^ 2 / w t) := by
  obtain ⟨r, hr, hn, hp⟩ := exists_weightedPWReciprocalPacket hw hw₁ hφ₂ x
  exact ⟨r, hr, evaluationVector_eq_projected_reproducer Y x hμ hφ hone r hp, hn⟩

end RiemannMasullo.RealPWBand
