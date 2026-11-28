module

public import RiemannMasullo.AppA_AlgebraicNT.Sec3
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Positive Haar half-densities on the real ray -/

public noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace RiemannMasullo.RatEmptyHaarHalfDensity

local instance : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
private abbrev ray := volume.restrict (Ioi (0 : ℝ))
private def E : ℝ ≃ₜ ℝ≥0ˣ :=
  Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
private theorem haar_map : positiveRealHaar = volume.map E := by
  apply congrArg (fun h : ℝ → ℝ≥0ˣ ↦ volume.map h)
  funext y
  exact Units.ext (NNReal.eq (Real.coe_toNNReal _ (Real.exp_pos y).le))

private theorem substitution (g : ℝ → ℝ≥0∞) :
    ∫⁻ r, g r ∂ray = ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp x) * g (Real.exp x) := by
  simpa [image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _)] using
    lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
      (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g

private theorem flat_ae {P : ℝ → Prop} :
    (∀ᵐ r ∂ray, P r) ↔ ∀ᵐ x : ℝ, P (Real.exp x) := by
  let w (x : ℝ) := ENNReal.ofReal (Real.exp x)
  have hw : Measurable w := by dsimp [w]; fun_prop
  have h : ray = (volume.withDensity w).map Real.exp := by
    apply Measure.ext_of_lintegral
    intro g hg
    rw [lintegral_map hg Real.continuous_exp.measurable]
    change _ = ∫⁻ x, (g ∘ Real.exp) x ∂volume.withDensity w
    rw [lintegral_withDensity_eq_lintegral_mul _ hw (hg.comp Real.continuous_exp.measurable)]
    exact substitution g
  rw [h, Real.isOpenEmbedding_exp.measurableEmbedding.ae_map_iff, ae_withDensity_iff hw]
  have hn (x : ℝ) : w x ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos x)
  exact ⟨fun H ↦ H.mono fun x hx ↦ hx (hn x), fun H ↦ H.mono fun _ hx _ ↦ hx⟩

private theorem haar_ae {P : ℝ≥0ˣ → Prop} :
    (∀ᵐ t ∂positiveRealHaar, P t) ↔ ∀ᵐ x : ℝ, P (E x) := by
  rw [haar_map, E.isClosedEmbedding.measurableEmbedding.ae_map_iff]

private abbrev rad (t : ℝ≥0ˣ) : ℝ := t.val
private theorem rad_E (x : ℝ) : rad (E x) = Real.exp x := rfl
private theorem rad_meas : Measurable rad :=
  (NNReal.continuous_coe.comp Units.continuous_val).measurable
/-- Ray-almost-everywhere statements pull back to Haar norm coordinates. -/
theorem rad_ae {P : ℝ → Prop} (h : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)), P r) :
    ∀ᵐ t ∂positiveRealHaar, P (t.val : ℝ) :=
  (haar_ae (P := fun t ↦ P (rad t))).2 ((flat_ae (P := P)).1 h)
private def lift (g : ℝ → ℂ) (t : ℝ≥0ˣ) : ℂ := (Real.sqrt (rad t) : ℂ) * g (rad t)
private theorem lift_meas {g : ℝ → ℂ} (hg : Measurable g) : Measurable (lift g) :=
  (Complex.continuous_ofReal.measurable.comp (Real.continuous_sqrt.measurable.comp rad_meas)).mul
    (hg.comp rad_meas)

private theorem lift_norm {g : ℝ → ℂ} (hg : Measurable g) :
    eLpNorm (lift g) 2 positiveRealHaar = eLpNorm g 2 ray := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num)
        (lift_meas hg).aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hg.aestronglyMeasurable,
      haar_map, E.isClosedEmbedding.measurableEmbedding.lintegral_map, substitution]
  congr 1
  apply lintegral_congr
  intro x
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, lift, rad_E]
  rw [← ofReal_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_pow,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (Real.exp_pos _).le, ofReal_norm]

private theorem lift_mem (g : Lp ℂ 2 ray) : MemLp (lift g) 2 positiveRealHaar :=
  (lift_norm (Lp.stronglyMeasurable g).measurable).trans_lt (Lp.memLp g)

private def back : Lp ℂ 2 ray →ₗᵢ[ℂ] Lp ℂ 2 positiveRealHaar where
  toFun g := (lift_mem g).toLp _
  norm_map' g := by
    change ‖(lift_mem g).toLp _‖ = ‖g‖
    rw [Lp.norm_toLp, Lp.norm_def, lift_norm (Lp.stronglyMeasurable g).measurable]
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(lift_mem (f+g)).coeFn_toLp, (lift_mem f).coeFn_toLp,
      (lift_mem g).coeFn_toLp, Lp.coeFn_add ((lift_mem f).toLp _) ((lift_mem g).toLp _),
      rad_ae (P := fun r ↦ (f+g) r = f r + g r)
        (by simpa only [Filter.EventuallyEq, Pi.add_apply] using Lp.coeFn_add f g)] with t ha hf hg hs ht
    simp_all [lift, mul_add]
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [(lift_mem (c • g)).coeFn_toLp, (lift_mem g).coeFn_toLp,
      Lp.coeFn_smul c ((lift_mem g).toLp _),
      rad_ae (P := fun r ↦ (c • g) r = c • g r)
        (by simpa only [Filter.EventuallyEq, Pi.smul_apply] using Lp.coeFn_smul c g)] with t ha hg hs ht
    simp_all [lift, smul_eq_mul, mul_left_comm]

/-- The extension off the ray is immaterial for the restricted measure. -/
def representative (f : ℝ≥0ˣ → ℂ) (r : ℝ) : ℂ := f (E (Real.log r)) / (Real.sqrt r : ℂ)

private theorem recover (f : ℝ≥0ˣ → ℂ) : lift (representative f) = f := by
  funext t
  obtain ⟨x, rfl⟩ := E.surjective t
  simp only [lift, representative, rad_E, Real.log_exp]
  have hn : (Real.sqrt (Real.exp x) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (Real.exp_pos x)).ne'
  field_simp [hn]

private theorem rep_mem (f : Lp ℂ 2 positiveRealHaar) : MemLp (representative f) 2 ray := by
  have hm : Measurable (representative f) :=
    ((Lp.stronglyMeasurable f).measurable.comp (E.continuous.measurable.comp Real.measurable_log)).div
      (Complex.continuous_ofReal.measurable.comp Real.continuous_sqrt.measurable)
  change eLpNorm (representative f) 2 ray < ∞
  rw [← lift_norm hm, recover]
  exact Lp.memLp f

private theorem back_rep (f : Lp ℂ 2 positiveRealHaar) : back ((rep_mem f).toLp _) = f := by
  let g := (rep_mem f).toLp _
  apply Lp.ext
  filter_upwards [(lift_mem g).coeFn_toLp,
    rad_ae (P := fun r ↦ g r = representative f r) (rep_mem f).coeFn_toLp] with t ht hr
  exact ht.trans ((congrArg (fun z : ℂ ↦ (Real.sqrt (rad t) : ℂ) * z) hr).trans
    (congrFun (recover f) t))

/-- Multiplication by the positive Haar half-density, with no normalization constant. -/
def halfDensity : Lp ℂ 2 positiveRealHaar ≃ₗᵢ[ℂ] Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (LinearIsometryEquiv.ofSurjective back (fun f ↦ ⟨_, back_rep f⟩)).symm

/-- Inverse transport reinstates the square-root half-density on Haar representatives. -/
theorem halfDensity_symm_apply_ae (g : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    ⇑(halfDensity.symm g) =ᵐ[positiveRealHaar]
      fun t ↦ (Real.sqrt (t.val : ℝ) : ℂ) * g (t.val : ℝ) :=
  (lift_mem g).coeFn_toLp

theorem halfDensity_apply_ae (f : Lp ℂ 2 positiveRealHaar) :
    ⇑(halfDensity f) =ᵐ[volume.restrict (Ioi (0 : ℝ))] representative f := by
  have h : halfDensity f = (rep_mem f).toLp _ := by
    apply halfDensity.symm.injective
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact (back_rep f).symm
  rw [h]
  exact (rep_mem f).coeFn_toLp

end RiemannMasullo.RatEmptyHaarHalfDensity
