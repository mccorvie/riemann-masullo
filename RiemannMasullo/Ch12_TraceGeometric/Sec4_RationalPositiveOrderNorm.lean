module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealAnnularQuotient
import RiemannMasullo.Ch12_TraceGeometric.Sec4_RationalOrderZeroLevel
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Strict comparison of rational Sobolev norms on one physical profile

The positive-ray logarithmic weight is strictly greater than one off the
single radius one. Thus an actual nonzero half-twisted test has a larger
squared norm at every positive order than the same test has at order zero.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap

namespace RiemannMasullo.AnnularBand

/-- A nonzero common ray representative has strictly larger squared integral at positive order. -/
theorem integral_sq_positiveRayLogMeasure_zero_lt {s : ℝ} (hs : 0 < s) (f : ℝ → ℂ)
    (hfs : MemLp f 2 (positiveRayLogMeasure s))
    (hne : ¬ f =ᵐ[positiveRayLogMeasure 0] 0) :
    (∫ x, ‖f x‖ ^ 2 ∂positiveRayLogMeasure 0) < ∫ x, ‖f x‖ ^ 2 ∂positiveRayLogMeasure s := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let w (x : ℝ) := (1 + Real.log x ^ 2) ^ (s / 2)
  let g (x : ℝ) := ‖f x‖ ^ 2
  have hμ₀ : positiveRayLogMeasure 0 = μ := by simp [positiveRayLogMeasure, μ]
  have hμs : positiveRayLogMeasure s = μ.withDensity (fun x ↦ ENNReal.ofReal (w x)) := rfl
  have hwm : Measurable (fun x ↦ ENNReal.ofReal (w x)) := by unfold w; fun_prop
  have hwt : ∀ᵐ x ∂μ, ENNReal.ofReal (w x) < ⊤ := .of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hw₁ (x : ℝ) : 1 ≤ w x := Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg _))
    (by positivity)
  have hμle : positiveRayLogMeasure 0 ≤ positiveRayLogMeasure s := by
    unfold positiveRayLogMeasure
    apply withDensity_mono
    filter_upwards with x
    apply ENNReal.ofReal_le_ofReal
    simpa only [zero_div, Real.rpow_zero] using hw₁ x
  have hf₀ := hfs.mono_measure hμle
  have hstrict : ∀ᵐ x ∂μ, 1 < w x := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ))),
      ae_restrict_of_ae (Measure.ae_ne volume (1 : ℝ))] with x hx hx₁
    have hlog := Real.log_ne_zero_of_pos_of_ne_one hx hx₁
    exact Real.one_lt_rpow (lt_add_of_pos_right _ (sq_pos_of_ne_zero hlog)) (by positivity)
  have hsmul : (fun x ↦ (ENNReal.ofReal (w x)).toReal • g x) = fun x ↦ w x * g x := by
    funext x
    rw [ENNReal.toReal_ofReal (zero_le_one.trans (hw₁ x)), smul_eq_mul]
  have hg₀ : Integrable g μ := hμ₀ ▸ (memLp_two_iff_integrable_sq_norm hf₀.aestronglyMeasurable).mp hf₀
  have hgs : Integrable (fun x ↦ w x * g x) μ := by
    have hi : Integrable g (positiveRayLogMeasure s) :=
      (memLp_two_iff_integrable_sq_norm hfs.aestronglyMeasurable).mp hfs
    rwa [hμs, integrable_withDensity_iff_integrable_smul' hwm hwt, hsmul] at hi
  have hle : g ≤ᵐ[μ] (fun x ↦ w x * g x) :=
    .of_forall fun x ↦ le_mul_of_one_le_left (sq_nonneg _) (hw₁ x)
  change (∫ x, g x ∂positiveRayLogMeasure 0) < ∫ x, g x ∂positiveRayLogMeasure s
  rw [hμ₀, hμs, integral_withDensity_eq_integral_toReal_smul hwm hwt, hsmul]
  refine (integral_mono_ae hg₀ hgs hle).lt_of_ne fun he ↦ hne ?_
  rw [hμ₀]
  filter_upwards [(integral_eq_iff_of_ae_le hg₀ hgs hle).mp he, hstrict] with x heq hx
  change f x = 0
  by_contra hfx
  have hg : 0 < g x := pow_pos (norm_pos_iff.mpr hfx) 2
  exact (lt_mul_of_one_lt_left hg hx).ne heq

/-- The squared Hilbert norms themselves are strictly ordered for classes with the same profile. -/
theorem positiveRay_sameProfile_norm_sq_lt {s : ℝ} (hs : 0 < s)
    (f₀ : Lp ℂ 2 (positiveRayLogMeasure 0)) (fs : Lp ℂ 2 (positiveRayLogMeasure s))
    (heq : (f₀ : ℝ → ℂ) =ᵐ[positiveRayLogMeasure 0] fs) (hne : f₀ ≠ 0) :
    ‖f₀‖ ^ 2 < ‖fs‖ ^ 2 := by
  have heqs : (f₀ : ℝ → ℂ) =ᵐ[positiveRayLogMeasure s] fs :=
    (positiveRayLogMeasure_ae_eq_iff s _ _).mpr ((positiveRayLogMeasure_ae_eq_iff 0 _ _).mp heq)
  have hfs := (memLp_congr_ae heqs).mpr (Lp.memLp fs)
  rw [← L2.integral_sq_norm (𝕜 := ℂ) f₀, ← L2.integral_sq_norm (𝕜 := ℂ) fs]
  exact (integral_sq_positiveRayLogMeasure_zero_lt hs _ hfs
    (fun h ↦ hne (Lp.eq_zero_iff_ae_eq_zero.mpr h))).trans_eq
    (integral_congr_ae (heqs.mono fun _ hx ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hx))

/-- The very same banded algebraic test has larger quotient norm at positive order once its
theta profile represents a nonzero class. -/
theorem thetaLift_sameTest_norm_sq_lt {s : ℝ} (hs : 0 < s) (B : ℝ) (f : tests B)
    (hne : thetaLift 0 B f ≠ 0) : ‖thetaLift 0 B f‖ ^ 2 < ‖thetaLift s B f‖ ^ 2 := by
  let := positiveRayLogMeasure_hasTemperateGrowth 0 le_rfl
  let := positiveRayLogMeasure_hasTemperateGrowth s hs.le
  let p := profile f.val.val
  let u := p.toLp 2 (positiveRayLogMeasure 0)
  let v := p.toLp 2 (positiveRayLogMeasure s)
  have hu : positiveRayToQuotientLp 0 u = thetaLift 0 B f :=
    positiveRayToQuotientLp_profile 0 B le_rfl f
  have hv : positiveRayToQuotientLp s v = thetaLift s B f :=
    positiveRayToQuotientLp_profile s B hs.le f
  have huz : u ≠ 0 := fun h ↦ hne (hu.symm.trans (h ▸ map_zero (positiveRayToQuotientLp 0)))
  have hEq : (u : ℝ → ℂ) =ᵐ[positiveRayLogMeasure 0] v :=
    (p.coeFn_toLp 2 (positiveRayLogMeasure 0)).trans ((positiveRayLogMeasure_ae_eq_iff 0 _ _).mpr
      ((positiveRayLogMeasure_ae_eq_iff s _ _).mp (p.coeFn_toLp 2 (positiveRayLogMeasure s))).symm)
  have hlt := positiveRay_sameProfile_norm_sq_lt hs u v hEq huz
  rw [← hu, ← hv, positiveRayToQuotientLp_norm, positiveRayToQuotientLp_norm, mul_pow, mul_pow]
  exact mul_lt_mul_of_pos_left hlt (pow_pos (Real.sqrt_pos.mpr sLocalNormOneQuotientMeasure_ratEmpty_mass_pos) 2)

/-- Any pointwise nonzero smooth signed profile gives the strict inequality on the actual
arithmetic band, even before passing to its closure. -/
theorem thetaLift_norm_sq_lt_of_profile_ne_zero {s : ℝ} (hs : 0 < s) (B : ℝ) (f : tests B)
    (hp : profile f.val.val ≠ 0) : ‖thetaLift 0 B f‖ ^ 2 < ‖thetaLift s B f‖ ^ 2 := by
  apply thetaLift_sameTest_norm_sq_lt hs B f
  intro h
  have hnorm := profileBound 0 B le_rfl f
  rw [h, norm_zero, mul_zero] at hnorm
  have hzero := norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
  have hae := ((profile f.val.val).coeFn_toLp 2 volume).symm.trans
    (Lp.eq_zero_iff_ae_eq_zero.mp hzero)
  have he : (profile f.val.val : ℝ → ℂ) = 0 :=
    Measure.eq_of_ae_eq hae (profile f.val.val).continuous continuous_const
  exact hp (SchwartzMap.ext fun x ↦ congrFun he x)

/-- Every positive bandwidth admits a genuine rational test whose positive-order half-twisted norm exceeds its
order-zero norm. The full-line closure witness detects a nonzero generator. -/
theorem exists_test_thetaLift_norm_sq_lt {B s : ℝ} (hB : 0 < B) (hs : 0 < s) :
    ∃ f : tests B, ‖thetaLift 0 B f‖ ^ 2 < ‖thetaLift s B f‖ ^ 2 := by
  have hgen : ∃ f : tests B, thetaLift 0 B f ≠ 0 := by
    by_contra! hzero
    have hz : thetaLift 0 B = 0 := LinearMap.ext fun f ↦ hzero f
    have hV := actualLevel (s := 0) le_rfl B
    rw [LinearMap.range_eq_bot.mpr hz,
      IsClosed.submodule_topologicalClosure_eq (by simp)] at hV
    have hU := map_invariantOrderZeroLevel_evenExtension
        (1 : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker) hB
    rw [hV, Submodule.map_bot] at hU
    obtain ⟨F, hF, hi⟩ := exists_mem_realPWLevel_integral_ne_zero hB
    rw [← hU] at hF
    have hFz : F.toLp 2 volume = 0 := by simpa using hF
    apply hi
    calc
      (∫ x, F x) = ∫ _ : ℝ, (0 : ℂ) := integral_congr_ae
        ((F.coeFn_toLp 2 volume).symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hFz))
      _ = 0 := by simp
  obtain ⟨f, hf⟩ := hgen
  exact ⟨f, thetaLift_sameTest_norm_sq_lt hs B f hf⟩

end RiemannMasullo.AnnularBand
