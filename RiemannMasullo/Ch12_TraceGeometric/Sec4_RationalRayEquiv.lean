module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealAnnularQuotient
public import RiemannMasullo.Ch03_IdelicZeta.RatEmptyNormHaar
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelBridge
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-!
# The half-twist on the rational idèle quotient

At the empty finite stage the norm-one quotient of the rational idèles is trivial.
The positive norm ray therefore provides an inverse on each weighted Hilbert space.
-/

@[expose] public noncomputable section

open Function MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.AnnularBand

set_option quotPrecheck false
attribute [local instance] RiemannMasullo.instSIdeleQuotientMeasurableSpaceSec1

local notation "J" => SIdeleQuotient ℚ ∅
local notation "m" => continuousSIdeleQuotientNorm ℚ ∅
local notation "R(" g ")" => (((m g).val : ℝ))
local notation "μ" => sLocalQuotientTamagawaMeasure ℚ ∅
local notation "ν(" s ")" => (μ).withDensity
  (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (R(g)))))
local notation "H(" s ")" => Lp ℂ 2 ν(s)
local notation "Ray(" s ")" => Lp ℂ 2 (positiveRayLogMeasure s)

/-- Every weighted quotient class is the half-twist of a positive-ray class. -/
theorem positiveRayToQuotientLp_surjective (s : ℝ) : Surjective (positiveRayToQuotientLp s) := by
  let : BorelSpace J := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section ℚ ∅
  have hσ' (q : J) : σ (m q) = q := sIdeleQuotientNorm_ratEmpty_injective (hσ _)
  let e (t : ℝ) := Units.mk0 (Real.exp t).toNNReal (Real.toNNReal_eq_zero.not.mpr (Real.exp_pos t).not_ge)
  let v (x : ℝ) := e (Real.log x)
  have he : Measurable e := measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hv : Measurable v := he.comp Real.measurable_log
  have hv' (q : J) : v (R(q)) = m q := by
    apply Units.ext
    apply NNReal.eq
    rw [show ((v (R(q))).val : ℝ) = Real.exp (Real.log (R(q))) by
      exact Real.coe_toNNReal _ (Real.exp_pos _).le]
    exact Real.exp_log (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m q).ne_zero))
  intro u
  by_cases hu : u = 0
  · exact ⟨0, by simp [hu]⟩
  let f (x : ℝ) : ℂ := u (σ (v x)) / (Real.sqrt x : ℂ)
  have hf : Measurable f := ((Lp.stronglyMeasurable u).measurable.comp (σ.continuous.measurable.comp hv)).div
    (Complex.continuous_ofReal.measurable.comp Real.continuous_sqrt.measurable)
  have hfu (q : J) : quotientHalfTwistFun f q = u q := by
    have hpos : 0 < Real.sqrt (R(q)) := Real.sqrt_pos.mpr
      (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m q).ne_zero))
    rw [quotientHalfTwistFun_apply]
    change (Real.sqrt (R(q)) : ℂ) * (u (σ (v (R(q)))) / (Real.sqrt (R(q)) : ℂ)) = u q
    rw [hv', hσ']
    field_simp [Complex.ofReal_ne_zero.mpr hpos.ne']
  have hid := integral_sq_quotientHalfTwistFun s f hf
  simp_rw [hfu] at hid
  rw [L2.integral_sq_norm (𝕜 := ℂ) u] at hid
  have hnz : (∫ x, ‖f x‖ ^ 2 ∂positiveRayLogMeasure s) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hid
    exact hu (norm_eq_zero.mp ((sq_eq_zero_iff).mp hid))
  have hmem := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr (Integrable.of_integral_ne_zero hnz)
  refine ⟨hmem.toLp f, Lp.ext ?_⟩
  exact (positiveRayToQuotientLp_coeFn_of_ae_eq s _ f hf hmem.coeFn_toLp).trans
    (Filter.Eventually.of_forall hfu)

/-- The rational half-twist is a surjective linear isometry for every real weight exponent. -/
def positiveRayQuotientEquiv (s : ℝ) : Ray(s) ≃ₗᵢ[ℂ] H(s) :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (positiveRayToQuotientLp s).toLinearMap
      norm_map' := fun f ↦ by
        change ‖positiveRayToQuotientLp s f‖ = ‖f‖
        simpa only [measureReal_def, RatEmptyNormHaar.norm_one_mass, ENNReal.toReal_one, Real.sqrt_one, one_mul] using
          positiveRayToQuotientLp_norm s f }
    (positiveRayToQuotientLp_surjective s)

@[simp] theorem positiveRayQuotientEquiv_apply (s : ℝ) (f : Ray(s)) :
    positiveRayQuotientEquiv s f = positiveRayToQuotientLp s f := rfl

/-- At order zero the positive-ray chart uses Lebesgue measure. -/
theorem positiveRayLogMeasure_zero : positiveRayLogMeasure 0 = volume.restrict (Ioi (0 : ℝ)) := by
  simp [positiveRayLogMeasure]

/-- Identify the two Lebesgue L² realizations when their ray measures are equal. -/
def rayLpCongrMeasure {μ₁ μ₂ : Measure ℝ} (h : μ₁ = μ₂) : Lp ℂ 2 μ₁ ≃ₗᵢ[ℂ] Lp ℂ 2 μ₂ := by
  subst μ₂
  exact LinearIsometryEquiv.refl ℂ _

/-- The Lebesgue positive-ray Hilbert space in the actual arithmetic quotient at order zero. -/
def orderZeroHalfTwist : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))) ≃ₗᵢ[ℂ] H(0) :=
  (rayLpCongrMeasure positiveRayLogMeasure_zero.symm).trans (positiveRayQuotientEquiv 0)

set_option maxHeartbeats 1800000 in
/-- The order-zero isometry is the existing weighted half-twist after equating the ray measures. -/
theorem orderZeroHalfTwist_apply (u : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    orderZeroHalfTwist u = positiveRayToQuotientLp 0 (rayLpCongrMeasure positiveRayLogMeasure_zero.symm u) :=
  (LinearIsometryEquiv.trans_apply _ _ u).trans (positiveRayQuotientEquiv_apply 0 _)

/-- Equal ray measures transport an L² class without changing any measurable representative. -/
theorem rayLpCongrMeasure_coeFn_of_ae_eq {μ₁ μ₂ : Measure ℝ} (h : μ₁ = μ₂) (u : Lp ℂ 2 μ₁)
    {f : ℝ → ℂ} (hf : (u : ℝ → ℂ) =ᵐ[μ₁] f) : (rayLpCongrMeasure h u : ℝ → ℂ) =ᵐ[μ₂] f := by
  subst μ₂
  exact hf

/-- The arithmetic representative of the half-twist at order zero. -/
theorem orderZeroHalfTwist_coeFn_of_ae_eq (u : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ))))
    (f : ℝ → ℂ) (hf : Measurable f) (huf : (u : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] f) :
    (orderZeroHalfTwist u : J → ℂ) =ᵐ[ν(0)] quotientHalfTwistFun f := by
  rw [orderZeroHalfTwist_apply]
  exact positiveRayToQuotientLp_coeFn_of_ae_eq 0 _ f hf
    (rayLpCongrMeasure_coeFn_of_ae_eq positiveRayLogMeasure_zero.symm u huf)

end RiemannMasullo.AnnularBand
