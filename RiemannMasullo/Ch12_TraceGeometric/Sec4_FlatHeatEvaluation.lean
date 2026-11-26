module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatLogHeat
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Continuous evaluations of positive-ray logarithmic heat

On the positive ray a Gaussian-smoothed vector has a distinguished continuous
representative. The point evaluation is the inner product with a moving Gaussian
in the positive-ray Lebesgue normalization.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ComplexConjugate ComplexInnerProductSpace ENNReal NNReal Topology

@[expose] public noncomputable section

namespace RiemannMasullo.FlatPolar

local notation "ν" => volume.restrict (Ioi (0 : ℝ))
local notation "H" => Lp ℂ 2 ν

private def rayOrbit (f : H) (p : ℝ × ℝ) : ℂ :=
  (Real.sqrt (Real.exp p.1) : ℂ) * f (Real.exp p.1 * p.2)

private theorem measurable_rayOrbit (f : H) : Measurable (rayOrbit f) :=
  ((Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable).comp
    (Real.measurable_exp.comp measurable_fst)).mul
    ((Lp.stronglyMeasurable f).measurable.comp ((Real.measurable_exp.comp measurable_fst).mul measurable_snd))

private theorem rayOrbit_ae (f : H) (t : ℝ) :
    (logDilation t f : ℝ → ℂ) =ᵐ[ν] (fun x ↦ rayOrbit f (t, x)) :=
  positiveRayDilation_apply _ _ _

/-- The scalar Gaussian average of the normalized dilations, evaluated on the
chosen measurable representative. At positive variance its value on the
positive ray depends only on the `L²` class. -/
def heatRepresentative (τ : ℝ≥0) (f : H) (x : ℝ) : ℂ :=
  ∫ t, (Real.sqrt (Real.exp t) : ℂ) * f (Real.exp t * x) ∂gaussianReal 0 τ

private theorem integrable_rayOrbit_restrict (τ : ℝ≥0) (f : H) (s : Set ℝ)
    (hs : ν s < ∞) : Integrable (rayOrbit f) ((gaussianReal 0 τ).prod ((ν).restrict s)) := by
  let μ := gaussianReal 0 τ
  have hmeas := measurable_rayOrbit f
  have hsq (t : ℝ) : Integrable (fun x ↦ ‖rayOrbit f (t, x)‖ ^ 2) ν := by
    have hd := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (logDilation t f))).mp
      (Lp.memLp (logDilation t f))
    exact hd.congr ((rayOrbit_ae f t).mono fun _ hx ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hx)
  have hi (t : ℝ) : (∫ x, ‖rayOrbit f (t, x)‖ ^ 2 ∂ν) = ‖f‖ ^ 2 := by
    rw [← (logDilation t).norm_map f, ← L2.integral_sq_norm (𝕜 := ℂ)]
    exact integral_congr_ae ((rayOrbit_ae f t).mono fun _ hx ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hx.symm)
  have hprod : Integrable (fun p ↦ ‖rayOrbit f p‖ ^ 2) (μ.prod ν) := by
    apply (integrable_prod_iff (hmeas.norm.pow_const 2).aestronglyMeasurable).mpr
    refine ⟨.of_forall hsq, (integrable_const (‖f‖ ^ 2)).congr (.of_forall fun t ↦ ?_)⟩
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using (hi t).symm
  have : IsFiniteMeasure ((ν).restrict s) := isFiniteMeasure_restrict.mpr hs.ne
  have hres := hprod.mono_measure (Measure.prod_mono le_rfl (Measure.restrict_le_self (s := s)))
  apply ((integrable_const (1 : ℝ)).add hres).mono' hmeas.aestronglyMeasurable
  refine .of_forall fun p ↦ ?_
  change ‖rayOrbit f p‖ ≤ 1 + ‖rayOrbit f p‖ ^ 2
  nlinarith [sq_nonneg (‖rayOrbit f p‖ - 1 / 2)]

/-- The scalar heat representative represents the Hilbert-space Bochner average.
The verification compares finite-set integrals and uses square-integrability on the full ray. -/
theorem logHeat_ae_eq_heatRepresentative (τ : ℝ≥0) (f : H) :
    ⇑(logHeat τ f) =ᵐ[ν] heatRepresentative τ f := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · exact fun _ _ hs ↦ integrableOn_Lp_of_measure_ne_top _ fact_one_le_two_ennreal.elim hs.ne
  · exact fun s _ hs ↦ (integrable_rayOrbit_restrict τ f s hs).integral_prod_right
  · intro s hs hf
    have hi : Integrable (fun t ↦ logDilation t f) (gaussianReal 0 τ) :=
      Integrable.of_bound (continuous_logDilation f).aestronglyMeasurable ‖f‖
        (.of_forall fun t ↦ ((logDilation t).norm_map f).le)
    rw [← L2.inner_indicatorConstLp_one hs hf.ne, logHeat_apply, ← integral_inner hi]
    calc
      _ = ∫ t, ∫ x in s, rayOrbit f (t, x) ∂ν ∂gaussianReal 0 τ := by
        apply integral_congr_ae
        refine .of_forall fun t ↦ ?_
        change ⟪indicatorConstLp 2 hs hf.ne (1 : ℂ), logDilation t f⟫ = _
        rw [L2.inner_indicatorConstLp_one]
        exact integral_congr_ae (ae_restrict_of_ae (rayOrbit_ae f t))
      _ = _ := integral_integral_swap (integrable_rayOrbit_restrict τ f s hf)

/-- The Gaussian kernel at radius one, in positive-ray Lebesgue normalization. -/
def rayGaussianProfile (τ : ℝ≥0) (u : ℝ) : ℂ :=
  ((gaussianPDFReal 0 τ (Real.log u) / Real.sqrt u : ℝ) : ℂ)

private theorem rayGaussianProfile_sq_exp (τ : ℝ≥0) (t : ℝ) :
    (gaussianPDFReal 0 τ t) ^ 2 =
      Real.exp t • ‖rayGaussianProfile τ (Real.exp t)‖ ^ 2 := by
  simp only [rayGaussianProfile, Real.log_exp, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, div_pow, Real.sq_sqrt (Real.exp_pos t).le, smul_eq_mul]
  field_simp

/-- The Gaussian evaluation profile is square-integrable on the positive ray. -/
theorem rayGaussianProfile_memLp (τ : ℝ≥0) : MemLp (rayGaussianProfile τ) 2 ν := by
  let A := (Real.sqrt (2 * Real.pi * τ))⁻¹
  have hg (t : ℝ) : gaussianPDFReal 0 τ t ≤ A := by
    rw [gaussianPDFReal]
    change A * Real.exp (-(t - 0) ^ 2 / (2 * τ)) ≤ A
    calc
      _ ≤ A * 1 := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
        apply Real.exp_le_one_iff.mpr
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
          (mul_nonneg (by norm_num) τ.coe_nonneg)
      _ = _ := mul_one _
  have hi : Integrable (fun t ↦ (gaussianPDFReal 0 τ t) ^ 2) := by
    apply ((integrable_gaussianPDFReal 0 τ).const_mul A).mono'
      ((measurable_gaussianPDFReal 0 τ).pow_const 2).aestronglyMeasurable
    refine .of_forall fun t ↦ ?_
    rw [Real.norm_of_nonneg (sq_nonneg _), pow_two]
    exact mul_le_mul_of_nonneg_right (hg t) (gaussianPDFReal_nonneg _ _ _)
  have hm : Measurable (rayGaussianProfile τ) :=
    Complex.measurable_ofReal.comp (((measurable_gaussianPDFReal 0 τ).comp Real.measurable_log).div
      Real.continuous_sqrt.measurable)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (integrable_comp_exp _).mp
  exact hi.congr (.of_forall (rayGaussianProfile_sq_exp τ))

/-- The `L²((0,∞),du)` vector that represents evaluation of the heat at radius one.
The Jacobian contributes `1/√u` to its profile. -/
def heatEvaluationVector (τ : ℝ≥0) : H :=
  (rayGaussianProfile_memLp τ).toLp (rayGaussianProfile τ)

/-- The squared norm of evaluation at radius one is the squared Gaussian density
integral `1/(2√(πτ))`. -/
theorem norm_heatEvaluationVector_sq {τ : ℝ≥0} (hτ : 0 < τ) :
    ‖heatEvaluationVector τ‖ ^ 2 = (2 * Real.sqrt (Real.pi * τ))⁻¹ := by
  let A := (Real.sqrt (2 * Real.pi * τ))⁻¹
  have hτ' : (0 : ℝ) < τ := hτ
  have hscale (t : ℝ) : (gaussianPDFReal 0 τ t) ^ 2 =
      A ^ 2 * Real.exp (-(τ : ℝ)⁻¹ * t ^ 2) := by
    rw [gaussianPDFReal, mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    field_simp
    ring
  calc
    _ = ∫ u in Ioi 0, ‖rayGaussianProfile τ u‖ ^ 2 := by
      rw [← L2.integral_sq_norm (𝕜 := ℂ)]
      exact integral_congr_ae ((rayGaussianProfile_memLp τ).coeFn_toLp.mono
        fun _ hu ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hu)
    _ = ∫ t : ℝ, (gaussianPDFReal 0 τ t) ^ 2 := by
      rw [← integral_comp_exp]
      exact integral_congr_ae (.of_forall fun t ↦ (rayGaussianProfile_sq_exp τ t).symm)
    _ = A ^ 2 * Real.sqrt (Real.pi / (τ : ℝ)⁻¹) := by
      simp_rw [hscale]
      rw [integral_const_mul, integral_gaussian]
    _ = _ := by
      have hp : 0 < Real.pi * (τ : ℝ) := mul_pos Real.pi_pos hτ'
      rw [div_inv_eq_mul, show A ^ 2 = (2 * (Real.pi * τ))⁻¹ by
        dsimp only [A]
        rw [inv_pow, Real.sq_sqrt (by positivity), mul_assoc]]
      have hs := Real.sq_sqrt hp.le
      field_simp
      nlinarith

/-- The evaluation at a positive radius is an inner product with a normalized dilation
of the input. -/
theorem heatRepresentative_eq_inner {τ : ℝ≥0} (hτ : 0 < τ) (f : H) {x : ℝ} (hx : 0 < x) :
    heatRepresentative τ f x =
      (Real.sqrt x : ℂ)⁻¹ * ⟪heatEvaluationVector τ, positiveRayDilation x hx f⟫ := by
  have hk : ⟪heatEvaluationVector τ, positiveRayDilation x hx f⟫ =
      ∫ u in Ioi 0, rayGaussianProfile τ u * ((Real.sqrt x : ℂ) * f (x * u)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(rayGaussianProfile_memLp τ).coeFn_toLp,
      positiveRayDilation_apply x hx f] with u hu hD
    change heatEvaluationVector τ u = rayGaussianProfile τ u at hu
    rw [RCLike.inner_apply', hu, hD]
    simp [rayGaussianProfile]
  rw [hk, ← integral_const_mul, ← integral_comp_exp, heatRepresentative,
    integral_gaussianReal_eq_integral_smul hτ.ne']
  apply integral_congr_ae
  refine .of_forall fun t ↦ ?_
  simp only [rayGaussianProfile, Real.log_exp, Complex.real_smul, Complex.ofReal_div]
  have hx' : (Real.sqrt x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
  have ht' : (Real.sqrt (Real.exp t) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (Real.exp_pos t)).ne'
  have ht : (Real.sqrt (Real.exp t) : ℂ) ^ 2 = Real.exp t := by
    exact_mod_cast Real.sq_sqrt (Real.exp_pos t).le
  rw [mul_comm x (Real.exp t)]
  field_simp [hx', ht']
  linear_combination (gaussianPDFReal 0 τ t : ℂ) * f (Real.exp t * x) * ht

/-- Evaluation of smoothed profiles at a fixed positive radius is a bounded complex-linear
functional on the original Hilbert space. -/
def heatEvaluationCLM (τ : ℝ≥0) (x : Ioi (0 : ℝ)) : H →L[ℂ] ℂ :=
  (Real.sqrt (x : ℝ) : ℂ)⁻¹ •
    (innerSL ℂ (heatEvaluationVector τ)).comp (positiveRayDilation x.1 x.2 : H →L[ℂ] H)

/-- The functional gives the canonical representative at the chosen radius. -/
theorem heatEvaluationCLM_apply {τ : ℝ≥0} (hτ : 0 < τ) (x : Ioi (0 : ℝ)) (f : H) :
    heatEvaluationCLM τ x f = heatRepresentative τ f x :=
  (heatRepresentative_eq_inner hτ f x.2).symm

/-- Point evaluation is continuous in the positive radius and the input vector jointly. -/
theorem continuous_heatRepresentative {τ : ℝ≥0} (hτ : 0 < τ) :
    Continuous (fun p : Ioi (0 : ℝ) × H ↦ heatRepresentative τ p.2 p.1) := by
  let k := heatEvaluationVector τ
  have hmove (x : Ioi (0 : ℝ)) (f : H) :
      ⟪k, positiveRayDilation x.1 x.2 f⟫ = ⟪logDilation (-Real.log x.1) k, f⟫ := by
    have hleft : logDilation (Real.log x.1) (logDilation (-Real.log x.1) k) = k := by
      rw [logDilation_add, add_neg_cancel, logDilation_zero]
    have hright : logDilation (Real.log x.1) f = positiveRayDilation x.1 x.2 f := by
      simp only [logDilation, Real.exp_log x.2]
    exact (by simpa only [hleft, hright] using
      (logDilation (Real.log x.1)).inner_map_map (logDilation (-Real.log x.1) k) f)
  have hcoef : Continuous (fun x : Ioi (0 : ℝ) ↦ (Real.sqrt (x : ℝ) : ℂ)⁻¹) :=
    (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_subtype_val)).inv₀
      (fun x ↦ Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr x.2).ne')
  have hc := (continuous_logDilation k).comp Real.continuous_log'.neg
  exact ((hcoef.comp continuous_fst).mul ((hc.comp continuous_fst).inner continuous_snd)).congr
    (fun p ↦ by
      rw [heatRepresentative_eq_inner hτ p.2 p.1.2, hmove]
      rfl)

/-- The canonical representative is continuous on the open positive ray. -/
theorem continuousOn_heatRepresentative {τ : ℝ≥0} (hτ : 0 < τ) (f : H) :
    ContinuousOn (heatRepresentative τ f) (Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact (continuous_heatRepresentative hτ).comp (continuous_id.prodMk continuous_const)

/-- A continuous representative of this Hilbert-space vector agrees pointwise with the
Gaussian representative at every positive radius. -/
theorem eqOn_heatRepresentative {τ : ℝ≥0} (hτ : 0 < τ) (f : H) {q : ℝ → ℂ}
    (hq : ContinuousOn q (Ioi 0)) (heq : ⇑(logHeat τ f) =ᵐ[ν] q) :
    EqOn q (heatRepresentative τ f) (Ioi 0) :=
  Measure.eqOn_open_of_ae_eq (heq.symm.trans (logHeat_ae_eq_heatRepresentative τ f))
    isOpen_Ioi hq (continuousOn_heatRepresentative hτ f)

/-- The norm of the point evaluation is at most its radius-one norm divided by `√x`. -/
theorem norm_heatRepresentative_le {τ : ℝ≥0} (hτ : 0 < τ) (f : H) {x : ℝ} (hx : 0 < x) :
    ‖heatRepresentative τ f x‖ ≤ (Real.sqrt x)⁻¹ * ‖heatEvaluationVector τ‖ * ‖f‖ := by
  rw [heatRepresentative_eq_inner hτ f hx, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_assoc]
  exact mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans_eq
    (by rw [LinearIsometryEquiv.norm_map])) (inv_nonneg.mpr (Real.sqrt_nonneg _))

end RiemannMasullo.FlatPolar
