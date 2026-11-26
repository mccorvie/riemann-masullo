module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatPolar
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Logarithmic heat on the flat positive ray

In the real even model for Step III of Theorem 12.4.1.1, pp. 515–517,
the positive-ray frequency profile uses Lebesgue measure and the unitary dilation
carries its square-root Jacobian. We realize the Gaussian heat regularization
proposed in the discussion of #7354 as a strong average of these same unitaries.
Its exact matrix coefficient and squared error on the polar band are independent
of the positive band endpoint.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ComplexConjugate ComplexInnerProductSpace NNReal Topology

@[expose] public noncomputable section

namespace RiemannMasullo.FlatPolar

local notation "ν" => volume.restrict (Ioi (0 : ℝ))
local notation "H" => Lp ℂ 2 ν

/-- The logarithmic translation by `t` in the unitary positive-ray chart. -/
def logDilation (t : ℝ) : H ≃ₗᵢ[ℂ] H :=
  positiveRayDilation (Real.exp t) (Real.exp_pos t)

/-- Logarithmic unitary orbits are continuous in the translation parameter. -/
theorem continuous_logDilation (f : H) : Continuous (fun t ↦ logDilation t f) :=
  (positiveRayDilation_continuous f).comp (Real.continuous_exp.subtype_mk Real.exp_pos)

/-- Zero logarithmic translation fixes every vector. -/
theorem logDilation_zero (f : H) : logDilation 0 f = f := by
  apply Lp.ext
  simpa [logDilation] using positiveRayDilation_apply (Real.exp 0) (Real.exp_pos 0) f

/-- Composition of the physical normalized dilations adds logarithmic shifts. -/
theorem logDilation_add (s t : ℝ) (f : H) :
    logDilation s (logDilation t f) = logDilation (s + t) f := by
  apply Lp.ext
  filter_upwards [positiveRayDilation_apply (Real.exp s) (Real.exp_pos s) (logDilation t f),
    (positiveRayScale_quasiMeasurePreserving (Real.exp s) (Real.exp_pos s)).ae_eq_comp
      (positiveRayDilation_apply (Real.exp t) (Real.exp_pos t) f),
    positiveRayDilation_apply (Real.exp (s + t)) (Real.exp_pos _) f] with x hs ht hst
  change logDilation t f (Real.exp s * x) =
    (Real.sqrt (Real.exp t) : ℂ) * f (Real.exp t * (Real.exp s * x)) at ht
  change logDilation s (logDilation t f) x = _ at hs
  change logDilation (s + t) f x = _ at hst
  rw [hs, ht, hst, Real.exp_add, Real.sqrt_mul (Real.exp_pos s).le, Complex.ofReal_mul,
    ← mul_assoc]
  congr 2
  ring

private theorem integrable_logDilation (τ : ℝ≥0) (f : H) :
    Integrable (fun t ↦ logDilation t f) (gaussianReal 0 τ) :=
  Integrable.of_bound (continuous_logDilation f).aestronglyMeasurable ‖f‖
    (.of_forall fun t ↦ ((logDilation t).norm_map f).le)

/-- The heat operator at variance `τ` is the strong Gaussian average of the actual
positive-ray unitary dilations. Under the logarithmic Haar chart its time is `τ/2`
for the generator `∂²`. -/
def logHeat (τ : ℝ≥0) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ∫ t, logDilation t f ∂gaussianReal 0 τ
      map_add' := fun f g ↦ by
        simp only [map_add]
        exact integral_add (integrable_logDilation τ f) (integrable_logDilation τ g)
      map_smul' := fun c f ↦ by simp only [map_smul, RingHom.id_apply, integral_smul] }
    1 (fun f ↦ by
      change ‖∫ t, logDilation t f ∂gaussianReal 0 τ‖ ≤ 1 * ‖f‖
      simpa only [one_mul, probReal_univ, mul_one] using
        (norm_integral_le_of_norm_le_const (μ := gaussianReal 0 τ)
          (.of_forall fun t ↦ ((logDilation t).norm_map f).le)))

/-- The Bochner-integral formula for the heat contraction. -/
theorem logHeat_apply (τ : ℝ≥0) (f : H) :
    logHeat τ f = ∫ t, logDilation t f ∂gaussianReal 0 τ := rfl

/-- The heat average has operator norm at most one for all nonnegative times. -/
theorem norm_logHeat_le_one (τ : ℝ≥0) : ‖logHeat τ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul, logHeat_apply]
  simpa only [probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := gaussianReal 0 τ)
      (.of_forall fun t ↦ ((logDilation t).norm_map f).le))

/-- Symmetry of the Gaussian turns integration of dilations into a selfadjoint operator. -/
theorem isSelfAdjoint_logHeat (τ : ℝ≥0) : IsSelfAdjoint (logHeat τ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change ⟪logHeat τ f, g⟫ = ⟪f, logHeat τ g⟫
  rw [logHeat_apply, logHeat_apply, ← integral_inner (integrable_logDilation τ g)]
  calc
    _ = ∫ t, ⟪logDilation t f, g⟫ ∂gaussianReal 0 τ := by
      rw [← inner_conj_symm]
      simp_rw [← inner_conj_symm (logDilation _ f) g]
      rw [integral_conj, integral_inner (integrable_logDilation τ f)]
    _ = ∫ t, ⟪f, logDilation (-t) g⟫ ∂gaussianReal 0 τ := by
      apply integral_congr_ae
      filter_upwards with t
      have h : logDilation t (logDilation (-t) g) = g := by
        rw [logDilation_add, add_neg_cancel, logDilation_zero]
      simpa only [h] using ((logDilation t).inner_map_map f (logDilation (-t) g))
    _ = _ := by
      have he : (gaussianReal 0 τ).map (fun t : ℝ ↦ -t) = gaussianReal 0 τ := by
        simpa using gaussianReal_map_neg (μ := 0) (v := τ)
      have hc : Continuous (fun t ↦ ⟪f, logDilation t g⟫) :=
        continuous_const.inner (continuous_logDilation g)
      rw [← integral_map measurable_neg.aemeasurable hc.aestronglyMeasurable, he]

/-- The probability law at variance `τ` is the push-forward of the standard normal
under multiplication by `√τ`. -/
theorem logHeat_apply_standardGaussian (τ : ℝ≥0) (f : H) :
    logHeat τ f = ∫ t : ℝ, logDilation (Real.sqrt τ * t) f ∂gaussianReal 0 1 := by
  have hv : NNReal.mk ((Real.sqrt (τ : ℝ)) ^ 2) (sq_nonneg _) = τ :=
    Subtype.ext (Real.sq_sqrt τ.coe_nonneg)
  have hm := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt τ)
  rw [mul_zero, mul_one, hv] at hm
  rw [logHeat_apply, ← hm, integral_map (measurable_const_mul _).aemeasurable
    (continuous_logDilation f).aestronglyMeasurable]

/-- The heat contracts strongly to the identity on the whole positive-ray Hilbert space. -/
theorem tendsto_logHeat_zero (f : H) :
    Tendsto (fun τ : ℝ≥0 ↦ logHeat τ f) (𝓝 0) (𝓝 f) := by
  have h : Tendsto (fun τ : ℝ≥0 ↦ ∫ t, logDilation (Real.sqrt τ * t) f ∂gaussianReal 0 1)
      (𝓝 0) (𝓝 (∫ _ : ℝ, f ∂gaussianReal 0 1)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ ‖f‖) ?_ ?_
      (integrable_const _) ?_
    · exact .of_forall fun τ ↦
        ((continuous_logDilation f).comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    · exact .of_forall fun _ ↦ .of_forall fun t ↦ ((logDilation _).norm_map f).le
    · refine .of_forall fun t ↦ ?_
      have hc : Continuous (fun τ : ℝ≥0 ↦ logDilation (Real.sqrt τ * t) f) :=
        (continuous_logDilation f).comp ((Real.continuous_sqrt.comp NNReal.continuous_coe).mul_const t)
      simpa only [NNReal.coe_zero, Real.sqrt_zero, zero_mul, logDilation_zero] using hc.tendsto 0
  simpa only [← logHeat_apply_standardGaussian, integral_const, probReal_univ, one_smul] using h

/-- Gaussian convolution gives the exact heat semigroup law on positive-ray L². -/
theorem logHeat_add (σ τ : ℝ≥0) (f : H) : logHeat (σ + τ) f = logHeat σ (logHeat τ f) := by
  let μ := gaussianReal 0 σ
  let μ' := gaussianReal 0 τ
  have hc : (μ.prod μ').map (fun u : ℝ × ℝ ↦ u.1 + u.2) = gaussianReal 0 (σ + τ) := by
    simpa only [μ, μ', zero_add, Measure.conv] using
      (gaussianReal_conv_gaussianReal (m₁ := 0) (m₂ := 0) (v₁ := σ) (v₂ := τ))
  have hi : Integrable (fun u : ℝ × ℝ ↦ logDilation (u.1 + u.2) f) (μ.prod μ') :=
    Integrable.of_bound ((continuous_logDilation f).comp continuous_add).aestronglyMeasurable
      ‖f‖ (.of_forall fun _ ↦ ((logDilation _).norm_map f).le)
  rw [logHeat_apply, ← hc, integral_map continuous_add.measurable.aemeasurable
    (continuous_logDilation f).aestronglyMeasurable, integral_prod _ hi, logHeat_apply]
  apply integral_congr_ae
  filter_upwards with s
  rw [logHeat_apply]
  change _ = (logDilation s).toContinuousLinearEquiv.toContinuousLinearMap (∫ t, logDilation t f ∂μ')
  rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_logDilation τ f)]
  apply integral_congr_ae
  exact .of_forall fun t ↦ (logDilation_add s t f).symm

/-- The normalized band matrix coefficient depends only on the logarithmic shift. -/
theorem inner_bandVector_logDilation (t : ℝ) {B : ℝ} (hB : 0 < B) :
    ⟪bandVector B, logDilation t (bandVector B)⟫ = (Real.exp (-|t| / 2) : ℂ) := by
  have hb (x : ℝ) : ‖(1 : ℂ)‖ ≤ (1 : ℝ) := by simp
  let M := positiveRayMultiplier (fun _ : ℝ ↦ (1 : ℂ)) measurable_const 1 zero_le_one hb B
  have hM : M (bandVector B) = bandVector B := by
    apply Lp.ext
    simpa only [one_mul] using
      positiveRayMultiplier_apply (fun _ : ℝ ↦ (1 : ℂ)) measurable_const 1 zero_le_one hb B (bandVector B)
  have h := inner_bandVector_dilation_multiplier (fun _ : ℝ ↦ (1 : ℂ)) measurable_const
    1 zero_le_one hb (Real.exp_pos t) hB
  change ⟪bandVector B, logDilation t (M (bandVector B))⟫ = _ at h
  rw [hM, setIntegral_const, Real.volume_real_Ioc_of_le (le_min zero_le_one (Real.exp_pos t).le),
    sub_zero, Complex.real_smul, mul_one, ← Real.exp_half] at h
  rw [h, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [← Real.exp_neg]
  by_cases ht : 0 ≤ t
  · rw [min_eq_left (Real.one_le_exp ht), mul_one, abs_of_nonneg ht]
    congr 1
    ring
  · have htle := le_of_not_ge ht
    rw [min_eq_right (Real.exp_le_one_iff.mpr htle), ← Real.exp_add, abs_of_nonpos htle]
    congr 1
    ring

/-- The exact heat-regularized matrix coefficient of the normalized band is
independent of its endpoint. -/
theorem inner_bandVector_logHeat (τ : ℝ≥0) {B : ℝ} (hB : 0 < B) :
    ⟪bandVector B, logHeat τ (bandVector B)⟫ =
      Complex.ofReal (∫ t : ℝ, Real.exp (-|t| / 2) ∂gaussianReal 0 τ) := by
  rw [logHeat_apply, ← integral_inner (integrable_logDilation τ (bandVector B))]
  simp_rw [inner_bandVector_logDilation _ hB]
  exact integral_complex_ofReal

/-- The exact squared error is also independent of the band. Its norm-square
term involves the Gaussian at twice the variance by selfadjointness and the semigroup law. -/
theorem norm_logHeat_sub_bandVector_sq_eq (τ : ℝ≥0) {B : ℝ} (hB : 0 < B) :
    ‖logHeat τ (bandVector B) - bandVector B‖ ^ 2 =
      1 - 2 * (∫ t : ℝ, Real.exp (-|t| / 2) ∂gaussianReal 0 τ) +
        ∫ t : ℝ, Real.exp (-|t| / 2) ∂gaussianReal 0 (τ + τ) := by
  let e := bandVector B
  have hpair (s : ℝ≥0) : RCLike.re ⟪e, logHeat s e⟫ =
      ∫ t : ℝ, Real.exp (-|t| / 2) ∂gaussianReal 0 s := by
    rw [inner_bandVector_logHeat s hB]
    rfl
  have hsq : ‖logHeat τ e‖ ^ 2 = ∫ t : ℝ, Real.exp (-|t| / 2) ∂gaussianReal 0 (τ + τ) := by
    calc
      _ = RCLike.re ⟪logHeat τ e, logHeat τ e⟫ := (inner_self_eq_norm_sq _).symm
      _ = RCLike.re ⟪e, logHeat τ (logHeat τ e)⟫ :=
        congrArg RCLike.re ((isSelfAdjoint_logHeat τ).isSymmetric e (logHeat τ e))
      _ = _ := by rw [← logHeat_add, hpair]
  change ‖logHeat τ e - e‖ ^ 2 = _
  rw [norm_sub_sq (𝕜 := ℂ), hsq, inner_re_symm, hpair, norm_bandVector hB]
  ring

private theorem gaussian_integral_abs_le_sqrt (τ : ℝ≥0) :
    (∫ t : ℝ, |t| ∂gaussianReal 0 τ) ≤ Real.sqrt τ := by
  let μ := gaussianReal 0 τ
  have h₂ : MemLp id 2 μ := memLp_id_gaussianReal 2
  have habs : MemLp (fun t : ℝ ↦ |t|) 2 μ := by
    simpa only [Function.comp_def, id_eq, Real.norm_eq_abs] using h₂.norm
  have hmoment : (∫ t : ℝ, t ^ 2 ∂μ) = τ := by
    have hv := variance_eq_integral (μ := μ) measurable_id'.aemeasurable
    rw [variance_fun_id_gaussianReal] at hv
    simpa [μ] using hv.symm
  have hv := variance_nonneg (fun t : ℝ ↦ |t|) μ
  rw [variance_eq_sub habs] at hv
  simp only [Pi.pow_apply, sq_abs, hmoment] at hv
  exact le_of_sq_le_sq (by linarith [Real.sq_sqrt τ.coe_nonneg]) (Real.sqrt_nonneg _)

/-- At variance `τ`, the squared norm of the smoothing error on the literal
normalized band is at most `√τ`, uniformly over all positive band endpoints. -/
theorem norm_logHeat_sub_bandVector_sq_le (τ : ℝ≥0) {B : ℝ} (hB : 0 < B) :
    ‖logHeat τ (bandVector B) - bandVector B‖ ^ 2 ≤ Real.sqrt τ := by
  let μ := gaussianReal 0 τ
  let e := bandVector B
  let F (t : ℝ) := Real.exp (-|t| / 2)
  have he : ‖e‖ = 1 := norm_bandVector hB
  have hn : ‖logHeat τ e‖ ≤ 1 := by
    simpa only [he, mul_one] using ((logHeat τ).le_opNorm e).trans
      (mul_le_mul_of_nonneg_right (norm_logHeat_le_one τ) (norm_nonneg e))
  have hF (t : ℝ) : F t ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg t])
  have hFi : Integrable F μ := Integrable.of_bound (by fun_prop) 1
    (.of_forall fun t ↦ by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hF t)
  have hAi : Integrable (fun t : ℝ ↦ |t|) μ := by
    simpa only [id_eq, Real.norm_eq_abs] using
      ((memLp_id_gaussianReal (μ := 0) (v := τ) 1).integrable le_rfl).norm
  have hle : ∫ t : ℝ, 2 - 2 * F t ∂μ ≤ ∫ t : ℝ, |t| ∂μ := by
    apply integral_mono ((integrable_const 2).sub (hFi.const_mul 2)) hAi
    intro t
    change 2 - 2 * Real.exp (-|t| / 2) ≤ |t|
    linarith [Real.add_one_le_exp (-|t| / 2)]
  rw [integral_sub (integrable_const 2) (hFi.const_mul 2), integral_const_mul] at hle
  simp only [integral_const, probReal_univ, one_smul] at hle
  have hinner : RCLike.re ⟪logHeat τ e, e⟫ = ∫ t : ℝ, F t ∂μ := by
    rw [inner_re_symm, inner_bandVector_logHeat τ hB]
    rfl
  rw [norm_sub_sq (𝕜 := ℂ), he, hinner]
  have h₁ : ‖logHeat τ e‖ ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ (norm_nonneg _) zero_le_one).mpr hn
  linarith [gaussian_integral_abs_le_sqrt τ]

/-- The positive bands may vary arbitrarily as the heat variance shrinks. -/
theorem tendsto_logHeat_sub_bandVector {ι : Type*} {l : Filter ι} {τ : ι → ℝ≥0}
    (hτ : Tendsto τ l (𝓝 0)) (B : ι → ℝ) (hB : ∀ i, 0 < B i) :
    Tendsto (fun i ↦ ‖logHeat (τ i) (bandVector (B i)) - bandVector (B i)‖) l (𝓝 0) := by
  have ht : Tendsto (fun i ↦ Real.sqrt (Real.sqrt (τ i : ℝ))) l (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.continuousAt.tendsto.comp
      (Real.continuous_sqrt.continuousAt.tendsto.comp (NNReal.continuous_coe.continuousAt.tendsto.comp hτ)))
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ (Real.le_sqrt (norm_nonneg _)
    (Real.sqrt_nonneg _)).mpr (norm_logHeat_sub_bandVector_sq_le (τ i) (hB i))) ht

end RiemannMasullo.FlatPolar
