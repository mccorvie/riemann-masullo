module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.HilbertWeightInterpolation
public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.RadiusSixBessel

/-! # Fractional Bessel multipliers from one compatible pair of endpoints -/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace RiemannMasullo.WeakCardinal

private def besselLog (x : ℝ) : ℝ := Real.log (1+x^2)
private theorem continuous_besselLog : Continuous besselLog :=
  (continuous_const.add (continuous_id.pow 2)).log fun x ↦ by dsimp; positivity

private theorem besselLog_nonneg (x : ℝ) : 0 ≤ besselLog x :=
  Real.log_nonneg (by nlinarith [sq_nonneg x])

private def halfWeight (r x : ℝ) : ℝ := Real.exp ((r/2) * besselLog x)
private theorem continuous_halfWeight (r : ℝ) : Continuous (halfWeight r) :=
  Real.continuous_exp.comp (continuous_const.mul continuous_besselLog)

private theorem halfWeight_sq (r x : ℝ) : (halfWeight r x)^2 = weight r x := by
  rw [halfWeight, weight, Real.rpow_def_of_pos (by positivity : 0 < 1+x^2),
    sq, ← Real.exp_add]
  unfold besselLog
  congr 1
  ring

private theorem continuous_besselWeight (r : ℝ) : Continuous (weight r) := by
  exact ((continuous_halfWeight r).pow 2).congr (halfWeight_sq r)

private theorem angularMeasure_le_sobolevMeasure {r : ℝ} (hr : 0 ≤ r) :
    angularMeasure ≤ sobolevMeasure r := by
  change angularMeasure ≤ angularMeasure.withDensity _
  calc
    _ = angularMeasure.withDensity 1 := withDensity_one.symm
    _ ≤ _ := withDensity_mono (.of_forall fun x ↦ by
      change 1 ≤ ENNReal.ofReal (weight r x)
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow (by nlinarith [sq_nonneg x]) hr))

/-- Forget the Bessel weight while retaining the actual angular-frequency representative. -/
@[no_expose] def besselToAngular (r : ℝ) (hr : 0 ≤ r) :
    Lp ℂ 2 (sobolevMeasure r) →L[ℂ] Lp ℂ 2 angularMeasure :=
  complexLpInclusionOfMeasureLE (angularMeasure_le_sobolevMeasure hr)

theorem besselToAngular_ae (r : ℝ) (hr : 0 ≤ r) (f : Lp ℂ 2 (sobolevMeasure r)) :
    (besselToAngular r hr f : ℝ → ℂ) =ᵐ[angularMeasure] f :=
  complexLpInclusionOfMeasureLE_coeFn _ _

theorem besselToAngular_injective (r : ℝ) (hr : 0 ≤ r) :
    Function.Injective (besselToAngular r hr) :=
  complexLpInclusionOfMeasureLE_injective _ (withDensity_absolutelyContinuous _ _)

private theorem halfWeight_norm_sq (r x : ℝ) (z : ℂ) :
    ‖(halfWeight r x : ℂ) * z‖^2 = ‖z‖^2 * weight r x := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (show 0 < halfWeight r x from Real.exp_pos _),
    mul_pow,halfWeight_sq, mul_comm]

private theorem memLp_halfWeight_iff (r : ℝ) (f : ℝ → ℂ) (hf : StronglyMeasurable f) :
    MemLp (fun x ↦ (halfWeight r x : ℂ) * f x) 2 angularMeasure ↔
    MemLp f 2 (sobolevMeasure r) := by
  have hm : StronglyMeasurable (fun x ↦ (halfWeight r x : ℂ) * f x) :=
    (Complex.continuous_ofReal.comp (continuous_halfWeight r)).stronglyMeasurable.mul hf
  rw [memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable,
    memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable, sobolevMeasure,
    integrable_withDensity_iff (continuous_besselWeight r).measurable.ennreal_ofReal
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  have hw (x : ℝ) : (ENNReal.ofReal (weight r x)).toReal = weight r x :=
    ENNReal.toReal_ofReal ((halfWeight_sq r x) ▸ sq_nonneg _)
  simp only [halfWeight_norm_sq, hw]

private theorem halfWeight_norm (r : ℝ) (u : Lp ℂ 2 (sobolevMeasure r))
    (j : Lp ℂ 2 angularMeasure) (hj : (j : ℝ → ℂ) =ᵐ[angularMeasure] fun x ↦
      (halfWeight r x : ℂ) * u x) : ‖j‖ = ‖u‖ := by
  have h : ‖j‖^2 = ‖u‖^2 := by
    rw [complexLp_norm_sq_integral j, norm_sq_eq_weightedIntegral r u _ .rfl]
    apply integral_congr_ae
    filter_upwards [hj] with x hx
    rw [hx,halfWeight_norm_sq,mul_comm]
  nlinarith [norm_nonneg j, norm_nonneg u, sq_nonneg (‖j‖-‖u‖)]

/-- The exact angular-frequency order-two graph bound for the standard Bessel weight. -/
def BesselEndpointBound (T : Lp ℂ 2 angularMeasure →L[ℂ] Lp ℂ 2 angularMeasure)
    (C : ℝ) : Prop :=
  ∀ f j : Lp ℂ 2 angularMeasure,
    (j : ℝ → ℂ) =ᵐ[angularMeasure] (fun ξ ↦ ((1+ξ^2 : ℝ) : ℂ) * f ξ) →
    ∃ k : Lp ℂ 2 angularMeasure,
      (k : ℝ → ℂ) =ᵐ[angularMeasure] (fun ξ ↦ ((1+ξ^2 : ℝ) : ℂ) * T f ξ) ∧ ‖k‖ ≤ C * ‖j‖

/-- An actual bounded multiplier at both endpoints induces an operator on the genuine
order-r angular Bessel Hilbert space with the same norm bound. The operator commutes with
forgetting the weight, so its action is the given unweighted Fourier operator. -/
theorem exists_besselMultiplier_of_endpoints (r : ℝ) (hr₀ : 0 ≤ r) (hr₂ : r ≤ 2)
    (T : Lp ℂ 2 angularMeasure →L[ℂ] Lp ℂ 2 angularMeasure) {C : ℝ} (hC : 0 ≤ C)
    (h₀ : ‖T‖ ≤ C) (h₂ : BesselEndpointBound T C) :
    ∃ A : Lp ℂ 2 (sobolevMeasure r) →L[ℂ] Lp ℂ 2 (sobolevMeasure r),
      ‖A‖ ≤ C ∧ ∀ f, besselToAngular r hr₀ (A f) = T (besselToAngular r hr₀ f) := by
  let J := besselToAngular r hr₀
  have hG : WeightGraphBound besselLog T C := by
    have hw (x : ℝ) : Real.exp (besselLog x) = 1+x^2 := Real.exp_log (by positivity)
    simpa only [WeightGraphBound, BesselEndpointBound, hw] using h₂
  have hI := interpolateWeightGraph continuous_besselLog besselLog_nonneg T hC h₀ hG
    (t := r/2) (show r/2 ∈ Icc (0:ℝ) 1 from ⟨by linarith, by linarith⟩)
  have lift (f : Lp ℂ 2 (sobolevMeasure r)) :
      ∃ v : Lp ℂ 2 (sobolevMeasure r), J v = T (J f) ∧ ‖v‖ ≤ C * ‖f‖ := by
    have hmf := (memLp_halfWeight_iff r f (Lp.stronglyMeasurable f)).2 (Lp.memLp f)
    let j := hmf.toLp _
    have hj : (j : ℝ → ℂ) =ᵐ[angularMeasure] fun x ↦ (halfWeight r x : ℂ) * f x :=
      hmf.coeFn_toLp
    have haj := besselToAngular_ae r hr₀ f
    have hju : (j : ℝ → ℂ) =ᵐ[angularMeasure] fun x ↦ (halfWeight r x : ℂ) * J f x := by
      filter_upwards [hj,haj] with x h h'
      exact h.trans (congrArg _ h'.symm)
    obtain ⟨k,hk,hkn⟩ := hI (J f) j hju
    have hmoutW : MemLp (fun x ↦ (halfWeight r x : ℂ) * T (J f) x) 2 angularMeasure :=
      (memLp_congr_ae hk).mp (Lp.memLp k)
    have hmout := (memLp_halfWeight_iff r (T (J f)) (Lp.stronglyMeasurable _)).mp hmoutW
    let v := hmout.toLp (T (J f))
    have hv : (v : ℝ → ℂ) =ᵐ[angularMeasure] T (J f) :=
      ae_mono (angularMeasure_le_sobolevMeasure hr₀) hmout.coeFn_toLp
    refine ⟨v, Lp.ext ((besselToAngular_ae r hr₀ v).trans hv), ?_⟩
    have hkv : (k : ℝ → ℂ) =ᵐ[angularMeasure] fun x ↦ (halfWeight r x : ℂ) * v x := by
      filter_upwards [hk,hv] with x h h'
      exact h.trans (congrArg _ h'.symm)
    rw [← halfWeight_norm r v k hkv, ← halfWeight_norm r f j hj]
    exact hkn
  let Aₗ : Lp ℂ 2 (sobolevMeasure r) →ₗ[ℂ] Lp ℂ 2 (sobolevMeasure r) :=
    { toFun := fun f ↦ (lift f).choose
      map_add' := fun f g ↦ (besselToAngular_injective r hr₀) (by
        change J (lift (f+g)).choose = J ((lift f).choose + (lift g).choose)
        refine (lift (f+g)).choose_spec.1.trans ?_
        rw [J.map_add f g, T.map_add, J.map_add (lift f).choose (lift g).choose,
          (lift f).choose_spec.1, (lift g).choose_spec.1])
      map_smul' := fun c f ↦ (besselToAngular_injective r hr₀) (by
        change J (lift (c • f)).choose = J (c • (lift f).choose)
        refine (lift (c • f)).choose_spec.1.trans ?_
        rw [J.map_smul c f, T.map_smul, J.map_smul c (lift f).choose, (lift f).choose_spec.1]) }
  let A := Aₗ.mkContinuous C fun f ↦ (lift f).choose_spec.2
  exact ⟨A, A.opNorm_le_bound hC (fun f ↦ (lift f).choose_spec.2), fun f ↦ (lift f).choose_spec.1⟩

/-- The positive-phase inverse of a weighted vector agrees with its unweighted representative. -/
theorem integral_phase_besselToAngular (r : ℝ) (hr : 0 ≤ r) (f : Lp ℂ 2 (sobolevMeasure r)) (x : ℝ) :
    (∫ ξ, phase x ξ * besselToAngular r hr f ξ ∂angularMeasure) =
      ∫ ξ, phase x ξ * f ξ ∂angularMeasure :=
  integral_congr_ae ((besselToAngular_ae r hr f).mono fun ξ h ↦ congrArg (phase x ξ * ·) h)

/-- Above the evaluation threshold the Fourier representative is integrable in angular measure. -/
theorem integrable_besselToAngular (r : ℝ) (hr : 1/2 < r) (f : Lp ℂ 2 (sobolevMeasure r)) :
    Integrable (besselToAngular r (by linarith) f : ℝ → ℂ) angularMeasure := by
  have hi : Integrable (f : ℝ → ℂ) angularMeasure := by
    simpa [phase] using
      integrable_evaluation r hr 0 f
  exact hi.congr (besselToAngular_ae r _ f).symm

/-- A physical multiplication identity for angular L¹ Fourier representatives passes to
the pointwise inverse Fourier integrals of the interpolated Bessel operator. -/
theorem exists_besselPhysicalMultiplier_of_endpoints (r : ℝ) (hr : 1/2 < r) (hr₂ : r ≤ 2)
    (T : Lp ℂ 2 angularMeasure →L[ℂ] Lp ℂ 2 angularMeasure) (P : ℝ → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (h₀ : ‖T‖ ≤ C) (h₂ : BesselEndpointBound T C)
    (hP : ∀ f : Lp ℂ 2 angularMeasure, Integrable (f : ℝ → ℂ) angularMeasure →
      Integrable (T f : ℝ → ℂ) angularMeasure → ∀ x : ℝ,
        (∫ ξ, phase x ξ * T f ξ ∂angularMeasure) = P x * ∫ ξ, phase x ξ * f ξ ∂angularMeasure) :
    ∃ A : Lp ℂ 2 (sobolevMeasure r) →L[ℂ] Lp ℂ 2 (sobolevMeasure r), ‖A‖ ≤ C ∧
      ∀ (f : Lp ℂ 2 (sobolevMeasure r)) x,
        (∫ ξ, phase x ξ * A f ξ ∂angularMeasure) = P x * ∫ ξ, phase x ξ * f ξ ∂angularMeasure := by
  have hr₀ : 0 ≤ r := by linarith
  obtain ⟨A, hA, hJ⟩ := exists_besselMultiplier_of_endpoints r hr₀ hr₂ T hC h₀ h₂
  refine ⟨A,hA,fun f x ↦ ?_⟩
  have hin := integrable_besselToAngular r hr f
  have hout : Integrable (T (besselToAngular r hr₀ f) : ℝ → ℂ) angularMeasure :=
    hJ f ▸ integrable_besselToAngular r hr (A f)
  rw [← integral_phase_besselToAngular r hr₀ (A f) x, hJ, hP _ hin hout,
    integral_phase_besselToAngular]

end RiemannMasullo.WeakCardinal
