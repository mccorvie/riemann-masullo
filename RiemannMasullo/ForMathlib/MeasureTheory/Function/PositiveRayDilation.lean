module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space

/-!
# Unitary dilations on the positive ray

On positive-ray Lebesgue `L²`, the scaling `f(t) ↦ √a f(a t)` is unitary and depends
continuously on the positive ratio in the strong operator topology. A bounded measurable
profile `Q` defines multiplication by `Q(t / B)` on the same space.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

namespace RiemannMasullo.FlatPolar

local notation "ν" => (volume.restrict (Ioi (0 : ℝ)))
local notation "H" => Lp ℂ 2 ν

/-- Scaling the positive ray by a positive number pushes Lebesgue measure to its
reciprocal multiple. -/
theorem positiveRayScale_map (a : ℝ) (ha : 0 < a) :
    (ν).map (fun t ↦ a * t) = ENNReal.ofReal a⁻¹ • ν := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul a) hs,
    Measure.restrict_apply ((measurable_const_mul a) hs),
    smul_apply, Measure.restrict_apply hs]
  have hpre : ((fun t ↦ a * t) ⁻¹' s) ∩ Ioi 0 = (fun t ↦ a * t) ⁻¹' (s ∩ Ioi 0) := by
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_Ioi, mul_pos_iff_of_pos_left ha]
  rw [hpre, Real.volume_preimage_mul_left ha.ne', abs_of_pos (inv_pos.mpr ha)]
  rfl

/-- An almost-everywhere representative identity on the positive ray can be pulled back
along scaling by any positive number. -/
theorem positiveRayScale_quasiMeasurePreserving (a : ℝ) (ha : 0 < a) :
    QuasiMeasurePreserving (fun t : ℝ ↦ a * t) ν ν :=
  ⟨(measurable_const_mul a).aemeasurable, by rw [positiveRayScale_map a ha]; exact Measure.smul_absolutelyContinuous⟩

private theorem exists_dilationIsometry (a : ℝ) (ha : 0 < a) :
    ∃ T : H →ₗᵢ[ℂ] H, ∀ f : H, (T f : ℝ → ℂ) =ᵐ[ν] fun t ↦ (Real.sqrt a : ℂ) * f (a * t) := by
  let V (f : H) (t : ℝ) := (Real.sqrt a : ℂ) * f (a * t)
  have hmem (f : H) : MemLp (V f) 2 ν := by
    have hpush : MemLp (f : ℝ → ℂ) 2 ((ν).map (fun t ↦ a * t)) := by
      rw [positiveRayScale_map a ha]
      exact (Lp.memLp f).smul_measure ENNReal.ofReal_ne_top
    exact ((memLp_map_measure_iff hpush.aestronglyMeasurable
      (measurable_const_mul a).aemeasurable).mp hpush).const_mul _
  let T (f : H) := (hmem f).toLp (V f)
  have hT (f : H) : (T f : ℝ → ℂ) =ᵐ[ν] V f := (hmem f).coeFn_toLp
  have hscale := positiveRayScale_quasiMeasurePreserving a ha
  refine ⟨{ toFun := T, map_add' := ?_, map_smul' := ?_, norm_map' := ?_ }, hT⟩
  · intro f g
    apply Lp.ext
    filter_upwards [hT (f+g), hT f, hT g, Lp.coeFn_add (T f) (T g),
      hscale.ae_eq_comp (Lp.coeFn_add f g)] with t h₁ h₂ h₃ h₄ h₅
    change (f + g) (a * t) = f (a * t) + g (a * t) at h₅
    rw [h₁, h₄]
    simp only [Pi.add_apply, V, h₂, h₃, h₅, mul_add]
  · intro c f
    apply Lp.ext
    filter_upwards [hT (c • f), hT f, Lp.coeFn_smul c (T f),
      hscale.ae_eq_comp (Lp.coeFn_smul c f)] with t h₁ h₂ h₃ h₄
    change (c • f) (a * t) = c * f (a * t) at h₄
    change T (c • f) t = (c • T f) t
    rw [h₁, h₃]
    simp only [Pi.smul_apply, smul_eq_mul, V, h₂, h₄]
    ring
  · intro f
    have heq : ‖T f‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [← L2.integral_sq_norm (𝕜 := ℂ), ← L2.integral_sq_norm (𝕜 := ℂ)]
      calc
        _ = ∫ t in Ioi 0, a * ‖f (a * t)‖ ^ 2 := by
          apply integral_congr_ae
          filter_upwards [hT f] with t ht
          simp [ht, V, mul_pow, Real.sq_sqrt ha.le]
        _ = _ := by
          rw [integral_const_mul]
          simpa only [smul_eq_mul, mul_zero] using
            integral_comp_mul_left_Ioi' (fun t ↦ ‖f t‖ ^ 2) 0 ha
    exact (sq_eq_sq₀ (norm_nonneg (T f)) (norm_nonneg f)).mp heq

/-- There is a unitary with the normalized dilation representative. -/
theorem exists_positiveRayDilation (a : ℝ) (ha : 0 < a) :
    ∃ T : H ≃ₗᵢ[ℂ] H, ∀ f : H, (T f : ℝ → ℂ) =ᵐ[ν] fun t ↦ (Real.sqrt a : ℂ) * f (a * t) := by
  obtain ⟨D, hD⟩ := exists_dilationIsometry a ha
  obtain ⟨I, hI⟩ := exists_dilationIsometry a⁻¹ (inv_pos.mpr ha)
  refine ⟨LinearIsometryEquiv.ofSurjective D (fun f ↦ ⟨I f, ?_⟩), hD⟩
  apply Lp.ext
  filter_upwards [hD (I f), (positiveRayScale_quasiMeasurePreserving a ha).ae_eq_comp (hI f)]
    with t h₁ h₂
  change I f (a * t) = (Real.sqrt a⁻¹ : ℂ) * f (a⁻¹ * (a * t)) at h₂
  rw [h₁, h₂, inv_mul_cancel_left₀ ha.ne', Real.sqrt_inv, Complex.ofReal_inv, ← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ha).ne'), one_mul]

/-- Positive scaling acts unitarily on L² of the positive ray with Lebesgue measure. -/
def positiveRayDilation (a : ℝ) (ha : 0 < a) : H ≃ₗᵢ[ℂ] H :=
  (exists_positiveRayDilation a ha).choose

/-- The representative of the unitary dilation has the square-root Jacobian. -/
theorem positiveRayDilation_apply (a : ℝ) (ha : 0 < a) (f : H) :
    (positiveRayDilation a ha f : ℝ → ℂ) =ᵐ[ν] fun t ↦ (Real.sqrt a : ℂ) * f (a * t) :=
  (exists_positiveRayDilation a ha).choose_spec f

/-- A measurable bounded rescaled profile defines an operator with the stated norm bound. -/
theorem exists_positiveRayMultiplier (Q : ℝ → ℂ) (hQ : Measurable Q) (C : ℝ)
    (hC : 0 ≤ C) (hQC : ∀ t, ‖Q t‖ ≤ C) (B : ℝ) :
    ∃ M : H →L[ℂ] H, ‖M‖ ≤ C ∧ ∀ f : H, (M f : ℝ → ℂ) =ᵐ[ν] fun t ↦ Q (t / B) * f t := by
  let s (t : ℝ) := Q (t / B)
  have hs : MemLp s ∞ ν := memLp_top_of_bound
    (hQ.comp (measurable_id.div_const B)).aestronglyMeasurable C (.of_forall fun t ↦ hQC (t / B))
  let mul := ContinuousLinearMap.mul ℂ ℂ
  let M := mul.holderL ν ∞ 2 2 (hs.toLp s)
  have hM (u : H) : (M u : ℝ → ℂ) =ᵐ[ν] fun t ↦ s t * u t :=
    (mul.coeFn_holder (r := 2) (hs.toLp s) u).trans
      (hs.coeFn_toLp.mono fun t ht ↦ congrArg (· * u t) ht)
  refine ⟨M, M.opNorm_le_bound hC (fun u ↦ ?_), hM⟩
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hM u] with t ht
  rw [ht, norm_mul]
  exact mul_le_mul_of_nonneg_right (hQC (t / B)) (norm_nonneg _)

/-- Multiplication by the rescaled bounded measurable profile on the positive ray. -/
def positiveRayMultiplier (Q : ℝ → ℂ) (hQ : Measurable Q) (C : ℝ)
    (hC : 0 ≤ C) (hQC : ∀ t, ‖Q t‖ ≤ C) (B : ℝ) : H →L[ℂ] H :=
  (exists_positiveRayMultiplier Q hQ C hC hQC B).choose

/-- The multiplier acts by pointwise multiplication for each L² input. -/
theorem positiveRayMultiplier_apply (Q : ℝ → ℂ) (hQ : Measurable Q) (C : ℝ)
    (hC : 0 ≤ C) (hQC : ∀ t, ‖Q t‖ ≤ C) (B : ℝ) (f : H) :
    (positiveRayMultiplier Q hQ C hC hQC B f : ℝ → ℂ) =ᵐ[ν] fun t ↦ Q (t / B) * f t :=
  (exists_positiveRayMultiplier Q hQ C hC hQC B).choose_spec.2 f

/-- The same bound for the profile also bounds the operator norm. -/
theorem positiveRayMultiplier_norm_le (Q : ℝ → ℂ) (hQ : Measurable Q) (C : ℝ)
    (hC : 0 ≤ C) (hQC : ∀ t, ‖Q t‖ ≤ C) (B : ℝ) :
    ‖positiveRayMultiplier Q hQ C hC hQC B‖ ≤ C :=
  (exists_positiveRayMultiplier Q hQ C hC hQC B).choose_spec.1



/-- The normalized dilation of every positive-ray L² vector is continuous in its positive
scale parameter. In logarithmic coordinates the orbit has the distances of an ordinary
Lebesgue translation orbit. -/
theorem positiveRayDilation_continuous (f : Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    Continuous (fun a : Ioi (0 : ℝ) ↦ positiveRayDilation a.1 a.2 f) := by
  let q (a : Ioi (0 : ℝ)) (t : ℝ) := (Real.sqrt a.1 : ℂ) * f (a.1 * t)
  let z (s : ℝ) := (Real.sqrt (Real.exp s) : ℂ)
  let F (s : ℝ) := z s * f (Real.exp s)
  have hz (s : ℝ) : ‖z s‖ ^ 2 = Real.exp s := by
    simp [z, Real.sq_sqrt (Real.exp_pos s).le]
  have hFm : MemLp F 2 volume := by
    have hmeas : Measurable F :=
      ((Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable).comp Real.measurable_exp).mul
        ((Lp.stronglyMeasurable f).measurable.comp Real.measurable_exp)
    apply (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).2
    have hsq : Integrable (fun t ↦ ‖f t‖ ^ (2 : ℕ)) (volume.restrict (Ioi 0)) :=
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
    have hf := (integrable_comp_exp (fun t ↦ ‖f t‖ ^ (2 : ℕ))).mpr hsq
    refine hf.congr (.of_forall fun s ↦ ?_)
    simp only [F, norm_mul, mul_pow, hz, smul_eq_mul]
  let v := hFm.toLp F
  let τ (a : Ioi (0 : ℝ)) := Lp.compMeasurePreserving (fun s ↦ Real.log a.1 + s)
    (measurePreserving_add_left volume (Real.log a.1)) v
  have hτ (a : Ioi (0 : ℝ)) : (τ a : ℝ → ℂ) =ᵐ[volume] fun s ↦ F (Real.log a.1 + s) :=
    (Lp.coeFn_compMeasurePreserving v (measurePreserving_add_left volume (Real.log a.1))).trans
      ((measurePreserving_add_left volume (Real.log a.1)).quasiMeasurePreserving.ae_eq_comp hFm.coeFn_toLp)
  have hτc : Continuous τ := by
    have hc : Continuous fun a : Ioi (0 : ℝ) ↦ ContinuousMap.addLeft (X := ℝ) (Real.log a.1) :=
      (ContinuousMap.curry ⟨fun p : Ioi (0 : ℝ) × ℝ ↦ Real.log p.1.1 + p.2,
        (Real.continuous_log'.comp continuous_fst).add continuous_snd⟩).continuous
    exact continuous_const.compMeasurePreservingLp (f := fun _ : Ioi (0 : ℝ) ↦ v) hc
      (fun a ↦ measurePreserving_add_left volume (Real.log a.1)) (by simp)
  have halg (a : Ioi (0 : ℝ)) (s : ℝ) : z s * q a (Real.exp s) = F (Real.log a.1 + s) := by
    dsimp only [q, F, z]
    rw [Real.exp_add, Real.exp_log a.2, Real.sqrt_mul a.2.le, Complex.ofReal_mul]
    ring
  have hdist (a b : Ioi (0 : ℝ)) :
      ‖positiveRayDilation a.1 a.2 f - positiveRayDilation b.1 b.2 f‖ = ‖τ a - τ b‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← L2.integral_sq_norm (𝕜 := ℂ), ← L2.integral_sq_norm (𝕜 := ℂ)]
    calc
      _ = ∫ t in Ioi 0, ‖q a t - q b t‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (positiveRayDilation a.1 a.2 f) (positiveRayDilation b.1 b.2 f),
          positiveRayDilation_apply a.1 a.2 f, positiveRayDilation_apply b.1 b.2 f] with t h₁ h₂ h₃
        simp only [q, h₁, Pi.sub_apply, h₂, h₃]
      _ = ∫ s, Real.exp s • ‖q a (Real.exp s) - q b (Real.exp s)‖ ^ 2 :=
        (integral_comp_exp _).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (τ a) (τ b), hτ a, hτ b] with s h₁ h₂ h₃
        rw [h₁, Pi.sub_apply, h₂, h₃, ← halg a s, ← halg b s, ← mul_sub, norm_mul, mul_pow, hz, smul_eq_mul]
  rw [continuous_iff_continuousAt]
  intro a
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  simp only [hdist]
  exact tendsto_iff_norm_sub_tendsto_zero.mp (hτc.continuousAt (x := a))

end RiemannMasullo.FlatPolar
