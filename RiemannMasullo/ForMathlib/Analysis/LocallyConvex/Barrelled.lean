module

public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Integration of pointwise bounded families on a barrelled space -/

public section

open Filter MeasureTheory Set Topology
open scoped NNReal

namespace RiemannMasullo

/-- Integrating a pointwise bounded family of continuous linear forms against a
continuous weight gives a continuous linear form whenever each integral converges.
On compact subsets the supremum of the evaluation seminorms bounds the integral.
Banach–Steinhaus then gives continuity of the limit along a compact exhaustion. -/
theorem exists_continuousLinearMap_integral_mul {E X : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [BarrelledSpace ℂ E]
    [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (v : X → E →ₗ[ℂ] ℂ)
    (hv : ∀ x, Continuous (fun e ↦ ‖v x e‖)) (hb : ∀ e, ∃ B : ℝ, ∀ x, ‖v x e‖ ≤ B)
    (w : X → ℂ) (hw : Continuous w) (hi : ∀ e, Integrable (fun x ↦ v x e * w x) μ) :
    ∃ Z : E →L[ℂ] ℂ, ∀ e, Z e = ∫ x, v x e * w x ∂μ := by
  let q (x : X) := (normSeminorm ℂ ℂ).comp (v x)
  have hq : BddAbove (range q) := Seminorm.bddAbove_range_iff.mpr fun e ↦ by
    obtain ⟨B, hB⟩ := hb e
    exact ⟨B, forall_mem_range.mpr hB⟩
  let p : Seminorm ℂ E := ⨆ x, q x
  have hp : Continuous p := by
    rw [show (p : E → ℝ) = ⨆ x, (q x : E → ℝ) from Seminorm.coe_iSup_eq hq]
    exact Seminorm.continuous_iSup q hv hq
  have hle (e : E) (x : X) : ‖v x e‖ ≤ p e := (le_ciSup hq x : q x ≤ p) e
  let K := compactCovering X
  have hK (n : ℕ) : IsCompact (K n) := isCompact_compactCovering X n
  let L (n : ℕ) : E →ₗ[ℂ] ℂ :=
    { toFun := fun e ↦ ∫ x in K n, v x e * w x ∂μ
      map_add' := fun a b ↦ by
        simp_rw [map_add, add_mul]
        exact integral_add (hi a).integrableOn (hi b).integrableOn
      map_smul' := fun z e ↦ by
        simp only [map_smul, RingHom.id_apply, smul_eq_mul, mul_assoc, integral_const_mul] }
  have hc (n : ℕ) : Continuous (L n) := by
    let B := ∫ x in K n, ‖w x‖ ∂μ
    let b : ℝ≥0 := ⟨B, integral_nonneg fun _ ↦ norm_nonneg _⟩
    apply (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp (L n)
    intro _
    apply Seminorm.continuous_of_le (q := b • p) (hp.const_smul b)
    intro e
    change ‖∫ x in K n, v x e * w x ∂μ‖ ≤ B * p e
    rw [mul_comm B, ← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on
      (hi e).norm.integrableOn ((hw.norm.continuousOn.integrableOn_compact (hK n)).const_mul _)
      (hK n).measurableSet fun x _ ↦ ?_)
    exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right (hle e x) (norm_nonneg _))
  let T (n : ℕ) : E →L[ℂ] ℂ := ⟨L n, hc n⟩
  have hlim : Tendsto (fun n e ↦ T n e) atTop (𝓝 (fun e ↦ ∫ x, v x e * w x ∂μ)) := by
    apply tendsto_pi_nhds.mpr
    intro e
    change Tendsto (fun n ↦ ∫ x in K n, v x e * w x ∂μ) atTop (𝓝 _)
    simpa only [K, iUnion_compactCovering, setIntegral_univ] using
      (tendsto_setIntegral_of_monotone (fun n ↦ (hK n).measurableSet)
        (fun _ _ h ↦ compactCovering_subset X h) (hi e).integrableOn)
  exact ⟨continuousLinearMapOfTendsto T hlim, fun _ ↦ rfl⟩

end RiemannMasullo
