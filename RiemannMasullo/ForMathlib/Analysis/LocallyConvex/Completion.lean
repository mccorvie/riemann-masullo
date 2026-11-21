module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Topology.Algebra.LinearMapCompletion

public section

open Filter Set Topology UniformSpace

namespace RiemannMasullo

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E]
  [UniformContinuousConstSMul 𝕜 E]

/-- A continuous seminorm extends to a continuous seminorm on the completion. -/
private theorem exists_continuous_seminorm_completion (p : Seminorm 𝕜 E) (hp : Continuous p) :
    ∃ q : Seminorm 𝕜 (Completion E), Continuous q ∧ ∀ x : E, q x = p x := by
  let f : Completion E → ℝ := Completion.extension (p : E → ℝ)
  have hf : Continuous f := Completion.continuous_extension
  have hcoe (x : E) : f x = p x :=
    Completion.extension_coe (Seminorm.uniformContinuous_of_continuousAt_zero hp.continuousAt) x
  have hadd (x y : Completion E) : f (x + y) ≤ f x + f y := by
    refine Completion.induction_on₂ x y
      (isClosed_le (hf.comp (continuous_fst.add continuous_snd))
        ((hf.comp continuous_fst).add (hf.comp continuous_snd))) fun a b ↦ ?_
    rw [← Completion.coe_add, hcoe, hcoe, hcoe]
    exact map_add_le_add p a b
  have hsmul (c : 𝕜) (x : Completion E) : f (c • x) = ‖c‖ * f x := by
    refine Completion.induction_on x
      (isClosed_eq (hf.comp (continuous_const_smul c)) (continuous_const.mul hf)) fun a ↦ ?_
    rw [← Completion.coe_smul, hcoe, hcoe, map_smul_eq_mul]
  exact ⟨Seminorm.of f hadd hsmul, hf, hcoe⟩

/-- The completion of a polynormable space is polynormable. -/
theorem polynormableSpace_completion [PolynormableSpace 𝕜 E] :
    PolynormableSpace 𝕜 (Completion E) := by
  let p : SeminormFamily 𝕜 (Completion E) {q : Seminorm 𝕜 (Completion E) // Continuous q} :=
    Subtype.val
  refine ⟨(p.withSeminorms_iff_nhds_eq_iInf).mpr (le_antisymm ?_ ?_)⟩
  · refine le_iInf fun q ↦ ?_
    exact tendsto_iff_comap.mp (q.property.tendsto' 0 0 (map_zero q.val))
  · intro U hU
    obtain ⟨W, hW, hclosed, hWU⟩ := exists_mem_nhds_isClosed_subset hU
    have hpre : ((↑) : E → Completion E) ⁻¹' W ∈ 𝓝 (0 : E) :=
      (Completion.continuous_coe (α := E)).continuousAt.preimage_mem_nhds (by simpa using hW)
    obtain ⟨r, hr, hrW⟩ := (PolynormableSpace.hasBasis_zero_ball 𝕜 E).mem_iff.mp hpre
    obtain ⟨q, hq, hcoe⟩ := exists_continuous_seminorm_completion r hr
    have hqW : q.ball 0 1 ⊆ W := by
      intro x hx
      have hx' : x ∈ {y : Completion E | 1 ≤ q y} ∪ W := by
        refine Completion.induction_on x ((isClosed_le continuous_const hq).union hclosed)
          fun a ↦ ?_
        by_cases ha : q a < 1
        · exact Or.inr (hrW (r.mem_ball_zero.mpr ((hcoe a) ▸ ha)))
        · exact Or.inl (le_of_not_gt ha)
      exact hx'.resolve_left (not_le_of_gt (q.mem_ball_zero.mp hx))
    apply (iInf_le (fun i ↦ (𝓝 0).comap (p i)) ⟨q, hq⟩)
    refine mem_comap.mpr ⟨Metric.ball 0 1, Metric.ball_mem_nhds _ one_pos, ?_⟩
    change q ⁻¹' Metric.ball 0 1 ⊆ U
    rw [← q.ball_zero_eq_preimage_ball]
    exact hqW.trans hWU

end RiemannMasullo
