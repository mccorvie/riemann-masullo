module

public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Algebra.Module.ULift

@[expose] public section

open Set Bornology Topology

namespace RiemannMasullo

/-- A set in a polynormable space is bounded if every continuous linear functional is
bounded on it. -/
theorem isVonNBounded_of_dual_bounded {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E]
    [Module 𝕜 E] [TopologicalSpace E] [PolynormableSpace 𝕜 E] {s : Set E}
    (h : ∀ f : StrongDual 𝕜 E, ∃ C : ℝ, ∀ x ∈ s, ‖f x‖ ≤ C) : IsVonNBounded 𝕜 s := by
  let hp := PolynormableSpace.withSeminorms 𝕜 E
  refine hp.isVonNBounded_iff_seminorm_bddAbove.mpr fun p ↦ ?_
  rw [bddAbove_def]
  let e : ULift.{0} E ≃ₗ[𝕜] E := ULift.moduleEquiv
  let q := p.val.comp e.toLinearMap
  let : SeminormedAddCommGroup (ULift.{0} E) := q.toSeminormedAddCommGroup
  let : TopologicalSpace (ULift.{0} E) := q.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace
  let : NormedSpace 𝕜 (ULift.{0} E) := ⟨fun c x ↦ (map_smul_eq_mul q c x).le⟩
  let : IsTopologicalAddGroup E := hp.isTopologicalAddGroup
  have he : Continuous e.symm := by
    refine (Metric.continuous_iff' (f := fun y : E ↦ e.symm y)).mpr fun x ε hε ↦ ?_
    have hcont : Continuous (fun y : E ↦ p.val (y - x)) :=
      p.property.comp (continuous_id.sub continuous_const)
    have hsmall := hcont.continuousAt (x := x).eventually_lt continuousAt_const
      (show p.val (x - x) < ε by simpa)
    simp only [dist_eq_norm, ← map_sub]
    exact hsmall
  -- Apply uniform boundedness to the evaluations on the Banach dual for this seminorm.
  let ev (x : s) := NormedSpace.inclusionInDoubleDual 𝕜 (ULift E) (e.symm x)
  obtain ⟨C, hC⟩ := banach_steinhaus (g := ev) fun f ↦ by
    obtain ⟨C, hC⟩ := h (f.comp ⟨e.symm.toLinearMap, he⟩)
    exact ⟨C, fun x ↦ hC x x.property⟩
  refine ⟨C, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  change ‖e.symm x‖ ≤ C
  rw [← (NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map (e.symm x)]
  exact hC ⟨x, hx⟩

end RiemannMasullo
