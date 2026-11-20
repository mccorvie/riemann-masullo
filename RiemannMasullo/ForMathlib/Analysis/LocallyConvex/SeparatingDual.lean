module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

@[expose] public section

namespace RiemannMasullo

/-- The continuous dual of a Hausdorff polynormable space over `ℝ` or `ℂ` separates points. -/
theorem polynormableSpace_separatingDual (𝕜 E : Type*) [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [PolynormableSpace 𝕜 E] [T1Space E] : SeparatingDual 𝕜 E := by
  let : Module ℝ E := Module.restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  let : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup 𝕜 E
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms 𝕜 E).toLocallyConvexSpace
  refine ⟨fun x hx ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := RCLike.geometric_hahn_banach_point_point (𝕜 := 𝕜) hx
  exact ⟨φ, fun hzero ↦ by simp [hzero] at hφ⟩

end RiemannMasullo
