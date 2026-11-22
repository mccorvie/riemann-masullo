module

public import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.BanachSteinhaus
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

public section

open Bornology Set

namespace RiemannMasullo

/-- Applying a continuous linear map to a family with bounded range preserves boundedness. -/
theorem isVonNBounded_range_comp_clm {𝕜 X Y ι : Type*} [NormedField 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
    [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y]
    (A : X →L[𝕜] Y) (f : ι → X) (hf : IsVonNBounded 𝕜 (range f)) :
    IsVonNBounded 𝕜 (range fun n ↦ A (f n)) := by
  change IsVonNBounded 𝕜 (range (A ∘ f))
  rw [range_comp]
  exact hf.image A

/-- For a quasi-complete Hausdorff source, a pointwise bounded family of continuous
linear maps is bounded for the topology of uniform convergence on bounded sets. -/
theorem isVonNBounded_range_clm_of_pointwise {𝕜 X Y ι : Type*} [RCLike 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [UniformSpace X] [IsUniformAddGroup X]
    [PolynormableSpace 𝕜 X] [T2Space X] [QuasiCompleteSpace 𝕜 X]
    [AddCommGroup Y] [Module 𝕜 Y] [UniformSpace Y] [IsUniformAddGroup Y]
    [PolynormableSpace 𝕜 Y] (f : ι → X →L[𝕜] Y) (h : ∀ x, IsVonNBounded 𝕜 (range fun i ↦ f i x)) :
    IsVonNBounded 𝕜 (range f) :=
  ContinuousLinearMap.isVonNBounded_iff.mpr fun _ hT ↦ isVonNBounded_image2_apply_of_pointwise f h hT

/-- Precomposing a strongly bounded family of functionals on a barrelled space with a
continuous map gives an equicontinuous family. -/
theorem equicontinuous_comp_of_isVonNBounded_range_dual {𝕜 X Z ι : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [UniformSpace X] [IsUniformAddGroup X]
    [PolynormableSpace 𝕜 X] [BarrelledSpace 𝕜 X]
    [TopologicalSpace Z] (f : ι → StrongDual 𝕜 X) (h : IsVonNBounded 𝕜 (range f))
    (g : Z → X) (hg : Continuous g) : Equicontinuous (fun i z ↦ f i (g z)) := by
  have hpoint (x : X) : IsVonNBounded 𝕜 (range fun i ↦ f i x) :=
    isVonNBounded_range_comp_clm (ContinuousLinearMap.applyₗ 𝕜 (RingHom.id 𝕜) x) f h
  have he := (PolynormableSpace.banach_steinhaus hpoint).equicontinuous
  exact fun z U hU ↦ (hg.tendsto z).eventually (he (g z) U hU)

end RiemannMasullo
