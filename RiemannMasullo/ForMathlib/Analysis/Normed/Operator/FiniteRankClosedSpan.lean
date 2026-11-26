module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public noncomputable section
open Set
namespace RiemannMasullo

/-- If separating linear observations place the images of a spanning family in a
finite-dimensional space, every bounded operator supported on its closed span
has the same finite-rank bound. The observation space need not carry a topology. -/
theorem finrank_range_comp_le_of_closedSpan_images
    {H E V I : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [AddCommGroup V] [Module ℂ V]
    (u : I → H) (P : H →L[ℂ] H) (T : H →L[ℂ] E)
    (e : E →ₗ[ℂ] V) (he : Function.Injective e)
    (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (hP : ∀ x, P x ∈ (Submodule.span ℂ (range u)).topologicalClosure)
    (hT : ∀ i, e (T (u i)) ∈ W) :
    FiniteDimensional ℂ (T.comp P).toLinearMap.range ∧
      Module.finrank ℂ (T.comp P).toLinearMap.range ≤ Module.finrank ℂ W := by
  let K := W.comap e
  let f : K →ₗ[ℂ] W := (e.domRestrict K).codRestrict W (fun x ↦ x.property)
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (he (congrArg Subtype.val h))
  let : FiniteDimensional ℂ K := FiniteDimensional.of_injective f hf
  have hK : IsClosed (K : Set E) := K.isClosed_of_finiteDimensional
  have hs : (Submodule.span ℂ (range u)).topologicalClosure ≤ K.comap T.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hT i
    · exact hK.preimage T.continuous
  have hr : (T.comp P).toLinearMap.range ≤ K := by
    rintro _ ⟨x, rfl⟩
    exact hs (hP x)
  let : FiniteDimensional ℂ (T.comp P).toLinearMap.range := Submodule.finiteDimensional_of_le hr
  exact ⟨inferInstance, (Submodule.finrank_mono hr).trans (LinearMap.finrank_le_finrank_of_injective hf)⟩

end RiemannMasullo
