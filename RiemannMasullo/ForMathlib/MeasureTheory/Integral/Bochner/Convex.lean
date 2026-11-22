module

public import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! # Coordinatewise integrals in compact convex sets -/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology

namespace RiemannMasullo

/-- The coordinatewise probability average of functions in a compact convex
subset of a product is still in that subset. Compactness reduces the assertion
to finitely many coordinates, where the Bochner integral applies. -/
theorem integral_mem_compact_convex_functions {A K E : Type*} [MeasurableSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure K) [IsProbabilityMeasure μ] (C : Set (A → E)) (hc : IsCompact C)
    (hv : Convex ℝ C) (f : K → A → E) (hf : ∀ k, f k ∈ C)
    (hi : ∀ x, Integrable (fun k ↦ f k x) μ) : (fun x ↦ ∫ k, f k x ∂μ) ∈ C := by
  classical
  let g (x : A) := ∫ k, f k x ∂μ
  let S (x : A) := {l : A → E | l x = g x}
  have hS (x : A) : IsClosed (S x) := isClosed_eq (continuous_apply x) continuous_const
  have hfinite (I : Finset A) : (C ∩ ⋂ i ∈ I, S i).Nonempty := by
    let π : (A → E) →ₗ[ℝ] (I → E) := LinearMap.pi (fun i ↦ LinearMap.proj i.val)
    have hπ : Continuous π := continuous_pi fun i ↦ continuous_apply i.val
    let F (k : K) : I → E := π (f k)
    have hF : Integrable F μ := (integrable_pi_iff).mpr fun i ↦ hi i.val
    have hmean := (hv.linear_image π).integral_mem (hc.image hπ).isClosed
      (.of_forall fun k ↦ mem_image_of_mem π (hf k)) hF
    obtain ⟨y, hy, hpy⟩ := hmean
    refine ⟨y, hy, mem_iInter₂.mpr fun i hi ↦ ?_⟩
    have hcoord := congrFun hpy ⟨i, hi⟩
    exact hcoord.trans ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I ↦ E) ⟨i, hi⟩).integral_comp_comm hF).symm

  obtain ⟨l, hl, heq⟩ := hc.inter_iInter_nonempty S hS hfinite
  have hh : l = g := funext (mem_iInter.mp heq)
  change g ∈ C
  rwa [← hh]

end RiemannMasullo
