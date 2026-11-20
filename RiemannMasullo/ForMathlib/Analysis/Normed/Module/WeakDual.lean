module

public import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach

public section

open Filter Set Topology

namespace RiemannMasullo

/-- The weak-star dual of an infinite-dimensional normed space is incomplete. A discontinuous
linear functional is a pointwise limit of continuous Hahn–Banach extensions of its restrictions
to finite-dimensional subspaces. -/
theorem weakDual_not_completeSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (hinf : ¬ FiniteDimensional 𝕜 E) :
    letI := IsTopologicalAddGroup.rightUniformSpace (WeakDual 𝕜 E)
    ¬ CompleteSpace (WeakDual 𝕜 E) := by
  classical
  let := IsTopologicalAddGroup.rightUniformSpace (WeakDual 𝕜 E)
  let := isUniformAddGroup_of_addCommGroup (G := WeakDual 𝕜 E)
  intro hcomplete
  let eval : WeakDual 𝕜 E →+ (E → 𝕜) := ⟨⟨fun f x ↦ f x, rfl⟩, fun _ _ ↦ rfl⟩
  have heval : IsInducing eval := ⟨rfl⟩
  have hclosed : IsClosed (range eval) :=
    (AddMonoidHom.isUniformInducing_of_isInducing heval).isComplete_range.isClosed
  -- Prescribe values on a Hamel basis with unbounded ratios of value to vector norm.
  let b := Module.Free.chooseBasis 𝕜 E
  have : Infinite (Module.Free.ChooseBasisIndex 𝕜 E) :=
    not_finite_iff_infinite.mp fun _ ↦ hinf b.finiteDimensional_of_finite
  let i := Infinite.natEmbedding (Module.Free.ChooseBasisIndex 𝕜 E)
  let values (n : ℕ) : 𝕜 := (n : 𝕜) * (‖b (i n)‖ : 𝕜)
  let f : E →ₗ[𝕜] 𝕜 := b.constr 𝕜 (Function.extend i values 0)
  have happrox (s : Finset E) : ∃ g : StrongDual 𝕜 E, ∀ x ∈ s, g x = f x := by
    let V := Submodule.span 𝕜 (s : Set E)
    let fV : StrongDual 𝕜 V := (f.comp V.subtype).toContinuousLinearMap
    obtain ⟨g, hg, -⟩ := exists_extension_norm_eq V fV
    exact ⟨g, fun x hx ↦ hg ⟨x, Submodule.subset_span hx⟩⟩
  choose g hg using happrox
  have hlim : Tendsto (fun s x ↦ g s x) atTop (𝓝 (f : E → 𝕜)) :=
    tendsto_pi_nhds.mpr fun x ↦
      tendsto_atTop_of_eventually_const (i₀ := {x}) fun s hs ↦
        hg s x (Finset.singleton_subset_iff.mp hs)
  obtain ⟨l, hl⟩ := hclosed.mem_of_tendsto hlim
    (Eventually.of_forall fun s ↦ ⟨StrongDual.toWeakDual (g s), rfl⟩)
  obtain ⟨n, hn⟩ := exists_nat_gt ‖WeakDual.toStrongDual l‖
  have hvalue : WeakDual.toStrongDual l (b (i n)) = values n := by
    change eval l (b (i n)) = values n
    rw [hl, Module.Basis.constr_basis, i.injective.extend_apply]
  have hbound := (WeakDual.toStrongDual l).le_opNorm (b (i n))
  rw [hvalue, norm_mul, RCLike.norm_natCast, RCLike.norm_of_nonneg (norm_nonneg _)] at hbound
  exact (not_le_of_gt hn) (le_of_mul_le_mul_right hbound (norm_pos_iff.mpr (b.ne_zero _)))

end RiemannMasullo
