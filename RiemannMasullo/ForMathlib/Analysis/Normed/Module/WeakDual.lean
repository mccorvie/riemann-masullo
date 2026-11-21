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

open scoped Pointwise in
/-- The weak-dual polar of a zero-neighborhood in a topological vector space over a
proper normed field is compact. -/
theorem isCompact_weakDual_polar {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul 𝕜 X] {U : Set X} (hU : U ∈ 𝓝 (0 : X)) :
    IsCompact (WeakDual.polar 𝕜 U) := by
  let ev : WeakDual 𝕜 X → X → 𝕜 := fun φ x ↦ φ x
  have hev : IsEmbedding ev := ⟨⟨rfl⟩, DFunLike.coe_injective⟩
  rw [hev.isCompact_iff]
  have himage : ev '' WeakDual.polar 𝕜 U =
      range (fun l : X →ₗ[𝕜] 𝕜 ↦ (l : X → 𝕜)) ∩ ⋂ x ∈ U, {f | ‖f x‖ ≤ 1} := by
    ext f
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨⟨φ.toStrongDual.toLinearMap, rfl⟩, mem_iInter₂.mpr hφ⟩
    · rintro ⟨⟨l, rfl⟩, h⟩
      have hl : ∀ x ∈ U, ‖l x‖ ≤ 1 := mem_iInter₂.mp h
      have hc : Continuous l := by
        apply continuous_of_continuousAt_zero l
        rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
        intro ε hε
        obtain ⟨a, ha, haε⟩ := NormedField.exists_norm_lt 𝕜 hε
        have hnear : a • U ∈ 𝓝 (0 : X) := by
          simpa using smul_mem_nhds_smul₀ (norm_pos_iff.mp ha) hU
        filter_upwards [hnear] with x hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [dist_zero_right, map_smul, norm_smul]
        exact (mul_le_of_le_one_right ha.le (hl y hy)).trans_lt haε
      exact ⟨StrongDual.toWeakDual ⟨l, hc⟩, hl, rfl⟩
  have hclosed : IsClosed (ev '' WeakDual.polar 𝕜 U) := by
    rw [himage]
    exact (LinearMap.isClosed_range_coe X 𝕜 (RingHom.id 𝕜)).inter
      (isClosed_iInter fun x ↦ isClosed_iInter fun _ ↦
        isClosed_le (continuous_apply x).norm continuous_const)
  choose a ha using fun x : X ↦ (absorbent_nhds_zero (𝕜 := 𝕜) hU x).exists
  refine (isCompact_pi_infinite (fun x : X ↦ isCompact_closedBall (0 : 𝕜) ‖a x‖))
    |>.of_isClosed_subset hclosed ?_
  rintro _ ⟨φ, hφ, rfl⟩ x
  obtain ⟨y, hy, hxy⟩ := ha x (mem_singleton x)
  change φ x ∈ Metric.closedBall (0 : 𝕜) ‖a x‖
  rw [Metric.mem_closedBall, dist_zero_right,
    ← congrArg (fun z ↦ φ z) hxy, map_smul, norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hφ y hy)

end RiemannMasullo
