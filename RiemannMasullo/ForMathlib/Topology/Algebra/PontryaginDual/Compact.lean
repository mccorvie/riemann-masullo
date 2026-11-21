module

public import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Algebra.Equicontinuity
import Mathlib.Topology.MetricSpace.Equicontinuity

@[expose] public section

open Set Filter Topology

namespace RiemannMasullo

/-- There is a radius such that characters mapping any fixed identity neighborhood into
the closed circle ball of that radius form a compact set in the compact-open topology.
Powers give equicontinuity at the identity, and Arzelà–Ascoli gives compactness. -/
theorem exists_isCompact_pontryaginDual_polar {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    ∃ r : ℝ, 0 < r ∧ ∀ U ∈ 𝓝 (1 : G),
      IsCompact {χ : PontryaginDual G | MapsTo χ U (Metric.closedBall 1 r)} := by
  classical
  have hArc : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
    simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
  obtain ⟨r, hr, hBall⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hArc
  refine ⟨r, hr, fun U hU ↦ ?_⟩
  let W := Metric.closedBall (1 : Circle) r
  let S := {f : G →* Circle | MapsTo f U W}
  have hEqui : Equicontinuous (fun f : S ↦ (f.1 : G → Circle)) := by
    refine equicontinuous_of_equicontinuousAt_one Subtype.val ?_
    apply (Metric.equicontinuousAt_iff_right (α := Circle)).mpr
    intro ε hε
    let T (n : ℕ) := (fun z : Circle ↦ z ^ n) ⁻¹' W
    have hDisj : Disjoint (Metric.ball (1 : Circle) ε)ᶜ (⋂ n, T n) := by
      refine Set.disjoint_left.mpr fun z hz hzT ↦ ?_
      have hz1 := Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two (z := z)
        (fun n _ ↦ hBall (mem_iInter.mp hzT n))
      exact hz (hz1.symm ▸ Metric.mem_ball_self hε)
    obtain ⟨N, hN⟩ := (isClosed_compl_iff.mpr Metric.isOpen_ball).isCompact
      |>.elim_finite_subfamily_closed T
        (fun n ↦ Metric.isClosed_closedBall.preimage (continuous_pow n)) hDisj
    have hNear : ∀ᶠ x : G in 𝓝 1, ∀ n ∈ N, x ^ n ∈ U :=
      (eventually_all_finset N).2 fun n _ ↦
        (continuous_pow n).tendsto' 1 1 (one_pow n) hU
    filter_upwards [hNear] with x hx f
    have hPow : f.1 x ∈ ⋂ n ∈ N, T n := by
      simp only [mem_iInter, T, mem_preimage, ← map_pow]
      exact fun n hn ↦ f.2 (hx n hn)
    have hMem : f.1 x ∈ Metric.ball (1 : Circle) ε := by
      by_contra hz
      exact (Set.disjoint_left.mp hN) hz hPow
    simpa [Function.comp_def, map_one, Metric.mem_ball, dist_comm] using hMem
  let A := {f : ContinuousMonoidHom G Circle | MapsTo f U W}
  let C := ContinuousMonoidHom.toContinuousMap '' A
  have hPointwise : ContinuousMap.toFun '' C =
      Set.pi U (fun _ ↦ W) ∩ Set.range ((⇑) : (G →* Circle) → G → Circle) := by
    ext f
    constructor
    · rintro ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩
      exact ⟨hψ, ψ.toMonoidHom, rfl⟩
    · rintro ⟨hf, ψ, rfl⟩
      let ψc : ContinuousMonoidHom G Circle :=
        { toMonoidHom := ψ, continuous_toFun := hEqui.continuous ⟨ψ, hf⟩ }
      exact ⟨ψc.toContinuousMap, ⟨ψc, hf, rfl⟩, rfl⟩
  have hC : IsCompact C := by
    apply ArzelaAscoli.isCompact_of_equicontinuous
    · rw [hPointwise]
      exact ((isClosed_set_pi fun _ _ ↦ Metric.isClosed_closedBall).inter
        (MonoidHom.isClosed_range_coe G Circle)).isCompact
    · refine (equicontinuous_iff_range (F := fun f : C ↦ f.1.toFun)).mpr ?_
      rw [← Set.image_eq_range ContinuousMap.toFun C, hPointwise]
      have hRange : range (fun f : S ↦ (f.1 : G → Circle)) =
          Set.pi U (fun _ ↦ W) ∩ Set.range ((⇑) : (G →* Circle) → G → Circle) := by
        ext f
        constructor
        · rintro ⟨ψ, rfl⟩
          exact ⟨ψ.2, ψ.1, rfl⟩
        · rintro ⟨hf, ψ, rfl⟩
          exact ⟨⟨ψ, hf⟩, rfl⟩
      rw [← hRange]
      exact equicontinuous_iff_range.mp hEqui
  exact (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).isCompact_iff.mpr hC

end RiemannMasullo
