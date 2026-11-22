module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

public section

open Filter Topology

namespace RiemannMasullo

/-- A continuous seminorm on a product vanishes on vectors zero on some finite set. -/
theorem product_seminorm_tail {𝕜 I : Type*} [NontriviallyNormedField 𝕜] {X : I → Type*} [∀ i, AddCommGroup (X i)]
    [∀ i, Module 𝕜 (X i)] [∀ i, TopologicalSpace (X i)]
    (q : Seminorm 𝕜 (∀ i, X i)) (hq : Continuous q) :
    ∃ s : Finset I, ∀ x, (∀ i ∈ s, x i = 0) → q x = 0 := by
  have hU := q.ball_mem_nhds hq one_pos
  rw [nhds_pi] at hU
  obtain ⟨s, W, hW, hsub⟩ := Filter.mem_pi'.mp hU
  refine ⟨s, fun x hx ↦ ?_⟩
  by_contra h
  have hxpos := lt_of_le_of_ne (apply_nonneg q x) (Ne.symm h)
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 ((q x)⁻¹)
  have hcx : c • x ∈ q.ball 0 1 := hsub fun i hi ↦ by
    change c • x i ∈ W i
    rw [hx i hi, smul_zero]
    exact mem_of_mem_nhds (hW i)
  have hlt := q.mem_ball_zero.mp hcx
  rw [map_smul_eq_mul, ← lt_div_iff₀ hxpos, one_div] at hlt
  exact hlt.asymm hc

end RiemannMasullo
