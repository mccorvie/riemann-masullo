module

public import Mathlib.Topology.Algebra.Group.Pointwise

public section

open Set Filter Topology
open scoped Pointwise

namespace RiemannMasullo

/-- One can thicken a closed set by a zero neighborhood while keeping its closure
disjoint from a specified finite set of exterior points. -/
theorem exists_nhds_zero_closure_add_avoids_finset {E : Type*} [AddCommGroup E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    (K : Set E) (hK : IsClosed K) (F : Finset E) (hF : ∀ x ∈ F, x ∉ K) :
    ∃ W : Set E, W ∈ 𝓝 (0 : E) ∧ ∀ x ∈ F, x ∉ closure (K + W) := by
  classical
  have hpoint (x : E) (hx : x ∉ K) :
      ∃ W : Set E, W ∈ 𝓝 (0 : E) ∧ x ∉ closure (K + W) := by
    have hpre : (fun y : E ↦ x - y) ⁻¹' Kᶜ ∈ 𝓝 (0 : E) := by
      apply (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
      simpa using hK.isOpen_compl.mem_nhds hx
    obtain ⟨V, hVo, hV₀, hV⟩ := exists_open_nhds_zero_add_subset hpre
    let W := V ∩ -V
    have hW : W ∈ 𝓝 (0 : E) := by
      have hv := hVo.mem_nhds hV₀
      exact inter_mem hv (by simpa only [image_neg_eq_neg, neg_zero] using
        (isOpenMap_neg E).image_mem_nhds hv)
    have hsymm : ∀ y ∈ W, -y ∈ W := by
      intro y hy
      simpa [W, and_comm] using hy
    refine ⟨W, hW, fun hc ↦ ?_⟩
    have hx' : x ∈ K + (W + W) := by
      rw [← add_assoc]
      exact closure_subset_add_right_of_mem_nhds_zero_of_neg (K + W) hW hsymm hc
    obtain ⟨a, ha, b, hb, hab⟩ := mem_add.mp hx'
    have hb' := hV (add_subset_add inter_subset_left inter_subset_left hb)
    exact hb' (by simpa only [← hab, add_sub_cancel_right] using ha)
  choose W hW he using fun x : F ↦ hpoint x (hF x x.property)
  refine ⟨⋂ x : F, W x, Filter.iInter_mem.2 hW, fun x hx hc ↦ he ⟨x, hx⟩ ?_⟩
  exact closure_mono (add_subset_add Subset.rfl (iInter_subset W ⟨x, hx⟩)) hc

end RiemannMasullo
