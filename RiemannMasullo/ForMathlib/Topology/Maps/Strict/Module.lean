module

public import Mathlib.Topology.Maps.Strict.Module

@[expose] public section

open Set Filter Topology

namespace RiemannMasullo

variable {R G A B : Type*} [Ring R]
  [AddCommGroup G] [Module R G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [AddCommGroup A] [Module R A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [AddCommGroup B] [Module R B] [TopologicalSpace B] [IsTopologicalAddGroup B]

omit [IsTopologicalAddGroup A] in
/-- For two open linear quotient maps with a common source, strictness transfers from the
restriction of the first map to the second kernel to the restriction in the other direction. -/
private theorem isStrictMap_comp_ker_subtype_of
    (p : G →ₗ[R] A) (q : G →ₗ[R] B)
    (hp : IsOpenQuotientMap p) (hq : IsOpenQuotientMap q)
    (h : IsStrictMap (p.comp q.ker.subtype)) : IsStrictMap (q.comp p.ker.subtype) := by
  let f := (p.comp q.ker.subtype).rangeRestrict
  let g := (q.comp p.ker.subtype).rangeRestrict
  have hf : IsOpenQuotientMap f := LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mp h
  apply LinearMap.isStrictMap_iff_isOpenQuotientMap_rangeRestrict.mpr
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨b, x, rfl⟩
    exact ⟨x, rfl⟩
  · exact (hq.continuous.comp continuous_subtype_val).subtype_mk _
  · change IsOpenMap g
    rw [IsTopologicalAddGroup.isOpenMap_iff_nhds_zero]
    intro T hT
    let U := g ⁻¹' T
    have hU : U ∈ 𝓝 (0 : p.ker) := hT
    suffices h : g '' U ∈ 𝓝 (0 : (q.comp p.ker.subtype).range) from
      mem_of_superset h (image_preimage_subset _ _)
    rw [nhds_subtype] at hU
    obtain ⟨U₀, hU₀, hsub⟩ := Filter.mem_comap.mp hU
    have hdiff : (fun z : G × G ↦ z.1 - z.2) ⁻¹' U₀ ∈ 𝓝 ((0 : G), (0 : G)) :=
      continuous_sub.continuousAt.preimage_mem_nhds (by simpa using hU₀)
    obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hdiff
    let W' : Set q.ker := Subtype.val ⁻¹' W
    have hW' : W' ∈ 𝓝 (0 : q.ker) := preimage_coe_mem_nhds_subtype.mpr (mem_nhdsWithin_of_mem_nhds hW)
    have hIm : f '' W' ∈ 𝓝 (0 : (p.comp q.ker.subtype).range) := by
      rw [← map_zero f, ← hf.map_nhds_eq]
      exact Filter.image_mem_map hW'
    rw [nhds_subtype] at hIm
    obtain ⟨O, hO, hOsub⟩ := Filter.mem_comap.mp hIm
    have hsmall : V ∩ p ⁻¹' O ∈ 𝓝 (0 : G) :=
      inter_mem hV (hp.continuous.continuousAt.preimage_mem_nhds (by simpa using hO))
    have hnear : q '' (V ∩ p ⁻¹' O) ∈ 𝓝 (0 : B) := by
      rw [← map_zero q, ← hq.map_nhds_eq]
      exact Filter.image_mem_map hsmall
    have hnear' : Subtype.val ⁻¹' (q '' (V ∩ p ⁻¹' O)) ∈
        𝓝 (0 : (q.comp p.ker.subtype).range) := preimage_coe_mem_nhds_subtype.mpr
          (mem_nhdsWithin_of_mem_nhds hnear)
    refine mem_of_superset hnear' ?_
    rintro ⟨b, y, rfl⟩ ⟨v, hv, hvy⟩
    change q v = q y.val at hvy
    have hz : v - y.val ∈ q.ker := by
      change q (v - y.val) = 0
      exact (map_sub q _ _).trans (sub_eq_zero.mpr hvy)
    let z : q.ker := ⟨v - y.val, hz⟩
    have hpz : p z.val = p v := by
      change p (v - y.val) = p v
      rw [map_sub, LinearMap.mem_ker.mp y.property, sub_zero]
    obtain ⟨w, hw, hfw⟩ := hOsub (a := f z) (show p z.val ∈ O from hpz ▸ hv.2)
    have hwv : p w.val = p v := (congrArg Subtype.val hfw).trans hpz
    have hvw : v - w.val ∈ p.ker := by
      change p (v - w.val) = 0
      exact (map_sub p _ _).trans (sub_eq_zero.mpr hwv.symm)
    refine ⟨⟨v - w.val, hvw⟩, hsub (hVW (show (v, w.val) ∈ V ×ˢ W from ⟨hv.1, hw⟩)), Subtype.ext ?_⟩
    change q (v - w.val) = q y.val
    rw [map_sub, LinearMap.mem_ker.mp w.property, sub_zero, hvy]

/-- For two open linear quotient maps with a common source, the restriction of either map
to the other kernel is strict exactly when the opposite restriction is strict. -/
theorem isStrictMap_comp_ker_subtype_iff
    (p : G →ₗ[R] A) (q : G →ₗ[R] B)
    (hp : IsOpenQuotientMap p) (hq : IsOpenQuotientMap q) :
    IsStrictMap (p.comp q.ker.subtype) ↔ IsStrictMap (q.comp p.ker.subtype) :=
  ⟨isStrictMap_comp_ker_subtype_of p q hp hq, isStrictMap_comp_ker_subtype_of q p hq hp⟩

end RiemannMasullo
