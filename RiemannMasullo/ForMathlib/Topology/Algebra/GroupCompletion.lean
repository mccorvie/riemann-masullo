module

public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.Group.Neighborhood
public import Mathlib.Topology.Algebra.Group.Subgroup

public section

open Filter Set Topology UniformSpace

namespace RiemannMasullo

/-- The completion of a quotient homomorphism of uniform additive commutative groups
is a quotient map onto its range with the subspace topology. -/
theorem isQuotientMap_rangeFactorization_completion_map {A B : Type*}
    [AddCommGroup A] [UniformSpace A] [IsUniformAddGroup A]
    [AddCommGroup B] [UniformSpace B] [IsUniformAddGroup B]
    (f : A →+ B) (hf : IsQuotientMap f) :
    IsQuotientMap (rangeFactorization (Completion.map f)) := by
  let F := f.completion hf.continuous
  have hF : Continuous F := f.continuous_completion hf.continuous
  have hfOpen := (AddMonoidHom.isOpenQuotientMap_of_isQuotientMap hf).isOpenMap
  change IsQuotientMap F.rangeRestrict
  refine IsOpenMap.isQuotientMap ?_ (hF.subtype_mk _) F.rangeRestrict_surjective
  rw [IsTopologicalAddGroup.isOpenMap_iff_nhds_zero, le_map_iff]
  intro U hU
  obtain ⟨V, hV, hVzero, hVU⟩ := exists_open_nhds_zero_half hU
  let W := f '' (((↑) : A → Completion A) ⁻¹' V)
  have hW : IsOpen W := hfOpen _ (hV.preimage (Completion.continuous_coe A))
  obtain ⟨O, hO, hOW⟩ := (Completion.isDenseInducing_coe (α := B)).isInducing.isOpen_iff.mp hW
  have hOzero : (0 : Completion B) ∈ O := by
    rw [← Completion.coe_zero (α := B)]
    change (0 : B) ∈ ((↑) : B → Completion B) ⁻¹' O
    rw [hOW]
    exact ⟨0, by simpa only [mem_preimage, Completion.coe_zero] using hVzero, map_zero f⟩
  refine mem_of_superset ((hO.preimage continuous_subtype_val).mem_nhds hOzero) ?_
  rintro ⟨_, x, rfl⟩ (hx : F x ∈ O)
  -- Approximate a preimage by a point of `A` and lift its image back into `V`.
  have hsub : Continuous (fun z : Completion A ↦ x - z) := continuous_const.sub continuous_id
  obtain ⟨a, haV, haO⟩ := (Completion.denseRange_coe (α := A)).exists_mem_open
    ((hV.preimage hsub).inter (hO.preimage hF))
    ⟨x, by simpa only [mem_inter_iff, mem_preimage, sub_self] using And.intro hVzero hx⟩
  have hfa : f a ∈ W := by
    rw [← hOW]
    change F (a : Completion A) ∈ O at haO
    rwa [f.completion_coe hf.continuous] at haO
  obtain ⟨b, hbV, hb⟩ := hfa
  refine ⟨x - (a : Completion A) + b, hVU _ haV _ hbV, Subtype.ext ?_⟩
  change F (x - (a : Completion A) + b) = F x
  rw [map_add, map_sub, f.completion_coe hf.continuous, f.completion_coe hf.continuous,
    hb, sub_add_cancel]

end RiemannMasullo
