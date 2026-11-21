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

open scoped Pointwise Uniformity in
/-- The map on completions induced by an open quotient of uniform additive groups is
surjective if the source is first countable. -/
theorem completion_map_surjective_of_isOpenQuotientMap
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [UniformSpace A] [UniformSpace B]
    [IsUniformAddGroup A] [IsUniformAddGroup B] [FirstCountableTopology A]
    (f : A →+ B) (hf : IsOpenQuotientMap f) : Function.Surjective (Completion.map f) := by
  classical
  obtain ⟨W, hW, hadd⟩ := IsTopologicalAddGroup.exists_antitone_basis_nhds_zero A
  let j : B →+ Completion B := Completion.toCompl
  let d : A →+ Completion B := j.comp f
  let V (n : ℕ) : Set (Completion B) := closure (d '' W n)
  have hd : Continuous d := Completion.continuous_toCompl.comp hf.continuous
  have hV (n : ℕ) : V n ∈ 𝓝 (0 : Completion B) := by
    have hn : f '' W n ∈ 𝓝 (0 : B) := by
      simpa only [map_zero] using hf.isOpenMap.image_mem_nhds (hW.mem n)
    change closure ((Completion.coe' ∘ f) '' W n) ∈ 𝓝 (0 : Completion B)
    rw [Set.image_comp, ← Completion.coe_zero]
    exact Completion.isDenseInducing_coe.closure_image_mem_nhds hn
  have hVbasis : (𝓝 (0 : Completion B)).HasBasis (fun _ : ℕ ↦ True) V := by
    refine ⟨fun S ↦ ⟨fun hS ↦ ?_, fun ⟨n, _, hn⟩ ↦ mem_of_superset (hV n) hn⟩⟩
    obtain ⟨C, hC, hclosed, hCS⟩ := exists_mem_nhds_isClosed_subset hS
    have hpre : d ⁻¹' C ∈ 𝓝 (0 : A) :=
      hd.continuousAt.preimage_mem_nhds (by simpa only [map_zero] using hC)
    obtain ⟨n, hn⟩ := hW.mem_iff.mp hpre
    exact ⟨n, trivial, (closure_minimal (image_subset_iff.mpr hn) hclosed).trans hCS⟩
  have hnear {r : Completion B} {S : Set A} (hr : r ∈ closure (d '' S)) (n : ℕ) :
      ∃ w ∈ S, r - d w ∈ V n := by
    have hn : (fun y : Completion B ↦ r - y) ⁻¹' V n ∈ 𝓝 r :=
      (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
        (by simpa only [Pi.sub_apply, id_eq, sub_self] using hV n)
    obtain ⟨_, hw, w, hwS, rfl⟩ := mem_closure_iff_nhds.mp hr _ hn
    exact ⟨w, hwS, hw⟩
  intro z
  have hdense : DenseRange d :=
    Completion.denseRange_coe.comp hf.surjective.denseRange Completion.continuous_toCompl
  obtain ⟨x, _, hx⟩ := hnear (S := univ) (by simpa only [image_univ] using hdense z) 1
  -- Each correction shrinks the residual and lies in the corresponding source neighborhood.
  have hstep (n : ℕ) (a : {a : A // z - d a ∈ V (n + 1)}) :
      ∃ w ∈ W (n + 1), z - d (a.val + w) ∈ V (n + 2) := by
    obtain ⟨w, hw, hclose⟩ := hnear a.property (n + 2)
    exact ⟨w, hw, by rwa [map_add, ← sub_sub]⟩
  choose w hw hres using hstep
  let a : ∀ n : ℕ, {a : A // z - d a ∈ V (n + 1)} := fun n ↦
    Nat.recOn n ⟨x, hx⟩ (fun k a ↦ ⟨a.val + w k a, hres k a⟩)
  let u (n : ℕ) : A := (a n).val
  have hdiff (n : ℕ) : u (n + 1) - u n ∈ W (n + 1) := by
    change u n + w n (a n) - u n ∈ _
    simpa only [add_sub_cancel_left] using hw n (a n)
  have hu : CauchySeq u := by
    have hb : (𝓤 A).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ {p : A × A | p.1 - p.2 ∈ W n}) := by
      rw [uniformity_eq_comap_nhds_zero_swapped]
      exact hW.toHasBasis.comap _
    refine hb.cauchySeq_iff'.mpr fun n _ ↦ ⟨n, fun m hnm ↦ ?_⟩
    change u m - u n ∈ W n
    refine Nat.decreasingInduction' (fun k _ _ hk ↦ ?_) hnm ?_
    · refine hadd k ⟨_, hdiff k, _, hk, ?_⟩
      change (u (k + 1) - u k) + (u m - u (k + 1)) = u m - u k
      rw [add_comm, sub_add_sub_cancel]
    · simpa only [sub_self] using mem_of_mem_nhds (hW.mem m)
  have hz : Tendsto (fun n ↦ d (u n)) atTop (𝓝 z) := by
    have hresidual : Tendsto (fun n ↦ z - d (u n)) atTop (𝓝 0) :=
      hVbasis.tendsto_right_iff.mpr fun n _ ↦ eventually_atTop.mpr
        ⟨n, fun m hm ↦ closure_mono (image_mono (hW.antitone (hm.trans (Nat.le_succ m))))
          (a m).property⟩
    simpa only [sub_sub_cancel, sub_zero] using
      (tendsto_const_nhds (x := z)).sub hresidual
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete
    ((Completion.uniformContinuous_coe A).comp_cauchySeq hu)
  refine ⟨y, tendsto_nhds_unique ?_ hz⟩
  have hlim : Tendsto (fun n ↦ Completion.map f (u n : Completion A)) atTop
      (𝓝 (Completion.map f y)) :=
    Completion.continuous_map.continuousAt.tendsto.comp hy
  have hmap (b : A) : Completion.map f (b : Completion A) = d b :=
    Completion.map_coe (uniformContinuous_addMonoidHom_of_continuous hf.continuous) b
  simpa only [hmap] using hlim

end RiemannMasullo
