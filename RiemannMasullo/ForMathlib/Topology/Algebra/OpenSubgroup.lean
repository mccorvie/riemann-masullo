module

public import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Topology.Separation.Regular

@[expose] public section

open Filter Set Topology
open scoped Pointwise

namespace RiemannMasullo

/-- Van Dantzig's theorem. Every identity neighborhood in a totally disconnected,
locally compact Hausdorff group contains a compact open subgroup. -/
theorem exists_compact_openSubgroup_sub_mem_nhds {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] {U : Set G} (hU : U ∈ 𝓝 1) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U := by
  obtain ⟨K, hK, hKU, hKcompact⟩ := local_compact_nhds hU
  obtain ⟨W, ⟨hW, hOne⟩, hWK⟩ := (nhds_basis_isClopen (1 : G)).mem_iff.mp hK
  have hWcompact := hKcompact.of_isClosed_subset hW.isClosed hWK
  let H := MulAction.stabilizer G W
  have hsubset : (H : Set G) ⊆ W := by
    intro g hg
    have hgW : g • W = W := MulAction.mem_stabilizer_iff.mp hg
    simpa [hgW, smul_eq_mul] using (smul_mem_smul_set (a := g) hOne)
  -- Compactness makes both translations preserve inclusion uniformly near the identity.
  let O : Set (G × G) := {p | p.1 * p.2 ∈ W ∧ p.1⁻¹ * p.2 ∈ W}
  have hO : IsOpen O := (hW.isOpen.preimage continuous_mul).inter
    (hW.isOpen.preimage (continuous_fst.inv.mul continuous_snd))
  have honeW : ({1} : Set G) ×ˢ W ⊆ O := by
    rintro ⟨g, w⟩ ⟨hg, hw⟩
    change g = 1 at hg
    subst g
    simpa [O] using hw
  obtain ⟨V, T, hV, _, hOneV, hWT, hVT⟩ :=
    generalized_tube_lemma isCompact_singleton hWcompact hO honeW
  have hHopen : IsOpen (H : Set G) := by
    apply H.isOpen_of_mem_nhds (g := 1)
    refine mem_of_superset (hV.mem_nhds (hOneV (mem_singleton 1))) fun g hg ↦ ?_
    apply MulAction.mem_stabilizer_iff.mpr
    refine subset_antisymm (smul_set_subset_iff.mpr ?_) ?_
    · exact fun w hw ↦ (hVT (mk_mem_prod hg (hWT hw))).1
    · intro w hw
      exact mem_smul_set_iff_inv_smul_mem.mpr (hVT (mk_mem_prod hg (hWT hw))).2
  let J : OpenSubgroup G := ⟨H, hHopen⟩
  exact ⟨J, hWcompact.of_isClosed_subset J.isClosed hsubset, hsubset.trans (hWK.trans hKU)⟩

end RiemannMasullo
