module

public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Compactness.Compact

/-! # Units of compact monoids -/

@[expose] public section

namespace RiemannMasullo

open Topology

/-- The units of a compact Hausdorff topological monoid form a compact space. -/
theorem compactSpace_units_of_compactSpace (M : Type*) [Monoid M]
    [TopologicalSpace M] [T2Space M] [ContinuousMul M] [CompactSpace M] :
    CompactSpace Mˣ := by
  refine IsClosedEmbedding.compactSpace ⟨Units.isEmbedding_embedProduct, ?_⟩
  have hrange : Set.range (Units.embedProduct M) =
      {p | p.1 * MulOpposite.unop p.2 = 1} ∩ {p | MulOpposite.unop p.2 * p.1 = 1} := by
    ext p
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.val_inv, u.inv_val⟩
    · rintro ⟨h, h'⟩
      exact ⟨⟨p.1, MulOpposite.unop p.2, h, h'⟩, by cases p; rfl⟩
  rw [hrange]
  exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd))
    continuous_const).inter (isClosed_eq
      ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)

end RiemannMasullo
