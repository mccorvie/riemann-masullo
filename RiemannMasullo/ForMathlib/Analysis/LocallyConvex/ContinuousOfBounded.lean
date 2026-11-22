module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.Complex.Basic

/-! # Continuity from the bornological seminorm criterion -/

noncomputable section

open Bornology Set

namespace RiemannMasullo

/-- A linear self-map on a bornological space is continuous if it preserves bounded sets. -/
public theorem continuous_of_bornological_image {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [PolynormableSpace ℂ E]
    (hborn : ∀ p : Seminorm ℂ E, (∀ B, IsVonNBounded ℂ B → BddAbove (p '' B)) → Continuous p)
    (L : E →ₗ[ℂ] E) (hb : ∀ B, IsVonNBounded ℂ B → IsVonNBounded ℂ (L '' B)) :
    Continuous L := by
  let h := PolynormableSpace.withSeminorms ℂ E
  refine h.continuous_of_continuous_comp L fun p ↦ hborn (p.val.comp L) fun B hB ↦ ?_
  change BddAbove ((fun x ↦ p.val (L x)) '' B)
  simpa only [Set.image_image] using h.isVonNBounded_iff_seminorm_bddAbove.mp (hb B hB) p


end RiemannMasullo
