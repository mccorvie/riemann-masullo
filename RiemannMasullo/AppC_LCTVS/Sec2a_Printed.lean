module

public import RiemannMasullo.AppC_LCTVS.Sec2a

/-! # Appendix C.2.2: the printed criterion for equality of the dual topologies -/

@[expose] public noncomputable section

namespace RiemannMasullo

/-- Paper: §C.2.2.2, p. 674. As printed: on the continuous dual of a Hausdorff
locally convex complex space E, the strong and Mackey topologies agree exactly when
E is barrelled. `strongDualityTopology_le_mackeyTopology` gives the comparison
that holds for every separating duality. See ERRATA F5. -/
def Printed.strongDualityTopology_eq_mackeyTopology_iff_barrelled : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [PolynormableSpace ℂ E] [T2Space E],
    strongDualityTopology (topDualPairing ℂ E) = mackeyTopology (topDualPairing ℂ E) ↔
      BarrelledSpace ℂ E

/-- Paper: §C.2.2.2, p. 674. Let E be the Banach space c₀ of complex sequences
tending to zero with the supremum norm. It is barrelled. On its dual ℓ¹ the strong
topology is the norm topology and the sum of all coordinates is a continuous functional.
It is represented by the constant sequence 1, which lies outside c₀. The continuous
dual for the Mackey topology of the pairing is c₀, so the topologies differ. -/
theorem Printed.strongDualityTopology_eq_mackeyTopology_iff_barrelled_false :
    ¬ Printed.strongDualityTopology_eq_mackeyTopology_iff_barrelled := by sorry

end RiemannMasullo
