module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1c

/-! # Appendix D.1.6: the printed local compactness claim for the dual hom group -/

@[expose] public noncomputable section

namespace RiemannMasullo

universe u

/-- Paper: Lemma D.1.6.4, p. 766. As printed: for every Hausdorff locally compact
abelian G, the group of continuous homomorphisms from its Pontryagin dual to the
dual of ℝ is locally compact in the compact-open topology. This is the local
compactness clause. The canonical isomorphism is `lcaTopologicalLie_dual`.
See ERRATA F231. -/
def Printed.lcaTopologicalLie_dual_locallyCompact : Prop :=
  ∀ (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G],
    LocallyCompactSpace (PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ))

/-- Paper: Lemma D.1.6.4, p. 766. Take G to be the countable product of circles.
Its dual is the discrete direct sum of countably many copies of ℤ. The hom group
from that direct sum to the dual of ℝ is ℝ^ℕ in the product topology, since compact
sets in the discrete direct sum are finite. Every neighborhood of zero contains a
basic neighborhood with an unrestricted coordinate, so it cannot be compact. -/
theorem Printed.lcaTopologicalLie_dual_locallyCompact_false :
    ¬ Printed.lcaTopologicalLie_dual_locallyCompact := by
  sorry

end RiemannMasullo
