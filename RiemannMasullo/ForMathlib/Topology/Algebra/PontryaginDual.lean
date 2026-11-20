module

public import Mathlib.Topology.Algebra.PontryaginDual

@[expose] public section

namespace RiemannMasullo

/-- A character of a compact subgroup of a compact Hausdorff abelian group extends to the
whole group. The subgroup is presented by an injective continuous homomorphism.
Compact-group Fourier density and Tietze extension give density of the span of the
restricted characters. Orthogonality on the subgroup then gives the desired restriction. -/
theorem exists_pontryaginDual_extension_of_compact {H K : Type*}
    [CommGroup H] [TopologicalSpace H] [CompactSpace H]
    [CommGroup K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K] [CompactSpace K]
    (i : H →ₜ* K) (hi : Function.Injective i) (χ : PontryaginDual H) :
    ∃ ψ : PontryaginDual K, ∀ x, ψ (i x) = χ x := by
  sorry

end RiemannMasullo
