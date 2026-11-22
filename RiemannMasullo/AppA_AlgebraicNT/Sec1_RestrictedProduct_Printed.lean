module

public import RiemannMasullo.AppA_AlgebraicNT.Sec1

/-! # Appendix A.1: the printed restricted-product openness claim -/

@[expose] public noncomputable section

namespace RiemannMasullo

open scoped Classical RestrictedProduct

/-- Paper: Lemma A.1.1.2(5), p. 540. As printed: for any finite part of the index set,
an open box on that part times the distinguished subgroups on its complement is open in the
restricted product. `restrictedProduct_topology` requires open distinguished subgroups on the
complement. See ERRATA F1.
Deviation: The indexing preamble on p. 539 uses a Cartesian product where its conditions
require a partition into exceptional and ordinary indices. The partition on p. 540 is explicit. -/
def Printed.restrictedProduct_openBox : Prop :=
  ∀ (ι : Type) (G : ι → Type) [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)] [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)]
    (K : (i : ι) → Subgroup (G i)) (I₀ : Finset ι),
    (∀ i ∈ I₀, K i = ⊥) →
    (∀ i ∉ I₀, IsCompact (K i : Set (G i)) ∧ IsOpen (K i : Set (G i))) →
    ∀ (J : Finset ι) (U : (i : ι) → Set (G i)), (∀ i ∈ J, IsOpen (U i)) →
      IsOpen {x : Πʳ i, [G i, K i] | (∀ i ∈ J, x i ∈ U i) ∧ ∀ i ∉ J, x i ∈ K i}

/-- Paper: Lemma A.1.1.2(5), p. 540. Take a single factor `Multiplicative ℝ`, with
that index in I₀ and its distinguished subgroup trivial. Take J empty. The restricted
product is homeomorphic to ℝ and the box corresponds to the non-open singleton `{0}`. -/
theorem Printed.restrictedProduct_openBox_false : ¬ Printed.restrictedProduct_openBox := by sorry

end RiemannMasullo
