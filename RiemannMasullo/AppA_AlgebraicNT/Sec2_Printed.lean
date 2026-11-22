module

public import RiemannMasullo.AppA_AlgebraicNT.Sec2

/-! # Appendix A.2.1: rational specialization of the printed disjointness claim -/

@[expose] public noncomputable section

namespace RiemannMasullo

open NumberField InfinitePlace.Completion
open scoped NumberField.AdeleRing Pointwise

/-- Paper: §A.2.1 and Definition A.2.1.1, p. 545. Every nonzero diagonal translate
of the displayed adelic fundamental domain is disjoint from it.
Deviation: This is the specialization to ℚ with integral basis 1 and its unique real
place, using the absolute value in (A.2.1.1) on the real coefficient. The general
formula does not specify the scalar domain of its coefficients. See ERRATA F4. -/
def Printed.ratAdeleFundamentalDomain_disjoint : Prop :=
  let D : Set 𝔸[ℚ] := {a |
    |extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (a.1 Rat.infinitePlace)| ∈
      Set.Ico (0 : ℝ) 1 ∧ a ∈ integralAdelesOutside ℚ ∅}
  ∀ q : ℚ, q ≠ 0 → Disjoint (algebraMap ℚ 𝔸[ℚ] q +ᵥ D) D

/-- Paper: §A.2.1 and Definition A.2.1.1, p. 545. Take q = 1. The adele with
real component 1/2 and finite component zero belongs to D. Subtracting the diagonal
one leaves real component -1/2 and finite components -1, so the difference also
belongs to D. Both coefficients are rational already. -/
theorem Printed.ratAdeleFundamentalDomain_disjoint_false :
    ¬ Printed.ratAdeleFundamentalDomain_disjoint := by sorry

end RiemannMasullo
