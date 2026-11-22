module

public import RiemannMasullo.AppC_LCTVS.Sec2a_part2

/-! # Appendix C.2.3: the printed assertion about projective tensor embeddings -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Topology

/-- Paper: §C.2.3.2, after (C.2.3.15), p. 679. As printed: the projective tensor
product of two topological embeddings is a topological embedding. This is the
uncompleted embedding assertion of the claimed analogue of Lemma C.2.3.5(1).
The projective quotient-map result is `projectiveTensorMap_isQuotientMap`.
See ERRATA F7. -/
def Printed.projectiveTensorMap_isEmbedding : Prop :=
  ∀ (E₁ E₂ F₁ F₂ : Type)
    [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁] [PolynormableSpace ℂ E₁] [T2Space E₁]
    [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂] [PolynormableSpace ℂ E₂] [T2Space E₂]
    [AddCommGroup F₁] [Module ℂ F₁] [TopologicalSpace F₁] [PolynormableSpace ℂ F₁] [T2Space F₁]
    [AddCommGroup F₂] [Module ℂ F₂] [TopologicalSpace F₂] [PolynormableSpace ℂ F₂] [T2Space F₂]
    (T₁ : E₁ →L[ℂ] F₁) (T₂ : E₂ →L[ℂ] F₂),
    IsEmbedding T₁ → IsEmbedding T₂ →
      IsEmbedding (projectiveTensorMap T₁.toLinearMap T₂.toLinearMap)

/-- Paper: §C.2.3.2, after (C.2.3.15), p. 679. Take the inclusion of H, the closed
span of the Rademacher functions `rₙ(t) = (-1)^(⌊2^(n+1) t⌋)` in complex L¹[0,1],
and the identity on complex ℓ²(ℕ). The coefficient map H → ℓ² sends rₙ to the nth
unit vector and is bounded by the Khintchine inequality. If the tensor map were an
embedding, Hahn–Banach applied to its induced functional would extend the coefficient
map to L¹. The first m coordinate functionals of such an extension would be represented
by L∞ functions g₁, …, gₘ with pointwise ℓ² norm bounded by the same operator norm C.
The identities `∫ rⱼ gⱼ = 1` would give `m ≤ C √m` for all m. -/
theorem Printed.projectiveTensorMap_isEmbedding_false :
    ¬ Printed.projectiveTensorMap_isEmbedding := by sorry

end RiemannMasullo
