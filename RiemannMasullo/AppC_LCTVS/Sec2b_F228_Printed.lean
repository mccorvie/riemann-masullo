module

public import RiemannMasullo.AppC_LCTVS.Sec2b

/-! # Appendix C.2.4: the printed continuity claim for the strong-dual pairing -/

@[expose] public noncomputable section

namespace RiemannMasullo

universe u v

/-- Paper: After (C.2.4.9), p. 691. As printed: for every complete nuclear Hausdorff
locally convex complex space E, a continuous linear map T to its strong dual
makes (x, y) ↦ (Ty)(x) jointly continuous. This is the continuity clause of the
specialization. The statement `schwartz_kernel_series` assumes joint continuity.
See ERRATA F228. -/
def Printed.strongDual_pairing_continuous : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E] [CompleteSpace E],
    IsNuclearTVS.{v, u} E → ∀ T : E →L[ℂ] StrongDual ℂ E,
      Continuous (fun z : E × E ↦ T z.2 z.1)

/-- Paper: After (C.2.4.9), p. 691. Take E = ω × φ, where ω = ℂ^ℕ has the product
topology and φ = ℂ^(ℕ) has the finest locally convex topology. Both factors are
complete and nuclear. Set T(y, b)(x, a) = ∑ₙ aₙ yₙ. The φ-projection of each
bounded set is supported on finitely many coordinates, so T is continuous in the
strong dual topology. Every zero-neighborhood in ω leaves some coordinate
unrestricted, and every zero-neighborhood in φ contains a nonzero multiple of its
basis vector. Hence the pairing is unbounded on every product of zero-neighborhoods. -/
theorem Printed.strongDual_pairing_continuous_false :
    ¬ Printed.strongDual_pairing_continuous := by
  sorry

end RiemannMasullo
