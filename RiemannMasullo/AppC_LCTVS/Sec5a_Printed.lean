module

public import RiemannMasullo.AppC_LCTVS.Sec5a

/-! # Appendix C.5.1: the printed Lipschitz claim for a weakly differentiable map -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology

universe u

/-- Paper: Lemma C.5.1.13(1), p. 726. As printed: for a weakly continuously
differentiable map on an open subset of kᵈ, where k is ℝ or ℂ and d ≥ 1, one
bounded set contains all the normalized increments in (C.5.1.19) for distances
at most one. This is the Lipschitz clause. The continuity consequence is
`WeaklyContDiffOn.continuousOn`. See ERRATA F229. -/
def Printed.weaklyContDiffOn_lipschitz : Prop :=
  let over (k : Type) [RCLike k] [NormedAlgebra k ℂ] : Prop :=
    ∀ d : ℕ, 1 ≤ d →
      ∀ (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
        [PolynormableSpace ℂ E] [T2Space E],
        let W := EuclideanSpace k (Fin d)
        ∀ (Ω : Set W), IsOpen Ω → ∀ (f : W → E), WeaklyContDiffOn k f Ω →
          ∃ B : Set E, IsVonNBounded ℂ B ∧
            ∀ x' ∈ Ω, ∀ x ∈ Ω, x' ≠ x → ‖x' - x‖ ≤ 1 →
              ((‖x' - x‖⁻¹ : ℝ) : ℂ) • (f x' - f x) ∈ B
  over ℝ ∧ over ℂ

/-- Paper: Lemma C.5.1.13(1), p. 726. Take k = ℝ, d = 1, Ω = ℝ, E = ℂ,
and f(x) = x². Its weak differential is the jointly continuous map
(x, v) ↦ 2xv under the identification of ℂ with its weak completion.
The normalized increments for x' = x + 1 are 2x + 1, an unbounded set. -/
theorem Printed.weaklyContDiffOn_lipschitz_false :
    ¬ Printed.weaklyContDiffOn_lipschitz := by
  sorry

end RiemannMasullo
