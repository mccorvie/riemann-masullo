module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2

/-! # Appendix D.3.3: the printed countable boundedness test -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology Filter Function Set
open scoped NNReal

/-- Paper: Proposition D.3.3.10(3), p. 807. As printed: a set of decay functions is
bounded precisely when its weighted images are bounded at each exponent in a countable
subset with both endpoints of the interval as accumulation points. The endpoints are taken
in the extended real line to include infinite endpoints. The countable test in
`modulatedExponentialDecay_bounded_iff_countable_twists` requires exponents on both sides
of each exponent of the interval, allowing equality. See ERRATA F12. -/
def Printed.modulatedExponentialDecay_bounded_iff_countable_twists : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G),
    IsModulation m → RightInverse τ m →
    ∀ (I : Set ℝ), OrdConnected I → I.Nonempty →
    ∀ (B : Set (ModulatedExponentialDecay m I)) (J : Set I), J.Countable →
      let ends := (fun x : ℝ ↦ (x : EReal)) '' I
      let tests := (fun a : I ↦ ((a : ℝ) : EReal)) '' J
      AccPt (sInf ends) (𝓟 tests) → AccPt (sSup ends) (𝓟 tests) →
        (IsVonNBounded ℂ B ↔
          ∀ a ∈ J, IsVonNBounded ℂ (modulatedExponentialDecayTwist m I a '' B))

/-- Paper: Proposition D.3.3.10(3), p. 807. Take the positive real multiplicative group,
with identity modulation and section, I = [0,1] and J the rationals in (0,1). For a
smooth bump ψ on ℝ supported in [-1,1] with ψ(0) = 1, take B to consist of the functions
with log profiles `fₙ(x) = exp(-n) ψ(x - n)`. The a-twists tend to zero in Schwartz space
for each a < 1, by exponential decay in n dominating the polynomial seminorms. The
1-twist takes the value 1 at x = n, so its seminorm `supₓ |x g(x)|` is at least n. -/
theorem Printed.modulatedExponentialDecay_bounded_iff_countable_twists_false :
    ¬ Printed.modulatedExponentialDecay_bounded_iff_countable_twists := by sorry

end RiemannMasullo
