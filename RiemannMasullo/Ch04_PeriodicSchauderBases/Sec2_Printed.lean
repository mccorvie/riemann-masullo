module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec2

/-! # Chapter 4.2: the printed fixed-support periodization claims -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Function Set TopologicalSpace
open scoped Distributions

local notation "D[" K "]" => 𝓓_{K}(ℝ, ℂ)
local notation "quotientAt[" γ "]" => fun x : ℝ ↦ ((x / Real.log γ : ℝ) : AddCircle (1 : ℝ))

/-- Paper: Proposition 4.2.2.2(1), p. 171. As printed: for γ > 1, if a compact support
set has nonempty interior and maps onto the cyclic quotient, the induced periodization
on the fixed-support space modulo its kernel is surjective. This is the surjectivity
part of the stated isomorphism, in log coordinates. `compactIntervalPeriodization_quotient_equiv`
gives the strict-width interval case. See ERRATA F15. -/
def Printed.compactPeriodization_surjective : Prop :=
  ∀ (γ : ℝ) (hγ : 1 < γ) (K : Compacts ℝ), (interior (K : Set ℝ)).Nonempty →
    SurjOn (quotientAt[γ]) (K : Set ℝ) univ →
    Surjective ((cyclicPeriodizationCLM γ hγ).comp (compactLogProfileInclusion K))

/-- Paper: Proposition 4.2.2.2(1), p. 171. For γ > 1 take the multiplicative support
interval [1, γ], so K = [0, log γ] in log coordinates. It covers the quotient, but
every smooth function supported there vanishes at both endpoints. Its periodization
vanishes at the zero class, so the constant one is missed. -/
theorem Printed.compactPeriodization_surjective_false :
    ¬ Printed.compactPeriodization_surjective := by sorry

/-- Paper: Proposition 4.2.2.2(2), p. 171. As printed: for an admissible support
interval `b · [1/a, a]` contained in `[1/A₀, A₀]`, every kernel element is the difference
of a smooth function supported in `[exp(-A), exp A]` and its translate by γ, where
`A = |log A₀ - log γ|`. The variables and supports on the function side use log
coordinates. The strict-width case of the preceding part is
`compactIntervalPeriodization_quotient_equiv`. See ERRATA F15. -/
def Printed.compactIntervalPeriodization_kernel_support : Prop :=
  ∀ (γ : ℝ) (hγ : 1 < γ) (a b A₀ : ℝ), 1 < a → 0 < b → 0 < A₀ →
    let K : Compacts ℝ := ⟨Icc (Real.log b - Real.log a) (Real.log b + Real.log a), isCompact_Icc⟩
    (interior (K : Set ℝ)).Nonempty → SurjOn (quotientAt[γ]) (K : Set ℝ) univ →
    (K : Set ℝ) ⊆ Icc (-Real.log A₀) (Real.log A₀) →
    ∀ φ : D[K], cyclicPeriodizationCLM γ hγ (compactLogProfileInclusion K φ) = 0 →
      let A := |Real.log A₀ - Real.log γ|
      let Kₐ : Compacts ℝ := ⟨Icc (-A) A, isCompact_Icc⟩
      ∃ ψ : D[Kₐ], ∀ x : ℝ, ψ x - ψ (x + Real.log γ) = φ x

/-- Paper: Proposition 4.2.2.2(2), p. 171. Set a = A₀ = γ > 1 and b = 1. Then A = 0,
so every smooth function supported in the allowed singleton is zero. Take a nonzero
smooth bump u supported in `(0, log γ)` in log coordinates. The difference
`u(x) - u(x + log γ)` is nonzero, is supported in `[-log γ, log γ]`, and has zero
periodization by reindexing the sum. -/
theorem Printed.compactIntervalPeriodization_kernel_support_false :
    ¬ Printed.compactIntervalPeriodization_kernel_support := by sorry

end RiemannMasullo
