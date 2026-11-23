module

public import RiemannMasullo.AppA_AlgebraicNT.Sec3

/-! # Appendix A.3: the printed Fourier formula for a translated p-adic ball -/

@[expose] public noncomputable section

namespace RiemannMasullo

open MeasureTheory Set

local instance printedSec3TranslatedFourierPadicMeasurableSpace (p : ℕ) [Fact p.Prime] :
    MeasurableSpace ℚ_[p] := borel _

/-- Paper: Example A.3.1.6, (A.3.1.5), p. 557.
As printed: for every prime, integer scale, translation and frequency, the transform of the
translated ball indicator equals the scaled unit-ball transform at the shifted frequency and
the scaled reciprocal-ball indicator times the positive character at `a * x`. The inverse of
`padicStandardCharacter` gives the paper's character, and `tamagawaFourier` conjugates it as on
p. 558. The zero-translation specialization is `padicTamagawaFourier_scaledIntegers`.
See ERRATA F217. -/
def Printed.padicTamagawaFourier_translatedScaledIntegers : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℤ) (a x : ℚ_[p]),
    let integers := Metric.closedBall (0 : ℚ_[p]) 1
    let f₀ := integers.indicator (fun _ ↦ (1 : ℂ))
    let f := ((fun t : ℚ_[p] ↦ a + (p : ℚ_[p]) ^ n * t) '' integers).indicator
      (fun _ ↦ (1 : ℂ))
    let ψ := fun t : ℚ_[p] ↦ (padicStandardCharacter p t)⁻¹
    let transform := tamagawaFourier (padicTamagawaMeasure p) ψ
    let scale := ((p : ℝ) ^ (-n) : ℂ)
    transform f x = scale * transform f₀ ((p : ℚ_[p]) ^ n * (x - a)) ∧
      transform f x = scale * (ψ (a * x) : ℂ) *
        (((fun t : ℚ_[p] ↦ (p : ℚ_[p]) ^ (-n) * t) '' integers).indicator (fun _ ↦ 1)) x

/-- Paper: Example A.3.1.6, (A.3.1.5), p. 557.
Take `p = 3`, `n = 0` and `a = 1/3` in `ℚ_[3]`. At `x = 0` the transform is the mass
one of the translated unit ball. The shifted unit-ball transform is zero at `-1/3`.
At `x = 1` the transform is `exp(-2πi/3)`, since the character is constant on the coset,
and the printed phase gives `exp(2πi/3)`. -/
theorem Printed.padicTamagawaFourier_translatedScaledIntegers_false :
    ¬ Printed.padicTamagawaFourier_translatedScaledIntegers := by
  sorry

end RiemannMasullo
