module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

open MeasureTheory Set

namespace RiemannMasullo.Selberg

/-- Card 25. For N ≥ 2, indices in [1,N], and q ≥ 0, the double series of integrals of the
absolute Gaussian pair terms converges.
Titchmarsh, §10.11, p. 270, absolute Fubini for the Gaussian double series. -/
theorem pair_summable (N k l m v : ℕ) (hN : 2 ≤ N) (hk : k ∈ D N) (hl : l ∈ D N)
    (hm : m ∈ D N) (hv : v ∈ D N) (q : ℝ) (hq : 0 ≤ q) :
    Summable (fun ij : ℕ × ℕ ↦ ∫ x in Ioi (1 : ℝ), x^(-q)*Real.exp
      (-Real.pi*Real.sin (1/(H N : ℝ)) * ((freq ij.1 k l)^2+(freq ij.2 m v)^2)*x^2)) := by
  sorry

/-- Card 25, second part (added after the referee's check of the plan). Each absolute Gaussian
pair term is integrable on (1, ∞). The summability of the integrals in `pair_summable` does not
by itself allow the series to be exchanged with the integral, because the integral of a function
that is not integrable is zero in Lean; cards 26 and 28 use both statements.
Titchmarsh, §10.11, p. 270. -/
theorem pair_integrable (N k l m v : ℕ) (hN : 2 ≤ N) (hk : k ∈ D N) (hl : l ∈ D N)
    (hm : m ∈ D N) (hv : v ∈ D N) (q : ℝ) (hq : 0 ≤ q) (ij : ℕ × ℕ) :
    IntegrableOn (fun x : ℝ ↦ x^(-q)*Real.exp
      (-Real.pi*Real.sin (1/(H N : ℝ)) * ((freq ij.1 k l)^2+(freq ij.2 m v)^2)*x^2)) (Ioi 1) := by
  sorry

end RiemannMasullo.Selberg
