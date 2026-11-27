module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

open Classical

namespace RiemannMasullo.Selberg

/-- Card 31. With the first frequency fixed, the reciprocal gaps between its square and lower
squared frequencies sum to at most N³(1 + log((i+1)kv))/(i+1).
Titchmarsh, §10.16, p. 274, reciprocal differences. -/
theorem gap_harmonic (N k l m v i : ℕ) (hk : k ∈ D N) (hl : l ∈ D N)
    (hm : m ∈ D N) (hv : v ∈ D N) :
    let M := (i+1)*k*v
    (∑ j ∈ (Finset.range M).filter (fun j ↦ (j+1)*l*m < M),
      |(freq i k l)^2-(freq j m v)^2|⁻¹) ≤
      (N : ℝ)^3 / ((i : ℝ)+1) * (1+Real.log M) := by
  sorry

end RiemannMasullo.Selberg
