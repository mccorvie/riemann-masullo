module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 27. For positive k, l, m, v the equal-frequency pairs reindex as the positive multiples
of km/gcd(kv,lm) in the series of any complex-valued function.
Titchmarsh, §10.11, p. 270, diagonal parametrization. -/
theorem resonance (k l m v : ℕ) (hk : 0 < k) (hl : 0 < l) (hm : 0 < m) (hv : 0 < v) :
    ∀ f : ℝ → ℂ, (∑' ij : ℕ × ℕ, if freq ij.1 k l = freq ij.2 m v then
      f (freq ij.1 k l) else 0) = ∑' j : ℕ, f (((j+1 : ℕ) : ℝ)/ratio k l m v) := by
  sorry

end RiemannMasullo.Selberg
