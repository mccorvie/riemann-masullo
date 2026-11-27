module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 19. On the critical line the weighted Hardy function is π^(1/4) times the completed zeta
function, the exponential weight, and the squared norm of the Dirichlet polynomial.
Titchmarsh, §10.10, p. 269, definition of F, and §10.1, p. 254. -/
theorem archimedean_normalization (T N : ℕ) (b : ℕ → ℝ) (t : ℝ) :
    ((spectralLineJet_selbergWeight T N b t * hardyZ t : ℝ) : ℂ) =
      ((Real.pi ^ (1/4 : ℝ) * Real.exp ((Real.pi/4-1/(2*(T : ℝ)))*t) : ℝ) : ℂ) *
      completedRiemannZeta (1/2+(t : ℂ)*Complex.I) *
      ((‖∑ n ∈ D N, ((b n / Real.sqrt n : ℝ) : ℂ)*osc (-t*Real.log n)‖^2 : ℝ) : ℂ) := by
  sorry

end RiemannMasullo.Selberg
