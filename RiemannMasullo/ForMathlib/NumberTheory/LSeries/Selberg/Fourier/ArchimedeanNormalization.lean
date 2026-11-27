module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

private theorem norm_gamma_critical_line (t : ℝ) :
    ‖Complex.Gamma (1 / 4 + (t : ℂ) / 2 * Complex.I)‖ =
      Real.pi ^ (1 / 4 : ℝ) * ‖Complex.Gammaℝ (1 / 2 + (t : ℂ) * Complex.I)‖ := by
  let s : ℂ := 1 / 2 + (t : ℂ) * Complex.I
  have hhalf : s / 2 = 1 / 4 + (t : ℂ) / 2 * Complex.I := by dsimp [s]; ring
  have hre : (-s / 2).re = -(1 / 4 : ℝ) := by
    norm_num [s, Complex.div_ofNat_re]
  change _ = Real.pi ^ (1 / 4 : ℝ) * ‖Complex.Gammaℝ s‖
  rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    hhalf, hre, ← mul_assoc, ← Real.rpow_add Real.pi_pos]
  simp

/-- Card 19. On the critical line the weighted Hardy function is π^(1/4) times the completed zeta
function, the exponential weight, and the squared norm of the Dirichlet polynomial.
Titchmarsh, §10.10, p. 269, definition of F, and §10.1, p. 254. -/
theorem archimedean_normalization (T N : ℕ) (b : ℕ → ℝ) (t : ℝ) :
    ((spectralLineJet_selbergWeight T N b t * hardyZ t : ℝ) : ℂ) =
      ((Real.pi ^ (1/4 : ℝ) * Real.exp ((Real.pi/4-1/(2*(T : ℝ)))*t) : ℝ) : ℂ) *
      completedRiemannZeta (1/2+(t : ℂ)*Complex.I) *
      ((‖∑ n ∈ D N, ((b n / Real.sqrt n : ℝ) : ℂ)*osc (-t*Real.log n)‖^2 : ℝ) : ℂ) := by
  have phase (x : ℝ) : Complex.exp (-((t * x : ℝ) : ℂ) * Complex.I) = osc (-t * x) := by
    unfold osc
    congr 1
    push_cast
    ring
  have hden : (‖Complex.Gammaℝ (1 / 2 + (t : ℂ) * Complex.I)‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos (by simp)))
  have hhardy := (eq_div_iff hden).mp (ofReal_hardyZ t)
  simp only [spectralLineJet_selbergWeight, D, phase]
  simp only [norm_gamma_critical_line, Complex.ofReal_mul, ← hhardy]
  ac_rfl

end RiemannMasullo.Selberg
