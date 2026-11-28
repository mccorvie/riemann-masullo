module

public import RiemannMasullo.ForMathlib.Analysis.Calculus.MeanValueDecay

@[expose] public noncomputable section
namespace RiemannMasullo

/-- A polynomial derivative envelope centered at a node gives the local exponential
Lipschitz bound, with an explicit constant depending only on its polynomial degree. -/
theorem norm_sub_le_local_exp_of_deriv_polynomial_envelope {b : ℝ → ℂ}
    (hb : Differentiable ℝ b) {D z : ℝ} (hD : 0 ≤ D) (n : ℕ)
    (hderiv : ∀ u, ‖deriv b u‖ ≤ D * (1 + |u - z|) ^ n) (x y : ℝ) :
    ‖b x - b y‖ ≤
      (D * ((8 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (1 / 8))) *
        |x - y| * Real.exp ((|x - z| + |y - z|) / 8) := by
  apply norm_sub_le_local_exp_of_deriv hb (by positivity)
  intro u
  have hn : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hp := (div_le_iff₀ hn).mp
    (Real.pow_div_factorial_le_exp ((1 + |u - z|) / 8) (by positivity) n)
  rw [div_pow] at hp
  have hp' := (div_le_iff₀ (by positivity : 0 < (8 : ℝ) ^ n)).mp hp
  have he : (1 + |u - z|) ^ n ≤
      ((8 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (1 / 8)) * Real.exp (|u - z| / 8) := by
    rw [show (1 + |u - z|) / 8 = 1 / 8 + |u - z| / 8 by ring, Real.exp_add] at hp'
    convert hp' using 1
    ring
  exact (hderiv u).trans ((mul_le_mul_of_nonneg_left he hD).trans_eq (mul_assoc _ _ _).symm)

end RiemannMasullo
