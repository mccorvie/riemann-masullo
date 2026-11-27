module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

@[expose] public noncomputable section

namespace RiemannMasullo

/-- The nonnegative weight multiplying Hardy's Z in Selberg's mollification.
The gamma and exponential factors are Titchmarsh §10.10, p. 269, with δ=1/T,
up to an absolute constant. The finite Dirichlet polynomial is evaluated on
the critical line. -/
def spectralLineJet_selbergWeight (T N : ℕ) (b : ℕ → ℝ) (t : ℝ) : ℝ :=
  ‖Complex.Gamma (1 / 4 + (t : ℂ) / 2 * Complex.I)‖ * Real.exp ((Real.pi / 4 - 1 / (2 * T)) * t) *
    ‖∑ n ∈ Finset.Icc 1 N, ((b n / Real.sqrt n : ℝ) : ℂ) *
      Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ^ 2

/-- The Selberg weight is continuous and nonnegative for every real coefficient sequence. -/
theorem spectralLineJet_selbergWeight_spec (T N : ℕ) (b : ℕ → ℝ) :
    Continuous (spectralLineJet_selbergWeight T N b) ∧ ∀ t, 0 ≤ spectralLineJet_selbergWeight T N b t := by
  have hg : Continuous (fun t : ℝ ↦ Complex.Gamma (1 / 4 + (t : ℂ) / 2 * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply ContinuousAt.comp (g := Complex.Gamma) (f := fun x : ℝ ↦ 1 / 4 + (x : ℂ) / 2 * Complex.I)
    · apply Complex.continuousAt_Gamma
      intro m he
      have h := congrArg Complex.re he
      norm_num [Complex.div_ofNat_re, Complex.div_ofNat_im] at h
      linarith [Nat.cast_nonneg (α := ℝ) m]
    · fun_prop
  constructor
  · unfold spectralLineJet_selbergWeight
    apply (hg.norm.mul (by fun_prop)).mul
    fun_prop
  · intro t
    unfold spectralLineJet_selbergWeight
    positivity

end RiemannMasullo
