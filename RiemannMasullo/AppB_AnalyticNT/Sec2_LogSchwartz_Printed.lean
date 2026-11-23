module

public import RiemannMasullo.AppB_AnalyticNT.Sec2

/-! # Appendix B.2: printed assertions about growth and decay in logarithmic coordinates -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter Set
open scoped Asymptotics SchwartzMap

/-- Paper: Remark B.2.1.2, p. 593.
As printed: for a Schwartz logarithmic profile, the condition that every derivative is
`O(exp(-x))` as `x` tends to positive infinity suffices for forward semi-exponential decay.
This is the false direction of the printed correspondence. The equivalence with all Schwartz
weights is `forwardSemiExponentialDecay_iff_weighted_schwartz`. See ERRATA F224. -/
def Printed.forwardSemiExponentialDecay_of_single_rate : Prop :=
  ∀ f : 𝓢(ℝ, ℂ),
    (∀ j : ℕ, (iteratedDeriv j (f : ℝ → ℂ)) =O[atTop] fun x ↦ Real.exp (-x)) →
    ForwardSemiExponentialDecay f

/-- Paper: Remark B.2.1.2, p. 593.
Use the smooth cutoff `χ(t) = Real.smoothTransition (t - 1)`, zero for `t ≤ 1` and one
for `t ≥ 2`.
The logarithmic profile of `φ(t) = χ(t)/t` is Schwartz. For `x ≥ log 2` its `j`-th
derivative is `(-1)^j exp(-x)`, and the zeroth derivative fails the rate `exp(-2x)`. -/
theorem Printed.forwardSemiExponentialDecay_of_single_rate_false :
    ¬ Printed.forwardSemiExponentialDecay_of_single_rate := by
  sorry

/-- Paper: Remark B.2.1.3, p. 593.
As printed: if a complex-valued function on the positive reals has at most polynomial
growth in the logarithmic coordinate, then for every natural exponent `N` it admits a bound
`C_N |log t|^N` for all positive `t`. This is the false direction of the identification with
the usual polynomial growth condition on the real line. See ERRATA F224. -/
def Printed.logPolynomialGrowth_bound_for_every_exponent : Prop :=
  ∀ f : Ioi (0 : ℝ) → ℂ,
    (∃ (M : ℕ) (C : ℝ), 0 < C ∧ ∀ t : Ioi (0 : ℝ),
      ‖f t‖ ≤ C * (1 + |Real.log t.val|) ^ M) →
    ∀ N : ℕ, ∃ C > (0 : ℝ), ∀ t : Ioi (0 : ℝ), ‖f t‖ ≤ C * |Real.log t.val| ^ N

/-- Paper: Remark B.2.1.3, p. 593.
Take the constant function `1`, with degree zero and constant one in the usual polynomial
growth bound. The printed bound with `N = 1` at `t = 1` would give `1 ≤ 0`. -/
theorem Printed.logPolynomialGrowth_bound_for_every_exponent_false :
    ¬ Printed.logPolynomialGrowth_bound_for_every_exponent := by
  sorry

/-- Paper: Lemma B.2.1.4(1), p. 593.
As printed: every Schwartz profile on the positive reals with backward semi-exponential decay
has a Schwartz zero extension to the real line. The smoothness assertion is
`contDiff_zeroExtension_of_backwardSemiExponentialDecay`. The stronger decay hypothesis
in part (3) gives `exists_schwartz_zeroExtension_of_exponentialDecay`. See ERRATA F224. -/
def Printed.exists_schwartz_zeroExtension_of_backwardSemiExponentialDecay : Prop :=
  ∀ f : 𝓢(ℝ, ℂ), BackwardSemiExponentialDecay f →
    ∃ g : 𝓢(ℝ, ℂ), (g : ℝ → ℂ) = (Ioi (0 : ℝ)).indicator (fun t ↦ f (Real.log t))

/-- Paper: Lemma B.2.1.4(1), p. 593.
Take the logarithmic profile `f(x) = χ(exp x) exp(-x)`, with `χ(t) = Real.smoothTransition (t - 1)`.
It vanishes for `x ≤ 0` and is Schwartz in `x`. Its zero extension in the `t` coordinate
equals `1/t` for `t ≥ 2`, so the weight `t²` makes it unbounded. -/
theorem Printed.exists_schwartz_zeroExtension_of_backwardSemiExponentialDecay_false :
    ¬ Printed.exists_schwartz_zeroExtension_of_backwardSemiExponentialDecay := by
  sorry

end RiemannMasullo
