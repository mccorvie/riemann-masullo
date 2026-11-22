module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3b

/-! # §5.3.3: the printed logarithmic change of exponent interval -/

@[expose] public noncomputable section

open Set
open scoped NNReal

namespace RiemannMasullo

/-- Paper: Example 5.3.3.1, p. 249. The change of variable t = exp x is
claimed to identify the log(I)-decay space on ℝ with the I-decay space on
the positive multiplicative reals as topological complex vector spaces.
Deviation: The page allows any nonempty connected real interval. We record
the coordinate-change assertion where its real logarithm is defined on all
of I. The repaired statement is `positiveRealExponentialDecay_log_equiv`.
See ERRATA F176. -/
def Printed.positiveRealExponentialDecay_log_equiv : Prop :=
  ∀ (I : Set ℝ), OrdConnected I → I.Nonempty → I ⊆ Ioi 0 →
    ∃ e : PositiveRealExponentialDecay (Real.log '' I) ≃L[ℂ]
        ModulatedExponentialDecay (ContinuousMonoidHom.id ℝ≥0ˣ) I,
      ∀ f t, (e f).val t = f.val (Real.log (t.val : ℝ))

/-- Paper: Example 5.3.3.1, p. 249. Take I = (1, 2) and f(x) = η(x) exp(−x),
where η is smooth, zero on x ≤ 0 and one on x ≥ 1. For each a in (0, log 2),
the twist exp(ax)f(x) is Schwartz. For a = 3/2 the target twist of f(log t)
equals t^(1/2) for t ≥ exp 1 and fails even the order-zero Schwartz bound. -/
theorem Printed.positiveRealExponentialDecay_log_equiv_false :
    ¬ Printed.positiveRealExponentialDecay_log_equiv := by
  sorry

end RiemannMasullo
