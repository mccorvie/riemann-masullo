module

public import RiemannMasullo.Ch09_HardySobolev.Sec3

/-! # The absolute cutoff injectivity claim in §9.3.3 -/

@[expose] public noncomputable section

open Function MeasureTheory Set
open scoped NNReal

namespace RiemannMasullo

/-- Paper: Remark 9.3.3.4, p. 428. As printed: On the weighted space W^{s,2}(G)
of every ℝ₊-modulated group with a choice of Haar measure, each of the positive,
negative and two-sided absolute cutoffs is injective, for every radius Λ > 0
and every s ≥ 0. See `modulatedAbsoluteCutoffOperator_projection` and ERRATA F238. -/
def Printed.modulatedAbsoluteCutoffOperator_injective : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (m : G →ₜ* ℝ≥0ˣ), IsModulation m → Surjective m → ∀ (Λ s : ℝ), 0 < Λ → 0 ≤ s →
      let ν := sobolevMeasure μ (modulatedSobolevWeight m) s
      Injective (modulatedAbsoluteCutoffOperator m ν (Ici Λ⁻¹) measurableSet_Ici) ∧
      Injective (modulatedAbsoluteCutoffOperator m ν (Iic Λ) measurableSet_Iic) ∧
      Injective (modulatedAbsoluteCutoffOperator m ν (Icc Λ⁻¹ Λ) measurableSet_Icc)

/-- Paper: Remark 9.3.3.4, p. 428. Take the positive reals with the identity
modulation, s = 0 and Λ = 2. A nonzero smooth log-coordinate bump supported
in (−log 2−2, −log 2−1) is a nonzero L² class killed by the positive and
two-sided cutoffs. A bump supported in (log 2+1, log 2+2) is killed by
the negative cutoff. -/
theorem Printed.modulatedAbsoluteCutoffOperator_injective_false :
    ¬ Printed.modulatedAbsoluteCutoffOperator_injective := by sorry

end RiemannMasullo
