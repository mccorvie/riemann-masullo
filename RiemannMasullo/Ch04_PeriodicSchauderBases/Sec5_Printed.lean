module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec5

/-! # §4.5: statements that are false as printed -/

@[expose] public noncomputable section

open Function MeasureTheory Set UniformSpace
open scoped NNReal TensorProduct

namespace RiemannMasullo

set_option quotPrecheck false

local instance printedCh04Sec5QuotientMeasurableSpace {G : Type} [CommGroup G]
    [TopologicalSpace G] (γ : G) : MeasurableSpace (G ⧸ Subgroup.zpowers γ) := borel _

/-- Paper: Remarks 4.5.1.2 and 4.5.1.4, pp. 198, 203. Agreement with (4.5.1.1)
on the original tests, using the split coordinates of
`modulatedExponentialDecay_tensor_equiv` and the canonical tensor comparison. -/
def Printed.AgreesWithFullPeriodization {G : Type} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (τ : ℝ≥0ˣ →ₜ* G) (γ : G) (hγ : 1 < (m γ).val) (I : Set ℝ)
    (A : Completion (ProjectiveTensor (SchwartzBruhat m.toMonoidHom.ker)
        (PositiveRealExponentialDecay I)) → SchwartzBruhat (G ⧸ Subgroup.zpowers γ)) : Prop :=
  let K := m.toMonoidHom.ker
  let TI := InductiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I)
  let TP := ProjectiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I)
  letI : UniformContinuousConstSMul ℂ TI := uniformContinuousConstSMul_of_continuousConstSMul ℂ TI
  ∀ e : Completion TI ≃L[ℂ] ModulatedExponentialDecay m I,
    (∀ (h : SchwartzBruhat K) (p : PositiveRealExponentialDecay I) (u : K) (t : ℝ≥0ˣ),
      (e (Completion.coe' (α := TI) (h ⊗ₜ[ℂ] p))).val (u.val * τ t) =
        h u * p.val (Real.log (t.val : ℝ))) →
    ∀ (z : Completion TI) (f : ModulatedExponentialDecay m univ), (e z).val = f.val →
      A (@Completion.map TI _ TP _ (fun v : TI ↦ (show TP from v)) z) = modulatedPeriodizationCLM m γ hm hms hγ f

/-- Paper: Remark 4.5.1.2, p. 198. Ordinary periodization extends sequentially
continuously to the projective completion. The remark leaves I implicit.
Deviation: This records the reading with an arbitrary nonempty interval from
Definition D.3.3.1. The case with zero in I is treated by
`modulatedIntervalPeriodization_projective`. See ERRATA F174. -/
def Printed.modulatedIntervalPeriodization_projective_sequential : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (τ : ℝ≥0ˣ →ₜ* G), RightInverse τ m → ∀ (γ : G) (hγ : 1 < (m γ).val)
    (I : Set ℝ), OrdConnected I → I.Nonempty →
    let T := ProjectiveTensor (SchwartzBruhat m.toMonoidHom.ker) (PositiveRealExponentialDecay I)
    letI : UniformContinuousConstSMul ℂ T := uniformContinuousConstSMul_of_continuousConstSMul ℂ T
    ∃ A : Completion T →ₗ[ℂ] SchwartzBruhat (G ⧸ Subgroup.zpowers γ),
      SeqContinuous A ∧ Printed.AgreesWithFullPeriodization m hm hms τ γ hγ I A

/-- Paper: Remark 4.5.1.2, p. 198. Take the positive reals, period exp 1, and
I = (1,2). In log coordinates take a smooth bump ψ supported in (−1/4,1/4)
with ψ(0) = 1. Its translates ψ(x+n) are full-decay tests tending to zero in
the interval space, since each twist gains exp(−an) against polynomial growth
in n. Tensor with the constant 1 on the trivial kernel and pass to the completion.
Every periodization has value 1 at the identity class. -/
theorem Printed.modulatedIntervalPeriodization_projective_sequential_false :
    ¬ Printed.modulatedIntervalPeriodization_projective_sequential := by
  sorry

/-- Paper: Remark 4.5.1.4, p. 203. The forward map induced by ordinary
periodization on the quotient by its kernel is continuous. In the quotient
topology this is equivalent to continuity of the extension to the projective
completion. It agrees with (4.5.1.1) on its original full-decay domain.
Deviation: I is implicit in the remark. The counterexample works already for
full decay, I = ℝ. See ERRATA F174. -/
def Printed.modulatedIntervalPeriodization_projectiveQuotient_continuous : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (τ : ℝ≥0ˣ →ₜ* G), RightInverse τ m → ∀ (γ : G) (hγ : 1 < (m γ).val)
    (I : Set ℝ), OrdConnected I → I.Nonempty →
    let T := ProjectiveTensor (SchwartzBruhat m.toMonoidHom.ker) (PositiveRealExponentialDecay I)
    letI : UniformContinuousConstSMul ℂ T := uniformContinuousConstSMul_of_continuousConstSMul ℂ T
    ∃ A : Completion T →L[ℂ] SchwartzBruhat (G ⧸ Subgroup.zpowers γ),
      Printed.AgreesWithFullPeriodization m hm hms τ γ hγ I A

/-- Paper: Remark 4.5.1.4, p. 203. Use ℝ × ∏ⱼ ℤ/2 in log coordinates, with
module exp x, splitting through the identity of the compact factor, period
(1, 1), and I = ℝ. On the target the supremum of the jth derivative at zero
in the jth coordinate character is a continuous seminorm on the inductive
limit. Its pullback to pure tensors would be bounded by a product of two
continuous seminorms. On radial tests supported in (−1/4, 1/4), the radial
seminorm has some finite order N. Fix j > N and use that coordinate character
with a radial cutoff equal to one near zero times exp(inx). The output grows
as nʲ while the asserted bound grows at most as nᴺ. -/
theorem Printed.modulatedIntervalPeriodization_projectiveQuotient_continuous_false :
    ¬ Printed.modulatedIntervalPeriodization_projectiveQuotient_continuous := by
  sorry

/-- Paper: Theorem 4.5.2.3, (4.5.2.2), p. 207. As printed: For every compact
module window with nonempty interior, the map induced by inclusion from the
supported quotient to the full isotypic periodization quotient is a linear
homeomorphism. This is the isomorphism preceding the numbered parts.
The repaired statement is `modulatedCompactSupport_isotypicQuotient_equiv`.
See ERRATA F174. -/
def Printed.modulatedCompactSupport_isotypicQuotient_equiv : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m) (γ : G) (hγ : 1 < (m γ).val)
    (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]
    (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G),
    (∀ (ω : PontryaginDual m.toMonoidHom.ker) (k : m.toMonoidHom.ker), χ ω k.val = ω k) →
    ∀ (ω : PontryaginDual m.toMonoidHom.ker) (B : Set ℝ≥0ˣ), IsCompact B → (interior B).Nonempty →
    let P := modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ (χ ω)
    let D := modulatedCompactSupportSubmodule m B
    let N := P.ker.comap D.subtype
    ∃ e : (D ⧸ N) ≃L[ℂ] (ModulatedExponentialDecay m univ ⧸ P.ker),
      ∀ f : D, e (N.mkQ f) = P.ker.mkQ f.val

/-- Paper: Theorem 4.5.2.3, (4.5.2.2), p. 207. Take the positive reals with
identity module, the trivial character, γ > 1 and B = [1, γ]. Every smooth
test supported in B vanishes at both endpoints. These are the only orbit
points of the identity in B, so every supported periodization vanishes there.
A nonnegative smooth compactly supported test positive at 1 has nonzero
periodization at the identity, giving a missing class in the full quotient. -/
theorem Printed.modulatedCompactSupport_isotypicQuotient_equiv_false :
    ¬ Printed.modulatedCompactSupport_isotypicQuotient_equiv := by
  sorry

end RiemannMasullo
