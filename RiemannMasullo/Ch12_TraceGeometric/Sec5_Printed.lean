module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5
import all RiemannMasullo.Ch10_TraceSpectral.Sec1
import all RiemannMasullo.AppB_AnalyticNT.Sec4b

/-! # Printed trace formula of §12.5

The proposition records Theorem 12.5.1.1 as printed. The repaired statement is
`traceFormula` in `Sec5.lean`. Nothing imports this file.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b

local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "m[" F "]" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C[F] →ₜ* ℝ≥0ˣ)
local notation "M[" F "](" φ ", " c ")" =>
  modulatedFourierMellin m[F] univ
    (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m[F])
    (ideleClassTamagawaMeasure F) (φ : BruhatCompactSupport C[F]).val c
local notation "ord(" χ ", " s ")" => MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ s

open Classical in
/-- Paper: Theorem 12.5.1.1, pp. 519–520. As printed, for every number field F,
every test φ vanishing on C_F¹ and every interval I = [−α, α] with α > 0
as in §1.8.4, p. 53, the sum of the local principal
values equals M(φ)(|·|^{1/2}) + M(φ)(|·|^{−1/2}) minus the sum of N(c)·M(φ)(c|·|^{−1/2})
over the zeros c in the interior of Ω(C_F)_I, with convergent series. The interior
is |σ(c) − 1/2| < α, and a norm section lists each quasi-character once.
The complex denominator is the ordinary modulus printed in (12.5.1.1).
The local tests vanish at one, so this term is an ordinary integral. -/
def Printed.traceFormula : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (τ : ℝ≥0ˣ →ₜ* C[F]),
    RightInverse τ (ideleClassNorm F) →
    ∀ φ : BruhatCompactSupport C[F], (∀ g : (ideleClassNorm F).ker, φ.val g = 0) →
    ∀ α : ℝ, 0 < α →
      let zeros := {z : {χ : PontryaginDual C[F] // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
        0 < ord(z.1.val, z.2) ∧ |z.2.re - 1 / 2| < α}
      let finiteTerm := fun (v : HeightOneSpectrum (𝓞 F))
          (b : BruhatCompactSupport (v.adicCompletion F)ˣ) ↦
        let μ := finiteLocalMultiplicativeTamagawaMeasure F v
        let mass := (μ (v.adicCompletionIntegers F).units).toReal
        ((Real.log (v.asIdeal.absNorm : ℝ) / mass : ℝ) : ℂ) * finiteConnesWeilPrincipalValue v 1 b
      let archTerm := fun (w : InfinitePlace F) (a : BruhatCompactSupport w.Completionˣ) ↦
        if w.IsReal then infiniteConnesWeilPrincipalValue w a
        else (1 / (2 * (Real.pi : ℂ))) * ∫ u : w.Completionˣ,
          a.val u * (‖u.val‖ : ℂ) / (‖1 - u.val‖ : ℂ)
            ∂(infiniteLocalMultiplicativeTamagawaMeasure F w)
      ∃ (a : (w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
        (b : (v : HeightOneSpectrum (𝓞 F)) → BruhatCompactSupport (v.adicCompletion F)ˣ),
        (∀ w u, (a w).val u = φ.val (IdeleClassGroup.ofCompletion (𝓞 F) F w u)) ∧
        (∀ v u, (b v).val u = φ.val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)) ∧
        Summable (fun v ↦ finiteTerm v (b v)) ∧
        HasSum (fun z : zeros ↦ ((ord(z.val.1.val, z.val.2) : ℤ) : ℂ) *
            M[F](φ, ideleClassNormTwist z.val.1.val (z.val.2 - 1 / 2)))
          (M[F](φ, ideleClassNormTwist 1 (1 / 2)) + M[F](φ, ideleClassNormTwist 1 (-1 / 2)) -
            ((∑ w : InfinitePlace F, archTerm w (a w)) +
              ∑' v, finiteTerm v (b v)))

/-- Paper: Theorem 12.5.1.1, pp. 519–520. Take F = ℚ(i), α = 1, and
φ(g) = h(|g|) − h(|g|⁻¹) for a nonzero nonnegative smooth bump h supported
in (9/4, 11/4). All finite local terms vanish because the two norm intervals
avoid every prime power and its reciprocal. Inversion interchanges the two
pole terms with a minus sign. Only the trivial norm-one character contributes,
and the completed Dedekind zeta functional equation pairs s with 1 − s,
with equal multiplicity and opposite Mellin values in the centered strip.
At the complex place set r = ‖u‖, so |u|ᵥ = r². Inverting the inner annulus
makes the local integral a positive constant times the integral of
h(r²) (r − 1) / ‖1 − u‖ on the outer annulus, which is strictly positive. -/
theorem Printed.traceFormula_false : ¬ Printed.traceFormula := by sorry

end RiemannMasullo
