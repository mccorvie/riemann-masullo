module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
import all RiemannMasullo.AppA_AlgebraicNT.Sec3

/-!
# Appendix B.4: statements that are false as printed

The propositions record the false parts of the printed claims. The repaired statements are
in `Sec4b.lean`, and `ERRATA.md` records the counterexamples. Nothing imports this file.
-/

@[expose] public noncomputable section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing SchwartzMap Topology

namespace RiemannMasullo

set_option quotPrecheck false

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "U[" F "]" => PontryaginDual C[F]
local notation "q(" v ")" => (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℝ)
local notation "halfPlane" => (Complex.re ⁻¹' Ioi (1 : ℝ))
local notation "strip(" a ", " b ")" => (Complex.re ⁻¹' Ioo (a : ℝ) (b : ℝ))
local notation "atHeight" => (fun (σ t : ℝ) ↦ (σ : ℂ) + (t : ℂ) * Complex.I)
local notation "logMellin" => (fun (f : ℝ → ℂ) ↦ mellin (fun t ↦ f (Real.log t)))
local notation "twoPiI" => (2 * (Real.pi : ℂ) * Complex.I)
local notation "ord(" L ")" => MeromorphicOn.divisor L univ
local notation "isContinuation(" χ ", " L ")" =>
  (MeromorphicNFOn L univ ∧ ∀ s : halfPlane, L s = completedHeckeL χ s)
local notation "delta(" F ", " χ ")" =>
  (if (χ).toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then (1 : ℂ) else 0)

/-- Paper: Equation (B.4.2.2), p. 614. As printed: the pole contribution alone is
minus the Mellin values at zero and one when the character is trivial on norm-one
idele classes, and zero otherwise. See `hasSum_heckeAsymptoticResidue` and ERRATA F32. -/
def Printed.heckeAsymptoticResidue_poleTerm : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (f : 𝓢(ℝ, ℂ)),
    ExponentialDecay f →
    ∀ (L : ℂ → ℂ), isContinuation(χ, L) →
      HasSum (fun ρ : {z : ℂ // ord(L) z < 0} ↦ (ord(L) ρ.val : ℂ) * logMellin f ρ.val)
        (-(delta(F, χ) * (logMellin f 0 + logMellin f 1)))

/-- Paper: Equation (B.4.2.2), p. 614. Take `F = ℚ` and the character
`g ↦ |g| ^ i`. Its simple poles are at `-i` and `1 - i`. For a nonnegative,
nonzero smooth logarithmic bump supported in `(-1,1)`, the sum of the real parts
of the shifted Mellin values is strictly smaller than the unshifted sum, since
each integrand acquires the factor `cos x`. -/
theorem Printed.heckeAsymptoticResidue_poleTerm_false :
    ¬ Printed.heckeAsymptoticResidue_poleTerm := by sorry

/-- Paper: Theorem B.4.2.2, Equation (B.4.2.17), p. 616. As printed: the
centered pole contribution alone is minus the two Mellin values at minus and plus
one half for every character. See `hasSum_heckeExplicitFormula` and ERRATA F32. -/
def Printed.heckeExplicitFormula_poleTerm : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (f : 𝓢(ℝ, ℂ)),
    ExponentialDecay f →
    ∀ (L : ℂ → ℂ), isContinuation(χ, L) →
      HasSum (fun ρ : {z : ℂ // ord(L) z < 0} ↦ (ord(L) ρ.val : ℂ) * logMellin f (ρ.val - 1 / 2))
        (-logMellin f (-1 / 2) - logMellin f (1 / 2))

/-- Paper: Theorem B.4.2.2, Equation (B.4.2.17), p. 616. Over `ℚ`, the Hecke
character attached to the primitive nontrivial Dirichlet character modulo three
has entire completed L-function. The sum over poles is empty. A nonzero
nonnegative smooth logarithmic bump gives strictly positive Mellin values at both real points. -/
theorem Printed.heckeExplicitFormula_poleTerm_false :
    ¬ Printed.heckeExplicitFormula_poleTerm := by sorry

/-- Paper: §B.4.2.1, Equation (B.4.2.1), p. 614. As printed: the completed
logarithmic derivative satisfies the horizontal growth bound of Definition B.3.1.1
on the strip, including at index zero. This isolates clause (2) of slow growth.
See `hasSlowGrowthNearPoles_completedHeckeL_logDeriv`,
`hasSum_heckeAsymptoticResidue`, and ERRATA F33. -/
def Printed.hasSlowGrowthNearPoles_completedHeckeL_logDeriv : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (L : ℂ → ℂ),
    isContinuation(χ, L) → ∀ a : ℝ, 1 < a → a ≤ 2 →
      ∃ (T : ℤ → ℝ) (β A : ℝ), 0 < β ∧ 0 < A ∧
        ∀ (k : ℤ) (σ : ℝ), σ ∈ Ioo (1 - a) a →
          ‖logDeriv L (atHeight σ (T k))‖ ≤ A * |(k : ℝ)| ^ β

/-- Paper: §B.4.2.1, Equation (B.4.2.1), p. 614. Take the completed rational
zeta function and `a = 3/2`. The bound at `k = 0` forces the logarithmic derivative
to vanish along the horizontal segment at `T 0`. Its regular subsegment to the
right of one gives a zero germ. Meromorphic continuation would make that germ
zero throughout the strip, contrary to the logarithmic derivative’s pole at one. -/
theorem Printed.hasSlowGrowthNearPoles_completedHeckeL_logDeriv_false :
    ¬ Printed.hasSlowGrowthNearPoles_completedHeckeL_logDeriv := by sorry

/-- Paper: §B.4.2.1, unnumbered display before (B.4.2.2), p. 614. As printed:
the two pole samples with positive sign minus the zero sum equals the rectangular limit
of signed meromorphic orders. Each sum is truncated in absolute imaginary part, and the
signed sum also uses the open strip. See `hasSum_heckeAsymptoticResidue` and ERRATA F34. -/
def Printed.heckeAsymptoticResidue_reversedSigns : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (f : 𝓢(ℝ, ℂ)),
    ExponentialDecay f →
    ∀ (L : ℂ → ℂ), isContinuation(χ, L) → ∀ a : ℝ, 1 < a → a ≤ 2 →
      (∀ s : ℂ, s.re = 1 - a ∨ s.re = a → meromorphicOrderAt L s = 0) →
      ∃ zeros : ℂ,
        Tendsto (fun T : ℝ ↦
          ∑ᶠ ρ : {z : ℂ // 0 < ord(L) z ∧ |z.im| < T}, logMellin f ρ.val * (ord(L) ρ.val : ℂ))
          atTop (𝓝 zeros) ∧
        Tendsto (fun T : ℝ ↦
          ∑ᶠ ρ : {z : ℂ // z ∈ strip(1 - a, a) ∧ |z.im| < T},
            logMellin f ρ.val * (ord(L) ρ.val : ℂ))
          atTop (𝓝 (delta(F, χ) * (logMellin f 0 + logMellin f 1) - zeros))

/-- Paper: §B.4.2.1, unnumbered display before (B.4.2.2), p. 614. Take the
completed rational zeta function, `a = 3/2`, and a nonzero nonnegative smooth
compactly supported logarithmic bump `f₀` with Mellin transform `Φ₀`. Use
`f(x) = exp(-n) f₀(x - n)` for sufficiently large `n`. Its Mellin transform is
`exp(n(s - 1)) Φ₀(s)`. Each zero has real part less than one, so absolute
summability for `Φ₀` gives a zero sum tending to zero as `n` grows. The pole sample
at one remains `Φ₀(1) > 0` and the sample at zero tends to zero. The two sides
therefore have real parts of opposite signs for large `n`. -/
theorem Printed.heckeAsymptoticResidue_reversedSigns_false :
    ¬ Printed.heckeAsymptoticResidue_reversedSigns := by sorry

/-- Paper: Equation (B.4.2.3), p. 614. As printed: the logarithmic derivative
equals the reflected logarithmic derivative plus the logarithm of the discriminant–conductor
product, at regular nonzero points of both functions.
See `completedHeckeL_logDeriv_reflection` and ERRATA F35. -/
def Printed.completedHeckeL_logDeriv_reflection : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (L Ldual : ℂ → ℂ),
    isContinuation(χ, L) → isContinuation(χ⁻¹, Ldual) →
    ∀ s : ℂ, meromorphicOrderAt L s = 0 → meromorphicOrderAt Ldual (1 - s) = 0 →
      logDeriv L s = logDeriv Ldual (1 - s) + (heckeLogDiscriminantConductor χ : ℂ)

/-- Paper: Equation (B.4.2.3), p. 614. For the trivial rational character, use
the completed zeta function for both continuations and `s = 1 + 1/n` with `n`
sufficiently large. The conductor term vanishes and the logarithmic derivative
is nonzero near the simple pole at one. The functional equation gives the
negative of the reflected logarithmic derivative. -/
theorem Printed.completedHeckeL_logDeriv_reflection_false :
    ¬ Printed.completedHeckeL_logDeriv_reflection := by sorry

/-- Paper: Equation (B.4.2.10), p. 615. As printed: the raw real-line
integral gives the sample at the prime power with coefficient one. The character
value is defined at the unramified places in (3.2.1.1), and the contour
abscissa is the one chosen on p. 614.
See `hasSum_heckeExplicitFormula` and ERRATA F36. -/
def Printed.heckePrimePower_mellinSample : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (v : Primes(F)),
    (ideleClassNormTwist χ 0).IsUnramifiedAt v →
    ∀ (m : ℕ), 0 < m → ∀ (a : ℝ), 1 < a → a ≤ 2 →
    ∀ f : 𝓢(ℝ, ℂ), ExponentialDecay f →
      let Q : ℂ := q(v)
      let c := ((ideleClassNormTwist χ 0).localValue v) ^ m
      let l : ℂ := Real.log q(v)
      (l * c / Q ^ ((m : ℂ) * (a : ℂ))) *
        (∫ t : ℝ, logMellin f (atHeight a t) / Q ^ ((m : ℂ) * (t : ℂ) * Complex.I)) =
          l * c * f ((m : ℝ) * Real.log q(v))

/-- Paper: Equation (B.4.2.10), p. 615. Use the trivial character of `ℚ`,
its place at two, `m = 1`, `a = 2`, and `f(x) = exp(-x²)`. The prime-power
sample is nonzero, and Mellin inversion gives a factor `2π` in the raw integral. -/
theorem Printed.heckePrimePower_mellinSample_false : ¬ Printed.heckePrimePower_mellinSample :=
  by sorry

/-- Paper: Equation (B.4.2.11), p. 615. As printed: the reflected upward
contour gives the reciprocal sample with coefficient minus i times the inverse
prime power. The character value is defined at the unramified places in (3.2.1.1),
and the contour abscissa is the one chosen on p. 614.
See `hasSum_heckeExplicitFormula` and ERRATA F36. -/
def Printed.heckePrimePower_mellinSample_reflected : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (v : Primes(F)),
    (ideleClassNormTwist χ 0).IsUnramifiedAt v →
    ∀ (m : ℕ), 0 < m → ∀ (a : ℝ), 1 < a → a ≤ 2 →
    ∀ f : 𝓢(ℝ, ℂ), ExponentialDecay f →
      let Q : ℂ := q(v)
      let cdual := ((ideleClassNormTwist χ⁻¹ 0).localValue v) ^ m
      let l : ℂ := Real.log q(v)
      l * verticalLineIntegral
        (fun s ↦ logMellin f (1 - s) * cdual / Q ^ ((m : ℂ) * s)) a =
          -Complex.I * l * (cdual / Q ^ m) * f (-(m : ℝ) * Real.log q(v))

/-- Paper: Equation (B.4.2.11), p. 615. Use the trivial character of `ℚ`,
its place at two, `m = 1`, `a = 2`, and `f(x) = exp(-x²)`. The reciprocal
sample is nonzero. The reflected integral gives `2πi` times the inverse prime
power, since reversing the endpoints cancels the change of differential. -/
theorem Printed.heckePrimePower_mellinSample_reflected_false :
    ¬ Printed.heckePrimePower_mellinSample_reflected := by sorry

local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "localChart(" w ", " χ ")" =>
  quasiCharacterNormTwist
    ((Units.map nnNormHom.toMonoidHom) ^ (InfinitePlace.mult w) :
      (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ) (continuous_infiniteLocalModule w)
    (ContinuousMonoidHom.comp circleToComplex χ)
local notation "classRestriction(" F ", " w ", " χ ")" =>
  ((χ).comp ⟨IdeleClassGroup.ofCompletion (𝓞 F) F w, continuous_ideleClass_ofCompletion F w⟩)
local notation "positiveUnit(" w ", " t ", " ht ")" =>
  (if hw : InfinitePlace.IsReal w then
    Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom
      (Units.mk0 t (ne_of_gt ht))
  else
    Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp hw)).symm.toMonoidHom
      (Units.mk0 (t : ℂ) (Complex.ofReal_ne_zero.mpr (ne_of_gt ht))))
local notation "isRadialExponent(" w ", " χ ", " s ")" =>
  ((s : ℂ).re = 0 ∧ ∀ (t : ℝ) (ht : 0 < t), (χ (positiveUnit(w, t, ht)) : ℂ) = (t : ℂ) ^ s)
local notation "archAlpha(" w ")" =>
  (if InfinitePlace.IsReal w then -Real.log Real.pi / 2 else -Real.log (2 * Real.pi))
local notation "archDegree(" w ")" => (if InfinitePlace.IsReal w then (2 : ℝ) else 1)
local notation "archMult(" w ")" => (InfinitePlace.mult w : ℝ)

/-- Paper: Equation (B.4.2.12), pp. 615–616. As printed: the local logarithmic
derivative has constant minus alpha and the digamma argument is s minus the
positive-real character exponent, divided by the local degree. See
`realHeckeArchimedean_mellinLogDeriv`, `complexHeckeArchimedean_mellinLogDeriv`,
and ERRATA F37 and F39. -/
def Printed.heckeArchimedean_logDeriv : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (w : InfinitePlace F) (sv : ℂ),
    isRadialExponent(w, classRestriction(F, w, χ), sv) →
    ∀ s : ℂ,
      let Lv := infiniteLocalEulerFactor w ∘ localChart(w, classRestriction(F, w, χ))
      let z := (s - sv) / (archDegree(w) : ℂ)
      meromorphicOrderAt Lv s = 0 → meromorphicOrderAt Complex.Gamma z = 0 →
        logDeriv Lv s = -(archAlpha(w) : ℂ) + (archDegree(w) : ℂ)⁻¹ * logDeriv Complex.Gamma z

/-- Paper: Equation (B.4.2.12), pp. 615–616. At the real place of `ℚ` with
trivial character and `s = 2`, the printed and actual digamma arguments agree.
The constant is `-log(π)/2` from the gamma prefactor, while the printed constant is
`+log(π)/2`. Independently, the primitive quadratic character modulo three has
local sign at the real place. It has the same exponent on positive reals as the
trivial character, but its gamma argument is `(s + 1)/2` in place of `s/2`. -/
theorem Printed.heckeArchimedean_logDeriv_false :
    ¬ Printed.heckeArchimedean_logDeriv := by sorry

/-- Paper: Proposition B.4.2.1, proof, Equation (B.4.2.16), p. 616. As printed:
the sum of the local contour integrals equals the centered contour with the two
bare digammas. See `realHeckeArchimedean_mellinLogDeriv`,
`complexHeckeArchimedean_mellinLogDeriv`, and ERRATA F37. -/
def Printed.heckeArchimedean_mellinLogDeriv_centered : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) (sv : ℂ),
    isRadialExponent(w, χ, sv) →
    ∀ (a : ℝ), 1 < a → ∀ f : 𝓢(ℝ, ℂ), ExponentialDecay f →
      let Lv := infiniteLocalEulerFactor w ∘ localChart(w, χ)
      let LvDual := infiniteLocalEulerFactor w ∘ localChart(w, χ⁻¹)
      let N : ℂ := archMult(w)
      verticalLineIntegral
          (fun s ↦ logMellin f s * logDeriv Lv s + logMellin f (1 - s) * logDeriv LvDual s) a
          / twoPiI =
        verticalLineIntegral (fun s ↦ logMellin f s *
          (logDeriv Complex.Gamma (N * (s - sv) / 2) +
            logDeriv Complex.Gamma (N * (1 - s + sv) / 2))) (1 / 2) / twoPiI

/-- Paper: Proposition B.4.2.1, proof, Equation (B.4.2.16), p. 616. Use the real
place of `ℚ`, the trivial local character, `a = 2` and a nonzero nonnegative smooth
logarithmic bump supported in `(1,2)`. Its value at zero vanishes, so the constant
term contributes zero. The real gamma factor gives one half the printed digamma
sum by the chain rule. The digamma pairing on this bump is strictly negative by
the positive digamma kernel away from zero with its minus sign. -/
theorem Printed.heckeArchimedean_mellinLogDeriv_centered_false :
    ¬ Printed.heckeArchimedean_mellinLogDeriv_centered := by sorry

/-- Paper: Proposition B.4.2.1, Equation (B.4.2.15), p. 616. As printed: the
displayed archimedean integral exists. This isolates convergence at the upper
endpoint by truncating the printed integrand from one to a growing upper bound.
The same integral occurs in (B.4.2.17). See `heckeArchimedeanDigammaKernel` and ERRATA F38. -/
def Printed.heckeArchimedean_integral_convergesAtTop : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) (sv : ℂ),
    isRadialExponent(w, χ, sv) →
    ∀ (a : ℝ), 1 < a → ∀ f : 𝓢(ℝ, ℂ), ExponentialDecay f →
      let N : ℝ := archMult(w)
      let K := fun x : ℝ ↦
        (N : ℂ) * f 0 / (x : ℂ) -
          (f x * Complex.exp (sv * (x : ℂ)) + f (-x) * Complex.exp (-sv * (x : ℂ))) *
            (Real.exp ((2 / N - 1 / 2) * x) : ℂ) / (1 - (Real.exp (-(2 / N * x)) : ℂ))
      ∃ tail : ℂ, Tendsto (fun R : ℝ ↦ ∫ x in Ioc 1 R, K x) atTop (𝓝 tail)

/-- Paper: Proposition B.4.2.1, Equation (B.4.2.15), p. 616. At the real
place of `ℚ`, take the trivial local character, `a = 2`, and a smooth
logarithmic bump supported in `(-1,1)` with value one at zero. On `x > 1`
the two samples vanish, so the upper truncation is exactly `log R` for `R > 1`. -/
theorem Printed.heckeArchimedean_integral_convergesAtTop_false :
    ¬ Printed.heckeArchimedean_integral_convergesAtTop := by sorry

local notation "𝒮ₐ(" K ")" => SchwartzBruhat (Multiplicative K)
local notation "𝒟(" G ")" => BruhatCompactSupport G
local notation "addTest(" f ")" => (fun x ↦ f (Multiplicative.ofAdd x))
local notation "ν𝔭(" F ", " v ")" => finiteLocalAdditiveTamagawaMeasure F v
local notation "ν∞(" F ", " w ")" => infiniteLocalAdditiveTamagawaMeasure F w
local notation "ψ∞(" F ", " w ")" =>
  (fun x ↦ adeleStandardCharacter F (@Pi.single _ _ _ (Classical.decEq _) w x, 0))

local instance instFiniteCompletionMeasurableB4Printed
    (F : Type) [Field F] [NumberField F] (v : Primes(F)) :
    MeasurableSpace (v.adicCompletion F) := borel _
local instance instFiniteUnitsMeasurableB4Printed
    (F : Type) [Field F] [NumberField F] (v : Primes(F)) :
    MeasurableSpace (v.adicCompletion F)ˣ := borel _
local instance instInfiniteCompletionMeasurableB4Printed
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    MeasurableSpace w.Completion := borel _
local instance instFiniteUnitsLocallyCompactB4Printed
    (F : Type) [Field F] [NumberField F] (v : Primes(F)) :
    LocallyCompactSpace (v.adicCompletion F)ˣ :=
  letI : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  inferInstance
local instance instIdeleClassT2B4Printed
    (F : Type) [Field F] [NumberField F] : T2Space C[F] :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
local instance instIdeleClassLocallyCompactB4Printed
    (F : Type) [Field F] [NumberField F] : LocallyCompactSpace C[F] :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1

/-- Paper: Proposition B.4.3.1, uniqueness sentence, p. 618. As printed: the
function defined by (B.4.3.2) is an additive Schwartz–Bruhat test at every finite
place. This is the membership assertion in the uniqueness sentence. See
`finiteLogFourier_unique` and ERRATA F40. -/
def Printed.finiteLog_isSchwartzBruhat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : Primes(F)),
    ∃ J : 𝒮ₐ(v.adicCompletion F), ∀ x : v.adicCompletion F, x ≠ 0 →
      addTest(J) x = (Real.log ‖x‖ / Real.log q(v) : ℝ)

/-- Paper: Proposition B.4.3.1, uniqueness sentence, p. 618. In the completion
of `ℚ` at two, the values at `2^n` are `-n`. They are unbounded as the arguments
tend to zero, so no value at zero gives even a continuous representative. -/
theorem Printed.finiteLog_isSchwartzBruhat_false : ¬ Printed.finiteLog_isSchwartzBruhat := by sorry

local notation "archLogPairing(" F ", " w ", " f ")" =>
  (∫ y : InfinitePlace.Completion w, (Real.log (‖y‖ ^ InfinitePlace.mult w) : ℂ) *
    tamagawaFourier ν∞(F, w) ψ∞(F, w) addTest(f) y ∂ν∞(F, w))
local notation "eulerLogConstant" => (Real.log (2 * Real.pi) + Real.eulerMascheroniConstant)

/-- Paper: Proposition B.4.3.2(1), Equation (B.4.3.13), p. 619. As printed:
the real Fourier pairing is minus the full cutoff limit minus twice the logarithmic
constant times the value at zero. See `realLogFourier_finitePart` and ERRATA F41. -/
def Printed.realLogFourier_finitePart : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), w.IsReal →
    ∀ f : 𝒮ₐ(w.Completion), ∃ A : ℂ,
      Tendsto (fun ε : ℝ ↦
        (∫ x in {x : w.Completion | ε ≤ ‖x‖}, addTest(f) x / (‖x‖ : ℂ) ∂ν∞(F, w)) +
          2 * addTest(f) 0 * (Real.log ε : ℂ)) (𝓝[>] 0) (𝓝 A) ∧
      archLogPairing(F, w, f) = -A - 2 * (eulerLogConstant : ℂ) * addTest(f) 0

/-- Paper: Proposition B.4.3.2(1), Equation (B.4.3.13), p. 619. At the real
place of `ℚ`, take the self-dual Gaussian `f(x) = exp(-πx²)`. Its actual pairing
is `-(γ + log(4π))/2`, while the printed finite part gives `-(γ + log(4π))`. -/
theorem Printed.realLogFourier_finitePart_false : ¬ Printed.realLogFourier_finitePart := by sorry

/-- Paper: Proposition B.4.3.2(2), Equation (B.4.3.14), p. 619. As printed:
the complex Fourier pairing is minus the full squared-modulus cutoff limit minus
four pi times the logarithmic constant times the value at zero. The additive
measure is twice planar Lebesgue measure. See `complexLogFourier_finitePart` and ERRATA F41. -/
def Printed.complexLogFourier_finitePart : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), w.IsComplex →
    ∀ f : 𝒮ₐ(w.Completion), ∃ A : ℂ,
      Tendsto (fun ε : ℝ ↦
        (∫ x in {x : w.Completion | ε ≤ ‖x‖ ^ 2},
          addTest(f) x / ((‖x‖ ^ 2 : ℝ) : ℂ) ∂ν∞(F, w)) +
          (2 * Real.pi : ℝ) * addTest(f) 0 * (Real.log ε : ℂ)) (𝓝[>] 0) (𝓝 A) ∧
      archLogPairing(F, w, f) = -A - (4 * Real.pi * eulerLogConstant : ℝ) * addTest(f) 0

/-- Paper: Proposition B.4.3.2(2), Equation (B.4.3.14), p. 619. At the complex
place of `ℚ(i)`, take the self-dual Gaussian `f(z) = exp(-2π|z|²)`. Its actual
pairing is `-γ - log(2π)`. The printed expression gives `-2π(γ + log(2π))`. -/
theorem Printed.complexLogFourier_finitePart_false :
    ¬ Printed.complexLogFourier_finitePart := by sorry

/-- Paper: Lemma B.4.4.3, Equation (B.4.4.6), p. 620. As printed: on tests
vanishing at one, the principal value is minus the integer-unit mass times the
stated positive density paired with the inverse-square-root weighted test.
This substitutes the printed restriction of the distribution into the equation,
where the weighted test also vanishes at one. See
`existsUnique_finiteWeilFourierDistribution` and ERRATA F42. -/
def Printed.finiteWeilPrincipalValue_positiveDensity : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : Primes(F))
    (f : 𝒟((v.adicCompletion F)ˣ)), f.val 1 = 0 →
      let V := (finiteLocalMultiplicativeTamagawaMeasure F v (v.adicCompletionIntegers F).units).toReal
      let g := Function.extend Units.val (f.val : (v.adicCompletion F)ˣ → ℂ) (fun _ ↦ 0)
      finiteConnesWeilPrincipalValue v 1 f =
        -(V : ℂ) * ((q(v) / (q(v) - 1) : ℝ) : ℂ) *
          ∫ x, g x / (Real.sqrt ‖x‖ : ℂ) / (‖1 - x‖ : ℂ) ∂ν𝔭(F, v)

/-- Paper: Lemma B.4.4.3, Equation (B.4.4.6), p. 620. In the completion of
`ℚ` at two, use the indicator of `2ℤ₂ˣ`. By (B.4.4.5) the principal value
is `2^(-1/2) > 0`. The positive density evaluated on the weighted indicator
is positive, and the minus integer-unit mass makes the right side negative. -/
theorem Printed.finiteWeilPrincipalValue_positiveDensity_false :
    ¬ Printed.finiteWeilPrincipalValue_positiveDensity := by sorry

local notation "archUnitMass(" w ")" => (if InfinitePlace.IsReal w then (2 : ℝ) else 2 * Real.pi)

/-- Paper: Theorem B.4.4.7, Equation (B.4.4.16), p. 623. The pointwise
absolutely convergent identity on every idelic test includes one term for each
zero quasi-character and divides the archimedean principal values by the local
unit masses. A norm section indexes each quasi-character exactly once. This
isolates the scalar identity from the additional assertion of convergence in the
strong dual. See `idelicExplicitFormula` and ERRATA F43. -/
def Printed.idelicExplicitFormula_archNormalization : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (τ : ℝ≥0ˣ →ₜ* C[F]),
    RightInverse τ (ideleClassNorm F) → ∀ f : 𝒟(C[F]),
      let zeros := {z : {χ : U[F] // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
        0 < ord(explicitFormulaCompletedHeckeL z.1.val) z.2}
      let V : ℂ := (normOneIdeleClassTamagawaMeasure F univ).toReal
      let weight := fun (g : C[F]) (a : ℂ) ↦ (((ideleClassNorm F g).val : ℝ) : ℂ) ^ a
      let moment := fun (a : ℂ) ↦
        (∫ g, f.val g * weight g a ∂ideleClassTamagawaMeasure F) / V
      ∃ (arch : (w : InfinitePlace F) → 𝒟(w.Completionˣ))
        (finite : (v : Primes(F)) → 𝒟((v.adicCompletion F)ˣ)) (finiteSum : ℂ),
        (∀ w u, (arch w).val u = f.val (IdeleClassGroup.ofCompletion (𝓞 F) F w u)) ∧
        (∀ v u, (finite v).val u = f.val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)) ∧
        HasSum (fun v : Primes(F) ↦
          let μ := finiteLocalMultiplicativeTamagawaMeasure F v
          let mass := (μ (v.adicCompletionIntegers F).units).toReal
          (Real.log q(v) / mass : ℝ) * finiteConnesWeilPrincipalValue v 1 (finite v)) finiteSum ∧
        HasSum (fun z : zeros ↦
          (∫ g, f.val g * ideleClassNormTwist z.val.1.val z.val.2 g * weight g (-1 / 2)
            ∂ideleClassTamagawaMeasure F) / V)
          (moment (-1 / 2) + moment (1 / 2) -
            (∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (arch w) /
              (archUnitMass(w) : ℂ)) - finiteSum)

/-- Paper: Theorem B.4.4.7, Equation (B.4.4.16), p. 623. Over `ℚ` take the
radial tests `h(log |g| - t)`, for a nonzero nonnegative smooth bump supported
in `(log(5/4),log(7/4))` and `t ≥ 0`. Only the zeta component survives norm-one
integration. Subtract the printed formula from the multiplicity-weighted explicit
formula. The pole and finite terms cancel. Write `w = ρ - 1/2` and `b_w` for
the excess multiplicity times the normalized Mellin sample at `t = 0`.
The difference would give `∑ b_w exp(t w) = -PV∞(t)/2` for all these translates.
The real principal value is positive and decays as `O(exp(-t/2))`. Its Laplace
transform is holomorphic for `Re z > -1/2`, whereas the spectral transform
`∑ b_w/(z-w)` has residue `b_w` at each distinct `w` there. Rapid Mellin decay
and the zeta zero count give absolute summability of the coefficients and local
normal convergence away from the zeros. Every residue must vanish, contradicting
the positive principal value at `t = 0`. -/
theorem Printed.idelicExplicitFormula_archNormalization_false :
    ¬ Printed.idelicExplicitFormula_archNormalization := by sorry

/-- Paper: Lemma B.4.4.8, Equation (B.4.4.17), p. 624. As printed: for a
positive-real-modulated abelian Lie group and a Haar measure, the Mellin evaluations
of every compactly supported Bruhat test are absolutely summable over any set
of quasi-characters whose intersection with each connected component is discrete
and lies in a bounded-width vertical strip of that component. See
`summable_bruhatMellin_of_polynomialCount` and ERRATA F44. -/
def Printed.summable_bruhatMellin_of_discreteStrips : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (d : ℕ) [ChartedSpace (EuclideanSpace ℝ (Fin d)) G]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d))) (∞) G]
    [LieGroup (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d))) (∞) G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m), Surjective m →
    ∀ (μ : Measure G) [μ.IsHaarMeasure] (Z : Set (QuasiCharacter G)),
      (∀ c : QuasiCharacter G,
        IsDiscrete (Z ∩ connectedComponent c) ∧
          ∃ a b : ℝ, a < b ∧
            Z ∩ connectedComponent c ⊆ relativeVerticalStrip m.toMonoidHom hm.1 hm.2 (Ioo a b)) →
      ∀ f : 𝒟(G), Summable (fun c : Z ↦ ‖∫ g, f.val g * c.val g ∂μ‖)

/-- Paper: Lemma B.4.4.8, Equation (B.4.4.17), p. 624. Take the positive real
group with identity modulation and Haar measure `dt/t`. Choose a nonzero
nonnegative smooth bump with Mellin transform `Φ`. In each `(n,n+1/2)`, take
`tₙ` with `aₙ = |Φ(itₙ)| > 0` by analyticity. Take `⌈2/aₙ⌉` distinct heights
in that interval near `tₙ` with Mellin modulus at least `aₙ/2`. The
quasi-characters at those imaginary exponents form a closed discrete set in
one strip, and each block contributes at least one. -/
theorem Printed.summable_bruhatMellin_of_discreteStrips_false :
    ¬ Printed.summable_bruhatMellin_of_discreteStrips := by sorry

end RiemannMasullo
