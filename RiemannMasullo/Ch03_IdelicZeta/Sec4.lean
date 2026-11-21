module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3b
public import RiemannMasullo.AppC_LCTVS.Sec5b
public import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Eigendistributions and Weil's identity

Masullo, §3.4, pp. 141–153. Page 154 is blank. The zeta integrals use the
Tamagawa measures from Appendix A. The local factorization recalled in
Notation 3.4.1.1 is `heckeCharacter_eq_prod_restrictions` from §3.1.
-/

@[expose] public noncomputable section

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology UniformConvergenceCLM

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C₁" => (ideleClassNorm F).ker
local notation "C_F" => IdeleClassGroup (𝓞 F) F
local notation "X" => HeckeCharacter (𝓞 F) F
local notation "I_F" => IdeleGroup (𝓞 F) F
local notation "ℬ(" K ")" => SchwartzBruhat (Multiplicative K)
local notation "classOf" => QuotientGroup.mk (s := IdeleGroup.principalSubgroup (𝓞 F) F)
local notation "normℝ" => fun (g : C_F) ↦ ((ideleClassNorm F g : ℝ≥0) : ℝ)
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "finiteNorm(" v ")" =>
  (Units.map nnNormHom.toMonoidHom : (HeightOneSpectrum.adicCompletion F v)ˣ →* ℝ≥0ˣ)
local notation "infiniteNorm(" w ")" =>
  ((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w : (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ)

section UnramifiedIdentity

local notation "AArch" => SAdeleRing F (∅ : Finset V)
local notation "μArch" => sMultiplicativeTamagawaMeasure F (∅ : Finset V)
local notation "μv" => finiteLocalMultiplicativeTamagawaMeasure F
local notation "valuation(" v ")" =>
  (Valued.v : Valuation (HeightOneSpectrum.adicCompletion F v) (WithZero (Multiplicative ℤ)))
local notation "positive" => (relativeRightHalfPlane (G := C_F) (ideleClassNorm F)
  (isProperMap_ideleClassNorm F) (ideleClassNorm_ne_one (F := F)) 0 : Set X)

-- Named, because an anonymous instance gets the same generated name in every file that declares
-- it, and two such files can then not be imported together.
local instance instMeasurableSpaceUnitsAdicCompletionSec4 (v : V) :
    MeasurableSpace (v.adicCompletion F)ˣ := borel _

/-- Paper: Equation (3.4.1.2), p. 143. The archimedean integral uses the
restriction of the quasi-character along insertion of the archimedean ideles. -/
def weilArchimedeanIntegral (fArch : ℬ(AArch)) (c : X) : ℂ :=
  ∫ g : AArchˣ, fArch (Multiplicative.ofAdd g.val) *
    c (classOf (sIdeleInsertion F ∅ g)) ∂μArch

/-- Paper: Equation (3.4.1.2), p. 143. The integral at the bare norm is the
integral of the test function weighted by the archimedean module. -/
theorem weilArchimedeanIntegral_norm (fArch : ℬ(AArch)) :
    weilArchimedeanIntegral fArch (ideleClassNormTwist 1 1) =
      ∫ g : AArchˣ, fArch (Multiplicative.ofAdd g.val) *
        (((sIdeleNorm F ∅ g : ℝ≥0) : ℝ) : ℂ) ∂μArch := by sorry

/-- Paper: Theorem 3.4.1.1, p. 143. The archimedean integrand is absolutely
integrable at each quasi-character of positive abscissa. -/
theorem weilArchimedeanIntegral_integrable (fArch : ℬ(AArch)) (c : X) (hc : c ∈ positive) :
    Integrable (fun g : AArchˣ ↦ fArch (Multiplicative.ofAdd g.val) *
      c (classOf (sIdeleInsertion F ∅ g))) μArch := by sorry

open Classical in
/-- Paper: Equations (3.4.1.3)–(3.4.1.4), p. 143. At an unramified place,
subtract the test function pulled back by inverse uniformizer multiplication
before integrating. At a ramified place, integrate the original test function. -/
def weilModifiedFiniteIntegral (v : V) (π : (v.adicCompletion F)ˣ)
    (f : v.adicCompletion F → ℂ) (c : X) : ℂ :=
  localIdelicZetaIntegral (μv v)
    (if c.IsUnramifiedAt v then fun x ↦ f x - f ((↑π⁻¹ : v.adicCompletion F) * x) else f)
    (finitePlaceRestriction F v c)

open Classical in
/-- Paper: Theorem 3.4.1.1, pp. 143–144. The finite-place integrals of the
modified compact-open indicators are absolutely convergent at positive abscissa. -/
theorem weilModifiedFiniteIntegral_integrable (v : V) (π : (v.adicCompletion F)ˣ)
    (hπ : (valuation(v)).IsUniformizer π.val) (K : Set (v.adicCompletion F))
    (hK : IsCompact K) (hKo : IsOpen K) (c : X) (hc : c ∈ positive) :
    let f := K.indicator (fun _ ↦ (1 : ℂ))
    let test := if c.IsUnramifiedAt v then fun x ↦ f x - f ((↑π⁻¹ : v.adicCompletion F) * x)
      else f
    Integrable (fun g : (v.adicCompletion F)ˣ ↦ test g.val * finitePlaceRestriction F v c g)
      (μv v) := by
  sorry

/-- Paper: Theorem 3.4.1.1, p. 144. At an unramified place the modified
integer-ring indicator integrates to the Tamagawa mass of the integer units. -/
theorem weilModifiedFiniteIntegral_integerRing (v : V) (π : (v.adicCompletion F)ˣ)
    (hπ : (valuation(v)).IsUniformizer π.val) (c : X)
    (hc : c.IsUnramifiedAt v) :
    weilModifiedFiniteIntegral v π
        ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ ↦ 1)) c =
      ((μv v) (v.adicCompletionIntegers F).units).toReal := by sorry

/-- Paper: Equation (3.4.1.1), p. 143. The modified zeta function is the
archimedean integral times the product of the modified finite integrals. -/
def weilModifiedZeta (fArch : ℬ(AArch)) (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ) (c : X) : ℂ :=
  weilArchimedeanIntegral fArch c *
    (∏' v : V, weilModifiedFiniteIntegral v (uniformizer v) ((K v).indicator (fun _ ↦ 1)) c)

/-- Paper: Theorem 3.4.1.1, pp. 143–144. When the character is unramified
at every finite place and every local test is the integer-ring indicator,
the finite product contributes the product of integer-unit masses. -/
theorem weilModifiedZeta_integerRings (fArch : ℬ(AArch))
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hK : ∀ v : V, K v = v.adicCompletionIntegers F) (c : X)
    (hc : ∀ v, c.IsUnramifiedAt v) :
    weilModifiedZeta fArch K uniformizer c = weilArchimedeanIntegral fArch c *
      ∏ᶠ v : V, (((μv v) (v.adicCompletionIntegers F).units).toReal : ℂ) := by sorry

/-- Paper: Theorem 3.4.1.1, p. 143. The finite-place factors of the modified
zeta product differ from one by an absolutely summable family. -/
theorem weilModifiedZeta_summable
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hKc : ∀ v : V, IsCompact (K v)) (hKo : ∀ v : V, IsOpen (K v))
    (hK : ∀ᶠ v in cofinite, K v = v.adicCompletionIntegers F) (c : X) (hc : c ∈ positive) :
    Summable (fun v : V ↦
      ‖weilModifiedFiniteIntegral v (uniformizer v) ((K v).indicator (fun _ ↦ 1)) c - 1‖) := by sorry

/-- Paper: Theorem 3.4.1.1, p. 143. The net of partial modified products
converges uniformly on compact sets of quasi-characters of positive abscissa. -/
theorem weilModifiedZeta_tendstoUniformlyOn (fArch : ℬ(AArch))
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hKc : ∀ v : V, IsCompact (K v)) (hKo : ∀ v : V, IsOpen (K v))
    (hK : ∀ᶠ v in cofinite, K v = v.adicCompletionIntegers F)
    (L : Set X) (hL : IsCompact L) (hLpos : L ⊆ positive) :
    TendstoUniformlyOn (fun S : Finset V ↦ fun c ↦
      weilArchimedeanIntegral fArch c *
        ∏ v ∈ S, weilModifiedFiniteIntegral v (uniformizer v) ((K v).indicator (fun _ ↦ 1)) c)
      (weilModifiedZeta fArch K uniformizer) atTop L := by sorry

/-- Paper: Theorem 3.4.1.1, p. 143. The modified zeta product is holomorphic
on the positive half-plane in each unitary norm-twist coordinate. -/
theorem weilModifiedZeta_analyticOn (fArch : ℬ(AArch))
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hKc : ∀ v : V, IsCompact (K v)) (hKo : ∀ v : V, IsOpen (K v))
    (hK : ∀ᶠ v in cofinite, K v = v.adicCompletionIntegers F) (χ : PontryaginDual C_F) :
    AnalyticOnNhd ℂ (fun s ↦ weilModifiedZeta fArch K uniformizer (ideleClassNormTwist χ s))
      (Complex.re ⁻¹' Ioi 0) := by sorry

/-- Paper: Proof of Theorem 3.4.1.1, p. 144. For a character of positive abscissa
unramified at every finite place, the archimedean integral equals the continued
S-idelic Z-function with no finite places. -/
theorem weilArchimedeanIntegral_eq_sLocal (fArch : ℬ(AArch)) (c : X)
    (hc : c ∈ unramifiedOutside F ∅) (hpos : c ∈ positive) :
    weilArchimedeanIntegral fArch c =
      sLocalIdelicZFunction fArch (sIdeleRestriction F ∅ ⟨c, hc⟩) := by sorry

-- TODO(paper-gap): Equations (3.4.1.5)–(3.4.1.6) omit the outside integer-unit masses.
-- In (3.4.1.6) the ramified finite Euler factors are one, and the continuation
-- on the positive half-plane can have a pole. Footnote 3 asks for the product comparison.

open Classical in
/-- Paper: Equation (3.4.1.5), p. 143. The modified product factors through the
S₀-idelic integral over the archimedean and ramified places, with modified factors at
the remaining exceptional places in S.
Deviation: The Tamagawa masses of the integer units outside S are included. The finite
sets S₀ and S index only finite places, since all archimedean places are implicit. -/
theorem weilModifiedZeta_eq_sLocal (S₀ S : Finset V) (hS : S₀ ⊆ S)
    (fArch : ℬ(AArch)) (fS₀ : ℬ(SAdeleRing F S₀))
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hKc : ∀ v : V, IsCompact (K v)) (hKo : ∀ v : V, IsOpen (K v))
    (hK : ∀ v ∉ S, K v = v.adicCompletionIntegers F)
    (hfS₀ : ∀ x : SAdeleRing F S₀, fS₀ (Multiplicative.ofAdd x) =
      fArch (Multiplicative.ofAdd (x.1, 0)) *
        ∏ v : S₀, (K v.val).indicator (fun _ ↦ (1 : ℂ)) (x.2 v))
    (c : X) (hc : c ∈ positive) (hc₀ : c ∈ unramifiedOutside F S₀)
    (hram : ∀ v ∈ S₀, ¬ c.IsUnramifiedAt v) :
    weilModifiedZeta fArch K uniformizer c =
      (∏ᶠ v : {v : V // v ∉ S}, (((μv v.val) (v.val.adicCompletionIntegers F).units).toReal : ℂ)) *
        sLocalIdelicZetaIntegral fS₀ (sIdeleRestriction F S₀ ⟨c, hc₀⟩) *
        ∏ v ∈ S \ S₀,
          weilModifiedFiniteIntegral v (uniformizer v) ((K v).indicator (fun _ ↦ 1)) c := by sorry

/-- Paper: Equation (3.4.1.6), p. 143, in the form used on p. 231. The zeta integral
of a test extended from S is its S-idelic zeta integral times the outside Euler product.
Deviation: The Tamagawa masses of the integer units outside S are included. This is the
absolute-convergence form of the identity, with an arbitrary S-adelic test function. -/
theorem weilIdentity_unramifiedOutside (S : Finset V) (fS : ℬ(SAdeleRing F S))
    (χ : PontryaginDual C_F) (s : ℂ) (hs : 1 < s.re)
    (hc : ideleClassNormTwist χ s ∈ unramifiedOutside F S) :
    globalIdelicZetaIntegral (sAdeleSchwartzToGlobal F S fS) (ideleClassNormTwist χ s) =
      (∏ᶠ v : {v : V // v ∉ S},
          (((μv v.val) (v.val.adicCompletionIntegers F).units).toReal : ℂ)) *
        sLocalIdelicZetaIntegral fS (sIdeleRestriction F S ⟨ideleClassNormTwist χ s, hc⟩) *
        ∏' v : {v : V // v ∉ S}, finiteHeckeEulerFactor χ v.val s := by sorry

/-- Paper: Equation (3.4.1.6), pp. 143–144, as applied on p. 231. For a test extended
from S, the global Z-function is the S-local Z-function times the continued outside
Euler product and the outside integer-unit masses.
Deviation: The continuation is expressed away from a discrete set of exponents. -/
theorem weilIdentity_unramifiedOutside_meromorphic (S : Finset V) (fS : ℬ(SAdeleRing F S))
    (χ : PontryaginDual C_F) (hc : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hLf : ∀ (s : ℂ) (hs : 1 < s.re), L s = finiteHeckeL χ ⟨s, hs⟩) :
    let cS := sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, hc⟩
    let twistS := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous cS
    (fun s ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S fS) (ideleClassNormTwist χ s))
      =ᶠ[codiscrete ℂ] (fun s ↦
        (∏ᶠ v : {v : V // v ∉ S}, (((μv v.val) (v.val.adicCompletionIntegers F).units).toReal : ℂ)) *
          sLocalIdelicZFunction fS (twistS s) * (∏ v ∈ S, (finiteHeckeEulerFactor χ v s)⁻¹) * L s) := by
  sorry

/-- Paper: Equation (3.4.1.6), p. 143. For a pure tensor the zeta integral is the
modified zeta product times the finite Hecke L-function on the absolute-convergence half-plane.
Deviation: The modified product already contains the outside Tamagawa masses. The
finite Hecke L-function has Euler factor one at every ramified place, as in §3.2. -/
theorem weilIdentity_modifiedZeta (f : ℬ(𝔸[F])) (fArch : ℬ(AArch))
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hKc : ∀ v : V, IsCompact (K v)) (hKo : ∀ v : V, IsOpen (K v))
    (hK : ∀ᶠ v in cofinite, K v = v.adicCompletionIntegers F)
    (hf : ∀ x : 𝔸[F], f (Multiplicative.ofAdd x) =
      fArch (Multiplicative.ofAdd (adeleProjection F ∅ x)) *
        ∏ᶠ v : V, (K v).indicator (fun _ ↦ (1 : ℂ)) (x.2 v))
    (χ : PontryaginDual C_F) (s : ℂ) (hs : 1 < s.re) :
    globalIdelicZetaIntegral f (ideleClassNormTwist χ s) =
      weilModifiedZeta fArch K uniformizer (ideleClassNormTwist χ s) *
        finiteHeckeL χ ⟨s, hs⟩ := by sorry

/-- Paper: Equation (3.4.1.6), pp. 143–144. The pure-tensor identity extends to the
positive half-plane for the continued zeta function and finite Hecke L-function.
Deviation: The same normalization as in `weilIdentity_modifiedZeta` is used. The
continuation is meromorphic, with equality expressed off a discrete set. -/
theorem weilIdentity_modifiedZeta_meromorphic (f : ℬ(𝔸[F])) (fArch : ℬ(AArch))
    (K : (v : V) → Set (v.adicCompletion F))
    (uniformizer : (v : V) → (v.adicCompletion F)ˣ)
    (hπ : ∀ v : V, (valuation(v)).IsUniformizer (uniformizer v).val)
    (hKc : ∀ v : V, IsCompact (K v)) (hKo : ∀ v : V, IsOpen (K v))
    (hK : ∀ᶠ v in cofinite, K v = v.adicCompletionIntegers F)
    (hf : ∀ x : 𝔸[F], f (Multiplicative.ofAdd x) =
      fArch (Multiplicative.ofAdd (adeleProjection F ∅ x)) *
        ∏ᶠ v : V, (K v).indicator (fun _ ↦ (1 : ℂ)) (x.2 v))
    (χ : PontryaginDual C_F) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hLf : ∀ (s : ℂ) (hs : 1 < s.re), L s = finiteHeckeL χ ⟨s, hs⟩) :
    (fun s ↦ globalIdelicZFunction f (ideleClassNormTwist χ s)) =ᶠ[
        codiscreteWithin (Complex.re ⁻¹' Ioi 0)]
      (fun s ↦ weilModifiedZeta fArch K uniformizer (ideleClassNormTwist χ s) * L s) := by sorry

end UnramifiedIdentity

section Applications

-- TODO(paper-gap): Proposition 3.4.2.1 asserts Lebesgue integrability on the
-- relative one-line. The standard test function over ℚ gives absolute divergence.

open Classical in
/-- Paper: Equation (3.4.2.6), p. 146. For the trivial norm-one character
the cutoff is the indicator of norm at most one. For other characters it vanishes. -/
def thetaPolarCutoff (ω : PontryaginDual C₁) (g : C_F) : ℂ :=
  if ω = 1 ∧ normℝ g ≤ 1 then 1 else 0

/-- Paper: Equation (3.4.2.6), p. 146. The trivial-character cutoff equals
one at the identity class. -/
theorem thetaPolarCutoff_one : thetaPolarCutoff (1 : PontryaginDual C₁) 1 = 1 := by sorry

/-- Paper: Theorem 3.4.2.2(1), p. 146. At large norm homogeneous theta
decays to every inverse power, uniformly over a bounded set of test functions.
This restates the large-norm bound in `homogeneousAdelicTheta_decay_bounded`. -/
theorem weilTheta_decay_large (ω : PontryaginDual C₁)
    (B : Set ℬ(𝔸[F])) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : C_F, T < normℝ g →
      ‖homogeneousAdelicTheta ω f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by sorry

-- TODO(paper-gap): Equation (3.4.2.4) drops the norm-one class volume
-- included in Theorem 2.2.5.4 and in Equations (3.4.2.9)–(3.4.2.10).

/-- Paper: Theorem 3.4.2.2(2), p. 146. At small norm homogeneous theta
minus the cutoff polar term decays to every power, uniformly over bounded sets.
Deviation: The polar coefficient includes the norm-one Tamagawa volume as in
Equation (3.4.2.10) and `homogeneousAdelicTheta_decay_bounded`. -/
theorem weilTheta_decay_small (ω : PontryaginDual C₁)
    (B : Set ℬ(𝔸[F])) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : C_F, normℝ g < T →
      let zeroAdele := Multiplicative.ofAdd (0 : 𝔸[F])
      let polar := (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele - f zeroAdele
      ‖homogeneousAdelicTheta ω f g -
        (normOneIdeleClassTamagawaMeasure F univ).toReal • (thetaPolarCutoff ω g * polar)‖ ≤
        C * (normℝ g) ^ N := by sorry

/-- Paper: Theorem 3.4.2.2(2), p. 146. For norm at most one, the volume-scaled
cutoff polar term equals the polar term of Theorem 2.2.5.4. -/
theorem thetaPolarCutoff_polarTerm (ω : PontryaginDual C₁) (f : ℬ(𝔸[F])) (g : C_F)
    (hg : normℝ g ≤ 1) :
    (normOneIdeleClassTamagawaMeasure F univ).toReal •
        (thetaPolarCutoff ω g *
          ((normℝ g)⁻¹ • adeleSchwartzFourier f (Multiplicative.ofAdd (0 : 𝔸[F])) -
            f (Multiplicative.ofAdd (0 : 𝔸[F])))) =
      homogeneousAdelicTheta_polarTerm ω f g := by sorry

-- TODO(paper-gap): Equation (3.4.2.7) counts each modified finite factor
-- twice. The line below it also divides by the local Euler denominator,
-- while the definition (3.4.1.3) multiplies by that denominator.
-- TODO(paper-gap): Remarks 3.4.2.3–3.4.2.4 assert attainment of maxima on
-- arbitrary bounded sets. The compact closure gives a bound. The small-norm
-- estimate (3.4.2.17) also omits the polar subtraction for the full theta sum.

end Applications

section Eigendistributions

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

local notation "isEigen(" c "," T ")" =>
  (∀ g : Rˣ, ∀ f : ℬ(R), (T) (schwartzBruhatUnitTranslate g f) = (c) g * (T) f)

/-- Paper: Definition 3.4.3.1, p. 151. The weight condition is preserved
by zero, addition and complex scalar multiplication. -/
theorem schwartzBruhatEigen_submodule (c : QuasiCharacter Rˣ) :
    isEigen(c, (0 : StrongDual ℂ ℬ(R))) ∧
      (∀ T U : StrongDual ℂ ℬ(R), isEigen(c, T) → isEigen(c, U) → isEigen(c, T + U)) ∧
      (∀ (a : ℂ) (T : StrongDual ℂ ℬ(R)), isEigen(c, T) → isEigen(c, a • T)) := by sorry

-- TODO(paper-gap): The right-translation gloss in Definition 3.4.3.1 reverses
-- the action of (2.1.2.2) and the weight condition recalled in Definition 5.5.1.1.

/-- Paper: Definition 3.4.3.1(1)–(2), p. 151. The eigendistributions are the
continuous functionals that take translation by a unit to multiplication by its weight.
Deviation: The action on test functions is `ρ(g, f)(x) = f(g⁻¹x)`, as in
Equation (2.1.2.2) and Definition 5.5.1.1. -/
def schwartzBruhatEigendistributions (c : QuasiCharacter Rˣ) : Submodule ℂ (StrongDual ℂ ℬ(R)) where
  carrier := {T | isEigen(c, T)}
  zero_mem' := (schwartzBruhatEigen_submodule c).1
  add_mem' := (schwartzBruhatEigen_submodule c).2.1 _ _
  smul_mem' a := (schwartzBruhatEigen_submodule c).2.2 a _

/-- Paper: Definition 3.4.3.1(1)–(2), p. 151. Evaluation at zero belongs
to the weight-one subspace, since unit multiplication fixes zero. -/
theorem schwartzBruhatEigendistributions_zeroEval :
    ∃ T : StrongDual ℂ ℬ(R), T ∈ schwartzBruhatEigendistributions (1 : QuasiCharacter Rˣ) ∧
      ∀ f : ℬ(R), T f = f (Multiplicative.ofAdd 0) := by sorry

/-- Paper: Definition 3.4.3.1(1)–(2), p. 151. The weight subspace is
closed in the strong topology of the continuous dual. -/
theorem schwartzBruhatEigendistributions_isClosed (c : QuasiCharacter Rˣ) :
    IsClosed (schwartzBruhatEigendistributions c : Set (StrongDual ℂ ℬ(R))) := by sorry

end Eigendistributions

/-- Paper: Definition 3.4.3.1(2), p. 151. The global weight subspace uses the
pullback of the quasi-character from the idele classes to the ideles. -/
def adelicEigendistributions (c : X) : Submodule ℂ (StrongDual ℂ ℬ(𝔸[F])) :=
  schwartzBruhatEigendistributions
    (c.comp ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ : QuasiCharacter I_F)

/-- Paper: Definition 3.4.3.1(2), p. 151. At global weight one,
evaluation at the zero adele is an eigendistribution. -/
theorem adelicEigendistributions_zeroEval :
    ∃ T : StrongDual ℂ ℬ(𝔸[F]), T ∈ adelicEigendistributions (1 : X) ∧
      ∀ f : ℬ(𝔸[F]), T f = f (Multiplicative.ofAdd 0) := by sorry

section Gaussians

local notation "realCoord(" h ")" => InfinitePlace.Completion.ringEquivRealOfIsReal h
local notation "complexCoord(" h ")" => InfinitePlace.Completion.ringEquivComplexOfIsComplex h

-- TODO(paper-gap): The complex monomials in (3.4.3.5)–(3.4.3.6) have the same
-- angular weight as the character, so their local zeta integrals vanish at nonzero weight.

open Classical in
/-- Paper: Definition 3.4.3.2(1)–(2), p. 152. The local real Gaussian is
even or odd according to the character on signs. The complex Gaussian
has angular exponent opposite to the character.
Deviation: The monomials in (3.4.3.5)–(3.4.3.6) are conjugated so that the
angular factors cancel in the local zeta integral. -/
def infiniteStandardGaussianValue (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) (x : w.Completion) : ℂ :=
  if h : w.IsReal then
    let y := realCoord(h) x
    let parity := if χ (-1) = 1 then (1 : ℝ) else y
    (parity * Real.exp (-Real.pi * y ^ 2) : ℝ)
  else
    let e := complexCoord(InfinitePlace.not_isReal_iff_isComplex.mp h)
    let c : ℂˣ →ₜ* ℂ :=
      (circleToComplex).comp (χ.comp ⟨Units.map e.symm.toMonoidHom,
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp h)).symm.continuous.units_map _⟩)
    let m := (existsUnique_complexUnits_character_parameters c
      (fun _ ↦ Circle.norm_coe _)).exists.choose.2
    let z := e x
    let monomial := if 0 ≤ m then (star z) ^ m.natAbs else z ^ m.natAbs
    monomial * Complex.exp (-2 * (Real.pi : ℂ) * z * star z) / (2 * (Real.pi : ℂ))

/-- Paper: Definition 3.4.3.2(1)–(2), p. 152. The real and complex
Gaussian formulas give Schwartz–Bruhat test functions on the completion. -/
theorem infiniteStandardGaussian_mem (w : InfinitePlace F) (χ : PontryaginDual w.Completionˣ) :
    (fun x : Multiplicative w.Completion ↦ infiniteStandardGaussianValue w χ x.toAdd) ∈
      schwartzBruhatSubmodule (Multiplicative w.Completion) := by sorry

/-- Paper: Definition 3.4.3.2(1)–(2), p. 152. The standard infinite-place
test function is the Gaussian of the sign or angular weight.
Deviation: The complex Gaussian uses the conjugated monomials of `infiniteStandardGaussianValue`. -/
def infiniteStandardGaussian (w : InfinitePlace F) (χ : PontryaginDual w.Completionˣ) :
    ℬ(w.Completion) :=
  ⟨fun x ↦ infiniteStandardGaussianValue w χ x.toAdd, infiniteStandardGaussian_mem w χ⟩

open Classical in
/-- Paper: Equations (3.4.3.3) and (3.4.3.5), p. 152. At zero and weight
one, the real Gaussian equals one and the complex Gaussian equals one over two pi. -/
theorem infiniteStandardGaussian_trivial_zero (w : InfinitePlace F) :
    infiniteStandardGaussian w 1 (Multiplicative.ofAdd 0) =
      if w.IsReal then 1 else (2 * (Real.pi : ℂ))⁻¹ := by sorry

local notation "integerUnits(" v ")" => ((HeightOneSpectrum.adicCompletionIntegers F v).units)
local notation "unramified(" v "," c ")" => (∀ u ∈ integerUnits(v), c u = (1 : ℂ))

open Classical in
/-- Paper: Definition 3.4.3.2(3), p. 152. The finite Gaussian is the
integer-ring indicator for unramified weights. For ramified weights it
is the inverse quasi-character on the integer units, extended by zero. -/
def finiteStandardGaussianValue (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ)
    (x : v.adicCompletion F) : ℂ :=
  if unramified(v, c) then
    (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ ↦ 1) x
  else
    (Units.val '' integerUnits(v)).indicator
      (fun y ↦ if hy : y ≠ 0 then (c (Units.mk0 y hy))⁻¹ else 0) x

/-- Paper: Definition 3.4.3.2(3), p. 152. Both finite Gaussian formulas
give Schwartz–Bruhat test functions on the completion. -/
theorem finiteStandardGaussian_mem (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ) :
    (fun x : Multiplicative (v.adicCompletion F) ↦ finiteStandardGaussianValue v c x.toAdd) ∈
      schwartzBruhatSubmodule (Multiplicative (v.adicCompletion F)) := by sorry

/-- Paper: Definition 3.4.3.2(3), p. 152. The finite-place standard
Gaussian is the bundled test function given by the local indicator formula. -/
def finiteStandardGaussian (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ) :
    ℬ(v.adicCompletion F) :=
  ⟨fun x ↦ finiteStandardGaussianValue v c x.toAdd, finiteStandardGaussian_mem v c⟩

/-- Paper: Equations (3.4.3.7)–(3.4.3.8), p. 152. On an integer unit,
the local Gaussian takes the reciprocal of the character value. -/
theorem finiteStandardGaussian_integerUnit (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ)
    (u : (v.adicCompletion F)ˣ) (hu : u ∈ integerUnits(v)) :
    finiteStandardGaussian v c (Multiplicative.ofAdd u.val) = (c u)⁻¹ := by sorry

local notation "infiniteUnitaryRestriction(" χ "," w ")" =>
  ((χ).comp ⟨IdeleClassGroup.ofCompletion (𝓞 F) F w, continuous_ideleClass_ofCompletion F w⟩)

local notation "globalGaussianTest(" χ ")" => fun x : Multiplicative 𝔸[F] ↦
  (∏ w : InfinitePlace F,
    infiniteStandardGaussian w (infiniteUnitaryRestriction(χ,w))
      (Multiplicative.ofAdd (x.toAdd.1 w))) *
    ∏ᶠ v : V, finiteStandardGaussian v (finitePlaceRestriction F v (ideleClassNormTwist (χ) 0))
      (Multiplicative.ofAdd (x.toAdd.2 v))

/-- Paper: Equation (3.4.3.9), p. 152. The restricted product of local
Gaussians is Schwartz–Bruhat on the adeles. -/
theorem adelicStandardGaussian_mem (χ : PontryaginDual C_F) :
    globalGaussianTest(χ) ∈ schwartzBruhatSubmodule (Multiplicative 𝔸[F]) := by sorry

/-- Paper: Equation (3.4.3.9), p. 152. The adelic Gaussian is the pointwise
restricted product of the indicated local Gaussians.
Deviation: The component is specified by a unitary representative, and the complex
factors use the conjugated monomials of `infiniteStandardGaussianValue`. -/
def adelicStandardGaussian (χ : PontryaginDual C_F) : ℬ(𝔸[F]) :=
  ⟨globalGaussianTest(χ), adelicStandardGaussian_mem χ⟩

/-- Paper: Equation (3.4.3.9), p. 152. The trivial-character Gaussian
at the zero adele has one factor of one over two pi per complex place. -/
theorem adelicStandardGaussian_trivial_zero :
    adelicStandardGaussian (1 : PontryaginDual C_F) (Multiplicative.ofAdd 0) =
      (2 * (Real.pi : ℂ))⁻¹ ^ InfinitePlace.nrComplexPlaces F := by sorry

/-- Paper: Definition 3.4.3.2, p. 152. The adelic Gaussian depends only on
the restriction of the unitary representative to the norm-one classes. -/
theorem adelicStandardGaussian_eq_of_restriction (χ ψ : PontryaginDual C_F)
    (h : normOneRestriction (G := C_F) (ideleClassNorm F) (ideleClassNormTwist χ 0) =
      normOneRestriction (G := C_F) (ideleClassNorm F) (ideleClassNormTwist ψ 0)) :
    adelicStandardGaussian χ = adelicStandardGaussian ψ := by sorry

-- TODO(paper-gap): Even with the corrected complex Gaussians, the Tamagawa
-- zeta integral has an extra factor of |d_F|^(-1/2) relative to the Euler product of §3.2.

/-- Paper: Paragraph after Equation (3.4.3.9), p. 152.
The completed function with the Gaussian normalization is the continued
global zeta function of the standard Gaussian on the chosen component.
Deviation: This uses the corrected complex Gaussian and the Tamagawa measures.
The comparison with the completed Euler product of §3.2 includes the factor `|d_F|^(-1/2)`. -/
def gaussianCompletedHeckeL (χ : PontryaginDual C_F) (s : ℂ) : ℂ :=
  globalIdelicZFunction (adelicStandardGaussian χ) (ideleClassNormTwist χ s)

/-- Paper: Paragraph after Equation (3.4.3.9), p. 152.
In the half-plane of absolute convergence, the Gaussian normalization
is the global zeta integral of the Gaussian. -/
theorem gaussianCompletedHeckeL_eq_integral (χ : PontryaginDual C_F) (s : ℂ)
    (hs : 1 < s.re) :
    gaussianCompletedHeckeL χ s =
      globalIdelicZetaIntegral (adelicStandardGaussian χ) (ideleClassNormTwist χ s) := by sorry

/-- Paper: Paragraph after Equation (3.4.3.9), p. 152. In the half-plane of
absolute convergence the Gaussian zeta function gives the completed Euler product of §3.2
scaled by the product of the finite integer-unit Tamagawa masses.
Deviation: The scale is the inverse square root of the absolute discriminant. -/
theorem gaussianCompletedHeckeL_eq_completedHeckeL (χ : PontryaginDual C_F) (s : ℂ)
    (hs : 1 < s.re) :
    gaussianCompletedHeckeL χ s =
      ((Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ : ℝ) * completedHeckeL χ ⟨s, hs⟩ := by sorry

/-- Paper: Theorem 3.4.3.3(1), pp. 152–153. At a finite place each
quasi-character has a one-dimensional eigendistribution space. -/
theorem finiteEigendistributions_rank (v : V) (c : QuasiCharacter (v.adicCompletion F)ˣ) :
    Module.rank ℂ (schwartzBruhatEigendistributions c) = 1 := by sorry

/-- Paper: Theorem 3.4.3.3(1), pp. 152–153. At an infinite place each
quasi-character has a one-dimensional eigendistribution space. -/
theorem infiniteEigendistributions_rank (w : InfinitePlace F) (c : QuasiCharacter w.Completionˣ) :
    Module.rank ℂ (schwartzBruhatEigendistributions c) = 1 := by sorry

-- TODO(paper-gap): At a finite place (3.4.3.13) needs the Tamagawa mass of the
-- integer units with the normalized tests in (3.4.3.10)–(3.4.3.11).

/-- Paper: Theorem 3.4.3.3(1), p. 153. The holomorphic family at a finite place
is normalized on the integer-ring indicator in the unramified case and on the inverse
character supported on the integer units in the ramified case. Scaling by the Euler
factor and the unit mass gives the zeta function away from the trivial quasi-character.
Deviation: Equation (3.4.3.13) includes the integer-unit Tamagawa mass. -/
theorem finiteEigendistribution_normalized (v : V) (χ : PontryaginDual (v.adicCompletion F)ˣ) :
    let twist := quasiCharacterNormTwist (finiteNorm(v)) (continuous_finiteLocalModule v)
      ((circleToComplex).comp χ)
    ∃ D : ℂ → StrongDual ℂ ℬ(v.adicCompletion F), VectorHolomorphicOn D univ ∧
      (∀ s : ℂ, ∀ T : StrongDual ℂ ℬ(v.adicCompletion F),
        T = D s ↔ T ∈ schwartzBruhatEigendistributions (twist s) ∧
          T (finiteStandardGaussian v (twist s)) = 1) ∧
      ∀ s : ℂ, twist s ≠ 1 → ∀ f : ℬ(v.adicCompletion F),
        finiteLocalIdelicZFunction v f (twist s) =
          ((finiteLocalMultiplicativeTamagawaMeasure F v) integerUnits(v)).toReal *
            finiteLocalEulerFactor v (twist s) * D s f := by sorry

/-- Paper: Theorem 3.4.3.3(1), p. 153. At an infinite place the normalized
eigendistribution evaluates to one on the Gaussian and varies holomorphically.
Multiplication by the Euler factor recovers the local zeta function.
Deviation: The complex Gaussian uses the corrected angular weight, and the meromorphic
identity (3.4.3.13) is expressed off a discrete set of exponents. -/
theorem infiniteEigendistribution_normalized (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) :
    let twist := quasiCharacterNormTwist (infiniteNorm(w)) (continuous_infiniteLocalModule w)
      ((circleToComplex).comp χ)
    ∃ D : ℂ → StrongDual ℂ ℬ(w.Completion), VectorHolomorphicOn D univ ∧
      (∀ s : ℂ, ∀ T : StrongDual ℂ ℬ(w.Completion),
        T = D s ↔ T ∈ schwartzBruhatEigendistributions (twist s) ∧
          T (infiniteStandardGaussian w χ) = 1) ∧
      ∀ᶠ s : ℂ in codiscrete ℂ, ∀ f : ℬ(w.Completion),
        infiniteLocalIdelicZFunction w f (twist s) =
          infiniteLocalEulerFactor w (twist s) * D s f := by sorry

/-- Paper: Theorem 3.4.3.3(2), p. 153. The global eigendistributions of
each idelic weight form a one-dimensional space. -/
theorem adelicEigendistributions_rank (c : X) :
    Module.rank ℂ (adelicEigendistributions c) = 1 := by sorry

/-- Paper: Theorem 3.4.3.3(2), p. 153. The unique global eigendistribution normalized
on the adelic Gaussian varies holomorphically. Multiplication by the Gaussian zeta
function recovers the global zeta function away from its possible poles.
Deviation: The scalar factor uses the Gaussian normalization of p. 152, including
its Tamagawa scale relative to the completed Euler product in §3.2. -/
theorem adelicEigendistribution_normalized (χ : PontryaginDual C_F) :
    ∃ D : ℂ → StrongDual ℂ ℬ(𝔸[F]), VectorHolomorphicOn D univ ∧
      (∀ s : ℂ, ∀ T : StrongDual ℂ ℬ(𝔸[F]),
        T = D s ↔ T ∈ adelicEigendistributions (ideleClassNormTwist χ s) ∧
          T (adelicStandardGaussian χ) = 1) ∧
      ∀ s : ℂ, ideleClassNormTwist χ s ≠ 1 →
        ideleClassNormTwist χ s ≠ ideleClassNormTwist (1 : PontryaginDual C_F) 1 →
        ∀ f : ℬ(𝔸[F]), globalIdelicZFunction f (ideleClassNormTwist χ s) =
          gaussianCompletedHeckeL χ s * D s f := by sorry

/-- Paper: Equation (3.4.3.14), p. 153. The normalized global eigendistribution
evaluates on a restricted pure tensor as the product of normalized local evaluations.
Deviation: Pointwise factorization specifies the test tensor. The product of finite-place
evaluations has finite support because the local factors are normalized on the standard Gaussians. -/
theorem adelicEigendistribution_apply_pureTensor (χ : PontryaginDual C_F) (s : ℂ) :
    let c := ideleClassNormTwist χ s
    ∀ (T : StrongDual ℂ ℬ(𝔸[F]))
      (TArch : (w : InfinitePlace F) → StrongDual ℂ ℬ(w.Completion))
      (TFin : (v : V) → StrongDual ℂ ℬ(v.adicCompletion F)),
      T ∈ adelicEigendistributions c → T (adelicStandardGaussian χ) = 1 →
      (∀ w, TArch w ∈ schwartzBruhatEigendistributions (infinitePlaceRestriction F w c) ∧
        TArch w (infiniteStandardGaussian w (infiniteUnitaryRestriction(χ,w))) = 1) →
      (∀ v, TFin v ∈ schwartzBruhatEigendistributions (finitePlaceRestriction F v c) ∧
        TFin v (finiteStandardGaussian v (finitePlaceRestriction F v c)) = 1) →
      ∀ (f : ℬ(𝔸[F])) (fArch : (w : InfinitePlace F) → ℬ(w.Completion))
        (fFin : (v : V) → ℬ(v.adicCompletion F)),
        (∀ᶠ v in cofinite, fFin v = finiteStandardGaussian v (finitePlaceRestriction F v c)) →
        (∀ x : 𝔸[F], f (Multiplicative.ofAdd x) =
          (∏ w : InfinitePlace F, fArch w (Multiplicative.ofAdd (x.1 w))) *
            ∏ᶠ v : V, fFin v (Multiplicative.ofAdd (x.2 v))) →
        T f = (∏ w : InfinitePlace F, TArch w (fArch w)) * ∏ᶠ v : V, TFin v (fFin v) := by sorry

-- Remark 3.4.3.4, p. 153. The tensor acts on the full test space by continuity.
-- The completed archimedean product uses `schwartzBruhat_kernel_equiv`; the finite
-- stages and their passage to the adeles use `sAdeleSchwartz_inductiveTensor_equiv`
-- and `sAdeleSchwartzToGlobal_finalTopology`.

end Gaussians

end RiemannMasullo
