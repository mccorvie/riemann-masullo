module

public import RiemannMasullo.AppA_AlgebraicNT.Sec2b
public import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.Topology.Algebra.Group.Units

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Measure.Haar.Extension
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.IsOpenUnits
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Haar measures

Masullo, §A.3, pp. 555–562.
-/

@[expose] public noncomputable section

set_option maxSynthPendingDepth 8

namespace RiemannMasullo

open Function MeasureTheory NumberField IsDedekindDomain InfinitePlace.Completion Set
open scoped Classical ENNReal NNReal NumberField.AdeleRing Pointwise

variable (F : Type*) [Field F] [NumberField F]

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "P[" F "]" => IdeleGroup.principalSubgroup (𝓞 F) F
local notation "A[" F "]" => AddSubgroup.toSubgroup (AdeleRing.principalSubgroup (𝓞 F) F)
local notation "N[" F "]" => MonoidHom.ker (ideleNorm F)
local notation "C₁[" F "]" => MonoidHom.ker (ideleClassNorm F)

local instance (v : InfinitePlace F) : MeasurableSpace v.Completion := borel _
local instance : MeasurableSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (MeasurableSpace ((v : InfinitePlace F) → v.Completion))
local instance (v : Primes(F)) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : Primes(F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
local instance (v : Primes(F)) : LocallyCompactSpace (v.adicCompletion F) :=
  locallyCompactSpace_adicCompletion v
local instance (v : Primes(F)) : LocallyCompactSpace (v.adicCompletion F)ˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.adicCompletion F)).locallyCompactSpace
local instance (v : Primes(F)) : MeasurableSpace (v.adicCompletion F)ˣ := borel _
local instance (v : Primes(F)) : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
local instance : MeasurableSpace 𝔸[F] := borel _
local instance : MeasurableSpace (Multiplicative 𝔸[F] ⧸ A[F]) := borel _
local instance : MeasurableSpace 𝕀[F] := borel _
local instance : MeasurableSpace C[F] := borel _
local instance : MeasurableSpace (C[F] ⧸ C₁[F]) := borel _
local instance : MeasurableSpace (𝕀[F] ⧸ N[F]) := borel _

variable (S : Finset (Primes(F)))

local notation "dₛ" => RingHom.comp (adeleProjection F S)
  (RingHom.comp (Subring.subtype (integralAdelesOutside F S)) (integralAdeleDiagonal F S))
local notation "Aₛ" => AddSubgroup.toSubgroup (AddMonoidHom.range (RingHom.toAddMonoidHom dₛ))
local notation "𝕀ₛ" => (SAdeleRing F S)ˣ
local notation "Nₛ" => MonoidHom.ker (sIdeleNorm F S)

local instance : MeasurableSpace (SAdeleRing F S) :=
  inferInstanceAs (MeasurableSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
local instance : MeasurableSpace (Multiplicative (SAdeleRing F S) ⧸ Aₛ) := borel _
local instance : MeasurableSpace (𝕀ₛ ⧸ Nₛ) := borel _

open scoped IsDedekindDomain.FiniteAdeleRing RestrictedProduct in
/-- Paper: Definition A.3.1.1, p. 555. Exactly one regular additive Haar measure on
the adeles gives the additive quotient mass one when the diagonal has counting measure. -/
theorem additiveTamagawaMeasure_existsUnique :
    ∃! μ : Measure 𝔸[F], μ.IsAddHaarMeasure ∧ μ.Regular ∧
      ∃ ν : Measure (Multiplicative 𝔸[F] ⧸ A[F]),
        IsWeilQuotientMeasure A[F] (show Measure (Multiplicative 𝔸[F]) from μ)
          Measure.count ν ∧ ν univ = 1 := by
  classical
  let G := Multiplicative 𝔸[F]
  let H := A[F]
  let Q := G ⧸ H
  obtain ⟨-, hclosed, hdiscrete, -, -, hcompact, -, -⟩ := adele_additive_quotient.{_, 0} F
  let : CompactSpace Q := hcompact
  let : DiscreteTopology H := isDiscrete_iff_discreteTopology.mp hdiscrete
  let (v : Primes(F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  let : Fact (∀ v : Primes(F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  let : LocallyCompactSpace 𝔸ᶠ[𝓞 F, F] := by
    change LocallyCompactSpace (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F])
    infer_instance
  let : LocallyCompactSpace G := by
    change LocallyCompactSpace (InfiniteAdeleRing F × 𝔸ᶠ[𝓞 F, F])
    infer_instance
  let : T2Space G := by
    change T2Space (((v : InfinitePlace F) → v.Completion) ×
      (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  let : IsClosed (H : Set G) := hclosed
  let : BorelSpace G := ⟨rfl⟩
  let : BorelSpace Q := ⟨rfl⟩
  let : (Measure.count : Measure H).IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  let ses := TopologicalGroup.IsSES.ofClosedSubgroup H hclosed
  let count : Measure H := Measure.count
  let : count.IsHaarMeasure := inferInstanceAs (Measure.count : Measure H).IsHaarMeasure
  -- Normalize Haar measure on the compact quotient using the whole space.
  let K : TopologicalSpace.PositiveCompacts Q := ⟨⟨univ, isCompact_univ⟩, by simp⟩
  let ν : Measure Q := Measure.haarMeasure K
  have hν : ν univ = 1 := Measure.haarMeasure_self (K₀ := K)
  let μ := ses.inducedMeasure count ν
  let : μ.Regular := ses.inducedMeasure_regular count ν
  have hμ : ∀ f : C(G, ℂ), HasCompactSupport f →
      (∫ x, f x ∂μ) = ∫ q, lcaCosetIntegral H count f q ∂ν := by
    intro f hf
    let fc : CompactlySupportedContinuousMap G ℂ := ⟨f, hf⟩
    have hfiber (q : Q) : ses.pushforward count fc q = lcaCosetIntegral H count f q := by
      calc
        ses.pushforward count fc q =
            ses.pushforward count fc (QuotientGroup.mk' H q.out) :=
          congrArg (ses.pushforward count fc) (QuotientGroup.out_eq' q).symm
        _ = lcaCosetIntegral H count f q := ses.pushforward_apply_apply count fc q.out
    -- The induced measure formula for real functions applies to both complex coordinates.
    have hcoord (L : ℂ →L[ℝ] ℝ) :
        L (∫ x, f x ∂μ) = L (∫ q, ses.pushforward count fc q ∂ν) := by
      let g : CompactlySupportedContinuousMap G ℝ :=
        ⟨⟨fun x ↦ L (f x), L.continuous.comp f.continuous⟩, hf.comp_left L.map_zero⟩
      change L (∫ x, fc x ∂μ) = _
      rw [← L.integral_comp_comm (fc.integrable (μ := μ)),
        ← L.integral_comp_comm ((ses.pushforward count fc).integrable (μ := ν))]
      change (∫ x, g x ∂μ) = ∫ q, L (ses.pushforward count fc q) ∂ν
      rw [ses.integral_inducedMeasure, ses.integrate_apply]
      congr with q
      obtain ⟨x, rfl⟩ := ses.isOpenQuotientMap.surjective q
      rw [ses.pushforward_apply_apply, ses.pushforward_apply_apply,
        ← L.integral_comp_comm (ses.pullback fc x).integrable]
      rfl
    simp_rw [← hfiber]
    exact Complex.ext (hcoord Complex.reCLM) (hcoord Complex.imCLM)
  refine ⟨μ, ⟨?_, ses.inducedMeasure_regular count ν, ν, ⟨inferInstance, inferInstance, hμ⟩, hν⟩,
    ?_⟩
  · have hhaar := ses.isHaarMeasure_inducedMeasure count ν
    exact
      { toIsFiniteMeasureOnCompacts := hhaar.toIsFiniteMeasureOnCompacts
        toIsOpenPosMeasure := hhaar.toIsOpenPosMeasure
        map_add_left_eq_self := fun x ↦ hhaar.map_mul_left_eq_self (Multiplicative.ofAdd x) }
  rintro μ' ⟨-, hregular, ν', ⟨hhaar', hregular', hweil⟩, hν'⟩
  let : (show Measure G from μ').Regular := hregular
  let : ν'.IsHaarMeasure := hhaar'
  let : ν'.Regular := hregular'
  have heq : ν' = ν := by
    have hscale := Measure.isMulLeftInvariant_eq_smul_of_regular ν' ν
    have hmass := congrArg (fun m : Measure Q ↦ m univ) hscale
    change ν' univ = (ν'.haarScalarFactor ν : ℝ≥0∞) * ν univ at hmass
    have hfactor : ν'.haarScalarFactor ν = 1 := by
      rw [hν', hν, mul_one] at hmass
      exact ENNReal.coe_inj.mp hmass.symm
    rw [hscale, hfactor, one_smul]
  subst ν'
  apply Measure.ext_of_integral_eq_on_compactlySupported (X := G)
  intro f
  let fc : C(G, ℂ) := ⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hc : HasCompactSupport fc := f.hasCompactSupport.comp_left Complex.ofReal_zero
  have heq := (hweil fc hc).trans (hμ fc hc).symm
  apply Complex.ofReal_injective
  calc
    Complex.ofReal (∫ x : G, f x ∂(show Measure G from μ')) =
        ∫ x : G, (f x : ℂ) ∂(show Measure G from μ') := integral_complex_ofReal.symm
    _ = ∫ x : G, (f x : ℂ) ∂μ := heq
    _ = Complex.ofReal (∫ x : G, f x ∂μ) := integral_complex_ofReal

/-- Paper: Definition A.3.1.1, p. 555. The additive Tamagawa measure is the
adelic Haar measure normalized to give the quotient by the diagonal mass one. -/
def additiveTamagawaMeasure : Measure 𝔸[F] :=
  (additiveTamagawaMeasure_existsUnique F).exists.choose

/-- Paper: Definition A.3.1.1, p. 555. The adelic measure has a Weil quotient
of mass one with counting measure on the diagonal. -/
theorem additiveTamagawaMeasure_quotientVolume :
    ∃ ν : Measure (Multiplicative 𝔸[F] ⧸ A[F]),
      IsWeilQuotientMeasure A[F] (show Measure (Multiplicative 𝔸[F]) from
        additiveTamagawaMeasure F) Measure.count ν ∧ ν univ = 1 :=
  (Classical.choose_spec (additiveTamagawaMeasure_existsUnique F).exists).2.2

/-- Paper: Definition A.3.1.1, p. 555. The additive Tamagawa measure of the
chosen adelic fundamental domain equals the mass of the additive quotient, namely one. -/
theorem additiveTamagawaMeasure_fundamentalDomain :
    additiveTamagawaMeasure F (adeleFundamentalDomain F (RingOfIntegers.basis F)) = 1 := by sorry

/-- Paper: Definition A.3.1.1, p. 555. Exactly one regular additive Haar measure on
the S-adeles gives the quotient by the diagonal S-integers mass one. -/
theorem sAdditiveCovolumeOneMeasure_existsUnique :
    ∃! μ : Measure (SAdeleRing F S), μ.IsAddHaarMeasure ∧ μ.Regular ∧
      ∃ ν : Measure (Multiplicative (SAdeleRing F S) ⧸ Aₛ),
        IsWeilQuotientMeasure Aₛ (show Measure (Multiplicative (SAdeleRing F S)) from μ)
          Measure.count ν ∧ ν univ = 1 := by sorry

/-- Paper: Definition A.3.1.1, p. 555. This normalization gives the additive
quotient by the diagonal S-integers mass one.
Deviation: The notation distinguishes it from the product measure of Definition A.3.4.1. -/
def sAdditiveCovolumeOneMeasure : Measure (SAdeleRing F S) :=
  (sAdditiveCovolumeOneMeasure_existsUnique F S).exists.choose

/-- Paper: Definition A.3.1.1, p. 555. An S-adelic fundamental domain has mass one
for the additive measure normalized by the quotient. -/
theorem sAdditiveCovolumeOneMeasure_fundamentalDomain :
    sAdditiveCovolumeOneMeasure F S
      (sAdeleFundamentalDomain F S (RingOfIntegers.basis F)) = 1 := by sorry

/-- Paper: Definition A.3.1.2(1)–(2), p. 556. Transfer Lebesgue measure from the
real line or twice plane Lebesgue measure from the complex line to the completion. -/
def infiniteLocalAdditiveTamagawaMeasure (v : InfinitePlace F) : Measure v.Completion :=
  if h : v.IsReal then
    Measure.map (ringEquivRealOfIsReal h).symm (volume : Measure ℝ)
  else
    Measure.map (ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp h)).symm
      (2 • (volume : Measure ℂ))

/-- Paper: Definition A.3.1.2(1)–(2), p. 556. The local archimedean additive measure
assigns mass one to the real unit interval and mass two to the complex unit square. -/
theorem infiniteLocalAdditiveTamagawaMeasure_unitBox (v : InfinitePlace F) :
    (∀ h : v.IsReal, infiniteLocalAdditiveTamagawaMeasure F v
      ((ringEquivRealOfIsReal h).symm '' Icc (0 : ℝ) 1) = 1) ∧
    (∀ h : v.IsComplex, infiniteLocalAdditiveTamagawaMeasure F v
      ((ringEquivComplexOfIsComplex h).symm '' {z : ℂ | z.re ∈ Icc 0 1 ∧ z.im ∈ Icc 0 1}) = 2) :=
  by sorry

-- The exponent of v in the global different is the exponent of the local different.
local notation "differentExp(" F ", " v ")" =>
  multiplicity (HeightOneSpectrum.asIdeal v) (differentIdeal ℤ (𝓞 F))
local notation "differentMass(" F ", " v ")" =>
  Inv.inv (ENNReal.ofReal (Real.sqrt (Nat.cast (Ideal.absNorm (HeightOneSpectrum.asIdeal v)) ^
    differentExp(F, v))))

/-- Paper: Definition A.3.1.2(3), p. 556. Scale additive Haar measure so that the
integer ring has mass equal to the inverse square root of the norm of the local different.
Deviation: The norm is computed using the corresponding exponent in the global different. -/
def finiteLocalAdditiveTamagawaMeasure (v : Primes(F)) : Measure (v.adicCompletion F) :=
  let μ := Measure.addHaar (G := v.adicCompletion F)
  (differentMass(F, v) / μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) • μ

/-- Paper: Definition A.3.1.2(3), p. 556. The mass of the local integer ring is
the inverse square root of the local different norm. -/
theorem finiteLocalAdditiveTamagawaMeasure_integers (v : Primes(F)) :
    finiteLocalAdditiveTamagawaMeasure F v (v.adicCompletionIntegers F : Set (v.adicCompletion F)) =
      differentMass(F, v) := by sorry

/-- Paper: Definition A.3.1.2, p. 556. The local additive Tamagawa measures
are additive Haar measures on their completions. -/
theorem finiteLocalAdditiveTamagawaMeasure_isAddHaar (v : Primes(F)) :
    (finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure := by sorry

/-- Paper: §A.3.1, p. 556. The local different contributes mass one at
all but finitely many places, so the finite-tail products have finite support. -/
theorem finiteLocalTamagawaMass_finite :
    {v : Primes(F) | differentMass(F, v) ≠ 1}.Finite := by sorry

/-- Paper: Lemma A.3.1.3, p. 556. The global additive measure is the restricted
product of the local measures, expressed on rectangles with integral tails.
Deviation: The infinite places are grouped into a finite product measure. -/
theorem additiveTamagawaMeasure_restrictedProduct
    (B : Set (InfiniteAdeleRing F)) (hB : MeasurableSet B)
    (U : (v : S) → Set (v.val.adicCompletion F)) (hU : ∀ v, MeasurableSet (U v)) :
    additiveTamagawaMeasure F
        {a | a.1 ∈ B ∧ (∀ v : S, a.2 v.val ∈ U v) ∧ a ∈ integralAdelesOutside F S} =
      Measure.pi (infiniteLocalAdditiveTamagawaMeasure F) B *
        (∏ v : S, finiteLocalAdditiveTamagawaMeasure F v.val (U v)) *
          ∏ᶠ v : {v : Primes(F) // v ∉ S}, differentMass(F, v.val) := by sorry

-- TODO(paper-gap): The S-local equality in (A.3.1.3) fails for the quotient-volume-one
-- measure of Definition A.3.1.1. For F = ℚ(i) and S archimedean, the product has
-- quotient mass 2, since the Gaussian integers have Euclidean covolume 1 and ν∞ = 2 dx dy.

/-- Paper: Lemma A.3.1.4, p. 556. Multiplication of a Borel set by an idele
scales any additive Haar measure by the idelic norm. -/
theorem adeleHaar_mul_image (μ : Measure 𝔸[F]) [μ.IsAddHaarMeasure]
    (g : 𝕀[F]) (B : Set 𝔸[F]) (hB : MeasurableSet B) :
    μ ((fun a : 𝔸[F] ↦ g.val * a) '' B) = (↑(ideleNorm F g).val : ℝ≥0∞) * μ B := by sorry


section SelfDuality

variable {R : Type*} [CommRing R] [TopologicalSpace R] [MeasurableSpace R]

local instance : MeasurableSpace (PontryaginDual (Multiplicative R)) := borel _

/-- Paper: §A.3.1.1, p. 557. After identifying a ring's additive group with its dual
by the pairing `(x,y) ↦ ψ (x*y)`, the Fourier transform uses the conjugate character. -/
def tamagawaFourier (μ : Measure R) (ψ : R → Circle) (f : R → ℂ) (y : R) : ℂ :=
  ∫ x, f x * star (ψ (x * y) : ℂ) ∂μ

/-- Paper: §A.3.1.1, p. 557. Under the character pairing, the Fourier integral is
the transform of §D.1.1 evaluated at the character attached to the frequency. -/
theorem tamagawaFourier_eq_lcaFourier (μ : Measure R) (ψ : R → Circle) (f : R → ℂ)
    (y : R) (χ : PontryaginDual (Multiplicative R))
    (hχ : ∀ x : R, χ (Multiplicative.ofAdd x) = ψ (x * y)) :
    tamagawaFourier μ ψ f y = lcaFourier (G := Multiplicative R) μ
      (fun x ↦ f x.toAdd) χ := by
  unfold tamagawaFourier lcaFourier
  congr 1
  funext x
  rw [← hχ]
  rfl

/-- Paper: §A.3.1.1, p. 557. A measure is self-dual when the pairing identifies the
additive group with its Pontryagin dual and transports the measure to its Plancherel measure. -/
def IsTamagawaSelfDual (μ : Measure R) (ψ : R → Circle) : Prop :=
  ∃ e : Multiplicative R ≃ₜ* PontryaginDual (Multiplicative R),
    (∀ x y : R, e (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) = ψ (x * y)) ∧
      IsLCAPlancherelMeasure (G := Multiplicative R) μ
        (Measure.map e (show Measure (Multiplicative R) from μ))

end SelfDuality

/-- Paper: Example A.3.1.5, p. 557. Lebesgue measure is self-dual for the real
character with phase `2πx`. -/
theorem realTamagawaMeasure_selfDual :
    IsTamagawaSelfDual (volume : Measure ℝ) (fun x ↦ Circle.exp (2 * Real.pi * x)) := by sorry

/-- Paper: Example A.3.1.5, p. 557. Twice plane Lebesgue measure is self-dual
for the complex character with phase `4π Re(z)`. -/
theorem complexTamagawaMeasure_selfDual :
    IsTamagawaSelfDual (2 • (volume : Measure ℂ)) (fun z ↦ Circle.exp (4 * Real.pi * z.re)) :=
  by sorry

section Padic

variable (p : ℕ) [Fact p.Prime]

local instance instPadicMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
local instance : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- Paper: Example A.3.1.6, p. 557. Multiplying by the power of p that clears
the negative valuation places the result in the p-adic integer ring. -/
theorem padicStandardCharacter_integral (x : ℚ_[p]) :
    ‖(p : ℚ_[p]) ^ (-x.valuation).toNat * x‖ ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [norm_mul, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation hx, ← zpow_add₀]
  · apply zpow_le_one_of_nonpos₀
    · exact_mod_cast (Fact.out : p.Prime).one_lt.le
    · have := Int.self_le_toNat (-x.valuation)
      omega
  · exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- Paper: Example A.3.1.6, p. 557. The standard character exponentiates
the rational representative of the coset modulo the p-adic integers.
The representative uses the residue of the cleared integer modulo the clearing power.
Deviation: the sign is opposite to the printed `exp(2πit)`. With the printed sign at the real
place (Example A.3.1.5) and at the p-adic places, the product character of Example A.3.1.8 takes
the value `exp(4πi/3)` on the rational number 1/3. It must be trivial on the rationals for
Theorem 2.2.3.2 and Theorem 3.2.2.1, as in Tate's thesis, where the two kinds of place carry
opposite signs. The real character keeps the printed sign. -/
def padicStandardCharacter (x : ℚ_[p]) : Circle :=
  let n := (-x.valuation).toNat
  let a : ℤ_[p] := ⟨(p : ℚ_[p]) ^ n * x, padicStandardCharacter_integral p x⟩
  Circle.exp (-(2 * Real.pi * ((PadicInt.toZModPow n a).val : ℝ) / (p : ℝ) ^ n))

/-- Paper: Example A.3.1.6, p. 557. On a fraction with denominator a power of p,
the p-adic character has the phase opposite to the real exponential of that fraction.
Deviation: the sign, as in `padicStandardCharacter`. -/
theorem padicStandardCharacter_div_pow (a : ℤ) (n : ℕ) :
    padicStandardCharacter p ((a : ℚ_[p]) / (p : ℚ_[p]) ^ n) =
      Circle.exp (-(2 * Real.pi * ((a : ℝ) / (p : ℝ) ^ n))) := by sorry

local notation "ℤₚ" => Metric.closedBall (0 : ℚ_[p]) 1

/-- Paper: Example A.3.1.7, p. 557. The standard additive measure on the
p-adic field is Haar measure with the integer ring assigned volume one. -/
theorem padicTamagawaMeasure_existsUnique :
    ∃! μ : Measure ℚ_[p], μ.IsAddHaarMeasure ∧ μ.Regular ∧ μ (ℤₚ) = 1 := by sorry

/-- Paper: Example A.3.1.7, p. 557. Use the unique regular additive Haar
measure on the p-adic field for which the integer ring has mass one. -/
def padicTamagawaMeasure : Measure ℚ_[p] :=
  (padicTamagawaMeasure_existsUnique p).exists.choose

-- TODO(paper-gap): In (A.3.1.5) the scaling step inserts an incorrect frequency
-- shift, and the translation phase needs conjugation under (D.1.1.4).
-- The zero-translation specialization and the unit formula are unaffected.

/-- Paper: Example A.3.1.6, p. 557. The Fourier transform of the indicator of
the scaled p-adic integer ring is the reciprocal-scale indicator times the scaling factor.
Deviation: This is the valid zero-translation specialization of (A.3.1.5). -/
theorem padicTamagawaFourier_scaledIntegers (n : ℤ) :
    tamagawaFourier (padicTamagawaMeasure p) (padicStandardCharacter p)
        ((((p : ℚ_[p]) ^ n * ·) '' ℤₚ).indicator (fun _ ↦ (1 : ℂ))) =
      ((p : ℝ) ^ (-n) : ℂ) • ((((p : ℚ_[p]) ^ (-n) * ·) '' ℤₚ).indicator (fun _ ↦ (1 : ℂ))) := by sorry

/-- Paper: Example A.3.1.6, p. 557. The Fourier transform of the indicator of the
p-adic integer units is the difference in (A.3.1.6). -/
theorem padicTamagawaFourier_integerUnits :
    tamagawaFourier (padicTamagawaMeasure p) (padicStandardCharacter p)
        ({x : ℚ_[p] | ‖x‖ = 1}.indicator (fun _ ↦ (1 : ℂ))) =
      ((ℤₚ).indicator (fun _ ↦ (1 : ℂ))) - ((p : ℂ)⁻¹) • ((((p : ℚ_[p])⁻¹ * ·) '' ℤₚ).indicator (fun _ ↦ (1 : ℂ))) := by sorry

/-- Paper: Example A.3.1.7, p. 558. The standard additive measure on the p-adic field
is self-dual under the standard character. -/
theorem padicTamagawaMeasure_selfDual :
    IsTamagawaSelfDual (padicTamagawaMeasure p) (padicStandardCharacter p) := by sorry

end Padic

/-- Paper: Example A.3.1.8, p. 558. The rational adelic character multiplies the real
character and all the p-adic characters, only finitely many of which contribute. -/
def ratAdeleStandardCharacter (a : 𝔸[ℚ]) : Circle :=
  Circle.exp (2 * Real.pi * extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
    (a.1 Rat.infinitePlace)) *
    ∏ᶠ v : Primes(ℚ),
      let p := Rat.HeightOneSpectrum.primesEquiv v
      letI : Fact p.val.Prime := ⟨p.property⟩
      padicStandardCharacter p.val (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v (a.2 v))

/-- Paper: Example A.3.1.8, p. 558. On an adele supported at the real place, the
global rational character takes the value of the standard real character. -/
theorem ratAdeleStandardCharacter_real (a : 𝔸[ℚ]) (ha : a.2 = 0) :
    ratAdeleStandardCharacter a =
      Circle.exp (2 * Real.pi * extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
        (a.1 Rat.infinitePlace)) := by sorry

/-- Paper: Example A.3.1.8, p. 558. The global rational character is trivial on the
diagonally embedded rational numbers. The paper uses this without stating it; it is what
Poisson summation over the rationals needs, and it fails for the signs as printed. -/
theorem ratAdeleStandardCharacter_algebraMap (q : ℚ) :
    ratAdeleStandardCharacter (algebraMap ℚ 𝔸[ℚ] q) = 1 := by sorry

/-- Paper: Example A.3.1.8, p. 558. The additive Tamagawa measure on the rational
adeles is self-dual under the product of the standard local characters. -/
theorem ratAdditiveTamagawaMeasure_selfDual :
    IsTamagawaSelfDual (additiveTamagawaMeasure ℚ) ratAdeleStandardCharacter := by sorry

/-- Paper: Example A.3.1.9, p. 558. In (A.3.1.7) the standard adelic character is
the rational adelic character composed with the adelic trace.
Deviation: The displayed field trace is extended to the adele algebra as required by its domain. -/
def adeleStandardCharacter (a : 𝔸[F]) : Circle :=
  letI := (rationalAdeleEmbedding F).toAlgebra
  ratAdeleStandardCharacter (Algebra.trace 𝔸[ℚ] 𝔸[F] a)

/-- Paper: Example A.3.1.9, p. 558. The standard adelic character is trivial on the
diagonally embedded field, which is what Theorem 2.2.3.2 and Theorem 3.2.2.1 need. -/
theorem adeleStandardCharacter_algebraMap (x : F) :
    adeleStandardCharacter F (algebraMap F 𝔸[F] x) = 1 := by sorry

/-- Paper: Example A.3.1.9, p. 558. The standard adelic character reduces to the
rational adelic character for the rational field. -/
theorem adeleStandardCharacter_rat (a : 𝔸[ℚ]) :
    adeleStandardCharacter ℚ a = ratAdeleStandardCharacter a := by sorry

/-- Paper: Example A.3.1.9, p. 558. The global additive Tamagawa measure is self-dual
under the pairing from the trace character. -/
theorem additiveTamagawaMeasure_selfDual :
    IsTamagawaSelfDual (additiveTamagawaMeasure F) (adeleStandardCharacter F) := by sorry

/-- Paper: Example A.3.1.10, p. 558. The local character is the finite component
of the adelic trace character, evaluated on an adele supported at the given place.
Deviation: It is expressed by restriction of the adelic trace, whose component is the local trace. -/
def finiteLocalStandardCharacter (v : Primes(F)) (x : v.adicCompletion F) : Circle :=
  adeleStandardCharacter F (0, RestrictedProduct.single (fun w : Primes(F) ↦
    w.adicCompletionIntegers F) v x)

/-- Paper: Example A.3.1.10, p. 558. At a finite place the trace character
agrees with the standard p-adic character composed with the local field trace. -/
theorem finiteLocalStandardCharacter_trace (v : Primes(F)) (u : Primes(ℚ))
    (hu : u.asIdeal = v.asIdeal.comap (RingOfIntegers.mapRingHom (algebraMap ℚ F))) :
    let p := Rat.HeightOneSpectrum.primesEquiv u
    letI : Fact p.val.Prime := ⟨p.property⟩
    ∃ j : u.adicCompletion ℚ →+* v.adicCompletion F,
      Continuous j ∧ (∀ r : ℚ, j (algebraMap ℚ (u.adicCompletion ℚ) r) =
        algebraMap F (v.adicCompletion F) (algebraMap ℚ F r)) ∧
      letI := j.toAlgebra
      Module.Finite (u.adicCompletion ℚ) (v.adicCompletion F) ∧
        ∀ x : v.adicCompletion F, finiteLocalStandardCharacter F v x =
          padicStandardCharacter p.val (Rat.HeightOneSpectrum.adicCompletion.padicEquiv u
            (Algebra.trace (u.adicCompletion ℚ) (v.adicCompletion F) x)) := by sorry

/-- Paper: Example A.3.1.10, p. 558. The local measure is self-dual under
the local trace character. -/
theorem finiteLocalAdditiveTamagawaMeasure_selfDual (v : Primes(F)) :
    IsTamagawaSelfDual (finiteLocalAdditiveTamagawaMeasure F v)
      (finiteLocalStandardCharacter F v) := by sorry

/-- Paper: Example A.3.1.10, p. 558. The Fourier transform of the local integer-ring
indicator is the inverse-different indicator multiplied by the mass of the integer ring.
Deviation: The inverse different is the closed ball of normalized radius `qᵥ^dᵥ`. -/
theorem finiteLocalTamagawaFourier_integers (v : Primes(F)) :
    tamagawaFourier (finiteLocalAdditiveTamagawaMeasure F v) (finiteLocalStandardCharacter F v)
        ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ))) =
      (differentMass(F, v).toReal : ℂ) •
        ({x : v.adicCompletion F | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ differentExp(F, v)}.indicator
          (fun _ ↦ (1 : ℂ))) :=
  by sorry

/-- Paper: Example A.3.1.11, p. 559. The standard S-local character is the product
over all archimedean places and the finite places in S, as in (A.3.1.9).
Deviation: Each local character is expressed as a restriction of the global trace character. -/
def sAdeleStandardCharacter (a : SAdeleRing F S) : Circle :=
  (∏ w : InfinitePlace F, adeleStandardCharacter F (Pi.single w (a.1 w), 0)) *
    ∏ v : S, finiteLocalStandardCharacter F v.val (a.2 v)

/-- Paper: Example A.3.1.11, p. 559. On an S-adele supported at a single finite
place, the product character restricts to the trace character at that place. -/
theorem sAdeleStandardCharacter_single_finite (v : S) (x : v.val.adicCompletion F) :
    sAdeleStandardCharacter F S (0, Pi.single v x) = finiteLocalStandardCharacter F v.val x :=
  by sorry

-- TODO(paper-gap): In Example A.3.1.11, the lattice fails to annihilate itself
-- under (A.3.1.10) with the real and p-adic signs as printed. For F = ℚ and
-- S = {∞, 3}, the pairing of 1/3 with 1 is exp(4πi/3).
-- The proof also reverses the ambient group of the annihilator for (A.3.1.11).

/-- Paper: Example A.3.1.11, p. 559. The standard S-local character takes the
value one on every diagonally embedded S-integer.
Deviation: This consequence of the lattice pairing holds for every finite S with the
finite-place sign correction of ERRATA F13. -/
theorem sAdeleStandardCharacter_sInteger (x : (S : Set (Primes(F))).integer F) :
    sAdeleStandardCharacter F S (adeleProjection F S (integralAdeleDiagonal F S x).val) = 1 :=
  by sorry

/-- Paper: Example A.3.1.11, p. 559. The diagonal S-integers are their own annihilator
for the standard character pairing when S contains every finite prime dividing the different.
Deviation: The pairing uses the finite-place sign correction of ERRATA F13. -/
theorem sInteger_annihilator_iff
    (hS : ∀ v : Primes(F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S)
    (y : SAdeleRing F S) :
    (∀ x : (S : Set (Primes(F))).integer F,
        sAdeleStandardCharacter F S
          (adeleProjection F S (integralAdeleDiagonal F S x).val * y) = 1) ↔
      ∃ x : (S : Set (Primes(F))).integer F,
        y = adeleProjection F S (integralAdeleDiagonal F S x).val := by sorry

/-- Paper: Definition A.3.2.1, p. 559. The measure `dt/t` on the positive
reals is the pushforward of real Lebesgue measure along the exponential. -/
def positiveRealHaar : Measure ℝ≥0ˣ :=
  Measure.map (fun x : ℝ ↦
    Units.mk0 (Real.exp x).toNNReal
      (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))) volume

/-- Paper: §A.3.3.1, p. 561. The mass of the interval with endpoints 1 and T
under `dt/t` is the logarithm of T for T at least 1. -/
theorem positiveRealHaar_interval (T : ℝ≥0ˣ) (hT : 1 ≤ (T.val : ℝ)) :
    positiveRealHaar {t | (t.val : ℝ) ∈ Icc 1 (T.val : ℝ)} =
      ENNReal.ofReal (Real.log (T.val : ℝ)) := by
  let e (x : ℝ) := Units.mk0 (Real.exp x).toNNReal (by positivity)
  have he : Measurable e :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hset : MeasurableSet {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Icc 1 (T.val : ℝ)} :=
    measurableSet_Icc.preimage (NNReal.continuous_coe.measurable.comp MeasurableSpace.le_map_comap)
  change (volume.map e) _ = _
  rw [Measure.map_apply he hset]
  have hpre : e ⁻¹' {t | (t.val : ℝ) ∈ Icc 1 (T.val : ℝ)} = Icc 0 (Real.log (T.val : ℝ)) := by
    ext x
    change (1 ≤ ((Real.exp x).toNNReal : ℝ) ∧ ((Real.exp x).toNNReal : ℝ) ≤ _) ↔ _
    rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.one_le_exp_iff,
      ← Real.le_log_iff_exp_le (zero_lt_one.trans_le hT)]
    rfl
  rw [hpre, Real.volume_Icc, sub_zero]

local notation "classVolume(" F ")" =>
  ENNReal.ofReal ((2 : ℝ) ^ InfinitePlace.nrRealPlaces F *
    (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces F * Nat.cast (NumberField.classNumber F) *
    Units.regulator F / (Real.sqrt (Nat.cast (Int.natAbs (NumberField.discr F))) *
      Nat.cast (Units.torsionOrder F)))

/-- Paper: Definition A.3.2.1, pp. 559–560. There is a unique compatible triple
of regular Haar measures on the ideles, the idele classes and the norm-one
classes. The quotient normalizations use counting measure and `dt/t`, respectively. -/
theorem multiplicativeTamagawaMeasures_existsUnique :
    ∃! m : Measure 𝕀[F] × Measure C[F] × Measure C₁[F],
      m.1.IsHaarMeasure ∧ m.1.Regular ∧
        IsWeilQuotientMeasure P[F] m.1 Measure.count m.2.1 ∧
        m.2.2.IsHaarMeasure ∧ m.2.2.Regular ∧ m.2.2 univ = classVolume(F) ∧
        IsWeilQuotientMeasure C₁[F] m.2.1 m.2.2
          (positiveRealHaar.comap (QuotientGroup.kerLift (ideleClassNorm F))) :=
  by sorry

/-- Paper: Definition A.3.2.1, pp. 559–560. The global multiplicative Tamagawa
measure uses the prescribed mass on the norm-one idele classes. -/
def multiplicativeTamagawaMeasure : Measure 𝕀[F] :=
  (multiplicativeTamagawaMeasures_existsUnique F).exists.choose.1

/-- Paper: Definition A.3.2.1, pp. 559–560. The class measure is the quotient
of the idelic Tamagawa measure by counting measure on the principal ideles. -/
def ideleClassTamagawaMeasure : Measure C[F] :=
  (multiplicativeTamagawaMeasures_existsUnique F).exists.choose.2.1

/-- Paper: Definition A.3.2.1, pp. 559–560. Disintegrating the class measure
against `dt/t` gives the Tamagawa measure on the norm-one classes. -/
def normOneIdeleClassTamagawaMeasure : Measure C₁[F] :=
  (multiplicativeTamagawaMeasures_existsUnique F).exists.choose.2.2

/-- Paper: Definition A.3.2.1, pp. 559–560. The global idelic and class measures
satisfy Weil's formula with counting measure on the principal ideles. -/
theorem ideleClassTamagawaMeasure_isWeil :
    IsWeilQuotientMeasure P[F] (multiplicativeTamagawaMeasure F)
      Measure.count (ideleClassTamagawaMeasure F) := by sorry

/-- Paper: Definition A.3.2.1, p. 560. The norm-one idele classes have the
mass in (A.3.2.1), expressed with Mathlib's regulator and class number. -/
theorem normOneIdeleClassTamagawaMeasure_volume :
    normOneIdeleClassTamagawaMeasure F univ = classVolume(F) := by sorry

/-- Paper: Definition A.3.2.1, pp. 559–560. The class and norm-one class measures
satisfy Weil's formula with `dt/t` on the norm quotient. -/
theorem normOneIdeleClassTamagawaMeasure_isWeil :
    IsWeilQuotientMeasure C₁[F] (ideleClassTamagawaMeasure F)
      (normOneIdeleClassTamagawaMeasure F)
      (positiveRealHaar.comap (QuotientGroup.kerLift (ideleClassNorm F))) := by sorry

/-- Paper: Definition A.3.2.2(1), p. 560. The multiplicative measure at an infinite
place is the additive measure weighted by the reciprocal normalized absolute value. -/
def infiniteLocalMultiplicativeTamagawaMeasure (v : InfinitePlace F) : Measure v.Completionˣ :=
  ((infiniteLocalAdditiveTamagawaMeasure F v).withDensity
    (fun x ↦ (↑(‖x‖₊ ^ v.mult) : ℝ≥0∞)⁻¹)).comap Units.val

/-- Paper: Definition A.3.2.2(1), p. 560. On units at a real place with coordinate
between 1 and 2 the measure is the integral of `dt/t`, namely `log 2`. -/
theorem infiniteLocalMultiplicativeTamagawaMeasure_real_interval (v : InfinitePlace F)
    (h : v.IsReal) :
    infiniteLocalMultiplicativeTamagawaMeasure F v
      {x | ringEquivRealOfIsReal h x.val ∈ Icc 1 2} = ENNReal.ofReal (Real.log 2) := by sorry

/-- Paper: Definition A.3.2.2(2), p. 560. Scale local multiplicative Haar
measure so that the integer units have the inverse square root different-norm mass. -/
def finiteLocalMultiplicativeTamagawaMeasure (v : Primes(F)) : Measure (v.adicCompletion F)ˣ :=
  let μ := Measure.haar (G := (v.adicCompletion F)ˣ)
  (differentMass(F, v) / μ (v.adicCompletionIntegers F).units) • μ

/-- Paper: Definition A.3.2.2(2), p. 560. The local multiplicative measure assigns
the mass in (A.3.2.2) to the integer units. -/
theorem finiteLocalMultiplicativeTamagawaMeasure_integerUnits (v : Primes(F)) :
    finiteLocalMultiplicativeTamagawaMeasure F v (v.adicCompletionIntegers F).units =
      differentMass(F, v) := by sorry

/-- Paper: Lemma A.3.2.3, p. 560. At a finite place the multiplicative
measure is the weighted additive measure times `qᵥ / (qᵥ - 1)`. -/
theorem finiteLocalMultiplicativeTamagawaMeasure_eq_withDensity (v : Primes(F)) :
    finiteLocalMultiplicativeTamagawaMeasure F v =
      (↑v.asIdeal.absNorm / (↑v.asIdeal.absNorm - 1) : ℝ≥0∞) •
        ((finiteLocalAdditiveTamagawaMeasure F v).withDensity
          (fun x ↦ (↑‖x‖₊ : ℝ≥0∞)⁻¹)).comap Units.val := by sorry

local notation "∞unitAt" => fun w : InfinitePlace F ↦
  Units.map (RingHom.toMonoidHom (RingHom.comp (Pi.evalRingHom InfinitePlace.Completion w)
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))))
local notation "finiteUnitAt" => fun v : Primes(F) ↦
  Units.map (RingHom.toMonoidHom (RingHom.comp
    (RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ HeightOneSpectrum.adicCompletion F w) v)
    (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))))

/-- Paper: Lemma A.3.2.4, p. 560. The global multiplicative measure is the
restricted product of the local measures, evaluated on rectangles with integer-unit tails. -/
theorem multiplicativeTamagawaMeasure_restrictedProduct
    (B : (w : InfinitePlace F) → Set w.Completionˣ) (hB : ∀ w, MeasurableSet (B w))
    (U : (v : S) → Set (v.val.adicCompletion F)ˣ) (hU : ∀ v, MeasurableSet (U v)) :
    multiplicativeTamagawaMeasure F
        {g | (∀ w, (∞unitAt) w g ∈ B w) ∧ (∀ v : S, (finiteUnitAt) v.val g ∈ U v) ∧
          ∀ v : Primes(F), v ∉ S → (finiteUnitAt) v g ∈ (v.adicCompletionIntegers F).units} =
      (∏ w : InfinitePlace F, infiniteLocalMultiplicativeTamagawaMeasure F w (B w)) *
        (∏ v : S, finiteLocalMultiplicativeTamagawaMeasure F v.val (U v)) *
          ∏ᶠ v : {v : Primes(F) // v ∉ S}, differentMass(F, v.val) := by sorry

/-- Paper: §A.3.3.1, p. 561. Weil's formula for the idelic norm and `dt/t`
determines a unique regular Haar measure on the norm-one ideles. -/
theorem normOneIdeleTamagawaMeasure_existsUnique :
    ∃! ν : Measure N[F], ν.IsHaarMeasure ∧ ν.Regular ∧
      IsWeilQuotientMeasure N[F] (multiplicativeTamagawaMeasure F) ν
        (positiveRealHaar.comap (QuotientGroup.kerLift (ideleNorm F))) := by sorry

/-- Paper: §A.3.3.1, p. 561. Normalize the Haar measure on the norm-one
ideles by the global multiplicative Tamagawa measure and `dt/t`. -/
def normOneIdeleTamagawaMeasure : Measure N[F] :=
  (normOneIdeleTamagawaMeasure_existsUnique F).exists.choose

/-- Paper: §A.3.3.1, p. 561. Under any continuous homomorphic section, the
idelic decomposition transports the product of `dt/t` and the norm-one idele measure. -/
theorem multiplicativeTamagawaMeasure_normProduct (s : ℝ≥0ˣ →* 𝕀[F]) (hs : Continuous s)
    (hn : RightInverse s (ideleNorm F)) :
    (positiveRealHaar.prod (normOneIdeleTamagawaMeasure F)).map
        (fun tg : ℝ≥0ˣ × N[F] ↦ s tg.1 * tg.2.val) =
      multiplicativeTamagawaMeasure F := by sorry

/-- Paper: §A.3.3.1, p. 561. A section strip over the idelic fundamental domain
has volume `log T` times the volume of the norm-one idele classes.
Deviation: The formula uses `T ≥ 1` so that the logarithm equals the interval mass. -/
theorem multiplicativeTamagawaMeasure_sectionStrip
    (s : ℝ≥0ˣ →* 𝕀[F]) (hs : Continuous s) (hn : RightInverse s (ideleNorm F))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (r : CommRing.Pic (𝓞 F) → N[F]) (hr₁ : r 1 = 1)
    (hr : ∀ c, ideleIdealClass F (r c).val = c) (T : ℝ≥0ˣ) (hT : 1 ≤ (T.val : ℝ)) :
    multiplicativeTamagawaMeasure F
      {g | ∃ t : ℝ≥0ˣ, (t.val : ℝ) ∈ Icc 1 (T.val : ℝ) ∧
        ∃ x ∈ ideleFundamentalDomain F b v₀ σ r, g = s t * (x : N[F]).val} =
      ENNReal.ofReal (Real.log (T.val : ℝ)) * normOneIdeleClassTamagawaMeasure F univ := by sorry

/-- Paper: Definition A.3.4.1(1), p. 561. The S-local additive Tamagawa
measure is the product of all archimedean and the selected finite local measures. -/
def sAdditiveTamagawaMeasure : Measure (SAdeleRing F S) :=
  (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).prod
    (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val))

/-- Paper: Definition A.3.4.1(2), p. 561. The S-local multiplicative Tamagawa
measure is the finite product of the local measures on the unit groups. -/
def sMultiplicativeTamagawaMeasure : Measure 𝕀ₛ :=
  let e := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
    ((v : S) → v.val.adicCompletion F)
  let eArch := ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F ↦ w.Completion)
  let eS := ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)
  ((Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).prod
      (Measure.pi (fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val))).map
    (fun x ↦ e.symm (eArch.symm x.1, eS.symm x.2))

/-- Paper: Definition A.3.4.1(2), p. 561. The mass of an S-local unit rectangle
is the product of the archimedean coordinate masses and the finite integer-unit masses. -/
theorem sMultiplicativeTamagawaMeasure_integerUnits
    (B : (w : InfinitePlace F) → Set w.Completionˣ) (hB : ∀ w, MeasurableSet (B w)) :
    sMultiplicativeTamagawaMeasure F S
        {g | (∀ w, Units.map ((Pi.evalRingHom InfinitePlace.Completion w).comp
          (RingHom.fst _ _)).toMonoidHom g ∈ B w) ∧
            ∀ v : S, Units.map ((Pi.evalRingHom (fun u : S ↦ u.val.adicCompletion F) v).comp
              (RingHom.snd _ _)).toMonoidHom g ∈ (v.val.adicCompletionIntegers F).units} =
      (∏ w : InfinitePlace F, infiniteLocalMultiplicativeTamagawaMeasure F w (B w)) *
        ∏ v : S, differentMass(F, v.val) := by sorry

/-- Paper: Definition A.3.4.1(3)(1), p. 561. The Haar measure on the norm-one
S-ideles is uniquely determined by Weil's formula using the product and `dt/t`. -/
theorem sNormOneIdeleTamagawaMeasure_existsUnique :
    ∃! ν : Measure Nₛ, ν.IsHaarMeasure ∧ ν.Regular ∧
      IsWeilQuotientMeasure Nₛ (sMultiplicativeTamagawaMeasure F S) ν
        (positiveRealHaar.comap (QuotientGroup.kerLift (sIdeleNorm F S))) := by sorry

/-- Paper: Definition A.3.4.1(3)(1), p. 561. Use the Weil normalization of
the product measure on the norm-one S-ideles. -/
def sNormOneIdeleTamagawaMeasure : Measure Nₛ :=
  (sNormOneIdeleTamagawaMeasure_existsUnique F S).exists.choose

/-- Paper: Definition A.3.4.1(3)(1), p. 561. The chosen norm-one measure
satisfies Weil's formula with `dt/t` on the norm quotient. -/
theorem sNormOneIdeleTamagawaMeasure_isWeil :
    IsWeilQuotientMeasure Nₛ (sMultiplicativeTamagawaMeasure F S)
      (sNormOneIdeleTamagawaMeasure F S)
      (positiveRealHaar.comap (QuotientGroup.kerLift (sIdeleNorm F S))) := by sorry

-- TODO(paper-gap): Definition A.3.4.1(3)(2)–(3) prescribes a measure on the
-- local S-ideles but takes the quotient of the larger group in (A.1.5.7).
-- The latter includes the product of the integer-unit groups outside S.

/-- Paper: Example A.3.1.11, p. 559, and Remark A.3.4.2, p. 562. The S-local
product is self-dual under the pairing from the product character. -/
theorem sAdditiveTamagawaMeasure_selfDual :
    IsTamagawaSelfDual (sAdditiveTamagawaMeasure F S) (sAdeleStandardCharacter F S) := by sorry

-- TODO(paper-gap): The last sentence of Remark A.3.4.2 reverses the criterion
-- for mass one. The preceding prime-to-S volume is one precisely when S contains
-- all the ramified finite places.

/-- Paper: Remark A.3.4.2, p. 562. The additive quotient mass of the product
measure is the square root of the part of the different norm outside S.
Deviation: The prime-to-S part is taken over places of the number field. -/
theorem sAdditiveTamagawaMeasure_quotientVolume :
    ∃ ν : Measure (Multiplicative (SAdeleRing F S) ⧸ Aₛ),
      IsWeilQuotientMeasure Aₛ (show Measure (Multiplicative (SAdeleRing F S)) from
        sAdditiveTamagawaMeasure F S) Measure.count ν ∧
      ν univ = ∏ᶠ v : {v : Primes(F) // v ∉ S}, (differentMass(F, v.val))⁻¹ := by sorry

/-- Paper: Example A.3.1.11, p. 558. If every prime dividing the different
is in S, the S-local additive product has the quotient-volume-one normalization. -/
theorem sAdditiveTamagawaMeasure_eq_covolumeOne
    (hS : ∀ v : Primes(F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) → v ∈ S) :
    sAdditiveTamagawaMeasure F S = sAdditiveCovolumeOneMeasure F S := by sorry

/-- Paper: Remark A.3.4.2, p. 562. The local integer-ring indicator is fixed
by the Fourier transform exactly at places unramified over their residue prime.
Deviation: Unramifiedness is expressed by nondivisibility of the global different. -/
theorem finiteLocalTamagawaFourier_fixes_integers_iff (v : Primes(F)) :
    tamagawaFourier (finiteLocalAdditiveTamagawaMeasure F v) (finiteLocalStandardCharacter F v)
        ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ))) =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ)) ↔
      ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := by sorry

end RiemannMasullo
