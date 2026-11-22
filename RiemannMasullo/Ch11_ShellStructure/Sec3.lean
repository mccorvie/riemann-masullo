module

public import Mathlib.NumberTheory.PrimeCounting
public import RiemannMasullo.Ch11_ShellStructure.Sec2b

import all RiemannMasullo.Ch10_TraceSpectral.Sec1
import all RiemannMasullo.Ch11_ShellStructure.Sec1a

/-!
# Orbital kernels and orbital traces

Masullo, §11.3, pp. 491–496. The divisorial filtration is on ideles.
All archimedean places are implicit in the finite-place base set.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleMeasurableSpaceSec1a

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "N𝔽" => (ideleNorm F).ker
local notation "C₁" => (ideleClassNorm F).ker
local notation "principal" => IdeleGroup.unitEmbedding (𝓞 F) F
local notation "ℬₛ(" S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "above(" p ")" => (finite_nuclearityPlacesAbove (F := F) p).toFinset
local notation "resChar(" v ")" => Rat.HeightOneSpectrum.natGenerator ((v).under (𝓞 ℚ))

/-- Paper: (11.3.1.1), p. 492. For a base with trivial S-integer Picard group and
an unramified outside character, each homogeneous polar theta function has a
representative obtained by adjoining the integer indicators to an S-local test.
Deviation: The printed condition that S contains the places ramified over ℚ is
not used by Theorem 6.2.1.1(2) and is omitted. As on the page, the S-local test
is not asserted to have zero polar values. -/
theorem exists_divisorialThetaRepresentative (S : Finset V)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F))) (ω : PontryaginDual C₁)
    (_hω : NormOneCharacterUnramifiedOutside ω S) (f : adelePolarSubspace F) :
    ∃ fS : ℬₛ(S), homogeneousAdelicTheta ω (sAdeleSchwartzToGlobal F S fS) =
      homogeneousAdelicTheta ω f.val := by sorry

/-- Paper: §11.3.1.1, p. 492, before (11.3.1.2). The local factor is the
indicator of ideles whose component at the chosen finite place is a unit.
Deviation: The unrestricted tensor coordinates contribute the constant one. -/
def divisorialLocalIndicator (v : V) (g : I𝔽) : ℂ :=
  if Valued.v (g.val.2 v) = 1 then 1 else 0

/-- Paper: §11.3.1.1, p. 492. The local indicator detects precisely the
integer units in the chosen coordinate. -/
theorem divisorialLocalIndicator_eq_one_iff (v : V) (g : I𝔽) :
    divisorialLocalIndicator v g = 1 ↔ Valued.v (g.val.2 v) = 1 := by sorry

/-- Paper: (11.3.1.2), p. 492. Multiply the local unit indicators at the
selected finite places. The base set enters through the choice of these places. -/
def divisorialIndicator (T : Finset V) (g : I𝔽) : ℂ :=
  ∏ v ∈ T, divisorialLocalIndicator v g

/-- Paper: (11.3.1.2), p. 492. For a singleton the product recovers the local
indicator. -/
theorem divisorialIndicator_singleton (v : V) (g : I𝔽) :
    divisorialIndicator {v} g = divisorialLocalIndicator v g := by sorry

variable (F) in
/-- Paper: §11.3.1.1, p. 492, after (11.3.1.2). The divisorial stratum imposes
the local unit condition at each selected finite place.
Deviation: The ambient set on the right is the full idele group. -/
def divisorialStratum (T : Finset V) : Set I𝔽 :=
  {g | ∀ v ∈ T, Valued.v (g.val.2 v) = 1}

/-- Paper: §11.3.1.1, pp. 492–493. The finite product of local indicators
is the indicator of the stratum. -/
theorem divisorialIndicator_eq_indicator (T : Finset V) :
    divisorialIndicator T = (divisorialStratum F T).indicator (fun _ ↦ 1) := by sorry

/-- Paper: §11.3.1.1, p. 492. Every divisorial stratum is open and closed. -/
theorem isClopen_divisorialStratum (T : Finset V) :
    IsClopen (divisorialStratum F T) := by sorry

/-- Paper: §11.3.1.1, pp. 492–493. The difference of two nested strata consists
of ideles satisfying the old conditions and failing a condition at some new place.
The failure of a unit condition is the union of the nonzero valuation classes. -/
theorem divisorialStratum_sdiff (T U : Finset V) (hTU : T ⊆ U) :
    divisorialStratum F T \ divisorialStratum F U =
      ⋃ v ∈ U \ T, {g ∈ divisorialStratum F T | Valued.v (g.val.2 v) ≠ 1} := by sorry

/-- Paper: §11.3.1.1, pp. 492–493. The sequence of rational primes omitting the
residue characteristics represented in the finite base consists of primes. -/
theorem primaryDivisorialPrime_isPrime (S : Finset V) (k : ℕ) :
    (Nat.nth (fun p ↦ p.Prime ∧ p ∉ S.image (fun v ↦ resChar(v))) k).Prime := by sorry

/-- Paper: §11.3.1.1, p. 493. The rational prime for the next primary step is
selected in increasing order.
Deviation: Skip the residue characteristics in the base S as required by (11.3.1.2). -/
def primaryDivisorialPrime (S : Finset V) (k : ℕ) : Vℚ :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨_, primaryDivisorialPrime_isPrime S k⟩

/-- Paper: §11.3.1.1, p. 493. With no excluded primes the first step uses the
prime 2. -/
theorem primaryDivisorialPrime_empty_zero :
    primaryDivisorialPrime (∅ : Finset V) 0 =
      Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩ := by sorry

variable (F) in
/-- Paper: §11.3.1.1, p. 493. The kth primary place set takes the full fibres
over the first k rational primes of the sequence outside the base. -/
def primaryDivisorialPlaces (S : Finset V) (k : ℕ) : Finset V :=
  (Finset.range k).biUnion (fun j ↦ above(primaryDivisorialPrime S j))

/-- Paper: §11.3.1.1, p. 493. The next step adds precisely the places over the
next rational prime. -/
theorem primaryDivisorialPlaces_succ (S : Finset V) (k : ℕ) :
    primaryDivisorialPlaces F S (k + 1) =
      primaryDivisorialPlaces F S k ∪ above(primaryDivisorialPrime S k) := by sorry

/-- Paper: §11.3.1.1, p. 493. Together the indices exhaust the finite places
outside a saturated base. -/
theorem iUnion_primaryDivisorialPlaces (S : Finset V)
    (_hS : ∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) :
    (⋃ k, (primaryDivisorialPlaces F S k : Set V)) = (S : Set V)ᶜ := by sorry

/-- Paper: §11.3.1.1, p. 493. An idele with unit components at every place over
the chosen rational primes has unit norm components at those primes.
Deviation: The printed reverse inclusion fails when local valuations cancel above
a split prime. -/
theorem relativeIdeleNormRat_mem_divisorialStratum
    (T : Finset Vℚ) :
    divisorialStratum F (T.biUnion (fun p ↦ above(p))) ⊆
      (relativeIdeleNormRat F) ⁻¹' divisorialStratum ℚ T := by sorry

/-- Paper: §11.3.1.1, p. 493. The product of the unit indicators on a finite set
outside S converts the integer-extended test to its principal value at those places.
Deviation: Read the remaining integer factors as indexed outside S and the
selected places. The equality is recorded on the ideles. -/
theorem divisorialIndicator_mul_thetaRepresentative (S T : Finset V) (_hST : Disjoint S T)
    (f : ℬₛ(S)) (g : I𝔽) :
    divisorialIndicator T g * sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd g.val) =
      adelePrincipalValue F T (sAdeleSchwartzToGlobal F S f) (Multiplicative.ofAdd g.val) := by sorry

/-- Paper: §11.3.1.1, p. 493. Removing the next prime's integer factors
multiplies the zeta transform of the depleted test by the reciprocal Euler
product over that prime.
Deviation: State the identity on the half-plane of absolute convergence. -/
theorem primaryDivisorialZeta_succ (S : Finset V) (k : ℕ) (χ : PontryaginDual C𝔽)
    (_hχ : ∀ v ∉ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (f : ℬₛ(S)) (z : ℂ) (_hz : 1 < z.re) :
    let c := ideleClassNormTwist χ z
    let Z := fun j ↦ globalIdelicZFunction
      (adelePrincipalValue F (primaryDivisorialPlaces F S j) (sAdeleSchwartzToGlobal F S f)) c
    Z (k + 1) = reciprocalPartialHeckeEulerProduct χ above(primaryDivisorialPrime S k) z * Z k :=
  by sorry

/-- Paper: §11.3.1.1, p. 493. For a test whose global extension has both polar
values zero the depletion identity holds at every exponent, in particular at the
zeros of the reciprocal Euler product, which lie on the line of real part zero.
Deviation: The polar condition makes both zeta functions entire, so the
normal-form values at poles do not enter. -/
theorem primaryDivisorialZeta_succ_of_polar (S : Finset V) (k : ℕ) (χ : PontryaginDual C𝔽)
    (_hχ : ∀ v ∉ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (f : ℬₛ(S)) (_hf : sAdeleSchwartzToGlobal F S f ∈ adelePolarSubspace F) (z : ℂ) :
    let c := ideleClassNormTwist χ z
    let Z := fun j ↦ globalIdelicZFunction
      (adelePrincipalValue F (primaryDivisorialPlaces F S j) (sAdeleSchwartzToGlobal F S f)) c
    Z (k + 1) = reciprocalPartialHeckeEulerProduct χ above(primaryDivisorialPrime S k) z * Z k :=
  by sorry

-- TODO(paper-gap): The local "Weil's Identity" on p. 492 has an extra factor
-- μᵥ(𝒪ᵥˣ) on the left. With the Tamagawa measure of (A.3.2.2) both
-- Zᵥ(1_{𝒪ᵥˣ}, c) and Lᵥ(c)⁻¹ Zᵥ(1_{𝒪ᵥ}, c) equal μᵥ(𝒪ᵥˣ) for unramified c, so
-- the print holds only where this mass is one. At the place over 2 of ℚ(i) the
-- mass is 1/2 and the two printed sides are 1/4 and 1/2. The same page gives the
-- product of all unit masses as the square root of the absolute different. It
-- is the reciprocal square root of the absolute discriminant.

section ThetaSubquotient

local notation "P" => adelePolarSubspace F
local notation "Θ(" ω ")" =>
  (↥P ⧸ LinearMap.ker ((homogeneousAdelicThetaLinearMap F ω).domRestrict P))

/-- Paper: (11.3.1.3), p. 494. The theta denominator at a given stage is the
image of polar-free tests after the selected principal values in the polar
homogeneous theta space. -/
def divisorialThetaStage (ω : PontryaginDual C₁) (T : Finset V) : Submodule ℂ Θ(ω) :=
  Submodule.span ℂ (Set.range fun f : P ↦ (Submodule.Quotient.mk
    ⟨adelePrincipalValue F T f.val, adelePrincipalValue_mem_polarSubspace T f⟩ : Θ(ω)))

/-- Paper: (11.3.1.3), p. 494. With no principal values the stage is the entire
polar homogeneous theta space. -/
theorem divisorialThetaStage_empty (ω : PontryaginDual C₁) :
    divisorialThetaStage ω ∅ = ⊤ := by sorry

/-- Paper: (11.3.1.3), p. 494. Adding places decreases the principal-value image
of the polar theta space. -/
theorem divisorialThetaStage_antitone (ω : PontryaginDual C₁) :
    Antitone (divisorialThetaStage ω) := by sorry

/-- Paper: (11.3.1.3), p. 494, and (7.4.0.2), p. 366. At the fibre over one
rational prime the stage is the finite-place denominator of §7.4, so the first
subquotient of the chain is the finite orbital quotient used there. -/
theorem divisorialThetaStage_above (χ : PontryaginDual C𝔽) (p : Vℚ) :
    divisorialThetaStage (χ.comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
      C₁ →ₜ* C𝔽)) above(p) = finiteNuclearityDenominator χ p := by
  unfold divisorialThetaStage finiteNuclearityDenominator
  with_reducible rfl

/-- Paper: (11.3.1.3), p. 494. Divide the kth principal-value theta image
by the next image, viewed inside the kth stage. -/
abbrev PrimaryDivisorialThetaSubquotient (S : Finset V) (ω : PontryaginDual C₁) (k : ℕ) :=
  ↥(divisorialThetaStage ω (primaryDivisorialPlaces F S k)) ⧸
    (divisorialThetaStage ω (primaryDivisorialPlaces F S (k + 1))).comap
      (divisorialThetaStage ω (primaryDivisorialPlaces F S k)).subtype

/-- Paper: (11.3.1.3), p. 494. A representative in the kth stage has zero
class precisely when it belongs to the next stage. -/
theorem primaryDivisorialThetaSubquotient_mk_eq_zero (S : Finset V) (ω : PontryaginDual C₁)
    (k : ℕ) (x : divisorialThetaStage ω (primaryDivisorialPlaces F S k)) :
    (Submodule.Quotient.mk x : PrimaryDivisorialThetaSubquotient S ω k) = 0 ↔
      x.val ∈ divisorialThetaStage ω (primaryDivisorialPlaces F S (k + 1)) := by sorry

-- TODO(paper-gap): The claimed Schauder systems need a specified Paley–Wiener
-- subquotient at each global stage and compatible lifts in the strip Sobolev space.
-- The local subquotients of §7.3 and the zero-line quotient of §11.2.2 do not
-- identify these global stage quotients with the basis model used here.

end ThetaSubquotient

/-- Paper: (11.3.1.4), p. 494. Multiply an idelic kernel by the next indicator
minus the current indicator.
Deviation: The difference acts on the input coordinate, as in the shell
calculation on pp. 495–496. -/
def divisorialKernelDifference (S : Finset V) (k : ℕ) (K : I𝔽 × I𝔽 → ℂ)
    (xy : I𝔽 × I𝔽) : ℂ :=
  (divisorialIndicator (primaryDivisorialPlaces F S (k + 1)) xy.2 -
    divisorialIndicator (primaryDivisorialPlaces F S k) xy.2) * K xy

/-- Paper: (11.3.1.4), p. 494. On the removed part of the kth stratum the
successive difference is the negative of the original kernel. -/
theorem divisorialKernelDifference_eq_neg (S : Finset V) (k : ℕ) (K : I𝔽 × I𝔽 → ℂ)
    (xy : I𝔽 × I𝔽)
    (_hxy : xy.2 ∈ divisorialStratum F (primaryDivisorialPlaces F S k) \
      divisorialStratum F (primaryDivisorialPlaces F S (k + 1))) :
    divisorialKernelDifference S k K xy = -K xy := by sorry

variable (F) in
/-- Paper: §11.3.1.1, p. 491, and §11.3.2, p. 495. The S-local idelic
region in the definition of β consists of ideles that are units outside S. -/
def sLocalDivisorialStratum (S : Finset V) : Set I𝔽 :=
  {g | ∀ v ∉ S, Valued.v (g.val.2 v) = 1}

/-- Paper: §11.3.2, p. 495. The region of β is the product of the inserted
S-ideles and the outside integer unit group. -/
theorem mem_sLocalDivisorialStratum_iff (S : Finset V) (g : I𝔽) :
    g ∈ sLocalDivisorialStratum F S ↔
      ∃ (a : (SAdeleRing F S)ˣ) (u : outsideIntegralIdeleUnits F S),
        g = sIdeleInsertion F S a * u.val := by sorry

/-- Paper: §11.3.2, p. 495, and (D.1.10.1), p. 783. The region of β is the range
of the insertion of the ideles integral outside S. -/
theorem sLocalDivisorialStratum_eq_range_integralIdeleInsertion (S : Finset V) :
    sLocalDivisorialStratum F S = Set.range (integralIdeleInsertion F S) := by sorry

/-- Paper: §11.3.1.1, pp. 492–493. At a saturated base, the limit of the
descending primary strata is the S-local idelic region. -/
theorem iInter_primaryDivisorialStratum (S : Finset V)
    (_hS : ∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S) :
    (⋂ k, divisorialStratum F (primaryDivisorialPlaces F S k)) =
      sLocalDivisorialStratum F S := by sorry

/-- Paper: §11.3.1.1, p. 491 and (11.3.1.4), p. 494. The differences telescope
pointwise to the S-local restriction minus the original kernel. For each pair
of ideles at most one difference contributes.
Deviation: The sign here follows (11.3.1.4). The opening display on p. 491
adds the differences where it would need to subtract them. -/
theorem hasSum_divisorialKernelDifference (S : Finset V)
    (_hS : ∀ v ∈ S, ∀ w : V, w.under (𝓞 ℚ) = v.under (𝓞 ℚ) → w ∈ S)
    (K : I𝔽 × I𝔽 → ℂ) (xy : I𝔽 × I𝔽) :
    HasSum (fun k ↦ divisorialKernelDifference S k K xy)
      ((sLocalDivisorialStratum F S).indicator (fun _ ↦ K xy) xy.2 - K xy) := by sorry

section OrbitalTraces

local notation "𝒟" => BruhatCompactSupport C𝔽
local notation "πclass(" v ", " π ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π
local notation "q(" v ")" => (v).asIdeal.absNorm

/-- Paper: §11.3.1.1(2), pp. 494–495, and (11.3.2.5), p. 496.
The local summand of the Poisson evaluation integrates the test against the
character on each norm-one coset through a power of the local uniformizer.
Deviation: For the half-shifted Mellin sum the terms carry the norm weight
`qᵥ^(n/2)`. The Haar factor comes from the norm-one idele class measure. -/
def orbitalPlacePoissonTerm (χ : PontryaginDual C𝔽) (φ : 𝒟) (v : V)
    (π : (v.adicCompletion F)ˣ) (n : ℤ) : ℂ :=
  (Real.log (q(v) : ℝ) : ℂ) * (q(v) : ℂ) ^ ((n : ℂ) / 2) *
    ∫ h : C₁, φ.val (πclass(v, π) ^ n * h.val) * (χ h.val : ℂ)
      ∂normOneIdeleClassTamagawaMeasure F

/-- Paper: §11.3.1.1(2), p. 494. At exponent zero and for the trivial
character, the Poisson term is the log residue size times the norm-one integral. -/
theorem orbitalPlacePoissonTerm_trivial_zero (φ : 𝒟) (v : V) (π : (v.adicCompletion F)ˣ) :
    orbitalPlacePoissonTerm 1 φ v π 0 =
      (Real.log (q(v) : ℝ) : ℂ) * ∫ h : C₁, φ.val h.val
        ∂normOneIdeleClassTamagawaMeasure F := by sorry

/-- Paper: §11.3.1.1(2), p. 494, and (11.3.2.5), p. 496.
The half-shifted Mellin values at the zeros of the reciprocal Euler product sum,
with multiplicity, to the Poisson contributions of the places over the prime.
Deviation: This is the Poisson evaluation of the spectral expression. A layer
uses all its places, with the angular integral and the half-shift weight. -/
theorem orbitalEulerSum_eq_poisson (χ : PontryaginDual C𝔽) (φ : 𝒟) (p : Vℚ)
    (_hχ : ∀ v ∈ above(p), (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    (π : ∀ v : V, (v.adicCompletion F)ˣ)
    (_hπ : ∀ v ∈ above(p), Valued.v.IsUniformizer (π v : v.adicCompletion F)) :
    let zeros := {z : ℂ // reciprocalPartialHeckeEulerProduct χ above(p) z = 0}
    HasSum (fun z : zeros ↦ (orbitalEulerMultiplicity χ above(p) z.val : ℂ) *
      nuclearityTestMellin χ φ (z.val - 1 / 2))
      (∑ v ∈ above(p), ∑' n : ℤ, orbitalPlacePoissonTerm χ φ v (π v) n) := by sorry

/-- Paper: §11.3.1.1(2), pp. 494–495. If the test is supported at norms
strictly between one and the residue size, every summand at that place vanishes. -/
theorem orbitalPlacePoissonTerm_eq_zero (χ : PontryaginDual C𝔽) (φ : 𝒟) (v : V)
    (π : (v.adicCompletion F)ˣ) (_hπ : Valued.v.IsUniformizer (π : v.adicCompletion F))
    (_hφ : tsupport φ.val ⊆ {g : C𝔽 | ((ideleClassNorm F g).val : ℝ) ∈ Ioo 1 (q(v) : ℝ)})
    (n : ℤ) :
    orbitalPlacePoissonTerm χ φ v π n = 0 := by sorry

/-- Paper: §11.3.1.1(2), pp. 494–495. For a fixed compactly supported test
above norm one, only finitely many finite places contribute to the Poisson sum.
Deviation: The vanishing applies to the Poisson terms in (11.3.2.5).
Their identification with masses of geometric kernels requires a separate argument. -/
theorem finite_support_orbitalPlacePoisson (χ : PontryaginDual C𝔽) (φ : 𝒟)
    (_hφ : tsupport φ.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)})
    (π : ∀ v : V, (v.adicCompletion F)ˣ)
    (_hπ : ∀ v, Valued.v.IsUniformizer (π v : v.adicCompletion F)) :
    {v : V | ∃ n : ℤ, orbitalPlacePoissonTerm χ φ v (π v) n ≠ 0}.Finite := by sorry

/-- Paper: (11.3.2.2), p. 495. The printed weight averages products of the
two translated section indicators over the norm-one fundamental domain and
then sums over nonzero principal ideles.
Deviation: The domain is explicit and the right-hand side is a scalar weight. -/
def orbitalSectionWeight (E : Set N𝔽) (τ : ℝ≥0ˣ →* I𝔽) (xy : I𝔽 × I𝔽) : ℝ :=
  ∑' ξ : Fˣ, ∫ g in E,
    (Set.range τ).indicator (fun _ ↦ (1 : ℝ)) (principal ξ * g.val * xy.1) *
      (Set.range τ).indicator (fun _ ↦ (1 : ℝ)) (principal ξ * g.val * xy.2)
      ∂normOneIdeleTamagawaMeasure F

/-- Paper: (11.3.2.2), p. 495. The displayed weight vanishes everywhere.
For each principal multiplier, the first translated section condition forces
the integration variable into a single Haar-null point.
Deviation: The printed weight cannot implement a normalized indentation. -/
theorem orbitalSectionWeight_eq_zero (E : Set N𝔽) (τ : ℝ≥0ˣ →* I𝔽)
    (_hτ : RightInverse τ (ideleNorm F)) (xy : I𝔽 × I𝔽) :
    orbitalSectionWeight E τ xy = 0 := by sorry

/-- Paper: (11.3.2.1) and (11.3.2.3)–(11.3.2.4), pp. 495–496.
The printed weight gives a zero skew-diagonal integral for any kernel,
including when the cutoff and further indicators are absorbed into it. -/
theorem orbitalSectionWeight_skewIntegral_eq_zero (E : Set N𝔽) (τ : ℝ≥0ˣ →* I𝔽)
    (_hτ : RightInverse τ (ideleNorm F)) (K : I𝔽 × I𝔽 → ℂ) :
    (∑' ξ : Fˣ, ∫ t, ∫ g in E,
      let xy := (τ t, principal ξ * g.val * τ t)
      (orbitalSectionWeight E τ xy : ℂ) * K xy
      ∂normOneIdeleTamagawaMeasure F ∂positiveRealHaar) = 0 := by sorry

-- TODO(paper-gap): Theorem 11.3.2.1 (11.3.2.1) cannot use the weight (11.3.2.2).
-- A normalized lift and a shell-by-shell identification with the trace operator
-- are missing. The total skew-diagonal formula of §12.2 does not give these.
-- TODO(paper-gap): The proof of (11.3.2.3)–(11.3.2.5) gives no support bound for
-- a repaired lift, and the original primary indicators cut out the new place
-- once that place enters the index. A separate tail based at S′ and proof of the
-- cutoff limit on the global Paley–Wiener subquotients are needed.

end OrbitalTraces

end RiemannMasullo
