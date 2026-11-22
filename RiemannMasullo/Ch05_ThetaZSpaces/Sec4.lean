module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3b
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Second Structure Theorem and the S-local Čech sequence

Masullo, §5.4, pp. 265–277. The set S in Lean lists the finite places.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set TopologicalSpace Topology
open scoped MeasureTheory NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "ℬₛ" => SchwartzBruhat (Multiplicative Aₛ)
local notation "Jₛ" => SIdeleQuotient F S
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "J₁" => (mₛ).ker
local notation "hmₛ" => (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "normℝ(" t ")" => (((t : ℝ≥0ˣ).val : ℝ))
local notation "normChart(" χ ")" => quasiCharacterNormTwist (G := Jₛ) mₛ hmₛ
  ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (χ))
local notation "restrict₁(" χ ")" => ((χ : PontryaginDual Jₛ).comp
  (⟨(mₛ).ker.subtype, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ))
local notation "Θω(" ω ")" => SLocalHomogeneousThetaSpace F S (ω)
local notation "φω(" ω ")" => sLocalHomogeneousAdelicThetaLinearMap F S (ω)
local notation "Fourierₛ" => sAdeleSchwartzFourier (F := F) (S := S)
local notation "Zₛ" => sLocalIdelicZFunction (F := F) (S := S)
local notation "ρₛ(" χ ", " s ")" => sLocalRhoFactor (F := F) (S := S) (normChart(χ) (s))

local notation "rightInterval" => Ioi (0 : ℝ)
local notation "leftInterval" => Iio (1 : ℝ)
local notation "overlapInterval" => Ioo (0 : ℝ) 1
local notation "rightHalf" => Complex.re ⁻¹' rightInterval
local notation "leftHalf" => Complex.re ⁻¹' leftInterval
local notation "overlap" => Complex.re ⁻¹' overlapInterval
local notation "B⁺" => SchwartzBergman rightInterval
local notation "B⁻" => SchwartzBergman leftInterval
local notation "B⁰" => SchwartzBergman overlapInterval

section SecondStructure

-- The injectivity assertion in (5.4.1.1) is `sLocalThetaMellin_injective` from §5.1.

/-- Paper: (5.4.1.1), p. 265.
The Mellin map on the S-local theta quotient is continuous for compact convergence
on the regular locus of the meromorphic target. -/
theorem continuous_sLocalThetaMellin :
    Continuous (sLocalThetaMellin (F := F) (S := S)) := by sorry

/-- Paper: Theorem 5.4.1.1(1), p. 265.
Every norm-one character has a unique unitary lift trivial on the chosen norm section.
Its norm twists give the coordinates used for the Second Structure Theorem. -/
theorem existsUnique_sLocalNormSectionCharacter (τ : ℝ≥0ˣ →ₜ* Jₛ)
    (_hτ : RightInverse τ mₛ) (ω : PontryaginDual J₁) :
    ∃! χ : PontryaginDual Jₛ, restrict₁(χ) = ω ∧ ∀ t, χ (τ t) = 1 := by sorry

/-- Paper: (5.4.1.2), p. 265.
The two zeta restrictions descend uniquely as a linear map on homogeneous theta classes.
Deviation: We use the unitary-lift coordinates of Remark 5.4.1.2. The normalized lift
for a chosen section recovers the coordinates of Theorem 5.4.1.1. If the lift
has frequency x on the section, both entries, as functions of s here, shift by +ix.
The unreflected Fourier Mellin transform separately has frequency -x. -/
theorem existsUnique_sLocalZetaPair (χ : PontryaginDual Jₛ) :
    ∃! U : Θω(restrict₁(χ)) →ₗ[ℂ] B⁺ × B⁻, ∀ (f : ℬₛ),
      EqOn (U (Submodule.Quotient.mk f)).1.val (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf ∧
      EqOn (U (Submodule.Quotient.mk f)).2.val
        (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) (1 - s))) leftHalf := by sorry

/-- Paper: (5.4.1.2), p. 265.
The map pairs the zeta transform with the reflected zeta transform of the Fourier transform.
Deviation: The chart is the unitary-lift chart of Remark 5.4.1.2. -/
def sLocalZetaPair (χ : PontryaginDual Jₛ) : Θω(restrict₁(χ)) →ₗ[ℂ] B⁺ × B⁻ :=
  (existsUnique_sLocalZetaPair (F := F) (S := S) χ).exists.choose

/-- Paper: (5.4.1.2), p. 265.
On test functions the two components evaluate to their respective zeta integrals
on their half-planes of convergence. -/
theorem sLocalZetaPair_mk (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    EqOn (sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)).1.val
      (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf ∧
    EqOn (sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)).2.val
      (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) (1 - s))) leftHalf := by sorry

/-- Paper: (5.4.1.3), p. 266.
Subtracting the corrected second component from the first on the overlap is a
continuous linear map into the Schwartz–Bergman space of the overlap. -/
theorem existsUnique_sLocalZetaMatchingDifference (χ : PontryaginDual Jₛ) :
    ∃! D : B⁺ × B⁻ →L[ℂ] B⁰, ∀ p : B⁺ × B⁻,
      EqOn (D p).val (fun s ↦ p.1.val s - ρₛ(χ, s) * p.2.val s) overlap := by sorry

/-- Paper: (5.4.1.3), p. 266.
The space W is the kernel of the difference of the two restrictions, with the
second restriction multiplied by the local functional-equation factor. -/
def sLocalZetaMatching (χ : PontryaginDual Jₛ) : Submodule ℂ (B⁺ × B⁻) :=
  let difference : B⁺ × B⁻ →L[ℂ] B⁰ :=
    (existsUnique_sLocalZetaMatchingDifference (F := F) (S := S) χ).exists.choose
  LinearMap.ker difference.toLinearMap

/-- Paper: (5.4.1.3), p. 266.
A pair belongs to W exactly when its components satisfy the functional equation
at each point in the overlap strip. -/
theorem mem_sLocalZetaMatching (χ : PontryaginDual Jₛ) (p : B⁺ × B⁻) :
    p ∈ sLocalZetaMatching (F := F) (S := S) χ ↔
      EqOn p.1.val (fun s ↦ ρₛ(χ, s) * p.2.val s) overlap := by sorry

/-- Paper: Theorem 5.4.1.1(1), p. 266.
The zeta pair is a topological embedding with closed range. -/
theorem sLocalZetaPair_isClosedEmbedding (χ : PontryaginDual Jₛ) :
    IsClosedEmbedding (sLocalZetaPair (F := F) (S := S) χ) := by sorry

/-- Paper: Theorem 5.4.1.1(1), p. 266.
Every matching pair, and only a matching pair, comes from a homogeneous theta class. -/
theorem sLocalZetaPair_range (χ : PontryaginDual Jₛ) :
    (sLocalZetaPair (F := F) (S := S) χ).range = sLocalZetaMatching (F := F) (S := S) χ := by sorry

-- TODO(paper-gap): The two printed translation factors disagree on the overlap.
-- The functional equation and Fourier scaling both give the first factor on both entries.

/-- Paper: Theorem 5.4.1.1(1), p. 266, and Remark 5.4.1.2, p. 266.
Inverse left translation of a test induces multiplication of each zeta coordinate
by the first component's quasi-character evaluated at the translating idele class.
Deviation: Fourier scaling contributes the norm, and inversion of the Fourier
quasi-character gives the same multiplier as in the first coordinate. -/
theorem sLocalZetaPair_translate (χ : PontryaginDual Jₛ) (u : Aₛˣ) (f : ℬₛ) :
    let p : B⁺ × B⁻ := sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)
    let q : B⁺ × B⁻ := sLocalZetaPair (F := F) (S := S) χ
      (Submodule.Quotient.mk (schwartzBruhatUnitTranslate (R := Aₛ) u f))
    EqOn q.1.val (fun s ↦ normChart(χ) s (QuotientGroup.mk u) * p.1.val s) rightHalf ∧
    EqOn q.2.val (fun s ↦ normChart(χ) s (QuotientGroup.mk u) * p.2.val s) leftHalf :=
  by sorry

/-- Paper: Theorem 5.4.1.1(1), pp. 265–266.
The componentwise multipliers give a jointly continuous action on the ambient pair.
Deviation: Both coordinates in the reflected chart have the character of the test. -/
theorem exists_sLocalZetaPair_action (χ : PontryaginDual Jₛ) :
    ∃ A : Jₛ →* ((B⁺ × B⁻) →L[ℂ] (B⁺ × B⁻)),
      Continuous (fun p : Jₛ × (B⁺ × B⁻) ↦ A p.1 p.2) ∧
      ∀ (g : Jₛ) (p : B⁺ × B⁻),
        EqOn (A g p).1.val (fun s ↦ normChart(χ) s g * p.1.val s) rightHalf ∧
        EqOn (A g p).2.val (fun s ↦ normChart(χ) s g * p.2.val s) leftHalf := by sorry

/-- Paper: Theorem 5.4.1.1(2), p. 266.
The quotient topology on every homogeneous S-local theta space is Fréchet. -/
theorem sLocalHomogeneousThetaSpace_frechet (ω : PontryaginDual J₁) :
    IsFrechetTVS (Θω(ω)) := by sorry

/-- Paper: Theorem 5.4.1.1(2), p. 266.
Every homogeneous S-local theta space is separable. -/
theorem sLocalHomogeneousThetaSpace_separable (ω : PontryaginDual J₁) :
    SeparableSpace (Θω(ω)) := by sorry

-- The nuclearity assertion in (2) is `sLocalHomogeneousThetaSpace_nuclear` from §5.2.3.

/-- Paper: Lemma 5.4.1.3, p. 266.
The quotient-to-pair map is continuous. -/
theorem continuous_sLocalZetaPair (χ : PontryaginDual Jₛ) : Continuous (sLocalZetaPair (F := F) (S := S) χ) := by sorry

/-- Paper: Lemma 5.4.1.3, p. 266.
The two zeta restrictions determine the homogeneous theta class. -/
theorem injective_sLocalZetaPair (χ : PontryaginDual Jₛ) : Injective (sLocalZetaPair (F := F) (S := S) χ) := by sorry

-- Match the choice of archimedean coordinates in §5.3.4.
local notation "RealModels" => ((w : {v : InfinitePlace F // v.IsReal}) →
  {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
local notation "ComplexModels" => ((w : {v : InfinitePlace F // v.IsComplex}) →
  {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)})

local notation "polarTests(" r ", " c ")" => sAdelePolarFree (F := F) S (r) (c)

local notation "polarKernel(" P ", " ω ")" => LinearMap.ker ((φω(ω)).comp (P).subtype)

/-- Paper: (5.4.1.7), p. 267.
The polar-free homogeneous theta space is the quotient of the polar-free subspace
by the kernel of its restricted homogeneous theta transform. -/
abbrev SLocalPolarFreeThetaSpace (r : RealModels) (c : ComplexModels) (ω : PontryaginDual J₁) :=
  ↥(polarTests(r, c)) ⧸ polarKernel(polarTests(r, c), ω)

/-- Paper: (5.4.1.7), p. 267.
Two polar-free representatives define the same class exactly when their
homogeneous theta functions coincide. -/
theorem sLocalPolarFreeThetaSpace_mk_eq_iff (r : RealModels) (c : ComplexModels)
    (ω : PontryaginDual J₁) (f g : polarTests(r, c)) :
    (polarKernel(polarTests(r, c), ω)).mkQ f = (polarKernel(polarTests(r, c), ω)).mkQ g ↔
      φω(ω) f.val = φω(ω) g.val := by sorry

local notation "polarInclusion(" P ", " ω ")" =>
  (polarKernel(P, ω)).mapQ (LinearMap.ker (φω(ω))) (P).subtype
    (le_of_eq (LinearMap.ker_comp (P).subtype (φω(ω))))

/-- Paper: (5.4.1.7), p. 267.
The zeta pair on the polar-free quotient is the full zeta pair applied to the
class of the same test function. -/
def sLocalPolarFreeZetaPair (χ : PontryaginDual Jₛ) (r : RealModels) (c : ComplexModels) :
    SLocalPolarFreeThetaSpace (F := F) (S := S) r c (restrict₁(χ)) →ₗ[ℂ] B⁺ × B⁻ :=
  (sLocalZetaPair (F := F) (S := S) χ).comp (polarInclusion(polarTests(r, c), restrict₁(χ)))

/-- Paper: (5.4.1.8), p. 267.
The matching pairs in V are those whose first component extends to an entire function. -/
def sLocalPolarFreeMatching (χ : PontryaginDual Jₛ) : Set (B⁺ × B⁻) :=
  {p | p ∈ sLocalZetaMatching (F := F) (S := S) χ ∧
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H univ ∧ EqOn H p.1.val rightHalf}

/-- Paper: (5.4.1.8), p. 267.
In a matching pair the first component has an entire extension exactly when the
continued second component has no poles in the left half-plane. -/
theorem mem_sLocalPolarFreeMatching_iff (χ : PontryaginDual Jₛ) (p : B⁺ × B⁻) :
    p ∈ sLocalPolarFreeMatching (F := F) (S := S) χ ↔ p ∈ sLocalZetaMatching (F := F) (S := S) χ ∧
      ∀ s ∈ leftHalf, 0 ≤ meromorphicOrderAt (fun z ↦ ρₛ(χ, z) * p.2.val z) s := by sorry

/-- Paper: Proposition 5.4.1.4, p. 267.
The zeta pair on the polar-free quotient is a topological embedding with closed range. -/
theorem sLocalPolarFreeZetaPair_isClosedEmbedding (χ : PontryaginDual Jₛ)
    (r : RealModels) (c : ComplexModels) :
    IsClosedEmbedding (sLocalPolarFreeZetaPair (F := F) (S := S) χ r c) := by sorry

/-- Paper: Proposition 5.4.1.4, p. 267.
The image of the polar-free quotient consists exactly of the matching pairs in V. -/
theorem sLocalPolarFreeZetaPair_range (χ : PontryaginDual Jₛ)
    (r : RealModels) (c : ComplexModels) :
    ((sLocalPolarFreeZetaPair (F := F) (S := S) χ r c).range : Set (B⁺ × B⁻)) =
      sLocalPolarFreeMatching (F := F) (S := S) χ := by sorry

-- The translation formula restricts by `sLocalZetaPair_translate` and
-- `sAdelePolarFree_translate`.

-- TODO(paper-gap): (5.4.1.11) on p. 270 loses the inverse on the different in the
-- last indicator. Boundedness of the multiplier in (5.4.1.10) alone does not
-- imply the closed-range assertion for (5.4.1.12).
-- TODO(paper-gap): The lexicographic order before (5.4.1.14) on p. 270 does not
-- give the claimed inclusions of the pole sets. The limit used for the Laurent
-- coefficient on p. 271 fails at poles of order greater than its exponent.
-- TODO(paper-gap): The proof of (5.4.1.22) on p. 273 needs a comparison of the
-- quotient topologies. The proposed family in (5.4.1.23) fails to span: at two
-- real places with trivial character and cutoff (0,0) it gives one test. The
-- product Gaussian has a double pole at zero. Dilating one factor by 2 adds
-- log(2) times its leading Laurent coefficient to its residue, giving two
-- independent principal parts. The range theorem needs another argument.

-- TODO(paper-gap): Remark 5.4.1.5 on p. 274 cites part (4) of a theorem with two parts.
-- The local Fréchet assertion is part (2). The global assertion is Corollary
-- 6.2.1.2, via Theorem 6.2.1.1 on isotypes for S with trivial S-class group
-- containing the character's ramification.

end SecondStructure

section Cech

-- The quotient measure in §3.3 is defined with this Borel measurable structure.
local instance instSIdeleQuotientMeasurableSpaceSec4 : MeasurableSpace Jₛ := borel _

local instance instSIdeleGroupLocallyCompactSec4 : LocallyCompactSpace Aₛˣ :=
  (sIdeleGroup_description F S).2.2.1

local instance instSIdeleQuotientT2Sec4 : T2Space Jₛ :=
  letI := isClosed_sProjectedDiagonal (F := F) (S := S)
  inferInstance

local notation "Θₛ" => SLocalAdelicThetaSpace F S
local notation "μₛ" => sLocalQuotientTamagawaMeasure F S
local notation "μweighted" => ((μₛ).withDensity (fun g : Jₛ ↦ ENNReal.ofReal (normℝ(mₛ g))))
local notation "L²ₛ" => MeasureTheory.Lp ℂ 2 μweighted
local notation "Ẽ(" I ")" => ModulatedExponentialDecay (⟨mₛ, hmₛ⟩ : Jₛ →ₜ* ℝ≥0ˣ) I
local notation "reflect(" I ")" => ((fun a : ℝ ↦ 1 - a) ⁻¹' I)

/-- Paper: (5.4.2.1), p. 274.
The ordinary theta quotient injects continuously into L² for the norm-weighted
quotient Tamagawa measure. The map keeps the almost-everywhere class of the theta
function attached to a test representative. -/
theorem existsUnique_sLocalThetaWeightedL2 :
    ∃! j : Θₛ →L[ℂ] L²ₛ, Injective j ∧ ∀ f : ℬₛ,
      ((j (Submodule.Quotient.mk f)) : Jₛ → ℂ) =ᵐ[μweighted] sLocalAdelicThetaOnClasses F S f := by sorry

local notation "weightedTheta" =>
  (show Θₛ →L[ℂ] L²ₛ from (existsUnique_sLocalThetaWeightedL2 (F := F) (S := S)).exists.choose)

/-- Paper: (5.4.2.1), p. 274.
The norm of the embedded class equals the square root of the weighted integral
of the squared absolute value of its theta function. -/
theorem sLocalThetaWeightedL2_norm (f : ℬₛ) :
    ‖weightedTheta (Submodule.Quotient.mk f)‖ =
      Real.sqrt (∫ g : Jₛ, ‖sLocalAdelicThetaOnClasses F S f g‖ ^ 2 *
        normℝ(mₛ g) ∂μₛ) := by sorry

variable (F S) in
/-- Paper: (5.4.2.2), p. 274.
The weighted Hilbert completion is realized as the closure of the theta image
in the weighted L² space. -/
abbrev SLocalThetaL2 :=
  ↥(LinearMap.range ((weightedTheta).toLinearMap)).topologicalClosure

local notation "completionMap" => (show Θₛ →ₗ[ℂ] SLocalThetaL2 F S from
  (weightedTheta).toLinearMap.codRestrict
    (LinearMap.range (weightedTheta).toLinearMap).topologicalClosure
    (fun x ↦ Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x)))

/-- Paper: (5.4.2.2), p. 274.
The test-function image is dense in the chosen model of the completion. -/
theorem sLocalThetaL2_dense : DenseRange completionMap := by sorry

/-- Paper: (5.4.2.1)–(5.4.2.2), p. 274.
S-local Fourier transform has a unique unitary extension to the weighted completion,
given on theta classes by Fourier transform of the test representative. -/
theorem existsUnique_sLocalThetaL2Fourier :
    ∃! e : SLocalThetaL2 F S ≃ₗᵢ[ℂ] SLocalThetaL2 F S, ∀ f : ℬₛ,
      e (completionMap (Submodule.Quotient.mk f)) =
        completionMap (Submodule.Quotient.mk (Fourierₛ f)) := by sorry

local notation "weightedFourier" =>
  (show SLocalThetaL2 F S ≃ₗᵢ[ℂ] SLocalThetaL2 F S from
    (existsUnique_sLocalThetaL2Fourier (F := F) (S := S)).exists.choose)

local notation "decayEval(" I ", " g ")" =>
  (LinearMap.proj (g : Jₛ)).comp (modulatedExponentialDecaySubmodule
    (⟨mₛ, hmₛ⟩ : Jₛ →ₜ* ℝ≥0ˣ) (I)).subtype

/-- Paper: (5.4.2.3), p. 275.
The norm-one isotype in the weighted Schwartz–Bruhat space is the common
eigenspace for inverse left translation. -/
def sLocalDecayIsotype (I : Set ℝ) (ω : PontryaginDual J₁) : Submodule ℂ Ẽ(I) :=
  ⨅ u : J₁, ⨅ g : Jₛ, LinearMap.ker
    (decayEval(I, u.val⁻¹ * g) - (ω u : ℂ) • decayEval(I, g))

local notation "Eω(" I ", " ω ")" => ↥(sLocalDecayIsotype (F := F) (S := S) (I) (ω))

/-- Paper: (5.4.2.3), p. 275.
A weighted test function lies in the isotype exactly when it obeys the
norm-one translation law at every idele class. -/
theorem mem_sLocalDecayIsotype (I : Set ℝ) (ω : PontryaginDual J₁) (φ : Ẽ(I)) :
    φ ∈ sLocalDecayIsotype (F := F) (S := S) I ω ↔
      ∀ (u : J₁) (g : Jₛ), φ.val (u.val⁻¹ * g) = (ω u : ℂ) * φ.val g := by sorry

/-- Paper: (5.4.2.3), p. 275, and Proposition D.3.3.12, p. 811.
The coordinate equations give the Appendix D isotype for its translation action. -/
theorem sLocalDecayIsotype_eq_actionIsotype (I : Set ℝ) (ω : PontryaginDual J₁)
    (A : Jₛ →* (Ẽ(I) →L[ℂ] Ẽ(I)))
    (hA : ∀ (g : Jₛ) (f : Ẽ(I)) (x : Jₛ), (A g f).val x = f.val (g⁻¹ * x)) :
    sLocalDecayIsotype (F := F) (S := S) I ω = actionIsotype (A.comp (mₛ).ker.subtype) ω := by sorry

/-- Paper: Proposition 5.4.2.1(1), p. 275.
Fourier transform extends uniquely between the weighted isotype and the conjugate
isotype for the reflected exponent interval. Its value on each embedded homogeneous
theta function is the homogeneous theta function of the Fourier-transformed test.
Deviation: The extension identity uses the two isotypes of the theta quotient. -/
theorem existsUnique_sLocalDecayFourier (χ : PontryaginDual Jₛ) (I : Set ℝ) (_hOpen : IsOpen I)
    (_hInt : OrdConnected I) (_hne : I.Nonempty) (_hsub : I ⊆ overlapInterval) :
    let domain : Submodule ℂ Ẽ(I) := sLocalDecayIsotype (F := F) (S := S) I (restrict₁(χ))
    let codomain : Submodule ℂ Ẽ(reflect(I)) :=
      sLocalDecayIsotype (F := F) (S := S) (reflect(I)) (restrict₁(χ⁻¹))
    ∃! e : domain ≃L[ℂ] codomain,
      let transform : domain → codomain := e
      ∀ f : ℬₛ, ∃ (u : domain) (v : codomain), transform u = v ∧
        (∀ g : Jₛ, u.val.val g = φω(restrict₁(χ)) f g) ∧
        (∀ g : Jₛ, v.val.val g = φω(restrict₁(χ⁻¹)) (Fourierₛ f) g) := by sorry

/-- Paper: Proposition 5.4.2.1(2), p. 275.
If the exponent interval contains one half, the weighted Schwartz–Bruhat space
injects continuously into the theta completion by its almost-everywhere values. -/
theorem existsUnique_sLocalDecayToThetaL2 (I : Set ℝ) (_hOpen : IsOpen I)
    (_hInt : OrdConnected I) (_hsub : I ⊆ overlapInterval) (_hhalf : (1 / 2 : ℝ) ∈ I) :
    ∃! j : Ẽ(I) →L[ℂ] SLocalThetaL2 F S, Injective j ∧ ∀ f : Ẽ(I),
      (((j f).val : L²ₛ) : Jₛ → ℂ) =ᵐ[μweighted] f.val := by sorry

/-- Paper: Proposition 5.4.2.1(2), p. 275.
The unitary Fourier extension agrees on the weighted isotype with the Fourier map
for the reflected interval, after embedding both functions by their L² classes. -/
theorem sLocalDecayFourier_eq_weightedFourier (χ : PontryaginDual Jₛ) (I : Set ℝ) (hOpen : IsOpen I)
    (hInt : OrdConnected I) (hsub : I ⊆ overlapInterval) (hhalf : (1 / 2 : ℝ) ∈ I) :
    let j := (existsUnique_sLocalDecayToThetaL2 (F := F) (S := S)
      I hOpen hInt hsub hhalf).exists.choose
    let e := (existsUnique_sLocalDecayFourier (F := F) (S := S) χ I hOpen hInt ⟨_, hhalf⟩ hsub).exists.choose
    ∀ f : Eω(I, restrict₁(χ)),
      ((((weightedFourier (j f.val)).val : L²ₛ) : Jₛ → ℂ)) =ᵐ[μweighted] (e f).val.val :=
  by sorry

-- TODO(paper-gap): Theorem 5.4.2.2(2) prints incompatible intervals for J_τ.
-- In (3) the asserted half-plane map has poles, already at zero for the trivial
-- character over ℚ with no finite places. In (4) the printed operator omits
-- reflection and applies this multiplier on the entire positive half-plane.
-- Restriction to the overlap gives the continuous difference in the diagram below.
-- In (1), the conjugate character requires the opposite shift when x₀ ≠ 0.

/-- Paper: Theorem 5.4.2.2(2), p. 276.
Radial inversion, with the compact coordinate fixed, exchanges the two weight intervals.
Deviation: The target exponent interval is the reflection of the source interval. -/
theorem existsUnique_sLocalCechRadialReflection (τ : ℝ≥0ˣ →ₜ* Jₛ)
    (_hτ : RightInverse τ mₛ) (ω : PontryaginDual J₁) :
    ∃! J : Eω(rightInterval, ω) ≃L[ℂ] Eω(leftInterval, ω),
      ∀ (f : Eω(rightInterval, ω)) (t : ℝ≥0ˣ) (k : J₁),
        (J f).val.val (τ t * k.val) =
          ((normℝ(t) : ℂ)⁻¹) * f.val.val (τ t⁻¹ * k.val) := by sorry

local notation "upperMiddle(" χ ")" => Eω(rightInterval, restrict₁(χ)) × Eω(rightInterval, restrict₁(χ⁻¹))

/-- Paper: (5.4.2.6), p. 276.
The upper left arrow pairs the two homogeneous theta functions attached to
a test and to its S-adelic Fourier transform. -/
theorem existsUnique_sLocalCechThetaPair (χ : PontryaginDual Jₛ) :
    ∃! U : Θω(restrict₁(χ)) →L[ℂ] upperMiddle(χ), ∀ f : ℬₛ,
      (U (Submodule.Quotient.mk f)).1.val.val = ⇑(φω(restrict₁(χ)) f) ∧
      (U (Submodule.Quotient.mk f)).2.val.val = ⇑(φω(restrict₁(χ⁻¹)) (Fourierₛ f)) := by sorry

local notation "cechThetaPair(" χ ")" => (show Θω(restrict₁(χ)) →L[ℂ] upperMiddle(χ) from
  (existsUnique_sLocalCechThetaPair (F := F) (S := S) χ).exists.choose)

/-- Paper: (5.4.2.6), p. 276.
On the lower row the right half-plane zeta pair maps to the difference of the
first entry and the reflected second entry multiplied on the overlap by the
functional-equation factor. The image of the first map is the kernel of the difference.
Deviation: The multiplier is used on the overlap where it is holomorphic. -/
theorem sLocalCechBergman_exact (χ : PontryaginDual Jₛ) :
    ∃ (U : Θω(restrict₁(χ)) →L[ℂ] B⁺ × B⁺) (D : B⁺ × B⁺ →L[ℂ] B⁰),
      (∀ f : ℬₛ,
        EqOn (U (Submodule.Quotient.mk f)).1.val (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf ∧
        EqOn (U (Submodule.Quotient.mk f)).2.val
          (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) s)) rightHalf) ∧
      (∀ p : B⁺ × B⁺,
        EqOn (D p).val (fun s ↦ p.1.val s - ρₛ(χ, s) * p.2.val (1 - s)) overlap) ∧
      Function.Exact U D := by sorry

/-- Paper: (5.4.2.6), p. 276.
In the lower row the zeta pair of the test and its Fourier transform is a
topological embedding with closed range. -/
theorem sLocalCechBergman_isClosedEmbedding (χ : PontryaginDual Jₛ) (U : Θω(restrict₁(χ)) →L[ℂ] B⁺ × B⁺)
    (_hU : ∀ f : ℬₛ,
      EqOn (U (Submodule.Quotient.mk f)).1.val (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf ∧
      EqOn (U (Submodule.Quotient.mk f)).2.val
        (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) s)) rightHalf) :
    IsClosedEmbedding U := by sorry

/-- Paper: Theorem 5.4.2.2, p. 276.
Restriction of a unitary character to the norm section defines a unique real
frequency in the Mellin coordinate. -/
theorem existsUnique_sLocalCechFrequency (χ : PontryaginDual Jₛ) (τ : ℝ≥0ˣ →ₜ* Jₛ) :
    ∃! x : ℝ, ∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = (normℝ(t) : ℂ) ^ ((x : ℂ) * Complex.I) :=
  by sorry

local notation "mellinIntegrand(" τ ", " φ ", " z ")" =>
  (fun t : ℝ≥0ˣ ↦ (φ) ((τ) t) * (normℝ(t) : ℂ) ^ (z))

/-- Paper: Theorem 5.4.2.2(1), p. 276.
On a norm-one isotype, restriction to the norm section followed by the
vertically shifted Mellin integral defines a continuous linear equivalence.
The integrals are absolutely convergent in the open strip. -/
theorem existsUnique_sLocalDecayMellin (τ : ℝ≥0ˣ →ₜ* Jₛ) (_hτ : RightInverse τ mₛ)
    (I : Set ℝ) (_hOpen : IsOpen I) (_hInt : OrdConnected I) (_hne : I.Nonempty)
    (ω : PontryaginDual J₁) (x : ℝ) :
    ∃! M : Eω(I, ω) ≃L[ℂ] SchwartzBergman I, ∀ (f : Eω(I, ω)) (s : ℂ), s.re ∈ I →
      let k := mellinIntegrand(τ, f.val.val, s + (x : ℂ) * Complex.I)
      Integrable k positiveRealHaar ∧ (M f).val s = ∫ t, k t ∂positiveRealHaar := by sorry

/-- Paper: Theorem 5.4.2.2(6), p. 277.
The right vertical arrow is the Mellin equivalence on the overlap followed by
translation of the spectral argument by the section's imaginary frequency. -/
theorem existsUnique_sLocalCechStripMellin (x : ℝ) :
    ∃! M : PositiveRealExponentialDecay overlapInterval ≃L[ℂ] B⁰,
      ∀ f s, s ∈ overlap → (M f).val s =
        mellin (fun t ↦ f.val (Real.log t)) (s + (x : ℂ) * Complex.I) := by sorry

/-- Paper: (5.4.2.6), p. 276.
Applying the two shifted Mellin transforms to the upper left arrow gives the
lower zeta pair on every theta class.
Deviation: The first and conjugate isotypes use opposite frequency shifts. -/
theorem sLocalCech_left_commutes (χ : PontryaginDual Jₛ)
    (τ : ℝ≥0ˣ →ₜ* Jₛ) (_hτ : RightInverse τ mₛ)
    (x : ℝ) (_hx : ∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = (normℝ(t) : ℂ) ^ ((x : ℂ) * Complex.I))
    (M₁ : Eω(rightInterval, restrict₁(χ)) ≃L[ℂ] B⁺)
    (M₂ : Eω(rightInterval, restrict₁(χ⁻¹)) ≃L[ℂ] B⁺)
    (_h₁ : ∀ f s, s ∈ rightHalf →
      (M₁ f).val s = ∫ t, mellinIntegrand(τ, f.val.val, s + (x : ℂ) * Complex.I) t
        ∂positiveRealHaar)
    (_h₂ : ∀ f s, s ∈ rightHalf →
      (M₂ f).val s = ∫ t, mellinIntegrand(τ, f.val.val, s - (x : ℂ) * Complex.I) t
        ∂positiveRealHaar)
    (f : ℬₛ) :
    let p : upperMiddle(χ) := cechThetaPair(χ) (Submodule.Quotient.mk f)
    EqOn (M₁ p.1).val (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf ∧
    EqOn (M₂ p.2).val (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) s)) rightHalf := by sorry

/-- Paper: Theorem 5.4.2.2(3)–(6) and (5.4.2.6), pp. 276–277.
The upper difference is the unique continuous map whose shifted Mellin transform
is the lower difference. The upper row is exact at the pair of decay spaces.
Deviation: The correcting factor multiplies the reflected transform on the overlap. -/
theorem existsUnique_sLocalCechDifference (χ : PontryaginDual Jₛ)
    (τ : ℝ≥0ˣ →ₜ* Jₛ) (hτ : RightInverse τ mₛ) (x : ℝ)
    (_hx : ∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = (normℝ(t) : ℂ) ^ ((x : ℂ) * Complex.I)) :
    ∀ (M₁ : Eω(rightInterval, restrict₁(χ)) ≃L[ℂ] B⁺)
      (M₂ : Eω(rightInterval, restrict₁(χ⁻¹)) ≃L[ℂ] B⁺)
      (M₀ : PositiveRealExponentialDecay overlapInterval ≃L[ℂ] B⁰),
      (∀ f s, s ∈ rightHalf → (M₁ f).val s =
        ∫ t, mellinIntegrand(τ, f.val.val, s + (x : ℂ) * Complex.I) t ∂positiveRealHaar) →
      (∀ f s, s ∈ rightHalf → (M₂ f).val s =
        ∫ t, mellinIntegrand(τ, f.val.val, s - (x : ℂ) * Complex.I) t ∂positiveRealHaar) →
      (∀ f s, s ∈ overlap → (M₀ f).val s =
        mellin (fun t ↦ f.val (Real.log t)) (s + (x : ℂ) * Complex.I)) →
    ∃! D : upperMiddle(χ) →L[ℂ] PositiveRealExponentialDecay overlapInterval,
      (∀ p : upperMiddle(χ), EqOn (M₀ (D p)).val
        (fun s ↦ (M₁ p.1).val s - ρₛ(χ, s) * (M₂ p.2).val (1 - s)) overlap) ∧
      Function.Exact cechThetaPair(χ) D := by sorry

/-- Paper: Remark 5.4.2.3 and (5.4.2.7), p. 277.
The pair of homogeneous theta functions of a test and its Fourier transform
embeds the homogeneous quotient as a closed subspace of the two weighted isotypes. -/
theorem sLocalCechThetaPair_isClosedEmbedding (χ : PontryaginDual Jₛ) : IsClosedEmbedding cechThetaPair(χ) := by sorry

end Cech

end RiemannMasullo
