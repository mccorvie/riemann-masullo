module

public import RiemannMasullo.Ch10_TraceSpectral.Sec1
public import RiemannMasullo.Ch11_ShellStructure.Sec1a

import all RiemannMasullo.AppA_AlgebraicNT.Sec3

/-!
# S-local carvings

Masullo, §11.1.2, pp. 480–483. A finite set of places in the base records its
finite places, with all archimedean places included throughout.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "μ₁" => normOneIdeleClassTamagawaMeasure F
local notation "ℬ₀" => ↥(adelePolarSubspace F)
local notation "ℬₛ(" S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "norm𝔽" => fun g : C𝔽 ↦ ((ideleClassNorm F g).val : ℝ)
local notation "classOf" => QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)

local instance instIdeleClassMeasurableSpaceSec1b : MeasurableSpace C𝔽 := borel _
local instance instIdeleClassBorelSpaceSec1b : BorelSpace C𝔽 := ⟨rfl⟩
local instance instIdeleClassT2SpaceSec1b : T2Space C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
local instance instIdeleClassLocallyCompactSpaceSec1b : LocallyCompactSpace C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
local instance instIdeleClassSecondCountableSec1b : SecondCountableTopology C𝔽 :=
  letI := idele_secondCountable F
  inferInstanceAs (SecondCountableTopology
    (I𝔽 ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))
local instance instIdeleClassHaarMeasureSec1b : Measure.IsHaarMeasure μ𝔽 :=
  (ideleClassTamagawaMeasure_isWeil F).1

/-- Paper: (11.1.2.1), p. 480. The indices are the finite sets of places outside
the base set, ordered by inclusion. All the archimedean places are in the base. -/
abbrev SLocalCarvingIndex (S : Finset V) := {T : Finset V // Disjoint S T}

/-- Paper: (11.1.2.1), p. 480. A finite set occurs as an index exactly when
each of its places is outside the base set. -/
theorem exists_sLocalCarvingIndex_iff (S T : Finset V) :
    (∃ i : SLocalCarvingIndex (F := F) S, i.val = T) ↔ ∀ v ∈ T, v ∉ S := by sorry

/-- Paper: (11.1.2.1), p. 480. There are countably many finite-place indices. -/
theorem countable_sLocalCarvingIndex (S : Finset V) :
    Countable (SLocalCarvingIndex (F := F) S) := by sorry

variable (F) in
/-- Paper: Theorem 11.1.2.1, p. 480. The zero-line ambient space is weighted L²
on the idele classes. It is the singleton-base case of the space used in §10.1. -/
abbrev IdeleClassZeroLineSobolev (s : ℝ) :=
  CompactIntervalSobolev μ𝔽 (fun g ↦ Real.log (norm𝔽 g)) 0 0 s

local notation "W(" s ")" => IdeleClassZeroLineSobolev F s
local notation "ν(" s ")" =>
  (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (norm𝔽 g))))
local notation "M(" s ", " J ", " hJ ")" => modulatedAbsoluteCutoffOperator m𝔽 (ν(s)) J hJ
local notation "Wω(" s ", " hs ", " ω ")" =>
  actionIsotype ((hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs).comp
    (ideleClassNorm F).ker.subtype) ω

/-- Paper: (11.1.2.2)–(11.1.2.3), p. 480. The two cutoff choices are the
positive half-line and the two-sided band in the idelic norm variable. -/
def sLocalCarvingBand (twoSided : Bool) (Λ : ℝ) : Set ℝ :=
  if twoSided then Icc Λ⁻¹ Λ else Ici Λ⁻¹

/-- Paper: (11.1.2.3), p. 480. Both cutoff bands are Borel. -/
theorem measurableSet_sLocalCarvingBand (twoSided : Bool) (Λ : ℝ) :
    MeasurableSet (sLocalCarvingBand twoSided Λ) := by sorry

/-- Paper: (11.1.2.3), p. 480. The half-line retains norm one at radius two
and the bounded band excludes norm three.
Deviation: Sanity check distinguishing the two cutoffs. -/
theorem sLocalCarvingBand_radius_two :
    (1 : ℝ) ∈ sLocalCarvingBand false 2 ∧ (3 : ℝ) ∉ sLocalCarvingBand true 2 := by sorry

/-- Paper: (11.1.2.3), p. 480. Homogeneous theta of an adelic test with both
polar values zero is in weighted L² on the zero line. -/
theorem memLp_homogeneousTheta_zeroLine (s : ℝ) (ω : PontryaginDual C₁) (f : ℬ₀) :
    MemLp (homogeneousAdelicTheta ω f.val : C𝔽 → ℂ) 2 (ν(s)) := by sorry

/-- Paper: (11.1.2.3), p. 480. A global finite-place principal value preserves
the two polar vanishing conditions. -/
theorem adelePrincipalValue_mem_polarSubspace (T : Finset V) (f : ℬ₀) :
    adelePrincipalValue F T f.val ∈ adelePolarSubspace F := by sorry

local notation "P(" T ", " f ")" =>
  (⟨adelePrincipalValue F T (f).val, adelePrincipalValue_mem_polarSubspace T f⟩ : ℬ₀)
local notation "θ(" s ", " ω ", " f ")" =>
  (memLp_homogeneousTheta_zeroLine s ω f).toLp (homogeneousAdelicTheta ω (f).val)

/-- Paper: (11.1.2.5), p. 480. The uncut stage is the closure of the homogeneous
polar-free theta image after applying the selected finite-place principal values.
Deviation: The image is presented by its linear span in the full weighted L² model. -/
def sLocalUncutCarving (s : ℝ) (ω : PontryaginDual C₁) (T : Finset V) :
    Submodule ℂ (W(s)) :=
  (Submodule.span ℂ (range (fun f : ℬ₀ ↦ θ(s, ω, P(T, f))))).topologicalClosure

/-- Paper: (11.1.2.5), p. 480. The empty stage is the closure of the unrestricted
homogeneous polar-free theta image.
Deviation: Sanity check for the uncut stage. -/
theorem sLocalUncutCarving_empty (s : ℝ) (ω : PontryaginDual C₁) :
    sLocalUncutCarving s ω ∅ =
      (Submodule.span ℂ (range (fun f : ℬ₀ ↦ θ(s, ω, f)))).topologicalClosure := by sorry

/-- Paper: (11.1.2.5), p. 480. Before any prime condition the uncut stage is the
norm-one isotype of the global theta completion from Definition 10.1.1.1. -/
theorem sLocalUncutCarving_empty_eq_globalThetaSobolev (s : ℝ) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :
    sLocalUncutCarving s ω ∅ =
      globalThetaSobolev F 0 (α := 0) (β := 0) le_rfl hs ⊓ Wω(s, hs, ω) := by sorry

/-- Paper: (11.1.2.3), p. 480. The cutoff stage is the closure of the linear
space obtained by applying the cutoff to the restricted theta tests.
Deviation: Read the printed P as the principal value PV used on p. 481. The
definition accepts any measurable norm band, including both in `sLocalCarvingBand`. -/
def sLocalCutoffCarving (s : ℝ) (ω : PontryaginDual C₁) (T : Finset V)
    (J : Set ℝ) (hJ : MeasurableSet J) : Submodule ℂ (W(s)) :=
  (Submodule.span ℂ (range (fun f : ℬ₀ ↦ M(s, J, hJ) (θ(s, ω, P(T, f)))))).topologicalClosure

/-- Paper: (11.1.2.3), p. 480. Each finite cutoff stage belongs to the cutoff
image of the ambient norm-one isotype. -/
theorem sLocalCutoffCarving_le_cutoffIsotype (s : ℝ) (hs : 0 ≤ s) (ω : PontryaginDual C₁)
    (T : Finset V) (J : Set ℝ) (hJ : MeasurableSet J) :
    sLocalCutoffCarving s ω T J hJ ≤ (Wω(s, hs, ω)).map (M(s, J, hJ)).toLinearMap := by sorry

/-- Paper: (11.1.2.3), p. 480. The full norm band leaves the uncut stage unchanged.
Deviation: Sanity check for the cutoff-stage definition. -/
theorem sLocalCutoffCarving_univ (s : ℝ) (ω : PontryaginDual C₁) (T : Finset V) :
    sLocalCutoffCarving s ω T univ MeasurableSet.univ = sLocalUncutCarving s ω T := by sorry

/-- Paper: (11.1.2.4), p. 480. The cofinal limit is the intersection of all
finite-place cutoff stages outside the base set. -/
def sLocalCarvingLimit (s : ℝ) (ω : PontryaginDual C₁) (S : Finset V)
    (J : Set ℝ) (hJ : MeasurableSet J) : Submodule ℂ (W(s)) :=
  ⨅ i : SLocalCarvingIndex (F := F) S, sLocalCutoffCarving s ω i.val J hJ

/-- Paper: Remark 11.1.2.2, p. 480. A cofinal sequence increases by inclusion
and exhausts the finite places outside the base set. -/
def IsSLocalCarvingCofinal {S : Finset V} (A : ℕ → SLocalCarvingIndex (F := F) S) : Prop :=
  Monotone A ∧ (⋃ k, ((A k).val : Set V)) = (S : Set V)ᶜ

/-- Paper: Remark 11.1.2.2, p. 480. An increasing sequence exhausts the outside
places exactly when every finite set of them is contained in some term. -/
theorem isSLocalCarvingCofinal_iff {S : Finset V} (A : ℕ → SLocalCarvingIndex (F := F) S) :
    IsSLocalCarvingCofinal A ↔ Monotone A ∧ ∀ i : SLocalCarvingIndex (F := F) S, ∃ k, i ≤ A k := by sorry

/-- Paper: Remark 11.1.2.2, p. 480. Every base admits a cofinal sequence
of finite sets of outside places. -/
theorem exists_sLocalCarvingCofinal (S : Finset V) :
    ∃ A : ℕ → SLocalCarvingIndex (F := F) S, IsSLocalCarvingCofinal A := by sorry

/-- Paper: (11.1.2.12), p. 481. Adding finite-place conditions gives a smaller
cutoff stage in the inclusion order.
Deviation: The monotonicity applies to any measurable norm band. -/
theorem sLocalCutoffCarving_antitone (s : ℝ) (ω : PontryaginDual C₁)
    (J : Set ℝ) (hJ : MeasurableSet J) :
    Antitone (fun T : Finset V ↦ sLocalCutoffCarving s ω T J hJ) := by sorry

local notation "ωOf(" χ ")" =>
  (χ).comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
    C₁ →ₜ* C𝔽)
local notation "Unramified(" χ ", " S ")" => ideleClassNormTwist χ 0 ∈ unramifiedOutside F S
local notation "TrivialPic(" S ")" => Subsingleton (CommRing.Pic (Set.integer (R := 𝓞 F) S F))
local notation "DegreeBound(" s ")" => 2 * (Module.finrank ℚ F : ℝ) ≤ s
local notation "J(" b ", " Λ ")" => sLocalCarvingBand b Λ
local notation "hJ(" b ", " Λ ")" => measurableSet_sLocalCarvingBand b Λ

/-- Paper: Theorem 11.1.2.1(1), p. 480, and (11.1.2.13)–(11.1.2.15),
pp. 481–482. Every cofinal sequence realizes the same limit by intersection.
Deviation: Equality to the intersection over all indices also gives a sanity
check for the sequence-independent definition. -/
theorem sLocalCarvingLimit_eq_iInf {S : Finset V} (s : ℝ) (ω : PontryaginDual C₁)
    (J : Set ℝ) (hJ : MeasurableSet J)
    (A : ℕ → SLocalCarvingIndex (F := F) S) (_hA : IsSLocalCarvingCofinal A) :
    sLocalCarvingLimit s ω S J hJ = ⨅ k, sLocalCutoffCarving s ω (A k).val J hJ := by sorry

/-- Paper: Theorem 11.1.2.1(1), p. 480. The cofinal limit is closed in the
ambient weighted L² space. -/
theorem isClosed_sLocalCarvingLimit (S : Finset V) (s : ℝ) (ω : PontryaginDual C₁)
    (J : Set ℝ) (hJ : MeasurableSet J) :
    IsClosed (sLocalCarvingLimit s ω S J hJ : Set (W(s))) := by sorry

/-- Paper: Theorem 11.1.2.1(1), p. 480. The cofinal limit lies in the image
of the ambient isotype under the cutoff. -/
theorem sLocalCarvingLimit_le_cutoffIsotype {S : Finset V} (χ : PontryaginDual C𝔽)
    (_hχ : Unramified(χ, S)) (_hPic : TrivialPic((S : Set V)))
    (s : ℝ) (hs : DegreeBound(s)) (twoSided : Bool) (Λ : ℝ) (_hΛ : 0 < Λ) :
    let hs₀ : 0 ≤ s := (mul_nonneg zero_le_two (Nat.cast_nonneg _)).trans hs
    sLocalCarvingLimit s (ωOf(χ)) S (J(twoSided, Λ)) (hJ(twoSided, Λ)) ≤
      (Wω(s, hs₀, ωOf(χ))).map (M(s, J(twoSided, Λ), hJ(twoSided, Λ))).toLinearMap := by sorry

-- TODO(paper-gap): On p. 482 the basis conclusion of Theorem 11.2.0.2
-- requires s ≥ 2 * card(i'), while (11.1.2.2) bounds the field degree.
-- A direct proof can use a Mellin evaluation at a new Euler zero if one
-- exhibits a polar-free test on which the smaller stage has nonzero value.

/-- Paper: Theorem 11.1.2.1(2), p. 480, (11.1.2.5). If the larger stage adds
a place over a rational prime absent at the smaller stage, the inclusion of the
uncut completions is strict. -/
theorem sLocalUncutCarving_lt {S : Finset V} (χ : PontryaginDual C𝔽)
    (_hχ : Unramified(χ, S)) (_hPic : TrivialPic((S : Set V)))
    (s : ℝ) (_hs : DegreeBound(s)) (i i' : SLocalCarvingIndex (F := F) S) (_hii' : i < i')
    (_hp : ∃ p : ℕ, p.Prime ∧
      (∀ v ∈ i.val, (p : 𝓞 F) ∉ v.asIdeal) ∧ ∃ v ∈ i'.val, (p : 𝓞 F) ∈ v.asIdeal) :
    sLocalUncutCarving s (ωOf(χ)) i'.val < sLocalUncutCarving s (ωOf(χ)) i.val := by sorry

/-- Paper: Theorem 11.1.2.1(2), p. 480, (11.1.2.6). The cutoff stages
are nested under the inclusion order of their finite-place indices.
Deviation: The inclusion permits equality. The printed subsequence claim fails
for the bounded cutoffs over ℚ, already when one prime is added. -/
theorem sLocalCutoffCarving_le {S : Finset V} (χ : PontryaginDual C𝔽)
    (_hχ : Unramified(χ, S)) (_hPic : TrivialPic((S : Set V)))
    (s : ℝ) (_hs : DegreeBound(s)) (i i' : SLocalCarvingIndex (F := F) S) (_hii' : i ≤ i')
    (twoSided : Bool) (Λ : ℝ) (_hΛ : 0 < Λ) :
    let J := J(twoSided, Λ)
    let hJ : MeasurableSet J := hJ(twoSided, Λ)
    sLocalCutoffCarving s (ωOf(χ)) i'.val J hJ ≤
      sLocalCutoffCarving s (ωOf(χ)) i.val J hJ := by sorry

-- TODO(paper-gap): In (11.1.2.16) eventual equality gives equality at all
-- earlier radii by applying their nested cutoffs. The representatives can vary
-- with the radius, so strong convergence on fixed inputs gives no contradiction.

/-- Paper: (11.1.2.7), p. 480. The local test is extended to ideles by
multiplying by the indicator of integer units at every place outside S. -/
def sLocalCarvingIdeleTest (S : Finset V) (f : ℬₛ(S)) : I𝔽 → ℂ :=
  {g : I𝔽 | ∀ v ∉ S, Valued.v (g.val.2 v) = 1}.indicator
    (fun g ↦ f (Multiplicative.ofAdd (adeleProjection F S g.val)))

/-- Paper: (11.1.2.7), p. 480. At the identity idele the outside unit factor
is one.
Deviation: Sanity check for extension by the outside unit factor. -/
theorem sLocalCarvingIdeleTest_one (S : Finset V) (f : ℬₛ(S)) :
    sLocalCarvingIdeleTest S f 1 = f (Multiplicative.ofAdd 1) := by sorry

/-- Paper: (11.1.2.7), p. 480. The raw theta generator sums the extended local
test over nonzero principal multiples of an idele representing the class. -/
def sLocalCarvingTheta (S : Finset V) (f : ℬₛ(S)) (g : C𝔽) : ℂ :=
  ideleThetaSum (sLocalCarvingIdeleTest S f) g.out

/-- Paper: (11.1.2.7), p. 480. At any representative of the class the displayed
orbit series is absolutely convergent and gives the raw theta generator. -/
theorem sLocalCarvingTheta_spec (S : Finset V) (f : ℬₛ(S)) (g : I𝔽) :
    Summable (fun ξ : Fˣ ↦ sLocalCarvingIdeleTest S f
      (IdeleGroup.unitEmbedding (𝓞 F) F ξ * g)) ∧
    sLocalCarvingTheta S f (classOf g) = ideleThetaSum (sLocalCarvingIdeleTest S f) g := by sorry

/-- Paper: (11.1.2.7), p. 480. At an inserted S-idele the outside unit condition
selects exactly the S-units, giving the S-local theta of Definition 2.3.1.1. -/
theorem sLocalCarvingTheta_sIdeleInsertion (S : Finset V) (f : ℬₛ(S)) (g : (SAdeleRing F S)ˣ) :
    sLocalCarvingTheta S f (classOf (sIdeleInsertion F S g)) = sLocalAdelicTheta F S f g := by sorry

/-- Paper: (11.1.2.7), p. 480. The raw theta is integrable on each norm-one
coset against a continuous norm-one character.
Deviation: This is the integrability needed for the character projection. -/
theorem integrable_sLocalCarvingTheta_normOne (S : Finset V) (ω : PontryaginDual C₁)
    (f : ℬₛ(S)) (g : C𝔽) :
    Integrable (fun h : C₁ ↦ sLocalCarvingTheta S f (h.val * g) * (ω h : ℂ)) μ₁ := by sorry

/-- Paper: (11.1.2.7), p. 480. Average the raw theta generator against the
norm-one character and then apply the cutoff.
Deviation: The norm-one average places the generator in the claimed isotype. -/
def sLocalCarvingGenerator (S : Finset V) (ω : PontryaginDual C₁)
    (J : Set ℝ) (f : ℬₛ(S)) : C𝔽 → ℂ :=
  (norm𝔽 ⁻¹' J).indicator (fun g ↦ ∫ h : C₁,
    sLocalCarvingTheta S f (h.val * g) * (ω h : ℂ) ∂μ₁)

/-- Paper: (11.1.2.7), p. 480. For the trivial norm-one character the average
of a norm-one-invariant generator multiplies its cutoff by the Haar mass.
Deviation: Sanity check for the character average in the repaired generator. -/
theorem sLocalCarvingGenerator_trivial (S : Finset V) (J : Set ℝ) (f : ℬₛ(S))
    (_hf : ∀ (h : C₁) (g : C𝔽), sLocalCarvingTheta S f (h.val * g) = sLocalCarvingTheta S f g) :
    sLocalCarvingGenerator S 1 J f =
      fun g ↦ (μ₁).real univ • (norm𝔽 ⁻¹' J).indicator (sLocalCarvingTheta S f) g := by sorry

/-- Paper: Theorem 11.1.2.1(3), p. 480. The projected cutoff generators are
square-integrable for the zero-line weight. -/
theorem memLp_sLocalCarvingGenerator {S : Finset V} (χ : PontryaginDual C𝔽)
    (_hχ : Unramified(χ, S)) (_hPic : TrivialPic((S : Set V)))
    (s : ℝ) (_hs : DegreeBound(s)) (twoSided : Bool) (Λ : ℝ) (_hΛ : 0 < Λ)
    (f : ℬₛ(S)) (_hf : f (Multiplicative.ofAdd 0) = 0)
    (_hFf : sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) = 0) :
    MemLp (sLocalCarvingGenerator S (ωOf(χ)) (J(twoSided, Λ)) f) 2 (ν(s)) := by sorry

-- TODO(paper-gap): Page 483 uses R_{Λ,S} without defining it. Both spans in
-- the quotient already have Fourier value zero. The argument still needs to
-- approximate every vector of the intersection by projected local generators.

/-- Paper: Theorem 11.1.2.1(3), p. 480. The cofinal limit is the closed span of
the projected cutoff theta functions of local tests whose value and Fourier value
at zero vanish.
Deviation: Use the norm-one character average in (11.1.2.7). The closure is
taken in the full weighted L² space, where the cutoff isotype is closed. -/
theorem sLocalCarvingLimit_eq_closedSpan {S : Finset V} (χ : PontryaginDual C𝔽)
    (hχ : Unramified(χ, S)) (hPic : TrivialPic((S : Set V)))
    (s : ℝ) (hs : DegreeBound(s)) (twoSided : Bool) (Λ : ℝ) (hΛ : 0 < Λ) :
    sLocalCarvingLimit s (ωOf(χ)) S (J(twoSided, Λ)) (hJ(twoSided, Λ)) = (Submodule.span ℂ {u : W(s) |
      ∃ (f : ℬₛ(S)) (hf : f (Multiplicative.ofAdd 0) = 0)
        (hFf : sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) = 0),
        u = (memLp_sLocalCarvingGenerator χ hχ hPic s hs twoSided Λ hΛ f hf hFf).toLp
          (sLocalCarvingGenerator S (ωOf(χ)) (J(twoSided, Λ)) f)}).topologicalClosure := by sorry

/-- Paper: (11.1.2.8)–(11.1.2.9), p. 481. The cutoff norm is the weighted
L² norm restricted to the idelic norm band.
Deviation: For the two-sided cutoff the integral is over the bounded band. -/
theorem sLocalCarving_cutoff_norm (s : ℝ) (twoSided : Bool) (Λ : ℝ) (u : W(s)) :
    let E := norm𝔽 ⁻¹' J(twoSided, Λ)
    let integrand := fun g : C𝔽 ↦ ‖u g‖ ^ 2 * (1 + Real.log (norm𝔽 g) ^ 2) ^ (s / 2)
    IntegrableOn integrand E μ𝔽 ∧
      ‖M(s, J(twoSided, Λ), hJ(twoSided, Λ)) u‖ =
        Real.sqrt (∫ g in E, integrand g ∂μ𝔽) := by sorry

/-- Paper: (11.1.2.10)–(11.1.2.11), p. 481. The image under the cutoff of the
completed uncut stage lies in the cutoff stage, and its closure is the cutoff stage.
Deviation: The equality takes the closure of the image of the completed stage.
The argument in print establishes density there. -/
theorem sLocalCutoffCarving_eq_closure_map (s : ℝ) (ω : PontryaginDual C₁)
    (T : Finset V) (J : Set ℝ) (hJ : MeasurableSet J) :
    sLocalCutoffCarving s ω T J hJ =
      ((sLocalUncutCarving s ω T).map (M(s, J, hJ)).toLinearMap).topologicalClosure := by sorry

-- TODO(paper-gap): For (11.1.2.11), closed range of the cutoff on the ambient space
-- does not establish closed range on each completed uncut stage.

end RiemannMasullo
