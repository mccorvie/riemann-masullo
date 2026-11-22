module

public import RiemannMasullo.Ch02_AdelicTheta.Sec2b

/-!
# General convergence criteria for adelic theta

Masullo, §11.1.1, pp. 475–479. The limit functions are defined on ideles and
need not be Schwartz–Bruhat functions.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NNReal NumberField.AdeleRing nonZeroDivisors

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "N[" F "]" => MonoidHom.ker (ideleNorm F)
local notation "C₁[" F "]" => MonoidHom.ker (ideleClassNorm F)
local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "Frac[" F "]" => FractionalIdeal (𝓞 F)⁰ F
local notation "principal" => IdeleGroup.unitEmbedding (𝓞 F) F
local notation "ideleValue" => fun (φ : ℬ[F]) (g : 𝕀[F]) ↦ φ (Multiplicative.ofAdd (Units.val g))
local notation "classOf" => QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
local notation "saturation" => fun (Z : Set 𝕀[F]) ↦ ⋃ ξ : Fˣ, (fun g ↦ principal ξ * g) '' Z

local instance instIdeleMeasurableSpaceSec1a : MeasurableSpace 𝕀[F] := borel _

/-- Paper: Lemma 11.1.1.1, p. 475. The pointwise limit of a sequence of
Schwartz–Bruhat functions restricted to the ideles is Borel measurable. -/
theorem measurable_ideleLimit (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ)
    (h : ∀ g : 𝕀[F], Tendsto (fun k ↦ ideleValue (φ k) g) atTop (𝓝 (f g))) :
    Measurable f := by sorry

/-- Paper: Proposition 11.1.1.2, p. 476. The majorant series sums over the
nonzero elements of the given fractional ideal. -/
def fractionalIdealOrbitSum (I : Frac[F]) (α : 𝕀[F] → ℝ≥0) (g : 𝕀[F]) : ℝ :=
  ∑' ξ : {ξ : Fˣ // (ξ.val : F) ∈ I}, (α (principal ξ.val * g) : ℝ)

/-- Paper: Proposition 11.1.1.2, p. 476. If exactly one term indexed by a
nonzero element of the ideal can be nonzero, the series equals that term. -/
theorem fractionalIdealOrbitSum_eq_single (I : Frac[F]) (α : 𝕀[F] → ℝ≥0) (g : 𝕀[F])
    (ξ₀ : Fˣ) (hξ₀ : (ξ₀ : F) ∈ I)
    (h : ∀ ξ : Fˣ, (ξ : F) ∈ I → ξ ≠ ξ₀ → α (principal ξ * g) = 0) :
    fractionalIdealOrbitSum I α g = (α (principal ξ₀ * g) : ℝ) := by sorry

/-- Paper: Equation (11.1.1.3), p. 476. The theta series of an idele function
sums its values at all nonzero principal multiples of the idele. -/
def ideleThetaSum (f : 𝕀[F] → ℂ) (g : 𝕀[F]) : ℂ :=
  ∑' ξ : Fˣ, f (principal ξ * g)

/-- Paper: Equation (11.1.1.3), p. 476. On Schwartz–Bruhat inputs the
idele series equals the global adelic theta function evaluated on the idele class. -/
theorem ideleThetaSum_schwartzBruhat (φ : ℬ[F]) (g : 𝕀[F]) :
    ideleThetaSum (ideleValue φ) g = adelicTheta φ (classOf g) := by sorry

/-- Paper: Proposition 11.1.1.2(2), p. 476. At each idele in the given set,
the absolute orbit-sum tails can be made small uniformly in the sequence index.
Deviation: This is an extra hypothesis for the convergence claim. -/
def HasUniformThetaTails (φ : ℕ → 𝕀[F] → ℂ) (Z : Set 𝕀[F]) : Prop :=
  ∀ g ∈ Z, ∀ ε : ℝ≥0∞, 0 < ε → ∃ s : Finset Fˣ, ∀ k,
    (∑' ξ : {ξ : Fˣ // ξ ∉ s}, ‖φ k (principal ξ.val * g)‖ₑ) < ε

/-- Paper: Proposition 11.1.1.2(2), p. 476. A constant sequence has
uniform tails exactly when its orbit series are absolutely summable.
Deviation: This checks the extra tail hypothesis. -/
theorem hasUniformThetaTails_const_iff (f : 𝕀[F] → ℂ) (Z : Set 𝕀[F]) :
    HasUniformThetaTails (fun _ ↦ f) Z ↔
      ∀ g ∈ Z, Summable (fun ξ : Fˣ ↦ ‖f (principal ξ * g)‖) := by sorry

-- TODO(paper-gap): The limit is specified on Z, but (11.1.1.3) uses all of Fˣ Z.
-- Under the ideal-series interpretation, (11.1.1.2) on the whole saturation
-- forces every test function to vanish there. At 2^n g its right side is the
-- subseries on 2^n I, which tends to zero. The nontrivial criterion below
-- imposes the bound on Z. Its norm-convergence conclusion needs control of tails.
-- The references to (11.1.1.11) on pp. 477–478 point to the next corollary.

/-- Paper: Proposition 11.1.1.2(1), p. 476. The limit has an absolutely
summable theta series at every point of the Borel set.
Deviation: The limit is taken on the saturation of the set, and the total-mass
bound is imposed on the Borel set where the majorant is defined in part (1). -/
theorem summable_ideleThetaSum_of_dominated
    (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ) (Z : Set 𝕀[F])
    (hlim : ∀ g : 𝕀[F], g ∈ saturation Z → Tendsto (fun k ↦ ideleValue (φ k) g) atTop (𝓝 (f g)))
    (hZ : MeasurableSet Z) (η : Measure 𝕀[F]) (hη : η.Regular) (r : ℝ) (hr : 1 ≤ r)
    (hmajorant : ∃ (α : 𝕀[F] → ℝ≥0) (I : Frac[F]),
        Measurable (fun g : saturation Z ↦ α g.val) ∧
        (∀ g : 𝕀[F], g ∈ Z → Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦
          (α (principal ξ.val * g) : ℝ))) ∧
        Measurable (fun g : Z ↦ fractionalIdealOrbitSum I α g.val) ∧
        MemLp (fractionalIdealOrbitSum I α) (ENNReal.ofReal r) (η.restrict Z) ∧
        ∀ g : 𝕀[F], g ∈ Z → ∀ k,
          (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤ fractionalIdealOrbitSum I α g) :
    ∀ g : 𝕀[F], g ∈ Z → Summable (fun ξ : Fˣ ↦ ‖f (principal ξ * g)‖) := by sorry

/-- Paper: Proposition 11.1.1.2(1), p. 476. Extending the limit theta
series by zero from the Borel set gives a Borel function on the ideles.
Deviation: The pointwise limit is taken on the saturation, and the
total-mass bound is imposed on the Borel set. -/
theorem measurable_indicator_ideleThetaSum_of_dominated
    (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ) (Z : Set 𝕀[F])
    (hlim : ∀ g : 𝕀[F], g ∈ saturation Z → Tendsto (fun k ↦ ideleValue (φ k) g) atTop (𝓝 (f g)))
    (hZ : MeasurableSet Z) (η : Measure 𝕀[F]) (hη : η.Regular) (r : ℝ) (hr : 1 ≤ r)
    (hmajorant : ∃ (α : 𝕀[F] → ℝ≥0) (I : Frac[F]),
        Measurable (fun g : saturation Z ↦ α g.val) ∧
        (∀ g : 𝕀[F], g ∈ Z → Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦
          (α (principal ξ.val * g) : ℝ))) ∧
        Measurable (fun g : Z ↦ fractionalIdealOrbitSum I α g.val) ∧
        MemLp (fractionalIdealOrbitSum I α) (ENNReal.ofReal r) (η.restrict Z) ∧
        ∀ g : 𝕀[F], g ∈ Z → ∀ k,
          (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤ fractionalIdealOrbitSum I α g) :
    Measurable (Z.indicator (ideleThetaSum f)) := by sorry

/-- Paper: Proposition 11.1.1.2(2), p. 476. The limit theta sum is in
the finite-exponent Lᵣ space for the measure restricted to the Borel set.
Deviation: The pointwise limit is taken on the saturation, and the
total-mass bound is imposed on the Borel set. -/
theorem memLp_ideleThetaSum_of_dominated
    (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ) (Z : Set 𝕀[F])
    (hlim : ∀ g : 𝕀[F], g ∈ saturation Z → Tendsto (fun k ↦ ideleValue (φ k) g) atTop (𝓝 (f g)))
    (hZ : MeasurableSet Z) (η : Measure 𝕀[F]) (hη : η.Regular) (r : ℝ) (hr : 1 ≤ r)
    (hmajorant : ∃ (α : 𝕀[F] → ℝ≥0) (I : Frac[F]),
        Measurable (fun g : saturation Z ↦ α g.val) ∧
        (∀ g : 𝕀[F], g ∈ Z → Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦
          (α (principal ξ.val * g) : ℝ))) ∧
        Measurable (fun g : Z ↦ fractionalIdealOrbitSum I α g.val) ∧
        MemLp (fractionalIdealOrbitSum I α) (ENNReal.ofReal r) (η.restrict Z) ∧
        ∀ g : 𝕀[F], g ∈ Z → ∀ k,
          (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤ fractionalIdealOrbitSum I α g) :
    MemLp (Z.indicator (ideleThetaSum f)) (ENNReal.ofReal r) (η.restrict Z) := by sorry

/-- Paper: Proposition 11.1.1.2(2), p. 476. Each approximating theta sum
belongs to the Lᵣ space for the restricted measure.
Deviation: The total-mass bound is imposed on the Borel set. -/
theorem memLp_adelicTheta_of_dominated
    (φ : ℕ → ℬ[F]) (Z : Set 𝕀[F])
    (hZ : MeasurableSet Z) (η : Measure 𝕀[F]) (hη : η.Regular) (r : ℝ) (hr : 1 ≤ r)
    (hmajorant : ∃ (α : 𝕀[F] → ℝ≥0) (I : Frac[F]),
        Measurable (fun g : saturation Z ↦ α g.val) ∧
        (∀ g : 𝕀[F], g ∈ Z → Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦
          (α (principal ξ.val * g) : ℝ))) ∧
        Measurable (fun g : Z ↦ fractionalIdealOrbitSum I α g.val) ∧
        MemLp (fractionalIdealOrbitSum I α) (ENNReal.ofReal r) (η.restrict Z) ∧
        ∀ g : 𝕀[F], g ∈ Z → ∀ k,
          (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤ fractionalIdealOrbitSum I α g) :
    ∀ k, MemLp (fun g ↦ adelicTheta (φ k) (classOf g))
      (ENNReal.ofReal r) (η.restrict Z) := by sorry

/-- Paper: Proposition 11.1.1.2(2), p. 476. The approximating theta
functions converge to the limit theta sum in the restricted Lᵣ norm.
Deviation: The pointwise limit is taken on the saturation, the total-mass
bound is imposed on the Borel set, and the orbit series have uniform tails. -/
theorem tendsto_eLpNorm_ideleThetaSum_of_dominated
    (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ) (Z : Set 𝕀[F])
    (hlim : ∀ g : 𝕀[F], g ∈ saturation Z → Tendsto (fun k ↦ ideleValue (φ k) g) atTop (𝓝 (f g)))
    (hZ : MeasurableSet Z) (η : Measure 𝕀[F]) (hη : η.Regular) (r : ℝ) (hr : 1 ≤ r)
    (hmajorant : ∃ (α : 𝕀[F] → ℝ≥0) (I : Frac[F]),
        Measurable (fun g : saturation Z ↦ α g.val) ∧
        (∀ g : 𝕀[F], g ∈ Z → Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦
          (α (principal ξ.val * g) : ℝ))) ∧
        Measurable (fun g : Z ↦ fractionalIdealOrbitSum I α g.val) ∧
        MemLp (fractionalIdealOrbitSum I α) (ENNReal.ofReal r) (η.restrict Z) ∧
        ∀ g : 𝕀[F], g ∈ Z → ∀ k,
          (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤ fractionalIdealOrbitSum I α g)
    (htails : HasUniformThetaTails (fun k ↦ ideleValue (φ k)) Z) :
    Tendsto (fun k ↦ eLpNorm (fun g ↦
      adelicTheta (φ k) (classOf g) - Z.indicator (ideleThetaSum f) g)
      (ENNReal.ofReal r) (η.restrict Z)) atTop (𝓝 0) := by sorry

/-- Paper: Remark 11.1.1.3, p. 476. The saturation of a Borel set under
the countable group of principal ideles is Borel. -/
theorem measurableSet_principalIdeleSaturation {Z : Set 𝕀[F]} (hZ : MeasurableSet Z) :
    MeasurableSet (saturation Z) := by sorry

section FundamentalDomain

variable (e : (ℝ≥0ˣ × N[F]) ≃ₜ* 𝕀[F])
  (he_norm : ∀ t h, ideleNorm F (e (t, h)) = t)
  (he_one : ∀ h, e (1, h) = h.val)
  (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
  (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
  (rep : CommRing.Pic (𝓞 F) → N[F])
  (hrep₁ : rep 1 = 1) (hrep : ∀ c, ideleIdealClass F (rep c).val = c)

local notation "E₁" => ideleFundamentalDomain F b v₀ σ rep
local notation "TE₁" => e '' (Set.prod (Set.univ : Set ℝ≥0ˣ) E₁)
local notation "μ₁" => normOneIdeleTamagawaMeasure F
local notation "χ" => PontryaginDual C₁[F]

-- TODO(paper-gap): In (11.1.1.8), α_g is evaluated on ξ instead of ξg.
-- The bound on the total orbit sum alone does not imply (11.1.1.10).
-- The proof's references to (11.1.1.12) and (11.1.1.13) point to the next corollary.

/-- Paper: Corollary 11.1.1.4, p. 478. The limit theta series converges
absolutely on the fundamental domain multiplied by the norm section.
Deviation: The orbit majorant is indexed by ξ, with ξ representing ξg. -/
theorem summable_ideleThetaSum_on_fundamentalDomain
    (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ)
    (hlim : ∀ g : 𝕀[F], Tendsto (fun k ↦ ideleValue (φ k) g) atTop (𝓝 (f g)))
    (hmajorant : ∀ g : 𝕀[F], ∃ (α : Fˣ → ℝ≥0) (I : Frac[F]),
      Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦ (α ξ.val : ℝ)) ∧
      (g ∈ TE₁ → ∀ k, (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤
        ∑' ξ : {ξ : Fˣ // (ξ.val : F) ∈ I}, (α ξ.val : ℝ))) :
    ∀ g ∈ TE₁, Summable (fun ξ : Fˣ ↦ ‖f (principal ξ * g)‖) := by sorry

include he_norm he_one hrep₁ hrep in
/-- Paper: Corollary 11.1.1.4, p. 478. The approximating theta functions
converge pointwise on the idele class group to the theta series of the limit.
Deviation: The orbit majorant is indexed by ξ, with ξ representing ξg.
The orbit series have uniform tails at each point of the section times the domain. -/
theorem tendsto_adelicTheta_of_dominated
    (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ)
    (hlim : ∀ g : 𝕀[F], Tendsto (fun k ↦ ideleValue (φ k) g) atTop (𝓝 (f g)))
    (hmajorant : ∀ g : 𝕀[F], ∃ (α : Fˣ → ℝ≥0) (I : Frac[F]),
      Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦ (α ξ.val : ℝ)) ∧
      (g ∈ TE₁ → ∀ k, (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤
        ∑' ξ : {ξ : Fˣ // (ξ.val : F) ∈ I}, (α ξ.val : ℝ)))
    (htails : HasUniformThetaTails (fun k ↦ ideleValue (φ k)) TE₁) :
    ∃ Θ : C[F] → ℂ, (∀ g, Θ (classOf g) = ideleThetaSum f g) ∧
      ∀ c, Tendsto (fun k ↦ adelicTheta (φ k) c) atTop (𝓝 (Θ c)) := by sorry

-- TODO(paper-gap): Relative compactness and nonempty interior do not show
-- that T ⋅ E₁ is Borel. Use the Borel property of E₁ and the splitting.
-- The citation to part (1) of Lemma A.2.2.9 has no such numbered part.
/-- Paper: Discussion preceding Corollary 11.1.1.5, p. 478. The section
times the idelic fundamental domain is Borel. -/
theorem measurableSet_normSection_fundamentalDomain : MeasurableSet TE₁ := by sorry

local notation "classOfNormOne" => fun h : N[F] ↦
  (Subtype.mk (classOf (Subtype.val h)) (Subtype.property h) : C₁[F])
local notation "weightedTheta" => fun (ω : χ) (u : 𝕀[F] → ℂ) (g : 𝕀[F]) (h : N[F]) ↦
  ideleThetaSum u (g * Subtype.val h) *
    (ω (classOfNormOne (Prod.snd (ContinuousMulEquiv.symm e (g * Subtype.val h)))) : ℂ)

/-- Paper: Equation (11.1.1.12), p. 479. The homogeneous theta average
integrates the theta series against the character evaluated at the product
of the input idele and the variable of integration.
Deviation: The character of the norm-one classes is extended trivially
on the chosen norm section. On Schwartz–Bruhat inputs this weights the
Chapter 2 homogeneous theta by the character of the input's norm-one component. -/
def homogeneousThetaSectionAverage (ω : χ) (f : 𝕀[F] → ℂ) (g : 𝕀[F]) : ℂ :=
  ∫ h in E₁, weightedTheta ω f g h ∂μ₁

include he_one hrep₁ hrep in
/-- Paper: Equation (11.1.1.12), p. 479. For each Schwartz–Bruhat input,
the section average is the character of the norm-one component times the
Chapter 2 homogeneous adelic theta.
Deviation: Equation (2.2.5.2) weights the integration variable by its
character. Equation (11.1.1.12) also includes the character of the input. -/
theorem homogeneousThetaSectionAverage_schwartzBruhat_eq_character_mul (ω : χ)
    (ψ : ℬ[F]) (g : 𝕀[F]) :
    homogeneousThetaSectionAverage e v₀ σ b rep ω (ideleValue ψ) g =
      (ω (classOfNormOne (e.symm g).2) : ℂ) *
        homogeneousAdelicTheta ω ψ (classOf g) := by sorry

include he_one hrep₁ hrep in
/-- Paper: Equation (11.1.1.12), p. 479. At an idele on the norm section,
the integral of a Schwartz–Bruhat theta series agrees with homogeneous
adelic theta from Chapter 2.
Deviation: The character is extended trivially on the norm section. -/
theorem homogeneousThetaSectionAverage_schwartzBruhat (ω : χ)
    (ψ : ℬ[F]) (t : ℝ≥0ˣ) :
    homogeneousThetaSectionAverage e v₀ σ b rep ω (ideleValue ψ) (e (t, 1)) =
      homogeneousAdelicTheta ω ψ (classOf (e (t, 1))) := by
  have h := homogeneousThetaSectionAverage_schwartzBruhat_eq_character_mul
    e he_one v₀ σ b rep hrep₁ hrep ω ψ (e (t, 1))
  rw [e.symm_apply_apply] at h
  change _ = (ω (1 : C₁[F]) : ℂ) * _ at h
  simpa using h

-- TODO(paper-gap): The claimed interchange of the limit and orbit sum
-- in the proof of (11.1.1.13) needs control of the orbit tails.

include he_norm he_one hrep₁ hrep in
/-- Paper: Corollary 11.1.1.5, p. 479. The character-weighted theta
integrand is integrable over the norm-one domain for every idele.
Deviation: The character is extended trivially on the norm section.
Slice integrability of the majorant is written by pulling it back to the domain. -/
theorem integrable_homogeneousThetaSectionAverage_of_dominated
    (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ)
    (hlim : ∀ g : 𝕀[F], Tendsto (fun k ↦ ideleValue (φ k) g) atTop (𝓝 (f g)))
    (hmajorant : ∃ (α : 𝕀[F] → ℝ≥0) (I : Frac[F]),
      Measurable α ∧
      (∀ g : 𝕀[F], Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦ (α (principal ξ.val * g) : ℝ))) ∧
      Measurable (fractionalIdealOrbitSum I α) ∧
      (∀ t, Integrable (fun h : N[F] ↦ fractionalIdealOrbitSum I α (e (t, h)))
        ((μ₁).restrict E₁)) ∧
      ∀ g : 𝕀[F], g ∈ TE₁ → ∀ k,
        (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤ fractionalIdealOrbitSum I α g) :
    ∀ (ω : χ) (g : 𝕀[F]), Integrable (weightedTheta ω f g) ((μ₁).restrict E₁) := by sorry

include he_norm he_one hrep₁ hrep in
/-- Paper: Corollary 11.1.1.5, p. 479. The limit and approximating
averages descend to the quotient by the norm-one classes and converge
pointwise there.
Deviation: The character is extended trivially on the norm section.
Slice integrability is written by pullback, and uniform orbit tails are assumed.
The functions descending to the quotient include the character factor on the input
in (11.1.1.12). The Chapter 2 approximants have inverse-character equivariance. -/
theorem tendsto_homogeneousThetaSectionAverage_of_dominated
    (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ)
    (hlim : ∀ g : 𝕀[F], Tendsto (fun k ↦ ideleValue (φ k) g) atTop (𝓝 (f g)))
    (hmajorant : ∃ (α : 𝕀[F] → ℝ≥0) (I : Frac[F]),
      Measurable α ∧
      (∀ g : 𝕀[F], Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦ (α (principal ξ.val * g) : ℝ))) ∧
      Measurable (fractionalIdealOrbitSum I α) ∧
      (∀ t, Integrable (fun h : N[F] ↦ fractionalIdealOrbitSum I α (e (t, h)))
        ((μ₁).restrict E₁)) ∧
      ∀ g : 𝕀[F], g ∈ TE₁ → ∀ k,
        (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤ fractionalIdealOrbitSum I α g)
    (htails : HasUniformThetaTails (fun k ↦ ideleValue (φ k)) TE₁) :
    ∀ ω : χ, ∃ (A : C[F] ⧸ C₁[F] → ℂ) (Aₖ : ℕ → C[F] ⧸ C₁[F] → ℂ),
      (∀ g, A (QuotientGroup.mk' _ (classOf g)) =
        homogeneousThetaSectionAverage e v₀ σ b rep ω f g) ∧
      (∀ k g, Aₖ k (QuotientGroup.mk' _ (classOf g)) =
        (ω (classOfNormOne (e.symm g).2) : ℂ) *
          homogeneousAdelicTheta ω (φ k) (classOf g)) ∧
      ∀ q, Tendsto (fun k ↦ Aₖ k q) atTop (𝓝 (A q)) := by sorry

end FundamentalDomain

end RiemannMasullo
