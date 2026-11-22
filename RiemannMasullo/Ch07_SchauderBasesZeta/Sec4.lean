module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b
public import RiemannMasullo.Ch06_LocalGlobal.Sec3
public import RiemannMasullo.AppC_LCTVS.Sec3a

import all RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3b

import all RiemannMasullo.AppA_AlgebraicNT.Sec3

/-! # §7.4 Nuclearity

The spectral quotient is in Schwartz–Bergman coordinates. The orbital quotients
use the quotient topology of the zero-moment homogeneous theta space.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal NumberField.AdeleRing TensorProduct

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 150000
set_option Elab.async false

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "ω(" χ ")" => (χ : U).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* C𝔽)
local notation "P" => adelePolarSubspace F
local notation "B" => SchwartzBergman (univ : Set ℝ)
local notation "Entire" => entireContinuousMapSubalgebra

local instance instIdeleClassT2Sec4 : T2Space C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1

local instance instIdeleClassLocallyCompactSec4 : LocallyCompactSpace C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1

local instance instIdeleClassMeasurableSec4 (F : Type*) [Field F] [NumberField F] :
    MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _
local instance instNuclearitySecondCountable : SecondCountableTopology C𝔽 :=
  letI := idele_secondCountable F
  inferInstanceAs (SecondCountableTopology
    (IdeleGroup (𝓞 F) F ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))

local notation "𝒟" => BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "Π(" χ ")" => LinearMap.ker ((homogeneousAdelicThetaLinearMap F (ω(χ))).domRestrict P)
local notation "Θ₀(" χ ")" => ↥P ⧸ Π(χ)
local notation "mkΘ(" χ ", " f ")" => (Submodule.Quotient.mk f : Θ₀(χ))
local notation "Z(" χ ", " τ ", " hτ ")" => (exists_globalPolarThetaMellin χ τ hτ).choose
local notation "testIntegrand(" χ ", " φ ", " s ")" =>
  (fun g : C𝔽 ↦ (φ : 𝒟).val g * (ideleClassNormTwist χ s) g)

/-- Paper: Equation (7.4.1.1), p. 366.
The class-group Mellin transform of a Bruhat test uses the norm twist of the given character
and the idèle-class Tamagawa measure. -/
def nuclearityTestMellin (χ : U) (φ : 𝒟) (s : ℂ) : ℂ :=
  ∫ g, testIntegrand(χ, φ, s) g ∂μ𝔽

/-- Paper: Equation (7.4.1.1), p. 366.
The test integral converges absolutely throughout the norm chart.
At the trivial quasi-character it gives the integral of the test. -/
theorem nuclearityTestMellin_integrable (χ : U) (φ : 𝒟) :
    (∀ s : ℂ, Integrable (testIntegrand(χ, φ, s)) μ𝔽) ∧
      nuclearityTestMellin 1 φ 0 = ∫ g, φ.val g ∂μ𝔽 := by
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : (ideleClassTamagawaMeasure F).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have hc : Continuous φ.val :=
    continuous_schwartzBruhat (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  constructor
  · intro s
    exact (hc.mul (ideleClassNormTwist χ s).continuous).integrable_of_hasCompactSupport
      (show HasCompactSupport φ.val from φ.property.2).mul_right
  · apply integral_congr_ae
    filter_upwards with g
    change φ.val g * (1 * _ ^ (0 : ℂ)) = φ.val g
    simp

/-- Paper: Theorem 7.4.1.1(2), pp. 366–367.
An operator of order zero admits a nuclear presentation with rapidly decreasing
coefficients. The presentation includes equicontinuity and a common Banach disc. -/
def IsStronglyNuclearOperator {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    (A : E →L[ℂ] E) : Prop :=
  ∃ r : NuclearPresentation A, ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
    ‖r.coeff n‖ * ((n : ℝ) + 1) ^ k ≤ C

/-- Paper: Theorem 7.4.1.1(2), pp. 366–367.
Every continuous rank-one operator is of order zero. -/
theorem isStronglyNuclearOperator_rankOne {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E]
    (ℓ : StrongDual ℂ E) (x : E) : IsStronglyNuclearOperator (ℓ.smulRight x) := by
  obtain ⟨r, hr, _, _, htail⟩ := nuclearPresentation_smulRight ℓ x 1 one_ne_zero
  refine ⟨r, fun k ↦ ⟨1, ?_⟩⟩
  intro n
  cases n with
  | zero => simp [hr]
  | succ n => simp [htail n]

section Spectral

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))

local notation "Λ(" χ ", " τ ", " hτ ")" => regularizedCompletedHeckeL χ τ hτ
  (continuedCompletedHeckeL χ) (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2

/-- Paper: Equation (7.4.0.1), p. 366.
In Mellin coordinates the norm-power twist shifts the regularized completed generator
by translation of the argument by a. The shifted generator is entire. -/
theorem spectralNuclearityGenerator_differentiable (a : ℝ) :
    Differentiable ℂ (fun s ↦ (Λ(χ, τ, hτ)).val (s + (a : ℂ))) := by
  exact (Λ(χ, τ, hτ)).property.comp (differentiable_id.add_const (a : ℂ))

/-- Paper: Equation (7.4.0.1), p. 366.
The denominator is the shifted theta image in the Schwartz–Bergman model of the
exponentially decaying isotype. -/
def spectralNuclearityDenominator (a : ℝ) : Submodule ℂ B :=
  let h := spectralNuclearityGenerator_differentiable χ τ hτ a
  schwartzBergmanDivisible ⟨⟨_, h.continuous⟩, h⟩

/-- Paper: Equation (7.4.0.1), p. 366.
This is the spectral quotient with its quotient topology, in Mellin coordinates. -/
abbrev SpectralNuclearityQuotient (a : ℝ) := B ⧸ spectralNuclearityDenominator χ τ hτ a

/-- Paper: Equation (7.4.0.1), p. 366.
The unshifted denominator is precisely the image of the pole-free theta Mellin map. -/
theorem spectralNuclearityDenominator_zero :
    spectralNuclearityDenominator χ τ hτ 0 = (Z(χ, τ, hτ)).toLinearMap.range := by sorry

/-- Paper: Equation (7.4.0.1), p. 366.
The denominator consists precisely of the Mellin transforms of norm-twisted theta classes. -/
theorem mem_spectralNuclearityDenominator_iff (a : ℝ) (f : B) :
    f ∈ spectralNuclearityDenominator χ τ hτ a ↔
      ∃ x : Θ₀(χ), ∀ s : ℂ, f.val s = ((Z(χ, τ, hτ)) x).val (s + (a : ℂ)) := by sorry

/-- Paper: Equation (7.4.0.1), p. 366.
The section Mellin transform identifies the decay isotype with the full
Schwartz–Bergman space and takes the norm-twisted theta image to the denominator.
The section integral uses the quotient Haar measure dt/t of §3.2. -/
theorem spectralNuclearityDenominator_isotypeModel (a : ℝ) :
    let m : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
    let E := modulatedDecayIsotype m (Set.univ : Set ℝ) (Set.mem_univ 0) (ω(χ))
    ∃ M : ↥E ≃L[ℂ] B,
      (∀ (u : E) s, (M u).val s = ∫ t : ℝ≥0ˣ,
        u.val.val (QuotientGroup.mk (τ t)) *
          ideleClassNormTwist χ s (QuotientGroup.mk (τ t)) ∂positiveRealHaar) ∧
      ∀ u : E, M u ∈ spectralNuclearityDenominator χ τ hτ a ↔
        ∃ f : P, ∀ g : C𝔽, u.val.val g =
          ((((ideleClassNorm F g).val : ℝ) ^ a : ℝ) : ℂ) *
            homogeneousAdelicTheta (ω(χ)) f.val g := by sorry

/-- Paper: Theorem 7.4.1.1(1), p. 366.
The twisted theta image is closed. Compactly supported Bruhat tests act by continuous
Mellin multiplication, which preserves that image. -/
theorem spectralNuclearityDenominator_closed_invariant (a : ℝ) (φ : 𝒟) :
    let D := spectralNuclearityDenominator χ τ hτ a
    IsClosed (D : Set B) ∧
      ∃ A : B →L[ℂ] B,
        (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) ∧
        Set.MapsTo A (D : Set B) D := by sorry

local notation "zeros(" χ ", " τ ", " hτ ")" =>
  {z : ℂ // 0 < analyticOrderAt ((Λ(χ, τ, hτ)).val : ℂ → ℂ) z}
local notation "multiplicity(" χ ", " τ ", " hτ ", " z ")" =>
  (analyticOrderAt ((Λ(χ, τ, hτ)).val : ℂ → ℂ) (z : ℂ)).toNat
local notation "jets(" χ ", " τ ", " hτ ")" =>
  Σ z : zeros(χ, τ, hτ), Fin (multiplicity(χ, τ, hτ, z))
local notation "Q(" a ")" => SpectralNuclearityQuotient χ τ hτ a
local notation "D(" a ")" => spectralNuclearityDenominator χ τ hτ a

open Classical in
/-- Paper: Theorem 7.4.1.1(2), p. 366, using Theorem 7.1.4.2(3).
The jet functionals and their full biorthogonal families transport to the shifted
quotient. A zero z of the unshifted generator has its jets at z − a. -/
theorem exists_spectralNuclearityBiorthogonal (a : ℝ) :
    ∃ (d : jets(χ, τ, hτ) → StrongDual ℂ (Q(a))) (b : jets(χ, τ, hτ) → Q(a)),
      (∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ))) ∧
      ∀ i j, d i (b j) = if i = j then 1 else 0 := by sorry

-- TODO(paper-gap): The proof on p. 367 gives no uniform boundedness estimate for
-- the rescaled biorthogonal vectors. Discreteness does not control zero counts,
-- enumeration order, or separation. It also does not imply N(z)! = O(|Im z|).

open Classical in
/-- Paper: Theorem 7.4.1.1(2), pp. 366–367.
Compactly supported tests act on the quotient determined by the first N derivatives
in each block. Every nuclear presentation of the order-zero action has the stated trace.
Deviation: The printed span of the first N primal vectors can fail to be invariant.
Quotient by the common kernel of the retained derivative functionals. The multiplier
is evaluated at z − a for each unshifted zero z. -/
theorem spectralNuclearity_trace (a : ℝ) (N : ℕ) (_hN : 0 < N) (φ : 𝒟)
    (d : jets(χ, τ, hτ) → StrongDual ℂ (Q(a)))
    (_hd : ∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ))) :
    let K := ⨅ i : {i : jets(χ, τ, hτ) // i.2.val < N}, (d i.val).toLinearMap.ker
    let E := Q(a) ⧸ K
    letI instSpectralUniformSec4 : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    let term := fun z : zeros(χ, τ, hτ) ↦
      ((min N (multiplicity(χ, τ, hτ, z)) : ℕ) : ℂ) * nuclearityTestMellin χ φ (z.val - (a : ℂ))
    ∃ (A : B →L[ℂ] B) (T : E →L[ℂ] E),
      (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) ∧
      (∃ Aq : Q(a) →L[ℂ] Q(a),
        (∀ f, Aq ((D(a)).mkQ f) = (D(a)).mkQ (A f)) ∧
        ∀ x : Q(a), T (K.mkQ x) = K.mkQ (Aq x)) ∧
      IsStronglyNuclearOperator T ∧ Summable (fun z ↦ ‖term z‖) ∧
      ∀ r : NuclearPresentation T,
        HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n).val) (∑' z, term z) := by sorry

end Spectral

section Orbital

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))

/-- Paper: Theorem 7.4.2.1(1)–(2), p. 367, and Theorem 7.4.3.2, pp. 372–373.
In global Mellin coordinates the regularized theta action is multiplication by
the transform of the test. The induced map on theta functions is Haar convolution. -/
theorem exists_polarThetaNuclearityAction (φ : 𝒟) :
    ∃ A : Θ₀(χ) →L[ℂ] Θ₀(χ),
      (∀ f s, ((Z(χ, τ, hτ)) (A f)).val s =
        nuclearityTestMellin χ φ s * ((Z(χ, τ, hτ)) f).val s) ∧
      ∀ f g : P, A mkΘ(χ, f) = mkΘ(χ, g) ↔
        (homogeneousAdelicTheta (ω(χ)) g.val : C𝔽 → ℂ) =
          lcaConvolution μ𝔽 φ.val (homogeneousAdelicTheta (ω(χ)) f.val) := by sorry

local notation "Aθ(" φ ")" => (exists_polarThetaNuclearityAction χ τ hτ φ).choose

/-- Paper: Equation (7.4.0.2), p. 366.
The finite places of a number field lying above one rational prime form a finite set. -/
theorem finite_nuclearityPlacesAbove (p : HeightOneSpectrum (𝓞 ℚ)) :
    {v : V | v.under (𝓞 ℚ) = p}.Finite := by
  apply Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
    (hi := HeightOneSpectrum.asIdeal_injective.injOn)
  apply (IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 F)).subset
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal (show w.under (𝓞 ℚ) = p from hw).symm⟩⟩

local notation "Sₚ(" p ")" => (finite_nuclearityPlacesAbove (F := F) p).toFinset

/-- Paper: Equation (7.4.0.2), p. 366.
Principal value preserves the common kernel of the two global polar evaluations. -/
theorem nuclearityPrincipalValue_mem_polar (p : HeightOneSpectrum (𝓞 ℚ)) (f : P) :
    adelePrincipalValue F (Sₚ(p)) f.val ∈ P := by sorry

/-- Paper: Equation (7.4.0.2), p. 366.
The finite-place denominator is the theta image of principal values of zero-moment
tests, with the principal value taken at all places above the rational prime. -/
def finiteNuclearityDenominator (p : HeightOneSpectrum (𝓞 ℚ)) : Submodule ℂ (Θ₀(χ)) :=
  Submodule.span ℂ (Set.range (fun f : P ↦
    (Submodule.Quotient.mk ⟨adelePrincipalValue F (Sₚ(p)) f.val,
      nuclearityPrincipalValue_mem_polar (F := F) p f⟩ : Θ₀(χ))))

/-- Paper: Equation (7.4.0.2), p. 366.
The finite orbital quotient is taken by the principal-value image. -/
abbrev FiniteNuclearityQuotient (p : HeightOneSpectrum (𝓞 ℚ)) :=
  Θ₀(χ) ⧸ finiteNuclearityDenominator χ p

/-- Paper: Equation (7.4.0.2), p. 366.
The class of a test is zero in the finite quotient exactly when its theta class
is represented by a principal value. -/
theorem finiteNuclearityQuotient_mk_eq_zero (p : HeightOneSpectrum (𝓞 ℚ)) (f : P) :
    (finiteNuclearityDenominator χ p).mkQ mkΘ(χ, f) = 0 ↔
      ∃ g : P, mkΘ(χ, f) =
        mkΘ(χ, ⟨adelePrincipalValue F (Sₚ(p)) g.val, nuclearityPrincipalValue_mem_polar (F := F) p g⟩) :=
  by sorry

/-- Paper: Theorem 7.4.2.1(1), p. 367.
The finite-place denominator is closed and is stable under each regularized action. -/
theorem finiteNuclearityDenominator_closed_invariant (p : HeightOneSpectrum (𝓞 ℚ)) (φ : 𝒟) :
    let D := finiteNuclearityDenominator χ p
    IsClosed (D : Set (Θ₀(χ))) ∧ Set.MapsTo (Aθ(φ)) (D : Set (Θ₀(χ))) D := by sorry

-- TODO(paper-gap): The cited §7.1.4.3 concerns the entire comparison space.
-- To apply the rapid-decay argument on this quotient, one needs bounds in its
-- own topology for the functionals and the biorthogonal vectors.

/-- Paper: Theorem 7.4.2.1(2), p. 367.
The operator induced on the finite orbital quotient is of order zero. Its trace sums
the test Mellin transform over the zeros of the reciprocal partial Euler product,
counting collisions with their full order. -/
theorem finiteNuclearity_trace (p : HeightOneSpectrum (𝓞 ℚ)) (φ : 𝒟) :
    let D := finiteNuclearityDenominator χ p
    let Q := Θ₀(χ) ⧸ D
    letI instFiniteUniformSec4 : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
    let R := reciprocalPartialHeckeEulerProduct χ (Sₚ(p))
    let zeros := {z : ℂ // 0 < analyticOrderAt R z}
    let term := fun z : zeros ↦
      ((analyticOrderAt R z.val).toNat : ℂ) * nuclearityTestMellin χ φ z.val
    ∃ T : Q →L[ℂ] Q,
      (∀ f : Θ₀(χ), T (D.mkQ f) = D.mkQ (Aθ(φ) f)) ∧
      IsStronglyNuclearOperator T ∧ Summable (fun z ↦ ‖term z‖) ∧
      ∀ r : NuclearPresentation T,
        HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n).val) (∑' z, term z) := by sorry

end Orbital

section Archimedean

open Classical

local notation "RealPlaces" => {v : InfinitePlace F // v.IsReal}
local notation "ComplexPlaces" => {v : InfinitePlace F // v.IsComplex}
local notation "Coordinates" => (RealPlaces → ℝ) × (ComplexPlaces → ℂ)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)

variable (F) in
/-- Paper: Equation (7.4.3.1), p. 368.
Finite sums of adelic tensors have flat archimedean factors and arbitrary finite
factors. When required, each archimedean factor has additive integral zero.
Deviation: Uses the adelic tensor realization of §2.1.3 and the flat jet
conditions from §5.3.3. The tensor image carries the subspace topology from the
adelic Schwartz space. The display on p. 368 writes the projective tensor topology. -/
def globalArchimedeanFlatTests (requireArchMoment : Prop := False) : Submodule ℂ ℬ(𝔸[F]) :=
  let coordinates (x : InfiniteAdeleRing F) : Coordinates :=
    (fun v ↦ InfinitePlace.Completion.ringEquivRealOfIsReal v.property (x v.val),
      fun v ↦ InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property (x v.val))
  let tensor := (adeleSchwartz_inductiveTensor_equiv F).choose
  Submodule.span ℂ {test | ∃ (f : ℬ(InfiniteAdeleRing F))
    (g : ℬ(FiniteAdeleRing (𝓞 F) F))
    (h : archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)),
    (∀ x : InfiniteAdeleRing F, f (Multiplicative.ofAdd x) = h.val (coordinates x)) ∧
      (requireArchMoment → (∫ u : Coordinates, h.val u) = 0) ∧
      tensor (f ⊗ₜ[ℂ] g) = test}

variable (F) in
/-- Paper: Equation (7.4.3.1), p. 368.
The archimedean-flat tensor image is closed in the adelic Schwartz topology,
including when the archimedean integral of each tensor factor must vanish. -/
theorem globalArchimedeanFlatTests_isClosed (requireArchMoment : Prop) :
    IsClosed (globalArchimedeanFlatTests F requireArchMoment : Set ℬ(𝔸[F])) := by sorry

/-- Paper: Equation (7.4.3.1), p. 368.
Archimedean flatness kills evaluation at the adelic origin. Within the flat space,
the other zero-moment condition is the vanishing of the Fourier value at the origin. -/
theorem globalArchimedeanFlatTests_zero_moments (f : ℬ(𝔸[F]))
    (_hf : f ∈ globalArchimedeanFlatTests F) :
    f (Multiplicative.ofAdd 0) = 0 ∧
      (f ∈ adelePolarSubspace F ↔ adeleSchwartzFourier (F := F) f (Multiplicative.ofAdd 0) = 0) := by sorry

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))

/-- Paper: Equation (7.4.3.1), p. 368.
The denominator uses archimedean-flat factors. On the trivial norm-one component
each factor has zero additive integral, equivalently zero local Fourier value at zero.
Deviation: Implements the prose Fourier-moment condition. On a nontrivial norm-one
isotype the moment restriction can be imposed on representatives, since the two
polar functionals are trivial-isotypic. -/
def archNuclearityDenominator : Submodule ℂ (Θ₀(χ)) :=
  Submodule.span ℂ {x : Θ₀(χ) | ∃ f : P,
    f.val ∈ globalArchimedeanFlatTests F (ω(χ) = 1) ∧ x = Submodule.Quotient.mk f}

/-- Paper: Equations (7.4.3.1) and (7.4.3.12), pp. 368 and 371.
In the homogeneous theta image the factorwise moment condition agrees with
imposing the two global polar conditions on the unrestricted flat tensors. -/
theorem mem_archNuclearityDenominator_iff_flatPolarImage (x : Θ₀(χ)) :
    x ∈ archNuclearityDenominator χ ↔
      ∃ f : P, f.val ∈ globalArchimedeanFlatTests F ∧ x = mkΘ(χ, f) := by sorry

/-- Paper: Equation (7.4.3.13), p. 372.
The archimedean orbital quotient divides the zero-moment theta space by its flat image. -/
abbrev ArchNuclearityQuotient := Θ₀(χ) ⧸ archNuclearityDenominator χ

/-- Paper: Equation (7.4.3.13), p. 372.
A test represents zero in the archimedean quotient exactly when its theta class
has an archimedean-flat zero-moment representative. -/
theorem archNuclearityQuotient_mk_eq_zero (f : P) :
    (archNuclearityDenominator χ).mkQ mkΘ(χ, f) = 0 ↔
      ∃ g : P, g.val ∈ globalArchimedeanFlatTests F (ω(χ) = 1) ∧ mkΘ(χ, g) = mkΘ(χ, f) := by sorry

-- The finite factors of (7.4.3.6) on p. 369 also carry their integer-unit
-- Tamagawa masses. A positive archimedean bump on the trivial isotype needs a
-- difference of dilates to give zero additive integral.

/-- Paper: Theorem 7.4.3.1(1), p. 368.
The zero-moment archimedean-flat theta image is nonzero and closed.
Deviation: Uses the Fourier-moment correction from the prose after (7.4.3.1).
Without it the printed image need not be contained in the zero-moment theta space. -/
theorem archNuclearityDenominator_nonzero_closed :
    archNuclearityDenominator χ ≠ ⊥ ∧
      IsClosed (archNuclearityDenominator χ : Set (Θ₀(χ))) := by sorry

local notation "gammaOrder(" χ ", " s ")" =>
  (analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) s).toNat
local notation "atZeroPole(" χ ", " τ ", " hτ ")" =>
  (-(((existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose : ℝ) : ℂ) * Complex.I)

/-- Paper: Equations (7.4.3.2)–(7.4.3.3), p. 368.
In the fixed norm chart the archimedean pole set is the zero set of the reciprocal gamma
product. The pole set in that chart is discrete and closed. -/
theorem archNuclearityPoleSet_discrete :
    let S := {s : ℂ | 0 < gammaOrder(χ, s)}
    IsClosed S ∧ IsDiscrete S := by sorry

/-- Paper: Equations (7.4.3.2)–(7.4.3.3), p. 368.
The raw order in the global chart counts the same places as the local
multiplicity of Proposition 5.3.4.5 for the restricted character. -/
theorem archNuclearityGammaOrder_eq_sLocal (S : Finset V)
    (η : PontryaginDual (SIdeleQuotient F S))
    (h : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (_hη : sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, h⟩ =
      (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η) (s : ℂ) :
    gammaOrder(χ, s) = sLocalArchimedeanPoleMultiplicity η s := by sorry

/-- Paper: Theorem 7.4.3.1(2), p. 368.
The raw total pole order is reduced by one at the trivial quasi-character,
when it lies on the chosen component.
Deviation: Page 368 names the quasi-character |·|^(it₀). The chart parameter it₀
corresponds to the trivial quasi-character when χ = |·|^(−it₀). -/
def archNuclearityMultiplicity (s : ℂ) : ℕ :=
  gammaOrder(χ, s) - if ω(χ) = 1 ∧ s = atZeroPole(χ, τ, hτ) then 1 else 0

/-- Paper: Theorem 7.4.3.1(2), p. 368.
For the trivial rational character, the adjusted order at zero vanishes and the
simple gamma pole at minus two remains. -/
theorem archNuclearityMultiplicity_rat_one
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 ℚ) ℚ) (hτ : RightInverse τ (ideleNorm ℚ)) :
    archNuclearityMultiplicity (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) τ hτ 0 = 0 ∧
      archNuclearityMultiplicity (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) τ hτ (-2) = 1 :=
  by sorry

/-- Paper: Theorem 7.4.3.1(2), p. 368.
Each pole contributes derivative indices from zero up to its adjusted order. -/
abbrev ArchNuclearityJetIndex := {j : ℂ × ℕ // j.2 < archNuclearityMultiplicity χ τ hτ j.1}

/-- Paper: Equation (7.4.3.4), p. 368.
The orbital jet applies a continuous entire derivative to the Mellin transform of
a zero-moment theta class. -/
def archNuclearityJet (j : ArchNuclearityJetIndex χ τ hτ) : StrongDual ℂ (Θ₀(χ)) :=
  ((entireJet j.val.1 j.val.2).comp schwartzBergmanEntireInclusion).comp (Z(χ, τ, hτ))

/-- Paper: Equation (7.4.3.4), p. 368.
On a representative the orbital jet is the derivative of the idelic zeta integral.
Its inverse Mellin formula is the convergent logarithmic moment.
Deviation: Uses the normalized inverse Mellin transform, including the missing
factor 1/(2πi) in the printed vertical integral. -/
theorem archNuclearityJet_apply (j : ArchNuclearityJetIndex χ τ hτ) (f : P) :
    let u : ℂ → ℂ := ((Z(χ, τ, hτ)) mkΘ(χ, f)).val
    let moment := fun t : ℝ ↦ (Real.log t : ℂ) ^ j.val.2 * mellinInv 0 u t
    Complex.VerticalIntegrable u 0 ∧ MellinConvergent moment j.val.1.re ∧
      archNuclearityJet χ τ hτ j mkΘ(χ, f) =
        iteratedDeriv j.val.2 (fun s ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ s)) j.val.1 ∧
      archNuclearityJet χ τ hτ j mkΘ(χ, f) = mellin moment j.val.1 := by sorry

/-- Paper: Theorem 7.4.3.1(2), p. 368.
The closure of the linear span of the jets in the strong dual is the annihilator
of the archimedean-flat image. -/
theorem archNuclearityJet_span :
    ((Submodule.span ℂ (Set.range (archNuclearityJet χ τ hτ))).topologicalClosure :
        Set (StrongDual ℂ (Θ₀(χ)))) =
      {ℓ | ∀ x : archNuclearityDenominator χ, ℓ x.val = 0} := by sorry

/-- Paper: Theorem 7.4.3.1(3), p. 368.
Every enumeration of the adjusted jets gives a Schauder basis on the quotient strong
dual. Pullback along the quotient map recovers the original jets. -/
theorem archNuclearityJet_basis :
    let Q := ArchNuclearityQuotient χ
    let J := ArchNuclearityJetIndex χ τ hτ
    Nonempty (ℕ ≃ J) ∧
      ∀ σ : ℕ ≃ J, ∃ (d : ℕ → StrongDual ℂ Q) (b : ℕ → StrongDual ℂ (StrongDual ℂ Q)),
        (∀ n x, d n ((archNuclearityDenominator χ).mkQ x) = archNuclearityJet χ τ hτ (σ n) x) ∧
        IsSchauderBasis d b := by sorry

local notation "finiteL(" χ ")" => (finiteHeckeL_exists_continuation χ).choose
local notation "poleFactor(" χ ", " τ ", " hτ ", " s ")" =>
  ((s : ℂ) - 1 - atZeroPole(χ, τ, hτ)) ^ (if ω(χ) = 1 then (1 : ℕ) else 0)

/-- Paper: Equation (7.4.3.5), p. 368.
After cancellation of the pole on the trivial norm-one component, the continued
finite Hecke function is entire. -/
theorem archRegularizedFiniteHeckeL_differentiable :
    Differentiable ℂ (toMeromorphicNFOn
      (fun s ↦ poleFactor(χ, τ, hτ, s) * finiteL(χ) s) univ) := by sorry

/-- Paper: Equation (7.4.3.5), p. 368.
The generator of the archimedean ideal is the pole-removed finite Hecke function.
Normal form supplies the removable value at its canceled pole. -/
def archRegularizedFiniteHeckeL : Entire :=
  let h := archRegularizedFiniteHeckeL_differentiable χ τ hτ
  ⟨⟨_, h.continuous⟩, h⟩

/-- Paper: Equation (7.4.3.5), p. 368.
On the half-plane of absolute convergence the generator equals the Euler product
times the pole-removing factor. -/
theorem archRegularizedFiniteHeckeL_apply (s : {s : ℂ // 1 < s.re}) :
    (archRegularizedFiniteHeckeL χ τ hτ).val s.val =
      poleFactor(χ, τ, hτ, s.val) * finiteHeckeL χ s := by sorry

-- TODO(paper-gap): Before (7.4.3.12) on p. 371, not every numerator class
-- comes from a flat test. For ℚ, S = {∞}, χ = 1, finite PV is the identity.
-- The real Gaussian combination in Printed.archNuclearityJet_apply_false has
-- nonzero global Z(-2), whereas a flat real test times the finite integer
-- indicator has Z(-2) = 0. Also, odd flat bumps have zero trivial theta class.
-- Apply §6.2 to homogeneous classes of polar tests, then identify the image
-- of the flat denominator under insertion. Uniqueness is a quotient assertion.
-- TODO(paper-gap): On p. 371, injectivity of the comparison quotient map requires
-- the range identification below. Density of the inclusion into entire functions
-- does not give that identification. Evaluations at nontrivial completed zeros
-- lie in the kernel of the printed adjoint to the theta annihilator. Pass to
-- the relative quotient of the completed ideal by the finite ideal.

/-- Paper: Theorem 7.4.3.1(4), p. 368.
The Mellin image of the flat denominator is the intersection of the entire
principal ideal generated by the regularized finite Hecke function with the
Schwartz–Bergman space. That image is closed. -/
theorem archNuclearityMellin_range :
    let D := (Z(χ, τ, hτ)) '' (archNuclearityDenominator χ : Set (Θ₀(χ)))
    D = (schwartzBergmanDivisible (archRegularizedFiniteHeckeL χ τ hτ) : Set B) ∧ IsClosed D := by sorry

/-- Paper: Equation (7.4.3.13) and the following paragraph, p. 372.
The coefficients of a quotient class are its adjusted jets, with the product topology.
The map includes simultaneous realization of every family of coefficients. -/
theorem archNuclearityQuotient_jetEquiv :
    ∃ e : ArchNuclearityQuotient χ ≃L[ℂ] (ArchNuclearityJetIndex χ τ hτ → ℂ),
      ∀ (x : Θ₀(χ)) j, e ((archNuclearityDenominator χ).mkQ x) j =
        archNuclearityJet χ τ hτ j x := by sorry

/-- Paper: Theorem 7.4.3.1(5), pp. 368–369.
The strong dual of the archimedean quotient carries the finest locally convex topology. -/
theorem archNuclearityStrongDual_finest :
    let E := StrongDual ℂ (ArchNuclearityQuotient χ)
    (inferInstance : TopologicalSpace E) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex E)) := by sorry

local notation "Aθ(" φ ")" => (exists_polarThetaNuclearityAction χ τ hτ φ).choose

/-- Paper: Theorem 7.4.3.2(1), p. 372.
The archimedean-flat theta denominator is a closed subspace stable under the
regularized action of every Bruhat test. -/
theorem archNuclearityDenominator_closed_invariant (φ : 𝒟) :
    let D := archNuclearityDenominator χ
    IsClosed (D : Set (Θ₀(χ))) ∧ Set.MapsTo (Aθ(φ)) (D : Set (Θ₀(χ))) D := by sorry

-- TODO(paper-gap): The contour identity (7.4.3.15) uses positive pole orders
-- on the right, but the logarithmic derivative has their negatives as residues.
-- Both boundary lines must avoid the poles. With χ = 1 over ℚ and a = 2,
-- the left line passes through the simple pole at -2.

/-- Paper: Theorem 7.4.3.2(2), pp. 372–373.
For tests supported where the norm is greater than one, the quotient operator has
an absolutely convergent matrix trace in every enumeration of the specified
basis of the strong dual. The gamma-pole series is also absolutely convergent.
Deviation: On a trivial norm-one isotype the omitted jet is at the trivial
quasi-character, so its weight is the integral of the test with no character factor. -/
theorem archNuclearity_trace (φ : 𝒟)
    (_hφ : tsupport φ.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)}) :
    let D := archNuclearityDenominator χ
    let Q := Θ₀(χ) ⧸ D
    let poles := {z : ℂ // 0 < gammaOrder(χ, z)}
    let term := fun z : poles ↦ (gammaOrder(χ, z.val) : ℂ) * nuclearityTestMellin χ φ z.val
    let correction := if ω(χ) = 1 then nuclearityTestMellin 1 φ 0 else 0
    ∃ T : Q →L[ℂ] Q,
      (∀ f, T (D.mkQ f) = D.mkQ (Aθ(φ) f)) ∧ Summable (fun z ↦ ‖term z‖) ∧
      ∀ (σ : ℕ ≃ ArchNuclearityJetIndex χ τ hτ) (d : ℕ → StrongDual ℂ Q)
        (b : ℕ → StrongDual ℂ (StrongDual ℂ Q)),
        (∀ n x, d n (D.mkQ x) = archNuclearityJet χ τ hτ (σ n) x) →
        IsSchauderBasis d b →
        let diagonal := fun n ↦ b n ((d n).comp T)
        Summable (fun n ↦ ‖diagonal n‖) ∧ HasSum diagonal ((∑' z, term z) - correction) := by sorry

/-- Paper: Remark 7.4.3.3, p. 373.
Nuclear endomorphisms of the strong dual of the archimedean quotient have finite rank.
Deviation: The printed universal nonnuclearity conclusion needs infinite rank,
which fails for the zero test. -/
theorem archNuclearityStrongDual_finiteRank
    (T : StrongDual ℂ (ArchNuclearityQuotient χ) →L[ℂ] StrongDual ℂ (ArchNuclearityQuotient χ))
    (_hT : Nonempty (NuclearPresentation T)) :
    FiniteDimensional ℂ T.toLinearMap.range := by sorry

/-- Paper: Remark 7.4.3.3, p. 373.
A nuclear endomorphism of the archimedean quotient has finite-dimensional range,
and every continuous finite-rank endomorphism admits a nuclear presentation.
Deviation: This gives the rank criterion on the space carrying the test action. -/
theorem archNuclearityQuotient_nuclear_iff_finiteRank :
    let Q := ArchNuclearityQuotient χ
    letI instArchUniformSec4 : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
    ∀ T : Q →L[ℂ] Q, Nonempty (NuclearPresentation T) ↔
      FiniteDimensional ℂ T.toLinearMap.range := by sorry

/-- Paper: Remark 7.4.3.3, p. 373.
The quotient action is nuclear exactly when it is nonzero on finitely many jet blocks.
Deviation: A block of length m vanishes when all multiplier derivatives of orders
strictly below m vanish at its center. This allows tests whose induced action is zero. -/
theorem archNuclearityAction_nuclear_iff (φ : 𝒟) :
    let D := archNuclearityDenominator χ
    let Q := ArchNuclearityQuotient χ
    letI instArchActionUniformSec4 : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
    ∀ T : Q →L[ℂ] Q, (∀ x : Θ₀(χ), T (D.mkQ x) = D.mkQ (Aθ(φ) x)) →
      (Nonempty (NuclearPresentation T) ↔
        {z : ℂ | ∃ k : Fin (archNuclearityMultiplicity χ τ hτ z),
          iteratedDeriv k.val (nuclearityTestMellin χ φ) z ≠ 0}.Finite) := by sorry

end Archimedean

end RiemannMasullo
