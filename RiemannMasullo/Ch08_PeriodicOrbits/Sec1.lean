module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a

/-! # §8.1 On orbital supports I

The comparison maps are induced by inclusion of the restricted tests. The asserted
isomorphisms fail even with the corrected additive test spaces. The support and stack
interpretations announced in the chapter introduction belong to §§8.2–8.3.
-/

@[expose] public noncomputable section

open Classical Function IsDedekindDomain NumberField Set
open scoped NumberField.AdeleRing TensorProduct

namespace RiemannMasullo
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option Elab.async false

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "B(" S ")" => ℬ(SAdeleRing F S)
local notation "J₁(" S ")" => (sIdeleQuotientNorm F S).ker
local notation "C₁" => (ideleClassNorm F).ker
local notation "PicTrivial(" S ")" => Subsingleton (CommRing.Pic ((S : Set V).integer F))
local notation "RealPlaces" => {w : InfinitePlace F // w.IsReal}
local notation "ComplexPlaces" => {w : InfinitePlace F // w.IsComplex}
local notation "ArchCoordinates" => ((RealPlaces → ℝ) × (ComplexPlaces → ℂ))
local notation "assemble(" x ")" =>
  (show InfiniteAdeleRing F from fun w ↦
    if hw : w.IsReal then (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm ((x).1 ⟨w, hw⟩)
    else
      let hw' := InfinitePlace.not_isReal_iff_isComplex.mp hw
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw').symm ((x).2 ⟨w, hw'⟩))

variable (F) in
/-- Paper: Equations (8.1.0.2) and (8.1.0.4), p. 382.
The common archimedean factor consists of Schwartz tests that are flat along every
archimedean coordinate hyperplane, expressed in the coordinates of §5.3.3. -/
def sLocalOrbitalArchimedeanFlatTests :
    Submodule ℂ ℬ(InfiniteAdeleRing F) :=
  let flat := (archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)).map
    ((archimedeanSchwartz_coe_isLinear (F := F)).mk' _)
  let coords := LinearMap.funLeft ℂ ℂ (fun x : ArchCoordinates ↦ Multiplicative.ofAdd (assemble(x)))
  flat.comap (coords.comp (schwartzBruhatSubmodule (Multiplicative (InfiniteAdeleRing F))).subtype)

/-- Paper: Equations (8.1.0.2) and (8.1.0.4), p. 382.
Every archimedean-flat test in the displayed tensor products vanishes at the origin. -/
theorem sLocalOrbitalArchimedeanFlatTests_zero
    (f : sLocalOrbitalArchimedeanFlatTests F) :
    f.val (Multiplicative.ofAdd 0) = 0 := by sorry

/-- Paper: Equations (8.1.0.2) and (8.1.0.4), p. 382.
These are the restricted S-adelic tests, with the fibre or singleton entered as T.
The archimedean factor is flat and every finite factor outside T vanishes at zero.
Deviation: The punctured factors are the zero extensions of compactly supported locally
constant tests on the units, as in §5.3.4 and ERRATA R11. The subspace carries the inherited
S-adelic Schwartz–Bruhat topology of §2.1.4. Even for the corrected factors, the
printed projective tensor topology can be strictly coarser (ERRATA I156). -/
def sLocalOrbitalSupportTests (S T : Finset V) : Submodule ℂ B(S) :=
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  Submodule.span ℂ {f : B(S) |
    ∃ (a : sLocalOrbitalArchimedeanFlatTests F) (b : ∀ w : S, ℬ(w.val.adicCompletion F)),
      (∀ w : S, w.val ∉ T → b w (Multiplicative.ofAdd 0) = 0) ∧
      e (a.val ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w)) = f}

variable {S T : Finset (HeightOneSpectrum (𝓞 F))}

local notation "U(" S ", " T ")" => sLocalOrbitalSupportTests (F := F) S T
local notation "Θ(" η ")" => SLocalHomogeneousThetaSpace F S η
local notation "q(" η ")" => (sLocalHomogeneousAdelicThetaLinearMap F S η).ker.mkQL
local notation "D(" hT ", " η ")" =>
  (sLocalHomogeneousThetaPrincipalValue (F := F) hT η).range

/-- Paper: Equations (8.1.0.2) and (8.1.0.4), p. 382.
For a pure tensor with nonzero factors, membership is precisely archimedean flatness
and vanishing at zero in each finite factor outside T. -/
theorem sLocalOrbitalSupportTests_tmul_iff
    (a : ℬ(InfiniteAdeleRing F)) (b : ∀ w : S, ℬ(w.val.adicCompletion F))
    (_ha : a ≠ 0) (_hb : ∀ w : S, b w ≠ 0) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, b w)) ∈ U(S, T) ↔
      a ∈ sLocalOrbitalArchimedeanFlatTests F ∧
        ∀ w : S, w.val ∉ T → b w (Multiplicative.ofAdd 0) = 0 := by sorry

/-- Paper: Theorem 8.1.0.1(1)–(2), p. 382.
The corrected test subspaces in (8.1.0.2) and (8.1.0.4) are closed in the S-adelic
Schwartz–Bruhat topology. -/
theorem sLocalOrbitalSupportTests_isClosed : IsClosed (↑U(S, T) : Set B(S)) := by sorry

/-- Paper: Equations (8.1.0.1) and (8.1.0.3), p. 382.
Principal value on the selected places preserves the restricted test space. -/
theorem sLocalOrbitalSupportTests_principalValue (hT : T ⊆ S) (f : U(S, T)) :
    sAdelePrincipalValue F hT f.val ∈ U(S, T) := by sorry

/-- Paper: Equations (8.1.0.1) and (8.1.0.3), p. 382.
The source quotient imposes the homogeneous theta kernel and the principal-value
image of the restricted tests. Its quotient topology is taken directly from those tests.
Deviation: In both source denominators the principal value acts on the same S-adelic
test space used in the numerator. -/
def sLocalOrbitalSupportRelations (hT : T ⊆ S) (η : PontryaginDual J₁(S)) :
    Submodule ℂ U(S, T) :=
  let tests : Submodule ℂ B(S) := U(S, T)
  let θ := sLocalHomogeneousAdelicThetaLinearMap F S η
  let P : B(S) →ₗ[ℂ] B(S) := sAdelePrincipalValue F hT
  let restrictedPV : tests →ₗ[ℂ] tests :=
    LinearMap.codRestrict tests (P.domRestrict tests) (fun f ↦
      sLocalOrbitalSupportTests_principalValue (F := F) hT f)
  let K : Submodule ℂ tests := (θ.domRestrict tests).ker
  K ⊔ restrictedPV.range

/-- Paper: Equations (8.1.0.1) and (8.1.0.3), p. 382.
A restricted test represents zero in the source quotient exactly when its theta class
is the principal value of the theta class of another restricted test. -/
theorem mem_sLocalOrbitalSupportRelations_iff (hT : T ⊆ S) (η : PontryaginDual J₁(S))
    (f : U(S, T)) :
    f ∈ sLocalOrbitalSupportRelations hT η ↔
      ∃ g : U(S, T), q(η) f.val = sLocalHomogeneousThetaPrincipalValue hT η (q(η) g.val) :=
  by sorry

local notation "π(" hT ", " η ")" => (D(hT, η)).mkQL.comp (q(η))

/-- Paper: Equations (8.1.0.1) and (8.1.0.3), p. 382.
The map to the ambient orbital quotient kills the source relations. -/
theorem sLocalOrbitalSupportRelations_le_ker (hT : T ⊆ S) (η : PontryaginDual J₁(S)) :
    sLocalOrbitalSupportRelations hT η ≤ ((π(hT, η)).comp (U(S, T)).subtypeL).ker := by sorry

/-- Paper: Equations (8.1.0.1) and (8.1.0.3), p. 382.
The comparison is the continuous linear map induced by including restricted tests
in the full S-adelic test space. -/
def sLocalOrbitalSupportComparison (hT : T ⊆ S) (η : PontryaginDual J₁(S)) :
    (↥U(S, T) ⧸ sLocalOrbitalSupportRelations hT η) →L[ℂ] (Θ(η) ⧸ D(hT, η)) :=
  (sLocalOrbitalSupportRelations hT η).liftQL ((π(hT, η)).comp (U(S, T)).subtypeL)
    (sLocalOrbitalSupportRelations_le_ker hT η)

/-- Paper: Equations (8.1.0.1) and (8.1.0.3), p. 382.
The comparison sends the class of a restricted test to its ambient orbital class. -/
theorem sLocalOrbitalSupportComparison_mk (hT : T ⊆ S) (η : PontryaginDual J₁(S))
    (f : U(S, T)) :
    sLocalOrbitalSupportComparison hT η ((sLocalOrbitalSupportRelations hT η).mkQL f) =
      π(hT, η) f.val := by sorry

-- TODO(paper-gap): On p. 383 the identity Λ/L_out = L_S omits the factor regularizing
-- the trivial norm-one component. Moreover the surjectivity argument on pp. 383–384
-- passes from zero-moment to unrestricted tests, and from archimedean entire Mellin
-- transforms to tests with the required finite punctured factors. Already (8.1.0.5)
-- gives the full pair space as the range for two-moment tests. For ℚ, S = {∞, 2},
-- the Gaussian pair has a double pole at zero, whose coefficient detects f(0).
-- In (8.1.0.9), L_S exp(s²) is nonzero at 1, whereas every left-hand member
-- vanishes there since L_out has a pole. On p. 384 insertion also needs the outside
-- Tamagawa masses (ERRATA I96). Both quotient comparisons fail in Sec1_Printed.

/-- Paper: Theorem 8.1.0.1(1), p. 382.
The range of the primary comparison consists of the orbital classes that admit
representatives in the corrected test space (8.1.0.2).
Deviation: The comparison need not be a topological isomorphism. The unramified
character is expressed by its norm-one restriction, as in Theorem 6.2.1.1. -/
theorem sLocalPrimaryOrbitalSupportComparison_range (p : Vℚ)
    (_hp : ∀ v : V, v.under (𝓞 ℚ) = p → v ∈ S) (_hPic : PicTrivial(S))
    {ω : PontryaginDual C₁} (hω : NormOneCharacterUnramifiedOutside ω S) :
    let T := sLocalPrimaryPlaces S p
    let hT := sLocalPrimaryPlaces_subset S p
    let η := sLocalNormOneCharacter S ω hω
    let A : (↥U(S, T) ⧸ sLocalOrbitalSupportRelations hT η) →L[ℂ]
        SLocalPrimaryOrbitalQuotient p η := sLocalOrbitalSupportComparison hT η
    LinearMap.range A.toLinearMap = (U(S, T)).map (π(hT, η)).toLinearMap := by sorry

/-- Paper: Theorem 8.1.0.1(2), p. 382.
The range of the single-place comparison consists of the orbital classes that admit
representatives in the corrected test space (8.1.0.4).
Deviation: The comparison need not be a topological isomorphism. The unramified
character is expressed by its norm-one restriction, as in Theorem 6.2.1.1. -/
theorem sLocalPlaceOrbitalSupportComparison_range (v : S) (_hPic : PicTrivial(S))
    {ω : PontryaginDual C₁} (hω : NormOneCharacterUnramifiedOutside ω S) :
    let T : Finset V := {v.val}
    let hT : T ⊆ S := Finset.singleton_subset_iff.mpr v.property
    let η := sLocalNormOneCharacter S ω hω
    LinearMap.range (sLocalOrbitalSupportComparison hT η).toLinearMap =
      (U(S, T)).map (π(hT, η)).toLinearMap := by sorry

-- TODO(later): needs §§8.2–8.3 for the announced stack description and the
-- support of the transposed dual basis elements (Theorem 8.3.0.1, p. 387).
-- TODO(paper-gap): The support assertion for ambient test functions on pp. 387–388
-- fails: the open set with every coordinate nonzero is dense, so an ambient
-- continuous function supported on its complement vanishes. On ℚ with S = {∞, 2},
-- the double-pole coefficient of the Gaussian at zero gives a nonzero orbital
-- functional. The support of that distribution and the support of its test
-- functions play different roles.

end RiemannMasullo
