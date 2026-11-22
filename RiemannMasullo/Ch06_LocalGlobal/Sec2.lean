module

public import RiemannMasullo.Ch06_LocalGlobal.Sec1
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3a
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a

/-! # Structure Theorem V: isotypic exhaustiveness

Masullo, §6.2, pp. 295–302. Finite sets of places index only the finite factors.
Every S-adelic space includes all archimedean places.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Topology
open scoped DirectSum NNReal NumberField.AdeleRing TensorProduct

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
variable {S T : Finset (HeightOneSpectrum (𝓞 F))}

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Iₛ(" S ")" => (SAdeleRing F S)ˣ
local notation "Nₛ(" S ")" => (sIdeleNorm F S).ker
local notation "Jₛ(" S ")" => SIdeleQuotient F S
local notation "J₁(" S ")" => (sIdeleQuotientNorm F S).ker
local notation "C₁" => (ideleClassNorm F).ker
local notation "Picₛ(" S ")" => CommRing.Pic ((S : Set V).integer F)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "ℬₛ(" S ")" => ℬ(SAdeleRing F S)
local notation "ℬ∞" => ℬ(InfiniteAdeleRing F)
local notation "Θₛ(" S ")" => SLocalAdelicThetaSpace F S
local notation "Θ𝔽" => GlobalAdelicThetaSpace F
local notation "Θₛω(" S ", " χ ")" => SLocalHomogeneousThetaSpace F S χ
local notation "Θ𝔽ω(" ω ")" => GlobalHomogeneousThetaSpace F ω
local notation "Kₛω(" S ", " χ ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S χ)
local notation "ρₛ(" S ")" => (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
local notation "ρ𝔽" => (existsUnique_globalThetaAction (F := F)).exists.choose

section Exhaustiveness

/-- Paper: (6.2.1.1), p. 297.
The norm-one quotient at T maps openly onto the norm-one quotient at S when the
S-integer Picard group is trivial. Its kernel is the image of the integral units at
the additional places, and the map reverses insertion on representatives at S. -/
theorem existsUnique_sLocalNormOneQuotientTransition (hST : S ⊂ T)
    (_hPic : Subsingleton Picₛ(S)) :
    ∃! q : J₁(T) →ₜ* J₁(S), Surjective q ∧ IsOpenMap q ∧
      (∀ x : J₁(T), q x = 1 ↔
        ∃ u : relativeIntegralIdeleUnits F S T, x.val = QuotientGroup.mk u.val) ∧
      ∀ (g : Nₛ(S)) (x : J₁(T)) (y : J₁(S)),
        x.val = QuotientGroup.mk (Units.map (adeleProjection F T).toMonoidHom
          (sIdeleInsertion F S g.val)) →
        y.val = QuotientGroup.mk g.val → q x = y := by sorry

/-- Paper: Theorem 6.2.1.1(1), p. 295.
For a T-local character trivial on the additional integer units, adjoining integer
indicators gives a surjective topological linear isomorphism on homogeneous classes.
The source character is the unique descent of the target character. -/
theorem sLocalHomogeneousThetaTransition_equiv_of_unramified
    (hST : S ⊂ T) (hPic : Subsingleton Picₛ(S)) (χ : PontryaginDual J₁(T))
    (_hχ : ∀ (x : J₁(T)) (u : relativeIntegralIdeleUnits F S T),
      x.val = QuotientGroup.mk u.val → χ x = 1) :
    let q := (existsUnique_sLocalNormOneQuotientTransition hST hPic).exists.choose
    ∃ (χS : PontryaginDual J₁(S)) (e : Θₛω(S, χS) ≃L[ℂ] Θₛω(T, χ)),
      (∀ x, χS (q x) = χ x) ∧
      ∀ f : ℬₛ(S), e ((Kₛω(S, χS)).mkQ f) =
        (Kₛω(T, χ)).mkQ (sAdeleSchwartzTransition F hST.le f) := by sorry

/-- Paper: Theorem 6.2.1.1(2), p. 295.
If the S-integer Picard group is trivial and the global character is unramified
outside S, the existing homogeneous insertion is a topological linear isomorphism. -/
theorem sLocalHomogeneousThetaToGlobal_equiv_of_unramified
    (_hPic : Subsingleton Picₛ(S)) {ω : PontryaginDual C₁}
    (hω : NormOneCharacterUnramifiedOutside ω S) :
    ∃ e : Θₛω(S, sLocalNormOneCharacter S ω hω) ≃L[ℂ] Θ𝔽ω(ω),
      e.toLinearMap = sLocalHomogeneousThetaToGlobal hω := by sorry

/-- Paper: Corollary 6.2.1.2, p. 295.
Each global homogeneous theta quotient is a nuclear Fréchet space. -/
theorem globalHomogeneousThetaSpace_nuclearFrechet (ω : PontryaginDual C₁) :
    IsFrechetTVS Θ𝔽ω(ω) ∧ IsNuclearTVS Θ𝔽ω(ω) := by sorry

-- TODO(paper-gap): The proof of Lemma 6.2.1.3 repeats the componentwise-seminorm
-- error in ERRATA I125. Joint continuity of the action and compactness apply.

/-- Paper: Lemma 6.2.1.3(1), p. 296.
Convergence of a net of local theta classes implies uniform convergence of its orbit
maps over the compact norm-one quotient. -/
theorem sLocalThetaAction_tendstoUniformly {ι : Type*} (l : Filter ι)
    (f : ι → Θₛ(S)) (x : Θₛ(S)) (hf : Tendsto f l (𝓝 x)) :
    ∀ U ∈ 𝓝 (0 : Θₛ(S)), ∀ᶠ i in l, ∀ g : J₁(S),
      ρₛ(S) g.val (f i) - ρₛ(S) g.val x ∈ U := by sorry

/-- Paper: Lemma 6.2.1.3(2), p. 296.
Uniform convergence over the norm-one quotient also holds after twisting the action
by a unitary character. -/
theorem sLocalThetaAction_twist_tendstoUniformly {ι : Type*} (l : Filter ι)
    (f : ι → Θₛ(S)) (x : Θₛ(S)) (hf : Tendsto f l (𝓝 x)) (χ : PontryaginDual J₁(S)) :
    ∀ U ∈ 𝓝 (0 : Θₛ(S)), ∀ᶠ i in l, ∀ g : J₁(S),
      (χ g : ℂ) • ρₛ(S) g.val (f i) - (χ g : ℂ) • ρₛ(S) g.val x ∈ U := by sorry

end Exhaustiveness

section IsotypicSums

local notation "ρₛ₁(" S ")" => (ρₛ(S)).comp (MonoidHom.ker (sIdeleQuotientNorm F S)).subtype
local notation "ρ𝔽₁" => (ρ𝔽).comp (MonoidHom.ker (ideleClassNorm F)).subtype
local notation "Eₛ(" χ ")" => actionIsotype (ρₛ₁(S)) χ
local notation "E𝔽(" ω ")" => actionIsotype ρ𝔽₁ ω

-- TODO(paper-gap): In Remark 6.2.1.4(1)–(2), neither local topology comparison is
-- strict for F = ℚ and the archimedean stage. Its norm-one quotient is trivial,
-- so both comparisons reduce to the topology on the sole isotype.
-- The global comparison can also be equality over ℚ: each finite test stage
-- factors through a finite quotient of the norm-one unit action.
-- The proof of strictness also assumes infinitely many everywhere unramified
-- characters, which fails over ℚ.

/-- Paper: Remark 6.2.1.4(1), pp. 297–298.
The direct sum of the S-local isotypes maps continuously and injectively to the
theta quotient with dense range.
Deviation: The topology of the direct sum is the locally convex final topology.
The strict comparison in the remark fails in general. -/
theorem sLocalThetaIsotypeSum_dense :
    let X := fun χ : PontryaginDual J₁(S) ↦ ↥(Eₛ(χ))
    letI := Classical.decEq (PontryaginDual J₁(S))
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ _ X)
    let i := DirectSum.toModule ℂ _ Θₛ(S) (fun χ ↦ (Eₛ(χ)).subtype)
    Continuous i ∧ Injective i ∧ DenseRange i := by sorry

/-- Paper: Remark 6.2.1.4(1), pp. 297–298.
The direct sum of the global isotypes maps continuously and injectively to the
global theta quotient with dense range.
Deviation: The topology of the direct sum is the locally convex final topology.
The strict comparison is omitted. -/
theorem globalThetaIsotypeSum_dense :
    let X := fun ω : PontryaginDual C₁ ↦ ↥(E𝔽(ω))
    letI := Classical.decEq (PontryaginDual C₁)
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ _ X)
    let i := DirectSum.toModule ℂ _ Θ𝔽 (fun ω ↦ (E𝔽(ω)).subtype)
    Continuous i ∧ Injective i ∧ DenseRange i := by sorry

/-- Paper: Remark 6.2.1.4(1), p. 297.
The locally convex direct sum of the S-local isotypes is Hausdorff and complete. -/
theorem sLocalThetaIsotypeSum_complete :
    let X := fun χ : PontryaginDual J₁(S) ↦ ↥(Eₛ(χ))
    letI := Classical.decEq (PontryaginDual J₁(S))
    let D := ⨁ χ, X χ
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ _ X)
    T2Space D ∧ PolynormableSpace ℂ D ∧
      ∀ (u : UniformSpace D), u.toTopologicalSpace = (inferInstance : TopologicalSpace D) →
        @IsUniformAddGroup D u _ → @CompleteSpace D u := by sorry

/-- Paper: Remark 6.2.1.4(1), p. 297.
The locally convex direct sum of the global isotypes is Hausdorff and complete. -/
theorem globalThetaIsotypeSum_complete :
    let X := fun ω : PontryaginDual C₁ ↦ ↥(E𝔽(ω))
    letI := Classical.decEq (PontryaginDual C₁)
    let D := ⨁ ω, X ω
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ _ X)
    T2Space D ∧ PolynormableSpace ℂ D ∧
      ∀ (u : UniformSpace D), u.toTopologicalSpace = (inferInstance : TopologicalSpace D) →
        @IsUniformAddGroup D u _ → @CompleteSpace D u := by sorry

-- The properties referred to in Remark 6.2.1.4(1) are listed in Theorem 5.2.3.1(2).
local notation "sumProperties(" D ")" =>
  IsLFSpace D ∧ IsNuclearTVS D ∧ BarrelledSpace ℂ D ∧ MontelSpace ℂ D ∧
    CompleteSpace (StrongDual ℂ D) ∧ IsNuclearTVS (StrongDual ℂ D) ∧
    BarrelledSpace ℂ (StrongDual ℂ D) ∧ MontelSpace ℂ (StrongDual ℂ D)

/-- Paper: Remark 6.2.1.4(1), p. 297.
The locally convex sum of the local isotypes inherits the space and strong-dual properties
listed in Theorem 5.2.3.1(2). -/
theorem sLocalThetaIsotypeSum_inherited_properties :
    let X := fun χ : PontryaginDual J₁(S) ↦ ↥(Eₛ(χ))
    letI := Classical.decEq (PontryaginDual J₁(S))
    let D := ⨁ χ, X χ
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ _ X)
    sumProperties(D) := by sorry

/-- Paper: Remark 6.2.1.4(1), p. 297.
The locally convex sum of the global isotypes inherits the space and strong-dual properties
listed in Theorem 5.2.3.1(2). -/
theorem globalThetaIsotypeSum_inherited_properties :
    let X := fun ω : PontryaginDual C₁ ↦ ↥(E𝔽(ω))
    letI := Classical.decEq (PontryaginDual C₁)
    let D := ⨁ ω, X ω
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ _ X)
    sumProperties(D) := by sorry

-- TODO(paper-gap): Remark 6.2.1.4(2) also asserts nonclosed product images.
-- At the rational archimedean stage the image in the product of homogeneous
-- theta quotients is the whole product. The remark conflates that product
-- with the product of the meromorphic Mellin target spaces.

/-- Paper: Remark 6.2.1.4(2), p. 298.
The global theta quotient has nonclosed image in the product of its homogeneous
quotients.
Deviation: The earlier continuous injection in (5.2.3.13) identifies the product map. -/
theorem globalThetaToHomogeneousProduct_not_isClosed_range :
    ¬ IsClosed (Set.range (exists_globalThetaToHomogeneousProduct (F := F)).choose) := by sorry

/-- Paper: Remark 6.2.1.4(2), p. 298.
The topology on the global theta quotient induced by the product of homogeneous
quotients is strictly coarser than its intrinsic topology.
Deviation: The earlier continuous injection in (5.2.3.13) identifies the product map. -/
theorem globalThetaToHomogeneousProduct_not_isInducing :
    ¬ IsInducing (exists_globalThetaToHomogeneousProduct (F := F)).choose := by sorry

end IsotypicSums

section StandardFunctions

local notation "L(" v ")" => HeightOneSpectrum.adicCompletion (R := 𝓞 F) F v
local notation "O(" v ")" => HeightOneSpectrum.adicCompletionIntegers (R := 𝓞 F) F v
local notation "U(" v ")" => ((O(v)).units : Set (L(v))ˣ)
local notation "μ(" v ")" => finiteLocalMultiplicativeTamagawaMeasure F v

local instance finiteIdeleMeasurableSpaceSec2 (v : V) : MeasurableSpace (L(v))ˣ := borel _

open Classical in
/-- Paper: Theorem 6.2.2.1, p. 298.
In the ramified case the zeta integral is the integer-unit mass for matching unit
characters and zero for all others. Compact support in the multiplicative group
gives integrability for every local quasi-character. -/
theorem finiteStandardGaussian_zeta_of_ramified (v : V) (c d : QuasiCharacter (L(v))ˣ)
    (_hc : ∃ u ∈ U(v), c u ≠ 1) :
    Integrable (fun g : (L(v))ˣ ↦ finiteStandardGaussian v c
      (Multiplicative.ofAdd g.val) * d g) (μ(v)) ∧
    (localIdelicZetaIntegral (μ(v)) (fun x ↦ finiteStandardGaussian v c
      (Multiplicative.ofAdd x)) d =
      if (∀ u ∈ U(v), d u = c u) then ((μ(v)) (U(v))).toReal else 0) := by sorry

/-- Paper: Theorem 6.2.2.1, p. 298.
Tensoring an archimedean test with the fixed standard tests at the finite places
gives a linear map into the S-adelic test space.
Deviation: The tensor identification uses the inductive topology of §2.1.4. -/
def sLocalStandardThetaTensor (c : QuasiCharacter Jₛ(S)) : ℬ∞ →ₗ[ℂ] ℬₛ(S) :=
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  let W := FinestLocallyConvex (⨂[ℂ] v : S, ℬ(L(v.val)))
  let g : W := ⨂ₜ[ℂ] v : S, finiteStandardGaussian v.val (sLocalFiniteRestriction v c)
  e.toLinearMap.comp ((TensorProduct.mk ℂ ℬ∞ W).flip g)

/-- Paper: Theorem 6.2.2.1, p. 298.
Evaluation on an S-adele multiplies the archimedean test value by the standard
finite test value at each finite coordinate. -/
theorem sLocalStandardThetaTensor_apply (c : QuasiCharacter Jₛ(S)) (f : ℬ∞)
    (x : SAdeleRing F S) :
    sLocalStandardThetaTensor c f (Multiplicative.ofAdd x) =
      f (Multiplicative.ofAdd x.1) * ∏ v : S, finiteStandardGaussian v.val
        (sLocalFiniteRestriction v c) (Multiplicative.ofAdd (x.2 v)) := by sorry

/-- Paper: Theorem 6.2.2.1, p. 298.
For trivial S-integer Picard group, the archimedean test space maps continuously,
surjectively and openly onto the global isotype after tensoring with the standard tests.
Deviation: The existence of the stated descent requires unramifiedness outside S.
The fixed finite tensor factor identifies its domain with the archimedean test space. -/
theorem sLocalStandardThetaTensor_toGlobal_openQuotient
    (_hPic : Subsingleton Picₛ(S)) {ω : PontryaginDual C₁}
    (hω : NormOneCharacterUnramifiedOutside ω S) :
    let c := sIdeleRestriction F S hω.choose
    let χ := sLocalNormOneCharacter S ω hω
    IsOpenQuotientMap (fun f : ℬ∞ ↦ sLocalHomogeneousThetaToGlobal (ω := ω) hω
      ((Kₛω(S, χ)).mkQ (sLocalStandardThetaTensor (F := F) (S := S) c f))) := by sorry

local notation "I∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => Nₛ((∅ : Finset V))
local notation "archPart(" D ")" => Units.map (RingHom.fst (InfiniteAdeleRing F)
  (∀ v : D, L(v.val))).toMonoidHom
local notation "archInsert(" D ")" =>
  Units.map (MonoidHom.inl (InfiniteAdeleRing F) (∀ v : D, L(v.val)))

/-- Paper: (6.2.2.3), p. 298.
Every term of the archimedean integral is absolutely integrable. The norm-one
archimedean measure is the Tamagawa measure for the stage with no finite places. -/
theorem infiniteStandardThetaAverage_integrable (χ : PontryaginDual Iₛ(S))
    (f : ℬ∞) (a x : I∞) :
    Integrable (fun g : N∞ ↦
      f (Multiplicative.ofAdd ((a * archPart((∅ : Finset V)) g.val)⁻¹ * x).val) *
        (χ (archInsert(S) (a * archPart((∅ : Finset V)) g.val)) : ℂ))
      (sNormOneIdeleTamagawaMeasure F ∅) := by sorry

/-- Paper: (6.2.2.3), p. 298.
The sum of archimedean integrals specifies a continuous linear map into the
continuous functions on the archimedean ideles. -/
theorem exists_infiniteStandardThetaAverage (χ : PontryaginDual Iₛ(S))
    (r : Fin (classNumber F) → Nₛ(S)) :
    ∃ A : ℬ∞ →L[ℂ] C(I∞, ℂ), ∀ f x,
      A f x = ∑ k, ∫ g : N∞,
        let a := archPart(S) (r k).val * archPart((∅ : Finset V)) g.val
        f (Multiplicative.ofAdd (a⁻¹ * x).val) * (χ (archInsert(S) a) : ℂ)
        ∂sNormOneIdeleTamagawaMeasure F ∅ := by sorry

/-- Paper: (6.2.2.3), p. 298.
The archimedean operator sums the character-weighted integrals over the
norm-one archimedean ideles, one translate for each entry of the supplied family.
Deviation: The analytic formula works for arbitrary entries. To obtain the printed sum,
choose ideal class representatives with the identity representing the principal class. -/
def infiniteStandardThetaAverage (χ : PontryaginDual Iₛ(S))
    (r : Fin (classNumber F) → Nₛ(S)) : ℬ∞ →L[ℂ] C(I∞, ℂ) :=
  (exists_infiniteStandardThetaAverage χ r).choose

/-- Paper: (6.2.2.3), p. 298.
Evaluation on an archimedean idele gives the finite sum in the paper. -/
theorem infiniteStandardThetaAverage_apply (χ : PontryaginDual Iₛ(S))
    (r : Fin (classNumber F) → Nₛ(S)) (f : ℬ∞) (x : I∞) :
    infiniteStandardThetaAverage χ r f x = ∑ k, ∫ g : N∞,
      let a := archPart(S) (r k).val * archPart((∅ : Finset V)) g.val
      f (Multiplicative.ofAdd (a⁻¹ * x).val) * (χ (archInsert(S) a) : ℂ)
      ∂sNormOneIdeleTamagawaMeasure F ∅ := by sorry

-- In §5.3.1 the punctured-field tests are additive tests vanishing at zero.
-- Local constancy makes these vanish on a neighborhood of zero.
/-- Paper: (6.2.2.4), p. 299.
The punctured-field tests form the subspace of additive Schwartz–Bruhat functions with
value zero at the origin, equipped with its induced topology as in §5.3.1. -/
def finitePuncturedThetaTestSpace (v : V) : Submodule ℂ ℬ(L(v)) :=
  LinearMap.ker ((LinearMap.proj (Multiplicative.ofAdd (0 : L(v)))).comp
    (schwartzBruhatSubmodule (Multiplicative (L(v)))).subtype)

/-- Paper: (6.2.2.4), p. 299.
An additive test belongs to the punctured-field subspace exactly when it vanishes at zero. -/
theorem mem_finitePuncturedThetaTestSpace (v : V) (f : ℬ(L(v))) :
    f ∈ finitePuncturedThetaTestSpace v ↔ f (Multiplicative.ofAdd (0 : L(v))) = 0 := Iff.rfl

local notation "ℬ₀(" v ")" => ↥(finitePuncturedThetaTestSpace v)

/-- Paper: (6.2.2.4), p. 299.
The finite-place integral of a compactly supported test on the punctured field is absolutely
integrable for every translation and unitary character. -/
theorem finiteStandardThetaAverage_integrable (v : V) (χ : PontryaginDual (L(v))ˣ)
    (f : ℬ₀(v)) (x : (L(v))ˣ) :
    Integrable (fun g : (L(v))ˣ ↦ f.val (Multiplicative.ofAdd (g⁻¹ * x).val) * (χ g : ℂ)) (μ(v)) := by sorry

/-- Paper: (6.2.2.4), p. 299.
The finite-place convolution formula specifies a continuous linear map on
locally constant, compactly supported functions on the punctured field. -/
theorem exists_finiteStandardThetaAverage (v : V) (χ : PontryaginDual (L(v))ˣ) :
    ∃ A : ℬ₀(v) →L[ℂ] C((L(v))ˣ, ℂ), ∀ f x,
      A f x = ∫ g : (L(v))ˣ, f.val (Multiplicative.ofAdd (g⁻¹ * x).val) * (χ g : ℂ) ∂μ(v) := by sorry

/-- Paper: (6.2.2.4), p. 299.
The finite operator convolves a compactly supported punctured-field test with the local
character against multiplicative Tamagawa measure. The inverse in the test gives the
Mellin functional for the inverse character at the identity. -/
def finiteStandardThetaAverage (v : V) (χ : PontryaginDual (L(v))ˣ) :
    ℬ₀(v) →L[ℂ] C((L(v))ˣ, ℂ) :=
  (exists_finiteStandardThetaAverage v χ).choose

/-- Paper: (6.2.2.4), p. 299.
At the identity, the finite convolution integrates the inverse pullback of the test
against the local character. -/
theorem finiteStandardThetaAverage_one (v : V) (χ : PontryaginDual (L(v))ˣ)
    (f : ℬ₀(v)) :
    finiteStandardThetaAverage v χ f 1 =
      ∫ g : (L(v))ˣ, f.val (Multiplicative.ofAdd (g⁻¹).val) * (χ g : ℂ) ∂μ(v) := by sorry

/-- Paper: (6.2.2.11), p. 301.
The finite convolution is the character times the Mellin integral with the inverse character.
Deviation: On the test χ times the unit indicator, the coefficient is the integer-unit mass. -/
theorem finiteStandardThetaAverage_eq_character_mul_integral (v : V)
    (χ : PontryaginDual (L(v))ˣ) (f : ℬ₀(v)) (x : (L(v))ˣ) :
    finiteStandardThetaAverage v χ f x = (χ x : ℂ) *
      ∫ y : (L(v))ˣ, f.val (Multiplicative.ofAdd y.val) * (χ y : ℂ)⁻¹ ∂μ(v) := by sorry

/-- Paper: Theorem 6.2.2.1(1), p. 299.
The kernel of the archimedean operator is closed in the archimedean test space. -/
theorem infiniteStandardThetaAverage_isClosed_ker (χ : PontryaginDual Iₛ(S))
    (r : Fin (classNumber F) → Nₛ(S)) :
    IsClosed ((infiniteStandardThetaAverage χ r).ker : Set ℬ∞) := by sorry

/-- Paper: Theorem 6.2.2.1(1), p. 299.
The kernel of the finite convolution is closed in the multiplicative test space. -/
theorem finiteStandardThetaAverage_isClosed_ker (v : V) (χ : PontryaginDual (L(v))ˣ) :
    IsClosed ((finiteStandardThetaAverage v χ).ker : Set (ℬ₀(v))) := by sorry

-- TODO(paper-gap): The tensor agreement in Theorem 6.2.2.1(1), p. 299, fails.
-- For ℚ at S = {∞, p} with trivial character, take a finite test 1_{pℤₚˣ}
-- and a nonnegative even archimedean bump at ±1 supported away from ±p.
-- At the identity the full norm-one integral is zero, because the finite
-- support forces the absolute value of the inverse real component to be p.
-- The product of the separate integrals is strictly positive.

/-- Paper: Theorem 6.2.2.1(1), p. 299.
Integrating over a single archimedean norm fibre gives the archimedean factor of the
Mellin transform with the character convention of §5.2.
Deviation: (6.2.2.3) uses the inverse argument and sums translates over ideal classes.
The product formula of §3.3 uses one fibre with the positive argument. -/
theorem exists_infiniteStandardThetaMellinAverage (χ : PontryaginDual Iₛ(S)) :
    ∃ A : ℬ∞ →L[ℂ] C(I∞, ℂ), ∀ f x,
      A f x = ∫ g : N∞,
        let h := archPart((∅ : Finset V)) g.val
        f (Multiplicative.ofAdd (h * x).val) * (χ (archInsert(S) h) : ℂ)
        ∂sNormOneIdeleTamagawaMeasure F ∅ := by sorry

/-- Paper: Theorem 6.2.2.1(1), p. 299.
The archimedean Mellin average integrates the positive translate against the given character.
Deviation: This uses the single norm fibre occurring in the Mellin integral of §3.3. -/
def infiniteStandardThetaMellinAverage (χ : PontryaginDual Iₛ(S)) : ℬ∞ →L[ℂ] C(I∞, ℂ) :=
  (exists_infiniteStandardThetaMellinAverage χ).choose

/-- Paper: Theorem 6.2.2.1(1), p. 299.
At each idele the Mellin average evaluates to the character-weighted norm-fibre integral.
Deviation: The factors follow the homogeneous transform of §5.2. -/
theorem infiniteStandardThetaMellinAverage_apply (χ : PontryaginDual Iₛ(S)) (f : ℬ∞)
    (x : I∞) :
    infiniteStandardThetaMellinAverage χ f x = ∫ g : N∞,
      let h := archPart((∅ : Finset V)) g.val
      f (Multiplicative.ofAdd (h * x).val) * (χ (archInsert(S) h) : ℂ)
      ∂sNormOneIdeleTamagawaMeasure F ∅ :=
  (exists_infiniteStandardThetaMellinAverage χ).choose_spec f x

/-- Paper: Theorem 6.2.2.1(1), p. 299.
Tensoring with the standard finite test identifies the local homogeneous quotient with
the archimedean quotient by the kernel of the archimedean Mellin average.
Deviation: This kernel uses the character orientation of §5.2 and the single norm fibre
of §3.3. The fixed tensor factor is expressed by insertion. -/
theorem sLocalStandardThetaTensor_quotient_equiv
    (_hPic : Subsingleton Picₛ(S)) {ω : PontryaginDual C₁}
    (hω : NormOneCharacterUnramifiedOutside ω S) (χ : PontryaginDual Iₛ(S))
    (_hχ : ∀ (g : Nₛ(S)) (y : J₁(S)), y.val = QuotientGroup.mk g.val →
      χ g.val = sLocalNormOneCharacter S ω hω y) :
    let c := sIdeleRestriction F S hω.choose
    let χS := sLocalNormOneCharacter S ω hω
    let K := (infiniteStandardThetaMellinAverage χ).ker
    ∃ e : (ℬ∞ ⧸ K) ≃L[ℂ] Θₛω(S, χS), ∀ f : ℬ∞,
      e (K.mkQ f) = (Kₛω(S, χS)).mkQ (sLocalStandardThetaTensor c f) := by sorry

-- TODO(paper-gap): The archimedean output need not be constant on norm fibres
-- for nontrivial characters. Use a norm section for the logarithmic profile.
-- At norm zero the paper only obtains logarithmic growth, so a Schwartz
-- profile without a positive weight would fail even over ℚ with a Gaussian.

/-- Paper: Theorem 6.2.2.1(2), p. 299.
The archimedean operator has forward semi-exponential decay along the norm
coordinate, including all logarithmic derivatives.
Deviation: The profile is evaluated on the canonical norm section. Every strictly
positive norm weight gives a Schwartz profile, as allowed by the growth in (6.2.2.12). -/
theorem infiniteStandardThetaAverage_forwardDecay (χ : PontryaginDual Iₛ(S))
    (r : Fin (classNumber F) → Nₛ(S)) (f : ℬ∞) :
    (fun t : ℝ ↦
      let u : ℝ≥0ˣ := Units.mk0 (Real.toNNReal (Real.exp t))
        (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos t)))
      let x := Units.map (RingHom.fst (InfiniteAdeleRing F)
        (FiniteAdeleRing (𝓞 F) F)).toMonoidHom (canonicalIdeleNormSection F u)
      infiniteStandardThetaAverage χ r f x) ∈ logExponentialDecaySubmodule (Set.Ioi 0) := by sorry

/-- Paper: (6.2.2.12), p. 302.
Near norm zero, the archimedean operator grows at most as the logarithm to the
power of the number of archimedean places minus one. -/
theorem infiniteStandardThetaAverage_logBound (χ : PontryaginDual Iₛ(S))
    (r : Fin (classNumber F) → Nₛ(S)) (f : ℬ∞) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ x : I∞,
      ((infiniteIdeleNorm F x).val : ℝ) < ε →
      ‖infiniteStandardThetaAverage χ r f x‖ ≤
        C * |Real.log (infiniteIdeleNorm F x).val| ^ (Fintype.card (InfinitePlace F) - 1) := by sorry

end StandardFunctions

/-- Paper: Example 6.2.2.2, p. 299.
The trivial homogeneous theta space over the rationals is a topological linear
quotient of real Schwartz functions, inserted with the integer indicator at every finite place. -/
theorem ratTrivialHomogeneousTheta_quotient :
    ∃ q : SchwartzMap ℝ ℂ →L[ℂ] GlobalHomogeneousThetaSpace ℚ 1,
      IsOpenQuotientMap q ∧
      ∀ (f : SchwartzMap ℝ ℂ) (g : ℬ(InfiniteAdeleRing ℚ)),
        (∀ x : InfiniteAdeleRing ℚ, g (Multiplicative.ofAdd x) =
          f (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
            (x Rat.infinitePlace))) →
        q f = (LinearMap.ker (homogeneousAdelicThetaLinearMap ℚ 1)).mkQ
          (sAdeleSchwartzToGlobal ℚ ∅ (sLocalStandardThetaTensor (F := ℚ) (S := ∅) 1 g)) := by sorry

end RiemannMasullo
