module

public import RiemannMasullo.Ch06_LocalGlobal.Sec2

/-! # Chapter 6.2: statements that are false as printed -/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Topology
open scoped DirectSum NNReal

namespace RiemannMasullo

set_option quotPrecheck false

local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Picₛ(" F ", " S ")" => CommRing.Pic ((S : Set (Places(F))).integer F)
local notation "Iₛ(" F ", " S ")" => (SAdeleRing F S)ˣ
local notation "Nₛ(" F ", " S ")" => (sIdeleNorm F S).ker
local notation "J₁(" F ", " S ")" => (sIdeleQuotientNorm F S).ker
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "ℬ∞(" F ")" => ℬ(InfiniteAdeleRing F)
local notation "L(" F ", " v ")" => HeightOneSpectrum.adicCompletion (R := 𝓞 F) F v
local notation "O(" F ", " v ")" => HeightOneSpectrum.adicCompletionIntegers (R := 𝓞 F) F v

open Classical in
/-- Paper: Remark 6.2.1.4(1), (6.2.1.2), p. 297. As printed: the locally convex direct sum
topologies of the S-local and global isotypes are strictly finer than the topologies induced by
their inclusions into the ordinary theta quotients. See `sLocalThetaIsotypeSum_dense`,
`globalThetaIsotypeSum_dense` and ERRATA F71. -/
def Printed.thetaIsotypeSum_strictlyFiner : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    (∀ S : Finset (Places(F)),
      let ρ := (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose
      let E := actionIsotype (ρ.comp (sIdeleQuotientNorm F S).ker.subtype)
      let X := fun χ : PontryaginDual J₁(F, S) ↦ ↥(E χ)
      let _ := locallyConvexFinalTopology (DirectSum.lof ℂ _ X)
      ¬ IsInducing (DirectSum.toModule ℂ _ (SLocalAdelicThetaSpace F S) fun χ ↦ (E χ).subtype)) ∧
    (let ρ := (existsUnique_globalThetaAction (F := F)).exists.choose
      let E := actionIsotype (ρ.comp (ideleClassNorm F).ker.subtype)
      let X := fun ω : PontryaginDual C₁(F) ↦ ↥(E ω)
      let _ := locallyConvexFinalTopology (DirectSum.lof ℂ _ X)
      ¬ IsInducing (DirectSum.toModule ℂ _ (GlobalAdelicThetaSpace F) fun ω ↦ (E ω).subtype))

/-- A norm-one rational idele at the archimedean stage is represented by a diagonal sign. -/
private theorem thetaIsotypeSum_strictlyFiner_false_rat :
    Subsingleton (sIdeleQuotientNorm ℚ ∅).ker := by
  classical
  refine subsingleton_of_forall_eq 1 ?_
  rintro ⟨q, hq⟩
  apply Subtype.ext
  change q = 1
  revert hq
  refine Quotient.inductionOn q fun g hg ↦ ?_
  change sIdeleNorm ℚ ∅ g = 1 at hg
  let w := Rat.infinitePlace
  let coord : SAdeleRing ℚ ∅ ≃+* ℝ :=
    ((RingEquiv.prodZeroRing _ _).symm.trans
      (RingEquiv.piUnique fun v : InfinitePlace ℚ ↦ v.Completion)).trans
      (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)
  have hn : ‖g.val.1 w‖ = 1 := by
    have h := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) hg
    rwa [sIdeleNorm, Finset.univ_eq_empty (α := (∅ : Finset (Places(ℚ)))),
      Finset.prod_empty, mul_one, Fintype.prod_subsingleton _ w,
      Rat.isReal_infinitePlace.mult_eq_one, pow_one] at h
  have ha : |coord g.val| = 1 :=
    ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
      Rat.isReal_infinitePlace).norm_map_of_map_zero (map_zero _) _).trans hn
  apply (sIdeleQuotient_mk_eq_one ℚ ∅ g).mpr
  rcases eq_or_eq_neg_of_abs_eq ha with h | h
  · refine ⟨1, Units.ext (coord.injective ?_)⟩
    simpa only [map_one, Units.val_one] using h
  · refine ⟨-1, Units.ext (coord.injective ?_)⟩
    change coord g.val = coord (((adeleProjection ℚ ∅).comp (integralAdelesOutside ℚ ∅).subtype)
      (integralAdeleDiagonal ℚ ∅ (-1)))
    simpa only [map_neg, map_one] using h

/-- For a single submodule, the locally convex direct sum induces the subspace topology. -/
private theorem thetaIsotypeSum_strictlyFiner_false_single
    {E I : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
    [Subsingleton I] [DecidableEq I] (X : I → Submodule ℂ E) (k : I) :
    letI := locallyConvexFinalTopology (DirectSum.lof ℂ I fun i ↦ ↥(X i))
    IsInducing (DirectSum.toModule ℂ I E fun i ↦ (X i).subtype) := by
  let D := ⨁ i, ↥(X i)
  let j := DirectSum.lof ℂ I fun i ↦ ↥(X i)
  let : TopologicalSpace D := locallyConvexFinalTopology j
  have hD : WithSeminorms
      (Subtype.val : {p : Seminorm ℂ D // ∀ i, Continuous (p ∘ j i)} → Seminorm ℂ D) := ⟨rfl⟩
  let := hD.isTopologicalAddGroup
  let := PolynormableSpace.isTopologicalAddGroup ℂ E
  let c := DirectSum.component ℂ I (fun i ↦ ↥(X i)) k
  have hj : Continuous (j k) := hD.continuous_of_continuous_comp _ fun p ↦ p.property k
  have hc : Continuous c := by
    apply (PolynormableSpace.withSeminorms ℂ (X k)).continuous_of_continuous_comp c
    intro p
    apply hD.continuous_seminorm ⟨p.val.comp c, ?_⟩
    intro i
    obtain rfl := Subsingleton.elim i k
    change Continuous fun x : X i ↦ p.val ((j i x) i)
    simp only [j, DirectSum.lof_apply]
    exact p.property
  -- Projection onto the only component is inverse to its inclusion.
  have hleft : LeftInverse (j k) c := by
    intro x
    apply DFinsupp.ext
    intro i
    obtain rfl := Subsingleton.elim i k
    exact DFinsupp.single_eq_same
  have hsum : ⇑(DirectSum.toModule ℂ I E fun i ↦ (X i).subtype) = Subtype.val ∘ c := by
    funext x
    conv_lhs => rw [← hleft x]
    exact DirectSum.toModule_lof (M := fun i ↦ ↥(X i)) (φ := fun i ↦ (X i).subtype) ℂ k (c x)
  rw [hsum]
  exact IsInducing.subtypeVal.comp (hleft.isEmbedding hj hc).isInducing

/-- Paper: Remark 6.2.1.4(1), (6.2.1.2), p. 297. Over ℚ at the archimedean stage the norm-one
quotient is `{±1}/{±1}`, so the sole summand is the entire theta space with its own topology.
Globally over ℚ, the action of the profinite norm-one group factors through a finite group on
each finite test level. The finite character projections extend through the inductive limit and
the theta quotient to a continuous inverse to the sum map. -/
theorem Printed.thetaIsotypeSum_strictlyFiner_false :
    ¬ Printed.thetaIsotypeSum_strictlyFiner := by
  classical
  intro h
  apply (h ℚ).1 ∅
  let G := (sIdeleQuotientNorm ℚ ∅).ker
  let : Subsingleton G := thetaIsotypeSum_strictlyFiner_false_rat
  let : Subsingleton (PontryaginDual G) := subsingleton_of_forall_eq 1 fun χ ↦
    PontryaginDual.ext fun g ↦ by rw [Subsingleton.elim g 1, map_one, map_one]
  let : DecidableEq (PontryaginDual G) := Classical.decEq _
  let : PolynormableSpace ℂ (SLocalAdelicThetaSpace ℚ ∅) := sLocalAdelicThetaSpace_polynormable
  let ρ := (existsUnique_sLocalThetaAction (F := ℚ) (S := ∅)).exists.choose
  let X := actionIsotype (ρ.comp (sIdeleQuotientNorm ℚ ∅).ker.subtype)
  exact thetaIsotypeSum_strictlyFiner_false_single (E := SLocalAdelicThetaSpace ℚ ∅)
    (I := PontryaginDual G) X 1

/-- Paper: Remark 6.2.1.4(2), p. 298. As printed: the S-local theta quotient has nonclosed
image in the product of its homogeneous theta quotients, and the topology induced by the product
is strictly coarser. We take the product in (5.2.3.13), Proposition 5.2.3.2(2), p. 236.
The remark gives conflicting references, including (5.2.2.3), which defines a quotient. See the
global versions `globalThetaToHomogeneousProduct_not_isClosed_range` and
`globalThetaToHomogeneousProduct_not_isInducing`, and ERRATA F72. -/
def Printed.sLocalThetaToHomogeneousProduct_strictlyCoarser_nonclosed : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    let P := (exists_sLocalThetaToHomogeneousProduct (F := F) (S := S)).choose
    ¬ IsInducing P ∧ ¬ IsClosed (Set.range P)

/-- Paper: Remark 6.2.1.4(2), p. 298. Take ℚ and the archimedean stage. The norm-one quotient
is trivial, and projection to the sole factor identifies the product map with the identity on
the theta quotient. The range is closed and the induced topology is the intrinsic topology. -/
theorem Printed.sLocalThetaToHomogeneousProduct_strictlyCoarser_nonclosed_false :
    ¬ Printed.sLocalThetaToHomogeneousProduct_strictlyCoarser_nonclosed := by sorry

section StandardFunctions

variable {F : Type*} [Field F] [NumberField F]

local instance printedCh06Sec2FiniteIdeleMeasurableSpace (v : Places(F)) :
    MeasurableSpace (L(F, v))ˣ := borel _

local notation "U(" F ", " v ")" => ((O(F, v)).units : Set (L(F, v))ˣ)
local notation "μ(" F ", " v ")" => finiteLocalMultiplicativeTamagawaMeasure F v

open Classical in
/-- Paper: Theorem 6.2.2.1, first numbered definition, p. 298. As printed: at a ramified place
in S the standard test has zeta integral equal to the integer-unit mass when the character
matches on integer units and has positive abscissa, and zero otherwise. See
`finiteStandardGaussian_zeta_of_ramified` and ERRATA F73. -/
def Printed.finiteStandardGaussian_zeta_of_ramified_positive : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    Subsingleton Picₛ(F, S) →
    ∀ (ω : PontryaginDual C₁(F)) (hω : NormOneCharacterUnramifiedOutside ω S) (v : S)
      (d : QuasiCharacter (L(F, v.val))ˣ),
      let c := sLocalFiniteRestriction v (sIdeleRestriction F S hω.choose)
      let Uv := U(F, v.val)
      (∃ u ∈ Uv, c u ≠ 1) →
        localIdelicZetaIntegral (μ(F, v.val))
          (fun x ↦ finiteStandardGaussian v.val c (Multiplicative.ofAdd x)) d =
        if (∀ u ∈ Uv, d u = c u) ∧ (∃ σ : ℝ, 0 < σ ∧ ∀ g : (L(F, v.val))ˣ,
          ‖d g‖ = ‖g.val‖ ^ σ) then ((μ(F, v.val)) Uv).toReal else 0

/-- Paper: Theorem 6.2.2.1, first numbered definition, p. 298. Over ℚ take the even quadratic
idele class character modulo 5, S consisting of the infinite place and 5, and the unitary local
character at 5 as d. Its abscissa is zero. The standard test is its conjugate on the integer
units, so the integrand is their indicator and the integral is their positive mass. -/
theorem Printed.finiteStandardGaussian_zeta_of_ramified_positive_false :
    ¬ Printed.finiteStandardGaussian_zeta_of_ramified_positive := by sorry

-- The sum in (6.2.2.3) uses a list of norm-one representatives of the full class group.
local notation "ClassRepresentatives(" F ", " S ", " r ")" =>
  (r ⟨0, classNumber_pos F⟩ = 1 ∧
    Bijective (fun k ↦ ideleIdealClass F (sIdeleInsertion F S (r k).val)))

local notation "Lifts(" F ", " S ", " χ ", " ωₛ ")" =>
  (∀ (g : Nₛ(F, S)) (y : J₁(F, S)), y.val = QuotientGroup.mk g.val → χ g.val = ωₛ y)

open Classical in
/-- Paper: Theorem 6.2.2.1(1), (6.2.2.7)–(6.2.2.10), pp. 299–301. As printed: on pure tensors
of archimedean tests and punctured finite tests the norm-one integral (6.2.2.7) equals the product
of the archimedean operator (6.2.2.3) and the finite convolutions (6.2.2.4). This is the
pointwise identity asserted for the tensor extension. See
`sLocalStandardThetaTensor_toGlobal_openQuotient` and ERRATA F74. -/
def Printed.sLocalStandardThetaTensor_factorization : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    Subsingleton Picₛ(F, S) →
    ∀ (ω : PontryaginDual C₁(F)) (hω : NormOneCharacterUnramifiedOutside ω S)
      (χ : PontryaginDual Iₛ(F, S)),
      Lifts(F, S, χ, sLocalNormOneCharacter S ω hω) →
      ∀ (r : Fin (classNumber F) → Nₛ(F, S)), ClassRepresentatives(F, S, r) →
      ∀ (f : ℬ∞(F)) (fv : ∀ v : S, finitePuncturedThetaTestSpace v.val) (x : Iₛ(F, S)),
        let xArch := Units.map (RingHom.fst (InfiniteAdeleRing F) (∀ v : S, L(F, v.val))).toMonoidHom x
        let ins (v : S) := Units.map ((MonoidHom.inr (InfiniteAdeleRing F) _).comp
          (MonoidHom.mulSingle (fun v : S ↦ L(F, v.val)) v))
        (∫ g : Nₛ(F, S),
          let y := g.val⁻¹ * x
          f (Multiplicative.ofAdd y.val.1) *
            (∏ v : S, (fv v).val (Multiplicative.ofAdd (y.val.2 v))) * (χ g.val : ℂ)
          ∂sNormOneIdeleTamagawaMeasure F S) =
        infiniteStandardThetaAverage χ r f xArch *
          ∏ v : S, ∫ g : (L(F, v.val))ˣ,
            (fv v).val (Multiplicative.ofAdd ((g⁻¹).val * x.val.2 v)) * (χ (ins v g) : ℂ)
            ∂μ(F, v.val)

/-- Paper: Theorem 6.2.2.1(1), (6.2.2.7)–(6.2.2.10), pp. 299–301. Over ℚ take S with one finite
prime p, the trivial character, the identity class representative, and x = 1. Use the finite
indicator of `pℤₚˣ` and an even nonnegative smooth compactly supported function positive at ±1
and supported away from ±p. The norm-one integral is zero since the finite support forces the
inverse real component to have absolute value p. The separate factors are both positive. -/
theorem Printed.sLocalStandardThetaTensor_factorization_false :
    ¬ Printed.sLocalStandardThetaTensor_factorization := by sorry

/-- Paper: Theorem 6.2.2.1(1), (6.2.2.5), p. 299. As printed: the insertion with the fixed
standard finite tests induces a linear homeomorphism from the quotient by the kernel of the
inverse-argument archimedean average (6.2.2.3) to the S-local homogeneous theta quotient. The
fixed tensor line is expressed by insertion. See `sLocalStandardThetaTensor_quotient_equiv`
and ERRATA F75. -/
def Printed.sLocalStandardThetaTensor_inverseAverage_quotient_equiv : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    Subsingleton Picₛ(F, S) →
    ∀ (ω : PontryaginDual C₁(F)) (hω : NormOneCharacterUnramifiedOutside ω S)
      (χ : PontryaginDual Iₛ(F, S)),
      let ωₛ := sLocalNormOneCharacter S ω hω
      Lifts(F, S, χ, ωₛ) →
      ∀ (r : Fin (classNumber F) → Nₛ(F, S)), ClassRepresentatives(F, S, r) →
        let K := (infiniteStandardThetaAverage χ r).ker
        let c := sIdeleRestriction F S hω.choose
        ∃ e : (ℬ∞(F) ⧸ K) ≃L[ℂ] SLocalHomogeneousThetaSpace F S ωₛ,
          ∀ f : ℬ∞(F), e (K.mkQ f) = (sLocalHomogeneousAdelicThetaLinearMap F S ωₛ).ker.mkQ
            (sLocalStandardThetaTensor c f)

/-- Paper: Theorem 6.2.2.1(1), (6.2.2.5), p. 299. Take ℚ(i) at its complex stage, the
identity representative, `χ(z) = (z/|z|)^4` and `f(z) = z^4 exp(-|z|²)`. The character kills
the four global units and extends unramified at all finite places since the class group is
trivial. The inverse-argument average at 1 is the integral of `exp(-1)` on the circle. The
homogeneous theta average uses the positive argument, so its circle integrand has weight 8
and averages to zero. The proposed map sends the resulting nonzero source class to zero. -/
theorem Printed.sLocalStandardThetaTensor_inverseAverage_quotient_equiv_false :
    ¬ Printed.sLocalStandardThetaTensor_inverseAverage_quotient_equiv := by sorry

/-- Paper: Theorem 6.2.2.1(2), p. 299. As printed: the archimedean operator has semi-exponential
decay in the norm coordinate. This isolates the requirement of Definition B.2.1.1 that its
unweighted logarithmic profile be Schwartz, tested on the canonical norm section. See
`infiniteStandardThetaAverage_forwardDecay`, `infiniteStandardThetaAverage_logBound` and
ERRATA F76. -/
def Printed.infiniteStandardThetaAverage_schwartz_logProfile : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F))),
    Subsingleton Picₛ(F, S) →
    ∀ (ω : PontryaginDual C₁(F)) (hω : NormOneCharacterUnramifiedOutside ω S)
      (χ : PontryaginDual Iₛ(F, S)),
      Lifts(F, S, χ, sLocalNormOneCharacter S ω hω) →
      ∀ (r : Fin (classNumber F) → Nₛ(F, S)), ClassRepresentatives(F, S, r) →
      ∀ f : ℬ∞(F), ∃ φ : SchwartzMap ℝ ℂ, ∀ t : ℝ,
        let u : ℝ≥0ˣ := Units.mk0 (Real.toNNReal (Real.exp t))
          (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos t)))
        let x := Units.map (RingHom.fst (InfiniteAdeleRing F)
          (FiniteAdeleRing (𝓞 F) F)).toMonoidHom (canonicalIdeleNormSection F u)
        φ t = infiniteStandardThetaAverage χ r f x

/-- Paper: Theorem 6.2.2.1(2), pp. 299, 302. Over ℚ at the archimedean stage, take the
trivial character, the identity representative and the real Gaussian `exp(-πx²)`. Its unweighted
logarithmic profile is a positive constant times `exp(-π exp(2t))`, which has a nonzero limit
as t tends to negative infinity. -/
theorem Printed.infiniteStandardThetaAverage_schwartz_logProfile_false :
    ¬ Printed.infiniteStandardThetaAverage_schwartz_logProfile := by sorry

end StandardFunctions

end RiemannMasullo
