module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
public import RiemannMasullo.Ch06_LocalGlobal.Sec2
import RiemannMasullo.Ch02_AdelicTheta.Sec2a
import all RiemannMasullo.Ch02_AdelicTheta.Sec4

import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Gaussian
import RiemannMasullo.ForMathlib.RingTheory.PicardGroup
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import all RiemannMasullo.Ch03_IdelicZeta.Sec3b
import RiemannMasullo.External.AlgebraicNumberTheoryLean.Chebotarev.DirichletHecke
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Topology.Algebra.Module.Equiv.Pi

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

/-- At the rational archimedean stage, the two norm-one ideles are both diagonal units. -/
private theorem sLocalThetaToHomogeneousProduct_normOne_rat :
    Subsingleton (sIdeleQuotientNorm ℚ ∅).ker := by
  refine subsingleton_of_forall_eq 1 fun ⟨x, hx⟩ ↦ Subtype.ext ?_
  change x = 1
  revert hx
  refine Quotient.inductionOn x fun g hg ↦ ?_
  change sIdeleNorm ℚ ∅ g = 1 at hg
  let j := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  let e : SAdeleRing ℚ ∅ ≃+* ℝ := ((RingEquiv.prodZeroRing _ _).symm.trans
    (RingEquiv.piUnique fun w : InfinitePlace ℚ ↦ w.Completion)).trans j
  have hnorm : |e g.val| = 1 := by
    trans ‖g.val.1 Rat.infinitePlace‖
    · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
        Rat.isReal_infinitePlace).norm_map_of_map_zero (map_zero _) _
    have h := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) hg
    rw [sIdeleNorm, Finset.univ_eq_empty (α := (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))),
      Finset.prod_empty, mul_one, Fintype.prod_subsingleton _ Rat.infinitePlace,
      Rat.isReal_infinitePlace.mult_eq_one, pow_one] at h
    exact h
  rcases eq_or_eq_neg_of_abs_eq hnorm with h | h
  · have hg1 : g = 1 := Units.ext (e.injective (h.trans (map_one e).symm))
    simp [hg1]
  · have hgneg : g = -1 := Units.ext (e.injective (by simpa using h))
    refine (sIdeleQuotient_mk_eq_one ℚ ∅ g).2 ⟨-1, ?_⟩
    apply Units.ext
    simp [hgneg]

/-- With just the trivial norm-one character, any element of the product is represented
by a test function in its sole coordinate. Thus the product map has closed range. -/
private theorem sLocalThetaToHomogeneousProduct_isClosed_of_subsingleton
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hG : Subsingleton (sIdeleQuotientNorm F S).ker) :
    IsClosed (Set.range (exists_sLocalThetaToHomogeneousProduct (F := F) (S := S)).choose) := by
  let P := (exists_sLocalThetaToHomogeneousProduct (F := F) (S := S)).choose
  suffices hs : Surjective P by
    exact (congrArg IsClosed hs.range_eq).mpr isClosed_univ
  let χ₀ : PontryaginDual (sIdeleQuotientNorm F S).ker := 1
  have hχ (χ : PontryaginDual (sIdeleQuotientNorm F S).ker) : χ = χ₀ := by
    apply PontryaginDual.ext
    intro g
    rw [hG.allEq g 1, map_one, map_one]
  intro y
  let K := LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S χ₀)
  let f := (K.mkQ_surjective (y χ₀)).choose
  have hf : K.mkQ f = y χ₀ := (K.mkQ_surjective (y χ₀)).choose_spec
  let x := (sLocalAdelicTheta F S).ker.mkQ f
  have hx := (exists_sLocalThetaToHomogeneousProduct (F := F) (S := S)).choose_spec.2 f χ₀
  refine ⟨x, ?_⟩
  funext χ
  exact (congrArg (fun i ↦ P x i = y i) (hχ χ)).mpr (hx.trans hf)

/-- Paper: Remark 6.2.1.4(2), p. 298. Take ℚ and the archimedean stage. The norm-one quotient
is trivial, and projection to the sole factor identifies the product map with the identity on
the theta quotient. The range is closed and the induced topology is the intrinsic topology. -/
theorem Printed.sLocalThetaToHomogeneousProduct_strictlyCoarser_nonclosed_false :
    ¬ Printed.sLocalThetaToHomogeneousProduct_strictlyCoarser_nonclosed := by
  intro h
  exact (h ℚ ∅).2 (sLocalThetaToHomogeneousProduct_isClosed_of_subsingleton ℚ ∅
    sLocalThetaToHomogeneousProduct_normOne_rat)

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

open NumberFieldKB.Chebotarev.RatIdele in
/-- The idelic character of a Dirichlet character modulo 5, at the idele with `2` at the place
over 5 and `1` elsewhere, is the inverse of the character value at `2`. -/
private theorem Printed.finiteStandardGaussian_zeta_of_ramified_positive_false_two
    (χ : DirichletCharacter ℂ 5) (v : Pl) (hv : pr v = 5) (u : (v.adicCompletion ℚ)ˣ)
    (hu : (u : v.adicCompletion ℚ) = ((2 : ℕ) : v.adicCompletion ℚ)) :
    ((ideleChar 5 χ (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) : ℂˣ) : ℂ) =
      (χ (2 : ZMod 5))⁻¹ := by
  have hval : Valued.v (u : v.adicCompletion ℚ) = WithZero.exp (-(0 : ℤ)) := by
    rw [neg_zero, WithZero.exp_zero, hu, ← Rat.cast_natCast, valued_ratCast,
      ← map_natCast (algebraMap (𝓞 ℚ) ℚ) 2,
      IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem, natCast_mem_asIdeal_iff, hv]
    norm_num
  have hq : ratPart (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = 1 := by
    rw [ratPart_ofAdicCompletion v u 0 hval, zpow_zero]
  have hU : unitPart (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) =
      IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u := by
    rw [unitPart_apply, hq, map_one, inv_one, mul_one]
  have hr : resMod 5 (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = (2 : ZMod 5) := by
    rw [resMod_apply, resModFun, hU]
    refine (ZMod.equivPi 5 (NeZero.ne 5)).symm_apply_eq.mpr (funext fun q ↦ ?_)
    have hq5 : (q : ℕ) = 5 :=
      (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors q.2) Nat.prime_five).mp
        (Nat.dvd_of_mem_primeFactors q.2)
    have hqN : (q : ℕ) ^ (5 : ℕ).factorization q ∣ 5 := Nat.ordProj_dvd 5 q
    have hcomp : ZMod.equivPi 5 (NeZero.ne 5) (2 : ZMod 5) q =
        ZMod.castHom hqN (ZMod ((q : ℕ) ^ (5 : ℕ).factorization q)) (2 : ZMod 5) :=
      RingHom.congr_fun (Subsingleton.elim ((Pi.evalRingHom _ q).comp
        (ZMod.equivPi 5 (NeZero.ne 5)).toRingHom) (ZMod.castHom hqN _)) (2 : ZMod 5)
    rw [hcomp, map_ofNat]
    have hqv : placeP 5 q = v := pr_injective (by rw [placeP, pr_placeOf, hq5, hv])
    subst hqv
    rw [compV_ofAdicCompletion_self]
    erw [hu, redP_natCast]
    rfl
  rw [coe_ideleChar, MulChar.coe_toUnitHom, MonoidHom.coe_toHomUnits, hr]

/-- Paper: Theorem 6.2.2.1, first numbered definition, p. 298. Over ℚ take the even quadratic
idele class character modulo 5, S consisting of the infinite place and 5, and the unitary local
character at 5 as d. Its abscissa is zero. The standard test is its conjugate on the integer
units, so the integrand is their indicator and the integral is their positive mass. -/
theorem Printed.finiteStandardGaussian_zeta_of_ramified_positive_false :
    ¬ Printed.finiteStandardGaussian_zeta_of_ramified_positive := by
  classical
  intro h
  let v5 : Places(ℚ) := NumberFieldKB.Chebotarev.RatIdele.placeOf 5 Nat.prime_five
  have hv5 : NumberFieldKB.Chebotarev.RatIdele.pr v5 = 5 := NumberFieldKB.Chebotarev.RatIdele.pr_placeOf 5 Nat.prime_five
  let S : Finset Places(ℚ) := {v5}
  -- A character modulo 5 that is nontrivial at 2.
  obtain ⟨χ, hχ2⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (ZMod 5) ℂ
    (a := (2 : ZMod 5)) (by decide)
  -- The idelic character and its norm-one restriction.
  let H : HeckeCharacter (𝓞 ℚ) ℚ := (⟨Units.coeHom ℂ, Units.continuous_val⟩ : ℂˣ →ₜ* ℂ).comp
    (NumberFieldKB.Chebotarev.RatIdele.ratDirichletChar 5 χ)
  have hH (x : IdeleClassGroup (𝓞 ℚ) ℚ) : ‖H x‖ = 1 := by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    change ‖((NumberFieldKB.Chebotarev.RatIdele.ideleChar 5 χ y : ℂˣ) : ℂ)‖ = 1
    rw [NumberFieldKB.Chebotarev.RatIdele.coe_ideleChar, norm_inv, MulChar.coe_toUnitHom,
      DirichletCharacter.unit_norm_eq_one χ, inv_one]
  let ψ : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ) :=
    ⟨{ toFun := fun x ↦ ⟨H x, mem_sphere_zero_iff_norm.2 (hH x)⟩
       map_one' := Circle.ext H.map_one
       map_mul' := fun x y ↦ Circle.ext (H.map_mul x y) }, H.continuous.subtype_mk _⟩
  let ω : PontryaginDual C₁(ℚ) :=
    ψ.comp ⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩
  have hHS : H ∈ unramifiedOutside ℚ S := by
    refine (mem_unramifiedOutside_iff ℚ S H).mpr fun v hv u ↦ ?_
    have hne : v ≠ v5 := fun e ↦ hv (e ▸ Finset.mem_singleton_self v5)
    have hcop : (NumberFieldKB.Chebotarev.RatIdele.pr v).Coprime 5 := by
      refine (Nat.coprime_primes (NumberFieldKB.Chebotarev.RatIdele.pr_prime v) Nat.prime_five).mpr fun e ↦ hne ?_
      exact NumberFieldKB.Chebotarev.RatIdele.pr_injective (e.trans hv5.symm)
    let x := Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom u
    have hx : Valued.v (x : v.adicCompletion ℚ) = 1 :=
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (a := x)).mp
        ⟨u.val.property, u.inv.property⟩
    change ((NumberFieldKB.Chebotarev.RatIdele.ideleChar 5 χ (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v x) : ℂˣ) : ℂ) = 1
    rw [NumberFieldKB.Chebotarev.RatIdele.ideleChar_unit 5 χ hcop x hx, Units.val_one]
  have hω : NormOneCharacterUnramifiedOutside ω S := ⟨⟨H, hHS⟩, fun _ ↦ rfl⟩
  have hPic : Subsingleton Picₛ(ℚ, S) := by
    have : IsPrincipalIdealRing (𝓞 ℚ) := classNumber_eq_one_iff.mp Rat.classNumber_eq
    have h0 : Subsingleton Picₛ(ℚ, (∅ : Finset Places(ℚ))) := by
      rw [Finset.coe_empty, integer_empty]
      let e := Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)
      let := IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
      infer_instance
    obtain ⟨_, _, _, hsurj, _⟩ := picard_localization_exact ℚ ∅ S (Finset.empty_subset S)
    exact hsurj.subsingleton
  let w : S := ⟨v5, Finset.mem_singleton_self v5⟩
  let c := sLocalFiniteRestriction w (sIdeleRestriction ℚ S hω.choose)
  -- Values of `c` on local units of norm one are values of `H`.
  have hcH (u : (L(ℚ, v5))ˣ) (hu : ‖(u : L(ℚ, v5))‖ = 1) :
      c u = ((NumberFieldKB.Chebotarev.RatIdele.ideleChar 5 χ (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v5 u) : ℂˣ) : ℂ) := by
    have hins := sIdeleInsertion_finiteUnit (F := ℚ) (S := S) w u
    have hmem : (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v5 u) ∈ (ideleClassNorm ℚ).ker := by
      rw [MonoidHom.mem_ker, ideleClassNorm_ofAdicCompletion]
      ext
      simpa using hu
    have hspec := hω.choose_spec ⟨_, hmem⟩
    change hω.choose.val (QuotientGroup.mk (sIdeleInsertion ℚ S _)) = _
    rw [hins]
    exact hspec
  -- An integer unit of `ℚ₅` on which `c` is not trivial.
  have hval2 : Valued.v ((2 : ℕ) : L(ℚ, v5)) = 1 := by
    rw [← Rat.cast_natCast, NumberFieldKB.Chebotarev.RatIdele.valued_ratCast,
      ← map_natCast (algebraMap (𝓞 ℚ) ℚ) 2,
      IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem,
      NumberFieldKB.Chebotarev.RatIdele.natCast_mem_asIdeal_iff, hv5]
    norm_num
  have h2ne : ((2 : ℕ) : L(ℚ, v5)) ≠ 0 := fun e ↦ by
    rw [e, map_zero] at hval2
    exact zero_ne_one hval2
  let u2 : (L(ℚ, v5))ˣ := Units.mk0 _ h2ne
  have hu2v : Valued.v (u2 : L(ℚ, v5)) = 1 := hval2
  have hu2U : u2 ∈ U(ℚ, v5) :=
    (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (a := u2)).mpr hu2v
  have hunorm (u : (L(ℚ, v5))ˣ) (hu : u ∈ U(ℚ, v5)) : ‖(u : L(ℚ, v5))‖ = 1 :=
    Valued.toNormedField.norm_eq_one_iff.mpr
      ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (a := u)).mp hu)
  have hcram : ∃ u ∈ U(ℚ, v5), c u ≠ 1 := by
    refine ⟨u2, hu2U, ?_⟩
    rw [hcH u2 (hunorm u2 hu2U),
      Printed.finiteStandardGaussian_zeta_of_ramified_positive_false_two χ v5 hv5 u2 rfl]
    exact fun e ↦ hχ2 (inv_eq_one.mp e)
  -- A local quasi-character agreeing with `c` on integer units and of abscissa zero.
  let σ0 : ℝ := if hσ : ∃ σ : ℝ, 0 < σ ∧ ∀ g : (L(ℚ, v5))ˣ, ‖c g‖ = ‖(g : L(ℚ, v5))‖ ^ σ then
    hσ.choose else 0
  let tw : QuasiCharacter (L(ℚ, v5))ˣ :=
    ⟨{ toFun := fun g ↦ ((‖(g : L(ℚ, v5))‖ ^ (-σ0) : ℝ) : ℂ)
       map_one' := by simp
       map_mul' := fun g g' ↦ by
         rw [Units.val_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
           Complex.ofReal_mul] },
      Complex.continuous_ofReal.comp ((continuous_norm.comp Units.continuous_val).rpow_const
        fun g ↦ Or.inl (norm_ne_zero_iff.mpr g.ne_zero))⟩
  let d : QuasiCharacter (L(ℚ, v5))ˣ := c * tw
  have hdg (g : (L(ℚ, v5))ˣ) : d g = c g * ((‖(g : L(ℚ, v5))‖ ^ (-σ0) : ℝ) : ℂ) := rfl
  have hdc : ∀ u ∈ U(ℚ, v5), d u = c u := fun u hu ↦ by
    rw [hdg, hunorm u hu, Real.one_rpow, Complex.ofReal_one, mul_one]
  have hdσ : ¬ ∃ σ : ℝ, 0 < σ ∧ ∀ g : (L(ℚ, v5))ˣ, ‖d g‖ = ‖(g : L(ℚ, v5))‖ ^ σ := by
    rintro ⟨σ, hσpos, hd⟩
    by_cases hσ : ∃ σ : ℝ, 0 < σ ∧ ∀ g : (L(ℚ, v5))ˣ, ‖c g‖ = ‖(g : L(ℚ, v5))‖ ^ σ
    · have hσ0 : σ0 = hσ.choose := dite_eq_left hσ
      let val : Valuation (L(ℚ, v5)) (WithZero (Multiplicative ℤ)) := Valued.v
      have hπ := val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec
      let π : (L(ℚ, v5))ˣ := Units.mk0 _ hπ.ne_zero
      have hπn : ‖(π : L(ℚ, v5))‖ = 5⁻¹ := by
        rw [Units.val_mk0, norm_uniformizer_adicCompletion v5 _ hπ,
          NumberFieldKB.Chebotarev.RatIdele.absNorm_asIdeal, hv5]
        norm_num
      have h1 := hd π
      rw [hdg, norm_mul, hσ.choose_spec.2 π, ← hσ0, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
        ← Real.rpow_add (norm_pos_iff.mpr π.ne_zero), add_neg_cancel, Real.rpow_zero, hπn] at h1
      have h2 : (5⁻¹ : ℝ) ^ σ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hσpos
      linarith
    · have hσ0 : σ0 = 0 := dite_eq_right hσ
      refine hσ ⟨σ, hσpos, fun g ↦ ?_⟩
      rw [← hd g, hdg, hσ0, neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]
  -- The printed formula and the corrected one disagree.
  have hP := h ℚ S hPic ω hω w d hcram
  have hT := (finiteStandardGaussian_zeta_of_ramified v5 c d hcram).2
  rw [ite_eq_left hdc] at hT
  rw [ite_eq_right (fun hh ↦ hdσ hh.2)] at hP
  have hpos : 0 < ((μ(ℚ, v5)) U(ℚ, v5)).toReal := by
    let : CompactSpace O(ℚ, v5) := compactSpace_adicCompletionIntegers v5
    let : BorelSpace (L(ℚ, v5))ˣ := ⟨rfl⟩
    let : (μ(ℚ, v5)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v5
    exact ENNReal.toReal_pos ((Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measure_pos
      _ ⟨1, (O(ℚ, v5)).units.one_mem⟩).ne' (Submonoid.units_isCompact
        (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v5))).measure_ne_top
  exact hpos.ne' (by exact_mod_cast hT.symm.trans hP)

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

/-- Over ℚ every ring of S-integers has trivial Picard group: it is a localization of `𝓞 ℚ`,
which is a principal ideal domain. -/
private theorem sLocalStandardThetaTensor_factorization_false_pic (S : Finset (Places(ℚ))) :
    Subsingleton Picₛ(ℚ, S) := by
  have : IsPrincipalIdealRing (𝓞 ℚ) := classNumber_eq_one_iff.mp Rat.classNumber_eq
  have hs := picMapAlgebra_surjective_of_isLocalization
    (Localization.submonoid (S : Set (Places(ℚ)))) (R := 𝓞 ℚ)
    (A := (S : Set (Places(ℚ))).integer ℚ)
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨a', rfl⟩ := hs a
  obtain ⟨b', rfl⟩ := hs b
  rw [Subsingleton.elim a' b']

/-- The trivial norm-one character is unramified outside any set of places. -/
private theorem sLocalStandardThetaTensor_factorization_false_unramified
    (S : Finset (Places(ℚ))) :
    NormOneCharacterUnramifiedOutside (1 : PontryaginDual C₁(ℚ)) S :=
  ⟨⟨1, (mem_unramifiedOutside_iff ℚ S 1).mpr fun _ _ _ ↦ rfl⟩, fun _ ↦ rfl⟩

/-- The descent of the trivial norm-one character is trivial. -/
private theorem sLocalStandardThetaTensor_factorization_false_descent
    (S : Finset (Places(ℚ))) (hω : NormOneCharacterUnramifiedOutside (1 : PontryaginDual C₁(ℚ)) S) :
    sLocalNormOneCharacter S (1 : PontryaginDual C₁(ℚ)) hω = 1 :=
  ((normOneCharacterUnramifiedOutside_iff (F := ℚ) (S := S) 1).mp hω).unique
    ((normOneCharacterUnramifiedOutside_iff (F := ℚ) (S := S) 1).mp hω).exists.choose_spec
    (fun _ _ _ _ _ ↦ rfl)

/-- Over ℚ the constant family `1` lists representatives of the (trivial) class group. -/
private theorem sLocalStandardThetaTensor_factorization_false_classes (S : Finset (Places(ℚ))) :
    ClassRepresentatives(ℚ, S, fun _ : Fin (classNumber ℚ) ↦ (1 : Nₛ(ℚ, S))) := by
  have : IsPrincipalIdealRing (𝓞 ℚ) := classNumber_eq_one_iff.mp Rat.classNumber_eq
  refine ⟨rfl, ⟨fun a b _ ↦ ?_, fun c ↦ ⟨⟨0, classNumber_pos ℚ⟩, Subsingleton.elim _ _⟩⟩⟩
  have ha := a.isLt
  have hb := b.isLt
  have hc := Rat.classNumber_eq
  exact Fin.ext (by omega)

/-- The archimedean test `(q² - t²) exp(-t²)` on the infinite adeles of ℚ, written in terms of
the norm of the real coordinate. -/
private theorem sLocalStandardThetaTensor_factorization_false_arch (q : ℝ) :
    ∃ f : ℬ∞(ℚ), ∀ x : InfiniteAdeleRing ℚ, f (Multiplicative.ofAdd x) =
      (((q ^ 2 - ‖x Rat.infinitePlace‖ ^ 2) * Real.exp (-‖x Rat.infinitePlace‖ ^ 2) : ℝ) : ℂ) := by
  let g0 : SchwartzMap ℝ ℝ := SchwartzMap.gaussian 1 zero_lt_one
  let g : SchwartzMap ℝ ℂ := SchwartzMap.postcompCLM Complex.ofRealCLM g0
  let h1 : SchwartzMap ℝ ℂ := SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)) g
  let h2 : SchwartzMap ℝ ℂ := SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)) h1
  let b : SchwartzMap ℝ ℂ := ((q : ℂ) ^ 2) • g - h2
  have hg : ∀ x : ℝ, g x = (Real.exp (-(x ^ 2)) : ℂ) := by
    intro x
    simp [g, g0, SchwartzMap.postcompCLM_apply, SchwartzMap.gaussian_apply]
  have hb : ∀ x : ℝ, b x = (((q ^ 2 - x ^ 2) * Real.exp (-x ^ 2) : ℝ) : ℂ) := by
    intro x
    have e1 : h1 x = (x : ℂ) * g x := by
      change SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)) g x = _
      rw [SchwartzMap.smulLeftCLM_apply_apply Complex.hasTemperateGrowth_ofReal]
      rfl
    have e2 : h2 x = (x : ℂ) * h1 x := by
      change SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)) h1 x = _
      rw [SchwartzMap.smulLeftCLM_apply_apply Complex.hasTemperateGrowth_ofReal]
      rfl
    change ((q : ℂ) ^ 2) * g x - h2 x = _
    rw [e2, e1, hg]
    push_cast
    ring_nf
  obtain ⟨T, hT⟩ := realSchwartzBruhat_equiv
  let realEquiv := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  let realIso := InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  let eInfHomeo : InfiniteAdeleRing ℚ ≃ₜ ℝ :=
    (Homeomorph.piUnique fun w : InfinitePlace ℚ ↦ w.Completion).trans realIso.toHomeomorph
  let eArch : Multiplicative (InfiniteAdeleRing ℚ) ≃ₜ* Multiplicative ℝ :=
    { toEquiv :=
        { toFun := fun x ↦ Multiplicative.ofAdd (realEquiv (x.toAdd Rat.infinitePlace))
          invFun := fun y ↦ Multiplicative.ofAdd (eInfHomeo.symm y.toAdd)
          left_inv := fun x ↦ by
            apply congrArg Multiplicative.ofAdd
            exact eInfHomeo.symm_apply_apply x.toAdd
          right_inv := fun y ↦ by
            apply congrArg Multiplicative.ofAdd
            exact eInfHomeo.apply_symm_apply y.toAdd }
      map_mul' := fun x y ↦ congrArg Multiplicative.ofAdd (map_add realEquiv _ _)
      continuous_toFun := eInfHomeo.continuous
      continuous_invFun := eInfHomeo.symm.continuous }
  have : T2Space (Multiplicative (InfiniteAdeleRing ℚ)) := eArch.isEmbedding.t2Space
  have : LocallyCompactSpace (Multiplicative (InfiniteAdeleRing ℚ)) :=
    eArch.isOpenEmbedding.locallyCompactSpace
  have : T2Space (Multiplicative ℝ) := inferInstanceAs (T2Space ℝ)
  have : LocallyCompactSpace (Multiplicative ℝ) := inferInstanceAs (LocallyCompactSpace ℝ)
  refine ⟨⟨(T b).val ∘ eArch, schwartzBruhat_mem_comp_equiv eArch (T b).property⟩, fun x ↦ ?_⟩
  have hnorm : ‖realEquiv (x Rat.infinitePlace)‖ = ‖x Rat.infinitePlace‖ :=
    realIso.isometry.norm_map_of_map_zero (map_zero realEquiv) _
  change (T b) (Multiplicative.ofAdd (realEquiv (x Rat.infinitePlace))) = _
  rw [hT b, hb, ← hnorm, Real.norm_eq_abs, sq_abs]

/-- The indicator of the sphere of radius `‖π‖ = q⁻¹` is a punctured finite test. -/
private theorem sLocalStandardThetaTensor_factorization_false_fin (v : Places(ℚ)) (r : ℝ)
    (hr : r ≠ 0) :
    ∃ fv : finitePuncturedThetaTestSpace v, ∀ z : L(ℚ, v),
      fv.val (Multiplicative.ofAdd z) = if ‖z‖ = r then 1 else 0 := by
  classical
  let : ProperSpace (L(ℚ, v)) := properSpace_adicCompletion v
  have hloc : IsLocallyConstant (fun z : L(ℚ, v) ↦ if ‖z‖ = r then (1 : ℂ) else 0) := by
    have hs : IsClopen (Metric.sphere (0 : L(ℚ, v)) r) := IsUltrametricDist.isClopen_sphere (0 : L(ℚ, v)) hr
    have hlc :=
      (LocallyConstant.indicator (LocallyConstant.const (L(ℚ, v)) (1 : ℂ)) hs).isLocallyConstant
    convert hlc using 1
    funext z
    change _ = Set.indicator _ _ z
    simp [Set.indicator_apply, mem_sphere_iff_norm]
  have hcpt : HasCompactSupport (fun z : L(ℚ, v) ↦ if ‖z‖ = r then (1 : ℂ) else 0) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : L(ℚ, v)) |r|) fun z hz ↦ ?_
    refine ite_eq_right_iff.mpr fun h ↦ absurd ?_ hz
    simpa [h] using le_abs_self r
  obtain ⟨g, hg⟩ := (mem_finitePlaceSchwartz_iff ℚ v _).mpr ⟨hloc, hcpt⟩
  refine ⟨⟨g, ?_⟩, hg⟩
  rw [mem_finitePuncturedThetaTestSpace, hg, norm_zero]
  exact ite_eq_right_iff.mpr fun h ↦ absurd h.symm hr

/-- Norm-one condition at the archimedean stage of ℚ. -/
private theorem sLocalStandardThetaTensor_factorization_false_normEmpty
    (y : Iₛ(ℚ, (∅ : Finset (Places(ℚ))))) (hy : sIdeleNorm ℚ ∅ y = 1) :
    ‖y.val.1 Rat.infinitePlace‖ = 1 := by
  have h := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) hy
  rwa [sIdeleNorm, Finset.univ_eq_empty (α := (∅ : Finset (Places(ℚ)))),
    Finset.prod_empty, mul_one, Fintype.prod_subsingleton _ Rat.infinitePlace,
    Rat.isReal_infinitePlace.mult_eq_one, pow_one] at h

/-- Norm-one condition at the stage with one finite place over ℚ. -/
private theorem sLocalStandardThetaTensor_factorization_false_normSingle (v : Places(ℚ))
    (y : Iₛ(ℚ, ({v} : Finset (Places(ℚ))))) (hy : sIdeleNorm ℚ {v} y = 1) :
    ‖y.val.1 Rat.infinitePlace‖ * ‖y.val.2 ⟨v, Finset.mem_singleton_self v⟩‖ = 1 := by
  have : Subsingleton ({v} : Finset (Places(ℚ))) :=
    ⟨fun a b ↦ Subtype.ext ((Finset.mem_singleton.mp a.2).trans (Finset.mem_singleton.mp b.2).symm)⟩
  have h := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) hy
  rwa [sIdeleNorm, Fintype.prod_subsingleton _ Rat.infinitePlace,
    Rat.isReal_infinitePlace.mult_eq_one, pow_one,
    Fintype.prod_subsingleton _ ⟨v, Finset.mem_singleton_self v⟩] at h

/-- The norm-one archimedean ideles of ℚ are `±1`, a finite group. -/
private theorem sLocalStandardThetaTensor_factorization_false_finite :
    Finite Nₛ(ℚ, (∅ : Finset (Places(ℚ)))) := by
  let realEquiv := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  let realIso := InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
  have hmem (g : Nₛ(ℚ, (∅ : Finset (Places(ℚ))))) :
      realEquiv (g.val.val.1 Rat.infinitePlace) ∈ ({1, -1} : Set ℝ) := by
    have hn := sLocalStandardThetaTensor_factorization_false_normEmpty g.val
      (MonoidHom.mem_ker.mp g.property)
    have hnorm : ‖realEquiv (g.val.val.1 Rat.infinitePlace)‖ = ‖g.val.val.1 Rat.infinitePlace‖ :=
      realIso.isometry.norm_map_of_map_zero (map_zero realEquiv) _
    rw [hn, Real.norm_eq_abs] at hnorm
    rcases eq_or_eq_neg_of_abs_eq hnorm with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine Finite.of_injective (β := ({1, -1} : Set ℝ)) (fun g ↦ ⟨_, hmem g⟩) fun a b hab ↦ ?_
  have h1 : a.val.val.1 Rat.infinitePlace = b.val.val.1 Rat.infinitePlace :=
    realEquiv.injective (congrArg Subtype.val hab)
  have h2 : a.val.val.1 = b.val.val.1 := funext fun w ↦ by
    rw [Subsingleton.elim w Rat.infinitePlace]
    exact h1
  have h3 : a.val.val.2 = b.val.val.2 := funext fun w ↦ absurd w.2 (Finset.notMem_empty _)
  exact Subtype.ext (Units.ext (Prod.ext h2 h3))

/-- A Haar measure on a finite group has finite positive total mass. -/
private theorem sLocalStandardThetaTensor_factorization_false_mass {G : Type*} [Group G]
    [TopologicalSpace G] [Finite G] {m : MeasurableSpace G} (ν : Measure G)
    (hH : @Measure.IsHaarMeasure G _ _ m ν) : ν.real Set.univ ≠ 0 := by
  have : CompactSpace G := Finite.compactSpace
  have : IsFiniteMeasure ν := CompactSpace.isFiniteMeasure
  exact ENNReal.toReal_ne_zero.mpr
    ⟨Measure.measure_univ_ne_zero.mpr (NeZero.ne ν), measure_ne_top ν _⟩

/-- Paper: Theorem 6.2.2.1(1), (6.2.2.7)–(6.2.2.10), pp. 299–301. Over ℚ take S with one finite
prime p, the trivial character, the identity class representative, and x = 1. Use the finite
indicator of `pℤₚˣ` and an even nonnegative smooth compactly supported function positive at ±1
and supported away from ±p. The norm-one integral is zero since the finite support forces the
inverse real component to have absolute value p. The separate factors are both positive. -/
theorem Printed.sLocalStandardThetaTensor_factorization_false :
    ¬ Printed.sLocalStandardThetaTensor_factorization := by
  classical
  intro h
  let v : Places(ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩
  let S : Finset (Places(ℚ)) := {v}
  let v' : S := ⟨v, Finset.mem_singleton_self v⟩
  have : Subsingleton S :=
    ⟨fun a b ↦ Subtype.ext ((Finset.mem_singleton.mp a.2).trans (Finset.mem_singleton.mp b.2).symm)⟩
  let q : ℝ := (v.asIdeal.absNorm : ℝ)
  have hq : 2 ≤ q := by
    have h0 : v.asIdeal.absNorm ≠ 0 := fun h0 ↦ v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
    have h1 : v.asIdeal.absNorm ≠ 1 := fun h1 ↦ v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h1)
    have h2 : 2 ≤ v.asIdeal.absNorm := by omega
    have h3 := (Nat.cast_le (α := ℝ)).mpr h2
    rwa [Nat.cast_ofNat] at h3
  obtain ⟨f, hf⟩ := sLocalStandardThetaTensor_factorization_false_arch q
  have hq0 : q⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  let G : ∀ w : Places(ℚ), finitePuncturedThetaTestSpace w := fun w ↦
    (sLocalStandardThetaTensor_factorization_false_fin w q⁻¹ hq0).choose
  have hfv₀ := (sLocalStandardThetaTensor_factorization_false_fin v q⁻¹ hq0).choose_spec
  have hω := sLocalStandardThetaTensor_factorization_false_unramified S
  have hdesc := sLocalStandardThetaTensor_factorization_false_descent S hω
  have key := h ℚ S (sLocalStandardThetaTensor_factorization_false_pic S) 1 hω 1
    (fun g y _ ↦ by rw [hdesc]; rfl) (fun _ ↦ 1)
    (sLocalStandardThetaTensor_factorization_false_classes S) f (fun w ↦ G w.val) 1
  dsimp only at key
  have hL : ∀ g : Nₛ(ℚ, S), f (Multiplicative.ofAdd (g.val⁻¹ * 1).val.1) *
      (∏ w : S, (G w.val).val (Multiplicative.ofAdd ((g.val⁻¹ * 1).val.2 w))) *
      ((1 : PontryaginDual Iₛ(ℚ, S)) g.val : ℂ) = 0 := by
    intro g
    have hy : sIdeleNorm ℚ S (g.val⁻¹ * 1) = 1 := by
      rw [mul_one, map_inv, MonoidHom.mem_ker.mp g.property, inv_one]
    have hn := sLocalStandardThetaTensor_factorization_false_normSingle v _ hy
    rw [Fintype.prod_subsingleton _ v', hfv₀]
    split_ifs with hz
    · have h1 : ‖(g.val⁻¹ * 1).val.1 Rat.infinitePlace‖ = q := by
        have hz' : ‖(g.val⁻¹ * 1).val.2 ⟨v, Finset.mem_singleton_self v⟩‖ = q⁻¹ := hz
        rw [hz'] at hn
        have hq0 : q ≠ 0 := by linarith
        field_simp at hn
        linarith
      rw [hf, h1]
      simp
    · simp
  simp only [hL, integral_zero] at key
  refine absurd key (Ne.symm (mul_ne_zero ?_ ?_))
  · -- the archimedean average is a positive multiple of the norm-one mass
    let ν := sNormOneIdeleTamagawaMeasure ℚ ∅
    let c : ℂ := (((q ^ 2 - 1) * Real.exp (-1) : ℝ) : ℂ)
    refine ne_of_eq_of_ne (?_ : _ = ∑ _k : Fin (classNumber ℚ), ∫ _g, c ∂ν) ?_
    · rw [infiniteStandardThetaAverage_apply]
      refine Finset.sum_congr rfl fun k _ ↦ integral_congr_ae
        (Filter.Eventually.of_forall fun g ↦ ?_)
      dsimp only
      have hy : sIdeleNorm ℚ ∅ g.val⁻¹ = 1 := by
        rw [map_inv, MonoidHom.mem_ker.mp g.property, inv_one]
      have hn := sLocalStandardThetaTensor_factorization_false_normEmpty _ hy
      rw [hf]
      simp only [OneMemClass.coe_one, map_one, one_mul, mul_one, ← map_inv, Units.coe_map,
        PontryaginDual.one_apply, Circle.coe_one]
      rw [show ‖((RingHom.fst (InfiniteAdeleRing ℚ)
          ((w : (∅ : Finset (Places(ℚ)))) → L(ℚ, w.val))).toMonoidHom ((g.val)⁻¹ : Iₛ(ℚ, ∅)).val)
          Rat.infinitePlace‖ = 1 from hn]
      simp [c]
    · rw [integral_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Rat.classNumber_eq, one_smul]
      have : Finite Nₛ(ℚ, (∅ : Finset (Places(ℚ)))) :=
        sLocalStandardThetaTensor_factorization_false_finite
      refine smul_ne_zero ?_ ?_
      · exact sLocalStandardThetaTensor_factorization_false_mass ν
          (sNormOneIdeleTamagawaMeasure_existsUnique ℚ ∅).exists.choose_spec.1
      · refine Complex.ofReal_ne_zero.mpr (mul_ne_zero ?_ (Real.exp_pos _).ne')
        nlinarith
  · -- the finite factor is the mass of the elements of norm `q`
    rw [Fintype.prod_subsingleton _ v']
    let μ := finiteLocalMultiplicativeTamagawaMeasure ℚ v
    let T : Set (L(ℚ, v))ˣ := {g | ‖g.val‖ = q}
    have : BorelSpace (L(ℚ, v))ˣ := ⟨rfl⟩
    have hTm : MeasurableSet T :=
      (isClosed_eq (continuous_norm.comp Units.continuous_val) continuous_const).measurableSet
    refine ne_of_eq_of_ne (?_ : _ = ∫ g, T.indicator (fun _ ↦ (1 : ℂ)) g ∂μ) ?_
    · refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
      change (G v).val (Multiplicative.ofAdd ((g⁻¹).val * (1 : Iₛ(ℚ, S)).val.2 v')) * _ = _
      rw [Units.val_one, Prod.snd_one, Pi.one_apply, mul_one, hfv₀]
      simp only [PontryaginDual.one_apply, Circle.coe_one, mul_one, Set.indicator_apply, T,
        Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, norm_inv, inv_inj]
    · have : μ.IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := ℚ) v
      obtain ⟨π, hπ⟩ :=
        (Valued.v (R := L(ℚ, v))).exists_isUniformizer_of_isCyclic_of_nontrivial
      have hπn : ‖π‖ = q⁻¹ := norm_uniformizer_adicCompletion (K := ℚ) v π hπ
      let u : (L(ℚ, v))ˣ := Units.mk0 π hπ.ne_zero
      have hT : T = (fun h ↦ u * h) ⁻¹' ((v.adicCompletionIntegers ℚ).units : Set (L(ℚ, v))ˣ) := by
        ext h
        change ‖h.val‖ = q ↔ u * h ∈ (v.adicCompletionIntegers ℚ).units
        rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
          ← Valued.toNormedField.norm_eq_one_iff, Units.val_mul, norm_mul]
        change ‖h.val‖ = q ↔ ‖π‖ * ‖h.val‖ = 1
        rw [hπn]
        have hq0 : q ≠ 0 := by linarith
        constructor
        · intro e; rw [e, inv_mul_cancel₀ hq0]
        · intro e; field_simp at e; linarith
      rw [integral_indicator_const _ hTm, Measure.real, hT, measure_preimage_mul,
        finiteLocalMultiplicativeTamagawaMeasure_integerUnits]
      refine smul_ne_zero (ENNReal.toReal_ne_zero.mpr ⟨?_, ?_⟩) one_ne_zero
      · exact ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
      · refine ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr ?_)).ne'
        have h0 : v.asIdeal.absNorm ≠ 0 := fun h0 ↦ v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)
        positivity

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

section InverseAverageCounterexample

open scoped ENNReal ContDiff
open Set

local notation "I₀(" F ")" => (SAdeleRing F ∅)ˣ
local notation "N₀(" F ")" => (sIdeleNorm F ∅).ker
local notation "J₀(" F ")" => SIdeleQuotient F ∅
local notation "J₁₀(" F ")" => (sIdeleQuotientNorm F ∅).ker
local notation "archPart(" F ")" => Units.map (RingHom.fst (InfiniteAdeleRing F)
  (∀ v : (∅ : Finset Places(F)), L(F, v.val))).toMonoidHom
local notation "archInsert(" F ")" => Units.map (MonoidHom.inl (InfiniteAdeleRing F)
  (∀ v : (∅ : Finset Places(F)), L(F, v.val)))

open IsCyclotomicExtension.Rat NumberField.InfinitePlace in
/-- The discriminant and Minkowski bound give class number one for the Gaussian field. -/
private theorem inverseAverage_gaussianClassNumber :
    NumberField.classNumber (CyclotomicField 4 ℚ) = 1 := by
  let K := CyclotomicField 4 ℚ
  have hK : IsCyclotomicExtension {4} ℚ K := CyclotomicField.isCyclotomicExtension 4 ℚ
  have : IsCyclotomicExtension {2 ^ (1 + 1)} ℚ K := hK
  change NumberField.classNumber K = 1
  apply NumberField.classNumber_eq_one_iff.mpr
  apply NumberField.RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  have hdisc : NumberField.discr K = -4 := by
    simpa using discr_prime_pow_succ 2 1 K
  rw [hdisc, IsCyclotomicExtension.Rat.finrank 4 K, nrComplexPlaces_eq_totient_div_two 4]
  have hφ : Nat.totient 4 = 2 := by decide
  rw [hφ]
  norm_num [Nat.factorial]
  nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]

local notation "GField" => CyclotomicField 4 ℚ

/-- The Gaussian field has one infinite place and it is complex. -/
private theorem inverseAverage_gaussianPlace :
    ∃ w : InfinitePlace GField, w.IsComplex ∧ ∀ v : InfinitePlace GField, v = w := by
  let F := GField
  have : IsCyclotomicExtension {4} ℚ F := CyclotomicField.isCyclotomicExtension 4 ℚ
  have hcx := IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) F (by decide)
  have hn : InfinitePlace.nrComplexPlaces F = 1 := by
    rw [IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two 4]
    decide
  have hcard : Fintype.card (InfinitePlace F) = 1 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, hn,
      NumberField.IsTotallyComplex.nrRealPlaces_eq_zero F, zero_add]
  obtain ⟨w, hw⟩ := Fintype.card_eq_one_iff.mp hcard
  exact ⟨w, hcx.isComplex w, hw⟩

/-- Evaluation at the sole complex place identifies the archimedean ring with ℂ. -/
private theorem inverseAverage_archComplex {F : Type} [Field F] [NumberField F]
    (w : InfinitePlace F) (hw : w.IsComplex) (huniq : ∀ v : InfinitePlace F, v = w) :
    ∃ e : InfiniteAdeleRing F ≃+* ℂ,
      Continuous e ∧ Continuous e.symm ∧
      ∀ x, e x = InfinitePlace.Completion.extensionEmbedding w (x w) := by
  let : Unique (InfinitePlace F) := ⟨⟨w⟩, huniq⟩
  let e := (RingEquiv.piUnique fun v : InfinitePlace F ↦ v.Completion).trans
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)
  exact ⟨e, (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).continuous.comp
    (continuous_apply w), (Homeomorph.piUnique InfinitePlace.Completion).symm.continuous.comp
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous, fun _ ↦ rfl⟩

/-- On the stage without finite places the archimedean coordinate identifies ideles with ℂˣ. -/
private theorem inverseAverage_ideleComplex {F : Type} [Field F] [NumberField F]
    (e : InfiniteAdeleRing F ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm) :
    ∃ D : I₀(F) ≃ₜ* ℂˣ, ∀ g, (D g : ℂ) = e g.val.1 := by
  let R₀ := ∀ v : (∅ : Finset (Places(F))), L(F, v.val)
  let r : SAdeleRing F ∅ ≃+* ℂ := ((RingEquiv.prodZeroRing (InfiniteAdeleRing F) R₀).symm).trans e
  let r' : SAdeleRing F ∅ ≃ₜ* ℂ :=
    { r.toMulEquiv with
      continuous_toFun := he.comp continuous_fst
      continuous_invFun := he'.prodMk continuous_const }
  exact ⟨Units.mapContinuousMulEquiv r', fun _ ↦ rfl⟩

/-- The norm-one ideles are the complex unit circle in the sole complex coordinate. -/
private theorem inverseAverage_normOne_complex {F : Type} [Field F] [NumberField F]
    (w : InfinitePlace F) (hw : w.IsComplex) (huniq : ∀ v : InfinitePlace F, v = w)
    (e : InfiniteAdeleRing F ≃+* ℂ)
    (he : ∀ x, e x = InfinitePlace.Completion.extensionEmbedding w (x w)) (g : I₀(F)) :
    g ∈ (sIdeleNorm F ∅).ker ↔ ‖e g.val.1‖ = 1 := by
  let : Subsingleton (InfinitePlace F) := ⟨fun u v ↦ (huniq u).trans (huniq v).symm⟩
  have hnorm : ((sIdeleNorm F ∅ g).val : ℝ) = ‖e g.val.1‖ ^ 2 := by
    rw [he]
    have hcomp := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) (g.val.1 w)
    rw [hcomp]
    simp only [sIdeleNorm, Finset.univ_eq_empty (α := (∅ : Finset (Places(F)))),
      Finset.prod_empty, mul_one, Fintype.prod_subsingleton _ w]
    rw [hw.mult_eq_two]
    rfl
  rw [MonoidHom.mem_ker, ← Units.val_inj, ← NNReal.coe_inj, Units.val_one, NNReal.coe_one, hnorm,
    pow_two, mul_self_eq_one_iff]
  exact ⟨fun h ↦ h.resolve_right (by linarith [norm_nonneg (e g.val.1)]), Or.inl⟩

/-- The circle inclusion into the complex unit group is continuous. -/
private theorem inverseAverage_unitsCircle_continuous : Continuous Circle.toUnits := by
  apply Units.isEmbedding_val₀.isInducing.continuous_iff.mpr
  exact continuous_subtype_val

/-- Compactness of the archimedean norm-one group follows from its parametrization by
the unit circle. -/
private theorem inverseAverage_normOne_compact {F : Type} [Field F] [NumberField F]
    (e : InfiniteAdeleRing F ≃+* ℂ) (D : I₀(F) ≃ₜ* ℂˣ)
    (hD : ∀ g, (D g : ℂ) = e g.val.1)
    (hn : ∀ g : I₀(F), g ∈ (sIdeleNorm F ∅).ker ↔ ‖e g.val.1‖ = 1) :
    CompactSpace N₀(F) := by
  apply isCompact_iff_compactSpace.mp
  have h : (↑(sIdeleNorm F ∅).ker : Set I₀(F)) = Set.range (fun z : Circle ↦ D.symm (Circle.toUnits z)) := by
    ext g
    rw [SetLike.mem_coe, hn, ← hD]
    constructor
    · intro hg
      let z : Circle := ⟨D g, mem_sphere_zero_iff_norm.mpr hg⟩
      exact ⟨z, D.injective (by rw [D.apply_symm_apply]; exact Units.ext rfl)⟩
    · rintro ⟨z, rfl⟩
      rw [D.apply_symm_apply]
      exact Circle.norm_coe z
  rw [h]
  exact isCompact_range (D.symm.continuous.comp inverseAverage_unitsCircle_continuous)

/-- The normalized power sends a nonzero complex number to its angular character. -/
private theorem inverseAverage_phase (k : ℕ) :
    ∃ χ : PontryaginDual ℂˣ, ∀ z, (χ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ k := by
  have hn (z : ℂˣ) : (‖(z : ℂ)‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.ne_zero)
  let value (z : ℂˣ) : ℂ := ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ k
  have hv (z : ℂˣ) : value z ∈ Submonoid.unitSphere ℂ := by
    apply mem_sphere_zero_iff_norm.mpr
    simp only [value, norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr z.ne_zero), one_pow]
  have hc : Continuous value :=
    (Units.continuous_val.div (Complex.continuous_ofReal.comp (continuous_norm.comp Units.continuous_val)) hn).pow k
  exact ⟨{ toFun := fun z ↦ ⟨value z, hv z⟩
           map_one' := Circle.ext (by simp [value])
           map_mul' := fun x y ↦ Circle.ext (by
             change value (x * y) = value x * value y
             simp only [value, Units.val_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm, mul_pow])
           continuous_toFun := hc.subtype_mk hv }, fun _ ↦ rfl⟩

/-- A compactly supported radial bump times a monomial has the given rotation weight. -/
private theorem inverseAverage_weightedSchwartz (k : ℕ) :
    ∃ f : SchwartzMap ℂ ℂ, f 1 = 1 ∧
      ∀ (u z : ℂ), ‖u‖ = 1 → f (u * z) = u ^ k * f z := by
  let b : ContDiffBump (1 : ℝ) := default
  let g (z : ℂ) : ℂ := z ^ k * (b (Complex.normSq z) : ℂ)
  have hn : ContDiff ℝ ∞ Complex.normSq := by
    change ContDiff ℝ ∞ (fun z : ℂ ↦ z.re * z.re + z.im * z.im)
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hs : ContDiff ℝ ∞ g :=
    (contDiff_id.pow k).mul (Complex.ofRealCLM.contDiff.comp (b.contDiff.comp hn))
  have hc : HasCompactSupport g := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) (b.rOut + 2))
    intro z hz
    have hb : Complex.normSq z ∈ Function.support b := fun h ↦ hz (by
      have hzero : b (Complex.normSq z) = 0 := h
      simp [g, hzero])
    rw [b.support_eq, Metric.mem_ball, Real.dist_eq] at hb
    rw [Complex.normSq_eq_norm_sq] at hb
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [abs_lt.mp hb, sq_nonneg (‖z‖ - 1)]
  let f := hc.toSchwartzMap hs
  refine ⟨f, ?_, fun u z hu ↦ ?_⟩
  · change g 1 = 1
    simp [g, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
  · change g (u * z) = u ^ k * g z
    simp only [g, mul_pow, Complex.normSq_mul, Complex.normSq_eq_norm_sq u, hu, one_pow, one_mul,
      mul_assoc]

/-- Transport the weighted Schwartz function through the unique complex coordinate. -/
private theorem inverseAverage_archTest {F : Type} [Field F] [NumberField F]
    (w : InfinitePlace F) (hw : w.IsComplex) (huniq : ∀ v : InfinitePlace F, v = w)
    (e : InfiniteAdeleRing F ≃+* ℂ)
    (he : ∀ x, e x = InfinitePlace.Completion.extensionEmbedding w (x w))
    (k : ℕ) :
    ∃ f : ℬ∞(F), f (Multiplicative.ofAdd (1 : InfiniteAdeleRing F)) = 1 ∧
      ∀ (a x : InfiniteAdeleRing F), ‖e a‖ = 1 →
        f (Multiplicative.ofAdd (a * x)) = e a ^ k * f (Multiplicative.ofAdd x) := by
  classical
  let R := {v : InfinitePlace F // v.IsReal}
  let C := {v : InfinitePlace F // v.IsComplex}
  have : IsEmpty R := ⟨fun v ↦ (InfinitePlace.not_isReal_iff_isComplex.mpr hw) (huniq v.val ▸ v.property)⟩
  let : Unique C := ⟨⟨⟨w, hw⟩⟩, fun v ↦ Subtype.ext (huniq v.val)⟩
  let L : mixedEmbedding.mixedSpace F ≃L[ℝ] ℂ :=
    (ContinuousLinearEquiv.uniqueProd ℝ (C → ℂ) (R → ℝ)).trans
      (ContinuousLinearEquiv.piUnique ℝ (fun _ : C ↦ ℂ))
  have hL (a : InfiniteAdeleRing F) : L (InfiniteAdeleRing.ringEquiv_mixedSpace F a) = e a :=
    (he a).symm
  obtain ⟨s, h1, hs⟩ := inverseAverage_weightedSchwartz k
  let G (a : InfiniteAdeleRing F) := s (e a)
  let S := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L s
  let f : ℬ∞(F) :=
    ⟨G ∘ Multiplicative.toAdd, (mem_archimedeanSchwartzBruhat_iff G).mpr
      ⟨S, fun a ↦ congrArg s (hL a)⟩⟩
  refine ⟨f, ?_, fun a x ha ↦ ?_⟩
  · change s (e 1) = 1
    rw [map_one, h1]
  · change s (e (a * x)) = e a ^ k * s (e x)
    rw [map_mul, hs _ _ ha]

/-- An archimedean unit in the principal diagonal has angular order dividing
the order of the torsion subgroup of the integer unit group. -/
private theorem inverseAverage_diagonal_pow {F : Type} [Field F] [NumberField F]
    (w : InfinitePlace F) (huniq : ∀ v : InfinitePlace F, v = w)
    (e : InfiniteAdeleRing F ≃+* ℂ)
    (he : ∀ x, e x = InfinitePlace.Completion.extensionEmbedding w (x w))
    (hn : ∀ g : I₀(F), g ∈ (sIdeleNorm F ∅).ker ↔ ‖e g.val.1‖ = 1)
    (g : I₀(F)) (hg : (QuotientGroup.mk g : J₀(F)) = 1) :
    ‖e g.val.1‖ = 1 ∧ (e g.val.1) ^ NumberField.Units.torsionOrder F = 1 := by
  have hn₁ : ‖e g.val.1‖ = 1 := hn g |>.mp (by
    rw [MonoidHom.mem_ker, ← sIdeleQuotientNorm_mk, hg, map_one])
  refine ⟨hn₁, ?_⟩
  obtain ⟨u, hu⟩ := (sIdeleQuotient_mk_eq_one F ∅ g).mp hg
  have ha := congrArg (fun b : I₀(F) ↦ b.val.1 w) hu
  change g.val.1 w = algebraMap F w.Completion (u.val : F) at ha
  have harg : e g.val.1 = w.embedding (u.val : F) := by
    rw [he, ha, AbsoluteValue.Completion.algebraMap_def,
      InfinitePlace.Completion.extensionEmbedding_coe]
    rfl
  have huint : IsIntegral ℤ (u.val : F) := by
    have hmem : (u.val : F) ∈ ((∅ : Finset Places(F)) : Set Places(F)).integer F := (u.val).2
    simp only [Finset.coe_empty, integer_empty, Algebra.mem_bot] at hmem
    obtain ⟨a, ha⟩ := hmem
    rw [← ha]
    exact a.isIntegral_coe
  have hnorm (v : InfinitePlace F) : v (u.val : F) = 1 := by
    rw [huniq v, ← InfinitePlace.norm_embedding_eq, ← harg]
    exact hn₁
  obtain ⟨m, hm, hm'⟩ := Embeddings.pow_eq_one_of_norm_eq_one F ℂ huint
    (fun v ↦ by rw [← InfinitePlace.apply]; exact hnorm _)
  let a : 𝓞 F := ⟨(u.val : F), huint⟩
  have ha' : a ^ m = 1 := by
    apply Subtype.ext
    exact hm'
  obtain ⟨v, hv⟩ := IsUnit.of_pow_eq_one ha' (by omega)
  have hpow := NumberField.Units.pow_torsionOrder_eq_one F
    ((NumberField.Units.mem_torsion F).mpr
      (fun t ↦ by change t ((v.val : 𝓞 F) : F) = 1; rw [hv]; exact hnorm t))
  have h : (u.val : F) ^ NumberField.Units.torsionOrder F = 1 := by
    have hh := congrArg (fun u : (𝓞 F)ˣ ↦ ((u.val : 𝓞 F) : F)) hpow
    change ((v.val : 𝓞 F) : F) ^ _ = 1 at hh
    rwa [hv] at hh
  rw [harg, ← map_pow, h, map_one]

/-- The character of the archimedean ideles descends through a principal diagonal on which it
is trivial, and the descended character extends to an unramified global norm-one character. -/
private theorem inverseAverage_descend {F : Type} [Field F] [NumberField F]
    (χ : PontryaginDual I₀(F))
    (hχ : ∀ g : I₀(F), (QuotientGroup.mk g : J₀(F)) = 1 → χ g = 1) :
    ∃ (ηG : PontryaginDual C₁(F)) (hη : NormOneCharacterUnramifiedOutside ηG ∅),
      ∀ (g : N₀(F)) (y : J₁₀(F)), y.val = QuotientGroup.mk g.val →
        χ g.val = sLocalNormOneCharacter ∅ ηG hη y := by
  let η : PontryaginDual J₀(F) :=
    ⟨QuotientGroup.lift _ χ.toMonoidHom (fun g hg ↦ hχ g ((QuotientGroup.eq_one_iff g).mpr hg)),
      (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr χ.continuous⟩
  let coeCircle : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  obtain ⟨c, hc⟩ := sIdeleRestriction_surjective F ∅ (coeCircle.comp η)
  let C := IdeleClassGroup (𝓞 F) F
  let : T2Space C := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
  let : LocallyCompactSpace C := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
  have hn (x : C₁(F)) : ‖c.val x.val‖ = 1 := by
    rw [norm_quasiCharacter_eq_rpow_abscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      (ideleClassNorm_ne_one (F := F))]
    simp [MonoidHom.mem_ker.mp x.property]
  let w : PontryaginDual C₁(F) :=
    { toFun := fun x ↦ ⟨c.val x.val, mem_sphere_zero_iff_norm.mpr (hn x)⟩
      map_one' := Circle.ext (map_one c.val)
      map_mul' := fun x y ↦ Circle.ext (map_mul c.val x.val y.val)
      continuous_toFun := (c.val.continuous.comp continuous_subtype_val).subtype_mk
        (fun x ↦ mem_sphere_zero_iff_norm.mpr (hn x)) }
  let hw : NormOneCharacterUnramifiedOutside w ∅ := ⟨c, fun _ ↦ rfl⟩
  refine ⟨w, hw, fun g y hy ↦ Circle.ext ?_⟩
  rw [sLocalNormOneCharacter_eq_sIdeleRestriction w c (fun _ ↦ rfl), hc, hy]
  rfl

/-- A positive angular degree has square different from one at a suitable point of the circle. -/
private theorem inverseAverage_exists_rotation (k : ℕ) (hk : 0 < k) :
    ∃ z : Circle, (z : ℂ) ^ k * (z : ℂ) ^ k ≠ 1 := by
  let t := Real.pi / (2 * (k : ℝ))
  refine ⟨Circle.exp t, ?_⟩
  rw [← pow_add, Circle.coe_exp, ← Complex.exp_nat_mul]
  have h : ((k + k : ℕ) : ℂ) * ((t : ℂ) * Complex.I) = (Real.pi : ℂ) * Complex.I := by
    rw [← mul_assoc]
    congr 1
    have hr : ((k + k : ℕ) : ℝ) * t = Real.pi := by
      push_cast
      dsimp [t]
      rw [show (k : ℝ) + k = 2 * k by ring, mul_div_cancel₀ _ (by positivity)]
    exact_mod_cast hr
  rw [h, Complex.exp_pi_mul_I]
  norm_num

/-- At the empty finite stage, archimedean projection followed by insertion is the identity. -/
private theorem inverseAverage_archInsert_archPart (F : Type) [Field F] [NumberField F]
    (g : I₀(F)) : archInsert(F) (archPart(F) g) = g :=
  Units.ext (Prod.ext rfl (Subsingleton.elim _ _))

/-- On the stage without finite places, the archimedean covariance of a test
passes through the S-unit sum to its theta function. -/
private theorem inverseAverage_theta_covariance {F : Type} [Field F] [NumberField F]
    (f : ℬ∞(F)) (c : QuasiCharacter J₀(F)) (a : I₀(F)) (ξ : ℂ)
    (hf : ∀ x : InfiniteAdeleRing F, f (Multiplicative.ofAdd (a.val.1 * x)) =
      ξ * f (Multiplicative.ofAdd x)) (q : J₀(F)) :
    sLocalAdelicThetaOnClasses F ∅ (sLocalStandardThetaTensor c f) (q * QuotientGroup.mk a) =
      ξ * sLocalAdelicThetaOnClasses F ∅ (sLocalStandardThetaTensor c f) q := by
  induction q using QuotientGroup.induction_on with | H g => ?_
  rw [← QuotientGroup.mk_mul, sLocalAdelicThetaOnClasses_mk, sLocalAdelicThetaOnClasses_mk,
    sLocalAdelicTheta_apply, sLocalAdelicTheta_apply]
  let d := (Units.map ((adeleProjection F ∅).comp (integralAdelesOutside F ∅).subtype).toMonoidHom).comp
    (Units.map (integralAdeleDiagonal F ∅).toMonoidHom)
  let t := sLocalStandardThetaTensor c f
  change (∑' u, t (Multiplicative.ofAdd ((d u).val * (g * a).val))) =
    ξ * ∑' u, t (Multiplicative.ofAdd ((d u).val * g.val))
  rw [← tsum_mul_left]
  apply tsum_congr
  intro u
  simp only [t, sLocalStandardThetaTensor_apply, Fintype.prod_empty, mul_one]
  change f (Multiplicative.ofAdd ((d u).val.1 * (g.val.1 * a.val.1))) =
    ξ * f (Multiplicative.ofAdd ((d u).val.1 * g.val.1))
  rw [mul_comm g.val.1 a.val.1, mul_left_comm, hf]

/-- An archimedean test of a character weight with nontrivial square belongs
to the kernel of the positive-argument homogeneous theta transform. -/
private theorem inverseAverage_homogeneous_zero {F : Type} [Field F] [NumberField F]
    (f : ℬ∞(F)) (c : QuasiCharacter J₀(F)) (a : N₀(F)) (χS : PontryaginDual J₁₀(F))
    (y : J₁₀(F)) (hy : y.val = QuotientGroup.mk a.val)
    (hf : ∀ x : InfiniteAdeleRing F, f (Multiplicative.ofAdd (a.val.val.1 * x)) =
      (χS y : ℂ) * f (Multiplicative.ofAdd x)) (hdiff : (χS y : ℂ) * (χS y : ℂ) ≠ 1) :
    sLocalStandardThetaTensor c f ∈ (sLocalHomogeneousAdelicThetaLinearMap F ∅ χS).ker := by
  apply LinearMap.mem_ker.mpr
  ext q
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply, ContinuousMap.zero_apply]
  let : MeasurableSpace J₁₀(F) := borel _
  let : BorelSpace J₁₀(F) := ⟨rfl⟩
  let μ := sLocalNormOneQuotientMeasure F ∅
  have : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F)
    (S := (∅ : Finset Places(F)))).1
  let θ := sLocalAdelicThetaOnClasses F ∅ (sLocalStandardThetaTensor c f)
  let I (z : J₁₀(F)) : ℂ := θ (q * z.val) * χS z
  change ∫ z, I z ∂μ = 0
  have hμ := integral_mul_left_eq_self (μ := μ) I y
  have hi (z : J₁₀(F)) : I (y * z) = ((χS y : ℂ) * (χS y : ℂ)) * I z := by
    change θ (q * (y.val * z.val)) * (χS (y * z) : ℂ) = _
    rw [show q * (y.val * z.val) = q * z.val * QuotientGroup.mk a.val by rw [← hy]; ac_rfl]
    rw [show θ (q * z.val * QuotientGroup.mk a.val) = (χS y : ℂ) * θ (q * z.val)
      from inverseAverage_theta_covariance f c a.val _ hf _]
    simp only [map_mul, Circle.coe_mul, I]
    ring
  simp_rw [hi, integral_const_mul] at hμ
  exact (mul_eq_zero.mp (by rw [sub_mul, one_mul, hμ, sub_self] :
    ((χS y : ℂ) * (χS y : ℂ) - 1) * (∫ z, I z ∂μ) = 0)).resolve_left
    (sub_ne_zero.mpr hdiff)

/-- The integral of the constant one on a compact group with Haar measure is nonzero. -/
private theorem inverseAverage_integral_one_ne_zero {G : Type*} [Group G] [TopologicalSpace G]
    [MeasurableSpace G] [CompactSpace G] (μ : Measure G) (hμ : μ.IsHaarMeasure) :
    (∫ _ : G, (1 : ℂ) ∂μ) ≠ 0 := by
  rw [integral_const, Algebra.smul_def, mul_one]
  exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos
    (hμ.open_pos Set.univ isOpen_univ Set.univ_nonempty)
    (hμ.lt_top_of_isCompact isCompact_univ).ne).ne'

/-- With class number one, the inverse average at the identity is a single
norm-one integral. A matching character weight makes its integrand constant. -/
private theorem inverseAverage_at_one_ne_zero {F : Type} [Field F] [NumberField F]
    [CompactSpace N₀(F)] (hclass : classNumber F = 1)
    (f : ℬ∞(F)) (χ : PontryaginDual I₀(F))
    (hf : ∀ a : N₀(F), ∀ x : InfiniteAdeleRing F,
      f (Multiplicative.ofAdd (a.val.val.1 * x)) =
        (χ a.val : ℂ) * f (Multiplicative.ofAdd x))
    (hf₁ : f (Multiplicative.ofAdd (1 : InfiniteAdeleRing F)) = 1) :
    infiniteStandardThetaAverage χ (fun _ ↦ 1) f 1 ≠ 0 := by
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : Places(F)) : MeasurableSpace L(F, v) := borel _
  let : MeasurableSpace (SAdeleRing F ∅) := inferInstanceAs
    (MeasurableSpace (((w : InfinitePlace F) → w.Completion) ×
      ((v : (∅ : Finset Places(F))) → L(F, v.val))))
  have : Subsingleton (Fin (classNumber F)) := by rw [hclass]; infer_instance
  rw [infiniteStandardThetaAverage_apply, Fintype.sum_subsingleton _ ⟨0, classNumber_pos F⟩]
  have hg (a : N₀(F)) :
      f (Multiplicative.ofAdd (((archPart(F) a.val)⁻¹ * 1).val)) *
          (χ (archInsert(F) (archPart(F) a.val)) : ℂ) = 1 := by
    rw [mul_one, inverseAverage_archInsert_archPart]
    have hv : (archPart(F) a.val)⁻¹ = archPart(F) (a⁻¹).val :=
      (map_inv (archPart(F)) a.val).symm
    rw [hv]
    have he : f (Multiplicative.ofAdd ((a⁻¹).val.val.1 * 1)) =
        (χ (a⁻¹).val : ℂ) * f (Multiplicative.ofAdd (1 : InfiniteAdeleRing F)) := hf _ _
    rw [mul_one] at he
    change f (Multiplicative.ofAdd ((a⁻¹).val.val.1)) * (χ a.val : ℂ) = 1
    rw [he, hf₁, mul_one, Subgroup.coe_inv, map_inv, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  simp only [Subgroup.coe_one, map_one, one_mul, hg]
  exact @inverseAverage_integral_one_ne_zero N₀(F) _ _ _ _
    (sNormOneIdeleTamagawaMeasure F ∅)
    (sNormOneIdeleTamagawaMeasure_existsUnique F ∅).exists.choose_spec.1

/-- A class-number-one field with a single complex place gives opposite character
weights for the inverse-argument and positive-argument averages. -/
private theorem inverseAverage_contradiction (h : Printed.sLocalStandardThetaTensor_inverseAverage_quotient_equiv)
    (F : Type) [Field F] [NumberField F] (hclass : classNumber F = 1)
    (w : InfinitePlace F) (hw : w.IsComplex) (huniq : ∀ v : InfinitePlace F, v = w) : False := by
  classical
  let : IsPrincipalIdealRing (𝓞 F) := classNumber_eq_one_iff.mp hclass
  have hPic : Subsingleton Picₛ(F, (∅ : Finset Places(F))) := by
    rw [Finset.coe_empty, integer_empty]
    let e := Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 F) F)
    let := IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
    infer_instance
  have : Subsingleton (Fin (classNumber F)) := by rw [hclass]; infer_instance
  have : Nonempty (Fin (classNumber F)) := ⟨⟨0, classNumber_pos F⟩⟩
  have : Subsingleton (ClassGroup (𝓞 F)) := Fintype.card_le_one_iff_subsingleton.mp hclass.le
  obtain ⟨e, he, he', heval⟩ := inverseAverage_archComplex w hw huniq
  obtain ⟨D, hD⟩ := inverseAverage_ideleComplex e he he'
  have hn (g : I₀(F)) := inverseAverage_normOne_complex w hw huniq e heval g
  let : CompactSpace N₀(F) := inverseAverage_normOne_compact e D hD hn
  let k := NumberField.Units.torsionOrder F
  obtain ⟨χ₀, hχ₀⟩ := inverseAverage_phase k
  let χ : PontryaginDual I₀(F) := χ₀.comp ⟨D.toMonoidHom, D.continuous⟩
  have hphase (g : I₀(F)) (hg : ‖e g.val.1‖ = 1) : (χ g : ℂ) = e g.val.1 ^ k := by
    change (χ₀ (D g) : ℂ) = _
    rw [hχ₀, hD, hg, Complex.ofReal_one, div_one]
  have hdiag (g : I₀(F)) (hg : (QuotientGroup.mk g : J₀(F)) = 1) : χ g = 1 := by
    obtain ⟨hg₁, hg₂⟩ := inverseAverage_diagonal_pow w huniq e heval hn g hg
    exact Circle.ext ((hphase g hg₁).trans hg₂)
  obtain ⟨η, hη, hηS⟩ := inverseAverage_descend χ hdiag
  obtain ⟨E, hE⟩ := h F ∅ hPic η hη χ hηS (fun _ ↦ 1) ⟨rfl, bijective_of_subsingleton' _⟩
  obtain ⟨f, hf₁, hfCov⟩ := inverseAverage_archTest w hw huniq e heval k
  have hf (a : N₀(F)) (x : InfiniteAdeleRing F) :
      f (Multiplicative.ofAdd (a.val.val.1 * x)) = (χ a.val : ℂ) * f (Multiplicative.ofAdd x) := by
    have ha := (hn a.val).mp a.property
    rw [hphase a.val ha, hfCov _ _ ha]
  have hnz := inverseAverage_at_one_ne_zero hclass f χ hf hf₁
  obtain ⟨z, hz⟩ := inverseAverage_exists_rotation k (NumberField.Units.torsionOrder_pos F)
  let a₀ := D.symm (Circle.toUnits z)
  have ha₀ : e a₀.val.1 = (z : ℂ) := by
    rw [← hD, D.apply_symm_apply]
    rfl
  let a : N₀(F) := ⟨a₀, (hn a₀).mpr (ha₀ ▸ Circle.norm_coe z)⟩
  let y : J₁₀(F) := ⟨QuotientGroup.mk a.val, a.property⟩
  have hηy := hηS a y rfl
  have haχ : (χ a.val : ℂ) = (z : ℂ) ^ k :=
    (hphase a₀ (ha₀ ▸ Circle.norm_coe z)).trans (congrArg (fun t : ℂ ↦ t ^ k) ha₀)
  let ξ := sLocalNormOneCharacter ∅ η hη
  let c := sIdeleRestriction F ∅ hη.choose
  have hzero := inverseAverage_homogeneous_zero f c a ξ y rfl
    (fun x ↦ by rw [← hηy]; exact hf a x)
    (by rw [show ξ y = χ a.val from hηy.symm, haχ]; exact hz)
  let K := (infiniteStandardThetaAverage χ (fun _ ↦ 1)).ker
  let M := (sLocalHomogeneousAdelicThetaLinearMap F ∅ ξ).ker
  have htarget : M.mkQ (sLocalStandardThetaTensor c f) = 0 :=
    (Submodule.Quotient.mk_eq_zero M).mpr hzero
  have hsource : K.mkQ f = 0 :=
    E.injective ((hE f).trans (htarget.trans E.map_zero.symm))
  have hker : f ∈ K := (Submodule.Quotient.mk_eq_zero K).mp hsource
  exact hnz (DFunLike.congr_fun (LinearMap.mem_ker.mp hker) 1)

/-- Paper: Theorem 6.2.2.1(1), (6.2.2.5), p. 299. Over ℚ(i) at its complex stage,
take the angular character of degree equal to the torsion order of the integer unit group
and a monomial test of the same degree times a radial cutoff. The inverse-argument average
at 1 integrates the constant 1. The positive-argument homogeneous average has twice the
character weight and vanishes. The proposed map kills a nonzero source class. -/
theorem Printed.sLocalStandardThetaTensor_inverseAverage_quotient_equiv_false :
    ¬ Printed.sLocalStandardThetaTensor_inverseAverage_quotient_equiv := by
  intro h
  obtain ⟨w, hw, huniq⟩ := inverseAverage_gaussianPlace
  exact inverseAverage_contradiction h GField inverseAverage_gaussianClassNumber w hw huniq

end InverseAverageCounterexample

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

private theorem infiniteStandardThetaAverage_ratGaussian : ∃ f : ℬ∞(ℚ), ∀ x : InfiniteAdeleRing ℚ,
    f (Multiplicative.ofAdd x) = (Real.exp (-Real.pi * ‖x Rat.infinitePlace‖ ^ 2) : ℂ) := by
  let e : Multiplicative (InfiniteAdeleRing ℚ) ≃ₜ* Multiplicative Rat.infinitePlace.Completion :=
    { Homeomorph.piUnique InfinitePlace.Completion with map_mul' := fun _ _ ↦ rfl }
  let s := infiniteStandardGaussian Rat.infinitePlace 1
  let : LocallyCompactSpace (Multiplicative (InfiniteAdeleRing ℚ)) :=
    inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing ℚ))
  let : LocallyCompactSpace (Multiplicative Rat.infinitePlace.Completion) :=
    inferInstanceAs (LocallyCompactSpace Rat.infinitePlace.Completion)
  let : T2Space (Multiplicative (InfiniteAdeleRing ℚ)) :=
    inferInstanceAs (T2Space ((v : InfinitePlace ℚ) → v.Completion))
  let : T2Space (Multiplicative Rat.infinitePlace.Completion) :=
    inferInstanceAs (T2Space Rat.infinitePlace.Completion)
  refine ⟨⟨_, schwartzBruhat_mem_comp_equiv e s.property⟩, fun x ↦ ?_⟩
  change infiniteStandardGaussianValue Rat.infinitePlace 1 (x Rat.infinitePlace) = _
  have hi := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
  have hn := hi.norm_map_of_map_zero (map_zero _) (x Rat.infinitePlace)
  simp [infiniteStandardGaussianValue, Rat.isReal_infinitePlace,
    ← hn, Real.norm_eq_abs, sq_abs]

private theorem infiniteStandardThetaAverage_ratNormOne (g : Nₛ(ℚ, ∅)) :
    ‖g.val.val.1 Rat.infinitePlace‖ = 1 := by
  simpa [MonoidHom.mem_ker.mp g.property] using (rat_sIdeleNorm_eq ∅ g.val).symm

private theorem infiniteStandardThetaAverage_ratFinite : Finite Nₛ(ℚ, ∅) := by
  classical
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  let c (g : Nₛ(ℚ, ∅)) := e (g.val.val.1 Rat.infinitePlace)
  have hi := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
  have hc (g : Nₛ(ℚ, ∅)) : |c g| = 1 :=
    (hi.norm_map_of_map_zero (map_zero _) _).trans (infiniteStandardThetaAverage_ratNormOne g)
  let signs : Finset ℝ := {1, -1}
  have hmem (g : Nₛ(ℚ, ∅)) : c g ∈ signs := by
    simpa [signs] using (abs_eq (zero_le_one : (0 : ℝ) ≤ 1)).mp (hc g)
  apply Finite.of_injective (fun g : Nₛ(ℚ, ∅) ↦ (⟨c g, hmem g⟩ : signs))
  intro g h eq
  apply Subtype.ext
  apply Units.ext
  apply Prod.ext _ (Subsingleton.elim _ _)
  funext v
  obtain rfl := Subsingleton.elim v Rat.infinitePlace
  exact e.injective (congrArg Subtype.val eq)

private theorem infiniteStandardThetaAverage_ratGaussian_apply (f : ℬ∞(ℚ))
    (hf : ∀ x : InfiniteAdeleRing ℚ, f (Multiplicative.ofAdd x) =
      (Real.exp (-Real.pi * ‖x Rat.infinitePlace‖ ^ 2) : ℂ))
    (x : (InfiniteAdeleRing ℚ)ˣ) :
    infiniteStandardThetaAverage (F := ℚ) (S := ∅) 1 (fun _ ↦ 1) f x =
      (sNormOneIdeleTamagawaMeasure ℚ ∅).real Set.univ •
        (Real.exp (-Real.pi * ‖x.val Rat.infinitePlace‖ ^ 2) : ℂ) := by
  classical
  have : Subsingleton (Fin (classNumber ℚ)) := by
    rw [Rat.classNumber_eq]
    infer_instance
  rw [infiniteStandardThetaAverage_apply, Fintype.sum_subsingleton _ ⟨0, classNumber_pos ℚ⟩,
    ← integral_const]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro g
  simp only [Subgroup.coe_one, map_one, one_mul, PontryaginDual.one_apply, Circle.coe_one,
    mul_one, hf]
  let v := Units.map (Pi.evalRingHom InfinitePlace.Completion Rat.infinitePlace).toMonoidHom
  let a := Units.map (RingHom.fst (InfiniteAdeleRing ℚ)
    (∀ p : (∅ : Finset Places(ℚ)), L(ℚ, p.val))).toMonoidHom g.val
  have harg : ‖(a⁻¹ * x).val Rat.infinitePlace‖ = ‖x.val Rat.infinitePlace‖ := by
    change ‖(v (a⁻¹ * x)).val‖ = _
    rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv]
    change ‖g.val.val.1 Rat.infinitePlace‖⁻¹ * ‖x.val Rat.infinitePlace‖ = _
    rw [infiniteStandardThetaAverage_ratNormOne, inv_one, one_mul]
  rw [harg]

private theorem infiniteStandardThetaAverage_ratSection_norm (u : ℝ≥0ˣ) :
    ‖(canonicalIdeleNormSection ℚ u).val.1 Rat.infinitePlace‖ = (u.val : ℝ) := by
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding Rat.infinitePlace
  have hn := hi.norm_map_of_map_zero (map_zero _) ((canonicalIdeleNormSection ℚ u).val.1 Rat.infinitePlace)
  rw [← hn, canonicalIdeleNormSection_infinite]
  simp

/-- Paper: Theorem 6.2.2.1(2), pp. 299, 302. Over ℚ at the archimedean stage, take the
trivial character, the identity representative and the real Gaussian `exp(-πx²)`. Its unweighted
logarithmic profile is a positive constant times `exp(-π exp(2t))`, which has a nonzero limit
as t tends to negative infinity. -/
theorem Printed.infiniteStandardThetaAverage_schwartz_logProfile_false :
    ¬ Printed.infiniteStandardThetaAverage_schwartz_logProfile := by
  classical
  intro h
  have hω : NormOneCharacterUnramifiedOutside (F := ℚ) 1 ∅ :=
    ⟨⟨1, (mem_unramifiedOutside_iff ℚ ∅ 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ rfl⟩
  have hchar : sLocalNormOneCharacter (F := ℚ) ∅ 1 hω = 1 := by
    let hu := (normOneCharacterUnramifiedOutside_iff (F := ℚ) 1).mp hω
    exact hu.unique hu.exists.choose_spec (fun _ _ _ _ _ ↦ rfl)
  have : IsPrincipalIdealRing (𝓞 ℚ) := classNumber_eq_one_iff.mp Rat.classNumber_eq
  have hPic : Subsingleton Picₛ(ℚ, (∅ : Finset Places(ℚ))) := by
    rw [Finset.coe_empty, integer_empty]
    let e := Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)
    let := IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
    infer_instance
  have : Subsingleton (Fin (classNumber ℚ)) := by
    rw [Rat.classNumber_eq]
    infer_instance
  have : Nonempty (Fin (classNumber ℚ)) := ⟨⟨0, classNumber_pos ℚ⟩⟩
  obtain ⟨f, hf⟩ := infiniteStandardThetaAverage_ratGaussian
  obtain ⟨φ, hφ⟩ := h ℚ ∅ hPic 1 hω 1 (by simp [hchar]) (fun _ ↦ 1)
    ⟨rfl, bijective_of_subsingleton' _⟩ f
  let μ := sNormOneIdeleTamagawaMeasure ℚ ∅
  have haar := (sNormOneIdeleTamagawaMeasure_existsUnique ℚ ∅).exists.choose_spec.1
  have : Finite Nₛ(ℚ, ∅) := infiniteStandardThetaAverage_ratFinite
  have : CompactSpace Nₛ(ℚ, ∅) := Finite.compactSpace
  have hm : (μ.real Set.univ : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (ENNReal.toReal_pos (haar.open_pos Set.univ isOpen_univ Set.univ_nonempty)
      (haar.lt_top_of_isCompact isCompact_univ).ne).ne'
  have hval (t : ℝ) : φ t =
      (μ.real Set.univ : ℂ) * (Real.exp (-Real.pi * Real.exp t ^ 2) : ℂ) := by
    rw [hφ, infiniteStandardThetaAverage_ratGaussian_apply f hf]
    simp [infiniteStandardThetaAverage_ratSection_norm, Units.coe_map,
      Real.toNNReal_of_nonneg (Real.exp_pos t).le, Algebra.smul_def, μ]
  have hlim : Filter.Tendsto φ Filter.atBot (𝓝 (μ.real Set.univ : ℂ)) := by
    have hc : Continuous (fun s : ℝ ↦ (μ.real Set.univ : ℂ) *
        (Real.exp (-Real.pi * s ^ 2) : ℂ)) := by fun_prop
    rw [funext hval]
    simpa [Function.comp_def] using (hc.tendsto 0).comp Real.tendsto_exp_atBot
  exact hm (tendsto_nhds_unique hlim (φ.tendsto_cocompact.mono_left atBot_le_cocompact))

end StandardFunctions

end RiemannMasullo
