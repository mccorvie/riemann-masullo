module

public import RiemannMasullo.Ch06_LocalGlobal.Sec1
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3a
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import all RiemannMasullo.Ch02_AdelicTheta.Sec1

import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.IsOpenUnits

import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

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
      ρₛ(S) g.val (f i) - ρₛ(S) g.val x ∈ U := by
  have uniform {G X : Type _} [TopologicalSpace G] [AddCommGroup X] [TopologicalSpace X]
      [IsTopologicalAddGroup X] {K : Set G} (hK : IsCompact K)
      (A : G → X → X) (hA : Continuous (fun p : G × X ↦ A p.1 p.2))
      (u : ι → X) (v : X) (hu : Tendsto u l (𝓝 v)) (U : Set X) (hU : U ∈ 𝓝 0) :
      ∀ᶠ i in l, ∀ g ∈ K, A g (u i) - A g v ∈ U := by
    have hd : Continuous (fun p : X × G ↦ A p.2 p.1 - A p.2 v) :=
      (hA.comp (continuous_snd.prodMk continuous_fst)).sub
        (hA.comp (continuous_snd.prodMk continuous_const))
    exact hu.eventually (hK.eventually_forall_of_forall_eventually (P := fun y g ↦ A g y - A g v ∈ U)
      fun g _ ↦
        hd.continuousAt (x := (v, g)) (by simpa only [sub_self] using hU))
  let : PolynormableSpace ℂ (Θₛ(S)) := sLocalAdelicThetaSpace_polynormable
  let : IsTopologicalAddGroup (Θₛ(S)) := PolynormableSpace.isTopologicalAddGroup ℂ _
  have hc := (isProperMap_sIdeleQuotientNorm F S).isCompact_preimage
    (isCompact_singleton (x := (1 : ℝ≥0ˣ)))
  have hA := (existsUnique_sLocalThetaAction (F := F) (S := S)).exists.choose_spec.1
  intro U hU
  have h := uniform (G := Jₛ(S)) (X := Θₛ(S)) hc (fun g y ↦ ρₛ(S) g y) hA f x hf U hU
  exact h.mono fun i hi g ↦ hi g.val g.property

/-- Multiplication by scalars of norm at most one keeps uniform convergence of differences. -/
private theorem smul_sub_eventually_mem_of_norm_le_one {E ι κ : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [ContinuousSMul ℂ E] (l : Filter ι) (u : ι → κ → E)
    (w : κ → E) (c : κ → ℂ) (hc : ∀ k, ‖c k‖ ≤ 1)
    (h : ∀ U ∈ 𝓝 (0 : E), ∀ᶠ i in l, ∀ k, u i k - w k ∈ U) :
    ∀ U ∈ 𝓝 (0 : E), ∀ᶠ i in l, ∀ k, c k • u i k - c k • w k ∈ U := by
  intro U hU
  obtain ⟨W, ⟨hW, hWb⟩, hWU⟩ := (nhds_basis_balanced ℂ E).mem_iff.mp hU
  filter_upwards [h W hW] with i hi k
  rw [← smul_sub]
  exact hWU (hWb.smul_mem (hc k) (hi k))

/-- Paper: Lemma 6.2.1.3(2), p. 296.
Uniform convergence over the norm-one quotient also holds after twisting the action
by a unitary character. -/
theorem sLocalThetaAction_twist_tendstoUniformly {ι : Type*} (l : Filter ι)
    (f : ι → Θₛ(S)) (x : Θₛ(S)) (hf : Tendsto f l (𝓝 x)) (χ : PontryaginDual J₁(S)) :
    ∀ U ∈ 𝓝 (0 : Θₛ(S)), ∀ᶠ i in l, ∀ g : J₁(S),
      (χ g : ℂ) • ρₛ(S) g.val (f i) - (χ g : ℂ) • ρₛ(S) g.val x ∈ U :=
  smul_sub_eventually_mem_of_norm_le_one l _ _ (fun g ↦ (χ g : ℂ))
    (fun g ↦ (Circle.norm_coe (χ g)).le) (sLocalThetaAction_tendstoUniformly l f x hf)

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
      if (∀ u ∈ U(v), d u = c u) then ((μ(v)) (U(v))).toReal else 0) := by
  classical
  let : BorelSpace (L(v))ˣ := ⟨rfl⟩
  let : (μ(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  let q (g : (L(v))ˣ) := d g / c g
  have hc (g : (L(v))ˣ) : c g ≠ 0 := ((Group.isUnit g).map c).ne_zero
  have hram : ¬ ∀ u ∈ U(v), c u = 1 := fun h ↦
    _hc.elim fun u hu ↦ hu.2 (h u hu.1)
  have hfun : (fun g : (L(v))ˣ ↦ finiteStandardGaussian v c (Multiplicative.ofAdd g.val) * d g) =
      (U(v)).indicator q := by
    funext g
    by_cases hg : g ∈ U(v)
    · rw [Set.indicator_of_mem hg, finiteStandardGaussian_integerUnit v c g hg]
      exact (mul_comm _ _).trans (div_eq_mul_inv _ _).symm
    · rw [Set.indicator_of_notMem hg]
      have hv : g.val ∉ Units.val '' U(v) := fun ⟨u, hu, h⟩ ↦ hg ((Units.ext h) ▸ hu)
      have hz : finiteStandardGaussian v c (Multiplicative.ofAdd g.val) = 0 :=
        (ite_eq_right hram).trans (Set.indicator_of_notMem hv _)
      rw [hz, zero_mul]
  have hopen : IsOpen (U(v)) := Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hcompact : IsCompact (U(v)) := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  have hq : Continuous q := d.continuous.div c.continuous hc
  constructor
  · rw [hfun, integrable_indicator_iff hopen.measurableSet]
    exact hq.continuousOn.integrableOn_compact hcompact
  · change (∫ g : (L(v))ˣ, finiteStandardGaussian v c (Multiplicative.ofAdd g.val) * d g ∂μ(v)) = _
    rw [hfun, integral_indicator hopen.measurableSet]
    split_ifs with hmatch
    · have eqOne : Set.EqOn q (fun _ ↦ (1 : ℂ)) (U(v)) := fun u hu ↦
        (div_eq_one_iff_eq (hc u)).mpr (hmatch u hu)
      rw [setIntegral_congr_fun hopen.measurableSet eqOne, setIntegral_const]
      simp [measureReal_def]
    · push Not at hmatch
      obtain ⟨a, ha, hne⟩ := hmatch
      have hpre : (fun y : (L(v))ˣ ↦ a * y) ⁻¹' U(v) = U(v) := by
        ext y
        exact (O(v)).units.mul_mem_cancel_left ha
      have hI := (measurePreserving_mul_left (μ(v)) a).setIntegral_preimage_emb
        (Homeomorph.mulLeft a).toMeasurableEquiv.measurableEmbedding q (U(v))
      rw [hpre] at hI
      change (∫ y in U(v), q (a * y) ∂μ(v)) = ∫ y in U(v), q y ∂μ(v) at hI
      have hmul (y : (L(v))ˣ) : q (a * y) = q a * q y := by
        simp only [q, map_mul, mul_div_mul_comm]
      simp_rw [hmul] at hI
      rw [integral_const_mul, ← sub_eq_zero, ← sub_one_mul] at hI
      exact (mul_eq_zero.mp hI).resolve_left
        (sub_ne_zero.mpr (fun h ↦ hne ((div_eq_one_iff_eq (hc a)).mp h)))

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
        (sLocalFiniteRestriction v c) (Multiplicative.ofAdd (x.2 v)) := by
  let factors (v : S) : ℬ(L(v.val)) :=
    finiteStandardGaussian (F := F) v.val (sLocalFiniteRestriction (F := F) v c)
  let W := FinestLocallyConvex (⨂[ℂ] v : S, ℬ(L(v.val)))
  let b : W := ⨂ₜ[ℂ] v : S, factors v
  let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
  have slice {X Y Z : Type _} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
      [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
      [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
      (E : InductiveTensor X Y ≃L[ℂ] Z) (a : X) (b : Y) (p : Z → ℂ) (r : ℂ)
      (h : p (E (a ⊗ₜ[ℂ] b)) = r) :
      p (E.toLinearMap.comp ((TensorProduct.mk ℂ X Y).flip b) a) = r := h
  have hx := (sAdeleSchwartz_inductiveTensor_equiv F S).choose_spec f factors x
  unfold sLocalStandardThetaTensor
  with_reducible_and_instances
    exact slice (X := ℬ∞) (Y := W) (Z := ℬₛ(S)) e f b
      (fun φ : ℬₛ(S) ↦ φ (Multiplicative.ofAdd x)) _ hx

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
      ∂sNormOneIdeleTamagawaMeasure F ∅ :=
  (exists_infiniteStandardThetaAverage χ r).choose_spec f x

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
      ∫ g : (L(v))ˣ, f.val (Multiplicative.ofAdd (g⁻¹).val) * (χ g : ℂ) ∂μ(v) := by
  have h := (exists_finiteStandardThetaAverage v χ).choose_spec f 1
  simpa [finiteStandardThetaAverage] using h

/-- Paper: (6.2.2.11), p. 301.
The finite convolution is the character times the Mellin integral with the inverse character.
Deviation: On the test χ times the unit indicator, the coefficient is the integer-unit mass. -/
theorem finiteStandardThetaAverage_eq_character_mul_integral (v : V)
    (χ : PontryaginDual (L(v))ˣ) (f : ℬ₀(v)) (x : (L(v))ˣ) :
    finiteStandardThetaAverage v χ f x = (χ x : ℂ) *
      ∫ y : (L(v))ˣ, f.val (Multiplicative.ofAdd y.val) * (χ y : ℂ)⁻¹ ∂μ(v) := by
  let : BorelSpace (L(v))ˣ := ⟨rfl⟩
  let : (μ(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v
  let : ProperSpace (L(v)) := properSpace_adicCompletion v
  let : LocallyCompactSpace (L(v))ˣ :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := L(v))).locallyCompactSpace
  have : (μ(v)).IsInvInvariant := by
    constructor
    unfold finiteLocalMultiplicativeTamagawaMeasure
    rw [Measure.inv_def, Measure.map_smul, Measure.map_inv_eq_self]
    exact measurable_inv.aemeasurable
  have factor {G : Type _} [CommGroup G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
      (ν : Measure G) [ν.IsInvInvariant] [ν.IsMulLeftInvariant]
      (φ : G → ℂ) (c : G →* Circle) (x : G) :
      (∫ g, φ (g⁻¹ * x) * (c g : ℂ) ∂ν) = (c x : ℂ) * ∫ y, φ y * (c y : ℂ)⁻¹ ∂ν := by
    let k (g : G) := φ (g⁻¹ * x) * (c g : ℂ)
    refine (integral_div_left_eq_self k ν x).symm.trans ?_
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    change φ ((x / y)⁻¹ * x) * (c (x / y) : ℂ) = _
    rw [inv_div, div_mul_cancel, map_div, Circle.coe_div, div_eq_mul_inv]
    ring
  exact ((exists_finiteStandardThetaAverage v χ).choose_spec f x).trans
    (factor (μ(v)) (fun y ↦ f.val (Multiplicative.ofAdd y.val)) χ.toMonoidHom x)

/-- Paper: Theorem 6.2.2.1(1), p. 299.
The kernel of the archimedean operator is closed in the archimedean test space. -/
theorem infiniteStandardThetaAverage_isClosed_ker (χ : PontryaginDual Iₛ(S))
    (r : Fin (classNumber F) → Nₛ(S)) :
    IsClosed ((infiniteStandardThetaAverage χ r).ker : Set ℬ∞) :=
  ContinuousLinearMap.isClosed_ker _

/-- Paper: Theorem 6.2.2.1(1), p. 299.
The kernel of the finite convolution is closed in the multiplicative test space. -/
theorem finiteStandardThetaAverage_isClosed_ker (v : V) (χ : PontryaginDual (L(v))ˣ) :
    IsClosed ((finiteStandardThetaAverage v χ).ker : Set (ℬ₀(v))) :=
  ContinuousLinearMap.isClosed_ker _

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

/-- Pullback along the unique real coordinate identifies real Schwartz functions with
the rational adelic test functions at the stage with no finite places. -/
private theorem ratTrivialHomogeneousTheta_quotient_realEquiv :
    ∃ E : SchwartzMap ℝ ℂ ≃L[ℂ] ℬ(SAdeleRing ℚ ∅),
      ∀ (f : SchwartzMap ℝ ℂ) (x : SAdeleRing ℚ ∅),
        E f (Multiplicative.ofAdd x) = f (InfinitePlace.Completion.ringEquivRealOfIsReal
          Rat.isReal_infinitePlace (x.1 Rat.infinitePlace)) := by
  let D : Type := (v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) → v.val.adicCompletion ℚ
  let _ : Unique D := uniqueOfSubsingleton 0
  let real : Rat.infinitePlace.Completion ≃ᵢ ℝ :=
    InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
  let coord : SAdeleRing ℚ ∅ ≃ₜ ℝ := (Homeomorph.prodUnique (InfiniteAdeleRing ℚ) D).trans
    ((Homeomorph.piUnique (fun v : InfinitePlace ℚ ↦ v.Completion)).trans real.toHomeomorph)
  let e : Multiplicative (SAdeleRing ℚ ∅) ≃ₜ* Multiplicative ℝ :=
    ContinuousMulEquiv.mk' coord fun x y ↦
      (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).map_add
        (x.toAdd.1 Rat.infinitePlace) (y.toAdd.1 Rat.infinitePlace)
  with_reducible refine realSchwartzBruhat_equiv.elim fun R hR ↦ ?_
  refine ⟨R.trans (schwartzBruhatPullbackEquiv e), ?_⟩
  intro f x
  exact hR f (coord x)

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
          (sAdeleSchwartzToGlobal ℚ ∅ (sLocalStandardThetaTensor (F := ℚ) (S := ∅) 1 g)) := by
  have hω : NormOneCharacterUnramifiedOutside (F := ℚ) 1 ∅ := by
    refine ⟨⟨1, (mem_unramifiedOutside_iff ℚ ∅ 1).mpr (fun _ _ _ ↦ rfl)⟩, fun _ ↦ ?_⟩
    rfl
  with_reducible refine ratTrivialHomogeneousTheta_quotient_realEquiv.elim fun E hE ↦ ?_
  with_reducible refine (sLocalHomogeneousThetaToGlobal_equiv_of_unramified
    (F := ℚ) (S := ∅) (ω := 1) ?_ hω).elim fun T hT ↦ ?_
  · rw [Finset.coe_empty, integer_empty]
    let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
    let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
    let := IsPrincipalIdealRing.of_surjective i i.surjective
    infer_instance
  let K := (sLocalHomogeneousAdelicThetaLinearMap ℚ ∅
    (sLocalNormOneCharacter (F := ℚ) ∅ 1 hω)).ker
  refine ⟨T.toContinuousLinearMap.comp (K.mkQL.comp E.toContinuousLinearMap), ?_, ?_⟩
  · change IsOpenQuotientMap (T.toHomeomorph ∘ (K.mkQL ∘ E.toHomeomorph))
    exact T.toHomeomorph.isOpenQuotientMap.comp
      (K.isOpenQuotientMap_mkQL.comp E.toHomeomorph.isOpenQuotientMap)
  intro f g hg
  have hfg : E f = sLocalStandardThetaTensor (F := ℚ) (S := ∅) 1 g := by
    refine Subtype.ext (funext fun (x : Multiplicative (SAdeleRing ℚ ∅)) ↦ ?_)
    have h := sLocalStandardThetaTensor_apply (F := ℚ) (S := ∅) 1 g x.toAdd
    have ht : sLocalStandardThetaTensor (F := ℚ) (S := ∅) 1 g x =
        g (Multiplicative.ofAdd x.toAdd.1) :=
      h.trans ((congrArg (g (Multiplicative.ofAdd x.toAdd.1) * ·)
        (Fintype.prod_empty _)).trans (mul_one _))
    exact ((hE f x.toAdd).trans (hg x.toAdd.1).symm).trans ht.symm
  let t := sLocalStandardThetaTensor (F := ℚ) (S := ∅) 1 g
  change T.toLinearMap (K.mkQ (E f)) = _
  have hrep := sLocalHomogeneousThetaToGlobal_mk (F := ℚ) (S := ∅) (ω := 1) hω t
  have hglobal := LinearMap.congr_fun hT (K.mkQ t)
  with_reducible exact (congrArg (fun b ↦ T.toLinearMap (K.mkQ b)) hfg).trans (hglobal.trans hrep)

end RiemannMasullo
