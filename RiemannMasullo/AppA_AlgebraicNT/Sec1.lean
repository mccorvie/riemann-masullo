module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.DedekindDomain.SInteger
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Maps.Proper.Basic
public import RiemannMasullo.ForMathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.RingTheory.PicardGroup

/-!
# The topology of adeles, ideles and their class groups

Appendix A.1 of Masullo. Finite sets of places containing all infinite places are
parametrized by their finite part. The positive real multiplicative group is `ℝ≥0ˣ`.
-/

@[expose] public section

noncomputable section

namespace RiemannMasullo

open Filter Function NumberField IsDedekindDomain Topology
open scoped NNReal RestrictedProduct NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing TensorProduct

section RestrictedProducts

-- TODO(paper-gap): In A.1.1.1–2, membership in I₀ and I₁ requires a partition of I.
-- The printed Cartesian product supplies neither of the indicated inclusions.

variable {ι : Type*} (G : ι → Type*) [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)]
  (K : (i : ι) → Subgroup (G i)) (I₀ : Finset ι)
  (h₀ : ∀ i ∈ I₀, K i = ⊥) (h₁ : ∀ i ∉ I₀, IsCompact (K i : Set (G i)) ∧ IsOpen (K i : Set (G i)))

include h₀ h₁ in
/-- Paper: Definition A.1.1.1, p. 539. The restricted product consists of the tuples
eventually in the distinguished subgroups. Boxes of identity neighborhoods which eventually
equal those subgroups form a neighborhood basis at the identity.
Deviation: The printed Cartesian product does not provide the two subsets used in the
definition. We use a finite subset of exceptional indices and its complement. -/
theorem restrictedProduct_description :
    Set.range (fun x : Πʳ i, [G i, K i] ↦ fun i ↦ x i) =
      {x | ∀ᶠ i in cofinite, x i ∈ K i} ∧
    (𝓝 (1 : Πʳ i, [G i, K i])).HasBasis
      (fun U : (i : ι) → Set (G i) ↦ (∀ i, U i ∈ 𝓝 1) ∧ ∀ᶠ i in cofinite, U i = K i)
      (fun U ↦ {x | ∀ i, x i ∈ U i}) := by
  classical
  refine ⟨RestrictedProduct.range_coe G _, hasBasis_iff.mpr fun T ↦ ⟨?_, ?_⟩⟩
  · intro hT
    let S : Set ι := {i | i ∉ I₀}
    have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr I₀.eventually_cofinite_notMem
    let f := RestrictedProduct.inclusion G (fun i ↦ (K i : Set (G i))) hS
    have hT' : f ⁻¹' T ∈ 𝓝 (1 : Πʳ i, [G i, K i]_[𝓟 S]) :=
      (RestrictedProduct.continuous_inclusion hS).continuousAt hT
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isInducing.nhds_eq_comap] at hT'
    obtain ⟨W, hW, hWT⟩ := mem_comap.mp hT'
    rw [nhds_pi, Filter.mem_pi'] at hW
    obtain ⟨J, V, hV, hVW⟩ := hW
    let U (i : ι) := (if i ∈ J then V i else Set.univ) ∩
      (if i ∈ I₀ then Set.univ else (K i : Set (G i)))
    refine ⟨U, ⟨fun i ↦ inter_mem ?_ ?_, ?_⟩, ?_⟩
    · by_cases hi : i ∈ J
      · simpa only [ite_eq_left hi, RestrictedProduct.one_apply] using hV i
      · simp [hi]
    · by_cases hi : i ∈ I₀
      · simp [hi]
      · simpa [hi] using (h₁ i hi).2.mem_nhds (K i).one_mem
    · filter_upwards [J.eventually_cofinite_notMem, I₀.eventually_cofinite_notMem] with i hiJ hi₀
      simp [U, hiJ, hi₀]
    · intro x hx
      let y : Πʳ i, [G i, K i]_[𝓟 S] :=
        ⟨x, fun i hi ↦ by simpa [U, show i ∉ I₀ from hi] using (hx i).2⟩
      have hy : (fun i ↦ y i) ∈ (J : Set ι).pi V := by
        intro i hi
        change x i ∈ V i
        simpa [U, Finset.mem_coe.mp hi] using (hx i).1
      exact hWT (hVW hy)
  · rintro ⟨U, ⟨hU, hUK⟩, hUT⟩
    let S : Set ι := {i | i ∉ I₀ ∧ U i = K i}
    have hS : S ∈ (cofinite : Filter ι) := I₀.eventually_cofinite_notMem.and hUK
    have hTail := (isOpen_restrictedProduct_forall_mem S (fun i hi ↦ (h₁ i hi.1).2)).mem_nhds
      (x := (1 : Πʳ i, [G i, K i])) (fun i _ ↦ (K i).one_mem)
    have hFinite : Sᶜ.pi U ∈ 𝓝 (fun i ↦ (1 : G i)) :=
      set_pi_mem_nhds (mem_cofinite.mp hS) (fun i _ ↦ hU i)
    refine mem_of_superset (inter_mem hTail
      (RestrictedProduct.continuous_coe.continuousAt hFinite)) ?_
    intro x hx
    apply hUT
    intro i
    by_cases hi : i ∈ S
    · exact hi.2.symm ▸ hx.1 i hi
    · exact hx.2 i hi

include h₀ h₁ in
/-- Paper: Lemma A.1.1.2, p. 539. The restricted product is a locally compact Hausdorff
group. The identity on coordinates preserves it under finite changes of the distinguished
subgroups, compact closures are characterized by boxes, and finite factors split off.
Deviation: We use the index partition of Definition A.1.1.1. In (5) we record the case
where the distinguished subgroups outside the finite set are open. -/
theorem restrictedProduct_topology :
    let P := Πʳ i, [G i, K i]
    (T2Space P ∧ LocallyCompactSpace P ∧ IsTopologicalGroup P) ∧
    (∀ K' : (i : ι) → Subgroup (G i), (∀ i ∈ I₀, K' i = ⊥) →
      (∀ i ∉ I₀, IsCompact (K' i : Set (G i)) ∧ IsOpen (K' i : Set (G i))) →
      (∀ᶠ i in cofinite, K' i = K i) →
      ∃ e : (Πʳ i, [G i, K' i]) ≃ₜ* P, ∀ x i, e x i = x i) ∧
    (∀ H : Set P, IsCompact (closure H) ↔
      ∃ B : (i : ι) → Set (G i), (∀ i, IsCompact (B i)) ∧
        (∀ᶠ i in cofinite, B i = K i) ∧ ∀ x ∈ H, ∀ i, x i ∈ B i) ∧
    (∀ J : Finset ι, ∃ e : P ≃ₜ* (((j : J) → G j) ×
      (Πʳ j : {i // i ∉ J}, [G j, K j])),
      ∀ x, (∀ j, (e x).1 j = x j) ∧ ∀ j, (e x).2 j = x j) ∧
    (∀ J : Finset ι, (∀ i ∉ J, IsOpen (K i : Set (G i))) →
      ∀ U : (i : ι) → Set (G i), (∀ i ∈ J, IsOpen (U i)) →
      IsOpen {x : P | (∀ i ∈ J, x i ∈ U i) ∧ ∀ i ∉ J, x i ∈ K i}) := by
  dsimp only
  have hK := I₀.eventually_cofinite_notMem.mono h₁
  have hOpen := hK.mono fun _ hi ↦ hi.2
  refine ⟨?_, fun K' _ _ heq ↦ ⟨restrictedProductCongr heq, fun _ _ ↦ rfl⟩,
    isCompact_closure_restrictedProduct_iff hK,
    fun J ↦ ⟨restrictedProductSplitFinset hOpen J, fun _ ↦ ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩⟩, ?_⟩
  · let e := restrictedProductSplitFinset hOpen I₀
    have : Fact (∀ j : {i // i ∉ I₀}, IsOpen (K j : Set (G j))) :=
      ⟨fun j ↦ (h₁ j j.2).2⟩
    have : LocallyCompactSpace (Πʳ j : {i // i ∉ I₀}, [G j, K j]) :=
      RestrictedProduct.locallyCompactSpace_of_group _ (.of_forall fun j ↦ (h₁ j j.2).1)
    exact ⟨inferInstance, e.toHomeomorph.isOpenEmbedding.locallyCompactSpace,
      e.toHomeomorph.isInducing.isTopologicalGroup e⟩
  · intro J hJ U hU
    exact ((isOpen_set_pi J.finite_toSet hU).preimage RestrictedProduct.continuous_coe).inter
      (isOpen_restrictedProduct_forall_mem (↑J : Set ι)ᶜ hJ)

-- TODO(paper-gap): A.1.1.2(5) allows J₁ to omit a nondiscrete exceptional factor with Kᵢ = 1.
-- With just that factor and J₁ empty the claimed open box is a non-open singleton.

end RestrictedProducts

variable (F : Type*) [Field F] [NumberField F]

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "AQuot(" F ")" => 𝔸[F] ⧸ AdeleRing.principalSubgroup (𝓞 F) F

/-- Paper: Definition A.1.1.3, p. 540. The infinite factor is the real scalar extension
of the field, the finite factor is the restricted product of the nonarchimedean completions,
and their product carries the adelic topology. The diagonal is the completion map at each place. -/
theorem adeleRing_factors :
    letI := moduleTopology ℝ (ℝ ⊗[ℚ] F)
    (∃ e : (ℝ ⊗[ℚ] F) ≃+* InfiniteAdeleRing F, Continuous e ∧ Continuous e.symm ∧
      ∀ x : F, e (1 ⊗ₜ[ℚ] x) = algebraMap F (InfiniteAdeleRing F) x) ∧
    IsHomeomorph (fun a : 𝔸ᶠ[𝓞 F, F] ↦
      (a : Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F])) ∧
    IsHomeomorph (fun a : 𝔸[F] ↦ (a.1, a.2) : 𝔸[F] → InfiniteAdeleRing F × 𝔸ᶠ[𝓞 F, F]) ∧
    ∀ x : F, (∀ w, (algebraMap F 𝔸[F] x).1 w = algebraMap F w.Completion x) ∧
      ∀ v : Primes(F), (algebraMap F 𝔸[F] x).2 v = algebraMap F (v.adicCompletion F) x := by
  classical
  let _ := moduleTopology ℝ (ℝ ⊗[ℚ] F)
  refine ⟨?_, IsHomeomorph.id, IsHomeomorph.id, ?_⟩
  · let f : (ℝ ⊗[ℚ] F) →ₐ[ℝ] mixedEmbedding.mixedSpace F :=
      AlgHom.liftEquiv ℚ ℝ F _ (mixedEmbedding F).toRatAlgHom
    have hf (x : F) : f (1 ⊗ₜ[ℚ] x) = mixedEmbedding F x := by
      simp [f]
    let b := (integralBasis F).baseChange ℝ
    let l := b.equiv (mixedEmbedding.latticeBasis F) (Equiv.refl _)
    have hfl : f.toLinearMap = l.toLinearMap := by
      apply b.ext
      intro i
      change f (b i) = l (b i)
      rw [show l (b i) = mixedEmbedding.latticeBasis F i from
        Module.Basis.equiv_apply .., mixedEmbedding.latticeBasis_apply]
      simpa only [b, Module.Basis.baseChange_apply] using hf (integralBasis F i)
    let e := AlgEquiv.ofBijective f (show Bijective f.toLinearMap from hfl ▸ l.bijective)
    let h : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
      (Homeomorph.piEquivPiSubtypeProd InfinitePlace.IsReal
        (fun w : InfinitePlace F ↦ w.Completion)).trans
        (Homeomorph.prodCongr
          (Homeomorph.piCongrRight fun w ↦
            (InfinitePlace.Completion.isometryEquivRealOfIsReal w.2).toHomeomorph)
          ((Homeomorph.piCongrRight fun w ↦
            (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
              (InfinitePlace.not_isReal_iff_isComplex.mp w.2)).toHomeomorph).trans
            (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ)
              (Equiv.subtypeEquivRight fun _ ↦ InfinitePlace.not_isReal_iff_isComplex))))
    let g := InfiniteAdeleRing.ringEquiv_mixedSpace F
    have : ContinuousAdd (ℝ ⊗[ℚ] F) := IsModuleTopology.toContinuousAdd ℝ _
    have : IsModuleTopology ℝ (mixedEmbedding.mixedSpace F) := isModuleTopologyOfFiniteDimensional
    refine ⟨e.toRingEquiv.trans g.symm, ?_, ?_, ?_⟩
    · exact h.symm.continuous.comp (IsModuleTopology.continuous_of_linearMap e.toLinearMap)
    · exact (IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap).comp h.continuous
    · intro x
      change g.symm (f (1 ⊗ₜ[ℚ] x)) = _
      rw [hf, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, RingEquiv.symm_apply_apply]
  · intro x
    refine ⟨fun w ↦ ?_, fun _ ↦ rfl⟩
    rw [AdeleRing.algebraMap_fst_apply, AbsoluteValue.Completion.algebraMap_def,
      WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply]

-- TODO(paper-gap): The completion in the introduction to A.1.2 allows every proper ideal.
-- Including the zero ideal gives the discrete topology. The integral factors used in
-- (A.1.2.2) and A.1.5.1 are the local integer rings of the usual profinite completion.

/-- Paper: Lemma A.1.2.1, p. 540. This subring consists of the adeles integral at
every finite place outside the given set. Taking the empty set gives the domain
of the inclusion in (A.1.2.2), and the general case occurs in Lemma A.1.5.1.
Deviation: We use the product of the local integer rings for the profinite completion. -/
def integralAdelesOutside (S : Finset (Primes(F))) : Subring 𝔸[F] :=
  ⨅ (v : Primes(F)) (_ : v ∉ S), (v.adicCompletionIntegers F).toSubring.comap
    ((RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ w.adicCompletion F) v).comp
      (RingHom.snd (InfiniteAdeleRing F) 𝔸ᶠ[𝓞 F, F]))

/-- Paper: Lemma A.1.2.1, p. 540. A diagonal element is integral outside the finite
set precisely when it is an S-integer. -/
theorem diagonal_mem_integralAdelesOutside (S : Finset (Primes(F))) (x : F) :
    algebraMap F 𝔸[F] x ∈ integralAdelesOutside F S ↔ x ∈ (S : Set (Primes(F))).integer F := by
  simp only [integralAdelesOutside, Subring.mem_iInf]
  change (∀ v : Primes(F), v ∉ S → Valued.v (x : v.adicCompletion F) ≤ 1) ↔
    ∀ v : Primes(F), v ∉ S → v.valuation F x ≤ 1
  simp only [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

/-- Paper: Lemma A.1.2.1, p. 541. The diagonal map on S-integers takes values in the
adeles integral outside S. For empty finite part its domain identifies with the integers. -/
def integralAdeleDiagonal (S : Finset (Primes(F))) :
    (S : Set (Primes(F))).integer F →+* integralAdelesOutside F S :=
  ((algebraMap F 𝔸[F]).comp ((S : Set (Primes(F))).integer F).val.toRingHom).codRestrict _
    (fun x ↦ (diagonal_mem_integralAdelesOutside F S x).2 x.property)

local notation "IQuot(" F ", " S ")" =>
  (integralAdelesOutside F S) ⧸ AddMonoidHom.range (RingHom.toAddMonoidHom (integralAdeleDiagonal F S))

/-- Paper: Lemma A.1.2.1, p. 541. An adelic extension of a field embedding is continuous,
extends that embedding on the diagonal, and its component at a place depends only on the
component at the place below. For additive maps this dependence is expressed on kernels. -/
def IsAdeleExtension {L : Type*} [Field L] [NumberField L] (σ : F →+* L) (f : 𝔸[F] →+* 𝔸[L]) :
    Prop :=
  Continuous f ∧ (∀ x, f (algebraMap F 𝔸[F] x) = algebraMap L 𝔸[L] (σ x)) ∧
  (∀ (w : InfinitePlace L) (a : 𝔸[F]), a.1 (w.comap σ) = 0 → (f a).1 w = 0) ∧
  (∀ (v : Primes(F)) (w : Primes(L)), v.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingHom σ) →
    ∀ a : 𝔸[F], a.2 v = 0 → (f a).2 w = 0)

/-- Paper: Lemma A.1.2.1, p. 541. The identity embedding acts by identity on adeles. -/
theorem isAdeleExtension_id : IsAdeleExtension F (RingHom.id F) (RingHom.id 𝔸[F]) := by
  refine ⟨continuous_id, fun _ ↦ rfl, fun _ _ h ↦ h, ?_⟩
  intro v w h
  have hvw : v = w := HeightOneSpectrum.ext (h.trans w.asIdeal.comap_id)
  subst w
  exact fun _ ha ↦ ha

section AdeleAdditiveQuotient

local notation "Principal(" F ")" => AdeleRing.principalSubgroup (𝓞 F) F
local notation "Integral(" F ")" => integralAdelesOutside F ∅
local notation "IntegralPrincipal(" F ")" =>
  AddMonoidHom.range (RingHom.toAddMonoidHom (integralAdeleDiagonal F ∅))

/-- Integrality in the empty-exception model is coordinatewise integrality. -/
private theorem mem_integralAdeles_iff (a : 𝔸[F]) :
    a ∈ Integral(F) ↔ ∀ v : Primes(F), a.2 v ∈ v.adicCompletionIntegers F := by
  simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true, true_implies]
  rfl

/-- The integral adele model is open in the full ring of adeles. -/
private theorem isOpen_integralAdeles : IsOpen (Integral(F) : Set 𝔸[F]) := by
  have h : (Integral(F) : Set 𝔸[F]) =
      Prod.snd ⁻¹' {a : 𝔸ᶠ[𝓞 F, F] | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    Set.ext (mem_integralAdeles_iff F)
  rw [h]
  exact (RestrictedProduct.isOpen_forall_mem (fun v : Primes(F) ↦
    Valued.isOpen_integer (v.adicCompletion F))).preimage continuous_snd

/-- The archimedean adele ring and the mixed space have the same product topology. -/
private def infiniteAdeleMixedHomeomorph : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F := by
  classical
  refine ((Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace F ↦ v.IsReal)
    (fun v ↦ v.Completion))).trans ?_
  exact (Homeomorph.piCongrRight fun v ↦
    (InfinitePlace.Completion.isometryEquivRealOfIsReal v.2).toHomeomorph).prodCongr
      ((Homeomorph.piCongrRight fun v ↦ (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        (InfinitePlace.not_isReal_iff_isComplex.mp v.2)).toHomeomorph).trans
        (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ) <|
          Equiv.subtypeEquivRight fun _ ↦ InfinitePlace.not_isReal_iff_isComplex))

/-- Paper: Lemma A.1.2.1, p. 540. The principal adeles are discrete, since the integral
ones project to the integer lattice in the archimedean factor. -/
private theorem isDiscrete_principalAdeles : IsDiscrete (Principal(F) : Set 𝔸[F]) := by
  let e := infiniteAdeleMixedHomeomorph F
  have hL : IsOpen ({0} : Set (mixedEmbedding.integerLattice F)) := isOpen_discrete _
  obtain ⟨U, hU, hzero⟩ := isOpen_induced_iff.mp hL
  have hzero_mem : (0 : mixedEmbedding.mixedSpace F) ∈ U := by
    have hz : (0 : mixedEmbedding.integerLattice F) ∈ ({0} : Set (mixedEmbedding.integerLattice F)) :=
      Set.mem_singleton _
    rw [← hzero] at hz
    exact hz
  apply isDiscrete_iff_discreteTopology.mpr
  change DiscreteTopology (Principal(F))
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  refine isOpen_induced_iff.mpr ⟨(Integral(F) : Set 𝔸[F]) ∩
    (e ∘ Prod.fst) ⁻¹' U, (isOpen_integralAdeles F).inter
      (hU.preimage (e.continuous.comp continuous_fst)), ?_⟩
  ext a
  constructor
  · rintro ⟨ha, hU'⟩
    obtain ⟨x, hx⟩ := a.property
    have hxInt := (diagonal_mem_integralAdelesOutside F ∅ x).mp (hx ▸ ha)
    simp only [Finset.coe_empty, integer_empty, Algebra.mem_bot] at hxInt
    obtain ⟨r, rfl⟩ := hxInt
    have hr : mixedEmbedding F (algebraMap (𝓞 F) F r) ∈ mixedEmbedding.integerLattice F :=
      ⟨r, rfl⟩
    have he : e (algebraMap F (InfiniteAdeleRing F) (algebraMap (𝓞 F) F r)) =
        mixedEmbedding F (algebraMap (𝓞 F) F r) :=
      (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp (K := F)).symm
    have hm : (⟨_, hr⟩ : mixedEmbedding.integerLattice F) ∈ ({0} : Set _) := by
      rw [← hzero]
      change mixedEmbedding F (algebraMap (𝓞 F) F r) ∈ U
      rw [← he]
      change e (algebraMap F 𝔸[F] (algebraMap (𝓞 F) F r)).1 ∈ U
      rw [hx]
      exact hU'
    have hr0 : algebraMap (𝓞 F) F r = 0 :=
      (mixedEmbedding F).injective (by simpa using congrArg Subtype.val (Set.mem_singleton_iff.mp hm))
    exact Set.mem_singleton_iff.mpr (Subtype.ext (by simpa [hr0] using hx.symm))
  · rintro ha
    have ha' := Set.mem_singleton_iff.mp ha
    subst a
    refine ⟨(Integral(F)).zero_mem, ?_⟩
    change InfiniteAdeleRing.ringEquiv_mixedSpace F 0 ∈ U
    rwa [map_zero]

/-- Every adelic class has a representative integral at all finite places. -/
private theorem exists_sub_diagonal_mem_integralAdeles (a : 𝔸[F]) :
    ∃ x : F, a - algebraMap F 𝔸[F] x ∈ Integral(F) := by
  classical
  let bad := (FiniteAdeleRing.finite_valued_one_lt a.2).toFinset
  have hlocal (v : Primes(F)) : ∃ x : F,
      Valued.v (a.2 v - (x : v.adicCompletion F)) ≤ 1 := by
    let U := (fun y : v.adicCompletion F ↦ a.2 v - y) ⁻¹'
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    have hU : IsOpen U :=
      (Valued.isOpen_integer _).preimage (continuous_const.sub continuous_id)
    have ha : a.2 v ∈ U := by
      change Valued.v (a.2 v - a.2 v) ≤ 1
      simp
    exact (v.denseRange_algebraMap F).mem_nhds (hU.mem_nhds ha)
  choose y hy using hlocal
  let x : Primes(F) → F := fun v ↦ if v ∈ bad then y v else 0
  have hx (v : Primes(F)) : Valued.v (a.2 v - (x v : v.adicCompletion F)) ≤ 1 := by
    by_cases hv : v ∈ bad
    · simpa only [x, ite_eq_left hv] using hy v
    · have hnv : ¬ 1 < Valued.v (a.2 v) := by simpa [bad] using hv
      simpa only [x, ite_eq_right hv, HeightOneSpectrum.adicCompletion.coe_zero, sub_zero] using
        le_of_not_gt hnv
  -- Clear the denominators of the local representatives at the finitely many bad places.
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 F)) bad x
  have hd₀ : (d : 𝓞 F) ≠ 0 := nonZeroDivisors.ne_zero d.property
  have hnum (v : Primes(F)) : ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F r = algebraMap (𝓞 F) F d * x v := by
    by_cases hv : v ∈ bad
    · simpa only [IsLocalization.IsInteger, RingHom.mem_rangeS, Algebra.smul_def] using hd v hv
    · exact ⟨0, by simp [x, hv]⟩
  choose r hr using hnum
  let I : Ideal (𝓞 F) := Ideal.span {(d : 𝓞 F)}
  have hI : I ≠ ⊥ := by simp [I, hd₀]
  have hS : {v : Primes(F) | v.asIdeal ∣ I}.Finite := Ideal.finite_factors hI
  let S := hS.toFinset
  let m := fun v : Primes(F) ↦ multiplicity v.asIdeal I
  -- Match the resulting numerators modulo the prime powers dividing the common denominator.
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S)
    HeightOneSpectrum.asIdeal m (fun v _ ↦ v.prime)
    (fun _ _ _ _ h ↦ fun he ↦ h (HeightOneSpectrum.ext he)) (fun v ↦ r v)
  have hb' (v : Primes(F)) : v.intValuation (b - r v) ≤ v.intValuation d := by
    by_cases hv : v ∈ S
    · rw [v.intValuation_eq_exp_neg_multiplicity hd₀, v.intValuation_le_pow_iff_mem]
      exact hb v hv
    · have hn : ¬ v.asIdeal ∣ I := by simpa [S] using hv
      have hd' : v.intValuation (d : 𝓞 F) = 1 :=
        HeightOneSpectrum.intValuation_eq_one_iff.mpr (mt Ideal.dvd_span_singleton.mpr hn)
      rw [hd']
      exact v.intValuation_le_one _
  let D := algebraMap (𝓞 F) F d
  let z := algebraMap (𝓞 F) F b / D
  refine ⟨z, (mem_integralAdeles_iff F _).mpr fun v ↦ ?_⟩
  have hD : D ≠ 0 := (RingOfIntegers.coe_ne_zero_iff (K := F)).mpr hd₀
  have hz : v.valuation F (x v - z) ≤ 1 := by
    rw [(v.valuation F).map_sub_swap, div_sub', ← hr v, ← map_sub, Valuation.map_div,
      v.valuation_of_algebraMap, v.valuation_of_algebraMap]
    · exact div_le_one_of_le₀ (hb' v) zero_le
    · exact hD
  change Valued.v (a.2 v - (z : v.adicCompletion F)) ≤ 1
  rw [← sub_add_sub_cancel (a.2 v) (x v : v.adicCompletion F) (z : v.adicCompletion F)]
  apply (Valued.v : Valuation (v.adicCompletion F) _).map_add_le (hx v)
  change Valued.v (algebraMap F (v.adicCompletion F) (x v) -
    algebraMap F (v.adicCompletion F) z) ≤ 1
  rw [← map_sub]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) _).trans_le hz

/-- Paper: Lemma A.1.2.1, p. 541. Inclusion of the open integral adele model induces a
topological additive isomorphism on taking the quotient by principal adeles. -/
private theorem integralAdeleQuotient_equiv :
    ∃ e : IQuot(F, ∅) ≃ₜ+ AQuot(F), ∀ x,
      e (QuotientAddGroup.mk' (IntegralPrincipal(F)) x) =
        QuotientAddGroup.mk' (Principal(F)) x.val := by
  let i := (Integral(F)).subtype.toAddMonoidHom
  let P := Principal(F)
  let P₀ := IntegralPrincipal(F)
  have hP : P.comap i = P₀ := by
    ext a
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨⟨x, (diagonal_mem_integralAdelesOutside F ∅ x).mp (hx ▸ a.property)⟩,
        Subtype.ext hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  let e₀ := QuotientAddGroup.map P₀ P i hP.ge
  have hs : Surjective (QuotientAddGroup.mk ∘ i : Integral(F) → AQuot(F)) := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H a =>
      obtain ⟨x, hx⟩ := exists_sub_diagonal_mem_integralAdeles F a
      refine ⟨⟨_, hx⟩, QuotientAddGroup.eq_iff_sub_mem.mpr ?_⟩
      change a - algebraMap F 𝔸[F] x - a ∈ P
      rw [sub_right_comm, sub_self, zero_sub, ← map_neg]
      exact ⟨-x, rfl⟩
  let e := AddEquiv.ofBijective e₀ ⟨(QuotientAddGroup.map_injective_iff P₀ P i _).2 hP.le,
    QuotientAddGroup.map_surjective_of_surjective P₀ P i hs _⟩
  have hq := QuotientAddGroup.isOpenQuotientMap_mk (N := P)
  have hq₀ := QuotientAddGroup.isOpenQuotientMap_mk (N := P₀)
  have hc : Continuous e := hq₀.continuous_comp_iff.mp
    (hq.continuous.comp continuous_subtype_val)
  have ho : IsOpenMap e := hq₀.isOpenMap_iff.mpr
    (hq.isOpenMap.comp (isOpen_integralAdeles F).isOpenMap_subtype_val)
  exact ⟨ContinuousAddEquiv.mk' (e.toEquiv.toHomeomorphOfContinuousOpen hc ho) e.map_add,
    fun _ ↦ rfl⟩

/-- Paper: Lemma A.1.2.1, p. 541. Positive integer multiplication on the quotient is
invertible, since it is invertible on both the adeles and the principal adeles. -/
private theorem adeleQuotient_nsmul_bijective (n : ℕ) (hn : 0 < n) :
    Bijective (fun x : AQuot(F) ↦ n • x) := by
  let P := Principal(F)
  let d := algebraMap F 𝔸[F]
  let q := QuotientAddGroup.mk' P
  have hn' : (n : F) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hmul (a : 𝔸[F]) : n • (d (n : F)⁻¹ * a) = a := by
    rw [nsmul_eq_mul, ← map_natCast d, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hn', map_one,
      one_mul]
  constructor
  · intro a b hab
    induction a using QuotientAddGroup.induction_on with
    | H a =>
      induction b using QuotientAddGroup.induction_on with
      | H b =>
        change n • q a = n • q b at hab
        rw [← map_nsmul, ← map_nsmul] at hab
        obtain ⟨x, hx⟩ := QuotientAddGroup.eq_iff_sub_mem.mp hab
        apply QuotientAddGroup.eq_iff_sub_mem.mpr
        refine ⟨(n : F)⁻¹ * x, ?_⟩
        rw [map_mul, hx, ← nsmul_sub, nsmul_eq_mul, ← map_natCast d, ← mul_assoc, ← map_mul,
          inv_mul_cancel₀ hn', map_one, one_mul]
  · intro a
    induction a using QuotientAddGroup.induction_on with
    | H a =>
      refine ⟨q (d (n : F)⁻¹ * a), ?_⟩
      change n • q (d (n : F)⁻¹ * a) = q a
      rw [← map_nsmul, hmul]

open scoped Valued in
/-- The local integer rings form a compact subset of the finite adeles. -/
private theorem isCompact_integralFiniteAdeles :
    IsCompact {a : 𝔸ᶠ[𝓞 F, F] | ∀ v, a v ∈ v.adicCompletionIntegers F} := by
  let K := fun v : Primes(F) ↦ v.adicCompletion F
  let O := fun v : Primes(F) ↦ (v.adicCompletionIntegers F : Set (K v))
  have (v : Primes(F)) : CompactSpace (v.adicCompletionIntegers F) := by
    have : LocallyCompactSpace (K v) := locallyCompactSpace_adicCompletion v
    exact (Valued.integer.properSpace_iff_compactSpace_integer (K := K v)
      (Γ₀ := WithZero (Multiplicative ℤ))).mp
        (.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _)
  let j : (∀ v : Primes(F), v.adicCompletionIntegers F) → Πʳ v, [K v, O v]_[𝓟 Set.univ] :=
    fun x ↦ ⟨fun v ↦ x v, Eventually.of_forall fun v ↦ (x v).property⟩
  let i := RestrictedProduct.inclusion K O
    (show cofinite ≤ 𝓟 (Set.univ : Set (Primes(F))) by simp)
  have hj : Continuous j := RestrictedProduct.continuous_rng_of_principal.mpr
    (continuous_pi fun v ↦ continuous_subtype_val.comp (continuous_apply v))
  have hc := isCompact_range ((RestrictedProduct.continuous_inclusion _).comp hj :
    Continuous (i ∘ j))
  have h : Set.range (i ∘ j) =
      {a : 𝔸ᶠ[𝓞 F, F] | ∀ v, a v ∈ v.adicCompletionIntegers F} := by
    apply Set.ext
    intro a
    exact ⟨fun ⟨x, hx⟩ v ↦ hx ▸ (x v).property,
      fun ha ↦ ⟨fun v ↦ ⟨a v, ha v⟩, rfl⟩⟩
  rwa [← h]

/-- Paper: Lemma A.1.2.1, p. 540. The adelic quotient is covered by the product of an
archimedean lattice parallelepiped and the compact local integer rings. -/
private theorem compactSpace_adeleQuotient : CompactSpace (AQuot(F)) := by
  classical
  let e := infiniteAdeleMixedHomeomorph F
  let B := mixedEmbedding.latticeBasis F
  let q := QuotientAddGroup.mk' (Principal(F))
  let C : Set 𝔸[F] := (e.symm '' (B.parallelepiped : Set (mixedEmbedding.mixedSpace F))) ×ˢ
    {a : 𝔸ᶠ[𝓞 F, F] | ∀ v, a v ∈ v.adicCompletionIntegers F}
  have hc : IsCompact C :=
    (B.parallelepiped.isCompact.image e.symm.continuous).prod (isCompact_integralFiniteAdeles F)
  have hq : q '' C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H a =>
      obtain ⟨x, hx⟩ := exists_sub_diagonal_mem_integralAdeles F a
      let a' := a - algebraMap F 𝔸[F] x
      obtain ⟨z, hz, _⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B (e a'.1)
      have hz' := (mixedEmbedding.mem_span_latticeBasis F).mp z.property
      obtain ⟨r, hr⟩ : ∃ r : 𝓞 F, mixedEmbedding F (algebraMap (𝓞 F) F r) = z.val := hz'
      let d := algebraMap F 𝔸[F] (algebraMap (𝓞 F) F r)
      refine ⟨a' + d, ⟨?_, ?_⟩, QuotientAddGroup.eq_iff_sub_mem.mpr ?_⟩
      · refine ⟨e (a' + d).1, ?_, e.symm_apply_apply _⟩
        apply ZSpan.fundamentalDomain_subset_parallelepiped B
        change _ + (InfiniteAdeleRing.ringEquiv_mixedSpace F) (a'.1) ∈ _ at hz
        change InfiniteAdeleRing.ringEquiv_mixedSpace F (a'.1 + d.1) ∈ _
        rw [map_add, show d.1 = algebraMap F (InfiniteAdeleRing F) (algebraMap (𝓞 F) F r) from rfl,
          ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, hr, add_comm]
        exact hz
      · have hd : d ∈ Integral(F) := by
          apply (diagonal_mem_integralAdelesOutside F ∅ _).mpr
          simp only [Finset.coe_empty, integer_empty, Algebra.mem_bot]
          exact ⟨r, rfl⟩
        exact (mem_integralAdeles_iff F _).mp ((Integral(F)).add_mem hx hd)
      · change a - algebraMap F 𝔸[F] x + d - a ∈ Principal(F)
        refine ⟨algebraMap (𝓞 F) F r - x, ?_⟩
        rw [map_sub]
        change d - _ = _
        abel
  rw [← isCompact_univ_iff, ← hq]
  exact hc.image QuotientAddGroup.continuous_mk

section AdeleExtension

variable {L : Type*} [Field L] [NumberField L]

/-- The map on archimedean completions is obtained by completing the isometric field embedding
for the absolute value pulled back from the target place. -/
private theorem exists_infiniteAdeleLocalMap (σ : F →+* L) (w : InfinitePlace L) :
    ∃ f : (w.comap σ).Completion →+* w.Completion, Continuous f ∧
      ∀ x : F, f (x : (w.comap σ).Completion) = (σ x : w.Completion) := by
  let := σ.toAlgebra
  have : w.1.LiesOver (w.comap σ).1 := ⟨rfl⟩
  refine ⟨AbsoluteValue.Completion.map (w.comap σ).1 w.1,
    AbsoluteValue.Completion.continuous_map _ _, ?_⟩
  intro x
  exact AbsoluteValue.Completion.map_coe (w.comap σ).1 w.1 (WithAbs.toAbs _ x)

/-- The map on adic completions is obtained from the uniformly continuous field embedding at
a pair of places related by contraction. It sends local integers to local integers. -/
private theorem exists_finiteAdeleLocalMap [Algebra F L] (w : Primes(L)) :
    let v := w.under (𝓞 F)
    ∃ f : v.adicCompletion F →+* w.adicCompletion L, Continuous f ∧
      (∀ x : F, f (algebraMap F (v.adicCompletion F) x) =
        algebraMap L (w.adicCompletion L) (algebraMap F L x)) ∧
      Set.MapsTo f (v.adicCompletionIntegers F) (w.adicCompletionIntegers L) := by
  dsimp only
  let v := w.under (𝓞 F)
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  let g := algebraMap (WithVal (v.valuation F)) (WithVal (w.valuation L))
  have hg := v.uniformContinuous_algebraMap_liesOver F L w
  let e := UniformSpace.Completion.mapRingHom g hg.continuous
  let f := (HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp
    (e.comp (HeightOneSpectrum.adicCompletion.equiv F v).toRingHom)
  have hf : Continuous f := (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L w).comp
    (UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion F v))
  have hd (x : F) : f (algebraMap F (v.adicCompletion F) x) =
      algebraMap L (w.adicCompletion L) (algebraMap F L x) := by
    apply (HeightOneSpectrum.adicCompletion.equiv L w).injective
    exact UniformSpace.Completion.mapRingHom_coe hg.continuous ((WithVal.equiv _).symm x)
  refine ⟨f, hf, hd, ?_⟩
  intro x
  refine (v.denseRange_algebraMap F).induction_on x ?_ ?_
  · convert (Valued.isOpen_integer (v.adicCompletion F)).isClosed_compl.union
      ((Valued.isClosed_integer (w.adicCompletion L)).preimage hf) using 1
    exact Set.ext fun _ ↦ imp_iff_not_or
  · intro y hy
    rw [hd]
    change Valued.v ((algebraMap F L y : L) : w.adicCompletion L) ≤ 1
    change Valued.v (y : v.adicCompletion F) ≤ 1 at hy
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hy ⊢
    rw [← v.valuation_liesOver L w]
    exact pow_le_one₀ zero_le hy

/-- Contraction of finite places along an extension of number fields has finite fibers. -/
private theorem tendsto_cofinite_finitePlace_under [Algebra F L] :
    Tendsto (HeightOneSpectrum.under (𝓞 F) : Primes(L) → Primes(F)) cofinite cofinite := by
  apply Tendsto.cofinite_of_finite_preimage_singleton
  intro v
  apply Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
    (hi := HeightOneSpectrum.asIdeal_injective.injOn)
  apply (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).subset
  rintro _ ⟨w, hw, rfl⟩
  have hv : w.under (𝓞 F) = v := Set.mem_singleton_iff.mp hw
  exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal hv.symm⟩⟩

/-- Paper: Lemma A.1.2.1, p. 541. The local completion embeddings assemble into a
continuous adelic extension that preserves integrality at the finite places. -/
private theorem exists_integralAdeleExtension (σ : F →+* L) :
    ∃ f : 𝔸[F] →+* 𝔸[L], IsAdeleExtension F σ f ∧
      Set.MapsTo f (Integral(F) : Set 𝔸[F]) (Integral(L) : Set 𝔸[L]) := by
  let := σ.toAlgebra
  choose g hg hgDiag using exists_infiniteAdeleLocalMap F σ
  choose h hh hhDiag hhInt using exists_finiteAdeleLocalMap F (L := L)
  let i : InfiniteAdeleRing F →+* InfiniteAdeleRing L :=
    RingHom.pi fun w ↦ (g w).comp (Pi.evalRingHom _ (w.comap σ))
  let k : 𝔸ᶠ[𝓞 F, F] →+* 𝔸ᶠ[𝓞 L, L] :=
    RestrictedProduct.mapAlongRingHom _ _ _ (tendsto_cofinite_finitePlace_under F) h
      (Eventually.of_forall hhInt)
  let f : 𝔸[F] →+* 𝔸[L] := i.prodMap k
  refine ⟨f, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (continuous_pi fun w ↦ (hg w).comp (continuous_apply (w.comap σ))).prodMap
      (RestrictedProduct.mapAlong_continuous _ _ _ (tendsto_cofinite_finitePlace_under F)
        _ (Eventually.of_forall hhInt) hh)
  · intro x
    apply Prod.ext
    · funext w
      change g w ((algebraMap F 𝔸[F] x).1 (w.comap σ)) =
        (algebraMap L 𝔸[L] (σ x)).1 w
      simpa only [AdeleRing.algebraMap_fst_apply] using hgDiag w x
    · apply DFunLike.ext
      intro w
      exact hhDiag w x
  · intro w a ha
    change g w (a.1 (w.comap σ)) = 0
    rw [ha, map_zero]
  · intro v w hv a ha
    have he : w.under (𝓞 F) = v := HeightOneSpectrum.ext hv.symm
    subst v
    change h w (a.2 (w.under (𝓞 F))) = 0
    rw [ha, map_zero]
  · intro a ha
    exact (mem_integralAdeles_iff L _).mpr fun w ↦
      hhInt w ((mem_integralAdeles_iff F a).mp ha (w.under (𝓞 F)))

/-- An additive map out of the adeles that factors through a place is determined by its
values on the diagonal, using a continuous section of the place projection. -/
private theorem adeleLocalMap_eq_on_diagonal {A B : Type*} [AddGroup A] [AddGroup B]
    [TopologicalSpace A] [TopologicalSpace B] [T2Space B] (p : 𝔸[F] →+ A) (j : A → 𝔸[F]) (hj : Continuous j)
    (hpj : ∀ x, p (j x) = x) (hd : DenseRange (p ∘ algebraMap F 𝔸[F]))
    (u v : 𝔸[F] →+ B) (hu : Continuous u) (hv : Continuous v)
    (hu₀ : ∀ a, p a = 0 → u a = 0) (hv₀ : ∀ a, p a = 0 → v a = 0)
    (he : ∀ x : F, u (algebraMap F 𝔸[F] x) = v (algebraMap F 𝔸[F] x)) :
    ∀ a : 𝔸[F], u a = v a := by
  have factor (m : 𝔸[F] →+ B) (hm : ∀ a, p a = 0 → m a = 0) (a : 𝔸[F]) :
      m (j (p a)) = m a := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply hm
    rw [map_sub, hpj, sub_self]
  have hEq : u ∘ j = v ∘ j := hd.equalizer (hu.comp hj) (hv.comp hj) (funext fun x ↦ by
    exact (factor u hu₀ _).trans ((he x).trans (factor v hv₀ _).symm))
  exact fun a ↦ (factor u hu₀ a).symm.trans ((congrFun hEq (p a)).trans (factor v hv₀ a))

/-- Two adelic extensions agree at every place by density of the field in the corresponding
completion and the kernel condition in the definition of an adelic extension. -/
private theorem adeleExtension_unique (σ : F →+* L) {f g : 𝔸[F] →+* 𝔸[L]}
    (hf : IsAdeleExtension F σ f) (hg : IsAdeleExtension F σ g) : f = g := by
  classical
  apply RingHom.ext
  intro a
  apply Prod.ext
  · funext w
    let v := w.comap σ
    let p := ((Pi.evalRingHom (fun w : InfinitePlace F ↦ w.Completion) v).comp
      (RingHom.fst (InfiniteAdeleRing F) (𝔸ᶠ[𝓞 F, F]))).toAddMonoidHom
    let k := ((Pi.evalRingHom (fun w : InfinitePlace L ↦ w.Completion) w).comp
      (RingHom.fst (InfiniteAdeleRing L) (𝔸ᶠ[𝓞 L, L]))).toAddMonoidHom
    let j : v.Completion → 𝔸[F] := fun x ↦ (Pi.single v x, 0)
    have hk : Continuous k := (continuous_apply w).comp continuous_fst
    refine adeleLocalMap_eq_on_diagonal F p j ((continuous_single v).prodMk continuous_const)
      (Pi.single_eq_same v) ?_ (k.comp f.toAddMonoidHom) (k.comp g.toAddMonoidHom)
      (hk.comp hf.1) (hk.comp hg.1) (hf.2.2.1 w) (hg.2.2.1 w) ?_ a
    · have h : Surjective (fun y : InfiniteAdeleRing F ↦ y v) :=
        fun x ↦ ⟨Pi.single v x, Pi.single_eq_same v x⟩
      exact h.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap F) (continuous_apply v)
    · intro x
      exact congrArg k ((hf.2.1 x).trans (hg.2.1 x).symm)
  · apply DFunLike.ext
    intro w
    let := σ.toAlgebra
    let v := w.under (𝓞 F)
    let K := fun v : Primes(F) ↦ v.adicCompletion F
    let O := fun v : Primes(F) ↦ v.adicCompletionIntegers F
    let J := ({v}ᶜ : Set (Primes(F)))
    let j₀ (x : K v) : Πʳ i, [K i, O i]_[𝓟 J] :=
      ⟨Pi.single v x, by
        rw [eventually_principal]
        intro i hi
        exact (Pi.single_eq_of_ne hi x).symm ▸ (O i).zero_mem⟩
    have hj₀ : Continuous j₀ := RestrictedProduct.continuous_rng_of_principal.mpr
      (continuous_single v)
    let i := RestrictedProduct.inclusion K (fun v ↦ (O v : Set (K v)))
      (show cofinite ≤ 𝓟 J by simp [J, le_principal_iff])
    let j : K v → 𝔸[F] := fun x ↦ (0, i (j₀ x))
    have hj : Continuous j := continuous_const.prodMk
      ((RestrictedProduct.continuous_inclusion _).comp hj₀)
    let p := ((RestrictedProduct.evalRingHom K v).comp
      (RingHom.snd (InfiniteAdeleRing F) (𝔸ᶠ[𝓞 F, F]))).toAddMonoidHom
    let k := ((RestrictedProduct.evalRingHom _ w).comp
      (RingHom.snd (InfiniteAdeleRing L) (𝔸ᶠ[𝓞 L, L]))).toAddMonoidHom
    have hk : Continuous k := (RestrictedProduct.continuous_eval w).comp continuous_snd
    refine adeleLocalMap_eq_on_diagonal F p j hj (Pi.single_eq_same v) (v.denseRange_algebraMap F)
      (k.comp f.toAddMonoidHom) (k.comp g.toAddMonoidHom) (hk.comp hf.1) (hk.comp hg.1)
      (hf.2.2.2 v w rfl) (hg.2.2.2 v w rfl) ?_ a
    intro x
    exact congrArg k ((hf.2.1 x).trans (hg.2.1 x).symm)

/-- Paper: Lemma A.1.2.1, p. 541. A continuous adelic extension preserving the integral
model descends to continuous maps on both quotients, with the stated formulas on representatives. -/
private theorem adeleExtension_descends (σ : F →+* L) {f : 𝔸[F] →+* 𝔸[L]}
    (hf : IsAdeleExtension F σ f)
    (hInt : Set.MapsTo f (Integral(F) : Set 𝔸[F]) (Integral(L) : Set 𝔸[L])) :
    ∃ (r : Integral(F) →+ Integral(L)) (c : AQuot(F) →+ AQuot(L))
      (c₀ : IQuot(F, ∅) →+ IQuot(L, ∅)),
      Continuous r ∧ Continuous c ∧ Continuous c₀ ∧ (∀ x, (r x).val = f x.val) ∧
      (∀ a, c (QuotientAddGroup.mk' (Principal(F)) a) =
        QuotientAddGroup.mk' (Principal(L)) (f a)) ∧
      ∀ x, c₀ (QuotientAddGroup.mk' (IntegralPrincipal(F)) x) =
        QuotientAddGroup.mk' (IntegralPrincipal(L)) (r x) := by
  let r := (f.toAddMonoidHom.comp (Integral(F)).subtype.toAddMonoidHom).codRestrict
    (Integral(L)) fun x ↦ hInt x.property
  have hP : Principal(F) ≤ (Principal(L)).comap f.toAddMonoidHom := by
    rintro _ ⟨x, rfl⟩
    exact ⟨σ x, (hf.2.1 x).symm⟩
  have hP₀ : IntegralPrincipal(F) ≤ (IntegralPrincipal(L)).comap r := by
    rintro _ ⟨x, rfl⟩
    have hx : algebraMap L 𝔸[L] (σ x.val) ∈ Integral(L) :=
      hf.2.1 x.val ▸ hInt ((integralAdeleDiagonal F ∅ x).property)
    refine ⟨⟨σ x.val, (diagonal_mem_integralAdelesOutside L ∅ _).mp hx⟩, ?_⟩
    exact Subtype.ext (hf.2.1 x.val).symm
  let c := QuotientAddGroup.map (Principal(F)) (Principal(L)) f.toAddMonoidHom hP
  let c₀ := QuotientAddGroup.map (IntegralPrincipal(F)) (IntegralPrincipal(L)) r hP₀
  have hr : Continuous r := (hf.1.comp continuous_subtype_val).subtype_mk _
  refine ⟨r, c, c₀, hr, ?_, ?_, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩
  · exact QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
      (QuotientAddGroup.continuous_mk.comp hf.1)
  · exact QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
      (QuotientAddGroup.continuous_mk.comp hr)

end AdeleExtension

/-- Paper: Lemma A.1.2.1, p. 540. The diagonal has closed discrete image, the additive
quotient is compact Hausdorff and uniquely divisible, and inclusion of the integral model
induces the displayed isomorphism. A field embedding extends uniquely on adeles and
induces maps on both quotient models which agree on representatives. -/
theorem adele_additive_quotient :
    let d := algebraMap F 𝔸[F]
    let q := QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)
    let q₀ := QuotientAddGroup.mk' (integralAdeleDiagonal F ∅).toAddMonoidHom.range
    Injective d ∧ IsClosed (Set.range d) ∧ IsDiscrete (Set.range d) ∧
    Exact d q ∧ IsOpenQuotientMap q ∧ CompactSpace (AQuot(F)) ∧ T2Space (AQuot(F)) ∧
    (∀ n : ℕ, 0 < n → Bijective (fun x : AQuot(F) ↦ n • x)) ∧
    (∃ e : IQuot(F, ∅) ≃ₜ+ (AQuot(F)), ∀ x, e (q₀ x) = q x.val) ∧
    (∀ (L : Type*) [Field L] [NumberField L] (σ : F →+* L),
      (∃! f : 𝔸[F] →+* 𝔸[L], IsAdeleExtension F σ f) ∧
      ∀ f : 𝔸[F] →+* 𝔸[L], IsAdeleExtension F σ f →
        ∃ (r : integralAdelesOutside F ∅ →+ integralAdelesOutside L ∅)
          (c : AQuot(F) →+ AQuot(L)) (c₀ : IQuot(F, ∅) →+ IQuot(L, ∅)),
          Continuous r ∧ Continuous c ∧ Continuous c₀ ∧ (∀ x, (r x).val = f x.val) ∧
          (∀ a, c (q a) = QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 L) L) (f a)) ∧
          ∀ x, c₀ (q₀ x) = QuotientAddGroup.mk' (integralAdeleDiagonal L ∅).toAddMonoidHom.range (r x)) := by
  dsimp only
  have hdisc := isDiscrete_principalAdeles F
  have : T2Space (InfiniteAdeleRing F) := by
    change T2Space ((v : InfinitePlace F) → v.Completion)
    infer_instance
  have : T2Space (𝔸ᶠ[𝓞 F, F]) := by
    change T2Space (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F])
    infer_instance
  have : T2Space 𝔸[F] := by
    change T2Space (InfiniteAdeleRing F × 𝔸ᶠ[𝓞 F, F])
    infer_instance
  have hclosed : IsClosed (Principal(F) : Set 𝔸[F]) :=
    (Principal(F)).isClosed_of_isDiscrete hdisc
  refine ⟨AdeleRing.algebraMap_injective _ F, hclosed, hdisc, ?_,
    QuotientAddGroup.isOpenQuotientMap_mk, compactSpace_adeleQuotient F, inferInstance,
    adeleQuotient_nsmul_bijective F, integralAdeleQuotient_equiv F, ?_⟩
  · intro a
    exact QuotientAddGroup.eq_zero_iff a
  · intro L _ _ σ
    obtain ⟨f, hf, hInt⟩ := exists_integralAdeleExtension F σ
    refine ⟨⟨f, hf, fun g hg ↦ adeleExtension_unique F σ hg hf⟩, ?_⟩
    intro g hg
    have he := adeleExtension_unique F σ hg hf
    subst g
    exact adeleExtension_descends F σ hf hInt

end AdeleAdditiveQuotient

/-- Paper: Definition A.1.3.1, p. 541. The topology on Mathlib's idele group is induced
by the map recording both an idele and its inverse as adeles. -/
theorem ideleTopology_induced :
    IsInducing (fun x : 𝕀[F] ↦ ((x : 𝔸[F]), (↑x⁻¹ : 𝔸[F]))) := by
  exact (IsInducing.id.prodMap MulOpposite.opHomeomorph.symm.isInducing).comp
    Units.isInducing_embedProduct

-- Remark A.1.3.2 is historical and gives references for adelization.

/-- Paper: Equation (A.1.3.3), p. 541. Mathlib's adelic norm is positive and
multiplicative on units, so it defines a homomorphism to the positive reals. -/
theorem adeleNorm_unit_laws :
    (∀ g : 𝕀[F], 0 < ‖g.val‖) ∧ ∀ g h : 𝕀[F], ‖(g * h).val‖ = ‖g.val‖ * ‖h.val‖ := by
  constructor
  · intro g
    obtain ⟨hinf, hfin, _⟩ := AdeleRing.isUnit_iff.mp g.isUnit
    rw [AdeleRing.norm_apply_of_isUnit g.isUnit]
    apply mul_pos
    · exact Finset.prod_pos fun w _ ↦ pow_pos (norm_pos_iff.mpr (hinf w)) _
    · exact finprod_induction (0 < ·) zero_lt_one (fun _ _ ↦ mul_pos)
        fun v ↦ norm_pos_iff.mpr (hfin v)
  · intro g h
    have hs (u : 𝕀[F]) : (fun v : Primes(F) ↦ ‖u.val.2 v‖).HasFiniteMulSupport :=
      FiniteAdeleRing.hasFiniteMulSupport_norm (MulEquiv.prodUnits u).2
    rw [AdeleRing.norm_apply_of_isUnit (g * h).isUnit, AdeleRing.norm_apply_of_isUnit g.isUnit,
      AdeleRing.norm_apply_of_isUnit h.isUnit]
    change (∏ w : InfinitePlace F, ‖g.val.1 w * h.val.1 w‖ ^ w.mult) *
      (∏ᶠ v : Primes(F), ‖g.val.2 v * h.val.2 v‖) = _
    simp only [norm_mul, mul_pow, Finset.prod_mul_distrib]
    rw [finprod_mul_distrib (hs g) (hs h)]
    ac_rfl

/-- Paper: Equation (A.1.3.3), p. 541. The idelic norm is the adelic norm restricted
to units, with values in the multiplicative group of positive real numbers. -/
def ideleNorm : 𝕀[F] →* ℝ≥0ˣ :=
  MonoidHom.mk' (fun g : 𝕀[F] ↦ Units.mk0 (Real.toNNReal ‖g.val‖)
    (Real.toNNReal_pos.mpr ((adeleNorm_unit_laws F).1 g)).ne')
    (fun g h ↦ Units.ext ((congrArg Real.toNNReal ((adeleNorm_unit_laws F).2 g h)).trans
      (Real.toNNReal_mul ((adeleNorm_unit_laws F).1 g).le)))

/-- Paper: Equation (A.1.3.3), p. 541. The idelic norm is the product of normalized local
norms, with finite support away from infinity and exponent two at the complex places.
Its value on every principal idele is one. -/
theorem ideleNorm_spec :
    (∀ g : 𝕀[F], (fun v : Primes(F) ↦ ‖g.val.2 v‖).HasFiniteMulSupport ∧
      ((ideleNorm F g : ℝ≥0) : ℝ) = (∏ w : InfinitePlace F, ‖g.val.1 w‖ ^ w.mult) *
        ∏ᶠ v : Primes(F), ‖g.val.2 v‖) ∧
    IdeleGroup.principalSubgroup (𝓞 F) F ≤ (ideleNorm F).ker := by
  constructor
  · intro g
    refine ⟨FiniteAdeleRing.hasFiniteMulSupport_norm (MulEquiv.prodUnits g).2, ?_⟩
    change (Real.toNNReal ‖g.val‖ : ℝ) = _
    rw [Real.coe_toNNReal _ ((adeleNorm_unit_laws F).1 g).le,
      AdeleRing.norm_apply_of_isUnit g.isUnit]
  · rintro _ ⟨x, rfl⟩
    apply Units.ext
    change Real.toNNReal ‖algebraMap F 𝔸[F] (x : F)‖ = 1
    rw [AdeleRing.norm_algebraMap_eq_one_of_ne_zero x.ne_zero, Real.toNNReal_one]

/-- Paper: Lemma A.1.3.3, p. 541. The ideles are locally compact Hausdorff and split
coordinatewise into the infinite local unit groups and the restricted product of the finite
local unit groups. The norm is continuous with closed kernel. -/
theorem ideleGroup_topology :
    T2Space 𝕀[F] ∧ LocallyCompactSpace 𝕀[F] ∧ IsTopologicalGroup 𝕀[F] ∧
    (∃ e : 𝕀[F] ≃ₜ* (((v : InfinitePlace F) → v.Completionˣ) ×
      (Πʳ v : Primes(F), [(v.adicCompletion F)ˣ, (v.adicCompletionIntegers F).units])),
      ∀ g, (∀ v, ((e g).1 v).val = g.val.1 v) ∧ ∀ v, ((e g).2 v).val = g.val.2 v) ∧
    Continuous (ideleNorm F) ∧ IsClosed ((ideleNorm F).ker : Set 𝕀[F]) := by
  have hOpen (v : Primes(F)) : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    Valued.isOpen_valuationSubring _
  have hUnits : Fact (∀ v : Primes(F), IsOpen
      ((v.adicCompletionIntegers F).units : Set (v.adicCompletion F)ˣ)) :=
    ⟨fun v ↦ Submonoid.isOpen_units (hOpen v)⟩
  have (v : Primes(F)) : LocallyCompactSpace (v.adicCompletion F) :=
    locallyCompactSpace_adicCompletion v
  have hCompact (v : Primes(F)) : IsCompact
      ((v.adicCompletionIntegers F).units : Set (v.adicCompletion F)ˣ) := by
    let := Valued.toNontriviallyNormedField (v.adicCompletion F) _
    have : ProperSpace (v.adicCompletion F) :=
      .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
    apply Submonoid.units_isCompact
    change IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    convert isCompact_closedBall (0 : v.adicCompletion F) 1 using 1
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
      Metric.mem_closedBall, dist_zero_right, Valued.toNormedField.norm_le_one_iff]
  have : LocallyCompactSpace
      (Πʳ v : Primes(F), [(v.adicCompletion F)ˣ, (v.adicCompletionIntegers F).units]) :=
    RestrictedProduct.locallyCompactSpace_of_group _ (.of_forall hCompact)
  let eInf := ContinuousMulEquiv.piUnits (M := fun v : InfinitePlace F ↦ v.Completion)
  let eFin : (𝔸ᶠ[𝓞 F, F])ˣ ≃ₜ*
      (Πʳ v : Primes(F), [(v.adicCompletion F)ˣ, (v.adicCompletionIntegers F).units]) :=
    restrictedProductUnitsEquiv (fun v : Primes(F) ↦ v.adicCompletionIntegers F) hOpen
  let e := (ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) (𝔸ᶠ[𝓞 F, F])).trans
    (ContinuousMulEquiv.mk' (eInf.toHomeomorph.prodCongr eFin.toHomeomorph)
      (fun x y ↦ Prod.ext (map_mul eInf x.1 y.1) (map_mul eFin x.2 y.2)))
  have hNorm : Continuous (ideleNorm F) := by
    apply Continuous.of_coeHom_comp
    apply continuous_of_continuousAt_one
    have hInf : Continuous (fun g : 𝕀[F] ↦ Real.toNNReal (∏ w : InfinitePlace F,
        ‖g.val.1 w‖ ^ w.mult)) :=
      continuous_real_toNNReal.comp (continuous_finsetProd _ fun w _ ↦
        ((continuous_apply w).comp (continuous_fst.comp Units.continuous_val)).norm.pow _)
    apply hInf.continuousAt.congr
    -- On the open subgroup integral at every finite place, every finite norm is one.
    have hU : {g : 𝕀[F] | ∀ v, (e g).2 v ∈ (v.adicCompletionIntegers F).units} ∈ 𝓝 1 :=
      ((RestrictedProduct.isOpen_forall_mem hUnits.out).preimage e.continuous.snd).mem_nhds
        (by
          change ∀ v : Primes(F), (e (1 : 𝕀[F])).2 v ∈ (v.adicCompletionIntegers F).units
          rw [map_one]
          exact fun v ↦ one_mem (v.adicCompletionIntegers F).units)
    filter_upwards [hU] with g hg
    have hfin : (∏ᶠ v : Primes(F), ‖g.val.2 v‖) = 1 := by
      apply finprod_eq_one_of_forall_eq_one
      intro v
      exact Valued.toNormedField.norm_eq_one_iff.mpr
        (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp (hg v))
    change Real.toNNReal _ = Real.toNNReal ‖g.val‖
    rw [AdeleRing.norm_apply_of_isUnit g.isUnit, hfin, mul_one]
  refine ⟨e.toHomeomorph.isEmbedding.t2Space, e.toHomeomorph.isOpenEmbedding.locallyCompactSpace,
    inferInstance,
    ⟨e, fun _ ↦ ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩⟩, hNorm, ?_⟩
  rw [MonoidHom.coe_ker]
  exact isClosed_singleton.preimage hNorm

/-- Paper: Equation (A.1.3.6), p. 542. The norm on idele classes is the quotient lift
of the product of the normalized local norms. -/
def ideleClassNorm : C[F] →* ℝ≥0ˣ :=
  QuotientGroup.lift _ (ideleNorm F) (ideleNorm_spec F).2

/-- The finite adeles integral at every place form an open subset. -/
private theorem isOpen_finiteAdeles_integral :
    IsOpen {a : 𝔸ᶠ[𝓞 F, F] | ∀ v : Primes(F), a v ∈ v.adicCompletionIntegers F} := by
  change IsOpen {a : Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F] |
    ∀ v : Primes(F), a v ∈ v.adicCompletionIntegers F}
  convert isOpen_restrictedProduct_forall_mem (G := fun v : Primes(F) ↦ v.adicCompletion F)
    (A := fun v ↦ v.adicCompletionIntegers F) Set.univ
    (fun _ _ ↦ Valued.isOpen_valuationSubring _) using 1
  ext a
  exact ⟨fun ha v _ ↦ ha v, fun ha v ↦ ha v (Set.mem_univ v)⟩

/-- The infinite adelic norm is a continuous finite product of powers of local norms. -/
private theorem continuous_infiniteAdeleNorm :
    Continuous (fun a : InfiniteAdeleRing F ↦ ‖a‖) := by
  simp only [InfiniteAdeleRing.norm_def]
  fun_prop

/-- Paper: Lemma A.1.3.4(1), p. 542. The principal ideles are discrete by the product
formula, using the additive neighborhood of infinite norm less than one and finite integrality. -/
private theorem isDiscrete_principalIdeles :
    IsDiscrete (Set.range (IdeleGroup.unitEmbedding (𝓞 F) F)) := by
  let N := AdeleRing.principalSubgroup (𝓞 F) F
  let U : Set 𝔸[F] := {a | ‖a.1‖ < 1 ∧ ∀ v : Primes(F), a.2 v ∈ v.adicCompletionIntegers F}
  have hU : IsOpen U :=
    (isOpen_lt ((continuous_infiniteAdeleNorm F).comp continuous_fst) continuous_const).inter
      ((isOpen_finiteAdeles_integral F).preimage continuous_snd)
  have hzero : (0 : 𝔸[F]) ∈ U := by
    refine ⟨?_, fun v ↦ (v.adicCompletionIntegers F).zero_mem⟩
    change ‖(0 : InfiniteAdeleRing F)‖ < 1
    rw [InfiniteAdeleRing.norm_eq_zero_of_not_isUnit (by simp)]
    exact zero_lt_one
  have hN : DiscreteTopology N := by
    apply discreteTopology_of_isOpen_singleton_zero
    convert hU.preimage (continuous_subtype_val : Continuous ((↑) : N → 𝔸[F])) using 1
    ext a
    obtain ⟨x, hx⟩ := a.property
    have hax : a.val = algebraMap F 𝔸[F] x := hx.symm
    change a = 0 ↔ a.val ∈ U
    refine ⟨fun h ↦ h.symm ▸ hzero, fun h ↦ ?_⟩
    by_contra ha
    have hx₀ : x ≠ 0 := by
      intro h
      apply ha
      apply Subtype.ext
      simp [hax, h]
    rw [hax] at h
    have hu : IsUnit (algebraMap F 𝔸[F] x) := (isUnit_iff_ne_zero.mpr hx₀).map _
    have hfin : ‖(algebraMap F 𝔸[F] x).2‖ ≤ 1 := by
      rw [FiniteAdeleRing.norm_eq_finprod_of_isUnit (Prod.isUnit_iff.mp hu).2,
        ← finprod_one (α := Primes(F))]
      exact finprod_le_finprod₀
        (FiniteAdeleRing.hasFiniteMulSupport_norm (MulEquiv.prodUnits hu.unit).2)
        (fun _ ↦ norm_nonneg _) hasFiniteMulSupport_one
        (fun v ↦ Valued.toNormedField.norm_le_one_iff.mpr (h.2 v))
    have hnorm : ‖algebraMap F 𝔸[F] x‖ < 1 := by
      rw [AdeleRing.norm_def]
      exact (mul_le_of_le_one_right (by rw [InfiniteAdeleRing.norm_def]; positivity) hfin).trans_lt h.1
    exact (AdeleRing.norm_algebraMap_eq_one_of_ne_zero hx₀).not_lt hnorm
  have hrange : Set.range (IdeleGroup.unitEmbedding (𝓞 F) F) =
      Units.val ⁻¹' (N : Set 𝔸[F]) := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, rfl⟩
    · rintro ⟨x, hx⟩
      have hx₀ : x ≠ 0 := by
        intro h
        have : Nontrivial 𝔸[F] := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
        exact g.ne_zero (by simpa [h] using hx.symm)
      exact ⟨Units.mk0 x hx₀, Units.ext hx⟩
  rw [hrange]
  exact (isDiscrete_iff_discreteTopology.mpr hN).preimage
    Units.continuous_val.continuousOn Units.val_injective

/-- Paper: Lemma A.1.3.3, p. 541. The ideles are locally compact because the adele ring
is Hausdorff locally compact and its unit group is closed in the product with its opposite. -/
private theorem adeleHausdorff_ideleLocallyCompact :
    T2Space 𝔸[F] ∧ LocallyCompactSpace 𝕀[F] := by
  have : T2Space 𝔸[F] := by
    change T2Space (((v : InfinitePlace F) → v.Completion) ×
      (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  have (v : Primes(F)) : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  have : Fact (∀ v : Primes(F), IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  have (v : Primes(F)) : CompactSpace (v.adicCompletionIntegers F) := by
    apply isCompact_iff_compactSpace.mp
    convert isCompact_closedBall (0 : v.adicCompletion F) 1 using 1
    ext x
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
      Metric.mem_closedBall, dist_zero_right, Valued.toNormedField.norm_le_one_iff]
  have : LocallyCompactSpace 𝔸ᶠ[𝓞 F, F] := by
    change LocallyCompactSpace (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F])
    infer_instance
  have : LocallyCompactSpace 𝔸[F] := by
    change LocallyCompactSpace (InfiniteAdeleRing F × 𝔸ᶠ[𝓞 F, F])
    infer_instance
  exact ⟨inferInstance, inferInstance⟩

/-- Paper: Lemma A.1.3.3, p. 541. The idelic norm is continuous. Near the identity,
finite components and their inverses are all integral, so only the infinite norm contributes. -/
private theorem continuous_idelicNorm : Continuous (ideleNorm F) := by
  apply Continuous.of_coeHom_comp
  apply continuous_of_continuousAt_one
  let U : Set 𝔸ᶠ[𝓞 F, F] := {a | ∀ v : Primes(F), a v ∈ v.adicCompletionIntegers F}
  have hU : IsOpen U := isOpen_finiteAdeles_integral F
  have h₁ : (1 : 𝔸ᶠ[𝓞 F, F]) ∈ U := fun v ↦ (v.adicCompletionIntegers F).one_mem
  have hval : Continuous (fun g : 𝕀[F] ↦ g.val.2) := continuous_snd.comp Units.continuous_val
  have hinv : Continuous (fun g : 𝕀[F] ↦ g.inv.2) := continuous_snd.comp Units.continuous_coe_inv
  refine ((continuous_real_toNNReal.comp ((continuous_infiniteAdeleNorm F).comp
    (continuous_fst.comp Units.continuous_val))).continuousAt (x := (1 : 𝕀[F]))).congr ?_
  filter_upwards [hval.continuousAt (hU.mem_nhds h₁), hinv.continuousAt (hU.mem_nhds h₁)]
    with g hg hginv
  change Real.toNNReal ‖g.val.1‖ = Real.toNNReal ‖g.val‖
  rw [AdeleRing.norm_def, FiniteAdeleRing.norm_eq_finprod_of_isUnit
    (Prod.isUnit_iff.mp g.isUnit).2]
  have hfinite (v : Primes(F)) : ‖g.val.2 v‖ = 1 := by
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    let eval := (RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ w.adicCompletion F) v).comp
      (RingHom.snd (InfiniteAdeleRing F) 𝔸ᶠ[𝓞 F, F])
    exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := Units.map eval.toMonoidHom g)).mp ⟨hg v, hginv v⟩
  simp [hfinite]

/-- Paper: Lemma A.2.2.6, p. 547. The section of the idelic norm obtained from one infinite
place has finite part one. -/
private theorem exists_ideleNorm_section_finite_one :
    ∃ s : ℝ≥0ˣ →* 𝕀[F], Continuous s ∧ RightInverse s (ideleNorm F) ∧
      ∀ t, (s t).val.2 = 1 := by
  classical
  let v : InfinitePlace F := Classical.choice inferInstance
  let r := (v.mult : ℝ)⁻¹
  have hscalar : ∃ f : ℝ →+* v.Completion, Continuous f ∧ ∀ x, ‖f x‖ = ‖x‖ := by
    open InfinitePlace.Completion in
    by_cases hv : v.IsReal
    · let e := ringEquivRealOfIsReal hv
      have hi : Isometry e.symm := (isometryEquivRealOfIsReal hv).symm.isometry
      exact ⟨e.symm, hi.continuous, hi.norm_map_of_map_zero (map_zero e.symm)⟩
    · have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
      let e := ringEquivComplexOfIsComplex hv'
      have hi : Isometry e.symm := (isometryEquivComplexOfIsComplex hv').symm.isometry
      exact ⟨e.symm.toRingHom.comp Complex.ofRealHom, hi.continuous.comp Complex.continuous_ofReal,
        fun x ↦ (hi.norm_map_of_map_zero (map_zero e.symm) (x : ℂ)).trans (Complex.norm_real x)⟩
  obtain ⟨f, hf, hfnorm⟩ := hscalar
  let p : ℝ≥0ˣ →* v.Completionˣ :=
    Units.map ((f.comp NNReal.toRealHom).toMonoidHom.comp (NNReal.rpowMonoidHom r))
  let s := (IdeleGroup.ofCompletion (𝓞 F) F v).comp p
  refine ⟨s, ?_, ?_, fun _ ↦ rfl⟩
  · change Continuous ((IdeleGroup.ofCompletion (𝓞 F) F v) ∘ p)
    apply Continuous.comp
    · apply Continuous.units_map
      exact (continuous_mulSingle (A := InfinitePlace.Completion) v).prodMk continuous_const
    · apply Continuous.of_coeHom_comp
      exact hf.comp ((Real.continuous_rpow_const (by positivity : 0 ≤ r)).comp
        (NNReal.continuous_coe.comp Units.continuous_val))
  · intro t
    apply Units.ext
    apply NNReal.eq
    rw [((ideleNorm_spec F).1 (s t)).2]
    change (∏ w : InfinitePlace F, ‖Pi.mulSingle v (p t).val w‖ ^ w.mult) *
      (∏ᶠ w : Primes(F), ‖(1 : w.adicCompletion F)‖) = (t.val : ℝ)
    simp only [norm_one, finprod_one, mul_one]
    rw [Finset.prod_eq_single_of_mem v (Finset.mem_univ _), Pi.mulSingle_eq_same]
    · change ‖f ((t.val : ℝ) ^ r)‖ ^ v.mult = (t.val : ℝ)
      rw [hfnorm, Real.norm_of_nonneg (Real.rpow_nonneg t.val.coe_nonneg r),
        ← Real.rpow_mul_natCast t.val.coe_nonneg, inv_mul_cancel₀ v.mult_coe_ne_zero,
        Real.rpow_one]
    · intro w _ hw
      simp only [Pi.mulSingle_eq_of_ne hw, norm_one, one_pow]

/-- Paper: Lemma A.2.2.6, p. 547. Inserting a positive real root at one infinite place
gives a continuous homomorphic section of the idele norm. -/
private theorem exists_ideleNorm_section :
    ∃ s : ℝ≥0ˣ →* 𝕀[F], Continuous s ∧ RightInverse s (ideleNorm F) := by
  obtain ⟨s, hs, hright, _⟩ := exists_ideleNorm_section_finite_one F
  exact ⟨s, hs, hright⟩

/-- Paper: Lemma A.1.3.4, p. 542. Principal ideles form a closed discrete subgroup,
the class group is locally compact Hausdorff, and the descended norm admits a continuous
homomorphic section. Extension along a field embedding commutes with the quotient maps. -/
theorem ideleGroup_quotient :
    let d := IdeleGroup.unitEmbedding (𝓞 F) F
    let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
    Injective d ∧ IsClosed (Set.range d) ∧ IsDiscrete (Set.range d) ∧
    MulExact d q ∧ IsOpenQuotientMap q ∧ T2Space C[F] ∧ LocallyCompactSpace C[F] ∧
    (∀ g, ideleClassNorm F (q g) = ideleNorm F g) ∧
    Continuous (ideleClassNorm F) ∧ Surjective (ideleClassNorm F) ∧
    (∃ s : ℝ≥0ˣ →* C[F], Continuous s ∧ RightInverse s (ideleClassNorm F)) ∧
    (∀ (L : Type*) [Field L] [NumberField L] (σ : F →+* L) (f : 𝔸[F] →+* 𝔸[L]),
      IsAdeleExtension F σ f → ∃ c : C[F] →* C[L], Continuous c ∧
        ∀ g, c (q g) = QuotientGroup.mk (Units.map f.toMonoidHom g)) := by
  dsimp only
  let N := IdeleGroup.principalSubgroup (𝓞 F) F
  obtain ⟨hHausdorff, hLocallyCompact⟩ := adeleHausdorff_ideleLocallyCompact F
  have hdiscrete := isDiscrete_principalIdeles F
  have hclosed : IsClosed (N : Set 𝕀[F]) := N.isClosed_of_isDiscrete hdiscrete
  have hq : IsOpenQuotientMap (QuotientGroup.mk' N) := QuotientGroup.isOpenQuotientMap_mk
  obtain ⟨s, hs, hright⟩ := exists_ideleNorm_section F
  have hsection : RightInverse ((QuotientGroup.mk' N).comp s) (ideleClassNorm F) := hright
  refine ⟨Units.map_injective (AdeleRing.algebraMap_injective (𝓞 F) F), hclosed, hdiscrete,
    QuotientGroup.eq_one_iff, hq, inferInstance, inferInstance, fun _ ↦ rfl,
    hq.continuous_comp_iff.mp (continuous_idelicNorm F), hsection.surjective,
    ⟨_, hq.continuous.comp hs, hsection⟩, ?_⟩
  intro L _ _ σ f hf
  let j := (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 L) L)).comp
    (Units.map f.toMonoidHom)
  have hj : N ≤ j.ker := by
    rintro _ ⟨x, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨Units.map σ.toMonoidHom x, Units.ext (hf.2.1 x.val).symm⟩
  refine ⟨QuotientGroup.lift N j hj, hq.continuous_comp_iff.mp ?_, fun _ ↦ rfl⟩
  exact QuotientGroup.continuous_mk.comp (hf.1.units_map f.toMonoidHom)

/-- Paper: Definition A.1.4.1, p. 542. The idele class group carries the quotient
topology, and two ideles represent the same class precisely when they differ by a
principal idele. -/
theorem ideleClassGroup_description :
    let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
    IsQuotientMap q ∧ ∀ g h, q g = q h ↔ ∃ x : Fˣ, g = IdeleGroup.unitEmbedding (𝓞 F) F x * h := by
  refine ⟨QuotientGroup.isQuotientMap_mk _, fun g h ↦ QuotientGroup.eq_iff_div_mem.trans ?_⟩
  rw [IdeleGroup.principalSubgroup, MonoidHom.mem_range]
  exact exists_congr fun x ↦ eq_div_iff_mul_eq'.trans eq_comm

-- TODO(paper-gap): The sentence after (A.1.4.2) attributes compactness of the kernel
-- to A.1.3.4(3). Existence of a continuous splitting does not imply this. The compactness
-- assertion has its own proof obligation in Theorem A.1.4.3.

/-- Paper: Lemma A.1.2.1, p. 540. The diagonal field is discrete and closed in the adeles. -/
private theorem principalAdeles_closed_discrete :
    IsClosed (Set.range (algebraMap F 𝔸[F])) ∧ IsDiscrete (Set.range (algebraMap F 𝔸[F])) := by
  have : T2Space 𝔸[F] := inferInstanceAs (T2Space (((w : InfinitePlace F) → w.Completion) ×
    (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F])))
  have : IsTopologicalAddGroup 𝔸[F] :=
    inferInstanceAs (IsTopologicalAddGroup (InfiniteAdeleRing F × 𝔸ᶠ[𝓞 F, F]))
  let A := AdeleRing.principalSubgroup (𝓞 F) F
  suffices h : IsDiscrete (A : Set 𝔸[F]) from ⟨A.isClosed_of_isDiscrete h, h⟩
  let archNorm (a : InfiniteAdeleRing F) : ℝ := ∏ w : InfinitePlace F, ‖a w‖ ^ w.mult
  have harch : Continuous archNorm :=
    continuous_finsetProd _ fun w _ ↦ (continuous_apply w).norm.pow _
  let U : Set 𝔸[F] := {a | archNorm a.1 < 1} ∩
    {a | ∀ v : Primes(F), a.2 v ∈ v.adicCompletionIntegers F}
  have hU : IsOpen U := (isOpen_lt (harch.comp continuous_fst) continuous_const).inter
    ((RestrictedProduct.isOpen_forall_mem fun v : Primes(F) ↦
      Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage continuous_snd)
  apply isDiscrete_iff_discreteTopology.mpr
  change DiscreteTopology A
  apply discreteTopology_of_isOpen_singleton_zero
  have hpre : (Subtype.val : A → 𝔸[F]) ⁻¹' U = {0} := by
    ext a
    change a.val ∈ U ↔ a = 0
    constructor
    · rintro ⟨hinf, hfin⟩
      obtain ⟨x, hx⟩ := a.property
      by_contra ha
      have hx₀ : x ≠ 0 := by
        rintro rfl
        exact ha (Subtype.ext (hx.symm.trans (map_zero _)))
      have haUnit : IsUnit a.val := hx ▸ (isUnit_iff_ne_zero.mpr hx₀).map (algebraMap F 𝔸[F])
      have hprod : (∏ᶠ v : Primes(F), ‖a.val.2 v‖) ≤ 1 := by
        refine (finprod_induction (fun r : ℝ ↦ 0 ≤ r ∧ r ≤ 1) ⟨zero_le_one, le_rfl⟩
          (fun _ _ hr hs ↦ ⟨mul_nonneg hr.1 hs.1, (mul_le_of_le_one_right hr.1 hs.2).trans hr.2⟩)
          (fun v ↦ ⟨norm_nonneg _, Valued.toNormedField.norm_le_one_iff.mpr (hfin v)⟩)).2
      have hnorm : ‖a.val‖ = 1 := hx ▸ AdeleRing.norm_algebraMap_eq_one_of_ne_zero hx₀
      rw [AdeleRing.norm_apply_of_isUnit haUnit] at hnorm
      have hnonneg : 0 ≤ archNorm a.val.1 :=
        Finset.prod_nonneg fun w _ ↦ pow_nonneg (norm_nonneg _) _
      have hlt : archNorm a.val.1 * (∏ᶠ v : Primes(F), ‖a.val.2 v‖) < 1 :=
        (mul_le_of_le_one_right hnonneg hprod).trans_lt hinf
      exact hlt.ne hnorm
    · rintro rfl
      refine ⟨?_, fun v ↦ (v.adicCompletionIntegers F).zero_mem⟩
      change archNorm 0 < 1
      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
      have hw : archNorm 0 = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ w)
        change ‖(0 : w.Completion)‖ ^ w.mult = 0
        simp [InfinitePlace.mult_ne_zero]
      rw [hw]
      exact zero_lt_one
  rw [← hpre]
  exact hU.preimage continuous_subtype_val

/-- Paper: Remark A.1.4.2, p. 542. Restricting the quotient map to the norm-one subgroups
gives a strict short exact sequence and the corresponding topological group isomorphism. -/
theorem normOne_idele_quotient :
    let d := IdeleGroup.unitEmbedding (𝓞 F) F
    let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
    ∃ (i : Fˣ →* (ideleNorm F).ker) (p : (ideleNorm F).ker →* (ideleClassNorm F).ker),
      (∀ x, (i x).val = d x) ∧ (∀ x, (p x).val = q x.val) ∧
      Injective i ∧ IsClosed (Set.range i) ∧ IsDiscrete (Set.range i) ∧
      MulExact i p ∧ IsOpenQuotientMap p ∧
      ∃ e : ((ideleNorm F).ker ⧸ i.range) ≃ₜ* (ideleClassNorm F).ker,
        ∀ x, e (QuotientGroup.mk x) = p x := by
  dsimp only
  let d := IdeleGroup.unitEmbedding (𝓞 F) F
  let P := IdeleGroup.principalSubgroup (𝓞 F) F
  let q := QuotientGroup.mk' P
  let i : Fˣ →* (ideleNorm F).ker := d.codRestrict _ (fun x ↦ (ideleNorm_spec F).2 ⟨x, rfl⟩)
  let p : (ideleNorm F).ker →* (ideleClassNorm F).ker :=
    (q.comp (ideleNorm F).ker.subtype).codRestrict _ (fun x ↦ x.property)
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  have hp : IsOpenQuotientMap p := hq.restrictPreimage ((ideleClassNorm F).ker : Set C[F])
  have hd : Injective d := Units.map_injective (AdeleRing.algebraMap_injective (𝓞 F) F)
  have hi : Injective i := fun _ _ h ↦ hd (congrArg Subtype.val h)
  have hexact : MulExact i p := by
    intro x
    change p x = 1 ↔ ∃ y, i y = x
    rw [← Subtype.coe_inj]
    change q x.val = 1 ↔ ∃ y, i y = x
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact exists_congr fun y ↦ ⟨fun h ↦ Subtype.ext h, congrArg Subtype.val⟩
  let val : (ideleNorm F).ker → 𝔸[F] := fun x ↦ x.val.val
  have hrange : Set.range i = val ⁻¹' Set.range (algebraMap F 𝔸[F]) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.val, rfl⟩
    · rintro ⟨y, hy⟩
      have hy₀ : y ≠ 0 := by
        rintro rfl
        have : Nontrivial 𝔸[F] := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
        exact x.val.ne_zero (hy.symm.trans (map_zero _))
      exact ⟨Units.mk0 y hy₀, Subtype.ext (Units.ext hy)⟩
  have hval : Continuous val := Units.continuous_val.comp continuous_subtype_val
  obtain ⟨hclosed, hdiscrete⟩ := principalAdeles_closed_discrete F
  refine ⟨i, p, fun _ ↦ rfl, fun _ ↦ rfl, hi, ?_, ?_, hexact, hp, ?_⟩
  · rw [hrange]
    exact hclosed.preimage hval
  · rw [hrange]
    exact hdiscrete.preimage hval.continuousOn (Units.val_injective.comp Subtype.val_injective)
  · have hker := MonoidHom.mulExact_iff.mp hexact
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective p hp.surjective)
    have he (x : (ideleNorm F).ker) : e (QuotientGroup.mk x) = p x := rfl
    have hmk : IsOpenQuotientMap (QuotientGroup.mk : (ideleNorm F).ker → _ ⧸ i.range) :=
      QuotientGroup.isOpenQuotientMap_mk
    have heOpen : IsOpenQuotientMap e := hmk.of_comp_iff.mp
      (show IsOpenQuotientMap (e ∘ QuotientGroup.mk) by simpa only [Function.comp_def, he] using hp)
    exact ⟨ContinuousMulEquiv.mk'
      (e.toEquiv.toHomeomorphOfContinuousOpen heOpen.continuous heOpen.isOpenMap) (map_mul e), he⟩

/-- Paper: Lemma A.1.3.4, p. 542. Principal ideles form a closed subgroup.
An integral diagonal element whose archimedean coordinates all lie in the open
unit ball centered at one must equal one. -/
private theorem isClosed_principalIdeles :
    IsClosed (IdeleGroup.principalSubgroup (𝓞 F) F : Set 𝕀[F]) := by
  have : T2Space 𝕀[F] := (ideleGroup_topology F).1
  let D := IdeleGroup.principalSubgroup (𝓞 F) F
  apply D.isClosed_of_isDiscrete
  rw [isDiscrete_iff_discreteTopology]
  apply discreteTopology_of_isOpen_singleton_one (G := D)
  let U : Set 𝕀[F] := {g | (∀ w : InfinitePlace F, ‖g.val.1 w - 1‖ < 1) ∧
    ∀ v : Primes(F), g.val.2 v ∈ v.adicCompletionIntegers F}
  have hU : IsOpen U := by
    have hInf : IsOpen (⋂ w : InfinitePlace F, {g : 𝕀[F] | ‖g.val.1 w - 1‖ < 1}) :=
      isOpen_iInter_of_finite fun w ↦
        isOpen_lt ((((continuous_apply w).comp (continuous_fst.comp Units.continuous_val)).sub
          continuous_const).norm) continuous_const
    have hFin := (isOpen_restrictedProduct_forall_mem (A := fun v : Primes(F) ↦
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Set.univ
      (fun v _ ↦ Valued.isOpen_valuationSubring _)).preimage
      (continuous_snd.comp (Units.continuous_val (M := 𝔸[F])))
    convert hInf.inter hFin using 1
    ext g
    simp [U, Set.preimage]
    intro _
    rfl
  have hpre : (Subtype.val : D → 𝕀[F]) ⁻¹' U = {1} := by
    ext g
    constructor
    · rintro ⟨hinf, hfin⟩
      obtain ⟨x, hx⟩ := g.property
      have hv (v : Primes(F)) : v.valuation F ((x : F) - 1) ≤ 1 := by
        have h := hfin v
        rw [← hx] at h
        change Valued.v ((x : F) : v.adicCompletion F) ≤ 1 at h
        rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
        exact (v.valuation F).map_sub_le h (by simp)
      obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hv
      have hsmall (w : InfinitePlace F) :
          ‖algebraMap F (InfiniteAdeleRing F) ((x : F) - 1) w‖ < 1 := by
        have h := hinf w
        rw [← hx] at h
        simpa [map_sub] using h
      have hzero : (x : F) - 1 = 0 := by
        by_contra hne
        have hnorm : ‖algebraMap F (InfiniteAdeleRing F) ((x : F) - 1)‖ < 1 := by
          let z := algebraMap F (InfiniteAdeleRing F) ((x : F) - 1)
          have hpos (w : InfinitePlace F) : 0 < ‖z w‖ ^ w.mult := by
            let f : F →+* w.Completion :=
              (Pi.evalRingHom InfinitePlace.Completion w).comp (algebraMap F (InfiniteAdeleRing F))
            exact pow_pos (norm_pos_iff.mpr ((map_ne_zero f).mpr hne)) _
          have hlt (w : InfinitePlace F) : ‖z w‖ ^ w.mult < (1 : ℝ) :=
            pow_lt_one₀ (norm_nonneg _) (hsmall w) (ne_of_gt w.mult_pos)
          rw [InfiniteAdeleRing.norm_def]
          simpa only [Finset.prod_const_one] using
            (Finset.prod_lt_prod_of_nonempty₀ (s := Finset.univ) (g := fun _ ↦ (1 : ℝ))
              (fun w _ ↦ hpos w) (fun w _ ↦ hlt w) Finset.univ_nonempty)
        rw [InfiniteAdeleRing.coe_norm_eq_abs_norm, ← hy, ← Algebra.coe_norm_int] at hnorm
        have hInt : |Algebra.norm ℤ y| < 1 := by exact_mod_cast hnorm
        have hy0 : Algebra.norm ℤ y = 0 :=
          abs_eq_zero.mp (le_antisymm (Int.lt_add_one_iff.mp hInt) (abs_nonneg _))
        apply hne ((Algebra.norm_eq_zero_iff (R := ℚ)).mp ?_)
        rw [← hy, ← Algebra.coe_norm_int, hy0, Int.cast_zero]
      have hx1 : x = 1 := Units.ext (sub_eq_zero.mp hzero)
      exact Set.mem_singleton_iff.mpr (Subtype.ext (by simpa [hx1] using hx.symm))
    · rintro rfl
      exact ⟨fun w ↦ by change ‖(1 : w.Completion) - 1‖ < 1; simp, fun _ ↦ one_mem _⟩
  exact hpre ▸ hU.preimage continuous_subtype_val

section IdeleCompactness

open scoped nonZeroDivisors WithZero

local notation "FracIdeals" => (FractionalIdeal (𝓞 F)⁰ F)ˣ
local notation "primeUnit" v => (Units.mk0 ((HeightOneSpectrum.asIdeal v) :
  FractionalIdeal (𝓞 F)⁰ F) (FractionalIdeal.coeIdeal_ne_zero.mpr (HeightOneSpectrum.ne_bot v)))

/-- The finite valuation of an idele, with a uniformizer assigned exponent one. -/
private def ideleExponent (g : 𝕀[F]) (v : Primes(F)) : ℤ :=
  -WithZero.log (Valued.v (g.val.2 v))

/-- Almost every finite exponent of an idele is zero. -/
private theorem eventually_ideleExponent_eq_zero (g : 𝕀[F]) :
    ∀ᶠ v in cofinite, ideleExponent F g v = 0 :=
  ((AdeleRing.isUnit_iff.mp g.isUnit).2.2).mono fun v hv ↦ by
    simp [ideleExponent, hv]

/-- The fractional ideal of an idele is the product of the prime ideals raised to its
finite exponents. -/
private def ideleFractionalIdeal : 𝕀[F] →* FracIdeals where
  toFun g := ∏ᶠ v : Primes(F), (primeUnit v) ^ ideleExponent F g v
  map_one' := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    change _ ^ (-WithZero.log (Valued.v (1 : v.adicCompletion F))) = _
    simp
  map_mul' g h := by
    let P (v : Primes(F)) : FracIdeals := primeUnit v
    change (∏ᶠ v, P v ^ ideleExponent F (g * h) v) =
      (∏ᶠ v, P v ^ ideleExponent F g v) * (∏ᶠ v, P v ^ ideleExponent F h v)
    have hs (a : 𝕀[F]) :
        (fun v ↦ P v ^ ideleExponent F a v).HasFiniteMulSupport :=
      eventually_cofinite.mp ((eventually_ideleExponent_eq_zero F a).mono
        fun v hv ↦ by simp [hv])
    rw [← finprod_mul_distrib (hs g) (hs h)]
    apply finprod_congr
    intro v
    rw [← zpow_add]
    congr 1
    change -WithZero.log (Valued.v (g.val.2 v * h.val.2 v)) =
      -WithZero.log (Valued.v (g.val.2 v)) + -WithZero.log (Valued.v (h.val.2 v))
    rw [map_mul, WithZero.log_mul, neg_add]
    · exact (Valuation.ne_zero_iff _).mpr ((AdeleRing.isUnit_iff.mp g.isUnit).2.1 v)
    · exact (Valuation.ne_zero_iff _).mpr ((AdeleRing.isUnit_iff.mp h.isUnit).2.1 v)

/-- The prime factorization of the fractional ideal records the finite valuations. -/
private theorem coe_ideleFractionalIdeal (g : 𝕀[F]) :
    (ideleFractionalIdeal F g : FractionalIdeal (𝓞 F)⁰ F) =
      ∏ᶠ v : Primes(F), (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ ideleExponent F g v := by
  change Units.coeHom _ (∏ᶠ v : Primes(F), (primeUnit v) ^ ideleExponent F g v) = _
  rw [map_finprod]
  · apply finprod_congr
    intro v
    exact Units.val_zpow_eq_zpow_val (primeUnit v) _
  · exact eventually_cofinite.mp ((eventually_ideleExponent_eq_zero F g).mono
      fun v hv ↦ by simp [hv])

/-- The diagonal idele of a field unit determines its principal fractional ideal. -/
private theorem ideleFractionalIdeal_principal (x : Fˣ) :
    ideleFractionalIdeal F (IdeleGroup.unitEmbedding (𝓞 F) F x) = toPrincipalIdeal (𝓞 F) F x := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq (𝓞 F)⁰ (x : F)
  have hn : n ≠ 0 := by
    rintro rfl
    exact x.ne_zero (by rw [← hnd, IsFractionRing.mk'_eq_div, map_zero, zero_div])
  apply Units.ext
  rw [coe_ideleFractionalIdeal, coe_toPrincipalIdeal, ← hnd,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization_principal_fraction (K := F) hn d]
  apply finprod_congr
  intro v
  congr 1
  change -WithZero.log (Valued.v ((x : F) : v.adicCompletion F)) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← hnd,
    HeightOneSpectrum.valuation_of_mk', v.intValuation_if_neg hn,
    v.intValuation_if_neg (nonZeroDivisors.coe_ne_zero d), WithZero.log_div,
    WithZero.log_exp, WithZero.log_exp]
  · ring
  · exact WithZero.exp_ne_zero
  · exact WithZero.exp_ne_zero

/-- If an idele has trivial ideal class, its class has a representative that is
a local unit at every finite place. -/
private theorem exists_integral_fin_idele (g : 𝕀[F])
    (hg : ClassGroup.mk F (ideleFractionalIdeal F g) = 1) :
    ∃ x : Fˣ, ∀ v : Primes(F),
      Valued.v ((g / IdeleGroup.unitEmbedding (𝓞 F) F x).val.2 v) = (1 : ℤᵐ⁰) := by
  obtain ⟨x, hx⟩ := (ClassGroup.mk_eq_one_iff.mp hg).principal
  have hx' : (ideleFractionalIdeal F g : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton _ x := by
    rwa [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coeToSubmodule_spanSingleton]
  have hx0 : x ≠ 0 := fun h ↦ (ideleFractionalIdeal F g).ne_zero
    (hx'.trans (FractionalIdeal.spanSingleton_eq_zero_iff.mpr h))
  let u := Units.mk0 x hx0
  have hI : ideleFractionalIdeal F (g / IdeleGroup.unitEmbedding (𝓞 F) F u) = 1 := by
    rw [map_div, ideleFractionalIdeal_principal, div_eq_one]
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    exact hx'
  refine ⟨u, fun v ↦ ?_⟩
  let a := g / IdeleGroup.unitEmbedding (𝓞 F) F u
  have hc := FractionalIdeal.count_finprod F v (ideleExponent F a)
    (eventually_ideleExponent_eq_zero F a)
  rw [← coe_ideleFractionalIdeal, hI, Units.val_one, FractionalIdeal.count_one] at hc
  have hv : WithZero.log (Valued.v (a.val.2 v)) = 0 := neg_eq_zero.mp hc.symm
  have hv0 : Valued.v (a.val.2 v) ≠ (0 : ℤᵐ⁰) :=
    (Valuation.ne_zero_iff _).mpr ((AdeleRing.isUnit_iff.mp a.isUnit).2.1 v)
  change Valued.v (a.val.2 v) = (1 : ℤᵐ⁰)
  rw [← WithZero.exp_log hv0, hv, WithZero.exp_zero]

/-- The normalized archimedean product is the mixed-space norm. -/
private theorem mixedNorm_infiniteAdele (a : InfiniteAdeleRing F) :
    mixedEmbedding.norm (InfiniteAdeleRing.ringEquiv_mixedSpace F a) = ‖a‖ := by
  rw [InfiniteAdeleRing.norm_def, mixedEmbedding.norm_apply]
  congr 1
  funext w
  congr 1
  by_cases hw : w.IsReal
  · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw]
    change ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (a w)‖ = ‖a w‖
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) (a w)
  · have hw' := InfinitePlace.not_isReal_iff_isComplex.mp hw
    rw [mixedEmbedding.normAtPlace_apply_of_isComplex hw']
    change ‖InfinitePlace.Completion.extensionEmbedding w (a w)‖ = ‖a w‖
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) (a w)

/-- The norm-one archimedean ideles admit compact representatives modulo global units. -/
private theorem exists_compact_infiniteIdeleRepresentatives :
    ∃ K : Set (InfiniteAdeleRing F)ˣ, IsCompact K ∧
      ∀ a : (InfiniteAdeleRing F)ˣ, ‖a.val‖ = (1 : ℝ) →
        ∃ u : (𝓞 F)ˣ, Units.map (algebraMap (𝓞 F) (InfiniteAdeleRing F)).toMonoidHom u * a ∈ K := by
  classical
  let m := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let h : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
    (Homeomorph.piEquivPiSubtypeProd InfinitePlace.IsReal
      (fun w : InfinitePlace F ↦ w.Completion)).trans
      (Homeomorph.prodCongr
        (Homeomorph.piCongrRight fun w ↦
          (InfinitePlace.Completion.isometryEquivRealOfIsReal w.2).toHomeomorph)
        ((Homeomorph.piCongrRight fun w ↦
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
            (InfinitePlace.not_isReal_iff_isComplex.mp w.2)).toHomeomorph).trans
          (Homeomorph.piCongrLeft (Y := fun _ ↦ ℂ)
            (Equiv.subtypeEquivRight fun _ ↦ InfinitePlace.not_isReal_iff_isComplex))))
  let S : Set (mixedEmbedding.mixedSpace F) := closure (mixedEmbedding.fundamentalCone.normLeOne F) ∩
    {z | mixedEmbedding.norm z = 1}
  have hc : IsCompact (closure (mixedEmbedding.fundamentalCone.normLeOne F)) :=
    (mixedEmbedding.fundamentalCone.isBounded_normLeOne F).isCompact_closure
  have hS : IsCompact S :=
    hc.inter_right (isClosed_eq (mixedEmbedding.continuous_norm F) continuous_const)
  let f := fun a : (InfiniteAdeleRing F)ˣ ↦ m a.val
  have hf : IsInducing f :=
    h.isInducing.comp
      (IsOpenUnits.isOpenEmbedding_unitsVal (M := (w : InfinitePlace F) → w.Completion)).isInducing
  have hRange : S ⊆ Set.range f := by
    intro z hz
    have hnorm : ‖m.symm z‖ = (1 : ℝ) := by
      rw [← mixedNorm_infiniteAdele F, RingEquiv.apply_symm_apply]
      exact hz.2
    have hu : IsUnit (m.symm z) := by
      by_contra hu
      rw [InfiniteAdeleRing.norm_eq_zero_of_not_isUnit hu] at hnorm
      exact zero_ne_one hnorm
    obtain ⟨a, ha⟩ := hu
    exact ⟨a, (congrArg m ha).trans (m.apply_symm_apply z)⟩
  refine ⟨f ⁻¹' S, hf.isCompact_preimage' hS hRange, fun a ha ↦ ?_⟩
  have hNorm : mixedEmbedding.norm (m a.val) = 1 :=
    (mixedNorm_infiniteAdele F a.val).trans ha
  obtain ⟨u, hu⟩ := mixedEmbedding.fundamentalCone.exists_unit_smul_mem
    (hNorm.trans_ne one_ne_zero)
  have hm :
      f (Units.map (algebraMap (𝓞 F) (InfiniteAdeleRing F)).toMonoidHom u * a) = u • m a.val := by
    change m (algebraMap (𝓞 F) (InfiniteAdeleRing F) u.val * a.val) = _
    rw [map_mul, IsScalarTower.algebraMap_apply (𝓞 F) F (InfiniteAdeleRing F),
      ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, mixedEmbedding.unitSMul_smul]
  have hn : mixedEmbedding.norm (u • m a.val) = 1 := by
    rw [mixedEmbedding.norm_unit_smul, hNorm]
  refine ⟨u, ?_⟩
  change f _ ∈ S
  rw [hm]
  exact ⟨subset_closure ⟨hu, hn.le⟩, hn⟩

/-- Paper: Theorem A.1.4.3(1), p. 542. The norm-one idele classes are compact. -/
private theorem compactSpace_normOneIdeleClasses : CompactSpace (ideleClassNorm F).ker := by
  classical
  let N := (ideleNorm F).ker
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
  let d := IdeleGroup.unitEmbedding (𝓞 F) F
  have hq (g : 𝕀[F]) : ideleClassNorm F (q g) = ideleNorm F g := rfl
  let p : Fˣ →* N := d.codRestrict N fun x ↦ (ideleNorm_spec F).2 (Set.mem_range_self x)
  let q₁ : N →* (ideleClassNorm F).ker := (q.comp N.subtype).codRestrict _ fun g ↦ by
    change ideleClassNorm F (q g.val) = 1
    exact (hq g.val).trans g.property
  have hq₁ : Continuous q₁ :=
    (QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _
  have hsurj : Surjective q₁ := by
    intro c
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective _ c.val
    have hN : g ∈ N := (hq g).symm.trans ((congrArg (ideleClassNorm F) hg).trans c.property)
    exact ⟨⟨g, hN⟩, Subtype.ext hg⟩
  have hprincipal (x : Fˣ) : q₁ (p x) = 1 := by
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (d x)).mpr (Set.mem_range_self x)

  obtain ⟨e, he⟩ := (ideleGroup_topology F).2.2.2.1
  obtain ⟨A, hA, hRep⟩ := exists_compact_infiniteIdeleRepresentatives F
  let eInf := ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F ↦ w.Completion)
  let B : Set (Πʳ v : Primes(F), [(v.adicCompletion F)ˣ, (v.adicCompletionIntegers F).units]) :=
    {b | ∀ v, b v ∈ (v.adicCompletionIntegers F).units}
  have hBv (v : Primes(F)) : IsCompact ((v.adicCompletionIntegers F).units :
      Set (v.adicCompletion F)ˣ) :=
    Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  have hB : IsCompact B := by
    have hOpen (v : Primes(F)) : IsOpen ((v.adicCompletionIntegers F).units :
        Set (v.adicCompletion F)ˣ) :=
      Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
    have hClosed : IsClosed B := by
      convert isClosed_iInter (fun v ↦
        (hBv v).isClosed.preimage (RestrictedProduct.continuous_eval v)) using 1
      ext b
      simp only [B, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rw [← hClosed.closure_eq]
    exact (isCompact_closure_restrictedProduct_iff (.of_forall fun v ↦ ⟨hBv v, hOpen v⟩) B).mpr
      ⟨_, hBv, .of_forall fun _ ↦ rfl, fun _ hb ↦ hb⟩
  let K : Set 𝕀[F] := e.symm '' ((eInf '' A) ×ˢ B)
  have hK : IsCompact K := ((hA.image eInf.continuous).prod hB).image e.symm.continuous
  let K₁ : Set N := Subtype.val ⁻¹' K
  have hK₁ : IsCompact K₁ :=
    (ideleGroup_topology F).2.2.2.2.2.isClosedEmbedding_subtypeVal.isCompact_preimage hK

  let f := (ClassGroup.mk F).comp (ideleFractionalIdeal F)
  -- Remove the principal fractional ideal, then use a global unit to reduce the infinite part.
  have hSmall (g : N) (hg : f g.val = 1) : ∃ y ∈ K₁, q₁ y = q₁ g := by
    obtain ⟨x, hx⟩ := exists_integral_fin_idele F g.val hg
    let y : N := g / p x
    let atInfinity := Units.map (RingHom.fst (InfiniteAdeleRing F) 𝔸ᶠ[𝓞 F, F]).toMonoidHom
    have hFin : (∏ᶠ v : Primes(F), ‖y.val.val.2 v‖) = 1 :=
      finprod_eq_one_of_forall_eq_one fun v ↦ Valued.toNormedField.norm_eq_one_iff.mpr (hx v)
    have hInf : ‖(atInfinity y.val).val‖ = (1 : ℝ) := by
      have hn := ((ideleNorm_spec F).1 y.val).2
      rw [show ideleNorm F y.val = 1 from y.property, hFin, mul_one] at hn
      exact hn.symm
    obtain ⟨u, hu⟩ := hRep (atInfinity y.val) hInf
    let uF := Units.map (algebraMap (𝓞 F) F).toMonoidHom u
    let z : N := p uF * y
    have hArch : atInfinity z.val =
        Units.map (algebraMap (𝓞 F) (InfiniteAdeleRing F)).toMonoidHom u * atInfinity y.val := by
      apply Units.ext
      change algebraMap F (InfiniteAdeleRing F) (algebraMap (𝓞 F) F u.val) * _ =
        algebraMap (𝓞 F) (InfiniteAdeleRing F) u.val * _
      rw [← IsScalarTower.algebraMap_apply]
      rfl
    have hUnit (v : Primes(F)) : v.valuation F (uF : F) = 1 := by
      have hmul : v.valuation F (uF : F) * v.valuation F (↑uF⁻¹ : F) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      apply le_antisymm (v.valuation_le_one u.val)
      calc
        1 = v.valuation F (uF : F) * v.valuation F (↑uF⁻¹ : F) := hmul.symm
        _ ≤ v.valuation F (uF : F) * 1 := by
          gcongr
          exact v.valuation_le_one (u⁻¹ : (𝓞 F)ˣ).val
        _ = v.valuation F (uF : F) := mul_one _
    refine ⟨z, ?_, ?_⟩
    · change z.val ∈ K
      refine ⟨e z.val, ⟨?_, ?_⟩, e.symm_apply_apply _⟩
      · refine ⟨atInfinity z.val, ?_, ?_⟩
        · rw [hArch]
          exact hu
        · funext w
          exact Units.ext (he z.val |>.1 w).symm
      · intro v
        rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one, (he z.val).2 v]
        change Valued.v (((uF : F) : v.adicCompletion F) * y.val.val.2 v) = 1
        rw [map_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hUnit, one_mul]
        exact hx v
    · simp [z, y, hprincipal]

  -- Choose one norm-one idele for each ideal class occurring in the norm-one subgroup.
  let I := Set.range (fun g : N ↦ f g.val)
  let r (c : I) : N := Classical.choose c.property
  have hr (c : I) : f (r c).val = c.val := Classical.choose_spec c.property
  let U (c : I) := (fun t ↦ q₁ (r c) * t) '' (q₁ '' K₁)
  have hU (c : I) : IsCompact (U c) :=
    (hK₁.image hq₁).image (continuous_const.mul continuous_id)
  refine ⟨?_⟩
  suffices Set.univ = ⋃ c, U c by rw [this]; exact isCompact_iUnion hU
  apply Set.Subset.antisymm (fun a _ ↦ ?_) (Set.subset_univ _)
  obtain ⟨g, rfl⟩ := hsurj a
  let c : I := ⟨f g.val, Set.mem_range_self g⟩
  have hgr : f (g / r c : N).val = 1 := by
    change f (g.val / (r c).val) = 1
    rw [map_div, hr, div_self']
  obtain ⟨y, hy, hyq⟩ := hSmall (g / r c) hgr
  refine Set.mem_iUnion.mpr ⟨c, q₁ y, ⟨y, hy, rfl⟩, ?_⟩
  change q₁ (r c) * q₁ y = q₁ g
  rw [hyq, map_div, mul_comm, div_mul_cancel]

end IdeleCompactness

/-- Paper: Theorem A.1.4.3, p. 542. The norm-one idele classes form a compact Hausdorff
closed subgroup. The units are finitely generated of rank the number of infinite places
minus one, and the ideal class group is finite. -/
theorem ideleClassGroup_finiteness :
    IsClosed ((ideleClassNorm F).ker : Set C[F]) ∧ CompactSpace (ideleClassNorm F).ker ∧
    T2Space (ideleClassNorm F).ker ∧ Group.FG (𝓞 F)ˣ ∧
    Module.finrank ℤ (Additive (𝓞 F)ˣ) = Fintype.card (InfinitePlace F) - 1 ∧
    Finite (ClassGroup (𝓞 F)) ∧ Nonempty (ClassGroup (𝓞 F) ≃* CommRing.Pic (𝓞 F)) := by
  have : IsClosed (IdeleGroup.principalSubgroup (𝓞 F) F : Set 𝕀[F]) :=
    isClosed_principalIdeles F
  have hNorm : Continuous (ideleClassNorm F) :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr (ideleGroup_topology F).2.2.2.2.1
  refine ⟨?_, compactSpace_normOneIdeleClasses F, inferInstance, inferInstance,
    NumberField.Units.finrank_eq F, inferInstance, ⟨ClassGroup.equivPic (𝓞 F)⟩⟩
  rw [MonoidHom.coe_ker]
  exact isClosed_singleton.preimage hNorm

section SAdeles

variable (S : Finset (Primes(F)))

local notation "Oₛ(" F ", " S ")" => Set.integer (S : Set (Primes(F))) F

/-- Paper: Equation (A.1.5.1), p. 543. The S-adele ring is the product of all infinite
completions and the finite completions in S, with the product ring structure and topology. -/
abbrev SAdeleRing := InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)

/-- Paper: Equation (A.1.5.3), p. 543. Projection to the places in S keeps all infinite
coordinates and the selected finite coordinates. Its composite with the diagonal on
S-integers is the paper's inclusion. -/
def adeleProjection : 𝔸[F] →+* SAdeleRing F S :=
  (RingHom.fst _ _).prod (RingHom.pi fun v ↦
    (RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ w.adicCompletion F) v.val).comp
      (RingHom.snd _ _))

/-- Paper: Equation (A.1.5.3), p. 543. On a diagonal S-integer the global integral model
and its projection to S both have the prescribed completion coordinates. -/
theorem sAdele_diagonal_apply (x : Oₛ(F, S)) :
    let a := integralAdeleDiagonal F S x
    a.val = algebraMap F 𝔸[F] x.val ∧
    (∀ w, (adeleProjection F S a.val).1 w = algebraMap F w.Completion x.val) ∧
    ∀ v : S, (adeleProjection F S a.val).2 v = algebraMap F (v.val.adicCompletion F) x.val := by
  exact ⟨rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- Paper: Equation (A.1.5.2), p. 543. The units of the S-adele ring have the subspace
topology and identify coordinatewise with the finite product of local unit groups. -/
theorem sIdeleGroup_description :
    IsInducing (Units.val : (SAdeleRing F S)ˣ → SAdeleRing F S) ∧
    T2Space (SAdeleRing F S)ˣ ∧ LocallyCompactSpace (SAdeleRing F S)ˣ ∧
    ∃ e : (SAdeleRing F S)ˣ ≃ₜ* (((w : InfinitePlace F) → w.Completionˣ) ×
      ((v : S) → (v.val.adicCompletion F)ˣ)),
      ∀ g, (∀ w, ((e g).1 w).val = g.val.1 w) ∧ ∀ v, ((e g).2 v).val = g.val.2 v := by
  have (v : S) : LocallyCompactSpace (v.val.adicCompletion F) :=
    locallyCompactSpace_adicCompletion v.val
  have hOpen := IsOpenUnits.isOpenEmbedding_unitsVal
    (M := ((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F))
  let eInf := ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F ↦ w.Completion)
  let eS := ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)
  let e := (ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) _).trans
    (ContinuousMulEquiv.mk' (eInf.toHomeomorph.prodCongr eS.toHomeomorph)
      (fun x y ↦ Prod.ext (map_mul eInf x.1 y.1) (map_mul eS x.2 y.2)))
  exact ⟨hOpen.isInducing, hOpen.isEmbedding.t2Space, hOpen.locallyCompactSpace, e,
    fun _ ↦ ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩⟩

/-- Paper: Lemma A.1.5.1, p. 543. With its adelic subspace topology, the ring integral
outside S is the product of the S-adeles and the local integer rings outside S. -/
theorem integralAdelesOutside_factors :
    ∃ e : integralAdelesOutside F S ≃+*
        (SAdeleRing F S × ((v : {v : Primes(F) // v ∉ S}) → v.val.adicCompletionIntegers F)),
      Continuous e ∧ Continuous e.symm ∧ ∀ a,
        (e a).1 = adeleProjection F S a.val ∧ ∀ v, ((e a).2 v).val = a.val.2 v.val := by
  classical
  let Outside := {v : Primes(F) // v ∉ S}
  let Factors := SAdeleRing F S × ((v : Outside) → v.val.adicCompletionIntegers F)
  have hmem (a : 𝔸[F]) :
      a ∈ integralAdelesOutside F S ↔
        ∀ v : Primes(F), v ∉ S → a.2 v ∈ v.adicCompletionIntegers F := by
    simp only [integralAdelesOutside, Subring.mem_iInf]
    rfl
  let glue (a : Factors) (v : Primes(F)) : v.adicCompletion F :=
    if hv : v ∈ S then a.1.2 ⟨v, hv⟩ else (a.2 ⟨v, hv⟩).val
  have hglue (a : Factors) (v : Primes(F)) (hv : v ∉ S) :
      glue a v ∈ v.adicCompletionIntegers F := by
    simpa only [glue, dite_eq_right hv] using (a.2 ⟨v, hv⟩).property
  let joinFinite (a : Factors) : 𝔸ᶠ[𝓞 F, F] :=
    ⟨glue a, S.eventually_cofinite_notMem.mono (hglue a)⟩
  let e : integralAdelesOutside F S ≃+* Factors :=
    { toFun := fun a ↦ (adeleProjection F S a.val, fun v ↦
        ⟨a.val.2 v.val, (hmem a.val).mp a.property v.val v.property⟩)
      invFun := fun a ↦ ⟨(a.1.1, joinFinite a), (hmem _).mpr (hglue a)⟩
      left_inv := by
        intro a
        apply Subtype.ext
        refine Prod.ext rfl ?_
        apply RestrictedProduct.ext
        intro v
        change glue _ v = a.val.2 v
        by_cases hv : v ∈ S
        · simp only [glue, dite_eq_left hv]
          rfl
        · simp only [glue, dite_eq_right hv]
      right_inv := by
        intro a
        refine Prod.ext (Prod.ext rfl (funext fun v ↦ ?_)) (funext ?_)
        · change glue a v.val = a.1.2 v
          simp only [glue, dite_eq_left v.property]
        · rintro ⟨v, hv⟩
          apply Subtype.ext
          change glue a v = (a.2 ⟨v, hv⟩).val
          simp only [glue, dite_eq_right hv]
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  have hEval (v : Primes(F)) :
      Continuous (fun a : integralAdelesOutside F S ↦ a.val.2 v) :=
    (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp continuous_subtype_val)
  refine ⟨e, ?_, ?_, fun _ ↦ ⟨rfl, fun _ ↦ rfl⟩⟩
  · exact ((continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_pi fun v : S ↦ hEval v.val)).prodMk
      (continuous_pi fun v : Outside ↦ (hEval v.val).subtype_mk _)
  · refine (Continuous.prodMk (continuous_fst.comp continuous_fst)
      (show Continuous joinFinite from ?_)).subtype_mk _
    apply continuous_restrictedProduct_of_uniform
    · intro v
      change Continuous fun a : Factors ↦ glue a v
      by_cases hv : v ∈ S
      · simp only [glue, dite_eq_left hv]
        exact (continuous_apply (⟨v, hv⟩ : S)).comp (continuous_snd.comp continuous_fst)
      · simp only [glue, dite_eq_right hv]
        exact continuous_subtype_val.comp
          ((continuous_apply (⟨v, hv⟩ : Outside)).comp continuous_snd)
    · exact S.eventually_cofinite_notMem.mono fun v hv a ↦ hglue a v hv

/-- Paper: Lemma A.1.5.1, p. 543. Projection from the adeles integral outside S is
continuous, surjective, and closed.
The omitted coordinates range over a compact product of local integer rings. -/
private theorem integralAdelesOutside_projection :
    let p := (adeleProjection F S).comp (integralAdelesOutside F S).subtype
    Continuous p ∧ Surjective p ∧ IsClosedMap p := by
  classical
  dsimp only
  let K := fun v : Primes(F) ↦ v.adicCompletion F
  let B := (v : {v : Primes(F) // v ∉ S}) → v.val.adicCompletionIntegers F
  have (v : {v : Primes(F) // v ∉ S}) :
      CompactSpace (v.val.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v.val
  let coords (x : SAdeleRing F S × B) (v : Primes(F)) : K v :=
    if hv : v ∈ S then x.1.2 ⟨v, hv⟩ else (x.2 ⟨v, hv⟩).val
  have hInt (x : SAdeleRing F S × B) (v : Primes(F)) (hv : v ∉ S) :
      coords x v ∈ v.adicCompletionIntegers F := by
    simpa only [coords, dite_eq_right hv] using (x.2 ⟨v, hv⟩).property
  let finite (x : SAdeleRing F S × B) : 𝔸ᶠ[𝓞 F, F] :=
    ⟨coords x, S.eventually_cofinite_notMem.mono (hInt x)⟩
  let j (x : SAdeleRing F S × B) : integralAdelesOutside F S :=
    ⟨(x.1.1, finite x), by
      simp only [integralAdelesOutside, Subring.mem_iInf]
      exact hInt x⟩
  have hj : Continuous j := by
    apply Continuous.subtype_mk
    refine (continuous_fst.comp continuous_fst).prodMk
      (continuous_restrictedProduct_of_uniform (f := finite) (fun v ↦ ?_)
        (S.eventually_cofinite_notMem.mono fun v hv x ↦ hInt x v hv))
    change Continuous (fun x ↦ coords x v)
    by_cases hv : v ∈ S
    · simp only [coords, dite_eq_left hv]
      exact (continuous_apply (⟨v, hv⟩ : S)).comp (continuous_snd.comp continuous_fst)
    · simp only [coords, dite_eq_right hv]
      exact continuous_subtype_val.comp
        ((continuous_apply (⟨v, hv⟩ : {v : Primes(F) // v ∉ S})).comp continuous_snd)
  let p := (adeleProjection F S).comp (integralAdelesOutside F S).subtype
  have hpj (x : SAdeleRing F S × B) : p (j x) = x.1 := by
    refine Prod.ext rfl (funext fun v ↦ ?_)
    change coords x v = x.1.2 v
    simp only [coords, dite_eq_left v.property]
  have hs : Surjective j := by
    intro a
    have ha := a.property
    simp only [integralAdelesOutside, Subring.mem_iInf] at ha
    refine ⟨(p a, fun v ↦ ⟨a.val.2 v, ha v v.property⟩), Subtype.ext (Prod.ext rfl ?_)⟩
    apply DFunLike.ext
    intro v
    change coords _ v = a.val.2 v
    by_cases hv : v ∈ S
    · simp only [coords, dite_eq_left hv]
      rfl
    · simp only [coords, dite_eq_right hv]
  refine ⟨(continuous_fst.prodMk (continuous_pi fun v ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).comp continuous_subtype_val,
    fun x ↦ ⟨j (x, 0), hpj _⟩, ?_⟩
  intro C hC
  have h : p '' C = Prod.fst '' (j ⁻¹' C) := by
    rw [show (Prod.fst : SAdeleRing F S × B → SAdeleRing F S) =
      p ∘ j from (funext hpj).symm, Set.image_comp, hs.image_preimage]
  rw [h]
  exact isClosedMap_fst_of_compactSpace _ (hC.preimage hj)

/-- Paper: Lemma A.1.5.1, p. 543. The principal adeles in the integral-outside-S model
are exactly the diagonal S-integers. -/
private theorem principalSubgroup_comap_integralAdelesOutside :
    (AdeleRing.principalSubgroup (𝓞 F) F).comap
        (integralAdelesOutside F S).subtype.toAddMonoidHom =
      (integralAdeleDiagonal F S).toAddMonoidHom.range := by
  ext a
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, (diagonal_mem_integralAdelesOutside F S x).mp (hx ▸ a.property)⟩,
      Subtype.ext hx⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

/-- Paper: Lemma A.1.5.1, p. 543. Inclusion identifies the quotient of the open
integral-outside-S model by its diagonal S-integers with the full additive adelic quotient. -/
private theorem integralAdeleQuotientOutside_equiv :
    ∃ e : IQuot(F, S) ≃ₜ+ AQuot(F), ∀ x,
      e (QuotientAddGroup.mk' (integralAdeleDiagonal F S).toAddMonoidHom.range x) =
        QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F) x.val := by
  let I := integralAdelesOutside F S
  let i := I.subtype.toAddMonoidHom
  let P := AdeleRing.principalSubgroup (𝓞 F) F
  let D := (integralAdeleDiagonal F S).toAddMonoidHom.range
  have hOpen : IsOpen (I : Set 𝔸[F]) := by
    change IsOpen (integralAdelesOutside F S : Set 𝔸[F])
    simp only [integralAdelesOutside, Subring.coe_iInf, Set.iInter_ofPred]
    exact (isOpen_restrictedProduct_forall_mem (↑S : Set (Primes(F)))ᶜ
      (fun v _ ↦ Valued.isOpen_integer (v.adicCompletion F))).preimage continuous_snd
  have hD : P.comap i = D := principalSubgroup_comap_integralAdelesOutside F S
  have hs : Surjective (QuotientAddGroup.mk ∘ i : I → AQuot(F)) := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H a =>
      obtain ⟨x, hx⟩ := exists_sub_diagonal_mem_integralAdeles F a
      have ha : a - algebraMap F 𝔸[F] x ∈ I := by
        simp only [I, integralAdelesOutside, Subring.mem_iInf]
        exact fun v _ ↦ (mem_integralAdeles_iff F _).mp hx v
      refine ⟨⟨_, ha⟩, QuotientAddGroup.eq_iff_sub_mem.mpr ?_⟩
      change a - algebraMap F 𝔸[F] x - a ∈ P
      rw [sub_right_comm, sub_self, zero_sub, ← map_neg]
      exact ⟨-x, rfl⟩
  let e₀ := QuotientAddGroup.map D P i hD.ge
  let e := AddEquiv.ofBijective e₀ ⟨(QuotientAddGroup.map_injective_iff D P i _).2 hD.le,
    QuotientAddGroup.map_surjective_of_surjective D P i hs _⟩
  have hq := QuotientAddGroup.isOpenQuotientMap_mk (N := P)
  have hq₀ := QuotientAddGroup.isOpenQuotientMap_mk (N := D)
  have hc : Continuous e := hq₀.continuous_comp_iff.mp
    (hq.continuous.comp continuous_subtype_val)
  have ho : IsOpenMap e := hq₀.isOpenMap_iff.mpr
    (hq.isOpenMap.comp hOpen.isOpenMap_subtype_val)
  exact ⟨ContinuousAddEquiv.mk' (e.toEquiv.toHomeomorphOfContinuousOpen hc ho) e.map_add,
    fun _ ↦ rfl⟩

/-- Paper: Lemma A.1.5.1, p. 543. The diagonal S-integers are closed and discrete with
compact Hausdorff quotient. Forgetting the outside integral coordinates induces a proper
quotient map, and inclusion identifies its source with the global additive quotient.
Deviation: The final claim of a rational vector space structure is false. -/
theorem sAdele_additive_quotient :
    let p := adeleProjection F S
    let d := (p.comp (integralAdelesOutside F S).subtype).comp (integralAdeleDiagonal F S)
    let q := QuotientAddGroup.mk' d.toAddMonoidHom.range
    let q' := QuotientAddGroup.mk' (integralAdeleDiagonal F S).toAddMonoidHom.range
    Injective d ∧ IsClosed (Set.range d) ∧ IsDiscrete (Set.range d) ∧
    Exact d q ∧ IsOpenQuotientMap q ∧
    CompactSpace (SAdeleRing F S ⧸ d.toAddMonoidHom.range) ∧
    T2Space (SAdeleRing F S ⧸ d.toAddMonoidHom.range) ∧
    (∃ π : IQuot(F, S) →+ (SAdeleRing F S ⧸ d.toAddMonoidHom.range),
      IsProperMap π ∧ IsQuotientMap π ∧ ∀ x, π (q' x) = q (p x.val)) ∧
    ∃ e : IQuot(F, S) ≃ₜ+ (AQuot(F)), ∀ x, e (q' x) =
      QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F) x.val := by
  dsimp only
  let I := integralAdelesOutside F S
  let p := (adeleProjection F S).comp I.subtype
  let i := integralAdeleDiagonal F S
  let d := p.comp i
  let P := AdeleRing.principalSubgroup (𝓞 F) F
  let D := i.toAddMonoidHom.range
  let Q := d.toAddMonoidHom.range
  have hd : Injective d := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    intro x y h
    exact Subtype.ext ((algebraMap F w.Completion).injective
      (congrArg (fun a : SAdeleRing F S ↦ a.1 w) h))
  obtain ⟨hp, hps, hpClosed⟩ := integralAdelesOutside_projection F S
  -- Pull back the closed discrete principal subgroup, then project it injectively.
  have : T2Space 𝔸[F] := by
    change T2Space (((w : InfinitePlace F) → w.Completion) ×
      (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F]))
    infer_instance
  have hP := isDiscrete_principalAdeles F
  have hPClosed : IsClosed (P : Set 𝔸[F]) := P.isClosed_of_isDiscrete hP
  have : DiscreteTopology P := SetLike.isDiscrete_iff_discreteTopology.mp hP
  have hD : (D : Set I) = Subtype.val ⁻¹' (P : Set 𝔸[F]) := by
    change (D : Set I) = ((P.comap I.subtype.toAddMonoidHom : AddSubgroup I) : Set I)
    rw [principalSubgroup_comap_integralAdelesOutside F S]
  have hDClosed : IsClosed (D : Set I) := hD ▸ hPClosed.preimage continuous_subtype_val
  let j (x : D) : P := ⟨x.val.val, Set.mem_preimage.mp (hD ▸ x.property)⟩
  have : DiscreteTopology D := DiscreteTopology.of_continuous_injective
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ : Continuous j)
    (fun _ _ h ↦ Subtype.ext (Subtype.ext (congrArg (fun a : P ↦ a.val) h)))
  let f : D → SAdeleRing F S := p ∘ Subtype.val
  have hf : IsClosedEmbedding f := .of_continuous_injective_isClosedMap
    (hp.comp continuous_subtype_val) (by
      rintro ⟨_, ⟨x, rfl⟩⟩ ⟨_, ⟨y, rfl⟩⟩ h
      exact Subtype.ext (congrArg i (hd h))) (hpClosed.comp hDClosed.isClosedMap_subtype_val)
  have hRange : Set.range f = Set.range d := by
    ext a
    exact ⟨fun ⟨⟨_, ⟨x, rfl⟩⟩, hx⟩ ↦ ⟨x, hx⟩, fun ⟨x, hx⟩ ↦ ⟨⟨i x, ⟨x, rfl⟩⟩, hx⟩⟩
  have hClosed : IsClosed (Q : Set (SAdeleRing F S)) := by
    change IsClosed (Set.range d)
    rw [← hRange]
    exact hf.isClosed_range
  have hDiscrete : IsDiscrete (Set.range d) := hRange ▸ hf.isInducing.isDiscrete_range
  have : T2Space (SAdeleRing F S ⧸ Q) := inferInstance
  -- The global quotient supplies compactness of the source of the induced projection.
  obtain ⟨e, he⟩ := integralAdeleQuotientOutside_equiv F S
  have : CompactSpace (AQuot(F)) := compactSpace_adeleQuotient F
  have : CompactSpace (IQuot(F, S)) := e.toHomeomorph.symm.surjective.compactSpace
    e.toHomeomorph.symm.continuous
  have hmap : D ≤ Q.comap p.toAddMonoidHom := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  let π := QuotientAddGroup.map D Q p.toAddMonoidHom hmap
  have hq := QuotientAddGroup.isOpenQuotientMap_mk (N := Q)
  have hπ : Continuous π := (QuotientAddGroup.isOpenQuotientMap_mk (N := D)).continuous_comp_iff.mp
    (hq.continuous.comp hp)
  have hπs : Surjective π := QuotientAddGroup.map_surjective_of_surjective D Q p.toAddMonoidHom
    (hq.surjective.comp hps) hmap
  exact ⟨hd, hClosed, hDiscrete, fun a ↦ QuotientAddGroup.eq_zero_iff a, hq,
    hπs.compactSpace hπ, inferInstance,
    ⟨π, hπ.isProperMap, IsQuotientMap.of_surjective_continuous hπs hπ, fun _ ↦ rfl⟩, e, he⟩

-- TODO(paper-gap): For F = ℚ and S = {∞}, A_{F,S}/O_{F,S} = ℝ/ℤ.
-- The class of 1/2 has order two, which rules out a ℚ-vector space structure.

/-- Paper: Equation (A.1.5.6), p. 544. The S-idelic norm is the product of the normalized
absolute values at exactly the places of S. -/
def sIdeleNorm : (SAdeleRing F S)ˣ →* ℝ≥0ˣ :=
  (∏ w : InfinitePlace F, ((Units.map nnNormHom.toMonoidHom).comp
    (Units.map ((Pi.evalRingHom _ w).comp (RingHom.fst _ _)).toMonoidHom)) ^ w.mult) *
  ∏ v : S, (Units.map nnNormHom.toMonoidHom).comp
    (Units.map ((Pi.evalRingHom _ v).comp (RingHom.snd _ _)).toMonoidHom)

/-- Paper: Equation (A.1.5.7), p. 544. S-idele classes are units of the adelic ring
integral outside S, modulo diagonal S-units. In particular the outside local unit factors
are part of the numerator. -/
abbrev SIdeleClassGroup := (integralAdelesOutside F S)ˣ ⧸
  (Units.map (integralAdeleDiagonal F S).toMonoidHom).range

/-- Paper: Equation (A.1.5.8), p. 544. On ideles which are units outside S the global
norm equals the S-norm of the projection. In particular the latter kills diagonal S-units. -/
theorem sIdeleNorm_spec :
    let i := (integralAdelesOutside F S).subtype
    let p := (adeleProjection F S).comp i
    (∀ g, ideleNorm F (Units.map i.toMonoidHom g) = sIdeleNorm F S (Units.map p.toMonoidHom g)) ∧
    (Units.map (integralAdeleDiagonal F S).toMonoidHom).range ≤
      ((sIdeleNorm F S).comp (Units.map p.toMonoidHom)).ker := by
  let i := (integralAdelesOutside F S).subtype
  let p := (adeleProjection F S).comp i
  have hnorm (g : (integralAdelesOutside F S)ˣ) :
      ideleNorm F (Units.map i.toMonoidHom g) = sIdeleNorm F S (Units.map p.toMonoidHom g) := by
    let a := Units.map i.toMonoidHom g
    have hmem (x : integralAdelesOutside F S) (v : Primes(F)) (hv : v ∉ S) :
        x.val.2 v ∈ v.adicCompletionIntegers F := by
      have hx := x.property
      simp only [integralAdelesOutside, Subring.mem_iInf] at hx
      exact hx v hv
    have hS : (fun v : Primes(F) ↦ ‖a.val.2 v‖).mulSupport ⊆ (S : Set (Primes(F))) := by
      intro v hv
      by_contra hvS
      let ev := (RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ w.adicCompletion F) v).comp
        (RingHom.snd (InfiniteAdeleRing F) 𝔸ᶠ[𝓞 F, F])
      apply hv
      apply Valued.toNormedField.norm_eq_one_iff.mpr
      exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
        (a := Units.map ev.toMonoidHom a)).mp ⟨hmem g.val v hvS, hmem g.inv v hvS⟩
    apply Units.ext
    apply NNReal.coe_injective
    let evaluate : ((SAdeleRing F S)ˣ →* ℝ≥0ˣ) →* ℝ :=
      NNReal.toRealHom.toMonoidHom.comp
        ((Units.coeHom ℝ≥0).comp (MonoidHom.eval (Units.map p.toMonoidHom g)))
    change ((ideleNorm F a).val : ℝ) = evaluate (sIdeleNorm F S)
    rw [((ideleNorm_spec F).1 a).2, finprod_eq_prod_of_mulSupport_subset _ hS,
      ← Finset.prod_coe_sort S (fun v ↦ ‖a.val.2 v‖)]
    simp only [sIdeleNorm, map_mul, map_prod, map_pow]
    rfl
  refine ⟨hnorm, ?_⟩
  rintro _ ⟨u, rfl⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← hnorm]
  apply MonoidHom.mem_ker.mp
  apply (ideleNorm_spec F).2
  exact ⟨Units.map (Oₛ(F, S)).val.toRingHom.toMonoidHom u, Units.ext rfl⟩

/-- Paper: Equation (A.1.5.8), p. 544. The class norm is the quotient lift of the S-idelic
norm after projection to the coordinates in S. Its kernel is the norm-one S-idele class group. -/
def sIdeleClassNorm : SIdeleClassGroup F S →* ℝ≥0ˣ :=
  QuotientGroup.lift _ ((sIdeleNorm F S).comp (Units.map
    ((adeleProjection F S).comp (integralAdelesOutside F S).subtype).toMonoidHom))
    (sIdeleNorm_spec F S).2

/-- The adeles integral outside the chosen finite set form an open subring. -/
private theorem isOpen_integralAdelesOutside : IsOpen (integralAdelesOutside F S : Set 𝔸[F]) := by
  have h : (integralAdelesOutside F S : Set 𝔸[F]) =
      Prod.snd ⁻¹' {a : 𝔸ᶠ[𝓞 F, F] | ∀ v ∈ (S : Set (Primes(F)))ᶜ,
        a v ∈ v.adicCompletionIntegers F} := by
    ext a
    simp only [SetLike.mem_coe, integralAdelesOutside, Subring.mem_iInf]
    rfl
  rw [h]
  exact (isOpen_restrictedProduct_forall_mem (G := fun v : Primes(F) ↦ v.adicCompletion F)
    (A := fun v ↦ v.adicCompletionIntegers F) ((S : Set (Primes(F)))ᶜ)
    (fun _ _ ↦ Valued.isOpen_valuationSubring _)).preimage continuous_snd

/-- The units of the integral adelic model form an open subgroup of the ideles. -/
private theorem isOpenEmbedding_integralAdeleUnits :
    IsOpenEmbedding (Units.map (integralAdelesOutside F S).subtype.toMonoidHom) := by
  let A := integralAdelesOutside F S
  let j := Units.map A.subtype.toMonoidHom
  refine ⟨⟨(ideleTopology_induced F).of_comp_iff.mp ?_,
    Units.map_injective Subtype.val_injective⟩, ?_⟩
  · have hi : IsInducing (Subtype.val : A → 𝔸[F]) := IsInducing.subtypeVal
    exact (hi.prodMap hi).comp
      ((IsInducing.id.prodMap MulOpposite.opHomeomorph.symm.isInducing).comp
        Units.isInducing_embedProduct)
  · change IsOpen (Set.range j)
    have hrange : Set.range j = (A.toSubmonoid.units : Set 𝕀[F]) := by
      ext g
      exact ⟨fun ⟨x, hx⟩ ↦ hx ▸ ⟨x.val.property, x.inv.property⟩,
        fun hg ↦ ⟨A.toSubmonoid.unitsEquivUnitsType ⟨g, hg⟩, Units.ext rfl⟩⟩
    rw [hrange]
    exact Submonoid.isOpen_units (isOpen_integralAdelesOutside F S)

/-- Paper: Equation (A.1.5.8), p. 544. The S-class norm is the unique descent of the
product norm. It is continuous and surjective, and the norm-one classes are the quotient
of the norm-one representatives by diagonal S-units. -/
theorem sIdeleClassNorm_descent :
    let d := Units.map (integralAdeleDiagonal F S).toMonoidHom
    let q := QuotientGroup.mk' d.range
    let n := (sIdeleNorm F S).comp (Units.map
      ((adeleProjection F S).comp (integralAdelesOutside F S).subtype).toMonoidHom)
    T2Space (SIdeleClassGroup F S) ∧ LocallyCompactSpace (SIdeleClassGroup F S) ∧
    Continuous (sIdeleClassNorm F S) ∧ Surjective (sIdeleClassNorm F S) ∧
    (∀ g, sIdeleClassNorm F S (q g) = n g) ∧
    ∃ e : (n.ker ⧸ d.range.comap n.ker.subtype) ≃ₜ* (sIdeleClassNorm F S).ker,
      ∀ x : n.ker, (e (QuotientGroup.mk x)).val = q x.val := by
  dsimp only
  let A := integralAdelesOutside F S
  let j := Units.map A.subtype.toMonoidHom
  let d := Units.map (integralAdeleDiagonal F S).toMonoidHom
  let q := QuotientGroup.mk' d.range
  let n := (sIdeleNorm F S).comp (Units.map ((adeleProjection F S).comp A.subtype).toMonoidHom)
  let c := sIdeleClassNorm F S
  let D := IdeleGroup.principalSubgroup (𝓞 F) F
  have hj : IsOpenEmbedding j := isOpenEmbedding_integralAdeleUnits F S
  have : T2Space 𝔸[F] := (adeleHausdorff_ideleLocallyCompact F).1
  have : LocallyCompactSpace 𝕀[F] := (adeleHausdorff_ideleLocallyCompact F).2
  have : LocallyCompactSpace Aˣ := hj.locallyCompactSpace
  have hD : (d.range : Set Aˣ) = j ⁻¹' (D : Set 𝕀[F]) := by
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨Units.map (Oₛ(F, S)).val.toRingHom.toMonoidHom u, Units.ext rfl⟩
    · rintro ⟨u, hu⟩
      have huval : u.val ∈ Oₛ(F, S) := by
        apply (diagonal_mem_integralAdelesOutside F S _).mp
        change ((IdeleGroup.unitEmbedding (𝓞 F) F) u).val ∈ A
        rw [hu]
        exact g.val.property
      have huinv : u.inv ∈ Oₛ(F, S) := by
        apply (diagonal_mem_integralAdelesOutside F S _).mp
        change ((IdeleGroup.unitEmbedding (𝓞 F) F) u).inv ∈ A
        rw [hu]
        exact g.inv.property
      let uS := (Oₛ(F, S)).toSubmonoid.unitsEquivUnitsType ⟨u, huval, huinv⟩
      exact ⟨uS, hj.injective ((Units.ext rfl : j (d uS) = _).trans hu)⟩
  have : IsClosed (d.range : Set Aˣ) := by
    rw [hD]
    exact (D.isClosed_of_isDiscrete (isDiscrete_principalIdeles F)).preimage hj.continuous
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  have hn : n = (ideleNorm F).comp j := MonoidHom.ext fun g ↦ ((sIdeleNorm_spec F S).1 g).symm
  have hcont : Continuous n := by
    rw [hn]
    exact (continuous_idelicNorm F).comp hj.continuous
  have hsurj : Surjective n := by
    obtain ⟨s, _, hs, hsfin⟩ := exists_ideleNorm_section_finite_one F
    intro t
    have hmem (a : 𝔸[F]) (ha : a.2 = 1) : a ∈ A := by
      simp only [A, integralAdelesOutside, Subring.mem_iInf]
      intro v _
      change a.2 v ∈ v.adicCompletionIntegers F
      rw [ha]
      exact (v.adicCompletionIntegers F).one_mem
    have ht : s t ∈ A.toSubmonoid.units :=
      ⟨hmem _ (hsfin t), hmem _ (by
        change ((s t)⁻¹ : 𝕀[F]).val.2 = 1
        rw [← map_inv]
        exact hsfin _)⟩
    let g := A.toSubmonoid.unitsEquivUnitsType ⟨s t, ht⟩
    exact ⟨g, by rw [hn]; exact hs t⟩
  refine ⟨inferInstance, inferInstance, hq.continuous_comp_iff.mp hcont,
    fun t ↦ ?_, fun _ ↦ rfl, ?_⟩
  · obtain ⟨g, hg⟩ := hsurj t
    exact ⟨q g, hg⟩
  · let k : n.ker →* c.ker := (q.comp n.ker.subtype).codRestrict c.ker fun x ↦ x.property
    have hk : IsOpenQuotientMap k := hq.restrictPreimage (c.ker : Set (SIdeleClassGroup F S))
    let N := d.range.comap n.ker.subtype
    have hker : N = k.ker := by
      ext x
      change x.val ∈ d.range ↔ k x = 1
      rw [← QuotientGroup.eq_one_iff, Subtype.ext_iff]
      rfl
    let e := QuotientGroup.liftEquiv N hk.surjective hker
    have he (x : n.ker) : e (QuotientGroup.mk x) = k x := rfl
    have hmk : IsOpenQuotientMap (QuotientGroup.mk : n.ker → n.ker ⧸ N) :=
      QuotientGroup.isOpenQuotientMap_mk
    exact ⟨ContinuousMulEquiv.mk' (e.toEquiv.toHomeomorphOfContinuousOpen
      (hmk.continuous_comp_iff.mp hk.continuous) (hmk.isOpenMap_iff.mpr hk.isOpenMap))
      e.map_mul, fun x ↦ congrArg Subtype.val (he x)⟩

open scoped nonZeroDivisors in
/-- Paper: Theorem A.1.5.2(3), p. 544. The Picard group of the S-integers is finite
because every ideal of the localization extends an ideal of the ring of integers. -/
private theorem finite_sInteger_picard : Finite (CommRing.Pic (Oₛ(F, S))) := by
  let R := 𝓞 F
  let A := Oₛ(F, S)
  let f : R →+* A := algebraMap R A
  have hf : Injective f := fun x y h ↦
    IsFractionRing.injective R F (congrArg (fun a : Oₛ(F, S) ↦ (a : F)) h)
  apply Finite.of_surjective ((ClassGroup.equivPic A).toMonoidHom.comp (ClassGroup.map f hf))
  intro c
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective ((ClassGroup.equivPic A).symm c)
  let I : Ideal R := J.val.under R
  have hmap : I.map f = J.val :=
    IsLocalization.map_under (Localization.submonoid (S : Set (Primes(F)))) A J.val
  have hI : I ≠ ⊥ := by
    intro he
    rw [he, Ideal.map_bot] at hmap
    exact (nonZeroDivisors.ne_zero J.property) hmap.symm
  refine ⟨ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI⟩, ?_⟩
  rw [MonoidHom.comp_apply, ClassGroup.map_mk0]
  change ClassGroup.equivPic A (ClassGroup.mk0 _) = c
  rw [show (⟨I.map f, _⟩ : (Ideal A)⁰) = J from Subtype.ext hmap, hJ, MulEquiv.apply_symm_apply]

open scoped Classical nonZeroDivisors in
/-- Every prime ideal has a principal power with exponent the class number.
A generator has valuation `exp (-classNumber F)` there and valuation one elsewhere. -/
private theorem exists_prime_power_generator (v : Primes(F)) :
    ∃ x : Fˣ, ∀ w : Primes(F),
      w.valuation F (x : F) = if w = v then WithZero.exp (-(classNumber F : ℤ)) else 1 := by
  classical
  let n := classNumber F
  have hv : v.asIdeal ∈ (Ideal (𝓞 F))⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot
  have hpow : (ClassGroup.mk0 ⟨v.asIdeal, hv⟩) ^ n = 1 := pow_card_eq_one
  have hp : (v.asIdeal ^ n).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem hv n), ← hpow, ← map_pow]
    rfl
  obtain ⟨a, ha⟩ := hp
  change v.asIdeal ^ n = Ideal.span {a} at ha
  have ha₀ : a ≠ 0 := by
    rintro rfl
    exact (pow_ne_zero n v.ne_bot) (by simpa using ha)
  have haF : algebraMap (𝓞 F) F a ≠ 0 := fun h ↦
    ha₀ (IsFractionRing.injective (𝓞 F) F (h.trans (map_zero _).symm))
  refine ⟨Units.mk0 _ haF, fun w ↦ ?_⟩
  change w.valuation F (algebraMap (𝓞 F) F a) = _
  rw [w.valuation_of_algebraMap]
  by_cases h : w = v
  · subst w
    rw [ite_eq_left rfl, v.intValuation_eq_exp_neg_multiplicity ha₀]
    have hmult : multiplicity v.asIdeal (Ideal.span {a}) = n := by
      rw [← ha]
      refine multiplicity_eq_of_dvd_of_not_dvd dvd_rfl ?_
      rw [pow_dvd_pow_iff v.ne_bot (mt Ideal.isUnit_iff.mp v.isPrime.ne_top)]
      exact Nat.not_succ_le_self n
    rw [hmult]
  · rw [ite_eq_right h, w.intValuation_eq_one_iff]
    intro hd
    have hw : w.asIdeal ∣ v.asIdeal ^ n := ha.symm ▸ (Ideal.dvd_span_singleton.mpr hd)
    have hle : v.asIdeal ≤ w.asIdeal :=
      w.isPrime.le_of_pow_le (Ideal.dvd_iff_le.mp hw)
    exact h (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm)

/-- Paper: Theorem A.1.5.2(2), p. 544. The S-unit group is finitely generated and its
rank is the ordinary unit rank plus the number of finite places in S. -/
private theorem sInteger_units_finiteness :
    Group.FG (Oₛ(F, S))ˣ ∧ Module.finrank ℤ (Additive (Oₛ(F, S))ˣ) =
      Fintype.card (InfinitePlace F) + S.card - 1 := by
  classical
  let i := Units.map (algebraMap (𝓞 F) (Oₛ(F, S))).toMonoidHom
  let d := Units.map (Oₛ(F, S)).val.toRingHom.toMonoidHom
  let f := i.toAdditive.toIntLinearMap
  let ord : Additive (Oₛ(F, S))ˣ →ₗ[ℤ] (S → ℤ) :=
    LinearMap.pi fun v ↦ ((v.val.valuationOfNeZero : Fˣ →* Multiplicative ℤ).comp d)
      |>.toAdditive |>.toIntLinearMap
  have hfi : Injective f := Units.map_injective (fun x y h ↦
    IsFractionRing.injective (𝓞 F) F (congrArg (fun a : Oₛ(F, S) ↦ (a : F)) h))
  have hval (u : (Oₛ(F, S))ˣ) (v : S) :
      WithZero.exp (ord (.ofMul u) v) = v.val.valuation F ((u.val : Oₛ(F, S)) : F) :=
    v.val.valuationOfNeZero_eq (d u)
  have hexact : Exact f ord := by
    intro a
    change ord a = 0 ↔ ∃ b : Additive (𝓞 F)ˣ, i b.toMul = a.toMul
    constructor
    · intro h
      let u := a.toMul
      have hu (v : Primes(F)) : v.valuation F (u.val : F) = 1 := by
        by_cases hv : v ∈ S
        · have hu := hval u ⟨v, hv⟩
          change WithZero.exp (ord a _) = _ at hu
          simpa [h] using hu.symm
        · exact (Set.unitEquivUnitsInteger _ F).symm u |>.property v hv
      obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (u.val : F)
        (fun v ↦ (hu v).le)
      have hinv : (u.inv : F) = (u.val : F)⁻¹ :=
        Units.val_inv_eq_inv_val (d u)
      obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (u.inv : F)
        (fun v ↦ by rw [hinv, map_inv₀, hu, inv_one])
      have hxy : x * y = 1 := (IsFractionRing.injective (𝓞 F) F) (by
        rw [map_mul, hx, hy, map_one]
        exact congrArg Subtype.val u.val_inv)
      let b : (𝓞 F)ˣ := ⟨x, y, hxy, (mul_comm y x).trans hxy⟩
      exact ⟨.ofMul b, Units.ext (Subtype.ext hx)⟩
    · rintro ⟨b, hb⟩
      have hfb : f b = a := hb
      rw [← hfb]
      funext v
      apply WithZero.exp_inj.mp
      change WithZero.exp (ord (.ofMul (i b.toMul)) v) = WithZero.exp ((0 : S → ℤ) v)
      rw [hval, Pi.zero_apply, WithZero.exp_zero]
      change v.val.valuation F (algebraMap (𝓞 F) F b.toMul.val) = 1
      rw [v.val.valuation_of_algebraMap]
      apply eq_one_of_one_le_mul_left (v.val.intValuation_le_one _)
        (v.val.intValuation_le_one b.toMul.inv)
      rw [← map_mul, Units.val_inv, map_one]
  have hrange : Module.finrank ℤ ord.range = S.card := by
    let n : ℤ := classNumber F
    have hn : n ≠ 0 := Int.natCast_ne_zero.mpr (classNumber_ne_zero F)
    let m : (S → ℤ) →ₗ[ℤ] (S → ℤ) := DistribSMul.toLinearMap ℤ _ (-n)
    have hm : Injective m := fun x y h ↦ funext fun v ↦ by
      have hv : -n * x v = -n * y v := congrFun h v
      exact mul_left_cancel₀ (neg_ne_zero.mpr hn) hv
    have hsingle (v : S) : Pi.single v (-n) ∈ ord.range := by
      obtain ⟨x, hx⟩ := exists_prime_power_generator F v.val
      let u : (S : Set (Primes(F))).unit F := ⟨x, fun w hw ↦ by
        change w.valuation F (x : F) = 1
        rw [hx, ite_eq_right (show w ≠ v.val from fun e ↦ hw (e.symm ▸ v.property))]⟩
      refine ⟨.ofMul (Set.unitEquivUnitsInteger _ F u), ?_⟩
      funext w
      apply WithZero.exp_inj.mp
      rw [hval]
      change w.val.valuation F (x : F) = _
      rw [hx]
      by_cases h : w = v
      · subst w
        simp [n]
      · rw [ite_eq_right (fun e ↦ h (Subtype.ext e)), Pi.single_eq_of_ne h, WithZero.exp_zero]
    have hle : m.range ≤ ord.range := by
      rintro _ ⟨x, rfl⟩
      rw [show m x = ∑ v : S, x v • Pi.single v (-n) from by
        funext w
        simp [m, Finset.sum_apply, Pi.single_apply, mul_comm]]
      exact Submodule.sum_mem _ fun v _ ↦ Submodule.smul_mem _ _ (hsingle v)
    have hcard : Module.finrank ℤ (S → ℤ) = S.card := by
      simp
    apply le_antisymm ((Submodule.finrank_le _).trans_eq hcard)
    rw [← hcard, ← LinearMap.finrank_range_of_inj hm]
    exact Submodule.finrank_mono hle
  have hk : ord.ker = f.range := hexact.linearMap_ker_eq
  have : Module.Finite ℤ ord.ker := hk ▸ inferInstanceAs (Module.Finite ℤ f.range)
  have : Module.Finite ℤ (_ ⧸ ord.ker) := Module.Finite.equiv ord.quotKerEquivRange.symm
  have : Module.Finite ℤ (Additive (Oₛ(F, S))ˣ) := Module.Finite.of_submodule_quotient ord.ker
  have hr := ord.ker.finrank_quotient_add_finrank
  rw [ord.quotKerEquivRange.finrank_eq, hk, LinearMap.finrank_range_of_inj hfi,
    NumberField.Units.finrank_eq, NumberField.Units.rank, hrange] at hr
  have hfg : AddGroup.FG (Additive (Oₛ(F, S))ˣ) :=
    Module.Finite.iff_addGroup_fg.mp inferInstance
  refine ⟨AddGroup.fg_iff_mul_fg.mp hfg, ?_⟩
  have hpos : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
  omega

/-- The S-idele classes embed as an open subgroup of the global idele class group,
and this embedding preserves the norm. -/
private theorem sIdeleClassGroup_openEmbedding :
    ∃ j : SIdeleClassGroup F S →* C[F], IsOpenEmbedding j ∧
      (∀ c, ideleClassNorm F (j c) = sIdeleClassNorm F S c) ∧
      ∀ u : (integralAdelesOutside F S)ˣ, j (QuotientGroup.mk u) =
        QuotientGroup.mk (Units.map (integralAdelesOutside F S).subtype.toMonoidHom u) := by
  let A := integralAdelesOutside F S
  let i := Units.map A.subtype.toMonoidHom
  let d := Units.map (integralAdeleDiagonal F S).toMonoidHom
  let P := IdeleGroup.principalSubgroup (𝓞 F) F
  let q := QuotientGroup.mk' P
  let qS := QuotientGroup.mk' d.range
  have hA : IsOpen (A : Set 𝔸[F]) := by
    have h := isOpen_restrictedProduct_forall_mem (G := fun v : Primes(F) ↦ v.adicCompletion F)
      (A := fun v ↦ v.adicCompletionIntegers F) (↑S : Set (Primes(F)))ᶜ
      (fun v _ ↦ Valued.isOpen_valuationSubring (v.adicCompletion F))
    have he : (A : Set 𝔸[F]) = Prod.snd ⁻¹'
        {a : 𝔸ᶠ[𝓞 F, F] | ∀ v ∈ (↑S : Set (Primes(F)))ᶜ,
          a v ∈ v.adicCompletionIntegers F} := by
      ext x
      change x ∈ A ↔ _
      simp only [A, integralAdelesOutside, Subring.mem_iInf]
      rfl
    rw [he]
    exact h.preimage continuous_snd
  have hiVal : IsEmbedding (A.subtype : A → 𝔸[F]) := IsEmbedding.subtypeVal
  have hiEmb : IsEmbedding i := by
    refine IsEmbedding.of_comp
      (hiVal.continuous.units_map A.subtype.toMonoidHom) Units.isEmbedding_embedProduct.continuous ?_
    exact (hiVal.prodMap (MulOpposite.opHomeomorph.isEmbedding.comp
      (hiVal.comp MulOpposite.opHomeomorph.symm.isEmbedding))).comp Units.isEmbedding_embedProduct
  have hrange : Set.range i = {g : 𝕀[F] | g.val ∈ A ∧ g.inv ∈ A} := by
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.val.property, u.inv.property⟩
    · rintro ⟨hg, hg'⟩
      exact ⟨⟨⟨g.val, hg⟩, ⟨g.inv, hg'⟩, Subtype.ext g.val_inv, Subtype.ext g.inv_val⟩,
        Units.ext rfl⟩
  have hiOpen : IsOpenEmbedding i :=
    ⟨hiEmb, hrange ▸ (hA.preimage Units.continuous_val).inter
      (hA.preimage Units.continuous_coe_inv)⟩
  have hker : (q.comp i).ker = d.range := by
    ext u
    change QuotientGroup.mk (i u) = (1 : C[F]) ↔ u ∈ d.range
    rw [QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨x, hx⟩
      have hxVal : algebraMap F 𝔸[F] x.val = u.val.val := congrArg Units.val hx
      have hxInv : algebraMap F 𝔸[F] x.inv = u.inv.val := congrArg Units.inv hx
      let y : Oₛ(F, S)ˣ :=
        ⟨⟨x.val, (diagonal_mem_integralAdelesOutside F S x.val).mp (hxVal ▸ u.val.property)⟩,
         ⟨x.inv, (diagonal_mem_integralAdelesOutside F S x.inv).mp (hxInv ▸ u.inv.property)⟩,
         Subtype.ext x.val_inv, Subtype.ext x.inv_val⟩
      exact ⟨y, Units.ext (Subtype.ext hxVal)⟩
    · rintro ⟨x, rfl⟩
      exact ⟨Units.map (Oₛ(F, S)).val.toRingHom.toMonoidHom x, Units.ext rfl⟩
  let j := QuotientGroup.lift d.range (q.comp i) hker.ge
  have hj (u : Aˣ) : j (qS u) = q (i u) := rfl
  have hqS : IsOpenQuotientMap qS := QuotientGroup.isOpenQuotientMap_mk
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  have hji : Injective j := by
    apply (MonoidHom.ker_eq_bot_iff j).mp
    rw [Subgroup.eq_bot_iff_forall]
    intro c hc
    obtain ⟨u, rfl⟩ := hqS.surjective c
    rw [MonoidHom.mem_ker, hj] at hc
    have hu : u ∈ (q.comp i).ker := hc
    rw [hker] at hu
    exact (QuotientGroup.eq_one_iff u).mpr hu
  refine ⟨j, .of_continuous_injective_isOpenMap
    (hqS.continuous_comp_iff.mp (hq.continuous.comp hiOpen.continuous)) hji
    (hqS.isOpenMap_iff.mpr (hq.isOpenMap.comp hiOpen.isOpenMap)), ?_, hj⟩
  intro c
  obtain ⟨u, rfl⟩ := hqS.surjective c
  exact (sIdeleNorm_spec F S).1 u

open NumberField.Units.dirichletUnitTheorem in
/-- The norm-one classes of ideles that are local units at every finite place lie in a
compact set. Ordinary units reduce the archimedean logarithms to a bounded domain. -/
private theorem exists_compact_integralIdeleClass_cover :
    ∃ K : Set C[F], IsCompact K ∧ ∀ g : 𝕀[F], ideleNorm F g = 1 →
      (∀ v : Primes(F), Valued.v (g.val.2 v) = 1) →
      QuotientGroup.mk g ∈ K := by
  classical
  let b := (NumberField.Units.basisUnitLattice F).ofZLatticeBasis ℝ
  obtain ⟨r, hr⟩ := (ZSpan.fundamentalDomain_isBounded b).subset_closedBall 0
  let R : ℝ := Real.exp ((Fintype.card (InfinitePlace F) + 1 : ℝ) * max r 0)
  obtain ⟨_, _, _, ⟨e, he⟩, _, _⟩ := ideleGroup_topology F
  let finiteBox : Set (Πʳ v : Primes(F), [(v.adicCompletion F)ˣ,
      (v.adicCompletionIntegers F).units]) := {x | ∀ v, x v ∈ (v.adicCompletionIntegers F).units}
  have hLocal (v : Primes(F)) :
      IsCompact ((v.adicCompletionIntegers F).units : Set (v.adicCompletion F)ˣ) := by
    have : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
    apply Submonoid.units_isCompact
    change IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    convert isCompact_closedBall (0 : v.adicCompletion F) 1 using 1
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
      Metric.mem_closedBall, dist_zero_right, Valued.toNormedField.norm_le_one_iff]
  have hfiniteBox : IsCompact (closure finiteBox) :=
    (isCompact_closure_restrictedProduct_iff
      (Filter.Eventually.of_forall fun v ↦ ⟨hLocal v,
        Submonoid.isOpen_units (Valued.isOpen_valuationSubring (v.adicCompletion F))⟩) finiteBox).mpr
      ⟨_, hLocal, Filter.Eventually.of_forall fun _ ↦ rfl, fun _ hx ↦ hx⟩
  let arch (w : InfinitePlace F) : Set w.Completionˣ :=
    {u | ‖u.val‖ ≤ R ∧ ‖u.inv‖ ≤ R}
  have hArch (w : InfinitePlace F) : IsCompact (arch w) := by
    have he := InfinitePlace.Completion.isometry_extensionEmbedding w
    have hBall : IsCompact (Metric.closedBall (0 : w.Completion) R) := by
      have h := he.isClosedEmbedding.isCompact_preimage
        (isCompact_closedBall (InfinitePlace.Completion.extensionEmbedding w 0) R)
      convert h using 1
      ext z
      simp only [Set.mem_preimage, Metric.mem_closedBall, he.dist_eq]
    have h := hBall.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.mpr hBall)
    convert (Units.isClosedEmbedding_embedProduct (α := w.Completion)).isCompact_preimage h using 1
    ext u
    simp only [arch, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod,
      Metric.mem_closedBall, dist_zero_right]
    rfl
  let B := (Set.univ.pi arch) ×ˢ closure finiteBox
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
  refine ⟨q '' (e ⁻¹' B),
    (e.toHomeomorph.isCompact_preimage.mpr ((isCompact_univ_pi hArch).prod hfiniteBox)).image
      QuotientGroup.continuous_mk, ?_⟩
  intro g hg hgFin
  let L (a : 𝕀[F]) (w : InfinitePlace F) := (w.mult : ℝ) * Real.log ‖a.val.1 w‖
  have hnz (a : 𝕀[F]) (w : InfinitePlace F) : a.val.1 w ≠ 0 := by
    let ev := (Pi.evalRingHom _ w).comp (RingHom.fst (InfiniteAdeleRing F) 𝔸ᶠ[𝓞 F, F])
    exact (Units.map ev.toMonoidHom a).ne_zero
  have hLmul (a t : 𝕀[F]) (w : InfinitePlace F) : L (a * t) w = L a w + L t w := by
    change (w.mult : ℝ) * Real.log ‖a.val.1 w * t.val.1 w‖ = _
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hnz a w))
      (norm_ne_zero_iff.mpr (hnz t w)), mul_add]
  let x : logSpace F := fun w ↦ L g w.val
  obtain ⟨l, hl, _⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b x
  have hl' : l.val ∈ NumberField.Units.unitLattice F := by
    rw [← (NumberField.Units.basisUnitLattice F).ofZLatticeBasis_span ℝ]
    exact l.property
  obtain ⟨u, _, hu⟩ := hl'
  let uF := Units.map (algebraMap (𝓞 F) F).toMonoidHom u.toMul
  let t := IdeleGroup.unitEmbedding (𝓞 F) F uF
  let a := g * t
  have ht : ideleNorm F t = 1 := (ideleNorm_spec F).2 ⟨uF, rfl⟩
  have ha : ideleNorm F a = 1 := by rw [show a = g * t from rfl, map_mul, hg, ht, mul_one]
  have haFin (v : Primes(F)) : Valued.v (a.val.2 v) = 1 := by
    change Valued.v (g.val.2 v * (algebraMap (𝓞 F) F u.toMul.val : v.adicCompletion F)) = 1
    rw [Valuation.map_mul, hgFin, one_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      v.valuation_of_algebraMap]
    apply eq_one_of_one_le_mul_left (v.intValuation_le_one _) (v.intValuation_le_one u.toMul.inv)
    rw [← map_mul, Units.val_inv, map_one]
  have hrest : (fun w : {w : InfinitePlace F // w ≠ w₀} ↦ L a w.val)
      ∈ ZSpan.fundamentalDomain b := by
    convert hl using 1
    funext w
    rw [hLmul]
    change L g w.val + L t w.val = l.val w + x w
    rw [add_comm, show x w = L g w.val from rfl, ← hu]
    congr 1
    change (w.val.mult : ℝ) * Real.log ‖(algebraMap F 𝔸[F] (uF : F)).1 w.val‖ =
      NumberField.Units.logEmbedding F u w
    rw [AdeleRing.algebraMap_fst_apply, AbsoluteValue.Completion.norm_coe]
    rfl
  have hsum : ∑ w, L a w = 0 := by
    have hprod := (ideleNorm_spec F).1 a |>.2
    have hfin : (∏ᶠ v : Primes(F), ‖a.val.2 v‖) = 1 :=
      finprod_eq_one_of_forall_eq_one fun v ↦ Valued.toNormedField.norm_eq_one_iff.mpr (haFin v)
    rw [ha, hfin, mul_one] at hprod
    have h' := congrArg Real.log hprod.symm
    simpa [L, Real.log_prod (fun w _ ↦ pow_ne_zero _ (norm_ne_zero_iff.mpr (hnz a w))),
      Real.log_pow] using h'
  have hrestBound (w : {w : InfinitePlace F // w ≠ w₀}) :
      |L a w.val| ≤ max r 0 :=
    (norm_le_pi_norm _ w).trans ((mem_closedBall_zero_iff.mp (hr hrest)).trans (le_max_left _ _))
  have hbound (w : InfinitePlace F) :
      |L a w| ≤ (Fintype.card (InfinitePlace F) + 1 : ℝ) * max r 0 := by
    have hr₀ : 0 ≤ max r 0 := le_max_right _ _
    by_cases hw : w = w₀
    · subst w
      rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀,
        add_eq_zero_iff_eq_neg] at hsum
      rw [hsum, abs_neg]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply (Finset.sum_le_sum fun j _ ↦ hrestBound j).trans
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      gcongr
      exact_mod_cast (Fintype.card_subtype_le
        (fun w : InfinitePlace F ↦ w ≠ w₀) |>.trans (Nat.le_succ _))
    · refine (hrestBound ⟨w, hw⟩).trans ?_
      exact le_mul_of_one_le_left hr₀ (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have hArchMem (w : InfinitePlace F) : (e a).1 w ∈ arch w := by
    have hlog : |Real.log ‖((e a).1 w).val‖| ≤
        (Fintype.card (InfinitePlace F) + 1 : ℝ) * max r 0 := by
      rw [(he a).1 w]
      apply le_trans _ (hbound w)
      dsimp only [L]
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg w.mult : 0 ≤ (w.mult : ℝ))]
      exact le_mul_of_one_le_left (abs_nonneg _) (by exact_mod_cast w.mult_pos)
    have hpos : 0 < ‖((e a).1 w).val‖ := norm_pos_iff.mpr ((e a).1 w).ne_zero
    refine ⟨(Real.log_le_iff_le_exp hpos).mp ((le_abs_self _).trans hlog), ?_⟩
    change ‖(((e a).1 w)⁻¹).val‖ ≤ R
    rw [Units.val_inv_eq_inv_val, norm_inv]
    exact (Real.log_le_iff_le_exp (inv_pos.mpr hpos)).mp
      (by rw [Real.log_inv]; exact (neg_le_abs _).trans hlog)
  refine ⟨a, ⟨fun w _ ↦ hArchMem w, subset_closure ?_⟩, ?_⟩
  · intro v
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one, (he a).2 v]
    exact haFin v
  · change q (g * t) = q g
    simp only [map_mul, show q t = 1 from (QuotientGroup.eq_one_iff t).mpr ⟨uF, rfl⟩]
    exact mul_one (q g)

/-- The valuation vectors at the places in S, reduced modulo the class number, give
finitely many representatives up to principal ideles and ideles that are local units
at every finite place. The representatives can all be taken to have norm one. -/
private theorem exists_finite_normOne_sIdele_representatives :
    ∃ T : Set 𝕀[F], T.Finite ∧ ∀ g : 𝕀[F], ideleNorm F g = 1 →
      (∀ v : Primes(F), v ∉ S → Valued.v (g.val.2 v) = 1) →
      ∃ r ∈ T, ∃ h : 𝕀[F], ideleNorm F h = 1 ∧
        (∀ v : Primes(F), Valued.v (h.val.2 v) = 1) ∧
        (QuotientGroup.mk g : C[F]) = QuotientGroup.mk r * QuotientGroup.mk h := by
  classical
  let n := classNumber F
  have : NeZero n := ⟨classNumber_ne_zero F⟩
  let P := IdeleGroup.principalSubgroup (𝓞 F) F
  let q := QuotientGroup.mk' P
  let d := IdeleGroup.unitEmbedding (𝓞 F) F
  have hne (v : Primes(F)) (g : 𝕀[F]) : Valued.v (g.val.2 v) ≠ 0 := by
    let ev := (RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ w.adicCompletion F) v).comp
      (RingHom.snd (InfiniteAdeleRing F) 𝔸ᶠ[𝓞 F, F])
    exact (map_ne_zero _).mpr (Units.map ev.toMonoidHom g).ne_zero
  let ν (v : Primes(F)) : 𝕀[F] →* Multiplicative ℤ :=
    { toFun := fun g ↦ .ofAdd (WithZero.log (Valued.v (g.val.2 v)))
      map_one' := by
        change Multiplicative.ofAdd (WithZero.log (Valued.v (1 : v.adicCompletion F))) = 1
        rw [map_one, WithZero.log_one]
        rfl
      map_mul' := fun g h ↦ by
        change Multiplicative.ofAdd (WithZero.log (Valued.v (g.val.2 v * h.val.2 v))) =
          Multiplicative.ofAdd (WithZero.log (Valued.v (g.val.2 v)) +
            WithZero.log (Valued.v (h.val.2 v)))
        rw [Valuation.map_mul, WithZero.log_mul (hne v g) (hne v h)] }
  have hν (v : Primes(F)) (g : 𝕀[F]) :
      WithZero.exp (ν v g).toAdd = Valued.v (g.val.2 v) := WithZero.exp_log (hne v g)
  let α (g : 𝕀[F]) (v : S) : ZMod n := ((ν v.val g).toAdd : ℤ)
  let U (k : S → ZMod n) := {g : 𝕀[F] | ideleNorm F g = 1 ∧
    (∀ v : Primes(F), v ∉ S → Valued.v (g.val.2 v) = 1) ∧ α g = k}
  let rep (k : S → ZMod n) : 𝕀[F] := if h : (U k).Nonempty then h.choose else 1
  refine ⟨Set.range rep, Set.finite_range rep, ?_⟩
  intro g hg hgS
  let r := rep (α g)
  have hr : r ∈ U (α g) := by
    have h : (U (α g)).Nonempty := ⟨g, hg, hgS, rfl⟩
    simpa only [r, rep, dite_eq_left h] using h.choose_spec
  let x := g / r
  have hxNorm : ideleNorm F x = 1 := by
    change ideleNorm F (g / r) = 1
    rw [map_div, hg, hr.1, div_one]
  have hxOut (w : Primes(F)) (hw : w ∉ S) : (ν w x).toAdd = 0 := by
    change (ν w (g / r)).toAdd = 0
    rw [map_div]
    change WithZero.log (Valued.v (g.val.2 w)) - WithZero.log (Valued.v (r.val.2 w)) = 0
    rw [hgS w hw, hr.2.1 w hw, sub_self]
  have hdiv (v : S) : (n : ℤ) ∣ (ν v.val x).toAdd := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    change ((ν v.val (g / r)).toAdd : ZMod n) = 0
    rw [map_div, toAdd_div, Int.cast_sub]
    exact sub_eq_zero.mpr (congrFun hr.2.2 v).symm
  choose z hz using hdiv
  choose gen hval using fun v : S ↦ exists_prime_power_generator F v.val
  have hgen (w : Primes(F)) (v : S) :
      (ν w (d (gen v))).toAdd = if w = v.val then -(n : ℤ) else 0 := by
    apply WithZero.exp_inj.mp
    rw [hν]
    change Valued.v ((gen v : F) : w.adicCompletion F) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hval]
    split_ifs <;> rfl
  let u : Fˣ := ∏ v : S, gen v ^ (-z v)
  have hu (w : Primes(F)) : (ν w (d u)).toAdd = (ν w x).toAdd := by
    change (ν w (d (∏ v : S, gen v ^ (-z v)))).toAdd = _
    simp only [map_prod, map_zpow, toAdd_prod, toAdd_zpow, hgen]
    by_cases hw : w ∈ S
    · let v : S := ⟨w, hw⟩
      rw [Finset.sum_eq_single_of_mem v (Finset.mem_univ v)]
      · simpa [v, mul_comm] using (hz v).symm
      · intro j _ hj
        simp [ite_eq_right (show w ≠ j.val from fun h ↦ hj (Subtype.ext h.symm))]
    · rw [hxOut w hw]
      exact Finset.sum_eq_zero fun v _ ↦ by simp [show w ≠ v.val from fun h ↦ hw (h ▸ v.property)]
  let y := x / d u
  have hdu : d u ∈ P := ⟨u, rfl⟩
  have hy : ideleNorm F y = 1 := by
    change ideleNorm F (x / d u) = 1
    rw [map_div, hxNorm, show ideleNorm F (d u) = 1 from (ideleNorm_spec F).2 hdu, div_one]
  refine ⟨r, ⟨_, rfl⟩, y, hy, ?_, ?_⟩
  · intro w
    rw [← hν w y]
    change WithZero.exp (ν w (x / d u)).toAdd = 1
    rw [map_div, toAdd_div, hu, sub_self, WithZero.exp_zero]
  · change q g = q r * q (g / r / d u)
    rw [map_div, map_div, show q (d u) = 1 from (QuotientGroup.eq_one_iff _).mpr hdu, div_one,
      mul_comm (q r), div_mul_cancel]

/-- Paper: Theorem A.1.5.2(1), p. 544. Norm-one S-idele classes form a closed compact
Hausdorff subgroup. Their image in the global classes is closed and lies in finitely
many translates of a compact set coming from ideles that are local units at all finite places. -/
private theorem sIdeleClassGroup_normOne_topology :
    IsClosed ((sIdeleClassNorm F S).ker : Set (SIdeleClassGroup F S)) ∧
      CompactSpace (sIdeleClassNorm F S).ker ∧ T2Space (sIdeleClassNorm F S).ker := by
  obtain ⟨j, hj, hnorm, hmk⟩ := sIdeleClassGroup_openEmbedding F S
  obtain ⟨_, _, _, _, _, hHausdorff, _, _, hcont, _⟩ := ideleGroup_quotient.{_, 0} F
  have : T2Space C[F] := hHausdorff
  have : T2Space (SIdeleClassGroup F S) := hj.isEmbedding.t2Space
  have hScont : Continuous (sIdeleClassNorm F S) := by
    simpa only [Function.comp_def, hnorm] using hcont.comp hj.continuous
  have hClosed : IsClosed ((sIdeleClassNorm F S).ker : Set (SIdeleClassGroup F S)) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hScont
  have hj' : IsClosedEmbedding j :=
    ⟨hj.isEmbedding, j.range.isClosed_of_isOpen hj.isOpen_range⟩
  refine ⟨hClosed, isCompact_iff_compactSpace.mp (hj.isEmbedding.isCompact_iff.mpr ?_), inferInstance⟩
  obtain ⟨K, hK, hKmem⟩ := exists_compact_integralIdeleClass_cover F
  obtain ⟨T, hT, hTmem⟩ := exists_finite_normOne_sIdele_representatives F S
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
  have hCover : IsCompact (⋃ r ∈ T, (fun c ↦ q r * c) '' K) :=
    hT.isCompact_biUnion fun r _ ↦ hK.image (continuous_const_mul (q r))
  refine hCover.of_isClosed_subset (hj'.isClosedMap _ hClosed) ?_
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective c
  let g := Units.map (integralAdelesOutside F S).subtype.toMonoidHom u
  have hg : ideleNorm F g = 1 := (sIdeleNorm_spec F S).1 u |>.trans hc
  have hgS (v : Primes(F)) (hv : v ∉ S) : Valued.v (g.val.2 v) = 1 := by
    let ev := (RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ w.adicCompletion F) v).comp
      (RingHom.snd (InfiniteAdeleRing F) 𝔸ᶠ[𝓞 F, F])
    have hmem (x : integralAdelesOutside F S) : x.val.2 v ∈ v.adicCompletionIntegers F := by
      have hx := x.property
      simp only [integralAdelesOutside, Subring.mem_iInf] at hx
      exact hx v hv
    exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := Units.map ev.toMonoidHom g)).mp ⟨hmem u.val, hmem u.inv⟩
  obtain ⟨r, hr, h, hh, hhFin, heq⟩ := hTmem g hg hgS
  rw [hmk, heq]
  exact Set.mem_iUnion₂.mpr ⟨r, hr, _, hKmem h hh hhFin, rfl⟩

/-- Paper: Theorem A.1.5.2, p. 544. The norm-one S-idele classes form a closed compact
Hausdorff subgroup. The S-units are finitely generated of rank the total number of places
in S minus one, and the Picard group of the S-integers is finite. -/
theorem sIdeleClassGroup_finiteness :
    IsClosed ((sIdeleClassNorm F S).ker : Set (SIdeleClassGroup F S)) ∧
    CompactSpace (sIdeleClassNorm F S).ker ∧ T2Space (sIdeleClassNorm F S).ker ∧
    Group.FG (Oₛ(F, S))ˣ ∧ Module.finrank ℤ (Additive (Oₛ(F, S))ˣ) =
      Fintype.card (InfinitePlace F) + S.card - 1 ∧ Finite (CommRing.Pic (Oₛ(F, S))) := by
  obtain ⟨hClosed, hCompact, hHausdorff⟩ := sIdeleClassGroup_normOne_topology F S
  obtain ⟨hFG, hRank⟩ := sInteger_units_finiteness F S
  exact ⟨hClosed, hCompact, hHausdorff, hFG, hRank, finite_sInteger_picard F S⟩

end SAdeles

section PicardGroups

open scoped Classical

local notation "Oₛ(" F ", " S ")" => Set.integer (S : Set (Primes(F))) F
local notation "LocalClass(" F ", " v ")" =>
  (HeightOneSpectrum.adicCompletion F v)ˣ ⧸ Submonoid.units (Submonoid.ofClass (HeightOneSpectrum.adicCompletionIntegers F v))

/-- Paper: Equation (A.1.5.9), p. 544. A T-unit determines a tuple of local multiplicative
classes at the indicated finite places, by diagonal embedding modulo the local unit groups. -/
def sUnitLocalClasses (T D : Finset (Primes(F))) :
    (T : Set (Primes(F))).unit F →* ((v : D) → LocalClass(F, v.val)) :=
  MonoidHom.pi fun v ↦ (QuotientGroup.mk' (v.val.adicCompletionIntegers F).units).comp
    ((Units.map (algebraMap F (v.val.adicCompletion F)).toMonoidHom).comp
      ((T : Set (Primes(F))).unit F).subtype)

/-- Paper: Equation (A.1.5.9), p. 544. A T-unit has trivial classes at the places of
T outside S precisely when it is already an S-unit. -/
theorem sUnitLocalClasses_eq_one (S T : Finset (Primes(F))) (h : S ⊆ T)
    (u : (T : Set (Primes(F))).unit F) :
    sUnitLocalClasses F T (T \ S) u = 1 ↔ u.val ∈ (S : Set (Primes(F))).unit F := by
  have local_eq_one (v : ↥(T \ S)) :
      sUnitLocalClasses F T (T \ S) u v = 1 ↔ v.val.valuation F (u.val : F) = 1 := by
    let x := Units.map (algebraMap F (v.val.adicCompletion F)).toMonoidHom u.val
    change (QuotientGroup.mk x : LocalClass(F, v.val)) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    refine (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := x)).trans ?_
    change Valued.v ((u.val : F) : v.val.adicCompletion F) = 1 ↔ _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  change _ ↔ ∀ v : Primes(F), v ∉ S → v.valuation F (u.val : F) = 1
  constructor
  · intro hu v hvS
    by_cases hv : v ∈ T \ S
    · let w : ↥(T \ S) := ⟨v, hv⟩
      exact (local_eq_one w).mp (congrFun hu w)
    · apply u.property v
      change v ∉ T
      rw [← Finset.sdiff_union_of_subset h, Finset.mem_union]
      exact fun hvT ↦ hvT.elim hv hvS
  · intro hu
    funext v
    exact (local_eq_one v).mpr (hu v.val (Finset.mem_sdiff.mp v.property).2)

/-- Paper: Equation (A.1.5.9), p. 544. The local contribution of a nonzero component
to an ideal class is its prime ideal class raised to its additive order. -/
def localIdealClass (v : Primes(F)) (x : (v.adicCompletion F)ˣ) : CommRing.Pic (𝓞 F) :=
  (ClassGroup.equivPic (𝓞 F) (ClassGroup.mk0
    ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩)) ^ (-WithZero.log (Valued.v x.val))

/-- Paper: Equation (A.1.5.9), p. 544. A local unit contributes the identity and a
uniformizer contributes the class of the prime to the first power. -/
theorem localIdealClass_normalization (v : Primes(F)) (x : (v.adicCompletion F)ˣ) :
    (x ∈ (v.adicCompletionIntegers F).units → localIdealClass F v x = 1) ∧
    (Valued.v x.val = WithZero.exp (-1 : ℤ) → localIdealClass F v x =
      ClassGroup.equivPic (𝓞 F) (ClassGroup.mk0
        ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩)) := by
  constructor
  · intro hx
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one] at hx
    simp [localIdealClass, hx]
  · intro hx
    simp [localIdealClass, hx]

local notation "LocalQuot(" F ", " T ", " D ")" =>
  _ ⧸ MonoidHom.range (sUnitLocalClasses F T D)

/-- The class of the divisor given by finitely many prime exponents. -/
private def divisorPic : Multiplicative (Primes(F) →₀ ℤ) →* CommRing.Pic (𝓞 F) where
  toFun n := n.toAdd.prod fun v k ↦
    ClassGroup.equivPic (𝓞 F)
      (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩) ^ k
  map_one' := Finsupp.prod_zero_index
  map_mul' _ _ := Finsupp.prod_add_index' (fun _ ↦ zpow_zero _) (fun _ _ _ ↦ zpow_add ..)

open scoped nonZeroDivisors in
/-- Prime ideal factorization represents every Picard class of the ring of integers
by a divisor. -/
private theorem divisorPic_surjective : Surjective (divisorPic F) := by
  intro y
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective ((ClassGroup.equivPic (𝓞 F)).symm y)
  let J := FractionalIdeal.mk0 F I
  have hfin : (Function.support fun v : Primes(F) ↦ FractionalIdeal.count F v J.val).Finite := by
    simpa only [Filter.eventually_cofinite, Function.support] using FractionalIdeal.finite_factors J.val
  let n := Finsupp.ofSupportFinite (fun v : Primes(F) ↦ FractionalIdeal.count F v J.val) hfin
  let prime (v : Primes(F)) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
    FractionalIdeal.mk0 F ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
  have hprod : (∏ v ∈ n.support, prime v ^ n v) = J := by
    apply Units.ext
    change (Units.coeHom _) (∏ v ∈ n.support, prime v ^ n v) = _
    rw [map_prod]
    simp only [Units.coeHom_apply, Units.val_zpow_eq_zpow_val, prime, FractionalIdeal.coe_mk0]
    have hsupport : (Function.mulSupport fun v : Primes(F) ↦
        (v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ n v) ⊆ ↑n.support := by
      intro v hv
      simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using
        (show n v ≠ 0 from fun h ↦ hv (by simp [h]))
    rw [← finprod_eq_finsetProd_of_mulSupport_subset _ hsupport]
    exact FractionalIdeal.finprod_heightOneSpectrum_factorization' F J.ne_zero
  refine ⟨Multiplicative.ofAdd n, ?_⟩
  let c := (ClassGroup.equivPic (𝓞 F)).toMonoidHom.comp (ClassGroup.mk F)
  calc
    _ = ∏ v ∈ n.support, c (prime v ^ n v) := by
      apply Finset.prod_congr rfl
      intro v _
      rw [map_zpow]
      change _ = ClassGroup.equivPic (𝓞 F) (ClassGroup.mk F (prime v)) ^ n v
      rw [ClassGroup.mk_mk0]
      rfl
    _ = c J := by rw [← map_prod, hprod]
    _ = y := by
      change ClassGroup.equivPic (𝓞 F) (ClassGroup.mk F (FractionalIdeal.mk0 F I)) = y
      rw [ClassGroup.mk_mk0, hI, MulEquiv.apply_symm_apply]

/-- The class map from divisors of the ring of integers onto the Picard group of
the S-integers is surjective. -/
private theorem sInteger_divisorPic_surjective (S : Finset (Primes(F))) :
    Surjective ((CommRing.Pic.mapAlgebra (𝓞 F) (Oₛ(F, S))).comp (divisorPic F)) :=
  (picMapAlgebra_surjective_of_isLocalization (Localization.submonoid (S : Set (Primes(F))))
    (Oₛ(F, S))).comp (divisorPic_surjective F)

open scoped nonZeroDivisors in
/-- A prime of the ring of integers is disjoint from the S-integer denominators exactly
when it lies outside S. -/
private theorem sInteger_prime_disjoint_iff (S : Finset (Primes(F))) (v : Primes(F)) :
    Disjoint (Localization.submonoid (S : Set (Primes(F))) : Set (𝓞 F)) (v.asIdeal : Set (𝓞 F)) ↔
      v ∉ S := by
  classical
  constructor
  · intro hd hv
    obtain ⟨a, ha⟩ := exists_prime_power_generator F v
    have hpos : 0 < (classNumber F : ℤ) := by
      exact_mod_cast (classNumber_ne_zero F).bot_lt
    have hlt : WithZero.exp (-(classNumber F : ℤ)) < 1 :=
      WithZero.exp_lt_one_iff.mpr (neg_lt_zero.mpr hpos)
    obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (a : F) (by
      intro w
      rw [ha]
      split_ifs
      · exact hlt.le
      · exact le_rfl)
    have hval (w : Primes(F)) :
        w.intValuation b = if w = v then WithZero.exp (-(classNumber F : ℤ)) else 1 := by
      rw [← w.valuation_of_algebraMap (K := F) b]
      change w.valuation F ((algebraMap (𝓞 F) F) b) = _
      rw [hb, ha]
    have hbV : b ∈ v.asIdeal := (v.intValuation_lt_one_iff_mem b).mp (by simpa [hval] using hlt)
    have hbM : b ∈ Localization.submonoid (S : Set (Primes(F))) := by
      rw [Localization.mem_submonoid_iff]
      refine ⟨fun w hw ↦ w.intValuation_eq_one_iff.mp ?_, mem_nonZeroDivisors_iff_ne_zero.mpr ?_⟩
      · exact (hval w).trans (ite_eq_right (show w ≠ v from fun h ↦ hw (h.symm ▸ hv)))
      · exact fun h ↦ a.ne_zero (by rw [← hb, h, map_zero])
    exact Set.disjoint_left.mp hd hbM hbV
  · intro hv
    apply Set.disjoint_left.mpr
    intro b hb
    change b ∈ Localization.submonoid (S : Set (Primes(F))) at hb
    rw [Localization.mem_submonoid_iff] at hb
    exact hb.1 v hv

open scoped nonZeroDivisors in
/-- Paper: Equation (A.1.5.9), p. 544. A divisor becomes principal over the S-integers
precisely when its exponents away from S agree with the orders of a single nonzero field
element. The exponents at the primes in S disappear under localization. -/
private theorem sInteger_divisorPic_eq_one_iff (S : Finset (Primes(F))) (n : Primes(F) →₀ ℤ) :
    CommRing.Pic.mapAlgebra (𝓞 F) (Oₛ(F, S)) (divisorPic F (Multiplicative.ofAdd n)) = 1 ↔
      ∃ a : Fˣ, ∀ v ∉ S, n v = -WithZero.log (v.valuation F (a : F)) := by
  classical
  let R := 𝓞 F
  let A := Oₛ(F, S)
  let M := Localization.submonoid (S : Set (Primes(F)))
  have hM : M ≤ R⁰ := Localization.submonoid_le_nonZeroDivisors _
  let : IsFractionRing A F := IsFractionRing.isFractionRing_of_isLocalization M A F hM
  let extend := Units.map (FractionalIdeal.extendedHom F A :
    FractionalIdeal R⁰ F →+* FractionalIdeal A⁰ F).toMonoidHom
  let prime (v : Primes(F)) : (Ideal R)⁰ :=
    ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
  let divisor (m : Primes(F) →₀ ℤ) : (FractionalIdeal R⁰ F)ˣ :=
    m.prod fun v k ↦ FractionalIdeal.mk0 F (prime v) ^ k
  let extendPrime (v : Primes(F)) (hv : v ∉ S) : HeightOneSpectrum A :=
    ⟨v.asIdeal.map (algebraMap R A), IsLocalization.isPrime_of_isPrime_disjoint M A _
      v.isPrime ((sInteger_prime_disjoint_iff F S v).mpr hv),
      (Ideal.map_eq_bot_iff_of_injective
        (FaithfulSMul.algebraMap_injective R A)).not.mpr v.ne_bot⟩
  have hunder (v : Primes(F)) (hv : v ∉ S) : (extendPrime v hv).asIdeal.under R = v.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint M A v.isPrime
      ((sInteger_prime_disjoint_iff F S v).mpr hv)
  have hprime (v : Primes(F)) :
      extend (FractionalIdeal.mk0 F (prime v)) =
        FractionalIdeal.mk0 F (ClassGroup.extendedIdeal R A (prime v)) := by
    apply Units.ext
    simp only [extend, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      FractionalIdeal.coe_mk0, FractionalIdeal.extendedHom_coeIdeal_eq_map]
  have hPic :
      CommRing.Pic.mapAlgebra R A (divisorPic F (Multiplicative.ofAdd n)) =
        ClassGroup.equivPic A (ClassGroup.mk F (extend (divisor n))) := by
    change CommRing.Pic.mapAlgebra R A (n.prod _) = _
    dsimp only [divisor, Finsupp.prod]
    simp only [map_prod]
    apply Finset.prod_congr rfl
    intro v _
    rw [map_zpow, map_zpow, map_zpow, hprime, ClassGroup.mk_mk0, map_zpow,
      picMapAlgebra_equivPic_mk0_of_isLocalization M A (prime v)
        (ClassGroup.extendedIdeal R A (prime v)) rfl]
  have hcount (m : Primes(F) →₀ ℤ) (w : HeightOneSpectrum A) (v : Primes(F))
      (hv : w.asIdeal.under R = v.asIdeal) :
      FractionalIdeal.count F w (extend (divisor m) : FractionalIdeal A⁰ F) = m v := by
    have hfactor (j : Primes(F)) :
        FractionalIdeal.count F w
          (extend (FractionalIdeal.mk0 F (prime j)) : FractionalIdeal A⁰ F) =
          if j = v then 1 else 0 := by
      rw [hprime, FractionalIdeal.coe_mk0]
      change FractionalIdeal.count F w
        ((j.asIdeal.map (algebraMap R A) : Ideal A) : FractionalIdeal A⁰ F) = _
      by_cases hjv : j = v
      · subst j
        rw [← hv, IsLocalization.map_under M A, FractionalIdeal.count_self, ite_eq_left rfl]
      rw [ite_eq_right hjv]
      by_cases hj : j ∈ S
      · have htop : j.asIdeal.map (algebraMap R A) = ⊤ := by
          by_contra hne
          exact (sInteger_prime_disjoint_iff F S j).mp
            ((IsLocalization.map_algebraMap_ne_top_iff_disjoint M A _).mp hne) hj
        rw [htop, FractionalIdeal.coeIdeal_top, FractionalIdeal.count_one]
      · have hne : extendPrime j hj ≠ w := by
          intro h
          apply hjv
          apply HeightOneSpectrum.ext
          rw [← hv, ← hunder j hj]
          exact congrArg (fun p : HeightOneSpectrum A ↦ p.asIdeal.under R) h
        exact FractionalIdeal.count_maximal_coprime F w hne
    change FractionalIdeal.count F w (Units.coeHom _ (extend (divisor m))) = _
    dsimp only [divisor, Finsupp.prod]
    simp only [map_prod]
    rw [FractionalIdeal.count_prod]
    · simp only [map_zpow, Units.coeHom_apply,
        FractionalIdeal.count_zpow, hfactor, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finsupp.mem_support_iff, ne_eq, ite_not]
      split_ifs with h
      · exact h.symm
      · rfl
    · exact fun _ _ ↦ Units.ne_zero _
  have hdivisor_eq (m : Primes(F) →₀ ℤ) :
      extend (divisor n) = extend (divisor m) ↔ ∀ v ∉ S, n v = m v := by
    constructor
    · intro h v hv
      rw [← hcount n (extendPrime v hv) v (hunder v hv),
        ← hcount m (extendPrime v hv) v (hunder v hv), h]
    · intro h
      apply Units.ext
      rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' F
        (extend (divisor n)).ne_zero, ← FractionalIdeal.finprod_heightOneSpectrum_factorization' F
          (extend (divisor m)).ne_zero]
      apply finprod_congr
      intro w
      have := w.isPrime
      obtain ⟨hp, hd⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint M A _).mp w.isPrime
      let v : Primes(F) := ⟨w.asIdeal.under R, hp,
        (IsLocalization.bot_lt_under_prime M A hM _ w.ne_bot).ne'⟩
      rw [hcount n w v rfl, hcount m w v rfl, h v ((sInteger_prime_disjoint_iff F S v).mp hd)]
  have hprincipal (a : Fˣ) : ∃ m : Primes(F) →₀ ℤ,
      (∀ v, m v = -WithZero.log (v.valuation F (a : F))) ∧
        extend (divisor m) = toPrincipalIdeal A F a := by
    let g := IdeleGroup.unitEmbedding R F a
    let m := Finsupp.ofSupportFinite (ideleExponent F g)
      (eventually_cofinite.mp (eventually_ideleExponent_eq_zero F g))
    have hm (v : Primes(F)) : m v = -WithZero.log (v.valuation F (a : F)) := by
      change -WithZero.log (Valued.v ((a : F) : v.adicCompletion F)) = _
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have hmI : divisor m = ideleFractionalIdeal F g := by
      change (∏ v ∈ m.support, FractionalIdeal.mk0 F (prime v) ^ m v) =
        ∏ᶠ v, FractionalIdeal.mk0 F (prime v) ^ m v
      rw [finprod_eq_finsetProd_of_mulSupport_subset]
      intro v hv
      exact Finsupp.mem_support_iff.mpr fun hz ↦ hv (by simp [hz])
    refine ⟨m, hm, ?_⟩
    rw [hmI, ideleFractionalIdeal_principal]
    apply Units.ext
    simp only [extend, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      coe_toPrincipalIdeal]
    rw [FractionalIdeal.extendedHom_spanSingleton (A := R)]
    have hid : IsFractionRing.map (K := F) (L := F)
        (FaithfulSMul.algebraMap_injective R A) = RingHom.id F := by
      apply IsLocalization.ringHom_ext R⁰
      ext r
      change (IsFractionRing.map (FaithfulSMul.algebraMap_injective R A))
        ((algebraMap R F) r) = (algebraMap R F) r
      rw [IsFractionRing.map, IsLocalization.map_eq]
      exact (IsScalarTower.algebraMap_apply R A F r).symm
    rw [hid, RingHom.id_apply]
  rw [hPic, ← (ClassGroup.equivPic A).map_one, (ClassGroup.equivPic A).injective.eq_iff,
    ← (ClassGroup.equiv F).injective.eq_iff, ClassGroup.equiv_mk, map_one]
  rw [FractionalIdeal.canonicalEquiv_self]
  change (QuotientGroup.mk (extend (divisor n)) :
    (FractionalIdeal A⁰ F)ˣ ⧸ (toPrincipalIdeal A F).range) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨m, hm, hmI⟩ := hprincipal a
    have h := (hdivisor_eq m).mp (ha.symm.trans hmI.symm)
    exact ⟨a, fun v hv ↦ (h v hv).trans (hm v)⟩
  · rintro ⟨a, ha⟩
    obtain ⟨m, hm, hmI⟩ := hprincipal a
    have h := (hdivisor_eq m).mpr (fun v hv ↦ (ha v hv).trans (hm v).symm)
    exact ⟨a, (h.trans hmI).symm⟩

/-- The additive order identifies the local multiplicative classes with the integers. -/
private def localClassOrder (v : Primes(F)) : LocalClass(F, v) ≃* Multiplicative ℤ := by
  let order : (v.adicCompletion F)ˣ →* Multiplicative ℤ :=
    { toFun := fun x ↦ Multiplicative.ofAdd (-WithZero.log (Valued.v x.val))
      map_one' := by change Multiplicative.ofAdd (-WithZero.log (Valued.v 1)) = 1; simp
      map_mul' := by
        intro x y
        change -WithZero.log (Valued.v (x.val * y.val)) =
          -WithZero.log (Valued.v x.val) + -WithZero.log (Valued.v y.val)
        rw [map_mul, WithZero.log_mul (by simp [x.ne_zero]) (by simp [y.ne_zero]), neg_add] }
  have hker : order.ker = (v.adicCompletionIntegers F).units := by
    ext x
    rw [MonoidHom.mem_ker, HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    change -WithZero.log (Valued.v x.val) = 0 ↔ _
    rw [neg_eq_zero, ← WithZero.exp_eq_one, WithZero.exp_log (by simp [x.ne_zero])]
  have hsurj : Surjective order := by
    intro k
    obtain ⟨x, hx⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp (-k.toAdd))
    have hx₀ : x ≠ 0 := fun h ↦ WithZero.exp_ne_zero (hx.symm.trans (by simp [h]))
    refine ⟨Units.mk0 x hx₀, ?_⟩
    change -WithZero.log (Valued.v x) = k.toAdd
    simp [hx]
  exact (QuotientGroup.congr _ _ (MulEquiv.refl _) (by rw [hker]; exact Subgroup.map_id _)).trans
    (QuotientGroup.quotientKerEquivOfSurjective order hsurj)

/-- The order of a local class represented by a completion unit is minus its valuation logarithm. -/
private theorem localClassOrder_mk (v : Primes(F)) (x : (v.adicCompletion F)ˣ) :
    (localClassOrder F v (QuotientGroup.mk x)).toAdd = -WithZero.log (Valued.v x.val) := rfl

/-- The product of local classes at D maps to divisors by extending orders by zero. -/
private def localClassDivisor (D : Finset (Primes(F))) :
    ((v : D) → LocalClass(F, v.val)) →* Multiplicative (Primes(F) →₀ ℤ) where
  toFun x := Multiplicative.ofAdd
    ((Finsupp.equivFunOnFinite.symm (fun v : D ↦ (localClassOrder F v.val (x v)).toAdd)).extendDomain)
  map_one' := by
    change (Finsupp.equivFunOnFinite.symm fun v : D ↦ (localClassOrder F v.val 1).toAdd).extendDomain = 0
    ext v
    by_cases hv : v ∈ D <;> simp [Finsupp.extendDomain_apply, hv]
  map_mul' x y := by
    change (Finsupp.equivFunOnFinite.symm fun v : D ↦
      (localClassOrder F v.val (x v * y v)).toAdd).extendDomain =
      (Finsupp.equivFunOnFinite.symm fun v : D ↦ (localClassOrder F v.val (x v)).toAdd).extendDomain +
      (Finsupp.equivFunOnFinite.symm fun v : D ↦ (localClassOrder F v.val (y v)).toAdd).extendDomain
    ext v
    by_cases hv : v ∈ D <;> simp [Finsupp.extendDomain_apply, hv]

/-- On D the extended divisor records the order of the corresponding local class. -/
private theorem localClassDivisor_apply (D : Finset (Primes(F)))
    (x : (v : D) → LocalClass(F, v.val)) (v : D) :
    (localClassDivisor F D x).toAdd v.val = (localClassOrder F v.val (x v)).toAdd := by
  simp [localClassDivisor, Finsupp.extendDomain_apply, v.property]

/-- The extended divisor vanishes outside D. -/
private theorem localClassDivisor_apply_of_notMem (D : Finset (Primes(F)))
    (x : (v : D) → LocalClass(F, v.val)) {v : Primes(F)} (hv : v ∉ D) :
    (localClassDivisor F D x).toAdd v = 0 := by
  simp [localClassDivisor, Finsupp.extendDomain_apply, hv]

/-- The local order of a diagonal unit is its valuation order in the field. -/
private theorem localClassOrder_sUnit (T D : Finset (Primes(F)))
    (a : (T : Set (Primes(F))).unit F) (v : D) :
    (localClassOrder F v.val (sUnitLocalClasses F T D a v)).toAdd =
      -WithZero.log (v.val.valuation F (a.val : F)) := by
  rw [show sUnitLocalClasses F T D a v =
    QuotientGroup.mk (Units.map (algebraMap F (v.val.adicCompletion F)).toMonoidHom a.val)
    from rfl, localClassOrder_mk]
  rw [Units.coe_map]
  change -WithZero.log (Valued.v ((a.val : F) : v.val.adicCompletion F)) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

/-- Paper: Equation (A.1.5.9), p. 544. Enlarging S to T gives a surjection of Picard
groups. Its kernel is the product of the new local multiplicative classes modulo T-units,
embedded by sending a uniformizer to the corresponding prime ideal class. -/
theorem picard_localization_exact (S T : Finset (Primes(F))) (h : S ⊆ T) :
    let D := T \ S
    let i : Oₛ(F, S) →+* Oₛ(F, T) :=
      (Subalgebra.inclusion (S := Oₛ(F, S)) (T := Oₛ(F, T))
        (fun _ hx v hv ↦ hx v (fun hvS ↦ hv (h hvS)))).toRingHom
    let p := CommRing.Pic.mapRingHom i
    ∃ j : LocalQuot(F, T, D) →* CommRing.Pic (Oₛ(F, S)),
      Injective j ∧ MulExact j p ∧ Surjective p ∧
      ∀ x : (v : D) → (v.val.adicCompletion F)ˣ,
        j (QuotientGroup.mk (fun v ↦ QuotientGroup.mk (x v))) =
          CommRing.Pic.mapAlgebra (𝓞 F) (Oₛ(F, S)) (∏ v, localIdealClass F v.val (x v)) := by
  intro D i p
  let q := (CommRing.Pic.mapAlgebra (𝓞 F) (Oₛ(F, S))).comp (divisorPic F)
  let qT := (CommRing.Pic.mapAlgebra (𝓞 F) (Oₛ(F, T))).comp (divisorPic F)
  let f := q.comp (localClassDivisor F D)
  have hp (n : Multiplicative (Primes(F) →₀ ℤ)) : p (q n) = qT n := by
    change CommRing.Pic.mapRingHom i
      (CommRing.Pic.mapAlgebra (𝓞 F) (Oₛ(F, S)) (divisorPic F n)) = _
    rw [← CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapRingHom_mapRingHom]
    exact CommRing.Pic.mapRingHom_algebraMap (R := 𝓞 F) (A := Oₛ(F, T)) ▸ rfl
  -- A principal divisor supported on D away from S comes from a T-unit.
  have hf : f.ker = (sUnitLocalClasses F T D).range := by
    ext x
    change q (localClassDivisor F D x) = 1 ↔ _
    rw [show q (localClassDivisor F D x) = 1 ↔ _ from
      sInteger_divisorPic_eq_one_iff F S (localClassDivisor F D x).toAdd]
    constructor
    · rintro ⟨a, ha⟩
      have hau : a ∈ (T : Set (Primes(F))).unit F := by
        intro v hv
        have hvT : v ∉ T := hv
        have hn := ha v (fun hvS ↦ hvT (h hvS))
        rw [localClassDivisor_apply_of_notMem F D x (fun hvD ↦ hvT (Finset.mem_sdiff.mp hvD).1),
          zero_eq_neg] at hn
        rw [← WithZero.exp_eq_one, WithZero.exp_log (by simp [a.ne_zero])] at hn
        exact hn
      refine ⟨⟨a, hau⟩, ?_⟩
      funext v
      apply (localClassOrder F v.val).injective
      apply Multiplicative.toAdd.injective
      rw [localClassOrder_sUnit, ← ha v.val (Finset.mem_sdiff.mp v.property).2,
        localClassDivisor_apply]
    · rintro ⟨a, rfl⟩
      refine ⟨a.val, fun v hvS ↦ ?_⟩
      by_cases hvT : v ∈ T
      · let w : D := ⟨v, Finset.mem_sdiff.mpr ⟨hvT, hvS⟩⟩
        rw [localClassDivisor_apply F D _ w, localClassOrder_sUnit]
      · rw [localClassDivisor_apply_of_notMem F D _ (fun hvD ↦ hvT (Finset.mem_sdiff.mp hvD).1)]
        simp [show v.valuation F (a.val : F) = 1 from a.property v hvT]
  let j := QuotientGroup.lift _ f hf.ge
  refine ⟨j, ?_, ?_, ?_, ?_⟩
  · apply (MonoidHom.ker_eq_bot_iff j).mp
    ext z
    induction z using QuotientGroup.induction_on with
    | H x =>
      change f x = 1 ↔ _
      rw [← MonoidHom.mem_ker, hf, Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  · intro y
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := sInteger_divisorPic_surjective F S y
      change q n = y at hn
      have hqT : qT n = 1 := by rwa [← hp, hn]
      obtain ⟨a, ha⟩ := (sInteger_divisorPic_eq_one_iff F T n.toAdd).mp hqT
      -- Subtract the principal divisor to leave only the new primes away from S.
      let m (v : Primes(F)) := -WithZero.log (v.valuation F (a : F))
      let x : (v : D) → LocalClass(F, v.val) :=
        fun v ↦ (localClassOrder F v.val).symm (Multiplicative.ofAdd (n.toAdd v.val - m v.val))
      let k := localClassDivisor F D x
      have hnk : q (n / k) = 1 := (sInteger_divisorPic_eq_one_iff F S (n / k).toAdd).mpr
        ⟨a, fun v hvS ↦ by
          change n.toAdd v - k.toAdd v = m v
          by_cases hvT : v ∈ T
          · let w : D := ⟨v, Finset.mem_sdiff.mpr ⟨hvT, hvS⟩⟩
            rw [localClassDivisor_apply F D x w]
            dsimp only [x]
            rw [MulEquiv.apply_symm_apply]
            exact sub_sub_cancel ..
          · rw [localClassDivisor_apply_of_notMem F D x
                (fun hvD ↦ hvT (Finset.mem_sdiff.mp hvD).1), sub_zero]
            exact ha v hvT⟩
      refine ⟨QuotientGroup.mk x, ?_⟩
      change q k = y
      rw [map_div, div_eq_one] at hnk
      exact hnk.symm.trans hn
    · rintro ⟨z, rfl⟩
      induction z using QuotientGroup.induction_on with
      | H x =>
        change p (q (localClassDivisor F D x)) = 1
        rw [hp]
        apply (sInteger_divisorPic_eq_one_iff F T _).mpr
        refine ⟨1, fun v hv ↦ ?_⟩
        change (localClassDivisor F D x).toAdd v = _
        rw [localClassDivisor_apply_of_notMem F D x (fun hvD ↦ hv (Finset.mem_sdiff.mp hvD).1)]
        simp
  · intro y
    obtain ⟨n, hn⟩ := sInteger_divisorPic_surjective F T y
    exact ⟨q n, (hp n).trans hn⟩
  · intro x
    change CommRing.Pic.mapAlgebra (𝓞 F) (Oₛ(F, S))
      (divisorPic F (localClassDivisor F D (fun v ↦ QuotientGroup.mk (x v)))) = _
    apply congrArg (CommRing.Pic.mapAlgebra (𝓞 F) (Oₛ(F, S)))
    change (Finsupp.extendDomain (Finsupp.equivFunOnFinite.symm fun v : D ↦
      (localClassOrder F v.val (QuotientGroup.mk (x v))).toAdd)).prod _ = _
    rw [Finsupp.extendDomain_eq_embDomain_subtype, Finsupp.prod_embDomain, Finsupp.prod_fintype]
    · simp [localClassOrder_mk, localIdealClass]
    · exact fun _ ↦ zpow_zero _

open scoped nonZeroDivisors in
/-- Any finitely supported collection of finite orders is realized by a norm-one idele. -/
private theorem exists_normOne_idele_with_exponents (n : Primes(F) → ℤ)
    (hn : ∀ᶠ v in cofinite, n v = 0) :
    ∃ g : (ideleNorm F).ker, ∀ v, ideleExponent F g.val v = n v := by
  choose x hx using fun v : Primes(F) ↦ v.valuedAdicCompletion_surjective F (WithZero.exp (-n v))
  have hval : ∀ᶠ v in cofinite, Valued.v (x v) = 1 := hn.mono fun v hv ↦ by simp [hx, hv]
  let a : 𝔸[F] := (1, ⟨x, hval.mono fun v hv ↦ hv.le⟩)
  have ha : IsUnit a := AdeleRing.isUnit_iff.mpr
    ⟨fun _ ↦ one_ne_zero, fun v ↦ (Valuation.ne_zero_iff Valued.v).mp (by
      change Valued.v (x v) ≠ 0
      rw [hx]
      exact WithZero.exp_ne_zero),
      hval⟩
  obtain ⟨s, _, hs, hsfin⟩ := exists_ideleNorm_section_finite_one F
  let g := ha.unit / s (ideleNorm F ha.unit)
  have hg : g ∈ (ideleNorm F).ker := by
    change ideleNorm F g = 1
    rw [map_div, hs _, div_self']
  refine ⟨⟨g, hg⟩, fun v ↦ ?_⟩
  have hfin : g.val.2 = a.2 := by
    change ha.unit.val.2 * (s (ideleNorm F ha.unit)).inv.2 = _
    have h := hsfin ((ideleNorm F ha.unit)⁻¹)
    rw [map_inv] at h
    rw [show (s (ideleNorm F ha.unit)).inv.2 = 1 from h, mul_one, IsUnit.unit_spec]
  unfold ideleExponent
  rw [hfin]
  change -WithZero.log (Valued.v (x v)) = _
  simp [hx]

open scoped WithZero in
/-- An idele is a unit in the integral adele model exactly when every finite order is zero. -/
private theorem mem_integralIdeleRange_iff (g : 𝕀[F]) :
    g ∈ (Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom).range ↔
      ∀ v : Primes(F), Valued.v (g.val.2 v) = (1 : ℤᵐ⁰) := by
  have hval (a : 𝕀[F]) (v : Primes(F)) :
      Valued.v (a.val.2 v) * Valued.v (a.inv.2 v) = (1 : ℤᵐ⁰) := by
    let f := (RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ w.adicCompletion F) v).comp
      (RingHom.snd (InfiniteAdeleRing F) 𝔸ᶠ[𝓞 F, F])
    change Valued.v (f a.val) * Valued.v (f a.inv) = 1
    rw [← map_mul, ← map_mul, a.val_inv, map_one, map_one]
  constructor
  · rintro ⟨u, rfl⟩ v
    let a := Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom u
    exact eq_one_of_one_le_mul_left ((mem_integralAdeles_iff F _).mp u.val.property v)
      ((mem_integralAdeles_iff F _).mp u.inv.property v) (hval a v).ge
  · intro hg
    have hinv (v : Primes(F)) : Valued.v (g.inv.2 v) = (1 : ℤᵐ⁰) := by
      simpa only [hg v, one_mul] using hval g v
    let u : (integralAdelesOutside F ∅)ˣ :=
      ⟨⟨g.val, (mem_integralAdeles_iff F _).mpr fun v ↦ (hg v).le⟩,
        ⟨g.inv, (mem_integralAdeles_iff F _).mpr fun v ↦ (hinv v).le⟩,
        Subtype.ext g.val_inv, Subtype.ext g.inv_val⟩
    exact ⟨u, Units.ext rfl⟩

open scoped nonZeroDivisors in
/-- Paper: Remark A.1.5.3, pp. 544–545. Taking the finite fractional ideal identifies the
norm-one ideles modulo principal ideles and integral idelic units with the Picard group. -/
private theorem picard_uniformization_ideles :
    let N := (ideleNorm F).ker
    let U := (Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom).range
    let H := (IdeleGroup.principalSubgroup (𝓞 F) F ⊔ U).comap N.subtype
    ∃ e : (N ⧸ H) ≃* CommRing.Pic (𝓞 F), ∀ g : N, e (QuotientGroup.mk g) =
      ∏ᶠ v : Primes(F), localIdealClass F v (Units.map
        ((RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ w.adicCompletion F) v).comp
          (RingHom.snd _ _)).toMonoidHom g.val) := by
  classical
  dsimp only
  let N := (ideleNorm F).ker
  let U := (Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom).range
  let P := IdeleGroup.principalSubgroup (𝓞 F) F
  let f := (ClassGroup.mk F).comp (ideleFractionalIdeal F)
  let p := f.comp N.subtype
  have hP : P ≤ f.ker := by
    rintro _ ⟨x, rfl⟩
    change ClassGroup.mk F (ideleFractionalIdeal F _) = 1
    rw [ideleFractionalIdeal_principal]
    exact ClassGroup.mk_eq_one_iff.mpr ⟨⟨x, by rw [coe_toPrincipalIdeal,
      FractionalIdeal.coeToSubmodule_spanSingleton]⟩⟩
  have hU : U ≤ f.ker := by
    intro a ha
    have ha' := (mem_integralIdeleRange_iff F a).mp ha
    have hI : ideleFractionalIdeal F a = 1 := by
      apply Units.ext
      rw [coe_ideleFractionalIdeal]
      exact finprod_eq_one_of_forall_eq_one fun v ↦ by simp [ideleExponent, ha' v]
    change ClassGroup.mk F (ideleFractionalIdeal F a) = 1
    rw [hI, map_one]
  have hker : (P ⊔ U).comap N.subtype = p.ker := by
    ext g
    change g.val ∈ P ⊔ U ↔ f g.val = 1
    refine ⟨fun hg ↦ (sup_le hP hU) hg, fun hg ↦ ?_⟩
    obtain ⟨x, hx⟩ := exists_integral_fin_idele F g.val hg
    exact Subgroup.mem_sup.mpr ⟨_, ⟨x, rfl⟩, _, (mem_integralIdeleRange_iff F _).mpr hx,
      mul_div_cancel _ _⟩
  have hsurj : Surjective p := by
    intro c
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
    let J := FractionalIdeal.mk0 F I
    obtain ⟨g, hg⟩ := exists_normOne_idele_with_exponents F
      (fun v ↦ FractionalIdeal.count F v J) (FractionalIdeal.finite_factors J.val)
    refine ⟨g, ?_⟩
    change ClassGroup.mk F (ideleFractionalIdeal F g.val) = _
    have hJ : ideleFractionalIdeal F g.val = J := by
      apply Units.ext
      rw [coe_ideleFractionalIdeal]
      simpa only [hg] using FractionalIdeal.finprod_heightOneSpectrum_factorization' F J.ne_zero
    rw [hJ, ClassGroup.mk_mk0]
  let e := (QuotientGroup.quotientMulEquivOfEq hker).trans
    ((QuotientGroup.quotientKerEquivOfSurjective p hsurj).trans (ClassGroup.equivPic (𝓞 F)))
  refine ⟨e, fun g ↦ ?_⟩
  let c := (ClassGroup.equivPic (𝓞 F)).toMonoidHom.comp (ClassGroup.mk F)
  let P' (v : Primes(F)) := FractionalIdeal.mk0 F
    ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
  have hI : ideleFractionalIdeal F g.val = ∏ᶠ v : Primes(F), P' v ^ ideleExponent F g.val v :=
    rfl
  change c (ideleFractionalIdeal F g.val) = _
  rw [hI, map_finprod]
  · apply finprod_congr
    intro v
    rw [map_zpow]
    change _ = _ ^ ideleExponent F g.val v
    rw [MonoidHom.comp_apply, ClassGroup.mk_mk0]
    rfl
  · exact eventually_cofinite.mp ((eventually_ideleExponent_eq_zero F g.val).mono
      fun v hv ↦ by simp [hv])

open scoped nonZeroDivisors in
/-- Paper: Remark A.1.5.3, p. 544. One can invert a nonzero element of an integral
representative of each ideal class by adding the primes dividing that element. -/
private theorem exists_trivial_sInteger_picard (S : Finset (Primes(F))) :
    ∃ T : Finset (Primes(F)), S ⊆ T ∧ Subsingleton (CommRing.Pic (Oₛ(F, T))) := by
  classical
  let R := 𝓞 F
  let := Fintype.ofFinite (ClassGroup R)
  choose I hI using (ClassGroup.mk0_surjective (R := R))
  have hnonzero (c : ClassGroup R) : ∃ a : R, a ∈ (I c).val ∧ a ≠ 0 :=
    Submodule.exists_mem_ne_zero_of_ne_bot (mem_nonZeroDivisors_iff_ne_zero.mp (I c).property)
  choose a ha ha₀ using hnonzero
  let support (c : ClassGroup R) :=
    (Ideal.finite_factors (I := Ideal.span {a c}) (by simp [ha₀ c])).toFinset
  let T := S ∪ Finset.univ.biUnion support
  let A := Oₛ(F, T)
  let M := Localization.submonoid (T : Set (Primes(F)))
  have hu (c : ClassGroup R) : a c ∈ M := by
    change a c ∈ Localization.submonoid (T : Set (Primes(F)))
    rw [Localization.mem_submonoid_iff]
    refine ⟨fun v hv h ↦ ?_,
      mem_nonZeroDivisors_iff_ne_zero.mpr (ha₀ c)⟩
    apply hv
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, by
      simpa [support] using (Ideal.dvd_span_singleton.mpr h : v.asIdeal ∣ Ideal.span {a c})⟩
  have hone (c : ClassGroup R) : ClassGroup.extendedHom R A c = 1 := by
    rw [← hI c, ClassGroup.extendedHom_mk0]
    apply (ClassGroup.mk0_eq_one_iff _).mpr
    have htop : (I c).val.map (algebraMap R A) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (ha c))
        (IsLocalization.map_units A (⟨a c, hu c⟩ : M))
    change ((I c).val.map (algebraMap R A)).IsPrincipal
    rw [htop]
    infer_instance
  have hsurj : Surjective (ClassGroup.extendedHom R A) := by
    intro c
    obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective c
    have hJ := IsLocalization.map_under M A J.val
    have hJ' : J.val.under R ≠ ⊥ := by
      intro hz
      rw [hz, Ideal.map_bot] at hJ
      exact (mem_nonZeroDivisors_iff_ne_zero.mp J.property) hJ.symm
    refine ⟨ClassGroup.mk0 ⟨_, mem_nonZeroDivisors_iff_ne_zero.mpr hJ'⟩, ?_⟩
    rw [ClassGroup.extendedHom_mk0]
    exact congrArg ClassGroup.mk0 (Subtype.ext hJ)
  have : Subsingleton (ClassGroup A) := ⟨fun x y ↦ by
    obtain ⟨x, rfl⟩ := hsurj x
    obtain ⟨y, rfl⟩ := hsurj y
    rw [hone, hone]⟩
  exact ⟨T, Finset.subset_union_left, (ClassGroup.equivPic A).symm.toEquiv.subsingleton⟩

/-- Paper: Remark A.1.5.3, p. 544. The injection in the localization sequence is
surjective whenever the Picard group on the right is trivial. -/
private theorem picard_uniformization_finite (S T : Finset (Primes(F))) (h : S ⊆ T)
    (hT : Subsingleton (CommRing.Pic (Oₛ(F, T)))) :
    let D := T \ S
    ∃ e : LocalQuot(F, T, D) ≃* CommRing.Pic (Oₛ(F, S)),
      ∀ x : (v : D) → (v.val.adicCompletion F)ˣ,
        e (QuotientGroup.mk (fun v ↦ QuotientGroup.mk (x v))) =
          CommRing.Pic.mapAlgebra (𝓞 F) (Oₛ(F, S)) (∏ v, localIdealClass F v.val (x v)) := by
  obtain ⟨j, hinj, hexact, _, hj⟩ := picard_localization_exact F S T h
  exact ⟨MulEquiv.ofBijective j ⟨hinj, fun y ↦ (hexact y).mp (hT.elim _ _)⟩, hj⟩

/-- Paper: Remark A.1.5.3, p. 544. Enlarging S can kill the Picard group. In that case
the local presentation is an isomorphism. For the ordinary integers the finite-place and
norm-one idelic presentations give the same ideal class by the product of local contributions. -/
theorem picard_uniformization (S : Finset (Primes(F))) :
    (∃ T : Finset (Primes(F)), S ⊆ T ∧ Subsingleton (CommRing.Pic (Oₛ(F, T)))) ∧
    (∀ T : Finset (Primes(F)), S ⊆ T → Subsingleton (CommRing.Pic (Oₛ(F, T))) →
      let D := T \ S
      ∃ e : LocalQuot(F, T, D) ≃* CommRing.Pic (Oₛ(F, S)),
        ∀ x : (v : D) → (v.val.adicCompletion F)ˣ,
          e (QuotientGroup.mk (fun v ↦ QuotientGroup.mk (x v))) =
            CommRing.Pic.mapAlgebra (𝓞 F) (Oₛ(F, S)) (∏ v, localIdealClass F v.val (x v))) ∧
    (∀ T : Finset (Primes(F)), Subsingleton (CommRing.Pic (Oₛ(F, T))) →
      ∃ e : LocalQuot(F, T, T) ≃* CommRing.Pic (𝓞 F),
        ∀ x : (v : T) → (v.val.adicCompletion F)ˣ,
          e (QuotientGroup.mk (fun v ↦ QuotientGroup.mk (x v))) =
            ∏ v, localIdealClass F v.val (x v)) ∧
    (let N := (ideleNorm F).ker
     let U := (Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom).range
     let H := (IdeleGroup.principalSubgroup (𝓞 F) F ⊔ U).comap N.subtype
     ∃ e : (N ⧸ H) ≃* CommRing.Pic (𝓞 F), ∀ g : N, e (QuotientGroup.mk g) =
       ∏ᶠ v : Primes(F), localIdealClass F v (Units.map
         ((RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ w.adicCompletion F) v).comp
           (RingHom.snd _ _)).toMonoidHom g.val)) := by
  refine ⟨exists_trivial_sInteger_picard F S, picard_uniformization_finite F S, ?_,
    picard_uniformization_ideles F⟩
  intro T hT
  have h := picard_uniformization_finite F ∅ T (Finset.empty_subset T) hT
  dsimp only at h
  rw [Finset.sdiff_empty] at h
  obtain ⟨e, he⟩ := h
  let A := Oₛ(F, (∅ : Finset (Primes(F))))
  have hA : A = ⊥ := by
    change ((↑(∅ : Finset (Primes(F))) : Set (Primes(F))).integer F) = ⊥
    rw [Finset.coe_empty, integer_empty]
  let a : A ≃ₐ[𝓞 F] 𝓞 F :=
    (Subalgebra.equivOfEq _ _ hA).trans
      (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 F) F))
  let r := a.toRingEquiv
  let q : CommRing.Pic A ≃* CommRing.Pic (𝓞 F) :=
    { CommRing.Pic.mapRingHom r.toRingHom with
      invFun := CommRing.Pic.mapRingHom r.symm.toRingHom
      left_inv := fun x ↦ by
        change CommRing.Pic.mapRingHom r.symm.toRingHom (CommRing.Pic.mapRingHom r.toRingHom x) = x
        rw [CommRing.Pic.mapRingHom_mapRingHom, r.symm_toRingHom_comp_toRingHom,
          CommRing.Pic.mapRingHom_id_apply]
      right_inv := fun x ↦ by
        change CommRing.Pic.mapRingHom r.toRingHom (CommRing.Pic.mapRingHom r.symm.toRingHom x) = x
        rw [CommRing.Pic.mapRingHom_mapRingHom, r.toRingHom_comp_symm_toRingHom,
          CommRing.Pic.mapRingHom_id_apply] }
  refine ⟨e.trans q, fun x ↦ ?_⟩
  rw [MulEquiv.trans_apply, he]
  change CommRing.Pic.mapRingHom r.toRingHom (CommRing.Pic.mapAlgebra (𝓞 F) A _) = _
  rw [← CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapRingHom_mapRingHom]
  have ha : r.toRingHom.comp (algebraMap (𝓞 F) A) = RingHom.id (𝓞 F) := by
    apply RingHom.ext
    intro z
    exact (a.commutes z).trans (Algebra.algebraMap_self_apply z)
  rw [ha, CommRing.Pic.mapRingHom_id_apply]

end PicardGroups

end RiemannMasullo
