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
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.IsOpenUnits
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- Paper: Theorem A.1.5.2, p. 544. The norm-one S-idele classes form a closed compact
Hausdorff subgroup. The S-units are finitely generated of rank the total number of places
in S minus one, and the Picard group of the S-integers is finite. -/
theorem sIdeleClassGroup_finiteness :
    IsClosed ((sIdeleClassNorm F S).ker : Set (SIdeleClassGroup F S)) ∧
    CompactSpace (sIdeleClassNorm F S).ker ∧ T2Space (sIdeleClassNorm F S).ker ∧
    Group.FG (Oₛ(F, S))ˣ ∧ Module.finrank ℤ (Additive (Oₛ(F, S))ˣ) =
      Fintype.card (InfinitePlace F) + S.card - 1 ∧ Finite (CommRing.Pic (Oₛ(F, S))) := by
  sorry

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
  sorry

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
  sorry

end PicardGroups

end RiemannMasullo
