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
  sorry

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
  sorry

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
  sorry

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

/-- Paper: Theorem A.1.4.3, p. 542. The norm-one idele classes form a compact Hausdorff
closed subgroup. The units are finitely generated of rank the number of infinite places
minus one, and the ideal class group is finite. -/
theorem ideleClassGroup_finiteness :
    IsClosed ((ideleClassNorm F).ker : Set C[F]) ∧ CompactSpace (ideleClassNorm F).ker ∧
    T2Space (ideleClassNorm F).ker ∧ Group.FG (𝓞 F)ˣ ∧
    Module.finrank ℤ (Additive (𝓞 F)ˣ) = Fintype.card (InfinitePlace F) - 1 ∧
    Finite (ClassGroup (𝓞 F)) ∧ Nonempty (ClassGroup (𝓞 F) ≃* CommRing.Pic (𝓞 F)) := by
  sorry

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
