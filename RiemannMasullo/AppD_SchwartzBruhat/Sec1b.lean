module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
public import RiemannMasullo.AppC_LCTVS.Sec2b
public import RiemannMasullo.AppA_AlgebraicNT.Sec1
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# Structure of locally compact abelian groups and their Schwartz–Bruhat spaces

Masullo, §§D.1.4–D.1.5, pp. 757–765.
-/

@[expose] public noncomputable section

open Bornology Filter MeasureTheory Set Topology TopologicalSpace
open scoped Cardinal ContDiff DirectSum Topology

namespace RiemannMasullo

section Structure

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G]

/-- Paper: Definition D.1.4.1, p. 757. A compact neighborhood of the identity
generates the whole group. -/
def IsCompactlyGeneratedGroup (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ U : Set G, U ∈ 𝓝 (1 : G) ∧ IsCompact U ∧ Subgroup.closure U = ⊤

/-- Paper: Definition D.1.4.1, p. 757. A compact group is compactly generated.
Deviation: Sanity check using the whole group as the generating neighborhood. -/
theorem isCompactlyGeneratedGroup_of_compact [CompactSpace G] :
    IsCompactlyGeneratedGroup G :=
  ⟨Set.univ, Filter.univ_mem, isCompact_univ, Subgroup.closure_univ⟩

/-- Paper: Theorem D.1.4.2, p. 757. A locally Euclidean space admits charts in
some fixed finite real dimension. -/
def IsLocallyEuclidean (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ n : ℕ, Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin n)) X)

/-- Paper: Theorem D.1.4.2, p. 757. A discrete space is locally Euclidean in
dimension zero.
Deviation: Sanity check for the locally Euclidean condition. -/
theorem isLocallyEuclidean_of_discrete (X : Type*) [TopologicalSpace X]
    [DiscreteTopology X] : IsLocallyEuclidean X :=
  ⟨0, ⟨ChartedSpace.ofDiscreteTopology⟩⟩

/-- Paper: (D.1.4.2), p. 757. A presentation identifies a group topologically
with a product of real, torus, free discrete and finite factors.
Deviation: The finite factor is enumerated by `Fin finiteOrder`. -/
structure ElementaryLCAPresentation (G : Type*) [CommGroup G] [TopologicalSpace G] where
  realDim : ℕ
  torusDim : ℕ
  latticeRank : ℕ
  finiteOrder : ℕ
  finiteGroup : AddCommGroup (Fin finiteOrder)
  equiv : letI := finiteGroup
    G ≃ₜ* Multiplicative (ElementaryLieGroup realDim torusDim latticeRank (Fin finiteOrder))

/-- Paper: (D.1.4.2), p. 757. Two elementary presentations have the same real
dimension, torus dimension and free lattice rank, and isomorphic finite factors.
Deviation: The finite factors are compared up to group isomorphism. -/
theorem ElementaryLCAPresentation.invariants (e e' : ElementaryLCAPresentation G) :
    e.realDim = e'.realDim ∧ e.torusDim = e'.torusDim ∧ e.latticeRank = e'.latticeRank ∧
      Nonempty (@AddEquiv (Fin e.finiteOrder) (Fin e'.finiteOrder)
        e.finiteGroup.toAdd e'.finiteGroup.toAdd) := by sorry

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- Paper: Theorem D.1.4.2, p. 757. A locally Euclidean LCA group is a product
of real and torus factors and a discrete abelian group. -/
theorem lca_equiv_real_torus_discrete (hG : IsLocallyEuclidean G) :
    ∃ (m n : ℕ) (D : Type u) (_ : AddCommGroup D) (_ : TopologicalSpace D)
      (_ : DiscreteTopology D),
      Nonempty (G ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin m) ×
        (Fin n → AddCircle (1 : ℝ)) × D)) := by sorry

/-- Paper: Theorem D.1.4.3(1), p. 757. An LCA group is compactly generated
exactly when its dual is locally Euclidean. -/
theorem isCompactlyGeneratedGroup_iff_dual_locallyEuclidean :
    IsCompactlyGeneratedGroup G ↔ IsLocallyEuclidean (PontryaginDual G) := by sorry

/-- Paper: Theorem D.1.4.3(1), p. 757. A closed subgroup of a compactly generated
LCA group is compactly generated. -/
theorem isCompactlyGeneratedGroup_closedSubgroup (hG : IsCompactlyGeneratedGroup G)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : IsCompactlyGeneratedGroup H := by sorry

/-- Paper: Theorem D.1.4.3(1), p. 757. The quotient of a compactly generated LCA
group by a closed subgroup is compactly generated. -/
theorem isCompactlyGeneratedGroup_quotient (hG : IsCompactlyGeneratedGroup G)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : IsCompactlyGeneratedGroup (G ⧸ H) := by sorry

/-- Paper: Theorem D.1.4.3(2), p. 757. An LCA group has an elementary presentation
exactly when it is compactly generated and locally Euclidean. -/
theorem lca_elementary_iff :
    (IsCompactlyGeneratedGroup G ∧ IsLocallyEuclidean G) ↔
      Nonempty (ElementaryLCAPresentation G) := by sorry

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Paper: (D.1.4.3), p. 758. The indexing set consists of open compactly
generated subgroups ordered by inclusion. -/
abbrev OpenCompactlyGeneratedSubgroups (G : Type*) [CommGroup G] [TopologicalSpace G] :=
  {H : Subgroup G // IsOpen (H : Set G) ∧ IsCompactlyGeneratedGroup H}

/-- Paper: (D.1.4.3), p. 758. The open compactly generated subgroups are filtered
and cover the group. The topology is final for their open inclusions. -/
theorem openCompactlyGeneratedSubgroups_colimit :
    IsDirectedOrder (OpenCompactlyGeneratedSubgroups G) ∧
      (∀ x : G, ∃ H : OpenCompactlyGeneratedSubgroups G, x ∈ H.val) ∧
      (∀ U : Set G, IsOpen U ↔
        ∀ H : OpenCompactlyGeneratedSubgroups G, IsOpen (Subtype.val ⁻¹' U : Set H.val)) := by sorry

/-- Paper: Lemma D.1.4.4, p. 758. Evaluation on the open compactly generated
subgroups of the dual identifies the group with their duals' inverse limit.
Deviation: The limit is expressed as the range in the product, with the subspace topology. -/
theorem lca_dualSubgroups_inverseLimit :
    let I := OpenCompactlyGeneratedSubgroups (PontryaginDual G)
    ∃ γ : G →ₜ* ((H : I) → PontryaginDual H.val),
      (∀ x H (χ : H.val), γ x H χ = χ.val x) ∧ IsEmbedding γ ∧
        range γ = {a | ∀ (H J : I) (h : H ≤ J) (χ : H.val),
          a H χ = a J (Subgroup.inclusion h χ)} := by sorry

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Paper: Definition D.1.4.5, p. 758. The annihilator consists of characters
whose restriction to the subgroup is trivial. -/
def lcaAnnihilator (H : Subgroup G) : Subgroup (PontryaginDual G) :=
  (PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)).toMonoidHom.ker

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Paper: Definition D.1.4.5, p. 758. The annihilator in the original group is
the intersection of the kernels of the characters in the given subgroup. -/
def lcaDualAnnihilator (J : Subgroup (PontryaginDual G)) : Subgroup G :=
  ⨅ χ : J, (show G →ₜ* Circle from χ.val).toMonoidHom.ker

/-- Paper: Definition D.1.4.5, p. 758. A character is in the annihilator exactly
when its value on every element of the subgroup is one. -/
theorem mem_lcaAnnihilator_iff (H : Subgroup G) (χ : PontryaginDual G) :
    χ ∈ lcaAnnihilator H ↔ ∀ x : H, χ x.val = 1 := by
  rw [lcaAnnihilator, MonoidHom.mem_ker]
  constructor
  · intro h x
    exact congrArg (fun ψ : PontryaginDual H ↦ ψ x) h
  · exact fun h ↦ PontryaginDual.ext h

/-- Paper: Definition D.1.4.5, p. 758. A group element is in the dual annihilator
exactly when every character of the subgroup takes value one there. -/
theorem mem_lcaDualAnnihilator_iff (J : Subgroup (PontryaginDual G)) (x : G) :
    x ∈ lcaDualAnnihilator J ↔ ∀ χ : J, χ.val x = 1 :=
  Subgroup.mem_iInf

/-- Paper: Lemma D.1.4.6(1), p. 758. Taking the annihilator twice recovers a
closed subgroup under the evaluation pairing. -/
theorem lcaDualAnnihilator_annihilator (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    lcaDualAnnihilator (lcaAnnihilator H) = H := by sorry

/-- Paper: Lemma D.1.4.6(2), p. 758. Pullback by the quotient map identifies
the dual of a quotient with the annihilator. -/
theorem lcaQuotientDual_equiv_annihilator (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ e : PontryaginDual (G ⧸ H) ≃ₜ* lcaAnnihilator H,
      ∀ (χ : PontryaginDual (G ⧸ H)) x, (e χ).val x = χ (QuotientGroup.mk x) := by sorry

/-- Paper: Lemma D.1.4.6(2), p. 758. Restriction of characters identifies the
dual modulo the annihilator with the dual of the subgroup. -/
theorem lcaDualQuotient_equiv_subgroupDual (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ e : (PontryaginDual G ⧸ lcaAnnihilator H) ≃ₜ* PontryaginDual H,
      ∀ (χ : PontryaginDual G) (x : H), e (QuotientGroup.mk χ) x = χ x.val := by sorry

/-- Paper: Lemma D.1.4.6(3), p. 758. The annihilator of a compact subgroup is open. -/
theorem isOpen_lcaAnnihilator (H : Subgroup G) (hH : IsCompact (H : Set G)) :
    IsOpen (lcaAnnihilator H : Set (PontryaginDual G)) := by sorry

/-- Paper: Lemma D.1.4.6(4), p. 758. The annihilator of an open subgroup is compact. -/
theorem isCompact_lcaAnnihilator (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    IsCompact (lcaAnnihilator H : Set (PontryaginDual G)) := by sorry

/-- Paper: (D.1.4.9)–(D.1.4.10), p. 759. The evaluation map onto the dual of
an open compactly generated subgroup of the dual is an open quotient. Its
kernel is the compact annihilator of the subgroup. -/
theorem lca_dualSubgroup_quotient (H : OpenCompactlyGeneratedSubgroups (PontryaginDual G)) :
    ∃ γ : G →ₜ* PontryaginDual H.val,
      (∀ x (χ : H.val), γ x χ = χ.val x) ∧ IsOpenQuotientMap γ ∧
        γ.toMonoidHom.ker = lcaDualAnnihilator H.val ∧ IsCompact (γ.toMonoidHom.ker : Set G) := by sorry

-- TODO(paper-gap): p. 759 calls the quotient codomains Uᵢ small subgroups of G.
-- The kernels Kᵢ are the subgroups that become small, as on p. 760.

/-- Paper: After (D.1.4.10), p. 759. Every identity neighborhood contains
one of the compact annihilators.
Deviation: The small subgroups are the kernels Kᵢ, as stated on p. 760. -/
theorem exists_lcaDualAnnihilator_subset_nhds {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ H : OpenCompactlyGeneratedSubgroups (PontryaginDual G),
      (lcaDualAnnihilator H.val : Set G) ⊆ U := by sorry

-- TODO(paper-gap): The component group of Aᵢⱼ can be infinite, as for G = ℤ with
-- Gⱼ = ℤ and Kᵢ = 1. Its component group is finitely generated by (D.1.4.12).

/-- Paper: (D.1.4.12), p. 759. A quotient in the inverse system of an open
compactly generated subgroup has an elementary presentation. -/
theorem lca_openSubgroup_quotient_elementary (J : OpenCompactlyGeneratedSubgroups G)
    (H : OpenCompactlyGeneratedSubgroups (PontryaginDual G))
    (_h : lcaDualAnnihilator H.val ≤ J.val) :
    Nonempty (ElementaryLCAPresentation (J.val ⧸ (lcaDualAnnihilator H.val).comap J.val.subtype)) := by
  sorry

/-- Paper: Lemma D.1.4.7, p. 760. Each open compactly generated subgroup is the
inverse limit of its quotients by the annihilators it contains.
Deviation: We express the compatible families as the range in the product. At comparable
indices the coordinates are compatible exactly when they have a common representative.
Together with the open exhaustion (D.1.4.3), this realizes (D.1.4.16). -/
theorem lca_openSubgroup_inverseLimit (J : OpenCompactlyGeneratedSubgroups G) :
    let I := {H : OpenCompactlyGeneratedSubgroups (PontryaginDual G) //
      lcaDualAnnihilator H.val ≤ J.val}
    let K : I → Subgroup J.val := fun H ↦ (lcaDualAnnihilator H.val.val).comap J.val.subtype
    let δ : J.val → ((H : I) → J.val ⧸ K H) := fun x _ ↦ QuotientGroup.mk x
    Nonempty I ∧ IsDirectedOrder I ∧
      IsEmbedding δ ∧ range δ = {a | ∀ (H H' : I), H ≤ H' →
      ∃ x : J.val, δ x H = a H ∧ δ x H' = a H'} := by sorry

end Structure

section StructuralPairs

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- Paper: Definition D.1.5.1(1), p. 760. A good subgroup is closed and has an
open compactly generated annihilator in the dual. -/
def IsBruhatGoodSubgroup (k : Subgroup G) : Prop :=
  IsClosed (k : Set G) ∧ IsOpen (lcaAnnihilator k : Set (PontryaginDual G)) ∧
    IsCompactlyGeneratedGroup (lcaAnnihilator k)

/-- Paper: Definition D.1.5.1(2), p. 760. A structural pair consists of an open
compactly generated subgroup and a good subgroup contained in it.
The order enlarges the first subgroup and shrinks the second. -/
abbrev BruhatStructuralPair (G : Type*) [CommGroup G] [TopologicalSpace G] :=
  {p : Subgroup G × (Subgroup G)ᵒᵈ //
    IsOpen (p.1 : Set G) ∧ IsCompactlyGeneratedGroup p.1 ∧
      IsBruhatGoodSubgroup (OrderDual.ofDual p.2) ∧ OrderDual.ofDual p.2 ≤ p.1}

/-- Paper: (D.1.5.2), p. 761. The quotient associated to a pair divides the
open subgroup by the good subgroup inside it. -/
abbrev BruhatStructuralPair.quotient (p : BruhatStructuralPair G) :=
  p.val.1 ⧸ (OrderDual.ofDual p.val.2).comap p.val.1.subtype

/-- Paper: (D.1.5.2), p. 761. The quotient sends a point to the identity if and
only if it belongs to the good subgroup. -/
theorem BruhatStructuralPair.quotient_mk_eq_one (p : BruhatStructuralPair G) (x : p.val.1) :
    (QuotientGroup.mk x : p.quotient) = 1 ↔ (x : G) ∈ OrderDual.ofDual p.val.2 := by sorry

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- Paper: Definition D.1.5.1(1), p. 760. The trivial subgroup is good exactly
when the group is locally Euclidean.
Deviation: Sanity check using the fact that its annihilator is the entire dual. -/
theorem isBruhatGoodSubgroup_bot_iff :
    IsBruhatGoodSubgroup (⊥ : Subgroup G) ↔ IsLocallyEuclidean G := by sorry

/-- Paper: Lemma D.1.5.2, p. 760. Structural pairs form a nonempty directed order. -/
theorem bruhatStructuralPair_filtered :
    Nonempty (BruhatStructuralPair G) ∧ IsDirectedOrder (BruhatStructuralPair G) := by sorry

/-- Paper: Lemma D.1.5.2(1), p. 761. The quotient attached to a structural pair
has an elementary presentation. -/
theorem BruhatStructuralPair.elementary (p : BruhatStructuralPair G) :
    Nonempty (ElementaryLCAPresentation p.quotient) := by sorry

/-- Paper: Lemma D.1.5.2(2), p. 761. The two annihilators form a structural pair
in the dual, with the annihilator of the good subgroup as the open subgroup. -/
theorem BruhatStructuralPair.dual (p : BruhatStructuralPair G) :
    ∃ q : BruhatStructuralPair (PontryaginDual G),
      q.val.1 = lcaAnnihilator (OrderDual.ofDual p.val.2) ∧
      OrderDual.ofDual q.val.2 = lcaAnnihilator p.val.1 := by sorry

section Fourier

variable [MeasurableSpace G] [BorelSpace G]

local instance : MeasurableSpace (PontryaginDual G) := borel _

variable {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]
variable {ν : Measure (PontryaginDual G)}

-- TODO(paper-gap): D.1.5.2(3) asserts pointwise converses for arbitrary integrable
-- representatives. On ℝ a function nonzero only at 0 has zero Fourier transform.

/-- Paper: Lemma D.1.5.2(3), p. 761. Invariance under a subgroup forces the Fourier
transform to vanish off the annihilator.
Deviation: Stated in the forward direction because pointwise invariance can fail
for an integrable representative of an invariant class. -/
theorem lcaFourier_support_subset_annihilator (_hν : IsLCAPlancherelMeasure μ ν)
    {f : G → ℂ} (hf : Integrable f μ) (_hfhat : Integrable (lcaFourier μ f) ν)
    (H : Subgroup G) (_hH : IsClosed (H : Set G)) (hinv : ∀ h : H, ∀ x, f (h.val * x) = f x) :
    Function.support (lcaFourier μ f) ⊆ (lcaAnnihilator H : Set (PontryaginDual G)) := by sorry

/-- Paper: Lemma D.1.5.2(3), p. 761. Support in the open subgroup and invariance
under the good subgroup give the corresponding conditions for the dual pair.
Deviation: Stated in the forward direction because pointwise support and invariance
can fail after changing a representative on a null set. -/
theorem lcaFourier_structuralPair_imp (_hν : IsLCAPlancherelMeasure μ ν)
    {f : G → ℂ} (hf : Integrable f μ) (_hfhat : Integrable (lcaFourier μ f) ν)
    (a : BruhatStructuralPair G) (hs : Function.support f ⊆ (a.val.1 : Set G))
    (hinv : ∀ h : ↥(OrderDual.ofDual a.val.2 : Subgroup G), ∀ x, f (h.val * x) = f x) :
    (∀ χ : lcaAnnihilator a.val.1, ∀ ψ : PontryaginDual G,
      lcaFourier μ f (χ.val * ψ) = lcaFourier μ f ψ) ∧
      Function.support (lcaFourier μ f) ⊆
        (lcaAnnihilator (OrderDual.ofDual a.val.2) : Set (PontryaginDual G)) := by sorry

end Fourier
end StructuralPairs

section SchwartzBruhat

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- Paper: Definition D.1.5.3(1), p. 762. A single good subgroup fixes the
function and its descent to each structural quotient with that subgroup is of class Cᵖ.
The derivatives are tested on the real and torus covers of the discrete fibers. -/
def IsBruhatContDiff (p : ℕ) (f : G → ℂ) : Prop :=
  ∃ k : Subgroup G, IsBruhatGoodSubgroup k ∧ (∀ h : k, ∀ x, f (h.val * x) = f x) ∧
    ∀ a : BruhatStructuralPair G, OrderDual.ofDual a.val.2 = k →
      ∃ f₀ : a.quotient → ℂ, (∀ x : a.val.1, f₀ (QuotientGroup.mk x) = f x.val) ∧
        ∀ (e : ElementaryLCAPresentation a.quotient)
          (z : Fin e.latticeRank → ℤ) (b : Fin e.finiteOrder),
          letI := e.finiteGroup
          ContDiff ℝ (p : ℕ∞) (fun xt ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd
            (elementaryCover xt z b))))

/-- Paper: Definition D.1.5.3(1), p. 762. A function is smooth if it is of class Cᵖ
for every finite order p. -/
def IsBruhatSmooth (f : G → ℂ) : Prop :=
  ∀ p : ℕ, IsBruhatContDiff p f

/-- Paper: Definition D.1.5.3(1), p. 762. On the real additive group, finite
orders of Bruhat differentiability agree with ordinary differentiability.
Deviation: Sanity check on the real group. -/
theorem isBruhatContDiff_real_iff (p : ℕ) (f : Multiplicative ℝ → ℂ) :
    IsBruhatContDiff p f ↔ ContDiff ℝ (p : ℕ∞) (f ∘ Multiplicative.ofAdd) := by sorry

/-- Paper: Definition D.1.5.3(1), p. 762. On the real additive group, Bruhat
smoothness agrees with ordinary smoothness.
Deviation: Sanity check on the real group. -/
theorem isBruhatSmooth_real_iff (f : Multiplicative ℝ → ℂ) :
    IsBruhatSmooth f ↔ ContDiff ℝ ∞ (f ∘ Multiplicative.ofAdd) := by sorry

variable [hTop : IsTopologicalGroup G] [hT2 : T2Space G] [hLC : LocallyCompactSpace G]

/-- Paper: Definition D.1.5.3(1), p. 762. The zero function is of class Cᵖ. -/
theorem isBruhatContDiff_zero (p : ℕ) : IsBruhatContDiff p (0 : G → ℂ) := by sorry

/-- Paper: Definition D.1.5.3(1), p. 762. The sum of two functions of class Cᵖ
is of class Cᵖ. -/
theorem IsBruhatContDiff.add {p : ℕ} {f g : G → ℂ}
    (hf : IsBruhatContDiff p f) (hg : IsBruhatContDiff p g) :
    IsBruhatContDiff p (f + g) := by sorry

/-- Paper: Definition D.1.5.3(1), p. 762. A complex scalar multiple of a function
of class Cᵖ is of class Cᵖ. -/
theorem IsBruhatContDiff.smul {p : ℕ} {f : G → ℂ}
    (hf : IsBruhatContDiff p f) (z : ℂ) : IsBruhatContDiff p (z • f) := by sorry

/-- Paper: Definition D.1.5.3(1), p. 762. The Cᵖ functions form a complex vector
subspace of the functions on G. -/
def bruhatContDiffSubmodule (p : ℕ) : Submodule ℂ (G → ℂ) where
  carrier := {f | IsBruhatContDiff p f}
  zero_mem' := isBruhatContDiff_zero p
  add_mem' hf hg := hf.add hg
  smul_mem' z _ hf := hf.smul z

/-- Paper: Definition D.1.5.3(1), p. 762. The smooth functions are the
intersection of the Cᵖ subspaces over all finite orders. -/
def bruhatSmoothSubmodule : Submodule ℂ (G → ℂ) :=
  ⨅ p : ℕ, bruhatContDiffSubmodule p

/-- Paper: Definition D.1.5.3(1), p. 762. Membership in the Cᵖ submodule is
equivalent to the stated Bruhat differentiability condition. -/
theorem mem_bruhatContDiffSubmodule_iff (p : ℕ) (f : G → ℂ) :
    f ∈ bruhatContDiffSubmodule p ↔ IsBruhatContDiff p f := by sorry

/-- Paper: Definition D.1.5.3(1), p. 762. Membership in the smooth submodule
means Bruhat differentiability at every finite order. -/
theorem mem_bruhatSmoothSubmodule_iff (f : G → ℂ) :
    f ∈ bruhatSmoothSubmodule ↔ IsBruhatSmooth f := by sorry

omit hTop hT2 hLC

/-- Paper: Definition D.1.5.3(2), p. 762. In an elementary presentation, a stage
is the existing elementary Schwartz space with its seminorm topology. -/
abbrev SchwartzBruhatStage {A : Type*} [CommGroup A] [TopologicalSpace A]
    (e : ElementaryLCAPresentation A) :=
  ElementarySchwartz e.realDim e.torusDim e.latticeRank (Fin e.finiteOrder)

open Classical in
/-- Paper: Definition D.1.5.3(2), p. 762. A stage function is pulled back along
the quotient and extended by zero outside the open subgroup.
Deviation: The printed composition is reversed and omits restriction to the open subgroup. -/
def schwartzBruhatStageRealization (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) : SchwartzBruhatStage e →ₗ[ℂ] (G → ℂ) :=
  letI := e.finiteGroup
  (LinearMap.pi fun x : G ↦
    if hx : x ∈ a.val.1 then
      LinearMap.proj (Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩)))
    else 0).comp (elementarySchwartzSubmodule e.realDim e.torusDim e.latticeRank
      (Fin e.finiteOrder)).subtype

open Classical in
/-- Paper: Definition D.1.5.3(2), p. 762. The realization evaluates a stage
function at the quotient coordinate on the open subgroup and vanishes outside it. -/
theorem schwartzBruhatStageRealization_apply (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (f : SchwartzBruhatStage e) (x : G) :
    letI := e.finiteGroup
    schwartzBruhatStageRealization a e f x =
      if hx : x ∈ a.val.1 then
        f (Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩)))
      else 0 := by sorry

include hTop hT2 hLC in
/-- Paper: Lemma D.1.5.4, p. 762. Pullback to the smaller kernel and extension by
zero to the larger open subgroup give a closed embedding of stages.
Deviation: The map is characterized by equality of the realized functions on G,
which determines the pullback and extension on the elementary quotients. -/
theorem schwartzBruhatStage_transition {a b : BruhatStructuralPair G} (h : a ≤ b)
    (e : ElementaryLCAPresentation a.quotient) (e' : ElementaryLCAPresentation b.quotient) :
    ∃ j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage e',
      (∀ f, schwartzBruhatStageRealization b e' (j f) = schwartzBruhatStageRealization a e f) ∧
        IsClosedEmbedding j := by sorry

/-- Paper: (D.1.5.4), p. 763. The underlying Schwartz–Bruhat submodule is generated
by the realizations in every structural pair and every elementary presentation. -/
def schwartzBruhatSubmodule (G : Type*) [CommGroup G] [TopologicalSpace G] :
    Submodule ℂ (G → ℂ) :=
  ⨆ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
    (schwartzBruhatStageRealization a e).range

/-- Paper: (D.1.5.4), p. 763. The stage realization takes values in the
Schwartz–Bruhat submodule and gives the canonical linear stage map. -/
def schwartzBruhatStageInclusion (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) :
    SchwartzBruhatStage e →ₗ[ℂ] schwartzBruhatSubmodule G :=
  (schwartzBruhatStageRealization a e).codRestrict (schwartzBruhatSubmodule G)
    (fun f ↦ Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem e ⟨f, rfl⟩))

/-- Paper: (D.1.5.4), p. 763. The Schwartz–Bruhat topology is generated by the
seminorms that pull back continuously to each stage.
Deviation: Using all elementary presentations avoids fixing any choice of coordinates. -/
abbrev SchwartzBruhat (G : Type*) [CommGroup G] [TopologicalSpace G] :=
  WithGeneratingSeminorms (schwartzBruhatSubmodule G)
    (Subtype.val : {p : Seminorm ℂ (schwartzBruhatSubmodule G) //
      ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
        Continuous (p ∘ schwartzBruhatStageInclusion a e)} → _)

instance : CoeFun (SchwartzBruhat G) (fun _ ↦ G → ℂ) where
  coe f := (show schwartzBruhatSubmodule G from f).val

/-- Paper: (D.1.5.4), p. 763. The stage inclusion evaluates to the function
obtained by pullback and extension by zero. -/
theorem schwartzBruhatStageInclusion_apply (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (f : SchwartzBruhatStage e) (x : G) :
    (show SchwartzBruhat G from schwartzBruhatStageInclusion a e f) x =
      schwartzBruhatStageRealization a e f x := by sorry

include hTop hT2 hLC

/-- Paper: Definition D.1.5.3(2), p. 762. A function belongs to the
Schwartz–Bruhat submodule exactly when a single structural pair and a single
elementary Schwartz function realize it. -/
theorem mem_schwartzBruhatSubmodule_iff (f : G → ℂ) :
    f ∈ schwartzBruhatSubmodule G ↔
      ∃ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
        (s : SchwartzBruhatStage e), schwartzBruhatStageRealization a e s = f := by sorry

/-- Paper: (D.1.5.4), p. 763. The topology has the final locally convex property
for the canonical linear stage maps. -/
theorem schwartzBruhat_topology_eq_final :
    (inferInstance : TopologicalSpace (SchwartzBruhat G)) =
      locallyConvexFinalTopology
        (fun i : (a : BruhatStructuralPair G) × ElementaryLCAPresentation a.quotient ↦
          (show SchwartzBruhatStage i.2 →ₗ[ℂ] SchwartzBruhat G from
            schwartzBruhatStageInclusion i.1 i.2)) := by sorry

-- TODO(paper-gap): Remark D.1.5.5 identifies global smooth functions with a
-- colimit of the smooth structural quotients. For the same extension-by-zero
-- maps, that colimit contains only functions supported in an open compactly
-- generated subgroup. The constant function 1 on discrete ℚ is smooth but
-- has no such support.

/-- Paper: Remark D.1.5.5, p. 763. Every Schwartz–Bruhat function is smooth in
the sense of Definition D.1.5.3(1). -/
theorem schwartzBruhat_isBruhatSmooth (f : SchwartzBruhat G) : IsBruhatSmooth f := by sorry

/-- Paper: Remark D.1.5.5, p. 763. A character restricts to a smooth function on
each open compactly generated subgroup. -/
theorem pontryaginDual_restriction_isBruhatSmooth (χ : PontryaginDual G)
    (J : OpenCompactlyGeneratedSubgroups G) :
    IsBruhatSmooth (fun x : J.val ↦ (χ x.val : ℂ)) := by sorry

/-- Paper: Lemma D.1.5.6(1), p. 763. The final locally convex topology is Hausdorff
when the group is second countable. -/
theorem schwartzBruhat_t2 [SecondCountableTopology G] : T2Space (SchwartzBruhat G) := by sorry

/-- Paper: Lemma D.1.5.6(1), p. 763. Each structural stage inherits its intrinsic
topology from the final locally convex topology. -/
theorem schwartzBruhatStage_isEmbedding [SecondCountableTopology G]
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
    IsEmbedding (show SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G from
      schwartzBruhatStageInclusion a e) := by sorry

/-- Paper: Lemma D.1.5.6(2), p. 763. Every bounded subset of the limit is
the image of a bounded subset of a single stage. -/
theorem schwartzBruhat_bounded_image_stage [SecondCountableTopology G]
    {B : Set (SchwartzBruhat G)} (hB : IsVonNBounded ℂ B) :
    ∃ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
      (C : Set (SchwartzBruhatStage e)), IsVonNBounded ℂ C ∧
        (show SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G from
          schwartzBruhatStageInclusion a e) '' C = B := by sorry

end SchwartzBruhat

section MainTheorems

universe v

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Paper: Theorem D.1.5.7, p. 763. The Schwartz–Bruhat space is barrelled. -/
theorem schwartzBruhat_barrelled [SecondCountableTopology G] :
    BarrelledSpace ℂ (SchwartzBruhat G) := by sorry

/-- Paper: Theorem D.1.5.7 and Remark D.1.5.8, p. 764. The Schwartz–Bruhat space
is bornological, including beyond the second-countable case.
Deviation: We use the criterion that a seminorm bounded on every bounded set is continuous. -/
theorem schwartzBruhat_bornological :
    ∀ p : Seminorm ℂ (SchwartzBruhat G),
      (∀ B : Set (SchwartzBruhat G), IsVonNBounded ℂ B → BddAbove (p '' B)) →
        Continuous p := by sorry

/-- Paper: Theorem D.1.5.7 and Remark D.1.5.8, p. 764. The Schwartz–Bruhat space
is complete for its additive uniformity, including beyond the second-countable case. -/
theorem schwartzBruhat_complete :
    CompleteSpace (SchwartzBruhat G) := by sorry

/-- Paper: Theorem D.1.5.7, p. 764. The strong dual of the Schwartz–Bruhat space
is complete. -/
theorem schwartzBruhat_strongDual_complete [SecondCountableTopology G] :
    CompleteSpace (StrongDual ℂ (SchwartzBruhat G)) := by sorry

/-- Paper: Theorem D.1.5.7, p. 764. The Schwartz–Bruhat space of a second-countable
group is nuclear. -/
theorem schwartzBruhat_nuclear [SecondCountableTopology G] :
    IsNuclearTVS.{v} (SchwartzBruhat G) := by sorry

/-- Paper: Theorem D.1.5.7, p. 764. The strong dual of the Schwartz–Bruhat space
of a second-countable group is nuclear. -/
theorem schwartzBruhat_strongDual_nuclear [SecondCountableTopology G] :
    IsNuclearTVS.{v} (StrongDual ℂ (SchwartzBruhat G)) := by sorry

/-- Paper: Theorem D.1.5.7 and Remark D.1.5.8, p. 764. Closed bounded subsets
of the Schwartz–Bruhat space are compact, including beyond the second-countable case. -/
theorem schwartzBruhat_montel :
    MontelSpace ℂ (SchwartzBruhat G) := by sorry

/-- Paper: Theorem D.1.5.7, p. 764. Closed bounded subsets of the strong dual
of the Schwartz–Bruhat space are compact. -/
theorem schwartzBruhat_strongDual_montel [SecondCountableTopology G] :
    MontelSpace ℂ (StrongDual ℂ (SchwartzBruhat G)) := by sorry

/-- Paper: Theorem D.1.5.7 and Remark D.1.5.8, p. 764. Evaluation gives a
linear homeomorphism with the strong bidual, the paper's reflexivity property
of Montel spaces, including beyond the second-countable case. -/
theorem schwartzBruhat_reflexive :
    ∃ e : SchwartzBruhat G ≃L[ℂ] StrongDual ℂ (StrongDual ℂ (SchwartzBruhat G)),
      ∀ f L, e f L = L f := by sorry

/-- Paper: Theorem D.1.5.7, p. 764. Evaluation identifies the strong dual
linearly and topologically with its own strong bidual. -/
theorem schwartzBruhat_strongDual_reflexive [SecondCountableTopology G] :
    let D := StrongDual ℂ (SchwartzBruhat G)
    letI : TopologicalSpace D := inferInstanceAs (TopologicalSpace (StrongDual ℂ (SchwartzBruhat G)))
    let DD := StrongDual ℂ D
    letI : TopologicalSpace DD := ContinuousLinearMap.topologicalSpace
    letI : TopologicalSpace (StrongDual ℂ DD) := ContinuousLinearMap.topologicalSpace
    ∃ e : D ≃L[ℂ] StrongDual ℂ DD, ∀ L M, e L M = M L := by sorry

/-- Paper: Theorem D.1.5.7, p. 764. The strong dual of the Schwartz–Bruhat space
is barrelled. -/
theorem schwartzBruhat_strongDual_barrelled [SecondCountableTopology G] :
    BarrelledSpace ℂ (StrongDual ℂ (SchwartzBruhat G)) := by sorry

/-- Paper: Remark D.1.5.8, p. 764. The Schwartz–Bruhat space of a group that
fails second countability fails nuclearity. -/
theorem schwartzBruhat_not_nuclear (hG : ¬ SecondCountableTopology G) :
    ¬ IsNuclearTVS.{v} (SchwartzBruhat G) := by sorry

/-- Paper: Proposition D.1.5.9, p. 764. Every defining countable sequence
of Fréchet stages for the Schwartz–Bruhat space is acyclic in the sense of §C.1.5.
Deviation: A defining sequence is expressed using the compatible injections and the
locally convex limit topology of `IsInjectiveLCLimit`. -/
theorem schwartzBruhat_acyclic [SecondCountableTopology G]
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)]
    [∀ n, TopologicalSpace (X n)] (hX : ∀ n, IsFrechetTVS (X n))
    {j : ∀ n, X n →L[ℂ] X (n + 1)} {i : ∀ n, X n →L[ℂ] SchwartzBruhat G}
    (h : IsInjectiveLCLimit j i) : IsAcyclicSystem j := by sorry

/-- Paper: Theorem D.1.5.10, p. 765. A cofinal increasing sequence of structural
stages gives a short topologically exact sequence. The difference map embeds
as the closed kernel of the quotient map given by summing the stage inclusions.
Deviation: Each stage is expressed in an elementary presentation and the difference
map uses the induced maps between successive presentations. -/
theorem schwartzBruhat_exists_topologicallyExact [SecondCountableTopology G] :
    ∃ (a : ℕ → BruhatStructuralPair G)
      (e : ∀ n, ElementaryLCAPresentation (a n).quotient)
      (j : ∀ n, SchwartzBruhatStage (e n) →L[ℂ] SchwartzBruhatStage (e (n + 1))),
      Monotone a ∧ (∀ b, ∃ n, b ≤ a n) ∧
      (∀ n f, schwartzBruhatStageRealization (a (n + 1)) (e (n + 1)) (j n f) =
        schwartzBruhatStageRealization (a n) (e n) f) ∧
      let X := fun n ↦ SchwartzBruhatStage (e n)
      let q := DirectSum.toModule ℂ ℕ (SchwartzBruhat G)
        (fun n ↦ (show X n →ₗ[ℂ] SchwartzBruhat G from schwartzBruhatStageInclusion (a n) (e n)))
      letI := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ X)
      IsClosedEmbedding (directSumDifference j) ∧
        LinearMap.range (directSumDifference j) = LinearMap.ker q ∧ IsQuotientMap q := by sorry

end MainTheorems

/-! ## Deferred from §C.1 -/

section DeferredFromC1

open NumberField

/-- Paper: Remark C.1.3.3, p. 660. The Schwartz–Bruhat space of the additive
adele ring of a number field is nonmetrizable. -/
theorem schwartzBruhat_adele_not_metrizable (F : Type*) [Field F] [NumberField F] :
    ¬ MetrizableSpace (SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F))) := by sorry

/-- Paper: Remark C.1.3.3, p. 660. The Schwartz–Bruhat space of a number field's
idele class group is nonmetrizable. -/
theorem schwartzBruhat_ideleClass_not_metrizable (F : Type*) [Field F] [NumberField F] :
    ¬ MetrizableSpace (SchwartzBruhat (IdeleClassGroup (𝓞 F) F)) := by sorry

variable (L : Type*) [NontriviallyNormedField L] [IsUltrametricDist L] [LocallyCompactSpace L]

/-- Paper: Remark C.1.3.3, p. 660. The Schwartz–Bruhat space of the additive
group of a nonarchimedean local field is nonmetrizable. -/
theorem schwartzBruhat_localField_not_metrizable :
    ¬ MetrizableSpace (SchwartzBruhat (Multiplicative L)) := by sorry

/-- Paper: Remark C.1.3.3, p. 660. The Schwartz–Bruhat space of a nonarchimedean
local field has countably infinite complex dimension. -/
theorem schwartzBruhat_localField_rank :
    Module.rank ℂ (SchwartzBruhat (Multiplicative L)) = ℵ₀ := by sorry

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]

/-- Paper: Example C.1.4.6(3), p. 662. The complete Schwartz–Bruhat space of a
second-countable LCA group is quasi-complete. The example's other properties
are `schwartzBruhat_complete`, `schwartzBruhat_nuclear`, `schwartzBruhat_montel`
and `schwartzBruhat_reflexive` from Theorem D.1.5.7. -/
theorem schwartzBruhat_quasiComplete :
    QuasiCompleteSpace ℂ (SchwartzBruhat G) := by sorry

end DeferredFromC1

end RiemannMasullo
