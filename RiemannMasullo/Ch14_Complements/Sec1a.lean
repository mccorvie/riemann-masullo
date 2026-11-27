module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.RepresentationTheory.Induced
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
public import RiemannMasullo.Ch03_IdelicZeta.Sec2

/-!
# Artin–Weil L-functions

Masullo, §14.1.1, pp. 524–528. The Weil-to-Galois maps, Artin maps, and
abelianization isomorphisms are supplied as data. The absolute Galois groups use
the Krull topology. The local factors at finite places use a lift of base-field
Frobenius acting on the inertia invariants. The global product and continuation
are specified independently of a construction of the arithmetic input.
-/

@[expose] public noncomputable section

open Filter Function Set Topology
open scoped Topology WithZero

namespace RiemannMasullo
namespace ArtinWeil

/-- Paper: Equation (14.1.1.2), p. 524. The map to the topological abelianization
takes an element to its coset modulo the closed commutator subgroup. -/
def abelianize (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    G →* TopologicalAbelianization G :=
  QuotientGroup.mk' (commutator G).topologicalClosure

/-- Paper: Equation (14.1.1.2), p. 524. The topological abelianization map has
kernel equal to the closed commutator subgroup. -/
theorem abelianize_ker (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    (abelianize G).ker = (commutator G).topologicalClosure := by sorry

section WeilGroups

variable {F K W : Type*} [Field F] [Field K] [Algebra F K]
  [Group W] [TopologicalSpace W] [IsTopologicalGroup W]
  (φ : W →ₜ* (K ≃ₐ[F] K))

/-- Paper: §14.1.1, p. 524. The Weil subgroup of an intermediate field is the
inverse image of the subgroup fixing that field pointwise. -/
def subgroup (E : IntermediateField F K) : Subgroup W :=
  E.fixingSubgroup.comap φ.toMonoidHom

/-- Paper: §14.1.1, p. 524. An element belongs to the Weil subgroup of an
intermediate field precisely when its Galois image fixes that field. -/
theorem mem_subgroup_iff (E : IntermediateField F K) (w : W) :
    w ∈ subgroup φ E ↔ ∀ x : E, φ w x = x := by sorry

/-- Paper: §14.1.1, p. 524. The Weil subgroup corresponding to a finite
intermediate field is open. -/
theorem subgroup_open (E : IntermediateField F K) [FiniteDimensional F E] :
    IsOpen (subgroup φ E : Set W) := by sorry

/-- Paper: Equation (14.1.1.1), p. 524. The Weil-to-Galois map induces the
indicated bijection of left coset spaces at every finite subextension. -/
theorem coset_equiv (E : IntermediateField F K) [FiniteDimensional F E]
    (hdense : DenseRange φ) :
    ∃ e : (W ⧸ subgroup φ E) ≃ ((K ≃ₐ[F] K) ⧸ E.fixingSubgroup),
      ∀ w : W, e (QuotientGroup.mk w) = QuotientGroup.mk (φ w) := by sorry

/-- Paper: §14.1.1, p. 524. The Weil subgroup of a Galois extension is normal. -/
instance subgroupNormal (E : IntermediateField F K) [IsGalois F K] [IsGalois F E] :
    (subgroup φ E).Normal :=
  inferInstanceAs (E.fixingSubgroup.comap φ.toMonoidHom).Normal

/-- Paper: Equation (14.1.1.1), p. 524. At a finite Galois level the same map
on cosets is a multiplicative equivalence. -/
theorem coset_mulEquiv (E : IntermediateField F K) [IsGalois F K] [IsGalois F E]
    [FiniteDimensional F E] (hdense : DenseRange φ) :
    ∃ e : (W ⧸ subgroup φ E) ≃* ((K ≃ₐ[F] K) ⧸ E.fixingSubgroup),
      ∀ w : W, e (QuotientGroup.mk w) = QuotientGroup.mk (φ w) := by sorry

/-- Paper: Equation (14.1.1.2), p. 524. An abelianization isomorphism realizes
the Artin map when the images of any representative in the two abelianizations
agree. Here the class group is supplied, with local convention `Eˣ` and global
convention the idele class group. -/
def RealizesArtinMap (E : IntermediateField F K)
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    (r : C ≃ₜ* TopologicalAbelianization (subgroup φ E))
    (art : C →ₜ* TopologicalAbelianization E.fixingSubgroup) : Prop :=
  ∀ w : subgroup φ E,
    art (r.symm (abelianize (subgroup φ E) w)) =
      abelianize E.fixingSubgroup ⟨φ w, w.property⟩

/-- Paper: Equation (14.1.1.2), p. 524. For an abelianization realizing
reciprocity, a class represented by an element in the kernel of the Weil-to-Galois
map has trivial Artin image. -/
theorem RealizesArtinMap.eq_one_of_representative (E : IntermediateField F K)
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    {r : C ≃ₜ* TopologicalAbelianization (subgroup φ E)}
    {art : C →ₜ* TopologicalAbelianization E.fixingSubgroup}
    (h : RealizesArtinMap φ E r art) (w : subgroup φ E) (hw : φ w = 1) :
    art (r.symm (abelianize (subgroup φ E) w)) = 1 := by sorry

/-- Paper: Equation (14.1.1.3), p. 524. View the closure of the commutator
subgroup of the Weil subgroup of `E` inside the whole Weil group. -/
def closedCommutator (E : IntermediateField F K) : Subgroup W :=
  (commutator (subgroup φ E)).topologicalClosure.map (subgroup φ E).subtype

/-- Paper: Equation (14.1.1.3), p. 524. The closed commutator subgroup lies
in the Weil subgroup from which it is formed. -/
theorem closedCommutator_le (E : IntermediateField F K) :
    closedCommutator φ E ≤ subgroup φ E := by sorry

/-- Paper: Equation (14.1.1.3), p. 524. Closed commutators at a larger
intermediate field lie in the closed commutators at a smaller field. -/
theorem closedCommutator_antitone : Antitone (closedCommutator φ) := by sorry

/-- Paper: Equation (14.1.1.3), p. 524. At a Galois subextension the closed
commutator subgroup of the Weil subgroup is normal in the ambient Weil group. -/
instance closedCommutatorNormal (E : IntermediateField F K)
    [IsGalois F K] [IsGalois F E] : (closedCommutator φ E).Normal := by sorry

variable [IsGalois F K]

/-- Paper: Equation (14.1.1.3), p. 524. The relative Weil group is the
topological quotient by the closed commutator subgroup of the Weil subgroup. -/
def Relative (E : IntermediateField F K) [IsGalois F E] : Type _ :=
  W ⧸ closedCommutator φ E

/-- Paper: Equation (14.1.1.3), p. 524. Multiplication is induced by the Weil group. -/
instance relativeGroup (E : IntermediateField F K) [IsGalois F E] : Group (Relative φ E) :=
  inferInstanceAs (Group (W ⧸ closedCommutator φ E))

/-- Paper: Equation (14.1.1.3), p. 524. The relative group has the quotient topology. -/
instance relativeTopology (E : IntermediateField F K) [IsGalois F E] :
    TopologicalSpace (Relative φ E) :=
  inferInstanceAs (TopologicalSpace (W ⧸ closedCommutator φ E))

/-- Paper: Equation (14.1.1.3), p. 524. The group operations are continuous. -/
instance relativeIsTopologicalGroup (E : IntermediateField F K) [IsGalois F E] :
    IsTopologicalGroup (Relative φ E) :=
  inferInstanceAs (IsTopologicalGroup (W ⧸ closedCommutator φ E))

/-- Paper: Equation (14.1.1.3), p. 524. The projection to the relative Weil
group sends an element of the Weil group to its quotient class. -/
def relativeProjection (E : IntermediateField F K) [IsGalois F E] : W →ₜ* Relative φ E :=
  ⟨QuotientGroup.mk' (closedCommutator φ E), QuotientGroup.continuous_mk⟩

/-- Paper: Equation (14.1.1.3), p. 524. The relative projection identifies
exactly the cosets of the closed commutator subgroup. -/
theorem relativeProjection_eq_iff (E : IntermediateField F K) [IsGalois F E] (x y : W) :
    relativeProjection φ E x = relativeProjection φ E y ↔ x⁻¹ * y ∈ closedCommutator φ E :=
  by sorry

/-- Paper: Equation (14.1.1.4), p. 525. The subgroup used to form the
relative quotient fixes the intermediate field. -/
theorem closedCommutator_le_restrict_ker (E : IntermediateField F K) [IsGalois F E] :
    closedCommutator φ E ≤ ((AlgEquiv.restrictNormalHom E).comp φ.toMonoidHom).ker := by sorry

/-- Paper: Proposition 14.1.1.1(1), p. 525. The map from the relative Weil
group to the finite Galois group descends restriction of the Weil-to-Galois map. -/
def relativeGalois (E : IntermediateField F K) [IsGalois F E] :
    Relative φ E →* (E ≃ₐ[F] E) :=
  QuotientGroup.lift (closedCommutator φ E) ((AlgEquiv.restrictNormalHom E).comp φ.toMonoidHom)
    (closedCommutator_le_restrict_ker φ E)

/-- Paper: Equation (14.1.1.4), p. 525. On a class represented by `w` the
relative Galois map is the restriction of `φ w` to the intermediate field. -/
theorem relativeGalois_projection (E : IntermediateField F K) [IsGalois F E] (w : W) :
    relativeGalois φ E (relativeProjection φ E w) = AlgEquiv.restrictNormalHom E (φ w) :=
  by sorry

/-- Paper: Equation (14.1.1.4), p. 525. The relative projection restricted
to the Weil subgroup kills its closed commutator subgroup. -/
theorem abelianize_ker_le_relativeProjection_ker (E : IntermediateField F K)
    [IsGalois F E] :
    (commutator (subgroup φ E)).topologicalClosure ≤
      ((relativeProjection φ E).toMonoidHom.comp (subgroup φ E).subtype).ker := by sorry

/-- Paper: Equation (14.1.1.4), p. 525. Inclusion of the Weil subgroup induces
the map from its abelianization into the relative Weil group. -/
def relativeInclusion (E : IntermediateField F K) [IsGalois F E] :
    TopologicalAbelianization (subgroup φ E) →* Relative φ E :=
  QuotientGroup.lift _ ((relativeProjection φ E).toMonoidHom.comp (subgroup φ E).subtype)
    (abelianize_ker_le_relativeProjection_ker φ E)

/-- Paper: Equation (14.1.1.4), p. 525. The relative inclusion on an
abelianization class sends a representative to its relative Weil class. -/
theorem relativeInclusion_abelianize (E : IntermediateField F K) [IsGalois F E]
    (w : subgroup φ E) :
    relativeInclusion φ E (abelianize (subgroup φ E) w) = relativeProjection φ E w := by sorry

/-- Paper: Proposition 14.1.1.1(1), p. 525. The relative inclusion is a closed
embedding. Composing with `r_E` identifies its source with the class group.
Deviation: The image is a closed normal subgroup, as in erratum R18. -/
theorem relativeInclusion_closedEmbedding (E : IntermediateField F K) [IsGalois F E]
    [FiniteDimensional F E] :
    IsClosedEmbedding (relativeInclusion φ E) := by sorry

/-- Paper: Proposition 14.1.1.1(1), p. 525. The image of the relative
inclusion is the kernel of the relative Galois map.
Deviation: This is exactness of the extension in erratum R18. -/
theorem relativeInclusion_range (E : IntermediateField F K) [IsGalois F E] :
    (relativeInclusion φ E).range = (relativeGalois φ E).ker := by sorry

/-- Paper: Proposition 14.1.1.1(1), p. 525. The map to the finite discrete
Galois group is a continuous open surjection. -/
theorem relativeGalois_open_surjection (E : IntermediateField F K) [IsGalois F E]
    [FiniteDimensional F E] (hdense : DenseRange φ) :
    Continuous (relativeGalois φ E) ∧ IsOpenMap (relativeGalois φ E) ∧
      Surjective (relativeGalois φ E) := by sorry

/-- Paper: §14.1.1, archimedean groups, p. 527. At the trivial relative
level the relative group is the abelianization, hence is the class group
under the given reciprocity isomorphism.
Deviation: In particular the trivial real level gives `ℝˣ`. -/
theorem relative_bot_classGroup {C : Type*} [CommGroup C] [TopologicalSpace C]
    (r : C ≃ₜ* TopologicalAbelianization (subgroup φ (⊥ : IntermediateField F K))) :
    ∃ e : C ≃ₜ* Relative φ (⊥ : IntermediateField F K),
      ∀ x : C, e x = relativeInclusion φ (⊥ : IntermediateField F K) (r x) := by sorry

/-- Paper: Equation (14.1.1.5), p. 525. The transition from a larger to a
smaller Galois level is induced by the identity of the absolute Weil group. -/
def relativeTransition {E E' : IntermediateField F K} [IsGalois F E] [IsGalois F E']
    (h : E ≤ E') : Relative φ E' →* Relative φ E :=
  QuotientGroup.map _ _ (MonoidHom.id W) (closedCommutator_antitone φ h)

/-- Paper: Equation (14.1.1.5), p. 525. Transitions carry the class of an
absolute Weil element to the class of the same element at the lower level. -/
theorem relativeTransition_projection {E E' : IntermediateField F K}
    [IsGalois F E] [IsGalois F E'] (h : E ≤ E') (w : W) :
    relativeTransition φ h (relativeProjection φ E' w) = relativeProjection φ E w := by sorry

end WeilGroups

section Limit

variable {F K W : Type*} [Field F] [Field K] [Algebra F K] [IsGalois F K]
  [Group W] [TopologicalSpace W] [IsTopologicalGroup W]
  (φ : W →ₜ* (K ≃ₐ[F] K))

local notation "Levels" => {E : IntermediateField F K // FiniteDimensional F E ∧ IsGalois F E}

/-- Paper: Equation (14.1.1.5), p. 525. The chosen levels are Galois. -/
instance levelGalois (E : Levels) : IsGalois F E.val := E.property.2

/-- Paper: Proposition 14.1.1.1(2), p. 525. The canonical map to the product
of relative groups is a topological isomorphism onto the subspace of compatible
families, provided it is a closed embedding into the product.
Deviation: Use the cofinal finite Galois levels from (14.1.1.3). The closed
embedding hypothesis is the missing arithmetic completion input. -/
theorem relativeLimit [IsSepClosed K] (hclosed : IsClosedEmbedding
    (fun w : W ↦ fun E : Levels ↦ relativeProjection φ E.val w)) :
    ∃ e : W ≃ₜ {x : ∀ E : Levels, Relative φ E.val //
      ∀ (E E' : Levels) (h : E.val ≤ E'.val), relativeTransition φ h (x E') = x E},
      (∀ (x y : W) (E : Levels), (e (x * y)).val E = (e x).val E * (e y).val E) ∧
      ∀ (w : W) (E : Levels), (e w).val E = relativeProjection φ E.val w := by sorry

end Limit

section Representations

variable {F K W V : Type*} [Field F] [Field K] [Algebra F K] [IsGalois F K]
  [Group W] [TopologicalSpace W] [IsTopologicalGroup W]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

-- TODO: The construction of the localization in part (3) is cited to Tate.
-- The maps on the chosen separable closures and on classes must be connected
-- to the class-formation constructions.

/-- Paper: Proposition 14.1.1.1(3), p. 525. A local Weil map over the
given Galois restriction and class-group insertion respects both reciprocity
and abelianization. The absolute abelianizations use the base fields. -/
def IsWeilLocalization {Wv G Gv C Cv : Type*}
    [Group Wv] [TopologicalSpace Wv] [IsTopologicalGroup Wv]
    [Group G] [TopologicalSpace G] [Group Gv] [TopologicalSpace Gv]
    [CommGroup C] [TopologicalSpace C] [CommGroup Cv] [TopologicalSpace Cv]
    (φ : W →ₜ* G) (φv : Wv →ₜ* Gv) (restrict : Gv →ₜ* G)
    (r : C ≃ₜ* TopologicalAbelianization W) (rv : Cv ≃ₜ* TopologicalAbelianization Wv)
    (insert : Cv →ₜ* C) (θ : Wv →ₜ* W) : Prop :=
  Injective θ ∧ φ.comp θ = restrict.comp φv ∧
    ∀ w : Wv, abelianize W (θ w) = r (insert (rv.symm (abelianize Wv w)))

/-- Paper: Proposition 14.1.1.1(3), p. 525. A compatible localization
takes a local Weil element whose Galois image is trivial to a global Weil
element with trivial Galois image. -/
theorem IsWeilLocalization.map_galois_eq_one {Wv G Gv C Cv : Type*}
    [Group Wv] [TopologicalSpace Wv] [IsTopologicalGroup Wv]
    [Group G] [TopologicalSpace G] [Group Gv] [TopologicalSpace Gv]
    [CommGroup C] [TopologicalSpace C] [CommGroup Cv] [TopologicalSpace Cv]
    {φ : W →ₜ* G} {φv : Wv →ₜ* Gv} {restrict : Gv →ₜ* G}
    {r : C ≃ₜ* TopologicalAbelianization W} {rv : Cv ≃ₜ* TopologicalAbelianization Wv}
    {insert : Cv →ₜ* C} {θ : Wv →ₜ* W}
    (h : IsWeilLocalization φ φv restrict r rv insert θ) {w : Wv} (hw : φv w = 1) :
    φ (θ w) = 1 := by sorry

-- TODO(paper-gap): The proof on p. 526 needs the closed commutator of the
-- smaller Weil group inside the chosen identity neighborhood. The full
-- smaller Weil group need not lie in it, for instance for a norm character.

/-- Paper: Proposition 14.1.1.1(4), p. 525. A continuous finite-dimensional
representation descends uniquely to the relative group for some finite Galois level.
Deviation: The neighborhood condition on the relative kernels is supplied explicitly
pending a construction of the Weil group and its topology. -/
theorem representation_factors [IsSepClosed K] (φ : W →ₜ* (K ≃ₐ[F] K))
    [TopologicalSpace V] [IsModuleTopology ℂ V]
    (hsmall : ∀ U ∈ 𝓝 (1 : W), ∃ (E : IntermediateField F K)
      (_ : FiniteDimensional F E) (_ : IsGalois F E), (closedCommutator φ E : Set W) ⊆ U)
    (ρ : Representation ℂ W V) (hρ : ∀ x : V, Continuous (fun w ↦ ρ w x)) :
    ∃ (E : IntermediateField F K) (_ : FiniteDimensional F E) (_ : IsGalois F E),
      ∃! σ : Representation ℂ (Relative φ E) V,
        (∀ x : V, Continuous (fun w ↦ σ w x)) ∧
          σ.comp (relativeProjection φ E).toMonoidHom = ρ := by sorry

/-- Paper: Proposition 14.1.1.1(5)(a), p. 525. A representation has a
Galois twist if it is a continuous Galois representation pulled back along
`φ`, multiplied by a continuous quasi-character of the class group.
Deviation: This specifies the conclusion. The arithmetic assertion for
irreducible primitive representations requires the Weil-group twist theorem. -/
def IsGaloisTwist {C : Type*} [CommGroup C] [TopologicalSpace C]
    (φ : W →ₜ* (K ≃ₐ[F] K)) (r : C ≃ₜ* TopologicalAbelianization W)
    [TopologicalSpace V] (ρ : Representation ℂ W V) : Prop :=
  ∃ (σ : Representation ℂ (K ≃ₐ[F] K) V) (c : QuasiCharacter C),
    (∀ x : V, Continuous (fun g ↦ σ g x)) ∧
      ∀ w x, ρ w x = c (r.symm (abelianize W w)) • σ (φ w) x

/-- Paper: Proposition 14.1.1.1(5)(a), p. 525. A continuous Galois
representation pulled back along reciprocity has the trivial twist. -/
theorem isGaloisTwist_of_pullback {C : Type*} [CommGroup C] [TopologicalSpace C]
    (φ : W →ₜ* (K ≃ₐ[F] K)) (r : C ≃ₜ* TopologicalAbelianization W)
    [TopologicalSpace V] (σ : Representation ℂ (K ≃ₐ[F] K) V)
    (hσ : ∀ x : V, Continuous (fun g ↦ σ g x)) :
    IsGaloisTwist φ r (σ.comp φ.toMonoidHom) := by sorry

-- TODO: Deduce IsGaloisTwist for primitive irreducible Weil representations
-- from the arithmetic Weil-group hypotheses.

/-- Paper: Proposition 14.1.1.1(5)(b), p. 525. Induction of an irreducible
complex representation from a finite-index subgroup gives a semisimple representation.
Deviation: The source representation is on the subgroup, as required for induction.
The algebraic statement applies in particular to the underlying Weil representations. -/
theorem induced_semisimple (H : Subgroup W) [H.FiniteIndex]
    (ρ : Representation ℂ H V) [ρ.IsIrreducible] :
    (ρ.ind H.subtype).IsSemisimpleRepresentation := by sorry

/-- Paper: Proposition 14.1.1.1(5)(c), p. 525. Each element acts semisimply
on an induced one-dimensional representation of a finite-index subgroup.
Deviation: The inducing character is on the subgroup. -/
theorem induced_character_element_semisimple (H : Subgroup W) [H.FiniteIndex]
    (ρ : Representation ℂ H V) (hV : Module.finrank ℂ V = 1) (w : W) :
    Module.End.IsSemisimple ((ρ.ind H.subtype) w) := by sorry

end Representations

section LocalDegree

variable {L W : Type*} [Field L] [TopologicalSpace L]
  [Group W] [TopologicalSpace W] [IsTopologicalGroup W]

/-- Paper: Equation (14.1.1.7), p. 527. The local degree is the additive
valuation on the local multiplicative group, pulled back along local Weil
abelianization. A uniformizer has degree one with arithmetic reciprocity.
Deviation: This uses the base local field, as in the repair of R21. -/
def localDegree (v : Valuation L ℤᵐ⁰)
    (r : Lˣ ≃ₜ* TopologicalAbelianization W) : W →* Multiplicative ℤ :=
  invMonoidHom.comp (WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    ((Units.map v.toMonoidHom).comp (r.symm.toMonoidHom.comp (abelianize W))))

/-- Paper: Equation (14.1.1.7), p. 527. A Weil element has degree zero
precisely when the corresponding class has valuation one. -/
theorem localDegree_eq_one_iff (v : Valuation L ℤᵐ⁰)
    (r : Lˣ ≃ₜ* TopologicalAbelianization W) (w : W) :
    localDegree v r w = 1 ↔ v (r.symm (abelianize W w) : L) = 1 := by sorry

end LocalDegree

section LocalFactors

variable {G V : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

-- TODO: The upper-numbering filtration of the relative local Weil groups is
-- referred to Langlands on p. 526. The finite factor uses only its inertia term.
-- Compatibility of localDegree with passage to a relative level is still needed.

/-- Paper: §14.1.1, p. 526. If all elements of a finite-dimensional complex
representation act semisimply and the group has an abelian subgroup of finite
index, the representation is semisimple. -/
theorem semisimple_of_abelian_finiteIndex (ρ : Representation ℂ G V) (H : Subgroup G)
    [H.FiniteIndex] (hcomm : ∀ a b : H, a * b = b * a)
    (hρ : ∀ g, Module.End.IsSemisimple (ρ g)) : ρ.IsSemisimpleRepresentation := by sorry

/-- Paper: §14.1.1, p. 526. The restriction to the abelian subgroup admits a
basis of common eigenvectors.
Deviation: The character decomposition is on the abelian subgroup (R19). -/
theorem restriction_has_character_basis (ρ : Representation ℂ G V) (H : Subgroup G)
    (hcomm : ∀ a b : H, a * b = b * a) (hρ : ∀ g : H, Module.End.IsSemisimple (ρ g)) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V)
      (c : Fin (Module.finrank ℂ V) → H →* ℂˣ),
      ∀ (h : H) i, ρ h (b i) = (c i h : ℂ) • b i := by sorry

/-- Paper: §14.1.1, p. 527. Inertia invariants are the vectors fixed by the
kernel of the local Weil degree.
Deviation: Degree is supplied with the convention that base arithmetic
Frobenius has degree one. -/
def inertiaInvariants (degree : G →* Multiplicative ℤ) (ρ : Representation ℂ G V) :
    Submodule ℂ V :=
  Representation.invariants (ρ.comp degree.ker.subtype)

/-- Paper: §14.1.1, p. 527. A vector is inertia invariant precisely when
every degree-zero element fixes it. -/
theorem mem_inertiaInvariants_iff (degree : G →* Multiplicative ℤ)
    (ρ : Representation ℂ G V) (x : V) :
    x ∈ inertiaInvariants degree ρ ↔ ∀ g : G, degree g = 1 → ρ g x = x := by sorry

/-- Paper: §14.1.1, p. 527. Normality of inertia makes its fixed subspace
stable under each Weil element. -/
theorem mapsTo_inertiaInvariants (degree : G →* Multiplicative ℤ)
    (ρ : Representation ℂ G V) (g : G) :
    ∀ x ∈ inertiaInvariants degree ρ, ρ g x ∈ inertiaInvariants degree ρ := by sorry

/-- Paper: §14.1.1 before (14.1.1.7), p. 527. On pulling back to the
abelian class group, the inertia invariants have a simultaneous eigenbasis.
The resulting quasi-characters are trivial on the unit subgroup.
Deviation: The basis is indexed by the dimension of the inertia invariants (R20). -/
theorem inertiaInvariants_has_character_basis
    {C : Type*} [CommGroup C] [TopologicalSpace C]
    [TopologicalSpace G] [TopologicalSpace V] [IsModuleTopology ℂ V]
    (degree : G →* Multiplicative ℤ) (ρ : Representation ℂ G V)
    (i : C →ₜ* G) (U : Subgroup C) (hU : ∀ u ∈ U, degree (i u) = 1)
    (hρ : ∀ x : V, Continuous (fun g ↦ ρ g x))
    (hss : ∀ c : C, Module.End.IsSemisimple (ρ (i c))) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ (inertiaInvariants degree ρ))) ℂ
        (inertiaInvariants degree ρ))
      (χ : Fin (Module.finrank ℂ (inertiaInvariants degree ρ)) → QuasiCharacter C),
      (∀ c j, ρ (i c) (b j : V) = χ j c • (b j : V)) ∧
        ∀ j u, u ∈ U → χ j u = 1 := by sorry

/-- Paper: Equation (14.1.1.7), p. 527. The reciprocal Euler factor is the
characteristic determinant of a lift of base Frobenius on the inertia invariants,
evaluated at the base residue cardinality to the power `-s`.
Deviation: The determinant has size `dim V⁰` (R20). It uses the base Frobenius
and base residue cardinality (R21). -/
def finiteDenominator (degree : G →* Multiplicative ℤ)
    (ρ : Representation ℂ G V) (frob : G)
    (_hfrob : degree frob = Multiplicative.ofAdd (1 : ℤ)) (q : ℕ) (s : ℂ) : ℂ :=
  LinearMap.det (LinearMap.id -
    (q : ℂ) ^ (-s) • (ρ frob).restrict (mapsTo_inertiaInvariants degree ρ frob))

/-- Paper: Equation (14.1.1.7), p. 527. The choice of Frobenius lift does
not change the reciprocal Euler factor. -/
theorem finiteDenominator_congr_frobenius (degree : G →* Multiplicative ℤ)
    (ρ : Representation ℂ G V) (frob frob' : G)
    (h : degree frob = Multiplicative.ofAdd (1 : ℤ))
    (h' : degree frob' = Multiplicative.ofAdd (1 : ℤ)) (q : ℕ) (s : ℂ) :
    finiteDenominator degree ρ frob h q s = finiteDenominator degree ρ frob' h' q s := by sorry

/-- Paper: Equation (14.1.1.7), p. 527. The finite Euler factor is the
reciprocal of the Frobenius determinant. At a pole the value is Mathlib's
normal-form value zero. -/
def finiteFactor (degree : G →* Multiplicative ℤ)
    (ρ : Representation ℂ G V) (frob : G)
    (hfrob : degree frob = Multiplicative.ofAdd (1 : ℤ)) (q : ℕ) (s : ℂ) : ℂ :=
  (finiteDenominator degree ρ frob hfrob q s)⁻¹

/-- Paper: Equation (14.1.1.7), p. 527. In the trivial one-dimensional
representation the finite factor is the ordinary local zeta factor. -/
theorem finiteFactor_trivial (degree : G →* Multiplicative ℤ) (frob : G)
    (h : degree frob = Multiplicative.ofAdd (1 : ℤ)) (q : ℕ) (s : ℂ) :
    finiteFactor degree (Representation.trivial ℂ G ℂ) frob h q s =
      (1 - (q : ℂ) ^ (-s))⁻¹ := by sorry

/-- Paper: Equation (14.1.1.7), p. 527. With zero inertia invariants the
finite factor is the empty product, which is one. -/
theorem finiteFactor_eq_one_of_invariants_eq_bot (degree : G →* Multiplicative ℤ)
    (ρ : Representation ℂ G V) (frob : G)
    (h : degree frob = Multiplicative.ofAdd (1 : ℤ)) (q : ℕ) (s : ℂ)
    (hinv : inertiaInvariants degree ρ = ⊥) :
    finiteFactor degree ρ frob h q s = 1 := by sorry

/-- Paper: Equation (14.1.1.7), p. 527. The finite factor is holomorphic
where its denominator is nonzero.
Deviation: Holomorphy on the entire half-plane `Re s > 0` requires a size bound
on Frobenius eigenvalues. -/
theorem finiteFactor_analyticAt (degree : G →* Multiplicative ℤ)
    (ρ : Representation ℂ G V) (frob : G)
    (h : degree frob = Multiplicative.ofAdd (1 : ℤ)) (q : ℕ) (hq : 1 < q) (s : ℂ)
    (hs : finiteDenominator degree ρ frob h q s ≠ 0) :
    AnalyticAt ℂ (finiteFactor degree ρ frob h q) s := by sorry

/-- Paper: Equations (14.1.1.7) and (14.1.1.12), p. 527. At a finite place
the factor of a direct sum is the product of the factors. -/
theorem finiteFactor_prod {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    [FiniteDimensional ℂ V'] (degree : G →* Multiplicative ℤ)
    (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (frob : G)
    (h : degree frob = Multiplicative.ofAdd (1 : ℤ)) (q : ℕ) (s : ℂ) :
    finiteFactor degree (ρ.prod ρ') frob h q s =
      finiteFactor degree ρ frob h q s * finiteFactor degree ρ' frob h q s := by sorry

/-- Paper: Equation (14.1.1.9), p. 527. Pullbacks to a common local Weil group
of two realizations of the same absolute Weil representation have the same
finite factor. The degree and residue cardinality are those of the base place. -/
theorem finiteFactor_inflation {W Q Q' : Type*} [Group W] [Group Q] [Group Q']
    (θ : G →* W) (p : W →* Q) (p' : W →* Q')
    (ρ : Representation ℂ Q V) (ρ' : Representation ℂ Q' V)
    (hρ : ρ.comp p = ρ'.comp p') (degree : G →* Multiplicative ℤ) (frob : G)
    (hfrob : degree frob = Multiplicative.ofAdd (1 : ℤ)) (q : ℕ) (s : ℂ) :
    finiteFactor degree (ρ.comp (p.comp θ)) frob hfrob q s =
      finiteFactor degree (ρ'.comp (p'.comp θ)) frob hfrob q s := by sorry

/-- Paper: §14.1.1 after (14.1.1.13), p. 528. The norm twist by `a`
translates the finite Euler factor from `s` to `s+a`. In particular
this applies to a representation pulled back from the Galois group. -/
theorem finiteFactor_normTwist (degree : G →* Multiplicative ℤ)
    (ρ ρ₀ : Representation ℂ G V) (frob : G)
    (hfrob : degree frob = Multiplicative.ofAdd (1 : ℤ)) (q : ℕ) (hq : 1 < q)
    (a s : ℂ) (htwist : ∀ g x,
      ρ g x = (q : ℂ) ^ (-((Multiplicative.toAdd (degree g) : ℤ) : ℂ) * a) • ρ₀ g x) :
    finiteFactor degree ρ frob hfrob q s = finiteFactor degree ρ₀ frob hfrob q (s + a) :=
  by sorry

end LocalFactors

section NumberFieldFactors

open NumberField

variable {F W V : Type*} [Field F] [NumberField F] [Group W] [TopologicalSpace W]
  [IsTopologicalGroup W] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
  (r : (v.adicCompletion F)ˣ ≃ₜ* TopologicalAbelianization W)

local notation "degree" => localDegree Valued.v r

/-- Paper: Equations (14.1.1.7)–(14.1.1.8), p. 527. At a finite place of a
number field, evaluate the local Weil representation using the normalized
valuation and the residue cardinality of the base completion.
Deviation: Uses the base place and its residue cardinality (R21). -/
def finitePlaceFactor (ρ : Representation ℂ W V) (frob : W)
    (h : degree frob = Multiplicative.ofAdd (1 : ℤ)) (s : ℂ) : ℂ :=
  finiteFactor degree ρ frob h v.asIdeal.absNorm s

/-- Paper: Equations (14.1.1.7) and (14.1.1.11), p. 527. At a finite place
the trivial Weil representation gives the local zeta factor of the base field. -/
theorem finitePlaceFactor_trivial (frob : W)
    (h : degree frob = Multiplicative.ofAdd (1 : ℤ)) (s : ℂ) :
    finitePlaceFactor v r (Representation.trivial ℂ W ℂ) frob h s =
      (1 - (v.asIdeal.absNorm : ℂ) ^ (-s))⁻¹ := by sorry

/-- Paper: Equation (14.1.1.11), p. 528. A local Weil character obtained by
pulling back the restriction of `χ |·|^a` gives the Chapter 3 finite Hecke
factor at `s+a`. This includes the ramified case, where both factors are one.
Deviation: The agreement of characters under local reciprocity is explicit. -/
theorem finitePlaceFactor_eq_hecke
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (a : ℂ)
    (ρ : Representation ℂ W ℂ) (frob : W)
    (h : degree frob = Multiplicative.ofAdd (1 : ℤ))
    (hρ : ∀ w z, ρ w z =
      finitePlaceRestriction F v (ideleClassNormTwist χ a) (r.symm (abelianize W w)) * z)
    (s : ℂ) : finitePlaceFactor v r ρ frob h s = finiteHeckeEulerFactor χ v (s + a) :=
  by sorry

end NumberFieldFactors

-- TODO: For the archimedean passage on p. 527 the parameters of each irreducible
-- summand still need to be extracted from the relative Weil representation.

/-- Paper: §14.1.1, p. 527. A real one-dimensional summand with radial exponent
`a` and sign parity `e` contributes `Γℝ(s+a+e)`. A complex character with
normalized radial exponent `a` and angular weight `m` contributes
`Γℂ(s+a+|m|/2)`. The latter is also the factor for its irreducible induction
to the real Weil group when `m ≠ 0`.
Deviation: This gives the gamma blocks with input parameters, in the
normalization already used in Chapter 3. -/
def archimedeanBlock (parameter : (ℂ × Fin 2) ⊕ (ℂ × ℤ)) (s : ℂ) : ℂ :=
  match parameter with
  | .inl (a, e) => Complex.Gammaℝ (s + a + (e.val : ℂ))
  | .inr (a, m) => Complex.Gammaℂ (s + a + (m.natAbs : ℂ) / 2)

/-- Paper: §14.1.1, p. 527. The real trivial block has the unshifted
real gamma factor. -/
theorem archimedeanBlock_trivial_real (s : ℂ) :
    archimedeanBlock (.inl (0, 0)) s = Complex.Gammaℝ s := by sorry

section GlobalFactors

variable {ι ι' κ : Type*}

/-- Paper: Equation (14.1.1.8), p. 527. The finite factors converge
absolutely and uniformly on some right half-plane, and the resulting product,
multiplied by the archimedean factor, has value `L` there.
Deviation: The finite index is over the places of the base field (R21).
This specifies the product using its convergence data. -/
def IsEulerProduct (factors : ι → ℂ → ℂ) (arch L : ℂ → ℂ) : Prop :=
  ∃ (A : ℝ) (_ : 1 < A) (P : ℂ → ℂ),
    HasProdUniformlyOn factors P {s | A < s.re} ∧
      (∀ s : ℂ, A < s.re → Summable (fun v ↦ ‖factors v s - 1‖)) ∧
      ∀ s : ℂ, A < s.re → L s = arch s * P s

/-- Paper: Equation (14.1.1.8), p. 527. On a sufficiently far right half-plane
the completed Euler product equals the archimedean factor times the convergent
product of the finite factors. -/
theorem IsEulerProduct.eq_tprod {factors : ι → ℂ → ℂ} {arch L : ℂ → ℂ}
    (h : IsEulerProduct factors arch L) :
    ∃ A > (1 : ℝ), ∀ s : ℂ, A < s.re →
      Multipliable (fun v ↦ factors v s) ∧ L s = arch s * ∏' v, factors v s := by sorry

/-- Paper: §14.1.1 just after (14.1.1.10), p. 528. A meromorphic continuation
in normal form of the completed Euler product agrees with the product on
its half-plane of convergence. -/
def IsContinuation (factors : ι → ℂ → ℂ) (arch L : ℂ → ℂ) : Prop :=
  MeromorphicNFOn L univ ∧ IsEulerProduct factors arch L

/-- Paper: Equations (14.1.1.6)–(14.1.1.8), p. 527. At a base finite
place, take a local Weil group with its map to the global group, its degree
map, a Frobenius lift of degree one and the base residue cardinality.
Deviation: The arithmetic data of a base place are given as inputs (R21). -/
structure FinitePlaceData (W : Type*) [Group W] where
  Local : Type*
  [localGroup : Group Local]
  localization : Local →* W
  degree : Local →* Multiplicative ℤ
  frobenius : Local
  degree_frobenius : degree frobenius = Multiplicative.ofAdd (1 : ℤ)
  residueCard : ℕ
  one_lt_residueCard : 1 < residueCard

attribute [instance] FinitePlaceData.localGroup

/-- Paper: Equations (14.1.1.8)–(14.1.1.9), p. 527. For a representation and
a family of base finite places, a completed Artin–Weil L-function continues
the Euler product of its localized representations times its archimedean factor.
Deviation: The place data and the archimedean product are supplied (R21). -/
def IsWeilLFunction {W V : Type*} [Group W] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (places : ι → FinitePlaceData W)
    (ρ : Representation ℂ W V) (arch L : ℂ → ℂ) : Prop :=
  IsContinuation (fun v ↦
    let p := places v
    finiteFactor p.degree (ρ.comp p.localization) p.frobenius p.degree_frobenius p.residueCard)
    arch L

/-- Paper: Equation (14.1.1.8), p. 527. For the trivial line, the finite
part of a completed Weil L-function is the product of the base zeta factors. -/
theorem IsWeilLFunction.trivial_eulerProduct {W : Type*} [Group W]
    (places : ι → FinitePlaceData W) {arch L : ℂ → ℂ}
    (h : IsWeilLFunction places (Representation.trivial ℂ W ℂ) arch L) :
    IsEulerProduct (fun v s ↦ (1 - ((places v).residueCard : ℂ) ^ (-s))⁻¹) arch L :=
  by sorry

/-- Paper: Equation (14.1.1.9), p. 527. Realizations at two levels give the
same meromorphic continuation when their base-place factors agree.
Deviation: For the arithmetic application the localizations and factors are
supplied independently of the chosen relative level (R21). -/
theorem continuation_eq_of_factors_eq
    {factors factors' : ι → ℂ → ℂ} {arch arch' L L' : ℂ → ℂ}
    (h : IsContinuation factors arch L) (h' : IsContinuation factors' arch' L')
    (hf : factors = factors') (ha : arch = arch') : L = L' := by sorry

-- TODO: The arithmetic convergence and existence of the meromorphic
-- continuation require the local factors of the compatible Weil localizations.
-- TODO(paper-gap): A reflection equation for the products initially defined
-- on right half-planes alone does not fill the intervening strip on p. 528.
-- Tate's cited theorem supplies actual meromorphic continuation.

/-- Paper: §14.1.1 following (14.1.1.10), p. 527. The global epsilon factor
is the product of the local epsilon factors over the base places. The local
functions supplied here have finite multiplicative support. -/
def epsilonProduct (εv : κ → ℂ → ℂ) (_hfin : (mulSupport εv).Finite) (s : ℂ) : ℂ :=
  ∏ᶠ v, εv v s

/-- Paper: §14.1.1 following (14.1.1.10), p. 527. Its product is one when
every local epsilon factor is trivial. -/
theorem epsilonProduct_trivial (h : (mulSupport (1 : κ → ℂ → ℂ)).Finite) (s : ℂ) :
    epsilonProduct (1 : κ → ℂ → ℂ) h s = 1 := by sorry

-- TODO: The local epsilon factors of a Weil representation with respect to
-- the components of a single global additive character are referred to Tate
-- and Langlands. The analytic form of (14.1.1.10) uses these factors and the
-- continuation of the dual representation.

/-- Paper: Equation (14.1.1.10), p. 527. The functional equation identifies
the meromorphic function with the reflected dual times an entire nowhere-zero
epsilon factor. Equality is taken off a discrete set for meromorphic functions.
Deviation: The local epsilon factors and the dual continuation are supplied. -/
def HasFunctionalEquation (L Ldual ε : ℂ → ℂ) : Prop :=
  Differentiable ℂ ε ∧ (∀ s, ε s ≠ 0) ∧
    L =ᶠ[Filter.codiscrete ℂ] (fun s ↦ ε s * Ldual (1 - s))

/-- Paper: Equation (14.1.1.10), p. 527. If the reflected equality with the
finite epsilon product holds on a right half-plane, then it holds as an
identity of meromorphic functions. The entire nonvanishing epsilon factor is
obtained from the corresponding local properties. -/
theorem functionalEquation_of_epsilonProduct
    {L Ldual : ℂ → ℂ} (hL : MeromorphicNFOn L univ) (hdual : MeromorphicNFOn Ldual univ)
    (εv : κ → ℂ → ℂ) (hfin : (mulSupport εv).Finite)
    (hε : ∀ v, Differentiable ℂ (εv v)) (hne : ∀ v s, εv v s ≠ 0)
    (A : ℝ) (heq : ∀ s : ℂ, A < s.re →
      L s = epsilonProduct εv hfin s * Ldual (1 - s)) :
    HasFunctionalEquation L Ldual (epsilonProduct εv hfin) := by sorry

open NumberField in
/-- Paper: Equation (14.1.1.11), p. 528. If a rank-one Euler product has the
local factors of a Hecke character `χ |·|^a`, its continuation equals the
Chapter 3 completed Hecke continuation shifted by `a`.
Deviation: This states the comparison for number fields, conditional on
identification of the local factors via reciprocity. -/
theorem continuation_eq_hecke {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (a : ℂ) {H L : ℂ → ℂ}
    (hH : MeromorphicNFOn H univ)
    (hHright : ∀ s : {z : ℂ | 1 < z.re}, H s = completedHeckeL χ s)
    (hL : IsContinuation (fun v s ↦ finiteHeckeEulerFactor χ v (s + a))
      (fun s ↦ heckeGammaFactor χ (s + a)) L) :
    ∀ s : ℂ, L s = H (s + a) := by sorry

/-- Paper: Equation (14.1.1.12), p. 528. Local multiplicativity gives
multiplicativity of the completed L-functions as meromorphic functions.
Deviation: The factor of the direct sum is supplied as a product locally.
For the finite determinant this is `finiteFactor_prod`. -/
theorem continuation_prod {f₁ f₂ : ι → ℂ → ℂ} {a₁ a₂ L₁ L₂ L : ℂ → ℂ}
    (h₁ : IsContinuation f₁ a₁ L₁) (h₂ : IsContinuation f₂ a₂ L₂)
    (h : IsContinuation (fun v s ↦ f₁ v s * f₂ v s) (fun s ↦ a₁ s * a₂ s) L) :
    L =ᶠ[Filter.codiscrete ℂ] (fun s ↦ L₁ s * L₂ s) := by sorry

/-- Paper: Equation (14.1.1.13), p. 528. The product of the factors over
the places of the upper field agrees with the product of the induced factors
over the lower field if each induced factor is the product over its fiber.
Deviation: The arithmetic local induction identity and the product of the
archimedean induction identities are hypotheses. -/
theorem continuation_induction (below : ι' → ι)
    [∀ v : ι, Finite {w : ι' // below w = v}]
    {f : ι → ℂ → ℂ} {f' : ι' → ℂ → ℂ} {arch L L' : ℂ → ℂ}
    (h : IsContinuation f arch L) (h' : IsContinuation f' arch L')
    (A : ℝ) (hind : ∀ (v : ι) (s : ℂ), A < s.re →
      f v s = ∏ᶠ w : {w : ι' // below w = v}, f' w.val s) : L = L' := by sorry

/-- Paper: §14.1.1 after (14.1.1.13), p. 528. Shifting all local factors
of an Euler product by `a` shifts its continuation by `a`.
Deviation: This gives the analytic comparison once the Artin factors are
identified with the factors of the pullback from Galois. -/
theorem continuation_normTwist {f : ι → ℂ → ℂ} {arch L L' : ℂ → ℂ}
    (a : ℂ) (h : IsContinuation f arch L)
    (h' : IsContinuation (fun v s ↦ f v (s + a)) (fun s ↦ arch (s + a)) L') :
    ∀ s : ℂ, L' s = L (s + a) := by sorry

-- TODO: Identify the Artin Frobenius and inertia at a finite Galois level
-- with their images from the local Weil groups for the Galois-type comparison.

end GlobalFactors
end ArtinWeil
end RiemannMasullo
