module

public import Mathlib.Data.List.TFAE
public import Mathlib.SetTheory.ZFC.VonNeumann
public import Mathlib.Topology.Category.CompactlyGenerated
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.Maps.Strict.Basic

/-!
# Appendix E.1.1. Preparations on compactly generated spaces

Paper: Notation E.0.0.1, p. 824. The categories of sets and spaces are
`CategoryTheory.types` and `TopCat`. Use the coercion to a type for the underlying set
and `ContinuousMap` (notation `C(X, Y)`) for the set of continuous maps.

Paper: Terminology E.0.0.1, p. 824. Set-functions are ordinary Lean functions. Coercion
takes a continuous map to its underlying function, and `CategoryTheory.forget TopCat`
forgets the topology. Compactness and local compactness are `CompactSpace` (with no
separation assumption) and `LocallyCompactSpace` (a basis of compact neighborhoods).

Paper: Terminology E.0.0.2, pp. 824–825. The preimage of a subspace is the subtype of the
set preimage. For immersions, submersive maps, and étale maps use `Topology.IsEmbedding`,
`Topology.IsQuotientMap`, and `IsLocalHomeomorph`, respectively. The intrinsic topology
is the original `TopologicalSpace` instance.

The introduction on pp. 825–828 previews results in §§E.1.2–E.3. Here the compact probes
are compact Hausdorff spaces in an explicit universe, independent of the carrier universe.
-/

@[expose] public section

open Set Topology TopologicalSpace

open scoped Topology

namespace RiemannMasullo

universe u v w

section Image

variable {X : Type u} {Y : Type v} [tX : TopologicalSpace X] [TopologicalSpace Y]

/-- Paper: Terminology E.0.0.2(1)–(2), pp. 824–825.
The topology of the image is the quotient topology on the range of the continuous map. -/
@[instance_reducible]
def quotientImageTopology (f : C(X, Y)) : TopologicalSpace (range f) :=
  tX.coinduced (rangeFactorization f)

/-- Paper: Terminology E.0.0.2(1), pp. 824–825.
A subset of the image is open in the quotient topology exactly when its preimage is open. -/
theorem isOpen_quotientImageTopology_iff (f : C(X, Y)) (s : Set (range f)) :
    IsOpen[quotientImageTopology f] s ↔ IsOpen (rangeFactorization f ⁻¹' s) := by
  sorry

/-- Paper: Terminology E.0.0.2(1), pp. 824–825.
A map is strict exactly when the quotient image topology agrees with the subspace topology. -/
theorem isStrictMap_iff_quotientImageTopology (f : C(X, Y)) :
    IsStrictMap f ↔ quotientImageTopology f = (inferInstance : TopologicalSpace (range f)) := by
  sorry

end Image

section CompactGeneration

variable {X : Type w} [tX : TopologicalSpace X]

/-- Paper: Definition E.1.1.1(1), p. 828.
A subset is k-closed if its preimage under every compact Hausdorff probe is closed.
Deviation: The probes have carriers in a fixed universe `u`. -/
def IsKClosed (s : Set X) : Prop :=
  ∀ (K : CompHaus.{u}) (g : C(K, X)), IsClosed (g ⁻¹' s)

/-- Paper: Definition E.1.1.1(2), p. 828.
Mathlib's compactly generated topology on the original carrier is the coarsest topology
in which every k-closed subset is closed.
Deviation: The probes have carriers in a fixed universe `u`. -/
theorem isCoarsest_compactlyGenerated :
    IsGreatest {t : TopologicalSpace X | ∀ s : Set X, IsKClosed.{u} s → IsClosed[t] s}
      (TopologicalSpace.compactlyGenerated.{u} X) := by
  sorry

/-- Paper: Remark E.1.1.2(1), p. 828.
The identity from the k-topology to the original topology is continuous.
Deviation: The k-topology uses probes in universe `u`. -/
theorem continuous_compactlyGenerated_to_original :
    Continuous[TopologicalSpace.compactlyGenerated.{u} X, tX] (id : X → X) := by
  sorry

/-- Paper: Remark E.1.1.2(2), p. 828.
The closed sets of the k-topology are exactly the k-closed sets.
Deviation: Both tests use probes in universe `u`. -/
theorem isClosed_compactlyGenerated_iff (s : Set X) :
    IsClosed[TopologicalSpace.compactlyGenerated.{u} X] s ↔ IsKClosed.{u} s := by
  sorry

/-- Paper: Lemma E.1.1.3(1), p. 828.
A function out of the space is continuous exactly when its composites with all compact
Hausdorff probes are continuous.
Deviation: Probe and target carriers lie in universes `u` and `v`, respectively. -/
def HasCompactHausdorffContinuityTest.{probe, target, carrier} (X : Type carrier)
    [TopologicalSpace X] : Prop :=
  ∀ (Y : Type target) [TopologicalSpace Y] (f : X → Y),
    Continuous f ↔ ∀ (K : CompHaus.{probe}) (g : C(K, X)), Continuous (f ∘ g)

/-- Paper: Lemma E.1.1.3(2), p. 828.
There is a small family of compact Hausdorff sources such that continuity can be tested on
all continuous maps from every member of the family.
Deviation: Source and target carriers have fixed universes. The index is small in the
common universe of the source carriers and the tested space. -/
def HasCompactHausdorffContinuityTestFamily.{probe, target, carrier} (X : Type carrier)
    [TopologicalSpace X] : Prop :=
  ∃ (I : Type (max probe carrier)) (K : I → CompHaus.{probe}),
    ∀ (Y : Type target) [TopologicalSpace Y] (f : X → Y),
      Continuous f ↔ ∀ i, ∀ g : C(K i, X), Continuous (f ∘ g)

/-- Paper: Lemma E.1.1.3(3), p. 829.
Openness in the space is equivalent to openness of preimages along all compact Hausdorff probes.
Deviation: The probes have carriers in a fixed universe `u`. -/
def HasCompactHausdorffOpennessTest (X : Type w) [TopologicalSpace X] : Prop :=
  ∀ s : Set X, IsOpen s ↔ ∀ (K : CompHaus.{u}) (g : C(K, X)), IsOpen (g ⁻¹' s)

/-- Paper: Lemma E.1.1.3(4), p. 829.
The space admits a quotient map from a coproduct of compact Hausdorff spaces.
Deviation: The summands lie in universe `u` and the index is small in the common
universe of their carriers and `X`. -/
def HasCompactHausdorffQuotientPresentation (X : Type w) [TopologicalSpace X] : Prop :=
  ∃ (I : Type (max u w)) (K : I → CompHaus.{u}) (q : (Σ i, K i) → X),
    IsQuotientMap q

/-- Paper: Lemma E.1.1.3, pp. 828–829.
The all-probe continuity test, the set of sources test, the openness test, and the
quotient presentation are equivalent.
Deviation: The probe, target, and index universes are those of the corresponding conditions. -/
theorem compactHausdorffTests_tfae (X : Type w) [TopologicalSpace X] :
    List.TFAE [HasCompactHausdorffContinuityTest.{u, v} X,
      HasCompactHausdorffContinuityTestFamily.{u, v} X,
      HasCompactHausdorffOpennessTest.{u} X,
      HasCompactHausdorffQuotientPresentation.{u} X] := by
  sorry

/-- Paper: Lemma E.1.1.4, p. 829.
A point has this property when every subset containing it is closed. -/
def AllSupersetsClosed (x : X) : Prop :=
  ∀ s : Set X, x ∈ s → IsClosed s

/-- Paper: Lemma E.1.1.4(1), p. 829.
Two distinct points all of whose supersets are closed force the space to be discrete. -/
theorem discreteTopology_of_two_allSupersetsClosed {x y : X} (hxy : x ≠ y)
    (hx : AllSupersetsClosed x) (hy : AllSupersetsClosed y) : DiscreteTopology X := by
  sorry

/-- Paper: Lemma E.1.1.4(1), p. 829.
With two distinct points all of whose supersets are closed, the continuity test holds,
and hence so do the other conditions of Lemma E.1.1.3.
Deviation: Probe and target carriers lie in universes `u` and `v`, respectively. -/
theorem compactHausdorffContinuityTest_of_two_allSupersetsClosed {x y : X} (hxy : x ≠ y)
    (hx : AllSupersetsClosed x) (hy : AllSupersetsClosed y) :
    HasCompactHausdorffContinuityTest.{u, v} X := by
  sorry

section UniquePoint

variable (x : X) (hx : ∀ y : X, AllSupersetsClosed y ↔ y = x)

include hx

/-- Paper: Lemma E.1.1.4(2a), p. 829.
The complement of the unique point all of whose supersets are closed is open. -/
theorem isOpen_compl_singleton_of_unique_allSupersetsClosed : IsOpen ({x}ᶜ : Set X) := by
  sorry

/-- Paper: Lemma E.1.1.4(2a), p. 829.
The complement of the unique point all of whose supersets are closed is discrete. -/
theorem discreteTopology_compl_singleton_of_unique_allSupersetsClosed :
    DiscreteTopology ↑({x}ᶜ : Set X) := by
  sorry

/-- Paper: Lemma E.1.1.4(2bi), equation (E.1.1.1), p. 829.
The map from the coproduct of the connected component of the distinguished point and
the closure of its complement, given by the two inclusions, is a quotient map. -/
theorem isQuotientMap_connectedComponent_sum_closure_compl :
    IsQuotientMap (Sum.elim
      (Subtype.val : connectedComponent x → X)
      (Subtype.val : closure ((connectedComponent x)ᶜ) → X)) := by
  sorry

/-- Paper: Lemma E.1.1.4(2bii), p. 829.
The image of a compact Hausdorff probe in the closure of the complement of the component
is compact. -/
theorem isCompact_range_into_closure_compl_connectedComponent (K : CompHaus.{u})
    (g : C(K, ↑(closure ((connectedComponent x)ᶜ)))) : IsCompact (range g) := by
  sorry

/-- Paper: Lemma E.1.1.4(2bii), p. 829.
The image of a compact Hausdorff probe in the closure of the complement of the component
is Hausdorff with its subspace topology. -/
theorem t2Space_range_into_closure_compl_connectedComponent (K : CompHaus.{u})
    (g : C(K, ↑(closure ((connectedComponent x)ᶜ)))) : T2Space ↑(range g) := by
  sorry

/-- Paper: Lemma E.1.1.4(2bii), p. 829.
The image of a compact Hausdorff probe in the closure of the complement of the component
is closed in that closure. -/
theorem isClosed_range_into_closure_compl_connectedComponent (K : CompHaus.{u})
    (g : C(K, ↑(closure ((connectedComponent x)ᶜ)))) : IsClosed (range g) := by
  sorry

/-- Paper: Lemma E.1.1.4(2bii), p. 829.
The map from a compact Hausdorff probe to its range in the closure of the complement
of the component is a quotient map for the subspace topology. -/
theorem isQuotientMap_rangeFactorization_into_closure_compl_connectedComponent
    (K : CompHaus.{u}) (g : C(K, ↑(closure ((connectedComponent x)ᶜ)))) :
    IsQuotientMap (rangeFactorization g) := by
  sorry

-- TODO(paper-gap): On p. 830 the circle coproduct has no marked point when the
-- connected component is a singleton. A singleton probe covers this case.

/-- Paper: Lemma E.1.1.4(2biii), pp. 829–830.
The connected component of the distinguished point is a quotient of a compact Hausdorff space.
Deviation: The witness can be taken in the carrier universe of the original space. -/
theorem exists_compactHausdorff_quotient_connectedComponent :
    ∃ (K : CompHaus.{w}) (g : K → connectedComponent x), IsQuotientMap g := by
  sorry

/-- Paper: Lemma E.1.1.4(2c), pp. 829–830.
For a space with the distinguished point, the continuity test implies the test by a set of sources.
Deviation: Probe and target carriers lie in universes `u` and `v`, respectively. -/
theorem compactHausdorffContinuityTestFamily_of_unique_allSupersetsClosed :
    HasCompactHausdorffContinuityTest.{u, v} X →
      HasCompactHausdorffContinuityTestFamily.{u, v} X := by
  sorry

end UniquePoint

/-- Paper: Remark E.1.1.5, p. 830.
The closed point of the Sierpiński trait is its unique point with all supersets closed. -/
theorem allSupersetsClosed_sierpinski_iff (p : Prop) :
    AllSupersetsClosed p ↔ p = False := by
  sorry

/-- Paper: Remark E.1.1.5, p. 830.
The bouquet glues the closed points of Sierpiński traits at `none`. Each `some i` is
the open point of the trait indexed by `i`.
Deviation: The empty bouquet retains its marked point. -/
@[instance_reducible]
def traitBouquetTopology (I : Type u) : TopologicalSpace (Option I) :=
  generateFrom (range fun i : I ↦ ({some i} : Set (Option I)))

/-- Paper: Remark E.1.1.5, p. 830.
The open sets of the bouquet are the subsets of its open points and the whole space. -/
theorem isOpen_traitBouquetTopology_iff {I : Type u} (s : Set (Option I)) :
    IsOpen[traitBouquetTopology I] s ↔ none ∉ s ∨ s = univ := by
  sorry

/-- Paper: Remark E.1.1.5, p. 830.
The connected component is homeomorphic to the bouquet indexed by its other points,
with the distinguished point sent to the basepoint and all other points sent to their labels.
Deviation: The bouquet of the empty family is the one-point space. -/
theorem exists_homeomorph_connectedComponent_traitBouquet (x : X)
    (hx : ∀ y : X, AllSupersetsClosed y ↔ y = x) :
    let I := {z : connectedComponent x // (z : X) ≠ x}
    let t := traitBouquetTopology I
    ∃ e : connectedComponent x ≃ₜ WithTopology (Option I) t,
      e ⟨x, mem_connectedComponent⟩ = WithTopology.toTopology t none ∧
        ∀ i : I, e i.val = WithTopology.toTopology t (some i) := by
  sorry

end CompactGeneration

-- TODO(paper-gap): On p. 831 the witnessing ordinals form an unbounded class. The
-- minimum exists by minimizing below a witnessing stage. For (2) retain all maps
-- over each source. The discrete case on p. 830 includes the empty space.

/-- Paper: Lemma E.1.1.3, equations (E.1.1.2)–(E.1.1.3), p. 831.
Each nonempty class has a least witnessing stage. The supremum of those stages meets
each class, providing a common bound for collecting witnesses.
Deviation: The rank argument is stated for predicates on `ZFSet` and a universe-small
index type. The least stage is specified by its order property. -/
theorem exists_least_vonNeumannStages {I : Type u} (C : I → ZFSet.{u} → Prop)
    (hC : ∀ i, ∃ z, C i z) :
    ∃ (a : I → Ordinal.{u}) (b : Ordinal.{u}),
      (∀ i, IsLeast {o | ∃ z ∈ ZFSet.vonNeumann o, C i z} (a i)) ∧
        IsLUB (range a) b ∧ (∀ i, ∃ z ∈ ZFSet.vonNeumann b, C i z) := by
  sorry

/-- Paper: Lemma E.1.1.3, equation (E.1.1.4), p. 831.
The coproduct map restricts on each summand to the corresponding probe. -/
def compactHausdorffCoproductMap {I : Type v} {K : I → CompHaus.{u}}
    {X : Type w} [TopologicalSpace X] (g : ∀ i, C(K i, X)) (p : Σ i, K i) : X :=
  g p.1 p.2

/-- Paper: Lemma E.1.1.3, equation (E.1.1.5), p. 831.
The preimage under the coproduct map is the disjoint union of the preimages under the summand maps. -/
theorem compactHausdorffCoproductMap_preimage {I : Type v} {K : I → CompHaus.{u}}
    {X : Type w} [TopologicalSpace X] (g : ∀ i, C(K i, X)) (s : Set X) :
    compactHausdorffCoproductMap g ⁻¹' s = univ.sigma (fun i ↦ g i ⁻¹' s) := by
  sorry

/-- Paper: Remark E.1.1.6, p. 832.
Scott's rank bound allows a set of witnesses to meet every member of a small indexed family
of nonempty classes. The set consists of the elements of the common stage lying in some class.
Deviation: The witnesses are abstract `ZFSet` elements. The collected set can be empty
when the family is empty. This states the set-existence conclusion of the rank argument. -/
theorem exists_zfSet_meeting_classes {I : Type u} (C : I → ZFSet.{u} → Prop)
    (hC : ∀ i, ∃ z, C i z) :
    ∃ (b : Ordinal.{u}) (S : ZFSet.{u}),
      (∀ z, z ∈ S ↔ z ∈ ZFSet.vonNeumann b ∧ ∃ i, C i z) ∧
        ∀ i, ∃ z ∈ S, C i z := by
  sorry

/-- Paper: Definition E.1.1.7(1), p. 832.
Mathlib's compact generation predicate agrees with the equivalent conditions of Lemma E.1.1.3.
Deviation: The predicate uses probes in universe `u`; the test uses targets in universe `v`. -/
theorem uCompactlyGeneratedSpace_iff_continuityTest (X : Type w) [TopologicalSpace X] :
    UCompactlyGeneratedSpace.{u} X ↔ HasCompactHausdorffContinuityTest.{u, v} X := by
  sorry

/-- Paper: Definition E.1.1.7(2), p. 832.
Mathlib's category `CompactlyGenerated` has the compactly generated spaces as objects and
continuous maps as morphisms. Its forgetful functor to topological spaces is fully faithful.
Deviation: Objects have carriers in universe `w` and are tested by probes in universe `u`. -/
theorem compactlyGeneratedToTop_full_faithful :
    (CompactlyGenerated.compactlyGeneratedToTop.{u, w}).Full ∧
      (CompactlyGenerated.compactlyGeneratedToTop.{u, w}).Faithful := by
  sorry

/-- Paper: Remark E.1.1.8, p. 832.
A space is compactly generated exactly when its original topology equals its k-topology.
Deviation: Both sides use the same fixed probe universe `u`. -/
theorem uCompactlyGeneratedSpace_iff_eq_compactlyGenerated
    (X : Type w) [tX : TopologicalSpace X] :
    UCompactlyGeneratedSpace.{u} X ↔ TopologicalSpace.compactlyGenerated.{u} X = tX := by
  sorry

/-- Paper: Example E.1.1.9, p. 832.
The cocountable topology is generated by the empty set and complements of countable sets. -/
@[instance_reducible]
def cocountableTopology (X : Type w) : TopologicalSpace X :=
  generateFrom {s | s = ∅ ∨ sᶜ.Countable}

/-- Paper: Example E.1.1.9, p. 832.
The closed sets in the cocountable topology are the countable sets and the whole space. -/
theorem isClosed_cocountableTopology_iff {X : Type w} (s : Set X) :
    IsClosed[cocountableTopology X] s ↔ s = univ ∨ s.Countable := by
  sorry

/-- Paper: Example E.1.1.9, p. 832.
The k-topology of an uncountable set with the cocountable topology is discrete.
Deviation: The k-topology is formed with probes in a fixed universe `u`. -/
theorem compactlyGenerated_cocountableTopology_eq_bot (X : Type w) [Uncountable X] :
    @TopologicalSpace.compactlyGenerated.{u, w} X (cocountableTopology X) = ⊥ := by
  sorry

/-- Paper: Example E.1.1.9, p. 832.
An uncountable set with the cocountable topology is not compactly generated.
Deviation: The compact generation predicate uses probes in a fixed universe `u`. -/
theorem not_uCompactlyGeneratedSpace_cocountableTopology (X : Type w) [Uncountable X] :
    ¬ @UCompactlyGeneratedSpace.{u, w} X (cocountableTopology X) := by
  sorry

end RiemannMasullo
