module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment
public import Mathlib.Topology.Category.CompactlyGenerated
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.WithTopology
public import RiemannMasullo.AppE_TopologicalStacks.Sec1a

/-!
# Appendix E.1.2. Categorical and topological stabilities of compactly generated spaces

Paper: §E.1.2 (items E.1.2.1–E.1.2.18, displays E.1.2.1–E.1.2.28), pp. 833–842.

This file formalizes the adjunction between `CompactlyGenerated` and `TopCat`, completeness and
cocompleteness of `CompactlyGenerated`, the distinction between categorical products/pullbacks in
`CompactlyGenerated` and topological products/pullbacks in `TopCat`, the compact-open topology of
Definition E.1.2.6 (distinguished in Remark E.1.2.7 and Remark E.1.2.11 from both the subspace
compact-open topology and Rezk's finer topology), the internal Hom bifunctor `ContK`, cartesian
closure and self-enrichment of `CompactlyGenerated`, the characterization of submersive maps as
regular/effective epimorphisms, and counterexamples to base-change stability in `CG` (Example
E.1.2.16) and product stability of quotient maps in `TopCat` (Example E.1.2.18).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set Topology TopologicalSpace

open scoped Topology CategoryTheory.MonoidalCategory

namespace RiemannMasullo

universe u v v' w w'

section KFunctor

/-- Paper: Lemma E.1.2.1, p. 833.
Equipping any topological space with its `k`-topology produces a compactly generated space.
Deviation: Uses compact Hausdorff probes in a fixed universe `u`. -/
theorem uCompactlyGeneratedSpace_withTopology_compactlyGenerated (X : Type w)
    [TopologicalSpace X] :
    UCompactlyGeneratedSpace.{u}
      (WithTopology X (TopologicalSpace.compactlyGenerated.{u} X)) := by
  sorry

/-- Paper: Lemma E.1.2.1, p. 833.
Any continuous map remains continuous when domain and codomain are equipped with their `k`-topologies.
Deviation: Uses compact Hausdorff probes in a fixed universe `u`. -/
theorem continuous_kFunctor_map {X Y : TopCat.{w}} (f : X ⟶ Y) :
    Continuous (fun x : WithTopology X (TopologicalSpace.compactlyGenerated.{u} X) =>
      WithTopology.toTopology (TopologicalSpace.compactlyGenerated.{u} Y)
        (f (WithTopology.ofTopology x))) := by
  sorry

/-- Paper: Lemma E.1.2.1, display (E.1.2.2), p. 833.
The `k`-ification functor `k : TopCat ⥤ CompactlyGenerated` sending each space to its carrier
with the `k`-topology.
Deviation: Probes lie in a fixed universe `u` and spaces in universe `w`. -/
noncomputable def kFunctor : TopCat.{w} ⥤ CompactlyGenerated.{u, w} where
  obj X :=
    @CompactlyGenerated.of
      (WithTopology X (TopologicalSpace.compactlyGenerated.{u} X)) _
      (uCompactlyGeneratedSpace_withTopology_compactlyGenerated X)
  map {X Y} f :=
    @CompactlyGenerated.ofHom
      (WithTopology X (TopologicalSpace.compactlyGenerated.{u} X)) _
      (uCompactlyGeneratedSpace_withTopology_compactlyGenerated X)
      (WithTopology Y (TopologicalSpace.compactlyGenerated.{u} Y)) _
      (uCompactlyGeneratedSpace_withTopology_compactlyGenerated Y)
      ⟨fun x => WithTopology.toTopology _ (f (WithTopology.ofTopology x)),
        continuous_kFunctor_map.{u} f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Paper: Lemma E.1.2.1(1), p. 833.
The natural bijection `k(Y) → Y` is continuous from the `k`-topology to the original topology. -/
theorem continuous_kCounitApp (Y : TopCat.{w}) :
    Continuous
      (WithTopology.ofTopology :
        WithTopology Y (TopologicalSpace.compactlyGenerated.{u} Y) → Y) := by
  sorry

/-- Paper: Lemma E.1.2.1(1), p. 833.
The natural continuous bijection `k(Y) → Y`. -/
noncomputable def kCounitApp (Y : TopCat.{w}) :
    CompactlyGenerated.compactlyGeneratedToTop.obj (kFunctor.{u, w}.obj Y) ⟶ Y :=
  TopCat.ofHom ⟨WithTopology.ofTopology, continuous_kCounitApp.{u} Y⟩

/-- Paper: Lemma E.1.2.1(1), p. 833.
The counit `k(Y) → Y` is a bijection on underlying sets. -/
theorem bijective_kCounitApp (Y : TopCat.{w}) : Function.Bijective (kCounitApp.{u} Y) := by
  sorry

/-- Paper: Lemma E.1.2.1(2), p. 833.
The canonical identity map `X → k(X)` is continuous when `X` is compactly generated. -/
theorem continuous_kUnitApp (X : CompactlyGenerated.{u, w}) :
    Continuous (fun x : X =>
      WithTopology.toTopology (TopologicalSpace.compactlyGenerated.{u} X) x) := by
  sorry

/-- Paper: Lemma E.1.2.1(2), p. 833.
The unit component `X ⟶ k(u_cg(X))` for a compactly generated space `X`. -/
noncomputable def kUnitApp (X : CompactlyGenerated.{u, w}) :
    X ⟶ kFunctor.{u, w}.obj (CompactlyGenerated.compactlyGeneratedToTop.obj X) :=
  @CompactlyGenerated.ofHom X _ _
    (WithTopology X (TopologicalSpace.compactlyGenerated.{u} X)) _
    (uCompactlyGeneratedSpace_withTopology_compactlyGenerated X)
    ⟨WithTopology.toTopology _, continuous_kUnitApp.{u} X⟩

theorem kUnit_naturality {X Y : CompactlyGenerated.{u, w}} (f : X ⟶ Y) :
    f ≫ kUnitApp.{u} Y =
      kUnitApp.{u} X ≫ kFunctor.map (CompactlyGenerated.compactlyGeneratedToTop.map f) := by
  sorry

theorem kCounit_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) :
    CompactlyGenerated.compactlyGeneratedToTop.map (kFunctor.{u, w}.map f) ≫ kCounitApp.{u} Y =
      kCounitApp.{u} X ≫ f := by
  sorry

theorem kAdjunction_left_triangle (X : CompactlyGenerated.{u, w}) :
    CompactlyGenerated.compactlyGeneratedToTop.map (kUnitApp.{u} X) ≫
        kCounitApp.{u} (CompactlyGenerated.compactlyGeneratedToTop.obj X) =
      𝟙 (CompactlyGenerated.compactlyGeneratedToTop.obj X) := by
  sorry

theorem kAdjunction_right_triangle (Y : TopCat.{w}) :
    kUnitApp.{u} (kFunctor.obj Y) ≫ kFunctor.map (kCounitApp.{u} Y) = 𝟙 (kFunctor.obj Y) := by
  sorry

/-- Paper: Lemma E.1.2.1(1)–(2), displays (E.1.2.1)–(E.1.2.2), p. 833.
The `k`-ification functor `kFunctor` is right adjoint to the forgetful functor
`CompactlyGenerated.compactlyGeneratedToTop`.
Deviation: Both functors use probes in universe `u` and carriers in universe `w`. -/
noncomputable def kFunctorAdjunction :
    CompactlyGenerated.compactlyGeneratedToTop.{u, w} ⊣ kFunctor.{u, w} where
  unit :=
    { app := kUnitApp.{u}
      naturality := @kUnit_naturality.{u, w} }
  counit :=
    { app := kCounitApp.{u}
      naturality := @kCounit_naturality.{u, w} }
  left_triangle_components := kAdjunction_left_triangle.{u, w}
  right_triangle_components := kAdjunction_right_triangle.{u, w}

/-- Paper: Lemma E.1.2.1(1), p. 833.
Every continuous map from a compactly generated space `X` to a topological space `Y` factors
uniquely through the natural continuous bijection `k(Y) → Y`. -/
theorem existsUnique_factor_through_kCounit {X : CompactlyGenerated.{u, w}} {Y : TopCat.{w}}
    (f : CompactlyGenerated.compactlyGeneratedToTop.obj X ⟶ Y) :
    ∃! g : X ⟶ kFunctor.{u, w}.obj Y,
      CompactlyGenerated.compactlyGeneratedToTop.map g ≫ kCounitApp.{u} Y = f := by
  sorry

/-- Paper: Lemma E.1.2.1(2), p. 833.
The unit `id ⟶ k ∘ u_cg` is a natural isomorphism of functors. -/
theorem isIso_kFunctorAdjunction_unit : IsIso kFunctorAdjunction.{u, w}.unit := by
  sorry

/-- Paper: Lemma E.1.2.1(2), p. 833.
For every compactly generated space `X`, the natural map `k(u_cg(X)) → X` is a homeomorphism
inverse to the unit component `X → k(u_cg(X))`. -/
theorem isHomeomorph_kCounitApp_compactlyGenerated (X : CompactlyGenerated.{u, w}) :
    IsHomeomorph (kCounitApp.{u} (CompactlyGenerated.compactlyGeneratedToTop.obj X)) := by
  sorry

end KFunctor

section LimitsAndColimits

/-- Paper: Lemma E.1.2.2, p. 833.
`CompactlyGenerated.{u, w}` has limits of all small diagrams (indexed in any universe `v ≤ w`). -/
theorem hasLimitsOfSize_compactlyGenerated [UnivLE.{v, w}] :
    HasLimitsOfSize.{v', v} CompactlyGenerated.{u, w} := by
  sorry

/-- Paper: Lemma E.1.2.2, p. 833.
`CompactlyGenerated.{u, w}` has colimits of all small diagrams (indexed in any universe `v ≤ w`). -/
theorem hasColimitsOfSize_compactlyGenerated [UnivLE.{v, w}] :
    HasColimitsOfSize.{v', v} CompactlyGenerated.{u, w} := by
  sorry

noncomputable instance instHasLimitsOfSizeCompactlyGenerated [UnivLE.{v, w}] :
    HasLimitsOfSize.{v', v} CompactlyGenerated.{u, w} :=
  hasLimitsOfSize_compactlyGenerated

noncomputable instance instHasColimitsOfSizeCompactlyGenerated [UnivLE.{v, w}] :
    HasColimitsOfSize.{v', v} CompactlyGenerated.{u, w} :=
  hasColimitsOfSize_compactlyGenerated

/-- Paper: Lemma E.1.2.2(1), display (E.1.2.3), p. 833.
Canonical comparison morphism from the limit in `CompactlyGenerated` to `k` applied to the limit
of `u_cg ∘ P` in `TopCat`. -/
noncomputable def compactlyGeneratedLimitComparison {I : Type v} [Category.{v'} I] [UnivLE.{v, w}]
    (P : I ⥤ CompactlyGenerated.{u, w}) :
    limit P ⟶ kFunctor.{u, w}.obj (limit (P ⋙ CompactlyGenerated.compactlyGeneratedToTop)) :=
  kFunctorAdjunction.homEquiv (limit P) _
    (limit.lift (P ⋙ CompactlyGenerated.compactlyGeneratedToTop)
      (CompactlyGenerated.compactlyGeneratedToTop.mapCone (limit.cone P)))

/-- Paper: Lemma E.1.2.2(1), display (E.1.2.3), p. 833.
The limit of a small diagram `P` in `CG` is computed as `k(lim_I (u_cg ∘ P))`. -/
theorem isIso_compactlyGeneratedLimitComparison {I : Type v} [Category.{v'} I] [UnivLE.{v, w}]
    (P : I ⥤ CompactlyGenerated.{u, w}) :
    IsIso (compactlyGeneratedLimitComparison.{u, v, v', w} P) := by
  sorry

/-- Paper: Lemma E.1.2.2(2), p. 833.
The forgetful functor `u_cg : CG ⥤ Spaces` preserves all small colimits. -/
theorem preservesColimitsOfSize_compactlyGeneratedToTop [UnivLE.{v, w}] :
    PreservesColimitsOfSize.{v', v} (CompactlyGenerated.compactlyGeneratedToTop.{u, w}) := by
  sorry

/-- Paper: Lemma E.1.2.2(2), p. 833.
The forgetful functor `u_cg : CG ⥤ Spaces` reflects all small colimits. -/
theorem reflectsColimitsOfSize_compactlyGeneratedToTop [UnivLE.{v, w}] :
    ReflectsColimitsOfSize.{v', v} (CompactlyGenerated.compactlyGeneratedToTop.{u, w}) := by
  sorry

noncomputable instance instPreservesColimitsOfSizeCompactlyGeneratedToTop [UnivLE.{v, w}] :
    PreservesColimitsOfSize.{v', v} (CompactlyGenerated.compactlyGeneratedToTop.{u, w}) :=
  preservesColimitsOfSize_compactlyGeneratedToTop

noncomputable instance instReflectsColimitsOfSizeCompactlyGeneratedToTop [UnivLE.{v, w}] :
    ReflectsColimitsOfSize.{v', v} (CompactlyGenerated.compactlyGeneratedToTop.{u, w}) :=
  reflectsColimitsOfSize_compactlyGeneratedToTop

/-- Paper: Lemma E.1.2.2(2), pp. 833–834.
A topological coproduct of compactly generated spaces is compactly generated. -/
theorem uCompactlyGeneratedSpace_sigma {I : Type v} {P : I → Type w}
    [∀ i, TopologicalSpace (P i)] [∀ i, UCompactlyGeneratedSpace.{u} (P i)] :
    UCompactlyGeneratedSpace.{u} (Σ i, P i) := by
  sorry

/-- Paper: Lemma E.1.2.2(2), p. 834.
A quotient of a compactly generated space by a submersive map is compactly generated. -/
theorem uCompactlyGeneratedSpace_of_isQuotientMap {X : Type w} {Z : Type w'}
    [TopologicalSpace X] [TopologicalSpace Z] [UCompactlyGeneratedSpace.{u} X]
    {f : X → Z} (hf : IsQuotientMap f) :
    UCompactlyGeneratedSpace.{u} Z := by
  sorry

/-- Paper: Remark E.1.2.3, p. 834.
The forgetful functor `u_cg : CG ⥤ Spaces` does not preserve binary products (and hence does not
preserve all small limits). Cf. Lemma E.2.4.9 and Example E.1.2.18. -/
theorem not_preservesBinaryProducts_compactlyGeneratedToTop :
    ¬ PreservesLimitsOfShape (Discrete WalkingPair)
      (CompactlyGenerated.compactlyGeneratedToTop.{u, w}) := by
  sorry

end LimitsAndColimits

section TopologicalProducts

/-- Paper: Definition E.1.2.4(2), p. 834.
The topological product `X ×₀ Y` of two compactly generated spaces in `TopCat`, i.e., `X × Y`
endowed with the product topology. -/
noncomputable def cgTopProd (X Y : CompactlyGenerated.{u, w}) : TopCat.{w} :=
  TopCat.of (X × Y)

/-- Paper: Definition E.1.2.4(2), p. 834.
`cgTopProd X Y` is isomorphic in `TopCat` to the categorical product of `u_cg X` and `u_cg Y`. -/
theorem cgTopProd_eq_topCat_prod (X Y : CompactlyGenerated.{u, w}) :
    Nonempty (cgTopProd X Y ≅
      CompactlyGenerated.compactlyGeneratedToTop.obj X ⨯
        CompactlyGenerated.compactlyGeneratedToTop.obj Y) := by
  sorry

/-- Paper: Definition E.1.2.4(3), p. 834.
The topological fibre product `X ×⁰_{f, Z, g} Y` in `TopCat`, defined as the preimage of the
diagonal under `(f, g) : X ×₀ Y → Z ×₀ Z`. -/
noncomputable def cgTopPullback {X Y Z : CompactlyGenerated.{u, w}}
    (f : X ⟶ Z) (g : Y ⟶ Z) : TopCat.{w} :=
  TopCat.of { p : X × Y // f p.1 = g p.2 }

/-- Paper: Definition E.1.2.4(3), p. 834.
The topological fibre product is the preimage of the diagonal under `(f, g) : X ×₀ Y → Z ×₀ Z`
with the subspace topology, and models the pullback in `TopCat`. -/
theorem cgTopPullback_eq_preimage_diagonal {X Y Z : CompactlyGenerated.{u, w}}
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    { p : cgTopProd X Y | (fun q : cgTopProd X Y => (f q.1, g q.2)) p ∈ diagonal Z } =
      { p : X × Y | f p.1 = g p.2 } ∧
      Nonempty (cgTopPullback f g ≅
        pullback (CompactlyGenerated.compactlyGeneratedToTop.map f)
          (CompactlyGenerated.compactlyGeneratedToTop.map g)) := by
  sorry

/-- Paper: Definition E.1.2.4(4), p. 834.
The topological product `∏⁰_I P` of an `I`-indexed family in `CG`, computed in `TopCat`. -/
noncomputable def cgTopPi {I : Type w} (P : I → CompactlyGenerated.{u, w}) : TopCat.{w} :=
  TopCat.of (∀ i : I, P i)

/-- Paper: Definition E.1.2.4(4), p. 834.
`cgTopPi P` is isomorphic in `TopCat` to the categorical product of `u_cg ∘ P`. -/
theorem cgTopPi_eq_topCat_pi {I : Type w} (P : I → CompactlyGenerated.{u, w}) :
    Nonempty (cgTopPi P ≅ ∏ᶜ (fun i => CompactlyGenerated.compactlyGeneratedToTop.obj (P i))) := by
  sorry

/-- Paper: Remark E.1.2.5(1), p. 834.
The coproduct `∐ P` in `CG` has underlying space isomorphic in `TopCat` to the topological
disjoint union `Σ i, P i`. -/
theorem compactlyGenerated_coproduct_iso_sigma {I : Type w}
    (P : I → CompactlyGenerated.{u, w}) :
    Nonempty (CompactlyGenerated.compactlyGeneratedToTop.obj (∐ P) ≅ TopCat.of (Σ i, P i)) := by
  sorry

/-- Paper: Remark E.1.2.5(2), p. 834.
The internal product `X ⨯ Y` in `CG` is isomorphic to `k(X ×₀ Y)`. -/
theorem compactlyGenerated_prod_iso_kFunctor (X Y : CompactlyGenerated.{u, w}) :
    Nonempty (X ⨯ Y ≅ kFunctor.{u, w}.obj (cgTopProd X Y)) := by
  sorry

/-- Paper: Remark E.1.2.5(2), p. 834.
The internal product `∏ᶜ P` in `CG` is isomorphic to `k(∏⁰_I P)`. -/
theorem compactlyGenerated_pi_iso_kFunctor {I : Type w} (P : I → CompactlyGenerated.{u, w}) :
    Nonempty (∏ᶜ P ≅ kFunctor.{u, w}.obj (cgTopPi P)) := by
  sorry

end TopologicalProducts

section CompactOpenAndContK

/-- Paper: Definition E.1.2.6(1), p. 835.
The sub-basic subset `N(g, K, U) ⊆ C(X, Y)` consisting of continuous maps `f : X → Y` such that
`(f ∘ g)(K) ⊆ U`.
Deviation: Compact Hausdorff probes `K` lie in a fixed universe `u`. -/
def cgSubbaseSet {X : Type w} {Y : Type w'} [TopologicalSpace X] [TopologicalSpace Y]
    {K : CompHaus.{u}} (g : C(K, X)) (U : Set Y) : Set C(X, Y) :=
  { f | ∀ k : K, f (g k) ∈ U }

/-- Paper: Definition E.1.2.6(1), display (E.1.2.4), p. 835.
The sub-basic set `N(g, K, U)` coincides with the fibre product condition `f ∘ g = j ∘ h` for
`h : C(K, U)` and open inclusion `j : U → Y`. -/
theorem cgSubbaseSet_eq_fiberProduct {X : Type w} {Y : Type w'}
    [TopologicalSpace X] [TopologicalSpace Y] {K : CompHaus.{u}} (g : C(K, X))
    {U : Set Y} (hU : IsOpen U) :
    cgSubbaseSet.{u} g U =
      { f : C(X, Y) | ∃ h : C(K, U),
        f.comp g = (⟨Subtype.val, continuous_subtype_val⟩ : C(U, Y)).comp h } := by
  sorry

/-- Paper: Definition E.1.2.6(2), p. 835.
The compact-open topology on `C(X, Y)` generated by the sub-base `N(g, K, U)` for compact
Hausdorff probes `K : CompHaus.{u}`, continuous maps `g : C(K, X)`, and open sets `U ⊆ Y`.
Deviation: Distinguished from Mathlib's `ContinuousMap.compactOpen` (see Remark E.1.2.7), which
uses all compact subsets of `X` rather than continuous images of `CompHaus.{u}` probes. -/
@[instance_reducible]
def cgCompactOpenTopology (X : Type w) (Y : Type w') [TopologicalSpace X] [TopologicalSpace Y] :
    TopologicalSpace C(X, Y) :=
  generateFrom
    { S | ∃ (K : CompHaus.{u}) (g : C(K, X)) (U : Set Y), IsOpen U ∧ S = cgSubbaseSet g U }

/-- Paper: Remark E.1.2.7, p. 835.
A `cgCompactOpenTopology`-open set is generated from `cgSubbaseSet` sets; every `cgSubbaseSet` is
contained in Mathlib's `ContinuousMap.compactOpen` sub-base because `Set.range g` is compact,
while `cgCompactOpenTopology` is strictly finer than the topology generated only by immersions
from compact Hausdorff spaces in general. -/
theorem cgCompactOpenTopology_le_mathlibCompactOpen (X : Type w) (Y : Type w')
    [TopologicalSpace X] [TopologicalSpace Y] :
    (ContinuousMap.compactOpen : TopologicalSpace C(X, Y)) ≤
      cgCompactOpenTopology.{u} X Y := by
  sorry

/-- Paper: Definition E.1.2.6(2) and Construction E.1.2.9, pp. 835–836.
The space of continuous maps `C(X, Y)` endowed with the compact-open topology of Definition E.1.2.6.
Deviation: Uses compact Hausdorff probes in a fixed universe `u`. -/
def CGCompactOpen (X : Type w) (Y : Type w') [TopologicalSpace X] [TopologicalSpace Y] :
    Type (max w w') :=
  WithTopology C(X, Y) (cgCompactOpenTopology.{u} X Y)

instance instTopologicalSpaceCGCompactOpen (X : Type w) (Y : Type w')
    [TopologicalSpace X] [TopologicalSpace Y] :
    TopologicalSpace (CGCompactOpen.{u} X Y) :=
  inferInstanceAs (TopologicalSpace (WithTopology C(X, Y) (cgCompactOpenTopology.{u} X Y)))

/-- Paper: Definition E.1.2.6(2), p. 835.
Coercion/equivalence between `CGCompactOpen X Y` and `C(X, Y)`. -/
def cgCompactOpenEquiv (X : Type w) (Y : Type w') [TopologicalSpace X] [TopologicalSpace Y] :
    CGCompactOpen.{u} X Y ≃ C(X, Y) :=
  WithTopology.equiv C(X, Y) (cgCompactOpenTopology.{u} X Y)

/-- Paper: Definition E.1.2.6(2), p. 835.
A subset of `CGCompactOpen X Y` is open iff its image in `C(X, Y)` is open for
`cgCompactOpenTopology`. -/
theorem isOpen_cgCompactOpen_iff {X : Type w} {Y : Type w'}
    [TopologicalSpace X] [TopologicalSpace Y] (S : Set (CGCompactOpen.{u} X Y)) :
    IsOpen S ↔ IsOpen[cgCompactOpenTopology.{u} X Y] ((cgCompactOpenEquiv.{u} X Y).symm ⁻¹' S) :=
  Iff.rfl

/-- Paper: Definition E.1.2.6(2), p. 835.
Sanity lemma: each sub-basic set `N(g, K, U)` for open `U` is open in `CGCompactOpen X Y`. -/
theorem isOpen_cgCompactOpen_subbase {X : Type w} {Y : Type w'}
    [TopologicalSpace X] [TopologicalSpace Y] {K : CompHaus.{u}} (g : C(K, X))
    {U : Set Y} (hU : IsOpen U) :
    IsOpen ((cgCompactOpenEquiv.{u} X Y) ⁻¹' cgSubbaseSet.{u} g U) := by
  sorry

/-- Paper: Lemma E.1.2.8, displays (E.1.2.5)–(E.1.2.6), p. 836.
Set-theoretic consistency check: there exists a `max w w'`-small index type `S_{X, Y}` and triples
`(K_σ, g_σ, U_σ)` such that the coarsest topology making every `N(g_σ, K_σ, U_σ)` open is the
compact-open topology `cgCompactOpenTopology X Y`.
Deviation: Compact Hausdorff probes `K_σ` lie in `CompHaus.{u}`, and smallness is witnessed in
`Type (max w w')`, the universe of `C(X, Y)`. -/
theorem exists_small_subbase_cgCompactOpenTopology (X : Type w) (Y : Type w')
    [TopologicalSpace X] [TopologicalSpace Y] :
    ∃ (I : Type (max w w')) (K : I → CompHaus.{u}) (g : ∀ σ, C(K σ, X)) (U : I → Set Y),
      (∀ σ, IsOpen (U σ)) ∧
        cgCompactOpenTopology.{u} X Y = generateFrom (range fun σ => cgSubbaseSet (g σ) (U σ)) := by
  sorry

/-- Paper: Construction E.1.2.9, p. 836.
The internal function space `ContK X Y := k(CGCompactOpen X Y)` between compactly generated
spaces `X, Y : CompactlyGenerated.{u, w}`. -/
noncomputable def ContK (X Y : CompactlyGenerated.{u, w}) : CompactlyGenerated.{u, w} :=
  kFunctor.{u, w}.obj (TopCat.of (CGCompactOpen.{u} X Y))

/-- Paper: Construction E.1.2.9, p. 836.
Canonical bijection between points of `ContK X Y` and continuous maps `C(X, Y)`. -/
def contKEquiv (X Y : CompactlyGenerated.{u, w}) : (ContK X Y : Type w) ≃ C(X, Y) :=
  (WithTopology.equiv _ _).trans (cgCompactOpenEquiv.{u} X Y)

/-- Paper: Construction E.1.2.9, p. 836.
Sanity lemma: the identity from `ContK X Y` to `CGCompactOpen X Y` is continuous, and a map
from a compactly generated space into `ContK X Y` is continuous iff it is continuous into
`CGCompactOpen X Y`. -/
theorem continuous_to_contK_iff {T X Y : CompactlyGenerated.{u, w}} (f : T → ContK X Y) :
    Continuous f ↔ Continuous (fun t => (WithTopology.ofTopology (f t) : CGCompactOpen.{u} X Y)) := by
  sorry

/-- Paper: Lemma E.1.2.10, display (E.1.2.7), pp. 836–837.
Covariant functoriality on `CGCompactOpen`: postcomposition by a continuous map `f : Y → Y'` is
continuous for `cgCompactOpenTopology`. -/
theorem continuous_cgCompactOpen_postcomp (X : CompactlyGenerated.{u, w})
    {Y Y' : CompactlyGenerated.{u, w}} (f : Y ⟶ Y') :
    Continuous (fun g : CGCompactOpen.{u} X Y =>
      (cgCompactOpenEquiv.{u} X Y').symm
        (f.hom.hom.comp (cgCompactOpenEquiv.{u} X Y g))) := by
  sorry

/-- Paper: Lemma E.1.2.10, display (E.1.2.8), p. 837.
Preimage of a sub-basic set under postcomposition `f_*`. -/
theorem preimage_postcomp_cgSubbaseSet (X : CompactlyGenerated.{u, w})
    {Y Y' : CompactlyGenerated.{u, w}} (f : Y ⟶ Y') {K : CompHaus.{u}}
    (a : C(K, X)) (U : Set Y') :
    (fun g : C(X, Y) => f.hom.hom.comp g) ⁻¹' cgSubbaseSet a U =
      cgSubbaseSet a (f ⁻¹' U) := by
  sorry

/-- Paper: Lemma E.1.2.10, p. 837.
Contravariant functoriality on `CGCompactOpen`: precomposition by a continuous map `f : X' → X` is
continuous for `cgCompactOpenTopology`. -/
theorem continuous_cgCompactOpen_precomp {X X' : CompactlyGenerated.{u, w}} (f : X' ⟶ X)
    (Y : CompactlyGenerated.{u, w}) :
    Continuous (fun g : CGCompactOpen.{u} X Y =>
      (cgCompactOpenEquiv.{u} X' Y).symm
        ((cgCompactOpenEquiv.{u} X Y g).comp f.hom.hom)) := by
  sorry

/-- Paper: Lemma E.1.2.10, p. 837.
Preimage of a sub-basic set under precomposition `f^*`. -/
theorem preimage_precomp_cgSubbaseSet {X X' : CompactlyGenerated.{u, w}} (f : X' ⟶ X)
    (Y : CompactlyGenerated.{u, w}) {K : CompHaus.{u}} (a : C(K, X')) (U : Set Y) :
    (fun g : C(X, Y) => g.comp f.hom.hom) ⁻¹' cgSubbaseSet a U =
      cgSubbaseSet (f.hom.hom.comp a) U := by
  sorry

/-- Paper: Lemma E.1.2.10, pp. 836–837.
Covariant map of `ContK` in the second variable. -/
noncomputable def contKPostcomp (X : CompactlyGenerated.{u, w})
    {Y Y' : CompactlyGenerated.{u, w}} (f : Y ⟶ Y') : ContK X Y ⟶ ContK X Y' :=
  kFunctor.{u, w}.map (TopCat.ofHom ⟨_, continuous_cgCompactOpen_postcomp X f⟩)

/-- Paper: Lemma E.1.2.10, p. 837.
Contravariant map of `ContK` in the first variable. -/
noncomputable def contKPrecomp {X X' : CompactlyGenerated.{u, w}} (f : X' ⟶ X)
    (Y : CompactlyGenerated.{u, w}) : ContK X Y ⟶ ContK X' Y :=
  kFunctor.{u, w}.map (TopCat.ofHom ⟨_, continuous_cgCompactOpen_precomp f Y⟩)

theorem contK_postcomp_id (X Y : CompactlyGenerated.{u, w}) :
    contKPostcomp X (𝟙 Y) = 𝟙 (ContK X Y) := by
  sorry

theorem contK_postcomp_comp (X : CompactlyGenerated.{u, w})
    {Y₁ Y₂ Y₃ : CompactlyGenerated.{u, w}} (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) :
    contKPostcomp X (f ≫ g) = contKPostcomp X f ≫ contKPostcomp X g := by
  sorry

theorem contK_precomp_id (X Y : CompactlyGenerated.{u, w}) :
    contKPrecomp (𝟙 X) Y = 𝟙 (ContK X Y) := by
  sorry

theorem contK_precomp_comp {X₁ X₂ X₃ : CompactlyGenerated.{u, w}}
    (f : X₂ ⟶ X₁) (g : X₃ ⟶ X₂) (Y : CompactlyGenerated.{u, w}) :
    contKPrecomp (g ≫ f) Y = contKPrecomp f Y ≫ contKPrecomp g Y := by
  sorry

theorem contK_bimap_naturality {X X' Y Y' : CompactlyGenerated.{u, w}}
    (f : X' ⟶ X) (g : Y ⟶ Y') :
    contKPrecomp f Y ≫ contKPostcomp X' g = contKPostcomp X g ≫ contKPrecomp f Y' := by
  sorry

/-- Paper: Lemma E.1.2.10, pp. 836–837.
The internal Hom bifunctor `ContK : CGᵒᵖ ⥤ CG ⥤ CG`. -/
noncomputable def contKBifunctor :
    CompactlyGenerated.{u, w}ᵒᵖ ⥤ CompactlyGenerated.{u, w} ⥤ CompactlyGenerated.{u, w} where
  obj X :=
    { obj := fun Y => ContK X.unop Y
      map := fun g => contKPostcomp X.unop g
      map_id := fun Y => contK_postcomp_id X.unop Y
      map_comp := fun f g => contK_postcomp_comp X.unop f g }
  map {X X'} f :=
    { app := fun Y => contKPrecomp f.unop Y
      naturality := fun _ _ g => contK_bimap_naturality f.unop g }
  map_id X := by
    ext Y
    exact ConcreteCategory.congr_hom (contK_precomp_id X.unop Y) _
  map_comp {X₁ X₂ X₃} f g := by
    ext Y
    exact ConcreteCategory.congr_hom (contK_precomp_comp f.unop g.unop Y) _

end CompactOpenAndContK

section ExponentialAndCartesianClosed

/-- Paper: Lemma E.1.2.12, displays (E.1.2.9) and (E.1.2.26), pp. 838–840.
The evaluation map `ContK Y Z ⨯ Y ⟶ Z` sending `(f, y)` to `f(y)` is continuous in `CG`. -/
theorem continuous_contKEval (Y Z : CompactlyGenerated.{u, w}) :
    Continuous (fun p : (ContK Y Z ⨯ Y : CompactlyGenerated.{u, w}) =>
      (contKEquiv Y Z (Limits.prod.fst (X := ContK Y Z) (Y := Y) p))
        (Limits.prod.snd (X := ContK Y Z) (Y := Y) p)) := by
  sorry

/-- Paper: Lemma E.1.2.12, display (E.1.2.26), p. 840.
The evaluation morphism `ev_{Y, Z} : ContK Y Z ⨯ Y ⟶ Z` in `CompactlyGenerated`. -/
noncomputable def contKEval (Y Z : CompactlyGenerated.{u, w}) : ContK Y Z ⨯ Y ⟶ Z :=
  CompactlyGenerated.ofHom
    ⟨fun p =>
      (contKEquiv Y Z (Limits.prod.fst (X := ContK Y Z) (Y := Y) p))
        (Limits.prod.snd (X := ContK Y Z) (Y := Y) p),
      continuous_contKEval Y Z⟩

/-- Paper: Lemma E.1.2.12, displays (E.1.2.19)–(E.1.2.24), pp. 839–840.
Given `h : X ⨯ Y ⟶ Z`, the curried map `x ↦ (y ↦ h(x, y))` sends each `x` to a continuous map
`Y → Z` and is continuous as a map `X → ContK Y Z`. -/
theorem continuous_contKCurry_slice {X Y Z : CompactlyGenerated.{u, w}} (h : X ⨯ Y ⟶ Z)
    (x : X) :
    Continuous (fun y : Y =>
      h ((Limits.prod.lift
        (CompactlyGenerated.ofHom (ContinuousMap.const (Y : Type w) x)) (𝟙 Y)) y)) := by
  sorry

/-- Paper: Lemma E.1.2.12, displays (E.1.2.20)–(E.1.2.24), pp. 839–840.
The currying map `X ⟶ ContK Y Z` induced by `h : X ⨯ Y ⟶ Z` is continuous. -/
theorem continuous_contKCurry {X Y Z : CompactlyGenerated.{u, w}} (h : X ⨯ Y ⟶ Z) :
    Continuous (fun x : X =>
      (contKEquiv Y Z).symm ⟨_, continuous_contKCurry_slice h x⟩) := by
  sorry

/-- Paper: Lemma E.1.2.12, display (E.1.2.25), p. 840.
Natural currying morphism `X ⟶ ContK Y Z` attached to `h : X ⨯ Y ⟶ Z`. -/
noncomputable def contKCurry {X Y Z : CompactlyGenerated.{u, w}} (h : X ⨯ Y ⟶ Z) :
    X ⟶ ContK Y Z :=
  ConcreteCategory.ofHom (C := CompactlyGenerated.{u, w}) ⟨_, continuous_contKCurry h⟩

/-- Paper: Lemma E.1.2.12, display (E.1.2.28), p. 840.
Postcomposition `g ↦ g_*` is continuous as a map `ContK X₂ X₃ → ContK (ContK X₁ X₂) (ContK X₁ X₃)`.
Note: Footnote 3 on p. 840 flags the missing explanation of continuity of (E.1.2.28) in the
printed proof. -/
theorem continuous_contKPostcompMap (X₁ X₂ X₃ : CompactlyGenerated.{u, w}) :
    Continuous (fun g : ContK X₂ X₃ =>
      (contKEquiv (ContK X₁ X₂) (ContK X₁ X₃)).symm
        (ConcreteCategory.hom (contKPostcomp X₁ (CompactlyGenerated.ofHom (contKEquiv X₂ X₃ g))))) := by
  sorry

/-- Paper: Lemma E.1.2.12, pp. 837–840.
The currying map `θ_{X, Y, Z} : ContK (X ⨯ Y) Z → ContK X (ContK Y Z)` is continuous. -/
theorem continuous_contKCurryHomeomorph (X Y Z : CompactlyGenerated.{u, w}) :
    Continuous (fun f : ContK (X ⨯ Y) Z =>
      (contKEquiv X (ContK Y Z)).symm
        (ConcreteCategory.hom
          (contKCurry (CompactlyGenerated.ofHom (contKEquiv (X ⨯ Y) Z f))))) := by
  sorry

/-- Paper: Lemma E.1.2.12, pp. 837–840.
The uncurrying map `ψ_{X, Y, Z} : ContK X (ContK Y Z) → ContK (X ⨯ Y) Z` is continuous. -/
theorem continuous_contKUncurryHomeomorph (X Y Z : CompactlyGenerated.{u, w}) :
    Continuous (fun f : ContK X (ContK Y Z) =>
      (contKEquiv (X ⨯ Y) Z).symm
        (ConcreteCategory.hom
          ((Limits.prod.map (CompactlyGenerated.ofHom (contKEquiv X (ContK Y Z) f)) (𝟙 Y)) ≫
            contKEval Y Z))) := by
  sorry

theorem contKCurryHomeomorph_left_inv (X Y Z : CompactlyGenerated.{u, w})
    (f : (ContK (X ⨯ Y) Z : Type w)) :
    (contKEquiv (X ⨯ Y) Z).symm
        (ConcreteCategory.hom
          ((Limits.prod.map
              (CompactlyGenerated.ofHom
                (contKEquiv X (ContK Y Z)
                  ((contKEquiv X (ContK Y Z)).symm
                    (ConcreteCategory.hom
                      (contKCurry (CompactlyGenerated.ofHom (contKEquiv (X ⨯ Y) Z f)))))))
              (𝟙 Y)) ≫
            contKEval Y Z)) =
      f := by
  sorry

theorem contKCurryHomeomorph_right_inv (X Y Z : CompactlyGenerated.{u, w})
    (f : (ContK X (ContK Y Z) : Type w)) :
    (contKEquiv X (ContK Y Z)).symm
        (ConcreteCategory.hom
          (contKCurry
            (CompactlyGenerated.ofHom
              (contKEquiv (X ⨯ Y) Z
                ((contKEquiv (X ⨯ Y) Z).symm
                  (ConcreteCategory.hom
                    ((Limits.prod.map (CompactlyGenerated.ofHom (contKEquiv X (ContK Y Z) f)) (𝟙 Y)) ≫
                      contKEval Y Z))))))) =
      f := by
  sorry

/-- Paper: Lemma E.1.2.12, pp. 837–840.
The natural exponential homeomorphism
`θ_{X, Y, Z} : ContK (X ⨯ Y) Z ≃ₜ ContK X (ContK Y Z)`. -/
noncomputable def contKCurryHomeomorph (X Y Z : CompactlyGenerated.{u, w}) :
    (ContK (X ⨯ Y) Z : Type w) ≃ₜ ContK X (ContK Y Z) where
  toFun f :=
    (contKEquiv X (ContK Y Z)).symm
      (ConcreteCategory.hom
        (contKCurry (CompactlyGenerated.ofHom (contKEquiv (X ⨯ Y) Z f))))
  invFun f :=
    (contKEquiv (X ⨯ Y) Z).symm
      (ConcreteCategory.hom
        ((Limits.prod.map (CompactlyGenerated.ofHom (contKEquiv X (ContK Y Z) f)) (𝟙 Y)) ≫
          contKEval Y Z))
  left_inv := contKCurryHomeomorph_left_inv X Y Z
  right_inv := contKCurryHomeomorph_right_inv X Y Z
  continuous_toFun := continuous_contKCurryHomeomorph X Y Z
  continuous_invFun := continuous_contKUncurryHomeomorph X Y Z

/-- Paper: Lemma E.1.2.12, pp. 837–840.
In particular, applying `θ⁻¹_{ContK X Y, X, Y}` to the identity map of `ContK X Y` yields the
evaluation map `(f, x) ↦ f(x)`. -/
theorem contKCurryHomeomorph_symm_id_eq_eval (X Y : CompactlyGenerated.{u, w}) :
    (contKEquiv ((ContK X Y ⨯ X)) Y
        ((contKCurryHomeomorph (ContK X Y) X Y).symm
          ((contKEquiv (ContK X Y) (ContK X Y)).symm (ContinuousMap.id _))) :
        (ContK X Y ⨯ X : CompactlyGenerated.{u, w}) → Y) =
      (contKEval X Y : (ContK X Y ⨯ X : CompactlyGenerated.{u, w}) → Y) := by
  sorry

end ExponentialAndCartesianClosed

section CartesianClosedAndSubmersive

/-- Paper: Proposition E.1.2.13, p. 841.
The cartesian symmetric monoidal structure on `CompactlyGenerated.{u, w}` induced by finite
products and the terminal object. -/
noncomputable instance instCartesianMonoidalCategoryCompactlyGenerated :
    CartesianMonoidalCategory CompactlyGenerated.{u, w} :=
  CartesianMonoidalCategory.ofHasFiniteProducts

theorem continuous_contKTensorUnit_slice (Y X : CompactlyGenerated.{u, w}) (x : X) :
    Continuous (fun y : Y =>
      (CartesianMonoidalCategory.lift
        (CompactlyGenerated.ofHom (ContinuousMap.id (Y : Type w)))
        (CompactlyGenerated.ofHom (ContinuousMap.const (Y : Type w) x)) : Y ⟶ Y ⊗ X) y) := by
  sorry

theorem continuous_contKTensorUnit (Y X : CompactlyGenerated.{u, w}) :
    Continuous (fun x : X =>
      (contKEquiv Y (Y ⊗ X)).symm ⟨_, continuous_contKTensorUnit_slice Y X x⟩) := by
  sorry

noncomputable def contKTensorUnitApp (Y X : CompactlyGenerated.{u, w}) :
    X ⟶ ContK Y (Y ⊗ X) :=
  ConcreteCategory.ofHom (C := CompactlyGenerated.{u, w}) ⟨_, continuous_contKTensorUnit Y X⟩

theorem continuous_contKTensorCounit (Y Z : CompactlyGenerated.{u, w}) :
    Continuous (fun p : (Y ⊗ ContK Y Z : CompactlyGenerated.{u, w}) =>
      (contKEquiv Y Z (CartesianMonoidalCategory.snd Y (ContK Y Z) p))
        (CartesianMonoidalCategory.fst Y (ContK Y Z) p)) := by
  sorry

noncomputable def contKTensorCounitApp (Y Z : CompactlyGenerated.{u, w}) :
    Y ⊗ ContK Y Z ⟶ Z :=
  CompactlyGenerated.ofHom
    ⟨fun p =>
      (contKEquiv Y Z (CartesianMonoidalCategory.snd Y (ContK Y Z) p))
        (CartesianMonoidalCategory.fst Y (ContK Y Z) p),
      continuous_contKTensorCounit Y Z⟩

theorem contKTensorUnit_naturality (Y : CompactlyGenerated.{u, w})
    {X X' : CompactlyGenerated.{u, w}} (f : X ⟶ X') :
    f ≫ contKTensorUnitApp Y X' =
      contKTensorUnitApp Y X ≫
        (contKBifunctor.{u, w}.obj (Opposite.op Y)).map ((MonoidalCategory.tensorLeft Y).map f) := by
  sorry

theorem contKTensorCounit_naturality (Y : CompactlyGenerated.{u, w})
    {Z Z' : CompactlyGenerated.{u, w}} (f : Z ⟶ Z') :
    (MonoidalCategory.tensorLeft Y).map ((contKBifunctor.{u, w}.obj (Opposite.op Y)).map f) ≫
        contKTensorCounitApp Y Z' =
      contKTensorCounitApp Y Z ≫ f := by
  sorry

theorem contKTensorAdjunction_left_triangle (Y X : CompactlyGenerated.{u, w}) :
    (MonoidalCategory.tensorLeft Y).map (contKTensorUnitApp Y X) ≫
        contKTensorCounitApp Y ((MonoidalCategory.tensorLeft Y).obj X) =
      𝟙 ((MonoidalCategory.tensorLeft Y).obj X) := by
  sorry

theorem contKTensorAdjunction_right_triangle (Y Z : CompactlyGenerated.{u, w}) :
    contKTensorUnitApp Y ((contKBifunctor.{u, w}.obj (Opposite.op Y)).obj Z) ≫
        (contKBifunctor.{u, w}.obj (Opposite.op Y)).map (contKTensorCounitApp Y Z) =
      𝟙 ((contKBifunctor.{u, w}.obj (Opposite.op Y)).obj Z) := by
  sorry

/-- Paper: Proposition E.1.2.13, p. 841.
Closed structure on every compactly generated space `Y`, with right adjoint `ContK Y -`. -/
@[instance_reducible]
noncomputable def closedCompactlyGenerated (Y : CompactlyGenerated.{u, w}) :
    Closed Y where
  rightAdj := contKBifunctor.{u, w}.obj (Opposite.op Y)
  adj :=
    { unit :=
        { app := contKTensorUnitApp Y
          naturality := fun _ _ f => contKTensorUnit_naturality Y f }
      counit :=
        { app := contKTensorCounitApp Y
          naturality := fun _ _ f => contKTensorCounit_naturality Y f }
      left_triangle_components := contKTensorAdjunction_left_triangle Y
      right_triangle_components := contKTensorAdjunction_right_triangle Y }

/-- Paper: Proposition E.1.2.13, p. 841.
`CompactlyGenerated.{u, w}` is cartesian monoidal closed with internal Hom given by `ContK`. -/
noncomputable instance instMonoidalClosedCompactlyGenerated :
    MonoidalClosed CompactlyGenerated.{u, w} where
  closed := closedCompactlyGenerated

/-- Paper: Proposition E.1.2.13, p. 841.
`CompactlyGenerated.{u, w}` carries a self-enriched ordinary category structure via `ContK`. -/
theorem nonempty_enrichedOrdinaryCategorySelf_compactlyGenerated :
    Nonempty (EnrichedOrdinaryCategory CompactlyGenerated.{u, w} CompactlyGenerated.{u, w}) :=
  ⟨by
    let _ := MonoidalClosed.enrichedOrdinaryCategorySelf CompactlyGenerated.{u, w}
    infer_instance⟩

/-- Paper: Lemma E.1.2.14, p. 841.
For a continuous map `f : X ⟶ Y` in `CG`, the following are equivalent:
(1) `f` is isomorphic (via a homeomorphism on the target) to the coequalizer of a parallel pair
`s, t : R ⇉ X` in `CG`;
(2) `f` is the coequalizer in `CG` of the kernel pair `pullback.fst f f, pullback.snd f f : X ×_Y X ⇉ X`;
(3) `f` is a submersive (quotient) map. -/
theorem isQuotientMap_compactlyGenerated_tfae {X Y : CompactlyGenerated.{u, w}} (f : X ⟶ Y) :
    List.TFAE
      [∃ (R : CompactlyGenerated.{u, w}) (s t : R ⟶ X) (c : coequalizer s t ≅ Y),
          coequalizer.π s t ≫ c.hom = f,
        Nonempty (IsColimit (Cofork.ofπ f (pullback.condition :
          pullback.fst f f ≫ f = pullback.snd f f ≫ f))),
        IsQuotientMap f] := by
  sorry

/-- Paper: Remark E.1.2.15, p. 841.
Every submersive map in `CG` is a regular epimorphism (and conversely). -/
theorem isRegularEpi_iff_isQuotientMap_compactlyGenerated {X Y : CompactlyGenerated.{u, w}}
    (f : X ⟶ Y) :
    IsRegularEpi f ↔ IsQuotientMap f := by
  sorry

section Example16

/-- Paper: Example E.1.2.16, p. 842.
The four-point space `X = {1, 2, 3, 4}` with open sets `{∅, {1, 2}, X}`. -/
def Ex16X : Type w :=
  WithTopology (ULift.{w} (Fin 4))
    (generateFrom { {x : ULift.{w} (Fin 4) | x.down = 0 ∨ x.down = 1} })

instance instTopologicalSpaceEx16X : TopologicalSpace Ex16X.{w} :=
  inferInstanceAs
    (TopologicalSpace (WithTopology (ULift.{w} (Fin 4))
      (generateFrom { {x : ULift.{w} (Fin 4) | x.down = 0 ∨ x.down = 1} })))

/-- Paper: Example E.1.2.16, p. 842.
The three-point space `Y = {a, b, c}` with the indiscrete topology `{∅, Y}`. -/
def Ex16Y : Type w :=
  WithTopology (ULift.{w} (Fin 3)) ⊤

instance instTopologicalSpaceEx16Y : TopologicalSpace Ex16Y.{w} :=
  inferInstanceAs (TopologicalSpace (WithTopology (ULift.{w} (Fin 3)) ⊤))

/-- Paper: Example E.1.2.16, p. 842.
The three-point space `Z = {α, β, γ}` with open sets `{∅, {α, β}, Z}`. -/
def Ex16Z : Type w :=
  WithTopology (ULift.{w} (Fin 3))
    (generateFrom { {z : ULift.{w} (Fin 3) | z.down = 0 ∨ z.down = 1} })

instance instTopologicalSpaceEx16Z : TopologicalSpace Ex16Z.{w} :=
  inferInstanceAs
    (TopologicalSpace (WithTopology (ULift.{w} (Fin 3))
      (generateFrom { {z : ULift.{w} (Fin 3) | z.down = 0 ∨ z.down = 1} })))

theorem uCompactlyGeneratedSpace_ex16X : UCompactlyGeneratedSpace.{u} Ex16X.{w} := by
  sorry

theorem uCompactlyGeneratedSpace_ex16Y : UCompactlyGeneratedSpace.{u} Ex16Y.{w} := by
  sorry

theorem uCompactlyGeneratedSpace_ex16Z : UCompactlyGeneratedSpace.{u} Ex16Z.{w} := by
  sorry

/-- Paper: Example E.1.2.16, p. 842.
The finite spaces `Ex16X`, `Ex16Y`, `Ex16Z` as objects of `CompactlyGenerated.{u, w}`. -/
noncomputable def ex16XCG : CompactlyGenerated.{u, w} :=
  @CompactlyGenerated.of Ex16X.{w} _ uCompactlyGeneratedSpace_ex16X

noncomputable def ex16YCG : CompactlyGenerated.{u, w} :=
  @CompactlyGenerated.of Ex16Y.{w} _ uCompactlyGeneratedSpace_ex16Y

noncomputable def ex16ZCG : CompactlyGenerated.{u, w} :=
  @CompactlyGenerated.of Ex16Z.{w} _ uCompactlyGeneratedSpace_ex16Z

def ex16FFun : Ex16X.{w} → Ex16Y.{w} := fun x =>
  WithTopology.toTopology _ <| ULift.up <|
    match x.ofTopology.down with
    | 0 => 0
    | 1 => 1
    | 2 => 1
    | 3 => 2

def ex16GFun : Ex16Z.{w} → Ex16Y.{w} := fun z =>
  WithTopology.toTopology _ <| ULift.up <|
    match z.ofTopology.down with
    | 0 => 0
    | 1 => 2
    | 2 => 2

theorem continuous_ex16F : Continuous (ex16FFun.{w}) := by
  sorry

theorem continuous_ex16G : Continuous (ex16GFun.{w}) := by
  sorry

/-- Paper: Example E.1.2.16, p. 842.
The map `f : X → Y` sending `1 ↦ a`, `2, 3 ↦ b`, `4 ↦ c`. -/
noncomputable def ex16F : ex16XCG.{u, w} ⟶ ex16YCG.{u, w} :=
  @CompactlyGenerated.ofHom Ex16X.{w} _ uCompactlyGeneratedSpace_ex16X
    Ex16Y.{w} _ uCompactlyGeneratedSpace_ex16Y ⟨ex16FFun, continuous_ex16F⟩

/-- Paper: Example E.1.2.16, p. 842.
The map `g : Z → Y` sending `α ↦ a`, `β, γ ↦ c`. -/
noncomputable def ex16G : ex16ZCG.{u, w} ⟶ ex16YCG.{u, w} :=
  @CompactlyGenerated.ofHom Ex16Z.{w} _ uCompactlyGeneratedSpace_ex16Z
    Ex16Y.{w} _ uCompactlyGeneratedSpace_ex16Y ⟨ex16GFun, continuous_ex16G⟩

/-- Paper: Example E.1.2.16, p. 842.
In Example E.1.2.16, `f : X → Y` is submersive (`IsQuotientMap`), the topological fibre product
`cgTopPullback ex16F ex16G` computes the fibre product in `CG`, and the base-changed projection
onto `Z` is not submersive.
Deviation: The paper calls `f_Z : P → Z` "the first projection"; in `Limits.pullback f g` it is
the second projection `pullback.snd ex16F ex16G`. -/
theorem example_E_1_2_16 :
    IsQuotientMap ex16F.{u, w} ∧
      ¬ IsQuotientMap (pullback.snd ex16F.{u, w} ex16G.{u, w}) ∧
      ¬ IsQuotientMap (TopCat.pullbackSnd
        (CompactlyGenerated.compactlyGeneratedToTop.map ex16F.{u, w})
        (CompactlyGenerated.compactlyGeneratedToTop.map ex16G.{u, w})) ∧
      Nonempty (cgTopPullback ex16F.{u, w} ex16G.{u, w} ≅
        CompactlyGenerated.compactlyGeneratedToTop.obj (pullback ex16F.{u, w} ex16G.{u, w})) := by
  sorry

end Example16

/-- Paper: Lemma E.1.2.17, p. 842.
The categorical product `(f, g) : X ⨯ Y ⟶ X' ⨯ Y'` in `CG` of two submersive maps is
submersive. -/
theorem isQuotientMap_prod_map_compactlyGenerated
    {X Y X' Y' : CompactlyGenerated.{u, w}} {f : X ⟶ X'} {g : Y ⟶ Y'}
    (hf : IsQuotientMap f) (hg : IsQuotientMap g) :
    IsQuotientMap (Limits.prod.map f g) := by
  sorry

section Example18

/-- Paper: Example E.1.2.18, p. 842.
Equivalence relation on `ℚ` identifying `ℤ ⊂ ℚ` to a single point (`0`). -/
def ratQuotIntSetoid : Setoid ℚ where
  r x y := x = y ∨ ((∃ m : ℤ, (m : ℚ) = x) ∧ (∃ n : ℤ, (n : ℚ) = y))
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := by
        rintro x y (rfl | ⟨hx, hy⟩)
        · exact Or.inl rfl
        · exact Or.inr ⟨hy, hx⟩
      trans := by
        rintro x y z (rfl | ⟨hx, hy⟩) (rfl | ⟨hy', hz⟩)
        · exact Or.inl rfl
        · exact Or.inr ⟨hy', hz⟩
        · exact Or.inr ⟨hx, hy⟩
        · exact Or.inr ⟨hx, hz⟩ }

/-- Paper: Example E.1.2.18, p. 842.
The quotient map `ℚ → ℚ / ℤ` identifying the integers to a point is submersive, whereas the
topological product map `(f, id) : ℚ ×₀ ℚ → (ℚ / ℤ) ×₀ ℚ` is not submersive. -/
theorem isQuotientMap_ratQuotInt :
    IsQuotientMap (Quotient.mk ratQuotIntSetoid) := by
  sorry

/-- Paper: Example E.1.2.18, p. 842.
The topological product map `(f, id) : ℚ ×₀ ℚ → (ℚ / ℤ) ×₀ ℚ` is not a quotient map. -/
theorem not_isQuotientMap_ratQuotInt_prodMap_id :
    ¬ IsQuotientMap (Prod.map (Quotient.mk ratQuotIntSetoid) (id : ℚ → ℚ)) := by
  sorry

end Example18

end CartesianClosedAndSubmersive

end RiemannMasullo

