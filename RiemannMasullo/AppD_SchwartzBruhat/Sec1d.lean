module

public import RiemannMasullo.Ch02_AdelicTheta.Sec1
public import RiemannMasullo.AppA_AlgebraicNT.Sec3
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.InnerProductSpace.Calculus

import RiemannMasullo.ForMathlib.RingTheory.PicardGroup

/-!
# Schwartz–Bruhat topologies on elementary groups and idele class groups

Masullo, §D.1.10, pp. 783–792.
-/

@[expose] public noncomputable section

open Bornology Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Distributions ENNReal FourierTransform NNReal NumberField.AdeleRing Real SchwartzMap

namespace RiemannMasullo

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F

section IdeleInsertion

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "SUnits" => (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)ˣ

-- TODO(paper-gap): The sentence before (D.1.10.1) includes the outside-S integer
-- factors in A_{F,S}, although the insertion formula and (A.1.5.1) separate them.

/-- Paper: (D.1.10.1), p. 783. Take units of the subring of adeles integral
outside S and include them into the global idele group.
Deviation: Appendix A's integral-outside-S subring already includes the outside
factors. The finite set records the finite part of S. -/
def integralIdeleInsertion : (integralAdelesOutside F S)ˣ →* 𝕀[F] :=
  Units.map (integralAdelesOutside F S).subtype.toMonoidHom

/-- Paper: (D.1.10.1), p. 783. An idele in the image is a unit at every finite place
outside S, and every such idele occurs.
Deviation: Sanity check on the domain of insertion, phrased using the integral
coordinates of an idele and its inverse. -/
theorem mem_range_integralIdeleInsertion (g : 𝕀[F]) :
    g ∈ range (integralIdeleInsertion F S) ↔
      ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
        g.val.2 v ∈ v.adicCompletionIntegers F ∧
          g.inv.2 v ∈ v.adicCompletionIntegers F := by
  have hmem (a : 𝔸[F]) :
      a ∈ integralAdelesOutside F S ↔
        ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → a.2 v ∈ v.adicCompletionIntegers F := by
    simp only [integralAdelesOutside, Subring.mem_iInf]
    rfl
  constructor
  · rintro ⟨u, rfl⟩ v hv
    exact ⟨(hmem _).mp u.val.property v hv, (hmem _).mp u.inv.property v hv⟩
  · intro hg
    let u : (integralAdelesOutside F S)ˣ :=
      ⟨⟨g.val, (hmem _).mpr fun v hv ↦ (hg v hv).1⟩,
        ⟨g.inv, (hmem _).mpr fun v hv ↦ (hg v hv).2⟩,
        Subtype.ext g.val_inv, Subtype.ext g.inv_val⟩
    exact ⟨u, Units.ext rfl⟩

/-- Paper: Lemma D.1.10.1(1), p. 784. Insertion from the full S-stage is a continuous
injective open map. -/
theorem integralIdeleInsertion_isOpenEmbedding :
    IsOpenEmbedding (integralIdeleInsertion F S) := by
  have hopen : IsOpen (integralAdelesOutside F S : Set 𝔸[F]) := by
    simp only [integralAdelesOutside, Subring.coe_iInf, Set.iInter_ofPred]
    exact (RestrictedProduct.isOpen_forall_imp_mem
      (R := fun v : HeightOneSpectrum (𝓞 F) ↦ v.adicCompletion F)
      (A := fun v ↦ v.adicCompletionIntegers F)
      (fun v ↦ Valued.isOpen_valuationSubring (v.adicCompletion F))
      (p := fun v ↦ v ∉ S)).preimage continuous_snd
  have h := hopen.isOpenEmbedding_subtypeVal
  have he : IsEmbedding (integralIdeleInsertion F S) := h.isEmbedding.units_map
  have ho : IsOpenMap (integralIdeleInsertion F S) :=
    Units.isOpenMap_map h.injective h.isOpenMap
  exact ⟨he, ho.isOpen_range⟩

/-- Paper: Lemma D.1.10.1(1), p. 784. The diagonal S-unit actions on the stage and
on the global ideles are continuous, and insertion intertwines left translation.
Deviation: The target diagonal is evaluated by mapping S-units to F-units. -/
theorem integralIdeleInsertion_equivariant :
    letI : TopologicalSpace SUnits := ⊥
    let d := Units.map (integralAdeleDiagonal F S).toMonoidHom
    let e := (IdeleGroup.unitEmbedding (𝓞 F) F).comp
      (Units.map (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F).val.toRingHom.toMonoidHom)
    Continuous (fun x : SUnits × (integralAdelesOutside F S)ˣ ↦ d x.1 * x.2) ∧
    Continuous (fun x : SUnits × 𝕀[F] ↦ e x.1 * x.2) ∧
    ∀ u g, integralIdeleInsertion F S (d u * g) =
      e u * integralIdeleInsertion F S g := by
  let : TopologicalSpace SUnits := ⊥
  let : DiscreteTopology SUnits := discreteTopology_bot _
  intro d e
  have hd : Continuous d := continuous_of_discreteTopology
  have he : Continuous e := continuous_of_discreteTopology
  refine ⟨(hd.comp continuous_fst).mul continuous_snd,
    (he.comp continuous_fst).mul continuous_snd, ?_⟩
  intro u g
  rw [map_mul]
  exact congrArg (· * integralIdeleInsertion F S g) (Units.ext rfl)

-- TODO(paper-gap): D.1.10.1(2) names only GL₁(A_{F,S}). With the finite-product
-- convention of (A.1.5.1), inserting 1 off S misses ideles with infinitely many
-- nonidentity unit coordinates. The colimit below uses the full stages of (D.1.10.1).

/-- Paper: Lemma D.1.10.1(2), p. 784. Images of the full S-stages increase
with S and exhaust the global ideles.
Deviation: The source is the full stage in (D.1.10.1), with the outside local units. -/
theorem integralIdeleInsertion_exhaustive :
    Monotone (fun T : Finset (HeightOneSpectrum (𝓞 F)) ↦
      range (integralIdeleInsertion F T)) ∧
    ∀ g : 𝕀[F], ∃ T, g ∈ range (integralIdeleInsertion F T) := by
  constructor
  · intro U T hUT g hg
    apply (mem_range_integralIdeleInsertion F T g).2
    intro v hv
    exact (mem_range_integralIdeleInsertion F U g).1 hg v (fun h ↦ hv (hUT h))
  · intro g
    have hfinite := Filter.eventually_cofinite.mp
      (g.val.2.cofinite_mem_adicCompletionIntegers.and
        g.inv.2.cofinite_mem_adicCompletionIntegers)
    refine ⟨hfinite.toFinset, (mem_range_integralIdeleInsertion F _ g).2 ?_⟩
    intro v hv
    exact not_not.mp (fun h ↦ hv (hfinite.mem_toFinset.mpr h))

/- The subring of adeles integral outside a finite set of finite places is open,
being the product of the infinite adeles with the cofinite distinguished sets of
the finite adeles. Used to make each full stage an open subgroup of the ideles. -/
private theorem isOpen_integralAdelesOutside (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (integralAdelesOutside F S : Set 𝔸[F]) := by
  simp only [integralAdelesOutside, Subring.coe_iInf, Set.iInter_ofPred]
  exact (isOpen_restrictedProduct_forall_mem (↑S : Set (HeightOneSpectrum (𝓞 F)))ᶜ
    (fun v _ ↦ Valued.isOpen_integer (v.adicCompletion F))).preimage continuous_snd

/- The insertion from the full stage into the ideles is continuous, injective and open
onto its image, and its image is the open set of ideles integral outside `S` with
integral inverse (helper for Lemma D.1.10.1(1), p. 784, and (2), p. 784). -/
private theorem integralIdeleInsertion_continuous_aux (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (integralIdeleInsertion F S) :=
  Units.continuous_map continuous_subtype_val

private theorem integralIdeleInsertion_isOpenEmbedding_aux
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpenEmbedding (integralIdeleInsertion F S) := by
  have hemb : IsEmbedding ((integralAdelesOutside F S).subtype.toMonoidHom) :=
    Topology.IsEmbedding.subtypeVal
  exact IsOpenEmbedding.of_isEmbedding_isOpenMap
    (Topology.IsEmbedding.units_map hemb)
    (Units.isOpenMap_map hemb.injective
      ((isOpen_integralAdelesOutside F S).isOpenEmbedding_subtypeVal.isOpenMap))

private theorem isOpen_range_integralIdeleInsertion_aux
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (Set.range (integralIdeleInsertion F S)) := by
  have hmem (a : 𝔸[F]) : a ∈ integralAdelesOutside F S ↔
      ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → a.2 v ∈ v.adicCompletionIntegers F := by
    simp only [integralAdelesOutside, Subring.mem_iInf]
    rfl
  have heq : Set.range (integralIdeleInsertion F S) =
      (fun g : 𝕀[F] ↦ g.val) ⁻¹' (integralAdelesOutside F S : Set 𝔸[F]) ∩
        (fun g : 𝕀[F] ↦ g.inv) ⁻¹' (integralAdelesOutside F S : Set 𝔸[F]) := by
    ext g
    rw [mem_inter_iff, mem_preimage, mem_preimage, mem_range_integralIdeleInsertion F S g]
    constructor
    · intro h
      exact ⟨(hmem _).mpr fun v hv ↦ (h v hv).1, (hmem _).mpr fun v hv ↦ (h v hv).2⟩
    · intro h v hv
      exact ⟨(hmem _).mp h.1 v hv, (hmem _).mp h.2 v hv⟩
  rw [heq]
  exact ((isOpen_integralAdelesOutside F S).preimage Units.continuous_val).inter
    ((isOpen_integralAdelesOutside F S).preimage Units.continuous_coe_inv)

/- Every idele is integral outside a finite set of finite places with integral inverse,
so it lies in the image of the insertion from that stage (helper for the exhaustiveness
part of Lemma D.1.10.1(2), p. 784). -/
private theorem integralIdeleInsertion_exhaustive_aux (g : 𝕀[F]) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), g ∈ Set.range (integralIdeleInsertion F T) := by
  classical
  have hboth : ∀ᶠ v in Filter.cofinite,
      g.val.2 v ∈ v.adicCompletionIntegers F ∧ g.inv.2 v ∈ v.adicCompletionIntegers F := by
    filter_upwards [g.val.2.2, g.inv.2.2] with v h1 h2
    exact ⟨h1, h2⟩
  have hfin := Filter.eventually_cofinite.mp hboth
  refine ⟨hfin.toFinset, ?_⟩
  rw [mem_range_integralIdeleInsertion]
  intro v hv
  rw [hfin.mem_toFinset] at hv
  simp only [mem_setOf_eq, not_not] at hv
  exact hv

/-- Paper: Lemma D.1.10.1(2), p. 784. The topology on the union of the full S-stages
is final for their insertions. Their transition maps are the inclusions of the images.
Deviation: The source is the full stage in (D.1.10.1), with the outside local units. -/
theorem integralIdeleInsertion_finalTopology (U : Set 𝕀[F]) :
    IsOpen U ↔ ∀ T : Finset (HeightOneSpectrum (𝓞 F)),
      IsOpen (integralIdeleInsertion F T ⁻¹' U) := by
  constructor
  · intro hU T
    exact hU.preimage (integralIdeleInsertion_continuous_aux F T)
  · intro h
    have heq : U = ⋃ T : Finset (HeightOneSpectrum (𝓞 F)),
        integralIdeleInsertion F T '' (integralIdeleInsertion F T ⁻¹' U) := by
      ext g
      simp only [mem_iUnion, mem_image, mem_preimage]
      constructor
      · intro hg
        obtain ⟨T, hu⟩ := integralIdeleInsertion_exhaustive_aux F g
        obtain ⟨u, rfl⟩ := hu
        exact ⟨T, u, mem_preimage.mpr hg, rfl⟩
      · rintro ⟨T, u, hu, rfl⟩
        exact hu
    rw [heq]
    exact isOpen_iUnion fun T ↦
      IsOpenEmbedding.isOpenMap (integralIdeleInsertion_isOpenEmbedding_aux F T)
        (integralIdeleInsertion F T ⁻¹' U) (h T)

/-- Paper: (D.1.10.2), p. 784. The composite of insertion with the global class map
kills the diagonal S-units. -/
theorem integralIdeleInsertion_descends :
    (Units.map (integralAdeleDiagonal F S).toMonoidHom).range ≤
      ((QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)).comp
        (integralIdeleInsertion F S)).ker := by
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  rintro _ ⟨u, rfl⟩
  exact ⟨Units.map (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F).val.toRingHom.toMonoidHom u,
    Units.ext rfl⟩

/-- Paper: (D.1.10.2), p. 784. Insert an S-idele representative and take its global
idele class. The source is Appendix A's S-idele class group. -/
def sIdeleClassInsertion : SIdeleClassGroup F S →* C[F] :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)).comp
      (integralIdeleInsertion F S)) (integralIdeleInsertion_descends F S)

/-- Paper: (D.1.10.2), p. 784. The class insertion is determined by insertion on
representatives.
Deviation: Sanity check stated as the unique descent of the representative map. -/
theorem sIdeleClassInsertion_unique :
    (∀ u : (integralAdelesOutside F S)ˣ,
      sIdeleClassInsertion F S (QuotientGroup.mk u) =
        QuotientGroup.mk (integralIdeleInsertion F S u)) ∧
    ∀ j : SIdeleClassGroup F S →* C[F],
      (∀ u : (integralAdelesOutside F S)ˣ,
        j (QuotientGroup.mk u) = QuotientGroup.mk (integralIdeleInsertion F S u)) →
      j = sIdeleClassInsertion F S :=
  ⟨fun _ ↦ rfl, fun _ hj ↦ QuotientGroup.monoidHom_ext _ (MonoidHom.ext hj)⟩

/-- Paper: Lemma D.1.10.1(3), p. 784. The induced map of class groups is
continuous, injective and open. -/
theorem sIdeleClassInsertion_isOpenEmbedding : IsOpenEmbedding (sIdeleClassInsertion F S) := by
  let D := (Units.map (integralAdeleDiagonal F S).toMonoidHom).range
  let P := IdeleGroup.principalSubgroup (𝓞 F) F
  have hsource := QuotientGroup.isOpenQuotientMap_mk (N := D)
  have htarget := QuotientGroup.isOpenQuotientMap_mk (N := P)
  have hinsertion := integralIdeleInsertion_isOpenEmbedding F S
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    (hsource.continuous_comp_iff.mp (htarget.continuous.comp hinsertion.continuous)) ?_
    (hsource.isOpenMap_iff.mpr (htarget.isOpenMap.comp hinsertion.isOpenMap))
  apply (QuotientGroup.injective_lift_iff _ _ (integralIdeleInsertion_descends F S)).2
  refine le_antisymm (integralIdeleInsertion_descends F S) ?_
  intro g hg
  change (QuotientGroup.mk (s := P) (integralIdeleInsertion F S g)) = 1 at hg
  obtain ⟨u, hu⟩ := (QuotientGroup.eq_one_iff _).mp hg
  have hval : algebraMap F 𝔸[F] u.val = g.val.val := congrArg Units.val hu
  have hinv : algebraMap F 𝔸[F] u.inv = g.inv.val := congrArg Units.inv hu
  -- The diagonal field element and its inverse are both S-integers.
  let x : SUnits :=
    ⟨⟨u.val, (diagonal_mem_integralAdelesOutside F S _).mp (hval.symm ▸ g.val.property)⟩,
      ⟨u.inv, (diagonal_mem_integralAdelesOutside F S _).mp (hinv.symm ▸ g.inv.property)⟩,
      Subtype.ext u.val_inv, Subtype.ext u.inv_val⟩
  exact ⟨x, hinsertion.injective (Units.ext hval)⟩

/-- The ideal classes of ideles that are units outside S are precisely the classes
that become trivial over the S-integers. -/
private theorem map_range_integralIdeleInsertion (p : 𝕀[F] →* CommRing.Pic (𝓞 F))
    (hp : ∀ g, p g = ideleIdealClass F g) :
    (integralIdeleInsertion F S).range.map p =
      (CommRing.Pic.mapAlgebra (𝓞 F) (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)).ker := by
  classical
  let A := Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F
  let m := CommRing.Pic.mapAlgebra (𝓞 F) A
  ext c
  change c ∈ (integralIdeleInsertion F S).range.map p ↔ m c = 1
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    rw [hp]
    exact sIdele_ideal_class_trivial F S u
  · intro hc
    have h := picard_localization_exact F ∅ S (Finset.empty_subset S)
    dsimp only at h
    rw [Finset.sdiff_empty] at h
    obtain ⟨j, _, hexact, _, hj⟩ := h
    let A₀ := Set.integer
      ((∅ : Finset (HeightOneSpectrum (𝓞 F))) : Set (HeightOneSpectrum (𝓞 F))) F
    let m₀ := CommRing.Pic.mapAlgebra (𝓞 F) A₀
    have hc₀ := hc
    unfold m at hc₀
    rw [← CommRing.Pic.mapRingHom_algebraMap] at hc₀
    obtain ⟨z, hz⟩ := (hexact (m₀ c)).mp (by
      rw [show m₀ c = CommRing.Pic.mapRingHom (algebraMap (𝓞 F) A₀) c by
        rw [CommRing.Pic.mapRingHom_algebraMap],
        CommRing.Pic.mapRingHom_mapRingHom]
      exact hc₀)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    choose x hx using fun v : S ↦ QuotientGroup.mk_surjective (y v)
    have hy : (fun v : S ↦ QuotientGroup.mk (x v)) = y := funext hx
    rw [← hy, hj] at hz
    let a (v : S) := IdeleGroup.ofAdicCompletion (𝓞 F) F v.val (x v)
    have ha (v : S) : a v ∈ (integralIdeleInsertion F S).range := by
      apply (mem_range_integralIdeleInsertion F S _).mpr
      intro w hw
      have hne : w ≠ v.val := fun e ↦ hw (e.symm ▸ v.property)
      constructor
      · change Pi.mulSingle v.val (x v).val w ∈ w.adicCompletionIntegers F
        rw [Pi.mulSingle_eq_of_ne hne]
        exact one_mem _
      · change ((a v)⁻¹).val.2 w ∈ w.adicCompletionIntegers F
        dsimp only [a]
        rw [← map_inv]
        change Pi.mulSingle v.val ((x v)⁻¹).val w ∈ w.adicCompletionIntegers F
        rw [Pi.mulSingle_eq_of_ne hne]
        exact one_mem _
    refine ⟨∏ v, a v, (integralIdeleInsertion F S).range.prod_mem (fun v _ ↦ ha v), ?_⟩
    rw [map_prod]
    calc
      (∏ v, p (a v)) = ∏ v, localIdealClass F v.val (x v) :=
        Finset.prod_congr rfl fun v _ ↦ (hp _).trans (ideleIdealClass_ofAdicCompletion F _ _)
      _ = c := by
        -- The base change to the empty stage is injective: its integer ring is the base ring.
        have hA : A₀ = ⊥ := by simp [A₀]
        let e := (Subalgebra.equivOfEq _ _ hA).trans
          (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 F) F))
        have he : e.toRingHom.comp (algebraMap (𝓞 F) _) = RingHom.id (𝓞 F) :=
          RingHom.ext fun r ↦ (e.commutes r).trans (Algebra.algebraMap_self_apply r)
        have hleft : LeftInverse (CommRing.Pic.mapRingHom e.toRingHom) m₀ := by
          intro d
          dsimp only [m₀]
          rw [← CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapRingHom_mapRingHom,
            he, CommRing.Pic.mapRingHom_id_apply]
        exact hleft.injective hz

/-- Paper: Lemma D.1.10.1(3), p. 784. The quotient by the image of the S-idele
classes is isomorphic to the finite Picard group of the S-integer ring. -/
theorem sIdeleClassInsertion_cokernel :
    Nonempty ((C[F] ⧸ (sIdeleClassInsertion F S).range) ≃*
      CommRing.Pic (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)) ∧
    Finite (C[F] ⧸ (sIdeleClassInsertion F S).range) := by
  let P := IdeleGroup.principalSubgroup (𝓞 F) F
  let U := (integralIdeleInsertion F S).range
  let A := Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F
  let m := CommRing.Pic.mapAlgebra (𝓞 F) A
  let : TopologicalSpace (CommRing.Pic (𝓞 F)) := ⊥
  obtain ⟨p, hp, _, hexact, hquot⟩ := idele_ideal_class_exact F
  have hpker : p.ker = P ⊔ (integralIdeleInsertion F ∅).range := by
    rw [hexact.monoidHom_ker_eq, Subgroup.range_subtype]
    rfl
  have hU : (integralIdeleInsertion F ∅).range ≤ U :=
    (integralIdeleInsertion_exhaustive F).1 (Finset.empty_subset S)
  have hk : (m.comp p).ker = P ⊔ U := by
    rw [← MonoidHom.comap_ker, ← map_range_integralIdeleInsertion F S p hp,
      Subgroup.comap_map_eq, hpker, ← sup_left_comm, sup_eq_left.mpr hU, sup_comm]
  have hP : P ≤ (m.comp p).ker := hk.symm ▸ le_sup_left
  let q := QuotientGroup.lift P (m.comp p) hP
  have hq : Surjective q := QuotientGroup.lift_surjective_of_surjective P _
    ((picMapAlgebra_surjective_of_isLocalization
      (Localization.submonoid (S : Set (HeightOneSpectrum (𝓞 F)))) A).comp hquot.surjective) hP
  have hker : (sIdeleClassInsertion F S).range = q.ker := by
    change (sIdeleClassInsertion F S).range = (QuotientGroup.lift P (m.comp p) hP).ker
    rw [QuotientGroup.ker_lift, hk, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    change (sIdeleClassInsertion F S).range = (integralIdeleInsertion F S).range.map _
    rw [← MonoidHom.range_comp]
    change (sIdeleClassInsertion F S).range =
      ((sIdeleClassInsertion F S).comp (QuotientGroup.mk' _)).range
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
      Subgroup.map_top]
  let e := QuotientGroup.liftEquiv _ hq hker
  have : Finite (CommRing.Pic A) := (sIdeleClassGroup_finiteness F S).2.2.2.2.2
  exact ⟨⟨e⟩, Finite.of_injective e e.injective⟩

/-- Paper: Lemma D.1.10.1(3), p. 784. Insertion restricts to a topological
group isomorphism between the identity components. -/
theorem sIdeleClassInsertion_connectedComponent :
    ∃ e : Subgroup.connectedComponentOfOne (SIdeleClassGroup F S) ≃ₜ*
        Subgroup.connectedComponentOfOne C[F],
      ∀ x, (e x).val = sIdeleClassInsertion F S x.val := by
  let f := sIdeleClassInsertion F S
  let A := Subgroup.connectedComponentOfOne (SIdeleClassGroup F S)
  let B := Subgroup.connectedComponentOfOne C[F]
  have hf : IsOpenEmbedding f := sIdeleClassInsertion_isOpenEmbedding F S
  have hrange : IsClopen (f.range : Set C[F]) :=
    ⟨f.range.isClosed_of_isOpen hf.isOpen_range, hf.isOpen_range⟩
  have hB : (B : Set C[F]) ⊆ range f := hrange.connectedComponent_subset f.range.one_mem
  have hpre : IsPreconnected (f ⁻¹' (B : Set C[F])) := by
    apply hf.isEmbedding.isInducing.isPreconnected_image.mp
    rw [image_preimage_eq_of_subset hB]
    exact isPreconnected_connectedComponent
  have hpreA : f ⁻¹' (B : Set C[F]) ⊆ A :=
    hpre.subset_connectedComponent (show f 1 ∈ B from (map_one f).symm ▸ B.one_mem)
  have hmap (x : A) : f x.val ∈ B := by
    change f x.val ∈ connectedComponent (1 : C[F])
    simpa only [map_one] using hf.continuous.mapsTo_connectedComponent 1 x.property
  let g : A →* B := (f.comp A.subtype).codRestrict B hmap
  have hg : IsEmbedding g :=
    (hf.isEmbedding.comp IsEmbedding.subtypeVal).codRestrict (B : Set C[F]) hmap
  have hsurj : Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hB y.property
    exact ⟨⟨x, hpreA (show f x ∈ B from hx.symm ▸ y.property)⟩, Subtype.ext hx⟩
  let e := MulEquiv.ofBijective g ⟨hg.injective, hsurj⟩
  exact ⟨{ e, e.toEquiv.toHomeomorphOfIsInducing hg.isInducing with }, fun _ ↦ rfl⟩

/-- Paper: Lemma D.1.10.1(3), p. 784. For all sufficiently large finite sets the
insertion is surjective, and hence is an isomorphism by openness and injectivity. -/
theorem sIdeleClassInsertion_eventually_surjective :
    ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ U, T ⊆ U →
      Surjective (sIdeleClassInsertion F U) := by
  classical
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
  let stage (U : Finset (HeightOneSpectrum (𝓞 F))) := (sIdeleClassInsertion F U).range
  have hstage (U : Finset (HeightOneSpectrum (𝓞 F))) :
      (stage U : Set C[F]) = q '' range (integralIdeleInsertion F U) := by
    ext c
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ x
      exact ⟨_, ⟨u, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨QuotientGroup.mk u, rfl⟩
  obtain ⟨hmono, hexhaust⟩ := integralIdeleInsertion_exhaustive F
  have hmonotone : Monotone (fun U ↦ (stage U : Set C[F])) := by
    intro U V hUV
    change (stage U : Set C[F]) ⊆ stage V
    rw [hstage U, hstage V]
    exact image_mono (hmono hUV)
  have hcover (c : C[F]) : c ∈ ⋃ U, (stage U : Set C[F]) := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ c
    obtain ⟨U, hg⟩ := hexhaust g
    exact mem_iUnion.mpr ⟨U, (hstage U).symm ▸ mem_image_of_mem q hg⟩
  have hcompact : IsCompact ((ideleClassNorm F).ker : Set C[F]) :=
    isCompact_iff_compactSpace.mpr (ideleClassGroup_finiteness F).2.1
  obtain ⟨T, hT⟩ := hcompact.elim_directed_cover (fun U ↦ (stage U : Set C[F]))
    (fun U ↦ (sIdeleClassInsertion_isOpenEmbedding F U).isOpen_range)
    (fun c _ ↦ hcover c)
    (fun U V ↦ ⟨U ∪ V, hmonotone Finset.subset_union_left, hmonotone Finset.subset_union_right⟩)
  refine ⟨T, fun U hTU c ↦ ?_⟩
  obtain ⟨j, _, hjNorm, hjRep⟩ := sIdeleClassGroup_openEmbedding F U
  have hj : j = sIdeleClassInsertion F U := (sIdeleClassInsertion_unique F U).2 j hjRep
  obtain ⟨x, hx⟩ := (sIdeleClassNorm_descent F U).2.2.2.1 (ideleClassNorm F c)
  have hxc : ideleClassNorm F (j x) = ideleClassNorm F c := (hjNorm x).trans hx
  have hdiv : c / j x ∈ (ideleClassNorm F).ker := by
    rw [MonoidHom.mem_ker, map_div, hxc, div_self']
  have hmem : c / j x ∈ stage U := hmonotone hTU (hT hdiv)
  have hxmem : j x ∈ stage U := by
    rw [hj]
    exact ⟨x, rfl⟩
  exact div_mul_cancel c (j x) ▸ (stage U).mul_mem hmem hxmem

end IdeleInsertion

section SchwartzTopologies

/-- Paper: Proposition D.1.10.2, p. 784. A family of extended values generates
the topology when its values are exactly those of real generating seminorms.
Deviation: This common formulation also records finiteness of all the values. -/
def GeneratesSeminormTopology {E ι : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (v : ι → E → ℝ≥0∞) : Prop :=
  ∃ P : ι → Seminorm ℂ E, WithSeminorms P ∧ ∀ i f, ENNReal.ofReal (P i f) = v i f

/-- Paper: Proposition D.1.10.2, p. 784. Boundedness is equivalent to an upper bound
for the values of each generating seminorm on the set.
Deviation: Sanity check on the topology formulation, stated with finite bounds. -/
theorem GeneratesSeminormTopology.isVonNBounded_iff
    {E ι : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {v : ι → E → ℝ≥0∞} (hv : GeneratesSeminormTopology v) (B : Set E) :
    IsVonNBounded ℂ B ↔ ∀ i, ∃ C : ℝ≥0, ∀ f ∈ B, v i f ≤ (C : ℝ≥0∞) := by
  obtain ⟨P, hP, hvalues⟩ := hv
  simp_rw [hP.isVonNBounded_iff_seminorm_bounded, ← hvalues, ENNReal.ofReal_le_coe]
  constructor
  · intro h i
    obtain ⟨r, hr, hbound⟩ := h i
    exact ⟨⟨r, hr.le⟩, fun f hf ↦ (hbound f hf).le⟩
  · intro h i
    obtain ⟨C, hbound⟩ := h i
    exact ⟨(C : ℝ) + 1, by positivity, fun f hf ↦ lt_of_le_of_lt (hbound f hf) (lt_add_one _)⟩

/-- Paper: Proposition D.1.10.2, p. 784. A family of function transforms gives a
generating Lᵖ family if the transforms belong to Lᵖ and their norms generate the topology.
Deviation: Membership is explicit so the extended norm cannot hide a measurability
or integrability condition. -/
def GeneratesLpSeminorms {E ι X : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [MeasurableSpace X] (μ : Measure X) (p : ℝ≥0∞)
    (u : ι → E → X → ℂ) : Prop :=
  (∀ i f, MemLp (u i f) p μ) ∧
    GeneratesSeminormTopology (fun i f ↦ eLpNorm (u i f) p μ)

/-- Paper: Proposition D.1.10.2, p. 784. Bounds on each Lᵖ norm characterize
bounded sets when the Lᵖ family generates.
Deviation: Sanity check stated in terms of the actual extended norms. -/
theorem GeneratesLpSeminorms.isVonNBounded_iff
    {E ι X : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [MeasurableSpace X] {μ : Measure X} {p : ℝ≥0∞} {u : ι → E → X → ℂ}
    (h : GeneratesLpSeminorms μ p u) (B : Set E) :
    IsVonNBounded ℂ B ↔
      ∀ i, ∃ C : ℝ≥0, ∀ f ∈ B, eLpNorm (u i f) p μ ≤ (C : ℝ≥0∞) := by
  exact h.2.isVonNBounded_iff B

/-- Paper: (D.1.10.3), p. 784. Apply the nth derivative, Fourier transform,
and then apply the mth derivative. -/
def realSchwartzFourierDeriv (m n : ℕ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (SchwartzMap.derivCLM ℂ ℂ)^[m] (𝓕 ((SchwartzMap.derivCLM ℂ ℂ)^[n] f))

/-- Paper: (D.1.10.3), p. 784. With both differentiation orders zero only
the Fourier transform remains.
Deviation: Sanity check on the differential orders. -/
theorem realSchwartzFourierDeriv_zero (f : 𝓢(ℝ, ℂ)) :
    realSchwartzFourierDeriv 0 0 f = 𝓕 f := by
  rfl

section RealSchwartzFourierLp

open LineDeriv MeasureTheory.Measure SchwartzMap Complex Filter

/-! ### Iterated derivative and monomial multiplication on the real Schwartz space -/

/-- The `n`-th iterated derivative of a Schwartz map is the `n`-th iterated derivative
of its underlying function. -/
private theorem coe_derivIterate (f : 𝓢(ℝ, ℂ)) (n : ℕ) (x : ℝ) :
    ((SchwartzMap.derivCLM ℂ ℂ)^[n] f : ℝ → ℂ) x = iteratedDeriv n (f : ℝ → ℂ) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hfun : ((SchwartzMap.derivCLM ℂ ℂ)^[n] f : ℝ → ℂ) =
        iteratedDeriv n (f : ℝ → ℂ) := funext ih
    rw [Function.iterate_succ_apply', SchwartzMap.derivCLM_apply, hfun, iteratedDeriv_succ]

/-- Iterating the multiplication-by-`x` operator gives multiplication by `x ^ j`. -/
private theorem smulLeftIterate (j : ℕ) (h : 𝓢(ℝ, ℂ)) :
    (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[j] h =
      SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ j) h := by
  induction j with
  | zero =>
    have h1 : (fun x : ℝ ↦ (x : ℂ) ^ 0) = (fun _ : ℝ ↦ (1 : ℂ)) := by funext x; simp
    rw [h1, SchwartzMap.smulLeftCLM_const]
    simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    have hgrowth : (fun x : ℝ ↦ (x : ℂ) ^ j).HasTemperateGrowth := by fun_prop
    have hgrowth1 : (fun x : ℝ ↦ (x : ℂ)).HasTemperateGrowth := by fun_prop
    have heq : ((fun x : ℝ ↦ (x : ℂ)) * (fun x : ℝ ↦ (x : ℂ) ^ j)) =
        fun x : ℝ ↦ (x : ℂ) ^ (j + 1) := by
      funext x; simp [pow_succ, mul_comm]
    rw [SchwartzMap.smulLeftCLM_smulLeftCLM_apply hgrowth1 hgrowth, heq]

/-! ### The Fourier transform turns monomials into derivatives -/

/-- `∂_{1}` on one real variable is the ordinary derivative. -/
private theorem lineDerivOp_one_eq_derivCLM (u : 𝓢(ℝ, ℂ)) :
    ∂_{(1:ℝ)} u = (SchwartzMap.derivCLM ℂ ℂ) u := by
  ext1 x
  have hd : Differentiable ℝ (u : ℝ → ℂ) := u.differentiable
  have h1 : (fderiv ℝ (u : ℝ → ℂ) x) 1 = deriv (u : ℝ → ℂ) x :=
    (hd x).hasFDerivAt.hasDerivAt.deriv
  rw [lineDerivOp_apply_eq_fderiv]
  show (fderiv ℝ (u : ℝ → ℂ) x) 1 = _
  rw [h1]
  rfl

/-- Differentiating a Fourier transform is the Fourier transform of multiplication
by `-(2 * Real.pi * I) * x`. -/
private theorem fourier_mul_step (g : 𝓢(ℝ, ℂ)) :
    (SchwartzMap.derivCLM ℂ ℂ) (𝓕 g) =
      (-(2 * Real.pi * Complex.I)) • 𝓕 ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ))) g) := by
  have hgrowth : (fun x : ℝ ↦ (x : ℂ)).HasTemperateGrowth := by fun_prop
  have hstep := SchwartzMap.fourierInv_lineDerivOp_eq (𝓕 g) (1 : ℝ)
  rw [lineDerivOp_one_eq_derivCLM] at hstep
  rw [FourierTransform.fourierInv_fourier_eq] at hstep
  have hinner : (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ inner ℝ x 1) g) =
      (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ))) g := by
    ext1 x
    rw [SchwartzMap.smulLeftCLM_apply_apply (hg := by fun_prop),
      SchwartzMap.smulLeftCLM_apply_apply (hg := hgrowth)]
    simp
  rw [hinner] at hstep
  have h2 := congrArg 𝓕 hstep
  rw [FourierTransform.fourier_fourierInv_eq, FourierTransform.fourier_smul] at h2
  exact h2

/-- One step of the commutation, in the useful direction. -/
private theorem fourier_smulLeft_step (g : 𝓢(ℝ, ℂ)) :
    𝓕 ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ))) g) =
      ((-(2 * Real.pi * Complex.I))⁻¹) • ((SchwartzMap.derivCLM ℂ ℂ) (𝓕 g)) := by
  have hc : (-(2 * Real.pi * Complex.I) : ℂ) ≠ 0 := by
    have h2pi : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 :=
      mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.2 Real.pi_pos.ne')
    exact neg_ne_zero.2 (mul_ne_zero h2pi Complex.I_ne_zero)
  rw [eq_comm, inv_smul_eq_iff₀ hc]
  exact fourier_mul_step g

/-- The Fourier transform of the `j`-fold monomial multiplication is the
`j`-fold differentiation of the Fourier transform, up to the constant
`(-(2 * Real.pi * I))⁻¹`. -/
private theorem fourier_smulLeftIterate (j : ℕ) (h : 𝓢(ℝ, ℂ)) :
    𝓕 ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[j] h) =
      ((-(2 * Real.pi * Complex.I))⁻¹ ^ j) • ((SchwartzMap.derivCLM ℂ ℂ)^[j] (𝓕 h)) := by
  induction j generalizing h with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply' (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ))) j h,
      fourier_smulLeft_step, ih, map_smul (SchwartzMap.derivCLM ℂ ℂ), smul_smul, pow_succ',
      Function.iterate_succ_apply']

/-- The Fourier transform is an isometry for the `L²` norm on Schwartz functions
(in `lpNorm` form). -/
private theorem lpNorm_fourier (h : 𝓢(ℝ, ℂ)) :
    lpNorm ((𝓕 h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) 2 volume = lpNorm (h : ℝ → ℂ) 2 volume := by
  have h2 := SchwartzMap.norm_fourier_toL2_eq h
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp] at h2
  exact h2

/-- Scalar multiplication scales the `L²` norm of a Schwartz function. -/
private theorem lpNorm_smul (c : ℂ) (h : 𝓢(ℝ, ℂ)) :
    lpNorm ((c • h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) 2 volume = ‖c‖ * lpNorm (h : ℝ → ℂ) 2 volume := by
  have hcoe : ((c • h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = c • (h : ℝ → ℂ) := by
    funext x; simp
  rw [hcoe, lpNorm, eLpNorm_const_smul, ← toReal_eLpNorm, ENNReal.toReal_mul]
  simp

/-! ### The pointwise `sup ≤ L² + L²` estimate -/

private theorem lpNorm_sq_eq_integral_norm_sq (φ : 𝓢(ℝ, ℂ)) :
    ∫ y : ℝ, ‖φ y‖ ^ 2 = (lpNorm (φ : ℝ → ℂ) 2 volume) ^ 2 := by
  have hm : AEStronglyMeasurable (φ : ℝ → ℂ) volume := φ.continuous.aestronglyMeasurable
  have hpow : (fun y : ℝ ↦ ‖φ y‖ ^ (2 : ℝ)) = fun y ↦ ‖φ y‖ ^ 2 := by
    funext y
    exact Real.rpow_natCast ‖φ y‖ 2
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hm]
  simp only [ENNReal.toReal_ofNat]
  rw [hpow]
  have hexp : ((2 : ℝ) ⁻¹) = (1 / 2 : ℝ) := by norm_num
  rw [hexp, ← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg fun _ ↦ by positivity)]

/-- A Schwartz function on the line is pointwise bounded by the L² norms of itself
and its derivative. -/
private theorem schwartz_norm_le_lpNorm_add_deriv (ψ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖ψ x‖ ≤ lpNorm (ψ : ℝ → ℂ) 2 volume +
      lpNorm ((SchwartzMap.derivCLM ℂ ℂ ψ) : ℝ → ℂ) 2 volume := by
  let d : ℝ → ℂ := SchwartzMap.derivCLM ℂ ℂ ψ
  let F : ℝ → ℝ := fun t ↦ ‖ψ t‖ ^ 2
  let F' : ℝ → ℝ := fun t ↦ 2 * inner ℝ (ψ t) (d t)
  have hd (y : ℝ) : d y = deriv (ψ : ℝ → ℂ) y := by
    simp [d]
  have hF (y : ℝ) : HasDerivAt F (F' y) y := by
    simpa [F, F', hd y] using (SchwartzMap.hasDerivAt ψ y).norm_sq
  have hsqψ : Integrable (fun y : ℝ ↦ ‖ψ y‖ ^ 2) volume := by
    have h := (ψ.memLp 2 volume).integrable_norm_rpow (by norm_num) (by norm_num)
    have hfun : (fun y : ℝ ↦ ‖ψ y‖ ^ (2 : ℝ≥0∞).toReal) = fun y ↦ ‖ψ y‖ ^ 2 := by
      funext y
      simp only [ENNReal.toReal_ofNat]
      exact Real.rpow_natCast ‖ψ y‖ 2
    simpa [hfun] using h
  have hsqd : Integrable (fun y : ℝ ↦ ‖d y‖ ^ 2) volume := by
    have h := ((SchwartzMap.derivCLM ℂ ℂ ψ).memLp 2 volume).integrable_norm_rpow
      (by norm_num) (by norm_num)
    rw [show (fun y : ℝ ↦ ‖d y‖ ^ 2) =
        fun y ↦ ‖(SchwartzMap.derivCLM ℂ ℂ ψ) y‖ ^ (2 : ℝ≥0∞).toReal by
      funext y
      simp only [ENNReal.toReal_ofNat, d]
      exact (Real.rpow_natCast ‖d y‖ 2).symm]
    exact h
  have hsumsq : Integrable (fun y : ℝ ↦ ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2) volume := hsqψ.add hsqd
  have hcs (y : ℝ) : |inner ℝ (ψ y) (d y)| ≤ ‖ψ y‖ * ‖d y‖ :=
    abs_real_inner_le_norm (ψ y) (d y)
  have hdom (y : ℝ) : ‖F' y‖ ≤ ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 := by
    have hyoung : 2 * ‖ψ y‖ * ‖d y‖ ≤ ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖ψ y‖ - ‖d y‖)]
    calc ‖F' y‖ = |2 * inner ℝ (ψ y) (d y)| := by simp [F', Real.norm_eq_abs]
      _ = 2 * |inner ℝ (ψ y) (d y)| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * (‖ψ y‖ * ‖d y‖) := mul_le_mul_of_nonneg_left (hcs y) (by norm_num)
      _ ≤ ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 := by simpa [mul_assoc] using hyoung
  have hFmeas : AEStronglyMeasurable F' volume := by
    apply Continuous.aestronglyMeasurable
    have hcψ : Continuous (fun t : ℝ ↦ (ψ t : ℂ)) := ψ.continuous
    have hcd : Continuous d := (SchwartzMap.derivCLM ℂ ℂ ψ).continuous
    exact continuous_const.mul (continuous_inner.comp (hcψ.prodMk hcd))
  have hF'int : Integrable F' volume :=
    hsumsq.mono' hFmeas (Eventually.of_forall hdom)
  have hlim : Tendsto F atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := x) (f := F) (f' := F')
      (fun y _ ↦ hF y) hF'int.integrableOn hsqψ.integrableOn
  have heq : ∫ y in Ioi x, F' y = - F x := by
    simpa using integral_Ioi_of_hasDerivAt_of_tendsto' (a := x) (f := F) (f' := F') (m := 0)
      (fun y _ ↦ hF y) hF'int.integrableOn hlim
  have hpoint (y : ℝ) : - F' y ≤ ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 :=
    (neg_le_abs _).trans (by simpa [Real.norm_eq_abs] using hdom y)
  have htail : ∫ y in Ioi x, - F' y ≤ ∫ y in Ioi x, ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 :=
    setIntegral_mono hF'int.neg.integrableOn hsumsq.integrableOn hpoint
  have hfull : ∫ y in Ioi x, ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 ≤ ∫ y, ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 := by
    have hnonneg : 0 ≤ᵐ[volume] (fun y : ℝ ↦ ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2) :=
      Eventually.of_forall fun y ↦ add_nonneg (sq_nonneg _) (sq_nonneg _)
    simpa using integral_mono_measure (Measure.restrict_le_self (s := Ioi x))
      hnonneg hsumsq
  have hsqx : ‖ψ x‖ ^ 2 ≤ (lpNorm (ψ : ℝ → ℂ) 2 volume) ^ 2 +
      (lpNorm (d : ℝ → ℂ) 2 volume) ^ 2 := by
    calc ‖ψ x‖ ^ 2 = - ∫ y in Ioi x, F' y := by rw [heq, neg_neg]
      _ = ∫ y in Ioi x, - F' y := (integral_neg _).symm
      _ ≤ ∫ y in Ioi x, ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 := htail
      _ ≤ ∫ y, ‖ψ y‖ ^ 2 + ‖d y‖ ^ 2 := hfull
      _ = (lpNorm (ψ : ℝ → ℂ) 2 volume) ^ 2 +
            (lpNorm (d : ℝ → ℂ) 2 volume) ^ 2 := by
          rw [integral_add hsqψ hsqd, lpNorm_sq_eq_integral_norm_sq ψ,
            lpNorm_sq_eq_integral_norm_sq (SchwartzMap.derivCLM ℂ ℂ ψ)]
  have hsqrt : ‖ψ x‖ ≤ Real.sqrt ((lpNorm (ψ : ℝ → ℂ) 2 volume) ^ 2 +
      (lpNorm (d : ℝ → ℂ) 2 volume) ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt hsqx
  refine hsqrt.trans ?_
  have ha0 : 0 ≤ lpNorm (ψ : ℝ → ℂ) 2 volume := lpNorm_nonneg
  have hb0 : 0 ≤ lpNorm (d : ℝ → ℂ) 2 volume := lpNorm_nonneg
  rw [← Real.sqrt_sq (add_nonneg ha0 hb0)]
  refine Real.sqrt_le_sqrt ?_
  nlinarith

/-- Pointwise domination translates into a bound of `lpNorm` by the `√2`-multiple
of a combination of two `lpNorm`s. -/
private theorem lpNorm_le_add_of_pointwise {u g h : ℝ → ℂ} {c : ℝ}
    (hc : 0 ≤ c) (hu : MemLp u 2 volume) (hg : MemLp g 2 volume) (hh : MemLp h 2 volume)
    (hpt : ∀ y, ‖u y‖ ≤ c * ‖g y‖ + ‖h y‖) :
    lpNorm u 2 volume ≤
      Real.sqrt 2 * (c * lpNorm g 2 volume + lpNorm h 2 volume) := by
  classical
  have huI : Integrable (fun y : ℝ ↦ ‖u y‖ ^ 2) volume := by
    simpa using hu.integrable_norm_rpow (by norm_num) (by norm_num)
  have hgI : Integrable (fun y : ℝ ↦ ‖g y‖ ^ 2) volume := by
    simpa using hg.integrable_norm_rpow (by norm_num) (by norm_num)
  have hhI : Integrable (fun y : ℝ ↦ ‖h y‖ ^ 2) volume := by
    simpa using hh.integrable_norm_rpow (by norm_num) (by norm_num)
  set A : ℝ := ∫ y : ℝ, ‖g y‖ ^ 2 with hA
  set B : ℝ := ∫ y : ℝ, ‖h y‖ ^ 2 with hB
  have hA0 : 0 ≤ A := by rw [hA]; exact integral_nonneg fun y ↦ sq_nonneg _
  have hB0 : 0 ≤ B := by rw [hB]; exact integral_nonneg fun y ↦ sq_nonneg _
  have hwmeas : AEStronglyMeasurable (fun y : ℝ ↦ (c * ‖g y‖ + ‖h y‖) ^ 2) volume :=
    (((hg.aestronglyMeasurable.norm).const_mul c).add
      hh.aestronglyMeasurable.norm).pow 2
  have hbig : Integrable (fun y : ℝ ↦ (2 * c * c) * ‖g y‖ ^ 2 + 2 * ‖h y‖ ^ 2) volume :=
    (hgI.const_mul (2 * c * c)).add (hhI.const_mul 2)
  have hwI : Integrable (fun y : ℝ ↦ (c * ‖g y‖ + ‖h y‖) ^ 2) volume :=
    hbig.mono' hwmeas (Eventually.of_forall fun y ↦ by
      have hsq := sq_nonneg (c * ‖g y‖ - ‖h y‖)
      have hpos : (0:ℝ) ≤ 2 * c * c * ‖g y‖ ^ 2 + 2 * ‖h y‖ ^ 2 := by positivity
      have hnn : (0:ℝ) ≤ (c * ‖g y‖ + ‖h y‖) ^ 2 := sq_nonneg _
      simp only [Real.norm_eq_abs, abs_of_nonneg hnn]
      nlinarith)
  have hint : ∫ y : ℝ, ‖u y‖ ^ 2 ≤ ∫ y : ℝ, (c * ‖g y‖ + ‖h y‖) ^ 2 :=
    integral_mono huI hwI fun y ↦ pow_le_pow_left₀ (norm_nonneg _) (hpt y) 2
  have hsplit : ∫ y : ℝ, (c * ‖g y‖ + ‖h y‖) ^ 2 ≤ (2 * c * c) * A + 2 * B := by
    have hpt2 : ∀ y : ℝ, (c * ‖g y‖ + ‖h y‖) ^ 2 ≤ (2 * c * c) * ‖g y‖ ^ 2 + 2 * ‖h y‖ ^ 2 := by
      intro y
      have hyoung : (2:ℝ) * (c * ‖g y‖) * ‖h y‖ ≤ (c * ‖g y‖) ^ 2 + ‖h y‖ ^ 2 := by
        have hsq := sq_nonneg (c * ‖g y‖ - ‖h y‖)
        nlinarith
      nlinarith
    calc ∫ y : ℝ, (c * ‖g y‖ + ‖h y‖) ^ 2
        ≤ ∫ y : ℝ, (2 * c * c) * ‖g y‖ ^ 2 + 2 * ‖h y‖ ^ 2 :=
          integral_mono hwI hbig hpt2
      _ = (2 * c * c) * A + 2 * B := by
          have splitEq := integral_add (hgI.const_mul (2 * c * c)) (hhI.const_mul 2)
          simp only [splitEq, integral_const_mul, hA, hB]
  -- convert the `lpNorm`s to square roots of integrals
  have huN' : lpNorm u 2 volume = (∫ y : ℝ, ‖u y‖ ^ (2 : ℕ)) ^ ((2:ℝ≥0∞).toReal⁻¹) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num : (2:ℝ≥0∞) ≠ ∞) hu.aestronglyMeasurable]
    simp
  have hgN' : lpNorm g 2 volume = (∫ y : ℝ, ‖g y‖ ^ (2 : ℕ)) ^ ((2:ℝ≥0∞).toReal⁻¹) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num : (2:ℝ≥0∞) ≠ ∞) hg.aestronglyMeasurable]
    simp
  have hhN' : lpNorm h 2 volume = (∫ y : ℝ, ‖h y‖ ^ (2 : ℕ)) ^ ((2:ℝ≥0∞).toReal⁻¹) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num : (2:ℝ≥0∞) ≠ ∞) hh.aestronglyMeasurable]
    simp
  have hexp : ((2:ℝ≥0∞).toReal)⁻¹ = ((1 / 2 : ℝ)) := by
    simp [ENNReal.toReal_ofNat]
  have hexp2 : ∀ z : ℝ, z ^ ((2:ℝ≥0∞).toReal⁻¹) = Real.sqrt z := by
    intro z
    rw [hexp, ← Real.sqrt_eq_rpow]
  have hint' : (∫ y : ℝ, ‖u y‖ ^ 2) ^ ((2:ℝ≥0∞).toReal⁻¹) ≤
      (∫ y : ℝ, (c * ‖g y‖ + ‖h y‖) ^ 2) ^ ((2:ℝ≥0∞).toReal⁻¹) := by
    rw [hexp2 (∫ y : ℝ, ‖u y‖ ^ 2), hexp2 (∫ y : ℝ, (c * ‖g y‖ + ‖h y‖) ^ 2)]
    exact Real.sqrt_le_sqrt hint
  have hsplit' : (∫ y : ℝ, (c * ‖g y‖ + ‖h y‖) ^ 2) ^ ((2:ℝ≥0∞).toReal⁻¹) ≤
      ((2 * c * c) * A + 2 * B) ^ ((2:ℝ≥0∞).toReal⁻¹) := by
    rw [hexp2 (∫ y : ℝ, (c * ‖g y‖ + ‖h y‖) ^ 2), hexp2 ((2 * c * c) * A + 2 * B)]
    exact Real.sqrt_le_sqrt hsplit
  have hfinal : ((2 * c * c) * A + 2 * B) ^ ((2:ℝ≥0∞).toReal⁻¹) ≤
      Real.sqrt 2 * (c * A ^ ((2:ℝ≥0∞).toReal⁻¹) + B ^ ((2:ℝ≥0∞).toReal⁻¹)) := by
    have hsplit2 : ((2 * c * c) * A + 2 * B) = 2 * (c * c * A + B) := by ring
    have hmain : Real.sqrt (c * c * A + B) ≤ c * Real.sqrt A + Real.sqrt B := by
      refine (Real.sqrt_le_iff (x := c * c * A + B)
        (y := c * Real.sqrt A + Real.sqrt B)).2
        ⟨add_nonneg (mul_nonneg hc (Real.sqrt_nonneg A)) (Real.sqrt_nonneg B), ?_⟩
      have e1 : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA0
      have e2 : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB0
      have hsq : (c * Real.sqrt A + Real.sqrt B) ^ 2 =
          c * c * A + 2 * (c * (Real.sqrt A * Real.sqrt B)) + B := by
        rw [add_sq, mul_pow, e1, e2]
        ring
      rw [hsq]
      linarith [mul_nonneg hc (mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B))]
    rw [hexp2 ((2 * c * c) * A + 2 * B),
      show ((2 * c * c) * A + 2 * B) = 2 * (c * c * A + B) from by ring,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), hexp2 A, hexp2 B]
    exact mul_le_mul_of_nonneg_left hmain (Real.sqrt_nonneg 2)
  calc lpNorm u 2 volume = (∫ y : ℝ, ‖u y‖ ^ (2 : ℕ)) ^ ((2:ℝ≥0∞).toReal⁻¹) := huN'
    _ ≤ (∫ y : ℝ, (c * ‖g y‖ + ‖h y‖) ^ (2 : ℕ)) ^ ((2:ℝ≥0∞).toReal⁻¹) := hint'
    _ ≤ ((2 * c * c) * A + 2 * B) ^ ((2:ℝ≥0∞).toReal⁻¹) := hsplit'
    _ ≤ Real.sqrt 2 * (c * A ^ ((2:ℝ≥0∞).toReal⁻¹) + B ^ ((2:ℝ≥0∞).toReal⁻¹)) := hfinal
    _ = Real.sqrt 2 * (c * lpNorm g 2 volume + lpNorm h 2 volume) := by
        rw [hA, hB, ← hgN', ← hhN']

/-! ### The core estimate -/

/-- The real Schwartz seminorm `(k, n)` is bounded by the three Fourier `L²`
seminorms with indices `(k, n), (k - 1, n), (k, n + 1)`. -/
private theorem schwartz_seminorm_le_l2 (f : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n f ≤
      lpNorm ((realSchwartzFourierDeriv k n f : ℝ → ℂ)) 2 volume +
      Real.sqrt 2 * ((k : ℝ) * lpNorm ((realSchwartzFourierDeriv (k - 1) n f : ℝ → ℂ)) 2 volume +
        lpNorm ((realSchwartzFourierDeriv k (n + 1) f : ℝ → ℂ)) 2 volume) := by
  classical
  have hgrowth : ∀ j : ℕ, (fun x : ℝ ↦ (x : ℂ) ^ j).HasTemperateGrowth := by
    intro j; fun_prop
  -- the underlying function of `D ^[n] f` is the iterated derivative
  have hcoeg0 : ((SchwartzMap.derivCLM ℂ ℂ)^[n] f : ℝ → ℂ) =
      iteratedDeriv n (f : ℝ → ℂ) :=
    funext (coe_derivIterate f n)
  have hnormcoe : ∀ y : ℝ, ‖(y : ℂ)‖ = |y| := by
    intro y
    exact RCLike.norm_ofReal (K := ℂ) y
  -- the monomially-multiplied iterated derivative
  set ψ : 𝓢(ℝ, ℂ) := (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k]
      ((SchwartzMap.derivCLM ℂ ℂ)^[n] f) with hψdef
  have hcoepsi : ((ψ : ℝ → ℂ)) =
      fun y : ℝ ↦ (y : ℂ) ^ k * ((SchwartzMap.derivCLM ℂ ℂ)^[n] f : ℝ → ℂ) y := by
    funext y
    rw [hψdef, smulLeftIterate, SchwartzMap.smulLeftCLM_apply_apply (hg := hgrowth k)]
    simp [smul_eq_mul]
  -- the pointwise estimate on the derivative of `ψ`
  have hdiff : ∀ y : ℝ,
      ‖deriv (ψ : ℝ → ℂ) y‖ ≤
        (k : ℝ) * ‖(((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k-1]
            ((SchwartzMap.derivCLM ℂ ℂ)^[n] f)) : ℝ → ℂ) y‖ +
          ‖(((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k]
            ((SchwartzMap.derivCLM ℂ ℂ)^[n+1] f)) : ℝ → ℂ) y‖ := by
    intro y
    have hd1 : HasDerivAt (((SchwartzMap.derivCLM ℂ ℂ)^[n] f : ℝ → ℂ))
        (((SchwartzMap.derivCLM ℂ ℂ)^[n+1] f : ℝ → ℂ) y) y := by
      have h0 := SchwartzMap.hasDerivAt ((SchwartzMap.derivCLM ℂ ℂ)^[n] f) y
      rw [hcoeg0, ← iteratedDeriv_succ] at h0
      rw [hcoeg0, coe_derivIterate f (n + 1)]
      exact h0
    have hpow : HasDerivAt (fun z : ℝ ↦ (z : ℂ) ^ k) ((k : ℂ) * ((y : ℂ) ^ (k - 1))) y :=
      HasDerivAt.comp_ofReal (hasDerivAt_pow k (y : ℂ))
    have hdψ := hpow.mul hd1
    have hdψeq : deriv ((ψ : ℝ → ℂ)) y =
        ((k : ℂ) * (y : ℂ) ^ (k - 1)) * ((SchwartzMap.derivCLM ℂ ℂ)^[n] f : ℝ → ℂ) y +
          (y : ℂ) ^ k * ((SchwartzMap.derivCLM ℂ ℂ)^[n + 1] f : ℝ → ℂ) y := by
      rw [hcoepsi]
      exact hdψ.deriv
    rw [hdψeq]
    have hsmul1 : (((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k-1]
        ((SchwartzMap.derivCLM ℂ ℂ)^[n] f)) : ℝ → ℂ) y =
        (y : ℂ) ^ (k - 1) • ((SchwartzMap.derivCLM ℂ ℂ)^[n] f : ℝ → ℂ) y := by
      rw [smulLeftIterate, SchwartzMap.smulLeftCLM_apply_apply (hg := hgrowth (k-1))]
    have hsmul2 : (((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k]
        ((SchwartzMap.derivCLM ℂ ℂ)^[n+1] f)) : ℝ → ℂ) y =
        (y : ℂ) ^ k • ((SchwartzMap.derivCLM ℂ ℂ)^[n+1] f : ℝ → ℂ) y := by
      rw [smulLeftIterate, SchwartzMap.smulLeftCLM_apply_apply (hg := hgrowth k)]
    have hy1 : ‖((k : ℂ) * (y : ℂ) ^ (k - 1)) * ((SchwartzMap.derivCLM ℂ ℂ)^[n] f : ℝ → ℂ) y‖ ≤
        (k : ℝ) * ‖(((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k-1]
          ((SchwartzMap.derivCLM ℂ ℂ)^[n] f)) : ℝ → ℂ) y‖ := by
      rw [norm_mul, norm_mul, norm_natCast, hsmul1, norm_smul, norm_pow]
      exact le_of_eq (by ring)
    have hy2 : ‖(y : ℂ) ^ k * ((SchwartzMap.derivCLM ℂ ℂ)^[n + 1] f : ℝ → ℂ) y‖ ≤
        ‖(((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k]
          ((SchwartzMap.derivCLM ℂ ℂ)^[n+1] f)) : ℝ → ℂ) y‖ := by
      simp only [hsmul2, norm_mul, norm_smul, norm_pow]
      exact le_refl _
    exact le_trans (norm_add_le _ _) (add_le_add hy1 hy2)
  -- the two `L²` bounds from the fundamental lemma
  have hψbound : ∀ x : ℝ, ‖ψ x‖ ≤ lpNorm (ψ : ℝ → ℂ) 2 volume +
      lpNorm (((SchwartzMap.derivCLM ℂ ℂ) ψ : ℝ → ℂ)) 2 volume :=
    schwartz_norm_le_lpNorm_add_deriv ψ
  have hψx : ∀ x : ℝ, ‖ψ x‖ = |x| ^ k * ‖iteratedDeriv n (f : ℝ → ℂ) x‖ := by
    intro x
    rw [hψdef, smulLeftIterate, SchwartzMap.smulLeftCLM_apply_apply (hg := hgrowth k),
      norm_smul, norm_pow, hnormcoe x, coe_derivIterate f n]
  -- each monomial multiplication reduces (up to a constant of norm `≤ 1`) to a
  -- Fourier derivative, whose `L²` norm is one of the target seminorms
  have hcoef : ∀ j : ℕ, ‖((-(2 * Real.pi * Complex.I))⁻¹ ^ j : ℂ)‖ ≤ 1 := by
    intro j
    have hle : ‖(-(2 * Real.pi * Complex.I))⁻¹‖ ≤ 1 := by
      have h2 : ‖(-(2 * Real.pi * Complex.I))‖ = 2 * Real.pi := by
        rw [norm_neg, norm_mul, norm_mul, hnormcoe Real.pi, abs_of_pos Real.pi_pos,
          Complex.norm_I, mul_one]
        norm_num
      rw [norm_inv, h2, inv_eq_one_div]
      exact (div_le_one (by linarith [Real.pi_gt_three])).2 (by linarith [Real.pi_gt_three])
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hle j).trans (one_pow j).le
  have hfourier : ∀ (j i : ℕ),
      lpNorm ((((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[j]
        ((SchwartzMap.derivCLM ℂ ℂ)^[i] f)) : ℝ → ℂ)) 2 volume ≤
        lpNorm ((realSchwartzFourierDeriv j i f : ℝ → ℂ)) 2 volume := by
    intro j i
    have hE := lpNorm_fourier ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[j]
      ((SchwartzMap.derivCLM ℂ ℂ)^[i] f))
    rw [← hE, fourier_smulLeftIterate, lpNorm_smul]
    refine le_trans (mul_le_mul_of_nonneg_right (hcoef j) lpNorm_nonneg) ?_
    rw [one_mul]
    exact le_refl _
  -- assembly of the pointwise bound
  have h2 : lpNorm ((ψ : ℝ → ℂ)) 2 volume ≤
      lpNorm ((realSchwartzFourierDeriv k n f : ℝ → ℂ)) 2 volume := hfourier k n
  have h3 : lpNorm (((SchwartzMap.derivCLM ℂ ℂ) ψ : ℝ → ℂ)) 2 volume ≤
      Real.sqrt 2 * ((k : ℝ) * lpNorm ((realSchwartzFourierDeriv (k - 1) n f : ℝ → ℂ)) 2 volume +
        lpNorm ((realSchwartzFourierDeriv k (n + 1) f : ℝ → ℂ)) 2 volume) := by
    have hmem1 : MemLp ((((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k-1]
        ((SchwartzMap.derivCLM ℂ ℂ)^[n] f)) : ℝ → ℂ)) 2 volume :=
      ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k-1]
        ((SchwartzMap.derivCLM ℂ ℂ)^[n] f)).memLp 2 volume
    have hmem2 : MemLp ((((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k]
        ((SchwartzMap.derivCLM ℂ ℂ)^[n+1] f)) : ℝ → ℂ)) 2 volume :=
      ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k]
        ((SchwartzMap.derivCLM ℂ ℂ)^[n+1] f)).memLp 2 volume
    have hu0 : MemLp (((SchwartzMap.derivCLM ℂ ℂ) ψ : ℝ → ℂ)) 2 volume :=
      (SchwartzMap.derivCLM ℂ ℂ ψ).memLp 2 volume
    have hbase := lpNorm_le_add_of_pointwise (Nat.cast_nonneg k) hu0 hmem1 hmem2 hdiff
    calc lpNorm (((SchwartzMap.derivCLM ℂ ℂ) ψ : ℝ → ℂ)) 2 volume
        ≤ Real.sqrt 2 * ((k : ℝ) * lpNorm ((((SchwartzMap.smulLeftCLM ℂ
                (fun x : ℝ ↦ (x : ℂ)))^[k-1]
              ((SchwartzMap.derivCLM ℂ ℂ)^[n] f)) : ℝ → ℂ)) 2 volume +
            lpNorm ((((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k]
              ((SchwartzMap.derivCLM ℂ ℂ)^[n+1] f)) : ℝ → ℂ)) 2 volume) := hbase
      _ ≤ Real.sqrt 2 * ((k : ℝ) * lpNorm ((realSchwartzFourierDeriv (k - 1) n f : ℝ → ℂ)) 2 volume +
            lpNorm ((realSchwartzFourierDeriv k (n + 1) f : ℝ → ℂ)) 2 volume) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left (hfourier (k - 1) n) (by norm_num : (0:ℝ) ≤ (k:ℝ)))
              (hfourier k (n + 1))) (Real.sqrt_nonneg 2)
  have hpoint : ∀ x : ℝ, |x| ^ k * ‖iteratedDeriv n (f : ℝ → ℂ) x‖ ≤
      lpNorm ((realSchwartzFourierDeriv k n f : ℝ → ℂ)) 2 volume +
      Real.sqrt 2 * ((k : ℝ) * lpNorm ((realSchwartzFourierDeriv (k - 1) n f : ℝ → ℂ)) 2 volume +
        lpNorm ((realSchwartzFourierDeriv k (n + 1) f : ℝ → ℂ)) 2 volume) := by
    intro x
    have h1 := hψbound x
    rw [hψx x] at h1
    linarith
  exact SchwartzMap.seminorm_le_bound' ℂ k n f
    (add_nonneg lpNorm_nonneg (mul_nonneg (Real.sqrt_nonneg 2)
      (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (k:ℝ)) lpNorm_nonneg)
        lpNorm_nonneg))) hpoint

private theorem iterateCLM_add (L : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) (n : ℕ) (f g : 𝓢(ℝ, ℂ)) :
    L^[n] (f + g) = L^[n] f + L^[n] g := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_add]

private theorem iterateCLM_smul (L : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) (n : ℕ) (c : ℂ) (f : 𝓢(ℝ, ℂ)) :
    L^[n] (c • f) = c • L^[n] f := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Function.iterate_succ_apply', ih, map_smul]

private theorem realSchwartzFourierDeriv_add (m n : ℕ) (f g : 𝓢(ℝ, ℂ)) :
    realSchwartzFourierDeriv m n (f + g) =
      realSchwartzFourierDeriv m n f + realSchwartzFourierDeriv m n g := by
  simp only [realSchwartzFourierDeriv]
  rw [iterateCLM_add (SchwartzMap.derivCLM ℂ ℂ) n]
  have hF (g : 𝓢(ℝ, ℂ)) : 𝓕 g = fourierTransformCLM ℂ g := rfl
  rw [hF, (fourierTransformCLM ℂ).map_add, iterateCLM_add (SchwartzMap.derivCLM ℂ ℂ) m, hF, hF]

private theorem realSchwartzFourierDeriv_smul (m n : ℕ) (c : ℂ) (f : 𝓢(ℝ, ℂ)) :
    realSchwartzFourierDeriv m n (c • f) = c • realSchwartzFourierDeriv m n f := by
  simp only [realSchwartzFourierDeriv]
  rw [iterateCLM_smul (SchwartzMap.derivCLM ℂ ℂ) n]
  have hF (g : 𝓢(ℝ, ℂ)) : 𝓕 g = fourierTransformCLM ℂ g := rfl
  rw [hF, (fourierTransformCLM ℂ).map_smul, iterateCLM_smul (SchwartzMap.derivCLM ℂ ℂ) m, hF]

private theorem lpNorm_fourierDeriv_eq (j i : ℕ) (f : 𝓢(ℝ, ℂ)) :
    lpNorm (realSchwartzFourierDeriv j i f : ℝ → ℂ) 2 volume =
      (2 * Real.pi) ^ j *
        lpNorm ((((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[j]
          ((SchwartzMap.derivCLM ℂ ℂ)^[i] f)) : ℝ → ℂ)) 2 volume := by
  set mono : 𝓢(ℝ, ℂ) := (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[j]
      ((SchwartzMap.derivCLM ℂ ℂ)^[i] f)
  have hE := lpNorm_fourier mono
  rw [fourier_smulLeftIterate, lpNorm_smul] at hE
  have hnorm : ‖((-(2 * Real.pi * Complex.I))⁻¹ ^ j : ℂ)‖ = (2 * Real.pi)⁻¹ ^ j := by
    rw [norm_pow]
    congr 1
    rw [norm_inv, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hnorm] at hE
  have hpos : (2 * Real.pi)⁻¹ ^ j ≠ 0 := by positivity
  have hE' : (2 * Real.pi)⁻¹ ^ j *
      lpNorm (realSchwartzFourierDeriv j i f : ℝ → ℂ) 2 volume =
      lpNorm (mono : ℝ → ℂ) 2 volume := by
    simpa [realSchwartzFourierDeriv] using hE
  apply mul_left_cancel₀ hpos
  calc (2 * Real.pi)⁻¹ ^ j * lpNorm (realSchwartzFourierDeriv j i f : ℝ → ℂ) 2 volume
      = lpNorm (mono : ℝ → ℂ) 2 volume := hE'
    _ = (2 * Real.pi)⁻¹ ^ j * ((2 * Real.pi) ^ j * lpNorm (mono : ℝ → ℂ) 2 volume) := by
        rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (by positivity : (2 : ℝ) * Real.pi ≠ 0),
          one_pow, one_mul]

private theorem lpNorm_monomial_le (f : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    lpNorm ((((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k]
        ((SchwartzMap.derivCLM ℂ ℂ)^[n] f)) : ℝ → ℂ)) 2 volume ≤
      Real.sqrt Real.pi *
        (SchwartzMap.seminorm ℂ k n f + SchwartzMap.seminorm ℂ (k + 1) n f) := by
  set φ : 𝓢(ℝ, ℂ) := (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)))^[k]
      ((SchwartzMap.derivCLM ℂ ℂ)^[n] f)
  set C : ℝ := SchwartzMap.seminorm ℂ k n f + SchwartzMap.seminorm ℂ (k + 1) n f
  have hC : 0 ≤ C := add_nonneg (apply_nonneg _ _) (apply_nonneg _ _)
  have hgrowth : (fun x : ℝ ↦ (x : ℂ) ^ k).HasTemperateGrowth := by fun_prop
  have hcoe : ∀ x : ℝ, φ x = (x : ℂ) ^ k * ((SchwartzMap.derivCLM ℂ ℂ)^[n] f) x := by
    intro x
    have hmap : φ = SchwartzMap.smulLeftCLM ℂ (fun y : ℝ ↦ (y : ℂ) ^ k)
        ((SchwartzMap.derivCLM ℂ ℂ)^[n] f) := by
      simpa [φ] using smulLeftIterate k ((SchwartzMap.derivCLM ℂ ℂ)^[n] f)
    rw [hmap, SchwartzMap.smulLeftCLM_apply_apply (hg := hgrowth)]
    simp [smul_eq_mul]
  have hnorm : ∀ x : ℝ, ‖φ x‖ = |x| ^ k * ‖iteratedDeriv n (f : ℝ → ℂ) x‖ := by
    intro x
    rw [hcoe, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, coe_derivIterate]
  have hsum : ∀ x : ℝ, (1 + |x|) * ‖φ x‖ ≤ C := by
    intro x
    rw [show (1 + |x|) * ‖φ x‖ = ‖φ x‖ + |x| * ‖φ x‖ by ring, hnorm]
    have h1 := SchwartzMap.le_seminorm' ℂ k n f x
    have h2 := SchwartzMap.le_seminorm' ℂ (k + 1) n f x
    have hx : |x| * (|x| ^ k * ‖iteratedDeriv n (f : ℝ → ℂ) x‖) =
        |x| ^ (k + 1) * ‖iteratedDeriv n (f : ℝ → ℂ) x‖ := by
      rw [pow_succ, mul_assoc, mul_left_comm |x| (|x| ^ k)]
    simpa [hx] using add_le_add h1 h2
  have hdiv : ∀ x : ℝ, ‖φ x‖ ≤ C * (1 + |x|)⁻¹ := by
    intro x
    have hpos : 0 < 1 + |x| := by positivity
    have hx := hsum x
    rw [mul_comm] at hx
    rwa [← le_div_iff₀ hpos, div_eq_mul_inv] at hx
  have hsq : ∀ x : ℝ, ‖φ x‖ ^ 2 ≤ C ^ 2 * (1 + x ^ 2)⁻¹ := by
    intro x
    have hinv : (1 + |x|)⁻¹ ^ 2 ≤ (1 + x ^ 2)⁻¹ := by
      have hden : 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by
        calc 1 + x ^ 2 = 1 + |x| ^ 2 := by rw [sq_abs]
          _ ≤ 1 + 2 * |x| + |x| ^ 2 := by linarith [abs_nonneg x]
          _ = (1 + |x|) ^ 2 := by ring
      rw [inv_pow, ← one_div, ← one_div]
      exact div_le_div_of_nonneg_left zero_le_one (by positivity) hden
    calc ‖φ x‖ ^ 2 ≤ (C * (1 + |x|)⁻¹) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hdiv x) 2
      _ = C ^ 2 * (1 + |x|)⁻¹ ^ 2 := by ring
      _ ≤ C ^ 2 * (1 + x ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
  have hsqφ : Integrable (fun y : ℝ ↦ ‖φ y‖ ^ 2) volume := by
    have h := (φ.memLp 2 volume).integrable_norm_rpow (by norm_num) (by norm_num)
    have hfun : (fun y : ℝ ↦ ‖φ y‖ ^ (2 : ℝ≥0∞).toReal) = fun y ↦ ‖φ y‖ ^ 2 := by
      funext y
      simp only [ENNReal.toReal_ofNat]
      exact Real.rpow_natCast ‖φ y‖ 2
    simpa [hfun] using h
  have hintC : Integrable (fun y : ℝ ↦ C ^ 2 * (1 + y ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul (C ^ 2)
  have hint : ∫ y : ℝ, ‖φ y‖ ^ 2 ≤ ∫ y : ℝ, C ^ 2 * (1 + y ^ 2)⁻¹ :=
    integral_mono hsqφ hintC hsq
  have hrhs : ∫ y : ℝ, C ^ 2 * (1 + y ^ 2)⁻¹ = C ^ 2 * Real.pi := by
    rw [integral_const_mul, integral_univ_inv_one_add_sq]
  have hsqle : (lpNorm (φ : ℝ → ℂ) 2 volume) ^ 2 ≤ C ^ 2 * Real.pi := by
    rw [← lpNorm_sq_eq_integral_norm_sq φ]
    exact hint.trans_eq hrhs
  calc lpNorm (φ : ℝ → ℂ) 2 volume
      ≤ Real.sqrt (C ^ 2 * Real.pi) := by
        rw [← Real.sqrt_sq (lpNorm_nonneg : 0 ≤ lpNorm (φ : ℝ → ℂ) 2 volume)]
        exact Real.sqrt_le_sqrt hsqle
    _ = Real.sqrt Real.pi * C := by
        rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC, mul_comm]

private theorem lpNorm_fourierDeriv_le_seminorm (f : 𝓢(ℝ, ℂ)) (m n : ℕ) :
    lpNorm (realSchwartzFourierDeriv m n f : ℝ → ℂ) 2 volume ≤
      (2 * Real.pi) ^ m * Real.sqrt Real.pi *
        (SchwartzMap.seminorm ℂ m n f + SchwartzMap.seminorm ℂ (m + 1) n f) := by
  rw [lpNorm_fourierDeriv_eq, mul_assoc]
  exact mul_le_mul_of_nonneg_left (lpNorm_monomial_le f m n)
    (pow_nonneg (by positivity : 0 ≤ 2 * Real.pi) _)

private theorem lpNorm_fourierDeriv_add (i : ℕ × ℕ) (f g : 𝓢(ℝ, ℂ)) :
    lpNorm (realSchwartzFourierDeriv i.1 i.2 (f + g) : ℝ → ℂ) 2 volume ≤
      lpNorm (realSchwartzFourierDeriv i.1 i.2 f : ℝ → ℂ) 2 volume +
        lpNorm (realSchwartzFourierDeriv i.1 i.2 g : ℝ → ℂ) 2 volume := by
  rw [realSchwartzFourierDeriv_add]
  have hcoe :
      ((realSchwartzFourierDeriv i.1 i.2 f + realSchwartzFourierDeriv i.1 i.2 g : 𝓢(ℝ, ℂ)) :
        ℝ → ℂ) =
      (realSchwartzFourierDeriv i.1 i.2 f : ℝ → ℂ) +
        (realSchwartzFourierDeriv i.1 i.2 g : ℝ → ℂ) := by
    funext x; simp
  rw [hcoe]
  exact lpNorm_add_le ((realSchwartzFourierDeriv i.1 i.2 f).memLp 2 volume)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)

private theorem lpNorm_fourierDeriv_smul (i : ℕ × ℕ) (c : ℂ) (f : 𝓢(ℝ, ℂ)) :
    lpNorm (realSchwartzFourierDeriv i.1 i.2 (c • f) : ℝ → ℂ) 2 volume =
      ‖c‖ * lpNorm (realSchwartzFourierDeriv i.1 i.2 f : ℝ → ℂ) 2 volume := by
  rw [realSchwartzFourierDeriv_smul]
  have hcoe : ((c • realSchwartzFourierDeriv i.1 i.2 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) =
      c • (realSchwartzFourierDeriv i.1 i.2 f : ℝ → ℂ) := by
    funext x; simp
  rw [hcoe, lpNorm_const_smul]
  rfl

/-- Paper: Proposition D.1.10.2, p. 784. L² norms of the differentiated real
Fourier transforms in (D.1.10.3) generate the Schwartz topology. -/
theorem realSchwartz_fourierLp_generates :
    GeneratesLpSeminorms (volume : Measure ℝ) 2
      (fun i : ℕ × ℕ ↦ fun f : 𝓢(ℝ, ℂ) ↦
        (realSchwartzFourierDeriv i.1 i.2 f : ℝ → ℂ)) := by
  classical
  let ν : ℕ × ℕ → 𝓢(ℝ, ℂ) → ℝ := fun i f ↦
    lpNorm (realSchwartzFourierDeriv i.1 i.2 f : ℝ → ℂ) 2 volume
  let P : ℕ × ℕ → Seminorm ℂ 𝓢(ℝ, ℂ) := fun i ↦
    Seminorm.of (ν i) (fun f g ↦ lpNorm_fourierDeriv_add i f g)
      (fun c f ↦ lpNorm_fourierDeriv_smul i c f)
  refine ⟨fun i f ↦ (realSchwartzFourierDeriv i.1 i.2 f).memLp 2 volume, ⟨P, ?_, ?_⟩⟩
  · refine (schwartz_withSeminorms ℂ ℝ ℂ).congr ?_ ?_
    · refine Seminorm.IsBounded.of_real ?_
      rintro ⟨m, n⟩
      let s : Finset (ℕ × ℕ) := {(m, n), (m + 1, n)}
      refine ⟨s, (2 * Real.pi) ^ m * Real.sqrt Real.pi * 2, fun f ↦ ?_⟩
      have hle := lpNorm_fourierDeriv_le_seminorm f m n
      have h1 : SchwartzMap.seminorm ℂ m n f ≤ (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
        simpa [s, schwartzSeminormFamily_apply] using
          (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ ℝ ℂ)
            (by simp [s] : (m, n) ∈ s))
      have h2 : SchwartzMap.seminorm ℂ (m + 1) n f ≤
          (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by
        simpa [s, schwartzSeminormFamily_apply] using
          (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ ℝ ℂ)
            (by simp [s] : (m + 1, n) ∈ s))
      have hsup : SchwartzMap.seminorm ℂ m n f + SchwartzMap.seminorm ℂ (m + 1) n f ≤
          2 * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by linarith
      have hcoef : 0 ≤ (2 * Real.pi) ^ m * Real.sqrt Real.pi := by positivity
      calc P (m, n) f = ν (m, n) f := rfl
        _ ≤ (2 * Real.pi) ^ m * Real.sqrt Real.pi *
            (SchwartzMap.seminorm ℂ m n f + SchwartzMap.seminorm ℂ (m + 1) n f) := hle
        _ ≤ (2 * Real.pi) ^ m * Real.sqrt Real.pi *
            (2 * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f) :=
              mul_le_mul_of_nonneg_left hsup hcoef
        _ = ((2 * Real.pi) ^ m * Real.sqrt Real.pi * 2) *
            (s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) f := by ring
    · refine Seminorm.IsBounded.of_real ?_
      rintro ⟨k, n⟩
      let s : Finset (ℕ × ℕ) := {(k, n), (k - 1, n), (k, n + 1)}
      refine ⟨s, 1 + Real.sqrt 2 * (k : ℝ) + Real.sqrt 2, fun f ↦ ?_⟩
      have hle := schwartz_seminorm_le_l2 f k n
      have hPeq (a b : ℕ) :
          P (a, b) f = lpNorm (realSchwartzFourierDeriv a b f : ℝ → ℂ) 2 volume := rfl
      have h1 : lpNorm (realSchwartzFourierDeriv k n f : ℝ → ℂ) 2 volume ≤ (s.sup P) f := by
        rw [← hPeq]
        exact Seminorm.le_finset_sup_apply (by simp [s])
      have h2 : lpNorm (realSchwartzFourierDeriv (k - 1) n f : ℝ → ℂ) 2 volume ≤
          (s.sup P) f := by
        rw [← hPeq]
        exact Seminorm.le_finset_sup_apply (by simp [s])
      have h3 : lpNorm (realSchwartzFourierDeriv k (n + 1) f : ℝ → ℂ) 2 volume ≤
          (s.sup P) f := by
        rw [← hPeq]
        exact Seminorm.le_finset_sup_apply (by simp [s])
      have hS : 0 ≤ (s.sup P) f := apply_nonneg _ _
      have hgoal : SchwartzMap.seminorm ℂ k n f ≤
          (1 + Real.sqrt 2 * (k : ℝ) + Real.sqrt 2) * (s.sup P) f := by
        set S : ℝ := (s.sup P) f
        have hmid : lpNorm (realSchwartzFourierDeriv k n f : ℝ → ℂ) 2 volume +
            Real.sqrt 2 * ((k : ℝ) * lpNorm (realSchwartzFourierDeriv (k - 1) n f : ℝ → ℂ) 2 volume +
              lpNorm (realSchwartzFourierDeriv k (n + 1) f : ℝ → ℂ) 2 volume) ≤
            S + Real.sqrt 2 * ((k : ℝ) * S + S) := by
          have hB : (k : ℝ) * lpNorm (realSchwartzFourierDeriv (k - 1) n f : ℝ → ℂ) 2 volume ≤
              (k : ℝ) * S := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg k)
          have hsum : (k : ℝ) * lpNorm (realSchwartzFourierDeriv (k - 1) n f : ℝ → ℂ) 2 volume +
              lpNorm (realSchwartzFourierDeriv k (n + 1) f : ℝ → ℂ) 2 volume ≤
              (k : ℝ) * S + S := add_le_add hB h3
          exact add_le_add h1 (mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _))
        calc SchwartzMap.seminorm ℂ k n f ≤
            lpNorm (realSchwartzFourierDeriv k n f : ℝ → ℂ) 2 volume +
              Real.sqrt 2 * ((k : ℝ) *
                lpNorm (realSchwartzFourierDeriv (k - 1) n f : ℝ → ℂ) 2 volume +
                lpNorm (realSchwartzFourierDeriv k (n + 1) f : ℝ → ℂ) 2 volume) := hle
          _ ≤ S + Real.sqrt 2 * ((k : ℝ) * S + S) := hmid
          _ = (1 + Real.sqrt 2 * (k : ℝ) + Real.sqrt 2) * S := by ring
      simpa [schwartzSeminormFamily_apply] using hgoal
  · intro i f
    have hP : P i f = (eLpNorm (realSchwartzFourierDeriv i.1 i.2 f : ℝ → ℂ) 2 volume).toReal := by
      change ν i f = _
      rfl
    rw [hP, ENNReal.ofReal_toReal]
    exact ((realSchwartzFourierDeriv i.1 i.2 f).memLp 2 volume).eLpNorm_ne_top

end RealSchwartzFourierLp

open scoped LineDeriv in
/-- Paper: (D.1.10.4), p. 785. Differentiating the Fourier transform corresponds
to taking the Fourier transform after multiplication by a power of the coordinate. -/
private theorem realSchwartz_iterate_deriv_fourier (m : ℕ) (f : 𝓢(ℝ, ℂ)) :
    (SchwartzMap.derivCLM ℂ ℂ)^[m] (𝓕 f) =
      𝓕 (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ ((-2 * π * Complex.I : ℂ) * x) ^ m) f) := by
  have hweight : (fun x : ℝ ↦ (-2 * π * Complex.I : ℂ) * x).HasTemperateGrowth := by fun_prop
  have hpow (k : ℕ) :
      (fun x : ℝ ↦ ((-2 * π * Complex.I : ℂ) * x) ^ k).HasTemperateGrowth := by
    exact hweight.pow k
  have hderiv (g : 𝓢(ℝ, ℂ)) :
      SchwartzMap.derivCLM ℂ ℂ (𝓕 g) =
        𝓕 (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (-2 * π * Complex.I : ℂ) * x) g) := by
    have hline : ∂_{(1 : ℝ)} (𝓕 g) = SchwartzMap.derivCLM ℂ ℂ (𝓕 g) := by
      ext1 x
      let G : 𝓢(ℝ, ℂ) := 𝓕 g
      change fderiv ℝ (⇑G) x 1 = deriv (⇑G) x
      exact fderiv_apply_one_eq_deriv
    rw [← hline, SchwartzMap.lineDerivOp_fourier_eq]
    congr 1
    ext1 x
    have hinner : (fun y : ℝ ↦ inner ℝ y 1) = id := by
      funext y
      exact (Real.inner_apply y 1).trans (mul_one y)
    rw [hinner, SchwartzMap.smulLeftCLM_apply_apply hweight]
    have hid : (id : ℝ → ℝ).HasTemperateGrowth := by fun_prop
    rw [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hid]
    simp [Complex.real_smul]
    ring
  induction m with
  | zero =>
    rw [Function.iterate_zero_apply]
    congr 1
    ext1 x
    rw [SchwartzMap.smulLeftCLM_apply_apply (hpow 0)]
    simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, hderiv]
    congr 1
    ext1 x
    rw [SchwartzMap.smulLeftCLM_apply_apply hweight,
      SchwartzMap.smulLeftCLM_apply_apply (hpow m),
      SchwartzMap.smulLeftCLM_apply_apply (hpow (m + 1))]
    simp only [smul_smul, pow_succ']

/-- The weighted derivative's L² norm is controlled by the corresponding Fourier
seminorm via Plancherel. -/
private theorem realSchwartz_weightedDeriv_eLpNorm (m n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    eLpNorm (fun x : ℝ ↦ ‖x‖ ^ m * ‖iteratedFDeriv ℝ n f x‖) 2 volume ≤
      eLpNorm (realSchwartzFourierDeriv m n f : ℝ → ℂ) 2 volume := by
  let g := (SchwartzMap.derivCLM ℂ ℂ)^[n] f
  have hg' (k : ℕ) : ⇑((SchwartzMap.derivCLM ℂ ℂ)^[k] f) = iteratedDeriv k f := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', iteratedDeriv_succ, ← ih]
      rfl
  have hg (x : ℝ) : ‖g x‖ = ‖iteratedFDeriv ℝ n f x‖ := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← hg']
  let w (x : ℝ) := ((-2 * π * Complex.I : ℂ) * x) ^ m
  let h := SchwartzMap.smulLeftCLM ℂ w g
  have hw : w.HasTemperateGrowth := by dsimp [w]; fun_prop
  have hFourier : realSchwartzFourierDeriv m n f = 𝓕 h :=
    realSchwartz_iterate_deriv_fourier m g
  have hPlancherel : eLpNorm ((𝓕 h : 𝓢(ℝ, ℂ)) : ℝ → ℂ) 2 volume = eLpNorm (⇑h) 2 volume := by
    have hL2 := SchwartzMap.norm_fourier_toL2_eq h
    simp only [SchwartzMap.norm_toLp] at hL2
    simpa only [ENNReal.ofReal_toReal ((𝓕 h : 𝓢(ℝ, ℂ)).eLpNorm_lt_top 2 volume).ne,
      ENNReal.ofReal_toReal (h.eLpNorm_lt_top 2 volume).ne] using congrArg ENNReal.ofReal hL2
  rw [hFourier, hPlancherel]
  apply eLpNorm_mono (f.integrable_pow_mul_iteratedFDeriv volume m n).aestronglyMeasurable
  intro x
  change ‖‖x‖ ^ m * ‖iteratedFDeriv ℝ n f x‖‖ ≤ ‖h x‖
  rw [Real.norm_of_nonneg (by positivity)]
  dsimp [h]
  rw [SchwartzMap.smulLeftCLM_apply_apply hw, norm_smul]
  change _ ≤ ‖((-2 * π * Complex.I : ℂ) * x) ^ m‖ * ‖g x‖
  rw [hg, norm_pow, norm_mul, Complex.norm_real]
  have hc : 1 ≤ ‖(-2 * π * Complex.I : ℂ)‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
    norm_num
    linarith [Real.pi_gt_three]
  gcongr
  exact le_mul_of_one_le_left (abs_nonneg x) hc

/-- Bounds on Fourier L² seminorms give uniform bounds on the weighted L¹ norms
of the original derivatives by Cauchy–Schwarz. -/
private theorem realSchwartz_weightedDeriv_integral_bounded (B : Set (𝓢(ℝ, ℂ)))
    (hB : ∀ m n : ℕ, ∃ C : ℝ≥0, ∀ f ∈ B,
      eLpNorm (realSchwartzFourierDeriv m n f : ℝ → ℂ) 2 volume ≤ (C : ℝ≥0∞)) :
    ∀ m n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ f ∈ B,
      (∫ x : ℝ, ‖x‖ ^ m * ‖iteratedFDeriv ℝ n f x‖) ≤ C := by
  let u (m n : ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) := ‖x‖ ^ m * ‖iteratedFDeriv ℝ n f x‖
  have hu (m n : ℕ) (f : 𝓢(ℝ, ℂ)) : Integrable (u m n f) :=
    f.integrable_pow_mul_iteratedFDeriv volume m n
  have hu_nonneg (m n : ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) : 0 ≤ u m n f x := by
    dsimp [u]
    positivity
  obtain ⟨k, hk⟩ := Measure.HasTemperateGrowth.exists_eLpNorm_lt_top 2
    (inferInstance : (volume : Measure ℝ).HasTemperateGrowth)
  let w (x : ℝ) := (1 + ‖x‖) ^ (-(k : ℝ))
  have hw : AEStronglyMeasurable w volume :=
    (Continuous.rpow_const (by fun_prop) (fun x ↦ Or.inl (by positivity))).aestronglyMeasurable
  let K : ℝ≥0 := (eLpNorm w 2 volume).toNNReal
  have hK : eLpNorm w 2 volume = (K : ℝ≥0∞) := (ENNReal.coe_toNNReal hk.ne).symm
  intro m n
  obtain ⟨C₀, hC₀⟩ := hB 0 n
  obtain ⟨C₁, hC₁⟩ := hB (m + k) n
  let C : ℝ≥0 := K * (2 ^ k * (C₀ + C₁))
  refine ⟨C, C.coe_nonneg, fun f hf ↦ ?_⟩
  let v : ℝ → ℝ := u 0 n f + u (m + k) n f
  have hv : AEStronglyMeasurable v volume := (hu 0 n f).aestronglyMeasurable.add
    (hu (m + k) n f).aestronglyMeasurable
  have hnorm : eLpNorm (u m n f) 1 volume ≤ (C : ℝ≥0∞) := calc
    _ ≤ eLpNorm (w • ((2 : ℝ) ^ k • v)) 1 volume := by
      refine eLpNorm_mono (hu m n f).aestronglyMeasurable fun x ↦ ?_
      rw [Real.norm_of_nonneg (hu_nonneg m n f x)]
      have h := pow_mul_le_of_le_of_pow_mul_le (k := m) (l := k)
        (norm_nonneg x) (norm_nonneg (iteratedFDeriv ℝ n f x)) (le_refl _)
        (le_refl (u (m + k) n f x))
      change u m n f x ≤ ‖w x * ((2 : ℝ) ^ k * (u 0 n f x + u (m + k) n f x))‖
      refine h.trans ?_
      rw [mul_comm _ (w x), Real.norm_of_nonneg
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity))]
      simp [u, w]
    _ ≤ eLpNorm w 2 volume * eLpNorm ((2 : ℝ) ^ k • v) 2 volume :=
      eLpNorm_smul_le_mul_eLpNorm hw (hv.const_smul _)
    _ ≤ (C : ℝ≥0∞) := by
      have htwo : ‖(2 : ℝ)‖ₑ = 2 := by exact_mod_cast Real.eNorm_natCast 2
      rw [hK, eLpNorm_const_smul, ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_pow,
        ENNReal.coe_ofNat, ENNReal.coe_add, eNorm_pow, htwo]
      gcongr
      exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
        (add_le_add ((realSchwartz_weightedDeriv_eLpNorm 0 n f).trans (hC₀ f hf))
          ((realSchwartz_weightedDeriv_eLpNorm (m + k) n f).trans (hC₁ f hf)))
  change ∫ x, u m n f x ≤ (C : ℝ)
  calc
    _ = ∫ x, ‖u m n f x‖ := integral_congr_ae (ae_of_all _ fun x ↦
      (Real.norm_of_nonneg (hu_nonneg m n f x)).symm)
    _ = (eLpNorm (u m n f) 1 volume).toReal := by
      rw [integral_norm_eq_lintegral_eNorm (hu m n f).aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_eNorm (hu m n f).aestronglyMeasurable]
    _ ≤ (C : ℝ) := ENNReal.toReal_le_of_le_ofReal C.coe_nonneg
      (by simpa only [ENNReal.ofReal_coe_nnreal] using hnorm)

/-- Paper: Proposition D.1.10.2, p. 784. A set of real Schwartz functions is bounded
exactly when each Fourier L² seminorm is bounded on it. -/
theorem realSchwartz_fourierLp_bounded_iff (B : Set (𝓢(ℝ, ℂ))) :
    IsVonNBounded ℂ B ↔ ∀ m n : ℕ, ∃ C : ℝ≥0, ∀ f ∈ B,
      eLpNorm (realSchwartzFourierDeriv m n f : ℝ → ℂ) 2 volume ≤ (C : ℝ≥0∞) := by
  constructor
  · intro hB m n
    let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
    let D := SchwartzMap.derivCLM ℂ ℂ
    let T := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ) ∘L
      ((D ^ m) ∘L SchwartzMap.fourierTransformCLM ℂ) ∘L (D ^ n)
    obtain ⟨R, hR⟩ := (NormedSpace.image_isVonNBounded_iff ℂ).1 (hB.image T)
    refine ⟨Real.toNNReal R, fun f hf ↦ ?_⟩
    have hTf : T f = (realSchwartzFourierDeriv m n f).toLp 2 volume := by
      simp [T, D, realSchwartzFourierDeriv, FunLike.coe_pow_eq_iterate]
    have hRf := hR f hf
    rw [hTf, SchwartzMap.norm_toLp] at hRf
    rw [← ENNReal.ofReal_toReal ((realSchwartzFourierDeriv m n f).eLpNorm_lt_top 2 volume).ne]
    simpa only [ENNReal.ofReal_coe_nnreal] using
      ENNReal.ofReal_le_ofReal (hRf.trans (Real.le_coe_toNNReal R))
  · intro hB
    choose C hCpos hC using realSchwartz_weightedDeriv_integral_bounded B hB
    have h := (schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bounded
      (s := (𝓕 · : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)) '' B)
    have hFB : IsVonNBounded ℂ ((𝓕 · : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)) '' B) := h.mpr (fun (k, n) ↦ by
      let M := (2 * π) ^ n * (2 * (n : ℝ) + 2) ^ k *
        ∑ p ∈ Finset.range (n + 1) ×ˢ Finset.range (k + 1), C p.1 p.2
      have hM : 0 ≤ M := by
        dsimp [M]
        exact mul_nonneg (by positivity) (Finset.sum_nonneg fun p _ ↦ hCpos p.1 p.2)
      refine ⟨M + 1, by linarith, ?_⟩
      rintro _ ⟨f, hf, rfl⟩
      apply lt_of_le_of_lt _ (lt_add_one M)
      apply SchwartzMap.seminorm_le_bound ℂ k n _ hM
      intro x
      rw [SchwartzMap.fourier_coe]
      apply (Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := ⊤) (N := ⊤) (f.smooth ⊤)
        (fun i j _ _ ↦ f.integrable_pow_mul_iteratedFDeriv volume i j) le_top le_top x).trans
      dsimp [M]
      gcongr with p _
      exact hC p.1 p.2 f hf)
    apply (hFB.image (FourierTransform.fourierInvCLM ℂ 𝓢(ℝ, ℂ))).subset
    intro f hf
    refine ⟨𝓕 f, ⟨f, hf, rfl⟩, ?_⟩
    rw [FourierTransform.fourierInvCLM_apply, FourierTransform.fourierInv_fourier_eq]

-- TODO(paper-gap): The last sum in (D.1.10.5) omits the constant term k = 0.
-- For m = n = 0 and N = 1, bumps concentrated at 0 disprove that estimate.

/-- Paper: (D.1.10.6)–(D.1.10.8), p. 785. Multiply the coordinate mixed partial
of a Euclidean Schwartz function by the coordinate monomial. -/
def euclideanSchwartzMonomialPartial {m : ℕ} (α β : Fin m → ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (x : EuclideanSpace ℝ (Fin m)) : ℂ :=
  (∏ i, (x i : ℂ) ^ α i) *
    elementaryPartial (fun g : ElementaryLieGroup m 0 0 PUnit.{1} ↦ f g.1)
      β 0 (x, 0) 0 PUnit.unit

/-- Paper: (D.1.10.6)–(D.1.10.8), p. 785. At zero multi-indices the weighted
partial is the original function.
Deviation: Sanity check on the weight and derivative. -/
theorem euclideanSchwartzMonomialPartial_zero {m : ℕ}
    (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (x : EuclideanSpace ℝ (Fin m)) :
    euclideanSchwartzMonomialPartial 0 0 f x = f x := by
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 0)
  let directions : List X :=
    ((List.ofFn (fun _ : Fin m ↦ ([] : List X))).flatten ++
      (List.ofFn (fun _ : Fin 0 ↦ ([] : List X))).flatten)
  have hnil (k : ℕ) : (List.replicate k ([] : List X)).flatten = [] := by
    induction k with
    | zero => rfl
    | succ j ih => rw [List.replicate_succ, List.flatten_cons, ih]; rfl
  have hdir : directions = [] := by
    dsimp [directions]
    rw [List.ofFn_const, List.ofFn_const]
    rw [hnil m, hnil 0]
    rfl
  have hlen : directions.length = 0 := by rw [hdir]; rfl
  simp [euclideanSchwartzMonomialPartial, elementaryPartial]
  change (iteratedFDeriv ℝ directions.length
        (fun v ↦ f ((elementaryCover v ![] PUnit.unit).1)) (x, 0)) directions.get = f x
  have hiter (k : ℕ) (hk : k = 0) (d : Fin k → X) :
      (iteratedFDeriv ℝ k (fun v ↦ f ((elementaryCover v ![] PUnit.unit).1)) (x, 0)) d = f x := by
    subst k
    simp [elementaryCover]
  exact hiter directions.length hlen directions.get

/-- The derivative on the elementary cover reduces to the Euclidean coordinate derivative. -/
private theorem euclideanSchwartzMonomialPartial_eq {m : ℕ} (α β : Fin m → ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (x : EuclideanSpace ℝ (Fin m)) :
    let directions := (List.finRange m).flatMap fun i ↦ List.replicate (β i) i
    euclideanSchwartzMonomialPartial α β f x =
      (∏ i, (x i : ℂ) ^ α i) *
        iteratedFDeriv ℝ directions.length f x
          (fun j ↦ EuclideanSpace.single (directions.get j) 1) := by
  let E := EuclideanSpace ℝ (Fin m)
  let X := E × EuclideanSpace ℝ (Fin 0)
  let P : X →L[ℝ] E := ContinuousLinearMap.fst ℝ E _
  let lift (i : Fin m) : X := (EuclideanSpace.single i 1, 0)
  let directions := (List.finRange m).flatMap fun i ↦ List.replicate (β i) i
  have hdirs : (List.ofFn (fun i ↦ List.replicate (β i) (lift i))).flatten ++
      (List.ofFn (fun i : Fin 0 ↦ List.replicate ((0 : Fin 0 → ℕ) i)
        ((0 : E), EuclideanSpace.single i 1))).flatten = directions.map lift := by
    simp [directions, List.ofFn_eq_map, List.flatMap, Function.comp_def]
  unfold euclideanSchwartzMonomialPartial elementaryPartial
  change (∏ i, (x i : ℂ) ^ α i) *
    (fun l : List X ↦ iteratedFDeriv ℝ l.length ((f : E → ℂ) ∘ P) (x, 0) l.get) _ = _
  rw [hdirs]
  have hderiv (l : List (Fin m)) :
      iteratedFDeriv ℝ (l.map lift).length ((f : E → ℂ) ∘ P) (x, 0) (l.map lift).get =
        iteratedFDeriv ℝ l.length f x (fun j ↦ EuclideanSpace.single (l.get j) 1) := by
    rw [P.iteratedFDeriv_comp_right (f := (f : E → ℂ)) f.smooth' (x, 0) (by simp),
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    let eval (s : Σ n, Fin n → X) :=
      iteratedFDeriv ℝ s.1 f x (fun j ↦ P (s.2 j))
    have hl : l.map lift = List.ofFn (lift ∘ l.get) := by
      rw [← List.map_ofFn, List.ofFn_get]
    change eval (List.equivSigmaTuple (l.map lift)) = _
    rw [hl]
    exact congrArg eval (List.equivSigmaTuple.apply_symm_apply ⟨l.length, lift ∘ l.get⟩)
  exact congrArg (_ * ·) (hderiv directions)

/-- The weight in the Euclidean convergence criterion adds the unweighted derivative norm. -/
private theorem euclideanSchwartzWeightedDeriv_eq_norms {m : ℕ} (α β : Fin m → ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ)) (x : EuclideanSpace ℝ (Fin m)) :
    euclideanSchwartzWeightedDeriv α β f x =
      ‖euclideanSchwartzMonomialPartial 0 β f x‖ +
        ‖euclideanSchwartzMonomialPartial α β f x‖ := by
  rw [euclideanSchwartzMonomialPartial_eq, euclideanSchwartzMonomialPartial_eq]
  simp [euclideanSchwartzWeightedDeriv, one_add_mul, ← Real.norm_eq_abs, norm_prod]

open Filter in
/-- Paper: Example D.1.10.3, p. 785. Supremum norms of the monomial-weighted
Euclidean partials generate the usual Schwartz topology. -/
theorem euclideanSchwartz_monomialSup_generates (m : ℕ) (hm : 1 ≤ m) :
    GeneratesSeminormTopology (fun i : (Fin m → ℕ) × (Fin m → ℕ) ↦
      fun f : 𝓢(EuclideanSpace ℝ (Fin m), ℂ) ↦
        ⨆ x, (‖euclideanSchwartzMonomialPartial i.1 i.2 f x‖₊ : ℝ≥0∞)) := by
  let E := EuclideanSpace ℝ (Fin m)
  let S := 𝓢(E, ℂ)
  let I := (Fin m → ℕ) × (Fin m → ℕ)
  -- Pull back the seminorms of the elementary space with only Euclidean coordinates.
  let A : S →ₗ[ℂ] elementarySchwartzSubmodule m 0 0 PUnit.{1} :=
    { toFun := fun f ↦ ⟨fun g ↦ f g.1, (elementarySchwartzSubmodule_real_iff _).mpr ⟨f, rfl⟩⟩
      map_add' := fun _ _ ↦ Subtype.ext rfl
      map_smul' := fun _ _ ↦ Subtype.ext rfl }
  let index (i : I) : ElementarySchwartzIndex m 0 0 := (i.1, i.2, 0, 0)
  let P : SeminormFamily ℂ S I := fun i ↦ (elementarySchwartzSeminorm (index i)).comp A
  have hvalues (i : I) (f : S) :
      ENNReal.ofReal (P i f) = ⨆ x, (‖euclideanSchwartzMonomialPartial i.1 i.2 f x‖₊ : ℝ≥0∞) := by
    change ENNReal.ofReal (elementarySchwartzBound (A f).val (index i)).toReal = _
    rw [ENNReal.ofReal_toReal ((A f).property.2 (index i)).ne]
    have hfiber (xt : E × EuclideanSpace ℝ (Fin 0)) (a : Fin 0 → ℤ) (b : PUnit) :
        ((∏ k, (xt.1 k : ℂ) ^ (index i).1 k) * (∏ k, (a k : ℂ) ^ (index i).2.2.2 k)) *
          elementaryPartial (A f).val (index i).2.1 (index i).2.2.1 xt a b =
            euclideanSchwartzMonomialPartial i.1 i.2 f xt.1 := by
      obtain ⟨x, t⟩ := xt
      obtain rfl : t = 0 := Subsingleton.elim _ _
      obtain rfl : a = 0 := Subsingleton.elim _ _
      cases b
      simp only [Finset.univ_eq_empty (α := Fin 0), Finset.prod_empty, mul_one]
      rfl
    let b (x : E) : ℝ≥0∞ := ‖euclideanSchwartzMonomialPartial i.1 i.2 f x‖₊
    calc
      _ = ⨆ (xt : E × EuclideanSpace ℝ (Fin 0)) (_ : Fin 0 → ℤ) (_ : PUnit), b xt.1 :=
        iSup_congr fun xt ↦ iSup_congr fun a ↦ iSup_congr fun p ↦
          congrArg (fun z : ℂ ↦ (‖z‖₊ : ℝ≥0∞)) (hfiber xt a p)
      _ = _ := by
        simp only [iSup_const]
        exact (show Surjective (Prod.fst : E × EuclideanSpace ℝ (Fin 0) → E) from
          fun x ↦ ⟨(x, 0), rfl⟩).iSup_comp b
  have hbound (i : I) (f : S) {c : ℝ} (hc : 0 ≤ c) :
      P i f ≤ c ↔ ∀ x, ‖euclideanSchwartzMonomialPartial i.1 i.2 f x‖ ≤ c := by
    rw [← ENNReal.ofReal_le_ofReal_iff hc, hvalues, iSup_le_iff]
    simp only [ENNReal.coe_nnreal_eq, coe_nnNorm, ENNReal.ofReal_le_ofReal_iff hc]
  have hle (i : I) (f : S) (x : E) :
      ‖euclideanSchwartzMonomialPartial i.1 i.2 f x‖ ≤ P i f :=
    (hbound i f (apply_nonneg (P i) f)).mp le_rfl x
  refine ⟨P, ?_, hvalues⟩
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
  let lP : Filter S := ⨅ i, (𝓝 (0 : ℝ)).comap (P i)
  have hP (l : Filter S) :
      l ≤ lP ↔ ∀ (i : I) ε, 0 < ε → ∀ᶠ f in l, P i f < ε := by
    simp only [lP, le_iInf_iff, ← Filter.map_le_iff_le_comap]
    change (∀ i, Tendsto (P i) l (𝓝 0)) ↔ _
    simp only [Metric.tendsto_nhds, Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg (P _) _)]
  -- The two convergence criteria give the same neighborhood filter at zero.
  have ht (l : Filter S) : l ≤ 𝓝 (0 : S) ↔ l ≤ lP := by
    refine Filter.tendsto_id'.symm.trans
      ((schwartzMap_euclidean_tendsto_iff (m := m) l (id : S → S) 0).trans ?_)
    refine Iff.trans ?_ (hP l).symm
    simp only [id_eq, FunLike.coe_zero, sub_zero]
    constructor
    · intro h i ε hε
      filter_upwards [h i.1 i.2 (ε / 2) (half_pos hε)] with f hf
      apply ((hbound i f (half_pos hε).le).mpr fun x ↦ ?_).trans_lt (half_lt_self hε)
      have hfx := hf x
      rw [euclideanSchwartzWeightedDeriv_eq_norms] at hfx
      exact ((le_add_of_nonneg_left (norm_nonneg _)).trans_lt hfx).le
    · intro h α β ε hε
      filter_upwards [h (0, β) (ε / 2) (half_pos hε), h (α, β) (ε / 2) (half_pos hε)]
        with f hf₀ hf x
      rw [euclideanSchwartzWeightedDeriv_eq_norms]
      exact (add_lt_add ((hle (0, β) f x).trans_lt hf₀)
        ((hle (α, β) f x).trans_lt hf)).trans_eq (add_halves ε)
  exact le_antisymm ((ht _).mp le_rfl) ((ht _).mpr le_rfl)

section EuclideanSchwartzLp

open LineDeriv SchwartzMap

local notation "Euc[" m "]" => EuclideanSpace ℝ (Fin m)
local notation "Sch[" m "]" => 𝓢(Euc[m], ℂ)

private def coordDirections {m : ℕ} (β : Fin m → ℕ) : List (Euc[m]) :=
  (List.ofFn fun i ↦ List.replicate (β i) (EuclideanSpace.single i 1)).flatten

private def monomialPartialCLM {m : ℕ} (α β : Fin m → ℕ) : Sch[m] →L[ℂ] Sch[m] :=
  SchwartzMap.smulLeftCLM ℂ (fun x : Euc[m] ↦ ∏ i, (x i : ℂ) ^ α i) ∘L
    iteratedLineDerivOpCLM ℂ (Sch[m]) (coordDirections β).get

private theorem monomial_hasTemperateGrowth {m : ℕ} (α : Fin m → ℕ) :
    (fun x : Euc[m] ↦ ∏ i, (x i : ℂ) ^ α i).HasTemperateGrowth := by
  generalize Finset.univ (α := Fin m) = s
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact HasTemperateGrowth.const _
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    have h := (Complex.ofRealCLM.comp (EuclideanSpace.proj i)).hasTemperateGrowth
    exact HasTemperateGrowth.fun_mul (HasTemperateGrowth.fun_pow h (α i)) ih

private theorem monomialPartialCLM_apply {m : ℕ} (α β : Fin m → ℕ) (f : Sch[m]) :
    (monomialPartialCLM α β f : Euc[m] → ℂ) = euclideanSchwartzMonomialPartial α β f := by
  funext x
  simp only [monomialPartialCLM, ContinuousLinearMap.comp_apply, iteratedLineDerivOpCLM_apply,
    smulLeftCLM_apply_apply (monomial_hasTemperateGrowth α), smul_eq_mul,
    iteratedLineDerivOp_eq_iteratedFDeriv, euclideanSchwartzMonomialPartial]
  congr 1
  let L : Euc[m] × Euc[0] →L[ℝ] Euc[m] := ContinuousLinearMap.fst ℝ (Euc[m]) (Euc[0])
  let d : List (Euc[m] × Euc[0]) :=
    (List.ofFn fun i : Fin m ↦ List.replicate (β i) (EuclideanSpace.single i 1, 0)).flatten
  have hzero : (List.ofFn fun i : Fin 0 ↦ List.replicate ((0 : Fin 0 → ℕ) i)
      ((0 : Euc[m]), EuclideanSpace.single i (1 : ℝ))).flatten = [] := rfl
  unfold elementaryPartial
  dsimp only
  have hdirs : d ++ (List.ofFn fun i : Fin 0 ↦ List.replicate ((0 : Fin 0 → ℕ) i)
      ((0 : Euc[m]), EuclideanSpace.single i (1 : ℝ))).flatten = d := by
    rw [hzero, List.append_nil]
  refine Eq.trans ?_ (congrArg (fun w : List (Euc[m] × Euc[0]) ↦
    iteratedFDeriv ℝ w.length ((f : Euc[m] → ℂ) ∘ L) (x, 0) w.get) hdirs).symm
  change iteratedFDeriv ℝ (coordDirections β).length f x (coordDirections β).get =
    iteratedFDeriv ℝ d.length ((f : Euc[m] → ℂ) ∘ L) (x, 0) d.get
  rw [L.iteratedFDeriv_comp_right (f.smooth ⊤) _ (by simp)]
  change _ = iteratedFDeriv ℝ d.length f x (fun i ↦ L (d.get i))
  have hd : d.map L = coordDirections β := by
    simp only [d, coordDirections, List.map_flatten, List.map_ofFn]
    congr 2
    funext i
    simp [List.map_replicate, L]
  rw [← hd]
  have hg : (d.map L).get = fun i ↦ L (d.get (i.cast (List.length_map L))) := by
    funext i
    simp [List.get_eq_getElem]
  rw [hg]
  have hcast {n k : ℕ} (h : n = k) (v : Fin k → Euc[m]) :
      iteratedFDeriv ℝ n f x (fun i ↦ v (i.cast h)) = iteratedFDeriv ℝ k f x v := by
    subst n
    rfl
  exact hcast (List.length_map L) (fun i ↦ L (d.get i))

/-- The closed unit cube with lower corner `x`, in Euclidean coordinates. -/
private def unitCube {m : ℕ} (x : Euc[m]) : Set Euc[m] :=
  WithLp.ofLp ⁻¹' Icc (WithLp.ofLp x) (fun j ↦ x j + 1)

/-- Integrating the norm of a Schwartz function over a unit cube is bounded by
its global Lᵖ norm, by Hölder on a set of measure one. -/
private theorem unitCube_integral_norm_le_toLp {m : ℕ} (x : Euc[m]) (g : Sch[m])
    (q : ℝ≥0∞) (hq : 1 ≤ q) :
    (∫ y in unitCube x, ‖g y‖) ≤ ‖g.toLp q volume‖ := by
  let ν := (volume : Measure Euc[m]).restrict (unitCube x)
  have hvol : ν univ = 1 := by
    rw [show ν univ = volume (unitCube x) from Measure.restrict_apply_univ _, unitCube,
      (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage measurableSet_Icc.nullMeasurableSet,
      Real.volume_Icc_pi]
    simp
  have hg : AEStronglyMeasurable (g : Euc[m] → ℂ) ν :=
    g.continuous.aestronglyMeasurable
  have hle : eLpNorm (g : Euc[m] → ℂ) 1 ν ≤ eLpNorm (g : Euc[m] → ℂ) q volume := by
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq hg).trans ?_
    rw [hvol, ENNReal.one_rpow, mul_one]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  rw [SchwartzMap.norm_toLp, integral_norm_eq_lintegral_eNorm hg,
    ← eLpNorm_one_eq_lintegral_eNorm hg]
  exact ENNReal.toReal_mono (g.eLpNorm_lt_top q volume).ne hle

/-- The multi-index with a derivative in each coordinate of `s` and order zero elsewhere. -/
private def squarefreeMultiIndex {m : ℕ} (s : Finset (Fin m)) : Fin m → ℕ :=
  fun j ↦ if j ∈ s then 1 else 0

/-- Evaluation at the lower corner of a unit cube is bounded by the integrals
of the square-free partials over that cube. In one variable this is the
fundamental theorem of calculus averaged over the unit interval. In multiple
variables the one-variable bounds are iterated using Fubini. -/
private theorem euclideanSchwartz_norm_le_unitCube_integrals {m : ℕ} (g : Sch[m]) (x : Euc[m]) :
    ‖g x‖ ≤ ∑ s : Finset (Fin m),
      ∫ y in unitCube x, ‖euclideanSchwartzMonomialPartial 0 (squarefreeMultiIndex s) g y‖ := by
  sorry

/-- The square-free partial in coordinates `s` of a monomial-weighted partial,
expanded by the product rule. Each subset `t` lists the coordinates in which
the derivative acts on the monomial. -/
private theorem euclideanSchwartz_monomialPartial_leibniz {m : ℕ}
    (α β : Fin m → ℕ) (s : Finset (Fin m)) (f : Sch[m]) (y : Euc[m]) :
    euclideanSchwartzMonomialPartial 0 (squarefreeMultiIndex s) (monomialPartialCLM α β f) y =
      ∑ t ∈ s.powerset, (∏ j ∈ t, (α j : ℂ)) *
        euclideanSchwartzMonomialPartial (α - squarefreeMultiIndex t)
          (β + squarefreeMultiIndex (s \ t)) f y := by
  sorry

/-- The unit-cube evaluation bound for a monomial-weighted partial, with each
term expressed as the integral of another monomial-weighted partial. -/
private theorem euclideanSchwartz_monomialPartial_le_unitCube_integrals {m : ℕ}
    (α β : Fin m → ℕ) (f : Sch[m]) (x : Euc[m]) :
    ‖euclideanSchwartzMonomialPartial α β f x‖ ≤
      ∑ s : Finset (Fin m), ∑ t ∈ s.powerset, (∏ j ∈ t, (α j : ℝ)) *
        ∫ y in unitCube x,
          ‖euclideanSchwartzMonomialPartial (α - squarefreeMultiIndex t)
            (β + squarefreeMultiIndex (s \ t)) f y‖ := by
  rw [← monomialPartialCLM_apply]
  apply (euclideanSchwartz_norm_le_unitCube_integrals _ x).trans
  refine Finset.sum_le_sum fun s _ ↦ ?_
  let a (t : Finset (Fin m)) : ℝ := ∏ j ∈ t, (α j : ℝ)
  let g (t : Finset (Fin m)) :=
    monomialPartialCLM (α - squarefreeMultiIndex t) (β + squarefreeMultiIndex (s \ t)) f
  have hint (t : Finset (Fin m)) :
      IntegrableOn (fun y ↦ a t * ‖g t y‖) (unitCube x) volume :=
    ((g t).integrable.norm.const_mul (a t)).integrableOn
  simp_rw [← monomialPartialCLM_apply]
  change _ ≤ ∑ t ∈ s.powerset, a t * ∫ y in unitCube x, ‖g t y‖
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun t _ ↦ hint t)]
  refine integral_mono (monomialPartialCLM 0 (squarefreeMultiIndex s)
    (monomialPartialCLM α β f)).integrable.norm.integrableOn
    (integrable_finsetSum _ fun t _ ↦ hint t) (fun y ↦ ?_)
  rw [show (monomialPartialCLM 0 (squarefreeMultiIndex s) (monomialPartialCLM α β f)) y =
      _ from congrFun (monomialPartialCLM_apply ..) y, euclideanSchwartz_monomialPartial_leibniz]
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum fun t _ ↦ by
    simp [a, g, monomialPartialCLM_apply, norm_prod]

/-- Paper: Example D.1.10.3(1)–(2), p. 785. For every real p at least one,
the Lᵖ norms of the monomial-weighted Euclidean partials generate the topology.
Deviation: The same statement includes p = 1 and p > 1. -/
theorem euclideanSchwartz_monomialLp_generates (m : ℕ) (hm : 1 ≤ m) (p : ℝ) (hp : 1 ≤ p) :
    GeneratesLpSeminorms (volume : Measure (EuclideanSpace ℝ (Fin m))) (ENNReal.ofReal p)
      (fun i : (Fin m → ℕ) × (Fin m → ℕ) ↦ euclideanSchwartzMonomialPartial i.1 i.2) := by
  classical
  let q := ENNReal.ofReal p
  have hq : 1 ≤ q := by simpa [q] using ENNReal.ofReal_le_ofReal hp
  let : Fact (1 ≤ q) := ⟨hq⟩
  let U (i : (Fin m → ℕ) × (Fin m → ℕ)) :=
    SchwartzMap.toLpCLM ℂ ℂ q (volume : Measure Euc[m]) ∘L monomialPartialCLM i.1 i.2
  let P (i : (Fin m → ℕ) × (Fin m → ℕ)) :=
    (normSeminorm ℂ (Lp ℂ q (volume : Measure Euc[m]))).comp (U i).toLinearMap
  have hP (i : (Fin m → ℕ) × (Fin m → ℕ)) (f : Sch[m]) :
      P i f = ‖(monomialPartialCLM i.1 i.2 f).toLp q volume‖ := by
    change ‖(U i) f‖ = _
    rw [ContinuousLinearMap.comp_apply, SchwartzMap.toLpCLM_apply]
  refine ⟨?_, ⟨P, ?_, ?_⟩⟩
  · intro i f
    change MemLp (euclideanSchwartzMonomialPartial i.1 i.2 f) q volume
    rw [← monomialPartialCLM_apply]
    exact (monomialPartialCLM i.1 i.2 f).memLp q volume
  · obtain ⟨Q, hQ, hvalues⟩ := euclideanSchwartz_monomialSup_generates m hm
    refine hQ.congr (fun i ↦ ?_) (Seminorm.IsBounded.of_real fun i ↦ ?_)
    · obtain ⟨s, C, _, h⟩ := Seminorm.bound_of_continuous hQ (P i)
        ((U i).continuous.norm : Continuous fun f ↦ ‖U i f‖)
      exact ⟨s, C, h⟩
    · let index (s t : Finset (Fin m)) :=
        (i.1 - squarefreeMultiIndex t, i.2 + squarefreeMultiIndex (s \ t))
      let support := (Finset.univ : Finset (Finset (Fin m) × Finset (Fin m))).image
        (fun j ↦ index j.1 j.2)
      let C : ℝ := ∑ s : Finset (Fin m), ∑ t ∈ s.powerset, ∏ j ∈ t, (i.1 j : ℝ)
      have hC : 0 ≤ C := by
        dsimp [C]
        positivity
      refine ⟨support, C, fun f ↦ ?_⟩
      have hterm (s t : Finset (Fin m)) :
          P (index s t) f ≤ support.sup P f :=
        Seminorm.le_finset_sup_apply (Finset.mem_image.mpr ⟨(s, t), Finset.mem_univ _, rfl⟩)
      have hle (x : Euc[m]) : ‖euclideanSchwartzMonomialPartial i.1 i.2 f x‖ ≤
          C * support.sup P f := calc
        _ ≤ _ := euclideanSchwartz_monomialPartial_le_unitCube_integrals i.1 i.2 f x
        _ ≤ ∑ s : Finset (Fin m), ∑ t ∈ s.powerset, (∏ j ∈ t, (i.1 j : ℝ)) *
            support.sup P f := by
          refine Finset.sum_le_sum fun s _ ↦ Finset.sum_le_sum fun t _ ↦ ?_
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          change (∫ y in unitCube x, ‖euclideanSchwartzMonomialPartial
            (index s t).1 (index s t).2 f y‖) ≤ support.sup P f
          rw [← monomialPartialCLM_apply]
          exact (unitCube_integral_norm_le_toLp x _ q hq).trans
            ((hP (index s t) f).symm ▸ hterm s t)
        _ = _ := by simp only [C, Finset.sum_mul]
      apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (apply_nonneg _ _))).mp
      rw [LinearMap.id_apply, hvalues]
      exact iSup_le fun x ↦ by
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal (hle x)
  · intro i f
    rw [hP, SchwartzMap.norm_toLp,
      ENNReal.ofReal_toReal ((monomialPartialCLM i.1 i.2 f).eLpNorm_lt_top q volume).ne,
      monomialPartialCLM_apply]

end EuclideanSchwartzLp

/-- Paper: (D.1.10.9)–(D.1.10.10), p. 785. On the torus take the mixed partial
by differentiating the periodic lift.
Deviation: We evaluate the lifted partial at the representative in the unit cube. -/
def torusSchwartzPartial {n : ℕ} (β : Fin n → ℕ)
    (f : ElementarySchwartz 0 n 0 PUnit) (z : Fin n → AddCircle (1 : ℝ)) : ℂ :=
  elementaryPartial f 0 β
    (0, WithLp.toLp 2 (fun i ↦ (AddCircle.equivIco (1 : ℝ) 0 (z i)).val)) 0 PUnit.unit

/-- Paper: (D.1.10.9)–(D.1.10.10), p. 785. The partial of order zero evaluates
the original function on the torus.
Deviation: Sanity check for the chosen lift. -/
theorem torusSchwartzPartial_zero {n : ℕ}
    (f : ElementarySchwartz 0 n 0 PUnit) (z : Fin n → AddCircle (1 : ℝ)) :
    torusSchwartzPartial 0 f z = f (0, z, 0, PUnit.unit) := by
  rw [torusSchwartzPartial, elementaryPartial_zero]
  have hz : (fun i ↦ (((AddCircle.equivIco (1 : ℝ) 0 (z i)).val : ℝ) : AddCircle (1 : ℝ))) = z :=
    funext fun i ↦ (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (z i)
  simp only [elementaryCover]
  rw [hz]

/-- Paper: Example D.1.10.4, p. 785. Supremum norms of the torus partials
generate the smooth topology. -/
theorem torusSchwartz_sup_generates (n : ℕ) (hn : 1 ≤ n) :
    GeneratesSeminormTopology (fun β : Fin n → ℕ ↦
      fun f : ElementarySchwartz 0 n 0 PUnit ↦
        ⨆ z, (‖torusSchwartzPartial β f z‖₊ : ℝ≥0∞)) := by
  let idx (β : Fin n → ℕ) : ElementarySchwartzIndex 0 n 0 := (0, 0, β, 0)
  have hidx (i : ElementarySchwartzIndex 0 n 0) : idx i.2.2.1 = i := by
    rcases i with ⟨a, b, c, d⟩
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    have hd : d = 0 := Subsingleton.elim _ _
    subst a; subst b; subst d
    rfl
  have hbound (β : Fin n → ℕ) (f : ElementarySchwartz 0 n 0 PUnit) :
      elementarySchwartzBound f.val (idx β) =
        ⨆ z, (‖torusSchwartzPartial β f z‖₊ : ℝ≥0∞) := by
    simp only [elementarySchwartzBound, idx, Finset.univ_eq_empty (α := Fin 0),
      Finset.prod_empty, one_mul]
    apply le_antisymm
    · refine iSup_le fun xt ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
      have ha : a = 0 := Subsingleton.elim _ _
      have hb : b = PUnit.unit := Subsingleton.elim _ _
      subst a; subst b
      let z : Fin n → AddCircle (1 : ℝ) := fun i ↦ (xt.2 i : AddCircle (1 : ℝ))
      have heq : elementaryPartial f.val 0 β xt 0 PUnit.unit = torusSchwartzPartial β f z := by
        unfold torusSchwartzPartial
        apply (elementaryPartial_descends f.val 0 β 0 PUnit.unit (f.property.1 0 PUnit.unit)).2
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · simp only [elementaryCover]
          apply Prod.ext
          · apply funext
            intro i
            exact ((AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (z i)).symm
          · rfl
      rw [heq]
      exact le_iSup (fun z ↦ (‖torusSchwartzPartial β f z‖₊ : ℝ≥0∞)) z
    · refine iSup_le fun z ↦ ?_
      exact le_iSup_of_le (0, WithLp.toLp 2 (fun i ↦ (AddCircle.equivIco (1 : ℝ) 0 (z i)).val))
        (le_iSup_of_le 0 (le_iSup_of_le PUnit.unit le_rfl))
  refine ⟨fun β ↦ elementarySchwartzSeminorm (idx β), ?_, ?_⟩
  · let e : (Fin n → ℕ) ≃ ElementarySchwartzIndex 0 n 0 :=
      Equiv.ofBijective idx ⟨fun a b h ↦ congrArg (fun i : ElementarySchwartzIndex 0 n 0 ↦ i.2.2.1) h,
        fun i ↦ ⟨i.2.2.1, hidx i⟩⟩
    exact (elementarySchwartz_withSeminorms (m := 0) (n := n) (r := 0) (F := PUnit)).congr_equiv e
  · intro β f
    change ENNReal.ofReal (elementarySchwartzBound f.val (idx β)).toReal = _
    rw [ENNReal.ofReal_toReal (f.property.2 (idx β)).ne, hbound]

/-- Paper: Example D.1.10.4, p. 785. With product probability Haar measure, the Lᵖ
norms of torus partials generate the smooth topology for each finite real p ≥ 1.
Deviation: The stage with only torus coordinates represents the smooth space. -/
theorem torusSchwartz_lp_generates (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp : 1 ≤ p) :
    GeneratesLpSeminorms (Measure.pi (fun _ : Fin n ↦ AddCircle.haarAddCircle (T := (1 : ℝ))))
      (ENNReal.ofReal p) (torusSchwartzPartial (n := n)) := by sorry

/-- Paper: (D.1.10.12), p. 786. Multiply a rapidly decreasing sequence
by the integer coordinate monomial. -/
def latticeSchwartzMonomial {r : ℕ} (γ : Fin r → ℕ)
    (f : RapidDecaySequence r) (a : Fin r → ℤ) : ℂ :=
  (∏ i, (a i : ℂ) ^ γ i) * f a

/-- Paper: (D.1.10.12), p. 786. The zero weight leaves the sequence unchanged.
Deviation: Sanity check on the weight. -/
theorem latticeSchwartzMonomial_zero {r : ℕ} (f : RapidDecaySequence r) (a : Fin r → ℤ) :
    latticeSchwartzMonomial 0 f a = f a := by
  simp [latticeSchwartzMonomial]

/-- Paper: Example D.1.10.5, p. 786. The weighted sup norms generate the
rapidly decreasing sequence topology on the integer lattice. -/
theorem latticeSchwartz_sup_generates (r : ℕ) :
    GeneratesSeminormTopology (fun γ : Fin r → ℕ ↦ fun f : RapidDecaySequence r ↦
      ⨆ a, (‖latticeSchwartzMonomial γ f a‖₊ : ℝ≥0∞)) := by sorry

/-- Paper: Example D.1.10.5, p. 786. The counting-measure Lᵖ seminorms of
the monomial-weighted sequences generate the rapidly decreasing sequence topology. -/
theorem latticeSchwartz_lp_generates (r p : ℕ) (hp : 1 ≤ p) :
    GeneratesLpSeminorms (Measure.count : Measure (Fin r → ℤ)) (p : ℝ≥0∞)
      (latticeSchwartzMonomial (r := r)) := by sorry

end SchwartzTopologies

section ElementaryOperators

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Paper: Proposition D.1.10.6(3)–(4), p. 787. Repeat the first-order operator
in each direction according to its multi-index and compose the resulting operators. -/
def bruhatDiffMonomial {d : ℕ} (a : Fin d → LCATopologicalLie G) (α : Fin d → ℕ) :
    bruhatDiffAlgebra G :=
  bruhatDiffWord ((List.finRange d).flatMap fun j ↦ List.replicate (α j) (a j))

/-- Paper: Proposition D.1.10.6(3)–(4), p. 787. The multi-index of weight one in
one direction gives the corresponding first-order operator.
Deviation: Sanity check on repetition of directions. -/
theorem bruhatDiffMonomial_single {d : ℕ} (a : Fin d → LCATopologicalLie G) (j : Fin d) :
    bruhatDiffMonomial a (Pi.single j 1) = bruhatDiffGenerator (a j) := by
  rw [bruhatDiffMonomial, ← bruhatDiffWord_singleton]
  congr 1
  rw [← List.replicate_one, List.eq_replicate_iff]
  constructor
  · rw [List.length_flatMap]
    simp only [List.length_replicate]
    rw [← Fin.sum_univ_def]
    simp
  · intro x hx
    obtain ⟨i, -, hi⟩ := List.mem_flatMap.1 hx
    have hij : i = j := by
      by_contra h
      simp [Pi.single_eq_of_ne h] at hi
    subst hij
    exact List.eq_of_mem_replicate hi

/-- Paper: Proposition D.1.10.6(1)–(2), p. 787. Differentiate a Schwartz–Bruhat
function and multiply it by the symbol of the dual operator through biduality. -/
def bruhatDiffSymbolWeightedApply (b : G ≃ₜ* PontryaginDual (PontryaginDual G))
    (D : bruhatDiffAlgebra G) (E : bruhatDiffAlgebra (PontryaginDual G))
    (f : SchwartzBruhat G) (x : G) : ℂ :=
  bruhatDiffSymbol E (b x) *
    (D.val ⟨f, (mem_bruhatSmoothSubmodule_iff _).2 (schwartzBruhat_isBruhatSmooth f)⟩).val x

/-- Paper: Proposition D.1.10.6(1)–(2), p. 787. Applying the pair of identity
operators returns the original function.
Deviation: Sanity check on the symbol and application conventions. -/
theorem bruhatDiffSymbolWeightedApply_one
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (f : SchwartzBruhat G) :
    bruhatDiffSymbolWeightedApply b 1 1 f = (f : G → ℂ) := by
  funext x
  simp [bruhatDiffSymbolWeightedApply, bruhatDiffSymbol_one]

variable (e : ElementaryLCAPresentation G)
variable (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (hb : ∀ x χ, b x χ = χ x)

include e hb

/-- Paper: Proposition D.1.10.6(1), p. 787. The sup norms of the symbol-weighted
derivatives for arbitrary pairs of invariant operators generate the Schwartz topology. -/
theorem elementarySchwartz_operatorSup_generates :
    GeneratesSeminormTopology (fun i : bruhatDiffAlgebra G × bruhatDiffAlgebra (PontryaginDual G) ↦
      fun f : SchwartzBruhat G ↦
        ⨆ x, (‖bruhatDiffSymbolWeightedApply b i.1 i.2 f x‖₊ : ℝ≥0∞)) := by sorry

/-- Paper: Proposition D.1.10.6(2), p. 787. For each integer q at least one,
the Lᵠ norms of the symbol-weighted derivatives generate the Schwartz topology. -/
theorem elementarySchwartz_operatorLp_generates [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (q : ℕ) (hq : 1 ≤ q) :
    GeneratesLpSeminorms μ (q : ℝ≥0∞)
      (fun i : bruhatDiffAlgebra G × bruhatDiffAlgebra (PontryaginDual G) ↦
        bruhatDiffSymbolWeightedApply b i.1 i.2) := by sorry

variable {d d' : ℕ}
variable (a : Fin d → LCATopologicalLie G) (a' : Fin d' → LCATopologicalLie (PontryaginDual G))
variable
  (ha : LinearIndependent ℝ (fun j ↦ bruhatFirstOrder (a j)))
  (hspan : Submodule.span ℝ (range (fun j ↦ bruhatFirstOrder (a j))) =
    bruhatDiffDegreeOneReal (G := G))
  (ha' : LinearIndependent ℝ (fun j ↦ bruhatFirstOrder (a' j)))
  (hspan' : Submodule.span ℝ (range (fun j ↦ bruhatFirstOrder (a' j))) =
    bruhatDiffDegreeOneReal (G := PontryaginDual G))

include ha hspan ha' hspan'

/-- Paper: Proposition D.1.10.6(3), p. 787. The monomials in any pair of real
first-order bases suffice for the sup family. -/
theorem elementarySchwartz_basisSup_generates :
    GeneratesSeminormTopology (fun i : (Fin d → ℕ) × (Fin d' → ℕ) ↦
      fun f : SchwartzBruhat G ↦ ⨆ x,
        (‖bruhatDiffSymbolWeightedApply b (bruhatDiffMonomial a i.1)
          (bruhatDiffMonomial a' i.2) f x‖₊ : ℝ≥0∞)) := by sorry

/-- Paper: Proposition D.1.10.6(4), p. 787. The monomials in any pair of real
first-order bases suffice for each finite integer Lᵠ family. -/
theorem elementarySchwartz_basisLp_generates [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (q : ℕ) (hq : 1 ≤ q) :
    GeneratesLpSeminorms μ (q : ℝ≥0∞)
      (fun i : (Fin d → ℕ) × (Fin d' → ℕ) ↦
        bruhatDiffSymbolWeightedApply b (bruhatDiffMonomial a i.1)
          (bruhatDiffMonomial a' i.2)) := by sorry

-- TODO(paper-gap): On p. 789 the proof uses convergence in the new seminorm
-- to identify its value at the limit before proving its continuity.

end ElementaryOperators

section IdeleClassSeminorms

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Paper: Proposition D.1.10.7, p. 789. Realize the space of k-invariant
Schwartz–Bruhat functions as a submodule with the inherited topology. -/
def schwartzBruhatInvariantSubmodule (k : Subgroup G) : Submodule ℂ (SchwartzBruhat G) :=
  let ev (x : G) : SchwartzBruhat G →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  ⨅ (g : G) (u : k), (ev (g * u.val) - ev g).ker

/-- Paper: Proposition D.1.10.7, p. 789. The fixed submodule consists exactly
of the functions invariant under translation by the subgroup.
Deviation: Sanity check on the fixed subspace used for S(k,G). -/
theorem mem_schwartzBruhatInvariantSubmodule_iff
    (k : Subgroup G) (f : SchwartzBruhat G) :
    f ∈ schwartzBruhatInvariantSubmodule k ↔
      ∀ (x : G) (u : k), f (x * u.val) = f x := by
  simp only [schwartzBruhatInvariantSubmodule, Submodule.mem_iInf]
  refine forall_congr' fun x ↦ forall_congr' fun u ↦ ?_
  rw [LinearMap.mem_ker]
  exact sub_eq_zero

/-- Paper: (D.1.10.15), p. 789. Apply the compact-direction derivatives and the
derivatives along the norm section, then multiply by a weight in the absolute log norm.
Deviation: The radial derivatives use the exponential coordinate, so differentiation
with respect to its parameter is the operator t∂t. -/
def ideleClassWeightedDeriv {d : ℕ} (n : G →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G)
    (γ : Fin d → LCATopologicalLie n.ker) (m : ℕ) (α : Fin d → ℕ) (weight : ℝ → ℝ)
    (f : SchwartzBruhat G) (t : ℝ≥0ˣ) (x : G) : ℂ :=
  let j : n.ker →ₜ* G := ⟨n.ker.subtype, continuous_subtype_val⟩
  let D := bruhatDiffMonomial (fun i ↦ j.comp (γ i)) α
  let Df := D.val ⟨f, (mem_bruhatSmoothSubmodule_iff _).2 (schwartzBruhat_isBruhatSmooth f)⟩
  (weight |Real.log (t.val : ℝ)| : ℂ) *
    iteratedDeriv m (fun s : ℝ ↦
      Df.val (τ (Units.mk0 (Real.exp s).toNNReal
        (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos s)))) * x)) 0

/-- The monomial of multi-index zero is the identity operator. -/
theorem bruhatDiffMonomial_zero {d : ℕ} (a : Fin d → LCATopologicalLie G) :
    bruhatDiffMonomial a 0 = 1 := by
  have h : (List.finRange d).flatMap (fun j ↦ List.replicate ((0 : Fin d → ℕ) j) (a j)) = [] :=
    List.flatMap_eq_nil_iff.2 (by simp)
  rw [bruhatDiffMonomial, h]
  rfl

/-- Paper: (D.1.10.15), p. 789. At zero differential orders the result is the
value of the original function multiplied by the weight in the absolute log norm.
Deviation: Sanity check on the derivatives and the argument of the weight. -/
theorem ideleClassWeightedDeriv_zero {d : ℕ} (n : G →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G)
    (γ : Fin d → LCATopologicalLie n.ker) (weight : ℝ → ℝ) (f : SchwartzBruhat G)
    (t : ℝ≥0ˣ) (x : G) :
    ideleClassWeightedDeriv n τ γ 0 0 weight f t x =
      (weight |Real.log (t.val : ℝ)| : ℂ) * f x := by
  simp only [ideleClassWeightedDeriv, iteratedDeriv_zero, bruhatDiffMonomial_zero]
  congr 1
  have h1 : Units.mk0 (Real.exp 0).toNNReal
      (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos 0))) = (1 : ℝ≥0ˣ) :=
    Units.ext (by simp)
  rw [h1, map_one, one_mul]
  rfl

universe u

variable (F : Type u) [Field F] [NumberField F]

local instance : T2Space C[F] := (ideleGroup_quotient.{u, 0} F).2.2.2.2.2.1
local instance : LocallyCompactSpace C[F] := (ideleGroup_quotient.{u, 0} F).2.2.2.2.2.2.1

local notation "C₀[" F "]" => Subgroup.connectedComponentOfOne C[F]
local notation "C₁[" F "]" => MonoidHom.ker (ideleClassNorm F)
local notation "d[" F "]" => (Module.finrank ℚ F - 1)

local instance : LocallyCompactSpace C₀[F] := isClosed_connectedComponent.locallyCompactSpace
local instance : LocallyCompactSpace C₁[F] :=
  (ideleClassGroup_finiteness F).1.locallyCompactSpace

/-- Paper: Proposition D.1.10.7, p. 789. On all sufficiently small compact
good-subgroup stages of the identity component, weighted sup norms of the radial
and norm-one directional derivatives generate the Schwartz–Bruhat topology.
Deviation: The section and directions take values directly in the identity
component, since their domains are connected. The supremum is over all
representatives of the quotient. -/
theorem ideleClassComponent_weightedSup_generates
    (τ : ℝ≥0ˣ →ₜ* C₀[F]) (hτ : RightInverse τ ((ideleClassNorm F).comp (C₀[F]).subtype)) :
    let n := (ideleClassNorm F).comp (C₀[F]).subtype
    ∃ k₀ : Subgroup C₀[F], IsCompact (k₀ : Set C₀[F]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup C₀[F], k ≤ k₀ → IsCompact (k : Set C₀[F]) → IsBruhatGoodSubgroup k →
        ∃ γ : Fin d[F] → LCATopologicalLie n.ker,
          GeneratesSeminormTopology
            (fun i : ℕ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
              ⨆ x : C₀[F], (‖ideleClassWeightedDeriv n τ γ i.2.1 i.2.2
                (fun t ↦ 1 + t ^ i.1) f.val (n x) x‖₊ : ℝ≥0∞)) := by sorry

/-- Paper: Remark D.1.10.8, p. 789. Every continuous one-parameter subgroup
of the norm-one idele classes has image in their identity component. -/
theorem normOneIdeleClass_direction_mem_connectedComponent
    (γ : LCATopologicalLie C₁[F]) (t : ℝ) :
    γ (Multiplicative.ofAdd t) ∈ Subgroup.connectedComponentOfOne C₁[F] := by
  have : PreconnectedSpace (Multiplicative ℝ) := inferInstanceAs (PreconnectedSpace ℝ)
  exact (isPreconnected_range γ.continuous).subset_connectedComponent
    ⟨1, map_one γ⟩ ⟨_, rfl⟩

-- TODO(paper-gap): In D.1.10.9 the subgroup Γ is unbound. The stage S(k,C_F) in
-- the title and conclusion uses the full group, which is compactly generated.
-- TODO(paper-gap): On p. 791 the proof claims generation on the entire LF-space.
-- Over ℚ, fixed radial bumps times indicators of shrinking open subgroups of
-- the norm-one group tend to zero in the listed Lᵖ norms but retain their value at 1.

/-- Paper: (D.1.10.17) and (D.1.10.20), pp. 790–791. Evaluate the weighted
directional derivative in the product chart of a norm section and its kernel. -/
def ideleClassProductWeightedDeriv {d : ℕ} (n : G →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G)
    (γ : Fin d → LCATopologicalLie n.ker) (m : ℕ) (α : Fin d → ℕ) (weight : ℝ → ℝ)
    (f : SchwartzBruhat G) (z : ℝ≥0ˣ × n.ker) : ℂ :=
  ideleClassWeightedDeriv n τ γ m α weight f z.1 (τ z.1 * z.2.val)

/-- Paper: (D.1.10.17) and (D.1.10.20), pp. 790–791. At zero differential orders
and unit weight evaluation is at the idele class represented by the product chart.
Deviation: Sanity check on the section and kernel factors. -/
theorem ideleClassProductWeightedDeriv_zero {d : ℕ} (n : G →* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G)
    (γ : Fin d → LCATopologicalLie n.ker) (f : SchwartzBruhat G) (z : ℝ≥0ˣ × n.ker) :
    ideleClassProductWeightedDeriv n τ γ 0 0 (fun _ ↦ 1) f z = f (τ z.1 * z.2.val) := by
  rw [ideleClassProductWeightedDeriv, ideleClassWeightedDeriv_zero]
  simp

section Global
local instance : MeasurableSpace C[F] := borel _

variable (τ : ℝ≥0ˣ →ₜ* C[F]) (hτ : RightInverse τ (ideleClassNorm F))
variable (γ : Fin d[F] → LCATopologicalLie C₁[F])
variable
  (hγ : LinearIndependent ℝ (fun j ↦ bruhatFirstOrder (γ j)))
  (hspan : Submodule.span ℝ (range (fun j ↦ bruhatFirstOrder (γ j))) =
    bruhatDiffDegreeOneReal (G := C₁[F]))

include hτ hγ hspan

local notation "μ₁[" F "]" => positiveRealHaar.prod (normOneIdeleClassTamagawaMeasure F)

/-- Paper: Proposition D.1.10.9(1), p. 790. For sufficiently small compact
good subgroups, the weighted Lᵖ norms using one plus powers of the absolute
log norm generate the topology on the fixed subspace.
Deviation: The norm-one directions are specified by their real basis property
and the integration measure is the product in (D.1.10.17). -/
theorem ideleClass_weightedLp_generates :
    ∃ k₀ : Subgroup C[F], IsCompact (k₀ : Set C[F]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup C[F], k ≤ k₀ → IsCompact (k : Set C[F]) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → GeneratesLpSeminorms μ₁[F] (ENNReal.ofReal p)
          (fun i : ℕ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
            ideleClassProductWeightedDeriv (ideleClassNorm F) τ γ i.2.1 i.2.2
              (fun t ↦ 1 + t ^ i.1) f.val) := by sorry

/-- Paper: Proposition D.1.10.9(2), p. 790. Powers of the absolute log norm
alone give an Lᵖ seminorm family generating the same fixed-subspace topology.
Deviation: The norm-one directions are specified by their real basis property. -/
theorem ideleClass_logPowerLp_generates :
    ∃ k₀ : Subgroup C[F], IsCompact (k₀ : Set C[F]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup C[F], k ≤ k₀ → IsCompact (k : Set C[F]) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → GeneratesLpSeminorms μ₁[F] (ENNReal.ofReal p)
          (fun i : ℕ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
            ideleClassProductWeightedDeriv (ideleClassNorm F) τ γ i.2.1 i.2.2
              (fun t ↦ t ^ i.1) f.val) := by sorry

/-- Paper: Proposition D.1.10.9(3), p. 790. Absolute values of arbitrary complex
polynomials in the absolute log norm give a generating Lᵖ family on the fixed stage.
Deviation: The norm-one directions are specified by their real basis property. -/
theorem ideleClass_logPolynomialLp_generates :
    ∃ k₀ : Subgroup C[F], IsCompact (k₀ : Set C[F]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup C[F], k ≤ k₀ → IsCompact (k : Set C[F]) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → GeneratesLpSeminorms μ₁[F] (ENNReal.ofReal p)
          (fun i : Polynomial ℂ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
            ideleClassProductWeightedDeriv (ideleClassNorm F) τ γ i.2.1 i.2.2
              (fun t ↦ ‖i.1.eval (t : ℂ)‖) f.val) := by sorry

end Global

section SLocal

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Cₛ[" F ", " S "]" => SIdeleClassGroup F S
local notation "Cₛ₁[" F ", " S "]" => MonoidHom.ker (sIdeleClassNorm F S)

local instance : T2Space Cₛ[F, S] := (sIdeleClassNorm_descent F S).1
local instance : LocallyCompactSpace Cₛ[F, S] := (sIdeleClassNorm_descent F S).2.1
local instance : LocallyCompactSpace Cₛ₁[F, S] :=
  (sIdeleClassGroup_finiteness F S).1.locallyCompactSpace
local instance : MeasurableSpace Cₛ₁[F, S] := borel _

variable (τ : ℝ≥0ˣ →ₜ* Cₛ[F, S]) (hτ : RightInverse τ (sIdeleClassNorm F S))
variable (γ : Fin d[F] → LCATopologicalLie Cₛ₁[F, S])
variable
  (hγ : LinearIndependent ℝ (fun j ↦ bruhatFirstOrder (γ j)))
  (hspan : Submodule.span ℝ (range (fun j ↦ bruhatFirstOrder (γ j))) =
    bruhatDiffDegreeOneReal (G := Cₛ₁[F, S]))
variable (μ : Measure Cₛ₁[F, S]) [hμ : μ.IsHaarMeasure]

include hτ hγ hspan hμ

-- TODO(paper-gap): The normalization of the measure in (D.1.10.20) refers
-- to (A.3.4.1)(3), which omits the outside-S unit factors from the numerator.
-- The topology assertions below hold for any Haar measure on the full kernel.

/-- Paper: Proposition D.1.10.10(1), p. 791. For sufficiently small compact
good subgroups, the Lᵖ family with weights one plus powers of the absolute log
S-norm generates the fixed-subspace topology.
Deviation: The norm-one directions are specified by their real basis property
and the compact kernel carries any Haar measure. -/
theorem sIdeleClass_weightedLp_generates :
    ∃ k₀ : Subgroup Cₛ[F, S], IsCompact (k₀ : Set Cₛ[F, S]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup Cₛ[F, S], k ≤ k₀ → IsCompact (k : Set Cₛ[F, S]) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → GeneratesLpSeminorms (positiveRealHaar.prod μ) (ENNReal.ofReal p)
          (fun i : ℕ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
            ideleClassProductWeightedDeriv (sIdeleClassNorm F S) τ γ i.2.1 i.2.2
              (fun t ↦ 1 + t ^ i.1) f.val) := by sorry

/-- Paper: Proposition D.1.10.10(2), p. 791. Powers of the absolute log S-norm
give a generating family on the fixed subspace.
Deviation: The directions satisfy the real basis property and the compact
kernel carries any Haar measure. -/
theorem sIdeleClass_logPowerLp_generates :
    ∃ k₀ : Subgroup Cₛ[F, S], IsCompact (k₀ : Set Cₛ[F, S]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup Cₛ[F, S], k ≤ k₀ → IsCompact (k : Set Cₛ[F, S]) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → GeneratesLpSeminorms (positiveRealHaar.prod μ) (ENNReal.ofReal p)
          (fun i : ℕ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
            ideleClassProductWeightedDeriv (sIdeleClassNorm F S) τ γ i.2.1 i.2.2
              (fun t ↦ t ^ i.1) f.val) := by sorry

/-- Paper: Proposition D.1.10.10(3), p. 792. Absolute values of polynomials in
the absolute log S-norm give a generating family on the fixed subspace.
Deviation: The coefficients are complex as in D.1.10.9(3). The directions
satisfy the real basis property and the compact kernel carries any Haar measure. -/
theorem sIdeleClass_logPolynomialLp_generates :
    ∃ k₀ : Subgroup Cₛ[F, S], IsCompact (k₀ : Set Cₛ[F, S]) ∧ IsBruhatGoodSubgroup k₀ ∧
      ∀ k : Subgroup Cₛ[F, S], k ≤ k₀ → IsCompact (k : Set Cₛ[F, S]) → IsBruhatGoodSubgroup k →
        ∀ p : ℝ, 1 ≤ p → GeneratesLpSeminorms (positiveRealHaar.prod μ) (ENNReal.ofReal p)
          (fun i : Polynomial ℂ × ℕ × (Fin d[F] → ℕ) ↦ fun f : schwartzBruhatInvariantSubmodule k ↦
            ideleClassProductWeightedDeriv (sIdeleClassNorm F S) τ γ i.2.1 i.2.2
              (fun t ↦ ‖i.1.eval (t : ℂ)‖) f.val) := by sorry

-- TODO(paper-gap): The equality after D.1.10.10(3) also requires compatible
-- section and Haar choices. Even for identical classes, Haar rescaling changes
-- the seminorms.

end SLocal

end IdeleClassSeminorms

end RiemannMasullo
