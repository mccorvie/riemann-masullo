module

public import RiemannMasullo.Ch06_LocalGlobal.Sec1
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.Seminorm.DirectSum

/-! # Chapter 6.1: statements that are false as printed -/

@[expose] public noncomputable section

open IsDedekindDomain NumberField
open scoped MonoidAlgebra TensorProduct

namespace RiemannMasullo

local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "L(" F ", " v ")" => HeightOneSpectrum.adicCompletion (R := 𝓞 F) F v
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)

/-- Paper: §6.1.2, (6.1.2.2), p. 288. As printed: the full product of the multiplicative
groups outside S, inserted with identity coordinates in S, lies in the global idele group.
This is the ambient inclusion in (6.1.2.2). See `outsideIntegralIdeleUnits` and ERRATA F69. -/
def Printed.outsideLocalUnits_embed_in_ideles : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (Places(F)))
    (u : (v : {v : Places(F) // v ∉ S}) → (L(F, v.val))ˣ),
    ∃ g : IdeleGroup (𝓞 F) F, g.val.1 = 1 ∧
      (∀ v ∈ S, g.val.2 v = 1) ∧ ∀ v, g.val.2 v.val = (u v).val

/-- Paper: §6.1.2, (6.1.2.2), p. 288. Over ℚ take S to contain only the infinite place and
choose the component p at every prime p. The tuple is integral everywhere, but its coordinatewise
inverse is nonintegral at every prime, so no idele has these coordinates. -/
theorem Printed.outsideLocalUnits_embed_in_ideles_false :
    ¬ Printed.outsideLocalUnits_embed_in_ideles := by
  classical
  intro h
  let : Infinite (Places(ℚ)) := Infinite.of_injective Rat.HeightOneSpectrum.primesEquiv.symm
    Rat.HeightOneSpectrum.primesEquiv.symm.injective
  have bad (v : Places(ℚ)) : ∃ u : (L(ℚ, v))ˣ, u.val ∉ v.adicCompletionIntegers ℚ := by
    let val := (Valued.v : Valuation (L(ℚ, v)) (WithZero (Multiplicative ℤ)))
    obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
    refine ⟨(Units.mk0 π hπ.ne_zero)⁻¹, (HeightOneSpectrum.notMem_adicCompletionIntegers _ _ v).mpr ?_⟩
    change 1 < val π⁻¹
    rw [map_inv₀]
    exact (one_lt_inv₀ (pos_iff_ne_zero.mpr hπ.val_ne_zero)).mpr hπ.val_lt_one
  choose u hu using bad
  obtain ⟨g, -, -, hg⟩ := h ℚ ∅ (fun v ↦ u v.val)
  obtain ⟨v, hv⟩ := g.val.2.property.exists
  exact hu v ((hg ⟨v, Finset.notMem_empty v⟩) ▸ hv)

open Classical in
/-- Paper: Lemma 6.1.2.2(2), (6.1.2.5)–(6.1.2.6), p. 289. As printed: the monomial-to-ball
assignment extends to a linear homeomorphism from the projective tensor product of the S-local
tests and the Laurent polynomials with their finest locally convex topology to the relative unit
invariants. See `sLocalSchwartz_invariants_laurent_equiv` and ERRATA F70. -/
def Printed.sLocalSchwartz_invariants_projectiveLaurent_equiv : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S T : Finset (Places(F))) (hST : S ⊂ T),
    Subsingleton (CommRing.Pic ((S : Set (Places(F))).integer F)) →
    ∀ (π : ∀ v : ↥(T \ S), (L(F, v.val))ˣ),
      (∀ v : ↥(T \ S), Valuation.IsUniformizer
        (Valued.v : Valuation (L(F, v.val)) (WithZero (Multiplicative ℤ))) (π v).val) →
      ∃ e : ProjectiveTensor ℬ(SAdeleRing F S)
          (FinestLocallyConvex (AddMonoidAlgebra ℂ (↥(T \ S) → ℤ))) ≃L[ℂ]
          (Representation.invariants ((schwartzBruhatUnitRepresentation (R := SAdeleRing F T)).comp
            (relativeIntegralIdeleUnits F S T).subtype)),
        ∀ (f : ℬ(SAdeleRing F S)) (a : ↥(T \ S) → ℤ) (x : SAdeleRing F T),
          (e (f ⊗ₜ[ℂ] AddMonoidAlgebra.single a 1)).val (Multiplicative.ofAdd x) =
            f (Multiplicative.ofAdd (x.1, fun v : S ↦ x.2 ⟨v.val, hST.le v.property⟩)) *
              ∏ v : ↥(T \ S), finitePlaceBallIndicator v.val (π v) (a v)
                (x.2 ⟨v.val, (Finset.mem_sdiff.mp v.property).1⟩)

/-- Trivial Picard group of the empty-set S-integers of Q. -/
private theorem sLocalSchwartz_invariants_projectiveLaurent_equiv_false_rat_empty_pic :
    Subsingleton (CommRing.Pic (((∅ : Finset (Places(ℚ))) : Set (Places(ℚ))).integer ℚ)) := by
  rw [Finset.coe_empty, integer_empty]
  let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
  let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
  let := IsPrincipalIdealRing.of_surjective i i.surjective
  infer_instance

/-- Two linear maps on a tensor product with a monoid algebra agree when they agree on monomials. -/
private theorem sLocalSchwartz_invariants_projectiveLaurent_equiv_false_eq_of_single
    {E I Y : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup Y] [Module ℂ Y]
    (f g : E ⊗[ℂ] AddMonoidAlgebra ℂ I →ₗ[ℂ] Y)
    (h : ∀ (x : E) (a : I),
      f (x ⊗ₜ[ℂ] AddMonoidAlgebra.single a (1 : ℂ)) =
        g (x ⊗ₜ[ℂ] AddMonoidAlgebra.single a (1 : ℂ))) : f = g := by
  apply TensorProduct.ext'
  intro x y
  refine AddMonoidAlgebra.induction_linear y ?_ (fun a b ha hb ↦ ?_) (fun a c ↦ ?_)
  · simp only [TensorProduct.tmul_zero, map_zero]
  · simp only [TensorProduct.tmul_add, map_add, ha, hb]
  · have hsc : AddMonoidAlgebra.single a c = c • AddMonoidAlgebra.single a (1 : ℂ) := by
      rw [AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [hsc, TensorProduct.tmul_smul, map_smul, map_smul, h x a]

/-- Assemble a continuous seminorm on the inductive tensor product from one per basis index. -/
private theorem sLocalSchwartz_invariants_projectiveLaurent_equiv_false_seminorm
    {E V ι : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
    [AddCommGroup V] [Module ℂ V] [t : TopologicalSpace V]
    (b : Module.Basis ι ℂ V)
    (ht : t = (inferInstance : TopologicalSpace (FinestLocallyConvex V)))
    (p : ι → Seminorm ℂ E) (hp : ∀ i, Continuous (p i)) :
    ∃ q : Seminorm ℂ (InductiveTensor E V), Continuous q ∧ ∀ i x, q (x ⊗ₜ[ℂ] b i) = p i x := by
  classical
  let c := (TensorProduct.equivFinsuppOfBasisRight (M := E) b).trans (finsuppLequivDFinsupp ℂ)
  let q := (directSumSeminorm p).comp c.toLinearMap
  have hcoord (x : E) (y : V) (i : ι) : c (x ⊗ₜ[ℂ] y) i = b.repr y i • x :=
    TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply b x y i
  have hq (x : E) (y : V) : q (x ⊗ₜ[ℂ] y) = ∑ i ∈ (b.repr y).support, p i (b.repr y i • x) := by
    change directSumSeminorm p (c _) = _
    rw [directSumSeminorm_apply p (c _) (b.repr y).support (fun i hi ↦ ?_)]
    · exact Finset.sum_congr rfl fun i _ ↦ congrArg (p i) (hcoord x y i)
    · by_contra hn
      exact (DFinsupp.mem_support_iff.mp hi) ((hcoord x y i).trans (by
        rw [Finsupp.notMem_support_iff.mp hn, zero_smul]))
  have hsp := withGeneratingSeminorms_spec (E ⊗[ℂ] V)
    (fun j : {r : Seminorm ℂ (E ⊗[ℂ] V) // (∀ x : E, Continuous (fun y : V ↦ r (x ⊗ₜ[ℂ] y))) ∧
      (∀ y : V, Continuous (fun x : E ↦ r (x ⊗ₜ[ℂ] y)))} ↦ j.val)
  have := PolynormableSpace.continuousSMul ℂ E
  refine ⟨q, hsp.continuous_seminorm ⟨q, fun x ↦ ?_, fun y ↦ ?_⟩, fun i x ↦ ?_⟩
  · let r := q.comp (TensorProduct.mk ℂ E V x)
    exact Eq.mpr (congrArg (fun t' ↦ @Continuous V ℝ t' _ r) ht)
      ((finestLocallyConvex_withSeminorms V).continuous_seminorm r)
  · exact (continuous_finsetSum _ fun i _ ↦ (hp i).comp
      (continuous_const.smul (continuous_id (X := E)))).congr (fun x ↦ (hq x y).symm)
  · exact (hq x (b i)).trans (by simp)

/-- Continuity of the identity from projective to inductive tensor contradicts unbounded seminorms. -/
private theorem sLocalSchwartz_invariants_projectiveLaurent_equiv_false_not_continuous_id
    {E V ι : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [PolynormableSpace ℂ E]
    [T2Space E] [AddCommGroup V] [Module ℂ V] [t : TopologicalSpace V]
    (b : Module.Basis ι ℂ V)
    (ht : t = (inferInstance : TopologicalSpace (FinestLocallyConvex V)))
    (p : ι → Seminorm ℂ E) (hp : ∀ i, Continuous (p i))
    (hno : ∀ U ∈ nhds (0 : E), ∃ i, ¬ BddAbove (p i '' U))
    (hback : @Continuous (ProjectiveTensor E V) (InductiveTensor E V) _ _ id) : False := by
  subst ht
  let : TopologicalSpace V := inferInstanceAs (TopologicalSpace (FinestLocallyConvex V))
  have : PolynormableSpace ℂ V :=
    (finestLocallyConvex_withSeminorms V).toPolynormableSpace
  have : T2Space V := finestLocallyConvex_t2 V
  obtain ⟨q, hq, hqv⟩ :=
    sLocalSchwartz_invariants_projectiveLaurent_equiv_false_seminorm b rfl p hp
  let L : ProjectiveTensor E V →ₗ[ℂ] InductiveTensor E V := LinearMap.id
  have hjoint := (continuous_projectiveTensor_iff (E := E) (F := V) L).mp hback
  have h := (hq.comp hjoint).continuousAt (x := ((0 : E), (0 : V)))
  have hz : (fun z : E × V ↦ q (L (z.1 ⊗ₜ[ℂ] z.2))) ⁻¹' Set.Iio 1 ∈ nhds ((0 : E), (0 : V)) :=
    h.preimage_mem_nhds (Iio_mem_nhds (by
      change q (L ((0 : E) ⊗ₜ[ℂ] (0 : V))) < 1
      exact lt_of_eq_of_lt ((congrArg (fun z ↦ q (L z)) (TensorProduct.zero_tmul E (0 : V))).trans
        ((congrArg q L.map_zero).trans (map_zero q))) zero_lt_one))
  obtain ⟨U, hU, W0, hW0, hUW⟩ := mem_nhds_prod_iff.1 hz
  obtain ⟨i, hi⟩ := hno U hU
  have := PolynormableSpace.continuousSMul ℂ V
  have hc : ∀ᶠ c : ℂ in nhds 0, c • b i ∈ W0 :=
    (continuous_id.smul (continuous_const (y := b i))).continuousAt.preimage_mem_nhds
      (by simpa using hW0)
  obtain ⟨c, hcW, hc0⟩ := ((hc.filter_mono (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ)))).and
    (self_mem_nhdsWithin (a := (0 : ℂ)) (s := {0}ᶜ))).exists
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  apply hi
  refine ⟨1 / ‖c‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hl : q (x ⊗ₜ[ℂ] (c • b i)) < 1 := hUW (Set.mk_mem_prod hx hcW)
  have hh : q (x ⊗ₜ[ℂ] (c • b i)) = ‖c‖ * p i x :=
    (congrArg q (TensorProduct.tmul_smul _ _ _)).trans
      ((map_smul_eq_mul q _ _).trans (congrArg (‖c‖ * ·) (hqv i x)))
  exact (le_div_iff₀' hcpos).mpr (hh ▸ hl).le

/-- A topological group isomorphism carries a compact generating neighborhood to one. -/
private theorem sLocalSchwartz_invariants_projectiveLaurent_equiv_false_compactGen
    {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    (e : G ≃ₜ* H) (h : IsCompactlyGeneratedGroup G) : IsCompactlyGeneratedGroup H := by
  obtain ⟨U, hU, hK, hgen⟩ := h
  refine ⟨e '' U, ?_, hK.image e.continuous, ?_⟩
  · have hmap := e.toHomeomorph.map_nhds_eq 1
    rw [show e.toHomeomorph 1 = 1 from map_one e] at hmap
    rw [← hmap]
    exact Filter.mem_map.mpr (Filter.mem_of_superset hU (Set.subset_preimage_image e U))
  · have hmap := MonoidHom.map_closure e.toMulEquiv.toMonoidHom U
    rw [hgen, Subgroup.map_top, MonoidHom.range_eq_top.mpr e.surjective] at hmap
    exact hmap.symm

/-- Pullback along a topological group isomorphism carries each structural stage to a stage. -/
private theorem sLocalSchwartz_invariants_projectiveLaurent_equiv_false_stage_pullback
    {G H : Type*} [CommGroup G] [CommGroup H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [T2Space G] [T2Space H]
    [LocallyCompactSpace G] [LocallyCompactSpace H]
    (e : G ≃ₜ* H) (a : BruhatStructuralPair H) (p : ElementaryLCAPresentation a.quotient) :
    ∃ (b : BruhatStructuralPair G) (q : ElementaryLCAPresentation b.quotient)
      (j : SchwartzBruhatStage p →L[ℂ] SchwartzBruhatStage q),
      ∀ f, schwartzBruhatStageRealization b q (j f) = schwartzBruhatStageRealization a p f ∘ e := by
  classical
  let J := a.val.1
  let K := OrderDual.ofDual a.val.2
  let J' := J.comap e.toMulEquiv.toMonoidHom
  let K' := K.comap e.toMulEquiv.toMonoidHom
  let eJ : J' ≃ₜ* J := ContinuousMulEquiv.mk'
    (e.toHomeomorph.subtype fun _ ↦ Iff.rfl)
    (fun x y ↦ Subtype.ext (map_mul e (x : G) (y : G)))
  let hom : G →ₜ* H := ⟨e.toMulEquiv.toMonoidHom, e.continuous⟩
  let inv : H →ₜ* G := ⟨e.symm.toMulEquiv.toMonoidHom, e.symm.continuous⟩
  let dual : PontryaginDual H ≃ₜ* PontryaginDual G :=
    { toFun := PontryaginDual.map hom
      invFun := PontryaginDual.map inv
      left_inv := fun χ ↦ PontryaginDual.ext fun y ↦ congrArg χ (e.apply_symm_apply y)
      right_inv := fun χ ↦ PontryaginDual.ext fun x ↦ congrArg χ (e.symm_apply_apply x)
      map_mul' := map_mul (PontryaginDual.map hom)
      continuous_toFun := (PontryaginDual.map hom).continuous
      continuous_invFun := (PontryaginDual.map inv).continuous }
  have hAnn (χ : PontryaginDual H) : χ ∈ lcaAnnihilator K ↔ dual χ ∈ lcaAnnihilator K' := by
    simp only [mem_lcaAnnihilator_iff]
    refine ⟨fun h x ↦ h ⟨e x, x.property⟩, fun h y ↦ ?_⟩
    have hy : e.symm y ∈ K' := by
      change e (e.symm y) ∈ K
      rw [e.apply_symm_apply]
      exact y.property
    have heval : χ (e (e.symm y)) = 1 := h ⟨e.symm y, hy⟩
    simpa using heval
  let eAnn : lcaAnnihilator K ≃ₜ* lcaAnnihilator K' := ContinuousMulEquiv.mk'
    (dual.toHomeomorph.subtype hAnn)
    (fun x y ↦ Subtype.ext (map_mul dual (x : PontryaginDual H) y))
  have hopen : IsOpen (lcaAnnihilator K' : Set (PontryaginDual G)) := by
    have heq : (lcaAnnihilator K' : Set (PontryaginDual G)) =
        dual.symm ⁻¹' (lcaAnnihilator K : Set (PontryaginDual H)) := by
      ext χ
      simpa using (hAnn (dual.symm χ)).symm
    rw [heq]
    exact a.property.2.2.1.2.1.preimage dual.symm.continuous
  let a' : BruhatStructuralPair G :=
    ⟨(J', OrderDual.toDual K'), a.property.1.preimage e.continuous,
      sLocalSchwartz_invariants_projectiveLaurent_equiv_false_compactGen eJ.symm a.property.2.1,
      ⟨a.property.2.2.1.1.preimage e.continuous, hopen,
        sLocalSchwartz_invariants_projectiveLaurent_equiv_false_compactGen eAnn
          a.property.2.2.1.2.2⟩,
      Subgroup.comap_mono a.property.2.2.2⟩
  let N := K.comap J.subtype
  let N' := K'.comap J'.subtype
  have hN : N'.map eJ.toMulEquiv.toMonoidHom = N := by
    change N'.map (eJ.toMulEquiv : J' →* J) = N
    rw [Subgroup.map_equiv_eq_comap_symm eJ.toMulEquiv]
    ext y
    change e (e.symm y) ∈ K ↔ (y : H) ∈ K
    rw [e.apply_symm_apply]
  let q := QuotientGroup.congr N' N eJ.toMulEquiv hN
  let eQ : a'.quotient ≃ₜ* a.quotient :=
    ⟨q, (QuotientGroup.isQuotientMap_mk N').continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp eJ.continuous),
      (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
        (QuotientGroup.continuous_mk.comp eJ.symm.continuous)⟩
  let p' : ElementaryLCAPresentation a'.quotient := { p with equiv := eQ.trans p.equiv }
  exact ⟨a', p', ContinuousLinearMap.id ℂ _, fun _ ↦ rfl⟩

/-- Pullback along a topological group isomorphism is a continuous linear map on test spaces. -/
private theorem sLocalSchwartz_invariants_projectiveLaurent_equiv_false_pullbackCLM
    {G H : Type*} [CommGroup G] [CommGroup H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [T2Space G] [T2Space H]
    [LocallyCompactSpace G] [LocallyCompactSpace H] (e : G ≃ₜ* H) :
    ∃ T : SchwartzBruhat H →L[ℂ] SchwartzBruhat G, ∀ f x, T f x = f (e x) := by
  have hmem {g : H → ℂ} (hg : g ∈ schwartzBruhatSubmodule H) :
      g ∘ e ∈ schwartzBruhatSubmodule G := by
    let pullback : (H → ℂ) →ₗ[ℂ] (G → ℂ) := LinearMap.funLeft ℂ ℂ e
    have hle : schwartzBruhatSubmodule H ≤ (schwartzBruhatSubmodule G).comap pullback := by
      refine iSup_le fun a ↦ iSup_le fun p ↦ ?_
      rintro _ ⟨f, rfl⟩
      obtain ⟨b, q, j, hj⟩ :=
        sLocalSchwartz_invariants_projectiveLaurent_equiv_false_stage_pullback e a p
      change schwartzBruhatStageRealization a p f ∘ e ∈ schwartzBruhatSubmodule G
      rw [← hj f]
      exact (schwartzBruhatStageInclusion b q (j f)).property
    exact hle hg
  let L := (LinearMap.funLeft ℂ ℂ e).comp (schwartzBruhatSubmodule H).subtype
  let T : SchwartzBruhat H →ₗ[ℂ] SchwartzBruhat G := L.codRestrict _ fun f ↦ hmem f.property
  refine ⟨⟨T, ?_⟩, fun _ _ ↦ rfl⟩
  refine (withGeneratingSeminorms_spec _ Subtype.val).continuous_of_continuous_comp T ?_
  rintro ⟨s, hs⟩
  refine (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm ⟨s.comp T, ?_⟩
  intro a p
  obtain ⟨b, q, j, hj⟩ :=
    sLocalSchwartz_invariants_projectiveLaurent_equiv_false_stage_pullback e a p
  exact ((hs b q).comp j.continuous).congr fun f ↦ congrArg s (Subtype.ext (hj f))

/-- Dirac evaluations on an infinite locally compact group show the test space is infinite dimensional. -/
private theorem sLocalSchwartz_invariants_projectiveLaurent_equiv_false_not_finDim
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [Infinite G] :
    ¬ FiniteDimensional ℂ (SchwartzBruhat G) := by
  classical
  intro hfin
  let d (x : G) := (schwartzBruhat_dirac_support x).choose
  have hev (x : G) (f : SchwartzBruhat G) : d x f = f x :=
    (schwartzBruhat_dirac_support x).choose_spec.1 f
  have hSep (x : G) (U : Set G) (hU : IsOpen U) (hx : x ∈ U) :
      ∃ f : SchwartzBruhat G, tsupport (f : G → ℂ) ⊆ U ∧ f x ≠ 0 := by
    by_contra! h
    have hx' : x ∈ schwartzBruhatVanishingLocus (d x) :=
      Set.mem_sUnion.mpr ⟨U, ⟨hU, fun f hf ↦ (hev x f).trans (h f hf)⟩, hx⟩
    exact ((schwartzBruhat_dirac_support x).choose_spec.2.1 ▸ hx') (Set.mem_singleton x)
  let l (x : G) : Module.Dual ℂ (SchwartzBruhat G) := (d x).toLinearMap
  have hlin : LinearIndependent ℂ l := by
    apply linearIndependent_iff'.mpr
    intro s g he i hi
    let t := s.erase i
    obtain ⟨f, hf, hfi⟩ := hSep i (t : Set G)ᶜ t.finite_toSet.isClosed.isOpen_compl
      (Finset.notMem_erase i s)
    have hz (j : G) (hj : j ∈ s) (hne : j ≠ i) : l j f = 0 := by
      rw [show l j f = f j from hev j f]
      by_contra h
      exact hf (subset_tsupport _ h) (Finset.mem_erase.mpr ⟨hne, hj⟩)
    have hsum : ∑ j ∈ s, g j * l j f = 0 := by
      simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
        using DFunLike.congr_fun he f
    rw [Finset.sum_eq_single_of_mem i hi (fun j hj hji ↦ by rw [hz j hj hji, mul_zero])] at hsum
    exact (mul_eq_zero.mp hsum).resolve_right fun ht ↦ hfi ((hev i f).symm.trans ht)
  exact @_root_.not_finite G inferInstance hlin.finite

/-- The empty-set S-adelic test space over Q is Hausdorff and has a countable family of continuous
seminorms such that no zero neighborhood is bounded under all of them. -/
private theorem sLocalSchwartz_invariants_projectiveLaurent_equiv_false_empty_seminorms :
    T2Space ℬ(SAdeleRing ℚ (∅ : Finset (Places(ℚ)))) ∧
    ∃ p : (ℕ × ℕ) → Seminorm ℂ ℬ(SAdeleRing ℚ (∅ : Finset (Places(ℚ)))),
      (∀ i, Continuous (p i)) ∧
      ∀ U ∈ nhds (0 : ℬ(SAdeleRing ℚ (∅ : Finset (Places(ℚ))))),
        ∃ i, ¬ BddAbove (p i '' U) := by
  let realEquiv := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  let realIso := InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  let eInfHomeo : InfiniteAdeleRing ℚ ≃ₜ ℝ :=
    (Homeomorph.piUnique fun w : InfinitePlace ℚ ↦ w.Completion).trans realIso.toHomeomorph
  let eHomeo : SAdeleRing ℚ (∅ : Finset (Places(ℚ))) ≃ₜ ℝ :=
    (Homeomorph.prodUnique (InfiniteAdeleRing ℚ)
      ((w : (∅ : Finset (Places(ℚ)))) → L(ℚ, w.val))).trans eInfHomeo
  let eGrp : Multiplicative (SAdeleRing ℚ (∅ : Finset (Places(ℚ)))) ≃ₜ* Multiplicative ℝ :=
    { toEquiv :=
        { toFun := fun x ↦ Multiplicative.ofAdd (realEquiv (x.toAdd.1 Rat.infinitePlace))
          invFun := fun y ↦ Multiplicative.ofAdd (eHomeo.symm y.toAdd)
          left_inv := fun x ↦ by
            apply congrArg Multiplicative.ofAdd
            exact eHomeo.symm_apply_apply x.toAdd
          right_inv := fun y ↦ by
            apply congrArg Multiplicative.ofAdd
            exact eHomeo.apply_symm_apply y.toAdd }
      map_mul' := fun x y ↦ congrArg Multiplicative.ofAdd (map_add realEquiv _ _)
      continuous_toFun := eHomeo.continuous
      continuous_invFun := eHomeo.symm.continuous }
  let : T2Space (Multiplicative (SAdeleRing ℚ (∅ : Finset (Places(ℚ))))) :=
    eGrp.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative (SAdeleRing ℚ (∅ : Finset (Places(ℚ))))) :=
    eGrp.isOpenEmbedding.locallyCompactSpace
  let : T2Space (Multiplicative ℝ) := inferInstanceAs (T2Space ℝ)
  let : LocallyCompactSpace (Multiplicative ℝ) := inferInstanceAs (LocallyCompactSpace ℝ)
  let : T2Space ℬ(ℝ) := schwartzBruhat_t2
  let : MontelSpace ℂ ℬ(ℝ) := schwartzBruhat_montel
  obtain ⟨T1, hT1⟩ :=
    sLocalSchwartz_invariants_projectiveLaurent_equiv_false_pullbackCLM eGrp.symm
  obtain ⟨T2, hT2⟩ :=
    sLocalSchwartz_invariants_projectiveLaurent_equiv_false_pullbackCLM eGrp
  let eS : ℬ(SAdeleRing ℚ (∅ : Finset (Places(ℚ)))) ≃L[ℂ] ℬ(ℝ) :=
    { toLinearMap := T1.toLinearMap
      invFun := T2
      left_inv := fun f ↦ Subtype.ext (funext fun x ↦ by
        change T2 (T1 f) x = f x
        exact (hT2 (T1 f) x).trans ((hT1 f (eGrp x)).trans (congrArg f (eGrp.symm_apply_apply x))))
      right_inv := fun f ↦ Subtype.ext (funext fun y ↦ by
        change T1 (T2 f) y = f y
        exact (hT1 (T2 f) y).trans ((hT2 f (eGrp.symm y)).trans (congrArg f (eGrp.apply_symm_apply y))))
      continuous_toFun := T1.continuous
      continuous_invFun := T2.continuous }
  let eR : SchwartzMap ℝ ℂ ≃L[ℂ] ℬ(ℝ) := realSchwartzBruhat_equiv.choose
  let pR : (ℕ × ℕ) → Seminorm ℂ ℬ(ℝ) :=
    fun i ↦ (schwartzSeminormFamily ℂ ℝ ℂ i).comp eR.symm.toLinearMap
  have hpR (i : ℕ × ℕ) : Continuous (pR i) :=
    ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm i).comp eR.symm.continuous
  have hnoR : ∀ U ∈ nhds (0 : ℬ(ℝ)), ∃ i, ¬ BddAbove (pR i '' U) := by
    intro U hU
    by_contra! hn
    have hb : Bornology.IsVonNBounded ℂ (eR.symm '' U) :=
      (schwartz_withSeminorms ℂ ℝ ℂ).isVonNBounded_iff_seminorm_bddAbove.mpr
        (fun i ↦ Set.image_image (schwartzSeminormFamily ℂ ℝ ℂ i) eR.symm U ▸ hn i)
    have hUbounded : Bornology.IsVonNBounded ℂ U := by
      have h := hb.image eR.toContinuousLinearMap
      simpa only [ContinuousLinearEquiv.coe_coe, Set.image_image, eR.apply_symm_apply,
        Set.image_id'] using h
    have hc := MontelSpace.isCompact_of_isClosed_of_isVonNBounded ℂ isClosed_closure
      hUbounded.closure
    exact sLocalSchwartz_invariants_projectiveLaurent_equiv_false_not_finDim (G := Multiplicative ℝ)
      (FiniteDimensional.of_totallyBounded_nhds_zero ℂ hU
        (hc.totallyBounded.subset subset_closure))
  refine ⟨eS.toHomeomorph.isEmbedding.t2Space, fun i ↦ (pR i).comp eS.toLinearMap,
    fun i ↦ (hpR i).comp eS.continuous, fun U hU ↦ ?_⟩
  have hU' : eS '' U ∈ nhds (0 : ℬ(ℝ)) := eS.map_zero ▸ eS.isOpenMap.image_mem_nhds hU
  obtain ⟨i, hi⟩ := hnoR _ hU'
  exact ⟨i, fun hb ↦ hi (Set.image_image (pR i) eS U ▸ hb)⟩

/-- Paper: Lemma 6.1.2.2(2), (6.1.2.5), p. 289. Over ℚ add one prime to the archimedean
stage. In ball coordinates the target is a locally convex direct sum of real Schwartz spaces,
where the seminorm `∑_{n ≥ 0} |f_n⁽ⁿ⁾(0)|` is continuous. Each Laurent zero neighborhood contains
a nonzero multiple of every monomial. Joint continuity would therefore bound the derivative of
order k+1 on a Schwartz zero neighborhood controlling derivatives only through order k. A smooth
compactly supported cutoff equal to one near zero times `exp(itx)/t^k`, scaled by a fixed nonzero
constant into that neighborhood, has unbounded derivative of order k+1 at zero. -/
theorem Printed.sLocalSchwartz_invariants_projectiveLaurent_equiv_false :
    ¬ Printed.sLocalSchwartz_invariants_projectiveLaurent_equiv := by
  classical
  intro h
  let v : Places(ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩
  let S : Finset (Places(ℚ)) := ∅
  let T : Finset (Places(ℚ)) := {v}
  have hST : S ⊂ T := Finset.empty_ssubset.mpr ⟨v, Finset.mem_singleton_self v⟩
  have hPic := sLocalSchwartz_invariants_projectiveLaurent_equiv_false_rat_empty_pic
  have hpi_ex (w : ↥(T \ S)) :
      ∃ u : (L(ℚ, w.val))ˣ, Valuation.IsUniformizer
        (Valued.v : Valuation (L(ℚ, w.val)) (WithZero (Multiplicative ℤ))) u.val := by
    let val := (Valued.v : Valuation (L(ℚ, w.val)) (WithZero (Multiplicative ℤ)))
    obtain ⟨π₀, hπ₀⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
    exact ⟨Units.mk0 π₀ hπ₀.ne_zero, hπ₀⟩
  choose π hπ using hpi_ex
  obtain ⟨eP, heP⟩ := h ℚ S T hST hPic π hπ
  obtain ⟨eI, heI, -⟩ := sLocalSchwartz_invariants_laurent_equiv (F := ℚ) hST hPic π hπ
  let E := ℬ(SAdeleRing ℚ S)
  let I := ↥(T \ S) → ℤ
  let W := FinestLocallyConvex (AddMonoidAlgebra ℂ I)
  have heq : ∀ z : ProjectiveTensor E W, eP z = eI z := by
    have hlin := sLocalSchwartz_invariants_projectiveLaurent_equiv_false_eq_of_single
      (E := E) (I := I) eP.toLinearMap eI.toLinearMap fun f a ↦ by
        apply Subtype.ext
        apply Subtype.ext
        funext x
        exact (heP f a x.toAdd).trans (heI f a x.toAdd).symm
    exact fun z ↦ LinearMap.congr_fun hlin z
  have hback : @Continuous (ProjectiveTensor E W) (InductiveTensor E W) _ _ id := by
    refine (eI.symm.continuous.comp eP.continuous).congr fun z ↦ ?_
    change eI.symm (eP z) = z
    rw [heq z]
    exact eI.symm_apply_apply z
  obtain ⟨hT2E, p0, hp0, hno0⟩ :=
    sLocalSchwartz_invariants_projectiveLaurent_equiv_false_empty_seminorms
  let : T2Space E := hT2E
  let emb : (ℕ × ℕ) ↪ I :=
    ⟨fun k _ ↦ (Nat.pair k.1 k.2 : ℤ), fun a b hab ↦ by
      have hw : v ∈ T \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_singleton_self v, Finset.notMem_empty v⟩
      have h1 : (Nat.pair a.1 a.2 : ℤ) = (Nat.pair b.1 b.2 : ℤ) := congrFun hab ⟨v, hw⟩
      have h2 := congrArg Nat.unpair (Int.ofNat.inj h1)
      simpa only [Nat.unpair_pair] using h2⟩
  let invEmb : I → ℕ × ℕ := Function.invFun emb
  let b : Module.Basis I ℂ W := AddMonoidAlgebra.basis I ℂ
  exact sLocalSchwartz_invariants_projectiveLaurent_equiv_false_not_continuous_id (E := E) (V := W)
    b rfl (fun i ↦ p0 (invEmb i)) (fun i ↦ hp0 _) (fun U hU ↦ by
      obtain ⟨k, hk⟩ := hno0 U hU
      refine ⟨emb k, ?_⟩
      simpa only [invEmb, Function.leftInverse_invFun emb.injective k] using hk)
    hback

end RiemannMasullo
