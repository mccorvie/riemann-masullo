module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec2
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec5

import Mathlib.Algebra.Polynomial.Taylor
import all RiemannMasullo.AppC_LCTVS.Sec2b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import RiemannMasullo.ForMathlib.Topology.Algebra.Module.OpenMapping
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L1Space.Continuous

/-!
# Periodic Schauder bases in the presence of multiplicity

Masullo, §4.6, pp. 209–220. Lists of cyclic differences retain repetitions.
-/

@[expose] public noncomputable section

open Function MeasureTheory Set Topology TopologicalSpace
open scoped NNReal Pointwise

set_option quotPrecheck false

namespace RiemannMasullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [hSC : SecondCountableTopology G]
variable (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)

local notation "K" => m.toMonoidHom.ker
local notation "E" => ModulatedExponentialDecay m (univ : Set ℝ)
local notation "ρK" => (schwartzBruhatTranslationAction (G := G)).comp (K).subtype
local notation "period" x => Real.log ((m x).val : ℝ)

/-! ## 4.6.1 Bases in the presence of multiplicity -/

-- Situation 4.6.1.1 uses the section frequency and normalized phase from
-- existsUnique_modulatedMellinSectionFrequency and existsUnique_modulatedCharacterPhase.

-- TODO(paper-gap): Situation 4.6.1.1(4) omits the right-hand side of the restriction
-- equation. The real phase in (5) is unique only modulo 2π / log |γₖ|.

variable (ω : PontryaginDual m.toMonoidHom.ker) (γ : G)

/-- Paper: Notation 4.6.1.1, p. 209. The fiber consists of characters that
annihilate the generator and restrict to the indicated norm-one character.
Deviation: The restriction itself indexes the fiber. -/
def modulatedCyclicAnnihilatorFiber (m : G →ₜ* ℝ≥0ˣ)
    (ω : PontryaginDual m.toMonoidHom.ker) (γ : G) : Set (PontryaginDual G) :=
  let K₁ := m.toMonoidHom.ker
  {ξ | ξ ∈ lcaAnnihilator (Subgroup.zpowers γ) ∧
    PontryaginDual.map (⟨K₁.subtype, continuous_subtype_val⟩ : K₁ →ₜ* G) ξ = ω}

/-- Paper: Notation 4.6.1.1, p. 209. The fiber can be tested at the generator
and on each element of the norm-one subgroup. -/
theorem mem_modulatedCyclicAnnihilatorFiber_iff (ξ : PontryaginDual G) :
    ξ ∈ modulatedCyclicAnnihilatorFiber m ω γ ↔
      ξ γ = 1 ∧ ∀ u : K, ξ u.val = ω u := by
  constructor
  · rintro ⟨hann, hres⟩
    exact ⟨(mem_lcaAnnihilator_iff _ ξ).mp hann ⟨γ, Subgroup.mem_zpowers γ⟩,
      DFunLike.congr_fun hres⟩
  · rintro ⟨hγ, hres⟩
    refine ⟨(mem_lcaAnnihilator_iff _ ξ).mpr ?_, PontryaginDual.ext hres⟩
    have hker : Subgroup.zpowers γ ≤ ξ.toMonoidHom.ker := Subgroup.zpowers_le.mpr hγ
    exact fun u ↦ hker u.property

include hm hSC in
/-- Paper: Remark 4.6.1.2, p. 210. Every norm-one character has a compact
kernel subgroup with finitely generated annihilator. For that subgroup the
entire cyclic fiber annihilates its product with the cyclic subgroup. -/
theorem modulatedCyclicAnnihilatorFiber_subset :
    ∃ k : Subgroup K, IsCompact (k : Set K) ∧ (lcaAnnihilator k).FG ∧
      ω ∈ lcaAnnihilator k ∧
      modulatedCyclicAnnihilatorFiber m ω γ ⊆
        (lcaAnnihilator (Subgroup.zpowers γ ⊔ k.map (K).subtype) : Set (PontryaginDual G)) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let J := Subgroup.zpowers ω
  let k := lcaDualAnnihilator J
  have hk : IsClosed (k : Set K) := by
    rw [show (k : Set K) = ⋂ χ : J, χ.val ⁻¹' ({1} : Set Circle) by
      ext x
      change x ∈ k ↔ _
      simpa only [mem_iInter, mem_preimage, mem_singleton_iff] using
        mem_lcaDualAnnihilator_iff J x]
    exact isClosed_iInter fun χ ↦ isClosed_singleton.preimage χ.val.continuous
  have hAnn : lcaAnnihilator k = J := by
    obtain ⟨e, he⟩ := pontryaginDual_bidual (G := K)
    have hEval (x : K) : e x ∈ lcaAnnihilator J ↔ x ∈ k := by
      change _ ↔ x ∈ lcaDualAnnihilator J
      simp only [mem_lcaAnnihilator_iff, mem_lcaDualAnnihilator_iff, he]
    ext χ
    conv_rhs => rw [← lcaDualAnnihilator_annihilator J (isClosed_discrete _)]
    rw [mem_lcaAnnihilator_iff, mem_lcaDualAnnihilator_iff]
    constructor
    · intro h ψ
      obtain ⟨x, hx⟩ := e.surjective ψ.val
      have hmem : x ∈ k := (hEval x).mp (hx.symm ▸ ψ.property)
      rw [← hx, he]
      exact h ⟨x, hmem⟩
    · intro h x
      have hx := h ⟨e x.val, (hEval x.val).mpr x.property⟩
      change e x.val χ = 1 at hx
      rwa [he] at hx
  have hω : ω ∈ lcaAnnihilator k := hAnn.symm ▸ Subgroup.mem_zpowers ω
  refine ⟨k, hk.isCompact, ?_, hω, ?_⟩
  · rw [hAnn]
    infer_instance
  · intro ξ hξ
    obtain ⟨hγ, hres⟩ := (mem_modulatedCyclicAnnihilatorFiber_iff m ω γ ξ).mp hξ
    have hker : Subgroup.zpowers γ ⊔ k.map (K).subtype ≤ ξ.toMonoidHom.ker := by
      refine sup_le (Subgroup.zpowers_le.mpr hγ) (Subgroup.map_le_iff_le_comap.mpr ?_)
      intro y hy
      exact (hres y).trans ((mem_lcaAnnihilator_iff k ω).mp hω ⟨y, hy⟩)
    exact (mem_lcaAnnihilator_iff _ ξ).mpr fun x ↦ hker x.property

section Difference

variable (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty)

/-- Paper: Lemma 4.6.1.3(1) and Corollary 4.6.3.1, pp. 210, 219.
The iterated difference composes the cyclic differences for the entries
of the list, with one factor for each occurrence.
Deviation: The operator is defined on the ambient decay space and then
restricted to isotypes. The empty list gives the identity. -/
def modulatedDifferenceProduct (S : List G) :
    ModulatedExponentialDecay m I →L[ℂ] ModulatedExponentialDecay m I :=
  (S.map fun g ↦ modulatedCyclicDifference m g hm hms I hInt hne).prod

/-- Paper: Lemma 4.6.1.3(1) and Example 4.6.1.6, pp. 210, 217.
A repeated generator gives the second finite difference at every point. -/
theorem modulatedDifferenceProduct_pair_apply (f : ModulatedExponentialDecay m I) (x : G) :
    (modulatedDifferenceProduct m hm hms I hInt hne [γ, γ] f).val x =
      f.val x - 2 * f.val (γ * x) + f.val (γ ^ 2 * x) := by
  let Δ := modulatedCyclicDifference m γ hm hms I hInt hne
  have eval (g : ModulatedExponentialDecay m I) (y : G) :
      (Δ g).val y = g.val y - g.val (γ * y) :=
    modulatedCyclicDifference_apply m γ hm hms I hInt hne g y
  calc
    _ = (Δ f).val x - (Δ f).val (γ * x) := eval (Δ f) x
    _ = (f.val x - f.val (γ * x)) -
        (f.val (γ * x) - f.val (γ ^ 2 * x)) :=
      congrArg₂ (· - ·) (eval f x) (by simpa only [pow_two, mul_assoc] using eval f (γ * x))
    _ = _ := by ring

end Difference

/-- Paper: Lemma 4.6.1.3 and Corollary 4.6.3.1, pp. 210, 219.
The decay isotype consists of the functions whose zero twist belongs to
the ordinary Schwartz–Bruhat isotype for the same norm-one character. -/
def modulatedDecayIsotype (m : G →ₜ* ℝ≥0ˣ) (I : Set ℝ) (h0 : 0 ∈ I)
    (ω : PontryaginDual m.toMonoidHom.ker) : Submodule ℂ (ModulatedExponentialDecay m I) :=
  let ρ := (schwartzBruhatTranslationAction (G := G)).comp m.toMonoidHom.ker.subtype
  (actionIsotype ρ ω).comap (modulatedExponentialDecayTwist m I ⟨0, h0⟩)

local notation "H₀[" w "]" =>
  (modulatedDecayIsotype m (Set.univ : Set ℝ) (Set.mem_univ (0 : ℝ)) w)

/-- Paper: Lemma 4.6.1.3, p. 210. Isotype membership means left
translation by each norm-one element acts by its character value. -/
theorem mem_modulatedDecayIsotype_iff (I : Set ℝ) (h0 : 0 ∈ I)
    (f : ModulatedExponentialDecay m I) :
    f ∈ (modulatedDecayIsotype m I h0 ω) ↔ ∀ (u : K) (x : G),
      f.val (u.val⁻¹ * x) = (ω u : ℂ) * f.val x := by
  let z := modulatedExponentialDecayTwist m I ⟨0, h0⟩ f
  have hz (x : G) : z x = f.val x :=
    (modulatedExponentialDecayTwist_apply m I ⟨0, h0⟩ f x).trans (by simp)
  let ρ := (schwartzBruhatTranslationAction (G := G)).comp m.toMonoidHom.ker.subtype
  refine (mem_actionIsotype ρ ω z).trans ?_
  have hl (u : K) (x : G) :
      schwartzBruhatTranslationAction (G := G) u.val z x = f.val (u.val⁻¹ * x) :=
    (schwartzBruhatTranslationAction_apply u.val x z).trans (hz _)
  have hr (u : K) (x : G) : ((ω u : ℂ) • z) x = (ω u : ℂ) * f.val x :=
    congrArg ((ω u : ℂ) * ·) (hz x)
  constructor
  · intro h u x
    exact (hl u x).symm.trans ((congrArg (fun g : SchwartzBruhat G ↦ g x) (h u)).trans (hr u x))
  · intro h u
    exact Subtype.ext (funext fun x ↦ (hl u x).trans ((h u x).trans (hr u x).symm))

/-- Paper: Lemma 4.6.1.3(1), p. 210. The difference product preserves each
norm-one isotype. The same restriction is used for intervals containing zero
in Corollary 4.6.3.1. -/
theorem modulatedDifferenceProduct_mem_isotype
    (I : Set ℝ) (hInt : OrdConnected I) (h0 : 0 ∈ I) (S : List G) :
    ∀ f ∈ modulatedDecayIsotype m I h0 ω,
      modulatedDifferenceProduct m hm hms I hInt ⟨0, h0⟩ S f ∈
        modulatedDecayIsotype m I h0 ω := by
  induction S with
  | nil => exact fun f hf ↦ hf
  | cons g S ih =>
    intro f hf
    have hP := (mem_modulatedDecayIsotype_iff m ω I h0 _).mp (ih f hf)
    refine (mem_modulatedDecayIsotype_iff m ω I h0
      (modulatedDifferenceProduct m hm hms I hInt ⟨0, h0⟩ (g :: S) f)).mpr fun u x ↦ ?_
    have h1 := modulatedCyclicDifference_apply m g hm hms I hInt ⟨0, h0⟩
      (modulatedDifferenceProduct m hm hms I hInt ⟨0, h0⟩ S f) (u.val⁻¹ * x)
    have h2 := modulatedCyclicDifference_apply m g hm hms I hInt ⟨0, h0⟩
      (modulatedDifferenceProduct m hm hms I hInt ⟨0, h0⟩ S f) x
    have hcomm : g * (u.val⁻¹ * x) = u.val⁻¹ * (g * x) := mul_left_comm _ _ _
    exact h1.trans ((congrArg₂ (· - ·) (hP u x)
      ((congrArg (modulatedDifferenceProduct m hm hms I hInt ⟨0, h0⟩ S f).val hcomm).trans
        (hP u (g * x)))).trans
      ((mul_sub _ _ _).symm.trans (congrArg ((ω u : ℂ) * ·) h2.symm)))

/-- Paper: Equation (4.6.1.3), p. 210. The cyclic difference product on
the isotype is the restriction of the ambient operator. -/
def modulatedIsotypicDifferenceProduct (I : Set ℝ) (hInt : OrdConnected I) (h0 : 0 ∈ I)
    (S : List G) : (modulatedDecayIsotype m I h0 ω) →L[ℂ] (modulatedDecayIsotype m I h0 ω) :=
  (modulatedDifferenceProduct m hm hms I hInt ⟨0, h0⟩ S).restrict
    (modulatedDifferenceProduct_mem_isotype (m := m) (hm := hm) (hms := hms) (ω := ω) I hInt h0 S)

-- Avoid the unused-section-variable linter traversing the large decay-space types.
set_option linter.unusedSectionVars false in
/-- Paper: Equation (4.6.1.3), p. 210. Forgetting the isotype condition
recovers the same difference product on the ambient decay space. -/
theorem modulatedIsotypicDifferenceProduct_apply_coe
    (I : Set ℝ) (hInt : OrdConnected I) (h0 : 0 ∈ I) (S : List G)
    (f : modulatedDecayIsotype m I h0 ω) :
    (modulatedIsotypicDifferenceProduct (m := m) (hm := hm) (hms := hms) (ω := ω) I hInt h0 S f).val =
      modulatedDifferenceProduct m hm hms I hInt ⟨0, h0⟩ S f.val := by
  have h := ContinuousLinearMap.coe_restrict_apply
    (modulatedDifferenceProduct_mem_isotype (m := m) (hm := hm) (hms := hms)
      (ω := ω) I hInt h0 S) f
  unfold modulatedIsotypicDifferenceProduct
  unfold modulatedDifferenceProduct modulatedCyclicDifference at h ⊢
  exact h

local notation "P[" w "," s "]" =>
  (modulatedIsotypicDifferenceProduct (m := m) (hm := hm) (hms := hms) (ω := w)
    univ ordConnected_univ (mem_univ (0 : ℝ)) s)

section IsotypicQuotient

variable (S₀ : List G) (hS₀ : ∀ g ∈ S₀, 1 < (m g).val)
variable (hγ : 1 < (m γ).val)

section

set_option linter.unusedSectionVars false

private theorem metrizable_separable_of_subset_range {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (S : Set Y) (i : X → Y) (hi : IsEmbedding i)
    (hsub : S ⊆ range i) (hM : MetrizableSpace X) (hS : SeparableSpace X) :
    MetrizableSpace S ∧ SeparableSpace S := by
  have he := hi.toHomeomorph.symm.isEmbedding.comp (IsEmbedding.inclusion hsub)
  have : SecondCountableTopology X := by
    let := pseudoMetrizableSpaceUniformity X
    have := pseudoMetrizableSpaceUniformity_countably_generated X
    exact UniformSpace.secondCountable_of_separable X
  have : SecondCountableTopology S := he.secondCountableTopology
  exact ⟨he.metrizableSpace, inferInstance⟩

private theorem isotype_le_stage_of_trivial
    (k : {k : Subgroup G // IsCompact (k : Set G) ∧ IsCompactlyGeneratedGroup (lcaAnnihilator k)})
    (htriv : ∀ v : K, v.val ∈ k.val → ω v = 1) :
    (H₀[ω] : Set E) ⊆ range (modulatedExponentialDecayStageInclusion m univ k) := by
  intro f hf
  apply ((modulatedExponentialDecayStageInclusion_range m univ k).2 f).mpr
  intro x u
  let v : K := ⟨u.val, compactSubgroup_le_modulation_ker m k.val k.property.1 u.property⟩
  have h := (mem_modulatedDecayIsotype_iff m ω univ (mem_univ _) f).mp hf v⁻¹ x
  have hx : ((v⁻¹ : K).val)⁻¹ * x = x * u.val := by
    change ((u.val)⁻¹)⁻¹ * x = _
    rw [inv_inv, mul_comm]
  have hv : (ω v⁻¹ : ℂ) = 1 := by rw [map_inv, htriv v u.property, inv_one, Circle.coe_one]
  exact (congrArg f.val hx.symm).trans (h.trans ((congrArg (· * f.val x) hv).trans (one_mul _)))

include hm hms in
private theorem exists_surjectiveModulation_section :
    ∃ τ : ℝ≥0ˣ →ₜ* G, RightInverse τ m := by
  let τ₀ := hm.exists_section.choose
  let τ : ℝ≥0ˣ →ₜ* G := τ₀.comp
    ⟨(MonoidHom.id ℝ≥0ˣ).codRestrict _ fun t ↦ MonoidHom.mem_range.mpr (hms t),
      continuous_id.subtype_mk _⟩
  exact ⟨τ, fun _ ↦ hm.exists_section.choose_spec _⟩

include hm hms in
private theorem exists_goodCompact_trivial (k₀ : {k : Subgroup G //
    IsCompact (k : Set G) ∧ IsCompactlyGeneratedGroup (lcaAnnihilator k)}) :
    ∃ l : {k : Subgroup G // IsCompact (k : Set G) ∧ IsCompactlyGeneratedGroup (lcaAnnihilator k)},
      ∀ v : K, v.val ∈ l.val → ω v = 1 := by
  let τ := (exists_surjectiveModulation_section m hm hms).choose
  have hτ (t : ℝ≥0ˣ) : m (τ t) = t := (exists_surjectiveModulation_section m hm hms).choose_spec t
  -- The compact character is trivial on one of the subgroups indexing the stages.
  let two : ℝ≥0ˣ := Units.mk0 2 (by norm_num)
  obtain ⟨χ, _, _, hχ, -⟩ := exists_modulatedCyclicCharacter_lifts m (τ two) τ hτ
    (by rw [hτ]; change (1 : ℝ≥0) < 2; norm_num)
  obtain ⟨l, η, -, hη⟩ := goodCompact_refine_unitaryCharacter k₀ (χ ω)
  refine ⟨l, fun v hv ↦ ?_⟩
  exact (hχ ω v).symm.trans ((hη v.val).symm.trans
    ((congrArg η ((QuotientGroup.eq_one_iff _).mpr hv)).trans (map_one η)))
include hm hms in
private theorem isotype_stage_metrizable_separable (k)
    (hk : IsEmbedding (show ModulatedExponentialDecayStage m univ k → E from modulatedExponentialDecayStageInclusion m univ k))
    (hs : (H₀[ω] : Set E) ⊆ range (modulatedExponentialDecayStageInclusion m univ k)) :
    MetrizableSpace H₀[ω] ∧ SeparableSpace H₀[ω] := by
  exact metrizable_separable_of_subset_range (H₀[ω] : Set E) _ hk hs
    (modulatedExponentialDecayStage_frechet m hm hms univ ordConnected_univ univ_nonempty k).2.2.1
    (modulatedExponentialDecayStage_separable m hm hms univ ordConnected_univ univ_nonempty k)
include hm hms in
private theorem isotype_metrizable_separable : MetrizableSpace H₀[ω] ∧ SeparableSpace H₀[ω] := by
  refine (modulatedExponentialDecay_stageLimit m univ hm hms ordConnected_univ univ_nonempty).elim fun k h ↦ ?_
  refine (exists_goodCompact_trivial m hm hms ω (k 0)).elim fun l hl ↦ ?_
  refine (h.2.1 l).elim fun n hn ↦ ?_
  exact isotype_stage_metrizable_separable m hm hms ω (k n) (h.2.2.1 n)
    (isotype_le_stage_of_trivial m ω (k n) (fun v hv ↦ hl v (hn hv)))

include hm hms in
private theorem isotype_complete : CompleteSpace H₀[ω] := by
  let τ := (exists_surjectiveModulation_section m hm hms).choose
  have hτ (t : ℝ≥0ˣ) : m (τ t) = t := (exists_surjectiveModulation_section m hm hms).choose_spec t
  have : CompleteSpace E :=
    modulatedExponentialDecay_complete m univ hm ordConnected_univ univ_nonempty τ hτ
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  have : T2Space (SchwartzBruhat G) := schwartzBruhat_t2
  have hclosed : IsClosed (H₀[ω] : Set E) := (isClosed_actionIsotype ρK ω).preimage
    (modulatedExponentialDecay_zeroTwist_continuous m hm hms univ ordConnected_univ (mem_univ _))
  exact completeSpace_coe_iff_isComplete.mpr hclosed.isComplete

include hm hms in
private theorem isotype_nuclear : IsNuclearTVS H₀[ω] := by
  let sections := exists_surjectiveModulation_section m hm hms
  exact isNuclearTVS_submodule (modulatedExponentialDecay_nuclear m univ hm
    ordConnected_univ univ_nonempty sections.choose sections.choose_spec) H₀[ω]

private theorem frechet_of_complete_metrizable (X : Type*) [AddCommGroup X] [Module ℂ X]
    [UniformSpace X] [IsUniformAddGroup X] [CompleteSpace X]
    (hP : PolynormableSpace ℂ X) (hM : MetrizableSpace X) : IsFrechetTVS X := by
  refine ⟨inferInstance, hP, hM, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq (G := X)]
  infer_instance

include hm hms in
private theorem isotype_frechet : IsFrechetTVS H₀[ω] := by
  have : CompleteSpace H₀[ω] := isotype_complete m hm hms ω
  have : IsUniformAddGroup H₀[ω] := (H₀[ω]).toAddSubgroup.isUniformAddGroup
  exact frechet_of_complete_metrizable H₀[ω] (isotype_nuclear.{_, 0} m hm hms ω).2.1
    (isotype_metrizable_separable m hm hms ω).1
section
universe v
private theorem isotype_quotient_properties {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] (hS : SeparableSpace X) (hN : IsNuclearTVS.{v} X) (hF : IsFrechetTVS X)
    (M : Submodule ℂ X) (hc : IsClosed (M : Set X)) :
    SeparableSpace (X ⧸ M) ∧ IsNuclearTVS.{v} (X ⧸ M) ∧ IsFrechetTVS (X ⧸ M) := by
  have hQ := isFrechetTVS_quotient hF M hc
  have : MetrizableSpace (X ⧸ M) := hQ.2.2.1
  exact ⟨M.isQuotientMap_mkQL.separableSpace, isNuclearTVS_quotient hN M, hQ⟩

end

end

section

set_option linter.unusedSectionVars false

private theorem cyclicDifference_injective (g : G) (hg : 1 < (m g).val) :
    Injective (modulatedCyclicDifference m g hm hms univ ordConnected_univ univ_nonempty) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro f hf
  change modulatedCyclicDifference m g hm hms univ ordConnected_univ univ_nonempty f = 0 at hf
  have hper (x : G) : f.val (g * x) = f.val x := by
    apply (sub_eq_zero.mp _).symm
    exact (modulatedCyclicDifference_apply m g hm hms univ ordConnected_univ univ_nonempty f x).symm.trans
      (congrArg (fun v : E ↦ v.val x) hf)
  change f = 0
  refine Subtype.ext (funext fun x ↦ ?_)
  have hn (n : ℕ) : f.val (g ^ n * x) = f.val x := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_assoc, hper, ih]
  have hs := (modulatedPeriodization_hasSum m g hm hms hg f x).summable.comp_injective
    (Nat.cast_injective : Injective (fun n : ℕ ↦ (n : ℤ)))
  change Summable (fun n : ℕ ↦ f.val (g ^ (n : ℤ) * x)) at hs
  change f.val x = 0
  simpa only [Function.comp_apply, Int.ofNat_eq_natCast, zpow_natCast, hn, summable_const_iff] using hs

private theorem frechet_closedEmbedding_of_injective {X : Type*} [AddCommGroup X]
    [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    (hX : IsFrechetTVS X) (A : X →L[ℂ] X) (hi : Injective A) (hc : IsClosed (range A)) :
    IsClosedEmbedding A := by
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  have : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have : MetrizableSpace X := hX.2.2.1
  have : CompleteSpace X := hX.2.2.2
  have : CompleteSpace A.range := completeSpace_coe_iff_isComplete.mpr hc.isComplete
  have : IsUniformAddGroup A.range := A.range.toAddSubgroup.isUniformAddGroup
  have : FirstCountableTopology A.range := inferInstanceAs (FirstCountableTopology (A.range : Set X))
  have : (uniformity A.range).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : BaireSpace A.range := BaireSpace.of_completelyPseudoMetrizable
  let F := A.rangeRestrict
  have hs : Surjective F := fun ⟨_, x, hx⟩ ↦ ⟨x, Subtype.ext hx⟩
  have ho : IsOpenMap F := by
    apply isOpenMap_of_not_isMeagre_range F
    rw [hs.range_eq]
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty
  have he : IsEmbedding F := (IsOpenEmbedding.of_continuous_injective_isOpenMap
    F.continuous (fun _ _ h ↦ hi (congrArg Subtype.val h)) ho).isEmbedding
  exact ⟨IsEmbedding.subtypeVal.comp he, hc⟩

private theorem isClosed_range_submodule_restriction {X : Type*} [AddCommGroup X]
    [Module ℂ X] [TopologicalSpace X] (H : Submodule ℂ X) (A : X →L[ℂ] X) (B : H →L[ℂ] H)
    (he : ∀ x : H, (B x).val = A x.val)
    (hh : A.range ⊓ H = H.map A.toLinearMap) (hc : IsClosed (range A)) : IsClosed (range B) := by
  have hr : range B = Subtype.val ⁻¹' range A := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, (he x).symm⟩
    · intro hy
      have hx : y.val ∈ H.map A.toLinearMap := (le_of_eq hh) ⟨hy, y.property⟩
      obtain ⟨x, hx, hxy⟩ := hx
      exact ⟨⟨x, hx⟩, Subtype.ext ((he ⟨x, hx⟩).trans hxy)⟩
  exact (congrArg IsClosed hr).mpr (hc.preimage continuous_subtype_val)

local notation "δ[" g "]" => modulatedCyclicDifference m g hm hms univ ordConnected_univ univ_nonempty

private theorem cyclicDifference_range_inf_isotype (g : G) :
    (δ[g]).range ⊓ H₀[ω] = (H₀[ω]).map (δ[g]).toLinearMap := by
  have h := modulatedCyclicDifference_range_isotype m g hm hms ω
  unfold modulatedDecayIsotype
  unfold modulatedCyclicDifference at h ⊢
  exact h

private theorem isotypicDifference_closedEmbedding (g : G) (hg : 1 < (m g).val)
    (hF : IsFrechetTVS H₀[ω]) : IsClosedEmbedding (P[ω, [g]]) := by
  have he (x : H₀[ω]) : (P[ω, [g]] x).val = δ[g] x.val := by
    unfold modulatedIsotypicDifferenceProduct modulatedDifferenceProduct modulatedCyclicDifference
    rfl
  have hi := cyclicDifference_injective m hm hms g hg
  have hinj : Injective (P[ω, [g]]) := by
    intro x y h
    exact Subtype.ext (hi ((he x).symm.trans ((congrArg Subtype.val h).trans (he y))))
  have hc : IsClosed (range δ[g]) := modulatedCyclicDifference_isClosed_range m g hm hms hg
  have hh := cyclicDifference_range_inf_isotype m hm hms ω g
  have hclosed := isClosed_range_submodule_restriction (X := E) H₀[ω] δ[g] (P[ω, [g]]) he hh hc
  exact frechet_closedEmbedding_of_injective hF (P[ω, [g]]) hinj hclosed

private theorem isotypicDifferenceProduct_nil_fun :
    (P[ω, []] : H₀[ω] → H₀[ω]) = id := by
  unfold modulatedIsotypicDifferenceProduct modulatedDifferenceProduct
  rfl

private theorem isotypicDifferenceProduct_cons_fun (g : G) (s : List G) :
    (P[ω, g :: s] : H₀[ω] → H₀[ω]) = (P[ω, [g]]) ∘ (P[ω, s]) := by
  unfold modulatedIsotypicDifferenceProduct modulatedDifferenceProduct
  rfl


private theorem list_closedEmbedding {L X : Type*} [TopologicalSpace X] (P : List L → X → X)
    (hn : P [] = id) (hc : ∀ g s, P (g :: s) = P [g] ∘ P s) (ok : L → Prop)
    (h : ∀ g, ok g → IsClosedEmbedding (P [g])) (s : List L) (hs : ∀ g ∈ s, ok g) :
    IsClosedEmbedding (P s) := by
  induction s with
  | nil => exact (congrArg IsClosedEmbedding hn).mpr IsClosedEmbedding.id
  | cons g s ih =>
    exact (congrArg IsClosedEmbedding (hc g s)).mpr
      ((h g (hs g (.head _))).comp (ih fun a ha ↦ hs a (.tail _ ha)))

private theorem list_closedRange {L X : Type*} [TopologicalSpace X] (P : List L → X → X)
    (hn : P [] = id) (hc : ∀ g s, P (g :: s) = P [g] ∘ P s) (ok : L → Prop)
    (h : ∀ g, ok g → IsClosedEmbedding (P [g])) (s : List L) (hs : ∀ g ∈ s, ok g) :
    IsClosed (range (P s)) := (list_closedEmbedding P hn hc ok h s hs).isClosed_range


end

include hS₀ in
/-- Paper: Lemma 4.6.1.3(1), p. 210. The product of expanding cyclic
differences has closed range in the norm-one isotype of the decay space. -/
theorem modulatedIsotypicDifferenceProduct_isClosed_range :
    IsClosed (range (P[ω, S₀])) := by
  exact list_closedRange (fun l ↦ (P[ω, l] : H₀[ω] → H₀[ω]))
    (isotypicDifferenceProduct_nil_fun m hm hms ω)
    (isotypicDifferenceProduct_cons_fun m hm hms ω) (fun g ↦ 1 < (m g).val)
    (fun g hg ↦ isotypicDifference_closedEmbedding m hm hms ω g hg (isotype_frechet m hm hms ω))
    S₀ hS₀

include hS₀ in
/-- Paper: Lemma 4.6.1.3(2), p. 210. The isotypic quotient by the difference
product is a separable nuclear Fréchet space. -/
theorem modulatedIsotypicDifferenceProduct_quotient :
    let U := H₀[ω] ⧸ (P[ω, S₀]).range
    SeparableSpace U ∧ IsNuclearTVS U ∧ IsFrechetTVS U := by
  exact isotype_quotient_properties (isotype_metrizable_separable m hm hms ω).2
    (isotype_nuclear m hm hms ω) (isotype_frechet m hm hms ω) (P[ω, S₀]).range
    (modulatedIsotypicDifferenceProduct_isClosed_range m hm hms ω S₀ hS₀)

section

set_option linter.unusedSectionVars false

private theorem range_quotient_actions {X L : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [TopologicalSpace L]
    (A : X →L[ℂ] X) (N : Submodule ℂ X) (M : Submodule ℂ A.range)
    (F : (X ⧸ N) ≃L[ℂ] (A.range ⧸ M))
    (hF : ∀ x, F (N.mkQ x) = M.mkQ (A.rangeRestrict x))
    (t : L → X →L[ℂ] X) (hc : Continuous fun u : L × X ↦ t u.1 u.2)
    (hN : ∀ g x, x ∈ N → t g x ∈ N) (hA : ∀ g x, A (t g x) = t g (A x)) :
    ∃ (ρ : L × (X ⧸ N) → X ⧸ N) (τ : L × (A.range ⧸ M) → A.range ⧸ M),
      Continuous ρ ∧ Continuous τ ∧ (∀ g x, ρ (g, N.mkQ x) = N.mkQ (t g x)) ∧
      (∀ (g : L) (u : A.range), ∃ u' : A.range, u'.val = t g u.val ∧ τ (g, M.mkQ u) = M.mkQ u') ∧
      ∀ g v, F (ρ (g, v)) = τ (g, F v) := by
  obtain ⟨ρ, hρ, hρq⟩ := N.exists_continuous_quotient_family t hc hN
  let τ (p : L × (A.range ⧸ M)) := F (ρ (p.1, F.symm p.2))
  refine ⟨ρ, τ, hρ, F.continuous.comp (hρ.comp
    (continuous_fst.prodMk (F.symm.continuous.comp continuous_snd))), hρq, ?_, ?_⟩
  · intro g u
    obtain ⟨x, hx⟩ := u.property
    have hu : A.rangeRestrict x = u := Subtype.ext hx
    refine ⟨A.rangeRestrict (t g x), (hA g x).trans (congrArg (t g) hx), ?_⟩
    have hrep : F (N.mkQ x) = M.mkQ u := (hF x).trans (congrArg M.mkQ hu)
    have hi : F.symm (M.mkQ u) = N.mkQ x := F.symm_apply_eq.mpr hrep.symm
    exact (congrArg (fun y ↦ F (ρ (g, y))) hi).trans
      ((congrArg F (hρq g x)).trans (hF (t g x)))
  · intro g v
    exact (congrArg (fun y ↦ F (ρ (g, y))) (F.symm_apply_apply v)).symm

private theorem restrict_family_continuous {X L : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [TopologicalSpace L] (H : Submodule ℂ X)
    (A : L → X →L[ℂ] X) (ha : Continuous fun p : L × X ↦ A p.1 p.2)
    (h : ∀ g, ∀ x ∈ H, A g x ∈ H) :
    Continuous (fun p : L × H ↦ (A p.1).restrict (h p.1) p.2) :=
  (ha.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

private theorem translation_preserves_decayIsotype (ρ : G → (E →L[ℂ] E))
    (hρ : ∀ g f x, (ρ g f).val x = f.val (g⁻¹ * x))
    (g : G) (f : E) (hf : f ∈ H₀[ω]) : ρ g f ∈ H₀[ω] := by
  refine (mem_modulatedDecayIsotype_iff m ω univ (mem_univ _) _).mpr fun k x ↦ ?_
  have h := (mem_modulatedDecayIsotype_iff m ω univ (mem_univ _) f).mp hf k (g⁻¹ * x)
  exact (hρ g f _).trans ((congrArg f.val (mul_left_comm _ _ _)).trans
    (h.trans (congrArg ((ω k : ℂ) * ·) (hρ g f x).symm)))

include hm hms in
private theorem isotype_translation_family :
    ∃ t : G → (H₀[ω] →L[ℂ] H₀[ω]), (Continuous fun p : G × H₀[ω] ↦ t p.1 p.2) ∧
      ∀ g f x, (t g f).val.val x = f.val.val (g⁻¹ * x) := by
  refine (exists_modulatedExponentialDecay_translationAction m univ hm hms
    ordConnected_univ univ_nonempty).elim fun ρ h ↦ ?_
  have hi := translation_preserves_decayIsotype m ω (fun g ↦ ρ g) h.1
  let t (g : G) : H₀[ω] →L[ℂ] H₀[ω] := (ρ g).restrict (hi g)
  have he (g : G) (f : H₀[ω]) (x : G) : (t g f).val.val x = f.val.val (g⁻¹ * x) := h.1 g f.val x
  have hc := restrict_family_continuous (X := E) H₀[ω] (fun g ↦ ρ g) h.2 hi
  exact ⟨t, hc, he⟩

private theorem isotype_product_translate (s : List G) (g : G) (f f' : H₀[ω])
    (ht : ∀ x, f'.val.val x = f.val.val (g⁻¹ * x)) :
    ∀ x, (P[ω, s] f').val.val x = (P[ω, s] f).val.val (g⁻¹ * x) := by
  induction s with
  | nil => exact ht
  | cons d s ih =>
    intro x
    have h1 := modulatedCyclicDifference_apply m d hm hms univ ordConnected_univ univ_nonempty
      (P[ω, s] f').val x
    have h2 := modulatedCyclicDifference_apply m d hm hms univ ordConnected_univ univ_nonempty
      (P[ω, s] f).val (g⁻¹ * x)
    exact h1.trans ((congrArg₂ (· - ·) (ih x)
      ((ih (d * x)).trans (congrArg (P[ω, s] f).val.val (mul_left_comm _ _ _)))).trans h2.symm)

private theorem isotype_product_commute_single (s : List G) (g : G) :
    ∀ f : H₀[ω], P[ω, s ++ [g]] f = P[ω, [g]] (P[ω, s] f) := by
  induction s with
  | nil => exact fun _ ↦ rfl
  | cons d s ih =>
    intro f
    have eval (c : G) (u : H₀[ω]) (x : G) :
        (P[ω, [c]] u).val.val x = u.val.val x - u.val.val (c * x) :=
      modulatedCyclicDifference_apply m c hm hms univ ordConnected_univ univ_nonempty _ x
    have hcomm (u : H₀[ω]) (x : G) :
        (P[ω, [d]] (P[ω, [g]] u)).val.val x = (P[ω, [g]] (P[ω, [d]] u)).val.val x := by
      have h1 := eval d (P[ω, [g]] u) x
      have h2 := eval g (P[ω, [d]] u) x
      have h3 := eval g u x
      have h4 := eval g u (d * x)
      have h5 := eval d u x
      have h6 := eval d u (g * x)
      have hx := congrArg u.val.val (mul_left_comm g d x)
      have hcalc (a b c k : ℂ) : (a - b) - (c - k) = (a - c) - (b - k) := by ring
      exact h1.trans ((congrArg₂ (· - ·) h3 h4).trans ((hcalc _ _ _ _).trans
        ((congrArg (fun k ↦ (_ - _) - (_ - k)) hx).trans ((congrArg₂ (· - ·) h5 h6).symm.trans h2.symm))))
    exact (congrArg (P[ω, [d]]) (ih f)).trans
      (Subtype.ext (Subtype.ext (funext (hcomm (P[ω, s] f)))))

section
universe v

private theorem separable_nuclear_frechet_of_equiv {X Y : Type*} [AddCommGroup X]
    [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X] [AddCommGroup Y]
    [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] (F : X ≃L[ℂ] Y)
    (h : SeparableSpace X ∧ IsNuclearTVS.{v} X ∧ IsFrechetTVS X) :
    SeparableSpace Y ∧ IsNuclearTVS.{v} Y ∧ IsFrechetTVS Y := by
  have : SeparableSpace X := h.1
  have : MetrizableSpace X := h.2.2.2.2.1
  have : PolynormableSpace ℂ X := h.2.1.2.1
  have : PolynormableSpace ℂ Y := F.symm.PolynormableSpace
  have hn := nuclear_of_equiv F h.2.1
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  have : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  let U : X ≃ᵤ Y := { __ := F.toEquiv, uniformContinuous_toFun := F.toContinuousLinearMap.uniformContinuous,
                       uniformContinuous_invFun := F.symm.toContinuousLinearMap.uniformContinuous }
  exact ⟨F.surjective.denseRange.separableSpace F.continuous, hn,
    ⟨inferInstance, hn.2.1, F.symm.toHomeomorph.isEmbedding.metrizableSpace,
      U.completeSpace_iff.mp h.2.2.2.2.2⟩⟩

end

section
universe v

private theorem cancel_comm_submodule {L Z : Type*} [TopologicalSpace L] [CommGroup L]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z]
    (H : Submodule ℂ Z)
    (A B C : H →L[ℂ] H) (ha : IsClosedEmbedding A) (hp : ∀ x, C x = A (B x))
    (eval : H → L → ℂ) (hinj : Injective eval)
    (ht : ∃ t : L → H →L[ℂ] H, (Continuous fun p : L × H ↦ t p.1 p.2) ∧
      ∀ g f x, eval (t g f) x = eval f (g⁻¹ * x))
    (hA : ∀ g f f', (∀ x, eval f' x = eval f (g⁻¹ * x)) → ∀ x, eval (A f') x = eval (A f) (g⁻¹ * x))
    (hB : ∀ g f f', (∀ x, eval f' x = eval f (g⁻¹ * x)) → ∀ x, eval (B f') x = eval (B f) (g⁻¹ * x))
    (hX : SeparableSpace (H ⧸ B.range) ∧ IsNuclearTVS.{v} (H ⧸ B.range) ∧ IsFrechetTVS (H ⧸ B.range)) :
    let a := A
    let R := a.range
    let N := B.range
    let M := C.range.comap R.subtype
    let U := H ⧸ N
    let V := R ⧸ M
    ∃ F : U ≃L[ℂ] V, (∀ f, F (N.mkQ f) = M.mkQ (a.rangeRestrict f)) ∧
      (∃ (ρ : L × U → U) (τ : L × V → V), Continuous ρ ∧ Continuous τ ∧
        (∀ g f, ∃ f', (∀ x, eval f' x = eval f (g⁻¹ * x)) ∧ ρ (g, N.mkQ f) = N.mkQ f') ∧
        (∀ g (u : R), ∃ u' : R, (∀ x, eval u'.val x = eval u.val (g⁻¹ * x)) ∧ τ (g, M.mkQ u) = M.mkQ u') ∧
        ∀ g w, F (ρ (g, w)) = τ (g, F w)) ∧
      SeparableSpace (R ⧸ M) ∧ IsNuclearTVS.{v} (R ⧸ M) ∧ IsFrechetTVS (R ⧸ M) := by
  obtain ⟨t, hc, ht⟩ := ht
  have hca (g : L) (f : H) : A (t g f) = t g (A f) :=
    hinj (funext fun x ↦ (hA g f (t g f) (ht g f) x).trans (ht g (A f) x).symm)
  have hcb (g : L) (f : H) : B (t g f) = t g (B f) :=
    hinj (funext fun x ↦ (hB g f (t g f) (ht g f) x).trans (ht g (B f) x).symm)

  dsimp only
  let R := A.range
  let N := B.range
  let M := C.range.comap R.subtype
  have hM (x : H) : A.rangeRestrict x ∈ M ↔ x ∈ N := by
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, ha.injective ((hp y).symm.trans hy)⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, (hp y).trans (congrArg A hy)⟩
  obtain ⟨F, hF⟩ := A.exists_quotient_range_equiv ha.isEmbedding N M hM
  have hN (g : L) (x : H) : x ∈ N → t g x ∈ N := fun ⟨y, hy⟩ ↦
    ⟨t g y, (hcb g y).trans (congrArg (t g) hy)⟩
  obtain ⟨ρ, τ, hρ, hτ, hρq, hτq, he⟩ := range_quotient_actions A N M F hF t hc hN hca
  refine ⟨F, hF, ⟨ρ, τ, hρ, hτ, fun g f ↦ ⟨t g f, ht g f, hρq g f⟩, ?_, he⟩,
    separable_nuclear_frechet_of_equiv F hX⟩
  intro g u
  obtain ⟨u', hu', hq⟩ := hτq g u
  exact ⟨u', fun x ↦ (congrArg (fun y ↦ eval y x) hu').trans (ht g u.val x), hq⟩
end

end

include hS₀ hγ in
/-- Paper: Lemma 4.6.1.3(3), pp. 210–211. Applying the last cyclic difference
identifies the shorter quotient with the last difference image modulo the
full product image. The isomorphism intertwines the jointly continuous
left translation actions on the two quotients. -/
theorem modulatedIsotypicDifferenceProduct_cancel_equiv :
    let A := P[ω, [γ]]
    let R := A.range
    let N := (P[ω, S₀]).range
    let M := (P[ω, S₀ ++ [γ]]).range.comap R.subtype
    let X := H₀[ω] ⧸ N
    let Y := R ⧸ M
    ∃ F : X ≃L[ℂ] Y,
      (∀ f, F (N.mkQ f) = M.mkQ (A.rangeRestrict f)) ∧
      (∃ (ρ : G × X → X) (τ : G × Y → Y), Continuous ρ ∧ Continuous τ ∧
        (∀ g (f : H₀[ω]), ∃ f' : H₀[ω],
          (∀ x, f'.val.val x = f.val.val (g⁻¹ * x)) ∧ ρ (g, N.mkQ f) = N.mkQ f') ∧
        (∀ g (u : R), ∃ u' : R,
          (∀ x, u'.val.val.val x = u.val.val.val (g⁻¹ * x)) ∧ τ (g, M.mkQ u) = M.mkQ u') ∧
        ∀ g v, F (ρ (g, v)) = τ (g, F v)) ∧
      SeparableSpace (R ⧸ M) ∧ IsNuclearTVS (R ⧸ M) ∧ IsFrechetTVS (R ⧸ M) := by
  have ha := isotypicDifference_closedEmbedding m hm hms ω γ hγ (isotype_frechet m hm hms ω)
  have hp := isotype_product_commute_single m hm hms ω S₀ γ
  let ev (x : H₀[ω]) : G → ℂ := x.val.val
  have hi : Injective ev := fun _ _ h ↦ Subtype.ext (Subtype.ext h)
  have ht := isotype_translation_family m hm hms ω
  have hA := isotype_product_translate m hm hms ω [γ]
  have hB := isotype_product_translate m hm hms ω S₀
  with_reducible_and_instances
    exact cancel_comm_submodule (L := G) (Z := E) H₀[ω] (P[ω, [γ]]) (P[ω, S₀]) (P[ω, S₀ ++ [γ]])
      ha hp ev hi ht hA hB (modulatedIsotypicDifferenceProduct_quotient m hm hms ω S₀ hS₀)

end IsotypicQuotient

-- TODO(paper-gap): In Lemma 4.6.1.4(1), bₖ must be replaced by log bₖ.
-- The printed condition holds for b₁ = 2 and b₂ = 3, but log 2 / log 3 is irrational.

/-- Paper: Lemma 4.6.1.4, p. 211. Logarithmic commensurability of the bases
is equivalent to finiteness of all mutual cyclic phases.
Deviation: Part (1) uses log bₖ as in both directions of the proof.

Deviation: Part (1) on p. 211 and the opening assumption of its proof put the bases themselves
in $\mathbb Q\cdot\log(b)$. We use their logarithms, as the subsequent reasoning in both
directions does.
-/
theorem finite_cyclicPhases_iff {N : ℕ} (hN : 0 < N) (b : Fin N → ℝ) (hb : ∀ k, 1 < b k) :
    (∃ a : ℝ, 1 < a ∧ ∀ k, ∃ r : ℚ, Real.log (b k) = (r : ℝ) * Real.log a) ↔
      (range fun p : Fin N × Fin N × ℤ ↦
        Circle.exp (2 * Real.pi * (p.2.2 : ℝ) * (Real.log (b p.1) / Real.log (b p.2.1)))).Finite := by
  let phases (x : ℝ) := range fun n : ℤ ↦ Circle.exp (2 * Real.pi * (n : ℝ) * x)
  -- The phases are the image of the subgroup generated by x in ℝ/ℤ.
  have finite_phases_iff (x : ℝ) : (phases x).Finite ↔ ∃ q : ℚ, (q : ℝ) = x := by
    have himage : phases x = AddCircle.toCircle ''
        (AddSubgroup.zmultiples (x : AddCircle (1 : ℝ)) : Set (AddCircle (1 : ℝ))) := by
      rw [AddSubgroup.coe_zmultiples, ← range_comp']
      apply congrArg range
      funext n
      rw [← AddCircle.coe_zsmul, AddCircle.toCircle_apply_mk, div_one, zsmul_eq_mul, mul_assoc]
    rw [himage, finite_image_iff (AddCircle.injective_toCircle one_ne_zero).injOn]
    change Finite (AddSubgroup.zmultiples (x : AddCircle (1 : ℝ))) ↔ _
    rw [finite_zmultiples, AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div, div_one]
  let ratio (i j : Fin N) := Real.log (b i) / Real.log (b j)
  have hunion : (range fun p : Fin N × Fin N × ℤ ↦
      Circle.exp (2 * Real.pi * (p.2.2 : ℝ) * ratio p.1 p.2.1)) =
      ⋃ i, ⋃ j, phases (ratio i j) := by
    ext z
    simp only [mem_range, Prod.exists, mem_iUnion, phases]
  rw [hunion]
  constructor
  · rintro ⟨a, ha, h⟩
    refine finite_iUnion fun i ↦ finite_iUnion fun j ↦ (finite_phases_iff _).2 ?_
    obtain ⟨r, hr⟩ := h i
    obtain ⟨s, hs⟩ := h j
    refine ⟨r / s, ?_⟩
    simp only [ratio, Rat.cast_div, hr, hs, mul_div_mul_right _ _ (Real.log_pos ha).ne']
  · intro h
    let j : Fin N := ⟨0, hN⟩
    refine ⟨b j, hb j, fun i ↦ ?_⟩
    have hi := h.subset (subset_iUnion₂ i j)
    obtain ⟨q, hq⟩ := (finite_phases_iff _).mp hi
    exact ⟨q, ((eq_div_iff (Real.log_pos (hb j)).ne').mp hq).symm⟩

section Moments

variable {N : ℕ} (γs : Fin N → G)

/-- Paper: Equation (4.6.1.12), p. 212. The periodic spectrum is the union of
the cyclic annihilator fibers for the given norm-one character. -/
def modulatedPeriodicSpectrum (m : G →ₜ* ℝ≥0ˣ) (ω : PontryaginDual m.toMonoidHom.ker)
    (γs : Fin N → G) : Set (PontryaginDual G) :=
  ⋃ k, modulatedCyclicAnnihilatorFiber m ω (γs k)

/-- Paper: Equations (4.6.1.12)–(4.6.1.13), p. 212. The spectrum multiplicity
counts the entries whose cyclic fiber contains the character, including repetitions.
Deviation: The multiplicity is extended by zero off the union. -/
def modulatedPeriodicMultiplicity (m : G →ₜ* ℝ≥0ˣ) (ω : PontryaginDual m.toMonoidHom.ker)
    (γs : Fin N → G) (ξ : PontryaginDual G) : ℕ :=
  haveI : DecidablePred (fun k : Fin N ↦ ξ ∈ modulatedCyclicAnnihilatorFiber m ω (γs k)) :=
    Classical.decPred _
  (Finset.univ.filter fun k ↦ ξ ∈ modulatedCyclicAnnihilatorFiber m ω (γs k)).card

/-- Paper: Equations (4.6.1.12)–(4.6.1.13), p. 212. The spectrum consists
exactly of the characters of positive multiplicity. -/
theorem mem_modulatedPeriodicSpectrum_iff (ξ : PontryaginDual G) :
    ξ ∈ modulatedPeriodicSpectrum m ω γs ↔ 0 < modulatedPeriodicMultiplicity m ω γs ξ := by
  classical
  simp only [modulatedPeriodicSpectrum, modulatedPeriodicMultiplicity, Set.mem_iUnion,
    Finset.card_pos, Finset.Nonempty, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Paper: Equation (4.6.1.13) and Example 4.6.1.6, pp. 212, 217.
Every character in the fiber for a twice-repeated generator has multiplicity two. -/
theorem modulatedPeriodicMultiplicity_repeat (ξ : PontryaginDual G)
    (hξ : ξ ∈ modulatedCyclicAnnihilatorFiber m ω γ) :
    modulatedPeriodicMultiplicity m ω (fun _ : Fin 2 ↦ γ) ξ = 2 := by
  classical
  simp [modulatedPeriodicMultiplicity, hξ]

variable (hγs : ∀ k, 1 < (m (γs k)).val)

omit hSC in
/-- The annihilator of a subgroup is closed in the dual group. -/
private theorem isClosed_lcaAnnihilator_coe (H : Subgroup G) :
    IsClosed (lcaAnnihilator H : Set (PontryaginDual G)) := by
  have : (lcaAnnihilator H : Set (PontryaginDual G)) = ⋂ x : H, {ξ | ξ x.val = 1} := by
    ext ξ; simp [mem_lcaAnnihilator_iff]
  rw [this]
  exact isClosed_iInter fun x ↦ isClosed_eq
    (continuous_eval_const (F := ContinuousMonoidHom G Circle) x.val) continuous_const

include hm hγs in
/-- Paper: Equation (4.6.1.12), p. 212. The finite union of the cyclic
fibers is discrete in the unitary dual. -/
theorem modulatedPeriodicSpectrum_isDiscrete :
    IsDiscrete (modulatedPeriodicSpectrum m ω γs) := by
  have hann (k : Fin N) :
      IsDiscrete (lcaAnnihilator (Subgroup.zpowers (γs k)) : Set (PontryaginDual G)) :=
    isDiscrete_iff_discreteTopology.mpr
      (modulatedCyclicAnnihilator_discrete m (γs k) hm (hγs k))
  have hsub (k : Fin N) : modulatedCyclicAnnihilatorFiber m ω (γs k) ⊆
      lcaAnnihilator (Subgroup.zpowers (γs k)) := fun _ h ↦ h.1
  exact IsDiscrete.iUnion (fun k ↦ (hann k).mono (hsub k)) fun k ↦
    isClosed_of_subset_discrete_closed (hsub k) (hann k) (isClosed_lcaAnnihilator_coe _)

variable (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G)
variable (hχ : ∀ (ω' : PontryaginDual m.toMonoidHom.ker) (u : m.toMonoidHom.ker), χ ω' u.val = ω' u)
variable (t₀ : Fin N → PontryaginDual m.toMonoidHom.ker → ℝ)
variable (ht₀ : ∀ k ω',
  let L := Real.log ((m (γs k)).val : ℝ)
  t₀ k ω' ∈ Ico 0 (2 * Real.pi / L) ∧ Circle.exp (t₀ k ω' * L) = χ ω' (γs k))

local notation "freq[" k "," n "]" =>
  ((PontryaginDual.map
    (⟨QuotientGroup.mk' (Subgroup.zpowers (γs k)), QuotientGroup.continuous_mk⟩ :
      G →ₜ* (G ⧸ Subgroup.zpowers (γs k)))
    (modulatedCyclicCharacter m (γs k) (hγs k) χ (t₀ k) (ht₀ k) (ω, n)))⁻¹)

/-- Every unitary character of the positive reals is `t ↦ exp(i s log t)` for some real `s`. -/
private theorem exists_circleExp_freq (ψ : PontryaginDual ℝ≥0ˣ) :
    ∃ s : ℝ, ∀ t, ψ t = Circle.exp (s * Real.log ((t : ℝ≥0) : ℝ)) := by
  let c : ℝ≥0ˣ →ₜ* ℂ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ψ
  obtain ⟨z, ⟨hz0, hz⟩, -⟩ := existsUnique_unitaryComplexPower c (fun t ↦ Circle.norm_coe (ψ t))
  have hz' : (z.im : ℂ) * Complex.I = z := by apply Complex.ext <;> simp [hz0]
  refine ⟨z.im, fun t ↦ Circle.ext ((hz t).trans ?_)⟩
  have hpos : 0 < ((t : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt t)
  rw [Circle.coe_exp, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
    ← Complex.ofReal_log hpos.le]
  conv_lhs => rw [← hz']
  congr 1
  push_cast
  ring

include hm hms hχ in
/-- Paper: Situation 4.6.1.1(5) and Theorem 4.6.1.5, pp. 209, 212.
The integer frequency parametrizes each cyclic fiber bijectively.
Deviation: Frequencies have denominator log |γₖ| and use the normalized phase.
The character is the inverse of the pulled-back basis character of §4.4.

Deviation: Part (4) on p. 209 leaves the restriction equation unfinished. We require
$\chi\vert_{G^1}=\omega$. The phase equation in part (5) determines the phase modulo $2\pi/L_k$.
We choose it in $[0,2\pi/L_k)$, where $L_k=\log\lvert\gamma_k\rvert_G$, as on pp. 192 and 215.
-/
theorem modulatedPeriodicFrequency_bijective (k : Fin N) :
    Injective (fun n : ℤ ↦ freq[k, n]) ∧
      range (fun n : ℤ ↦ freq[k, n]) = modulatedCyclicAnnihilatorFiber m ω (γs k) := by
  have hpos (x : G) : 0 < ((m x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hL : 0 < Real.log ((m (γs k)).val : ℝ) := Real.log_pos (by exact_mod_cast hγs k)
  have hlog (l : ℝ) : ∃ x : G, Real.log ((m x).val : ℝ) = l := by
    obtain ⟨x, hx⟩ := hms (Units.mk0 ⟨Real.exp l, (Real.exp_pos l).le⟩
      fun h ↦ (Real.exp_pos l).ne' (congrArg Subtype.val h))
    exact ⟨x, by rw [hx]; exact Real.log_exp l⟩
  have hfreq (n : ℤ) (x : G) : freq[k, n] x = χ ω x * Circle.exp
      (-((t₀ k ω - 2 * Real.pi * (n : ℝ) / Real.log ((m (γs k)).val : ℝ)) *
        Real.log ((m x).val : ℝ))) := by
    change (modulatedCyclicCharacter m (γs k) (hγs k) χ (t₀ k) (ht₀ k) (ω, n)
      (QuotientGroup.mk x))⁻¹ = _
    rw [modulatedCyclicCharacter_mk, Circle.exp_neg, mul_inv, inv_inv]
  refine ⟨fun n₁ n₂ h ↦ ?_, ?_⟩
  · by_contra hne
    have hd : ((n₁ : ℝ) - n₂) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
    obtain ⟨x, hx⟩ := hlog (Real.log ((m (γs k)).val : ℝ) / (2 * ((n₁ : ℝ) - n₂)))
    have hx' := DFunLike.congr_fun h x
    simp only [hfreq, hx] at hx'
    have key (a b : ℝ) (hab : Circle.exp a = Circle.exp b) (hπ : a - b = Real.pi) : False :=
      Circle.exp_pi_ne_one (by rw [← hπ, Circle.exp_sub, hab, div_self'])
    refine key _ _ (mul_left_cancel hx') ?_
    field_simp
    ring
  · ext ξ
    rw [mem_modulatedCyclicAnnihilatorFiber_iff]
    constructor
    · rintro ⟨n, rfl⟩
      refine ⟨?_, fun u ↦ ?_⟩
      · rw [hfreq, ← (ht₀ k ω).2, ← Circle.exp_add]
        convert Circle.exp_two_pi_mul_int n using 2
        field_simp
        ring
      · rw [hfreq, show m u.val = 1 from u.2, hχ]
        simp
    · rintro ⟨hγ, hK⟩
      obtain ⟨τ₀, hτ₀⟩ := hm.exists_section
      let τ : ℝ≥0ˣ →ₜ* G := τ₀.comp
        ⟨(MonoidHom.id ℝ≥0ˣ).codRestrict _ fun t ↦ MonoidHom.mem_range.mpr (hms t),
          continuous_id.subtype_mk _⟩
      have hτ (t : ℝ≥0ˣ) : m (τ t) = t := hτ₀ _
      let φ : PontryaginDual G := ξ * (χ ω)⁻¹
      have hφ (x : G) : φ x = ξ x * (χ ω x)⁻¹ := rfl
      obtain ⟨s, hs⟩ := exists_circleExp_freq (φ.comp τ)
      have hξx (x : G) : ξ x = χ ω x * Circle.exp (s * Real.log ((m x).val : ℝ)) := by
        have hmem : x * (τ (m x))⁻¹ ∈ K := by
          rw [MonoidHom.mem_ker, map_mul, map_inv]
          change m x * (m (τ (m x)))⁻¹ = 1
          rw [hτ, mul_inv_cancel]
        have h1 : φ (x * (τ (m x))⁻¹) = 1 := by
          rw [hφ]
          exact mul_inv_eq_one.mpr ((hK ⟨_, hmem⟩).trans (hχ ω ⟨_, hmem⟩).symm)
        rw [map_mul, map_inv, mul_inv_eq_one] at h1
        have h2 : φ (τ (m x)) = Circle.exp (s * Real.log ((m x).val : ℝ)) := hs (m x)
        rw [← h2, ← h1, hφ, mul_comm, inv_mul_cancel_right]
      have h3 := hξx (γs k)
      rw [hγ, ← (ht₀ k ω).2, ← Circle.exp_add, eq_comm, Circle.exp_eq_one] at h3
      obtain ⟨n, hn⟩ := h3
      refine ⟨n, DFunLike.ext _ _ fun x ↦ ?_⟩
      rw [hfreq, hξx]
      have hs' : s = (n * (2 * Real.pi) - t₀ k ω * Real.log ((m (γs k)).val : ℝ)) /
          Real.log ((m (γs k)).val : ℝ) := by
        rw [eq_div_iff hL.ne']
        linarith
      congr 2
      rw [hs']
      field_simp
      ring

variable [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [hμHaar : μ.IsHaarMeasure]

local notation "integrand[" ξ "," r "," f "]" =>
  (fun g : G ↦ (f : H₀[ω]).val.val g * (ξ g : ℂ) * (period g : ℂ) ^ (r : ℕ))

section

set_option linter.unusedSectionVars false

private theorem frechet_barrelled (X : Type*) [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    (hF : IsFrechetTVS X) : BarrelledSpace ℂ X := by
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  have : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have : MetrizableSpace X := hF.2.2.1
  have : CompleteSpace X := hF.2.2.2
  have : (uniformity X).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : BaireSpace X := BaireSpace.of_completelyPseudoMetrizable
  infer_instance

private theorem integrable_logMoment (ξ : PontryaginDual G) (r : ℕ) (f : H₀[ω]) :
    Integrable (integrand[ξ, r, f]) μ := by
  let v := f.val.val
  let t (x : G) : ℝ := (m x).val
  have ht (x : G) : 0 < t x := NNReal.coe_pos.mpr (Units.zero_lt _)
  have htw (c : ℝ) : Integrable (fun x ↦ ((t x ^ c : ℝ) : ℂ) * v x) μ := by
    let w := modulatedExponentialDecayTwist m univ ⟨c, mem_univ _⟩ f.val
    exact ((schwartzBruhat_fourier_equiv μ).choose_spec w).1
  have h0 : Integrable v μ := (htw 0).congr (ae_of_all μ fun x ↦ by
    simp only [Real.rpow_zero, Complex.ofReal_one, one_mul])
  have hchar : Continuous (fun x : G ↦ (ξ x : ℂ)) := continuous_subtype_val.comp ξ.continuous
  have hlog : Continuous (fun x ↦ (Real.log (t x) : ℂ)) :=
    Complex.continuous_ofReal.comp ((NNReal.continuous_coe.comp
      (Units.continuous_val.comp m.continuous)).log fun x ↦ (ht x).ne')
  have hmeas := (h0.aestronglyMeasurable.mul hchar.aestronglyMeasurable).mul
    (hlog.pow r).aestronglyMeasurable
  have hmajor := (((htw 1).norm.add (htw (-1)).norm).const_mul (r.factorial : ℝ))
  apply hmajor.mono' hmeas
  refine ae_of_all μ fun x ↦ ?_
  have ht' := ht x
  have hbound : |Real.log (t x)| ^ r ≤ r.factorial * (t x + (t x)⁻¹) := by
    have h := (div_le_iff₀ (show 0 < (r.factorial : ℝ) by positivity)).mp
      (Real.pow_div_factorial_le_exp _ (abs_nonneg (Real.log (t x))) r)
    have he : Real.exp |Real.log (t x)| ≤ t x + (t x)⁻¹ := by
      rcases le_total 0 (Real.log (t x)) with hp | hn
      · rw [abs_of_nonneg hp, Real.exp_log ht']
        exact le_add_of_nonneg_right (inv_nonneg.mpr ht'.le)
      · rw [abs_of_nonpos hn, Real.exp_neg, Real.exp_log ht']
        exact le_add_of_nonneg_left ht'.le
    exact h.trans ((mul_le_mul_of_nonneg_right he (by positivity)).trans_eq (mul_comm _ _))
  change ‖v x * (ξ x : ℂ) * (Real.log (t x) : ℂ) ^ r‖ ≤
    (r.factorial : ℝ) * (‖((t x ^ (1 : ℝ) : ℝ) : ℂ) * v x‖ +
      ‖((t x ^ (-1 : ℝ) : ℝ) : ℂ) * v x‖)
  simpa only [norm_mul, Circle.norm_coe, mul_one, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Real.rpow_one, Real.rpow_neg_one, abs_of_pos ht', abs_of_pos (inv_pos.mpr ht')] using
    (mul_le_mul_of_nonneg_left hbound (norm_nonneg (v x))).trans_eq (by ring)

include hm hms in
private theorem isotype_eval_continuous (x : G) : Continuous (fun f : H₀[ω] ↦ f.val.val x) := by
  let Z := modulatedExponentialDecayTwist m univ ⟨0, mem_univ _⟩
  have hv : Continuous fun f : H₀[ω] ↦ Z f.val x :=
    (continuous_schwartzBruhat_eval x).comp ((modulatedExponentialDecay_zeroTwist_continuous
      m hm hms univ ordConnected_univ (mem_univ _)).comp continuous_subtype_val)
  have hzero (t : ℝ) (z : ℂ) : ((t ^ (0 : ℝ) : ℝ) : ℂ) * z = z := by simp
  have he (f : H₀[ω]) : Z f.val x = f.val.val x :=
    (modulatedExponentialDecayTwist_apply m univ ⟨0, mem_univ _⟩ f.val x).trans (hzero _ _)
  exact hv.congr he

end

include hm hms hμHaar in
/-- Paper: Equation (4.6.1.14), p. 212. Every log-moment is integrable and
its integral defines a continuous linear functional on the isotype.
Deviation: Integrability and continuity hold for all unitary characters and
all natural log-powers. Descent to the quotient imposes the multiplicity bound. -/
theorem modulatedLogMoment_linearContinuous (ξ : PontryaginDual G) (r : ℕ) :
    (∀ f : H₀[ω], Integrable (integrand[ξ, r, f]) μ) ∧
      IsLinearMap ℂ (fun f : H₀[ω] ↦ ∫ g, integrand[ξ, r, f] g ∂μ) ∧
      Continuous (fun f : H₀[ω] ↦ ∫ g, integrand[ξ, r, f] g ∂μ) := by
  have hi := integrable_logMoment m ω μ ξ r
  have lin : IsLinearMap ℂ (fun f : H₀[ω] ↦ integrand[ξ, r, f]) := by
    constructor
    · intro f h
      funext x
      exact (congrArg (· * (period x : ℂ) ^ r) (add_mul (f.val.val x) (h.val.val x) (ξ x : ℂ))).trans
        (add_mul _ _ _)
    · intro c f
      funext x
      exact (congrArg (· * (period x : ℂ) ^ r) (mul_assoc c (f.val.val x) (ξ x : ℂ))).trans
        (mul_assoc _ _ _)
  have hc (x : G) : Continuous (fun f : H₀[ω] ↦ integrand[ξ, r, f] x) :=
    ((isotype_eval_continuous m hm hms ω x).mul continuous_const).mul continuous_const
  have hF := isotype_frechet m hm hms ω
  have : MetrizableSpace H₀[ω] := hF.2.2.1
  have : BarrelledSpace ℂ H₀[ω] := frechet_barrelled H₀[ω] hF
  exact ⟨hi, MeasureTheory.linearContinuous_integral_of_continuous_eval μ (fun f : H₀[ω] ↦ integrand[ξ, r, f]) lin hi hc⟩

/-- Paper: Equation (4.6.1.14), p. 212. The log-moment integrates the test
function against a unitary character times the indicated power of the log-module. -/
def modulatedLogMoment (ξ : PontryaginDual G) (r : ℕ) : StrongDual ℂ H₀[ω] :=
  let h := modulatedLogMoment_linearContinuous (m := m) (hm := hm) (hms := hms) (ω := ω) (μ := μ) ξ r
  ⟨IsLinearMap.mk' (fun f : H₀[ω] ↦ ∫ g, integrand[ξ, r, f] g ∂μ) h.2.1, h.2.2⟩

/-- An integrand weighted by a function equal to one and a zeroth power integrates to the
unweighted integral. -/
private theorem integral_mul_one_mul_pow_zero {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (φ ξ L : X → ℂ) (hξ : ∀ x, ξ x = 1) : ∫ x, φ x * ξ x * L x ^ (0 : ℕ) ∂ν = ∫ x, φ x ∂ν := by
  simp [hξ]

/-- The trivial character takes the value one. -/
private theorem coe_one_pontryaginDual_apply {H : Type*} [CommGroup H] [TopologicalSpace H]
    (g : H) : (((1 : PontryaginDual H) g : Circle) : ℂ) = 1 := by
  simp

-- The binders below are the section variables, written out. Stated with the section
-- variables themselves, every complete proof of this theorem fails to finish elaborating
-- (even a one-term application of a lemma with the same type), while this form takes seconds.
-- The universe is named `u_1` to keep the statement identical to the section-variable form.
/-- Paper: Equation (4.6.1.14), p. 212. The zeroth moment at the trivial
character is the integral of the test function. -/
theorem modulatedLogMoment_one_zero {G : Type u_1} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [hSC : SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (ω : PontryaginDual m.toMonoidHom.ker) [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [hμHaar : μ.IsHaarMeasure]
    (f : modulatedDecayIsotype m (Set.univ : Set ℝ) (Set.mem_univ (0 : ℝ)) ω) :
    modulatedLogMoment (m := m) (hm := hm) (hms := hms) (ω := ω) (μ := μ) 1 0 f = ∫ g, f.val.val g ∂μ := by
  unfold modulatedLogMoment
  exact integral_mul_one_mul_pow_zero μ _ _ _ fun g ↦ coe_one_pontryaginDual_apply g

local notation "J" => {p : PontryaginDual G × ℕ // p.2 < modulatedPeriodicMultiplicity m ω γs p.1}
local notation "S" => List.ofFn γs
local notation "R" => (P[ω, S]).range
local notation "U" => (H₀[ω] ⧸ R)

open Polynomial in
private theorem integral_difference_polynomial (ξ : PontryaginDual G) (g : G)
    (v : G → ℂ) (hv : ∀ r : ℕ, Integrable (fun x ↦ v x * (ξ x : ℂ) * (period x : ℂ) ^ r) μ)
    (p : ℂ[X]) :
    let w (q : ℂ[X]) (x : G) := (ξ x : ℂ) * q.eval (period x : ℂ)
    let q := p - C (ξ g⁻¹ : ℂ) * taylor (-(period g : ℂ)) p
    (∫ x, (v x - v (g * x)) * w p x ∂μ) =
      ∫ x, v x * w q x ∂μ := by
  intro w q
  have hi (a : ℂ[X]) : Integrable (fun x ↦ v x * w a x) μ := by
    induction a using Polynomial.induction_on' with
    | add a b ha hb =>
      exact (ha.add hb).congr (Filter.Eventually.of_forall fun x ↦ by
        simp only [Pi.add_apply, w, eval_add, mul_add])
    | monomial n c =>
      have h := hv n
      exact (h.const_mul c).congr (Filter.Eventually.of_forall fun x ↦ by
        change c * (v x * (ξ x : ℂ) * _) = _
        simp only [w, eval_monomial]; ring)
  let b := C (ξ g⁻¹ : ℂ) * taylor (-(period g : ℂ)) p
  have hshift (x : G) : w b (g * x) = w p x := by
    have hg : 0 < ((m g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    have hx : 0 < ((m x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    have hlog : (period (g * x) : ℂ) = (period g : ℂ) + (period x : ℂ) := by
      rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul hg.ne' hx.ne', Complex.ofReal_add]
    simp only [b, w, eval_mul, eval_C, taylor_eval, hlog, add_neg_cancel_comm,
      map_mul ξ, Circle.coe_mul, map_inv ξ, Circle.coe_inv]
    have hne : (ξ g : ℂ) ≠ 0 := Circle.coe_ne_zero _
    field_simp
  have hb := (hi b).comp_mul_left g
  have hpow (x : G) : v x * w q x = v x * w p x - v x * w b x := by
    simp only [q, b, w, eval_sub, mul_sub]
  have hsplit (x : G) : (v x - v (g * x)) * w p x =
      v x * w p x - v (g * x) * w b (g * x) := by rw [sub_mul, hshift]
  simp_rw [hsplit, hpow]
  rw [integral_sub (hi p) hb, integral_sub (hi p) (hi b)]
  exact congrArg (_ - ·) (integral_mul_left_eq_self (fun x ↦ v x * w b x) g)

open scoped Classical in
open Polynomial in
/-- A log-polynomial moment of an iterated cyclic difference vanishes whenever
the polynomial degree is less than the number of factors on whose generator
the character is trivial in the selected norm-one isotype. -/
theorem integral_differenceProduct_polynomial (ξ : PontryaginDual G)
    (v : List G → G → ℂ)
    (hdiff : ∀ g l x, v (g :: l) x = v l x - v l (g * x))
    (hint : ∀ l r, Integrable (fun x ↦ v l x * (ξ x : ℂ) * (period x : ℂ) ^ (r : ℕ)) μ)
    (l : List G) (p : ℂ[X])
    (hdeg : p.degree < (l.countP (fun g ↦ decide (ξ ∈ modulatedCyclicAnnihilatorFiber m ω g)) : ℕ)) :
    ∫ x, v l x * ((ξ x : ℂ) * p.eval (period x : ℂ)) ∂μ = 0 := by
  classical
  induction l generalizing p with
  | nil =>
    have hp : p = 0 := by
      by_contra hn
      simp [Polynomial.degree_eq_natDegree hn] at hdeg
    subst p
    simp only [eval_zero, mul_zero, integral_zero]
  | cons g l ih =>
    by_cases hp : p = 0
    · subst p
      simp only [eval_zero, mul_zero, integral_zero]
    let q := p - C (ξ g⁻¹ : ℂ) * taylor (-(period g : ℂ)) p
    have hd : q.degree < (l.countP (fun g ↦ decide (ξ ∈ modulatedCyclicAnnihilatorFiber m ω g)) : ℕ) := by
      by_cases h : ξ ∈ modulatedCyclicAnnihilatorFiber m ω g
      · have hg := ((mem_modulatedCyclicAnnihilatorFiber_iff m ω g ξ).mp h).1
        have hq : q.degree < p.degree := by
          simp only [q, map_inv, hg, inv_one, Circle.coe_one, C_1, one_mul]
          exact degree_sub_lt_left (by simp) hp (by simp)
        rw [degree_eq_natDegree hp] at hdeg hq
        simp [h] at hdeg
        have hnat : p.natDegree < l.countP (fun g ↦ decide (ξ ∈ modulatedCyclicAnnihilatorFiber m ω g)) + 1 := by exact_mod_cast hdeg
        exact hq.trans_le (by exact_mod_cast Nat.le_of_lt_succ hnat)
      · simp [h] at hdeg
        exact (degree_sub_le _ _).trans_lt (by
          rw [degree_C_mul (Circle.coe_ne_zero _), degree_taylor, max_self]; exact hdeg)
    refine (integral_congr_ae (ae_of_all μ fun x ↦ congrArg (· * _) (hdiff g l x))).trans ?_
    exact (integral_difference_polynomial m μ ξ g (v l) (hint l) p).trans (ih q hd)

include hγs in
/-- Paper: Theorem 4.6.1.5 and Equation (4.6.1.15), p. 212.
Log-moments of order strictly below the multiplicity vanish on the
isotypic difference product, so they descend to the quotient. -/
theorem modulatedLogMoment_range_le_ker (j : J) :
    R ≤ (modulatedLogMoment (m := m) (hm := hm) (hms := hms) (ω := ω) (μ := μ) j.val.1 j.val.2).ker := by
  classical
  rintro _ ⟨f, rfl⟩
  let v (l : List G) := (P[ω, l] f).val.val
  have h := integral_differenceProduct_polynomial m ω μ j.val.1 v
    (fun g l x ↦ modulatedCyclicDifference_apply m g hm hms univ ordConnected_univ univ_nonempty _ x)
    (fun l r ↦ (modulatedLogMoment_linearContinuous m hm hms ω μ j.val.1 r).1 (P[ω, l] f))
    S (Polynomial.X ^ j.val.2) (by
      simpa [List.countP_ofFn, modulatedPeriodicMultiplicity] using j.property)
  have heval (x : G) : (Polynomial.X ^ j.val.2 : Polynomial ℂ).eval (period x : ℂ) =
      (period x : ℂ) ^ j.val.2 := by rw [Polynomial.eval_pow, Polynomial.eval_X]
  exact (integral_congr_ae (ae_of_all μ fun x ↦ (mul_assoc _ _ _).trans
    (congrArg (fun t ↦ v S x * ((j.val.1 x : ℂ) * t)) (heval x).symm))).trans h

/-- Paper: Equation (4.6.1.15), p. 212. Each allowed log-moment is viewed
as a member of the strong dual of the difference quotient. -/
def modulatedQuotientLogMoment (j : J) : StrongDual ℂ U :=
  (R).liftQL (modulatedLogMoment (m := m) (hm := hm) (hms := hms) (ω := ω) (μ := μ) j.val.1 j.val.2)
    (modulatedLogMoment_range_le_ker (m := m) (hm := hm) (hms := hms)
      (ω := ω) (γs := γs) (hγs := hγs) (μ := μ) j)

local notation "D" =>
  (modulatedQuotientLogMoment (m := m) (hm := hm) (hms := hms)
    (ω := ω) (γs := γs) (hγs := hγs) (μ := μ))

/-- Paper: Equations (4.6.1.14)–(4.6.1.15), p. 212. On a quotient
representative the descended moment is the original log-moment integral. -/
theorem modulatedQuotientLogMoment_mkQ (j : J) (f : H₀[ω]) :
    D j ((R).mkQ f) = ∫ g, integrand[j.val.1, j.val.2, f] g ∂μ := rfl

-- TODO(paper-gap): Theorem 4.6.1.5 as printed assumes commensurability of the
-- logarithms of the periods. A unit period and a Liouville period satisfy that
-- hypothesis, but their distinct lattice frequencies can approach each other
-- faster than any inverse power. See the report for the counterexample.

/-- A circle exponential of a multiple of the logarithm is a purely imaginary complex power. -/
private theorem coe_circleExp_mul_log (s : ℝ) (t : ℝ≥0ˣ) :
    (Circle.exp (s * Real.log ((t : ℝ≥0) : ℝ)) : ℂ) =
      (((t : ℝ≥0) : ℝ) : ℂ) ^ ((s : ℂ) * Complex.I) := by
  have hpos : 0 < ((t : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt t)
  rw [Circle.coe_exp, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
    ← Complex.ofReal_log hpos.le]
  congr 1
  push_cast
  ring

/-- For each real frequency, `t ↦ exp(i s log t)` is a unitary character of the positive reals. -/
private theorem exists_positiveRealCharacter (s : ℝ) :
    ∃ ψ : PontryaginDual ℝ≥0ˣ, ∀ t, ψ t = Circle.exp (s * Real.log ((t : ℝ≥0) : ℝ)) := by
  have hpos (t : ℝ≥0ˣ) : 0 < ((t : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt t)
  refine ⟨{ toFun := fun t ↦ Circle.exp (s * Real.log ((t : ℝ≥0) : ℝ))
            map_one' := by simp
            map_mul' := fun t u ↦ by
              simp only [Units.val_mul, NNReal.coe_mul]
              rw [Real.log_mul (hpos t).ne' (hpos u).ne', mul_add, Circle.exp_add]
            continuous_toFun := Circle.exp.continuous.comp (continuous_const.mul
              ((NNReal.continuous_coe.comp Units.continuous_val).log
                fun t ↦ (hpos t).ne')) }, fun _ ↦ rfl⟩

/-- Every unitary character of the positive reals is `t ↦ exp(i s log t)` for a unique `s`. -/
private theorem existsUnique_positiveRealCharacter_freq (ψ : PontryaginDual ℝ≥0ˣ) :
    ∃! s : ℝ, ∀ t, ψ t = Circle.exp (s * Real.log ((t : ℝ≥0) : ℝ)) := by
  let c : ℝ≥0ˣ →ₜ* ℂ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ψ
  obtain ⟨z, ⟨hz0, hz⟩, -⟩ := existsUnique_unitaryComplexPower c (fun t ↦ Circle.norm_coe (ψ t))
  obtain ⟨w, -, hw⟩ := existsUnique_complexPower c
  have hz' : (z.im : ℂ) * Complex.I = z := by apply Complex.ext <;> simp [hz0]
  refine ⟨z.im, fun t ↦ Circle.ext ?_, fun s hs ↦ ?_⟩
  · rw [coe_circleExp_mul_log, hz']
    exact hz t
  · have h1 := hw _ fun t ↦ (congrArg Subtype.val (hs t)).trans (coe_circleExp_mul_log s t)
    have h2 := hw _ fun t ↦ (hz t).trans (congrArg _ hz'.symm)
    have := mul_right_cancel₀ Complex.I_ne_zero (h1.trans h2.symm)
    exact_mod_cast this

/-- Through a section of the modulation, a character of the norm-one subgroup extends to a
character trivial on the section, and every extension is that one times a character of the
section. -/
private theorem exists_baseCharacter_of_section (τ : ℝ≥0ˣ →ₜ* G)
    (hτ : ∀ t, m (τ t) = t) :
    ∃ ξ₀ : PontryaginDual G, (∀ u : K, ξ₀ u.val = ω u) ∧ (∀ t, ξ₀ (τ t) = 1) ∧
      ∀ ξ : PontryaginDual G, (∀ u : K, ξ u.val = ω u) → ∀ g, ξ g = ξ₀ g * ξ (τ (m g)) := by
  have hmem (g : G) : g * (τ (m g))⁻¹ ∈ K := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change m g * (m (τ (m g)))⁻¹ = 1
    rw [hτ, mul_inv_cancel]
  let r : G →ₜ* K :=
    { toFun := fun g ↦ ⟨g * (τ (m g))⁻¹, hmem g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h ↦ Subtype.ext (by
        simp only [map_mul, Subgroup.coe_mul, mul_inv]
        ac_rfl)
      continuous_toFun := (continuous_id.mul (τ.continuous.comp m.continuous).inv).subtype_mk _ }
  have hr (g : G) : ((r g : K) : G) = g * (τ (m g))⁻¹ := rfl
  have hsplit (g : G) : g = (r g : G) * τ (m g) := by rw [hr, inv_mul_cancel_right]
  refine ⟨ω.comp r, fun u ↦ ?_, fun t ↦ ?_, fun ξ hξ g ↦ ?_⟩
  · change ω (r u) = ω u
    congr 1
    apply Subtype.ext
    rw [hr, show m u.val = 1 from u.2, map_one, inv_one, mul_one]
  · change ω (r (τ t)) = 1
    rw [show r (τ t) = 1 from Subtype.ext (by rw [hr, hτ, mul_inv_cancel]; rfl), map_one]
  · conv_lhs => rw [hsplit g, map_mul, hξ]
    rfl


include hm hms hγs in
/-- Paper: Theorem 4.6.1.5, p. 212. The moment index is countably infinite,
so the arbitrary enumerations used for the bases exist. -/
theorem modulatedPeriodicMomentIndex_enumerable (hN : 0 < N) :
    Nonempty (ℕ ≃ J) := by
  classical
  obtain ⟨τ₀, hτ₀⟩ := hm.exists_section
  let τ : ℝ≥0ˣ →ₜ* G := τ₀.comp
    ⟨(MonoidHom.id ℝ≥0ˣ).codRestrict _ fun t ↦ MonoidHom.mem_range.mpr (hms t),
      continuous_id.subtype_mk _⟩
  have hτ (t : ℝ≥0ˣ) : m (τ t) = t := hτ₀ _
  obtain ⟨ξ₀, hξ₀K, hξ₀τ, hξ₀⟩ := exists_baseCharacter_of_section m ω τ hτ
  set L : Fin N → ℝ := fun k ↦ Real.log ((m (γs k) : ℝ≥0) : ℝ)
  have hL (k : Fin N) : L k ≠ 0 :=
    (Real.log_pos (show (1 : ℝ) < ((m (γs k) : ℝ≥0) : ℝ) by exact_mod_cast hγs k)).ne'
  choose c hc using fun k ↦ Circle.exp_surjective (ξ₀ (γs k))⁻¹
  -- Characters in the fibers are determined by a frequency on the section.
  have hfreq (j : J) :
      ∃ k : Fin N, ∃ n : ℤ, ∃ s : ℝ, (∀ u : K, j.val.1 u.val = ω u) ∧
        (∀ t, j.val.1 (τ t) = Circle.exp (s * Real.log ((t : ℝ≥0) : ℝ))) ∧
        s * L k = c k + n * (2 * Real.pi) := by
    have hpos := (mem_modulatedPeriodicSpectrum_iff m ω γs j.val.1).mpr
      (lt_of_le_of_lt (Nat.zero_le _) j.2)
    obtain ⟨k, hk⟩ := mem_iUnion.mp hpos
    obtain ⟨hγ, hK⟩ := (mem_modulatedCyclicAnnihilatorFiber_iff m ω (γs k) _).mp hk
    obtain ⟨s, hs, -⟩ := existsUnique_positiveRealCharacter_freq (j.val.1.comp τ)
    have h1 : Circle.exp (s * L k) = Circle.exp (c k) := by
      show Circle.exp (s * Real.log ((m (γs k) : ℝ≥0) : ℝ)) = _
      rw [hc, ← hs (m (γs k))]
      change j.val.1 (τ (m (γs k))) = (ξ₀ (γs k))⁻¹
      rw [eq_inv_iff_mul_eq_one, mul_comm, ← hξ₀ _ hK, hγ]
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp h1
    exact ⟨k, n, s, hK, hs, hn⟩
  choose k n s hK hs hn using hfreq
  have hcount : Injective fun j ↦ (k j, n j, j.val.2) := by
    intro i j hij
    simp only [Prod.mk.injEq] at hij
    obtain ⟨hk, hnij, h2⟩ := hij
    have hss : s i = s j := by
      have := hn i
      rw [hk, hnij, ← hn j] at this
      exact mul_right_cancel₀ (hL _) this
    apply Subtype.ext
    refine Prod.ext (PontryaginDual.ext fun g ↦ ?_) h2
    rw [hξ₀ _ (hK i), hξ₀ _ (hK j), hs, hs, hss]
  have : Countable J := hcount.countable
  -- Infinitely many characters lie in the first fiber.
  let k₀ : Fin N := ⟨0, hN⟩
  let sₙ : ℕ → ℝ := fun n ↦ (c k₀ + n * (2 * Real.pi)) / L k₀
  choose ψ hψ using fun n ↦ exists_positiveRealCharacter (sₙ n)
  let ξ : ℕ → PontryaginDual G := fun n ↦ ξ₀ * PontryaginDual.map m (ψ n)
  have hξ (n : ℕ) : ξ n ∈ modulatedCyclicAnnihilatorFiber m ω (γs k₀) := by
    rw [mem_modulatedCyclicAnnihilatorFiber_iff]
    refine ⟨?_, fun u ↦ ?_⟩
    · change ξ₀ (γs k₀) * ψ n (m (γs k₀)) = 1
      rw [hψ, show sₙ n * Real.log ((m (γs k₀) : ℝ≥0) : ℝ) = c k₀ + (n : ℤ) * (2 * Real.pi) by
        simp only [sₙ]; field_simp [hL k₀]; push_cast; ring]
      rw [show Circle.exp (c k₀ + (n : ℤ) * (2 * Real.pi)) = Circle.exp (c k₀) from
        Circle.exp_eq_exp.mpr ⟨n, rfl⟩, hc, mul_inv_cancel]
    · change ξ₀ u.val * ψ n (m u.val) = ω u
      rw [show m u.val = 1 from u.2, map_one, mul_one, hξ₀K]
  let f : ℕ → J :=
    fun n ↦ ⟨(ξ n, 0), (mem_modulatedPeriodicSpectrum_iff m ω γs (ξ n)).mp
      (mem_iUnion.mpr ⟨k₀, hξ n⟩)⟩
  have hf : Injective f := by
    intro a b hab
    have hξab : ξ a = ξ b := congrArg (fun j ↦ j.val.1) hab
    have hτξ (n : ℕ) (t : ℝ≥0ˣ) :
        ξ n (τ t) = Circle.exp (sₙ n * Real.log ((t : ℝ≥0) : ℝ)) := by
      change ξ₀ (τ t) * ψ n (m (τ t)) = _
      rw [hξ₀τ, one_mul, hτ, hψ]
    obtain ⟨_, -, huniq⟩ := existsUnique_positiveRealCharacter_freq ((ξ a).comp τ)
    have hab' : sₙ a = sₙ b :=
      (huniq _ (hτξ a)).trans (huniq _ fun t ↦ (congrArg (fun χ ↦ χ (τ t)) hξab).trans
        (hτξ b t)).symm
    simp only [sₙ] at hab'
    rw [div_left_inj₀ (hL k₀)] at hab'
    have := mul_right_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero) (add_left_cancel hab')
    exact_mod_cast this
  have : Infinite J := Infinite.of_injective f hf
  exact nonempty_equiv_of_countable

variable (hcomm : ∃ a : ℝ, 0 < a ∧ ∀ k, ∃ r : ℚ, Real.log ((m (γs k)).val : ℝ) = (r : ℝ) * a)

include hcomm in
/-- Paper: Theorem 4.6.1.5, p. 212. There is a family of vectors of the difference quotient on
which the descended log-moments take the values of the Kronecker delta. The vectors are chosen
by induction from the density of the span of the descended moments in the strong dual; the
lattice Schwartz decay of (4.6.1.15) provides the surjectivity used at each step. -/
private theorem modulatedQuotientLogMoment_bases_biorthogonal :
    ∃ ψ : J → U, (∀ j, D j (ψ j) = 1) ∧ ∀ j k, j ≠ k → D j (ψ k) = 0 := by
  sorry

include hγs in
/-- Paper: Theorem 4.1.2.6(2), p. 161, applied to Theorem 4.6.1.5, p. 212. The difference quotient
is a separable nuclear Frechet space (by `modulatedIsotypicDifferenceProduct_quotient`), and every
Schauder basis of a nuclear Frechet space is absolute. -/
private theorem modulatedQuotientLogMoment_bases_absolute (σ : ℕ ≃ J) (ψ : J → U)
    (hb : IsSchauderBasis (ψ ∘ σ) (D ∘ σ)) :
    SchauderBasis.IsAbsolute (ψ ∘ σ) (D ∘ σ) := by
  have hS₀ : ∀ g ∈ List.ofFn γs, 1 < (m g).val := by
    intro g hg
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    exact hγs k
  obtain ⟨-, hN, hF⟩ := modulatedIsotypicDifferenceProduct_quotient (m := m) (hm := hm)
    (hms := hms) (ω := ω) (List.ofFn γs) hS₀
  exact SchauderBasis.isAbsolute_of_nuclear_frechet.{_, 0} hN hF hb

include hcomm in
/-- Paper: Theorem 4.6.1.5 and Equation (4.6.1.15), p. 212. Under every enumeration of the
moment family, the biorthogonal vectors are a Schauder basis of the difference quotient with
the descended log-moments as coefficient functionals. This is the expansion step: the coordinate
series of a quotient representative converges to it because the coefficients decay faster than
any power of the lattice frequency. Absoluteness is
`modulatedQuotientLogMoment_bases_absolute`. -/
private theorem modulatedQuotientLogMoment_bases_quotient (σ : ℕ ≃ J) (ψ : J → U)
    (hbi : (∀ j, D j (ψ j) = 1) ∧ ∀ j k, j ≠ k → D j (ψ k) = 0) :
    IsSchauderBasis (ψ ∘ σ) (D ∘ σ) := by
  sorry

include hcomm in
/-- Paper: Theorem 4.6.1.5 and Equation (4.6.1.16), p. 212, via Lemma 4.1.2.4, p. 159. Once
the descended log-moments are the coefficient functionals of an absolute Schauder basis of the
difference quotient, they form an unconditional Schauder basis of the strong dual, whose
coordinates are the evaluations at the basis vectors. -/
private theorem modulatedQuotientLogMoment_bases_dual (σ : ℕ ≃ J) (ψ : J → U)
    (hb : IsSchauderBasis (ψ ∘ σ) (D ∘ σ))
    (ha : SchauderBasis.IsAbsolute (ψ ∘ σ) (D ∘ σ)) :
    let d := D ∘ σ
    let ev : ℕ → StrongDual ℂ (StrongDual ℂ U) :=
      fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) ((ψ ∘ σ) n)
    IsSchauderBasis d ev ∧ SchauderBasis.IsUnconditional d ev := by
  sorry

include hcomm in
/-- Paper: Theorem 4.6.1.5 and Equations (4.6.1.15)–(4.6.1.16), p. 212.
Every enumeration of the moment family is an unconditional basis of the
strong dual. The biorthogonal vectors are an absolute basis of the quotient.
Deviation: The actual log-periods are commensurate, as required by the
finite-phase step (4.6.1.25). -/
theorem modulatedQuotientLogMoment_bases (σ : ℕ ≃ J) :
    ∃ ψ : J → U,
      let e := ψ ∘ σ
      let d := D ∘ σ
      let ev : ℕ → StrongDual ℂ (StrongDual ℂ U) :=
        fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (e n)
      IsSchauderBasis e d ∧ SchauderBasis.IsAbsolute e d ∧
        IsSchauderBasis d ev ∧ SchauderBasis.IsUnconditional d ev := by
  obtain ⟨ψ, hbi⟩ := modulatedQuotientLogMoment_bases_biorthogonal (m := m) (hm := hm)
    (hms := hms) (ω := ω) (γs := γs) (hγs := hγs) (μ := μ) (hcomm := hcomm)
  obtain hb := modulatedQuotientLogMoment_bases_quotient (m := m) (hm := hm)
    (hms := hms) (ω := ω) (γs := γs) (hγs := hγs) (μ := μ) (hcomm := hcomm) σ ψ hbi
  have ha := modulatedQuotientLogMoment_bases_absolute (m := m) (hm := hm) (hms := hms)
    (ω := ω) (γs := γs) (hγs := hγs) (μ := μ) σ ψ hb
  exact ⟨ψ, hb, ha, modulatedQuotientLogMoment_bases_dual (m := m) (hm := hm)
    (hms := hms) (ω := ω) (γs := γs) (hγs := hγs) (μ := μ) (hcomm := hcomm) σ ψ hb ha⟩

include hχ hcomm in
/-- Paper: Theorem 4.6.1.5(1), p. 212. A continuous seminorm of the
biorthogonal vectors grows at most polynomially in each lattice frequency,
uniformly in the moment order.
Deviation: The actual log-periods are commensurate. A positive multiple
of a power of one plus the frequency norm expresses polynomial growth. -/
theorem modulatedQuotientLogMoment_biorthogonal_growth (ψ : J → U)
    (hdiag : ∀ j, D j (ψ j) = 1) (hoff : ∀ j k, j ≠ k → D j (ψ k) = 0)
    (q : Seminorm ℂ U) (hq : Continuous q) :
    ∃ d : ℕ, ∀ k : Fin N, ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℤ) (j : J), j.val.1 = freq[k, n] →
        q (ψ j) ≤ C * (1 + |(n : ℝ)|) ^ d := by sorry

/-- A logarithmic moment along a one-parameter family of characters is the Fourier
transform of a single Schwartz function on the logarithmic coordinate. -/
private theorem modulatedLogMoment_logFourier (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] [CompactSpace m.toMonoidHom.ker]
    (ν : Measure G) (hν : ν = (μ₁.prod positiveRealHaar).map
      (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ z.1.val * τ z.2))
    (χ₀ : PontryaginDual G) (b : ℝ) (hb : ∀ t : ℝ≥0ˣ, χ₀ (τ t) = Circle.exp (b * Real.log (t.val : ℝ)))
    (φ : G → ℂ) (p : PositiveRealExponentialDecay univ)
    (hp : ∀ t : ℝ≥0ˣ, p.val (Real.log (t.val : ℝ)) =
      ∫ k : m.toMonoidHom.ker, (χ₀ k.val : ℂ) * φ (k.val * τ t) ∂μ₁) (r : ℕ) :
    ∃ H : SchwartzMap ℝ ℂ, ∀ (q : ℝ) (ξ : PontryaginDual G),
      (∀ x, ξ x = χ₀ x * Circle.exp (q * period x)) →
      Integrable (fun x ↦ φ x * (ξ x : ℂ) * (period x : ℂ)^r) ν →
      (∫ x, φ x * (ξ x : ℂ) * (period x : ℂ)^r ∂ν) = H (-(q+b)/(2*Real.pi)) := by
  let s₀ := logExponentialDecayTwist univ ⟨0, mem_univ _⟩ p
  have hs₀ (x : ℝ) : s₀ x = p.val x := by
    change (logExponentialDecayTwist univ ⟨0, mem_univ _⟩ p) x = _
    simpa only [zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul] using
      logExponentialDecayTwist_apply univ ⟨0, mem_univ _⟩ p x
  let w (x : ℝ) := (x : ℂ)^r
  have hw : w.HasTemperateGrowth := by dsimp [w]; fun_prop
  let s := SchwartzMap.smulLeftCLM ℂ w s₀
  have hs (x : ℝ) : s x = (x : ℂ)^r * p.val x := by
    change (SchwartzMap.smulLeftCLM ℂ w s₀) x = _
    rw [SchwartzMap.smulLeftCLM_apply hw]
    exact congrArg ((x : ℂ)^r * ·) (hs₀ x)
  refine ⟨FourierTransform.fourier s, fun q ξ hξ hi ↦ ?_⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let split (z : K × ℝ≥0ˣ) := z.1.val * τ z.2
  have hsplit : Continuous split :=
    (continuous_subtype_val.comp continuous_fst).mul (τ.continuous.comp continuous_snd)
  let F (x : G) := φ x * (ξ x : ℂ) * (period x : ℂ)^r
  have hi' : Integrable F ((μ₁.prod positiveRealHaar).map split) := hν ▸ hi
  have hprod := hi'.comp_measurable hsplit.measurable
  have hfiber (t : ℝ≥0ˣ) : (∫ k : K, (F ∘ split) (k,t) ∂μ₁) =
      (Circle.exp ((q+b)*Real.log (t.val : ℝ)) : ℂ) * (Real.log (t.val : ℝ) : ℂ)^r *
        p.val (Real.log (t.val : ℝ)) := by
    rw [hp, ← integral_const_mul]
    apply integral_congr_ae (.of_forall fun k ↦ ?_)
    change φ (k.val * τ t) * (ξ (k.val * τ t) : ℂ) * (period (k.val * τ t) : ℂ)^r = _
    rw [hξ, map_mul χ₀, map_mul m, show m k.val = 1 from k.property, hτ t, one_mul, hb]
    rw [add_mul, Circle.exp_add]
    simp only [Circle.coe_mul]
    ring
  let ex : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have hval (x : ℝ) : ((ex x).val : ℝ) = Real.exp x := rfl
  have hex : positiveRealHaar = Measure.map ex volume := by
    unfold positiveRealHaar
    congr 1
    funext x
    apply Units.ext
    apply NNReal.eq
    exact (Real.coe_toNNReal _ (Real.exp_pos x).le).trans (hval x).symm
  change (∫ x, F x ∂ν) = _
  rw [hν, integral_map hsplit.measurable.aemeasurable hi'.aestronglyMeasurable]
  change (∫ z, (F ∘ split) z ∂μ₁.prod positiveRealHaar) = _
  rw [integral_prod_symm (F ∘ split) hprod]
  simp_rw [hfiber]
  rw [hex, ex.measurableEmbedding.integral_map, SchwartzMap.fourier_coe, Real.fourier_eq]
  apply integral_congr_ae (.of_forall fun x ↦ ?_)
  rw [hval, Real.log_exp, Real.fourierChar_apply', Circle.smul_def, smul_eq_mul, hs, Real.inner_apply]
  have hphase : 2 * Real.pi * -(x * (-(q+b) / (2*Real.pi))) = (q+b)*x := by
    field_simp
  rw [hphase, mul_assoc]

include hχ in
/-- Paper: Theorem 4.6.1.5(2), p. 212. At each fixed moment order, the
coefficients on each cyclic lattice give a Schwartz sequence.
Deviation: The sequence is extended by zero at indices where the moment
order is at least the multiplicity, consistent with (4.6.1.15). The page prints
"multiplicity at least m", which includes the indices where the order equals the
multiplicity; the moment of the test function at those indices is not covered here.
The decay estimate does not require commensurability. -/
theorem modulatedLogMoment_lattice_schwartz (f : H₀[ω]) (r : Fin N) (k : Fin N) :
    ∃ v : SchwartzBruhat (Multiplicative ℤ), ∀ n : ℤ, v (Multiplicative.ofAdd n) =
      if r.val < modulatedPeriodicMultiplicity m ω γs (freq[k, n]) then
        modulatedLogMoment (m := m) (hm := hm) (hms := hms) (ω := ω) (μ := μ) (freq[k, n]) r.val f
      else 0 := by
  classical
  obtain ⟨τ, hτ⟩ := exists_surjectiveModulation_section m hm hms
  obtain ⟨b, hb⟩ := exists_circleExp_freq ((χ ω).comp τ)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let μ₁ : Measure K := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)
  let ν := canonicalModulatedHaar m hm
  let : ν.IsHaarMeasure := (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists).1
  have hν := canonicalModulatedHaar_eq_map_prod m hm τ hτ μ₁ Measure.haarMeasure_self
  obtain ⟨A, _, _, _, hA, _⟩ := modulatedMellin_isotypicDiagram m hm hms univ
    isOpen_univ ordConnected_univ univ_nonempty τ hτ μ₁ ν hν (χ ω) b hb
  obtain ⟨H, hH⟩ := modulatedLogMoment_logFourier m τ hτ μ₁ ν hν (χ ω) b hb
    f.val.val (A f.val) (hA f.val) r.val
  let L := Real.log ((m (γs k)).val : ℝ)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hγs k)
  let q (n : ℤ) := -(t₀ k ω - 2 * Real.pi * (n : ℝ) / L)
  have hξ (n : ℤ) (x : G) : freq[k, n] x = χ ω x * Circle.exp (q n * period x) := by
    change (modulatedCyclicCharacter m (γs k) (hγs k) χ (t₀ k) (ht₀ k) (ω, n)
      (QuotientGroup.mk x))⁻¹ = _
    rw [modulatedCyclicCharacter_mk, show q n * (period x) =
      -((t₀ k ω - 2 * Real.pi * (n : ℝ) / L) * period x) from neg_mul _ _, Circle.exp_neg, mul_inv, inv_inv]
  let c := Measure.haarScalarFactor μ ν
  have hscale : μ = c • ν := Measure.isMulLeftInvariant_eq_smul μ ν
  let a : ℝ := -1 / L
  let d := (t₀ k ω - b) / (2 * Real.pi)
  have hsample (n : ℤ) : modulatedLogMoment (m := m) (hm := hm) (hms := hms)
      (ω := ω) (μ := μ) (freq[k, n]) r.val f = (((c : ℝ) : ℂ) • H) (a*n+d) := by
    change (∫ x, f.val.val x * (freq[k, n] x : ℂ) * (period x : ℂ)^r.val ∂μ) = _
    rw [hscale, integral_smul_nnreal_measure, hH (q n) (freq[k, n]) (hξ n)
      (integrable_logMoment m ω ν (freq[k, n]) r.val f)]
    have heq : -(q n + b)/(2*Real.pi) = a*n+d := by
      dsimp [q, a, d]
      field_simp
      ring
    rw [heq]
    rfl
  let mask (n : ℤ) := r.val < modulatedPeriodicMultiplicity m ω γs (freq[k, n])
  obtain ⟨v, hv⟩ := schwartzBruhat_of_affine_integer_samples (((c : ℝ) : ℂ) • H) a d
    (div_ne_zero (by norm_num) hL.ne') mask
  exact ⟨v, fun n ↦ (hv n).trans (by simp only [mask, hsample])⟩

end Moments

section RepeatedGenerator

variable (a : ℝ≥0ˣ) (ha : 1 < a.val)

local notation "A" => SchwartzBergman (univ : Set ℝ)
local notation "mPos" => ContinuousMonoidHom.id ℝ≥0ˣ
local notation "Mellin" => positiveRealFourierMellin univ isOpen_univ ordConnected_univ univ_nonempty
local notation "factor[" z "]" => (1 - Complex.exp (-((Real.log (a.val : ℝ) : ℂ) * z)))

include ha in
private theorem cyclicMellin_model (hmId : IsModulation mPos) (hsId : Surjective mPos) :
    letI : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
    let Δ := modulatedCyclicDifference mPos a hmId hsId univ ordConnected_univ univ_nonempty
    ∃ (e : PositiveRealExponentialDecay univ ≃L[ℂ] ModulatedExponentialDecay mPos univ)
      (T : A →L[ℂ] A), (∀ f t, (e f).val t = f.val (Real.log (t.val : ℝ))) ∧
      (∀ f z, (T f).val z = factor[z] * f.val z) ∧
      (∀ f, Mellin (e.symm (Δ f)) = T (Mellin (e.symm f))) ∧ IsClosedEmbedding T := by
  intro Δ
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let e := (identityModulationExponentialDecay_equiv univ ordConnected_univ univ_nonempty).choose
  have he := (identityModulationExponentialDecay_equiv univ ordConnected_univ univ_nonempty).choose_spec
  let U := e.symm.trans Mellin
  let T : A →L[ℂ] A := U.toContinuousLinearMap.comp (Δ.comp U.symm.toContinuousLinearMap)
  have hT (f : ModulatedExponentialDecay mPos univ) : U (Δ f) = T (U f) := by
    change U (Δ f) = U (Δ (U.symm (U f)))
    exact congrArg (fun v ↦ U (Δ v)) (U.symm_apply_apply f).symm
  have hmul (H : A) (z : ℂ) : (T H).val z = factor[z] * H.val z := by
    let f := U.symm H
    let p := e.symm f
    let p' := p - e.symm (Δ f)
    have hs (x : ℝ) : p'.val x = p.val (Real.log (a.val : ℝ) + x) := by
      let t : ℝ≥0ˣ := Units.mk0 ⟨Real.exp x, (Real.exp_pos x).le⟩ (by
        exact ne_of_gt (show 0 < (⟨Real.exp x, (Real.exp_pos x).le⟩ : ℝ≥0) from Real.exp_pos x))
      have ht : Real.log (t.val : ℝ) = x := Real.log_exp x
      have hlog : Real.log ((a * t).val : ℝ) = Real.log (a.val : ℝ) + x := by
        rw [Units.val_mul, NNReal.coe_mul, Real.log_mul (NNReal.coe_pos.mpr (Units.zero_lt a)).ne'
          (NNReal.coe_pos.mpr (Units.zero_lt t)).ne', ht]
      have hh (v : ModulatedExponentialDecay mPos univ) (u : ℝ≥0ˣ) :
          (e.symm v).val (Real.log (u.val : ℝ)) = v.val u :=
        (he _ u).symm.trans (congrArg (fun y : ModulatedExponentialDecay mPos univ ↦ y.val u)
          (e.apply_symm_apply v))
      change p.val x - (e.symm (Δ f)).val x = _
      calc
        _ = f.val t - (Δ f).val t :=
          congrArg₂ (· - ·)
            ((congrArg p.val ht.symm).trans (hh f t))
            ((congrArg (e.symm (Δ f)).val ht.symm).trans (hh (Δ f) t))
        _ = f.val (a * t) :=
          (congrArg (f.val t - ·) (modulatedCyclicDifference_apply mPos a hmId hsId univ
            ordConnected_univ univ_nonempty f t)).trans (sub_sub_cancel _ _)
        _ = _ := (hh f (a * t)).symm.trans (congrArg p.val hlog)
    let : MeasurableSpace ℝ≥0ˣ := borel _
    have : BorelSpace ℝ≥0ˣ := ⟨rfl⟩
    have hshift := modulatedMellin_profile_translate mPos a univ isOpen_univ ordConnected_univ
      univ_nonempty mPos (1 : PontryaginDual ℝ≥0ˣ) p p'
      (fun x ↦ (hs x).trans (one_mul _).symm) z (mem_univ _)
    have ha' : 0 < (a.val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    have hpow : ((a.val : ℝ) : ℂ) ^ (-z) = Complex.exp (-((Real.log (a.val : ℝ) : ℂ) * z)) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha'.ne'),
        ← Complex.ofReal_log ha'.le, mul_neg]
    have hz := congrArg (fun F : A ↦ F.val z) ((Mellin).map_sub p (e.symm (Δ f)))
    have hH : Mellin p = H := U.apply_symm_apply H
    have heval := congrArg (fun F : A ↦ F.val z) hH
    have hcalc {u v w s : ℂ} (h₁ : u = v - w) (h₂ : u = s * v) :
        w = (1 - s) * v := by linear_combination h₁ - h₂
    exact (hcalc hz (hshift.trans (congrArg (· * (Mellin p).val z)
      ((one_mul _).trans hpow)))).trans (congrArg (factor[z] * ·) heval)
  have hcl : IsClosedEmbedding T := by
    have hc := modulatedCyclicDifference_isClosed_range mPos a hmId hsId ha
    have hi := cyclicDifference_injective mPos hmId hsId a ha
    apply frechet_closedEmbedding_of_injective (schwartzBergman_frechet univ isOpen_univ
      ordConnected_univ univ_nonempty)
    · exact U.injective.comp (hi.comp U.symm.injective)
    · change IsClosed (range (U ∘ Δ ∘ U.symm))
      rw [← Function.comp_assoc, U.symm.surjective.range_comp, range_comp]
      exact U.toHomeomorph.isClosedMap _ hc

  exact ⟨e, T, he, hmul, hT, hcl⟩

include ha in
/-- Paper: Example 4.6.1.6, p. 217. In logarithmic coordinates Mellin
transform carries the cyclic difference to multiplication by the given
entire factor. Its square has closed range and represents the repeated difference. -/
theorem repeatedCyclicDifference_mellin (hmId : IsModulation mPos) (hsId : Surjective mPos) :
    letI : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
    let EPos := ModulatedExponentialDecay mPos (univ : Set ℝ)
    let Δ := modulatedDifferenceProduct mPos hmId hsId univ ordConnected_univ univ_nonempty [a]
    let Δ₂ := modulatedDifferenceProduct mPos hmId hsId univ ordConnected_univ univ_nonempty [a, a]
    ∃ (e : PositiveRealExponentialDecay univ ≃L[ℂ] EPos) (T : A →L[ℂ] A),
      (∀ f t, (e f).val t = f.val (Real.log (t.val : ℝ))) ∧
      (∀ f z, (T f).val z = factor[z] * f.val z) ∧
      (∀ f, Mellin (e.symm (Δ f)) = T (Mellin (e.symm f))) ∧
      (∀ f, Mellin (e.symm (Δ₂ f)) = T (T (Mellin (e.symm f)))) ∧
      IsClosed (range (T.comp T)) := by
  intro EPos Δ Δ₂
  have model := cyclicMellin_model a ha hmId hsId
  let e := model.choose
  let T := model.choose_spec.choose
  have h := model.choose_spec.choose_spec
  have ht := h.2.2.1
  refine ⟨e, T, h.1, h.2.1, ?_, ?_, (h.2.2.2.comp h.2.2.2).isClosed_range⟩
  · exact ht
  · intro f
    exact (ht _).trans (congrArg T (ht f))

variable (T : SchwartzBergman univ →L[ℂ] SchwartzBergman univ)
variable (hT : ∀ f z, (T f).val z =
  (1 - Complex.exp (-((Real.log (a.val : ℝ) : ℂ) * z))) * f.val z)

local notation "R₁" => T.range
local notation "R₂" => (T.comp T).range
local notation "N₂" => (R₂).comap (R₁).subtype

include ha hT in
private theorem cyclicMellinMultiplier_isClosedEmbedding : IsClosedEmbedding T := by
  have model := cyclicMellin_model a ha ⟨isProperMap_id, exists_ne 1⟩ surjective_id
  let T' := model.choose_spec.choose
  have h := model.choose_spec.choose_spec
  have he : T' = T := ContinuousLinearMap.ext fun f ↦
    Subtype.ext (funext fun z ↦ (h.2.1 f z).trans (hT f z).symm)
  exact he ▸ h.2.2.2

include ha hT in
/-- Paper: Example 4.6.1.6 and Equation (4.6.1.29), p. 217.
The first and second multiplier images give a short exact sequence.
Its left inclusion is a closed topological embedding. -/
theorem repeatedCyclicDifference_mellin_exact :
    ∃ (i : ((R₁) ⧸ N₂) →L[ℂ] (A ⧸ R₂)) (q : (A ⧸ R₂) →L[ℂ] (A ⧸ R₁)),
      (∀ f : R₁, i ((N₂).mkQ f) = (R₂).mkQ f.val) ∧
      (∀ f : A, q ((R₂).mkQ f) = (R₁).mkQ f) ∧
      IsClosedEmbedding i ∧ Function.Exact i q ∧ Surjective q := by
  exact Submodule.exists_exact_quotient_maps R₂ R₁
    (fun _ ⟨f, hf⟩ ↦ ⟨T f, hf⟩) (cyclicMellinMultiplier_isClosedEmbedding a ha T hT).isClosed_range

include ha hT in
/-- Paper: Example 4.6.1.6 and Equation (4.6.1.30), p. 218.
Division by the entire factor identifies the image quotient with the
quotient by the single factor. The rule is specified on products so it
applies also at the zeros of the factor. -/
theorem repeatedCyclicDifference_mellin_division :
    ∃ F : ((R₁) ⧸ N₂) ≃L[ℂ] (A ⧸ R₁),
      ∀ f : A, F ((N₂).mkQ (T.rangeRestrict f)) = (R₁).mkQ f := by
  have he := cyclicMellinMultiplier_isClosedEmbedding a ha T hT
  have hi := he.injective
  obtain ⟨F, hF⟩ := T.exists_quotient_range_equiv he.isEmbedding R₁ N₂
    (fun x ↦ ⟨fun ⟨y, hy⟩ ↦ ⟨y, hi hy⟩, fun ⟨y, hy⟩ ↦ ⟨y, congrArg T hy⟩⟩)
  exact ⟨F.symm, fun x ↦ F.symm_apply_eq.mpr (hF x).symm⟩

include ha hT in
/-- Paper: Example 4.6.1.6, p. 218. Evaluation of the analytic quotient at
a lattice zero equals the derivative of the numerator divided by the
logarithm of the generator. -/
theorem repeatedCyclicDifference_mellin_division_eval (f : A) (n : ℤ) :
    let z : ℂ := ((2 * Real.pi * (n : ℝ) / Real.log (a.val : ℝ) : ℝ) : ℂ) * Complex.I
    f.val z = deriv (T f).val z / (Real.log (a.val : ℝ) : ℂ) := by
  intro z
  let L : ℝ := Real.log (a.val : ℝ)
  have hL : L ≠ 0 := (Real.log_pos (by exact_mod_cast ha)).ne'
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hz : -((L : ℂ) * z) = ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    dsimp [z, L] at *
    push_cast
    field_simp
    <;> ring
  have hexp : Complex.exp (-((L : ℂ) * z)) = 1 :=
    hz ▸ Complex.exp_int_mul_two_pi_mul_I (-n)
  have hlin : HasDerivAt (fun w : ℂ ↦ -((L : ℂ) * w)) (-(L : ℂ)) z :=
    ((hasDerivAt_id z).const_mul (L : ℂ)).neg.congr_deriv (by simp)
  have hfactor : HasDerivAt (fun w : ℂ ↦ 1 - Complex.exp (-((L : ℂ) * w))) (L : ℂ) z := by
    simpa only [hexp, one_mul, neg_neg, zero_sub] using!
      (hasDerivAt_const z (1 : ℂ)).sub hlin.cexp
  have hf : Differentiable ℂ f.val := by
    apply differentiableOn_univ.mp
    simpa using f.property.2.1
  have hderiv : HasDerivAt (T f).val ((L : ℂ) * f.val z) z := by
    rw [show (T f).val = _ from funext (hT f)]
    simpa only [hexp, sub_self, zero_mul, add_zero] using!
      hfactor.mul (hf z).hasDerivAt
  rw [hderiv.deriv, mul_div_cancel_left₀ _ hLc]

include ha hT in
/-- Paper: Example 4.6.1.6, p. 218. The normalized Fourier coefficient of
the periodized profile is a first derivative of the repeated-generator numerator.
Deviation: The coefficient in (4.2.1.4) contributes another inverse log-period
and uses the negative Mellin frequency. -/
theorem repeatedCyclicDifference_mellin_division_fourierCoeff
    (f : PositiveRealExponentialDecay univ) (n : ℤ) :
    let L := Real.log (a.val : ℝ)
    let z := (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) / (L : ℂ)
    cyclicFourierCoeff n (cyclicPeriodizationCLM (a.val : ℝ) (by exact_mod_cast ha) f) =
      deriv (T (Mellin f)).val (-z) / (L : ℂ) ^ 2 := by
  dsimp only
  have hreal : 1 < (a.val : ℝ) := by exact_mod_cast ha
  have hL : (Real.log (a.val : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hreal).ne'
  have hc := cyclicQuotientMellinCoeff_mk (a.val : ℝ) hreal n f
  change (Real.log (a.val : ℝ) : ℂ) * cyclicFourierCoeff n
    (cyclicPeriodizationCLM (a.val : ℝ) hreal f) = _ at hc
  rw [← positiveRealFourierMellin_apply univ isOpen_univ ordConnected_univ univ_nonempty
    f _ (mem_univ _)] at hc
  have hd := repeatedCyclicDifference_mellin_division_eval a ha T hT (Mellin f) (-n)
  dsimp only at hd
  have hz : ((2 * Real.pi * ((-n : ℤ) : ℝ) / Real.log (a.val : ℝ) : ℝ) : ℂ) * Complex.I =
      -(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / (Real.log (a.val : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [hz] at hd
  rw [hd] at hc
  field_simp [hL] at hc ⊢
  linear_combination hc

end RepeatedGenerator

/-! ## 4.6.2 Support conditions in the presence of multiplicity -/

variable (S : List G) (hS : S ≠ []) (hγS : ∀ g ∈ S, 1 < (m g).val)

-- TODO(paper-gap): On p. 219 the window needs 2 log b′₁ > log |γ₁|. The
-- support enlargement uses γ₁⁻¹, and the final shift must have module below one.

include hS hγS in
/-- Paper: Theorem 4.6.2.1, p. 218. Each isotype has a compact norm-one-stable
support set of module below one. The supported functions surject onto the
difference quotient, and the quotient by the kernel is identified by inclusion.
Deviation: A stable compact support is represented by the preimage of its
compact module window. Its isotype has the inherited topology. -/
theorem modulatedDifferenceProduct_compactSupport_quotient :
    ∃ B : Set ℝ≥0ˣ, IsCompact B ∧ (∀ t ∈ B, t.val < 1) ∧
      let W := (modulatedCompactSupportSubmodule m B).comap (H₀[ω]).subtype
      let R := (P[ω, S]).range
      let M := R.comap W.subtype
      Surjective (R.mkQ ∘ W.subtype) ∧
      ∃ F : (W ⧸ M) ≃L[ℂ] (H₀[ω] ⧸ R),
        ∀ f : W, F (M.mkQ f) = R.mkQ f.val := by sorry

/-! ## 4.6.3 The case of an interval containing zero -/

/-- Paper: Corollary 4.6.3.1, p. 219. On ordinary Schwartz–Bruhat functions
the difference product composes the cyclic differences, retaining repetitions. -/
def schwartzBruhatDifferenceProduct (S : List G) : SchwartzBruhat G →L[ℂ] SchwartzBruhat G :=
  (S.map schwartzBruhatCyclicDifference).prod

/-- Paper: Corollary 4.6.3.1, p. 219. For a repeated generator the ordinary
Schwartz–Bruhat difference product is the second finite difference. -/
theorem schwartzBruhatDifferenceProduct_pair_apply (f : SchwartzBruhat G) (x : G) :
    schwartzBruhatDifferenceProduct [γ, γ] f x =
      f x - 2 * f (γ * x) + f (γ ^ 2 * x) := by
  -- `schwartzBruhatCyclicDifference_apply` was stated with a Borel structure in scope; its
  -- conclusion does not depend on it, so any Borel structure will do.
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  have h : schwartzBruhatDifferenceProduct [γ, γ] f =
      schwartzBruhatCyclicDifference γ (schwartzBruhatCyclicDifference γ f) := by
    simp only [schwartzBruhatDifferenceProduct, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_apply_eq_comp]
  have h0 := congrArg (fun g : SchwartzBruhat G ↦ g x) h
  have h1 := schwartzBruhatCyclicDifference_apply γ (schwartzBruhatCyclicDifference γ f) x
  have h2 := schwartzBruhatCyclicDifference_apply γ f x
  have h3 := schwartzBruhatCyclicDifference_apply γ f (γ * x)
  have h4 : f (γ ^ 2 * x) = f (γ * (γ * x)) := congrArg f (by rw [sq, mul_assoc])
  -- No `rw` on the main goal: its closing `rfl` check, like rewriting with `h2`, makes Lean
  -- unfold the translation action defining the cyclic difference, which times out.
  linear_combination h0 + h1 + h2 - h3 - h4

/-- A Schwartz–Bruhat function lies in the norm-one isotype exactly when translating its
argument by a norm-one element multiplies its values by the character. -/
private theorem mem_actionIsotype_translation_iff (φ : SchwartzBruhat G) :
    φ ∈ actionIsotype ρK ω ↔ ∀ (u : K) (x : G), φ (u.val⁻¹ * x) = (ω u : ℂ) * φ x := by
  refine (mem_actionIsotype ρK ω φ).trans (forall_congr' fun u ↦ ⟨fun h x ↦ ?_, fun h ↦ ?_⟩)
  · have hx := congrArg (fun g : SchwartzBruhat G ↦ g x) h
    change schwartzBruhatTranslationAction (G := G) u.val φ x = (ω u : ℂ) * φ x at hx
    exact (schwartzBruhatTranslationAction_apply u.val x φ).symm.trans hx
  · refine Subtype.ext (funext fun x ↦ ?_)
    change schwartzBruhatTranslationAction (G := G) u.val φ x = (ω u : ℂ) * φ x
    exact (schwartzBruhatTranslationAction_apply u.val x φ).trans (h x)

/-- The ordinary cyclic difference at a point subtracts the value at the translate
by the generator. -/
private theorem schwartzBruhatCyclicDifference_eval (g : G) (f : SchwartzBruhat G) (x : G) :
    schwartzBruhatCyclicDifference g f x = f x - f (g * x) :=
  congrArg (f x - ·) ((schwartzBruhatTranslationAction_apply g⁻¹ x f).trans
    (congrArg (fun y ↦ f (y * x)) (inv_inv g)))

/-- Paper: Corollary 4.6.3.1, pp. 219–220. The ordinary Schwartz–Bruhat
difference product preserves the norm-one isotype. -/
theorem schwartzBruhatDifferenceProduct_mem_isotype :
    ∀ f ∈ actionIsotype ρK ω, schwartzBruhatDifferenceProduct S f ∈ actionIsotype ρK ω :=
  by
  induction S with
  | nil => exact fun f hf ↦ hf
  | cons g S ih =>
    intro f hf
    have hP := (mem_actionIsotype_translation_iff m ω _).mp (ih f hf)
    refine (mem_actionIsotype_translation_iff m ω
      (schwartzBruhatDifferenceProduct (g :: S) f)).mpr fun u x ↦ ?_
    have h1 := schwartzBruhatCyclicDifference_eval g (schwartzBruhatDifferenceProduct S f)
      (u.val⁻¹ * x)
    have h2 := schwartzBruhatCyclicDifference_eval g (schwartzBruhatDifferenceProduct S f) x
    have hcomm : g * (u.val⁻¹ * x) = u.val⁻¹ * (g * x) := mul_left_comm _ _ _
    exact h1.trans ((congrArg₂ (· - ·) (hP u x)
      ((congrArg (fun y ↦ schwartzBruhatDifferenceProduct S f y) hcomm).trans
        (hP u (g * x)))).trans
      ((mul_sub _ _ _).symm.trans (congrArg ((ω u : ℂ) * ·) h2.symm)))

section
set_option linter.unusedSectionVars false

private theorem compare_single_quotients {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (i : X →L[ℂ] Y) (A : X →L[ℂ] X)
    (B : Y →L[ℂ] Y) (F : (X ⧸ A.range) ≃L[ℂ] (Y ⧸ B.range))
    (hF : ∀ x, F (A.range.mkQ x) = B.range.mkQ (i x)) :
    (∀ x, i x ∈ B.range → x ∈ A.range) ∧ ∀ y, ∃ x v, y = i x + B v := by
  constructor
  · intro x hx
    apply (Submodule.Quotient.mk_eq_zero _).mp
    apply F.injective
    exact (hF x).trans (((Submodule.Quotient.mk_eq_zero _).mpr hx).trans F.map_zero.symm)
  · intro y
    obtain ⟨x, hx⟩ := A.range.mkQ_surjective (F.symm (B.range.mkQ y))
    have he := (hF x).symm.trans ((congrArg F hx).trans (F.apply_symm_apply _))
    obtain ⟨v, hv⟩ := (Submodule.Quotient.eq _).mp he.symm
    exact ⟨x, v, (show y = i x + (y - i x) by abel).trans (congrArg (i x + ·) hv.symm)⟩

private theorem compare_product_ranges {L X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (i : X →L[ℂ] Y) (A : L → X →L[ℂ] X) (B : L → Y →L[ℂ] Y) (s : List L)
    (hc : ∀ g ∈ s, ∀ x, i (A g x) = B g (i x))
    (hi : ∀ g ∈ s, Injective (B g))
    (h1 : ∀ g ∈ s, (∀ x, i x ∈ (B g).range → x ∈ (A g).range) ∧
      ∀ y, ∃ x v, y = i x + B g v) :
    (∀ x, i x ∈ (s.map B).prod.range ↔ x ∈ (s.map A).prod.range) ∧
      ∀ y, ∃ x v, y = i x + (s.map B).prod v := by
  induction s with
  | nil =>
    exact ⟨fun x ↦ ⟨fun _ ↦ ⟨x, rfl⟩, fun _ ↦ ⟨i x, rfl⟩⟩,
      fun y ↦ ⟨0, y, by simp⟩⟩
  | cons g l ih =>
    obtain ⟨hp, hs⟩ := ih (fun a ha ↦ hc a (.tail _ ha)) (fun a ha ↦ hi a (.tail _ ha))
      (fun a ha ↦ h1 a (.tail _ ha))
    have hg := h1 g (.head _)
    have comm := hc g (.head _)
    refine ⟨fun x ↦ ⟨?_, ?_⟩, ?_⟩
    · rintro ⟨z, hz⟩
      obtain ⟨u, hu⟩ := hg.1 x ⟨(l.map B).prod z, hz⟩
      have hz' := (hi g (.head _) (hz.trans ((congrArg i hu).symm.trans (comm u))))
      obtain ⟨v, hv⟩ := (hp u).mp ⟨z, hz'⟩
      exact ⟨v, (congrArg (A g) hv).trans hu⟩
    · rintro ⟨v, hv⟩
      obtain ⟨z, hz⟩ := (hp ((l.map A).prod v)).mpr ⟨v, rfl⟩
      exact ⟨z, (congrArg (B g) hz).trans ((comm _).symm.trans (congrArg i hv))⟩
    · intro y
      obtain ⟨u, w, hu⟩ := hg.2 y
      obtain ⟨v, z, hv⟩ := hs w
      refine ⟨u + A g v, z, ?_⟩
      calc
        y = i u + B g (i v + (l.map B).prod z) := hu.trans (congrArg (fun w ↦ i u + B g w) hv)
        _ = i (u + A g v) + B g ((l.map B).prod z) := by rw [map_add, i.map_add, comm, add_assoc]

private theorem lf_open_surjection {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℂ X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (hX : IsLFSpace X) (hY : IsLFSpace Y) (q : X →L[ℂ] Y) (hq : Surjective q) : IsOpenMap q := by
  obtain ⟨hT, V, _, _, _, hV, j, i, h⟩ := hX
  refine isOpenMap_of_surjective_toLF hY hV i ?_ h.exhaustive q hq
  rintro n _ ⟨v, rfl⟩
  exact ⟨j n v, DFunLike.congr_fun (h.compatible n) v⟩

private theorem lf_compare_quotients {X Y Z : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℂ X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℂ Y] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    [IsTopologicalAddGroup Z] [ContinuousSMul ℂ Z]
    (hX : IsLFSpace X) (hZ : IsLFSpace Z) (e : Z ≃L[ℂ] Y) (i : X →L[ℂ] Y)
    (N : Submodule ℂ X) (M : Submodule ℂ Y) (hclosed : IsClosed (M : Set Y))
    (hker : ∀ x, i x ∈ M ↔ x ∈ N) (hs : ∀ y, ∃ x, y - i x ∈ M) :
    ∃ F : (X ⧸ N) ≃L[ℂ] (Y ⧸ M), ∀ x, F (N.mkQ x) = M.mkQ (i x) := by
  let M' := M.comap e.toLinearMap
  have hM : M'.map e.toLinearMap = M := Submodule.map_comap_eq_of_surjective e.surjective M
  let eQ := e.quotientMapEquiv M' M hM
  have hZ' := (lfSpace_quotient_properties («E» := Z)).2 hZ M' (hclosed.preimage e.continuous)
  let q := M.mkQL.comp i
  have hq : Surjective q := by
    intro w
    obtain ⟨y, rfl⟩ := M.mkQ_surjective w
    obtain ⟨x, hx⟩ := hs y
    exact ⟨x, ((Submodule.Quotient.eq M).mpr hx).symm⟩
  have ho := lf_open_surjection hX hZ' (eQ.symm.toContinuousLinearMap.comp q) (eQ.symm.surjective.comp hq)
  have hqo : IsOpenMap q := by
    have h := eQ.toHomeomorph.isOpenMap.comp ho
    exact (congrArg IsOpenMap (funext (fun x ↦ eQ.apply_symm_apply (q x)) :
      eQ.toHomeomorph ∘ (eQ.symm.toContinuousLinearMap.comp q) = q)).mp h
  let f := N.liftQL q fun x hx ↦ (Submodule.Quotient.mk_eq_zero M).mpr ((hker x).mpr hx)
  have hf (x : X) : f (N.mkQ x) = q x := rfl
  have hf' : Bijective f := by
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply le_antisymm _ bot_le
      intro z hz
      obtain ⟨x, rfl⟩ := N.mkQ_surjective z
      exact (Submodule.Quotient.mk_eq_zero N).mpr ((hker x).mp ((Submodule.Quotient.mk_eq_zero M).mp hz))
    · intro z
      obtain ⟨x, hx⟩ := hq z
      exact ⟨N.mkQ x, (hf x).trans hx⟩
  let F := LinearEquiv.ofBijective f.toLinearMap hf'
  have hcont : Continuous F.symm := (IsOpenQuotientMap.isQuotientMap (show IsOpenQuotientMap q from ⟨hq, q.continuous, hqo⟩)).continuous_iff.mpr
    (N.mkQL.continuous.congr (fun x ↦ (F.symm_apply_eq.mpr (hf x).symm).symm))
  exact ⟨{ __ := F, continuous_toFun := f.continuous, continuous_invFun := hcont }, hf⟩

private theorem compare_factor_on_representatives {L X Y Z : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (ex : X → L → ℂ) (ey : Y → L → ℂ) (hy : Injective ey) (i : X →L[ℂ] Y) (j : Y →L[ℂ] Z)
    (j₀ : Y → Z) (hj : ∀ y, j y = j₀ y)
    (hi : ∀ x t, ey (i x) t = ex x t) (A : X →L[ℂ] X) (B : Y →L[ℂ] Y) (C : Z →L[ℂ] Z)
    (h : ∃ (i' : X →L[ℂ] Y) (F : (X ⧸ A.range) ≃L[ℂ] (Y ⧸ B.range))
      (J : (Y ⧸ B.range) ≃L[ℂ] (Z ⧸ C.range)),
      (∀ x t, ey (i' x) t = ex x t) ∧ (∀ x, F (A.range.mkQ x) = B.range.mkQ (i' x)) ∧
        ∀ y, J (B.range.mkQ y) = C.range.mkQ (j₀ y)) :
    ((∀ x, i x ∈ B.range → x ∈ A.range) ∧ ∀ y, ∃ x v, y = i x + B v) ∧
      (∀ y, j y ∈ C.range → y ∈ B.range) ∧ ∀ z, ∃ y v, z = j y + C v := by
  obtain ⟨i', F, J, hi', hF, hJ⟩ := h
  have h' : i' = i := ContinuousLinearMap.ext fun x ↦ hy (funext fun t ↦ (hi' x t).trans (hi x t).symm)
  subst i'
  exact ⟨compare_single_quotients i A B F hF, compare_single_quotients j B C J (fun y ↦ (hJ y).trans (congrArg C.range.mkQ (hj y).symm))⟩

private theorem commute_difference_of_evaluation {L X Y : Type*} [Mul L] [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (ex : X → L → ℂ) (ey : Y → L → ℂ) (hy : Injective ey) (i : X →L[ℂ] Y)
    (hi : ∀ x t, ey (i x) t = ex x t) (A : L → X →L[ℂ] X) (B : L → Y →L[ℂ] Y)
    (ha : ∀ g f t, ex (A g f) t = ex f t - ex f (g * t))
    (hb : ∀ g f t, ey (B g f) t = ey f t - ey f (g * t)) (g : L) (f : X) :
    i (A g f) = B g (i f) :=
  hy (funext fun t ↦ (hi _ t).trans ((ha _ _ _).trans
    ((congrArg₂ (· - ·) (hi f t).symm (hi f (g * t)).symm).trans (hb _ _ _).symm)))

private theorem comparison_equiv_of_product {L X Y Z : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℂ Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z] [ContinuousSMul ℂ Z]
    (hX : IsLFSpace X) (hZ : IsLFSpace Z) (e : Z ≃L[ℂ] Y)
    (i : X →L[ℂ] Y) (A : L → X →L[ℂ] X) (B : L → Y →L[ℂ] Y) (s : List L)
    (hc : ∀ g ∈ s, ∀ x, i (A g x) = B g (i x))
    (hi : ∀ g ∈ s, Injective (B g))
    (h1 : ∀ g ∈ s, (∀ x, i x ∈ (B g).range → x ∈ (A g).range) ∧ ∀ y, ∃ x v, y = i x + B g v)
    (hclosed : IsClosed ((s.map B).prod.range : Set Y)) :
    let N := (s.map A).prod.range
    let M := (s.map B).prod.range
    IsClosed (N : Set X) ∧ ∃ F : (X ⧸ N) ≃L[ℂ] (Y ⧸ M), ∀ x, F (N.mkQ x) = M.mkQ (i x) := by
  intro N M
  obtain ⟨hker, hs⟩ := compare_product_ranges i A B s hc hi h1
  have heq : (N : Set X) = i ⁻¹' M := Set.ext fun x ↦ (hker x).symm
  refine ⟨(congrArg IsClosed heq).mpr (hclosed.preimage i.continuous), ?_⟩
  apply lf_compare_quotients hX hZ e i N M hclosed hker
  intro y
  obtain ⟨x, v, hv⟩ := hs y
  exact ⟨x, v, by rw [hv]; abel⟩

private theorem retract_quotient_maps {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (H : Submodule ℂ X) (D P : X →L[ℂ] X)
    (hp : ∀ x, P x ∈ H) (hfix : ∀ x ∈ H, P x = x) (hc : ∀ x, P (D x) = D (P x)) :
    let N := (H.map D.toLinearMap).comap H.subtype
    ∃ (a : (H ⧸ N) →L[ℂ] (X ⧸ D.range)) (b : (X ⧸ D.range) →L[ℂ] (H ⧸ N)),
      LeftInverse b a ∧ (∀ x : H, a (N.mkQ x) = D.range.mkQ x.val) ∧
      ∀ x, b (D.range.mkQ x) = N.mkQ ⟨P x, hp x⟩ := by
  intro N
  let a := N.liftQL (D.range.mkQL.comp H.subtypeL) (by
    rintro x ⟨y, hy, he⟩
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, he⟩)
  let r := P.codRestrict H hp
  let b := D.range.liftQL (N.mkQL.comp r) (by
    rintro x ⟨y, hy⟩
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      ⟨P y, hp y, (hc y).symm.trans (congrArg P hy)⟩)
  refine ⟨a, b, ?_, fun _ ↦ rfl, fun _ ↦ rfl⟩
  intro z
  obtain ⟨x, rfl⟩ := N.mkQ_surjective z
  exact congrArg N.mkQ (Subtype.ext (hfix x.val x.property))

private theorem quotient_equiv_on_retracts {X Y U V : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup U] [Module ℂ U] [TopologicalSpace U] [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (F : X ≃L[ℂ] Y) (a : U →L[ℂ] X) (b : X →L[ℂ] U) (c : V →L[ℂ] Y) (d : Y →L[ℂ] V)
    (hba : LeftInverse b a) (hdc : LeftInverse d c) (h : F '' range a = range c) :
    ∃ J : U ≃L[ℂ] V, ∀ x, c (J x) = F (a x) := by
  let j := (d.comp F.toContinuousLinearMap).comp a
  let k := (b.comp F.symm.toContinuousLinearMap).comp c
  have hj (x : U) : c (j x) = F (a x) := by
    obtain ⟨y, hy⟩ := h ▸ (mem_image_of_mem F (mem_range_self x) : F (a x) ∈ F '' range a)
    exact (congrArg (fun v ↦ c (d v)) hy.symm).trans ((congrArg c (hdc y)).trans hy)
  have hk (y : V) : a (k y) = F.symm (c y) := by
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := h.symm ▸ (mem_range_self y : c y ∈ range c)
    have hv := F.symm_apply_eq.mpr hx.symm
    exact (congrArg (fun v ↦ a (b v)) hv).trans ((congrArg a (hba x)).trans hv.symm)
  refine ⟨{ __ := j.toLinearMap
            invFun := k
            continuous_toFun := j.continuous
            continuous_invFun := k.continuous
            left_inv := ?_
            right_inv := ?_ }, hj⟩
  · intro x
    exact hba.injective ((hk (j x)).trans ((congrArg F.symm (hj x)).trans (F.symm_apply_apply _)))
  · intro y
    exact hdc.injective ((hj (k y)).trans ((congrArg F (hk y)).trans (F.apply_symm_apply _)))

private theorem compared_isotype_images {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (D : X →L[ℂ] X) (B : Y →L[ℂ] Y) (H : Submodule ℂ X) (S : Submodule ℂ Y) (i : X →L[ℂ] Y)
    (F : (X ⧸ D.range) ≃L[ℂ] (Y ⧸ B.range)) (hF : ∀ x, F (D.range.mkQ x) = B.range.mkQ (i x))
    (P : X →L[ℂ] X) (Q : Y →L[ℂ] Y) (hp : ∀ x, P x ∈ H) (hS : ∀ y ∈ S, Q y = y)
    (hiH : ∀ x ∈ H, i x ∈ S) (hq : ∀ y, Q (B y) = B (Q y)) (hcomm : ∀ x, i (P x) = Q (i x)) :
    F '' (D.range.mkQ '' (H : Set X)) = B.range.mkQ '' (S : Set Y) := by
  ext w
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨i x, hiH x hx, (hF x).symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx⟩ := D.range.mkQ_surjective (F.symm (B.range.mkQ y))
    have he := (hF x).symm.trans ((congrArg F hx).trans (F.apply_symm_apply _))
    obtain ⟨v, hv⟩ := (Submodule.Quotient.eq _).mp he
    refine ⟨_, ⟨P x, hp x, rfl⟩, (hF _).trans ((Submodule.Quotient.eq _).mpr ⟨Q v, ?_⟩)⟩
    have eq := (hq v).symm.trans ((congrArg Q hv).trans (Q.map_sub _ _))
    exact eq.trans (congrArg₂ (· - ·) (hcomm x).symm (hS y hy))


private theorem range_quotient_isotype_inclusion {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (H : Submodule ℂ X) (B : Submodule ℂ X) (N : Submodule ℂ H)
    (a : (H ⧸ N) →L[ℂ] (X ⧸ B)) (ha : ∀ x : H, a (N.mkQ x) = B.mkQ x.val) :
    range a = B.mkQ '' (H : Set X) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨x,rfl⟩ := N.mkQ_surjective w
    exact ⟨x.val, x.property, (ha x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨N.mkQ ⟨x,hx⟩, ha _⟩

private def IsotypicProjectionLift {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (z : X → Y) (P : Y →L[ℂ] Y) (H : Submodule ℂ X) : Prop :=
  ∃ Q : X →L[ℂ] X, (∀ f, z (Q f) = P (z f)) ∧ (∀ f, Q f ∈ H) ∧ ∀ f ∈ H, Q f = f

private theorem compare_from_projectors {X Y T : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup T] [Module ℂ T] [TopologicalSpace T]
    {z : X → T} {w : Y → T} {P : T →L[ℂ] T} {H : Submodule ℂ X} {S : Submodule ℂ Y}
    (C : T →L[ℂ] T) (hpc : ∀ v, P (C v) = C (P v))
    (px : IsotypicProjectionLift z P H) (py : IsotypicProjectionLift w P S)
    (A : X →L[ℂ] X) (B : Y →L[ℂ] Y) (i : X →L[ℂ] Y)
    (hz : Injective z) (hw : Injective w) (hi : ∀ x, w (i x) = z x)
    (hA : ∀ x, z (A x) = C (z x)) (hB : ∀ y, w (B y) = C (w y))
    (F : (X ⧸ A.range) ≃L[ℂ] (Y ⧸ B.range)) (hF : ∀ x, F (A.range.mkQ x) = B.range.mkQ (i x)) :
    let N := (H.map A.toLinearMap).comap H.subtype
    let M := (S.map B.toLinearMap).comap S.subtype
    F '' (A.range.mkQ '' (H : Set X)) = B.range.mkQ '' (S : Set Y) ∧
    ∃ J : (H ⧸ N) ≃L[ℂ] (S ⧸ M), ∀ x : H, ∃ y : S, y.val = i x.val ∧ J (N.mkQ x) = M.mkQ y := by
  intro N M
  obtain ⟨Q,hQ,hQm,hQf⟩ := px
  obtain ⟨R,hR,hRm,hRf⟩ := py
  have hQc x : Q (A x) = A (Q x) := hz ((hQ _).trans ((congrArg P (hA x)).trans ((hpc _).trans
    ((congrArg C (hQ x).symm).trans (hA _).symm))))
  have hRc y : R (B y) = B (R y) := hw ((hR _).trans ((congrArg P (hB y)).trans ((hpc _).trans
    ((congrArg C (hR y).symm).trans (hB _).symm))))
  have hIQ x : i (Q x) = R (i x) := hw ((hi _).trans ((hQ x).trans ((congrArg P (hi x).symm).trans (hR _).symm)))
  have him (x : X) (hx : x ∈ H) : i x ∈ S := by
    have he := (hIQ x).symm.trans (congrArg i (hQf x hx))
    exact he ▸ hRm (i x)
  have hI := compared_isotype_images A B H S i F hF Q R hQm hRf him hRc hIQ
  refine ⟨hI, ?_⟩
  obtain ⟨a,b,hab,ha,-⟩ := retract_quotient_maps H A Q hQm hQf hQc
  obtain ⟨c,d,hcd,hc,-⟩ := retract_quotient_maps S B R hRm hRf hRc
  have hr : F '' range a = range c := by rw [range_quotient_isotype_inclusion H A.range N a ha,
    range_quotient_isotype_inclusion S B.range M c hc, hI]
  obtain ⟨J,hJ⟩ := quotient_equiv_on_retracts F a b c d hab hcd hr
  refine ⟨J, fun x ↦ ⟨⟨i x.val, him x.val x.property⟩, rfl, hcd.injective ?_⟩⟩
  exact (hJ (N.mkQ x)).trans ((congrArg F (ha x)).trans ((hF x.val).trans (hc ⟨i x.val, him x.val x.property⟩).symm))
end

section
set_option linter.unusedSectionVars false
variable [MeasurableSpace G] [BorelSpace G] (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]
variable (ω : PontryaginDual m.toMonoidHom.ker)

private theorem project_endomorphism {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (z : X → Y) (P : Y →L[ℂ] Y)
    (H : Submodule ℂ X) (A : X →ₗ[ℂ] H) (hc : Continuous A) (hA : ∀ f, z (A f).val = P (z f)) :
    ∃ Q : X →L[ℂ] X, ∀ f, z (Q f) = P (z f) :=
  ⟨H.subtypeL.comp ⟨A, hc⟩, hA⟩

private theorem project_endomorphism_of_family {X Y J : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (z : J → X → Y) (j : J) (P : Y →L[ℂ] Y)
    (H : Submodule ℂ X) (hu : ∃! A : X →ₗ[ℂ] H, ∀ f a, z a (A f).val = P (z a f))
    (hc : ∀ A : X →ₗ[ℂ] H, (∀ f a, z a (A f).val = P (z a f)) → Continuous A) :
    ∃ Q : X →L[ℂ] X, ∀ f, z j (Q f) = P (z j f) := by
  obtain ⟨A, hA, -⟩ := hu
  exact project_endomorphism (z j) P H A (hc A hA) (fun f ↦ hA f j)

private theorem mem_of_quotient_projector {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (A : X →L[ℂ] X) (H : Submodule ℂ X)
    (hq : ∃ e : (X ⧸ A.ker) ≃L[ℂ] H, ∀ f, (e (A.ker.mkQ f)).val = A f) (f : X) : A f ∈ H := by
  obtain ⟨e, he⟩ := hq
  exact (he f) ▸ (e (A.ker.mkQ f)).property

private theorem ordinary_isotypicProjector_mem (f : SchwartzBruhat G) :
    schwartzBruhatIsotypicProjector m hm μ₁ ω f ∈ actionIsotype ρK ω :=
  mem_of_quotient_projector (schwartzBruhatIsotypicProjector m hm μ₁ ω) (actionIsotype ρK ω)
    (schwartzBruhatIsotypicProjector_quotient_equiv m hm μ₁ ω) f

private theorem ordinary_projector_difference (g : G) (f : SchwartzBruhat G) :
    schwartzBruhatIsotypicProjector m hm μ₁ ω (schwartzBruhatCyclicDifference g f) =
      schwartzBruhatCyclicDifference g (schwartzBruhatIsotypicProjector m hm μ₁ ω f) := by
  let P := schwartzBruhatIsotypicProjector m hm μ₁ ω
  let t := schwartzBruhatTranslationAction (G := G) g⁻¹
  have ht (u : SchwartzBruhat G) (x : G) : t u x = u (g * x) :=
    (schwartzBruhatTranslationAction_apply g⁻¹ x u).trans (congrArg (fun a ↦ u (a * x)) (inv_inv g))
  have hpt : P (t f) = t (P f) := by
    apply Subtype.ext
    funext x
    change P (t f) x = t (P f) x
    have h1 := (schwartzBruhatIsotypicProjector_apply m hm μ₁ ω (t f) x).2
    have h2 := (schwartzBruhatIsotypicProjector_apply m hm μ₁ ω f (g * x)).2
    have h3 := integral_congr_ae (μ := μ₁) (ae_of_all _ fun k : K ↦
      congrArg (star (ω k : ℂ) * ·) ((ht f (k.val⁻¹*x)).trans (congrArg (fun u ↦ f u) (mul_left_comm g k.val⁻¹ x))))
    exact h1.trans ((congrArg ((μ₁.real univ)⁻¹ • ·) h3).trans (h2.symm.trans (ht (P f) x).symm))
  have eq := (P.map_sub f (t f)).trans (congrArg (P f - ·) hpt)
  unfold schwartzBruhatCyclicDifference
  exact eq

private theorem map_commutes_prod {X Y L : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] (p : X → Y) (A : L → X →L[ℂ] X)
    (B : L → Y →L[ℂ] Y) (h : ∀ g x, p (A g x) = B g (p x)) (s : List L) :
    ∀ x, p ((s.map A).prod x) = (s.map B).prod (p x) := by
  induction s with
  | nil => exact fun _ ↦ rfl
  | cons g s ih => exact fun x ↦ (h g ((s.map A).prod x)).trans (congrArg (B g) (ih x))

private theorem ordinary_projector_product (s : List G) (f : SchwartzBruhat G) :
    schwartzBruhatIsotypicProjector m hm μ₁ ω (schwartzBruhatDifferenceProduct s f) =
      schwartzBruhatDifferenceProduct s (schwartzBruhatIsotypicProjector m hm μ₁ ω f) :=
  map_commutes_prod (schwartzBruhatIsotypicProjector m hm μ₁ ω) schwartzBruhatCyclicDifference
    schwartzBruhatCyclicDifference (ordinary_projector_difference m hm μ₁ ω) s f

variable (I : Set ℝ) (hI : OrdConnected I) (h0 : 0 ∈ I)
local notation "V" => ModulatedExponentialDecay m I
local notation "z₀" => modulatedExponentialDecayTwist m I ⟨0,h0⟩
include hms hI in
private theorem decay_square_for_action (ρ : G →* V →L[ℂ] V)
    (hρ : ∀ g f x, (ρ g f).val x = f.val (g⁻¹ * x)) :
    ∃ Q : V →L[ℂ] V, ∀ f, z₀ (Q f) = schwartzBruhatIsotypicProjector m hm μ₁ ω (z₀ f) := by
  have hu := existsUnique_modulatedExponentialDecay_isotypicProjector m I hm hms hI ⟨0,h0⟩ μ₁ ρ hρ ω
  have hc := modulatedExponentialDecay_isotypicProjector_continuous m I hm hms hI ⟨0,h0⟩ μ₁ ρ hρ ω
  let eval (a : I) (f : V) : SchwartzBruhat G := modulatedExponentialDecayTwist m I a f
  let atZero : I := ⟨0, h0⟩
  let H := actionIsotype (ρ.comp m.toMonoidHom.ker.subtype) ω
  let P := schwartzBruhatIsotypicProjector m hm μ₁ ω
  with_reducible_and_instances
    exact project_endomorphism_of_family (X := V) (Y := SchwartzBruhat G) (J := I)
      eval atZero P H hu hc

include hms hI in
private theorem exists_decay_projector_commuting_zeroTwist :
    ∃ Q : V →L[ℂ] V, ∀ f, z₀ (Q f) = schwartzBruhatIsotypicProjector m hm μ₁ ω (z₀ f) := by
  have acts := exists_modulatedExponentialDecay_translationAction m I hm hms hI ⟨0,h0⟩
  have sq := decay_square_for_action m hm hms μ₁ ω I hI h0
  with_reducible_and_instances
    exact acts.elim fun act h ↦ sq act h.1

private theorem decay_projector_mem_of_square (Q : V →L[ℂ] V) (f : V)
    (hq : z₀ (Q f) = schwartzBruhatIsotypicProjector m hm μ₁ ω (z₀ f)) :
    Q f ∈ modulatedDecayIsotype m I h0 ω := by
  change z₀ (Q f) ∈ actionIsotype ρK ω
  have hmemb := ordinary_isotypicProjector_mem m hm μ₁ ω (z₀ f)
  exact (congrArg (fun y : SchwartzBruhat G ↦ y ∈ actionIsotype ρK ω) hq).mpr hmemb

private theorem decay_projector_fix_of_square (Q : V →L[ℂ] V) (f : V)
    (hq : z₀ (Q f) = schwartzBruhatIsotypicProjector m hm μ₁ ω (z₀ f))
    (hf : f ∈ modulatedDecayIsotype m I h0 ω) : Q f = f := by
  change z₀ f ∈ actionIsotype ρK ω at hf
  have hz := hq.trans (schwartzBruhatIsotypicProjector_apply_isotype m hm μ₁ ω (z₀ f) hf)
  have ev (p : V) (x : G) : z₀ p x = p.val x := (modulatedExponentialDecay_zeroTwist_injective m I h0).2 p x
  exact Subtype.ext (funext fun x ↦ (ev (Q f) x).symm.trans ((congrArg (fun p : SchwartzBruhat G ↦ p x) hz).trans (ev f x)))

include hms hI in
private theorem decay_projection_data :
    IsotypicProjectionLift (X := V) (Y := SchwartzBruhat G) (fun f : V ↦ z₀ f)
      (schwartzBruhatIsotypicProjector m hm μ₁ ω) (modulatedDecayIsotype m I h0 ω) := by
  unfold IsotypicProjectionLift
  have sq := exists_decay_projector_commuting_zeroTwist m hm hms μ₁ ω I hI h0
  have mem := decay_projector_mem_of_square m hm μ₁ ω I h0
  have fix := decay_projector_fix_of_square m hm μ₁ ω I h0
  with_reducible_and_instances
    exact sq.elim fun q h ↦ ⟨q, h, fun f ↦ mem q f (h f), fun f hf ↦ fix q f (h f) hf⟩
end

variable (I : Set ℝ) (hOpen : IsOpen I) (hInt : OrdConnected I) (h0 : 0 ∈ I)

local notation "V" => ModulatedExponentialDecay m I
local notation "T" => SchwartzBruhat G
local notation "ΔE" => modulatedDifferenceProduct m hm hms univ ordConnected_univ univ_nonempty S
local notation "ΔI" => modulatedDifferenceProduct m hm hms I hInt ⟨0, h0⟩ S
local notation "ΔT" => schwartzBruhatDifferenceProduct S
local notation "j₀" => modulatedExponentialDecayTwist m I ⟨0, h0⟩

-- TODO(paper-gap): In (4.6.3.2), the middle denominator must be P_S S_I(G).
-- The injection into P_γ E / P_S E has source E / P_{S₀} E.
-- The closedness argument needs higher moments at repeated frequencies.

section

set_option linter.unusedSectionVars false

/-- Test a difference product on a retract. Each single difference has closed image
on the retract by pullback, so on a Fréchet retract their product is a closed embedding. -/
private theorem closed_stage_test {L X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℂ Y]
    (hY : IsFrechetTVS Y) (i : Y →L[ℂ] X) (r : X →L[ℂ] Y) (hri : LeftInverse r i)
    (D : L → X →L[ℂ] X) (s : List L)
    (hd : ∀ g ∈ s, Injective (D g) ∧ IsClosed (range (D g)))
    (hp : ∀ g ∈ s, ∀ x, i (r (D g x)) = D g (i (r x)))
    (x : X) (hx : x ∈ closure (range ((s.map D).prod : X →L[ℂ] X))) (hfix : i (r x) = x) :
    x ∈ range ((s.map D).prod : X →L[ℂ] X) := by
  let C (g : L) := (r.comp (D g)).comp i
  have hir (g : L) (hg : g ∈ s) (y : Y) : i (C g y) = D g (i y) :=
    (hp g hg (i y)).trans (congrArg (fun v ↦ D g (i v)) (hri y))
  have hrc (g : L) (hg : g ∈ s) (u : X) : r (D g u) = C g (r u) :=
    (hri.injective ((hp g hg u).trans (hir g hg (r u)).symm))
  have hc (g : L) (hg : g ∈ s) : IsClosedEmbedding (C g) := by
    have hi : Injective (C g) := fun y z h ↦ hri.injective ((hd g hg).1
      ((hir g hg y).symm.trans ((congrArg i h).trans (hir g hg z))))
    have hr : range (C g) = i ⁻¹' range (D g) := by
      ext y
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨i v, (hir g hg v).symm⟩
      · rintro ⟨u, hu⟩
        exact ⟨r u, (hrc g hg u).symm.trans ((congrArg r hu).trans (hri y))⟩
    exact frechet_closedEmbedding_of_injective hY (C g) hi
      ((congrArg IsClosed hr).mpr ((hd g hg).2.preimage i.continuous))
  have hprod (l : List L) (hl : ∀ g ∈ l, g ∈ s) :
      IsClosedEmbedding ((l.map C).prod : Y →L[ℂ] Y) ∧
      (∀ y, i ((l.map C).prod y) = (l.map D).prod (i y)) ∧
      ∀ u, r ((l.map D).prod u) = (l.map C).prod (r u) := by
    induction l with
    | nil => exact ⟨IsClosedEmbedding.id, fun _ ↦ rfl, fun _ ↦ rfl⟩
    | cons g l ih =>
      have hg := hl g (.head _)
      obtain ⟨he, hi, hr⟩ := ih (fun a ha ↦ hl a (.tail _ ha))
      exact ⟨(hc g hg).comp he, fun y ↦ (hir g hg _).trans (congrArg (D g) (hi y)),
        fun u ↦ (hrc g hg _).trans (congrArg (C g) (hr u))⟩
  obtain ⟨he, hi, hr⟩ := hprod s fun _ h ↦ h
  have hsub : range ((s.map D).prod : X →L[ℂ] X) ⊆ r ⁻¹' range ((s.map C).prod : Y →L[ℂ] Y) :=
    fun _ ⟨u, hu⟩ ↦ ⟨r u, (hr u).symm.trans (congrArg r hu)⟩
  obtain ⟨v, hv⟩ := (closure_minimal hsub (he.isClosed_range.preimage r.continuous)) hx
  exact ⟨i v, (hi v).symm.trans ((congrArg i hv).trans hfix)⟩

private theorem schwartzBruhat_exists_full_stage (hgen : IsCompactlyGeneratedGroup G)
    (f : SchwartzBruhat G) : ∃ (a : BruhatStructuralPair G)
      (e : ElementaryLCAPresentation a.quotient), (∀ x : G, x ∈ a.val.1) ∧
      f ∈ range (show SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G from schwartzBruhatStageInclusion a e) := by
  refine ((mem_schwartzBruhatSubmodule_iff f.val).mp f.property).elim fun b h ↦ ?_
  refine h.elim fun d h ↦ ?_
  refine h.elim fun s hs ↦ ?_
  let top : (⊤ : Subgroup G) ≃ₜ* G :=
    { Subgroup.topEquiv with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  let a : BruhatStructuralPair G := ⟨(⊤, b.val.2), isOpen_univ,
    isCompactlyGeneratedGroup_of_continuousMulEquiv top.symm hgen, b.property.2.2.1, le_top⟩
  let e := Classical.choice a.elementary
  have hba : b ≤ a := ⟨le_top, le_rfl⟩
  refine (schwartzBruhatStage_transition hba d e).elim fun j hj ↦ ?_
  exact ⟨a, e, fun _ ↦ trivial, j s, Subtype.ext ((hj.1 s).trans hs)⟩



private theorem schwartzBruhatStage_average_translate (a : BruhatStructuralPair G)
    (ha : ∀ x : G, x ∈ a.val.1) (g : G) (u v : G → ℂ) (ht : ∀ x, u x = v (g * x)) (x : G) :
    schwartzBruhatStageAverage a u x = schwartzBruhatStageAverage a v (g * x) := by
  unfold schwartzBruhatStageAverage
  rw [ite_eq_left (ha _), ite_eq_left (ha _)]
  apply integral_congr_ae
  exact ae_of_all _ fun h ↦ (ht _).trans (congrArg v (mul_left_comm g _ x))


private theorem schwartzBruhatStage_average_difference (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (ha : ∀ x : G, x ∈ a.val.1)
    (i : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat G) (hi : ∀ y x, i y x = schwartzBruhatStageRealization a e y x)
    (r : SchwartzBruhat G →L[ℂ] SchwartzBruhatStage e)
    (hr : ∀ f x, schwartzBruhatStageRealization a e (r f) x = schwartzBruhatStageAverage a f x)
    (g : G) (f : SchwartzBruhat G) :
    i (r (schwartzBruhatCyclicDifference g f)) = schwartzBruhatCyclicDifference g (i (r f)) := by
  let translate : SchwartzBruhat G →L[ℂ] SchwartzBruhat G := schwartzBruhatTranslationAction (G := G) g⁻¹
  have ht (u : SchwartzBruhat G) (x : G) : translate u x = u (g * x) :=
    (schwartzBruhatTranslationAction_apply g⁻¹ x u).trans (congrArg (fun t ↦ u (t * x)) (inv_inv g))
  have ht' : i (r (translate f)) = translate (i (r f)) := by
    refine Subtype.ext (funext fun x ↦ ?_)
    exact (hi _ x).trans ((hr _ x).trans ((schwartzBruhatStage_average_translate a ha g (translate f) f (ht f) x).trans
      ((hr f (g * x)).symm.trans ((hi _ _).symm.trans (ht _ x).symm))))
  have H : i (r (f - translate f)) = i (r f) - translate (i (r f)) :=
    (congrArg i (r.map_sub f (translate f))).trans ((i.map_sub _ _).trans (congrArg (i (r f) - ·) ht'))
  unfold schwartzBruhatCyclicDifference
  exact H

include hm hms in
private theorem schwartzBruhat_single_difference (g : G) (hg : 1 < (m g).val) :
    Injective (schwartzBruhatCyclicDifference g) ∧ IsClosed (range (schwartzBruhatCyclicDifference g)) := by
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  have : IsClosed ((Subgroup.zpowers g : Subgroup G) : Set G) := modulatedCyclicSubgroup_closed m g hg
  have : T2Space (SchwartzBruhat (G ⧸ Subgroup.zpowers g)) := schwartzBruhat_t2
  have hclosed := (schwartzBruhatCyclicPeriodization m g hg).isClosed_ker
  have hk := schwartzBruhatCyclicPeriodization_ker_eq_range m g hm hms hg
  refine ⟨LinearMap.ker_eq_bot.mp (le_antisymm ?_ bot_le), ?_⟩
  · intro f hf
    change schwartzBruhatCyclicDifference g f = 0 at hf
    have hper (x : G) : f (g * x) = f x := (sub_eq_zero.mp ((schwartzBruhatCyclicDifference_apply g f x).symm.trans
      (congrArg (fun v : SchwartzBruhat G ↦ v x) hf))).symm
    refine Subtype.ext (funext fun x ↦ ?_)
    have hn (n : ℕ) : f (g ^ n * x) = f x := by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', mul_assoc, hper, ih]
    have hs := (schwartzBruhatCyclicPeriodization_hasSum m g hg f x).summable.comp_injective
      (Nat.cast_injective : Injective (fun n : ℕ ↦ (n : ℤ)))
    change Summable (fun n : ℕ ↦ f (g ^ (n : ℤ) * x)) at hs
    change f x = 0
    simpa only [zpow_natCast, hn, summable_const_iff] using hs
  · exact (congrArg (fun p : Submodule ℂ (SchwartzBruhat G) ↦ IsClosed (p : Set (SchwartzBruhat G))) hk).mp hclosed


end

include hm hms hS hγS in
private theorem ordinary_product_range_closed :
    IsClosed ((ΔT).range : Set (SchwartzBruhat G)) := by
  apply isClosed_of_closure_subset
  intro f hf
  refine (schwartzBruhat_exists_full_stage (compactlyGenerated_of_surjective_modulation m hm hms)
    f).elim fun a h ↦ ?_
  refine h.elim fun e he ↦ ?_
  let _ := e.finiteGroup
  let _ := e.finiteTopology
  let _ := e.finiteDiscrete
  let _ := e.finiteFintype
  have hFr : IsFrechetTVS (SchwartzBruhatStage e) :=
    elementarySchwartz_isFrechet (m := e.realDim) (n := e.torusDim) (r := e.latticeRank) (F := e.finiteFactor)
  let i : SchwartzBruhatStage e →L[ℂ] SchwartzBruhat G :=
    ⟨schwartzBruhatStageInclusion a e, (schwartzBruhatStage_isEmbedding a e).continuous⟩
  have hi (y : SchwartzBruhatStage e) (x : G) : i y x = schwartzBruhatStageRealization a e y x := rfl
  refine (schwartzBruhatStage_average_retraction a e).elim fun r hr ↦ ?_
  have hri : LeftInverse r i := hr.1
  have hfix : i (r f) = f := by
    refine he.2.elim fun y hy ↦ ?_
    exact (congrArg (fun u ↦ i (r u)) hy.symm).trans ((congrArg i (hri y)).trans hy)
  exact closed_stage_test hFr i r hri schwartzBruhatCyclicDifference S
    (fun g hg ↦ schwartzBruhat_single_difference m hm hms g (hγS g hg))
    (fun g _ ↦ schwartzBruhatStage_average_difference a e he.1 i hi r hr.2 g) f hf hfix

section
set_option linter.unusedSectionVars false

local notation "de" => (fun g ↦ modulatedCyclicDifference m g hm hms univ ordConnected_univ univ_nonempty)
local notation "di" => (fun g ↦ modulatedCyclicDifference m g hm hms I hInt ⟨0, h0⟩)
local notation "dt" => (schwartzBruhatCyclicDifference (G := G))
local notation "z₀" => modulatedExponentialDecayTwist m I ⟨0, h0⟩

include hm hms in
private theorem decay_lf (U : Set ℝ) (hU : OrdConnected U) (hn : U.Nonempty) :
    IsLFSpace (ModulatedExponentialDecay m U) := by
  let t := exists_surjectiveModulation_section m hm hms
  exact lfSpace_quotient_properties.1 (modulatedExponentialDecay_strictLF m U hm hU hn t.choose t.choose_spec)

variable [MeasurableSpace G] [BorelSpace G]

include hOpen hm hms hInt in
private theorem cyclic_comparison_data (i : E →L[ℂ] V) (hi : ∀ f x, (i f).val x = f.val x)
    (j : V →L[ℂ] T) (hj : ∀ f, j f = z₀ f) (g : G) (hg : 1 < (m g).val) :
    ((∀ x, i x ∈ (di g).range → x ∈ (de g).range) ∧ ∀ y, ∃ x v, y = i x + di g v) ∧
      (∀ y, j y ∈ (dt g).range → y ∈ (di g).range) ∧ ∀ z, ∃ y v, z = j y + dt g v := by
  let evE : E → G → ℂ := fun x ↦ x.val
  let evV : V → G → ℂ := fun x ↦ x.val
  let z : V → T := fun f ↦ z₀ f
  have hinj : Injective evV := Subtype.val_injective
  have ex := modulatedIntervalDifference_quotient_equivs m g hm hms hg I hOpen hInt h0
  let p := compare_factor_on_representatives (L := G) (X := E) (Y := V) (Z := T)
    evE evV hinj i j z hj hi (de g) (di g) (dt g)
  with_reducible_and_instances
    exact p ex
private theorem decay_comparison_commute (i : E →L[ℂ] V) (hi : ∀ f x, (i f).val x = f.val x) :
    ∀ g f, i (de g f) = di g (i f) :=
  commute_difference_of_evaluation (fun x : E ↦ x.val) (fun y : V ↦ y.val) Subtype.val_injective
    i hi de di (fun g ↦ modulatedCyclicDifference_apply m g hm hms univ ordConnected_univ univ_nonempty)
    (fun g ↦ modulatedCyclicDifference_apply m g hm hms I hInt ⟨0, h0⟩)

private theorem schwartz_comparison_commute (j : V →L[ℂ] T) (hj : ∀ f x, j f x = f.val x) :
    ∀ g f, j (di g f) = dt g (j f) :=
  commute_difference_of_evaluation (fun x : V ↦ x.val) (fun y : T ↦ y.val) Subtype.val_injective
    j hj di dt (fun g ↦ modulatedCyclicDifference_apply m g hm hms I hInt ⟨0, h0⟩)
    (fun g ↦ schwartzBruhatCyclicDifference_apply g)

include hS hγS hOpen in
private theorem ambient_given_inclusion (i : E →L[ℂ] V) (hi : ∀ f x, (i f).val x = f.val x) :
    let N := (S.map de).prod.range
    let M := (S.map di).prod.range
    let R := (S.map dt).prod.range
    ∃ (F : (E ⧸ N) ≃L[ℂ] (V ⧸ M)) (J : (V ⧸ M) ≃L[ℂ] (T ⧸ R)),
      (∀ f, F (N.mkQ f) = M.mkQ (i f)) ∧
      ∀ f, J (M.mkQ f) = R.mkQ (z₀ f) := by
  intro N M R
  let j : V →L[ℂ] T := ⟨z₀, modulatedExponentialDecay_zeroTwist_continuous m hm hms I hInt h0⟩
  have hj := (modulatedExponentialDecay_zeroTwist_injective m I h0).2
  have hc := cyclic_comparison_data m hm hms I hOpen hInt h0 i hi j (fun _ ↦ rfl)
  have commute := schwartz_comparison_commute m hm hms I hInt h0 j hj
  have hinj : Injective j := (modulatedExponentialDecay_zeroTwist_injective m I h0).1
  let e := (modulatedExponentialDecay_singleton_schwartz m hm hms 0).choose
  have hV := decay_lf m hm hms I hInt ⟨0, h0⟩
  have htinj (g : G) (hg : g ∈ S) := (schwartzBruhat_single_difference m hm hms g (hγS g hg)).1
  have hIinj (g : G) (hg : g ∈ S) : Injective (di g) := fun x y he ↦
    hinj (htinj g hg ((commute g x).symm.trans ((congrArg j he).trans (commute g y))))
  have hJ := comparison_equiv_of_product hV
    (decay_lf m hm hms {0} ordConnected_singleton (singleton_nonempty _)) e j di dt S
    (fun a _ ↦ commute a) htinj (fun a ha ↦ (hc a (hγS a ha)).2)
    (ordinary_product_range_closed m hm hms S hS hγS)
  have hF := comparison_equiv_of_product (decay_lf m hm hms univ ordConnected_univ univ_nonempty)
    hV (ContinuousLinearEquiv.refl ℂ V) i de di S
    (fun a _ ↦ decay_comparison_commute m hm hms I hInt h0 i hi a) hIinj
    (fun a ha ↦ (hc a (hγS a ha)).1) hJ.1
  with_reducible_and_instances
    exact hF.2.elim fun F hf ↦ hJ.2.elim fun J hj ↦ ⟨F, J, hf, hj⟩

include hS hγS hOpen hm hms hInt h0 in
private theorem comparison_inclusion_exists : ∃ i : E →L[ℂ] V, ∀ f x, (i f).val x = f.val x := by
  let g := (S.exists_mem_of_ne_nil hS).choose
  have hg := hγS g (S.exists_mem_of_ne_nil hS).choose_spec
  have h := modulatedIntervalDifference_quotient_equivs m g hm hms hg I hOpen hInt h0
  with_reducible_and_instances
    exact h.elim fun i rest ↦ rest.elim fun F rest ↦ rest.elim fun J data ↦ ⟨i, data.1⟩

include hS hγS hOpen in
private theorem ambient_difference_quotient_equivalences :
    let N := (S.map de).prod.range
    let M := (S.map di).prod.range
    let R := (S.map dt).prod.range
    ∃ (i : E →L[ℂ] V) (F : (E ⧸ N) ≃L[ℂ] (V ⧸ M)) (J : (V ⧸ M) ≃L[ℂ] (T ⧸ R)),
      (∀ f x, (i f).val x = f.val x) ∧ (∀ f, F (N.mkQ f) = M.mkQ (i f)) ∧
      ∀ f, J (M.mkQ f) = R.mkQ (z₀ f) := by
  have inc := comparison_inclusion_exists m hm hms S hS hγS I hOpen hInt h0
  have build := ambient_given_inclusion m hm hms S hS hγS I hOpen hInt h0
  with_reducible_and_instances
    exact inc.elim fun i hi ↦ (build i hi).elim fun F rest ↦ rest.elim fun J data ↦ ⟨i,F,J,hi,data⟩

private theorem zeroTwist_asFunction_injective : Injective (fun f : V ↦ z₀ f) := by
  have ev (p : V) (x : G) : z₀ p x = p.val x := (modulatedExponentialDecay_zeroTwist_injective m I h0).2 p x
  exact fun x y h ↦ Subtype.ext (funext fun a ↦ (ev x a).symm.trans
    ((congrArg (fun p : T ↦ p a) h).trans (ev y a)))

private theorem zeroTwist_product (s : List G) (f : V) :
    z₀ ((s.map di).prod f) = (s.map dt).prod (z₀ f) := by
  let j : V →L[ℂ] T := ⟨z₀, modulatedExponentialDecay_zeroTwist_continuous m hm hms I hInt h0⟩
  have hj (v : V) (x : G) : j v x = v.val x := (modulatedExponentialDecay_zeroTwist_injective m I h0).2 v x
  have comm := schwartz_comparison_commute m hm hms I hInt h0 j hj
  exact map_commutes_prod (X := V) (Y := T) j di dt comm s f

private theorem zeroTwist_inclusion_eq (i : E →L[ℂ] V) (h : ∀ f x, (i f).val x = f.val x) (f : E) :
    z₀ (i f) = modulatedExponentialDecayTwist m univ ⟨0, mem_univ _⟩ f := by
  refine Subtype.ext (funext fun x ↦ ?_)
  exact ((modulatedExponentialDecay_zeroTwist_injective m I h0).2 (i f) x).trans
    ((h f x).trans ((modulatedExponentialDecay_zeroTwist_injective m univ (mem_univ _)).2 f x).symm)

local notation "D₀" => (S.map de).prod
local notation "D₁" => (S.map di).prod
local notation "D₂" => (S.map dt).prod
local notation "zE" => modulatedExponentialDecayTwist m univ ⟨0, mem_univ (0 : ℝ)⟩
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]
variable (η : PontryaginDual m.toMonoidHom.ker)
local notation "H₁" => modulatedDecayIsotype m I h0 η
local notation "H₂" => actionIsotype ρK η

include μ₁ in
private theorem compare_full_interval_isotypes (i : E →L[ℂ] V) (hi : ∀ f x, (i f).val x = f.val x)
    (F : (E ⧸ (D₀).range) ≃L[ℂ] (V ⧸ (D₁).range))
    (hF : ∀ f, F ((D₀).range.mkQ f) = (D₁).range.mkQ (i f)) :
    let N := ((H₀[η]).map (D₀).toLinearMap).comap (H₀[η]).subtype
    let M := ((H₁).map (D₁).toLinearMap).comap (H₁).subtype
    F '' ((D₀).range.mkQ '' (H₀[η] : Set E)) = (D₁).range.mkQ '' (H₁ : Set V) ∧
      ∃ J : (H₀[η] ⧸ N) ≃L[ℂ] (H₁ ⧸ M), ∀ f : H₀[η], ∃ g : H₁,
        g.val = i f.val ∧ J (N.mkQ f) = M.mkQ g := by
  let z : E → T := fun f ↦ zE f
  let P := schwartzBruhatIsotypicProjector m hm μ₁ η
  have hz := zeroTwist_asFunction_injective m univ (mem_univ (0 : ℝ))
  have hw := zeroTwist_asFunction_injective m I h0
  have hiw := zeroTwist_inclusion_eq m I h0 i hi
  let ze : E →L[ℂ] T := ⟨zE, modulatedExponentialDecay_zeroTwist_continuous m hm hms univ ordConnected_univ (mem_univ _)⟩
  have je (f : E) (t : G) : ze f t = f.val t := (modulatedExponentialDecay_zeroTwist_injective m univ (mem_univ _)).2 f t
  have com (g : G) (f : E) : ze (de g f) = dt g (ze f) := by
    refine Subtype.ext (funext fun t ↦ ?_)
    exact (je _ t).trans ((modulatedCyclicDifference_apply m g hm hms univ ordConnected_univ univ_nonempty f t).trans
      ((congrArg₂ (· - ·) (je f t).symm (je f (g*t)).symm).trans (schwartzBruhatCyclicDifference_apply g (ze f) t).symm))
  have hA (f : E) : z (D₀ f) = D₂ (z f) := map_commutes_prod (X := E) (Y := T) ze de dt com S f
  have hB := zeroTwist_product m hm hms I hInt h0 S
  have pc := ordinary_projector_product m hm μ₁ η S
  unfold schwartzBruhatDifferenceProduct at pc
  have px := decay_projection_data m hm hms μ₁ η univ ordConnected_univ (mem_univ _)
  have py := decay_projection_data m hm hms μ₁ η I hInt h0
  let A := D₀
  let B := D₁
  let C := D₂
  with_reducible_and_instances
    have comp := compare_from_projectors (P := P) C pc px py
    have q := comp A B i hz hw hiw hA hB
    exact q F hF

include μ₁ in
private theorem compare_interval_ordinary_isotypes (J : (V ⧸ (D₁).range) ≃L[ℂ] (T ⧸ (D₂).range))
    (hJ : ∀ f, J ((D₁).range.mkQ f) = (D₂).range.mkQ (z₀ f)) :
    let N := ((H₁).map (D₁).toLinearMap).comap (H₁).subtype
    let M := ((H₂).map (D₂).toLinearMap).comap (H₂).subtype
    J '' ((D₁).range.mkQ '' (H₁ : Set V)) = (D₂).range.mkQ '' (H₂ : Set T) ∧
      ∃ F : (H₁ ⧸ N) ≃L[ℂ] (H₂ ⧸ M), ∀ f : H₁, ∃ g : H₂,
        g.val = z₀ f.val ∧ F (N.mkQ f) = M.mkQ g := by
  let z : V → T := fun f ↦ z₀ f
  let j : V →L[ℂ] T := ⟨z₀, modulatedExponentialDecay_zeroTwist_continuous m hm hms I hInt h0⟩
  let P := schwartzBruhatIsotypicProjector m hm μ₁ η
  have hz := zeroTwist_asFunction_injective m I h0
  have hB := zeroTwist_product m hm hms I hInt h0 S
  have hi (f : V) : id (j f) = z f := rfl
  have hp := ordinary_isotypicProjector_mem m hm μ₁ η
  have hf := schwartzBruhatIsotypicProjector_apply_isotype m hm μ₁ η
  have pc := ordinary_projector_product m hm μ₁ η S
  unfold schwartzBruhatDifferenceProduct at pc
  have px := decay_projection_data m hm hms μ₁ η I hInt h0
  have py : IsotypicProjectionLift (X := T) (Y := T) id P H₂ := ⟨P, fun _ ↦ rfl, hp, hf⟩
  let B := D₁
  let C := D₂
  have hC (y : T) : id (C y) = C (id y) := rfl
  with_reducible_and_instances
    have comp := compare_from_projectors (P := P) C pc px py
    have q := comp B C j hz injective_id hi hB hC
    exact q J hJ

end

include hS hγS hOpen in
/-- Paper: Corollary 4.6.3.1, pp. 219–220. The two canonical inclusions
induce topological linear isomorphisms of the difference quotients.
Each isomorphism carries the image of a norm-one isotype onto the image
of the same isotype in its target quotient. -/
theorem modulatedDifferenceProduct_quotient_equivs :
    let R₀ := (ΔE).toLinearMap.range
    let R₁ := (ΔI).toLinearMap.range
    let R₂ := (ΔT).toLinearMap.range
    ∃ (i : E →L[ℂ] V) (F : (E ⧸ R₀) ≃L[ℂ] (V ⧸ R₁))
      (J : (V ⧸ R₁) ≃L[ℂ] (T ⧸ R₂)),
      (∀ (f : E) (x : G), (i f).val x = f.val x) ∧
      (∀ f : E, F (R₀.mkQ f) = R₁.mkQ (i f)) ∧
      (∀ f : V, J (R₁.mkQ f) = R₂.mkQ (j₀ f)) ∧
      ∀ η : PontryaginDual m.toMonoidHom.ker,
        let H₁ := modulatedDecayIsotype m I h0 η
        let H₂ := actionIsotype ρK η
        F '' (R₀.mkQ '' (H₀[η] : Set E)) = R₁.mkQ '' (H₁ : Set V) ∧
          J '' (R₁.mkQ '' (H₁ : Set V)) = R₂.mkQ '' (H₂ : Set T) := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  have : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.1.isCompact_preimage (isCompact_singleton (x := 1)))
  let μ₁ : Measure K := Measure.haar
  have : μ₁.IsHaarMeasure := inferInstanceAs (Measure.haar (G := K)).IsHaarMeasure
  have aq := ambient_difference_quotient_equivalences m hm hms S hS hγS I hOpen hInt h0
  have cmpE := compare_full_interval_isotypes m hm hms S I hInt h0 μ₁
  have cmpI := compare_interval_ordinary_isotypes m hm hms S I hInt h0 μ₁
  unfold modulatedDifferenceProduct schwartzBruhatDifferenceProduct
  with_reducible_and_instances
    refine aq.elim fun i qi ↦ qi.elim fun F qF ↦ qF.elim fun J h ↦ ?_
    exact ⟨i, F, J, h.1, h.2.1, h.2.2, fun η ↦
      ⟨(cmpE η i h.1 F h.2.1).1, (cmpI η J h.2.2).1⟩⟩

include hm hms hS hγS in
/-- Paper: Corollary 4.6.3.1, p. 220. The ordinary product range is closed.
The two equivalences in (4.6.3.1) therefore identify Hausdorff quotients. -/
theorem schwartzBruhatDifferenceProduct_isClosed_range :
    IsClosed ((ΔT).range : Set (SchwartzBruhat G)) := by
  exact ordinary_product_range_closed m hm hms S hS hγS

include hS hγS hOpen in
/-- Paper: Corollary 4.6.3.1, pp. 219–220. On each norm-one isotype the
canonical inclusions identify the quotients by differences of isotypic functions. -/
theorem modulatedIsotypicDifferenceProduct_quotient_equivs :
    let H := H₀[ω]
    let H₁ := modulatedDecayIsotype m I h0 ω
    let H₂ := actionIsotype ρK ω
    let R₀ := (H.map (ΔE).toLinearMap).comap H.subtype
    let R₁ := (H₁.map (ΔI).toLinearMap).comap H₁.subtype
    let R₂ := (H₂.map (ΔT).toLinearMap).comap H₂.subtype
    ∃ (F : (H ⧸ R₀) ≃L[ℂ] (H₁ ⧸ R₁)) (J : (H₁ ⧸ R₁) ≃L[ℂ] (H₂ ⧸ R₂)),
      (∀ f : H, ∃ g : H₁, (∀ x, g.val.val x = f.val.val x) ∧ F (R₀.mkQ f) = R₁.mkQ g) ∧
      ∀ g : H₁, ∃ h : H₂, (∀ x, h.val x = g.val.val x) ∧ J (R₁.mkQ g) = R₂.mkQ h := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  have : CompactSpace K := isCompact_iff_compactSpace.mp
    (hm.1.isCompact_preimage (isCompact_singleton (x := 1)))
  let μ₁ : Measure K := Measure.haar
  have : μ₁.IsHaarMeasure := inferInstanceAs (Measure.haar (G := K)).IsHaarMeasure
  have aq := ambient_difference_quotient_equivalences m hm hms S hS hγS I hOpen hInt h0
  have cmpE := compare_full_interval_isotypes m hm hms S I hInt h0 μ₁ ω
  have cmpI := compare_interval_ordinary_isotypes m hm hms S I hInt h0 μ₁ ω
  let evalV : V → G → ℂ := fun v ↦ v.val
  have ev (v : V) (x : G) : j₀ v x = v.val x :=
    (modulatedExponentialDecay_zeroTwist_injective m I h0).2 v x
  unfold modulatedDifferenceProduct schwartzBruhatDifferenceProduct
  with_reducible_and_instances
    refine aq.elim fun i qi ↦ qi.elim fun F qF ↦ qF.elim fun J h ↦ ?_
    refine (cmpE i h.1 F h.2.1).2.elim fun A ha ↦ (cmpI J h.2.2).2.elim fun B hb ↦ ?_
    refine ⟨A, B, fun f ↦ (ha f).elim fun g hg ↦ ⟨g, fun x ↦ ?_, hg.2⟩,
      fun g ↦ (hb g).elim fun t ht ↦ ⟨t, fun x ↦ ?_, ht.2⟩⟩
    · exact (congrArg (fun v : V ↦ evalV v x) hg.1).trans (h.1 f.val x)
    · exact (congrArg (fun v : T ↦ v x) ht.1).trans (ev g.val x)

end RiemannMasullo
