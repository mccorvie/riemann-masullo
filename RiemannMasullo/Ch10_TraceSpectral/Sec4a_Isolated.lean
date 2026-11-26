module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppC_LCTVS.Sec3b_HilbertSchmidtProduct
import RiemannMasullo.AppC_LCTVS.Sec3a_SchattenInclusion
import RiemannMasullo.Ch10_TraceSpectral.Sec3_TraceClass
import RiemannMasullo.ForMathlib.Analysis.Distribution.DixmierMalliavin
import Mathlib.Topology.Instances.AddCircle.Defs

/-! # The spectral trace statements of §10.4.2 at orders between zero and one -/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSpectralQuotientPolynormableSec3

variable {F : Type*} [Field F] [NumberField F]
variable (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hI" => (neg_nonpos.mpr hα).trans hα
local notation "W" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s
local notation "H₀" => spectralSobolevQuotient F a hI hs
local notation "A(" φ ")" => hardySobolevTestAction μ𝔽 m𝔽 (-α) α s hI hs φ
local notation "Aq(" φ ")" => spectralConvolution (F := F) a hI hs φ
local notation "M(" hc ")" => modulatedCutoffOperator m𝔽
  ((μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (logIdeleClassNorm F g))) hc
local notation "band(" R ", " ε ")" => (0 < (R : ℝ)⁻¹ + ε ∧ R⁻¹ + ε < R - ε)

variable {Λ ε : ℝ} {ρ : IdeleClassGroup (𝓞 F) F → ℝ}

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). On a strip of width zero
at order at most one, quotient convolution is nuclear.
Deviation: This special case uses the density of theta at the strict endpoint cutoff of §10.2. -/
theorem spectralStripConvolution_nuclear_of_zero_width (hwidth : α = 0) (hs₁ : s ≤ 1)
    (φ : BruhatCompactSupport C𝔽) : IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ)) := by
  subst α
  have line (l : ℝ) (hl : l ≤ 0) (heq : l = 0) :
      IsNuclearOperator (E := spectralSobolevQuotient F a hl hs) (F := spectralSobolevQuotient F a hl hs)
        (spectralConvolution (F := F) a hl hs φ) := by
    subst l
    have hz (q : spectralSobolevQuotient F a hl hs) : q = 0 := by
      obtain ⟨v, rfl⟩ := (globalThetaSobolev F a hl hs).mkQ_surjective q
      apply (spectralSobolevQuotient_eq_zero a hl hs v).2
      rw [globalThetaSobolev_line_eq_top_of_le_one (F := F) a s hs hs₁]
      exact Submodule.mem_top
    have hA : spectralConvolution (F := F) a hl hs φ = 0 :=
      ContinuousLinearMap.ext fun _ ↦ hz _
    rw [hA]
    exact (nuclearEndomorphisms _).zero_mem
  exact line (-0) ((neg_nonpos.mpr hα).trans hα) neg_zero

namespace ConvolutionFactorization

open Function Set
open scoped Pointwise

section Abstract

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (a : BruhatStructuralPair G)
private abbrev kernel := (OrderDual.ofDual a.val.2).comap a.val.1.subtype
private abbrev stageMap : a.val.1 →* a.quotient := QuotientGroup.mk' (kernel a)

omit [MeasurableSpace G] [BorelSpace G] in
/-- The structural quotient map has compact kernel and is proper. -/
private theorem properStageMap : IsProperMap (stageMap a) := by
  let H := a.val.1
  let K := OrderDual.ofDual a.val.2
  have hK : IsCompact (K : Set G) := (lcaDualAnnihilator_annihilator K a.property.2.2.1.1) ▸
    isCompact_lcaDualAnnihilator (lcaAnnihilator K) a.property.2.2.1.2.1
  have hc : IsCompact (kernel a : Set a.val.1) :=
    (H.isClosed_of_isOpen a.property.1).isClosedEmbedding_subtypeVal.isCompact_preimage hK
  refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨QuotientGroup.continuous_mk, QuotientGroup.isClosedMap_coe hc, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (kernel a) y
  change IsCompact (QuotientGroup.mk ⁻¹' {QuotientGroup.mk x})
  rw [← image_singleton, QuotientGroup.preimage_image_mk_eq_mul]
  exact isCompact_singleton.mul hc

open Classical in
private def lift (f : a.quotient → ℂ) (x : G) : ℂ :=
  if hx : x ∈ a.val.1 then f (stageMap a ⟨x, hx⟩) else 0

private abbrev onStage (e : ElementaryLCAPresentation a.quotient) (f : SchwartzBruhatStage e)
    (q : a.quotient) := f (Multiplicative.toAdd (e.equiv q))

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem lift_stage (e : ElementaryLCAPresentation a.quotient) (f : SchwartzBruhatStage e) :
    lift a (onStage a e f) = schwartzBruhatStageRealization a e f := by
  funext x
  rw [schwartzBruhatStageRealization_apply]
  rfl

private theorem compact_lift {f : a.quotient → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (lift a f) := by
  classical
  let C := tsupport f
  have hc : IsCompact ((stageMap a) ⁻¹' C) := (properStageMap a).isCompact_preimage hf
  apply HasCompactSupport.intro (hc.image continuous_subtype_val)
  intro x hx
  by_cases h : x ∈ a.val.1
  · rw [lift, dite_eq_left h]
    apply image_eq_zero_of_notMem_tsupport
    exact fun he ↦ hx ⟨⟨x, h⟩, he, rfl⟩
  · rw [lift, dite_eq_right h]

private theorem compact_down {f : a.quotient → ℂ} (hf : HasCompactSupport (lift a f)) :
    HasCompactSupport f := by
  classical
  let C := tsupport (lift a f)
  have hc : IsCompact ((a.val.1).subtype ⁻¹' C) :=
    (a.val.1.isClosed_of_isOpen a.property.1).isClosedEmbedding_subtypeVal.isCompact_preimage hf
  apply HasCompactSupport.intro (hc.image (properStageMap a).continuous)
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (kernel a) q
  have hx : x.val ∉ C := fun he ↦ hq ⟨x, he, rfl⟩
  have he : lift a f x.val = 0 := image_eq_zero_of_notMem_tsupport hx
  rw [lift, dite_eq_left x.property] at he
  exact he

/-- A compactly supported function in the elementary Schwartz stage gives a compact Bruhat test. -/
private theorem stageTest (e : ElementaryLCAPresentation a.quotient) (u : SchwartzBruhatStage e)
    (hu : HasCompactSupport (onStage a e u)) :
    ∃ v : BruhatCompactSupport G, v.val = lift a (onStage a e u) := by
  have hc := compact_lift a hu
  rw [lift_stage] at hc
  let C : TopologicalSpace.Compacts G := ⟨_, hc⟩
  have hm := (mem_bruhatCompactSupportStage_iff a e C u).mpr (Subset.rfl)
  exact ⟨bruhatCompactSupportStageInclusion a e C ⟨u, hm⟩, (lift_stage a e u).symm⟩

private abbrev sourceMeasure (μ : Measure G) := μ.comap a.val.1.subtype
private abbrev quotientMeasure (μ : Measure G) : @Measure a.quotient (borel _) :=
  @Measure.map _ _ _ (borel _) (stageMap a) (sourceMeasure a μ)

/-- Restrict Haar measure to the open subgroup, then push it through the compact-kernel quotient. -/
private theorem quotientHaar (μ : Measure G) [μ.IsHaarMeasure] :
    letI : MeasurableSpace a.quotient := borel _
    (quotientMeasure a μ).IsHaarMeasure := by
  let : MeasurableSpace a.quotient := borel _
  let : BorelSpace a.quotient := ⟨rfl⟩
  let : LocallyCompactSpace a.val.1 := a.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let : LocallyCompactSpace a.quotient := QuotientGroup.instLocallyCompactSpace (kernel a)
  let : T1Space a.quotient := QuotientGroup.t1Space_iff.mpr
    (a.property.2.2.1.1.preimage continuous_subtype_val)
  let : (sourceMeasure a μ).IsHaarMeasure := Measure.IsHaarMeasure.comap
    (mH := ContinuousMul.measurableMul) μ (f := a.val.1.subtype) a.property.1.isOpenEmbedding_subtypeVal
  exact Measure.isHaarMeasure_map (sourceMeasure a μ) (stageMap a) (properStageMap a).continuous
    (QuotientGroup.mk'_surjective _) (isProperMap_iff_tendsto_cocompact.mp (properStageMap a)).2

/-- Pullback followed by zero extension intertwines the two convolutions for this choice of Haar measure. -/
private theorem lift_conv (μ : Measure G) (f g : a.quotient → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    letI : MeasurableSpace a.quotient := borel _
    lift a (lcaConvolution (quotientMeasure a μ) f g) = lcaConvolution μ (lift a f) (lift a g) := by
  classical
  let : MeasurableSpace a.quotient := borel _
  let : BorelSpace a.quotient := ⟨rfl⟩
  funext x
  by_cases hx : x ∈ a.val.1
  · let x' : a.val.1 := ⟨x, hx⟩
    rw [lift, dite_eq_left hx]
    unfold lcaConvolution
    let p (y : a.quotient) := f y * g (y⁻¹ * stageMap a x')
    have hpc : Continuous p := hf.mul (hg.comp (continuous_inv.mul continuous_const))
    change ∫ y, p y ∂((sourceMeasure a μ).map (stageMap a)) = _
    rw [MeasureTheory.integral_map (properStageMap a).continuous.measurable.aemeasurable
      hpc.aestronglyMeasurable]
    let P (y : G) := lift a f y * lift a g (y⁻¹ * x)
    have he : (∫ y, P y ∂μ) = ∫ y in (a.val.1 : Set G), P y ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
        change y ∉ a.val.1 at hy
        change lift a f y * _ = 0
        rw [lift, dite_eq_right hy, zero_mul]).symm
    change _ = ∫ y, P y ∂μ
    rw [he, ← integral_subtype_comap a.property.1.measurableSet]
    apply integral_congr_ae
    filter_upwards with y
    have hyx : y.val⁻¹ * x ∈ a.val.1 := a.val.1.mul_mem (a.val.1.inv_mem y.property) hx
    change f (stageMap a y) * g ((stageMap a y)⁻¹ * stageMap a x') = P y.val
    simp only [P, lift, dite_eq_left y.property, dite_eq_left hyx]
    congr 2
  · rw [lift, dite_eq_right hx, lcaConvolution]
    suffices h : (fun y ↦ lift a f y * lift a g (y⁻¹ * x)) = 0 by simp [h]
    funext y
    by_cases hy : y ∈ a.val.1
    · have hz : y⁻¹ * x ∉ a.val.1 := fun hz ↦ hx (by simpa using a.val.1.mul_mem hy hz)
      simp [lift, hz]
    · simp [lift, hy]

/-- The scalar input concerns compactly supported functions of elementary coordinates alone. -/
private def ElementaryFactorization {Q : Type*} [CommGroup Q] [TopologicalSpace Q]
    (e : ElementaryLCAPresentation Q) (ν : @Measure Q (borel _)) : Prop :=
  letI : MeasurableSpace Q := borel _
  let V (f : SchwartzBruhatStage e) (x : Q) := f (Multiplicative.toAdd (e.equiv x))
  ∀ f : SchwartzBruhatStage e, HasCompactSupport (V f) →
    V f ∈ AddSubmonoid.closure {θ : Q → ℂ | ∃ u v : SchwartzBruhatStage e,
      HasCompactSupport (V u) ∧ HasCompactSupport (V v) ∧ θ = lcaConvolution ν (V u) (V v)}

/-- Finite sums of convolutions of elementary test functions lift to the original group. -/
private theorem stage_descent [SecondCountableTopology G] (μ : Measure G) [μ.IsHaarMeasure]
    (e : ElementaryLCAPresentation a.quotient) (hdm : ElementaryFactorization e (quotientMeasure a μ))
    (f : SchwartzBruhatStage e) (φ : BruhatCompactSupport G)
    (hφ : φ.val = schwartzBruhatStageRealization a e f) :
    φ ∈ AddSubmonoid.closure {θ : BruhatCompactSupport G |
      ∃ u v : BruhatCompactSupport G, θ.val = lcaConvolution μ u.val v.val} := by
  classical
  let : MeasurableSpace a.quotient := borel _
  let : BorelSpace a.quotient := ⟨rfl⟩
  let D := AddSubmonoid.closure {θ : BruhatCompactSupport G |
      ∃ u v : BruhatCompactSupport G, θ.val = lcaConvolution μ u.val v.val}
  have he : φ.val = lift a (onStage a e f) := hφ.trans (lift_stage a e f).symm
  have hc : HasCompactSupport (onStage a e f) := compact_down a (he ▸ φ.property.2)
  have hbase := hdm f hc
  let P (h : a.quotient → ℂ) := ∃ t ∈ D, t.val = lift a h
  have ht : P (onStage a e f) := by
    apply AddSubmonoid.closure_induction (motive := fun h _ ↦ P h) _ _ _ hbase
    · intro h hh
      obtain ⟨u, v, hu, hv, rfl⟩ := hh
      obtain ⟨s, hs⟩ := stageTest a e u hu
      obtain ⟨t, ht⟩ := stageTest a e v hv
      have H : lift a (lcaConvolution (quotientMeasure a μ) (onStage a e u) (onStage a e v)) =
          lcaConvolution μ s.val t.val := by
        rw [hs, ht]
        exact lift_conv a μ _ _ ((elementarySchwartz_continuous u).comp e.equiv.continuous)
          ((elementarySchwartz_continuous v).comp e.equiv.continuous)
      let ρ : G →* (ℂ →L[ℂ] ℂ) := 1
      have hρ : Continuous (fun p : G × ℂ ↦ ρ p.1 p.2) := continuous_snd
      obtain ⟨k, hk, _⟩ := bruhatRegularizedAction_convolution μ ρ hρ s t
      exact ⟨k, AddSubmonoid.subset_closure ⟨s, t, hk⟩, hk.trans H.symm⟩
    · refine ⟨0, D.zero_mem, funext fun x ↦ ?_⟩
      by_cases hx : x ∈ a.val.1 <;> simp [lift, hx] <;> rfl
    · intro h g _ _ ih ig
      obtain ⟨u, hu, heu⟩ := ih
      obtain ⟨v, hv, hev⟩ := ig
      refine ⟨u + v, D.add_mem hu hv, funext (fun x ↦ ?_)⟩
      change u.val x + v.val x = _
      rw [heu, hev]
      by_cases hx : x ∈ a.val.1 <;> simp [lift, hx]
      rfl
  obtain ⟨t, ht, het⟩ := ht
  exact (show φ = t from Subtype.ext (he.trans het.symm)) ▸ ht

end Abstract

section Adeles

universe u
variable {K₀ : Type u} [Field K₀] [NumberField K₀]
local notation "C₀" => IdeleClassGroup (𝓞 K₀) K₀

/-- Every compact Bruhat test on the idele class group is realized on one structural quotient. -/
private theorem adelic_factorization_of_elementary
    (h : ∀ (Q : Type u) [CommGroup Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
      (e : ElementaryLCAPresentation Q) (ν : @Measure Q (borel _)),
      letI : MeasurableSpace Q := borel _
      ν.IsHaarMeasure → ElementaryFactorization e ν) (φ : BruhatCompactSupport C₀) :
    φ ∈ AddSubmonoid.closure {θ : BruhatCompactSupport C₀ | ∃ u v : BruhatCompactSupport C₀,
      θ.val = lcaConvolution (ideleClassTamagawaMeasure K₀) u.val v.val} := by
  let m : C₀ →ₜ* ℝ≥0ˣ := continuousIdeleClassNorm K₀
  have hm : IsModulation (G := C₀) m := by
    change IsProperMap (ideleClassNorm K₀) ∧ ∃ g, ideleClassNorm K₀ g ≠ 1
    exact ⟨isProperMap_ideleClassNorm K₀, ideleClassNorm_ne_one (F := K₀)⟩
  have hs : Surjective m := (ideleGroup_quotient.{_, 0} K₀).2.2.2.2.2.2.2.2.2.1
  have hφ := bruhatCompactSupport_le_modulatedExponentialDecay (G := C₀) m ({0} : Set ℝ) hm hs φ.property
  rw [modulatedExponentialDecaySubmodule_singleton_zero] at hφ
  obtain ⟨a, e, f, hf⟩ := (mem_schwartzBruhatSubmodule_iff (G := C₀) φ.val).mp hφ
  exact stage_descent a (ideleClassTamagawaMeasure K₀) e (h _ e _ (quotientHaar a _)) f φ hf.symm

end Adeles

/-- A compactly supported function on the elementary group that is smooth on the cover of
every discrete fibre is an elementary Schwartz function. This repeats the private
`elementarySchwartz_of_compactSupport` of Appendix D, §1. -/
private theorem elementaryLieGroup_schwartz_of_compactSupport {m n r : ℕ} {F : Type}
    [AddCommGroup F] [Fintype F] [TopologicalSpace F] [DiscreteTopology F]
    {f : ElementaryLieGroup m n r F → ℂ}
    (hf : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun xt ↦ f (elementaryCover xt a b)))
    (hc : HasCompactSupport f) :
    f ∈ elementarySchwartzSubmodule m n r F := by
  classical
  refine ⟨hf, fun i ↦ ?_⟩
  let Em := EuclideanSpace ℝ (Fin m)
  let N := EuclideanSpace ℝ (Fin n)
  let T := Fin n → AddCircle (1 : ℝ)
  let Z := Fin r → ℤ
  let q (v : N) : T := fun j ↦ (v j : AddCircle (1 : ℝ))
  have hq : IsOpenQuotientMap q := (IsOpenQuotientMap.piMap
    (fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk)).comp
    (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap
  let lift (t : T) := hq.surjective.hasRightInverse.choose t
  have hl (t : T) : q (lift t) = t := hq.surjective.hasRightInverse.choose_spec t
  let d (y : ElementaryLieGroup m n r F) := elementaryPartial f i.2.1 i.2.2.1
    (y.1, lift y.2.1) y.2.2.1 y.2.2.2
  have hd (v : Em × N) (z : Z) (b : F) :
      d (elementaryCover v z b) = elementaryPartial f i.2.1 i.2.2.1 v z b := by
    apply (elementaryPartial_descends _ _ _ _ _ (hf z b)).2
    exact Prod.ext rfl (Prod.ext (hl (q v.2)) rfl)
  have hdc : Continuous d := by
    apply (Homeomorph.prodAssoc Em T (Z × F)).isQuotientMap.continuous_iff.mpr
    apply continuous_prod_of_discrete_right.mpr
    intro z
    apply (IsOpenQuotientMap.id.prodMap hq).continuous_comp_iff.mp
    exact ((elementaryPartial_descends _ _ _ _ _ (hf z.1 z.2)).1.continuous).congr
      (fun w ↦ (hd w z.1 z.2).symm)
  have hdz {y : ElementaryLieGroup m n r F} (hy : y ∉ tsupport f) : d y = 0 := by
    let v : Em × N := (y.1, lift y.2.1)
    let p (w : Em × N) := elementaryCover w y.2.2.1 y.2.2.2
    have hp : Continuous p := continuous_fst.prodMk ((hq.continuous.comp continuous_snd).prodMk continuous_const)
    have hpv : p v = y := Prod.ext rfl (Prod.ext (hl y.2.1) rfl)
    have hv : v ∉ tsupport (f ∘ p) := fun hv ↦ hy (hpv ▸ tsupport_comp_subset_preimage f hp hv)
    have h0 (j : ℕ) : iteratedFDeriv ℝ j (f ∘ p) v = 0 := by
      by_contra hn
      exact hv (support_iteratedFDeriv_subset j hn)
    dsimp only [d, elementaryPartial]
    change (iteratedFDeriv ℝ _ (f ∘ p) v) _ = 0
    rw [h0]
    rfl
  let w (y : ElementaryLieGroup m n r F) : ℂ :=
    ((∏ j, (y.1 j : ℂ) ^ i.1 j) * (∏ j, (y.2.2.1 j : ℂ) ^ i.2.2.2 j)) * d y
  have hw : Continuous w := by
    apply Continuous.mul _ hdc
    apply Continuous.mul
    · fun_prop
    · exact (continuous_of_discreteTopology (f := fun z : Z ↦ ∏ j, (z j : ℂ) ^ i.2.2.2 j)).comp
        (continuous_fst.comp (continuous_snd.comp continuous_snd))
  have hwK : HasCompactSupport w := HasCompactSupport.intro hc fun y hy ↦ by simp [w, hdz hy]
  obtain ⟨C,hC⟩ := hw.bounded_above_of_compact_support hwK
  apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
  refine iSup_le fun v ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  rw [ENNReal.coe_nnreal_eq]
  apply ENNReal.ofReal_le_ofReal
  have h := hC (elementaryCover v a b)
  dsimp only [w] at h
  rw [hd] at h
  exact h

/-- One-parameter Dixmier–Malliavin on the elementary group for a function supported on
one discrete fibre `d`: the two-term factorization `h = φ ⋆ᵥ h₁ + ψ ⋆ᵥ h`. The fibre is
lifted to `ℝᵐ × ℝⁿ`, where the function is periodic in the torus coordinates, and
`dixmierMalliavin_periodic_direction` applies. -/
private theorem elementaryLieGroup_direction_fibre {m n r : ℕ} {D : Type}
    [AddCommGroup D] [Fintype D] [TopologicalSpace D] [DiscreteTopology D]
    (h : ElementarySchwartz m n r D)
    (hh : HasCompactSupport (h : ElementaryLieGroup m n r D → ℂ))
    (v : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (d : (Fin r → ℤ) × D)
    (hd : ∀ g : ElementaryLieGroup m n r D, g.2.2 ≠ d → h g = 0) :
    ∃ (φ ψ : ℝ → ℂ) (h₁ : ElementarySchwartz m n r D),
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ ContDiff ℝ (⊤ : ℕ∞) ψ ∧
      HasCompactSupport ψ ∧ HasCompactSupport (h₁ : ElementaryLieGroup m n r D → ℂ) ∧
      ∀ x, h x = (∫ t : ℝ, φ t * h₁ (x + elementaryCover (t • v) 0 0)) +
        ∫ t : ℝ, ψ t * h (x + elementaryCover (t • v) 0 0) := by
  classical
  let G := ElementaryLieGroup m n r D
  let e₁ := EuclideanSpace.equiv (Fin m) ℝ
  let e₂ := EuclideanSpace.equiv (Fin n) ℝ
  let P : ((Fin m → ℝ) × (Fin n → ℝ)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) := e₁.symm.prodCongr e₂.symm
  let Fh : (Fin m → ℝ) × (Fin n → ℝ) → ℂ := fun w ↦ h (elementaryCover (P w) d.1 d.2)
  have hFh : ContDiff ℝ (⊤ : ℕ∞) Fh := (h.property.1 d.1 d.2).comp P.contDiff
  have hint (k : ℤ) : ((k : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k, by simp⟩
  have hcover (x : Fin m → ℝ) (t : Fin n → ℝ) (k : Fin n → ℤ) (c : (Fin r → ℤ) × D) :
      (elementaryCover (P (x, fun j ↦ t j + k j)) c.1 c.2 : G) =
        elementaryCover (P (x, t)) c.1 c.2 := by
    refine Prod.ext rfl (Prod.ext (funext fun j ↦ ?_) rfl)
    change ((t j + k j : ℝ) : AddCircle (1 : ℝ)) = (t j : AddCircle (1 : ℝ))
    rw [AddCircle.coe_add, hint, add_zero]
  let K : Set (Fin m → ℝ) := (fun g : G ↦ e₁ g.1) '' tsupport (h : G → ℂ)
  have hK : IsCompact K := hh.isCompact.image (e₁.continuous.comp continuous_fst)
  have hFK (x : Fin m → ℝ) (t : Fin n → ℝ) (hx : x ∉ K) : Fh (x, t) = 0 := by
    by_contra h0
    exact hx ⟨_, subset_tsupport _ h0, e₁.apply_symm_apply x⟩
  obtain ⟨F₁, φ, ψ, hF₁, hper₁, hF₁K, hφ, hφc, hψ, hψc, heq⟩ :=
    dixmierMalliavin_periodic_direction (e₁ v.1) (e₂ v.2) Fh hFh
      (fun x t k ↦ congrArg h (hcover x t k d)) K hK hFK
  choose sec hsec using fun z : AddCircle (1 : ℝ) ↦ QuotientAddGroup.mk_surjective z
  let h₁f : G → ℂ := fun g ↦ if g.2.2 = d then F₁ (e₁ g.1, fun j ↦ sec (g.2.1 j)) else 0
  have star (w : (Fin m → ℝ) × (Fin n → ℝ)) (c : (Fin r → ℤ) × D) :
      h₁f (elementaryCover (P w) c.1 c.2) = if c = d then F₁ w else 0 := by
    by_cases hc : c = d
    · have hk : ∀ j, ∃ k : ℤ, sec ((w.2 j : ℝ) : AddCircle (1 : ℝ)) = w.2 j + k := fun j ↦ by
        have h0 : ((sec ((w.2 j : ℝ) : AddCircle (1 : ℝ)) - w.2 j : ℝ) :
            AddCircle (1 : ℝ)) = 0 := by
          rw [AddCircle.coe_sub]
          exact sub_eq_zero.mpr (hsec _)
        obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h0
        exact ⟨k, by simp at hk; linarith⟩
      choose k hk using hk
      have e : h₁f (elementaryCover (P w) c.1 c.2) = F₁ (w.1, fun j ↦ w.2 j + k j) := by
        change (if (c.1, c.2) = d then
          F₁ (e₁ (e₁.symm w.1), fun j ↦ sec ((w.2 j : ℝ) : AddCircle (1 : ℝ))) else 0) = _
        rw [ite_eq_left (show (c.1, c.2) = d from hc), e₁.apply_symm_apply]
        exact congrArg F₁ (Prod.ext rfl (funext hk))
      rw [e, hper₁, ite_eq_left hc]
    · change (if (c.1, c.2) = d then _ else 0) = _
      rw [ite_eq_right (show ¬(c.1, c.2) = d from hc), ite_eq_right hc]
  have hsm (a : Fin r → ℤ) (b : D) :
      ContDiff ℝ (⊤ : ℕ∞) (fun xt ↦ h₁f (elementaryCover xt a b)) := by
    have e : (fun xt ↦ h₁f (elementaryCover xt a b)) =
        fun xt ↦ if (a, b) = d then F₁ (P.symm xt) else 0 := funext fun xt ↦ by
      have := star (P.symm xt) (a, b)
      rwa [P.apply_symm_apply] at this
    rw [e]
    by_cases hc : (a, b) = d
    · simp only [ite_eq_left hc]
      exact hF₁.comp P.symm.contDiff
    · simp only [ite_eq_right hc]
      exact contDiff_const
  have hh₁c : HasCompactSupport h₁f := by
    have hKc : IsCompact ((e₁.symm '' K) ×ˢ ((univ : Set (Fin n → AddCircle (1 : ℝ))) ×ˢ
        ({d} : Set ((Fin r → ℤ) × D)))) :=
      (hK.image e₁.symm.continuous).prod (isCompact_univ.prod isCompact_singleton)
    refine HasCompactSupport.intro hKc fun g hg ↦ ?_
    by_cases hc : g.2.2 = d
    · have hx : e₁ g.1 ∉ K := fun hx ↦
        hg ⟨⟨_, hx, e₁.symm_apply_apply g.1⟩, mem_univ _, hc⟩
      change (if g.2.2 = d then _ else 0) = 0
      rw [ite_eq_left hc]
      exact hF₁K _ _ hx
    · change (if g.2.2 = d then _ else 0) = 0
      rw [ite_eq_right hc]
  let h₁ : ElementarySchwartz m n r D :=
    ⟨h₁f, elementaryLieGroup_schwartz_of_compactSupport hsm hh₁c⟩
  refine ⟨φ, ψ, h₁, hφ, hφc, hψ, hψc, hh₁c, fun x ↦ ?_⟩
  obtain ⟨t₀, ht₀⟩ := elementaryCover_surjective x.2.2.1 x.2.2.2 x.1 x.2.1
  let w : (Fin m → ℝ) × (Fin n → ℝ) := P.symm (x.1, t₀)
  let c : (Fin r → ℤ) × D := x.2.2
  have hx : x = elementaryCover (P w) c.1 c.2 := by
    rw [P.apply_symm_apply]
    exact ht₀.symm
  have hshift (t : ℝ) : x + elementaryCover (t • v) 0 0 =
      elementaryCover (P (w + t • (e₁ v.1, e₂ v.2))) c.1 c.2 := by
    have hv : P (e₁ v.1, e₂ v.2) = v :=
      Prod.ext (e₁.symm_apply_apply v.1) (e₂.symm_apply_apply v.2)
    rw [map_add, map_smul, hv, hx]
    refine Prod.ext rfl (Prod.ext (funext fun j ↦ ?_) (Prod.ext (add_zero _) (add_zero _)))
    exact (AddCircle.coe_add (1 : ℝ) _ _).symm
  have h1 (t : ℝ) : h₁ (x + elementaryCover (t • v) 0 0) =
      if c = d then F₁ (w + t • (e₁ v.1, e₂ v.2)) else 0 := by
    rw [hshift]
    exact star _ c
  by_cases hc : c = d
  · have h2 (t : ℝ) : h (x + elementaryCover (t • v) 0 0) = Fh (w + t • (e₁ v.1, e₂ v.2)) := by
      rw [hshift, hc]
    have h3 : h x = Fh w := by rw [hx, hc]
    simp only [h1, h2, h3, ite_eq_left hc]
    exact heq w
  · have h2 (t : ℝ) : h (x + elementaryCover (t • v) 0 0) = 0 := by
      rw [hshift]
      exact hd _ hc
    have h3 : h x = 0 := hd x hc
    simp only [h1, h2, h3, ite_eq_right hc, mul_zero, integral_zero, add_zero]

/-- Dixmier–Malliavin for one one-parameter subgroup of the elementary group
`ℝᵐ × (ℝ/ℤ)ⁿ × ℤʳ × D`. For a vector `v` of the covering space `ℝᵐ × ℝⁿ`, each compactly
supported elementary Schwartz function `h` is a finite sum of functions
`x ↦ ∫ φ t * h₁ (x + elementaryCover (t • v) 0 0) dt` with `φ` a test function on the line
and `h₁` a compactly supported elementary Schwartz function (J. Dixmier, P. Malliavin, Bull.
Sci. Math. (2) 102 (1978), 307–330, §2 and Théorème 3.1 for a one-parameter group).
The function is split over the finitely many discrete fibres that meet its support, and
`elementaryLieGroup_direction_fibre` applies on each fibre. -/
private theorem elementaryLieGroup_direction_factorization {m n r : ℕ} {D : Type}
    [AddCommGroup D] [Fintype D] [TopologicalSpace D] [DiscreteTopology D]
    (h : ElementarySchwartz m n r D)
    (hh : HasCompactSupport (h : ElementaryLieGroup m n r D → ℂ))
    (v : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :
    (h : ElementaryLieGroup m n r D → ℂ) ∈ AddSubmonoid.closure
      {θ : ElementaryLieGroup m n r D → ℂ | ∃ (φ : ℝ → ℂ) (h₁ : ElementarySchwartz m n r D),
        ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
        HasCompactSupport (h₁ : ElementaryLieGroup m n r D → ℂ) ∧
        θ = fun x ↦ ∫ t : ℝ, φ t * h₁ (x + elementaryCover (t • v) 0 0)} := by
  classical
  let G := ElementaryLieGroup m n r D
  have hfin : ((fun g : G ↦ g.2.2) '' tsupport (h : G → ℂ)).Finite :=
    (hh.isCompact.image (continuous_snd.comp continuous_snd)).finite_of_discrete
  let hf (d : (Fin r → ℤ) × D) : G → ℂ := fun g ↦ if g.2.2 = d then h g else 0
  have hfs (d : (Fin r → ℤ) × D) (a : Fin r → ℤ) (b : D) :
      ContDiff ℝ (⊤ : ℕ∞) (fun xt ↦ hf d (elementaryCover xt a b)) := by
    by_cases hc : (a, b) = d
    · have e : (fun xt ↦ hf d (elementaryCover xt a b)) = fun xt ↦ h (elementaryCover xt a b) :=
        funext fun xt ↦ ite_eq_left hc
      rw [e]
      exact h.property.1 a b
    · have e : (fun xt ↦ hf d (elementaryCover xt a b)) = fun _ ↦ 0 :=
        funext fun xt ↦ ite_eq_right hc
      rw [e]
      exact contDiff_const
  have hfc (d : (Fin r → ℤ) × D) : HasCompactSupport (hf d) :=
    hh.mono fun g hg h0 ↦ hg (by
      change (if g.2.2 = d then h g else 0) = 0
      rw [h0, ite_self])
  let hd (d : (Fin r → ℤ) × D) : ElementarySchwartz m n r D :=
    ⟨hf d, elementaryLieGroup_schwartz_of_compactSupport (hfs d) (hfc d)⟩
  have hsum : (h : G → ℂ) = ∑ d ∈ hfin.toFinset, (hd d : G → ℂ) := by
    funext g
    rw [Finset.sum_apply]
    change h g = ∑ d ∈ hfin.toFinset, if g.2.2 = d then h g else 0
    rw [Finset.sum_ite_eq hfin.toFinset g.2.2 (fun _ ↦ h g)]
    split_ifs with hg
    · rfl
    · by_contra h0
      exact hg (hfin.mem_toFinset.mpr ⟨g, subset_tsupport _ h0, rfl⟩)
  rw [hsum]
  refine sum_mem fun d _ ↦ ?_
  obtain ⟨φ, ψ, h₁, hφ, hφc, hψ, hψc, hh₁, heq⟩ :=
    elementaryLieGroup_direction_fibre (hd d) (hfc d) v d (fun g hg ↦ ite_eq_right hg)
  rw [show ((hd d : ElementarySchwartz m n r D) : G → ℂ) =
    (fun x ↦ ∫ t : ℝ, φ t * h₁ (x + elementaryCover (t • v) 0 0)) +
      (fun x ↦ ∫ t : ℝ, ψ t * (hd d) (x + elementaryCover (t • v) 0 0)) from funext heq]
  exact add_mem (AddSubmonoid.subset_closure ⟨φ, h₁, hφ, hφc, hh₁, rfl⟩)
    (AddSubmonoid.subset_closure ⟨ψ, hd d, hψ, hψc, hfc d, rfl⟩)

/-- Dixmier–Malliavin for the translation action of the covering vector space
`ℝᵐ × ℝⁿ` on the elementary group `ℝᵐ × (ℝ/ℤ)ⁿ × ℤʳ × D`. Each compactly supported elementary
Schwartz function `f` is a finite sum of smoothed functions
`x ↦ ∫ Φ w * h (x + elementaryCover w 0 0) dw`, with `Φ` smooth of compact support on the
cover and `h` a compactly supported elementary Schwartz function. No Haar measure of the
group occurs: the integral is over the covering vector space. -/
private theorem elementaryLieGroup_cover_factorization {m n r : ℕ} {D : Type}
    [AddCommGroup D] [Fintype D] [TopologicalSpace D] [DiscreteTopology D]
    (f : ElementarySchwartz m n r D)
    (hf : HasCompactSupport (f : ElementaryLieGroup m n r D → ℂ)) :
    (f : ElementaryLieGroup m n r D → ℂ) ∈ AddSubmonoid.closure
      {θ : ElementaryLieGroup m n r D → ℂ |
        ∃ (Φ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℂ)
          (h : ElementarySchwartz m n r D), ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
          HasCompactSupport (h : ElementaryLieGroup m n r D → ℂ) ∧
          θ = fun x ↦ ∫ w, Φ w * h (x + elementaryCover w 0 0)} := by
  let G := ElementaryLieGroup m n r D
  let Wc := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let γ : Wc →+ G := elementaryCoverZeroHom
  have hγ : Continuous γ := elementaryCoverZeroHom_continuous_isOpenMap.1
  let 𝒜 : Set (G → ℂ) :=
    {θ | ∃ h : ElementarySchwartz m n r D, HasCompactSupport (h : G → ℂ) ∧ θ = h}
  have : (volume : Measure Wc).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have key := dixmierMalliavin_action (volume : Measure Wc) 𝒜 (fun w x ↦ x + γ w)
    (fun x ↦ by simp) (fun w w' x ↦ by simp only [map_add, add_assoc])
    (by
      rintro _ ⟨h, -, rfl⟩ x
      exact (elementarySchwartz_continuous h).comp (continuous_const.add hγ))
    (by
      rintro _ ⟨h, hh, rfl⟩ v
      refine AddSubmonoid.closure_mono ?_ (elementaryLieGroup_direction_factorization h hh v)
      rintro θ ⟨φ, h₁, hφ, hφc, hh₁, rfl⟩
      exact ⟨φ, h₁, ⟨h₁, hh₁, rfl⟩, hφ, hφc, rfl⟩)
    f ⟨f, hf, rfl⟩
  refine AddSubmonoid.closure_mono ?_ key
  rintro θ ⟨Φ, _, ⟨h, hh, rfl⟩, hΦ, hΦc, rfl⟩
  exact ⟨Φ, h, hΦ, hΦc, hh, rfl⟩

/-- The cover does not see integer translations of the torus coordinates. -/
private theorem elementaryCover_add_int {m n r : ℕ} {D : Type} [AddCommGroup D]
    (w : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (z : Fin n → ℤ)
    (a : Fin r → ℤ) (b : D) :
    (elementaryCover (w + (0, WithLp.toLp 2 fun j ↦ (z j : ℝ))) a b :
      ElementaryLieGroup m n r D) = elementaryCover w a b := by
  refine Prod.ext (add_zero w.1) (Prod.ext (funext fun j ↦ ?_) rfl)
  have hint : ((z j : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨z j, by simp⟩
  change ((w.2 j + (z j : ℝ) : ℝ) : AddCircle (1 : ℝ)) = (w.2 j : AddCircle (1 : ℝ))
  rw [AddCircle.coe_add, hint, add_zero]

/-- The sum of a smooth compactly supported function on the cover `ℝᵐ × ℝⁿ` over the fibres
of the covering map `w ↦ elementaryCover w 0 0` is a compactly supported elementary Schwartz
function, carried by the identity component. -/
private theorem elementaryLieGroup_cover_periodization {m n r : ℕ} {D : Type}
    [AddCommGroup D] [Fintype D] [TopologicalSpace D] [DiscreteTopology D]
    (Φ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) :
    ∃ k : ElementarySchwartz m n r D,
      HasCompactSupport (k : ElementaryLieGroup m n r D → ℂ) ∧
      (∀ g : ElementaryLieGroup m n r D, g.2.2 ≠ 0 → k g = 0) ∧
      ∀ w, k (elementaryCover w 0 0) =
        ∑' z : Fin n → ℤ, Φ (w + (0, WithLp.toLp 2 fun j ↦ (z j : ℝ))) := by
  classical
  let G := ElementaryLieGroup m n r D
  let Wc := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let γ : Wc →+ G := elementaryCoverZeroHom
  have hγ : Continuous γ := elementaryCoverZeroHom_continuous_isOpenMap.1
  let ζ : (Fin n → ℤ) → Wc := fun z ↦ (0, WithLp.toLp 2 fun j ↦ (z j : ℝ))
  have hζadd (z z' : Fin n → ℤ) : ζ (z + z') = ζ z + ζ z' := by
    refine Prod.ext (add_zero _).symm ?_
    ext j
    exact Int.cast_add (z j) (z' j)
  have hζfin (R : ℝ) : {z | ‖ζ z‖ ≤ R}.Finite := by
    refine (Set.Finite.pi fun _ : Fin n ↦ Set.finite_Icc (-⌈R⌉) ⌈R⌉).subset fun z hz ↦ ?_
    have hj (j : Fin n) : |(z j : ℝ)| ≤ R := by
      have h1 : ‖(ζ z).2 j‖ ≤ ‖(ζ z).2‖ := PiLp.norm_apply_le _ j
      have h2 : ‖(ζ z).2‖ ≤ ‖ζ z‖ := norm_snd_le _
      exact (h1.trans h2).trans hz
    refine fun j _ ↦ ⟨?_, ?_⟩
    · have h1 := (abs_le.mp (hj j)).1
      have h2 : ((-⌈R⌉ : ℤ) : ℝ) ≤ (z j : ℝ) := by
        push_cast
        linarith [Int.le_ceil R]
      exact_mod_cast h2
    · have h1 := (abs_le.mp (hj j)).2
      have h2 : (z j : ℝ) ≤ ((⌈R⌉ : ℤ) : ℝ) := by linarith [Int.le_ceil R]
      exact_mod_cast h2
  let S : Wc → ℂ := fun w ↦ ∑' z, Φ (w + ζ z)
  have hS : ContDiff ℝ (⊤ : ℕ∞) S := contDiff_tsum_translates ζ hζfin Φ hΦ hΦc
  have hSper (w : Wc) (z₀ : Fin n → ℤ) : S (w + ζ z₀) = S w := by
    change ∑' z, Φ (w + ζ z₀ + ζ z) = ∑' z, Φ (w + ζ z)
    rw [← (Equiv.addLeft z₀).tsum_eq (fun z ↦ Φ (w + ζ z))]
    refine tsum_congr fun z ↦ ?_
    simp only [Equiv.coe_addLeft, hζadd, add_assoc]
  choose sec hsec using fun z : AddCircle (1 : ℝ) ↦ QuotientAddGroup.mk_surjective z
  let kf : G → ℂ := fun g ↦
    if g.2.2 = 0 then S (g.1, WithLp.toLp 2 fun j ↦ sec (g.2.1 j)) else 0
  have star (w : Wc) (c : (Fin r → ℤ) × D) :
      kf (elementaryCover w c.1 c.2) = if c = 0 then S w else 0 := by
    by_cases hc : c = 0
    · have hk : ∀ j, ∃ k : ℤ, sec ((w.2 j : ℝ) : AddCircle (1 : ℝ)) = w.2 j + k := fun j ↦ by
        have h0 : ((sec ((w.2 j : ℝ) : AddCircle (1 : ℝ)) - w.2 j : ℝ) :
            AddCircle (1 : ℝ)) = 0 := by
          rw [AddCircle.coe_sub]
          exact sub_eq_zero.mpr (hsec _)
        obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h0
        exact ⟨k, by simp at hk; linarith⟩
      choose k hk using hk
      have e : ((w.1, WithLp.toLp 2 fun j ↦ sec ((w.2 j : ℝ) : AddCircle (1 : ℝ))) : Wc) =
          w + ζ k := by
        refine Prod.ext (add_zero _).symm ?_
        ext j
        exact hk j
      change (if (c.1, c.2) = 0 then
        S (w.1, WithLp.toLp 2 fun j ↦ sec ((w.2 j : ℝ) : AddCircle (1 : ℝ))) else 0) = _
      rw [ite_eq_left (show (c.1, c.2) = 0 from hc), e, hSper, ite_eq_left hc]
    · change (if (c.1, c.2) = 0 then _ else 0) = _
      rw [ite_eq_right (show ¬(c.1, c.2) = 0 from hc), ite_eq_right hc]
  have hsm (a : Fin r → ℤ) (b : D) :
      ContDiff ℝ (⊤ : ℕ∞) (fun xt ↦ kf (elementaryCover xt a b)) := by
    have e : (fun xt ↦ kf (elementaryCover xt a b)) =
        fun xt ↦ if (a, b) = 0 then S xt else 0 := funext fun xt ↦ star xt (a, b)
    rw [e]
    by_cases hc : (a, b) = 0
    · simp only [ite_eq_left hc]
      exact hS
    · simp only [ite_eq_right hc]
      exact contDiff_const
  have hkc : HasCompactSupport kf := by
    refine HasCompactSupport.intro (hΦc.isCompact.image hγ) fun g hg ↦ ?_
    by_cases hc : g.2.2 = 0
    · let wg : Wc := (g.1, WithLp.toLp 2 fun j ↦ sec (g.2.1 j))
      have hwg : γ wg = g := Prod.ext rfl (Prod.ext (funext fun j ↦ hsec (g.2.1 j)) hc.symm)
      have hz : ∀ z, Φ (wg + ζ z) = 0 := fun z ↦ by
        by_contra h0
        exact hg ⟨wg + ζ z, subset_tsupport _ h0, (elementaryCover_add_int wg z 0 0).trans hwg⟩
      change (if g.2.2 = 0 then ∑' z, Φ (wg + ζ z) else 0) = 0
      rw [ite_eq_left hc, tsum_congr hz, tsum_zero]
    · change (if g.2.2 = 0 then _ else 0) = 0
      rw [ite_eq_right hc]
  refine ⟨⟨kf, elementaryLieGroup_schwartz_of_compactSupport hsm hkc⟩, hkc,
    fun g hg ↦ ite_eq_right hg, fun w ↦ ?_⟩
  exact (star w 0).trans (ite_eq_left rfl)

/-- Unfolding along the cover. For a Haar measure `μ` of the elementary group
`ℝᵐ × (ℝ/ℤ)ⁿ × ℤʳ × D` there is a constant `c > 0` such that, when a continuous function
`κ` carried by the identity component is the sum of a continuous compactly supported `Ψ`
over the fibres of the covering map `w ↦ elementaryCover w 0 0`, the integral of `κ` for `μ`
is `c` times the Lebesgue integral of `Ψ` over `ℝᵐ × ℝⁿ`.
The identity component `ℝᵐ × (ℝ/ℤ)ⁿ × 0` is an open subgroup, so `μ` restricts to a Haar
measure there, which is a multiple of the product of Lebesgue measure and the Haar measures
of the circles; `integral_eq_integral_of_tsum_int_translates` unfolds that product. -/
private theorem elementaryLieGroup_cover_unfolding {m n r : ℕ} {D : Type}
    [AddCommGroup D] [Fintype D] [TopologicalSpace D] [DiscreteTopology D]
    (μ : @Measure (ElementaryLieGroup m n r D) (borel _)) :
    letI : MeasurableSpace (ElementaryLieGroup m n r D) := borel _
    μ.IsAddHaarMeasure →
      ∃ c : ℝ, 0 < c ∧
        ∀ (Ψ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℂ)
          (κ : ElementaryLieGroup m n r D → ℂ), Continuous Ψ → HasCompactSupport Ψ →
          Continuous κ → (∀ g : ElementaryLieGroup m n r D, g.2.2 ≠ 0 → κ g = 0) →
          (∀ w, κ (elementaryCover w 0 0) =
            ∑' z : Fin n → ℤ, Ψ (w + (0, WithLp.toLp 2 fun j ↦ (z j : ℝ)))) →
          ∫ g, κ g ∂μ = (c : ℂ) * ∫ w, Ψ w := by
  intro hμ
  classical
  let G := ElementaryLieGroup m n r D
  let Wc := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let Hc := (Fin m → ℝ) × (Fin n → AddCircle (1 : ℝ))
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  let e₁ := EuclideanSpace.equiv (Fin m) ℝ
  let e₂ := EuclideanSpace.equiv (Fin n) ℝ
  let P : ((Fin m → ℝ) × (Fin n → ℝ)) ≃L[ℝ] Wc := e₁.symm.prodCongr e₂.symm
  let jh : Hc →+ G :=
    { toFun := fun p ↦ (e₁.symm p.1, p.2, 0, 0)
      map_zero' := Prod.ext (map_zero e₁.symm) rfl
      map_add' := fun p p' ↦ Prod.ext (map_add e₁.symm p.1 p'.1)
        (Prod.ext rfl (Prod.ext (add_zero 0).symm (add_zero 0).symm)) }
  have hjc : Continuous jh :=
    (e₁.symm.continuous.comp continuous_fst).prodMk (continuous_snd.prodMk continuous_const)
  have hji : Injective jh := fun p p' hpp ↦ Prod.ext
    (e₁.symm.injective (congrArg Prod.fst hpp)) (congrArg (fun g : G ↦ g.2.1) hpp)
  have hrange (g : G) (hg : g.2.2 = 0) : jh (e₁ g.1, g.2.1) = g :=
    Prod.ext (e₁.symm_apply_apply g.1) (Prod.ext rfl hg.symm)
  have hjo : IsOpenMap jh := fun U hU ↦ by
    have e : jh '' U = (fun g : G ↦ (e₁ g.1, g.2.1)) ⁻¹' U ∩ (fun g : G ↦ g.2.2) ⁻¹' {0} := by
      ext g
      constructor
      · rintro ⟨p, hp, rfl⟩
        refine ⟨?_, rfl⟩
        change (e₁ (e₁.symm p.1), p.2) ∈ U
        rwa [e₁.apply_symm_apply]
      · rintro ⟨hg1, hg2⟩
        exact ⟨_, hg1, hrange g hg2⟩
    rw [e]
    exact (hU.preimage ((e₁.continuous.comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd))).inter
      ((isOpen_discrete _).preimage (continuous_snd.comp continuous_snd))
  have hj : Topology.IsOpenEmbedding jh :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hjc hji hjo
  let μ₀ : Measure Hc := μ.comap jh
  have hμ₀ : μ₀.IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.comap (mH := ContinuousAdd.measurableAdd) μ hj
  have hvol : (volume : Measure Hc).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  let c := Measure.addHaarScalarFactor μ₀ (volume : Measure Hc)
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ₀ volume
  have hμc : μ₀ = c • (volume : Measure Hc) := Measure.isAddLeftInvariant_eq_smul μ₀ volume
  have hvolP : (volume : Measure ((Fin m → ℝ) × (Fin n → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hvolW : (volume : Measure Wc).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  let μP : Measure Wc := Measure.map P volume
  have hμP : μP.IsAddHaarMeasure := P.isAddHaarMeasure_map volume
  let aP := Measure.addHaarScalarFactor μP (volume : Measure Wc)
  have haP : 0 < aP := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μP volume
  have hμPa : μP = aP • (volume : Measure Wc) := Measure.isAddLeftInvariant_eq_smul μP volume
  refine ⟨(c : ℝ) * (aP : ℝ), mul_pos (NNReal.coe_pos.mpr hc) (NNReal.coe_pos.mpr haP),
    fun Ψ κ hΨ hΨc hκ hκ0 hfib ↦ ?_⟩
  have s1 : ∫ g, κ g ∂μ = ∫ p, κ (jh p) ∂μ₀ := by
    rw [← hj.measurableEmbedding.integral_map, hj.measurableEmbedding.map_comap]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg ↦ hκ0 g fun h0 ↦ ?_).symm
    exact hg ⟨_, hrange g h0⟩
  have s2 : ∫ p, κ (jh p) = ∫ w, Ψ (P w) := by
    refine integral_eq_integral_of_tsum_int_translates (fun w ↦ Ψ (P w))
      (hΨ.comp P.continuous) (hΨc.comp_homeomorph P.toHomeomorph) (fun p ↦ κ (jh p))
      (hκ.comp hjc) fun x t ↦ ?_
    change κ (elementaryCover (P (x, t)) 0 0) = _
    rw [hfib]
    exact tsum_congr fun z ↦ congrArg Ψ (Prod.ext (add_zero _) rfl)
  have s3 : ∫ w, Ψ (P w) = (aP : ℝ) * ∫ w, Ψ w := by
    have e : ∫ w, Ψ (P w) = ∫ w, Ψ w ∂μP := by
      change _ = ∫ w, Ψ w ∂(Measure.map P.toHomeomorph.toMeasurableEquiv volume)
      rw [integral_map_equiv]
      rfl
    rw [e, hμPa, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  rw [s1, hμc, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, s2, s3]
  push_cast
  ring

/-- The image under the covering homomorphism `w ↦ elementaryCover w 0 0` of a smooth
compactly supported density on `ℝᵐ × ℝⁿ` has a compactly supported elementary Schwartz
density `k` for any Haar measure `μ` of the elementary group: smoothing by `Φ` along the
cover is convolution with `k`. The density is a constant multiple of the sum of `Φ` over the
fibres of the cover, reflected. -/
private theorem elementaryLieGroup_cover_kernel {m n r : ℕ} {D : Type}
    [AddCommGroup D] [Fintype D] [TopologicalSpace D] [DiscreteTopology D]
    (μ : @Measure (ElementaryLieGroup m n r D) (borel _)) :
    letI : MeasurableSpace (ElementaryLieGroup m n r D) := borel _
    μ.IsAddHaarMeasure →
      ∀ Φ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
        ∃ k : ElementarySchwartz m n r D,
          HasCompactSupport (k : ElementaryLieGroup m n r D → ℂ) ∧
          ∀ h : ElementaryLieGroup m n r D → ℂ, Continuous h → ∀ x,
            ∫ y, k y * h (-y + x) ∂μ = ∫ w, Φ w * h (x + elementaryCover w 0 0) := by
  intro hμ Φ hΦ hΦc
  obtain ⟨c, hc, hunf⟩ := elementaryLieGroup_cover_unfolding μ hμ
  let G := ElementaryLieGroup m n r D
  let Wc := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let γ : Wc →+ G := elementaryCoverZeroHom
  have hγ : Continuous γ := elementaryCoverZeroHom_continuous_isOpenMap.1
  have : (volume : Measure Wc).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hΦn : HasCompactSupport (fun w : Wc ↦ Φ (-w)) := hΦc.comp_homeomorph (Homeomorph.neg Wc)
  obtain ⟨k₀, hk₀c, hk₀z, hk₀⟩ := elementaryLieGroup_cover_periodization (r := r) (D := D)
    (fun w ↦ Φ (-w)) (hΦ.comp contDiff_neg) hΦn
  have hcc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  refine ⟨(c : ℂ)⁻¹ • k₀, ?_, fun h hh x ↦ ?_⟩
  · exact hk₀c.mono fun g hg h0 ↦ hg (by
      change (c : ℂ)⁻¹ * k₀ g = 0
      rw [h0, mul_zero])
  · have key := hunf (fun w ↦ Φ (-w) * h (-(γ w) + x)) (fun g ↦ k₀ g * h (-g + x))
      ((hΦ.continuous.comp continuous_neg).mul (hh.comp ((hγ.neg).add continuous_const)))
      hΦn.mul_right
      ((elementarySchwartz_continuous k₀).mul (hh.comp (continuous_neg.add continuous_const)))
      (fun g hg ↦ by rw [hk₀z g hg, zero_mul])
      (fun w ↦ by
        rw [hk₀ w, ← tsum_mul_right]
        refine tsum_congr fun z ↦ ?_
        change _ = Φ (-(w + _)) * h (-(elementaryCover (w + _) 0 0) + x)
        rw [elementaryCover_add_int])
    have hneg : ∫ w : Wc, Φ (-w) * h (-(γ w) + x) = ∫ w : Wc, Φ w * h (x + γ w) := by
      rw [← integral_comp_neg_of_isAddHaarMeasure (volume : Measure Wc)
        (fun w : Wc ↦ Φ w * h (x + γ w))]
      refine integral_congr_ae (Eventually.of_forall fun w ↦ ?_)
      change Φ (-w) * h (-(γ w) + x) = Φ (-w) * h (x + γ (-w))
      rw [map_neg, add_comm]
    change ∫ y, (c : ℂ)⁻¹ * k₀ y * h (-y + x) ∂μ = ∫ w : Wc, Φ w * h (x + γ w)
    simp only [mul_assoc]
    rw [integral_const_mul, key, hneg, ← mul_assoc, inv_mul_cancel₀ hcc, one_mul]

/-- Dixmier–Malliavin on the elementary group in additive form: each compactly supported
elementary Schwartz function is a finite sum of convolutions of two such functions, for any
Haar measure. -/
private theorem elementaryLieGroup_compact_convolution_factorization {m n r : ℕ} {D : Type}
    [AddCommGroup D] [Fintype D] [TopologicalSpace D] [DiscreteTopology D]
    (μ : @Measure (ElementaryLieGroup m n r D) (borel _)) :
    letI : MeasurableSpace (ElementaryLieGroup m n r D) := borel _
    μ.IsAddHaarMeasure → ∀ f : ElementarySchwartz m n r D,
      HasCompactSupport (f : ElementaryLieGroup m n r D → ℂ) →
      (f : ElementaryLieGroup m n r D → ℂ) ∈ AddSubmonoid.closure
        {θ : ElementaryLieGroup m n r D → ℂ | ∃ u v : ElementarySchwartz m n r D,
          HasCompactSupport (u : ElementaryLieGroup m n r D → ℂ) ∧
          HasCompactSupport (v : ElementaryLieGroup m n r D → ℂ) ∧
          θ = fun x ↦ ∫ y, u y * v (-y + x) ∂μ} := by
  intro hμ f hf
  refine AddSubmonoid.closure_mono ?_ (elementaryLieGroup_cover_factorization f hf)
  rintro θ ⟨Φ, h, hΦ, hΦc, hh, rfl⟩
  obtain ⟨k, hk, hkh⟩ := elementaryLieGroup_cover_kernel μ hμ Φ hΦ hΦc
  exact ⟨k, h, hk, hh, funext fun x ↦ (hkh h (elementarySchwartz_continuous h) x).symm⟩

/-- Dixmier and Malliavin, *Factorisations de fonctions et de vecteurs
indéfiniment différentiables*, Bull. Sci. Math. (2) 102 (1978), Théorème 3.1. On the elementary
abelian Lie group presented by `e` (a product of Euclidean, torus, lattice and finite factors),
each compactly supported smooth function is a finite sum of convolutions of two such functions
for the given Haar measure. Smooth functions of compact support belong to the elementary
Schwartz stage; the membership below is in the algebraic additive closure.
This case was first stated as a classical input (#7486) and is now proved (#7543), from the
one-parameter theorem vendored in `External/FermatDixmierMalliavin`. -/
private theorem elementary_compact_convolution_factorization {Q : Type*} [CommGroup Q]
    [TopologicalSpace Q] [IsTopologicalGroup Q] (e : ElementaryLCAPresentation Q)
    (ν : @Measure Q (borel _)) :
    letI : MeasurableSpace Q := borel _
    ν.IsHaarMeasure →
      let V (f : SchwartzBruhatStage e) (x : Q) := f (Multiplicative.toAdd (e.equiv x))
      ∀ f : SchwartzBruhatStage e, HasCompactSupport (V f) →
        V f ∈ AddSubmonoid.closure {θ : Q → ℂ | ∃ u v : SchwartzBruhatStage e,
          HasCompactSupport (V u) ∧ HasCompactSupport (V v) ∧ θ = lcaConvolution ν (V u) (V v)} := by
  let : MeasurableSpace Q := borel _
  have : BorelSpace Q := ⟨rfl⟩
  intro hν V f hf
  let G := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let : MeasurableSpace G := borel _
  have : BorelSpace G := ⟨rfl⟩
  let ψ : Q ≃ₜ G :=
    { toEquiv := e.equiv.toEquiv.trans Multiplicative.toAdd
      continuous_toFun := e.equiv.continuous
      continuous_invFun := e.equiv.symm.continuous }
  have hmul (x y : Q) : ψ (x * y) = ψ x + ψ y := by
    change Multiplicative.toAdd (e.equiv (x * y)) = _
    rw [map_mul]
    rfl
  have hinv (x : Q) : ψ x⁻¹ = -ψ x := by
    change Multiplicative.toAdd (e.equiv x⁻¹) = _
    rw [map_inv]
    rfl
  let μ : Measure G := ν.map ψ
  have hμ : μ.IsAddHaarMeasure := by
    have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK ↦ by
      change (ν.map ψ.toMeasurableEquiv) K < ⊤
      rw [ψ.toMeasurableEquiv.map_apply]
      exact (ψ.isCompact_preimage.mpr hK).measure_lt_top⟩
    have : μ.IsOpenPosMeasure := ψ.continuous.isOpenPosMeasure_map ψ.surjective
    have : μ.IsAddLeftInvariant := ⟨fun g ↦ by
      have hc : (fun y ↦ g + y) ∘ ψ = ψ ∘ (fun y ↦ ψ.symm g * y) := by
        funext y
        simp [hmul]
      have hg : Measurable (fun y : G ↦ g + y) := (continuous_const.add continuous_id).measurable
      have hq : Measurable (fun y : Q ↦ ψ.symm g * y) :=
        (continuous_const.mul continuous_id).measurable
      change Measure.map (fun y ↦ g + y) (ν.map ψ) = ν.map ψ
      rw [Measure.map_map hg ψ.continuous.measurable, hc,
        ← Measure.map_map ψ.continuous.measurable hq, map_mul_left_eq_self]⟩
    exact {}
  have hfc : HasCompactSupport (f : G → ℂ) := by
    have h := hf.comp_homeomorph ψ.symm
    have he : V f ∘ ψ.symm = (f : G → ℂ) := funext fun y ↦ congrArg f (ψ.apply_symm_apply y)
    rwa [he] at h
  have key := elementaryLieGroup_compact_convolution_factorization μ hμ f hfc
  refine AddSubmonoid.closure_induction (motive := fun θ _ ↦ θ ∘ ψ ∈ AddSubmonoid.closure
    {θ : Q → ℂ | ∃ u v : SchwartzBruhatStage e,
      HasCompactSupport (V u) ∧ HasCompactSupport (V v) ∧ θ = lcaConvolution ν (V u) (V v)})
    ?_ ?_ ?_ key
  · rintro θ ⟨u, v, hu, hv, rfl⟩
    apply AddSubmonoid.subset_closure
    refine ⟨u, v, hu.comp_homeomorph ψ, hv.comp_homeomorph ψ, funext fun x ↦ ?_⟩
    change ∫ y, u y * v (-y + ψ x) ∂(ν.map ψ.toMeasurableEquiv) = ∫ y, u (ψ y) * v (ψ (y⁻¹ * x)) ∂ν
    rw [integral_map_equiv]
    simp [hmul, hinv]
  · exact zero_mem _
  · intro a b _ _ ha hb
    exact add_mem ha hb

end ConvolutionFactorization

/-- The Dixmier–Malliavin factorization theorem. Every compactly supported
Bruhat test on the idele class group is a finite sum of convolutions of two such tests, for
the Tamagawa Haar measure. J. Dixmier and P. Malliavin, *Factorisations de fonctions et de
vecteurs indéfiniment différentiables*, Bull. Sci. Math. (2) 102 (1978), 307–330,
Théorème 3.1, applied on the Lie group `G₁ / K` for an open subgroup `G₁` and a compact
subgroup `K` with respect to which the test is a Bruhat test (F. Bruhat, *Distributions sur
un groupe localement compact et applications à l'étude des représentations des groupes
℘-adiques*, Bull. Soc. Math. France 89 (1961), 43–75). The library proves the case of tests
of one angular character (`spectralHomogeneousTest_convolution_factorization` in §10.3).
The structural quotient and zero extension reduce this to factorization on the elementary Lie
group (#7501), which is proved above (#7543). -/
theorem bruhatCompactSupport_convolution_factorization (φ : BruhatCompactSupport C𝔽) :
    φ ∈ AddSubmonoid.closure {θ : BruhatCompactSupport C𝔽 |
      ∃ u v : BruhatCompactSupport C𝔽, θ.val = lcaConvolution μ𝔽 u.val v.val} := by
  apply ConvolutionFactorization.adelic_factorization_of_elementary
  intro Q _ _ _ e ν hν
  exact ConvolutionFactorization.elementary_compact_convolution_factorization e ν hν

/-- Paper: Theorem 10.4.2.1, p. 459, at orders `0 ≤ s ≤ 1`. Every compactly supported Bruhat
test acts on the strip quotient by a Hilbert–Schmidt operator.
Reconstruction: The paper does not state this. It is the estimate of the argument posted on
#7405 for the whole range. After the Mellin transform, each angular component of the quotient
is `D_s ⊖ V` for an equivalent norm `∫_{∂S} |F|² + ∬_S |F'|² (α − |σ|)^{1−s}` on the strip
`S = {|Re z| < α}`, where `V` is the space of functions that vanish at the zeros in the open
strip. That identification is `spectralStripJet_commonKernel`; at `s ≤ 1` no boundary jet
survives. A Carleson formula with a positive measure for finite Blaschke products gives an
orthonormal basis `B_{n−1} g_n` of `D_s ⊖ V`. A positivity bound for the normalized kernels
`g_n`, uniform in the measure, gives `‖Φ g_n‖² ≪ (1 + (Im ρ_n)²)^{−M}`, and the count of zeros
with multiplicity makes the sum converge.
The Lean proof does not follow that argument. Convolution on the strip quotient is trace class
for every Sobolev order `s ≥ 0` (`spectralStripConvolution_nuclear_of_summable_clusterTraceNorms`
of `Sec3_TraceClass`: the zeros are summed by clusters between well-chosen heights, with contour
multipliers built from the Hecke L-functions), and a nuclear operator is Hilbert–Schmidt
(`mem_hilbertSchmidtOperators_of_isNuclearOperator`). The hypothesis `s ≤ 1` is not used. -/
theorem spectralStripConvolution_hilbertSchmidt_of_le_one (_hs₁ : s ≤ 1)
    (φ : BruhatCompactSupport C𝔽) : Aq(φ) ∈ hilbertSchmidtOperators H₀ H₀ :=
  mem_hilbertSchmidtOperators_of_isNuclearOperator
    (spectralStripConvolution_nuclear_of_summable_clusterTraceNorms a hα hs φ)

/-- Convolution of tests is composition of their actions on the strip quotient. -/
private theorem spectralConvolution_lcaConvolution (θ u v : BruhatCompactSupport C𝔽)
    (h : θ.val = lcaConvolution μ𝔽 u.val v.val) : Aq(θ) = (Aq(u)).comp (Aq(v)) := by
  obtain ⟨θ', hθ', hact⟩ := bruhatRegularizedAction_convolution μ𝔽
    (hardySobolevTranslation μ𝔽 m𝔽 (-α) α s hI hs)
    (exists_hardySobolevTranslation μ𝔽 m𝔽 (-α) α s hI hs).choose_spec.2 u v
  obtain rfl : θ' = θ := Subtype.ext (hθ'.trans h.symm)
  ext q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change Aq(θ') ((globalThetaSobolev F a hI hs).mkQ x) =
    Aq(u) (Aq(v) ((globalThetaSobolev F a hI hs).mkQ x))
  rw [spectralConvolution_mkQ, spectralConvolution_mkQ, spectralConvolution_mkQ]
  exact congrArg _ (hact x)

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). Every compactly supported
Bruhat test acts by a nuclear convolution operator on the strip quotient.
Deviation: The theorems of §10.4.2 print `s ≥ 0`, while p. 455 assumes `s > 1` for
the section. This statement covers `0 ≤ s ≤ 1`.
Proved directly from trace class on the strip quotient for every Sobolev order `s ≥ 0`
(`spectralStripConvolution_nuclear_of_summable_clusterTraceNorms` of `Sec3_TraceClass`, the
cluster route), so neither the Hilbert–Schmidt statement
`spectralStripConvolution_hilbertSchmidt_of_le_one` nor the Dixmier–Malliavin factorization
`bruhatCompactSupport_convolution_factorization` is used. At width zero the statement is also
`spectralStripConvolution_nuclear_of_zero_width`. Nothing in the Lean uses this statement, and
it is not known how it connects with the rest of the proof in Lean; in the paper it is used on
pp. 459–461, 463–464, 503, 519–520. -/
theorem spectralStripConvolution_nuclear_of_le_one (_hs₁ : s ≤ 1) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ)) :=
  spectralStripConvolution_nuclear_of_summable_clusterTraceNorms a hα hs φ

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). If every test acts on the strip
quotient by a Hilbert–Schmidt operator, then every test acts by a nuclear operator.
Reconstruction: The paper does not state a Hilbert–Schmidt bound. This is the argument of
`spectralStripConvolution_nuclear_of_le_one`, with the open statement
`spectralStripConvolution_hilbertSchmidt_of_le_one` as a hypothesis and at every order, proved
from the classical input `bruhatCompactSupport_convolution_factorization`: a test is a finite
sum of convolutions `u * v`, the quotient action takes `u * v` to the composite of the two
actions, and a composite of two Hilbert–Schmidt operators is nuclear
(`nuclear_hilbertSchmidt_comp`).
Deviation: No restriction on the Sobolev order or the width is needed. Nothing in the Lean uses
this statement, and it is not known how it connects with the rest of the proof in Lean. -/
theorem spectralStripConvolution_nuclear_of_hilbertSchmidt
    (hHS : ∀ ψ : BruhatCompactSupport C𝔽, Aq(ψ) ∈ hilbertSchmidtOperators H₀ H₀)
    (φ : BruhatCompactSupport C𝔽) : IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ)) := by
  induction (bruhatCompactSupport_convolution_factorization φ) using
    AddSubmonoid.closure_induction with
  | mem h hh =>
    obtain ⟨u, v, huv⟩ := hh
    rw [spectralConvolution_lcaConvolution a hα hs h u v huv]
    exact nuclear_hilbertSchmidt_comp ⟨_, hHS u⟩ ⟨_, hHS v⟩
  | zero =>
    rw [(spectralConvolution_isLinear (F := F) a hI hs).map_zero]
    exact (nuclearEndomorphisms _).zero_mem
  | add x y _ _ hx hy =>
    rw [(spectralConvolution_isLinear (F := F) a hI hs).map_add]
    exact (nuclearEndomorphisms _).add_mem hx hy

/-- Summable real sequences are square summable. -/
private theorem spectralStripConvolution_hilbertSchmidt_of_nuclear_summable (f : ℕ → ℝ)
    (hf : Summable (fun n ↦ f n ^ (1 : ℝ))) : Summable (fun n ↦ f n ^ (2 : ℝ)) := by
  simp only [Real.rpow_one] at hf
  simp only [Real.rpow_two]
  have h0 : ∀ᶠ n in cofinite, ‖f n‖ ≤ 1 := by
    have := (hf.tendsto_cofinite_zero).norm
    rw [norm_zero] at this
    exact this.eventually (eventually_le_nhds one_pos)
  refine hf.norm.of_norm_bounded_eventually ?_
  filter_upwards [h0] with n hn
  rw [norm_pow, sq]
  exact mul_le_of_le_one_left (norm_nonneg _) hn

/-- Paper: Theorem 10.4.2.1, p. 459. A nuclear quotient convolution is Hilbert–Schmidt: the
converse of `spectralStripConvolution_nuclear_of_hilbertSchmidt`, test by test. -/
theorem spectralStripConvolution_hilbertSchmidt_of_nuclear (φ : BruhatCompactSupport C𝔽)
    (hn : IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ))) :
    Aq(φ) ∈ hilbertSchmidtOperators H₀ H₀ := by
  obtain ⟨hc, hsum⟩ := (mem_traceClassOperators_iff_isNuclearOperator _).mpr hn
  exact ⟨hc, spectralStripConvolution_hilbertSchmidt_of_nuclear_summable _ hsum⟩

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). At each order and width, every test
acts on the strip quotient by a nuclear operator exactly when every test acts by a
Hilbert–Schmidt operator. So the conclusion of `spectralStripConvolution_nuclear_of_le_one`
is equivalent to the Hilbert–Schmidt property, given the classical input
`bruhatCompactSupport_convolution_factorization`.
Deviation: No restriction on the Sobolev order or the width is needed. Nothing in the Lean uses
this statement, and it is not known how it connects with the rest of the proof in Lean. -/
theorem spectralStripConvolution_nuclear_iff_hilbertSchmidt :
    (∀ φ : BruhatCompactSupport C𝔽, IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ))) ↔
      ∀ φ : BruhatCompactSupport C𝔽, Aq(φ) ∈ hilbertSchmidtOperators H₀ H₀ :=
  ⟨fun h φ ↦ spectralStripConvolution_hilbertSchmidt_of_nuclear a hα hs φ (h φ),
    fun h φ ↦ spectralStripConvolution_nuclear_of_hilbertSchmidt a hα hs h φ⟩

/-- Approximation numbers are nonnegative. -/
private theorem spectralStripConvolution_hilbertSchmidt_of_spectralProjection_nonneg
    {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] (T : E →L[ℂ] G) (n : ℕ) :
    0 ≤ approximationNumber T n :=
  Real.sInf_nonneg (by rintro _ ⟨_, _, rfl⟩; exact norm_nonneg _)

/-- Composing a Hilbert–Schmidt operator with bounded operators on both sides gives a
Hilbert–Schmidt operator. -/
private theorem spectralStripConvolution_hilbertSchmidt_of_spectralProjection_ideal
    {D E G K : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]
    [CompleteSpace D] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (L : G →L[ℂ] K) (X : E →L[ℂ] G) (R : D →L[ℂ] E) (hX : X ∈ hilbertSchmidtOperators E G) :
    (L.comp X).comp R ∈ hilbertSchmidtOperators D K := by
  obtain ⟨hc, hsum⟩ := hX
  refine ⟨(hc.clm_comp L).comp_clm R, ?_⟩
  simp only [Real.rpow_two] at hsum ⊢
  set c := approximationNumber L 0 * approximationNumber R 0
  have hb (n : ℕ) :
      approximationNumber ((L.comp X).comp R) (n + 2) ≤ c * approximationNumber X n := by
    have h1 := approximationNumber_comp_le (L.comp X) R (n + 1) 0
    have h2 := approximationNumber_comp_le L X 0 n
    have e1 : n + 1 + 0 + 1 = n + 2 := by omega
    have e2 : 0 + n + 1 = n + 1 := by omega
    rw [e1] at h1
    rw [e2] at h2
    calc _ ≤ approximationNumber (L.comp X) (n + 1) * approximationNumber R 0 := h1
      _ ≤ (approximationNumber L 0 * approximationNumber X n) * approximationNumber R 0 :=
          mul_le_mul_of_nonneg_right h2
            (spectralStripConvolution_hilbertSchmidt_of_spectralProjection_nonneg _ _)
      _ = c * approximationNumber X n := by ring
  refine (summable_nat_add_iff 2).mp ?_
  refine (hsum.mul_left (c ^ 2)).of_nonneg_of_le (fun n ↦ sq_nonneg _) (fun n ↦ ?_)
  rw [← mul_pow]
  exact pow_le_pow_left₀
    (spectralStripConvolution_hilbertSchmidt_of_spectralProjection_nonneg _ _) (hb n) 2

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). If convolution after spectral
projection is Hilbert–Schmidt on the weighted space, then quotient convolution is
Hilbert–Schmidt.
Reconstruction: The paper does not state a Hilbert–Schmidt bound. This reduces the open
statement `spectralStripConvolution_hilbertSchmidt_of_le_one`, the hypothesis of
`spectralStripConvolution_nuclear_of_hilbertSchmidt`, to a statement on the weighted space:
the quotient action is the quotient map after convolution after spectral projection, applied
to the isometric section of the quotient map, and Hilbert–Schmidt operators form an ideal.
For a Hilbert basis `e` of the spectral complement, the hypothesis says that the sum of
`‖A(φ) e n‖²` is finite. The converse would also need the block from the spectral complement
to the theta subspace to be Hilbert–Schmidt, which this argument does not give.
Deviation: No restriction on the Sobolev order or the width is needed. Nothing in the Lean uses
this statement, and it is not known how it connects with the rest of the proof in Lean. -/
theorem spectralStripConvolution_hilbertSchmidt_of_spectralProjection (φ : BruhatCompactSupport C𝔽)
    (hHS : (A(φ)).comp (spectralProjection (F := F) a hα hs) ∈ hilbertSchmidtOperators W W) :
    Aq(φ) ∈ hilbertSchmidtOperators H₀ H₀ := by
  let Θ := globalThetaSobolev F a hI hs
  let S : H₀ →L[ℂ] W := Θᗮ.subtypeL.comp
    Θ.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  have hS (x : H₀) : Θ.mkQ (S x) = x ∧ spectralProjection (F := F) a hα hs (S x) = S x :=
    ⟨by simp [S], Submodule.starProjection_eq_self_iff.mpr (Θ.quotientEquivOrthogonal x).2⟩
  have heq : Aq(φ) = (Θ.mkQL.comp ((A(φ)).comp (spectralProjection (F := F) a hα hs))).comp S := by
    ext x
    obtain ⟨h1, h2⟩ := hS x
    conv_lhs => rw [← h1]
    rw [spectralConvolution_mkQ]
    change _ = Θ.mkQ (A(φ) (spectralProjection (F := F) a hα hs (S x)))
    rw [h2]
  rw [heq]
  exact spectralStripConvolution_hilbertSchmidt_of_spectralProjection_ideal _ _ _ hHS

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). If convolution after spectral
projection is Hilbert–Schmidt on the weighted space for every test, then every test acts on the
strip quotient by a nuclear operator.
Reconstruction: The paper does not state a Hilbert–Schmidt bound. This combines
`spectralStripConvolution_hilbertSchmidt_of_spectralProjection` with
`spectralStripConvolution_nuclear_of_hilbertSchmidt`, and so uses the classical input
`bruhatCompactSupport_convolution_factorization`.
Deviation: No restriction on the Sobolev order or the width is needed. Nothing in the Lean uses
this statement, and it is not known how it connects with the rest of the proof in Lean. -/
theorem spectralStripConvolution_nuclear_of_spectralProjection_hilbertSchmidt
    (hHS : ∀ ψ : BruhatCompactSupport C𝔽,
      (A(ψ)).comp (spectralProjection (F := F) a hα hs) ∈ hilbertSchmidtOperators W W)
    (φ : BruhatCompactSupport C𝔽) : IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ)) :=
  spectralStripConvolution_nuclear_of_hilbertSchmidt a hα hs
    (fun ψ ↦ spectralStripConvolution_hilbertSchmidt_of_spectralProjection a hα hs ψ (hHS ψ)) φ

/-- An operator after the orthogonal projection onto a complete subspace is Hilbert–Schmidt
exactly when the squared norms of its values on a Hilbert basis of the subspace are summable. -/
private theorem spectralStripConvolution_comp_spectralProjection_hilbertSchmidt_iff_aux
    {E G ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (K : Submodule ℂ E) [CompleteSpace K] (e : HilbertBasis ι ℂ K) (T : E →L[ℂ] G) :
    T.comp K.starProjection ∈ hilbertSchmidtOperators E G ↔
      Summable (fun i ↦ ‖T (e i)‖ ^ (2 : ℕ)) := by
  have hcrit : T.comp K.subtypeL ∈ hilbertSchmidtOperators K G ↔
      Summable (fun i ↦ ‖T (e i)‖ ^ (2 : ℕ)) :=
    mem_hilbertSchmidtOperators_iff_summable_basis e (T.comp K.subtypeL)
  rw [← hcrit]
  constructor
  · intro h
    have hfac : T.comp K.subtypeL =
        ((ContinuousLinearMap.id ℂ G).comp (T.comp K.starProjection)).comp K.subtypeL := by
      ext x
      simp [Submodule.starProjection_eq_self_iff.mpr x.2]
    rw [hfac]
    exact spectralStripConvolution_hilbertSchmidt_of_spectralProjection_ideal _ _ _ h
  · intro h
    have hfac : T.comp K.starProjection =
        ((ContinuousLinearMap.id ℂ G).comp (T.comp K.subtypeL)).comp
          K.orthogonalProjectionOnto := by
      ext x
      rfl
    rw [hfac]
    exact spectralStripConvolution_hilbertSchmidt_of_spectralProjection_ideal _ _ _ h

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). Convolution after spectral projection
is Hilbert–Schmidt on the weighted space exactly when, for any Hilbert basis `e` of the
orthogonal complement of the theta closure, the squared norms `‖A(φ) e i‖²` are summable.
Reconstruction: The paper does not state a Hilbert–Schmidt bound. This is the form in which the
hypothesis of `spectralStripConvolution_hilbertSchmidt_of_spectralProjection` is checked on a
basis, for instance the basis of `exists_spectralComplement_takenakaBasis`.
Deviation: No restriction on the Sobolev order or the width is needed. Nothing in the Lean uses
this statement, and it is not known how it connects with the rest of the proof in Lean. -/
theorem spectralStripConvolution_comp_spectralProjection_hilbertSchmidt_iff {ι : Type*}
    (e : HilbertBasis ι ℂ (globalThetaSobolev F a hI hs)ᗮ) (φ : BruhatCompactSupport C𝔽) :
    (A(φ)).comp (spectralProjection (F := F) a hα hs) ∈ hilbertSchmidtOperators W W ↔
      Summable (fun i ↦ ‖A(φ) (e i)‖ ^ (2 : ℕ)) :=
  spectralStripConvolution_comp_spectralProjection_hilbertSchmidt_iff_aux _ e _

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). If for one Hilbert basis `e` of the
orthogonal complement of the theta closure the squared norms `‖A(ψ) e i‖²` are summable for
every test `ψ`, then every test acts on the strip quotient by a nuclear operator.
Reconstruction: The paper does not state a Hilbert–Schmidt bound. This combines
`spectralStripConvolution_comp_spectralProjection_hilbertSchmidt_iff` with
`spectralStripConvolution_nuclear_of_spectralProjection_hilbertSchmidt`, and so uses the
classical input `bruhatCompactSupport_convolution_factorization`. For the basis of
`exists_spectralComplement_takenakaBasis` the summands are indexed by the strip jets, that is, by
the zeros counted with multiplicity.
Deviation: No restriction on the Sobolev order or the width is needed. Nothing in the Lean uses
this statement, and it is not known how it connects with the rest of the proof in Lean. -/
theorem spectralStripConvolution_nuclear_of_summable_basis {ι : Type*}
    (e : HilbertBasis ι ℂ (globalThetaSobolev F a hI hs)ᗮ)
    (hsum : ∀ ψ : BruhatCompactSupport C𝔽, Summable (fun i ↦ ‖A(ψ) (e i)‖ ^ (2 : ℕ)))
    (φ : BruhatCompactSupport C𝔽) : IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ)) :=
  spectralStripConvolution_nuclear_of_spectralProjection_hilbertSchmidt a hα hs
    (fun ψ ↦ (spectralStripConvolution_comp_spectralProjection_hilbertSchmidt_iff a hα hs e ψ).mpr
      (hsum ψ)) φ

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). Quotient convolution is
Hilbert–Schmidt if convolution is Hilbert–Schmidt on a Hilbert space mapped boundedly into the
weighted space, and the quotient map on that image has a bounded right inverse.
Reconstruction: The paper does not state a Hilbert–Schmidt bound. The section need not be the
orthogonal one, and the Hilbert space may carry a different but equivalent norm, as for a model
space of a Hardy space mapped into the weighted space by an inverse Mellin transform.
Deviation: No restriction on the Sobolev order or the width is needed. Nothing in the Lean uses
this statement, and it is not known how it connects with the rest of the proof in Lean. -/
theorem spectralStripConvolution_hilbertSchmidt_of_section {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] (J : G →L[ℂ] W) (R : H₀ →L[ℂ] G)
    (hJR : ∀ x, (globalThetaSobolev F a hI hs).mkQ (J (R x)) = x)
    (φ : BruhatCompactSupport C𝔽) (hHS : (A(φ)).comp J ∈ hilbertSchmidtOperators G W) :
    Aq(φ) ∈ hilbertSchmidtOperators H₀ H₀ := by
  have heq : Aq(φ) = ((globalThetaSobolev F a hI hs).mkQL.comp ((A(φ)).comp J)).comp R := by
    ext x
    conv_lhs => rw [← hJR x]
    rw [spectralConvolution_mkQ]
    rfl
  rw [heq]
  exact spectralStripConvolution_hilbertSchmidt_of_spectralProjection_ideal _ _ _ hHS

open Classical in
/-- Gram–Schmidt along an enumeration turns a linearly independent family whose orthogonal
complement is zero into a Hilbert basis whose `i`-th vector lies in the span of the vectors of
index at most `i` and is orthogonal to the vectors of smaller index. -/
private theorem exists_spectralComplement_takenakaBasis_aux {H ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (f : ι → H) (hf : LinearIndependent ℂ f)
    (hsep : ∀ v : H, (∀ i, inner ℂ (f i) v = 0) → v = 0) (n : ι → ℕ)
    (hn : Function.Injective n) :
    ∃ e : HilbertBasis ι ℂ H, (∀ i, e i ∈ Submodule.span ℂ (f '' {k | n k ≤ n i})) ∧
      ∀ i k, n k < n i → inner ℂ (f k) (e i) = 0 := by
  let S := {m : ℕ // m ∈ Set.range n}
  let σ : ι ≃ S := Equiv.ofInjective n hn
  let g : S → H := f ∘ σ.symm
  have hg : LinearIndependent ℂ g := hf.comp _ σ.symm.injective
  let gs := InnerProductSpace.gramSchmidtNormed ℂ g
  have hgs : Orthonormal ℂ gs := InnerProductSpace.gramSchmidtNormed_orthonormal hg
  have hv : Orthonormal ℂ (gs ∘ σ) := hgs.comp _ σ.injective
  have hspan : Submodule.span ℂ (Set.range (gs ∘ σ)) = Submodule.span ℂ (Set.range g) := by
    rw [Set.range_comp, σ.range_eq_univ, Set.image_univ,
      InnerProductSpace.span_gramSchmidtNormed_range, InnerProductSpace.span_gramSchmidt]
  have hbot : (Submodule.span ℂ (Set.range (gs ∘ σ)))ᗮ = ⊥ := by
    rw [hspan, Submodule.eq_bot_iff]
    intro v hv'
    apply hsep v
    intro i
    have := (Submodule.mem_orthogonal _ v).mp hv' (g (σ i))
      (Submodule.subset_span ⟨σ i, rfl⟩)
    simpa [g] using this
  refine ⟨HilbertBasis.mkOfOrthogonalEqBot hv hbot, fun i ↦ ?_, fun i k hki ↦ ?_⟩
  swap
  · rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
    have hlt : σ k < σ i := hki
    have h0 := InnerProductSpace.gramSchmidt_inv_triangular ℂ g hlt
    have hgk : g (σ k) = f k := congrArg f (σ.symm_apply_apply k)
    rw [hgk] at h0
    change inner ℂ (f k) (InnerProductSpace.gramSchmidtNormed ℂ g (σ i)) = 0
    rw [InnerProductSpace.gramSchmidtNormed, inner_smul_right, inner_eq_zero_symm.mp h0, mul_zero]
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  have hmem : InnerProductSpace.gramSchmidt ℂ g (σ i) ∈
      Submodule.span ℂ (g '' Set.Iic (σ i)) :=
    InnerProductSpace.gramSchmidt_mem_span ℂ g le_rfl
  have hsub : g '' Set.Iic (σ i) ⊆ f '' {k | n k ≤ n i} := by
    rintro _ ⟨m, hm, rfl⟩
    refine ⟨σ.symm m, ?_, rfl⟩
    have h1 : n (σ.symm m) = m.val := congrArg Subtype.val (σ.apply_symm_apply m)
    have h2 : (σ i).val = n i := rfl
    simp only [Set.mem_ofPred_eq, h1]
    exact h2 ▸ hm
  change InnerProductSpace.gramSchmidtNormed ℂ g (σ i) ∈ _
  rw [InnerProductSpace.gramSchmidtNormed]
  exact Submodule.smul_mem _ _ (Submodule.span_mono hsub hmem)

/-- Paper: Theorem 10.2.2.1, p. 446, and Theorem 10.4.2.1, p. 459. Every strip jet pairing is
the inner product with a vector `r j` of the weighted space, and for an enumeration `n` of the
jets the orthogonal complement of the theta closure has a Hilbert basis `e` indexed by the jets
whose `j`-th vector lies in the span of the `r k` with `n k ≤ n j` and has vanishing pairing with
every jet `u k` with `n k < n j`.
Reconstruction: The paper does not use such a basis. It is the analogue, in the weighted space,
of the Takenaka–Malmquist–Walsh basis of a model space, the Gram–Schmidt orthonormalization of
the reproducing kernels at the zeros (S. R. Garcia and W. T. Ross, *Model spaces: a survey*,
Contemp. Math. 638 (2015), §5.4). It is built from the common-kernel theorem
`spectralStripJet_commonKernel` and the linear independence of the jets, at every order and
width.
Deviation: No restriction on the Sobolev order or the width is needed. Nothing in the Lean uses
this statement, and it is not known how it connects with the rest of the proof in Lean. -/
theorem exists_spectralComplement_takenakaBasis
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) :
    let u (j : SpectralStripJetIndex χ a α s) :
        CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s true :=
      (spectralStripJet_memLp χ hα hs j).toLp
        (spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)
    ∃ (r : SpectralStripJetIndex χ a α s → W) (n : SpectralStripJetIndex χ a α s → ℕ)
      (e : HilbertBasis (SpectralStripJetIndex χ a α s) ℂ (globalThetaSobolev F a hI hs)ᗮ),
      (∀ j f, inner ℂ (r j) f = spectralSobolevPairing f (u j)) ∧ Function.Injective n ∧
      (∀ j, (e j : W) ∈ Submodule.span ℂ (r '' {k | n k ≤ n j})) ∧
      ∀ j k, n k < n j → spectralSobolevPairing (e j : W) (u k) = 0 := by
  intro u
  let Θ := globalThetaSobolev F a hI hs
  let T := (modulatedIntervalSobolev_dual m𝔽
    (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
    μ𝔽 (-α) α s hI hs).exists.choose
  let Λ (j : SpectralStripJetIndex χ a α s) : StrongDual ℂ W := T.symm (u j)
  have hΛ (j) (f : W) : Λ j f = spectralSobolevPairing f (u j) := by
    have h := (spectralSobolevPairing_dual hI hs (Λ j) f).2
    rw [h]
    exact congrArg (spectralSobolevPairing f) (T.apply_symm_apply (u j))
  let r (j : SpectralStripJetIndex χ a α s) : W := (InnerProductSpace.toDual ℂ W).symm (Λ j)
  have hr (j) (f : W) : inner ℂ (r j) f = spectralSobolevPairing f (u j) := by
    rw [InnerProductSpace.toDual_symm_apply, hΛ]
  have hK := spectralStripJet_commonKernel χ hχ (a := a) hα hs
  have hrΘ (j) : r j ∈ Θᗮ := by
    rw [Submodule.mem_orthogonal']
    intro θ hθ
    rw [hr]
    exact (hK θ).mp hθ j
  have hu := spectralStripJet_toLp_linearIndependent χ hχ a hα hs
  have hrind : LinearIndependent ℂ r := by
    apply linearIndependent_iff'.mpr
    intro S c h i hi
    have h' := congrArg (fun x ↦ T (InnerProductSpace.toDual ℂ W x)) h
    simp only [map_sum, map_smulₛₗ, LinearIsometryEquiv.apply_symm_apply, map_zero, r, Λ] at h'
    have hz := linearIndependent_iff'.mp hu S _ h' i hi
    simpa using hz
  let f' (j : SpectralStripJetIndex χ a α s) : Θᗮ := ⟨r j, hrΘ j⟩
  have hf' : LinearIndependent ℂ f' := LinearIndependent.of_comp Θᗮ.subtype hrind
  have hsep (v : Θᗮ) (hv : ∀ j, inner ℂ (f' j) v = 0) : v = 0 := by
    have hvΘ : (v : W) ∈ Θ := by
      apply (hK v).mpr
      intro j
      rw [← hr]
      exact hv j
    have h0 := Submodule.inner_right_of_mem_orthogonal hvΘ v.2
    exact Subtype.ext (inner_self_eq_zero.mp h0)
  obtain ⟨n, hn⟩ := (spectralStripJet_countable χ a α s).exists_injective_nat
  obtain ⟨e, he, hortho⟩ := exists_spectralComplement_takenakaBasis_aux f' hf' hsep n hn
  refine ⟨r, n, e, hr, hn, fun j ↦ ?_, fun j k hkj ↦ ?_⟩
  swap
  · rw [← hr]
    exact hortho j k hkj
  have h1 : ((e j : Θᗮ) : W) ∈ (Submodule.span ℂ (f' '' {k | n k ≤ n j})).map Θᗮ.subtype :=
    Submodule.mem_map_of_mem (he j)
  rw [Submodule.map_span, ← Set.image_comp] at h1
  exact h1

/-- The sum of `⟪T d i, T d i⟫` over an orthonormal basis of a finite-dimensional space does not
depend on the basis. -/
private theorem traceKey {V G ι κ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [Fintype ι] [Fintype κ] (T : V →L[ℂ] G) (d : OrthonormalBasis ι ℂ V)
    (c : OrthonormalBasis κ ℂ V) :
    ∑ i, inner ℂ (T (d i)) (T (d i)) = ∑ j, inner ℂ (T (c j)) (T (c j)) := by
  let Gm := T.adjoint ∘L T
  have hG (x y : V) : inner ℂ (T x) (T y) = inner ℂ x (Gm y) := by
    simp [Gm, ContinuousLinearMap.adjoint_inner_right]
  have hG' (x y : V) : inner ℂ x (Gm y) = inner ℂ (Gm x) y := by
    simp only [Gm, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right]
  calc ∑ i, inner ℂ (T (d i)) (T (d i))
      = ∑ i, ∑ j, inner ℂ (d i) (c j) * inner ℂ (c j) (Gm (d i)) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hG, c.sum_inner_mul_inner]
    _ = ∑ j, ∑ i, inner ℂ (Gm (c j)) (d i) * inner ℂ (d i) (c j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hG', mul_comm]
    _ = ∑ j, inner ℂ (T (c j)) (T (c j)) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [d.sum_inner_mul_inner, ← hG', ← hG]

/-- The squared Hilbert–Schmidt sum over an orthonormal basis of a finite-dimensional space does
not depend on the basis. -/
private theorem traceX {V G ι κ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [Fintype ι] [Fintype κ] (T : V →L[ℂ] G) (b : OrthonormalBasis ι ℂ V)
    (c : OrthonormalBasis κ ℂ V) :
    ∑ i, ‖T (b i)‖ ^ 2 = ∑ i, ‖T (c i)‖ ^ 2 := by
  have h := traceKey T b c
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/-- An orthonormal family in a finite-dimensional subspace with at least as many vectors as the
dimension is a basis, so its squared Hilbert–Schmidt sum is the one over any orthonormal basis. -/
private theorem sum_sq_eq_of_orthonormal_mem {E G κ ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] [Fintype κ] [Fintype ι] (V : Submodule ℂ E) [FiniteDimensional ℂ V]
    (T : E →L[ℂ] G) (b : OrthonormalBasis ι ℂ V) (w : κ → E) (hw : Orthonormal ℂ w)
    (hwV : ∀ j, w j ∈ V) (hcard : Module.finrank ℂ V ≤ Fintype.card κ) :
    ∑ j, ‖T (w j)‖ ^ 2 = ∑ i, ‖T (b i)‖ ^ 2 := by
  let v (j : κ) : V := ⟨w j, hwV j⟩
  have hv : Orthonormal ℂ v := ⟨fun j ↦ hw.1 j, fun i j hij ↦ hw.2 hij⟩
  have htop : Submodule.span ℂ (Set.range v) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    apply le_antisymm (Submodule.finrank_le _)
    rw [finrank_span_eq_card hv.linearIndependent]
    exact hcard
  let bv := OrthonormalBasis.mk hv htop.ge
  have h := traceX (T.comp V.subtypeL) bv b
  have hbv (j : κ) : (bv j : E) = w j := by
    simp only [bv, OrthonormalBasis.coe_mk, v]
  have hT (x : V) : (T.comp V.subtypeL) x = T (x : E) := rfl
  simpa only [hT, hbv] using h

/-- The case of `sum_sq_eq_of_orthonormal_mem` for the span of finitely many vectors, indexed by
the same finite set as the orthonormal family. -/
private theorem sum_sq_eq_of_orthonormal_mem_span {E G ι κ : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] [Fintype ι] (r : κ → E) (S : Finset κ)
    (T : E →L[ℂ] G) (b : OrthonormalBasis ι ℂ (Submodule.span ℂ (r '' (S : Set κ))))
    (w : S → E) (hw : Orthonormal ℂ w)
    (hwV : ∀ j, w j ∈ Submodule.span ℂ (r '' (S : Set κ))) :
    ∑ j, ‖T (w j)‖ ^ 2 = ∑ i, ‖T (b i)‖ ^ 2 := by
  classical
  have : FiniteDimensional ℂ (Submodule.span ℂ (r '' (S : Set κ))) :=
    FiniteDimensional.span_of_finite ℂ (S.finite_toSet.image r)
  refine sum_sq_eq_of_orthonormal_mem _ T b w hw hwV ?_
  have h1 := finrank_span_finset_le_card (R := ℂ) (S.image r)
  rw [Finset.coe_image] at h1
  exact h1.trans (Finset.card_image_le.trans (Fintype.card_coe S).ge)

/-- For the Takenaka basis `e` of `exists_spectralComplement_takenakaBasis`, a bound on the
squared Hilbert–Schmidt sums of an operator over orthonormal bases of the spans of finitely many
jet representers gives square summability of its values on `e`. -/
private theorem exists_spectralComplement_basis_summable_of_finite_bound
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (r : SpectralStripJetIndex χ a α s → W)
    (hr : ∀ j f, inner ℂ (r j) f = spectralSobolevPairing f
      ((spectralStripJet_memLp χ hα hs j).toLp
        (spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))) :
    ∃ e : HilbertBasis (SpectralStripJetIndex χ a α s) ℂ (globalThetaSobolev F a hI hs)ᗮ,
      ∀ (T : W →L[ℂ] W) (C : ℝ), (∀ S : Finset (SpectralStripJetIndex χ a α s),
        ∃ (k : ℕ) (b : OrthonormalBasis (Fin k) ℂ (Submodule.span ℂ (r '' S))),
          ∑ i, ‖T (b i)‖ ^ 2 ≤ C) → Summable (fun j ↦ ‖T (e j)‖ ^ (2 : ℕ)) := by
  classical
  obtain ⟨r', n, e, hr', hn, hspan, -⟩ := exists_spectralComplement_takenakaBasis a hα hs χ hχ
  have hrr : r' = r := by
    funext j
    exact ext_inner_right ℂ fun f ↦ (hr' j f).trans (hr j f).symm
  subst hrr
  refine ⟨e, fun T C hCψ ↦ ?_⟩
  -- initial segments
  let Sg (N : ℕ) : Finset (SpectralStripJetIndex χ a α s) :=
    (Finset.range N).preimage n (hn.injOn)
  have hseg (N : ℕ) : ∑ j ∈ Sg N, ‖T (e j)‖ ^ 2 ≤ C := by
    obtain ⟨k, b, hb⟩ := hCψ (Sg N)
    let V := Submodule.span ℂ (r' '' (Sg N : Set _))
    have hmem (j : Sg N) : (e j : W) ∈ V := by
      refine Submodule.span_mono ?_ (hspan j)
      rintro _ ⟨i, hi, rfl⟩
      refine ⟨i, ?_, rfl⟩
      have hj := j.2
      simp only [Sg, Finset.coe_preimage, Set.mem_preimage, Finset.coe_range, Set.mem_Iio,
        Finset.mem_preimage, Finset.mem_range] at hj ⊢
      exact lt_of_le_of_lt hi hj
    have he : Orthonormal ℂ (fun j : Sg N ↦ ((e j : (globalThetaSobolev F a hI hs)ᗮ) : W)) :=
      ((e.orthonormal).comp _ Subtype.val_injective).comp_linearIsometry
        (globalThetaSobolev F a hI hs)ᗮ.subtypeₗᵢ
    have key := sum_sq_eq_of_orthonormal_mem_span r' (Sg N) T b _ he hmem
    rw [← Finset.sum_coe_sort (Sg N)]
    exact key.le.trans hb
  -- summability from bounded initial segments
  apply summable_of_sum_le (fun j ↦ sq_nonneg _) (c := C)
  intro T'
  obtain ⟨N, hN⟩ : ∃ N, ∀ j ∈ T', n j < N := ⟨T'.sup n + 1, fun j hj ↦
    Nat.lt_succ_of_le (Finset.le_sup (f := n) hj)⟩
  have hsub : T' ⊆ Sg N := fun j hj ↦ by
    simp only [Sg, Finset.mem_preimage, Finset.mem_range]
    exact hN j hj
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ sq_nonneg _).trans (hseg N)

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). Let `r j` be the vector of the weighted
space whose inner product is the pairing with the strip jet `u j`. If for every test `ψ` there is a
constant `C` such that, for every finite set `S` of jets, the squared norms `‖A(ψ) b i‖²` over
some orthonormal basis `b` of the span of the `r j` with `j ∈ S` add up to at most `C`, then every
test acts on the strip quotient by a nuclear operator.
Reconstruction: The paper does not state a Hilbert–Schmidt bound. On the initial segments of the
enumeration in `exists_spectralComplement_takenakaBasis` the Takenaka basis vectors form an
orthonormal basis of the span of the `r j`, so the partial sums of `‖A(ψ) e j‖²` equal the sums
over `b` and are bounded by `C`; then `spectralStripConvolution_nuclear_of_summable_basis`
applies. The hypothesis involves only finitely many zeros at a time, as for the finite Blaschke
products of a model space, and uses the classical input
`bruhatCompactSupport_convolution_factorization` through
`spectralStripConvolution_nuclear_of_summable_basis`.
Deviation: No restriction on the Sobolev order or the width is needed. Nothing in the Lean uses
this statement, and it is not known how it connects with the rest of the proof in Lean. -/
theorem spectralStripConvolution_nuclear_of_finite_jet_bound
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) :
    let u (j : SpectralStripJetIndex χ a α s) :
        CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s true :=
      (spectralStripJet_memLp χ hα hs j).toLp
        (spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)
    (∃ r : SpectralStripJetIndex χ a α s → W,
      (∀ j f, inner ℂ (r j) f = spectralSobolevPairing f (u j)) ∧
      ∀ ψ : BruhatCompactSupport C𝔽, ∃ C : ℝ, ∀ S : Finset (SpectralStripJetIndex χ a α s),
        ∃ (k : ℕ) (b : OrthonormalBasis (Fin k) ℂ (Submodule.span ℂ (r '' S))),
          ∑ i, ‖A(ψ) (b i)‖ ^ 2 ≤ C) →
    ∀ φ : BruhatCompactSupport C𝔽, IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ)) := by
  intro u ⟨r, hr, hC⟩
  obtain ⟨e, he⟩ := exists_spectralComplement_basis_summable_of_finite_bound a hα hs χ hχ r hr
  exact spectralStripConvolution_nuclear_of_summable_basis a hα hs e fun ψ ↦
    he _ _ (hC ψ).choose_spec

/-- Parseval's identity for a Hilbert basis. -/
private theorem hasSum_norm_inner_sq_hilbertBasis {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (b : HilbertBasis ι ℂ E) (x : E) :
    HasSum (fun i ↦ ‖inner ℂ (b i) x‖ ^ (2 : ℕ)) (‖x‖ ^ (2 : ℕ)) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map,
    b.repr_apply_apply] using lp.hasSum_norm (p := 2) (by norm_num) (b.repr x)

/-- The squared norms of an operator on one Hilbert basis are summable exactly when the squared
norms of its adjoint on another Hilbert basis are: both sums add up `|⟪f j, T (b i)⟫|²`. -/
private theorem summable_sq_basis_iff_summable_sq_adjoint {E G ι κ : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] (b : HilbertBasis ι ℂ E)
    (f : HilbertBasis κ ℂ G) (T : E →L[ℂ] G) :
    Summable (fun i ↦ ‖T (b i)‖ ^ (2 : ℕ)) ↔
      Summable (fun j ↦ ‖T.adjoint (f j)‖ ^ (2 : ℕ)) := by
  let c (i : ι) (j : κ) : ℝ := ‖inner ℂ (f j) (T (b i))‖ ^ (2 : ℕ)
  have hnn (i : ι) (j : κ) : 0 ≤ c i j := by positivity
  have hrow (i : ι) : HasSum (c i) (‖T (b i)‖ ^ (2 : ℕ)) :=
    hasSum_norm_inner_sq_hilbertBasis f (T (b i))
  have hcol (j : κ) : HasSum (fun i ↦ c i j) (‖T.adjoint (f j)‖ ^ (2 : ℕ)) := by
    have h := hasSum_norm_inner_sq_hilbertBasis b (T.adjoint (f j))
    convert h using 2 with i
    simp only [c]
    rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
  have h1 : Summable (fun p : ι × κ ↦ c p.1 p.2) ↔ Summable (fun i ↦ ‖T (b i)‖ ^ (2 : ℕ)) := by
    have htsum (i : ι) : (∑' j, c i j) = ‖T (b i)‖ ^ (2 : ℕ) := (hrow i).tsum_eq
    rw [summable_prod_of_nonneg (fun p ↦ hnn p.1 p.2), and_iff_right (fun i ↦ (hrow i).summable)]
    simp only [htsum]
  have h2 : Summable (fun p : κ × ι ↦ c p.2 p.1) ↔
      Summable (fun j ↦ ‖T.adjoint (f j)‖ ^ (2 : ℕ)) := by
    have htsum (j : κ) : (∑' i, c i j) = ‖T.adjoint (f j)‖ ^ (2 : ℕ) := (hcol j).tsum_eq
    rw [summable_prod_of_nonneg (fun p ↦ hnn p.2 p.1), and_iff_right (fun j ↦ (hcol j).summable)]
    simp only [htsum]
  have h3 : Summable (fun p : κ × ι ↦ c p.2 p.1) ↔ Summable (fun p : ι × κ ↦ c p.1 p.2) :=
    (Equiv.prodComm κ ι).summable_iff (f := fun p : ι × κ ↦ c p.1 p.2)
  exact h1.symm.trans (h3.symm.trans h2)

/-- For an operator with square summable values on a Hilbert basis, the sum of the squared norms
equals the sum of the squared norms of the adjoint on another Hilbert basis. -/
private theorem tsum_sq_basis_eq_tsum_sq_adjoint {E G ι κ : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] (b : HilbertBasis ι ℂ E)
    (f : HilbertBasis κ ℂ G) (T : E →L[ℂ] G) (h : Summable (fun i ↦ ‖T (b i)‖ ^ (2 : ℕ))) :
    ∑' i, ‖T (b i)‖ ^ (2 : ℕ) = ∑' j, ‖T.adjoint (f j)‖ ^ (2 : ℕ) := by
  let c (i : ι) (j : κ) : ℝ := ‖inner ℂ (f j) (T (b i))‖ ^ (2 : ℕ)
  have hnn (i : ι) (j : κ) : 0 ≤ c i j := by positivity
  have hrow (i : ι) : HasSum (c i) (‖T (b i)‖ ^ (2 : ℕ)) :=
    hasSum_norm_inner_sq_hilbertBasis f (T (b i))
  have hcol (j : κ) : HasSum (fun i ↦ c i j) (‖T.adjoint (f j)‖ ^ (2 : ℕ)) := by
    have h := hasSum_norm_inner_sq_hilbertBasis b (T.adjoint (f j))
    convert h using 2 with i
    simp only [c]
    rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
  have htsum (i : ι) : (∑' j, c i j) = ‖T (b i)‖ ^ (2 : ℕ) := (hrow i).tsum_eq
  have htsum' (j : κ) : (∑' i, c i j) = ‖T.adjoint (f j)‖ ^ (2 : ℕ) := (hcol j).tsum_eq
  have hprod : Summable (fun p : ι × κ ↦ c p.1 p.2) := by
    rw [summable_prod_of_nonneg (fun p ↦ hnn p.1 p.2)]
    refine ⟨fun i ↦ (hrow i).summable, ?_⟩
    simp only [htsum]
    exact h
  have hswap : Summable (fun q : κ × ι ↦ c q.2 q.1) :=
    ((Equiv.prodComm κ ι).summable_iff (f := fun p : ι × κ ↦ c p.1 p.2)).mpr hprod
  calc ∑' i, ‖T (b i)‖ ^ (2 : ℕ) = ∑' i, ∑' j, c i j := by simp only [htsum]
    _ = ∑' p : ι × κ, c p.1 p.2 := hprod.tsum_prod.symm
    _ = ∑' q : κ × ι, c q.2 q.1 :=
        ((Equiv.prodComm κ ι).tsum_eq (fun p : ι × κ ↦ c p.1 p.2)).symm
    _ = ∑' j, ∑' i, c i j := hswap.tsum_prod
    _ = ∑' j, ‖T.adjoint (f j)‖ ^ (2 : ℕ) := by simp only [htsum']

/-- Bessel's inequality for Hilbert–Schmidt sums: the squared norms of an operator on a finite
orthonormal family add up to at most the sum over a Hilbert basis. -/
private theorem sum_sq_orthonormal_le_tsum_sq_basis {E G ι κ : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] [Fintype κ] (e : HilbertBasis ι ℂ E)
    (T : E →L[ℂ] G) (h : Summable (fun i ↦ ‖T (e i)‖ ^ (2 : ℕ))) (v : κ → E)
    (hv : Orthonormal ℂ v) :
    ∑ i, ‖T (v i)‖ ^ (2 : ℕ) ≤ ∑' j, ‖T (e j)‖ ^ (2 : ℕ) := by
  obtain ⟨w, g, -⟩ := exists_hilbertBasis ℂ G
  have hadj : Summable (fun j ↦ ‖T.adjoint (g j)‖ ^ (2 : ℕ)) :=
    (summable_sq_basis_iff_summable_sq_adjoint e g T).mp h
  rw [tsum_sq_basis_eq_tsum_sq_adjoint e g T h]
  calc ∑ i, ‖T (v i)‖ ^ (2 : ℕ) = ∑ i, ∑' j, ‖inner ℂ (g j) (T (v i))‖ ^ (2 : ℕ) :=
        Finset.sum_congr rfl fun i _ ↦ (hasSum_norm_inner_sq_hilbertBasis g _).tsum_eq.symm
    _ = ∑' j, ∑ i, ‖inner ℂ (g j) (T (v i))‖ ^ (2 : ℕ) :=
        (Summable.tsum_finsetSum fun i _ ↦ (hasSum_norm_inner_sq_hilbertBasis g _).summable).symm
    _ ≤ ∑' j, ‖T.adjoint (g j)‖ ^ (2 : ℕ) := by
        refine Summable.tsum_le_tsum (fun j ↦ ?_)
          (summable_sum fun i _ ↦ (hasSum_norm_inner_sq_hilbertBasis g _).summable) hadj
        calc ∑ i, ‖inner ℂ (g j) (T (v i))‖ ^ (2 : ℕ)
            = ∑ i, ‖inner ℂ (v i) (T.adjoint (g j))‖ ^ (2 : ℕ) :=
              Finset.sum_congr rfl fun i _ ↦ by
                rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
          _ ≤ ‖T.adjoint (g j)‖ ^ (2 : ℕ) := hv.sum_inner_products_le (T.adjoint (g j))

/-- An operator induced on the quotient by a closed subspace is Hilbert–Schmidt exactly when the
squared norms of the adjoint of the operator on a Hilbert basis of the orthogonal complement are
summable. The operator preserves the subspace, so its adjoint preserves the complement, and the
adjoint of the induced operator sends the class of `e j` to the class of `T† (e j)`. -/
private theorem quotient_hilbertSchmidt_iff_summable_adjoint {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (K : Submodule ℂ E)
    [K.HasOrthogonalProjection] [IsClosed (K : Set E)] [CompleteSpace (E ⧸ K)] (T : E →L[ℂ] E)
    (Tq : (E ⧸ K) →L[ℂ] (E ⧸ K)) (hTq : ∀ x, Tq (K.mkQ x) = K.mkQ (T x))
    (e : HilbertBasis ι ℂ Kᗮ) :
    Tq ∈ hilbertSchmidtOperators (E ⧸ K) (E ⧸ K) ↔
      Summable (fun j ↦ ‖T.adjoint (e j)‖ ^ (2 : ℕ)) := by
  let U := K.quotientEquivOrthogonal
  let g : HilbertBasis ι ℂ (E ⧸ K) := ⟨U.trans e.repr⟩
  have hg (j : ι) : g j = K.mkQ (e j) := by
    classical
    have h1 : g j = U.symm (e j) := by
      rw [← g.repr_symm_single, ← e.repr_symm_single]
      rfl
    rw [h1]
    exact K.quotientEquivOrthogonal_symm_eq_mk _ (e j).2
  have hinv (x : E) (hx : x ∈ K) : T x ∈ K := by
    have h := hTq x
    rw [(Submodule.mkQ_apply K x), (Submodule.Quotient.mk_eq_zero K).mpr hx, map_zero] at h
    exact (Submodule.Quotient.mk_eq_zero K).mp h.symm
  have hinner (z : E) (hz : z ∈ Kᗮ) (y : E) :
      inner ℂ (K.mkQ z) (K.mkQ y) = inner ℂ z y := by
    rw [Submodule.inner_quotient_eq]
    change inner ℂ ((U (Submodule.Quotient.mk z) : Kᗮ) : E) (U (Submodule.Quotient.mk y) : E) = _
    rw [K.quotientEquivOrthogonal_mk z hz]
    set w := U (Submodule.Quotient.mk y)
    have hw : y - (w : E) ∈ K := by
      have h1 : U.symm w = Submodule.Quotient.mk y := U.symm_apply_apply _
      rw [show w = ⟨(w : E), w.2⟩ from rfl, K.quotientEquivOrthogonal_symm_eq_mk _ w.2] at h1
      exact (Submodule.Quotient.eq K).mp h1.symm
    have h0 : inner ℂ z (y - (w : E)) = 0 :=
      inner_eq_zero_symm.mp ((Submodule.mem_orthogonal K z).mp hz _ hw)
    rw [inner_sub_right, sub_eq_zero] at h0
    exact h0.symm
  have hadj (j : ι) : Tq.adjoint (g j) = K.mkQ (T.adjoint (e j)) := by
    have hmem : T.adjoint (e j) ∈ Kᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      rw [ContinuousLinearMap.adjoint_inner_right]
      exact Submodule.inner_right_of_mem_orthogonal (hinv u hu) (e j).2
    refine ext_inner_right ℂ fun q ↦ ?_
    obtain ⟨x, rfl⟩ := K.mkQ_surjective q
    rw [ContinuousLinearMap.adjoint_inner_left, hg, hTq, hinner _ (e j).2, hinner _ hmem,
      ContinuousLinearMap.adjoint_inner_left]
  have hnorm (j : ι) : ‖Tq.adjoint (g j)‖ = ‖T.adjoint (e j)‖ := by
    have hmem : T.adjoint (e j) ∈ Kᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      rw [ContinuousLinearMap.adjoint_inner_right]
      exact Submodule.inner_right_of_mem_orthogonal (hinv u hu) (e j).2
    rw [hadj, ← U.norm_map]
    change ‖U (Submodule.Quotient.mk _)‖ = _
    rw [K.quotientEquivOrthogonal_mk _ hmem]
    rfl
  rw [mem_hilbertSchmidtOperators_iff_summable_basis g,
    summable_sq_basis_iff_summable_sq_adjoint g g Tq]
  simp only [hnorm]

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). Quotient convolution is
Hilbert–Schmidt exactly when, for a Hilbert basis `e` of the orthogonal complement of the theta
closure, the squared norms of the adjoint of convolution on `e` are summable.
Reconstruction: The paper does not state a Hilbert–Schmidt bound. Convolution preserves the
theta closure, so its adjoint preserves the complement and the quotient action is the adjoint
of the adjoint restricted to the complement. Unlike
`spectralStripConvolution_comp_spectralProjection_hilbertSchmidt_iff`, this is an exact
criterion for the Hilbert–Schmidt property of the quotient action, so at `s ≤ 1` it is
equivalent to the open statement `spectralStripConvolution_hilbertSchmidt_of_le_one`.
Deviation: No restriction on the Sobolev order or the width is needed. Nothing in the Lean uses
this statement, and it is not known how it connects with the rest of the proof in Lean. -/
theorem spectralStripConvolution_hilbertSchmidt_iff_summable_adjoint {ι : Type*}
    (e : HilbertBasis ι ℂ (globalThetaSobolev F a hI hs)ᗮ) (φ : BruhatCompactSupport C𝔽) :
    Aq(φ) ∈ hilbertSchmidtOperators H₀ H₀ ↔
      Summable (fun i ↦ ‖(A(φ)).adjoint (e i)‖ ^ (2 : ℕ)) :=
  quotient_hilbertSchmidt_iff_summable_adjoint _ (A(φ)) (Aq(φ))
    (fun x ↦ spectralConvolution_mkQ a hI hs φ x) e

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). Every test acts on the strip
quotient by a nuclear operator exactly when, for a Hilbert basis `e` of the orthogonal complement
of the theta closure and every test `ψ`, the squared norms of the adjoint of `A(ψ)` on `e` are
summable.
Reconstruction: The paper does not state a Hilbert–Schmidt bound. This combines
`spectralStripConvolution_hilbertSchmidt_iff_summable_adjoint` with
`spectralStripConvolution_nuclear_iff_hilbertSchmidt`, and so uses the classical input
`bruhatCompactSupport_convolution_factorization`.
Deviation: No restriction on the Sobolev order or the width is needed. Nothing in the Lean uses
this statement, and it is not known how it connects with the rest of the proof in Lean. -/
theorem spectralStripConvolution_nuclear_iff_summable_adjoint {ι : Type*}
    (e : HilbertBasis ι ℂ (globalThetaSobolev F a hI hs)ᗮ) :
    (∀ φ : BruhatCompactSupport C𝔽, IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ))) ↔
      ∀ ψ : BruhatCompactSupport C𝔽, Summable (fun i ↦ ‖(A(ψ)).adjoint (e i)‖ ^ (2 : ℕ)) := by
  rw [spectralStripConvolution_nuclear_iff_hilbertSchmidt a hα hs]
  exact forall_congr' fun ψ ↦ spectralStripConvolution_hilbertSchmidt_iff_summable_adjoint a hα hs e ψ

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). Let `r j` be the vector of the weighted
space whose inner product is the pairing with the strip jet `u j`. If for every test `ψ` there is
a constant `C` such that, for every finite set `S` of jets, the squared norms of the adjoint of
`A(ψ)` over some orthonormal basis of the span of the `r j` with `j ∈ S` add up to at most `C`,
then every test acts on the strip quotient by a nuclear operator.
Reconstruction: The paper does not state a Hilbert–Schmidt bound. As in
`spectralStripConvolution_nuclear_of_finite_jet_bound`, the Takenaka basis turns the bound into
square summability of the adjoint on a Hilbert basis of the complement, and
`spectralStripConvolution_nuclear_iff_summable_adjoint` applies. The adjoint is expected to be
the natural operator here, although this is not formalized: a pairing with a jet at a zero `ρ`
should intertwine convolution by `ψ` with multiplication by the transform of `ψ` and its
derivatives at `ρ`, so that the adjoint maps the span of the `r j` of the jets at `ρ` into
itself, with eigenvalue the conjugate of the transform at `ρ`. On the span of finitely many `r j`
the hypothesis would then bound the Hilbert–Schmidt norm of a triangular matrix, with no lower
bound needed for the Gram matrix of the `r j`.
Deviation: No restriction on the Sobolev order or the width is needed. Nothing in the Lean uses
this statement, and it is not known how it connects with the rest of the proof in Lean. -/
theorem spectralStripConvolution_nuclear_of_finite_jet_bound_adjoint
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) :
    let u (j : SpectralStripJetIndex χ a α s) :
        CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s true :=
      (spectralStripJet_memLp χ hα hs j).toLp
        (spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)
    (∃ r : SpectralStripJetIndex χ a α s → W,
      (∀ j f, inner ℂ (r j) f = spectralSobolevPairing f (u j)) ∧
      ∀ ψ : BruhatCompactSupport C𝔽, ∃ C : ℝ, ∀ S : Finset (SpectralStripJetIndex χ a α s),
        ∃ (k : ℕ) (b : OrthonormalBasis (Fin k) ℂ (Submodule.span ℂ (r '' S))),
          ∑ i, ‖(A(ψ)).adjoint (b i)‖ ^ 2 ≤ C) →
    ∀ φ : BruhatCompactSupport C𝔽, IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ)) := by
  intro u h
  obtain ⟨r, h⟩ := h
  obtain ⟨hr, hC⟩ := h
  obtain ⟨e, he⟩ := exists_spectralComplement_basis_summable_of_finite_bound a hα hs χ hχ r hr
  refine (spectralStripConvolution_nuclear_iff_summable_adjoint a hα hs e).mpr fun ψ ↦ ?_
  obtain ⟨C, hCψ⟩ := hC ψ
  exact he ((A(ψ)).adjoint) C hCψ

/-- Paper: Theorem 10.4.2.1, p. 459, equation (10.4.2.5). Every test acts on the strip
quotient by a nuclear operator exactly when, for every test `ψ`, the squared norms of the adjoint
of `A(ψ)` over an orthonormal basis of the span of the jet representers `r j` with `j ∈ S` are
bounded uniformly over the finite sets `S` of jets.
Reconstruction: The paper does not state a Hilbert–Schmidt bound. One direction is
`spectralStripConvolution_nuclear_of_finite_jet_bound_adjoint`. Conversely the spans lie in the
orthogonal complement of the theta closure (`spectralStripJet_commonKernel`), and by Bessel's
inequality the finite sums are at most the full sum over a Hilbert basis, which is finite by
`spectralStripConvolution_nuclear_iff_summable_adjoint`. So the finite-dimensional bound is
equivalent to the open statement `spectralStripConvolution_nuclear_of_le_one`, given the
classical input `bruhatCompactSupport_convolution_factorization`.
Deviation: No restriction on the Sobolev order or the width is needed. Nothing in the Lean uses
this statement, and it is not known how it connects with the rest of the proof in Lean. -/
theorem spectralStripConvolution_nuclear_iff_finite_jet_bound_adjoint
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) :
    let u (j : SpectralStripJetIndex χ a α s) :
        CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s true :=
      (spectralStripJet_memLp χ hα hs j).toLp
        (spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)
    (∀ φ : BruhatCompactSupport C𝔽, IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ))) ↔
      ∃ r : SpectralStripJetIndex χ a α s → W,
        (∀ j f, inner ℂ (r j) f = spectralSobolevPairing f (u j)) ∧
        ∀ ψ : BruhatCompactSupport C𝔽, ∃ C : ℝ, ∀ S : Finset (SpectralStripJetIndex χ a α s),
          ∃ (k : ℕ) (b : OrthonormalBasis (Fin k) ℂ (Submodule.span ℂ (r '' S))),
            ∑ i, ‖(A(ψ)).adjoint (b i)‖ ^ 2 ≤ C := by
  intro u
  refine ⟨fun hnuc ↦ ?_, fun h ↦ spectralStripConvolution_nuclear_of_finite_jet_bound_adjoint
    a hα hs χ hχ h⟩
  obtain ⟨r, n, e, hr, -⟩ := exists_spectralComplement_takenakaBasis a hα hs χ hχ
  refine ⟨r, hr, fun ψ ↦ ?_⟩
  have hsum := (spectralStripConvolution_nuclear_iff_summable_adjoint a hα hs e).mp hnuc ψ
  refine ⟨∑' j, ‖(A(ψ)).adjoint (e j)‖ ^ (2 : ℕ), fun S ↦ ?_⟩
  have hK := spectralStripJet_commonKernel χ hχ (a := a) hα hs
  have hrΘ (j : SpectralStripJetIndex χ a α s) : r j ∈ (globalThetaSobolev F a hI hs)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro θ hθ
    rw [hr]
    exact (hK θ).mp hθ j
  have hle : Submodule.span ℂ (r '' S) ≤ (globalThetaSobolev F a hI hs)ᗮ :=
    Submodule.span_le.mpr (by rintro _ ⟨j, -, rfl⟩; exact hrΘ j)
  have : FiniteDimensional ℂ (Submodule.span ℂ (r '' S)) :=
    FiniteDimensional.span_of_finite ℂ (S.finite_toSet.image r)
  let b := stdOrthonormalBasis ℂ (Submodule.span ℂ (r '' S))
  refine ⟨_, b, ?_⟩
  let v (i : Fin (Module.finrank ℂ (Submodule.span ℂ (r '' S)))) :
      (globalThetaSobolev F a hI hs)ᗮ := ⟨b i, hle (b i).2⟩
  have hv : Orthonormal ℂ v := ⟨fun i ↦ b.orthonormal.1 i, fun i j hij ↦ b.orthonormal.2 hij⟩
  exact sum_sq_orthonormal_le_tsum_sq_basis e
    ((A(ψ)).adjoint.comp (globalThetaSobolev F a hI hs)ᗮ.subtypeL) hsum v hv

/-- Paper: Theorem 10.4.2.1, p. 459. Spectral projection after convolution is nuclear.
This follows from the statement `spectralStripConvolution_nuclear_of_le_one` by (10.4.2.5).
Deviation: This is the part of the printed range with `0 ≤ s ≤ 1`. The operator is independent
of the cutoff. -/
theorem spectralProjection_convolution_nuclear_of_le_one (_hs₁ : s ≤ 1) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator ((spectralProjection (F := F) a hα hs).comp (A(φ))) :=
  spectralProjection_convolution_nuclear a hα hs φ
    (spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ)

/-- Paper: Theorem 10.4.2.1, p. 459. Spectral projection after convolution is nuclear.
Deviation: This checks the uncut conclusion on the range `1 < s` of the strip theorem. -/
theorem spectralProjection_convolution_nuclear_of_one_lt (_hs₁ : 1 < s) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator ((spectralProjection (F := F) a hα hs).comp (A(φ))) :=
  spectralProjection_convolution_nuclear a hα hs φ
    (spectralStripConvolution_nuclear_of_summable_clusterTraceNorms a hα hs φ)

/-- Paper: Theorem 10.4.2.1, p. 459. At each admissible cutoff, spectral truncation
after convolution is nuclear. This follows from the open `spectralStripConvolution_nuclear_of_le_one`
by composing the projected convolution with cutoff multiplication.
Deviation: The range here is `0 ≤ s ≤ 1`. The real cutoff uses the profile of Definition 9.3.3.1. -/
theorem spectralTruncatedConvolution_nuclear_of_le_one (_hs₁ : s ≤ 1)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (_hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (spectralTruncatedConvolution a hα hs hρ φ) :=
  spectralTruncatedConvolution_nuclear a hα hs hρ φ
    (spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ)

/-- Paper: Theorem 10.4.2.1, p. 459. Spectral truncation after convolution is nuclear.
Deviation: At `1 < s` the existing theorem applies to real cutoffs even without the inner-band inequality. -/
theorem spectralTruncatedConvolution_nuclear_of_one_lt (_hs₁ : 1 < s)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (spectralTruncatedConvolution a hα hs hρ φ) :=
  spectralTruncatedConvolution_nuclear a hα hs hρ φ
    (spectralStripConvolution_nuclear_of_summable_clusterTraceNorms a hα hs φ)

/-- Paper: Theorem 10.4.2.1, p. 459. At each admissible cutoff, geometric truncation
after convolution is nuclear. Given the open `spectralStripConvolution_nuclear_of_le_one`,
this follows by subtracting the spectral summand from cutoff convolution.
Deviation: The range here is `0 ≤ s ≤ 1`, with the real cutoff of Definition 9.3.3.1. -/
theorem geometricTruncatedConvolution_nuclear_of_le_one (_hs₁ : s ≤ 1)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (geometricTruncatedConvolution a hα hs hρ φ) :=
  geometricTruncatedConvolution_nuclear a hα hs hρ hband φ
    (spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ)

/-- Paper: Theorem 10.4.2.1, p. 459. Geometric truncation after convolution is nuclear.
Deviation: This checks the real-cutoff conclusion at `1 < s` using the strip theorem. -/
theorem geometricTruncatedConvolution_nuclear_of_one_lt (_hs₁ : 1 < s)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (geometricTruncatedConvolution a hα hs hρ φ) :=
  geometricTruncatedConvolution_nuclear a hα hs hρ hband φ
    (spectralStripConvolution_nuclear_of_summable_clusterTraceNorms a hα hs φ)

local notation "traceSplit(" hρ ", " φ ")" =>
  (let T := (M(hρ)).comp (A(φ))
   let G := geometricTruncatedConvolution a hα hs hρ φ
   let S := spectralTruncatedConvolution a hα hs hρ φ
   ∃ (hT : IsNuclearOperator T) (hG : IsNuclearOperator G) (hS : IsNuclearOperator S),
     hilbertTrace (H := W) ⟨T, hT⟩ =
       hilbertTrace (H := W) ⟨G, hG⟩ + hilbertTrace (H := W) ⟨S, hS⟩)

/-- Paper: Theorem 10.4.2.1, p. 459. At an admissible cutoff the trace of cutoff convolution
is the sum of the geometric and spectral traces, as in (10.4.2.3). The statement
`spectralStripConvolution_nuclear_of_le_one` supplies the hypothesis for the trace split.
Deviation: The order is restricted to `0 ≤ s ≤ 1` and the three nuclearity witnesses are
part of the conclusion for the real cutoff. -/
theorem truncatedConvolution_trace_split_of_le_one (_hs₁ : s ≤ 1)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    traceSplit(hρ, φ) :=
  truncatedConvolution_trace_split a hα hs hρ hband φ
    (spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ)

/-- Paper: Theorem 10.4.2.1, p. 459. The nuclear trace splits as in (10.4.2.3).
Deviation: This checks the identity with real cutoffs and all three nuclearity witnesses at `1 < s`. -/
theorem truncatedConvolution_trace_split_of_one_lt (_hs₁ : 1 < s)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    traceSplit(hρ, φ) :=
  truncatedConvolution_trace_split a hα hs hρ hband φ
    (spectralStripConvolution_nuclear_of_summable_clusterTraceNorms a hα hs φ)

section Limits

variable (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)) (ε : ℝ → ℝ)
  (ρ : ℝ → IdeleClassGroup (𝓞 F) F → ℝ)

local notation "traceLimit(" op ")" =>
  (∃ (hq : IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ))) (t : ℝ → ℂ),
    (∀ᶠ R in atTop, ∃ hc : IsModulatedCutoff m𝔽 R (ε R) (ρ R),
      let T := (op) a hα hs hc φ
      ∃ hT : IsNuclearOperator T, t R = hilbertTrace (H := W) ⟨T, hT⟩) ∧
    Tendsto t atTop (𝓝 (hilbertTrace (H := H₀) ⟨Aq(φ), hq⟩)))

variable (hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
  (hρ : ∀ᶠ R in atTop, IsModulatedCutoff (continuousIdeleClassNorm F) R (ε R) (ρ R) ∧ band(R, ε R))

include hε hρ

/-- Paper: Theorem 10.4.2.2, p. 460. The traces of cutoff projection after convolution tend
to the trace of convolution on the strip quotient, as in (10.4.2.9). This follows from
the statement `spectralStripConvolution_nuclear_of_le_one`.
Deviation: At `0 ≤ s ≤ 1` this asserts quotient nuclearity along with the limit. The proof
on p. 461 uses the strip quotient. Real cutoffs and their traces need only agree with the
prescribed data eventually as the radius tends to infinity. -/
theorem spectralTruncatedConvolution_trace_tendsto_of_le_one (_hs₁ : s ≤ 1) :
    traceLimit(spectralTruncatedConvolution) := by
  have hq := spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ
  exact ⟨hq, spectralTruncatedConvolution_trace_tendsto a hα hs φ hq ε ρ hε hρ⟩

/-- Paper: Theorem 10.4.2.2, p. 460. The projection-after-convolution traces tend to the strip quotient trace.
Deviation: This checks the eventual real-cutoff formulation at `1 < s` with the nuclearity witness from §10.3. -/
theorem spectralTruncatedConvolution_trace_tendsto_of_one_lt (_hs₁ : 1 < s) :
    traceLimit(spectralTruncatedConvolution) := by
  have hq := spectralStripConvolution_nuclear_of_summable_clusterTraceNorms a hα hs φ
  exact ⟨hq, spectralTruncatedConvolution_trace_tendsto a hα hs φ hq ε ρ hε hρ⟩

/-- Paper: Theorem 10.4.2.8, p. 463. The traces of cutoff convolution after spectral
projection tend to the strip quotient trace, as in (10.4.2.20). This follows from the
statement `spectralStripConvolution_nuclear_of_le_one`.
Deviation: At `0 ≤ s ≤ 1` this asserts quotient nuclearity along with the limit. The real
cutoff conditions and agreement with the nuclear traces are eventual. -/
theorem spectralRestriction_trace_tendsto_of_le_one (_hs₁ : s ≤ 1) :
    traceLimit(spectralRestriction) := by
  have hq := spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ
  exact ⟨hq, spectralRestriction_trace_tendsto a hα hs φ hq ε ρ hε hρ⟩

/-- Paper: Theorem 10.4.2.8, p. 463. The convolution-after-projection traces tend to the strip quotient trace.
Deviation: This checks the eventual real-cutoff formulation at `1 < s` with the nuclearity witness from §10.3. -/
theorem spectralRestriction_trace_tendsto_of_one_lt (_hs₁ : 1 < s) :
    traceLimit(spectralRestriction) := by
  have hq := spectralStripConvolution_nuclear_of_summable_clusterTraceNorms a hα hs φ
  exact ⟨hq, spectralRestriction_trace_tendsto a hα hs φ hq ε ρ hε hρ⟩

end Limits

end RiemannMasullo.Isolated
