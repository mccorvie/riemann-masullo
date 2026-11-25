module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppC_LCTVS.Sec3b_HilbertSchmidtProduct
import RiemannMasullo.ForMathlib.Analysis.Distribution.CompactSmoothFactorization
import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import RiemannMasullo.AppD_SchwartzBruhat.Sec1d

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

section Elementary

open scoped ContDiff

variable {Q : Type*} [CommGroup Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (e : ElementaryLCAPresentation Q)
local notation "E" => EuclideanSpace ℝ (Fin e.realDim)
local notation "T" => (Fin e.torusDim → AddCircle (1 : ℝ))
local notation "A" => E × T
local notation "D" => (Fin e.latticeRank → ℤ) × e.finiteFactor
local notation "H" => ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
local instance : MeasurableSpace e.finiteFactor := borel _
local instance : BorelSpace e.finiteFactor := ⟨rfl⟩

private def FiberSmooth (f : H → ℂ) : Prop :=
  ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun u ↦ f (elementaryCover u a b))

private def ConnectedSmooth (g : A → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (fun x : E × (Fin e.torusDim → ℝ) ↦ g (DixmierMalliavin.Torus.cover x))

/-- The analytic factorization uses the product Haar measure of Appendix D. -/
private def ProductDM : Prop :=
  ∀ f : H → ℂ, FiberSmooth e f → HasCompactSupport f → f ∈ AddSubmonoid.closure
    {h | ∃ u v : H → ℂ, FiberSmooth e u ∧ HasCompactSupport u ∧
      FiberSmooth e v ∧ HasCompactSupport v ∧
      h = fun x ↦ ∫ y : H, u y * v (-y + x) ∂(productHaar e)}

private theorem productDM_of_connected
    (base : ∀ g : A → ℂ, ConnectedSmooth e g → HasCompactSupport g →
      g ∈ AddSubmonoid.closure {h | ∃ u v : A → ℂ,
        ConnectedSmooth e u ∧ HasCompactSupport u ∧ ConnectedSmooth e v ∧ HasCompactSupport v ∧
        h = DixmierMalliavin.Discrete.conv ((volume : Measure E).prod
          (Measure.pi fun _ : Fin e.torusDim ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle))) u v}) :
    ProductDM e := by
  classical
  let s := Homeomorph.prodAssoc E T D
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin e.torusDim ↦ ℝ)
  have hfib (f : H → ℂ) : FiberSmooth e f ↔
      ∀ j : D, ConnectedSmooth e (fun x : A ↦ f (s (x,j))) := by
    constructor
    · intro hf ⟨a,b⟩
      exact (hf a b).comp (contDiff_fst.prodMk (L.symm.contDiff.comp contDiff_snd))
    · intro hf a b
      exact (show ContDiff ℝ (⊤ : ℕ∞) _ from hf (a,b)).comp
        (contDiff_fst.prodMk (L.contDiff.comp contDiff_snd))
  have hcircle : (volume : Measure (AddCircle (1 : ℝ))) = AddCircle.haarAddCircle := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
  have htorus : (volume : Measure T) = Measure.pi
      (fun _ : Fin e.torusDim ↦ (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ)))) := by
    change Measure.pi (fun _ : Fin e.torusDim ↦ (volume : Measure (AddCircle (1 : ℝ)))) = _
    simp only [hcircle]
  rw [← htorus] at base
  intro f hf hc
  let C := AddSubmonoid.closure {h : H → ℂ | ∃ u v : H → ℂ,
    FiberSmooth e u ∧ HasCompactSupport u ∧ FiberSmooth e v ∧ HasCompactSupport v ∧
    h = fun x ↦ ∫ y : H, u y * v (-y + x) ∂(productHaar e)}
  have hall := DixmierMalliavin.Discrete.finite_slice_factorization
    ((volume : Measure E).prod (volume : Measure T)) (ConnectedSmooth e)
    (show ConnectedSmooth e 0 from contDiff_const) (fun z : A × D ↦ f (s z))
    (hc.comp_homeomorph s) ((hfib f).mp hf) base
  apply AddSubmonoid.closure_induction (motive := fun h _ ↦ (fun x : H ↦ h (s.symm x)) ∈ C)
    _ _ _ hall
  · rintro _ ⟨u, v, hu, hcu, hv, hcv, rfl⟩
    refine AddSubmonoid.subset_closure ⟨fun x ↦ u (s.symm x), fun x ↦ v (s.symm x),
      (hfib _).mpr hu, hcu.comp_homeomorph s.symm, (hfib _).mpr hv,
      hcv.comp_homeomorph s.symm, ?_⟩
    funext x
    exact (measurePreserving_prodAssoc (volume : Measure E) (volume : Measure T)
      (Measure.count : Measure D)).integral_comp' (fun y : H ↦ u (s.symm y) * v (s.symm (-y + x)))
  · exact C.zero_mem
  · intro a b _ _ ha hb
    exact C.add_mem ha hb

private theorem elementaryFactorization_of_productDM (hDM : ProductDM e)
    (ν : @Measure Q (borel _)) (hν : letI : MeasurableSpace Q := borel _; ν.IsHaarMeasure) :
    ElementaryFactorization e ν := by
  classical
  let : MeasurableSpace Q := borel _
  let : BorelSpace Q := ⟨rfl⟩
  let : ν.IsHaarMeasure := hν
  let : T2Space (Multiplicative H) := inferInstanceAs (T2Space H)
  let : LocallyCompactSpace (Multiplicative H) := inferInstanceAs (LocallyCompactSpace H)
  let : T2Space Q := e.equiv.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace Q := e.equiv.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let : BorelSpace (Multiplicative H) := by
    have : BorelSpace D := inferInstance
    have : BorelSpace (T × D) := inferInstance
    exact inferInstanceAs (BorelSpace H)
  let η := ν.map e.equiv
  let σ := productHaar e
  let : η.IsHaarMeasure := e.equiv.isHaarMeasure_map ν
  let : σ.IsHaarMeasure := productHaar_isHaar e
  let k := σ.haarScalarFactor η
  have hscale : σ = k • η := Measure.isMulLeftInvariant_eq_smul σ η
  let V (f : H → ℂ) (x : Q) := f (Multiplicative.toAdd (e.equiv x))
  let C := AddSubmonoid.closure {h : Q → ℂ | ∃ u v : SchwartzBruhatStage e,
    HasCompactSupport (V u) ∧ HasCompactSupport (V v) ∧ h = lcaConvolution ν (V u) (V v)}
  intro f hc
  change V f ∈ C
  have hc' : HasCompactSupport (f : H → ℂ) := by
    have ht := (show HasCompactSupport (V f) from hc).comp_homeomorph e.equiv.toHomeomorph.symm
    have ht' : HasCompactSupport (fun y : H ↦ V f (e.equiv.symm (Multiplicative.ofAdd y))) := ht
    simpa [V] using ht'
  apply AddSubmonoid.closure_induction (motive := fun h _ ↦ V h ∈ C) _ _ _
    (hDM f f.property.1 hc')
  · rintro h ⟨u, v, hu, hcu, hv, hcv, rfl⟩
    let u' : H → ℂ := fun y ↦ (k : ℂ) * u y
    have hcu' : HasCompactSupport u' := hcu.mul_left (f := fun _ ↦ (k : ℂ))
    let U : SchwartzBruhatStage e := ⟨u', mem_elementarySchwartzSubmodule_of_fiberwise_contDiff u'
      (fun a b ↦ contDiff_const.mul (hu a b)) hcu'⟩
    let Vstage : SchwartzBruhatStage e :=
      ⟨v, mem_elementarySchwartzSubmodule_of_fiberwise_contDiff v hv hcv⟩
    apply AddSubmonoid.subset_closure
    refine ⟨U, Vstage, hcu'.comp_homeomorph e.equiv.toHomeomorph,
      hcv.comp_homeomorph e.equiv.toHomeomorph, ?_⟩
    funext x
    let p (y : Multiplicative H) := u y.toAdd * v (-(y.toAdd) + (e.equiv x).toAdd)
    change (∫ y, p y ∂σ) = ∫ z, ((k : ℂ) * u (e.equiv z).toAdd) * v (e.equiv (z⁻¹ * x)).toAdd ∂ν
    rw [hscale, integral_smul_nnreal_measure]
    have hmap : (∫ y, p y ∂η) = ∫ z, p (e.equiv z) ∂ν :=
      integral_map_equiv e.equiv.toHomeomorph.toMeasurableEquiv p
    rw [hmap, NNReal.smul_def, Complex.real_smul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    rw [map_mul, map_inv, mul_assoc]; rfl
  · exact C.zero_mem
  · intro h g _ _ ih ig
    exact C.add_mem ih ig

end Elementary

/-- Dixmier and Malliavin, *Factorisations de fonctions et de vecteurs
indéfiniment différentiables*, Bull. Sci. Math. (2) 102 (1978), Théorème 3.1. On the elementary
abelian Lie group presented by `e` (a product of Euclidean, torus, lattice and finite factors),
each compactly supported smooth function is a finite sum of convolutions of two such functions
for the given Haar measure. Smooth functions of compact support belong to the elementary
Schwartz stage; the membership below is in the algebraic additive closure. -/
private theorem elementary_compact_convolution_factorization {Q : Type*} [CommGroup Q]
    [TopologicalSpace Q] [IsTopologicalGroup Q] (e : ElementaryLCAPresentation Q)
    (ν : @Measure Q (borel _)) :
    letI : MeasurableSpace Q := borel _
    ν.IsHaarMeasure →
      let V (f : SchwartzBruhatStage e) (x : Q) := f (Multiplicative.toAdd (e.equiv x))
      ∀ f : SchwartzBruhatStage e, HasCompactSupport (V f) →
        V f ∈ AddSubmonoid.closure {θ : Q → ℂ | ∃ u v : SchwartzBruhatStage e,
          HasCompactSupport (V u) ∧ HasCompactSupport (V v) ∧ θ = lcaConvolution ν (V u) (V v)} := by
  intro hν
  exact elementaryFactorization_of_productDM e
    (productDM_of_connected e (fun g hg hc ↦
      DixmierMalliavin.Torus.compact_euclidean_torus_factorization e.realDim e.torusDim g hg hc))
    ν hν

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
The structural quotient and zero extension reduce this to factorization on the elementary Lie group. -/
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
Gap: Not proved in Lean. The argument is posted on #7405 as mathematics and was checked there
by other contributors, not by Lean; the library has no Hardy or Dirichlet-type space of the
strip in which to carry it out. Nothing in the Lean outside this file uses this statement. -/
theorem spectralStripConvolution_hilbertSchmidt_of_le_one (_hs₁ : s ≤ 1)
    (φ : BruhatCompactSupport C𝔽) : Aq(φ) ∈ hilbertSchmidtOperators H₀ H₀ := by
  sorry

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
Proved from the Hilbert–Schmidt statement `spectralStripConvolution_hilbertSchmidt_of_le_one`
and the Dixmier–Malliavin factorization `bruhatCompactSupport_convolution_factorization`: a
product of two Hilbert–Schmidt operators is nuclear. At width zero the statement is also
`spectralStripConvolution_nuclear_of_zero_width`. Nothing in the Lean uses this statement, and
it is not known how it connects with the rest of the proof in Lean; in the paper it is used on
pp. 459–461, 463–464, 503, 519–520. -/
theorem spectralStripConvolution_nuclear_of_le_one (_hs₁ : s ≤ 1) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (E := H₀) (F := H₀) (Aq(φ)) := by
  have hlin := spectralConvolution_isLinear (F := F) a hI hs
  induction bruhatCompactSupport_convolution_factorization φ using
    AddSubmonoid.closure_induction with
  | mem θ h =>
    obtain ⟨u, v, huv⟩ := h
    rw [spectralConvolution_lcaConvolution a hα hs θ u v huv]
    exact nuclear_hilbertSchmidt_comp
      ⟨_, spectralStripConvolution_hilbertSchmidt_of_le_one a hα hs _hs₁ u⟩
      ⟨_, spectralStripConvolution_hilbertSchmidt_of_le_one a hα hs _hs₁ v⟩
  | zero =>
    rw [hlin.map_zero]
    exact (nuclearEndomorphisms _).zero_mem
  | add x y _ _ hx hy =>
    rw [hlin.map_add]
    exact (nuclearEndomorphisms _).add_mem hx hy

/-- Paper: Theorem 10.4.2.1, p. 459. Spectral projection after convolution is nuclear.
This follows from the open statement `spectralStripConvolution_nuclear_of_le_one` by (10.4.2.5).
Deviation: This is the part of the printed range with `0 ≤ s ≤ 1`. The operator is independent
of the cutoff. -/
theorem spectralProjection_convolution_nuclear_of_le_one (_hs₁ : s ≤ 1) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator ((spectralProjection (F := F) a hα hs).comp (A(φ))) :=
  spectralProjection_convolution_nuclear a hα hs φ
    (spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ)

/-- Paper: Theorem 10.4.2.1, p. 459. Spectral projection after convolution is nuclear.
Deviation: This checks the uncut conclusion on the range `1 < s` of the strip theorem. -/
theorem spectralProjection_convolution_nuclear_of_one_lt (hs₁ : 1 < s) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator ((spectralProjection (F := F) a hα hs).comp (A(φ))) :=
  RiemannMasullo.spectralProjection_convolution_nuclear_of_one_lt a hα hs₁ φ

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
theorem spectralTruncatedConvolution_nuclear_of_one_lt (hs₁ : 1 < s)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (spectralTruncatedConvolution a hα hs hρ φ) :=
  RiemannMasullo.spectralTruncatedConvolution_nuclear_of_one_lt a hα hs₁ hρ φ

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
theorem geometricTruncatedConvolution_nuclear_of_one_lt (hs₁ : 1 < s)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    IsNuclearOperator (geometricTruncatedConvolution a hα hs hρ φ) :=
  RiemannMasullo.geometricTruncatedConvolution_nuclear_of_one_lt a hα hs₁ hρ hband φ

local notation "traceSplit(" hρ ", " φ ")" =>
  (let T := (M(hρ)).comp (A(φ))
   let G := geometricTruncatedConvolution a hα hs hρ φ
   let S := spectralTruncatedConvolution a hα hs hρ φ
   ∃ (hT : IsNuclearOperator T) (hG : IsNuclearOperator G) (hS : IsNuclearOperator S),
     hilbertTrace (H := W) ⟨T, hT⟩ =
       hilbertTrace (H := W) ⟨G, hG⟩ + hilbertTrace (H := W) ⟨S, hS⟩)

/-- Paper: Theorem 10.4.2.1, p. 459. At an admissible cutoff the trace of cutoff convolution
is the sum of the geometric and spectral traces, as in (10.4.2.3). The open statement
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
theorem truncatedConvolution_trace_split_of_one_lt (hs₁ : 1 < s)
    (hρ : IsModulatedCutoff m𝔽 Λ ε ρ) (hband : band(Λ, ε)) (φ : BruhatCompactSupport C𝔽) :
    traceSplit(hρ, φ) :=
  RiemannMasullo.truncatedConvolution_trace_split_of_one_lt a hα hs₁ hρ hband φ

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
the open statement `spectralStripConvolution_nuclear_of_le_one`.
Deviation: At `0 ≤ s ≤ 1` this asserts quotient nuclearity along with the limit. The proof
on p. 461 uses the strip quotient. Real cutoffs and their traces need only agree with the
prescribed data eventually as the radius tends to infinity. -/
theorem spectralTruncatedConvolution_trace_tendsto_of_le_one (_hs₁ : s ≤ 1) :
    traceLimit(spectralTruncatedConvolution) := by
  have hq := spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ
  exact ⟨hq, spectralTruncatedConvolution_trace_tendsto a hα hs φ hq ε ρ hε hρ⟩

/-- Paper: Theorem 10.4.2.2, p. 460. The projection-after-convolution traces tend to the strip quotient trace.
Deviation: This checks the eventual real-cutoff formulation at `1 < s` with the nuclearity witness from §10.3. -/
theorem spectralTruncatedConvolution_trace_tendsto_of_one_lt (hs₁ : 1 < s) :
    traceLimit(spectralTruncatedConvolution) :=
  ⟨spectralStripConvolution_nuclear a hα hs₁ φ,
    RiemannMasullo.spectralTruncatedConvolution_trace_tendsto_of_one_lt a hα hs₁ φ ε ρ hε hρ⟩

/-- Paper: Theorem 10.4.2.8, p. 463. The traces of cutoff convolution after spectral
projection tend to the strip quotient trace, as in (10.4.2.20). This follows from the
open statement `spectralStripConvolution_nuclear_of_le_one`.
Deviation: At `0 ≤ s ≤ 1` this asserts quotient nuclearity along with the limit. The real
cutoff conditions and agreement with the nuclear traces are eventual. -/
theorem spectralRestriction_trace_tendsto_of_le_one (_hs₁ : s ≤ 1) :
    traceLimit(spectralRestriction) := by
  have hq := spectralStripConvolution_nuclear_of_le_one a hα hs _hs₁ φ
  exact ⟨hq, spectralRestriction_trace_tendsto a hα hs φ hq ε ρ hε hρ⟩

/-- Paper: Theorem 10.4.2.8, p. 463. The convolution-after-projection traces tend to the strip quotient trace.
Deviation: This checks the eventual real-cutoff formulation at `1 < s` with the nuclearity witness from §10.3. -/
theorem spectralRestriction_trace_tendsto_of_one_lt (hs₁ : 1 < s) :
    traceLimit(spectralRestriction) :=
  ⟨spectralStripConvolution_nuclear a hα hs₁ φ,
    RiemannMasullo.spectralRestriction_trace_tendsto_of_one_lt a hα hs₁ φ ε ρ hε hρ⟩

end Limits

end RiemannMasullo.Isolated
