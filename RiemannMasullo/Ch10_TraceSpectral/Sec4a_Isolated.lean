module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppC_LCTVS.Sec3b_HilbertSchmidtProduct

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

/-- Classical input: Dixmier and Malliavin, *Factorisations de fonctions et de vecteurs
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
  sorry

end ConvolutionFactorization

/-- Classical input: the Dixmier–Malliavin factorization theorem. Every compactly supported
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
