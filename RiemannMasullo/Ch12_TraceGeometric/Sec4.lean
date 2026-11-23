module

public import RiemannMasullo.Ch12_TraceGeometric.Sec2
public import RiemannMasullo.Ch11_ShellStructure.Sec2b
public import RiemannMasullo.AppB_AnalyticNT.Sec4b
public import RiemannMasullo.Ch06_LocalGlobal.Sec1
import all RiemannMasullo.AppB_AnalyticNT.Sec4b
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # S-local trace calculation

Masullo, §§12.3–12.4, pp. 514–519. The additive kernel, its sharp orbital mass,
and the diagonal integral on the idele quotient use different measures.
-/

@[expose] public noncomputable section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff ENNReal NNReal NumberField.AdeleRing SchwartzMap Topology

namespace RiemannMasullo

-- TODO(paper-gap): §12.3, p. 514, contains only the heading and footnote 1
-- asking to include the section. No global-to-S-local comparison is stated.

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instSIdeleLocallyCompactSec1
  instFiniteCompletionUnitsLocallyCompactSec4b

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Hₛ" =>
  Subgroup.map (Units.map ((adeleProjection F S).comp (integralAdelesOutside F S).subtype).toMonoidHom)
    (Units.map (integralAdeleDiagonal F S).toMonoidHom).range
local notation "classAtS(" g ")" => (QuotientGroup.mk (sIdeleInsertion F S g) : C𝔽)
local notation "modS(" x ")" => ((∏ w : InfinitePlace F, ‖(x : Aₛ).1 w‖ ^ w.mult) *
  ∏ v : S, ‖(x : Aₛ).2 v‖)
local notation "normS(" x ")" => (((sIdeleNorm F S x).val : ℝ))
local notation "νₛ" => sAdditiveTamagawaMeasure F S
local notation "μₛ" => sMultiplicativeTamagawaMeasure F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "volume₁" => ((sLocalNormOneQuotientMeasure F S) univ).toReal
local notation "ψₛ" => sAdeleStandardCharacter F S
local notation "fourierₛ" => tamagawaFourier νₛ ψₛ
local notation "band(" L ")" => sLocalPWProductRegion (F := F) S L
local notation "testₛ" => SchwartzBruhat (Multiplicative Aₛ)
local notation "testAt(" f "," x ")" => (f : testₛ) (Multiplicative.ofAdd x)

local instance instSIdeleT2Sec4 : T2Space Iₛ := (sIdeleGroup_description F S).2.1

/-- Paper: (12.4.1.4), p. 515. The restriction of an outside-unit-invariant test admits
a compactly supported Bruhat lift whose S-unit periodization recovers the restriction.
Deviation: The inserted S-idele evaluates the global test before taking the quotient. -/
theorem exists_sLocalTraceLift
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (φ : BruhatCompactSupport C𝔽)
    (_hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c) :
    ∃ f : BruhatCompactSupport Iₛ, ∀ g : Iₛ,
      HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))) := by sorry

-- TODO(paper-gap): The operator A on p. 515 has an extra factor |x|^(1/2)
-- in its output. Step I computes the scalar kernel with that factor removed.
-- The asserted factorization through the revised Proposition 5.3.4.4 needs a
-- comparison of the actual norm-weighted spaces and operators.

/-- Paper: (12.4.1.5) and (12.4.1.7), p. 516. Acting on a test integrates its values
at the translated points against the lift weighted by the inverse square-root norm.
Deviation: The definition gives the scalar pairing of the distributional kernel. -/
def sLocalTraceDilationKernel (f : BruhatCompactSupport Iₛ) (b : Aₛ → ℂ) (x : Aₛ) : ℂ :=
  ∫ g : Iₛ, f.val g / (Real.sqrt (normS(g)) : ℂ) * b ((g⁻¹).val * x) ∂μₛ

/-- Continuity of a Bruhat-smooth function follows already from order zero
(ported from the private `continuous_of_bruhatSmooth` in Ch09 Sec3). -/
private theorem sLocalTraceDilationKernel_apply_zero_continuous {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    {f : G → ℂ} (hf : IsBruhatSmooth f) : Continuous f := by
  classical
  obtain ⟨k, hk, _, hdesc⟩ := hf 0
  have hkc := hk.isCompact
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨U, hU, hU₁⟩ := exists_compact_mem_nhds (1 : G)
  let K := insert x (U ∪ (k : Set G))
  let H := Subgroup.closure K
  have hK : K ⊆ (H : Set G) := Subgroup.subset_closure
  have hK₁ : K ∈ 𝓝 (1 : G) := mem_of_superset hU₁ (subset_union_left.trans (subset_insert ..))
  have hH : IsOpen (H : Set G) := H.isOpen_of_mem_nhds (mem_of_superset hK₁ hK)
  let a : BruhatStructuralPair G :=
    ⟨(H, OrderDual.toDual k), hH,
      ⟨Subtype.val ⁻¹' K, continuous_subtype_val.continuousAt.preimage_mem_nhds hK₁,
        (H.isClosed_of_isOpen hH).isClosedEmbedding_subtypeVal.isCompact_preimage
          ((hU.union hkc).insert x), Subgroup.closure_preimage_eq_top K⟩,
      hk, subset_union_right.trans ((subset_insert ..).trans hK)⟩
  let e := Classical.choice a.elementary
  obtain ⟨f₀, hval, hsm⟩ := hdesc a rfl
  let q : EuclideanSpace ℝ (Fin e.torusDim) → (Fin e.torusDim → AddCircle (1 : ℝ)) :=
    fun t i ↦ (t i : AddCircle (1 : ℝ))
  have hq : IsOpenQuotientMap q :=
    (IsOpenQuotientMap.piMap (fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk)).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin e.torusDim ↦ ℝ)).toHomeomorph.isOpenQuotientMap
  have hmodel : Continuous (fun y : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor ↦
      f₀ (e.equiv.symm (Multiplicative.ofAdd y))) := by
    rw [← (Homeomorph.prodAssoc _ _ _).isOpenQuotientMap.continuous_comp_iff]
    refine continuous_prod_of_discrete_right.mpr fun zd ↦ ?_
    rw [← ((IsOpenQuotientMap.id (X := EuclideanSpace ℝ (Fin e.realDim))).prodMap hq).continuous_comp_iff]
    exact (hsm e zd.1 zd.2).continuous
  have hf₀ : Continuous f₀ := by
    simpa only [Function.comp_def, ofAdd_toAdd, ContinuousMulEquiv.symm_apply_apply]
      using hmodel.comp (show Continuous (fun z : a.quotient ↦ (e.equiv z).toAdd) from e.equiv.continuous)
  have hcont : Continuous (fun z : H ↦ f (z : G)) :=
    (hf₀.comp (QuotientGroup.continuous_mk (N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype))).congr hval
  exact hH.isOpenEmbedding_subtypeVal.continuousAt_iff.mp (hcont.continuousAt (x := ⟨x, hK (mem_insert ..)⟩))

/-- Paper: (12.4.1.5) and (12.4.1.7), p. 516. At the origin each translated
evaluation is the test value at zero, and the kernel has the corresponding weighted mass. -/
theorem sLocalTraceDilationKernel_apply_zero (f : BruhatCompactSupport Iₛ) (b : testₛ) :
    Integrable (fun g ↦ f.val g / (Real.sqrt (normS(g)) : ℂ)) μₛ ∧
      sLocalTraceDilationKernel f (fun y ↦ testAt(b, y)) 0 =
        (∫ g : Iₛ, f.val g / (Real.sqrt (normS(g)) : ℂ) ∂μₛ) * testAt(b, 0) := by
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace (F := F) (S := S)
  have : (sMultiplicativeTamagawaMeasure F S).IsHaarMeasure :=
    sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
  have hc : Continuous f.val := sLocalTraceDilationKernel_apply_zero_continuous
    ((mem_bruhatSmoothSubmodule_iff _).1 f.property.1)
  have hn : Continuous fun g : Iₛ ↦ normS(g) := by
    have h : Continuous fun g : Iₛ ↦ sIdeleQuotientNorm F S (QuotientGroup.mk g) :=
      (isProperMap_sIdeleQuotientNorm F S).continuous.comp continuous_quot_mk
    exact NNReal.continuous_coe.comp (Units.continuous_val.comp h)
  have hpos (g : Iₛ) : 0 < normS(g) := NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S g))
  have hsq : Continuous fun g : Iₛ ↦ (Real.sqrt (normS(g)) : ℂ) :=
    Complex.continuous_ofReal.comp hn.sqrt
  have hne (g : Iₛ) : (Real.sqrt (normS(g)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hpos g)).ne'
  have hcs : HasCompactSupport fun g ↦ f.val g / (Real.sqrt (normS(g)) : ℂ) :=
    HasCompactSupport.mono f.property.2 fun g hg h0 ↦ hg (by simp [h0])
  refine ⟨(hc.div hsq hne).integrable_of_hasCompactSupport hcs, ?_⟩
  simp [sLocalTraceDilationKernel, integral_mul_const]

private theorem exists_sLocalTraceDilationStrongDual_exists_norm_le {H : Type*} [CommGroup H]
    [TopologicalSpace H] {g : H → ℂ} (hg : g ∈ schwartzBruhatSubmodule H) :
    ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C := by
  let P (g : H → ℂ) : Prop := ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C
  have hzero : P 0 := ⟨0, fun x ↦ by simp⟩
  have hadd : ∀ g h, P g → P h → P (g + h) := by
    rintro g h ⟨C, hC⟩ ⟨D, hD⟩
    exact ⟨C + D, fun x ↦ (norm_add_le (g x) (h x)).trans (add_le_add (hC x) (hD x))⟩
  refine Submodule.iSup_induction (motive := P) _ hg (fun a g hg ↦ ?_) hzero hadd
  refine Submodule.iSup_induction (motive := P) _ hg (fun e g hg ↦ ?_) hzero hadd
  obtain ⟨s, rfl⟩ := LinearMap.mem_range.mp hg
  have hb (z) : ‖s z‖ ≤ (elementarySchwartzBound (s : _ → ℂ) (0, 0, 0, 0)).toReal := by
    have hz : (‖s z‖₊ : ℝ≥0∞) ≤ elementarySchwartzBound (s : _ → ℂ) (0, 0, 0, 0) := by
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun y ↦ (‖s y‖₊ : ℝ≥0∞)) z
    exact ENNReal.toReal_mono (s.property.2 (0, 0, 0, 0)).ne hz
  refine ⟨(elementarySchwartzBound (s : _ → ℂ) (0, 0, 0, 0)).toReal, fun x ↦ ?_⟩
  rw [schwartzBruhatStageRealization_apply]
  split_ifs
  · exact hb _
  · simp

private theorem exists_sLocalTraceDilationStrongDual_integrable
    (f : BruhatCompactSupport Iₛ) (x : Aₛ) (b : testₛ) :
    Integrable (fun g : Iₛ ↦
      f.val g / (Real.sqrt (normS(g)) : ℂ) * testAt(b, (g⁻¹).val * x)) μₛ := by
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace (F := F) (S := S)
  have hweight := (sLocalTraceDilationKernel_apply_zero f 0).1
  obtain ⟨M, hM⟩ := exists_sLocalTraceDilationStrongDual_exists_norm_le b.property
  have hshift : Continuous (fun g : Iₛ ↦ Multiplicative.ofAdd ((g⁻¹).val * x)) :=
    continuous_ofAdd.comp ((Units.continuous_val.comp continuous_inv).mul continuous_const)
  exact hweight.mul_bdd ((schwartzBruhat_continuous b).comp hshift).aestronglyMeasurable
    (.of_forall fun g ↦ hM _)

private theorem exists_sLocalTraceDilationStrongDual_continuous_of_sup_bound {A : Type*} [CommGroup A]
    [TopologicalSpace A] (Λ : SchwartzBruhat A →ₗ[ℂ] ℂ) (C : ℝ≥0)
    (hΛ : ∀ (f : SchwartzBruhat A) (M : ℝ), (∀ x, ‖f x‖ ≤ M) → ‖Λ f‖ ≤ C * M) :
    Continuous Λ := by
  classical
  let p := (normSeminorm ℂ ℂ).comp Λ
  have hp : ∀ (b : BruhatStructuralPair A) (s : ElementaryLCAPresentation b.quotient),
      Continuous (p ∘ schwartzBruhatStageInclusion b s) := by
    intro b s
    let q := (normSeminorm ℂ ℂ).comp (Λ.comp (schwartzBruhatStageInclusion b s))
    change Continuous q
    let p₀ : Seminorm ℂ (SchwartzBruhatStage s) := elementarySchwartzSeminorm (0, 0, 0, 0)
    have hp₀ : Continuous p₀ :=
      (withGeneratingSeminorms_spec _ _).continuous_seminorm (0, 0, 0, 0)
    have hpt (f : SchwartzBruhatStage s) (x : A) :
        ‖schwartzBruhatStageRealization b s f x‖ ≤ p₀ f := by
      let := s.finiteGroup
      have he := schwartzBruhatStageRealization_apply b s f x
      by_cases hx : x ∈ b.val.1
      · rw [dite_eq_left hx] at he
        rw [he]
        let y := Multiplicative.toAdd (s.equiv (QuotientGroup.mk ⟨x, hx⟩))
        change (‖f y‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
        have hb : (‖f y‖₊ : ENNReal) ≤ elementarySchwartzBound f.val (0, 0, 0, 0) :=
          (le_iSup (fun g ↦ (‖f.val g‖₊ : ENNReal)) y).trans_eq
            (elementarySchwartzBound_zero f.val).symm
        exact ENNReal.toReal_mono (f.property.2 (0, 0, 0, 0)).ne hb
      · rw [dite_eq_right hx] at he
        exact ((congrArg norm he).trans (norm_zero : ‖(0 : ℂ)‖ = 0)).le.trans
          (apply_nonneg p₀ f)
    have hC : Continuous (C • p₀) := hp₀.const_smul C
    exact Seminorm.continuous_of_le hC fun f ↦
      hΛ (schwartzBruhatStageInclusion b s f) (p₀ f) (hpt f)
  let i : {q : Seminorm ℂ (schwartzBruhatSubmodule A) //
      ∀ (b : BruhatStructuralPair A) (s : ElementaryLCAPresentation b.quotient),
        Continuous (q ∘ schwartzBruhatStageInclusion b s)} := ⟨p, hp⟩
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp Λ fun _ ↦
    (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm i

/-- Paper: (12.4.1.5)–(12.4.1.7), p. 516. At each output point the scalar
pairing with the test defines a continuous linear functional on additive
Schwartz–Bruhat functions. -/
theorem exists_sLocalTraceDilationStrongDual (f : BruhatCompactSupport Iₛ) (x : Aₛ) :
    ∃ K : StrongDual ℂ testₛ, ∀ b : testₛ,
      Integrable (fun g : Iₛ ↦
        f.val g / (Real.sqrt (normS(g)) : ℂ) * testAt(b, (g⁻¹).val * x)) μₛ ∧
      K b = sLocalTraceDilationKernel f (fun y ↦ testAt(b, y)) x := by
  let weight (g : Iₛ) := f.val g / (Real.sqrt (normS(g)) : ℂ)
  let shift (g : Iₛ) : Multiplicative Aₛ := Multiplicative.ofAdd ((g⁻¹).val * x)
  let Φ (b : testₛ) : ℂ := ∫ g, weight g * b (shift g) ∂μₛ
  have hint (b : testₛ) : Integrable (fun g ↦ weight g * b (shift g)) μₛ :=
    exists_sLocalTraceDilationStrongDual_integrable f x b
  have hlin : IsLinearMap ℂ Φ := by
    constructor
    · intro b c
      change (∫ g, weight g * (b + c) (shift g) ∂μₛ) =
        (∫ g, weight g * b (shift g) ∂μₛ) + ∫ g, weight g * c (shift g) ∂μₛ
      simp_rw [show ∀ g, (b + c) (shift g) = b (shift g) + c (shift g) from fun g ↦ by rfl]
      simp_rw [mul_add]
      exact integral_add (hint b) (hint c)
    · intro c b
      change (∫ g, weight g * (c • b) (shift g) ∂μₛ) =
        c • ∫ g, weight g * b (shift g) ∂μₛ
      simp_rw [show ∀ g, (c • b) (shift g) = c * b (shift g) from fun g ↦ by rfl]
      simp_rw [mul_left_comm (weight _) c]
      simpa only [smul_eq_mul] using (integral_const_mul c (fun g ↦ weight g * b (shift g)))
  let Λ : testₛ →ₗ[ℂ] ℂ := IsLinearMap.mk' Φ hlin
  have hweight : Integrable weight μₛ := (sLocalTraceDilationKernel_apply_zero f 0).1
  let C : ℝ≥0 := ⟨∫ g, ‖weight g‖ ∂μₛ, integral_nonneg fun _ ↦ norm_nonneg _⟩
  have hΛ : ∀ (b : testₛ) (M : ℝ), (∀ z, ‖b z‖ ≤ M) → ‖Λ b‖ ≤ C * M := by
    intro b M hM
    change ‖∫ g, weight g * b (shift g) ∂μₛ‖ ≤ C * M
    calc
      _ ≤ ∫ g, ‖weight g * b (shift g)‖ ∂μₛ := norm_integral_le_integral_norm _
      _ ≤ ∫ g, ‖weight g‖ * M ∂μₛ := by
        apply integral_mono (hint b).norm (hweight.norm.mul_const M)
        intro g
        change ‖weight g * b (shift g)‖ ≤ ‖weight g‖ * M
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      _ = C * M := by rw [integral_mul_const]; rfl
  refine ⟨⟨Λ, exists_sLocalTraceDilationStrongDual_continuous_of_sup_bound Λ C hΛ⟩, fun b ↦ ⟨hint b, ?_⟩⟩
  rfl

-- TODO(paper-gap): The application of (12.4.1.6) requires a kernel theorem for
-- the particular vector-valued Schwartz–Bruhat space and operator topology.
-- The scalar distribution pairing above does not establish that assertion.

-- TODO(paper-gap): Footnotes 2–4 request new one-sided smooth cutoffs and an
-- independent lower bound. In Step II the product-norm multipliers also fail
-- to have the advertised Schwartz–Bruhat mapping properties (I218 and R9).

/-- Paper: Step II, p. 516. In the rational real model, a compact smooth cutoff
vanishing near zero multiplies any Schwartz test into the flat subspace.
Deviation: A ball cutoff that is one near zero does not have this range. -/
theorem realSpatialCutoff_flat_of_eventually_zero (ρ : ℝ → ℝ)
    (_hSmooth : ContDiff ℝ (∞ : ℕ∞ω) ρ) (_hCompact : HasCompactSupport ρ)
    (_hZero : ∀ᶠ x in 𝓝 (0 : ℝ), ρ x = 0) (f : 𝓢(ℝ, ℂ)) :
    ∃ h : 𝓢(ℝ, ℂ), h ∈ realSchwartzFlatAtOrigin ∧
      ∀ x : ℝ, h x = (ρ x : ℂ) * f x := by
  have hg : (fun x : ℝ ↦ (ρ x : ℂ)).HasTemperateGrowth :=
    (_hCompact.comp_left Complex.ofReal_zero).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp _hSmooth)
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (ρ x : ℂ)) f,
    (mem_realSchwartzFlatAtOrigin_iff _).2 fun k ↦ ?_, fun x ↦ ?_⟩
  · have h0 : (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (ρ x : ℂ)) f : ℝ → ℂ) =ᶠ[𝓝 0]
        fun _ ↦ 0 :=
      _hZero.mono fun x hx ↦ by simp [SchwartzMap.smulLeftCLM_apply_apply hg, hx]
    rw [h0.iteratedDeriv_eq]
    simp
  · simp [SchwartzMap.smulLeftCLM_apply_apply hg]

/-- Paper: Step II and (12.4.1.8)–(12.4.1.10), pp. 516–517. The Fourier cutoff
multiplies the Fourier transform by a symbol, then applies the inverse transform.
Deviation: This is a scalar function on the additive adeles. The definition makes
no assertion that the result belongs to the Schwartz–Bruhat test space. -/
def sLocalTraceFourierCutoff (ρ' : Aₛ → ℂ) (b : testₛ) (x : Aₛ) : ℂ :=
  fourierₛ (fun u ↦ ρ' u * testAt(sAdeleSchwartzFourier b, u)) (-x)

/-- Paper: (12.4.1.8), p. 517. The constant-one Fourier symbol recovers the test
by inversion. -/
theorem sLocalTraceFourierCutoff_one (b : testₛ) (x : Aₛ) :
    sLocalTraceFourierCutoff (fun _ ↦ 1) b x = testAt(b, x) := by
  have h := sLocal_fourier_inversion b (-x)
  rw [neg_neg] at h
  unfold sLocalTraceFourierCutoff
  simp only [one_mul]
  unfold sAdeleSchwartzFourier at h
  exact h

/-- Paper: Step II, p. 517. For an integrable symbol the inverse Fourier transform
of the symbol, evaluated at output minus input, is the Fourier cutoff kernel.
Deviation: The inverse transform gives the sign for general symbols. For the even
symbols in the paper the forward transform has the same values. -/
def sLocalTraceFourierKernel (ρ' : Aₛ → ℂ) (_hρ' : Integrable ρ' νₛ) (x y : Aₛ) : ℂ :=
  fourierₛ ρ' (y - x)

/-- Paper: Step II, p. 517. The diagonal Fourier kernel for an integrable
symbol is its integral against additive Tamagawa measure. -/
theorem sLocalTraceFourierKernel_diagonal (ρ' : Aₛ → ℂ) (hρ' : Integrable ρ' νₛ)
    (x : Aₛ) :
    sLocalTraceFourierKernel ρ' hρ' x x = ∫ u, ρ' u ∂νₛ := by
  have h0 : ψₛ 0 = 1 := by
    have h1 : ∀ w : InfinitePlace F, (0 : Aₛ).1 w = 0 := fun _ ↦ rfl
    simp [sAdeleStandardCharacter, adeleStandardCharacter_zero, finiteLocalStandardCharacter_zero,
      h1, Pi.single_zero, Prod.mk_zero_zero]
  simp [sLocalTraceFourierKernel, tamagawaFourier, h0]

/-- Paper: Step II, p. 517. With an S-idele as output, integrate the
dilation average of the Fourier phases against the frequency symbol and multiply
by the spatial cutoff.
Deviation: The dilation average is taken first. This formula can be used even
when the frequency symbol has no ordinary inverse Fourier kernel. -/
def sLocalTraceCutoffKernel (f : BruhatCompactSupport Iₛ) (ρ : Iₛ → ℂ) (ρ' : Aₛ → ℂ)
    (x : Iₛ) (y : Aₛ) : ℂ :=
  ρ x * ∫ u, ρ' u *
    sLocalTraceDilationKernel f (fun z ↦ (ψₛ ((z - y) * u) : ℂ)) x.val ∂νₛ

/-- An integrable product weight dominates the joint integrand of the two kernels. -/
private theorem sLocalTraceCutoffKernel_eq_comp_fubini
    {G A : Type*} [MeasurableSpace G] [MeasurableSpace A]
    (μ : Measure G) (ν : Measure A) [SFinite μ] [SFinite ν]
    (weight : G → ℂ) (symbol : A → ℂ) (phase : G → A → ℂ)
    (hweight : Integrable weight μ) (hsymbol : Integrable symbol ν)
    (hphase : AEStronglyMeasurable (fun p : A × G ↦ phase p.2 p.1) (ν.prod μ))
    (hunit : ∀ g u, ‖phase g u‖ = 1) :
    (∫ u, symbol u * (∫ g, weight g * phase g u ∂μ) ∂ν) =
      ∫ g, weight g * (∫ u, symbol u * phase g u ∂ν) ∂μ := by
  have hweightProd := hsymbol.mul_prod hweight
  have hprod : Integrable (uncurry fun u g ↦ symbol u * weight g * phase g u)
      (ν.prod μ) := by
    refine hweightProd.mono (hweightProd.aestronglyMeasurable.mul hphase) ?_
    exact ae_of_all _ fun p ↦ by simp [uncurry, hunit]
  simp_rw [← integral_const_mul]
  simpa only [mul_assoc, mul_left_comm] using integral_integral_swap hprod

/-- Paper: Step II, p. 517. For an integrable symbol the composed kernel
agrees with the dilation average of the inverse Fourier kernel, multiplied by the
spatial cutoff. -/
theorem sLocalTraceCutoffKernel_eq_comp (f : BruhatCompactSupport Iₛ)
    (ρ : Iₛ → ℂ) (ρ' : Aₛ → ℂ) (hρ' : Integrable ρ' νₛ) (x : Iₛ) (y : Aₛ) :
    sLocalTraceCutoffKernel f ρ ρ' x y =
      ρ x * sLocalTraceDilationKernel f (fun z ↦ sLocalTraceFourierKernel ρ' hρ' z y) x.val :=
  by
    have : BorelSpace Aₛ := sAdeleRing_borelSpace (F := F) (S := S)
    have : BorelSpace Iₛ := sIdeleGroup_borelSpace (F := F) (S := S)
    let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
    let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
      (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
    let : SecondCountableTopology Iₛ := (sIdeleGroup_description F S).1.secondCountableTopology
    let : (μₛ).IsHaarMeasure := sMultiplicativeTamagawaMeasure_isHaarMeasure
    let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
    let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
    let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
    let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
    let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
      infiniteLocalAdditiveTamagawaMeasure_haar F w
    let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
      finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
    let : (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).IsAddHaarMeasure :=
      Measure.pi.isAddHaarMeasure _
    let : (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)).IsAddHaarMeasure :=
      Measure.pi.isAddHaarMeasure _
    let : (νₛ).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
    let weight (g : Iₛ) := f.val g / (Real.sqrt (normS(g)) : ℂ)
    have hweight : Integrable weight μₛ := (sLocalTraceDilationKernel_apply_zero f 0).1
    obtain ⟨e, he, _⟩ := sAdditiveTamagawaMeasure_selfDual F S
    let char := e (Multiplicative.ofAdd (1 : Aₛ))
    have hchar (z : Aₛ) : char (Multiplicative.ofAdd z) = ψₛ z := by
      simpa only [one_mul] using he 1 z
    have hcontinuous : Continuous (fun z : Aₛ ↦ (ψₛ z : ℂ)) := by
      simp_rw [← hchar]
      exact continuous_subtype_val.comp ((map_continuous char).comp continuous_ofAdd)
    have hneg (z : Aₛ) : star (ψₛ (-z) : ℂ) = (ψₛ z : ℂ) := by
      rw [← hchar, ofAdd_neg, map_inv, Circle.coe_inv_eq_conj,
        ← Complex.star_def, star_star, hchar]
    let phase (g : Iₛ) (u : Aₛ) := (ψₛ (((g⁻¹).val * x.val - y) * u) : ℂ)
    have hphase : Continuous (uncurry phase) := hcontinuous.comp
      (((((Units.continuous_val.comp continuous_inv).comp continuous_fst).mul
        continuous_const).sub continuous_const).mul continuous_snd)
    have hfourier (g : Iₛ) :
        sLocalTraceFourierKernel ρ' hρ' ((g⁻¹).val * x.val) y =
          ∫ u, ρ' u * phase g u ∂νₛ := by
      unfold sLocalTraceFourierKernel tamagawaFourier
      apply integral_congr_ae
      exact ae_of_all _ fun u ↦ by
        change ρ' u * star (ψₛ (u * (y - (g⁻¹).val * x.val)) : ℂ) = ρ' u * phase g u
        rw [show u * (y - (g⁻¹).val * x.val) = -(((g⁻¹).val * x.val - y) * u) by
          rw [← neg_sub ((g⁻¹).val * x.val) y, mul_neg, mul_comm u], hneg]
    unfold sLocalTraceCutoffKernel sLocalTraceDilationKernel
    apply congrArg (fun z : ℂ ↦ ρ x * z)
    simp_rw [hfourier]
    exact sLocalTraceCutoffKernel_eq_comp_fubini μₛ νₛ weight ρ' phase hweight hρ'
      (hphase.comp continuous_swap).aestronglyMeasurable (fun g u ↦ Circle.norm_coe _)

-- TODO(paper-gap): The function on additive adeles constructed in Step II
-- requires a measure conversion and a quotient kernel construction before
-- Proposition 12.2.2.2 can be applied to it. On the additive side the
-- skew-diagonal convention below puts ξx in the output slot. The resulting
-- orbit sum reindexes the S-units by inversion.

-- TODO(paper-gap): The reference to (12.4.1.4) on pp. 514, 516 and 519 should
-- refer to (12.4.1.1)–(12.4.1.3). Equation (12.4.1.4) is the lifting identity.

/-- Paper: (12.4.1.17), p. 518. The factor converting additive to
multiplicative measure is the product of q/(q−1) over the finite places. -/
def sLocalTraceMeasureFactor (S : Finset V) : ℝ :=
  ∏ v ∈ S, (v.asIdeal.absNorm : ℝ) / ((v.asIdeal.absNorm : ℝ) - 1)

/-- Paper: (12.4.1.17), p. 518. The factor for the empty finite set is one
and the factor for one finite place is the corresponding Euler factor. -/
theorem sLocalTraceMeasureFactor_empty_singleton (v : V) :
    sLocalTraceMeasureFactor (F := F) ∅ = 1 ∧
      sLocalTraceMeasureFactor {v} = (v.asIdeal.absNorm : ℝ) / ((v.asIdeal.absNorm : ℝ) - 1) := by
  constructor <;> simp [sLocalTraceMeasureFactor]

/-- The lower integral of a product of coordinate functions over a product measure on
`n` coordinates is the product of the lower integrals. -/
private theorem sLocalTrace_measure_density_lintegral_fin {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
        (MeasurableEquiv.measurableEmbedding _), Fin.prod_univ_succAbove _ 0]
      have hfun : (fun p ↦ ∏ i, f i ((MeasurableEquiv.piFinSuccAbove E 0).symm p i)) =
          fun p ↦ f 0 p.1 * ∏ j : Fin n, f (Fin.succAbove 0 j) (p.2 j) := by
        funext p
        rw [Fin.prod_univ_succAbove _ 0]
        exact congrArg₂ (· * ·) (congrArg (f 0) (Fin.insertNth_apply_same 0 p.1 p.2))
          (Finset.prod_congr rfl fun j _ ↦ congrArg _ (Fin.insertNth_apply_succAbove 0 p.1 p.2 j))
      rw [hfun, lintegral_prod_mul (f := f 0) (g := fun x : (j : Fin n) → E (Fin.succAbove 0 j) ↦
          ∏ j : Fin n, f (Fin.succAbove 0 j) (x j))
        (hf 0).aemeasurable (Finset.measurable_prod _ fun j _ ↦
          (hf (Fin.succAbove 0 j)).comp (measurable_pi_apply j)).aemeasurable,
        n_ih (fun j ↦ f (Fin.succAbove 0 j)) (fun j ↦ hf _)]

/-- The lower integral of a product of coordinate functions over a finite product measure
is the product of the lower integrals. -/
private theorem sLocalTrace_measure_density_lintegral_pi {ι : Type*} [Fintype ι]
    {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact sLocalTrace_measure_density_lintegral_fin (fun i ↦ f (e i)) (fun i ↦ hf (e i))

/-- A finite product of measures with densities is the product measure with the
product density. -/
private theorem sLocalTrace_measure_density_pi_withDensity {ι : Type*} [Fintype ι]
    {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)} (μ : (i : ι) → Measure (E i))
    [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i ↦ (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x ↦ ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs ↦ ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    sLocalTrace_measure_density_lintegral_pi f hf]
  exact Finset.prod_congr rfl fun i _ ↦ (withDensity_apply _ (hs i)).symm

/-- Paper: (12.4.1.17), p. 518. The pushforward of multiplicative Tamagawa
measure to the invertible locus has density c_S divided by the product norm.
Deviation: The density is applied to additive measure restricted to the invertible locus. -/
theorem sLocalTrace_measure_density :
    (μₛ).map (Units.val : Iₛ → Aₛ) =
      ((νₛ).restrict (range (Units.val : Iₛ → Aₛ))).withDensity
        (fun z ↦ ENNReal.ofReal (sLocalTraceMeasureFactor S / modS(z))) := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F)ˣ := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (w : InfinitePlace F) : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let (v : S) : BorelSpace (v.val.adicCompletion F)ˣ := ⟨rfl⟩
  let (w : InfinitePlace F) : SecondCountableTopology w.Completionˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let (v : S) : SecondCountableTopology (v.val.adicCompletion F)ˣ :=
    Units.isEmbedding_val₀.secondCountableTopology
  let (w : InfinitePlace F) : LocallyCompactSpace w.Completionˣ :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).locallyCompactSpace
  let (w : InfinitePlace F) : (infiniteLocalMultiplicativeTamagawaMeasure F w).IsHaarMeasure :=
    infiniteLocalMultiplicativeTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalMultiplicativeTamagawaMeasure F v.val).IsHaarMeasure :=
    finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure v.val
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let ρI (w : InfinitePlace F) (x : w.Completion) : ℝ≥0∞ := (↑(‖x‖₊ ^ w.mult) : ℝ≥0∞)⁻¹
  let c (v : S) : ℝ≥0∞ := ↑v.val.asIdeal.absNorm / (↑v.val.asIdeal.absNorm - 1)
  let ρS (v : S) (x : v.val.adicCompletion F) : ℝ≥0∞ := c v * (↑‖x‖₊ : ℝ≥0∞)⁻¹
  have hq (v : S) : 1 < v.val.asIdeal.absNorm := HeightOneSpectrum.one_lt_absNorm v.val
  have hc (v : S) : c v ≠ ⊤ := ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
    (tsub_pos_of_lt (by exact_mod_cast hq v)).ne'
  have hρI (w : InfinitePlace F) : Measurable (ρI w) :=
    ((measurable_nnNorm.pow_const _).coe_nnreal_ennreal).inv
  have hρS (v : S) : Measurable (ρS v) :=
    measurable_const.mul measurable_nnNorm.coe_nnreal_ennreal.inv
  have hRI (w : InfinitePlace F) : MeasurableSet (range (Units.val : w.Completionˣ → _)) :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).isOpen_range.measurableSet
  have hRS (v : S) : MeasurableSet (range (Units.val : (v.val.adicCompletion F)ˣ → _)) :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.val.adicCompletion F)).isOpen_range.measurableSet
  have hlocI (w : InfinitePlace F) : (infiniteLocalMultiplicativeTamagawaMeasure F w).map Units.val =
      ((infiniteLocalAdditiveTamagawaMeasure F w).restrict (range Units.val)).withDensity (ρI w) := by
    rw [infiniteLocalMultiplicativeTamagawaMeasure,
      (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding.map_comap,
      restrict_withDensity (hRI w)]
  have hlocS (v : S) : (finiteLocalMultiplicativeTamagawaMeasure F v.val).map Units.val =
      ((finiteLocalAdditiveTamagawaMeasure F v.val).restrict (range Units.val)).withDensity
        (ρS v) := by
    rw [finiteLocalMultiplicativeTamagawaMeasure_eq_withDensity, Measure.map_smul,
      (IsOpenUnits.isOpenEmbedding_unitsVal (M := v.val.adicCompletion F)).measurableEmbedding.map_comap,
      restrict_withDensity (hRS v), ← withDensity_smul' _ _ (hc v)]
    · rfl
    · exact Units.continuous_val.measurable.aemeasurable
  have hsfI (w : InfinitePlace F) : SigmaFinite
      (((infiniteLocalAdditiveTamagawaMeasure F w).restrict (range Units.val)).withDensity
        (ρI w)) :=
    SigmaFinite.withDensity_of_ne_top ((ae_restrict_iff' (hRI w)).2 (ae_of_all _ fun x hx ↦ by
      obtain ⟨u, rfl⟩ := hx
      exact ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2 (pow_ne_zero _
        (nnNorm_ne_zero_iff.2 u.ne_zero)))))
  have hsfS (v : S) : SigmaFinite
      (((finiteLocalAdditiveTamagawaMeasure F v.val).restrict (range Units.val)).withDensity
        (ρS v)) :=
    SigmaFinite.withDensity_of_ne_top ((ae_restrict_iff' (hRS v)).2 (ae_of_all _ fun x hx ↦ by
      obtain ⟨u, rfl⟩ := hx
      exact ENNReal.mul_ne_top (hc v) (ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2
        (nnNorm_ne_zero_iff.2 u.ne_zero)))))
  have (w : InfinitePlace F) :
      SigmaFinite ((infiniteLocalMultiplicativeTamagawaMeasure F w).map Units.val) := by
    rw [hlocI w]; exact hsfI w
  have (v : S) :
      SigmaFinite ((finiteLocalMultiplicativeTamagawaMeasure F v.val).map Units.val) := by
    rw [hlocS v]; exact hsfS v
  have hAI : Measurable (fun (f : (w : InfinitePlace F) → w.Completionˣ) (w : InfinitePlace F) ↦
      (f w).val) :=
    measurable_pi_iff.2 fun w ↦ Units.continuous_val.measurable.comp (measurable_pi_apply w)
  have hAS : Measurable (fun (f : (v : S) → (v.val.adicCompletion F)ˣ) (v : S) ↦ (f v).val) :=
    measurable_pi_iff.2 fun v ↦ Units.continuous_val.measurable.comp (measurable_pi_apply v)
  have hmapL : (μₛ).map (Units.val : Iₛ → Aₛ) =
      ((Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).map
        (fun (f : (w : InfinitePlace F) → w.Completionˣ) (w : InfinitePlace F) ↦ (f w).val)).prod
      ((Measure.pi fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val).map
        (fun (f : (v : S) → (v.val.adicCompletion F)ˣ) (v : S) ↦ (f v).val)) := by
    rw [Measure.map_prod_map _ _ hAI hAS]
    unfold sMultiplicativeTamagawaMeasure
    rw [Measure.map_map]
    · rfl
    · exact fun s hs ↦ ⟨s, hs, rfl⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact (hAI.prodMap hAS) ht
  have hrange : range (Units.val : Iₛ → Aₛ) =
      (univ.pi fun w : InfinitePlace F ↦ range (Units.val : w.Completionˣ → w.Completion)) ×ˢ
        (univ.pi fun v : S ↦
          range (Units.val : (v.val.adicCompletion F)ˣ → v.val.adicCompletion F)) := by
    ext z
    simp only [Set.mem_prod, Set.mem_univ_pi]
    change IsUnit z ↔ (∀ w, IsUnit (z.1 w)) ∧ ∀ v, IsUnit (z.2 v)
    rw [Prod.isUnit_iff, Pi.isUnit_iff, Pi.isUnit_iff]
  have hbox : MeasurableSet ((univ.pi fun w : InfinitePlace F ↦
      range (Units.val : w.Completionˣ → w.Completion)) ×ˢ (univ.pi fun v : S ↦
          range (Units.val : (v.val.adicCompletion F)ˣ → v.val.adicCompletion F))) :=
    (MeasurableSet.univ_pi hRI).prod (MeasurableSet.univ_pi hRS)
  have hpiI : (Measure.pi (infiniteLocalMultiplicativeTamagawaMeasure F)).map
      (fun (f : (w : InfinitePlace F) → w.Completionˣ) (w : InfinitePlace F) ↦ (f w).val) =
      Measure.pi fun w ↦ (infiniteLocalMultiplicativeTamagawaMeasure F w).map Units.val :=
    Measure.pi_map_pi fun w ↦ Units.continuous_val.measurable.aemeasurable
  have hpiS : (Measure.pi fun v : S ↦ finiteLocalMultiplicativeTamagawaMeasure F v.val).map
      (fun (f : (v : S) → (v.val.adicCompletion F)ˣ) (v : S) ↦ (f v).val) =
      Measure.pi fun v : S ↦ (finiteLocalMultiplicativeTamagawaMeasure F v.val).map Units.val :=
    Measure.pi_map_pi fun v ↦ Units.continuous_val.measurable.aemeasurable
  rw [hmapL, hpiI, hpiS]
  simp_rw [hlocI, hlocS]
  rw [sLocalTrace_measure_density_pi_withDensity _ ρI hρI,
    sLocalTrace_measure_density_pi_withDensity _ ρS hρS,
    prod_withDensity (f := fun x : (w : InfinitePlace F) → w.Completion ↦ ∏ w, ρI w (x w))
      (g := fun x : (v : S) → v.val.adicCompletion F ↦ ∏ v, ρS v (x v))
      (Finset.measurable_prod _ fun w _ ↦ (hρI w).comp (measurable_pi_apply w))
      (Finset.measurable_prod _ fun v _ ↦ (hρS v).comp (measurable_pi_apply v)),
    ← Measure.restrict_pi_pi, ← Measure.restrict_pi_pi, Measure.prod_restrict, hrange]
  refine withDensity_congr_ae ((ae_restrict_iff' hbox).2 (ae_of_all _ fun z hz ↦ ?_))
  have hz1 (w : InfinitePlace F) : 0 < ‖z.1 w‖ := by
    obtain ⟨u, hu⟩ := (Set.mem_univ_pi.1 hz.1) w
    exact norm_pos_iff.2 (hu ▸ u.ne_zero)
  have hz2 (v : S) : 0 < ‖z.2 v‖ := by
    obtain ⟨u, hu⟩ := (Set.mem_univ_pi.1 hz.2) v
    exact norm_pos_iff.2 (hu ▸ u.ne_zero)
  have hq' (v : S) : (1 : ℝ) < v.val.asIdeal.absNorm := by exact_mod_cast hq v
  have e1 (w : InfinitePlace F) :
      ρI w (z.1 w) = ENNReal.ofReal ((‖z.1 w‖ ^ w.mult)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (pow_pos (hz1 w) _),
      show ‖z.1 w‖ ^ w.mult = ((‖z.1 w‖₊ ^ w.mult : ℝ≥0) : ℝ) by simp,
      ENNReal.ofReal_coe_nnreal]
  have e2 (v : S) : ρS v (z.2 v) =
      ENNReal.ofReal ((v.val.asIdeal.absNorm : ℝ) / ((v.val.asIdeal.absNorm : ℝ) - 1)) *
        ENNReal.ofReal ‖z.2 v‖⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (hz2 v), ENNReal.ofReal_div_of_pos (sub_pos.2 (hq' v)),
      ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one,
      ← coe_nnNorm, ENNReal.ofReal_coe_nnreal]
  simp only [e1, e2]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ ↦ inv_nonneg.2 (pow_nonneg (hz1 w).le _))]
  simp_rw [← ENNReal.ofReal_mul (div_nonneg (Nat.cast_nonneg _) (sub_pos.2 (hq' _)).le)]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun v _ ↦ mul_nonneg
      (div_nonneg (Nat.cast_nonneg _) (sub_pos.2 (hq' v)).le) (inv_nonneg.2 (hz2 v).le)),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ ↦ inv_nonneg.2 (pow_nonneg (hz1 w).le _))]
  congr 1
  rw [sLocalTraceMeasureFactor, ← Finset.prod_coe_sort S, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  ring

/-- Paper: (12.4.1.18)–(12.4.1.21), p. 518. Translate and invert the lifted test
and divide by the square-root norm after the change of variable z = gξ − 1.
Deviation: The function on the additive adeles is extended by zero where 1 + z
is not invertible. The printed domain in (12.4.1.18) is written for g. -/
def sLocalTraceEta (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (z : Aₛ) : ℂ :=
  Function.extend (Units.val : Iₛ → Aₛ)
    (fun u ↦ f.val ((ξ.val⁻¹ * u)⁻¹) / (Real.sqrt (normS(ξ.val⁻¹ * u)) : ℂ))
    (fun _ ↦ 0) (1 + z)

/-- Paper: (12.4.1.20), p. 518. The translated test has value f(ξ) at the
origin, and it is zero at minus one. -/
theorem sLocalTraceEta_zero_neg_one (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    sLocalTraceEta f ξ 0 = f.val ξ.val ∧ sLocalTraceEta f ξ (-1) = 0 := by
  have h2 : sIdeleNorm F S ξ.val = 1 := by
    obtain ⟨γ, hγ, hξ⟩ := Subgroup.mem_map.mp ξ.property
    have h1 := ((sIdeleNorm_spec F S).2 hγ)
    rw [← hξ]; exact h1
  constructor
  · unfold sLocalTraceEta
    have h : (1 : Aₛ) + 0 = ((1 : Iₛ) : Aₛ) := by simp
    rw [h, Units.val_injective.extend_apply]
    simp [h2]
  · unfold sLocalTraceEta
    have h : (1 : Aₛ) + -1 = 0 := by simp
    rw [h, Function.extend_apply']
    rintro ⟨u, hu⟩
    exact not_isUnit_zero (hu ▸ u.isUnit)

section

private theorem sLocalTrace_additiveHaar : (νₛ).IsAddHaarMeasure := by
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : S) : MeasurableSpace (v.val.adicCompletion F) := borel _
  let (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
  let (v : S) : BorelSpace (v.val.adicCompletion F) := ⟨rfl⟩
  let (w : InfinitePlace F) : (infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure :=
    infiniteLocalAdditiveTamagawaMeasure_haar F w
  let (v : S) : (finiteLocalAdditiveTamagawaMeasure F v.val).IsAddHaarMeasure :=
    finiteLocalAdditiveTamagawaMeasure_isAddHaar F v.val
  let : (Measure.pi (infiniteLocalAdditiveTamagawaMeasure F)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  let : (Measure.pi (fun v : S ↦ finiteLocalAdditiveTamagawaMeasure F v.val)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  exact Measure.prod.instIsAddHaarMeasure _ _

/-- Paper: (12.4.1.17), p. 518. For an additive integrand vanishing off the units,
its multiplicative integral weighted by the idelic norm is its additive integral
times the finite-place measure factor. -/
private theorem sLocalTrace_integral_units (a : Aₛ → ℂ) (ha : ∀ t, t ∉ range (Units.val : Iₛ → Aₛ) → a t = 0) :
    (∫ t : Iₛ, (normS(t) : ℂ) * a t.val ∂μₛ) =
      (sLocalTraceMeasureFactor S : ℂ) * ∫ t, a t ∂νₛ := by
  have : BorelSpace Aₛ := sAdeleRing_borelSpace
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace
  have ho : Topology.IsOpenEmbedding (Units.val : Iₛ → Aₛ) := IsOpenUnits.isOpenEmbedding_unitsVal
    (M := ((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F))
  let n (t : Aₛ) := modS(t)
  have hn (t : Iₛ) : normS(t) = n t.val := by simp [n, sIdeleNorm, Units.coe_prod]
  have hm : Continuous n := by
    unfold n
    exact (continuous_finsetProd _ fun w _ ↦
      (((continuous_apply w).comp continuous_fst).norm.pow _)).mul
      (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  let c := sLocalTraceMeasureFactor (F := F) S
  have hc : 0 ≤ c := by
    apply Finset.prod_nonneg
    intro v _
    have hv : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    exact div_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hv.le)
  let d (t : Aₛ) := ENNReal.ofReal (c / n t)
  have hd : Measurable d := (measurable_const.div hm.measurable).ennreal_ofReal
  simp_rw [hn]
  rw [← ho.measurableEmbedding.integral_map (μ := μₛ) (fun t ↦ (n t : ℂ) * a t),
    sLocalTrace_measure_density]
  change (∫ t, (n t : ℂ) * a t ∂((νₛ).restrict _).withDensity d) = _
  rw [integral_withDensity_eq_integral_toReal_smul hd (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero ha, ← integral_const_mul]
  apply integral_congr_ae
  apply (ae_restrict_iff' ho.isOpen_range.measurableSet).2
  apply ae_of_all
  rintro _ ⟨t, rfl⟩
  have hpos : 0 < n t.val := (hn t) ▸ NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S t))
  simp only [d, ENNReal.toReal_ofReal (div_nonneg hc hpos.le), Complex.real_smul,
    Complex.ofReal_div]
  change (c : ℂ) / _ * (_ * _) = (c : ℂ) * _
  field_simp [Complex.ofReal_ne_zero.mpr hpos.ne']

private theorem sLocalTraceDilationKernel_skew_frequency (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (x : Iₛ) (u : Aₛ) :
    sLocalTraceDilationKernel f (fun z ↦ (ψₛ ((z - x.val) * u) : ℂ)) (ξ.val * x).val =
      (sLocalTraceMeasureFactor S : ℂ) * fourierₛ (sLocalTraceEta f ξ) (-(x.val * u)) := by
  have : BorelSpace Aₛ := sAdeleRing_borelSpace
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace
  let : (νₛ).IsAddHaarMeasure := sLocalTrace_additiveHaar
  let : (μₛ).Regular := sMultiplicativeTamagawaMeasure_regular
  let : (μₛ).IsHaarMeasure := sMultiplicativeTamagawaMeasure_isHaarMeasure
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology Iₛ := (sIdeleGroup_description F S).1.secondCountableTopology
  let : T2Space Aₛ := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace Aₛ := inferInstanceAs (LocallyCompactSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  have hξ : sIdeleNorm F S ξ.val = 1 := by
    obtain ⟨γ, hγ, he⟩ := Subgroup.mem_map.mp ξ.property
    exact he ▸ (sIdeleNorm_spec F S).2 hγ
  obtain ⟨e, he, -⟩ := sAdditiveTamagawaMeasure_selfDual F S
  let char := e (Multiplicative.ofAdd (1 : Aₛ))
  have hchar (z : Aₛ) : char (Multiplicative.ofAdd z) = ψₛ z := by
    simpa only [one_mul] using he 1 z
  have hneg (z : Aₛ) : star (ψₛ (-z) : ℂ) = (ψₛ z : ℂ) := by
    rw [← hchar, ofAdd_neg, map_inv, Circle.coe_inv_eq_conj,
      ← Complex.star_def, star_star, hchar]
  let k (z : Aₛ) := sLocalTraceEta f ξ z * (ψₛ (z * (x.val * u)) : ℂ)
  let j (t : Iₛ) := (normS(t) : ℂ) * k (t.val - 1)
  have hj (g : Iₛ) : j (ξ.val * g⁻¹) = f.val g / (Real.sqrt (normS(g)) : ℂ) *
      (ψₛ (((g⁻¹).val * (ξ.val * x).val - x.val) * u) : ℂ) := by
    have ht (t : Iₛ) : (1 : Aₛ) + (t.val - 1) = t.val := by abel
    simp only [j, k, sLocalTraceEta, ht, Units.val_injective.extend_apply,
      inv_mul_cancel_left, inv_inv, map_mul, map_inv, hξ, one_mul, inv_one, Units.val_inv_eq_inv_val,
      NNReal.coe_inv, Real.sqrt_inv, Complex.ofReal_inv, div_inv_eq_mul, Units.val_mul]
    rw [show (ξ.val.val * (g⁻¹).val - 1) * (x.val * u) =
      ((g⁻¹).val * (ξ.val.val * x.val) - x.val) * u by ring]
    have hs : (Real.sqrt (normS(g)) : ℂ) ^ 2 = (normS(g) : ℂ) := by
      exact_mod_cast Real.sq_sqrt (NNReal.coe_nonneg _)
    rw [← hs]
    have hne : (Real.sqrt (normS(g)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (NNReal.coe_pos.mpr (Units.zero_lt _))).ne'
    field_simp [hne]
  unfold sLocalTraceDilationKernel
  simp_rw [← hj]
  rw [integral_inv_eq_self (fun t ↦ j (ξ.val * t)) μₛ, integral_mul_left_eq_self]
  change (∫ t : Iₛ, (normS(t) : ℂ) * k (t.val - 1) ∂μₛ) = _
  rw [sLocalTrace_integral_units (fun t ↦ k (t - 1)) (by
    intro t ht
    simp [k, sLocalTraceEta, show (1 : Aₛ) + (t - 1) = t by abel, Function.extend_apply' _ _ _ ht]),
    integral_sub_right_eq_self]
  unfold tamagawaFourier
  simp only [mul_neg, hneg, k]

/-- Paper: (12.4.1.21)–(12.4.1.22), p. 518. On the skew diagonal, an even frequency
symbol gives the same scalar integral on the kernel and Fourier sides.
Deviation: The dilation average is taken first. This equality of Bochner integrals
holds independently of the separate integrability assertion. -/
private theorem sLocalTraceCutoffKernel_skew_eq (f : BruhatCompactSupport Iₛ) (ρ : Iₛ → ℂ) (r : Aₛ → ℂ)
    (heven : ∀ u, r (-u) = r u) (ξ : Hₛ) (x : Iₛ) :
    sLocalTraceCutoffKernel f ρ r (ξ.val * x) x.val =
      ρ (ξ.val * x) * (sLocalTraceMeasureFactor S : ℂ) *
        ∫ u, r u * fourierₛ (sLocalTraceEta f ξ) (x.val * u) ∂νₛ := by
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  let : (νₛ).IsAddHaarMeasure := sLocalTrace_additiveHaar
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : T2Space Aₛ := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace Aₛ := inferInstanceAs (LocallyCompactSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : SigmaCompactSpace Aₛ := inferInstanceAs (SigmaCompactSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : (νₛ).Regular := addHaar_regular_of_sigmaCompactSpace νₛ
  let φ (u : Aₛ) := r u * fourierₛ (sLocalTraceEta f ξ) (x.val * u)
  have h (u : Aₛ) : r u * ((sLocalTraceMeasureFactor S : ℂ) *
      fourierₛ (sLocalTraceEta f ξ) (-(x.val * u))) =
      (sLocalTraceMeasureFactor S : ℂ) * φ (-u) := by
    rw [show φ (-u) = r u * fourierₛ (sLocalTraceEta f ξ) (-(x.val * u)) by simp [φ, heven]]
    ring
  unfold sLocalTraceCutoffKernel
  simp_rw [sLocalTraceDilationKernel_skew_frequency, h]
  rw [integral_const_mul, integral_neg_eq_self, mul_assoc]

private theorem sLocalTrace_integrable_symbol_dilate (p : Aₛ → ℂ) (hp : Integrable p νₛ) (x : Iₛ) (r : Aₛ → ℂ)
    (hr : Measurable r) (M : ℝ) (hb : ∀ u, ‖r u‖ ≤ M) :
    Integrable (fun u ↦ r u * p (x.val * u)) νₛ := by
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  let : (νₛ).IsAddHaarMeasure := sLocalTrace_additiveHaar
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : T2Space Aₛ := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace Aₛ := inferInstanceAs (LocallyCompactSpace
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let e := DistribMulAction.toAddEquiv Aₛ x
  have hc : Continuous e := continuous_const.mul continuous_id
  have hci : Continuous e.symm := continuous_const.mul continuous_id
  let m := (νₛ).map e
  let hm : m.IsAddHaarMeasure := e.isAddHaarMeasure_map νₛ hc hci
  have hi : Integrable p m := by
    rw [Measure.isAddLeftInvariant_eq_smul m νₛ]
    exact hp.smul_measure_nnreal
  have hd : Integrable (fun u ↦ p (x.val * u)) νₛ := hi.comp_measurable hc.measurable
  simpa only [mul_comm] using hd.mul_bdd hr.aestronglyMeasurable (ae_of_all _ hb)

end

namespace SLocalTraceEta

open Topology

private theorem containing {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] {K : Set G} (hK : IsCompact K) :
    ∃ H : OpenCompactlyGeneratedSubgroups G, K ⊆ (H.val : Set G) := by
  obtain ⟨U, hU, hU₁⟩ := exists_compact_mem_nhds (1 : G)
  let H := Subgroup.closure (U ∪ K)
  have hSubset : U ∪ K ⊆ (H : Set G) := Subgroup.subset_closure
  have hOpen : IsOpen (H : Set G) :=
    H.isOpen_of_mem_nhds (mem_of_superset hU₁ (subset_union_left.trans hSubset))
  refine ⟨⟨H, hOpen, ⟨Subtype.val ⁻¹' (U ∪ K), ?_, ?_, ?_⟩⟩,
    subset_union_right.trans hSubset⟩
  · exact continuous_subtype_val.continuousAt.preimage_mem_nhds
      (mem_of_superset hU₁ subset_union_left)
  · exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage' (hU.union hK)
      (Subtype.range_coe.symm ▸ hSubset)
  · exact Subgroup.closure_preimage_eq_top _

/-- Pull a joint Bruhat-smooth test back along an entire real vector group. -/
private theorem smooth_vector_pullback {G E : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : Multiplicative E →* G) (hj : Continuous j) (f : G → ℂ) (hf : IsBruhatSmooth f)
    (g : G) : ContDiff ℝ (⊤ : ℕ∞) (fun v : E ↦ f (g * j (Multiplicative.ofAdd v))) := by
  classical
  rw [contDiff_infty]
  intro n
  obtain ⟨k,hk,_,hd⟩ := hf n
  obtain ⟨H,hH⟩ := containing ((isCompact_singleton (x := g)).union hk.isCompact)
  let a : BruhatStructuralPair G := ⟨(H.val, OrderDual.toDual k), H.property.1, H.property.2,
    hk, fun _ hx ↦ hH (Or.inr hx)⟩
  have hg : g ∈ a.val.1 := hH (Or.inl rfl)
  have hJ (v : Multiplicative E) : j v ∈ a.val.1 := by
    let : PreconnectedSpace (Multiplicative E) := inferInstanceAs (PreconnectedSpace E)
    apply (isPreconnected_range hj).subset_isClopen
      ⟨a.val.1.isClosed_of_isOpen a.property.1, a.property.1⟩
      ⟨1, ⟨1, j.map_one⟩, a.val.1.one_mem⟩ ⟨v,rfl⟩
  obtain ⟨e⟩ := a.elementary
  obtain ⟨f₀, heval, hs⟩ := hd a rfl
  let θm := e.equiv.toMulEquiv.toMonoidHom.comp ((QuotientGroup.mk' _).comp (j.codRestrict _ hJ))
  let θ := AddMonoidHom.toMultiplicative.symm θm
  have hθ : Continuous θ := e.equiv.continuous.comp (QuotientGroup.continuous_mk.comp
    (hj.subtype_mk _))
  let R := (AddMonoidHom.fst _ _).comp θ
  let T := (AddMonoidHom.fst _ _).comp ((AddMonoidHom.snd _ _).comp θ)
  choose l hl using fun i : Fin e.torusDim ↦ exists_addCircle_coe_linearMap_eq
    ((Pi.evalAddMonoidHom _ i).comp T) ((continuous_apply i).comp hθ.snd.fst)
  let L := (R.toRealLinearMap hθ.fst).prod
    ((EuclideanSpace.equiv (Fin e.torusDim) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi l))
  let c := (e.equiv (QuotientGroup.mk (⟨g,hg⟩ : a.val.1))).toAdd
  obtain ⟨t, ht⟩ := elementaryCover_surjective c.2.2.1 c.2.2.2 c.1 c.2.1
  have hv (v : E) : elementaryCover (L v + (c.1,t)) c.2.2.1 c.2.2.2 = θ v + c := by
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · funext i
      change ((l i v + t i : ℝ) : AddCircle (1 : ℝ)) = (θ v).2.1 i + c.2.1 i
      rw [AddCircle.coe_add, hl i v]
      exact congrArg ((θ v).2.1 i + ·) (congrArg (fun y ↦ y.2.1 i) ht)
    · have h := hθ.snd.snd.isConst_of_preconnectedSpace v 0
      rw [map_zero θ] at h
      change c.2.2 = (θ v).2.2 + c.2.2
      rw [h]; exact (zero_add _).symm
  have h := (hs e c.2.2.1 c.2.2.2).comp (L.contDiff.add (contDiff_const (c := (c.1,t))))
  convert h using 1
  funext v
  symm
  simp only [Function.comp_apply, hv, ofAdd_add]
  rw [mul_comm]
  change f₀ (e.equiv.symm (e.equiv _ * e.equiv _)) = _
  rw [← map_mul, e.equiv.symm_apply_apply]
  exact heval (⟨g,hg⟩ * ⟨j (Multiplicative.ofAdd v),hJ _⟩)

local notation "X∞" => mixedEmbedding.mixedSpace F
local notation "coord" => InfiniteAdeleRing.ringEquiv_mixedSpace F
local notation "Bₛ" => ((v : S) → v.val.adicCompletion F)

private def archExp : Multiplicative X∞ →* Iₛ :=
  MonoidHom.toHomUnits
    { toFun := fun v ↦ ((coord).symm (NormedSpace.exp v.toAdd), 1)
      map_one' := Prod.ext (by change (coord).symm (NormedSpace.exp 0) = 1; rw [NormedSpace.exp_zero, map_one]) rfl
      map_mul' := fun v w ↦ Prod.ext (by change (coord).symm (NormedSpace.exp (v.toAdd + w.toAdd)) = _; rw [NormedSpace.exp_add, map_mul]; rfl) (one_mul _).symm }

private theorem archExp_continuous : Continuous (archExp (F := F) (S := S)) := by
  apply (sIdeleGroup_description F S).1.continuous_iff.mpr
  exact ((continuous_infiniteAdeleRingEquivMixedSpace_symm F).comp
    ((NormedSpace.exp_continuous (𝔸 := X∞)).comp continuous_toAdd)).prodMk continuous_const

private theorem norm_curve {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : Multiplicative E →* Iₛ) (hj : Continuous j) (g : Iₛ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v : E ↦ (normS(g * j (Multiplicative.ofAdd v)))) := by
  have hn : Continuous (fun t : Iₛ ↦ normS(t)) := by
    have h : Continuous fun t : Iₛ ↦ sIdeleQuotientNorm F S (QuotientGroup.mk t) :=
      (isProperMap_sIdeleQuotientNorm F S).continuous.comp continuous_quot_mk
    exact NNReal.continuous_coe.comp (Units.continuous_val.comp h)
  have hp (t : Iₛ) : 0 < normS(t) := NNReal.coe_pos.mpr (Units.zero_lt _)
  let A : E →+ ℝ :=
    { toFun := fun v ↦ Real.log (normS(j (Multiplicative.ofAdd v)))
      map_zero' := by simp
      map_add' := fun x y ↦ by simp only [ofAdd_add, map_mul, Units.val_mul, NNReal.coe_mul,
        Real.log_mul (hp _).ne' (hp _).ne'] }
  have hc : Continuous A := (hn.comp (hj.comp continuous_ofAdd)).log fun v ↦ (hp _).ne'
  have h := contDiff_const (n := (⊤ : ℕ∞)) (c := normS(g)) |>.mul
    (Real.contDiff_exp.comp (A.toRealLinearMap hc).contDiff)
  convert h using 1
  funext v
  change normS(g * j (Multiplicative.ofAdd v)) = _ * Real.exp (Real.log _)
  simp [Real.exp_log (hp _)]

private theorem archLog :
    ∃ L : X∞ → X∞, ContDiffAt ℝ (⊤ : ℕ∞) L 1 ∧ ∀ᶠ y in 𝓝 1, NormedSpace.exp (L y) = y := by
  let E := X∞
  let exp := NormedSpace.exp (𝔸 := E)
  let A := ContinuousLinearEquiv.refl ℝ E
  have hd : HasFDerivAt exp (A : E →L[ℝ] E) 0 := hasFDerivAt_exp_zero
  have hc : ContDiffAt ℝ (⊤ : ℕ∞) exp 0 := (NormedSpace.exp_analytic (𝕂 := ℝ) _).contDiffAt
  have hs := hc.hasStrictFDerivAt hd (by simp)
  have h0 : (hs.toOpenPartialHomeomorph exp).symm (exp 0) = 0 := hs.localInverse_apply_image
  have hL := (hs.toOpenPartialHomeomorph exp).contDiffAt_symm hs.image_mem_toOpenPartialHomeomorph_target
    (by rw [h0]; exact hd) (by rw [h0]; exact hc)
  have hr := hs.eventually_right_inverse
  simpa [exp] using (show ∃ L : E → E, ContDiffAt ℝ (⊤ : ℕ∞) L (exp 0) ∧
    ∀ᶠ y in 𝓝 (exp 0), exp (L y) = y from ⟨_, hL, hr⟩)

private theorem eta_on_units (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (t : Iₛ) :
    sLocalTraceEta f ξ (t.val - 1) =
      f.val ((ξ.val⁻¹ * t)⁻¹) / (Real.sqrt (normS(ξ.val⁻¹ * t)) : ℂ) := by
  unfold sLocalTraceEta
  rw [show (1 : Aₛ) + (t.val - 1) = t.val by abel, Units.val_injective.extend_apply]

private theorem eta_log_chart (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (t : Iₛ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun v : X∞ ↦
      sLocalTraceEta f ξ ((t * archExp (Multiplicative.ofAdd v)).val - 1)) := by
  let j := archExp (F := F) (S := S)
  let g := ξ.val⁻¹ * t
  have hf := smooth_vector_pullback j archExp_continuous f.val
    ((mem_bruhatSmoothSubmodule_iff _).1 f.property.1) g⁻¹
  have hp (v : X∞) : 0 < normS(g * j (Multiplicative.ofAdd v)) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hn := (norm_curve j archExp_continuous g).sqrt (fun v ↦ (hp v).ne')
  have hden : ContDiff ℝ (⊤ : ℕ∞) (fun v : X∞ ↦ (Real.sqrt (normS(g * j (Multiplicative.ofAdd v))) : ℂ)) := Complex.ofRealCLM.contDiff.comp hn
  let H (v : X∞) := f.val (g⁻¹ * j (Multiplicative.ofAdd (-v))) *
    ((Real.sqrt (normS(g * j (Multiplicative.ofAdd v))) : ℂ))⁻¹
  have hs : ContDiff ℝ (⊤ : ℕ∞) H := (hf.comp (contDiff_neg (𝕜 := ℝ))).mul (hden.inv
    (fun v ↦ Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hp v)).ne'))
  have he (v : X∞) : sLocalTraceEta f ξ ((t * j (Multiplicative.ofAdd v)).val - 1) = H v := by
    rw [eta_on_units, ← mul_assoc]
    change f.val ((g * j (Multiplicative.ofAdd v))⁻¹) / _ = _
    rw [mul_inv_rev, mul_comm (j _)⁻¹, div_eq_mul_inv]
    unfold H
    rw [ofAdd_neg, map_inv]
  change ContDiff ℝ (⊤ : ℕ∞) (fun v : X∞ ↦ sLocalTraceEta f ξ ((t * j (Multiplicative.ofAdd v)).val - 1))
  simp_rw [he]
  exact hs

private theorem eta_arch_slice_smooth (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (b : Bₛ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : X∞ ↦ sLocalTraceEta f ξ ((coord).symm y,b)) := by
  let Z := (fun g : Iₛ ↦ (ξ.val * g⁻¹).val - 1) '' tsupport f.val
  have hc : IsCompact Z := f.property.2.image
    ((Units.continuous_val.comp (continuous_const.mul continuous_inv)).sub continuous_const)
  let Y (y : X∞) : Aₛ := ((coord).symm y,b)
  have hY : Continuous Y := (continuous_infiniteAdeleRingEquivMixedSpace_symm F).prodMk continuous_const
  have hzero (z : Aₛ) (hz : z ∉ Z) : sLocalTraceEta f ξ z = 0 := by
    by_cases hu : 1 + z ∈ range (Units.val : Iₛ → Aₛ)
    · obtain ⟨t, ht⟩ := hu
      have he : z = t.val - 1 := by rw [ht]; abel
      rw [he, eta_on_units]
      have hnot : (ξ.val⁻¹ * t)⁻¹ ∉ tsupport f.val := fun h ↦ hz
        ⟨_, h, by simp [ht]⟩
      rw [image_eq_zero_of_notMem_tsupport hnot, zero_div]
    · exact Function.extend_apply' _ _ _ hu
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : Y y ∈ Z
  · obtain ⟨g, _, hgy⟩ := hy
    let t := ξ.val * g⁻¹
    have ht : t.val - 1 = Y y := hgy
    have h1 : coord t.val.1 = 1 + y := by
      have hh := congrArg (fun z : Aₛ ↦ coord z.1) ht
      change coord (t.val.1 - 1) = coord ((coord).symm y) at hh
      rw [map_sub, map_one, RingEquiv.apply_symm_apply] at hh
      linear_combination hh
    let a := coord ((t⁻¹).val.1)
    have ha : coord t.val.1 * a = 1 := by
      rw [show a = coord ((t⁻¹).val.1) by rfl, ← map_mul,
        show t.val.1 * (t⁻¹).val.1 = 1 from congrArg Prod.fst t.mul_inv, map_one]
    let N (w : X∞) := (1+w)*a
    have hN : ContDiff ℝ (⊤ : ℕ∞) N := (contDiff_const.add contDiff_id).mul contDiff_const
    have hNy : N y = 1 := by change (1+y)*a = 1; rwa [← h1]
    obtain ⟨L,hL,hEL⟩ := archLog (F := F)
    have hlim : Tendsto N (𝓝 y) (𝓝 1) := hNy ▸ hN.continuous.tendsto y
    have hc' := (eta_log_chart f ξ t).contDiffAt.comp y
      ((show ContDiffAt ℝ (⊤ : ℕ∞) L (N y) from hNy.symm ▸ hL).comp y hN.contDiffAt)
    refine hc'.congr_of_eventuallyEq ?_
    filter_upwards [hlim.eventually hEL] with w hw
    apply congrArg (sLocalTraceEta f ξ)
    apply Prod.ext
    · apply (coord).injective
      change coord ((coord).symm w) = coord (t.val.1 * (coord).symm (NormedSpace.exp (L (N w))) - 1)
      rw [RingEquiv.apply_symm_apply, map_sub, map_one, map_mul, RingEquiv.apply_symm_apply, hw]
      change w = coord t.val.1 * ((1+w)*a) - 1
      rw [mul_left_comm, ha, mul_one]; abel
    · change b = t.val.2 * 1 - 1
      rw [mul_one]; exact (congrArg Prod.snd ht).symm
  · let : T2Space Aₛ := inferInstanceAs (T2Space
      (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [hY.continuousAt.preimage_mem_nhds (hc.isClosed.isOpen_compl.mem_nhds hy)] with w hw
    exact hzero _ hw

/-- A cyclic subgroup small on a compact generating set of the annihilator
lies in the original closed subgroup. -/
private theorem smallPowers {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (K : Subgroup G) (hK : IsBruhatGoodSubgroup K) :
    ∃ W ∈ 𝓝 (1 : G), ∀ x : G, (∀ n : ℕ, x ^ n ∈ W) → x ∈ K := by
  let D := lcaAnnihilator K
  obtain ⟨C, _, hc, hgen⟩ := hK.2.2
  let arc := Circle.centeredArc (Real.pi / 2)
  have ha : arc ∈ 𝓝 (1 : Circle) := by
    simpa [arc] using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
  let W := {x : G | ∀ χ ∈ C, (χ : D).val x ∈ arc}
  have hW : W ∈ 𝓝 (1 : G) := by
    apply hc.eventually_forall_of_forall_eventually
    intro χ _
    have hχ : Continuous (fun χ : D ↦ (χ.val : G →ₜ* Circle)) := continuous_subtype_val
    have he : Continuous (fun p : G × D ↦ p.2.val p.1) :=
      (continuous_eval (F := G →ₜ* Circle)).comp ((hχ.comp ((show Continuous (Prod.snd : G × D → D) from continuous_snd))).prodMk continuous_fst)
    exact he.continuousAt.preimage_mem_nhds (by simpa only [map_one] using ha)
  refine ⟨W, hW, fun x hx ↦ ?_⟩
  let ev : D →* Circle := ⟨⟨fun χ ↦ χ.val x, rfl⟩, fun _ _ ↦ rfl⟩
  have hg : C ⊆ ev.ker := by
    intro χ hχ
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro n _
    change χ.val x ^ n ∈ arc
    simpa only [map_pow] using hx n χ hχ
  have htop : ⊤ ≤ ev.ker := hgen ▸ (Subgroup.closure_le _).mpr hg
  rw [← lcaDualAnnihilator_annihilator K hK.1, mem_lcaDualAnnihilator_iff]
  exact fun χ ↦ htop (Subgroup.mem_top χ)

private theorem power_bound {L : Type*} [NormedField L] [IsUltrametricDist L]
    (y : L) (hy : ‖y‖ ≤ 1) (n : ℕ) : ‖y ^ n - 1‖ ≤ ‖y - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, show y ^ n * y - 1 = (y ^ n - 1) * y + (y - 1) by ring]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
      (by rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) hy).trans ih) le_rfl)

/-- A single finite principal-unit neighborhood fixes an arbitrary joint test. -/
private theorem finite_principal_units (f : BruhatCompactSupport Iₛ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ e : Iₛ, e.val.1 = 1 →
      (∀ v : S, ‖e.val.2 v - 1‖ < r) → ∀ g, f.val (e * g) = f.val g := by
  obtain ⟨K, hK, hfix, _⟩ := ((mem_bruhatSmoothSubmodule_iff _).1 f.property.1) 0
  obtain ⟨W, hW, hsub⟩ := smallPowers K hK
  rw [(sIdeleGroup_description F S).1.nhds_eq_comap] at hW
  obtain ⟨O, hV, hv⟩ := mem_comap.mp hW
  have hpre : (fun b : Bₛ ↦ ((1,b) : Aₛ)) ⁻¹' O ∈ 𝓝 (1 : Bₛ) :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds hV
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨min d 1, lt_min hd zero_lt_one, min_le_right .., fun e he he' g ↦ ?_⟩
  apply hfix ⟨e, hsub e (fun n ↦ hv ?_)⟩ g
  change (e ^ n).val ∈ O
  have harch : (e ^ n).val.1 = 1 := by simp [he]
  rw [show (e ^ n).val = (1, (e ^ n).val.2) from Prod.ext harch rfl]
  apply hball
  rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hd]
  intro v
  change ‖e.val.2 v ^ n - 1‖ < d
  have hy : ‖e.val.2 v‖ ≤ 1 := by
    simpa using (IsUltrametricDist.norm_add_le_max (e.val.2 v - 1) 1).trans
      (max_le ((he' v).le.trans (min_le_right ..)) (norm_one.le))
  exact (power_bound _ hy n).trans_lt ((he' v).trans_le (min_le_left ..))

private theorem eta_finite_invariance (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    ∃ (r : ℝ) (U : OpenAddSubgroup Bₛ), 0 < r ∧ (∀ h : Bₛ, h ∈ U ↔ ∀ v, ‖h v‖ < r) ∧
      ∀ (z : Aₛ) (h : Bₛ), h ∈ U → sLocalTraceEta f ξ (z + (0,h)) = sLocalTraceEta f ξ z := by
  classical
  obtain ⟨r, hr, hr1, hfix⟩ := finite_principal_units f
  let d := ξ.val
  have hct : Continuous (fun g : Iₛ ↦ ((d * g⁻¹)⁻¹).val.2) :=
    continuous_snd.comp (Units.continuous_val.comp (continuous_const.mul continuous_inv).inv)
  obtain ⟨M, hM⟩ := f.property.2.exists_bound_of_continuousOn hct.continuousOn
  let C := max 1 M
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left ..)
  let b := r / C
  have hb : 0 < b := div_pos hr hC
  let P : AddSubgroup Bₛ :=
    { carrier := {h | ∀ v, ‖h v‖ < b}
      zero_mem' := fun v ↦ by simpa using hb
      add_mem' := fun ha hb' v ↦ (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt (ha v) (hb' v))
      neg_mem' := fun ha v ↦ by simpa using ha v }
  have hball : (P : Set Bₛ) = Metric.ball 0 b := by
    ext h
    simp only [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hb]
    rfl
  let U : OpenAddSubgroup Bₛ := ⟨P, by change IsOpen (P : Set Bₛ); rw [hball]; exact Metric.isOpen_ball⟩
  have hsmall (z : Aₛ) (h : Bₛ) (hh : h ∈ U) (hz : sLocalTraceEta f ξ z ≠ 0) :
      sLocalTraceEta f ξ (z + (0,h)) = sLocalTraceEta f ξ z := by
    obtain ⟨t, ht⟩ : 1 + z ∈ range (Units.val : Iₛ → Aₛ) := by
      by_contra hn
      exact hz (Function.extend_apply' _ _ _ hn)
    have he : z = t.val - 1 := by rw [ht]; abel
    subst z
    rw [eta_on_units] at hz ⊢
    let g := (d⁻¹ * t)⁻¹
    have hg : g ∈ tsupport f.val := subset_tsupport f.val (by
      intro he
      exact hz (by change f.val g / _ = 0; rw [he, zero_div]))
    have ht' : d * g⁻¹ = t := by simp [g]
    have hbound : ‖(t⁻¹).val.2‖ ≤ C := by
      simpa only [ht'] using (hM g hg).trans (le_max_right 1 M)
    let a := h * (t⁻¹).val.2
    have ha (v : S) : ‖a v‖ < r := by
      change ‖h v * (t⁻¹).val.2 v‖ < r
      rw [norm_mul]
      calc
        _ ≤ ‖h v‖ * C := mul_le_mul_of_nonneg_left
          ((norm_le_pi_norm _ v).trans hbound) (norm_nonneg _)
        _ < r := (lt_div_iff₀ hC).mp (show ‖h v‖ < b from hh v)
    have hn (v : S) : ‖1 + a v‖ = 1 := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, norm_one, max_eq_left ((ha v).le.trans hr1)]
      rw [norm_one]
      exact ((ha v).trans_le hr1).ne'
    let m : Aₛ := (1, 1 + a)
    have hm : IsUnit m := Prod.isUnit_iff.mpr ⟨isUnit_one, Pi.isUnit_iff.mpr (fun v ↦
      isUnit_iff_ne_zero.mpr (norm_pos_iff.mp ((hn v).symm ▸ zero_lt_one)))⟩
    let e := hm.unit
    have hval : e.val = m := hm.unit_spec
    have hnorm : sIdeleNorm F S e = 1 := by
      apply Units.ext
      apply NNReal.eq
      have h1 (w : InfinitePlace F) : (1 : InfiniteAdeleRing F) w = 1 := rfl
      simp [sIdeleNorm, Units.coe_prod, hval, m, hn, h1]
    have hv : (e * t).val - 1 = t.val - 1 + (0,h) := by
      have hh' : (t⁻¹).val.2 * t.val.2 = 1 := congrArg Prod.snd t.inv_mul
      rw [Units.val_mul, hval]
      apply Prod.ext
      · simp [m]
      · change (1 + h * (t⁻¹).val.2) * t.val.2 - 1 = t.val.2 - 1 + h
        rw [add_mul, one_mul, mul_assoc, hh', mul_one]
        abel
    rw [← hv, eta_on_units]
    have hi := hfix e (by rw [hval]) (fun v ↦ by simpa [hval, m] using ha v) ((d⁻¹ * (e*t))⁻¹)
    rw [show e * (d⁻¹ * (e*t))⁻¹ = g by simp [g, mul_comm, mul_left_comm]] at hi
    change f.val ((d⁻¹ * (e*t))⁻¹) / _ = f.val g / _
    rw [← hi, show ξ.val⁻¹ * (e*t) = e * (ξ.val⁻¹*t) by ac_rfl, map_mul, hnorm, one_mul]
  refine ⟨b, U, hb, fun _ ↦ Iff.rfl, fun z h hh ↦ ?_⟩
  by_cases hz : sLocalTraceEta f ξ z = 0
  · by_contra he
    have hne : sLocalTraceEta f ξ (z + (0,h)) ≠ 0 := hz ▸ he
    apply he
    simpa only [show ((0,-h) : Aₛ) = -(0,h) by simp, add_neg_cancel_right] using (hsmall (z + (0,h)) (-h) (U.neg_mem hh) hne).symm
  · exact hsmall z h hh hz

/-- The finite coordinates descend to a discrete quotient, and only finitely
many quotient classes support a nonzero archimedean slice. -/
private theorem eta_finite_slices (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    ∃ (r : ℝ) (U : OpenAddSubgroup Bₛ), 0 < r ∧ (∀ h : Bₛ, h ∈ U ↔ ∀ v, ‖h v‖ < r) ∧
      ∃ C : Finset (Bₛ ⧸ U.toAddSubgroup),
        let slice := fun (q : Bₛ ⧸ U.toAddSubgroup) (a : InfiniteAdeleRing F) ↦ sLocalTraceEta f ξ (a,q.out)

        (∀ z : Aₛ, sLocalTraceEta f ξ z = slice (QuotientAddGroup.mk z.2) z.1) ∧
        ∀ q ∉ C, ∀ a, slice q a = 0 := by
  classical
  obtain ⟨r,U,hr,hU,hi⟩ := eta_finite_invariance f ξ
  let Q := Bₛ ⧸ U.toAddSubgroup
  let : DiscreteTopology Q := QuotientAddGroup.discreteTopology U.isOpen
  let π : Bₛ → Q := QuotientAddGroup.mk
  let c (g : Iₛ) : Q := π (((ξ.val * g⁻¹).val - 1).2)
  have hc : Continuous c := QuotientAddGroup.continuous_mk.comp (continuous_snd.comp
    ((Units.continuous_val.comp (continuous_const.mul continuous_inv)).sub continuous_const))
  let C := (f.property.2.image hc).finite_of_discrete.toFinset
  let slice (q : Q) (a : InfiniteAdeleRing F) := sLocalTraceEta f ξ (a, q.out)
  refine ⟨r,U,hr,hU,C, fun z ↦ ?_, fun q hq a ↦ ?_⟩
  · have he : π (π z.2).out = π z.2 := Quotient.out_eq _
    have hh := QuotientAddGroup.eq_iff_sub_mem.mp he
    have h := hi z _ hh
    change sLocalTraceEta f ξ z = sLocalTraceEta f ξ (z.1, (π z.2).out)
    rw [← h]
    congr 1
    exact Prod.ext (add_zero _) (by change z.2 + ((π z.2).out - z.2) = _; abel)
  · by_contra hn
    let z : Aₛ := (a, q.out)
    have hz : sLocalTraceEta f ξ z ≠ 0 := hn
    obtain ⟨t, ht⟩ : 1 + z ∈ range (Units.val : Iₛ → Aₛ) := by
      by_contra hu
      exact hz (Function.extend_apply' _ _ _ hu)
    have ht' : t.val - 1 = z := by rw [ht]; abel
    rw [← ht', eta_on_units] at hz
    let g := (ξ.val⁻¹ * t)⁻¹
    have hg : g ∈ tsupport f.val := subset_tsupport f.val (by
      intro he
      exact hz (by change f.val g / _ = 0; rw [he, zero_div]))
    apply hq
    apply (f.property.2.image hc).finite_of_discrete.mem_toFinset.mpr
    refine ⟨g, hg, ?_⟩
    change π (((ξ.val * g⁻¹).val - 1).2) = q
    rw [show ξ.val * g⁻¹ = t by simp [g], ht']
    exact Quotient.out_eq _

private theorem eta_compact (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    HasCompactSupport (sLocalTraceEta f ξ) := by
  let φ (g : Iₛ) : Aₛ := (ξ.val * g⁻¹).val - 1
  have hc : Continuous φ :=
    (Units.continuous_val.comp (continuous_const.mul continuous_inv)).sub continuous_const
  apply HasCompactSupport.intro (f.property.2.image hc)
  intro z hz
  unfold sLocalTraceEta
  by_cases hu : 1 + z ∈ range (Units.val : Iₛ → Aₛ)
  · obtain ⟨t, ht⟩ := hu
    rw [← ht, Units.val_injective.extend_apply]
    have hn : (ξ.val⁻¹ * t)⁻¹ ∉ tsupport f.val := by
      intro h
      apply hz
      refine ⟨_, h, ?_⟩
      simp [φ, ht]
    rw [image_eq_zero_of_notMem_tsupport hn, zero_div]
  · exact Function.extend_apply' _ _ _ hu

private theorem arch_test (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (b : Bₛ) :
    ∃ φ : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)), ∀ a : InfiniteAdeleRing F,
      φ (Multiplicative.ofAdd a) = sLocalTraceEta f ξ (a,b) := by
  let p (a : InfiniteAdeleRing F) := sLocalTraceEta f ξ (a,b)
  let Y (y : X∞) : Aₛ := ((coord).symm y,b)
  have hcs : HasCompactSupport (fun y ↦ sLocalTraceEta f ξ (Y y)) := by
    refine HasCompactSupport.intro ((eta_compact f ξ).image
      ((continuous_infiniteAdeleRingEquivMixedSpace F).comp continuous_fst)) fun y hy ↦ ?_
    apply image_eq_zero_of_notMem_tsupport
    exact fun h ↦ hy ⟨Y y,h, (coord).apply_symm_apply y⟩
  have hm := (mem_archimedeanSchwartzBruhat_iff (F := F) p).2
    ⟨hcs.toSchwartzMap (eta_arch_slice_smooth f ξ b), fun a ↦ by
      change sLocalTraceEta f ξ ((coord).symm (coord a), b) = _
      rw [RingEquiv.symm_apply_apply]⟩
  exact ⟨⟨_,hm⟩, fun _ ↦ rfl⟩

private theorem finite_ball_test (v : S) (a : v.val.adicCompletion F) (r : ℝ) :
    ∃ φ : SchwartzBruhat (Multiplicative (v.val.adicCompletion F)), ∀ y : v.val.adicCompletion F,
      φ (Multiplicative.ofAdd y) = if ‖y-a‖ < r then (1 : ℂ) else 0 := by
  classical
  let : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let U := Metric.ball a r
  have hc : IsClopen U := IsUltrametricDist.isClopen_ball _ _
  apply (mem_finitePlaceSchwartz_iff (F := F) v.val _).2
  constructor
  · apply (IsLocallyConstant.iff_exists_open _).2
    intro x
    by_cases h : x ∈ U
    · refine ⟨U,hc.isOpen,h,fun y hy ↦ ?_⟩
      simp only [Metric.mem_ball, dist_eq_norm, U] at h hy
      simp [h,hy]
    · refine ⟨Uᶜ,hc.isClosed.isOpen_compl,h,fun y hy ↦ ?_⟩
      change y ∉ U at hy
      simp only [Metric.mem_ball, dist_eq_norm, U] at h hy
      simp [h,hy]
  · apply HasCompactSupport.intro (isCompact_closedBall a r)
    intro x hx
    exact ite_eq_right (fun h ↦ hx (Metric.ball_subset_closedBall (by simpa [dist_eq_norm] using h)))

open scoped TensorProduct in
/-- Paper: (12.4.1.20)–(12.4.1.21), p. 518. The translated, zero-extended test
is an additive Schwartz–Bruhat function on the S-adeles.
Deviation: The input can depend jointly on all places. Compact support and finite
translation invariance give a finite expansion in compact-open coset indicators. -/
theorem eta_test (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    ∃ η : testₛ, ∀ z : Aₛ, testAt(η,z) = sLocalTraceEta f ξ z := by
  classical
  obtain ⟨r,U,_,hU,C,hval,hzero⟩ := eta_finite_slices f ξ
  let Q := Bₛ ⧸ U.toAddSubgroup
  let π : Bₛ → Q := QuotientAddGroup.mk
  choose A hA using fun q : Q ↦ arch_test f ξ q.out
  choose B hB using fun (q : Q) (v : S) ↦ finite_ball_test v (q.out v) r
  obtain ⟨T,hT⟩ := sAdeleSchwartz_inductiveTensor_equiv F S
  let t (q : Q) : testₛ := T (A q ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, B q v))
  have hprod (q : Q) (b : Bₛ) : (∀ v, ‖b v - q.out v‖ < r) ↔ π b = q := by
    calc
      _ ↔ b - q.out ∈ U := (hU _).symm
      _ ↔ π b = π q.out := QuotientAddGroup.eq_iff_sub_mem.symm
      _ ↔ π b = q := by rw [show π q.out = q from Quotient.out_eq q]
  have ht (q : Q) (z : Aₛ) : testAt(t q,z) =
      if π z.2 = q then sLocalTraceEta f ξ (z.1,q.out) else 0 := by
    change T _ _ = _
    rw [hT, hA]
    simp_rw [hB]
    simp only [Fintype.prod_ite_zero, hprod q z.2, Finset.prod_const_one]
    split_ifs <;> simp
  refine ⟨∑ q ∈ C, t q, fun z ↦ ?_⟩
  have he : ∀ D : Finset Q, testAt(∑ q ∈ D, t q,z) = ∑ q ∈ D, testAt(t q,z) := by
    intro D
    induction D using Finset.induction_on with
    | empty => rfl
    | insert q D h ih =>
      simp only [Finset.sum_insert h]
      change testAt(t q,z) + _ = _
      rw [← ih]
  rw [he]
  simp_rw [ht]
  by_cases hz : π z.2 ∈ C
  · rw [Finset.sum_eq_single_of_mem (π z.2) hz (fun q _ hq ↦ ite_eq_right (Ne.symm hq)), ite_eq_left rfl]
    exact (hval z).symm
  · rw [Finset.sum_eq_zero fun q hq ↦ ite_eq_right (show π z.2 ≠ q from fun h ↦ hz (h.symm ▸ hq)), hval z]
    exact (hzero _ hz _).symm

end SLocalTraceEta

/-- Paper: (12.4.1.21)–(12.4.1.22), p. 518. The additive Tamagawa Fourier transform
of the translated, zero-extended S-idelic test is integrable.
Deviation: Step III uses Fourier integration on p. 518. We state explicitly the
absolute integrability required for the constant frequency symbol. -/
private theorem sLocalTraceEta_fourier_integrable (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) :
    Integrable (fourierₛ (sLocalTraceEta f ξ)) νₛ := by
  obtain ⟨η, hη⟩ := SLocalTraceEta.eta_test f ξ
  let G := Multiplicative Aₛ
  let μ : Measure G := νₛ
  have hν : (νₛ).IsAddHaarMeasure := sLocalTrace_additiveHaar
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hν.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hν.toIsOpenPosMeasure
      map_mul_left_eq_self := fun y ↦ hν.map_add_left_eq_self y.toAdd }
  let (v : S) : LocallyCompactSpace (v.val.adicCompletion F) := locallyCompactSpace_adicCompletion _
  let : T2Space G := inferInstanceAs (T2Space
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace G := inferInstanceAs (LocallyCompactSpace Aₛ)
  let : BorelSpace G := sAdeleRing_borelSpace (F := F) (S := S)
  rw [← funext hη]
  exact SchwartzBruhat.integrable μ (sAdeleSchwartzFourier η)

/-- Paper: (12.4.1.12)–(12.4.1.22), pp. 517–518. The skew diagonal of the
composed kernel is the integral of the Fourier transform of the translated test,
weighted by both cutoffs.
Deviation: Retain the cutoffs in the exact identity, and write the skew diagonal
with its output first. Measurable bounded even frequency symbols suffice here. -/
theorem sLocalTraceCutoffKernel_skew (f : BruhatCompactSupport Iₛ)
    (ρ : Iₛ → ℂ) (ρ' : Aₛ → ℂ) (_hρ' : Measurable ρ')
    (_hBound : ∃ C : ℝ, ∀ u, ‖ρ' u‖ ≤ C) (_hEven : ∀ u, ρ' (-u) = ρ' u)
    (ξ : Hₛ) (x : Iₛ) :
    Integrable (fun u ↦ ρ' u * fourierₛ (sLocalTraceEta f ξ) (x.val * u)) νₛ ∧
      sLocalTraceCutoffKernel f ρ ρ' (ξ.val * x) x.val =
        ρ (ξ.val * x) * (sLocalTraceMeasureFactor S : ℂ) *
          ∫ u, ρ' u * fourierₛ (sLocalTraceEta f ξ) (x.val * u) ∂νₛ := by
  obtain ⟨M, hM⟩ := _hBound
  exact ⟨sLocalTrace_integrable_symbol_dilate _ (sLocalTraceEta_fourier_integrable f ξ)
    x ρ' _hρ' M hM, sLocalTraceCutoffKernel_skew_eq f ρ ρ' _hEven ξ x⟩

/-- Paper: (12.4.1.23)–(12.4.1.24), p. 518. One sharp orbital mass integrates
the transformed test against the logarithmic width of the spatial norm interval.
Deviation: This defines the sharp one-sided expression for a product of radii.
The additive integral omits the null nonunit locus before taking its logarithm. -/
def sLocalTraceSharpMass (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (R : ℝ) : ℂ :=
  (volume₁ : ℂ) * ∫ w in band(R) ∩ range (Units.val : Iₛ → Aₛ),
    fourierₛ (sLocalTraceEta f ξ) w * ((Real.log R - Real.log (modS(w)) : ℝ) : ℂ) ∂νₛ

/-- Paper: (12.4.1.24), p. 518. The sharp orbital mass of the zero lift vanishes
at every radius. -/
theorem sLocalTraceSharpMass_zero (ξ : Hₛ) (R : ℝ) :
    sLocalTraceSharpMass (0 : BruhatCompactSupport Iₛ) ξ R = 0 := by
  have h0 : sLocalTraceEta (0 : BruhatCompactSupport Iₛ) ξ = 0 := by
    funext z
    have h : (0 : BruhatCompactSupport Iₛ).val = 0 := rfl
    simp only [sLocalTraceEta, h]
    simp
  have h1 : fourierₛ (0 : Aₛ → ℂ) = 0 := by
    funext w; simp [tamagawaFourier]
  simp [sLocalTraceSharpMass, h0, h1]

/-- Paper: (12.4.1.22)–(12.4.1.24), p. 518. With sharp upper cutoffs the orbital
mass is the skew-diagonal integral on an S-unit fundamental domain. The change
of variable w = xu converts the integral to the log-weighted Fourier integral.
Deviation: Use the sharp indicators explicitly. The spatial variable is an S-idele,
and its additive integral uses the image of the fundamental domain under the unit embedding. -/
theorem sLocalTraceSharpMass_eq_integral (f : BruhatCompactSupport Iₛ) (ξ : Hₛ)
    (D : Set Iₛ) (_hD : IsFundamentalDomain Hₛ D μₛ)
    (L L' : ℝ) (_hL : 0 < L) (_hL' : 0 < L') :
    let d := D ∩ {x : Iₛ | normS(x) ≤ L}
    let K := sLocalTraceCutoffKernel f (indicator {x : Iₛ | normS(x) ≤ L} (fun _ ↦ 1))
      (indicator band(L') (fun _ ↦ 1))
    let diag := fun x : Iₛ ↦ K (ξ.val * x) x.val
    IntegrableOn diag d ((νₛ).comap (Units.val : Iₛ → Aₛ)) ∧
      (∫ x in d, diag x ∂((νₛ).comap (Units.val : Iₛ → Aₛ))) =
        sLocalTraceSharpMass f ξ (L * L') := by sorry

local notation "archTest" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest" => ((v : S) → BruhatCompactSupport (v.val.adicCompletion F)ˣ)
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "finiteVolume(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal
local notation "principalValues(" a "," b ")" =>
  ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
    ∑ v : S, ((Real.log (v.val.asIdeal.absNorm : ℝ) / finiteVolume(v.val) : ℝ) : ℂ) *
      finiteConnesWeilPrincipalValue v.val 1 (b v))

/-- Summation bookkeeping for `sLocalTraceSharpMass_asymptotic`: if the masses split as the
logarithmic term, a summable constant term and a remainder that sums to something tending
to zero, then the summed masses have the stated asymptotic. -/
private theorem sLocalTraceSharpMass_asymptotic_assemble {ι : Type*} (m : ι → ℝ → ℂ)
    (y κ : ι → ℂ) (K P c : ℂ) (T : ℝ → ℂ) (hy : HasSum y c) (hκ : HasSum κ P)
    (hT : ∀ᶠ R in atTop, HasSum (fun i ↦ m i R - K * (y i * (Real.log R : ℂ) + κ i)) (T R))
    (hT0 : Tendsto T atTop (𝓝 0)) :
    ∃ M : ℝ → ℂ, (∀ᶠ R in atTop, HasSum (fun i ↦ m i R) (M R)) ∧
      Tendsto (fun R ↦ M R - K * c * (Real.log R : ℂ)) atTop (𝓝 (K * P)) := by
  refine ⟨fun R ↦ T R + K * (c * (Real.log R : ℂ) + P), ?_, ?_⟩
  · filter_upwards [hT] with R hR
    have h := hR.add (((hy.mul_right (Real.log R : ℂ)).add hκ).mul_left K)
    simpa using h
  · have h := hT0.add_const (K * P)
    rw [zero_add] at h
    refine h.congr fun R ↦ ?_
    ring

/-- Paper: (12.4.1.26)–(12.4.1.28), p. 519. The restrictions of the global test to the
local unit groups at the infinite places and at the places of S are compactly supported
Bruhat tests. -/
private theorem sLocalTraceSharpMass_asymptotic_restrict (φ : BruhatCompactSupport C𝔽) :
    ∃ (a : archTest) (b : finiteTest),
      (∀ (w : InfinitePlace F) (u : w.Completionˣ),
        (a w).val u = φ.val (archClass(w) u)) ∧
      (∀ (v : S) (u : (v.val.adicCompletion F)ˣ),
        (b v).val u = φ.val (finiteClass(v.val) u)) := by sorry

/-- Paper: (12.4.1.25)–(12.4.1.28), p. 519. Constant term of the summed sharp masses.
For each S-unit ξ the constant term of the sharp mass is minus the pairing of the Fourier
transform of the translated test with the logarithm of the S-norm. Only finitely many ξ
contribute, and the sum is the sum of the local Connes–Weil principal values of the
restrictions of φ to the local unit groups.
Deviation: The printed proof does this in one display. The route is a partial Fourier
inversion per place, discreteness of the S-units after dropping one place, the lift
identity, and invariance of the principal values under u ↦ u⁻¹ (the last step on p. 519). -/
private theorem sLocalTraceSharpMass_asymptotic_const
    (φ : BruhatCompactSupport C𝔽)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (_hRamified : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (_hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (_hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (a : archTest) (b : finiteTest)
    (_ha : ∀ (w : InfinitePlace F) (u : w.Completionˣ),
      (a w).val u = φ.val (archClass(w) u))
    (_hb : ∀ (v : S) (u : (v.val.adicCompletion F)ˣ),
      (b v).val u = φ.val (finiteClass(v.val) u)) :
    HasSum (fun ξ : Hₛ ↦ -∫ w in range (Units.val : Iₛ → Aₛ),
        fourierₛ (sLocalTraceEta f ξ) w * ((Real.log (modS(w)) : ℝ) : ℂ) ∂νₛ)
      principalValues(a, b) := by sorry

/-- Paper: (12.4.1.25)–(12.4.1.27), p. 519. Remainder of the summed sharp masses.
For each S-unit ξ, Fourier inversion splits the sharp mass into the logarithmic term
`f(ξ) log R`, the constant term, and an integral over the Fourier region `|w|_S > R`.
These remainders are summable over the S-units for large R and their sum tends to zero.
Deviation: The paper does not treat the sum over ξ; it cites [Co, §VII, Thm 4]. -/
private theorem sLocalTraceSharpMass_asymptotic_tail
    (_hRamified : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (f : BruhatCompactSupport Iₛ) :
    ∃ T : ℝ → ℂ, (∀ᶠ R in atTop, HasSum (fun ξ : Hₛ ↦ sLocalTraceSharpMass f ξ R -
        (volume₁ : ℂ) * (f.val ξ.val * (Real.log R : ℂ) +
          -∫ w in range (Units.val : Iₛ → Aₛ),
            fourierₛ (sLocalTraceEta f ξ) w * ((Real.log (modS(w)) : ℝ) : ℂ) ∂νₛ)) (T R)) ∧
      Tendsto T atTop (𝓝 0) := by sorry

/-- Paper: (12.4.1.25)–(12.4.1.28), p. 519. After subtraction of the logarithmic
term the sum of sharp orbital masses tends to the norm-one volume times the local
principal values.
Deviation: Uses the sharp expression from (12.4.1.24) with R = λλ′. The replacement
of φ(g⁻¹) by φ(g) is the last step on p. 519. Appendix B.4 incorporates the real and
complex normalization factors in the archimedean distributions. -/
theorem sLocalTraceSharpMass_asymptotic
    (φ : BruhatCompactSupport C𝔽)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (_hRamified : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (_hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (_hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g)))) :
    ∃ (a : archTest) (b : finiteTest) (M : ℝ → ℂ),
      (∀ (w : InfinitePlace F) (u : w.Completionˣ),
        (a w).val u = φ.val (archClass(w) u)) ∧
      (∀ (v : S) (u : (v.val.adicCompletion F)ˣ),
        (b v).val u = φ.val (finiteClass(v.val) u)) ∧
      (∀ᶠ R in atTop, HasSum (fun ξ : Hₛ ↦ sLocalTraceSharpMass f ξ R) (M R)) ∧
      Tendsto (fun R ↦ M R - (volume₁ : ℂ) * φ.val 1 * (Real.log R : ℂ))
        atTop (𝓝 ((volume₁ : ℂ) * principalValues(a, b))) := by
  obtain ⟨a, b, ha, hb⟩ := sLocalTraceSharpMass_asymptotic_restrict φ
  have hκ := sLocalTraceSharpMass_asymptotic_const φ _hPic _hRamified _hOutside f _hLift
    a b ha hb
  obtain ⟨T, hT, hT0⟩ := sLocalTraceSharpMass_asymptotic_tail _hRamified f
  have hy : HasSum (fun ξ : Hₛ ↦ f.val ξ.val) (φ.val 1) := by
    have h := _hLift 1
    simp only [mul_one, map_one, QuotientGroup.mk_one] at h
    exact h
  obtain ⟨M, hM, hlim⟩ := sLocalTraceSharpMass_asymptotic_assemble
    (fun ξ R ↦ sLocalTraceSharpMass f ξ R) (fun ξ : Hₛ ↦ f.val ξ.val) _ _ _ _ T hy hκ hT hT0
  exact ⟨a, b, M, ha, hb, hM, hlim⟩

-- TODO(paper-gap): Theorem 12.4.1.1 needs the actual smoothed PW quotient kernel
-- and a limit for its difference from the sharp orbital mass. Neither the cutoff
-- family with the independent lower bound nor the comparison is specified.
-- The following statement records the conclusion with that comparison exposed.

/-- Paper: Theorem 12.4.1.1, p. 514. The normalized quotient diagonal integral,
with its logarithmic term removed, tends to the sum of local principal values.
Deviation: The chosen quotient kernel must have integrable diagonals and agree
asymptotically with the summed sharp masses. These hypotheses expose the missing
comparison with the regularized Paley–Wiener operator. The limit is joint. -/
theorem sLocalTrace_asymptotic_of_sharp_comparison
    (φ : BruhatCompactSupport C𝔽)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (_hRamified : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (_hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (_hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (k : ℝ × ℝ → Jₛ → Jₛ → ℂ) (M : ℝ → ℂ)
    (_hSum : ∀ᶠ R in atTop, HasSum (fun ξ : Hₛ ↦ sLocalTraceSharpMass f ξ R) (M R))
    (_hDiag : ∀ᶠ p in atTop ×ˢ atTop, Integrable (fun x ↦ k p x x) μJ)
    (_hComparison : Tendsto
      (fun p : ℝ × ℝ ↦ (∫ x, k p x x ∂μJ) - M (p.1 * p.2))
      (atTop ×ˢ atTop) (𝓝 0)) :
    ∃ (a : archTest) (b : finiteTest),
      (∀ (w : InfinitePlace F) (u : w.Completionˣ),
        (a w).val u = φ.val (archClass(w) u)) ∧
      (∀ (v : S) (u : (v.val.adicCompletion F)ˣ),
        (b v).val u = φ.val (finiteClass(v.val) u)) ∧
      Tendsto (fun p : ℝ × ℝ ↦ (∫ x, k p x x ∂μJ) / (volume₁ : ℂ) -
        φ.val 1 * (Real.log (p.1 * p.2) : ℂ)) (atTop ×ˢ atTop) (𝓝 principalValues(a, b)) := by
  obtain ⟨a, b, N, ha, hb, hsum, hN⟩ :=
    sLocalTraceSharpMass_asymptotic (F := F) (S := S) φ _hPic _hRamified _hOutside f _hLift
  refine ⟨a, b, ha, hb, ?_⟩
  have heq : N =ᶠ[atTop] M := by
    filter_upwards [hsum, _hSum] with R h₁ h₂ using h₁.unique h₂
  have hM : Tendsto (fun R ↦ M R - (volume₁ : ℂ) * φ.val 1 * (Real.log R : ℂ))
      atTop (𝓝 ((volume₁ : ℂ) * principalValues(a, b))) :=
    hN.congr' (heq.mono fun R h ↦ by simp only [h])
  have hp : Tendsto (fun p : ℝ × ℝ ↦ p.1 * p.2) (atTop ×ˢ atTop) atTop :=
    tendsto_fst.atTop_mul_atTop₀ tendsto_snd
  let G := (sIdeleQuotientNorm F S).ker
  let : CompactSpace G := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let μ := sLocalNormOneQuotientMeasure F S
  have : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have hv : (volume₁ : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨?_, ?_⟩)
    · exact isOpen_univ.measure_ne_zero μ univ_nonempty
    · exact measure_ne_top μ univ
  have h := (_hComparison.add (hM.comp hp)).div_const (volume₁ : ℂ)
  have hc : (0 + (volume₁ : ℂ) * principalValues(a, b)) / (volume₁ : ℂ) = principalValues(a, b) := by
    rw [zero_add, mul_comm, mul_div_cancel_right₀ _ hv]
  rw [hc] at h
  refine h.congr' (Eventually.of_forall fun p ↦ ?_)
  change ((∫ x, k p x x ∂μJ) - M (p.1 * p.2) +
    (M (p.1 * p.2) - (volume₁ : ℂ) * φ.val 1 * (Real.log (p.1 * p.2) : ℂ))) / _ = _
  field_simp
  ring

end RiemannMasullo
