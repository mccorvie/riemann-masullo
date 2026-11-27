module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelBridge
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelAverage
public import RiemannMasullo.AppC_LCTVS.Sec3a_IsometryTransport
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # The trace of the compression on the level of the project, over `ℚ` with no finite place

Paper: Theorem 12.4.1.1, pp. 514–519, with Definition 11.2.1.3(1), p. 488.

`Sec4_RealPWLevelBridge` carries the level `sLocalInvariantPWSobolev` of the project, for
`F = ℚ`, `S = ∅`, order zero and twist `1/2`, onto `realPWLevel Y` by an isometry `U`.
`Sec4_RealPWLevelAverage` computes the trace of the compression of the averaged dilation on
`realPWLevel Y`. This file carries the operators and the trace back, so that the statement is
about the weighted space of the project and its own level.

* `ratEmptyTranslation h` and `ratEmptyCutoff L`: translation by a class `h` of the quotient,
  and the cutoff to the classes of norm at most `L`, on the weighted space of the project.
* `ratEmpty_translation_intertwine` and `ratEmpty_cutoff_intertwine`: `U` carries the
  translation by a class of norm `t` to the dilation `D_t`, and the cutoff to norm at most `L`
  to the cutoff to `[-L, L]`.
* `ratEmpty_hilbertTrace_average_compression`: with `P` the orthogonal projection onto the
  level of the project, `χ_L` the cutoff and `A F = ∫ t in a..b, (φ t / t) • F ((σ t)⁻¹ ·)` the
  action of a test, `P ∘ χ_L ∘ A ∘ P` is nuclear and its Hilbert trace is
  `∫ g in a..b, φ g * realPWLevelCompressionTrace Y L g / g`.
* `ratEmpty_tendsto_hilbertTrace_average_compression`: as `Y * L → ∞` these traces tend to the
  real-place term of (12.5.1.1) minus `∫ φ(g) min(g^(1/2), g^(-1/2)) d×g`, for `φ` continuous
  on an interval of `(0, ∞)` that does not contain `1`.

The trace is transported by `hilbertTrace_eq_of_isometry_intertwining`: the operator on the
project's space is intertwined by `U` with the operator on `L²(ℝ)`, whose range lies in the
range of `U`.

**Not formalized.** The cutoffs are the sharp cutoff to norm at most `L` and no lower cutoff.
The paper does not specify its cutoffs. The action of the test is written in the norm
coordinate, in which the quotient measure is a constant multiple of `dt / t`. The limit is
compared with the principal value of the project in `Sec4_RealPWLevelPrincipalValue`. Order
zero and the field `ℚ` with no finite place only.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal ENNReal NumberField.AdeleRing Topology InnerProductSpace

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSIdeleQuotientMeasurableSpaceSec1

local notation "mₛ(" F ", " S ")" =>
  (continuousSIdeleQuotientNorm F S :
    SIdeleQuotient F S →ₜ* ℝ≥0ˣ)
local notation "μₛ(" F ", " S ")" => sLocalQuotientTamagawaMeasure F S
local notation "localMeasure(" F ", " S ", " s ")" =>
  (μₛ(F, S)).withDensity (fun g ↦
    ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (((mₛ(F, S)) g).val : ℝ))))
local notation "J₀" => SIdeleQuotient ℚ ∅
local notation "W₀" => Lp ℂ 2 (localMeasure(ℚ, ∅, 0))
local notation "H" => Lp ℂ 2 (volume : Measure ℝ)
local notation "normℝ(" g ")" => (((sIdeleQuotientNorm ℚ ∅ g : ℝ≥0ˣ) : ℝ≥0) : ℝ)

/-! ### General operators -/

section General

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- Multiplication by the indicator of a measurable set, as an operator on `L²`. -/
def lpIndicatorCLM {s : Set α} (hs : MeasurableSet s) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ((Lp.memLp f).indicator hs.nullMeasurableSet).toLp _
      map_add' := fun f g ↦ by
        refine Lp.ext ?_
        filter_upwards [((Lp.memLp (f + g)).indicator hs.nullMeasurableSet).coeFn_toLp,
          Lp.coeFn_add (((Lp.memLp f).indicator hs.nullMeasurableSet).toLp _)
            (((Lp.memLp g).indicator hs.nullMeasurableSet).toLp _),
          ((Lp.memLp f).indicator hs.nullMeasurableSet).coeFn_toLp,
          ((Lp.memLp g).indicator hs.nullMeasurableSet).coeFn_toLp, Lp.coeFn_add f g]
          with x h1 h2 h3 h4 h5
        rw [h1, h2, Pi.add_apply, h3, h4]
        by_cases hx : x ∈ s
        · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx, h5, Pi.add_apply]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx, add_zero]
      map_smul' := fun c f ↦ by
        refine Lp.ext ?_
        filter_upwards [((Lp.memLp (c • f)).indicator hs.nullMeasurableSet).coeFn_toLp,
          Lp.coeFn_smul c (((Lp.memLp f).indicator hs.nullMeasurableSet).toLp _),
          ((Lp.memLp f).indicator hs.nullMeasurableSet).coeFn_toLp, Lp.coeFn_smul c f]
          with x h1 h2 h3 h5
        rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3]
        by_cases hx : x ∈ s
        · rw [indicator_of_mem hx, indicator_of_mem hx, h5, Pi.smul_apply]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, smul_zero] }
    1 (fun f ↦ by
      rw [one_mul]
      change ‖((Lp.memLp f).indicator hs.nullMeasurableSet).toLp _‖ ≤ ‖f‖
      rw [Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
        (eLpNorm_indicator_le _ hs.nullMeasurableSet))

/-- The operator of multiplication by an indicator gives the class of `1_s f`. -/
theorem coeFn_lpIndicatorCLM {s : Set α} (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    (lpIndicatorCLM μ hs f : α → ℂ) =ᵐ[μ] s.indicator f :=
  ((Lp.memLp f).indicator hs.nullMeasurableSet).coeFn_toLp

end General

/-- A linear isometry of Hilbert spaces carries the orthogonal projection onto a subspace to the
orthogonal projection onto its image. -/
theorem LinearIsometry.map_starProjection' {W E : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [NormedAddCommGroup E] [InnerProductSpace ℂ E] (U : W →ₗᵢ[ℂ] E)
    (K : Submodule ℂ W) [K.HasOrthogonalProjection] (K' : Submodule ℂ E)
    [K'.HasOrthogonalProjection] (hK : K.map U.toLinearMap = K') (v : W) :
    U (K.starProjection v) = K'.starProjection (U v) := by
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · rw [← hK]
    exact Submodule.mem_map_of_mem (Submodule.starProjection_apply_mem K v)
  · intro w hw
    rw [← hK] at hw
    obtain ⟨k, hk, rfl⟩ := hw
    rw [← map_sub]
    change ⟪U (v - K.starProjection v), U k⟫_ℂ = 0
    rw [U.inner_map_map]
    exact Submodule.starProjection_inner_eq_zero v k hk

/-! ### Translation and cutoff on the weighted space of the project -/

/-- At order zero the weighted measure of the project is the quotient measure. -/
theorem ratEmpty_localMeasure_eq : localMeasure(ℚ, ∅, 0) = μₛ(ℚ, ∅) := by
  conv_rhs => rw [← withDensity_one (μ := μₛ(ℚ, ∅))]
  congr 1
  funext g
  simp [intervalSobolevDensity]

/-- Left translation preserves the measure of the weighted space at order zero. -/
theorem measurePreserving_mul_left_ratEmpty (h : J₀) :
    MeasurePreserving (fun g : J₀ ↦ h⁻¹ * g) (localMeasure(ℚ, ∅, 0))
      (localMeasure(ℚ, ∅, 0)) := by
  have : BorelSpace J₀ := ⟨rfl⟩
  have : (μₛ(ℚ, ∅)).IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := ℚ) (S := ∅)).1
  rw [ratEmpty_localMeasure_eq]
  exact measurePreserving_mul_left _ h⁻¹

/-- Translation by a class `h` of the quotient on the weighted space of the project over `ℚ`
with no finite place at order zero: `F ↦ F (h⁻¹ ·)`. -/
def ratEmptyTranslation (h : J₀) : W₀ →L[ℂ] W₀ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun g : J₀ ↦ h⁻¹ * g)
    (measurePreserving_mul_left_ratEmpty h)).toContinuousLinearMap

/-- The translate of `F` by `h` is the class of `g ↦ F (h⁻¹ g)`. -/
theorem coeFn_ratEmptyTranslation (h : J₀) (F : W₀) :
    (ratEmptyTranslation h F : J₀ → ℂ) =ᵐ[localMeasure(ℚ, ∅, 0)] fun g ↦ F (h⁻¹ * g) :=
  Lp.coeFn_compMeasurePreserving F (measurePreserving_mul_left_ratEmpty h)

/-- The classes of norm at most `L` form a measurable set. -/
theorem measurableSet_ratEmptyNormLE (L : ℝ) : MeasurableSet {g : J₀ | normℝ(g) ≤ L} := by
  have : BorelSpace J₀ := ⟨rfl⟩
  have hc : Continuous fun g : J₀ ↦ normℝ(g) :=
    NNReal.continuous_coe.comp
      (Units.continuous_val.comp (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous)
  exact (isClosed_le hc continuous_const).measurableSet

/-- The cutoff to the classes of norm at most `L`, on the weighted space of the project over `ℚ`
with no finite place at order zero. -/
def ratEmptyCutoff (L : ℝ) : W₀ →L[ℂ] W₀ :=
  lpIndicatorCLM _ (measurableSet_ratEmptyNormLE L)

/-- Under the isometry of the bridge, the cutoff to norm at most `L` becomes the cutoff to
`[-L, L]`. -/
theorem ratEmpty_cutoff_intertwine {U : W₀ →ₗᵢ[ℂ] H} {κ : ℝ → J₀} {c : ℝ}
    (hκ : ∀ x : ℝ, x ≠ 0 → normℝ(κ x) = |x|)
    (hU : ∀ F : W₀, (U F : ℝ → ℂ) =ᵐ[volume] fun x ↦
      ((c * |x| ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * F (κ x))
    (hq : QuasiMeasurePreserving κ volume (localMeasure(ℚ, ∅, 0))) (L : ℝ) (F : W₀) :
    U (ratEmptyCutoff L F) = realCutoff L (U F) := by
  refine Lp.ext ?_
  have h0 : ∀ᵐ x : ℝ, x ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  filter_upwards [hU (ratEmptyCutoff L F),
    hq.ae (coeFn_lpIndicatorCLM _ (measurableSet_ratEmptyNormLE L) F),
    coeFn_realCutoff L (U F), hU F, h0] with x e1 e2 e3 e4 hx
  rw [e1, e3]
  have e2' : (ratEmptyCutoff L F : J₀ → ℂ) (κ x) =
      {g : J₀ | normℝ(g) ≤ L}.indicator F (κ x) := e2
  rw [e2']
  have hmem : κ x ∈ {g : J₀ | normℝ(g) ≤ L} ↔ x ∈ Icc (-L) L := by
    change normℝ(κ x) ≤ L ↔ _
    rw [hκ x hx, mem_Icc]
    exact abs_le
  by_cases hxL : x ∈ Icc (-L) L
  · rw [indicator_of_mem hxL, indicator_of_mem (hmem.mpr hxL), e4]
  · rw [indicator_of_notMem hxL, indicator_of_notMem (mt hmem.mp hxL), mul_zero]

/-- Under the isometry of the bridge, the translation by a class of norm `t` becomes the
dilation `D_t`. -/
theorem ratEmpty_translation_intertwine {U : W₀ →ₗᵢ[ℂ] H} {κ : ℝ → J₀} {c : ℝ}
    (hκ : ∀ x : ℝ, x ≠ 0 → normℝ(κ x) = |x|)
    (hU : ∀ F : W₀, (U F : ℝ → ℂ) =ᵐ[volume] fun x ↦
      ((c * |x| ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * F (κ x))
    (hq : QuasiMeasurePreserving κ volume (localMeasure(ℚ, ∅, 0))) (h : J₀) (F : W₀) :
    U (ratEmptyTranslation h F) = realDilation normℝ(h) (U F) := by
  have ht : 0 < normℝ(h) := NNReal.coe_pos.mpr (Units.zero_lt _)
  generalize htdef : normℝ(h) = t at ht ⊢
  refine Lp.ext ?_
  have h0 : ∀ᵐ x : ℝ, x ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  have hdiv := (quasiMeasurePreserving_div_const_real ht).ae (hU F)
  filter_upwards [hU (ratEmptyTranslation h F), hq.ae (coeFn_ratEmptyTranslation h F),
    coeFn_realDilation ht (U F), hdiv, h0] with x e1 e2 e3 e4 hx
  rw [e1, e3, e4]
  have e2' : (ratEmptyTranslation h F : J₀ → ℂ) (κ x) = F (h⁻¹ * κ x) := e2
  rw [e2']
  have hxt : x / t ≠ 0 := div_ne_zero hx ht.ne'
  have hclass : h⁻¹ * κ x = κ (x / t) := by
    apply ratEmptyLevel_norm_injective
    apply Units.ext
    apply NNReal.coe_injective
    have h1 : normℝ(h⁻¹ * κ x) = t⁻¹ * |x| := by
      simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, NNReal.coe_mul,
        NNReal.coe_inv, hκ x hx, htdef]
    change normℝ(h⁻¹ * κ x) = normℝ(κ (x / t))
    rw [h1, hκ _ hxt, abs_div, abs_of_pos ht]
    ring
  rw [hclass]
  have hs : √t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have h2 : t ^ (-(1 / 2) : ℝ) = (√t)⁻¹ := by
    rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
  have hcoef : c * |x| ^ (-(1 / 2) : ℝ) = (√t)⁻¹ * (c * |x / t| ^ (-(1 / 2) : ℝ)) := by
    rw [abs_div, abs_of_pos ht, Real.div_rpow (abs_nonneg x) ht.le, h2]
    field_simp
  rw [hcoef]
  push_cast
  ring

/-! ### Transport of the averaged compression along an isometry -/

section Transport

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  {a b : ℝ} {φ : ℝ → ℝ}

/-- If an isometry `U` into `L²(ℝ)` carries a family `τ t` of operators to the dilations `D_t`
for `t` in `[a, b]`, then there is an operator `A` with `A F = ∫ (φ t / t) • τ t F` that `U`
carries to the averaged dilation. -/
theorem exists_average_of_isometry_intertwining (U : W →ₗᵢ[ℂ] H) (τ : ℝ → W →L[ℂ] W)
    (ha : 0 < a) (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b))
    (hτ : ∀ t ∈ Icc a b, ∀ F : W, U (τ t F) = realDilation t (U F)) :
    ∃ A : W →L[ℂ] W, (∀ F : W, A F = ∫ t in a..b, ((φ t / t : ℝ) : ℂ) • τ t F) ∧
      ∀ F : W, U (A F) = realDilationAverage φ a b (U F) := by
  let Uc : W →L[ℂ] H := U.toContinuousLinearMap
  let Ua : H →L[ℂ] W := ContinuousLinearMap.adjoint Uc
  have hUU : Ua ∘L Uc = ContinuousLinearMap.id ℂ W :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self Uc).mp U.norm_map
  have hUU' : ∀ w : W, Ua (U w) = w := fun w ↦ DFunLike.congr_fun hUU w
  have hAU : ∀ G : W, realDilationAverage φ a b (U G) =
      ∫ t in a..b, ((φ t / t : ℝ) : ℂ) • U (τ t G) := by
    intro G
    rw [realDilationAverage_apply ha hab hφ]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hab] at ht
    exact congrArg (fun v ↦ ((φ t / t : ℝ) : ℂ) • v) (hτ t ht G).symm
  have hintU : ∀ G : W, IntervalIntegrable
      (fun t ↦ ((φ t / t : ℝ) : ℂ) • U (τ t G)) volume a b := by
    intro G
    refine (intervalIntegrable_smul_realDilation ha hab hφ (U G)).congr_ae ?_
    rw [uIoc_of_le hab]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact congrArg (fun v ↦ ((φ t / t : ℝ) : ℂ) • v) (hτ t ⟨ht.1.le, ht.2⟩ G).symm
  refine ⟨Ua ∘L realDilationAverage φ a b ∘L Uc, fun F ↦ ?_, fun F ↦ ?_⟩
  · change Ua (realDilationAverage φ a b (U F)) = _
    rw [hAU F, ← ContinuousLinearMap.intervalIntegral_comp_comm Ua (hintU F)]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    change Ua (((φ t / t : ℝ) : ℂ) • U (τ t F)) = _
    rw [map_smul, hUU']
  · change U (Ua (realDilationAverage φ a b (U F))) = _
    have h := ContinuousLinearMap.intervalIntegral_comp_comm (Uc ∘L Ua) (hintU F)
    rw [hAU F]
    change (Uc ∘L Ua) _ = _
    rw [← h]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    change Uc (Ua (((φ t / t : ℝ) : ℂ) • U (τ t F))) = _
    rw [map_smul, map_smul, hUU']
    rfl

/-- **Transport of the trace of the averaged compression.** Let `U` be an isometry into `L²(ℝ)`
that carries operators `PW`, `χ` and `A` to the projection onto the real Paley–Wiener level,
the cutoff and the averaged dilation, and whose range contains the level. Then `PW ∘ χ ∘ A ∘ PW`
is nuclear, with the trace of the compression of the averaged dilation. -/
theorem hilbertTrace_average_compression_of_isometry {Y L : ℝ} (U : W →ₗᵢ[ℂ] H)
    (PW χ A : W →L[ℂ] W) (hY : 0 < Y) (hL : 0 ≤ L) (ha : 0 < a) (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b))
    (hP : ∀ v : W, U (PW v) = (realPWLevel Y).starProjection (U v))
    (hC : ∀ F : W, U (χ F) = realCutoff L (U F))
    (hA : ∀ F : W, U (A F) = realDilationAverage φ a b (U F))
    (hrange : ∀ v ∈ realPWLevel Y, ∃ w : W, U w = v) :
    ∃ hn : IsNuclearOperator (PW ∘L χ ∘L A ∘L PW),
      hilbertTrace ⟨PW ∘L χ ∘L A ∘L PW, hn⟩ =
        ∫ g in a..b, (φ g : ℂ) * realPWLevelCompressionTrace Y L g / (g : ℂ) := by
  let Uc : W →L[ℂ] H := U.toContinuousLinearMap
  let Ua : H →L[ℂ] W := ContinuousLinearMap.adjoint Uc
  have hUU : Ua ∘L Uc = ContinuousLinearMap.id ℂ W :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self Uc).mp U.norm_map
  have hUU' : ∀ w : W, Ua (U w) = w := fun w ↦ DFunLike.congr_fun hUU w
  have hint : Uc ∘L (PW ∘L χ ∘L A ∘L PW) =
      ((realPWLevel Y).starProjection ∘L realCutoff L ∘L realDilationAverage φ a b ∘L
        (realPWLevel Y).starProjection) ∘L Uc := by
    ext1 F
    change U (PW (χ (A (PW F)))) = (realPWLevel Y).starProjection (realCutoff L
      (realDilationAverage φ a b ((realPWLevel Y).starProjection (U F))))
    rw [hP, hC, hA, hP]
  have hrange' : Uc ∘L (ContinuousLinearMap.adjoint Uc ∘L
      ((realPWLevel Y).starProjection ∘L realCutoff L ∘L realDilationAverage φ a b ∘L
        (realPWLevel Y).starProjection)) =
      (realPWLevel Y).starProjection ∘L realCutoff L ∘L realDilationAverage φ a b ∘L
        (realPWLevel Y).starProjection := by
    ext1 v
    obtain ⟨w, hw⟩ := hrange _ (Submodule.starProjection_apply_mem (realPWLevel Y)
      (realCutoff L (realDilationAverage φ a b ((realPWLevel Y).starProjection v))))
    change U (Ua ((realPWLevel Y).starProjection (realCutoff L (realDilationAverage φ a b
      ((realPWLevel Y).starProjection v))))) = _
    rw [← hw, hUU']
    exact hw
  obtain ⟨hS, htrace⟩ := hilbertTrace_eq_of_isometry_intertwining U
    ⟨(realPWLevel Y).starProjection ∘L realCutoff L ∘L realDilationAverage φ a b ∘L
      (realPWLevel Y).starProjection,
      isNuclearOperator_realPWLevel_average_compression hY hL ha hab hφ⟩ _ hint hrange'
  exact ⟨hS, htrace.trans (hilbertTrace_realPWLevel_average_compression hY hL ha hab hφ)⟩

end Transport

/-! ### The trace on the level of the project -/

local notation "level₀(" ω ", " Y ")" =>
  sLocalInvariantPWSobolev (F := ℚ) (S := ∅) (s := 0) le_rfl (a := 1 / 2) (by norm_num) ω Y

/-- The invariant level of the project over `ℚ` with no finite place is closed. -/
theorem isClosed_ratEmptyLevel (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker) (Y : ℝ) :
    IsClosed ((level₀(ω, Y) : Submodule ℂ W₀) : Set W₀) := by
  rw [sLocalInvariantPWSobolev]
  exact Submodule.isClosed_topologicalClosure _

/-- The invariant level of the project over `ℚ` with no finite place is complete. -/
instance instCompleteSpaceRatEmptyLevel (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker)
    (Y : ℝ) : CompleteSpace (level₀(ω, Y)) :=
  (isClosed_ratEmptyLevel ω Y).completeSpace_coe

/-- Paper: Theorem 12.4.1.1, pp. 514–519, with Definition 11.2.1.3(1), p. 488. **The trace of
the compression on the level of the project.** Over `ℚ` with no finite place, at order zero and
twist `1/2`, let `P` be the orthogonal projection onto `sLocalInvariantPWSobolev` with parameter
`Y` in the weighted space of the project, `χ_L` the cutoff to the classes of norm at most `L`,
and `A` the action of the test, `A F = ∫ t in a..b, (φ t / t) • F ((σ t)⁻¹ ·)` with `σ t` the
class of norm `t`. Then `P ∘ χ_L ∘ A ∘ P` is nuclear, and its Hilbert trace is the average
against `φ(g) dg / g` of the closed form `realPWLevelCompressionTrace Y L g`.
Reconstruction: the paper does not specify the cutoffs. This is the sharp cutoff to norm at
most `L`, with no lower cutoff, and the action is written in the norm coordinate, in which the
quotient measure is a constant multiple of `dt / t`. -/
theorem ratEmpty_hilbertTrace_average_compression
    (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker) {Y L a b : ℝ} {φ : ℝ → ℝ} (hY : 0 < Y)
    (hL : 0 ≤ L) (ha : 0 < a) (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b)) (σ : ℝ → J₀)
    (hσ : ∀ t : ℝ, 0 < t → normℝ(σ t) = t) :
    ∃ A : W₀ →L[ℂ] W₀,
      (∀ F : W₀, A F = ∫ t in a..b, ((φ t / t : ℝ) : ℂ) • ratEmptyTranslation (σ t) F) ∧
      ∃ hn : IsNuclearOperator ((level₀(ω, Y)).starProjection ∘L ratEmptyCutoff L ∘L A ∘L
          (level₀(ω, Y)).starProjection),
        hilbertTrace ⟨(level₀(ω, Y)).starProjection ∘L ratEmptyCutoff L ∘L A ∘L
          (level₀(ω, Y)).starProjection, hn⟩ =
          ∫ g in a..b, (φ g : ℂ) * realPWLevelCompressionTrace Y L g / (g : ℂ) := by
  have hbridge := exists_linearIsometry_map_sLocalInvariantPWSobolev_rat ω hY
  obtain ⟨U, κ, c, -, hκ, hU, hq, hmap⟩ := hbridge
  have hτ : ∀ t ∈ Icc a b, ∀ F : W₀,
      U (ratEmptyTranslation (σ t) F) = realDilation t (U F) := by
    intro t ht F
    have h := ratEmpty_translation_intertwine hκ hU hq (σ t) F
    have hn : normℝ(σ t) = t := hσ t (ha.trans_le ht.1)
    exact h.trans (congrArg (fun r ↦ realDilation r (U F)) hn)
  have hex := exists_average_of_isometry_intertwining (a := a) (b := b) (φ := φ) U
    (fun t ↦ ratEmptyTranslation (σ t)) ha hab hφ hτ
  obtain ⟨A, hAformula, hAU⟩ := hex
  have hP : ∀ v : W₀, U ((level₀(ω, Y)).starProjection v) =
      (realPWLevel Y).starProjection (U v) :=
    fun v ↦ LinearIsometry.map_starProjection' U _ _ hmap v
  have hC : ∀ F : W₀, U (ratEmptyCutoff L F) = realCutoff L (U F) :=
    ratEmpty_cutoff_intertwine hκ hU hq L
  have hrange : ∀ v ∈ realPWLevel Y, ∃ w : W₀, U w = v := by
    intro v hv
    rw [← hmap] at hv
    obtain ⟨w, -, hw⟩ := hv
    exact ⟨w, hw⟩
  have hfinal := hilbertTrace_average_compression_of_isometry (Y := Y) (L := L) U
    ((level₀(ω, Y)).starProjection) (ratEmptyCutoff L) A hY hL ha hab hφ hP hC hAU hrange
  exact ⟨A, hAformula, hfinal⟩

section Limit

variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {Ys Ls : ι → ℝ}

/-- Paper: Theorem 12.4.1.1, pp. 514–519, as used on p. 520. **The limit of the traces on the
level of the project.** Over `ℚ` with no finite place, at order zero and twist `1/2`, with `P_Y`
the projection onto `sLocalInvariantPWSobolev` with parameter `Y`, `χ_L` the cutoff to norm at
most `L` and `A` the action of a test `φ` that is continuous on an interval `[a, b]` of `(0, ∞)`
not containing `1`: the Hilbert traces of `P_Y ∘ χ_L ∘ A ∘ P_Y` tend, as `Y * L → ∞`, to the
real-place term of (12.5.1.1) minus `∫ φ(g) min(g^(1/2), g^(-1/2)) d×g`.
Reconstruction: as for `ratEmpty_hilbertTrace_average_compression`. The paper asserts the limit
without the second integral. -/
theorem ratEmpty_tendsto_hilbertTrace_average_compression
    (ω : PontryaginDual (sIdeleQuotientNorm ℚ ∅).ker) {a b : ℝ} {φ : ℝ → ℝ} (ha : 0 < a)
    (hab : a ≤ b) (h1 : 1 ∉ Icc a b) (hφ : ContinuousOn φ (Icc a b)) (σ : ℝ → J₀)
    (hσ : ∀ t : ℝ, 0 < t → normℝ(σ t) = t) (hY : ∀ i, 0 < Ys i) (hL : ∀ i, 0 ≤ Ls i)
    (hYL : Tendsto (fun i ↦ Ys i * Ls i) l atTop) :
    ∃ A : W₀ →L[ℂ] W₀,
      (∀ F : W₀, A F = ∫ t in a..b, ((φ t / t : ℝ) : ℂ) • ratEmptyTranslation (σ t) F) ∧
      ∃ tr : ι → ℂ,
        (∀ i, ∃ hn : IsNuclearOperator ((level₀(ω, Ys i)).starProjection ∘L
            ratEmptyCutoff (Ls i) ∘L A ∘L (level₀(ω, Ys i)).starProjection),
          hilbertTrace ⟨(level₀(ω, Ys i)).starProjection ∘L ratEmptyCutoff (Ls i) ∘L A ∘L
            (level₀(ω, Ys i)).starProjection, hn⟩ = tr i) ∧
        Tendsto tr l
          (𝓝 (((∫ g in a..b, φ g * (1 / 2 * (√g / |1 - g| + √g / |1 + g|)) / g) -
            ∫ g in a..b, φ g * min (√g) (√g)⁻¹ / g : ℝ) : ℂ)) := by
  have h0 := ratEmpty_hilbertTrace_average_compression ω (Y := 1) (L := 0) one_pos le_rfl ha hab
    hφ σ hσ
  obtain ⟨A, hA, -⟩ := h0
  refine ⟨A, hA, fun i ↦ ∫ g in a..b,
    (φ g : ℂ) * realPWLevelCompressionTrace (Ys i) (Ls i) g / (g : ℂ), fun i ↦ ?_,
    tendsto_integral_realPWLevelCompressionTrace ha hab h1 hφ hY hL hYL⟩
  have hi := ratEmpty_hilbertTrace_average_compression ω (hY i) (hL i) ha hab hφ σ hσ
  obtain ⟨A', hA', hn, htr⟩ := hi
  have hAA : A' = A := ContinuousLinearMap.ext fun F ↦ (hA' F).trans (hA F).symm
  subst hAA
  exact ⟨hn, htr⟩

end Limit

end RiemannMasullo
