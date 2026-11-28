module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_CornerRiesz_Isolated
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import RiemannMasullo.AppD_SchwartzBruhat.Sec1c

/-!
# Corner orbit profiles, directional smoothness, and Riesz Fourier factorization

This module develops the adelic corner orbit profile `cornerOrbitProfile w ω φ u x`:
1. Smooth iterated differentiation `normFlowIterDeriv` along the negated norm-section flow
   and `C^∞` regularity (`cornerOrbitProfile_contDiff`).
2. Local-`L²` Tonelli energy `localL2Energy`, `memLp_localL2Energy`, and the Cauchy–Schwarz
   envelope `cornerOrbitProfile_bound_and_integrable`.
3. The 1D Fourier factorization `weightedRieszJet_convolution_inner_eq_fourier`.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.Isolated

section CornerFactorization

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "logNorm" => logIdeleClassNorm F

/-- Negated canonical norm flow `x ↦ canonicalNormFlow F (ofAdd (-x))`. -/
def canonicalNormFlowNeg (F : Type*) [Field F] [NumberField F] :
    LCATopologicalLie (IdeleClassGroup (𝓞 F) F) where
  toFun m := (canonicalNormFlow F m)⁻¹
  map_one' := by simp
  map_mul' x y := by rw [map_mul, mul_inv]
  continuous_toFun := continuous_inv.comp (canonicalNormFlow F).continuous

lemma canonicalNormFlowNeg_coe (x : ℝ) :
    canonicalNormFlowNeg F (Multiplicative.ofAdd x) =
      canonicalNormFlow F (Multiplicative.ofAdd (-x)) := by
  change (canonicalNormFlow F (Multiplicative.ofAdd x))⁻¹ = _
  rw [← map_inv]
  rfl

/-- Directional derivative of a `BruhatCompactSupport C𝔽` test along `canonicalNormFlowNeg F`. -/
def normFlowDeriv (φ : BruhatCompactSupport C𝔽) : BruhatCompactSupport C𝔽 :=
  ⟨bruhatDirectionalDeriv (canonicalNormFlowNeg F) φ.val,
    bruhatDirectionalDeriv_mem_smooth (canonicalNormFlowNeg F) ⟨φ.val, φ.property.1⟩, by
    refine HasCompactSupport.of_support_subset_isCompact φ.property.2 fun x ↦ ?_
    contrapose
    intro hx
    have hγ : Tendsto (fun t : ℝ ↦ x * canonicalNormFlowNeg F (Multiplicative.ofAdd t)) (𝓝 0) (𝓝 x) := by
      have hc : Continuous (fun t : ℝ ↦ x * canonicalNormFlowNeg F (Multiplicative.ofAdd t)) :=
        continuous_const.mul ((canonicalNormFlowNeg F).continuous.comp continuous_ofAdd)
      simpa using hc.tendsto 0
    have hz := (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto hγ
    rw [notMem_support]
    simpa [bruhatDirectionalDeriv, comp_def] using hz.deriv_eq⟩

lemma tsupport_normFlowDeriv_subset (φ : BruhatCompactSupport C𝔽) :
    tsupport (normFlowDeriv φ).val ⊆ tsupport φ.val := by
  refine closure_minimal ?_ (isClosed_tsupport _)
  intro x hx
  by_contra hnot
  have hγ : Tendsto (fun t : ℝ ↦ x * canonicalNormFlowNeg F (Multiplicative.ofAdd t)) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ ↦ x * canonicalNormFlowNeg F (Multiplicative.ofAdd t)) :=
      continuous_const.mul ((canonicalNormFlowNeg F).continuous.comp continuous_ofAdd)
    simpa using hc.tendsto 0
  have hz := (notMem_tsupport_iff_eventuallyEq.mp hnot).comp_tendsto hγ
  rw [mem_support] at hx
  exact hx (by simpa [normFlowDeriv, bruhatDirectionalDeriv, comp_def] using hz.deriv_eq)

def normFlowIterDeriv (j : ℕ) (φ : BruhatCompactSupport C𝔽) : BruhatCompactSupport C𝔽 :=
  (normFlowDeriv (F := F))^[j] φ

lemma tsupport_normFlowIterDeriv_subset (j : ℕ) (φ : BruhatCompactSupport C𝔽) :
    tsupport (normFlowIterDeriv j φ).val ⊆ tsupport φ.val := by
  induction j with
  | zero => exact Subset.rfl
  | succ k ih =>
    rw [normFlowIterDeriv, Function.iterate_succ_apply']
    exact (tsupport_normFlowDeriv_subset _).trans ih

lemma hasDerivAt_normFlowIterDeriv (j : ℕ) (φ : BruhatCompactSupport C𝔽) (y : C𝔽) (x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (normFlowIterDeriv j φ).val (y * canonicalNormFlow F (Multiplicative.ofAdd (-t))))
      ((normFlowIterDeriv (j + 1) φ).val (y * canonicalNormFlow F (Multiplicative.ofAdd (-x)))) x := by
  let ψ := normFlowIterDeriv j φ
  have h1 : IsBruhatContDiff 1 ψ.val := (mem_bruhatSmoothSubmodule_iff _).mp ψ.property.1 1
  let yx := y * canonicalNormFlowNeg F (Multiplicative.ofAdd x)
  have hd0 := hasDerivAt_bruhatDirectionalDeriv (canonicalNormFlowNeg F) h1 yx
  let g : ℝ → ℝ := fun t ↦ t - x
  have hshift : HasDerivAt g 1 x := (hasDerivAt_id x).sub_const x
  let f₀ : ℝ → ℂ := fun t ↦ ψ.val (yx * canonicalNormFlowNeg F (Multiplicative.ofAdd t))
  have hhd : HasDerivAt f₀ (bruhatDirectionalDeriv (canonicalNormFlowNeg F) ψ.val yx) (g x) := by
    change HasDerivAt f₀ (bruhatDirectionalDeriv (canonicalNormFlowNeg F) ψ.val yx) (x - x)
    rw [sub_self]; exact hd0
  have hcomp : HasDerivAt (fun t : ℝ ↦ f₀ (t - x))
      ((1 : ℝ) • bruhatDirectionalDeriv (canonicalNormFlowNeg F) ψ.val yx) x :=
    hhd.scomp x hshift
  rw [one_smul] at hcomp
  have hcomp' : HasDerivAt (fun t : ℝ ↦ f₀ (t - x))
      ((normFlowIterDeriv (j + 1) φ).val (y * canonicalNormFlow F (Multiplicative.ofAdd (-x)))) x := by
    convert hcomp using 1
    rw [normFlowIterDeriv, Function.iterate_succ_apply']
    change bruhatDirectionalDeriv (canonicalNormFlowNeg F) ψ.val
        (y * canonicalNormFlow F (Multiplicative.ofAdd (-x))) =
      bruhatDirectionalDeriv (canonicalNormFlowNeg F) ψ.val yx
    congr 1
    exact (congrArg (y * ·) (canonicalNormFlowNeg_coe x)).symm
  refine hcomp'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
  dsimp only [f₀]
  have hmul : yx * canonicalNormFlowNeg F (Multiplicative.ofAdd (t - x)) =
      y * canonicalNormFlowNeg F (Multiplicative.ofAdd t) := by
    change (y * canonicalNormFlowNeg F (Multiplicative.ofAdd x)) *
      canonicalNormFlowNeg F (Multiplicative.ofAdd (t - x)) = _
    rw [mul_assoc, ← map_mul, ← ofAdd_add]
    congr 2; ring
  change ψ.val (y * canonicalNormFlow F (Multiplicative.ofAdd (-t))) =
    ψ.val (yx * canonicalNormFlowNeg F (Multiplicative.ofAdd (t - x)))
  rw [hmul, canonicalNormFlowNeg_coe]

/-- The `(ideleClassNorm F).ker`-averaged overlap kernel `G(x)` for `w`, `ω`, `φ`, `u`. -/
def cornerOrbitProfile (w : ℝ → ℝ) (ω : PontryaginDual (ideleClassNorm F).ker) (φ : BruhatCompactSupport C𝔽)
    (u : Lp ℂ 2 (weightedSobolevMeasure F w)) (x : ℝ) : ℂ :=
  ∫ p : (ideleClassNorm F).ker × C𝔽,
    star (φ.val (p.2 * (p.1 : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x)))) *
      (ω p.1 : ℂ) * u p.2 * (w (logNorm p.2) : ℂ) ∂((normOneProbHaar F).prod μ𝔽)

lemma exists_logNorm_bound_tsupport (φ : BruhatCompactSupport C𝔽) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y ∈ tsupport φ.val, |logNorm y| ≤ R := by
  by_cases hne : (tsupport φ.val).Nonempty
  · obtain ⟨y₀, hy₀, hmax⟩ := φ.property.2.exists_isMaxOn hne continuous_logNorm.abs.continuousOn
    refine ⟨|logNorm y₀|, abs_nonneg _, fun y hy ↦ hmax hy⟩
  · exact ⟨0, le_rfl, fun y hy ↦ absurd ⟨y, hy⟩ hne⟩

/-- Local `L²` energy profile `h(x) = (∫_{|logNorm g - x| ≤ R} |u g|² w(logNorm g) dμ𝔽)^{1/2}`. -/
def localL2Energy (w : ℝ → ℝ) (u : Lp ℂ 2 (weightedSobolevMeasure F w)) (R x : ℝ) : ℝ :=
  Real.sqrt (∫ g : C𝔽, {g : C𝔽 | |logNorm g - x| ≤ R}.indicator
    (fun g ↦ ‖u g‖ ^ 2 * w (logNorm g)) g ∂μ𝔽)

lemma integrable_sq_mul_weight {w : ℝ → ℝ} (hw_cont : Continuous w) (hw_pos : ∀ x, 0 < w x)
    (u : Lp ℂ 2 (weightedSobolevMeasure F w)) :
    Integrable (fun g : C𝔽 ↦ ‖u g‖ ^ 2 * w (logNorm g)) μ𝔽 := by
  have hlu : MemLp (u : C𝔽 → ℂ) 2 (weightedSobolevMeasure F w) := Lp.memLp u
  have hu := hlu.norm.integrable_sq
  have hwd : Measurable (fun g : C𝔽 ↦ ENNReal.ofReal (w (logNorm g))) :=
    (hw_cont.measurable.comp measurable_logNorm).ennreal_ofReal
  have h1 := (integrable_withDensity_iff_integrable_smul' hwd
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mp hu
  refine h1.congr (ae_of_all _ fun g ↦ ?_)
  dsimp only
  rw [ENNReal.toReal_ofReal (hw_pos _).le, smul_eq_mul, mul_comm]

lemma memLp_localL2Energy {w : ℝ → ℝ} (hw_cont : Continuous w) (hw_pos : ∀ x, 0 < w x)
    (u : Lp ℂ 2 (weightedSobolevMeasure F w)) {R : ℝ} (hR : 0 ≤ R) :
    MemLp (localL2Energy w u R) 2 volume := by
  have hint := integrable_sq_mul_weight hw_cont hw_pos u
  have hnonneg : ∀ g : C𝔽, 0 ≤ ‖u g‖ ^ 2 * w (logNorm g) := fun g ↦
    mul_nonneg (sq_nonneg _) (hw_pos _).le
  let ker : ℝ × C𝔽 → ℝ := fun q ↦ {g : C𝔽 | |logNorm g - q.1| ≤ R}.indicator
    (fun g ↦ ‖u g‖ ^ 2 * w (logNorm g)) q.2
  have hmeas_set : MeasurableSet {q : ℝ × C𝔽 | |logNorm q.2 - q.1| ≤ R} :=
    measurableSet_le (continuous_abs.measurable.comp ((measurable_logNorm.comp measurable_snd).sub measurable_fst))
      measurable_const
  have hker_eq : ker = ({q : ℝ × C𝔽 | |logNorm q.2 - q.1| ≤ R}).indicator
      (fun q ↦ ‖u q.2‖ ^ 2 * w (logNorm q.2)) := by
    funext ⟨x, g⟩
    by_cases h : |logNorm g - x| ≤ R <;> simp [ker, h]
  have hker_aestr : AEStronglyMeasurable ker (volume.prod μ𝔽) := by
    rw [hker_eq]
    exact (hint.1.comp_snd).indicator hmeas_set
  have hker_prod : Integrable ker (volume.prod μ𝔽) := by
    have hmeas_int : Integrable (fun q : C𝔽 × ℝ ↦ ker (q.2, q.1)) (Measure.prod μ𝔽 volume) := by
      refine (integrable_prod_iff (μ := μ𝔽) (ν := volume) ?_).mpr ⟨?_, ?_⟩
      · exact hker_aestr.comp_quasiMeasurePreserving
          (Measure.measurePreserving_swap (μ := μ𝔽) (ν := volume)).quasiMeasurePreserving
      · refine ae_of_all _ fun g ↦ ?_
        have hs : {x : ℝ | |logNorm g - x| ≤ R} = Icc (logNorm g - R) (logNorm g + R) := by
          ext x; simp only [mem_ofPred_eq, mem_Icc, abs_sub_comm, abs_le]
          constructor <;> intro ⟨a, b⟩ <;> exact ⟨by linarith, by linarith⟩
        have hfun : (fun x : ℝ ↦ ker (x, g)) = (Icc (logNorm g - R) (logNorm g + R)).indicator
            (fun _ ↦ ‖u g‖ ^ 2 * w (logNorm g)) := by
          funext x
          by_cases hx : x ∈ Icc (logNorm g - R) (logNorm g + R)
          · have hx' : |logNorm g - x| ≤ R := by rw [← hs] at hx; exact hx
            simp [ker, hx, hx']
          · have hx' : ¬ |logNorm g - x| ≤ R := by rw [← hs] at hx; exact hx
            simp [ker, hx, hx']
        rw [hfun]
        exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
      · have hnorm_eq : (fun g : C𝔽 ↦ ∫ x : ℝ, ‖ker (x, g)‖ ∂volume) =
            fun g : C𝔽 ↦ (2 * R) * (‖u g‖ ^ 2 * w (logNorm g)) := by
          funext g
          have hs : {x : ℝ | |logNorm g - x| ≤ R} = Icc (logNorm g - R) (logNorm g + R) := by
            ext x; simp only [mem_ofPred_eq, mem_Icc, abs_sub_comm, abs_le]
            constructor <;> intro ⟨a, b⟩ <;> exact ⟨by linarith, by linarith⟩
          have hfun : (fun x : ℝ ↦ ‖ker (x, g)‖) = (Icc (logNorm g - R) (logNorm g + R)).indicator
              (fun _ ↦ ‖u g‖ ^ 2 * w (logNorm g)) := by
            funext x
            by_cases hx : x ∈ Icc (logNorm g - R) (logNorm g + R)
            · have hx' : |logNorm g - x| ≤ R := by rw [← hs] at hx; exact hx
              simp [ker, hx, hx', Real.norm_of_nonneg (hnonneg g)]
            · have hx' : ¬ |logNorm g - x| ≤ R := by rw [← hs] at hx; exact hx
              simp [ker, hx, hx']
          rw [hfun, integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
            Real.volume_real_Icc_of_le (by linarith)]
          ring
        rw [hnorm_eq]
        exact hint.const_mul (2 * R)
    exact (Measure.measurePreserving_swap (μ := volume) (ν := μ𝔽)).integrable_comp_of_integrable
      hmeas_int
  have hslice := hker_prod.integral_prod_left
  refine (memLp_two_iff_integrable_sq_norm ?_).mpr ?_
  · exact Real.continuous_sqrt.comp_aestronglyMeasurable hslice.aestronglyMeasurable
  · refine hslice.congr (ae_of_all _ fun x ↦ ?_)
    have hnonneg_x : 0 ≤ ∫ g : C𝔽, ker (x, g) ∂μ𝔽 :=
      integral_nonneg fun g ↦ indicator_nonneg (fun g _ ↦ hnonneg g) g
    dsimp only [localL2Energy]
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hnonneg_x]

lemma indicator_slab_integrable_and_norm {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    Integrable (fun g : C𝔽 ↦ {g : C𝔽 | |logNorm g - x| ≤ R}.indicator (fun _ ↦ (1 : ℝ)) g) μ𝔽 ∧
      ∫ g : C𝔽, {g : C𝔽 | |logNorm g - x| ≤ R}.indicator (fun _ ↦ (1 : ℝ)) g ∂μ𝔽 =
        tamagawaNormFactor F * (2 * R) := by
  let f : C𝔽 → ℝ := {g : C𝔽 | |logNorm g - x| ≤ R}.indicator (fun _ ↦ (1 : ℝ))
  have hf_eq : (fun p : ℝ × (ideleClassNorm F).ker ↦ f (splitCoordEquiv F p)) =
      fun p : ℝ × (ideleClassNorm F).ker ↦ (Icc (x - R) (x + R)).indicator (fun _ ↦ (1 : ℝ)) p.1 * (1 : ℝ) := by
    funext p
    have hk : ideleClassNorm F (p.2 : C𝔽) = 1 := p.2.property
    have hL : logNorm (splitCoordEquiv F p) = p.1 := by
      change Real.log ((ideleClassNorm F ((p.2 : C𝔽) * canonicalNormFlow F (Multiplicative.ofAdd p.1))).val : ℝ) = p.1
      rw [map_mul, hk, one_mul, ideleClassNorm_canonicalNormFlow]
      exact Real.log_exp p.1
    by_cases hp : p.1 ∈ Icc (x - R) (x + R)
    · have hp' : |logNorm (splitCoordEquiv F p) - x| ≤ R := by
        rw [hL, abs_le]; exact ⟨by linarith [hp.1], by linarith [hp.2]⟩
      simp [f, hp, hp']
    · have hp' : ¬ |logNorm (splitCoordEquiv F p) - x| ≤ R := by
        rw [hL, abs_le]; exact fun ⟨h1, h2⟩ ↦ hp ⟨by linarith, by linarith⟩
      simp [f, hp, hp']
  have : IsFiniteMeasure (normOneProbHaar F) := normOneProbHaar_isFinite
  have hi_prod : Integrable (fun p : ℝ × (ideleClassNorm F).ker ↦ f (splitCoordEquiv F p))
      (volume.prod (normOneProbHaar F)) := by
    rw [hf_eq]
    exact ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc).mul_prod
      (integrable_const (1 : ℝ))
  refine ⟨(integrable_tamagawa_iff_splitCoord f).mpr hi_prod, ?_⟩
  rw [integral_tamagawa_eq_splitCoord, hf_eq, smul_eq_mul,
    show (fun p : ℝ × (ideleClassNorm F).ker ↦ (Icc (x - R) (x + R)).indicator (fun _ ↦ (1 : ℝ)) p.1 * (1 : ℝ)) =
      fun p ↦ (Icc (x - R) (x + R)).indicator (fun _ ↦ (1 : ℝ)) p.1 * (fun _ : (ideleClassNorm F).ker ↦ (1 : ℝ)) p.2 from rfl,
    integral_prod_mul (f := (Icc (x - R) (x + R)).indicator (fun _ ↦ (1 : ℝ)))
      (g := fun _ : (ideleClassNorm F).ker ↦ (1 : ℝ)),
    integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
    Real.volume_real_Icc_of_le (by linarith),
    show ∫ _k : (ideleClassNorm F).ker, (1 : ℝ) ∂(normOneProbHaar F) = 1 by
      rw [integral_const, smul_eq_mul, mul_one, Measure.real_def, normOneProbHaar_univ, ENNReal.toReal_one]]
  ring

private lemma real_l2_norm_eq_sqrt_integral_sq {μ : Measure ℝ} (f : Lp ℝ 2 μ) :
    ‖f‖ = Real.sqrt (∫ x : ℝ, (f x) ^ 2 ∂μ) := by
  have hsq : ‖f‖ ^ 2 = ∫ x : ℝ, (f x) ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp [sq]
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

private lemma l2_real_norm_eq_sqrt_integral_sq {μ : Measure C𝔽} (f : Lp ℝ 2 μ) :
    ‖f‖ = Real.sqrt (∫ g : C𝔽, (f g) ^ 2 ∂μ) := by
  have hsq : ‖f‖ ^ 2 = ∫ g : C𝔽, (f g) ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
    refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
    simp [sq]
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

lemma cornerOrbitProfile_bound_and_integrable {w : ℝ → ℝ} (hw_cont : Continuous w) (hw_pos : ∀ x, 0 < w x)
    (u : Lp ℂ 2 (weightedSobolevMeasure F w)) (ω : PontryaginDual (ideleClassNorm F).ker)
    (φ : BruhatCompactSupport C𝔽) {R : ℝ} (hR : 0 ≤ R) (hsupp : ∀ y ∈ tsupport φ.val, |logNorm y| ≤ R)
    {CR : ℝ} (hCR : 0 < CR) (hshift : ∀ x y : ℝ, |x - y| ≤ R → w x ≤ CR * w y)
    (x : ℝ) :
    Integrable (fun p : (ideleClassNorm F).ker × C𝔽 ↦
      star (φ.val (p.2 * (p.1 : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x)))) *
        (ω p.1 : ℂ) * u p.2 * (w (logNorm p.2) : ℂ)) ((normOneProbHaar F).prod μ𝔽) ∧
    ‖cornerOrbitProfile w ω φ u x‖ ≤
      (⨆ y : C𝔽, ‖φ.val y‖) * Real.sqrt (CR * tamagawaNormFactor F * (2 * R)) *
        Real.sqrt (w x) * localL2Energy w u R x := by
  have habs := tamagawa_absCont_weightedSobolevMeasure (F := F) hw_cont hw_pos
  have : IsFiniteMeasure (normOneProbHaar F) := normOneProbHaar_isFinite
  have hφ_cont : Continuous φ.val := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  obtain ⟨M_raw, hM_raw⟩ := φ.property.2.exists_bound_of_continuousOn hφ_cont.continuousOn
  let Mφ : ℝ := ⨆ y : C𝔽, ‖φ.val y‖
  have hMφ_nonneg : 0 ≤ Mφ := Real.iSup_nonneg fun _ ↦ norm_nonneg _
  have hbdd : BddAbove (Set.range fun y : C𝔽 ↦ ‖φ.val y‖) := by
    refine ⟨max M_raw 0, ?_⟩
    rintro _ ⟨y, rfl⟩
    by_cases hy : φ.val y = 0
    · simp [hy]
    · exact (hM_raw y (subset_tsupport _ hy)).trans (le_max_left _ _)
  have hnorm_le : ∀ y : C𝔽, ‖φ.val y‖ ≤ Mφ := fun y ↦ le_ciSup hbdd y
  have hlog_shift (k : (ideleClassNorm F).ker) (g : C𝔽) :
      logNorm (g * (k : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x))) = logNorm g - x := by
    have hk : ideleClassNorm F (k : C𝔽) = 1 := k.property
    change Real.log ((ideleClassNorm F (g * (k : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x)))).val : ℝ) =
      logNorm g - x
    rw [map_mul, map_mul, map_inv, hk, inv_one, mul_one, ideleClassNorm_canonicalNormFlow,
      Units.val_mul, NNReal.coe_mul, Real.log_mul (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
      (NNReal.coe_pos.mpr (Units.zero_lt _)).ne']
    change logNorm g + Real.log (Real.exp (-x)) = logNorm g - x
    rw [Real.log_exp, sub_eq_add_neg]
  let Sx : Set C𝔽 := {g : C𝔽 | |logNorm g - x| ≤ R}
  have hSx_m : MeasurableSet Sx :=
    measurableSet_le (continuous_abs.measurable.comp (measurable_logNorm.sub measurable_const)) measurable_const
  have hslab := indicator_slab_integrable_and_norm (F := F) hR x
  have h1_mem : MemLp (fun g : C𝔽 ↦ Sx.indicator (fun _ ↦ (1 : ℝ)) g) 2 μ𝔽 := by
    refine (memLp_two_iff_integrable_sq_norm hslab.1.1).mpr ?_
    refine hslab.1.congr (ae_of_all _ fun g ↦ ?_)
    by_cases hg : g ∈ Sx
    · simp [Sx, hg]
    · simp [Sx, hg]
  have h2_mem : MemLp (fun g : C𝔽 ↦ Sx.indicator (fun g ↦ ‖u g‖ * Real.sqrt (w (logNorm g))) g) 2 μ𝔽 := by
    refine (memLp_two_iff_integrable_sq_norm ?_).mpr ?_
    · exact (((Lp.aestronglyMeasurable u).mono_ac habs).norm.mul
        (Real.continuous_sqrt.measurable.comp
          (hw_cont.measurable.comp measurable_logNorm)).aestronglyMeasurable).indicator hSx_m
    refine ((integrable_sq_mul_weight hw_cont hw_pos u).indicator hSx_m).congr (ae_of_all _ fun g ↦ ?_)
    by_cases hg : g ∈ Sx
    · simp only [hg, indicator_of_mem, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (hw_pos _).le]
    · simp [hg]
  have huw_int : Integrable (fun g : C𝔽 ↦ Sx.indicator (fun g ↦ ‖u g‖ * Real.sqrt (w (logNorm g))) g) μ𝔽 := by
    refine (MemLp.integrable_mul h2_mem h1_mem).congr (ae_of_all _ fun g ↦ ?_)
    by_cases hg : g ∈ Sx <;> simp [hg]
  have hpoint_le : ∀ p : (ideleClassNorm F).ker × C𝔽,
      ‖star (φ.val (p.2 * (p.1 : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x)))) *
          (ω p.1 : ℂ) * u p.2 * (w (logNorm p.2) : ℂ)‖ ≤
        (Mφ * Real.sqrt (CR * w x)) * Sx.indicator (fun g ↦ ‖u g‖ * Real.sqrt (w (logNorm g))) p.2 := by
    intro ⟨k, g⟩
    rw [norm_mul, norm_mul, norm_mul, norm_star, Circle.norm_coe, mul_one,
      Complex.norm_real, Real.norm_of_nonneg (hw_pos _).le]
    by_cases hzero : φ.val (g * (k : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x))) = 0
    · simp only [hzero, norm_zero, zero_mul]
      exact mul_nonneg (mul_nonneg hMφ_nonneg (Real.sqrt_nonneg _))
        (indicator_nonneg (fun _ _ ↦ mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) g)
    · have hmem_supp : g * (k : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x)) ∈ tsupport φ.val :=
        subset_tsupport _ hzero
      have hgSx : g ∈ Sx := by
        change |logNorm g - x| ≤ R
        rw [← hlog_shift k g]
        exact hsupp _ hmem_supp
      simp only [hgSx, indicator_of_mem]
      have hw_le : w (logNorm g) ≤ CR * w x := hshift (logNorm g) x hgSx
      have hsq : w (logNorm g) = Real.sqrt (w (logNorm g)) * Real.sqrt (w (logNorm g)) :=
        (Real.mul_self_sqrt (hw_pos _).le).symm
      have hsq_le : Real.sqrt (w (logNorm g)) ≤ Real.sqrt (CR * w x) := Real.sqrt_le_sqrt hw_le
      calc ‖φ.val (g * (k : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x)))‖ * ‖u g‖ * w (logNorm g)
          ≤ Mφ * ‖u g‖ * (Real.sqrt (w (logNorm g)) * Real.sqrt (CR * w x)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right (hnorm_le _) (norm_nonneg _)) ?_
              (hw_pos _).le (mul_nonneg hMφ_nonneg (norm_nonneg _))
            conv_lhs => rw [hsq]
            exact mul_le_mul_of_nonneg_left hsq_le (Real.sqrt_nonneg (w (logNorm g)))
        _ = (Mφ * Real.sqrt (CR * w x)) * (‖u g‖ * Real.sqrt (w (logNorm g))) := by ring
  have hmeas_int : AEStronglyMeasurable (fun p : (ideleClassNorm F).ker × C𝔽 ↦
      star (φ.val (p.2 * (p.1 : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x)))) *
        (ω p.1 : ℂ) * u p.2 * (w (logNorm p.2) : ℂ)) ((normOneProbHaar F).prod μ𝔽) := by
    have hm1 : Continuous (fun p : (ideleClassNorm F).ker × C𝔽 ↦
        star (φ.val (p.2 * (p.1 : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x))))) :=
      continuous_star.comp (hφ_cont.comp ((continuous_snd.mul (continuous_subtype_val.comp continuous_fst).inv).mul
        continuous_const))
    have hm2 : Continuous (fun p : (ideleClassNorm F).ker × C𝔽 ↦ (ω p.1 : ℂ)) :=
      (continuous_subtype_val.comp ω.continuous).comp continuous_fst
    have hm3 : AEStronglyMeasurable (fun p : (ideleClassNorm F).ker × C𝔽 ↦ u p.2)
        ((normOneProbHaar F).prod μ𝔽) :=
      ((Lp.aestronglyMeasurable u).mono_ac habs).comp_snd
    have hm4 : Continuous (fun p : (ideleClassNorm F).ker × C𝔽 ↦ (w (logNorm p.2) : ℂ)) :=
      Complex.continuous_ofReal.comp ((hw_cont.comp continuous_logNorm).comp continuous_snd)
    exact ((hm1.aestronglyMeasurable.mul hm2.aestronglyMeasurable).mul hm3).mul hm4.aestronglyMeasurable
  have hint_dom : Integrable (fun p : (ideleClassNorm F).ker × C𝔽 ↦
      (Mφ * Real.sqrt (CR * w x)) * Sx.indicator (fun g ↦ ‖u g‖ * Real.sqrt (w (logNorm g))) p.2)
      ((normOneProbHaar F).prod μ𝔽) :=
    ((integrable_const (1 : ℝ)).mul_prod (huw_int.const_mul (Mφ * Real.sqrt (CR * w x)))).congr
      (ae_of_all _ fun p ↦ by simp)
  have hint : Integrable (fun p : (ideleClassNorm F).ker × C𝔽 ↦
      star (φ.val (p.2 * (p.1 : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x)))) *
        (ω p.1 : ℂ) * u p.2 * (w (logNorm p.2) : ℂ)) ((normOneProbHaar F).prod μ𝔽) :=
    hint_dom.mono' hmeas_int (ae_of_all _ hpoint_le)
  refine ⟨hint, ?_⟩
  have hcs : ∫ g : C𝔽, Sx.indicator (fun g ↦ ‖u g‖ * Real.sqrt (w (logNorm g))) g ∂μ𝔽 ≤
      localL2Energy w u R x * Real.sqrt (tamagawaNormFactor F * (2 * R)) := by
    let f2 : Lp ℝ 2 μ𝔽 := h2_mem.toLp _
    let f1 : Lp ℝ 2 μ𝔽 := h1_mem.toLp _
    have hleft_eq : (∫ g : C𝔽, Sx.indicator (fun g ↦ ‖u g‖ * Real.sqrt (w (logNorm g))) g ∂μ𝔽) =
        @inner ℝ (Lp ℝ 2 μ𝔽) _ f2 f1 := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [h2_mem.coeFn_toLp, h1_mem.coeFn_toLp] with g hg2 hg1
      change Sx.indicator (fun g ↦ ‖u g‖ * Real.sqrt (w (logNorm g))) g = @inner ℝ ℝ _ (f2 g) (f1 g)
      rw [hg2, hg1, RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm]
      by_cases hg : g ∈ Sx <;> simp [hg]
    have hle : ∫ g : C𝔽, Sx.indicator (fun g ↦ ‖u g‖ * Real.sqrt (w (logNorm g))) g ∂μ𝔽 ≤
        ‖f2‖ * ‖f1‖ := by
      rw [hleft_eq]
      exact real_inner_le_norm f2 f1
    have h2_norm : ‖f2‖ = localL2Energy w u R x := by
      rw [l2_real_norm_eq_sqrt_integral_sq]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [h2_mem.coeFn_toLp] with g hg2
      change (f2 g) ^ 2 = _
      rw [hg2]
      by_cases hg : g ∈ Sx
      · simp [Sx, hg, mul_pow, Real.sq_sqrt (hw_pos _).le]
      · simp [Sx, hg]
    have h1_norm : ‖f1‖ = Real.sqrt (tamagawaNormFactor F * (2 * R)) := by
      rw [l2_real_norm_eq_sqrt_integral_sq, ← hslab.2]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [h1_mem.coeFn_toLp] with g hg1
      change (f1 g) ^ 2 = _
      rw [hg1]
      by_cases hg : g ∈ Sx <;> simp [Sx, hg]
    rwa [h2_norm, h1_norm] at hle
  refine (norm_integral_le_integral_norm _).trans ((integral_mono hint.norm hint_dom hpoint_le).trans ?_)
  rw [show (fun p : (ideleClassNorm F).ker × C𝔽 ↦
      (Mφ * Real.sqrt (CR * w x)) * Sx.indicator (fun g ↦ ‖u g‖ * Real.sqrt (w (logNorm g))) p.2) =
      fun p ↦ (1 : ℝ) * ((Mφ * Real.sqrt (CR * w x)) *
        Sx.indicator (fun g ↦ ‖u g‖ * Real.sqrt (w (logNorm g))) p.2) from by funext p; simp,
    integral_prod_mul (f := fun _ : (ideleClassNorm F).ker ↦ (1 : ℝ))
      (g := fun g : C𝔽 ↦ (Mφ * Real.sqrt (CR * w x)) * Sx.indicator (fun g ↦ ‖u g‖ * Real.sqrt (w (logNorm g))) g),
    show ∫ _k : (ideleClassNorm F).ker, (1 : ℝ) ∂(normOneProbHaar F) = 1 by
      rw [integral_const, smul_eq_mul, mul_one, Measure.real_def, normOneProbHaar_univ, ENNReal.toReal_one],
    one_mul, integral_const_mul]
  calc Mφ * Real.sqrt (CR * w x) * ∫ g : C𝔽, Sx.indicator (fun g ↦ ‖u g‖ * Real.sqrt (w (logNorm g))) g ∂μ𝔽
      ≤ Mφ * Real.sqrt (CR * w x) * (localL2Energy w u R x * Real.sqrt (tamagawaNormFactor F * (2 * R))) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = Mφ * Real.sqrt (CR * tamagawaNormFactor F * (2 * R)) * Real.sqrt (w x) * localL2Energy w u R x := by
        rw [Real.sqrt_mul hCR.le (w x), mul_assoc CR (tamagawaNormFactor F) (2 * R),
          Real.sqrt_mul hCR.le (tamagawaNormFactor F * (2 * R))]
        ring

lemma cornerOrbitProfile_contDiff {w : ℝ → ℝ} (hw_cont : Continuous w) (hw_pos : ∀ x, 0 < w x)
    (u : Lp ℂ 2 (weightedSobolevMeasure F w)) (ω : PontryaginDual (ideleClassNorm F).ker)
    (φ : BruhatCompactSupport C𝔽) {R : ℝ} (hR : 0 ≤ R) (hsupp : ∀ y ∈ tsupport φ.val, |logNorm y| ≤ R)
    {CR₁ : ℝ} (hCR₁ : 0 < CR₁) (hshift : ∀ x y : ℝ, |x - y| ≤ R + 1 → w x ≤ CR₁ * w y) :
    ∀ j : ℕ, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ ↦ cornerOrbitProfile w ω (normFlowIterDeriv j φ) u x) ∧
      ∀ x : ℝ, iteratedDeriv j (cornerOrbitProfile w ω φ u) x =
        cornerOrbitProfile w ω (normFlowIterDeriv j φ) u x := by
  have : IsFiniteMeasure (normOneProbHaar F) := normOneProbHaar_isFinite
  have hhasDeriv : ∀ (m : ℕ) (x₀ : ℝ),
      HasDerivAt (fun x : ℝ ↦ cornerOrbitProfile w ω (normFlowIterDeriv m φ) u x)
        (cornerOrbitProfile w ω (normFlowIterDeriv (m + 1) φ) u x₀) x₀ := by
    intro m x₀
    let s : Set ℝ := Metric.ball x₀ 1
    have hs_nhds : s ∈ 𝓝 x₀ := Metric.ball_mem_nhds x₀ zero_lt_one
    let ψm := normFlowIterDeriv m φ
    let ψm1 := normFlowIterDeriv (m + 1) φ
    have hψm1_cont : Continuous ψm1.val :=
      continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp ψm1.property.1)
    have hψm_cont : Continuous ψm.val :=
      continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp ψm.property.1)
    obtain ⟨M1_raw, hM1_raw⟩ := ψm1.property.2.exists_bound_of_continuousOn hψm1_cont.continuousOn
    let M1 : ℝ := max M1_raw 0
    have hM1 : ∀ y ∈ tsupport ψm1.val, ‖ψm1.val y‖ ≤ M1 := fun y hy ↦ (hM1_raw y hy).trans (le_max_left _ _)
    have hM1_nonneg : 0 ≤ M1 := le_max_right _ _
    let S0 : Set C𝔽 := {g : C𝔽 | |logNorm g - x₀| ≤ R + 1}
    have hS0_m : MeasurableSet S0 :=
      measurableSet_le (continuous_abs.measurable.comp (measurable_logNorm.sub measurable_const)) measurable_const
    let bound : (ideleClassNorm F).ker × C𝔽 → ℝ := fun p ↦ M1 * S0.indicator (fun g ↦ ‖u g‖ * w (logNorm g)) p.2
    have habs := tamagawa_absCont_weightedSobolevMeasure (F := F) hw_cont hw_pos
    have hbound_int : Integrable bound ((normOneProbHaar F).prod μ𝔽) := by
      have hS0_int : Integrable (fun g : C𝔽 ↦ S0.indicator (fun g ↦ ‖u g‖ * Real.sqrt (w (logNorm g))) g) μ𝔽 := by
        have hu_sq : Integrable (fun g : C𝔽 ↦ S0.indicator (fun g ↦ ‖u g‖ ^ 2 * w (logNorm g)) g) μ𝔽 :=
          (integrable_sq_mul_weight hw_cont hw_pos u).indicator hS0_m
        have hslab := indicator_slab_integrable_and_norm (F := F) (show 0 ≤ R + 1 by linarith) x₀
        have h1_mem : MemLp (fun g : C𝔽 ↦ S0.indicator (fun _ ↦ (1 : ℝ)) g) 2 μ𝔽 :=
          (memLp_two_iff_integrable_sq_norm hslab.1.1).mpr
            (hslab.1.congr (ae_of_all _ fun g ↦ by by_cases hg : g ∈ S0 <;> simp [S0, hg]))
        have h2_mem : MemLp (fun g : C𝔽 ↦ S0.indicator (fun g ↦ ‖u g‖ * Real.sqrt (w (logNorm g))) g) 2 μ𝔽 := by
          refine (memLp_two_iff_integrable_sq_norm ?_).mpr ?_
          · exact (((Lp.aestronglyMeasurable u).mono_ac habs).norm.mul
              (Real.continuous_sqrt.measurable.comp
                (hw_cont.measurable.comp measurable_logNorm)).aestronglyMeasurable).indicator hS0_m
          refine hu_sq.congr (ae_of_all _ fun g ↦ ?_)
          by_cases hg : g ∈ S0
          · simp only [hg, indicator_of_mem, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (hw_pos _).le]
          · simp [hg]
        refine (MemLp.integrable_mul h2_mem h1_mem).congr (ae_of_all _ fun g ↦ ?_)
        by_cases hg : g ∈ S0 <;> simp [hg]
      have hdom_g : ∀ g : C𝔽, ‖S0.indicator (fun g ↦ ‖u g‖ * w (logNorm g)) g‖ ≤
          Real.sqrt (CR₁ * w x₀) * S0.indicator (fun g ↦ ‖u g‖ * Real.sqrt (w (logNorm g))) g := by
        intro g
        by_cases hg : g ∈ S0
        · simp only [hg, indicator_of_mem, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hw_pos _).le)]
          have hw_le : Real.sqrt (w (logNorm g)) ≤ Real.sqrt (CR₁ * w x₀) := Real.sqrt_le_sqrt (hshift _ _ hg)
          calc ‖u g‖ * w (logNorm g)
              = ‖u g‖ * (Real.sqrt (w (logNorm g)) * Real.sqrt (w (logNorm g))) := by
                rw [Real.mul_self_sqrt (hw_pos _).le]
            _ ≤ ‖u g‖ * (Real.sqrt (CR₁ * w x₀) * Real.sqrt (w (logNorm g))) := by
                rw [mul_comm (Real.sqrt (CR₁ * w x₀))]
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hw_le (Real.sqrt_nonneg (w (logNorm g)))) (norm_nonneg _)
            _ = Real.sqrt (CR₁ * w x₀) * (‖u g‖ * Real.sqrt (w (logNorm g))) := by ring
        · simp [hg]
      have hmeas_g : AEStronglyMeasurable (fun g : C𝔽 ↦ S0.indicator (fun g ↦ ‖u g‖ * w (logNorm g)) g) μ𝔽 :=
        ((((Lp.aestronglyMeasurable u).mono_ac habs).norm.mul
          (hw_cont.measurable.comp measurable_logNorm).aestronglyMeasurable).indicator hS0_m)
      have hint_g : Integrable (fun g : C𝔽 ↦ S0.indicator (fun g ↦ ‖u g‖ * w (logNorm g)) g) μ𝔽 :=
        (hS0_int.const_mul (Real.sqrt (CR₁ * w x₀))).mono' hmeas_g (ae_of_all _ hdom_g)
      exact ((integrable_const (1 : ℝ)).mul_prod (hint_g.const_mul M1)).congr (ae_of_all _ fun p ↦ by simp [bound])
    let FF (x : ℝ) (p : (ideleClassNorm F).ker × C𝔽) : ℂ :=
      star (ψm.val (p.2 * (p.1 : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x)))) *
        (ω p.1 : ℂ) * u p.2 * (w (logNorm p.2) : ℂ)
    let FF' (x : ℝ) (p : (ideleClassNorm F).ker × C𝔽) : ℂ :=
      star (ψm1.val (p.2 * (p.1 : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x)))) *
        (ω p.1 : ℂ) * u p.2 * (w (logNorm p.2) : ℂ)
    have hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (FF x) ((normOneProbHaar F).prod μ𝔽) :=
      Filter.Eventually.of_forall fun x ↦ by
        have h1 : Continuous (fun p : (ideleClassNorm F).ker × C𝔽 ↦
            star (ψm.val (p.2 * (p.1 : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x))))) :=
          continuous_star.comp (hψm_cont.comp ((continuous_snd.mul (continuous_subtype_val.comp continuous_fst).inv).mul
            continuous_const))
        have h2 : Continuous (fun p : (ideleClassNorm F).ker × C𝔽 ↦ (ω p.1 : ℂ)) :=
          (continuous_subtype_val.comp ω.continuous).comp continuous_fst
        have h3 : AEStronglyMeasurable (fun p : (ideleClassNorm F).ker × C𝔽 ↦ u p.2)
            ((normOneProbHaar F).prod μ𝔽) :=
          ((Lp.aestronglyMeasurable u).mono_ac habs).comp_snd
        have h4 : Continuous (fun p : (ideleClassNorm F).ker × C𝔽 ↦ (w (logNorm p.2) : ℂ)) :=
          Complex.continuous_ofReal.comp ((hw_cont.comp continuous_logNorm).comp continuous_snd)
        exact ((h1.aestronglyMeasurable.mul h2.aestronglyMeasurable).mul h3).mul h4.aestronglyMeasurable
    have hF_int : Integrable (FF x₀) ((normOneProbHaar F).prod μ𝔽) :=
      (cornerOrbitProfile_bound_and_integrable hw_cont hw_pos u ω ψm hR
        (fun y hy ↦ hsupp y (tsupport_normFlowIterDeriv_subset m φ hy))
        hCR₁ (fun x y hxy ↦ hshift x y (hxy.trans (by linarith))) x₀).1
    have hF'_meas : AEStronglyMeasurable (FF' x₀) ((normOneProbHaar F).prod μ𝔽) :=
      (cornerOrbitProfile_bound_and_integrable hw_cont hw_pos u ω ψm1 hR
        (fun y hy ↦ hsupp y (tsupport_normFlowIterDeriv_subset (m + 1) φ hy))
        hCR₁ (fun x y hxy ↦ hshift x y (hxy.trans (by linarith))) x₀).1.1
    have h_bound : ∀ᵐ p ∂((normOneProbHaar F).prod μ𝔽), ∀ x ∈ s, ‖FF' x p‖ ≤ bound p := by
      refine ae_of_all _ fun ⟨k, g⟩ x hx ↦ ?_
      simp only [FF', bound, norm_mul, norm_star, Circle.norm_coe, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (hw_pos _).le]
      by_cases hzero : ψm1.val (g * (k : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x))) = 0
      · simp only [hzero, norm_zero, zero_mul]
        exact mul_nonneg hM1_nonneg (indicator_nonneg (fun _ _ ↦ mul_nonneg (norm_nonneg _) (hw_pos _).le) g)
      · have hsup1 : |logNorm (g * (k : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x)))| ≤ R :=
          hsupp _ (tsupport_normFlowIterDeriv_subset (m + 1) φ (subset_tsupport _ hzero))
        have hlog_eq : logNorm (g * (k : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x))) = logNorm g - x := by
          have hk : ideleClassNorm F (k : C𝔽) = 1 := k.property
          change Real.log ((ideleClassNorm F (g * (k : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x)))).val : ℝ) =
            logNorm g - x
          rw [map_mul, map_mul, map_inv, hk, inv_one, mul_one, ideleClassNorm_canonicalNormFlow,
            Units.val_mul, NNReal.coe_mul, Real.log_mul (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
            (NNReal.coe_pos.mpr (Units.zero_lt _)).ne']
          change logNorm g + Real.log (Real.exp (-x)) = logNorm g - x
          rw [Real.log_exp, sub_eq_add_neg]
        have hx1 : |x - x₀| ≤ 1 := (Metric.mem_ball.mp hx).le
        have hgS0 : g ∈ S0 := by
          change |logNorm g - x₀| ≤ R + 1
          rw [hlog_eq] at hsup1
          calc |logNorm g - x₀| = |(logNorm g - x) + (x - x₀)| := by ring_nf
            _ ≤ |logNorm g - x| + |x - x₀| := abs_add_le _ _
            _ ≤ R + 1 := add_le_add hsup1 hx1
        simp only [hgS0, indicator_of_mem]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (hM1 _ (subset_tsupport _ hzero))
          (mul_nonneg (norm_nonneg (u g)) (hw_pos _).le)
    have h_diff : ∀ᵐ p ∂((normOneProbHaar F).prod μ𝔽), ∀ x ∈ s, HasDerivAt (FF · p) (FF' x p) x := by
      refine ae_of_all _ fun ⟨k, g⟩ x _ ↦ ?_
      have hd := hasDerivAt_normFlowIterDeriv m φ (g * (k : C𝔽)⁻¹) x
      have hsc : HasDerivAt (fun t : ℝ ↦
          star (ψm.val (g * (k : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-t)))))
          (star (ψm1.val (g * (k : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x))))) x :=
        Complex.conjCLE.hasFDerivAt.comp_hasDerivAt x hd
      exact ((hsc.mul_const (ω k : ℂ)).mul_const (u g)).mul_const (w (logNorm g) : ℂ)
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs_nhds hF_meas hF_int hF'_meas
      h_bound hbound_int h_diff).2
  have hcd_nat : ∀ (n m : ℕ), ContDiff ℝ n
      (fun x : ℝ ↦ cornerOrbitProfile w ω (normFlowIterDeriv m φ) u x) := by
    intro n
    induction n with
    | zero =>
      intro m
      exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr fun x ↦ (hhasDeriv m x).continuousAt)
    | succ k ih =>
      intro m
      rw [show (↑(k + 1) : WithTop ℕ∞) = (↑k : WithTop ℕ∞) + 1 by push_cast; rfl, contDiff_succ_iff_deriv]
      refine ⟨fun x ↦ (hhasDeriv m x).differentiableAt, fun htop ↦ absurd htop (by simp), ?_⟩
      have hdeq : deriv (fun x : ℝ ↦ cornerOrbitProfile w ω (normFlowIterDeriv m φ) u x) =
          fun x ↦ cornerOrbitProfile w ω (normFlowIterDeriv (m + 1) φ) u x :=
        funext fun x ↦ (hhasDeriv m x).deriv
      rw [hdeq]
      exact ih (m + 1)
  have hiter : ∀ (j m : ℕ) (x : ℝ),
      iteratedDeriv j (fun t : ℝ ↦ cornerOrbitProfile w ω (normFlowIterDeriv m φ) u t) x =
        cornerOrbitProfile w ω (normFlowIterDeriv (m + j) φ) u x := by
    intro j
    induction j with
    | zero => intro m x; simp
    | succ k ih =>
      intro m x
      rw [iteratedDeriv_succ', show deriv (fun t : ℝ ↦ cornerOrbitProfile w ω (normFlowIterDeriv m φ) u t) =
          fun t ↦ cornerOrbitProfile w ω (normFlowIterDeriv (m + 1) φ) u t from
        funext fun t ↦ (hhasDeriv m t).deriv, ih (m + 1) x, add_right_comm, add_assoc]
  intro j
  refine ⟨contDiff_infty.mpr fun n ↦ hcd_nat n j, fun x ↦ ?_⟩
  simpa [normFlowIterDeriv] using hiter j 0 x

/-- Adelic-to-1D Fourier factorization of `⟪A r_z, u⟫` for any bounded operator whose a.e.
action is `lcaConvolution μ𝔽 φ.val`. -/
theorem weightedRieszJet_convolution_inner_eq_fourier {w : ℝ → ℝ} (hw_cont : Continuous w)
    (hw_pos : ∀ x, 0 < w x) {s σ : ℝ} (hs : 1 < s)
    (hw_dom : ∀ x, Real.exp (2 * σ * x) / w x ≤ (1 + x ^ 2) ^ (-s / 2))
    {R : ℝ} (hR : 0 ≤ R) {CR : ℝ} (hCR : 0 < CR)
    (hshift : ∀ x y : ℝ, |x - y| ≤ R → w x ≤ CR * w y)
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    (ω : PontryaginDual (ideleClassNorm F).ker) (τ : ℝ)
    (hτ : ∀ x : ℝ, (χ ω (canonicalNormFlow F (Multiplicative.ofAdd x)) : ℂ) =
      Complex.exp (Complex.I * (τ : ℂ) * (x : ℂ)))
    (φ : BruhatCompactSupport C𝔽) (hsupp : ∀ y ∈ tsupport φ.val, |logNorm y| ≤ R)
    (T : ℝ) (A : Lp ℂ 2 (weightedSobolevMeasure F w) →L[ℂ] Lp ℂ 2 (weightedSobolevMeasure F w))
    (hA : ∀ v, (A v : C𝔽 → ℂ) =ᵐ[μ𝔽] lcaConvolution μ𝔽 φ.val v)
    (u : Lp ℂ 2 (weightedSobolevMeasure F w)) :
    let r := weightedRieszJet hw_cont hw_pos hs hw_dom (χ ω) T
    @inner ℂ (Lp ℂ 2 (weightedSobolevMeasure F w)) _ (A r) u =
      (tamagawaNormFactor F : ℂ) * ∫ x : ℝ,
        (cornerOrbitProfile w ω φ u x * ((Real.exp (σ * x) / w x : ℝ) : ℂ)) *
          Complex.exp (-Complex.I * ((-(T + τ) : ℝ) : ℂ) * (x : ℂ)) := by
  classical
  intro r
  have h_isHaar : (μ𝔽).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have h_fin : IsFiniteMeasure (normOneProbHaar F) := normOneProbHaar_isFinite
  have hφ_cont : Continuous φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have hφ_int : Integrable φ.val μ𝔽 := hφ_cont.integrable_of_hasCompactSupport φ.property.2
  let rfn : C𝔽 → ℂ := fun g ↦
    star (ideleClassNormTwist (χ ω) (↑σ + ↑T * Complex.I) g) / (w (logNorm g) : ℂ)
  have hrfn_cont : Continuous rfn := Continuous.div
    (continuous_star.comp (ideleClassNormTwist (χ ω) (↑σ + ↑T * Complex.I)).continuous)
    (Complex.continuous_ofReal.comp (hw_cont.comp continuous_logNorm))
    fun g ↦ Complex.ofReal_ne_zero.mpr (hw_pos _).ne'
  have habs := tamagawa_absCont_weightedSobolevMeasure (F := F) hw_cont hw_pos
  have hrep_r : (r : C𝔽 → ℂ) =ᵐ[μ𝔽] rfn := habs.ae_le (MemLp.coeFn_toLp _)
  have hconv_eq (g : C𝔽) : lcaConvolution μ𝔽 φ.val r g = ∫ h : C𝔽, φ.val (g * h⁻¹) * rfn h ∂μ𝔽 := by
    let mp_g : MeasurePreserving (fun h : C𝔽 ↦ g * h⁻¹) μ𝔽 μ𝔽 :=
      (measurePreserving_mul_left μ𝔽 g).comp (Measure.measurePreserving_inv μ𝔽)
    have hcongr1 : (fun y : C𝔽 ↦ φ.val y * r (y⁻¹ * g)) =ᵐ[μ𝔽] fun y ↦ φ.val y * rfn (y⁻¹ * g) := by
      let mp_y : MeasurePreserving (fun y : C𝔽 ↦ y⁻¹ * g) μ𝔽 μ𝔽 :=
        (measurePreserving_mul_right μ𝔽 g).comp (Measure.measurePreserving_inv μ𝔽)
      filter_upwards [mp_y.quasiMeasurePreserving.ae hrep_r] with y hy
      rw [hy]
    rw [lcaConvolution, integral_congr_ae hcongr1, ← mp_g.integral_comp
      ((MeasurableEquiv.inv C𝔽).trans (MeasurableEquiv.mulLeft g)).measurableEmbedding]
    refine integral_congr_ae (ae_of_all _ fun h ↦ ?_)
    change φ.val (g * h⁻¹) * rfn ((g * h⁻¹)⁻¹ * g) = φ.val (g * h⁻¹) * rfn h
    congr 2
    group
  have hwd : Measurable (fun g : C𝔽 ↦ ENNReal.ofReal (w (logNorm g))) :=
    (hw_cont.measurable.comp measurable_logNorm).ennreal_ofReal
  have hinner_Ar : @inner ℂ (Lp ℂ 2 (weightedSobolevMeasure F w)) _ (A r) u =
      ∫ g : C𝔽, (∫ h : C𝔽, star (φ.val (g * h⁻¹)) * star (rfn h) ∂μ𝔽) * u g * (w (logNorm g) : ℂ) ∂μ𝔽 := by
    rw [L2.inner_def]
    have hwd_int : ∫ g : C𝔽, @inner ℂ ℂ _ ((A r) g) (u g) ∂(weightedSobolevMeasure F w) =
        ∫ g : C𝔽, (ENNReal.ofReal (w (logNorm g))).toReal • @inner ℂ ℂ _ ((A r) g) (u g) ∂μ𝔽 :=
      integral_withDensity_eq_integral_toReal_smul (μ := μ𝔽) hwd
        (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) (fun g : C𝔽 ↦ @inner ℂ ℂ _ ((A r) g) (u g))
    rw [hwd_int]
    refine integral_congr_ae ?_
    filter_upwards [hA r] with g hg
    rw [ENNReal.toReal_ofReal (hw_pos _).le, Complex.real_smul, RCLike.inner_apply, Complex.star_def,
      hg, hconv_eq g, ← integral_conj]
    simp only [map_mul]
    ring
  let Ker : C𝔽 × C𝔽 → ℂ := fun q ↦ star (φ.val (q.1 * q.2⁻¹)) * star (rfn q.2) * u q.1 * (w (logNorm q.1) : ℂ)
  have hKer_int : Integrable Ker (Measure.prod μ𝔽 μ𝔽) := by
    have hm1 : Continuous (fun q : C𝔽 × C𝔽 ↦ star (φ.val (q.1 * q.2⁻¹))) :=
      continuous_star.comp (hφ_cont.comp (continuous_fst.mul continuous_snd.inv))
    have hm2 : Continuous (fun q : C𝔽 × C𝔽 ↦ star (rfn q.2)) :=
      continuous_star.comp (hrfn_cont.comp continuous_snd)
    have hm3 : AEStronglyMeasurable (fun q : C𝔽 × C𝔽 ↦ u q.1) (Measure.prod μ𝔽 μ𝔽) :=
      ((Lp.aestronglyMeasurable u).mono_ac habs).comp_fst
    have hm4 : Continuous (fun q : C𝔽 × C𝔽 ↦ (w (logNorm q.1) : ℂ)) :=
      Complex.continuous_ofReal.comp ((hw_cont.comp continuous_logNorm).comp continuous_fst)
    have hKer_meas : AEStronglyMeasurable Ker (Measure.prod μ𝔽 μ𝔽) :=
      ((hm1.aestronglyMeasurable.mul hm2.aestronglyMeasurable).mul hm3).mul hm4.aestronglyMeasurable
    let r1 (h : C𝔽) : ℝ := ‖rfn h‖ * Real.sqrt (w (logNorm h))
    let u1 (g : C𝔽) : ℝ := ‖u g‖ * Real.sqrt (w (logNorm g))
    have hr1_sq : Integrable (fun h : C𝔽 ↦ r1 h ^ 2) μ𝔽 := by
      have hr2 : Integrable (fun h : C𝔽 ↦ ‖rfn h‖ ^ 2 * w (logNorm h)) μ𝔽 :=
        (integrable_sq_mul_weight hw_cont hw_pos r).congr (hrep_r.mono fun h hh ↦ by
          dsimp only; rw [hh])
      refine hr2.congr (ae_of_all _ fun h ↦ ?_)
      simp [r1, mul_pow, Real.sq_sqrt (hw_pos _).le]
    have hu1_sq : Integrable (fun g : C𝔽 ↦ u1 g ^ 2) μ𝔽 :=
      (integrable_sq_mul_weight hw_cont hw_pos u).congr (ae_of_all _ fun g ↦ by
        simp [u1, mul_pow, Real.sq_sqrt (hw_pos _).le])
    let dom1 : C𝔽 × C𝔽 → ℝ := fun q ↦ (Real.sqrt CR / 2) * (‖φ.val (q.1 * q.2⁻¹)‖ * r1 q.2 ^ 2)
    let dom2 : C𝔽 × C𝔽 → ℝ := fun q ↦ (Real.sqrt CR / 2) * (‖φ.val (q.1 * q.2⁻¹)‖ * u1 q.1 ^ 2)
    have hdom1_int : Integrable dom1 (Measure.prod μ𝔽 μ𝔽) := by
      have hswap_int : Integrable (fun q : C𝔽 × C𝔽 ↦ ‖φ.val (q.2 * q.1⁻¹)‖ * r1 q.1 ^ 2) (Measure.prod μ𝔽 μ𝔽) := by
        refine (integrable_prod_iff (μ := μ𝔽) (ν := μ𝔽) ?_).mpr ⟨?_, ?_⟩
        · exact (((hφ_cont.norm.comp (continuous_snd.mul continuous_fst.inv)).aestronglyMeasurable).mul
            (hr1_sq.1.comp_fst))
        · refine ae_of_all _ fun h ↦ ?_
          have mp_h : MeasurePreserving (fun g : C𝔽 ↦ g * h⁻¹) μ𝔽 μ𝔽 := measurePreserving_mul_right μ𝔽 h⁻¹
          exact (mp_h.integrable_comp_of_integrable hφ_int.norm).mul_const (r1 h ^ 2)
        · have heq_n : (fun h : C𝔽 ↦ ∫ g : C𝔽, ‖‖φ.val (g * h⁻¹)‖ * r1 h ^ 2‖ ∂μ𝔽) =
              fun h : C𝔽 ↦ (∫ y : C𝔽, ‖φ.val y‖ ∂μ𝔽) * r1 h ^ 2 := by
            funext h
            have mp_h : MeasurePreserving (fun g : C𝔽 ↦ g * h⁻¹) μ𝔽 μ𝔽 := measurePreserving_mul_right μ𝔽 h⁻¹
            simp_rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)), integral_mul_const,
              mp_h.integral_comp (MeasurableEquiv.mulRight h⁻¹).measurableEmbedding (fun y ↦ ‖φ.val y‖)]
          rw [heq_n]
          exact hr1_sq.const_mul _
      exact ((Measure.measurePreserving_swap (μ := μ𝔽) (ν := μ𝔽)).integrable_comp_of_integrable
        hswap_int).const_mul (Real.sqrt CR / 2)
    have hdom2_int : Integrable dom2 (Measure.prod μ𝔽 μ𝔽) := by
      have h_int : Integrable (fun q : C𝔽 × C𝔽 ↦ ‖φ.val (q.1 * q.2⁻¹)‖ * u1 q.1 ^ 2) (Measure.prod μ𝔽 μ𝔽) := by
        refine (integrable_prod_iff (μ := μ𝔽) (ν := μ𝔽) ?_).mpr ⟨?_, ?_⟩
        · exact (((hφ_cont.norm.comp (continuous_fst.mul continuous_snd.inv)).aestronglyMeasurable).mul
            (hu1_sq.1.comp_fst))
        · refine ae_of_all _ fun g ↦ ?_
          have mp_g : MeasurePreserving (fun h : C𝔽 ↦ g * h⁻¹) μ𝔽 μ𝔽 :=
            (measurePreserving_mul_left μ𝔽 g).comp (Measure.measurePreserving_inv μ𝔽)
          exact (mp_g.integrable_comp_of_integrable hφ_int.norm).mul_const (u1 g ^ 2)
        · have heq_n : (fun g : C𝔽 ↦ ∫ h : C𝔽, ‖‖φ.val (g * h⁻¹)‖ * u1 g ^ 2‖ ∂μ𝔽) =
              fun g : C𝔽 ↦ (∫ y : C𝔽, ‖φ.val y‖ ∂μ𝔽) * u1 g ^ 2 := by
            funext g
            have mp_g : MeasurePreserving (fun h : C𝔽 ↦ g * h⁻¹) μ𝔽 μ𝔽 :=
              (measurePreserving_mul_left μ𝔽 g).comp (Measure.measurePreserving_inv μ𝔽)
            simp_rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)), integral_mul_const]
            congr 1
            exact mp_g.integral_comp ((MeasurableEquiv.inv C𝔽).trans (MeasurableEquiv.mulLeft g)).measurableEmbedding
              (fun y ↦ ‖φ.val y‖)
          rw [heq_n]
          exact hu1_sq.const_mul _
      exact h_int.const_mul (Real.sqrt CR / 2)
    refine (hdom1_int.add hdom2_int).mono' hKer_meas (ae_of_all _ fun ⟨g, h⟩ ↦ ?_)
    dsimp only [Ker, dom1, dom2]
    rw [norm_mul, norm_mul, norm_mul, norm_star, norm_star, Complex.norm_real,
      Real.norm_of_nonneg (hw_pos _).le]
    by_cases h0 : φ.val (g * h⁻¹) = 0
    · simp only [h0, norm_zero, zero_mul]
      exact add_nonneg
        (mul_nonneg (by positivity) (mul_nonneg (norm_nonneg _) (sq_nonneg _)))
        (mul_nonneg (by positivity) (mul_nonneg (norm_nonneg _) (sq_nonneg _)))
    · have hlog_diff : |logNorm g - logNorm h| ≤ R := by
        have hgh : logNorm (g * h⁻¹) = logNorm g - logNorm h := by
          change Real.log ((ideleClassNorm F (g * h⁻¹)).val : ℝ) = _
          rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, NNReal.coe_mul,
            NNReal.coe_inv, Real.log_mul (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
            (inv_ne_zero (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'), Real.log_inv, sub_eq_add_neg]
        rw [← hgh]
        exact hsupp _ (subset_tsupport _ h0)
      have hw_le : Real.sqrt (w (logNorm g)) ≤ Real.sqrt CR * Real.sqrt (w (logNorm h)) := by
        rw [← Real.sqrt_mul hCR.le]
        exact Real.sqrt_le_sqrt (hshift _ _ hlog_diff)
      have hw_sq : w (logNorm g) = Real.sqrt (w (logNorm g)) * Real.sqrt (w (logNorm g)) :=
        (Real.mul_self_sqrt (hw_pos _).le).symm
      have ham : r1 h * u1 g ≤ (r1 h ^ 2 + u1 g ^ 2) / 2 := by
        nlinarith [sq_nonneg (r1 h - u1 g)]
      calc ‖φ.val (g * h⁻¹)‖ * ‖rfn h‖ * ‖u g‖ * w (logNorm g)
          = ‖φ.val (g * h⁻¹)‖ * ‖rfn h‖ * ‖u g‖ * (Real.sqrt (w (logNorm g)) * Real.sqrt (w (logNorm g))) := by
            rw [← hw_sq]
        _ ≤ ‖φ.val (g * h⁻¹)‖ * ‖rfn h‖ * ‖u g‖ *
              ((Real.sqrt CR * Real.sqrt (w (logNorm h))) * Real.sqrt (w (logNorm g))) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw_le (Real.sqrt_nonneg _))
              (by positivity)
        _ = Real.sqrt CR * (‖φ.val (g * h⁻¹)‖ * (r1 h * u1 g)) := by
            simp only [r1, u1]; ring
        _ ≤ Real.sqrt CR * (‖φ.val (g * h⁻¹)‖ * ((r1 h ^ 2 + u1 g ^ 2) / 2)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left ham (norm_nonneg _)) (Real.sqrt_nonneg _)
        _ = Real.sqrt CR / 2 * (‖φ.val (g * h⁻¹)‖ * r1 h ^ 2) +
              Real.sqrt CR / 2 * (‖φ.val (g * h⁻¹)‖ * u1 g ^ 2) := by ring
  have hswap1 : @inner ℂ (Lp ℂ 2 (weightedSobolevMeasure F w)) _ (A r) u =
      ∫ h : C𝔽, star (rfn h) * ∫ g : C𝔽, star (φ.val (g * h⁻¹)) * u g * (w (logNorm g) : ℂ) ∂μ𝔽 ∂μ𝔽 := by
    rw [hinner_Ar]
    calc ∫ g : C𝔽, (∫ h : C𝔽, star (φ.val (g * h⁻¹)) * star (rfn h) ∂μ𝔽) * u g * (w (logNorm g) : ℂ) ∂μ𝔽
        = ∫ g : C𝔽, ∫ h : C𝔽, Ker (g, h) ∂μ𝔽 ∂μ𝔽 := by
          refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
          dsimp only [Ker]
          rw [← integral_mul_const, ← integral_mul_const]
      _ = ∫ p : C𝔽 × C𝔽, Ker p ∂(Measure.prod μ𝔽 μ𝔽) := (integral_prod Ker hKer_int).symm
      _ = ∫ h : C𝔽, ∫ g : C𝔽, Ker (g, h) ∂μ𝔽 ∂μ𝔽 := integral_prod_symm Ker hKer_int
      _ = ∫ h : C𝔽, star (rfn h) * ∫ g : C𝔽, star (φ.val (g * h⁻¹)) * u g * (w (logNorm g) : ℂ) ∂μ𝔽 ∂μ𝔽 := by
          refine integral_congr_ae (ae_of_all _ fun h ↦ ?_)
          dsimp only [Ker]
          rw [← integral_const_mul]
          refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
          ring
  rw [hswap1, integral_tamagawa_eq_splitCoord, Complex.real_smul]
  congr 1
  let Φ₀ : C𝔽 → ℂ := fun h ↦
    star (rfn h) * ∫ g : C𝔽, star (φ.val (g * h⁻¹)) * u g * (w (logNorm g) : ℂ) ∂μ𝔽
  let Φ (p : ℝ × (ideleClassNorm F).ker) : ℂ := Φ₀ (splitCoordEquiv F p)
  have hΦ_int : Integrable Φ (volume.prod (normOneProbHaar F)) := by
    change Integrable (fun p : ℝ × (ideleClassNorm F).ker ↦ Φ₀ (splitCoordEquiv F p))
      (volume.prod (normOneProbHaar F))
    rw [← integrable_tamagawa_iff_splitCoord]
    exact hKer_int.integral_prod_right.congr (ae_of_all _ fun h ↦ by
      dsimp only [Φ₀, Ker]
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
      ring)
  rw [integral_prod Φ hΦ_int]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  have h_inv (k : (ideleClassNorm F).ker) (g : C𝔽) :
      g * (splitCoordEquiv F (x, k))⁻¹ = g * (k : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x)) := by
    change g * ((k : C𝔽) * canonicalNormFlow F (Multiplicative.ofAdd x))⁻¹ = _
    rw [mul_inv, ← map_inv (canonicalNormFlow F), show (Multiplicative.ofAdd x)⁻¹ = Multiplicative.ofAdd (-x) from rfl]
    group
  have h_srfn (k : (ideleClassNorm F).ker) :
      star (rfn (splitCoordEquiv F (x, k))) =
        (ω k : ℂ) * ((Real.exp (σ * x) / w x : ℝ) : ℂ) *
          Complex.exp (-Complex.I * ((-(T + τ) : ℝ) : ℂ) * (x : ℂ)) := by
    have hk : ideleClassNorm F (k : C𝔽) = 1 := k.property
    have hL : logNorm (splitCoordEquiv F (x, k)) = x := by
      change Real.log ((ideleClassNorm F ((k : C𝔽) * canonicalNormFlow F (Multiplicative.ofAdd x))).val : ℝ) = x
      rw [map_mul, hk, one_mul, ideleClassNorm_canonicalNormFlow]
      exact Real.log_exp x
    have hχk : χ ω (k : C𝔽) = ω k := DFunLike.congr_fun (hχ ω) k
    have hpow : (((ideleClassNorm F (splitCoordEquiv F (x, k))).val : ℝ) : ℂ) ^ ((σ : ℂ) + (T : ℂ) * Complex.I) =
        (Real.exp (σ * x) : ℂ) * Complex.exp (Complex.I * (T : ℂ) * (x : ℂ)) := by
      have hval : ((ideleClassNorm F (splitCoordEquiv F (x, k))).val : ℝ) = Real.exp x := by
        change ((ideleClassNorm F ((k : C𝔽) * canonicalNormFlow F (Multiplicative.ofAdd x))).val : ℝ) = Real.exp x
        rw [map_mul, hk, one_mul, ideleClassNorm_canonicalNormFlow]
        rfl
      rw [hval, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
        ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, mul_add, Complex.exp_add,
        mul_comm (x : ℂ) (σ : ℂ), ← Complex.ofReal_mul, ← Complex.ofReal_exp]
      congr 1
      congr 1
      ring
    dsimp only [rfn]
    rw [star_div₀, star_star, Complex.star_def, Complex.conj_ofReal, hL]
    change ideleClassNormTwist (χ ω) ((σ : ℂ) + (T : ℂ) * Complex.I)
        ((k : C𝔽) * canonicalNormFlow F (Multiplicative.ofAdd x)) / (w x : ℂ) = _
    have htw : ideleClassNormTwist (χ ω) ((σ : ℂ) + (T : ℂ) * Complex.I)
        ((k : C𝔽) * canonicalNormFlow F (Multiplicative.ofAdd x)) =
        (χ ω (k : C𝔽) : ℂ) * (χ ω (canonicalNormFlow F (Multiplicative.ofAdd x)) : ℂ) *
          (((ideleClassNorm F (splitCoordEquiv F (x, k))).val : ℝ) : ℂ) ^ ((σ : ℂ) + (T : ℂ) * Complex.I) := by
      change ((χ ω ((k : C𝔽) * canonicalNormFlow F (Multiplicative.ofAdd x)) : Circle) : ℂ) *
          (((ideleClassNorm F ((k : C𝔽) * canonicalNormFlow F (Multiplicative.ofAdd x))).val : ℝ) : ℂ) ^
            ((σ : ℂ) + (T : ℂ) * Complex.I) = _
      rw [map_mul, Circle.coe_mul, mul_assoc]
      simp only [mul_assoc]
      rfl
    rw [htw, hχk, hτ x, hpow]
    have hexp : Complex.exp (Complex.I * (τ : ℂ) * (x : ℂ)) * Complex.exp (Complex.I * (T : ℂ) * (x : ℂ)) =
        Complex.exp (-Complex.I * ((-(T + τ) : ℝ) : ℂ) * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1; push_cast; ring
    rw [div_eq_mul_inv]
    calc ((ω k : ℂ) * Complex.exp (Complex.I * (τ : ℂ) * (x : ℂ)) *
          ((Real.exp (σ * x) : ℂ) * Complex.exp (Complex.I * (T : ℂ) * (x : ℂ)))) * (w x : ℂ)⁻¹
        = (ω k : ℂ) * ((Real.exp (σ * x) : ℂ) * (w x : ℂ)⁻¹) *
            (Complex.exp (Complex.I * (τ : ℂ) * (x : ℂ)) * Complex.exp (Complex.I * (T : ℂ) * (x : ℂ))) := by ring
      _ = (ω k : ℂ) * ((Real.exp (σ * x) / w x : ℝ) : ℂ) *
            Complex.exp (-Complex.I * ((-(T + τ) : ℝ) : ℂ) * (x : ℂ)) := by
          rw [hexp, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← div_eq_mul_inv]
  have hint_x := (cornerOrbitProfile_bound_and_integrable hw_cont hw_pos u ω φ hR hsupp hCR hshift x).1
  calc ∫ k : (ideleClassNorm F).ker, Φ (x, k) ∂(normOneProbHaar F)
      = ∫ k : (ideleClassNorm F).ker, ∫ g : C𝔽,
          (star (φ.val (g * (k : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x)))) *
            (ω k : ℂ) * u g * (w (logNorm g) : ℂ)) *
            (((Real.exp (σ * x) / w x : ℝ) : ℂ) *
              Complex.exp (-Complex.I * ((-(T + τ) : ℝ) : ℂ) * (x : ℂ))) ∂μ𝔽 ∂(normOneProbHaar F) := by
        refine integral_congr_ae (ae_of_all _ fun k ↦ ?_)
        dsimp only [Φ, Φ₀]
        rw [h_srfn k, ← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
        dsimp only
        rw [h_inv k g]
        ring
    _ = (∫ k : (ideleClassNorm F).ker, ∫ g : C𝔽,
          star (φ.val (g * (k : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-x)))) *
            (ω k : ℂ) * u g * (w (logNorm g) : ℂ) ∂μ𝔽 ∂(normOneProbHaar F)) *
          (((Real.exp (σ * x) / w x : ℝ) : ℂ) *
            Complex.exp (-Complex.I * ((-(T + τ) : ℝ) : ℂ) * (x : ℂ))) := by
        simp_rw [integral_mul_const]
    _ = (cornerOrbitProfile w ω φ u x * ((Real.exp (σ * x) / w x : ℝ) : ℂ)) *
          Complex.exp (-Complex.I * ((-(T + τ) : ℝ) : ℂ) * (x : ℂ)) := by
        rw [cornerOrbitProfile, integral_prod _ hint_x]
        ring

end CornerFactorization

end RiemannMasullo.Isolated
