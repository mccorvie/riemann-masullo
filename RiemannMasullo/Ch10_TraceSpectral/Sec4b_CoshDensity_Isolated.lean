module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch10_TraceSpectral.Sec3
import RiemannMasullo.Ch09_HardySobolev.Sec2
import RiemannMasullo.Ch09_HardySobolev.Sec3

/-!
# Smooth `cosh` Sobolev space and spectral/geometric projections (`#7406`)

1. `coshSobolevDensity`, `coshSobolevMeasure`, `CoshIntervalSobolev`, `coshIntervalEquiv`.
2. `coshGlobalThetaSobolev`, `coshGeometricProjection` (`G_cosh`), `coshSpectralProjection` (`P_cosh`),
   `coshSpectralQuotient`, `coshQuotientEquiv`, `coshTestAction` (`A_cosh`), `coshSpectralConvolution`,
   and `coshGeometricProjection_comp_adjoint_comp_spectral`: `G_cosh ∘ (A_cosh ψ)† ∘ P_cosh = 0`.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set Topology
open scoped BigOperators ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo.Isolated.CoshPositiveWidth

section CoshDensitySpace

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => logIdeleClassNorm F
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α s

/-- Smooth strictly positive Sobolev density `2 * cosh (2 * α * x) * (1 + x^2)^{s/2}`. -/
def coshSobolevDensity (α s x : ℝ) : ℝ :=
  2 * Real.cosh (2 * α * x) * (1 + x ^ 2) ^ (s / 2)

lemma coshSobolevDensity_pos (α s x : ℝ) : 0 < coshSobolevDensity α s x := by
  unfold coshSobolevDensity
  exact mul_pos (mul_pos zero_lt_two (Real.cosh_pos _)) (by positivity)

lemma continuous_coshSobolevDensity (α s : ℝ) : Continuous (coshSobolevDensity α s) := by
  unfold coshSobolevDensity
  refine (continuous_const.mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).mul ?_
  exact (continuous_const.add (continuous_id.pow 2)).rpow_const fun x ↦
    Or.inl (by positivity : (1 : ℝ) + x ^ 2 ≠ 0)

lemma intervalSobolevDensity_le_coshSobolevDensity {α : ℝ} (_hα : 0 ≤ α) (s x : ℝ) :
    intervalSobolevDensity (-α) α s x ≤ coshSobolevDensity α s x := by
  unfold intervalSobolevDensity coshSobolevDensity
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hcosh : 2 * Real.cosh (2 * α * x) = Real.exp (2 * α * x) + Real.exp (-(2 * α * x)) := by
    rw [Real.cosh_eq]; ring
  rw [hcosh]
  refine max_le ?_ ?_
  · rw [show 2 * -α * x = -(2 * α * x) by ring]
    exact le_add_of_nonneg_left (Real.exp_pos _).le
  · exact le_add_of_nonneg_right (Real.exp_pos _).le

lemma coshSobolevDensity_le_two_mul {α : ℝ} (_hα : 0 ≤ α) (s x : ℝ) :
    coshSobolevDensity α s x ≤ 2 * intervalSobolevDensity (-α) α s x := by
  unfold intervalSobolevDensity coshSobolevDensity
  rw [← mul_assoc (2 : ℝ)]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hcosh : 2 * Real.cosh (2 * α * x) = Real.exp (2 * α * x) + Real.exp (-(2 * α * x)) := by
    rw [Real.cosh_eq]; ring
  rw [hcosh, show -(2 * α * x) = 2 * -α * x by ring]
  linarith [le_max_left (Real.exp (2 * -α * x)) (Real.exp (2 * α * x)),
    le_max_right (Real.exp (2 * -α * x)) (Real.exp (2 * α * x))]

lemma coshSobolevDensity_shift_le {α s : ℝ} (_hα : 0 ≤ α) (hs : 0 ≤ s) (t x : ℝ) :
    coshSobolevDensity α s (t + x) ≤
      Real.exp (2 * α * |t|) * (1 + |t|) ^ s * coshSobolevDensity α s x := by
  unfold coshSobolevDensity
  have hcosh : Real.cosh (2 * α * (t + x)) ≤ Real.exp (2 * α * |t|) * Real.cosh (2 * α * x) := by
    rw [Real.cosh_eq, Real.cosh_eq, ← mul_div_assoc]
    have h1 : Real.exp (2 * α * (t + x)) ≤ Real.exp (2 * α * |t|) * Real.exp (2 * α * x) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith [le_abs_self t])
    have h2 : Real.exp (-(2 * α * (t + x))) ≤ Real.exp (2 * α * |t|) * Real.exp (-(2 * α * x)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith [neg_abs_le t])
    linarith
  have hpoly : (1 + (t + x) ^ 2) ^ (s / 2) ≤ (1 + |t|) ^ s * (1 + x ^ 2) ^ (s / 2) := by
    have hsq : 1 + (t + x) ^ 2 ≤ (1 + |t|) ^ 2 * (1 + x ^ 2) := by
      have htx : 2 * (t * x) ≤ 2 * (|t| * |x|) :=
        mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (by rw [abs_mul])) zero_le_two
      have hx2 : 2 * |x| ≤ 1 + x ^ 2 := by nlinarith [sq_abs x, sq_nonneg (|x| - 1)]
      have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
      nlinarith [sq_abs t, sq_abs x, abs_nonneg t]
    calc (1 + (t + x) ^ 2) ^ (s / 2)
        ≤ ((1 + |t|) ^ 2 * (1 + x ^ 2)) ^ (s / 2) :=
          Real.rpow_le_rpow (by positivity) hsq (by positivity)
      _ = ((1 + |t|) ^ 2) ^ (s / 2) * (1 + x ^ 2) ^ (s / 2) :=
          Real.mul_rpow (by positivity) (by positivity)
      _ = (1 + |t|) ^ s * (1 + x ^ 2) ^ (s / 2) := by
          rw [← Real.rpow_natCast (1 + |t|) 2, ← Real.rpow_mul (by positivity)]
          congr 2; push_cast; ring
  calc 2 * Real.cosh (2 * α * (t + x)) * (1 + (t + x) ^ 2) ^ (s / 2)
      ≤ (2 * (Real.exp (2 * α * |t|) * Real.cosh (2 * α * x))) *
          ((1 + |t|) ^ s * (1 + x ^ 2) ^ (s / 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcosh zero_le_two) hpoly
          (by positivity) (mul_nonneg zero_le_two (mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le))
    _ = Real.exp (2 * α * |t|) * (1 + |t|) ^ s *
          (2 * Real.cosh (2 * α * x) * (1 + x ^ 2) ^ (s / 2)) := by ring

lemma continuous_logNorm : Continuous (logNorm : C𝔽 → ℝ) :=
  (NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).log
    fun g ↦ NNReal.coe_ne_zero.mpr ((continuousIdeleClassNorm F g).ne_zero)

lemma measurable_logNorm : Measurable (logNorm : C𝔽 → ℝ) :=
  (continuous_logNorm (F := F)).measurable

variable (F) in
/-- Weighted measure on `C𝔽` with smooth `cosh` density. -/
def coshSobolevMeasure (α s : ℝ) : Measure C𝔽 :=
  (μ𝔽).withDensity fun g ↦ ENNReal.ofReal (coshSobolevDensity α s (logNorm g))

lemma coshSobolevMeasure_eq_withDensity (α s : ℝ) :
    coshSobolevMeasure F α s =
      (μ𝔽).withDensity fun g ↦ ENNReal.ofReal (coshSobolevDensity α s (logNorm g)) := rfl

lemma coshSobolevMeasure_absCont (α s : ℝ) : coshSobolevMeasure F α s ≪ μ𝔽 :=
  withDensity_absolutelyContinuous _ _

lemma tamagawa_absCont_coshSobolevMeasure (α s : ℝ) : μ𝔽 ≪ coshSobolevMeasure F α s :=
  withDensity_absolutelyContinuous'
    (((continuous_coshSobolevDensity α s).measurable.comp (measurable_logNorm (F := F))).ennreal_ofReal.aemeasurable)
    (ae_of_all _ fun g ↦ (ENNReal.ofReal_pos.mpr (coshSobolevDensity_pos α s (logNorm g))).ne')

lemma coshSobolevMeasure_sigmaFinite (α s : ℝ) : SigmaFinite (coshSobolevMeasure F α s) :=
  MeasureTheory.SigmaFinite.withDensity_ofReal (μ := μ𝔽) _

variable (F) in
/-- Sharp-interval weighted measure with `intervalSobolevDensity (-α) α s`. -/
def sharpIntervalMeasure (α s : ℝ) : Measure C𝔽 :=
  intervalSobolevMeasure μ𝔽 logNorm (-α) α s false

lemma sharpIntervalMeasure_eq_withDensity (α s : ℝ) :
    sharpIntervalMeasure F α s =
      (μ𝔽).withDensity fun g ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s (logNorm g)) := by
  unfold sharpIntervalMeasure intervalSobolevMeasure
  simp only [Bool.false_eq_true, ↓reduceIte]

lemma sharpIntervalMeasure_absCont (α s : ℝ) : sharpIntervalMeasure F α s ≪ μ𝔽 := by
  rw [sharpIntervalMeasure_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

lemma continuous_intervalSobolevDensity' (a b s : ℝ) : Continuous (intervalSobolevDensity a b s) := by
  unfold intervalSobolevDensity
  refine ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).max
    (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul ?_
  exact (continuous_const.add (continuous_id.pow 2)).rpow_const fun x ↦
    Or.inl (by positivity : (1 : ℝ) + x ^ 2 ≠ 0)

lemma intervalSobolevDensity'_pos (a b s x : ℝ) : 0 < intervalSobolevDensity a b s x := by
  unfold intervalSobolevDensity
  exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (by positivity)

lemma tamagawa_absCont_sharpIntervalMeasure (α s : ℝ) : μ𝔽 ≪ sharpIntervalMeasure F α s := by
  rw [sharpIntervalMeasure_eq_withDensity]
  exact withDensity_absolutelyContinuous'
    (((continuous_intervalSobolevDensity' (-α) α s).measurable.comp (measurable_logNorm (F := F))).ennreal_ofReal.aemeasurable)
    (ae_of_all _ fun g ↦ (ENNReal.ofReal_pos.mpr (intervalSobolevDensity'_pos (-α) α s (logNorm g))).ne')

lemma coshSobolevMeasure_le_two_mul_sharp {α : ℝ} (hα : 0 ≤ α) (s : ℝ) :
    coshSobolevMeasure F α s ≤ (2 : ℝ≥0∞) • sharpIntervalMeasure F α s := by
  intro S
  rw [smul_apply, smul_eq_mul, coshSobolevMeasure, sharpIntervalMeasure_eq_withDensity]
  simp only [withDensity_apply' _]
  rw [← lintegral_const_mul' (2 : ℝ≥0∞) _ ENNReal.ofNat_ne_top]
  refine lintegral_mono fun g ↦ ?_
  rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul zero_le_two]
  exact ENNReal.ofReal_le_ofReal (coshSobolevDensity_le_two_mul hα s (logNorm g))

lemma sharpIntervalMeasure_le_cosh {α : ℝ} (hα : 0 ≤ α) (s : ℝ) :
    sharpIntervalMeasure F α s ≤ coshSobolevMeasure F α s := by
  intro S
  rw [coshSobolevMeasure, sharpIntervalMeasure_eq_withDensity]
  refine withDensity_mono (ae_of_all _ fun g ↦ ?_) S
  exact ENNReal.ofReal_le_ofReal (intervalSobolevDensity_le_coshSobolevDensity hα s (logNorm g))

variable (F) in
/-- Smooth `cosh`-weighted Sobolev Hilbert space `L²(μ𝔽, 2 cosh(2 α log|·|) (1 + (log|·|)^2)^{s/2})`. -/
def CoshIntervalSobolev (α s : ℝ) : Type _ :=
  Lp ℂ 2 (coshSobolevMeasure F α s)

instance instNormedAddCommGroupCosh (α s : ℝ) :
    NormedAddCommGroup (CoshIntervalSobolev F α s) :=
  inferInstanceAs (NormedAddCommGroup (Lp ℂ 2 (coshSobolevMeasure F α s)))

instance instInnerProductSpaceCosh (α s : ℝ) :
    InnerProductSpace ℂ (CoshIntervalSobolev F α s) :=
  inferInstanceAs (InnerProductSpace ℂ (Lp ℂ 2 (coshSobolevMeasure F α s)))

instance instCompleteSpaceCosh (α s : ℝ) :
    CompleteSpace (CoshIntervalSobolev F α s) :=
  inferInstanceAs (CompleteSpace (Lp ℂ 2 (coshSobolevMeasure F α s)))

variable (F) in
/-- Definitional `LinearIsometryEquiv` identifying `CoshIntervalSobolev F α s` with `Lp ℂ 2 (coshSobolevMeasure F α s)`. -/
def coshIntervalToLp (α s : ℝ) :
    CoshIntervalSobolev F α s ≃ₗᵢ[ℂ] Lp ℂ 2 (coshSobolevMeasure F α s) :=
  LinearIsometryEquiv.refl ℂ (Lp ℂ 2 (coshSobolevMeasure F α s))

instance instCoeFunCoshInterval (α s : ℝ) :
    CoeFun (CoshIntervalSobolev F α s) (fun _ ↦ C𝔽 → ℂ) :=
  ⟨fun u ↦ (coshIntervalToLp F α s u : C𝔽 → ℂ)⟩

@[ext]
lemma CoshIntervalSobolev.ext {α s : ℝ} {u v : CoshIntervalSobolev F α s}
    (h : (coshIntervalToLp F α s u : C𝔽 → ℂ) =ᵐ[coshSobolevMeasure F α s]
      (coshIntervalToLp F α s v : C𝔽 → ℂ)) : u = v :=
  (coshIntervalToLp F α s).injective (Lp.ext h)

/-- Linear isometry equivalence between `Lp ℂ 2 μ₁` and `Lp ℂ 2 μ₂` when `μ₁ = μ₂`. -/
def coshLpEquivOfMeasureEq {α : Type*} [MeasurableSpace α] {μ₁ μ₂ : Measure α} (h : μ₁ = μ₂) :
    Lp ℂ 2 μ₁ ≃ₗᵢ[ℂ] Lp ℂ 2 μ₂ := by
  subst h
  exact LinearIsometryEquiv.refl ℂ (Lp ℂ 2 μ₁)

def coshToSharpFun {α : ℝ} (hα : 0 ≤ α) (s : ℝ) (u : CoshIntervalSobolev F α s) :
    Lp ℂ 2 (sharpIntervalMeasure F α s) :=
  ((Lp.memLp (coshIntervalToLp F α s u)).mono_measure (sharpIntervalMeasure_le_cosh hα s)).toLp
    (coshIntervalToLp F α s u)

def sharpToCoshFun {α : ℝ} (hα : 0 ≤ α) (s : ℝ) (v : Lp ℂ 2 (sharpIntervalMeasure F α s)) :
    CoshIntervalSobolev F α s :=
  (coshIntervalToLp F α s).symm
    (((Lp.memLp v).of_measure_le_smul (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (coshSobolevMeasure_le_two_mul_sharp hα s)).toLp v)

/-- Bounded linear isomorphism between `CoshIntervalSobolev F α s` and `CompactIntervalSobolev μ𝔽 logNorm (-α) α s`. -/
def coshIntervalEquiv {α : ℝ} (hα : 0 ≤ α) (s : ℝ) :
    CoshIntervalSobolev F α s ≃L[ℂ] W(α, s) := by
  have h1 : sharpIntervalMeasure F α s ≤ coshSobolevMeasure F α s := sharpIntervalMeasure_le_cosh hα s
  have h2 : coshSobolevMeasure F α s ≤ (2 : ℝ≥0∞) • sharpIntervalMeasure F α s :=
    coshSobolevMeasure_le_two_mul_sharp hα s
  let toLp (u : CoshIntervalSobolev F α s) : Lp ℂ 2 (coshSobolevMeasure F α s) :=
    coshIntervalToLp F α s u
  have habs_sh := tamagawa_absCont_sharpIntervalMeasure (F := F) α s
  have habs_co := tamagawa_absCont_coshSobolevMeasure (F := F) α s
  let L_fwd_lm : CoshIntervalSobolev F α s →ₗ[ℂ] Lp ℂ 2 (sharpIntervalMeasure F α s) :=
    { toFun := coshToSharpFun hα s
      map_add' := fun u v ↦ by
        ext1
        have hEq : (coshToSharpFun hα s (u + v) : C𝔽 → ℂ) =ᵐ[μ𝔽]
            ((coshToSharpFun hα s u + coshToSharpFun hα s v : Lp ℂ 2 (sharpIntervalMeasure F α s)) : C𝔽 → ℂ) := by
          filter_upwards [habs_sh.ae_le ((Lp.memLp (toLp (u + v))).mono_measure h1).coeFn_toLp,
            habs_sh.ae_le ((Lp.memLp (toLp u)).mono_measure h1).coeFn_toLp,
            habs_sh.ae_le ((Lp.memLp (toLp v)).mono_measure h1).coeFn_toLp,
            habs_co.ae_le (Lp.coeFn_add (toLp u) (toLp v)),
            habs_sh.ae_le (Lp.coeFn_add (coshToSharpFun hα s u) (coshToSharpFun hα s v))] with g h0 hu hv ha hb
          exact h0.trans (ha.trans (by dsimp only [Pi.add_apply]; rw [← hu, ← hv]; exact hb.symm))
        exact (sharpIntervalMeasure_absCont α s).ae_le hEq
      map_smul' := fun c u ↦ by
        ext1
        have hEq : (coshToSharpFun hα s (c • u) : C𝔽 → ℂ) =ᵐ[μ𝔽]
            ((c • coshToSharpFun hα s u : Lp ℂ 2 (sharpIntervalMeasure F α s)) : C𝔽 → ℂ) := by
          filter_upwards [habs_sh.ae_le ((Lp.memLp (toLp (c • u))).mono_measure h1).coeFn_toLp,
            habs_sh.ae_le ((Lp.memLp (toLp u)).mono_measure h1).coeFn_toLp,
            habs_co.ae_le (Lp.coeFn_smul c (toLp u)),
            habs_sh.ae_le (Lp.coeFn_smul c (coshToSharpFun hα s u))] with g h0 hu ha hb
          exact h0.trans (ha.trans (by dsimp only [Pi.smul_apply]; rw [← hu]; exact hb.symm))
        exact (sharpIntervalMeasure_absCont α s).ae_le hEq }
  let L_fwd : CoshIntervalSobolev F α s →L[ℂ] Lp ℂ 2 (sharpIntervalMeasure F α s) :=
    LinearMap.mkContinuous L_fwd_lm 1 fun u ↦ by
      rw [one_mul]
      dsimp only [L_fwd_lm, LinearMap.coe_mk, AddHom.coe_mk, coshToSharpFun]
      rw [Lp.norm_toLp, show ‖u‖ = (eLpNorm (toLp u : C𝔽 → ℂ) 2 (coshSobolevMeasure F α s)).toReal from
        Lp.norm_def (toLp u)]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top (toLp u)) (eLpNorm_mono_measure _ h1)
  let L_bwd : Lp ℂ 2 (sharpIntervalMeasure F α s) →L[ℂ] CoshIntervalSobolev F α s :=
    LinearMap.mkContinuous
      { toFun := sharpToCoshFun hα s
        map_add' := fun u v ↦ by
          refine CoshIntervalSobolev.ext ((coshSobolevMeasure_absCont α s).ae_le ?_)
          have hEq : (toLp (sharpToCoshFun hα s (u + v)) : C𝔽 → ℂ) =ᵐ[μ𝔽]
              (toLp (sharpToCoshFun hα s u + sharpToCoshFun hα s v) : C𝔽 → ℂ) := by
            filter_upwards [habs_co.ae_le ((Lp.memLp (u + v)).of_measure_le_smul (by norm_num) h2).coeFn_toLp,
              habs_co.ae_le ((Lp.memLp u).of_measure_le_smul (by norm_num) h2).coeFn_toLp,
              habs_co.ae_le ((Lp.memLp v).of_measure_le_smul (by norm_num) h2).coeFn_toLp,
              habs_sh.ae_le (Lp.coeFn_add u v),
              habs_co.ae_le (Lp.coeFn_add (toLp (sharpToCoshFun hα s u)) (toLp (sharpToCoshFun hα s v)))] with g h0 hu hv ha hb
            change (coshIntervalToLp F α s ((coshIntervalToLp F α s).symm _) : C𝔽 → ℂ) g =
              (toLp (sharpToCoshFun hα s u) + toLp (sharpToCoshFun hα s v)) g
            rw [(coshIntervalToLp F α s).apply_symm_apply]
            have hu' : (toLp (sharpToCoshFun hα s u) : C𝔽 → ℂ) g = u g := by
              change (coshIntervalToLp F α s ((coshIntervalToLp F α s).symm _) : C𝔽 → ℂ) g = u g
              rw [(coshIntervalToLp F α s).apply_symm_apply]; exact hu
            have hv' : (toLp (sharpToCoshFun hα s v) : C𝔽 → ℂ) g = v g := by
              change (coshIntervalToLp F α s ((coshIntervalToLp F α s).symm _) : C𝔽 → ℂ) g = v g
              rw [(coshIntervalToLp F α s).apply_symm_apply]; exact hv
            exact h0.trans (ha.trans (by dsimp only [Pi.add_apply]; rw [← hu', ← hv']; exact hb.symm))
          exact hEq
        map_smul' := fun c u ↦ by
          refine CoshIntervalSobolev.ext ((coshSobolevMeasure_absCont α s).ae_le ?_)
          have hEq : (toLp (sharpToCoshFun hα s (c • u)) : C𝔽 → ℂ) =ᵐ[μ𝔽]
              (toLp (c • sharpToCoshFun hα s u) : C𝔽 → ℂ) := by
            filter_upwards [habs_co.ae_le ((Lp.memLp (c • u)).of_measure_le_smul (by norm_num) h2).coeFn_toLp,
              habs_co.ae_le ((Lp.memLp u).of_measure_le_smul (by norm_num) h2).coeFn_toLp,
              habs_sh.ae_le (Lp.coeFn_smul c u),
              habs_co.ae_le (Lp.coeFn_smul c (toLp (sharpToCoshFun hα s u)))] with g h0 hu ha hb
            change (coshIntervalToLp F α s ((coshIntervalToLp F α s).symm _) : C𝔽 → ℂ) g =
              (c • toLp (sharpToCoshFun hα s u)) g
            rw [(coshIntervalToLp F α s).apply_symm_apply]
            have hu' : (toLp (sharpToCoshFun hα s u) : C𝔽 → ℂ) g = u g := by
              change (coshIntervalToLp F α s ((coshIntervalToLp F α s).symm _) : C𝔽 → ℂ) g = u g
              rw [(coshIntervalToLp F α s).apply_symm_apply]; exact hu
            exact h0.trans (ha.trans (by dsimp only [Pi.smul_apply]; rw [← hu']; exact hb.symm))
          exact hEq }
      (Real.sqrt 2) fun u ↦ by
        dsimp only [LinearMap.coe_mk, AddHom.coe_mk, sharpToCoshFun]
        change ‖coshIntervalToLp F α s ((coshIntervalToLp F α s).symm
          (((Lp.memLp u).of_measure_le_smul (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) h2).toLp u))‖ ≤ _
        rw [(coshIntervalToLp F α s).apply_symm_apply, Lp.norm_toLp, Lp.norm_def]
        have he := eLpNorm_mono_measure (p := 2) (u : C𝔽 → ℂ) h2
        rw [eLpNorm_smul_measure_of_ne_zero (by norm_num : (2 : ℝ≥0∞) ≠ 0), smul_eq_mul] at he
        have he2 : eLpNorm (u : C𝔽 → ℂ) 2 (coshSobolevMeasure F α s) ≤
            (ENNReal.ofReal (Real.sqrt 2)) * eLpNorm (u : C𝔽 → ℂ) 2 (sharpIntervalMeasure F α s) := by
          refine he.trans_eq ?_
          congr 1
          rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
            ← ENNReal.ofReal_ofNat 2, ENNReal.ofReal_rpow_of_pos zero_lt_two]
          exact congrArg ENNReal.ofReal (by norm_num [Real.sqrt_eq_rpow])
        refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top u)) he2).trans_eq ?_
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg 2)]
  let E_lp : CoshIntervalSobolev F α s ≃L[ℂ] Lp ℂ 2 (sharpIntervalMeasure F α s) :=
    { L_fwd.toLinearMap with
      invFun := L_bwd
      left_inv := fun u ↦ by
        refine CoshIntervalSobolev.ext ?_
        have ha : (toLp (sharpToCoshFun hα s (coshToSharpFun hα s u)) : C𝔽 → ℂ) =ᵐ[μ𝔽]
            (coshToSharpFun hα s u : C𝔽 → ℂ) := by
          have hc := habs_co.ae_le ((Lp.memLp (coshToSharpFun hα s u)).of_measure_le_smul (by norm_num) h2).coeFn_toLp
          filter_upwards [hc] with g hg
          change (coshIntervalToLp F α s ((coshIntervalToLp F α s).symm _) : C𝔽 → ℂ) g = _
          rw [(coshIntervalToLp F α s).apply_symm_apply]; exact hg
        have hb : (coshToSharpFun hα s u : C𝔽 → ℂ) =ᵐ[μ𝔽] (toLp u : C𝔽 → ℂ) :=
          habs_sh.ae_le ((Lp.memLp (toLp u)).mono_measure h1).coeFn_toLp
        exact (coshSobolevMeasure_absCont α s).ae_le (ha.trans hb)
      right_inv := fun v ↦ by
        ext1
        have ha : (coshToSharpFun hα s (sharpToCoshFun hα s v) : C𝔽 → ℂ) =ᵐ[μ𝔽]
            (toLp (sharpToCoshFun hα s v) : C𝔽 → ℂ) :=
          habs_sh.ae_le ((Lp.memLp (toLp (sharpToCoshFun hα s v))).mono_measure h1).coeFn_toLp
        have hb : (toLp (sharpToCoshFun hα s v) : C𝔽 → ℂ) =ᵐ[μ𝔽] (v : C𝔽 → ℂ) := by
          have hc := habs_co.ae_le ((Lp.memLp v).of_measure_le_smul (by norm_num) h2).coeFn_toLp
          filter_upwards [hc] with g hg
          change (coshIntervalToLp F α s ((coshIntervalToLp F α s).symm _) : C𝔽 → ℂ) g = _
          rw [(coshIntervalToLp F α s).apply_symm_apply]; exact hg
        exact (sharpIntervalMeasure_absCont α s).ae_le (ha.trans hb)
      continuous_toFun := L_fwd.continuous
      continuous_invFun := L_bwd.continuous }
  exact E_lp.trans (coshLpEquivOfMeasureEq (rfl : sharpIntervalMeasure F α s =
    intervalSobolevMeasure μ𝔽 logNorm (-α) α s false)).toContinuousLinearEquiv

lemma coshIntervalEquiv_ae {α : ℝ} (hα : 0 ≤ α) (s : ℝ) (u : CoshIntervalSobolev F α s) :
    (coshIntervalEquiv (F := F) hα s u : C𝔽 → ℂ) =ᵐ[μ𝔽] (u : C𝔽 → ℂ) := by
  have h1 : sharpIntervalMeasure F α s ≤ coshSobolevMeasure F α s := sharpIntervalMeasure_le_cosh hα s
  change (coshToSharpFun hα s u : C𝔽 → ℂ) =ᵐ[μ𝔽] (u : C𝔽 → ℂ)
  exact (tamagawa_absCont_sharpIntervalMeasure (F := F) α s).ae_le
    ((Lp.memLp (coshIntervalToLp F α s u)).mono_measure h1).coeFn_toLp

lemma coshIntervalEquiv_symm_ae {α : ℝ} (hα : 0 ≤ α) (s : ℝ) (v : W(α, s)) :
    ((coshIntervalEquiv (F := F) hα s).symm v : C𝔽 → ℂ) =ᵐ[μ𝔽] (v : C𝔽 → ℂ) := by
  have h2 : coshSobolevMeasure F α s ≤ (2 : ℝ≥0∞) • sharpIntervalMeasure F α s :=
    coshSobolevMeasure_le_two_mul_sharp hα s
  let v₀ : Lp ℂ 2 (sharpIntervalMeasure F α s) :=
    (coshLpEquivOfMeasureEq (rfl : sharpIntervalMeasure F α s =
      intervalSobolevMeasure μ𝔽 logNorm (-α) α s false)).symm v
  have hmem := (tamagawa_absCont_coshSobolevMeasure (F := F) α s).ae_le
    ((Lp.memLp v₀).of_measure_le_smul (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) h2).coeFn_toLp
  filter_upwards [hmem] with g hg
  change (coshIntervalToLp F α s (sharpToCoshFun hα s v₀) : C𝔽 → ℂ) g = (v : C𝔽 → ℂ) g
  dsimp only [sharpToCoshFun]
  rw [(coshIntervalToLp F α s).apply_symm_apply]
  exact hg

end CoshDensitySpace

section CoshOperatorsAndSubspaces

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => logIdeleClassNorm F
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α s

private lemma cosh_liftQL_mkQL {M N : Type*} [AddCommGroup M] [Module ℂ M] [TopologicalSpace M]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (S : Submodule ℂ M) (f : M →L[ℂ] N) (h : S ≤ f.ker) (x : M) :
    S.liftQL f h (S.mkQL x) = f x :=
  LinearMap.congr_fun (S.liftQ_mkQ f.toLinearMap h) x

/-- Closed theta subspace transferred to `CoshIntervalSobolev F α s`. -/
def coshGlobalThetaSobolev (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    Submodule ℂ (CoshIntervalSobolev F α s) :=
  (globalThetaSobolev F a ((neg_nonpos.mpr hα).trans hα) hs).comap
    (coshIntervalEquiv hα s).toContinuousLinearMap.toLinearMap

instance instClosedCoshGlobalThetaSobolev (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    IsClosed ((coshGlobalThetaSobolev (F := F) a hα hs : Submodule ℂ (CoshIntervalSobolev F α s)) :
      Set (CoshIntervalSobolev F α s)) :=
  (Submodule.isClosed_topologicalClosure _).preimage (coshIntervalEquiv hα s).continuous

instance instHasOrthogonalProjectionCoshTheta (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    (coshGlobalThetaSobolev (F := F) a hα hs).HasOrthogonalProjection := by
  have : CompleteSpace (coshGlobalThetaSobolev (F := F) a hα hs) :=
    (instClosedCoshGlobalThetaSobolev a hα hs).completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace (K := coshGlobalThetaSobolev (F := F) a hα hs)

/-- Orthogonal projector onto `coshGlobalThetaSobolev`. -/
def coshGeometricProjection (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    CoshIntervalSobolev F α s →L[ℂ] CoshIntervalSobolev F α s :=
  (coshGlobalThetaSobolev (F := F) a hα hs).starProjection

/-- Orthogonal projector onto `(coshGlobalThetaSobolev)ᗮ`. -/
def coshSpectralProjection (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    CoshIntervalSobolev F α s →L[ℂ] CoshIntervalSobolev F α s :=
  (coshGlobalThetaSobolev (F := F) a hα hs).orthogonal.starProjection

variable (F) in
/-- Quotient Hilbert space `CoshIntervalSobolev F α s ⧸ coshGlobalThetaSobolev a hα hs`. -/
def coshSpectralQuotient (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) : Type _ :=
  CoshIntervalSobolev F α s ⧸ coshGlobalThetaSobolev (F := F) a hα hs

instance instNormedAddCommGroupCoshQuot (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    NormedAddCommGroup (coshSpectralQuotient F a hα hs) :=
  inferInstanceAs (NormedAddCommGroup (CoshIntervalSobolev F α s ⧸ coshGlobalThetaSobolev a hα hs))

instance instInnerProductSpaceCoshQuot (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    InnerProductSpace ℂ (coshSpectralQuotient F a hα hs) :=
  inferInstanceAs (InnerProductSpace ℂ (CoshIntervalSobolev F α s ⧸ coshGlobalThetaSobolev a hα hs))

instance instCompleteSpaceCoshQuot (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    CompleteSpace (coshSpectralQuotient F a hα hs) :=
  inferInstanceAs (CompleteSpace (CoshIntervalSobolev F α s ⧸ coshGlobalThetaSobolev a hα hs))

/-- Linear isometry equivalence between `coshSpectralQuotient` and the underlying submodule quotient. -/
def coshSpectralQuotientToQuot (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    coshSpectralQuotient F a hα hs ≃ₗᵢ[ℂ]
      (CoshIntervalSobolev F α s ⧸ coshGlobalThetaSobolev (F := F) a hα hs) :=
  LinearIsometryEquiv.refl ℂ _

/-- Canonical quotient map onto `coshSpectralQuotient F a hα hs`. -/
def coshQuotMk (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    CoshIntervalSobolev F α s →L[ℂ] coshSpectralQuotient F a hα hs :=
  (coshSpectralQuotientToQuot a hα hs).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (coshGlobalThetaSobolev (F := F) a hα hs).mkQL

lemma coshQuotMk_surjective (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    Surjective (coshQuotMk (F := F) a hα hs) := by
  intro q
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective (coshGlobalThetaSobolev a hα hs)
    (coshSpectralQuotientToQuot a hα hs q)
  exact ⟨u, rfl⟩

/-- Bounded linear isomorphism between `coshSpectralQuotient` and `spectralSobolevQuotient`. -/
def coshQuotientEquiv (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    coshSpectralQuotient F a hα hs ≃L[ℂ]
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs := by
  let E := coshIntervalEquiv (F := F) hα s
  let Θ₀ := globalThetaSobolev F a ((neg_nonpos.mpr hα).trans hα) hs
  let Θ_c := coshGlobalThetaSobolev (F := F) a hα hs
  let eQ := (coshSpectralQuotientToQuot (F := F) a hα hs).toContinuousLinearEquiv
  have h1 : Θ_c ≤ (Θ₀.mkQL.comp E.toContinuousLinearMap).ker := fun u hu ↦
    (Submodule.Quotient.mk_eq_zero Θ₀).mpr hu
  have h2 : Θ₀ ≤ (Θ_c.mkQL.comp E.symm.toContinuousLinearMap).ker := fun v hv ↦ by
    refine (Submodule.Quotient.mk_eq_zero Θ_c).mpr ?_
    change E (E.symm v) ∈ Θ₀
    rw [E.apply_symm_apply]
    exact hv
  let fwd : coshSpectralQuotient F a hα hs →L[ℂ]
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs :=
    (Θ_c.liftQL (Θ₀.mkQL.comp E.toContinuousLinearMap) h1).comp eQ.toContinuousLinearMap
  let bwd : spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs →L[ℂ]
      coshSpectralQuotient F a hα hs :=
    eQ.symm.toContinuousLinearMap.comp (Θ₀.liftQL (Θ_c.mkQL.comp E.symm.toContinuousLinearMap) h2)
  refine
    { fwd.toLinearMap with
      invFun := bwd
      left_inv := fun q ↦ by
        obtain ⟨u, rfl⟩ := coshQuotMk_surjective a hα hs q
        change bwd (fwd (eQ.symm (Θ_c.mkQL u))) = eQ.symm (Θ_c.mkQL u)
        dsimp only [fwd, bwd, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
        rw [eQ.apply_symm_apply, cosh_liftQL_mkQL, ContinuousLinearMap.comp_apply,
          cosh_liftQL_mkQL, ContinuousLinearMap.comp_apply]
        erw [E.symm_apply_apply]
      right_inv := fun q ↦ by
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective Θ₀ q
        change fwd (bwd (Θ₀.mkQL v)) = Θ₀.mkQL v
        dsimp only [fwd, bwd, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
        rw [cosh_liftQL_mkQL, ContinuousLinearMap.comp_apply, eQ.apply_symm_apply,
          cosh_liftQL_mkQL, ContinuousLinearMap.comp_apply]
        erw [E.apply_symm_apply]
      continuous_toFun := fwd.continuous
      continuous_invFun := bwd.continuous }

/-- Regularized compact test action on `CoshIntervalSobolev F α s`, conjugated from `hardySobolevTestAction`. -/
def coshTestAction {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽) :
    CoshIntervalSobolev F α s →L[ℂ] CoshIntervalSobolev F α s :=
  (coshIntervalEquiv hα s).symm.toContinuousLinearMap.comp
    ((hardySobolevTestAction μ𝔽 m𝔽 (-α) α s ((neg_nonpos.mpr hα).trans hα) hs φ).comp
      (coshIntervalEquiv hα s).toContinuousLinearMap)

lemma coshTestAction_isLinear {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    IsLinearMap ℂ (coshTestAction (F := F) hα hs) := by
  let hI := (neg_nonpos.mpr hα).trans hα
  let A := hardySobolevTestAction μ𝔽 m𝔽 (-α) α s hI hs
  let E := coshIntervalEquiv (F := F) hα s
  refine ⟨fun φ ψ ↦ ?_, fun c φ ↦ ?_⟩
  · ext1 u
    change E.symm ((A (φ + ψ)) (E u)) = E.symm ((A φ) (E u)) + E.symm ((A ψ) (E u))
    rw [A.map_add φ ψ]
    exact map_add E.symm ((A φ) (E u)) ((A ψ) (E u))
  · ext1 u
    change E.symm ((A (c • φ)) (E u)) = c • E.symm ((A φ) (E u))
    rw [A.map_smul c φ]
    exact map_smul E.symm c ((A φ) (E u))

lemma coshTestAction_apply {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽)
    (u : CoshIntervalSobolev F α s) :
    ((coshIntervalToLp F α s (coshTestAction (F := F) hα hs φ u) : Lp ℂ 2 (coshSobolevMeasure F α s)) : C𝔽 → ℂ) =ᵐ[μ𝔽]
      lcaConvolution μ𝔽 φ.val (coshIntervalToLp F α s u : Lp ℂ 2 (coshSobolevMeasure F α s)) := by
  have h1 := coshIntervalEquiv_symm_ae (F := F) hα s
    (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s ((neg_nonpos.mpr hα).trans hα) hs φ (coshIntervalEquiv hα s u))
  have h2 := hardySobolevTestAction_apply μ𝔽 m𝔽 (-α) α s ((neg_nonpos.mpr hα).trans hα) hs φ
    (coshIntervalEquiv hα s u)
  have h3 := coshIntervalEquiv_ae (F := F) hα s u
  have hconv : lcaConvolution μ𝔽 φ.val (coshIntervalEquiv hα s u) =ᵐ[μ𝔽]
      lcaConvolution μ𝔽 φ.val (coshIntervalToLp F α s u : Lp ℂ 2 (coshSobolevMeasure F α s)) := by
    refine ae_of_all _ fun g ↦ integral_congr_ae ?_
    have h_isHaar : (μ𝔽).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
    let mp : MeasurePreserving (fun y : C𝔽 ↦ y⁻¹ * g) μ𝔽 μ𝔽 :=
      (measurePreserving_mul_right μ𝔽 g).comp (Measure.measurePreserving_inv μ𝔽)
    filter_upwards [mp.quasiMeasurePreserving.ae h3] with y hy
    rw [hy]
  exact h1.trans (h2.trans hconv)

lemma coshTestAction_preserves_theta (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport C𝔽) :
    coshGlobalThetaSobolev (F := F) a hα hs ≤
      ((coshGlobalThetaSobolev (F := F) a hα hs).mkQL.comp
        (coshTestAction (F := F) hα hs φ)).ker := by
  intro u hu
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  change coshIntervalEquiv hα s (coshTestAction hα hs φ u) ∈
    globalThetaSobolev F a ((neg_nonpos.mpr hα).trans hα) hs
  dsimp only [coshTestAction, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [(coshIntervalEquiv hα s).apply_symm_apply]
  have hp := hardySobolevTestAction_preserves_globalTheta (F := F) a
    ((neg_nonpos.mpr hα).trans hα) hs φ hu
  exact (Submodule.Quotient.mk_eq_zero _).mp hp

/-- Descended convolution on `coshSpectralQuotient`. -/
def coshSpectralConvolution (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport C𝔽) :
    coshSpectralQuotient F a hα hs →L[ℂ] coshSpectralQuotient F a hα hs :=
  let eQ := (coshSpectralQuotientToQuot (F := F) a hα hs).toContinuousLinearEquiv
  eQ.symm.toContinuousLinearMap.comp
    (((coshGlobalThetaSobolev (F := F) a hα hs).liftQL
      ((coshGlobalThetaSobolev (F := F) a hα hs).mkQL.comp (coshTestAction hα hs φ))
      (coshTestAction_preserves_theta a hα hs φ)).comp eQ.toContinuousLinearMap)

lemma coshSpectralConvolution_apply_mk (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport C𝔽) (u : CoshIntervalSobolev F α s) :
    coshSpectralConvolution (F := F) a hα hs φ (coshQuotMk a hα hs u) =
      coshQuotMk a hα hs (coshTestAction hα hs φ u) := by
  dsimp only [coshSpectralConvolution, coshQuotMk]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  erw [(coshSpectralQuotientToQuot (F := F) a hα hs).apply_symm_apply]

lemma coshQuotientEquiv_apply_mk (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (u : CoshIntervalSobolev F α s) :
    coshQuotientEquiv (F := F) a hα hs (coshQuotMk a hα hs u) =
      (globalThetaSobolev F a ((neg_nonpos.mpr hα).trans hα) hs).mkQL
        (coshIntervalEquiv hα s u) := by
  dsimp only [coshQuotientEquiv, coshQuotMk, ContinuousLinearEquiv.coe_mk, LinearEquiv.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  erw [(coshSpectralQuotientToQuot (F := F) a hα hs).apply_symm_apply]
  exact cosh_liftQL_mkQL _ _ _ u

lemma coshSpectralConvolution_intertwines (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport C𝔽) :
    (coshQuotientEquiv (F := F) a hα hs).toContinuousLinearMap.comp
        (coshSpectralConvolution a hα hs φ) =
      (spectralConvolution (F := F) a ((neg_nonpos.mpr hα).trans hα) hs φ).comp
        (coshQuotientEquiv a hα hs).toContinuousLinearMap := by
  ext q
  obtain ⟨u, rfl⟩ := coshQuotMk_surjective a hα hs q
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, coshSpectralConvolution_apply_mk,
    coshQuotientEquiv_apply_mk, coshQuotientEquiv_apply_mk, Submodule.mkQL_apply,
    Submodule.mkQL_apply, spectralConvolution_mkQ]
  dsimp only [coshTestAction, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [(coshIntervalEquiv hα s).apply_symm_apply]
  rfl

/-- Key vanishing identity for the adjoint block: since `A_cosh ψ` leaves `Θ_cosh` invariant,
`(A_cosh ψ)†` leaves `Θ_coshᗮ` invariant, so `G_cosh ∘ (A_cosh ψ)† ∘ P_cosh = 0`. -/
theorem coshGeometricProjection_comp_adjoint_comp_spectral (a : ℝ) {α s : ℝ}
    (hα : 0 ≤ α) (hs : 0 ≤ s) (ψ : BruhatCompactSupport C𝔽) :
    (coshGeometricProjection (F := F) a hα hs).comp
      (((coshTestAction (F := F) hα hs ψ).adjoint).comp
        (coshSpectralProjection (F := F) a hα hs)) = 0 := by
  refine ContinuousLinearMap.ext fun u ↦ ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  change (coshGeometricProjection (F := F) a hα hs)
    (((coshTestAction (F := F) hα hs ψ).adjoint) ((coshSpectralProjection (F := F) a hα hs) u)) = 0
  refine (coshGlobalThetaSobolev (F := F) a hα hs).starProjection_apply_eq_zero_iff.mpr ?_
  intro θ hθ
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hmem : coshTestAction (F := F) hα hs ψ θ ∈ coshGlobalThetaSobolev (F := F) a hα hs :=
    (Submodule.Quotient.mk_eq_zero _).mp (coshTestAction_preserves_theta a hα hs ψ hθ)
  exact (Submodule.mem_orthogonal _ _).mp
    ((coshGlobalThetaSobolev a hα hs).orthogonal.starProjection_apply_mem u) _ hmem

end CoshOperatorsAndSubspaces

end RiemannMasullo.Isolated.CoshPositiveWidth
