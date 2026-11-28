module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_CoshDensity_Isolated
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec5

/-!
# Adjoint kernels, multipliers, and left translation on `CoshIntervalSobolev` (`#7406`)

1. `bruhatAdjoint`, `radialMul`, `bruhatLeftTranslate`, and `coshMulOp`.
2. `coshIntegralKernel_eLpNorm_le`, `norm_coshIntegralKernel_le`, and `coshTestAction_norm_le`.
3. `coshLeftTranslate`, its operator-norm bound, and `coshTestAction_bruhatLeftTranslate`.
4. `coshTestAction_sub_adjoint_eq_integral`: exact Haar integral formula for
   `A_cosh(ψ) - A_cosh(ψ*)†` on `CoshIntervalSobolev`.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set Topology
open scoped BigOperators ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo.Isolated.CoshPositiveWidth

section CoshKernelsAndTranslation

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => logIdeleClassNorm F

private lemma lintegral_coshSobolevMeasure {α s : ℝ} {f : C𝔽 → ℝ≥0∞}
    (hf : AEMeasurable f (coshSobolevMeasure F α s)) :
    ∫⁻ x : C𝔽, f x ∂(coshSobolevMeasure F α s) =
      ∫⁻ x : C𝔽, ENNReal.ofReal (coshSobolevDensity α s (logNorm x)) * f x ∂μ𝔽 := by
  rw [coshSobolevMeasure_eq_withDensity] at hf ⊢
  exact lintegral_withDensity_eq_lintegral_mul₀'
    ((continuous_coshSobolevDensity α s).measurable.comp measurable_logNorm).ennreal_ofReal.aemeasurable
    hf

private lemma integral_coshSobolevMeasure {α s : ℝ} (f : C𝔽 → ℂ) :
    ∫ x : C𝔽, f x ∂(coshSobolevMeasure F α s) =
      ∫ x : C𝔽, (coshSobolevDensity α s (logNorm x) : ℂ) * f x ∂μ𝔽 := by
  rw [coshSobolevMeasure_eq_withDensity]
  have h0 := integral_withDensity_eq_integral_toReal_smul (μ := μ𝔽) (g := f)
    ((continuous_coshSobolevDensity α s).measurable.comp measurable_logNorm).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)
  refine h0.trans (integral_congr_ae (ae_of_all _ fun x ↦ ?_))
  dsimp only [Function.comp_apply]
  rw [ENNReal.toReal_ofReal (coshSobolevDensity_pos α s _).le, Complex.real_smul]

private lemma eNorm_star_complex (z : ℂ) : ‖star z‖ₑ = ‖z‖ₑ := by
  rw [← ofReal_norm, norm_star, ofReal_norm]

private lemma eNorm_ofReal_nonneg {x : ℝ} (hx : 0 ≤ x) : ‖(x : ℂ)‖ₑ = ENNReal.ofReal x := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hx]

lemma isBruhatContDiff_conj_inv {G : Type*} [CommGroup G] [TopologicalSpace G]
    {f : G → ℂ} {p : ℕ} (h : IsBruhatContDiff p f) :
    IsBruhatContDiff p (fun x ↦ star (f x⁻¹)) := by
  obtain ⟨k, hk, hinv, hdesc⟩ := h
  refine ⟨k, hk, fun h x ↦ ?_, fun a ha ↦ ?_⟩
  · exact congrArg star (by simpa only [mul_inv_rev, Subgroup.coe_inv, mul_comm] using hinv h⁻¹ x⁻¹)
  · obtain ⟨f₀, hf₀, hd⟩ := hdesc a ha
    refine ⟨fun x ↦ star (f₀ x⁻¹), fun x ↦ ?_, fun e z b ↦ ?_⟩
    · exact congrArg star (hf₀ x⁻¹)
    · have hcov (t) : (e.equiv.symm (Multiplicative.ofAdd (elementaryCover t z b)))⁻¹ =
          e.equiv.symm (Multiplicative.ofAdd (elementaryCover (-t) (-z) (-b))) := by
        rw [← map_inv]
        apply congrArg e.equiv.symm
        apply congrArg Multiplicative.ofAdd
        exact Prod.ext rfl (Prod.ext (funext fun i ↦ (AddCircle.coe_neg (1 : ℝ)).symm) rfl)
      simp only [hcov]
      exact Complex.conjCLE.contDiff.comp ((hd e (-z) (-b)).comp contDiff_neg)

/-- Pointwise conjugate-inversion adjoint on `BruhatCompactSupport C𝔽`:
`(bruhatAdjoint φ).val g = star (φ.val g⁻¹)`. -/
def bruhatAdjoint (φ : BruhatCompactSupport C𝔽) : BruhatCompactSupport C𝔽 :=
  ⟨fun g ↦ star (φ.val g⁻¹),
    (mem_bruhatSmoothSubmodule_iff _).mpr fun p ↦
      isBruhatContDiff_conj_inv ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1 p),
    (φ.property.2.comp_homeomorph (Homeomorph.inv C𝔽)).comp_left (star_zero ℂ)⟩

@[simp]
lemma bruhatAdjoint_apply (φ : BruhatCompactSupport C𝔽) (g : C𝔽) :
    (bruhatAdjoint φ).val g = star (φ.val g⁻¹) := rfl

lemma tsupport_bruhatAdjoint_eq (φ : BruhatCompactSupport C𝔽) :
    tsupport (bruhatAdjoint φ).val = (· ⁻¹) '' tsupport φ.val := by
  ext g
  have himg : g ∈ (· ⁻¹) '' tsupport φ.val ↔ g⁻¹ ∈ tsupport φ.val :=
    ⟨by rintro ⟨y, hy, rfl⟩; simpa using hy, fun hg ↦ ⟨g⁻¹, hg, inv_inv g⟩⟩
  rw [himg, ← not_iff_not, notMem_tsupport_iff_eventuallyEq, notMem_tsupport_iff_eventuallyEq]
  constructor
  · intro hg
    have htend : Tendsto (fun x : C𝔽 ↦ x⁻¹) (𝓝 g⁻¹) (𝓝 g) := by
      simpa only [inv_inv] using continuous_inv.tendsto g⁻¹
    refine (hg.comp_tendsto htend).mono fun x hx ↦ ?_
    change star (φ.val x⁻¹⁻¹) = 0 at hx
    simpa [inv_inv] using congrArg star hx
  · intro hg
    refine (hg.comp_tendsto continuous_inv.continuousAt).mono fun x hx ↦ ?_
    change star (φ.val x⁻¹) = 0
    change φ.val x⁻¹ = 0 at hx
    simp [hx]

/-- Radial smooth cutoff/profile multiplication on `BruhatCompactSupport C𝔽`. -/
def radialMul (r : ℝ → ℂ) (hr : ContDiff ℝ (⊤ : ℕ∞) r) (φ : BruhatCompactSupport C𝔽) :
    BruhatCompactSupport C𝔽 :=
  ⟨fun g ↦ r (logNorm g) * φ.val g,
    (mem_bruhatSmoothSubmodule_iff _).mpr fun p ↦
      isBruhatContDiff_mul (isBruhatSmooth_logProfile m𝔽 hr p)
        ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1 p),
    φ.property.2.mul_left⟩

@[simp]
lemma radialMul_apply (r : ℝ → ℂ) (hr : ContDiff ℝ (⊤ : ℕ∞) r) (φ : BruhatCompactSupport C𝔽) (g : C𝔽) :
    (radialMul (F := F) r hr φ).val g = r (logNorm g) * φ.val g := rfl

lemma tsupport_radialMul_subset (r : ℝ → ℂ) (hr : ContDiff ℝ (⊤ : ℕ∞) r) (φ : BruhatCompactSupport C𝔽) :
    tsupport (radialMul (F := F) r hr φ).val ⊆ tsupport φ.val :=
  tsupport_mul_subset_right (f := fun g ↦ r (logNorm g)) (g := φ.val)

/-- Left translation on `BruhatCompactSupport C𝔽`: `(bruhatLeftTranslate h φ).val g = φ.val (h⁻¹ * g)`. -/
def bruhatLeftTranslate (h : C𝔽) (φ : BruhatCompactSupport C𝔽) : BruhatCompactSupport C𝔽 :=
  ⟨fun g ↦ φ.val (h⁻¹ * g), by
    obtain ⟨f', hf', _⟩ := bruhatFirstOrder_translate (1 : LCATopologicalLie C𝔽) ⟨φ.val, φ.property.1⟩ h
    have heq : (fun g ↦ φ.val (h⁻¹ * g)) = f'.val := funext fun g ↦ (hf' g).symm
    rw [heq]
    exact f'.property,
    φ.property.2.comp_homeomorph (Homeomorph.mulLeft h⁻¹)⟩

@[simp]
lemma bruhatLeftTranslate_apply (h : C𝔽) (φ : BruhatCompactSupport C𝔽) (g : C𝔽) :
    (bruhatLeftTranslate (F := F) h φ).val g = φ.val (h⁻¹ * g) := rfl

/-- Bounded measurable radial multiplication operator on `CoshIntervalSobolev F α s`. -/
def coshMulOp {α s : ℝ} (f : ℝ → ℂ) (hf_m : Measurable f) {M : ℝ} (hf_b : ∀ x, ‖f x‖ ≤ M) :
    CoshIntervalSobolev F α s →L[ℂ] CoshIntervalSobolev F α s :=
  let ν := coshSobolevMeasure F α s
  let M₀ := max M 0
  have hM₀ : 0 ≤ M₀ := le_max_right _ _
  have hs_m : AEStronglyMeasurable (fun g : C𝔽 ↦ f (logNorm g)) ν :=
    (hf_m.comp measurable_logNorm).aestronglyMeasurable
  have h_bound (u : CoshIntervalSobolev F α s) :
      eLpNorm (fun g : C𝔽 ↦ f (logNorm g) * u g) 2 ν ≤
        ENNReal.ofReal M₀ * eLpNorm (coshIntervalToLp F α s u : C𝔽 → ℂ) 2 ν := by
    let u₀ := coshIntervalToLp F α s u
    have hsm : AEStronglyMeasurable (fun g : C𝔽 ↦ f (logNorm g) * u g) ν :=
      hs_m.mul (Lp.aestronglyMeasurable u₀)
    calc eLpNorm (fun g ↦ f (logNorm g) * u g) 2 ν
        ≤ eLpNorm (fun g ↦ M₀ • u₀ g) 2 ν := by
          refine eLpNorm_mono hsm fun g ↦ ?_
          change ‖f (logNorm g) * u₀ g‖ ≤ ‖M₀ • u₀ g‖
          rw [norm_smul, Real.norm_of_nonneg hM₀, norm_mul]
          exact mul_le_mul_of_nonneg_right ((hf_b _).trans (le_max_left _ _)) (norm_nonneg _)
      _ ≤ ENNReal.ofReal M₀ * eLpNorm (u₀ : C𝔽 → ℂ) 2 ν := by
          refine (eLpNorm_const_smul_le (c := M₀) (f := (u₀ : C𝔽 → ℂ)) (p := 2) (μ := ν)).trans_eq ?_
          congr 1
          rw [← ofReal_norm, Real.norm_of_nonneg hM₀]
  have hmem (u : CoshIntervalSobolev F α s) : MemLp (fun g : C𝔽 ↦ f (logNorm g) * u g) 2 ν := by
    rw [memLp_iff]
    exact (h_bound u).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top _))
  LinearMap.mkContinuous
    { toFun := fun u ↦ (coshIntervalToLp F α s).symm ((hmem u).toLp _)
      map_add' := fun u v ↦ by
        refine CoshIntervalSobolev.ext ((coshSobolevMeasure_absCont α s).ae_le ?_)
        let u₀ := coshIntervalToLp F α s u
        let v₀ := coshIntervalToLp F α s v
        let w₀ := coshIntervalToLp F α s (u + v)
        let tu₀ := coshIntervalToLp F α s ((coshIntervalToLp F α s).symm ((hmem u).toLp _))
        let tv₀ := coshIntervalToLp F α s ((coshIntervalToLp F α s).symm ((hmem v).toLp _))
        let tw₀ := coshIntervalToLp F α s ((coshIntervalToLp F α s).symm ((hmem (u + v)).toLp _))
        have htw : tw₀ = (hmem (u + v)).toLp _ := (coshIntervalToLp F α s).apply_symm_apply _
        have htu : tu₀ = (hmem u).toLp _ := (coshIntervalToLp F α s).apply_symm_apply _
        have htv : tv₀ = (hmem v).toLp _ := (coshIntervalToLp F α s).apply_symm_apply _
        have hw0 : (w₀ : C𝔽 → ℂ) = (u₀ + v₀ : Lp ℂ 2 ν) := rfl
        filter_upwards [(tamagawa_absCont_coshSobolevMeasure α s).ae_le (hmem (u + v)).coeFn_toLp,
          (tamagawa_absCont_coshSobolevMeasure α s).ae_le (hmem u).coeFn_toLp,
          (tamagawa_absCont_coshSobolevMeasure α s).ae_le (hmem v).coeFn_toLp,
          (tamagawa_absCont_coshSobolevMeasure α s).ae_le (Lp.coeFn_add u₀ v₀),
          (tamagawa_absCont_coshSobolevMeasure α s).ae_le (Lp.coeFn_add tu₀ tv₀)]
          with g h0 hu hv hadd hpadd
        change tw₀ g = (tu₀ + tv₀) g
        rw [htw, h0, hpadd, Pi.add_apply, htu, htv, hu, hv]
        change f (logNorm g) * w₀ g = f (logNorm g) * u₀ g + f (logNorm g) * v₀ g
        rw [hw0, hadd, Pi.add_apply, mul_add]
      map_smul' := fun c u ↦ by
        refine CoshIntervalSobolev.ext ((coshSobolevMeasure_absCont α s).ae_le ?_)
        let u₀ := coshIntervalToLp F α s u
        let cu₀ := coshIntervalToLp F α s (c • u)
        let tu₀ := coshIntervalToLp F α s ((coshIntervalToLp F α s).symm ((hmem u).toLp _))
        let tcu₀ := coshIntervalToLp F α s ((coshIntervalToLp F α s).symm ((hmem (c • u)).toLp _))
        have htcu : tcu₀ = (hmem (c • u)).toLp _ := (coshIntervalToLp F α s).apply_symm_apply _
        have htu : tu₀ = (hmem u).toLp _ := (coshIntervalToLp F α s).apply_symm_apply _
        have hcu0 : (cu₀ : C𝔽 → ℂ) = (c • u₀ : Lp ℂ 2 ν) := rfl
        filter_upwards [(tamagawa_absCont_coshSobolevMeasure α s).ae_le (hmem (c • u)).coeFn_toLp,
          (tamagawa_absCont_coshSobolevMeasure α s).ae_le (hmem u).coeFn_toLp,
          (tamagawa_absCont_coshSobolevMeasure α s).ae_le (Lp.coeFn_smul c u₀),
          (tamagawa_absCont_coshSobolevMeasure α s).ae_le (Lp.coeFn_smul c tu₀)]
          with g h0 hu hsmul hpsmul
        change tcu₀ g = (c • tu₀) g
        rw [htcu, h0, hpsmul, Pi.smul_apply, smul_eq_mul, htu, hu]
        change f (logNorm g) * cu₀ g = c * (f (logNorm g) * u₀ g)
        rw [hcu0, hsmul, Pi.smul_apply, smul_eq_mul]
        ring }
    M₀ fun u ↦ by
      let u₀ := coshIntervalToLp F α s u
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      change ‖coshIntervalToLp F α s ((coshIntervalToLp F α s).symm ((hmem u).toLp _))‖ ≤ M₀ * ‖u₀‖
      rw [(coshIntervalToLp F α s).apply_symm_apply, Lp.norm_toLp, Lp.norm_def,
        ← ENNReal.toReal_ofReal hM₀, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top u₀)) (h_bound u)

lemma coshMulOp_apply {α s : ℝ} (f : ℝ → ℂ) (hf_m : Measurable f) {M : ℝ} (hf_b : ∀ x, ‖f x‖ ≤ M)
    (u : CoshIntervalSobolev F α s) :
    (coshMulOp (F := F) (α := α) (s := s) f hf_m hf_b u : C𝔽 → ℂ) =ᵐ[μ𝔽]
      fun g ↦ f (logNorm g) * u g := by
  dsimp only [coshMulOp, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  change (coshIntervalToLp F α s ((coshIntervalToLp F α s).symm (MemLp.toLp _ _)) : C𝔽 → ℂ) =ᵐ[μ𝔽] _
  rw [(coshIntervalToLp F α s).apply_symm_apply]
  exact (tamagawa_absCont_coshSobolevMeasure α s).ae_le (MemLp.coeFn_toLp _)

lemma norm_coshMulOp_le {α s : ℝ} (f : ℝ → ℂ) (hf_m : Measurable f) {M : ℝ} (hM : 0 ≤ M)
    (hf_b : ∀ x, ‖f x‖ ≤ M) :
    ‖coshMulOp (F := F) (α := α) (s := s) f hf_m hf_b‖ ≤ M := by
  dsimp only [coshMulOp]
  refine (LinearMap.mkContinuous_norm_le _ (le_max_right M 0) _).trans_eq (max_eq_left hM)

/-- Left translation operator on `CoshIntervalSobolev F α s`: `(T_h u)(g) = u(h⁻¹ * g)`. -/
def coshLeftTranslate {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (h : C𝔽) :
    CoshIntervalSobolev F α s →L[ℂ] CoshIntervalSobolev F α s :=
  let ν := coshSobolevMeasure F α s
  let δ := |logNorm h|
  let Csh : ℝ := Real.exp (2 * α * δ) * (1 + δ) ^ s
  have hCsh : 0 ≤ Csh := by positivity
  have h_isHaar : (μ𝔽).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have hlog_mul : ∀ a b : C𝔽, logNorm (a * b) = logNorm a + logNorm b := fun a b ↦ by
    change Real.log ((m𝔽 (a * b)).val : ℝ) = Real.log ((m𝔽 a).val : ℝ) + Real.log ((m𝔽 b).val : ℝ)
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.2 (m𝔽 a).ne_zero) (NNReal.coe_ne_zero.2 (m𝔽 b).ne_zero)]
  let wd : C𝔽 → ℝ≥0∞ := fun g ↦ ENNReal.ofReal (coshSobolevDensity α s (logNorm g))
  have h_eLp_le (u : CoshIntervalSobolev F α s) :
      eLpNorm (fun g : C𝔽 ↦ u (h⁻¹ * g)) 2 ν ≤
        ENNReal.ofReal (Real.sqrt Csh) * eLpNorm (coshIntervalToLp F α s u : C𝔽 → ℂ) 2 ν := by
    let u₀ := coshIntervalToLp F α s u
    have hu_ae : AEStronglyMeasurable (fun g : C𝔽 ↦ u (h⁻¹ * g)) ν :=
      ((Lp.stronglyMeasurable u₀).measurable.comp (measurable_const.mul measurable_id)).aestronglyMeasurable
    have hsq : eLpNorm (fun g : C𝔽 ↦ u (h⁻¹ * g)) 2 ν ^ 2 ≤
        ENNReal.ofReal Csh * eLpNorm (u₀ : C𝔽 → ℂ) 2 ν ^ 2 := by
      rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hu_ae,
        ENNReal.toReal_ofNat, ← ENNReal.rpow_two, ← ENNReal.rpow_mul,
        show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
        lintegral_coshSobolevMeasure (hu_ae.aemeasurable.eNorm.pow_const (2 : ℝ))]
      calc ∫⁻ g : C𝔽, wd g * ‖u (h⁻¹ * g)‖ₑ ^ (2 : ℝ) ∂μ𝔽
          = ∫⁻ x : C𝔽, wd (h * x) * ‖u x‖ₑ ^ (2 : ℝ) ∂μ𝔽 := by
            rw [← lintegral_mul_left_eq_self (μ := μ𝔽) _ h]
            refine lintegral_congr_ae (ae_of_all _ fun x ↦ by simp [inv_mul_cancel_left])
        _ ≤ ∫⁻ x : C𝔽, (ENNReal.ofReal Csh * wd x) * ‖u x‖ₑ ^ (2 : ℝ) ∂μ𝔽 := by
            refine lintegral_mono fun x ↦ ?_
            gcongr
            dsimp only [wd]
            rw [← ENNReal.ofReal_mul hCsh]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [hlog_mul]
            exact coshSobolevDensity_shift_le hα hs (logNorm h) (logNorm x)
        _ = ENNReal.ofReal Csh * eLpNorm (u₀ : C𝔽 → ℂ) 2 ν ^ 2 := by
            simp_rw [mul_assoc]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
            congr 1
            rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num)
              (Lp.aestronglyMeasurable u₀), ENNReal.toReal_ofNat, ← ENNReal.rpow_two,
              ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
              lintegral_coshSobolevMeasure ((Lp.aestronglyMeasurable u₀).aemeasurable.eNorm.pow_const (2 : ℝ))]
    have hr := ENNReal.rpow_le_rpow hsq (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.rpow_two (eLpNorm _ 2 ν), ← ENNReal.rpow_two (eLpNorm (u₀ : C𝔽 → ℂ) 2 ν),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
      ENNReal.rpow_one, ENNReal.rpow_one,
      ENNReal.ofReal_rpow_of_nonneg hCsh (by norm_num : (0 : ℝ) ≤ 1 / 2), ← Real.sqrt_eq_rpow] at hr
    exact hr
  have hmem (u : CoshIntervalSobolev F α s) : MemLp (fun g : C𝔽 ↦ u (h⁻¹ * g)) 2 ν := by
    rw [memLp_iff]
    exact (h_eLp_le u).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top _))
  LinearMap.mkContinuous
    { toFun := fun u ↦ (coshIntervalToLp F α s).symm ((hmem u).toLp _)
      map_add' := fun u v ↦ by
        refine CoshIntervalSobolev.ext (coshSobolevMeasure_absCont α s |>.ae_le ?_)
        let u₀ := coshIntervalToLp F α s u
        let v₀ := coshIntervalToLp F α s v
        let uv₀ := coshIntervalToLp F α s (u + v)
        let tu₀ := coshIntervalToLp F α s ((coshIntervalToLp F α s).symm ((hmem u).toLp _))
        let tv₀ := coshIntervalToLp F α s ((coshIntervalToLp F α s).symm ((hmem v).toLp _))
        let tuv₀ := coshIntervalToLp F α s ((coshIntervalToLp F α s).symm ((hmem (u + v)).toLp _))
        have htuv : tuv₀ = (hmem (u + v)).toLp _ := (coshIntervalToLp F α s).apply_symm_apply _
        have htu : tu₀ = (hmem u).toLp _ := (coshIntervalToLp F α s).apply_symm_apply _
        have htv : tv₀ = (hmem v).toLp _ := (coshIntervalToLp F α s).apply_symm_apply _
        have huv : (uv₀ : C𝔽 → ℂ) = (u₀ + v₀ : Lp ℂ 2 ν) := rfl
        let mp : MeasurePreserving (fun g : C𝔽 ↦ h⁻¹ * g) μ𝔽 μ𝔽 := measurePreserving_mul_left μ𝔽 h⁻¹
        have hadd := mp.quasiMeasurePreserving.ae ((tamagawa_absCont_coshSobolevMeasure α s).ae_le (Lp.coeFn_add u₀ v₀))
        filter_upwards [(tamagawa_absCont_coshSobolevMeasure α s).ae_le (hmem (u + v)).coeFn_toLp,
          (tamagawa_absCont_coshSobolevMeasure α s).ae_le (hmem u).coeFn_toLp,
          (tamagawa_absCont_coshSobolevMeasure α s).ae_le (hmem v).coeFn_toLp,
          (tamagawa_absCont_coshSobolevMeasure α s).ae_le (Lp.coeFn_add tu₀ tv₀),
          hadd] with g h0 hu hv hpa hgadd
        change tuv₀ g = (tu₀ + tv₀) g
        rw [htuv, h0, hpa, Pi.add_apply, htu, htv, hu, hv]
        change uv₀ (h⁻¹ * g) = u₀ (h⁻¹ * g) + v₀ (h⁻¹ * g)
        rw [huv, hgadd, Pi.add_apply]
      map_smul' := fun c u ↦ by
        refine CoshIntervalSobolev.ext (coshSobolevMeasure_absCont α s |>.ae_le ?_)
        let u₀ := coshIntervalToLp F α s u
        let cu₀ := coshIntervalToLp F α s (c • u)
        let tu₀ := coshIntervalToLp F α s ((coshIntervalToLp F α s).symm ((hmem u).toLp _))
        let tcu₀ := coshIntervalToLp F α s ((coshIntervalToLp F α s).symm ((hmem (c • u)).toLp _))
        have htcu : tcu₀ = (hmem (c • u)).toLp _ := (coshIntervalToLp F α s).apply_symm_apply _
        have htu : tu₀ = (hmem u).toLp _ := (coshIntervalToLp F α s).apply_symm_apply _
        have hcu : (cu₀ : C𝔽 → ℂ) = (c • u₀ : Lp ℂ 2 ν) := rfl
        let mp : MeasurePreserving (fun g : C𝔽 ↦ h⁻¹ * g) μ𝔽 μ𝔽 := measurePreserving_mul_left μ𝔽 h⁻¹
        have hsmul := mp.quasiMeasurePreserving.ae ((tamagawa_absCont_coshSobolevMeasure α s).ae_le (Lp.coeFn_smul c u₀))
        filter_upwards [(tamagawa_absCont_coshSobolevMeasure α s).ae_le (hmem (c • u)).coeFn_toLp,
          (tamagawa_absCont_coshSobolevMeasure α s).ae_le (hmem u).coeFn_toLp,
          (tamagawa_absCont_coshSobolevMeasure α s).ae_le (Lp.coeFn_smul c tu₀),
          hsmul] with g h0 hu hps hgsmul
        change tcu₀ g = (c • tu₀) g
        rw [htcu, h0, hps, Pi.smul_apply, htu, hu]
        change cu₀ (h⁻¹ * g) = c • u₀ (h⁻¹ * g)
        rw [hcu, hgsmul, Pi.smul_apply] }
    (Real.sqrt Csh) fun u ↦ by
      let u₀ := coshIntervalToLp F α s u
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      change ‖coshIntervalToLp F α s ((coshIntervalToLp F α s).symm ((hmem u).toLp _))‖ ≤ Real.sqrt Csh * ‖u₀‖
      rw [(coshIntervalToLp F α s).apply_symm_apply, Lp.norm_toLp, Lp.norm_def,
        ← ENNReal.toReal_ofReal (Real.sqrt_nonneg Csh), ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top u₀)) (h_eLp_le u)

lemma coshLeftTranslate_apply {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (h : C𝔽)
    (u : CoshIntervalSobolev F α s) :
    (coshLeftTranslate (F := F) hα hs h u : C𝔽 → ℂ) =ᵐ[μ𝔽] fun g ↦ u (h⁻¹ * g) := by
  dsimp only [coshLeftTranslate, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  change (coshIntervalToLp F α s ((coshIntervalToLp F α s).symm (MemLp.toLp _ _)) : C𝔽 → ℂ) =ᵐ[μ𝔽] _
  rw [(coshIntervalToLp F α s).apply_symm_apply]
  exact (tamagawa_absCont_coshSobolevMeasure α s).ae_le (MemLp.coeFn_toLp _)

lemma norm_coshLeftTranslate_le {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (h : C𝔽) :
    ‖coshLeftTranslate (F := F) hα hs h‖ ≤
      Real.sqrt (Real.exp (2 * α * |logNorm h|) * (1 + |logNorm h|) ^ s) := by
  dsimp only [coshLeftTranslate]
  exact LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _

/-- Left-translated Bruhat convolution factors cleanly through `coshLeftTranslate`. -/
lemma coshTestAction_bruhatLeftTranslate {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (h : C𝔽)
    (φ : BruhatCompactSupport C𝔽) :
    coshTestAction (F := F) hα hs (bruhatLeftTranslate h φ) =
      (coshLeftTranslate hα hs h).comp (coshTestAction hα hs φ) := by
  have h_isHaar : (μ𝔽).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  ext1 u
  refine CoshIntervalSobolev.ext ((coshSobolevMeasure_absCont α s).ae_le ?_)
  have h1 := coshTestAction_apply (F := F) hα hs (bruhatLeftTranslate h φ) u
  have h2 := coshLeftTranslate_apply (F := F) hα hs h (coshTestAction hα hs φ u)
  let mp : MeasurePreserving (fun g : C𝔽 ↦ h⁻¹ * g) μ𝔽 μ𝔽 := measurePreserving_mul_left μ𝔽 h⁻¹
  have h3 := mp.quasiMeasurePreserving.ae (coshTestAction_apply (F := F) hα hs φ u)
  filter_upwards [h1, h2, h3] with g hg1 hg2 hg3
  change (coshTestAction hα hs (bruhatLeftTranslate h φ) u : C𝔽 → ℂ) g =
    ((coshLeftTranslate hα hs h) (coshTestAction hα hs φ u) : C𝔽 → ℂ) g
  rw [hg1, hg2, hg3]
  change ∫ y : C𝔽, φ.val (h⁻¹ * y) * u (y⁻¹ * g) ∂μ𝔽 = ∫ z : C𝔽, φ.val z * u (z⁻¹ * (h⁻¹ * g)) ∂μ𝔽
  rw [← integral_mul_left_eq_self (μ := μ𝔽) (fun y : C𝔽 ↦ φ.val (h⁻¹ * y) * u (y⁻¹ * g)) h]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  simp only [inv_mul_cancel_left, mul_inv_rev, mul_assoc]

/-- Cauchy-Schwarz + Fubini-Tonelli operator norm bound on `CoshIntervalSobolev F α s` for any
convolution operator with kernel `ψ(y) * K(logNorm g, logNorm y)` where `supp(ψ) ⊆ {|logNorm| ≤ δ}`
and `|K(x, t)| ≤ ε` when `|t| ≤ δ`. -/
private lemma coshIntegralKernel_eLpNorm_le {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (ψ : BruhatCompactSupport C𝔽) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hsupp : ∀ y, ψ.val y ≠ 0 → |logNorm y| ≤ δ)
    (K : ℝ → ℝ → ℂ) (hKm : Measurable (uncurry K)) (hKb : ∀ x t, |t| ≤ δ → ‖K x t‖ ≤ ε)
    (u_c : CoshIntervalSobolev F α s) :
    eLpNorm (fun g : C𝔽 ↦ ∫ y : C𝔽, ψ.val y * K (logNorm g) (logNorm y) * u_c (y⁻¹ * g) ∂μ𝔽) 2
        (coshSobolevMeasure F α s) ≤
      ENNReal.ofReal (ε * Real.sqrt (Real.exp (2 * α * δ) * (1 + δ) ^ s) * ∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽) *
        eLpNorm (u_c : C𝔽 → ℂ) 2 (coshSobolevMeasure F α s) := by
  let u := coshIntervalToLp F α s u_c
  have h_isHaar : (μ𝔽).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have : SFinite μ𝔽 := inferInstance
  have hψ_cont : Continuous ψ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp ψ.property.1)
  let L₁ : ℝ := ∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽
  have hL₁ : 0 ≤ L₁ := integral_nonneg fun _ ↦ norm_nonneg _
  have hL₁_enn : (∫⁻ y : C𝔽, ‖ψ.val y‖ₑ ∂μ𝔽) = ENNReal.ofReal L₁ :=
    (ofReal_integral_norm_eq_lintegral_eNorm (hψ_cont.integrable_of_hasCompactSupport ψ.property.2)).symm
  let Csh : ℝ := Real.exp (2 * α * δ) * (1 + δ) ^ s
  have hCsh : 0 ≤ Csh := by positivity
  let ν := coshSobolevMeasure F α s
  let wd : C𝔽 → ℝ≥0∞ := fun g ↦ ENNReal.ofReal (coshSobolevDensity α s (logNorm g))
  have hwd_m : Measurable wd :=
    ((continuous_coshSobolevDensity α s).measurable.comp measurable_logNorm).ennreal_ofReal
  have hu_sm := Lp.stronglyMeasurable u
  have hraw_ae : AEStronglyMeasurable
      (fun g : C𝔽 ↦ ∫ y : C𝔽, ψ.val y * K (logNorm g) (logNorm y) * u_c (y⁻¹ * g) ∂μ𝔽) ν :=
    (((hψ_cont.measurable.comp measurable_snd).mul
      (hKm.comp ((measurable_logNorm.comp measurable_fst).prodMk
        (measurable_logNorm.comp measurable_snd)))).mul
      (hu_sm.measurable.comp (measurable_snd.inv.mul measurable_fst))).aestronglyMeasurable.integral_prod_right'
  have hpt (g : C𝔽) :
      ‖∫ y : C𝔽, ψ.val y * K (logNorm g) (logNorm y) * u (y⁻¹ * g) ∂μ𝔽‖ₑ ^ 2 ≤
        ENNReal.ofReal (ε ^ 2 * L₁) * ∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ 2 ∂μ𝔽 := by
    have h1 : ‖∫ y : C𝔽, ψ.val y * K (logNorm g) (logNorm y) * u (y⁻¹ * g) ∂μ𝔽‖ₑ ≤
        ENNReal.ofReal ε *
          ∫⁻ y : C𝔽, (‖ψ.val y‖ₑ ^ (1 / 2 : ℝ)) * (‖ψ.val y‖ₑ ^ (1 / 2 : ℝ) * ‖u (y⁻¹ * g)‖ₑ) ∂μ𝔽 := by
      refine (eNorm_integral_le_lintegral_eNorm _).trans ?_
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
      refine lintegral_mono fun y ↦ ?_
      by_cases hψ0 : ψ.val y = 0
      · simp [hψ0]
      · have hky : ‖K (logNorm g) (logNorm y)‖ₑ ≤ ENNReal.ofReal ε := by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hKb _ _ (hsupp y hψ0))
        calc ‖ψ.val y * K (logNorm g) (logNorm y) * u (y⁻¹ * g)‖ₑ
            = ‖ψ.val y‖ₑ * ‖K (logNorm g) (logNorm y)‖ₑ * ‖u (y⁻¹ * g)‖ₑ := by simp [eNorm_mul]
          _ ≤ ‖ψ.val y‖ₑ * ENNReal.ofReal ε * ‖u (y⁻¹ * g)‖ₑ := by gcongr
          _ = ENNReal.ofReal ε * (‖ψ.val y‖ₑ ^ (1 / 2 : ℝ) * (‖ψ.val y‖ₑ ^ (1 / 2 : ℝ) * ‖u (y⁻¹ * g)‖ₑ)) := by
              have hhalf : ‖ψ.val y‖ₑ ^ (1 / 2 : ℝ) * ‖ψ.val y‖ₑ ^ (1 / 2 : ℝ) = ‖ψ.val y‖ₑ := by
                rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num),
                  show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, ENNReal.rpow_one]
              calc ‖ψ.val y‖ₑ * ENNReal.ofReal ε * ‖u (y⁻¹ * g)‖ₑ
                  = ENNReal.ofReal ε * (‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ) := by ring
                _ = ENNReal.ofReal ε * (‖ψ.val y‖ₑ ^ (1 / 2 : ℝ) * ‖ψ.val y‖ₑ ^ (1 / 2 : ℝ) * ‖u (y⁻¹ * g)‖ₑ) := by
                    rw [hhalf]
                _ = ENNReal.ofReal ε * (‖ψ.val y‖ₑ ^ (1 / 2 : ℝ) * (‖ψ.val y‖ₑ ^ (1 / 2 : ℝ) * ‖u (y⁻¹ * g)‖ₑ)) := by
                    rw [mul_assoc]
    have hm1 : AEMeasurable (fun y : C𝔽 ↦ ‖ψ.val y‖ₑ ^ (1 / 2 : ℝ)) μ𝔽 :=
      (hψ_cont.measurable.eNorm.pow_const _).aemeasurable
    have hm2 : AEMeasurable (fun y : C𝔽 ↦ ‖ψ.val y‖ₑ ^ (1 / 2 : ℝ) * ‖u (y⁻¹ * g)‖ₑ) μ𝔽 :=
      hm1.mul ((hu_sm.measurable.comp (measurable_inv.mul measurable_const)).eNorm).aemeasurable
    have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq μ𝔽 (by constructor <;> norm_num : (2 : ℝ).HolderConjugate 2) hm1 hm2
    have hcs2 : (∫⁻ y : C𝔽, (‖ψ.val y‖ₑ ^ (1 / 2 : ℝ)) * (‖ψ.val y‖ₑ ^ (1 / 2 : ℝ) * ‖u (y⁻¹ * g)‖ₑ) ∂μ𝔽) ^ 2 ≤
        (∫⁻ y : C𝔽, ‖ψ.val y‖ₑ ∂μ𝔽) * ∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ 2 ∂μ𝔽 := by
      have hsq := ENNReal.rpow_le_rpow hcs zero_le_two
      nth_rw 1 [ENNReal.rpow_two] at hsq
      rw [ENNReal.mul_rpow_of_nonneg _ _ zero_le_two,
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
        ENNReal.rpow_one, ENNReal.rpow_one] at hsq
      refine hsq.trans_eq ?_
      congr 1
      · refine lintegral_congr_ae (ae_of_all _ fun y ↦ ?_)
        dsimp only
        rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
      · refine lintegral_congr_ae (ae_of_all _ fun y ↦ ?_)
        dsimp only
        rw [ENNReal.mul_rpow_of_nonneg _ _ zero_le_two, ← ENNReal.rpow_mul,
          show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_two]
    calc ‖∫ y : C𝔽, ψ.val y * K (logNorm g) (logNorm y) * u (y⁻¹ * g) ∂μ𝔽‖ₑ ^ 2
        ≤ (ENNReal.ofReal ε * ∫⁻ y : C𝔽, (‖ψ.val y‖ₑ ^ (1 / 2 : ℝ)) *
            (‖ψ.val y‖ₑ ^ (1 / 2 : ℝ) * ‖u (y⁻¹ * g)‖ₑ) ∂μ𝔽) ^ 2 :=
          pow_le_pow_left' h1 2
      _ = ENNReal.ofReal ε ^ 2 * _ ^ 2 := by rw [mul_pow]
      _ ≤ ENNReal.ofReal ε ^ 2 * ((∫⁻ y : C𝔽, ‖ψ.val y‖ₑ ∂μ𝔽) *
            ∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ 2 ∂μ𝔽) :=
          mul_le_mul_of_nonneg_left hcs2 (by positivity)
      _ = ENNReal.ofReal (ε ^ 2 * L₁) * ∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ 2 ∂μ𝔽 := by
          rw [hL₁_enn, ← mul_assoc, ← ENNReal.ofReal_pow hε, ← ENNReal.ofReal_mul (sq_nonneg _)]
  have heLp_le : eLpNorm (fun g : C𝔽 ↦ ∫ y : C𝔽, ψ.val y * K (logNorm g) (logNorm y) * u (y⁻¹ * g) ∂μ𝔽) 2 ν ^ 2 ≤
      ENNReal.ofReal ((ε * Real.sqrt Csh * L₁) ^ 2) * eLpNorm (u : C𝔽 → ℂ) 2 ν ^ 2 := by
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hraw_ae,
      ENNReal.toReal_ofNat, ← ENNReal.rpow_two, ← ENNReal.rpow_mul,
      show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
      lintegral_coshSobolevMeasure (hraw_ae.aemeasurable.eNorm.pow_const (2 : ℝ))]
    simp_rw [ENNReal.rpow_two]
    calc ∫⁻ g : C𝔽, wd g * ‖∫ y : C𝔽, ψ.val y * K (logNorm g) (logNorm y) * u (y⁻¹ * g) ∂μ𝔽‖ₑ ^ 2 ∂μ𝔽
        ≤ ∫⁻ g : C𝔽, wd g * (ENNReal.ofReal (ε ^ 2 * L₁) *
            ∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ 2 ∂μ𝔽) ∂μ𝔽 := by
          refine lintegral_mono fun g ↦ mul_le_mul_of_nonneg_left (hpt g) (by positivity)
      _ = ENNReal.ofReal (ε ^ 2 * L₁) *
            ∫⁻ g : C𝔽, ∫⁻ y : C𝔽, wd g * (‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ 2) ∂μ𝔽 ∂μ𝔽 := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
          refine lintegral_congr_ae (ae_of_all _ fun g ↦ ?_)
          dsimp only
          rw [mul_left_comm (wd g)]
          congr 1
          exact (lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne).symm
      _ = ENNReal.ofReal (ε ^ 2 * L₁) *
            ∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * ∫⁻ g : C𝔽, wd g * ‖u (y⁻¹ * g)‖ₑ ^ 2 ∂μ𝔽 ∂μ𝔽 := by
          congr 1
          have hm_joint : AEMeasurable (fun p : C𝔽 × C𝔽 ↦ wd p.1 * (‖ψ.val p.2‖ₑ * ‖u (p.2⁻¹ * p.1)‖ₑ ^ 2))
              ((μ𝔽).prod μ𝔽) :=
            ((hwd_m.comp measurable_fst).mul ((hψ_cont.measurable.eNorm.comp measurable_snd).mul
              (((hu_sm.measurable.comp (measurable_snd.inv.mul measurable_fst)).eNorm).pow_const 2))).aemeasurable
          rw [lintegral_lintegral_swap hm_joint]
          refine lintegral_congr_ae (ae_of_all _ fun y ↦ ?_)
          simp_rw [mul_left_comm (wd _)]
          exact lintegral_const_mul' (‖ψ.val y‖ₑ) _ eNorm_lt_top.ne
      _ ≤ ENNReal.ofReal (ε ^ 2 * L₁) *
            ∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * (ENNReal.ofReal Csh * eLpNorm (u : C𝔽 → ℂ) 2 ν ^ 2) ∂μ𝔽 := by
          refine mul_le_mul_of_nonneg_left (lintegral_mono fun y ↦ ?_) (by positivity)
          by_cases hψ0 : ψ.val y = 0
          · simp [hψ0]
          · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hshift_y : ∀ x : C𝔽, wd (y * x) ≤ ENNReal.ofReal Csh * wd x := fun x ↦ by
              dsimp only [wd]
              rw [← ENNReal.ofReal_mul hCsh]
              refine ENNReal.ofReal_le_ofReal ?_
              have hlog_m : logNorm (y * x) = logNorm y + logNorm x := by
                change Real.log ((m𝔽 (y * x)).val : ℝ) = Real.log ((m𝔽 y).val : ℝ) + Real.log ((m𝔽 x).val : ℝ)
                rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
                  (NNReal.coe_ne_zero.2 (m𝔽 y).ne_zero) (NNReal.coe_ne_zero.2 (m𝔽 x).ne_zero)]
              rw [hlog_m]
              refine (coshSobolevDensity_shift_le hα hs (logNorm y) (logNorm x)).trans ?_
              refine mul_le_mul_of_nonneg_right ?_ (coshSobolevDensity_pos α s _).le
              have hyδ : |logNorm y| ≤ δ := hsupp y hψ0
              exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hyδ (by linarith)))
                (Real.rpow_le_rpow (by positivity) (by linarith) hs) (by positivity) (by positivity)
            calc ∫⁻ g : C𝔽, wd g * ‖u (y⁻¹ * g)‖ₑ ^ 2 ∂μ𝔽
                = ∫⁻ x : C𝔽, wd (y * x) * ‖u (y⁻¹ * (y * x))‖ₑ ^ 2 ∂μ𝔽 :=
                  (lintegral_mul_left_eq_self (μ := μ𝔽) (fun g ↦ wd g * ‖u (y⁻¹ * g)‖ₑ ^ 2) y).symm
              _ = ∫⁻ x : C𝔽, wd (y * x) * ‖u x‖ₑ ^ 2 ∂μ𝔽 := by simp [inv_mul_cancel_left]
              _ ≤ ∫⁻ x : C𝔽, (ENNReal.ofReal Csh * wd x) * ‖u x‖ₑ ^ 2 ∂μ𝔽 := by
                  refine lintegral_mono fun x ↦ ?_; gcongr; exact hshift_y x
              _ = ENNReal.ofReal Csh * ∫⁻ x : C𝔽, wd x * ‖u x‖ₑ ^ 2 ∂μ𝔽 := by
                  simp_rw [mul_assoc]
                  exact lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne
              _ = ENNReal.ofReal Csh * eLpNorm (u : C𝔽 → ℂ) 2 ν ^ 2 := by
                  congr 1
                  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num)
                    (Lp.aestronglyMeasurable u), ENNReal.toReal_ofNat, ← ENNReal.rpow_two,
                    ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
                    lintegral_coshSobolevMeasure ((Lp.aestronglyMeasurable u).aemeasurable.eNorm.pow_const (2 : ℝ))]
                  simp_rw [ENNReal.rpow_two]
                  rfl
      _ = ENNReal.ofReal ((ε * Real.sqrt Csh * L₁) ^ 2) * eLpNorm (u : C𝔽 → ℂ) 2 ν ^ 2 := by
          rw [lintegral_mul_const _ hψ_cont.measurable.eNorm, hL₁_enn,
            show (ε * Real.sqrt Csh * L₁) ^ 2 = ε ^ 2 * L₁ * (L₁ * Csh) by
              rw [mul_pow, mul_pow, Real.sq_sqrt hCsh]; ring,
            ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hL₁), ENNReal.ofReal_mul hL₁]
          ring
  have hr := ENNReal.rpow_le_rpow heLp_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.rpow_two (eLpNorm _ 2 ν), ← ENNReal.rpow_two (eLpNorm (u : C𝔽 → ℂ) 2 ν),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
    ENNReal.rpow_one, ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)] at hr
  exact hr

/-- Cauchy-Schwarz + Fubini-Tonelli operator norm bound on `CoshIntervalSobolev F α s`. -/
lemma norm_coshIntegralKernel_le {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (ψ : BruhatCompactSupport C𝔽) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hsupp : ∀ y, ψ.val y ≠ 0 → |logNorm y| ≤ δ)
    (K : ℝ → ℝ → ℂ) (hKm : Measurable (uncurry K)) (hKb : ∀ x t, |t| ≤ δ → ‖K x t‖ ≤ ε)
    (T : CoshIntervalSobolev F α s →L[ℂ] CoshIntervalSobolev F α s)
    (hT : ∀ u, (T u : C𝔽 → ℂ) =ᵐ[μ𝔽] fun g ↦ ∫ y : C𝔽, ψ.val y * K (logNorm g) (logNorm y) * u (y⁻¹ * g) ∂μ𝔽) :
    ‖T‖ ≤ ε * Real.sqrt (Real.exp (2 * α * δ) * (1 + δ) ^ s) * ∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  let u₀ := coshIntervalToLp F α s u
  let Tu₀ := coshIntervalToLp F α s (T u)
  have he := coshIntegralKernel_eLpNorm_le hα hs ψ hδ hε hsupp K hKm hKb u
  rw [← eLpNorm_congr_ae ((coshSobolevMeasure_absCont α s).ae_le (hT u))] at he
  change ‖Tu₀‖ ≤ _ * ‖u₀‖
  rw [Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_ofReal (by positivity :
      0 ≤ ε * Real.sqrt (Real.exp (2 * α * δ) * (1 + δ) ^ s) * ∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽),
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top u₀)) he

/-- Operator-norm bound for `coshTestAction` on compactly supported tests in `{|logNorm| ≤ δ}`. -/
lemma coshTestAction_norm_le {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (ψ : BruhatCompactSupport C𝔽) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsupp : ∀ y, ψ.val y ≠ 0 → |logNorm y| ≤ δ) :
    ‖coshTestAction (F := F) hα hs ψ‖ ≤
      Real.sqrt (Real.exp (2 * α * δ) * (1 + δ) ^ s) * ∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽 := by
  have h := norm_coshIntegralKernel_le (F := F) hα hs ψ hδ zero_le_one hsupp
    (fun _ _ ↦ 1) measurable_const (fun _ _ _ ↦ by simp) (coshTestAction hα hs ψ)
    fun u ↦ (coshTestAction_apply hα hs ψ u).mono fun g hg ↦ by simpa [lcaConvolution] using hg
  simpa using h

/-- Exact Haar integral representation of `coshTestAction ψ - (coshTestAction (bruhatAdjoint ψ))†`
on `CoshIntervalSobolev F α s`. -/
lemma coshTestAction_sub_adjoint_eq_integral {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (ψ : BruhatCompactSupport C𝔽) (u_c : CoshIntervalSobolev F α s) :
    ((coshTestAction (F := F) hα hs ψ - (coshTestAction hα hs (bruhatAdjoint ψ)).adjoint) u_c : C𝔽 → ℂ) =ᵐ[μ𝔽]
      fun g ↦ ∫ y : C𝔽, ψ.val y *
        ((1 - coshSobolevDensity α s (logNorm g - logNorm y) / coshSobolevDensity α s (logNorm g) : ℝ) : ℂ) *
          u_c (y⁻¹ * g) ∂μ𝔽 := by
  let u := coshIntervalToLp F α s u_c
  have h_isHaar : (μ𝔽).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have : SFinite μ𝔽 := inferInstance
  have hψ_cont : Continuous ψ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp ψ.property.1)
  obtain ⟨C, hC⟩ := ψ.property.2.exists_bound_of_continuousOn continuous_logNorm.continuousOn
  let δ : ℝ := max 0 C
  have hδ : 0 ≤ δ := le_max_left _ _
  have hsupp : ∀ y, ψ.val y ≠ 0 → |logNorm y| ≤ δ := fun y hy ↦ by
    have h := hC y (subset_tsupport _ hy)
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_right _ _)
  let K_adj : ℝ → ℝ → ℂ := fun x t ↦ ((coshSobolevDensity α s (x - t) / coshSobolevDensity α s x : ℝ) : ℂ)
  have hK_cont : Continuous (uncurry K_adj) :=
    Complex.continuous_ofReal.comp
      (((continuous_coshSobolevDensity α s).comp (continuous_fst.sub continuous_snd)).div
        ((continuous_coshSobolevDensity α s).comp continuous_fst) fun p ↦ (coshSobolevDensity_pos α s _).ne')
  let Csh : ℝ := Real.exp (2 * α * δ) * (1 + δ) ^ s
  have hKb : ∀ x t, |t| ≤ δ → ‖K_adj x t‖ ≤ Csh := fun x t ht ↦ by
    rw [Complex.norm_real, Real.norm_of_nonneg (div_pos (coshSobolevDensity_pos α s _)
      (coshSobolevDensity_pos α s _)).le, div_le_iff₀ (coshSobolevDensity_pos α s _)]
    have hs1 : coshSobolevDensity α s (-t + x) ≤
        Real.exp (2 * α * |-t|) * (1 + |-t|) ^ s * coshSobolevDensity α s x :=
      coshSobolevDensity_shift_le hα hs (-t) x
    rw [neg_add_eq_sub, abs_neg] at hs1
    refine hs1.trans (mul_le_mul_of_nonneg_right ?_ (coshSobolevDensity_pos α s _).le)
    exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht (by linarith)))
      (Real.rpow_le_rpow (by positivity) (by linarith) hs) (by positivity) (by positivity)
  let adjRaw : C𝔽 → ℂ := fun g ↦ ∫ y : C𝔽, ψ.val y * K_adj (logNorm g) (logNorm y) * u (y⁻¹ * g) ∂μ𝔽
  have hadj_mem : MemLp adjRaw 2 (coshSobolevMeasure F α s) := by
    rw [memLp_iff]
    exact (coshIntegralKernel_eLpNorm_le hα hs ψ hδ (by positivity) hsupp K_adj hK_cont.measurable
      hKb u_c).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top u))
  let ν := coshSobolevMeasure F α s
  let wd : C𝔽 → ℝ≥0∞ := fun g ↦ ENNReal.ofReal (coshSobolevDensity α s (logNorm g))
  have hwd_m : Measurable wd :=
    ((continuous_coshSobolevDensity α s).measurable.comp measurable_logNorm).ennreal_ofReal
  have hCsh : 0 ≤ Csh := by positivity
  have hu_sm := Lp.stronglyMeasurable u
  have hlog_mul : ∀ a b : C𝔽, logNorm (a * b) = logNorm a + logNorm b := fun a b ↦ by
    change Real.log ((m𝔽 (a * b)).val : ℝ) = Real.log ((m𝔽 a).val : ℝ) + Real.log ((m𝔽 b).val : ℝ)
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.2 (m𝔽 a).ne_zero) (NNReal.coe_ne_zero.2 (m𝔽 b).ne_zero)]
  have hlog_inv : ∀ a : C𝔽, logNorm a⁻¹ = -logNorm a := fun a ↦ by
    change Real.log ((m𝔽 a⁻¹).val : ℝ) = -Real.log ((m𝔽 a).val : ℝ)
    rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv]
  have hshift_le_Csh : ∀ y x : C𝔽, |logNorm y| ≤ δ → wd (y * x) ≤ ENNReal.ofReal Csh * wd x := fun y x hy ↦ by
    dsimp only [wd]
    rw [← ENNReal.ofReal_mul hCsh]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hlog_mul]
    refine (coshSobolevDensity_shift_le hα hs (logNorm y) (logNorm x)).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (coshSobolevDensity_pos α s _).le
    exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy (by linarith)))
      (Real.rpow_le_rpow (by positivity) (by linarith) hs) (by positivity) (by positivity)
  have hae_int_u : ∀ᵐ g ∂μ𝔽, Integrable (fun y : C𝔽 ↦ ψ.val y * u (y⁻¹ * g)) μ𝔽 := by
    let L₁ : ℝ := ∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽
    have hL₁_enn : (∫⁻ y : C𝔽, ‖ψ.val y‖ₑ ∂μ𝔽) = ENNReal.ofReal L₁ :=
      (ofReal_integral_norm_eq_lintegral_eNorm (hψ_cont.integrable_of_hasCompactSupport ψ.property.2)).symm
    have hfin_tot : ∫⁻ g : C𝔽, wd g * (∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ∂μ𝔽) ^ 2 ∂μ𝔽 < ⊤ := by
      let νψ : Measure C𝔽 := (μ𝔽).withDensity (fun y ↦ ‖ψ.val y‖ₑ)
      have hpt : ∀ g : C𝔽, (∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ∂μ𝔽) ^ 2 ≤
          ENNReal.ofReal L₁ * ∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ 2 ∂μ𝔽 := fun g ↦ by
        have h1 : ∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ∂μ𝔽 = ∫⁻ y : C𝔽, ‖u (y⁻¹ * g)‖ₑ ∂νψ :=
          (lintegral_withDensity_eq_lintegral_mul _ hψ_cont.measurable.eNorm
            (hu_sm.measurable.comp (measurable_inv.mul measurable_const)).eNorm).symm
        have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq νψ (by constructor <;> norm_num : (2 : ℝ).HolderConjugate 2)
          (f := fun _ ↦ (1 : ℝ≥0∞)) (g := fun y ↦ ‖u (y⁻¹ * g)‖ₑ) measurable_const.aemeasurable
          (((hu_sm.measurable.comp (measurable_inv.mul measurable_const)).eNorm).aemeasurable)
        have hholder' : ∫⁻ y : C𝔽, ‖u (y⁻¹ * g)‖ₑ ∂νψ ≤
            νψ Set.univ ^ (1 / 2 : ℝ) * (∫⁻ y : C𝔽, ‖u (y⁻¹ * g)‖ₑ ^ (2 : ℝ) ∂νψ) ^ (1 / 2 : ℝ) := by
          have hm : (fun y : C𝔽 ↦ ‖u (y⁻¹ * g)‖ₑ) = ((fun _ : C𝔽 ↦ (1 : ℝ≥0∞)) * fun y ↦ ‖u (y⁻¹ * g)‖ₑ) := by
            ext y; simp
          calc ∫⁻ y : C𝔽, ‖u (y⁻¹ * g)‖ₑ ∂νψ
              = ∫⁻ y : C𝔽, ((fun _ : C𝔽 ↦ (1 : ℝ≥0∞)) * fun y ↦ ‖u (y⁻¹ * g)‖ₑ) y ∂νψ := by rw [← hm]
            _ ≤ (∫⁻ y : C𝔽, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂νψ) ^ (1 / 2 : ℝ) *
                  (∫⁻ y : C𝔽, ‖u (y⁻¹ * g)‖ₑ ^ (2 : ℝ) ∂νψ) ^ (1 / 2 : ℝ) := by
                simpa only [one_div] using hholder
            _ = νψ Set.univ ^ (1 / 2 : ℝ) * (∫⁻ y : C𝔽, ‖u (y⁻¹ * g)‖ₑ ^ (2 : ℝ) ∂νψ) ^ (1 / 2 : ℝ) := by
                simp
        have hνψ_univ : νψ Set.univ = ENNReal.ofReal L₁ := by
          rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]; exact hL₁_enn
        have hrhs : (∫⁻ y : C𝔽, ‖u (y⁻¹ * g)‖ₑ ^ (2 : ℝ) ∂νψ) =
            ∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ 2 ∂μ𝔽 := by
          refine (lintegral_withDensity_eq_lintegral_mul _ hψ_cont.measurable.eNorm
            (((hu_sm.measurable.comp (measurable_inv.mul measurable_const)).eNorm).pow_const (2 : ℝ))).trans ?_
          refine lintegral_congr_ae (ae_of_all _ fun y ↦ ?_)
          change ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ (2 : ℝ) = ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ 2
          rw [ENNReal.rpow_two]
        rw [← h1, hνψ_univ, hrhs] at hholder'
        have hsq := ENNReal.rpow_le_rpow hholder' (by norm_num : (0 : ℝ) ≤ 2)
        rw [ENNReal.rpow_two, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
          ENNReal.rpow_one, ENNReal.rpow_one] at hsq
        exact hsq
      calc ∫⁻ g : C𝔽, wd g * (∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ∂μ𝔽) ^ 2 ∂μ𝔽
          ≤ ∫⁻ g : C𝔽, wd g * (ENNReal.ofReal L₁ * ∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ 2 ∂μ𝔽) ∂μ𝔽 := by
            refine lintegral_mono fun g ↦ mul_le_mul_of_nonneg_left (hpt g) (by positivity)
        _ = ENNReal.ofReal L₁ * ∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * ∫⁻ g : C𝔽, wd g * ‖u (y⁻¹ * g)‖ₑ ^ 2 ∂μ𝔽 ∂μ𝔽 := by
            have hswap : (∫⁻ g : C𝔽, wd g * (ENNReal.ofReal L₁ * ∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ 2 ∂μ𝔽) ∂μ𝔽) =
                ENNReal.ofReal L₁ * ∫⁻ g : C𝔽, ∫⁻ y : C𝔽, wd g * (‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ^ 2) ∂μ𝔽 ∂μ𝔽 := by
              rw [← lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
              refine lintegral_congr_ae (ae_of_all _ fun g ↦ ?_)
              dsimp only
              rw [mul_left_comm (wd g)]
              congr 1
              exact (lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne).symm
            rw [hswap]
            congr 1
            rw [lintegral_lintegral_swap (((hwd_m.comp measurable_fst).mul
              ((hψ_cont.measurable.eNorm.comp measurable_snd).mul
                (((hu_sm.measurable.comp (measurable_snd.inv.mul measurable_fst)).eNorm).pow_const 2))).aemeasurable)]
            refine lintegral_congr_ae (ae_of_all _ fun y ↦ ?_)
            simp_rw [mul_left_comm (wd _)]
            exact lintegral_const_mul' (‖ψ.val y‖ₑ) _ eNorm_lt_top.ne
        _ ≤ ENNReal.ofReal L₁ * ∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * (ENNReal.ofReal Csh * eLpNorm (u : C𝔽 → ℂ) 2 ν ^ 2) ∂μ𝔽 := by
            refine mul_le_mul_of_nonneg_left (lintegral_mono fun y ↦ ?_) (by positivity)
            by_cases hy : ψ.val y = 0
            · simp [hy]
            · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              calc ∫⁻ g : C𝔽, wd g * ‖u (y⁻¹ * g)‖ₑ ^ 2 ∂μ𝔽
                  = ∫⁻ x : C𝔽, wd (y * x) * ‖u x‖ₑ ^ 2 ∂μ𝔽 := by
                    rw [← lintegral_mul_left_eq_self (μ := μ𝔽) _ y]
                    refine lintegral_congr_ae (ae_of_all _ fun x ↦ by simp [inv_mul_cancel_left])
                _ ≤ ∫⁻ x : C𝔽, (ENNReal.ofReal Csh * wd x) * ‖u x‖ₑ ^ 2 ∂μ𝔽 := by
                    refine lintegral_mono fun x ↦ ?_; gcongr; exact hshift_le_Csh y x (hsupp y hy)
                _ = ENNReal.ofReal Csh * eLpNorm (u : C𝔽 → ℂ) 2 ν ^ 2 := by
                    simp_rw [mul_assoc]
                    rw [lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
                    congr 1
                    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num)
                      (Lp.aestronglyMeasurable u), ENNReal.toReal_ofNat, ← ENNReal.rpow_two,
                      ← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
                      lintegral_coshSobolevMeasure ((Lp.aestronglyMeasurable u).aemeasurable.eNorm.pow_const (2 : ℝ))]
                    simp_rw [ENNReal.rpow_two]
                    rfl
        _ < ⊤ := by
            rw [lintegral_mul_const _ hψ_cont.measurable.eNorm, hL₁_enn]
            exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
              (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
                (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top (Lp.eLpNorm_lt_top u))))
    have hm_inner : Measurable (fun g : C𝔽 ↦ ∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ∂μ𝔽) :=
      ((hψ_cont.measurable.eNorm.comp measurable_snd).mul
        (hu_sm.measurable.comp (measurable_snd.inv.mul measurable_fst)).eNorm).lintegral_prod_right'
    filter_upwards [ae_lt_top (hwd_m.mul (hm_inner.pow_const 2)) hfin_tot.ne] with g hg
    have h_ne_top : (∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * ‖u (y⁻¹ * g)‖ₑ ∂μ𝔽) < ⊤ := by
      by_contra htop
      rw [not_lt, top_le_iff] at htop
      have hwd_pos : wd g ≠ 0 := (ENNReal.ofReal_pos.mpr (coshSobolevDensity_pos α s _)).ne'
      simp [htop, hwd_pos] at hg
    refine ⟨(hψ_cont.measurable.mul (hu_sm.measurable.comp (measurable_inv.mul measurable_const))).aestronglyMeasurable, ?_⟩
    simpa only [HasFiniteIntegral, eNorm_mul] using h_ne_top
  have hae_int_adj : ∀ᵐ g ∂μ𝔽, Integrable (fun y : C𝔽 ↦ ψ.val y * K_adj (logNorm g) (logNorm y) * u (y⁻¹ * g)) μ𝔽 := by
    filter_upwards [hae_int_u] with g hg
    refine Integrable.mono' (hg.norm.const_mul Csh)
      (((hψ_cont.measurable.mul (hK_cont.measurable.comp
        (measurable_const.prodMk measurable_logNorm))).mul
          (hu_sm.measurable.comp (measurable_inv.mul measurable_const))).aestronglyMeasurable)
      (ae_of_all _ fun y ↦ ?_)
    by_cases hy : ψ.val y = 0
    · simp [hy]
    · rw [norm_mul, norm_mul]
      calc ‖ψ.val y‖ * ‖K_adj (logNorm g) (logNorm y)‖ * ‖u (y⁻¹ * g)‖
          ≤ ‖ψ.val y‖ * Csh * ‖u (y⁻¹ * g)‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hKb _ _ (hsupp y hy)) (norm_nonneg _)) (norm_nonneg _)
        _ = Csh * ‖ψ.val y * u (y⁻¹ * g)‖ := by rw [norm_mul]; ring
  have hadj_eq : (coshTestAction (F := F) hα hs (bruhatAdjoint ψ)).adjoint u_c =
      (coshIntervalToLp F α s).symm (hadj_mem.toLp adjRaw) := by
    refine ext_inner_right ℂ fun v_c ↦ ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    let v := coshIntervalToLp F α s v_c
    have h1 := coshTestAction_apply hα hs (bruhatAdjoint ψ) v_c
    have hv_sm := Lp.stronglyMeasurable v
    have hcs_shift : ∀ (a : C𝔽 → ℂ) (b : C𝔽 → ℂ) (ha : AEStronglyMeasurable a ν) (hb : AEStronglyMeasurable b ν)
        (y : C𝔽) (_hy : |logNorm y| ≤ δ),
        ∫⁻ x : C𝔽, ‖a x‖ₑ * ‖b (y⁻¹ * x)‖ₑ * wd x ∂μ𝔽 ≤
          ENNReal.ofReal (Real.sqrt Csh) * (eLpNorm a 2 ν * eLpNorm b 2 ν) := fun a b ha hb y hy ↦ by
      have ha_eq : eLpNorm a 2 ν = (∫⁻ x : C𝔽, ‖a x‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) := by
        rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) ha, ENNReal.toReal_ofNat, one_div]
      have hb_eq : eLpNorm b 2 ν = (∫⁻ x : C𝔽, ‖b x‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) := by
        rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hb, ENNReal.toReal_ofNat, one_div]
      have hb_shift : AEMeasurable (fun x ↦ ‖b (y⁻¹ * x)‖ₑ) ν :=
        (((hb.aemeasurable.mono_ac (tamagawa_absCont_coshSobolevMeasure (F := F) α s)).comp_quasiMeasurePreserving
          (measurePreserving_mul_left μ𝔽 y⁻¹).quasiMeasurePreserving).mono_ac
          (coshSobolevMeasure_absCont α s)).eNorm
      have hν_eq : ∫⁻ x : C𝔽, ‖a x‖ₑ * ‖b (y⁻¹ * x)‖ₑ * wd x ∂μ𝔽 =
          ∫⁻ x : C𝔽, ‖a x‖ₑ * ‖b (y⁻¹ * x)‖ₑ ∂ν := by
        rw [lintegral_coshSobolevMeasure (f := fun x ↦ ‖a x‖ₑ * ‖b (y⁻¹ * x)‖ₑ) (ha.aemeasurable.eNorm.mul hb_shift)]
        refine lintegral_congr_ae (ae_of_all _ fun x ↦ by ring)
      have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq ν (by constructor <;> norm_num : (2 : ℝ).HolderConjugate 2)
        (f := fun x ↦ ‖a x‖ₑ) (g := fun x ↦ ‖b (y⁻¹ * x)‖ₑ) ha.aemeasurable.eNorm hb_shift
      have hb_norm : (∫⁻ x : C𝔽, ‖b (y⁻¹ * x)‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (Real.sqrt Csh) * eLpNorm b 2 ν := by
        have hstep : ∫⁻ x : C𝔽, ‖b (y⁻¹ * x)‖ₑ ^ (2 : ℝ) ∂ν ≤
            ENNReal.ofReal Csh * ∫⁻ g : C𝔽, ‖b g‖ₑ ^ (2 : ℝ) ∂ν := by
          rw [lintegral_coshSobolevMeasure (hb_shift.pow_const (2 : ℝ)),
            lintegral_coshSobolevMeasure (hb.aemeasurable.eNorm.pow_const (2 : ℝ))]
          calc ∫⁻ x : C𝔽, wd x * ‖b (y⁻¹ * x)‖ₑ ^ (2 : ℝ) ∂μ𝔽
              = ∫⁻ g : C𝔽, wd (y * g) * ‖b g‖ₑ ^ (2 : ℝ) ∂μ𝔽 := by
                rw [← lintegral_mul_left_eq_self (μ := μ𝔽) _ y]
                refine lintegral_congr_ae (ae_of_all _ fun g ↦ by simp [inv_mul_cancel_left])
            _ ≤ ∫⁻ g : C𝔽, (ENNReal.ofReal Csh * wd g) * ‖b g‖ₑ ^ (2 : ℝ) ∂μ𝔽 := by
                refine lintegral_mono fun g ↦ ?_; gcongr; exact hshift_le_Csh y g hy
            _ = ENNReal.ofReal Csh * ∫⁻ g : C𝔽, wd g * ‖b g‖ₑ ^ (2 : ℝ) ∂μ𝔽 := by
                simp_rw [mul_assoc]
                exact lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne
        refine (ENNReal.rpow_le_rpow hstep (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ENNReal.ofReal_rpow_of_nonneg hCsh (by norm_num : (0 : ℝ) ≤ 1 / 2), ← Real.sqrt_eq_rpow, hb_eq]
      rw [hν_eq, ha_eq, one_div]
      calc ∫⁻ x : C𝔽, (fun x ↦ ‖a x‖ₑ * ‖b (y⁻¹ * x)‖ₑ) x ∂ν
          ≤ (∫⁻ x : C𝔽, ‖a x‖ₑ ^ (2 : ℝ) ∂ν) ^ (2 : ℝ)⁻¹ *
              (∫⁻ x : C𝔽, ‖b (y⁻¹ * x)‖ₑ ^ (2 : ℝ) ∂ν) ^ (2 : ℝ)⁻¹ := by
            simpa only [Pi.mul_apply, one_div] using hholder
        _ ≤ (∫⁻ x : C𝔽, ‖a x‖ₑ ^ (2 : ℝ) ∂ν) ^ (2 : ℝ)⁻¹ * (ENNReal.ofReal (Real.sqrt Csh) * eLpNorm b 2 ν) := by
            gcongr; simpa only [one_div] using hb_norm
        _ = ENNReal.ofReal (Real.sqrt Csh) * ((∫⁻ x : C𝔽, ‖a x‖ₑ ^ (2 : ℝ) ∂ν) ^ (2 : ℝ)⁻¹ * eLpNorm b 2 ν) := by
            ring
    have heq_inner1 : @inner ℂ (CoshIntervalSobolev F α s) _ u_c (coshTestAction hα hs (bruhatAdjoint ψ) v_c) =
        ∫ x : C𝔽, star (u x) * (∫ z : C𝔽, star (ψ.val z⁻¹) * v (z⁻¹ * x) ∂μ𝔽) *
          (coshSobolevDensity α s (logNorm x) : ℂ) ∂μ𝔽 := by
      change @inner ℂ (Lp ℂ 2 (coshSobolevMeasure F α s)) _ u
        (coshIntervalToLp F α s (coshTestAction hα hs (bruhatAdjoint ψ) v_c)) = _
      rw [L2.inner_def, integral_coshSobolevMeasure]
      refine integral_congr_ae ?_
      filter_upwards [h1] with x hx
      have hbadj (z : C𝔽) : (bruhatAdjoint (F := F) ψ).val z = star (ψ.val z⁻¹) := bruhatAdjoint_apply ψ z
      have hx' : (coshIntervalToLp F α s (coshTestAction hα hs (bruhatAdjoint ψ) v_c) : C𝔽 → ℂ) x =
          ∫ z : C𝔽, star (ψ.val z⁻¹) * v (z⁻¹ * x) ∂μ𝔽 := by
        refine hx.trans ?_
        rw [lcaConvolution]
        refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
        change (bruhatAdjoint (F := F) ψ).val z * (coshIntervalToLp F α s v_c : C𝔽 → ℂ) (z⁻¹ * x) = _
        rw [hbadj]
      rw [hx', RCLike.inner_apply, Complex.star_def]
      ring
    have hint_joint : Integrable (fun p : C𝔽 × C𝔽 ↦
        star (u p.2) * star (ψ.val p.1⁻¹) * v (p.1⁻¹ * p.2) * (coshSobolevDensity α s (logNorm p.2) : ℂ))
        ((μ𝔽).prod μ𝔽) := by
      have hm : AEStronglyMeasurable (fun p : C𝔽 × C𝔽 ↦
          star (u p.2) * star (ψ.val p.1⁻¹) * v (p.1⁻¹ * p.2) * (coshSobolevDensity α s (logNorm p.2) : ℂ))
          ((μ𝔽).prod μ𝔽) :=
        ((((continuous_star.measurable.comp (hu_sm.measurable.comp measurable_snd)).mul
          (continuous_star.comp hψ_cont |>.comp continuous_inv |>.measurable.comp measurable_fst)).mul
          (hv_sm.measurable.comp (measurable_fst.inv.mul measurable_snd))).mul
          (Complex.continuous_ofReal.comp (continuous_coshSobolevDensity α s) |>.comp continuous_logNorm |>.measurable.comp measurable_snd)).aestronglyMeasurable
      refine ⟨hm, ?_⟩
      change (∫⁻ p : C𝔽 × C𝔽, _ ∂((μ𝔽).prod μ𝔽)) < ⊤
      rw [lintegral_prod _ hm.eNorm]
      have hbadj_supp (z : C𝔽) (hz : ψ.val z⁻¹ ≠ 0) : |logNorm z| ≤ δ := by
        simpa [hlog_inv, abs_neg] using hsupp z⁻¹ hz
      have hψ_inv_int : (∫⁻ z : C𝔽, ‖ψ.val z⁻¹‖ₑ ∂μ𝔽) = ENNReal.ofReal (∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽) := by
        rw [lintegral_inv_eq_self (μ := μ𝔽) (fun z : C𝔽 ↦ ‖ψ.val z‖ₑ),
          ofReal_integral_norm_eq_lintegral_eNorm (hψ_cont.integrable_of_hasCompactSupport ψ.property.2)]
      calc ∫⁻ z : C𝔽, ∫⁻ x : C𝔽, ‖star (u x) * star (ψ.val z⁻¹) * v (z⁻¹ * x) *
            (coshSobolevDensity α s (logNorm x) : ℂ)‖ₑ ∂μ𝔽 ∂μ𝔽
          ≤ ∫⁻ z : C𝔽, ‖ψ.val z⁻¹‖ₑ * (ENNReal.ofReal (Real.sqrt Csh) *
              (eLpNorm (u : C𝔽 → ℂ) 2 ν * eLpNorm (v : C𝔽 → ℂ) 2 ν)) ∂μ𝔽 := by
            refine lintegral_mono fun z ↦ ?_
            by_cases hz : ψ.val z⁻¹ = 0
            · simp [hz]
            · have heq_en : ∫⁻ x : C𝔽, ‖star (u x) * star (ψ.val z⁻¹) * v (z⁻¹ * x) *
                  (coshSobolevDensity α s (logNorm x) : ℂ)‖ₑ ∂μ𝔽 =
                  ‖ψ.val z⁻¹‖ₑ * ∫⁻ x : C𝔽, ‖u x‖ₑ * ‖v (z⁻¹ * x)‖ₑ * wd x ∂μ𝔽 := by
                simp_rw [eNorm_mul, eNorm_star_complex, eNorm_ofReal_nonneg (coshSobolevDensity_pos α s _).le]
                change ∫⁻ x : C𝔽, ‖u x‖ₑ * ‖ψ.val z⁻¹‖ₑ * ‖v (z⁻¹ * x)‖ₑ * wd x ∂μ𝔽 = _
                have hrw : ∀ x : C𝔽, ‖u x‖ₑ * ‖ψ.val z⁻¹‖ₑ * ‖v (z⁻¹ * x)‖ₑ * wd x =
                    ‖ψ.val z⁻¹‖ₑ * (‖u x‖ₑ * ‖v (z⁻¹ * x)‖ₑ * wd x) := fun x ↦ by ring
                simp_rw [hrw]
                exact lintegral_const_mul' (‖ψ.val z⁻¹‖ₑ) _ eNorm_lt_top.ne
              rw [heq_en]
              gcongr
              exact hcs_shift (u : C𝔽 → ℂ) (v : C𝔽 → ℂ)
                hu_sm.aestronglyMeasurable hv_sm.aestronglyMeasurable z (hbadj_supp z hz)
        _ = ENNReal.ofReal (∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽) *
              (ENNReal.ofReal (Real.sqrt Csh) * (eLpNorm (u : C𝔽 → ℂ) 2 ν * eLpNorm (v : C𝔽 → ℂ) 2 ν)) := by
            rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_lt_top.ne
              (ENNReal.mul_ne_top (Lp.eLpNorm_lt_top u).ne (Lp.eLpNorm_lt_top v).ne)), hψ_inv_int]
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
              (ENNReal.mul_lt_top (Lp.eLpNorm_lt_top u) (Lp.eLpNorm_lt_top v)))
    have hint_joint_adj : Integrable (fun p : C𝔽 × C𝔽 ↦
        star (u (p.1⁻¹ * p.2)) * star (ψ.val p.1) * v p.2 * (coshSobolevDensity α s (logNorm (p.1⁻¹ * p.2)) : ℂ))
        ((μ𝔽).prod μ𝔽) := by
      have hm : AEStronglyMeasurable (fun p : C𝔽 × C𝔽 ↦
          star (u (p.1⁻¹ * p.2)) * star (ψ.val p.1) * v p.2 * (coshSobolevDensity α s (logNorm (p.1⁻¹ * p.2)) : ℂ))
          ((μ𝔽).prod μ𝔽) :=
        ((((continuous_star.measurable.comp (hu_sm.measurable.comp (measurable_fst.inv.mul measurable_snd))).mul
          (continuous_star.comp hψ_cont |>.measurable.comp measurable_fst)).mul
          (hv_sm.measurable.comp measurable_snd)).mul
          (Complex.continuous_ofReal.comp (continuous_coshSobolevDensity α s) |>.comp continuous_logNorm |>.measurable.comp
            (measurable_fst.inv.mul measurable_snd))).aestronglyMeasurable
      refine ⟨hm, ?_⟩
      change (∫⁻ p : C𝔽 × C𝔽, _ ∂((μ𝔽).prod μ𝔽)) < ⊤
      rw [lintegral_prod _ hm.eNorm]
      have hψ_int : (∫⁻ y : C𝔽, ‖ψ.val y‖ₑ ∂μ𝔽) = ENNReal.ofReal (∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽) :=
        (ofReal_integral_norm_eq_lintegral_eNorm (hψ_cont.integrable_of_hasCompactSupport ψ.property.2)).symm
      calc ∫⁻ y : C𝔽, ∫⁻ g : C𝔽, ‖star (u (y⁻¹ * g)) * star (ψ.val y) * v g *
            (coshSobolevDensity α s (logNorm (y⁻¹ * g)) : ℂ)‖ₑ ∂μ𝔽 ∂μ𝔽
          ≤ ∫⁻ y : C𝔽, ‖ψ.val y‖ₑ * (ENNReal.ofReal Csh *
              (ENNReal.ofReal (Real.sqrt Csh) * (eLpNorm (u : C𝔽 → ℂ) 2 ν * eLpNorm (v : C𝔽 → ℂ) 2 ν))) ∂μ𝔽 := by
            refine lintegral_mono fun y ↦ ?_
            by_cases hy : ψ.val y = 0
            · simp [hy]
            · have hyδ : |logNorm y| ≤ δ := hsupp y hy
              have hle_y : ∫⁻ g : C𝔽, ‖star (u (y⁻¹ * g)) * star (ψ.val y) * v g *
                    (coshSobolevDensity α s (logNorm (y⁻¹ * g)) : ℂ)‖ₑ ∂μ𝔽 ≤
                    ‖ψ.val y‖ₑ * (ENNReal.ofReal Csh * ∫⁻ g : C𝔽, ‖u (y⁻¹ * g)‖ₑ * ‖v g‖ₑ * wd g ∂μ𝔽) := by
                have h_pt_g (g : C𝔽) : ‖star (u (y⁻¹ * g)) * star (ψ.val y) * v g *
                      (coshSobolevDensity α s (logNorm (y⁻¹ * g)) : ℂ)‖ₑ ≤
                      ‖ψ.val y‖ₑ * (ENNReal.ofReal Csh * (‖u (y⁻¹ * g)‖ₑ * ‖v g‖ₑ * wd g)) := by
                  simp only [eNorm_mul, eNorm_star_complex, eNorm_ofReal_nonneg (coshSobolevDensity_pos α s _).le]
                  have hw_inv : wd (y⁻¹ * g) ≤ ENNReal.ofReal Csh * wd g :=
                    hshift_le_Csh y⁻¹ g (by simpa [hlog_inv, abs_neg] using hyδ)
                  calc ‖u (y⁻¹ * g)‖ₑ * ‖ψ.val y‖ₑ * ‖v g‖ₑ * wd (y⁻¹ * g)
                      = ‖ψ.val y‖ₑ * (‖u (y⁻¹ * g)‖ₑ * ‖v g‖ₑ * wd (y⁻¹ * g)) := by ring
                    _ ≤ ‖ψ.val y‖ₑ * (‖u (y⁻¹ * g)‖ₑ * ‖v g‖ₑ * (ENNReal.ofReal Csh * wd g)) := by gcongr
                    _ = ‖ψ.val y‖ₑ * (ENNReal.ofReal Csh * (‖u (y⁻¹ * g)‖ₑ * ‖v g‖ₑ * wd g)) := by ring
                calc ∫⁻ g : C𝔽, ‖star (u (y⁻¹ * g)) * star (ψ.val y) * v g *
                      (coshSobolevDensity α s (logNorm (y⁻¹ * g)) : ℂ)‖ₑ ∂μ𝔽
                    ≤ ∫⁻ g : C𝔽, ‖ψ.val y‖ₑ * (ENNReal.ofReal Csh * (‖u (y⁻¹ * g)‖ₑ * ‖v g‖ₑ * wd g)) ∂μ𝔽 :=
                      lintegral_mono h_pt_g
                  _ = ‖ψ.val y‖ₑ * (ENNReal.ofReal Csh * ∫⁻ g : C𝔽, ‖u (y⁻¹ * g)‖ₑ * ‖v g‖ₑ * wd g ∂μ𝔽) := by
                      rw [lintegral_const_mul' (‖ψ.val y‖ₑ) _ eNorm_lt_top.ne,
                        lintegral_const_mul' (ENNReal.ofReal Csh) _ ENNReal.ofReal_lt_top.ne]
              refine hle_y.trans ?_
              refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
              have heq_cs := hcs_shift (v : C𝔽 → ℂ) (u : C𝔽 → ℂ)
                hv_sm.aestronglyMeasurable hu_sm.aestronglyMeasurable y hyδ
              rw [mul_comm (eLpNorm (v : C𝔽 → ℂ) 2 ν)] at heq_cs
              refine le_trans ?_ heq_cs
              have h_comm : ∫⁻ g : C𝔽, ‖u (y⁻¹ * g)‖ₑ * ‖v g‖ₑ * wd g ∂μ𝔽 =
                  ∫⁻ g : C𝔽, ‖v g‖ₑ * ‖u (y⁻¹ * g)‖ₑ * wd g ∂μ𝔽 :=
                lintegral_congr_ae (ae_of_all _ fun g ↦ by ring)
              rw [h_comm]
        _ = ENNReal.ofReal (∫ y : C𝔽, ‖ψ.val y‖ ∂μ𝔽) *
              (ENNReal.ofReal Csh * (ENNReal.ofReal (Real.sqrt Csh) *
                (eLpNorm (u : C𝔽 → ℂ) 2 ν * eLpNorm (v : C𝔽 → ℂ) 2 ν))) := by
            rw [lintegral_mul_const _ hψ_cont.measurable.eNorm, hψ_int]
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
              (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
                (ENNReal.mul_lt_top (Lp.eLpNorm_lt_top u) (Lp.eLpNorm_lt_top v))))
    have heq_inner2 : @inner ℂ (CoshIntervalSobolev F α s) _
          ((coshIntervalToLp F α s).symm (hadj_mem.toLp adjRaw)) v_c =
        ∫ g : C𝔽, star (adjRaw g) * v g * (coshSobolevDensity α s (logNorm g) : ℂ) ∂μ𝔽 := by
      change @inner ℂ (Lp ℂ 2 (coshSobolevMeasure F α s)) _
        (coshIntervalToLp F α s ((coshIntervalToLp F α s).symm (hadj_mem.toLp adjRaw))) v = _
      rw [(coshIntervalToLp F α s).apply_symm_apply, L2.inner_def, integral_coshSobolevMeasure]
      refine integral_congr_ae ?_
      filter_upwards [(tamagawa_absCont_coshSobolevMeasure (F := F) α s).ae_le hadj_mem.coeFn_toLp] with g hg
      rw [hg, RCLike.inner_apply, Complex.star_def]
      ring
    have heq_swap : ∫ x : C𝔽, star (u x) * (∫ z : C𝔽, star (ψ.val z⁻¹) * v (z⁻¹ * x) ∂μ𝔽) *
          (coshSobolevDensity α s (logNorm x) : ℂ) ∂μ𝔽 =
        ∫ g : C𝔽, star (adjRaw g) * v g * (coshSobolevDensity α s (logNorm g) : ℂ) ∂μ𝔽 := by
      calc ∫ x : C𝔽, star (u x) * (∫ z : C𝔽, star (ψ.val z⁻¹) * v (z⁻¹ * x) ∂μ𝔽) *
            (coshSobolevDensity α s (logNorm x) : ℂ) ∂μ𝔽
          = ∫ x : C𝔽, ∫ z : C𝔽, star (u x) * star (ψ.val z⁻¹) * v (z⁻¹ * x) *
              (coshSobolevDensity α s (logNorm x) : ℂ) ∂μ𝔽 ∂μ𝔽 := by
            refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
            dsimp only
            rw [mul_assoc (star (u x)), ← integral_mul_const, ← integral_const_mul]
            refine integral_congr_ae (ae_of_all _ fun z ↦ by ring)
        _ = ∫ z : C𝔽, ∫ x : C𝔽, star (u x) * star (ψ.val z⁻¹) * v (z⁻¹ * x) *
              (coshSobolevDensity α s (logNorm x) : ℂ) ∂μ𝔽 ∂μ𝔽 :=
            (integral_integral_swap hint_joint).symm
        _ = ∫ y : C𝔽, ∫ x : C𝔽, star (u x) * star (ψ.val y) * v (y * x) *
              (coshSobolevDensity α s (logNorm x) : ℂ) ∂μ𝔽 ∂μ𝔽 := by
            rw [← integral_inv_eq_self (μ := μ𝔽)
              (fun y : C𝔽 ↦ ∫ x : C𝔽, star (u x) * star (ψ.val y) * v (y * x) *
                (coshSobolevDensity α s (logNorm x) : ℂ) ∂μ𝔽)]
        _ = ∫ y : C𝔽, ∫ g : C𝔽, star (u (y⁻¹ * g)) * star (ψ.val y) * v g *
              (coshSobolevDensity α s (logNorm (y⁻¹ * g)) : ℂ) ∂μ𝔽 ∂μ𝔽 := by
            refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
            have hinv := integral_mul_left_eq_self (μ := μ𝔽)
              (fun g : C𝔽 ↦ star (u (y⁻¹ * g)) * star (ψ.val y) * v g *
                (coshSobolevDensity α s (logNorm (y⁻¹ * g)) : ℂ)) y
            exact (integral_congr_ae (ae_of_all _ fun x ↦ by
              simp only [inv_mul_cancel_left])).symm.trans hinv
        _ = ∫ g : C𝔽, ∫ y : C𝔽, star (u (y⁻¹ * g)) * star (ψ.val y) * v g *
              (coshSobolevDensity α s (logNorm (y⁻¹ * g)) : ℂ) ∂μ𝔽 ∂μ𝔽 :=
            integral_integral_swap hint_joint_adj
        _ = ∫ g : C𝔽, star (adjRaw g) * v g * (coshSobolevDensity α s (logNorm g) : ℂ) ∂μ𝔽 := by
            refine integral_congr_ae ?_
            filter_upwards [hae_int_adj] with g _hg
            have hconj : star (adjRaw g) =
                ∫ y : C𝔽, star (ψ.val y * K_adj (logNorm g) (logNorm y) * u (y⁻¹ * g)) ∂μ𝔽 :=
              (Complex.conjCLE.integral_comp_comm
                (fun y : C𝔽 ↦ ψ.val y * K_adj (logNorm g) (logNorm y) * u (y⁻¹ * g))).symm
            rw [hconj, ← integral_mul_const, ← integral_mul_const]
            refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
            dsimp only
            have hKstar : star (K_adj (logNorm g) (logNorm y)) = K_adj (logNorm g) (logNorm y) := by
              dsimp only [K_adj]; rw [Complex.star_def, Complex.conj_ofReal]
            rw [star_mul, star_mul, hKstar, hlog_mul, hlog_inv, ← sub_eq_neg_add]
            have hKmul : K_adj (logNorm g) (logNorm y) * (coshSobolevDensity α s (logNorm g) : ℂ) =
                (coshSobolevDensity α s (logNorm g - logNorm y) : ℂ) := by
              dsimp only [K_adj]
              rw [← Complex.ofReal_mul, div_mul_cancel₀ _ (coshSobolevDensity_pos α s _).ne']
            calc star (u (y⁻¹ * g)) * star (ψ.val y) * v g * (coshSobolevDensity α s (logNorm g - logNorm y) : ℂ)
                = star (u (y⁻¹ * g)) * star (ψ.val y) * v g *
                    (K_adj (logNorm g) (logNorm y) * (coshSobolevDensity α s (logNorm g) : ℂ)) := by rw [hKmul]
              _ = star (u (y⁻¹ * g)) * (K_adj (logNorm g) (logNorm y) * star (ψ.val y)) * v g *
                    (coshSobolevDensity α s (logNorm g) : ℂ) := by ring
    rw [heq_inner1, heq_inner2, heq_swap]
  rw [sub_apply, hadj_eq]
  have hsub := (tamagawa_absCont_coshSobolevMeasure (F := F) α s).ae_le (Lp.coeFn_sub
    (coshIntervalToLp F α s (coshTestAction (F := F) hα hs ψ u_c)) (hadj_mem.toLp adjRaw))
  have hadj_coe := (tamagawa_absCont_coshSobolevMeasure (F := F) α s).ae_le hadj_mem.coeFn_toLp
  filter_upwards [hsub, coshTestAction_apply hα hs ψ u_c, hadj_coe, hae_int_u, hae_int_adj]
    with g hg_sub hg_act hg_adj hg_iu hg_ia
  change ((coshIntervalToLp F α s (coshTestAction (F := F) hα hs ψ u_c) -
    coshIntervalToLp F α s ((coshIntervalToLp F α s).symm (hadj_mem.toLp adjRaw)) : Lp ℂ 2 ν) : C𝔽 → ℂ) g = _
  rw [(coshIntervalToLp F α s).apply_symm_apply, hg_sub, Pi.sub_apply, hg_act, hg_adj,
    lcaConvolution, ← integral_sub hg_iu hg_ia]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  dsimp only [K_adj]
  push_cast
  ring

end CoshKernelsAndTranslation

end RiemannMasullo.Isolated.CoshPositiveWidth
