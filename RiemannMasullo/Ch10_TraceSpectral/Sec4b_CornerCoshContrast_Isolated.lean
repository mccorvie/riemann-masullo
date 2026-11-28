module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_CornerScalar_Isolated
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_CornerRiesz_Isolated
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_CornerOrbit_Isolated
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_CornerLowerBound_Isolated
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch09_HardySobolev.Sec2
import RiemannMasullo.Ch09_HardySobolev.Sec3
import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import RiemannMasullo.AppD_SchwartzBruhat.Sec3b

/-!
# Smooth `cosh` Sobolev resolution and nonvanishing corner pairings (`#7406`)

1. `CoshSobolevSpace F α s`, `coshSobolevEquiv`, `coshTestAction`, and `coshRieszZeroJet`.
2. `coshSobolev_riesz_convolution_inner_rapid_decay`: replacing `intervalSobolevDensity (-α) α s`
   by `coshSobolevDensity α s` yields an equivalent Hilbert space where every
   `⟪A_cosh(φ) r_{σ, T}, u⟫` decays faster than `|T + τ|^{-N}` for all `N : ℕ`.
3. `exists_cornerPairing_ne_zero` & `exists_coshCornerPairing_ne_zero`: every nonzero vector
   in either Sobolev space has some `(ω, φ)` with nonzero corner pairing at `0`.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.Isolated

section CoshSobolevContrast

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => logIdeleClassNorm F
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α s

/-- Smooth `cosh` Sobolev Hilbert space `L²(μ𝔽, 2 * cosh (2 α |·|) * (1 + |·|^2)^{s/2})`. -/
def CoshSobolevSpace (F : Type*) [Field F] [NumberField F] (α s : ℝ) : Type _ :=
  Lp ℂ 2 (weightedSobolevMeasure F (coshSobolevDensity α s))

instance instNormedAddCommGroupCosh (α s : ℝ) :
    NormedAddCommGroup (CoshSobolevSpace F α s) :=
  inferInstanceAs (NormedAddCommGroup (Lp ℂ 2 (weightedSobolevMeasure F (coshSobolevDensity α s))))

instance instInnerProductSpaceCosh (α s : ℝ) :
    InnerProductSpace ℂ (CoshSobolevSpace F α s) :=
  inferInstanceAs (InnerProductSpace ℂ (Lp ℂ 2 (weightedSobolevMeasure F (coshSobolevDensity α s))))

instance instCompleteSpaceCosh (α s : ℝ) :
    CompleteSpace (CoshSobolevSpace F α s) :=
  inferInstanceAs (CompleteSpace (Lp ℂ 2 (weightedSobolevMeasure F (coshSobolevDensity α s))))

/-- Explicit `LinearIsometryEquiv` identifying `CoshSobolevSpace F α s` with its defining `Lp` space. -/
def coshSobolevToLp (F : Type*) [Field F] [NumberField F] (α s : ℝ) :
    CoshSobolevSpace F α s ≃ₗᵢ[ℂ] Lp ℂ 2 (weightedSobolevMeasure F (coshSobolevDensity α s)) :=
  LinearIsometryEquiv.refl ℂ (Lp ℂ 2 (weightedSobolevMeasure F (coshSobolevDensity α s)))

lemma weightedSobolev_memLp_of_le {w₁ w₂ : ℝ → ℝ} (hw₁ : Continuous w₁) (hw₁p : ∀ x, 0 < w₁ x)
    (hw₂ : Continuous w₂) (hw₂p : ∀ x, 0 < w₂ x) {C : ℝ} (_hC : 0 ≤ C) (hle : ∀ x, w₂ x ≤ C * w₁ x)
    (u : Lp ℂ 2 (weightedSobolevMeasure F w₁)) :
    MemLp (u : C𝔽 → ℂ) 2 (weightedSobolevMeasure F w₂) := by
  have haes : AEStronglyMeasurable (u : C𝔽 → ℂ) (weightedSobolevMeasure F w₂) :=
    ((Lp.aestronglyMeasurable u).mono_ac (tamagawa_absCont_weightedSobolevMeasure (F := F) hw₁ hw₁p)).mono_ac
      (weightedSobolevMeasure_absCont w₂)
  refine (memLp_two_iff_integrable_sq_norm haes).mpr ?_
  have hwd₂ : Measurable (fun g : C𝔽 ↦ ENNReal.ofReal (w₂ (logNorm g))) :=
    (hw₂.measurable.comp measurable_logNorm).ennreal_ofReal
  refine (integrable_withDensity_iff_integrable_smul' hwd₂
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mpr ?_
  have hu₁ := (integrable_sq_mul_weight hw₁ hw₁p u).const_mul C
  have hmeas : AEStronglyMeasurable (fun g : C𝔽 ↦ (ENNReal.ofReal (w₂ (logNorm g))).toReal • ‖u g‖ ^ 2) μ𝔽 :=
    (ENNReal.measurable_toReal.comp hwd₂).aestronglyMeasurable.smul
      (((Lp.aestronglyMeasurable u).mono_ac
        (tamagawa_absCont_weightedSobolevMeasure (F := F) hw₁ hw₁p)).norm.pow 2)
  refine hu₁.mono' hmeas (ae_of_all _ fun g ↦ ?_)
  rw [ENNReal.toReal_ofReal (hw₂p _).le, smul_eq_mul,
    Real.norm_of_nonneg (mul_nonneg (hw₂p _).le (sq_nonneg _))]
  calc w₂ (logNorm g) * ‖u g‖ ^ 2
      ≤ (C * w₁ (logNorm g)) * ‖u g‖ ^ 2 := mul_le_mul_of_nonneg_right (hle _) (sq_nonneg _)
    _ = C * (‖u g‖ ^ 2 * w₁ (logNorm g)) := by ring

lemma l2_norm_sq_eq_integral_mul_weight {w : ℝ → ℝ} (hw_cont : Continuous w) (hw_pos : ∀ x, 0 < w x)
    (u : Lp ℂ 2 (weightedSobolevMeasure F w)) :
    ‖u‖ ^ 2 = ∫ g : C𝔽, ‖u g‖ ^ 2 * w (logNorm g) ∂μ𝔽 := by
  have hsq : ((‖u‖ ^ 2 : ℝ) : ℂ) = @inner ℂ (Lp ℂ 2 (weightedSobolevMeasure F w)) _ u u := by
    simp [Complex.ofReal_pow]
  have hwd : Measurable (fun g : C𝔽 ↦ ENNReal.ofReal (w (logNorm g))) :=
    (hw_cont.measurable.comp measurable_logNorm).ennreal_ofReal
  have hwd_int : ∫ x : C𝔽, @inner ℂ ℂ _ (u x) (u x) ∂(weightedSobolevMeasure F w) =
      ∫ x : C𝔽, (ENNReal.ofReal (w (logNorm x))).toReal • @inner ℂ ℂ _ (u x) (u x) ∂μ𝔽 :=
    integral_withDensity_eq_integral_toReal_smul (μ := μ𝔽) hwd
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) (fun g : C𝔽 ↦ @inner ℂ ℂ _ (u g) (u g))
  apply Complex.ofReal_injective
  rw [hsq, L2.inner_def, hwd_int, ← Complex.ofRealCLM_apply,
    ← ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM (integrable_sq_mul_weight hw_cont hw_pos u)]
  refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
  dsimp only [Complex.ofRealCLM_apply]
  rw [ENNReal.toReal_ofReal (hw_pos _).le, Complex.real_smul, RCLike.inner_apply, mul_comm,
    Complex.mul_conj']
  push_cast; ring

def weightedSobolevChangeCLM {w₁ w₂ : ℝ → ℝ} (hw₁ : Continuous w₁) (hw₁p : ∀ x, 0 < w₁ x)
    (hw₂ : Continuous w₂) (hw₂p : ∀ x, 0 < w₂ x) {C : ℝ} (hC : 0 ≤ C) (hle : ∀ x, w₂ x ≤ C * w₁ x) :
    Lp ℂ 2 (weightedSobolevMeasure F w₁) →L[ℂ] Lp ℂ 2 (weightedSobolevMeasure F w₂) := by
  let habs₁ := tamagawa_absCont_weightedSobolevMeasure (F := F) hw₁ hw₁p
  let habs₂ := tamagawa_absCont_weightedSobolevMeasure (F := F) hw₂ hw₂p
  let L : Lp ℂ 2 (weightedSobolevMeasure F w₁) →ₗ[ℂ] Lp ℂ 2 (weightedSobolevMeasure F w₂) :=
    { toFun := fun u ↦ (weightedSobolev_memLp_of_le hw₁ hw₁p hw₂ hw₂p hC hle u).toLp u
      map_add' := fun u v ↦ by
        ext1
        have hEq : ((weightedSobolev_memLp_of_le hw₁ hw₁p hw₂ hw₂p hC hle (u + v)).toLp (u + v) : C𝔽 → ℂ) =ᵐ[μ𝔽]
            (((weightedSobolev_memLp_of_le hw₁ hw₁p hw₂ hw₂p hC hle u).toLp u +
              (weightedSobolev_memLp_of_le hw₁ hw₁p hw₂ hw₂p hC hle v).toLp v :
              Lp ℂ 2 (weightedSobolevMeasure F w₂)) : C𝔽 → ℂ) := by
          filter_upwards [habs₂.ae_le ((weightedSobolev_memLp_of_le hw₁ hw₁p hw₂ hw₂p hC hle (u + v)).coeFn_toLp),
            habs₂.ae_le ((weightedSobolev_memLp_of_le hw₁ hw₁p hw₂ hw₂p hC hle u).coeFn_toLp),
            habs₂.ae_le ((weightedSobolev_memLp_of_le hw₁ hw₁p hw₂ hw₂p hC hle v).coeFn_toLp),
            habs₁.ae_le (Lp.coeFn_add u v),
            habs₂.ae_le (Lp.coeFn_add
              ((weightedSobolev_memLp_of_le hw₁ hw₁p hw₂ hw₂p hC hle u).toLp u)
              ((weightedSobolev_memLp_of_le hw₁ hw₁p hw₂ hw₂p hC hle v).toLp v))]
            with g h1 h2 h3 h4 h5
          exact h1.trans (h4.trans (by dsimp only [Pi.add_apply]; rw [← h2, ← h3]; exact h5.symm))
        exact (weightedSobolevMeasure_absCont w₂).ae_le hEq
      map_smul' := fun c u ↦ by
        ext1
        have hEq : ((weightedSobolev_memLp_of_le hw₁ hw₁p hw₂ hw₂p hC hle (c • u)).toLp (c • u) : C𝔽 → ℂ) =ᵐ[μ𝔽]
            ((c • (weightedSobolev_memLp_of_le hw₁ hw₁p hw₂ hw₂p hC hle u).toLp u :
              Lp ℂ 2 (weightedSobolevMeasure F w₂)) : C𝔽 → ℂ) := by
          filter_upwards [habs₂.ae_le ((weightedSobolev_memLp_of_le hw₁ hw₁p hw₂ hw₂p hC hle (c • u)).coeFn_toLp),
            habs₂.ae_le ((weightedSobolev_memLp_of_le hw₁ hw₁p hw₂ hw₂p hC hle u).coeFn_toLp),
            habs₁.ae_le (Lp.coeFn_smul c u),
            habs₂.ae_le (Lp.coeFn_smul c ((weightedSobolev_memLp_of_le hw₁ hw₁p hw₂ hw₂p hC hle u).toLp u))]
            with g h1 h2 h3 h4
          exact h1.trans (h3.trans (by dsimp only [Pi.smul_apply]; rw [← h2]; exact h4.symm))
        exact (weightedSobolevMeasure_absCont w₂).ae_le hEq }
  refine L.mkContinuous (Real.sqrt C) fun u ↦ ?_
  have h1 : ‖L u‖ ^ 2 ≤ C * ‖u‖ ^ 2 := by
    rw [l2_norm_sq_eq_integral_mul_weight hw₂ hw₂p (L u),
      l2_norm_sq_eq_integral_mul_weight hw₁ hw₁p u, ← integral_const_mul]
    have hrep : (L u : C𝔽 → ℂ) =ᵐ[μ𝔽] (u : C𝔽 → ℂ) :=
      habs₂.ae_le ((weightedSobolev_memLp_of_le hw₁ hw₁p hw₂ hw₂p hC hle u).coeFn_toLp)
    have heq : (fun g : C𝔽 ↦ ‖(L u : C𝔽 → ℂ) g‖ ^ 2 * w₂ (logNorm g)) =ᵐ[μ𝔽]
        fun g : C𝔽 ↦ ‖u g‖ ^ 2 * w₂ (logNorm g) := hrep.mono fun g hg ↦ by simp [hg]
    rw [integral_congr_ae heq]
    refine integral_mono ((integrable_sq_mul_weight hw₂ hw₂p (L u)).congr heq)
      ((integrable_sq_mul_weight hw₁ hw₁p u).const_mul C) fun g ↦ ?_
    calc ‖u g‖ ^ 2 * w₂ (logNorm g) ≤ ‖u g‖ ^ 2 * (C * w₁ (logNorm g)) :=
          mul_le_mul_of_nonneg_left (hle _) (sq_nonneg _)
      _ = C * (‖u g‖ ^ 2 * w₁ (logNorm g)) := by ring
  have hsq := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hC, Real.sqrt_sq (norm_nonneg _)] at hsq

/-- Bounded linear isomorphism between `CoshSobolevSpace F α s` and `W(α, s)`. -/
def coshSobolevEquiv {α : ℝ} (hα : 0 ≤ α) (s : ℝ) : CoshSobolevSpace F α s ≃L[ℂ] W(α, s) :=
  let E := intervalToWeightedEquiv (F := F) (-α) α s
  let fwdCLM : Lp ℂ 2 (weightedSobolevMeasure F (coshSobolevDensity α s)) →L[ℂ]
      Lp ℂ 2 (weightedSobolevMeasure F (intervalSobolevDensity (-α) α s)) :=
    weightedSobolevChangeCLM (F := F) (continuous_coshSobolevDensity α s)
      (coshSobolevDensity_pos α s) (continuous_intervalSobolevDensity (-α) α s)
      (intervalSobolevDensity_pos (-α) α s) zero_le_one
      fun x ↦ (intervalSobolevDensity_le_coshSobolevDensity hα s x).trans_eq (one_mul _).symm
  let bwdCLM : Lp ℂ 2 (weightedSobolevMeasure F (intervalSobolevDensity (-α) α s)) →L[ℂ]
      Lp ℂ 2 (weightedSobolevMeasure F (coshSobolevDensity α s)) :=
    weightedSobolevChangeCLM (F := F) (continuous_intervalSobolevDensity (-α) α s)
      (intervalSobolevDensity_pos (-α) α s) (continuous_coshSobolevDensity α s)
      (coshSobolevDensity_pos α s) zero_le_two (coshSobolevDensity_le_two_mul hα s)
  let fwd : CoshSobolevSpace F α s →L[ℂ] W(α, s) :=
    E.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (fwdCLM.comp (coshSobolevToLp F α s).toContinuousLinearEquiv.toContinuousLinearMap)
  let bwd : W(α, s) →L[ℂ] CoshSobolevSpace F α s :=
    (coshSobolevToLp F α s).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (bwdCLM.comp E.toContinuousLinearEquiv.toContinuousLinearMap)
  have habs_sh := tamagawa_absCont_weightedSobolevMeasure (F := F)
    (continuous_intervalSobolevDensity (-α) α s) (intervalSobolevDensity_pos (-α) α s)
  have habs_co := tamagawa_absCont_weightedSobolevMeasure (F := F)
    (continuous_coshSobolevDensity α s) (coshSobolevDensity_pos α s)
  { toLinearEquiv :=
      { fwd.toLinearMap with
        invFun := bwd
        left_inv := fun u ↦ by
          apply (coshSobolevToLp F α s).injective
          ext1
          have hE_fwd : E (fwd u) = fwdCLM (coshSobolevToLp F α s u) := by
            dsimp only [fwd]
            simp only [ContinuousLinearMap.comp_apply]
            exact E.apply_symm_apply _
          change (bwdCLM (E ((fwd.toLinearMap) u)) : C𝔽 → ℂ) =ᵐ[weightedSobolevMeasure F (coshSobolevDensity α s)]
              (coshSobolevToLp F α s u : C𝔽 → ℂ)
          have h1 : (bwdCLM (E ((fwd.toLinearMap) u)) : C𝔽 → ℂ) =ᵐ[μ𝔽]
              ((E ((fwd.toLinearMap) u) : Lp ℂ 2 (weightedSobolevMeasure F (intervalSobolevDensity (-α) α s))) : C𝔽 → ℂ) :=
            habs_co.ae_le ((weightedSobolev_memLp_of_le (continuous_intervalSobolevDensity (-α) α s)
              (intervalSobolevDensity_pos (-α) α s) (continuous_coshSobolevDensity α s)
              (coshSobolevDensity_pos α s) zero_le_two (coshSobolevDensity_le_two_mul hα s)
              (E ((fwd.toLinearMap) u))).coeFn_toLp)
          have h2 : ((E ((fwd.toLinearMap) u) : Lp ℂ 2 (weightedSobolevMeasure F (intervalSobolevDensity (-α) α s))) : C𝔽 → ℂ) =ᵐ[μ𝔽]
              ((coshSobolevToLp F α s u : Lp ℂ 2 (weightedSobolevMeasure F (coshSobolevDensity α s))) : C𝔽 → ℂ) := by
            change (E (fwd u) : C𝔽 → ℂ) =ᵐ[μ𝔽] _
            rw [hE_fwd]
            exact habs_sh.ae_le ((weightedSobolev_memLp_of_le (continuous_coshSobolevDensity α s)
              (coshSobolevDensity_pos α s) (continuous_intervalSobolevDensity (-α) α s)
              (intervalSobolevDensity_pos (-α) α s) zero_le_one
              (fun x ↦ (intervalSobolevDensity_le_coshSobolevDensity hα s x).trans_eq (one_mul _).symm)
              (coshSobolevToLp F α s u)).coeFn_toLp)
          exact (weightedSobolevMeasure_absCont _).ae_le (h1.trans h2)
        right_inv := fun u ↦ by
          apply E.injective
          ext1
          change (E (fwd (bwd u)) : C𝔽 → ℂ) =ᵐ[weightedSobolevMeasure F (intervalSobolevDensity (-α) α s)] (E u : C𝔽 → ℂ)
          have hE_fb : E (fwd (bwd u)) = fwdCLM (bwdCLM (E u)) := by
            dsimp only [fwd, bwd]
            simp only [ContinuousLinearMap.comp_apply]
            exact E.apply_symm_apply _
          rw [hE_fb]
          have h1 : (fwdCLM (bwdCLM (E u)) : C𝔽 → ℂ) =ᵐ[μ𝔽] ((bwdCLM (E u) : CoshSobolevSpace F α s) : C𝔽 → ℂ) :=
            habs_sh.ae_le ((weightedSobolev_memLp_of_le (continuous_coshSobolevDensity α s)
              (coshSobolevDensity_pos α s) (continuous_intervalSobolevDensity (-α) α s)
              (intervalSobolevDensity_pos (-α) α s) zero_le_one
              (fun x ↦ (intervalSobolevDensity_le_coshSobolevDensity hα s x).trans_eq (one_mul _).symm)
              (bwdCLM (E u))).coeFn_toLp)
          have h2 : ((bwdCLM (E u) : CoshSobolevSpace F α s) : C𝔽 → ℂ) =ᵐ[μ𝔽] (E u : C𝔽 → ℂ) :=
            habs_co.ae_le ((weightedSobolev_memLp_of_le (continuous_intervalSobolevDensity (-α) α s)
              (intervalSobolevDensity_pos (-α) α s) (continuous_coshSobolevDensity α s)
              (coshSobolevDensity_pos α s) zero_le_two (coshSobolevDensity_le_two_mul hα s) (E u)).coeFn_toLp)
          exact (weightedSobolevMeasure_absCont _).ae_le (h1.trans h2) }
    continuous_toFun := fwd.continuous
    continuous_invFun := bwd.continuous }

lemma coshSobolevEquiv_ae {α : ℝ} (hα : 0 ≤ α) (s : ℝ) (u : CoshSobolevSpace F α s) :
    ((coshSobolevEquiv (F := F) hα s u : C𝔽 → ℂ) =ᵐ[μ𝔽]
      ((coshSobolevToLp F α s u : Lp ℂ 2 (weightedSobolevMeasure F (coshSobolevDensity α s))) : C𝔽 → ℂ)) := by
  let fwdCLM : Lp ℂ 2 (weightedSobolevMeasure F (coshSobolevDensity α s)) →L[ℂ]
      Lp ℂ 2 (weightedSobolevMeasure F (intervalSobolevDensity (-α) α s)) :=
    weightedSobolevChangeCLM (F := F) (continuous_coshSobolevDensity α s)
      (coshSobolevDensity_pos α s) (continuous_intervalSobolevDensity (-α) α s)
      (intervalSobolevDensity_pos (-α) α s) zero_le_one
      fun x ↦ (intervalSobolevDensity_le_coshSobolevDensity hα s x).trans_eq (one_mul _).symm
  have habs_sh := tamagawa_absCont_weightedSobolevMeasure (F := F)
    (continuous_intervalSobolevDensity (-α) α s) (intervalSobolevDensity_pos (-α) α s)
  have h1 : ((coshSobolevEquiv (F := F) hα s u : W(α, s)) : C𝔽 → ℂ) =ᵐ[μ𝔽]
      ((fwdCLM (coshSobolevToLp F α s u) :
        Lp ℂ 2 (weightedSobolevMeasure F (intervalSobolevDensity (-α) α s))) : C𝔽 → ℂ) := by
    change ((lpEquivOfMeasureEq (weightedSobolevMeasure_eq_interval (F := F) (-α) α s).symm).symm
      (fwdCLM (coshSobolevToLp F α s u)) : C𝔽 → ℂ) =ᵐ[μ𝔽] _
    generalize (weightedSobolevMeasure_eq_interval (F := F) (-α) α s).symm = h
    cases h
    exact Filter.EventuallyEq.refl _ _
  have h2 : ((fwdCLM (coshSobolevToLp F α s u) :
        Lp ℂ 2 (weightedSobolevMeasure F (intervalSobolevDensity (-α) α s))) : C𝔽 → ℂ) =ᵐ[μ𝔽]
      ((coshSobolevToLp F α s u : Lp ℂ 2 (weightedSobolevMeasure F (coshSobolevDensity α s))) : C𝔽 → ℂ) :=
    habs_sh.ae_le ((weightedSobolev_memLp_of_le (continuous_coshSobolevDensity α s)
      (coshSobolevDensity_pos α s) (continuous_intervalSobolevDensity (-α) α s)
      (intervalSobolevDensity_pos (-α) α s) zero_le_one
      (fun x ↦ (intervalSobolevDensity_le_coshSobolevDensity hα s x).trans_eq (one_mul _).symm)
      (coshSobolevToLp F α s u)).coeFn_toLp)
  exact h1.trans h2

/-- Bounded convolution operator on `CoshSobolevSpace F α s`, conjugated from `hardySobolevTestAction`. -/
def coshTestAction {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽) :
    CoshSobolevSpace F α s →L[ℂ] CoshSobolevSpace F α s :=
  (coshSobolevEquiv hα s).symm.toContinuousLinearMap.comp
    ((hardySobolevTestAction μ𝔽 m𝔽 (-α) α s ((neg_nonpos.mpr hα).trans hα) hs φ).comp
      (coshSobolevEquiv hα s).toContinuousLinearMap)

lemma coshTestAction_apply {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽)
    (u : CoshSobolevSpace F α s) :
    ((coshSobolevToLp F α s (coshTestAction (F := F) hα hs φ u) :
        Lp ℂ 2 (weightedSobolevMeasure F (coshSobolevDensity α s))) : C𝔽 → ℂ) =ᵐ[μ𝔽]
      lcaConvolution μ𝔽 φ.val (coshSobolevToLp F α s u) := by
  have h1 : ((coshSobolevToLp F α s (coshTestAction (F := F) hα hs φ u) :
        Lp ℂ 2 (weightedSobolevMeasure F (coshSobolevDensity α s))) : C𝔽 → ℂ) =ᵐ[μ𝔽]
      (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s ((neg_nonpos.mpr hα).trans hα) hs φ
        (coshSobolevEquiv hα s u) : C𝔽 → ℂ) :=
    (tamagawa_absCont_weightedSobolevMeasure (F := F) (continuous_coshSobolevDensity α s)
      (coshSobolevDensity_pos α s)).ae_le
      ((weightedSobolev_memLp_of_le (continuous_intervalSobolevDensity (-α) α s)
        (intervalSobolevDensity_pos (-α) α s) (continuous_coshSobolevDensity α s)
        (coshSobolevDensity_pos α s) zero_le_two (coshSobolevDensity_le_two_mul hα s)
        (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s ((neg_nonpos.mpr hα).trans hα) hs φ
          (coshSobolevEquiv hα s u))).coeFn_toLp)
  have h2 := hardySobolevTestAction_apply μ𝔽 m𝔽 (-α) α s ((neg_nonpos.mpr hα).trans hα) hs φ
    (coshSobolevEquiv hα s u)
  have h3 := coshSobolevEquiv_ae hα s u
  have hconv : lcaConvolution μ𝔽 φ.val (coshSobolevEquiv (F := F) hα s u) =ᵐ[μ𝔽]
      lcaConvolution μ𝔽 φ.val (coshSobolevToLp F α s u) := by
    refine ae_of_all _ fun g ↦ integral_congr_ae ?_
    have h_isHaar : (μ𝔽).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
    let mp : MeasurePreserving (fun y : C𝔽 ↦ y⁻¹ * g) μ𝔽 μ𝔽 :=
      (measurePreserving_mul_right μ𝔽 g).comp (Measure.measurePreserving_inv μ𝔽)
    filter_upwards [mp.quasiMeasurePreserving.ae h3] with y hy
    rw [hy]
  exact h1.trans (h2.trans hconv)

/-- Explicit depth-zero Riesz representer in `CoshSobolevSpace F α s`. -/
def coshRieszZeroJet {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) {σ : ℝ} (hσ : σ ∈ Icc (-α) α)
    (ψ : PontryaginDual C𝔽) (T : ℝ) : CoshSobolevSpace F α s :=
  (coshSobolevToLp F α s).symm
    (weightedRieszJet (F := F) (continuous_coshSobolevDensity α s)
      (coshSobolevDensity_pos α s) hs (exp_div_coshSobolevDensity_dom hα hσ) ψ T)

private lemma cosh_sqrt_inv_u_le {α σ : ℝ} (_hα : 0 ≤ α) (hσ : σ ∈ Icc (-α) α) (x : ℝ) :
    Real.sqrt (2 * Real.cosh (2 * α * x)) *
        (Real.exp ((2 * α - σ) * x) + Real.exp (-(2 * α + σ) * x))⁻¹ ≤ Real.sqrt 2 := by
  let u := Real.exp ((2 * α - σ) * x) + Real.exp (-(2 * α + σ) * x)
  have hu_pos : 0 < u := by positivity
  have hsq : 2 * Real.cosh (2 * α * x) ≤ 2 * u ^ 2 := by
    have hcosh : 2 * Real.cosh (2 * α * x) = Real.exp (2 * α * x) + Real.exp (-(2 * α * x)) := by
      rw [Real.cosh_eq]; ring
    rw [hcosh]
    have hsub1 : ∀ t : ℝ, Real.exp t ≤ u ^ 2 → Real.exp (-t) ≤ u ^ 2 →
        Real.exp t + Real.exp (-t) ≤ 2 * u ^ 2 := fun _ h1 h2 ↦ by linarith
    rcases le_total 0 x with hx | hx
    · have ha1 : Real.exp (2 * α * x) ≤ u ^ 2 := by
        have h1 : Real.exp (2 * α * x) ≤ Real.exp (2 * ((2 * α - σ) * x)) :=
          Real.exp_le_exp.mpr (by nlinarith [hσ.2])
        have h2 : Real.exp (2 * ((2 * α - σ) * x)) = Real.exp ((2 * α - σ) * x) ^ 2 := by
          rw [sq, ← Real.exp_add]; congr 1; ring
        have h3 : Real.exp ((2 * α - σ) * x) ^ 2 ≤ u ^ 2 := by
          nlinarith [sq_nonneg (Real.exp (-(2 * α + σ) * x)), (Real.exp_pos ((2 * α - σ) * x)).le,
            (Real.exp_pos (-(2 * α + σ) * x)).le]
        exact h1.trans (h2.trans_le h3)
      have ha2 : Real.exp (-(2 * α * x)) ≤ u ^ 2 := by
        have h1 : Real.exp (-(2 * α * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        have h2 : 1 ≤ Real.exp ((2 * α - σ) * x) := Real.one_le_exp (by nlinarith [hσ.2])
        nlinarith [h2, (Real.exp_pos (-(2 * α + σ) * x)).le]
      exact hsub1 _ ha1 ha2
    · have ha2 : Real.exp (-(2 * α * x)) ≤ u ^ 2 := by
        have h1 : Real.exp (-(2 * α * x)) ≤ Real.exp (2 * (-(2 * α + σ) * x)) :=
          Real.exp_le_exp.mpr (by nlinarith [hσ.1])
        have h2 : Real.exp (2 * (-(2 * α + σ) * x)) = Real.exp (-(2 * α + σ) * x) ^ 2 := by
          rw [sq, ← Real.exp_add]; congr 1; ring
        have h3 : Real.exp (-(2 * α + σ) * x) ^ 2 ≤ u ^ 2 := by
          nlinarith [sq_nonneg (Real.exp ((2 * α - σ) * x)), (Real.exp_pos ((2 * α - σ) * x)).le,
            (Real.exp_pos (-(2 * α + σ) * x)).le]
        exact h1.trans (h2.trans_le h3)
      have ha1 : Real.exp (2 * α * x) ≤ u ^ 2 := by
        have h1 : Real.exp (2 * α * x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        have h2 : 1 ≤ Real.exp (-(2 * α + σ) * x) := Real.one_le_exp (by nlinarith [hσ.1])
        nlinarith [h2, (Real.exp_pos ((2 * α - σ) * x)).le]
      exact hsub1 _ ha1 ha2
  have hsqrt : Real.sqrt (2 * Real.cosh (2 * α * x)) ≤ Real.sqrt 2 * u :=
    (Real.sqrt_le_sqrt hsq).trans_eq <| by
      rw [Real.sqrt_mul zero_le_two (u ^ 2), Real.sqrt_sq hu_pos.le]
  exact (mul_le_mul_of_nonneg_right hsqrt (inv_pos.mpr hu_pos).le).trans_eq
    (by rw [mul_assoc, mul_inv_cancel₀ hu_pos.ne', mul_one])

private lemma iteratedDeriv_inv_le_const_mul_inv {u : ℝ → ℝ} (hu : ContDiff ℝ (↑(⊤ : ℕ∞)) u)
    (h1 : ∀ x : ℝ, 1 ≤ u x) (hdom : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |iteratedDeriv j u x| ≤ C * u x) :
    ∀ m : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |iteratedDeriv m (fun t ↦ (u t)⁻¹) x| ≤ M * (u x)⁻¹ := by
  have hupos (x : ℝ) : 0 < u x := lt_of_lt_of_le zero_lt_one (h1 x)
  have h1_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) (iteratedDeriv 1 u) := by
    rw [show iteratedDeriv 1 u = deriv u from iteratedDeriv_one]
    exact contDiff_infty.mpr fun _n ↦
      (contDiff_succ_iff_deriv.mp (hu.of_le (by exact mod_cast le_top))).2.2
  have hq_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t ↦ iteratedDeriv 1 u t / u t) :=
    h1_cd.div hu fun t ↦ (hupos t).ne'
  have hi_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t ↦ (u t)⁻¹) := hu.inv fun t ↦ (hupos t).ne'
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    cases m with
    | zero =>
      refine ⟨1, zero_le_one, fun x ↦ ?_⟩
      simp [abs_of_pos (inv_pos.mpr (hupos x))]
    | succ k =>
      choose Qi hQi0 hQi using fun i ↦ (iteratedDeriv_inv_bounded_of_dom hu h1 hdom i).1 1
      have hsub : ∀ i ≤ k, ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |iteratedDeriv i (fun t ↦ (u t)⁻¹) x| ≤ M * (u x)⁻¹ :=
        fun i hi ↦ ih i (Nat.lt_succ_of_le hi)
      choose Mi hMi0 hMi using hsub
      have hderiv_eq : deriv (fun t ↦ (u t)⁻¹) = fun t ↦ -((iteratedDeriv 1 u t / u t) * (u t)⁻¹) := by
        funext t
        have hd : HasDerivAt u (iteratedDeriv 1 u t) t := by
          rw [iteratedDeriv_one]
          exact (hu.differentiable (by simp) t).hasDerivAt
        have hq := (hd.inv (hupos t).ne').deriv
        change deriv (fun r ↦ (u r)⁻¹) t = _
        rw [show (fun r ↦ (u r)⁻¹) = u⁻¹ from rfl, hq]
        field_simp [(hupos t).ne']
      refine ⟨∑ i ∈ Finset.range (k + 1), if _hi : i ≤ k then
          (k.choose i : ℝ) * Qi i * Mi (k - i) (by omega) else 0,
        Finset.sum_nonneg fun i _ ↦ by
          split_ifs with hi
          · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hQi0 i)) (hMi0 (k - i) (by omega))
          · exact le_rfl,
        fun x ↦ ?_⟩
      have hsplit : |iteratedDeriv (k + 1) (fun t ↦ (u t)⁻¹) x| =
          |iteratedDeriv k ((fun t ↦ iteratedDeriv 1 u t / u t) * fun t ↦ (u t)⁻¹) x| := by
        rw [iteratedDeriv_succ', hderiv_eq]
        change |iteratedDeriv k (-(fun t ↦ (iteratedDeriv 1 u t / u t) * (u t)⁻¹)) x| = _
        rw [iteratedDeriv_neg, abs_neg]
        rfl
      rw [hsplit, iteratedDeriv_mul (hq_cd.contDiffAt.of_le (by exact mod_cast le_top))
        (hi_cd.contDiffAt.of_le (by exact mod_cast le_top))]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi_mem ↦ ?_
      have hi : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi_mem)
      simp only [hi, ↓reduceDIte, abs_mul]
      rw [abs_of_nonneg (Nat.cast_nonneg (k.choose i))]
      have hqbx := hQi i x
      have hibx := hMi (k - i) (by omega) x
      calc (k.choose i : ℝ) * |iteratedDeriv i (fun t ↦ iteratedDeriv 1 u t / u t) x| *
            |iteratedDeriv (k - i) (fun t ↦ (u t)⁻¹) x|
          ≤ (k.choose i : ℝ) * Qi i * (Mi (k - i) (by omega) * (u x)⁻¹) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hqbx (Nat.cast_nonneg _)) hibx (abs_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _) (hQi0 i))
        _ = (k.choose i : ℝ) * Qi i * Mi (k - i) (by omega) * (u x)⁻¹ := by ring

/-- Under the smooth `cosh` Sobolev density, `⟪A_cosh(φ) r_{σ, T}, u⟫` decays faster than
every negative power of `|T + τ|` (resolving the corner obstruction at positive width). -/
theorem coshSobolev_riesz_convolution_inner_rapid_decay {α s σ : ℝ}
    (hα : 0 ≤ α) (hs : 1 < s) (hσ : σ ∈ Icc (-α) α)
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    (ω : PontryaginDual (ideleClassNorm F).ker) (τ : ℝ)
    (hτ : ∀ x : ℝ, (χ ω (canonicalNormFlow F (Multiplicative.ofAdd x)) : ℂ) =
      Complex.exp (Complex.I * (τ : ℂ) * (x : ℂ)))
    (φ : BruhatCompactSupport C𝔽) (u : CoshSobolevSpace F α s) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T + τ ≠ 0 →
      ‖@inner ℂ (CoshSobolevSpace F α s) _
          (coshTestAction (F := F) hα (zero_le_one.trans hs.le) φ
            (coshRieszZeroJet hα hs hσ (χ ω) T)) u‖ ≤ C / |T + τ| ^ N := by
  let w := coshSobolevDensity α s
  have hw_cont := continuous_coshSobolevDensity α s
  have hw_pos := coshSobolevDensity_pos α s
  obtain ⟨R, hR, hsupp⟩ := exists_logNorm_bound_tsupport (F := F) φ
  obtain ⟨CR, hCR, hshift⟩ := coshSobolevDensity_shift_bound (α := α) (s := s) hα
    (zero_le_one.trans hs.le) hR
  obtain ⟨CR₁, hCR₁, hshift1⟩ := coshSobolevDensity_shift_bound (α := α) (s := s) hα
    (zero_le_one.trans hs.le) (by linarith : 0 ≤ R + 1)
  let A : Lp ℂ 2 (weightedSobolevMeasure F w) →L[ℂ] Lp ℂ 2 (weightedSobolevMeasure F w) :=
    (coshSobolevToLp F α s).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((coshTestAction hα (zero_le_one.trans hs.le) φ).comp
        (coshSobolevToLp F α s).symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have hA : ∀ v : Lp ℂ 2 (weightedSobolevMeasure F w), (A v : C𝔽 → ℂ) =ᵐ[μ𝔽] lcaConvolution μ𝔽 φ.val v :=
    fun v ↦ coshTestAction_apply hα (zero_le_one.trans hs.le) φ ((coshSobolevToLp F α s).symm v)
  let uLp := coshSobolevToLp F α s u
  let G : ℝ → ℂ := cornerOrbitProfile w ω φ uLp
  have hG_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) G :=
    (cornerOrbitProfile_contDiff hw_cont hw_pos uLp ω φ hR hsupp hCR₁ hshift1 0).1
  let a : ℝ := 2 * α - σ
  let b : ℝ := -(2 * α + σ)
  let uExp (t : ℝ) : ℝ := Real.exp (a * t) + Real.exp (b * t)
  have hu_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) uExp :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).add
      (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  have hu_ge1 : ∀ x : ℝ, 1 ≤ uExp x := fun x ↦ by
    rcases le_total 0 x with hx | hx
    · exact le_add_of_le_of_nonneg (Real.one_le_exp (mul_nonneg (by linarith [hσ.2]) hx)) (Real.exp_pos _).le
    · exact le_add_of_nonneg_of_le (Real.exp_pos _).le
        (Real.one_le_exp (mul_nonneg_of_nonpos_of_nonpos (by linarith [hσ.1]) hx))
  have hu_deriv (j : ℕ) (x : ℝ) :
      iteratedDeriv j uExp x = a ^ j * Real.exp (a * x) + b ^ j * Real.exp (b * x) := by
    have hca : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t : ℝ ↦ Real.exp (a * t)) :=
      Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
    have hcb : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t : ℝ ↦ Real.exp (b * t)) :=
      Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
    rw [show uExp = (fun t ↦ Real.exp (a * t)) + (fun t ↦ Real.exp (b * t)) from rfl,
      iteratedDeriv_add (hca.contDiffAt.of_le (by exact mod_cast le_top))
        (hcb.contDiffAt.of_le (by exact mod_cast le_top)),
      congrFun (iteratedDeriv_exp_const_mul j a) x,
      congrFun (iteratedDeriv_exp_const_mul j b) x]
  have hu_dom : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |iteratedDeriv j uExp x| ≤ C * uExp x := by
    intro j
    refine ⟨|a| ^ j + |b| ^ j, by positivity, fun x ↦ ?_⟩
    rw [hu_deriv j x]
    refine (abs_add_le _ _).trans ?_
    simp only [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    have ha0 : 0 ≤ Real.exp (a * x) := (Real.exp_pos _).le
    have hb0 : 0 ≤ Real.exp (b * x) := (Real.exp_pos _).le
    have hab : 0 ≤ |a| ^ j * Real.exp (b * x) + |b| ^ j * Real.exp (a * x) := by positivity
    calc |a| ^ j * Real.exp (a * x) + |b| ^ j * Real.exp (b * x)
        ≤ |a| ^ j * Real.exp (a * x) + |b| ^ j * Real.exp (b * x) +
            (|a| ^ j * Real.exp (b * x) + |b| ^ j * Real.exp (a * x)) := le_add_of_nonneg_right hab
      _ = (|a| ^ j + |b| ^ j) * uExp x := by dsimp only [uExp]; ring
  let q : ℝ → ℝ := fun t ↦ Real.exp (σ * t) / w t
  have hq_eq : q = fun t : ℝ ↦ (uExp t)⁻¹ * (1 + t ^ 2) ^ (-s / 2) := by
    funext t
    dsimp only [q, w, coshSobolevDensity, uExp, a, b]
    have hcosh : 2 * Real.cosh (2 * α * t) * Real.exp (-σ * t) =
        Real.exp ((2 * α - σ) * t) + Real.exp (-(2 * α + σ) * t) := by
      rw [Real.cosh_eq, mul_div_cancel₀ _ two_ne_zero, add_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1 <;> congr 1 <;> ring
    have hrpow : (1 + t ^ 2) ^ (-s / 2) = ((1 + t ^ 2) ^ (s / 2))⁻¹ := by
      rw [show -s / 2 = -(s / 2) by ring, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + t ^ 2)]
    rw [hrpow, ← hcosh]
    simp only [div_eq_mul_inv, mul_inv, show -σ * t = -(σ * t) by ring, Real.exp_neg, inv_inv]
    ring
  have hrpow_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t : ℝ ↦ (1 + t ^ 2) ^ (-s / 2)) :=
    (contDiff_const.add (contDiff_id.pow 2)).rpow_const_of_ne fun x ↦ by positivity
  have hinv_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t : ℝ ↦ (uExp t)⁻¹) :=
    hu_cd.inv fun t ↦ (lt_of_lt_of_le zero_lt_one (hu_ge1 t)).ne'
  have hq_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) q := by
    rw [hq_eq]
    exact hinv_cd.mul hrpow_cd
  have hq_dom : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ (univ : Set ℝ),
      Real.sqrt (w x) * |iteratedDeriv k q x| ≤ C * (1 + x ^ 2) ^ (-s / 4) := by
    intro k
    choose Mi hMi0 hMi using fun i ↦ iteratedDeriv_inv_le_const_mul_inv hu_cd hu_ge1 hu_dom i
    choose Ck hCk0 hCk using fun i ↦ iteratedDeriv_one_add_sq_rpow_le s (k - i)
    refine ⟨Real.sqrt 2 * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Mi i * Ck i,
      mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun i _ ↦
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hMi0 i)) (hCk0 i)),
      fun x _ ↦ ?_⟩
    rw [hq_eq]
    have hmul_id : iteratedDeriv k (fun t : ℝ ↦ (uExp t)⁻¹ * (1 + t ^ 2) ^ (-s / 2)) x =
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          iteratedDeriv i (fun t ↦ (uExp t)⁻¹) x *
          iteratedDeriv (k - i) (fun t ↦ (1 + t ^ 2) ^ (-s / 2)) x := by
      change iteratedDeriv k ((fun t ↦ (uExp t)⁻¹) * fun t ↦ (1 + t ^ 2) ^ (-s / 2)) x = _
      rw [iteratedDeriv_mul (hinv_cd.contDiffAt.of_le (by exact mod_cast le_top))
        (hrpow_cd.contDiffAt.of_le (by exact mod_cast le_top))]
    rw [hmul_id]
    have hsqrt_w : Real.sqrt (w x) = Real.sqrt (2 * Real.cosh (2 * α * x)) * (1 + x ^ 2) ^ (s / 4) := by
      dsimp only [w, coshSobolevDensity]
      rw [Real.sqrt_mul (mul_nonneg zero_le_two (Real.cosh_pos _).le),
        Real.sqrt_eq_rpow ((1 + x ^ 2) ^ (s / 2)),
        ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + x ^ 2) (s / 2) (1 / 2)]
      congr 2; ring
    have hrpow : (1 + x ^ 2) ^ (s / 4) * (1 + x ^ 2) ^ (-s / 2) = (1 + x ^ 2) ^ (-s / 4) := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < 1 + x ^ 2)]
      congr 1; ring
    have habs_le : |∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          iteratedDeriv i (fun t ↦ (uExp t)⁻¹) x *
          iteratedDeriv (k - i) (fun t ↦ (1 + t ^ 2) ^ (-s / 2)) x| ≤
        (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Mi i * Ck i) *
          ((uExp x)⁻¹ * (1 + x ^ 2) ^ (-s / 2)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      calc (k.choose i : ℝ) * |iteratedDeriv i (fun t ↦ (uExp t)⁻¹) x| *
            |iteratedDeriv (k - i) (fun t ↦ (1 + t ^ 2) ^ (-s / 2)) x|
          ≤ (k.choose i : ℝ) * (Mi i * (uExp x)⁻¹) * (Ck i * (1 + x ^ 2) ^ (-s / 2)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hMi i x) (Nat.cast_nonneg _)) (hCk i x)
              (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hMi0 i) (by positivity)))
        _ = (k.choose i : ℝ) * Mi i * Ck i * ((uExp x)⁻¹ * (1 + x ^ 2) ^ (-s / 2)) := by ring
    calc Real.sqrt (w x) * |∑ i ∈ Finset.range (k + 1), _|
        ≤ Real.sqrt (w x) * ((∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Mi i * Ck i) *
            ((uExp x)⁻¹ * (1 + x ^ 2) ^ (-s / 2))) :=
          mul_le_mul_of_nonneg_left habs_le (Real.sqrt_nonneg _)
      _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Mi i * Ck i) *
            ((Real.sqrt (2 * Real.cosh (2 * α * x)) * (uExp x)⁻¹) *
              ((1 + x ^ 2) ^ (s / 4) * (1 + x ^ 2) ^ (-s / 2))) := by
          rw [hsqrt_w]; ring
      _ ≤ (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Mi i * Ck i) *
            (Real.sqrt 2 * (1 + x ^ 2) ^ (-s / 4)) := by
          rw [hrpow]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (cosh_sqrt_inv_u_le hα hσ x) (by positivity))
            (Finset.sum_nonneg fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hMi0 i)) (hCk0 i))
      _ = Real.sqrt 2 * (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Mi i * Ck i) *
            (1 + x ^ 2) ^ (-s / 4) := by ring
  let H : ℝ → ℂ := fun t ↦ G t * (q t : ℂ)
  have hH_cd : ContDiff ℝ N H := (hG_cd.mul (Complex.ofRealCLM.contDiff.comp hq_cd)).of_le (by exact mod_cast le_top)
  have hH_int : ∀ k ≤ N, Integrable (fun x : ℝ ↦ iteratedDeriv k H x) volume := fun k _ ↦ by
    rw [← integrableOn_univ]
    exact integrable_smooth_orbit_mul_poly_piece hw_cont hw_pos hs uLp ω φ hR hsupp hCR hCR₁
      hshift hshift1 hq_cd MeasurableSet.univ hq_dom k
  refine ⟨tamagawaNormFactor F * ∫ x : ℝ, ‖iteratedDeriv N H x‖,
    mul_nonneg (tamagawaNormFactor_pos (F := F)).le (integral_nonneg fun _ ↦ norm_nonneg _),
    fun T hTτ ↦ ?_⟩
  have hdec := fourier_smooth_rapid_decay N H hH_cd hH_int (η := -(T + τ)) (neg_ne_zero.mpr hTτ)
  have hfac := weightedRieszJet_convolution_inner_eq_fourier (F := F) hw_cont hw_pos hs
    (exp_div_coshSobolevDensity_dom hα hσ) hR hCR hshift χ hχ ω τ hτ φ hsupp T A hA uLp
  have hinner_eq : @inner ℂ (CoshSobolevSpace F α s) _
      (coshTestAction (F := F) hα (zero_le_one.trans hs.le) φ
        (coshRieszZeroJet hα hs hσ (χ ω) T)) u =
      @inner ℂ (Lp ℂ 2 (weightedSobolevMeasure F w)) _
        (A (weightedRieszJet hw_cont hw_pos hs (exp_div_coshSobolevDensity_dom hα hσ) (χ ω) T)) uLp := rfl
  rw [hinner_eq, hfac, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (tamagawaNormFactor_pos (F := F)).le]
  have hm := mul_le_mul_of_nonneg_left hdec (tamagawaNormFactor_pos (F := F)).le
  rw [abs_neg] at hm
  exact hm.trans_eq (by ring)

end CoshSobolevContrast

section CornerPairingNonvanishing

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => logIdeleClassNorm F
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α s

private lemma zero_of_forall_bruhat_pairing_zero {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    {w : ℝ → ℝ} (hw_cont : Continuous w) (hw_pos : ∀ x, 0 < w x)
    (hw_dom_sharp : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, w x ≤ C * intervalSobolevDensity (-α) α s x)
    (u : Lp ℂ 2 (weightedSobolevMeasure F w))
    (hpair : ∀ φ : BruhatCompactSupport C𝔽,
      ∫ g : C𝔽, star (φ.val g) * u g * (w (logNorm g) : ℂ) ∂μ𝔽 = 0) :
    u = 0 := by
  have hI : -α ≤ α := (neg_nonpos.mpr hα).trans hα
  have hm : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hsurj : Function.Surjective m𝔽 := fun t ↦
    ⟨QuotientGroup.mk (canonicalIdeleNormSection F t), canonicalIdeleNormSection_rightInverse F t⟩
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm
  have : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm).exists.choose_spec.1
  let c : ℝ := tamagawaNormFactor F
  have hc_pos : 0 < c := tamagawaNormFactor_pos (F := F)
  have hc_eq : (normOneIdeleClassTamagawaMeasure F) univ = ENNReal.ofReal c := by
    simpa [c, tamagawaNormFactor] using (ENNReal.ofReal_toReal (tamagawaNormFactor_ne_top (F := F))).symm
  have hμ_eq : μ𝔽 = ENNReal.ofReal c • ν := by
    rw [ideleClassTamagawaMeasure_eq_smul_canonical, hc_eq]
  let w_sh := intervalSobolevDensity (-α) α s
  let ν_sh : Measure C𝔽 := ν.withDensity fun g ↦ ENNReal.ofReal (w_sh (logNorm g))
  let Wν := ModulatedIntervalSobolev m𝔽 hm (-α) α s
  let v_raw : C𝔽 → ℂ := fun g ↦ u g * ((w (logNorm g) / w_sh (logNorm g) : ℝ) : ℂ)
  have hv_mem_sh : MemLp v_raw 2 (weightedSobolevMeasure F w_sh) := by
    have haes : AEStronglyMeasurable v_raw (weightedSobolevMeasure F w_sh) := by
      have hu_m := ((Lp.aestronglyMeasurable u).mono_ac
        (tamagawa_absCont_weightedSobolevMeasure (F := F) hw_cont hw_pos)).mono_ac
        (weightedSobolevMeasure_absCont w_sh)
      have hrat_c : Continuous (fun g : C𝔽 ↦ ((w (logNorm g) / w_sh (logNorm g) : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp ((hw_cont.comp continuous_logNorm).div
          ((continuous_intervalSobolevDensity (-α) α s).comp continuous_logNorm)
          fun g ↦ (intervalSobolevDensity_pos (-α) α s _).ne')
      exact hu_m.mul hrat_c.aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm haes).mpr ?_
    have hwd_sh : Measurable (fun g : C𝔽 ↦ ENNReal.ofReal (w_sh (logNorm g))) :=
      ((continuous_intervalSobolevDensity (-α) α s).measurable.comp measurable_logNorm).ennreal_ofReal
    refine (integrable_withDensity_iff_integrable_smul' hwd_sh
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mpr ?_
    obtain ⟨Cd, _hCd0, hCd⟩ := hw_dom_sharp
    have hu_int := (integrable_sq_mul_weight hw_cont hw_pos u).const_mul Cd
    have hmeas : AEStronglyMeasurable (fun g : C𝔽 ↦ (ENNReal.ofReal (w_sh (logNorm g))).toReal • ‖v_raw g‖ ^ 2) μ𝔽 := by
      have hu_m := (Lp.aestronglyMeasurable u).mono_ac (tamagawa_absCont_weightedSobolevMeasure (F := F) hw_cont hw_pos)
      have hrat_c : Continuous (fun g : C𝔽 ↦ ((w (logNorm g) / w_sh (logNorm g) : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp ((hw_cont.comp continuous_logNorm).div
          ((continuous_intervalSobolevDensity (-α) α s).comp continuous_logNorm)
          fun g ↦ (intervalSobolevDensity_pos (-α) α s _).ne')
      exact (ENNReal.measurable_toReal.comp hwd_sh).aestronglyMeasurable.smul
        ((hu_m.mul hrat_c.aestronglyMeasurable).norm.pow 2)
    refine hu_int.mono' hmeas (ae_of_all _ fun g ↦ ?_)
    have hwsh_pos := intervalSobolevDensity_pos (-α) α s (logNorm g)
    rw [ENNReal.toReal_ofReal hwsh_pos.le, smul_eq_mul,
      Real.norm_of_nonneg (mul_nonneg hwsh_pos.le (sq_nonneg _))]
    dsimp only [v_raw]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_pos (hw_pos _) hwsh_pos).le,
      mul_pow, div_pow]
    have hrat_le : w (logNorm g) / w_sh (logNorm g) ≤ Cd := (div_le_iff₀ hwsh_pos).mpr (hCd _)
    calc w_sh (logNorm g) * (‖u g‖ ^ 2 * (w (logNorm g) ^ 2 / w_sh (logNorm g) ^ 2))
        = (w (logNorm g) / w_sh (logNorm g)) * (‖u g‖ ^ 2 * w (logNorm g)) := by
          field_simp [hwsh_pos.ne']
      _ ≤ Cd * (‖u g‖ ^ 2 * w (logNorm g)) :=
          mul_le_mul_of_nonneg_right hrat_le (mul_nonneg (sq_nonneg _) (hw_pos _).le)
  have hle_νsh : ν_sh ≤ ENNReal.ofReal c⁻¹ • weightedSobolevMeasure F w_sh := by
    intro S
    simp only [ν_sh, weightedSobolevMeasure, hμ_eq, withDensity_smul_measure, smul_apply,
      smul_eq_mul]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.mpr hc_pos).le, inv_mul_cancel₀ hc_pos.ne',
      ENNReal.ofReal_one, one_mul]
  have hν_eq : ν_sh = intervalSobolevMeasure ν (fun x ↦ Real.log ((m𝔽 x).val : ℝ)) (-α) α s false := by
    unfold intervalSobolevMeasure
    simp only [Bool.false_eq_true, ↓reduceIte]
    rfl
  let u_ν : Wν := ((hv_mem_sh.of_measure_le_smul ENNReal.ofReal_lt_top.ne hle_νsh).mono_measure hν_eq.ge).toLp v_raw
  obtain ⟨j, _, hj_dense, hj_ae⟩ := modulatedIntervalSobolev_dense (m := m𝔽) hm (-α) α s hI hs
    univ isOpen_univ ordConnected_univ (subset_univ _)
  have hdense_br := hj_dense.comp
    (bruhatCompactSupport_dense_modulatedExponentialDecay (m := m𝔽) (I := univ) hm hsurj
      ordConnected_univ univ_nonempty)
    j.continuous
  have hwd_ν : Measurable (fun g : C𝔽 ↦ ENNReal.ofReal (w_sh (logNorm g))) :=
    ((continuous_intervalSobolevDensity (-α) α s).measurable.comp measurable_logNorm).ennreal_ofReal
  have habs_ν : ν ≪ intervalSobolevMeasure ν (fun x ↦ Real.log ((m𝔽 x).val : ℝ)) (-α) α s false :=
    hν_eq ▸ withDensity_absolutelyContinuous' hwd_ν.aemeasurable
      (ae_of_all _ fun _ ↦ (ENNReal.ofReal_pos.mpr (intervalSobolevDensity_pos (-α) α s _)).ne')
  have hvan_br : ∀ φ : BruhatCompactSupport C𝔽,
      @inner ℂ Wν _ (j (bruhatCompactSupportToModulatedExponentialDecay m𝔽 univ hm hsurj φ)) u_ν = 0 := by
    intro φ
    let ιφ := bruhatCompactSupportToModulatedExponentialDecay m𝔽 univ hm hsurj φ
    rw [L2.inner_def]
    have hwd_int : ∫ g : C𝔽, @inner ℂ ℂ _ (j ιφ g) (u_ν g) ∂ν_sh =
        ∫ g : C𝔽, (ENNReal.ofReal (w_sh (logNorm g))).toReal • @inner ℂ ℂ _ (j ιφ g) (u_ν g) ∂ν :=
      integral_withDensity_eq_integral_toReal_smul (μ := ν) hwd_ν
        (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) (fun g : C𝔽 ↦ @inner ℂ ℂ _ (j ιφ g) (u_ν g))
    have hcongr_m : ∫ g : C𝔽, @inner ℂ ℂ _ (j ιφ g) (u_ν g)
          ∂(intervalSobolevMeasure ν (fun x ↦ Real.log ((m𝔽 x).val : ℝ)) (-α) α s false) =
        ∫ g : C𝔽, @inner ℂ ℂ _ (j ιφ g) (u_ν g) ∂ν_sh :=
      congrArg (fun μ ↦ ∫ g : C𝔽, @inner ℂ ℂ _ (j ιφ g) (u_ν g) ∂μ) hν_eq.symm
    rw [hcongr_m, hwd_int]
    have hrep_j : (j ιφ : C𝔽 → ℂ) =ᵐ[ν] φ.val := (hj_ae ιφ).mono fun g hg ↦ hg
    have hrep_u : (u_ν : C𝔽 → ℂ) =ᵐ[ν] v_raw := habs_ν.ae_le (MemLp.coeFn_toLp _)
    have heq_ν : (fun g : C𝔽 ↦ (ENNReal.ofReal (w_sh (logNorm g))).toReal • @inner ℂ ℂ _ (j ιφ g) (u_ν g)) =ᵐ[ν]
        fun g : C𝔽 ↦ star (φ.val g) * u g * (w (logNorm g) : ℂ) := by
      filter_upwards [hrep_j, hrep_u] with g hgj hgu
      have hwsh_pos := intervalSobolevDensity_pos (-α) α s (logNorm g)
      rw [hgj, hgu, ENNReal.toReal_ofReal hwsh_pos.le, Complex.real_smul, RCLike.inner_apply,
        Complex.star_def]
      dsimp only [v_raw]
      have hwsh0 : (w_sh (logNorm g) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hwsh_pos.ne'
      rw [Complex.ofReal_div]
      field_simp [hwsh0]
      dsimp only [w_sh]
      ring
    rw [integral_congr_ae heq_ν]
    have hsm : ∫ g : C𝔽, star (φ.val g) * u g * (w (logNorm g) : ℂ) ∂μ𝔽 =
        (c : ℂ) * ∫ g : C𝔽, star (φ.val g) * u g * (w (logNorm g) : ℂ) ∂ν := by
      rw [hμ_eq, integral_smul_measure, ENNReal.toReal_ofReal hc_pos.le, Complex.real_smul]
    rw [hpair φ] at hsm
    exact (mul_eq_zero.mp hsm.symm).resolve_left (Complex.ofReal_ne_zero.mpr hc_pos.ne')
  have hvan_all : ∀ v : Wν, @inner ℂ Wν _ v u_ν = 0 := by
    have hclosed : IsClosed {v : Wν | @inner ℂ Wν _ v u_ν = 0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    have hsub : closure (Set.range (⇑j ∘ ⇑(bruhatCompactSupportToModulatedExponentialDecay m𝔽 univ hm hsurj))) ⊆
        {v : Wν | @inner ℂ Wν _ v u_ν = 0} :=
      hclosed.closure_subset_iff.mpr (by rintro _ ⟨φ, rfl⟩; exact hvan_br φ)
    rw [hdense_br.closure_eq] at hsub
    intro v
    exact hsub (Set.mem_univ v)
  have huν0 : u_ν = 0 := inner_self_eq_zero.mp (hvan_all u_ν)
  have hrep_uν : (u_ν : C𝔽 → ℂ) =ᵐ[ν] v_raw := habs_ν.ae_le (MemLp.coeFn_toLp _)
  have hzero_ν : v_raw =ᵐ[ν] 0 := by
    filter_upwards [hrep_uν, habs_ν.ae_le (Lp.coeFn_zero ℂ 2 _)] with g hg h0
    rw [huν0] at hg
    exact hg.symm.trans h0
  have hzero_μ : v_raw =ᵐ[μ𝔽] 0 := by
    rw [Filter.EventuallyEq, ae_iff] at hzero_ν ⊢
    rw [hμ_eq, smul_apply, smul_eq_mul, hzero_ν, mul_zero]
  have hu_ae_μ : (u : C𝔽 → ℂ) =ᵐ[μ𝔽] 0 := by
    filter_upwards [hzero_μ] with g hg
    dsimp only [v_raw, Pi.zero_apply] at hg
    have hrat0 : ((w (logNorm g) / w_sh (logNorm g) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (div_pos (hw_pos _) (intervalSobolevDensity_pos (-α) α s _)).ne'
    exact (mul_eq_zero.mp hg).resolve_right hrat0
  ext1
  exact (weightedSobolevMeasure_absCont w).ae_le
    (hu_ae_μ.trans ((tamagawa_absCont_weightedSobolevMeasure (F := F) hw_cont hw_pos).ae_le
      (Lp.coeFn_zero ℂ 2 (weightedSobolevMeasure F w)).symm))

private lemma exists_general_cornerPairing_ne_zero {α s : ℝ} (hα : 0 ≤ α) (_hs : 0 ≤ s)
    {w : ℝ → ℝ} (hw_cont : Continuous w) (hw_pos : ∀ x, 0 < w x)
    (hw_dom_sharp : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, w x ≤ C * intervalSobolevDensity (-α) α s x)
    (hw_shift_fn : ∀ R ≥ 0, ∃ CR : ℝ, 0 < CR ∧ ∀ x y : ℝ, |x - y| ≤ R → w x ≤ CR * w y)
    (u : Lp ℂ 2 (weightedSobolevMeasure F w)) (hu : u ≠ 0) :
    ∃ (ω : PontryaginDual (ideleClassNorm F).ker) (φ : BruhatCompactSupport C𝔽),
      cornerOrbitProfile w ω φ u 0 ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have : IsFiniteMeasure (normOneProbHaar F) := normOneProbHaar_isFinite
  have : (normOneProbHaar F).IsHaarMeasure := normOneProbHaar_isHaar
  have hpair : ∀ φ : BruhatCompactSupport C𝔽,
      ∫ g : C𝔽, star (φ.val g) * u g * (w (logNorm g) : ℂ) ∂μ𝔽 = 0 := by
    intro φ
    obtain ⟨R, hR, hsupp⟩ := exists_logNorm_bound_tsupport (F := F) φ
    obtain ⟨CR, hCR, hshift⟩ := hw_shift_fn R hR
    have hφ_cont : Continuous φ.val :=
      continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
    obtain ⟨M_raw, hM_raw⟩ := φ.property.2.exists_bound_of_continuousOn hφ_cont.continuousOn
    let Mφ : ℝ := max M_raw 0
    have hMφ_nonneg : 0 ≤ Mφ := le_max_right _ _
    have hMφ : ∀ y ∈ tsupport φ.val, ‖φ.val y‖ ≤ Mφ := fun y hy ↦ (hM_raw y hy).trans (le_max_left _ _)
    let Fφ : (ideleClassNorm F).ker → ℂ := fun k ↦
      ∫ g : C𝔽, star (φ.val (g * (k : C𝔽)⁻¹)) * u g * (w (logNorm g) : ℂ) ∂μ𝔽
    have hKer_joint (ω : PontryaginDual (ideleClassNorm F).ker) :
        Integrable (fun p : (ideleClassNorm F).ker × C𝔽 ↦
          star (φ.val (p.2 * (p.1 : C𝔽)⁻¹ * canonicalNormFlow F (Multiplicative.ofAdd (-0)))) *
            (ω p.1 : ℂ) * u p.2 * (w (logNorm p.2) : ℂ)) ((normOneProbHaar F).prod μ𝔽) :=
      (cornerOrbitProfile_bound_and_integrable hw_cont hw_pos u ω φ hR hsupp hCR hshift 0).1
    have hFφ_cont : Continuous Fφ := by
      let S0 : Set C𝔽 := {g : C𝔽 | |logNorm g - 0| ≤ R}
      have hS0_m : MeasurableSet S0 :=
        measurableSet_le (continuous_abs.measurable.comp (measurable_logNorm.sub measurable_const)) measurable_const
      have habs := tamagawa_absCont_weightedSobolevMeasure (F := F) hw_cont hw_pos
      have hslab := indicator_slab_integrable_and_norm (F := F) hR 0
      have h1_mem : MemLp (fun g : C𝔽 ↦ S0.indicator (fun _ ↦ (1 : ℝ)) g) 2 μ𝔽 := by
        refine (memLp_two_iff_integrable_sq_norm hslab.1.1).mpr ?_
        refine hslab.1.congr (ae_of_all _ fun g ↦ ?_)
        dsimp only
        rw [Real.norm_eq_abs, sq_abs, indicator_apply]
        split_ifs <;> norm_num
      have h2_mem : MemLp (fun g : C𝔽 ↦ S0.indicator (fun g ↦ ‖u g‖ * Real.sqrt (w (logNorm g))) g) 2 μ𝔽 := by
        refine (memLp_two_iff_integrable_sq_norm ?_).mpr ?_
        · exact (((Lp.aestronglyMeasurable u).mono_ac habs).norm.mul
            (Real.continuous_sqrt.measurable.comp
              (hw_cont.measurable.comp measurable_logNorm)).aestronglyMeasurable).indicator hS0_m
        refine ((integrable_sq_mul_weight hw_cont hw_pos u).indicator hS0_m).congr (ae_of_all _ fun g ↦ ?_)
        dsimp only
        rw [Real.norm_eq_abs, sq_abs]
        by_cases hg : g ∈ S0
        · rw [indicator_of_mem hg, indicator_of_mem hg, mul_pow, Real.sq_sqrt (hw_pos _).le]
        · rw [indicator_of_notMem hg, indicator_of_notMem hg]; norm_num
      have hu_int : Integrable (fun g : C𝔽 ↦ S0.indicator (fun g ↦ ‖u g‖ * Real.sqrt (w (logNorm g))) g) μ𝔽 := by
        refine (MemLp.integrable_mul h2_mem h1_mem).congr (ae_of_all _ fun g ↦ ?_)
        by_cases hg : g ∈ S0 <;> simp [hg]
      let B₀ : ℝ := Real.sqrt (CR * w 0) * Mφ
      have hdom_g : Integrable (fun g : C𝔽 ↦ B₀ * S0.indicator (fun g ↦ ‖u g‖ * Real.sqrt (w (logNorm g))) g) μ𝔽 :=
        hu_int.const_mul B₀
      change Continuous (fun k : (ideleClassNorm F).ker ↦
        ∫ g : C𝔽, star (φ.val (g * (k : C𝔽)⁻¹)) * u g * (w (logNorm g) : ℂ) ∂μ𝔽)
      have : FirstCountableTopology (ideleClassNorm F).ker :=
        Topology.IsInducing.subtypeVal.firstCountableTopology
      refine continuous_of_dominated
        (F := fun (k : (ideleClassNorm F).ker) (g : C𝔽) ↦ star (φ.val (g * (k : C𝔽)⁻¹)) * u g * (w (logNorm g) : ℂ))
        (fun k ↦ ?_) (fun k ↦ ae_of_all _ fun g ↦ ?_) hdom_g (ae_of_all _ fun g ↦ ?_)
      · exact (((continuous_star.comp (hφ_cont.comp (continuous_id.mul continuous_const))).aestronglyMeasurable).mul
          ((Lp.aestronglyMeasurable u).mono_ac habs)).mul
          (Complex.continuous_ofReal.comp (hw_cont.comp continuous_logNorm)).aestronglyMeasurable
      · rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg (hw_pos _).le]
        by_cases hz : φ.val (g * (k : C𝔽)⁻¹) = 0
        · simp only [hz, norm_zero, zero_mul]
          exact mul_nonneg (by positivity) (indicator_nonneg (fun _ _ ↦ by positivity) g)
        · have hgk : logNorm (g * (k : C𝔽)⁻¹) = logNorm g := by
            have hk : ideleClassNorm F (k : C𝔽) = 1 := k.property
            change Real.log ((ideleClassNorm F (g * (k : C𝔽)⁻¹)).val : ℝ) = logNorm g
            rw [map_mul, map_inv, hk, inv_one, mul_one]
          have hgS0 : g ∈ S0 := by
            change |logNorm g - 0| ≤ R
            rw [sub_zero, ← hgk]
            exact hsupp _ (subset_tsupport _ hz)
          simp only [hgS0, indicator_of_mem]
          have hw0 : w (logNorm g) ≤ CR * w 0 := hshift _ 0 (by simpa [S0] using hgS0)
          have hw_le : Real.sqrt (w (logNorm g)) ≤ Real.sqrt (CR * w 0) := Real.sqrt_le_sqrt hw0
          have hw_sq : w (logNorm g) = Real.sqrt (w (logNorm g)) * Real.sqrt (w (logNorm g)) :=
            (Real.mul_self_sqrt (hw_pos _).le).symm
          calc ‖φ.val (g * (k : C𝔽)⁻¹)‖ * ‖u g‖ * w (logNorm g)
              ≤ Mφ * ‖u g‖ * (Real.sqrt (CR * w 0) * Real.sqrt (w (logNorm g))) := by
                refine mul_le_mul (mul_le_mul_of_nonneg_right (hMφ _ (subset_tsupport _ hz)) (norm_nonneg _))
                  ?_ (hw_pos _).le (mul_nonneg hMφ_nonneg (norm_nonneg _))
                conv_lhs => rw [hw_sq]
                exact mul_le_mul_of_nonneg_right hw_le (Real.sqrt_nonneg _)
            _ = B₀ * (‖u g‖ * Real.sqrt (w (logNorm g))) := by dsimp only [B₀]; ring
      · exact ((continuous_star.comp (hφ_cont.comp (continuous_const.mul
          (continuous_subtype_val.inv)))).mul_const (u g)).mul_const (w (logNorm g) : ℂ)
    have hfour_zero : ∀ ω : PontryaginDual (ideleClassNorm F).ker, lcaFourier (normOneProbHaar F) Fφ ω = 0 := by
      intro ω
      have hcongr_k : lcaFourier (normOneProbHaar F) Fφ ω =
          cornerOrbitProfile w ω⁻¹ φ u 0 := by
        rw [lcaFourier, cornerOrbitProfile, integral_prod _ (hKer_joint ω⁻¹)]
        refine integral_congr_ae (ae_of_all _ fun k ↦ ?_)
        dsimp only [Fφ]
        rw [← integral_mul_const]
        refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
        dsimp only
        rw [neg_zero, ofAdd_zero, map_one, mul_one,
          show star ((ω k : ℂ)) = (ω⁻¹ k : ℂ) by
            change star (ω k : ℂ) = ((ω k)⁻¹ : ℂ)
            exact eq_inv_of_mul_eq_one_right <| by
              have hnorm : ‖(ω k : ℂ)‖ = 1 := Circle.norm_coe (ω k)
              rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]; norm_num]
        ring
      rw [hcongr_k]
      exact hnone ω⁻¹ φ
    have : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
    have hFφ_ae := ae_eq_zero_of_lcaFourier_eq_zero (normOneProbHaar F)
      (hFφ_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace Fφ)) hfour_zero
    have hFφ_all : Fφ = 0 := (normOneProbHaar F).eq_of_ae_eq hFφ_ae hFφ_cont continuous_zero
    have h1 := congrFun hFφ_all 1
    simpa [Fφ] using h1
  exact hu (zero_of_forall_bruhat_pairing_zero hα _hs hw_cont hw_pos hw_dom_sharp u hpair)

/-- Every nonzero `u : W(α, s)` has some `(ω, φ)` with nonzero corner pairing at `0`. -/
theorem exists_cornerPairing_ne_zero {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (u : W(α, s)) (hu : u ≠ 0) :
    ∃ (ω : PontryaginDual (ideleClassNorm F).ker) (φ : BruhatCompactSupport C𝔽),
      cornerOrbitProfile (intervalSobolevDensity (-α) α s) ω φ
        (intervalToWeightedEquiv (-α) α s u) 0 ≠ 0 :=
  exists_general_cornerPairing_ne_zero hα hs (continuous_intervalSobolevDensity (-α) α s)
    (intervalSobolevDensity_pos (-α) α s) ⟨1, zero_le_one, fun _ ↦ (one_mul _).ge⟩
    (fun _ hR ↦ intervalSobolevDensity_shift_bound hα hs hR)
    (intervalToWeightedEquiv (-α) α s u) (by simpa using hu)

/-- Every nonzero `u : CoshSobolevSpace F α s` has some `(ω, φ)` with nonzero corner pairing at `0`. -/
theorem exists_coshCornerPairing_ne_zero {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (u : CoshSobolevSpace F α s) (hu : u ≠ 0) :
    ∃ (ω : PontryaginDual (ideleClassNorm F).ker) (φ : BruhatCompactSupport C𝔽),
      cornerOrbitProfile (coshSobolevDensity α s) ω φ (coshSobolevToLp F α s u) 0 ≠ 0 :=
  exists_general_cornerPairing_ne_zero hα hs (continuous_coshSobolevDensity α s)
    (coshSobolevDensity_pos α s) ⟨2, zero_le_two, coshSobolevDensity_le_two_mul hα s⟩
    (fun _ hR ↦ coshSobolevDensity_shift_bound hα hs hR) (coshSobolevToLp F α s u) hu

end CornerPairingNonvanishing

end RiemannMasullo.Isolated
