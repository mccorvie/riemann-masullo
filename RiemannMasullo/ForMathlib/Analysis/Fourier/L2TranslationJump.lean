module

public import Mathlib.Analysis.Fourier.LpSpace
public import RiemannMasullo.ForMathlib.Analysis.Fourier.JumpForm
import Mathlib.MeasureTheory.Function.Holder

/-! # Exact Plancherel law for translations of actual L² vectors -/

public noncomputable section

open MeasureTheory
open scoped ENNReal NNReal FourierTransform SchwartzMap

namespace RiemannMasullo

local notation "JumpL2" => Lp ℂ 2 (volume : Measure ℝ)

/-- Pullback by translation, acting on equivalence classes. -/
noncomputable def jumpTranslate (h : ℝ) : JumpL2 →ₗᵢ[ℂ] JumpL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (· + h) (measurePreserving_add_right volume h)

theorem jumpTranslate_ae (h : ℝ) (f : JumpL2) :
    jumpTranslate h f =ᵐ[volume] fun x ↦ f (x + h) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume h)

private theorem jumpCharacter_memLp (h : ℝ) :
    MemLp (fun ξ : ℝ ↦ (𝐞 (h * ξ) : ℂ)) ∞ volume :=
  memLp_top_of_bound (by fun_prop) 1 (ae_of_all _ fun ξ ↦ by simp)

/-- The bounded Fourier-side character multiplier. -/
noncomputable def jumpModulate (h : ℝ) : JumpL2 →L[ℂ] JumpL2 :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2 ((jumpCharacter_memLp h).toLp _)

theorem jumpModulate_ae (h : ℝ) (f : JumpL2) :
    jumpModulate h f =ᵐ[volume] fun ξ ↦ (𝐞 (h * ξ) : ℂ) * f ξ := by
  have hm : jumpModulate h f =ᵐ[volume] fun ξ ↦ ((jumpCharacter_memLp h).toLp _) ξ * f ξ :=
    (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder ((jumpCharacter_memLp h).toLp _) f
  filter_upwards [hm, (jumpCharacter_memLp h).coeFn_toLp] with ξ h₁ h₂
  rw [h₁, h₂]

/-- Translation and character multiplication intertwine on all of actual Fourier L². -/
theorem l2_fourier_jumpTranslate (f : JumpL2) (h : ℝ) :
    𝓕 (jumpTranslate h f) = jumpModulate h (𝓕 f) := by
  let F := Lp.fourierTransformₗᵢ ℝ ℂ
  refine DenseRange.induction_on
    (p := fun g : JumpL2 ↦ 𝓕 (jumpTranslate h g) = jumpModulate h (𝓕 g))
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
    (isClosed_eq (F.continuous.comp (jumpTranslate h).continuous)
      ((jumpModulate h).continuous.comp F.continuous)) fun g ↦ ?_
  let t := g.compSubConstCLM ℂ (-h)
  have ht : jumpTranslate h (g.toLp 2 volume) = t.toLp 2 volume := by
    apply Lp.ext
    have hc := (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp
      (g.coeFn_toLp 2 volume)
    filter_upwards [jumpTranslate_ae h (g.toLp 2 volume), hc, t.coeFn_toLp 2 volume]
      with x hx hy hz
    rw [hx, hz]
    simpa [Function.comp_def, t, sub_neg_eq_add] using hy
  change 𝓕 (jumpTranslate h (g.toLp 2 volume)) = jumpModulate h (𝓕 (g.toLp 2 volume))
  rw [ht, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 t).coeFn_toLp 2 volume, jumpModulate_ae h ((𝓕 g).toLp 2 volume),
    (𝓕 g).coeFn_toLp 2 volume] with ξ h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  simp only [SchwartzMap.fourier_coe]
  convert congrFun (Fourier.fourierIntegral_comp_add_right 𝐞 volume (g : ℝ → ℂ) h) ξ
    using 1 <;> simp [t, Real.fourier_eq, Fourier.fourierIntegral, VectorFourier.fourierIntegral,
      sub_neg_eq_add, Circle.smul_def, mul_comm ξ]

/-- Squared mass of an L² representative, including the normalization as an extended real. -/
theorem l2_lintegral_norm_sq (f : JumpL2) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) = ‖f‖ₑ ^ 2 := by
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [Lp.eNorm_def]
  simpa using (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    (Lp.aestronglyMeasurable f)).symm

/-- Plancherel's translation-difference identity with arbitrary L² representatives. -/
theorem l2_lintegral_sq_translate_sub (f : JumpL2) (h : ℝ) :
    (∫⁻ x, ENNReal.ofReal (‖f (x + h) - f x‖ ^ 2)) =
      ∫⁻ ξ, ENNReal.ofReal (‖(𝐞 (h * ξ) : ℂ) - 1‖ ^ 2) *
        ENNReal.ofReal (‖(𝓕 f : JumpL2) ξ‖ ^ 2) := by
  let d := jumpTranslate h f - f
  have hd : d =ᵐ[volume] fun x ↦ f (x + h) - f x := by
    filter_upwards [Lp.coeFn_sub (jumpTranslate h f) f, jumpTranslate_ae h f] with x hx hy
    change d x = jumpTranslate h f x - f x at hx
    rw [hx, hy]
  have hF : 𝓕 d = jumpModulate h (𝓕 f) - 𝓕 f := by
    change (Lp.fourierTransformₗᵢ ℝ ℂ) (jumpTranslate h f - f) = _
    rw [map_sub]; exact congrArg (· - 𝓕 f) (l2_fourier_jumpTranslate f h)
  calc
    _ = ∫⁻ x, ENNReal.ofReal (‖d x‖ ^ 2) := lintegral_congr_ae (hd.mono fun x e ↦ by
      change d x = f (x + h) - f x at e
      exact congrArg (fun z : ℂ ↦ ENNReal.ofReal (‖z‖ ^ 2)) e.symm)
    _ = ∫⁻ ξ, ENNReal.ofReal (‖(𝓕 d : JumpL2) ξ‖ ^ 2) := by
      rw [l2_lintegral_norm_sq, l2_lintegral_norm_sq, ← ofReal_norm, ← ofReal_norm,
        Lp.norm_fourier_eq]
    _ = _ := by
      rw [hF]
      apply lintegral_congr_ae
      filter_upwards [Lp.coeFn_sub (jumpModulate h (𝓕 f)) (𝓕 f), jumpModulate_ae h (𝓕 f)]
        with ξ hx hy
      simp only [Pi.sub_apply] at hx
      rw [hx, hy]
      rw [show (𝐞 (h * ξ) : ℂ) * (𝓕 f : JumpL2) ξ - (𝓕 f : JumpL2) ξ =
        ((𝐞 (h * ξ) : ℂ) - 1) * (𝓕 f : JumpL2) ξ by ring,
        norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]

end RiemannMasullo
