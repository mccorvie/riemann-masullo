module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.Integrable
public import Mathlib.Analysis.Fourier.Convolution
import Mathlib.MeasureTheory.Function.L2Space

/-! # Removing a Fourier phase from a convolution in real L² -/

public noncomputable section

open Filter MeasureTheory
open scoped Convolution FourierTransform

namespace RiemannMasullo

local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "fourierL2" => Lp.fourierTransformₗᵢ ℝ ℂ
local notation "cmul" => ContinuousLinearMap.mul ℂ ℂ

/-- Convolution with an integrable kernel sends bounded, integrable profiles
to integrable profiles of finite (L²) norm. -/
theorem memLp_mul_convolution_two_of_integrable_of_bound
    {k f : ℝ → ℂ} (hk : Integrable k) (hf : Integrable f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) : MemLp (k ⋆[cmul] f) 2 volume := by
  have hconv : Integrable (k ⋆[cmul] f) := hk.integrable_convolution cmul hf
  have hBound (x : ℝ) : ‖(k ⋆[cmul] f) x‖ ≤ (∫ y, ‖k y‖) * C := by
    rw [MeasureTheory.convolution_def, ← integral_mul_const]
    exact norm_integral_le_of_norm_le (hk.norm.mul_const C)
      (ae_of_all _ fun y ↦ by
        change ‖k y * f (x - y)‖ ≤ ‖k y‖ * C
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _))
  apply (memLp_two_iff_integrable_sq_norm hconv.aestronglyMeasurable).2
  simpa only [pow_two] using hconv.norm.mul_bdd hconv.norm.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by rw [norm_norm]; exact hBound x)

/-- The real (L²) Fourier multiplier with symbol `star m` takes the
convolution with phase-corrected kernel `q` back to convolution with `k`.
The bounded integrable input supplies explicit representatives of both outputs. -/
theorem exists_L2_convolution_phase_transfer
    (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2) (m : ℝ → ℂ)
    (hU : ∀ v, (fourierL2 (U v) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦
      star (m ξ) * (fourierL2 v : FlatL2) ξ)
    (hm : ∀ᵐ ξ ∂volume, ‖m ξ‖ = 1)
    {k q f : ℝ → ℂ} (hk : Integrable k) (hq : Integrable q)
    (hf : Integrable f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C)
    (hphase : ∀ᵐ ξ ∂volume, 𝓕 q ξ = m ξ * 𝓕 k ξ) :
    ∃ v w : FlatL2, U v = w ∧
      (v : ℝ → ℂ) =ᵐ[volume] (q ⋆[cmul] f) ∧
      (w : ℝ → ℂ) =ᵐ[volume] (k ⋆[cmul] f) := by
  let v := (memLp_mul_convolution_two_of_integrable_of_bound hq hf hC).toLp (q ⋆[cmul] f)
  let w := (memLp_mul_convolution_two_of_integrable_of_bound hk hf hC).toLp (k ⋆[cmul] f)
  have hv : (v : ℝ → ℂ) =ᵐ[volume] (q ⋆[cmul] f) := MemLp.coeFn_toLp _
  have hw : (w : ℝ → ℂ) =ᵐ[volume] (k ⋆[cmul] f) := MemLp.coeFn_toLp _
  have hv₁ : Integrable (v : ℝ → ℂ) := (hq.integrable_convolution cmul hf).congr hv.symm
  have hw₁ : Integrable (w : ℝ → ℂ) := (hk.integrable_convolution cmul hf).congr hw.symm
  have hvF : (fourierL2 v : ℝ → ℂ) =ᵐ[volume] 𝓕 (q ⋆[cmul] f) :=
    (fourier_L2_coeFn_of_integrable v hv₁).trans
      (ae_of_all _ fun ξ ↦ Real.fourier_congr_ae hv ξ)
  have hwF : (fourierL2 w : ℝ → ℂ) =ᵐ[volume] 𝓕 (k ⋆[cmul] f) :=
    (fourier_L2_coeFn_of_integrable w hw₁).trans
      (ae_of_all _ fun ξ ↦ Real.fourier_congr_ae hw ξ)
  refine ⟨v, w, (fourierL2).injective (Lp.ext ?_), hv, hw⟩
  filter_upwards [hU v, hvF, hwF, hm, hphase] with ξ hξU hξv hξw hξm hξphase
  have hOne : star (m ξ) * m ξ = 1 := by
    change (starRingEnd ℂ) (m ξ) * m ξ = 1
    rw [mul_comm]
    simpa only [Complex.normSq_eq_norm_sq, hξm, one_pow, Complex.ofReal_one]
      using Complex.mul_conj (m ξ)
  rw [hξU, hξv, hξw, Real.fourier_mul_convolution_eq hq hf,
    Real.fourier_mul_convolution_eq hk hf, hξphase, ← mul_assoc, ← mul_assoc, hOne, one_mul]

end RiemannMasullo
