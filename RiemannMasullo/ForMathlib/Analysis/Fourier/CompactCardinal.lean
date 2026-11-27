module
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public noncomputable section
open MeasureTheory Set Function
open scoped FourierTransform SchwartzMap Convolution ContDiff Pointwise
namespace RiemannMasullo

private theorem fourier_normalized_interval_mesh {L : ℝ} (hL : 0 < L) (j : ℤ) :
    𝓕 ((Ioc 0 L).indicator (fun _ : ℝ ↦ ((1 / L : ℝ) : ℂ))) ((j : ℝ) / L) =
      if j = 0 then 1 else 0 := by
  let : Fact (0 < L) := ⟨hL⟩
  have hc := fourierCoeff_eq_intervalIntegral (fun _ : AddCircle L ↦ (1 : ℂ)) j 0
  rw [fourierCoeff_const] at hc
  have hleft : (Pi.single 0 (1 : ℂ) : ℤ → ℂ) j = if j = 0 then 1 else 0 := by
    by_cases hj : j = 0 <;> simp [hj]
  rw [hleft, zero_add] at hc
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hfun : (fun x : ℝ ↦ Complex.exp (↑(-2 * Real.pi * x * ((j : ℝ) / L)) * Complex.I) •
      (Ioc 0 L).indicator (fun _ : ℝ ↦ ((1 / L : ℝ) : ℂ)) x) =
      (Ioc 0 L).indicator (fun x : ℝ ↦ (1 / L : ℝ) •
        (fourier (-j) (x : AddCircle L) • (1 : ℂ))) := by
    funext x
    by_cases hx : x ∈ Ioc 0 L
    · simp only [indicator_of_mem hx, fourier_coe_apply, smul_eq_mul,
        Complex.real_smul, mul_one]
      rw [mul_comm]
      congr 1
      congr 1
      push_cast
      ring
    · simp [hx]
  rw [hfun, integral_indicator measurableSet_Ioc, integral_smul,
    ← intervalIntegral.integral_of_le hL.le]
  exact hc.symm


private theorem exists_compact_schwartz_mesh_unit {L : ℝ} (hL : 0 < L) (U : ℝ) :
    ∃ u : 𝓢(ℝ, ℂ), HasCompactSupport (u : ℝ → ℂ) ∧
      (∀ x, u x ≠ 0 → x < U) ∧ ∀ j : ℤ, 𝓕 u ((j : ℝ) / L) = if j = 0 then 1 else 0 := by
  let f := (Ioc 0 L).indicator (fun _ : ℝ ↦ ((1 / L : ℝ) : ℂ))
  have hfc : HasCompactSupport f := .of_support_subset_isCompact isCompact_Icc
    (support_indicator_subset.trans Ioc_subset_Icc_self)
  have hfi : Integrable f := (integrable_indicator_iff measurableSet_Ioc).mpr
    (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  let b : ContDiffBump (U - L - 3) := ⟨1, 2, one_pos, one_lt_two⟩
  let η : ℝ → ℂ := fun x ↦ (b.normed volume x : ℂ)
  have hηc : HasCompactSupport η := b.hasCompactSupport_normed.comp_left Complex.ofReal_zero
  have hηs : ContDiff ℝ ∞ η := Complex.ofRealCLM.contDiff.comp b.contDiff_normed
  have hηi : Integrable η := hηs.continuous.integrable_of_hasCompactSupport hηc
  have hη0 : 𝓕 η 0 = 1 := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    rw [integral_complex_ofReal, b.integral_normed, Complex.ofReal_one]
  let u := (hfc.convolution (μ := volume) (L := ContinuousLinearMap.mul ℂ ℂ) hηc).toSchwartzMap
    (hηc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) hfi.locallyIntegrable hηs)
  have hupp (x : ℝ) (hx : u x ≠ 0) : x < U := by
    obtain ⟨y, hy, z, hz, hxyz⟩ := support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ) hx
    have hyL : y ≤ L := (support_indicator_subset hy).2
    have hzη : b.normed volume z ≠ 0 := by simpa only [mem_support, η, ne_eq, Complex.ofReal_eq_zero] using hz
    have hzball : z ∈ Metric.ball (U - L - 3) 2 := by
      rw [← b.support_normed_eq (μ := (volume : Measure ℝ))]
      exact hzη
    have hzb := (abs_lt.mp (show |z - (U - L - 3)| < 2 from hzball)).2
    linarith
  refine ⟨u, hfc.convolution (ContinuousLinearMap.mul ℂ ℂ) hηc, hupp, fun j ↦ ?_⟩
  change 𝓕 (f ⋆[ContinuousLinearMap.mul ℂ ℂ] η) ((j : ℝ) / L) = _
  rw [Real.fourier_mul_convolution_eq hfi hηi, fourier_normalized_interval_mesh hL]
  by_cases hj : j = 0
  · simp [hj, hη0]
  · simp [hj]

/-- A compact smooth function with value one at the zero frequency and double
zeros at all other points of a prescribed Fourier lattice. -/
theorem exists_compact_schwartz_double_mesh {L : ℝ} (hL : 0 < L) (U : ℝ) :
    ∃ b : 𝓢(ℝ, ℂ), HasCompactSupport (b : ℝ → ℂ) ∧
      (tsupport (b : ℝ → ℂ) ⊆ Iio U) ∧ (∀ j : ℤ, 𝓕 b ((j : ℝ) / L) = if j = 0 then 1 else 0) ∧
      ∀ j : ℤ, j ≠ 0 → deriv (fun x ↦ 𝓕 b x) ((j : ℝ) / L) = 0 := by
  obtain ⟨u, hu, hupp, hmesh⟩ := exists_compact_schwartz_mesh_unit hL (U / 2 - 1)
  let b := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) u u
  have hb (x : ℝ) : b x = (u ⋆[ContinuousLinearMap.mul ℂ ℂ] u) x :=
    SchwartzMap.convolution_apply _ u u x
  have hbc : HasCompactSupport (b : ℝ → ℂ) := by
    rw [show (b : ℝ → ℂ) = (u ⋆[ContinuousLinearMap.mul ℂ ℂ] u) from funext hb]
    exact hu.convolution (ContinuousLinearMap.mul ℂ ℂ) hu
  have hB : (⇑(𝓕 b : 𝓢(ℝ, ℂ))) = fun x ↦ 𝓕 u x * 𝓕 u x := by
    ext x
    dsimp only [b]
    rw [SchwartzMap.fourier_convolution]
    rfl
  refine ⟨b, hbc, ?_, fun j ↦ ?_, fun j hj ↦ ?_⟩
  · have hsub : support (b : ℝ → ℂ) ⊆ Iic (U - 2) := by
      intro x hx
      rw [mem_support, hb] at hx
      obtain ⟨y, hy, z, hz, hxyz⟩ := support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ) hx
      have hh : x < U - 2 := by linarith [hupp y hy, hupp z hz]
      exact hh.le
    exact (closure_minimal hsub isClosed_Iic).trans (fun x hx ↦ by
      change x < U
      change x ≤ U - 2 at hx
      linarith)
  · rw [congrFun hB, hmesh]
    split_ifs <;> simp
  · rw [hB, deriv_fun_mul (𝓕 u).differentiable.differentiableAt
      (𝓕 u).differentiable.differentiableAt, hmesh, ite_eq_right hj]
    simp

end RiemannMasullo
