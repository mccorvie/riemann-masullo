module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.PSeries

@[expose] public noncomputable section

namespace RiemannMasullo

open scoped ContDiff FourierTransform SchwartzMap

/-- The periodization of a Schwartz function over the integer lattice is smooth. -/
theorem schwartz_contDiff_periodization (f : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ ∞ (fun x : ℝ ↦ ∑' n : ℤ, f (x + n)) := by
  let a (u : ℝ) : ℂ := 2 * Real.pi * Complex.I * u
  let b (k : ℕ) (n : ℤ) := a n ^ k * (𝓕 f) n
  let t (n : ℤ) (x : ℝ) := (𝓕 f) n * fourier n (x : AddCircle (1 : ℝ))
  have hd (n : ℤ) (k : ℕ) :
      iteratedDeriv k (t n) = fun x : ℝ ↦ b k n * fourier n (x : AddCircle (1 : ℝ)) := by
    induction k with
    | zero => simp [b, t]
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      convert ((hasDerivAt_fourier 1 n x).const_mul (b k n)).deriv using 1
      simp [b, a, pow_succ]
      ring
  have hb (k : ℕ) : Summable fun n : ℤ ↦ ‖b k n‖ := by
    have hg : (fun u : ℝ ↦ a u ^ k).HasTemperateGrowth := by
      dsimp [a]
      fun_prop
    let F := SchwartzMap.smulLeftCLM ℂ (fun u : ℝ ↦ a u ^ k) (𝓕 f)
    have hs : Summable (fun n : ℤ ↦ ‖F n‖) :=
      summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
        ((F.isBigO_cocompact_rpow (-2)).norm_left.comp_tendsto Int.tendsto_coe_cofinite)
    simpa only [F, b, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul] using hs
  simp_rw [f.tsum_eq_tsum_fourier]
  apply contDiff_tsum (f := t) (v := fun k n ↦ ‖b k n‖)
  · intro n
    have hcoe : ContDiff ℝ ∞ ((↑) : ℝ → ℂ) := Complex.ofRealCLM.contDiff
    simp only [t, fourier_coe_apply]
    fun_prop
  · exact fun k _ ↦ hb k
  · intro k n x _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hd, norm_mul]
    simp only [fourier_apply, Circle.norm_coe, mul_one, le_rfl]

open ContinuousMap Filter MeasureTheory Set in
open scoped Asymptotics in
/-- If a continuously differentiable function and its derivative both decay at least as
fast as the inverse square, its Fourier samples on the integer lattice are absolutely summable. -/
theorem summable_norm_fourier_int_of_isBigO {g : ℝ → ℂ} (hg : ContDiff ℝ 1 g)
    (h : g =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-2 : ℝ)))
    (h' : deriv g =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-2 : ℝ))) :
    Summable (fun m : ℤ ↦ ‖𝓕 g (m : ℝ)‖) := by
  have hs (v : C(ℝ, ℂ)) (hv : (v : ℝ → ℂ) =O[cocompact ℝ] (fun x : ℝ ↦ |x| ^ (-2 : ℝ)))
      (K : TopologicalSpace.Compacts ℝ) :
      Summable (fun m : ℤ ↦ ‖(v.comp (ContinuousMap.addRight m)).restrict K‖) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      ((isBigO_norm_restrict_cocompact v (by norm_num) hv K).comp_tendsto Int.tendsto_coe_cofinite)
  -- Periodize the derivative and use Parseval to get square-summable samples.
  let v : C(ℝ, ℂ) := ⟨deriv g, hg.continuous_deriv (by simp)⟩
  let V : C(UnitAddCircle, ℂ) :=
    ⟨(v.periodic_tsum_comp_add_zsmul 1).lift,
      continuous_coinduced_dom.mpr (map_continuous _)⟩
  have hv (m : ℤ) : fourierCoeff V m = 𝓕 (deriv g) (m : ℝ) :=
    Real.fourierCoeff_tsum_comp_add (hs v h') m
  have hsq : Summable (fun m : ℤ ↦ ‖𝓕 (deriv g) (m : ℝ)‖ ^ 2) := by
    simpa only [fourierCoeff_toLp, hv] using
      (hasSum_sq_fourierCoeff (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ V)).summable
  let u : C(ℝ, ℂ) := ⟨g, hg.continuous⟩
  let K : TopologicalSpace.Compacts ℝ := ⟨Icc 0 1, isCompact_Icc⟩
  have hi : Integrable g := Real.integrable_of_summable_norm_Icc (f := u) (hs u h K)
  have hi' : Integrable (deriv g) := Real.integrable_of_summable_norm_Icc (f := v) (hs v h' K)
  -- On nonzero modes the derivative contributes a factor of `2 * π * |m|`.
  have hpow : Summable (fun m : ℤ ↦ (|(m : ℝ)|⁻¹) ^ (2 : ℝ)) := by
    simpa only [Real.inv_rpow (abs_nonneg _), Real.rpow_neg (abs_nonneg _)] using
      Real.summable_abs_int_rpow one_lt_two
  have hprod := Real.summable_mul_of_Lp_Lq_of_nonneg Real.HolderConjugate.two_two
    (fun m : ℤ ↦ norm_nonneg (𝓕 (deriv g) (m : ℝ)))
    (fun m : ℤ ↦ inv_nonneg.mpr (abs_nonneg (m : ℝ)))
    (by simpa only [Real.rpow_two] using hsq) hpow
  apply (hprod.mul_left ((2 * Real.pi)⁻¹)).of_norm_bounded_eventually
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with m hm
  have hm' : |(m : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hm)
  rw [Real.fourier_deriv hi (hg.differentiable (by simp)) hi', norm_smul]
  simp only [Complex.norm_mul, Complex.norm_ofNat 2, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one, abs_of_nonneg (norm_nonneg _)]
  field_simp [Real.pi_ne_zero, hm']
  exact le_rfl

end RiemannMasullo
