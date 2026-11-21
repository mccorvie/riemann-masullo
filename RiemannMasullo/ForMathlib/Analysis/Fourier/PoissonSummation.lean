module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Fourier.PoissonSummation
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

end RiemannMasullo
