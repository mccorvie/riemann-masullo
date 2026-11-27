module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

public section

namespace RiemannMasullo.Selberg

open Complex
open scoped Topology

private theorem thetaArg_im_pos {z : ℂ} (hz : |z.im| < Real.pi / 4) :
    0 < (exp (z + z) * I).im := by
  rw [mul_I_im, exp_re, add_im]
  apply mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo _)
  obtain ⟨hl, hu⟩ := abs_lt.mp hz
  constructor <;> linarith

private theorem K_eq_theta {z : ℂ} (hz : |z.im| < Real.pi / 4) :
    K z = (exp (z / 2) * jacobiTheta (exp (z + z) * I) -
      exp (z / 2) - exp (-z / 2)) / 2 := by
  have hψ : psi (exp z) = (jacobiTheta (exp (z + z) * I) - 1) / 2 := by
    rw [← (hasSum_nat_jacobiTheta (thetaArg_im_pos hz)).tsum_eq]
    apply tsum_congr
    intro n
    congr 1
    push_cast
    rw [exp_add]
    linear_combination -(Real.pi : ℂ) * ((n : ℂ) + 1)^2 * (exp z)^2 * I_sq
  rw [K, hψ]
  ring

private theorem theta_neg {z : ℂ} (hz : |z.im| < Real.pi / 4) :
    jacobiTheta (exp (-z + -z) * I) = exp z * jacobiTheta (exp (z + z) * I) := by
  have hinv := jacobiTheta_S_smul ⟨_, thetaArg_im_pos hz⟩
  rw [UpperHalfPlane.modular_S_smul] at hinv
  change jacobiTheta (-(exp (z + z) * I))⁻¹ =
    (-I * (exp (z + z) * I)) ^ (1 / 2 : ℂ) * _ at hinv
  have harg : (-(exp (z + z) * I))⁻¹ = exp (-z + -z) * I := by
    rw [← neg_add, exp_neg, inv_neg, mul_inv_rev, inv_I]
    ring
  have hbase : -I * (exp (z + z) * I) = exp (z + z) := by
    linear_combination -exp (z + z) * I_sq
  obtain ⟨hl, hu⟩ := abs_lt.mp hz
  have hlog : log (exp (z + z)) = z + z := by
    apply log_exp <;> rw [add_im] <;> linarith [Real.pi_pos]
  rwa [harg, hbase, cpow_def_of_ne_zero (exp_ne_zero _), hlog,
    show (z + z) * (1 / 2) = z by ring] at hinv

/-- Card 15. On the open strip |Im z| < π/4, the corrected theta kernel is even, commutes with
conjugation, and is complex differentiable.
Titchmarsh, §10.10, p. 269, theta transformation, also §10.1 p. 254. -/
theorem kernel_symmetry {z : ℂ} (hz : |z.im| < Real.pi/4) :
    K (-z) = K z ∧ K (star z) = star (K z) ∧ DifferentiableAt ℂ K z := by
  refine ⟨?_, ?_, ?_⟩
  · have hn : |(-z).im| < Real.pi / 4 := by simpa using hz
    rw [K_eq_theta hn, K_eq_theta hz, theta_neg hz, neg_neg, ← mul_assoc, ← exp_add,
      show -z / 2 + z = z / 2 by ring]
    ring
  · simp [K, psi, Complex.conj_tsum, ← exp_conj, map_ofNat]
  · have hd := (differentiableAt_jacobiTheta (thetaArg_im_pos hz)).comp z
      (f := fun w : ℂ ↦ exp (w + w) * I) (by fun_prop)
    apply DifferentiableAt.congr_of_eventuallyEq (f := fun w : ℂ ↦
      (exp (w / 2) * jacobiTheta (exp (w + w) * I) - exp (w / 2) - exp (-w / 2)) / 2)
    · unfold Function.comp at hd
      fun_prop
    · filter_upwards [(isOpen_lt continuous_im.abs continuous_const).mem_nhds hz] with w hw
      exact K_eq_theta hw

end RiemannMasullo.Selberg
