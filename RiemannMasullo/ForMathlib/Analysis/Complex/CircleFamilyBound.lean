module

public import Mathlib.Analysis.Complex.Poisson
import Mathlib.Tactic

/-! # A mean-square detector for finite families on a disk -/

public section

open Classical Complex Filter Metric Real Set
open scoped Topology

namespace RiemannMasullo

private theorem norm_sq_le_circleAverage {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c w : ℂ} {r R : ℝ} (hr : 0 ≤ r) (hR : r < R) (hw : w ∈ closedBall c r) :
    ‖f w‖^2 ≤ (R+r)/(R-r) * circleAverage (fun z ↦ ‖f z‖^2) c R := by
  have hR₀ := hr.trans_lt hR
  let K (z : ℂ) := ((z-c+(w-c))/((z-c)-(w-c))).re
  have hnorm : ‖w-c‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hw
  have hden (z : ℂ) (hz : z ∈ sphere c |R|) : R-r ≤ ‖(z-c)-(w-c)‖ := by
    have he : ‖z-c‖ = R := (show ‖z-c‖ = |R| by simpa only [mem_sphere,dist_eq_norm] using hz).trans (abs_of_pos hR₀)
    linarith [norm_sub_norm_le (z-c) (w-c)]
  have hbound (z : ℂ) (hz : z ∈ sphere c |R|) : |K z| ≤ (R+r)/(R-r) := by
    have he : ‖z-c‖ = R := (show ‖z-c‖ = |R| by simpa only [mem_sphere,dist_eq_norm] using hz).trans (abs_of_pos hR₀)
    apply (Complex.abs_re_le_norm _).trans
    rw [norm_div]
    exact div_le_div₀ (by linarith) ((norm_add_le _ _).trans (by linarith)) (sub_pos.mpr hR) (hden z hz)
  have hnum : Continuous (fun z : ℂ ↦ z-c+(w-c)) := by fun_prop
  have hsub : Continuous (fun z : ℂ ↦ (z-c)-(w-c)) := by fun_prop
  have hK : ContinuousOn K (sphere c |R|) := continuous_re.comp_continuousOn
    (hnum.continuousOn.div hsub.continuousOn
      (fun z hz ↦ norm_pos_iff.mp ((sub_pos.mpr hR).trans_le (hden z hz))))
  have hw' : w ∈ ball c R := lt_of_le_of_lt (show dist w c ≤ r from hw) hR
  have hF : circleAverage (fun z ↦ K z • (f z)^2) c R = (f w)^2 := by
    simpa only [K, Pi.pow_apply] using
      ((hf.pow 2).diffContOnCl (s := ball c R)).circleAverage_re_herglotzRieszKernel_smul' hw'
  calc ‖f w‖^2 = ‖circleAverage (fun z ↦ K z • f z ^ 2) c R‖ := by rw [hF,norm_pow]
       _ ≤ circleAverage (fun z ↦ ‖K z • f z ^ 2‖) c R := norm_circleAverage_le_circleAverage_norm
       _ ≤ circleAverage (fun z ↦ ((R+r)/(R-r)) • ‖f z‖^2) c R := by
         refine circleAverage_mono ?_ ?_ ?_
         · apply ContinuousOn.circleIntegrable'
           apply ContinuousOn.norm
           exact hK.smul (hf.continuous.continuousOn.pow 2)
         · apply ContinuousOn.circleIntegrable'
           exact (continuousOn_const (c := (R+r)/(R-r))).smul (hf.continuous.norm.continuousOn.pow 2)
         · intro z hz
           rw [norm_smul,Real.norm_eq_abs,norm_pow,smul_eq_mul]
           exact mul_le_mul_of_nonneg_right (hbound z hz) (sq_nonneg _)
       _ = _ := circleAverage_fun_smul

/-- A uniform mean-square bound on one circle controls the number of
analytic functions in a finite family attaining modulus at least one in
the inner disk. The evaluation point can vary with the function. -/
theorem card_large_inside_disk_le {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ S, Differentiable ℂ (f i)) {c : ℂ} {r R B : ℝ} (hr : 0 ≤ r) (hR : r < R)
    (hlarge : ∀ i ∈ S, ∃ w ∈ closedBall c r, 1 ≤ ‖f i w‖)
    (hmean : ∀ z ∈ sphere c |R|, ∑ i ∈ S, ‖f i z‖^2 ≤ B) :
    (S.card : ℝ) ≤ (R+r)/(R-r)*B := by
  let C := (R+r)/(R-r)
  have hC : 0 ≤ C := div_nonneg (by linarith) (sub_nonneg.mpr hR.le)
  have hrow (i : ι) (hi : i ∈ S) : 1 ≤ C * circleAverage (fun z ↦ ‖f i z‖^2) c R := by
    obtain ⟨w,hw,hw'⟩ := hlarge i hi
    exact (one_le_pow₀ hw').trans (norm_sq_le_circleAverage (hf i hi) hr hR hw)
  calc (S.card : ℝ) = ∑ _ ∈ S, (1:ℝ) := by simp
       _ ≤ ∑ i ∈ S, C * circleAverage (fun z ↦ ‖f i z‖^2) c R := Finset.sum_le_sum hrow
       _ = C * circleAverage (fun z ↦ ∑ i ∈ S, ‖f i z‖^2) c R := by
         rw [← Finset.mul_sum,circleAverage_fun_sum (f := fun i z ↦ ‖f i z‖^2)
           (fun i hi ↦ ((hf i hi).continuous.norm.pow 2).continuousOn.circleIntegrable')]
       _ ≤ _ := mul_le_mul_of_nonneg_left (circleAverage_mono_on_of_le_circle
         ((continuous_finsetSum _ (fun i hi ↦ (hf i hi).continuous.norm.pow 2)).continuousOn.circleIntegrable') hmean) hC

end RiemannMasullo
