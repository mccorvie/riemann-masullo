module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

public section

open MeasureTheory Set

namespace RiemannMasullo

/-- The integral of a continuous real function over a fixed-length window is continuous in its start. -/
theorem spectralLineJet_selberg_continuousWindow {f : ℝ → ℝ} (hf : Continuous f) (h : ℝ) :
    Continuous (fun t : ℝ ↦ ∫ u in t..t + h, f u) := by
  let P (t : ℝ) := ∫ u in (0 : ℝ)..t, f u
  have hP : Continuous P := intervalIntegral.continuous_primitive (fun a b ↦ hf.intervalIntegrable a b) 0
  apply ((hP.comp (continuous_id.add_const h)).sub hP).congr
  intro t
  simpa [P] using (eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 t) (hf.intervalIntegrable t (t + h)))).symm

/-- Averaging a continuous function on sliding length-`h` windows costs at
most `h²` times its second moment on the enlarged interval. -/
theorem spectralLineJet_selberg_window_L2 (f : ℝ → ℝ) (hf : Continuous f)
    {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h) :
    (∫ t in a..b, (∫ u in t..t+h, f u)^2) ≤ h^2 * ∫ u in a..b+h, (f u)^2 := by
  rcases hh.eq_or_lt with rfl | hhpos
  · simp
  let P (u : ℝ) := ∫ v in a..u, (f v)^2
  have hp : Continuous P := intervalIntegral.continuous_primitive (fun _ _ ↦ (hf.pow 2).intervalIntegrable ..) a
  have hps (t : ℝ) : (∫ v in t..t+h, (f v)^2) = P (t+h) - P t :=
    (intervalIntegral.integral_interval_sub_left ((hf.pow 2).intervalIntegrable ..) ((hf.pow 2).intervalIntegrable ..)).symm
  have hcs (t : ℝ) : (∫ v in t..t+h, f v)^2 ≤ h*(P (t+h)-P t) := by
    let J := ∫ v in t..t+h, f v
    have he (v : ℝ) : (h*f v - J)^2 = h^2*(f v)^2 - (2*h*J)*f v + J^2 := by ring
    have hpos : 0 ≤ ∫ v in t..t+h, (h*f v-J)^2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun _ _ ↦ by positivity)
    simp_rw [he] at hpos
    have hs : Continuous (fun v ↦ h^2*(f v)^2) := continuous_const.mul (hf.pow 2)
    have hl : Continuous (fun v ↦ (2*h*J)*f v) := continuous_const.mul hf
    rw [intervalIntegral.integral_add (f := fun v ↦ h^2*(f v)^2 - (2*h*J)*f v) (g := fun _ ↦ J^2)
        ((hs.sub hl).intervalIntegrable ..) intervalIntegrable_const,
      intervalIntegral.integral_sub (hs.intervalIntegrable ..) (hl.intervalIntegrable ..),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      hps t, smul_eq_mul] at hpos
    change J^2 ≤ _
    change 0 ≤ h^2*(P (t+h)-P t) - 2*h*J*J + (t+h-t)*J^2 at hpos
    by_contra! hc
    nlinarith only [hpos, mul_pos hhpos (sub_pos.mpr hc)]
  have hdiff : (∫ t in a..b, P (t+h) - P t) = (∫ u in b..b+h, P u) - ∫ u in a..a+h, P u := by
    have hp' : Continuous (fun t ↦ P (t+h)) := hp.comp (continuous_id.add_const h)
    rw [intervalIntegral.integral_sub (hp'.intervalIntegrable ..) (hp.intervalIntegrable ..),
      intervalIntegral.integral_comp_add_right]
    exact intervalIntegral.integral_interval_sub_interval_comm' (hp.intervalIntegrable ..) (hp.intervalIntegrable ..) (hp.intervalIntegrable ..)
  have hlast : (∫ u in b..b+h, P u) ≤ h * P (b+h) := by
    calc _ ≤ ∫ _ in b..b+h, P (b+h) := by
           apply intervalIntegral.integral_mono_on (by linarith) (hp.intervalIntegrable ..) intervalIntegrable_const
           intro u hu
           exact intervalIntegral.integral_mono_interval le_rfl (hab.trans hu.1) hu.2
             (.of_forall fun _ ↦ sq_nonneg _) ((hf.pow 2).intervalIntegrable ..)
         _ = _ := by simp
  have hfirst : 0 ≤ ∫ u in a..a+h, P u := intervalIntegral.integral_nonneg (by linarith)
    (fun u hu ↦ intervalIntegral.integral_nonneg hu.1 fun _ _ ↦ sq_nonneg _)
  calc _ ≤ ∫ t in a..b, h*(P (t+h)-P t) := intervalIntegral.integral_mono_on hab
         (((spectralLineJet_selberg_continuousWindow hf h).pow 2).intervalIntegrable ..)
         ((continuous_const.mul ((hp.comp (continuous_id.add_const h)).sub hp)).intervalIntegrable ..) fun t _ ↦ hcs t
       _ = h * ((∫ u in b..b+h, P u) - ∫ u in a..a+h, P u) := by rw [intervalIntegral.integral_const_mul,hdiff]
       _ ≤ h*(h*P (b+h)) := mul_le_mul_of_nonneg_left (by linarith) hhpos.le
       _ = _ := by simp [P, sq, mul_assoc]

end RiemannMasullo
