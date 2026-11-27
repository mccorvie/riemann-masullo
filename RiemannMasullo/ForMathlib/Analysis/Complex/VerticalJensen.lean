module

public import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Jensen counts for a mollified analytic function on vertically translated disks -/

@[expose] public noncomputable section

open Classical Metric Complex Set Real MeasureTheory MeromorphicOn
open scoped Topology

namespace RiemannMasullo

/-- A local Jensen count in terms of the additive error of an analytic approximation
to one. Its advantage for translated disks is that the circle mean can be integrated
over their centers without taking a supremum. -/
theorem sum_orders_le_circleAverage_error {f g : ℂ → ℂ} {c : ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : r < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R)) (hc : ‖f c * g c - 1‖ ≤ 1/2)
    (S : Finset ℂ) (hS : ∀ z ∈ S, z ∈ closedBall c r ∧ f z = 0) :
    (∑ z ∈ S, ((meromorphicOrderAt f z).untop₀.toNat : ℝ)) * Real.log (R/r) ≤
      circleAverage (fun z ↦ ‖f z * g z - 1‖) c R + 2 * ‖f c * g c - 1‖ := by
  let F := f*g
  have hF : AnalyticOnNhd ℂ F (closedBall c R) := hf.mul hg
  change ‖F c-1‖ ≤ 1/2 at hc
  change _ ≤ circleAverage (fun z ↦ ‖F z-1‖) c R + 2*‖F c-1‖
  let D := divisor F (closedBall c R)
  let W (z : ℂ) := (D z : ℝ) * Real.log (R * ‖c - z‖⁻¹)
  have hR₀ := hr.trans hR
  have hF' : AnalyticOnNhd ℂ F (closedBall c |R|) := by simpa only [abs_of_pos hR₀] using hF
  have hfc : 1 - ‖F c‖ ≤ ‖F c - 1‖ := by
    simpa only [norm_one, norm_sub_rev (1 : ℂ)] using norm_sub_norm_le (1 : ℂ) (F c)
  have hhalf : 1/2 ≤ ‖F c‖ := by linarith
  have hnorm : 0 < ‖F c‖ := by linarith
  have hn := norm_ne_zero_iff.mp hnorm.ne'
  have hcenter : -Real.log ‖F c‖ ≤ 2 * ‖F c - 1‖ := by
    have hb : 1 - ‖F c‖ ≤ (2 * ‖F c - 1‖) * ‖F c‖ := hfc.trans (by
      nlinarith [mul_nonneg (norm_nonneg (F c - 1)) (sub_nonneg.mpr hhalf)])
    have hi : ‖F c‖⁻¹ ≤ 1 + 2 * ‖F c - 1‖ := by
      rw [inv_eq_one_div, div_le_iff₀ hnorm]; linarith
    linarith [Real.one_sub_inv_le_log_of_pos hnorm]
  have hfinite : (Function.support W).Finite := (D.finiteSupport (isCompact_closedBall ..)).subset
    (fun z hz ↦ by contrapose hz; simp_all [W, Function.mem_support])
  have hdist (z : ℂ) (hz : z ∈ closedBall c R) (hne : z ≠ c) :
      0 ≤ Real.log (R * ‖c - z‖⁻¹) := by
    have hpos := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
    apply Real.log_nonneg
    rw [← div_eq_mul_inv, one_le_div hpos]
    exact dist_eq_norm' z c ▸ hz
  have hW (z : ℂ) : 0 ≤ W z := by
    by_cases hz : z ∈ closedBall c R
    · rcases eq_or_ne z c with rfl | hz'
      · simp [W]
      · exact mul_nonneg (by exact_mod_cast hF.divisor_nonneg z) (hdist z hz hz')
    · simp [W, D, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]
  have hnon {u : ℂ → ℂ} (hu : AnalyticOnNhd ℂ u (closedBall c R)) (huc : u c ≠ 0) :
      ∀ z ∈ closedBall c R, meromorphicOrderAt u z ≠ ⊤ := by
    intro z hz
    have hfin := hu.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected
      (mem_closedBall_self hR₀.le) hz (by rw [(hu _ (mem_closedBall_self hR₀.le)).analyticOrderAt_eq_zero.mpr huc]; simp)
    obtain ⟨n,he⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [(hu _ hz).meromorphicOrderAt_eq,← he,ENat.map_natCast]; simp
  have hfg : f c * g c ≠ 0 := hn
  have hdiv := divisor_mul hf.meromorphicOn hg.meromorphicOn (hnon hf (left_ne_zero_of_mul hfg))
    (hnon hg (right_ne_zero_of_mul hfg))
  have hweight (z : ℂ) (hz : z ∈ S) :
      ((meromorphicOrderAt f z).untop₀.toNat : ℝ)*Real.log (R/r) ≤ W z := by
    obtain ⟨hm, hzero⟩ := hS z hz
    have hm' := closedBall_subset_closedBall hR.le hm
    have hne : z ≠ c := fun he ↦ (left_ne_zero_of_mul hfg) (he ▸ hzero)
    have hdpos := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
    have hfo := hf.divisor_nonneg z
    rw [hf.meromorphicOn.divisor_apply hm'] at hfo
    have ho : ((meromorphicOrderAt f z).untop₀.toNat : ℝ) ≤ D z := by
      dsimp only [D,F]
      rw [hdiv,Function.locallyFinsuppWithin.coe_add,Pi.add_apply,hf.meromorphicOn.divisor_apply hm']
      exact_mod_cast (show (((meromorphicOrderAt f z).untop₀.toNat : ℕ):ℤ) ≤
        (meromorphicOrderAt f z).untop₀+divisor g (closedBall c R) z by
        rw [Int.toNat_of_nonneg hfo]; exact le_add_of_nonneg_right (hg.divisor_nonneg z))
    have hlog : Real.log (R/r) ≤ Real.log (R * ‖c-z‖⁻¹) := by
      rw [← div_eq_mul_inv]
      exact Real.log_le_log (div_pos hR₀ hr) (div_le_div_of_nonneg_left hR₀.le hdpos (dist_eq_norm' z c ▸ hm))
    exact (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right ho (hdist z hm' hne))
  have hsum : (∑ z ∈ S, ((meromorphicOrderAt f z).untop₀.toNat:ℝ))*Real.log (R/r) ≤ ∑ᶠ z, W z := calc
    _ = ∑ z ∈ S, ((meromorphicOrderAt f z).untop₀.toNat:ℝ)*Real.log (R/r) := Finset.sum_mul ..
    _ ≤ ∑ z ∈ S, W z := Finset.sum_le_sum hweight
    _ ≤ ∑ᶠ z, W z := by
      rw [finsum_eq_sum_of_support_subset _ (s := S ∪ hfinite.toFinset) (fun z hz ↦
        Finset.mem_union_right _ (hfinite.mem_toFinset.mpr hz))]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (fun z _ _ ↦ hW z)
  have hJ := hF'.circleAverage_log_norm hn
  rw [abs_of_pos hR₀] at hJ
  have hmean : circleAverage (fun z ↦ Real.log ‖F z‖) c R ≤ circleAverage (fun z ↦ ‖F z - 1‖) c R := by
    apply circleAverage_mono (hF'.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
      ((hF'.mono sphere_subset_closedBall).continuousOn.sub (continuousOn_const (c := (1 : ℂ))) |>.norm.circleIntegrable')
    intro z hz
    rcases eq_or_ne (F z) 0 with h | h
    · simp [h]
    · exact (Real.log_le_sub_one_of_pos (norm_pos_iff.mpr h)).trans (by simpa using norm_sub_norm_le (F z) (1 : ℂ))
  change circleAverage _ c R = (∑ᶠ z, W z) + _ at hJ
  linarith

end RiemannMasullo

open Classical Complex Filter MeasureTheory Metric Real Set
open scoped Topology
namespace RiemannMasullo

private theorem swap_interval_integrals {F : ℝ × ℝ → ℝ} (hF : Continuous F) {a b u v : ℝ}
    (hab : a ≤ b) (huv : u ≤ v) :
    (∫ t in a..b, ∫ θ in u..v, F (t,θ)) = ∫ θ in u..v, ∫ t in a..b, F (t,θ) := by
  have hlim := (hF.continuousOn.integrableOn_compact (μ := volume.prod volume)
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc a b ×ˢ Icc u v)))
      |>.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  rw [IntegrableOn,← Measure.prod_restrict] at hlim
  simp only [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le huv]
  exact integral_integral_swap (f := fun t θ ↦ F (t,θ)) hlim

/-- A vertical line mean transfers to the angular mean on vertically
translated circles, with the same constant at every angle. -/
theorem vertical_circle_mean_le {F : ℂ → ℝ} (hF : Continuous F) {a b σ R B : ℝ}
    (hab : a ≤ b) (h : ∀ θ : ℝ, let z := circleMap 0 R θ
      (∫ t in (a+z.im)..(b+z.im), F ⟨σ+z.re,t⟩) ≤ B) :
    (∫ t in a..b, circleAverage F ⟨σ,t⟩ R) ≤ B := by
  let U := 2*Real.pi
  have hU : 0 < U := by dsimp [U]; positivity
  let G (p : ℝ × ℝ) := F (circleMap (⟨σ,p.1⟩:ℂ) R p.2)
  have hG : Continuous G := by
    have he (t : ℝ) : (⟨σ,t⟩:ℂ) = (σ:ℂ)+(t:ℂ)*Complex.I := (Complex.re_add_im _).symm
    dsimp only [G,circleMap]; simp_rw [he]
    apply hF.comp; fun_prop
  have hv (θ : ℝ) : (∫ t in a..b, G (t,θ)) ≤ B := by
    let z := circleMap 0 R θ
    have he (t : ℝ) : G (t,θ) = F ⟨σ+z.re,t+z.im⟩ := by
      apply congrArg F
      change circleMap (⟨σ,t⟩:ℂ) R θ = _
      have hz : circleMap (⟨σ,t⟩:ℂ) R θ = (⟨σ,t⟩:ℂ)+z := by dsimp [z,circleMap]; rw [zero_add]
      rw [hz]; rfl
    simp_rw [he]
    exact (intervalIntegral.integral_comp_add_right (fun t ↦ F ⟨σ+z.re,t⟩) z.im).le.trans (h θ)
  have hc : Continuous (fun θ ↦ ∫ t in a..b, G (t,θ)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := fun θ t ↦ G (t,θ)) (hG.comp continuous_swap) a b
  calc _ = U⁻¹ * (∫ t in a..b, ∫ θ in (0:ℝ)..U, G (t,θ)) := by
          simp only [Real.circleAverage_def,smul_eq_mul,intervalIntegral.integral_const_mul,U,G]
       _ = U⁻¹ * (∫ θ in (0:ℝ)..U, ∫ t in a..b, G (t,θ)) := by rw [swap_interval_integrals hG hab hU.le]
       _ ≤ U⁻¹ * ∫ θ in (0:ℝ)..U, B := mul_le_mul_of_nonneg_left
         (intervalIntegral.integral_mono_on hU.le (hc.intervalIntegrable ..) intervalIntegrable_const (fun θ _ ↦ hv θ)) (inv_nonneg.mpr hU.le)
       _ = B := by rw [intervalIntegral.integral_const,sub_zero,smul_eq_mul,← mul_assoc,inv_mul_cancel₀ hU.ne',one_mul]

/-- Integrating finite sliding-window counts counts every site for the same
length. All weight is retained even when several sites share an ordinate. -/
theorem integral_window_sum {S : Finset ℂ} (w : ℂ → ℝ) {a b h : ℝ} (hh : 0 ≤ h) (hab : a ≤ b)
    (hS : ∀ z ∈ S, a ≤ z.im-h ∧ z.im+h ≤ b) :
    (∫ t in a..b, ∑ z ∈ S, (Ioc (z.im-h) (z.im+h)).indicator (fun _ ↦ w z) t) =
      (2*h) * ∑ z ∈ S, w z := by
  have hi (z : ℂ) : IntervalIntegrable ((Ioc (z.im-h) (z.im+h)).indicator (fun _ ↦ w z)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (((integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp [Real.volume_Ioc]))).integrableOn)
  rw [intervalIntegral.integral_finsetSum (fun z _ ↦ hi z),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hm := hS z hz
  rw [intervalIntegral.integral_of_le hab,setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr (Ioc_subset_Ioc hm.1 hm.2),← intervalIntegral.integral_of_le (show z.im-h ≤ z.im+h by linarith),
    intervalIntegral.integral_const,smul_eq_mul]
  ring

end RiemannMasullo
