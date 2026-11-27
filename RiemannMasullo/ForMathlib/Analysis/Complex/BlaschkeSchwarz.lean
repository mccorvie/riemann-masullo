module

public import RiemannMasullo.ForMathlib.Analysis.Complex.BlaschkeFactorization
import Mathlib.Analysis.Complex.Schwarz

/-!
# The derivative of a bounded analytic function at a zero

Dividing out a finite collection of other zeros by their Blaschke factors and applying
Schwarz's lemma bounds the derivative at the center of an arbitrary disk. Each zero contributes
its normalized distance to the center, raised to the prescribed vanishing order.
-/

@[expose] public noncomputable section
open Complex Filter Function Metric Set
open scoped Topology

namespace RiemannMasullo.Blaschke

private theorem norm_finiteProduct_zero {ι : Type*} (a : ι → ℂ) (m : ι → ℕ) (S : Finset ι) :
    ‖finiteProduct a m S 0‖ = ∏ i ∈ S, ‖a i‖ ^ m i := by
  simp [finiteProduct, norm_prod, normalizedFactor_apply]

private theorem deriv_bound_unitDisk {ι : Type*} (a : ι → ℂ) (m : ι → ℕ) (S : Finset ι)
    (hinj : Injective a) (ha : ∀ i, a i ≠ 0) (hball : ∀ i, ‖a i‖ < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (ball 0 1)) (hzero : f 0 = 0)
    (hm : ∀ i ∈ S, (m i : ℕ∞) ≤ analyticOrderAt f (a i))
    (M : ℝ) (hM : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M) :
    ‖deriv f 0‖ ≤ M * ∏ i ∈ S, ‖a i‖ ^ m i := by
  have h0 : (0 : ℂ) ∈ ball 0 1 := by simp
  obtain ⟨g, hg, hbound, heq⟩ :=
    exists_bounded_finite_blaschke_quotient a m S hinj ha hball f hf hm M hM
  let P := finiteProduct a m S
  have hP : AnalyticAt ℂ P 0 := by
    dsimp only [P]
    rw [← product_subtype_mem a m S]
    exact analyticOnNhd_product (fun i : S ↦ a i.val) (fun i : S ↦ m i.val)
      (fun i ↦ ha i.val) (fun i ↦ hball i.val)
      (hasSum_fintype _).summable 0 h0
  have hp0 : P 0 ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [show ‖P 0‖ = _ from norm_finiteProduct_zero a m S]
    exact (Finset.prod_pos fun i _ ↦ pow_pos (norm_pos_iff.mpr (ha i)) _).ne'
  have hg0 : g 0 = 0 := (mul_eq_zero.mp ((heq 0 h0).trans hzero)).resolve_left hp0
  have hmaps : MapsTo g (ball 0 1) (closedBall (g 0) M) := by
    intro z hz
    rw [hg0, mem_closedBall_zero_iff]
    exact hbound z hz
  have hder : ‖deriv g 0‖ ≤ M := by
    simpa using Complex.norm_deriv_le_div_of_mapsTo_ball hg.differentiableOn hmaps one_pos
  have he : f =ᶠ[𝓝 0] (fun z ↦ P z * g z) := by
    filter_upwards [isOpen_ball.mem_nhds h0] with z hz using (heq z hz).symm
  have hprod := hP.differentiableAt.hasDerivAt.mul (hg 0 h0).differentiableAt.hasDerivAt
  rw [(hprod.congr_of_eventuallyEq he).deriv, hg0, mul_zero, zero_add, norm_mul,
    show ‖P 0‖ = _ from norm_finiteProduct_zero a m S, mul_comm M]
  exact mul_le_mul_of_nonneg_left hder (Finset.prod_nonneg fun i _ ↦ pow_nonneg (norm_nonneg _) _)

/-- If a bounded analytic function vanishes at the center of a disk, every additional
zero of multiplicity m contributes its normalized distance to the m-th power to the
bound for the first derivative at the center. -/
theorem norm_deriv_le_disk_zero_product (f : ℂ → ℂ) (z : ℂ) {r M : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (ball z r)) (hz : f z = 0)
    (hb : ∀ u ∈ ball z r, ‖f u‖ ≤ M) (S : Finset ℂ) (m : ℂ → ℕ)
    (hne : ∀ w ∈ S, w ≠ z) (hi : ∀ w ∈ S, w ∈ ball z r)
    (hm : ∀ w ∈ S, (m w : ℕ∞) ≤ analyticOrderAt f w) :
    ‖deriv f z‖ ≤ (M / r) * ∏ w ∈ S, (‖w - z‖ / r) ^ m w := by
  classical
  let a (w : S) : ℂ := (w.val - z) / (r : ℂ)
  let h (v : ℂ) := z + (r : ℂ) * v
  have hrc : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hrnorm : ‖(r : ℂ)‖ = r := by simp [Real.norm_eq_abs, hr.le]
  have ha (w : S) : a w ≠ 0 := div_ne_zero (sub_ne_zero.mpr (hne _ w.property)) hrc
  have han (w : S) : ‖a w‖ = ‖w.val - z‖ / r := by simp only [a, norm_div, hrnorm]
  have hain (w : S) : ‖a w‖ < 1 := by
    rw [han, div_lt_one hr]
    simpa [Metric.mem_ball, dist_eq_norm] using hi w.val w.property
  have hai : Injective a := by
    intro i j hh
    apply Subtype.ext
    apply sub_left_injective (b := z)
    exact (div_left_inj₀ hrc).mp hh
  have hza (w : S) : h (a w) = w.val := by
    dsimp only [h, a]
    field_simp
    ring
  have hhz : h 0 = z := by simp [h]
  have hmap : MapsTo h (ball 0 1) (ball z r) := by
    intro v hv
    have ht := mem_ball_zero_iff.mp hv
    rw [Metric.mem_ball, dist_eq_norm]
    simpa only [h, add_sub_cancel_left, norm_mul, hrnorm, mul_one]
      using mul_lt_mul_of_pos_left ht hr
  have hHA (v : ℂ) : AnalyticAt ℂ h v := analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hcomp : AnalyticOnNhd ℂ (f ∘ h) (ball 0 1) :=
    fun u hu ↦ (hf _ (hmap hu)).comp (hHA u)
  have horder (w : S) : ((m w.val : ℕ) : ℕ∞) ≤ analyticOrderAt (f ∘ h) (a w) := by
    apply RiemannMasullo.natCast_le_analyticOrderAt_comp
      (hf _ (by rw [hza]; exact hi _ w.property)) (hHA _)
    simpa only [hza] using hm w.val w.property
  have H := deriv_bound_unitDisk a (fun w ↦ m w.val) Finset.univ hai ha hain (f ∘ h)
    hcomp (by simpa only [Function.comp_apply, hhz] using hz) (fun w _ ↦ horder w) M
    (fun v hv ↦ hb _ (hmap hv))
  have hh' : HasDerivAt h (r : ℂ) 0 := by
    simpa [h] using (((hasDerivAt_id (0 : ℂ)).const_mul (r : ℂ)).const_add z)
  have hd := ((hf z (mem_ball_self hr)).differentiableAt.hasDerivAt)
  rw [← hhz] at hd
  have hd' := hd.comp 0 hh'
  rw [hd'.deriv, hhz, norm_mul, hrnorm] at H
  simp only [han] at H
  rw [Finset.prod_coe_sort S (fun w : ℂ ↦ (‖w - z‖ / r) ^ m w)] at H
  calc
    ‖deriv f z‖ ≤ (M * ∏ w ∈ S, (‖w - z‖ / r) ^ m w) / r := (le_div_iff₀ hr).mpr H
    _ = _ := by ring

end RiemannMasullo.Blaschke
end
