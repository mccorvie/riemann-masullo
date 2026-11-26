module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! # Two-sided envelope of the rational Riemann xi theta kernel

The even theta series represents the Fourier density of the completed Riemann xi
function. Its first summand controls the series uniformly on the entire logarithmic
line. This estimate serves the positivity comparison for pairs of shifted xi factors.
-/

public noncomputable section

open Real MeasureTheory

namespace RiemannMasullo

/-- The even Riemann xi theta kernel in logarithmic coordinates, factored by its
leading double-exponential scale. The index `n` denotes the term at `n + 1`. -/
@[expose] def rationalXiThetaKernel (u : ℝ) : ℝ :=
  let x := Real.exp (2 * |u|)
  4 * Real.pi ^ 2 * Real.exp (9 * |u| / 2 - Real.pi * x) *
    ∑' n : ℕ, ((n : ℝ) + 1) ^ 4 * (1 - 3 / (2 * Real.pi * ((n : ℝ) + 1) ^ 2 * x)) *
      Real.exp (-Real.pi * (((n : ℝ) + 1) ^ 2 - 1) * x)

/-- The double-exponential scale of the first rational theta summand. -/
@[expose] def rationalXiThetaScale (u : ℝ) : ℝ :=
  4 * Real.pi ^ 2 * Real.exp (9 * |u| / 2 - Real.pi * Real.exp (2 * |u|))

private theorem thetaXi_nat_growth (n : ℕ) : (n : ℝ) + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ]
    linarith [show 1 ≤ (2 : ℝ) ^ n by exact one_le_pow₀ (by norm_num)]

private theorem thetaXi_gaussian_bound {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    ((n : ℝ) + 1) ^ 4 * Real.exp (-Real.pi * (((n : ℝ) + 1) ^ 2 - 1) * x) ≤ (1 / 32 : ℝ) ^ n := by
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (by decide : 2 ≠ 0) n
  have hq : 3 * (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 - 1 := by nlinarith
  have hπ : 9 * (n : ℝ) ≤ Real.pi * (((n : ℝ) + 1) ^ 2 - 1) * x := calc
    9 * (n : ℝ) = 3 * (3 * (n : ℝ)) * 1 := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul Real.pi_gt_three.le hq (by positivity) Real.pi_pos.le) hx
      zero_le_one (mul_nonneg Real.pi_pos.le (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  have hexp : Real.exp (-9 : ℝ) ≤ 1 / 512 := by
    rw [Real.exp_neg, one_div, inv_le_inv₀ (by positivity) (by positivity)]
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2) Real.exp_one_gt_two.le 9
    rw [← Real.exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  calc
    _ ≤ ((2 : ℝ) ^ n) ^ 4 * Real.exp ((n : ℝ) * (-9)) := by
      apply mul_le_mul (pow_le_pow_left₀ (by positivity) (thetaXi_nat_growth n) _) _
        (Real.exp_pos _).le (by positivity)
      apply Real.exp_le_exp.mpr
      linarith
    _ = ((2 : ℝ) ^ 4) ^ n * (Real.exp (-9)) ^ n := by rw [pow_right_comm, Real.exp_nat_mul]
    _ ≤ ((2 : ℝ) ^ 4) ^ n * (1 / 512 : ℝ) ^ n := by gcongr
    _ = _ := by rw [← mul_pow]; norm_num

/-- The full theta series is between one half and `32 / 31` times the leading
Gaussian envelope, uniformly on the real logarithmic line. -/
theorem rationalXiThetaKernel_envelope (u : ℝ) :
    rationalXiThetaScale u / 2 ≤ rationalXiThetaKernel u ∧
      rationalXiThetaKernel u ≤ (32 / 31) * rationalXiThetaScale u := by
  let x := Real.exp (2 * |u|)
  let A := 4 * Real.pi ^ 2 * Real.exp (9 * |u| / 2 - Real.pi * x)
  let s (n : ℕ) := ((n : ℝ) + 1) ^ 4 * (1 - 3 / (2 * Real.pi * ((n : ℝ) + 1) ^ 2 * x)) * Real.exp (-Real.pi * (((n : ℝ) + 1) ^ 2 - 1) * x)
  have hx : 1 ≤ x := Real.one_le_exp (by positivity)
  have hA : 0 ≤ A := by positivity
  have hd (n : ℕ) : 6 ≤ 2 * Real.pi * ((n : ℝ) + 1) ^ 2 * x := by
    calc
      (6 : ℝ) = 2 * 3 * 1 ^ 2 * 1 := by norm_num
      _ ≤ _ := by gcongr <;> first | exact Real.pi_gt_three.le | linarith [Nat.cast_nonneg (α := ℝ) n]
  have hf (n : ℕ) : 0 ≤ 1 - 3 / (2 * Real.pi * ((n : ℝ) + 1) ^ 2 * x) := by
    apply sub_nonneg.mpr
    rw [div_le_one (by linarith [hd n])]
    linarith [hd n]
  have hn (n : ℕ) : 0 ≤ s n := mul_nonneg (mul_nonneg (by positivity) (hf n)) (Real.exp_pos _).le
  have hub (n : ℕ) : s n ≤ (1 / 32 : ℝ) ^ n := by
    calc
      _ ≤ ((n : ℝ) + 1) ^ 4 * Real.exp (-Real.pi * (((n : ℝ) + 1) ^ 2 - 1) * x) := by
        unfold s
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_of_le_one_right (by positivity) (by linarith [show
          0 ≤ 3 / (2 * Real.pi * ((n : ℝ) + 1) ^ 2 * x) by positivity])
      _ ≤ _ := thetaXi_gaussian_bound hx n
  have hg := hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 32 : ℝ)‖ < 1)
  have hs : Summable s := Summable.of_nonneg_of_le hn hub hg.summable
  have hzero : (1 / 2 : ℝ) ≤ s 0 := by
    simp [s]
    have h := hd 0
    norm_num at h
    have hdiv : 3 / (2 * Real.pi * x) ≤ 1 / 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
    linarith
  have hlo := hzero.trans (hs.le_tsum 0 (fun n _ ↦ hn n))
  have hhi := hs.tsum_le_tsum hub hg.summable
  rw [hg.tsum_eq] at hhi
  norm_num at hhi
  change A / 2 ≤ A * (∑' n, s n) ∧ A * (∑' n, s n) ≤ 32 / 31 * A
  constructor
  · convert mul_le_mul_of_nonneg_left hlo hA using 1; ring
  · simpa only [mul_comm A] using mul_le_mul_of_nonneg_left hhi hA

/-- The factored definition equals Riemann's usual even theta series. -/
theorem rationalXiThetaKernel_eq_series (u : ℝ) :
    rationalXiThetaKernel u = ∑' n : ℕ,
      (4 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * |u| / 2) -
        6 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * |u| / 2)) *
      Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * |u|)) := by
  unfold rationalXiThetaKernel
  dsimp only
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  let x := Real.exp (2 * |u|)
  let m : ℝ := n + 1
  have hm : 0 < m := by dsimp [m]; positivity
  have hx : 0 < x := Real.exp_pos _
  have hB : Real.exp (9 * |u| / 2) = Real.exp (5 * |u| / 2) * x := by
    dsimp [x]
    rw [← Real.exp_add]
    congr 1
    ring
  have he : Real.exp (9 * |u| / 2 - Real.pi * x) * Real.exp (-Real.pi * (m ^ 2 - 1) * x) =
      Real.exp (9 * |u| / 2) * Real.exp (-Real.pi * m ^ 2 * x) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = 4 * Real.pi ^ 2 * m ^ 4 * (1 - 3 / (2 * Real.pi * m ^ 2 * x)) *
        (Real.exp (9 * |u| / 2 - Real.pi * x) * Real.exp (-Real.pi * (m ^ 2 - 1) * x)) := by
      dsimp [x, m]
      ring
    _ = _ := by
      rw [he, hB]
      change _ = (_ * (Real.exp (5 * |u| / 2) * x) - _ * Real.exp (5 * |u| / 2)) * Real.exp (-Real.pi * m ^ 2 * x)
      field_simp [ne_of_gt hm, ne_of_gt hx, ne_of_gt Real.pi_pos]
      dsimp [m]
      ring

private theorem thetaXi_pair_bound (a h t : ℝ) (ht : t ^ 2 ≤ 2) :
    let p := rationalXiThetaKernel (a + h) * rationalXiThetaKernel (a - h)
    let r := rationalXiThetaScale (a + h) * rationalXiThetaScale (a - h)
    r / 4 - (4 * (32 / 31) ^ 2) * (h ^ 2 * r) ≤ p * Real.cos (2 * t * h) := by
  intro p r
  obtain ⟨hl₁, hu₁⟩ := rationalXiThetaKernel_envelope (a + h)
  obtain ⟨hl₂, hu₂⟩ := rationalXiThetaKernel_envelope (a - h)
  have hs (v : ℝ) : 0 ≤ rationalXiThetaScale v := by unfold rationalXiThetaScale; positivity
  have hp (v : ℝ) : 0 ≤ rationalXiThetaKernel v :=
    (div_nonneg (hs v) (by norm_num)).trans (rationalXiThetaKernel_envelope v).1
  have hl : r / 4 ≤ p := by
    have H := mul_le_mul hl₁ hl₂ (div_nonneg (hs _) (by norm_num)) (hp _)
    dsimp [r,p]
    linarith
  have hu : p ≤ (32 / 31) ^ 2 * r := by
    have H := mul_le_mul hu₁ hu₂ (hp _) (mul_nonneg (by norm_num) (hs _))
    dsimp [r,p]
    linarith
  have hpn : 0 ≤ p := mul_nonneg (hp _) (hp _)
  have hcost : p * ((2 * t * h) ^ 2 / 2) ≤ (4 * (32 / 31) ^ 2) * (h ^ 2 * r) := by
    calc
      _ = (2 * t ^ 2) * (h ^ 2 * p) := by ring
      _ ≤ 4 * (h ^ 2 * ((32 / 31) ^ 2 * r)) := by
        apply mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hu (sq_nonneg _))
          (mul_nonneg (sq_nonneg _) hpn) (by norm_num)
      _ = _ := by ring
  have hcos := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := 2 * t * h)) hpn
  linarith

private theorem thetaXi_measurable : Measurable rationalXiThetaKernel := by
  unfold rationalXiThetaKernel
  dsimp only
  fun_prop

private theorem thetaXi_shifted_lower (a t : ℝ) (ht : t ^ 2 ≤ 2) :
    let r (h : ℝ) := rationalXiThetaScale (a + h) * rationalXiThetaScale (a - h)
    Integrable r → Integrable (fun h : ℝ ↦ h ^ 2 * r h) →
    (∫ h : ℝ, h ^ 2 * r h) ≤ (∫ h : ℝ, r h) / (8 * Real.pi) →
    (∫ h : ℝ, r h) / 16 ≤ ∫ h : ℝ,
      (rationalXiThetaKernel (a + h) * rationalXiThetaKernel (a - h)) * Real.cos (2 * t * h) := by
  intro r hr hm hmoment
  let p (h : ℝ) := rationalXiThetaKernel (a + h) * rationalXiThetaKernel (a - h)
  have hs (v : ℝ) : 0 ≤ rationalXiThetaScale v := by unfold rationalXiThetaScale; positivity
  have hp (v : ℝ) : 0 ≤ rationalXiThetaKernel v :=
    (div_nonneg (hs v) (by norm_num)).trans (rationalXiThetaKernel_envelope v).1
  have hr0 (h : ℝ) : 0 ≤ r h := mul_nonneg (hs _) (hs _)
  have hp0 (h : ℝ) : 0 ≤ p h := mul_nonneg (hp _) (hp _)
  have hup (h : ℝ) : p h ≤ (32 / 31) ^ 2 * r h := by
    have H := mul_le_mul (rationalXiThetaKernel_envelope (a + h)).2
      (rationalXiThetaKernel_envelope (a - h)).2 (hp _) (mul_nonneg (by norm_num) (hs _))
    dsimp [r,p]
    linarith
  have hmeas : Measurable (fun h : ℝ ↦ p h * Real.cos (2 * t * h)) := by
    dsimp [p]
    exact ((thetaXi_measurable.comp (measurable_const.add measurable_id)).mul
      (thetaXi_measurable.comp (measurable_const.sub measurable_id))).mul (by fun_prop)
  have hi : Integrable (fun h : ℝ ↦ p h * Real.cos (2 * t * h)) := by
    apply (hr.const_mul ((32 / 31 : ℝ) ^ 2)).mono' hmeas.aestronglyMeasurable
    filter_upwards with h
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 h)]
    exact (mul_le_of_le_one_right (hp0 _) (Real.abs_cos_le_one _)).trans (hup _)
  have hineq := integral_mono ((hr.div_const 4).sub (hm.const_mul (4 * (32 / 31) ^ 2))) hi
    (fun h ↦ thetaXi_pair_bound a h t ht)
  simp only [Pi.sub_apply] at hineq
  rw [integral_sub (hr.div_const _) (hm.const_mul _), integral_div, integral_const_mul] at hineq
  have hmass : 0 ≤ ∫ h : ℝ, r h := integral_nonneg hr0
  have hweight : (4 * (32 / 31 : ℝ) ^ 2) * ((∫ h : ℝ, r h) / (8 * Real.pi)) ≤ (3 / 16) * (∫ h : ℝ, r h) := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    have hconst : 4 * (32 / 31 : ℝ) ^ 2 ≤ 3 / 16 * (8 * Real.pi) := by nlinarith [Real.pi_gt_three]
    convert mul_le_mul_of_nonneg_right hconst hmass using 1; ring
  have hcost := (mul_le_mul_of_nonneg_left hmoment (by norm_num : 0 ≤ 4 * (32 / 31 : ℝ) ^ 2)).trans hweight
  change _ ≤ ∫ h : ℝ, p h * Real.cos (2 * t * h)
  linarith

private theorem thetaXi_potential_convex :
    ConvexOn ℝ Set.univ (fun v : ℝ ↦ Real.pi * Real.exp (2 * |v|) - 9 * |v| / 2 - 2 * Real.pi * v ^ 2) := by
  let f (s : ℝ) := Real.pi * Real.exp (2 * s) - 9 * s / 2 - 2 * Real.pi * s ^ 2
  let d (s : ℝ) := 2 * Real.pi * Real.exp (2 * s) - 9 / 2 - 4 * Real.pi * s
  let dd (s : ℝ) := 4 * Real.pi * (Real.exp (2 * s) - 1)
  have hf (s : ℝ) : HasDerivAt f (d s) s := by
    dsimp [f,d]
    convert (((((hasDerivAt_id s).const_mul 2).exp.const_mul Real.pi).sub
      (((hasDerivAt_id s).const_mul 9).div_const 2)).sub
      (((hasDerivAt_id s).pow 2).const_mul (2 * Real.pi))) using 1
    all_goals try funext v
    all_goals simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    ring
  have hd (s : ℝ) : HasDerivAt d (dd s) s := by
    dsimp [d,dd]
    convert ((((((hasDerivAt_id s).const_mul 2).exp.const_mul (2 * Real.pi)).sub_const
      (9 / 2)).sub ((hasDerivAt_id s).const_mul (4 * Real.pi)))) using 1
    all_goals try funext v
    all_goals simp only [Pi.sub_apply, id_eq]
    ring
  have hconv : ConvexOn ℝ (Set.Ici 0) f := convexOn_of_hasDerivWithinAt2_nonneg
    (convex_Ici 0) (fun s _ ↦ (hf s).continuousAt.continuousWithinAt)
    (fun s _ ↦ (hf s).hasDerivWithinAt) (fun s _ ↦ (hd s).hasDerivWithinAt)
    (fun s hs ↦ by
      have h0 : 0 ≤ s := interior_subset hs
      exact mul_nonneg (by positivity) (sub_nonneg.mpr (Real.one_le_exp (by linarith))))
  have hmono : MonotoneOn f (Set.Ici 0) := monotoneOn_of_hasDerivWithinAt_nonneg
    (convex_Ici 0) (fun s _ ↦ (hf s).continuousAt.continuousWithinAt)
    (fun s _ ↦ (hf s).hasDerivWithinAt) (fun s _ ↦ by
      have H := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (2 * s)) Real.pi_pos.le
      dsimp [d]
      nlinarith [Real.pi_gt_three])
  have habs : ConvexOn ℝ Set.univ (fun v : ℝ ↦ |v|) := by
    rw [show (fun v : ℝ ↦ |v|) = (fun v : ℝ ↦ ‖v‖) from funext fun v ↦ (Real.norm_eq_abs v).symm]
    exact convexOn_norm convex_univ
  have him : (fun v : ℝ ↦ |v|) '' Set.univ = Set.Ici 0 := by
    ext s
    constructor
    · rintro ⟨v, _, rfl⟩
      exact abs_nonneg v
    · intro hs
      exact ⟨s, Set.mem_univ _, abs_of_nonneg hs⟩
  rw [← him] at hconv hmono
  simpa only [Function.comp_def,f, sq_abs] using hconv.comp habs hmono

private theorem thetaXi_symmetric_order (q : ℝ → ℝ) (hq : ConvexOn ℝ Set.univ q)
    (a h k : ℝ) (hhk : |h| ≤ |k|) :
    q (a + h) + q (a - h) ≤ q (a + k) + q (a - k) := by
  by_cases hk : k = 0
  · subst k
    have hh : h = 0 := abs_nonpos_iff.mp (by simpa using hhk)
    simp [hh]
  have hz : |h / k| ≤ 1 := by rw [abs_div, div_le_one (abs_pos.mpr hk)]; exact hhk
  obtain ⟨hl,hr⟩ := abs_le.mp hz
  let s := (1 + h / k) / 2
  let t := (1 - h / k) / 2
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hst : s + t = 1 := by dsimp [s,t]; ring
  have P := hq.2 (Set.mem_univ (a + k)) (Set.mem_univ (a - k)) hs ht hst
  have N := hq.2 (Set.mem_univ (a - k)) (Set.mem_univ (a + k)) hs ht hst
  simp only [smul_eq_mul] at P N
  have hp : s * (a + k) + t * (a - k) = a + h := by dsimp [s,t]; field_simp; ring
  have hn : s * (a - k) + t * (a + k) = a - h := by dsimp [s,t]; field_simp; ring
  rw [hp] at P
  rw [hn] at N
  nlinarith [add_le_add P N, congrArg (fun x : ℝ ↦ x * (q (a + k) + q (a - k))) hst]

private theorem thetaXi_scale_order (a h k : ℝ) (hhk : |h| ≤ |k|) :
    rationalXiThetaScale (a + k) * rationalXiThetaScale (a - k) * Real.exp (4 * Real.pi * k ^ 2) ≤
    rationalXiThetaScale (a + h) * rationalXiThetaScale (a - h) * Real.exp (4 * Real.pi * h ^ 2) := by
  let q (v : ℝ) := Real.pi * Real.exp (2 * |v|) - 9 * |v| / 2 - 2 * Real.pi * v ^ 2
  have he (v : ℝ) :
      rationalXiThetaScale (a + v) * rationalXiThetaScale (a - v) * Real.exp (4 * Real.pi * v ^ 2) =
        (4 * Real.pi ^ 2) ^ 2 * Real.exp (-(q (a + v) + q (a - v)) - 4 * Real.pi * a ^ 2) := by
    dsimp [rationalXiThetaScale,q]
    rw [show ∀ (c x y z : ℝ), c * x * (c * y) * z = c ^ 2 * (x * y * z) from fun c x y z ↦ by ring]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  rw [he,he]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  linarith [thetaXi_symmetric_order q thetaXi_potential_convex a h k hhk]

private theorem thetaXi_gaussian_moment {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2)) = (∫ x : ℝ, Real.exp (-b * x ^ 2)) / (2 * b) := by
  let g (x : ℝ) := Real.exp (-b * x ^ 2)
  have hi : Integrable g := integrable_exp_neg_mul_sq hb
  have hm : Integrable (fun x : ℝ ↦ x ^ 2 * g x) := by
    simpa only [g, Real.rpow_two] using integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1:ℝ)<2)
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ ↦ x * g x) (g x - (2 * b) * (x ^ 2 * g x)) x := by
    dsimp [g]
    convert (hasDerivAt_id x).mul ((((hasDerivAt_id x).pow 2).const_mul (-b)).exp) using 1
    all_goals try funext v
    all_goals simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
    ring
  have H := integral_eq_zero_of_hasDerivAt_of_integrable hd (hi.sub (hm.const_mul (2 * b)))
    (integrable_mul_exp_neg_mul_sq hb)
  rw [integral_sub hi (hm.const_mul _), integral_const_mul] at H
  apply (eq_div_iff (by positivity : 2 * b ≠ 0)).mpr
  change (∫ x : ℝ, x ^ 2 * g x) * (2 * b) = ∫ x : ℝ, g x
  linarith

private theorem thetaXi_reference_moment (a : ℝ) :
    let r (h : ℝ) := rationalXiThetaScale (a + h) * rationalXiThetaScale (a - h)
    Integrable r ∧ Integrable (fun h : ℝ ↦ h ^ 2 * r h) ∧
      (∫ h : ℝ, h ^ 2 * r h) ≤ (∫ h : ℝ, r h) / (8 * Real.pi) := by
  intro r
  let b := 4 * Real.pi
  let d := 1 / (2 * b)
  let g (h : ℝ) := Real.exp (-b * h ^ 2)
  let w (h : ℝ) := r h * Real.exp (b * h ^ 2)
  have hb : 0 < b := by dsimp [b]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hs : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd
  have hg : Integrable g := integrable_exp_neg_mul_sq hb
  have hgm : Integrable (fun h : ℝ ↦ h ^ 2 * g h) := by
    simpa only [g,Real.rpow_two] using integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1:ℝ)<2)
  have hr0 (h : ℝ) : 0 ≤ r h := by dsimp [r,rationalXiThetaScale]; positivity
  have hwm {s t : ℝ} (hst : |s| ≤ |t|) : w t ≤ w s :=
    thetaXi_scale_order a s t hst
  have hwr (h : ℝ) : w h * g h = r h := by
    dsimp [w,g]
    rw [mul_assoc, ← Real.exp_add, show b * h ^ 2 + -b * h ^ 2 = 0 by ring, Real.exp_zero, mul_one]
  have hub (h : ℝ) : r h ≤ w 0 * g h := by
    rw [← hwr]
    exact mul_le_mul_of_nonneg_right (hwm (by simp)) (Real.exp_pos _).le
  have hr : Integrable r := by
    apply (hg.const_mul (w 0)).mono' (by dsimp [r,rationalXiThetaScale]; fun_prop)
    filter_upwards with h
    simpa [Real.norm_eq_abs,abs_of_nonneg (hr0 h)] using hub h
  have hm : Integrable (fun h : ℝ ↦ h ^ 2 * r h) := by
    apply (hgm.const_mul (w 0)).mono' (by dsimp [r,rationalXiThetaScale]; fun_prop)
    filter_upwards with h
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (hr0 _))]
    calc
      h ^ 2 * r h ≤ h ^ 2 * (w 0 * g h) := mul_le_mul_of_nonneg_left (hub h) (sq_nonneg _)
      _ = _ := by ring
  refine ⟨hr,hm,?_⟩
  have hf (h : ℝ) :
      h ^ 2 * r h - d * r h ≤ w (Real.sqrt d) * (h ^ 2 * g h - d * g h) := by
    have hh : (h ^ 2 - d) * (w h - w (Real.sqrt d)) ≤ 0 := by
      by_cases hh : |h| ≤ |Real.sqrt d|
      · exact mul_nonpos_of_nonpos_of_nonneg (by linarith [sq_le_sq.mpr hh])
          (sub_nonneg.mpr (hwm hh))
      · exact mul_nonpos_of_nonneg_of_nonpos (by linarith [sq_le_sq.mpr (le_of_not_ge hh)])
          (sub_nonpos.mpr (hwm (le_of_not_ge hh)))
    have H := mul_nonpos_of_nonpos_of_nonneg hh (Real.exp_pos (-b * h ^ 2)).le
    change _ * g h ≤ 0 at H
    rw [← hwr]
    linarith
  have H := integral_mono (hm.sub (hr.const_mul d))
    ((hgm.sub (hg.const_mul d)).const_mul (w (Real.sqrt d))) hf
  simp only [Pi.sub_apply] at H
  rw [integral_sub hm (hr.const_mul d), integral_const_mul, integral_const_mul,
      integral_sub hgm (hg.const_mul d), integral_const_mul] at H
  have hGauss : (∫ h : ℝ, h ^ 2 * g h) = d * (∫ h : ℝ, g h) := by
    rw [show (∫ h : ℝ, h ^ 2 * g h) = (∫ h : ℝ, g h) / (2 * b) from thetaXi_gaussian_moment hb]
    dsimp [d]
    ring
  rw [hGauss,sub_self,mul_zero] at H
  have hfinal : d * (∫ h : ℝ, r h) = (∫ h : ℝ, r h) / (8 * Real.pi) := by dsimp [d,b]; ring
  linarith

/-- The symmetrically modulated pair of rational xi theta kernels has a uniform
positive lower bound relative to its envelope integral. The real interval
`t ^ 2 ≤ 2` contains the two frequencies of the compensated prime measurement. -/
theorem rationalXiThetaKernel_shiftedPair_lower (a t : ℝ) (ht : t ^ 2 ≤ 2) :
    let m := (∫ h : ℝ, rationalXiThetaScale (a + h) * rationalXiThetaScale (a - h)) / 16
    0 < m ∧ m ≤ ∫ h : ℝ, (rationalXiThetaKernel (a + h) * rationalXiThetaKernel (a - h)) * Real.cos (2 * t * h) := by
  obtain ⟨hr,hm,hv⟩ := thetaXi_reference_moment a
  have H (h : ℝ) : 0 < rationalXiThetaScale (a + h) * rationalXiThetaScale (a - h) := by
    unfold rationalXiThetaScale
    positivity
  have hi := integral_pos_of_integrable_nonneg_ne_zero
    (show Continuous (fun h : ℝ ↦ rationalXiThetaScale (a + h) * rationalXiThetaScale (a - h)) by
      unfold rationalXiThetaScale
      fun_prop) hr (fun h ↦ (H h).le) (H 0).ne'
  exact ⟨div_pos hi (by norm_num), thetaXi_shifted_lower a t ht hr hm hv⟩

end RiemannMasullo
