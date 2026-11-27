module

public import RiemannMasullo.Ch09_HardySobolev.Sec2
public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplaceDerivatives
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped ENNReal

/-! # A pure area norm for the positive-width Mellin strip

For every nonnegative Sobolev order, a sufficiently high finite strip jet with a
weight vanishing towards the boundary has a norm equivalent to the centered
interval Sobolev norm. No boundary trace term is needed for this comparison.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Real Set
open scoped Interval

namespace RiemannMasullo

private def laplaceWindowKernel (p r t : ℝ) : ℝ := t ^ (p - 1) * exp (-(r * t))

private theorem continuous_laplaceWindowKernel {p : ℝ} (hp : 1 ≤ p) (r : ℝ) :
    Continuous (laplaceWindowKernel p r) :=
  (continuous_id.rpow_const (fun _ ↦ Or.inr (sub_nonneg.mpr hp))).mul
    ((continuous_const.mul continuous_id).neg.rexp)

private theorem laplaceWindowKernel_nonneg (p r : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ laplaceWindowKernel p r t := mul_nonneg (rpow_nonneg ht _) (exp_pos _).le

private theorem laplaceWindowKernel_mono_rate (p : ℝ) {r s t : ℝ}
    (hrs : r ≤ s) (ht : 0 ≤ t) : laplaceWindowKernel p s t ≤ laplaceWindowKernel p r t :=
  mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hrs ht)))
    (rpow_nonneg ht _)

private theorem laplaceWindow_rescale {α p y : ℝ} (hα : 0 ≤ α) (hy : 0 ≤ y) :
    (∫ t in (0 : ℝ)..α, laplaceWindowKernel p (2*y) t) =
      (1+y)^(-p) * ∫ t in (0 : ℝ)..((1+y)*α), laplaceWindowKernel p (2*y/(1+y)) t := by
  let c := 1+y
  have hc : 0 < c := by dsimp [c]; linarith
  have he : (∫ t in (0 : ℝ)..α, laplaceWindowKernel p (2*y) t) =
      (c^(p-1))⁻¹ * ∫ t in (0 : ℝ)..α, laplaceWindowKernel p (2*y/c) (c*t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hα] at ht
    unfold laplaceWindowKernel
    dsimp only
    rw [Real.mul_rpow hc.le ht.1, ← mul_assoc, ← mul_assoc,
      inv_mul_cancel₀ (rpow_pos_of_pos hc _).ne', one_mul]
    have hrate : 2*y/c*(c*t)=2*y*t := by field_simp [hc.ne']
    rw [hrate]
  rw [he, intervalIntegral.integral_comp_mul_left _ hc.ne', mul_zero, smul_eq_mul, ← mul_assoc]
  change (c ^ (p-1))⁻¹ * c⁻¹ * _ = c ^ (-p) * _
  rw [← rpow_neg hc.le, ← rpow_neg_one, ← rpow_add hc]
  congr 2
  ring

/-- For positive width, truncated Laplace integrals have power decay in the ordinate.
The range `1 ≤ p` suffices for every real Sobolev order by choosing sufficiently
many strip derivatives. The constants are independent of the ordinate. -/
theorem laplaceWindow_comparable {α p : ℝ} (hα : 0 < α) (hp : 1 ≤ p) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ y : ℝ, 0 ≤ y →
      c * (1+y)^(-p) ≤ (∫ t in (0 : ℝ)..α, t^(p - 1) * exp (-(2*y*t))) ∧
      (∫ t in (0 : ℝ)..α, t^(p - 1) * exp (-(2*y*t))) ≤ C * (1+y)^(-p) := by
  let G := laplaceWindowKernel p
  have hcont (r : ℝ) : Continuous (G r) := continuous_laplaceWindowKernel hp r
  have hint (r M : ℝ) : IntervalIntegrable (G r) volume 0 M := (hcont r).intervalIntegrable _ _
  have hn (r : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ G r t := laplaceWindowKernel_nonneg p r ht
  let c := ∫ t in (0 : ℝ)..α, G 2 t
  let C := max (∫ t in (0 : ℝ)..(2*α), G 0 t) (Gamma p)
  have hc : 0 < c := intervalIntegral.intervalIntegral_pos_of_pos_on (hint 2 α)
    (fun t ht ↦ mul_pos (rpow_pos_of_pos ht.1 _) (exp_pos _)) hα
  have hp' : 0 < p := zero_lt_one.trans_le hp
  refine ⟨c, C, hc, (Gamma_pos_of_pos hp').trans_le (le_max_right _ _), fun y hy ↦ ?_⟩
  let b := (1+y)*α
  let r := 2*y/(1+y)
  have hcy : 0 < 1+y := by linarith
  have hb : α ≤ b := by dsimp [b]; nlinarith [mul_nonneg hy hα.le]
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr2 : r ≤ 2 := (div_le_iff₀ hcy).2 (by linarith)
  have hn0 (rate : ℝ) : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) b)] G rate :=
    (ae_restrict_mem measurableSet_Ioc).mono (fun _ ht ↦ hn rate ht.1.le)
  have hcJ : c ≤ ∫ t in (0 : ℝ)..b, G r t := by
    calc
      c ≤ ∫ t in (0 : ℝ)..α, G r t :=
        intervalIntegral.integral_mono_on hα.le (hint _ _) (hint _ _)
          (fun _ ht ↦ laplaceWindowKernel_mono_rate p hr2 ht.1)
      _ ≤ _ := intervalIntegral.integral_mono_interval le_rfl hα.le hb (hn0 r) (hint _ _)
  have hJC : (∫ t in (0 : ℝ)..b, G r t) ≤ C := by
    by_cases hy1 : y ≤ 1
    · have hb2 : b ≤ 2*α := by dsimp [b]; nlinarith [mul_nonneg (sub_nonneg.mpr hy1) hα.le]
      calc
        _ ≤ ∫ t in (0 : ℝ)..b, G 0 t :=
          intervalIntegral.integral_mono_on (hα.le.trans hb) (hint _ _) (hint _ _)
            (fun _ ht ↦ laplaceWindowKernel_mono_rate p hr0 ht.1)
        _ ≤ ∫ t in (0 : ℝ)..(2*α), G 0 t := by
          apply intervalIntegral.integral_mono_interval le_rfl (hα.le.trans hb) hb2 _ (hint _ _)
          exact (ae_restrict_mem measurableSet_Ioc).mono (fun _ ht ↦ hn 0 ht.1.le)
        _ ≤ C := le_max_left _ _
    · have hr1 : 1 ≤ r := (le_div_iff₀ hcy).2 (by linarith)
      have hEq : G 1 = fun t : ℝ ↦ exp (-t) * t^(p-1) := by
        funext t
        simp [G, laplaceWindowKernel, mul_comm]
      have hG : IntegrableOn (G 1) (Ioi 0) := by
        rw [hEq]
        exact Real.GammaIntegral_convergent hp'
      have hI : (∫ t in Ioi (0 : ℝ), G 1 t) = Gamma p := by
        rw [hEq]
        exact (Real.Gamma_eq_integral hp').symm
      calc
        _ ≤ ∫ t in (0 : ℝ)..b, G 1 t :=
          intervalIntegral.integral_mono_on (hα.le.trans hb) (hint _ _) (hint _ _)
            (fun _ ht ↦ laplaceWindowKernel_mono_rate p hr1 ht.1)
        _ ≤ ∫ t in Ioi (0 : ℝ), G 1 t := by
          rw [intervalIntegral.integral_of_le (hα.le.trans hb)]
          exact setIntegral_mono_set hG
            ((ae_restrict_iff' measurableSet_Ioi).2 (.of_forall fun _ ht ↦ hn 1 ht.le))
            (.of_forall fun _ ht ↦ ht.1)
        _ ≤ C := hI ▸ le_max_right _ _
  change c * (1+y)^(-p) ≤ (∫ t in (0 : ℝ)..α, G (2*y) t) ∧
    (∫ t in (0 : ℝ)..α, G (2*y) t) ≤ C * (1+y)^(-p)
  rw [laplaceWindow_rescale hα.le hy]
  have hd : 0 ≤ (1+y)^(-p) := rpow_nonneg hcy.le _
  exact ⟨by rw [mul_comm c]; exact mul_le_mul_of_nonneg_left hcJ hd,
    by rw [mul_comm C]; exact mul_le_mul_of_nonneg_left hJC hd⟩

open Finset

/-- Fourier-side weight of the pure area integral, before summing derivative orders. -/
def stripAreaWindow (α p x : ℝ) : ℝ :=
  ∫ σ in -α..α, (α - |σ|) ^ (p - 1) * exp (2 * σ * x)

private def halfAreaWindow (α p x : ℝ) : ℝ :=
  ∫ σ in (0 : ℝ)..α, (α - σ) ^ (p - 1) * exp (2 * σ * x)

private theorem halfAreaWindow_eq (α p x : ℝ) :
    halfAreaWindow α p x = exp (2*α*x) *
      ∫ t in (0 : ℝ)..α, t^(p-1) * exp (-(2*x*t)) := by
  let F := fun σ : ℝ ↦ (α-σ)^(p-1) * exp (2*σ*x)
  have href : (∫ t in (0 : ℝ)..α, F (α-t)) = halfAreaWindow α p x := by
    simpa only [sub_self, sub_zero, halfAreaWindow, F] using
      (intervalIntegral.integral_comp_sub_left (a := 0) (b := α) F α)
  rw [← href, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [F]
  rw [show α-(α-t)=t by ring, show 2*(α-t)*x = 2*α*x + -(2*x*t) by ring, exp_add]
  ring

private theorem stripAreaWindow_split {α p : ℝ} (hα : 0 ≤ α) (hp : 1 ≤ p) (x : ℝ) :
    stripAreaWindow α p x = halfAreaWindow α p |x| + halfAreaWindow α p (-|x|) := by
  let F := fun σ : ℝ ↦ (α - |σ|)^(p-1) * exp (2*σ*x)
  have hF : Continuous F := by
    exact ((continuous_const.sub continuous_abs).rpow_const (fun _ ↦ Or.inr (sub_nonneg.mpr hp))).mul
      (((continuous_const.mul continuous_id).mul continuous_const).rexp)
  have href : (∫ σ in (0 : ℝ)..α, F (-σ)) = ∫ σ in -α..0, F σ := by
    simpa only [neg_zero] using (intervalIntegral.integral_comp_neg (a := 0) (b := α) F)
  have hleft : (∫ σ in -α..0, F σ) = halfAreaWindow α p (-x) := by
    rw [← href]
    apply intervalIntegral.integral_congr
    intro σ hσ
    rw [uIcc_of_le hα] at hσ
    dsimp [F]
    rw [abs_neg, abs_of_nonneg hσ.1, show 2*(-σ)*x = 2*σ*(-x) by ring]
  have hright : (∫ σ in (0 : ℝ)..α, F σ) = halfAreaWindow α p x := by
    apply intervalIntegral.integral_congr
    intro σ hσ
    rw [uIcc_of_le hα] at hσ
    simp only [F, abs_of_nonneg hσ.1]
  change (∫ σ in -α..α, F σ) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable (-α) 0)
    (hF.intervalIntegrable 0 α), hleft, hright]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, add_comm]
  · rw [abs_of_nonpos hx, neg_neg]

/-- Exact endpoint scalings of both halves of the symmetric strip. -/
theorem stripAreaWindow_eq_laplace {α p : ℝ} (hα : 0 ≤ α) (hp : 1 ≤ p) (x : ℝ) :
    stripAreaWindow α p x =
      exp (2 * α * |x|) * (∫ t in (0 : ℝ)..α, t^(p-1) * exp (-(2 * |x| * t))) +
      exp (2 * α * (-|x|)) * (∫ t in (0 : ℝ)..α, t^(p-1) * exp (-(2 * (-|x|) * t))) := by
  rw [stripAreaWindow_split hα hp, halfAreaWindow_eq, halfAreaWindow_eq]

/-- The growing half of the strip controls the entire area window, within a factor two. -/
theorem stripAreaWindow_comparable {α p : ℝ} (hα : 0 < α) (hp : 1 ≤ p) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ,
      c * (exp (2*α*|x|) * (1+|x|)^(-p)) ≤ stripAreaWindow α p x ∧
      stripAreaWindow α p x ≤ C * (exp (2*α*|x|) * (1+|x|)^(-p)) := by
  obtain ⟨c, C, hc, hC, h⟩ := laplaceWindow_comparable hα hp
  refine ⟨c, 2*C, hc, by positivity, fun x ↦ ?_⟩
  have hhalf (z : ℝ) : Continuous (fun σ : ℝ ↦ (α-σ)^(p-1) * exp (2*σ*z)) :=
    ((continuous_const.sub continuous_id).rpow_const (fun _ ↦ Or.inr (sub_nonneg.mpr hp))).mul
      (((continuous_const.mul continuous_id).mul continuous_const).rexp)
  have hn : 0 ≤ halfAreaWindow α p (-|x|) := by
    apply intervalIntegral.integral_nonneg hα.le
    intro σ hσ
    exact mul_nonneg (rpow_nonneg (sub_nonneg.mpr hσ.2) _) (exp_pos _).le
  have hm : halfAreaWindow α p (-|x|) ≤ halfAreaWindow α p |x| := by
    apply intervalIntegral.integral_mono_on hα.le ((hhalf _).intervalIntegrable _ _)
      ((hhalf _).intervalIntegrable _ _)
    intro σ hσ
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (neg_le_self (abs_nonneg x)) (by linarith [hσ.1]))) (rpow_nonneg (sub_nonneg.mpr hσ.2) _)
  obtain ⟨hl, hu⟩ := h |x| (abs_nonneg x)
  replace hl := mul_le_mul_of_nonneg_left hl (exp_pos (2*α*|x|)).le
  replace hu := mul_le_mul_of_nonneg_left hu (exp_pos (2*α*|x|)).le
  rw [← halfAreaWindow_eq] at hl hu
  rw [stripAreaWindow_split hα.le hp]
  constructor <;> nlinarith only [hl, hu, hn, hm]

private theorem stripJetPolynomial_bounds (m : ℕ) (x : ℝ) :
    (1+|x|)^(2*m) ≤ (2:ℝ)^(2*m) * (∑ j ∈ range (m+1), (x^j)^2) ∧
    (∑ j ∈ range (m+1), (x^j)^2) ≤ ((m:ℝ)+1) * (1+|x|)^(2*m) := by
  let q := max 1 |x|
  have hq1 : 1 ≤ q := le_max_left _ _
  have hqx : |x| ≤ q := le_max_right _ _
  have he (j : ℕ) : (x^j)^2 = |x|^(2*j) := by
    rw [Nat.mul_comm 2 j, pow_mul, ← abs_pow, sq_abs]
  have htop (j : ℕ) (hj : j ≤ m) : (x^j)^2 ≤ ∑ k ∈ range (m+1), (x^k)^2 :=
    single_le_sum (fun k _ ↦ sq_nonneg (x^k)) (mem_range_succ_iff.mpr hj)
  have hq : q^(2*m) ≤ ∑ k ∈ range (m+1), (x^k)^2 := by
    rcases le_total 1 |x| with hx | hx
    · simpa only [q, max_eq_right hx, ← he] using htop m le_rfl
    · simpa [q, max_eq_left hx] using htop 0 (Nat.zero_le m)
  constructor
  · calc
      _ ≤ (2*q)^(2*m) := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_left hq (by positivity)
  · calc
      _ ≤ ∑ j ∈ range (m+1), (1+|x|)^(2*m) := by
        refine sum_le_sum fun j hj ↦ ?_
        rw [he]
        exact (pow_le_pow_left₀ (abs_nonneg x) (by linarith : |x| ≤ 1+|x|) _).trans
          (pow_le_pow_right₀ (by linarith [abs_nonneg x]) (Nat.mul_le_mul_left 2 (mem_range_succ_iff.mp hj)))
      _ = _ := by simp

/-- With `p = 2m - s ≥ 1`, the sum of all pure area jet weights up to order `m`
recovers the centered interval Sobolev density up to constants independent of `x`. -/
theorem stripAreaJetWeight_comparable {α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s)
    (m : ℕ) (hp : 1 ≤ 2*(m:ℝ)-s) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ,
      c * intervalSobolevDensity (-α) α s x ≤
        (∑ j ∈ range (m+1), (x^j)^2) * stripAreaWindow α (2*(m:ℝ)-s) x ∧
      (∑ j ∈ range (m+1), (x^j)^2) * stripAreaWindow α (2*(m:ℝ)-s) x ≤
        C * intervalSobolevDensity (-α) α s x := by
  obtain ⟨c, C, hc, hC, hwin⟩ := stripAreaWindow_comparable hα hp
  let K := (2:ℝ)^(2*m)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨c/K, ((m:ℝ)+1)*C*(4:ℝ)^(s/2), div_pos hc hK, by positivity, fun x ↦ ?_⟩
  let u := 1+|x|
  let D := 1+x^2
  let E := exp (2*α*|x|)
  let P := ∑ j ∈ range (m+1), (x^j)^2
  have hu : 0 < u := by dsimp [u]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := (exp_pos _).le
  have hP : 0 ≤ P := sum_nonneg fun j _ ↦ sq_nonneg _
  have hed : intervalSobolevDensity (-α) α s x = E * D^(s/2) := by
    unfold intervalSobolevDensity E D
    rcases le_total 0 x with hx | hx
    · have h : 2*(-α)*x ≤ 2*α*x := by nlinarith [mul_nonneg hα.le hx]
      rw [abs_of_nonneg hx, max_eq_right (exp_le_exp.mpr h)]
    · have h : 2*α*x ≤ 2*(-α)*x := by nlinarith [mul_nonpos_of_nonneg_of_nonpos hα.le hx]
      rw [abs_of_nonpos hx, max_eq_left (exp_le_exp.mpr h), show 2*(-α)*x = 2*α*(-x) by ring]
  have hs2 : 0 ≤ s/2 := by linarith
  have hsq : (u^2)^(s/2) = u^s := by
    rw [← rpow_natCast u 2, ← rpow_mul hu.le]
    congr 1
    push_cast
    ring
  have hlow : D^(s/2) ≤ u^s := by
    rw [← hsq]; apply rpow_le_rpow hD _ hs2
    dsimp [D,u]; nlinarith [sq_abs x, abs_nonneg x]
  have hhigh : u^s ≤ (4:ℝ)^(s/2)*D^(s/2) := by
    rw [← hsq, ← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hD]
    apply rpow_le_rpow (sq_nonneg _) _ hs2
    dsimp [D,u]; nlinarith [sq_abs x, sq_nonneg (|x|-1)]
  have hcancel : u^(2*m) * u^(-(2*(m:ℝ)-s)) = u^s := by
    rw [← rpow_natCast, ← rpow_add hu]; push_cast; ring_nf
  obtain ⟨hl, hh⟩ := stripJetPolynomial_bounds m x
  change u^(2*m) ≤ K*P at hl
  change P ≤ ((m:ℝ)+1)*u^(2*m) at hh
  obtain ⟨hw₁, hw₂⟩ := hwin x
  change c*(E*u^(-(2*(m:ℝ)-s))) ≤ _ at hw₁
  change _ ≤ C*(E*u^(-(2*(m:ℝ)-s))) at hw₂
  rw [hed]
  constructor
  · calc
      _ ≤ (c/K)*(E*u^s) := by gcongr
      _ = (u^(2*m)/K)*(c*(E*u^(-(2*(m:ℝ)-s)))) := by rw [← hcancel]; ring
      _ ≤ _ := mul_le_mul ((div_le_iff₀ hK).2 (by simpa [mul_comm] using hl)) hw₁
        (by positivity) hP
  · calc
      _ ≤ (((m:ℝ)+1)*u^(2*m))*(C*(E*u^(-(2*(m:ℝ)-s)))) :=
        (mul_le_mul_of_nonneg_left hw₂ hP).trans (mul_le_mul_of_nonneg_right hh (by positivity))
      _ = (((m:ℝ)+1)*C*E)*u^s := by rw [← hcancel]; ring
      _ ≤ (((m:ℝ)+1)*C*E)*((4:ℝ)^(s/2)*D^(s/2)) := by gcongr
      _ = _ := by ring

/-- Every nonnegative order admits the pure area construction with a nonnegative
boundary-distance exponent; no boundary trace term enters the comparison. -/
theorem exists_stripAreaJetWeight_comparable {α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s) :
    ∃ m : ℕ, 1 ≤ 2*(m:ℝ)-s ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ,
      c * intervalSobolevDensity (-α) α s x ≤
        (∑ j ∈ range (m+1), (x^j)^2) * stripAreaWindow α (2*(m:ℝ)-s) x ∧
      (∑ j ∈ range (m+1), (x^j)^2) * stripAreaWindow α (2*(m:ℝ)-s) x ≤
        C * intervalSobolevDensity (-α) α s x := by
  obtain ⟨m, hm⟩ := exists_nat_gt (s+1)
  have hp : 1 ≤ 2*(m:ℝ)-s := by linarith
  exact ⟨m, hp, stripAreaJetWeight_comparable hα hs m hp⟩

/-- The lower integral of the squared strip jet with the boundary-distance area weight. -/
def stripAreaJetEnergy (α s : ℝ) (m : ℕ) (F : ℂ → ℂ) : ℝ≥0∞ :=
  ∫⁻ σ in Ioo (-α) α, ENNReal.ofReal ((α - |σ|) ^ (2 * (m : ℝ) - s - 1)) *
    ∫⁻ t : ℝ, ∑ k ∈ range (m + 1), ‖iteratedDeriv k F ((σ : ℂ) + t * Complex.I)‖ₑ ^ 2

private theorem lintegral_stripAreaWindow {α p : ℝ}
    (hα : 0 ≤ α) (hp : 1 ≤ p) (x : ℝ) :
    ∫⁻ σ in Ioo (-α) α, ENNReal.ofReal ((α - |σ|) ^ (p - 1)) *
        ENNReal.ofReal (exp (2 * σ * x)) = ENNReal.ofReal (stripAreaWindow α p x) := by
  have hle : -α ≤ α := by linarith
  let F (σ : ℝ) := (α - |σ|) ^ (p - 1) * exp (2 * σ * x)
  have hc : Continuous F :=
    ((continuous_const.sub continuous_abs).rpow_const (fun _ ↦ Or.inr (sub_nonneg.mpr hp))).mul
      (((continuous_const.mul continuous_id).mul continuous_const).rexp)
  have hint : IntegrableOn F (Ioo (-α) α) :=
    (hc.intervalIntegrable (-α) α).1.mono Ioo_subset_Ioc_self le_rfl
  have hn (σ : ℝ) (hσ : σ ∈ Ioo (-α) α) : 0 ≤ (α - |σ|) ^ (p - 1) :=
    rpow_nonneg (sub_nonneg.mpr (abs_lt.mpr hσ).le) _
  calc
    _ = ∫⁻ σ in Ioo (-α) α, ENNReal.ofReal (F σ) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro σ hσ
      exact (ENNReal.ofReal_mul (hn σ hσ)).symm
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        ((ae_restrict_mem measurableSet_Ioo).mono (fun σ hσ ↦ mul_nonneg (hn σ hσ) (exp_pos _).le))]
      rw [stripAreaWindow, intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo]

/-- Weighted area Plancherel with the scalar strip window made explicit. -/
theorem stripAreaJetEnergy_bilateralLaplace {α s : ℝ} {f : ℝ → ℂ}
    (hα : 0 ≤ α) (m : ℕ) (hp : 1 ≤ 2 * (m : ℝ) - s)
    (hf : MemLp (fun x : ℝ ↦ exp (α * |x|) • f x) 2) :
    stripAreaJetEnergy α s m (bilateralLaplace f) =
      ENNReal.ofReal (2 * π) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ 2 *
        ENNReal.ofReal ((∑ k ∈ range (m + 1), (x^k)^2) * stripAreaWindow α (2 * (m : ℝ) - s) x) := by
  have hc : Continuous (fun σ : ℝ ↦ (α - |σ|) ^ (2 * (m : ℝ) - s - 1)) :=
    (continuous_const.sub continuous_abs).rpow_const (fun _ ↦ Or.inr (sub_nonneg.mpr hp))
  have hw := hc.measurable.ennreal_ofReal
  rw [stripAreaJetEnergy, lintegral_strip_sum_enorm_sq_iteratedDeriv_bilateralLaplace hf _ hw]
  simp_rw [lintegral_stripAreaWindow hα hp, ← ENNReal.ofReal_mul (sum_nonneg (fun _ _ ↦ sq_nonneg _))]

/-- The pure area squared norm and the centered interval Sobolev squared norm are
equivalent, with constants independent of the function. -/
theorem stripAreaJetEnergy_bilateralLaplace_comparable {α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s)
    (m : ℕ) (hp : 1 ≤ 2 * (m : ℝ) - s) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (f : ℝ → ℂ),
      MemLp (fun x : ℝ ↦ exp (α * |x|) • f x) 2 →
      let E := ∫⁻ x : ℝ, ‖f x‖ₑ ^ 2 * ENNReal.ofReal (intervalSobolevDensity (-α) α s x)
      ENNReal.ofReal c * E ≤ stripAreaJetEnergy α s m (bilateralLaplace f) ∧
        stripAreaJetEnergy α s m (bilateralLaplace f) ≤ ENNReal.ofReal C * E := by
  obtain ⟨c, C, hc, hC, h⟩ := stripAreaJetWeight_comparable hα hs m hp
  refine ⟨2 * π * c, 2 * π * C, by positivity, by positivity, fun f hf ↦ ?_⟩
  have hconst (d : ℝ) :
      ENNReal.ofReal (2 * π * d) *
          (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2 * ENNReal.ofReal (intervalSobolevDensity (-α) α s x)) =
        ENNReal.ofReal (2 * π) *
          (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2 * ENNReal.ofReal (d * intervalSobolevDensity (-α) α s x)) := by
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * π), mul_assoc,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    apply lintegral_congr
    intro x
    have hn : 0 ≤ intervalSobolevDensity (-α) α s x := by
      unfold intervalSobolevDensity
      positivity
    rw [ENNReal.ofReal_mul' hn]
    ac_rfl
  dsimp only
  rw [stripAreaJetEnergy_bilateralLaplace hα.le m hp hf, hconst, hconst]
  exact ⟨mul_le_mul' le_rfl (lintegral_mono (fun x ↦
    mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (h x).1))),
    mul_le_mul' le_rfl (lintegral_mono (fun x ↦
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (h x).2)))⟩

end RiemannMasullo
