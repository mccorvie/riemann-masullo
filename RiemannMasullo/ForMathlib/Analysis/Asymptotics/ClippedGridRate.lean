module

public import RiemannMasullo.ForMathlib.Analysis.Asymptotics.LogMeshRate
import Mathlib.Tactic

/-! # Rates for finite grids with a clipped predictor

A clipping loss of order exp(−c√Y) and a predictor budget of order exp(4Y) give an error
of order exp(−c′√log n). The constants can be eliminated from an eventual test by using
the larger tolerance exp(−(log n)^(1/4)). -/

@[expose] public noncomputable section

open Filter Real
open scoped Topology

namespace RiemannMasullo.LogQuadrature

private theorem cutoff_budget_le {B : ℝ} (hB : 0≤B) {n : ℕ} (hn : 0<n) (hsize : B^2 ≤ (n:ℝ)) :
    B*Real.exp (4*(Real.log n/8)) ≤ (n:ℝ)+1 := by
  rw [show 4*(Real.log n/8)=Real.log n/2 by ring,Real.exp_half,
    Real.exp_log (by exact_mod_cast hn : 0<(n:ℝ))]
  have hs : B ≤ Real.sqrt (n:ℝ) := (Real.le_sqrt hB (by positivity)).mpr hsize
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) n), mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (n:ℝ))]

private theorem inverse_sqrt_le_rootLog {n : ℕ} (hn : 0 < n) (hq : 2 ≤ meshScale n) :
    1/Real.sqrt ((n:ℝ)+1) ≤ Real.exp (-meshScale n) := by
  have hpos : 0 < (n:ℝ) := by exact_mod_cast hn
  calc
    _ ≤ 1 / Real.sqrt (n:ℝ) := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpos) (Real.sqrt_le_sqrt (by linarith))
    _ = Real.exp (-(Real.log n/2)) := by rw [Real.exp_neg,Real.exp_half,Real.exp_log hpos,one_div]
    _ ≤ _ := by
      apply Real.exp_monotone
      rw [←meshScale_sq hn]
      nlinarith [mul_nonneg (sub_nonneg.mpr hq) (by linarith : 0≤meshScale n)]

private theorem finite_trial_cost {x R L b B : ℝ} (hx : 1≤x) (hR : R≤1)
    (hb : 0≤b) (hL : L≤b) (hB : B≤x^2) :
    (1+x⁻¹)*(R+2*L) + (1+(x⁻¹)⁻¹) * (B/(x^2)^2) ≤ R+4*b+3/x := by
  have hx0 : 0<x := by linarith
  have hi : x⁻¹≤1 := (inv_le_one₀ hx0).mpr hx
  have htop : (1+x⁻¹)*(R+2*L) ≤ R+4*b+x⁻¹ := by
    calc
      _ ≤ (1+x⁻¹)*(R+2*b) := by gcongr
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hR (inv_nonneg.mpr hx0.le),
        mul_le_mul_of_nonneg_right hi hb]
  have hend : (1+x)* (B/(x^2)^2) ≤ 2/x := by
    calc
      _ ≤ (1+x)*(x^2/(x^2)^2) := by gcongr
      _ = (1+x)/x^2 := by field_simp
      _ ≤ 2/x := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hx0) hx0).mpr
        nlinarith [mul_nonneg (sub_nonneg.mpr hx) hx0.le]
  rw [inv_inv]
  linarith [show x⁻¹+2/x=3/x by ring]

private theorem square_gap_of_small_root {u v h : ℝ} (hu : 0 ≤ u) (hu1 : u≤1)
    (hv : 0 ≤ v) (hh : 0 ≤ h) (hut : Real.sqrt u ≤ Real.sqrt v + h) : u≤v+2*h := by
  by_cases hx : u≤v
  · linarith
  have hr : Real.sqrt v ≤ Real.sqrt u := Real.sqrt_le_sqrt (le_of_not_ge hx)
  have hroot : Real.sqrt u ≤ 1 := by simpa using Real.sqrt_le_sqrt hu1
  have hd : 0 ≤ Real.sqrt u-Real.sqrt v := sub_nonneg.mpr hr
  have hsum : Real.sqrt u+Real.sqrt v ≤ 2 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hd
  nlinarith [Real.sq_sqrt hu,Real.sq_sqrt hv]

/-- A one-sided finite-predictor estimate with an integrated clipping tail
gives the same stretched-exponential rate in the grid index. -/
theorem rootLogRate_of_clipped_grid {u : ℕ → ℝ} {loss : ℝ → ℝ} {R K B : ℝ}
    (hR : 0 ≤ R) (hR1 : R ≤ 1) (hK : 0 ≤ K) (hB0 : 0≤B)
    (hu : ∀ᶠ n : ℕ in atTop, R ≤ u n ∧ u n ≤ 1)
    (hl : ∃ C > 0, ∃ c > 0, ∀ᶠ Y : ℝ in atTop,
      loss Y ≤ C*Real.exp (-c*Real.sqrt Y))
    (ht : ∀ᶠ n : ℕ in atTop, ∀ Y τ : ℝ, 0 ≤ Y → 0 < τ →
      B*Real.exp (4*Y) ≤ (n:ℝ)+1 →
      ∃ v ≥ 0, v ≤ (1+τ)*(R+2*loss Y)+(1+τ⁻¹)*(B*Real.exp (4*Y)/((n:ℝ)+1)^2) ∧
        Real.sqrt (u n) ≤ Real.sqrt v+K/Real.sqrt ((n:ℝ)+1)) :
    HasRootLogRate (fun n ↦ u n-R) := by
  obtain ⟨C,hC,c,hc,hl⟩ := hl
  have hY : Tendsto (fun n : ℕ ↦ Real.log (n:ℝ)/8) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num) (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  let d := min (c/Real.sqrt 8) 1
  have hd : 0<d := lt_min (div_pos hc (by positivity)) zero_lt_one
  refine ⟨4*C+(3+2*K),by positivity,d,hd,?_⟩
  filter_upwards [hu,ht,hY.eventually hl,tendsto_natCast_atTop_atTop.eventually_ge_atTop (B^2),eventually_gt_atTop (0:ℕ),
      meshScale_atTop.eventually_ge_atTop 2] with n hun htn hln hn hn0 hq
  let x := Real.sqrt ((n:ℝ)+1)
  have hx2 : x^2=(n:ℝ)+1 := Real.sq_sqrt (by positivity)
  have hx : 1≤x := by dsimp [x]; simp
  let Y := Real.log (n:ℝ)/8
  have hY0 : 0≤Y := div_nonneg (Real.log_nonneg (by exact_mod_cast hn0)) (by norm_num)
  have hB := cutoff_budget_le hB0 hn0 hn
  obtain ⟨v,hv,hve,hvn⟩ := htn Y x⁻¹ hY0 (by positivity) hB
  let q := meshScale n
  have hq0 : 0≤q := by dsimp [q]; linarith
  have hclip : Real.sqrt Y = q/Real.sqrt 8 := by
    dsimp [Y,q,meshScale]
    rw [Real.sqrt_div (Real.log_nonneg (by exact_mod_cast hn0))]
  have hcdec : Real.exp (-c*Real.sqrt Y) ≤ Real.exp (-d*q) := by
    rw [hclip]
    apply Real.exp_monotone
    have h := mul_le_mul_of_nonneg_right (min_le_left (c/Real.sqrt 8) 1) hq0
    dsimp [d]
    linarith [show -c*(q/Real.sqrt 8) = -(c/Real.sqrt 8)*q by ring]
  have hdec : 1/x ≤ Real.exp (-d*q) := (inverse_sqrt_le_rootLog hn0 hq).trans (by
    apply Real.exp_monotone
    have hh := mul_le_mul_of_nonneg_right (min_le_right (c/Real.sqrt 8) 1) hq0
    dsimp [d,q] at *
    linarith)
  have he : loss Y ≤ C*Real.exp (-d*q) := hln.trans (mul_le_mul_of_nonneg_left hcdec hC.le)
  have hcst := finite_trial_cost (R:=R) (B:=B*Real.exp (4*Y)) hx hR1
    (mul_nonneg hC.le (Real.exp_pos _).le) he (hx2.symm ▸ hB)
  rw [hx2] at hcst
  have hupper := square_gap_of_small_root (hR.trans hun.1) hun.2 hv (by positivity) hvn
  change |u n-R| ≤ _
  rw [abs_of_nonneg (sub_nonneg.mpr hun.1)]
  have herr := add_le_add (mul_le_mul_of_nonneg_left hdec (by norm_num : (0:ℝ)≤3))
    (mul_le_mul_of_nonneg_left hdec (by positivity : 0≤2*K))
  calc
    _ ≤ 4*(C*Real.exp (-d*q))+3/x+2*(K/x) := by linarith
    _ ≤ 4*(C*Real.exp (-d*q))+(3+2*K)*Real.exp (-d*q) := by
      rw [show 4*(C*Real.exp (-d*q))+3/x+2*(K/x) = 4*(C*Real.exp (-d*q))+(3*(1/x)+(2*K)*(1/x)) by ring]
      linarith
    _ = _ := by dsimp [q]; ring

/-- A root-log rate eventually lies below one fixed tolerance, independently
of both constants in the rate. -/
theorem HasRootLogRate.eventually_le_exp_neg_sqrt_meshScale {u : ℕ → ℝ}
    (hu : HasRootLogRate u) :
    ∀ᶠ n : ℕ in atTop, u n ≤ Real.exp (-Real.sqrt (meshScale n)) := by
  obtain ⟨C,hC,c,hc,hbound⟩ := hu
  have hq := Real.tendsto_sqrt_atTop.comp meshScale_atTop
  filter_upwards [hbound, hq.eventually_ge_atTop (2/c), hq.eventually_ge_atTop (Real.log C)]
    with n hn hq' hC'
  let q := meshScale n
  have hq0 : 0≤q := by dsimp [q,meshScale]; positivity
  have hx : 2 ≤ Real.sqrt q*c := (div_le_iff₀ hc).mp hq'
  have hlarge := mul_le_mul_of_nonneg_right hx (Real.sqrt_nonneg q)
  calc
    u n ≤ |u n| := le_abs_self _
    _ ≤ C*Real.exp (-c*q) := hn
    _ = Real.exp (Real.log C-c*q) := by
      rw [show Real.log C-c*q = Real.log C+(-c*q) by ring, Real.exp_add, Real.exp_log hC]
    _ ≤ Real.exp (-Real.sqrt q) := by
      apply Real.exp_monotone
      change Real.log C ≤ Real.sqrt q at hC'
      nlinarith [Real.sq_sqrt hq0]

end RiemannMasullo.LogQuadrature
