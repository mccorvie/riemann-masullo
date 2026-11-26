module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Scalar estimates for logarithmic sampling on a mesh of width one over n. -/

@[expose] public noncomputable section

open Filter Real
open scoped Topology
namespace RiemannMasullo.LogQuadrature

/-- The slowly growing height parameter used for the mesh analysis. -/
def meshScale (n : ℕ) : ℝ := √(log n)

/-- An error bounded by a stretched exponential in the square root of log n. -/
def HasRootLogRate (e : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∃ c > 0, ∀ᶠ n : ℕ in atTop, |e n| ≤ C * exp (-c * meshScale n)

theorem meshScale_atTop : Tendsto meshScale atTop atTop :=
  tendsto_sqrt_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem meshScale_sq {n : ℕ} (hn : 0 < n) : meshScale n ^ 2 = log n :=
  Real.sq_sqrt (log_nonneg (by exact_mod_cast hn))

theorem exp_meshScale_sq {n : ℕ} (hn : 0 < n) : exp (meshScale n ^ 2) = n := by
  rw [meshScale_sq hn,exp_log (by positivity)]

/-- The polynomial local modulus at exp (q) is eventually smaller than exp (q²/2). -/
theorem eventually_mesh_polynomial (C : ℝ) (hC : 0 ≤ C) (p : ℕ) :
    ∀ᶠ q : ℝ in atTop, 1+C*(2+exp q)^p ≤ exp (q^2/2) := by
  filter_upwards [eventually_ge_atTop (2*((p:ℝ)+1)+C+2*p+4)] with q hq
  have hp := Nat.cast_nonneg (α:=ℝ) p
  have hq0 : 0 ≤ q := by linarith
  have he := one_le_exp hq0
  have hbase : 2+exp q ≤ exp (q+2) := by
    rw [exp_add]
    nlinarith [mul_le_mul_of_nonneg_left (Real.add_one_le_exp (2:ℝ)) (exp_pos q).le]
  have h₁ : 1 ≤ (2+exp q)^p := one_le_pow₀ (by linarith)
  have hC1 : 1+C ≤ exp (C+1) := by linarith [Real.add_one_le_exp (C+1)]
  calc
    1+C*(2+exp q)^p ≤ (1+C)*(2+exp q)^p := by nlinarith
    _ ≤ exp (C+1)*(exp (q+2))^p :=
      mul_le_mul hC1 (pow_le_pow_left₀ (by positivity) hbase p) (by positivity) (exp_pos _).le
    _ = exp (C+1+p*(q+2)) := by rw [exp_add (C+1) _, exp_nat_mul]
    _ ≤ exp (q^2/2) := by
      apply exp_monotone
      nlinarith [mul_nonneg (show 0 ≤ q/2-((p:ℝ)+1) by linarith) hq0]

theorem mesh_height_damping {q : ℝ} (hq : 0 ≤ q) :
    q^2 * exp (-q/2) ≤ 32 * exp (-q/4) := by
  have h := Real.pow_div_factorial_le_exp (q/4) (by positivity : 0 ≤ q/4) 2
  norm_num at h
  have hq2 : q^2 ≤ 32 * exp (q/4) := by nlinarith
  calc q^2 * exp (-q/2) ≤ (32 * exp (q/4)) * exp (-q/2) :=
      mul_le_mul_of_nonneg_right hq2 (exp_pos _).le
    _ = _ := by rw [mul_assoc, ←exp_add]; congr 2; ring

theorem HasRootLogRate.of_eventually_add_inv {e g : ℕ → ℝ} (he : HasRootLogRate e)
    {D : ℝ} (hD : 0 ≤ D)
    (hg : ∀ᶠ n : ℕ in atTop, |g n| ≤ |e n| + D / n) : HasRootLogRate g := by
  obtain ⟨C,hC,c,hc,h⟩ := he
  let k := min c 1
  have hk : 0 < k := lt_min hc zero_lt_one
  refine ⟨C+D,by positivity,k,hk,?_⟩
  filter_upwards [h,hg,eventually_gt_atTop (0:ℕ),meshScale_atTop.eventually_ge_atTop 1]
    with n hn hgn hn0 hq
  let q := meshScale n
  have hq0 : 0 ≤ q := (by dsimp [q,meshScale]; positivity)
  have h₁ : exp (-c*q) ≤ exp (-k*q) := by
    apply exp_monotone
    nlinarith [mul_le_mul_of_nonneg_right (min_le_left c (1:ℝ)) hq0]
  have h₂ : (n:ℝ)⁻¹ ≤ exp (-k*q) := by
    rw [← exp_meshScale_sq hn0,← exp_neg]
    apply exp_monotone
    have hq1 : 1 ≤ q := hq
    have hsmall : k ≤ 1 := min_le_right _ _
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1) hq0,
      mul_le_mul_of_nonneg_right hsmall hq0]
  calc |g n| ≤ |e n|+D/n := hgn
    _ ≤ C*exp (-c*q)+D*((n:ℝ)⁻¹) := by rw [div_eq_mul_inv]; exact add_le_add hn le_rfl
    _ ≤ C*exp (-k*q)+D*exp (-k*q) :=
      add_le_add (mul_le_mul_of_nonneg_left h₁ hC.le) (mul_le_mul_of_nonneg_left h₂ hD)
    _ = _ := by dsimp [q]; ring

/-- Finitely many initial values can be included without changing the exponent. -/
theorem HasRootLogRate.all_indices {e : ℕ → ℝ} (he : HasRootLogRate e) :
    ∃ C > 0, ∃ c > 0, ∀ n, |e n| ≤ C * exp (-c * meshScale n) := by
  classical
  obtain ⟨A,hA,c,hc,N,hN⟩ := (show ∃ A > 0, ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N,
      |e n| ≤ A * exp (-c * meshScale n) by
    simpa only [HasRootLogRate,eventually_atTop] using he)
  let S := ∑ j ∈ Finset.range N, |e j| / exp (-c * meshScale j)
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ by positivity
  refine ⟨A+S,by positivity,c,hc,fun n ↦ ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le)
  · have hb : |e n| / exp (-c * meshScale n) ≤ S :=
      Finset.single_le_sum (f := fun j : ℕ ↦ |e j| / exp (-c * meshScale j))
        (fun _ _ ↦ by positivity) (Finset.mem_range.mpr (lt_of_not_ge hn))
    exact (div_le_iff₀ (exp_pos _)).mp (hb.trans (by linarith))

end RiemannMasullo.LogQuadrature
