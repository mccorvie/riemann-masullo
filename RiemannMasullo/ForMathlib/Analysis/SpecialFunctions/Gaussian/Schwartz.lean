module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Schwartz Gaussians and their Mellin transforms -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RiemannMasullo

open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem gaussian_weight_bound (b : ℝ) (hb : 0<b) (m : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → (1+t)^m * Real.exp (-b*t^2) ≤ C := by
  let D := (m.factorial:ℝ)/b^m
  refine ⟨2^m*max 1 D, fun t ht ↦ ?_⟩
  have he : Real.exp (-b*t^2) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le) (sq_nonneg _))
  by_cases h : t ≤ 1
  · calc
      _ ≤ (2:ℝ)^m * 1 := by gcongr; linarith
      _ ≤ _ := by gcongr; exact le_max_left ..
  · have ht' : 1 ≤ t := le_of_not_ge h
    have hpol : t^(2*m) * Real.exp (-b*t^2) ≤ D := by
      have hy := Real.pow_div_factorial_le_exp _ (mul_nonneg hb.le (sq_nonneg t)) m
      rw [mul_pow, ← pow_mul] at hy
      rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      dsimp [D]
      rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hb m)]
      simpa only [mul_comm] using (div_le_iff₀ (by positivity : (0:ℝ)<m.factorial)).mp hy
    calc
      _ ≤ (2*t^2)^m * Real.exp (-b*t^2) := by gcongr; nlinarith [sq_nonneg (t-1)]
      _ = 2^m * (t^(2*m)* Real.exp (-b*t^2)) := by rw [mul_pow, pow_mul, mul_assoc]
      _ ≤ _ := by gcongr; exact hpol.trans (le_max_right ..)

/-- A Gaussian on a real inner product space is Schwartz. The composition
estimate bounds each derivative by a polynomial times the same Gaussian. -/
theorem exists_gaussian_schwartz (b : ℝ) (hb : 0<b) :
    ∃ g : SchwartzMap E ℂ, ∀ x, g x = Real.exp (-b*‖x‖^2) := by
  let p (x : E) := -b*‖x‖^2
  have hp : p.HasTemperateGrowth := by dsimp [p]; fun_prop
  let G : SchwartzMap E ℝ :=
    { toFun := Real.exp ∘ p
      smooth' := Real.contDiff_exp.comp hp.1
      decay' := by
        intro k n
        obtain ⟨j,C,hC,hj⟩ := hp.norm_iteratedFDeriv_le_uniform n
        obtain ⟨M,hM⟩ := gaussian_weight_bound b hb (k+j*n)
        refine ⟨n.factorial*(C+1)^n*M,fun x ↦ ?_⟩
        let X := 1+‖x‖
        have hX : 1 ≤ X := by simp [X]
        have hD : 1 ≤ (C+1)*X^j := one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hX)
        have H := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (n := n) (N := ∞) Real.contDiff_exp hp.1
          (by simp) x (C := Real.exp (p x)) (D := (C+1)*X^j) (fun i _ ↦ by
            rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
              Real.norm_of_nonneg (Real.exp_pos _).le]) (fun i hi hin ↦ (hj i hin x).trans
            ((by gcongr; linarith : C*X^j ≤ (C+1)*X^j).trans (le_self_pow₀ hD (by omega))))
        calc
          _ ≤ X^k * (n.factorial*Real.exp (p x)*((C+1)*X^j)^n) := by gcongr; simp [X]
          _ = (n.factorial*(C+1)^n) * (X^(k+j*n)*Real.exp (p x)) := by rw [mul_pow,pow_add,pow_mul]; ring
          _ ≤ _ := by gcongr; exact hM ‖x‖ (norm_nonneg x) }
  exact ⟨SchwartzMap.postcompCLM Complex.ofRealCLM G,fun _ ↦ rfl⟩

/-- The Mellin transform of a monomial times a Gaussian is an ordinary gamma factor. -/
theorem mellin_weightedGaussian (b : ℝ) (hb : 0<b) (n : ℕ) (z : ℂ)
    (hz : 0 < z.re) :
    mellin (fun t : ℝ ↦ (t:ℂ)^n * (Real.exp (-b * t^2):ℂ)) z =
      (1/2:ℂ) * (b:ℂ)^(-((z+n)/2)) * Complex.Gamma ((z+n)/2) := by
  let G (x : ℝ) : ℂ := Real.exp (-b*x)
  have hG (u : ℂ) (hu : 0 < u.re) : mellin G u = (b:ℂ)^(-u)*Complex.Gamma u := by
    change (∫ t : ℝ in Ioi 0, (t:ℂ)^(u-1) * (Real.exp (-b*t):ℂ)) = _
    have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hu hb
    simpa only [← Complex.ofReal_exp,← Complex.ofReal_mul,← Complex.ofReal_neg, one_div,
      Complex.inv_cpow_ofReal_nonneg hb.le,Complex.cpow_neg,neg_mul] using h
  have hn : (fun t : ℝ ↦ (t:ℂ)^n * (Real.exp (-b*t^2):ℂ)) =
      (fun t : ℝ ↦ (t:ℂ)^(n:ℂ) • G (t^(2:ℝ))) := by
    funext t
    simp [G,smul_eq_mul]
  rw [hn,mellin_cpow_smul,mellin_comp_rpow,hG]
  · simp [Complex.real_smul]
    ring
  · simp only [Complex.ofReal_ofNat,Complex.div_ofNat_re,Complex.add_re,Complex.natCast_re]
    positivity

end RiemannMasullo
