module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b
public import RiemannMasullo.ForMathlib.Analysis.FiniteHeightPacking
import Mathlib.Tactic

public section

open IsDedekindDomain NumberField Set Metric
open scoped NumberField.AdeleRing Topology

namespace RiemannMasullo

/-- Every sufficiently high signed unit window contains a horizontal segment with a
uniform squared-logarithmic derivative bound and inverse-logarithmic separation from the
ordinates of every zero in the controlling disk. The same ordinate works for all real parts. -/
theorem finiteHeckeL_continuation_exists_horizontal_logDeriv_le_log_sq
    {F : Type*} [Field F] [NumberField F] (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ z : {z : ℂ // 1 < z.re}, L z = finiteHeckeL χ z) :
    ∃ C > (0 : ℝ), ∃ J > (0 : ℝ), ∀ j : ℝ, J ≤ |j| →
      ∃ t ∈ Ioo j (j + 1),
        (∀ ρ ∈ closedBall (⟨2, j + 1 / 2⟩ : ℂ) (5 / 2), L ρ = 0 →
          1 / (C * Real.log (2 + |j|)) ≤ |t - ρ.im|) ∧
        ∀ σ ∈ Icc (1 / 2 : ℝ) 2,
          AnalyticAt ℂ (logDeriv L) (⟨σ, t⟩ : ℂ) ∧ L ⟨σ, t⟩ ≠ 0 ∧
          ‖logDeriv L ⟨σ, t⟩‖ ≤ C * Real.log (2 + |j|) ^ 2 := by
  classical
  obtain ⟨B, hB, J, _, hwindow⟩ :=
    finiteHeckeL_continuation_highHeight_unitWindow_logDeriv χ L hL hSeries
  let A := 2 * (B + 1)
  have hA : 0 < A := by dsimp [A]; positivity
  let C := max A (B + A * B)
  refine ⟨C, hA.trans_le (le_max_left _ _), max J (Real.exp 1),
    (Real.exp_pos _).trans_le (le_max_right _ _), fun j hj ↦ ?_⟩
  obtain ⟨_, _, S, hS, horder, hmass, _, hsegment⟩ :=
    hwindow j ((le_max_left _ _).trans hj)
  let u := Real.log (2 + |j|)
  have hu : 1 ≤ u := by
    have he : Real.exp 1 ≤ 2 + |j| := (le_max_right _ _).trans (hj.trans (by linarith))
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) he
  have hu₀ : 0 < u := zero_lt_one.trans_le hu
  have hcard : (S.card : ℝ) ≤ ∑ ρ ∈ S, (analyticOrderNatAt L ρ : ℝ) := by
    calc
      _ = ∑ _ρ ∈ S, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun ρ hρ ↦ by exact_mod_cast (horder ρ hρ).1
  have hsize : (S.card : ℝ) ≤ B * u := hcard.trans hmass
  have hden : 2 * ((S.card : ℝ) + 1) ≤ A * u := by dsimp [A]; linarith
  have hAu : 0 < A * u := mul_pos hA hu₀
  obtain ⟨t, ht, hmesh⟩ := S.exists_mem_Ioo_dist_ge_half_mesh Complex.im j
  have hsep (ρ : ℂ) (hρ : ρ ∈ S) : 1 / (A * u) ≤ |t - ρ.im| :=
    (one_div_le_one_div_of_le (by positivity) hden).trans (hmesh ρ hρ)
  have hdist (ρ : ℂ) (hρ : ρ ∈ S) : 0 < |t - ρ.im| :=
    (one_div_pos.mpr hAu).trans_le (hsep ρ hρ)
  refine ⟨t, ht, ?_, fun σ hσ ↦ ?_⟩
  · intro ρ hmem hzero
    exact (one_div_le_one_div_of_le hAu
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hu₀.le)).trans
      (hsep ρ ((hS ρ).mpr ⟨hmem, hzero⟩))
  obtain ⟨hreg, hne, hpoint⟩ := hsegment σ hσ t ⟨ht.1.le, ht.2.le⟩
    (fun ρ hρ ↦ sub_ne_zero.mp (abs_pos.mp (hdist ρ hρ)))
  refine ⟨hreg, hne, hpoint.trans ?_⟩
  have hterm (ρ : ℂ) (hρ : ρ ∈ S) :
      (analyticOrderNatAt L ρ : ℝ) / |t - ρ.im| ≤ (analyticOrderNatAt L ρ : ℝ) * (A * u) := by
    have hinv : 1 / |t - ρ.im| ≤ A * u := by
      apply (div_le_iff₀ (hdist ρ hρ)).2
      simpa only [mul_comm (A * u)] using (div_le_iff₀ hAu).1 (hsep ρ hρ)
    simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hinv
      (Nat.cast_nonneg (α := ℝ) (analyticOrderNatAt L ρ))
  have hu₂ : u ≤ u ^ 2 := by nlinarith [mul_nonneg hu₀.le (sub_nonneg.mpr hu)]
  calc
    B * u + ∑ ρ ∈ S, (analyticOrderNatAt L ρ : ℝ) / |t - ρ.im|
        ≤ B * u + ∑ ρ ∈ S, (analyticOrderNatAt L ρ : ℝ) * (A * u) :=
          add_le_add_right (Finset.sum_le_sum hterm) _
    _ = B * u + (∑ ρ ∈ S, (analyticOrderNatAt L ρ : ℝ)) * (A * u) := by rw [Finset.sum_mul]
    _ ≤ B * u + (B * u) * (A * u) := by gcongr
    _ ≤ B * u ^ 2 + (B * u) * (A * u) := by gcongr
    _ = (B + A * B) * u ^ 2 := by ring
    _ ≤ C * u ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg u)

end RiemannMasullo
