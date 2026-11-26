module

public import RiemannMasullo.ForMathlib.Analysis.Complex.CaratheodoryLogCoefficients
public import RiemannMasullo.Ch01_Introduction.Sec4_HeckePrimeLaguerre
import RiemannMasullo.AppB_AnalyticNT.Sec4b
import Mathlib.Tactic

/-! # Finite-height upper bounds for ordinary Hecke logarithmic moments -/

@[expose] public noncomputable section

open Complex Filter Function Metric NumberField Set
open scoped NNReal Topology

namespace RiemannMasullo.HeckeLaguerre
open HeckeHalfPlaneJensen HalfPlaneJensen DiskLogCoefficient SignedFrequency

variable {F : Type*} [Field F] [NumberField F]
local notation "CF" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual CF
local notation "Hp" => (Complex.re ⁻¹' Ioi (1 : ℝ))

/-- A lower bound on the absolute height of every right-hand positive site yields an explicit
zero-free disk for the genuine ordinary function in the Cayley coordinate. -/
theorem clearedDisk_ne_zero_of_verified_height
    (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {T : ℝ} (hT : 0 < T)
    (hheight : ∀ w : RightSite χ, T ≤ |w.val.im|) {z : ℂ}
    (hz : ‖z‖ < Real.exp (-(3/(2*T^2)))) : clearedDisk χ L z ≠ 0 := by
  have hK : 0 < 3/(2*T^2) := by positivity
  have hz1 := hz.trans ((Real.exp_lt_one_iff).mpr (neg_lt_zero.mpr hK))
  intro hz0
  let w : RightSite χ := ⟨toHalf z, (clearedDisk_eq_zero_iff τ hτ χ hχ L hL he hz1).mp hz0,
    toHalf_re hz1⟩
  have hstrip := (HeckePoisson.siteStrip (χ := χ) ⟨w.val,w.property.1⟩).2
  have hback : toDisk w.val = z := toDisk_toHalf (half_den hz1)
  have hs2 : w.val ≠ 2 := by
    intro h
    rw [h] at hstrip
    norm_num at hstrip
  have hpos : 0 < ‖z‖ := by
    rw [← hback, toDisk]
    exact norm_pos_iff.mpr (div_ne_zero (sub_ne_zero.mpr hs2) (disk_den w.property.2))
  have hG : greenKernel w.val = -Real.log ‖z‖ := by
    rw [← weight_one_eq_green w.property.2 hs2, weight, hback, one_div,
      max_eq_right (Real.log_pos ((one_lt_inv₀ hpos).mpr hz1)).le, Real.log_inv]
  have ht2 : T^2 ≤ w.val.im^2 := by
    simpa only [sq_abs] using sq_le_sq' (by linarith [hheight w] : -|w.val.im| ≤ T) (hheight w)
  have hGle := (greenKernel_bounds w.property.2.le hstrip).2
  have hden : 0 < 1+w.val.im^2 := by positivity
  have hfinal : greenKernel w.val ≤ 3/(2*T^2) := calc
    _ ≤ 3*(w.val.re-1/2)/(1+w.val.im^2) := hGle
    _ ≤ (3/2)/(1+w.val.im^2) := div_le_div_of_nonneg_right (by linarith) hden.le
    _ ≤ (3/2)/T^2 := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    _ = 3/(2*T^2) := by ring
  rw [hG] at hfinal
  have hzlog := (Real.log_lt_iff_lt_exp hpos).mpr hz
  linarith

/-- The actual ordinary logarithmic moment, centered at one, on a verified finite-height range.
The two size inputs bound the disk function after multiplication by `1-z` and its center. -/
theorem abs_actualMoment_sub_one_of_verified_height
    (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {T B b : ℝ} (hT : 0 < T)
    (hheight : ∀ w : RightSite χ, T ≤ |w.val.im|)
    (hsize : ∀ z ∈ ball (0 : ℂ) 1, ‖(1-z)*clearedDisk χ L z‖ ≤ B)
    (hb : 0 < b) (hcenter : b ≤ ‖clearedDisk χ L 0‖) {n : ℕ} (hn : 0 < n) :
    |actualMoment χ L n-1| ≤ 2*n*Real.log (B/b)*Real.exp (3*n/(2*T^2)) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let R := Real.exp (-(3/(2*T^2)))
  have hR : 0 < R := Real.exp_pos _
  have hR1 : R ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  have hsub : ball (0 : ℂ) R ⊆ ball 0 1 := ball_subset_ball hR1
  have hu := abs_logDeriv_coeff_re_sub_one_le hR hR1 ((clearedDisk_analytic τ hτ χ hχ L hL he).mono hsub)
    (fun z hz ↦ clearedDisk_ne_zero_of_verified_height τ hτ χ hχ L hL he hT hheight (mem_ball_zero_iff.mp hz))
    (fun z hz ↦ hsize z (hsub hz)) k
  have hnorm := hb.trans_le hcenter
  have hB : 0 < B := hnorm.trans_le (by simpa using hsize 0 (mem_ball_self (by norm_num : (0:ℝ)<1)))
  have hmono : Real.log (B / ‖clearedDisk χ L 0‖) ≤ Real.log (B/b) :=
    Real.log_le_log (div_pos hB hnorm) (div_le_div_of_nonneg_left hB.le hb hcenter)
  have hpow : R^(k+1) = (Real.exp (3*((k+1 : ℕ) : ℝ)/(2*T^2)))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpow] at hu
  change |(coeff (logDeriv (clearedDisk χ L)) k).re - 1| ≤ _
  calc
    _ ≤ (2*((k+1 : ℕ) : ℝ)*Real.log (B/‖clearedDisk χ L 0‖)) *
          Real.exp (3*((k+1 : ℕ) : ℝ)/(2*T^2)) := by
      apply (div_le_iff₀ (Real.exp_pos _)).mp
      simpa [div_eq_mul_inv] using hu
    _ ≤ _ := by gcongr

private theorem log_quartic_ratio_lt : Real.log (24/5) < 8/5 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ) < 24/5)).mpr
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤8/5) 5)
  norm_num [Finset.sum_range_succ, Nat.factorial]

private theorem exp_sixth_lt : Real.exp (1/6) < 6/5 := by
  convert Real.exp_bound_div_one_sub_of_interval' (by norm_num : (0:ℝ)<1/6)
    (by norm_num : (1:ℝ)/6<1) using 1; norm_num

/-- The conductor-five constants give this sharper finite raw bound through index
44,444,444,444,444. The ordinate input is two-sided. -/
theorem abs_fin25_sub_one_lt_of_quartic_data
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ) (hτ : RightInverse τ (ideleClassNorm ℚ))
    (χ : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) (hχ : ∀ u, χ (τ u) = 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (he : ∀ s : Hp, L s = finiteHeckeL χ s)
    (hheight : ∀ w : RightSite χ, 20000000 ≤ |w.val.im|)
    (hsize : ∀ z ∈ ball (0 : ℂ) 1, ‖(1-z)*clearedDisk χ L z‖ ≤ 9/2)
    (hcenter : 15/16 ≤ ‖clearedDisk χ L 0‖)
    {n : ℕ} (hn : 0 < n) (hnT : n ≤ 44444444444444) :
    |actualMoment χ L n - 1| < (96/25)*n ∧ |finiteMoment χ n (25^n)-1| < (146/25)*n := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hu := abs_actualMoment_sub_one_of_verified_height τ hτ χ hχ L hL he
    (by norm_num : (0:ℝ) < 20000000) hheight hsize (by norm_num : (0:ℝ) < 15/16) hcenter hn
  rw [show (9/2)/(15/16 : ℝ) = 24/5 by norm_num] at hu
  have hn' : (n:ℝ) ≤ 44444444444444 := by exact_mod_cast hnT
  have he' : Real.exp (3*(n:ℝ)/(2*(20000000:ℝ)^2)) < 6/5 :=
    (Real.exp_le_exp.mpr (by linarith : 3*(n:ℝ)/(2*(20000000:ℝ)^2) ≤ 1/6)).trans_lt exp_sixth_lt
  have hm : |actualMoment χ L n-1| < (96/25)*n := by
    refine hu.trans_lt ?_
    calc
      2*(n:ℝ)*Real.log (24/5)*Real.exp (3*(n:ℝ)/(2*(20000000:ℝ)^2)) < (2*(n:ℝ)*(8/5)) * (6/5) :=
        mul_lt_mul_of_pos_of_nonneg' (mul_lt_mul_of_pos_left log_quartic_ratio_lt (by positivity))
          he'.le (Real.exp_pos _) (by positivity)
      _ = _ := by ring
  refine ⟨hm, ?_⟩
  have htail := abs_actualMoment_sub_fin25 χ L hL he hn
  rw [Module.finrank_self] at htail
  have ht := abs_add_le (finiteMoment χ n (25^n)-actualMoment χ L n) (actualMoment χ L n-1)
  rw [sub_add_sub_cancel] at ht
  rw [abs_sub_comm (actualMoment χ L n)] at htail
  norm_num at htail
  linarith

end RiemannMasullo.HeckeLaguerre