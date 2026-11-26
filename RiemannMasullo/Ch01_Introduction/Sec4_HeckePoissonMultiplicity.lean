module

public import RiemannMasullo.Ch01_Introduction.Sec4_HeckePoissonMass
import RiemannMasullo.Ch01_Introduction.Sec4_HeckePoissonFormula
import RiemannMasullo.AppB_AnalyticNT.Sec4b_HeckeOuterLogDeriv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Local multiplicity bounds from the translated Hecke Poisson formula

The positive Poisson identity in #7669 bounds the total divisor order in a unit
ordinate window by the arithmetic mass at real part two. The Euler half-plane
estimate then bounds the multiplicity of each site logarithmically in its height.
-/

public noncomputable section

open Complex Function NumberField Set
open scoped NNReal

namespace RiemannMasullo.HeckePoisson

set_option quotPrecheck false
variable {F : Type*} [Field F] [NumberField F]
local notation "CF" => IdeleClassGroup (𝓞 F) F

/-- The pole-cleared arithmetic Poisson mass on the line of real part two grows
at most logarithmically in the ordinate. -/
theorem logDerivativeMass_two_le_log (χ : PontryaginDual CF) :
    ∃ A C : ℝ, 0 < C ∧ ∀ t : ℝ,
      logDerivativeMass χ 2 t ≤ A + C * Real.log (2 + |t|) := by
  classical
  obtain ⟨C,hC,h⟩ := completedHeckeL_poleCleared_logDeriv_bound_right χ
  refine ⟨heckeLogDiscriminantConductor χ / 2 + C*(1+Real.log 2), C, hC, fun t ↦ ?_⟩
  let s : ℂ := (2 : ℂ) + (t : ℂ)*I
  have hs : 2 ≤ s.re := by simp [s]
  have hn : ‖s‖ ≤ 2 + |t| := by
    calc ‖s‖ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ)*I‖ := norm_add_le _ _
         _ = _ := by simp [Real.norm_eq_abs]
  have hlog : Real.log (2 + ‖s‖) ≤ Real.log 2 + Real.log (2 + |t|) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith [abs_nonneg t])
  let P := logDeriv (continuedCompletedHeckeL χ) s + (if χ = 1 then 1/s+1/(s-1) else 0)
  have h1 : P.re ≤ C*(1+Real.log (2+‖s‖)) := (Complex.re_le_norm P).trans (h s hs)
  change heckeLogDiscriminantConductor χ / 2 + P.re ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hlog hC.le]

/-- The total multiplicity in each finite family in a unit ordinate window
is bounded by five halves of the arithmetic mass on the line of real part two. -/
theorem unitWindow_order_le_mass (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : PontryaginDual CF) (hχ : ∀ r, χ (τ r) = 1) (t : ℝ)
    (S : Finset (Site χ)) (hw : ∀ z ∈ S, |t-z.val.im| ≤ 1) :
    ∑ z ∈ S, (multiplicity z : ℝ) ≤ (5/2 : ℝ) * logDerivativeMass χ 2 t := by
  have hs := hasSum_logDerivativeMass τ hτ χ hχ 2 t (by norm_num)
  have hm := hs.summable.sum_le_tsum S (fun z _ ↦ mul_nonneg (Nat.cast_nonneg _) (poissonWeight_pos_of_site (by norm_num : (1:ℝ)<2) t z).le)
  rw [hs.tsum_eq] at hm
  calc ∑ z ∈ S, (multiplicity z : ℝ) ≤ ∑ z ∈ S, (5/2 : ℝ) * ((multiplicity z : ℝ) * poissonWeight 2 t z.val) := by
         apply Finset.sum_le_sum
         intro z hz
         have hstrip := siteStrip z
         let d := 2-z.val.re
         have hd1 : 1 ≤ d := by dsimp [d]; linarith [hstrip.2]
         have hd2 : d ≤ 2 := by dsimp [d]; linarith [hstrip.1]
         have hy := sq_le_sq' (abs_le.1 (hw z hz)).1 (abs_le.1 (hw z hz)).2
         have hden : 0 < d^2+(t-z.val.im)^2 := by positivity
         have hk : (2/5:ℝ) ≤ poissonWeight 2 t z.val := by
           change 2/5 ≤ d/(d^2+(t-z.val.im)^2)
           rw [le_div_iff₀ hden]
           nlinarith [mul_nonneg (sub_nonneg.2 hd1) (sub_nonneg.2 hd2)]
         nlinarith [mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg (multiplicity z) : (0:ℝ) ≤ _)]
       _ ≤ _ := by rw [← Finset.mul_sum]; gcongr

/-- Every individual positive divisor order has logarithmic growth with height. -/
theorem exists_multiplicity_le_log (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : PontryaginDual CF) (hχ : ∀ r, χ (τ r) = 1) :
    ∃ A C : ℝ, 0 < C ∧ ∀ p : Site χ,
      (multiplicity p : ℝ) ≤ A + C * Real.log (2+|p.val.im|) := by
  classical
  obtain ⟨A,C,hC,h⟩ := logDerivativeMass_two_le_log χ
  refine ⟨(5/2)*A, (5/2)*C, by positivity, fun p ↦ ?_⟩
  have hsingle := unitWindow_order_le_mass τ hτ χ hχ p.val.im {p} (by simp)
  simp only [Finset.sum_singleton] at hsingle
  linarith [h p.val.im]

end RiemannMasullo.HeckePoisson
