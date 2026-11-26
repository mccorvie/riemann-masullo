module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.QuarticFiveAbel
public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.CriticalMellinTail
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! # Effective critical-line frequency tails for the quartic Dirichlet character modulo five

Only the bounded diameter of its periodic partial sums and its ordinary Abel continuation
are used. The measure is the Cauchy probability measure with scale `3/2`. -/

@[expose] public noncomputable section

open MeasureTheory Complex
open scoped ENNReal

namespace RiemannMasullo.QuarticFive
open CriticalMellinTail

private theorem line_measurable (χ : DirichletCharacter ℂ 5) (hχ : χ 2 = I) :
    Measurable (fun t : ℝ ↦ χ.LFunction (line t)) :=
  ((_root_.DirichletCharacter.differentiable_LFunction (ne_one χ hχ)).continuous.comp
    (by unfold line; fun_prop)).measurable

/-- Whole high-frequency energy for the actual ordinary Dirichlet function. -/
theorem critical_tail_energy (χ : DirichletCharacter ℂ 5) (hχ : χ 2 = I) {T : ℝ}
    (hT : 1 ≤ T) :
    IntegrableOn (fun t ↦ CayleyCauchy.density (3/2) t * ‖χ.LFunction (line t)‖^2) (far T) ∧
    ∫ t in far T, CayleyCauchy.density (3/2) t * ‖χ.LFunction (line t)‖^2 ≤ 20/Real.sqrt T := by
  have hpos := zero_lt_one.trans_le hT
  have hroot : 1 ≤ Real.sqrt T := by simpa using Real.sqrt_le_sqrt hT
  obtain ⟨hi, hb⟩ := tail_energy (D := Real.sqrt 2) (X := Real.sqrt T) (line_measurable χ hχ)
    (fun k ↦ χ.norm_le_one (k : ZMod 5)) (norm_sub_partialSums_le χ hχ)
    (fun t ↦ LFunction_abel χ hχ (by simp [line_re])) hpos hroot
  refine ⟨hi, hb.trans ?_⟩
  have hx : Real.sqrt T ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hX : Real.sqrt T/T = 1/Real.sqrt T := (div_eq_div_iff hpos.ne' hx).mpr
    (by rw [← sq, Real.sq_sqrt hpos.le, one_mul])
  have hπ : 24/Real.pi ≤ 8 := (div_le_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), hX]
  calc
    _ ≤ 8*(1/Real.sqrt T) + 6*(2/Real.sqrt T) := by gcongr
    _ = _ := by ring

/-- The high-frequency `L²` norm is at most `√20 T^(-1/4)` for every `T ≥ 1`. -/
theorem critical_tail_eLpNorm (χ : DirichletCharacter ℂ 5) (hχ : χ 2 = I) {T : ℝ}
    (hT : 1 ≤ T) :
    MemLp ((far T).indicator (fun t ↦ χ.LFunction (line t))) 2 criticalMeasure ∧
    eLpNorm ((far T).indicator (fun t ↦ χ.LFunction (line t))) 2 criticalMeasure ≤
      ENNReal.ofReal (Real.sqrt 20 * T^(-(1/4 : ℝ))) := by
  obtain ⟨hi, he⟩ := critical_tail_energy χ hχ hT
  obtain ⟨hm,hb⟩ := indicator_eLpNorm_le_of_energy (measurableSet_far T) (line_measurable χ hχ) hi he
  refine ⟨hm, hb.trans_eq ?_⟩
  congr 1
  rw [Real.sqrt_div (by norm_num), Real.sqrt_eq_rpow (Real.sqrt T), Real.sqrt_eq_rpow T,
    ← Real.rpow_mul (zero_le_one.trans hT), Real.rpow_neg (zero_le_one.trans hT)]
  norm_num [div_eq_mul_inv]

/-- The literal character has `χ(2)=i` without any zero-location or numerical input. -/
theorem character_critical_tail_eLpNorm {T : ℝ} (hT : 1 ≤ T) :
    eLpNorm ((far T).indicator (fun t ↦ character.LFunction (line t))) 2 criticalMeasure ≤
      ENNReal.ofReal (Real.sqrt 20 * T^(-(1/4 : ℝ))) :=
  (critical_tail_eLpNorm character character_two hT).2

end RiemannMasullo.QuarticFive
