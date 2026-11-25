module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Tactic

/-! # Finite power moments from geometric tails at quadratic thresholds -/

@[expose] public noncomputable section
open MeasureTheory Filter Function Set
open scoped ENNReal Topology

namespace RiemannMasullo.LogQuadrature
/-- On a finite measure space, geometric decay at quadratic thresholds gives integrability
of every natural power of the absolute value. -/
theorem integrable_abs_pow_of_geometric_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) {A K q : ℝ} (hA : 0 < A) (hK : 0 ≤ K)
    (hq : 0 < q) (hq1 : q < 1)
    (h : ∀ j : ℕ, μ {x | A*((j:ℝ)+1)^2 < |f x|} ≤ ENNReal.ofReal (K*q^j)) (p : ℕ) :
    Integrable (fun x ↦ |f x|^p) μ := by
  let a (n : ℕ) := A*((n:ℝ)+1)^2
  let s (n : ℕ) := (fun x ↦ |f x|) ⁻¹' Ioc (a n) (a (n+1))
  let v (x : Ω) := |f x|^p
  have hfa : Measurable (fun x ↦ |f x|) := continuous_abs.measurable.comp hf
  have hv : Measurable v := hfa.pow_const _
  have ha : Monotone a := by intro i j hij; dsimp [a]; gcongr
  have htop : ¬ BddAbove (range a) := by
    rintro ⟨b,hb⟩
    obtain ⟨n,hn⟩ := exists_nat_gt (b/A)
    have hl := (div_lt_iff₀ hA).mp hn
    have ht := hb (mem_range_self n)
    have hsq : (n:ℝ) ≤ ((n:ℝ)+1)^2 := by nlinarith [sq_nonneg (n:ℝ), Nat.cast_nonneg (α:=ℝ) n]
    dsimp [a] at ht
    nlinarith [mul_le_mul_of_nonneg_left hsq hA.le]
  have hall : (⋃ n, s n) = {x | A < |f x|} := by
    dsimp only [s]
    rw [← preimage_iUnion]
    have hU : (⋃ i, Ioc (a i) (a (i+1))) = Ioi (a 0) :=
      iUnion_Ioc_map_succ_eq_Ioi (fun n ↦ ha (bot_le (a:=n))) htop
    rw [hU]
    simp [a, preimage, Ioi]
  have hs (n) : MeasurableSet (s n) := hfa measurableSet_Ioc
  have bound n x (hx : x ∈ s n) : ‖v x‖ ≤ a (n+1)^p := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) p)]
    exact pow_le_pow_left₀ (abs_nonneg _) hx.2 p
  have hi (n) : IntegrableOn v (s n) μ :=
    Integrable.of_bound hv.aestronglyMeasurable _ ((ae_restrict_mem (hs n)).mono fun x ↦ bound n x)
  have hmass (n) : μ.real (s n) ≤ K*q^n := by
    have hsub : s n ⊆ {x | A*((n:ℝ)+1)^2 < |f x|} := fun _ hx ↦ hx.1
    have hle : μ (s n) ≤ ENNReal.ofReal (K*q^n) := (measure_mono hsub).trans (h n)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans_eq (ENNReal.toReal_ofReal (by positivity))
  let b (n : ℕ) := ((n:ℝ)^(2*p))*q^n
  have hb : Summable b := summable_pow_mul_geometric_of_norm_lt_one _ (by simpa [abs_of_pos hq] using hq1)
  have hsum : Summable (fun n : ℕ ↦ a (n+1)^p * (K*q^n)) := by
    have hh := ((summable_nat_add_iff 2).mpr hb).mul_left ((A^p*K)/q^2)
    apply hh.congr
    intro n
    dsimp [a,b]
    push_cast
    rw [pow_add q, mul_pow, ← pow_mul]
    field_simp
    ring
  have hiU : IntegrableOn v (⋃ n, s n) μ := by
    apply integrableOn_iUnion_of_summable_integral_norm hi
    apply hsum.of_nonneg_of_le (fun _ ↦ integral_nonneg (fun _ ↦ norm_nonneg _))
    intro n
    calc
      _ ≤ a (n+1)^p * μ.real (s n) := by
        have e := norm_setIntegral_le_of_norm_le_const (f:=fun x ↦ ‖v x‖) (measure_lt_top μ (s n))
           (C:=a (n+1)^p) (fun x hx ↦ by simpa using bound n x hx)
        exact (le_abs_self _).trans e
      _ ≤ a (n+1)^p * (K*q^n) := mul_le_mul_of_nonneg_left (hmass n) (by dsimp [a]; positivity)
  rw [hall] at hiU
  have hlow : IntegrableOn v {x | |f x| ≤ A} μ := by
    apply Integrable.of_bound hv.aestronglyMeasurable (A^p)
    filter_upwards [ae_restrict_mem (measurableSet_le hfa measurable_const)] with x hx
    simpa only [v,Real.norm_eq_abs,abs_pow,abs_abs] using pow_le_pow_left₀ (abs_nonneg (f x)) hx p
  have hcov : {x | |f x| ≤ A} ∪ {x | A < |f x|} = univ := by ext x; simp [le_or_gt]
  simpa only [hcov,integrableOn_univ] using hlow.union hiU
end RiemannMasullo.LogQuadrature
