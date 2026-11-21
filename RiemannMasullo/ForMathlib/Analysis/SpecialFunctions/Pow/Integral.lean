module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! # Layer-cake formula for powers of extended nonnegative functions -/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RiemannMasullo

/-- The layer-cake formula for a positive real power of an extended nonnegative function. -/
theorem lintegral_ennreal_rpow_eq_lintegral_meas_lt_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, f x ^ p ∂μ) =
      ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ), μ {x | ENNReal.ofReal t < f x} *
        ENNReal.ofReal (t ^ (p - 1)) := by
  let trunc (n : ℕ) (x : α) := f x ⊓ (n : ℝ≥0∞)
  let tail (g : α → ℝ≥0∞) (t : ℝ) :=
    μ {x | ENNReal.ofReal t < g x} * ENNReal.ofReal (t ^ (p - 1))
  have hmono : Monotone trunc := fun n m hnm x ↦ inf_le_inf_left _ (Nat.cast_le.mpr hnm)
  have hmeas (n : ℕ) : AEMeasurable (trunc n) μ := hf.inf aemeasurable_const
  have htrunc (n : ℕ) (x : α) : ENNReal.ofReal (trunc n x).toReal = trunc n x :=
    ENNReal.ofReal_toReal ((inf_le_right : trunc n x ≤ (n : ℝ≥0∞)).trans_lt
      (ENNReal.natCast_lt_top n)).ne
  have hformula (n : ℕ) : (∫⁻ x, trunc n x ^ p ∂μ) =
      ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ), tail (trunc n) t := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal ((trunc n x).toReal ^ p) ∂μ := by
        apply lintegral_congr
        intro x
        rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le, htrunc]
      _ = ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ), μ {x | t < (trunc n x).toReal} *
          ENNReal.ofReal (t ^ (p - 1)) :=
        lintegral_rpow_eq_lintegral_meas_lt_mul μ
          (Filter.Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg) (hmeas n).ennreal_toReal hp
      _ = _ := by
        refine congrArg (ENNReal.ofReal p * ·) (lintegral_congr_ae ?_)
        filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
        dsimp only [tail]
        congr 2
        ext x
        change (t < (trunc n x).toReal ↔ ENNReal.ofReal t < trunc n x)
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt ht)).symm.trans
          (by rw [htrunc])
  have hs (x : α) : (⨆ n, trunc n x) = f x := by
    simp only [trunc, ← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have htail (n : ℕ) : Measurable (tail (trunc n)) := by
    have hanti : Antitone (fun t : ℝ ↦ μ {x | ENNReal.ofReal t < trunc n x}) :=
      fun _ _ hab ↦ measure_mono fun _ hx ↦ (ENNReal.ofReal_le_ofReal hab).trans_lt hx
    exact hanti.measurable.mul (by fun_prop)
  have htail_mono {g₁ g₂ : α → ℝ≥0∞} (h : g₁ ≤ g₂) (t : ℝ) : tail g₁ t ≤ tail g₂ t := by
    have hs : {x | ENNReal.ofReal t < g₁ x} ⊆ {x | ENNReal.ofReal t < g₂ x} :=
      fun x hx ↦ (show ENNReal.ofReal t < g₁ x from hx).trans_le (h x)
    dsimp only [tail]
    gcongr
  have htailMono : Monotone (fun n ↦ tail (trunc n)) := fun _ _ h t ↦ htail_mono (hmono h) t
  have htailSup (t : ℝ) : (⨆ n, tail (trunc n) t) = tail f t := by
    refine le_antisymm (iSup_le fun n ↦ htail_mono (fun x ↦ inf_le_left) t) ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.ofReal_ne_top (r := t))
    have heq : tail (trunc n) t = tail f t := by
      simp only [tail, trunc, lt_inf_iff, hn, and_true]
    exact heq ▸ le_iSup (fun n ↦ tail (trunc n) t) n
  change (∫⁻ x, f x ^ p ∂μ) = ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ), tail f t
  simp_rw [← hs, ENNReal.iSup_rpow_of_pos hp]
  rw [lintegral_iSup' (fun n ↦ (hmeas n).pow_const p) (Filter.Eventually.of_forall fun x _ _ hnm ↦
    ENNReal.rpow_le_rpow (hmono hnm x) hp.le)]
  simp_rw [hformula, ← ENNReal.mul_iSup]
  rw [← lintegral_iSup htail htailMono]
  exact congrArg (ENNReal.ofReal p * ·) (lintegral_congr htailSup)

end RiemannMasullo
