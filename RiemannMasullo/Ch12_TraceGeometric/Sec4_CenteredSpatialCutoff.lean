module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Dominated convergence for centered spatial cutoffs -/

public noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace RiemannMasullo

/-- A uniformly bounded spatial mask tending pointwise to one gives
vanishing squared error against any integrable weight. -/
theorem tendsto_integral_sq_sub_mask_of_eventually_one
    {ι X : Type*} [MeasurableSpace X] {μ : Measure X}
    {l : Filter ι} [l.IsCountablyGenerated] (ρ : ι → X → ℝ)
    (hm : ∀ᶠ i in l, AEStronglyMeasurable (ρ i) μ)
    (hb : ∀ᶠ i in l, ∀ᵐ x ∂μ, |ρ i x| ≤ 1)
    (ht : ∀ᵐ x ∂μ, ∀ᶠ i in l, ρ i x = 1)
    (g : X → ℝ) (hg : Integrable g μ) :
    Tendsto (fun i ↦ ∫ x, (ρ i x - 1) ^ 2 * g x ∂μ) l (𝓝 0) := by
  let E (i : ι) (x : X) := (ρ i x - 1) ^ 2 * g x
  have hMeas : ∀ᶠ i in l, AEStronglyMeasurable (E i) μ :=
    hm.mono fun _ hi ↦ ((hi.sub aestronglyMeasurable_const).pow 2).mul hg.aestronglyMeasurable
  have hBound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖E i x‖ ≤ 4 * ‖g x‖ := by
    filter_upwards [hb] with i hi
    filter_upwards [hi] with x hx
    change ‖(ρ i x - 1) ^ 2 * g x‖ ≤ 4 * ‖g x‖
    rw [norm_mul, norm_pow]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hnorm : ‖ρ i x - 1‖ ≤ 2 := by
      calc
        ‖ρ i x - 1‖ ≤ ‖ρ i x‖ + ‖(1 : ℝ)‖ := norm_sub_le _ _
        _ ≤ 2 := by simp only [Real.norm_eq_abs, abs_one]; linarith
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans (by norm_num)
  have hDom : Integrable (fun x ↦ 4 * ‖g x‖) μ := hg.norm.const_mul (4 : ℝ)
  have hLim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ E i x) l (𝓝 0) := by
    filter_upwards [ht] with x hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hx] with i hi
    simp only [E, hi, sub_self, zero_pow (Nat.succ_ne_zero 1), zero_mul]
  have h := tendsto_integral_filter_of_dominated_convergence
    (F := E) (f := fun _ ↦ (0 : ℝ)) (fun x ↦ 4 * ‖g x‖) hMeas hBound hDom hLim
  simpa only [E, integral_zero] using h

/-- With `a = -log B`, a physical plateau between `log h` and `log L`
becomes the centered interval between `log (B*h)` and `log (B*L)`. -/
theorem eventually_centeredSpatialMask_eq_one_of_norm_annulus
    {ι : Type*} {l : Filter ι} (B L h : ι → ℝ) (ρ : ι → ℝ → ℝ)
    (hPos : ∀ᶠ i in l, 0 < B i ∧ 0 < L i ∧ 0 < h i)
    (hUpper : Tendsto (fun i ↦ B i * L i) l atTop)
    (hLower : Tendsto (fun i ↦ B i * h i) l (𝓝[>] 0))
    (hPlateau : ∀ᶠ i in l, ∀ x ∈ Icc (Real.log (h i)) (Real.log (L i)), ρ i x = 1)
    (z : ℝ) : ∀ᶠ i in l, ρ i (z + -Real.log (B i)) = 1 := by
  have hHi : ∀ᶠ i in l, z ≤ Real.log (B i * L i) :=
    (Real.tendsto_log_atTop.comp hUpper).eventually (eventually_ge_atTop z)
  have hLo : ∀ᶠ i in l, Real.log (B i * h i) ≤ z :=
    (Real.tendsto_log_nhdsGT_zero.comp hLower).eventually (eventually_le_atBot z)
  filter_upwards [hPos, hPlateau, hHi, hLo] with i hi hp hhi hlo
  rw [Real.log_mul hi.1.ne' hi.2.1.ne'] at hhi
  rw [Real.log_mul hi.1.ne' hi.2.2.ne'] at hlo
  apply hp (z + -Real.log (B i))
  constructor
  · rw [← sub_eq_add_neg, le_sub_iff_add_le]
    exact (add_comm _ _).trans_le hlo
  · rw [← sub_eq_add_neg, sub_le_iff_le_add]
    exact hhi.trans_eq (add_comm _ _)

/-- The upper-only plateau requires only the product `B*L` to diverge. -/
theorem eventually_centeredSpatialMask_eq_one_of_norm_ceiling
    {ι : Type*} {l : Filter ι} (B L : ι → ℝ) (ρ : ι → ℝ → ℝ)
    (hPos : ∀ᶠ i in l, 0 < B i ∧ 0 < L i)
    (hUpper : Tendsto (fun i ↦ B i * L i) l atTop)
    (hPlateau : ∀ᶠ i in l, ∀ x ≤ Real.log (L i), ρ i x = 1)
    (z : ℝ) : ∀ᶠ i in l, ρ i (z + -Real.log (B i)) = 1 := by
  have hHi : ∀ᶠ i in l, z ≤ Real.log (B i * L i) :=
    (Real.tendsto_log_atTop.comp hUpper).eventually (eventually_ge_atTop z)
  filter_upwards [hPos, hPlateau, hHi] with i hi hp hhi
  rw [Real.log_mul hi.1.ne' hi.2.ne'] at hhi
  apply hp (z + -Real.log (B i))
  rw [← sub_eq_add_neg, sub_le_iff_le_add]
  exact hhi.trans_eq (add_comm _ _)

end RiemannMasullo
