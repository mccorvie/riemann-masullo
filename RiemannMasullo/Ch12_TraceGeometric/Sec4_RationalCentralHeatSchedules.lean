module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RationalCentralHeatTrace
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Two heat schedules with distinct finite parts at the rational real place

A smooth cubic near radius one has second log derivative nine. Multiplying it by
a bump in the reciprocal window gives a genuine quotient Bruhat test. Along
one sequence of cutoffs, doubling the heat parameter changes its uncentered
integrated Haar diagonal by a quantity tending to nine.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NumberField.AdeleRing NNReal Topology

namespace RiemannMasullo.AnnularBand

open RatEmptyRealLevelBridge

set_option quotPrecheck false
attribute [local instance] RiemannMasullo.instSIdeleQuotientMeasurableSpaceSec1

local notation "J" => SIdeleQuotient ℚ ∅
local notation "μ" => sLocalQuotientTamagawaMeasure ℚ ∅
local notation "r(" q ")" => (((continuousSIdeleQuotientNorm ℚ ∅ q).val : ℝ))

local instance : T2Space J := by
  have := isClosed_sProjectedDiagonal (F := ℚ) (S := ∅)
  exact inferInstanceAs (T2Space (_ ⧸ _))
local instance : LocallyCompactSpace J := by
  let : LocallyCompactSpace (SAdeleRing ℚ ∅)ˣ := (sIdeleGroup_description ℚ ∅).2.2.1
  exact inferInstanceAs (LocallyCompactSpace (_ ⧸ _))

/-- The multiplier is identically one on an open neighborhood of radius one. -/
private def cutoff : ContDiffBump (1 : ℝ) := ⟨1/8, 1/4, by norm_num, by norm_num⟩

/-- The cubic has distinct nonzero first and second radial derivatives at one. -/
private def weight (r : ℝ) : ℝ := r^3 * cutoff r

private theorem weight_smooth : ContDiff ℝ (∞) weight :=
  (contDiff_id.pow 3).mul cutoff.contDiff

private theorem weight_supported (r : ℝ)
    (hr : r ∉ Icc (centralDilation (1/2)) (centralDilation (-(1/2)))) : weight r = 0 := by
  have hdist : cutoff.rOut ≤ dist r 1 := by
    change 1/4 ≤ dist r 1
    by_contra! h
    rw [Real.dist_eq, abs_lt] at h
    apply hr
    norm_num [centralDilation]
    constructor <;> linarith [h.1, h.2]
  simp [weight, cutoff.zero_of_le_dist hdist]

private theorem weight_jet : weight 1 = 1 ∧ deriv weight 1 + deriv (deriv weight) 1 = 9 := by
  have he : weight =ᶠ[𝓝 (1:ℝ)] fun r : ℝ ↦ r^3 := by
    filter_upwards [cutoff.eventuallyEq_one] with r hr
    change cutoff r = 1 at hr
    simp [weight, hr]
  have hD : deriv (fun r : ℝ ↦ r^3) = fun r ↦ 3*r^2 := by
    ext r
    simp
  have hDD : deriv (fun r : ℝ ↦ 3*r^2) 1 = 6 := by
    convert (((hasDerivAt_id (1:ℝ)).pow 2).const_mul 3).deriv using 1 <;> norm_num
  rw [he.eq_of_nhds, he.deriv_eq, he.deriv.deriv_eq, hD, hDD]
  norm_num

private def floorRadius (n : ℕ) : ℝ := ((n:ℝ)+1)⁻¹
private def outerRadius (n : ℕ) : ℝ := Real.exp ((n:ℝ)+1)
private def heatTime (k : ℝ≥0) (n : ℕ) : ℝ≥0 := k / ((n:ℝ≥0)+1)

private theorem natScale : Tendsto (fun n : ℕ ↦ (n:ℝ)+1) atTop atTop :=
  tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

private theorem heat_time_zero (k : ℝ≥0) : Tendsto (heatTime k) atTop (𝓝 0) := by
  apply NNReal.tendsto_coe.mp
  simpa [heatTime, div_eq_mul_inv] using
    ((tendsto_inv_atTop_zero.comp natScale).const_mul (k : ℝ))

/-- The integral uses the actual two-variable quotient Haar kernel and the Chapter 9 compression. -/
private def diagonal (ψ : BruhatCompactSupport J) (k : ℝ≥0) (n : ℕ) : ℂ :=
  ∫ q : J, quotientLogHaarHeatKernel (heatTime k n)
    (quotientBruhatLevelCompression 1 (floorRadius n) (outerRadius n) ψ) q q ∂μ

/-- For one actual Bruhat test taking value one at the identity, compare the two
log-heat parameters on identical windows. The difference of the uncentered
integrated quotient Haar diagonals tends to nine. -/
theorem exists_quotientBruhatLevel_haarDiagonal_heatSchedules_sub_tendsto_nine :
    ∃ ψ : BruhatCompactSupport J, ψ.val 1 = 1 ∧
      Tendsto (fun n : ℕ ↦
        let T := quotientBruhatLevelCompression 1 ((n : ℝ) + 1)⁻¹ (Real.exp ((n : ℝ) + 1)) ψ
        (∫ q : J, quotientLogHaarHeatKernel (2 / ((n : ℝ≥0) + 1)) T q q ∂μ) -
        (∫ q : J, quotientLogHaarHeatKernel (1 / ((n : ℝ≥0) + 1)) T q q ∂μ))
        atTop (𝓝 (9 : ℂ)) := by
  obtain ⟨ψ, hψ, hlim⟩ := exists_bruhatTest_haarDiagonal_centralFinitePart
    (δ := (1/2:ℝ)) (by norm_num) (by norm_num) weight_smooth weight_supported
  have hf : Tendsto floorRadius atTop (𝓝 0) := tendsto_inv_atTop_zero.comp natScale
  have hL : Tendsto outerRadius atTop atTop := Real.tendsto_exp_atTop.comp natScale
  have hbox : ∀ n : ℕ, 0 ≤ floorRadius n ∧ floorRadius n ≤ outerRadius n := by
    intro n
    have hn : 1 ≤ (n:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hf1 : floorRadius n ≤ 1 := (inv_le_one₀ (by positivity : 0 < (n:ℝ)+1)).mpr hn
    exact ⟨by dsimp [floorRadius]; positivity, hf1.trans (Real.one_le_exp (by positivity))⟩
  have h (k : ℝ≥0) (hk : 0 < k) :
      Tendsto (fun n ↦ diagonal ψ k n - (Real.log (outerRadius n) : ℂ)) atTop
        (𝓝 ((actualCentralTraceFinitePart (1/2) weight + (k:ℝ)*9 : ℝ) : ℂ)) := by
    have hs : ∀ n, (heatTime k n : ℝ) * Real.log (1*outerRadius n) = k := by
      intro n
      simp only [heatTime, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one,
        one_mul, outerRadius, Real.log_exp]
      exact div_mul_cancel₀ _ (by positivity)
    have p := hlim (l := atTop) (B := fun _ : ℕ ↦ (1:ℝ)) (L := outerRadius)
      (h := floorRadius) (τ := heatTime k) (κ := (k:ℝ)) (fun _ ↦ zero_lt_one)
      (fun n ↦ Real.exp_pos _) (.of_forall hbox) (by simpa using hL)
      (by simpa using hf) (heat_time_zero k) (by simp only [hs]; exact tendsto_const_nhds)
      (.of_forall fun n ↦ div_pos hk (by positivity))
    simpa only [diagonal, one_mul, weight_jet.1, weight_jet.2] using p
  refine ⟨ψ, ?_, ?_⟩
  · simpa only [map_one, Units.val_one, NNReal.coe_one, weight_jet.1, Complex.ofReal_one] using hψ 1
  · change Tendsto (fun n ↦ diagonal ψ 2 n - diagonal ψ 1 n) atTop (𝓝 (9 : ℂ))
    have p := (h 2 (by norm_num)).sub (h 1 (by norm_num))
    convert p using 1
    · ext n
      ring
    · push_cast
      ring_nf

end RiemannMasullo.AnnularBand
