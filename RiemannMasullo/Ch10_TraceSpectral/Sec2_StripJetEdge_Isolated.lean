module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
public import RiemannMasullo.ForMathlib.Analysis.Fourier.WeightedLaplaceAsymptotics
import RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch09_HardySobolev.Sec2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Boundary growth of strip jets

At Sobolev order two the squared jet norm from Proposition 10.2.2.2, pp. 446–447, is a
fixed Haar measure factor times the scalar integral below (see the norm formula in `Sec2`).
For every jet order, the squared norm has power growth, logarithmic growth, or a finite
endpoint limit according to the Sobolev order.
-/

public section

open Real Set MeasureTheory Filter
open scoped Topology

namespace RiemannMasullo.Isolated

/-- Paper: Proposition 10.2.2.2, pp. 446–447. For an order-one jet at Sobolev order two,
the difference between the edge pole and the radial norm integral belongs to `[0, π]`. -/
theorem spectralStripJet_orderOne_integral_edge_bounds {α b : ℝ} (hb : |b| < α) :
    let J := ∫ x : ℝ, Real.exp (2 * b * x - 2 * α * |x|) * x ^ 2 / (1 + x ^ 2)
    α / (α ^ 2 - b ^ 2) - π ≤ J ∧ J ≤ α / (α ^ 2 - b ^ 2) := by
  let w (x : ℝ) := Real.exp (2 * b * x - 2 * α * |x|)
  have hLeft : 0 < 2 * (b + α) := by linarith [(abs_lt.mp hb).1]
  have hRight : 2 * (b - α) < 0 := by linarith [(abs_lt.mp hb).2]
  have hwLeft : EqOn w (fun x ↦ Real.exp (2 * (b + α) * x)) (Iic 0) := by
    intro x hx
    dsimp [w]
    rw [abs_of_nonpos hx]
    ring_nf
  have hwRight : EqOn w (fun x ↦ Real.exp (2 * (b - α) * x)) (Ioi 0) := by
    intro x hx
    dsimp [w]
    rw [abs_of_pos hx]
    ring_nf
  have hiLeft := (integrableOn_congr_fun hwLeft measurableSet_Iic).2
    (integrableOn_exp_mul_Iic hLeft 0)
  have hiRight := (integrableOn_congr_fun hwRight measurableSet_Ioi).2
    (integrableOn_exp_mul_Ioi hRight 0)
  have hw : Integrable w := by
    simpa only [Iic_union_Ioi, integrableOn_univ] using hiLeft.union hiRight
  have hwint : ∫ x : ℝ, w x = α / (α ^ 2 - b ^ 2) := by
    rw [← intervalIntegral.integral_Iic_add_Ioi hiLeft hiRight,
      setIntegral_congr_fun measurableSet_Iic hwLeft, setIntegral_congr_fun measurableSet_Ioi hwRight,
      integral_exp_mul_Iic hLeft, integral_exp_mul_Ioi hRight]
    simp only [mul_zero, exp_zero]
    have hd : α ^ 2 - b ^ 2 ≠ 0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero (by linarith : α + b ≠ 0) (by linarith : α - b ≠ 0)
    have hsum : b + α ≠ 0 := by linarith
    have hdiff : b - α ≠ 0 := by linarith
    field_simp [hd, hsum, hdiff]
    ring
  have hw1 (x : ℝ) : w x ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hbx : b * x ≤ α * |x| :=
      calc b * x ≤ |b * x| := le_abs_self _
           _ = |b| * |x| := abs_mul _ _
           _ ≤ α * |x| := mul_le_mul_of_nonneg_right hb.le (abs_nonneg x)
    linarith
  let r (x : ℝ) := w x / (1 + x ^ 2)
  have hr0 (x : ℝ) : 0 ≤ r x := div_nonneg (Real.exp_nonneg _) (by positivity)
  have hr1 (x : ℝ) : r x ≤ (1 + x ^ 2)⁻¹ := by
    simpa only [r, div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_right (hw1 x) (show 0 ≤ (1 + x ^ 2)⁻¹ by positivity)
  have hr : Integrable r := by
    refine integrable_inv_one_add_sq.mono' ?_ (ae_of_all _ fun x ↦ ?_)
    · have hden (x : ℝ) : 1 + x ^ 2 ≠ 0 := by positivity
      exact ((by fun_prop : Continuous w).div (by fun_prop) hden).aestronglyMeasurable
    · simpa only [Real.norm_eq_abs, abs_of_nonneg (hr0 x)] using hr1 x
  have heq : (∫ x : ℝ, Real.exp (2 * b * x - 2 * α * |x|) * x ^ 2 / (1 + x ^ 2)) =
      (∫ x : ℝ, w x) - ∫ x : ℝ, r x := by
    rw [← integral_sub hw hr]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [w, r]
    field_simp
    ring
  dsimp only
  rw [heq, hwint]
  have hπ := integral_mono hr integrable_inv_one_add_sq hr1
  rw [integral_univ_inv_one_add_sq] at hπ
  exact ⟨by linarith, sub_le_self _ (integral_nonneg hr0)⟩

/-- Paper: Proposition 10.2.2.2, pp. 446–447. A bound on the order-one jet integral at
Sobolev order two gives an explicit lower bound on the distance to either edge. -/
theorem spectralStripJet_orderOne_margin_of_integral_bound {α b C : ℝ} (hb : |b| < α)
    (hC : (∫ x : ℝ, Real.exp (2 * b * x - 2 * α * |x|) * x ^ 2 / (1 + x ^ 2)) ≤ C) :
    1 / (2 * (C + π)) ≤ α - |b| := by
  have he := (spectralStripJet_orderOne_integral_edge_bounds hb).1.trans hC
  have hA : 0 < α := (abs_nonneg b).trans_lt hb
  have hδ : 0 < α - |b| := sub_pos.mpr hb
  have hsum : 0 < α + |b| := add_pos_of_pos_of_nonneg hA (abs_nonneg b)
  have hprod : α ^ 2 - b ^ 2 = (α + |b|) * (α - |b|) := by
    rw [← sq_sub_sq, sq_abs]
  have hinv : 1 / (2 * (α - |b|)) ≤ α / (α ^ 2 - b ^ 2) := by
    rw [hprod, div_le_div_iff₀ (by positivity) (mul_pos hsum hδ)]
    nlinarith [sq_nonneg (α - |b|)]
  have hle : 1 / (2 * (α - |b|)) ≤ C + π := by linarith
  have hCp : 0 < C + π := (by positivity : 0 < 1 / (2 * (α - |b|))).trans_le hle
  rw [div_le_iff₀ (by positivity)] at hle ⊢
  linarith

/-- Paper: Proposition 10.2.2.2, pp. 446–447. At Sobolev order two, multiplying the
order-one jet integral by the distance to either strip edge gives the limit one half. -/
theorem spectralStripJet_orderOne_scaled_integral_tendsto {ι : Type*} {l : Filter ι}
    {α : ℝ} (hα : 0 < α) {b : ι → ℝ} (hb : Tendsto (fun i ↦ |b i|) l (𝓝[<] α)) :
    Tendsto (fun i ↦ (α - |b i|) *
      ∫ x : ℝ, Real.exp (2 * b i * x - 2 * α * |x|) * x ^ 2 / (1 + x ^ 2)) l (𝓝 (1 / 2)) := by
  have h := tendsto_scaled_polynomialWeight_laplace_gamma hα 1 zero_le_two (by norm_num) hb
  norm_num [Real.Gamma_one, ← div_eq_mul_inv] at h
  have h' := h.div_const 2
  convert h' using 2
  ring

section IdeleClassJets

set_option quotPrecheck false

open NumberField
open scoped NNReal NumberField.AdeleRing

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "jetLp(" χ ", " hα ", " hs ", " j ")" =>
  (spectralStripJet_memLp χ hα hs j).toLp
    (spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2)

/-- Paper: Proposition 10.2.2.2, pp. 446–447. The squared norm of every admitted
order-one strip jet at Sobolev order two is within `A * π` of its edge pole, where
`A` is the factor converting canonical modulated Haar measure to Tamagawa measure. -/
theorem spectralStripJet_orderOne_norm_sq_edge_bounds
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a α : ℝ} (hα : 0 ≤ α)
    (j : SpectralStripJetIndex χ a α 2) (hj : j.val.2.2.2 = 1)
    (ν : Measure C𝔽) [ν.IsHaarMeasure] (hν : ν = canonicalModulatedHaar m𝔽 hm𝔽) :
    let A : ℝ := Measure.haarScalarFactor (ideleClassTamagawaMeasure F) ν
    let b := j.val.2.1
    A * (α / (α ^ 2 - b ^ 2) - π) ≤ ‖jetLp(χ, hα, zero_le_two, j)‖ ^ 2 ∧
      ‖jetLp(χ, hα, zero_le_two, j)‖ ^ 2 ≤ A * (α / (α ^ 2 - b ^ 2)) := by
  have hb : |j.val.2.1| < α := by
    have h := j.property
    unfold spectralStripMultiplicity at h
    split_ifs at h with hi he
    · exact abs_lt.mpr hi
    · have hh := ((lt_spectralBoundaryMultiplicity _ _ _).mp h).2
      norm_num [hj] at hh
    · omega
  dsimp only
  rw [spectralStripJet_norm_sq χ hα zero_le_two j ν hν]
  simp only [hj, mul_one, div_self (two_ne_zero : (2 : ℝ) ≠ 0), Real.rpow_one, ← div_eq_mul_inv]
  obtain ⟨hlo, hhi⟩ := spectralStripJet_orderOne_integral_edge_bounds hb
  exact ⟨mul_le_mul_of_nonneg_left hlo (NNReal.coe_nonneg _),
    mul_le_mul_of_nonneg_left hhi (NNReal.coe_nonneg _)⟩

/-- Paper: Proposition 10.2.2.2, pp. 446–447. Along any family of admitted order-`k` jets
approaching the strip boundary with `s < 2k + 1`, the rescaled squared norms tend to the
Gamma coefficient times the Tamagawa-to-canonical Haar factor. -/
theorem spectralStripJet_scaled_norm_sq_tendsto_Gamma
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s)
    (k : ℕ) (hp : -1 < ((2 * k : ℕ) - s : ℝ)) {ι : Type*} {l : Filter ι}
    (j : ι → SpectralStripJetIndex χ a α s) (hk : ∀ i, (j i).val.2.2.2 = k)
    (hb : Tendsto (fun i ↦ |(j i).val.2.1|) l (𝓝[<] α))
    (ν : Measure C𝔽) [ν.IsHaarMeasure] (hν : ν = canonicalModulatedHaar m𝔽 hm𝔽) :
    let A : ℝ := Measure.haarScalarFactor (ideleClassTamagawaMeasure F) ν
    Tendsto (fun i ↦ (2 * (α - |(j i).val.2.1|)) ^ ((2 * k : ℕ) - s + 1 : ℝ) *
      ‖jetLp(χ, hα.le, hs, j i)‖ ^ 2) l (𝓝 (A * Real.Gamma ((2 * k : ℕ) - s + 1 : ℝ))) := by
  let A : ℝ := Measure.haarScalarFactor (ideleClassTamagawaMeasure F) ν
  apply ((tendsto_scaled_polynomialWeight_laplace_gamma hα k hs hp hb).const_mul A).congr'
  filter_upwards [] with i
  rw [spectralStripJet_norm_sq χ hα.le hs (j i) ν hν, hk i]
  exact mul_left_comm _ _ _

/-- Paper: Proposition 10.2.2.2, pp. 446–447. At the critical Sobolev order `s = 2k + 1`,
the squared jet norm divided by the logarithm of the inverse scaled distance to the edge
tends to the Tamagawa-to-canonical Haar factor. -/
theorem spectralStripJet_critical_norm_sq_div_log_tendsto
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a α : ℝ} (hα : 0 < α) (k : ℕ)
    {ι : Type*} {l : Filter ι} (j : ι → SpectralStripJetIndex χ a α ((2 * k : ℕ) + 1 : ℝ))
    (hk : ∀ i, (j i).val.2.2.2 = k) (hb : Tendsto (fun i ↦ |(j i).val.2.1|) l (𝓝[<] α))
    (ν : Measure C𝔽) [ν.IsHaarMeasure] (hν : ν = canonicalModulatedHaar m𝔽 hm𝔽) :
    let A : ℝ := Measure.haarScalarFactor (ideleClassTamagawaMeasure F) ν
    let hs : 0 ≤ ((2 * k : ℕ) + 1 : ℝ) := by positivity
    Tendsto (fun i ↦ ‖jetLp(χ, hα.le, hs, j i)‖ ^ 2 / (-Real.log (2 * (α - |(j i).val.2.1|))))
      l (𝓝 A) := by
  let A : ℝ := Measure.haarScalarFactor (ideleClassTamagawaMeasure F) ν
  have hs : 0 ≤ ((2 * k : ℕ) + 1 : ℝ) := by positivity
  have h := (tendsto_polynomialWeight_laplace_div_log hα k hb).const_mul A
  rw [mul_one] at h
  apply h.congr'
  filter_upwards [] with i
  rw [spectralStripJet_norm_sq χ hα.le hs (j i) ν hν, hk i]
  exact (mul_div_assoc _ _ _).symm

/-- Paper: Proposition 10.2.2.2, pp. 446–447. When `s > 2k + 1`, the squared norm of an
order-`k` jet tends at either edge to the finite radial endpoint integral with its Haar factor. -/
theorem spectralStripJet_norm_sq_tendsto_endpoint
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a α s : ℝ} (hα : 0 ≤ α) (k : ℕ)
    (hs : 2 * (k : ℝ) + 1 < s) {ι : Type*} {l : Filter ι}
    (j : ι → SpectralStripJetIndex χ a α s) (hk : ∀ i, (j i).val.2.2.2 = k)
    (hb : Tendsto (fun i ↦ |(j i).val.2.1|) l (𝓝[<] α))
    (ν : Measure C𝔽) [ν.IsHaarMeasure] (hν : ν = canonicalModulatedHaar m𝔽 hm𝔽) :
    let A : ℝ := Measure.haarScalarFactor (ideleClassTamagawaMeasure F) ν
    let hs' : 0 ≤ s := by linarith [Nat.cast_nonneg (α := ℝ) k]
    Tendsto (fun i ↦ ‖jetLp(χ, hα, hs', j i)‖ ^ 2) l
      (𝓝 (A * ∫ x : ℝ, Real.exp (2 * α * x - 2 * α * |x|) * x ^ (2 * k) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹)) := by
  let A : ℝ := Measure.haarScalarFactor (ideleClassTamagawaMeasure F) ν
  have hs' : 0 ≤ s := by linarith [Nat.cast_nonneg (α := ℝ) k]
  apply ((tendsto_polynomialWeight_laplace_endpoint k hs hb).const_mul A).congr'
  filter_upwards [] with i
  rw [spectralStripJet_norm_sq χ hα hs' (j i) ν hν, hk i]

end IdeleClassJets

end RiemannMasullo.Isolated
