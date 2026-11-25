module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Abel means of exponentially weighted squares

On the positive half-line, the Abel mean of `‖f(y)‖² exp(-2cy)` averages it against
`ε exp(-εy) dy`. Finiteness at `ε > 0` gives absolute integrability with any exponential
weight of exponent `σ > c + ε / 2`. When `c > 0`, a bounded error in a function of growth
`O(exp(cy))` preserves the Abel limit.
-/

open Filter MeasureTheory Real Set
open scoped ENNReal Topology

@[expose] public noncomputable section

namespace RiemannMasullo.AbelEdge

/-- The Abel mean of the squared norm of an exponentially weighted function on `[0, ∞)`,
with shift `c` and damping parameter `ε`. -/
def weightedSquareAbelMean (f : ℝ → ℂ) (c ε : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ε * ∫⁻ y in Ici (0 : ℝ), ENNReal.ofReal (‖f y‖ ^ 2 * exp (-(ε + 2 * c) * y))

private theorem integrableOn_exp_decay {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ ↦ exp (-a * y)) (Ici 0) :=
  Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0)

/-- A square-integrable exponential weight gives absolute integrability at every
strictly larger exponent on the positive half-line. -/
theorem integrableOn_norm_mul_exp_of_sq_mul_exp {f : ℝ → ℂ} (hf : Measurable f)
    {q σ : ℝ} (hσ : q < σ)
    (hL : IntegrableOn (fun y ↦ ‖f y‖ ^ 2 * exp (-(2 * q) * y)) (Ici 0)) :
    IntegrableOn (fun y ↦ ‖f y‖ * exp (-σ * y)) (Ici 0) := by
  have htail : IntegrableOn (fun y : ℝ ↦ exp (-(2 * (σ - q)) * y)) (Ici 0) :=
    integrableOn_exp_decay (show 0 < 2 * (σ - q) by linarith)
  have hm : Measurable (fun y ↦ ‖f y‖ * exp (-σ * y)) := by fun_prop
  apply (hL.add htail).mono' hm.aestronglyMeasurable (.of_forall fun y ↦ ?_)
  change ‖‖f y‖ * exp (-σ * y)‖ ≤ ‖f y‖ ^ 2 * exp (-(2 * q) * y) + exp (-(2 * (σ - q)) * y)
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (exp_pos _).le)]
  have hsquare (r : ℝ) : exp (-r * y) ^ 2 = exp (-(2 * r) * y) := by
    rw [pow_two, ← exp_add]
    congr 1
    ring
  calc
    ‖f y‖ * exp (-σ * y) = (‖f y‖ * exp (-q * y)) * exp (-(σ - q) * y) := by
      rw [mul_assoc, ← exp_add]
      congr 2
      ring
    _ ≤ (‖f y‖ * exp (-q * y)) ^ 2 + exp (-(σ - q) * y) ^ 2 := by
      have hab := two_mul_le_add_sq (‖f y‖ * exp (-q * y)) (exp (-(σ - q) * y))
      have hpos := mul_nonneg (mul_nonneg (norm_nonneg (f y)) (exp_pos (-q * y)).le)
        (exp_pos (-(σ - q) * y)).le
      linarith
    _ = _ := by rw [mul_pow, hsquare, hsquare]

/-- At positive `ε`, finiteness of the scaled extended-real mean is exactly weighted
square integrability at `q = c + ε / 2`. -/
theorem weightedSquareAbelMean_ne_top_iff_integrableOn_sq_mul_exp {f : ℝ → ℂ}
    (hf : Measurable f) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    weightedSquareAbelMean f c ε ≠ ∞ ↔
      IntegrableOn (fun y ↦ ‖f y‖ ^ 2 * exp (-(2 * (c + ε / 2)) * y)) (Ici 0) := by
  let g (y : ℝ) := ‖f y‖ ^ 2 * exp (-(ε + 2 * c) * y)
  have hg : Measurable g := by
    dsimp [g]
    fun_prop
  have hg₀ (y : ℝ) : 0 ≤ g y := mul_nonneg (sq_nonneg _) (exp_pos _).le
  rw [show 2 * (c + ε / 2) = ε + 2 * c by ring]
  change (ENNReal.ofReal ε * ∫⁻ y in Ici (0 : ℝ), ENNReal.ofReal (g y)) ≠ ∞ ↔
    Integrable g (volume.restrict (Ici 0))
  have hscale : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  rw [← lintegral_ofReal_ne_top_iff_integrable hg.aestronglyMeasurable (.of_forall hg₀)]
  constructor
  · intro hfinite htop
    exact hfinite (by rw [htop, ENNReal.mul_top hscale])
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top

private def abelDensity (f : ℝ → ℂ) (c ε y : ℝ) : ℝ :=
  ‖f y‖ ^ 2 * exp (-(ε + 2 * c) * y)

/-- A pointwise exponential growth bound gives integrability of the square density at
every positive Abel parameter. -/
private theorem integrableOn_sq_mul_abelWeight_of_exp_bound {f : ℝ → ℂ} (hf : Measurable f)
    {A c ε : ℝ} (hε : 0 < ε) (hF : ∀ y : ℝ, 0 ≤ y → ‖f y‖ ≤ A * exp (c * y)) :
    IntegrableOn (fun y ↦ ‖f y‖ ^ 2 * exp (-(ε + 2 * c) * y)) (Ici 0) := by
  have hm : Measurable (abelDensity f c ε) := by
    unfold abelDensity
    fun_prop
  apply ((integrableOn_exp_decay hε).const_mul (A ^ 2)).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ici] with y (hy : 0 ≤ y)
  change ‖‖f y‖ ^ 2 * exp (-(ε + 2 * c) * y)‖ ≤ A ^ 2 * exp (-ε * y)
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (exp_pos _).le)]
  calc
    _ ≤ (A * exp (c * y)) ^ 2 * exp (-(ε + 2 * c) * y) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hF y hy) 2) (exp_pos _).le
    _ = _ := by
      rw [mul_pow, mul_assoc, pow_two (exp _), ← exp_add, ← exp_add]
      congr 2
      ring

private theorem norm_le_exp_of_bounded_sub {f g : ℝ → ℂ} {c C A : ℝ} (hc : 0 ≤ c)
    (hd : ∀ y : ℝ, 0 ≤ y → ‖f y - g y‖ ≤ C)
    (hg : ∀ y : ℝ, 0 ≤ y → ‖g y‖ ≤ A * exp (c * y))
    (y : ℝ) (hy : 0 ≤ y) : ‖f y‖ ≤ (C + A) * exp (c * y) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hd 0 le_rfl)
  calc
    ‖f y‖ ≤ C + ‖g y‖ := by linarith [(norm_sub_norm_le (f y) (g y)).trans (hd y hy)]
    _ ≤ C * exp (c * y) + A * exp (c * y) :=
      add_le_add (le_mul_of_one_le_right hC (one_le_exp (mul_nonneg hc hy))) (hg y hy)
    _ = _ := (add_mul ..).symm

private theorem norm_abelDensity_sub_le {f g : ℝ → ℂ} {c C A : ℝ} (hc : 0 ≤ c)
    (hd : ∀ y : ℝ, 0 ≤ y → ‖f y - g y‖ ≤ C)
    (hg : ∀ y : ℝ, 0 ≤ y → ‖g y‖ ≤ A * exp (c * y))
    (ε y : ℝ) (hy : 0 ≤ y) :
    ‖abelDensity f c ε y - abelDensity g c ε y‖ ≤ C * (C + 2 * A) * exp (-(ε + c) * y) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hd 0 le_rfl)
  have hsum : ‖f y‖ + ‖g y‖ ≤ (C + 2 * A) * exp (c * y) := by
    linarith [norm_le_exp_of_bounded_sub hc hd hg y hy, hg y hy]
  have hsquare : |‖f y‖ ^ 2 - ‖g y‖ ^ 2| ≤ C * ((C + 2 * A) * exp (c * y)) := by
    rw [show ‖f y‖ ^ 2 - ‖g y‖ ^ 2 = (‖f y‖ - ‖g y‖) * (‖f y‖ + ‖g y‖) by ring,
      abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul ((abs_norm_sub_norm_le _ _).trans (hd y hy)) hsum
      (add_nonneg (norm_nonneg _) (norm_nonneg _)) hC
  unfold abelDensity
  rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
  calc
    _ ≤ (C * ((C + 2 * A) * exp (c * y))) * exp (-(ε + 2 * c) * y) :=
      mul_le_mul_of_nonneg_right hsquare (exp_pos _).le
    _ = _ := by
      rw [← mul_assoc C (C + 2 * A), mul_assoc (C * (C + 2 * A)), ← exp_add]
      congr 2
      ring

/-- If `‖f - g‖ ≤ C` and `‖g(y)‖ ≤ A exp(cy)` on the positive half-line, the real square
means differ by at most `C (C + 2 A) ε / (ε + c)`. -/
theorem abs_abel_square_difference_le_of_bounded_sub {f g : ℝ → ℂ}
    (hf : Measurable f) (hg : Measurable g) {c C A ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hd : ∀ y : ℝ, 0 ≤ y → ‖f y - g y‖ ≤ C)
    (hG : ∀ y : ℝ, 0 ≤ y → ‖g y‖ ≤ A * exp (c * y)) :
    |ε * (∫ y in Ici (0 : ℝ), ‖f y‖ ^ 2 * exp (-(ε + 2 * c) * y)) -
      ε * (∫ y in Ici (0 : ℝ), ‖g y‖ ^ 2 * exp (-(ε + 2 * c) * y))| ≤
      ε * (C * (C + 2 * A) / (ε + c)) := by
  have hFi : IntegrableOn (abelDensity f c ε) (Ici 0) :=
    integrableOn_sq_mul_abelWeight_of_exp_bound hf hε (norm_le_exp_of_bounded_sub hc.le hd hG)
  have hGi : IntegrableOn (abelDensity g c ε) (Ici 0) :=
    integrableOn_sq_mul_abelWeight_of_exp_bound hg hε hG
  let D := C * (C + 2 * A)
  have hmaj : IntegrableOn (fun y : ℝ ↦ D * exp (-(ε + c) * y)) (Ici 0) :=
    (integrableOn_exp_decay (add_pos hε hc)).const_mul D
  change |ε * (∫ y in Ici (0 : ℝ), abelDensity f c ε y) -
    ε * (∫ y in Ici (0 : ℝ), abelDensity g c ε y)| ≤ ε * (D / (ε + c))
  rw [← mul_sub, abs_mul, abs_of_pos hε, ← integral_sub hFi hGi, ← Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ hε.le
  calc
    _ ≤ ∫ y in Ici (0 : ℝ), ‖abelDensity f c ε y - abelDensity g c ε y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ici (0 : ℝ), D * exp (-(ε + c) * y) := by
      apply integral_mono_ae (hFi.sub hGi).norm hmaj
      filter_upwards [ae_restrict_mem measurableSet_Ici] with y (hy : 0 ≤ y)
      exact norm_abelDensity_sub_le hc.le hd hG ε y hy
    _ = D / (ε + c) := by
      rw [integral_const_mul, integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (by linarith)]
      rw [mul_zero, exp_zero, neg_div_neg_eq, ← mul_div_assoc, mul_one]

/-- At any fixed positive shift, bounded errors in an exponentially bounded profile have
vanishing normalized square-mean discrepancy as the Abel parameter decreases to zero. -/
private theorem tendsto_abel_square_difference_of_bounded_sub {f g : ℝ → ℂ}
    (hf : Measurable f) (hg : Measurable g) {c C A : ℝ} (hc : 0 < c)
    (hd : ∀ y : ℝ, 0 ≤ y → ‖f y - g y‖ ≤ C)
    (hG : ∀ y : ℝ, 0 ≤ y → ‖g y‖ ≤ A * exp (c * y)) :
    Tendsto (fun ε : ℝ ↦ ε * (∫ y in Ici (0 : ℝ), ‖f y‖ ^ 2 * exp (-(ε + 2 * c) * y)) -
      ε * (∫ y in Ici (0 : ℝ), ‖g y‖ ^ 2 * exp (-(ε + 2 * c) * y))) (𝓝[>] 0) (𝓝 0) := by
  let D := C * (C + 2 * A)
  have hC : 0 ≤ C := (norm_nonneg _).trans (hd 0 le_rfl)
  have hA : 0 ≤ A := (norm_nonneg (g 0)).trans (by simpa using hG 0 le_rfl)
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun ε : ℝ ↦ ε * (D / c)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul] using hid.mul_const (D / c)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) ?_ hzero
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [Real.norm_eq_abs]
  exact (abs_abel_square_difference_le_of_bounded_sub hf hg hc hε hd hG).trans
    (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hD hc (by linarith)) hε.le)

/-- At a positive shift, a bounded difference preserves the Abel limit of the squared norm
under the stated exponential growth bound. The real integral for `g` uses `(0, ∞)` and
the extended-real mean for `f` uses `[0, ∞)` with Lebesgue measure. -/
theorem tendsto_ennreal_abel_square_of_bounded_sub {f g : ℝ → ℂ}
    (hf : Measurable f) (hg : Measurable g) {c C A M : ℝ} (hc : 0 < c)
    (hd : ∀ y : ℝ, 0 ≤ y → ‖f y - g y‖ ≤ C)
    (hG : ∀ y : ℝ, 0 ≤ y → ‖g y‖ ≤ A * exp (c * y))
    (hM : Tendsto (fun ε : ℝ ↦ ε * ∫ y : ℝ in Ioi 0,
      exp (-(ε + 2 * c) * y) * ‖g y‖ ^ 2) (𝓝[>] 0) (𝓝 M)) :
    Tendsto (weightedSquareAbelMean f c) (𝓝[>] 0) (𝓝 (ENNReal.ofReal M)) := by
  have hgmean : Tendsto (fun ε : ℝ ↦ ε * ∫ y in Ici (0 : ℝ), abelDensity g c ε y)
      (𝓝[>] 0) (𝓝 M) := by
    simpa only [abelDensity, integral_Ici_eq_integral_Ioi, mul_comm] using hM
  have hdif := tendsto_abel_square_difference_of_bounded_sub hf hg hc hd hG
  have hfmean : Tendsto (fun ε : ℝ ↦ ε * ∫ y in Ici (0 : ℝ), abelDensity f c ε y)
      (𝓝[>] 0) (𝓝 M) := by
    simpa only [abelDensity, sub_add_cancel, zero_add] using hdif.add hgmean
  apply (ENNReal.tendsto_ofReal hfmean).congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hFi : IntegrableOn (abelDensity f c ε) (Ici 0) :=
    integrableOn_sq_mul_abelWeight_of_exp_bound hf hε (norm_le_exp_of_bounded_sub hc.le hd hG)
  have hpos (y : ℝ) : 0 ≤ abelDensity f c ε y := mul_nonneg (sq_nonneg _) (exp_pos _).le
  rw [weightedSquareAbelMean, ENNReal.ofReal_mul hε.le,
    ofReal_integral_eq_lintegral_ofReal hFi (.of_forall hpos)]
  rfl

/-- If the unaveraged squared energy at the given shift is integrable, it is
the exact coefficient of the Abel mean to first order in the damping
parameter. It also bounds every positive damped mean after normalization. -/
theorem weightedSquareAbelMean_firstOrder {f : ℝ → ℂ} (hf : Measurable f) (c : ℝ)
    (hint : IntegrableOn (fun y : ℝ ↦ ‖f y‖ ^ 2 * exp (-(2 * c) * y)) (Ici 0)) :
    let E := ∫ y in Ici (0 : ℝ), ‖f y‖ ^ 2 * exp (-(2 * c) * y)
    (∀ ε > (0 : ℝ), weightedSquareAbelMean f c ε ≤ ENNReal.ofReal ε * ENNReal.ofReal E) ∧
      Tendsto (fun ε : ℝ ↦ weightedSquareAbelMean f c ε / ENNReal.ofReal ε)
        (𝓝[>] 0) (𝓝 (ENNReal.ofReal E)) := by
  let μ := volume.restrict (Ici (0 : ℝ))
  let G (ε y : ℝ) := ‖f y‖ ^ 2 * exp (-(ε + 2 * c) * y)
  have hGm (ε : ℝ) : Measurable (G ε) := by dsimp only [G]; fun_prop
  have hG₀ (ε y : ℝ) : 0 ≤ G ε y := mul_nonneg (sq_nonneg _) (exp_pos _).le
  have h0 : Integrable (G 0) μ := by simpa [μ, G, IntegrableOn] using hint
  have hle (ε : ℝ) (hε : 0 ≤ ε) : ∀ᵐ y ∂μ, G ε y ≤ G 0 y := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ici] with y hy
    apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (by linarith) hy
  have hi (ε : ℝ) (hε : 0 ≤ ε) : Integrable (G ε) μ :=
    h0.mono' (hGm ε).aestronglyMeasurable ((hle ε hε).mono fun y hy ↦ by
      simpa only [Real.norm_of_nonneg (hG₀ _ _)] using hy)
  have hmean (ε : ℝ) (hε : 0 ≤ ε) :
      weightedSquareAbelMean f c ε = ENNReal.ofReal ε * ENNReal.ofReal (∫ y, G ε y ∂μ) := by
    rw [weightedSquareAbelMean, ofReal_integral_eq_lintegral_ofReal (hi ε hε) (.of_forall (hG₀ ε))]
  change (∀ ε > (0 : ℝ), weightedSquareAbelMean f c ε ≤ ENNReal.ofReal ε *
    ENNReal.ofReal (∫ y in Ici (0 : ℝ), ‖f y‖ ^ 2 * exp (-(2 * c) * y))) ∧ _
  have heq : (∫ y, G 0 y ∂μ) = ∫ y in Ici (0 : ℝ), ‖f y‖ ^ 2 * exp (-(2 * c) * y) := by simp [μ, G]
  rw [← heq]
  constructor
  · intro ε hε
    rw [hmean ε hε.le]
    exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (integral_mono_ae (hi _ hε.le) h0 (hle ε hε.le))) bot_le
  · have hlim : Tendsto (fun ε : ℝ ↦ ∫ y, G ε y ∂μ) (𝓝[>] 0) (𝓝 (∫ y, G 0 y ∂μ)) := by
      refine tendsto_integral_filter_of_dominated_convergence (G 0)
        (.of_forall fun ε ↦ (hGm ε).aestronglyMeasurable) ?_ h0 ?_
      · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
        exact (hle ε hε.le).mono fun y hy ↦ by simpa only [Real.norm_of_nonneg (hG₀ _ _)] using hy
      · exact .of_forall fun y ↦
          ((by dsimp only [G]; fun_prop : Continuous (fun ε ↦ G ε y)).tendsto 0).mono_left nhdsWithin_le_nhds
    apply (ENNReal.tendsto_ofReal hlim).congr'
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [hmean ε hε.le, mul_comm (ENNReal.ofReal ε), mul_div_assoc,
      ENNReal.div_self (ENNReal.ofReal_pos.mpr hε).ne' ENNReal.ofReal_ne_top, mul_one]

end RiemannMasullo.AbelEdge
