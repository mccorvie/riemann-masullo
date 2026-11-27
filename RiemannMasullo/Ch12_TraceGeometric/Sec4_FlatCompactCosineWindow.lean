module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatCompactCosineLimit
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Order.Field

/-!
# Bounds for Gaussian shifts of the reduced finite cosine band

The reduced-band trace is uniformly bounded in every logarithmic shift by the size
of its unshifted spatial-frequency rectangle. Near zero, all traces in a single
fixed shift window eventually approximate the same compact-test orbital value.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped NNReal CompactlySupported Topology

namespace RiemannMasullo.FlatPolar

private theorem reducedCosineBand_eq (B r : ℝ) (hB : 0 ≤ B) :
    min B (r * B) = min 1 r * B := by
  by_cases hr : 1 ≤ r
  · have h : B ≤ r * B := by simpa using (mul_le_mul_of_nonneg_right hr hB)
    rw [min_eq_left hr, one_mul, min_eq_left h]
  · have hr' := le_of_not_ge hr
    have h : r * B ≤ B := by simpa using (mul_le_mul_of_nonneg_right hr' hB)
    rw [min_eq_right hr', min_eq_right h]

private theorem norm_hilbertTrace_cosine_atom_rectangular {h L b a : ℝ} (hh : 0 ≤ h)
    (hL : 0 ≤ L) (hb : 0 ≤ b) (ha : 0 < a) :
    ‖hilbertTrace (finiteCosineTraceOperator 0 b h L a)‖ ≤ 4 * (b * L) / Real.sqrt a := by
  let f (x t : ℝ) := Real.cos (2 * Real.pi * (x * t)) * Real.cos (2 * Real.pi * (x * t / a))
  have hf (x t : ℝ) : ‖f x t‖ ≤ 1 := by
    dsimp only [f]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc
      _ ≤ (1 : ℝ) * 1 := mul_le_mul
        (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
        (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hrow (x : ℝ) : ‖∫ t in Ioc (0 : ℝ) b, f x t‖ ≤ b := by
    simpa only [Real.volume_real_Ioc_of_le hb, sub_zero, one_mul] using
      (norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ)) (C := 1)
        measure_Ioc_lt_top (fun t (_ : t ∈ Ioc 0 b) ↦ hf x t))
  have harea : ‖∫ x in Ioc h L, ∫ t in Ioc (0 : ℝ) b, f x t‖ ≤ b * L := by
    calc
      _ ≤ b * volume.real (Ioc h L) := norm_setIntegral_le_of_norm_le_const
        measure_Ioc_lt_top (fun x _ ↦ hrow x)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by rw [Real.volume_real_Ioc]; exact max_le (by linarith) hL) hb
  rw [hilbertTrace_finiteCosine_frequencyBand _ _ _ _ hh]
  change ‖((4 / Real.sqrt a * ∫ x in Ioc h L, ∫ t in Ioc (0 : ℝ) b, f x t : ℝ) : ℂ)‖ ≤ _
  rw [Complex.norm_real, norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 4 / Real.sqrt a)]
  calc
    _ ≤ (4 / Real.sqrt a) * (b * L) := mul_le_mul_of_nonneg_left harea (by positivity)
    _ = _ := by ring

private theorem min_one_le_sqrt {r : ℝ} (hr : 0 < r) : min 1 r ≤ Real.sqrt r := by
  by_cases h : r ≤ 1
  · rw [min_eq_right h]
    calc
      r = Real.sqrt r * Real.sqrt r := (Real.mul_self_sqrt hr.le).symm
      _ ≤ _ := mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr h)
  · rw [min_eq_left (le_of_not_ge h)]
    exact Real.one_le_sqrt.mpr (le_of_not_ge h)

/-- For every positive shift, reducing the band to `min B (r B)` absorbs the inverse
square-root dilation growth. The resulting global bound is independent of the shift. -/
theorem norm_hilbertTrace_compactCosineShift_reducedBand_le
    (φ : C_c(ℝ≥0ˣ, ℂ)) (r : ℝ≥0ˣ) {B h L : ℝ} (hB : 0 ≤ B) (hh : 0 ≤ h) (hL : 0 ≤ L) :
    ‖hilbertTrace (compactCosineTraceOperator 0 (min B ((r.val : ℝ) * B)) h L
        (compactRadialTranslate φ r))‖ ≤
      (4 * (B * L)) * ∫ a : ℝ≥0ˣ, ‖φ a‖ / Real.sqrt a.val ∂positiveRealHaar := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  let b := min B ((r.val : ℝ) * B)
  let P := 4 * (B * L)
  have hpositive (a : ℝ≥0ˣ) : 0 < (a.val : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr a.ne_zero)
  have hp (a : ℝ≥0ˣ) : 0 < Real.sqrt a.val := Real.sqrt_pos.mpr (hpositive a)
  have hb : 0 ≤ b := le_min hB (mul_nonneg (hpositive r).le hB)
  let w (a : ℝ≥0ˣ) := ‖φ a‖ / Real.sqrt a.val
  have hw : Integrable w positiveRealHaar := by
    refine (φ.continuous.norm.div (Real.continuous_sqrt.comp
      (NNReal.continuous_coe.comp Units.continuous_val)) (fun a ↦ (hp a).ne')).integrable_of_hasCompactSupport ?_
    simp only [div_eq_mul_inv]
    exact φ.hasCompactSupport.norm.mul_right
  have hatom (a : ℝ≥0ˣ) : ‖hilbertTrace (finiteCosineTraceOperator 0 b h L (a * r).val)‖ ≤ P / Real.sqrt a.val := by
    apply (norm_hilbertTrace_cosine_atom_rectangular hh hL hb (hpositive (a * r))).trans
    change 4 * (min B ((r.val : ℝ) * B) * L) / Real.sqrt ((a.val : ℝ) * (r.val : ℝ)) ≤ P / Real.sqrt a.val
    rw [reducedCosineBand_eq B _ hB, Real.sqrt_mul (hpositive a).le,
      div_le_iff₀ (mul_pos (hp a) (hp r))]
    calc
      _ ≤ 4 * ((Real.sqrt r.val * B) * L) := by gcongr; exact min_one_le_sqrt (hpositive r)
      _ = _ := by dsimp only [P]; field_simp [(hp a).ne']
  rw [hilbertTrace_compactCosineTraceOperator_shift]
  calc
    _ ≤ ∫ a : ℝ≥0ˣ, ‖φ a * hilbertTrace (finiteCosineTraceOperator 0 b h L (a * r).val)‖ ∂positiveRealHaar :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ a, P * w a ∂positiveRealHaar := by
      apply integral_mono_of_nonneg (.of_forall (fun _ ↦ norm_nonneg _)) (hw.const_mul P)
      filter_upwards with a
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hatom a) (norm_nonneg (φ a))).trans_eq (by dsimp only [w]; ring)
    _ = _ := integral_const_mul _ _

/-- For the reduced band and any permitted sequence or net of cutoffs, a single
fixed logarithmic shift neighborhood eventually has the desired error throughout. -/
theorem eventually_hilbertTrace_compactCosineShift_log_reducedBand_near_zero
    {ι : Type*} {l : Filter ι} {h L B : ι → ℝ} (φ : C_c(ℝ≥0ˣ, ℂ)) {η M : ℝ} (hη : 0 < η)
    (hs : ∀ a ∈ tsupport φ, (a.val : ℝ) ∈ Icc (1 + η) M)
    (hbox : ∀ᶠ i in l, 0 ≤ h i ∧ 0 < B i)
    (hBh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hBL : Tendsto (fun i ↦ B i * L i) l atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ i in l, ∀ z : ℝ, |z| < d →
      ‖hilbertTrace (compactCosineTraceOperator 0 (min (B i) (Real.exp z * B i)) (h i) (L i)
        (compactRadialTranslate φ (expRadialUnit z))) - compactCosineOrbitalValue φ 1‖ ≤ ε := by
  let l' : Filter (ι × ℝ) := l ×ˢ 𝓝 (0 : ℝ)
  let p (q : ι × ℝ) := min 1 (Real.exp q.2)
  let b (q : ι × ℝ) := min (B q.1) (Real.exp q.2 * B q.1)
  have hi : Tendsto Prod.fst l' l := tendsto_fst
  have hz : Tendsto Prod.snd l' (𝓝 (0 : ℝ)) := tendsto_snd
  have hp : Tendsto p l' (𝓝 1) := by
    simpa only [p, Function.comp_def, Real.exp_zero, min_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).min ((Real.continuous_exp.tendsto 0).comp hz)
  have hr : Tendsto (fun q : ι × ℝ ↦ expRadialUnit q.2) l' (𝓝 1) := by
    simpa only [Function.comp_def, expRadialUnit_zero] using (continuous_expRadialUnit.tendsto 0).comp hz
  have hbox' : ∀ᶠ q in l', 0 ≤ h q.1 ∧ 0 < b q := by
    filter_upwards [hi.eventually hbox] with q hq
    exact ⟨hq.1, lt_min hq.2 (mul_pos (Real.exp_pos _) hq.2)⟩
  have he (f : ι → ℝ) :
      (fun q : ι × ℝ ↦ p q * (B q.1 * f q.1)) =ᶠ[l'] fun q ↦ b q * f q.1 := by
    filter_upwards [hi.eventually hbox] with q hq
    dsimp only [b, p]
    rw [reducedCosineBand_eq _ _ hq.2.le, mul_assoc]
  have hBh' : Tendsto (fun q : ι × ℝ ↦ b q * h q.1) l' (𝓝 0) := by
    simpa only [mul_zero] using (hp.mul (hBh.comp hi)).congr' (he h)
  have hBL' : Tendsto (fun q : ι × ℝ ↦ b q * L q.1) l' atTop :=
    (hp.pos_mul_atTop zero_lt_one (hBL.comp hi)).congr' (he L)
  have hlim := tendsto_hilbertTrace_compactCosineShift_frequencyBand φ hη hs hr hbox' hBh' hBL'
  have heps := (tendsto_iff_norm_sub_tendsto_zero.mp hlim).eventually (gt_mem_nhds hε)
  obtain ⟨I, hI, U, hU, hIU⟩ := Filter.mem_prod_iff.mp heps
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨d, hd, ?_⟩
  filter_upwards [hI] with i hi'
  intro z hz'
  have hzu : z ∈ U := hball (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hz')
  exact (hIU (show (i, z) ∈ I ×ˢ U from ⟨hi', hzu⟩)).le

end RiemannMasullo.FlatPolar
