module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWSharpCutoff
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! # Weight bounds for the rational real-place cutoff -/

public noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology SchwartzMap

namespace RiemannMasullo.Isolated

private theorem weight_at_large {α s x : ℝ} (ha : 0 ≤ α) (hx : 1 ≤ x) :
    realPWIntervalWeight α s x = x ^ (2 * α) * (1 + Real.log x ^ 2) ^ (s / 2) := by
  rw [realPWIntervalWeight_eq _ _ (show x ≠ 0 by linarith), abs_of_nonneg (by linarith : 0 ≤ x),
    max_eq_left (Real.rpow_le_rpow_of_exponent_le hx (show -(2*α) ≤ 2*α by linarith))]

/-- On a dyadic neighborhood at the positive end the weight ratio is uniformly bounded. -/
theorem realPWIntervalWeight_near_ratio {α s x t : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s)
    (hx : 4 ≤ x) (ht : |t| ≤ x / 2) :
    Real.sqrt (realPWIntervalWeight α s x / realPWIntervalWeight α s (x+t)) ≤
      Real.sqrt ((2 : ℝ) ^ (2*α) * (4 : ℝ) ^ (s/2)) := by
  let y := x+t
  have ht' := (abs_le.mp ht).1
  have hy : 2 ≤ y := by dsimp [y]; linarith
  have hy0 : 0 ≤ y := by linarith
  have hxy : x ≤ 2*y := by dsimp [y]; linarith
  have hxy2 : x ≤ y^2 := by nlinarith [mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ y-2 by linarith)]
  have hl := Real.log_le_log (by linarith : 0 < x) hxy2
  rw [Real.log_pow] at hl
  have hlogs : 1 + Real.log x ^ 2 ≤ 4 * (1 + Real.log y ^ 2) := by
    have h := Real.log_nonneg (show 1 ≤ x by linarith)
    norm_num at hl
    nlinarith [sq_nonneg (Real.log y), mul_nonneg (show 0 ≤ 2 * Real.log y - Real.log x by linarith)
      (show 0 ≤ 2 * Real.log y + Real.log x by linarith)]
  apply Real.sqrt_le_sqrt
  apply (div_le_iff₀ (show 0 < realPWIntervalWeight α s y from lt_of_lt_of_le zero_lt_one (one_le_realPWIntervalWeight α s hs y))).2
  change realPWIntervalWeight α s x ≤ _ * realPWIntervalWeight α s y
  rw [weight_at_large ha (show 1 ≤ x by linarith), weight_at_large ha (show 1 ≤ y by linarith)]
  have hp := Real.rpow_le_rpow (by linarith : 0 ≤ x) hxy (show 0 ≤ 2*α by positivity)
  have hq := Real.rpow_le_rpow (by positivity) hlogs (show 0 ≤ s/2 by positivity)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by linarith : 0 ≤ y)] at hp
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (by positivity : 0 ≤ 1 + Real.log y ^ 2)] at hq
  calc
    _ ≤ _ := mul_le_mul hp hq (by positivity) (by positivity)
    _ = _ := by ring

/-- A single polynomial in the translation controls the square-root ratio at every x ≥ 4. -/
theorem realPWIntervalWeight_translation_envelope {α s : ℝ} (ha : 0 ≤ α) (hs : 0 ≤ s) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ x : ℝ, 4 ≤ x → ∀ t : ℝ,
      Real.sqrt (realPWIntervalWeight α s x / realPWIntervalWeight α s (x+t)) ≤ C * (1+|t|)^N := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2*α + 2*s)
  let A := Real.sqrt ((2 : ℝ) ^ (2*α) * (4 : ℝ) ^ (s/2))
  refine ⟨max A ((2 : ℝ)^N), N, fun x hx t ↦ ?_⟩
  have ht1 : 1 ≤ 1+|t| := by linarith [abs_nonneg t]
  have hpow := one_le_pow₀ ht1 (n := N)
  by_cases ht : |t| ≤ x/2
  · exact (realPWIntervalWeight_near_ratio ha hs hx ht).trans
      ((le_max_left A _).trans (le_mul_of_one_le_right (le_trans (by dsimp [A]; positivity) (le_max_left A _)) hpow))
  · let b := 2*(1+|t|)
    have hb : 1 ≤ b := by dsimp [b]; linarith
    have hb0 : 0 ≤ b := by linarith
    have hxb : x ≤ b := by dsimp [b]; push Not at ht; linarith
    have hl : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos (show 0 < x by linarith)]
    have hl0 := Real.log_nonneg (show 1 ≤ x by linarith)
    have hb2 : 1 + Real.log x ^ 2 ≤ b ^ (4:ℕ) := by
      have hsq := mul_self_le_mul_self hl0 (hl.trans hxb)
      have hb4 : 0 ≤ (b^2-2)*(b^2+1) := mul_nonneg (by nlinarith [sq_nonneg (b-4)]) (by positivity)
      nlinarith
    have hw : realPWIntervalWeight α s x ≤ b^N := by
      rw [weight_at_large ha (show 1 ≤ x by linarith)]
      have hp := Real.rpow_le_rpow (by linarith : 0 ≤ x) hxb (show 0 ≤ 2*α by positivity)
      have hq := Real.rpow_le_rpow (by positivity) hb2 (show 0 ≤ s/2 by positivity)
      rw [← Real.rpow_natCast b 4, ← Real.rpow_mul (by linarith : 0 ≤ b)] at hq
      calc
        _ ≤ _ := mul_le_mul hp hq (by positivity) (by positivity)
        _ = b ^ (2*α + 2*s) := by
          rw [← Real.rpow_add (by linarith : 0 < b)]
          congr 1
          push_cast
          ring
        _ ≤ b ^ (N:ℝ) := Real.rpow_le_rpow_of_exponent_le hb hN
        _ = _ := Real.rpow_natCast _ _
    have hden := one_le_realPWIntervalWeight α s hs (x + t)
    have hr : realPWIntervalWeight α s x / realPWIntervalWeight α s (x+t) ≤ b^N := by
      apply (div_le_iff₀ (by linarith)).2
      exact hw.trans (le_mul_of_one_le_right (pow_nonneg (by linarith) _) hden)
    have hbN := one_le_pow₀ hb (n := N)
    calc
      _ ≤ Real.sqrt (b^N) := Real.sqrt_le_sqrt hr
      _ ≤ b^N := by nlinarith [Real.sq_sqrt (show 0 ≤ b^N by linarith), sq_nonneg (Real.sqrt (b^N)-1)]
      _ = (2:ℝ)^N * (1+|t|)^N := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

private theorem weight_in_log_coordinates (α s x : ℝ) :
    realPWIntervalWeight α s x = Real.exp (abs (2 * α * Real.log (abs x))) *
      (1 + Real.log |x| ^ 2) ^ (s / 2) := by
  rw [Real.rpow_def_of_pos (by positivity : 0 < 1 + Real.log |x| ^ 2),
    mul_comm (Real.log (1 + Real.log |x| ^ 2)) (s / 2)]
  simp only [realPWIntervalWeight, abs_eq_max_neg (a := 2 * α * Real.log |x|),
    Real.exp_monotone.map_max]

/-- Global distortion under positive dilation, for either sign of the strip parameter. -/
theorem realPWIntervalWeight_le_dilation {α s a : ℝ} (hs : 0 ≤ s) (ha : 0 < a) (x : ℝ) :
    realPWIntervalWeight α s x ≤
      (Real.exp (2 * |α * Real.log a|) * (1 + |Real.log a| + Real.log a ^ 2) ^ (s / 2)) *
        realPWIntervalWeight α s (a * x) := by
  let D := 1 + |Real.log a| + Real.log a ^ 2
  have hD : 1 ≤ D := by dsimp [D]; nlinarith [abs_nonneg (Real.log a), sq_nonneg (Real.log a)]
  have hs' : 0 ≤ s / 2 := by positivity
  by_cases hx : x = 0
  · subst x
    simpa [realPWIntervalWeight, D] using
      one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity : 0 ≤ 2 * |α * Real.log a|))
        (Real.one_le_rpow hD hs')
  let t := Real.log |x|
  let b := Real.log |a * x|
  let c := Real.log a
  have hbc : b = c + t := by
    dsimp [b, c, t]
    rw [abs_mul, abs_of_pos ha, Real.log_mul ha.ne' (abs_ne_zero.mpr hx)]
  have habs : |2 * α * t| ≤ 2 * |α * c| + |2 * α * b| := by
    calc
      _ = |-(2 * (α * c)) + 2 * α * b| := by rw [hbc]; congr 1; ring
      _ ≤ |-(2 * (α * c))| + |2 * α * b| := abs_add_le _ _
      _ = _ := by rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have he := Real.exp_monotone habs
  rw [Real.exp_add] at he
  have hpoly : 1 + t ^ 2 ≤ D * (1 + b ^ 2) := by
    change 1 + t ^ 2 ≤ (1 + |c| + c ^ 2) * (1 + b ^ 2)
    have hb : 2 * |b| ≤ 1 + b ^ 2 := by nlinarith [sq_nonneg (|b| - 1), sq_abs b]
    have hcross : -(2 * b * c) ≤ |c| * (1 + b ^ 2) := calc
      _ ≤ |2 * b * c| := neg_le_abs _
      _ = (2 * |b|) * |c| := by rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ (1 + b ^ 2) * |c| := mul_le_mul_of_nonneg_right hb (abs_nonneg c)
      _ = _ := mul_comm _ _
    nlinarith only [hcross, mul_nonneg (sq_nonneg b) (sq_nonneg c),
      show t ^ 2 = (b - c) ^ 2 by rw [hbc]; ring]
  have hp := Real.rpow_le_rpow (by positivity) hpoly hs'
  rw [Real.mul_rpow (by linarith : 0 ≤ D) (by positivity)] at hp
  rw [weight_in_log_coordinates, weight_in_log_coordinates]
  change Real.exp (|2 * α * t|) * (1 + t ^ 2) ^ (s / 2) ≤
    (Real.exp (2 * |α * c|) * D ^ (s / 2)) * (Real.exp (|2 * α * b|) * (1 + b ^ 2) ^ (s / 2))
  exact (mul_le_mul he hp (by positivity) (by positivity)).trans_eq (by ring)

/-- Dilation preserves weighted `MemLp`, including at the endpoint exponents. -/
theorem memLp_realPWIntervalMeasure_dilation {α s a : ℝ} (hs : 0 ≤ s) (ha : 0 < a)
    {p : ℝ≥0∞} {f : ℝ → ℂ} (hf : MemLp f p (realPWIntervalMeasure α s)) :
    MemLp (fun x ↦ f (a * x)) p (realPWIntervalMeasure α s) := by
  let C := Real.exp (2 * |α * Real.log a|) * (1 + |Real.log a| + Real.log a ^ 2) ^ (s / 2)
  let W := fun x ↦ ENNReal.ofReal (realPWIntervalWeight α s x)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hW : Measurable W := (measurable_realPWIntervalWeight α s).ennreal_ofReal
  have hmul : Measurable (a * ·) := measurable_const_mul a
  let k := ENNReal.ofReal C * ENNReal.ofReal |a⁻¹|
  have hmap : Measure.map (a * ·) (realPWIntervalMeasure α s) ≤ k • realPWIntervalMeasure α s := by
    apply Measure.le_iff.mpr
    intro S hS
    rw [Measure.map_apply hmul hS, smul_apply, realPWIntervalMeasure,
      withDensity_apply _ (hmul hS), withDensity_apply _ hS]
    change (∫⁻ x in (a * ·) ⁻¹' S, W x) ≤ k * ∫⁻ x in S, W x
    calc
      _ ≤ ∫⁻ x in (a * ·) ⁻¹' S, ENNReal.ofReal C * W (a * x) := by
        apply lintegral_mono
        intro x
        change ENNReal.ofReal (realPWIntervalWeight α s x) ≤
          ENNReal.ofReal C * ENNReal.ofReal (realPWIntervalWeight α s (a * x))
        rw [← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (realPWIntervalWeight_le_dilation hs ha x)
      _ = ENNReal.ofReal C * ∫⁻ y in S, W y ∂Measure.map (a * ·) volume := by
        rw [setLIntegral_map hS hW hmul]
        exact lintegral_const_mul _ (hW.comp hmul)
      _ = _ := by
        rw [Real.map_volume_mul_left ha.ne', setLIntegral_smul_measure, smul_eq_mul, ← mul_assoc]
  exact ((hf.smul_measure (c := k) (by dsimp [k]; finiteness)).mono_measure hmap).comp_of_map
    hmul.aemeasurable

/-- A Schwartz kernel times the square-root translation distortion has an explicit
square-integrable envelope, independent of the packet center. -/
theorem schwartz_realPWIntervalWeight_L2_envelope {α s : ℝ}
    (h : ∃ C : ℝ, ∃ N : ℕ, ∀ x : ℝ, 4 ≤ x → ∀ t : ℝ,
      Real.sqrt (realPWIntervalWeight α s x / realPWIntervalWeight α s (x+t)) ≤ C*(1+|t|)^N)
    (K : 𝓢(ℝ, ℂ)) : ∃ B : ℝ, MemLp (fun t : ℝ ↦ B*(1+|t|)⁻¹) 2 volume ∧
      ∀ x : ℝ, 4 ≤ x → ∀ t : ℝ, ‖K t‖ *
        Real.sqrt (realPWIntervalWeight α s x / realPWIntervalWeight α s (x+t)) ≤ B*(1+|t|)⁻¹ := by
  obtain ⟨C,N,hC⟩ := h
  let S := (Finset.Iic ((N + 1, 0) : ℕ × ℕ)).sup (fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) K
  let B := |C| * (2^(N+1)*S)
  let u (t : ℝ) := (1 + ‖t‖)⁻¹
  have hu : MemLp u 2 volume := by
    apply (integrable_norm_rpow_iff (by dsimp [u]; fun_prop) (by norm_num) (by norm_num)).mp
    have hn (t : ℝ) : ‖u t‖ = (1 + ‖t‖)⁻¹ := Real.norm_of_nonneg (by dsimp [u]; positivity)
    simpa only [hn, Real.rpow_neg_eq_inv_rpow] using
      (integrable_one_add_norm (μ := (volume : Measure ℝ)) (r := (2 : ENNReal).toReal) (by simp))
  refine ⟨B, ?_, fun x hx t ↦ ?_⟩
  · change MemLp (B • u) 2 volume
    exact hu.const_smul B
  have hk := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N+1, 0))
    (le_refl (N+1)) (le_refl 0) K t
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hk
  change (1+|t|)^(N+1) * ‖K t‖ ≤ 2^(N+1)*S at hk
  have hc := (hC x hx t).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  apply (mul_le_mul_of_nonneg_left hc (norm_nonneg _)).trans
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc
    _ = |C| * ((1+|t|)^(N+1) * ‖K t‖) := by rw [pow_succ]; ring
    _ ≤ B := mul_le_mul_of_nonneg_left hk (abs_nonneg C)

/-- A dilation converging to one changes the interval density by a ratio tending
to one, uniformly with respect to the arguments being dilated. -/
theorem tendsto_realPWIntervalWeight_div_of_dilation_tendsto_one {ι : Type*} {l : Filter ι}
    {α s : ℝ} (hs : 0 ≤ s) {a x : ι → ℝ} (ha : Tendsto a l (𝓝 1)) :
    Tendsto (fun i ↦ realPWIntervalWeight α s (x i) /
      realPWIntervalWeight α s (a i * x i)) l (𝓝 1) := by
  let w := realPWIntervalWeight α s
  let D (a : ℝ) := Real.exp (2 * |α * Real.log a|) *
    (1 + |Real.log a| + Real.log a ^ 2) ^ (s / 2)
  have hlog : ContinuousAt Real.log 1 := Real.continuousAt_log (by norm_num)
  have hc : ContinuousAt (fun _ : ℝ ↦ (1 : ℝ)) 1 := continuousAt_const
  have hpow : ContinuousAt (fun a : ℝ ↦ (1 + |Real.log a| + Real.log a ^ 2) ^ (s / 2)) 1 :=
    ((hc.add hlog.abs).add (hlog.pow 2)).rpow_const (Or.inr (by positivity))
  have hD : ContinuousAt D 1 :=
    (Real.continuous_exp.continuousAt.comp ((hlog.const_mul α).abs.const_mul 2)).mul hpow
  have hD₁ : D 1 = 1 := by simp [D]
  have hpos (a : ℝ) : 0 < D a := by dsimp [D]; positivity
  have hw (a : ℝ) : 0 < w a := zero_lt_one.trans_le (one_le_realPWIntervalWeight α s hs a)
  have hu : Tendsto (fun i ↦ D (a i)) l (𝓝 1) := by
    change Tendsto (D ∘ a) l (𝓝 1)
    rw [← hD₁]
    exact hD.tendsto.comp ha
  have hai : Tendsto (fun i ↦ (a i)⁻¹) l (𝓝 1) := by simpa using ha.inv₀ (by norm_num)
  have hl₀ : Tendsto (fun i ↦ D ((a i)⁻¹)) l (𝓝 1) := by
    change Tendsto (D ∘ fun i ↦ (a i)⁻¹) l (𝓝 1)
    rw [← hD₁]
    exact hD.tendsto.comp hai
  have hl : Tendsto (fun i ↦ (D ((a i)⁻¹))⁻¹) l (𝓝 1) := by
    simpa only [inv_one] using hl₀.inv₀ (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu ?_ ?_
  · filter_upwards [(tendsto_order.1 ha).1 0 zero_lt_one] with i hi
    apply (le_div_iff₀ (hw _)).2
    rw [mul_comm, ← div_eq_mul_inv]
    apply (div_le_iff₀ (hpos _)).2
    have h := realPWIntervalWeight_le_dilation (α := α) hs (inv_pos.mpr hi) (a i * x i)
    rw [← mul_assoc, inv_mul_cancel₀ hi.ne', one_mul] at h
    exact h.trans_eq (mul_comm _ _)
  · filter_upwards [(tendsto_order.1 ha).1 0 zero_lt_one] with i hi
    exact (div_le_iff₀ (hw _)).2 (realPWIntervalWeight_le_dilation hs hi _)

/-- Translation by any fixed displacement has asymptotically unit weight ratio. -/
theorem tendsto_realPWIntervalWeight_translation_ratio (α s t : ℝ) (hs : 0 ≤ s) :
    Tendsto (fun x ↦ realPWIntervalWeight α s x /
      realPWIntervalWeight α s (x + t)) atTop (𝓝 1) := by
  have h : Tendsto (fun x : ℝ ↦ t / x) atTop (𝓝 0) := tendsto_id.const_div_atTop _
  have ha : Tendsto (fun x : ℝ ↦ 1 + t / x) atTop (𝓝 1) := by simpa using h.const_add 1
  refine (tendsto_realPWIntervalWeight_div_of_dilation_tendsto_one (α := α) hs (x := id) ha).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hmul : (1 + t / x) * x = x + t := by field_simp [hx.ne']
  simp only [id_eq, hmul]

end RiemannMasullo.Isolated
