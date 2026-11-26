module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! # Clipped logarithmic quadrature on expanding intervals

The cells have width `1/n` on `[-n,n)`. Exact cell masses give the step-function
integral. A polynomial local derivative bound and logarithmic integrability yield
convergence when the sampled values have a uniform geometric error. -/

@[expose] public noncomputable section
open Filter MeasureTheory Set
open scoped Topology

namespace RiemannMasullo.LogQuadrature

/-- Left end of cell `j` in the mesh of spacing `1/n` starting at `-n`. -/
def node (n j : ℕ) : ℝ := -(n : ℝ) + j / (n : ℝ)

/-- The half-open interval between adjacent mesh nodes. -/
def cell (n j : ℕ) : Set ℝ := Ico (node n j) (node n (j+1))

/-- The cell index at height `x` inside the mesh. -/
def index (n : ℕ) (x : ℝ) : ℕ := ⌊(x + n) * n⌋₊

/-- The log modulus with a floor of `1/n` inside the logarithm. -/
def clip (n : ℕ) (u : ℂ) : ℝ := Real.log (max (n : ℝ)⁻¹ ‖u‖)

/-- The sum uses exact interval masses and the sampled values only at the left endpoints. -/
def statistic (μ : Measure ℝ) (S : ℕ → ℝ → ℂ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (2*n*n), μ.real (cell n j) * clip n (S n (node n j))

private def step (S : ℕ → ℝ → ℂ) (n : ℕ) (x : ℝ) : ℝ :=
  (Ico (-(n : ℝ)) n).indicator (fun y ↦ clip n (S n (node n (index n y)))) x

theorem node_dist (n j : ℕ) :
    node n (j+1) = node n j + (n : ℝ)⁻¹ := by
  simp only [node, Nat.cast_add, Nat.cast_one, add_div, one_div]
  ring

private theorem node_end {n : ℕ} (hn : 0 < n) : node n (2*n*n) = (n : ℝ) := by
  have h : (n : ℝ) ≠ 0 := by positivity
  simp [node, h]
  ring

private theorem cell_iff {n j : ℕ} {x : ℝ} (hn : 0 < n) :
    x ∈ cell n j ↔ (j : ℝ) ≤ (x+n)*n ∧ (x+n)*n < (j : ℝ)+1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  change -(n : ℝ) + (j : ℝ) / n ≤ x ∧
    x < -(n : ℝ) + ((j+1 : ℕ) : ℝ) / n ↔ _
  push_cast
  constructor
  · rintro ⟨h,k⟩
    exact ⟨(div_le_iff₀ hn').mp (by linarith), (lt_div_iff₀ hn').mp (by linarith)⟩
  · rintro ⟨h,k⟩
    have a := (div_le_iff₀ hn').mpr h
    have b := (lt_div_iff₀ hn').mpr k
    constructor <;> linarith

private theorem index_cell {n : ℕ} {x : ℝ} (hn : 0 < n) (hx : x ∈ Ico (-(n:ℝ)) n) :
    index n x < 2*n*n ∧ x ∈ cell n (index n x) := by
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  have hpos : 0 ≤ (x+n)*n := mul_nonneg (by linarith [hx.1]) hN.le
  constructor
  · rw [index,Nat.floor_lt hpos]
    push_cast
    nlinarith [mul_lt_mul_of_pos_right hx.2 hN]
  · rw [cell_iff hn,index]
    exact ⟨Nat.floor_le hpos, Nat.lt_floor_add_one _⟩

theorem of_cell {n j : ℕ} {x : ℝ} (hn : 0 < n) (hj : j < 2*n*n) (hx : x ∈ cell n j) :
    x ∈ Ico (-(n:ℝ)) n ∧ index n x = j := by
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  obtain ⟨a,b⟩ := (cell_iff hn).mp hx
  have hp : 0 ≤ (x+n)*n := (Nat.cast_nonneg j).trans a
  have hbound : (j:ℝ)+1 ≤ (2:ℝ)*n*n := by exact_mod_cast hj
  refine ⟨⟨?_,?_⟩, (Nat.floor_eq_iff hp).mpr ⟨a,b⟩⟩
  · have := nonneg_of_mul_nonneg_left hp hN
    linarith
  · by_contra! h
    nlinarith [mul_le_mul_of_nonneg_right h hN.le]

private theorem step_eq_cell_sum {n : ℕ} (hn : 0 < n) (S : ℕ → ℝ → ℂ) (x : ℝ) :
    step S n x = ∑ j ∈ Finset.range (2*n*n),
      (cell n j).indicator (fun _ ↦ clip n (S n (node n j))) x := by
  classical
  by_cases hx : x ∈ Ico (-(n:ℝ)) n
  · obtain ⟨hi, hc⟩ := index_cell hn hx
    rw [step, indicator_of_mem hx, Finset.sum_eq_single_of_mem (index n x) (Finset.mem_range.mpr hi)]
    · rw [indicator_of_mem hc]
    · intro j hj hne
      exact indicator_of_notMem (fun h ↦ hne ((of_cell hn (Finset.mem_range.mp hj) h).2.symm)) _
  · rw [step, indicator_of_notMem hx, Finset.sum_eq_zero]
    intro j hj
    exact indicator_of_notMem (fun h ↦ hx ((of_cell hn (Finset.mem_range.mp hj) h).1)) _

private theorem integral_step (μ : Measure ℝ) [IsFiniteMeasure μ] (S : ℕ → ℝ → ℂ)
    {n : ℕ} (hn : 0 < n) : (∫ x, step S n x ∂μ) = statistic μ S n := by
  simp_rw [step_eq_cell_sum hn S]
  rw [integral_finsetSum]
  · unfold statistic
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_indicator (show MeasurableSet (cell n j) from measurableSet_Ico), setIntegral_const, smul_eq_mul]
  · intro j _
    exact (integrable_const _).indicator measurableSet_Ico

private theorem measurable_step {n : ℕ} (hn : 0 < n) (S : ℕ → ℝ → ℂ) :
    Measurable (step S n) := by
  simp_rw [funext (step_eq_cell_sum hn S)]
  exact Finset.measurable_sum _ fun _ _ ↦ measurable_const.indicator measurableSet_Ico

/-- The same `1/n` mesh works for every exponent in this local growth bound. -/
def LocalPolynomialLipschitz (f : ℝ → ℂ) (C : ℝ) (p : ℕ) : Prop :=
  ∀ x y : ℝ, |y-x| ≤ 1 → ‖f y - f x‖ ≤ C*(2+|x|)^p*|y-x|

private theorem log_max_le {a b E : ℝ} {u v : ℂ} (ha : 0 < a) (hE : 0 ≤ E)
    (he : ‖u-v‖ ≤ E*a) (hb : b = max a ‖v‖) :
    Real.log (max a ‖u‖) ≤ Real.log (1+E) + Real.log b := by
  subst b
  have hmax : 0 < max a ‖v‖ := ha.trans_le (le_max_left _ _)
  rw [← Real.log_mul (by positivity) hmax.ne']
  apply Real.log_le_log (ha.trans_le (le_max_left _ _))
  have ha' := le_max_left a ‖v‖
  have hv := le_max_right a ‖v‖
  have hnorm := norm_sub_norm_le u v
  have hmul := mul_le_mul_of_nonneg_left ha' hE
  apply max_le <;> nlinarith [mul_nonneg hE hmax.le]

/-- Clipping at (1/n) turns the logarithm of the modulus into an (n)-Lipschitz real function. -/
theorem abs_clip_sub_clip {n : ℕ} (hn : 0 < n) (u v : ℂ) :
    |clip n u - clip n v| ≤ (n:ℝ) * ‖u-v‖ := by
  let D := (n:ℝ)*‖u-v‖
  have hD : 0 ≤ D := by positivity
  have h₁ : ‖u-v‖ ≤ D*(n:ℝ)⁻¹ := by
    dsimp only [D]
    rw [mul_comm (n:ℝ) _,mul_assoc,mul_inv_cancel₀ (by positivity),mul_one]
  have h₂ : ‖v-u‖ ≤ D*(n:ℝ)⁻¹ := by rwa [norm_sub_rev]
  have h₃ := log_max_le (by positivity : 0 < (n:ℝ)⁻¹) hD h₁ rfl
  have h₄ := log_max_le (by positivity : 0 < (n:ℝ)⁻¹) hD h₂ rfl
  have h₅ := Real.log_le_sub_one_of_pos (by linarith : 0 < 1+D)
  change |Real.log (max _ ‖u‖) - Real.log (max _ ‖v‖)| ≤ D
  exact abs_le.mpr ⟨by linarith,by linarith⟩

private theorem abs_clip_le {n : ℕ} (hn : 0 < n) {E : ℝ} (hE : 0 ≤ E)
    {u v : ℂ} (hv : v ≠ 0) (he : ‖u-v‖ ≤ E*(n:ℝ)⁻¹) :
    |clip n u| ≤ |Real.log ‖v‖| + Real.log (1+E) := by
  have ha : 0 < (n:ℝ)⁻¹ := by positivity
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have ha' : (n:ℝ)⁻¹ ≤ 1 := by simpa using (inv_le_one₀ (by positivity : (0:ℝ)<n)).mpr hn'
  have hu := log_max_le ha hE he rfl
  have he' : ‖v-u‖ ≤ E*(n:ℝ)⁻¹ := by simpa [norm_sub_rev] using he
  have hl := log_max_le ha hE he' rfl
  have hc : |clip n v| ≤ |Real.log ‖v‖| := by
    by_cases h : (n:ℝ)⁻¹ ≤ ‖v‖
    · simp [clip,max_eq_right h]
    · have hv' := norm_pos_iff.mpr hv
      have hlv := Real.log_le_log hv' (le_of_not_ge h)
      have hla := Real.log_nonpos ha.le ha'
      simp only [clip, max_eq_left (le_of_not_ge h), abs_of_nonpos hla,
        abs_of_nonpos (hlv.trans hla)]
      linarith
  change |Real.log (max (n:ℝ)⁻¹ ‖v‖)| ≤ _ at hc
  unfold clip
  exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log (max (n:ℝ)⁻¹ ‖v‖))],
    by linarith [le_abs_self (Real.log (max (n:ℝ)⁻¹ ‖v‖))]⟩

private theorem sampleTag_le {f : ℝ → ℂ} {C : ℝ} {p : ℕ} (hC : 0 ≤ C)
    (hmod : LocalPolynomialLipschitz f C p) {S : ℕ → ℝ → ℂ} {n : ℕ} (hn : 0 < n)
    (hs : ∀ y, |y| ≤ (n:ℝ)+1 → ‖f y-S n y‖ ≤ (1/2:ℝ)^n)
    {x : ℝ} (hx : x ∈ Ico (-(n:ℝ)) n) :
    ‖S n (node n (index n x)) - f x‖ ≤ (1+C*(2+|x|)^p)*(n:ℝ)⁻¹ := by
  set y := node n (index n x)
  have hc := (index_cell hn hx).2
  have hy : y ≤ x := hc.1
  have hy' : x < y + (n:ℝ)⁻¹ := by simpa only [node_dist] using hc.2
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hi : (n:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hn'
  have hd : |y-x| ≤ (n:ℝ)⁻¹ := by rw [abs_of_nonpos (sub_nonpos.mpr hy)]; linarith
  have hyl : -(n:ℝ) ≤ y := by
    dsimp only [y,node]
    linarith [show 0 ≤ (index n x:ℝ)/(n:ℝ) by positivity]
  have ht := hs y (abs_le.mpr ⟨by linarith,by linarith [hx.2]⟩)
  have hu : (n:ℝ) ≤ (2:ℝ)^n := by
    exact_mod_cast (Nat.lt_pow_self (by decide : 1<2) (n := n)).le
  have hdyadic : (1/2:ℝ)^n ≤ (n:ℝ)⁻¹ := by
    rw [one_div,inv_pow]
    exact inv_anti₀ (by positivity) hu
  have hm := (hmod x y (hd.trans hi)).trans
    (mul_le_mul_of_nonneg_left hd (mul_nonneg hC (pow_nonneg (by positivity) _)))
  calc ‖S n y-f x‖ ≤ ‖S n y-f y‖+‖f y-f x‖ := by simpa only [dist_eq_norm] using dist_triangle (S n y) (f y) (f x)
    _ ≤ _ := by rw [norm_sub_rev (S n y)]; linarith [ht.trans hdyadic]

private theorem near_tag_tendsto {f : ℝ → ℂ} {C : ℝ} {p : ℕ} (hC : 0 ≤ C)
    (hmod : LocalPolynomialLipschitz f C p) (S : ℕ → ℝ → ℂ)
    (hs : ∀ᶠ n : ℕ in atTop, ∀ y, |y| ≤ (n:ℝ)+1 → ‖f y-S n y‖ ≤ (1/2:ℝ)^n)
    (x : ℝ) :
    Tendsto (fun n ↦ S n (node n (index n x))) atTop (𝓝 (f x)) := by
  have hpos : ∀ᶠ n : ℕ in atTop, x ∈ Ico (-(n:ℝ)) n := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop |x|)] with n h
    exact ⟨by linarith [neg_abs_le x],by linarith [le_abs_self x]⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
  · filter_upwards [hs,hpos,eventually_gt_atTop (0:ℕ)] with n hn hx hn'
    exact sampleTag_le hC hmod hn' hn hx
  · simpa only [mul_zero,one_div] using
      (tendsto_one_div_atTop_nhds_zero_nat.const_mul (1+C*(2+|x|)^p))

/-- Finite sums of left-endpoint samples of the clipped logarithm converge under any finite
measure with a finite logarithmic moment. The tag values may be inexact. -/
theorem tendsto_statistic (μ : Measure ℝ) [IsFiniteMeasure μ] (f : ℝ → ℂ) (S : ℕ → ℝ → ℂ)
    {C : ℝ} {p : ℕ} (hC : 0 ≤ C) (hmod : LocalPolynomialLipschitz f C p)
    (hs : ∀ᶠ n : ℕ in atTop, ∀ y, |y| ≤ (n:ℝ)+1 → ‖f y-S n y‖ ≤ (1/2:ℝ)^n)
    (hne : ∀ᵐ x ∂μ, f x ≠ 0) (hlog : Integrable (fun x ↦ Real.log ‖f x‖) μ)
    (hmom : Integrable (fun x : ℝ ↦ Real.log (2+|x|)) μ) :
    Tendsto (statistic μ S) atTop (𝓝 (∫ x, Real.log ‖f x‖ ∂μ)) := by
  let B (x : ℝ) := |Real.log ‖f x‖| + Real.log (2+C) + (p:ℝ)*Real.log (2+|x|)
  have hB : Integrable B μ := ((hlog.abs.add (integrable_const _)).add (hmom.const_mul _))
  have hP (x : ℝ) : 0 ≤ Real.log (2+|x|) := Real.log_nonneg (by linarith [abs_nonneg x])
  have hBC : 0 ≤ Real.log (2+C) := Real.log_nonneg (by linarith)
  refine Tendsto.congr' (f₁ := fun n ↦ ∫ x, step S n x ∂μ) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    exact integral_step μ S hn
  apply tendsto_integral_filter_of_dominated_convergence B
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    exact (measurable_step hn S).aestronglyMeasurable
  · filter_upwards [hs,eventually_gt_atTop (0:ℕ)] with n h hn
    filter_upwards [hne] with x hxne
    by_cases hx : x ∈ Ico (-(n:ℝ)) n
    · rw [step,indicator_of_mem hx, Real.norm_eq_abs]
      have hE : 0 ≤ C*(2+|x|)^p := mul_nonneg hC (by positivity)
      have hu := abs_clip_le hn (by linarith : 0 ≤ 1+C*(2+|x|)^p) hxne
        (sampleTag_le hC hmod hn h hx)
      have hpow : 1 ≤ (2+|x|)^p := one_le_pow₀ (by linarith [abs_nonneg x])
      have hprod : 1+(1+C*(2+|x|)^p) ≤ (2+C)*(2+|x|)^p := by nlinarith
      have hmono := Real.log_le_log (by linarith : 0 < 1+(1+C*(2+|x|)^p)) hprod
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hmono
      dsimp only [B]
      linarith
    · rw [step,indicator_of_notMem hx,norm_zero]
      dsimp only [B]
      positivity [hP x]
  · exact hB
  · filter_upwards [hne] with x hx
    have hwin : ∀ᶠ n : ℕ in atTop, x ∈ Ico (-(n:ℝ)) n := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop |x|)] with n h
      exact ⟨by linarith [neg_abs_le x],by linarith [le_abs_self x]⟩
    have hi : Tendsto (fun n : ℕ ↦ (n:ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [one_div] using (show Tendsto (fun n : ℕ ↦ 1/(n:ℝ)) atTop (𝓝 0) from
        tendsto_one_div_atTop_nhds_zero_nat)
    have hg := hi.max (near_tag_tendsto hC hmod S hs x).norm
    rw [max_eq_right (norm_nonneg _)] at hg
    have hh := (Real.continuousAt_log (norm_ne_zero_iff.mpr hx)).tendsto.comp hg
    apply hh.congr'
    filter_upwards [hwin] with n hn
    simp [step,hn,clip]

end RiemannMasullo.LogQuadrature
