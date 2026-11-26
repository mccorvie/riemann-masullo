module

public import RiemannMasullo.ForMathlib.Analysis.Asymptotics.LogMeshRate
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

open Real

/-- A bound for the integrated tails of a real logarithm under its sampling measure. -/
def HasIntegratedLogTail (μ : Measure ℝ) (u : ℝ → ℝ) : Prop :=
  ∃ A > 0, ∃ c > 0, ∀ᶠ Y : ℝ in atTop,
    (∫ x in {x | Y ≤ |u x|}, |u x| ∂μ) ≤ A * exp (-c * √Y)

private theorem abs_log_sub_log_le_floor {a d x y : ℝ} (ha : 0 < a) (hd : 0 ≤ d)
    (hx : a ≤ x) (hy : a ≤ y) (hxy : x-y ≤ d) (hyx : y-x ≤ d) :
    |log x-log y| ≤ d/a := by
  have side {r s : ℝ} (hr : a ≤ r) (hs : a ≤ s) (hb : r-s ≤ d) :
      log r-log s ≤ d/a := by
    have hsp := ha.trans_le hs
    rw [← log_div (ha.trans_le hr).ne' hsp.ne']
    calc log (r/s) ≤ r/s-1 := log_le_sub_one_of_pos (div_pos (ha.trans_le hr) hsp)
      _ = (r-s)/s := by field_simp
      _ ≤ d/s := div_le_div_of_nonneg_right hb hsp.le
      _ ≤ d/a := div_le_div_of_nonneg_left hd ha hs
  exact abs_le.mpr ⟨by linarith [side hy hx hyx], side hx hy hxy⟩

private theorem clip_error_interior {n : ℕ} {q : ℝ} (hq : 4 ≤ q)
    (hn : exp (q^2) = n) {z v : ℂ} (hv : v ≠ 0) (hl : |log ‖v‖| ≤ q^2/4)
    (hd : ‖z-v‖ ≤ exp (-q^2/2)) : |clip n z - log ‖v‖| ≤ 2*exp (-q^2/4) := by
  have hn' : (n:ℝ)⁻¹ = exp (-(q^2)) := by rw [←hn,exp_neg]
  have hL : exp (-q^2/4) ≤ ‖v‖ := by
    rw [← exp_log (norm_pos_iff.mpr hv)]
    apply exp_monotone
    linarith [(abs_le.mp hl).1]
  have hsplit : 2 * exp (-q^2/2) ≤ exp (-q^2/4) := by
    have hh : 2 ≤ exp (q^2/4) := by nlinarith [add_one_le_exp (q^2/4),sq_nonneg (q-2)]
    have h := mul_le_mul_of_nonneg_right hh (exp_pos (-q^2/2)).le
    rw [←exp_add, show q^2/4+ -q^2/2 = -q^2/4 by ring] at h
    exact h
  have hinv : (n:ℝ)⁻¹ ≤ exp (-q^2/2) := by
    rw [hn']; exact exp_monotone (by nlinarith [sq_nonneg q])
  have norm₁ := (norm_sub_norm_le z v).trans hd
  have norm₂ := (norm_sub_norm_le v z).trans (by rwa [norm_sub_rev] : ‖v-z‖ ≤ exp (-q^2/2))
  have hz : exp (-q^2/4)/2 ≤ ‖z‖ := by linarith
  rw [clip,max_eq_right (by linarith : (n:ℝ)⁻¹ ≤ ‖z‖)]
  calc
    |log ‖z‖-log ‖v‖| ≤ exp (-q^2/2) / (exp (-q^2/4)/2) :=
      abs_log_sub_log_le_floor (by positivity) (exp_pos _).le hz
        (by linarith [exp_pos (-q^2/4)]) norm₁ norm₂
    _ = 2*exp (-q^2/4) := by
      have hh : exp (-q^2/4) * exp (-q^2/4) = exp (-q^2/2) := by
        rw [←exp_add]; congr 1; ring
      apply (div_eq_iff (by positivity)).2
      rw [← hh]
      ring

private theorem step_abs_le_log {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq : 4 ≤ q)
    (hnq : q^2 = log n) {f : ℝ → ℂ} {C : ℝ} {p : ℕ} (hC : 0 ≤ C)
    (hmod : LocalPolynomialLipschitz f C p) {S : ℕ → ℝ → ℂ}
    (hs : ∀ y, |y| ≤ (n:ℝ)+1 → ‖f y-S n y‖ ≤ (1/2:ℝ)^n)
    {x : ℝ} (hne : f x ≠ 0) :
    |step S n x| ≤ |log ‖f x‖| + (log (2+C)+2*p)*q^2 := by
  have hn0 : 0 < n := by omega
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hln := log_nonneg (show 1 ≤ 2+C by linarith)
  have hq1 : 1 ≤ q^2 := by nlinarith [sq_nonneg (q-1)]
  by_cases hx : x ∈ Ico (-(n:ℝ)) n
  · have h := abs_clip_le hn0 (by positivity : 0 ≤ 1+C*(2+|x|)^p) hne
      (sampleTag_le hC hmod hn0 hs hx)
    rw [step,indicator_of_mem hx]
    refine h.trans (add_le_add le_rfl ?_)
    have hx' : |x| ≤ n := abs_le.mpr ⟨hx.1,hx.2.le⟩
    have hp' := pow_le_pow_left₀ (by positivity : 0 ≤ 2+|x|)
      (by linarith : 2+|x| ≤ 2+n) p
    have hsize : 2+C*(2+|x|)^p ≤ (2+C)*(2+n)^p := by
      have hpn := one_le_pow₀ (show 1 ≤ 2+(n:ℝ) by linarith) (n:=p)
      nlinarith [mul_le_mul_of_nonneg_left hp' hC]
    have hsq : 2+(n:ℝ) ≤ (n:ℝ)^2 := by nlinarith [sq_nonneg ((n:ℝ)-2)]
    have hlog := log_le_log (by positivity : 0 < 2+(n:ℝ)) hsq
    rw [log_pow,←hnq] at hlog
    have hbig := log_le_log (by positivity : 0 < 2+C*(2+|x|)^p) hsize
    rw [log_mul (by positivity) (by positivity),log_pow] at hbig
    have hp := Nat.cast_nonneg (α:=ℝ) p
    rw [show 1+(1+C*(2+|x|)^p) = 2+C*(2+|x|)^p by ring]
    norm_num at hlog
    nlinarith [mul_le_mul_of_nonneg_left hlog hp,mul_le_mul_of_nonneg_left hq1 hln]
  · rw [step,indicator_of_notMem hx, abs_zero]
    positivity

private theorem integrable_step_rate (μ : Measure ℝ) [IsFiniteMeasure μ]
    (S : ℕ → ℝ → ℂ) {n : ℕ} (hn : 0 < n) : Integrable (step S n) μ := by
  simp_rw [funext (step_eq_cell_sum hn S)]
  exact integrable_finsetSum _ fun j _ ↦ (integrable_const _).indicator measurableSet_Ico

/-- A one-mesh error estimate. The interior term uses the polynomial derivative bound,
the second term measures exceptional continuum values, and the last term measures height. -/
private theorem abs_statistic_sub_integral_mesh (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ℝ → ℂ} {C : ℝ} {p : ℕ} (hC : 0 ≤ C) (hmod : LocalPolynomialLipschitz f C p)
    (S : ℕ → ℝ → ℂ) {n : ℕ} (hn : 2 ≤ n)
    (hs : ∀ y, |y| ≤ (n:ℝ)+1 → ‖f y-S n y‖ ≤ (1/2:ℝ)^n)
    (hne : ∀ᵐ x ∂μ, f x ≠ 0) (hm : Measurable f)
    (hu : Integrable (fun x ↦ log ‖f x‖) μ)
    (hheight : Integrable (fun x : ℝ ↦ √(1+|x|)) μ)
    {q : ℝ} (hq : 4 ≤ q) (hnq : q^2 = log n)
    (hpoly : 1+C*(2+exp q)^p ≤ exp (q^2/2)) :
    let A := log (2+C)+2*p
    let u := fun x ↦ log ‖f x‖
    |statistic μ S n - ∫ x, u x ∂μ| ≤ 2*exp (-q^2/4) +
      (2+4*A)*(∫ x in {x | q^2/4 ≤ |u x|}, |u x| ∂μ) +
      ((A+1)*(q^2 * exp (-q/2))) * (∫ x : ℝ, √(1+|x|) ∂μ) := by
  intro A u
  let B := {x : ℝ | q^2/4 ≤ |u x|}
  have hB : MeasurableSet B := measurableSet_le measurable_const (continuous_abs.measurable.comp hm.norm.log)
  have hn0 : 0 < n := by omega
  have hEn : exp (q^2) = n := by rw [hnq,exp_log (by positivity)]
  have hq0 : 0 ≤ q := by linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity [log_nonneg (show 1 ≤ 2+C by linarith)]
  let m₀ := 2*exp (-q^2/4)
  let m₁ := 2+4*A
  let m₂ := (A+1)*(q^2*exp (-q/2))
  let tail := B.indicator (fun x ↦ |u x|)
  have ht : Integrable tail μ := hu.abs.indicator hB
  have hi := integrable_step_rate μ S hn0
  have h₀ : Integrable (fun _ : ℝ ↦ m₀) μ := integrable_const _
  have h₁ := ht.const_mul m₁
  have h₂ := hheight.const_mul m₂
  have hb : ∀ᵐ x ∂μ, |step S n x-u x| ≤ m₀+m₁*tail x+m₂*√(1+|x|) := by
    filter_upwards [hne] with x hx
    have hbasic := step_abs_le_log hn hq hnq hC hmod hs hx
    change |step S n x| ≤ |u x|+A*q^2 at hbasic
    have hrough := abs_sub (step S n x) (u x)
    have hm0 : 0 ≤ m₀ := by dsimp [m₀]; positivity
    have hm2x : 0 ≤ m₂*√(1+|x|) := by dsimp [m₂]; positivity
    by_cases hbad : x ∈ B
    · have hh : q^2/4 ≤ |u x| := hbad
      have htail : tail x = |u x| := indicator_of_mem hbad _
      rw [htail]
      dsimp only [m₁]
      nlinarith [mul_le_mul_of_nonneg_left hh hA]
    · have hh : |u x| ≤ q^2/4 := (lt_of_not_ge (show ¬ q^2/4 ≤ |u x| from hbad)).le
      have htail : tail x = 0 := indicator_of_notMem hbad _
      rw [htail,mul_zero,add_zero]
      by_cases hc : |x| ≤ exp q
      · have hex : exp q < (n:ℝ) := by
          rw [←hEn]; apply exp_lt_exp.mpr; nlinarith [sq_nonneg (q-2)]
        have hM : x ∈ Ico (-(n:ℝ)) n :=
          ⟨by linarith [neg_abs_le x],by linarith [le_abs_self x]⟩
        have hv := sampleTag_le hC hmod hn0 hs hM
        have hh' : 1+C*(2+|x|)^p ≤ exp (q^2/2) :=
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (by linarith : 2+|x| ≤ 2+exp q) p) hC)).trans hpoly
        have hinv : (n:ℝ)⁻¹ = exp (-(q^2)) := by rw [←hEn,exp_neg]
        have hnoise : ‖S n (node n (index n x))-f x‖ ≤ exp (-q^2/2) := by
          refine hv.trans ((mul_le_mul_of_nonneg_right hh' (by positivity)).trans_eq ?_)
          rw [hinv, ←exp_add]; congr 1; ring
        rw [step,indicator_of_mem hM]
        exact (clip_error_interior hq hEn hx hh hnoise).trans (by linarith)
      · have hsr := Real.sqrt_le_sqrt (show exp q ≤ 1+|x| by linarith [lt_of_not_ge hc])
        rw [←exp_half] at hsr
        have hsq : 1 ≤ exp (-q/2)*√(1+|x|) := calc
          1 = exp (-q/2)*exp (q/2) := by rw [←exp_add, show -q/2+q/2=0 by ring, exp_zero]
          _ ≤ _ := mul_le_mul_of_nonneg_left hsr (exp_pos _).le
        have hmt : (A+1)*q^2 ≤ m₂*√(1+|x|) := by
          have xx := mul_le_mul_of_nonneg_left hsq
            (show 0 ≤ (A+1)*q^2 by positivity)
          dsimp [m₂]; nlinarith
        nlinarith [sq_nonneg q]
  calc
    |statistic μ S n - ∫ x, u x ∂μ| = |∫ x, step S n x - u x ∂μ| := by
      rw [integral_sub hi hu,integral_step μ S hn0]
    _ ≤ ∫ x, |step S n x-u x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, m₀+m₁*tail x + m₂*√(1+|x|) ∂μ :=
      integral_mono_ae (hi.sub hu).abs ((h₀.add h₁).add h₂) hb
    _ = _ := by
      have h01 : Integrable (fun x : ℝ ↦ m₀+m₁*tail x) μ := h₀.add h₁
      rw [integral_add h01 h₂,integral_add h₀ h₁,
        integral_const_mul m₁ tail,integral_const_mul m₂ (fun x : ℝ ↦ √(1+|x|))]
      simp [m₀,m₁,m₂,tail,B,integral_indicator hB]

/-- A logarithmic tail bound and a polynomial derivative modulus give a root-log rate for
the exact clipped mesh, allowing exponentially accurate input tables. -/
theorem hasRootLogRate_statistic (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : ℝ → ℂ) (S : ℕ → ℝ → ℂ) {C : ℝ} {p : ℕ}
    (hC : 0 ≤ C) (hmod : LocalPolynomialLipschitz f C p)
    (hs : ∀ᶠ n : ℕ in atTop, ∀ y, |y| ≤ (n:ℝ)+1 → ‖f y-S n y‖ ≤ (1/2:ℝ)^n)
    (hne : ∀ᵐ x ∂μ, f x ≠ 0) (hm : Measurable f)
    (hu : Integrable (fun x ↦ log ‖f x‖) μ) (hheight : Integrable (fun x : ℝ ↦ √(1+|x|)) μ)
    (htail : HasIntegratedLogTail μ (fun x ↦ log ‖f x‖)) :
    HasRootLogRate (fun n ↦ statistic μ S n - ∫ x, log ‖f x‖ ∂μ) := by
  obtain ⟨K,hK,c,hc,hbound⟩ := htail
  obtain ⟨Y,hY⟩ := eventually_atTop.mp hbound
  let A := log (2+C)+2*p
  let M := ∫ x : ℝ, √(1+|x|) ∂μ
  let k := min (c/2) (1/4)
  have hk : 0 < k := lt_min (by positivity) (by norm_num)
  have hA : 0 ≤ A := by dsimp [A]; positivity [log_nonneg (show 1 ≤ 2+C by linarith)]
  have hM : 0 ≤ M := integral_nonneg fun _ ↦ sqrt_nonneg _
  refine ⟨2+(2+4*A)*K+32*(A+1)*M,by positivity,k,hk,?_⟩
  filter_upwards [hs,eventually_ge_atTop (2:ℕ),
    meshScale_atTop.eventually_ge_atTop (4+4*|Y|),
    meshScale_atTop.eventually (eventually_mesh_polynomial C hC p)] with n hn hN hqY hpoly
  let q := meshScale n
  have hq : 4 ≤ q := by change 4+4*|Y| ≤ q at hqY; linarith [abs_nonneg Y]
  have hq0 : 0 ≤ q := by linarith
  have hqSq := meshScale_sq (show 0 < n by omega)
  have hraw := abs_statistic_sub_integral_mesh μ hC hmod S hN hn hne hm hu hheight hq hqSq hpoly
  have hsmall : Y ≤ q^2/4 := by
    change 4+4*|Y| ≤ q at hqY
    nlinarith [le_abs_self Y,sq_nonneg (q-2)]
  have hbad := hY _ hsmall
  rw [show q^2/4 = (q/2)^2 by ring, Real.sqrt_sq (by positivity)] at hbad
  have hkc : k ≤ c/2 := min_le_left _ _
  have hk4 : k ≤ 1/4 := min_le_right _ _
  have h₀ : exp (-q^2/4) ≤ exp (-k*q) := by
    apply exp_monotone
    nlinarith [mul_le_mul_of_nonneg_right hk4 hq0,sq_nonneg (q-2)]
  have h₁ : exp (-c*(q/2)) ≤ exp (-k*q) := by
    apply exp_monotone
    nlinarith [mul_le_mul_of_nonneg_right hkc hq0]
  have h₂ : exp (-q/4) ≤ exp (-k*q) := by
    apply exp_monotone
    nlinarith [mul_le_mul_of_nonneg_right hk4 hq0]
  have hbad' : (∫ x in {x | q^2/4 ≤ |log ‖f x‖|}, |log ‖f x‖| ∂μ) ≤ K*exp (-k*q) := by
    rw [show q^2/4 = (q/2)^2 by ring]
    exact hbad.trans (mul_le_mul_of_nonneg_left h₁ hK.le)
  have hh := (mesh_height_damping hq0).trans (mul_le_mul_of_nonneg_left h₂ (by norm_num))
  calc
    |statistic μ S n - ∫ x, log ‖f x‖ ∂μ| ≤ 2*exp (-q^2/4) +
      (2+4*A)*(∫ x in {x | q^2/4 ≤ |log ‖f x‖|}, |log ‖f x‖| ∂μ) +
      ((A+1)*(q^2*exp (-q/2)))*M := hraw
    _ ≤ 2*exp (-k*q)+(2+4*A)*(K*exp (-k*q))+((A+1)*(32*exp (-k*q)))*M := by
      gcongr
    _ = _ := by dsimp only [q]; ring

end RiemannMasullo.LogQuadrature
