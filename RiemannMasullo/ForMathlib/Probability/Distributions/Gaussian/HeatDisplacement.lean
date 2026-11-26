module

public import Mathlib.Analysis.Calculus.Taylor
public import RiemannMasullo.ForMathlib.Probability.Distributions.Gaussian.Window
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Gaussian averaging of a through-one trace at sandwich time twice the heat parameter. -/

@[expose] public noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Real
open scoped Topology NNReal ENNReal

namespace RiemannMasullo.ThroughOneStability

private theorem heatGaussian_map (τ : ℝ≥0) :
    (gaussianReal 0 2).map (fun x : ℝ ↦ sqrt τ * x) = gaussianReal 0 (τ + τ) := by
  have hv : NNReal.mk ((sqrt (τ : ℝ)) ^ 2) (sq_nonneg _) = τ :=
    Subtype.ext (Real.sq_sqrt τ.coe_nonneg)
  simpa only [mul_zero, hv, mul_two] using gaussianReal_map_const_mul (μ := 0) (v := 2) (sqrt τ)

private theorem quadraticTaylorData (W : ℝ → ℝ)
    (hW : ContDiff ℝ 2 W) (hK : HasCompactSupport W) :
    ∃ q : ℝ → ℝ, Continuous q ∧ q 0 = 0 ∧ (∃ K : ℝ, ∀ x, |q x| ≤ K) ∧
      ∀ x, W x = W 0 + deriv W 0 * x + (iteratedDeriv 2 W 0 / 2) * x^2 + x^2*q x := by
  let b := deriv W 0
  let c := iteratedDeriv 2 W 0 / 2
  let q (x : ℝ) := (W x - (W 0 + b*x + c*x^2))/x^2
  have ht (x : ℝ) : taylorWithinEval W 2 univ 0 x = W 0 + b*x + c*x^2 := by
    rw [taylorWithinEval_succ W 1 univ 0 x, taylorWithinEval_succ W 0 univ 0 x]
    norm_num [taylor_within_zero_eval, iteratedDerivWithin_univ, b, c, smul_eq_mul]
    ring
  have hqt : Tendsto q (𝓝 0) (𝓝 0) := by
    simpa only [q, ht, nhdsWithin_univ, sub_zero] using
      (Real.taylor_tendsto (x₀ := (0 : ℝ)) (n := 2) convex_univ (mem_univ _) hW.contDiffOn)
  have hq0 : q 0 = 0 := by simp [q]
  have hc : Continuous q := by
    refine continuous_iff_continuousAt.mpr fun x ↦ ?_
    rcases eq_or_ne x 0 with rfl | hx
    · simpa [ContinuousAt, hq0] using hqt
    · have hw : Continuous W := hW.continuous
      dsimp [q]
      fun_prop (disch := exact pow_ne_zero _ hx)
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuous hW.continuous
  obtain ⟨N,hN⟩ := (isCompact_Icc (a := (-1:ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨q, hc, hq0, ⟨max N (M+|W 0|+|b|+|c|), fun x ↦ ?_⟩, fun x ↦ ?_⟩
  · by_cases hx : |x| ≤ 1
    · exact (hN x (abs_le.mp hx)).trans (le_max_left _ _)
    · have hx1 : 1 ≤ |x| := (lt_of_not_ge hx).le
      have hn : x ≠ 0 := by rintro rfl; norm_num at hx
      have he : q x = ((W x - W 0)/x - b)/x - c := by
        dsimp [q]
        field_simp
        ring
      have hd (a : ℝ) : |a/x| ≤ |a| := by
        rw [abs_div]
        exact div_le_self (abs_nonneg _) hx1
      apply le_trans _ (le_max_right _ _)
      rw [he]
      calc
        _ ≤ |((W x-W 0)/x-b)/x|+|c| := abs_sub _ _
        _ ≤ |(W x-W 0)/x-b|+|c| := by linarith only [hd ((W x-W 0)/x-b)]
        _ ≤ |(W x-W 0)/x|+|b|+|c| := by gcongr; exact abs_sub _ _
        _ ≤ |W x-W 0|+|b|+|c| := by linarith only [hd (W x-W 0)]
        _ ≤ |W x|+|W 0|+|b|+|c| := by gcongr; exact abs_sub _ _
        _ ≤ M+|W 0|+|b|+|c| := by gcongr; exact hM x
  · change W x = W 0 + b*x + c*x^2 + x^2*q x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · dsimp [q]
      field_simp
      ring

private theorem heatReference_integrable_sq : Integrable (fun x : ℝ ↦ x^2) (gaussianReal 0 2) :=
  (memLp_two_iff_integrable_sq measurable_id'.aestronglyMeasurable).mp (memLp_id_gaussianReal 2)

private theorem heatReference_secondMoment : (∫ x : ℝ, x^2 ∂gaussianReal 0 2) = 2 := by
  have hv := variance_eq_integral (μ := gaussianReal 0 2) measurable_id'.aemeasurable
  rw [variance_fun_id_gaussianReal] at hv
  simpa using hv.symm

/-- Exact at zero heat. The coefficient of the first-order change at variance `τ+τ`
is the ordinary second derivative of the log-coordinate profile. -/
theorem exists_gaussian_heat_secondOrder_error (W : ℝ → ℝ)
    (hW : ContDiff ℝ 2 W) (hK : HasCompactSupport W) :
    ∃ e : ℝ≥0 → ℝ, Tendsto e (𝓝 0) (𝓝 0) ∧ ∀ τ,
      (∫ z : ℝ, W (-z) ∂gaussianReal 0 (τ+τ)) - W 0 =
        (τ:ℝ) * (iteratedDeriv 2 W 0 + e τ) := by
  obtain ⟨q, hq, hq0, ⟨K,hKq⟩, hTaylor⟩ := quadraticTaylorData W hW hK
  let ν := gaussianReal 0 2
  let Q (τ : ℝ≥0) (x : ℝ) := x^2*q (-(sqrt τ*x))
  have hc (τ : ℝ≥0) : Continuous (Q τ) :=
    (continuous_id.pow 2).mul (hq.comp ((continuous_const.mul continuous_id).neg))
  have hb (τ : ℝ≥0) (x : ℝ) : ‖Q τ x‖ ≤ K*x^2 := by
    simp only [Q, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg x)]
    exact (mul_le_mul_of_nonneg_left (hKq _) (sq_nonneg x)).trans_eq (mul_comm _ _)
  have hQi (τ : ℝ≥0) : Integrable (Q τ) ν :=
    (heatReference_integrable_sq.const_mul K).mono' (hc τ).aestronglyMeasurable (.of_forall (hb τ))
  refine ⟨fun τ ↦ ∫ x, Q τ x ∂ν, ?_, fun τ ↦ ?_⟩
  · have hl (x : ℝ) : Tendsto (fun τ : ℝ≥0 ↦ Q τ x) (𝓝 0) (𝓝 0) := by
      have hh : Continuous (fun τ : ℝ≥0 ↦ Q τ x) :=
        continuous_const.mul (hq.comp ((Real.continuous_sqrt.comp NNReal.continuous_coe).mul continuous_const).neg)
      simpa [ContinuousAt,Q,hq0] using hh.continuousAt (x := 0)
    have hh := tendsto_integral_filter_of_dominated_convergence (μ := ν)
      (f := fun _ : ℝ ↦ (0:ℝ)) (fun x : ℝ ↦ K*x^2)
      (.of_forall fun τ ↦ (hc τ).aestronglyMeasurable)
      (.of_forall fun τ ↦ .of_forall (hb τ)) (heatReference_integrable_sq.const_mul K) (.of_forall hl)
    simpa using hh
  · rw [← heatGaussian_map τ, integral_map (f := fun z : ℝ ↦ W (-z)) (measurable_const_mul _).aemeasurable
        (hW.continuous.comp continuous_neg).aestronglyMeasurable]
    let b := -deriv W 0 * sqrt τ
    let c := (iteratedDeriv 2 W 0 / 2) * (τ:ℝ)
    have he (x : ℝ) : W (-(sqrt τ*x)) = W 0 + b*x + c*x^2 + (τ:ℝ)*Q τ x := by
      calc
        _ = _ := hTaylor (-(sqrt τ*x))
        _ = _ := by dsimp [b,c,Q]; rw [neg_sq, mul_pow, Real.sq_sqrt τ.coe_nonneg]; ring
    simp_rw [he]
    have h₁ : Integrable (fun x : ℝ ↦ x) ν := (memLp_id_gaussianReal (μ := 0) (v := 2) 1).integrable le_rfl
    have h₂ : Integrable (fun x : ℝ ↦ x^2) ν := heatReference_integrable_sq
    rw [integral_add (f := fun x : ℝ ↦ W 0+b*x+c*x^2) (g := fun x ↦ (τ:ℝ)*Q τ x) (((integrable_const _).add (h₁.const_mul b)).add (h₂.const_mul c)) ((hQi τ).const_mul _),
      integral_add (f := fun x : ℝ ↦ W 0+b*x) (g := fun x ↦ c*x^2) ((integrable_const _).add (h₁.const_mul b)) (h₂.const_mul c),
      integral_add (f := fun _ : ℝ ↦ W 0) (g := fun x ↦ b*x) (integrable_const _) (h₁.const_mul b)]
    simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
    have hmean : (∫ x : ℝ, x ∂ν) = 0 := by simp [ν]
    rw [integral_const_mul (μ := ν) b (fun x : ℝ ↦ x), hmean, show (∫ x : ℝ, x^2 ∂ν) = 2 from heatReference_secondMoment]
    dsimp [c]
    ring

private theorem heatReference_integrable_abs :
    Integrable (fun x : ℝ ↦ |x|) (gaussianReal 0 2) :=
  ((memLp_id_gaussianReal (μ := 0) (v := 2) 1).integrable le_rfl).norm

private theorem heatReference_integrable_fourth :
    Integrable (fun x : ℝ ↦ |x|^4) (gaussianReal 0 2) := by
  have h : MemLp id (4 : ℝ≥0∞) (gaussianReal 0 2) := memLp_id_gaussianReal 4
  exact h.integrable_norm_pow (p := 4) (by decide)

/-- At heat time `τ` the local contribution costs `O(√τ)` and the complement costs
`O(H τ²/d⁴)`.  Both estimates include the atom at zero heat. -/
theorem gaussian_heat_window_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (τ : ℝ≥0) (E : ℝ → V) {d K H : ℝ} (hd : 0 < d) (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hm : AEStronglyMeasurable E (gaussianReal 0 (τ+τ)))
    (hlocal : ∀ z, |z| < d → ‖E z‖ ≤ K*|z|)
    (hglobal : ∀ z, ‖E z‖ ≤ H) :
    ‖∫ z, E z ∂gaussianReal 0 (τ+τ)‖ ≤
      K*sqrt τ*(∫ x : ℝ, |x| ∂gaussianReal 0 2) +
      ((H/d^4)*(τ:ℝ)^2)*(∫ x : ℝ, |x|^4 ∂gaussianReal 0 2) := by
  let s := sqrt (τ:ℝ)
  have hs : 0 ≤ s := sqrt_nonneg _
  have hs2 : s^2 = (τ:ℝ) := sq_sqrt τ.coe_nonneg
  have hs4 : s^4 = (τ:ℝ)^2 := by rw [← hs2]; ring
  have hden := div_nonneg hH (pow_nonneg hd.le 4)
  have hp (x : ℝ) : ‖E (s*x)‖ ≤ (K*s)*|x| + ((H/d^4)*(τ:ℝ)^2)*|x|^4 := by
    rcases lt_or_ge |s*x| d with hx | hx
    · refine (hlocal _ hx).trans ?_
      rw [abs_mul, abs_of_nonneg hs, ← mul_assoc]
      exact le_add_of_nonneg_right (by positivity)
    · have hpow : d^4 ≤ (τ:ℝ)^2*|x|^4 := by
        calc
          d^4 ≤ |s*x|^4 := pow_le_pow_left₀ hd.le hx 4
          _ = _ := by rw [abs_mul,abs_of_nonneg hs,mul_pow,hs4]
      calc
        _ ≤ H := hglobal _
        _ = (H/d^4)*d^4 := (div_mul_cancel₀ H (pow_ne_zero 4 hd.ne')).symm
        _ ≤ (H/d^4)*((τ:ℝ)^2*|x|^4) := mul_le_mul_of_nonneg_left hpow hden
        _ ≤ _ := by rw [← mul_assoc]; exact le_add_of_nonneg_left (by positivity)
  rw [← heatGaussian_map τ] at hm ⊢
  rw [integral_map (measurable_const_mul _).aemeasurable hm]
  have h₁ := heatReference_integrable_abs.const_mul (K*s)
  have h₄ := heatReference_integrable_fourth.const_mul ((H/d^4)*(τ:ℝ)^2)
  calc
    _ ≤ ∫ x : ℝ, (K*s)*|x|+((H/d^4)*(τ:ℝ)^2)*|x|^4 ∂gaussianReal 0 2 :=
      norm_integral_le_of_norm_le (h₁.add h₄) (.of_forall hp)
    _ = _ := by rw [integral_add h₁ h₄, integral_const_mul, integral_const_mul]

/-- A finite limit of `τ log R` suffices for the averaged phase remainder. The result
only requires `R ≥ 1` eventually and allows arbitrary zero-heat terms. -/
theorem tendsto_gaussian_heat_window_remainder {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {l : Filter ι} (τ : ι → ℝ≥0) (R : ι → ℝ) (E : ι → ℝ → V) {κ d K M : ℝ}
    (hτ : Tendsto τ l (𝓝 0)) (hκ : Tendsto (fun i ↦ (τ i:ℝ)*log (R i)) l (𝓝 κ))
    (hR : ∀ᶠ i in l, 1 ≤ R i) (hd : 0 < d) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hm : ∀ᶠ i in l, AEStronglyMeasurable (E i) (gaussianReal 0 (τ i+τ i)))
    (hlocal : ∀ᶠ i in l, ∀ z, |z| < d → ‖E i z‖ ≤ K*|z|)
    (hglobal : ∀ᶠ i in l, ∀ z, ‖E i z‖ ≤ M*(1+log (R i))) :
    Tendsto (fun i ↦ ∫ z, E i z ∂gaussianReal 0 (τ i+τ i)) l (𝓝 0) := by
  have ht : Tendsto (fun i ↦ (τ i:ℝ)) l (𝓝 0) := by
    simpa only [Function.comp_def, NNReal.coe_zero] using (NNReal.continuous_coe.tendsto 0).comp hτ
  have hs : Tendsto (fun i ↦ sqrt (τ i:ℝ)) l (𝓝 0) := by
    simpa only [Function.comp_def, sqrt_zero] using (continuous_sqrt.tendsto 0).comp ht
  have hl : Tendsto (fun i ↦ (τ i:ℝ)*(1+log (R i))) l (𝓝 κ) := by
    simpa only [mul_add,mul_one,zero_add] using ht.add hκ
  have htail : Tendsto (fun i ↦ (M*(1+log (R i))/d^4)*(τ i:ℝ)^2) l (𝓝 0) := by
    have hh := (ht.mul hl).const_mul (M/d^4)
    convert hh using 1
    · ext i
      ring
    · simp
  apply squeeze_zero_norm' (a := fun i ↦ K*sqrt (τ i:ℝ)*(∫ x : ℝ, |x| ∂gaussianReal 0 2) +
      ((M*(1+log (R i))/d^4)*(τ i:ℝ)^2)*(∫ x : ℝ, |x|^4 ∂gaussianReal 0 2))
  · filter_upwards [hR,hm,hlocal,hglobal] with i hi hme hlo hgl
    apply gaussian_heat_window_bound (τ i) (E i) hd hK _ hme hlo hgl
    exact mul_nonneg hM (by linarith [log_nonneg hi])
  · simpa using ((hs.const_mul K).mul_const (∫ x : ℝ, |x| ∂gaussianReal 0 2)).add
      (htail.mul_const (∫ x : ℝ, |x|^4 ∂gaussianReal 0 2))

/-- The log-divergent coefficient contributes `κ W″(0)`, including schedules which
visit heat time zero. -/
theorem tendsto_gaussian_heat_log_coefficient {ι : Type*} {l : Filter ι}
    (W : ℝ → ℝ) (hW : ContDiff ℝ 2 W) (hK : HasCompactSupport W)
    (τ : ι → ℝ≥0) (R : ι → ℝ) {κ : ℝ} (hτ : Tendsto τ l (𝓝 0))
    (hκ : Tendsto (fun i ↦ (τ i:ℝ)*log (R i)) l (𝓝 κ)) :
    Tendsto (fun i ↦ ((∫ z, W (-z) ∂gaussianReal 0 (τ i+τ i))-W 0)*log (R i))
      l (𝓝 (κ*iteratedDeriv 2 W 0)) := by
  obtain ⟨e,he,heq⟩ := exists_gaussian_heat_secondOrder_error W hW hK
  have hc := hκ.mul ((he.comp hτ).const_add (iteratedDeriv 2 W 0))
  simp only [Function.comp_def, add_zero] at hc
  refine hc.congr' (.of_forall fun i ↦ ?_)
  dsimp only
  rw [heq (τ i)]
  ring

/-- Combines the cold-to-shifted estimate on one identity window with a uniform
logarithmic envelope for the raw shifted trace. The cold scalar equals the zero shift
by taking `z=0` in the local estimate. -/
theorem tendsto_gaussian_heat_trace_displacement {ι : Type*} {l : Filter ι}
    (W : ℝ → ℝ) (hW : ContDiff ℝ 2 W) (hKW : HasCompactSupport W)
    (τ : ι → ℝ≥0) (R C : ι → ℝ) (F : ι → ℝ → ℝ) {κ d K M : ℝ}
    (hτ : Tendsto τ l (𝓝 0)) (hκ : Tendsto (fun i ↦ (τ i:ℝ)*log (R i)) l (𝓝 κ))
    (hR : ∀ᶠ i in l, 1 ≤ R i) (hd : 0 < d) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hm : ∀ᶠ i in l, AEStronglyMeasurable (F i) (gaussianReal 0 (τ i+τ i)))
    (hlocal : ∀ᶠ i in l, ∀ z, |z| < d →
      |F i z-C i-(W (-z)-W 0)*log (R i)| ≤ K*|z|)
    (hglobal : ∀ᶠ i in l, ∀ z, |F i z| ≤ M*(1+log (R i))) :
    Tendsto (fun i ↦ (∫ z, F i z ∂gaussianReal 0 (τ i+τ i))-C i)
      l (𝓝 (κ*iteratedDeriv 2 W 0)) := by
  let E (i : ι) (z : ℝ) := F i z-C i-(W (-z)-W 0)*log (R i)
  obtain ⟨P,hP⟩ := hKW.exists_bound_of_continuous hW.continuous
  have hP0 : 0 ≤ P := (norm_nonneg _).trans (hP 0)
  have hw : Continuous (fun z : ℝ ↦ W (-z)) := hW.continuous.comp continuous_neg
  have hEm : ∀ᶠ i in l, AEStronglyMeasurable (E i) (gaussianReal 0 (τ i+τ i)) := by
    filter_upwards [hm] with i hi
    exact (hi.sub aestronglyMeasurable_const).sub
      ((hw.aestronglyMeasurable.sub aestronglyMeasurable_const).mul aestronglyMeasurable_const)
  have hEl : ∀ᶠ i in l, ∀ z, |z| < d → ‖E i z‖ ≤ K*|z| := hlocal
  have hEg : ∀ᶠ i in l, ∀ z, ‖E i z‖ ≤ (2*M+2*P)*(1+log (R i)) := by
    filter_upwards [hR,hlocal,hglobal] with i hRi hli hgi
    have hp : 0 ≤ log (R i) := log_nonneg hRi
    have hg : |F i 0-C i| ≤ 0 := by simpa using hli 0 (by simpa using hd)
    have hC : F i 0 = C i := sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hg (abs_nonneg _)))
    intro z
    change |F i z-C i-(W (-z)-W 0)*log (R i)| ≤ _
    have hlocalW : |W (-z)-W 0| ≤ P+P := (abs_sub _ _).trans (add_le_add (hP _) (hP 0))
    calc
      _ ≤ |F i z-C i| + |(W (-z)-W 0)*log (R i)| := abs_sub _ _
      _ ≤ (|F i z|+|C i|)+(P+P)*log (R i) := by
        rw [abs_mul,abs_of_nonneg hp]
        exact add_le_add (abs_sub _ _) (mul_le_mul_of_nonneg_right hlocalW hp)
      _ ≤ _ := by rw [← hC]; nlinarith only [hgi z,hgi 0,hP0]
  have hEr := tendsto_gaussian_heat_window_remainder τ R E hτ hκ hR hd hK
    (show 0 ≤ 2*M+2*P by positivity) hEm hEl hEg
  have hcoef := tendsto_gaussian_heat_log_coefficient W hW hKW τ R hτ hκ
  have hboth := hEr.add hcoef
  rw [zero_add] at hboth
  apply hboth.congr'
  filter_upwards [hm,hglobal] with i hmi hgi
  let μ := gaussianReal 0 (τ i+τ i)
  have hFi : Integrable (F i) μ :=
    (integrable_const (M*(1+log (R i)))).mono' hmi (.of_forall (hgi ·))
  have hWi : Integrable (fun z : ℝ ↦ W (-z)) μ :=
    (integrable_const P).mono' hw.aestronglyMeasurable (.of_forall fun z ↦ hP (-z))
  have hΔi : Integrable (fun z : ℝ ↦ (W (-z)-W 0)*log (R i)) μ :=
    (hWi.sub (integrable_const _)).mul_const _
  dsimp only [E]
  rw [integral_sub (f := fun z ↦ F i z-C i) (g := fun z ↦ (W (-z)-W 0)*log (R i))
      (hFi.sub (integrable_const _)) hΔi,
    integral_sub hFi (integrable_const _), integral_mul_const,
    integral_sub hWi (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- A radial test carried by a compact positive window has compact support in log
coordinates, and its log curvature at the identity has both radial derivative terms. -/
theorem radialProfile_log_data (w : ℝ → ℝ) (hw : ContDiff ℝ 2 w) {a b : ℝ} (ha : 0 < a)
    (hsupp : ∀ r, r ∉ Icc a b → w r = 0) :
    ContDiff ℝ 2 (fun y : ℝ ↦ w (exp y)) ∧ HasCompactSupport (fun y : ℝ ↦ w (exp y)) ∧
    iteratedDeriv 2 (fun y : ℝ ↦ w (exp y)) 0 = deriv w 1 + iteratedDeriv 2 w 1 := by
  refine ⟨hw.comp contDiff_exp, HasCompactSupport.intro (K := Icc (log a) (log b)) isCompact_Icc ?_, ?_⟩
  · intro y hy
    apply hsupp
    intro h
    exact hy ⟨(log_le_iff_le_exp ha).mpr h.1, (le_log_iff_exp_le ((exp_pos y).trans_le h.2)).mpr h.2⟩
  · have hw₁ := hw.differentiable (by norm_num)
    have hd : deriv (fun y : ℝ ↦ w (exp y)) = fun y ↦ deriv w (exp y)*exp y := by
      funext y
      exact ((hw₁ (exp y)).hasDerivAt.comp y (hasDerivAt_exp y)).deriv
    have htwo (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
      rw [iteratedDeriv_succ (n := 1),iteratedDeriv_one]
    have hh := (((hw.differentiable_deriv_two (exp 0)).hasDerivAt.comp 0
      (hasDerivAt_exp 0)).mul (hasDerivAt_exp 0)).deriv
    simp only [htwo,hd]
    simpa only [Pi.mul_def,Function.comp_def,exp_zero,mul_one,add_comm] using hh

end RiemannMasullo.ThroughOneStability
