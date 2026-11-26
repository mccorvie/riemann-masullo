module

public import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.RealDeriv

/-! # The prime number theorem against a compact smooth weight

Abel summation transfers the usual Chebyshev prime number theorem to a dilating interval.
In logarithmic coordinates the resulting limit is the exponential moment of the profile.
-/

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

namespace RiemannMasullo

private def primeLogWeight (n : ℕ) : ℂ := if n.Prime then Real.log n else 0

private theorem sum_primeLogWeight (t : ℝ) :
    ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, primeLogWeight n = (Chebyshev.theta t : ℂ) := by
  rw [Chebyshev.theta_eq_sum_Icc, Complex.ofReal_sum, Finset.sum_filter]
  rfl

private theorem scaledTheta_tendsto (t : ℝ) (ht : 0 < t) :
    Tendsto (fun X : ℝ ↦ ((Chebyshev.theta (X * t) / X : ℝ) : ℂ)) atTop (𝓝 (t : ℂ)) := by
  have h := (Chebyshev.tendsto_theta_div_atTop.comp (tendsto_id.atTop_mul_const ht)).mul_const t
  apply Complex.continuous_ofReal.continuousAt.tendsto.comp
  convert h using 1
  · funext X
    dsimp
    by_cases hx : X = 0
    · simp [hx]
    · field_simp
  · rw [one_mul]

private theorem scaledTheta_integral_tendsto {a b : ℝ} (ha : 0 < a) {K : ℝ → ℂ}
    (hK : ContinuousOn K (Icc a b)) :
    Tendsto (fun X : ℝ ↦ ∫ t in Ioc a b, K t * ((Chebyshev.theta (X * t) / X : ℝ) : ℂ)) atTop
      (𝓝 (∫ t in Ioc a b, K t * (t : ℂ))) := by
  have hr : AEStronglyMeasurable K (volume.restrict (Ioc a b)) :=
    (hK.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  apply tendsto_integral_filter_of_dominated_convergence (fun t : ℝ ↦ ‖K t‖ * (Real.log 4 * b))
  · apply Eventually.of_forall
    intro X
    exact hr.mul (Complex.continuous_ofReal.measurable.comp
      ((Chebyshev.theta_mono.measurable.comp
        (measurable_const.mul measurable_id)).div_const X)).aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Chebyshev.theta_nonneg _) hX.le)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (div_le_iff₀ hX).mpr
    have hbnd := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht.2 hX.le)
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
    apply (Chebyshev.theta_le_log4_mul_x (mul_nonneg hX.le (ha.trans ht.1).le)).trans
    linarith only [hbnd]
  · exact (hK.norm.mul continuousOn_const).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht
    exact (scaledTheta_tendsto t (ha.trans ht.1)).const_mul _

private theorem scaled_primeLog_abel {a b X : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hX : 0 < X)
    {K K' : ℝ → ℂ} (hK : ∀ t ∈ Icc a b, HasDerivAt K (K' t) t)
    (hc : ContinuousOn K' (Icc a b)) :
    (∑ n ∈ Finset.Ioc ⌊X * a⌋₊ ⌊X * b⌋₊, K (n / X) * primeLogWeight n) / (X : ℂ) =
      K b * ((Chebyshev.theta (X * b) / X : ℝ) : ℂ) - K a * ((Chebyshev.theta (X * a) / X : ℝ) : ℂ) -
        ∫ t in Ioc a b, K' t * ((Chebyshev.theta (X * t) / X : ℝ) : ℂ) := by
  let f := fun u : ℝ ↦ K (u / X)
  have hm {u : ℝ} (hu : u ∈ Icc (X * a) (X * b)) : u / X ∈ Icc a b := by
    constructor
    · exact (le_div_iff₀ hX).mpr (by linarith [hu.1])
    · exact (div_le_iff₀ hX).mpr (by linarith [hu.2])
  have hd (u : ℝ) (hu : u ∈ Icc (X * a) (X * b)) : HasDerivAt f (K' (u / X) / (X : ℂ)) u := by
    have hh := (hK _ (hm hu)).scomp u ((hasDerivAt_id u).div_const X)
    simpa [f, Function.comp_def, Complex.real_smul, div_eq_mul_inv, mul_comm] using hh
  have hc' : ContinuousOn (deriv f) (Icc (X * a) (X * b)) := by
    refine ((hc.comp (continuous_id.div_const X).continuousOn (fun _ h ↦ hm h)).div_const (X : ℂ)).congr ?_
    intro u hu
    exact (hd _ hu).deriv
  have h := sum_mul_eq_sub_sub_integral_mul primeLogWeight (mul_nonneg hX.le ha)
    (mul_le_mul_of_nonneg_left hab hX.le) (fun u hu ↦ (hd u hu).differentiableAt) hc'.integrableOn_Icc
  have hsub : (∫ u in Ioc (X * a) (X * b), deriv f u * (Chebyshev.theta u : ℂ)) =
      ∫ t in Ioc a b, K' t * (Chebyshev.theta (X * t) : ℂ) := by
    rw [← intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hab hX.le),
      ← intervalIntegral.integral_of_le hab]
    have ht := intervalIntegral.integral_comp_mul_left (a := a) (b := b)
      (fun u : ℝ ↦ K' (u / X) * (Chebyshev.theta u : ℂ)) hX.ne'
    simp only [mul_div_cancel_left₀ _ hX.ne', Complex.real_smul, Complex.ofReal_inv] at ht
    rw [ht, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [(hd u (by rwa [Set.uIcc_of_le (mul_le_mul_of_nonneg_left hab hX.le)] at hu)).deriv]
    ring
  simp_rw [sum_primeLogWeight] at h
  rw [h, hsub]
  dsimp [f]
  rw [mul_div_cancel_left₀ _ hX.ne', mul_div_cancel_left₀ _ hX.ne']
  simp_rw [Complex.ofReal_div]
  rw [show (∫ t in Ioc a b, K' t * ((Chebyshev.theta (X * t) : ℂ) / (X : ℂ))) =
    (∫ t in Ioc a b, K' t * (Chebyshev.theta (X * t) : ℂ)) / (X : ℂ) by
      rw [← integral_div]; congr 1; funext t; ring]
  ring

/-- On a positive dilation interval, the normalized sum of a C¹ test against the
logarithms of the primes converges to its integral. -/
public theorem tendsto_scaled_sum_prime_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {K K' : ℝ → ℂ}
    (hK : ∀ t ∈ Icc a b, HasDerivAt K (K' t) t) (hc : ContinuousOn K' (Icc a b)) :
    Tendsto (fun X : ℝ ↦ (∑ p ∈ (Finset.Ioc ⌊X * a⌋₊ ⌊X * b⌋₊).filter Nat.Prime,
      K (p / X) * (Real.log p : ℂ)) / (X : ℂ)) atTop (𝓝 (∫ t in a..b, K t)) := by
  have hcont : ContinuousOn K (Icc a b) := fun x hx ↦ (hK x hx).continuousAt.continuousWithinAt
  have hU : uIcc a b = Icc a b := uIcc_of_le hab
  have hkc : ContinuousOn K (uIcc a b) := hU.symm ▸ hcont
  have hdc : ContinuousOn K' (uIcc a b) := hU.symm ▸ hc
  have hx : (∫ t in a..b, K t) = K b * (b : ℂ) - K a * (a : ℂ) - ∫ t in Ioc a b, K' t * (t : ℂ) := by
    have hh := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt (u := K) (v := Complex.ofReal)
      (u' := K') (v' := fun _ ↦ 1) hkc Complex.continuous_ofReal.continuousOn
      (fun t ht ↦ hK t (by simpa [min_eq_left hab, max_eq_right hab] using Ioo_subset_Icc_self ht))
      (fun t _ ↦ by simpa using (hasDerivAt_id t).ofReal_comp)
      hdc.intervalIntegrable (continuous_const.intervalIntegrable a b)
    simp only [mul_one] at hh
    rw [intervalIntegral.integral_add (f := fun t : ℝ ↦ K' t * (t : ℂ)) (g := K) (μ := volume)
      (hdc.mul Complex.continuous_ofReal.continuousOn).intervalIntegrable hkc.intervalIntegrable] at hh
    rw [← intervalIntegral.integral_of_le hab]
    linear_combination hh
  rw [hx]
  apply ((((scaledTheta_tendsto b (ha.trans_le hab)).const_mul (K b)).sub
    ((scaledTheta_tendsto a ha).const_mul (K a))).sub (scaledTheta_integral_tendsto ha hc)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  rw [← scaled_primeLog_abel ha.le hab hX hK hc, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : n.Prime <;> simp [primeLogWeight, hn]

private def primePowerKernel (H : ℝ → ℂ) (k σ t : ℝ) : ℂ :=
  (Real.exp (-σ * Real.log t) : ℂ) * H (k * Real.log t)

private theorem primePowerKernel_contDiffOn {H : ℝ → ℂ} (hH : ContDiff ℝ 1 H) (k σ : ℝ) :
    ContDiffOn ℝ 1 (primePowerKernel H k σ) (Ioi 0) := by
  have hl : ContDiffOn ℝ 1 Real.log (Ioi 0) := fun x hx ↦
    (Real.contDiffAt_log.mpr (ne_of_gt hx)).contDiffWithinAt
  exact (Complex.ofRealCLM.contDiff.comp_contDiffOn (Real.contDiff_exp.comp_contDiffOn
    (contDiffOn_const.mul hl))).mul (hH.comp_contDiffOn (contDiffOn_const.mul hl))

private theorem primePowerKernel_integral {H : ℝ → ℂ} (hH : ContDiff ℝ 1 H)
    {a b : ℝ} (hab : a ≤ b) (hs : Function.support H ⊆ Ioc a b)
    {k : ℝ} (hk : 0 < k) (σ : ℝ) :
    (∫ t in Real.exp (a / k)..Real.exp (b / k), primePowerKernel H k σ t) =
      (∫ v : ℝ, H v * (Real.exp ((1 - σ) / k * v) : ℂ)) / (k : ℂ) := by
  let f := fun v : ℝ ↦ Real.exp (v / k)
  let f' := fun v : ℝ ↦ Real.exp (v / k) / k
  have hd (v : ℝ) : HasDerivAt f (f' v) v := by
    simpa [f, f', div_eq_mul_inv] using (((hasDerivAt_id v).div_const k).exp)
  have hc : Continuous f' := (Real.continuous_exp.comp (continuous_id.div_const k)).div_const k
  have hK := (primePowerKernel_contDiffOn hH k σ).continuousOn.mono
    (show f '' uIcc a b ⊆ Ioi 0 by rintro t ⟨v, _, rfl⟩; exact Real.exp_pos _)
  have hsub := intervalIntegral.integral_deriv_smul_comp' (a := a) (b := b)
    (fun v _ ↦ hd v) hc.continuousOn hK
  change (∫ t in f a..f b, _) = _
  rw [← hsub, ← integral_div]
  let L := fun v : ℝ ↦ H v * (Real.exp ((1 - σ) / k * v) : ℂ) / (k : ℂ)
  have hz (v : ℝ) (hv : v ∉ Ioc a b) : L v = 0 := by
    have hzero : H v = 0 := by by_contra hn; exact hv (hs hn)
    simp [L, hzero]
  change _ = ∫ v : ℝ, L v
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz, ← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp [f, f', primePowerKernel, L]
  rw [Real.log_exp, mul_div_cancel₀ v hk.ne']
  have he : Real.exp (v / k) * Real.exp (-σ * (v / k)) =
      Real.exp ((1 - σ) / k * v) := by rw [← Real.exp_add]; congr 1; ring
  rw [Complex.ofReal_div, ← he, Complex.ofReal_mul]
  ring

private theorem primePowerKernel_tendsto {H : ℝ → ℂ} (hH : ContDiff ℝ 1 H)
    {a b : ℝ} (hab : a ≤ b) (hs : Function.support H ⊆ Ioc a b)
    {k : ℝ} (hk : 0 < k) (σ : ℝ) :
    Tendsto (fun X : ℝ ↦
      (∑ p ∈ (Finset.Ioc ⌊X * Real.exp (a / k)⌋₊ ⌊X * Real.exp (b / k)⌋₊).filter Nat.Prime,
        primePowerKernel H k σ (p / X) * (Real.log p : ℂ)) / (X : ℂ)) atTop
      (𝓝 ((∫ v : ℝ, H v * (Real.exp ((1 - σ) / k * v) : ℂ)) / (k : ℂ))) := by
  have hI : Icc (Real.exp (a / k)) (Real.exp (b / k)) ⊆ Ioi 0 :=
    fun x hx ↦ (Real.exp_pos _).trans_le hx.1
  have hc := primePowerKernel_contDiffOn hH k σ
  rw [← primePowerKernel_integral hH hab hs hk σ]
  refine tendsto_scaled_sum_prime_log (K' := deriv (primePowerKernel H k σ)) (Real.exp_pos _) (Real.exp_le_exp.mpr (by gcongr)) ?_ ?_
  · intro t ht
    exact ((hc.differentiableOn (by decide) _ (hI ht)).differentiableAt
      (isOpen_Ioi.mem_nhds (hI ht))).hasDerivAt
  · exact (hc.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hI

private theorem primePowerSum_eq_finite {H : ℝ → ℂ} {a b : ℝ}
    (hs : Function.support H ⊆ Ioc a b) {k : ℝ} (hk : 0 < k) (σ y : ℝ) :
    (∑' p : ℕ, if p.Prime then (Real.log p : ℂ) * (Real.exp (-σ * Real.log p) : ℂ) *
      H (k * Real.log p - y) else 0) =
    ∑ p ∈ (Finset.Ioc ⌊Real.exp ((y + a) / k)⌋₊ ⌊Real.exp ((y + b) / k)⌋₊).filter Nat.Prime,
      (Real.log p : ℂ) * (Real.exp (-σ * Real.log p) : ℂ) * H (k * Real.log p - y) := by
  classical
  let s := (Finset.Ioc ⌊Real.exp ((y + a) / k)⌋₊ ⌊Real.exp ((y + b) / k)⌋₊).filter Nat.Prime
  rw [tsum_eq_sum (s := s)]
  · exact Finset.sum_congr rfl fun p hp ↦ ite_eq_left (Finset.mem_filter.mp hp).2
  · intro p hps
    split_ifs with hprime
    · have hp : (0 : ℝ) < p := by exact_mod_cast hprime.pos
      have hz : H (k * Real.log p - y) = 0 := by
        by_contra hn
        have hI := hs hn
        apply hps
        refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨(Nat.floor_lt (Real.exp_pos _).le).mpr ?_,
          Nat.le_floor ?_⟩, hprime⟩
        · rw [← Real.log_lt_log_iff (Real.exp_pos _) hp, Real.log_exp]
          exact (div_lt_iff₀ hk).mpr (by nlinarith [hI.1])
        · rw [← Real.log_le_log_iff hp (Real.exp_pos _), Real.log_exp]
          exact (le_div_iff₀ hk).mpr (by nlinarith [hI.2])
      rw [hz, mul_zero]
    · rfl

/-- The prime number theorem for a compactly supported C¹ profile in logarithmic coordinates.
For index `k > 0` and weight `p ^ (-σ)`, the normalized sum over ordinary primes converges
to the exponential moment at `(1 - σ) / k`, divided by `k`. -/
public theorem tendsto_smoothed_primePower_sum {H : ℝ → ℂ}
    (hH : ContDiff ℝ 1 H) (hHc : HasCompactSupport H) {k : ℝ} (hk : 0 < k) (σ : ℝ) :
    Tendsto (fun y : ℝ ↦ (Real.exp ((σ - 1) / k * y) : ℂ) *
      ∑' p : ℕ, if p.Prime then (Real.log p : ℂ) * (Real.exp (-σ * Real.log p) : ℂ) *
        H (k * Real.log p - y) else 0) atTop
      (𝓝 ((∫ v : ℝ, H v * (Real.exp ((1 - σ) / k * v) : ℂ)) / (k : ℂ))) := by
  obtain ⟨l, hl⟩ := hHc.bddBelow
  obtain ⟨u, hu⟩ := hHc.bddAbove
  let a := min l u - 1
  let b := max l u + 1
  have hab : a ≤ b := by dsimp [a, b]; linarith [min_le_left l u, le_max_left l u]
  have hs : Function.support H ⊆ Ioc a b := by
    intro t ht
    have ht' := subset_tsupport H ht
    constructor
    · dsimp [a]; linarith [hl ht', min_le_left l u]
    · dsimp [b]; linarith [hu ht', le_max_right l u]
  have ht : Tendsto (fun y : ℝ ↦ Real.exp (y / k)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const hk)
  apply ((primePowerKernel_tendsto hH hab hs hk σ).comp ht).congr
  intro y
  dsimp [Function.comp_def]
  have hew (c : ℝ) : Real.exp ((y + c) / k) = Real.exp (y / k) * Real.exp (c / k) := by
    rw [add_div, Real.exp_add]
  rw [primePowerSum_eq_finite hs hk, hew a, hew b, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Finset.mem_filter.mp hp).2.pos
  unfold primePowerKernel
  rw [Real.log_div hp0.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [show k * (Real.log p - y / k) = k * Real.log p - y by field_simp]
  have he : Real.exp (-σ * (Real.log p - y / k)) / Real.exp (y / k) =
      Real.exp ((σ - 1) / k * y) * Real.exp (-σ * Real.log p) := by
    rw [← Real.exp_sub, ← Real.exp_add]
    congr 1
    ring
  have hce := congrArg Complex.ofReal he
  simp only [Complex.ofReal_div, Complex.ofReal_mul] at hce
  linear_combination (norm := ring_nf) ((Real.log p : ℂ) * H (k * Real.log p - y)) * hce

end RiemannMasullo
