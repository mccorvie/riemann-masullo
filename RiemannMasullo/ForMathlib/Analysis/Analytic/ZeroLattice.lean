module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.DiscreteSubset

/-!
# Detecting analytic zero orders with consecutive lattice samples

A forward comparison between consecutive magnitudes on the grid of mesh `1 / n²`
accepts `m * n + O(1)` points near a zero of order `m`, uniformly in the grid phase.
For a continuous compactly supported weight, the prescribed finite sums converge to
its sum over the zeros with their full analytic orders.
-/

public noncomputable section

open Filter Set Topology
open scoped NNReal
namespace RiemannMasullo.AnalyticLattice

private def gridInterval (θ a b : ℝ) : Finset ℤ :=
  Finset.Ioo ⌊a - θ⌋ ⌈b - θ⌉

private lemma mem_gridInterval {θ a b : ℝ} {k : ℤ} :
    k ∈ gridInterval θ a b ↔ a < (k : ℝ) + θ ∧ (k : ℝ) + θ < b := by
  simp only [gridInterval, Finset.mem_Ioo, Int.floor_lt, Int.lt_ceil]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

private lemma card_gridInterval {θ a b : ℝ} (h : a < b) :
    b - a - 1 ≤ ((gridInterval θ a b).card : ℝ) ∧
      ((gridInterval θ a b).card : ℝ) ≤ b - a + 1 := by
  have hi := Int.card_Ioo_of_lt _ _ (Int.floor_lt_ceil_of_lt (sub_lt_sub_right h θ))
  have hr : ((gridInterval θ a b).card : ℝ) =
      (⌈b - θ⌉ : ℝ) - (⌊a - θ⌋ : ℝ) - 1 := by exact_mod_cast hi
  rw [hr]
  have hf := Int.floor_le (a - θ)
  have hf' := Int.lt_floor_add_one (a - θ)
  have hc := Int.le_ceil (b - θ)
  have hc' := Int.ceil_lt_add_one (b - θ)
  constructor <;> linarith

/-- Indices strictly inside the radius at which the consecutive sample magnitudes
satisfy the forward threshold. The phase translates the grid in units of one mesh. -/
def accepted (f : ℝ → ℂ) (γ r : ℝ) (n : ℕ) (θ : ℝ) : Finset ℤ := by
  classical
  exact (gridInterval θ (-r * (n : ℝ) ^ 2) (r * (n : ℝ) ^ 2)).filter fun k ↦
    ((n : ℝ) + 1) * ‖f (γ + ((k : ℝ) + θ) / (n : ℝ) ^ 2)‖ <
      (n : ℝ) * ‖f (γ + (((k : ℝ) + θ) + 1) / (n : ℝ) ^ 2)‖

/-- The geometric interval and strict magnitude test defining an accepted index. -/
lemma mem_accepted_iff {f : ℝ → ℂ} {γ r θ : ℝ} {n : ℕ} {k : ℤ} :
    k ∈ accepted f γ r n θ ↔
      (-r * (n : ℝ) ^ 2 < (k : ℝ) + θ ∧ (k : ℝ) + θ < r * (n : ℝ) ^ 2) ∧
      ((n : ℝ) + 1) * ‖f (γ + ((k : ℝ) + θ) / (n : ℝ) ^ 2)‖ <
        n * ‖f (γ + ((k : ℝ) + θ + 1) / (n : ℝ) ^ 2)‖ := by
  classical
  rw [accepted, Finset.mem_filter, mem_gridInterval]

private lemma log_step {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ≤ Real.log ((x + 1) / x) ∧ Real.log ((x + 1) / x) ≤ 1 / x := by
  have hx' : 0 < x + 1 := by positivity
  have hp := div_pos hx' hx
  constructor
  · convert Real.one_sub_inv_le_log_of_pos hp using 1
    field_simp
    ring
  · convert Real.log_le_sub_one_of_pos hp using 1
    field_simp
    ring

private lemma factor_threshold {n p q U V : ℝ} (m : ℕ) (hn : 0 < n)
    (hp : 0 < p) (hq : 0 < q) (hU : 0 < U) (hV : 0 < V) :
    (n + 1) * p ^ m * U < n * q ^ m * V ↔
      Real.log ((n + 1) / n) <
        (m : ℝ) * Real.log (q / p) + (Real.log V - Real.log U) := by
  have h₁ : 0 < n + 1 := by positivity
  rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_div h₁.ne' hn.ne',
    Real.log_div hq.ne' hp.ne']
  simp only [Real.log_mul (by positivity : (n + 1) * p ^ m ≠ 0) hU.ne',
    Real.log_mul (by positivity : n * q ^ m ≠ 0) hV.ne',
    Real.log_mul h₁.ne' (pow_ne_zero _ hp.ne'), Real.log_mul hn.ne' (pow_ne_zero _ hq.ne'),
    Real.log_pow]
  constructor <;> intro h <;> linarith

private lemma threshold_sandwich {C n y U V : ℝ} {m : ℕ} (hm : 0 < m)
    (hC : 0 ≤ C) (hn : 2 * (C + 1) ≤ n) (hU : 0 < U) (hV : 0 < V)
    (hΔ : |Real.log V - Real.log U| ≤ C / n ^ 2) :
    (0 < y ∧ y < m * n - (2 * m * (C + 1) + 2) →
      (n + 1) * |y| ^ m * U < n * |y + 1| ^ m * V) ∧
    ((n + 1) * |y| ^ m * U < n * |y + 1| ^ m * V →
      -1 < y ∧ y < m * n + (2 * m * (C + 1) + 2)) := by
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : 0 < n := by linarith
  have hn₂ := sq_pos_of_pos hn'
  have hn₁ : 0 < n + 1 := by positivity
  obtain ⟨hΔ₁, hΔ₂⟩ := abs_le.mp hΔ
  obtain ⟨ha₁, ha₂⟩ := log_step hn'
  have hD : 0 < n - (C + 1) := by linarith
  have hfloor : (n - (C + 1)) / n ^ 2 ≤ 1 / (n + 1) - C / n ^ 2 := by
    rw [le_sub_iff_add_le, ← add_div, div_le_div_iff₀ hn₂ hn₁]
    nlinarith
  constructor
  · rintro ⟨hy, hy'⟩
    have hy₁ : 0 < y + 1 := by positivity
    rw [abs_of_pos hy, abs_of_pos hy₁, factor_threshold m hn' hy hy₁ hU hV]
    have hsmall : y + 1 < m * (n - C) := by
      nlinarith [mul_nonneg hmp.le hC]
    have hmul := mul_lt_mul_of_pos_right hsmall (by linarith : 0 < n + C)
    have hbound : (1 / n + C / n ^ 2) < (m : ℝ) / (y + 1) := by
      calc
        1 / n + C / n ^ 2 = (n + C) / n ^ 2 := by field_simp
        _ < _ := (div_lt_div_iff₀ hn₂ hy₁).2 (by
          nlinarith [mul_nonneg hmp.le (sq_nonneg C)])
    have hylog := mul_le_mul_of_nonneg_left (log_step hy).1 hmp.le
    rw [← div_eq_mul_one_div] at hylog
    linarith
  · intro htest
    have hleft : -1 < y := by
      by_contra! hneg
      have hp : 0 < |y| := abs_pos.mpr (by linarith)
      by_cases hz : y + 1 = 0
      · rw [hz, abs_zero, zero_pow hm.ne'] at htest
        nlinarith [mul_pos (mul_pos hn₁ (pow_pos hp m)) hU]
      have hq := abs_pos.mpr hz
      have hle : |y + 1| ≤ |y| := by rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      have hlog := Real.log_nonpos (by positivity : 0 ≤ |y + 1| / |y|)
        ((div_le_one hp).2 hle)
      have htn := (factor_threshold m hn' hp hq hU hV).1 htest
      have ha := div_pos hD hn₂
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hmp.le hlog]
    refine ⟨hleft, ?_⟩
    by_cases hy : 0 < y
    · have hy₁ : 0 < y + 1 := by positivity
      rw [abs_of_pos hy, abs_of_pos hy₁, factor_threshold m hn' hy hy₁ hU hV] at htest
      have hylog := mul_le_mul_of_nonneg_left (log_step hy).2 hmp.le
      rw [← div_eq_mul_one_div] at hylog
      have hscale : (n - (C + 1)) / n ^ 2 < (m : ℝ) / y := by linarith
      have hcross := (div_lt_div_iff₀ hn₂ hy).1 hscale
      have hcap : (m : ℝ) * n ^ 2 ≤ (m * (n + 2 * (C + 1))) * (n - (C + 1)) := by
        have hpos := mul_nonneg (mul_nonneg hmp.le (by linarith : 0 ≤ C + 1))
          (by linarith : 0 ≤ n - 2 * (C + 1))
        nlinarith
      have hbound : y < m * (n + 2 * (C + 1)) :=
        (mul_lt_mul_iff_left₀ hD).mp (show y * (n - (C + 1)) <
            (m * (n + 2 * (C + 1))) * (n - (C + 1)) by nlinarith)
      linarith
    · nlinarith [mul_pos hmp hn', mul_nonneg hmp.le hC]

/-- For a supplied factorization on a ball and a Lipschitz log-magnitude of its nonzero
factor, a single explicit constant controls the count discrepancy and the accepted positions
for every phase. -/
theorem accepted_card_bound_of_factor {f u : ℝ → ℂ} {γ r R : ℝ} {m : ℕ} {K : ℝ≥0}
    (hm : 0 < m) (hr : 0 < r) (hrR : r ≤ R)
    (hfac : ∀ t ∈ Metric.ball γ (2 * R), f t = (t - γ) ^ m • u t ∧ u t ≠ 0)
    (hlip : LipschitzOnWith K (fun t ↦ Real.log ‖u t‖) (Metric.ball γ (2 * R))) :
    ∀ᶠ n : ℕ in atTop, ∀ θ : ℝ,
      |((accepted f γ r n θ).card : ℝ) - m * (n : ℝ)| ≤ 2 * m * (K + 1 : ℝ) + 4 ∧
      ∀ k ∈ accepted f γ r n θ, |(k : ℝ) + θ| ≤ m * (n : ℝ) + (2 * m * (K + 1 : ℝ) + 4) := by
  classical
  let B : ℝ := 2 * m * ((K : ℝ) + 1) + 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hmp : 0 < (m : ℝ) := by exact_mod_cast hm
  have large (b : ℝ) : ∀ᶠ n : ℕ in atTop, b < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop b)
  filter_upwards [large (2 * ((K : ℝ) + 1)), large (1 / r), large (m / r),
    large (B / m)] with n hn hstep hwidth hlen θ
  have hn' : 0 < (n : ℝ) := by linarith [K.coe_nonneg]
  have hn₂ := sq_pos_of_pos hn'
  have hone : 1 ≤ (n : ℝ) := by linarith [K.coe_nonneg]
  have hs : 1 / (n : ℝ) ^ 2 < r := by
    rw [div_lt_iff₀ hn₂]
    have hh := (div_lt_iff₀ hr).mp hstep
    nlinarith [mul_nonneg (mul_nonneg hr.le hn'.le) (sub_nonneg.mpr hone)]
  have hw : (m : ℝ) * n < r * (n : ℝ) ^ 2 := by
    have hh := mul_lt_mul_of_pos_right ((div_lt_iff₀ hr).mp hwidth) hn'
    nlinarith
  have hi : 0 < (m : ℝ) * n - B := by
    have hh := (div_lt_iff₀ hmp).mp hlen
    linarith
  let T (y : ℝ) := γ + y / (n : ℝ) ^ 2
  have atPoint (y : ℝ) (hy : -r * (n : ℝ) ^ 2 < y ∧ y < r * (n : ℝ) ^ 2) :
      T y ∈ Metric.ball γ (2 * R) ∧ T (y + 1) ∈ Metric.ball γ (2 * R) := by
    have h1 : -r < y / (n : ℝ) ^ 2 := (lt_div_iff₀ hn₂).2 hy.1
    have h2 : y / (n : ℝ) ^ 2 < r := (div_lt_iff₀ hn₂).2 hy.2
    simp only [T, Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, abs_lt, add_div]
    constructor <;> constructor <;> linarith [one_div_pos.mpr hn₂]
  have factorValue (y : ℝ) (hy : T y ∈ Metric.ball γ (2 * R)) :
      ‖f (T y)‖ = (|y| ^ m * ‖u (T y)‖) / ((n : ℝ) ^ 2) ^ m := by
    rw [(hfac _ hy).1, norm_smul, Real.norm_eq_abs, abs_pow]
    have hsub : T y - γ = y / (n : ℝ) ^ 2 := by dsimp [T]; ring
    rw [hsub, abs_div, abs_of_pos hn₂, div_pow]
    ring
  have localTest (y : ℝ) (hy : -r * (n : ℝ) ^ 2 < y ∧ y < r * (n : ℝ) ^ 2) :
      (0 < y ∧ y < (m : ℝ) * n - B → ((n : ℝ) + 1) * ‖f (T y)‖ < n * ‖f (T (y + 1))‖) ∧
      (((n : ℝ) + 1) * ‖f (T y)‖ < n * ‖f (T (y + 1))‖ → -1 < y ∧ y < (m : ℝ) * n + B) := by
    obtain ⟨h1, h2⟩ := atPoint y hy
    have hdiff := hlip.dist_le_mul (T (y + 1)) h2 (T y) h1
    have hdist : dist (T (y + 1)) (T y) = 1 / (n : ℝ) ^ 2 := by
      rw [Real.dist_eq]
      have hsub : T (y + 1) - T y = 1 / (n : ℝ) ^ 2 := by dsimp [T]; ring
      rw [hsub, abs_of_pos (one_div_pos.mpr hn₂)]
    rw [hdist, Real.dist_eq, ← div_eq_mul_one_div] at hdiff
    have hadd := threshold_sandwich (y := y) hm K.coe_nonneg hn.le (norm_pos_iff.mpr (hfac _ h1).2)
      (norm_pos_iff.mpr (hfac _ h2).2) hdiff
    have hnorm : ((n : ℝ) + 1) * ‖f (T y)‖ < n * ‖f (T (y + 1))‖ ↔
        ((n : ℝ) + 1) * |y| ^ m * ‖u (T y)‖ < n * |y + 1| ^ m * ‖u (T (y + 1))‖ := by
      rw [factorValue y h1, factorValue (y + 1) h2, ← mul_div_assoc, ← mul_div_assoc,
        div_lt_div_iff_of_pos_right (pow_pos hn₂ m)]
      simp only [mul_assoc]
    simpa only [hnorm, B] using (show
      (0 < y ∧ y < (m : ℝ) * n - B → _) ∧ (_ → -1 < y ∧ y < (m : ℝ) * n + B) from hadd)
  have hinner : gridInterval θ 0 (m * (n : ℝ) - B) ⊆ accepted f γ r n θ := by
    intro k hk
    obtain ⟨hl, hu⟩ := mem_gridInterval.mp hk
    have hp : -r * (n : ℝ) ^ 2 < (k : ℝ) + θ ∧ (k : ℝ) + θ < r * (n : ℝ) ^ 2 :=
      ⟨by nlinarith [mul_pos hr hn₂], by linarith⟩
    exact Finset.mem_filter.mpr ⟨mem_gridInterval.mpr hp, (localTest _ hp).1 ⟨hl, hu⟩⟩
  have houter : accepted f γ r n θ ⊆ gridInterval θ (-1) (m * (n : ℝ) + B) := by
    intro k hk
    obtain ⟨hk', ht⟩ := Finset.mem_filter.mp hk
    exact mem_gridInterval.mpr ((localTest _ (mem_gridInterval.mp hk')).2 ht)
  have hl := (card_gridInterval (θ := θ) hi).1
  have hu := (card_gridInterval (θ := θ) (a := -1) (b := m * (n : ℝ) + B) (by linarith [mul_pos hmp hn'])).2
  have hlc : ((gridInterval θ 0 (m * (n : ℝ) - B)).card : ℝ) ≤
      (accepted f γ r n θ).card := by exact_mod_cast Finset.card_le_card hinner
  have huc : ((accepted f γ r n θ).card : ℝ) ≤
      (gridInterval θ (-1) (m * (n : ℝ) + B)).card := by exact_mod_cast Finset.card_le_card houter
  refine ⟨abs_le.mpr ⟨?_, ?_⟩, ?_⟩
  · dsimp [B] at hl; linarith
  · dsimp [B] at hu; linarith
  · intro k hk
    obtain ⟨hneg, hpos⟩ := mem_gridInterval.mp (houter hk)
    dsimp [B] at hpos
    exact abs_le.mpr ⟨by nlinarith [mul_pos hmp hn', mul_nonneg hmp.le K.coe_nonneg], by linarith⟩

/-- Near a zero of finite positive analytic order, the number of forward comparisons that
pass differs from `m * n` by a bounded amount. The bound and enclosing radius work for every
grid phase and every sufficiently small fixed neighborhood. -/
theorem exists_accepted_card_bound {f : ℝ → ℂ} {γ : ℝ} {m : ℕ}
    (hf : AnalyticAt ℝ f γ) (hm : 0 < m) (ho : analyticOrderAt f γ = m) :
    ∃ R > 0, ∃ B > 0, ∀ r : ℝ, 0 < r → r ≤ R → ∀ᶠ n : ℕ in atTop, ∀ θ : ℝ,
      |((accepted f γ r n θ).card : ℝ) - m * (n : ℝ)| ≤ B ∧
        ∀ k ∈ accepted f γ r n θ, |(k : ℝ) + θ| ≤ m * (n : ℝ) + B := by
  obtain ⟨u, hu, hu0, hfu⟩ := hf.analyticOrderAt_eq_natCast.mp ho
  have hlog : ContDiffAt ℝ 1 (fun t ↦ Real.log ‖u t‖) γ :=
    (hu.contDiffAt.norm ℝ hu0).log (norm_ne_zero_iff.mpr hu0)
  obtain ⟨K, s, hs, hK⟩ := hlog.exists_lipschitzOnWith
  have hnear : ∀ᶠ t in 𝓝 γ, (f t = (t - γ) ^ m • u t ∧ u t ≠ 0) ∧ t ∈ s :=
    (hfu.and (hu.continuousAt.eventually_ne hu0)).and hs
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨d / 2, by positivity, 2 * m * ((K : ℝ) + 1) + 4, by positivity, ?_⟩
  intro r hr hrd
  have hEq : 2 * (d / 2) = d := by ring
  apply accepted_card_bound_of_factor (u := u) (K := K) hm hr hrd
  · simpa only [hEq] using fun t (ht : t ∈ Metric.ball γ d) ↦ (hball ht).1
  · rw [hEq]
    exact hK.mono (fun t ht ↦ (hball ht).2)

/-- On any sufficiently small fixed interval about a zero, a continuous signed weight tends to
its value at that zero times its order. The grid may be translated independently at each scale. -/
theorem tendsto_accepted_sum {f : ℝ → ℂ} {γ : ℝ} {m : ℕ}
    (hf : AnalyticAt ℝ f γ) (hm : 0 < m) (ho : analyticOrderAt f γ = m) :
    ∃ R > 0, ∀ r : ℝ, 0 < r → r ≤ R → ∀ (θ : ℕ → ℝ) (g : ℝ → ℝ), ContinuousAt g γ →
      Tendsto (fun n : ℕ ↦
        (∑ k ∈ accepted f γ r n (θ n), g (γ + ((k : ℝ) + θ n) / (n : ℝ) ^ 2)) / n)
        atTop (𝓝 ((m : ℝ) * g γ)) := by
  classical
  obtain ⟨R, hR, B, hB, hlocal⟩ := exists_accepted_card_bound hf hm ho
  refine ⟨R, hR, ?_⟩
  intro r hr hrR θ g hg
  let A (n : ℕ) := accepted f γ r n (θ n)
  let T (n : ℕ) (k : ℤ) := γ + ((k : ℝ) + θ n) / (n : ℝ) ^ 2
  have hA := (hlocal r hr hrR).mono (fun n h ↦ h (θ n))
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop 0)
  have hrecip : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hsmall : Tendsto (fun n : ℕ ↦ B * (1 / (n : ℝ))) atTop (𝓝 0) := by
    simpa using hrecip.const_mul B
  have hcard : Tendsto (fun n : ℕ ↦ ((A n).card : ℝ) / n) atTop (𝓝 (m : ℝ)) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [hA, hpos, hsmall.eventually_lt_const hε] with n h hn hεn
    rw [Real.dist_eq]
    calc
      |((A n).card : ℝ) / n - m| = |((A n).card : ℝ) - m * (n : ℝ)| / n := by
        rw [← abs_of_pos hn, ← abs_div, abs_of_pos hn]
        congr 1
        field_simp
      _ ≤ B / n := div_le_div_of_nonneg_right h.1 hn.le
      _ < ε := by rw [div_eq_mul_one_div]; exact hεn
  have hwidth : Tendsto (fun n : ℕ ↦ ((m : ℝ) * n + B) / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    have h := (hrecip.const_mul (m : ℝ)).add ((hrecip.pow 2).const_mul B)
    apply (show Tendsto _ _ (𝓝 (0 : ℝ)) from by simpa using h).congr'
    filter_upwards [hpos] with n hn
    field_simp
  have herr : Tendsto (fun n : ℕ ↦ (∑ k ∈ A n, (g (T n k) - g γ)) / n) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    have hm₁ : 0 < (m : ℝ) + 1 := by positivity
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hg (ε / (m + 1 : ℝ)) (div_pos hε hm₁)
    filter_upwards [hA, hwidth.eventually_lt_const hδ, hpos,
      hcard.eventually_lt_const (lt_add_one (m : ℝ))] with n h hδn hn hc
    have hclose (k : ℤ) (hk : k ∈ A n) : |g (T n k) - g γ| ≤ ε / (m + 1 : ℝ) := by
      apply le_of_lt
      change dist (g (T n k)) (g γ) < _
      apply hcont
      rw [Real.dist_eq]
      simp only [T, add_sub_cancel_left, abs_div, abs_of_pos (sq_pos_of_pos hn)]
      exact (div_le_div_of_nonneg_right (h.2 k hk) (sq_nonneg _)).trans_lt hδn
    simp only [Real.dist_eq, sub_zero, abs_div, abs_of_pos hn]
    calc
      |∑ k ∈ A n, (g (T n k) - g γ)| / n ≤ (∑ k ∈ A n, |g (T n k) - g γ|) / n :=
        div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hn.le
      _ ≤ (∑ _k ∈ A n, ε / (m + 1 : ℝ)) / n :=
        div_le_div_of_nonneg_right (Finset.sum_le_sum hclose) hn.le
      _ = (((A n).card : ℝ) / n) * (ε / (m + 1 : ℝ)) := by simp; ring
      _ < ((m : ℝ) + 1) * (ε / (m + 1 : ℝ)) := mul_lt_mul_of_pos_right hc (div_pos hε hm₁)
      _ = ε := by field_simp
  have h := herr.add (hcard.mul_const (g γ))
  apply (show Tendsto _ _ (𝓝 ((m : ℝ) * g γ)) from by simpa only [zero_add] using h).congr'
  exact Eventually.of_forall fun n ↦ by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, A, T]
    ring

private lemma zeroSetOnCompact_finite {f : ℝ → ℂ} {K : Set ℝ} (hK : IsCompact K)
    (hfa : ∀ x ∈ K, AnalyticAt ℝ f x) (hord : ∀ x ∈ K, analyticOrderAt f x ≠ ⊤) :
    (K ∩ {x | f x = 0}).Finite := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let Z := K ∩ {x | f x = 0}
  have hfK : ContinuousOn f K := fun x hx ↦ (hfa x hx).continuousAt.continuousWithinAt
  have hclosed : IsClosed {x : K | f x = 0} :=
    isClosed_eq (continuousOn_iff_continuous_domRestrict.mp hfK) continuous_const
  have hcompact : IsCompact Z := by
    convert hclosed.isCompact.image continuous_subtype_val using 1
    ext x
    simp [Z, and_comm]
  apply hcompact.finite
  rw [isDiscrete_iff_nhdsNE]
  intro x hx
  rw [inf_principal_eq_bot]
  have hne := (hfa x hx.1).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    (fun hv ↦ hord x hx.1 (analyticOrderAt_eq_top.mpr hv))
  exact hne.mono fun t ht hz ↦ ht hz.2

private lemma no_threshold_on_compact {f : ℝ → ℂ} {E : Set ℝ} (hE : IsCompact E)
    (hf : ∀ t ∈ E, AnalyticAt ℝ f t) (hne : ∀ t ∈ E, f t ≠ 0) :
    ∀ᶠ n : ℕ in atTop, ∀ t ∈ E,
      (n : ℝ) * ‖f (t + 1 / (n : ℝ) ^ 2)‖ ≤ ((n : ℝ) + 1) * ‖f t‖ := by
  classical
  apply hE.induction_on (p := fun D ↦ ∀ᶠ n : ℕ in atTop, ∀ t ∈ D,
    (n : ℝ) * ‖f (t + 1 / (n : ℝ) ^ 2)‖ ≤ ((n : ℝ) + 1) * ‖f t‖)
  · simp
  · exact fun _ _ hst ht ↦ ht.mono (fun n h t ht ↦ h t (hst ht))
  · intro s t hs ht
    filter_upwards [hs, ht] with n hn hn' x hx
    exact hx.elim (hn x) (hn' x)
  · intro a ha
    have hfa := hf a ha
    have hp := norm_pos_iff.mpr (hne a ha)
    have haC : ContDiffAt ℝ 1 f a := hfa.contDiffAt
    obtain ⟨C, s, hs, hC⟩ := haC.exists_lipschitzOnWith
    let c := ‖f a‖ / 2
    have hc : 0 < c := by dsimp [c]; positivity
    have hnear := (show ∀ᶠ t in 𝓝 a, t ∈ s from hs).and (hfa.continuousAt.norm.tendsto.eventually_const_lt
      (show c < ‖f a‖ by dsimp [c]; linarith))
    obtain ⟨d, hd, hb⟩ := Metric.mem_nhds_iff.mp hnear
    refine ⟨Metric.ball a (d / 2), mem_nhdsWithin_of_mem_nhds
      (Metric.ball_mem_nhds _ (by positivity)), ?_⟩
    have large (b : ℝ) : ∀ᶠ n : ℕ in atTop, b < (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop b)
    filter_upwards [large 1, large (2 / d), large ((C : ℝ) / c)] with n hn hn' hCn t ht
    have hn₀ : 0 < (n : ℝ) := by linarith
    have hmesh : 1 / (n : ℝ) ^ 2 < d / 2 := by
      rw [div_lt_iff₀ (sq_pos_of_pos hn₀)]
      have hh := (div_lt_iff₀ hd).mp hn'
      nlinarith [mul_nonneg (mul_nonneg hd.le hn₀.le) (by linarith : 0 ≤ (n : ℝ) - 1)]
    have ht' : t ∈ Metric.ball a d := (Metric.ball_subset_ball (by linarith) : Metric.ball a (d / 2) ⊆ _) ht
    have hd' : dist (t + 1 / (n : ℝ) ^ 2) t = 1 / (n : ℝ) ^ 2 := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (one_div_pos.mpr (sq_pos_of_pos hn₀))]
    have hq : t + 1 / (n : ℝ) ^ 2 ∈ Metric.ball a d := by
      apply (dist_triangle _ t _).trans_lt
      rw [hd']
      linarith [Metric.mem_ball.mp ht]
    have hdist := hC.dist_le_mul _ (hb hq).1 _ (hb ht').1
    rw [dist_eq_norm (f _) (f _)] at hdist
    have hdiff := (norm_sub_norm_le _ _).trans hdist
    rw [hd', ← div_eq_mul_one_div] at hdiff
    have hmul := mul_le_mul_of_nonneg_left hdiff hn₀.le
    have hred : (n : ℝ) * (C / (n : ℝ) ^ 2) = C / (n : ℝ) := by field_simp
    rw [hred] at hmul
    have hlim : (C : ℝ) / n < c := (div_lt_iff₀ hn₀).mpr (by linarith [(div_lt_iff₀ hc).mp hCn])
    linarith [(hb ht').2]

private def gridPoint (n : ℕ) (k : ℤ) : ℝ := (k : ℝ) / (n : ℝ) ^ 2

private lemma recenter {n : ℕ} (hn : 0 < (n : ℝ)) (a : ℝ) (k : ℤ) :
    a + ((k : ℝ) + -(a * (n : ℝ) ^ 2)) / (n : ℝ) ^ 2 = gridPoint n k := by
  dsimp [gridPoint]
  field_simp
  ring

private lemma mem_recentered {f : ℝ → ℂ} {a r : ℝ} {k : ℤ} {n : ℕ} (hn : 0 < (n : ℝ)) :
    k ∈ accepted f a r n (-(a * (n : ℝ) ^ 2)) ↔
      gridPoint n k ∈ Metric.ball a r ∧ ((n : ℝ) + 1) * ‖f (gridPoint n k)‖ <
        n * ‖f (gridPoint n k + 1 / (n : ℝ) ^ 2)‖ := by
  classical
  have hn₂ := sq_pos_of_pos hn
  have hid : a + ((k : ℝ) + -(a * (n : ℝ) ^ 2) + 1) / (n : ℝ) ^ 2 =
      gridPoint n k + 1 / (n : ℝ) ^ 2 := by rw [add_div, ← add_assoc, recenter hn]
  rw [accepted, Finset.mem_filter, mem_gridInterval, recenter hn, hid]
  apply and_congr_left
  intro _
  rw [Metric.mem_ball, Real.dist_eq, abs_lt, gridPoint, lt_sub_iff_add_lt,
    sub_lt_iff_lt_add, lt_div_iff₀ hn₂, div_lt_iff₀ hn₂]
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> nlinarith

/-- Finite sum over the prescribed grid between indices `-n³` and `n³`, using only
the magnitudes at each sample and its successor. -/
def sampleSum (f : ℝ → ℂ) (g : ℝ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact (∑ k ∈ (Finset.Icc (-(n : ℤ) ^ 3) ((n : ℤ) ^ 3)).filter (fun (k : ℤ) ↦
      ((n : ℝ) + 1) * ‖f ((k : ℝ) / (n : ℝ) ^ 2)‖ <
        n * ‖f (((k : ℝ) + 1) / (n : ℝ) ^ 2)‖), g ((k : ℝ) / (n : ℝ) ^ 2)) / n

/-- The finite comparison uses the two consecutive magnitudes on the prescribed mesh. -/
theorem sampleSum_eq_sum (f : ℝ → ℂ) (g : ℝ → ℝ) (n : ℕ) :
    sampleSum f g n = (∑ k ∈ (Finset.Icc (-(n : ℤ) ^ 3) ((n : ℤ) ^ 3)).filter (fun k : ℤ ↦
      ((n : ℝ) + 1) * ‖f ((k : ℝ) / (n : ℝ) ^ 2)‖ <
        n * ‖f (((k : ℝ) + 1) / (n : ℝ) ^ 2)‖), g ((k : ℝ) / (n : ℝ) ^ 2)) / n := by
  classical
  rfl

/-- Consecutive lattice magnitudes recover every real zero in a compact continuous test with
its full order. Analyticity and finiteness of the order are required only on the closed support. -/
theorem tendsto_sampleSum {f : ℝ → ℂ} {g : ℝ → ℝ} (hg : Continuous g)
    (hK : HasCompactSupport g) (hfa : ∀ x ∈ tsupport g, AnalyticAt ℝ f x)
    (hord : ∀ x ∈ tsupport g, analyticOrderAt f x ≠ ⊤) :
    Tendsto (sampleSum f g) atTop
      (𝓝 (∑' z : {x : ℝ // f x = 0}, (analyticOrderNatAt f (z : ℝ) : ℝ) * g z)) := by
  classical
  let K := tsupport g
  have hcompact : IsCompact K := hK
  have hZ := zeroSetOnCompact_finite hK hfa hord
  let S := hZ.toFinset
  have hS (a : ℝ) : a ∈ S ↔ a ∈ K ∧ f a = 0 := hZ.mem_toFinset
  obtain ⟨O, hO, hdis⟩ := S.finite_toSet.t2_separation
  have hroot (a : ℝ) (ha : a ∈ S) :
      ∃ r > 0, Metric.ball a r ⊆ O a ∧
        Tendsto (fun n : ℕ ↦ (∑ k ∈ accepted f a r n (-(a * (n : ℝ) ^ 2)), g (gridPoint n k)) / n)
          atTop (𝓝 ((analyticOrderNatAt f a : ℝ) * g a)) := by
    have hA := hfa a ((hS a).mp ha).1
    have hfinite := hord a ((hS a).mp ha).1
    have horder := (Nat.cast_analyticOrderNatAt hfinite).symm
    have hm : 0 < analyticOrderNatAt f a := Nat.pos_of_ne_zero fun h ↦ by
      have hz : analyticOrderAt f a = 0 := by rw [horder, h, Nat.cast_zero]
      exact (analyticOrderAt_eq_zero.mp hz).elim (fun h ↦ h hA) (fun h ↦ h ((hS a).mp ha).2)
    obtain ⟨R, hR, hlim⟩ := tendsto_accepted_sum hA hm horder
    obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp ((hO a).2.mem_nhds (hO a).1)
    refine ⟨min R d, lt_min hR hd, (Metric.ball_subset_ball (min_le_right _ _)).trans hball, ?_⟩
    apply (hlim _ (lt_min hR hd) (min_le_left _ _) (fun n ↦ -(a * (n : ℝ) ^ 2)) g hg.continuousAt).congr'
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    simp only [recenter hn]
  choose rad hrad hradO hradLim using hroot
  let r (a : ℝ) := if ha : a ∈ S then rad a ha else 0
  have hr (a : ℝ) (ha : a ∈ S) : r a = rad a ha := dite_eq_left ha
  let U := ⋃ a ∈ S, Metric.ball a (r a)
  have hU : IsOpen U := isOpen_biUnion (fun _ _ ↦ Metric.isOpen_ball)
  let E := K \ U
  have hE : IsCompact E := hcompact.inter_right hU.isClosed_compl
  have hfE (a : ℝ) (ha : a ∈ E) : f a ≠ 0 := by
    intro haz
    have hs := (hS a).mpr ⟨ha.1, haz⟩
    exact ha.2 (mem_iUnion₂.mpr ⟨a, hs, Metric.mem_ball_self (by rw [hr a hs]; exact hrad a hs)⟩)
  have hreg := no_threshold_on_compact hE (fun a ha ↦ hfa a ha.1) hfE
  let L (n : ℕ) (a : ℝ) := accepted f a (r a) n (-(a * (n : ℝ) ^ 2))
  let J (n : ℕ) := (Finset.Icc (-(n : ℤ) ^ 3) ((n : ℤ) ^ 3)).filter (fun k ↦
    ((n : ℝ) + 1) * ‖f (gridPoint n k)‖ < n * ‖f (gridPoint n k + 1 / (n : ℝ) ^ 2)‖)
  have hneighborhoods := tendsto_finsetSum S (fun a ha ↦ (show
    Tendsto (fun n : ℕ ↦ (∑ k ∈ L n a, g (gridPoint n k)) / n) atTop
      (𝓝 ((analyticOrderNatAt f a : ℝ) * g a)) from by simpa only [L, hr a ha] using hradLim a ha))
  have hlimit : (∑' z : {x : ℝ // f x = 0}, (analyticOrderNatAt f (z : ℝ) : ℝ) * g z) =
      ∑ a ∈ S, (analyticOrderNatAt f a : ℝ) * g a := by
    have hall : (∑' z : {x : ℝ // f x = 0}, (analyticOrderNatAt f (z : ℝ) : ℝ) * g z) =
        ∑' x : ℝ, (analyticOrderNatAt f x : ℝ) * g x := by
      refine tsum_subtype_eq_of_support_subset (s := {x : ℝ | f x = 0})
        (f := fun x : ℝ ↦ (analyticOrderNatAt f x : ℝ) * g x) ?_
      intro x hx
      by_contra hz
      exact hx (by simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hz)])
    rw [hall]
    apply tsum_eq_sum
    intro a ha
    by_cases hak : a ∈ K
    · have hn : f a ≠ 0 := fun h ↦ ha ((hS a).mpr ⟨hak, h⟩)
      simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hn)]
    · simp [image_eq_zero_of_notMem_tsupport (f := g) hak]
  rw [hlimit]
  apply hneighborhoods.congr'
  have allLarge : ∀ᶠ n : ℕ in atTop, ∀ a ∈ S, |a| + r a < (n : ℝ) :=
    S.eventually_all.mpr fun a _ ↦ tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
  filter_upwards [hreg, allLarge, tendsto_natCast_atTop_atTop.eventually
    (eventually_gt_atTop (0 : ℝ))] with n haway hlarge hn
  have hn₂ := sq_pos_of_pos hn
  have hsplit : (S : Set ℝ).PairwiseDisjoint (L n) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    have h₁ := (mem_recentered hn).mp hk
    have h₂ := (mem_recentered hn).mp hk'
    have haO : gridPoint n k ∈ O a := hradO a ha (hr a ha ▸ h₁.1)
    have hbO : gridPoint n k ∈ O b := hradO b hb (hr b hb ▸ h₂.1)
    exact Set.disjoint_left.mp (hdis ha hb hab) haO hbO
  have hsub : S.biUnion (L n) ⊆ J n := by
    intro k hk
    obtain ⟨a, ha, hka⟩ := Finset.mem_biUnion.mp hk
    obtain ⟨hball, htest⟩ := (mem_recentered hn).mp hka
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ?_, htest⟩
    have habs : |gridPoint n k| < (n : ℝ) := by
      calc
        |gridPoint n k| = |(gridPoint n k - a) + a| := by rw [sub_add_cancel]
        _ ≤ |gridPoint n k - a| + |a| := abs_add_le _ _
        _ < n := by linarith [show |gridPoint n k - a| < r a from hball, hlarge a ha]
    rw [gridPoint, abs_div, abs_of_pos hn₂] at habs
    have hd : |(k : ℝ)| < (n : ℝ) ^ 3 := by nlinarith [(div_lt_iff₀ hn₂).mp habs]
    obtain ⟨h₁, h₂⟩ := abs_lt.mp hd
    exact_mod_cast And.intro h₁.le h₂.le
  have hout (k : ℤ) (hk : k ∈ J n) (hkn : k ∉ S.biUnion (L n)) : g (gridPoint n k) = 0 := by
    by_contra hgk
    have hkK : gridPoint n k ∈ K := subset_tsupport g (show gridPoint n k ∈ Function.support g from hgk)
    have ht := (Finset.mem_filter.mp hk).2
    have hkU : gridPoint n k ∉ U := by
      intro hx
      obtain ⟨a, ha, hb⟩ := mem_iUnion₂.mp hx
      exact hkn (Finset.mem_biUnion.mpr ⟨a, ha, (mem_recentered hn).mpr ⟨hb, ht⟩⟩)
    exact (not_lt_of_ge (haway _ ⟨hkK, hkU⟩)) ht
  change (∑ a ∈ S, (∑ k ∈ L n a, g (gridPoint n k)) / n) = sampleSum f g n
  rw [← Finset.sum_div, ← Finset.sum_biUnion hsplit, Finset.sum_subset hsub hout]
  unfold sampleSum J
  congr 1
  apply Finset.sum_congr
  · ext k
    simp only [Finset.mem_filter, gridPoint, add_div]
    exact Finset.mem_filter
  · intro k _
    rfl

end RiemannMasullo.AnalyticLattice
