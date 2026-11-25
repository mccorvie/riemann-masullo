module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Triangular sums of bounded deficits

Pointwise convergence in each row suffices for the clipped geometric sums at increasing
resolutions. Arbitrarily small sums detect simultaneous vanishing of the nonnegative row limits.
-/

@[expose] public noncomputable section
open Filter Topology Finset

namespace RiemannMasullo.TriangularComparison

/-- Keep the magnitude of a nonnegative deficit uniformly bounded by one.
Small negative finite-sampling errors are discarded. -/
def clip (x : ℝ) : ℝ := min 1 (max 0 x)

private theorem clip_nonneg (x : ℝ) : 0 ≤ clip x := le_min zero_le_one (le_max_left _ _)
private theorem clip_le_one (x : ℝ) : clip x ≤ 1 := min_le_left _ _
private theorem clip_continuous : Continuous clip :=
  continuous_const.min (continuous_const.max continuous_id)

/-- Geometrically weight the rows of index below the current resolution. -/
def weighted (u : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ range n, (1 / 2 : ℝ)^j * clip (u j n)

/-- A single triangular array admits a limit under pointwise convergence in each row.
The finite statistic uses only rows with index less than its common resolution. -/
theorem tendsto_weighted (u : ℕ → ℕ → ℝ) (L : ℕ → ℝ)
    (h : ∀ j, Tendsto (u j) atTop (𝓝 (L j))) :
    Tendsto (weighted u) atTop (𝓝 (∑' j, (1 / 2 : ℝ)^j * clip (L j))) := by
  let f (n j : ℕ) : ℝ := if j < n then (1/2 : ℝ)^j * clip (u j n) else 0
  have hsum : Summable (fun j : ℕ ↦ (1/2 : ℝ)^j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hlim (j : ℕ) : Tendsto (fun n ↦ f n j) atTop (𝓝 ((1/2 : ℝ)^j * clip (L j))) := by
    apply ((clip_continuous.continuousAt.tendsto.comp (h j)).const_mul _).congr'
    filter_upwards [eventually_gt_atTop j] with n hn
    simp [f, hn]
  have hbound (n j : ℕ) : ‖f n j‖ ≤ (1/2 : ℝ)^j := by
    by_cases hj : j < n
    · have hpos : 0 ≤ (1/2 : ℝ)^j * clip (u j n) :=
        mul_nonneg (by positivity) (clip_nonneg _)
      simp only [f, hj, ite_true, Real.norm_eq_abs, abs_of_nonneg hpos]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (clip_le_one (u j n))
        (by positivity : 0 ≤ (1/2 : ℝ)^j)
    · simp [f, hj]
  have main := tendsto_tsum_of_dominated_convergence hsum hlim (Eventually.of_forall hbound)
  have ht (n : ℕ) : (∑' j, f n j) = weighted u n := by
    rw [tsum_eq_sum (s := range n) fun j hj ↦ by
      have hjn : ¬j < n := fun h ↦ hj (mem_range.mpr h)
      simp [f, hjn]]
    apply sum_congr rfl fun j hj ↦ ?_
    simp [f, mem_range.mp hj]
  exact main.congr (fun n ↦ ht n)

/-- Positive clipped deficits over any fixed countable enumeration can be tested with
one unbounded sequence of finite, bounded scalar comparisons. -/
theorem frequently_weighted_small_iff {u : ℕ → ℕ → ℝ} {L : ℕ → ℝ}
    (h : ∀ j, Tendsto (u j) atTop (𝓝 (L j))) (hL : ∀ j, 0 ≤ L j) :
    (∀ δ : ℝ, 0 < δ → ∃ᶠ n : ℕ in atTop, weighted u n < δ) ↔ ∀ j, L j = 0 := by
  have lim := tendsto_weighted u L h
  let w (j : ℕ) := (1/2 : ℝ)^j * clip (L j)
  have hw (j : ℕ) : 0 ≤ w j := mul_nonneg (by positivity) (clip_nonneg _)
  have hs : Summable w := by
    apply Summable.of_nonneg_of_le hw (fun j ↦ ?_) (summable_geometric_of_lt_one
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (clip_le_one (L j))
      (by positivity : 0 ≤ (1/2 : ℝ)^j)
  constructor
  · intro hsmall j
    by_contra hbad
    have lpos : 0 < L j := (hL j).lt_of_ne (Ne.symm hbad)
    have cp : 0 < clip (L j) := lt_min zero_lt_one (lt_sup_of_lt_right lpos)
    have wp : 0 < w j := mul_pos (by positivity) cp
    have pos : 0 < ∑' i, w i := wp.trans_le (hs.le_tsum j (fun i _ ↦ hw i))
    change Tendsto _ _ (𝓝 (∑' i, w i)) at lim
    have above := lim.eventually_const_lt (show (∑' i, w i)/2 < ∑' i, w i by linarith)
    obtain ⟨n, hn, hm⟩ := ((hsmall _ (half_pos pos)).and_eventually above).exists
    exact lt_asymm hn hm
  · intro hzero δ hδ
    simp [hzero, clip] at lim
    exact (lim.eventually_lt_const hδ).frequently

/-- The limiting geometric series of clipped real rows converges absolutely and
has mass between zero and two. -/
theorem summable_clip_and_tsum_mem_Icc (L : ℕ → ℝ) :
    Summable (fun j : ℕ ↦ (1/2 : ℝ)^j * clip (L j)) ∧
      (∑' j : ℕ, (1/2 : ℝ)^j * clip (L j)) ∈ Set.Icc (0 : ℝ) 2 := by
  have hg : Summable (fun j : ℕ ↦ (1/2 : ℝ)^j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hn (j : ℕ) : 0 ≤ (1/2 : ℝ)^j * clip (L j) :=
    mul_nonneg (by positivity) (clip_nonneg _)
  have hb (j : ℕ) : (1/2 : ℝ)^j * clip (L j) ≤ (1/2 : ℝ)^j := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (clip_le_one (L j)) (by positivity : 0 ≤ (1/2 : ℝ)^j)
  have hs := Summable.of_nonneg_of_le hn hb hg
  refine ⟨hs, tsum_nonneg hn, (hs.tsum_le_tsum hb hg).trans ?_⟩
  rw [tsum_geometric_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num)]
  norm_num

/-- The test may be restricted to any prescribed unbounded set of resolutions. -/
theorem cofinal_weighted_small_along_iff {u : ℕ → ℕ → ℝ} {L : ℕ → ℝ}
    (h : ∀ j, Tendsto (u j) atTop (𝓝 (L j))) (hL : ∀ j, 0 ≤ L j)
    (I : Set ℕ) (hI : ∀ N : ℕ, ∃ n ∈ I, N ≤ n) :
    (∀ δ : ℝ, 0 < δ → ∀ N : ℕ, ∃ n ∈ I, N ≤ n ∧ weighted u n < δ) ↔
      ∀ j, L j = 0 := by
  constructor
  · intro hs
    apply (frequently_weighted_small_iff h hL).mp
    intro δ hδ
    rw [frequently_atTop]
    intro N
    obtain ⟨n, _, hN, hn⟩ := hs δ hδ N
    exact ⟨n, hN, hn⟩
  · intro hzero δ hδ N
    have lim := tendsto_weighted u L h
    simp [hzero, clip] at lim
    obtain ⟨k, hk⟩ := eventually_atTop.1 (lim.eventually_lt_const hδ)
    obtain ⟨n, hn, hkn⟩ := hI (max k N)
    exact ⟨n, hn, (le_max_right _ _).trans hkn, hk n ((le_max_left _ _).trans hkn)⟩

end RiemannMasullo.TriangularComparison
