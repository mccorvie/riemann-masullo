module

public import RiemannMasullo.ForMathlib.Analysis.Analytic.ZeroLatticeWindow
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Extending a lattice zero measurement to Schwartz tests

Cut off the Schwartz test outside a growing interval. The contribution omitted by the
cutoff is uniformly bounded by a constant divided by the cutoff radius plus one. The
critical-line application supplies compact convergence and an inverse-square bound on
its genuine zero multiplicities.
-/

public noncomputable section
open Filter Function Set Topology
open scoped SchwartzMap
namespace RiemannMasullo.AnalyticLattice

private def cutoff (r : ℕ) (t : ℝ) := max 0 (min 1 ((r : ℝ) + 1 - |t|))

private lemma cutoff_one {r : ℕ} {t : ℝ} (ht : |t| ≤ r) : cutoff r t = 1 := by
  simp [cutoff, min_eq_left (by linarith : 1 ≤ (r : ℝ) + 1 - |t|)]

private lemma cutoff_bounds (r : ℕ) (t : ℝ) : 0 ≤ cutoff r t ∧ cutoff r t ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

private lemma cutoff_compact (r : ℕ) : HasCompactSupport (cutoff r) := by
  apply HasCompactSupport.intro (K := Icc (-(r : ℝ)-1) ((r : ℝ)+1)) isCompact_Icc
  intro t ht
  have hh : (r : ℝ)+1 < |t| := by
    by_contra! h
    exact ht ⟨by linarith [(abs_le.mp h).1], (abs_le.mp h).2⟩
  simp [cutoff, max_eq_left ((min_le_right _ _).trans (by linarith : (r : ℝ) + 1 - |t| ≤ 0))]

private lemma decay_bound (g : 𝓢(ℝ, ℝ)) (k : ℕ) :
    ∃ P > (0 : ℝ), ∀ x : ℝ, (1 + |x|) ^ k * |g x| ≤ P := by
  let P := 2 ^ k * (Finset.Iic (k, 0)).sup (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) g
  refine ⟨max 1 P, zero_lt_one.trans_le (le_max_left _ _), fun x ↦ ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl g x
  exact (show _ ≤ P from by simpa only [P, norm_iteratedFDeriv_zero, Real.norm_eq_abs] using h).trans
    (le_max_right _ _)

private lemma summable_bin_weight : Summable (fun j : ℤ ↦ 1 / (1 + |(j : ℝ)|) ^ 2) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
  have hn : Summable (fun n : ℕ ↦ 1 / (1 + (n : ℝ)) ^ 2) := by
    apply h.congr
    intro n
    rw [Real.rpow_two, abs_of_nonneg (by positivity)]
    ring
  apply Summable.of_nat_of_neg
  · simpa using hn
  · simpa using hn

private def finiteNodes (f : ℝ → ℂ) (n : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Icc (-(n : ℤ) ^ 3) ((n : ℤ) ^ 3)).filter fun k : ℤ ↦
    ((n : ℝ) + 1) * ‖f ((k : ℝ) / (n : ℝ) ^ 2)‖ <
      n * ‖f (((k : ℝ) + 1) / (n : ℝ) ^ 2)‖

private lemma sampleSum_eq (f : ℝ → ℂ) (g : ℝ → ℝ) (n : ℕ) :
    sampleSum f g n = (∑ k ∈ finiteNodes f n, g ((k : ℝ) / (n : ℝ) ^ 2)) / n := by
  exact sampleSum_eq_sum f g n

private lemma tail_bound (f : ℝ → ℂ) (g : ℝ → ℝ) {P C J : ℝ}
    (hP : 0 < P) (hdec : ∀ x, (1+|x|)^5 * |g x| ≤ P) (hC : 0 ≤ C)
    (hhi : ∀ j : ℤ, J ≤ |(j : ℝ)| → ∀ n : ℕ, 0 < n →
      ((binIndices f j n).card : ℝ) / n ≤ C * (1 + |(j : ℝ)|) ^ 2)
    {r n : ℕ} (hr : J + 1 ≤ r) (hn : 0 < n) :
    |sampleSum f g n - sampleSum f (fun t ↦ cutoff r t * g t) n| ≤
      (16 * P * C * (∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2)) / ((r : ℝ) + 1) := by
  classical
  let A := finiteNodes f n
  let x (k : ℤ) := (k : ℝ) / (n : ℝ) ^ 2
  let b (k : ℤ) := ⌊x k⌋
  let T (j : ℤ) := A.filter (fun k ↦ b k = j)
  let e (k : ℤ) := |g (x k) - cutoff r (x k) * g (x k)|
  let w (j : ℤ) := 1 / (1 + |(j : ℝ)|) ^ 2
  let K := 16 * P * C / ((r : ℝ) + 1)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn₂ := sq_pos_of_pos hn'
  have hr₁ : 0 < (r : ℝ) + 1 := by positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hw (j : ℤ) : 0 ≤ w j := by dsimp [w]; positivity
  have hbin {j k : ℤ} (hk : k ∈ T j) : (j : ℝ) ≤ x k ∧ x k < (j : ℝ)+1 := by
    have hb : ⌊x k⌋ = j := (Finset.mem_filter.mp hk).2
    rw [← hb]
    exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  have near {j k : ℤ} (hk : k ∈ T j) :
      |x k| ≤ |(j : ℝ)| + 1 ∧ |(j : ℝ)| ≤ |x k| + 1 := by
    obtain ⟨hl, hu⟩ := hbin hk
    have hneg := neg_abs_le (j : ℝ)
    have hv := le_abs_self (j : ℝ)
    have hneg' := neg_abs_le (x k)
    have hv' := le_abs_self (x k)
    constructor <;> apply abs_le.mpr <;> constructor <;> linarith
  have hsub (j : ℤ) : T j ⊆ binIndices f j n := by
    intro k hk
    obtain ⟨hl, hu⟩ := hbin hk
    have hacc := (Finset.mem_filter.mp (show k ∈ finiteNodes f n from (Finset.mem_filter.mp hk).1)).2
    refine (mem_binIndices_iff f j n k).mpr ⟨⟨?_, ?_⟩, hacc⟩
    · exact_mod_cast (le_div_iff₀ hn₂).mp hl
    · exact_mod_cast (div_lt_iff₀ hn₂).mp hu
  have ebound {j k : ℤ} (hk : k ∈ T j) :
      e k ≤ 16 * P / (((r : ℝ)+1) * (1 + |(j : ℝ)|) ^ 4) := by
    by_cases hlow : |x k| ≤ r
    · simp only [e, cutoff_one hlow, one_mul, sub_self, abs_zero]
      positivity
    have hc := cutoff_bounds r (x k)
    have he : e k ≤ |g (x k)| := by
      dsimp [e]
      rw [← one_sub_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hc.2)]
      nlinarith [mul_nonneg hc.1 (abs_nonneg (g (x k)))]
    have hden : 0 < ((r : ℝ)+1) * (1 + |(j : ℝ)|) ^ 4 := by positivity
    apply he.trans
    apply (le_div_iff₀ hden).mpr
    have hh : ((r : ℝ)+1) * (1 + |(j : ℝ)|) ^ 4 ≤ 16 * (1 + |x k|)^5 := by
      calc
        _ ≤ (1 + |x k|) * (2*(1 + |x k|))^4 := by
          apply mul_le_mul (by linarith : (r : ℝ) + 1 ≤ 1 + |x k|) _ (by positivity) (by positivity)
          apply pow_le_pow_left₀ (by positivity)
          linarith [(near hk).2, abs_nonneg (x k)]
        _ = _ := by ring
    nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (g (x k))), hdec (x k)]
  have bin (j : ℤ) : (∑ k ∈ T j, e k) / (n : ℝ) ≤ K * w j := by
    by_cases H : J ≤ |(j : ℝ)|
    · have hcard : ((T j).card : ℝ) ≤ (binIndices f j n).card := by
        exact_mod_cast Finset.card_le_card (hsub j)
      have hc := (div_le_div_of_nonneg_right hcard hn'.le).trans (hhi j H n hn)
      let D := 16 * P / (((r : ℝ)+1) * (1 + |(j : ℝ)|) ^ 4)
      have hD : 0 ≤ D := by dsimp [D]; positivity
      calc
        _ ≤ (∑ _k ∈ T j, D) / n := div_le_div_of_nonneg_right (Finset.sum_le_sum fun _ hk ↦ ebound hk) hn'.le
        _ = ((T j).card / (n : ℝ)) * D := by simp; ring
        _ ≤ (C * (1 + |(j : ℝ)|)^2) * D := mul_le_mul_of_nonneg_right hc hD
        _ = K * w j := by
          dsimp [K, w, D]
          field_simp [show (1 + |(j : ℝ)|) ≠ 0 by positivity]
    · have hz : ∑ k ∈ T j, e k = 0 := Finset.sum_eq_zero fun k hk ↦ by
        have ht : |x k| ≤ r := by linarith [(near hk).1]
        simp [e, cutoff_one ht]
      rw [hz, zero_div]
      exact mul_nonneg hK (hw j)
  have hsum : Summable (fun j ↦ K * w j) := summable_bin_weight.mul_left K
  calc
    _ ≤ (∑ k ∈ A, e k) / n := by
      rw [sampleSum_eq, sampleSum_eq, ← sub_div, abs_div, abs_of_pos hn']
      refine div_le_div_of_nonneg_right ?_ hn'.le
      rw [← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ A.image b, (∑ k ∈ T j, e k) / n := by
      rw [← Finset.sum_div]
      exact congrArg (· / (n : ℝ)) (Finset.sum_fiberwise_of_maps_to (fun k hk ↦ Finset.mem_image_of_mem b hk) e).symm
    _ ≤ ∑ j ∈ A.image b, K * w j := Finset.sum_le_sum fun j _ ↦ bin j
    _ ≤ ∑' j : ℤ, K * w j := hsum.sum_le_tsum _ fun j _ ↦ mul_nonneg hK (hw j)
    _ = _ := by rw [tsum_mul_left]; dsimp [K, w]; ring

/-- Compact convergence of the strict finite samples extends to every signed Schwartz test if
the normalized high-bin counts grow quadratically and the target weights are summable with
inverse-square decay. -/
theorem tendsto_sampleSum_schwartz {ι : Type*} (f : ℝ → ℂ) (q m : ι → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hsites : Summable (fun i ↦ m i / (1 + |q i|)^2))
    (hcompact : ∀ v : ℝ → ℝ, Continuous v → HasCompactSupport v →
      Tendsto (sampleSum f v) atTop (𝓝 (∑' i, m i * v (q i))))
    {C J : ℝ} (hC : 0 ≤ C) (hhi : ∀ j : ℤ, J ≤ |(j : ℝ)| → ∀ n : ℕ, 0 < n →
      ((binIndices f j n).card : ℝ) / n ≤ C * (1 + |(j : ℝ)|) ^ 2)
    (g : 𝓢(ℝ, ℝ)) :
    Tendsto (sampleSum f g) atTop (𝓝 (∑' i, m i * g (q i))) := by
  classical
  obtain ⟨P, hP, h5⟩ := decay_bound g 5
  obtain ⟨Q, hQ, h2⟩ := decay_bound g 2
  let G (r : ℕ) (t : ℝ) := cutoff r t * g t
  have hGc (r : ℕ) : Continuous (G r) := by
    dsimp [G, cutoff]
    fun_prop
  have hGK (r : ℕ) : HasCompactSupport (G r) := (cutoff_compact r).mul_right
  have hzero : Tendsto (fun r : ℕ ↦ ∑' i, m i * G r (q i)) atTop (𝓝 (∑' i, m i * g (q i))) := by
    apply tendsto_tsum_of_dominated_convergence (hsites.mul_left Q)
    · intro i
      apply tendsto_const_nhds.congr'
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop |q i|)] with r hr
      simp [G, cutoff_one hr]
    · filter_upwards with r i
      simp only [Real.norm_eq_abs, G, abs_mul, abs_of_nonneg (hm i), abs_of_nonneg (cutoff_bounds _ _).1]
      have hden : 0 < (1 + |q i|)^2 := by positivity
      calc
        m i * (cutoff r (q i) * |g (q i)|) ≤ m i * |g (q i)| :=
          mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (abs_nonneg _) (cutoff_bounds _ _).2) (hm i)
        _ ≤ m i * (Q / (1 + |q i|)^2) := mul_le_mul_of_nonneg_left
          ((le_div_iff₀ hden).mpr (by simpa only [mul_comm] using h2 (q i))) (hm i)
        _ = _ := by ring
  let K := 16 * P * C * (∑' j : ℤ, 1 / (1 + |(j : ℝ)|)^2)
  have hKlim : Tendsto (fun r : ℕ ↦ K / ((r : ℝ)+1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul K
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hε₃ : 0 < ε / 3 := by linarith
  have hev := (hzero.eventually (Metric.ball_mem_nhds _ hε₃)).and
    ((hKlim.eventually_lt_const hε₃).and
      (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (J+1))))
  obtain ⟨r, hrclose, hrK, hrJ⟩ := hev.exists
  have hf := hcompact (G r) (hGc r) (hGK r)
  filter_upwards [hf.eventually (Metric.ball_mem_nhds _ hε₃), eventually_gt_atTop (0 : ℕ)] with n hnclose hn
  have htail := tail_bound f g hP h5 hC hhi hrJ hn
  rw [Real.dist_eq]
  have hh := abs_add_le (sampleSum f g n - sampleSum f (G r) n)
    (sampleSum f (G r) n - ∑' i, m i * g (q i))
  rw [sub_add_sub_cancel] at hh
  have ht := abs_add_le (sampleSum f (G r) n - ∑' i, m i * G r (q i))
    ((∑' i, m i * G r (q i)) - ∑' i, m i * g (q i))
  rw [sub_add_sub_cancel] at ht
  change |(∑' i, m i * G r (q i)) - ∑' i, m i * g (q i)| < _ at hrclose
  change |sampleSum f (G r) n - ∑' i, m i * G r (q i)| < _ at hnclose
  change |sampleSum f g n - sampleSum f (G r) n| ≤ K / ((r : ℝ)+1) at htail
  linarith

end RiemannMasullo.AnalyticLattice
