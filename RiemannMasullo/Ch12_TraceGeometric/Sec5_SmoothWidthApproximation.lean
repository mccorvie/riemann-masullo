module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Approximation of the signed strip trace near a width

A continuous approximation of the spectral trace near a strip edge has an error at least half
of the corresponding jump. The two one-sided limits separate the boundary jets that the closed
strip retains from the boundary jets that it omits.
-/

public noncomputable section

open Filter Set
open scoped Topology

namespace RiemannMasullo

private theorem widthApprox_stripMultiplicity_le (a s b : ℝ) (n : ℕ) :
    spectralStripMultiplicity a s b n ≤ n := by
  unfold spectralStripMultiplicity spectralBoundaryMultiplicity
  split_ifs <;> first | exact le_rfl | exact min_le_left _ _ | exact Nat.zero_le _

private theorem widthApprox_stripMultiplicity_outside {a b : ℝ} (ha : 0 ≤ a)
    (hb : a < |b|) (s : ℝ) (n : ℕ) : spectralStripMultiplicity a s b n = 0 := by
  have hi : ¬ (-a < b ∧ b < a) := fun h ↦ hb.not_gt (abs_lt.mpr h)
  have he : ¬ (b = -a ∨ b = a) := by
    rintro (rfl | rfl) <;> simp [abs_of_nonneg ha] at hb
  simp [spectralStripMultiplicity, hi, he]

private theorem widthApprox_stripMultiplicity_edge {a b : ℝ} (ha : 0 ≤ a)
    (hb : |b| = a) (s : ℝ) (n : ℕ) :
    spectralStripMultiplicity a s b n = spectralBoundaryMultiplicity s n := by
  apply spectralStripMultiplicity_boundary ha _ s n
  rcases le_total 0 b with h | h
  · exact Or.inr (by simpa only [abs_of_nonneg h] using hb)
  · exact Or.inl (by rw [abs_of_nonpos h] at hb; linarith)

private theorem widthApprox_norm_nat_mul_le {p n : ℕ} (h : p ≤ n) (z : ℂ) :
    ‖(p : ℂ) * z‖ ≤ (n : ℝ) * ‖z‖ := by
  rw [norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (norm_nonneg _)

private theorem widthApprox_tendsto_left {ι : Type*} (x : ι → ℝ) (v : ι → ℂ) (m : ι → ℕ)
    (h : Summable (fun i ↦ (m i : ℝ) * ‖v i‖)) {a : ℝ} (ha : 0 < a) (s : ℝ) :
    Tendsto (fun b : ℝ ↦ ∑' i, (spectralStripMultiplicity b s (x i) (m i) : ℂ) * v i)
      (𝓝[<] a) (𝓝 (∑' i, if |x i| < a then (m i : ℂ) * v i else 0)) := by
  apply tendsto_tsum_of_dominated_convergence h
  · intro i
    by_cases hi : |x i| < a
    · rw [ite_eq_left hi]
      apply tendsto_const_nhds.congr'
      filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds hi)] with b hb
      rw [spectralStripMultiplicity_interior (abs_lt.mp hb)]
    · rw [ite_eq_right hi]
      apply tendsto_const_nhds.congr'
      filter_upwards [show ∀ᶠ b in 𝓝[<] a, b < a from self_mem_nhdsWithin,
        nhdsWithin_le_nhds (eventually_gt_nhds ha)] with b hba hb
      rw [widthApprox_stripMultiplicity_outside hb.le (hba.trans_le (le_of_not_gt hi)),
        Nat.cast_zero, zero_mul]
  · exact Eventually.of_forall fun b i ↦
      widthApprox_norm_nat_mul_le (widthApprox_stripMultiplicity_le b s (x i) (m i)) (v i)

private theorem widthApprox_tendsto_right {ι : Type*} (x : ι → ℝ) (v : ι → ℂ) (m : ι → ℕ)
    (h : Summable (fun i ↦ (m i : ℝ) * ‖v i‖)) {a : ℝ} (ha : 0 < a) (s : ℝ) :
    Tendsto (fun b : ℝ ↦ ∑' i, (spectralStripMultiplicity b s (x i) (m i) : ℂ) * v i)
      (𝓝[>] a) (𝓝 (∑' i, if |x i| ≤ a then (m i : ℂ) * v i else 0)) := by
  apply tendsto_tsum_of_dominated_convergence h
  · intro i
    by_cases hi : |x i| ≤ a
    · rw [ite_eq_left hi]
      apply tendsto_const_nhds.congr'
      filter_upwards [show ∀ᶠ b in 𝓝[>] a, a < b from self_mem_nhdsWithin] with b hb
      rw [spectralStripMultiplicity_interior (abs_lt.mp (hi.trans_lt hb))]
    · rw [ite_eq_right hi]
      apply tendsto_const_nhds.congr'
      filter_upwards [show ∀ᶠ b in 𝓝[>] a, a < b from self_mem_nhdsWithin,
        nhdsWithin_le_nhds (eventually_lt_nhds (lt_of_not_ge hi))] with b hab hb
      rw [widthApprox_stripMultiplicity_outside (ha.trans hab).le hb, Nat.cast_zero, zero_mul]
  · exact Eventually.of_forall fun b i ↦
      widthApprox_norm_nat_mul_le (widthApprox_stripMultiplicity_le b s (x i) (m i)) (v i)

private theorem widthApprox_summable {ι : Type*} (v : ι → ℂ) (m n : ι → ℕ)
    (h : Summable (fun i ↦ (m i : ℝ) * ‖v i‖)) (hle : ∀ i, n i ≤ m i) :
    Summable (fun i ↦ (n i : ℂ) * v i) :=
  h.of_norm_bounded fun i ↦ widthApprox_norm_nat_mul_le (hle i) (v i)

/-- Paper: (10.2.2.5), p. 446 and (12.5.1.4), p. 520. A continuous approximation to
the complex closed-strip spectral sum near a positive width has error at least half each edge
contribution. The left jump counts the retained jets, the right jump counts the omitted jets,
and the total jump counts the full boundary multiplicity. A constant minus the closed-strip
sum has the same error bounds after subtracting it from the same constant. -/
theorem spectralStripTrace_edgeJump_le_two_mul_uniformError {ι : Type*}
    (x : ι → ℝ) (v : ι → ℂ) (m : ι → ℕ) (h : Summable (fun i ↦ (m i : ℝ) * ‖v i‖))
    {a : ℝ} (ha : 0 < a) (s : ℝ) (D : ℝ → ℂ) (hD : ContinuousAt D a) (ε : ℝ) :
    let T (b : ℝ) := ∑' i, (spectralStripMultiplicity b s (x i) (m i) : ℂ) * v i
    (∀ᶠ b in 𝓝 a, ‖D b - T b‖ ≤ ε) →
      ‖∑' i, if |x i| = a then (spectralBoundaryMultiplicity s (m i) : ℂ) * v i else 0‖ ≤ 2 * ε ∧
      ‖∑' i, if |x i| = a then ((m i - spectralBoundaryMultiplicity s (m i) : ℕ) : ℂ) * v i
        else 0‖ ≤ 2 * ε ∧
      ‖∑' i, if |x i| = a then (m i : ℂ) * v i else 0‖ ≤ 2 * ε := by
  classical
  intro T hnear
  let L (i : ι) := if |x i| < a then (m i : ℂ) * v i else 0
  let R (i : ι) := if |x i| ≤ a then (m i : ℂ) * v i else 0
  let C (i : ι) := (spectralStripMultiplicity a s (x i) (m i) : ℂ) * v i
  let E (i : ι) := if |x i| = a then (spectralBoundaryMultiplicity s (m i) : ℂ) * v i else 0
  let O (i : ι) := if |x i| = a then ((m i - spectralBoundaryMultiplicity s (m i) : ℕ) : ℂ) * v i
    else 0
  let F (i : ι) := if |x i| = a then (m i : ℂ) * v i else 0
  have hL : Summable L := by
    apply h.of_norm_bounded
    intro i
    by_cases hi : |x i| < a
    · simp [L, hi]
    · simp [L, hi, mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)]
  have hR : Summable R := by
    apply h.of_norm_bounded
    intro i
    by_cases hi : |x i| ≤ a
    · simp [R, hi]
    · simp [R, hi, mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)]
  have hC : Summable C := widthApprox_summable v m _ h
    fun i ↦ widthApprox_stripMultiplicity_le a s (x i) (m i)
  have hsplit (i : ι) : C i - L i = E i ∧ R i - C i = O i ∧ R i - L i = F i := by
    rcases lt_trichotomy |x i| a with hi | hi | hi
    · simp [C, L, R, E, O, F, hi, hi.le, hi.ne,
        spectralStripMultiplicity_interior (abs_lt.mp hi)]
    · have hcap : spectralBoundaryMultiplicity s (m i) ≤ m i := min_le_left _ _
      simp only [C, L, R, E, O, F, hi, lt_self_iff_false, le_refl, ite_false, ite_true, sub_zero,
        widthApprox_stripMultiplicity_edge ha.le hi, Nat.cast_sub hcap, sub_mul, and_self]
    · simp [C, L, R, E, O, F, not_le.mpr hi, hi.not_gt, hi.ne',
        widthApprox_stripMultiplicity_outside ha.le hi]
  have hEqE : (∑' i, E i) = T a - ∑' i, L i := by
    rw [← hC.tsum_sub hL]
    exact tsum_congr fun i ↦ (hsplit i).1.symm
  have hEqO : (∑' i, O i) = (∑' i, R i) - T a := by
    rw [← hR.tsum_sub hC]
    exact tsum_congr fun i ↦ (hsplit i).2.1.symm
  have hEqF : (∑' i, F i) = (∑' i, R i) - ∑' i, L i := by
    rw [← hR.tsum_sub hL]
    exact tsum_congr fun i ↦ (hsplit i).2.2.symm
  have hleft : ‖D a - ∑' i, L i‖ ≤ ε :=
    le_of_tendsto (((hD.tendsto.mono_left nhdsWithin_le_nhds).sub
      (widthApprox_tendsto_left x v m h ha s)).norm) (nhdsWithin_le_nhds hnear)
  have hright : ‖D a - ∑' i, R i‖ ≤ ε :=
    le_of_tendsto (((hD.tendsto.mono_left nhdsWithin_le_nhds).sub
      (widthApprox_tendsto_right x v m h ha s)).norm) (nhdsWithin_le_nhds hnear)
  have hat : ‖D a - T a‖ ≤ ε := mem_of_mem_nhds hnear
  have hpair {u w : ℂ} (hu : ‖D a - u‖ ≤ ε) (hw : ‖D a - w‖ ≤ ε) : ‖u - w‖ ≤ 2 * ε := by
    calc
      ‖u - w‖ ≤ ‖u - D a‖ + ‖D a - w‖ := by
        simpa only [dist_eq_norm] using dist_triangle u (D a) w
      _ ≤ ε + ε := add_le_add (by simpa only [norm_sub_rev u (D a)] using hu) hw
      _ = 2 * ε := (two_mul ε).symm
  change ‖∑' i, E i‖ ≤ _ ∧ ‖∑' i, O i‖ ≤ _ ∧ ‖∑' i, F i‖ ≤ _
  rw [hEqE, hEqO, hEqF]
  exact ⟨hpair hat hleft, hpair hright hat, hpair hright hleft⟩

/-- If continuous finite-cutoff diagonals approximate the signed strip trace near the width
with vanishing uniform error, the full edge contribution is zero. The neighborhood on which
the error is uniform may depend on the cutoff. -/
theorem spectralStripTrace_edgeMass_eq_zero_of_vanishingWidthError {ι κ : Type*}
    (x : ι → ℝ) (v : ι → ℂ) (m : ι → ℕ) (h : Summable (fun i ↦ (m i : ℝ) * ‖v i‖))
    {a : ℝ} (ha : 0 < a) (s : ℝ) {l : Filter κ} [NeBot l]
    (D : κ → ℝ → ℂ) (ε : κ → ℝ) (hε : Tendsto ε l (𝓝 0)) :
    let T (b : ℝ) := ∑' i, (spectralStripMultiplicity b s (x i) (m i) : ℂ) * v i
    (∀ᶠ k in l, ContinuousAt (D k) a ∧ ∀ᶠ b in 𝓝 a, ‖D k b - T b‖ ≤ ε k) →
      (∑' i, if |x i| = a then (m i : ℂ) * v i else 0) = 0 := by
  intro T hnear
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have ht : Tendsto (fun k ↦ 2 * ε k) l (𝓝 0) := by
    simpa only [mul_zero] using hε.const_mul (2 : ℝ)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ht
  filter_upwards [hnear] with k hk
  exact (spectralStripTrace_edgeJump_le_two_mul_uniformError x v m h ha s
    (D k) hk.1 (ε k) hk.2).2.2

end RiemannMasullo
