module

public import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.CanonicalDecomposition

/-! # Bounded holomorphic functions with zeros in a compact subset of a disk -/

public section
open Complex Metric Set
open scoped ComplexConjugate
namespace Complex

private noncomputable def diskFactor (R : ℝ) (a z : ℂ) : ℂ :=
  R * (z - a) / ((R : ℂ) ^ 2 - conj a * z)

private theorem diskFactor_gap (R : ℝ) (a z : ℂ) :
    normSq ((R : ℂ) ^ 2 - conj a * z) - normSq ((R : ℂ) * (z - a)) =
      (R ^ 2 - normSq a) * (R ^ 2 - normSq z) := by
  simp [normSq_apply, sq, mul_re, mul_im, sub_re, sub_im]
  ring

private theorem diskFactor_lt {R : ℝ} {a z : ℂ} (ha : a ∈ ball 0 R) (hz : z ∈ ball 0 R) :
    ‖diskFactor R a z‖ < 1 := by
  rw [mem_ball_zero_iff] at ha hz
  have h₁ : 0 < R ^ 2 - normSq a := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have h₂ : 0 < R ^ 2 - normSq z := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have h := (diskFactor_gap R a z).symm ▸ mul_pos h₁ h₂
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at h
  have hlt : ‖(R : ℂ) * (z - a)‖ < ‖(R : ℂ) ^ 2 - conj a * z‖ := by
    nlinarith [norm_nonneg ((R : ℂ) * (z - a)), norm_nonneg ((R : ℂ) ^ 2 - conj a * z)]
  simpa [diskFactor, norm_div] using (div_lt_one ((norm_nonneg _).trans_lt hlt)).mpr hlt

private theorem diskFactor_den {R : ℝ} {a z : ℂ} (ha : a ∈ ball 0 R) (hz : z ∈ closedBall 0 R) :
    (R : ℂ) ^ 2 - conj a * z ≠ 0 := by
  rw [mem_ball_zero_iff] at ha
  rw [mem_closedBall_zero_iff] at hz
  have hR := (norm_nonneg a).trans_lt ha
  have hlt : ‖conj a * z‖ < ‖(R : ℂ) ^ 2‖ := by
    rw [norm_mul, norm_conj, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hR, sq]
    exact (mul_le_mul_of_nonneg_left hz (norm_nonneg a)).trans_lt (mul_lt_mul_of_pos_right ha hR)
  exact sub_ne_zero.mpr (fun e ↦ hlt.ne (congrArg norm e.symm))

private theorem finite_disk_factors (R : ℝ) (S : Finset ℂ) (f : ℂ → ℂ) {M q : ℝ}
    (hR : 0 < R) (hq : 0 ≤ q) (w : ℂ) (hw : w ∈ ball 0 R)
    (ha : AnalyticOnNhd ℂ f (closedBall 0 R)) (hbound : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M)
    (hS : ∀ a ∈ S, a ∈ ball (0 : ℂ) R ∧ f a = 0 ∧ ‖diskFactor R a w‖ ≤ q) :
    ‖f w‖ ≤ M * q ^ S.card := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty =>
    simp only [Finset.card_empty, pow_zero, mul_one]
    exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (ha.differentiableOn.diffContOnCl_ball Subset.rfl)
      (fun z hz ↦ hbound z (frontier_ball_subset_sphere hz)) (subset_closure hw)
  | @insert a S haS ih =>
    obtain ⟨haR, hfa, hwq⟩ := hS a (Finset.mem_insert_self ..)
    let G (z : ℂ) := (((R : ℂ) ^ 2 - conj a * z) / R) * dslope f a z
    have hfac (z : ℂ) (hz : z ∈ closedBall 0 R) : diskFactor R a z * G z = f z := by
      have hfz := sub_smul_dslope f a z
      rw [smul_eq_mul, hfa, sub_zero] at hfz
      rw [← hfz]
      dsimp [G, diskFactor]
      have hd := diskFactor_den haR hz
      generalize he : (R : ℂ) ^ 2 - conj a * z = d at hd ⊢
      field_simp [hd, hR.ne']
    have hGa : AnalyticOnNhd ℂ G (closedBall 0 R) := by
      intro z hz
      exact (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).div_const.mul
        ((ha.dslope a) z hz)
    have hGb (z : ℂ) (hz : z ∈ sphere (0 : ℂ) R) : ‖G z‖ ≤ M := by
      have hn := norm_canonicalFactor_eval_circle_eq_one haR hz
      have hrev : ‖diskFactor R a z‖ = 1 := by
        have he : diskFactor R a z = (canonicalFactor R a z)⁻¹ := by
          simp only [diskFactor, canonicalFactor_apply, inv_div]
        rw [he, norm_inv, hn, inv_one]
      have h := congrArg norm (hfac z (sphere_subset_closedBall hz))
      simpa [norm_mul, hrev] using h.trans_le (hbound z hz)
    have hGz (z : ℂ) (hz : z ∈ S) : z ∈ ball 0 R ∧ G z = 0 ∧ ‖diskFactor R z w‖ ≤ q := by
      obtain ⟨hzR, hfz, hzq⟩ := hS z (Finset.mem_insert_of_mem hz)
      refine ⟨hzR, ?_, hzq⟩
      have hne : z ≠ a := fun e ↦ haS (e ▸ hz)
      have hne' : diskFactor R a z ≠ 0 :=
        div_ne_zero (mul_ne_zero (by exact_mod_cast hR.ne') (sub_ne_zero.mpr hne))
          (diskFactor_den haR (ball_subset_closedBall hzR))
      exact (mul_eq_zero.mp ((hfac z (ball_subset_closedBall hzR)).trans hfz)).resolve_left hne'
    rw [← hfac w (ball_subset_closedBall hw), norm_mul, Finset.card_insert_of_notMem haS, pow_succ]
    exact (mul_le_mul hwq (ih G hGa hGb hGz) (norm_nonneg _) hq).trans_eq (by ring)

/-- Zeros in a compact subset of the open unit disk force geometric decay at
any fixed interior point, uniformly over bounded analytic functions. -/
theorem exists_geometric_bound_of_zeros_in_compact {K : Set ℂ} (hK : IsCompact K)
    (hKin : K ⊆ ball 0 1) {w : ℂ} (hw : w ∈ ball 0 1) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ (S : Finset ℂ), ↑S ⊆ K → ∀ (f : ℂ → ℂ) (M : ℝ),
      AnalyticOnNhd ℂ f (ball 0 1) → (∀ u ∈ ball (0 : ℂ) 1, ‖f u‖ ≤ M) →
      (∀ u ∈ S, f u = 0) → ‖f w‖ ≤ M * q ^ S.card := by
  let J := insert w K
  have hJ : IsCompact J := hK.insert w
  have hwJ : w ∈ J := mem_insert w K
  have hin : J ⊆ ball 0 1 := insert_subset hw hKin
  obtain ⟨b, hb, hbmax⟩ := hJ.exists_isMaxOn ⟨w, hwJ⟩ (continuous_norm.continuousOn (s := J))
  obtain ⟨R, hbR, hR1⟩ := exists_between (mem_ball_zero_iff.mp (hin hb))
  have hR := (norm_nonneg b).trans_lt hbR
  have hJR {z : ℂ} (hz : z ∈ J) : z ∈ ball 0 R := mem_ball_zero_iff.mpr ((hbmax hz).trans_lt hbR)
  have hc : ContinuousOn (fun a : ℂ ↦ ‖diskFactor R a w‖) J := by
    apply ContinuousOn.norm
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro a ha
      exact diskFactor_den (hJR ha) (ball_subset_closedBall (hJR hwJ))
  obtain ⟨a, ha, hamax⟩ := hJ.exists_isMaxOn ⟨w, hwJ⟩ hc
  refine ⟨_, norm_nonneg _, diskFactor_lt (hJR ha) (hJR hwJ), fun S hS f M hf hbound hzero ↦ ?_⟩
  have hclosed : closedBall (0 : ℂ) R ⊆ ball 0 1 := closedBall_subset_ball hR1
  exact finite_disk_factors R S f hR (norm_nonneg _) w (hJR hwJ) (hf.mono hclosed)
    (fun z hz ↦ hbound z (hclosed (sphere_subset_closedBall hz)))
    (fun z hz ↦ ⟨hJR (mem_insert_of_mem _ (hS hz)), hzero z hz,
      hamax (mem_insert_of_mem _ (hS hz))⟩)

end Complex
