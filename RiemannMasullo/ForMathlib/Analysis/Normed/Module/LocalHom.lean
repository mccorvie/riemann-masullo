module

public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Extending additive maps on balls -/

public section

open Filter Metric Set Topology

namespace RiemannMasullo

/-- A function on a real normed space that is additive whenever the two summands and their
sum belong to a ball about zero agrees there with a global additive homomorphism. -/
theorem exists_addMonoidHom_eqOn_ball_of_local_additive {E A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup A] {r : ℝ} (hr : 0 < r)
    (σ : E → A) (hadd : ∀ x y, ‖x‖ < r → ‖y‖ < r → ‖x + y‖ < r →
      σ (x + y) = σ x + σ y) : ∃ f : E →+ A, EqOn f σ (ball 0 r) := by
  let half (n : ℕ) (x : E) := ((1 / 2 : ℝ) ^ n) • x
  let value (n : ℕ) (x : E) := (2 ^ n : ℕ) • σ (half n x)
  have hnorm (x : E) (n : ℕ) : ‖half n x‖ = (1 / 2 : ℝ) ^ n * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have hsmall (x : E) : ∀ᶠ n in atTop, ‖half n x‖ < r := by
    have hlim : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n * ‖x‖) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).mul_const ‖x‖
    simpa only [hnorm] using hlim.eventually_lt_const hr
  have hmono (x : E) : Antitone fun n ↦ ‖half n x‖ := by
    intro n m hnm
    change ‖half m x‖ ≤ ‖half n x‖
    rw [hnorm, hnorm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) hnm)
      (norm_nonneg x)
  -- Once the halved vector enters the ball, further halving gives the same value.
  have hstep (x : E) (n : ℕ) (hn : ‖half n x‖ < r) : value n x = value (n + 1) x := by
    have hs := (hmono x (Nat.le_succ n)).trans_lt hn
    have heq : half (n + 1) x + half (n + 1) x = half n x := by
      simp only [half, ← add_smul, pow_succ]
      congr 1
      ring
    have h := hadd _ _ hs hs (heq.symm ▸ hn)
    rw [heq, ← two_nsmul] at h
    simp only [value, pow_succ', mul_nsmul, h]
  have hstable (x : E) (n m : ℕ) (hn : ‖half n x‖ < r) (hnm : n ≤ m) :
      value n x = value m x := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih => exact ih.trans (hstep x m ((hmono x hnm).trans_lt hn))
  classical
  choose N hN using fun x ↦ (eventually_atTop.mp (hsmall x))
  let f (x : E) := value (N x) x
  have hf (x : E) (n : ℕ) (hn : ‖half n x‖ < r) : f x = value n x :=
    (hstable x (N x) (max (N x) n) (hN x _ le_rfl) (le_max_left _ _)).trans
      (hstable x n (max (N x) n) hn (le_max_right _ _)).symm
  refine ⟨AddMonoidHom.mk' f ?_, ?_⟩
  · intro x y
    obtain ⟨n, hn⟩ := ((hsmall x).and ((hsmall y).and (hsmall (x + y)))).exists
    have hsum : half n (x + y) = half n x + half n y := smul_add ..
    rw [hf x n hn.1, hf y n hn.2.1, hf (x + y) n hn.2.2]
    simp only [value, hsum, hadd _ _ hn.1 hn.2.1 (hsum ▸ hn.2.2), nsmul_add]
  · intro x hx
    simpa [half, value] using hf x 0 (by simpa [half] using mem_ball_zero_iff.mp hx)

end RiemannMasullo
