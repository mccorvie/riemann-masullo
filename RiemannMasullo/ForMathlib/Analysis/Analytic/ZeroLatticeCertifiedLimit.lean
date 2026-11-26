module

public import RiemannMasullo.ForMathlib.Analysis.Analytic.ZeroLatticeCertified
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Passing a nonnegative whole-axis lattice limit to certified data

Exact compact convergence and exact whole-axis convergence suffice once the conservative
rule recovers every compact test. The exact finite sum gives the upper bound at each mesh.
-/

public noncomputable section

open Filter Set Topology
namespace RiemannMasullo.AnalyticLattice

private def cut (r : ℕ) (x : ℝ) : ℝ := max 0 (min 1 ((r : ℝ)+1-|x|))
private lemma cut_le (r : ℕ) (x : ℝ) : cut r x ≤ 1 := max_le (by norm_num) (min_le_left _ _)
private lemma cut_eq {r : ℕ} {x : ℝ} (hx : |x| ≤ r) : cut r x = 1 := by
  simp [cut, min_eq_left (by linarith : 1 ≤ (r : ℝ)+1-|x|)]
private lemma cut_compact (r : ℕ) : HasCompactSupport (cut r) := by
  apply HasCompactSupport.intro (K := Icc (-(r : ℝ)-1) ((r : ℝ)+1)) isCompact_Icc
  intro t ht
  have hh : (r : ℝ)+1 < |t| := by
    by_contra! h
    exact ht ⟨by linarith [(abs_le.mp h).1], (abs_le.mp h).2⟩
  simp [cut, max_eq_left ((min_le_right _ _).trans (by linarith : (r : ℝ)+1-|t| ≤ 0))]

/-- A nonnegative exact whole-axis zero sum is inherited by the conservative table with
the same limit. The compact and whole-axis targets may already have been reindexed. -/
theorem tendsto_certifiedSum_nonnegative_of_exact {ι : Type*} {f : ℝ → ℂ} {A : ℕ → ℤ → ℝ}
    (hA : AccurateMagnitudes f A) (hf : ∀ t, AnalyticAt ℝ f t)
    (hfin : ∀ t, analyticOrderAt f t ≠ ⊤) (q m : ι → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hcompact : ∀ v : ℝ → ℝ, Continuous v → HasCompactSupport v →
      Tendsto (sampleSum f v) atTop (𝓝 (∑' i, m i * v (q i))))
    {g : ℝ → ℝ} (hg : Continuous g) (hgn : ∀ t, 0 ≤ g t)
    (hexact : Tendsto (sampleSum f g) atTop (𝓝 (∑' i, m i * g (q i)))) :
    Tendsto (certifiedSum A g) atTop (𝓝 (∑' i, m i * g (q i))) := by
  classical
  have hupper : ∀ᶠ n : ℕ in atTop, certifiedSum A g n ≤ sampleSum f g n :=
    (eventually_gt_atTop (0 : ℕ)).mono fun n hn ↦ certifiedSum_le hA hgn hn
  by_cases hs : Summable (fun i ↦ m i * g (q i))
  · let G (r : ℕ) (t : ℝ) := cut r t * g t
    have hGc (r : ℕ) : Continuous (G r) := by dsimp [G,cut]; fun_prop
    have hGK (r : ℕ) : HasCompactSupport (G r) := (cut_compact r).mul_right
    have hGl (r : ℕ) (t : ℝ) : G r t ≤ g t :=
      mul_le_of_le_one_left (hgn t) (cut_le r t)
    have hGn (r : ℕ) (t : ℝ) : 0 ≤ G r t := mul_nonneg (le_max_left _ _) (hgn t)
    have hmass : Tendsto (fun r : ℕ ↦ ∑' i, m i * G r (q i)) atTop (𝓝 (∑' i, m i * g (q i))) := by
      apply tendsto_tsum_of_dominated_convergence hs
      · intro i
        apply tendsto_const_nhds.congr'
        filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop |q i|)] with r hr
        simp [G,cut_eq hr]
      · filter_upwards with r i
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hm i) (hGn _ _))]
        exact mul_le_mul_of_nonneg_left (hGl _ _) (hm i)
    have hcut (r : ℕ) : Tendsto (certifiedSum A (G r)) atTop (𝓝 (∑' i, m i * G r (q i))) := by
      have h := tendsto_nhds_unique (tendsto_sampleSum (f := f) (hGc r) (hGK r)
        (fun t _ ↦ hf t) (fun t _ ↦ hfin t)) (hcompact _ (hGc r) (hGK r))
      rw [← h]
      exact tendsto_certifiedSum hA (hGc r) (hGK r) (fun t _ ↦ hf t) (fun t _ ↦ hfin t)
    apply tendsto_order.mpr
    refine ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
    · obtain ⟨r, hr⟩ := (hmass.eventually_const_lt ha).exists
      filter_upwards [(hcut r).eventually_const_lt hr] with n hn
      exact hn.trans_le (certifiedSum_mono A (hGl r) n)
    · filter_upwards [hupper,hexact.eventually_lt_const ha] with n hn hn'
      exact hn.trans_lt hn'
  · rw [tsum_eq_zero_of_not_summable hs] at hexact ⊢
    apply squeeze_zero' _ hupper hexact
    exact Eventually.of_forall fun n ↦ certifiedSum_nonneg A hgn n

end RiemannMasullo.AnalyticLattice
