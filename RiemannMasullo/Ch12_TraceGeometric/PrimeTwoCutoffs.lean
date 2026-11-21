module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Prime 2 cutoffs

Section 12.4, footnote 2 on p. 514 asks what happens to (12.4.1.23) when the physical norm window has a lower endpoint. For the symmetric window of radius `L` and Fourier cutoff `B`, the integral is `J (L * B) - J (B / L)`, where `J` is the one-sided integral. The first two lemmas derive the subtraction from the length of the log interval. The limit lemmas take the endpoint values of `J` as hypotheses.

For the rational test supported at norms between `3/2` and `5/2`, the only signed dyadic frequency in the support of the inverted real test is `1/2`. Its signed 2-adic shell weights have mass zero and first moment `1/2`. The last lemma computes what survives from the logarithmic term when the test has value one at norm two. Identifying the local Fourier integral with the global strip trace is the separate comparison in §12.3.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Topology

namespace RiemannMasullo.PrimeTwoCutoffs

/-- Paper: Equation (12.4.1.23), p. 518. Deviation: impose the lower physical endpoint proposed on p. 514. With log endpoints `-c` and `a`, log Fourier cutoff `b` and log product norm `s`, the length is the difference of two positive parts. -/
theorem annularLogLength (a b c s : ℝ) (hac : 0 ≤ a + c) :
    max 0 (a - max (s - b) (-c)) = max 0 (a + b - s) - max 0 (b - c - s) := by
  by_cases hs : s - b ≤ -c
  · rw [max_eq_right hs, max_eq_right (by linarith : 0 ≤ a - -c),
      max_eq_right (by linarith : 0 ≤ a + b - s), max_eq_right (by linarith : 0 ≤ b - c - s)]
    ring
  · rw [max_eq_left (le_of_not_ge hs), max_eq_left (by linarith : b - c - s ≤ 0), sub_zero]
    rw [show a - (s - b) = a + b - s by ring]

/-- Integrating the log length against an amplitude gives the difference of the two one-sided integrals. -/
theorem integral_annularLogLength {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} (s : X → ℝ) (f : X → E) (a b c : ℝ) (hac : 0 ≤ a + c)
    (hu : Integrable (fun x ↦ max 0 (a + b - s x) • f x) μ)
    (hl : Integrable (fun x ↦ max 0 (b - c - s x) • f x) μ) :
    (∫ x, max 0 (a - max (s x - b) (-c)) • f x ∂μ) =
      (∫ x, max 0 (a + b - s x) • f x ∂μ) - ∫ x, max 0 (b - c - s x) • f x ∂μ := by
  simp_rw [annularLogLength a b c _ hac, sub_smul]
  exact integral_sub hu hl

/-- A finite prime removal acts as `I - T` on the half-weighted theta space. If `T` preserves a closed subspace and its iterates are summable there, removing the prime preserves the whole subspace. -/
theorem image_sub_of_summable_powers {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : Submodule ℝ E) (hW : IsClosed (W : Set E)) (T : E →L[ℝ] E)
    (hT : ∀ x ∈ W, T x ∈ W) (hs : ∀ x ∈ W, Summable (fun n : ℕ ↦ (T ^ n) x)) :
    (fun x ↦ x - T x) '' (W : Set E) = W := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact W.sub_mem hx (hT x hx)
  · intro x hx
    have hpow (n : ℕ) : (T ^ n) x ∈ W := by
      induction n with
      | zero => simpa using hx
      | succ n ih => simpa [pow_succ', mul_apply_eq_comp] using hT _ ih
    have hsum := hs x hx
    refine ⟨∑' n : ℕ, (T ^ n) x, ?_, ?_⟩
    · apply hW.mem_of_tendsto hsum.hasSum
      exact Filter.Eventually.of_forall fun s ↦ W.sum_mem fun n _ ↦ hpow n
    · change (∑' n : ℕ, (T ^ n) x) - T (∑' n : ℕ, (T ^ n) x) = x
      rw [T.map_tsum hsum]
      apply sub_eq_iff_eq_add.mpr
      simpa [pow_succ', mul_apply_eq_comp] using hsum.tsum_eq_zero_add

/-- A norm cutoff and a bounded retained orbital weight can be removed along any two cofinal sequences on an integrable global diagonal. -/
theorem tendsto_integral_two_cutoffs {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure X} {d : X → E} (hd : Integrable d μ)
    {k w : ℕ → X → ℝ} {v : X → ℝ}
    (hk : ∀ n, Measurable (k n)) (hw : ∀ n, Measurable (w n))
    (hk₁ : ∀ n x, |k n x| ≤ 1) (hw₁ : ∀ n x, |w n x| ≤ 1)
    (hkLim : ∀ x, Tendsto (fun n ↦ k n x) atTop (𝓝 1))
    (hwLim : ∀ x, Tendsto (fun n ↦ w n x) atTop (𝓝 (v x)))
    {p l : ℕ → ℕ} (hp : Tendsto p atTop atTop) (hl : Tendsto l atTop atTop) :
    Tendsto (fun n ↦ ∫ x, (k (l n) x * w (p n) x) • d x ∂μ)
      atTop (𝓝 (∫ x, v x • d x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖d x‖)
  · intro n
    exact ((hk _).mul (hw _)).aestronglyMeasurable.smul hd.aestronglyMeasurable
  · exact hd.norm
  · intro n
    apply Filter.Eventually.of_forall
    intro x
    have hkw : |k (l n) x| * |w (p n) x| ≤ 1 := by
      simpa using mul_le_mul (hk₁ _ _) (hw₁ _ _) (abs_nonneg _) zero_le_one
    rw [norm_smul, Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hkw
  · apply Filter.Eventually.of_forall
    intro x
    simpa using (((hkLim x).comp hl).mul ((hwLim x).comp hp)).smul
      (tendsto_const_nhds (x := d x))

/-- Removing the Fourier cutoff at fixed positive norm radius sends both arguments to infinity. -/
theorem tendsto_fourier_first {J : ℝ → ℝ} {C L : ℝ} (hL : 0 < L)
    (hLarge : Tendsto J atTop (𝓝 C)) :
    Tendsto (fun b : ℝ ↦ J (L * b) - J (b / L)) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun b : ℝ ↦ L * b) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hL).2 tendsto_id
  have h₂ : Tendsto (fun b : ℝ ↦ b / L) atTop atTop :=
    (tendsto_div_const_atTop_of_pos hL).2 tendsto_id
  simpa [Function.comp_def] using (hLarge.comp h₁).sub (hLarge.comp h₂)

/-- Removing the norm cutoff at fixed positive Fourier radius sends the second argument to zero from the right. -/
theorem tendsto_norm_first {J : ℝ → ℝ} {C B : ℝ} (hB : 0 < B)
    (hSmall : Tendsto J (𝓝[>] 0) (𝓝 0)) (hLarge : Tendsto J atTop (𝓝 C)) :
    Tendsto (fun l : ℝ ↦ J (l * B) - J (B / l)) atTop (𝓝 C) := by
  have h₁ : Tendsto (fun l : ℝ ↦ l * B) atTop atTop :=
    (tendsto_mul_const_atTop_of_pos hB).2 tendsto_id
  have h₂ : Tendsto (fun l : ℝ ↦ B / l) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul B
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with l hl
      exact div_pos hB hl
  simpa [Function.comp_def] using (hLarge.comp h₁).sub (hSmall.comp h₂)

/-- Signed coefficient at valuation `k` in the 2-adic Fourier integral for frequency `1/2`, with the additive measure of `ℤ₂` normalised to one. The coefficients at negative valuations are zero. -/
def shellWeight : ℕ → ℝ
  | 0 => -(1 / 4)
  | n + 1 => 1 / 8 * (1 / 2) ^ n

/-- The weights at frequency `1/2` have total mass zero and first moment one half. -/
theorem shellWeight_moments :
    HasSum shellWeight 0 ∧ HasSum (fun k : ℕ ↦ shellWeight k * k) (1 / 2) := by
  have hg := hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hn := hasSum_coe_mul_geometric_of_norm_lt_one
    (r := (1 / 2 : ℝ)) (by norm_num [Real.norm_eq_abs])
  constructor
  · rw [← hasSum_nat_add_iff' 1]
    have h := hg.mul_left (1 / 8 : ℝ)
    rw [show (1 / 8 : ℝ) * (1 - 1 / 2)⁻¹ = 1 / 4 by norm_num] at h
    simpa [shellWeight] using h
  · rw [← hasSum_nat_add_iff' 1]
    have h := ((hn.add hg).mul_left (1 / 8 : ℝ)).congr_fun
      (g := fun n : ℕ ↦ (1 / 8 : ℝ) * (1 / 2 : ℝ)^n * (n + 1 : ℝ)) (fun n ↦ by ring)
    rw [show (1 / 8 : ℝ) * (1 / 2 / (1 - 1 / 2)^2 + (1 - 1 / 2)⁻¹) = 1 / 2 by norm_num] at h
    simpa [shellWeight] using h

/-- The affine part of the logarithmic asymptote contributes `log 2 / √2` for every log cutoff `t` and every constant term `c`. -/
theorem hasSum_resonantLog (t c : ℝ) :
    HasSum (fun k : ℕ ↦ shellWeight k * (Real.sqrt 2 * (t + k * Real.log 2) + c))
      (Real.log 2 / Real.sqrt 2) := by
  obtain ⟨hm, hmoment⟩ := shellWeight_moments
  have h := ((hm.mul_right (Real.sqrt 2 * t + c)).add
    (hmoment.mul_right (Real.sqrt 2 * Real.log 2))).congr_fun
      (g := fun k : ℕ ↦ shellWeight k * (Real.sqrt 2 * (t + k * Real.log 2) + c)) (fun k ↦ by ring)
  have ht : 0 * (Real.sqrt 2 * t + c) + (1 / 2 : ℝ) * (Real.sqrt 2 * Real.log 2) =
      Real.log 2 / Real.sqrt 2 := by
    apply (eq_div_iff (ne_of_gt (Real.sqrt_pos.2 (by norm_num)))).2
    calc
      _ = Real.log 2 * ((Real.sqrt 2)^2 / 2) := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
  rwa [ht] at h

end RiemannMasullo.PrimeTwoCutoffs
