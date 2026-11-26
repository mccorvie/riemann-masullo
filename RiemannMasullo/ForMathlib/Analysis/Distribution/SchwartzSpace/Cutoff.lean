module
public import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public noncomputable section
open Filter Function Metric Set Finset
open scoped SchwartzMap Topology ContDiff
namespace RiemannMasullo

/-- Every Schwartz seminorm of a rescaled cutoff error decays by any prescribed
power of the inverse radius. This strengthens Mathlib's compact-cutoff density
estimate by spending the corresponding higher weighted seminorms. -/
theorem schwartz_cutoff_rapid_seminorm
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (h1 : ∀ x ∈ ball (0 : ℝ) 1, φ x = 1) (f : 𝓢(ℝ, ℂ)) (k n N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ‖ε‖ ≤ 1 →
      SchwartzMap.seminorm ℝ k n (SchwartzMap.smulLeftCLM (𝕜 := ℝ) ℂ (fun x ↦ φ (ε • x)) f - f) ≤ C * ‖ε‖ ^ N := by
  obtain ⟨A, hA0, hA⟩ := hc.exists_bound_iteratedFDeriv hφ n
  have hψ : ∀ i ≤ n, ∀ y, ‖iteratedFDeriv ℝ i (fun z ↦ φ z - 1) y‖ ≤ A + 1 := by
    rintro (- | i) hi y
    · grind [norm_iteratedFDeriv_zero, norm_sub_le, norm_one, hA 0 hi y]
    · rw [fun_iteratedFDeriv_sub_apply (hφ.contDiffAt.of_le (mod_cast le_top)) contDiffAt_const,
        iteratedFDeriv_succ_const, Pi.zero_apply, sub_zero]
      linarith [hA _ hi y]
  let C := ∑ i ∈ range (n + 1), (n.choose i : ℝ) * (A + 1) * SchwartzMap.seminorm ℝ (k + N) (n - i) f
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ ↦ by positivity
  refine ⟨C, hC, fun ε hε ↦ ?_⟩
  have hg : ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i (fun y ↦ φ (ε • y) - 1) x‖ ≤ A + 1 := by
    intro i hi x
    rw [iteratedFDeriv_comp_const_smul (f := fun z ↦ φ z - 1) _
      ((hφ.sub contDiff_const).of_le (mod_cast le_top)), norm_smul, norm_pow]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hε)).trans (hψ i hi _)
  have hsmul : ⇑(SchwartzMap.smulLeftCLM (𝕜 := ℝ) ℂ (fun x ↦ φ (ε • x)) f - f) =
      fun x ↦ (φ (ε • x) - 1) • f x := by
    ext x
    rw [sub_apply, SchwartzMap.smulLeftCLM_apply_apply
      (show (fun x : ℝ ↦ φ (ε • x)).HasTemperateGrowth by fun_prop)]
    rw [sub_smul, one_smul]
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (mul_nonneg hC (pow_nonneg (norm_nonneg _) _))
  intro x
  rw [hsmul]
  rcases lt_or_ge ‖ε • x‖ 1 with hx | hx
  · have hz : (fun y ↦ (φ (ε • y) - 1) • f y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [(isOpen_ball.preimage (continuous_const_smul ε)).mem_nhds
        (mem_ball_zero_iff.mpr hx)] with y hy
      rw [h1 (ε • y) hy, sub_self, zero_smul]
      rfl
    have he : ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y ↦ (φ (ε • y) - 1) • f y) x‖ = 0 := by
      rw [(hz.iteratedFDeriv ℝ n).eq_of_nhds]
      simp
    rw [he]
    positivity
  · rw [norm_smul] at hx
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y ↦ (φ (ε • y) - 1) • f y) x‖ ≤
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y ↦ (φ (ε • y) - 1) • f y) x‖) *
            (‖ε‖ * ‖x‖) ^ N :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hx)
      _ = ‖ε‖ ^ N * (‖x‖ ^ (k + N) *
          ‖iteratedFDeriv ℝ n (fun y ↦ (φ (ε • y) - 1) • f y) x‖) := by
        rw [mul_pow, pow_add]; ring
      _ ≤ ‖ε‖ ^ N * ∑ i ∈ range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y ↦ φ (ε • y) - 1) x‖ *
          (‖x‖ ^ (k + N) * ‖iteratedFDeriv ℝ (n - i) f x‖) := by
        grw [norm_iteratedFDeriv_smul_le (by fun_prop) (f.smooth ⊤) x (mod_cast le_top)]
        simp only [mul_sum]
        exact le_of_eq (sum_congr rfl fun _ _ ↦ by ring)
      _ ≤ ‖ε‖ ^ N * C := by
        dsimp only [C]
        gcongr with i hi
        · exact hg i (by grind) x
        · exact SchwartzMap.le_seminorm ℝ _ _ f x
      _ = C * ‖ε‖ ^ N := mul_comm _ _

/-- Every continuous linear image of a Schwartz cutoff error has arbitrary
polynomial decay in the inverse cutoff radius. -/
theorem schwartz_cutoff_rapid_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (h1 : ∀ x ∈ ball (0 : ℝ) 1, φ x = 1) (f : 𝓢(ℝ, ℂ))
    (T : 𝓢(ℝ, ℂ) →L[ℝ] E) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ‖ε‖ ≤ 1 →
      ‖T (SchwartzMap.smulLeftCLM (𝕜 := ℝ) ℂ (fun x ↦ φ (ε • x)) f - f)‖ ≤ C * ‖ε‖ ^ N := by
  let q : Seminorm ℝ 𝓢(ℝ, ℂ) := (normSeminorm ℝ E).comp T.toLinearMap
  obtain ⟨s, c, _, hq⟩ := Seminorm.bound_sum_of_continuous
    (schwartz_withSeminorms ℝ ℝ ℂ) q (continuous_norm.comp T.continuous)
  choose C hC0 hC using fun i : ℕ × ℕ ↦ schwartz_cutoff_rapid_seminorm φ hφ hc h1 f i.1 i.2 N
  refine ⟨(c : ℝ) * ∑ i ∈ s, C i, mul_nonneg c.coe_nonneg (sum_nonneg fun i _ ↦ hC0 i),
    fun ε hε ↦ ?_⟩
  let g := SchwartzMap.smulLeftCLM (𝕜 := ℝ) ℂ (fun x ↦ φ (ε • x)) f - f
  have hh := hq g
  simp only [smul_apply, sum_apply, NNReal.smul_def, smul_eq_mul] at hh
  change ‖T g‖ ≤ (c : ℝ) * ∑ i ∈ s, SchwartzMap.seminorm ℝ i.1 i.2 g at hh
  refine hh.trans ?_
  calc
    _ ≤ (c : ℝ) * ∑ i ∈ s, C i * ‖ε‖ ^ N :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun i _ ↦ hC i ε hε) c.coe_nonneg
    _ = _ := by rw [← sum_mul, mul_assoc]


/-- A Schwartz function admits compact frequency cutoffs of radius `2(n+1)`
whose error under any fixed continuous linear map decays faster than every
inverse power of `n+1`. -/
theorem schwartz_exists_rapid_compact_cutoffs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : 𝓢(ℝ, ℂ)) (T : 𝓢(ℝ, ℂ) →L[ℝ] E) :
    ∃ q : ℕ → 𝓢(ℝ, ℂ),
      (∀ n t, q n t ≠ 0 → |t| < 2 * ((n : ℝ) + 1)) ∧
      Tendsto (fun n ↦ T (q n)) atTop (𝓝 (T f)) ∧
      ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
        ‖T (q n - f)‖ ≤ C / ((n : ℝ) + 1) ^ N := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hbGrowth : (b : ℝ → ℝ).HasTemperateGrowth := b.hasCompactSupport.hasTemperateGrowth b.contDiff
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  let q (n : ℕ) := SchwartzMap.smulLeftCLM (𝕜 := ℝ) ℂ (fun x ↦ b (ε n • x)) f
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε1 (n : ℕ) : ‖ε n‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hε n).le]
    exact (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  refine ⟨q, ?_, ?_, fun N ↦ ?_⟩
  · intro n t ht
    have hb : b (ε n • t) ≠ 0 := by
      intro hz
      apply ht
      rw [SchwartzMap.smulLeftCLM_apply_apply
        (show (fun x : ℝ ↦ b (ε n • x)).HasTemperateGrowth by fun_prop)]
      rw [hz, zero_smul]
    have hball : ε n • t ∈ ball (0 : ℝ) 2 := by
      change ε n • t ∈ ball (0 : ℝ) b.rOut
      rw [← b.support_eq]
      exact hb
    have hh : ε n * |t| < 2 := by
      simpa only [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (hε n).le,
        Real.norm_eq_abs] using hball
    dsimp [ε] at hh
    rw [one_div, ← div_eq_inv_mul] at hh
    exact (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mp hh
  · have hq := SchwartzMap.tendsto_smulLeftCLM_comp_smul b.contDiff b.hasCompactSupport b.eventuallyEq_one f
    exact T.continuous.tendsto f |>.comp (hq.comp tendsto_one_div_add_atTop_nhds_zero_nat)
  · obtain ⟨C, hC, hbound⟩ := schwartz_cutoff_rapid_image b b.contDiff b.hasCompactSupport
      (fun x hx ↦ b.one_of_mem_closedBall (ball_subset_closedBall hx)) f T N
    refine ⟨C, hC, fun n ↦ ?_⟩
    have hh := hbound (ε n) (hε1 n)
    rw [Real.norm_of_nonneg (hε n).le] at hh
    simpa only [q, ε, one_div, one_mul, inv_pow, div_eq_mul_inv] using hh

end RiemannMasullo
