module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.FractionalModelCardinal
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.LpCardinal
public import Mathlib.Analysis.InnerProductSpace.Dual

@[expose] public noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace RiemannMasullo

variable {I J H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The exact norm of a physical observation follows from a unitary Fourier model. -/
theorem norm_probe_of_fractional_model {θ c : ℝ} (hθ : 1 / 2 < θ) (hc : 0 ≤ c)
    (U : H ≃ₗᵢ[ℂ] lp (fun _ : I ↦ Lp ℂ 2 (volume : Measure ℝ)) 2)
    (E : I → ℝ → StrongDual ℂ H)
    (hU : ∀ i t w, E i t w = c • fractionalSynthesis θ (U w i) t) (i : I) (t : ℝ) :
    ‖E i t‖ = c * ‖fractionalProbe θ hθ 0‖ := by
  classical
  let p := U.symm (lp.single (E := fun _ : I ↦ Lp ℂ 2 (volume : Measure ℝ)) 2 i
    (c • fractionalProbe θ hθ t))
  have he : E i t = InnerProductSpace.toDual ℂ H p := by
    apply ContinuousLinearMap.ext
    intro w
    rw [InnerProductSpace.toDual_apply_apply, ← U.inner_map_map]
    change E i t w = ⟪U (U.symm _), U w⟫_ℂ
    rw [U.apply_symm_apply, lp.inner_single_left, inner_smul_left_eq_smul,
      fractionalProbe_inner hθ, hU]
  rw [he, (InnerProductSpace.toDual ℂ H).norm_map]
  change ‖U.symm _‖ = _
  rw [U.symm.norm_map, lp.norm_single (by norm_num), norm_smul, Real.norm_eq_abs, abs_of_nonneg hc,
    fractionalProbe_norm_eq hθ]

/-- The uniform fractional cardinal bound controls actual residual rows whenever a
unitary model identifies the observations and the selected vector is the orthogonal
interpolant. The normalization cancels from the row cost. -/
theorem fractional_model_cardinal_row_sq_le {θ c : ℝ} (hθ : 1 / 2 < θ) (hθ₁ : θ < 1)
    (hc : 0 < c)
    (U : H ≃ₗᵢ[ℂ] lp (fun _ : I ↦ Lp ℂ 2 (volume : Measure ℝ)) 2)
    (E : I → ℝ → StrongDual ℂ H)
    (hU : ∀ i t w, E i t w = c • fractionalSynthesis θ (U w i) t)
    (site : J → I × ℝ) (j : J) (w r : H)
    (hwj : E (site j).1 (site j).2 w = 1)
    (hw : ∀ k, k ≠ j → E (site k).1 (site k).2 w = 0)
    (horth : ∀ v : H, (∀ k, E (site k).1 (site k).2 v = 0) → ⟪w, v⟫_ℂ = 0)
    (b : I → ℝ → ℂ)
    (hr : ∀ i t, E i t r = b i t * E i t w)
    {A : ℝ} (hA : 0 ≤ A) {B L : NNReal}
    (hB : ∀ x, ‖b (site j).1 x‖ ≤ B) (hb : LipschitzWith L (b (site j).1))
    (bz : b (site j).1 (site j).2 = 0)
    (hbw : ∀ x y, ‖b (site j).1 x - b (site j).1 y‖ ≤ A * |x - y| *
      Real.exp ((|x - (site j).2| + |y - (site j).2|) / 8)) :
    (‖E (site j).1 (site j).2‖ * ‖r‖) ^ 2 ≤
      ‖fractionalProbe θ hθ 0‖ ^ 2 * (8 * θ * ((2 : ℝ) ^ (θ - 1 / 2)) ^ 2 * A ^ 2) := by
  classical
  let ω := (site j).1
  let z := (site j).2
  let S : Set ℝ := {t | ∃ k, k ≠ j ∧ site k = (ω, t)}
  let v : Lp ℂ 2 (volume : Measure ℝ) := c • U w ω
  let u : Lp ℂ 2 (volume : Measure ℝ) := c • U r ω
  have hprofile (q : H) (i : I) (t : ℝ) :
      fractionalSynthesis θ (c • U q i) t = E i t q := by
    rw [← fractionalProbe_inner hθ, inner_smul_right_eq_smul, fractionalProbe_inner hθ, hU]
  have hmodelorth : ∀ q : lp (fun _ : I ↦ Lp ℂ 2 (volume : Measure ℝ)) 2,
      (∀ k, fractionalSynthesis θ (q (site k).1) (site k).2 = 0) → ⟪U w, q⟫_ℂ = 0 := by
    intro q hq
    rw [← U.apply_symm_apply q, U.inner_map_map]
    apply horth
    intro k
    rw [hU, U.apply_symm_apply, hq k, smul_zero]
  have hlocalorth : ∀ q : Lp ℂ 2 (volume : Measure ℝ),
      fractionalSynthesis θ q z = 0 → (∀ t ∈ S, fractionalSynthesis θ q t = 0) → ⟪v, q⟫_ℂ = 0 := by
    intro q qz qS
    have he := hmodelorth (lp.single (E := fun _ : I ↦ Lp ℂ 2 (volume : Measure ℝ)) 2 ω q) (by
      intro k
      by_cases hi : (site k).1 = ω
      · rw [hi, lp.single_apply_self]
        by_cases hk : k = j
        · subst k
          exact qz
        · exact qS (site k).2 ⟨k, hk, Prod.ext hi rfl⟩
      · rw [lp.single_apply_ne _ _ _ hi, ← fractionalProbe_inner hθ, inner_zero_right])
    rw [lp.inner_single_right] at he
    change ⟪c • U w ω, q⟫_ℂ = 0
    rw [inner_smul_left_eq_smul, he, smul_zero]
  have hvoff (i : I) (hi : i ≠ ω) : U w i = 0 := by
    apply lp_cardinal_support (range site) (fractionalProbe θ hθ) (U w) ω
    · intro k t ht hki
      obtain ⟨a, ha⟩ := ht
      have haj : a ≠ j := by
        intro h
        subst a
        exact hki (congrArg Prod.fst ha).symm
      have he := hw a haj
      rw [hU, ha, smul_eq_zero] at he
      rw [fractionalProbe_inner hθ]
      exact he.resolve_left hc.ne'
    · intro q hq
      apply hmodelorth q
      intro k
      rw [← fractionalProbe_inner hθ]
      exact hq (site k).1 (site k).2 (mem_range_self k)
    · exact hi
  have hroff (i : I) (hi : i ≠ ω) : U r i = 0 := by
    apply fractionalProbe_separates hθ
    intro t
    have hwzero : E i t w = 0 := by
      rw [hU, hvoff i hi, ← fractionalProbe_inner hθ, inner_zero_right, smul_zero]
    have he := hr i t
    rw [hwzero, mul_zero, hU, smul_eq_zero] at he
    rw [fractionalProbe_inner hθ]
    exact he.resolve_left hc.ne'
  have hsingle : U r = lp.single (E := fun _ : I ↦ Lp ℂ 2 (volume : Measure ℝ)) 2 ω (U r ω) := by
    apply lp.ext
    funext i
    by_cases hi : i = ω
    · subst i
      rw [lp.single_apply_self]
    · rw [lp.single_apply_ne _ _ _ hi, hroff i hi]
  have hn : ‖u‖ = c * ‖r‖ := by
    change ‖c • U r ω‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, ← U.norm_map r, hsingle, lp.norm_single (by norm_num), lp.single_apply_self]
  have he := fractionalSynthesis_cardinal_residual_norm_sq_le hθ hθ₁ S z v u
    (by exact (hprofile w ω z).trans hwj)
    (by
      intro t ht
      obtain ⟨k, hk, he⟩ := ht
      have hh := hw k hk
      rw [he] at hh
      exact (hprofile w ω t).trans hh)
    hlocalorth hA hB hb bz hbw (by
      funext t
      change fractionalSynthesis θ (c • U r ω) t = fractionalSynthesis θ (c • U w ω) t * b ω t
      rw [hprofile, hprofile, hr, mul_comm])
  have hcost : ‖E (site j).1 (site j).2‖ * ‖r‖ = ‖fractionalProbe θ hθ 0‖ * ‖u‖ := by
    rw [norm_probe_of_fractional_model hθ hc.le U E hU, hn]
    ring
  rw [hcost, mul_pow]
  exact mul_le_mul_of_nonneg_left he (sq_nonneg _)

end RiemannMasullo
