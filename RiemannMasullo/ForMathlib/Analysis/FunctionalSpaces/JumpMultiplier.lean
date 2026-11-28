module

public import RiemannMasullo.ForMathlib.Analysis.FunctionalSpaces.RealJumpEnergy

/-! # Multipliers of the finite jump-energy domain

Bounded Lipschitz multiplication preserves the local and jump square-integrability when
the jump measure has a finite second moment. This includes the squared-norm multiplier
needed to test the cardinal-interpolant orthogonality relation.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace RiemannMasullo

/-- A bounded Lipschitz multiplier preserves both the local and jump `L²` domains. -/
theorem memLp_mul_and_jump_of_lipschitz (κ : Measure ℝ) {b h : ℝ → ℂ}
    (hh : Measurable h) (hh₂ : MemLp h 2) {B : ℝ} {L : NNReal}
    (hB : ∀ x, ‖b x‖ ≤ B) (hb : LipschitzWith L b)
    (hκ : Integrable (fun r : ℝ ↦ r ^ 2) κ)
    (hj : MemLp (fun p : ℝ × ℝ ↦ h p.1 - h p.2) 2 (realJumpPairMeasure κ)) :
    MemLp (fun x ↦ b x * h x) 2 ∧
      MemLp (fun p : ℝ × ℝ ↦ b p.1 * h p.1 - b p.2 * h p.2) 2
        (realJumpPairMeasure κ) := by
  have hbc := hb.continuous
  have hbt : MemLp b ⊤ := memLp_top_of_bound (by fun_prop) B (.of_forall hB)
  constructor
  · exact hbt.mul hh₂
  · apply (memLp_two_iff_integrable_sq_norm
      (by apply Measurable.aestronglyMeasurable; fun_prop)).mpr
    exact integrable_jump_sq_mul_of_lipschitz κ hh hh₂ hB hb hκ
      ((memLp_two_iff_integrable_sq_norm hj.aestronglyMeasurable).mp hj)

/-- Squared norms of a bounded Lipschitz multiplier remain bounded Lipschitz. -/
theorem lipschitzWith_norm_sq_of_bound {b : ℝ → ℂ} {B L : NNReal}
    (hB : ∀ x, ‖b x‖ ≤ B) (hb : LipschitzWith L b) :
    LipschitzWith (2 * B * L) (fun x ↦ ‖b x‖ ^ 2) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mul, NNReal.coe_ofNat]
  have he : ‖b x‖ ^ 2 - ‖b y‖ ^ 2 = (‖b x‖ - ‖b y‖) * (‖b x‖ + ‖b y‖) := by ring
  rw [he, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hnorm : |‖b x‖ - ‖b y‖| ≤ (L : ℝ) * |x - y| := by
    simpa only [Real.norm_eq_abs] using (abs_norm_sub_norm_le (b x) (b y)).trans (hb.norm_sub_le x y)
  calc
    _ ≤ ((L : ℝ) * |x - y|) * (2 * B) :=
      mul_le_mul hnorm (by linarith [hB x, hB y])
        (add_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ = _ := by ring

/-- The real test function `|b|² h` is in the full energy domain. This is the test used
in the exact cardinal residual cancellation. -/
theorem memLp_norm_sq_mul_and_jump (κ : Measure ℝ) {b : ℝ → ℂ} {h : ℝ → ℝ}
    (hh : Measurable h) (hh₂ : MemLp h 2) {B L : NNReal}
    (hB : ∀ x, ‖b x‖ ≤ B) (hb : LipschitzWith L b)
    (hκ : Integrable (fun r : ℝ ↦ r ^ 2) κ)
    (hj : MemLp (fun p : ℝ × ℝ ↦ h p.1 - h p.2) 2 (realJumpPairMeasure κ)) :
    MemLp (fun x ↦ ‖b x‖ ^ 2 * h x) 2 ∧
      MemLp (fun p : ℝ × ℝ ↦ ‖b p.1‖ ^ 2 * h p.1 - ‖b p.2‖ ^ 2 * h p.2) 2
        (realJumpPairMeasure κ) := by
  have hbc := hb.continuous
  have hc : LipschitzWith (2 * B * L) (fun x ↦ (‖b x‖ ^ 2 : ℝ) : ℝ → ℝ) :=
    lipschitzWith_norm_sq_of_bound hB hb
  have hc' : LipschitzWith (2 * B * L) (fun x ↦ ((‖b x‖ ^ 2 : ℝ) : ℂ)) := by
    simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitzWith.comp hc
  have hj' : MemLp (fun p : ℝ × ℝ ↦ (h p.1 : ℂ) - (h p.2 : ℂ)) 2 (realJumpPairMeasure κ) := by
    apply (hj.ofReal (K := ℂ)).ae_eq
    exact .of_forall fun p ↦ by dsimp only; exact RCLike.ofReal_sub _ _
  have hCb : ∀ x, ‖((‖b x‖ ^ 2 : ℝ) : ℂ)‖ ≤ (B : ℝ) ^ 2 := by
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB x) 2
  have hdom := memLp_mul_and_jump_of_lipschitz κ
    (b := fun x ↦ ((‖b x‖ ^ 2 : ℝ) : ℂ)) (h := fun x ↦ (h x : ℂ))
    (by fun_prop) (hh₂.ofReal (K := ℂ)) hCb hc' hκ hj'
  constructor
  · apply hdom.1.re.ae_eq
    exact .of_forall fun x ↦ by simp only [RCLike.re_to_complex, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  · apply hdom.2.re.ae_eq
    exact .of_forall fun p ↦ by simp only [RCLike.re_to_complex, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

end RiemannMasullo
