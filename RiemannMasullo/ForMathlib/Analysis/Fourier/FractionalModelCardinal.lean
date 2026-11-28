module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.FractionalModelEnergy
public import RiemannMasullo.ForMathlib.Analysis.Fourier.FractionalCardinal

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform InnerProductSpace
namespace RiemannMasullo

/-- Real interpolation data force a complex cardinal minimizer to be real-valued.
Conjugation preserves the energy, and equality in the minimal-norm property gives uniqueness. -/
theorem fractionalSynthesis_real_of_cardinal {θ : ℝ} (hθ : 1 / 2 < θ) (hθ₁ : θ < 1)
    (S : Set ℝ) (v : Lp ℂ 2 (volume : Measure ℝ))
    (hdata : ∀ t ∈ S, (fractionalSynthesis θ v t).im = 0)
    (horth : ∀ u : Lp ℂ 2 (volume : Measure ℝ),
      (∀ t ∈ S, fractionalSynthesis θ u t = 0) → ⟪v, u⟫_ℂ = 0) :
    ∀ x, (fractionalSynthesis θ v x).im = 0 := by
  let f := fractionalSynthesis θ v
  have fc := continuous_fractionalSynthesis hθ v
  have f₂ := memLp_fractionalSynthesis hθ v
  have fJ := memLp_jump_fractionalSynthesis hθ hθ₁ v
  have hJ : MemLp (fun p : ℝ × ℝ ↦ star (f p.1) - star (f p.2)) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ)) := by
    apply fJ.star.ae_eq
    exact .of_forall fun p ↦ by
      change star (f p.1 - f p.2) = star (f p.1) - star (f p.2)
      rw [star_sub]
  obtain ⟨u, hu⟩ := exists_fractionalSynthesis_eq_of_memLp_jump hθ hθ₁
    (f := fun x ↦ star (f x)) fc.star f₂.star hJ
  have hn : ‖u‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← fractionalSynthesis_energy hθ hθ₁ u, hu,
      ← fractionalSynthesis_energy hθ hθ₁ v]
    simp only [nonlocalEnergy, norm_star, ← star_sub, f]
  have ho := horth (v - u) (by
    intro t ht
    rw [← fractionalProbe_inner hθ, inner_sub_right,
      fractionalProbe_inner hθ, fractionalProbe_inner hθ, hu]
    apply sub_eq_zero.mpr
    apply Complex.ext
    · simp only [Complex.star_def, Complex.conj_re, f]
    · simp only [Complex.star_def, Complex.conj_im]
      change (f t).im = -(f t).im
      rw [hdata t ht, neg_zero])
  have hre := congrArg Complex.re ho
  rw [inner_sub_right, Complex.sub_re, Complex.zero_re] at hre
  rw [show (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) v] at hre
  have hvu : v = u := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have he := norm_sub_sq (𝕜 := ℂ) v u
    change ‖v - u‖ ^ 2 = ‖v‖ ^ 2 - 2 * (⟪v, u⟫_ℂ).re + ‖u‖ ^ 2 at he
    nlinarith [norm_nonneg (v - u)]
  intro x
  have h := congrFun hu x
  rw [← hvu] at h
  have him := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at him
  change (f x).im = -(f x).im at him
  linarith


/-- A real-valued test profile extracts the real part of the model pairing. -/
theorem fractionalSynthesis_real_pairing {θ : ℝ} (hθ : 1 / 2 < θ) (hθ₁ : θ < 1)
    (v u : Lp ℂ 2 (volume : Measure ℝ)) {g : ℝ → ℝ}
    (hu : fractionalSynthesis θ u = fun x ↦ (g x : ℂ)) :
    realNonlocalPairing volume (realJumpPairMeasure (fractionalJumpMeasure θ))
      (fun x ↦ (fractionalSynthesis θ v x).re) g = (⟪v, u⟫_ℂ).re := by
  have he := fractionalSynthesis_pairing_re hθ hθ₁ v u
  rw [hu] at he
  simpa only [realNonlocalPairing, Complex.star_def, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    sub_self, mul_zero, sub_zero] using he

/-- The real profile of a model cardinal vector is orthogonal to every admissible
real test vanishing on the interpolation set. -/
theorem fractionalSynthesis_cardinal_real_orthogonal {θ : ℝ}
    (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) (S : Set ℝ) (v : Lp ℂ 2 (volume : Measure ℝ))
    (horth : ∀ u : Lp ℂ 2 (volume : Measure ℝ),
      (∀ t ∈ S, fractionalSynthesis θ u t = 0) → ⟪v, u⟫_ℂ = 0)
    {g : ℝ → ℝ} (gc : Continuous g) (g₂ : MemLp g 2)
    (gJ : MemLp (fun p : ℝ × ℝ ↦ g p.1 - g p.2) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ))) (gS : ∀ t ∈ S, g t = 0) :
    realNonlocalPairing volume (realJumpPairMeasure (fractionalJumpMeasure θ))
      (fun x ↦ (fractionalSynthesis θ v x).re) g = 0 := by
  have gJc : MemLp (fun p : ℝ × ℝ ↦ (g p.1 : ℂ) - (g p.2 : ℂ)) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ)) := by
    apply (gJ.ofReal (K := ℂ)).ae_eq
    exact .of_forall fun p ↦ by dsimp only; exact RCLike.ofReal_sub _ _
  obtain ⟨u, hu⟩ := exists_fractionalSynthesis_eq_of_memLp_jump hθ hθ₁
    (f := fun x ↦ (g x : ℂ)) (by fun_prop) g₂.ofReal gJc
  rw [fractionalSynthesis_real_pairing hθ hθ₁ v u hu,
    horth u (by intro t ht; simp only [hu, gS t ht, Complex.ofReal_zero]), Complex.zero_re]

/-- A cardinal multiplier residual in the Hilbert model satisfies the uniform
fractional energy bound, with no spacing or finite-set hypothesis on its sites. -/
theorem fractionalSynthesis_cardinal_residual_norm_sq_le {θ : ℝ}
    (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) (S : Set ℝ) (z : ℝ)
    (v u : Lp ℂ 2 (volume : Measure ℝ))
    (hz : fractionalSynthesis θ v z = 1)
    (hS : ∀ t ∈ S, fractionalSynthesis θ v t = 0)
    (horth : ∀ w : Lp ℂ 2 (volume : Measure ℝ),
      fractionalSynthesis θ w z = 0 →
      (∀ t ∈ S, fractionalSynthesis θ w t = 0) → ⟪v, w⟫_ℂ = 0)
    {b : ℝ → ℂ} {A : ℝ} (hA : 0 ≤ A) {B L : NNReal}
    (hB : ∀ x, ‖b x‖ ≤ B) (hb : LipschitzWith L b) (bz : b z = 0)
    (hbw : ∀ x y, ‖b x - b y‖ ≤ A * |x - y| *
      Real.exp ((|x - z| + |y - z|) / 8))
    (hu : fractionalSynthesis θ u = fun x ↦ fractionalSynthesis θ v x * b x) :
    ‖u‖ ^ 2 ≤ 8 * θ * ((2 : ℝ) ^ (θ - 1 / 2)) ^ 2 * A ^ 2 := by
  have ho : ∀ w : Lp ℂ 2 (volume : Measure ℝ),
      (∀ t ∈ insert z S, fractionalSynthesis θ w t = 0) → ⟪v, w⟫_ℂ = 0 :=
    fun w hw ↦ horth w (hw z (Set.mem_insert z S))
      (fun t ht ↦ hw t (Set.mem_insert_of_mem z ht))
  have him := fractionalSynthesis_real_of_cardinal hθ hθ₁ (insert z S) v (by
    intro t ht
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · rw [hz, Complex.one_im]
    · rw [hS t ht, Complex.zero_im]) ho
  have hreal (x : ℝ) : (((fractionalSynthesis θ v x).re : ℝ) : ℂ) = fractionalSynthesis θ v x := by
    apply Complex.ext
    · rfl
    · simp only [Complex.ofReal_im, him]
  have hv₂ := (memLp_fractionalSynthesis hθ v).re
  have hvJ : MemLp (fun p : ℝ × ℝ ↦
      (fractionalSynthesis θ v p.1).re - (fractionalSynthesis θ v p.2).re) 2
      (realJumpPairMeasure (fractionalJumpMeasure θ)) := by
    simpa only [Complex.sub_re, RCLike.re_to_complex] using
      (memLp_jump_fractionalSynthesis hθ hθ₁ v).re
  have he := fractional_cardinal_residual_energy_le hθ hθ₁ S
    (h := fun x ↦ (fractionalSynthesis θ v x).re)
    (Complex.continuous_re.comp (continuous_fractionalSynthesis hθ v)) hv₂ hvJ
    (by rw [hz, Complex.one_re]) (by intro t ht; rw [hS t ht, Complex.zero_re])
    hA hB hb bz hbw (by
      intro g gc g₂ gJ gz gS
      apply fractionalSynthesis_cardinal_real_orthogonal hθ hθ₁ (insert z S) v ho gc g₂ gJ
      intro t ht
      rcases Set.mem_insert_iff.mp ht with rfl | ht
      · exact gz
      · exact gS t ht)
  rw [← fractionalSynthesis_energy hθ hθ₁ u, hu]
  simpa only [hreal] using he

end RiemannMasullo
