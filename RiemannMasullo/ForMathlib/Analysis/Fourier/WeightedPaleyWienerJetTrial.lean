module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.WeightedPaleyWienerBand
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Schwartz jet trials inside a weighted Paley–Wiener band -/

public noncomputable section

open Filter Set MeasureTheory
open scoped FourierTransform Topology InnerProductSpace LineDeriv SchwartzMap

namespace RiemannMasullo.RealPWBand

private def coordPower : ℕ → 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)
  | 0, f => f
  | k+1, f => SchwartzMap.smulLeftCLM ℂ (inner ℝ · (1 : ℝ)) (coordPower k f)

private theorem coordPower_apply (k : ℕ) (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    coordPower k f t = t^k • f t := by
  induction k with
  | zero => simp [coordPower]
  | succ k ih =>
    rw [coordPower, SchwartzMap.smulLeftCLM_apply_apply (hg := by fun_prop), ih, smul_smul]
    simp [pow_succ, mul_comm]

private theorem coordPower_band (k : ℕ) (Y : ℝ) (f : 𝓢(ℝ, ℂ))
    (hf : ∀ y ∉ Icc (-Y) Y, (𝓕 f) y = 0) :
    ∀ y ∉ Icc (-Y) Y, (𝓕 (coordPower k f)) y = 0 := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    intro y hy
    let g := coordPower k f
    have hz : (fun t ↦ (𝓕 g : 𝓢(ℝ, ℂ)) t) =ᶠ[𝓝 y] fun _ => 0 := by
      have hmem : (Icc (-Y) Y)ᶜ ∈ 𝓝 y := isClosed_Icc.isOpen_compl.mem_nhds hy
      filter_upwards [hmem] with t ht
      exact ih t ht
    have hd := congrArg (fun u : 𝓢(ℝ, ℂ) => u y) (SchwartzMap.lineDerivOp_fourier_eq g (1 : ℝ))
    rw [FourierTransform.fourier_smul] at hd
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hz.fderiv_eq] at hd
    have hzero : (fderiv ℝ (fun _ : ℝ ↦ (0 : ℂ)) y) 1 = 0 := by simp
    rw [hzero] at hd
    change (0 : ℂ) = -(2 * (Real.pi : ℂ) * Complex.I) * (𝓕 (coordPower (k + 1) f)) y at hd
    have hne : -(2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
    exact (mul_eq_zero.mp hd.symm).resolve_left hne

private theorem translated_band (φ : 𝓢(ℝ, ℂ)) (x y : ℝ) (h : (𝓕 φ) y = 0) :
    (𝓕 (φ.compSubConstCLM ℂ x)) y = 0 := by
  have hFT (g : ℝ → ℂ) : 𝓕 g y = Fourier.fourierIntegral Real.fourierChar volume g y := by
    rw [Real.fourier_real_eq, Fourier.fourierIntegral_def]
  have he : ⇑(φ.compSubConstCLM ℂ x) = ⇑φ ∘ fun v => v + -x := by
    funext v; simp [sub_eq_add_neg]
  rw [SchwartzMap.fourier_coe, he, hFT, Fourier.fourierIntegral_comp_add_right]
  simp only [← hFT, ← SchwartzMap.fourier_coe, h, smul_zero]

/-- A pair of translates multiplied by a normalized even coordinate monomial. -/
def translatedJetTrial (φ : 𝓢(ℝ, ℂ)) (x : ℝ) (n : ℕ) : 𝓢(ℝ, ℂ) :=
  ((x : ℂ)⁻¹ ^ (2*n)) • coordPower (2*n) (φ.compSubConstCLM ℂ x + φ.compSubConstCLM ℂ (-x))

theorem translatedJetTrial_apply (φ : 𝓢(ℝ, ℂ)) (x t : ℝ) (n : ℕ) :
    translatedJetTrial φ x n t = ((t / x : ℝ) : ℂ)^(2*n) * (φ (t-x) + φ (t+x)) := by
  simp [translatedJetTrial, coordPower_apply, Complex.real_smul, div_eq_mul_inv, mul_pow]
  ring

theorem translatedJetTrial_at_center (φ : 𝓢(ℝ, ℂ)) {x : ℝ} (hx : x ≠ 0) (n : ℕ) :
    translatedJetTrial φ x n x = φ 0 + φ (2*x) := by
  simp [translatedJetTrial_apply, hx, two_mul]

theorem translatedJetTrial_even (φ : 𝓢(ℝ, ℂ)) (hφ : ∀ t, φ (-t) = φ t) (x : ℝ) (n : ℕ)
    (t : ℝ) : translatedJetTrial φ x n (-t) = translatedJetTrial φ x n t := by
  rw [translatedJetTrial_apply, translatedJetTrial_apply, show -t-x = -(t+x) by ring,
    show -t+x = -(t-x) by ring, hφ, hφ, neg_div, Complex.ofReal_neg, pow_mul, neg_sq, ← pow_mul]
  rw [add_comm (φ (t+x))]

theorem translatedJetTrial_band (φ : 𝓢(ℝ, ℂ)) (Y x : ℝ) (n : ℕ)
    (hφ : ∀ y ∉ Icc (-Y) Y, (𝓕 φ) y = 0) :
    ∀ y ∉ Icc (-Y) Y, (𝓕 (translatedJetTrial φ x n)) y = 0 := by
  intro y hy
  rw [translatedJetTrial, FourierTransform.fourier_smul, smul_apply]
  have hpair : ∀ z ∉ Icc (-Y) Y,
      (𝓕 (φ.compSubConstCLM ℂ x + φ.compSubConstCLM ℂ (-x))) z = 0 := by
    intro z hz
    simp only [FourierTransform.fourier_add, add_apply, translated_band φ x z (hφ z hz),
      translated_band φ (-x) z (hφ z hz), add_zero]
  rw [coordPower_band _ Y _ hpair y hy, smul_zero]

theorem translatedJetTrial_jet (φ : 𝓢(ℝ, ℂ)) (x : ℝ) {n j : ℕ} (hj : j < 2*n) :
    iteratedDeriv j (translatedJetTrial φ x n : ℝ → ℂ) 0 = 0 := by
  let g : 𝓢(ℝ, ℂ) := ((x : ℂ)⁻¹^(2*n)) • (φ.compSubConstCLM ℂ x + φ.compSubConstCLM ℂ (-x))
  have he : (translatedJetTrial φ x n : ℝ → ℂ) = (fun t : ℝ => t^(2*n)) • (g : ℝ → ℂ) := by
    funext t
    simp [translatedJetTrial, g, coordPower_apply, Complex.real_smul]
    ring
  rw [he, ← iteratedDerivWithin_univ, iteratedDerivWithin_smul (mem_univ _) uniqueDiffOn_univ
    (by fun_prop) (g.smooth j).contDiffAt.contDiffWithinAt]
  apply Finset.sum_eq_zero
  intro i hi
  have hne : 2*n - i ≠ 0 := by have := Finset.mem_range.mp hi; omega
  simp [iteratedDerivWithin_univ, hne]

/-- Multiplication by a coordinate monomial preserves Schwartz regularity and the Fourier band. -/
theorem exists_coordinatePowerSchwartz (Y : ℝ) (φ : 𝓢(ℝ, ℂ)) (k : ℕ)
    (hφ : ∀ t ∉ Icc (-Y) Y, (𝓕 φ) t = 0) :
    ∃ ψ : 𝓢(ℝ, ℂ), (∀ t, ψ t = t ^ k • φ t) ∧
      ∀ t ∉ Icc (-Y) Y, (𝓕 ψ) t = 0 :=
  ⟨coordPower k φ, coordPower_apply k φ, coordPower_band k Y φ hφ⟩

/-- An even weighted-square-integrable Schwartz function with the specified
Fourier support is realized pointwise by its vector in the closed band. -/
theorem exists_evaluation_eq_of_weightedSchwartz (Y : ℝ) (g : 𝓢(ℝ, ℂ))
    (he : Function.Even (g : ℝ → ℂ)) (hb : ∀ t ∉ Icc (-Y) Y, (𝓕 g) t = 0)
    {μ : Measure ℝ} (hμ : volume ≤ μ) (hm : MemLp (g : ℝ → ℂ) 2 μ) :
    ∃ f : space Y hμ, (fun t ↦ evaluation Y hμ t f) = (g : ℝ → ℂ) := by
  apply exists_evaluation_eq_of_band Y hμ g.continuous he hm
  have hto : (hm.mono_measure hμ).toLp (g : ℝ → ℂ) = g.toLp 2 volume := rfl
  rw [hto, SchwartzMap.toLp_fourier_eq]
  filter_upwards [ae_restrict_of_ae ((𝓕 g).coeFn_toLp 2 volume),
    ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc.compl] with t ht hs
  exact ht.trans (hb t hs)

/-- Realize the actual normalized translated trial in any weight for which its
Schwartz representative is square-integrable. -/
theorem exists_translatedJetTrial_evaluation (φ : 𝓢(ℝ, ℂ)) (Y x : ℝ) (n : ℕ)
    (heven : Function.Even (φ : ℝ → ℂ)) (hφ : ∀ y ∉ Icc (-Y) Y, (𝓕 φ) y = 0)
    {μ : Measure ℝ} (hμ : volume ≤ μ) (hm : MemLp (translatedJetTrial φ x n : ℝ → ℂ) 2 μ) :
    ∃ f : space Y hμ, (fun t ↦ evaluation Y hμ t f) = (translatedJetTrial φ x n : ℝ → ℂ) :=
  exists_evaluation_eq_of_weightedSchwartz Y _ (translatedJetTrial_even φ heven x n)
    (translatedJetTrial_band φ Y x n hφ) hμ hm

end RiemannMasullo.RealPWBand
