module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # An energy estimate for multipliers with a diagonal identity

Let `κ` be a function with "derivative" `κ'` on a measure space, and let `Ψ`, `Φ` be multipliers
with derivatives `Ψ'`, `Φ'` such that `re Ψ` dominates `‖Φ‖² + ‖Φ'‖²` and `‖Ψ'‖ ≤ ε * re Ψ` with
`ε < 2`. If the Dirichlet-type inner product `⟪Ψ κ, κ⟫ = ∫ (Ψ κ) conj κ + ∫ (Ψ κ)' conj κ'`
equals `c`, then the energy `∫ ‖Φ κ‖² + ‖(Φ κ)'‖²` is at most `2 / (1 - ε / 2) * re c`.

The second part gives the multiplier `Ψ z = (L² - z²)⁻¹` on a vertical strip `|re z| ≤ α`,
for which `ε = 1` when `α + 1 ≤ L`.
-/

open MeasureTheory Complex
open scoped ComplexConjugate

@[expose] public noncomputable section

namespace RiemannMasullo

/-- Energy estimate from a diagonal identity. With `E = ‖κ‖² + ‖κ'‖²`, if
`∫ Ψ E + ∫ Ψ' κ conj κ' = c`, `‖Φ‖² + ‖Φ'‖² ≤ re Ψ` and `‖Ψ'‖ ≤ ε * re Ψ` with `ε < 2`, then
`∫ ‖Φ κ‖² + ‖Φ' κ + Φ κ'‖² ≤ 2 / (1 - ε / 2) * re c`. -/
theorem integral_energy_le_of_diagonal {S : Type*} [MeasurableSpace S] {μ : Measure S}
    {κ κ' Ψ Ψ' Φ Φ' : S → ℂ} {ε : ℝ} (hε : ε < 2)
    (hdom : ∀ x, ‖Φ x‖ ^ 2 + ‖Φ' x‖ ^ 2 ≤ (Ψ x).re)
    (hder : ∀ x, ‖Ψ' x‖ ≤ ε * (Ψ x).re)
    (h1 : Integrable (fun x ↦ Ψ x * ((‖κ x‖ ^ 2 + ‖κ' x‖ ^ 2 : ℝ) : ℂ)) μ)
    (h2 : Integrable (fun x ↦ Ψ' x * κ x * conj (κ' x)) μ) {c : ℂ}
    (hc : ∫ x, Ψ x * ((‖κ x‖ ^ 2 + ‖κ' x‖ ^ 2 : ℝ) : ℂ) ∂μ +
      ∫ x, Ψ' x * κ x * conj (κ' x) ∂μ = c) :
    ∫ x, (‖Φ x * κ x‖ ^ 2 + ‖Φ' x * κ x + Φ x * κ' x‖ ^ 2) ∂μ ≤ 2 / (1 - ε / 2) * c.re := by
  have hpos : 0 < 1 - ε / 2 := by linarith
  have hR (x : S) : 0 ≤ (Ψ x).re := le_trans (by positivity) (hdom x)
  -- the real part of the first integrand
  have hXi : Integrable (fun x ↦ (Ψ x).re * (‖κ x‖ ^ 2 + ‖κ' x‖ ^ 2)) μ := by
    refine h1.re.congr (.of_forall fun x ↦ ?_)
    exact Complex.re_mul_ofReal _ _
  set X := ∫ x, (Ψ x).re * (‖κ x‖ ^ 2 + ‖κ' x‖ ^ 2) ∂μ with hX
  have hre1 : (∫ x, Ψ x * ((‖κ x‖ ^ 2 + ‖κ' x‖ ^ 2 : ℝ) : ℂ) ∂μ).re = X := by
    have e : (∫ x, Ψ x * ((‖κ x‖ ^ 2 + ‖κ' x‖ ^ 2 : ℝ) : ℂ) ∂μ).re =
        ∫ x, (Ψ x * ((‖κ x‖ ^ 2 + ‖κ' x‖ ^ 2 : ℝ) : ℂ)).re ∂μ := (integral_re h1).symm
    rw [e, hX]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    exact Complex.re_mul_ofReal _ _
  -- the cross term is at least `-(ε / 2) * X`
  have hcross : -(ε / 2 * X) ≤ (∫ x, Ψ' x * κ x * conj (κ' x) ∂μ).re := by
    have e : (∫ x, Ψ' x * κ x * conj (κ' x) ∂μ).re =
        ∫ x, (Ψ' x * κ x * conj (κ' x)).re ∂μ := (integral_re h2).symm
    rw [e, hX, ← integral_const_mul, ← integral_neg]
    refine integral_mono (hXi.const_mul _).neg h2.re (fun x ↦ ?_)
    have hn : ‖Ψ' x * κ x * conj (κ' x)‖ ≤ ε * (Ψ x).re * (‖κ x‖ * ‖κ' x‖) := by
      rw [norm_mul, norm_mul, Complex.norm_conj, mul_assoc]
      exact mul_le_mul_of_nonneg_right (hder x) (by positivity)
    have hab : ‖κ x‖ * ‖κ' x‖ ≤ (‖κ x‖ ^ 2 + ‖κ' x‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖κ x‖ - ‖κ' x‖)]
    have hεR : 0 ≤ ε * (Ψ x).re := le_trans (norm_nonneg _) (hder x)
    have h3 : -(ε / 2 * ((Ψ x).re * (‖κ x‖ ^ 2 + ‖κ' x‖ ^ 2))) ≤
        -‖Ψ' x * κ x * conj (κ' x)‖ := by
      have := mul_le_mul_of_nonneg_left hab hεR
      nlinarith
    exact h3.trans (neg_le_of_abs_le (Complex.abs_re_le_norm _))
  have hXle : X ≤ c.re / (1 - ε / 2) := by
    rw [le_div_iff₀ hpos]
    have := congrArg Complex.re hc
    rw [Complex.add_re, hre1] at this
    nlinarith
  -- the energy is pointwise at most twice the first integrand
  have hpt (x : S) : ‖Φ x * κ x‖ ^ 2 + ‖Φ' x * κ x + Φ x * κ' x‖ ^ 2 ≤
      2 * ((Ψ x).re * (‖κ x‖ ^ 2 + ‖κ' x‖ ^ 2)) := by
    have h4 : ‖Φ' x * κ x + Φ x * κ' x‖ ≤ ‖Φ' x‖ * ‖κ x‖ + ‖Φ x‖ * ‖κ' x‖ := by
      simpa [norm_mul] using norm_add_le (Φ' x * κ x) (Φ x * κ' x)
    have h5 : ‖Φ' x * κ x + Φ x * κ' x‖ ^ 2 ≤ (‖Φ' x‖ * ‖κ x‖ + ‖Φ x‖ * ‖κ' x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h4 2
    have h6 := mul_le_mul_of_nonneg_right (hdom x)
      (by positivity : (0 : ℝ) ≤ ‖κ x‖ ^ 2 + ‖κ' x‖ ^ 2)
    rw [norm_mul]
    nlinarith [sq_nonneg (‖Φ' x‖ * ‖κ x‖ - ‖Φ x‖ * ‖κ' x‖), sq_nonneg (‖Φ' x‖ * ‖κ' x‖),
      sq_nonneg (‖Φ x‖ * ‖κ x‖)]
  calc ∫ x, (‖Φ x * κ x‖ ^ 2 + ‖Φ' x * κ x + Φ x * κ' x‖ ^ 2) ∂μ
      ≤ ∫ x, 2 * ((Ψ x).re * (‖κ x‖ ^ 2 + ‖κ' x‖ ^ 2)) ∂μ :=
        integral_mono_of_nonneg (.of_forall fun x ↦ by positivity) (hXi.const_mul 2)
          (.of_forall hpt)
    _ = 2 * X := by rw [integral_const_mul]
    _ ≤ 2 / (1 - ε / 2) * c.re := by
        rw [div_mul_eq_mul_div, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hXle zero_le_two

/-- The real part of `L² - z²`. -/
theorem re_sq_sub_sq (L : ℝ) (z : ℂ) :
    ((L : ℂ) ^ 2 - z ^ 2).re = L ^ 2 - z.re ^ 2 + z.im ^ 2 := by
  simp [sq]
  ring

/-- On the strip `|re z| ≤ α < L`, the real part of `L² - z²` is positive. -/
theorem re_sq_sub_sq_pos {L α : ℝ} {z : ℂ} (hα : α < L) (hz : |z.re| ≤ α) :
    0 < ((L : ℂ) ^ 2 - z ^ 2).re := by
  rw [re_sq_sub_sq]
  have h0 : 0 ≤ α := (abs_nonneg _).trans hz
  have h1 : z.re ^ 2 ≤ α ^ 2 := by
    rw [← sq_abs z.re]
    exact pow_le_pow_left₀ (abs_nonneg _) hz 2
  nlinarith [sq_nonneg z.im]

/-- The derivative of the multiplier `z ↦ (L² - z²)⁻¹`. -/
theorem hasDerivAt_inv_sq_sub_sq {L : ℝ} {z : ℂ} (hne : (L : ℂ) ^ 2 - z ^ 2 ≠ 0) :
    HasDerivAt (fun w : ℂ ↦ ((L : ℂ) ^ 2 - w ^ 2)⁻¹) (2 * z / ((L : ℂ) ^ 2 - z ^ 2) ^ 2) z := by
  have h0 : HasDerivAt (fun w : ℂ ↦ (L : ℂ) ^ 2 - w ^ 2) (-(2 * z)) z := by
    simpa using HasDerivAt.const_sub ((L : ℂ) ^ 2) (hasDerivAt_pow 2 z)
  have h : HasDerivAt (fun w : ℂ ↦ ((L : ℂ) ^ 2 - w ^ 2)⁻¹)
      (-(-(2 * z)) / ((L : ℂ) ^ 2 - z ^ 2) ^ 2) z := HasDerivAt.inv h0 hne
  rwa [neg_neg] at h

/-- On the strip `|re z| ≤ α` with `α + 1 ≤ L`, the derivative of the multiplier
`z ↦ (L² - z²)⁻¹` is bounded by its real part, which is positive. -/
theorem norm_deriv_inv_sq_sub_sq_le_re {L α : ℝ} {z : ℂ} (hL : α + 1 ≤ L) (hz : |z.re| ≤ α) :
    ‖2 * z / ((L : ℂ) ^ 2 - z ^ 2) ^ 2‖ ≤ (((L : ℂ) ^ 2 - z ^ 2)⁻¹).re := by
  have h0 : 0 ≤ α := (abs_nonneg _).trans hz
  have hwre := re_sq_sub_sq L z
  have hpos : 0 < ((L : ℂ) ^ 2 - z ^ 2).re := re_sq_sub_sq_pos (by linarith) hz
  have hw : (L : ℂ) ^ 2 - z ^ 2 ≠ 0 := fun h ↦ by rw [h] at hpos; simp at hpos
  have hN : 0 < normSq ((L : ℂ) ^ 2 - z ^ 2) := Complex.normSq_pos.mpr hw
  have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  have h2 : z.re ^ 2 ≤ α ^ 2 := by
    rw [← sq_abs z.re]
    exact pow_le_pow_left₀ (abs_nonneg _) hz 2
  have h3 : 2 * |z.im| ≤ z.im ^ 2 + 1 := by nlinarith [sq_nonneg (|z.im| - 1), sq_abs z.im]
  have h4 : 2 * ‖z‖ ≤ ((L : ℂ) ^ 2 - z ^ 2).re := by
    rw [hwre]
    nlinarith
  rw [Complex.inv_re, norm_div, norm_pow, Complex.sq_norm, norm_mul, Complex.norm_ofNat]
  exact div_le_div_of_nonneg_right h4 hN.le

end RiemannMasullo
