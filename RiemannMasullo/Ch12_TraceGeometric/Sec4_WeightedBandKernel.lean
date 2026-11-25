module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelDiagonal

/-! # The weighted band of the rational real-place model: the kernel and the multiplier

Paper: Theorem 12.4.1.1, pp. 514–519, and the value used on p. 520.

The weight is `w x = x ^ 2 + x ^ (-2)` on the even functions of `L²(ℝ)`. With
`μ x = (x ^ 2 - i) / x`, which has `|μ| ^ 2 = w`, multiplication by `μ` carries the even
band-limited functions of finite weighted norm onto the odd band-limited functions that vanish
at `ζ = e ^ (i π / 4)`, and it carries the dilation `D_g` to the multiplication by
`r_g x = μ x / μ (x / g)` after `D_g`. This file holds the definitions shared by the files that
compute the trace in that picture.

* `realOddBandKernel`: the kernel `(S (u - y) - S (u + y)) / 2` of the projection onto the odd
  functions of the band.
* `weightedZero`: the point `ζ`, with `ζ ^ 2 = i`.
* `weightedDilationMultiplier`: the multiplier `r_g x = g (x ^ 2 - i) / (x ^ 2 - i g ^ 2)`.
* `weightedBandDefect`: the term `E (Y)` that appears both in the trace over the odd band and in
  the rank-one correction, and cancels between them.
-/

open Real

@[expose] public noncomputable section

namespace RiemannMasullo

/-- The kernel of the orthogonal projection onto the odd functions of the band `[-Y, Y]`:
`(S (u - y) - S (u + y)) / 2` with `S` the band kernel. -/
def realOddBandKernel (Y u y : ℝ) : ℝ :=
  (realBandKernel Y (u - y) - realBandKernel Y (u + y)) / 2

/-- The point `ζ = e ^ (i π / 4) = (1 + i) / √2` of the upper half-plane at which the functions
of the weighted band vanish after multiplication by `μ`. -/
def weightedZero : ℂ := (1 + Complex.I) / ((√2 : ℝ) : ℂ)

/-- `ζ ^ 2 = i`. -/
theorem weightedZero_sq : weightedZero ^ 2 = Complex.I := by
  have h2 : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have h0 : ((√2 : ℝ) : ℂ) ≠ 0 := by
    intro h
    rw [h] at h2
    norm_num at h2
  rw [weightedZero, div_pow, h2]
  have : (1 + Complex.I) ^ 2 = 2 * Complex.I := by
    rw [add_sq, Complex.I_sq]
    ring
  rw [this]
  ring

/-- The real part of `ζ`. -/
theorem weightedZero_re : weightedZero.re = 1 / √2 := by
  rw [weightedZero, Complex.div_ofReal_re]
  simp

/-- The imaginary part of `ζ`. -/
theorem weightedZero_im : weightedZero.im = 1 / √2 := by
  rw [weightedZero, Complex.div_ofReal_im]
  simp

/-- `ζ` lies in the upper half-plane. -/
theorem weightedZero_im_pos : 0 < weightedZero.im := by
  rw [weightedZero_im]
  positivity

/-- `ζ` is not zero. -/
theorem weightedZero_ne_zero : weightedZero ≠ 0 := fun h ↦ by
  have := weightedZero_im_pos
  rw [h] at this
  simp at this

/-- The multiplier `r_g x = g (x ^ 2 - i) / (x ^ 2 - i g ^ 2)` that the dilation `D_g` acquires
when the weighted band is carried to the odd band. -/
def weightedDilationMultiplier (g x : ℝ) : ℂ :=
  (g : ℂ) * ((x : ℂ) ^ 2 - Complex.I) / ((x : ℂ) ^ 2 - Complex.I * (g : ℂ) ^ 2)

/-- The square of the norm of `x ^ 2 - i c` for real `x` and `c`. -/
theorem norm_sq_sub_I_mul (x c : ℝ) :
    ‖(x : ℂ) ^ 2 - Complex.I * (c : ℂ)‖ ^ 2 = x ^ 4 + c ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [pow_two]
  ring

/-- The denominator of the multiplier does not vanish. -/
theorem weightedDilationMultiplier_den_ne_zero {g : ℝ} (hg : g ≠ 0) (x : ℝ) :
    (x : ℂ) ^ 2 - Complex.I * (g : ℂ) ^ 2 ≠ 0 := by
  intro h
  have h1 := norm_sq_sub_I_mul x (g ^ 2)
  rw [Complex.ofReal_pow, h, norm_zero] at h1
  have : 0 < x ^ 4 + (g ^ 2) ^ 2 := by positivity
  nlinarith

/-- The multiplier is continuous. -/
theorem continuous_weightedDilationMultiplier {g : ℝ} (hg : g ≠ 0) :
    Continuous (weightedDilationMultiplier g) := by
  unfold weightedDilationMultiplier
  exact Continuous.div (by fun_prop) (by fun_prop) (weightedDilationMultiplier_den_ne_zero hg)

/-- The multiplier is bounded by `g` when `g ≥ 1`. -/
theorem norm_weightedDilationMultiplier_le {g : ℝ} (hg : 1 ≤ g) (x : ℝ) :
    ‖weightedDilationMultiplier g x‖ ≤ g := by
  have hg0 : 0 < g := by linarith
  have h1 := norm_sq_sub_I_mul x 1
  have h2 := norm_sq_sub_I_mul x (g ^ 2)
  rw [Complex.ofReal_one, mul_one] at h1
  rw [Complex.ofReal_pow] at h2
  have hle : ‖(x : ℂ) ^ 2 - Complex.I‖ ≤ ‖(x : ℂ) ^ 2 - Complex.I * (g : ℂ) ^ 2‖ := by
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [h1, h2]
    have : (1 : ℝ) ≤ (g ^ 2) ^ 2 := by
      have : (1 : ℝ) ≤ g ^ 2 := by nlinarith
      nlinarith
    linarith
  have hpos : 0 < ‖(x : ℂ) ^ 2 - Complex.I * (g : ℂ) ^ 2‖ :=
    norm_pos_iff.mpr (weightedDilationMultiplier_den_ne_zero hg0.ne' x)
  rw [weightedDilationMultiplier, norm_div, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hg0.le, div_le_iff₀ hpos]
  gcongr

/-- The multiplier is the constant `g` plus a rational function that decays at infinity. -/
theorem weightedDilationMultiplier_eq {g : ℝ} (hg : g ≠ 0) (x : ℝ) :
    weightedDilationMultiplier g x =
      (g : ℂ) + Complex.I * (g : ℂ) * ((g : ℂ) ^ 2 - 1) /
        ((x : ℂ) ^ 2 - Complex.I * (g : ℂ) ^ 2) := by
  have h := weightedDilationMultiplier_den_ne_zero hg x
  rw [weightedDilationMultiplier, div_eq_iff h, add_mul, div_mul_cancel₀ _ h]
  ring

/-- The multiplier is even. -/
theorem weightedDilationMultiplier_neg (g x : ℝ) :
    weightedDilationMultiplier g (-x) = weightedDilationMultiplier g x := by
  simp [weightedDilationMultiplier]

/-- The term `E (Y)` of the trace over the odd band that the rank-one correction cancels:
`(g ^ 2 - 1) / (2 √g) (E₋ / (g - 1) - E₊ / (g + 1))` with `E_± = exp (2 π i Y (g ± 1) ζ)`. -/
def weightedBandDefect (Y g : ℝ) : ℂ :=
  (((g ^ 2 - 1) / (2 * √g) : ℝ) : ℂ) *
    (Complex.exp (2 * π * Complex.I * Y * (g - 1) * weightedZero) / ((g : ℂ) - 1) -
      Complex.exp (2 * π * Complex.I * Y * (g + 1) * weightedZero) / ((g : ℂ) + 1))

end RiemannMasullo
