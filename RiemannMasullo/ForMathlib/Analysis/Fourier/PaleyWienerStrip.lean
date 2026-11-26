module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace

/-! # Laplace kernels of entire functions bounded on a vertical strip

An entire function `g` with `‖g (σ + i t)‖ ≤ B / (1 + t²)` on the closed strip `|σ| ≤ β` is the
two-sided Laplace transform, on the open strip, of a continuous kernel `k` with
`‖k y‖ ≤ B / 2 · exp (-β |y|)`, and the moments of `k` are the derivatives of `g`. This is the
Paley–Wiener theorem for a strip, in the form needed to turn a bound for a multiplier into a
bound for a convolution kernel.

The transform is `bilateralLaplace` of `StripLaplace.lean`, and the moments come from its
derivative lemmas there; this file adds the converse direction, from the function to its kernel.
-/

public section

open MeasureTheory Filter Set Complex
open scoped Topology Real FourierTransform Interval

namespace RiemannMasullo

/-- The product of an entire function bounded by `B / (1 + t²)` on a vertical line with the
exponential `exp (-u y)` is integrable along that line. -/
private theorem exists_laplaceKernel_of_strip_bound_integrable {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) {β B : ℝ}
    (hb : ∀ u : ℂ, |u.re| ≤ β → ‖g u‖ ≤ B / (1 + u.im ^ 2)) (y : ℝ) {σ : ℝ} (hσ : |σ| ≤ β) :
    Integrable (fun t : ℝ ↦ g (σ + t * I) * cexp (-(σ + t * I) * y)) ∧
      ∀ t : ℝ, ‖g (σ + t * I) * cexp (-(σ + t * I) * y)‖ ≤
        B * Real.exp (-σ * y) * (1 + t ^ 2)⁻¹ := by
  have hle (t : ℝ) : ‖g (σ + t * I) * cexp (-(σ + t * I) * y)‖ ≤
      B * Real.exp (-σ * y) * (1 + t ^ 2)⁻¹ := by
    have h1 := hb (σ + t * I) (by simpa using hσ)
    have h2 : ‖cexp (-(σ + t * I) * y)‖ = Real.exp (-σ * y) := by
      rw [Complex.norm_exp]
      simp
    rw [norm_mul, h2]
    have h3 : ‖g (σ + t * I)‖ ≤ B * (1 + t ^ 2)⁻¹ := by
      simpa [div_eq_mul_inv] using h1
    calc ‖g (σ + t * I)‖ * Real.exp (-σ * y) ≤ B * (1 + t ^ 2)⁻¹ * Real.exp (-σ * y) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = B * Real.exp (-σ * y) * (1 + t ^ 2)⁻¹ := by ring
  refine ⟨?_, hle⟩
  refine (integrable_inv_one_add_sq.const_mul (B * Real.exp (-σ * y))).mono' ?_ (.of_forall hle)
  exact ((hg.continuous.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable

/-- Contour shift: the integral of `g u · exp (-u y)` over a vertical line of the strip does
not depend on the line. -/
private theorem exists_laplaceKernel_of_strip_bound_shift {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) {β B : ℝ}
    (hb : ∀ u : ℂ, |u.re| ≤ β → ‖g u‖ ≤ B / (1 + u.im ^ 2)) (y : ℝ) {σ₁ σ₂ : ℝ}
    (h₁ : |σ₁| ≤ β) (h₂ : |σ₂| ≤ β) :
    ∫ t : ℝ, g (σ₁ + t * I) * cexp (-(σ₁ + t * I) * y) =
      ∫ t : ℝ, g (σ₂ + t * I) * cexp (-(σ₂ + t * I) * y) := by
  let F (u : ℂ) : ℂ := g u * cexp (-u * y)
  have hF : Differentiable ℂ F := hg.mul (by fun_prop)
  have hB : 0 ≤ B := by
    have h := (norm_nonneg _).trans (hb 0 (by simpa using (abs_nonneg σ₁).trans h₁))
    simpa using h
  let C : ℝ := B * Real.exp (β * |y|)
  -- A uniform bound on the horizontal sides.
  have hhor (T x : ℝ) (hx : |x| ≤ β) : ‖F (x + T * I)‖ ≤ C * (1 + T ^ 2)⁻¹ := by
    have h := (exists_laplaceKernel_of_strip_bound_integrable hg hb y hx).2 T
    refine h.trans ?_
    have he : Real.exp (-x * y) ≤ Real.exp (β * |y|) := by
      refine Real.exp_le_exp.mpr ?_
      calc -x * y ≤ |x * y| := by rw [neg_mul]; exact neg_le_abs _
        _ = |x| * |y| := abs_mul x y
        _ ≤ β * |y| := mul_le_mul_of_nonneg_right hx (abs_nonneg y)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hB) (by positivity)
  have hbetween (x : ℝ) (hx : x ∈ Ι σ₁ σ₂) : |x| ≤ β := by
    rcases uIoc_subset_uIcc hx with ⟨hlo, hhi⟩
    refine abs_le.mpr ⟨?_, ?_⟩
    · exact (le_min (abs_le.mp h₁).1 (abs_le.mp h₂).1).trans hlo
    · exact hhi.trans (max_le (abs_le.mp h₁).2 (abs_le.mp h₂).2)
  have hside (s : ℝ → ℝ) (hs : Tendsto (fun T ↦ |s T|) atTop atTop) :
      Tendsto (fun T : ℝ ↦ ∫ x in σ₁..σ₂, F (x + s T * I)) atTop (𝓝 0) := by
    have hbd (T : ℝ) : ‖∫ x in σ₁..σ₂, F (x + s T * I)‖ ≤ C * (1 + (s T) ^ 2)⁻¹ * |σ₂ - σ₁| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦ hhor (s T) x (hbetween x hx)
    refine squeeze_zero_norm hbd ?_
    have h0 : Tendsto (fun T : ℝ ↦ (1 + (s T) ^ 2)⁻¹) atTop (𝓝 0) := by
      refine tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _ ?_)
      have := hs.atTop_mul_atTop₀ hs
      simpa [sq] using this
    simpa using (h0.const_mul C).mul_const |σ₂ - σ₁|
  have hvert (σ : ℝ) (hσ : |σ| ≤ β) :
      Tendsto (fun T : ℝ ↦ ∫ t in (-T)..T, F (σ + t * I)) atTop
        (𝓝 (∫ t : ℝ, F (σ + t * I))) :=
    intervalIntegral_tendsto_integral (exists_laplaceKernel_of_strip_bound_integrable hg hb y hσ).1
      tendsto_neg_atTop_atBot tendsto_id
  have hrect (T : ℝ) :
      (∫ x in σ₁..σ₂, F (x + (-T : ℝ) * I)) - (∫ x in σ₁..σ₂, F (x + T * I)) +
        I • (∫ t in (-T)..T, F (σ₂ + t * I)) - I • (∫ t in (-T)..T, F (σ₁ + t * I)) = 0 := by
    have h := integral_boundary_rect_eq_zero_of_differentiableOn F (⟨σ₁, -T⟩ : ℂ) (⟨σ₂, T⟩ : ℂ)
      hF.differentiableOn
    simpa using h
  have hlim := (((hside (fun T ↦ -T) (by simpa using tendsto_abs_atTop_atTop)).sub
    (hside (fun T ↦ T) tendsto_abs_atTop_atTop)).add ((hvert σ₂ h₂).const_smul I)).sub
    ((hvert σ₁ h₁).const_smul I)
  have hzero : (0 : ℂ) - 0 + I • (∫ t : ℝ, F (σ₂ + t * I)) - I • (∫ t : ℝ, F (σ₁ + t * I)) = 0 :=
    tendsto_nhds_unique hlim
      (Tendsto.congr (fun T ↦ (hrect T).symm) (tendsto_const_nhds (x := (0 : ℂ)) (f := atTop)))
  have hI : I • ((∫ t : ℝ, F (σ₂ + t * I)) - ∫ t : ℝ, F (σ₁ + t * I)) = 0 := by
    rw [smul_sub]
    simpa using hzero
  have := (smul_eq_zero.mp hI).resolve_left I_ne_zero
  exact (sub_eq_zero.mp this).symm

/-- The function `|y|ⁿ · exp (-c |y|)` is integrable on the real line for `c > 0`: it is at most
a constant times `exp (-(c / 2) |y|)`, which is integrable by `integrable_exp_neg_mul_abs`. -/
theorem integrable_abs_pow_mul_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Integrable (fun y : ℝ ↦ |y| ^ n * Real.exp (-c * |y|)) := by
  have hc2 : 0 < c / 2 := by positivity
  refine ((integrable_exp_neg_mul_abs hc2).const_mul ((n.factorial : ℝ) / (c / 2) ^ n)).mono'
    (Continuous.aestronglyMeasurable (by fun_prop)) (.of_forall fun y ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have h1 := Real.pow_div_factorial_le_exp (x := c / 2 * |y|) (by positivity) n
  have h2 : (c / 2 * |y|) ^ n ≤ n.factorial * Real.exp (c / 2 * |y|) :=
    ((div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial)).mp h1).trans_eq (mul_comm _ _)
  have h3 : Real.exp (-c * |y|) = Real.exp (-(c / 2 * |y|)) * Real.exp (-(c / 2 * |y|)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h4 : Real.exp (c / 2 * |y|) * Real.exp (-(c / 2 * |y|)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [h3, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  rw [le_div_iff₀ (by positivity)]
  calc |y| ^ n * Real.exp (-(c / 2 * |y|)) * (c / 2) ^ n
      = (c / 2 * |y|) ^ n * Real.exp (-(c / 2 * |y|)) := by
        rw [mul_pow]
        ring
    _ ≤ n.factorial * Real.exp (c / 2 * |y|) * Real.exp (-(c / 2 * |y|)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = n.factorial := by rw [mul_assoc, h4, mul_one]

/-- The function `(1 + |y|) ^ r · exp (-c |y|)` is integrable on the real line for `c > 0`. -/
theorem integrable_one_add_abs_rpow_mul_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) (r : ℝ) :
    Integrable (fun y : ℝ ↦ (1 + |y|) ^ r * Real.exp (-c * |y|)) := by
  let n := ⌈r⌉₊
  have hn : Integrable (fun y : ℝ ↦ (1 + |y|) ^ n * Real.exp (-c * |y|)) := by
    have hexp : (fun y : ℝ ↦ (1 + |y|) ^ n * Real.exp (-c * |y|)) = fun y : ℝ ↦
        ∑ m ∈ Finset.range (n + 1), (n.choose m : ℝ) * (|y| ^ (n - m) * Real.exp (-c * |y|)) := by
      funext y
      rw [add_pow, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [one_pow]
      ring
    rw [hexp]
    exact integrable_finsetSum _ fun m _ ↦
      (integrable_abs_pow_mul_exp_neg_mul_abs hc (n - m)).const_mul _
  refine hn.mono' (Continuous.aestronglyMeasurable ?_) (.of_forall fun y ↦ ?_)
  · refine Continuous.mul ?_ (by fun_prop)
    exact (continuous_const.add continuous_abs).rpow_const fun y ↦
      Or.inl (by positivity : (0 : ℝ) < 1 + |y|).ne'
  · have h1 : (1 : ℝ) ≤ 1 + |y| := le_add_of_nonneg_right (abs_nonneg y)
    rw [Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    calc (1 + |y|) ^ r ≤ (1 + |y|) ^ (n : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil r)
      _ = (1 + |y|) ^ n := Real.rpow_natCast _ _

/-- The kernel of an entire function bounded on a strip: its inverse Laplace transform along
the imaginary axis. It is continuous, bounded by `B / 2 · exp (-β |y|)`, and can be computed
on every vertical line of the strip. -/
private theorem exists_laplaceKernel_of_strip_bound_kernel {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) {β B : ℝ} (hβ : 0 < β)
    (hb : ∀ u : ℂ, |u.re| ≤ β → ‖g u‖ ≤ B / (1 + u.im ^ 2)) :
    ∃ k : ℝ → ℂ, Continuous k ∧ (∀ y, ‖k y‖ ≤ B / 2 * Real.exp (-β * |y|)) ∧
      ∀ (y σ : ℝ), |σ| ≤ β →
        k y = (2 * π : ℂ)⁻¹ * ∫ t : ℝ, g (σ + t * I) * cexp (-(σ + t * I) * y) := by
  let J (σ y : ℝ) : ℂ := ∫ t : ℝ, g (σ + t * I) * cexp (-(σ + t * I) * y)
  have hJ (y : ℝ) {σ : ℝ} (hσ : |σ| ≤ β) : J 0 y = J σ y :=
    exists_laplaceKernel_of_strip_bound_shift hg hb y (by simpa using hβ.le) hσ
  have hJbound (y : ℝ) {σ : ℝ} (hσ : |σ| ≤ β) : ‖J σ y‖ ≤ B * Real.exp (-σ * y) * π := by
    have haux := exists_laplaceKernel_of_strip_bound_integrable hg hb y hσ
    calc ‖J σ y‖ ≤ ∫ t : ℝ, B * Real.exp (-σ * y) * (1 + t ^ 2)⁻¹ :=
          norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _) (.of_forall haux.2)
      _ = B * Real.exp (-σ * y) * π := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  refine ⟨fun y ↦ (2 * π : ℂ)⁻¹ * J 0 y, ?_, fun y ↦ ?_, fun y σ hσ ↦ ?_⟩
  · refine continuous_const.mul ?_
    have h0 : |(0 : ℝ)| ≤ β := by simpa using hβ.le
    refine continuous_of_dominated (bound := fun t : ℝ ↦ B * (1 + t ^ 2)⁻¹) (fun y ↦ ?_)
      (fun y ↦ .of_forall fun t ↦ ?_) (integrable_inv_one_add_sq.const_mul _)
      (.of_forall fun t ↦ by fun_prop)
    · exact (exists_laplaceKernel_of_strip_bound_integrable hg hb y h0).1.aestronglyMeasurable
    · simpa using (exists_laplaceKernel_of_strip_bound_integrable hg hb y h0).2 t
  · obtain ⟨σ, hσ, hσy⟩ : ∃ σ : ℝ, |σ| ≤ β ∧ -σ * y = -β * |y| := by
      rcases le_total 0 y with hy | hy
      · exact ⟨β, by rw [abs_of_pos hβ], by rw [abs_of_nonneg hy]⟩
      · exact ⟨-β, by rw [abs_neg, abs_of_pos hβ], by rw [abs_of_nonpos hy]; ring⟩
    have h := hJbound y hσ
    rw [hσy] at h
    have h2π : ‖(2 * π : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
      rw [norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    change ‖(2 * π : ℂ)⁻¹ * J 0 y‖ ≤ _
    rw [hJ y hσ, norm_mul, h2π]
    calc (2 * π)⁻¹ * ‖J σ y‖ ≤ (2 * π)⁻¹ * (B * Real.exp (-β * |y|) * π) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = B / 2 * Real.exp (-β * |y|) := by
        field_simp
  · change (2 * π : ℂ)⁻¹ * J 0 y = (2 * π : ℂ)⁻¹ * J σ y
    rw [hJ y hσ]

/-- Fourier inversion on a vertical line: on the open strip the two-sided Laplace transform of
the kernel is the function itself. -/
private theorem exists_laplaceKernel_of_strip_bound_laplace {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) {β B : ℝ}
    (hb : ∀ u : ℂ, |u.re| ≤ β → ‖g u‖ ≤ B / (1 + u.im ^ 2)) (k : ℝ → ℂ) (hkc : Continuous k)
    (hkb : ∀ y, ‖k y‖ ≤ B / 2 * Real.exp (-β * |y|))
    (hk : ∀ (y σ : ℝ), |σ| ≤ β →
      k y = (2 * π : ℂ)⁻¹ * ∫ t : ℝ, g (σ + t * I) * cexp (-(σ + t * I) * y))
    (u : ℂ) (hu : |u.re| < β) :
    bilateralLaplace k u = g u := by
  unfold bilateralLaplace
  have hσ : |u.re| ≤ β := hu.le
  have h2π : (2 * π : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  let h (t : ℝ) : ℂ := g (u.re + t * I)
  have hhc : Continuous h := hg.continuous.comp (by fun_prop)
  have hhi : Integrable h := by
    have := (exists_laplaceKernel_of_strip_bound_integrable hg hb 0 hσ).1
    simpa using this
  -- The Fourier transform of the restriction to the line, in terms of the kernel.
  have hF (ξ : ℝ) : 𝓕 h ξ =
      (2 * π : ℂ) * (cexp (u.re * ((2 * π * ξ : ℝ) : ℂ)) * k (2 * π * ξ)) := by
    have key (t : ℝ) : cexp (↑(-2 * π * t * ξ) * I) • h t =
        (2 * π : ℂ) * (cexp (u.re * ((2 * π * ξ : ℝ) : ℂ)) * ((2 * π : ℂ)⁻¹ *
          (g (u.re + t * I) * cexp (-(u.re + t * I) * ((2 * π * ξ : ℝ) : ℂ))))) := by
      have he : cexp (↑(-2 * π * t * ξ) * I) =
          cexp (u.re * ((2 * π * ξ : ℝ) : ℂ)) *
            cexp (-(u.re + t * I) * ((2 * π * ξ : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [smul_eq_mul, he]
      change _ * _ * g (u.re + t * I) = _
      field_simp
    calc 𝓕 h ξ = ∫ t : ℝ, cexp (↑(-2 * π * t * ξ) * I) • h t :=
          Real.fourier_real_eq_integral_exp_smul h ξ
      _ = ∫ t : ℝ, (2 * π : ℂ) * (cexp (u.re * ((2 * π * ξ : ℝ) : ℂ)) * ((2 * π : ℂ)⁻¹ *
          (g (u.re + t * I) * cexp (-(u.re + t * I) * ((2 * π * ξ : ℝ) : ℂ))))) :=
          integral_congr_ae (.of_forall key)
      _ = (2 * π : ℂ) * (cexp (u.re * ((2 * π * ξ : ℝ) : ℂ)) * ((2 * π : ℂ)⁻¹ *
          ∫ t : ℝ, g (u.re + t * I) * cexp (-(u.re + t * I) * ((2 * π * ξ : ℝ) : ℂ)))) := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul]
      _ = _ := by rw [← hk (2 * π * ξ) u.re hσ]
  have hFeq : 𝓕 h = fun ξ : ℝ ↦
      (2 * π : ℂ) * (cexp (u.re * ((2 * π * ξ : ℝ) : ℂ)) * k (2 * π * ξ)) := funext hF
  have hc : 0 < 2 * π * (β - |u.re|) := by
    have := sub_pos.mpr hu
    positivity
  have hB : 0 ≤ B := by
    have h := (norm_nonneg _).trans (hb u hσ)
    have hpos : 0 < 1 + u.im ^ 2 := by positivity
    exact (div_nonneg_iff.mp h).elim (fun h ↦ h.1) (fun h ↦ absurd h.2 (not_le.mpr hpos))
  have hFint : Integrable (𝓕 h) := by
    rw [hFeq]
    refine ((integrable_abs_pow_mul_exp_neg_mul_abs hc 0).const_mul (π * B)).mono'
      (Continuous.aestronglyMeasurable (by fun_prop)) (.of_forall fun ξ ↦ ?_)
    have hk' := hkb (2 * π * ξ)
    have hre : (↑u.re * ((2 * π * ξ : ℝ) : ℂ)).re = u.re * (2 * π * ξ) := by
      simp
    have h2n : ‖(2 * π : ℂ)‖ = 2 * π := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    rw [norm_mul, h2n, norm_mul (cexp _), Complex.norm_exp, hre, pow_zero, one_mul]
    have hexp : Real.exp (u.re * (2 * π * ξ)) * Real.exp (-β * |2 * π * ξ|) ≤
        Real.exp (-(2 * π * (β - |u.re|)) * |ξ|) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have habs : |2 * π * ξ| = 2 * π * |ξ| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      have h1 : u.re * (2 * π * ξ) ≤ |u.re| * (2 * π * |ξ|) := by
        calc u.re * (2 * π * ξ) ≤ |u.re * (2 * π * ξ)| := le_abs_self _
          _ = |u.re| * (2 * π * |ξ|) := by rw [abs_mul, habs]
      rw [habs]
      linarith
    calc 2 * π * (Real.exp (u.re * (2 * π * ξ)) * ‖k (2 * π * ξ)‖)
        ≤ 2 * π * (Real.exp (u.re * (2 * π * ξ)) * (B / 2 * Real.exp (-β * |2 * π * ξ|))) := by
          gcongr
      _ = π * B * (Real.exp (u.re * (2 * π * ξ)) * Real.exp (-β * |2 * π * ξ|)) := by ring
      _ ≤ π * B * Real.exp (-(2 * π * (β - |u.re|)) * |ξ|) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
  have hinv := hhi.fourierInv_fourier_eq hFint (hhc.continuousAt (x := u.im))
  have hsub := Measure.integral_comp_mul_left (fun y : ℝ ↦ k y * cexp (u * y)) (2 * π)
  have hpos : (0 : ℝ) < 2 * π := by positivity
  rw [abs_of_pos (inv_pos.mpr hpos)] at hsub
  have hval : ∫ y : ℝ, k y * cexp (u * y) =
      (2 * π : ℂ) * ∫ ξ : ℝ, k (2 * π * ξ) * cexp (u * ((2 * π * ξ : ℝ) : ℂ)) := by
    rw [hsub, Complex.real_smul]
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ h2π, one_mul]
  have hu' : h u.im = g u := by
    change g (u.re + u.im * I) = g u
    rw [Complex.re_add_im]
  rw [hval, ← hu', ← hinv, Real.fourierInv_eq', ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun ξ ↦ ?_)
  change (2 * π : ℂ) * (k (2 * π * ξ) * cexp (u * ((2 * π * ξ : ℝ) : ℂ))) =
    cexp (↑(2 * π * inner ℝ ξ u.im) * I) • 𝓕 h ξ
  rw [hF ξ, smul_eq_mul]
  have he : cexp (u * ((2 * π * ξ : ℝ) : ℂ)) =
      cexp (↑(2 * π * inner ℝ ξ u.im) * I) * cexp (u.re * ((2 * π * ξ : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    have hin : inner ℝ ξ u.im = u.im * ξ := by
      simp [mul_comm]
    rw [hin]
    conv_lhs => rw [← Complex.re_add_im u]
    push_cast
    ring
  rw [he]
  ring

/-- On the open strip, the iterated derivatives of the two-sided Laplace transform of a
function in the weighted `L²` space are the transforms of `x ^ q * f x`. -/
theorem iteratedDeriv_bilateralLaplace {f : ℝ → ℂ} {α : ℝ}
    (hf : MemLp (fun x : ℝ ↦ Real.exp (α * |x|) • f x) 2) {z : ℂ} (hz : |z.re| < α) (q : ℕ) :
    iteratedDeriv q (bilateralLaplace f) z =
      bilateralLaplace (fun x : ℝ ↦ (x : ℂ) ^ q * f x) z := by
  induction q generalizing f α z with
  | zero =>
    rw [iteratedDeriv_zero]
    congr 1
    funext x
    simp
  | succ q ih =>
    obtain ⟨β, hβ₁, hβ₂⟩ := exists_between hz
    have hopen : IsOpen {w : ℂ | |w.re| < α} :=
      isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
    have heq : deriv (bilateralLaplace f) =ᶠ[𝓝 z]
        bilateralLaplace (fun x : ℝ ↦ (x : ℂ) * f x) := by
      filter_upwards [hopen.mem_nhds hz] with w hw using deriv_bilateralLaplace hf hw
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq q, ih (memLp_exp_abs_smul_id_mul hf hβ₂) hβ₁]
    congr 1
    funext x
    ring

/-- A continuous function bounded by `C · exp (-β |y|)` lies in the weighted `L²` space of every
smaller exponent. -/
private theorem exists_laplaceKernel_of_strip_bound_memLp {k : ℝ → ℂ} (hkc : Continuous k)
    {β C α : ℝ} (hkb : ∀ y, ‖k y‖ ≤ C * Real.exp (-β * |y|)) (hα : α < β) :
    MemLp (fun y : ℝ ↦ Real.exp (α * |y|) • k y) 2 := by
  have hc : 0 < 2 * (β - α) := by linarith
  have hcont : Continuous (fun y : ℝ ↦ Real.exp (α * |y|) • k y) :=
    (by fun_prop : Continuous fun y : ℝ ↦ Real.exp (α * |y|)).smul hkc
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  refine ((integrable_exp_neg_mul_abs hc).const_mul (C ^ 2)).mono'
    (hcont.norm.pow 2).aestronglyMeasurable (.of_forall fun y ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity), norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h1 : Real.exp (α * |y|) * ‖k y‖ ≤ C * Real.exp (-((β - α) * |y|)) := by
    calc Real.exp (α * |y|) * ‖k y‖ ≤ Real.exp (α * |y|) * (C * Real.exp (-β * |y|)) :=
          mul_le_mul_of_nonneg_left (hkb y) (Real.exp_pos _).le
      _ = C * (Real.exp (α * |y|) * Real.exp (-β * |y|)) := by ring
      _ = C * Real.exp (-((β - α) * |y|)) := by
          rw [← Real.exp_add]
          congr 2
          ring
  calc (Real.exp (α * |y|) * ‖k y‖) ^ 2 ≤ (C * Real.exp (-((β - α) * |y|))) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h1 2
    _ = C ^ 2 * Real.exp (-(2 * (β - α) * |y|)) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        push_cast
        ring

/-- **Paley–Wiener theorem for a strip.** An entire function `g` with
`‖g (σ + i t)‖ ≤ B / (1 + t²)` on the closed strip `|σ| ≤ β` has a continuous kernel `k` with
`‖k y‖ ≤ B / 2 · exp (-β |y|)` whose two-sided Laplace moments on the open strip are the
derivatives of `g`: `∫ k y · exp (u y) · y^q dy = g^(q) (u)` for `|Re u| < β`. In the notation
of `StripLaplace.lean`, `g` is `bilateralLaplace k` on the open strip, and the moments are
`iteratedDeriv_bilateralLaplace`. -/
theorem exists_laplaceKernel_of_strip_bound {g : ℂ → ℂ} (hg : Differentiable ℂ g) {β B : ℝ}
    (hβ : 0 < β) (hb : ∀ u : ℂ, |u.re| ≤ β → ‖g u‖ ≤ B / (1 + u.im ^ 2)) :
    ∃ k : ℝ → ℂ, Continuous k ∧ (∀ y, ‖k y‖ ≤ B / 2 * Real.exp (-β * |y|)) ∧
      ∀ u : ℂ, |u.re| < β → ∀ q : ℕ,
        ∫ y : ℝ, k y * (cexp (u * y) * (y : ℂ) ^ q) = iteratedDeriv q g u := by
  obtain ⟨k, hkc, hkb, hk⟩ := exists_laplaceKernel_of_strip_bound_kernel hg hβ hb
  refine ⟨k, hkc, hkb, fun u hu q ↦ ?_⟩
  obtain ⟨α, hα₁, hα₂⟩ := exists_between hu
  have hopen : IsOpen {v : ℂ | |v.re| < β} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have hg0 : g =ᶠ[𝓝 u] bilateralLaplace k := by
    filter_upwards [hopen.mem_nhds hu] with v hv
    exact (exists_laplaceKernel_of_strip_bound_laplace hg hb k hkc hkb hk v hv).symm
  rw [hg0.iteratedDeriv_eq q, iteratedDeriv_bilateralLaplace
    (exists_laplaceKernel_of_strip_bound_memLp hkc hkb hα₂) hα₁ q]
  unfold bilateralLaplace
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  ring

end RiemannMasullo
