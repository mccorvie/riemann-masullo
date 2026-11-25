module

public import RiemannMasullo.ForMathlib.Analysis.Complex.GoodHeight
public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Good heights for a family of entire functions, uniformly in a size

`GoodHeight.lean` bounds one entire function from below on most horizontal lines of a window,
with every constant visible. This file reads off what that gives for a family `f i` of entire
functions with a size `q i ≥ 1`, when the hypotheses hold with constants that do not depend on
`i`:

* a lower bound `δ * (q i * (2 + |t|)) ^ (-D₀) ≤ ‖f i (x₀ + i t)‖` on one vertical line;
* a growth bound `‖f i s‖ ≤ C * q i ^ B₀ * (2 + |Im s|) ^ G` on the strip `|Re s - x₀| ≤ 6 ρ`.

Then the lower bound at a good height is a negative power of the size times a negative power of
the height, with a constant and exponents that do not depend on `i`.

* `exists_goodHeight_norm_lower_bound_family_off_small_set`: outside a set of heights of measure
  at most `ρ / B` in the window `[T, T + 1]`, with the constant `goodHeightFamilyConstant` and
  the two exponents explicit.
* `exists_goodHeight_norm_lower_bound_family`: there are `c > 0` and `B₁ ≥ 0` such that for
  every `i` every unit window contains a height `t` with
  `c * (q i * (2 + |T|)) ^ (-B₁) ≤ ‖f i (σ + i t)‖` on the segment `|σ - x₀| ≤ 5 ρ / 2`.
* `exists_goodHeight_windows_of_norm_le_one`: the case of entire functions bounded by one on
  the strip with the lower bound `c / (‖s‖ + X) ^ n` on the line. The constants are chosen
  before the function and its size `X`, and the result is one height `T k` in every window
  `[2 k, 2 k + 1]` with `c' / (X + |T k| + 2) ^ n' ≤ ‖ϑ (σ + i T k)‖`.

The disc of the underlying theorem has radius `6 ρ` around a point of the line `Re s = x₀`, so
the growth bound is needed on the strip `x₀ - 6 ρ ≤ Re s ≤ x₀ + 6 ρ` and nowhere else.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set
open scoped Topology

namespace RiemannMasullo

/-! ## The constants -/

/-- The constant of the lower bound at a good height for a family of entire functions: `ρ` is
the scale of the segment, `δ` and `D₀` the constant and the exponent of the lower bound on the
center line, `C` and `G` the constant and the height exponent of the growth bound, and the
exceptional set of heights has measure at most `ρ / B`. It does not depend on the member of
the family. -/
def goodHeightFamilyConstant (ρ δ D₀ C G B : ℝ) : ℝ :=
  Real.exp (-(8 + 2 * B)) * (δ * (2 : ℝ) ^ (-D₀)) *
    (δ * (2 : ℝ) ^ (-D₀) / (C * (1 + 6 * ρ) ^ G)) ^ goodHeightExponent B

/-- The constant of the lower bound at good heights for a family is positive. -/
theorem goodHeightFamilyConstant_pos {ρ δ D₀ C G B : ℝ} (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hC : 0 < C) : 0 < goodHeightFamilyConstant ρ δ D₀ C G B := by
  unfold goodHeightFamilyConstant
  have h1 : 0 < δ * (2 : ℝ) ^ (-D₀) := mul_pos hδ (Real.rpow_pos_of_pos two_pos _)
  have h2 : 0 < C * (1 + 6 * ρ) ^ G := mul_pos hC (Real.rpow_pos_of_pos (by linarith) _)
  exact mul_pos (mul_pos (Real.exp_pos _) h1) (Real.rpow_pos_of_pos (div_pos h1 h2) _)

/-! ## Entire functions -/

/-- The powers of the size and of the height in the lower bound, collected. -/
private theorem exists_goodHeight_norm_lower_bound_family_off_small_set_rpow
    {a c q u κ D₀ B₀ G : ℝ} (ha : 0 < a) (hc : 0 < c) (hq : 0 < q) (hu : 0 < u) :
    a * (q * u) ^ (-D₀) * (a * (q * u) ^ (-D₀) / (c * q ^ B₀)) ^ κ * u ^ (-(κ * G)) =
      a * (a / c) ^ κ * q ^ (-(D₀ * (1 + κ) + κ * B₀)) * u ^ (-(D₀ * (1 + κ) + κ * G)) := by
  obtain ⟨la, rfl⟩ : ∃ x, a = Real.exp x := ⟨Real.log a, (Real.exp_log ha).symm⟩
  obtain ⟨lc, rfl⟩ : ∃ x, c = Real.exp x := ⟨Real.log c, (Real.exp_log hc).symm⟩
  obtain ⟨lq, rfl⟩ : ∃ x, q = Real.exp x := ⟨Real.log q, (Real.exp_log hq).symm⟩
  obtain ⟨lu, rfl⟩ : ∃ x, u = Real.exp x := ⟨Real.log u, (Real.exp_log hu).symm⟩
  simp only [← Real.exp_add, ← Real.exp_sub, ← Real.exp_mul]
  congr 1
  ring

/-- A bound `C₁ * (2 + |Im s|) ^ G` on a vertical strip of half-width `6 ρ` gives the bound
`C₁ * (1 + 6 ρ) ^ G * (2 + |T|) ^ G` on the circle of radius `6 ρ` around the point of the
middle line at height `T + 1/2`. -/
private theorem exists_goodHeight_norm_lower_bound_family_off_small_set_circle {f : ℂ → ℂ}
    {x₀ ρ C₁ G T : ℝ} (hρ : 1 ≤ ρ) (hG : 0 ≤ G) (hC₁ : 0 ≤ C₁)
    (hfgrowth : ∀ s : ℂ, s.re ∈ Icc (x₀ - 6 * ρ) (x₀ + 6 * ρ) →
      ‖f s‖ ≤ C₁ * (2 + |s.im|) ^ G) :
    ∀ z ∈ Metric.sphere (⟨x₀, T + 1 / 2⟩ : ℂ) (6 * ρ),
      ‖f z‖ ≤ C₁ * (1 + 6 * ρ) ^ G * (2 + |T|) ^ G := by
  intro z hz
  rw [mem_sphere_iff_norm] at hz
  have hu0 : 0 < 2 + |T| := by linarith [abs_nonneg T]
  have hre : |z.re - x₀| ≤ 6 * ρ := by
    have h : |z.re - x₀| ≤ ‖z - ⟨x₀, T + 1 / 2⟩‖ :=
      Complex.abs_re_le_norm (z - ⟨x₀, T + 1 / 2⟩)
    rwa [hz] at h
  have him : |z.im - (T + 1 / 2)| ≤ 6 * ρ := by
    have h : |z.im - (T + 1 / 2)| ≤ ‖z - ⟨x₀, T + 1 / 2⟩‖ :=
      Complex.abs_im_le_norm (z - ⟨x₀, T + 1 / 2⟩)
    rwa [hz] at h
  have hstrip : z.re ∈ Icc (x₀ - 6 * ρ) (x₀ + 6 * ρ) := by
    rw [abs_le] at hre
    constructor <;> linarith [hre.1, hre.2]
  have himz : 2 + |z.im| ≤ (1 + 6 * ρ) * (2 + |T|) := by
    have h1 : |z.im| ≤ |T| + 1 / 2 + 6 * ρ := by
      rw [abs_le] at him ⊢
      constructor
      · linarith [him.1, neg_abs_le T]
      · linarith [him.2, le_abs_self T]
    have h2 := mul_nonneg (zero_le_one.trans hρ) (abs_nonneg T)
    nlinarith
  calc ‖f z‖ ≤ C₁ * (2 + |z.im|) ^ G := hfgrowth z hstrip
    _ ≤ C₁ * ((1 + 6 * ρ) * (2 + |T|)) ^ G :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by linarith [abs_nonneg z.im]) himz hG) hC₁
    _ = C₁ * (1 + 6 * ρ) ^ G * (2 + |T|) ^ G := by
      rw [Real.mul_rpow (by linarith) hu0.le]
      ring

/-- The lower bound on the center line, at the center of the window. -/
private theorem exists_goodHeight_norm_lower_bound_family_off_small_set_center
    {δ D₀ q T v : ℝ} (hδ : 0 ≤ δ) (hD₀ : 0 ≤ D₀) (hq : 0 < q)
    (hv : δ * (q * (2 + |T + 1 / 2|)) ^ (-D₀) ≤ v) :
    δ * (2 : ℝ) ^ (-D₀) * (q * (2 + |T|)) ^ (-D₀) ≤ v := by
  refine le_trans ?_ hv
  have hu0 : 0 < 2 + |T| := by linarith [abs_nonneg T]
  have h0 : |T + 1 / 2| ≤ |T| + 1 / 2 := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le T]
    · linarith [le_abs_self T]
  have h1 : q * (2 + |T + 1 / 2|) ≤ 2 * (q * (2 + |T|)) := by
    have := mul_le_mul_of_nonneg_left
      (show 2 + |T + 1 / 2| ≤ 2 * (2 + |T|) by linarith [abs_nonneg T]) hq.le
    linarith
  have h2 : (2 * (q * (2 + |T|))) ^ (-D₀) ≤ (q * (2 + |T + 1 / 2|)) ^ (-D₀) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos hq (by linarith [abs_nonneg (T + 1 / 2)])) h1
      (by linarith)
  rw [Real.mul_rpow (by norm_num) (mul_pos hq hu0).le] at h2
  calc δ * (2 : ℝ) ^ (-D₀) * (q * (2 + |T|)) ^ (-D₀)
      = δ * ((2 : ℝ) ^ (-D₀) * (q * (2 + |T|)) ^ (-D₀)) := by ring
    _ ≤ δ * (q * (2 + |T + 1 / 2|)) ^ (-D₀) := mul_le_mul_of_nonneg_left h2 hδ

/-- **Good heights for a family of entire functions, uniformly in a size.** Let `f i` be
entire, with a size `q i ≥ 1`. Assume the lower bound
`δ * (q i * (2 + |t|)) ^ (-D₀) ≤ ‖f i (x₀ + i t)‖` on the line of real part `x₀` and the growth
bound `‖f i s‖ ≤ C * q i ^ B₀ * (2 + |Im s|) ^ G` on the strip `|Re s - x₀| ≤ 6 ρ`, with `δ`,
`D₀`, `C`, `B₀`, `G` the same for all `i`. Then for every `i`, every real `T` and every `B > ρ`
there is a measurable set `E` of heights in `[T, T + 1]`, of measure at most `ρ / B`, such that
for every other height `t` of the window and every real `σ` within `5 ρ / 2` of `x₀`,
`c * q i ^ (-(D₀ (1 + κ) + κ B₀)) * (2 + |T|) ^ (-(D₀ (1 + κ) + κ G)) ≤ ‖f i (σ + i t)‖`,
with `κ = goodHeightExponent B` and `c = goodHeightFamilyConstant ρ δ D₀ C G B`. Neither the
constant nor the two exponents depend on `i`. -/
theorem exists_goodHeight_norm_lower_bound_family_off_small_set {ι : Type*} {f : ι → ℂ → ℂ}
    {q : ι → ℝ} {x₀ ρ δ D₀ C B₀ G B : ℝ} (hf : ∀ i, AnalyticOnNhd ℂ (f i) univ)
    (hq : ∀ i, 1 ≤ q i) (hρ : 1 ≤ ρ) (hδ : 0 < δ) (hD₀ : 0 ≤ D₀) (hC : 1 ≤ C)
    (hB₀ : 0 ≤ B₀) (hG : 0 ≤ G)
    (hcentre : ∀ i (t : ℝ), δ * (q i * (2 + |t|)) ^ (-D₀) ≤ ‖f i ⟨x₀, t⟩‖)
    (hgrowth : ∀ i (s : ℂ), s.re ∈ Icc (x₀ - 6 * ρ) (x₀ + 6 * ρ) →
      ‖f i s‖ ≤ C * q i ^ B₀ * (2 + |s.im|) ^ G)
    (hB : ρ < B) (i : ι) (T : ℝ) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc T (T + 1) ∧ volume E ≤ ENNReal.ofReal (ρ / B) ∧
      ∀ t ∈ Icc T (T + 1) \ E, ∀ σ ∈ Icc (x₀ - 5 / 2 * ρ) (x₀ + 5 / 2 * ρ),
        goodHeightFamilyConstant ρ δ D₀ C G B *
            q i ^ (-(D₀ * (1 + goodHeightExponent B) + goodHeightExponent B * B₀)) *
            (2 + |T|) ^ (-(D₀ * (1 + goodHeightExponent B) + goodHeightExponent B * G)) ≤
          ‖f i ⟨σ, t⟩‖ := by
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  have hq0 : 0 < q i := zero_lt_one.trans_le (hq i)
  have hu0 : 0 < 2 + |T| := by linarith [abs_nonneg T]
  have ha : 0 < δ * (2 : ℝ) ^ (-D₀) := mul_pos hδ (Real.rpow_pos_of_pos two_pos _)
  have hc1 : 1 ≤ C * (1 + 6 * ρ) ^ G :=
    one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow (by linarith) hG)
  have hc : 0 < C * (1 + 6 * ρ) ^ G := zero_lt_one.trans_le hc1
  have hqB : 1 ≤ q i ^ B₀ := Real.one_le_rpow (hq i) hB₀
  have hδ' : 0 < δ * (2 : ℝ) ^ (-D₀) * (q i * (2 + |T|)) ^ (-D₀) :=
    mul_pos ha (Real.rpow_pos_of_pos (mul_pos hq0 hu0) _)
  have hfc : δ * (2 : ℝ) ^ (-D₀) * (q i * (2 + |T|)) ^ (-D₀) ≤ ‖f i ⟨x₀, T + 1 / 2⟩‖ :=
    exists_goodHeight_norm_lower_bound_family_off_small_set_center hδ.le hD₀ hq0
      (hcentre i (T + 1 / 2))
  have hC' : 1 ≤ C * (1 + 6 * ρ) ^ G * q i ^ B₀ := one_le_mul_of_one_le_of_one_le hc1 hqB
  have hbd : ∀ z ∈ Metric.sphere (⟨x₀, T + 1 / 2⟩ : ℂ) (6 * ρ),
      ‖f i z‖ ≤ C * (1 + 6 * ρ) ^ G * q i ^ B₀ * (2 + |T|) ^ G := by
    intro z hz
    refine (exists_goodHeight_norm_lower_bound_family_off_small_set_circle (T := T) hρ hG
      (mul_nonneg (zero_le_one.trans hC) (zero_le_one.trans hqB)) (hgrowth i) z hz).trans
      (le_of_eq ?_)
    ring
  obtain ⟨E, hEm, hEI, hEv, hgood⟩ :=
    exists_goodHeight_norm_lower_bound_of_growth (B := B) (hf i) hρ hδ' hfc hC' hG hbd hB
  refine ⟨E, hEm, hEI, hEv, fun t ht σ hσ ↦ ?_⟩
  have h := hgood t ht σ hσ
  have hid := exists_goodHeight_norm_lower_bound_family_off_small_set_rpow
    (κ := goodHeightExponent B) (D₀ := D₀) (B₀ := B₀) (G := G) ha hc hq0 hu0
  calc goodHeightFamilyConstant ρ δ D₀ C G B *
          q i ^ (-(D₀ * (1 + goodHeightExponent B) + goodHeightExponent B * B₀)) *
          (2 + |T|) ^ (-(D₀ * (1 + goodHeightExponent B) + goodHeightExponent B * G))
      = Real.exp (-(8 + 2 * B)) * (δ * (2 : ℝ) ^ (-D₀) *
          (δ * (2 : ℝ) ^ (-D₀) / (C * (1 + 6 * ρ) ^ G)) ^ goodHeightExponent B *
          q i ^ (-(D₀ * (1 + goodHeightExponent B) + goodHeightExponent B * B₀)) *
          (2 + |T|) ^ (-(D₀ * (1 + goodHeightExponent B) + goodHeightExponent B * G))) := by
        unfold goodHeightFamilyConstant
        ring
    _ = Real.exp (-(8 + 2 * B)) * (δ * (2 : ℝ) ^ (-D₀) * (q i * (2 + |T|)) ^ (-D₀) *
          (δ * (2 : ℝ) ^ (-D₀) * (q i * (2 + |T|)) ^ (-D₀) /
            (C * (1 + 6 * ρ) ^ G * q i ^ B₀)) ^ goodHeightExponent B *
          (2 + |T|) ^ (-(goodHeightExponent B * G))) := by rw [hid]
    _ = Real.exp (-(8 + 2 * B)) * (δ * (2 : ℝ) ^ (-D₀) * (q i * (2 + |T|)) ^ (-D₀)) *
          (δ * (2 : ℝ) ^ (-D₀) * (q i * (2 + |T|)) ^ (-D₀) /
            (C * (1 + 6 * ρ) ^ G * q i ^ B₀)) ^ goodHeightExponent B *
          (2 + |T|) ^ (-(goodHeightExponent B * G)) := by ring
    _ ≤ ‖f i ⟨σ, t⟩‖ := h

/-- One power of the product of the size and the height in place of two powers. -/
private theorem exists_goodHeight_norm_lower_bound_family_combine {c q u e₁ e₂ B₁ : ℝ}
    (hc : 0 ≤ c) (hq : 1 ≤ q) (hu : 1 ≤ u) (h₁ : e₁ ≤ B₁) (h₂ : e₂ ≤ B₁) :
    c * (q * u) ^ (-B₁) ≤ c * q ^ (-e₁) * u ^ (-e₂) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  rw [Real.mul_rpow hq0.le hu0.le, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (Real.rpow_le_rpow_of_exponent_le hq (by linarith))
      (Real.rpow_le_rpow_of_exponent_le hu (by linarith)) (Real.rpow_nonneg hu0.le _)
      (Real.rpow_nonneg hq0.le _)) hc

/-- A set of heights of measure at most one half does not cover a unit interval. -/
private theorem exists_goodHeight_norm_lower_bound_family_height {E : Set ℝ} {T ρ : ℝ}
    (hρ : 0 < ρ) (hE : volume E ≤ ENNReal.ofReal (ρ / (2 * ρ))) :
    ∃ t ∈ Icc T (T + 1), t ∉ E := by
  by_contra h
  have hsub : Icc T (T + 1) ⊆ E := fun x hx ↦ by
    by_contra hxE
    exact h ⟨x, hx, hxE⟩
  have h1 : volume (Icc T (T + 1)) ≤ ENNReal.ofReal (ρ / (2 * ρ)) :=
    (measure_mono hsub).trans hE
  rw [Real.volume_Icc, add_sub_cancel_left] at h1
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  have h3 : ρ / (2 * ρ) = 1 / 2 := by field_simp
  rw [h3] at h2
  norm_num at h2

/-- **A good height in every window, uniformly in a size.** Let `f i` be entire, with a size
`q i ≥ 1`, the lower bound `δ * (q i * (2 + |t|)) ^ (-D₀) ≤ ‖f i (x₀ + i t)‖` on the line of real
part `x₀` and the growth bound `‖f i s‖ ≤ C * q i ^ B₀ * (2 + |Im s|) ^ G` on the strip
`|Re s - x₀| ≤ 6 ρ`, with constants that do not depend on `i`. Then there are `c > 0` and
`B₁ ≥ 0`, the same for all `i`, such that for every `i` every unit window `[T, T + 1]` contains
a height `t` with `c * (q i * (2 + |T|)) ^ (-B₁) ≤ ‖f i (σ + i t)‖` for all real `σ` within
`5 ρ / 2` of `x₀`. One may take `c = goodHeightFamilyConstant ρ δ D₀ C G (2 ρ)` and
`B₁ = D₀ (1 + κ) + κ max B₀ G`, `κ = goodHeightExponent (2 ρ)`. -/
theorem exists_goodHeight_norm_lower_bound_family {ι : Type*} {f : ι → ℂ → ℂ}
    {q : ι → ℝ} {x₀ ρ δ D₀ C B₀ G : ℝ} (hf : ∀ i, AnalyticOnNhd ℂ (f i) univ)
    (hq : ∀ i, 1 ≤ q i) (hρ : 1 ≤ ρ) (hδ : 0 < δ) (hD₀ : 0 ≤ D₀) (hC : 1 ≤ C)
    (hB₀ : 0 ≤ B₀) (hG : 0 ≤ G)
    (hcentre : ∀ i (t : ℝ), δ * (q i * (2 + |t|)) ^ (-D₀) ≤ ‖f i ⟨x₀, t⟩‖)
    (hgrowth : ∀ i (s : ℂ), s.re ∈ Icc (x₀ - 6 * ρ) (x₀ + 6 * ρ) →
      ‖f i s‖ ≤ C * q i ^ B₀ * (2 + |s.im|) ^ G) :
    ∃ c B₁ : ℝ, 0 < c ∧ 0 ≤ B₁ ∧ ∀ (i : ι) (T : ℝ), ∃ t ∈ Icc T (T + 1),
      ∀ σ ∈ Icc (x₀ - 5 / 2 * ρ) (x₀ + 5 / 2 * ρ),
        c * (q i * (2 + |T|)) ^ (-B₁) ≤ ‖f i ⟨σ, t⟩‖ := by
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  have hκ : 0 ≤ goodHeightExponent (2 * ρ) := goodHeightExponent_nonneg (by linarith)
  have hc := goodHeightFamilyConstant_pos (D₀ := D₀) (G := G) (B := 2 * ρ) hρ0.le hδ
    (zero_lt_one.trans_le hC)
  refine ⟨goodHeightFamilyConstant ρ δ D₀ C G (2 * ρ),
    D₀ * (1 + goodHeightExponent (2 * ρ)) + goodHeightExponent (2 * ρ) * max B₀ G, hc,
    add_nonneg (mul_nonneg hD₀ (by linarith)) (mul_nonneg hκ (le_max_of_le_left hB₀)),
    fun i T ↦ ?_⟩
  obtain ⟨E, -, -, hEv, hgood⟩ :=
    exists_goodHeight_norm_lower_bound_family_off_small_set hf hq hρ hδ hD₀ hC hB₀ hG hcentre
      hgrowth (B := 2 * ρ) (by linarith) i T
  obtain ⟨t, ht, htE⟩ :=
    exists_goodHeight_norm_lower_bound_family_height (T := T) hρ0 hEv
  refine ⟨t, ht, fun σ hσ ↦ le_trans ?_ (hgood t ⟨ht, htE⟩ σ hσ)⟩
  exact exists_goodHeight_norm_lower_bound_family_combine hc.le (hq i)
    (by linarith [abs_nonneg T])
    (by linarith [mul_le_mul_of_nonneg_left (le_max_left B₀ G) hκ])
    (by linarith [mul_le_mul_of_nonneg_left (le_max_right B₀ G) hκ])

/-! ## Bounded entire functions with a lower bound `c / (‖s‖ + X) ^ n` on a line -/

/-- The lower bound `c / (‖s‖ + X) ^ n` on the line of real part `x₀`, as a power of
`X * (2 + |t|)`. -/
private theorem exists_goodHeight_windows_of_norm_le_one_center {c x₀ X t : ℝ} {n : ℕ}
    (hc : 0 ≤ c) (hX : 1 ≤ X) :
    c / (1 + |x₀|) ^ n * (X * (2 + |t|)) ^ (-(n : ℝ)) ≤ c / (‖(⟨x₀, t⟩ : ℂ)‖ + X) ^ n := by
  have hu : 0 < 2 + |t| := by linarith [abs_nonneg t]
  have hXu : 0 < X * (2 + |t|) := mul_pos (by linarith) hu
  have hXu1 : 1 ≤ X * (2 + |t|) := by nlinarith [abs_nonneg t]
  have hnorm : ‖(⟨x₀, t⟩ : ℂ)‖ ≤ |x₀| + |t| := Complex.norm_le_abs_re_add_abs_im _
  have hle : ‖(⟨x₀, t⟩ : ℂ)‖ + X ≤ (1 + |x₀|) * (X * (2 + |t|)) := by
    have h1 : X + |t| ≤ X * (2 + |t|) := by nlinarith [abs_nonneg t]
    have h2 : |x₀| ≤ |x₀| * (X * (2 + |t|)) := le_mul_of_one_le_right (abs_nonneg _) hXu1
    linarith
  have hpos : 0 < ‖(⟨x₀, t⟩ : ℂ)‖ + X := by linarith [norm_nonneg (⟨x₀, t⟩ : ℂ)]
  have heq : c / (1 + |x₀|) ^ n * ((X * (2 + |t|)) ^ n)⁻¹ =
      c / ((1 + |x₀|) * (X * (2 + |t|))) ^ n := by
    rw [← div_eq_mul_inv, div_div, ← mul_pow]
  rw [Real.rpow_neg hXu.le, Real.rpow_natCast, heq]
  exact div_le_div_of_nonneg_left hc (pow_pos hpos n) (pow_le_pow_left₀ hpos.le hle n)

/-- From a power of the product `X * (2 + |u|)` at the window `[u, u + 1]` to a natural power
of the sum `X + |t| + 2` at the height `t` itself. -/
private theorem exists_goodHeight_windows_of_norm_le_one_arith {c₁ B₁ X t u : ℝ}
    (hc : 0 ≤ c₁) (hB : 0 ≤ B₁) (hX : 1 ≤ X) (ht : t ∈ Icc u (u + 1)) :
    c₁ / (X + |t| + 2) ^ ⌈2 * B₁⌉₊ ≤ c₁ * (X * (2 + |u|)) ^ (-B₁) := by
  have hb1 : 1 ≤ X + |t| + 2 := by linarith [abs_nonneg t]
  have hb0 : 0 < X + |t| + 2 := by linarith
  have hu : |u| ≤ |t| + 1 := by
    rw [abs_le]
    constructor
    · linarith [ht.2, neg_abs_le t]
    · linarith [ht.1, le_abs_self t]
  have hXu0 : 0 < X * (2 + |u|) := mul_pos (by linarith) (by linarith [abs_nonneg u])
  have hle : X * (2 + |u|) ≤ (X + |t| + 2) ^ (2 : ℝ) := by
    have h5 : X * (2 + |u|) ≤ X * (X + |t| + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h6 : X * (X + |t| + 2) ≤ (X + |t| + 2) * (X + |t| + 2) :=
      mul_le_mul_of_nonneg_right (by linarith [abs_nonneg t]) hb0.le
    rw [Real.rpow_two, sq]
    linarith
  have h1 : (X + |t| + 2) ^ (-(⌈2 * B₁⌉₊ : ℝ)) ≤ (X + |t| + 2) ^ (-(2 * B₁)) :=
    Real.rpow_le_rpow_of_exponent_le hb1 (neg_le_neg (Nat.le_ceil _))
  have h2 : (X + |t| + 2) ^ (-(2 * B₁)) = ((X + |t| + 2) ^ (2 : ℝ)) ^ (-B₁) := by
    rw [← Real.rpow_mul hb0.le]
    congr 1
    ring
  have h3 : ((X + |t| + 2) ^ (2 : ℝ)) ^ (-B₁) ≤ (X * (2 + |u|)) ^ (-B₁) :=
    Real.rpow_le_rpow_of_nonpos hXu0 hle (by linarith)
  have h4 : c₁ / (X + |t| + 2) ^ ⌈2 * B₁⌉₊ = c₁ * (X + |t| + 2) ^ (-(⌈2 * B₁⌉₊ : ℝ)) := by
    rw [Real.rpow_neg hb0.le, Real.rpow_natCast, div_eq_mul_inv]
  rw [h4]
  exact mul_le_mul_of_nonneg_left (h1.trans (h2.le.trans h3)) hc

/-- **Good heights for bounded entire functions, with constants chosen before the function.**
Fix a real `x₀`, a scale `ρ ≥ 1`, a constant `c > 0` and a natural number `n`. There are
`c' > 0` and a natural number `n'`, depending only on these four, such that the following holds
for every entire function `ϑ` and every real `X ≥ 1`: if `‖ϑ s‖ ≤ 1` on the strip
`x₀ - 6 ρ ≤ Re s ≤ x₀ + 6 ρ` and `c / (‖s‖ + X) ^ n ≤ ‖ϑ s‖` on the line `Re s = x₀`, then
every window `[2 k, 2 k + 1]`, `k` an integer, contains a height `T k` with
`c' / (X + |T k| + 2) ^ n' ≤ ‖ϑ (σ + i T k)‖` for all real `σ` within `5 ρ / 2` of `x₀`.
This is the form for a family of functions of different sizes `X`: neither `c'` nor `n'` depends
on the function or on its size. -/
theorem exists_goodHeight_windows_of_norm_le_one {x₀ ρ c : ℝ} {n : ℕ} (hρ : 1 ≤ ρ)
    (hc : 0 < c) :
    ∃ (c' : ℝ) (n' : ℕ), 0 < c' ∧ ∀ (ϑ : ℂ → ℂ) (X : ℝ), Differentiable ℂ ϑ → 1 ≤ X →
      (∀ s : ℂ, x₀ - 6 * ρ ≤ s.re → s.re ≤ x₀ + 6 * ρ → ‖ϑ s‖ ≤ 1) →
      (∀ s : ℂ, s.re = x₀ → c / (‖s‖ + X) ^ n ≤ ‖ϑ s‖) →
      ∃ T : ℤ → ℝ, (∀ k : ℤ, T k ∈ Icc (2 * (k : ℝ)) (2 * k + 1)) ∧
        ∀ k : ℤ, ∀ σ ∈ Icc (x₀ - 5 / 2 * ρ) (x₀ + 5 / 2 * ρ),
          c' / (X + |T k| + 2) ^ n' ≤ ‖ϑ ⟨σ, T k⟩‖ := by
  -- the family of all admissible pairs of a function and a size
  let ι := {p : (ℂ → ℂ) × ℝ // Differentiable ℂ p.1 ∧ 1 ≤ p.2 ∧
    (∀ s : ℂ, x₀ - 6 * ρ ≤ s.re → s.re ≤ x₀ + 6 * ρ → ‖p.1 s‖ ≤ 1) ∧
    ∀ s : ℂ, s.re = x₀ → c / (‖s‖ + p.2) ^ n ≤ ‖p.1 s‖}
  have hδ : 0 < c / (1 + |x₀|) ^ n := div_pos hc (pow_pos (by linarith [abs_nonneg x₀]) n)
  have hcentre : ∀ (p : ι) (t : ℝ),
      c / (1 + |x₀|) ^ n * (p.1.2 * (2 + |t|)) ^ (-(n : ℝ)) ≤ ‖p.1.1 ⟨x₀, t⟩‖ := fun p t ↦
    (exists_goodHeight_windows_of_norm_le_one_center hc.le p.2.2.1).trans
      (p.2.2.2.2 ⟨x₀, t⟩ rfl)
  have hgrowth : ∀ (p : ι) (s : ℂ), s.re ∈ Icc (x₀ - 6 * ρ) (x₀ + 6 * ρ) →
      ‖p.1.1 s‖ ≤ 1 * p.1.2 ^ (0 : ℝ) * (2 + |s.im|) ^ (0 : ℝ) := fun p s hs ↦ by
    rw [Real.rpow_zero, Real.rpow_zero, mul_one, mul_one]
    exact p.2.2.2.1 s hs.1 hs.2
  obtain ⟨c₁, B₁, hc₁, hB₁, h⟩ := exists_goodHeight_norm_lower_bound_family
    (f := fun p : ι ↦ p.1.1) (q := fun p : ι ↦ p.1.2)
    (fun p s _ ↦ p.2.1.analyticAt s) (fun p ↦ p.2.2.1) hρ hδ (Nat.cast_nonneg n) le_rfl
    le_rfl le_rfl hcentre hgrowth
  refine ⟨c₁, ⌈2 * B₁⌉₊, hc₁, fun ϑ X hϑ hX hb hl ↦ ?_⟩
  choose T hT hT' using fun k : ℤ ↦ h ⟨(ϑ, X), hϑ, hX, hb, hl⟩ (2 * (k : ℝ))
  refine ⟨T, hT, fun k σ hσ ↦ le_trans ?_ (hT' k σ hσ)⟩
  exact exists_goodHeight_windows_of_norm_le_one_arith hc₁.le hB₁ hX (hT k)

end RiemannMasullo
