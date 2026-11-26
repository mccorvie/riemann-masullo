module

public import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Trigonometric.SincIntegral
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-! # The diagonal integral on the Paley–Wiener level in the rational real-place model

Paper: Theorem 12.4.1.1, pp. 514–519, and its use in the proof of Theorem 12.5.1.1, p. 520.

**The model.** `F = ℚ`, `S = {∞}`, order `s = 0`, sharp cutoffs. Functions are even functions
on `ℝ`, written on the half-line `x > 0`. The dilation by `g > 0` is
`D_g f (x) = g^(-1/2) f (x / g)`. The band `B_Y` is the space of even square-integrable
functions whose Fourier transform is supported in `[-Y, Y]`. On the half-line its orthogonal
projection has the kernel `S (x - y) + S (x + y)`, where `S u = sin (2π Y u) / (π u)` is
`realBandKernel Y u`. The polar-free level is the closure in `L²` of the even Schwartz functions
of the band with `f 0 = 0` and `∫ f = 0`. On the band `f 0` is the inner product with `S`, of
square norm `2 Y`, so the first condition is closed; the second is not continuous for the `L²`
norm and does not survive the closure. The level is therefore the band less the line of `S`,
and its projection has the kernel `S (x - y) + S (x + y) - S x * S y / Y`.

The operator `1_[0,L] ∘ D_g ∘ Q_Y` then has the kernel `g^(-1/2) q (x / g, y)` for `x ≤ L`.
Its diagonal is `g^(-1/2) * realPWLevelDiagonal Y g x`, and for a test function `φ` and the
measure `d×g = dg / g` the integral over the diagonal is

`∫ x in 0..L, ∫ g in a..b, φ g * ((√g)⁻¹ * realPWLevelDiagonal Y g x) / g`.

**Results.** For `φ` continuous on `[a, b]` with `0 < a` and `1 ∉ [a, b]`, and `Y * L → ∞`
along any filter:

* `sLocalTrace_realPWBand_diagonal_tendsto`: with the band in place of the level the limit is
  `1/2 ∫ φ(g) g^(1/2) (1/|1 - g| + 1/|1 + g|) d×g`, the real-place term of (12.5.1.1) for an
  even test function. This is what pp. 516–519 compute.
* `sLocalTrace_realPWLevel_diagonal_tendsto`: on the level the limit is that term minus
  `∫ φ(g) min(g^(1/2), g^(-1/2)) d×g`. For a test function supported above norm one this is
  `V_∞ - L₋` in the notation of the comments on issue 7354
  (`sLocalTrace_realPWLevel_diagonal_tendsto_of_one_lt`), the case without finite places of the
  limit stated there for every finite set of rational places.
* `sLocalTrace_realPWLevel_diagonal_not_tendsto_principalValue` and
  `sLocalTrace_realPWLevel_diagonal_not_tendsto_sub_poles`: for `φ > 0` on `(a, b)` the limit
  on the level is neither the real-place term alone nor that term minus
  `∫ φ(g) (g^(1/2) + g^(-1/2)) d×g`, the value used on p. 520.

* `sLocalTrace_realPWLevel_diagonal_floor_tendsto` and
  `sLocalTrace_realPWLevel_diagonal_floor_tendsto_zero`: with a spatial floor, as in the
  cutoffs on `[1/λ, λ]` of Definition 9.3.3.1 and footnote 2 on p. 514, the limit is unchanged
  when `Y * h → 0` and is zero when `Y * h → ∞`. `tendsto_integral_realPWLevelDiagonal_floor`
  gives the value in between.

The computation is exact at every finite `Y` and `L`: the integral over `[0, L]` of each of
the three diagonals is a combination of sine integrals and cosines at multiples of `Y * L`
(`integral_realPWBandDiagonal`, `integral_realPWPolarDiagonal`), and the limits follow from the
Dirichlet integral.

**Not formalized.** The description of the level and of its projection given above, and the
identification of the diagonal integral with a trace. `Isolated.sLocalTrace_projectedCutoffKernel`
in `Sec4_Isolated.lean` proves that identification at a fixed level for a continuous cutoff and
an operator that preserves the level; the dilations do not preserve the band, and the cutoff
here is sharp. Only `s = 0` and one real place are treated, and the test function is supported
away from `g = 1`.
-/

open Filter MeasureTheory Set Topology Real
open scoped Interval

@[expose] public noncomputable section

namespace RiemannMasullo

/-! ### The band kernel -/

/-- The kernel of the projection of `L²(ℝ)` onto the functions with Fourier transform
supported in `[-Y, Y]`, as a function of the difference of the two arguments:
`sin (2π Y u) / (π u)`, written `2 Y sinc (2π Y u)` so that it is defined at `u = 0`. -/
noncomputable def realBandKernel (Y u : ℝ) : ℝ := 2 * Y * sinc (2 * π * Y * u)

/-- The band kernel is continuous. -/
theorem continuous_realBandKernel (Y : ℝ) : Continuous (realBandKernel Y) := by
  unfold realBandKernel
  exact continuous_const.mul (continuous_sinc.comp (by fun_prop))

/-- The band kernel is the integral of the cosines of the band. -/
theorem integral_cos_eq_realBandKernel (Y x : ℝ) :
    ∫ η in (-Y)..Y, cos (2 * π * x * η) = realBandKernel Y x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [realBandKernel]
    ring
  · have hc : 2 * π * x ≠ 0 := by positivity
    rw [intervalIntegral.integral_comp_mul_left (fun t ↦ cos t) hc, integral_cos, realBandKernel,
      show 2 * π * Y * x = (2 * π * Y) * x by ring]
    have h := mul_sinc_mul (2 * π * Y) hx
    have h2 : 2 * Y * sinc (2 * π * Y * x) = sin (2 * π * Y * x) / (π * x) := by
      have : 2 * Y * sinc (2 * π * Y * x) = (2 * π * Y * sinc (2 * π * Y * x)) / π := by
        field_simp
      rw [this, h]
      field_simp
    rw [h2, smul_eq_mul, show 2 * π * x * -Y = -(2 * π * Y * x) by ring,
      show 2 * π * x * Y = 2 * π * Y * x by ring, sin_neg]
    field_simp
    ring

/-- The integral of the band kernel along a ray `u = c x`. -/
theorem integral_realBandKernel_mul {c : ℝ} (hc : c ≠ 0) (Y L : ℝ) :
    ∫ x in (0 : ℝ)..L, realBandKernel Y (c * x) =
      (π * c)⁻¹ * ∫ t in (0 : ℝ)..(2 * π * c * (Y * L)), sinc t := by
  have h := integral_mul_sinc_mul (2 * π * Y * c) L
  rw [show 2 * π * Y * c * L = 2 * π * c * (Y * L) by ring] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ ↦ ?_
  simp only [realBandKernel]
  rw [show 2 * π * Y * (c * x) = 2 * π * Y * c * x by ring]
  field_simp

/-- The integral over `[0, L]` of the product of the band kernel at `x / g` and at `x`, as an
integral over the band of integrals of `sinc`. -/
theorem integral_realBandKernel_mul_realBandKernel {g : ℝ} (hg : g ≠ 0) (Y L : ℝ) :
    ∫ x in (0 : ℝ)..L, realBandKernel Y (x / g) * realBandKernel Y x =
      g / (2 * π) * ∫ η in (-Y)..Y,
        ((∫ t in (0 : ℝ)..((2 * π * Y / g + 2 * π * η) * L), sinc t) +
          ∫ t in (0 : ℝ)..((2 * π * Y / g - 2 * π * η) * L), sinc t) := by
  have hF : Continuous (Function.uncurry fun x η : ℝ ↦
      realBandKernel Y (x / g) * cos (2 * π * x * η)) := by
    unfold Function.uncurry
    exact ((continuous_realBandKernel Y).comp (by fun_prop)).mul (by fun_prop)
  have hswap := MeasureTheory.intervalIntegral_intervalIntegral_swap
    (F := fun x η : ℝ ↦ realBandKernel Y (x / g) * cos (2 * π * x * η))
    (a := 0) (b := L) (c := -Y) (d := Y)
    ((hF.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc))
  have hleft : ∫ x in (0 : ℝ)..L, realBandKernel Y (x / g) * realBandKernel Y x =
      ∫ x in (0 : ℝ)..L, ∫ η in (-Y)..Y, realBandKernel Y (x / g) * cos (2 * π * x * η) := by
    refine intervalIntegral.integral_congr fun x _ ↦ ?_
    rw [intervalIntegral.integral_const_mul, integral_cos_eq_realBandKernel]
  rw [hleft, hswap, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun η _ ↦ ?_
  have h := integral_mul_sinc_mul_cos (2 * π * Y / g) (2 * π * η) L
  have hpt : ∀ x : ℝ, realBandKernel Y (x / g) * cos (2 * π * x * η) =
      g / π * (2 * π * Y / g * sinc (2 * π * Y / g * x) * cos (2 * π * η * x)) := fun x ↦ by
    simp only [realBandKernel]
    rw [show 2 * π * Y * (x / g) = 2 * π * Y / g * x by ring,
      show 2 * π * x * η = 2 * π * η * x by ring]
    field_simp
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, h]
  field_simp

/-- The integral over `[0, L]` of the product of the band kernel at `x / g` and at `x`, in
closed form: sine integrals and cosines at multiples of `Y * L`. -/
theorem integral_realBandKernel_mul_realBandKernel_eq {g Y L : ℝ} (hg : g ≠ 0) (hY : Y ≠ 0)
    (hL : L ≠ 0) :
    ∫ x in (0 : ℝ)..L, realBandKernel Y (x / g) * realBandKernel Y x =
      Y * (g / π * ((1 / g + 1) * (∫ t in (0 : ℝ)..(2 * π * (1 / g + 1) * (Y * L)), sinc t) -
        (1 / g - 1) * (∫ t in (0 : ℝ)..(2 * π * (1 / g - 1) * (Y * L)), sinc t) +
        (cos (2 * π * (1 / g + 1) * (Y * L)) - cos (2 * π * (1 / g - 1) * (Y * L))) /
          (2 * π * (Y * L)))) := by
  have hk : 2 * π * (Y * L) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) (mul_ne_zero hY hL)
  have hsub := intervalIntegral.smul_integral_comp_mul_left (a := (-1 : ℝ)) (b := 1)
    (fun η : ℝ ↦ (∫ t in (0 : ℝ)..((2 * π * Y / g + 2 * π * η) * L), sinc t) +
      ∫ t in (0 : ℝ)..((2 * π * Y / g - 2 * π * η) * L), sinc t) Y
  rw [mul_neg_one, mul_one, smul_eq_mul] at hsub
  have hpt : ∀ ζ : ℝ, ((∫ t in (0 : ℝ)..((2 * π * Y / g + 2 * π * (Y * ζ)) * L), sinc t) +
      ∫ t in (0 : ℝ)..((2 * π * Y / g - 2 * π * (Y * ζ)) * L), sinc t) =
      (∫ t in (0 : ℝ)..(2 * π * (Y * L) * (1 / g + ζ)), sinc t) +
        ∫ t in (0 : ℝ)..(2 * π * (Y * L) * (1 / g - ζ)), sinc t := fun ζ ↦ by
    rw [show (2 * π * Y / g + 2 * π * (Y * ζ)) * L = 2 * π * (Y * L) * (1 / g + ζ) by ring,
      show (2 * π * Y / g - 2 * π * (Y * ζ)) * L = 2 * π * (Y * L) * (1 / g - ζ) by ring]
  have hci (s : ℝ) : IntervalIntegrable
      (fun ζ : ℝ ↦ ∫ t in (0 : ℝ)..(2 * π * (Y * L) * (1 / g + s * ζ)), sinc t) volume (-1) 1 :=
    (continuous_integral_sinc.comp (by fun_prop)).intervalIntegrable _ _
  have h1 := hci 1
  have h2 := hci (-1)
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at h1 h2
  rw [integral_realBandKernel_mul_realBandKernel hg, ← hsub]
  simp_rw [hpt]
  rw [intervalIntegral.integral_add h1 h2, integral_integral_sinc_add hk,
    integral_integral_sinc_sub hk,
    show 2 * π * (Y * L) * (1 / g + 1) = 2 * π * (1 / g + 1) * (Y * L) by ring,
    show 2 * π * (Y * L) * (1 / g - 1) = 2 * π * (1 / g - 1) * (Y * L) by ring]
  field_simp
  ring

/-! ### The diagonals under a dilation -/

/-- Paper: Theorem 12.4.1.1, pp. 516–517. The diagonal of the kernel of the dilation by `g`
composed with the band projection, on even functions and without the factor `g^(-1/2)`:
`S (x / g - x) + S (x / g + x)` with `S = realBandKernel Y`.
Reconstruction: the rational real-place model at order zero that the file header describes. -/
noncomputable def realPWBandDiagonal (Y g x : ℝ) : ℝ :=
  realBandKernel Y (x / g - x) + realBandKernel Y (x / g + x)

/-- Paper: Theorem 12.4.1.1, pp. 514–515. The diagonal of the kernel of the dilation by `g`
composed with the rank-one projection onto the reproducing kernel of the band at the origin,
without the factor `g^(-1/2)`: `S (x / g) * S x / Y`.
Reconstruction: in the model this projection is the difference between the band and the
level. -/
noncomputable def realPWPolarDiagonal (Y g x : ℝ) : ℝ :=
  realBandKernel Y (x / g) * realBandKernel Y x / Y

/-- Paper: Theorem 12.4.1.1, pp. 514–515. The diagonal on the polar-free level: the band less
the rank-one term.
Reconstruction: see the file header. -/
noncomputable def realPWLevelDiagonal (Y g x : ℝ) : ℝ :=
  realPWBandDiagonal Y g x - realPWPolarDiagonal Y g x

/-- The integral of the band diagonal over `[0, L]`, as a function of `R = Y * L` and `g`. -/
noncomputable def realPWBandDiagonalMass (R g : ℝ) : ℝ :=
  (π * (1 / g - 1))⁻¹ * (∫ t in (0 : ℝ)..(2 * π * (1 / g - 1) * R), sinc t) +
    (π * (1 / g + 1))⁻¹ * (∫ t in (0 : ℝ)..(2 * π * (1 / g + 1) * R), sinc t)

/-- The integral of the rank-one diagonal over `[0, L]`, as a function of `R = Y * L` and
`g`. -/
noncomputable def realPWPolarDiagonalMass (R g : ℝ) : ℝ :=
  g / π * ((1 / g + 1) * (∫ t in (0 : ℝ)..(2 * π * (1 / g + 1) * R), sinc t) -
    (1 / g - 1) * (∫ t in (0 : ℝ)..(2 * π * (1 / g - 1) * R), sinc t) +
    (cos (2 * π * (1 / g + 1) * R) - cos (2 * π * (1 / g - 1) * R)) / (2 * π * R))

/-- The band diagonal is continuous in `x`. -/
theorem continuous_realPWBandDiagonal (Y g : ℝ) : Continuous (realPWBandDiagonal Y g) := by
  unfold realPWBandDiagonal
  exact ((continuous_realBandKernel Y).comp (by fun_prop)).add
    ((continuous_realBandKernel Y).comp (by fun_prop))

/-- The rank-one diagonal is continuous in `x`. -/
theorem continuous_realPWPolarDiagonal (Y g : ℝ) : Continuous (realPWPolarDiagonal Y g) := by
  unfold realPWPolarDiagonal
  exact (((continuous_realBandKernel Y).comp (by fun_prop)).mul
    (continuous_realBandKernel Y)).div_const _

/-- The integral of the band diagonal over `[0, L]`. -/
theorem integral_realPWBandDiagonal {g : ℝ} (hg0 : 0 < g) (hg1 : g ≠ 1) (Y L : ℝ) :
    ∫ x in (0 : ℝ)..L, realPWBandDiagonal Y g x = realPWBandDiagonalMass (Y * L) g := by
  have hm : 1 / g - 1 ≠ 0 := by
    rw [sub_ne_zero, Ne, div_eq_iff hg0.ne', one_mul]
    exact fun h ↦ hg1 h.symm
  have hp : 1 / g + 1 ≠ 0 := by positivity
  have h : ∀ x : ℝ, realPWBandDiagonal Y g x =
      realBandKernel Y ((1 / g - 1) * x) + realBandKernel Y ((1 / g + 1) * x) := fun x ↦ by
    rw [realPWBandDiagonal, show x / g - x = (1 / g - 1) * x by ring,
      show x / g + x = (1 / g + 1) * x by ring]
  have hc (c : ℝ) : IntervalIntegrable (fun x : ℝ ↦ realBandKernel Y (c * x)) volume 0 L :=
    ((continuous_realBandKernel Y).comp (continuous_const.mul continuous_id)).intervalIntegrable
      _ _
  simp_rw [h]
  rw [intervalIntegral.integral_add (hc _) (hc _), integral_realBandKernel_mul hm,
    integral_realBandKernel_mul hp, realPWBandDiagonalMass]

/-- The integral of the rank-one diagonal over `[0, L]`. -/
theorem integral_realPWPolarDiagonal {g Y L : ℝ} (hg : g ≠ 0) (hY : Y ≠ 0) (hL : L ≠ 0) :
    ∫ x in (0 : ℝ)..L, realPWPolarDiagonal Y g x = realPWPolarDiagonalMass (Y * L) g := by
  unfold realPWPolarDiagonal realPWPolarDiagonalMass
  rw [intervalIntegral.integral_div, integral_realBandKernel_mul_realBandKernel_eq hg hY hL,
    mul_div_cancel_left₀ _ hY]

/-! ### Limits of the masses -/

section Limits

variable {ι : Type*} {l : Filter ι} {R : ι → ℝ}

private theorem tendsto_mul_integral_sinc (hR : Tendsto R l atTop) (c : ℝ) :
    Tendsto (fun i ↦ c * ∫ t in (0 : ℝ)..(2 * π * c * R i), sinc t) l (𝓝 (|c| * (π / 2))) := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have h := (tendsto_integral_sinc_mul_of_neg hR (c := 2 * π * c)
      (by nlinarith [pi_pos])).const_mul c
    rwa [abs_of_neg hc, neg_mul, ← mul_neg]
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ)) l (𝓝 0))
  · have h := (tendsto_integral_sinc_mul_of_pos hR (c := 2 * π * c) (by positivity)).const_mul c
    rwa [abs_of_pos hc]

private theorem tendsto_inv_mul_integral_sinc (hR : Tendsto R l atTop) {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun i ↦ (π * c)⁻¹ * ∫ t in (0 : ℝ)..(2 * π * c * R i), sinc t) l
      (𝓝 ((2 * |c|)⁻¹)) := by
  have h := (tendsto_mul_integral_sinc hR c).const_mul ((π * c ^ 2)⁻¹)
  have hc2 : c ^ 2 = |c| ^ 2 := (sq_abs c).symm
  have habs : |c| ≠ 0 := abs_ne_zero.mpr hc
  have e : (π * c ^ 2)⁻¹ * (|c| * (π / 2)) = (2 * |c|)⁻¹ := by
    rw [hc2]
    field_simp
  rw [e] at h
  refine h.congr fun i ↦ ?_
  field_simp

private theorem tendsto_cos_sub_cos_div (hR : Tendsto R l atTop) (u v : ι → ℝ) :
    Tendsto (fun i ↦ (cos (u i) - cos (v i)) / (2 * π * R i)) l (𝓝 0) := by
  have h0 : Tendsto (fun i ↦ 2 / (2 * π * R i)) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hR.const_mul_atTop (by positivity))
  refine squeeze_zero_norm' ?_ h0
  filter_upwards [hR.eventually_gt_atTop 0] with i hi
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < 2 * π * R i)]
  have hc1 := abs_cos_le_one (u i)
  have hc2 := abs_cos_le_one (v i)
  gcongr
  exact (abs_sub _ _).trans (by linarith)

/-- The band mass tends to `1 / (2 |1 / g - 1|) + 1 / (2 (1 / g + 1))`. -/
theorem tendsto_realPWBandDiagonalMass (hR : Tendsto R l atTop) {g : ℝ} (hg0 : 0 < g)
    (hg1 : g ≠ 1) :
    Tendsto (fun i ↦ realPWBandDiagonalMass (R i) g) l
      (𝓝 ((2 * |1 / g - 1|)⁻¹ + (2 * (1 / g + 1))⁻¹)) := by
  have hm : 1 / g - 1 ≠ 0 := by
    rw [sub_ne_zero, Ne, div_eq_iff hg0.ne', one_mul]
    exact fun h ↦ hg1 h.symm
  have hp : 0 < 1 / g + 1 := by positivity
  have h := (tendsto_inv_mul_integral_sinc hR hm).add (tendsto_inv_mul_integral_sinc hR hp.ne')
  rwa [abs_of_pos hp] at h

/-- The rank-one mass tends to `min 1 g`. -/
theorem tendsto_realPWPolarDiagonalMass (hR : Tendsto R l atTop) {g : ℝ} (hg0 : 0 < g) :
    Tendsto (fun i ↦ realPWPolarDiagonalMass (R i) g) l (𝓝 (min 1 g)) := by
  have hp : 0 < 1 / g + 1 := by positivity
  have h := ((((tendsto_mul_integral_sinc hR (1 / g + 1)).sub
    (tendsto_mul_integral_sinc hR (1 / g - 1))).add
    (tendsto_cos_sub_cos_div hR (fun i ↦ 2 * π * (1 / g + 1) * R i)
      (fun i ↦ 2 * π * (1 / g - 1) * R i))).const_mul (g / π))
  have e : g / π * (|1 / g + 1| * (π / 2) - |1 / g - 1| * (π / 2) + 0) = min 1 g := by
    rw [abs_of_pos hp]
    rcases le_total g 1 with h1 | h1
    · have : 0 ≤ 1 / g - 1 := by
        rw [sub_nonneg, le_div_iff₀ hg0]
        linarith
      rw [abs_of_nonneg this, min_eq_right h1]
      field_simp
      ring
    · have : 1 / g - 1 ≤ 0 := by
        rw [sub_nonpos, div_le_iff₀ hg0]
        linarith
      rw [abs_of_nonpos this, min_eq_left h1]
      field_simp
      ring
  rw [e] at h
  exact h

end Limits

/-! ### Bounds and measurability of the masses -/

/-- A bound for the band mass that does not depend on `R`. -/
theorem abs_realPWBandDiagonalMass_le (R g : ℝ) :
    |realPWBandDiagonalMass R g| ≤
      ((π * |1 / g - 1|)⁻¹ + (π * |1 / g + 1|)⁻¹) * (π / 2 + 2) := by
  unfold realPWBandDiagonalMass
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_inv, abs_inv, abs_mul, abs_mul, abs_of_pos pi_pos, add_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (abs_integral_sinc_le _) (by positivity))
    (mul_le_mul_of_nonneg_left (abs_integral_sinc_le _) (by positivity))

/-- The cosine difference of the rank-one mass as a product of two sines. -/
private theorem abs_cos_sub_cos_eq (g R : ℝ) :
    |cos (2 * π * (1 / g + 1) * R) - cos (2 * π * (1 / g - 1) * R)| =
      2 * |sin (2 * π * (1 / g) * R)| * |sin (2 * π * R)| := by
  rw [cos_sub_cos,
    show (2 * π * (1 / g + 1) * R + 2 * π * (1 / g - 1) * R) / 2 = 2 * π * (1 / g) * R by ring,
    show (2 * π * (1 / g + 1) * R - 2 * π * (1 / g - 1) * R) / 2 = 2 * π * R by ring,
    abs_mul, abs_mul, abs_neg, abs_two]

/-- The cosine term of the rank-one mass is at most `2`, for every `R`. -/
private theorem abs_cos_sub_cos_div_le_two (g R : ℝ) :
    |(cos (2 * π * (1 / g + 1) * R) - cos (2 * π * (1 / g - 1) * R)) / (2 * π * R)| ≤ 2 := by
  rcases eq_or_ne R 0 with rfl | hR
  · simp
  · have hpos : 0 < |2 * π * R| := abs_pos.mpr (mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hR)
    have h1 := abs_sin_le_one (2 * π * (1 / g) * R)
    have h2 : |sin (2 * π * R)| ≤ |2 * π * R| := abs_sin_le_abs
    rw [abs_div, div_le_iff₀ hpos, abs_cos_sub_cos_eq]
    nlinarith [abs_nonneg (sin (2 * π * (1 / g) * R)), abs_nonneg (sin (2 * π * R))]

/-- The cosine term of the rank-one mass is `O(R)` near `R = 0`. -/
private theorem abs_cos_sub_cos_div_le_mul (g R : ℝ) :
    |(cos (2 * π * (1 / g + 1) * R) - cos (2 * π * (1 / g - 1) * R)) / (2 * π * R)| ≤
      2 * |2 * π * (1 / g) * R| := by
  rcases eq_or_ne R 0 with rfl | hR
  · simp
  · have hpos : 0 < |2 * π * R| := abs_pos.mpr (mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hR)
    have h1 : |sin (2 * π * (1 / g) * R)| ≤ |2 * π * (1 / g) * R| := abs_sin_le_abs
    have h2 : |sin (2 * π * R)| ≤ |2 * π * R| := abs_sin_le_abs
    rw [abs_div, div_le_iff₀ hpos, abs_cos_sub_cos_eq]
    nlinarith [abs_nonneg (sin (2 * π * (1 / g) * R)), abs_nonneg (sin (2 * π * R)),
      abs_nonneg (2 * π * (1 / g) * R)]

/-- A bound for the rank-one mass that does not depend on `R`. -/
theorem abs_realPWPolarDiagonalMass_le (R g : ℝ) :
    |realPWPolarDiagonalMass R g| ≤
      |g| / π * ((|1 / g + 1| + |1 / g - 1|) * (π / 2 + 2) + 2) := by
  unfold realPWPolarDiagonalMass
  rw [abs_mul, abs_div, abs_of_pos pi_pos]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hcos := abs_cos_sub_cos_div_le_two g R
  have h1 : |(1 / g + 1) * ∫ t in (0 : ℝ)..(2 * π * (1 / g + 1) * R), sinc t| ≤
      |1 / g + 1| * (π / 2 + 2) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_integral_sinc_le _) (abs_nonneg _)
  have h2 : |(1 / g - 1) * ∫ t in (0 : ℝ)..(2 * π * (1 / g - 1) * R), sinc t| ≤
      |1 / g - 1| * (π / 2 + 2) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_integral_sinc_le _) (abs_nonneg _)
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add ((abs_sub _ _).trans (add_le_add h1 h2)) hcos).trans (le_of_eq ?_)
  ring

/-- The band mass is measurable in `g`. -/
theorem measurable_realPWBandDiagonalMass (R : ℝ) : Measurable (realPWBandDiagonalMass R) := by
  obtain ⟨G, hG, hGdef⟩ : ∃ G : ℝ → ℝ, Measurable G ∧ ∀ u, G u = ∫ v in (0 : ℝ)..u, sinc v :=
    ⟨_, continuous_integral_sinc.measurable, fun _ ↦ rfl⟩
  have h : realPWBandDiagonalMass R = fun g ↦ (π * (1 / g - 1))⁻¹ * G (2 * π * (1 / g - 1) * R) +
      (π * (1 / g + 1))⁻¹ * G (2 * π * (1 / g + 1) * R) := by
    funext g
    simp only [realPWBandDiagonalMass, hGdef]
  rw [h]
  fun_prop

/-- The rank-one mass is measurable in `g`. -/
theorem measurable_realPWPolarDiagonalMass (R : ℝ) : Measurable (realPWPolarDiagonalMass R) := by
  obtain ⟨G, hG, hGdef⟩ : ∃ G : ℝ → ℝ, Measurable G ∧ ∀ u, G u = ∫ v in (0 : ℝ)..u, sinc v :=
    ⟨_, continuous_integral_sinc.measurable, fun _ ↦ rfl⟩
  have h : realPWPolarDiagonalMass R = fun g ↦ g / π * ((1 / g + 1) * G (2 * π * (1 / g + 1) * R) -
      (1 / g - 1) * G (2 * π * (1 / g - 1) * R) +
      (cos (2 * π * (1 / g + 1) * R) - cos (2 * π * (1 / g - 1) * R)) / (2 * π * R)) := by
    funext g
    simp only [realPWPolarDiagonalMass, hGdef]
  rw [h]
  fun_prop

/-! ### The limit of the diagonal integrals -/

section Main

variable {a b : ℝ} {w : ℝ → ℝ}

private theorem one_div_sub_one_ne_zero {g : ℝ} (hg0 : 0 < g) (hg1 : g ≠ 1) : 1 / g - 1 ≠ 0 := by
  rw [sub_ne_zero, Ne, div_eq_iff hg0.ne', one_mul]
  exact fun h ↦ hg1 h.symm

private theorem ne_one_of_mem_Icc (h1 : 1 ∉ Icc a b) {g : ℝ} (hg : g ∈ Icc a b) : g ≠ 1 :=
  fun h ↦ h1 (h ▸ hg)

private theorem continuousOn_one_div (ha : 0 < a) :
    ContinuousOn (fun g : ℝ ↦ 1 / g) (Icc a b) :=
  continuousOn_const.div continuousOn_id fun _ hg ↦ (ha.trans_le hg.1).ne'

private theorem continuousOn_bandBound (ha : 0 < a) (hab : a ≤ b) (h1 : 1 ∉ Icc a b) (c d : ℝ)
    (hc : c ≠ 0) :
    ContinuousOn (fun g : ℝ ↦ ((c * |1 / g - 1|)⁻¹ + (c * |1 / g + 1|)⁻¹) * d) (uIcc a b) := by
  rw [uIcc_of_le hab]
  have hm : ContinuousOn (fun g : ℝ ↦ c * |1 / g - 1|) (Icc a b) :=
    continuousOn_const.mul ((continuousOn_one_div ha).sub continuousOn_const).abs
  have hp : ContinuousOn (fun g : ℝ ↦ c * |1 / g + 1|) (Icc a b) :=
    continuousOn_const.mul ((continuousOn_one_div ha).add continuousOn_const).abs
  refine ((hm.inv₀ fun g hg ↦ ?_).add (hp.inv₀ fun g hg ↦ ?_)).mul continuousOn_const
  · exact mul_ne_zero hc (abs_ne_zero.mpr
      (one_div_sub_one_ne_zero (ha.trans_le hg.1) (ne_one_of_mem_Icc h1 hg)))
  · have hg0 : 0 < g := ha.trans_le hg.1
    have : 0 < 1 / g + 1 := by positivity
    exact mul_ne_zero hc (abs_ne_zero.mpr this.ne')

private theorem continuousOn_polarBound (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun g : ℝ ↦ |g| / π * ((|1 / g + 1| + |1 / g - 1|) * (π / 2 + 2) + 2))
      (uIcc a b) := by
  rw [uIcc_of_le hab]
  exact (continuous_abs.continuousOn.div_const π).mul
    (((((continuousOn_one_div ha).add continuousOn_const).abs.add
      ((continuousOn_one_div ha).sub continuousOn_const).abs).mul continuousOn_const).add
      continuousOn_const)

/-- The limit density of the band is continuous on an interval that avoids `0` and `1`. -/
theorem continuousOn_realPWBandDiagonalLimit (ha : 0 < a) (hab : a ≤ b) (h1 : 1 ∉ Icc a b) :
    ContinuousOn (fun g : ℝ ↦ (2 * |1 / g - 1|)⁻¹ + (2 * (1 / g + 1))⁻¹) (uIcc a b) := by
  have h := continuousOn_bandBound ha hab h1 2 1 two_ne_zero
  refine h.congr fun g hg ↦ ?_
  rw [uIcc_of_le hab] at hg
  have hg0 : 0 < g := ha.trans_le hg.1
  have : 0 < 1 / g + 1 := by positivity
  simp only [mul_one, abs_of_pos this]

variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]

private theorem tendsto_intervalIntegral_mul_of_abs_le {K : ℝ → ℝ}
    (hw : IntervalIntegrable w volume a b) (hK : ContinuousOn K (uIcc a b))
    {F : ι → ℝ → ℝ} {f : ℝ → ℝ} (hFm : ∀ᶠ i in l, Measurable (F i))
    (hbound : ∀ᶠ i in l, ∀ g ∈ Ι a b, |F i g| ≤ K g)
    (hlim : ∀ g ∈ Ι a b, Tendsto (fun i ↦ F i g) l (𝓝 (f g))) :
    Tendsto (fun i ↦ ∫ g in a..b, w g * F i g) l (𝓝 (∫ g in a..b, w g * f g)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun g ↦ |w g| * K g) ?_ ?_ (hw.abs.mul_continuousOn hK) ?_
  · filter_upwards [hFm] with i hi
    exact hw.def'.aestronglyMeasurable.mul hi.aestronglyMeasurable
  · filter_upwards [hbound] with i hi
    refine Eventually.of_forall fun g hg ↦ ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hi g hg) (abs_nonneg _)
  · exact Eventually.of_forall fun g hg ↦ (hlim g hg).const_mul (w g)

variable {R : ι → ℝ}

/-- The weighted band masses tend to the weighted limit density. -/
theorem tendsto_integral_realPWBandDiagonalMass (ha : 0 < a) (hab : a ≤ b) (h1 : 1 ∉ Icc a b)
    (hw : IntervalIntegrable w volume a b) (hR : Tendsto R l atTop) :
    Tendsto (fun i ↦ ∫ g in a..b, w g * realPWBandDiagonalMass (R i) g) l
      (𝓝 (∫ g in a..b, w g * ((2 * |1 / g - 1|)⁻¹ + (2 * (1 / g + 1))⁻¹))) := by
  refine tendsto_intervalIntegral_mul_of_abs_le hw
    (continuousOn_bandBound ha hab h1 π (π / 2 + 2) pi_ne_zero)
    (Eventually.of_forall fun i ↦ measurable_realPWBandDiagonalMass _)
    (Eventually.of_forall fun i g _ ↦ abs_realPWBandDiagonalMass_le _ _) fun g hg ↦ ?_
  rw [uIoc_of_le hab] at hg
  exact tendsto_realPWBandDiagonalMass hR (ha.trans hg.1)
    (ne_one_of_mem_Icc h1 (Ioc_subset_Icc_self hg))

/-- The weighted rank-one masses tend to the integral of the weight against `min 1 g`. -/
theorem tendsto_integral_realPWPolarDiagonalMass (ha : 0 < a) (hab : a ≤ b)
    (hw : IntervalIntegrable w volume a b) (hR : Tendsto R l atTop) :
    Tendsto (fun i ↦ ∫ g in a..b, w g * realPWPolarDiagonalMass (R i) g) l
      (𝓝 (∫ g in a..b, w g * min 1 g)) := by
  refine tendsto_intervalIntegral_mul_of_abs_le hw (continuousOn_polarBound ha hab)
    (Eventually.of_forall fun i ↦ measurable_realPWPolarDiagonalMass _)
    (Eventually.of_forall fun i g _ ↦ abs_realPWPolarDiagonalMass_le _ g) fun g hg ↦ ?_
  rw [uIoc_of_le hab] at hg
  exact tendsto_realPWPolarDiagonalMass hR (ha.trans hg.1)

/-- The weighted level masses tend to the difference of the two limits. -/
theorem tendsto_integral_realPWLevelDiagonalMass (ha : 0 < a) (hab : a ≤ b) (h1 : 1 ∉ Icc a b)
    (hw : IntervalIntegrable w volume a b) (hR : Tendsto R l atTop) :
    Tendsto (fun i ↦ ∫ g in a..b,
        w g * (realPWBandDiagonalMass (R i) g - realPWPolarDiagonalMass (R i) g)) l
      (𝓝 (∫ g in a..b, w g * ((2 * |1 / g - 1|)⁻¹ + (2 * (1 / g + 1))⁻¹ - min 1 g))) := by
  refine tendsto_intervalIntegral_mul_of_abs_le hw
    ((continuousOn_bandBound ha hab h1 π (π / 2 + 2) pi_ne_zero).add
      (continuousOn_polarBound ha hab))
    (Eventually.of_forall fun i ↦ (measurable_realPWBandDiagonalMass _).sub
      (measurable_realPWPolarDiagonalMass _))
    (Eventually.of_forall fun i g _ ↦ (abs_sub _ _).trans
      (add_le_add (abs_realPWBandDiagonalMass_le _ _) (abs_realPWPolarDiagonalMass_le _ g)))
    fun g hg ↦ ?_
  rw [uIoc_of_le hab] at hg
  exact (tendsto_realPWBandDiagonalMass hR (ha.trans hg.1)
    (ne_one_of_mem_Icc h1 (Ioc_subset_Icc_self hg))).sub
    (tendsto_realPWPolarDiagonalMass hR (ha.trans hg.1))

/-- The integral of the level diagonal over `[0, L]`. -/
theorem integral_realPWLevelDiagonal {g Y L : ℝ} (hg0 : 0 < g) (hg1 : g ≠ 1) (hY : Y ≠ 0)
    (hL : L ≠ 0) :
    ∫ x in (0 : ℝ)..L, realPWLevelDiagonal Y g x =
      realPWBandDiagonalMass (Y * L) g - realPWPolarDiagonalMass (Y * L) g := by
  unfold realPWLevelDiagonal
  rw [intervalIntegral.integral_sub ((continuous_realPWBandDiagonal Y g).intervalIntegrable _ _)
    ((continuous_realPWPolarDiagonal Y g).intervalIntegrable _ _),
    integral_realPWBandDiagonal hg0 hg1, integral_realPWPolarDiagonal hg0.ne' hY hL]

variable {Y L : ι → ℝ}

/-- The weighted integrals of the band diagonal over `[0, L] × [a, b]` tend to the weighted
limit density when `Y * L → ∞`. -/
theorem tendsto_integral_realPWBandDiagonal (ha : 0 < a) (hab : a ≤ b) (h1 : 1 ∉ Icc a b)
    (hw : IntervalIntegrable w volume a b) (hYL : Tendsto (fun i ↦ Y i * L i) l atTop) :
    Tendsto (fun i ↦ ∫ g in a..b, w g * ∫ x in (0 : ℝ)..L i, realPWBandDiagonal (Y i) g x) l
      (𝓝 (∫ g in a..b, w g * ((2 * |1 / g - 1|)⁻¹ + (2 * (1 / g + 1))⁻¹))) := by
  refine (tendsto_integral_realPWBandDiagonalMass ha hab h1 hw hYL).congr fun i ↦ ?_
  refine intervalIntegral.integral_congr fun g hg ↦ ?_
  rw [uIcc_of_le hab] at hg
  rw [integral_realPWBandDiagonal (ha.trans_le hg.1) (ne_one_of_mem_Icc h1 hg)]

/-- The weighted integrals of the rank-one diagonal over `[0, L] × [a, b]` tend to the integral
of the weight against `min 1 g` when `Y * L → ∞`. -/
theorem tendsto_integral_realPWPolarDiagonal (ha : 0 < a) (hab : a ≤ b)
    (hw : IntervalIntegrable w volume a b) (hYL : Tendsto (fun i ↦ Y i * L i) l atTop) :
    Tendsto (fun i ↦ ∫ g in a..b, w g * ∫ x in (0 : ℝ)..L i, realPWPolarDiagonal (Y i) g x) l
      (𝓝 (∫ g in a..b, w g * min 1 g)) := by
  refine (tendsto_integral_realPWPolarDiagonalMass ha hab hw hYL).congr' ?_
  filter_upwards [hYL.eventually_gt_atTop 0] with i hi
  refine intervalIntegral.integral_congr fun g hg ↦ ?_
  rw [uIcc_of_le hab] at hg
  rw [integral_realPWPolarDiagonal (ha.trans_le hg.1).ne' (left_ne_zero_of_mul hi.ne')
    (right_ne_zero_of_mul hi.ne')]

/-- The weighted integrals of the level diagonal over `[0, L] × [a, b]` tend to the difference
of the two limits when `Y * L → ∞`. -/
theorem tendsto_integral_realPWLevelDiagonal (ha : 0 < a) (hab : a ≤ b) (h1 : 1 ∉ Icc a b)
    (hw : IntervalIntegrable w volume a b) (hYL : Tendsto (fun i ↦ Y i * L i) l atTop) :
    Tendsto (fun i ↦ ∫ g in a..b, w g * ∫ x in (0 : ℝ)..L i, realPWLevelDiagonal (Y i) g x) l
      (𝓝 (∫ g in a..b, w g * ((2 * |1 / g - 1|)⁻¹ + (2 * (1 / g + 1))⁻¹ - min 1 g))) := by
  refine (tendsto_integral_realPWLevelDiagonalMass ha hab h1 hw hYL).congr' ?_
  filter_upwards [hYL.eventually_gt_atTop 0] with i hi
  refine intervalIntegral.integral_congr fun g hg ↦ ?_
  rw [uIcc_of_le hab] at hg
  rw [integral_realPWLevelDiagonal (ha.trans_le hg.1) (ne_one_of_mem_Icc h1 hg)
    (left_ne_zero_of_mul hi.ne') (right_ne_zero_of_mul hi.ne')]

end Main

/-! ### A spatial floor

Definition 9.3.3.1 and footnote 2 on p. 514 use spatial cutoffs supported on `[1/λ, λ]`. With a
sharp cutoff `1_[h, L]` the diagonal integral is the difference of the closed forms at `Y * L`
and at `Y * h`, so the limit depends on `Y * h`: it is the limit without a floor when
`Y * h → 0`, it is zero when `Y * h → ∞`, and in between it is the limit without a floor minus
the mass at `lim Y * h`. -/

section Floor

/-- The band mass is continuous in `R`. -/
theorem continuous_realPWBandDiagonalMass_left (g : ℝ) :
    Continuous fun R : ℝ ↦ realPWBandDiagonalMass R g := by
  unfold realPWBandDiagonalMass
  exact (continuous_const.mul (continuous_integral_sinc.comp (by fun_prop))).add
    (continuous_const.mul (continuous_integral_sinc.comp (by fun_prop)))

private theorem continuous_cos_sub_cos_div (g : ℝ) :
    Continuous fun R : ℝ ↦
      (cos (2 * π * (1 / g + 1) * R) - cos (2 * π * (1 / g - 1) * R)) / (2 * π * R) := by
  rw [continuous_iff_continuousAt]
  intro R
  rcases eq_or_ne R 0 with rfl | hR
  · have h0 : Tendsto (fun R : ℝ ↦ 2 * |2 * π * (1 / g) * R|) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun R : ℝ ↦ 2 * |2 * π * (1 / g) * R| := by fun_prop
      simpa using hc.tendsto 0
    have h := squeeze_zero_norm (fun R ↦ by
      rw [Real.norm_eq_abs]
      exact abs_cos_sub_cos_div_le_mul g R) h0
    rw [ContinuousAt]
    simpa using h
  · exact ContinuousAt.div (by fun_prop) (by fun_prop)
      (mul_ne_zero (mul_ne_zero two_ne_zero pi_ne_zero) hR)

/-- The rank-one mass is continuous in `R`. -/
theorem continuous_realPWPolarDiagonalMass_left (g : ℝ) :
    Continuous fun R : ℝ ↦ realPWPolarDiagonalMass R g := by
  unfold realPWPolarDiagonalMass
  exact continuous_const.mul
    (((continuous_const.mul (continuous_integral_sinc.comp (by fun_prop))).sub
      (continuous_const.mul (continuous_integral_sinc.comp (by fun_prop)))).add
      (continuous_cos_sub_cos_div g))

/-- The band mass vanishes at `R = 0`. -/
theorem realPWBandDiagonalMass_zero (g : ℝ) : realPWBandDiagonalMass 0 g = 0 := by
  simp [realPWBandDiagonalMass]

/-- The rank-one mass vanishes at `R = 0`. -/
theorem realPWPolarDiagonalMass_zero (g : ℝ) : realPWPolarDiagonalMass 0 g = 0 := by
  simp [realPWPolarDiagonalMass]

/-- The integral of the level diagonal over `[h, L]`: the closed form at `Y * L` minus the
closed form at `Y * h`. -/
theorem integral_realPWLevelDiagonal_floor {g Y L : ℝ} (hg0 : 0 < g) (hg1 : g ≠ 1) (hY : Y ≠ 0)
    (hL : L ≠ 0) (h : ℝ) :
    ∫ x in h..L, realPWLevelDiagonal Y g x =
      (realPWBandDiagonalMass (Y * L) g - realPWPolarDiagonalMass (Y * L) g) -
        (realPWBandDiagonalMass (Y * h) g - realPWPolarDiagonalMass (Y * h) g) := by
  have hc : Continuous (realPWLevelDiagonal Y g) := by
    unfold realPWLevelDiagonal
    exact (continuous_realPWBandDiagonal Y g).sub (continuous_realPWPolarDiagonal Y g)
  have h0 : ∫ x in (0 : ℝ)..h, realPWLevelDiagonal Y g x =
      realPWBandDiagonalMass (Y * h) g - realPWPolarDiagonalMass (Y * h) g := by
    rcases eq_or_ne h 0 with rfl | hh
    · simp [realPWBandDiagonalMass_zero, realPWPolarDiagonalMass_zero]
    · exact integral_realPWLevelDiagonal hg0 hg1 hY hh
  rw [← intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable 0 L)
    (hc.intervalIntegrable 0 h), integral_realPWLevelDiagonal hg0 hg1 hY hL, h0]

variable {a b : ℝ} {w : ℝ → ℝ} {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
  {Y L h : ι → ℝ}

private theorem eventually_integral_floor_eq (ha : 0 < a) (hab : a ≤ b) (h1 : 1 ∉ Icc a b)
    (hYL : Tendsto (fun i ↦ Y i * L i) l atTop) :
    (fun i ↦ ∫ g in a..b, w g *
      ((realPWBandDiagonalMass (Y i * L i) g - realPWPolarDiagonalMass (Y i * L i) g) -
        (realPWBandDiagonalMass (Y i * h i) g - realPWPolarDiagonalMass (Y i * h i) g))) =ᶠ[l]
      fun i ↦ ∫ g in a..b, w g * ∫ x in (h i)..(L i), realPWLevelDiagonal (Y i) g x := by
  filter_upwards [hYL.eventually_gt_atTop 0] with i hi
  refine intervalIntegral.integral_congr fun g hg ↦ ?_
  rw [uIcc_of_le hab] at hg
  rw [integral_realPWLevelDiagonal_floor (ha.trans_le hg.1) (ne_one_of_mem_Icc h1 hg)
    (left_ne_zero_of_mul hi.ne') (right_ne_zero_of_mul hi.ne')]

/-- Paper: Theorem 12.4.1.1, p. 514, footnote 2. With a spatial floor `h` such that
`Y * h → c`, the weighted integrals of the level diagonal over `[h, L] × [a, b]` tend to the
limit without a floor minus the weighted mass at `c`. -/
theorem tendsto_integral_realPWLevelDiagonal_floor (ha : 0 < a) (hab : a ≤ b)
    (h1 : 1 ∉ Icc a b) (hw : IntervalIntegrable w volume a b)
    (hYL : Tendsto (fun i ↦ Y i * L i) l atTop) {c : ℝ}
    (hYh : Tendsto (fun i ↦ Y i * h i) l (𝓝 c)) :
    Tendsto (fun i ↦ ∫ g in a..b, w g * ∫ x in (h i)..(L i), realPWLevelDiagonal (Y i) g x) l
      (𝓝 (∫ g in a..b, w g * (((2 * |1 / g - 1|)⁻¹ + (2 * (1 / g + 1))⁻¹ - min 1 g) -
        (realPWBandDiagonalMass c g - realPWPolarDiagonalMass c g)))) := by
  refine Tendsto.congr' (eventually_integral_floor_eq ha hab h1 hYL) ?_
  have hK := (continuousOn_bandBound ha hab h1 π (π / 2 + 2) pi_ne_zero).add
    (continuousOn_polarBound ha hab)
  refine tendsto_intervalIntegral_mul_of_abs_le hw (hK.add hK)
    (Eventually.of_forall fun i ↦ ((measurable_realPWBandDiagonalMass _).sub
      (measurable_realPWPolarDiagonalMass _)).sub ((measurable_realPWBandDiagonalMass _).sub
      (measurable_realPWPolarDiagonalMass _)))
    (Eventually.of_forall fun i g _ ↦ (abs_sub _ _).trans (add_le_add
      ((abs_sub _ _).trans (add_le_add (abs_realPWBandDiagonalMass_le _ _)
        (abs_realPWPolarDiagonalMass_le _ g)))
      ((abs_sub _ _).trans (add_le_add (abs_realPWBandDiagonalMass_le _ _)
        (abs_realPWPolarDiagonalMass_le _ g)))))
    fun g hg ↦ ?_
  rw [uIoc_of_le hab] at hg
  exact ((tendsto_realPWBandDiagonalMass hYL (ha.trans hg.1)
    (ne_one_of_mem_Icc h1 (Ioc_subset_Icc_self hg))).sub
    (tendsto_realPWPolarDiagonalMass hYL (ha.trans hg.1))).sub
    ((((continuous_realPWBandDiagonalMass_left g).tendsto c).comp hYh).sub
      (((continuous_realPWPolarDiagonalMass_left g).tendsto c).comp hYh))

/-- A floor with `Y * h → 0` does not change the limit. -/
theorem tendsto_integral_realPWLevelDiagonal_floor_zero (ha : 0 < a) (hab : a ≤ b)
    (h1 : 1 ∉ Icc a b) (hw : IntervalIntegrable w volume a b)
    (hYL : Tendsto (fun i ↦ Y i * L i) l atTop) (hYh : Tendsto (fun i ↦ Y i * h i) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ g in a..b, w g * ∫ x in (h i)..(L i), realPWLevelDiagonal (Y i) g x) l
      (𝓝 (∫ g in a..b, w g * ((2 * |1 / g - 1|)⁻¹ + (2 * (1 / g + 1))⁻¹ - min 1 g))) := by
  have h := tendsto_integral_realPWLevelDiagonal_floor ha hab h1 hw hYL hYh
  simpa only [realPWBandDiagonalMass_zero, realPWPolarDiagonalMass_zero, sub_zero] using h

/-- A floor with `Y * h → ∞` removes the whole limit: the integrals tend to zero. -/
theorem tendsto_integral_realPWLevelDiagonal_floor_atTop (ha : 0 < a) (hab : a ≤ b)
    (h1 : 1 ∉ Icc a b) (hw : IntervalIntegrable w volume a b)
    (hYL : Tendsto (fun i ↦ Y i * L i) l atTop) (hYh : Tendsto (fun i ↦ Y i * h i) l atTop) :
    Tendsto (fun i ↦ ∫ g in a..b, w g * ∫ x in (h i)..(L i), realPWLevelDiagonal (Y i) g x) l
      (𝓝 0) := by
  refine Tendsto.congr' (eventually_integral_floor_eq ha hab h1 hYL) ?_
  have hK := (continuousOn_bandBound ha hab h1 π (π / 2 + 2) pi_ne_zero).add
    (continuousOn_polarBound ha hab)
  have hlim : ∀ g ∈ Ι a b, Tendsto (fun i ↦
      (realPWBandDiagonalMass (Y i * L i) g - realPWPolarDiagonalMass (Y i * L i) g) -
        (realPWBandDiagonalMass (Y i * h i) g - realPWPolarDiagonalMass (Y i * h i) g)) l
      (𝓝 ((fun _ : ℝ ↦ (0 : ℝ)) g)) := fun g hg ↦ by
    rw [uIoc_of_le hab] at hg
    have hg1 := ne_one_of_mem_Icc h1 (Ioc_subset_Icc_self hg)
    have t := ((tendsto_realPWBandDiagonalMass hYL (ha.trans hg.1) hg1).sub
      (tendsto_realPWPolarDiagonalMass hYL (ha.trans hg.1))).sub
      ((tendsto_realPWBandDiagonalMass hYh (ha.trans hg.1) hg1).sub
        (tendsto_realPWPolarDiagonalMass hYh (ha.trans hg.1)))
    rwa [sub_self] at t
  have key := tendsto_intervalIntegral_mul_of_abs_le hw (hK.add hK)
    (Eventually.of_forall fun i ↦ ((measurable_realPWBandDiagonalMass _).sub
      (measurable_realPWPolarDiagonalMass _)).sub ((measurable_realPWBandDiagonalMass _).sub
      (measurable_realPWPolarDiagonalMass _)))
    (Eventually.of_forall fun i g _ ↦ (abs_sub _ _).trans (add_le_add
      ((abs_sub _ _).trans (add_le_add (abs_realPWBandDiagonalMass_le _ _)
        (abs_realPWPolarDiagonalMass_le _ g)))
      ((abs_sub _ _).trans (add_le_add (abs_realPWBandDiagonalMass_le _ _)
        (abs_realPWPolarDiagonalMass_le _ g)))))
    hlim
  simpa only [mul_zero, intervalIntegral.integral_zero, Pi.sub_apply] using key

end Floor

/-! ### The diagonal integral in the other order -/

section Swap

variable {a b : ℝ} {w : ℝ → ℝ}

private theorem integral_integral_mul_swap {d : ℝ → ℝ → ℝ} (hab : a ≤ b)
    (hw : ContinuousOn w (Icc a b)) (h L : ℝ)
    (hd : ContinuousOn (fun p : ℝ × ℝ ↦ d p.2 p.1) (uIcc h L ×ˢ uIcc a b)) :
    ∫ x in h..L, ∫ g in a..b, w g * d g x =
      ∫ g in a..b, w g * ∫ x in h..L, d g x := by
  have hw' : ContinuousOn (fun p : ℝ × ℝ ↦ w p.2) (uIcc h L ×ˢ uIcc a b) :=
    hw.comp continuousOn_snd fun p hp ↦ by
      rw [← uIcc_of_le hab]
      exact hp.2
  have hcont : ContinuousOn (Function.uncurry fun x g : ℝ ↦ w g * d g x)
      (uIcc h L ×ˢ uIcc a b) := hw'.mul hd
  rw [MeasureTheory.intervalIntegral_intervalIntegral_swap
    ((hcont.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc))]
  refine intervalIntegral.integral_congr fun g _ ↦ ?_
  exact intervalIntegral.integral_const_mul _ _

private theorem continuousOn_div_prod (ha : 0 < a) (hab : a ≤ b) (h L : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ ↦ p.1 / p.2) (uIcc h L ×ˢ uIcc a b) :=
  continuousOn_fst.div continuousOn_snd fun p hp ↦ by
    have h := hp.2
    rw [uIcc_of_le hab] at h
    exact (ha.trans_le h.1).ne'

private theorem continuousOn_realPWBandDiagonal_prod (ha : 0 < a) (hab : a ≤ b)
    (Y h L : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ ↦ realPWBandDiagonal Y p.2 p.1) (uIcc h L ×ˢ uIcc a b) := by
  have hq := continuousOn_div_prod ha hab h L
  have hS := continuous_realBandKernel Y
  unfold realPWBandDiagonal
  exact (hS.comp_continuousOn (hq.sub continuousOn_fst)).add
    (hS.comp_continuousOn (hq.add continuousOn_fst))

private theorem continuousOn_realPWPolarDiagonal_prod (ha : 0 < a) (hab : a ≤ b)
    (Y h L : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ ↦ realPWPolarDiagonal Y p.2 p.1) (uIcc h L ×ˢ uIcc a b) := by
  have hq := continuousOn_div_prod ha hab h L
  have hS := continuous_realBandKernel Y
  unfold realPWPolarDiagonal
  exact ((hS.comp_continuousOn hq).mul (hS.comp_continuousOn continuousOn_fst)).div_const Y

/-- The two orders of integration of the weighted band diagonal agree. -/
theorem integral_integral_realPWBandDiagonal_swap (ha : 0 < a) (hab : a ≤ b)
    (hw : ContinuousOn w (Icc a b)) (Y L : ℝ) :
    ∫ x in (0 : ℝ)..L, ∫ g in a..b, w g * realPWBandDiagonal Y g x =
      ∫ g in a..b, w g * ∫ x in (0 : ℝ)..L, realPWBandDiagonal Y g x :=
  integral_integral_mul_swap hab hw 0 L (continuousOn_realPWBandDiagonal_prod ha hab Y 0 L)

/-- The two orders of integration of the weighted level diagonal agree, over `[h, L]`. -/
theorem integral_integral_realPWLevelDiagonal_swap_floor (ha : 0 < a) (hab : a ≤ b)
    (hw : ContinuousOn w (Icc a b)) (Y h L : ℝ) :
    ∫ x in h..L, ∫ g in a..b, w g * realPWLevelDiagonal Y g x =
      ∫ g in a..b, w g * ∫ x in h..L, realPWLevelDiagonal Y g x := by
  refine integral_integral_mul_swap hab hw h L ?_
  unfold realPWLevelDiagonal
  exact (continuousOn_realPWBandDiagonal_prod ha hab Y h L).sub
    (continuousOn_realPWPolarDiagonal_prod ha hab Y h L)

/-- The two orders of integration of the weighted level diagonal agree. -/
theorem integral_integral_realPWLevelDiagonal_swap (ha : 0 < a) (hab : a ≤ b)
    (hw : ContinuousOn w (Icc a b)) (Y L : ℝ) :
    ∫ x in (0 : ℝ)..L, ∫ g in a..b, w g * realPWLevelDiagonal Y g x =
      ∫ g in a..b, w g * ∫ x in (0 : ℝ)..L, realPWLevelDiagonal Y g x :=
  integral_integral_realPWLevelDiagonal_swap_floor ha hab hw Y 0 L

end Swap

/-! ### The limits in the variables of the paper -/

section Paper

/-- The limit density of the band in the variables of the paper. -/
theorem realPWBandDiagonalLimit_eq {g : ℝ} (hg0 : 0 < g) (hg1 : g ≠ 1) :
    (√g * g)⁻¹ * ((2 * |1 / g - 1|)⁻¹ + (2 * (1 / g + 1))⁻¹) =
      1 / 2 * (√g / |1 - g| + √g / |1 + g|) / g := by
  have hs : 0 < √g := Real.sqrt_pos.mpr hg0
  have hgs : g = √g ^ 2 := (Real.sq_sqrt hg0.le).symm
  have hA : |1 - g| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hg1.symm)
  have e1 : |1 / g - 1| = |1 - g| / g := by
    rw [show 1 / g - 1 = (1 - g) / g by field_simp, abs_div, abs_of_pos hg0]
  have e2 : |1 + g| = 1 + g := abs_of_pos (by positivity)
  rw [e1, e2]
  generalize |1 - g| = A at hA ⊢
  generalize √g = s at hs hgs ⊢
  subst hgs
  field_simp

/-- The limit density of the rank-one term in the variables of the paper. -/
theorem realPWPolarDiagonalLimit_eq {g : ℝ} (hg0 : 0 < g) :
    (√g * g)⁻¹ * min 1 g = min (√g) (√g)⁻¹ / g := by
  have hs : 0 < √g := Real.sqrt_pos.mpr hg0
  have hgs : g = √g ^ 2 := (Real.sq_sqrt hg0.le).symm
  rcases le_total g 1 with h | h
  · have hs1 : √g ≤ 1 := Real.sqrt_le_one.mpr h
    have : √g ≤ (√g)⁻¹ := hs1.trans ((one_le_inv₀ hs).mpr hs1)
    rw [min_eq_right h, min_eq_left this]
    generalize √g = s at hs hgs ⊢
    subst hgs
    field_simp
  · have hs1 : 1 ≤ √g := Real.one_le_sqrt.mpr h
    have : (√g)⁻¹ ≤ √g := (inv_le_one_of_one_le₀ hs1).trans hs1
    rw [min_eq_left h, min_eq_right this]
    generalize √g = s at hs hgs ⊢
    subst hgs
    field_simp

variable {a b : ℝ} {φ : ℝ → ℝ}

private theorem continuousOn_weight (ha : 0 < a) (hφ : ContinuousOn φ (Icc a b)) :
    ContinuousOn (fun g : ℝ ↦ φ g * (√g * g)⁻¹) (Icc a b) :=
  hφ.mul ((Real.continuous_sqrt.continuousOn.mul continuousOn_id).inv₀ fun _ hg ↦
    mul_ne_zero (Real.sqrt_pos.mpr (ha.trans_le hg.1)).ne' (ha.trans_le hg.1).ne')

private theorem intervalIntegrable_weight (ha : 0 < a) (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) :
    IntervalIntegrable (fun g : ℝ ↦ φ g * (√g * g)⁻¹) volume a b := by
  have h := continuousOn_weight ha hφ
  rw [← uIcc_of_le hab] at h
  exact h.intervalIntegrable

private theorem integral_weight_band (ha : 0 < a) (hab : a ≤ b) (h1 : 1 ∉ Icc a b) :
    ∫ g in a..b, φ g * (√g * g)⁻¹ * ((2 * |1 / g - 1|)⁻¹ + (2 * (1 / g + 1))⁻¹) =
      ∫ g in a..b, φ g * (1 / 2 * (√g / |1 - g| + √g / |1 + g|)) / g := by
  refine intervalIntegral.integral_congr fun g hg ↦ ?_
  rw [uIcc_of_le hab] at hg
  rw [mul_assoc, realPWBandDiagonalLimit_eq (ha.trans_le hg.1) (ne_one_of_mem_Icc h1 hg)]
  ring

private theorem integral_weight_polar (ha : 0 < a) (hab : a ≤ b) :
    ∫ g in a..b, φ g * (√g * g)⁻¹ * min 1 g = ∫ g in a..b, φ g * min (√g) (√g)⁻¹ / g := by
  refine intervalIntegral.integral_congr fun g hg ↦ ?_
  rw [uIcc_of_le hab] at hg
  rw [mul_assoc, realPWPolarDiagonalLimit_eq (ha.trans_le hg.1)]
  ring

private theorem integral_weight_level (ha : 0 < a) (hab : a ≤ b) (h1 : 1 ∉ Icc a b)
    (hφ : ContinuousOn φ (Icc a b)) :
    ∫ g in a..b, φ g * (√g * g)⁻¹ * ((2 * |1 / g - 1|)⁻¹ + (2 * (1 / g + 1))⁻¹ - min 1 g) =
      (∫ g in a..b, φ g * (1 / 2 * (√g / |1 - g| + √g / |1 + g|)) / g) -
        ∫ g in a..b, φ g * min (√g) (√g)⁻¹ / g := by
  have hwi := intervalIntegrable_weight ha hab hφ
  have hI1 := hwi.mul_continuousOn (continuousOn_realPWBandDiagonalLimit ha hab h1)
  have hI2 := hwi.mul_continuousOn
    (continuous_const.min continuous_id : Continuous fun g : ℝ ↦ min 1 g).continuousOn
  have hsplit : (fun g : ℝ ↦ φ g * (√g * g)⁻¹ *
      ((2 * |1 / g - 1|)⁻¹ + (2 * (1 / g + 1))⁻¹ - min 1 g)) = fun g ↦
      φ g * (√g * g)⁻¹ * ((2 * |1 / g - 1|)⁻¹ + (2 * (1 / g + 1))⁻¹) -
        φ g * (√g * g)⁻¹ * min 1 g := funext fun g ↦ mul_sub _ _ _
  rw [hsplit, intervalIntegral.integral_sub hI1 hI2, integral_weight_band ha hab h1,
    integral_weight_polar ha hab]

variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {Y L : ι → ℝ}

/-- Paper: Theorem 12.4.1.1, pp. 516–519, and (12.5.1.1), p. 519. In the rational real-place
model at order zero, with sharp cutoffs, the diagonal integral of the dilation average composed
with the band projection tends to `1/2 ∫ φ(g) g^(1/2) (1/|1 - g| + 1/|1 + g|) d×g`, the
real-place term of (12.5.1.1) for an even test function, when `Y * L → ∞`. The test function
is continuous on `[a, b]`, with `0 < a` and `1 ∉ [a, b]`, so no principal value and no
counterterm is needed.
Reconstruction: the diagonal integral stands for the regularized trace with the Fourier cutoff;
the identification of the two is not formalized. -/
theorem sLocalTrace_realPWBand_diagonal_tendsto (ha : 0 < a) (hab : a ≤ b) (h1 : 1 ∉ Icc a b)
    (hφ : ContinuousOn φ (Icc a b)) (hYL : Tendsto (fun i ↦ Y i * L i) l atTop) :
    Tendsto (fun i ↦ ∫ x in (0 : ℝ)..L i, ∫ g in a..b,
        φ g * ((√g)⁻¹ * realPWBandDiagonal (Y i) g x) / g) l
      (𝓝 (∫ g in a..b, φ g * (1 / 2 * (√g / |1 - g| + √g / |1 + g|)) / g)) := by
  rw [← integral_weight_band ha hab h1]
  refine (tendsto_integral_realPWBandDiagonal ha hab h1 (intervalIntegrable_weight ha hab hφ)
    hYL).congr fun i ↦ ?_
  rw [← integral_integral_realPWBandDiagonal_swap ha hab (continuousOn_weight ha hφ)]
  refine intervalIntegral.integral_congr fun x _ ↦ intervalIntegral.integral_congr fun g _ ↦ ?_
  ring

/-- Paper: Theorem 12.4.1.1, pp. 514–519, as used on p. 520. In the rational real-place model
at order zero, with sharp cutoffs, the diagonal integral of the dilation average composed with
the projection onto the polar-free level tends to the real-place term of (12.5.1.1) minus
`∫ φ(g) min(g^(1/2), g^(-1/2)) d×g`, when `Y * L → ∞`.
Reconstruction: the diagonal integral stands for the regularized trace on the level; the
description of the level in the file header and the identification with a trace are not
formalized.
Deviation: formulas (12.4.1.1)–(12.4.1.3) have no second term, and p. 520 subtracts
`M(φ)(|·|^(1/2)) + M(φ)(|·|^(-1/2))`; see the two theorems that follow. -/
theorem sLocalTrace_realPWLevel_diagonal_tendsto (ha : 0 < a) (hab : a ≤ b) (h1 : 1 ∉ Icc a b)
    (hφ : ContinuousOn φ (Icc a b)) (hYL : Tendsto (fun i ↦ Y i * L i) l atTop) :
    Tendsto (fun i ↦ ∫ x in (0 : ℝ)..L i, ∫ g in a..b,
        φ g * ((√g)⁻¹ * realPWLevelDiagonal (Y i) g x) / g) l
      (𝓝 ((∫ g in a..b, φ g * (1 / 2 * (√g / |1 - g| + √g / |1 + g|)) / g) -
        ∫ g in a..b, φ g * min (√g) (√g)⁻¹ / g)) := by
  rw [← integral_weight_level ha hab h1 hφ]
  refine (tendsto_integral_realPWLevelDiagonal ha hab h1 (intervalIntegrable_weight ha hab hφ)
    hYL).congr fun i ↦ ?_
  rw [← integral_integral_realPWLevelDiagonal_swap ha hab (continuousOn_weight ha hφ)]
  refine intervalIntegral.integral_congr fun x _ ↦ intervalIntegral.integral_congr fun g _ ↦ ?_
  ring

/-- Paper: Theorem 12.4.1.1, pp. 514–519. The limit on the level for a test function supported
above norm one, in the form `V_∞ - L₋` used in the comments on issue 7354:
`V_∞ = ∫ φ(g) g^(3/2) / (g² - 1) d×g` is the real-place term of (12.5.1.1) and
`L₋ = ∫ φ(g) g^(-1/2) d×g` is the Mellin transform `M(φ)(|·|^(-1/2))`.
Reconstruction: as for `sLocalTrace_realPWLevel_diagonal_tendsto`. -/
theorem sLocalTrace_realPWLevel_diagonal_tendsto_of_one_lt (ha : 1 < a) (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) (hYL : Tendsto (fun i ↦ Y i * L i) l atTop) :
    Tendsto (fun i ↦ ∫ x in (0 : ℝ)..L i, ∫ g in a..b,
        φ g * ((√g)⁻¹ * realPWLevelDiagonal (Y i) g x) / g) l
      (𝓝 ((∫ g in a..b, φ g * (g * √g / (g ^ 2 - 1)) / g) -
        ∫ g in a..b, φ g * (√g)⁻¹ / g)) := by
  have h1 : (1 : ℝ) ∉ Icc a b := fun h ↦ absurd h.1 (not_le.mpr ha)
  have h := sLocalTrace_realPWLevel_diagonal_tendsto (zero_lt_one.trans ha) hab h1 hφ hYL
  have e1 : ∫ g in a..b, φ g * (1 / 2 * (√g / |1 - g| + √g / |1 + g|)) / g =
      ∫ g in a..b, φ g * (g * √g / (g ^ 2 - 1)) / g := by
    refine intervalIntegral.integral_congr fun g hg ↦ ?_
    rw [uIcc_of_le hab] at hg
    have hg1 : 1 < g := ha.trans_le hg.1
    have h2 : g - 1 ≠ 0 := (sub_pos.mpr hg1).ne'
    have h3 : g + 1 ≠ 0 := by positivity
    have h4 : g ^ 2 - 1 ≠ 0 := by
      have : 0 < g ^ 2 - 1 := by nlinarith
      exact this.ne'
    have e : 1 / 2 * (√g / |1 - g| + √g / |1 + g|) = g * √g / (g ^ 2 - 1) := by
      rw [abs_of_neg (by linarith), abs_of_pos (by linarith), neg_sub, add_comm 1 g]
      field_simp
      ring
    simp only [e]
  have e2 : ∫ g in a..b, φ g * min (√g) (√g)⁻¹ / g = ∫ g in a..b, φ g * (√g)⁻¹ / g := by
    refine intervalIntegral.integral_congr fun g hg ↦ ?_
    rw [uIcc_of_le hab] at hg
    have hs1 : 1 ≤ √g := Real.one_le_sqrt.mpr (ha.trans_le hg.1).le
    have hle : (√g)⁻¹ ≤ √g := (inv_le_one_of_one_le₀ hs1).trans hs1
    simp only [min_eq_right hle]
  rwa [e1, e2] at h

/-- Paper: Theorem 12.4.1.1, p. 514, footnote 2, with Definition 9.3.3.1. In the model, with
the sharp spatial cutoff `1_[h, L]` and `Y * h → 0`, the diagonal integrals on the level have
the same limit as without a floor. -/
theorem sLocalTrace_realPWLevel_diagonal_floor_tendsto (ha : 0 < a) (hab : a ≤ b)
    (h1 : 1 ∉ Icc a b) (hφ : ContinuousOn φ (Icc a b)) {h : ι → ℝ}
    (hYL : Tendsto (fun i ↦ Y i * L i) l atTop) (hYh : Tendsto (fun i ↦ Y i * h i) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x in (h i)..(L i), ∫ g in a..b,
        φ g * ((√g)⁻¹ * realPWLevelDiagonal (Y i) g x) / g) l
      (𝓝 ((∫ g in a..b, φ g * (1 / 2 * (√g / |1 - g| + √g / |1 + g|)) / g) -
        ∫ g in a..b, φ g * min (√g) (√g)⁻¹ / g)) := by
  rw [← integral_weight_level ha hab h1 hφ]
  refine (tendsto_integral_realPWLevelDiagonal_floor_zero ha hab h1
    (intervalIntegrable_weight ha hab hφ) hYL hYh).congr fun i ↦ ?_
  rw [← integral_integral_realPWLevelDiagonal_swap_floor ha hab (continuousOn_weight ha hφ)]
  refine intervalIntegral.integral_congr fun x _ ↦ intervalIntegral.integral_congr fun g _ ↦ ?_
  ring

/-- Paper: Theorem 12.4.1.1, p. 514, footnote 2, with Definition 9.3.3.1. In the model, with
the sharp spatial cutoff `1_[h, L]` and `Y * h → ∞`, the diagonal integrals on the level tend
to zero, whatever the test function supported away from norm one. So a floor that is not small
against the band scale `1 / Y` loses the whole limit, the real-place term included. -/
theorem sLocalTrace_realPWLevel_diagonal_floor_tendsto_zero (ha : 0 < a) (hab : a ≤ b)
    (h1 : 1 ∉ Icc a b) (hφ : ContinuousOn φ (Icc a b)) {h : ι → ℝ}
    (hYL : Tendsto (fun i ↦ Y i * L i) l atTop) (hYh : Tendsto (fun i ↦ Y i * h i) l atTop) :
    Tendsto (fun i ↦ ∫ x in (h i)..(L i), ∫ g in a..b,
        φ g * ((√g)⁻¹ * realPWLevelDiagonal (Y i) g x) / g) l (𝓝 0) := by
  refine (tendsto_integral_realPWLevelDiagonal_floor_atTop ha hab h1
    (intervalIntegrable_weight ha hab hφ) hYL hYh).congr fun i ↦ ?_
  rw [← integral_integral_realPWLevelDiagonal_swap_floor ha hab (continuousOn_weight ha hφ)]
  refine intervalIntegral.integral_congr fun x _ ↦ intervalIntegral.integral_congr fun g _ ↦ ?_
  ring

end Paper

/-! ### Comparison with the printed formula and with page 520 -/

section Comparison

variable {a b : ℝ} {φ : ℝ → ℝ}

private theorem continuousOn_sqrt_inv (ha : 0 < a) :
    ContinuousOn (fun g : ℝ ↦ (√g)⁻¹) (Icc a b) :=
  Real.continuous_sqrt.continuousOn.inv₀ fun _ hg ↦
    (Real.sqrt_pos.mpr (ha.trans_le hg.1)).ne'

private theorem continuousOn_minIntegrand (ha : 0 < a) (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) :
    ContinuousOn (fun g : ℝ ↦ φ g * min (√g) (√g)⁻¹ / g) (uIcc a b) := by
  rw [uIcc_of_le hab]
  have hs : ContinuousOn (fun g : ℝ ↦ √g) (Icc a b) := Real.continuous_sqrt.continuousOn
  exact (hφ.mul (hs.inf (continuousOn_sqrt_inv ha))).div
    continuousOn_id fun _ hg ↦ (ha.trans_le hg.1).ne'

private theorem continuousOn_addIntegrand (ha : 0 < a) (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) :
    ContinuousOn (fun g : ℝ ↦ φ g * (√g + (√g)⁻¹) / g) (uIcc a b) := by
  rw [uIcc_of_le hab]
  have hs : ContinuousOn (fun g : ℝ ↦ √g) (Icc a b) := Real.continuous_sqrt.continuousOn
  exact (hφ.mul (hs.add (continuousOn_sqrt_inv ha))).div
    continuousOn_id fun _ hg ↦ (ha.trans_le hg.1).ne'

/-- The rank-one limit `∫ φ(g) min(g^(1/2), g^(-1/2)) d×g` is positive for a positive test. -/
theorem integral_mul_min_sqrt_pos (ha : 0 < a) (hab : a < b) (hφ : ContinuousOn φ (Icc a b))
    (hpos : ∀ g ∈ Ioo a b, 0 < φ g) :
    0 < ∫ g in a..b, φ g * min (√g) (√g)⁻¹ / g := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (continuousOn_minIntegrand ha hab.le hφ).intervalIntegrable (fun g hg ↦ ?_) hab
  have hg0 : 0 < g := ha.trans hg.1
  have hs : 0 < √g := Real.sqrt_pos.mpr hg0
  exact div_pos (mul_pos (hpos g hg) (lt_min hs (inv_pos.mpr hs))) hg0

/-- The rank-one limit is strictly smaller than `∫ φ(g) (g^(1/2) + g^(-1/2)) d×g`. -/
theorem integral_mul_min_sqrt_lt (ha : 0 < a) (hab : a < b) (hφ : ContinuousOn φ (Icc a b))
    (hpos : ∀ g ∈ Ioo a b, 0 < φ g) :
    ∫ g in a..b, φ g * min (√g) (√g)⁻¹ / g < ∫ g in a..b, φ g * (√g + (√g)⁻¹) / g := by
  have h1 := (continuousOn_minIntegrand ha hab.le hφ).intervalIntegrable (μ := volume)
  have h2 := (continuousOn_addIntegrand ha hab.le hφ).intervalIntegrable (μ := volume)
  rw [← sub_pos, ← intervalIntegral.integral_sub h2 h1]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (h2.sub h1) (fun g hg ↦ ?_) hab
  have hg0 : 0 < g := ha.trans hg.1
  have hs : 0 < √g := Real.sqrt_pos.mpr hg0
  have hlt : min (√g) (√g)⁻¹ < √g + (√g)⁻¹ :=
    (min_le_left _ _).trans_lt (lt_add_of_pos_right _ (inv_pos.mpr hs))
  have h : 0 < φ g * (√g + (√g)⁻¹) / g - φ g * min (√g) (√g)⁻¹ / g := by
    rw [← sub_div, ← mul_sub]
    exact div_pos (mul_pos (hpos g hg) (sub_pos.mpr hlt)) hg0
  exact h

variable {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot] {Y L : ι → ℝ}

/-- Paper: Theorem 12.4.1.1, pp. 514–519. In the model, for a test function that is positive on
`(a, b)`, the diagonal integrals on the level do not tend to the real-place term of (12.5.1.1)
alone, which is what formulas (12.4.1.1)–(12.4.1.3) give when read on the level. -/
theorem sLocalTrace_realPWLevel_diagonal_not_tendsto_principalValue (ha : 0 < a) (hab : a < b)
    (h1 : 1 ∉ Icc a b) (hφ : ContinuousOn φ (Icc a b)) (hpos : ∀ g ∈ Ioo a b, 0 < φ g)
    (hYL : Tendsto (fun i ↦ Y i * L i) l atTop) :
    ¬ Tendsto (fun i ↦ ∫ x in (0 : ℝ)..L i, ∫ g in a..b,
        φ g * ((√g)⁻¹ * realPWLevelDiagonal (Y i) g x) / g) l
      (𝓝 (∫ g in a..b, φ g * (1 / 2 * (√g / |1 - g| + √g / |1 + g|)) / g)) := by
  intro h
  have h' := tendsto_nhds_unique h
    (sLocalTrace_realPWLevel_diagonal_tendsto ha hab.le h1 hφ hYL)
  have hD := integral_mul_min_sqrt_pos ha hab hφ hpos
  linarith

/-- Paper: Theorem 12.5.1.1, p. 520. In the model, for a test function that is positive on
`(a, b)`, the diagonal integrals on the level do not tend to the real-place term of (12.5.1.1)
minus `M(φ)(|·|^(1/2)) + M(φ)(|·|^(-1/2)) = ∫ φ(g) (g^(1/2) + g^(-1/2)) d×g`, which is the
value that p. 520 takes from Theorem 12.4.1.1. -/
theorem sLocalTrace_realPWLevel_diagonal_not_tendsto_sub_poles (ha : 0 < a) (hab : a < b)
    (h1 : 1 ∉ Icc a b) (hφ : ContinuousOn φ (Icc a b)) (hpos : ∀ g ∈ Ioo a b, 0 < φ g)
    (hYL : Tendsto (fun i ↦ Y i * L i) l atTop) :
    ¬ Tendsto (fun i ↦ ∫ x in (0 : ℝ)..L i, ∫ g in a..b,
        φ g * ((√g)⁻¹ * realPWLevelDiagonal (Y i) g x) / g) l
      (𝓝 ((∫ g in a..b, φ g * (1 / 2 * (√g / |1 - g| + √g / |1 + g|)) / g) -
        ∫ g in a..b, φ g * (√g + (√g)⁻¹) / g)) := by
  intro h
  have h' := tendsto_nhds_unique h
    (sLocalTrace_realPWLevel_diagonal_tendsto ha hab.le h1 hφ hYL)
  have hD := integral_mul_min_sqrt_lt ha hab hφ hpos
  linarith

end Comparison

end RiemannMasullo
