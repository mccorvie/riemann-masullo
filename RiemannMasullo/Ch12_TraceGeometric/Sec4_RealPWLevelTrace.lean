module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelDiagonal
public import RiemannMasullo.ForMathlib.Analysis.Fourier.Parseval
public import RiemannMasullo.AppC_LCTVS.Sec3b_HilbertSchmidtProduct
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The trace of the compressed cutoff dilation on the real Paley–Wiener level

Paper: Theorem 12.4.1.1, Step III, pp. 515–517.

`Sec4_RealPWLevelDiagonal` computes the integral over the diagonal of the kernel of the cutoff
dilation composed with the projection onto the level, in the rational real-place model at order
zero. This file shows that the integral is the Hilbert trace of an actual nuclear operator on
`L²(ℝ)`: the composite of the two Hilbert–Schmidt operators with kernels

* `S (x - z) 1_[-L, L] (z)`, the band projection after the sharp spatial cutoff, and
* `1_[-L, L] (z) g^(-1/2) q (z / g, y)`, the cutoff dilation after the projection onto the
  level, where `q (u, y) = (S (u - y) + S (u + y)) / 2 - S u * S y / (2 Y)` is the kernel on
  the whole line of the projection onto the even functions of the band orthogonal to `S`.

The composite is the compression of the cutoff dilation to the level.

* `integral_realBandKernel_sub_mul_sub`: the band kernel reproduces itself,
  `∫ S (x - a) S (x - b) dx = S (a - b)`, from Parseval's identity.
* `hilbertTrace_realPWLevel_compression`: the composite is nuclear and its Hilbert trace is
  `g^(-1/2) ∫ x in 0..L, realPWLevelDiagonal Y g x`, at every finite `Y` and `L`.
* `tendsto_hilbertTrace_realPWLevel_compression`: for one dilation `g ≠ 1` the traces tend to
  `g^(-1/2) (1 / (2 |1 / g - 1|) + 1 / (2 (1 / g + 1)) - min 1 g)` as `Y * L → ∞`.
* `tendsto_integral_hilbertTrace_realPWLevel_compression`: averaged against `φ(g) d×g`, the
  traces tend to the real-place term of (12.5.1.1) minus `∫ φ(g) min(g^(1/2), g^(-1/2)) d×g`.

**Not formalized here.** That the first kernel operator is the Fourier projection onto the band
composed with the cutoff is not proved. That the second is the cutoff composed with the dilation
and the projection onto the level is proved in `Sec4_RealPWLevelOperator`, which also computes
the trace of the compression written with the projection onto the level on both sides. The
average of the operators against `φ` is not formed, only the average of their traces. The
identification of this level with the level of the paper is described in the header of
`Sec4_RealPWLevelDiagonal`.
-/

open MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate

@[expose] public noncomputable section

namespace RiemannMasullo

/-! ### The band kernel reproduces itself -/

/-- The band exponential `1_[-Y, Y] (ξ) exp (2π i a ξ)`. -/
def bandExp (Y a : ℝ) : ℝ → ℂ :=
  (Icc (-Y) Y).indicator fun ξ ↦ Complex.exp (((2 * π * a * ξ : ℝ) : ℂ) * Complex.I)

/-- The band exponential is integrable. -/
theorem integrable_bandExp (Y a : ℝ) : Integrable (bandExp Y a) := by
  unfold bandExp
  rw [integrable_indicator_iff measurableSet_Icc]
  exact Continuous.integrableOn_Icc (by fun_prop)

/-- The band exponential is square-integrable. -/
theorem memLp_bandExp (Y a : ℝ) : MemLp (bandExp Y a) 2 := by
  unfold bandExp
  rw [memLp_indicator_iff_restrict
    (measurableSet_Icc : MeasurableSet (Icc (-Y) Y)).nullMeasurableSet]
  have hc : Continuous fun ξ : ℝ ↦ Complex.exp (((2 * π * a * ξ : ℝ) : ℂ) * Complex.I) := by
    fun_prop
  exact MemLp.of_bound hc.aestronglyMeasurable 1
    (Eventually.of_forall fun ξ ↦ (Complex.norm_exp_ofReal_mul_I _).le)

/-- The integral of an odd sine over a symmetric interval vanishes. -/
theorem integral_sin_mul_symm (c Y : ℝ) : ∫ η in (-Y)..Y, sin (c * η) = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -Y) (b := Y) (fun η ↦ sin (c * η))
  simp only [neg_neg, mul_neg, sin_neg, intervalIntegral.integral_neg] at h
  linarith

/-- The band kernel is even. -/
theorem realBandKernel_neg (Y u : ℝ) : realBandKernel Y (-u) = realBandKernel Y u := by
  simp only [realBandKernel, mul_neg, sinc_neg]

/-- The integral of the band exponential is the band kernel. -/
theorem integral_bandExp {Y : ℝ} (hY : 0 ≤ Y) (c : ℝ) :
    ∫ ξ, bandExp Y c ξ = (realBandKernel Y c : ℂ) := by
  unfold bandExp
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -Y ≤ Y)]
  have hpt : ∀ ξ : ℝ, Complex.exp (((2 * π * c * ξ : ℝ) : ℂ) * Complex.I) =
      ((cos (2 * π * c * ξ) : ℝ) : ℂ) + ((sin (2 * π * c * ξ) : ℝ) : ℂ) * Complex.I := fun ξ ↦ by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  simp_rw [hpt]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
    integral_cos_eq_realBandKernel, integral_sin_mul_symm]
  · simp
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- The Fourier integral of the band exponential is a translate of the band kernel. -/
theorem fourier_bandExp {Y : ℝ} (hY : 0 ≤ Y) (a x : ℝ) :
    𝓕 (bandExp Y a) x = (realBandKernel Y (x - a) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← realBandKernel_neg, ← integral_bandExp hY]
  refine integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_)
  simp only [bandExp, smul_eq_mul]
  by_cases h : ξ ∈ Icc (-Y) Y
  · simp only [h, indicator_of_mem]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp [h]

/-- The band kernel is square-integrable. -/
theorem memLp_realBandKernel {Y : ℝ} (hY : 0 ≤ Y) :
    MemLp (fun x : ℝ ↦ (realBandKernel Y x : ℂ)) 2 := by
  have h := (memLp_two_fourier_and_eLpNorm_eq (integrable_bandExp Y 0) (memLp_bandExp Y 0)).1
  refine h.congr_norm ?_ (Eventually.of_forall fun x ↦ ?_)
  · exact (Complex.continuous_ofReal.comp (continuous_realBandKernel Y)).aestronglyMeasurable
  · rw [fourier_bandExp hY, sub_zero]

/-- **The band kernel reproduces itself**: the integral of two translates of the band kernel is
the band kernel at the difference of the translations. -/
theorem integral_realBandKernel_sub_mul_sub {Y : ℝ} (hY : 0 ≤ Y) (a b : ℝ) :
    ∫ x, realBandKernel Y (x - a) * realBandKernel Y (x - b) = realBandKernel Y (a - b) := by
  have h := integral_conj_fourier_mul_fourier (integrable_bandExp Y a) (memLp_bandExp Y a)
    (integrable_bandExp Y b) (memLp_bandExp Y b)
  have hl : ∫ x, conj (𝓕 (bandExp Y a) x) * 𝓕 (bandExp Y b) x =
      ((∫ x, realBandKernel Y (x - a) * realBandKernel Y (x - b) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [fourier_bandExp hY, Complex.conj_ofReal, Complex.ofReal_mul]
  have hr : ∫ ξ, conj (bandExp Y a ξ) * bandExp Y b ξ = (realBandKernel Y (a - b) : ℂ) := by
    rw [← realBandKernel_neg, neg_sub, ← integral_bandExp hY]
    refine integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_)
    simp only [bandExp]
    by_cases hξ : ξ ∈ Icc (-Y) Y
    · simp only [hξ, indicator_of_mem]
      rw [← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring
    · simp [hξ]
  rw [hl, hr] at h
  exact_mod_cast h

/-- The real band kernel is square-integrable. -/
theorem memLp_realBandKernel_real {Y : ℝ} (hY : 0 ≤ Y) : MemLp (realBandKernel Y) 2 := by
  have h := (memLp_realBandKernel hY).re
  simpa using h

/-- The product of two translates of the band kernel is integrable. -/
theorem integrable_realBandKernel_sub_mul_sub {Y : ℝ} (hY : 0 ≤ Y) (a b : ℝ) :
    Integrable fun x ↦ realBandKernel Y (x - a) * realBandKernel Y (x - b) := by
  have h := memLp_realBandKernel_real hY
  exact (h.comp_measurePreserving (measurePreserving_sub_right volume a)).integrable_mul
    (h.comp_measurePreserving (measurePreserving_sub_right volume b))

/-! ### The kernel of the projection onto the level -/

/-- Paper: Theorem 12.4.1.1, Step III, pp. 515–517. The kernel on the whole line of the
orthogonal projection onto the even functions of the band that are orthogonal to the band kernel
`S`: `(S (u - y) + S (u + y)) / 2 - S u * S y / (2 Y)`.
Reconstruction: the level of the rational real-place model at order zero, as described in the
header of `Sec4_RealPWLevelDiagonal`. -/
def realPWLevelKernel (Y u y : ℝ) : ℝ :=
  (realBandKernel Y (u - y) + realBandKernel Y (u + y)) / 2 -
    realBandKernel Y u * realBandKernel Y y / (2 * Y)

private theorem realPWLevelKernel_eq (Y u y : ℝ) :
    realPWLevelKernel Y u y = (realBandKernel Y (y - u) + realBandKernel Y (y - -u)) / 2 -
      realBandKernel Y u * realBandKernel Y (y - 0) / (2 * Y) := by
  rw [realPWLevelKernel, ← realBandKernel_neg Y (u - y), neg_sub, sub_neg_eq_add, add_comm y u,
    sub_zero]

/-- The band kernel reproduces the kernel of the level in its second variable. -/
theorem integral_realBandKernel_sub_mul_realPWLevelKernel {Y : ℝ} (hY : 0 ≤ Y) (z u : ℝ) :
    ∫ x, realBandKernel Y (x - z) * realPWLevelKernel Y u x = realPWLevelKernel Y u z := by
  have h1 := integrable_realBandKernel_sub_mul_sub hY z u
  have h2 := integrable_realBandKernel_sub_mul_sub hY z (-u)
  have h3 := integrable_realBandKernel_sub_mul_sub hY z 0
  have hpt : ∀ x : ℝ, realBandKernel Y (x - z) * realPWLevelKernel Y u x =
      (realBandKernel Y (x - z) * realBandKernel Y (x - u) +
        realBandKernel Y (x - z) * realBandKernel Y (x - -u)) / 2 -
      realBandKernel Y u / (2 * Y) * (realBandKernel Y (x - z) * realBandKernel Y (x - 0)) :=
    fun x ↦ by
      rw [realPWLevelKernel_eq]
      ring
  have h12 : Integrable fun x ↦ (realBandKernel Y (x - z) * realBandKernel Y (x - u) +
      realBandKernel Y (x - z) * realBandKernel Y (x - -u)) / 2 := (h1.add h2).div_const 2
  have h3' : Integrable fun x ↦ realBandKernel Y u / (2 * Y) *
      (realBandKernel Y (x - z) * realBandKernel Y (x - 0)) := h3.const_mul _
  simp_rw [hpt]
  rw [integral_sub h12 h3', integral_div, integral_add h1 h2, integral_const_mul,
    integral_realBandKernel_sub_mul_sub hY, integral_realBandKernel_sub_mul_sub hY,
    integral_realBandKernel_sub_mul_sub hY, realPWLevelKernel_eq]
  ring

/-- On the diagonal of the dilation the kernel of the level is half the level diagonal. -/
theorem realPWLevelKernel_div_self {Y : ℝ} (g z : ℝ) :
    realPWLevelKernel Y (z / g) z = realPWLevelDiagonal Y g z / 2 := by
  simp only [realPWLevelKernel, realPWLevelDiagonal, realPWBandDiagonal, realPWPolarDiagonal]
  ring

/-- The level diagonal is even in the spatial variable. -/
theorem realPWLevelDiagonal_neg (Y g x : ℝ) :
    realPWLevelDiagonal Y g (-x) = realPWLevelDiagonal Y g x := by
  simp only [realPWLevelDiagonal, realPWBandDiagonal, realPWPolarDiagonal]
  rw [show -x / g - -x = -(x / g - x) by ring, show -x / g + -x = -(x / g + x) by ring,
    show -x / g = -(x / g) by ring, realBandKernel_neg, realBandKernel_neg, realBandKernel_neg,
    realBandKernel_neg]

/-! ### The two Hilbert–Schmidt kernels -/

/-- The kernel `S (x - z) 1_[-L, L] (z)` of the band projection after the sharp spatial
cutoff. -/
def realBandCutKernel (Y L : ℝ) (p : ℝ × ℝ) : ℂ :=
  (realBandKernel Y (p.1 - p.2) : ℂ) * (Icc (-L) L).indicator (fun _ ↦ (1 : ℂ)) p.2

/-- The kernel `1_[-L, L] (z) g^(-1/2) q (z / g, y)` of the sharp spatial cutoff after the
dilation by `g` after the projection onto the level. -/
def realLevelDilationKernel (Y g L : ℝ) (p : ℝ × ℝ) : ℂ :=
  (Icc (-L) L).indicator (fun _ ↦ (1 : ℂ)) p.1 *
    (((√g)⁻¹ * realPWLevelKernel Y (p.1 / g) p.2 : ℝ) : ℂ)

private theorem volume_Icc_ne_top (L : ℝ) : volume (Icc (-L) L) ≠ ⊤ := by
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-- The first kernel is square-integrable. -/
theorem memLp_realBandCutKernel {Y : ℝ} (hY : 0 ≤ Y) (L : ℝ) :
    MemLp (realBandCutKernel Y L) 2 (volume.prod volume) :=
  memLp_convCutKernel measurableSet_Icc (volume_Icc_ne_top L) (memLp_realBandKernel hY)

private theorem memLp_cut_comp_sub {C : Set ℝ} (hC : MeasurableSet C) (hCf : volume C ≠ ⊤)
    {u : ℝ → ℂ} (huc : Continuous u) (hu : MemLp u 2) {ℓ : ℝ → ℝ} (hℓ : Continuous ℓ) :
    MemLp (fun p : ℝ × ℝ ↦ C.indicator (fun _ ↦ (1 : ℂ)) p.1 * u (ℓ p.1 - p.2)) 2
      (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ C.indicator (fun _ ↦ (1 : ℂ)) p.1 * u (ℓ p.1 - p.2))
      (volume.prod volume) :=
    (((measurable_const.indicator hC).comp measurable_fst).aestronglyMeasurable).mul
      (huc.comp ((hℓ.comp continuous_fst).sub continuous_snd)).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
  have hu2 : Integrable (fun w ↦ ‖u w‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  have hpt (p : ℝ × ℝ) : ‖C.indicator (fun _ ↦ (1 : ℂ)) p.1 * u (ℓ p.1 - p.2)‖ ^ 2 =
      C.indicator (fun _ ↦ (1 : ℝ)) p.1 * ‖u (ℓ p.1 - p.2)‖ ^ 2 := by
    by_cases h : p.1 ∈ C <;> simp [h]
  have hsq_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ C.indicator (fun _ ↦ (1 : ℝ)) p.1 * ‖u (ℓ p.1 - p.2)‖ ^ 2)
      (volume.prod volume) :=
    (hmeas.norm.pow 2).congr (Eventually.of_forall hpt)
  simp_rw [hpt]
  refine (integrable_prod_iff hsq_meas).mpr ⟨Eventually.of_forall fun x ↦ ?_, ?_⟩
  · show Integrable (fun z : ℝ ↦ C.indicator (fun _ ↦ (1 : ℝ)) x * ‖u (ℓ x - z)‖ ^ 2)
    exact (hu2.comp_sub_left (ℓ x)).const_mul (C.indicator (fun _ ↦ (1 : ℝ)) x)
  · show Integrable (fun x : ℝ ↦ ∫ z, ‖C.indicator (fun _ ↦ (1 : ℝ)) x * ‖u (ℓ x - z)‖ ^ 2‖)
    have hK (x : ℝ) : (∫ z, ‖C.indicator (fun _ ↦ (1 : ℝ)) x * ‖u (ℓ x - z)‖ ^ 2‖) =
        C.indicator (fun _ ↦ ∫ w, ‖u w‖ ^ 2) x := by
      by_cases h : x ∈ C
      · simp only [h, Set.indicator_of_mem, one_mul, norm_pow, norm_norm]
        exact integral_sub_left_eq_self (fun w ↦ ‖u w‖ ^ 2) volume (ℓ x)
      · simp [h]
    simp_rw [hK]
    exact (integrable_indicator_iff hC).mpr (integrableOn_const hCf)

private theorem memLp_cut_mul_prod (L : ℝ) {f u : ℝ → ℂ} (hf : Continuous f)
    (huc : Continuous u) (hu : MemLp u 2) :
    MemLp (fun p : ℝ × ℝ ↦ (Icc (-L) L).indicator (fun _ ↦ (1 : ℂ)) p.1 * f p.1 * u p.2) 2
      (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ (Icc (-L) L).indicator (fun _ ↦ (1 : ℂ)) p.1 * f p.1 * u p.2)
      (volume.prod volume) :=
    ((((measurable_const.indicator measurableSet_Icc).comp measurable_fst).aestronglyMeasurable).mul
      (hf.comp continuous_fst).aestronglyMeasurable).mul
      (huc.comp continuous_snd).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
  have hu2 : Integrable (fun w ↦ ‖u w‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  have hf2 : Integrable (fun x ↦ (Icc (-L) L).indicator (fun x ↦ ‖f x‖ ^ 2) x) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact Continuous.integrableOn_Icc (by fun_prop)
  refine (hf2.mul_prod hu2).congr (Eventually.of_forall fun p ↦ ?_)
  by_cases h : p.1 ∈ Icc (-L) L <;> simp [h, mul_pow]

/-- The second kernel is square-integrable. -/
theorem memLp_realLevelDilationKernel {Y : ℝ} (hY : 0 ≤ Y) (g L : ℝ) :
    MemLp (realLevelDilationKernel Y g L) 2 (volume.prod volume) := by
  have hS := memLp_realBandKernel hY
  have hSc : Continuous fun x : ℝ ↦ (realBandKernel Y x : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_realBandKernel Y)
  have h1 := memLp_cut_comp_sub measurableSet_Icc (volume_Icc_ne_top L) hSc hS
    (ℓ := fun z ↦ z / g) (by fun_prop)
  have h2 := memLp_cut_comp_sub measurableSet_Icc (volume_Icc_ne_top L) hSc hS
    (ℓ := fun z ↦ -(z / g)) (by fun_prop)
  have h3 := memLp_cut_mul_prod L (f := fun z ↦ (realBandKernel Y (z / g) : ℂ))
    (hSc.comp (by fun_prop)) hSc hS
  have h := ((h1.const_mul (((√g)⁻¹ / 2 : ℝ) : ℂ)).add
    (h2.const_mul (((√g)⁻¹ / 2 : ℝ) : ℂ))).sub (h3.const_mul (((√g)⁻¹ / (2 * Y) : ℝ) : ℂ))
  refine (memLp_congr_ae (Eventually.of_forall fun p ↦ ?_)).mp h
  simp only [Pi.add_apply, Pi.sub_apply, realLevelDilationKernel, realPWLevelKernel]
  rw [show -(p.1 / g) - p.2 = -(p.1 / g + p.2) by ring, realBandKernel_neg]
  by_cases hp : p.1 ∈ Icc (-L) L
  · simp only [hp, indicator_of_mem, one_mul]
    push_cast
    ring
  · simp [hp]

/-! ### The trace of the compression -/

private theorem integral_symm_of_even {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) (hc : Continuous f)
    (L : ℝ) : ∫ x in (-L)..L, f x = 2 * ∫ x in (0 : ℝ)..L, f x := by
  have h1 : ∫ x in (-L)..0, f x = ∫ x in (0 : ℝ)..L, f x := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := L) f
    simp only [hf, neg_zero] at h
    exact h.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-L) 0)
    (hc.intervalIntegrable 0 L), h1]
  ring

/-- The level diagonal is continuous in the spatial variable. -/
theorem continuous_realPWLevelDiagonal (Y g : ℝ) : Continuous (realPWLevelDiagonal Y g) := by
  unfold realPWLevelDiagonal
  exact (continuous_realPWBandDiagonal Y g).sub (continuous_realPWPolarDiagonal Y g)

/-- Paper: Theorem 12.4.1.1, Step III, pp. 515–517. In the rational real-place model at order
zero, the compression to the level of the sharp spatial cutoff after the dilation by `g` is
nuclear, as the composite of two Hilbert–Schmidt kernel operators on `L²(ℝ)`, and its Hilbert
trace is `g^(-1/2)` times the integral over `[0, L]` of the level diagonal. This is the
integral that `Sec4_RealPWLevelDiagonal` computes in closed form.
Reconstruction: the first factor has the kernel of the band projection after the cutoff, the
second the kernel of the cutoff after the dilation after the projection onto the level. That
the level of the paper is this one is described in the header of `Sec4_RealPWLevelDiagonal`
and is not formalized. -/
theorem hilbertTrace_realPWLevel_compression {Y : ℝ} (hY : 0 < Y) (g : ℝ) {L : ℝ}
    (hL : 0 ≤ L) :
    hilbertTrace ⟨(integralKernelOperator volume
        (MemLp.toLp (realBandCutKernel Y L) (memLp_realBandCutKernel hY.le L))).val.comp
      (integralKernelOperator volume
        (MemLp.toLp (realLevelDilationKernel Y g L)
          (memLp_realLevelDilationKernel hY.le g L))).val,
      nuclear_hilbertSchmidt_comp _ _⟩ =
      (((√g)⁻¹ * ∫ x in (0 : ℝ)..L, realPWLevelDiagonal Y g x : ℝ) : ℂ) := by
  rw [hilbertTrace_integralKernelOperator_comp]
  have ha := (memLp_realBandCutKernel hY.le L).coeFn_toLp
  have hb := (memLp_realLevelDilationKernel hY.le g L).coeFn_toLp
  have hbs := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)
    ).quasiMeasurePreserving.ae_eq_comp hb
  have heq : (fun p : ℝ × ℝ ↦
      MemLp.toLp (realBandCutKernel Y L) (memLp_realBandCutKernel hY.le L) p *
        MemLp.toLp (realLevelDilationKernel Y g L) (memLp_realLevelDilationKernel hY.le g L)
          p.swap) =ᵐ[volume.prod volume]
      fun p ↦ realBandCutKernel Y L p * realLevelDilationKernel Y g L p.swap := by
    filter_upwards [ha, hbs] with p hpa hpb
    rw [hpa]
    rw [show MemLp.toLp (realLevelDilationKernel Y g L)
      (memLp_realLevelDilationKernel hY.le g L) p.swap = _ from hpb]
    rfl
  rw [integral_congr_ae heq]
  have hint : Integrable
      (fun p : ℝ × ℝ ↦ realBandCutKernel Y L p * realLevelDilationKernel Y g L p.swap)
      (volume.prod volume) :=
    (memLp_realBandCutKernel hY.le L).integrable_mul
      ((memLp_realLevelDilationKernel hY.le g L).comp_measurePreserving
        (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)))
  rw [integral_prod_symm _ hint]
  have hin (z : ℝ) : ∫ x, realBandCutKernel Y L (x, z) *
      realLevelDilationKernel Y g L (Prod.swap (x, z)) =
      (Icc (-L) L).indicator
        (fun z ↦ (((√g)⁻¹ * (realPWLevelDiagonal Y g z / 2) : ℝ) : ℂ)) z := by
    by_cases h : z ∈ Icc (-L) L
    · simp only [realBandCutKernel, realLevelDilationKernel, Prod.swap, h, indicator_of_mem,
        mul_one, one_mul]
      have hc : ∀ x : ℝ, (realBandKernel Y (x - z) : ℂ) *
          (((√g)⁻¹ * realPWLevelKernel Y (z / g) x : ℝ) : ℂ) =
          (((√g)⁻¹ * (realBandKernel Y (x - z) * realPWLevelKernel Y (z / g) x) : ℝ) : ℂ) :=
        fun x ↦ by
          push_cast
          ring
      simp_rw [hc]
      rw [integral_complex_ofReal, integral_const_mul,
        integral_realBandKernel_sub_mul_realPWLevelKernel hY.le, realPWLevelKernel_div_self]
    · simp [realBandCutKernel, realLevelDilationKernel, h]
  simp_rw [hin]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -L ≤ L), intervalIntegral.integral_ofReal]
  congr 1
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    integral_symm_of_even (realPWLevelDiagonal_neg Y g) (continuous_realPWLevelDiagonal Y g) L]
  ring

/-! ### The limit of the traces -/

section Limit

variable {ι : Type*} {l : Filter ι} {Y L : ι → ℝ}

/-- Paper: Theorem 12.4.1.1, pp. 514–519. For one dilation `g ≠ 1`, the Hilbert traces of the
compressions of the cutoff dilation to the level tend, as `Y * L → ∞`, to `g^(-1/2)` times
`1 / (2 |1 / g - 1|) + 1 / (2 (1 / g + 1)) - min 1 g`. For `g > 1` this is
`g^(3/2) / (g² - 1) - g^(-1/2)`.
Reconstruction: as for `hilbertTrace_realPWLevel_compression`. -/
theorem tendsto_hilbertTrace_realPWLevel_compression (hY : ∀ i, 0 < Y i) (hL : ∀ i, 0 ≤ L i)
    (hYL : Tendsto (fun i ↦ Y i * L i) l atTop) {g : ℝ} (hg0 : 0 < g) (hg1 : g ≠ 1) :
    Tendsto (fun i ↦ hilbertTrace ⟨(integralKernelOperator volume
        (MemLp.toLp (realBandCutKernel (Y i) (L i))
          (memLp_realBandCutKernel (hY i).le (L i)))).val.comp
      (integralKernelOperator volume
        (MemLp.toLp (realLevelDilationKernel (Y i) g (L i))
          (memLp_realLevelDilationKernel (hY i).le g (L i)))).val,
      nuclear_hilbertSchmidt_comp _ _⟩) l
      (𝓝 (((√g)⁻¹ * ((2 * |1 / g - 1|)⁻¹ + (2 * (1 / g + 1))⁻¹ - min 1 g) : ℝ) : ℂ)) := by
  refine Tendsto.congr (fun i ↦ (hilbertTrace_realPWLevel_compression (hY i) g (hL i)).symm) ?_
  refine (Complex.continuous_ofReal.tendsto _).comp ?_
  have h := ((tendsto_realPWBandDiagonalMass hYL hg0 hg1).sub
    (tendsto_realPWPolarDiagonalMass hYL hg0)).const_mul ((√g)⁻¹)
  refine h.congr' ?_
  filter_upwards [hYL.eventually_gt_atTop 0] with i hi
  rw [integral_realPWLevelDiagonal hg0 hg1 (hY i).ne' (right_ne_zero_of_mul hi.ne')]

variable [l.IsCountablyGenerated] {a b : ℝ} {φ : ℝ → ℝ}

/-- Paper: Theorem 12.4.1.1, pp. 514–519, as used on p. 520. The average against `φ(g) d×g` of
the Hilbert traces of the compressions tends, as `Y * L → ∞`, to the real-place term of
(12.5.1.1) minus `∫ φ(g) min(g^(1/2), g^(-1/2)) d×g`.
Reconstruction: the average of the traces stands for the trace of the averaged operator; the
average of the operators is not formed here. -/
theorem tendsto_integral_hilbertTrace_realPWLevel_compression (ha : 0 < a) (hab : a ≤ b)
    (h1 : 1 ∉ Icc a b) (hφ : ContinuousOn φ (Icc a b)) (hY : ∀ i, 0 < Y i)
    (hL : ∀ i, 0 ≤ L i) (hYL : Tendsto (fun i ↦ Y i * L i) l atTop) :
    Tendsto (fun i ↦ ∫ g in a..b, (φ g : ℂ) * hilbertTrace ⟨(integralKernelOperator volume
        (MemLp.toLp (realBandCutKernel (Y i) (L i))
          (memLp_realBandCutKernel (hY i).le (L i)))).val.comp
      (integralKernelOperator volume
        (MemLp.toLp (realLevelDilationKernel (Y i) g (L i))
          (memLp_realLevelDilationKernel (hY i).le g (L i)))).val,
      nuclear_hilbertSchmidt_comp _ _⟩ / (g : ℂ)) l
      (𝓝 (((∫ g in a..b, φ g * (1 / 2 * (√g / |1 - g| + √g / |1 + g|)) / g) -
        ∫ g in a..b, φ g * min (√g) (√g)⁻¹ / g : ℝ) : ℂ)) := by
  have hw : ContinuousOn (fun g : ℝ ↦ φ g * (√g * g)⁻¹) (Icc a b) :=
    hφ.mul ((Real.continuous_sqrt.continuousOn.mul continuousOn_id).inv₀ fun _ hg ↦
      mul_ne_zero (Real.sqrt_pos.mpr (ha.trans_le hg.1)).ne' (ha.trans_le hg.1).ne')
  have hreal := sLocalTrace_realPWLevel_diagonal_tendsto ha hab h1 hφ hYL
  refine ((Complex.continuous_ofReal.tendsto _).comp hreal).congr fun i ↦ ?_
  simp only [Function.comp_apply]
  have hpt : ∀ g : ℝ, (φ g : ℂ) * hilbertTrace ⟨(integralKernelOperator volume
        (MemLp.toLp (realBandCutKernel (Y i) (L i))
          (memLp_realBandCutKernel (hY i).le (L i)))).val.comp
      (integralKernelOperator volume
        (MemLp.toLp (realLevelDilationKernel (Y i) g (L i))
          (memLp_realLevelDilationKernel (hY i).le g (L i)))).val,
      nuclear_hilbertSchmidt_comp _ _⟩ / (g : ℂ) =
      ((φ g * (√g * g)⁻¹ * ∫ x in (0 : ℝ)..L i, realPWLevelDiagonal (Y i) g x : ℝ) : ℂ) :=
    fun g ↦ by
      rw [hilbertTrace_realPWLevel_compression (hY i) g (hL i)]
      push_cast
      ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_ofReal,
    ← integral_integral_realPWLevelDiagonal_swap ha hab hw]
  congr 1
  refine intervalIntegral.integral_congr fun x _ ↦ intervalIntegral.integral_congr fun g _ ↦ ?_
  ring

end Limit

end RiemannMasullo
