module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedBandLevel
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelAverage
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! # The weighted band: the compression of the averaged dilation to the odd band

Paper: Theorem 12.4.1.1, pp. 514–519, and the value used on p. 520.

`Sec4_RealOddBandOperator` computes the Hilbert trace of `P_o ∘ M_L ∘ M_r ∘ D_g ∘ P_o` on the odd
band for one dilation `g`. In the Paley–Wiener picture of the weighted band the dilation is
`R_g = M_{r_g} ∘ D_g` (`weightedPWDilation g`). This file forms the average of these operators
against `φ(g) dg / g` and computes the trace of its compression to the odd band, as
`Sec4_RealPWLevelAverage` does for the unweighted level.

* `weightedOddDiagonal Y L g`: the diagonal integral
  `g^(-1/2) ∫ z in -L..L, r_g z * K_o (z / g, z)`, which is the trace of
  `P_o ∘ M_L ∘ R_g ∘ P_o`.
* `weightedPWDilationAverage φ a b`: the operator `A = ∫ g in a..b, (φ g / g) • R_g`, a Bochner
  integral in `L²(ℝ)` applied vector by vector, for `1 ≤ a ≤ b`.
* `isNuclearOperator_realOddBand_average_compression`: `P_o ∘ M_L ∘ A ∘ P_o` is nuclear.
* `hilbertTrace_realOddBand_average_compression`: its Hilbert trace is
  `∫ g in a..b, φ g * weightedOddDiagonal Y L g / g`.
* `continuous_weightedOddDiagonal_Ioi`: the diagonal integral is continuous in `g > 0`.

The proof goes through kernels, as in `Sec4_RealPWLevelAverage`. The kernel of
`M_L ∘ R_g ∘ P_o` is a vector of `L²` of the plane that is strongly measurable in `g` and
bounded for `g` in a bounded part of `[1, ∞)`, so its weighted integral exists. The
correspondence from kernels to operators is a continuous linear map, and the trace of a
composite of two kernel operators is a continuous linear functional of the second kernel, so
both commute with the integral.
-/

open MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate InnerProductSpace ENNReal

@[expose] public noncomputable section

namespace RiemannMasullo

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)
local notation "H₂" => Lp ℂ 2 (Measure.prod (volume : Measure ℝ) (volume : Measure ℝ))

/-- The diagonal integral of the weighted model on the odd band:
`g^(-1/2) ∫ z in -L..L, r_g z * K_o (z / g, z)`. It is the Hilbert trace of
`P_o ∘ M_L ∘ R_g ∘ P_o`. -/
def weightedOddDiagonal (Y L g : ℝ) : ℂ :=
  (((√g)⁻¹ : ℝ) : ℂ) *
    ∫ z in (-L)..L, weightedDilationMultiplier g z * (realOddBandKernel Y (z / g) z : ℂ)

/-! ### Measurability in the dilation parameter -/

/-- The multiplier `r_g x` is measurable in `g` and `x` jointly. -/
theorem measurable_weightedDilationMultiplier_uncurry :
    Measurable fun p : ℝ × ℝ ↦ weightedDilationMultiplier p.1 p.2 := by
  have h1 : Measurable fun p : ℝ × ℝ ↦ (p.1 : ℂ) := Complex.measurable_ofReal.comp measurable_fst
  have h2 : Measurable fun p : ℝ × ℝ ↦ (p.2 : ℂ) := Complex.measurable_ofReal.comp measurable_snd
  have hnum : Measurable fun p : ℝ × ℝ ↦ (p.1 : ℂ) * ((p.2 : ℂ) ^ 2 - Complex.I) :=
    h1.mul ((h2.pow_const 2).sub measurable_const)
  have hden : Measurable fun p : ℝ × ℝ ↦ (p.2 : ℂ) ^ 2 - Complex.I * (p.1 : ℂ) ^ 2 :=
    (h2.pow_const 2).sub (measurable_const.mul (h1.pow_const 2))
  exact hnum.div hden

/-- The kernel of the odd band is measurable in its two variables jointly. -/
theorem measurable_realOddBandKernel (Y : ℝ) :
    Measurable fun r : ℝ × ℝ ↦ realOddBandKernel Y r.1 r.2 := by
  have hS := (continuous_realBandKernel Y).measurable
  have hfun : (fun r : ℝ × ℝ ↦ realOddBandKernel Y r.1 r.2) = fun r ↦
      (realBandKernel Y (r.1 - r.2) - realBandKernel Y (r.1 + r.2)) / 2 := rfl
  rw [hfun]
  exact ((hS.comp (measurable_fst.sub measurable_snd)).sub
    (hS.comp (measurable_fst.add measurable_snd))).div_const 2

private theorem measurable_weightedKernel_aux1 (L : ℝ) : Measurable fun q : ℝ × (ℝ × ℝ) ↦
    (Icc (-L) L).indicator (fun _ ↦ (1 : ℂ)) q.2.1 := by
  have hi : Measurable ((Icc (-L) L).indicator (fun _ : ℝ ↦ (1 : ℂ))) :=
    measurable_const.indicator measurableSet_Icc
  exact hi.comp (measurable_fst.comp measurable_snd)

private theorem measurable_weightedKernel_aux2 :
    Measurable fun q : ℝ × (ℝ × ℝ) ↦ (q.2.1 / q.1, q.2.2) := by
  have h1 : Measurable fun q : ℝ × (ℝ × ℝ) ↦ q.2.1 := measurable_fst.comp measurable_snd
  have h2 : Measurable fun q : ℝ × (ℝ × ℝ) ↦ q.1 := measurable_fst
  have h3 : Measurable fun q : ℝ × (ℝ × ℝ) ↦ q.2.2 := measurable_snd.comp measurable_snd
  exact (h1.div h2).prodMk h3

private theorem measurable_weightedKernel_aux3 (Y : ℝ) :
    Measurable fun q : ℝ × (ℝ × ℝ) ↦ realOddBandKernel Y (q.2.1 / q.1) q.2.2 := by
  have h := (measurable_realOddBandKernel Y).comp measurable_weightedKernel_aux2
  exact h

private theorem measurable_weightedKernel_aux4 (Y : ℝ) : Measurable fun q : ℝ × (ℝ × ℝ) ↦
    (((√q.1)⁻¹ * realOddBandKernel Y (q.2.1 / q.1) q.2.2 : ℝ) : ℂ) := by
  have h5 : Measurable fun q : ℝ × (ℝ × ℝ) ↦ (√q.1)⁻¹ :=
    (Real.continuous_sqrt.measurable.comp measurable_fst).inv
  exact Complex.measurable_ofReal.comp (h5.mul (measurable_weightedKernel_aux3 Y))

private theorem measurable_weightedKernel_aux5 :
    Measurable fun q : ℝ × (ℝ × ℝ) ↦ weightedDilationMultiplier q.1 q.2.1 := by
  have h : Measurable fun q : ℝ × (ℝ × ℝ) ↦ (q.1, q.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  exact measurable_weightedDilationMultiplier_uncurry.comp h

/-- The kernel of the cutoff weighted dilation after the projection onto the odd band is
measurable in the dilation and the two variables jointly. -/
theorem measurable_weightedOddDilationKernel (Y L : ℝ) : Measurable fun q : ℝ × (ℝ × ℝ) ↦
    realOddDilationKernel Y q.1 L (weightedDilationMultiplier q.1) q.2 :=
  (measurable_weightedKernel_aux1 L).mul
    (measurable_weightedKernel_aux5.mul (measurable_weightedKernel_aux4 Y))

/-- The kernel of `M_L ∘ R_g ∘ P_o` as a vector of `L²` of the plane. It is set to zero unless
`0 ≤ Y` and `1 ≤ g`. -/
def weightedOddDilationVector (Y L g : ℝ) : H₂ :=
  if h : 0 ≤ Y ∧ 1 ≤ g then
    (memLp_realOddDilationKernel h.1 g L
      (continuous_weightedDilationMultiplier (zero_lt_one.trans_le h.2).ne').measurable
      (norm_weightedDilationMultiplier_le h.2)).toLp
      (realOddDilationKernel Y g L (weightedDilationMultiplier g))
  else 0

/-- The vector is the class of the kernel `1_[-L, L] (z) r_g (z) g^(-1/2) K_o (z / g, y)`. -/
theorem coeFn_weightedOddDilationVector {Y : ℝ} (hY : 0 ≤ Y) (L : ℝ) {g : ℝ} (hg : 1 ≤ g) :
    (weightedOddDilationVector Y L g : ℝ × ℝ → ℂ) =ᵐ[volume.prod volume]
      realOddDilationKernel Y g L (weightedDilationMultiplier g) := by
  simp only [weightedOddDilationVector, hY, hg, and_self, ↓reduceDIte]
  exact MemLp.coeFn_toLp _

/-- The inner product of a fixed vector with the kernel of `M_L ∘ R_g ∘ P_o` is measurable in
`g`. -/
theorem measurable_inner_weightedOddDilationVector {Y : ℝ} (hY : 0 ≤ Y) (L : ℝ) (h : H₂) :
    Measurable fun g : ℝ ↦ ⟪h, weightedOddDilationVector Y L g⟫_ℂ := by
  have hsm : StronglyMeasurable (fun q : ℝ × (ℝ × ℝ) ↦ conj ((h : ℝ × ℝ → ℂ) q.2) *
      realOddDilationKernel Y q.1 L (weightedDilationMultiplier q.1) q.2) :=
    ((Complex.continuous_conj.measurable.comp
      ((Lp.stronglyMeasurable h).measurable.comp measurable_snd)).mul
      (measurable_weightedOddDilationKernel Y L)).stronglyMeasurable
  have hint := (hsm.integral_prod_right' (ν := (volume : Measure ℝ).prod volume)).measurable
  have heq : (fun g : ℝ ↦ ⟪h, weightedOddDilationVector Y L g⟫_ℂ) = fun g ↦
      if 1 ≤ g then ∫ p, conj ((h : ℝ × ℝ → ℂ) p) *
        realOddDilationKernel Y g L (weightedDilationMultiplier g) p ∂(volume.prod volume)
      else 0 := by
    funext g
    split_ifs with hg
    · rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_weightedOddDilationVector hY L hg] with p hp
      rw [hp, RCLike.inner_apply]
      ring
    · simp [weightedOddDilationVector, hg]
  rw [heq]
  exact Measurable.ite measurableSet_Ici hint measurable_const

/-- The kernel of `M_L ∘ R_g ∘ P_o` is strongly measurable in `g`. -/
theorem stronglyMeasurable_weightedOddDilationVector {Y : ℝ} (hY : 0 ≤ Y) (L : ℝ) :
    StronglyMeasurable (weightedOddDilationVector Y L) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  have : SecondCountableTopology H₂ := Lp.SecondCountableTopology
  exact stronglyMeasurable_of_measurable_inner (measurable_inner_weightedOddDilationVector hY L)

/-- The inner product of a fixed vector with the weighted dilate of another, cut off to
`g ≥ 1`, is measurable in the dilation. -/
theorem measurable_inner_weightedPWDilation_Ici (h f : H) :
    Measurable fun g : ℝ ↦ ⟪h, if 1 ≤ g then weightedPWDilation g f else 0⟫_ℂ := by
  have hsm : StronglyMeasurable (fun p : ℝ × ℝ ↦ conj ((h : ℝ → ℂ) p.2) *
      (weightedDilationMultiplier p.1 p.2 *
        ((((√p.1)⁻¹ : ℝ) : ℂ) * (f : ℝ → ℂ) (p.2 / p.1)))) := by
    refine Measurable.stronglyMeasurable ?_
    have h1 : Measurable fun p : ℝ × ℝ ↦ (h : ℝ → ℂ) p.2 :=
      (Lp.stronglyMeasurable h).measurable.comp measurable_snd
    have h2 : Measurable fun p : ℝ × ℝ ↦ (f : ℝ → ℂ) (p.2 / p.1) :=
      (Lp.stronglyMeasurable f).measurable.comp (measurable_snd.div measurable_fst)
    have h3 : Measurable fun p : ℝ × ℝ ↦ (((√p.1)⁻¹ : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp measurable_fst).inv
    exact (Complex.continuous_conj.measurable.comp h1).mul
      (measurable_weightedDilationMultiplier_uncurry.mul (h3.mul h2))
  have hint := (hsm.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  have heq : (fun g : ℝ ↦ ⟪h, if 1 ≤ g then weightedPWDilation g f else 0⟫_ℂ) = fun g ↦
      if 1 ≤ g then ∫ x, conj ((h : ℝ → ℂ) x) * (weightedDilationMultiplier g x *
        ((((√g)⁻¹ : ℝ) : ℂ) * (f : ℝ → ℂ) (x / g)))
      else 0 := by
    funext g
    by_cases hg : 1 ≤ g
    · simp only [hg, ↓reduceIte]
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [coeFn_weightedPWDilation hg f,
        coeFn_realDilation (zero_lt_one.trans_le hg) f] with x e1 e2
      rw [e1, e2, RCLike.inner_apply]
      ring
    · simp only [hg, ↓reduceIte, inner_zero_right]
  rw [heq]
  exact Measurable.ite measurableSet_Ici hint measurable_const

/-- The weighted dilate of a fixed vector, cut off to `g ≥ 1`, is strongly measurable in the
dilation. -/
theorem stronglyMeasurable_weightedPWDilation_Ici (f : H) :
    StronglyMeasurable fun g : ℝ ↦ if 1 ≤ g then weightedPWDilation g f else 0 := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  have : SecondCountableTopology H := Lp.SecondCountableTopology
  exact stronglyMeasurable_of_measurable_inner fun h ↦
    measurable_inner_weightedPWDilation_Ici h f

/-- The weighted dilation by `g ≥ 1` multiplies the norm by at most `g`. -/
theorem norm_weightedPWDilation_le {g : ℝ} (hg : 1 ≤ g) (f : H) :
    ‖weightedPWDilation g f‖ ≤ g * ‖f‖ := by
  have hg0 : 0 < g := zero_lt_one.trans_le hg
  have h := norm_realMultiplier_apply_le
    (continuous_weightedDilationMultiplier hg0.ne').measurable
    (norm_weightedDilationMultiplier_le hg) (realDilation g f)
  rw [norm_realDilation hg0] at h
  exact h

/-! ### A bound for the kernels -/

/-- The kernel of the odd band is symmetric. -/
theorem realOddBandKernel_comm (Y u y : ℝ) :
    realOddBandKernel Y u y = realOddBandKernel Y y u := by
  unfold realOddBandKernel
  rw [show u - y = -(y - u) by ring, realBandKernel_neg, add_comm u y]

/-- The square integral of a row of the kernel of the odd band is its value on the diagonal. -/
theorem integral_realOddBandKernel_sq {Y : ℝ} (hY : 0 ≤ Y) (u : ℝ) :
    ∫ y, realOddBandKernel Y u y ^ 2 = realOddBandKernel Y u u := by
  rw [← integral_realOddBandKernel_mul_realOddBandKernel hY u u]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  change realOddBandKernel Y u x ^ 2 = realOddBandKernel Y x u * realOddBandKernel Y u x
  rw [realOddBandKernel_comm Y x u]
  ring

/-- The kernel of the odd band on the diagonal is nonnegative. -/
theorem realOddBandKernel_self_nonneg {Y : ℝ} (hY : 0 ≤ Y) (u : ℝ) :
    0 ≤ realOddBandKernel Y u u := by
  rw [← integral_realOddBandKernel_sq hY u]
  exact integral_nonneg fun y ↦ sq_nonneg _

/-- The kernel of the odd band on the diagonal is at most `2 Y`. -/
theorem realOddBandKernel_self_le {Y : ℝ} (hY : 0 ≤ Y) (u : ℝ) :
    realOddBandKernel Y u u ≤ 2 * Y := by
  unfold realOddBandKernel
  have h1 := abs_realBandKernel_le Y (u - u)
  have h2 := abs_realBandKernel_le Y (u + u)
  rw [abs_of_nonneg hY] at h1 h2
  have h3 := (abs_le.mp h1).2
  have h4 := (abs_le.mp h2).1
  linarith

/-- The kernel of the odd band on the dilated diagonal is continuous. -/
theorem continuous_realOddBandKernel_diag (Y g : ℝ) :
    Continuous fun z : ℝ ↦ realOddBandKernel Y (z / g) (z / g) := by
  have h := (continuous_realOddBandKernel_div Y g).comp
    (continuous_id.prodMk (continuous_id.div_const g))
  exact h

/-- The `L²` norm of the kernel of `M_L ∘ R_g ∘ P_o` is bounded by a multiple of `g`. -/
theorem norm_weightedOddDilationVector_sq_le {Y : ℝ} (hY : 0 ≤ Y) {L : ℝ} (hL : 0 ≤ L) {g : ℝ}
    (hg : 1 ≤ g) : ‖weightedOddDilationVector Y L g‖ ^ 2 ≤ g * (2 * L * (2 * Y)) := by
  have hg0 : 0 < g := zero_lt_one.trans_le hg
  have hrc := continuous_weightedDilationMultiplier hg0.ne'
  have hrb := norm_weightedDilationMultiplier_le hg
  have hco := coeFn_weightedOddDilationVector hY L hg
  have hmem := memLp_realOddDilationKernel hY g L hrc.measurable hrb
  have hnorm : ((‖weightedOddDilationVector Y L g‖ ^ 2 : ℝ) : ℂ) =
      ∫ p, ((‖realOddDilationKernel Y g L (weightedDilationMultiplier g) p‖ ^ 2 : ℝ) : ℂ)
        ∂(volume.prod volume) := by
    have h1 : ⟪weightedOddDilationVector Y L g, weightedOddDilationVector Y L g⟫_ℂ =
        ((‖weightedOddDilationVector Y L g‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [← h1, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hco] with p hp
    rw [hp, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [integral_complex_ofReal] at hnorm
  have hnorm' : ‖weightedOddDilationVector Y L g‖ ^ 2 =
      ∫ p, ‖realOddDilationKernel Y g L (weightedDilationMultiplier g) p‖ ^ 2
        ∂(volume.prod volume) := by
    exact_mod_cast hnorm
  rw [hnorm']
  have hint : Integrable (fun p : ℝ × ℝ ↦
      ‖realOddDilationKernel Y g L (weightedDilationMultiplier g) p‖ ^ 2)
      (volume.prod volume) :=
    (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
  rw [integral_prod _ hint]
  have hin : ∀ z : ℝ,
      ∫ y, ‖realOddDilationKernel Y g L (weightedDilationMultiplier g) (z, y)‖ ^ 2 =
      (Icc (-L) L).indicator (fun z ↦ ‖weightedDilationMultiplier g z‖ ^ 2 *
        (g⁻¹ * realOddBandKernel Y (z / g) (z / g))) z := by
    intro z
    by_cases hz : z ∈ Icc (-L) L
    · have hpt : ∀ y : ℝ,
          ‖realOddDilationKernel Y g L (weightedDilationMultiplier g) (z, y)‖ ^ 2 =
          ‖weightedDilationMultiplier g z‖ ^ 2 * (g⁻¹ * realOddBandKernel Y (z / g) y ^ 2) :=
        fun y ↦ by
          simp only [realOddDilationKernel, indicator_of_mem hz, one_mul, norm_mul,
            Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, inv_pow, Real.sq_sqrt hg0.le]
      simp_rw [hpt]
      rw [integral_const_mul, integral_const_mul, integral_realOddBandKernel_sq hY,
        indicator_of_mem hz]
    · simp [realOddDilationKernel, hz]
  simp_rw [hin]
  rw [integral_indicator measurableSet_Icc]
  have hmono : ∫ z in Icc (-L) L, ‖weightedDilationMultiplier g z‖ ^ 2 *
        (g⁻¹ * realOddBandKernel Y (z / g) (z / g)) ≤
      ∫ z in Icc (-L) L, g ^ 2 * (g⁻¹ * (2 * Y)) := by
    refine setIntegral_mono_on ?_ ?_ measurableSet_Icc fun z _ ↦ ?_
    · exact ((hrc.norm.pow 2).mul (continuous_const.mul
        (continuous_realOddBandKernel_diag Y g))).continuousOn.integrableOn_Icc
    · exact integrableOn_const (by simp)
    · have h1 : ‖weightedDilationMultiplier g z‖ ^ 2 ≤ g ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hrb z) 2
      have h2 : g⁻¹ * realOddBandKernel Y (z / g) (z / g) ≤ g⁻¹ * (2 * Y) :=
        mul_le_mul_of_nonneg_left (realOddBandKernel_self_le hY _) (inv_nonneg.mpr hg0.le)
      have h3 : 0 ≤ g⁻¹ * realOddBandKernel Y (z / g) (z / g) :=
        mul_nonneg (inv_nonneg.mpr hg0.le) (realOddBandKernel_self_nonneg hY _)
      exact mul_le_mul h1 h2 h3 (sq_nonneg g)
  refine hmono.trans (le_of_eq ?_)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

/-! ### The average of the weighted dilations -/

variable {Y L a b : ℝ} {φ : ℝ → ℝ}

/-- The weighted dilates of a vector, weighted by `φ(g) / g`, are interval integrable. -/
theorem intervalIntegrable_smul_weightedPWDilation (ha : 1 ≤ a) (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) (f : H) :
    IntervalIntegrable (fun g ↦ ((φ g / g : ℝ) : ℂ) • weightedPWDilation g f) volume a b := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have h := intervalIntegrable_smul_of_bounded ha0 hab hφ
    (stronglyMeasurable_weightedPWDilation_Ici f) (C := b * ‖f‖) fun g hg ↦ by
      have hg1 := ha.trans hg.1
      simp only [hg1, ↓reduceIte]
      exact (norm_weightedPWDilation_le hg1 f).trans
        (mul_le_mul_of_nonneg_right hg.2 (norm_nonneg _))
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at h ⊢
  refine h.congr_fun (fun g hg ↦ ?_) measurableSet_Icc
  have hg1 := ha.trans hg.1
  simp only [hg1, ↓reduceIte]

/-- The weighted kernels of `M_L ∘ R_g ∘ P_o` are interval integrable in `L²` of the plane. -/
theorem intervalIntegrable_smul_weightedOddDilationVector (hY : 0 ≤ Y) (hL : 0 ≤ L)
    (ha : 1 ≤ a) (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b)) :
    IntervalIntegrable (fun g ↦ ((φ g / g : ℝ) : ℂ) • weightedOddDilationVector Y L g)
      volume a b :=
  intervalIntegrable_smul_of_bounded (zero_lt_one.trans_le ha) hab hφ
    (stronglyMeasurable_weightedOddDilationVector hY L)
    (C := √(b * (2 * L * (2 * Y)))) fun g hg ↦ by
      have h := norm_weightedOddDilationVector_sq_le hY hL (ha.trans hg.1)
      have h2 : g * (2 * L * (2 * Y)) ≤ b * (2 * L * (2 * Y)) :=
        mul_le_mul_of_nonneg_right hg.2 (by positivity)
      exact (le_abs_self _).trans (Real.abs_le_sqrt (h.trans h2))

/-- The average of the weighted dilations against `φ(g) dg / g` over `[a, b]`, as an operator
on `L²(ℝ)`: `A f = ∫ g in a..b, (φ g / g) • R_g f` with `R_g = M_{r_g} ∘ D_g`. It is set to zero
unless `1 ≤ a ≤ b` and `φ` is continuous on `[a, b]`. -/
def weightedPWDilationAverage (φ : ℝ → ℝ) (a b : ℝ) : H →L[ℂ] H :=
  open Classical in
  if h : 1 ≤ a ∧ a ≤ b ∧ ContinuousOn φ (Icc a b) then
    LinearMap.mkContinuous
      { toFun := fun f ↦ ∫ g in a..b, ((φ g / g : ℝ) : ℂ) • weightedPWDilation g f
        map_add' := fun f f' ↦ by
          rw [← intervalIntegral.integral_add
            (intervalIntegrable_smul_weightedPWDilation h.1 h.2.1 h.2.2 f)
            (intervalIntegrable_smul_weightedPWDilation h.1 h.2.1 h.2.2 f')]
          refine intervalIntegral.integral_congr fun g _ ↦ ?_
          simp only [map_add, smul_add]
        map_smul' := fun c f ↦ by
          rw [RingHom.id_apply, ← intervalIntegral.integral_smul]
          refine intervalIntegral.integral_congr fun g _ ↦ ?_
          simp only [map_smul, smul_comm c] }
      (∫ g in a..b, ‖((φ g / g : ℝ) : ℂ)‖ * g)
      (fun f ↦ by
        have ha0 : 0 < a := zero_lt_one.trans_le h.1
        have hw : ContinuousOn (fun g : ℝ ↦ ‖((φ g / g : ℝ) : ℂ)‖ * g * ‖f‖) (Icc a b) :=
          (((Complex.continuous_ofReal.comp_continuousOn
            (h.2.2.div continuousOn_id fun g hg ↦ (ha0.trans_le hg.1).ne')).norm).mul
            continuousOn_id).mul continuousOn_const
        refine (intervalIntegral.norm_integral_le_integral_norm h.2.1).trans ?_
        rw [← intervalIntegral.integral_mul_const]
        refine intervalIntegral.integral_mono_on h.2.1
          (intervalIntegrable_smul_weightedPWDilation h.1 h.2.1 h.2.2 f).norm
          (hw.intervalIntegrable_of_Icc h.2.1) fun g hg ↦ ?_
        rw [norm_smul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (norm_weightedPWDilation_le (h.1.trans hg.1) f)
          (norm_nonneg _))
  else 0

/-- The averaged weighted dilation applied to a vector is the integral of its weighted
dilates. -/
theorem weightedPWDilationAverage_apply (ha : 1 ≤ a) (hab : a ≤ b)
    (hφ : ContinuousOn φ (Icc a b)) (f : H) :
    weightedPWDilationAverage φ a b f =
      ∫ g in a..b, ((φ g / g : ℝ) : ℂ) • weightedPWDilation g f := by
  simp only [weightedPWDilationAverage, ha, hab, hφ, and_self, ↓reduceDIte]
  rfl

/-- The kernel of `M_L ∘ A ∘ P_o`, as the integral of the kernels of `M_L ∘ R_g ∘ P_o`. -/
def weightedOddAverageVector (Y L : ℝ) (φ : ℝ → ℝ) (a b : ℝ) : H₂ :=
  ∫ g in a..b, ((φ g / g : ℝ) : ℂ) • weightedOddDilationVector Y L g

/-- The integral operator with the kernel of `M_L ∘ R_g ∘ P_o` is that operator. -/
theorem integralKernelOperator_weightedOddDilationVector (hY : 0 < Y) (L : ℝ) {g : ℝ}
    (hg : 1 ≤ g) :
    (integralKernelOperator volume (weightedOddDilationVector Y L g)).val =
      realCutoff L ∘L weightedPWDilation g ∘L (realOddBand Y).starProjection := by
  have hg0 : 0 < g := zero_lt_one.trans_le hg
  simp only [weightedOddDilationVector, hY.le, hg, and_self, ↓reduceDIte]
  exact integralKernelOperator_realOddDilationKernel hY hg0 L
    (continuous_weightedDilationMultiplier hg0.ne').measurable
    (norm_weightedDilationMultiplier_le hg)

/-- The integral operator with the averaged kernel is the cutoff after the averaged weighted
dilation after the projection onto the odd band. -/
theorem realKernelOperatorCLM_weightedOddAverageVector (hY : 0 < Y) (hL : 0 ≤ L) (ha : 1 ≤ a)
    (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b)) :
    realKernelOperatorCLM (weightedOddAverageVector Y L φ a b) =
      realCutoff L ∘L weightedPWDilationAverage φ a b ∘L (realOddBand Y).starProjection := by
  ext1 f
  have hint := intervalIntegrable_smul_weightedOddDilationVector hY.le hL ha hab hφ
  have h1 : realKernelOperatorCLM (weightedOddAverageVector Y L φ a b) f =
      ∫ g in a..b, ((ContinuousLinearMap.apply ℂ H f).comp realKernelOperatorCLM)
        (((φ g / g : ℝ) : ℂ) • weightedOddDilationVector Y L g) := by
    rw [ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
    rfl
  rw [h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    weightedPWDilationAverage_apply ha hab hφ,
    ← ContinuousLinearMap.intervalIntegral_comp_comm (realCutoff L)
      (intervalIntegrable_smul_weightedPWDilation ha hab hφ _)]
  refine intervalIntegral.integral_congr fun g hg ↦ ?_
  rw [uIcc_of_le hab] at hg
  have hk := integralKernelOperator_weightedOddDilationVector hY L (ha.trans hg.1)
  simp only [ContinuousLinearMap.comp_apply, map_smul, ContinuousLinearMap.apply_apply,
    realKernelOperatorCLM_apply, hk]

/-! ### The trace of the compression of the averaged weighted dilation -/

/-- The compression of the cutoff averaged weighted dilation to the odd band is the composite
of the two kernel operators, the second with the averaged kernel. -/
theorem realOddBand_average_compression_eq (hY : 0 < Y) (hL : 0 ≤ L) (ha : 1 ≤ a)
    (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b)) :
    (realOddBand Y).starProjection ∘L (realCutoff L ∘L weightedPWDilationAverage φ a b) ∘L
        (realOddBand Y).starProjection =
      (integralKernelOperator volume
        (MemLp.toLp (realOddCutKernel Y L) (memLp_realOddCutKernel hY.le L))).val.comp
      (integralKernelOperator volume (weightedOddAverageVector Y L φ a b)).val := by
  rw [integralKernelOperator_realOddCutKernel hY L, ← realKernelOperatorCLM_apply,
    realKernelOperatorCLM_weightedOddAverageVector hY hL ha hab hφ]
  ext1 f
  simp only [ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.comp_apply (realCutoff L) (realCutoff L),
    realCutoff_comp_realCutoff]

/-- The compression of the cutoff averaged weighted dilation to the odd band is nuclear. -/
theorem isNuclearOperator_realOddBand_average_compression (hY : 0 < Y) (hL : 0 ≤ L)
    (ha : 1 ≤ a) (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b)) :
    IsNuclearOperator ((realOddBand Y).starProjection ∘L
      (realCutoff L ∘L weightedPWDilationAverage φ a b) ∘L
      (realOddBand Y).starProjection) := by
  rw [realOddBand_average_compression_eq hY hL ha hab hφ]
  exact nuclear_hilbertSchmidt_comp _ _

/-- **The trace of the compression of the averaged weighted dilation to the odd band.** With
`A = ∫ φ(g) R_g dg / g`, the Hilbert trace of `P_o ∘ M_L ∘ A ∘ P_o` is the average of the
diagonal integrals `weightedOddDiagonal Y L g`, which are the traces of
`P_o ∘ M_L ∘ R_g ∘ P_o`. -/
theorem hilbertTrace_realOddBand_average_compression (hY : 0 < Y) (hL : 0 ≤ L) (ha : 1 ≤ a)
    (hab : a ≤ b) (hφ : ContinuousOn φ (Icc a b)) :
    hilbertTrace ⟨(realOddBand Y).starProjection ∘L
        (realCutoff L ∘L weightedPWDilationAverage φ a b) ∘L (realOddBand Y).starProjection,
      isNuclearOperator_realOddBand_average_compression hY hL ha hab hφ⟩ =
      ∫ g in a..b, (φ g : ℂ) * weightedOddDiagonal Y L g / (g : ℂ) := by
  have hsub : (⟨(realOddBand Y).starProjection ∘L
        (realCutoff L ∘L weightedPWDilationAverage φ a b) ∘L (realOddBand Y).starProjection,
      isNuclearOperator_realOddBand_average_compression hY hL ha hab hφ⟩ :
        nuclearEndomorphisms H) =
      ⟨(integralKernelOperator volume
        (MemLp.toLp (realOddCutKernel Y L) (memLp_realOddCutKernel hY.le L))).val.comp
      (integralKernelOperator volume (weightedOddAverageVector Y L φ a b)).val,
      nuclear_hilbertSchmidt_comp _ _⟩ :=
    Subtype.ext (realOddBand_average_compression_eq hY hL ha hab hφ)
  rw [hsub, hilbertTrace_integralKernelOperator_comp]
  obtain ⟨ℓ, hℓ⟩ := exists_kernelPairingCLM
    (MemLp.toLp (realOddCutKernel Y L) (memLp_realOddCutKernel hY.le L))
  rw [← hℓ, weightedOddAverageVector, ← ContinuousLinearMap.intervalIntegral_comp_comm ℓ
    (intervalIntegrable_smul_weightedOddDilationVector hY.le hL ha hab hφ)]
  refine intervalIntegral.integral_congr fun g hg ↦ ?_
  rw [uIcc_of_le hab] at hg
  have hg1 := ha.trans hg.1
  have hg0 : 0 < g := zero_lt_one.trans_le hg1
  have hr := (continuous_weightedDilationMultiplier hg0.ne').measurable
  have hC := norm_weightedDilationMultiplier_le hg1
  have htr : ∫ p, (MemLp.toLp (realOddCutKernel Y L) (memLp_realOddCutKernel hY.le L) :
      ℝ × ℝ → ℂ) p * (weightedOddDilationVector Y L g : ℝ × ℝ → ℂ) p.swap
        ∂(volume.prod volume) = weightedOddDiagonal Y L g := by
    have hκ : weightedOddDilationVector Y L g =
        MemLp.toLp (realOddDilationKernel Y g L (weightedDilationMultiplier g))
          (memLp_realOddDilationKernel hY.le g L hr hC) := by
      simp only [weightedOddDilationVector, hY.le, hg1, and_self, ↓reduceDIte]
    rw [hκ, ← hilbertTrace_integralKernelOperator_comp volume _ _
      (nuclear_hilbertSchmidt_comp _ _), weightedOddDiagonal,
      ← hilbertTrace_realOddBand_compression_eq hY hg0 hL hr hC]
    congr 1
    exact Subtype.ext (realOddBand_compression_eq hY hg0 L hr hC).symm
  change ℓ (((φ g / g : ℝ) : ℂ) • weightedOddDilationVector Y L g) = _
  rw [map_smul, hℓ, htr, smul_eq_mul]
  push_cast
  ring

/-! ### Continuity of the diagonal integral in the dilation -/

/-- The diagonal integral `weightedOddDiagonal Y L g` is continuous in `g > 0`. -/
theorem continuous_weightedOddDiagonal_Ioi (Y L : ℝ) :
    ContinuousOn (weightedOddDiagonal Y L) (Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hg0 : ∀ g : Ioi (0 : ℝ), (g : ℝ) ≠ 0 := fun g ↦ (g.property : (0 : ℝ) < g).ne'
  have hfst : Continuous fun p : Ioi (0 : ℝ) × ℝ ↦ ((p.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
  have hsnd : Continuous fun p : Ioi (0 : ℝ) × ℝ ↦ ((p.2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp continuous_snd
  have hmult : Continuous fun p : Ioi (0 : ℝ) × ℝ ↦ weightedDilationMultiplier p.1 p.2 := by
    unfold weightedDilationMultiplier
    exact (hfst.mul ((hsnd.pow 2).sub continuous_const)).div
      ((hsnd.pow 2).sub (continuous_const.mul (hfst.pow 2)))
      fun p ↦ weightedDilationMultiplier_den_ne_zero (hg0 p.1) p.2
  have hdiv : Continuous fun p : Ioi (0 : ℝ) × ℝ ↦ p.2 / (p.1 : ℝ) :=
    continuous_snd.div (continuous_subtype_val.comp continuous_fst) fun p ↦ hg0 p.1
  have hS := continuous_realBandKernel Y
  have hK : Continuous fun p : Ioi (0 : ℝ) × ℝ ↦
      realOddBandKernel Y (p.2 / (p.1 : ℝ)) p.2 := by
    unfold realOddBandKernel
    exact ((hS.comp (hdiv.sub continuous_snd)).sub
      (hS.comp (hdiv.add continuous_snd))).div_const 2
  have hr : Continuous (Function.uncurry fun (g : Ioi (0 : ℝ)) (z : ℝ) ↦
      weightedDilationMultiplier g z * (realOddBandKernel Y (z / g) z : ℂ)) :=
    hmult.mul (Complex.continuous_ofReal.comp hK)
  have hint := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) hr (-L) L
  have hs : Continuous fun g : Ioi (0 : ℝ) ↦ (((√(g : ℝ))⁻¹ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((Real.continuous_sqrt.comp continuous_subtype_val).inv₀
      fun g ↦ (Real.sqrt_pos.mpr g.property).ne')
  exact hs.mul hint

end RiemannMasullo
