module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedPolarVector
public import RiemannMasullo.ForMathlib.Analysis.Fourier.L2ConvolutionPhase
import Mathlib.MeasureTheory.Function.Holder
import RiemannMasullo.Ch12_TraceGeometric.Sec4_CenteredSpatialCutoff
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.Ring

/-! # Removing the spatial cutoff from the reflected polar pairing -/

public noncomputable section

open Filter Function MeasureTheory Set
open scoped Convolution ENNReal FourierTransform InnerProductSpace Topology

namespace RiemannMasullo

local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "fourierL2" => Lp.fourierTransformₗᵢ ℝ ℂ
local notation "cmul" => ContinuousLinearMap.mul ℂ ℂ
local notation "e(" a ")" =>
  Set.indicator (Ici a) (fun y : ℝ ↦ Real.exp ((a - y) / 2))

private theorem integrable_normalizedHalflineExponential (a : ℝ) :
    Integrable (fun x ↦ (e(a) x : ℂ)) := by
  have h : IntegrableOn (fun y : ℝ ↦ Real.exp ((-(1 / 2 : ℝ)) * y)) (Ioi a) :=
    integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) a
  have h' : IntegrableOn (fun y : ℝ ↦ Real.exp ((a - y) / 2)) (Ioi a) := by
    have hh (y : ℝ) : Real.exp ((a - y) / 2) =
        Real.exp (a / 2) * Real.exp ((-(1 / 2 : ℝ)) * y) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp_rw [hh]
    exact h.const_mul _
  exact ((integrable_indicator_iff measurableSet_Ici).2
    ((integrableOn_Ici_iff_integrableOn_Ioi).2 h')).ofReal

private theorem norm_normalizedHalflineExponential_le_one (a x : ℝ) :
    ‖(e(a) x : ℂ)‖ ≤ 1 := by
  by_cases hx : x ∈ Ici a
  · rw [indicator_of_mem hx, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (by norm_num))
  · simp [indicator_of_notMem hx]

/-- The phase-free polar convolution pairing is independent of the position
of the half-line, and has the exponential autocorrelation value. -/
theorem exists_reflectedPolarConvolution_pairing
    (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2) (m : ℝ → ℂ)
    (hU : ∀ v, (fourierL2 (U v) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦
      star (m ξ) * (fourierL2 v : FlatL2) ξ)
    (hm : ∀ᵐ ξ ∂volume, ‖m ξ‖ = 1)
    {k q : ℝ → ℂ} (hk : Integrable k) (hq : Integrable q)
    (hphase : ∀ᵐ ξ ∂volume, 𝓕 q ξ = m ξ * 𝓕 k ξ) (a : ℝ) :
    ∃ v : FlatL2, (v : ℝ → ℂ) =ᵐ[volume] (q ⋆[cmul] fun x ↦ (e(a) x : ℂ)) ∧
      ⟪U.symm (normalizedHalflineExponentialL2 a), v⟫_ℂ =
        ∫ t, k t * (Real.exp (-|t| / 2) : ℂ) := by
  obtain ⟨v, w, hEq, hv, hw⟩ := exists_L2_convolution_phase_transfer U m hU hm hk hq
    (integrable_normalizedHalflineExponential a) (norm_normalizedHalflineExponential_le_one a) hphase
  refine ⟨v, hv, ?_⟩
  calc
    _ = ⟪normalizedHalflineExponentialL2 a, w⟫_ℂ := by
      rw [← U.inner_map_map, U.apply_symm_apply, hEq]
    _ = ∫ x, (e(a) x : ℂ) * (∫ t, k t * (e(a) (x - t) : ℂ)) := by
      rw [(normalizedHalflineExponentialL2_inner_spec a w).2]
      apply integral_congr_ae
      filter_upwards [hw] with x hx
      rw [hx]
      rfl
    _ = _ := integral_normalizedHalflineExponential_convolution_pairing a k hk

private theorem reflectedExponentialConvolution_eq_setIntegral (q : ℝ → ℂ) (a x : ℝ) :
    (q ⋆[cmul] fun y ↦ (e(a) y : ℂ)) x =
      ∫ y in Ici a, q (x - y) * (Real.exp ((a - y) / 2) : ℂ) := by
  rw [convolution_mul_swap, ← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  refine ae_of_all _ fun y ↦ ?_
  by_cases hy : y ∈ Ici a
  · simp only [indicator_of_mem hy]
  · simp only [indicator_of_notMem hy, Complex.ofReal_zero, mul_zero]

private theorem reflectedExponentialConvolution_center (q : ℝ → ℂ) (a z : ℝ) :
    (q ⋆[cmul] fun y ↦ (e(a) y : ℂ)) (z + a) =
      (q ⋆[cmul] fun y ↦ (e(0) y : ℂ)) z := by
  have hE (x : ℝ) : e(a) (x + a) = e(0) x := by
    have hm : x + a ∈ Ici a ↔ x ∈ Ici (0 : ℝ) := by
      simpa only [mem_Ici, zero_add] using
        (add_le_add_iff_right a : 0 + a ≤ x + a ↔ 0 ≤ x)
    by_cases hx : x ∈ Ici (0 : ℝ)
    · simp only [indicator_of_mem (hm.mpr hx), indicator_of_mem hx]
      congr 1
      ring
    · simp only [indicator_of_notMem (mt hm.mp hx), indicator_of_notMem hx]
  simp only [MeasureTheory.convolution_def]
  apply integral_congr_ae
  refine ae_of_all _ fun t ↦ ?_
  change q t * (e(a) (z + a - t) : ℂ) = q t * (e(0) (z - t) : ℂ)
  rw [show z + a - t = z - t + a by ring, hE]

private theorem flatL2_norm_sq (v : FlatL2) : ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 := by
  rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ, L2.inner_def]
  simp_rw [inner_self_eq_norm_sq_to_K]
  norm_cast

private theorem exists_realSpatialMask (ρ : ℝ → ℝ) (hm : Measurable ρ)
    (hb : ∀ x, |ρ x| ≤ 1) :
    ∃ M : FlatL2 →L[ℂ] FlatL2,
      ∀ v, (M v : ℝ → ℂ) =ᵐ[volume] fun x ↦ (ρ x : ℂ) * v x := by
  let s (x : ℝ) : ℂ := ρ x
  have hs : MemLp s ∞ (volume : Measure ℝ) := memLp_top_of_bound
    (Complex.measurable_ofReal.comp hm).aestronglyMeasurable 1
    (ae_of_all _ fun x ↦ by simpa only [s, Complex.norm_real, Real.norm_eq_abs] using hb x)
  refine ⟨(cmul).holderL volume ∞ 2 2 (hs.toLp s), fun v ↦ ?_⟩
  exact ((cmul).coeFn_holder (r := 2) (hs.toLp s) v).trans
    (hs.coeFn_toLp.mono fun x hx ↦ congrArg (· * v x) hx)

private theorem norm_sq_masked_reflectedExponential_error
    (q : ℝ → ℂ) (a : ℝ) (ρ : ℝ → ℝ)
    (M : FlatL2 →L[ℂ] FlatL2) (v : FlatL2)
    (hM : (M v : ℝ → ℂ) =ᵐ[volume] fun x ↦ (ρ x : ℂ) * v x)
    (hv : (v : ℝ → ℂ) =ᵐ[volume] (q ⋆[cmul] fun y ↦ (e(a) y : ℂ))) :
    ‖M v - v‖ ^ 2 =
      ∫ z, (ρ (z + a) - 1) ^ 2 * ‖(q ⋆[cmul] fun y ↦ (e(0) y : ℂ)) z‖ ^ 2 := by
  let g := q ⋆[cmul] fun y ↦ (e(a) y : ℂ)
  calc
    ‖M v - v‖ ^ 2 = ∫ x, (ρ x - 1) ^ 2 * ‖g x‖ ^ 2 := by
      rw [flatL2_norm_sq]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (M v) v, hM, hv]
        with x hsub hmask hx
      change (M v - v) x = M v x - v x at hsub
      change M v x = (ρ x : ℂ) * v x at hmask
      change v x = g x at hx
      rw [hsub, hmask, hx]
      calc
        ‖(ρ x : ℂ) * g x - g x‖ ^ 2 = ‖((ρ x - 1 : ℝ) : ℂ) * g x‖ ^ 2 := by
          rw [Complex.ofReal_sub, Complex.ofReal_one, sub_mul, one_mul]
        _ = _ := by rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = ∫ z, (ρ (z + a) - 1) ^ 2 * ‖g (z + a)‖ ^ 2 :=
      (integral_add_right_eq_self (μ := volume) (fun x : ℝ ↦ (ρ x - 1) ^ 2 * ‖g x‖ ^ 2) a).symm
    _ = _ := by simp_rw [g, reflectedExponentialConvolution_center]

/-- The cutoff correction tends to the unmasked exponential pairing whenever
the masks eventually equal one at each fixed coordinate after centering.
The proof estimates the missed convolution row in L². -/
theorem tendsto_reflectedPolarConvolution_pairing
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2) (m : ℝ → ℂ)
    (hU : ∀ v, (fourierL2 (U v) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦
      star (m ξ) * (fourierL2 v : FlatL2) ξ)
    (hm : ∀ᵐ ξ ∂volume, ‖m ξ‖ = 1)
    {k q : ℝ → ℂ} (hk : Integrable k) (hq : Integrable q)
    (hphase : ∀ᵐ ξ ∂volume, 𝓕 q ξ = m ξ * 𝓕 k ξ)
    (a : ι → ℝ) (ρ : ι → ℝ → ℝ) (hρm : ∀ i, Measurable (ρ i))
    (hρ : ∀ i x, |ρ i x| ≤ 1) (hOne : ∀ z, ∀ᶠ i in l, ρ i (z + a i) = 1) :
    Tendsto (fun i ↦ ∫ x, (starRingEnd ℂ) (U.symm (normalizedHalflineExponentialL2 (a i)) x) *
        ((ρ i x : ℂ) * ∫ y in Ici (a i), q (x - y) * (Real.exp ((a i - y) / 2) : ℂ)))
      l (𝓝 (∫ t, k t * (Real.exp (-|t| / 2) : ℂ))) := by
  let g₀ := q ⋆[cmul] fun y ↦ (e(0) y : ℂ)
  have hg₀ : MemLp g₀ 2 volume := memLp_mul_convolution_two_of_integrable_of_bound hq
    (integrable_normalizedHalflineExponential 0) (norm_normalizedHalflineExponential_le_one 0)
  have hSq := tendsto_integral_sq_sub_mask_of_eventually_one (l := l)
    (fun i z ↦ ρ i (z + a i))
    (.of_forall fun i ↦ ((hρm i).comp (measurable_id.add measurable_const)).aestronglyMeasurable)
    (.of_forall fun i ↦ ae_of_all _ fun z ↦ hρ i (z + a i)) (ae_of_all _ hOne)
    (fun z ↦ ‖g₀ z‖ ^ 2) ((memLp_two_iff_integrable_sq_norm hg₀.aestronglyMeasurable).mp hg₀)
  have hSqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hSq
  rw [Real.sqrt_zero] at hSqrt
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) (.of_forall fun i ↦ ?_) hSqrt
  obtain ⟨v, hv, hPair⟩ := exists_reflectedPolarConvolution_pairing
    U m hU hm hk hq hphase (a i)
  obtain ⟨M, hM⟩ := exists_realSpatialMask (ρ i) (hρm i) (hρ i)
  let w := U.symm (normalizedHalflineExponentialL2 (a i))
  have hMasked : (∫ x, (starRingEnd ℂ) (w x) *
      ((ρ i x : ℂ) * ∫ y in Ici (a i), q (x - y) * (Real.exp ((a i - y) / 2) : ℂ))) =
      ⟪w, M v⟫_ℂ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hM v, hv] with x hmrow hvrow
    change M v x = (ρ i x : ℂ) * v x at hmrow
    rw [RCLike.inner_apply', hmrow, hvrow, reflectedExponentialConvolution_eq_setIntegral]
  change ‖(∫ x, (starRingEnd ℂ) (w x) *
    ((ρ i x : ℂ) * ∫ y in Ici (a i), q (x - y) * (Real.exp ((a i - y) / 2) : ℂ))) -
    (∫ t, k t * (Real.exp (-|t| / 2) : ℂ))‖ ≤ _
  rw [hMasked, ← hPair, ← inner_sub_right]
  have hNorm : ‖w‖ = 1 := (U.symm.norm_map _).trans (norm_normalizedHalflineExponentialL2 (a i))
  have hErr := norm_sq_masked_reflectedExponential_error q (a i) (ρ i) M v (hM v) hv
  calc
    _ ≤ ‖w‖ * ‖M v - v‖ := norm_inner_le_norm _ _
    _ = ‖M v - v‖ := by rw [hNorm, one_mul]
    _ = _ := by
      change ‖M v - v‖ = Real.sqrt (∫ z, (ρ i (z + a i) - 1) ^ 2 *
        ‖(q ⋆[cmul] fun y ↦ (e(0) y : ℂ)) z‖ ^ 2)
      rw [← hErr]
      exact (Real.sqrt_sq (norm_nonneg _)).symm

end RiemannMasullo
