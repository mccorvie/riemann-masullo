module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelTrace
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelClosure
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Group.Integral

/-! # The compression of the cutoff dilation to the real Paley–Wiener level, as an operator

Paper: Theorem 12.4.1.1, Step III, pp. 515–517.

`Sec4_RealPWLevelClosure` shows that the level of the rational real-place model at order zero,
the closure of the polar-free core, is `realPWLevel Y`: the even functions of `L²(ℝ)` with
Fourier transform supported in `[-Y, Y]` and of integral zero over the band.
`Sec4_RealPWLevelTrace` computes the Hilbert trace of a composite of two integral operators
whose kernels are written with `q (u, y) = (S (u - y) + S (u + y)) / 2 - S u * S y / (2 Y)`.
This file joins the two. The orthogonal projection onto the level, the sharp spatial cutoff and
the dilation are built as operators on `L²(ℝ)`, the kernel operators are identified with their
composites, and the trace is computed for the literal composite.

* `starProjection_realPWLevel_ae`: the orthogonal projection `P` onto `realPWLevel Y` is the
  integral operator with kernel `q`. The proof is by reproducing vectors: the class of
  `y ↦ q (x, y)` lies in the level, and its inner product with a vector `F` of the level is
  `F x` for almost every `x`.
* `realCutoff L` and `realDilation g`: multiplication by `1_[-L, L]`, and the unitary dilation
  `D_g f (x) = g^(-1/2) f (x / g)`, as continuous linear maps.
* `integralKernelOperator_realLevelCutKernel`: the integral operator with kernel
  `q (x, z) 1_[-L, L] (z)` is `P ∘ M_L`.
* `integralKernelOperator_realLevelDilationKernel`: the integral operator with kernel
  `1_[-L, L] (z) g^(-1/2) q (z / g, y)` is `M_L ∘ D_g ∘ P`.
* `hilbertTrace_realPWLevel_compression_eq`: the compression `P ∘ M_L ∘ D_g ∘ P` of the cutoff
  dilation to the level is nuclear, and its Hilbert trace is
  `g^(-1/2) ∫ x in 0..L, realPWLevelDiagonal Y g x`, at every finite `Y` and `L`.
* `tendsto_hilbertTrace_realPWLevel_compression_eq`: for one dilation `g ≠ 1` the traces tend
  to `g^(-1/2) (1 / (2 |1 / g - 1|) + 1 / (2 (1 / g + 1)) - min 1 g)` as `Y * L → ∞`.
* `tendsto_integral_realPWLevelCompressionTrace`: averaged against `φ(g) d×g`, the traces tend
  to the real-place term of (12.5.1.1) minus `∫ φ(g) min(g^(1/2), g^(-1/2)) d×g`.

The identification of `realPWLevel Y` with the level `sLocalInvariantPWSobolev` of the project
over `ℚ` with no finite place is proved in `Sec4_RealPWLevelBridge`.

**Not formalized.** The average of the operators against `φ` is not formed, only the average of
their traces.
-/

open MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate InnerProductSpace SchwartzMap ContDiff ENNReal

@[expose] public noncomputable section

namespace RiemannMasullo

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

/-! ### The Fourier transform on `L²(ℝ)` and the reflection -/

/-- On `L²(ℝ)` the inverse Fourier transform is the Fourier transform followed by the
reflection. -/
theorem lp_fourierInv_eq_realReflection_fourier (G : H) :
    (𝓕⁻ G : H) = realReflection (𝓕 G : H) := by
  have hc1 : Continuous fun G : H ↦ (𝓕⁻ G : H) :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).symm.continuous
  have hc2 : Continuous fun G : H ↦ realReflection (𝓕 G : H) :=
    realReflection.continuous.comp (Lp.fourierTransformₗᵢ ℝ ℂ).continuous
  refine DenseRange.induction_on (p := fun G : H ↦ (𝓕⁻ G : H) = realReflection (𝓕 G : H))
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) G (isClosed_eq hc1 hc2)
    fun g ↦ ?_
  change (𝓕⁻ (g.toLp 2 volume) : H) = realReflection (𝓕 (g.toLp 2 volume) : H)
  rw [SchwartzMap.toLp_fourierInv_eq, SchwartzMap.toLp_fourier_eq]
  refine Lp.ext ?_
  have h1 := (𝓕⁻ g).coeFn_toLp 2 (μ := volume)
  have h2 := Lp.coeFn_compMeasurePreserving ((𝓕 g).toLp 2 volume)
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  have h3 := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
    ((𝓕 g).coeFn_toLp 2 (μ := volume))
  filter_upwards [h1, h2, h3] with x e1 e2 e3
  rw [e1]
  refine Eq.trans ?_ e2.symm
  refine Eq.trans ?_ e3.symm
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, SchwartzMap.fourier_coe]
  rfl

/-- The reflection is an involution. -/
theorem realReflection_realReflection (G : H) : realReflection (realReflection G) = G := by
  refine Lp.ext ?_
  have h1 := Lp.coeFn_compMeasurePreserving (realReflection G)
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  have h2 := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving G (Measure.measurePreserving_neg (volume : Measure ℝ)))
  filter_upwards [h1, h2] with x e1 e2
  refine e1.trans (e2.trans ?_)
  simp [Function.comp]

/-- On `L²(ℝ)` the square of the Fourier transform is the reflection. -/
theorem lp_fourier_fourier (G : H) : (𝓕 (𝓕 G : H) : H) = realReflection G := by
  have h := lp_fourierInv_eq_realReflection_fourier (𝓕 G : H)
  have h0 : (𝓕⁻ (𝓕 G : H) : H) = G := by simp
  rw [h0] at h
  have h' := congrArg realReflection h
  rw [realReflection_realReflection] at h'
  exact h'.symm

/-- The inverse Fourier transform on `L²` of an integrable square-integrable function is the
reflected Fourier integral, almost everywhere. -/
theorem fourierInv_toLp_ae {h : ℝ → ℂ} (h₁ : Integrable h) (h₂ : MemLp h 2) :
    ((𝓕⁻ (h₂.toLp h) : H) : ℝ → ℂ) =ᵐ[volume] fun x ↦ 𝓕 h (-x) := by
  rw [lp_fourierInv_eq_realReflection_fourier]
  have h1 := Lp.coeFn_compMeasurePreserving (𝓕 (h₂.toLp h) : H)
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  have h2 := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
    (fourier_ae_eq_fourier_toLp h₁ h₂)
  filter_upwards [h1, h2] with x e1 e2
  exact e1.trans e2.symm

/-! ### The reproducing vectors -/

/-- The translate `y ↦ S (y - a)` of the band kernel as a vector of `L²`, defined as the Fourier
transform of the class of the band exponential. -/
def realBandVector (Y a : ℝ) : H :=
  𝓕 ((memLp_bandExp Y a).toLp (bandExp Y a))

/-- The translate of the band kernel as a vector is the class of `y ↦ S (y - a)`. -/
theorem coeFn_realBandVector {Y : ℝ} (hY : 0 ≤ Y) (a : ℝ) :
    (realBandVector Y a : ℝ → ℂ) =ᵐ[volume] fun y ↦ (realBandKernel Y (y - a) : ℂ) := by
  have h := fourier_ae_eq_fourier_toLp (integrable_bandExp Y a) (memLp_bandExp Y a)
  filter_upwards [h] with y hy
  rw [← fourier_bandExp hY, hy]
  rfl

/-- Reflecting the frequency of a band exponential reflects its phase. -/
theorem bandExp_neg (Y a ξ : ℝ) : bandExp Y a (-ξ) = bandExp Y (-a) ξ := by
  have hmem : (-ξ ∈ Icc (-Y) Y) ↔ (ξ ∈ Icc (-Y) Y) := by
    constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩
  simp only [bandExp]
  by_cases h : ξ ∈ Icc (-Y) Y
  · rw [indicator_of_mem (hmem.mpr h), indicator_of_mem h]
    congr 2
    push_cast
    ring
  · rw [indicator_of_notMem (mt hmem.mp h), indicator_of_notMem h]

/-- The Fourier transform of a translate of the band kernel is a band exponential. -/
theorem fourier_realBandVector (Y a : ℝ) :
    (𝓕 (realBandVector Y a) : H) = (memLp_bandExp Y (-a)).toLp (bandExp Y (-a)) := by
  rw [realBandVector, lp_fourier_fourier]
  refine Lp.ext ?_
  have h1 := Lp.coeFn_compMeasurePreserving ((memLp_bandExp Y a).toLp (bandExp Y a))
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  have h2 := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae_eq_comp
    (memLp_bandExp Y a).coeFn_toLp
  have h3 := (memLp_bandExp Y (-a)).coeFn_toLp
  filter_upwards [h1, h2, h3] with ξ e1 e2 e3
  rw [e3]
  refine e1.trans (e2.trans ?_)
  exact bandExp_neg Y a ξ

/-- The reproducing vector of the level at `x`: the class of `y ↦ q (x, y)`. -/
def realPWLevelVector (Y x : ℝ) : H :=
  (1 / 2 : ℂ) • (realBandVector Y x + realBandVector Y (-x)) -
    ((realBandKernel Y x / (2 * Y) : ℝ) : ℂ) • realBandVector Y 0

/-- The reproducing vector at `x` is the class of `y ↦ q (x, y)`. -/
theorem coeFn_realPWLevelVector {Y : ℝ} (hY : 0 ≤ Y) (x : ℝ) :
    (realPWLevelVector Y x : ℝ → ℂ) =ᵐ[volume] fun y ↦ (realPWLevelKernel Y x y : ℂ) := by
  have h1 := coeFn_realBandVector hY x
  have h2 := coeFn_realBandVector hY (-x)
  have h3 := coeFn_realBandVector hY 0
  have hsub := Lp.coeFn_sub ((1 / 2 : ℂ) • (realBandVector Y x + realBandVector Y (-x)))
    (((realBandKernel Y x / (2 * Y) : ℝ) : ℂ) • realBandVector Y 0)
  have hs1 := Lp.coeFn_smul (1 / 2 : ℂ) (realBandVector Y x + realBandVector Y (-x))
  have hs2 := Lp.coeFn_smul ((realBandKernel Y x / (2 * Y) : ℝ) : ℂ) (realBandVector Y 0)
  have hadd := Lp.coeFn_add (realBandVector Y x) (realBandVector Y (-x))
  filter_upwards [h1, h2, h3, hsub, hs1, hs2, hadd] with y e1 e2 e3 e4 e5 e6 e7
  rw [realPWLevelVector, e4, Pi.sub_apply, e5, e6, Pi.smul_apply, Pi.smul_apply, e7, Pi.add_apply,
    e1, e2, e3, realPWLevelKernel, ← realBandKernel_neg Y (y - x), neg_sub, sub_neg_eq_add,
    add_comm y x, sub_zero]
  simp only [smul_eq_mul]
  push_cast
  ring

/-- The Fourier transform of the reproducing vector. -/
theorem fourier_realPWLevelVector (Y x : ℝ) :
    (𝓕 (realPWLevelVector Y x) : H) =
      (1 / 2 : ℂ) • ((memLp_bandExp Y (-x)).toLp (bandExp Y (-x)) +
        (memLp_bandExp Y x).toLp (bandExp Y x)) -
      ((realBandKernel Y x / (2 * Y) : ℝ) : ℂ) • (memLp_bandExp Y 0).toLp (bandExp Y 0) := by
  have hlin : ∀ (c d : ℂ) (u v w : H), (𝓕 (c • (u + v) - d • w) : H) =
      c • ((𝓕 u : H) + (𝓕 v : H)) - d • (𝓕 w : H) := fun c d u v w ↦ by
    change Lp.fourierTransformₗᵢ ℝ ℂ (c • (u + v) - d • w) = _
    rw [map_sub, map_smul, map_add, map_smul]
    rfl
  rw [realPWLevelVector, hlin, fourier_realBandVector, fourier_realBandVector,
    fourier_realBandVector]
  simp only [neg_neg, neg_zero]

private theorem coeFn_fourier_realPWLevelVector (Y x : ℝ) :
    ((𝓕 (realPWLevelVector Y x) : H) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦
      (1 / 2 : ℂ) * (bandExp Y (-x) ξ + bandExp Y x ξ) -
        ((realBandKernel Y x / (2 * Y) : ℝ) : ℂ) * bandExp Y 0 ξ := by
  rw [fourier_realPWLevelVector]
  have hsub := Lp.coeFn_sub ((1 / 2 : ℂ) • ((memLp_bandExp Y (-x)).toLp (bandExp Y (-x)) +
      (memLp_bandExp Y x).toLp (bandExp Y x)))
    (((realBandKernel Y x / (2 * Y) : ℝ) : ℂ) • (memLp_bandExp Y 0).toLp (bandExp Y 0))
  have hs1 := Lp.coeFn_smul (1 / 2 : ℂ) ((memLp_bandExp Y (-x)).toLp (bandExp Y (-x)) +
      (memLp_bandExp Y x).toLp (bandExp Y x))
  have hs2 := Lp.coeFn_smul ((realBandKernel Y x / (2 * Y) : ℝ) : ℂ)
    ((memLp_bandExp Y 0).toLp (bandExp Y 0))
  have hadd := Lp.coeFn_add ((memLp_bandExp Y (-x)).toLp (bandExp Y (-x)))
    ((memLp_bandExp Y x).toLp (bandExp Y x))
  filter_upwards [hsub, hs1, hs2, hadd, (memLp_bandExp Y (-x)).coeFn_toLp,
    (memLp_bandExp Y x).coeFn_toLp, (memLp_bandExp Y 0).coeFn_toLp] with ξ e1 e2 e3 e4 e5 e6 e7
  rw [e1, Pi.sub_apply, e2, e3, Pi.smul_apply, Pi.smul_apply, e4, Pi.add_apply, e5, e6, e7]
  simp only [smul_eq_mul]

/-- A band exponential vanishes outside the band. -/
theorem bandExp_of_notMem {Y a ξ : ℝ} (h : ξ ∉ Icc (-Y) Y) : bandExp Y a ξ = 0 := by
  simp only [bandExp, indicator_of_notMem h]

/-- The band kernel at the origin is the width `2 Y` of the band. -/
theorem realBandKernel_zero (Y : ℝ) : realBandKernel Y 0 = 2 * Y := by
  simp [realBandKernel]

/-- The reproducing vector at `x` lies in the level. -/
theorem realPWLevelVector_mem {Y : ℝ} (hY : 0 < Y) (x : ℝ) :
    realPWLevelVector Y x ∈ realPWLevel Y := by
  rw [mem_realPWLevel_iff, mem_realPWLevelFourier_iff]
  have hco := coeFn_fourier_realPWLevelVector Y x
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hco] with ξ h hξ
    rw [h, bandExp_of_notMem hξ, bandExp_of_notMem hξ, bandExp_of_notMem hξ]
    simp
  · have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)
      ).quasiMeasurePreserving.ae_eq_comp
      hco
    filter_upwards [hco, hneg] with ξ h1 h2
    have h3 : ((𝓕 (realPWLevelVector Y x) : H) : ℝ → ℂ) (-ξ) = _ := h2
    rw [h1, h3]
    simp only [Function.comp_apply]
    rw [bandExp_neg Y (-x) ξ, bandExp_neg Y x ξ, bandExp_neg Y 0 ξ, neg_neg, neg_zero]
    ring
  · rw [setIntegral_congr_ae measurableSet_Icc (hco.mono fun ξ h _ ↦ h),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun ξ hξ ↦ by
        rw [bandExp_of_notMem hξ, bandExp_of_notMem hξ, bandExp_of_notMem hξ]
        simp)]
    have i1 := integrable_bandExp Y (-x)
    have i2 := integrable_bandExp Y x
    have i3 := integrable_bandExp Y 0
    have i12 : Integrable fun ξ ↦ (1 / 2 : ℂ) * (bandExp Y (-x) ξ + bandExp Y x ξ) :=
      (i1.add i2).const_mul _
    have i3' : Integrable fun ξ ↦ ((realBandKernel Y x / (2 * Y) : ℝ) : ℂ) * bandExp Y 0 ξ :=
      i3.const_mul _
    have hadd : ∫ ξ, (bandExp Y (-x) ξ + bandExp Y x ξ) =
        (∫ ξ, bandExp Y (-x) ξ) + ∫ ξ, bandExp Y x ξ := integral_add i1 i2
    rw [integral_sub i12 i3', integral_const_mul, integral_const_mul, hadd,
      integral_bandExp hY.le, integral_bandExp hY.le, integral_bandExp hY.le,
      realBandKernel_neg, realBandKernel_zero]
    have hYc : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
    push_cast
    field_simp
    ring

/-- Conjugating a band exponential reflects its phase. -/
theorem conj_bandExp (Y a ξ : ℝ) : conj (bandExp Y a ξ) = bandExp Y (-a) ξ := by
  simp only [bandExp]
  by_cases h : ξ ∈ Icc (-Y) Y
  · rw [indicator_of_mem h, indicator_of_mem h, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  · rw [indicator_of_notMem h, indicator_of_notMem h, map_zero]

/-- A square-integrable function that vanishes outside the band is integrable. -/
private theorem integrable_of_vanish_outside {Y : ℝ} {Ψ : H}
    (hout : ∀ᵐ ξ, ξ ∉ Icc (-Y) Y → Ψ ξ = 0) : Integrable (Ψ : ℝ → ℂ) := by
  have h1 : IntegrableOn (Ψ : ℝ → ℂ) (Icc (-Y) Y) :=
    ((Lp.memLp Ψ).restrict (Icc (-Y) Y)).integrable one_le_two
  have h2 : Integrable ((Icc (-Y) Y).indicator (Ψ : ℝ → ℂ)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr h1
  refine h2.congr ?_
  filter_upwards [hout] with ξ hξ
  by_cases h : ξ ∈ Icc (-Y) Y
  · rw [indicator_of_mem h]
  · rw [indicator_of_notMem h, hξ h]

/-- The pairing of the reproducing vector with a vector of the level, on the frequency side. -/
private theorem inner_realPWLevelVector_eq {Y : ℝ} (x : ℝ) {F : H} (hF : F ∈ realPWLevel Y) :
    ⟪realPWLevelVector Y x, F⟫_ℂ = ∫ ξ, bandExp Y x ξ * (𝓕 F : H) ξ := by
  obtain ⟨hout, heven, hint⟩ := mem_realPWLevelFourier_iff.mp (mem_realPWLevel_iff.mp hF)
  rw [← Lp.inner_fourier_eq, L2.inner_def]
  generalize (𝓕 F : H) = Ψ at hout heven hint ⊢
  have hΨ := Lp.memLp Ψ
  have i1 : Integrable fun ξ ↦ bandExp Y x ξ * Ψ ξ := (memLp_bandExp Y x).integrable_mul hΨ
  have i2 : Integrable fun ξ ↦ bandExp Y (-x) ξ * Ψ ξ := (memLp_bandExp Y (-x)).integrable_mul hΨ
  have i3 : Integrable fun ξ ↦ bandExp Y 0 ξ * Ψ ξ := (memLp_bandExp Y 0).integrable_mul hΨ
  have h3 : ∫ ξ, bandExp Y 0 ξ * Ψ ξ = 0 := by
    rw [← hint, ← integral_indicator measurableSet_Icc]
    refine integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_)
    by_cases h : ξ ∈ Icc (-Y) Y
    · simp [bandExp, h]
    · simp [bandExp, h]
  have h2 : ∫ ξ, bandExp Y (-x) ξ * Ψ ξ = ∫ ξ, bandExp Y x ξ * Ψ ξ := by
    rw [← integral_neg_eq_self (fun ξ ↦ bandExp Y x ξ * Ψ ξ) volume]
    refine integral_congr_ae ?_
    filter_upwards [heven] with ξ hξ
    rw [bandExp_neg, hξ]
  have hsplit : ∫ a, ⟪(𝓕 (realPWLevelVector Y x) : H) a, Ψ a⟫_ℂ =
      (1 / 2 : ℂ) * ((∫ ξ, bandExp Y x ξ * Ψ ξ) + ∫ ξ, bandExp Y (-x) ξ * Ψ ξ) -
        ((realBandKernel Y x / (2 * Y) : ℝ) : ℂ) * ∫ ξ, bandExp Y 0 ξ * Ψ ξ := by
    have i12 : Integrable fun ξ ↦
        (1 / 2 : ℂ) * (bandExp Y x ξ * Ψ ξ + bandExp Y (-x) ξ * Ψ ξ) := (i1.add i2).const_mul _
    have i3' : Integrable fun ξ ↦
        ((realBandKernel Y x / (2 * Y) : ℝ) : ℂ) * (bandExp Y 0 ξ * Ψ ξ) := i3.const_mul _
    rw [← integral_add i1 i2, ← integral_const_mul, ← integral_const_mul,
      ← integral_sub i12 i3']
    refine integral_congr_ae ?_
    filter_upwards [coeFn_fourier_realPWLevelVector Y x] with ξ hξ
    rw [hξ, RCLike.inner_apply, map_sub, map_mul, map_mul, map_add, conj_bandExp, conj_bandExp,
      conj_bandExp, Complex.conj_ofReal, neg_neg, neg_zero]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  rw [hsplit, h2, h3]
  ring

/-- **The reproducing property.** For a vector `F` of the level, `F x` is the pairing of `F`
with the reproducing vector at `x`, for almost every `x`. -/
theorem inner_realPWLevelVector_ae {Y : ℝ} {F : H} (hF : F ∈ realPWLevel Y) :
    ∀ᵐ x, ⟪realPWLevelVector Y x, F⟫_ℂ = F x := by
  obtain ⟨hout, -, -⟩ := mem_realPWLevelFourier_iff.mp (mem_realPWLevel_iff.mp hF)
  have hint := integrable_of_vanish_outside hout
  have hinv := fourierInv_toLp_ae hint (Lp.memLp (𝓕 F : H))
  have hF' : (𝓕⁻ ((Lp.memLp (𝓕 F : H)).toLp ((𝓕 F : H) : ℝ → ℂ)) : H) = F := by
    rw [Lp.toLp_coeFn]
    simp
  rw [hF'] at hinv
  filter_upwards [hinv] with x hx
  rw [hx, inner_realPWLevelVector_eq x hF, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae ?_
  filter_upwards [hout] with ξ hξ
  by_cases h : ξ ∈ Icc (-Y) Y
  · simp only [bandExp, indicator_of_mem h, smul_eq_mul]
    congr 2
    push_cast
    ring
  · rw [bandExp_of_notMem h, hξ h]
    simp

/-! ### The projection onto the level is the integral operator with kernel `q` -/

/-- The level is complete. -/
instance instCompleteSpaceRealPWLevel (Y : ℝ) : CompleteSpace (realPWLevel Y) :=
  (isClosed_realPWLevel Y).completeSpace_coe

/-- **The projection onto the level is the integral operator with kernel `q`.** For every
square-integrable `f`, the orthogonal projection of `f` onto the level is, almost everywhere,
`x ↦ ∫ q (x, y) f y dy`. -/
theorem starProjection_realPWLevel_ae {Y : ℝ} (hY : 0 < Y) (f : H) :
    ∀ᵐ x, ((realPWLevel Y).starProjection f : H) x =
      ∫ y, (realPWLevelKernel Y x y : ℂ) * f y := by
  have hP : (realPWLevel Y).starProjection f ∈ realPWLevel Y :=
    Submodule.starProjection_apply_mem _ f
  filter_upwards [inner_realPWLevelVector_ae hP] with x hx
  rw [← hx, ← Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (realPWLevelVector_mem hY x), L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_realPWLevelVector hY.le x] with y hy
  rw [hy, RCLike.inner_apply, Complex.conj_ofReal, mul_comm]

/-- The kernel of the level is even in its second variable. -/
theorem realPWLevelKernel_neg_right (Y u y : ℝ) :
    realPWLevelKernel Y u (-y) = realPWLevelKernel Y u y := by
  simp only [realPWLevelKernel, sub_neg_eq_add, ← sub_eq_add_neg, realBandKernel_neg]
  ring

/-- The kernel of the level vanishes when its second variable is the origin. -/
theorem realPWLevelKernel_zero_right {Y : ℝ} (hY : Y ≠ 0) (u : ℝ) :
    realPWLevelKernel Y u 0 = 0 := by
  simp only [realPWLevelKernel, sub_zero, add_zero, realBandKernel_zero]
  field_simp
  ring

/-- The kernel of the level is square-integrable in its second variable. -/
theorem memLp_realPWLevelKernel_right {Y : ℝ} (hY : 0 ≤ Y) (u : ℝ) :
    MemLp (fun x ↦ realPWLevelKernel Y u x) 2 := by
  have hS := memLp_realBandKernel_real hY
  have h1 : MemLp (fun x ↦ realBandKernel Y (x - u)) 2 :=
    hS.comp_measurePreserving (measurePreserving_sub_right volume u)
  have h2 : MemLp (fun x ↦ realBandKernel Y (x - -u)) 2 :=
    hS.comp_measurePreserving (measurePreserving_sub_right volume (-u))
  have h := ((h1.add h2).const_mul (1 / 2)).sub (hS.const_mul (realBandKernel Y u / (2 * Y)))
  refine (memLp_congr_ae (Eventually.of_forall fun x ↦ ?_)).mp h
  simp only [Pi.add_apply, Pi.sub_apply, realPWLevelKernel]
  rw [← realBandKernel_neg Y (u - x), neg_sub, sub_neg_eq_add, add_comm x u]
  ring

/-- **The kernel of the level reproduces itself.** -/
theorem integral_realPWLevelKernel_mul_realPWLevelKernel {Y : ℝ} (hY : 0 < Y) (z u : ℝ) :
    ∫ x, realPWLevelKernel Y x z * realPWLevelKernel Y u x = realPWLevelKernel Y u z := by
  have hq := memLp_realPWLevelKernel_right hY.le u
  have hS := memLp_realBandKernel_real hY.le
  have i (a : ℝ) : Integrable fun x ↦ realBandKernel Y (x - a) * realPWLevelKernel Y u x :=
    (hS.comp_measurePreserving (measurePreserving_sub_right volume a)).integrable_mul hq
  have hpt : ∀ x : ℝ, realPWLevelKernel Y x z * realPWLevelKernel Y u x =
      (realBandKernel Y (x - z) * realPWLevelKernel Y u x +
        realBandKernel Y (x - -z) * realPWLevelKernel Y u x) / 2 -
      realBandKernel Y z / (2 * Y) * (realBandKernel Y (x - 0) * realPWLevelKernel Y u x) :=
    fun x ↦ by
      simp only [realPWLevelKernel, sub_neg_eq_add, sub_zero]
      ring
  have i12 : Integrable fun x ↦ (realBandKernel Y (x - z) * realPWLevelKernel Y u x +
      realBandKernel Y (x - -z) * realPWLevelKernel Y u x) / 2 := ((i z).add (i (-z))).div_const 2
  have i3 : Integrable fun x ↦ realBandKernel Y z / (2 * Y) *
      (realBandKernel Y (x - 0) * realPWLevelKernel Y u x) := (i 0).const_mul _
  simp_rw [hpt]
  rw [integral_sub i12 i3, integral_div, integral_add (i z) (i (-z)), integral_const_mul,
    integral_realBandKernel_sub_mul_realPWLevelKernel hY.le,
    integral_realBandKernel_sub_mul_realPWLevelKernel hY.le,
    integral_realBandKernel_sub_mul_realPWLevelKernel hY.le, realPWLevelKernel_neg_right,
    realPWLevelKernel_zero_right hY.ne']
  ring

/-! ### The two kernel operators -/

/-- The kernel `q (x, z) 1_[-L, L] (z)` of the projection onto the level after the sharp spatial
cutoff. -/
def realLevelCutKernel (Y L : ℝ) (p : ℝ × ℝ) : ℂ :=
  (realPWLevelKernel Y p.1 p.2 : ℂ) * (Icc (-L) L).indicator (fun _ ↦ (1 : ℂ)) p.2

private theorem volume_Icc_neg_ne_top' (L : ℝ) : volume (Icc (-L) L) ≠ ⊤ := by
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

private theorem memLp_mul_prod {u v : ℝ → ℂ} (hu : MemLp u 2) (hv : MemLp v 2) :
    MemLp (fun p : ℝ × ℝ ↦ u p.1 * v p.2) 2 (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ u p.1 * v p.2) (volume.prod volume) :=
    (hu.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
      (hv.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
  have hu2 := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  have hv2 := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  refine (hu2.mul_prod hv2).congr (Eventually.of_forall fun p ↦ ?_)
  simp [mul_pow]

/-- The first kernel of the compression is square-integrable. -/
theorem memLp_realLevelCutKernel {Y : ℝ} (hY : 0 ≤ Y) (L : ℝ) :
    MemLp (realLevelCutKernel Y L) 2 (volume.prod volume) := by
  have hS := memLp_realBandKernel hY
  have h1 := memLp_convCutKernel measurableSet_Icc (volume_Icc_neg_ne_top' L) hS
  have h2 := h1.comp_measurePreserving
    ((MeasurePreserving.id (volume : Measure ℝ)).prod (Measure.measurePreserving_neg volume))
  have hcut : MemLp (fun z : ℝ ↦ (realBandKernel Y z : ℂ) *
      (Icc (-L) L).indicator (fun _ ↦ (1 : ℂ)) z) 2 := by
    have h := hS.indicator (measurableSet_Icc : MeasurableSet (Icc (-L) L)).nullMeasurableSet
    refine (memLp_congr_ae (Eventually.of_forall fun z ↦ ?_)).mp h
    by_cases hz : z ∈ Icc (-L) L <;> simp [hz]
  have h3 := memLp_mul_prod hS hcut
  have h := ((h1.const_mul (1 / 2 : ℂ)).add (h2.const_mul (1 / 2 : ℂ))).sub
    (h3.const_mul ((1 / (2 * Y) : ℝ) : ℂ))
  refine (memLp_congr_ae (Eventually.of_forall fun p ↦ ?_)).mp h
  have hmem : (-p.2 ∈ Icc (-L) L) ↔ (p.2 ∈ Icc (-L) L) := by
    constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩
  simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply, Prod.map_fst, Prod.map_snd,
    id_eq, realLevelCutKernel, realPWLevelKernel, sub_neg_eq_add]
  by_cases hp : p.2 ∈ Icc (-L) L
  · rw [indicator_of_mem hp, indicator_of_mem (hmem.mpr hp)]
    push_cast
    ring
  · rw [indicator_of_notMem hp, indicator_of_notMem (mt hmem.mp hp)]
    simp

/-- The sharp spatial cutoff of a vector of `L²`: the class of `1_[-L, L] f`. -/
def realCutoffVector (L : ℝ) (f : H) : H :=
  ((Lp.memLp f).indicator
    (measurableSet_Icc : MeasurableSet (Icc (-L) L)).nullMeasurableSet).toLp _

/-- The cutoff vector is the class of `1_[-L, L] f`. -/
theorem coeFn_realCutoffVector (L : ℝ) (f : H) :
    (realCutoffVector L f : ℝ → ℂ) =ᵐ[volume] (Icc (-L) L).indicator f :=
  MemLp.coeFn_toLp _

/-- The first kernel operator, applied to a vector: the projection onto the level of its
cutoff. -/
theorem integralKernelOperator_realLevelCutKernel_apply {Y : ℝ} (hY : 0 < Y) (L : ℝ) (f : H) :
    (integralKernelOperator volume
      (MemLp.toLp (realLevelCutKernel Y L) (memLp_realLevelCutKernel hY.le L))).val f =
      (realPWLevel Y).starProjection (realCutoffVector L f) := by
  refine Lp.ext ?_
  have happ := integralKernelOperator_apply volume
    (MemLp.toLp (realLevelCutKernel Y L) (memLp_realLevelCutKernel hY.le L)) f
  have hker := Measure.ae_ae_of_ae_prod (memLp_realLevelCutKernel hY.le L).coeFn_toLp
  have hproj := starProjection_realPWLevel_ae hY (realCutoffVector L f)
  filter_upwards [happ, hker, hproj] with x h1 h2 h3
  rw [h1.2, h3]
  refine integral_congr_ae ?_
  filter_upwards [h2, coeFn_realCutoffVector L f] with y e1 e2
  rw [e1, e2, realLevelCutKernel]
  by_cases hy : y ∈ Icc (-L) L <;> simp [hy]

/-- Division by `g > 0` carries Lebesgue measure to `g` times Lebesgue measure. -/
theorem measurePreserving_div_const_real {g : ℝ} (hg : 0 < g) :
    MeasurePreserving (fun x : ℝ ↦ x / g) volume (ENNReal.ofReal g • volume) := by
  refine ⟨by fun_prop, ?_⟩
  have hfun : (fun z : ℝ ↦ z / g) = fun z ↦ z * g⁻¹ := funext fun z ↦ div_eq_mul_inv z g
  rw [hfun, Real.map_volume_mul_right (inv_ne_zero hg.ne'), inv_inv, abs_of_pos hg]

/-- Division by `g > 0` preserves the null sets of Lebesgue measure. -/
theorem quasiMeasurePreserving_div_const_real {g : ℝ} (hg : 0 < g) :
    QuasiMeasurePreserving (fun z : ℝ ↦ z / g) volume volume :=
  ⟨by fun_prop, (measurePreserving_div_const_real hg).map_eq ▸
    Measure.smul_absolutelyContinuous⟩

/-- The second kernel operator, applied to a vector: the cutoff of the dilate of its projection
onto the level. -/
theorem integralKernelOperator_realLevelDilationKernel_apply {Y : ℝ} (hY : 0 < Y) {g : ℝ}
    (hg : 0 < g) (L : ℝ) (f : H) :
    ((integralKernelOperator volume
      (MemLp.toLp (realLevelDilationKernel Y g L)
        (memLp_realLevelDilationKernel hY.le g L))).val f : ℝ → ℂ) =ᵐ[volume] fun z ↦
      (Icc (-L) L).indicator (fun _ ↦ (1 : ℂ)) z *
        ((((√g)⁻¹ : ℝ) : ℂ) * ((realPWLevel Y).starProjection f : H) (z / g)) := by
  have happ := integralKernelOperator_apply volume
    (MemLp.toLp (realLevelDilationKernel Y g L) (memLp_realLevelDilationKernel hY.le g L)) f
  have hker := Measure.ae_ae_of_ae_prod (memLp_realLevelDilationKernel hY.le g L).coeFn_toLp
  have hproj := (quasiMeasurePreserving_div_const_real hg).ae
    (starProjection_realPWLevel_ae hY f)
  filter_upwards [happ, hker, hproj] with z h1 h2 h3
  rw [h1.2, h3, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [h2] with y e
  rw [e, realLevelDilationKernel]
  push_cast
  ring

/-! ### The cutoff and the dilation as operators -/

private theorem integral_symm_of_even' {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) (hc : Continuous f)
    (L : ℝ) : ∫ x in (-L)..L, f x = 2 * ∫ x in (0 : ℝ)..L, f x := by
  have h1 : ∫ x in (-L)..0, f x = ∫ x in (0 : ℝ)..L, f x := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := L) f
    simp only [hf, neg_zero] at h
    exact h.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-L) 0)
    (hc.intervalIntegrable 0 L), h1]
  ring

/-- The sharp spatial cutoff as an operator on `L²(ℝ)`: multiplication by `1_[-L, L]`. -/
def realCutoff (L : ℝ) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := realCutoffVector L
      map_add' := fun f g ↦ by
        refine Lp.ext ?_
        filter_upwards [coeFn_realCutoffVector L (f + g),
          Lp.coeFn_add (realCutoffVector L f) (realCutoffVector L g),
          coeFn_realCutoffVector L f, coeFn_realCutoffVector L g, Lp.coeFn_add f g]
          with x h1 h2 h3 h4 h5
        rw [h1, h2, Pi.add_apply, h3, h4]
        by_cases hx : x ∈ Icc (-L) L
        · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx, h5, Pi.add_apply]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx, add_zero]
      map_smul' := fun c f ↦ by
        refine Lp.ext ?_
        filter_upwards [coeFn_realCutoffVector L (c • f),
          Lp.coeFn_smul c (realCutoffVector L f), coeFn_realCutoffVector L f,
          Lp.coeFn_smul c f] with x h1 h2 h3 h5
        rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3]
        by_cases hx : x ∈ Icc (-L) L
        · rw [indicator_of_mem hx, indicator_of_mem hx, h5, Pi.smul_apply]
        · rw [indicator_of_notMem hx, indicator_of_notMem hx, smul_zero] }
    1 (fun f ↦ by
      rw [one_mul]
      change ‖realCutoffVector L f‖ ≤ ‖f‖
      rw [realCutoffVector, Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
        (eLpNorm_indicator_le _ measurableSet_Icc.nullMeasurableSet))

/-- The cutoff of `f` is the class of `1_[-L, L] f`. -/
theorem coeFn_realCutoff (L : ℝ) (f : H) :
    (realCutoff L f : ℝ → ℂ) =ᵐ[volume] (Icc (-L) L).indicator f :=
  coeFn_realCutoffVector L f

/-- The cutoff is idempotent. -/
theorem realCutoff_comp_realCutoff (L : ℝ) : realCutoff L ∘L realCutoff L = realCutoff L := by
  ext1 f
  refine Lp.ext ?_
  filter_upwards [coeFn_realCutoff L (realCutoff L f), coeFn_realCutoff L f] with x h1 h2
  rw [ContinuousLinearMap.comp_apply, h1]
  by_cases hx : x ∈ Icc (-L) L
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, h2, indicator_of_notMem hx]

/-- A dilate of a square-integrable function is square-integrable. -/
theorem memLp_comp_div_const {g : ℝ} (hg : 0 < g) (f : H) :
    MemLp (fun x ↦ f (x / g)) 2 volume :=
  ((Lp.memLp f).smul_measure ENNReal.ofReal_ne_top).comp_measurePreserving
    (measurePreserving_div_const_real hg)

/-- The unitary dilation of a vector of `L²(ℝ)`: the class of `x ↦ g^(-1/2) f (x / g)`. -/
def realDilationVector {g : ℝ} (hg : 0 < g) (f : H) : H :=
  (((√g)⁻¹ : ℝ) : ℂ) • (memLp_comp_div_const hg f).toLp _

/-- The dilation vector is the class of `x ↦ g^(-1/2) f (x / g)`. -/
theorem coeFn_realDilationVector {g : ℝ} (hg : 0 < g) (f : H) :
    (realDilationVector hg f : ℝ → ℂ) =ᵐ[volume] fun x ↦ (((√g)⁻¹ : ℝ) : ℂ) * f (x / g) := by
  filter_upwards [Lp.coeFn_smul (((√g)⁻¹ : ℝ) : ℂ) ((memLp_comp_div_const hg f).toLp _),
    (memLp_comp_div_const hg f).coeFn_toLp] with x h1 h2
  rw [realDilationVector, h1, Pi.smul_apply, h2, smul_eq_mul]

/-- The dilation preserves the norm of `L²(ℝ)`. -/
theorem norm_realDilationVector {g : ℝ} (hg : 0 < g) (f : H) :
    ‖realDilationVector hg f‖ = ‖f‖ := by
  have hsq : 0 < √g := Real.sqrt_pos.mpr hg
  rw [realDilationVector, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    Lp.norm_toLp, Lp.norm_def]
  have h1 : eLpNorm (fun x ↦ f (x / g)) 2 volume =
      eLpNorm f 2 (ENNReal.ofReal g • volume) :=
    eLpNorm_comp_measurePreserving
      ((Lp.memLp f).smul_measure ENNReal.ofReal_ne_top).aestronglyMeasurable
      (measurePreserving_div_const_real hg)
  rw [h1, eLpNorm_smul_measure_of_ne_zero (by simpa using hg : ENNReal.ofReal g ≠ 0)]
  rw [smul_eq_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hg.le]
  have h2 : g ^ (1 / (2 : ℝ≥0∞)).toReal = √g := by
    rw [Real.sqrt_eq_rpow]
    norm_num
  rw [h2, ← mul_assoc, inv_mul_cancel₀ hsq.ne', one_mul]

/-- The dilation by `g > 0` as a continuous linear map. -/
def realDilationOfPos {g : ℝ} (hg : 0 < g) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := realDilationVector hg
      map_add' := fun f f' ↦ by
        refine Lp.ext ?_
        filter_upwards [coeFn_realDilationVector hg (f + f'),
          Lp.coeFn_add (realDilationVector hg f) (realDilationVector hg f'),
          coeFn_realDilationVector hg f, coeFn_realDilationVector hg f',
          (quasiMeasurePreserving_div_const_real hg).ae (Lp.coeFn_add f f')]
          with x h1 h2 h3 h4 h5
        rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, mul_add]
      map_smul' := fun c f ↦ by
        refine Lp.ext ?_
        filter_upwards [coeFn_realDilationVector hg (c • f),
          Lp.coeFn_smul c (realDilationVector hg f), coeFn_realDilationVector hg f,
          (quasiMeasurePreserving_div_const_real hg).ae (Lp.coeFn_smul c f)]
          with x h1 h2 h3 h5
        rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3, h5, Pi.smul_apply, smul_eq_mul,
          smul_eq_mul]
        ring }
    1 (fun f ↦ by
      rw [one_mul]
      exact (norm_realDilationVector hg f).le)

/-- The unitary dilation `D_g f (x) = g^(-1/2) f (x / g)` of `L²(ℝ)` for `g > 0`. For `g ≤ 0`
it is set to zero. -/
def realDilation (g : ℝ) : H →L[ℂ] H :=
  if hg : 0 < g then realDilationOfPos hg else 0

/-- The dilation of `f` by `g > 0` is the class of `x ↦ g^(-1/2) f (x / g)`. -/
theorem coeFn_realDilation {g : ℝ} (hg : 0 < g) (f : H) :
    (realDilation g f : ℝ → ℂ) =ᵐ[volume] fun x ↦ (((√g)⁻¹ : ℝ) : ℂ) * f (x / g) := by
  simp only [realDilation, hg, ↓reduceDIte]
  exact coeFn_realDilationVector hg f

/-- The dilation by `g > 0` preserves the norm. -/
theorem norm_realDilation {g : ℝ} (hg : 0 < g) (f : H) : ‖realDilation g f‖ = ‖f‖ := by
  simp only [realDilation, hg, ↓reduceDIte]
  exact norm_realDilationVector hg f

/-! ### The two kernel operators and the compression -/

/-- Paper: Theorem 12.4.1.1, Step III, pp. 515–517. **The first kernel operator is the
projection onto the level after the cutoff**, `P ∘ M_L`.
Reconstruction: stated for the rational real-place model at order zero. -/
theorem integralKernelOperator_realLevelCutKernel {Y : ℝ} (hY : 0 < Y) (L : ℝ) :
    (integralKernelOperator volume
      (MemLp.toLp (realLevelCutKernel Y L) (memLp_realLevelCutKernel hY.le L))).val =
      (realPWLevel Y).starProjection ∘L realCutoff L :=
  ContinuousLinearMap.ext fun f ↦ integralKernelOperator_realLevelCutKernel_apply hY L f

/-- Paper: Theorem 12.4.1.1, Step III, pp. 515–517. **The second kernel operator is the cutoff
after the dilation after the projection onto the level**, `M_L ∘ D_g ∘ P`.
Reconstruction: stated for the rational real-place model at order zero. -/
theorem integralKernelOperator_realLevelDilationKernel {Y : ℝ} (hY : 0 < Y) {g : ℝ}
    (hg : 0 < g) (L : ℝ) :
    (integralKernelOperator volume
      (MemLp.toLp (realLevelDilationKernel Y g L)
        (memLp_realLevelDilationKernel hY.le g L))).val =
      realCutoff L ∘L realDilation g ∘L (realPWLevel Y).starProjection := by
  ext1 f
  refine Lp.ext ?_
  have hD := coeFn_realDilation hg ((realPWLevel Y).starProjection f)
  filter_upwards [integralKernelOperator_realLevelDilationKernel_apply hY hg L f,
    coeFn_realCutoff L (realDilation g ((realPWLevel Y).starProjection f)), hD]
    with z h1 h2 h3
  rw [h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h2]
  by_cases hz : z ∈ Icc (-L) L
  · rw [indicator_of_mem hz, indicator_of_mem hz, h3, one_mul]
  · rw [indicator_of_notMem hz, indicator_of_notMem hz, zero_mul]

/-- The compression `P ∘ M_L ∘ D_g ∘ P` of the cutoff dilation to the level is the composite of
the two kernel operators. -/
theorem realPWLevel_compression_eq {Y : ℝ} (hY : 0 < Y) {g : ℝ} (hg : 0 < g) (L : ℝ) :
    (realPWLevel Y).starProjection ∘L realCutoff L ∘L realDilation g ∘L
        (realPWLevel Y).starProjection =
      (integralKernelOperator volume
        (MemLp.toLp (realLevelCutKernel Y L) (memLp_realLevelCutKernel hY.le L))).val.comp
      (integralKernelOperator volume
        (MemLp.toLp (realLevelDilationKernel Y g L)
          (memLp_realLevelDilationKernel hY.le g L))).val := by
  rw [integralKernelOperator_realLevelCutKernel hY L,
    integralKernelOperator_realLevelDilationKernel hY hg L]
  ext1 f
  simp only [ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.comp_apply (realCutoff L) (realCutoff L),
    realCutoff_comp_realCutoff]

/-- The compression of the cutoff dilation to the level is nuclear. -/
theorem isNuclearOperator_realPWLevel_compression {Y : ℝ} (hY : 0 < Y) {g : ℝ} (hg : 0 < g)
    (L : ℝ) :
    IsNuclearOperator ((realPWLevel Y).starProjection ∘L realCutoff L ∘L realDilation g ∘L
      (realPWLevel Y).starProjection) := by
  rw [realPWLevel_compression_eq hY hg L]
  exact nuclear_hilbertSchmidt_comp _ _

/-- Paper: Theorem 12.4.1.1, Step III, pp. 515–517. **The trace of the compression.** With `P`
the orthogonal projection onto the level, `M_L` the sharp spatial cutoff and `D_g` the unitary
dilation, the Hilbert trace of `P ∘ M_L ∘ D_g ∘ P` is
`g^(-1/2) ∫ x in 0..L, realPWLevelDiagonal Y g x`, at every `Y > 0`, `g > 0` and `L ≥ 0`.
Reconstruction: the rational real-place model at order zero, with the sharp spatial cutoff and
no lower cutoff. The level is the closure of the polar-free core
(`topologicalClosure_span_realPWPolarFreeCore`). -/
theorem hilbertTrace_realPWLevel_compression_eq {Y : ℝ} (hY : 0 < Y) {g : ℝ} (hg : 0 < g)
    {L : ℝ} (hL : 0 ≤ L) :
    hilbertTrace ⟨(realPWLevel Y).starProjection ∘L realCutoff L ∘L realDilation g ∘L
        (realPWLevel Y).starProjection, isNuclearOperator_realPWLevel_compression hY hg L⟩ =
      (((√g)⁻¹ * ∫ x in (0 : ℝ)..L, realPWLevelDiagonal Y g x : ℝ) : ℂ) := by
  have hsub : (⟨(realPWLevel Y).starProjection ∘L realCutoff L ∘L realDilation g ∘L
        (realPWLevel Y).starProjection, isNuclearOperator_realPWLevel_compression hY hg L⟩ :
        nuclearEndomorphisms H) =
      ⟨(integralKernelOperator volume
        (MemLp.toLp (realLevelCutKernel Y L) (memLp_realLevelCutKernel hY.le L))).val.comp
      (integralKernelOperator volume
        (MemLp.toLp (realLevelDilationKernel Y g L)
          (memLp_realLevelDilationKernel hY.le g L))).val,
      nuclear_hilbertSchmidt_comp _ _⟩ := Subtype.ext (realPWLevel_compression_eq hY hg L)
  rw [hsub, hilbertTrace_integralKernelOperator_comp]
  have ha := (memLp_realLevelCutKernel hY.le L).coeFn_toLp
  have hb := (memLp_realLevelDilationKernel hY.le g L).coeFn_toLp
  have hbs := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)
    ).quasiMeasurePreserving.ae_eq_comp hb
  have heq : (fun p : ℝ × ℝ ↦
      MemLp.toLp (realLevelCutKernel Y L) (memLp_realLevelCutKernel hY.le L) p *
        MemLp.toLp (realLevelDilationKernel Y g L) (memLp_realLevelDilationKernel hY.le g L)
          p.swap) =ᵐ[volume.prod volume]
      fun p ↦ realLevelCutKernel Y L p * realLevelDilationKernel Y g L p.swap := by
    filter_upwards [ha, hbs] with p hpa hpb
    rw [hpa]
    rw [show MemLp.toLp (realLevelDilationKernel Y g L)
      (memLp_realLevelDilationKernel hY.le g L) p.swap = _ from hpb]
    rfl
  rw [integral_congr_ae heq]
  have hint : Integrable
      (fun p : ℝ × ℝ ↦ realLevelCutKernel Y L p * realLevelDilationKernel Y g L p.swap)
      (volume.prod volume) :=
    (memLp_realLevelCutKernel hY.le L).integrable_mul
      ((memLp_realLevelDilationKernel hY.le g L).comp_measurePreserving
        (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)))
  rw [integral_prod_symm _ hint]
  have hin (z : ℝ) : ∫ x, realLevelCutKernel Y L (x, z) *
      realLevelDilationKernel Y g L (Prod.swap (x, z)) =
      (Icc (-L) L).indicator
        (fun z ↦ (((√g)⁻¹ * (realPWLevelDiagonal Y g z / 2) : ℝ) : ℂ)) z := by
    by_cases h : z ∈ Icc (-L) L
    · simp only [realLevelCutKernel, realLevelDilationKernel, Prod.swap, h, indicator_of_mem,
        mul_one, one_mul]
      have hc : ∀ x : ℝ, (realPWLevelKernel Y x z : ℂ) *
          (((√g)⁻¹ * realPWLevelKernel Y (z / g) x : ℝ) : ℂ) =
          (((√g)⁻¹ * (realPWLevelKernel Y x z * realPWLevelKernel Y (z / g) x) : ℝ) : ℂ) :=
        fun x ↦ by
          push_cast
          ring
      simp_rw [hc]
      rw [integral_complex_ofReal, integral_const_mul,
        integral_realPWLevelKernel_mul_realPWLevelKernel hY, realPWLevelKernel_div_self]
    · simp [realLevelCutKernel, realLevelDilationKernel, h]
  simp_rw [hin]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -L ≤ L), intervalIntegral.integral_ofReal]
  congr 1
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    integral_symm_of_even' (realPWLevelDiagonal_neg Y g) (continuous_realPWLevelDiagonal Y g) L]
  ring

/-! ### The limit of the traces -/

/-- The Hilbert trace of the compression `P ∘ M_L ∘ D_g ∘ P`, as a function of the dilation.
It is set to zero unless `Y > 0` and `g > 0`. -/
def realPWLevelCompressionTrace (Y L g : ℝ) : ℂ :=
  if h : 0 < Y ∧ 0 < g then
    hilbertTrace ⟨(realPWLevel Y).starProjection ∘L realCutoff L ∘L realDilation g ∘L
      (realPWLevel Y).starProjection, isNuclearOperator_realPWLevel_compression h.1 h.2 L⟩
  else 0

/-- The trace of the compression in closed form. -/
theorem realPWLevelCompressionTrace_eq {Y : ℝ} (hY : 0 < Y) {g : ℝ} (hg : 0 < g) {L : ℝ}
    (hL : 0 ≤ L) :
    realPWLevelCompressionTrace Y L g =
      (((√g)⁻¹ * ∫ x in (0 : ℝ)..L, realPWLevelDiagonal Y g x : ℝ) : ℂ) := by
  simp only [realPWLevelCompressionTrace, hY, hg, and_self, ↓reduceDIte]
  exact hilbertTrace_realPWLevel_compression_eq hY hg hL

section Limit

variable {ι : Type*} {l : Filter ι} {Y L : ι → ℝ}

/-- Paper: Theorem 12.4.1.1, pp. 514–519. For one dilation `g ≠ 1`, the Hilbert traces of the
compressions `P ∘ M_L ∘ D_g ∘ P` tend, as `Y * L → ∞`, to `g^(-1/2)` times
`1 / (2 |1 / g - 1|) + 1 / (2 (1 / g + 1)) - min 1 g`. For `g > 1` this is
`g^(3/2) / (g² - 1) - g^(-1/2)`.
Reconstruction: as for `hilbertTrace_realPWLevel_compression_eq`. -/
theorem tendsto_hilbertTrace_realPWLevel_compression_eq (hY : ∀ i, 0 < Y i)
    (hL : ∀ i, 0 ≤ L i) (hYL : Tendsto (fun i ↦ Y i * L i) l atTop) {g : ℝ} (hg0 : 0 < g)
    (hg1 : g ≠ 1) :
    Tendsto (fun i ↦ hilbertTrace ⟨(realPWLevel (Y i)).starProjection ∘L realCutoff (L i) ∘L
        realDilation g ∘L (realPWLevel (Y i)).starProjection,
      isNuclearOperator_realPWLevel_compression (hY i) hg0 (L i)⟩) l
      (𝓝 (((√g)⁻¹ * ((2 * |1 / g - 1|)⁻¹ + (2 * (1 / g + 1))⁻¹ - min 1 g) : ℝ) : ℂ)) := by
  refine Tendsto.congr
    (fun i ↦ (hilbertTrace_realPWLevel_compression_eq (hY i) hg0 (hL i)).symm) ?_
  refine (Complex.continuous_ofReal.tendsto _).comp ?_
  have h := ((tendsto_realPWBandDiagonalMass hYL hg0 hg1).sub
    (tendsto_realPWPolarDiagonalMass hYL hg0)).const_mul ((√g)⁻¹)
  refine h.congr' ?_
  filter_upwards [hYL.eventually_gt_atTop 0] with i hi
  rw [integral_realPWLevelDiagonal hg0 hg1 (hY i).ne' (right_ne_zero_of_mul hi.ne')]

variable [l.IsCountablyGenerated] {a b : ℝ} {φ : ℝ → ℝ}

/-- Paper: Theorem 12.4.1.1, pp. 514–519, as used on p. 520. The average against `φ(g) d×g` of
the Hilbert traces of the compressions `P ∘ M_L ∘ D_g ∘ P` tends, as `Y * L → ∞`, to the
real-place term of (12.5.1.1) minus `∫ φ(g) min(g^(1/2), g^(-1/2)) d×g`.
Reconstruction: the average of the traces stands for the trace of the averaged operator; the
average of the operators is not formed here. -/
theorem tendsto_integral_realPWLevelCompressionTrace (ha : 0 < a) (hab : a ≤ b)
    (h1 : 1 ∉ Icc a b) (hφ : ContinuousOn φ (Icc a b)) (hY : ∀ i, 0 < Y i)
    (hL : ∀ i, 0 ≤ L i) (hYL : Tendsto (fun i ↦ Y i * L i) l atTop) :
    Tendsto (fun i ↦ ∫ g in a..b,
        (φ g : ℂ) * realPWLevelCompressionTrace (Y i) (L i) g / (g : ℂ)) l
      (𝓝 (((∫ g in a..b, φ g * (1 / 2 * (√g / |1 - g| + √g / |1 + g|)) / g) -
        ∫ g in a..b, φ g * min (√g) (√g)⁻¹ / g : ℝ) : ℂ)) := by
  have hw : ContinuousOn (fun g : ℝ ↦ φ g * (√g * g)⁻¹) (Icc a b) :=
    hφ.mul ((Real.continuous_sqrt.continuousOn.mul continuousOn_id).inv₀ fun _ hg ↦
      mul_ne_zero (Real.sqrt_pos.mpr (ha.trans_le hg.1)).ne' (ha.trans_le hg.1).ne')
  have hreal := sLocalTrace_realPWLevel_diagonal_tendsto ha hab h1 hφ hYL
  refine ((Complex.continuous_ofReal.tendsto _).comp hreal).congr fun i ↦ ?_
  simp only [Function.comp_apply]
  have hpt : ∀ g ∈ uIcc a b,
      (φ g : ℂ) * realPWLevelCompressionTrace (Y i) (L i) g / (g : ℂ) =
      ((φ g * (√g * g)⁻¹ * ∫ x in (0 : ℝ)..L i, realPWLevelDiagonal (Y i) g x : ℝ) : ℂ) :=
    fun g hg ↦ by
      rw [uIcc_of_le hab] at hg
      rw [realPWLevelCompressionTrace_eq (hY i) (ha.trans_le hg.1) (hL i)]
      push_cast
      ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_ofReal,
    ← integral_integral_realPWLevelDiagonal_swap ha hab hw]
  congr 1
  refine intervalIntegral.integral_congr fun x _ ↦ intervalIntegral.integral_congr fun g _ ↦ ?_
  ring

end Limit

end RiemannMasullo
