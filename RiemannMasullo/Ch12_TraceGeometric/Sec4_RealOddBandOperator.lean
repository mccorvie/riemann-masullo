module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelOperator
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedBandKernel

/-! # The compression of a multiplier after the dilation to the odd band

Paper: Theorem 12.4.1.1, Step III, pp. 515–517, and the value used on p. 520.

`Sec4_RealPWLevelOperator` computes the Hilbert trace of the compression of the cutoff dilation
to the even functions of the band less one line. The weighted band of the rational real-place
model is carried by multiplication by `μ x = (x ^ 2 - i) / x` into the odd functions of the
band, and the dilation becomes a bounded multiplier after the dilation
(`Sec4_WeightedBandKernel`). This file does the operator theory on the odd band, with an
arbitrary bounded measurable multiplier.

* `realOddBand Y`: the functions of `L²(ℝ)` whose Fourier transform vanishes outside `[-Y, Y]`
  and is odd.
* `starProjection_realOddBand_ae`: the orthogonal projection `P_o` onto the odd band is the
  integral operator with kernel `K_o (u, y) = (S (u - y) - S (u + y)) / 2`, where `S` is the
  band kernel. The proof is by reproducing vectors, as for the level.
* `realMultiplier r`: multiplication by a bounded measurable function `r`, as a continuous
  linear map of `L²(ℝ)`.
* `integralKernelOperator_realOddCutKernel`: the integral operator with kernel
  `K_o (x, z) 1_[-L, L] (z)` is `P_o ∘ M_L`.
* `integralKernelOperator_realOddDilationKernel`: the integral operator with kernel
  `1_[-L, L] (z) r (z) g^(-1/2) K_o (z / g, y)` is `M_L ∘ M_r ∘ D_g ∘ P_o`.
* `hilbertTrace_realOddBand_compression_eq`: the compression `P_o ∘ M_L ∘ M_r ∘ D_g ∘ P_o` is
  nuclear, and its Hilbert trace is `g^(-1/2) ∫ z in -L..L, r z * K_o (z / g, z)`.

**Not formalized here.** The limit of these traces for the multiplier of the weighted band, and
the passage from the odd band to the functions of it that vanish at `ζ`, are in the files that
import this one.
-/

open MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate InnerProductSpace SchwartzMap ContDiff ENNReal

@[expose] public noncomputable section

namespace RiemannMasullo

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

/-! ### The odd band -/

/-- The frequency side of the odd band: square-integrable functions that vanish outside
`[-Y, Y]` and are odd. -/
def realOddBandFourier (Y : ℝ) : Submodule ℂ H :=
  LinearMap.ker (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Icc (-Y) Y)ᶜ).toLinearMap ⊓
    LinearMap.ker (realReflection.toLinearMap + LinearMap.id)

/-- Membership in the frequency side of the odd band, in terms of the function. -/
theorem mem_realOddBandFourier_iff {Y : ℝ} {Ψ : H} : Ψ ∈ realOddBandFourier Y ↔
    (∀ᵐ ξ, ξ ∉ Icc (-Y) Y → Ψ ξ = 0) ∧ (∀ᵐ ξ, Ψ (-ξ) = -Ψ ξ) := by
  simp only [realOddBandFourier, Submodule.mem_inf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe]
  refine and_congr ?_ ?_
  · have hco := LpToLpRestrictCLM_coeFn (𝕜 := ℂ) (Icc (-Y) Y)ᶜ Ψ
    have hae : (∀ᵐ ξ, ξ ∉ Icc (-Y) Y → Ψ ξ = 0) ↔
        ∀ᵐ ξ ∂volume.restrict (Icc (-Y) Y)ᶜ, Ψ ξ = 0 :=
      (ae_restrict_iff' (measurableSet_Icc.compl : MeasurableSet (Icc (-Y) Y)ᶜ)).symm
    rw [hae]
    constructor
    · intro h
      have h0 : (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Icc (-Y) Y)ᶜ Ψ : ℝ → ℂ)
          =ᵐ[volume.restrict (Icc (-Y) Y)ᶜ] 0 := by
        have := (Lp.eq_zero_iff_ae_eq_zero
          (f := LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Icc (-Y) Y)ᶜ Ψ)).mp h
        exact this
      filter_upwards [hco, h0] with ξ h1 h2
      rw [← h1, h2]
      rfl
    · intro h
      refine (Lp.eq_zero_iff_ae_eq_zero).mpr ?_
      filter_upwards [hco, h] with ξ h1 h2
      rw [h1, h2]
      rfl
  · have hco := Lp.coeFn_compMeasurePreserving Ψ (Measure.measurePreserving_neg volume)
    simp only [LinearMap.add_apply, LinearMap.id_coe, id_eq, add_eq_zero_iff_eq_neg]
    constructor
    · intro h
      have h' : (realReflection Ψ : ℝ → ℂ) =ᵐ[volume] (-Ψ : H) := by
        have : realReflection Ψ = -Ψ := h
        rw [this]
      filter_upwards [hco, h', Lp.coeFn_neg Ψ] with ξ h1 h2 h3
      have h4 : (realReflection Ψ : ℝ → ℂ) ξ = Ψ (-ξ) := h1
      rw [← h4, h2, h3]
      rfl
    · intro h
      refine Lp.ext ?_
      filter_upwards [hco, h, Lp.coeFn_neg Ψ] with ξ h1 h2 h3
      rw [h3]
      exact h1.trans h2

/-- The odd functions of the band: the functions of `L²(ℝ)` whose Fourier transform vanishes
outside `[-Y, Y]` and is odd. -/
def realOddBand (Y : ℝ) : Submodule ℂ H :=
  (realOddBandFourier Y).comap (Lp.fourierTransformₗᵢ ℝ ℂ).toLinearEquiv.toLinearMap

/-- A function is in the odd band when its Fourier transform is in the frequency side. -/
theorem mem_realOddBand_iff {Y : ℝ} {F : H} :
    F ∈ realOddBand Y ↔ (𝓕 F : H) ∈ realOddBandFourier Y := Iff.rfl

/-- The frequency side of the odd band is closed. -/
theorem isClosed_realOddBandFourier (Y : ℝ) : IsClosed (realOddBandFourier Y : Set H) := by
  have h : (realOddBandFourier Y : Set H) =
      {Ψ | LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Icc (-Y) Y)ᶜ Ψ = 0} ∩
        {Ψ | realReflection Ψ + Ψ = 0} := by
    ext Ψ
    simp only [realOddBandFourier, Submodule.coe_inf, mem_inter_iff, SetLike.mem_coe,
      LinearMap.mem_ker, ContinuousLinearMap.coe_coe, LinearMap.add_apply, LinearMap.id_coe,
      id_eq, mem_ofPred_eq, LinearIsometry.coe_toLinearMap]
  rw [h]
  exact (isClosed_eq (ContinuousLinearMap.continuous _) continuous_const).inter
    (isClosed_eq (realReflection.continuous.add continuous_id) continuous_const)

/-- The odd band is closed. -/
theorem isClosed_realOddBand (Y : ℝ) : IsClosed (realOddBand Y : Set H) :=
  (isClosed_realOddBandFourier Y).preimage (Lp.fourierTransformₗᵢ ℝ ℂ).continuous

/-- The odd band is complete. -/
instance instCompleteSpaceRealOddBand (Y : ℝ) : CompleteSpace (realOddBand Y) :=
  (isClosed_realOddBand Y).completeSpace_coe

/-! ### The reproducing vectors -/

/-- The reproducing vector of the odd band at `x`: the class of `y ↦ K_o (x, y)`. -/
def realOddBandVector (Y x : ℝ) : H :=
  (1 / 2 : ℂ) • (realBandVector Y x - realBandVector Y (-x))

/-- The reproducing vector at `x` is the class of `y ↦ K_o (x, y)`. -/
theorem coeFn_realOddBandVector {Y : ℝ} (hY : 0 ≤ Y) (x : ℝ) :
    (realOddBandVector Y x : ℝ → ℂ) =ᵐ[volume] fun y ↦ (realOddBandKernel Y x y : ℂ) := by
  have h1 := coeFn_realBandVector hY x
  have h2 := coeFn_realBandVector hY (-x)
  have hs := Lp.coeFn_smul (1 / 2 : ℂ) (realBandVector Y x - realBandVector Y (-x))
  have hsub := Lp.coeFn_sub (realBandVector Y x) (realBandVector Y (-x))
  filter_upwards [h1, h2, hs, hsub] with y e1 e2 e3 e4
  rw [realOddBandVector, e3, Pi.smul_apply, e4, Pi.sub_apply, e1, e2, realOddBandKernel,
    ← realBandKernel_neg Y (y - x), neg_sub, sub_neg_eq_add, add_comm y x]
  simp only [smul_eq_mul]
  push_cast
  ring

/-- The Fourier transform of the reproducing vector. -/
theorem fourier_realOddBandVector (Y x : ℝ) :
    (𝓕 (realOddBandVector Y x) : H) =
      (1 / 2 : ℂ) • ((memLp_bandExp Y (-x)).toLp (bandExp Y (-x)) -
        (memLp_bandExp Y x).toLp (bandExp Y x)) := by
  have hlin : ∀ (c : ℂ) (u v : H), (𝓕 (c • (u - v)) : H) = c • ((𝓕 u : H) - (𝓕 v : H)) :=
    fun c u v ↦ by
      change Lp.fourierTransformₗᵢ ℝ ℂ (c • (u - v)) = _
      rw [map_smul, map_sub]
      rfl
  rw [realOddBandVector, hlin, fourier_realBandVector, fourier_realBandVector, neg_neg]

private theorem coeFn_fourier_realOddBandVector (Y x : ℝ) :
    ((𝓕 (realOddBandVector Y x) : H) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦
      (1 / 2 : ℂ) * (bandExp Y (-x) ξ - bandExp Y x ξ) := by
  rw [fourier_realOddBandVector]
  have hs := Lp.coeFn_smul (1 / 2 : ℂ) ((memLp_bandExp Y (-x)).toLp (bandExp Y (-x)) -
      (memLp_bandExp Y x).toLp (bandExp Y x))
  have hsub := Lp.coeFn_sub ((memLp_bandExp Y (-x)).toLp (bandExp Y (-x)))
    ((memLp_bandExp Y x).toLp (bandExp Y x))
  filter_upwards [hs, hsub, (memLp_bandExp Y (-x)).coeFn_toLp,
    (memLp_bandExp Y x).coeFn_toLp] with ξ e1 e2 e3 e4
  rw [e1, Pi.smul_apply, e2, Pi.sub_apply, e3, e4]
  simp only [smul_eq_mul]

/-- The reproducing vector at `x` lies in the odd band. -/
theorem realOddBandVector_mem (Y x : ℝ) : realOddBandVector Y x ∈ realOddBand Y := by
  rw [mem_realOddBand_iff, mem_realOddBandFourier_iff]
  have hco := coeFn_fourier_realOddBandVector Y x
  refine ⟨?_, ?_⟩
  · filter_upwards [hco] with ξ h hξ
    rw [h, bandExp_of_notMem hξ, bandExp_of_notMem hξ]
    simp
  · have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)
      ).quasiMeasurePreserving.ae_eq_comp hco
    filter_upwards [hco, hneg] with ξ h1 h2
    have h3 : ((𝓕 (realOddBandVector Y x) : H) : ℝ → ℂ) (-ξ) = _ := h2
    rw [h1, h3]
    simp only [Function.comp_apply]
    rw [bandExp_neg Y (-x) ξ, bandExp_neg Y x ξ, neg_neg]
    ring

/-- A square-integrable function that vanishes outside the band is integrable. -/
private theorem integrable_of_vanish_outside_band {Y : ℝ} {Ψ : H}
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

/-- The pairing of the reproducing vector with a vector of the odd band, on the frequency
side. -/
private theorem inner_realOddBandVector_eq {Y : ℝ} (x : ℝ) {F : H} (hF : F ∈ realOddBand Y) :
    ⟪realOddBandVector Y x, F⟫_ℂ = ∫ ξ, bandExp Y x ξ * (𝓕 F : H) ξ := by
  obtain ⟨hout, hodd⟩ := mem_realOddBandFourier_iff.mp (mem_realOddBand_iff.mp hF)
  rw [← Lp.inner_fourier_eq, L2.inner_def]
  generalize (𝓕 F : H) = Ψ at hout hodd ⊢
  have hΨ := Lp.memLp Ψ
  have i1 : Integrable fun ξ ↦ bandExp Y x ξ * Ψ ξ := (memLp_bandExp Y x).integrable_mul hΨ
  have i2 : Integrable fun ξ ↦ bandExp Y (-x) ξ * Ψ ξ := (memLp_bandExp Y (-x)).integrable_mul hΨ
  have h2 : ∫ ξ, bandExp Y (-x) ξ * Ψ ξ = -∫ ξ, bandExp Y x ξ * Ψ ξ := by
    rw [← integral_neg_eq_self (fun ξ ↦ bandExp Y x ξ * Ψ ξ) volume, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hodd] with ξ hξ
    rw [bandExp_neg, hξ]
    ring
  have hsplit : ∫ a, ⟪(𝓕 (realOddBandVector Y x) : H) a, Ψ a⟫_ℂ =
      (1 / 2 : ℂ) * ((∫ ξ, bandExp Y x ξ * Ψ ξ) - ∫ ξ, bandExp Y (-x) ξ * Ψ ξ) := by
    rw [← integral_sub i1 i2, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_fourier_realOddBandVector Y x] with ξ hξ
    rw [hξ, RCLike.inner_apply, map_mul, map_sub, conj_bandExp, conj_bandExp, neg_neg]
    simp only [map_div₀, map_one, map_ofNat]
    ring
  rw [hsplit, h2]
  ring

/-- **The reproducing property.** For a vector `F` of the odd band, `F x` is the pairing of `F`
with the reproducing vector at `x`, for almost every `x`. -/
theorem inner_realOddBandVector_ae {Y : ℝ} {F : H} (hF : F ∈ realOddBand Y) :
    ∀ᵐ x, ⟪realOddBandVector Y x, F⟫_ℂ = F x := by
  obtain ⟨hout, -⟩ := mem_realOddBandFourier_iff.mp (mem_realOddBand_iff.mp hF)
  have hint := integrable_of_vanish_outside_band hout
  have hinv := fourierInv_toLp_ae hint (Lp.memLp (𝓕 F : H))
  have hF' : (𝓕⁻ ((Lp.memLp (𝓕 F : H)).toLp ((𝓕 F : H) : ℝ → ℂ)) : H) = F := by
    rw [Lp.toLp_coeFn]
    simp
  rw [hF'] at hinv
  filter_upwards [hinv] with x hx
  rw [hx, inner_realOddBandVector_eq x hF, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae ?_
  filter_upwards [hout] with ξ hξ
  by_cases h : ξ ∈ Icc (-Y) Y
  · simp only [bandExp, indicator_of_mem h, smul_eq_mul]
    congr 2
    push_cast
    ring
  · rw [bandExp_of_notMem h, hξ h]
    simp

/-! ### The projection onto the odd band is the integral operator with kernel `K_o` -/

/-- **The projection onto the odd band is the integral operator with kernel `K_o`.** For every
square-integrable `f`, the orthogonal projection of `f` onto the odd band is, almost
everywhere, `x ↦ ∫ K_o (x, y) f y dy`. -/
theorem starProjection_realOddBand_ae {Y : ℝ} (hY : 0 < Y) (f : H) :
    ∀ᵐ x, ((realOddBand Y).starProjection f : H) x =
      ∫ y, (realOddBandKernel Y x y : ℂ) * f y := by
  have hP : (realOddBand Y).starProjection f ∈ realOddBand Y :=
    Submodule.starProjection_apply_mem _ f
  filter_upwards [inner_realOddBandVector_ae hP] with x hx
  rw [← hx, ← Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (realOddBandVector_mem Y x), L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_realOddBandVector hY.le x] with y hy
  rw [hy, RCLike.inner_apply, Complex.conj_ofReal, mul_comm]

/-- **The kernel of the odd band reproduces itself.** -/
theorem integral_realOddBandKernel_mul_realOddBandKernel {Y : ℝ} (hY : 0 ≤ Y) (z u : ℝ) :
    ∫ x, realOddBandKernel Y x z * realOddBandKernel Y u x = realOddBandKernel Y u z := by
  have i (a b : ℝ) := integrable_realBandKernel_sub_mul_sub hY a b
  have hpt : ∀ x : ℝ, realOddBandKernel Y x z * realOddBandKernel Y u x =
      (realBandKernel Y (x - z) * realBandKernel Y (x - u) -
        realBandKernel Y (x - z) * realBandKernel Y (x - -u) -
        realBandKernel Y (x - -z) * realBandKernel Y (x - u) +
        realBandKernel Y (x - -z) * realBandKernel Y (x - -u)) / 4 := fun x ↦ by
    simp only [realOddBandKernel, sub_neg_eq_add]
    rw [← realBandKernel_neg Y (u - x), neg_sub, add_comm u x]
    ring
  have iA : Integrable fun x ↦ realBandKernel Y (x - z) * realBandKernel Y (x - u) -
      realBandKernel Y (x - z) * realBandKernel Y (x - -u) := (i z u).sub (i z (-u))
  have iB : Integrable fun x ↦ realBandKernel Y (x - z) * realBandKernel Y (x - u) -
      realBandKernel Y (x - z) * realBandKernel Y (x - -u) -
      realBandKernel Y (x - -z) * realBandKernel Y (x - u) := iA.sub (i (-z) u)
  simp_rw [hpt]
  rw [integral_div, integral_add iB (i (-z) (-u)), integral_sub iA (i (-z) u),
    integral_sub (i z u) (i z (-u)), integral_realBandKernel_sub_mul_sub hY,
    integral_realBandKernel_sub_mul_sub hY, integral_realBandKernel_sub_mul_sub hY,
    integral_realBandKernel_sub_mul_sub hY]
  simp only [realOddBandKernel, sub_neg_eq_add]
  rw [← realBandKernel_neg Y (z - u), neg_sub, show -z - u = -(u + z) by ring,
    realBandKernel_neg, show -z + u = u - z by ring, add_comm z u]
  ring

/-! ### Multiplication by a bounded measurable function -/

/-- The product of a bounded measurable function and a square-integrable function is
square-integrable. -/
theorem memLp_mul_of_norm_le {r : ℝ → ℂ} (hr : Measurable r) {C : ℝ} (hC : ∀ x, ‖r x‖ ≤ C)
    (f : H) : MemLp (fun x ↦ r x * f x) 2 volume :=
  MemLp.of_le_mul (Lp.memLp f) (hr.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Eventually.of_forall fun x ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))

/-- The product of a bounded measurable function `r` and a vector of `L²(ℝ)`: the class of
`x ↦ r x * f x`. -/
def realMultiplierVector {r : ℝ → ℂ} (hr : Measurable r) {C : ℝ} (hC : ∀ x, ‖r x‖ ≤ C)
    (f : H) : H :=
  (memLp_mul_of_norm_le hr hC f).toLp _

/-- The product vector is the class of `x ↦ r x * f x`. -/
theorem coeFn_realMultiplierVector {r : ℝ → ℂ} (hr : Measurable r) {C : ℝ}
    (hC : ∀ x, ‖r x‖ ≤ C) (f : H) :
    (realMultiplierVector hr hC f : ℝ → ℂ) =ᵐ[volume] fun x ↦ r x * f x :=
  MemLp.coeFn_toLp _

/-- The product with a function bounded by `C` has norm at most `C` times the norm. -/
theorem norm_realMultiplierVector_le {r : ℝ → ℂ} (hr : Measurable r) {C : ℝ}
    (hC : ∀ x, ‖r x‖ ≤ C) (f : H) : ‖realMultiplierVector hr hC f‖ ≤ C * ‖f‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [coeFn_realMultiplierVector hr hC f] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- Multiplication by a measurable function bounded by `C`, as a continuous linear map. -/
def realMultiplierOfBounded {r : ℝ → ℂ} (hr : Measurable r) {C : ℝ} (hC : ∀ x, ‖r x‖ ≤ C) :
    H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := realMultiplierVector hr hC
      map_add' := fun f f' ↦ by
        refine Lp.ext ?_
        filter_upwards [coeFn_realMultiplierVector hr hC (f + f'),
          Lp.coeFn_add (realMultiplierVector hr hC f) (realMultiplierVector hr hC f'),
          coeFn_realMultiplierVector hr hC f, coeFn_realMultiplierVector hr hC f',
          Lp.coeFn_add f f'] with x h1 h2 h3 h4 h5
        rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply, mul_add]
      map_smul' := fun c f ↦ by
        refine Lp.ext ?_
        filter_upwards [coeFn_realMultiplierVector hr hC (c • f),
          Lp.coeFn_smul c (realMultiplierVector hr hC f), coeFn_realMultiplierVector hr hC f,
          Lp.coeFn_smul c f] with x h1 h2 h3 h5
        rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3, h5, Pi.smul_apply, smul_eq_mul,
          smul_eq_mul]
        ring }
    C (fun f ↦ norm_realMultiplierVector_le hr hC f)

open Classical in
/-- Multiplication by `r` as an operator on `L²(ℝ)`, when `r` is measurable and bounded.
Otherwise it is set to zero. -/
def realMultiplier (r : ℝ → ℂ) : H →L[ℂ] H :=
  if h : Measurable r ∧ ∃ C : ℝ, ∀ x, ‖r x‖ ≤ C then
    realMultiplierOfBounded h.1 h.2.choose_spec
  else 0

/-- The product of `f` with a bounded measurable `r` is the class of `x ↦ r x * f x`. -/
theorem coeFn_realMultiplier {r : ℝ → ℂ} (hr : Measurable r) {C : ℝ} (hC : ∀ x, ‖r x‖ ≤ C)
    (f : H) : (realMultiplier r f : ℝ → ℂ) =ᵐ[volume] fun x ↦ r x * f x := by
  unfold realMultiplier
  split_ifs with h
  · exact coeFn_realMultiplierVector h.1 h.2.choose_spec f
  · exact absurd ⟨hr, C, hC⟩ h

/-- Multiplication by a function bounded by `C` multiplies the norm by at most `C`. -/
theorem norm_realMultiplier_apply_le {r : ℝ → ℂ} (hr : Measurable r) {C : ℝ}
    (hC : ∀ x, ‖r x‖ ≤ C) (f : H) : ‖realMultiplier r f‖ ≤ C * ‖f‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [coeFn_realMultiplier hr hC f] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-! ### The two kernels -/

/-- The kernel `K_o (x, z) 1_[-L, L] (z)` of the projection onto the odd band after the sharp
spatial cutoff. -/
def realOddCutKernel (Y L : ℝ) (p : ℝ × ℝ) : ℂ :=
  (realOddBandKernel Y p.1 p.2 : ℂ) * (Icc (-L) L).indicator (fun _ ↦ (1 : ℂ)) p.2

/-- The kernel `1_[-L, L] (z) r (z) g^(-1/2) K_o (z / g, y)` of the sharp spatial cutoff after
the multiplication by `r` after the dilation by `g` after the projection onto the odd band. -/
def realOddDilationKernel (Y g L : ℝ) (r : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (Icc (-L) L).indicator (fun _ ↦ (1 : ℂ)) p.1 *
    (r p.1 * (((√g)⁻¹ * realOddBandKernel Y (p.1 / g) p.2 : ℝ) : ℂ))

/-- The first kernel is square-integrable. -/
theorem memLp_realOddCutKernel {Y : ℝ} (hY : 0 ≤ Y) (L : ℝ) :
    MemLp (realOddCutKernel Y L) 2 (volume.prod volume) := by
  have hS := memLp_realBandKernel hY
  have h1 := memLp_convCutKernel measurableSet_Icc (volume_Icc_neg_self_ne_top L) hS
  have h2 := h1.comp_measurePreserving
    ((MeasurePreserving.id (volume : Measure ℝ)).prod (Measure.measurePreserving_neg volume))
  have h := (h1.const_mul (1 / 2 : ℂ)).sub (h2.const_mul (1 / 2 : ℂ))
  refine (memLp_congr_ae (Eventually.of_forall fun p ↦ ?_)).mp h
  have hmem : (-p.2 ∈ Icc (-L) L) ↔ (p.2 ∈ Icc (-L) L) := by
    constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩
  simp only [Pi.sub_apply, Function.comp_apply, Prod.map_fst, Prod.map_snd,
    id_eq, realOddCutKernel, realOddBandKernel, sub_neg_eq_add]
  by_cases hp : p.2 ∈ Icc (-L) L
  · rw [indicator_of_mem hp, indicator_of_mem (hmem.mpr hp)]
    push_cast
    ring
  · rw [indicator_of_notMem hp, indicator_of_notMem (mt hmem.mp hp)]
    simp

private theorem memLp_cutLeft_comp_sub {C : Set ℝ} (hC : MeasurableSet C) (hCf : volume C ≠ ⊤)
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

/-- The kernel of the odd band along the dilation is continuous. -/
theorem continuous_realOddBandKernel_div (Y g : ℝ) :
    Continuous fun p : ℝ × ℝ ↦ realOddBandKernel Y (p.1 / g) p.2 := by
  unfold realOddBandKernel
  exact (((continuous_realBandKernel Y).comp (by fun_prop)).sub
    ((continuous_realBandKernel Y).comp (by fun_prop))).div_const 2

/-- The second kernel is square-integrable. -/
theorem memLp_realOddDilationKernel {Y : ℝ} (hY : 0 ≤ Y) (g L : ℝ) {r : ℝ → ℂ}
    (hr : Measurable r) {C : ℝ} (hC : ∀ x, ‖r x‖ ≤ C) :
    MemLp (realOddDilationKernel Y g L r) 2 (volume.prod volume) := by
  have hS := memLp_realBandKernel hY
  have hSc : Continuous fun x : ℝ ↦ (realBandKernel Y x : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_realBandKernel Y)
  have h1 := memLp_cutLeft_comp_sub measurableSet_Icc (volume_Icc_neg_self_ne_top L) hSc hS
    (ℓ := fun z ↦ z / g) (by fun_prop)
  have h2 := memLp_cutLeft_comp_sub measurableSet_Icc (volume_Icc_neg_self_ne_top L) hSc hS
    (ℓ := fun z ↦ -(z / g)) (by fun_prop)
  have h := (h1.const_mul (((√g)⁻¹ / 2 : ℝ) : ℂ)).sub (h2.const_mul (((√g)⁻¹ / 2 : ℝ) : ℂ))
  have hbase : MemLp (fun p : ℝ × ℝ ↦ (Icc (-L) L).indicator (fun _ ↦ (1 : ℂ)) p.1 *
      (((√g)⁻¹ * realOddBandKernel Y (p.1 / g) p.2 : ℝ) : ℂ)) 2 (volume.prod volume) := by
    refine (memLp_congr_ae (Eventually.of_forall fun p ↦ ?_)).mp h
    simp only [Pi.sub_apply, realOddBandKernel]
    rw [show -(p.1 / g) - p.2 = -(p.1 / g + p.2) by ring, realBandKernel_neg]
    by_cases hp : p.1 ∈ Icc (-L) L
    · simp only [hp, indicator_of_mem, one_mul]
      push_cast
      ring
    · simp [hp]
  have hmeas : AEStronglyMeasurable (realOddDilationKernel Y g L r) (volume.prod volume) := by
    have hk : Measurable fun p : ℝ × ℝ ↦
        (((√g)⁻¹ * realOddBandKernel Y (p.1 / g) p.2 : ℝ) : ℂ) :=
      (Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_realOddBandKernel_div Y g))).measurable
    exact (((measurable_const.indicator measurableSet_Icc).comp measurable_fst).mul
      ((hr.comp measurable_fst).mul hk)).aestronglyMeasurable
  refine MemLp.of_le_mul (c := C) hbase hmeas (Eventually.of_forall fun p ↦ ?_)
  rw [realOddDilationKernel, norm_mul, norm_mul, norm_mul]
  calc ‖(Icc (-L) L).indicator (fun _ ↦ (1 : ℂ)) p.1‖ *
        (‖r p.1‖ * ‖(((√g)⁻¹ * realOddBandKernel Y (p.1 / g) p.2 : ℝ) : ℂ)‖)
      ≤ ‖(Icc (-L) L).indicator (fun _ ↦ (1 : ℂ)) p.1‖ *
        (C * ‖(((√g)⁻¹ * realOddBandKernel Y (p.1 / g) p.2 : ℝ) : ℂ)‖) := by
        gcongr
        exact hC p.1
    _ = C * (‖(Icc (-L) L).indicator (fun _ ↦ (1 : ℂ)) p.1‖ *
        ‖(((√g)⁻¹ * realOddBandKernel Y (p.1 / g) p.2 : ℝ) : ℂ)‖) := by ring

/-! ### The two kernel operators and the compression -/

/-- The first kernel operator, applied to a vector: the projection onto the odd band of its
cutoff. -/
theorem integralKernelOperator_realOddCutKernel_apply {Y : ℝ} (hY : 0 < Y) (L : ℝ) (f : H) :
    (integralKernelOperator volume
      (MemLp.toLp (realOddCutKernel Y L) (memLp_realOddCutKernel hY.le L))).val f =
      (realOddBand Y).starProjection (realCutoffVector L f) := by
  refine Lp.ext ?_
  have happ := integralKernelOperator_apply volume
    (MemLp.toLp (realOddCutKernel Y L) (memLp_realOddCutKernel hY.le L)) f
  have hker := Measure.ae_ae_of_ae_prod (memLp_realOddCutKernel hY.le L).coeFn_toLp
  have hproj := starProjection_realOddBand_ae hY (realCutoffVector L f)
  filter_upwards [happ, hker, hproj] with x h1 h2 h3
  rw [h1.2, h3]
  refine integral_congr_ae ?_
  filter_upwards [h2, coeFn_realCutoffVector L f] with y e1 e2
  rw [e1, e2, realOddCutKernel]
  by_cases hy : y ∈ Icc (-L) L <;> simp [hy]

/-- The second kernel operator, applied to a vector: the cutoff of the product with `r` of the
dilate of its projection onto the odd band. -/
theorem integralKernelOperator_realOddDilationKernel_apply {Y : ℝ} (hY : 0 < Y) {g : ℝ}
    (hg : 0 < g) (L : ℝ) {r : ℝ → ℂ} (hr : Measurable r) {C : ℝ} (hC : ∀ x, ‖r x‖ ≤ C)
    (f : H) :
    ((integralKernelOperator volume
      (MemLp.toLp (realOddDilationKernel Y g L r)
        (memLp_realOddDilationKernel hY.le g L hr hC))).val f : ℝ → ℂ) =ᵐ[volume] fun z ↦
      (Icc (-L) L).indicator (fun _ ↦ (1 : ℂ)) z *
        (r z * ((((√g)⁻¹ : ℝ) : ℂ) * ((realOddBand Y).starProjection f : H) (z / g))) := by
  have happ := integralKernelOperator_apply volume
    (MemLp.toLp (realOddDilationKernel Y g L r)
      (memLp_realOddDilationKernel hY.le g L hr hC)) f
  have hker := Measure.ae_ae_of_ae_prod
    (memLp_realOddDilationKernel hY.le g L hr hC).coeFn_toLp
  have hproj := (quasiMeasurePreserving_div_const_real hg).ae
    (starProjection_realOddBand_ae hY f)
  filter_upwards [happ, hker, hproj] with z h1 h2 h3
  rw [h1.2, h3, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [h2] with y e
  rw [e, realOddDilationKernel]
  push_cast
  ring

/-- Paper: Theorem 12.4.1.1, Step III, pp. 515–517. **The first kernel operator is the
projection onto the odd band after the cutoff**, `P_o ∘ M_L`.
Reconstruction: stated for the odd band of the rational real-place model, the image of the
weighted band under multiplication by `μ`. -/
theorem integralKernelOperator_realOddCutKernel {Y : ℝ} (hY : 0 < Y) (L : ℝ) :
    (integralKernelOperator volume
      (MemLp.toLp (realOddCutKernel Y L) (memLp_realOddCutKernel hY.le L))).val =
      (realOddBand Y).starProjection ∘L realCutoff L :=
  ContinuousLinearMap.ext fun f ↦ integralKernelOperator_realOddCutKernel_apply hY L f

/-- Paper: Theorem 12.4.1.1, Step III, pp. 515–517. **The second kernel operator is the cutoff
after the multiplier after the dilation after the projection onto the odd band**,
`M_L ∘ M_r ∘ D_g ∘ P_o`.
Reconstruction: stated for the odd band of the rational real-place model, with an arbitrary
bounded measurable multiplier `r`. -/
theorem integralKernelOperator_realOddDilationKernel {Y : ℝ} (hY : 0 < Y) {g : ℝ}
    (hg : 0 < g) (L : ℝ) {r : ℝ → ℂ} (hr : Measurable r) {C : ℝ} (hC : ∀ x, ‖r x‖ ≤ C) :
    (integralKernelOperator volume
      (MemLp.toLp (realOddDilationKernel Y g L r)
        (memLp_realOddDilationKernel hY.le g L hr hC))).val =
      realCutoff L ∘L realMultiplier r ∘L realDilation g ∘L
        (realOddBand Y).starProjection := by
  ext1 f
  refine Lp.ext ?_
  have hD := coeFn_realDilation hg ((realOddBand Y).starProjection f)
  have hM := coeFn_realMultiplier hr hC (realDilation g ((realOddBand Y).starProjection f))
  filter_upwards [integralKernelOperator_realOddDilationKernel_apply hY hg L hr hC f,
    coeFn_realCutoff L (realMultiplier r (realDilation g ((realOddBand Y).starProjection f))),
    hM, hD] with z h1 h2 h3 h4
  rw [h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, h2]
  by_cases hz : z ∈ Icc (-L) L
  · rw [indicator_of_mem hz, indicator_of_mem hz, h3, h4, one_mul]
  · rw [indicator_of_notMem hz, indicator_of_notMem hz, zero_mul]

/-- The compression `P_o ∘ M_L ∘ M_r ∘ D_g ∘ P_o` to the odd band is the composite of the two
kernel operators. -/
theorem realOddBand_compression_eq {Y g : ℝ} (hY : 0 < Y) (hg : 0 < g) (L : ℝ) {r : ℝ → ℂ}
    (hr : Measurable r) {C : ℝ} (hC : ∀ x, ‖r x‖ ≤ C) :
    (realOddBand Y).starProjection ∘L realCutoff L ∘L realMultiplier r ∘L realDilation g ∘L
        (realOddBand Y).starProjection =
      (integralKernelOperator volume
        (MemLp.toLp (realOddCutKernel Y L) (memLp_realOddCutKernel hY.le L))).val.comp
      (integralKernelOperator volume
        (MemLp.toLp (realOddDilationKernel Y g L r)
          (memLp_realOddDilationKernel hY.le g L hr hC))).val := by
  rw [integralKernelOperator_realOddCutKernel hY L,
    integralKernelOperator_realOddDilationKernel hY hg L hr hC]
  ext1 f
  simp only [ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.comp_apply (realCutoff L) (realCutoff L),
    realCutoff_comp_realCutoff]

/-- The compression `P_o ∘ M_L ∘ M_r ∘ D_g ∘ P_o` to the odd band is nuclear. -/
theorem isNuclearOperator_realOddBand_compression {Y g : ℝ} (hY : 0 < Y) (hg : 0 < g) (L : ℝ)
    {r : ℝ → ℂ} (hr : Measurable r) {C : ℝ} (hC : ∀ x, ‖r x‖ ≤ C) :
    IsNuclearOperator ((realOddBand Y).starProjection ∘L realCutoff L ∘L realMultiplier r ∘L
      realDilation g ∘L (realOddBand Y).starProjection) := by
  rw [realOddBand_compression_eq hY hg L hr hC]
  exact nuclear_hilbertSchmidt_comp _ _

/-- Paper: Theorem 12.4.1.1, Step III, pp. 515–517. **The trace of the compression to the odd
band.** With `P_o` the orthogonal projection onto the odd band, `M_L` the sharp spatial cutoff,
`M_r` the multiplication by a bounded measurable `r` and `D_g` the unitary dilation, the Hilbert
trace of `P_o ∘ M_L ∘ M_r ∘ D_g ∘ P_o` is `g^(-1/2) ∫ z in -L..L, r z * K_o (z / g, z)`, at
every `Y > 0`, `g > 0` and `L ≥ 0`.
Reconstruction: the odd band of the rational real-place model, with the sharp spatial cutoff
and no lower cutoff. For `r = weightedDilationMultiplier g` this is the weighted band before
the rank-one correction at `ζ`. -/
theorem hilbertTrace_realOddBand_compression_eq {Y g : ℝ} (hY : 0 < Y) (hg : 0 < g) {L : ℝ}
    (hL : 0 ≤ L) {r : ℝ → ℂ} (hr : Measurable r) {C : ℝ} (hC : ∀ x, ‖r x‖ ≤ C) :
    hilbertTrace ⟨(realOddBand Y).starProjection ∘L realCutoff L ∘L realMultiplier r ∘L
        realDilation g ∘L (realOddBand Y).starProjection,
        isNuclearOperator_realOddBand_compression hY hg L hr hC⟩ =
      (((√g)⁻¹ : ℝ) : ℂ) * ∫ z in (-L)..L, r z * (realOddBandKernel Y (z / g) z : ℂ) := by
  have hsub : (⟨(realOddBand Y).starProjection ∘L realCutoff L ∘L realMultiplier r ∘L
        realDilation g ∘L (realOddBand Y).starProjection,
        isNuclearOperator_realOddBand_compression hY hg L hr hC⟩ :
        nuclearEndomorphisms H) =
      ⟨(integralKernelOperator volume
        (MemLp.toLp (realOddCutKernel Y L) (memLp_realOddCutKernel hY.le L))).val.comp
      (integralKernelOperator volume
        (MemLp.toLp (realOddDilationKernel Y g L r)
          (memLp_realOddDilationKernel hY.le g L hr hC))).val,
      nuclear_hilbertSchmidt_comp _ _⟩ :=
    Subtype.ext (realOddBand_compression_eq hY hg L hr hC)
  rw [hsub, hilbertTrace_integralKernelOperator_comp]
  have ha := (memLp_realOddCutKernel hY.le L).coeFn_toLp
  have hb := (memLp_realOddDilationKernel hY.le g L hr hC).coeFn_toLp
  have hbs := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)
    ).quasiMeasurePreserving.ae_eq_comp hb
  have heq : (fun p : ℝ × ℝ ↦
      MemLp.toLp (realOddCutKernel Y L) (memLp_realOddCutKernel hY.le L) p *
        MemLp.toLp (realOddDilationKernel Y g L r)
          (memLp_realOddDilationKernel hY.le g L hr hC) p.swap) =ᵐ[volume.prod volume]
      fun p ↦ realOddCutKernel Y L p * realOddDilationKernel Y g L r p.swap := by
    filter_upwards [ha, hbs] with p hpa hpb
    rw [hpa]
    rw [show MemLp.toLp (realOddDilationKernel Y g L r)
      (memLp_realOddDilationKernel hY.le g L hr hC) p.swap = _ from hpb]
    rfl
  rw [integral_congr_ae heq]
  have hint : Integrable
      (fun p : ℝ × ℝ ↦ realOddCutKernel Y L p * realOddDilationKernel Y g L r p.swap)
      (volume.prod volume) :=
    (memLp_realOddCutKernel hY.le L).integrable_mul
      ((memLp_realOddDilationKernel hY.le g L hr hC).comp_measurePreserving
        (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)))
  rw [integral_prod_symm _ hint]
  have hin (z : ℝ) : ∫ x, realOddCutKernel Y L (x, z) *
      realOddDilationKernel Y g L r (Prod.swap (x, z)) =
      (Icc (-L) L).indicator
        (fun z ↦ (((√g)⁻¹ : ℝ) : ℂ) * (r z * (realOddBandKernel Y (z / g) z : ℂ))) z := by
    by_cases h : z ∈ Icc (-L) L
    · simp only [realOddCutKernel, realOddDilationKernel, Prod.swap, h, indicator_of_mem,
        mul_one, one_mul]
      have hc : ∀ x : ℝ, (realOddBandKernel Y x z : ℂ) *
          (r z * (((√g)⁻¹ * realOddBandKernel Y (z / g) x : ℝ) : ℂ)) =
          (((√g)⁻¹ : ℝ) : ℂ) * r z *
            ((realOddBandKernel Y x z * realOddBandKernel Y (z / g) x : ℝ) : ℂ) :=
        fun x ↦ by
          push_cast
          ring
      simp_rw [hc]
      rw [integral_const_mul, integral_complex_ofReal,
        integral_realOddBandKernel_mul_realOddBandKernel hY.le]
      ring
    · simp [realOddCutKernel, realOddDilationKernel, h]
  simp_rw [hin]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -L ≤ L),
    intervalIntegral.integral_const_mul]

end RiemannMasullo
