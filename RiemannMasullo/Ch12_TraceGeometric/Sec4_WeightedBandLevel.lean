module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedBandBridge
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelClosure

/-! # The level of the weighted model: the traces tend to `V_∞ - L₋ - L₊`

Paper: Theorem 12.4.1.1, pp. 514–519, and the value used on p. 520.

The weight is `w x = x ^ 2 + x ^ (-2)`. On the weighted space `L²(ℝ, w dx)` the integral
`f ↦ ∫ f` is a continuous functional, so the functions of the weighted band with integral zero
form a closed subspace `weightedLevel Y`. In the unweighted model that condition is lost in the
closure (`exists_mem_realPWLevel_integral_ne_zero`), and the limit of the traces is
`V_∞ - L₋`. This file proves that on `weightedLevel Y` the limit is `V_∞ - L₋ - L₊`, the value
that p. 520 uses.

* `hilbertTrace_compression_of_unitary`: the trace of a compression is invariant under a
  unitary.
* `realDilation_mem_realPWLevel`, `weightedBandDilation_mem`, `weightedPWDilation_mem`: the
  dilation by `g ≥ 1` preserves the level of the project, the weighted band, and its
  Paley–Wiener picture.
* `weightedIntegralVector`, `inner_weightedIntegralVector_weightedPWDilation`: in the
  Paley–Wiener picture the integral is the pairing with the class of `1 / conj μ`, and it is an
  eigenfunctional of the dilation with eigenvalue `√g`.
* `weightedLevelVector_ne_zero`: the integral does not vanish on the weighted band.
* `weightedLevel Y`, `mem_weightedLevel_iff`: the level, the functions of the weighted band with
  `∫ f = 0`.
* `tendsto_hilbertTrace_weightedLevel_compression`: **on the weighted space, with `P` the
  projection onto the level, the Hilbert trace of `P ∘ M_L ∘ D_g ∘ P` tends to
  `g ^ (3/2) / (g ^ 2 - 1) - g ^ (-1/2) - g ^ (1/2)` as `L → ∞`, at every fixed `Y > 0` and
  `g > 1`.**

The proof removes one more line: the level is the weighted band less the line of the vector
`e` that represents the integral, the rank-one term is `⟪e, M_L R_g e⟫ / ‖e‖ ^ 2`, and its
limit is `√g` because the integral is an eigenfunctional and the dilation preserves the band.

**Not formalized.** One weight, `x ^ 2 + x ^ (-2)`, which is not the logarithmic weight of the
paper. One dilation `g > 1` at a time, with no average against a test function. The sharp
cutoff. The rational field with no finite place.
-/

open MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate InnerProductSpace ENNReal NNReal SchwartzMap

@[expose] public noncomputable section

namespace RiemannMasullo

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)
local notation "Hw" => Lp ℂ 2 weightedBandMeasure

/-! ### Transport of the trace of a compression along a unitary -/

section Transport

variable {W E : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A unitary that carries a subspace `K` onto `K'` carries the orthogonal projection onto `K`
to the orthogonal projection onto `K'`. -/
theorem unitary_map_starProjection (U : W ≃ₗᵢ[ℂ] E) (K : Submodule ℂ W)
    [K.HasOrthogonalProjection] (K' : Submodule ℂ E) [K'.HasOrthogonalProjection]
    (hmap : K.map U.toLinearIsometry.toLinearMap = K') (f : W) :
    U (K.starProjection f) = K'.starProjection (U f) := by
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · rw [← hmap]
    exact Submodule.mem_map_of_mem (Submodule.starProjection_apply_mem K f)
  · intro w hw
    rw [← hmap] at hw
    obtain ⟨k, hk, rfl⟩ := hw
    rw [← map_sub]
    change ⟪U (f - K.starProjection f), U k⟫_ℂ = 0
    rw [LinearIsometryEquiv.inner_map_map]
    exact Submodule.starProjection_inner_eq_zero f k hk

/-- **The trace of a compression is invariant under a unitary.** If the unitary `U` carries `K`
onto `K'` and intertwines `S` with `T`, and the compression of `T` to `K'` is nuclear, then
the compression of `S` to `K` is nuclear with the same Hilbert trace. -/
theorem hilbertTrace_compression_of_unitary (U : W ≃ₗᵢ[ℂ] E) (K : Submodule ℂ W)
    [K.HasOrthogonalProjection] (K' : Submodule ℂ E) [K'.HasOrthogonalProjection]
    (hmap : K.map U.toLinearIsometry.toLinearMap = K') (S : W →L[ℂ] W) (T : E →L[ℂ] E)
    (hST : ∀ f, U (S f) = T (U f))
    (hn : IsNuclearOperator (K'.starProjection ∘L T ∘L K'.starProjection)) :
    ∃ hn' : IsNuclearOperator (K.starProjection ∘L S ∘L K.starProjection),
      hilbertTrace ⟨_, hn'⟩ = hilbertTrace ⟨_, hn⟩ := by
  have hint : U.toLinearIsometry.toContinuousLinearMap ∘L
      (K.starProjection ∘L S ∘L K.starProjection) =
      (K'.starProjection ∘L T ∘L K'.starProjection) ∘L
        U.toLinearIsometry.toContinuousLinearMap := by
    ext1 f
    change U (K.starProjection (S (K.starProjection f))) =
      K'.starProjection (T (K'.starProjection (U f)))
    rw [unitary_map_starProjection U K K' hmap, hST, unitary_map_starProjection U K K' hmap]
  have h0 : ContinuousLinearMap.adjoint U.toLinearIsometry.toContinuousLinearMap ∘L
      U.toLinearIsometry.toContinuousLinearMap = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp U.toLinearIsometry.norm_map
  have hUU : U.toLinearIsometry.toContinuousLinearMap ∘L
      ContinuousLinearMap.adjoint U.toLinearIsometry.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ E := by
    ext1 y
    obtain ⟨f, rfl⟩ := U.surjective y
    have h1 : ContinuousLinearMap.adjoint U.toLinearIsometry.toContinuousLinearMap
        (U.toLinearIsometry.toContinuousLinearMap f) = f :=
      congrArg (fun A : W →L[ℂ] W ↦ A f) h0
    change U.toLinearIsometry.toContinuousLinearMap
      (ContinuousLinearMap.adjoint U.toLinearIsometry.toContinuousLinearMap
        (U.toLinearIsometry.toContinuousLinearMap f)) = _
    rw [h1]
    rfl
  have hrange : U.toLinearIsometry.toContinuousLinearMap ∘L
      (ContinuousLinearMap.adjoint U.toLinearIsometry.toContinuousLinearMap ∘L
        (K'.starProjection ∘L T ∘L K'.starProjection)) =
      K'.starProjection ∘L T ∘L K'.starProjection := by
    rw [← ContinuousLinearMap.comp_assoc, hUU, ContinuousLinearMap.id_comp]
  have h := hilbertTrace_eq_of_isometry_intertwining U.toLinearIsometry
    ⟨K'.starProjection ∘L T ∘L K'.starProjection, hn⟩
    (K.starProjection ∘L S ∘L K.starProjection) hint hrange
  obtain ⟨hS, htr⟩ := h
  exact ⟨hS, htr⟩

end Transport

/-! ### The frequency data of a function of the level -/

/-- A function of the level is the Fourier transform of even data supported in the band with
integral zero. -/
theorem exists_level_data {Y : ℝ} {F : H} (hF : F ∈ realPWLevel Y) :
    ∃ b : ℝ → ℂ, Integrable b ∧ ∃ hb : MemLp b 2, (∀ ξ, ξ ∉ Icc (-Y) Y → b ξ = 0) ∧
      (∀ ξ, b (-ξ) = b ξ) ∧ bandLaplace b 0 = 0 ∧ F = (𝓕 (hb.toLp b) : H) := by
  obtain ⟨hout, heven, hint⟩ := mem_realPWLevelFourier_iff.mp (mem_realPWLevel_iff.mp hF)
  have heven' : ∀ᵐ ξ, ((𝓕 F : H) : ℝ → ℂ) (-ξ) = 1 * ((𝓕 F : H) : ℝ → ℂ) ξ :=
    heven.mono fun ξ e ↦ by rw [e, one_mul]
  obtain ⟨b, hb1, hb2, hsupp, hbeven, hFb⟩ :=
    exists_band_data_of_parity (σ := 1) (by norm_num) hout heven'
  have hmem : ∀ ξ : ℝ, -ξ ∈ Icc (-Y) Y ↔ ξ ∈ Icc (-Y) Y := fun ξ ↦ by
    constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩
  refine ⟨b, hb1, hb2, hsupp, fun ξ ↦ by rw [hbeven, one_mul], ?_, hFb⟩
  have hco : ((𝓕 F : H) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦ b (-ξ) := by
    rw [hFb]
    exact coeFn_fourier_fourier_toLp hb2
  rw [bandLaplace_zero, ← integral_neg_eq_self b volume, ← hint,
    setIntegral_congr_ae measurableSet_Icc (hco.mono fun ξ e _ ↦ e),
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun ξ hξ ↦ hsupp _ (mt (hmem ξ).mp hξ))]

/-- The Fourier transform of even data supported in the band with integral zero is a function
of the level. -/
theorem fourier_toLp_mem_realPWLevel {Y : ℝ} {b : ℝ → ℂ} (hb : MemLp b 2)
    (hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → b ξ = 0) (heven : ∀ ξ, b (-ξ) = b ξ)
    (hB0 : bandLaplace b 0 = 0) : (𝓕 (hb.toLp b) : H) ∈ realPWLevel Y := by
  have hmem : ∀ ξ : ℝ, -ξ ∈ Icc (-Y) Y ↔ ξ ∈ Icc (-Y) Y := fun ξ ↦ by
    constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩
  have hco := coeFn_fourier_fourier_toLp hb
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)
    ).quasiMeasurePreserving.ae_eq_comp hco
  rw [mem_realPWLevel_iff, mem_realPWLevelFourier_iff]
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hco] with ξ e hξ
    rw [e, hsupp _ (mt (hmem ξ).mp hξ)]
  · filter_upwards [hco, hneg] with ξ e1 e2
    have e3 : ((𝓕 (𝓕 (hb.toLp b) : H) : H) : ℝ → ℂ) (-ξ) = b (- -ξ) := e2
    rw [e3, e1, neg_neg, heven]
  · rw [setIntegral_congr_ae measurableSet_Icc (hco.mono fun ξ e _ ↦ e),
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun ξ hξ ↦ hsupp _ (mt (hmem ξ).mp hξ)),
      integral_neg_eq_self b volume, ← bandLaplace_zero, hB0]

/-- **The dilation by `g ≥ 1` preserves the level.** -/
theorem realDilation_mem_realPWLevel {Y g : ℝ} (hg : 1 ≤ g) {F : H} (hF : F ∈ realPWLevel Y) :
    realDilation g F ∈ realPWLevel Y := by
  have hg0 : 0 < g := by linarith
  obtain ⟨b, hb1, hb2, hsupp, heven, hB0, hFb⟩ := exists_level_data hF
  have hFa : (F : ℝ → ℂ) =ᵐ[volume] 𝓕 b := by
    have := fourier_ae_eq_fourier_toLp hb1 hb2
    rw [← hFb] at this
    exact this.symm
  have hsupp' : ∀ η, η ∉ Icc (-Y) Y → ((√g : ℝ) : ℂ) * b (g * η) = 0 := fun η hη ↦ by
    have : g * η ∉ Icc (-Y) Y := by
      intro h
      apply hη
      constructor
      · rcases le_or_gt 0 η with h0 | h0
        · linarith [h.1, h.2]
        · nlinarith [h.1]
      · rcases le_or_gt η 0 with h0 | h0
        · linarith [h.1, h.2]
        · nlinarith [h.2]
    rw [hsupp _ this, mul_zero]
  have hc1 : Integrable fun η : ℝ ↦ ((√g : ℝ) : ℂ) * b (g * η) :=
    (hb1.comp_mul_left' hg0.ne').const_mul _
  have hc2 : MemLp (fun η : ℝ ↦ ((√g : ℝ) : ℂ) * b (g * η)) 2 := by
    have hmp : MeasurePreserving (fun η : ℝ ↦ g * η) volume (ENNReal.ofReal g⁻¹ • volume) := by
      refine ⟨by fun_prop, ?_⟩
      rw [Real.map_volume_mul_left hg0.ne', abs_of_pos (inv_pos.mpr hg0)]
    exact ((hb2.smul_measure ENNReal.ofReal_ne_top).comp_measurePreserving hmp).const_mul _
  have hD : realDilation g F = (𝓕 (hc2.toLp _) : H) := by
    refine Lp.ext ?_
    have hk := (quasiMeasurePreserving_div_const_real hg0).ae_eq_comp hFa
    filter_upwards [coeFn_realDilation hg0 F, hk, fourier_ae_eq_fourier_toLp hc1 hc2]
      with x e1 e2 e3
    have e2' : (F : ℝ → ℂ) (x / g) = 𝓕 b (x / g) := e2
    rw [e1, e2', ← e3, fourier_sqrt_mul_comp_mul hg0]
  rw [hD]
  refine fourier_toLp_mem_realPWLevel hc2 hsupp' (fun ξ ↦ ?_) ?_
  · rw [mul_neg, heven]
  · have h := bandLaplace_sqrt_mul_comp_mul hg0 b 0
    rw [mul_zero] at h
    rw [h, hB0, mul_zero]

/-- The frequency data of `F / x` for a function `F` of the band that vanishes at the origin. -/
theorem exists_fourier_div_data {Y : ℝ} {b : ℝ → ℂ} (hb1 : Integrable b)
    (hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → b ξ = 0) (hB0 : bandLaplace b 0 = 0) :
    ∃ cu : ℝ → ℂ, Integrable cu ∧ ∃ _ : MemLp cu 2, (∀ ξ, ξ ∉ Icc (-Y) Y → cu ξ = 0) ∧
      ∀ x : ℝ, x ≠ 0 → 𝓕 cu x = 𝓕 b x / (x : ℂ) := by
  refine ⟨fun ξ ↦ 2 * π * Complex.I * bandPrimitive Y b 0 ξ,
    (integrable_bandPrimitive hb1 hsupp 0).const_mul _,
    (memLp_bandPrimitive hb1 hsupp 0).const_mul _, fun ξ hξ ↦ ?_, fun x hx ↦ ?_⟩
  · dsimp only
    rw [bandPrimitive_of_notMem hξ, mul_zero]
  · have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    have hs : -(Complex.I * (x : ℂ)) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero hxc)
    have e := bandLaplace_bandPrimitive hb1 hsupp (v := 0) (s := -(Complex.I * (x : ℂ))) hs
    rw [hB0, mul_zero, zero_sub, sub_zero, ← fourier_eq_bandLaplace b x] at e
    rw [fourier_eq_bandLaplace, bandLaplace_const_mul, eq_div_iff hxc]
    refine mul_left_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) ?_
    linear_combination Complex.I * e

/-! ### The dilation preserves the weighted band -/

/-- The dilation by `g ≥ 1` preserves the weighted band. -/
theorem weightedBandDilation_mem {Y g : ℝ} (hg : 1 ≤ g) {f : Hw} (hf : f ∈ weightedBand Y) :
    weightedBandDilation g f ∈ weightedBand Y := by
  have hg0 : 0 < g := by linarith
  rw [mem_weightedBand_iff] at hf ⊢
  have h : weightedBandInclusion (weightedBandDilation g f) =
      realDilation g (weightedBandInclusion f) := by
    refine Lp.ext ?_
    have hk := (quasiMeasurePreserving_div_const_real hg0).ae_eq_comp
      (coeFn_weightedBandInclusion f)
    filter_upwards [coeFn_weightedBandInclusion (weightedBandDilation g f),
      coeFn_weightedBandDilation hg f, coeFn_realDilation hg0 (weightedBandInclusion f), hk]
      with x e1 e2 e3 e4
    have e4' : (weightedBandInclusion f : ℝ → ℂ) (x / g) = (f : ℝ → ℂ) (x / g) := e4
    rw [e1, e2, e3, e4']
  rw [h]
  exact realDilation_mem_realPWLevel hg hf

/-- In the Paley–Wiener picture, the dilation with its multiplier preserves the odd functions of
the band that vanish at `ζ`, for `g ≥ 1`. -/
theorem weightedPWDilation_mem {Y g : ℝ} (hg : 1 ≤ g) {h : H} (hh : h ∈ weightedPWBand Y) :
    weightedPWDilation g h ∈ weightedPWBand Y := by
  rw [← weightedBand_map_weightedBandUnitary Y] at hh ⊢
  obtain ⟨f, hf, rfl⟩ := hh
  exact ⟨weightedBandDilation g f, weightedBandDilation_mem hg hf,
    weightedBandUnitary_weightedBandDilation g f⟩

/-! ### The integral as a functional -/

/-- The function `1 / conj μ` is square-integrable. -/
theorem memLp_conj_inv_weightedBandFactor :
    MemLp (fun x : ℝ ↦ conj (weightedBandFactor x)⁻¹) 2 volume := by
  have hmeas : Measurable fun x : ℝ ↦ conj (weightedBandFactor x)⁻¹ :=
    Complex.continuous_conj.measurable.comp measurable_weightedBandFactor.inv
  refine (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).mpr ?_
  refine (integrable_inv_one_add_sq.const_mul 2).mono'
    (hmeas.norm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), RCLike.norm_conj, norm_inv, inv_pow]
  by_cases hx : x = 0
  · subst hx
    simp [weightedBandFactor]
  · rw [norm_sq_weightedBandFactor hx, weightedBandWeight]
    have ht : 0 < x ^ 2 := by positivity
    have h1 : (x ^ 2 + (x ^ 2)⁻¹)⁻¹ = x ^ 2 / ((x ^ 2) ^ 2 + 1) := by
      field_simp
    rw [h1, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (x ^ 2 - 1)]

/-- The vector of `L²(ℝ)` that represents the integral of `h / μ`: the class of `1 / conj μ`. -/
def weightedIntegralVector : H := memLp_conj_inv_weightedBandFactor.toLp _

/-- The pairing with the integral vector is the integral of `h / μ`. -/
theorem inner_weightedIntegralVector (V : H) :
    ⟪weightedIntegralVector, V⟫_ℂ = ∫ x, (weightedBandFactor x)⁻¹ * (V : ℝ → ℂ) x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [memLp_conj_inv_weightedBandFactor.coeFn_toLp] with x hx
  rw [weightedIntegralVector, hx, RCLike.inner_apply, Complex.conj_conj, mul_comm]

/-- **The integral is an eigenfunctional of the dilation.** In the Paley–Wiener picture, the
integral of `(R_g V) / μ` is `√g` times the integral of `V / μ`. -/
theorem inner_weightedIntegralVector_weightedPWDilation {g : ℝ} (hg : 1 ≤ g) (V : H) :
    ⟪weightedIntegralVector, weightedPWDilation g V⟫_ℂ =
      ((√g : ℝ) : ℂ) * ⟪weightedIntegralVector, V⟫_ℂ := by
  have hg0 : 0 < g := by linarith
  rw [inner_weightedIntegralVector, inner_weightedIntegralVector]
  have h1 : ∫ x, (weightedBandFactor x)⁻¹ * (weightedPWDilation g V : ℝ → ℂ) x =
      ∫ x : ℝ, (((√g)⁻¹ : ℝ) : ℂ) *
        ((weightedBandFactor (g⁻¹ * x))⁻¹ * (V : ℝ → ℂ) (g⁻¹ * x)) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_weightedPWDilation hg V, coeFn_realDilation hg0 V, ae_ne_zero_real]
      with x e1 e2 hx
    have hxg : x / g ≠ 0 := div_ne_zero hx hg0.ne'
    have hr := weightedDilationMultiplier_mul_weightedBandFactor hg0.ne' hx
    have hμ := weightedBandFactor_ne_zero hx
    have hμg := weightedBandFactor_ne_zero hxg
    have hr0 : weightedDilationMultiplier g x ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hr
      exact hμ hr.symm
    have hinv : (weightedBandFactor x)⁻¹ * weightedDilationMultiplier g x =
        (weightedBandFactor (x / g))⁻¹ := by
      rw [← hr]
      field_simp
    rw [e1, e2, show g⁻¹ * x = x / g from inv_mul_eq_div g x, ← mul_assoc, hinv]
    ring
  rw [h1, integral_const_mul, Measure.integral_comp_inv_mul_left
    (fun y : ℝ ↦ (weightedBandFactor y)⁻¹ * (V : ℝ → ℂ) y) g, abs_of_pos hg0, Complex.real_smul,
    ← mul_assoc]
  congr 1
  have hs : (√g) ^ 2 = g := Real.sq_sqrt hg0.le
  have hs0 : √g ≠ 0 := (Real.sqrt_pos.mpr hg0).ne'
  rw [← Complex.ofReal_mul]
  congr 1
  field_simp
  rw [hs]

/-! ### The level in the Paley–Wiener picture -/

/-- The projection of the integral vector onto the weighted band, in the Paley–Wiener picture.
Pairing a function of that space with it gives the integral of `h / μ`. -/
def weightedLevelVector (Y : ℝ) : H := (weightedPWBand Y).starProjection weightedIntegralVector

/-- The level vector lies in the weighted band. -/
theorem weightedLevelVector_mem (Y : ℝ) : weightedLevelVector Y ∈ weightedPWBand Y :=
  Submodule.starProjection_apply_mem _ _

/-- On the weighted band the level vector pairs like the integral vector. -/
theorem inner_weightedLevelVector {Y : ℝ} {h : H} (hh : h ∈ weightedPWBand Y) :
    ⟪weightedLevelVector Y, h⟫_ℂ = ⟪weightedIntegralVector, h⟫_ℂ := by
  rw [weightedLevelVector, Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr hh]

/-- The level in the Paley–Wiener picture: the odd functions `h` of the band that vanish at `ζ`
and have `∫ h / μ = 0`. -/
def weightedPWLevel (Y : ℝ) : Submodule ℂ H :=
  weightedPWBand Y ⊓ (ℂ ∙ weightedLevelVector Y)ᗮ

/-- Membership in the level, in the Paley–Wiener picture. -/
theorem mem_weightedPWLevel_iff {Y : ℝ} {h : H} :
    h ∈ weightedPWLevel Y ↔ h ∈ weightedPWBand Y ∧ ⟪weightedIntegralVector, h⟫_ℂ = 0 := by
  rw [weightedPWLevel, Submodule.mem_inf, Submodule.mem_orthogonal_singleton_iff_inner_right]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [← inner_weightedLevelVector h1]; exact h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [inner_weightedLevelVector h1]; exact h2⟩

/-- The level is closed. -/
theorem isClosed_weightedPWLevel (Y : ℝ) : IsClosed (weightedPWLevel Y : Set H) :=
  (isClosed_weightedPWBand Y).inter (Submodule.isClosed_orthogonal _)

/-- The level is complete. -/
instance instCompleteSpaceWeightedPWLevel (Y : ℝ) : CompleteSpace (weightedPWLevel Y) :=
  (isClosed_weightedPWLevel Y).completeSpace_coe

/-- **The integral does not vanish on the weighted band.** The level vector is not zero: the
weighted band contains a function whose integral is not zero. -/
theorem weightedLevelVector_ne_zero {Y : ℝ} (hY : 0 < Y) : weightedLevelVector Y ≠ 0 := by
  obtain ⟨f, hfmem, hfint⟩ := exists_mem_realPWLevel_integral_ne_zero hY
  obtain ⟨b, hb1, hb2, hsupp, -, hB0, hFb⟩ := exists_level_data hfmem
  obtain ⟨cu, hcu1, hcu2, -, hupt⟩ := exists_fourier_div_data hb1 hsupp hB0
  have hga : Function.HasTemperateGrowth (fun x : ℝ ↦ (x : ℂ)) :=
    Complex.ofRealCLM.hasTemperateGrowth
  obtain ⟨h, hhdef⟩ : ∃ h : H, h =
      ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)) f).toLp 2 volume : H) -
        Complex.I • (𝓕 (hcu2.toLp cu) : H) := ⟨_, rfl⟩
  have hFa : ((f.toLp 2 volume : H) : ℝ → ℂ) =ᵐ[volume] f := f.coeFn_toLp 2 volume
  have hFb' : ((f.toLp 2 volume : H) : ℝ → ℂ) =ᵐ[volume] 𝓕 b := by
    have := fourier_ae_eq_fourier_toLp hb1 hb2
    rw [← hFb] at this
    exact this.symm
  have hha : ∀ᵐ x, (h : ℝ → ℂ) x =
      weightedBandFactor x * ((f.toLp 2 volume : H) : ℝ → ℂ) x := by
    rw [hhdef]
    filter_upwards [Lp.coeFn_sub ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)) f).toLp 2
        volume : H) (Complex.I • (𝓕 (hcu2.toLp cu) : H)),
      Lp.coeFn_smul Complex.I (𝓕 (hcu2.toLp cu) : H),
      (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)) f).coeFn_toLp 2 volume, hFa, hFb',
      fourier_ae_eq_fourier_toLp hcu1 hcu2, ae_ne_zero_real] with x e1 e2 e3 e4 e5 e6 hx
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    rw [e1, Pi.sub_apply, e2, Pi.smul_apply, e3, ← e6, hupt x hx, ← e5, e4,
      SchwartzMap.smulLeftCLM_apply_apply hga, weightedBandFactor, smul_eq_mul, smul_eq_mul]
    field_simp
  have hhN := mem_weightedPWBand_of_weightedBandFactor_mul hfmem hha
  have hpair : ⟪weightedIntegralVector, h⟫_ℂ = ∫ x, f x := by
    rw [inner_weightedIntegralVector]
    refine integral_congr_ae ?_
    filter_upwards [hha, hFa, ae_ne_zero_real] with x e1 e2 hx
    rw [e1, e2, ← mul_assoc, inv_mul_cancel₀ (weightedBandFactor_ne_zero hx), one_mul]
  intro he
  have h0 := inner_weightedLevelVector hhN
  rw [he, inner_zero_left, hpair] at h0
  exact hfint h0.symm

/-- The rank-one term of the level: `⟪e, R_g e⟫ = √g ⟪e, e⟫` for the level vector `e`. -/
theorem inner_weightedLevelVector_weightedPWDilation {Y g : ℝ} (hg : 1 ≤ g) :
    ⟪weightedLevelVector Y, weightedPWDilation g (weightedLevelVector Y)⟫_ℂ =
      ((√g : ℝ) : ℂ) * ⟪weightedLevelVector Y, weightedLevelVector Y⟫_ℂ := by
  rw [inner_weightedLevelVector (weightedPWDilation_mem hg (weightedLevelVector_mem Y)),
    inner_weightedIntegralVector_weightedPWDilation hg,
    inner_weightedLevelVector (weightedLevelVector_mem Y)]

private theorem hilbertTrace_weightedPWLevel_compression_aux {Y g : ℝ} (hY : 0 < Y)
    (hg : 1 < g) (L : ℝ) :
    ∃ hn : IsNuclearOperator ((weightedPWLevel Y).starProjection ∘L
        (realCutoff L ∘L weightedPWDilation g) ∘L (weightedPWLevel Y).starProjection),
      hilbertTrace ⟨_, hn⟩ =
        hilbertTrace ⟨_, isNuclearOperator_weightedPWBand_compression hY hg L⟩ -
          ⟪weightedLevelVector Y,
            realCutoff L (weightedPWDilation g (weightedLevelVector Y))⟫_ℂ /
            (‖weightedLevelVector Y‖ : ℂ) ^ 2 := by
  have hinst : (weightedPWBand Y ⊓ (ℂ ∙ weightedLevelVector Y)ᗮ).HasOrthogonalProjection :=
    inferInstanceAs (weightedPWLevel Y).HasOrthogonalProjection
  have hmain := hilbertTrace_compression_inf_orthogonal_span_singleton
    (weightedLevelVector_mem Y) (weightedLevelVector_ne_zero hY)
    (realCutoff L ∘L weightedPWDilation g) (isNuclearOperator_weightedPWBand_compression hY hg L)
  obtain ⟨hn', htr'⟩ := hmain
  exact ⟨hn', htr'⟩

/-- The compression of the cutoff dilation to the level, in the Paley–Wiener picture, is
nuclear. -/
theorem isNuclearOperator_weightedPWLevel_compression {Y g : ℝ} (hY : 0 < Y) (hg : 1 < g)
    (L : ℝ) :
    IsNuclearOperator ((weightedPWLevel Y).starProjection ∘L
      (realCutoff L ∘L weightedPWDilation g) ∘L (weightedPWLevel Y).starProjection) :=
  (hilbertTrace_weightedPWLevel_compression_aux hY hg L).choose

/-- **The trace over the level, in the Paley–Wiener picture, tends to `V_∞ - L₋ - L₊`.** -/
theorem tendsto_hilbertTrace_weightedPWLevel_compression {Y g : ℝ} (hY : 0 < Y) (hg : 1 < g) :
    Tendsto (fun L : ℝ ↦
        hilbertTrace ⟨_, isNuclearOperator_weightedPWLevel_compression hY hg L⟩) atTop
      (𝓝 (((g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) - (√g)⁻¹ - √g : ℝ) : ℂ))) := by
  have h1 := tendsto_hilbertTrace_weightedPWBand_compression hY hg
  have h2 := tendsto_inner_realCutoff (weightedLevelVector Y)
    (weightedPWDilation g (weightedLevelVector Y))
  have hk0 : (‖weightedLevelVector Y‖ : ℂ) ^ 2 ≠ 0 := by
    have : (‖weightedLevelVector Y‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_pos_iff.mpr (weightedLevelVector_ne_zero hY)).ne'
    exact pow_ne_zero 2 this
  have hkk : ⟪weightedLevelVector Y, weightedLevelVector Y⟫_ℂ =
      (‖weightedLevelVector Y‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
  rw [inner_weightedLevelVector_weightedPWDilation hg.le, hkk] at h2
  have h3 := h1.sub (h2.div_const ((‖weightedLevelVector Y‖ : ℂ) ^ 2))
  have h4 : Tendsto (fun L : ℝ ↦
      hilbertTrace ⟨_, isNuclearOperator_weightedPWBand_compression hY hg L⟩ -
        ⟪weightedLevelVector Y,
          realCutoff L (weightedPWDilation g (weightedLevelVector Y))⟫_ℂ /
          (‖weightedLevelVector Y‖ : ℂ) ^ 2) atTop
      (𝓝 (((g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) - (√g)⁻¹ - √g : ℝ) : ℂ))) := by
    convert h3 using 2
    rw [mul_div_assoc, div_self, mul_one]
    · push_cast
      ring
    · exact hk0
  refine h4.congr fun L ↦ ?_
  exact (hilbertTrace_weightedPWLevel_compression_aux hY hg L).choose_spec.symm

/-! ### The level on the weighted space -/

/-- The integral `f ↦ ∫ f` as a continuous functional on the weighted space. -/
def weightedIntegralFunctional : Hw →L[ℂ] ℂ :=
  innerSL ℂ weightedIntegralVector ∘L weightedBandUnitary.toLinearIsometry.toContinuousLinearMap

/-- The functional is the integral against Lebesgue measure. -/
theorem weightedIntegralFunctional_apply (f : Hw) :
    weightedIntegralFunctional f = ∫ x, (f : ℝ → ℂ) x := by
  change ⟪weightedIntegralVector, weightedBandUnitary f⟫_ℂ = _
  rw [inner_weightedIntegralVector]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_weightedBandUnitary f, ae_ne_zero_real] with x e hx
  rw [e, ← mul_assoc, inv_mul_cancel₀ (weightedBandFactor_ne_zero hx), one_mul]

/-- Paper: Definition 11.2.1.1, pp. 487–488. The level of the weighted model: the functions of
the weighted band with integral zero. The weight makes the integral continuous, so this
condition, which the closure loses in the unweighted model
(`exists_mem_realPWLevel_integral_ne_zero`), defines a closed subspace here. -/
def weightedLevel (Y : ℝ) : Submodule ℂ Hw :=
  weightedBand Y ⊓ LinearMap.ker weightedIntegralFunctional.toLinearMap

/-- Membership in the level of the weighted model. -/
theorem mem_weightedLevel_iff {Y : ℝ} {f : Hw} :
    f ∈ weightedLevel Y ↔ f ∈ weightedBand Y ∧ ∫ x, (f : ℝ → ℂ) x = 0 := by
  rw [weightedLevel, Submodule.mem_inf, LinearMap.mem_ker, ← weightedIntegralFunctional_apply]
  rfl

/-- The level of the weighted model is closed. -/
theorem isClosed_weightedLevel (Y : ℝ) : IsClosed (weightedLevel Y : Set Hw) :=
  (isClosed_weightedBand Y).inter
    (isClosed_singleton.preimage weightedIntegralFunctional.continuous)

/-- The level of the weighted model is complete. -/
instance instCompleteSpaceWeightedLevel (Y : ℝ) : CompleteSpace (weightedLevel Y) :=
  (isClosed_weightedLevel Y).completeSpace_coe

/-- The unitary carries the level of the weighted model onto the level in the Paley–Wiener
picture. -/
theorem weightedLevel_map_weightedBandUnitary (Y : ℝ) :
    (weightedLevel Y).map weightedBandUnitary.toLinearIsometry.toLinearMap =
      weightedPWLevel Y := by
  ext h
  rw [Submodule.mem_map, mem_weightedPWLevel_iff, ← weightedBand_map_weightedBandUnitary Y]
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨hf1, hf2⟩ := Submodule.mem_inf.mp hf
    exact ⟨Submodule.mem_map_of_mem hf1, LinearMap.mem_ker.mp hf2⟩
  · rintro ⟨⟨f, hf, rfl⟩, h2⟩
    exact ⟨f, Submodule.mem_inf.mpr ⟨hf, LinearMap.mem_ker.mpr h2⟩, rfl⟩

private theorem hilbertTrace_weightedLevel_compression_aux {Y g : ℝ} (hY : 0 < Y) (hg : 1 < g)
    (L : ℝ) :
    ∃ hn : IsNuclearOperator ((weightedLevel Y).starProjection ∘L
        (weightedBandCutoff L ∘L weightedBandDilation g) ∘L (weightedLevel Y).starProjection),
      hilbertTrace ⟨_, hn⟩ =
        hilbertTrace ⟨_, isNuclearOperator_weightedPWLevel_compression hY hg L⟩ :=
  hilbertTrace_compression_of_unitary weightedBandUnitary (weightedLevel Y) (weightedPWLevel Y)
    (weightedLevel_map_weightedBandUnitary Y) (weightedBandCutoff L ∘L weightedBandDilation g)
    (realCutoff L ∘L weightedPWDilation g)
    (fun f ↦ by
      change weightedBandUnitary (weightedBandCutoff L (weightedBandDilation g f)) =
        realCutoff L (weightedPWDilation g (weightedBandUnitary f))
      rw [weightedBandUnitary_weightedBandCutoff, weightedBandUnitary_weightedBandDilation])
    (isNuclearOperator_weightedPWLevel_compression hY hg L)

/-- The compression of the cutoff dilation to the level of the weighted model is nuclear. -/
theorem isNuclearOperator_weightedLevel_compression {Y g : ℝ} (hY : 0 < Y) (hg : 1 < g)
    (L : ℝ) :
    IsNuclearOperator ((weightedLevel Y).starProjection ∘L
      (weightedBandCutoff L ∘L weightedBandDilation g) ∘L (weightedLevel Y).starProjection) :=
  (hilbertTrace_weightedLevel_compression_aux hY hg L).choose

/-- Paper: Theorem 12.4.1.1, pp. 514–519, and the value used on p. 520. **On the level of the
weighted model the traces tend to `V_∞ - L₋ - L₊`.** Let `w x = x ^ 2 + x ^ (-2)`, let `P` be the
orthogonal projection of `L²(ℝ, w dx)` onto the functions of the level `realPWLevel Y` that
have finite weighted norm and integral zero, `M_L` the multiplication by `1_[-L, L]`, and `D_g`
the dilation `f ↦ g^(-1/2) f (x / g)`. Then `P ∘ M_L ∘ D_g ∘ P` is nuclear and its Hilbert trace
tends to `g ^ (3/2) / (g ^ 2 - 1) - g ^ (-1/2) - g ^ (1/2)` as `L → ∞`, for every fixed `Y > 0`
and every `g > 1`. This is the value that p. 520 uses: the real-place term minus both pole
terms.
Reconstruction: the rational real-place model at order zero, with this weight in place of the
logarithmic weight of the paper, the sharp spatial cutoff, and a single dilation. In the
unweighted model the level is the band less one line and the limit is `V_∞ - L₋`
(`tendsto_hilbertTrace_realPWLevel_compression_eq`): the term `L₊` is absent there because the
condition `∫ f = 0` does not survive the closure. -/
theorem tendsto_hilbertTrace_weightedLevel_compression {Y g : ℝ} (hY : 0 < Y) (hg : 1 < g) :
    Tendsto (fun L : ℝ ↦
        hilbertTrace ⟨_, isNuclearOperator_weightedLevel_compression hY hg L⟩) atTop
      (𝓝 (((g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) - (√g)⁻¹ - √g : ℝ) : ℂ))) := by
  refine (tendsto_hilbertTrace_weightedPWLevel_compression hY hg).congr fun L ↦ ?_
  exact (hilbertTrace_weightedLevel_compression_aux hY hg L).choose_spec.symm

end RiemannMasullo
