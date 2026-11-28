module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedBandTrace

/-! # Division and multiplication by `x - p` on the band

Paper: Theorem 12.4.1.1, pp. 514–519, and the value used on p. 520.

The identification of the weighted band with its Paley–Wiener picture
(`Sec4_WeightedBandBridge`) needs two facts about the functions of `L²(ℝ)` whose Fourier
transform vanishes outside `[-Y, Y]`: such a function that vanishes at a point `p` can be
divided by `x - p` inside the band, and if `x F (x)` is square-integrable then it is again in
the band. Both are proved here on the frequency side, with explicit frequency data and no
complex analysis.

* `exists_band_data_of_parity`, `exists_band_data`: a function of the band is the Fourier
  transform of data `b` that vanishes outside the band at every point, with the same parity.
* `bandPrimitive`, `bandLaplace_bandPrimitive`: **the division formula.** With `B` the two-sided
  Laplace transform of `b`, the primitive of `b` twisted by `v` has transform
  `(e ^ (2 π (s - v) Y) B (v) - B (s)) / (2 π (s - v))`. On the imaginary axis this is the
  quotient of `F (x) - e ^ (-2 π i (x - p) Y) F (p)` by `x - p`, up to the factor `2 π i`.
* `realBandLimited Y`: the band as a closed subspace of `L²(ℝ)`.
* `tendsto_inner_fourier_bandDiffQuot`: the difference quotients of the frequency data, which
  correspond to the multiplication by `(e ^ (2 π i s x) - 1) / (2 π i s)`, converge weakly to
  the multiplication by `x`.
* `mul_fourier_mem_realBandLimited`: hence `x F (x)` is in the band when it is
  square-integrable.
* `inner_complexBandVector_mul_fourier`: and its value at the point `p` is `p F (p)`.
-/

open MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate InnerProductSpace ENNReal

@[expose] public noncomputable section

namespace RiemannMasullo

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

/-! ### Frequency data of a function of the band -/

/-- The Fourier integral at a real point is the two-sided Laplace transform on the imaginary
axis. -/
theorem fourier_eq_bandLaplace (c : ℝ → ℂ) (x : ℝ) :
    𝓕 c x = bandLaplace c (-(Complex.I * x)) := by
  rw [Real.fourier_real_eq_integral_exp_smul, bandLaplace]
  refine integral_congr_ae (Eventually.of_forall fun ξ ↦ ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  ring

/-- A function is the Fourier transform of its reflected Fourier transform. -/
theorem eq_fourier_toLp_of_ae {G : H} {b : ℝ → ℂ} (hb : MemLp b 2)
    (h : ∀ᵐ ξ, b ξ = (𝓕 G : H) (-ξ)) : G = (𝓕 (hb.toLp b) : H) := by
  have h1 : hb.toLp b = (𝓕⁻ G : H) := by
    rw [lp_fourierInv_eq_realReflection_fourier]
    refine Lp.ext ?_
    have hJ := Lp.coeFn_compMeasurePreserving (𝓕 G : H)
      (Measure.measurePreserving_neg (volume : Measure ℝ))
    filter_upwards [hb.coeFn_toLp, hJ, h] with ξ e1 e2 e3
    rw [e1, e3]
    exact e2.symm
  rw [h1]
  simp

/-- The Fourier transform on `L²(ℝ)` commutes with the reflection. -/
theorem fourier_realReflection (G : H) :
    (𝓕 (realReflection G) : H) = realReflection (𝓕 G : H) := by
  rw [← lp_fourier_fourier G]
  exact lp_fourier_fourier (𝓕 G : H)

/-- A vector is an eigenvector of the reflection exactly when its functions has that parity. -/
theorem realReflection_eq_smul_iff {G : H} {σ : ℂ} :
    realReflection G = σ • G ↔ ∀ᵐ x, (G : ℝ → ℂ) (-x) = σ * (G : ℝ → ℂ) x := by
  have hJ := Lp.coeFn_compMeasurePreserving G (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hs := Lp.coeFn_smul σ G
  constructor
  · intro h
    have h' : (realReflection G : ℝ → ℂ) =ᵐ[volume] (σ • G : H) := by rw [h]
    filter_upwards [hJ, hs, h'] with x e1 e2 e3
    have e1' : (realReflection G : ℝ → ℂ) x = (G : ℝ → ℂ) (-x) := e1
    rw [← e1', e3, e2, Pi.smul_apply, smul_eq_mul]
  · intro h
    refine Lp.ext ?_
    filter_upwards [hJ, hs, h] with x e1 e2 e3
    have e1' : (realReflection G : ℝ → ℂ) x = (G : ℝ → ℂ) (-x) := e1
    rw [e1', e3, e2, Pi.smul_apply, smul_eq_mul]

/-- A function and its Fourier transform have the same parity. -/
theorem fourier_parity_iff {G : H} {σ : ℂ} :
    (∀ᵐ ξ, ((𝓕 G : H) : ℝ → ℂ) (-ξ) = σ * ((𝓕 G : H) : ℝ → ℂ) ξ) ↔
      ∀ᵐ x, (G : ℝ → ℂ) (-x) = σ * (G : ℝ → ℂ) x := by
  rw [← realReflection_eq_smul_iff, ← realReflection_eq_smul_iff, ← fourier_realReflection]
  have hsm : (σ • (𝓕 G : H)) = (𝓕 (σ • G) : H) := by
    change _ = Lp.fourierTransformₗᵢ ℝ ℂ (σ • G)
    rw [map_smul]
    rfl
  rw [hsm]
  constructor
  · intro h
    change Lp.fourierTransformₗᵢ ℝ ℂ _ = Lp.fourierTransformₗᵢ ℝ ℂ _ at h
    exact (Lp.fourierTransformₗᵢ ℝ ℂ).injective h
  · intro h
    rw [h]

/-- A measurable function bounded on the band and vanishing outside is integrable. -/
theorem integrable_of_norm_le_of_band {Y : ℝ} {c : ℝ → ℂ} (hm : Measurable c) {C : ℝ}
    (hC : ∀ ξ, ‖c ξ‖ ≤ C) (hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → c ξ = 0) : Integrable c := by
  have h : Integrable ((Icc (-Y) Y).indicator fun _ : ℝ ↦ (C : ℝ)) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  refine h.mono' hm.aestronglyMeasurable (Eventually.of_forall fun ξ ↦ ?_)
  by_cases hξ : ξ ∈ Icc (-Y) Y
  · rw [indicator_of_mem hξ]
    exact hC ξ
  · simp [hsupp ξ hξ, hξ]

/-- A square-integrable function that vanishes outside the band is integrable. -/
theorem integrable_of_memLp_of_band {Y : ℝ} {c : ℝ → ℂ} (hc : MemLp c 2)
    (hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → c ξ = 0) : Integrable c := by
  have h1 : IntegrableOn c (Icc (-Y) Y) := (hc.restrict (Icc (-Y) Y)).integrable one_le_two
  have h2 : Integrable ((Icc (-Y) Y).indicator c) :=
    (integrable_indicator_iff measurableSet_Icc).mpr h1
  refine h2.congr (Eventually.of_forall fun ξ ↦ ?_)
  by_cases h : ξ ∈ Icc (-Y) Y
  · rw [indicator_of_mem h]
  · rw [indicator_of_notMem h, hsupp ξ h]

/-- **Frequency data.** A vector of `L²(ℝ)` whose Fourier transform vanishes outside the band
and has a parity `σ = ±1` is the Fourier transform of a function that vanishes outside the band
and has that parity at every point. -/
theorem exists_band_data_of_parity {Y : ℝ} {G : H} {σ : ℂ} (hσ : σ * σ = 1)
    (hG : ∀ᵐ ξ, ξ ∉ Icc (-Y) Y → ((𝓕 G : H) : ℝ → ℂ) ξ = 0)
    (hpar : ∀ᵐ ξ, ((𝓕 G : H) : ℝ → ℂ) (-ξ) = σ * ((𝓕 G : H) : ℝ → ℂ) ξ) :
    ∃ b : ℝ → ℂ, Integrable b ∧ ∃ hb : MemLp b 2, (∀ ξ, ξ ∉ Icc (-Y) Y → b ξ = 0) ∧
      (∀ ξ, b (-ξ) = σ * b ξ) ∧ G = (𝓕 (hb.toLp b) : H) := by
  set Ψ : ℝ → ℂ := ((𝓕 G : H) : ℝ → ℂ) with hΨ
  have hΨ2 : MemLp Ψ 2 := Lp.memLp _
  have hΨn : MemLp (fun ξ ↦ Ψ (-ξ)) 2 :=
    hΨ2.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))
  set b : ℝ → ℂ := (Icc (-Y) Y).indicator fun ξ ↦ (1 / 2 : ℂ) * (Ψ (-ξ) + σ * Ψ ξ) with hb
  have hb2 : MemLp b 2 :=
    ((hΨn.add (hΨ2.const_mul σ)).const_mul (1 / 2 : ℂ)).indicator
      measurableSet_Icc.nullMeasurableSet
  have hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → b ξ = 0 := fun ξ hξ ↦ by
    rw [hb, indicator_of_notMem hξ]
  have hmem : ∀ ξ : ℝ, -ξ ∈ Icc (-Y) Y ↔ ξ ∈ Icc (-Y) Y := fun ξ ↦ by
    constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩
  refine ⟨b, integrable_of_memLp_of_band hb2 hsupp, hb2, hsupp, fun ξ ↦ ?_, ?_⟩
  · by_cases hξ : ξ ∈ Icc (-Y) Y
    · rw [hb, indicator_of_mem ((hmem ξ).mpr hξ), indicator_of_mem hξ, neg_neg]
      linear_combination (-(1 / 2 : ℂ)) * Ψ ξ * hσ
    · rw [hsupp ξ hξ, hsupp (-ξ) (mt (hmem ξ).mp hξ), mul_zero]
  · refine eq_fourier_toLp_of_ae hb2 ?_
    have hGn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hG
    filter_upwards [hpar, hGn] with ξ e1 e2
    by_cases hξ : ξ ∈ Icc (-Y) Y
    · rw [hb, indicator_of_mem hξ]
      have e1' : Ψ (-ξ) = σ * Ψ ξ := e1
      rw [← e1']
      ring
    · rw [hsupp ξ hξ]
      exact (e2 (mt (hmem ξ).mp hξ)).symm

/-- **Frequency data, without parity.** A vector of `L²(ℝ)` whose Fourier transform vanishes
outside the band is the Fourier transform of a function that vanishes outside the band. -/
theorem exists_band_data {Y : ℝ} {G : H}
    (hG : ∀ᵐ ξ, ξ ∉ Icc (-Y) Y → ((𝓕 G : H) : ℝ → ℂ) ξ = 0) :
    ∃ b : ℝ → ℂ, Integrable b ∧ ∃ hb : MemLp b 2, (∀ ξ, ξ ∉ Icc (-Y) Y → b ξ = 0) ∧
      G = (𝓕 (hb.toLp b) : H) := by
  set Ψ : ℝ → ℂ := ((𝓕 G : H) : ℝ → ℂ) with hΨ
  have hΨn : MemLp (fun ξ ↦ Ψ (-ξ)) 2 :=
    (Lp.memLp _).comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))
  set b : ℝ → ℂ := (Icc (-Y) Y).indicator fun ξ ↦ Ψ (-ξ) with hb
  have hb2 : MemLp b 2 := hΨn.indicator measurableSet_Icc.nullMeasurableSet
  have hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → b ξ = 0 := fun ξ hξ ↦ by
    rw [hb, indicator_of_notMem hξ]
  have hmem : ∀ ξ : ℝ, -ξ ∈ Icc (-Y) Y ↔ ξ ∈ Icc (-Y) Y := fun ξ ↦ by
    constructor <;> intro h <;> exact ⟨by linarith [h.2], by linarith [h.1]⟩
  refine ⟨b, integrable_of_memLp_of_band hb2 hsupp, hb2, hsupp, eq_fourier_toLp_of_ae hb2 ?_⟩
  have hGn := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hG
  filter_upwards [hGn] with ξ e2
  by_cases hξ : ξ ∈ Icc (-Y) Y
  · rw [hb, indicator_of_mem hξ]
  · rw [hsupp ξ hξ]
    exact (e2 (mt (hmem ξ).mp hξ)).symm

/-! ### The primitive of the frequency data -/

/-- The primitive of the frequency data twisted by the rate `v`:
`ξ ↦ 1_[-Y, Y] (ξ) e ^ (-2 π v ξ) ∫ η in -Y..ξ, b η e ^ (2 π v η)`. Up to the factor `2 π i`
it is the frequency data of the quotient of the function by `x - p`, where `v = -i p`. -/
def bandPrimitive (Y : ℝ) (b : ℝ → ℂ) (v : ℂ) (ξ : ℝ) : ℂ :=
  (Icc (-Y) Y).indicator (fun ξ : ℝ ↦ Complex.exp (-(2 * π * v * ξ)) *
    ∫ η in (-Y)..ξ, b η * Complex.exp (2 * π * v * η)) ξ

/-- The primitive vanishes outside the band. -/
theorem bandPrimitive_of_notMem {Y : ℝ} {b : ℝ → ℂ} {v : ℂ} {ξ : ℝ} (h : ξ ∉ Icc (-Y) Y) :
    bandPrimitive Y b v ξ = 0 := by
  simp only [bandPrimitive, indicator_of_notMem h]

private theorem continuous_bandPrimitive_aux {Y : ℝ} {b : ℝ → ℂ} (hb : Integrable b)
    (hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → b ξ = 0) (v : ℂ) :
    Continuous fun ξ : ℝ ↦ Complex.exp (-(2 * π * v * ξ)) *
      ∫ η in (-Y)..ξ, b η * Complex.exp (2 * π * v * η) := by
  have hf := integrable_mul_cexp_of_band hb hsupp v
  exact (by fun_prop : Continuous fun ξ : ℝ ↦ Complex.exp (-(2 * π * v * ξ))).mul
    (intervalIntegral.continuous_primitive (fun _ _ ↦ hf.intervalIntegrable) (-Y))

/-- The primitive is measurable. -/
theorem measurable_bandPrimitive {Y : ℝ} {b : ℝ → ℂ} (hb : Integrable b)
    (hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → b ξ = 0) (v : ℂ) : Measurable (bandPrimitive Y b v) :=
  (continuous_bandPrimitive_aux hb hsupp v).measurable.indicator measurableSet_Icc

/-- The primitive is bounded. -/
theorem exists_norm_bandPrimitive_le {Y : ℝ} {b : ℝ → ℂ} (hb : Integrable b)
    (hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → b ξ = 0) (v : ℂ) :
    ∃ C, ∀ ξ, ‖bandPrimitive Y b v ξ‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-Y) Y)
    (continuous_bandPrimitive_aux hb hsupp v).continuousOn
  refine ⟨max C 0, fun ξ ↦ ?_⟩
  by_cases h : ξ ∈ Icc (-Y) Y
  · rw [bandPrimitive, indicator_of_mem h]
    exact (hC ξ h).trans (le_max_left _ _)
  · rw [bandPrimitive_of_notMem h, norm_zero]
    exact le_max_right _ _

/-- The primitive is integrable. -/
theorem integrable_bandPrimitive {Y : ℝ} {b : ℝ → ℂ} (hb : Integrable b)
    (hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → b ξ = 0) (v : ℂ) : Integrable (bandPrimitive Y b v) := by
  obtain ⟨C, hC⟩ := exists_norm_bandPrimitive_le hb hsupp v
  exact integrable_of_norm_le_of_band (measurable_bandPrimitive hb hsupp v) hC
    fun ξ hξ ↦ bandPrimitive_of_notMem hξ

/-- The primitive is square-integrable. -/
theorem memLp_bandPrimitive {Y : ℝ} {b : ℝ → ℂ} (hb : Integrable b)
    (hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → b ξ = 0) (v : ℂ) : MemLp (bandPrimitive Y b v) 2 := by
  obtain ⟨C, hC⟩ := exists_norm_bandPrimitive_le hb hsupp v
  exact memLp_of_norm_le_of_band (measurable_bandPrimitive hb hsupp v) hC
    fun ξ hξ ↦ bandPrimitive_of_notMem hξ

/-- **The division formula.** For frequency data `b` supported in the band, the two-sided
Laplace transform `B` of `b` and that of its primitive twisted by `v` satisfy
`2 π (s - v) B_prim (s) = e ^ (2 π (s - v) Y) B (v) - B (s)`. On the imaginary axis this says
that `(F (x) - e ^ (-2 π i (x - p) Y) F (p)) / (x - p)` is again a function of the band. -/
theorem bandLaplace_bandPrimitive {Y : ℝ} {b : ℝ → ℂ} (hb : Integrable b)
    (hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → b ξ = 0) {v s : ℂ} (hsv : s ≠ v) :
    2 * π * (s - v) * bandLaplace (bandPrimitive Y b v) s =
      Complex.exp (2 * π * (s - v) * Y) * bandLaplace b v - bandLaplace b s := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set c : ℂ := 2 * π * (s - v) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hπ) (sub_ne_zero.mpr hsv)
  set f : ℝ → ℂ := fun η ↦ b η * Complex.exp (2 * π * v * η) with hf
  have hfi : Integrable f := integrable_mul_cexp_of_band hb hsupp v
  have hbs : Integrable fun η : ℝ ↦ b η * Complex.exp (2 * π * s * η) :=
    integrable_mul_cexp_of_band hb hsupp s
  set S : Set (ℝ × ℝ) := {p | p.1 ∈ Icc (-Y) Y ∧ -Y < p.2 ∧ p.2 ≤ p.1} with hS
  have hSm : MeasurableSet S :=
    (measurable_fst measurableSet_Icc).inter
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst))
  set G : ℝ → ℝ → ℂ := fun ξ η ↦
    S.indicator (fun p : ℝ × ℝ ↦ f p.2 * Complex.exp (c * p.1)) (ξ, η) with hG
  have hA : ∀ ξ, bandPrimitive Y b v ξ * Complex.exp (2 * π * s * ξ) = ∫ η, G ξ η := fun ξ ↦ by
    by_cases hξ : ξ ∈ Icc (-Y) Y
    · have hin : ∀ η, G ξ η =
          (Ioc (-Y) ξ).indicator (fun η ↦ f η * Complex.exp (c * ξ)) η := fun η ↦ by
        by_cases hη : η ∈ Ioc (-Y) ξ
        · have hp : (ξ, η) ∈ S := ⟨hξ, hη.1, hη.2⟩
          rw [indicator_of_mem hη, hG]
          dsimp only
          rw [indicator_of_mem hp]
        · have hp : (ξ, η) ∉ S := fun h ↦ hη ⟨h.2.1, h.2.2⟩
          rw [indicator_of_notMem hη, hG]
          dsimp only
          rw [indicator_of_notMem hp]
      simp_rw [hin]
      rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hξ.1,
        intervalIntegral.integral_mul_const, bandPrimitive, indicator_of_mem hξ]
      have he : Complex.exp (c * ξ) =
          Complex.exp (-(2 * π * v * ξ)) * Complex.exp (2 * π * s * ξ) := by
        rw [← Complex.exp_add]
        congr 1
        rw [hc]
        ring
      rw [he]
      ring
    · have hin : ∀ η, G ξ η = 0 := fun η ↦ by
        have hp : (ξ, η) ∉ S := fun h ↦ hξ h.1
        rw [hG]
        dsimp only
        rw [indicator_of_notMem hp]
      simp_rw [hin]
      rw [integral_zero, bandPrimitive_of_notMem hξ, zero_mul]
  obtain ⟨M, hM⟩ := exists_norm_complexBandExp_le Y (s - v)
  have hGi : Integrable (Function.uncurry G) (volume.prod volume) := by
    have hind : Integrable ((Icc (-Y) Y).indicator fun _ : ℝ ↦ (max M 0 : ℝ)) := by
      rw [integrable_indicator_iff measurableSet_Icc]
      exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    have hmaj : Integrable (fun p : ℝ × ℝ ↦
        (Icc (-Y) Y).indicator (fun _ : ℝ ↦ (max M 0 : ℝ)) p.1 * ‖f p.2‖)
        (volume.prod volume) := hind.mul_prod hfi.norm
    have hmeas : AEStronglyMeasurable (Function.uncurry G) (volume.prod volume) := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ f p.2 * Complex.exp (c * p.1))
          (volume.prod volume) :=
        (hfi.aestronglyMeasurable.comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_snd).mul
          (by fun_prop : Continuous fun p : ℝ × ℝ ↦ Complex.exp (c * p.1)).aestronglyMeasurable
      exact h1.indicator hSm
    refine hmaj.mono' hmeas (Eventually.of_forall fun p ↦ ?_)
    by_cases hp : p ∈ S
    · have hb1 := hM p.1
      rw [complexBandExp_of_mem hp.1] at hb1
      have he : Complex.exp (c * p.1) = Complex.exp (2 * π * (s - v) * p.1) := by rw [hc]
      have hp' : (p.1, p.2) ∈ S := hp
      have hGp : Function.uncurry G p = f p.2 * Complex.exp (c * p.1) := by
        change G p.1 p.2 = _
        rw [hG]
        dsimp only
        rw [indicator_of_mem hp']
      rw [hGp, indicator_of_mem hp.1, norm_mul, mul_comm, he]
      gcongr
      exact hb1.trans (le_max_left _ _)
    · have hp' : (p.1, p.2) ∉ S := hp
      have hGp : Function.uncurry G p = 0 := by
        change G p.1 p.2 = _
        rw [hG]
        dsimp only
        rw [indicator_of_notMem hp']
      rw [hGp, norm_zero]
      exact mul_nonneg (indicator_nonneg (fun _ _ ↦ le_max_right _ _) _) (norm_nonneg _)
  have hswap := integral_integral_swap hGi
  have hD : ∀ᵐ η, ∫ ξ, G ξ η =
      f η * ((Complex.exp (c * Y) - Complex.exp (c * η)) / c) := by
    have hne : ∀ᵐ η : ℝ, η ≠ -Y := by
      rw [ae_iff]
      simp
    filter_upwards [hne] with η hη
    by_cases hmem : η ∈ Icc (-Y) Y
    · have hη' : -Y < η := lt_of_le_of_ne hmem.1 (Ne.symm hη)
      have hin : ∀ ξ, G ξ η =
          (Icc η Y).indicator (fun ξ : ℝ ↦ f η * Complex.exp (c * ξ)) ξ := fun ξ ↦ by
        by_cases hξ : ξ ∈ Icc η Y
        · have hp : (ξ, η) ∈ S := ⟨⟨by linarith [hξ.1], hξ.2⟩, hη', hξ.1⟩
          rw [indicator_of_mem hξ, hG]
          dsimp only
          rw [indicator_of_mem hp]
        · have hp : (ξ, η) ∉ S := fun h ↦ hξ ⟨h.2.2, h.1.2⟩
          rw [indicator_of_notMem hξ, hG]
          dsimp only
          rw [indicator_of_notMem hp]
      simp_rw [hin]
      rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hmem.2, intervalIntegral.integral_const_mul,
        integral_exp_mul_complex hc0]
    · have hf0 : f η = 0 := by
        rw [hf]
        dsimp only
        rw [hsupp η hmem, zero_mul]
      have hin : ∀ ξ, G ξ η = 0 := fun ξ ↦ by
        rw [hG]
        dsimp only
        by_cases hp : (ξ, η) ∈ S
        · rw [indicator_of_mem hp, hf0, zero_mul]
        · rw [indicator_of_notMem hp]
      simp_rw [hin]
      rw [integral_zero, hf0, zero_mul]
  have hfs : ∀ η : ℝ, f η * Complex.exp (c * η) = b η * Complex.exp (2 * π * s * η) := fun η ↦ by
    rw [hf]
    dsimp only
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    rw [hc]
    ring
  have hrew : ∀ η : ℝ, f η * ((Complex.exp (c * Y) - Complex.exp (c * η)) / c) =
      Complex.exp (c * Y) / c * f η - 1 / c * (b η * Complex.exp (2 * π * s * η)) := fun η ↦ by
    rw [← hfs]
    ring
  have hlhs : bandLaplace (bandPrimitive Y b v) s = ∫ ξ, ∫ η, G ξ η := by
    rw [bandLaplace]
    exact integral_congr_ae (Eventually.of_forall hA)
  rw [hlhs, hswap, integral_congr_ae hD]
  simp_rw [hrew]
  rw [integral_sub (hfi.const_mul _) (hbs.const_mul _), integral_const_mul, integral_const_mul]
  change c * (Complex.exp (c * Y) / c * bandLaplace b v - 1 / c * bandLaplace b s) = _
  field_simp

/-! ### Multiplication by `x` on the band -/

/-- The difference quotient of the frequency data: `(b (ξ + s) - b ξ) / (2 π i s)`. Its Fourier
integral is `(e ^ (2 π i s x) - 1) / (2 π i s)` times that of `b`, and the factor tends to `x`
as `s → 0`. -/
def bandDiffQuot (b : ℝ → ℂ) (s : ℝ) (ξ : ℝ) : ℂ :=
  (2 * π * Complex.I * s)⁻¹ * (b (ξ + s) - b ξ)

/-- The difference quotient of integrable data is integrable. -/
theorem integrable_bandDiffQuot {b : ℝ → ℂ} (hb : Integrable b) (s : ℝ) :
    Integrable (bandDiffQuot b s) :=
  ((hb.comp_add_right s).sub hb).const_mul _

/-- The difference quotient of square-integrable data is square-integrable. -/
theorem memLp_bandDiffQuot {b : ℝ → ℂ} (hb : MemLp b 2) (s : ℝ) :
    MemLp (bandDiffQuot b s) 2 :=
  ((hb.comp_measurePreserving (measurePreserving_add_right volume s)).sub hb).const_mul _

/-- The difference quotient of data supported in the band `[-Y, Y]` is supported in the band
`[-(Y + |s|), Y + |s|]`. -/
theorem bandDiffQuot_of_notMem {Y : ℝ} {b : ℝ → ℂ} (hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → b ξ = 0)
    {s ξ : ℝ} (hξ : ξ ∉ Icc (-(Y + |s|)) (Y + |s|)) : bandDiffQuot b s ξ = 0 := by
  have h1 : ξ ∉ Icc (-Y) Y := fun h ↦ hξ ⟨by linarith [h.1, abs_nonneg s], by
    linarith [h.2, abs_nonneg s]⟩
  have h2 : ξ + s ∉ Icc (-Y) Y := fun h ↦ hξ ⟨by linarith [h.1, le_abs_self s], by
    linarith [h.2, neg_abs_le s]⟩
  rw [bandDiffQuot, hsupp ξ h1, hsupp _ h2, sub_zero, mul_zero]

/-- The two-sided Laplace transform of the difference quotient. -/
theorem bandLaplace_bandDiffQuot {b : ℝ → ℂ} {v : ℂ}
    (hbv : Integrable fun ξ : ℝ ↦ b ξ * Complex.exp (2 * π * v * ξ)) (s : ℝ) :
    bandLaplace (bandDiffQuot b s) v =
      (2 * π * Complex.I * s)⁻¹ * (Complex.exp (-(2 * π * v * s)) - 1) * bandLaplace b v := by
  have htr : ∀ ξ : ℝ, b (ξ + s) * Complex.exp (2 * π * v * ξ) =
      Complex.exp (-(2 * π * v * s)) * (b (ξ + s) * Complex.exp (2 * π * v * ((ξ + s : ℝ) : ℂ))) :=
    fun ξ ↦ by
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast
      ring
  have hi1 : Integrable fun ξ : ℝ ↦ b (ξ + s) * Complex.exp (2 * π * v * ξ) := by
    have h := (hbv.comp_add_right s).const_mul (Complex.exp (-(2 * π * v * s)))
    refine h.congr (Eventually.of_forall fun ξ ↦ ?_)
    exact (htr ξ).symm
  have h1 : ∫ ξ : ℝ, b (ξ + s) * Complex.exp (2 * π * v * ξ) =
      Complex.exp (-(2 * π * v * s)) * bandLaplace b v := by
    rw [bandLaplace, ← integral_add_right_eq_self
      (fun ξ : ℝ ↦ b ξ * Complex.exp (2 * π * v * ξ)) s, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall htr)
  have hpt : ∀ ξ : ℝ, bandDiffQuot b s ξ * Complex.exp (2 * π * v * ξ) =
      (2 * π * Complex.I * s)⁻¹ * (b (ξ + s) * Complex.exp (2 * π * v * ξ) -
        b ξ * Complex.exp (2 * π * v * ξ)) := fun ξ ↦ by
    rw [bandDiffQuot]
    ring
  rw [bandLaplace]
  simp_rw [hpt]
  rw [integral_const_mul, integral_sub hi1 hbv, h1, bandLaplace]
  ring

/-- Data times a unimodular exponential is integrable. -/
theorem integrable_mul_cexp_imag {b : ℝ → ℂ} (hb : Integrable b) (x : ℝ) :
    Integrable fun ξ : ℝ ↦ b ξ * Complex.exp (2 * π * (-(Complex.I * x)) * ξ) := by
  refine hb.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun ξ ↦ ?_)
  have : (2 * π * (-(Complex.I * x)) * ξ : ℂ) = ((-(2 * π * x * ξ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- The Fourier integral of the difference quotient. -/
theorem fourier_bandDiffQuot {b : ℝ → ℂ} (hb : Integrable b) (s x : ℝ) :
    𝓕 (bandDiffQuot b s) x =
      (2 * π * Complex.I * s)⁻¹ * (Complex.exp (2 * π * Complex.I * s * x) - 1) * 𝓕 b x := by
  rw [fourier_eq_bandLaplace, fourier_eq_bandLaplace,
    bandLaplace_bandDiffQuot (integrable_mul_cexp_imag hb x)]
  have : Complex.exp (-(2 * π * (-(Complex.I * x)) * s)) =
      Complex.exp (2 * π * Complex.I * s * x) := by
    congr 1
    ring
  rw [this]

/-- The factor of the difference quotient is bounded by `|x|`. -/
theorem norm_diffQuot_factor_le {s : ℝ} (hs : s ≠ 0) (x : ℝ) :
    ‖(2 * π * Complex.I * s)⁻¹ * (Complex.exp (2 * π * Complex.I * s * x) - 1)‖ ≤ |x| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * π * s * x)
  have he : Complex.exp (Complex.I * ((2 * π * s * x : ℝ) : ℂ)) =
      Complex.exp (2 * π * Complex.I * s * x) := by
    congr 1
    push_cast
    ring
  rw [he] at h
  have hn : ‖(2 * π * Complex.I * s : ℂ)‖ = 2 * π * |s| := by
    simp [abs_of_pos Real.pi_pos]
  have hpos : 0 < 2 * π * |s| := by positivity
  rw [norm_mul, norm_inv, hn, inv_mul_le_iff₀ hpos]
  calc ‖Complex.exp (2 * π * Complex.I * s * x) - 1‖ ≤ ‖2 * π * s * x‖ := h
    _ = 2 * π * |s| * |x| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
      simp

/-- The steps `1 / (n + 1)` of the difference quotients. -/
def bandDiffStep (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- The steps are positive. -/
theorem bandDiffStep_pos (n : ℕ) : 0 < bandDiffStep n := by
  unfold bandDiffStep
  positivity

/-- The steps are at most one. -/
theorem bandDiffStep_le_one (n : ℕ) : bandDiffStep n ≤ 1 := by
  unfold bandDiffStep
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- The steps decrease. -/
theorem bandDiffStep_le {m n : ℕ} (h : m ≤ n) : bandDiffStep n ≤ bandDiffStep m := by
  unfold bandDiffStep
  have : (m : ℝ) ≤ n := Nat.cast_le.mpr h
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

/-- The steps tend to zero. -/
theorem tendsto_bandDiffStep : Tendsto bandDiffStep atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The difference quotient of the exponential along the steps tends to the rate. -/
theorem tendsto_cexp_sub_one_div_bandDiffStep (c : ℂ) :
    Tendsto (fun n : ℕ ↦ ((bandDiffStep n : ℝ) : ℂ)⁻¹ *
      (Complex.exp (c * bandDiffStep n) - 1)) atTop (𝓝 c) := by
  have h : HasDerivAt (fun s : ℝ ↦ Complex.exp (c * s)) c 0 := by
    have h1 : HasDerivAt (fun z : ℂ ↦ Complex.exp (c * z))
        (Complex.exp (c * ((0 : ℝ) : ℂ)) * (c * 1)) ((0 : ℝ) : ℂ) :=
      ((hasDerivAt_id _).const_mul c).cexp
    have h2 := h1.comp_ofReal
    simpa using h2
  have h3 := hasDerivAt_iff_tendsto_slope.mp h
  have hstep : Tendsto bandDiffStep atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_bandDiffStep,
      Eventually.of_forall fun n ↦ (bandDiffStep_pos n).ne'⟩
  refine (h3.comp hstep).congr fun n ↦ ?_
  simp [slope, Complex.real_smul]

/-! ### The band as a closed subspace -/

/-- The functions of `L²(ℝ)` whose Fourier transform vanishes outside `[-Y, Y]`. -/
def realBandLimited (Y : ℝ) : Submodule ℂ H :=
  (LinearMap.ker (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Icc (-Y) Y)ᶜ).toLinearMap).comap
    (Lp.fourierTransformₗᵢ ℝ ℂ).toLinearEquiv.toLinearMap

/-- Membership in the band, in terms of the Fourier transform. -/
theorem mem_realBandLimited_iff {Y : ℝ} {F : H} :
    F ∈ realBandLimited Y ↔ ∀ᵐ ξ, ξ ∉ Icc (-Y) Y → ((𝓕 F : H) : ℝ → ℂ) ξ = 0 := by
  change LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Icc (-Y) Y)ᶜ (𝓕 F : H) = 0 ↔ _
  generalize (𝓕 F : H) = Ψ
  have hco := LpToLpRestrictCLM_coeFn (𝕜 := ℂ) (Icc (-Y) Y)ᶜ Ψ
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

/-- The band is closed. -/
theorem isClosed_realBandLimited (Y : ℝ) : IsClosed (realBandLimited Y : Set H) := by
  have h : (realBandLimited Y : Set H) =
      {F | LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Icc (-Y) Y)ᶜ (Lp.fourierTransformₗᵢ ℝ ℂ F) = 0} := by
    ext F
    rfl
  rw [h]
  exact isClosed_eq ((ContinuousLinearMap.continuous _).comp
    (Lp.fourierTransformₗᵢ ℝ ℂ).continuous) continuous_const

/-- The band is complete. -/
instance instCompleteSpaceRealBandLimited (Y : ℝ) : CompleteSpace (realBandLimited Y) :=
  (isClosed_realBandLimited Y).completeSpace_coe

/-- The Fourier transform of the vector of frequency data `c` is the class of the reflection of
`c`. -/
theorem coeFn_fourier_fourier_toLp {c : ℝ → ℂ} (hc : MemLp c 2) :
    ((𝓕 (𝓕 (hc.toLp c) : H) : H) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦ c (-ξ) := by
  rw [lp_fourier_fourier]
  have h1 := Lp.coeFn_compMeasurePreserving (hc.toLp c)
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  have h2 := (Measure.measurePreserving_neg (volume : Measure ℝ)
    ).quasiMeasurePreserving.ae_eq_comp hc.coeFn_toLp
  filter_upwards [h1, h2] with ξ e1 e2
  exact e1.trans e2

/-- The vector of frequency data supported in the band lies in the band. -/
theorem fourier_toLp_mem_realBandLimited {Y : ℝ} {c : ℝ → ℂ} (hc : MemLp c 2)
    (hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → c ξ = 0) : (𝓕 (hc.toLp c) : H) ∈ realBandLimited Y := by
  rw [mem_realBandLimited_iff]
  filter_upwards [coeFn_fourier_fourier_toLp hc] with ξ e hξ
  rw [e]
  exact hsupp _ fun h ↦ hξ ⟨by linarith [h.2], by linarith [h.1]⟩

/-! ### Multiplication by `x` preserves the band -/

/-- **Weak convergence of the difference quotients.** If `G` is the class of `x F (x)` with `F`
the Fourier integral of `b`, then the pairings of any vector with the vectors of the difference
quotients of `b` tend to its pairing with `G`. -/
theorem tendsto_inner_fourier_bandDiffQuot {b : ℝ → ℂ} (hb1 : Integrable b) (hb2 : MemLp b 2)
    {G : H} (hG : (G : ℝ → ℂ) =ᵐ[volume] fun x ↦ (x : ℂ) * 𝓕 b x) (W : H) :
    Tendsto (fun n : ℕ ↦
        ⟪W, (𝓕 ((memLp_bandDiffQuot hb2 (bandDiffStep n)).toLp _) : H)⟫_ℂ) atTop
      (𝓝 ⟪W, G⟫_ℂ) := by
  simp only [L2.inner_def]
  have hVn : ∀ n : ℕ, ((𝓕 ((memLp_bandDiffQuot hb2 (bandDiffStep n)).toLp _) : H) : ℝ → ℂ)
      =ᵐ[volume] fun x ↦ (2 * π * Complex.I * bandDiffStep n)⁻¹ *
        (Complex.exp (2 * π * Complex.I * bandDiffStep n * x) - 1) * 𝓕 b x := fun n ↦ by
    filter_upwards [fourier_ae_eq_fourier_toLp (integrable_bandDiffQuot hb1 (bandDiffStep n))
      (memLp_bandDiffQuot hb2 (bandDiffStep n))] with x hx
    rw [← hx, fourier_bandDiffQuot hb1]
  have hall := ae_all_iff.mpr hVn
  refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖(W : ℝ → ℂ) x‖ * ‖(G : ℝ → ℂ) x‖)
    (fun n ↦ (L2.integrable_inner (𝕜 := ℂ) W _).aestronglyMeasurable)
    ((Lp.memLp W).norm.integrable_mul (Lp.memLp G).norm) (fun n ↦ ?_) ?_
  · filter_upwards [hVn n, hG] with x e1 e2
    rw [e1, e2, RCLike.inner_apply, norm_mul, RCLike.norm_conj, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [norm_mul, norm_mul (x : ℂ), Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (norm_diffQuot_factor_le (bandDiffStep_pos n).ne' x)
      (norm_nonneg _)
  · filter_upwards [hall, hG] with x e1 e2
    have hfac : Tendsto (fun n : ℕ ↦ (2 * π * Complex.I * bandDiffStep n)⁻¹ *
        (Complex.exp (2 * π * Complex.I * bandDiffStep n * x) - 1)) atTop (𝓝 (x : ℂ)) := by
      have h := (tendsto_cexp_sub_one_div_bandDiffStep (2 * π * Complex.I * x)).const_mul
        (2 * π * Complex.I)⁻¹
      have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hlim : (2 * π * Complex.I)⁻¹ * (2 * π * Complex.I * x) = (x : ℂ) := by
        field_simp
      rw [hlim] at h
      refine h.congr fun n ↦ ?_
      have : Complex.exp (2 * π * Complex.I * x * bandDiffStep n) =
          Complex.exp (2 * π * Complex.I * bandDiffStep n * x) := by
        congr 1
        ring
      have hs : ((bandDiffStep n : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (bandDiffStep_pos n).ne'
      rw [this]
      field_simp
    have h := (hfac.mul_const (𝓕 b x)).mul_const (conj ((W : ℝ → ℂ) x))
    have h' : Tendsto (fun n : ℕ ↦ ⟪(W : ℝ → ℂ) x,
        ((𝓕 ((memLp_bandDiffQuot hb2 (bandDiffStep n)).toLp _) : H) : ℝ → ℂ) x⟫_ℂ) atTop
        (𝓝 ((x : ℂ) * 𝓕 b x * conj ((W : ℝ → ℂ) x))) :=
      h.congr fun n ↦ by rw [e1 n, RCLike.inner_apply]
    rw [e2, RCLike.inner_apply]
    exact h'

/-- **Multiplication by `x` preserves the band.** If `F` is the Fourier integral of data `b`
supported in the band and `x F (x)` is square-integrable, with class `G`, then `G` lies in the
band. -/
theorem mul_fourier_mem_realBandLimited {Y : ℝ} {b : ℝ → ℂ} (hb1 : Integrable b)
    (hb2 : MemLp b 2) (hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → b ξ = 0) {G : H}
    (hG : (G : ℝ → ℂ) =ᵐ[volume] fun x ↦ (x : ℂ) * 𝓕 b x) : G ∈ realBandLimited Y := by
  have hm : ∀ m : ℕ, G ∈ realBandLimited (Y + bandDiffStep m) := fun m ↦ by
    rw [← Submodule.orthogonal_orthogonal (realBandLimited (Y + bandDiffStep m)),
      Submodule.mem_orthogonal]
    intro W hW
    have hlim := tendsto_inner_fourier_bandDiffQuot hb1 hb2 hG W
    have hz : ∀ᶠ n : ℕ in atTop,
        ⟪W, (𝓕 ((memLp_bandDiffQuot hb2 (bandDiffStep n)).toLp _) : H)⟫_ℂ = 0 := by
      filter_upwards [eventually_ge_atTop m] with n hn
      refine (Submodule.mem_orthogonal' _ W).mp hW _
        (fourier_toLp_mem_realBandLimited _ fun ξ hξ ↦ ?_)
      refine bandDiffQuot_of_notMem hsupp fun h ↦ hξ ?_
      have h1 := bandDiffStep_le hn
      rw [abs_of_pos (bandDiffStep_pos n)] at h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hz.mono fun n h ↦ h.symm))
  rw [mem_realBandLimited_iff]
  have hall : ∀ᵐ ξ, ∀ m : ℕ, ξ ∉ Icc (-(Y + bandDiffStep m)) (Y + bandDiffStep m) →
      ((𝓕 G : H) : ℝ → ℂ) ξ = 0 := ae_all_iff.mpr fun m ↦ mem_realBandLimited_iff.mp (hm m)
  filter_upwards [hall] with ξ hξ hnot
  have hcases : ξ < -Y ∨ Y < ξ := by
    by_contra h
    rw [not_or, not_lt, not_lt] at h
    exact hnot ⟨h.1, h.2⟩
  rcases hcases with h | h
  · obtain ⟨m, hm'⟩ := exists_nat_one_div_lt (sub_pos.mpr h : 0 < -Y - ξ)
    refine hξ m fun hmem ↦ ?_
    have := hmem.1
    unfold bandDiffStep at this
    linarith
  · obtain ⟨m, hm'⟩ := exists_nat_one_div_lt (sub_pos.mpr h : 0 < ξ - Y)
    refine hξ m fun hmem ↦ ?_
    have := hmem.2
    unfold bandDiffStep at this
    linarith

/-- **The value of `x F (x)` at a complex point.** With `F` the Fourier integral of data `b`
supported in the band and `G` the class of `x F (x)`, the pairing of `G` with the vector of
rate `conj v` of a larger band is `i v B (v)`, where `B` is the two-sided Laplace transform of
`b`: the value of `x F (x)` at the point `p` with `v = -i p` is `p F (p)`. -/
theorem inner_complexBandVector_mul_fourier {Y : ℝ} {b : ℝ → ℂ} (hb1 : Integrable b)
    (hb2 : MemLp b 2) (hsupp : ∀ ξ, ξ ∉ Icc (-Y) Y → b ξ = 0) {G : H}
    (hG : (G : ℝ → ℂ) =ᵐ[volume] fun x ↦ (x : ℂ) * 𝓕 b x) (v : ℂ) :
    ⟪complexBandVector (Y + 1) (conj v), G⟫_ℂ = Complex.I * v * bandLaplace b v := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hlim := tendsto_inner_fourier_bandDiffQuot hb1 hb2 hG (complexBandVector (Y + 1) (conj v))
  have heq : ∀ n : ℕ, ⟪complexBandVector (Y + 1) (conj v),
      (𝓕 ((memLp_bandDiffQuot hb2 (bandDiffStep n)).toLp _) : H)⟫_ℂ =
      (2 * π * Complex.I * bandDiffStep n)⁻¹ *
        (Complex.exp (-(2 * π * v * bandDiffStep n)) - 1) * bandLaplace b v := fun n ↦ by
    rw [inner_complexBandVector_fourier _ _ (fun ξ hξ ↦ ?_), Complex.conj_conj,
      bandLaplace_bandDiffQuot (integrable_mul_cexp_of_band hb1 hsupp v)]
    refine bandDiffQuot_of_notMem hsupp fun h ↦ hξ ?_
    have h1 := bandDiffStep_le_one n
    rw [abs_of_pos (bandDiffStep_pos n)] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hlim2 : Tendsto (fun n : ℕ ↦ (2 * π * Complex.I * bandDiffStep n)⁻¹ *
      (Complex.exp (-(2 * π * v * bandDiffStep n)) - 1) * bandLaplace b v) atTop
      (𝓝 (Complex.I * v * bandLaplace b v)) := by
    have h := ((tendsto_cexp_sub_one_div_bandDiffStep (-(2 * π * v))).const_mul
      (2 * π * Complex.I)⁻¹).mul_const (bandLaplace b v)
    have hval : (2 * π * Complex.I)⁻¹ * -(2 * π * v) * bandLaplace b v =
        Complex.I * v * bandLaplace b v := by
      have hI : (Complex.I)⁻¹ = -Complex.I := Complex.inv_I
      rw [mul_inv, hI]
      field_simp
    rw [hval] at h
    refine h.congr fun n ↦ ?_
    have hs : ((bandDiffStep n : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (bandDiffStep_pos n).ne'
    have he : Complex.exp (-(2 * π * v) * bandDiffStep n) =
        Complex.exp (-(2 * π * v * bandDiffStep n)) := by
      congr 1
      ring
    rw [he]
    field_simp
  exact tendsto_nhds_unique (hlim.congr heq) hlim2

end RiemannMasullo
