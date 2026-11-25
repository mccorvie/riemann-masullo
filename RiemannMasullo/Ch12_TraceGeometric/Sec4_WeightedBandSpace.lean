module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedBandTrace
public import RiemannMasullo.AppC_LCTVS.Sec3a_IsometryTransport

/-! # The weighted space of the rational real-place model and its unitary onto `L²(ℝ)`

Paper: Theorem 12.4.1.1, pp. 514–519, and the value used on p. 520.

The weight is `w x = x ^ 2 + x ^ (-2)`. This file sets up the weighted space
`L²(ℝ, w (x) dx)`, the weighted band inside it, and the unitary that carries the computation of
the trace to the Paley–Wiener picture of `Sec4_WeightedBandTrace`.

* `weightedBandMeasure`: the measure `w (x) dx`. It and Lebesgue measure have the same null
  sets.
* `weightedBandUnitary`: multiplication by `μ x = (x ^ 2 - i) / x`, a unitary of the weighted
  space onto `L²(ℝ)`, since `|μ| ^ 2 = w`.
* `weightedBandInclusion`: the inclusion of the weighted space in `L²(ℝ)`, bounded since
  `w ≥ 2`.
* `weightedBand Y`: the functions of the level `realPWLevel Y` of the project that have finite
  weighted norm, as a closed subspace of the weighted space.
* `weightedBandCutoff L`, `weightedBandDilation g`: the sharp spatial cutoff and the dilation
  on the weighted space. They are defined through the unitary, and
  `coeFn_weightedBandCutoff`, `coeFn_weightedBandDilation` prove that they are the
  multiplication by `1_[-L, L]` and the map `f ↦ g^(-1/2) f (x / g)`. The unitary carries them
  to the cutoff of `L²(ℝ)` and to the dilation with its multiplier `r_g`.
* `weightedBand_map_eq_of`: the unitary carries the weighted band onto `weightedPWBand Y` as
  soon as two statements about functions of `L²(ℝ)` hold.
* `tendsto_hilbertTrace_weightedBand_compression_of_map`: when the unitary carries the weighted
  band onto `weightedPWBand Y`, the compression `P ∘ M_L ∘ D_g ∘ P` on the weighted space is
  nuclear and its Hilbert trace tends to `g ^ (3/2) / (g ^ 2 - 1) - g ^ (-1/2)` as `L → ∞`, at
  every fixed `Y > 0` and `g > 1`.

**Not formalized here.** The two statements in `L²(ℝ)` that `weightedBand_map_eq_of` asks for
(multiplying a function of the level by `μ` gives an odd function of the band that vanishes at
`ζ`, and conversely) are proved in the files that import this one.
-/

open MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate InnerProductSpace ENNReal NNReal

@[expose] public noncomputable section

namespace RiemannMasullo

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

/-! ### The weighted measure -/

/-- Almost every real number is not zero. -/
theorem ae_ne_zero_real : ∀ᵐ x : ℝ, x ≠ 0 :=
  compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))

/-- The weight is measurable. -/
theorem measurable_weightedBandWeight : Measurable weightedBandWeight := by
  unfold weightedBandWeight
  fun_prop

/-- The weight is positive off the origin. -/
theorem weightedBandWeight_pos {x : ℝ} (hx : x ≠ 0) : 0 < weightedBandWeight x := by
  unfold weightedBandWeight
  positivity

/-- The weight is at least `2` off the origin. -/
theorem two_le_weightedBandWeight {x : ℝ} (hx : x ≠ 0) : 2 ≤ weightedBandWeight x := by
  have hx2 : 0 < x ^ 2 := by positivity
  have h : weightedBandWeight x - 2 = (x ^ 2 - 1) ^ 2 / x ^ 2 := by
    unfold weightedBandWeight
    field_simp
    ring
  have h0 : 0 ≤ (x ^ 2 - 1) ^ 2 / x ^ 2 := by positivity
  linarith

/-- The factor `μ` is measurable. -/
theorem measurable_weightedBandFactor : Measurable weightedBandFactor := by
  unfold weightedBandFactor
  fun_prop

/-- The weight as a function with values in the nonnegative reals. -/
def weightedBandWeightNN (x : ℝ) : ℝ≥0 := Real.toNNReal (weightedBandWeight x)

/-- The weight with values in the nonnegative reals is measurable. -/
theorem measurable_weightedBandWeightNN : Measurable weightedBandWeightNN :=
  measurable_weightedBandWeight.real_toNNReal

/-- The measure `w (x) dx` on the line, with `w x = x ^ 2 + x ^ (-2)`. -/
def weightedBandMeasure : Measure ℝ :=
  volume.withDensity fun x ↦ ENNReal.ofReal (weightedBandWeight x)

/-- The weighted measure, with the density written in the nonnegative reals. -/
theorem weightedBandMeasure_eq :
    weightedBandMeasure = volume.withDensity fun x ↦ (weightedBandWeightNN x : ℝ≥0∞) := rfl

/-- The weighted measure is absolutely continuous with respect to Lebesgue measure. -/
theorem weightedBandMeasure_absolutelyContinuous : weightedBandMeasure ≪ volume :=
  withDensity_absolutelyContinuous _ _

/-- Lebesgue measure is absolutely continuous with respect to the weighted measure. -/
theorem volume_absolutelyContinuous_weightedBandMeasure :
    (volume : Measure ℝ) ≪ weightedBandMeasure :=
  withDensity_absolutelyContinuous' measurable_weightedBandWeight.ennreal_ofReal.aemeasurable
    (ae_ne_zero_real.mono fun x hx ↦ by
      simpa using weightedBandWeight_pos hx)

local notation "Hw" => Lp ℂ 2 weightedBandMeasure

/-! ### Multiplication by `μ` is a unitary of the weighted space onto `L²(ℝ)` -/

/-- A function is square-integrable for the weighted measure exactly when its product with `μ`
is square-integrable for Lebesgue measure. -/
theorem memLp_weightedBandMeasure_iff {f : ℝ → ℂ} (hf : StronglyMeasurable f) :
    MemLp f 2 weightedBandMeasure ↔ MemLp (fun x ↦ weightedBandFactor x * f x) 2 volume := by
  have hcf : StronglyMeasurable fun x ↦ weightedBandFactor x * f x :=
    measurable_weightedBandFactor.stronglyMeasurable.mul hf
  rw [memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable,
    memLp_two_iff_integrable_sq_norm hcf.aestronglyMeasurable, weightedBandMeasure_eq,
    integrable_withDensity_iff_integrable_smul measurable_weightedBandWeightNN]
  refine integrable_congr ?_
  filter_upwards [ae_ne_zero_real] with x hx
  rw [NNReal.smul_def, smul_eq_mul, weightedBandWeightNN,
    Real.coe_toNNReal _ (weightedBandWeight_pos hx).le, norm_mul, mul_pow,
    norm_sq_weightedBandFactor hx]

/-- The product of a vector of the weighted space with `μ`, as a vector of `L²(ℝ)`. -/
def weightedBandMulVector (f : Hw) : H :=
  ((memLp_weightedBandMeasure_iff (Lp.stronglyMeasurable f)).mp (Lp.memLp f)).toLp _

/-- The product with `μ` is the class of `x ↦ μ x * f x`. -/
theorem coeFn_weightedBandMulVector (f : Hw) :
    (weightedBandMulVector f : ℝ → ℂ) =ᵐ[volume] fun x ↦ weightedBandFactor x * f x :=
  MemLp.coeFn_toLp _

/-- Multiplication by `μ` as a linear map from the weighted space to `L²(ℝ)`. -/
def weightedBandMulLinear : Hw →ₗ[ℂ] H where
  toFun := weightedBandMulVector
  map_add' f f' := by
    refine Lp.ext ?_
    filter_upwards [coeFn_weightedBandMulVector (f + f'), coeFn_weightedBandMulVector f,
      coeFn_weightedBandMulVector f',
      volume_absolutelyContinuous_weightedBandMeasure.ae_le (Lp.coeFn_add f f'),
      Lp.coeFn_add (weightedBandMulVector f) (weightedBandMulVector f')] with x h1 h2 h3 h4 h5
    rw [h1, h5, Pi.add_apply, h4, Pi.add_apply, h2, h3, mul_add]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [coeFn_weightedBandMulVector (c • f), coeFn_weightedBandMulVector f,
      volume_absolutelyContinuous_weightedBandMeasure.ae_le (Lp.coeFn_smul c f),
      Lp.coeFn_smul c (weightedBandMulVector f)] with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h4, Pi.smul_apply, h3, Pi.smul_apply, h2, smul_eq_mul,
      smul_eq_mul]
    ring

/-- Multiplication by `μ` preserves the norm. -/
theorem norm_weightedBandMulVector (f : Hw) : ‖weightedBandMulVector f‖ = ‖f‖ := by
  have hi : inner ℂ (weightedBandMulVector f) (weightedBandMulVector f) = inner ℂ f f := by
    rw [L2.inner_def, L2.inner_def]
    change _ = ∫ x, inner ℂ (f x) (f x)
      ∂(volume.withDensity fun x ↦ (weightedBandWeightNN x : ℝ≥0∞))
    rw [integral_withDensity_eq_integral_smul measurable_weightedBandWeightNN]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_weightedBandMulVector f, ae_ne_zero_real] with x hx hx0
    change inner ℂ (weightedBandMulVector f x) (weightedBandMulVector f x) =
      weightedBandWeightNN x • inner ℂ (f x) (f x)
    rw [hx, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    simp only [norm_mul, NNReal.smul_def, Complex.real_smul]
    have h := congrArg Complex.ofReal
      (show (‖weightedBandFactor x‖ * ‖f x‖) ^ 2 =
          (weightedBandWeightNN x : ℝ) * ‖f x‖ ^ 2 by
        rw [mul_pow, norm_sq_weightedBandFactor hx0, weightedBandWeightNN,
          Real.coe_toNNReal _ (weightedBandWeight_pos hx0).le])
    change (Complex.ofReal (‖weightedBandFactor x‖ * ‖f x‖)) ^ 2 =
      Complex.ofReal (weightedBandWeightNN x : ℝ) * Complex.ofReal ‖f x‖ ^ 2
    rw [Complex.ofReal_mul]
    simpa only [Complex.ofReal_mul, Complex.ofReal_pow] using h
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hi
  have hsq : ‖weightedBandMulVector f‖ ^ 2 = ‖f‖ ^ 2 := by exact_mod_cast hi
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Multiplication by `μ` as a linear isometry from the weighted space to `L²(ℝ)`. -/
def weightedBandMulIsometry : Hw →ₗᵢ[ℂ] H :=
  ⟨weightedBandMulLinear, norm_weightedBandMulVector⟩

/-- Multiplication by `μ` is onto `L²(ℝ)`. -/
theorem surjective_weightedBandMulIsometry : Function.Surjective weightedBandMulIsometry := by
  intro h
  have hsm : StronglyMeasurable fun x ↦ (h : ℝ → ℂ) x / weightedBandFactor x :=
    (Lp.stronglyMeasurable h).div measurable_weightedBandFactor.stronglyMeasurable
  have hae : (h : ℝ → ℂ) =ᵐ[volume] fun x ↦
      weightedBandFactor x * ((h : ℝ → ℂ) x / weightedBandFactor x) := by
    filter_upwards [ae_ne_zero_real] with x hx
    rw [mul_div_cancel₀ _ (weightedBandFactor_ne_zero hx)]
  have hg : MemLp (fun x ↦ (h : ℝ → ℂ) x / weightedBandFactor x) 2 weightedBandMeasure :=
    (memLp_weightedBandMeasure_iff hsm).mpr ((Lp.memLp h).ae_eq hae)
  refine ⟨hg.toLp _, Lp.ext ?_⟩
  filter_upwards [coeFn_weightedBandMulVector (hg.toLp _),
    volume_absolutelyContinuous_weightedBandMeasure.ae_le hg.coeFn_toLp, hae] with x h1 h2 h3
  change weightedBandMulVector (hg.toLp _) x = h x
  rw [h1, h2, ← h3]

/-- **Multiplication by `μ` is a unitary of the weighted space onto `L²(ℝ)`.** -/
def weightedBandUnitary : Hw ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective weightedBandMulIsometry surjective_weightedBandMulIsometry

/-- The unitary is the multiplication by `μ`. -/
theorem coeFn_weightedBandUnitary (f : Hw) :
    (weightedBandUnitary f : ℝ → ℂ) =ᵐ[volume] fun x ↦ weightedBandFactor x * f x :=
  coeFn_weightedBandMulVector f

/-- The inverse of the unitary is the division by `μ`. -/
theorem coeFn_weightedBandUnitary_symm (h : H) :
    (weightedBandUnitary.symm h : ℝ → ℂ) =ᵐ[volume] fun x ↦ h x / weightedBandFactor x := by
  have h1 := coeFn_weightedBandUnitary (weightedBandUnitary.symm h)
  rw [LinearIsometryEquiv.apply_symm_apply] at h1
  filter_upwards [h1, ae_ne_zero_real] with x hx hx0
  rw [hx, mul_div_cancel_left₀ _ (weightedBandFactor_ne_zero hx0)]

/-! ### The inclusion of the weighted space in `L²(ℝ)` and the weighted band -/

/-- The inverse of `μ` is bounded by `1`. -/
theorem norm_inv_weightedBandFactor_le (x : ℝ) : ‖(weightedBandFactor x)⁻¹‖ ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [weightedBandFactor]
  · have h2 := norm_sq_weightedBandFactor hx
    have h3 := two_le_weightedBandWeight hx
    have h1 : 1 ≤ ‖weightedBandFactor x‖ := by
      by_contra hlt
      have hlt' : ‖weightedBandFactor x‖ < 1 := not_le.mp hlt
      have : ‖weightedBandFactor x‖ ^ 2 < 1 := by
        have h0 := norm_nonneg (weightedBandFactor x)
        nlinarith
      linarith
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ h1

/-- The inclusion of the weighted space in `L²(ℝ)`: the unitary followed by the multiplication
by `1 / μ`, which is bounded since the weight is at least `2`. -/
def weightedBandInclusion : Hw →L[ℂ] H :=
  realMultiplier (fun x ↦ (weightedBandFactor x)⁻¹) ∘L
    weightedBandUnitary.toLinearIsometry.toContinuousLinearMap

/-- The inclusion does not change the function. -/
theorem coeFn_weightedBandInclusion (f : Hw) :
    (weightedBandInclusion f : ℝ → ℂ) =ᵐ[volume] (f : ℝ → ℂ) := by
  have h1 := coeFn_realMultiplier (r := fun x ↦ (weightedBandFactor x)⁻¹)
    measurable_weightedBandFactor.inv norm_inv_weightedBandFactor_le (weightedBandUnitary f)
  filter_upwards [h1, coeFn_weightedBandUnitary f, ae_ne_zero_real] with x e1 e2 hx
  change (realMultiplier (fun x ↦ (weightedBandFactor x)⁻¹) (weightedBandUnitary f) : ℝ → ℂ) x
    = _
  rw [e1, e2, inv_mul_cancel_left₀ (weightedBandFactor_ne_zero hx)]

/-- Paper: Definition 11.2.1.1, pp. 487–488, with the weight `x ^ 2 + x ^ (-2)`. The weighted
band: the functions of the level of the rational real-place model at order zero that have
finite weighted norm, as a subspace of the weighted space.
Reconstruction: the level is `realPWLevel Y`, the even functions of the band `[-Y, Y]` that
vanish at the origin. -/
def weightedBand (Y : ℝ) : Submodule ℂ Hw :=
  (realPWLevel Y).comap weightedBandInclusion.toLinearMap

/-- Membership in the weighted band. -/
theorem mem_weightedBand_iff {Y : ℝ} {f : Hw} :
    f ∈ weightedBand Y ↔ weightedBandInclusion f ∈ realPWLevel Y := Iff.rfl

/-- The weighted band is closed. -/
theorem isClosed_weightedBand (Y : ℝ) : IsClosed (weightedBand Y : Set Hw) :=
  (isClosed_realPWLevel Y).preimage weightedBandInclusion.continuous

/-- The weighted band is complete. -/
instance instCompleteSpaceWeightedBand (Y : ℝ) : CompleteSpace (weightedBand Y) :=
  (isClosed_weightedBand Y).completeSpace_coe

/-! ### The cutoff and the dilation on the weighted space -/

/-- The sharp spatial cutoff on the weighted space, defined through the unitary.
`coeFn_weightedBandCutoff` says that it is the multiplication by `1_[-L, L]`. -/
def weightedBandCutoff (L : ℝ) : Hw →L[ℂ] Hw :=
  weightedBandUnitary.symm.toLinearIsometry.toContinuousLinearMap ∘L realCutoff L ∘L
    weightedBandUnitary.toLinearIsometry.toContinuousLinearMap

/-- The dilation on the weighted space, defined through the unitary.
`coeFn_weightedBandDilation` says that it is `f ↦ g^(-1/2) f (x / g)`. -/
def weightedBandDilation (g : ℝ) : Hw →L[ℂ] Hw :=
  weightedBandUnitary.symm.toLinearIsometry.toContinuousLinearMap ∘L weightedPWDilation g ∘L
    weightedBandUnitary.toLinearIsometry.toContinuousLinearMap

/-- The unitary carries the cutoff of the weighted space to the cutoff of `L²(ℝ)`. -/
theorem weightedBandUnitary_weightedBandCutoff (L : ℝ) (f : Hw) :
    weightedBandUnitary (weightedBandCutoff L f) = realCutoff L (weightedBandUnitary f) :=
  LinearIsometryEquiv.apply_symm_apply _ _

/-- The unitary carries the dilation of the weighted space to the dilation with its
multiplier. -/
theorem weightedBandUnitary_weightedBandDilation (g : ℝ) (f : Hw) :
    weightedBandUnitary (weightedBandDilation g f) =
      weightedPWDilation g (weightedBandUnitary f) :=
  LinearIsometryEquiv.apply_symm_apply _ _

/-- **The cutoff of the weighted space is the multiplication by `1_[-L, L]`.** -/
theorem coeFn_weightedBandCutoff (L : ℝ) (f : Hw) :
    (weightedBandCutoff L f : ℝ → ℂ) =ᵐ[volume] (Icc (-L) L).indicator (f : ℝ → ℂ) := by
  have h1 := coeFn_weightedBandUnitary_symm (realCutoff L (weightedBandUnitary f))
  filter_upwards [h1, coeFn_realCutoff L (weightedBandUnitary f), coeFn_weightedBandUnitary f,
    ae_ne_zero_real] with x e1 e2 e3 hx
  change (weightedBandUnitary.symm (realCutoff L (weightedBandUnitary f)) : ℝ → ℂ) x = _
  rw [e1, e2]
  by_cases hmem : x ∈ Icc (-L) L
  · rw [indicator_of_mem hmem, indicator_of_mem hmem, e3,
      mul_div_cancel_left₀ _ (weightedBandFactor_ne_zero hx)]
  · rw [indicator_of_notMem hmem, indicator_of_notMem hmem, zero_div]

/-- **The dilation of the weighted space is `f ↦ g^(-1/2) f (x / g)`.** -/
theorem coeFn_weightedBandDilation {g : ℝ} (hg : 1 ≤ g) (f : Hw) :
    (weightedBandDilation g f : ℝ → ℂ) =ᵐ[volume] fun x ↦
      (((√g)⁻¹ : ℝ) : ℂ) * (f : ℝ → ℂ) (x / g) := by
  have hg0 : 0 < g := by linarith
  have h1 := coeFn_weightedBandUnitary_symm (weightedPWDilation g (weightedBandUnitary f))
  have h2 := coeFn_weightedPWDilation hg (weightedBandUnitary f)
  have h3 := coeFn_realDilation hg0 (weightedBandUnitary f)
  have h4 := (quasiMeasurePreserving_div_const_real hg0).ae_eq_comp (coeFn_weightedBandUnitary f)
  filter_upwards [h1, h2, h3, h4, ae_ne_zero_real] with x e1 e2 e3 e4 hx
  have e4' : (weightedBandUnitary f : ℝ → ℂ) (x / g) =
      weightedBandFactor (x / g) * (f : ℝ → ℂ) (x / g) := e4
  change (weightedBandUnitary.symm (weightedPWDilation g (weightedBandUnitary f)) : ℝ → ℂ) x = _
  have hne : weightedDilationMultiplier g x * weightedBandFactor (x / g) ≠ 0 := by
    rw [weightedDilationMultiplier_mul_weightedBandFactor hg0.ne' hx]
    exact weightedBandFactor_ne_zero hx
  rw [e1, e2, e3, e4', ← weightedDilationMultiplier_mul_weightedBandFactor hg0.ne' hx,
    show weightedDilationMultiplier g x * ((((√g)⁻¹ : ℝ) : ℂ) *
        (weightedBandFactor (x / g) * (f : ℝ → ℂ) (x / g))) =
      weightedDilationMultiplier g x * weightedBandFactor (x / g) *
        ((((√g)⁻¹ : ℝ) : ℂ) * (f : ℝ → ℂ) (x / g)) by ring,
    mul_div_cancel_left₀ _ hne]

/-! ### The image of the weighted band and the transport of the trace -/

/-- **The image of the weighted band, reduced to two statements in `L²(ℝ)`.** The unitary
carries the weighted band onto `weightedPWBand Y` as soon as: multiplying a function of the
level by `μ` gives a function of `weightedPWBand Y`, and dividing a function of
`weightedPWBand Y` by `μ` gives a function of the level. -/
theorem weightedBand_map_eq_of {Y : ℝ}
    (h1 : ∀ F h : H, F ∈ realPWLevel Y →
      (∀ᵐ x, (h : ℝ → ℂ) x = weightedBandFactor x * (F : ℝ → ℂ) x) → h ∈ weightedPWBand Y)
    (h2 : ∀ h F : H, h ∈ weightedPWBand Y →
      (∀ᵐ x, (F : ℝ → ℂ) x = (h : ℝ → ℂ) x / weightedBandFactor x) → F ∈ realPWLevel Y) :
    (weightedBand Y).map weightedBandUnitary.toLinearIsometry.toLinearMap =
      weightedPWBand Y := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨f, hf, rfl⟩
    refine h1 (weightedBandInclusion f) _ hf ?_
    filter_upwards [coeFn_weightedBandUnitary f, coeFn_weightedBandInclusion f] with x e1 e2
    change (weightedBandUnitary f : ℝ → ℂ) x = _
    rw [e1, e2]
  · intro h hh
    refine ⟨weightedBandUnitary.symm h, ?_, LinearIsometryEquiv.apply_symm_apply _ _⟩
    refine h2 h _ hh ?_
    filter_upwards [coeFn_weightedBandInclusion (weightedBandUnitary.symm h),
      coeFn_weightedBandUnitary_symm h] with x e1 e2
    exact e1.trans e2

/-- When the unitary carries the weighted band onto `weightedPWBand Y`, it carries the
orthogonal projection onto the first to the orthogonal projection onto the second. -/
theorem weightedBandUnitary_starProjection {Y : ℝ}
    (hmap : (weightedBand Y).map weightedBandUnitary.toLinearIsometry.toLinearMap =
      weightedPWBand Y) (f : Hw) :
    weightedBandUnitary ((weightedBand Y).starProjection f) =
      (weightedPWBand Y).starProjection (weightedBandUnitary f) := by
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · rw [← hmap]
    exact Submodule.mem_map_of_mem (Submodule.starProjection_apply_mem (weightedBand Y) f)
  · intro w hw
    rw [← hmap] at hw
    obtain ⟨k, hk, rfl⟩ := hw
    rw [← map_sub]
    change ⟪weightedBandUnitary (f - (weightedBand Y).starProjection f),
      weightedBandUnitary k⟫_ℂ = 0
    rw [LinearIsometryEquiv.inner_map_map]
    exact Submodule.starProjection_inner_eq_zero f k hk

/-- **The trace on the weighted space is the trace in the Paley–Wiener picture.** When the
unitary carries the weighted band onto `weightedPWBand Y`, the compression of the cutoff
dilation to the weighted band is nuclear on the weighted space and has the Hilbert trace of
the compression in `L²(ℝ)`. -/
theorem hilbertTrace_weightedBand_compression_of_map {Y g : ℝ} (hY : 0 < Y) (hg : 1 < g)
    (hmap : (weightedBand Y).map weightedBandUnitary.toLinearIsometry.toLinearMap =
      weightedPWBand Y) (L : ℝ) :
    ∃ hn : IsNuclearOperator ((weightedBand Y).starProjection ∘L
        (weightedBandCutoff L ∘L weightedBandDilation g) ∘L (weightedBand Y).starProjection),
      hilbertTrace ⟨_, hn⟩ =
        hilbertTrace ⟨(weightedPWBand Y).starProjection ∘L
          (realCutoff L ∘L weightedPWDilation g) ∘L (weightedPWBand Y).starProjection,
          isNuclearOperator_weightedPWBand_compression hY hg L⟩ := by
  have hint : weightedBandUnitary.toLinearIsometry.toContinuousLinearMap ∘L
      ((weightedBand Y).starProjection ∘L
        (weightedBandCutoff L ∘L weightedBandDilation g) ∘L (weightedBand Y).starProjection) =
      ((weightedPWBand Y).starProjection ∘L
        (realCutoff L ∘L weightedPWDilation g) ∘L (weightedPWBand Y).starProjection) ∘L
      weightedBandUnitary.toLinearIsometry.toContinuousLinearMap := by
    ext1 f
    change weightedBandUnitary ((weightedBand Y).starProjection
      (weightedBandCutoff L (weightedBandDilation g ((weightedBand Y).starProjection f)))) =
      (weightedPWBand Y).starProjection (realCutoff L (weightedPWDilation g
        ((weightedPWBand Y).starProjection (weightedBandUnitary f))))
    rw [weightedBandUnitary_starProjection hmap, weightedBandUnitary_weightedBandCutoff,
      weightedBandUnitary_weightedBandDilation, weightedBandUnitary_starProjection hmap]
  have h0 : ContinuousLinearMap.adjoint
      weightedBandUnitary.toLinearIsometry.toContinuousLinearMap ∘L
      weightedBandUnitary.toLinearIsometry.toContinuousLinearMap = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp
      weightedBandUnitary.toLinearIsometry.norm_map
  have hUU : weightedBandUnitary.toLinearIsometry.toContinuousLinearMap ∘L
      ContinuousLinearMap.adjoint weightedBandUnitary.toLinearIsometry.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ H := by
    ext1 y
    obtain ⟨f, rfl⟩ := weightedBandUnitary.surjective y
    have h1 : ContinuousLinearMap.adjoint
        weightedBandUnitary.toLinearIsometry.toContinuousLinearMap
        (weightedBandUnitary.toLinearIsometry.toContinuousLinearMap f) = f :=
      congrArg (fun A : Hw →L[ℂ] Hw ↦ A f) h0
    change weightedBandUnitary.toLinearIsometry.toContinuousLinearMap
      (ContinuousLinearMap.adjoint weightedBandUnitary.toLinearIsometry.toContinuousLinearMap
        (weightedBandUnitary.toLinearIsometry.toContinuousLinearMap f)) = _
    rw [h1]
    rfl
  have hrange : weightedBandUnitary.toLinearIsometry.toContinuousLinearMap ∘L
      (ContinuousLinearMap.adjoint weightedBandUnitary.toLinearIsometry.toContinuousLinearMap ∘L
        ((weightedPWBand Y).starProjection ∘L
          (realCutoff L ∘L weightedPWDilation g) ∘L (weightedPWBand Y).starProjection)) =
      (weightedPWBand Y).starProjection ∘L
        (realCutoff L ∘L weightedPWDilation g) ∘L (weightedPWBand Y).starProjection := by
    rw [← ContinuousLinearMap.comp_assoc, hUU, ContinuousLinearMap.id_comp]
  have h := hilbertTrace_eq_of_isometry_intertwining weightedBandUnitary.toLinearIsometry
    ⟨(weightedPWBand Y).starProjection ∘L
      (realCutoff L ∘L weightedPWDilation g) ∘L (weightedPWBand Y).starProjection,
      isNuclearOperator_weightedPWBand_compression hY hg L⟩
    ((weightedBand Y).starProjection ∘L
      (weightedBandCutoff L ∘L weightedBandDilation g) ∘L (weightedBand Y).starProjection)
    hint hrange
  exact h

/-- Paper: Theorem 12.4.1.1, pp. 514–519, and the value used on p. 520. **The trace over the
weighted band, on the weighted space, tends to `V_∞ - L₋` at every bandwidth**, when the unitary
carries the weighted band onto `weightedPWBand Y`. With `P` the orthogonal projection of the
weighted space onto the weighted band, `M_L` the sharp spatial cutoff and `D_g` the dilation,
the Hilbert trace of `P ∘ M_L ∘ D_g ∘ P` tends to `g ^ (3/2) / (g ^ 2 - 1) - g ^ (-1/2)` as
`L → ∞`, at every `Y > 0` and `g > 1`.
Reconstruction: the rational real-place model at order zero with the weight
`x ^ 2 + x ^ (-2)`. The hypothesis on the image of the weighted band is proved in the files
that import this one. -/
theorem tendsto_hilbertTrace_weightedBand_compression_of_map {Y g : ℝ} (hY : 0 < Y)
    (hg : 1 < g)
    (hmap : (weightedBand Y).map weightedBandUnitary.toLinearIsometry.toLinearMap =
      weightedPWBand Y) :
    ∃ hn : ∀ L : ℝ, IsNuclearOperator ((weightedBand Y).starProjection ∘L
        (weightedBandCutoff L ∘L weightedBandDilation g) ∘L (weightedBand Y).starProjection),
      Tendsto (fun L : ℝ ↦ hilbertTrace ⟨_, hn L⟩) atTop
        (𝓝 (((g ^ (3 / 2 : ℝ) / (g ^ 2 - 1) - (√g)⁻¹ : ℝ) : ℂ))) := by
  have h := fun L : ℝ ↦ hilbertTrace_weightedBand_compression_of_map hY hg hmap L
  refine ⟨fun L ↦ (h L).choose, ?_⟩
  refine (tendsto_hilbertTrace_weightedPWBand_compression hY hg).congr fun L ↦ ?_
  exact (h L).choose_spec.symm

end RiemannMasullo
