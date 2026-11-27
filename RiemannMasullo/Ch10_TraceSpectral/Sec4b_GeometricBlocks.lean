module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.ForMathlib.Analysis.Complex.BlaschkeSchwarz
import RiemannMasullo.ForMathlib.Analysis.MellinTransform.ExponentialMoments
import RiemannMasullo.Ch12_TraceGeometric.Sec5
import RiemannMasullo.ForMathlib.Analysis.Distribution.TestFunction.FirstMellinMoment

/-! # The geometric blocks of Theorem 10.4.3.5(2) at a simple zero

`Isolated.spectralStripGeometricKernel_blocks_bddAbove` of `Sec4b_Isolated` (#7406) says that the
finite sums of the geometric blocks `R_z = ∑ₘ f_{z,m}(q ·) • P^geom_a(A(φ)(S_a x_{z,m}))` over the
zeros of the strip are bounded in trace norm. This file proves what one block costs.

At a zero `z` with one retained jet the block is the rank-one operator
`f_z(q ·) • (A(φ) h_z − M_φ(z) h_z)`, where `h_z = S_a x_z` is the orthogonal lift of the
biorthogonal vector. The output `A(φ) h_z − M_φ(z) h_z` lies in the closed theta subspace, so
every retained jet vanishes on it. The jet of order one at `z`, which is not retained at a
simple zero, does not: by the Leibniz rule for the Mellin transform of a convolution it takes
the value `M_φ'(z)`, the derivative of the Mellin transform of the test at the zero. Hence

`‖M_φ'(z)‖ · ‖f_z ∘ q‖ ≤ ‖d_z − v‖ · ‖R_z‖₁`

for the jet `d_z` of order one at `z` and every `v` in the span of the retained jets, both in the
reciprocal-weight space (`spectralStripGeometricKernel_block_traceNorm_ge`). At a simple zero in
the open strip the jet of order one exists there (`exists_spectralZeroJet_one_dual`).

Under the bound of #7406 this gives one constant `B` with
`‖M_φ'(z)‖ · ‖f_z ∘ q‖ ≤ B · ‖d_z − v‖` at every such zero
(`spectralStripGeometricKernel_blocks_bddAbove_forces_firstJet_separation`). For a second zero
`w` of the same character, `v = (w − z)⁻¹ • (u_w − u_z)` is a difference quotient of retained
jets, and `d_z − v` is a Taylor remainder of the order of `|w − z|` in the reciprocal-weight
space (not proved in this file). So at positive width the bound of #7406 forces the zeros in the
open strip apart at the rate of `M_φ'`, as `spectralStripConvolution_traceCauchy_compact_block_series`
(#7241) does for the quotient blocks. On the line, at Sobolev orders `s ≤ 3`, the jet of order
one is not in the reciprocal-weight space and the inequality gives no constraint.

For a simple interior zero, the trace norm bound also detects the complete divisor in a disk
about the zero. Dividing the Mellin transform of the theta output by the finite Blaschke
product gives the estimate for a single test. Applying uniform boundedness to first moments
of actual compact Bruhat tests gives an inverse-polynomial lower bound for the product at
all simple centers of a fixed character and fixed interior margin.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.GeometricBaire

open Function MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F

/-- The full inverse of a fixed character cancels its angular and radial factors when a
smooth profile of the log norm is realized as a compact Bruhat test. -/
private theorem ideleFirstMoment_polynomial {I : Type*} (η : PontryaginDual C𝔽)
    {A : ℝ} (b t w : I → ℝ) (hb : ∀ i, |b i| ≤ A) (hw : ∀ i, 0 ≤ w i)
    (h : ∀ φ : BruhatCompactSupport C𝔽, BddAbove (range fun i ↦ w i *
      ‖∫ g : C𝔽, φ.val g * spectralZeroJet η (b i) (t i) 1 g ∂μ𝔽‖)) :
    ∃ C ≥ (0 : ℝ), ∃ N : ℕ, ∀ i, w i ≤ C * (1 + |t i|) ^ N := by
  let l := logIdeleClassNorm F
  have hl : l = fun g : C𝔽 ↦ (positiveRealLogEquiv (ideleClassNorm F g)).toAdd :=
    funext fun g ↦ (positiveRealLogEquiv_apply _).symm
  have hlp : IsProperMap l := by
    rw [hl]
    exact positiveRealLogEquiv.toHomeomorph.isProperMap.comp (isProperMap_ideleClassNorm F)
  have hls : Surjective l := by
    let q : IdeleGroup (𝓞 F) F →* C𝔽 := QuotientGroup.mk' _
    have hτ : RightInverse (q.comp (canonicalIdeleNormSection F)) (ideleClassNorm F) :=
      canonicalIdeleNormSection_rightInverse F
    rw [hl]
    exact positiveRealLogEquiv.surjective.comp hτ.surjective
  let ν := (μ𝔽).map l
  let : IsFiniteMeasureOnCompacts ν := ⟨fun K hK ↦ by
    change (μ𝔽).map l K < ⊤
    rw [Measure.map_apply hlp.continuous.measurable hK.measurableSet]
    exact (hlp.isCompact_preimage hK).measure_lt_top⟩
  let : ν.IsOpenPosMeasure := hlp.continuous.isOpenPosMeasure_map hls
  apply FirstMellinMoment.radialFirstMoment_polynomial ν b t w hb hw
  intro f
  obtain ⟨φ, hφ⟩ := exists_characterNormTest (F := F) η⁻¹ f f.contDiff f.hasCompactSupport
  have hform (g : C𝔽) : φ.val g = (η g : ℂ)⁻¹ * f (l g) := by
    rw [hφ]
    exact congrArg (· * f (l g)) (Circle.coe_inv _)
  obtain ⟨D, hD⟩ := h φ
  refine ⟨D, forall_mem_range.mpr fun i ↦ ?_⟩
  let phase (x : ℝ) := Complex.exp (((t i : ℂ) * Complex.I) * x)
  let K (x : ℝ) := ((x * Real.exp (b i * x) : ℝ) : ℂ) * phase x
  have hK : Continuous K := by
    dsimp [K, phase]
    fun_prop
  have hμ : (∫ x, f x * K x ∂ν) =
      ∫ g : C𝔽, φ.val g * spectralZeroJet η (b i) (t i) 1 g ∂μ𝔽 := by
    trans ∫ g : C𝔽, f (l g) * K (l g) ∂μ𝔽
    · exact integral_map (μ := μ𝔽) (φ := l) (f := fun x ↦ f x * K x)
        hlp.continuous.measurable.aemeasurable (f.continuous.mul hK).aestronglyMeasurable
    apply integral_congr_ae (.of_forall fun g ↦ ?_)
    have hp : 0 < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    have ht : ideleClassNormTwist η ((b i : ℂ) + (t i : ℂ) * Complex.I) g =
        (η g : ℂ) * ((Real.exp (b i * l g) : ℂ) * phase (l g)) := by
      change (η g : ℂ) * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^
        ((b i : ℂ) + (t i : ℂ) * Complex.I)) = _
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
        ← Complex.ofReal_log hp.le, Complex.ofReal_exp]
      dsimp only [phase]
      rw [← Complex.exp_add]
      congr 2
      change (l g : ℂ) * _ = _
      rw [Complex.ofReal_mul]
      ring
    rw [spectralZeroJet, ht, pow_one, hform]
    change f (l g) * K (l g) = _ * (_ * (l g : ℂ))
    simp only [K, Complex.ofReal_mul]
    field_simp [Circle.coe_ne_zero]
  change w i * ‖∫ x, f x * K x ∂ν‖ ≤ D
  rw [hμ]
  exact hD (mem_range_self i)

/-- On one fixed Hecke character, a positive denominator dominating the first Mellin moment
of every compact Bruhat test is bounded below by one inverse polynomial in the height. -/
theorem ideleFirstMoment_denominator_lower {I : Type*} (η : PontryaginDual C𝔽)
    {A : ℝ} (b t P : I → ℝ) (hb : ∀ i, |b i| ≤ A) (hP : ∀ i, 0 < P i)
    (h : ∀ φ : BruhatCompactSupport C𝔽, ∃ D : ℝ, ∀ i,
      ‖∫ g : C𝔽, φ.val g * spectralZeroJet η (b i) (t i) 1 g ∂μ𝔽‖ ≤ D * P i) :
    ∃ c > (0 : ℝ), ∃ N : ℕ, ∀ i, c / (1 + |t i|) ^ N ≤ P i := by
  obtain ⟨C, hC, N, hN⟩ := ideleFirstMoment_polynomial η b t (fun i ↦ (P i)⁻¹) hb
    (fun i ↦ (inv_pos.mpr (hP i)).le) (fun φ ↦ by
      obtain ⟨D, hD⟩ := h φ
      refine ⟨D, forall_mem_range.mpr fun i ↦ ?_⟩
      rw [inv_mul_eq_div]
      exact (div_le_iff₀ (hP i)).mpr (hD i))
  refine ⟨(C + 1)⁻¹, by positivity, N, fun i ↦ ?_⟩
  have hle : (P i)⁻¹ ≤ (C + 1) * (1 + |t i|) ^ N :=
    (hN i).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  simpa [div_eq_mul_inv, mul_comm] using inv_le_of_inv_le₀ (hP i) hle

end RiemannMasullo.GeometricBaire

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

section Abstract

/-- A vector `A h − μ h` of a subspace `Θ` has norm at least `‖c‖ / ‖d − v‖`, when the functional
of `d` satisfies the Leibniz identity `d(A h) = c + μ · d(h)` and `v` lies in the span of vectors
whose functionals vanish on `Θ`. -/
private theorem geometricBlock_norm_ge_abstract {W W' ι : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup W'] [NormedSpace ℂ W']
    (T : StrongDual ℂ W ≃ₗᵢ[ℂ] W') (Θ : Submodule ℂ W) (A : W →L[ℂ] W) (h : W) (μ c : ℂ)
    (hΘ : A h - μ • h ∈ Θ) (d : W')
    (hd : (T.symm d) (A h) = c + μ * (T.symm d) h)
    (u : ι → W') (hu : ∀ i, ∀ w ∈ Θ, (T.symm (u i)) w = 0)
    (v : W') (hv : v ∈ Submodule.span ℂ (range u)) :
    ‖c‖ ≤ ‖d - v‖ * ‖A h - μ • h‖ := by
  have hvΘ : ∀ w ∈ Θ, (T.symm v) w = 0 := by
    intro w hw
    refine Submodule.span_induction (p := fun v _ ↦ (T.symm v) w = 0) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨i, rfl⟩
      exact hu i w hw
    · rw [map_zero, zero_apply]
    · intro v₁ v₂ _ _ h₁ h₂
      rw [map_add, add_apply, h₁, h₂, add_zero]
    · intro r v₁ _ h₁
      rw [map_smul, smul_apply, h₁, smul_zero]
  have hsplit : T.symm (d - v) = T.symm d - T.symm v := map_sub T.symm d v
  have hval : (T.symm (d - v)) (A h - μ • h) = c := by
    rw [hsplit]
    change (T.symm d) (A h - μ • h) - (T.symm v) (A h - μ • h) = c
    rw [hvΘ _ hΘ, sub_zero, map_sub, map_smul, hd, smul_eq_mul]
    ring
  calc
    ‖c‖ = ‖(T.symm (d - v)) (A h - μ • h)‖ := by rw [hval]
    _ ≤ ‖T.symm (d - v)‖ * ‖A h - μ • h‖ := (T.symm (d - v)).le_opNorm _
    _ = ‖d - v‖ * ‖A h - μ • h‖ := by rw [T.symm.norm_map]

/-- Evaluation on a biorthogonal vector is determined by the coordinate functionals.
A copy of the private `spectralStripGeometricKernel_eq_of_coords` of `Sec4b_Isolated`. -/
private theorem geometricBlock_eq_of_coords
    {J Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (basis : J → Q) (coords : J → StrongDual ℂ Q) (h : IsSpectralMarkushevichBasis basis coords)
    {v w : Q} (heq : ∀ j, coords j v = coords j w) : v = w := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  have hall : ContinuousLinearMap.apply ℂ ℂ v = ContinuousLinearMap.apply ℂ ℂ w := by
    apply ContinuousLinearMap.ext_on h.2.2.2
    rintro _ ⟨j, rfl⟩
    exact heq j
  exact fun ℓ ↦ DFunLike.congr_fun hall ℓ

end Abstract

variable {F : Type*} [Field F] [NumberField F]
variable (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
  (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))
  (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (x : SpectralStripJetIndex χ a α s →
    spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) (zero_le_one.trans hs.le))
  (f : SpectralStripJetIndex χ a α s → StrongDual ℂ
    (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) (zero_le_one.trans hs.le)))

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hs₀" => (zero_le_one.trans hs.le)
local notation "hI" => (neg_nonpos.mpr hα).trans hα
local notation "W₀" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s
local notation "W₀'" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s true
local notation "Θ₀" => globalThetaSobolev F a hI hs₀
local notation "H₀" => spectralSobolevQuotient F a hI hs₀
local notation "Sₐ(" v ")" => ((Θ₀).quotientEquivOrthogonal v).val
local notation "Aφ" => hardySobolevTestAction μ𝔽 m𝔽 (-α) α s hI hs₀ φ
local notation "Gₐ" => geometricProjection (F := F) a hα hs₀
local notation "Pₐ" => spectralProjection (F := F) a hα hs₀
local notation "Dₐ" => spectralSobolevDualEmbedding F a hI hs₀
local notation "Tₐ" => (modulatedIntervalSobolev_dual m𝔽
  (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
  μ𝔽 (-α) α s hI hs₀).exists.choose

local notation "order(" χ ", " a ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (χ (z).1))
  (((a + (z).2.1 : ℝ) : ℂ) + ((z).2.2 : ℂ) * Complex.I)
local notation "zeros(" F ", " χ ", " a ", " α ")" => {z : PontryaginDual (ideleClassNorm F).ker × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ, a, z)}
local notation "jetCount(" z ")" => spectralStripMultiplicity α s (z).val.2.1 (order(χ, a, (z).val)).untop₀.toNat
local notation "jets" => SpectralStripJetIndex (F := F) χ a α s
local notation "jet(" z ", " m ")" =>
  (⟨((z).val.1, (z).val.2.1, (z).val.2.2, (m).val), (m).isLt⟩ : jets)
local notation "stripU(" j ")" => (spectralStripJet_memLp χ hα hs₀ j).toLp
  (spectralZeroJet (F := F) (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2)
local notation "geometricBlock(" z ")" =>
  (∑ m : Fin (jetCount(z)),
    (⟨((f jet(z, m)).comp (Θ₀).mkQL).smulRight (Gₐ (Aφ (Sₐ(x jet(z, m))))),
      smulRight_mem_nuclearEndomorphisms _ _⟩ : nuclearEndomorphisms _))
local notation "valueJet(" z ")" => spectralZeroJet (F := F) (χ (z).val.1) (z).val.2.1 (z).val.2.2 0
local notation "firstJet(" z ")" => spectralZeroJet (F := F) (χ (z).val.1) (z).val.2.1 (z).val.2.2 1
local notation "mellinAt(" z ")" =>
  (∫ g : IdeleClassGroup (𝓞 F) F, φ.val g * ideleClassNormTwist (χ (z).val.1)
    (((z).val.2.1 : ℂ) + ((z).val.2.2 : ℂ) * Complex.I) g ∂ideleClassTamagawaMeasure F)

section Pairing

omit hs in
/-- The logarithm of the idele class norm is continuous. -/
private theorem continuous_logIdeleClassNorm : Continuous (logIdeleClassNorm F) :=
  (NNReal.continuous_coe.comp (Units.continuous_val.comp
    (isProperMap_ideleClassNorm F).continuous)).log
    fun g ↦ NNReal.coe_ne_zero.2 (ideleClassNorm F g).ne_zero

/-- The zero jets are continuous. -/
private theorem continuous_spectralZeroJet (η : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) :
    Continuous (spectralZeroJet η b t k) :=
  (ideleClassNormTwist η (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I)).continuous.mul
    ((Complex.continuous_ofReal.comp (continuous_logIdeleClassNorm (F := F))).pow k)

/-- The jet of order one at a product: the Leibniz rule for the logarithm of the norm. -/
private theorem spectralZeroJet_one_mul (η : PontryaginDual C𝔽) (b t : ℝ) (g y : C𝔽) :
    spectralZeroJet η b t 1 (g * y) =
      spectralZeroJet η b t 1 g * spectralZeroJet η b t 0 y +
        spectralZeroJet η b t 0 g * spectralZeroJet η b t 1 y := by
  have hlog : logIdeleClassNorm F (g * y) = logIdeleClassNorm F g + logIdeleClassNorm F y := by
    change Real.log ((ideleClassNorm F (g * y)).val : ℝ) =
      Real.log ((ideleClassNorm F g).val : ℝ) + Real.log ((ideleClassNorm F y).val : ℝ)
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.2 (ideleClassNorm F g).ne_zero)
      (NNReal.coe_ne_zero.2 (ideleClassNorm F y).ne_zero)]
  unfold spectralZeroJet
  rw [map_mul, hlog, Complex.ofReal_add]
  ring

/-- The Tamagawa measure is absolutely continuous for the measure of the reciprocal strip
weight. -/
private theorem ideleClassTamagawaMeasure_absolutelyContinuous_reciprocal (α s : ℝ) :
    μ𝔽 ≪ intervalSobolevMeasure μ𝔽 (logIdeleClassNorm F) (-α) α s true := by
  have hD : Measurable fun t : ℝ ↦ intervalSobolevDensity (-α) α s t := by
    unfold intervalSobolevDensity
    fun_prop
  have hlog : Measurable (logIdeleClassNorm F) := (continuous_logIdeleClassNorm (F := F)).measurable
  refine withDensity_absolutelyContinuous' ?_ (.of_forall fun g ↦ ?_)
  · simpa using (hD.comp hlog).inv.ennreal_ofReal.aemeasurable
  · simp only [ite_true]
    refine ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr ?_)
    unfold intervalSobolevDensity
    exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)

/-- A vector of the reciprocal-weight space that is a given function almost everywhere acts on
the strip space, through the Sobolev duality, by the integral against that function. -/
private theorem reciprocalDual_apply (d : W₀') (J : C𝔽 → ℂ) (hd : (d : C𝔽 → ℂ) =ᵐ[μ𝔽] J)
    (u : W₀) :
    Integrable (fun y ↦ u y * J y) μ𝔽 ∧ ((Tₐ).symm d) u = ∫ y, u y * J y ∂μ𝔽 := by
  have he : Integrable (fun g ↦ u g * Tₐ ((Tₐ).symm d) g) μ𝔽 ∧
      ((Tₐ).symm d) u = spectralSobolevPairing (F := F) u (Tₐ ((Tₐ).symm d)) :=
    spectralSobolevPairing_dual (F := F) hI hs₀ ((Tₐ).symm d) u
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  have hEq : (fun y ↦ u y * d y) =ᵐ[μ𝔽] fun y ↦ u y * J y :=
    hd.mono fun y hy ↦ congrArg (u y * ·) hy
  exact ⟨he.1.congr hEq, he.2.trans (integral_congr_ae hEq)⟩

/-- The moment of order one of a translate is the Leibniz combination of the moments of orders
zero and one. -/
private theorem integral_translation_mul_spectralZeroJet_one (η : PontryaginDual C𝔽) (b t : ℝ)
    (u : W₀)
    (h0 : Integrable (fun y ↦ u y * spectralZeroJet η b t 0 y) μ𝔽)
    (h1 : Integrable (fun y ↦ u y * spectralZeroJet η b t 1 y) μ𝔽) (g : C𝔽) :
    ∫ y, hardySobolevTranslation μ𝔽 m𝔽 (-α) α s hI hs₀ g u y * spectralZeroJet η b t 1 y ∂μ𝔽 =
      spectralZeroJet η b t 1 g * ∫ y, u y * spectralZeroJet η b t 0 y ∂μ𝔽 +
        spectralZeroJet η b t 0 g * ∫ y, u y * spectralZeroJet η b t 1 y ∂μ𝔽 := by
  let J := spectralZeroJet η b t 1
  let H (y : C𝔽) := u (g⁻¹ * y) * J y
  calc
    _ = ∫ y, H y ∂μ𝔽 := integral_congr_ae
      ((hardySobolevTranslation_apply μ𝔽 m𝔽 (-α) α s hI hs₀ g u).mono
        fun y hy ↦ congrArg (· * J y) hy)
    _ = ∫ y, H (g * y) ∂μ𝔽 := (integral_mul_left_eq_self H g).symm
    _ = ∫ y, u y * J (g * y) ∂μ𝔽 := by simp only [H, inv_mul_cancel_left]
    _ = ∫ y, (spectralZeroJet η b t 1 g * (u y * spectralZeroJet η b t 0 y) +
          spectralZeroJet η b t 0 g * (u y * spectralZeroJet η b t 1 y)) ∂μ𝔽 := by
      refine integral_congr_ae (.of_forall fun y ↦ ?_)
      change u y * spectralZeroJet η b t 1 (g * y) = _
      rw [spectralZeroJet_one_mul]
      ring
    _ = _ := by
      rw [integral_add (h0.const_mul _) (h1.const_mul _), integral_const_mul, integral_const_mul]

/-- The Leibniz rule for the test action against the jet of order one: for a vector `d` of
the reciprocal-weight space that is the jet of order one at a point, the functional of `d`
at `A(φ) u` is the first Mellin moment of the test times the moment of order zero of `u`, plus
the Mellin value of the test times the functional of `d` at `u`. -/
private theorem reciprocalDual_testAction_spectralZeroJet_one (η : PontryaginDual C𝔽) (b t : ℝ)
    (d : W₀') (hd : (d : C𝔽 → ℂ) =ᵐ[μ𝔽] spectralZeroJet η b t 1) (u : W₀)
    (h0 : Integrable (fun y ↦ u y * spectralZeroJet η b t 0 y) μ𝔽)
    (hu : ∫ y, u y * spectralZeroJet η b t 0 y ∂μ𝔽 = 1) (M : ℂ)
    (hM : ∫ g, φ.val g * spectralZeroJet η b t 0 g ∂μ𝔽 = M) :
    ((Tₐ).symm d) (Aφ u) =
      (∫ g, φ.val g * spectralZeroJet η b t 1 g ∂μ𝔽) + M * ((Tₐ).symm d) u := by
  let ℓ : StrongDual ℂ W₀ := (Tₐ).symm d
  let τ := hardySobolevTranslation μ𝔽 m𝔽 (-α) α s hI hs₀
  let J₀ := spectralZeroJet η b t 0
  let J₁ := spectralZeroJet η b t 1
  have heval (w : W₀) := reciprocalDual_apply hα hs d J₁ hd w
  have hτ (g : C𝔽) : ℓ (τ g u) = J₁ g * (∫ y, u y * J₀ y ∂μ𝔽) + J₀ g * ℓ u :=
    (heval (τ g u)).2.trans ((integral_translation_mul_spectralZeroJet_one hα hs η b t u h0
      (heval u).1 g).trans (congrArg (J₁ g * (∫ y, u y * J₀ y ∂μ𝔽) + J₀ g * ·) (heval u).2.symm))
  have hc : Continuous φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have hφ (k : ℕ) : Integrable (fun g ↦ φ.val g * spectralZeroJet η b t k g) μ𝔽 :=
    (hc.mul (continuous_spectralZeroJet η b t k)).integrable_of_hasCompactSupport
      (show HasCompactSupport φ.val from φ.property.2).mul_right
  have hP := bruhatRegularizedAction_apply μ𝔽 τ
    (exists_hardySobolevTranslation μ𝔽 m𝔽 (-α) α s hI hs₀).choose_spec.2 φ u
  have he := congrArg (fun p : PettisWeakCompletion W₀ ↦
    (show Module.Dual ℂ (StrongDual ℂ W₀) from p) ℓ) hP.2
  change ℓ (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s hI hs₀ φ u) =
    ∫ g, ℓ (φ.val g • τ g u) ∂μ𝔽 at he
  calc
    ℓ (Aφ u) = ∫ g, ℓ (φ.val g • τ g u) ∂μ𝔽 := he
    _ = ∫ g, ((φ.val g * J₁ g) * (∫ y, u y * J₀ y ∂μ𝔽) + (φ.val g * J₀ g) * ℓ u) ∂μ𝔽 :=
      integral_congr_ae (.of_forall fun g ↦ by
        change ℓ (φ.val g • τ g u) = _
        rw [map_smul, smul_eq_mul, hτ g]
        ring)
    _ = (∫ g, φ.val g * J₁ g ∂μ𝔽) * (∫ y, u y * J₀ y ∂μ𝔽) + (∫ g, φ.val g * J₀ g ∂μ𝔽) * ℓ u := by
      rw [integral_add ((hφ 1).mul_const _) ((hφ 0).mul_const _), integral_mul_const,
        integral_mul_const]
    _ = (∫ g, φ.val g * J₁ g ∂μ𝔽) * 1 + M * ℓ u :=
      congrArg₂ (fun p q : ℂ ↦ (∫ g, φ.val g * J₁ g ∂μ𝔽) * p + q * ℓ u) hu hM
    _ = _ := congrArg (· + M * ℓ u) (mul_one _)

/-- The modulus of a zero jet: the exponential of the real offset times the logarithm of the
norm, times a power of the modulus of that logarithm. -/
private theorem norm_spectralZeroJet (η : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) (g : C𝔽) :
    ‖spectralZeroJet η b t k g‖ =
      Real.exp (b * logIdeleClassNorm F g) * |logIdeleClassNorm F g| ^ k := by
  have hpos : 0 < ((ideleClassNorm F g).val : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))
  have htwist : ‖ideleClassNormTwist η (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I) g‖ =
      Real.exp (b * logIdeleClassNorm F g) := by
    change ‖(η g : ℂ) *
      (((ideleClassNorm F g).val : ℝ) : ℂ) ^ (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Real.rpow_def_of_pos hpos,
      mul_comm]
  change ‖ideleClassNormTwist η (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I) g *
    (logIdeleClassNorm F g : ℂ) ^ k‖ = _
  rw [norm_mul, htwist, norm_pow, Complex.norm_real, Real.norm_eq_abs]

/-- An exponential with a linear factor is dominated by two exponentials with shifted rates. -/
private theorem exp_mul_abs_le_exp_add_exp (b : ℝ) {ε : ℝ} (hε : 0 < ε) (L : ℝ) :
    Real.exp (b * L) * |L| ≤ ε⁻¹ * (Real.exp ((b + ε) * L) + Real.exp ((b - ε) * L)) := by
  have h1 : |L| ≤ ε⁻¹ * Real.exp (ε * |L|) := by
    rw [inv_mul_eq_div, le_div_iff₀ hε, mul_comm]
    linarith [Real.add_one_le_exp (ε * |L|)]
  have h2 : Real.exp (b * L) * Real.exp (ε * |L|) ≤
      Real.exp ((b + ε) * L) + Real.exp ((b - ε) * L) := by
    rw [← Real.exp_add]
    rcases le_total 0 L with hL | hL
    · rw [abs_of_nonneg hL, show b * L + ε * L = (b + ε) * L by ring]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_nonpos hL, show b * L + ε * -L = (b - ε) * L by ring]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  calc
    Real.exp (b * L) * |L| ≤ Real.exp (b * L) * (ε⁻¹ * Real.exp (ε * |L|)) :=
      mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = ε⁻¹ * (Real.exp (b * L) * Real.exp (ε * |L|)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (inv_pos.mpr hε).le

end Pairing

section Blocks

/-- A quotient jet functional evaluates on a representative by its explicit Haar moment.
A copy of the private `spectralStripConvolution_jet_eval` of `Sec3`. -/
private theorem geometricBlock_jet_eval (j : jets) (hj : Dₐ (f j) = stripU(j)) (v : W₀) :
    Integrable (fun y ↦ v y *
        spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2 y) μ𝔽 ∧
      f j ((Θ₀).mkQL v) = ∫ y, v y *
        spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2 y ∂μ𝔽 := by
  have hae : (Dₐ (f j) : C𝔽 → ℂ) =ᵐ[μ𝔽]
      spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2 := by
    rw [hj]
    exact (ideleClassTamagawaMeasure_absolutelyContinuous_reciprocal α s).ae_le
      (MemLp.coeFn_toLp _)
  have he := reciprocalDual_apply hα hs (Dₐ (f j)) _ hae v
  have hsymm : (Tₐ).symm (Dₐ (f j)) = (f j).comp (Θ₀).mkQL := (Tₐ).symm_apply_apply _
  rw [hsymm] at he
  exact he

/-- At any strip zero with a single retained jet, the geometric output of convolution on the
lift of the biorthogonal vector subtracts the Mellin value times the lift.
A copy of `spectralStripGeometricKernel_output_eq_sub_of_one_jet` of `Sec4b_Isolated`, which
this file cannot import. -/
private theorem geometricBlock_output_eq_sub_of_one_jet
    (hb : IsSpectralMarkushevichBasis x f ∧ ∀ j, Dₐ (f j) = stripU(j))
    (z : zeros(F, χ, a, α)) (m : Fin (jetCount(z))) (hcount : jetCount(z) ≤ 1) :
    Gₐ (Aφ (Sₐ(x jet(z, m)))) = Aφ (Sₐ(x jet(z, m))) - mellinAt(z) • Sₐ(x jet(z, m)) := by
  let T := spectralConvolution (F := F) a hI hs₀ φ
  let lift := (Θ₀).orthogonal.subtypeL.comp
    (Θ₀).quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  have hcoeff := spectralStripConvolution_jetCoefficients a hα hs χ x f hb.1 hb.2 φ
  have heigen : T (x jet(z, m)) = mellinAt(z) • x jet(z, m) := by
    apply geometricBlock_eq_of_coords x f hb.1
    intro j
    let w : zeros(F, χ, a, α) :=
      ⟨(j.val.1, j.val.2.1, j.val.2.2.1), SpectralStripJetIndex.mem_strip_order_pos hα j⟩
    let n : Fin (jetCount(w)) := ⟨j.val.2.2.2, j.property⟩
    change f jet(w, n) (T (x jet(z, m))) = f jet(w, n) (mellinAt(z) • x jet(z, m))
    rw [map_smul, smul_eq_mul]
    by_cases hw : w = z
    · subst z
      have hnm : n = m := Fin.ext (by have := n.isLt; have := m.isLt; omega)
      rw [hnm, hb.1.1, mul_one]
      exact (hcoeff.2 w m).trans (spectralConvolution_mellin_integrable φ (χ w.val.1) _).2
    · have hne : (jet(z, m) : jets) ≠ jet(w, n) := by
        intro heq
        exact hw (Subtype.ext (congrArg (fun i : jets ↦ (i.val.1, i.val.2.1, i.val.2.2.1)) heq).symm)
      rw [hb.1.2.1 _ _ hne, mul_zero]
      exact hcoeff.1 w z hw n m
  have hsec (v : H₀) : (Θ₀).mkQL (lift v) = v :=
    ((Θ₀).quotientEquivOrthogonal_symm_eq_mk _ ((Θ₀).quotientEquivOrthogonal v).property).symm.trans
      ((Θ₀).quotientEquivOrthogonal.symm_apply_apply v)
  have hp := DFunLike.congr_fun (spectralProjection_convolution_factor (F := F) a hα hs₀ φ)
    (lift (x jet(z, m)))
  change Pₐ (Aφ (lift (x jet(z, m)))) = lift (T ((Θ₀).mkQL (lift (x jet(z, m))))) at hp
  rw [hsec, heigen, map_smul] at hp
  exact eq_sub_of_add_eq ((congrArg (Gₐ (Aφ (lift (x jet(z, m)))) + ·) hp.symm).trans
    ((Θ₀).starProjection_add_starProjection_orthogonal _))

/-- The retained jets, as functionals on the strip space, vanish on the theta subspace. -/
private theorem geometricBlock_retainedJet_apply_eq_zero (j : jets) (w : W₀) (hw : w ∈ Θ₀) :
    ((Tₐ).symm (Dₐ (f j))) w = 0 := by
  have hsymm : (Tₐ).symm (Dₐ (f j)) = (f j).comp (Θ₀).mkQL := (Tₐ).symm_apply_apply _
  rw [hsymm]
  change f j ((Θ₀).mkQ w) = 0
  rw [(spectralSobolevQuotient_eq_zero a hI hs₀ w).mpr hw, map_zero]

/-- The moment of order zero of the lift of the biorthogonal vector of a zero with one retained
jet is one. -/
private theorem geometricBlock_lift_valueJet
    (hb : IsSpectralMarkushevichBasis x f ∧ ∀ j, Dₐ (f j) = stripU(j))
    (z : zeros(F, χ, a, α)) (m : Fin (jetCount(z))) (hcount : jetCount(z) ≤ 1) :
    Integrable (fun y ↦ (Sₐ(x jet(z, m)) : W₀) y * valueJet(z) y) μ𝔽 ∧
      ∫ y, (Sₐ(x jet(z, m)) : W₀) y * valueJet(z) y ∂μ𝔽 = 1 := by
  have hm0 : m.val = 0 := by have := m.isLt; omega
  have hjet := geometricBlock_jet_eval a hα hs χ f jet(z, m) (hb.2 _) (Sₐ(x jet(z, m)))
  have hsec : (Θ₀).mkQL (Sₐ(x jet(z, m))) = x jet(z, m) :=
    ((Θ₀).quotientEquivOrthogonal_symm_eq_mk _
      ((Θ₀).quotientEquivOrthogonal (x jet(z, m))).property).symm.trans
      ((Θ₀).quotientEquivOrthogonal.symm_apply_apply (x jet(z, m)))
  have hF : f jet(z, m) ((Θ₀).mkQL (Sₐ(x jet(z, m)))) = 1 :=
    (congrArg (f jet(z, m)) hsec).trans (hb.1.1 _)
  have key : ∀ k : ℕ, k = 0 →
      (Integrable (fun y ↦ (Sₐ(x jet(z, m)) : W₀) y *
          spectralZeroJet (F := F) (χ z.val.1) z.val.2.1 z.val.2.2 k y) μ𝔽 ∧
        f jet(z, m) ((Θ₀).mkQL (Sₐ(x jet(z, m)))) = ∫ y, (Sₐ(x jet(z, m)) : W₀) y *
          spectralZeroJet (F := F) (χ z.val.1) z.val.2.1 z.val.2.2 k y ∂μ𝔽) →
      Integrable (fun y ↦ (Sₐ(x jet(z, m)) : W₀) y * valueJet(z) y) μ𝔽 ∧
        ∫ y, (Sₐ(x jet(z, m)) : W₀) y * valueJet(z) y ∂μ𝔽 = 1 := by
    rintro k rfl hk
    exact ⟨hk.1, hk.2.symm.trans hF⟩
  exact key m.val hm0 hjet

/-- The Leibniz rule at the lift of the biorthogonal vector of a zero with one retained jet:
the functional of the jet of order one at the convolved lift is the first Mellin moment of
the test plus the Mellin value times the functional at the lift. -/
private theorem geometricBlock_firstJet_leibniz
    (hb : IsSpectralMarkushevichBasis x f ∧ ∀ j, Dₐ (f j) = stripU(j))
    (z : zeros(F, χ, a, α)) (m : Fin (jetCount(z))) (hcount : jetCount(z) ≤ 1)
    (d : W₀') (hd : (d : C𝔽 → ℂ) =ᵐ[μ𝔽] firstJet(z)) :
    ((Tₐ).symm d) (Aφ (Sₐ(x jet(z, m)))) =
      (∫ g : C𝔽, φ.val g * firstJet(z) g ∂μ𝔽) + mellinAt(z) * ((Tₐ).symm d) (Sₐ(x jet(z, m))) := by
  have hlift := geometricBlock_lift_valueJet a hα hs χ x f hb z m hcount
  have hmellin : ∫ g : C𝔽, φ.val g * valueJet(z) g ∂μ𝔽 = mellinAt(z) := by
    refine integral_congr_ae (.of_forall fun g ↦ ?_)
    change φ.val g * (ideleClassNormTwist (χ z.val.1) _ g * (logIdeleClassNorm F g : ℂ) ^ 0) = _
    rw [pow_zero, mul_one]
  exact reciprocalDual_testAction_spectralZeroJet_one hα hs φ (χ z.val.1) z.val.2.1 z.val.2.2
    d hd (Sₐ(x jet(z, m))) hlift.1 hlift.2 mellinAt(z) hmellin

/-- The trace norm of the geometric block of a zero with one retained jet. -/
private theorem geometricBlock_traceNorm_of_one_jet
    (z : zeros(F, χ, a, α)) (m : Fin (jetCount(z))) (hcount : jetCount(z) ≤ 1) :
    traceNorm (geometricBlock(z)) =
      ‖(f jet(z, m)).comp (Θ₀).mkQL‖ * ‖Gₐ (Aφ (Sₐ(x jet(z, m))))‖ := by
  have hsub : Subsingleton (Fin (jetCount(z))) := Fin.subsingleton_iff_le_one.mpr hcount
  rw [Fintype.sum_subsingleton _ m]
  exact traceNorm_smulRight _ _

/-- Paper: Theorem 10.4.3.5(2), p. 472. A lower bound for one geometric block. Let `z` be a zero
of the strip with one retained jet, and let `d` be a vector of the reciprocal-weight space that
is the jet of order one at `z`. Then the first Mellin moment of the test at `z`, which is the
derivative of its Mellin transform there, times the norm of the retained jet functional at `z`,
is at most the trace norm of the geometric block of `z` times the distance from `d` to any
vector `v` in the span of the retained jets of the strip.
Reconstruction: The paper gives no estimate for the geometric component (p. 472). This is what a
bound for the blocks of `Isolated.spectralStripGeometricKernel_blocks_bddAbove` has to pay at a
simple zero: the output of the block lies in the theta subspace, where all retained jets vanish
and the jet of order one takes the value of the first Mellin moment. -/
theorem spectralStripGeometricKernel_block_traceNorm_ge
    (hb : IsSpectralMarkushevichBasis x f ∧ ∀ j, Dₐ (f j) = stripU(j))
    (z : zeros(F, χ, a, α)) (m : Fin (jetCount(z))) (hcount : jetCount(z) ≤ 1)
    (d : W₀') (hd : (d : C𝔽 → ℂ) =ᵐ[μ𝔽] firstJet(z))
    (v : W₀') (hv : v ∈ Submodule.span ℂ (range fun j : jets ↦ Dₐ (f j))) :
    ‖∫ g : C𝔽, φ.val g * firstJet(z) g ∂μ𝔽‖ * ‖(f jet(z, m)).comp (Θ₀).mkQL‖ ≤
      ‖d - v‖ * traceNorm (geometricBlock(z)) := by
  have hout := geometricBlock_output_eq_sub_of_one_jet a hα hs φ χ x f hb z m hcount
  have hΘ : Aφ (Sₐ(x jet(z, m))) - mellinAt(z) • Sₐ(x jet(z, m)) ∈ Θ₀ := by
    rw [← hout]
    exact (Θ₀).starProjection_apply_mem _
  have hnorm := geometricBlock_norm_ge_abstract (Tₐ) (Θ₀) (Aφ) (Sₐ(x jet(z, m))) mellinAt(z)
    (∫ g : C𝔽, φ.val g * firstJet(z) g ∂μ𝔽) hΘ d
    (geometricBlock_firstJet_leibniz a hα hs φ χ x f hb z m hcount d hd)
    (fun j : jets ↦ Dₐ (f j)) (geometricBlock_retainedJet_apply_eq_zero a hα hs χ f) v hv
  rw [geometricBlock_traceNorm_of_one_jet a hα hs φ χ x f z m hcount, hout]
  calc
    _ ≤ (‖d - v‖ * ‖Aφ (Sₐ(x jet(z, m))) - mellinAt(z) • Sₐ(x jet(z, m))‖) *
        ‖(f jet(z, m)).comp (Θ₀).mkQL‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = _ := by ring

include hα hs in
/-- Paper: (10.2.2.4), p. 446. At a zero of the open strip that has a retained jet, the jet of
order one is square-integrable for the reciprocal strip weight: it is represented by a vector
of the reciprocal-weight space.
Deviation: The paper retains a jet of order one only at a multiple zero. At a simple zero in
the open strip the function is still in the reciprocal-weight space, and that is all that is
used here. The proof compares it with two jets of order zero at shifted real offsets; those are
admitted strip jets for a shifted twist, so `spectralStripJet_memLp` applies to them. -/
theorem exists_spectralZeroJet_one_dual
    (z : zeros(F, χ, a, α)) (hz : z.val.2.1 ∈ Ioo (-α) α) (m : Fin (jetCount(z))) :
    ∃ d : W₀', (d : C𝔽 → ℂ) =ᵐ[μ𝔽] firstJet(z) := by
  obtain ⟨hlo, hhi⟩ := hz
  have hN : 0 < (order(χ, a, z.val)).untop₀.toNat := by
    have hm := m.isLt
    have heq := spectralStripMultiplicity_interior (α := α) (b := z.val.2.1) ⟨hlo, hhi⟩ s
      (order(χ, a, z.val)).untop₀.toNat
    omega
  let ε : ℝ := min (z.val.2.1 + α) (α - z.val.2.1) / 2
  have hε : 0 < ε := half_pos (lt_min (by linarith) (by linarith))
  have hε1 : ε < z.val.2.1 + α :=
    (half_lt_self (lt_min (by linarith) (by linarith))).trans_le (min_le_left _ _)
  have hε2 : ε < α - z.val.2.1 :=
    (half_lt_self (lt_min (by linarith) (by linarith))).trans_le (min_le_right _ _)
  -- the jets of order zero at the real offsets `b ± ε`, for the twists `a ∓ ε`
  have hmem (b' : ℝ) (hb' : b' ∈ Ioo (-α) α) :
      MemLp (spectralZeroJet (F := F) (χ z.val.1) b' z.val.2.2 0) 2
        (intervalSobolevMeasure μ𝔽 (logIdeleClassNorm F) (-α) α s true) := by
    have hpt : a + z.val.2.1 - b' + b' = a + z.val.2.1 := by ring
    have hj : 0 < spectralStripMultiplicity α s b' (meromorphicOrderAt
        (continuedCompletedHeckeL (χ z.val.1))
        (((a + z.val.2.1 - b' + b' : ℝ) : ℂ) + (z.val.2.2 : ℂ) * Complex.I)).untop₀.toNat := by
      rw [spectralStripMultiplicity_interior hb', hpt]
      exact hN
    let j' : SpectralStripJetIndex χ (a + z.val.2.1 - b') α s := ⟨(z.val.1, b', z.val.2.2, 0), hj⟩
    exact spectralStripJet_memLp χ hα hs₀ j'
  have hp := hmem (z.val.2.1 + ε) ⟨by linarith, by linarith⟩
  have hn := hmem (z.val.2.1 - ε) ⟨by linarith, by linarith⟩
  have hdom : MemLp (fun g : C𝔽 ↦ ε⁻¹ *
      (‖spectralZeroJet (F := F) (χ z.val.1) (z.val.2.1 + ε) z.val.2.2 0 g‖ +
        ‖spectralZeroJet (F := F) (χ z.val.1) (z.val.2.1 - ε) z.val.2.2 0 g‖)) 2
      (intervalSobolevMeasure μ𝔽 (logIdeleClassNorm F) (-α) α s true) :=
    (hp.norm.add hn.norm).const_mul ε⁻¹
  have hJ : MemLp (firstJet(z)) 2
      (intervalSobolevMeasure μ𝔽 (logIdeleClassNorm F) (-α) α s true) := by
    refine hdom.mono' (continuous_spectralZeroJet _ _ _ 1).aestronglyMeasurable
      (.of_forall fun g ↦ ?_)
    simp only [norm_spectralZeroJet, pow_one, pow_zero, mul_one]
    exact exp_mul_abs_le_exp_add_exp _ hε _
  exact ⟨hJ.toLp _, (ideleClassTamagawaMeasure_absolutelyContinuous_reciprocal α s).ae_le
    (MemLp.coeFn_toLp hJ)⟩

/-- Paper: Theorem 10.4.3.5(2), p. 472. What the bound of
`Isolated.spectralStripGeometricKernel_blocks_bddAbove` (#7406) forces. If the finite sums of
the geometric blocks are bounded in trace norm, then one constant `B` bounds, at every zero `z`
of the strip with one retained jet, the first Mellin moment of the test at `z` times the norm of
the retained jet functional at `z`, relative to the distance from the jet of order one at `z` to
any vector in the span of the retained jets. For a second zero `w` of the same character the
difference quotient `(w - z)⁻¹ • (u_w - u_z)` of retained jets is such a vector, and it tends to
the jet of order one as `w` tends to `z`: two zeros of the open strip that come close force the
derivative of the Mellin transform of the test down.
Reconstruction: The paper gives no estimate for the geometric component (p. 472). The hypothesis
is the statement of the recorded gap, word for word. -/
theorem spectralStripGeometricKernel_blocks_bddAbove_forces_firstJet_separation
    (hb : IsSpectralMarkushevichBasis x f ∧ ∀ j, Dₐ (f j) = stripU(j))
    (hbound : BddAbove (range fun K : Finset zeros(F, χ, a, α) ↦
      traceNorm (∑ z ∈ K, geometricBlock(z)))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (z : zeros(F, χ, a, α)) (m : Fin (jetCount(z))), jetCount(z) ≤ 1 →
      ∀ d : W₀', (d : C𝔽 → ℂ) =ᵐ[μ𝔽] firstJet(z) →
      ∀ v ∈ Submodule.span ℂ (range fun j : jets ↦ Dₐ (f j)),
        ‖∫ g : C𝔽, φ.val g * firstJet(z) g ∂μ𝔽‖ * ‖(f jet(z, m)).comp (Θ₀).mkQL‖ ≤
          B * ‖d - v‖ := by
  obtain ⟨B, hB⟩ := hbound
  refine ⟨max B 0, le_max_right _ _, fun z m hcount d hd v hv ↦ ?_⟩
  have hz : traceNorm (geometricBlock(z)) ≤ B := by
    have h := hB (mem_range_self ({z} : Finset zeros(F, χ, a, α)))
    rwa [Finset.sum_singleton] at h
  calc
    _ ≤ ‖d - v‖ * traceNorm (geometricBlock(z)) :=
      spectralStripGeometricKernel_block_traceNorm_ge a hα hs φ χ x f hb z m hcount d hd v hv
    _ ≤ ‖d - v‖ * max B 0 :=
      mul_le_mul_of_nonneg_left (hz.trans (le_max_left _ _)) (norm_nonneg _)
    _ = _ := mul_comm _ _

local notation "Xlog" => logIdeleClassNorm F
local notation "νrec" => intervalSobolevMeasure μ𝔽 Xlog (-α) α s true
local notation "envelope" => (fun g : C𝔽 ↦ (Real.exp (α * |Xlog g|) : ℂ))
local notation "Mm(" u ", " η ", " k ")" =>
  RiemannMasullo.MellinMoment.moment μ𝔽 Xlog (fun g : C𝔽 ↦ (u g : ℂ) * (η g : ℂ)) k
local notation "center(" z ")" => (((z).val.2.1 : ℂ) + ((z).val.2.2 : ℂ) * Complex.I)
local notation "ordAt(" η ", " w ")" =>
  (meromorphicOrderAt (continuedCompletedHeckeL η) ((a : ℂ) + w)).untop₀.toNat

private theorem geometricCluster_jet_exp (η : PontryaginDual C𝔽) (w : ℂ) (k : ℕ) (g : C𝔽) :
    spectralZeroJet η w.re w.im k g =
      (η g : ℂ) * Complex.exp (w * (Xlog g : ℂ)) * (Xlog g : ℂ) ^ k := by
  let q : ℝ := ((ideleClassNorm F g).val : ℝ)
  have hq : 0 < q := NNReal.coe_pos.mpr (Units.zero_lt _)
  unfold spectralZeroJet
  rw [Complex.re_add_im]
  change ((η g : ℂ) * (q : ℂ) ^ w) * _ = _
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne'), ← Complex.ofReal_log hq.le]
  rw [mul_comm (Complex.ofReal (Real.log q)) w]

private theorem geometricCluster_moment_eq_jet
    (u : W₀) (η : PontryaginDual C𝔽) (w : ℂ) (k : ℕ) :
    Mm(u, η, k) w = ∫ g : C𝔽, u g * spectralZeroJet η w.re w.im k g ∂μ𝔽 := by
  apply integral_congr_ae (.of_forall fun g ↦ ?_)
  rw [geometricCluster_jet_exp]
  ring

include hα hs in
/-- Every admitted spectral index supplies the same reciprocal envelope. The endpoints
admit their zeroth jet since the Sobolev exponent exceeds one. -/
private theorem geometricCluster_envelope_mem (j : jets) : MemLp envelope 2 νrec := by
  let b := j.val.2.1
  let t := j.val.2.2.1
  let η := χ j.val.1
  let N := (meromorphicOrderAt (continuedCompletedHeckeL η)
    (((a + b : ℝ) : ℂ) + (t : ℂ) * Complex.I)).untop₀.toNat
  have hN : 0 < N := by
    have hj : j.val.2.2.2 < spectralStripMultiplicity α s b N := j.property
    have hle : spectralStripMultiplicity α s b N ≤ N := by
      unfold spectralStripMultiplicity spectralBoundaryMultiplicity
      split_ifs <;> first | exact le_rfl | exact min_le_left _ _ | exact Nat.zero_le _
    omega
  have hside (v : ℝ) (hv : v = -α ∨ v = α) :
      MemLp (spectralZeroJet (F := F) η v t 0) 2 νrec := by
    have hpt : a + b - v + v = a + b := by ring
    have hj : 0 < spectralStripMultiplicity α s v (meromorphicOrderAt
        (continuedCompletedHeckeL η) (((a + b - v + v : ℝ) : ℂ) + (t : ℂ) * Complex.I)).untop₀.toNat := by
      rw [spectralStripMultiplicity_boundary hα hv, hpt, lt_spectralBoundaryMultiplicity]
      exact ⟨hN, by norm_num; linarith⟩
    exact spectralStripJet_memLp χ hα hs₀ (a := a + b - v) ⟨(j.val.1, v, t, 0), hj⟩
  have hp := hside α (Or.inr rfl)
  have hn := hside (-α) (Or.inl rfl)
  have hcont : Continuous envelope :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul (continuous_logIdeleClassNorm (F := F)).abs))
  refine (hp.norm.add hn.norm).mono' hcont.aestronglyMeasurable (.of_forall fun g ↦ ?_)
  simp only [Pi.add_apply, norm_spectralZeroJet, pow_zero, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rcases le_total 0 (Xlog g) with h | h
  · rw [abs_of_nonneg h]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos h, mul_neg, neg_mul]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

private theorem geometricCluster_moment_meas (u : W₀) (η : PontryaginDual C𝔽) :
    AEStronglyMeasurable (fun g : C𝔽 ↦ u g * (η g : ℂ)) μ𝔽 :=
  (Lp.stronglyMeasurable u).aestronglyMeasurable.mul
    (continuous_subtype_val.comp η.continuous).aestronglyMeasurable

include hα hs in
private theorem geometricCluster_exponential_integrable (hE : MemLp envelope 2 νrec)
    (u : W₀) (η : PontryaginDual C𝔽) :
    Integrable (fun g : C𝔽 ↦ ‖u g * (η g : ℂ)‖ * Real.exp (α * |Xlog g|)) μ𝔽 := by
  have ha := (ideleClassTamagawaMeasure_absolutelyContinuous_reciprocal α s).ae_le hE.coeFn_toLp
  have H := (reciprocalDual_apply hα hs (hE.toLp _) _ ha u).1.norm
  simpa only [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] using H

include hα hs in
private theorem geometricCluster_value_le (hE : MemLp envelope 2 νrec) (u : W₀)
    (η : PontryaginDual C𝔽) (w : ℂ) (hw : |w.re| ≤ α) :
    ‖Mm(u, η, 0) w‖ ≤ ‖hE.toLp _‖ * ‖u‖ := by
  let J := spectralZeroJet (F := F) η w.re w.im 0
  have hdom (g : C𝔽) : ‖J g‖ ≤ ‖envelope g‖ := by
    rw [norm_spectralZeroJet, pow_zero, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    exact ((le_abs_self _).trans (abs_mul _ _).le).trans (mul_le_mul_of_nonneg_right hw (abs_nonneg _))
  have hJ : MemLp J 2 νrec := hE.mono (continuous_spectralZeroJet _ _ _ 0).aestronglyMeasurable
    (.of_forall hdom)
  have hN : ‖hJ.toLp J‖ ≤ ‖hE.toLp _‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hJ.coeFn_toLp, hE.coeFn_toLp] with g hg hg'
    simpa only [hg, hg'] using hdom g
  have hp := (reciprocalDual_apply hα hs (hJ.toLp _) J
    ((ideleClassTamagawaMeasure_absolutelyContinuous_reciprocal α s).ae_le hJ.coeFn_toLp) u).2
  rw [geometricCluster_moment_eq_jet, ← hp]
  exact (((Tₐ).symm (hJ.toLp J)).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (((Tₐ).symm.norm_map _).le.trans hN) (norm_nonneg _))

private theorem geometricCluster_moment_vanishes (u : W₀) (hu : u ∈ Θ₀)
    (ω : PontryaginDual (ideleClassNorm F).ker) (w : ℂ) (hw : |w.re| < α)
    (k : ℕ) (hk : k < ordAt(χ ω, w)) : Mm(u, χ ω, k) w = 0 := by
  have hw' : (((a + w.re : ℝ) : ℂ) + (w.im : ℂ) * Complex.I) = (a : ℂ) + w := by
    rw [Complex.ofReal_add, add_assoc, Complex.re_add_im]
  have hj : k < spectralStripMultiplicity α s w.re (meromorphicOrderAt
      (continuedCompletedHeckeL (χ ω)) (((a + w.re : ℝ) : ℂ) + (w.im : ℂ) * Complex.I)).untop₀.toNat := by
    rwa [spectralStripMultiplicity_interior (abs_lt.mp hw), hw']
  let j : jets := ⟨(ω, w.re, w.im, k), hj⟩
  have he : (stripU(j) : C𝔽 → ℂ) =ᵐ[μ𝔽] spectralZeroJet (χ ω) w.re w.im k :=
    (ideleClassTamagawaMeasure_absolutelyContinuous_reciprocal α s).ae_le
    (spectralStripJet_memLp χ hα hs₀ j).coeFn_toLp
  have h := spectralStripJet_commonKernel_forward χ hα hs₀ u hu j
  rw [geometricCluster_moment_eq_jet]
  exact (integral_congr_ae (he.symm.mono fun g hg ↦ congrArg (u g * ·) hg)).trans h

private theorem geometricCluster_disk_inside {v : ℂ} {r α : ℝ} (hv : |v.re| + r ≤ α)
    {w : ℂ} (hw : w ∈ Metric.ball v r) : |w.re| < α := by
  have h := abs_add_le (w - v).re v.re
  rw [Complex.sub_re, sub_add_cancel] at h
  have h₁ := Complex.abs_re_le_norm (w - v)
  rw [Complex.sub_re] at h₁
  have h₂ : ‖w - v‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hw
  linarith

/-- Every theta vector has a first Mellin derivative bounded by the full product of
normalized distances to any finite selection of other zeros in the disk. -/
private theorem geometricCluster_theta_firstMoment_le_zero_product
    (hE : MemLp envelope 2 νrec) (u : W₀) (hu : u ∈ Θ₀)
    (ω : PontryaginDual (ideleClassNorm F).ker) (v : ℂ) {r : ℝ} (hr : 0 < r)
    (hv : |v.re| + r ≤ α) (hzero : 0 < ordAt(χ ω, v))
    (S : Finset ℂ) (hne : ∀ w ∈ S, w ≠ v) (hi : ∀ w ∈ S, w ∈ Metric.ball v r) :
    ‖Mm(u, χ ω, 1) v‖ ≤ (‖hE.toLp _‖ * ‖u‖ / r) *
      ∏ w ∈ S, (‖w - v‖ / r) ^ ordAt(χ ω, w) := by
  have hl := (continuous_logIdeleClassNorm (F := F)).measurable
  have hf := geometricCluster_moment_meas u (χ ω)
  have hInt := geometricCluster_exponential_integrable hα hs hE u (χ ω)
  have hA := RiemannMasullo.MellinMoment.analyticOnNhd_moment hl hf hInt 0
  have hball := fun w (hw : w ∈ Metric.ball v r) ↦ geometricCluster_disk_inside hv hw
  have hv' := hball v (Metric.mem_ball_self hr)
  have h0 := geometricCluster_moment_vanishes a hα hs χ u hu ω v hv' 0 hzero
  have horder (w : ℂ) (hw : w ∈ S) : (ordAt(χ ω, w) : ℕ∞) ≤ analyticOrderAt (Mm(u, χ ω, 0)) w := by
    have hwin := hball w (hi w hw)
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hA w hwin)).mpr
    intro k hk
    rw [RiemannMasullo.MellinMoment.iteratedDeriv_moment_zero hl hf hInt k hwin]
    exact geometricCluster_moment_vanishes a hα hs χ u hu ω w hwin k hk
  have h := RiemannMasullo.Blaschke.norm_deriv_le_disk_zero_product (Mm(u, χ ω, 0)) v hr
    (fun w hw ↦ hA _ (hball w hw)) h0
    (fun w hw ↦ geometricCluster_value_le hα hs hE u (χ ω) w (hball w hw).le)
    S (fun w ↦ ordAt(χ ω, w)) hne hi horder
  simpa only [(RiemannMasullo.MellinMoment.hasDerivAt_moment hl hf hInt 0 hv').deriv] using h

private theorem geometricBlock_linear_difference {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (L : StrongDual ℂ E) (u v : E) (b c : ℂ)
    (h : L u = c + b * L v) : L (u - b • v) = c := by
  rw [map_sub, map_smul, smul_eq_mul, h, add_sub_cancel_right]

/-- At a simple interior zero the first Mellin moment of the projected output is exactly
the first Mellin moment of the test. This combines the singleton formula and its
Leibniz identity from the first part of this file. -/
private theorem geometricBlock_output_firstMoment
    (hb : IsSpectralMarkushevichBasis x f ∧ ∀ j, Dₐ (f j) = stripU(j))
    (z : zeros(F, χ, a, α)) (m : Fin (jetCount(z))) (hcount : jetCount(z) ≤ 1)
    (hz : z.val.2.1 ∈ Ioo (-α) α) :
    ∫ g : C𝔽, (Gₐ (Aφ (Sₐ(x jet(z, m))))) g * firstJet(z) g ∂μ𝔽 =
      ∫ g : C𝔽, φ.val g * firstJet(z) g ∂μ𝔽 := by
  obtain ⟨d, hd⟩ := exists_spectralZeroJet_one_dual a hα hs χ z hz m
  let ℓ := (Tₐ).symm d
  let q := Sₐ(x jet(z, m))
  let u : W₀ := Gₐ (Aφ q)
  have hu : u = Aφ q - mellinAt(z) • q :=
    geometricBlock_output_eq_sub_of_one_jet a hα hs φ χ x f hb z m hcount
  have hL : ℓ (Aφ q) = (∫ g : C𝔽, φ.val g * firstJet(z) g ∂μ𝔽) + mellinAt(z) * ℓ q :=
    geometricBlock_firstJet_leibniz a hα hs φ χ x f hb z m hcount d hd
  calc
    _ = ℓ u := (reciprocalDual_apply hα hs d _ hd u).2.symm
    _ = ℓ (Aφ q - mellinAt(z) • q) := congrArg ℓ hu
    _ = _ := geometricBlock_linear_difference ℓ (Aφ q) q mellinAt(z) _ hL

/-- Paper: Theorem 10.4.3.5(2), p. 472. The first test moment times the norm of the retained
evaluation at a simple interior zero is bounded by the geometric singleton trace norm times the
product of normalized distances to any finite collection of other zeros in its disk, counted
with their full multiplicities. The prefactor is the reciprocal-weight norm of the exponential
envelope divided by the radius.
Reconstruction: Apply Schwarz's lemma to the Mellin transform of the actual theta output. -/
theorem spectralStripGeometricKernel_block_zero_product
    (hb : IsSpectralMarkushevichBasis x f ∧ ∀ j, Dₐ (f j) = stripU(j))
    (z : zeros(F, χ, a, α)) (m : Fin (jetCount(z))) (hcount : jetCount(z) ≤ 1)
    {r : ℝ} (hr : 0 < r) (hmargin : |z.val.2.1| + r ≤ α)
    (S : Finset ℂ) (hne : ∀ w ∈ S, w ≠ center(z))
    (hi : ∀ w ∈ S, w ∈ Metric.ball (center(z)) r) :
    ‖∫ g : C𝔽, φ.val g * firstJet(z) g ∂μ𝔽‖ * ‖(f jet(z, m)).comp (Θ₀).mkQL‖ ≤
      ((eLpNorm envelope 2 νrec).toReal / r) * traceNorm (geometricBlock(z)) *
        ∏ w ∈ S, (‖w - center(z)‖ / r) ^ ordAt(χ z.val.1, w) := by
  let hE := geometricCluster_envelope_mem a hα hs χ (jet(z, m))
  let v : ℂ := center(z)
  let u : W₀ := Gₐ (Aφ (Sₐ(x jet(z, m))))
  have hu : u ∈ Θ₀ := (Θ₀).starProjection_apply_mem _
  have hre : v.re = z.val.2.1 := by simp [v]
  have him : v.im = z.val.2.2 := by simp [v]
  have hz : z.val.2.1 ∈ Ioo (-α) α := abs_lt.mp (by linarith)
  have hN : 0 < ordAt(χ z.val.1, v) := by
    have hm : 0 < jetCount(z) := (Nat.zero_le m.val).trans_lt m.isLt
    rw [spectralStripMultiplicity_interior hz] at hm
    simpa only [v, ← add_assoc, ← Complex.ofReal_add] using hm
  have H := geometricCluster_theta_firstMoment_le_zero_product a hα hs χ hE u hu z.val.1 v hr
    (by rwa [hre]) hN S hne hi
  have hId : Mm(u, χ z.val.1, 1) v = ∫ g : C𝔽, φ.val g * firstJet(z) g ∂μ𝔽 := by
    rw [geometricCluster_moment_eq_jet, hre, him]
    exact geometricBlock_output_firstMoment a hα hs φ χ x f hb z m hcount hz
  let E := ‖(f jet(z, m)).comp (Θ₀).mkQL‖
  have heq : traceNorm (geometricBlock(z)) = E * ‖u‖ :=
    geometricBlock_traceNorm_of_one_jet a hα hs φ χ x f z m hcount
  rw [← hId, heq]
  exact (mul_le_mul_of_nonneg_right H (norm_nonneg _)).trans_eq (by rw [Lp.norm_toLp]; dsimp only [E, v]; ring)

/-- The geometric finite-block bound from #7406, for a fixed compact test, bounds its
first Mellin moment at every simple interior zero by the whole local divisor product.
The same constant works for all characters, heights, disks and finite selections. -/
private theorem spectralStripGeometricKernel_blocks_bddAbove_forces_zero_product
    (hχ : IsSpectralBasepointChoice χ)
    (hb : IsSpectralMarkushevichBasis x f ∧ ∀ j, Dₐ (f j) = stripU(j))
    (hbound : BddAbove (range fun K : Finset zeros(F, χ, a, α) ↦
      traceNorm (∑ z ∈ K, geometricBlock(z)))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : zeros(F, χ, a, α)) (_ : Fin (jetCount(z))),
      jetCount(z) ≤ 1 → ∀ (r : ℝ), 0 < r → |z.val.2.1| + r ≤ α →
      ∀ (S : Finset ℂ), (∀ w ∈ S, w ≠ center(z)) → (∀ w ∈ S, w ∈ Metric.ball (center(z)) r) →
      ‖∫ g : C𝔽, φ.val g * firstJet(z) g ∂μ𝔽‖ ≤
        (C / r) * ∏ w ∈ S, (‖w - center(z)‖ / r) ^ ordAt(χ z.val.1, w) := by
  obtain ⟨c, hc, hlow⟩ := spectralStripJet_lowerBound (a := a) χ hχ hα hs
  obtain ⟨B, hB⟩ := hbound
  let D := (eLpNorm envelope 2 νrec).toReal
  have hD : 0 ≤ D := ENNReal.toReal_nonneg
  refine ⟨D * max B 0 / c, by positivity, fun z m hcount r hr hmargin S hne hi ↦ ?_⟩
  have hbz : traceNorm (geometricBlock(z)) ≤ max B 0 := by
    have H := hB (mem_range_self ({z} : Finset zeros(F, χ, a, α)))
    rw [Finset.sum_singleton] at H
    exact H.trans (le_max_left _ _)
  have hc' : c ≤ ‖(f jet(z, m)).comp (Θ₀).mkQL‖ := by
    calc c ≤ ‖stripU(jet(z, m))‖ := hlow _
         _ = ‖Dₐ (f jet(z, m))‖ := by rw [hb.2 _]
         _ = _ := (Tₐ).norm_map _
  let P := ∏ w ∈ S, (‖w - center(z)‖ / r) ^ ordAt(χ z.val.1, w)
  have hP : 0 ≤ P := Finset.prod_nonneg (fun w _ ↦ pow_nonneg (div_nonneg (norm_nonneg _) hr.le) _)
  apply (mul_le_mul_iff_left₀ hc).mp
  calc
    _ ≤ ‖∫ g : C𝔽, φ.val g * firstJet(z) g ∂μ𝔽‖ * ‖(f jet(z, m)).comp (Θ₀).mkQL‖ :=
      mul_le_mul_of_nonneg_left hc' (norm_nonneg _)
    _ ≤ (D / r) * traceNorm (geometricBlock(z)) * P :=
      spectralStripGeometricKernel_block_zero_product a hα hs φ χ x f hb z m hcount hr hmargin S hne hi
    _ ≤ (D / r) * max B 0 * P := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbz (div_nonneg hD hr.le)) hP
    _ = _ := by dsimp only [P]; field_simp

/-- The finite set of distinct positive-order sites in a punctured disk of one Hecke
character. The arguments are spectral offsets from the real center of the strip. -/
def geometricClusterNeighbors (η : PontryaginDual C𝔽) (v : ℂ) (r : ℝ) : Finset ℂ :=
  (show {w : ℂ | w ≠ v ∧ w ∈ Metric.ball v r ∧ 0 < ordAt(η, w)}.Finite by
    let A (w : ℂ) := (a : ℂ) + w
    let K := A '' Metric.closedBall v r
    let L := continuedCompletedHeckeL η
    have hi : Function.Injective A := add_right_injective _
    have hK : IsCompact K := (isCompact_closedBall v r).image (continuous_const.add continuous_id)
    have hL : MeromorphicOn L K := fun w _ ↦ (continuedCompletedHeckeL_spec η).1.meromorphicOn w (mem_univ w)
    apply (((MeromorphicOn.divisor L K).finiteSupport hK).preimage hi.injOn).subset
    rintro w ⟨_, hwin, hm⟩
    change MeromorphicOn.divisor L K (A w) ≠ 0
    rw [hL.divisor_apply ⟨w, Metric.ball_subset_closedBall hwin, rfl⟩]
    change 0 < (meromorphicOrderAt L (A w)).untop₀.toNat at hm
    exact fun h ↦ by rw [h] at hm; simp at hm).toFinset

/-- Membership records exactly the noncentral, interior positive-order sites. -/
theorem mem_geometricClusterNeighbors (η : PontryaginDual C𝔽) (w v : ℂ) (r : ℝ) :
    w ∈ geometricClusterNeighbors a η v r ↔
      w ≠ v ∧ w ∈ Metric.ball v r ∧ 0 < ordAt(η, w) := Set.Finite.mem_toFinset _

/-- Paper: Theorem 10.4.3.5(2), p. 472. For each compact test satisfying the geometric
finite-family bound, its first Mellin moment at each simple interior site is bounded by the
complete product of the other zero distances in the disk, times a constant over the radius.
Reconstruction: The lower bound on retained evaluation norms is uniform in the angular mode
and height. -/
theorem spectralStripGeometricKernel_blocks_bddAbove_forces_full_zero_product
    (hχ : IsSpectralBasepointChoice χ)
    (hb : IsSpectralMarkushevichBasis x f ∧ ∀ j, Dₐ (f j) = stripU(j))
    (hbound : BddAbove (range fun K : Finset zeros(F, χ, a, α) ↦
      traceNorm (∑ z ∈ K, geometricBlock(z)))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : zeros(F, χ, a, α)) (_ : Fin (jetCount(z))),
      jetCount(z) ≤ 1 → ∀ (r : ℝ), 0 < r → |z.val.2.1| + r ≤ α →
      ‖∫ g : C𝔽, φ.val g * firstJet(z) g ∂μ𝔽‖ ≤ (C / r) *
        ∏ w ∈ geometricClusterNeighbors a (χ z.val.1) (center(z)) r,
          (‖w - center(z)‖ / r) ^ ordAt(χ z.val.1, w) := by
  obtain ⟨C, hC, H⟩ := spectralStripGeometricKernel_blocks_bddAbove_forces_zero_product
    a hα hs φ χ x f hχ hb hbound
  refine ⟨C, hC, fun z m hc r hr hmargin ↦ H z m hc r hr hmargin _ ?_ ?_⟩
  · exact fun w hw ↦ ((mem_geometricClusterNeighbors a _ w _ r).mp hw).1
  · exact fun w hw ↦ ((mem_geometricClusterNeighbors a _ w _ r).mp hw).2.1

local notation "simpleSites(" η ", " A ")" =>
  {w : ℂ // |w.re| ≤ A ∧ meromorphicOrderAt (continuedCompletedHeckeL η) ((a : ℂ) + w) = 1}

local notation "blockOf(" ψ ", " z ")" =>
  (∑ m : Fin (jetCount(z)), (⟨((f jet(z, m)).comp (Θ₀).mkQL).smulRight
    (Gₐ ((hardySobolevTestAction μ𝔽 m𝔽 (-α) α s hI hs₀ ψ) (Sₐ(x jet(z, m))))),
    smulRight_mem_nuclearEndomorphisms _ _⟩ : nuclearEndomorphisms _))

/-- Paper: Theorem 10.4.3.5(2), p. 472. If the arbitrary finite geometric sums in #7406
are bounded for every compact test, the product of the normalized distances to all the
other zeros in a fixed disk about a simple site has an inverse-polynomial lower bound in
the height. Every neighboring multiplicity is included. The constants are uniform over
simple centers of the fixed character with the prescribed margin.
Reconstruction: Fixed-support modulation tests the first logarithmic moment of the geometric
singleton. The all-neighbor Jensen obstruction for quotient blocks in #7455 is due to sflicht,
and the fixed-support modulation argument for quotient blocks in #7241 is due to mlyle. -/
theorem spectralStripGeometricKernel_allTests_forces_polynomial_cluster_product
    (hχ : IsSpectralBasepointChoice χ)
    (hb : IsSpectralMarkushevichBasis x f ∧ ∀ j, Dₐ (f j) = stripU(j))
    (hbound : ∀ ψ : BruhatCompactSupport C𝔽, BddAbove (range fun K : Finset zeros(F, χ, a, α) ↦
      traceNorm (∑ z ∈ K, blockOf(ψ, z))))
    (ω : PontryaginDual (ideleClassNorm F).ker) (A R : ℝ) (hR : 0 < R) (hmargin : A + R ≤ α) :
    ∃ c > (0 : ℝ), ∃ N : ℕ, ∀ v : simpleSites(χ ω, A),
      c / (1 + |v.val.im|) ^ N ≤ ∏ w ∈ geometricClusterNeighbors a (χ ω) v.val R,
        (‖w - v.val‖ / R) ^ ordAt(χ ω, w) := by
  apply GeometricBaire.ideleFirstMoment_denominator_lower (χ ω)
    (fun v : simpleSites(χ ω, A) ↦ v.val.re) (fun v ↦ v.val.im)
    (fun v ↦ ∏ w ∈ geometricClusterNeighbors a (χ ω) v.val R, (‖w - v.val‖ / R) ^ ordAt(χ ω, w))
    (fun v ↦ v.property.1)
  · intro v
    refine Finset.prod_pos fun w hw ↦ pow_pos (div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr ?_)) hR) _
    exact ((mem_geometricClusterNeighbors a _ _ _ _).mp hw).1
  · intro ψ
    obtain ⟨C, _, hC⟩ := spectralStripGeometricKernel_blocks_bddAbove_forces_full_zero_product
      a hα hs ψ χ x f hχ hb (hbound ψ)
    refine ⟨C / R, fun v ↦ ?_⟩
    have hvR : |v.val.re| + R ≤ α := by linarith [v.property.1]
    have hv : v.val.re ∈ Ioo (-α) α := abs_lt.mp (by linarith)
    have eqv : (((a + v.val.re : ℝ) : ℂ) + (v.val.im : ℂ) * Complex.I) = (a : ℂ) + v.val := by
      rw [Complex.ofReal_add, add_assoc, Complex.re_add_im]
    have ho : meromorphicOrderAt (continuedCompletedHeckeL (χ ω))
        (((a + v.val.re : ℝ) : ℂ) + (v.val.im : ℂ) * Complex.I) = 1 := eqv ▸ v.property.2
    let z : zeros(F, χ, a, α) := ⟨(ω, v.val.re, v.val.im),
      ⟨⟨hv.1.le, hv.2.le⟩, by rw [ho]; norm_num⟩⟩
    have hn : jetCount(z) = 1 := by
      change spectralStripMultiplicity α s v.val.re _ = 1
      rw [spectralStripMultiplicity_interior hv, ho]; rfl
    let m : Fin (jetCount(z)) := ⟨0, by rw [hn]; decide⟩
    simpa only [z, Complex.re_add_im] using hC z m hn.le R hR hvR

end Blocks

end RiemannMasullo.Isolated
