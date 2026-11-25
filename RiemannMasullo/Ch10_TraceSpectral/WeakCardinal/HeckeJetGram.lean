module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.AngularGram
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_LineGram
public import RiemannMasullo.Ch11_ShellStructure.Sec2a

/-! Native reciprocal Sobolev Gram pairings of the actual Hecke value jets at width zero.
The logarithmic Haar scalar, the angular Fourier factor and the sign of the phase are explicit.
This extends the degree-two comparison of `Sec3_LineGram` to the entire one-value-jet range. -/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField RCLike
open scoped InnerProductSpace Matrix NNReal ENNReal ComplexOrder NumberField.AdeleRing

namespace RiemannMasullo.WeakCardinal

/-- Equality with the project's actual width-zero Sobolev density. -/
theorem weight_eq_intervalSobolevDensity (r x : ℝ) :
    weight r x = intervalSobolevDensity 0 0 (2*r) x := by
  simp [weight, intervalSobolevDensity]

/-- The frequency-line Hilbert model uses the project's positive order-zero-strip measure. -/
theorem sobolevMeasure_eq_intervalSobolevMeasure (r : ℝ) :
    sobolevMeasure r = intervalSobolevMeasure angularMeasure id 0 0 (2*r) := by
  unfold sobolevMeasure intervalSobolevMeasure
  congr 1
  funext x
  simp only [Bool.false_eq_true, ↓reduceIte, id_eq, weight_eq_intervalSobolevDensity]

/-- The second finite Gram quadratic form is the concrete physical weighted Lebesgue integral,
including the angular-frequency normalization and the actual weak Sobolev density. -/
theorem weakQuadratic_eq_native_integral {ι : Type*} [Fintype ι] (r : ℝ) (hr : 1/2 < r)
    (site : ι → ℝ) (c : ι → ℂ) :
    (star c ⬝ᵥ (gramMatrix (r+1) site) *ᵥ c).re =
      (2*Real.pi)⁻¹ * ∫ x : ℝ, intervalSobolevDensity 0 0 (2*(r-1)) x *
        ‖∑ i, c i * evaluationWave r (site i) x‖^2 := by
  calc
    _ = (star c ⬝ᵥ (gramMatrix (2*r-(r-1)) site) *ᵥ c).re :=
      congrArg (fun t : ℝ ↦ (star c ⬝ᵥ (gramMatrix t site) *ᵥ c).re) (by ring)
    _ = _ := by
      rw [quadraticForm_eq_weightedIntegral r (r-1) (by linarith), angularMeasure,
        integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
      simp only [weight_eq_intervalSobolevDensity, angularFactor]
      rfl

private theorem continuous_weight_phase (r d : ℝ) : Continuous fun x ↦ (weight r x : ℂ)*phase d x := by
  have hw : Continuous (weight r) :=
    (show Continuous (fun x : ℝ ↦ 1+x^2) by fun_prop).rpow_const (fun x ↦ .inl (by dsimp; positivity))
  exact (Complex.continuous_ofReal.comp hw).mul
    (continuous_subtype_val.comp (Circle.exp.continuous.comp (continuous_const.mul continuous_id)))

section NativeJets

set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "ν𝔽" => canonicalModulatedHaar m𝔽 hm𝔽
local notation "μs(" s ")" => intervalSobolevMeasure μ𝔽 (logIdeleClassNorm F) (-0) 0 s true
local notation "ord(" j ")" => (j).val.2.2.1
local notation "native(" χ "," hs "," j ")" =>
  (spectralStripJet_memLp χ (le_refl (0 : ℝ)) hs j).toLp
    (spectralZeroJet (F := F) (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2)

local instance : (ν𝔽).IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1

variable (F) in
/-- Conversion between original Tamagawa Haar and the normalized angular-frequency integral
on a single character. The scalar is independent of the sites and of Sobolev order. -/
def heckeJetGramScale : ℝ :=
  (2*Real.pi) * (Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ)

theorem heckeJetGramScale_pos : 0 < heckeJetGramScale F := by
  have hf : 0 < (Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) := by
    exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν𝔽
  exact mul_pos (by positivity) hf

private theorem logNorm_preserving :
    MeasurePreserving (logIdeleClassNorm F) μ𝔽 (Measure.haarScalarFactor μ𝔽 ν𝔽 • volume) := by
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν𝔽]
  exact (orbitalJet_logNorm_measurePreserving (F := F)).smul_measure _

/-- In the whole range `s ≤ 3`, every retained width-zero jet has offset zero and order zero,
including the strict endpoint in the repository’s boundary multiplicity. -/
theorem retained_offset_order_zero {s b : ℝ} {k N : ℕ} (hs : s ≤ 3)
    (hk : k < spectralStripMultiplicity 0 s b N) : b = 0 ∧ k = 0 := by
  have hn : ¬ ((0 : ℝ) < b ∧ b < 0) := fun h ↦ h.1.asymm h.2
  by_cases hb : b = 0
  · refine ⟨hb, ?_⟩
    rw [spectralStripMultiplicity_boundary le_rfl (Or.inr hb)] at hk
    have hlt := ((lt_spectralBoundaryMultiplicity s N k).mp hk).2
    by_contra h
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    linarith
  · simp [spectralStripMultiplicity, hn, hb] at hk

private theorem valueJet_phase (η : PontryaginDual C𝔽) (t : ℝ) (g : C𝔽) :
    spectralZeroJet η 0 t 0 g = ((η g * Circle.exp (t * logIdeleClassNorm F g) : Circle) : ℂ) := by
  have hp : (0 : ℝ) < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  change ((η g : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^
    ((0 : ℂ) + (t : ℂ) * Complex.I)) * _ ^ 0 = _
  rw [zero_add, pow_zero, mul_one, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le, Circle.coe_mul, Circle.coe_exp, Complex.ofReal_mul]
  congr 2
  change (logIdeleClassNorm F g : ℂ) * (t * Complex.I) = _
  ring

private theorem valueJet_inner_phase (η : PontryaginDual C𝔽) (u v : ℝ) (g : C𝔽) :
    ⟪spectralZeroJet η 0 u 0 g, spectralZeroJet η 0 v 0 g⟫_ℂ = phase (v-u) (logIdeleClassNorm F g) := by
  rw [valueJet_phase, valueJet_phase, RCLike.inner_apply, starRingEnd_apply, Complex.star_def,
    ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, phase, sub_mul, Circle.exp_sub]
  congr 1
  rw [← div_eq_mul_inv]
  exact mul_div_mul_left_eq_div (Circle.exp (v * logIdeleClassNorm F g))
    (Circle.exp (u * logIdeleClassNorm F g)) (η g)

private theorem nativeMeasure_eq (s : ℝ) :
    μs(s) = (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (weight (-(s/2)) (logIdeleClassNorm F g))) := by
  unfold intervalSobolevMeasure
  congr 1
  ext g
  simp [intervalSobolevDensity, weight, Real.rpow_neg (by positivity : (0:ℝ) ≤ 1+(logIdeleClassNorm F g)^2)]

private theorem native_withDensity_integral (s : ℝ) (f : C𝔽 → ℂ) :
    (∫ g, f g ∂μs(s)) = ∫ g, (weight (-(s/2)) (logIdeleClassNorm F g) : ℂ) * f g ∂μ𝔽 := by
  have hw : Continuous (weight (-(s/2))) :=
    (show Continuous (fun x : ℝ ↦ 1+x^2) by fun_prop).rpow_const (fun x ↦ .inl (by dsimp; positivity))
  have hm : Measurable (fun g : C𝔽 ↦ ENNReal.ofReal (weight (-(s/2)) (logIdeleClassNorm F g))) :=
    (hw.measurable.comp (logNorm_preserving (F := F)).measurable).ennreal_ofReal
  rw [nativeMeasure_eq, integral_withDensity_eq_integral_toReal_smul hm
    (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae (.of_forall fun g ↦ ?_)
  have hp : 0 ≤ weight (-(s/2)) (logIdeleClassNorm F g) := Real.rpow_nonneg (by positivity) _
  rw [ENNReal.toReal_ofReal hp, Complex.real_smul]

private theorem integral_native_pair (s : ℝ) (η : PontryaginDual C𝔽) (u v : ℝ) :
    (∫ g : C𝔽, ⟪spectralZeroJet η 0 u 0 g, spectralZeroJet η 0 v 0 g⟫_ℂ ∂μs(s)) =
      (heckeJetGramScale F : ℂ) *
        ∫ x : ℝ, (weight (-(s/2)) x : ℂ) * phase (u-v) x ∂angularMeasure := by
  let r := s/2
  let f (x : ℝ) := (weight (-r) x : ℂ) * phase (v-u) x
  have hlog := logNorm_preserving (F := F)
  calc
    _ = ∫ g : C𝔽, f (logIdeleClassNorm F g) ∂μ𝔽 := by
      rw [native_withDensity_integral]
      apply integral_congr_ae (.of_forall fun g ↦ ?_)
      change (weight (-r) (logIdeleClassNorm F g) : ℂ) * ⟪_, _⟫_ℂ = _
      rw [valueJet_inner_phase]
    _ = ∫ x : ℝ, f x ∂(Measure.haarScalarFactor μ𝔽 ν𝔽 • volume) := by
      rw [← hlog.map_eq, integral_map hlog.measurable.aemeasurable
        (continuous_weight_phase (-r) (v-u)).aestronglyMeasurable]
    _ = _ := by
      rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, integral_angularMeasure]
      change _ * (∫ x : ℝ, (weight (-r) x : ℂ)*phase (v-u) x) = _
      rw [integral_even_weight_phase, heckeJetGramScale]
      push_cast
      field_simp [Real.pi_ne_zero]
      rfl

/-- At width zero through Sobolev degree three the native reciprocal-weight pairing on actual
indexed jets of one character is the positive Haar scalar times the angular model’s Gram entry. -/
theorem spectralStripJet_inner_angularGram
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 0 ≤ s) (h₃ : s ≤ 3)
    (j k : SpectralStripJetIndex χ a 0 s) (hχ : j.val.1 = k.val.1) :
    ⟪native(χ,hs,j), native(χ,hs,k)⟫_ℂ = (heckeJetGramScale F : ℂ) *
      gramMatrix (s/2) (fun l : SpectralStripJetIndex χ a 0 s ↦ ord(l)) j k := by
  obtain ⟨jb, jo⟩ := retained_offset_order_zero h₃ j.property
  obtain ⟨kb, ko⟩ := retained_offset_order_zero h₃ k.property
  rw [L2.inner_def]
  calc
    _ = ∫ g : C𝔽, ⟪spectralZeroJet (χ k.val.1) 0 (ord(j)) 0 g,
      spectralZeroJet (χ k.val.1) 0 (ord(k)) 0 g⟫_ℂ ∂μs(s) := by
        apply integral_congr_ae
        filter_upwards [(spectralStripJet_memLp χ (le_refl 0) hs j).coeFn_toLp,
          (spectralStripJet_memLp χ (le_refl 0) hs k).coeFn_toLp] with g hj hk
        rw [hj, hk, jb, kb, jo, ko, hχ]
    _ = _ := integral_native_pair s _ _ _

private theorem valueJet_translate (η : PontryaginDual C𝔽) (u : ℝ) (g : C₁) (x : C𝔽)
    (h : logIdeleClassNorm F (g.val * x) = logIdeleClassNorm F x) :
    spectralZeroJet η 0 u 0 (g.val * x) = (η g.val : ℂ) * spectralZeroJet η 0 u 0 x := by
  rw [valueJet_phase, valueJet_phase, map_mul, h, mul_assoc, Circle.coe_mul]

/-- The norm-one angular characters are orthogonal against every radial reciprocal weight.
In the non-integrable case the Haar integral uses its usual totalized value. -/
private theorem integral_native_pair_ne_character (s : ℝ) (η θ : PontryaginDual C𝔽) (u v : ℝ)
    (g : C₁) (hne : η g.val ≠ θ g.val) :
    (∫ x, ⟪spectralZeroJet η 0 u 0 x, spectralZeroJet θ 0 v 0 x⟫_ℂ ∂μs(s)) = 0 := by
  let c : ℂ := (θ g.val : ℂ) * star (η g.val : ℂ)
  let f (x : C𝔽) := (weight (-(s/2)) (logIdeleClassNorm F x) : ℂ) *
    ⟪spectralZeroJet η 0 u 0 x, spectralZeroJet θ 0 v 0 x⟫_ℂ
  have hc : c ≠ 1 := by
    intro h
    change (θ g.val : ℂ) * star (η g.val : ℂ) = 1 at h
    rw [Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, ← Circle.coe_one] at h
    exact hne (mul_inv_eq_one.mp (show θ g.val * (η g.val)⁻¹ = 1 from Subtype.ext h)).symm
  have he (x : C𝔽) : f (g.val * x) = c * f x := by
    have hL : logIdeleClassNorm F (g.val * x) = logIdeleClassNorm F x := by
      simp only [logIdeleClassNorm, map_mul, show ideleClassNorm F g.val = 1 from g.property, one_mul]
    unfold f c
    rw [hL, valueJet_translate η u g x hL, valueJet_translate θ v g x hL]
    simp only [RCLike.inner_apply, map_mul, starRingEnd_apply]
    ring
  have hI := integral_mul_left_eq_self (μ := μ𝔽) f g.val
  rw [funext he, integral_const_mul] at hI
  rw [native_withDensity_integral]
  change (∫ x, f x ∂μ𝔽) = 0
  apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hc)
  rw [sub_mul, one_mul, hI, sub_self]

/-- Genuine retained jets of different norm-one character are orthogonal in the original
reciprocal weighted Tamagawa Hilbert space throughout the value-jet range. -/
theorem spectralStripJet_inner_zero_of_ne_character
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {a s : ℝ} (hs : 0 ≤ s) (h₃ : s ≤ 3) (j k : SpectralStripJetIndex χ a 0 s)
    (hne : j.val.1 ≠ k.val.1) : ⟪native(χ,hs,j), native(χ,hs,k)⟫_ℂ = 0 := by
  obtain ⟨g, hg⟩ : ∃ g : C₁, j.val.1 g ≠ k.val.1 g := by
    by_contra! h
    exact hne (ContinuousMonoidHom.ext h)
  have hres (ξ : PontryaginDual C₁) : χ ξ g.val = ξ g := DFunLike.congr_fun (hχ ξ) g
  obtain ⟨jb, jo⟩ := retained_offset_order_zero h₃ j.property
  obtain ⟨kb, ko⟩ := retained_offset_order_zero h₃ k.property
  rw [L2.inner_def]
  calc
    _ = ∫ x : C𝔽, ⟪spectralZeroJet (χ j.val.1) 0 (ord(j)) 0 x,
        spectralZeroJet (χ k.val.1) 0 (ord(k)) 0 x⟫_ℂ ∂μs(s) := by
      apply integral_congr_ae
      filter_upwards [(spectralStripJet_memLp χ (le_refl 0) hs j).coeFn_toLp,
        (spectralStripJet_memLp χ (le_refl 0) hs k).coeFn_toLp] with x hj hk
      rw [hj, hk, jb, kb, jo, ko]
    _ = 0 := integral_native_pair_ne_character s _ _ _ _ g (by simpa only [hres] using hg)

/-- Entire native Gram matrices on an arbitrary family of genuine sites of one character
have precisely this same scalar. Finite restrictions require no choice of order on the ordinates. -/
theorem spectralStripJet_gramMatrix_line {ι : Type*}
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 0 ≤ s) (h₃ : s ≤ 3)
    (j : ι → SpectralStripJetIndex χ a 0 s) (hχ : ∀ i k, (j i).val.1 = (j k).val.1) :
    Matrix.gram ℂ (fun i ↦ native(χ,hs,j i)) =
      (heckeJetGramScale F : ℂ) • gramMatrix (s/2) (fun i ↦ ord(j i)) :=
  Matrix.ext fun i k ↦ spectralStripJet_inner_angularGram χ hs h₃ (j i) (j k) (hχ i k)

/-- A finite set of actual width-zero jets on one character has distinct real ordinates
through degree three, irrespective of the order of its Hecke zeros. -/
theorem spectralStripJet_ordinate_injective {χ : PontryaginDual C₁ → PontryaginDual C𝔽} {a s : ℝ}
    (h₃ : s ≤ 3) (S : Finset (SpectralStripJetIndex χ a 0 s))
    (hχ : ∀ i k : S, i.val.val.1 = k.val.val.1) :
    Function.Injective (fun i : S ↦ ord(i.val)) := by
  intro j k hjk
  obtain ⟨jb, jo⟩ := retained_offset_order_zero h₃ j.val.property
  obtain ⟨kb, ko⟩ := retained_offset_order_zero h₃ k.val.property
  exact Subtype.ext <| Subtype.ext <|
    Prod.ext (hχ j k) (Prod.ext (jb.trans kb.symm) (Prod.ext hjk (jo.trans ko.symm)))

/-- The principal Gram of a finite non-repeated family of actual jets of one character
is positive definite, including at the endpoint `s=3`. -/
theorem spectralStripJet_posDef_on_character
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 1 < s) (h₃ : s ≤ 3)
    (S : Finset (SpectralStripJetIndex χ a 0 s)) (hχ : ∀ i k : S, i.val.val.1 = k.val.val.1) :
    (Matrix.gram ℂ (fun i : S ↦ native(χ,(by linarith : 0 ≤ s),i.val))).PosDef := by
  rw [spectralStripJet_gramMatrix_line χ (by linarith : 0 ≤ s) h₃ (fun i : S ↦ i.val) hχ]
  exact (gramMatrix_posDef (s/2) (by linarith) (spectralStripJet_ordinate_injective h₃ S hχ)).smul
    (Complex.zero_lt_real.mpr (heckeJetGramScale_pos (F := F)))

open Classical in
/-- The inverse system of the original Hecke jets uses precisely the reciprocal Haar scale. -/
theorem spectralStripJet_inverse_gramMatrix_on_character
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 1 < s) (h₃ : s ≤ 3)
    (S : Finset (SpectralStripJetIndex χ a 0 s)) (hχ : ∀ i k : S, i.val.val.1 = k.val.val.1) :
    (Matrix.gram ℂ (fun i : S ↦ native(χ,(by linarith : 0 ≤ s),i.val)))⁻¹ =
      (heckeJetGramScale F : ℂ)⁻¹ • (gramMatrix (s/2) (fun i : S ↦ ord(i.val)))⁻¹ := by
  rw [spectralStripJet_gramMatrix_line χ (by linarith : 0 ≤ s) h₃ (fun i : S ↦ i.val) hχ]
  let : Invertible (heckeJetGramScale F : ℂ) := invertibleOfNonzero
    (Complex.ofReal_ne_zero.mpr (heckeJetGramScale_pos (F := F)).ne')
  rw [Matrix.inv_smul _ _ (isUnit_iff_ne_zero.mpr (gramMatrix_det_ne_zero (s/2)
    (by linarith) (spectralStripJet_ordinate_injective h₃ S hχ))), invOf_eq_inv]

/-- Every value wave at an arbitrary frequency is a genuine vector of the native reciprocal
Hilbert space for `s>1`. Its ordinate need not be an arithmetic zero. -/
theorem memLp_nativeValueWave {s : ℝ} (hs : 1 < s) (η : PontryaginDual C𝔽) (u : ℝ) :
    MemLp (spectralZeroJet η 0 u 0) 2 μs(s) := by
  have hw : Continuous (weight (-(s/2))) :=
    (show Continuous (fun x : ℝ ↦ 1+x^2) by fun_prop).rpow_const (fun x ↦ .inl (by dsimp; positivity))
  have hlog := logNorm_preserving (F := F)
  have hm : Measurable (fun g : C𝔽 ↦ ENNReal.ofReal (weight (-(s/2)) (logIdeleClassNorm F g))) :=
    (hw.measurable.comp hlog.measurable).ennreal_ofReal
  have hphase : Continuous (spectralZeroJet η 0 u 0) := by
    rw [funext (valueJet_phase η u)]
    exact continuous_subtype_val.comp (η.continuous.mul (Circle.exp.continuous.comp
      (continuous_const.mul (orbitalJet_logNorm_continuous (F := F)))))
  rw [memLp_two_iff_integrable_sq_norm hphase.aestronglyMeasurable, nativeMeasure_eq,
    integrable_withDensity_iff hm (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  have hi := hlog.integrable_comp_of_integrable
    ((integrable_weight_neg_volume (d := s/2) (by linarith)).smul_measure_nnreal (c := Measure.haarScalarFactor μ𝔽 ν𝔽))
  exact hi.congr (.of_forall fun g ↦ by
    have hp : 0 ≤ weight (-(s/2)) (logIdeleClassNorm F g) := Real.rpow_nonneg (by positivity) _
    simp only [Function.comp_apply, valueJet_phase, Circle.norm_coe, one_pow, one_mul, ENNReal.toReal_ofReal hp])

/-- A value jet may be placed in every admissible reciprocal-weight norm, including the
second order needed for the weak cardinal readout. -/
def nativeValueWave (s : ℝ) (hs : 1 < s) (η : PontryaginDual C𝔽) (u : ℝ) : Lp ℂ 2 μs(s) :=
  (memLp_nativeValueWave hs η u).toLp (spectralZeroJet η 0 u 0)

/-- The genuine indexed Hecke jet is the indicated native value wave, with no scalar change. -/
theorem spectralStripJet_eq_nativeValueWave
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 1 < s) (h₃ : s ≤ 3)
    (j : SpectralStripJetIndex χ a 0 s) :
    native(χ,(by linarith : 0 ≤ s),j) = nativeValueWave s hs (χ j.val.1) (ord(j)) := by
  obtain ⟨jb, jo⟩ := retained_offset_order_zero h₃ j.property
  apply Lp.ext
  filter_upwards [(spectralStripJet_memLp χ (le_refl 0) (by linarith : 0 ≤ s) j).coeFn_toLp,
    (memLp_nativeValueWave hs (χ j.val.1) (ord(j))).coeFn_toLp] with g hj hw
  change _ = (memLp_nativeValueWave hs (χ j.val.1) (ord(j))).toLp _ g
  rw [hj, hw, jb, jo]

/-- At arbitrary Sobolev orders the Gram of native value waves still has the same normalization. -/
theorem gram_nativeValueWave {ι : Type*} (s : ℝ) (hs : 1 < s) (η : PontryaginDual C𝔽) (site : ι → ℝ) :
    Matrix.gram ℂ (fun i ↦ nativeValueWave s hs η (site i)) =
      (heckeJetGramScale F : ℂ) • gramMatrix (s/2) site := by
  ext i k
  rw [Matrix.gram_apply, L2.inner_def]
  calc
    _ = ∫ g : C𝔽, ⟪spectralZeroJet η 0 (site i) 0 g, spectralZeroJet η 0 (site k) 0 g⟫_ℂ ∂μs(s) := by
      apply integral_congr_ae
      filter_upwards [(memLp_nativeValueWave hs η (site i)).coeFn_toLp,
        (memLp_nativeValueWave hs η (site k)).coeFn_toLp] with g hi hk
      change ⟪(memLp_nativeValueWave hs η (site i)).toLp _ g, (memLp_nativeValueWave hs η (site k)).toLp _ g⟫_ℂ = _
      rw [hi, hk]
    _ = _ := integral_native_pair s η (site i) (site k)

/-- Put the same value jets into the native reciprocal space of order `s+2`. The squared
norm of any finite sum reads the second angular Gram `G_(s/2+1)`, with exactly one Haar scale. -/
theorem norm_sq_nativeValueWave_weak {ι : Type*} [Fintype ι] (s : ℝ) (hs : 1 < s)
    (η : PontryaginDual C𝔽) (site : ι → ℝ) (c : ι → ℂ) :
    ‖∑ i, c i • nativeValueWave (s+2) (by linarith) η (site i)‖^2 =
      heckeJetGramScale F * (star c ⬝ᵥ (gramMatrix (s/2+1) site) *ᵥ c).re := by
  let v (i : ι) := nativeValueWave (s+2) (by linarith) η (site i)
  calc
    _ = (star c ⬝ᵥ (Matrix.gram ℂ v) *ᵥ c).re := by
      rw [Matrix.star_dotProduct_gram_mulVec]
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
    _ = _ := by
      rw [show Matrix.gram ℂ v = _ from gram_nativeValueWave (s+2) (by linarith) η site,
        Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul,
        show (s+2)/2 = s/2+1 by ring]

end NativeJets
end RiemannMasullo.WeakCardinal
