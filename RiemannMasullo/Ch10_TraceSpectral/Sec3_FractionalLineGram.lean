module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
public import RiemannMasullo.ForMathlib.Analysis.Fourier.FractionalModel
import RiemannMasullo.Ch11_ShellStructure.Sec2a

/-! # Reciprocal line Gram kernels for fractional Sobolev exponents

This extends the unrestricted-wave calculation in `Sec3_LineGram` from degree two
to every degree greater than one. The exact reciprocal density and Tamagawa scalar
are retained, so the result can be matched to the ordinary Fourier model.
-/

@[expose] public noncomputable section

open MeasureTheory NumberField
open scoped InnerProductSpace NNReal NumberField.AdeleRing

namespace RiemannMasullo.Isolated

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
variable {s : ℝ}

local notation "μs" => intervalSobolevMeasure μ𝔽 (logIdeleClassNorm F) (-0) 0 s true

local instance fractionalLineGramCanonicalHaar : (ν𝔽).IsHaarMeasure :=
  (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1

/-- At zero real offset, the zeroth spectral jet is the unitary angular-frequency wave. -/
theorem spectralZeroJet_line_phase (η : PontryaginDual C𝔽) (t : ℝ) (g : C𝔽) :
    spectralZeroJet η 0 t 0 g = ((η g * Circle.exp (t * logIdeleClassNorm F g) : Circle) : ℂ) := by
  have hp : (0 : ℝ) < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  change ((η g : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^
    ((0 : ℂ) + (t : ℂ) * Complex.I)) * _ ^ 0 = _
  rw [zero_add, pow_zero, mul_one, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le, Circle.coe_mul, Circle.coe_exp, Complex.ofReal_mul]
  congr 2
  change (logIdeleClassNorm F g : ℂ) * (t * Complex.I) = _
  ring

private theorem fractionalLineGram_phase_inner (η : PontryaginDual C𝔽) (u v : ℝ) (g : C𝔽) :
    ⟪spectralZeroJet η 0 u 0 g, spectralZeroJet η 0 v 0 g⟫_ℂ =
      Complex.exp (↑((v - u) * logIdeleClassNorm F g) * Complex.I) := by
  rw [spectralZeroJet_line_phase, spectralZeroJet_line_phase, RCLike.inner_apply, starRingEnd_apply, Complex.star_def,
    ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, ← Circle.coe_exp, sub_mul, Circle.exp_sub]
  congr 1
  rw [← div_eq_mul_inv]
  exact mul_div_mul_left_eq_div (Circle.exp (v * logIdeleClassNorm F g))
    (Circle.exp (u * logIdeleClassNorm F g)) (η g)

private theorem fractionalLineGram_log_preserving : MeasurePreserving (logIdeleClassNorm F) μ𝔽
    (Measure.haarScalarFactor μ𝔽 ν𝔽 • volume) := by
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν𝔽]
  exact (orbitalJet_logNorm_measurePreserving (F := F)).smul_measure _

private theorem fractionalLineGram_density :
    μs = (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal ((1 + (logIdeleClassNorm F g) ^ 2) ^ (-s / 2))) := by
  simp only [intervalSobolevMeasure, intervalSobolevDensity, neg_zero, mul_zero, zero_mul,
    Real.exp_zero, max_self, one_mul, ite_true]
  congr 1
  funext g
  rw [neg_div, Real.rpow_neg (by positivity), ENNReal.ofReal_inv_of_pos (by positivity)]

private theorem fractionalLineGram_density_measurable :
    Measurable fun g : C𝔽 ↦ ENNReal.ofReal ((1 + (logIdeleClassNorm F g) ^ 2) ^ (-s / 2)) := by
  have hm := (fractionalLineGram_log_preserving (F := F)).measurable
  fun_prop

/-- Above degree one, every unitary real-frequency wave belongs to the reciprocal line space. -/
theorem spectralZeroJet_memLp_line_fractional (hs : 1 < s) (η : PontryaginDual C𝔽) (t : ℝ) :
    MemLp (spectralZeroJet η 0 t 0) 2 μs := by
  have hphase : Continuous (spectralZeroJet η 0 t 0) := by
    rw [funext (spectralZeroJet_line_phase η t)]
    exact continuous_subtype_val.comp (η.continuous.mul (Circle.exp.continuous.comp
      (continuous_const.mul (orbitalJet_logNorm_continuous (F := F)))))
  apply (memLp_two_iff_integrable_sq_norm hphase.aestronglyMeasurable).2
  rw [fractionalLineGram_density, integrable_withDensity_iff fractionalLineGram_density_measurable
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  have hi₀ : Integrable (fun x : ℝ ↦ (1 + x ^ 2) ^ (-s / 2)) := by
    convert integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := (volume : Measure ℝ)) (r := s)
      (by simpa only [Module.finrank_self, Nat.cast_one] using hs) using 1
    funext x
    rw [Real.norm_eq_abs, sq_abs]
  have hi := (fractionalLineGram_log_preserving (F := F)).integrable_comp_of_integrable
    (hi₀.smul_measure_nnreal (c := Measure.haarScalarFactor μ𝔽 ν𝔽))
  apply hi.congr (ae_of_all _ fun g ↦ ?_)
  simp only [Function.comp_apply, spectralZeroJet_line_phase, Circle.norm_coe, one_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 + (logIdeleClassNorm F g) ^ 2) ^ (-s / 2)), one_mul]

/-- The unrestricted frequency wave in the reciprocal line space of degree `s > 1`. -/
def spectralLineFractionalWave (hs : 1 < s) (η : PontryaginDual C𝔽) (t : ℝ) : Lp ℂ 2 μs :=
  (spectralZeroJet_memLp_line_fractional hs η t).toLp (spectralZeroJet η 0 t 0)

/-- Almost everywhere the wave is the actual zeroth-jet function. -/
theorem spectralLineFractionalWave_coeFn (hs : 1 < s) (η : PontryaginDual C𝔽) (t : ℝ) :
    (spectralLineFractionalWave hs η t : C𝔽 → ℂ) =ᵐ[μs] spectralZeroJet η 0 t 0 :=
  (spectralZeroJet_memLp_line_fractional hs η t).coeFn_toLp

/-- The reciprocal-space wave represents the same function almost everywhere for Haar measure. -/
theorem spectralLineFractionalWave_coeFn_haar (hs : 1 < s) (η : PontryaginDual C𝔽) (t : ℝ) :
    (spectralLineFractionalWave hs η t : C𝔽 → ℂ) =ᵐ[μ𝔽] spectralZeroJet η 0 t 0 := by
  have hbase : μ𝔽 ≪ μs := by
    rw [fractionalLineGram_density]
    exact withDensity_absolutelyContinuous' fractionalLineGram_density_measurable.aemeasurable
      (.of_forall fun g ↦ (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos (by positivity) (-s / 2))).ne')
  exact hbase.ae_eq (spectralLineFractionalWave_coeFn hs η t)

private theorem fractionalLineGram_wave_inner_integral (hs : 1 < s) (η θ : PontryaginDual C𝔽) (u v : ℝ) :
    ⟪spectralLineFractionalWave hs η u, spectralLineFractionalWave hs θ v⟫_ℂ =
      ∫ g : C𝔽, (((1 + (logIdeleClassNorm F g) ^ 2) ^ (-s / 2) : ℝ) : ℂ) *
        ⟪spectralZeroJet η 0 u 0 g, spectralZeroJet θ 0 v 0 g⟫_ℂ ∂μ𝔽 := by
  rw [L2.inner_def]
  calc
    _ = ∫ g : C𝔽, ⟪spectralZeroJet η 0 u 0 g, spectralZeroJet θ 0 v 0 g⟫_ℂ ∂μs := by
      apply integral_congr_ae
      filter_upwards [spectralLineFractionalWave_coeFn hs η u, spectralLineFractionalWave_coeFn hs θ v] with g hu hv
      rw [hu, hv]
    _ = _ := by
      rw [fractionalLineGram_density, integral_withDensity_eq_integral_toReal_smul fractionalLineGram_density_measurable
        (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
      apply integral_congr_ae (ae_of_all _ fun g ↦ ?_)
      rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]

/-- The reciprocal-weight inner product of two waves on any one unitary character.
The Fourier density is the reciprocal Sobolev weight, with the actual Tamagawa scalar. -/
theorem spectralLineFractionalWave_inner (hs : 1 < s) (η : PontryaginDual C𝔽) (u v : ℝ) :
    ⟪spectralLineFractionalWave hs η u, spectralLineFractionalWave hs η v⟫_ℂ =
      (Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) •
        ∫ x : ℝ, Complex.exp (↑((v - u) * x) * Complex.I) *
          (((1 + x ^ 2) ^ (-s / 2) : ℝ) : ℂ) := by
  let d := v - u
  let f (x : ℝ) := Complex.exp (↑(d * x) * Complex.I) * (((1 + x ^ 2) ^ (-s / 2) : ℝ) : ℂ)
  have hn (x : ℝ) : 1 + x ^ 2 ≠ 0 := by positivity
  have hw : Continuous (fun x : ℝ ↦ (1 + x ^ 2) ^ (-s / 2)) :=
    (continuous_const.add (continuous_id.pow 2)).rpow_const (fun x ↦ Or.inl (hn x))
  have hf : Continuous f := by unfold f; fun_prop
  have hlog := fractionalLineGram_log_preserving (F := F)
  rw [fractionalLineGram_wave_inner_integral hs]
  calc
    _ = ∫ g : C𝔽, f (logIdeleClassNorm F g) ∂μ𝔽 := by
      apply integral_congr_ae (ae_of_all _ fun g ↦ ?_)
      rw [fractionalLineGram_phase_inner, mul_comm]
    _ = ∫ x : ℝ, f x ∂(Measure.haarScalarFactor μ𝔽 ν𝔽 • volume) := by
      rw [← hlog.map_eq, integral_map hlog.measurable.aemeasurable hf.aestronglyMeasurable]
    _ = _ := by rw [integral_smul_nnreal_measure, NNReal.smul_def]

private theorem fractionalLineGram_jet_translate (η : PontryaginDual C𝔽) (t : ℝ) (k : C₁) (x : C𝔽)
    (hL : logIdeleClassNorm F (k.val * x) = logIdeleClassNorm F x) :
    spectralZeroJet η 0 t 0 (k.val * x) = (η k.val : ℂ) * spectralZeroJet η 0 t 0 x := by
  rw [spectralZeroJet_line_phase, spectralZeroJet_line_phase, map_mul, hL, mul_assoc, Circle.coe_mul]

/-- Waves are orthogonal whenever the two characters have different restrictions to
the norm-one subgroup, independently of their real frequencies. -/
theorem spectralLineFractionalWave_inner_eq_zero (hs : 1 < s) (η θ : PontryaginDual C𝔽) (u v : ℝ)
    (k : C₁) (hne : η k.val ≠ θ k.val) :
    ⟪spectralLineFractionalWave hs η u, spectralLineFractionalWave hs θ v⟫_ℂ = 0 := by
  let c : ℂ := (θ k.val : ℂ) * star (η k.val : ℂ)
  let f (x : C𝔽) := (((1 + (logIdeleClassNorm F x) ^ 2) ^ (-s / 2) : ℝ) : ℂ) *
    ⟪spectralZeroJet η 0 u 0 x, spectralZeroJet θ 0 v 0 x⟫_ℂ
  have hc : c ≠ 1 := by
    intro h
    change (θ k.val : ℂ) * star (η k.val : ℂ) = 1 at h
    rw [Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, ← Circle.coe_one] at h
    have h' : θ k.val * (η k.val)⁻¹ = 1 := Subtype.ext h
    exact hne (mul_inv_eq_one.mp h').symm
  have he (x : C𝔽) : f (k.val * x) = c * f x := by
    have hL : logIdeleClassNorm F (k.val * x) = logIdeleClassNorm F x := by
      simp only [logIdeleClassNorm, map_mul, show ideleClassNorm F k.val = 1 from k.property,
        one_mul]
    unfold f c
    rw [hL, fractionalLineGram_jet_translate η u k x hL, fractionalLineGram_jet_translate θ v k x hL]
    simp only [RCLike.inner_apply, map_mul, starRingEnd_apply]
    ring
  have hI := integral_mul_left_eq_self (μ := μ𝔽) f k.val
  rw [funext he, integral_const_mul] at hI
  rw [fractionalLineGram_wave_inner_integral hs]
  change (∫ x, f x ∂μ𝔽) = 0
  apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hc)
  rw [sub_mul, one_mul, hI, sub_self]



private theorem fractionalLineGram_offset_order {s b : ℝ} (hs : s ≤ 3) {k N : ℕ}
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

/-- Up to degree three every retained zero-width jet is its zeroth-order frequency wave. -/
theorem spectralStripJet_eq_wave_line_fractional (hs : 1 < s) (hs₃ : s ≤ 3)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a : ℝ} (j : SpectralStripJetIndex χ a 0 s) :
    (spectralStripJet_memLp χ (le_refl (0 : ℝ)) (zero_le_one.trans hs.le) j).toLp
      (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2) =
        spectralLineFractionalWave hs (χ j.val.1) j.val.2.2.1 := by
  obtain ⟨jb, jo⟩ := fractionalLineGram_offset_order hs₃ j.property
  apply Lp.ext
  filter_upwards [(spectralStripJet_memLp χ (le_refl (0 : ℝ)) (zero_le_one.trans hs.le) j).coeFn_toLp,
    spectralLineFractionalWave_coeFn hs (χ j.val.1) j.val.2.2.1] with g hj hw
  rw [hj, hw, jb, jo]

end RiemannMasullo.Isolated
