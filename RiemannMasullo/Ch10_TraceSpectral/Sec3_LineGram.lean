module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.ExponentialGram
import RiemannMasullo.Ch11_ShellStructure.Sec2a
import RiemannMasullo.ForMathlib.Analysis.Fourier.AbelLimit
import Mathlib.Data.Finset.Sort

/-! # Principal Gram matrices on one character of the Sobolev line

At width zero and exponent two every retained jet has order zero. The reciprocal
Sobolev density gives the Cauchy kernel in log norm, whose Fourier transform gives
the exponential covariance on the ordinates. The inverse diagonal on an arbitrary
finite block of one character therefore depends only on the adjacent gaps.
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
local notation "μ₂" => intervalSobolevMeasure μ𝔽 (logIdeleClassNorm F) (-0) 0 2 true

local instance lineGramCanonicalHaar : (ν𝔽).IsHaarMeasure :=
  (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1

local notation "uJet(" χ ", " j ")" =>
  (spectralStripJet_memLp χ (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2) j).toLp
    (spectralZeroJet (F := F) (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2)

private theorem lineGram_offset_order {b : ℝ} {k N : ℕ} (hk : k < spectralStripMultiplicity 0 2 b N) :
    b = 0 ∧ k = 0 := by
  have hn : ¬ ((0 : ℝ) < b ∧ b < 0) := fun h ↦ h.1.asymm h.2
  by_cases hb : b = 0
  · refine ⟨hb, ?_⟩
    rw [spectralStripMultiplicity_boundary le_rfl (Or.inr hb)] at hk
    have hlt := ((lt_spectralBoundaryMultiplicity 2 N k).mp hk).2
    by_contra h
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    linarith
  · simp [spectralStripMultiplicity, hn, hb] at hk

private theorem lineGram_jet_phase (η : PontryaginDual C𝔽) (t : ℝ) (g : C𝔽) :
    spectralZeroJet η 0 t 0 g = ((η g * Circle.exp (t * logIdeleClassNorm F g) : Circle) : ℂ) := by
  have hp : (0 : ℝ) < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  change ((η g : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^
    ((0 : ℂ) + (t : ℂ) * Complex.I)) * _ ^ 0 = _
  rw [zero_add, pow_zero, mul_one, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
    ← Complex.ofReal_log hp.le, Circle.coe_mul, Circle.coe_exp, Complex.ofReal_mul]
  congr 2
  change (logIdeleClassNorm F g : ℂ) * (t * Complex.I) = _
  ring

private theorem lineGram_phase_inner (η : PontryaginDual C𝔽) (u v : ℝ) (g : C𝔽) :
    ⟪spectralZeroJet η 0 u 0 g, spectralZeroJet η 0 v 0 g⟫_ℂ =
      Complex.exp (↑((v - u) * logIdeleClassNorm F g) * Complex.I) := by
  rw [lineGram_jet_phase, lineGram_jet_phase, RCLike.inner_apply, starRingEnd_apply, Complex.star_def,
    ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, ← Circle.coe_exp, sub_mul, Circle.exp_sub]
  congr 1
  rw [← div_eq_mul_inv]
  exact mul_div_mul_left_eq_div (Circle.exp (v * logIdeleClassNorm F g))
    (Circle.exp (u * logIdeleClassNorm F g)) (η g)

private theorem lineGram_log_preserving : MeasurePreserving (logIdeleClassNorm F) μ𝔽
    (Measure.haarScalarFactor μ𝔽 ν𝔽 • volume) := by
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν𝔽]
  exact (orbitalJet_logNorm_measurePreserving (F := F)).smul_measure _

private theorem lineGram_density :
    μ₂ = (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal ((1 + (logIdeleClassNorm F g) ^ 2)⁻¹)) := by
  simp [intervalSobolevMeasure, intervalSobolevDensity]

private theorem lineGram_density_measurable :
    Measurable fun g : C𝔽 ↦ ENNReal.ofReal ((1 + (logIdeleClassNorm F g) ^ 2)⁻¹) :=
  (measurable_const.add ((lineGram_log_preserving (F := F)).measurable.pow_const 2)).inv.ennreal_ofReal

/-- At degree two on the line every character times a real-frequency wave belongs
to the reciprocal-weight space, at arbitrary frequencies. -/
theorem spectralZeroJet_memLp_line_two (η : PontryaginDual C𝔽) (t : ℝ) :
    MemLp (spectralZeroJet η 0 t 0) 2 μ₂ := by
  have hphase : Continuous (spectralZeroJet η 0 t 0) := by
    rw [funext (lineGram_jet_phase η t)]
    exact continuous_subtype_val.comp (η.continuous.mul (Circle.exp.continuous.comp
      (continuous_const.mul (orbitalJet_logNorm_continuous (F := F)))))
  apply (memLp_two_iff_integrable_sq_norm hphase.aestronglyMeasurable).2
  rw [lineGram_density, integrable_withDensity_iff lineGram_density_measurable
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  have hi := (lineGram_log_preserving (F := F)).integrable_comp_of_integrable
    (integrable_inv_one_add_sq.smul_measure_nnreal (c := Measure.haarScalarFactor μ𝔽 ν𝔽))
  apply hi.congr (ae_of_all _ fun g ↦ ?_)
  simp only [Function.comp_apply, lineGram_jet_phase, Circle.norm_coe, one_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 + (logIdeleClassNorm F g) ^ 2)⁻¹), one_mul]

/-- The order-zero wave in the reciprocal-weight space on the degree-two line. -/
def spectralLineTwoWave (η : PontryaginDual C𝔽) (t : ℝ) : Lp ℂ 2 μ₂ :=
  (spectralZeroJet_memLp_line_two η t).toLp (spectralZeroJet η 0 t 0)

/-- Almost everywhere the wave is the actual zeroth-jet function. -/
theorem spectralLineTwoWave_coeFn (η : PontryaginDual C𝔽) (t : ℝ) :
    (spectralLineTwoWave η t : C𝔽 → ℂ) =ᵐ[μ₂] spectralZeroJet η 0 t 0 :=
  (spectralZeroJet_memLp_line_two η t).coeFn_toLp

private theorem lineGram_wave_inner_integral (η θ : PontryaginDual C𝔽) (u v : ℝ) :
    ⟪spectralLineTwoWave η u, spectralLineTwoWave θ v⟫_ℂ =
      ∫ g : C𝔽, (((1 + (logIdeleClassNorm F g) ^ 2)⁻¹ : ℝ) : ℂ) *
        ⟪spectralZeroJet η 0 u 0 g, spectralZeroJet θ 0 v 0 g⟫_ℂ ∂μ𝔽 := by
  rw [L2.inner_def]
  calc
    _ = ∫ g : C𝔽, ⟪spectralZeroJet η 0 u 0 g, spectralZeroJet θ 0 v 0 g⟫_ℂ ∂μ₂ := by
      apply integral_congr_ae
      filter_upwards [spectralLineTwoWave_coeFn η u, spectralLineTwoWave_coeFn θ v] with g hu hv
      rw [hu, hv]
    _ = _ := by
      rw [lineGram_density, integral_withDensity_eq_integral_toReal_smul lineGram_density_measurable
        (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
      apply integral_congr_ae (ae_of_all _ fun g ↦ ?_)
      rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]

/-- The reciprocal-weight inner product of two waves on any one unitary character.
The positive factor is the same for every frequency and every character. -/
theorem spectralLineTwoWave_inner (η : PontryaginDual C𝔽) (u v : ℝ) :
    ⟪spectralLineTwoWave η u, spectralLineTwoWave η v⟫_ℂ =
      (((Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) * Real.pi * Real.exp (-|u - v|) : ℝ) : ℂ) := by
  let d := v - u
  let f (x : ℝ) := Complex.exp (↑(d * x) * Complex.I) * (((1 + x ^ 2)⁻¹ : ℝ) : ℂ)
  have hn (x : ℝ) : 1 + x ^ 2 ≠ 0 := by positivity
  have hf : Continuous f := by unfold f; fun_prop (disch := exact hn _)
  have hlog := lineGram_log_preserving (F := F)
  rw [lineGram_wave_inner_integral]
  calc
    _ = ∫ g : C𝔽, f (logIdeleClassNorm F g) ∂μ𝔽 := by
      apply integral_congr_ae (ae_of_all _ fun g ↦ ?_)
      rw [lineGram_phase_inner, mul_comm]
    _ = ∫ x : ℝ, f x ∂(Measure.haarScalarFactor μ𝔽 ν𝔽 • volume) := by
      rw [← hlog.map_eq, integral_map hlog.measurable.aemeasurable hf.aestronglyMeasurable]
    _ = _ := by
      rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul,
        show (∫ x : ℝ, f x) = _ from integral_cexp_mul_inv_one_add_sq d,
        show |d| = |u - v| from abs_sub_comm _ _]
      push_cast
      ring

private theorem lineGram_jet_translate (η : PontryaginDual C𝔽) (t : ℝ) (k : C₁) (x : C𝔽)
    (hL : logIdeleClassNorm F (k.val * x) = logIdeleClassNorm F x) :
    spectralZeroJet η 0 t 0 (k.val * x) = (η k.val : ℂ) * spectralZeroJet η 0 t 0 x := by
  rw [lineGram_jet_phase, lineGram_jet_phase, map_mul, hL, mul_assoc, Circle.coe_mul]

/-- Waves are orthogonal whenever the two characters have different restrictions to
the norm-one subgroup, independently of their real frequencies. -/
theorem spectralLineTwoWave_inner_eq_zero (η θ : PontryaginDual C𝔽) (u v : ℝ)
    (k : C₁) (hne : η k.val ≠ θ k.val) :
    ⟪spectralLineTwoWave η u, spectralLineTwoWave θ v⟫_ℂ = 0 := by
  let c : ℂ := (θ k.val : ℂ) * star (η k.val : ℂ)
  let f (x : C𝔽) := (((1 + (logIdeleClassNorm F x) ^ 2)⁻¹ : ℝ) : ℂ) *
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
    rw [hL, lineGram_jet_translate η u k x hL, lineGram_jet_translate θ v k x hL]
    simp only [RCLike.inner_apply, map_mul, starRingEnd_apply]
    ring
  have hI := integral_mul_left_eq_self (μ := μ𝔽) f k.val
  rw [funext he, integral_const_mul] at hI
  rw [lineGram_wave_inner_integral]
  change (∫ x, f x ∂μ𝔽) = 0
  apply (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hc)
  rw [sub_mul, one_mul, hI, sub_self]

/-- Each retained jet at degree two on the line is its zeroth-order frequency wave. -/
theorem spectralStripJet_eq_wave_line_two (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a : ℝ}
    (j : SpectralStripJetIndex χ a 0 2) :
    uJet(χ, j) = spectralLineTwoWave (χ j.val.1) j.val.2.2.1 := by
  obtain ⟨jb, jo⟩ := lineGram_offset_order j.property
  apply Lp.ext
  filter_upwards [(spectralStripJet_memLp χ (le_refl 0) (by norm_num : (0 : ℝ) ≤ 2) j).coeFn_toLp,
    spectralLineTwoWave_coeFn (χ j.val.1) j.val.2.2.1] with g hj hw
  rw [hj, hw, jb, jo]

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455.
At width zero and exponent two the reciprocal-weight Gram pairing of retained jets
within one character is exponential in the gap, times the Cauchy weight's mass. -/
theorem spectralStripJet_inner_line_two
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a : ℝ}
    (j k : SpectralStripJetIndex χ a 0 2) (hχ : j.val.1 = k.val.1) :
    ⟪uJet(χ, j), uJet(χ, k)⟫_ℂ = (((Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) *
      Real.pi * Real.exp (-|j.val.2.2.1 - k.val.2.2.1|) : ℝ) : ℂ) := by
  rw [spectralStripJet_eq_wave_line_two, spectralStripJet_eq_wave_line_two, hχ, spectralLineTwoWave_inner]

/-- Every finite block on one character has a strictly increasing enumeration by its
ordinates at degree two, including when the completed Hecke function has multiple zeros. -/
theorem spectralStripJet_exists_ordered_line_two
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a : ℝ}
    (S : Finset (SpectralStripJetIndex χ a 0 2))
    (hχ : ∀ j k : S, j.val.val.1 = k.val.val.1) :
    ∃ e : Fin S.card ≃ S, StrictMono (fun i ↦ (e i).val.val.2.2.1) := by
  let t (j : S) := j.val.val.2.2.1
  have hi : Function.Injective t := by
    intro j k hjk
    obtain ⟨jb, jo⟩ := lineGram_offset_order j.val.property
    obtain ⟨kb, ko⟩ := lineGram_offset_order k.val.property
    exact Subtype.ext <| Subtype.ext <|
      Prod.ext (hχ j k) (Prod.ext (jb.trans kb.symm) (Prod.ext hjk (jo.trans ko.symm)))
  let := LinearOrder.lift' t hi
  let e := Fintype.orderIsoFinOfCardEq S (Fintype.card_coe S)
  exact ⟨e.toEquiv, e.strictMono⟩

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455.
At width zero and exponent two the squared finite Gram factor in the majorant
equals one plus the two adjacent gap contributions on any sorted block of one
character. This includes all retained orders, regardless of the arithmetic
multiplicities at the sites. -/
theorem spectralStripJet_norm_mul_finiteGramCoordinate_sq_line_two
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a : ℝ}
    (S : Finset (SpectralStripJetIndex χ a 0 2)) {n : ℕ} (e : Fin n ≃ S)
    (hsort : StrictMono (fun i ↦ (e i).val.val.2.2.1))
    (hχ : ∀ j k : S, j.val.val.1 = k.val.val.1) (i : Fin n) :
    (‖uJet(χ, (e i).val)‖ * finiteGramCoordinate (fun j ↦ uJet(χ, j)) (e i).val S) ^ 2 =
      exponentialGramDiagonal (fun j ↦ (e j).val.val.2.2.1) i := by
  have hc : 0 < (Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) := by
    exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν𝔽
  exact norm_mul_finiteGramCoordinate_sq_of_exponential_inner (fun j ↦ uJet(χ, j)) S e _ hsort
    (mul_pos hc Real.pi_pos) (fun j k ↦ spectralStripJet_inner_line_two χ _ _ (hχ (e j) (e k))) i

open Classical in
/-- Paper: Theorem 10.3.2.1(1), pp. 453–455.
For an arbitrary principal block in the finite Gram majorant, sort the retained
sites of each character by their ordinate. All factors for that character in the
original matrix are determined by the two neighboring sites in this ordering. -/
theorem spectralStripJet_finiteGram_by_character_line_two
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) {a : ℝ}
    (S : Finset (SpectralStripJetIndex χ a 0 2)) (ω : PontryaginDual C₁) :
    let T := S.filter (fun j ↦ j.val.1 = ω)
    ∃ e : Fin T.card ≃ T, StrictMono (fun j ↦ (e j).val.val.2.2.1) ∧
      ∀ i, (‖uJet(χ, (e i).val)‖ * finiteGramCoordinate (fun j ↦ uJet(χ, j)) (e i).val S) ^ 2 =
        exponentialGramDiagonal (fun j ↦ (e j).val.val.2.2.1) i := by
  intro T
  have hT (j : T) : j.val.val.1 = ω := (Finset.mem_filter.mp j.property).2
  have hsame (j k : T) : j.val.val.1 = k.val.val.1 := (hT j).trans (hT k).symm
  obtain ⟨e, he⟩ := spectralStripJet_exists_ordered_line_two χ T hsame
  refine ⟨e, he, fun i ↦ ?_⟩
  have hoff (j) (hj : j ∈ T) (k) (hk : k ∈ S) (hk' : k ∉ T) :
      ⟪uJet(χ, j), uJet(χ, k)⟫_ℂ = 0 := by
    have hne : j.val.1 ≠ k.val.1 := fun h ↦
      hk' (Finset.mem_filter.mpr ⟨hk, h.symm.trans (hT ⟨j, hj⟩)⟩)
    obtain ⟨g, hg⟩ : ∃ g : C₁, j.val.1 g ≠ k.val.1 g := by
      by_contra! h
      exact hne (ContinuousMonoidHom.ext h)
    have hres (ξ : PontryaginDual C₁) : χ ξ g.val = ξ g := DFunLike.congr_fun (hχ ξ) g
    rw [spectralStripJet_eq_wave_line_two, spectralStripJet_eq_wave_line_two]
    exact spectralLineTwoWave_inner_eq_zero _ _ _ _ g (by simpa only [hres] using hg)
  have hu := spectralStripJet_toLp_linearIndependent χ hχ a (le_refl 0) (by norm_num : (0 : ℝ) ≤ 2)
  rw [finiteGramCoordinate_eq_of_orthogonal hu (Finset.filter_subset _ S) (e i).property hoff]
  exact spectralStripJet_norm_mul_finiteGramCoordinate_sq_line_two χ T e he hsame i

end RiemannMasullo.Isolated
