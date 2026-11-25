module

public import RiemannMasullo.Ch01_Introduction.Sec4_ExpandingPoisson
public import RiemannMasullo.Ch06_LocalGlobal.Sec3_HeckeEulerAsymptotic
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.HorizontalDigamma

/-! # The large real-abscissa arithmetic mass

The conductor, polar term and local gamma shifts determine the scaled completed
logarithmic derivative with an error bounded by a character-dependent constant
divided by the width. The first digamma correction contributes a real parity
term or half the complex angular weight.
Compare the classical digamma expansion, DLMF 5.11.2.
-/

@[expose] public noncomputable section

open Classical Filter NumberField
open scoped ENNReal Topology

namespace RiemannMasullo.HeckePoisson

variable {F : Type*} [Field F] [NumberField F]

/-- The first horizontal correction in the gamma product, written in terms of each
real sign parity or complex angular weight of the original character. -/
def archimedeanCountConstant (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) : ℝ :=
  ∑ v : InfinitePlace F, if hv : v.IsReal then
    ((realHeckeCharacter_parameters χ v hv).exists.choose.2.val : ℝ) / 2 - 1 / 4
  else
    ((complexHeckeCharacter_parameters χ v
      (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.2.natAbs : ℝ) / 2

/-- The scaled logarithmic derivative of the archimedean product has inverse-width
error after subtracting the field-degree term and the infinity-type corrections. -/
theorem eventually_abs_mul_re_heckeGamma_logDeriv_sub_main_le
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ a : ℝ in atTop,
      |a * (logDeriv (heckeGammaFactor χ) ((a + 1 / 2 : ℝ) : ℂ)).re -
        (Module.finrank ℚ F : ℝ) * a / 2 * Real.log (a / (2 * Real.pi)) -
          archimedeanCountConstant χ| ≤ B / a := by
  let k (v : InfinitePlace F) : ℝ := if v.IsReal then 1 / 2 else 1
  let b (v : InfinitePlace F) : ℂ := if hv : v.IsReal then
      let p := (realHeckeCharacter_parameters χ v hv).exists.choose
      p.1 + (p.2.val : ℂ)
    else
      let p := (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
      p.1 + (p.2.natAbs : ℂ) / 2
  let c (v : InfinitePlace F) : ℂ := (k v : ℂ) * (1 / 2 + b v)
  have hk (v : InfinitePlace F) : 0 < k v := by dsimp [k]; split_ifs <;> norm_num
  have hdeg : ∑ v : InfinitePlace F, k v = (Module.finrank ℚ F : ℝ) / 2 := by
    calc
      _ = ∑ v : InfinitePlace F, (v.mult : ℝ) / 2 := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v.IsReal <;> simp [k, InfinitePlace.mult, hv]
      _ = _ := by rw [← Finset.sum_div, ← Nat.cast_sum, InfinitePlace.sum_mult_eq]
  have hconst : (∑ v : InfinitePlace F, ((c v).re - 1 / 2)) = archimedeanCountConstant χ := by
    unfold archimedeanCountConstant
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v.IsReal
    · have hp := (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1
      simp only [c, Complex.re_ofReal_mul, Complex.add_re, Complex.div_ofNat_re, Complex.one_re,
        k, ite_eq_left hv, b, dite_eq_left hv, hp, Complex.natCast_re, zero_add]
      ring
    · have hp := (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose_spec.1
      simp only [c, Complex.re_ofReal_mul, Complex.add_re, Complex.div_ofNat_re, Complex.one_re,
        k, ite_eq_right hv, b, dite_eq_right hv, hp, Complex.natCast_re, zero_add]
      ring
  suffices hexp : ∀ a : ℝ, 0 < a →
      (∑ v, k v * (a * ((Complex.digamma (((k v * a : ℝ) : ℂ) + c v)).re -
        Real.log (k v * a)))) =
      a * (logDeriv (heckeGammaFactor χ) ((a + 1 / 2 : ℝ) : ℂ)).re -
        (Module.finrank ℚ F : ℝ) * a / 2 * Real.log (a / (2 * Real.pi)) by
    let M (v : InfinitePlace F) : ℝ :=
      (8 * (3 + (c v).im ^ 2) + 2 * (c v).re ^ 2 + |(c v).re|) / k v
    have hM (v : InfinitePlace F) : 0 < M v := div_pos (by positivity) (hk v)
    have hlocal (v : InfinitePlace F) : ∀ᶠ a : ℝ in atTop,
        |k v * (a * ((Complex.digamma (((k v * a : ℝ) : ℂ) + c v)).re -
          Real.log (k v * a))) - ((c v).re - 1 / 2)| ≤ M v / a := by
      have htop : Tendsto (fun a : ℝ ↦ k v * a) atTop atTop :=
        Tendsto.const_mul_atTop (hk v) tendsto_id
      filter_upwards [htop.eventually_ge_atTop (4 + 2 * |(c v).re|),
        eventually_gt_atTop (0 : ℝ)] with a ha ha0
      have hx := mul_pos (hk v) ha0
      have he (t q : ℝ) : k v * (a * t) - q = (k v * a) * (t - q / (k v * a)) := by
        rw [mul_sub, mul_div_cancel₀ _ hx.ne', mul_assoc]
      rw [he, abs_mul, abs_of_pos hx]
      refine (mul_le_mul_of_nonneg_left (digamma_re_shifted_horizontal_quadratic _ ha) hx.le).trans_eq ?_
      dsimp [M]
      field_simp [(hk v).ne', ha0.ne']
    refine ⟨∑ v, M v, Finset.sum_pos (fun v _ ↦ hM v) Finset.univ_nonempty, ?_⟩
    filter_upwards [eventually_all.mpr hlocal, eventually_gt_atTop (0 : ℝ)] with a hl ha
    rw [← hexp a ha, ← hconst, ← Finset.sum_sub_distrib, Finset.sum_div]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ ↦ hl v)
  intro a ha
  let s : ℂ := (a + 1 / 2 : ℝ)
  have hs : 0 < s.re := by dsimp [s]; positivity
  let D (v : InfinitePlace F) : ℂ := if v.IsReal then (Real.pi : ℂ) else 2 * (Real.pi : ℂ)
  have hlocal (v : InfinitePlace F) :
      k v * (a * ((Complex.digamma (((k v * a : ℝ) : ℂ) + c v)).re - Real.log (k v * a))) =
      a * ((k v : ℂ) * (Complex.digamma ((k v : ℂ) * (s + b v)) - Complex.log (D v))).re -
        k v * a * Real.log (a / (2 * Real.pi)) := by
    have haff : (((k v * a : ℝ) : ℂ) + c v) = (k v : ℂ) * (s + b v) := by
      dsimp only [c, s]
      push_cast
      ring
    have hD : D v = (((2 * Real.pi) * k v : ℝ) : ℂ) := by
      by_cases hv : v.IsReal <;> simp [D, k, hv]
      ring
    rw [haff, hD, Complex.re_ofReal_mul, Complex.sub_re, ← Complex.ofReal_log (by positivity),
      Complex.ofReal_re, Real.log_mul (hk v).ne' ha.ne',
      Real.log_mul (by positivity : 2 * Real.pi ≠ 0) (hk v).ne',
      Real.log_div ha.ne' (by positivity : 2 * Real.pi ≠ 0)]
    ring
  have hG := heckeGammaFactor_logDeriv_eq_sum_digamma χ s hs
  change logDeriv (heckeGammaFactor χ) s =
    ∑ v : InfinitePlace F, (k v : ℂ) * (Complex.digamma ((k v : ℂ) * (s + b v)) - Complex.log (D v)) at hG
  change _ = a * (logDeriv (heckeGammaFactor χ) s).re - _
  simp only [hlocal, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    hdeg, hG, Complex.re_sum]
  ring

/-- On the expanding real line, the coefficient of the leading logarithm is half the
field degree and the finite constant is the sum of the parity and angular corrections. -/
theorem tendsto_mul_re_heckeGamma_logDeriv_sub_main
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    Tendsto (fun a : ℝ ↦ a * (logDeriv (heckeGammaFactor χ) ((a + 1 / 2 : ℝ) : ℂ)).re -
      (Module.finrank ℚ F : ℝ) * a / 2 * Real.log (a / (2 * Real.pi))) atTop
      (𝓝 (archimedeanCountConstant χ)) := by
  obtain ⟨B, _, h⟩ := eventually_abs_mul_re_heckeGamma_logDeriv_sub_main_le χ
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg)
    (by simpa only [Real.dist_eq, id_eq] using h) (tendsto_id.const_div_atTop B)

local notation "U𝔽" => PontryaginDual (IdeleClassGroup (𝓞 F) F)

open Classical in
/-- The conductor and archimedean contribution to the scaled real logarithmic derivative.
The constant two counts the principal poles removed by the symmetric completion. -/
private def gammaCount (χ : U𝔽) (a : ℝ) : ℝ :=
  a * (heckeLogDiscriminantConductor χ / 2 +
    (logDeriv (heckeGammaFactor χ) ((a + 1 / 2 : ℝ) : ℂ)).re) + if χ = 1 then 2 else 0

open Classical in
/-- Elementary first-order approximation, expressed using the field degree, logarithmic conductor,
principal-pole correction, and real parity or complex angular parameters. -/
def elementaryCount (χ : U𝔽) (a : ℝ) : ℝ :=
  (Module.finrank ℚ F : ℝ) * a / 2 * Real.log (a / (2 * Real.pi)) +
    a / 2 * heckeLogDiscriminantConductor χ +
    (if χ = 1 then 2 else 0) + archimedeanCountConstant χ

private theorem eventually_abs_scaled_mass_sub_gamma (χ : U𝔽) :
    ∀ᶠ a : ℝ in atTop, |a * logDerivativeMass χ (a + 1 / 2) 0 - gammaCount χ a| ≤ 2 / a := by
  let E (a : ℝ) : ℝ := (logDeriv (continuedCompletedHeckeL χ) ((a + 1 / 2 : ℝ) : ℂ)).re -
    (logDeriv (heckeGammaFactor χ) ((a + 1 / 2 : ℝ) : ℂ)).re
  have hf : Tendsto (fun a : ℝ ↦ a ^ 2 * E a) atTop (𝓝 0) :=
    tendsto_pow_mul_re_completed_sub_gamma_logDeriv 2 χ
  have hnorm := hf.norm.eventually_lt_const (by norm_num : ‖(0 : ℝ)‖ < 1)
  filter_upwards [hnorm, eventually_gt_atTop (2 : ℝ)] with a h a2
  have ha : 0 < a := by linarith
  have hfin : |a * E a| ≤ 1 / a := by
    apply (le_div_iff₀ ha).mpr
    calc
      |a * E a| * a = |a ^ 2 * E a| := by
        rw [show a ^ 2 * E a = (a * E a) * a by ring]
        simp only [abs_mul, abs_of_pos ha]
      _ ≤ 1 := h.le
  by_cases hχ : χ = 1
  · have hn : 0 < 4 * a ^ 2 - 1 := by nlinarith [sq_nonneg (a-1)]
    have hpex : a * (1 / (a + 1 / 2) + 1 / (a + 1 / 2 - 1)) - 2 = 2 / (4 * a ^ 2 - 1) := by
      let x := a + 1 / 2
      let y := a + 1 / 2 - 1
      let d := 4 * a ^ 2 - 1
      have hx : x ≠ 0 := by dsimp [x]; linarith
      have hy : y ≠ 0 := by dsimp [y]; linarith
      have hd : d ≠ 0 := hn.ne'
      change a * (1 / x + 1 / y) - 2 = 2 / d
      field_simp [hx, hy, hd]
      dsimp only [x, y, d]
      ring
    have hp : |a * (1 / (a + 1 / 2) + 1 / (a + 1 / 2 - 1)) - 2| ≤ 1 / a := by
      rw [hpex, abs_of_pos (div_pos (by norm_num) hn)]
      apply (div_le_div_iff₀ hn ha).mpr
      nlinarith [sq_nonneg (a - 1)]
    have hrs :
        (1 / ((a + 1 / 2 : ℝ) : ℂ) + 1 / (((a + 1 / 2 : ℝ) : ℂ) - 1)).re =
          1 / (a + 1 / 2) + 1 / (a + 1 / 2 - 1) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div,
        ← Complex.ofReal_div, ← Complex.ofReal_add, Complex.ofReal_re]
    calc
      _ = |a * E a + (a * (1 / (a + 1 / 2) + 1 / (a + 1 / 2 - 1)) - 2)| := by
        simp only [logDerivativeMass, gammaCount, hχ, ite_true, Complex.ofReal_zero, zero_mul,
          add_zero, Complex.add_re, E]
        congr 1
        simp only [Complex.add_re] at hrs
        rw [← hrs]
        ring
      _ ≤ _ := (abs_add_le _ _).trans ((add_le_add hfin hp).trans_eq (by ring))
  · calc
      _ = |a * E a| := by
        simp only [logDerivativeMass, gammaCount, hχ, ite_false, Complex.ofReal_zero,
          zero_mul, add_zero, E]
        congr 1
        ring
      _ ≤ 1 / a := hfin
      _ ≤ 2 / a := div_le_div_of_nonneg_right (by norm_num) ha.le

/-- At expanding widths the scaled actual logarithmic derivative differs from the elementary
expression by at most a character-dependent constant divided by the width. -/
theorem eventually_abs_logDerivativeMass_sub_elementary_le (χ : U𝔽) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ a : ℝ in atTop,
      |a * logDerivativeMass χ (a + 1 / 2) 0 - elementaryCount χ a| ≤ B / a := by
  obtain ⟨B, hB, harch⟩ := eventually_abs_mul_re_heckeGamma_logDeriv_sub_main_le χ
  refine ⟨2 + B, by linarith, ?_⟩
  filter_upwards [eventually_abs_scaled_mass_sub_gamma χ, harch] with a hf hg
  have hgamma : |gammaCount χ a - elementaryCount χ a| ≤ B / a := by
    convert hg using 2
    dsimp only [gammaCount, elementaryCount]
    ring
  calc
    _ = |(a * logDerivativeMass χ (a + 1 / 2) 0 - gammaCount χ a) +
        (gammaCount χ a - elementaryCount χ a)| := by rw [sub_add_sub_cancel]
    _ ≤ _ := (abs_add_le _ _).trans ((add_le_add hf hgamma).trans_eq (add_div _ _ _).symm)

set_option quotPrecheck false

local notation "RealMass(" χ ")" =>
  ∀ᶠ a : ℝ in atTop, HasSum (fun z : Site χ ↦ (multiplicity z : ℝ) *
    poissonWeight (a + 1 / 2) 0 z.val) (logDerivativeMass χ (a + 1 / 2) 0)

/-- The elementary first-order expression differs from the scaled pole-cleared completed
logarithmic derivative by a quantity tending to zero. -/
theorem tendsto_logDerivativeMass_sub_elementary (χ : U𝔽) :
    Tendsto (fun a : ℝ ↦ a * logDerivativeMass χ (a + 1 / 2) 0 - elementaryCount χ a)
      atTop (𝓝 0) := by
  obtain ⟨B, _, h⟩ := eventually_abs_logDerivativeMass_sub_elementary_le χ
  have hB : Tendsto (fun a : ℝ ↦ B / a) atTop (𝓝 0) := tendsto_id.const_div_atTop B
  exact squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using h) hB

/-- An ordinate-zero logarithmic-derivative identity on a tail suffices to remove the
unknown complete-zero mass from the arithmetic approximation. -/
theorem tendsto_elementary_sub_zeroPoissonMass (χ : U𝔽) (h : RealMass(χ)) :
    Tendsto (fun a : ℝ ↦ elementaryCount χ a - a * zeroPoissonMass χ a) atTop (𝓝 0) := by
  have ht := (tendsto_logDerivativeMass_sub_elementary χ).neg
  rw [neg_zero] at ht
  apply ht.congr'
  filter_upwards [h] with a ha
  have he : zeroPoissonMass χ a = logDerivativeMass χ (a + 1 / 2) 0 := ha.tsum_eq
  rw [he]
  ring

/-- The elementary expression minus the true soft count of line zeros recovers the exact
off-line multiplicity in the extended nonnegative reals. -/
theorem tendsto_elementary_deficit (χ : U𝔽) (h : RealMass(χ)) :
    Tendsto (fun a ↦ ENNReal.ofReal (elementaryCount χ a - centralSoftCount χ a))
      atTop (𝓝 (offLineCount χ)) :=
  tendsto_approximate_deficit χ _ (tendsto_elementary_sub_zeroPoissonMass χ h)

/-- A fixed strict margin below two at unbounded widths in the elementary deficit
characterizes the critical-line assertion for the chosen character. -/
theorem criticalLine_iff_cofinal_elementaryCount (χ : U𝔽) (h : RealMass(χ)) :
    (∀ z : Site χ, z.val.re = 1 / 2) ↔ ∃ B : ℝ, B < 2 ∧
      ∃ᶠ a in atTop, elementaryCount χ a - centralSoftCount χ a ≤ B :=
  criticalLine_iff_cofinal_approximation χ _ (tendsto_elementary_sub_zeroPoissonMass χ h)

/-- A single sequence tending to infinity suffices when the elementary deficit is below
the fixed threshold infinitely often along that sequence. -/
theorem criticalLine_of_elementaryCount_sequence {χ : U𝔽} (h : RealMass(χ))
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) {B : ℝ} (hB : B < 2)
    (hc : ∃ᶠ n in atTop, elementaryCount χ (a n) - centralSoftCount χ (a n) ≤ B) :
    ∀ z : Site χ, z.val.re = 1 / 2 :=
  (criticalLine_iff_cofinal_elementaryCount χ h).mpr ⟨B, hB, ha.frequently hc⟩

open MeasureTheory
open scoped NNReal NumberField.AdeleRing

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

/-- Paper: Theorem 12.5.1.1, pp. 519–520.
Reconstruction: Given the real-axis Poisson identity for each section-normalized
character, exterior-zero cancellation at every positive strip width is equivalent to
arbitrarily large real widths where the elementary deficit has a fixed margin below two. -/
theorem exteriorCancellation_iff_cofinal_elementaryCount
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 F) F) (hτ : Function.RightInverse τ (ideleClassNorm F))
    (h : ∀ χ : U𝔽, (∀ t, χ (τ t) = 1) → RealMass(χ)) :
    (∀ α : ℝ, 0 < α → ∀ φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F),
      (∀ g : (ideleClassNorm F).ker, φ.val g = 0) →
        HasSum (fun p : {p : {χ : U𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
          0 < MeromorphicOn.divisor (continuedCompletedHeckeL p.1.val) Set.univ p.2 ∧
          α ≤ |p.2.re - 1 / 2|} ↦
          (MeromorphicOn.divisor (continuedCompletedHeckeL p.val.1.val) Set.univ p.val.2 : ℂ) *
            ∫ g, φ.val g * ideleClassNormTwist p.val.1.val (p.val.2 - 1 / 2) g
              ∂ideleClassTamagawaMeasure F) 0) ↔
    ∀ χ : U𝔽, (∀ t, χ (τ t) = 1) → ∃ B : ℝ, B < 2 ∧
      ∃ᶠ a in atTop, elementaryCount χ a - centralSoftCount χ a ≤ B :=
  exteriorCancellation_iff_cofinal_approximation τ hτ elementaryCount
    fun χ hχ ↦ tendsto_elementary_sub_zeroPoissonMass χ (h χ hχ)

end RiemannMasullo.HeckePoisson
