module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5_SignedHeightCutoff
import RiemannMasullo.Ch10_TraceSpectral.Sec2_Basepoint
import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import RiemannMasullo.AppD_SchwartzBruhat.Sec3b
import RiemannMasullo.Ch03_IdelicZeta.Sec1

/-! # Signed trace bounds for physical translates

The logarithmic zero-free region and every height moment of a compact test
control translates at a fixed thin width. The two ends of the norm use the
region for each active character and its inverse.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b
  instSIdeleLocallyCompactSec1 instSIdeleT2Sec4

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" ψ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) ψ) z
local notation "Sites(" χ ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  0 < order(χ z.1, shift(1 / 2 + z.2.1, z.2.2))}
local notation "mult(" χ ", " z ")" =>
  (order(χ (z).val.1, shift(1 / 2 + (z).val.2.1, (z).val.2.2))).untop₀.toNat
local notation "sample(" φ ", " χ ", " z ")" => modulatedFourierMellin m𝔽 univ
  ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽
  (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist (χ (z).val.1)
    (shift((z).val.2.1, (z).val.2.2)))

local notation "FM(" φ ", " ψ ", " w ")" => modulatedFourierMellin m𝔽 univ
  ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽
  (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist (F := F) ψ w)
local notation "wide(" φ ")" => halfTwistStripTrace (F := F) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  (by norm_num : (1 : ℝ) < 3) φ
local notation "omitted(" a ", " s ", " φ ", " χ ", " z ")" =>
  (((mult(χ, z) - spectralStripMultiplicity a s (z).val.2.1 (mult(χ, z)) : ℕ) : ℂ) * sample(φ, χ, z))

/-- Completing the square converts logarithmic clearance from the edge into
a uniform exponential estimate along log-norm translations. -/
private theorem exp_translate_bound {A B : ℝ} (hA : 0 < A) (hB : 1 ≤ B) (c : ℝ) :
    ∃ (n : ℕ) (K : ℝ), 0 ≤ K ∧ ∀ (t u b : ℝ), 0 ≤ t → 0 ≤ u →
      b ≤ 1 / 2 - A / Real.log (B * (t + 3)) →
      Real.exp (b * u) ≤ K * (1 + t ^ n) * Real.exp (u / 2 - c * Real.sqrt u) := by
  let n := ⌈c ^ 2 / (4 * A)⌉₊
  refine ⟨n, (4 * B) ^ n, by positivity, ?_⟩
  intro t u b ht hu hb
  let L := Real.log (B * (t + 3))
  have hprod : 1 < B * (t + 3) := by nlinarith [mul_nonneg (sub_nonneg.mpr hB) ht]
  have hL : 0 < L := Real.log_pos hprod
  have hc : c * Real.sqrt u ≤ A / L * u + c ^ 2 / (4 * A) * L := by
    rw [← Real.sq_sqrt hu]
    rw [Real.sqrt_sq (Real.sqrt_nonneg _)]
    field_simp
    nlinarith only [sq_nonneg (2 * A * Real.sqrt u - c * L)]
  have hN : c ^ 2 / (4 * A) ≤ (n : ℝ) := Nat.le_ceil _
  have hb' : b * u ≤ (1 / 2 - A / L) * u := mul_le_mul_of_nonneg_right hb hu
  have hlog : b * u ≤ (n : ℝ) * L + (u / 2 - c * Real.sqrt u) := by
    linarith [mul_le_mul_of_nonneg_right hN hL.le]
  have hpow : (B * (t + 3)) ^ n ≤ (4 * B) ^ n * (1 + t ^ n) := by
    rcases le_total t 1 with he | he
    · have h := pow_le_pow_left₀ (by positivity : 0 ≤ B * (t + 3))
        (by nlinarith [mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ B)] : B * (t + 3) ≤ 4 * B) n
      exact h.trans (le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg ht n]))
    · have h := pow_le_pow_left₀ (by positivity : 0 ≤ B * (t + 3))
        (by nlinarith [mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ B)] : B * (t + 3) ≤ (4 * B) * t) n
      rw [mul_pow (4 * B) t] at h
      exact h.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  calc
    Real.exp (b * u) ≤ Real.exp ((n : ℝ) * L + (u / 2 - c * Real.sqrt u)) := Real.exp_le_exp.mpr hlog
    _ = (B * (t + 3)) ^ n * Real.exp (u / 2 - c * Real.sqrt u) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans hprod)]
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le

/-- A physical left translate on the idele classes. Compact support is transported
by the homeomorphism, and the translated Schwartz–Bruhat function is smooth. -/
def ideleClassBruhatTranslate (g : C𝔽) (φ : BruhatCompactSupport C𝔽) : BruhatCompactSupport C𝔽 := by
  have hφ : φ.val ∈ schwartzBruhatSubmodule C𝔽 := by
    obtain ⟨m, _, hm, hms⟩ := exists_ideleClassModulation F
    have hd := bruhatCompactSupport_le_modulatedExponentialDecay m {0} hm hms φ.property
    rwa [modulatedExponentialDecaySubmodule_singleton_zero] at hd
  let f : SchwartzBruhat C𝔽 := ⟨φ.val, hφ⟩
  exact ⟨fun x ↦ φ.val (g⁻¹ * x),
    (mem_bruhatSmoothSubmodule_iff _).mpr (schwartzBruhat_isBruhatSmooth (schwartzBruhatTranslate g f)),
    (show HasCompactSupport φ.val from φ.property.2).comp_homeomorph (Homeomorph.mulLeft g⁻¹)⟩

/-- Evaluation of the translated test on the physical idele class group. -/
@[simp] theorem ideleClassBruhatTranslate_apply (g : C𝔽) (φ : BruhatCompactSupport C𝔽) (x : C𝔽) :
    (ideleClassBruhatTranslate g φ).val x = φ.val (g⁻¹ * x) := rfl

local notation "logNorm(" g ")" => Real.log (((ideleClassNorm F g).val : ℝ))
local notation "Tφ(" g ", " φ ")" => ideleClassBruhatTranslate (F := F) g φ

private theorem norm_mellin_translate (g : C𝔽) (φ : BruhatCompactSupport C𝔽)
    (ψ : PontryaginDual C𝔽) (w : ℂ) :
    ‖FM(Tφ(g, φ), ψ, w)‖ = Real.exp (w.re * logNorm(g)) * ‖FM(φ, ψ, w)‖ := by
  let c := ideleClassNormTwist (F := F) ψ w
  have ht : FM(Tφ(g, φ), ψ, w) = c g * FM(φ, ψ, w) := by
    simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
    rw [← integral_mul_left_eq_self (μ := μ𝔽) (fun x ↦ (Tφ(g, φ)).val x * c x) g, ← integral_const_mul]
    exact integral_congr_ae (.of_forall fun x ↦ by
      change φ.val (g⁻¹ * (g * x)) * c (g * x) = c g * (φ.val x * c x)
      rw [inv_mul_cancel_left, map_mul]; ring)
  rw [ht, norm_mul]
  congr 1
  change ‖(ψ g : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ w‖ = _
  have hp := NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))
  rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp,
    Real.rpow_def_of_pos hp, mul_comm]

/-- Paper: §12.3, p. 514. For a test with finitely many active angular rows,
the signed full-minus-narrow trace of every physical translate grows at most
as exp(|y|/2 − c√|y|), for every c, where y is the log norm of the translation.
The constant is uniform in the translating class, strip width and Sobolev order. -/
theorem finite_rows_translated_stripTrace_bound (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (hn : ∀ ω t, χ ω (τ t) = 1) (φ : BruhatCompactSupport C𝔽)
    (Ω : Finset (PontryaginDual C𝔽)) (hΩ : ∀ z : Sites(χ), sample(φ, χ, z) ≠ 0 → χ z.val.1 ∈ Ω)
    (c : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (g : C𝔽) {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s),
      ‖wide(Tφ(g, φ)) - halfTwistStripTrace (F := F) ha hs Tφ(g, φ)‖ ≤
        L * Real.exp (|logNorm(g)| / 2 - c * Real.sqrt |logNorm(g)|) := by
  obtain ⟨A, hA, B, hB, hZ⟩ := finite_hecke_rows_zeroFreeWidth χ Ω
  obtain ⟨n, K, hK, hpow⟩ := exp_translate_bound hA hB c
  let v (z : Sites(χ)) := (mult(χ, z) : ℝ) * ‖sample(φ, χ, z)‖
  let M (z : Sites(χ)) := (1 + |z.val.2.2| ^ n) * v z
  have hv : Summable v := by simpa only [pow_zero, one_mul] using summable_stripTrace_height_moments τ hτ χ hχ hn φ 0
  have hM : Summable M := by
    simpa only [M, add_mul, one_mul] using hv.add (summable_stripTrace_height_moments τ hτ χ hχ hn φ n)
  have hM₀ (z : Sites(χ)) : 0 ≤ M z := by dsimp [M, v]; positivity
  refine ⟨K * ∑' z, M z, mul_nonneg hK (tsum_nonneg hM₀), ?_⟩
  intro g a s ha hs
  let y := logNorm(g)
  let E := Real.exp (|y| / 2 - c * Real.sqrt |y|)
  let f (z : Sites(χ)) := omitted(a, s, Tφ(g, φ), χ, z)
  have hb (z : Sites(χ)) : ‖f z‖ ≤ K * E * M z := by
    change ‖(_ : ℂ) * FM(Tφ(g, φ), χ z.val.1, shift(z.val.2.1, z.val.2.2))‖ ≤ _
    rw [norm_mul, Complex.norm_natCast, norm_mellin_translate]
    rw [show (shift(z.val.2.1, z.val.2.2)).re = z.val.2.1 by simp]
    by_cases hz : sample(φ, χ, z) = 0
    · rw [hz, norm_zero, mul_zero, mul_zero]
      exact mul_nonneg (mul_nonneg hK (Real.exp_pos _).le) (hM₀ _)
    · have hzero := hZ _ (abs_nonneg _) z (hΩ z hz) (le_refl _)
      have hexp : Real.exp (z.val.2.1 * y) ≤ K * (1 + |z.val.2.2| ^ n) * E :=
        (Real.exp_le_exp.mpr ((le_abs_self _).trans_eq (abs_mul z.val.2.1 y))).trans
          (hpow _ _ _ (abs_nonneg _) (abs_nonneg _) hzero.le)
      have hmult : ((mult(χ, z) - spectralStripMultiplicity a s z.val.2.1 (mult(χ, z)) : ℕ) : ℝ) ≤ mult(χ, z) :=
        by exact_mod_cast (Nat.sub_le (mult(χ, z)) _)
      calc
        _ ≤ (mult(χ, z) : ℝ) * ((K * (1 + |z.val.2.2| ^ n) * E) * ‖sample(φ, χ, z)‖) :=
          mul_le_mul hmult (mul_le_mul_of_nonneg_right hexp (norm_nonneg _))
            (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (Nat.cast_nonneg _)
        _ = _ := by dsimp [M, v]; ring
  have h := hasSum_halfTwistStripTrace_defect χ hχ Tφ(g, φ) ha hs
  rw [← h.tsum_eq]
  calc
    ‖∑' z, f z‖ ≤ ∑' z, ‖f z‖ := norm_tsum_le_tsum_norm h.summable.norm
    _ ≤ ∑' z, K * E * M z := h.summable.norm.tsum_le_tsum hb (hM.mul_left _)
    _ = _ := by rw [tsum_mul_left]; ring

private theorem normOne_mode_support (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice χ) (ω : PontryaginDual C₁) (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ (k : C₁) x, φ.val (k.val * x) = ((ω k : Circle) : ℂ)⁻¹ * φ.val x) :
    ∀ z : Sites(χ), sample(φ, χ, z) ≠ 0 → χ z.val.1 ∈ ({χ ω} : Finset _) := by
  classical
  intro z hz
  suffices h : z.val.1 = ω by simp [h]
  apply PontryaginDual.ext
  intro k
  let ψ := χ z.val.1
  let w := shift(z.val.2.1, z.val.2.2)
  let q := ideleClassNormTwist (F := F) ψ w
  let f (x : C𝔽) := φ.val x * q x
  have hne : (∫ x, f x ∂μ𝔽) ≠ 0 := by
    simpa only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ] using hz
  have hq : q k.val = (ψ k.val : ℂ) := by
    change (ψ k.val : ℂ) * (((ideleClassNorm F k.val).val : ℝ) : ℂ) ^ w = _
    rw [MonoidHom.mem_ker.mp k.property]
    simp
  have he (x : C𝔽) : f (k.val * x) = (((ω k : Circle) : ℂ)⁻¹ * (ψ k.val : ℂ)) * f x := by
    dsimp only [f]
    rw [hφ, map_mul, hq]; ring
  have h := integral_mul_left_eq_self (μ := μ𝔽) f k.val
  simp_rw [he, integral_const_mul] at h
  have h1 := (mul_eq_right₀ hne).mp h
  have hval : (ψ k.val : ℂ) = (ω k : ℂ) := ((inv_mul_eq_one₀ (Circle.coe_ne_zero (ω k))).mp h1).symm
  have hres := congrArg (fun η : PontryaginDual C₁ ↦ η k) (hχ z.val.1)
  exact hres.symm.trans (Circle.ext hval)

local notation "translatedBound(" k ", " φ ", " S₀ ", " c ")" =>
  ∃ K : ℝ, 0 ≤ K ∧ ∀ g : IdeleClassGroup (𝓞 k) k,
    ∃ (S : Finset (HeightOneSpectrum (𝓞 k))) (f : BruhatCompactSupport (SAdeleRing k S)ˣ), S₀ ⊆ S ∧
      (∀ x : (SAdeleRing k S)ˣ, HasSum (fun ξ : sProjectedDiagonal k S ↦ f.val (ξ.val * x))
        ((ideleClassBruhatTranslate g φ).val (QuotientGroup.mk (sIdeleInsertion k S x)))) ∧
      ∀ᶠ R : ℝ in atTop, ∀ {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s),
        ‖-correctedSLocalTraceSharpMass (ideleClassBruhatTranslate g φ) f R -
          halfTwistStripTrace (F := k) ha hs (ideleClassBruhatTranslate g φ)‖ ≤
          let y := |Real.log (((ideleClassNorm k g).val : ℝ))|
          K * Real.exp (y / 2 - c * Real.sqrt y)

/-- A single finite set and lift for each translate work at every width and
order. The global growth estimate then holds for the actual signed comparison
at all sufficiently large finite local cutoffs. -/
private theorem translated_bound_to_sharpMass (φ : BruhatCompactSupport C𝔽) (S₀ : Finset V) (c L : ℝ)
    (hL : 0 ≤ L) (hb : ∀ (g : C𝔽) {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s),
      ‖wide(Tφ(g, φ)) - halfTwistStripTrace (F := F) ha hs Tφ(g, φ)‖ ≤
        L * Real.exp (|logNorm(g)| / 2 - c * Real.sqrt |logNorm(g)|)) :
    translatedBound(F, φ, S₀, c) := by
  refine ⟨1 + L, by linarith, fun g ↦ ?_⟩
  obtain ⟨S, f, hS, hf, hlim⟩ := exists_correctedSharpMass_tendsto_fullTrace Tφ(g, φ) S₀
  refine ⟨S, f, hS, hf, ?_⟩
  let E := Real.exp (|logNorm(g)| / 2 - c * Real.sqrt |logNorm(g)|)
  filter_upwards [Metric.tendsto_nhds.mp hlim E (Real.exp_pos _)] with R hR
  intro a s ha hs
  rw [dist_eq_norm] at hR
  have h := (norm_add_le _ _).trans (add_le_add hR.le (hb g ha hs))
  rw [add_mul, one_mul]
  simpa only [sub_add_sub_cancel] using h

/-- Paper: §12.3, p. 514, and the translated tests on pp. 519–520. For each
angular mode over any number field the signed sharp-local comparison satisfies
the two-sided translated estimate at arbitrary fixed or varying thin widths. -/
theorem mode_translated_sharpMass_stripTrace_bound (φ : BruhatCompactSupport C𝔽)
    (ω : PontryaginDual C₁) (hφ : ∀ (k : C₁) x, φ.val (k.val * x) = ((ω k : Circle) : ℂ)⁻¹ * φ.val x)
    (S₀ : Finset V) (c : ℝ) :
    translatedBound(F, φ, S₀, c) := by
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ := q.comp ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : RightInverse τ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  obtain ⟨χ, hχ, hn, -⟩ := exists_spectralBasepointChoice_of_normSection τ hτ
  obtain ⟨L, hL, hb⟩ := finite_rows_translated_stripTrace_bound τ hτ χ hχ hn φ {χ ω}
    (normOne_mode_support χ hχ ω φ hφ) c
  exact translated_bound_to_sharpMass φ S₀ c L hL hb

/-- Paper: §12.3, p. 514. Over the rationals every compact Bruhat test has the
translated subexponential saving simultaneously for all strip widths and orders.
The constant is independent of the translating class at both ends of the norm. -/
theorem rat_translated_sharpMass_stripTrace_bound (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 ℚ) ℚ))
    (S₀ : Finset (HeightOneSpectrum (𝓞 ℚ))) (c : ℝ) :
    translatedBound(ℚ, φ, S₀, c) := by
  let q : IdeleGroup (𝓞 ℚ) ℚ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ := q.comp ⟨canonicalIdeleNormSection ℚ, canonicalIdeleNormSection_continuous ℚ⟩
  have hτ : RightInverse τ (ideleClassNorm ℚ) := canonicalIdeleNormSection_rightInverse ℚ
  obtain ⟨χ, hχ, hn, -⟩ := exists_spectralBasepointChoice_of_normSection τ hτ
  obtain ⟨Ω, hΩ⟩ := rat_finite_mellin_rows τ hτ φ
  obtain ⟨L, hL, hb⟩ := finite_rows_translated_stripTrace_bound τ hτ χ hχ hn φ Ω
    (fun z hz ↦ hΩ _ (hn _) _ (by
      simpa only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ] using hz)) c
  exact translated_bound_to_sharpMass φ S₀ c L hL hb

end RiemannMasullo
