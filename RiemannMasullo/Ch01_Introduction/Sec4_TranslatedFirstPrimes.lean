module

public import RiemannMasullo.Ch01_Introduction.Sec4
import Mathlib.RingTheory.Ideal.Int
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import RiemannMasullo.Ch12_TraceGeometric.Sec5

/-! # Translated first-prime sums and the geometric explicit formula

Positive logarithmic support separates the Chapter 12 signed local terms into the two polar
moments, the actual archimedean principal values, and the finite-place prime-power atoms.
At rational-prime norms the only atoms are first powers in residue degree one.
-/

@[expose] public noncomputable section
open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology ContDiff

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instNormOneIdeleClassMeasurableSec4b

namespace FirstPrimeArch

/-- The positive norm branch in the log-norm coordinate `x`. -/
def translatedDensity (k : ℝ) (z : ℂ) (H : ℝ → ℂ) (y x : ℝ) : ℂ :=
  H (x - y) * Complex.exp (-z * ((x / k : ℝ) : ℂ)) /
    (1 - (Real.exp (-(x / k)) : ℂ))

/-- On a positive translated window, the principal-value gamma integral is an ordinary
integral over that window. The variable change is `x = k t`. -/
private theorem digamma_window {k u v y : ℝ} (hk : 0 < k) (hu : 0 < u) (hy : 0 ≤ y)
    (z z' : ℂ) (H : ℝ → ℂ) (hs : ∀ x, x ∉ Icc u v → H x = 0) :
    -(∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel k z z' (fun s ↦ H (s - y)) t) =
      ∫ x in Icc (y + u) (y + v), translatedDensity k z H y x := by
  have hz : H (-y) = 0 := hs _ (fun h ↦ by linarith [h.1])
  have hterm (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      -heckeArchimedeanDigammaKernel k z z' (fun s ↦ H (s - y)) t =
        k • translatedDensity k z H y (k * t) := by
    have hneg : H (-(k * t) - y) = 0 := hs _ (fun h ↦ by linarith [h.1, mul_pos hk ht])
    have hdiv : k * t / k = t := by field_simp
    simp [heckeArchimedeanDigammaKernel, translatedDensity, hz, hneg, hdiv, Complex.real_smul]
  calc
    _ = ∫ t in Ioi (0 : ℝ), k • translatedDensity k z H y (k * t) := by
      rw [← integral_neg]
      exact setIntegral_congr_fun measurableSet_Ioi hterm
    _ = ∫ x in Ioi (0 : ℝ), translatedDensity k z H y x := by
      rw [integral_smul, integral_comp_mul_left_Ioi' _ _ hk, mul_zero]
    _ = _ := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (t := Ioi (0 : ℝ))
        (s := Icc (y + u) (y + v)) measurableSet_Ioi
        (fun x (hx : x ∈ Icc (y + u) (y + v)) ↦
          (add_pos_of_nonneg_of_pos hy hu).trans_le hx.1)
      intro x hx
      have hmiss : x - y ∉ Icc u v := fun h ↦ hx.2 ⟨by linarith [h.1], by linarith [h.2]⟩
      simp [translatedDensity, hs _ hmiss]

/-- A translated local factor of decay order at least `r` is bounded explicitly by
the length of the log-support times its pointwise supremum. -/
private theorem norm_window {k u v y r B : ℝ} (hk : 0 < k) (hu : 0 < u) (huv : u ≤ v)
    (hy : 0 ≤ y) (hr : 0 ≤ r) (hB : 0 ≤ B) (z : ℂ) (hz : k * r ≤ z.re)
    (H : ℝ → ℂ) (hH : ∀ x ∈ Icc u v, ‖H x‖ ≤ B) :
    ‖∫ x in Icc (y + u) (y + v), translatedDensity k z H y x‖ ≤
      (v - u) * B * Real.exp (-(r * u)) / (1 - Real.exp (-(u / k))) * Real.exp (-(r * y)) := by
  let C := B * Real.exp (-(r * (y + u))) / (1 - Real.exp (-(u / k)))
  have hden : 0 < 1 - Real.exp (-(u / k)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos (div_pos hu hk)))
  have hpt (x : ℝ) (hx : x ∈ Icc (y + u) (y + v)) : ‖translatedDensity k z H y x‖ ≤ C := by
    have hxu : u ≤ x := by linarith [hx.1]
    have hrx : 0 ≤ x / k := div_nonneg (hu.le.trans hxu) hk.le
    have hn : 1 - Real.exp (-(u / k)) ≤ 1 - Real.exp (-(x / k)) :=
      sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg (div_le_div_of_nonneg_right hxu hk.le))) _
    have he : r * (y + u) ≤ z.re * (x / k) := calc
      _ ≤ r * x := mul_le_mul_of_nonneg_left hx.1 hr
      _ = (k * r) * (x / k) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hz hrx
    have hl : ‖H (x - y)‖ ≤ B := hH _ ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [translatedDensity, norm_div, norm_mul, Complex.norm_exp,
      show (1 - (Real.exp (-(x / k)) : ℂ)) = ((1 - Real.exp (-(x / k)) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_of_nonneg (hden.le.trans hn)]
    apply div_le_div₀ (mul_nonneg hB (Real.exp_pos _).le) _ hden hn
    apply mul_le_mul hl _ (Real.exp_pos _).le hB
    apply Real.exp_le_exp.mpr
    simpa [Complex.mul_re] using neg_le_neg he
  have hbound := norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Icc_lt_top hpt
  rw [Real.volume_real_Icc_of_le (by linarith : y + u ≤ y + v)] at hbound
  apply hbound.trans_eq
  dsimp [C]
  rw [show -(r * (y + u)) = -(r * u) + -(r * y) by ring, Real.exp_add]
  ring

variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "arch(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w

open Classical in
/-- Positive gamma parameter and scale in the log-norm variable. -/
def positiveParameter (χ : PontryaginDual C𝔽) (w : InfinitePlace F) : ℝ × ℂ :=
  if hw : w.IsReal then
    let p := (realHeckeCharacter_parameters χ w hw).exists.choose
    (1/2, (1/2 + p.1 + p.2.val)/2)
  else
    let p := (complexHeckeCharacter_parameters χ w (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
    (1, 1/2 + p.1 + (p.2.natAbs : ℂ)/2)

/-- The minimum radial decay rate is one half at each archimedean place. -/
private theorem positiveParameter_rate (χ : PontryaginDual C𝔽) (w : InfinitePlace F) :
    0 < (positiveParameter χ w).1 ∧ (positiveParameter χ w).1 / 2 ≤ (positiveParameter χ w).2.re := by
  classical
  by_cases hr : w.IsReal
  · let p := (realHeckeCharacter_parameters χ w hr).exists.choose
    have hp : p.1.re = 0 := (realHeckeCharacter_parameters χ w hr).exists.choose_spec.1
    rw [positiveParameter, dite_eq_left hr]
    change 0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) / 2 ≤ ((1 / 2 + p.1 + p.2.val) / 2 : ℂ).re
    simp [Complex.div_ofNat_re, hp]
    linarith [Nat.cast_nonneg (α := ℝ) p.2.val]
  · let hw := InfinitePlace.not_isReal_iff_isComplex.mp hr
    let p := (complexHeckeCharacter_parameters χ w hw).exists.choose
    have hp : p.1.re = 0 := (complexHeckeCharacter_parameters χ w hw).exists.choose_spec.1
    rw [positiveParameter, dite_eq_right hr]
    change 0 < (1 : ℝ) ∧ 1 / 2 ≤ (1 / 2 + p.1 + (p.2.natAbs : ℂ) / 2 : ℂ).re
    simp [Complex.div_ofNat_re, hp]
    positivity

/-- On the actual Chapter 12 translated test, the archimedean principal value is an
ordinary integral on the translated support with the gamma parameter of `ψ⁻¹`. -/
theorem translated_principalValue (w : InfinitePlace F) (ψ : PontryaginDual C𝔽)
    (H : ℝ → ℂ) (hH : Measurable H) {u v y : ℝ} (hu : 0 < u) (hy : 0 ≤ y)
    (hs : ∀ x, x ∉ Icc u v → H x = 0) (test : BruhatCompactSupport w.Completionˣ)
    (htest : ∀ x, test.val x = (ψ (arch(w) x) : ℂ) *
      H (Real.log ((ideleClassNorm F (arch(w) x)).val : ℝ) - y)) :
    let q := positiveParameter ψ⁻¹ w
    infiniteConnesWeilPrincipalValue w test =
      ∫ x in Icc (y + u) (y + v), translatedDensity q.1 q.2 H y x := by
  classical
  let f : ℝ → ℂ := (Ioi 1).indicator (fun r ↦ H (Real.log r - y))
  have hf : Measurable f := (hH.comp (Real.measurable_log.sub measurable_const)).indicator measurableSet_Ioi
  have hf₀ (r : ℝ) (hr : r ≤ 1) : f r = 0 := indicator_of_notMem (not_lt.mpr hr) _
  have hfpos (r : ℝ) (hr : 0 < r) : f r = H (Real.log r - y) := by
    by_cases h : 1 < r
    · exact indicator_of_mem h _
    · rw [hf₀ r (le_of_not_gt h), hs _ (fun h' ↦ by linarith [h'.1, Real.log_nonpos hr.le (le_of_not_gt h)])]
  have hχ (g : C𝔽) : star (((ψ⁻¹) g : Circle) : ℂ) = (ψ g : ℂ) := by
    change star (((ψ g)⁻¹ : Circle) : ℂ) = _
    rw [Circle.coe_inv_eq_conj]
    exact star_star _
  have hlocal (t : w.Completionˣ) : test.val t = introTraceTest ψ⁻¹ f (arch(w) t) := by
    rw [htest, introTraceTest, hχ, hfpos _ (NNReal.coe_pos.mpr (Units.zero_lt _))]
  have hf1 : test.val 1 = 0 := by simp [hlocal, introTraceTest, hf₀ 1 le_rfl]
  let K := fun t : w.Completionˣ ↦
    introTraceTest ψ⁻¹ f (arch(w) t) * (Real.sqrt (‖t.val‖ ^ w.mult) : ℂ) /
      ((‖1 - t.val‖ ^ w.mult : ℝ) : ℂ)
  have hmatch : Integrable K (infiniteLocalMultiplicativeTamagawaMeasure F w) ∧
      introTraceArchimedean ψ⁻¹ f w = infiniteConnesWeilPrincipalValue w test := by
    obtain ⟨hi, hv⟩ := infiniteConnesWeilPrincipalValue_of_apply_one_zero w test hf1
    exact ⟨by simpa only [K, hlocal] using hi,
      by simpa only [introTraceArchimedean, hlocal] using hv.symm⟩
  have he := introTraceArchimedean_eq_neg_digamma_of_supported_above_one ψ⁻¹ w f hf hf₀ hmatch.1
  have hlog (r : ℝ) : f (Real.exp r) = H (r - y) := by rw [hfpos _ (Real.exp_pos _), Real.log_exp]
  simp_rw [hlog] at he
  rw [← hmatch.2, he]
  by_cases hw : w.IsReal
  · simp only [positiveParameter, dite_eq_left hw]
    exact digamma_window (by norm_num) hu hy _ _ H hs
  · simp only [positiveParameter, dite_eq_right hw]
    exact digamma_window zero_lt_one hu hy _ _ H hs

/-- Actual principal values decay with the square root of the inverse norm of
translation, uniformly over all translations `y ≥ 0` and allowable local tests. -/
theorem translated_principalValue_bound (w : InfinitePlace F) (ψ : PontryaginDual C𝔽)
    (H : ℝ → ℂ) (hH : Measurable H) {u v B : ℝ} (hu : 0 < u) (huv : u ≤ v)
    (hB : 0 ≤ B) (hbound : ∀ x ∈ Icc u v, ‖H x‖ ≤ B) (hs : ∀ x, x ∉ Icc u v → H x = 0)
    {y : ℝ} (hy : 0 ≤ y) (test : BruhatCompactSupport w.Completionˣ)
    (htest : ∀ x, test.val x = (ψ (arch(w) x) : ℂ) *
      H (Real.log ((ideleClassNorm F (arch(w) x)).val : ℝ) - y)) :
    let k := (positiveParameter ψ⁻¹ w).1
    ‖infiniteConnesWeilPrincipalValue w test‖ ≤
      (v - u) * B * Real.exp (-(u/2)) / (1 - Real.exp (-(u/k))) * Real.exp (-(y/2)) := by
  let q := positiveParameter ψ⁻¹ w
  have hq := positiveParameter_rate ψ⁻¹ w
  rw [translated_principalValue w ψ H hH hu hy hs test htest]
  simpa only [one_div, mul_inv_cancel_left₀, mul_comm (2:ℝ)⁻¹, ← div_eq_mul_inv] using
    norm_window (k := q.1) hq.1 hu huv hy (r := 1 / 2) (by norm_num) hB q.2
      (by simpa only [div_eq_mul_inv, one_mul] using hq.2) H hbound

/-- The entire archimedean sum of the Chapter 12 local restrictions has square-root
decay for every fixed number field, character and continuous positive-window profile. -/
theorem translated_archimedean_sum_bound (ψ : PontryaginDual C𝔽) (H : ℝ → ℂ)
    (hH : Continuous H) {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hs : tsupport H ⊆ Icc u v) :
    ∃ C ≥ (0 : ℝ), ∀ y ≥ (0 : ℝ), ∀ φ : BruhatCompactSupport C𝔽,
      (∀ g, φ.val g = (ψ g : ℂ) * H (Real.log ((ideleClassNorm F g).val : ℝ) - y)) →
      ∀ A : (w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ,
        (∀ w t, (A w).val t = φ.val (arch(w) t)) →
        ‖∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (A w)‖ ≤
          C * Real.exp (-(y/2)) := by
  have hzero (x : ℝ) (hx : x ∉ Icc u v) : H x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))
  obtain ⟨B, hB⟩ := hH.bounded_above_of_compact_support (HasCompactSupport.intro isCompact_Icc hzero)
  have hB₀ := (norm_nonneg (H 0)).trans (hB 0)
  let c (w : InfinitePlace F) :=
    (v - u) * B * Real.exp (-(u/2)) / (1 - Real.exp (-(u/(positiveParameter ψ⁻¹ w).1)))
  have hc (w : InfinitePlace F) : 0 ≤ c w := by
    have hd := div_pos hu (positiveParameter_rate ψ⁻¹ w).1
    exact div_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr huv) hB₀) (Real.exp_pos _).le)
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hd))).le
  refine ⟨∑ w, c w, Finset.sum_nonneg (fun w _ ↦ hc w), fun y hy φ hφ A hA ↦ ?_⟩
  calc
    _ ≤ ∑ w : InfinitePlace F, ‖infiniteConnesWeilPrincipalValue w (A w)‖ := norm_sum_le _ _
    _ ≤ ∑ w, c w * Real.exp (-(y/2)) := Finset.sum_le_sum fun w _ ↦
      translated_principalValue_bound w ψ H hH.measurable hu huv hB₀ (fun x _ ↦ hB x) hzero
        hy (A w) (fun t ↦ (hA w t).trans (hφ _))
    _ = _ := (Finset.sum_mul ..).symm


/-- The explicit window integral is measurable in the translation, even for a
merely measurable profile. -/
theorem measurable_window (k u v : ℝ) (z : ℂ) (H : ℝ → ℂ) (hH : Measurable H) :
    Measurable (fun y : ℝ ↦ ∫ x in Icc (y+u) (y+v), translatedDensity k z H y x) := by
  let S : Set (ℝ × ℝ) := {p | p.1 + u ≤ p.2 ∧ p.2 ≤ p.1 + v}
  have hS : MeasurableSet S := (measurableSet_le (measurable_fst.add_const u) measurable_snd).inter
    (measurableSet_le measurable_snd (measurable_fst.add_const v))
  have hK : Measurable (fun p : ℝ × ℝ ↦ translatedDensity k z H p.1 p.2) := by
    unfold translatedDensity
    fun_prop
  have hI := (hK.indicator hS).stronglyMeasurable.integral_prod_right' (ν := volume)
  convert hI.measurable using 1
  funext y
  rw [← integral_indicator measurableSet_Icc]
  rfl

/-- Actual principal values of any family of translated Bruhat restrictions are
measurable on the nonnegative half-line, with arbitrary representatives elsewhere. -/
theorem translated_principalValue_aemeasurable
    {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F)
    (ψ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (H : ℝ → ℂ) (hH : Measurable H)
    {u v : ℝ} (hu : 0 < u) (hs : ∀ x, x ∉ Icc u v → H x = 0)
    (A : ℝ → BruhatCompactSupport w.Completionˣ) (hA : ∀ y ≥ (0 : ℝ), ∀ t,
      (A y).val t = (ψ (IdeleClassGroup.ofCompletion (𝓞 F) F w t) : ℂ) *
        H (Real.log ((ideleClassNorm F (IdeleClassGroup.ofCompletion (𝓞 F) F w t)).val : ℝ) - y)) :
    AEMeasurable (fun y : ℝ ↦ infiniteConnesWeilPrincipalValue w (A y)) (volume.restrict (Ici 0)) := by
  let q := positiveParameter ψ⁻¹ w
  apply (measurable_window q.1 u v q.2 H hH).aemeasurable.congr
  filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
  exact (translated_principalValue w ψ H hH hu hy hs (A y) (hA y hy)).symm

end FirstPrimeArch

variable {F : Type*} [Field F] [NumberField F]
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "G" => IdeleClassGroup (𝓞 F) F
local notation "U" => PontryaginDual G
local notation "tw(" χ ")" => ideleClassNormTwist (F := F) χ 0
local notation "Npk(" j ")" => (j).1.asIdeal.absNorm ^ ((j).2 + 1)
local notation "λpk(" χ ", " j ")" =>
  heckeIdealVonMangoldt tw(χ) ((j).1.asIdeal ^ ((j).2 + 1))

/-- A finite place has rational-prime norm precisely in residue degree one. -/
theorem firstPrime_norm_prime_iff (v : V) :
    v.asIdeal.absNorm.Prime ↔ v.asIdeal.inertiaDeg ℤ = 1 := by
  let p := (v.asIdeal.under ℤ).absNorm
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  have hp : p.Prime := Nat.absNorm_under_prime v.asIdeal
  have : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := Int.liesOver_span_absNorm _
  have hnorm : p ^ v.asIdeal.inertiaDeg ℤ = v.asIdeal.absNorm := by
    simpa only [Int.natAbs_natCast] using Ideal.natAbs_pow_inertiaDeg (p : ℤ) v.asIdeal
  exact ⟨fun h ↦ (h.pow_eq_iff.mp hnorm).2, fun h ↦ by simpa only [← hnorm, h, pow_one] using hp⟩

/-- A prime-power atom has rational-prime norm exactly at exponent one in degree one. -/
theorem firstPrime_primePower_norm_iff (v : V) (k : ℕ) :
    (v.asIdeal.absNorm ^ (k + 1)).Prime ↔ k = 0 ∧ v.asIdeal.inertiaDeg ℤ = 1 := by
  constructor
  · intro h
    have hk := (h.pow_eq_iff.mp (rfl : v.asIdeal.absNorm ^ (k + 1) = _)).2
    have hk₀ : k = 0 := by omega
    subst k
    exact ⟨rfl, (firstPrime_norm_prime_iff v).mp (by simpa using h)⟩
  · rintro ⟨rfl, hf⟩
    simpa using (firstPrime_norm_prime_iff v).mpr hf

/-- At a rational prime the Hecke coefficient is the sum of the unramified first
uniformizer values at exactly the residue-degree-one places above that prime. -/
theorem firstPrime_coefficient (χ : U) {p : ℕ} (hp : p.Prime) :
    heckeLogDerivCoefficient tw(χ) p =
      ∑ᶠ v : {v : V // v.asIdeal.absNorm = p ∧ v.asIdeal.inertiaDeg ℤ = 1},
        if tw(χ).IsUnramifiedAt v.val then
          tw(χ).localValue v.val * (Real.log (p : ℝ) : ℂ) else 0 := by
  classical
  let A := {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = p}
  let S := {v : V // v.asIdeal.absNorm = p ∧ v.asIdeal.inertiaDeg ℤ = 1}
  let e : S ≃ A :=
    { toFun := fun v ↦ ⟨v.val.asIdeal, v.val.ne_bot, v.property.1⟩
      invFun := fun I ↦ by
        have hprime : I.val.absNorm.Prime := by rw [I.property.2]; exact hp
        let v : V := ⟨I.val, Ideal.isPrime_of_irreducible_absNorm
          (Nat.irreducible_iff_prime.mpr (Nat.prime_iff.mp hprime)), I.property.1⟩
        exact ⟨v, I.property.2, (firstPrime_norm_prime_iff v).mp hprime⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  change (∑ᶠ I : A, heckeIdealVonMangoldt tw(χ) I.val) = _
  rw [← finsum_comp_equiv e]
  apply finsum_congr
  intro v
  change heckeIdealVonMangoldt tw(χ) v.val.asIdeal = _
  have h : heckeIdealVonMangoldt tw(χ) (v.val.asIdeal ^ 1) =
      (if tw(χ).IsUnramifiedAt v.val then tw(χ).localValue v.val ^ 1 else 0) *
        (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) := by
    rw [heckeIdealVonMangoldt, heckeIdealValue_prime_pow _ v.val (by decide : 0 < 1),
      idealVonMangoldt_prime_pow v.val (by decide : 0 < 1)]
  simpa only [pow_one, v.property.1, ite_mul, zero_mul] using h

/-- Group an arbitrary finite cutoff of positive prime ideal powers by rational norm.
The prime-power weights vanish on ramified ideals and off powers of primes. -/
private theorem firstPrime_regroup (χ : U) (T : ℕ) (b : ℕ → ℂ)
    (hb : ∀ n ∉ Finset.Ioc 0 T, b n = 0) :
    Summable (fun j : V × ℕ ↦ λpk(χ, j) * b Npk(j)) ∧
    (∑' j : V × ℕ, λpk(χ, j) * b Npk(j)) =
      ∑ n ∈ Finset.Ioc 0 T, heckeLogDerivCoefficient tw(χ) n * b n := by
  classical
  let I₀ := {I : Ideal (𝓞 F) // I ≠ ⊥}
  let P (j : V × ℕ) : I₀ := ⟨j.1.asIdeal ^ (j.2 + 1), pow_ne_zero _ j.1.ne_bot⟩
  let f (I : I₀) := heckeIdealVonMangoldt tw(χ) I.val * b I.val.absNorm
  have hf : HasFiniteSupport f := by
    apply ((Ring.HasFiniteQuotients.finite_absNorm_le (S := 𝓞 F) T).preimage
      (Subtype.val_injective (p := fun I : Ideal (𝓞 F) ↦ I ≠ ⊥)).injOn).subset
    intro I hI
    by_contra hn
    apply hI
    simp only [f, hb I.val.absNorm (fun h ↦ hn (Finset.mem_Ioc.mp h).2), mul_zero]
  have hs : Summable f := summable_of_hasFiniteSupport hf
  have hinj : Injective P := by
    rintro ⟨v, k⟩ ⟨w, j⟩ he
    have heq : v.asIdeal ^ (k + 1) = w.asIdeal ^ (j + 1) := congrArg Subtype.val he
    obtain rfl := HeightOneSpectrum.eq_of_dvd_pow ((dvd_pow_self _ k.succ_ne_zero).trans heq.dvd)
    exact Prod.ext rfl (Nat.succ.inj (pow_injective_of_not_isUnit v.prime.not_isUnit v.ne_bot heq))
  have he (j : V × ℕ) : f (P j) = λpk(χ, j) * b Npk(j) := by simp only [f, P, map_pow]
  refine ⟨(hs.comp_injective hinj).congr he, ?_⟩
  have hout : support f ⊆ range P := by
    intro I hI
    by_contra h
    have hn : ¬ ∃ v : V, ∃ k : ℕ, 0 < k ∧ I.val = v.asIdeal ^ k := by
      rintro ⟨v, _ | k, hk, heq⟩
      · exact hk.false
      · exact h ⟨(v, k), Subtype.ext heq.symm⟩
    exact hI (by simp [f, heckeIdealVonMangoldt, idealVonMangoldt, hn])
  let N (I : I₀) := I.val.absNorm
  have hgroup := hs.hasSum.tsum_fiberwise N
  have hterm (n : ℕ) : (∑' I : N ⁻¹' {n}, f I.val) = heckeLogDerivCoefficient tw(χ) n * b n := by
    let A := {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n}
    have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = n}.Finite :=
      (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) n).subset fun _ h ↦ h.2
    let : Finite A := hfin.to_subtype
    let : Fintype A := Fintype.ofFinite _
    let e : A ≃ ↥(N ⁻¹' {n}) :=
      { toFun := fun I ↦ ⟨⟨I.val, I.property.1⟩, I.property.2⟩
        invFun := fun I ↦ ⟨I.val.val, I.val.property, I.property⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [← e.tsum_eq, tsum_fintype, heckeLogDerivCoefficient, finsum_eq_sum_of_fintype, Finset.sum_mul]
    exact Finset.sum_congr rfl fun I _ ↦ by change _ * b I.val.absNorm = _; rw [I.property.2]; rfl
  calc
    _ = ∑' I : I₀, f I := (tsum_congr fun j ↦ (he j).symm).trans (hinj.tsum_eq hout)
    _ = ∑' n, heckeLogDerivCoefficient tw(χ) n * b n := (hgroup.congr_fun fun n ↦ (hterm n).symm).tsum_eq.symm
    _ = _ := tsum_eq_sum fun n hn ↦ by rw [hb n hn, mul_zero]

/-- The log-profile with the half-density at rational norm `n`. -/
def firstPrimeShellWeight (H : ℝ → ℂ) (y : ℝ) (n : ℕ) : ℂ :=
  H (Real.log (n : ℝ) - y) / (Real.sqrt (n : ℝ) : ℂ)

/-- The signed first-prime contribution, with only first powers in residue degree one. -/
def firstPrimeDegreeOneSum (χ : U) (H : ℝ → ℂ) (y b : ℝ) : ℂ :=
  ∑ p ∈ Finset.Ioc 0 ⌊Real.exp (y + b)⌋₊ with p.Prime,
    (∑ᶠ v : {v : V // v.asIdeal.absNorm = p ∧ v.asIdeal.inertiaDeg ℤ = 1},
      if tw(χ).IsUnramifiedAt v.val then
        tw(χ).localValue v.val * (Real.log (p : ℝ) : ℂ) else 0) *
        firstPrimeShellWeight H y p

/-- The remaining positive-shell terms have rational norm `p^a`, `a ≥ 2`. -/
def firstPrimeHigherPowers (χ : U) (H : ℝ → ℂ) (y b : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊Real.exp (y + b)⌋₊ with IsPrimePow n ∧ ¬ n.Prime,
    heckeLogDerivCoefficient tw(χ) n * firstPrimeShellWeight H y n

private theorem firstPrime_weight_support (H : ℝ → ℂ) {u v y : ℝ} (hu : 0 < u)
    (hs : tsupport H ⊆ Icc u v) (hy : 0 ≤ y) {n : ℕ}
    (hn : H (Real.log (n : ℝ) - y) ≠ 0) :
    0 < (n : ℝ) ∧ y + u ≤ Real.log n ∧ Real.log n ≤ y + v := by
  have h := hs (subset_tsupport H hn)
  have hn₀ : n ≠ 0 := by rintro rfl; simp at h; linarith [h.1]
  exact ⟨by exact_mod_cast Nat.pos_of_ne_zero hn₀, by linarith [h.1], by linarith [h.2]⟩

private theorem firstPrime_shell_assemble (χ : U) (H : ℝ → ℂ) {u v y : ℝ} (hu : 0 < u)
    (hs : tsupport H ⊆ Icc u v) (hy : 0 ≤ y) :
    Summable (fun j : V × ℕ ↦ introTracePrimePower χ (fun r ↦ H (Real.log r - y)) j.1 j.2) ∧
    (∑' j : V × ℕ, introTracePrimePower χ (fun r ↦ H (Real.log r - y)) j.1 j.2) =
      ∑ n ∈ Finset.Ioc 0 ⌊Real.exp (y + v)⌋₊,
        heckeLogDerivCoefficient tw(χ) n * firstPrimeShellWeight H y n := by
  classical
  have hcut (n : ℕ) (hn : n ∉ Finset.Ioc 0 ⌊Real.exp (y+v)⌋₊) :
      firstPrimeShellWeight H y n = 0 := by
    by_cases h : H (Real.log (n : ℝ) - y) = 0
    · simp [firstPrimeShellWeight, h]
    · obtain ⟨h₀, -, hhigh⟩ := firstPrime_weight_support H hu hs hy h
      exact (hn (Finset.mem_Ioc.mpr ⟨by exact_mod_cast h₀, Nat.le_floor
        ((Real.log_le_iff_le_exp h₀).mp hhigh)⟩)).elim
  have hatom (j : V × ℕ) : introTracePrimePower χ (fun r ↦ H (Real.log r - y)) j.1 j.2 =
      λpk(χ, j) * firstPrimeShellWeight H y Npk(j) := by
    obtain ⟨v, k⟩ := j
    let q : ℝ := v.asIdeal.absNorm
    have hq : 1 < q := by dsimp [q]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    have hQ : 1 < q ^ (k + 1) := one_lt_pow₀ hq k.succ_ne_zero
    have hz : H (Real.log ((q ^ (k + 1))⁻¹) - y) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      have hsmall := Real.log_nonpos (inv_nonneg.mpr (zero_le_one.trans hQ.le))
        (inv_le_one_of_one_le₀ hQ.le)
      linarith [(hs h).1]
    rw [heckeIdealVonMangoldt, heckeIdealValue_prime_pow _ v k.succ_pos,
      idealVonMangoldt_prime_pow v k.succ_pos]
    change (if tw(χ).IsUnramifiedAt v then (Real.log q : ℂ) *
      (_ * H (Real.log (q ^ (k + 1)) - y) + _ * H (Real.log (q ^ (k + 1))⁻¹ - y)) /
      ((q : ℂ) ^ (((k + 1 : ℕ) : ℂ) / 2)) else 0) = _
    have hsqrt : (Real.sqrt (q ^ (k + 1)) : ℂ) = (q : ℂ) ^ (((k + 1 : ℕ) : ℂ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hq.le),
        Complex.ofReal_cpow (zero_le_one.trans hq.le)]
      congr 1
      push_cast
      ring
    rw [hz, ← hsqrt]
    simp only [firstPrimeShellWeight, Nat.cast_pow, mul_zero, add_zero, q, Nat.succ_eq_add_one]
    split_ifs <;> ring
  obtain ⟨hS, hsum⟩ := firstPrime_regroup χ _ _ hcut
  exact ⟨hS.congr (fun j ↦ (hatom j).symm), (tsum_congr hatom).trans hsum⟩

private theorem firstPrime_filter (χ : U) (H : ℝ → ℂ) (y b : ℝ) :
    (∑ n ∈ Finset.Ioc 0 ⌊Real.exp (y + b)⌋₊ with n.Prime,
      heckeLogDerivCoefficient tw(χ) n * firstPrimeShellWeight H y n) =
      firstPrimeDegreeOneSum χ H y b := by
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [firstPrime_coefficient χ (Finset.mem_filter.mp hn).2]

/-- Exact decomposition of all translated positive-shell Hecke orbital atoms into
the residue-degree-one first primes and the remaining composite rational norms. -/
theorem firstPrime_orbital_eq (χ : U) (H : ℝ → ℂ) {u v y : ℝ} (hu : 0 < u)
    (hs : tsupport H ⊆ Icc u v) (hy : 0 ≤ y) :
    (∑' j : V × ℕ, introTracePrimePower χ (fun r ↦ H (Real.log r - y)) j.1 j.2) =
      firstPrimeDegreeOneSum χ H y v + firstPrimeHigherPowers χ H y v := by
  rw [(firstPrime_shell_assemble χ H hu hs hy).2, ← firstPrime_filter χ H,
    firstPrimeHigherPowers, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  by_cases hp : n.Prime
  · simp [hp]
  by_cases hq : IsPrimePow n
  · simp [hp, hq]
  have hz : heckeLogDerivCoefficient tw(χ) n = 0 := norm_le_zero_iff.mp (by
    simpa only [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hq, mul_zero]
      using heckeLogDerivCoefficient_le_vonMangoldt χ n)
  simp [hp, hq, hz]

/-- On a closed positive shell the bound for the higher rational powers depends on the
width of the shell. Only the values of the profile on its support enter. -/
theorem firstPrime_higherPowers_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type*) [Field E] [NumberField E]
      (χ : PontryaginDual (IdeleClassGroup (𝓞 E) E)) (H : ℝ → ℂ)
      (u v M : ℝ), 0 < u → tsupport H ⊆ Icc u v → 0 ≤ M →
      (∀ x ∈ tsupport H, ‖H x‖ ≤ M) → ∀ y ≥ 0,
        ‖firstPrimeHigherPowers χ H y v‖ ≤ Module.finrank ℚ E * M * (C * Real.exp ((v-u) / 2)) := by
  obtain ⟨C, hC⟩ := heckeLogDerivCoefficient_sum_sub_sum_prime_le_mul_sqrt
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro F _ _ χ H u v M hu hs hM₀ hM y hy
  have hweight (n : ℕ) : ‖firstPrimeShellWeight H y n‖ ≤ M / Real.exp ((y+u)/2) := by
    by_cases h : H (Real.log (n : ℝ) - y) = 0
    · simpa [firstPrimeShellWeight, h] using div_nonneg hM₀ (Real.exp_pos ((y+u)/2)).le
    · obtain ⟨hn, hlow, -⟩ := firstPrime_weight_support H hu hs hy h
      have hb : Real.exp ((y+u)/2) ≤ Real.sqrt n := by
        rw [Real.exp_half]
        apply Real.sqrt_le_sqrt
        simpa only [Real.exp_log hn] using Real.exp_le_exp.mpr hlow
      rw [firstPrimeShellWeight, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact (div_le_div_of_nonneg_right (hM _ (subset_tsupport H h)) (Real.sqrt_nonneg _)).trans
        (div_le_div_of_nonneg_left hM₀ (Real.exp_pos _) hb)
  have h := hC F χ (Real.exp (y+v)) (firstPrimeShellWeight H y) (M / Real.exp ((y+u)/2)) hweight
  rw [← (firstPrime_shell_assemble χ H hu hs hy).2, firstPrime_orbital_eq χ H hu hs hy,
    firstPrime_filter χ H, add_sub_cancel_left] at h
  refine h.trans ?_
  rw [← Real.exp_half, show (y+v)/2 = (y+u)/2 + (v-u)/2 by ring, Real.exp_add]
  calc
    _ = (Module.finrank ℚ F : ℝ) * M * (C * Real.exp ((v-u)/2)) := by
      field_simp [(Real.exp_pos ((y+u)/2)).ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
      (mul_nonneg (Nat.cast_nonneg _) hM₀)

local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "normAt(" g ")" => (((ideleClassNorm F) (g : G)).val : ℝ)
local notation "unitMass(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal

attribute [local instance] instFiniteCompletionUnitsLocallyCompactSec4b

/-- The sum of the normalized finite-place principal values on `ψ · H(log |x| - y)`
is the degree-one first-prime sum for `ψ⁻¹` plus its higher rational prime powers. -/
theorem firstPrime_finiteLocal_eq (ψ : U) (H : ℝ → ℂ) {u v y : ℝ} (hu : 0 < u)
    (hs : tsupport H ⊆ Icc u v) (hy : 0 ≤ y)
    (B : (v : V) → BruhatCompactSupport (v.adicCompletion F)ˣ)
    (hB : ∀ v u, (B v).val u =
      (ψ (finiteClass(v) u) : ℂ) * H (Real.log normAt(finiteClass(v) u) - y)) :
    (∑' v : V, ((Real.log (v.asIdeal.absNorm : ℝ) / unitMass(v) : ℝ) : ℂ) *
      finiteConnesWeilPrincipalValue v 1 (B v)) =
    firstPrimeDegreeOneSum ψ⁻¹ H y v + firstPrimeHigherPowers ψ⁻¹ H y v := by
  let h (r : ℝ) := H (Real.log r - y)
  have h₁ : h 1 = 0 := by
    change H (Real.log (1 : ℝ) - y) = 0
    rw [Real.log_one, zero_sub]
    exact image_eq_zero_of_notMem_tsupport fun hx ↦ (not_le_of_gt (by linarith : -y < u)) (hs hx).1
  have htest (g : G) : introTraceTest ψ⁻¹ h g = (ψ g : ℂ) * H (Real.log normAt(g) - y) := by
    change star ((((ψ g)⁻¹ : Circle) : ℂ)) * _ = _
    rw [Circle.coe_inv_eq_conj, Complex.star_def, Complex.conj_conj]
  calc
    _ = ∑' v : V, ∑' k : ℕ, introTracePrimePower ψ⁻¹ h v k :=
      tsum_congr fun v ↦ finiteConnesWeilPrincipalValue_eq_introTracePrimePower_sum ψ⁻¹ h h₁ v (B v)
        (fun u ↦ (hB v u).trans (htest _).symm)
    _ = ∑' j : V × ℕ, introTracePrimePower ψ⁻¹ h j.1 j.2 :=
      (firstPrime_shell_assemble ψ⁻¹ H hu hs hy).1.tsum_prod.symm
    _ = _ := firstPrime_orbital_eq ψ⁻¹ H hu hs hy


local notation "normOneMass" => ((normOneIdeleClassTamagawaMeasure F) univ).toReal

open Classical in
/-- Orthogonality and log translation give the exact polar Mellin moments of
the genuine character-weighted test in the translated explicit formula. -/
theorem translatedPrimeTest_mellin (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ (ideleClassNorm F))
    (ψ : U) (hψ : ∀ t, ψ (τ t) = 1) (H : ℝ → ℂ) (y : ℝ) (φ : (BruhatCompactSupport G))
    (hφ : ∀ g, φ.val g = (ψ g : ℂ) * H (Real.log normAt(g) - y)) (s : ℂ) :
    (∫ g, φ.val g * ideleClassNormTwist 1 s g ∂ideleClassTamagawaMeasure F) =
      if ψ = 1 then (normOneMass : ℂ) * (Complex.exp (s * y) * ∫ x : ℝ, H x * Complex.exp (s * x)) else 0 := by
  let f (r : ℝ) := H (Real.log r - y)
  have hinv (t) : ψ⁻¹ (τ t) = 1 := by change (ψ (τ t))⁻¹ = 1; rw [hψ t, inv_one]
  have htest (g : G) : φ.val g = introTraceTest ψ⁻¹ f g := by
    rw [hφ]
    change _ = star ((((ψ g)⁻¹ : Circle) : ℂ)) * _
    rw [Circle.coe_inv_eq_conj, Complex.star_def, Complex.conj_conj]
  rw [introTraceTest_mellin_normalized τ hτ ψ⁻¹ 1 hinv (fun _ ↦ rfl) f φ htest]
  by_cases h : ψ = 1
  · simp only [h, inv_one, ite_true]
    congr 1
    calc
      introTraceMellin f s = ∫ x : ℝ, H (x - y) * Complex.exp (s * x) := by
        rw [introTraceMellin, mellin, ← integral_comp_exp]
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        simp only [f, Real.log_exp, Complex.real_smul, smul_eq_mul]
        rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
          ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp,
          ← mul_assoc, ← Complex.exp_add, mul_comm]
        congr 1
        ring_nf
      _ = ∫ x : ℝ, H x * Complex.exp (s * (x + y)) := by
        convert integral_sub_right_eq_self (μ := volume)
          (fun x : ℝ ↦ H x * Complex.exp (s * (x + y))) y using 1
        congr 1
        funext x
        simp
      _ = _ := by
        rw [← integral_const_mul]
        congr 1
        funext x
        rw [mul_add, Complex.exp_add]
        ring
  · simp [h, eq_comm]

local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "archTest" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest" => ((w : V) → BruhatCompactSupport (w.adicCompletion F)ˣ)
local notation "moment(" H ", " s ")" => (∫ x : ℝ, (H : ℝ → ℂ) x * Complex.exp ((s : ℂ) * x))
local notation "testMellin(" φ ", " s ")" =>
  modulatedFourierMellin (continuousIdeleClassNorm F) univ
    (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation (continuousIdeleClassNorm F))
    (ideleClassTamagawaMeasure F) (φ : BruhatCompactSupport G).val (ideleClassNormTwist 1 (s : ℂ))

/-- The polar moment of the translated test after division by the norm-one volume.
Only the section-normalized trivial character contributes. -/
def firstPrimePolarMoment (ψ : U) (H : ℝ → ℂ) (y : ℝ) (s : ℂ) : ℂ :=
  if ψ = 1 then Complex.exp (s * y) * moment(H, s) else 0

/-- Paper: Theorem B.4.4.7, p. 623. The two global polar terms minus the volume times the
actual normalized local principal values, as in the Chapter 12 translated explicit formula. -/
def firstPrimeLocalTerms (φ : BruhatCompactSupport G) (A : archTest) (B : finiteTest) : ℂ :=
  testMellin(φ, 1/2) + testMellin(φ, -1/2) -
    (normOneMass : ℂ) * ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (A w)) +
      ∑' w : V, ((Real.log (w.asIdeal.absNorm : ℝ) / unitMass(w) : ℝ) : ℂ) *
        finiteConnesWeilPrincipalValue w 1 (B w))

/-- Exact decomposition of the signed local expression on a positive translate. The finite
remainder contains all the composite rational norms, including first powers in higher degree. -/
theorem firstPrime_localTerms_eq (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ (ideleClassNorm F))
    (ψ : U) (hψ : ∀ t, ψ (τ t) = 1) (H : ℝ → ℂ) {u v y : ℝ} (hu : 0 < u)
    (hs : tsupport H ⊆ Icc u v) (hy : 0 ≤ y) (φ : BruhatCompactSupport G)
    (hφ : ∀ g, φ.val g = (ψ g : ℂ) * H (Real.log normAt(g) - y))
    (A : archTest) (B : finiteTest) (hB : ∀ w t, (B w).val t = φ.val (finiteClass(w) t)) :
    firstPrimeLocalTerms φ A B = (normOneMass : ℂ) * (firstPrimePolarMoment ψ H y (1/2) +
      firstPrimePolarMoment ψ H y (-1/2) - (∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (A w)) -
      firstPrimeDegreeOneSum ψ⁻¹ H y v - firstPrimeHigherPowers ψ⁻¹ H y v) := by
  have hpolar (s : ℂ) : testMellin(φ, s) = (normOneMass : ℂ) * firstPrimePolarMoment ψ H y s := by
    simpa only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ,
      firstPrimePolarMoment, mul_ite, mul_zero] using translatedPrimeTest_mellin τ hτ ψ hψ H y φ hφ s
  rw [firstPrimeLocalTerms, hpolar, hpolar, firstPrime_finiteLocal_eq ψ H hu hs hy B
    (fun w t ↦ (hB w t).trans (hφ _))]
  ring

private theorem firstPrime_volume_pos : 0 < normOneMass := by
  have := NumberField.Units.regulator_pos F
  have := NumberField.classNumber_pos F
  have := NumberField.Units.torsionOrder_pos F
  have : (0 : ℝ) < Real.sqrt (Int.natAbs (NumberField.discr F) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero F))
  rw [normOneIdeleClassTamagawaMeasure_volume, ENNReal.toReal_ofReal (by positivity)]
  positivity

/-- Uniform comparison between the centered degree-one sum and the actual signed
geometric terms. It holds for every number field, every normalized character, and
each choice of the genuine local restrictions of each translated test. -/
theorem firstPrime_centered_localTerms_uniform (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ (ideleClassNorm F))
    (ψ : U) (hψ : ∀ t, ψ (τ t) = 1) (H : ℝ → ℂ) (hH : Continuous H) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hs : tsupport H ⊆ Icc u v) :
    ∃ C ≥ (0 : ℝ), ∀ y ≥ (0 : ℝ), ∀ φ : BruhatCompactSupport G,
      (∀ g, φ.val g = (ψ g : ℂ) * H (Real.log normAt(g) - y)) → ∀ (A : archTest) (B : finiteTest),
      (∀ w t, (A w).val t = φ.val (archClass(w) t)) →
      (∀ w t, (B w).val t = φ.val (finiteClass(w) t)) →
      ‖firstPrimeDegreeOneSum ψ⁻¹ H y v - firstPrimePolarMoment ψ H y (1/2) +
        firstPrimeLocalTerms φ A B / (normOneMass : ℂ)‖ ≤ C := by
  obtain ⟨D, hD, harch⟩ := FirstPrimeArch.translated_archimedean_sum_bound ψ H hH hu huv hs
  obtain ⟨K, hK, hrem⟩ := firstPrime_higherPowers_uniform
  have hc : HasCompactSupport H := HasCompactSupport.intro isCompact_Icc
    (fun x hx ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hx (hs h))
  obtain ⟨M, hM⟩ := hH.bounded_above_of_compact_support hc
  have hM₀ : 0 ≤ M := (norm_nonneg (H 0)).trans (hM 0)
  let Q := (Module.finrank ℚ F : ℝ) * M * (K * Real.exp ((v-u)/2))
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨‖moment(H, -1/2)‖ + D + Q, by positivity, fun y hy φ hφ A B hA hB ↦ ?_⟩
  have hV : (normOneMass : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (firstPrime_volume_pos (F := F)).ne'
  have he := firstPrime_localTerms_eq τ hτ ψ hψ H hu hs hy φ hφ A B hB
  rw [he, mul_div_cancel_left₀ _ hV]
  let S := ∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (A w)
  have ha : ‖S‖ ≤ D :=
    (harch y hy φ hφ A hA).trans (mul_le_of_le_one_right hD (Real.exp_le_one_iff.mpr (by linarith)))
  have hq : ‖firstPrimeHigherPowers ψ⁻¹ H y v‖ ≤ Q := hrem F ψ⁻¹ H u v M hu hs hM₀ (fun x _ ↦ hM x) y hy
  have hp : ‖firstPrimePolarMoment ψ H y (-1/2)‖ ≤ ‖moment(H, -1/2)‖ := by
    by_cases h : ψ = 1
    · simp only [firstPrimePolarMoment, ite_eq_left h, norm_mul, Complex.norm_exp]
      apply mul_le_of_le_one_left (norm_nonneg _)
      apply Real.exp_le_one_iff.mpr
      simp
      linarith
    · simp [firstPrimePolarMoment, h]
  calc
    _ = ‖firstPrimePolarMoment ψ H y (-1/2) - S - firstPrimeHigherPowers ψ⁻¹ H y v‖ := by
      congr 1
      dsimp only [S]
      ring
    _ ≤ ‖firstPrimePolarMoment ψ H y (-1/2)‖ + ‖S‖ + ‖firstPrimeHigherPowers ψ⁻¹ H y v‖ :=
      (norm_sub_le ..).trans (add_le_add (norm_sub_le ..) le_rfl)
    _ ≤ _ := add_le_add (add_le_add hp ha) hq


/-- A positive lower bound on the envelope transports any pointwise estimate of the signed
local terms to the centered degree-one observable. The local representatives are constructed
from the translated smooth test. -/
theorem firstPrime_centered_bound_of_localTerms (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ (ideleClassNorm F))
    (ψ : U) (hψ : ∀ t, ψ (τ t) = 1) (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hs : tsupport H ⊆ Icc u v)
    (weight : ℝ → ℝ) {m D : ℝ} (hm : 0 < m) (hD : 0 ≤ D) (hw : ∀ y ≥ 0, m ≤ weight y)
    (hlocal : ∀ y ≥ (0 : ℝ), ∀ φ : BruhatCompactSupport G,
      (∀ g, φ.val g = (ψ g : ℂ) * H (Real.log normAt(g) - y)) → ∀ (A : archTest) (B : finiteTest),
      (∀ w t, (A w).val t = φ.val (archClass(w) t)) →
      (∀ w t, (B w).val t = φ.val (finiteClass(w) t)) → ‖firstPrimeLocalTerms φ A B‖ ≤ D * weight y) :
    ∃ C ≥ (0 : ℝ), ∀ y ≥ (0 : ℝ),
      ‖firstPrimeDegreeOneSum ψ⁻¹ H y v - firstPrimePolarMoment ψ H y (1/2)‖ ≤ C * weight y := by
  have hc : HasCompactSupport H := HasCompactSupport.intro isCompact_Icc
    (fun x hx ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hx (hs h))
  obtain ⟨C, hC, he⟩ := firstPrime_centered_localTerms_uniform τ hτ ψ hψ H hH.continuous hu huv hs
  have hV := firstPrime_volume_pos (F := F)
  refine ⟨C / m + D / normOneMass, by positivity, fun y hy ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := exists_characterNormTest (F := F) ψ (fun x ↦ H (x - y))
    (hH.comp (contDiff_id.sub contDiff_const)) (hc.comp_homeomorph (Homeomorph.subRight y))
  let A (w : InfinitePlace F) := (idelicExplicitFormula_infiniteTestMap (F := F) w).choose φ
  let B (w : V) := (idelicExplicitFormula_finiteTestMap (F := F) w).choose φ
  have ha (w : InfinitePlace F) (t) : (A w).val t = φ.val (archClass(w) t) :=
    (idelicExplicitFormula_infiniteTestMap (F := F) w).choose_spec φ t
  have hb (w : V) (t) : (B w).val t = φ.val (finiteClass(w) t) :=
    (idelicExplicitFormula_finiteTestMap (F := F) w).choose_spec φ t
  let P := firstPrimeDegreeOneSum ψ⁻¹ H y v - firstPrimePolarMoment ψ H y (1/2)
  let L := firstPrimeLocalTerms φ A B / (normOneMass : ℂ)
  have hL : ‖L‖ ≤ (D / normOneMass) * weight y := by
    rw [show ‖L‖ = ‖firstPrimeLocalTerms φ A B‖ / normOneMass by
      simp only [L, norm_div, Complex.norm_real, Real.norm_of_nonneg hV.le]]
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (hlocal y hy φ hφ A B ha hb) hV.le
  have hCm : C ≤ (C / m) * weight y := by
    calc C = (C / m) * m := (div_mul_cancel₀ C hm.ne').symm
         _ ≤ _ := mul_le_mul_of_nonneg_left (hw y hy) (div_nonneg hC hm.le)
  calc
    ‖P‖ = ‖(P + L) - L‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖P + L‖ + ‖L‖ := norm_sub_le ..
    _ ≤ C + (D / normOneMass) * weight y := add_le_add (he y hy φ hφ A B ha hb) hL
    _ ≤ (C / m) * weight y + (D / normOneMass) * weight y := add_le_add hCm le_rfl
    _ = _ := (add_mul ..).symm

/-- Every square-root saving proved for the full signed local expression carries over
to the actual centered first-prime sum at the same fixed value of the saving parameter. -/
theorem firstPrime_centered_exp_sub_sqrt_of_localTerms (τ : ℝ≥0ˣ →ₜ* G)
    (hτ : RightInverse τ (ideleClassNorm F)) (ψ : U) (hψ : ∀ t, ψ (τ t) = 1)
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hs : tsupport H ⊆ Icc u v) (K : ℝ)
    (hlocal : ∃ D ≥ (0 : ℝ), ∀ y ≥ (0 : ℝ), ∀ φ : BruhatCompactSupport G,
      (∀ g, φ.val g = (ψ g : ℂ) * H (Real.log normAt(g) - y)) → ∀ (A : archTest) (B : finiteTest),
      (∀ w t, (A w).val t = φ.val (archClass(w) t)) →
      (∀ w t, (B w).val t = φ.val (finiteClass(w) t)) →
      ‖firstPrimeLocalTerms φ A B‖ ≤ D * Real.exp (y / 2 - K * Real.sqrt y)) :
    ∃ C ≥ (0 : ℝ), ∀ y ≥ (0 : ℝ), ‖firstPrimeDegreeOneSum ψ⁻¹ H y v -
      firstPrimePolarMoment ψ H y (1/2)‖ ≤ C * Real.exp (y / 2 - K * Real.sqrt y) := by
  obtain ⟨D, hD, hd⟩ := hlocal
  apply firstPrime_centered_bound_of_localTerms τ hτ ψ hψ H hH hu huv hs
    (fun y ↦ Real.exp (y / 2 - K * Real.sqrt y)) (Real.exp_pos (-(K^2)/2)) hD _ hd
  intro y hy
  exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (Real.sqrt y - K), Real.sq_sqrt hy])


private theorem firstPrime_measurable_cutoff (H : ℝ → ℂ) (hH : Measurable H) (v : ℝ)
    (c : ℕ → ℂ) (p : ℕ → Prop) [DecidablePred p] :
    Measurable (fun y : ℝ ↦ ∑ n ∈ Finset.Ioc 0 ⌊Real.exp (y + v)⌋₊ with p n,
      c n * firstPrimeShellWeight H y n) := by
  let S (z : ℝ × ℕ) := ∑ n ∈ Finset.Ioc 0 z.2 with p n, c n * firstPrimeShellWeight H z.1 n
  have hm : Measurable S := measurable_from_prod_countable_left fun N ↦ by
    change Measurable (fun y : ℝ ↦ ∑ n ∈ (Finset.Ioc 0 N).filter p, c n * firstPrimeShellWeight H y n)
    apply Finset.measurable_fun_sum
    intro n _
    exact measurable_const.mul ((hH.comp (measurable_const.sub measurable_id)).div measurable_const)
  exact hm.comp (measurable_id.prodMk ((Real.measurable_exp.comp (measurable_id.add_const v)).nat_floor))

private theorem firstPrime_polarMoment_measurable (ψ : U) (H : ℝ → ℂ) (s : ℂ) :
    Measurable (fun y : ℝ ↦ firstPrimePolarMoment ψ H y s) := by
  by_cases h : ψ = 1
  · simp only [firstPrimePolarMoment, ite_eq_left h]
    fun_prop
  · simp only [firstPrimePolarMoment, ite_eq_right h]
    exact measurable_const

/-- Every integrable weight on the positive half-line gives the same absolute-integrability
criterion for the centered degree-one sum and the signed geometric expression. The chosen
families of Bruhat tests and local restrictions need no measurability hypotheses. -/
theorem firstPrime_integrableOn_weight_iff (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ (ideleClassNorm F))
    (ψ : U) (hψ : ∀ t, ψ (τ t) = 1) (H : ℝ → ℂ) (hH : Continuous H) {u v : ℝ}
    (hu : 0 < u) (huv : u ≤ v) (hs : tsupport H ⊆ Icc u v) (φ : ℝ → BruhatCompactSupport G)
    (hφ : ∀ y ≥ (0 : ℝ), ∀ g, (φ y).val g = (ψ g : ℂ) * H (Real.log normAt(g) - y))
    (A : ℝ → archTest) (B : ℝ → finiteTest)
    (hA : ∀ y ≥ (0 : ℝ), ∀ w t, (A y w).val t = (φ y).val (archClass(w) t))
    (hB : ∀ y ≥ (0 : ℝ), ∀ w t, (B y w).val t = (φ y).val (finiteClass(w) t))
    (weight : ℝ → ℝ) (hw : IntegrableOn weight (Ici 0)) :
    IntegrableOn (fun y ↦ weight y * ‖firstPrimeDegreeOneSum ψ⁻¹ H y v -
      firstPrimePolarMoment ψ H y (1/2)‖) (Ici 0) ↔
    IntegrableOn (fun y ↦ weight y * ‖firstPrimeLocalTerms (φ y) (A y) (B y)‖) (Ici 0) := by
  let μ := volume.restrict (Ici (0 : ℝ))
  let P (y : ℝ) := firstPrimeDegreeOneSum ψ⁻¹ H y v - firstPrimePolarMoment ψ H y (1/2)
  let G₀ (y : ℝ) := firstPrimeLocalTerms (φ y) (A y) (B y)
  let L (y : ℝ) := G₀ y / (normOneMass : ℂ)
  have hp : Measurable (fun y ↦ firstPrimeDegreeOneSum ψ⁻¹ H y v) := by
    exact firstPrime_measurable_cutoff H hH.measurable v _ Nat.Prime
  have hq : Measurable (fun y ↦ firstPrimeHigherPowers ψ⁻¹ H y v) := by
    exact firstPrime_measurable_cutoff H hH.measurable v _ (fun n ↦ IsPrimePow n ∧ ¬ n.Prime)
  have hP : AEStronglyMeasurable P μ :=
    (hp.sub (firstPrime_polarMoment_measurable ψ H (1/2))).aestronglyMeasurable
  have hsum : AEMeasurable (fun y ↦ ∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (A y w)) μ :=
    Finset.aemeasurable_fun_sum _ fun w _ ↦ FirstPrimeArch.translated_principalValue_aemeasurable
      w ψ H hH.measurable hu (fun x hx ↦ image_eq_zero_of_notMem_tsupport fun h ↦ hx (hs h))
      (fun y ↦ A y w) (fun y hy t ↦ (hA y hy w t).trans (hφ y hy _))
  have hG : AEMeasurable G₀ μ := by
    apply (aemeasurable_const.mul (((((firstPrime_polarMoment_measurable ψ H (1/2)).aemeasurable.add
      (firstPrime_polarMoment_measurable ψ H (-1/2)).aemeasurable).sub hsum).sub hp.aemeasurable).sub
      hq.aemeasurable)).congr
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ici] with y hy
    exact (firstPrime_localTerms_eq τ hτ ψ hψ H hu hs hy (φ y) (hφ y hy) (A y) (B y) (hB y hy)).symm
  have hL : AEStronglyMeasurable L μ := (hG.div_const _).aestronglyMeasurable
  obtain ⟨C, _, hC⟩ := firstPrime_centered_localTerms_uniform τ hτ ψ hψ H hH hu huv hs
  have hd : ∀ᵐ y ∂μ, |‖P y‖ - ‖L y‖| ≤ C := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ici] with y hy
    have h := (abs_norm_sub_norm_le (P y) (-(L y))).trans
      (by simpa only [sub_neg_eq_add] using hC y hy (φ y) (hφ y hy) (A y) (B y) (hA y hy) (hB y hy))
    simpa only [norm_neg] using h
  have hdiff : Integrable (fun y ↦ weight y * (‖P y‖ - ‖L y‖)) μ := by
    apply (hw.norm.mul_const C).mono' (hw.aestronglyMeasurable.mul (hP.norm.sub hL.norm))
    filter_upwards [hd] with y hy
    change ‖weight y * (‖P y‖ - ‖L y‖)‖ ≤ ‖weight y‖ * C
    simpa only [Real.norm_eq_abs, abs_mul] using (mul_le_mul_of_nonneg_left hy (abs_nonneg (weight y)))
  have hsplit := integrable_add_iff_integrable_right' (g := fun y ↦ weight y * ‖L y‖) hdiff
  have heq : (fun y ↦ weight y * (‖P y‖ - ‖L y‖) + weight y * ‖L y‖) =
      (fun y ↦ weight y * ‖P y‖) := funext fun y ↦ by ring
  rw [heq] at hsplit
  have hV := firstPrime_volume_pos (F := F)
  have hh (y : ℝ) : weight y * ‖L y‖ = (normOneMass)⁻¹ * (weight y * ‖G₀ y‖) := by
    rw [show ‖L y‖ = ‖G₀ y‖ / normOneMass by
      simp only [L, norm_div, Complex.norm_real, Real.norm_of_nonneg hV.le], div_eq_mul_inv]
    ring
  exact hsplit.trans (by simp only [hh]; exact integrable_const_mul_iff (inv_ne_zero hV.ne').isUnit _)

end RiemannMasullo
