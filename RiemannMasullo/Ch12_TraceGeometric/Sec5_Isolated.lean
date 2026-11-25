module
import RiemannMasullo.AppB_AnalyticNT.Sec2
import RiemannMasullo.AppB_AnalyticNT.Sec4b
import RiemannMasullo.AppB_AnalyticNT.Sec6
import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.ForMathlib.Analysis.Complex.ExpSumLogarithmicRegion
import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace

public import RiemannMasullo.Ch12_TraceGeometric.Sec5

/-! # Isolated statements of §12.5

Statements of the section that are neither proved nor refuted and that nothing else in Lean
uses, with what follows from them (`AGENTS.md`, "False statements and gaps"). Nothing imports
this file.

## The projective strip kernel needed for (12.5.1.4)

The first theorem supplies the kernel hypothesis of the smoothened diagonal formula in §12.5.
The second theorem specializes that formula to this kernel.
-/

@[expose] public noncomputable section

open MeasureTheory NumberField Set
open scoped NNReal

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
local notation "hs₁(" hs ")" => (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 3) hs)
local notation "hs₀(" hs ")" => (zero_lt_one.trans hs₁(hs)).le

/-- Paper: (12.5.1.4), p. 520. For a test vanishing on the norm-one classes, a projective
Sobolev tensor represents convolution by the test after spectral projection at twist 1/2.
Reconstruction: Definition 10.4.3.7(2), p. 473, subtracts the spectral kernel. Using this
subtraction on p. 520 presupposes a tensor for the operator in (10.4.3.45).
Deviation: We ask for any representing tensor, restricted to the positive half-widths and
tests of Theorem 12.5.1.1. We impose no finite-rank expansion on the tensor.
Gap: The projective norm estimate for the geometric component of the output is missing.
Nothing in the Lean uses this statement, and it is not known how it connects with the rest of
the proof in Lean; in the paper it is used on pp. 520, 522. -/
theorem exists_projectiveKernel_stripTestAction_spectralProjection
    (φ : BruhatCompactSupport C𝔽) (_hφ : ∀ g : C₁, φ.val g = 0)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s) :
    ∃ K, sobolevProjectiveKernelOperator (F := F) hα.le hs₀(hs) K =
      (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s ((neg_nonpos.mpr hα.le).trans hα.le) hs₀(hs) φ).comp
        (spectralProjection (F := F) (1 / 2) hα.le hs₀(hs)) := by
  sorry

section PositiveTranslations

/-! ### Endpoint estimates for signed positive translates

The expansion of #7518 uses the inverse of the chosen normalized character.
The norm-one volume multiplies the local principal values in the full
functional of Theorem B.4.4.7, p. 623. The endpoint estimates below apply
for each fixed field and character, including the principal character.

mlyle observed a fixed square-root saving from the classical zero-free region
in [#5571](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7147625073).
Here arbitrary smoothness gives every fixed multiple of the square root.
The smoothed rational prime-shell asymptotic is in #7527, and a sharper
estimate for the principal rational Fabius profile is in [the endpoint discussion](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7149346245).
mlyle’s earlier rational theta probes used quadratically decreasing interval
widths. The last estimate accepts a transform bound for a profile on the centered strip.
-/

open Filter Function IsDedekindDomain
open scoped Asymptotics ContDiff Topology

attribute [local instance] instFiniteCompletionUnitsLocallyCompactSec4b

local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "zeros(" χ ")" =>
  {s : ℂ // 0 < MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ s}

/-- The log-coordinate coefficient of Proposition B.2.1.9, p. 598, with a
polynomial weight valid also on the real axis of a closed vertical strip. -/
private theorem bilateralLaplace_rapidDecay_on_closedStrip
    (H : ℝ → ℂ) (hs : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    {a b : ℝ} (hab : a < b) (n : ℕ) :
    ∃ C > (0 : ℝ), ∀ w : ℂ, w.re ∈ Icc a b →
      ‖bilateralLaplace H w‖ * (1 + |w.im|) ^ n ≤ C := by
  let f : _root_.SchwartzMap ℝ ℂ := hc.toSchwartzMap hs
  have hz (j : ℕ) : iteratedDeriv j H =ᶠ[cocompact ℝ] 0 := by
    have hh := hc.iteratedFDeriv (𝕜 := ℝ) j
    rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact] at hh
    filter_upwards [hh] with x hx
    rw [iteratedDeriv_eq_iteratedFDeriv, hx]
    rfl
  have hf : ExponentialDecay f :=
    ⟨fun j _ _ ↦ ((hz j).filter_mono atTop_le_cocompact).trans_isBigO
      (Asymptotics.isBigO_zero _ _), fun j _ _ ↦ ((hz j).filter_mono atBot_le_cocompact).trans_isBigO
      (Asymptotics.isBigO_zero _ _)⟩
  let Φ := mellin (fun t ↦ H (Real.log t))
  have heq (w : ℂ) : Φ w = bilateralLaplace H w := by
    change mellin (fun t ↦ H (Real.log t)) w = _
    rw [mellin, ← integral_comp_exp]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp,
      ← mul_assoc, ← Complex.exp_add, mul_comm]
    congr 1
    ring_nf
  obtain ⟨A, hA, hlarge⟩ := mellin_heightBound_of_exponentialDecay f hf a b hab
    (n + 1) (Nat.succ_pos _)
  have hΦ : Continuous Φ := (differentiable_mellin_of_exponentialDecay f hf).continuous
  obtain ⟨B, hsmall⟩ := (isCompact_Icc.reProdIm isCompact_Icc :
    IsCompact (Complex.reProdIm (Icc a b) (Icc (-1 : ℝ) 1))).exists_bound_of_continuousOn
      hΦ.continuousOn
  refine ⟨max A B * 2 ^ n, mul_pos (hA.trans_le (le_max_left _ _)) (by positivity), ?_⟩
  intro w hw
  rw [← heq]
  by_cases ht : 1 ≤ |w.im|
  · have hpos : 0 < |w.im| := zero_lt_one.trans_le ht
    have hd := hlarge w.re hw w.im (abs_pos.mp hpos)
    simp only [Complex.re_add_im] at hd
    have hwgt : (1 + |w.im|) ^ n ≤ 2 ^ n * |w.im| ^ (n + 1) := by
      calc (1 + |w.im|) ^ n ≤ (2 * |w.im|) ^ n :=
             pow_le_pow_left₀ (by positivity) (by linarith) n
        _ ≤ _ := by rw [mul_pow]; gcongr; exact Nat.le_succ n
    calc
      ‖Φ w‖ * (1 + |w.im|) ^ n ≤ ‖Φ w‖ * (2 ^ n * |w.im| ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left hwgt (norm_nonneg _)
      _ = (‖Φ w‖ * |w.im| ^ (n + 1)) * 2 ^ n := by ring
      _ ≤ max A B * 2 ^ n := mul_le_mul_of_nonneg_right
        (((le_div_iff₀ (pow_pos hpos _)).mp hd).trans (le_max_left _ _)) (by positivity)
  · have hmem : w ∈ Complex.reProdIm (Icc a b) (Icc (-1 : ℝ) 1) :=
      Complex.mem_reProdIm.mpr ⟨hw, abs_le.mp (not_le.mp ht).le⟩
    apply mul_le_mul ((hsmall w hmem).trans (le_max_right _ _))
      (pow_le_pow_left₀ (by positivity) (by linarith [not_le.mp ht]) n) (by positivity)
    exact (le_of_lt hA).trans (le_max_left _ _)

private theorem translatedLocalTerms_characterZero_order (χ : U) (z : zeros(χ)) :
    0 < meromorphicOrderAt (continuedCompletedHeckeL χ) z.val := by
  have hz := z.property
  rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec χ).1.meromorphicOn
    (mem_univ _)] at hz
  cases he : meromorphicOrderAt (continuedCompletedHeckeL χ) z.val with
  | top => simp
  | coe k =>
    rw [he, WithTop.untop₀_coe] at hz
    exact_mod_cast hz

/-- Replacing the scaled logarithm of Proposition B.6.1.1 by 1 + log(1 + |t|)
costs only a constant depending on the field and character. -/
private theorem translatedLocalTerms_logarithmicZeroGap (χ : U) :
    ∃ c > (0 : ℝ), ∀ z : zeros(χ),
      z.val.re ≤ 1 - c / (1 + Real.log (1 + |z.val.im|)) := by
  obtain ⟨A, hA, hF⟩ := finiteHeckeL_zeroFreeRegion
  obtain ⟨B, hB, hregion⟩ := hF F χ
  obtain ⟨L, hL, hseries⟩ := finiteHeckeL_exists_continuation χ
  let D := (Module.finrank ℚ F : ℝ) ^ 4
  let C := 1 + Real.log (3 * B)
  have hBpos : 0 < B := by linarith
  have hD : 0 < D := pow_pos (by exact_mod_cast Module.finrank_pos) _
  have hLB : 0 < Real.log (3 * B) := Real.log_pos (by linarith)
  have hC : 0 < C := by dsimp [C]; linarith
  let c := min 1 (A / (D * C))
  refine ⟨c, lt_min zero_lt_one (div_pos hA (mul_pos hD hC)), ?_⟩
  intro z
  let t := |z.val.im|
  have ht : 0 ≤ t := abs_nonneg _
  have hu : 0 < B * (t + 3) := by positivity
  have hv : 0 < 1 + t := by positivity
  have hr : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
  have hlog : 0 < Real.log (B * (t + 3)) :=
    Real.log_pos (by nlinarith [mul_nonneg hBpos.le ht])
  have hcomp : Real.log (B * (t + 3)) ≤ C * (1 + Real.log (1 + t)) := by
    calc
      Real.log (B * (t + 3)) ≤ Real.log ((3 * B) * (1 + t)) :=
        Real.log_le_log hu (by nlinarith [mul_nonneg hBpos.le ht])
      _ = Real.log (3 * B) + Real.log (1 + t) := Real.log_mul (by positivity) hv.ne'
      _ ≤ C * (1 + Real.log (1 + t)) := by
        dsimp only [C]
        nlinarith [mul_nonneg hLB.le hr]
  have hrpos : 0 < 1 + Real.log (1 + t) := by linarith
  by_cases hs : 0 < z.val.re
  case neg =>
    have hquot : c / (1 + Real.log (1 + t)) ≤ 1 :=
      (div_le_iff₀ hrpos).mpr (by rw [one_mul]; exact (min_le_left _ _).trans (by linarith))
    change z.val.re ≤ 1 - c / (1 + Real.log (1 + t))
    linarith
  have hleft : z.val.re < 1 - A / (D * Real.log (B * (t + 3))) := by
    apply lt_of_not_ge
    intro hz
    have hn := hregion L hL hseries z.val hz
    rw [meromorphicOrderAt_finiteHeckeL_continuation χ hL.meromorphicOn hseries hs] at hn
    exact hn.not_gt (translatedLocalTerms_characterZero_order χ z)
  refine hleft.le.trans (sub_le_sub_left ?_ 1)
  refine (div_le_div_of_nonneg_right (min_le_right 1 (A / (D * C))) hrpos.le).trans ?_
  change A / (D * C) / (1 + Real.log (1 + t)) ≤ A / (D * Real.log (B * (t + 3)))
  rw [div_div, mul_assoc]
  exact div_le_div_of_nonneg_left hA.le (mul_pos hD hlog) (mul_le_mul_of_nonneg_left hcomp hD.le)

local notation "V" => IsDedekindDomain.HeightOneSpectrum (𝓞 F)
local notation "M(" φ ", " c ")" =>
  modulatedFourierMellin m𝔽 univ ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
    μ𝔽 (φ : BruhatCompactSupport C𝔽).val c
local notation "twist(" χ ", " s ")" => ideleClassNormTwist (F := F) χ s
local notation "ord(" χ ", " z ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "vol₁" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "archTest" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest" => ((v : V) → BruhatCompactSupport (v.adicCompletion F)ˣ)
local notation "archRestricts(" φ ", " a ")" =>
  (∀ (w : InfinitePlace F) (u : w.Completionˣ), (a w).val u =
    (φ : BruhatCompactSupport C𝔽).val (IdeleClassGroup.ofCompletion (𝓞 F) F w u))
local notation "finiteRestricts(" φ ", " b ")" =>
  (∀ (v : V) (u : (v.adicCompletion F)ˣ), (b v).val u =
    (φ : BruhatCompactSupport C𝔽).val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u))
local notation "finiteTerm(" v ", " b ")" =>
  ((Real.log ((v : V).asIdeal.absNorm : ℝ) /
    (finiteLocalMultiplicativeTamagawaMeasure F v
      ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal : ℝ) : ℂ) *
    finiteConnesWeilPrincipalValue v 1 b
local notation "localTerms(" φ ", " a ", " b ")" =>
  (M(φ, twist(1, 1 / 2)) + M(φ, twist(1, -1 / 2)) -
    vol₁ * ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
      ∑' v : V, finiteTerm(v, b v)))
local notation "coef(" χ ", " H ", " z ")" =>
  ((ord(χ, (z : ℂ)) : ℤ) : ℂ) * (vol₁ * bilateralLaplace H ((z : ℂ) - 1 / 2))
local notation "mass(" χ ", " z ")" =>
  (ord(χ, (z : ℂ)) : ℝ) / (1 + |(z : ℂ).im|) ^ 2

private theorem translatedLocalTerms_coef_bound (χ : U) (H : ℝ → ℂ)
    (hs : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) (n : ℕ) :
    ∃ B > (0 : ℝ), ∀ z : zeros(χ),
      ‖coef(χ, H, z)‖ * (1 + |z.val.im|) ^ n ≤ B * mass(χ, z) := by
  obtain ⟨A, hA, h⟩ := bilateralLaplace_rapidDecay_on_closedStrip H hs hc
    (a := -(1 / 2)) (b := 1 / 2) (by norm_num) (n + 2)
  refine ⟨(‖vol₁‖ + 1) * A, mul_pos (by positivity) hA, ?_⟩
  intro z
  let x := 1 + |z.val.im|
  have hx : 0 < x := by dsimp only [x]; positivity
  have hz := explicitFormulaCompletedHeckeL_zero_re_mem χ z.property
  have hre : (z.val - 1 / 2).re ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    constructor <;> linarith [hz.1, hz.2]
  have hb : ‖bilateralLaplace H (z.val - 1 / 2)‖ * x ^ (n + 2) ≤ A := by
    simpa [x] using h (z.val - 1 / 2) hre
  have hm : (0 : ℝ) ≤ (ord(χ, z.val) : ℝ) := by exact_mod_cast z.property.le
  rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hm, norm_mul]
  change _ ≤ _ * (_ / x ^ 2)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (pow_pos hx _)).mpr
  calc
    _ = (ord(χ, z.val) : ℝ) * ‖vol₁‖ * (‖bilateralLaplace H (z.val - 1 / 2)‖ * x ^ (n + 2)) := by
      rw [pow_add]
      change (ord(χ, z.val) : ℝ) * (_ * _) * x ^ n * x ^ 2 = _
      ring
    _ ≤ (ord(χ, z.val) : ℝ) * ‖vol₁‖ * A := mul_le_mul_of_nonneg_left hb (mul_nonneg hm (norm_nonneg _))
    _ ≤ _ := by nlinarith [mul_nonneg hm hA.le]

/-- Paper: Theorem B.4.4.7, p. 623, and Proposition B.6.1.1, p. 636, for
the positive log translations of Theorem 12.5.1.1, pp. 519–520.
For each fixed normalized character and compact smooth radial profile, the full
signed local functional admits every fixed root-exponential saving at the
horizontal exponent one half. It includes both polar Mellin terms and the
negative of the norm-one volume times the sum of local principal values. -/
theorem translatedLocalTerms_norm_le_exp_sub_sqrt (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (ψ : PontryaginDual C𝔽) (hψ : ∀ t, ψ (τ t) = 1)
    (H : ℝ → ℂ) (hs : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) (K : ℝ) :
    ∃ D ≥ (0 : ℝ), ∀ (y : ℝ), 0 ≤ y → ∀ (φ : BruhatCompactSupport C𝔽),
      (∀ x, φ.val x = (ψ x : ℂ) * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y)) →
      ∀ (a : archTest) (b : finiteTest), archRestricts(φ, a) → finiteRestricts(φ, b) →
        ‖localTerms(φ, a, b)‖ ≤ D * Real.exp (y / 2 - K * Real.sqrt y) := by
  obtain ⟨c, hc', hgap⟩ := translatedLocalTerms_logarithmicZeroGap (ψ⁻¹)
  have hat := expSum_norm_le_exp_sub_sqrt
    (fun z : zeros(ψ⁻¹) ↦ z.val) (fun z ↦ coef(ψ⁻¹, H, z)) (fun z ↦ mass(ψ⁻¹, z))
    (explicitFormulaCompletedHeckeL_summable_divisor_div_sq _)
    (fun z ↦ div_nonneg (by exact_mod_cast z.property.le) (by positivity))
    hc' hgap (translatedLocalTerms_coef_bound (ψ⁻¹) H hs hc) K
  obtain ⟨D, hD, hbound⟩ := hat
  exact ⟨D, hD, fun y hy φ hφ a b ha hb ↦ hbound hy (translatedLocalTerms_hasSum τ hτ ψ hψ H hs hc y φ hφ a b ha hb)⟩

/-- For any fixed real k, the endpoint weight permits the further factor
exp(k √y). This holds for every choice of actual Bruhat representatives of the
positive translates and their finite and archimedean restrictions. -/
theorem translatedLocalTerms_integrableOn_exp_sqrt (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (ψ : PontryaginDual C𝔽) (hψ : ∀ t, ψ (τ t) = 1)
    (H : ℝ → ℂ) (hs : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    (φ : ℝ → BruhatCompactSupport C𝔽)
    (hφ : ∀ y : ℝ, 0 ≤ y → ∀ x, (φ y).val x =
      (ψ x : ℂ) * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y))
    (a : ℝ → archTest) (b : ℝ → finiteTest)
    (ha : ∀ y : ℝ, 0 ≤ y → archRestricts(φ y, a y))
    (hb : ∀ y : ℝ, 0 ≤ y → finiteRestricts(φ y, b y)) (k : ℝ) :
    IntegrableOn (fun y : ℝ ↦ ‖localTerms(φ y, a y, b y)‖ *
      Real.exp (-y / 2 + k * Real.sqrt y)) (Ici 0) := by
  apply integrableOn_expSum_exp_sqrt_of_bounds (fun z : zeros(ψ⁻¹) ↦ z.val)
    (fun z ↦ coef(ψ⁻¹, H, z)) (fun y ↦ localTerms(φ y, a y, b y))
    (fun z ↦ (explicitFormulaCompletedHeckeL_zero_re_mem (ψ⁻¹) z.property).2) ?_ ?_ ?_ k
  · have h := (translatedLocalTerms_hasSum τ hτ ψ hψ H hs hc 0 (φ 0) (hφ 0 le_rfl)
      (a 0) (b 0) (ha 0 le_rfl) (hb 0 le_rfl)).summable.norm
    simpa only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, bilateralLaplace] using h
  · intro y hy
    exact translatedLocalTerms_hasSum τ hτ ψ hψ H hs hc y (φ y) (hφ y hy)
      (a y) (b y) (ha y hy) (hb y hy)
  · intro K
    obtain ⟨D, hD, h⟩ := translatedLocalTerms_norm_le_exp_sub_sqrt τ hτ ψ hψ H hs hc K
    exact ⟨D, hD, fun y hy ↦ h y hy (φ y) (hφ y hy) (a y) (b y) (ha y hy) (hb y hy)⟩

/-- A square-root exponential height bound on the bilateral Laplace transform
improves the positive-translate saving to d*y/log(2+y) for the same local
functional. The constant d depends on the fixed field, character and profile. -/
theorem translatedLocalTerms_norm_le_exp_sub_div_log (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (ψ : PontryaginDual C𝔽) (hψ : ∀ t, ψ (τ t) = 1)
    (H : ℝ → ℂ) (hs : ContDiff ℝ ∞ H) (hc : HasCompactSupport H)
    {κ A : ℝ} (hκ : 0 < κ) (hA : 0 < A)
    (hH : ∀ w : ℂ, w.re ∈ Icc (-(1 / 2) : ℝ) (1 / 2) →
      ‖∫ x : ℝ, H x * Complex.exp (w * x)‖ ≤ A * Real.exp (-κ * Real.sqrt |w.im|)) :
    ∃ d > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ (y : ℝ), 0 ≤ y → ∀ (φ : BruhatCompactSupport C𝔽),
      (∀ x, φ.val x = (ψ x : ℂ) * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y)) →
      ∀ (a : archTest) (b : finiteTest), archRestricts(φ, a) → finiteRestricts(φ, b) →
        ‖localTerms(φ, a, b)‖ ≤ C * Real.exp (y / 2 - d * y / Real.log (2 + y)) := by
  obtain ⟨c, hc', hgap⟩ := translatedLocalTerms_logarithmicZeroGap (ψ⁻¹)
  let B := (‖vol₁‖ + 1) * A
  have hB : 0 < B := mul_pos (by positivity) hA
  have hamp (z : zeros(ψ⁻¹)) : ‖coef(ψ⁻¹, H, z)‖ ≤ B * mass(ψ⁻¹, z) * (1 + |z.val.im|) ^ 2 *
      Real.exp (-κ * Real.sqrt |z.val.im|) := by
    let m : ℝ := ord(ψ⁻¹, z.val)
    let x := 1 + |z.val.im|
    let E := Real.exp (-κ * Real.sqrt |z.val.im|)
    have hx : 0 < x := by dsimp [x]; positivity
    have hm : 0 ≤ m := by dsimp only [m]; exact_mod_cast z.property.le
    have he : 0 ≤ E := (Real.exp_pos _).le
    have hz := explicitFormulaCompletedHeckeL_zero_re_mem (ψ⁻¹) z.property
    have hre : (z.val - 1 / 2).re ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := by
      simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
      constructor <;> linarith [hz.1, hz.2]
    have hcoeff : ‖bilateralLaplace H (z.val - 1 / 2)‖ ≤ A * E := by
      simpa [bilateralLaplace, E] using hH _ hre
    rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hm, norm_mul]
    change m * (‖vol₁‖ * _) ≤ B * (m / x ^ 2) * x ^ 2 * E
    calc
      _ ≤ m * (‖vol₁‖ * (A * E)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcoeff (norm_nonneg _)) hm
      _ ≤ m * ((‖vol₁‖ + 1) * (A * E)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hA.le he)) hm
      _ = _ := by dsimp only [B]; field_simp [hx.ne']
  obtain ⟨d, hd, C, hC, h⟩ := expSum_norm_le_exp_sub_div_log (fun z : zeros(ψ⁻¹) ↦ z.val)
    (fun z ↦ coef(ψ⁻¹, H, z)) (fun z ↦ mass(ψ⁻¹, z))
    (explicitFormulaCompletedHeckeL_summable_divisor_div_sq _)
    (fun z ↦ div_nonneg (by exact_mod_cast z.property.le) (by positivity))
    hc' hκ hB hgap hamp
  exact ⟨d, hd, C, hC, fun y hy φ hφ a b ha hb ↦ h y hy _
    (translatedLocalTerms_hasSum τ hτ ψ hψ H hs hc y φ hφ a b ha hb)⟩

end PositiveTranslations

/-- Paper: (12.5.1.4), p. 520. The smoothened geometric diagonal is Haar-integrable, and the
strip zero terms sum absolutely to its negative integral.
Deviation: As in §12.5 of the library, a measurable D′-sequence specifies the smoothening,
and the sum uses the closed strip with strict reciprocal-weight multiplicities on its edges.
It agrees with the printed interior sum when both edges are zero-free.
It is proved from the kernel existence statement above, which is open, so it is no more
established than that statement. Nothing in the Lean uses it. -/
theorem hasSum_stripZeros_neg_integral_smoothenedDiagonal_of_vanishing
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ g : C₁, φ.val g = 0)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    {α s : ℝ} (hα : 0 < α) (hs : 3 ≤ s)
    (U : ℕ → Set C𝔽) (hU : IsDPrimeSequence μ𝔽 U) (hBorel : ∀ n, MeasurableSet (U n)) :
    let hK := exists_projectiveKernel_stripTestAction_spectralProjection φ hφ hα hs
    let diagonal (x : C𝔽) := dSequenceKernelSmoothening μ𝔽 U
      (globalStripGeometricKernel (F := F) (1 / 2) hα.le hs₁(hs) φ hK) (x, x)
    let shift (b t : ℝ) := (b : ℂ) + (t : ℂ) * Complex.I
    let order (η : PontryaginDual C𝔽) := meromorphicOrderAt (continuedCompletedHeckeL η)
    let Z := {z : PontryaginDual C₁ × ℝ × ℝ //
      z.2.1 ∈ Icc (-α) α ∧ 0 < order (χ z.1) (shift (1 / 2 + z.2.1) z.2.2)}
    let term (z : Z) := ((spectralStripMultiplicity α s z.val.2.1
      (order (χ z.val.1) (shift (1 / 2 + z.val.2.1) z.val.2.2)).untop₀.toNat : ℕ) : ℂ) *
      modulatedFourierMellin m𝔽 univ ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
        μ𝔽 φ.val (ideleClassNormTwist (χ z.val.1) (shift z.val.2.1 z.val.2.2))
    Integrable diagonal μ𝔽 ∧ Summable (fun z ↦ ‖term z‖) ∧
      HasSum term (-(∫ x, diagonal x ∂μ𝔽)) :=
  hasSum_stripZeros_neg_integral_smoothenedDiagonal φ hφ χ hχ hα hs
    (exists_projectiveKernel_stripTestAction_spectralProjection φ hφ hα hs) U hU hBorel

end RiemannMasullo.Isolated
