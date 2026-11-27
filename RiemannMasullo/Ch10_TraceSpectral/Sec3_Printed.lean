module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
import RiemannMasullo.Ch03_IdelicZeta.Sec4
import RiemannMasullo.Ch06_LocalGlobal.Sec3
import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.DirichletZeros
import RiemannMasullo.External.AlgebraicNumberTheoryLean.Chebotarev.DirichletHecke
public import RiemannMasullo.External.HardyCriticalLine.HardyFunctionNormalization
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.RingTheory.Binomial
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.Real.Pi.Bounds
import RiemannMasullo.External.HardyCriticalLine.LowerIntegralBound
import RiemannMasullo.External.HardyCriticalLine.UpperIntegralBound
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.LSeries.HardyZ
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # §10.3 assertions that are false as printed -/

@[expose] public noncomputable section

open Function MeasureTheory NumberField Set
open scoped NNReal

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "m𝔽(" F ")" =>
  (continuousIdeleClassNorm F : C𝔽(F) →ₜ* ℝ≥0ˣ)
local notation "h₀" => le_rfl (a := (0 : ℝ))
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "Wω(" F ", " l ", " r ", " s ", " hI ", " hs ", " ω ")" =>
  actionIsotype ((hardySobolevTranslation (ideleClassTamagawaMeasure F) m𝔽(F) l r s hI hs).comp
    (ideleClassNorm F).ker.subtype) ω

local notation "μ𝔽(" F ")" => ideleClassTamagawaMeasure F
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "orderAt(" F ", " χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "mellinAt(" F ", " φ ", " χ ", " z ")" =>
  ∫ g, (φ : BruhatCompactSupport C𝔽(F)).val g * ideleClassNormTwist (F := F) χ z g ∂μ𝔽(F)

local notation "printedMultiplicity(" F ", " χ ", " a ", " s ", " t ")" =>
  min ((meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ)
    ((a : ℂ) + (t : ℂ) * Complex.I)).untop₀.toNat) (Nat.floor ((s - 1) / 2 + 1))

/-- Paper: (10.3.1.18), p. 451. The products of jet norms and biorthogonal
vector norms within each zero block have a single bound across all blocks.
The family consists of all orders selected by the printed floor cutoff. -/
def Printed.spectralLineJet_uniformBiorthogonalBound : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)),
    IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω) →
    ∀ (a s : ℝ) (hs : 1 < s),
      let J := {j : PontryaginDual C₁(F) × ℝ × ℕ //
        j.2.2 < printedMultiplicity(F, χ j.1, a, s, j.2.1)}
      let Q := spectralSobolevQuotient F a h₀ hs₀(hs)
      let D := spectralSobolevDualEmbedding F a h₀ hs₀(hs)
      let w := (ideleClassTamagawaMeasure F).withDensity fun g : C𝔽(F) ↦
        ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log ((ideleClassNorm F g).val : ℝ)))⁻¹
      ∀ (x : J → Q) (Λ : J → StrongDual ℂ Q), IsSpectralMarkushevichBasis x Λ →
        (∀ j, let η := spectralZeroJet (F := F) (χ j.val.1) 0 j.val.2.1 j.val.2.2
          ∃ h : MemLp η 2 w, D (Λ j) = h.toLp η) →
        ∃ C : ℝ, 0 < C ∧ ∀ i j : J,
          i.val.1 = j.val.1 → i.val.2.1 = j.val.2.1 → j.val.2.2 ≤ i.val.2.2 →
          ‖D (Λ j)‖ * ‖x i‖ ≤ C

section SelbergBulk

open HardyCriticalLine

local notation "mode(" n ", " t ")" => (((n : ℕ) : ℂ) ^ (-criticalLinePoint t))
local notation "poly(" N ", " b ", " t ")" =>
  (∑ n ∈ Finset.Icc 1 N, ((b n : ℝ) : ℂ) * mode(n, t))

/-- The contribution of one mode to a dyadic mean after removing its constant term. -/
private theorem spectralLineJet_centered_mode {n : ℕ} (hn : 0 < n) (T : ℝ) :
    ‖(∫ t in T..2 * T, mode(n, t)) - (if n = 1 then (T : ℂ) else 0)‖ ≤
      4 / Real.sqrt n := by
  by_cases h : n = 1
  · subst n
    simp [two_mul, sub_eq_add_neg]
  · simpa [h] using norm_integral_cpow_neg_criticalLinePoint_le (n := n) (by omega) T

/-- Uniform pointwise control for all coefficient choices of a finite mollifier. -/
private theorem spectralLineJet_mollifier_norm (N : ℕ) (b : ℕ → ℝ)
    (hb : ∀ n ∈ Finset.Icc 1 N, |b n| ≤ 1) (t : ℝ) :
    ‖poly(N, b, t)‖ ≤ 2 * Real.sqrt N := by
  calc _ ≤ ∑ n ∈ Finset.Icc 1 N, ‖((b n : ℝ) : ℂ) * mode(n, t)‖ := norm_sum_le _ _
       _ ≤ ∑ n ∈ Finset.Icc 1 N, 1 / Real.sqrt n := by
         refine Finset.sum_le_sum fun n h ↦ ?_
         rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cpow_neg_criticalLinePoint (Finset.mem_Icc.mp h).1]
         exact mul_le_of_le_one_left (by positivity) (hb n h)
       _ ≤ _ := sum_Icc_one_div_sqrt_le_two_mul_sqrt N

/-- Integrating a Dirichlet polynomial against a second polynomial squared leaves its
constant coefficient, with error controlled by the three elementary inverse-square-root sums. -/
private theorem spectralLineJet_cutoff_mollified_mean (M N : ℕ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (b : ℕ → ℝ) (hb₁ : b 1 = 1) (hb : ∀ n ∈ Finset.Icc 1 N, |b n| ≤ 1) (T : ℝ) :
    ‖(∫ t in T..2 * T, (∑ k ∈ Finset.Icc 1 M, mode(k, t)) * poly(N, b, t) ^ 2) - (T : ℂ)‖ ≤
      32 * Real.sqrt M * N := by
  classical
  let S := (Finset.Icc 1 M ×ˢ Finset.Icc 1 N) ×ˢ Finset.Icc 1 N
  let n (p : (ℕ × ℕ) × ℕ) := p.1.1 * p.1.2 * p.2
  let B (p : (ℕ × ℕ) × ℕ) : ℂ := (b p.1.2 : ℂ) * (b p.2 : ℂ)
  have hparts {p} (hp : p ∈ S) :=
    (Finset.mem_product.mp (Finset.mem_product.mp hp).1).1
  have hn (p) (hp : p ∈ S) : 0 < n p :=
    Nat.mul_pos (Nat.mul_pos (Finset.mem_Icc.mp (hparts hp)).1
      (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_product.mp hp).1).2).1)
      (Finset.mem_Icc.mp (Finset.mem_product.mp hp).2).1
  have hnorm (p) (hp : p ∈ S) : ‖B p‖ ≤ 1 := by
    dsimp only [B]
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hb _ (Finset.mem_product.mp hp).2)).trans
      (hb _ (Finset.mem_product.mp (Finset.mem_product.mp hp).1).2)
  have hexp (t : ℝ) : (∑ k ∈ Finset.Icc 1 M, mode(k, t)) * poly(N, b, t) ^ 2 =
      ∑ p ∈ S, B p * mode(n p, t) := by
    dsimp only [S, B, n]
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul_sum]
    simp only [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun d _ ↦
      Finset.sum_congr rfl fun e _ ↦ ?_
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  have hint : (∫ t in T..2 * T, (∑ k ∈ Finset.Icc 1 M, mode(k, t)) * poly(N, b, t) ^ 2) =
      ∑ p ∈ S, B p * ∫ t in T..2 * T, mode(n p, t) := by
    simp_rw [hexp]
    rw [intervalIntegral.integral_finsetSum]
    · exact Finset.sum_congr rfl fun p _ ↦ intervalIntegral.integral_const_mul _ _
    · exact fun p hp ↦ (continuous_const.mul (continuous_cpow_neg_criticalLinePoint (hn p hp))).intervalIntegrable ..
  have hdiag : ∑ p ∈ S, B p * (if n p = 1 then (T : ℂ) else 0) = T := by
    rw [Finset.sum_eq_single ((1, 1), 1)]
    · simp [B, n, hb₁]
    · rintro ⟨⟨k, d⟩,e⟩ _ hne
      have h : k * d * e ≠ 1 := by
        intro he
        have split {i j : ℕ} (h : i * j = 1) : i = 1 ∧ j = 1 :=
          ⟨Nat.eq_one_of_dvd_one ⟨j, h.symm⟩, Nat.eq_one_of_dvd_one ⟨i, by simpa [Nat.mul_comm] using h.symm⟩⟩
        obtain ⟨hkd, he⟩ := split he
        obtain ⟨hk, hd⟩ := split hkd
        exact hne (by simp [hk, hd, he])
      simp [n, h]
    · simp [S, hM, hN]
  rw [hint, ← hdiag, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ S, ‖B p * (∫ t in T..2 * T, mode(n p, t)) -
        B p * (if n p = 1 then (T : ℂ) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ S, 4 / Real.sqrt (n p) := by
      refine Finset.sum_le_sum fun p hp ↦ ?_
      rw [← mul_sub, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hnorm p hp)).trans
        (spectralLineJet_centered_mode (hn p hp) T)
    _ = 4 * (∑ k ∈ Finset.Icc 1 M, 1 / Real.sqrt k) *
        (∑ d ∈ Finset.Icc 1 N, 1 / Real.sqrt d) ^ 2 := by
      dsimp only [S, n]
      rw [sq, mul_assoc, Finset.sum_mul_sum, Finset.sum_mul_sum]
      simp only [Finset.sum_product, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun d _ ↦
        Finset.sum_congr rfl fun e _ ↦ ?_
      rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
      ring
    _ ≤ 4 * (2 * Real.sqrt M) * (2 * Real.sqrt N) ^ 2 := by
      gcongr <;> apply sum_Icc_one_div_sqrt_le_two_mul_sqrt
    _ = _ := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]; ring

/-- On dyadic intervals the critical-line mean of ζ times the square of any normalized
finite Dirichlet mollifier of length `N` is `T + O(N √T)`, uniformly in the bounded
coefficients. This is the bulk first-moment step for Selberg's mollified Hardy function,
which enters the classical count supporting the refutation of (10.3.1.18), p. 451. -/
theorem spectralLineJet_mollified_zeta_dyadic_mean :
    ∃ C > (0 : ℝ), ∃ T₀ ≥ (2 : ℝ), ∀ T ≥ T₀, ∀ (N : ℕ) (b : ℕ → ℝ),
      1 ≤ N → b 1 = 1 → (∀ n ∈ Finset.Icc 1 N, |b n| ≤ 1) →
      ‖(∫ t in T..2 * T, riemannZeta (criticalLinePoint t) * poly(N, b, t) ^ 2) - (T : ℂ)‖ ≤
        C * N * Real.sqrt T := by
  obtain ⟨K, hK, T₀, hT₀, happrox⟩ := exists_uniform_zetaFirstApproximation
  refine ⟨4 * K + 32, by positivity, T₀, hT₀, ?_⟩
  intro T hT N b hN hb₁ hb
  have hT₂ := hT₀.trans hT
  have hTpos : 0 < T := by linarith
  have hroot : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTpos
  let M := zetaFirstApproximationCutoff T
  let D (t : ℝ) := ∑ k ∈ Finset.Icc 1 M, mode(k, t)
  let P (t : ℝ) := poly(N, b, t)
  let Z (t : ℝ) := riemannZeta (criticalLinePoint t)
  have hD : Continuous D := continuous_finsetSum _ fun k hk ↦
    continuous_cpow_neg_criticalLinePoint (Finset.mem_Icc.mp hk).1
  have hP : Continuous P := continuous_finsetSum _ fun k hk ↦
    continuous_const.mul (continuous_cpow_neg_criticalLinePoint (Finset.mem_Icc.mp hk).1)
  have hZ : Continuous Z := continuous_riemannZeta_criticalLine
  have hR : ‖∫ t in T..2 * T, (Z t - D t) * P t ^ 2‖ ≤ (4 * K) * N * Real.sqrt T := by
    have H := intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := 2 * T)
      (C := (K / Real.sqrt T) * (2 * Real.sqrt N) ^ 2)
      (f := fun t ↦ (Z t - D t) * P t ^ 2) (fun t ht ↦ by
        rw [uIoc_of_le (by linarith)] at ht
        rw [norm_mul, norm_pow]
        apply mul_le_mul _ (pow_le_pow_left₀ (norm_nonneg _) (spectralLineJet_mollifier_norm N b hb t) 2)
          (by positivity) (by positivity)
        have H₀ := happrox T t hT ht.1.le ht.2
        norm_num [Z, D, M, criticalLinePoint] at H₀ ⊢
        exact H₀)
    refine H.trans_eq ?_
    rw [abs_of_pos (by linarith), mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    field_simp [hroot.ne']
    nlinarith [Real.sq_sqrt hTpos.le]
  have hmain := spectralLineJet_cutoff_mollified_mean M N (one_le_zetaFirstApproximationCutoff hT₂)
    hN b hb₁ hb T
  have hadd : (∫ t in T..2 * T, Z t * P t ^ 2) -
      (∫ t in T..2 * T, D t * P t ^ 2) = ∫ t in T..2 * T, (Z t - D t) * P t ^ 2 := by
    rw [← intervalIntegral.integral_sub (f := fun t ↦ Z t * P t ^ 2) (g := fun t ↦ D t * P t ^ 2)
      ((hZ.mul (hP.pow 2)).intervalIntegrable ..) ((hD.mul (hP.pow 2)).intervalIntegrable ..)]
    simp only [sub_mul]
  change ‖(∫ t in T..2 * T, Z t * P t ^ 2) - (T : ℂ)‖ ≤ _
  calc
    _ ≤ ‖(∫ t in T..2 * T, Z t * P t ^ 2) - (∫ t in T..2 * T, D t * P t ^ 2)‖ +
        ‖(∫ t in T..2 * T, D t * P t ^ 2) - (T : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ (4 * K) * N * Real.sqrt T + 32 * Real.sqrt M * N := by rw [hadd]; exact add_le_add hR hmain
    _ ≤ (4 * K) * N * Real.sqrt T + 32 * Real.sqrt T * N := by
      gcongr
      exact zetaFirstApproximationCutoff_le_height hTpos.le
    _ = _ := by ring

/-- Selberg's gamma-exponential weight on a dyadic interval has a positive uniform
lower bound at its natural height scale. -/
private theorem spectralLineJet_selberg_gamma_dyadic_lower :
    ∃ c > (0 : ℝ), ∀ T ≥ (2 : ℝ), ∀ t ∈ Icc T (2 * T),
      c * (2 * T) ^ (-(1 / 4) : ℝ) ≤ ‖Complex.Gamma (criticalLineGammaArgument t)‖ *
        Real.exp ((Real.pi / 4 - 1 / (4 * T)) * t) := by
  obtain ⟨c, hc, hanchor⟩ := exists_pos_gammaBinetExponentialRatio_at_one
  let A := -(1 / 4) - (1 / 4) * Real.log Real.pi - 2
  refine ⟨c * Real.exp A, by positivity, ?_⟩
  intro T hT t ht
  let z := criticalLineGammaArgument t
  have ht₀ : 0 < t := by linarith [ht.1]
  have hz : 0 < z.re := by rw [criticalLineGammaArgument_re]; norm_num
  have hn : z ≠ 0 := fun h ↦ by rw [h] at hz; exact lt_irrefl _ hz
  have hlog : Real.log ‖z‖ ≤ Real.log (2 * T) := by
    apply Real.log_le_log (norm_pos_iff.mpr hn)
    calc ‖z‖ ≤ ‖(1 / 4 : ℂ)‖ + ‖((t / 2 : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
         _ ≤ _ := by
           rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
             abs_of_nonneg (by positivity)]
           norm_num
           linarith [ht.2]
  have harg := Complex.arg_le_pi_div_two_iff.mpr (Or.inl hz.le)
  have hrem : -1 ≤ (gammaBinetLogRemainder z).re := by
    have h₁ := norm_gammaBinetLogRemainder_criticalLine_le ht₀
    have h₂ := Complex.abs_re_le_norm (gammaBinetLogRemainder z)
    have h₃ : 1 / (2 * t) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [ht.1])
    exact (neg_le_of_abs_le (h₂.trans (h₁.trans h₃)))
  have hmain : (gammaRStirlingLogMain z).re =
      -(1 / 4) * Real.log ‖z‖ - (t / 2) * Complex.arg z - 1 / 4 - (1 / 4) * Real.log Real.pi := by
    simp only [gammaRStirlingLogMain, Complex.sub_re, Complex.mul_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.log_re, Complex.log_im, z,
      criticalLineGammaArgument_re, criticalLineGammaArgument_im]
    norm_num
  have hratio := gammaBinetExponentialRatio_eq_at_one hz
  rw [hanchor, div_eq_iff (Complex.exp_ne_zero _)] at hratio
  have hfac := congrArg norm hratio
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, Complex.norm_exp] at hfac
  have hpi : ‖(Real.pi : ℂ) ^ (-z)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.neg_re, criticalLineGammaArgument_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt (by linarith [Real.pi_gt_three])) (by norm_num)
  have hcancel : t / (4 * T) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith [ht.2])
  have hweight : A + Real.log (2 * T) * (-(1 / 4)) ≤
      (gammaRStirlingLogMain z + gammaBinetLogRemainder z).re + (Real.pi / 4 - 1 / (4 * T)) * t := by
    rw [Complex.add_re, hmain]
    have har := mul_le_mul_of_nonneg_left harg (show 0 ≤ t / 2 by positivity)
    dsimp [A]
    rw [sub_mul, show 1 / (4 * T) * t = t / (4 * T) by ring]
    linarith only [hlog, har, hrem, hcancel]
  rw [Real.rpow_def_of_pos (by linarith : 0 < 2 * T), mul_assoc, ← Real.exp_add]
  calc
    _ ≤ c * Real.exp ((gammaRStirlingLogMain z + gammaBinetLogRemainder z).re +
        (Real.pi / 4 - 1 / (4 * T)) * t) := by gcongr
    _ = (‖(Real.pi : ℂ) ^ (-z)‖ * ‖Complex.Gamma z‖) * Real.exp ((Real.pi / 4 - 1 / (4 * T)) * t) := by
      rw [Real.exp_add, ← mul_assoc, ← hfac]
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) hpi) (Real.exp_pos _).le

/-- The critical-line Dirichlet polynomial is the explicit exponential sum in the
Selberg weight, with the same real coefficients. -/
private theorem spectralLineJet_mollifier_as_phases (N : ℕ) (b : ℕ → ℝ) (t : ℝ) :
    poly(N, b, t) = ∑ n ∈ Finset.Icc 1 N, ((b n / Real.sqrt n : ℝ) : ℂ) *
      Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I) := by
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  have hn₀ : 0 < n := (Finset.mem_Icc.mp hn).1
  have hnℝ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hmode0 : mode(n, 0) = ((1 / Real.sqrt n : ℝ) : ℂ) := by
    change (n : ℂ) ^ (-(1 / 2 + ((0 : ℝ) : ℂ) * Complex.I)) = _
    simp only [Complex.ofReal_zero, zero_mul, add_zero]
    rw [show (-(1 / 2) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) by norm_num, ← Complex.ofReal_natCast,
      ← Complex.ofReal_cpow hnℝ, Real.rpow_neg hnℝ, ← Real.sqrt_eq_rpow, one_div]
  rw [cpow_neg_criticalLinePoint_eq_mode hn₀ t, hmode0,
    show Complex.log (n : ℂ) = (Real.log n : ℂ) by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hnℝ]]
  push_cast
  rw [show -Complex.I * Complex.log (n : ℂ) * (t : ℂ) = -(t * Complex.log (n : ℂ)) * Complex.I by ring]
  ring


/-- The dyadic absolute bulk moment used by Selberg's short-interval method. There are
absolute positive constants `c, η` such that the gamma-weighted integral of
`|Z(t)| |∑ bₙ n^(-1/2-it)|²` on `[T,2T]` (and hence on `[h,2T]` for every `h ≤ T`) is at least `c(2T)^(3/4)` whenever
the mollifier has length at most `η √T`, constant coefficient one, and real
coefficients of absolute value at most one. No zero-count assumption is used. -/
theorem spectralLineJet_selberg_mollified_bulk_lower :
    ∃ c > (0 : ℝ), ∃ η > (0 : ℝ), ∃ T₀ ≥ (2 : ℝ), ∀ T ≥ T₀, ∀ (N : ℕ) (b : ℕ → ℝ),
      1 ≤ N → N ≤ η * Real.sqrt T → b 1 = 1 → (∀ n ∈ Finset.Icc 1 N, |b n| ≤ 1) →
      ∀ h ≤ T, c * (2 * T) ^ (3 / 4 : ℝ) ≤
        ∫ t in h..2 * T, ‖Complex.Gamma (1 / 4 + ((t / 2 : ℝ) : ℂ) * Complex.I)‖ *
          Real.exp ((Real.pi / 4 - 1 / (4 * T)) * t) *
          ‖∑ n ∈ Finset.Icc 1 N, ((b n / Real.sqrt n : ℝ) : ℂ) *
            Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ^ 2 * |hardyZ t| := by
  obtain ⟨C, hC, T₀, hT₀, hm⟩ := spectralLineJet_mollified_zeta_dyadic_mean
  obtain ⟨c, hc, hg⟩ := spectralLineJet_selberg_gamma_dyadic_lower
  refine ⟨c / 4, by positivity, 1 / (2 * C), by positivity, T₀, hT₀, ?_⟩
  intro T hT N b hN hlen hb₁ hb h hh
  have hT₂ := hT₀.trans hT
  have hTpos : 0 < T := by linarith
  have h2T : 0 < 2 * T := by positivity
  let P (t : ℝ) := poly(N, b, t)
  let Z (t : ℝ) := riemannZeta (criticalLinePoint t)
  let W (t : ℝ) := ‖Complex.Gamma (criticalLineGammaArgument t)‖ * Real.exp ((Real.pi / 4 - 1 / (4 * T)) * t)
  have hP : Continuous P := continuous_finsetSum _ fun k hk ↦
    continuous_const.mul (continuous_cpow_neg_criticalLinePoint (Finset.mem_Icc.mp hk).1)
  have hZ : Continuous Z := continuous_riemannZeta_criticalLine
  have hW : Continuous W := by
    apply Continuous.mul _ (by fun_prop)
    apply Continuous.norm
    apply continuous_iff_continuousAt.mpr
    intro t
    apply ContinuousAt.comp (g := Complex.Gamma) (f := criticalLineGammaArgument)
    · apply Complex.continuousAt_Gamma
      intro n he
      have H := congrArg Complex.re he
      rw [criticalLineGammaArgument_re] at H
      norm_num at H
      linarith [Nat.cast_nonneg (α := ℝ) n]
    · unfold criticalLineGammaArgument
      fun_prop
  let U := ∫ t in T..2 * T, Z t * P t ^ 2
  have herror : ‖U - (T : ℂ)‖ ≤ T / 2 := by
    refine (hm T hT N b hN hb₁ hb).trans ?_
    calc C * N * Real.sqrt T ≤ C * (1 / (2 * C) * Real.sqrt T) * Real.sqrt T := by gcongr
         _ = T / 2 := by field_simp [hC.ne']; nlinarith [Real.sq_sqrt hTpos.le]
  have hbulk : T / 2 ≤ ∫ t in T..2 * T, ‖Z t * P t ^ 2‖ := by
    have hN := norm_sub_le_norm_sub_add_norm_sub (T : ℂ) U 0
    rw [sub_zero, sub_zero, norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hTpos] at hN
    exact (by linarith : T / 2 ≤ ‖U‖).trans (intervalIntegral.norm_integral_le_integral_norm (by linarith))
  simp_rw [← spectralLineJet_mollifier_as_phases]
  change _ ≤ ∫ t in h..2 * T, W t * ‖P t‖ ^ 2 * |hardyZ t|
  calc
    c / 4 * (2 * T) ^ (3 / 4 : ℝ) = (c * (2 * T) ^ (-(1 / 4) : ℝ)) * (T / 2) := by
      rw [show (3 / 4 : ℝ) = -(1 / 4) + 1 by norm_num, Real.rpow_add_one h2T.ne']
      ring
    _ ≤ (c * (2 * T) ^ (-(1 / 4) : ℝ)) * ∫ t in T..2 * T, ‖Z t * P t ^ 2‖ :=
      mul_le_mul_of_nonneg_left hbulk (by positivity)
    _ = ∫ t in T..2 * T, (c * (2 * T) ^ (-(1 / 4) : ℝ)) * ‖Z t * P t ^ 2‖ :=
      (intervalIntegral.integral_const_mul ..).symm
    _ ≤ ∫ t in T..2 * T, W t * ‖P t‖ ^ 2 * |hardyZ t| := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((continuous_const.mul (hZ.mul (hP.pow 2)).norm).intervalIntegrable ..)
        (((hW.mul (hP.norm.pow 2)).mul continuous_hardyZ.abs).intervalIntegrable ..)
      intro t ht
      change (c * (2 * T) ^ (-(1 / 4) : ℝ)) * ‖Z t * P t ^ 2‖ ≤ W t * ‖P t‖ ^ 2 * |hardyZ t|
      rw [norm_mul, norm_pow, abs_hardyZ]
      change _ ≤ W t * ‖P t‖ ^ 2 * ‖Z t‖
      calc _ ≤ W t * (‖Z t‖ * ‖P t‖ ^ 2) := mul_le_mul_of_nonneg_right
             (hg T hT₂ t ht) (by positivity)
           _ = _ := by ring
    _ ≤ _ := intervalIntegral.integral_mono_interval hh (by linarith) le_rfl
      (Filter.Eventually.of_forall (fun t ↦ by dsimp [W]; positivity))
      (((hW.mul (hP.norm.pow 2)).mul continuous_hardyZ.abs).intervalIntegrable ..)

/-- A finite continuous Dirichlet approximation on the critical line. The last
mode is interpolated linearly as the cutoff `3t/π` passes its next integer. -/
def spectralLineJet_selbergFiniteZeta (L : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 L, ((min 1 (max 0 (3 * t / Real.pi - n + 1)) : ℝ) : ℂ) * mode(n, t)

private theorem spectralLineJet_selbergFiniteZeta_continuous (L : ℕ) :
    Continuous (spectralLineJet_selbergFiniteZeta L) := by
  apply continuous_finsetSum
  intro n hn
  apply Continuous.mul _ (continuous_cpow_neg_criticalLinePoint (Finset.mem_Icc.mp hn).1)
  fun_prop

/-- Interpolating the cutoff costs at most one original Dirichlet mode. -/
private theorem spectralLineJet_selbergFiniteZeta_cutoff (L : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hL : zetaFirstApproximationCutoff t + 1 ≤ L) :
    let m := zetaFirstApproximationCutoff t
    ‖spectralLineJet_selbergFiniteZeta L t - ∑ n ∈ Finset.Icc 1 m, mode(n, t)‖ ≤
      1 / Real.sqrt (m + 1) := by
  intro m
  let q := 3 * t / Real.pi
  let w (n : ℕ) := min 1 (max 0 (q - n + 1))
  have hm : (m : ℝ) ≤ q := Nat.floor_le (show 0 ≤ 3 * t / Real.pi by positivity)
  have hm' : q < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hw (n : ℕ) (hn : n ≤ m) : w n = 1 := by
    have hn' : (n : ℝ) ≤ m := by exact_mod_cast hn
    exact min_eq_left ((by linarith : 1 ≤ q - n + 1).trans (le_max_right _ _))
  have hcut : spectralLineJet_selbergFiniteZeta L t =
      ∑ n ∈ Finset.Icc 1 (m + 1), (w n : ℂ) * mode(n, t) := by
    refine (Finset.sum_subset (Finset.Icc_subset_Icc_right hL) ?_).symm
    intro n hn hnot
    have hn' : m + 1 < n := by
      by_contra! h
      exact hnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, h⟩)
    have hn'' : (m : ℝ) + 2 ≤ n := by exact_mod_cast hn'
    have hz : w n = 0 := by simp [w, max_eq_left (show q - n + 1 ≤ 0 by linarith)]
    change (w n : ℂ) * mode(n, t) = 0
    simp [hz]
  rw [hcut, Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
  have hprefix : (∑ n ∈ Finset.Icc 1 m, (w n : ℂ) * mode(n, t)) =
      ∑ n ∈ Finset.Icc 1 m, mode(n, t) := Finset.sum_congr rfl fun n hn ↦ by
    rw [hw n (Finset.mem_Icc.mp hn).2, Complex.ofReal_one, one_mul]
  rw [hprefix, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (le_min (by norm_num) (le_max_left _ _)),
    norm_cpow_neg_criticalLinePoint (Nat.succ_pos _), Nat.cast_succ]
  exact mul_le_of_le_one_left (by positivity) (min_le_left _ _)

/-- The finite, continuous cutoff has a uniform approximation error
`O((1+t)^(-1/2))` on the whole positive half-line covered by its length. -/
private theorem spectralLineJet_selbergFiniteZeta_error :
    ∃ K > (0 : ℝ), ∀ (L : ℕ) (t : ℝ), 0 ≤ t → zetaFirstApproximationCutoff t + 1 ≤ L →
      ‖riemannZeta (criticalLinePoint t) - spectralLineJet_selbergFiniteZeta L t‖ *
        Real.sqrt (1 + t) ≤ K := by
  obtain ⟨K, hK, T₀, hT₀, ha⟩ := exists_uniform_zetaFirstApproximation
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (by linarith : 0 ≤ T₀)) continuous_riemannZeta_criticalLine.norm.continuousOn
  let D := ‖riemannZeta (criticalLinePoint u)‖ + 2 * Real.sqrt T₀ + 1
  refine ⟨max (D * Real.sqrt (1 + T₀)) (2 * K + 2), (by positivity : 0 < 2 * K + 2).trans_le (le_max_right _ _), ?_⟩
  intro L t ht hL
  let m := zetaFirstApproximationCutoff t
  let Z := riemannZeta (criticalLinePoint t)
  let P := ∑ n ∈ Finset.Icc 1 m, mode(n, t)
  let Q := spectralLineJet_selbergFiniteZeta L t
  have hdiff : ‖P - Q‖ ≤ 1 / Real.sqrt (m + 1) := by
    rw [norm_sub_rev]
    exact spectralLineJet_selbergFiniteZeta_cutoff L ht hL
  have hsplit : ‖Z - Q‖ ≤ ‖Z - P‖ + ‖P - Q‖ := norm_sub_le_norm_sub_add_norm_sub ..
  change ‖Z - Q‖ * _ ≤ _
  by_cases h : T₀ ≤ t
  · apply le_trans _ (le_max_right _ _)
    have ht' : 0 < t := by linarith
    have hz : ‖Z - P‖ ≤ K / Real.sqrt t := by
      have H := ha t t h le_rfl (by linarith)
      norm_num [Z, P, m, criticalLinePoint] at H ⊢
      exact H
    have hs₁ : Real.sqrt (1 + t) ≤ 2 * Real.sqrt t := by
      rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt ht]
      linarith
    have hs₂ : Real.sqrt (1 + t) ≤ 2 * Real.sqrt (m + 1) := by
      have hfloor : 3 * t / Real.pi < (m : ℝ) + 1 := Nat.lt_floor_add_one _
      have hfloor' := (div_lt_iff₀ Real.pi_pos).mp hfloor
      have hpi := mul_lt_mul_of_pos_left Real.pi_lt_four (show (0 : ℝ) < m + 1 by positivity)
      rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
      linarith
    calc _ ≤ (K / Real.sqrt t + 1 / Real.sqrt (m + 1)) * Real.sqrt (1 + t) :=
           mul_le_mul_of_nonneg_right (hsplit.trans (add_le_add hz hdiff)) (by positivity)
         _ ≤ K / Real.sqrt t * (2 * Real.sqrt t) + 1 / Real.sqrt (m + 1) * (2 * Real.sqrt (m + 1)) := by
           rw [add_mul]; gcongr
         _ = _ := by field_simp
  · apply le_trans _ (le_max_left _ _)
    have ht' := le_of_not_ge h
    have hz : ‖Z‖ ≤ ‖riemannZeta (criticalLinePoint u)‖ := hmax ⟨ht, ht'⟩
    have hrem : 1 / Real.sqrt (m + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      exact Real.one_le_sqrt.mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])
    have hp : ‖P‖ ≤ 2 * Real.sqrt T₀ :=
      (norm_sum_Icc_cpow_neg_criticalLinePoint_le m t).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ((zetaFirstApproximationCutoff_le_height ht).trans ht')) (by norm_num))
    exact mul_le_mul (hsplit.trans (add_le_add ((norm_sub_le Z P).trans (add_le_add hz hp)) (hdiff.trans hrem)))
      (Real.sqrt_le_sqrt (by linarith)) (by positivity) (by dsimp [D]; positivity)

private theorem spectralLineJet_selbergGamma_continuous :
    Continuous (fun t : ℝ ↦ Complex.Gamma (criticalLineGammaArgument t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply ContinuousAt.comp (g := Complex.Gamma) (f := criticalLineGammaArgument)
  · apply Complex.continuousAt_Gamma
    intro n he
    have H := congrArg Complex.re he
    rw [criticalLineGammaArgument_re] at H
    norm_num at H
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · unfold criticalLineGammaArgument
    fun_prop

/-- Uniform upper envelope for the critical-line gamma factor, including the exponential damping and bounded heights. -/
private theorem spectralLineJet_selbergGamma_upper :
    ∃ C > (0 : ℝ), ∀ H > (0 : ℝ), ∀ t ≥ (0 : ℝ),
      ‖Complex.Gamma (criticalLineGammaArgument t)‖ * Real.exp ((Real.pi / 4 - 1 / (2 * H)) * t) *
        (1 + t) ^ (1 / 4 : ℝ) ≤ C := by
  obtain ⟨c, hc, ha⟩ := exists_pos_gammaBinetExponentialRatio_at_one
  let A := Real.log 4 / 4 - Real.log Real.pi / 4 + 1
  let B (t : ℝ) := ‖Complex.Gamma (criticalLineGammaArgument t)‖ * Real.exp (Real.pi * t / 4) *
    (1 + t) ^ (1 / 4 : ℝ)
  have hB : Continuous B := by
    exact (spectralLineJet_selbergGamma_continuous.norm.mul (by fun_prop)).mul
      ((continuous_const.add continuous_id).rpow_const (fun _ ↦ Or.inr (by norm_num)))
  obtain ⟨u, _, hu⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr zero_le_one) (hB.continuousOn (s := Icc (0 : ℝ) 1))
  let p := Real.pi ^ (-(1 / 4) : ℝ)
  have hp : 0 < p := Real.rpow_pos_of_pos Real.pi_pos _
  refine ⟨max (B u) ((c * Real.exp A) / p), (by positivity : 0 < (c * Real.exp A) / p).trans_le
    (le_max_right _ _), ?_⟩
  intro H hH t ht
  apply le_trans (b := B t)
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    rw [sub_mul]
    linarith [show 0 ≤ 1 / (2 * H) * t by positivity]
  by_cases h : t ≤ 1
  · exact (hu ⟨ht, h⟩).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    have h₁ := le_of_not_ge h
    have ht₀ : 0 < t := by linarith
    let z := criticalLineGammaArgument t
    have hz : 0 < z.re := by rw [criticalLineGammaArgument_re]; norm_num
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr fun H ↦ by rw [H] at hz; exact lt_irrefl _ hz
    have hlog : Real.log (1 + t) ≤ Real.log 4 + Real.log ‖z‖ := by
      rw [← Real.log_mul (by norm_num) hn.ne']
      apply Real.log_le_log (by positivity)
      have hi := Complex.im_le_norm z
      rw [criticalLineGammaArgument_im] at hi
      linarith
    have hrem : (gammaBinetLogRemainder z).re ≤ 1 := by
      refine (Complex.re_le_norm _).trans ((norm_gammaBinetLogRemainder_criticalLine_le ht₀).trans ?_)
      apply (div_le_one (by positivity)).mpr
      linarith
    have har := mul_le_mul_of_nonneg_left (Real.arctan_le_self (show 0 ≤ 1 / (2 * t) by positivity))
      (show 0 ≤ t / 2 by positivity)
    rw [show t / 2 * (1 / (2 * t)) = 1 / 4 by field_simp; norm_num] at har
    have hmain : (gammaRStirlingLogMain z).re =
        -(1 / 4) * Real.log ‖z‖ - (t / 2) * Complex.arg z - 1 / 4 - (1 / 4) * Real.log Real.pi := by
      simp only [gammaRStirlingLogMain, Complex.sub_re, Complex.mul_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.log_re, Complex.log_im, z,
        criticalLineGammaArgument_re, criticalLineGammaArgument_im]
      norm_num
    have hweight : (gammaRStirlingLogMain z + gammaBinetLogRemainder z).re +
        Real.pi * t / 4 + Real.log (1 + t) * (1 / 4) ≤ A := by
      rw [Complex.add_re, hmain, arg_criticalLineGammaArgument_eq_pi_div_two_sub ht₀]
      dsimp [A]
      linarith only [hlog, har, hrem]
    have hratio := gammaBinetExponentialRatio_eq_at_one hz
    rw [ha, div_eq_iff (Complex.exp_ne_zero _)] at hratio
    have hfac := congrArg norm hratio
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, Complex.norm_exp,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.neg_re] at hfac
    rw [show z.re = 1 / 4 from criticalLineGammaArgument_re t] at hfac
    apply (le_div_iff₀ hp).mpr
    dsimp only [B]
    rw [Real.rpow_def_of_pos (by positivity : 0 < 1 + t)]
    calc _ = (p * ‖Complex.Gamma z‖) * Real.exp (Real.pi * t / 4) * Real.exp (Real.log (1 + t) * (1 / 4)) := by ring
         _ = c * Real.exp ((gammaRStirlingLogMain z + gammaBinetLogRemainder z).re +
             Real.pi * t / 4 + Real.log (1 + t) * (1 / 4)) := by rw [hfac, Real.exp_add, Real.exp_add]; ring
         _ ≤ _ := by gcongr

local notation "winWeight(" H ", " N ", " b ", " t ")" =>
  (‖Complex.Gamma (1 / 4 + (((t : ℝ) / 2 : ℝ) : ℂ) * Complex.I)‖ *
    Real.exp ((Real.pi / 4 - 1 / (2 * H)) * t) * ‖poly(N, b, t)‖ ^ 2)
local notation "finiteHardy(" L ", " t ")" =>
  (Complex.re (-hardyPhaseFactor t * spectralLineJet_selbergFiniteZeta L t))

/-- Replacing Hardy's Z by the phase-corrected finite critical-line sum costs
`O(N(1+t)^(-3/4))` in the gamma-weighted mollified function. -/
private theorem spectralLineJet_selberg_pointwise_error :
    ∃ K > (0 : ℝ), ∀ (H : ℝ), 0 < H → ∀ L N (b : ℕ → ℝ),
      (∀ n ∈ Finset.Icc 1 N, |b n| ≤ 1) → ∀ t ≥ (0 : ℝ), zetaFirstApproximationCutoff t + 1 ≤ L →
      |winWeight(H, N, b, t) * hardyZ t - winWeight(H, N, b, t) * finiteHardy(L, t)| ≤
        K * N * (1 + t) ^ (-(3 / 4) : ℝ) := by
  obtain ⟨A, hA, ha⟩ := spectralLineJet_selbergGamma_upper
  obtain ⟨B, hB, hb₀⟩ := spectralLineJet_selbergFiniteZeta_error
  refine ⟨4 * A * B, by positivity, ?_⟩
  intro H hH L N b hb t ht hL
  let Z := riemannZeta (criticalLinePoint t)
  let Q := spectralLineJet_selbergFiniteZeta L t
  let V := ‖Complex.Gamma (criticalLineGammaArgument t)‖ * Real.exp ((Real.pi / 4 - 1 / (2 * H)) * t)
  let σ := -hardyPhaseFactor t
  have hphase : (hardyZ t : ℂ) = σ * Z := by
    have hx := hardyFunction_eq_factor_unit_mul_riemannZeta t
    rw [hardyFunction, hardyFunctionReal, Complex.ofReal_neg] at hx
    simpa [σ, Z] using congrArg Neg.neg hx
  have hdiff : |hardyZ t - finiteHardy(L, t)| ≤ ‖Z - Q‖ := by
    change |hardyZ t - (σ * Q).re| ≤ _
    rw [show hardyZ t = (σ * Z).re from congrArg Complex.re hphase, ← Complex.sub_re, ← mul_sub]
    exact (Complex.abs_re_le_norm _).trans_eq (by simp [σ, norm_hardyPhaseFactor])
  have hgamma : V * (1 + t) ^ (1 / 4 : ℝ) ≤ A := ha H hH t ht
  have hp : ‖poly(N, b, t)‖ ^ 2 ≤ 4 * N := by
    refine (pow_le_pow_left₀ (norm_nonneg _) (spectralLineJet_mollifier_norm N b hb t) 2).trans_eq ?_
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    ring
  have ht₁ : 0 < 1 + t := by positivity
  rw [← mul_sub, abs_mul, abs_of_nonneg (show 0 ≤ winWeight(H, N, b, t) by positivity),
    Real.rpow_neg ht₁.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos ht₁ _)).mpr
  change V * ‖poly(N, b, t)‖ ^ 2 * _ * _ ≤ _
  have hpow : (1 + t) ^ (3 / 4 : ℝ) = (1 + t) ^ (1 / 4 : ℝ) * Real.sqrt (1 + t) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht₁]
    congr 1
    norm_num
  rw [hpow]
  calc
    _ ≤ (V * (1 + t) ^ (1 / 4 : ℝ)) * (‖Z - Q‖ * Real.sqrt (1 + t)) * ‖poly(N, b, t)‖ ^ 2 := by
      calc _ ≤ V * ‖poly(N, b, t)‖ ^ 2 * ‖Z - Q‖ * ((1 + t) ^ (1 / 4 : ℝ) * Real.sqrt (1 + t)) := by
             gcongr
           _ = _ := by ring
    _ ≤ (A * B) * (4 * N) := by
      apply mul_le_mul _ hp (by positivity) (by positivity)
      exact mul_le_mul hgamma (hb₀ L t ht hL) (by positivity) hA.le
    _ = _ := by ring

private theorem spectralLineJet_selberg_continuousWindow {f : ℝ → ℝ} (hf : Continuous f) (h : ℝ) :
    Continuous (fun t : ℝ ↦ ∫ u in t..t + h, f u) := by
  let P (t : ℝ) := ∫ u in (0 : ℝ)..t, f u
  have hP : Continuous P := intervalIntegral.continuous_primitive (fun a b ↦ hf.intervalIntegrable a b) 0
  apply ((hP.comp (continuous_id.add_const h)).sub hP).congr
  intro t
  simpa [P] using (eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 t) (hf.intervalIntegrable t (t + h)))).symm

/-- A `(1+t)^(-3/4)` error envelope costs a bounded short-window second moment
on arbitrarily long initial intervals. The same proof works after a 1-Lipschitz
map, in particular for the signed window and for the absolute window. -/
private theorem spectralLineJet_selberg_window_error_envelope {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) {H h D : ℝ} (hH : 0 ≤ H) (hh : 0 ≤ h) (hD : 0 ≤ D)
    (he : ∀ t ∈ Icc (0 : ℝ) (H + h), |f t - g t| ≤ D * (1 + t) ^ (-(3 / 4) : ℝ))
    (q : ℝ → ℝ) (hq : LipschitzWith 1 q) :
    (∫ t in (0 : ℝ)..H, ((∫ u in t..t + h, q (f u)) - ∫ u in t..t + h, q (g u)) ^ 2) ≤
      2 * (h * D) ^ 2 := by
  let E (u : ℝ) := q (f u) - q (g u)
  have hE : Continuous E := (hq.continuous.comp hf).sub (hq.continuous.comp hg)
  let J (t : ℝ) := ∫ u in t..t + h, E u
  have hJ : Continuous J := spectralLineJet_selberg_continuousWindow hE h
  have heq (t : ℝ) : (∫ u in t..t + h, q (f u)) - (∫ u in t..t + h, q (g u)) = J t :=
    (intervalIntegral.integral_sub ((hq.continuous.comp hf).intervalIntegrable ..)
      ((hq.continuous.comp hg).intervalIntegrable ..)).symm
  have hsq (t : ℝ) (ht : t ∈ Icc 0 H) : J t ^ 2 ≤ (h * D) ^ 2 * (1 + t) ^ (-(3 / 2) : ℝ) := by
    have ht₁ : 0 < 1 + t := by linarith [ht.1]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := t + h)
      (C := D * (1 + t) ^ (-(3 / 4) : ℝ)) (f := E) (fun u hu ↦ by
        rw [uIoc_of_le (by linarith)] at hu
        have h₁ := hq.dist_le_mul (f u) (g u)
        have h₂ := he u ⟨ht.1.trans hu.1.le, by linarith [ht.2, hu.2]⟩
        have h₃ : (1 + u) ^ (-(3 / 4) : ℝ) ≤ (1 + t) ^ (-(3 / 4) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos ht₁ (by linarith [hu.1]) (by norm_num)
        exact (by simpa only [E, Real.norm_eq_abs, Real.dist_eq, NNReal.coe_one, one_mul] using h₁ :
          ‖E u‖ ≤ |f u - g u|).trans (h₂.trans (mul_le_mul_of_nonneg_left h₃ hD)))
    rw [show t + h - t = h by ring, abs_of_nonneg hh] at hb
    calc J t ^ 2 = ‖J t‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
         _ ≤ (D * (1 + t) ^ (-(3 / 4) : ℝ) * h) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb _
         _ = _ := by
           rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast ht₁.le]
           norm_num
           ring
  have hpow : ContinuousOn (fun t : ℝ ↦ (1 + t) ^ (-(3 / 2) : ℝ)) (Icc 0 H) := by
    apply (continuous_const.add continuous_id).continuousOn.rpow_const
    intro t ht
    exact Or.inl (ne_of_gt (by linarith [ht.1] : 0 < 1 + t))
  have hint : (∫ t in (0 : ℝ)..H, (1 + t) ^ (-(3 / 2) : ℝ)) ≤ 2 := by
    rw [intervalIntegral.integral_comp_add_left (fun x : ℝ ↦ x ^ (-(3 / 2) : ℝ)) 1]
    simp only [add_zero]
    rw [integral_rpow (Or.inr ⟨by norm_num, by rw [uIcc_of_le (by linarith : 1 ≤ 1 + H)]; simp⟩)]
    norm_num
    have := Real.rpow_nonneg (show 0 ≤ 1 + H by linarith) (-(1 / 2) : ℝ)
    linarith
  simp_rw [heq]
  calc _ ≤ ∫ t in (0 : ℝ)..H, (h * D) ^ 2 * (1 + t) ^ (-(3 / 2) : ℝ) :=
         intervalIntegral.integral_mono_on hH ((hJ.pow 2).intervalIntegrable ..)
           ((continuousOn_const.mul hpow).intervalIntegrable_of_Icc hH) hsq
       _ = (h * D) ^ 2 * ∫ t in (0 : ℝ)..H, (1 + t) ^ (-(3 / 2) : ℝ) := intervalIntegral.integral_const_mul ..
       _ ≤ _ := (mul_le_mul_of_nonneg_left hint (sq_nonneg _)).trans_eq (mul_comm _ _)

private theorem spectralLineJet_selbergPhase_continuous : Continuous hardyPhaseFactor := by
  have hG : Continuous (fun t ↦ Complex.Gammaℝ (criticalLinePoint t)) := by
    have heq (t : ℝ) : criticalLinePoint t / 2 = criticalLineGammaArgument t := by
      unfold criticalLinePoint criticalLineGammaArgument
      push_cast
      ring
    simp_rw [Complex.Gammaℝ_def, heq]
    apply Continuous.mul _ spectralLineJet_selbergGamma_continuous
    apply Continuous.const_cpow (continuous_criticalLinePoint.neg.div_const _)
    exact Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact (hG.div (Complex.continuous_ofReal.comp hG.norm) fun t ↦ by
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos
      (by simp [criticalLinePoint] : 0 < (criticalLinePoint t).re)))).neg

private theorem spectralLineJet_selberg_signals_continuous (H : ℝ) (L N : ℕ) (b : ℕ → ℝ) :
    Continuous (fun t ↦ winWeight(H, N, b, t) * hardyZ t) ∧
    Continuous (fun t ↦ winWeight(H, N, b, t) * finiteHardy(L, t)) := by
  have hW : Continuous (fun t ↦ winWeight(H, N, b, t)) := by
    apply (spectralLineJet_selbergGamma_continuous.norm.mul (by fun_prop)).mul
    apply Continuous.pow _ 2
    apply Continuous.norm
    apply continuous_finsetSum
    intro n hn
    exact continuous_const.mul (continuous_cpow_neg_criticalLinePoint (Finset.mem_Icc.mp hn).1)
  have hQ : Continuous (fun t ↦ finiteHardy(L, t)) := Complex.continuous_re.comp
    (spectralLineJet_selbergPhase_continuous.neg.mul (spectralLineJet_selbergFiniteZeta_continuous L))
  exact ⟨hW.mul continuous_hardyZ, hW.mul hQ⟩

/-- Both short-window second moments in Selberg's counting argument can be computed
with a finite Dirichlet sum up to squared error `O(h² N²)`. Here `q = id` gives the
signed windows, and `q = abs` the absolute windows. The constant is independent of
height, window length, cutoff, and mollifier coefficients. The estimate includes
window starts at height zero and the final window extending beyond `H`. -/
theorem spectralLineJet_selberg_finite_window_second_moment_error :
    ∃ C > (0 : ℝ), ∀ H > (0 : ℝ), ∀ h ≥ (0 : ℝ), ∀ (L N : ℕ) (b : ℕ → ℝ),
      3 * (H + h) / Real.pi + 1 ≤ L → (∀ n ∈ Finset.Icc 1 N, |b n| ≤ 1) →
      ∀ (q : ℝ → ℝ), LipschitzWith 1 q →
      (∫ t in (0 : ℝ)..H,
        ((∫ u in t..t + h, q (winWeight(H, N, b, u) * hardyZ u)) -
          ∫ u in t..t + h, q (winWeight(H, N, b, u) * finiteHardy(L, u))) ^ 2) ≤
        C * (h * N) ^ 2 := by
  obtain ⟨K, hK, he⟩ := spectralLineJet_selberg_pointwise_error
  refine ⟨2 * K ^ 2, by positivity, ?_⟩
  intro H hH h hh L N b hL hb q hq
  obtain ⟨hf, hg⟩ := spectralLineJet_selberg_signals_continuous H L N b
  have hbnd := spectralLineJet_selberg_window_error_envelope hf hg hH.le hh (show 0 ≤ K * N by positivity) (fun t ht ↦ by
      apply he H hH L N b hb t ht.1
      have hcut : (zetaFirstApproximationCutoff t : ℝ) ≤ 3 * t / Real.pi :=
        Nat.floor_le (div_nonneg (mul_nonneg (by norm_num) ht.1) Real.pi_pos.le)
      have hdiv : 3 * t / Real.pi ≤ 3 * (H + h) / Real.pi := by gcongr; exact ht.2
      exact_mod_cast (show (zetaFirstApproximationCutoff t : ℝ) + 1 ≤ L by linarith)) q hq
  exact hbnd.trans_eq (by ring)

/-- The upper short-window second moments of the actual mollified Hardy function reduce
to those of one entirely finite Dirichlet sum. An arbitrarily small relative loss
`1 + ε` on the model costs only `O((1 + 1/ε) h² N²)` additively. -/
theorem spectralLineJet_selberg_finite_window_second_moment_upper :
    ∃ C > (0 : ℝ), ∀ H > (0 : ℝ), ∀ h ≥ (0 : ℝ), ∀ (L N : ℕ) (b : ℕ → ℝ),
      3 * (H + h) / Real.pi + 1 ≤ L → (∀ n ∈ Finset.Icc 1 N, |b n| ≤ 1) →
      ∀ (q : ℝ → ℝ), LipschitzWith 1 q → ∀ ε > (0 : ℝ),
      (∫ t in (0 : ℝ)..H, (∫ u in t..t + h, q (winWeight(H, N, b, u) * hardyZ u)) ^ 2) ≤
      (1 + ε) * (∫ t in (0 : ℝ)..H, (∫ u in t..t + h, q (winWeight(H, N, b, u) * finiteHardy(L, u))) ^ 2) +
        (1 + 1 / ε) * C * (h * N) ^ 2 := by
  obtain ⟨C, hC, he⟩ := spectralLineJet_selberg_finite_window_second_moment_error
  refine ⟨C, hC, ?_⟩
  intro H hH h hh L N b hL hb q hq ε hε
  let f (u : ℝ) := q (winWeight(H, N, b, u) * hardyZ u)
  let g (u : ℝ) := q (winWeight(H, N, b, u) * finiteHardy(L, u))
  let U (t : ℝ) := ∫ u in t..t + h, f u
  let V (t : ℝ) := ∫ u in t..t + h, g u
  obtain ⟨hf, hg⟩ := spectralLineJet_selberg_signals_continuous H L N b
  have hU : Continuous U := spectralLineJet_selberg_continuousWindow (hq.continuous.comp hf) h
  have hV : Continuous V := spectralLineJet_selberg_continuousWindow (hq.continuous.comp hg) h
  have hpt (t : ℝ) : U t ^ 2 ≤ (1 + ε) * V t ^ 2 + (1 + 1 / ε) * (U t - V t) ^ 2 := by
    apply (mul_le_mul_iff_right₀ hε).mp
    field_simp
    nlinarith [sq_nonneg (ε * V t - (U t - V t))]
  have H₁ : Continuous (fun t ↦ (1 + ε) * V t ^ 2) := continuous_const.mul (hV.pow 2)
  have H₂ : Continuous (fun t ↦ (1 + 1 / ε) * (U t - V t) ^ 2) := continuous_const.mul ((hU.sub hV).pow 2)
  change (∫ t in (0 : ℝ)..H, U t ^ 2) ≤ _
  calc
    _ ≤ ∫ t in (0 : ℝ)..H, (1 + ε) * V t ^ 2 + (1 + 1 / ε) * (U t - V t) ^ 2 :=
      intervalIntegral.integral_mono_on hH.le ((hU.pow 2).intervalIntegrable ..)
        ((H₁.add H₂).intervalIntegrable ..) fun t _ ↦ hpt t
    _ = (1 + ε) * (∫ t in (0 : ℝ)..H, V t ^ 2) +
        (1 + 1 / ε) * (∫ t in (0 : ℝ)..H, (U t - V t) ^ 2) := by
      rw [intervalIntegral.integral_add (H₁.intervalIntegrable ..) (H₂.intervalIntegrable ..),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ (1 + ε) * (∫ t in (0 : ℝ)..H, V t ^ 2) + (1 + 1 / ε) * (C * (h * N) ^ 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (he H hH h hh L N b hL hb q hq)
        (show 0 ≤ 1 + 1 / ε by positivity))
    _ = _ := by dsimp [V, g]; ring

/-- A uniform elementary bound for the critical-line zeta factor, including height zero. -/
private theorem spectralLineJet_selberg_zeta_growth :
    ∃ K > (0 : ℝ), ∀ t ≥ (0 : ℝ), ‖riemannZeta (criticalLinePoint t)‖ ≤ K * Real.sqrt (1 + t) := by
  obtain ⟨K, hK, he⟩ := spectralLineJet_selbergFiniteZeta_error
  refine ⟨K + 3, by positivity, ?_⟩
  intro t ht
  let m := zetaFirstApproximationCutoff t
  let Z := riemannZeta (criticalLinePoint t)
  let Q := spectralLineJet_selbergFiniteZeta (m + 1) t
  let D := ∑ n ∈ Finset.Icc 1 m, mode(n, t)
  have ht₁ : 1 ≤ Real.sqrt (1 + t) := Real.one_le_sqrt.mpr (by linarith)
  have hm₁ : 1 ≤ Real.sqrt (m + 1) := Real.one_le_sqrt.mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have herror : ‖Z - Q‖ ≤ K :=
    (le_mul_of_one_le_right (norm_nonneg _) ht₁).trans (he (m + 1) t ht le_rfl)
  have hcut : ‖Q - D‖ ≤ 1 := (spectralLineJet_selbergFiniteZeta_cutoff (m + 1) ht le_rfl).trans
    ((div_le_one (by positivity)).mpr hm₁)
  have hsum : ‖D‖ ≤ 2 * Real.sqrt (1 + t) := (norm_sum_Icc_cpow_neg_criticalLinePoint_le m t).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ((zetaFirstApproximationCutoff_le_height ht).trans
      (by linarith))) (by norm_num))
  have hzd := norm_sub_le_norm_sub_add_norm_sub Z Q D
  have hZ := norm_sub_le_norm_sub_add_norm_sub Z D 0
  simp only [sub_zero] at hZ
  change ‖Z‖ ≤ _
  nlinarith [mul_nonneg hK.le (sub_nonneg.mpr ht₁)]

/-- An unconditional upper bound for both actual short-window second moments on
initial heights `[0,Y]`. For bounded window length and power lengths `N ≤ H^β`,
`Y ≤ H^α`, this range is negligible at Selberg's scale `h²√H` if `4β + 3α < 1`. -/
theorem spectralLineJet_selberg_initial_window_second_moment_upper :
    ∃ C > (0 : ℝ), ∀ H > (0 : ℝ), ∀ h ≥ (0 : ℝ), ∀ Y ≥ (0 : ℝ), ∀ (N : ℕ) (b : ℕ → ℝ),
      (∀ n ∈ Finset.Icc 1 N, |b n| ≤ 1) →
      ∀ (q : ℝ → ℝ), LipschitzWith 1 q → q 0 = 0 →
      (∫ t in (0 : ℝ)..Y, (∫ u in t..t + h, q (winWeight(H, N, b, u) * hardyZ u)) ^ 2) ≤
        C * (h * N) ^ 2 * Y * Real.sqrt (1 + Y + h) := by
  obtain ⟨A, hA, ha⟩ := spectralLineJet_selbergGamma_upper
  obtain ⟨B, hB, hb₀⟩ := spectralLineJet_selberg_zeta_growth
  refine ⟨(4 * A * B) ^ 2, by positivity, ?_⟩
  intro H hH h hh Y hY N b hb q hq hq₀
  let f (t : ℝ) := q (winWeight(H, N, b, t) * hardyZ t)
  let U (t : ℝ) := ∫ u in t..t + h, f u
  let D := 4 * A * B * N
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hf : Continuous f := hq.continuous.comp (spectralLineJet_selberg_signals_continuous H 0 N b).1
  have hU : Continuous U := spectralLineJet_selberg_continuousWindow hf h
  have hsize (u : ℝ) (hu : 0 ≤ u) : ‖f u‖ ≤ D * (1 + u) ^ (1 / 4 : ℝ) := by
    have hu₁ : 0 < 1 + u := by positivity
    have he := hq.dist_le_mul (winWeight(H, N, b, u) * hardyZ u) 0
    rw [hq₀, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero, NNReal.coe_one, one_mul, abs_mul,
      abs_of_nonneg (show 0 ≤ winWeight(H, N, b, u) by positivity), abs_hardyZ] at he
    have hγ := ha H hH u hu
    have hp : ‖poly(N, b, u)‖ ^ 2 ≤ 4 * N := by
      refine (pow_le_pow_left₀ (norm_nonneg _) (spectralLineJet_mollifier_norm N b hb u) 2).trans_eq ?_
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
      ring
    have hpow : (1 + u) ^ (1 / 4 : ℝ) * (1 + u) ^ (1 / 4 : ℝ) = Real.sqrt (1 + u) := by
      rw [← Real.rpow_add hu₁, Real.sqrt_eq_rpow]
      congr 1
      norm_num
    change |q _| ≤ _
    refine he.trans ?_
    calc _ ≤ (‖Complex.Gamma (criticalLineGammaArgument u)‖ * Real.exp ((Real.pi / 4 - 1 / (2 * H)) * u)) *
            (4 * N) * (B * Real.sqrt (1 + u)) := by
           apply mul_le_mul _ (hb₀ u hu) (norm_nonneg _) (by positivity)
           exact mul_le_mul_of_nonneg_left hp (by positivity)
         _ = ((‖Complex.Gamma (criticalLineGammaArgument u)‖ * Real.exp ((Real.pi / 4 - 1 / (2 * H)) * u)) *
             (1 + u) ^ (1 / 4 : ℝ)) * ((4 * N) * B * (1 + u) ^ (1 / 4 : ℝ)) := by rw [← hpow]; ring
         _ ≤ A * ((4 * N) * B * (1 + u) ^ (1 / 4 : ℝ)) := mul_le_mul_of_nonneg_right hγ (by positivity)
         _ = _ := by dsimp [D]; ring
  have hbound (t : ℝ) (ht : t ∈ Icc 0 Y) : U t ^ 2 ≤ (D * h) ^ 2 * Real.sqrt (1 + Y + h) := by
    have H₁ := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := t + h)
      (C := D * (1 + Y + h) ^ (1 / 4 : ℝ)) (f := f) (fun u hu ↦ by
        rw [uIoc_of_le (by linarith)] at hu
        refine (hsize u (ht.1.trans hu.1.le)).trans (mul_le_mul_of_nonneg_left ?_ hD)
        exact Real.rpow_le_rpow (by linarith [ht.1, hu.1]) (by linarith [ht.2, hu.2]) (by norm_num))
    rw [show t + h - t = h by ring, abs_of_nonneg hh] at H₁
    calc _ = ‖U t‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
         _ ≤ (D * (1 + Y + h) ^ (1 / 4 : ℝ) * h) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) H₁ _
         _ = _ := by
           rw [mul_pow, mul_pow,← Real.rpow_mul_natCast (show 0 ≤ 1 + Y + h by linarith), Real.sqrt_eq_rpow]
           norm_num
           ring
  change (∫ t in (0 : ℝ)..Y, U t ^ 2) ≤ _
  calc _ ≤ ∫ _t in (0 : ℝ)..Y, (D * h) ^ 2 * Real.sqrt (1 + Y + h) :=
         intervalIntegral.integral_mono_on hY ((hU.pow 2).intervalIntegrable ..) intervalIntegrable_const hbound
       _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, D]; ring

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

private def spectralLineJet_selbergHalfCoeff (k : ℕ) : ℝ :=
  (-1) ^ k * Ring.choose (1/2 : ℝ) k

private theorem spectralLineJet_selbergHalfCoeff_bound (k : ℕ) :
    |spectralLineJet_selbergHalfCoeff k| ≤ 1 := by
  have hrec (k : ℕ) : ((k : ℝ) + 1) * Ring.choose (1/2 : ℝ) (k+1) =
      (1/2 - k) * Ring.choose (1/2 : ℝ) k := by
    have h := Ring.descPochhammer_eq_factorial_smul_choose (1/2 : ℝ) (k+1)
    rw [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
      Polynomial.smeval_X, Polynomial.smeval_natCast, Ring.descPochhammer_eq_factorial_smul_choose] at h
    simp only [nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
    apply mul_left_cancel₀ (show (k.factorial : ℝ) ≠ 0 by positivity)
    linear_combination -h
  have hb (n : ℕ) : |Ring.choose (1/2 : ℝ) n| ≤ 1 := by
    induction n with
    | zero => simp
    | succ i hi =>
      have ha : |1/2 - (i : ℝ)| ≤ i+1 := abs_le.mpr ⟨by linarith, by linarith [Nat.cast_nonneg (α := ℝ) i]⟩
      apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < i+1 by positivity)).mp
      have he := congrArg abs (hrec i)
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < i+1)] at he
      rw [mul_one, he]
      exact (mul_le_of_le_one_right (abs_nonneg _) hi).trans ha
  simpa [spectralLineJet_selbergHalfCoeff, abs_mul, abs_pow] using hb k

/-- The local inverse square root has convolution square `1-X`, including the
coefficient at zero. -/
private theorem spectralLineJet_selbergHalfCoeff_square (k : ℕ) :
    ∑ ij ∈ Finset.antidiagonal k, spectralLineJet_selbergHalfCoeff ij.1 *
      spectralLineJet_selbergHalfCoeff ij.2 =
        if k = 0 then (1 : ℝ) else if k = 1 then -1 else 0 := by
  have hv := Ring.add_choose_eq (r := (1/2 : ℝ)) (s := 1/2) k (Commute.refl _)
  have hnat : (1/2 : ℝ) + 1/2 = (1 : ℕ) := by norm_num
  calc _ = (-1 : ℝ)^k * ∑ ij ∈ Finset.antidiagonal k,
           Ring.choose (1/2 : ℝ) ij.1 * Ring.choose (1/2 : ℝ) ij.2 := by
         rw [Finset.mul_sum]
         refine Finset.sum_congr rfl fun ij hij ↦ ?_
         rw [← Finset.mem_antidiagonal.mp hij, pow_add]
         unfold spectralLineJet_selbergHalfCoeff
         ring
       _ = (-1 : ℝ)^k * ((1 : ℕ).choose k : ℝ) := by rw [← hv, hnat, Ring.choose_natCast]
       _ = _ := by
         rcases k with _ | k
         · simp
         rcases k with _ | k
         · simp
         simp [Nat.choose_eq_zero_of_lt (by omega : 1 < k+2)]

/-- The real coefficients of the inverse square root of the zeta Euler product.
Their cutoff gives a single admissible mollifier at every length. -/
def spectralLineJet_selbergHalfMoebius : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n = 0 then 0 else n.factorization.prod fun _ k ↦ (-1)^k * Ring.choose (1/2 : ℝ) k, by simp⟩

private theorem spectralLineJet_selbergHalfMoebius_mult :
    spectralLineJet_selbergHalfMoebius.IsMultiplicative := by
  constructor
  · simp [spectralLineJet_selbergHalfMoebius]
  · intro a b hab
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    change (if a*b = 0 then _ else _) = (if a = 0 then _ else _) * (if b = 0 then _ else _)
    simp only [ha,hb,mul_ne_zero ha hb,ite_false,Nat.factorization_mul_of_coprime hab]
    exact Finsupp.prod_add_index_of_disjoint hab.disjoint_primeFactors _

private theorem spectralLineJet_selbergHalfMoebius_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    spectralLineJet_selbergHalfMoebius (p^k) = spectralLineJet_selbergHalfCoeff k := by
  simp only [spectralLineJet_selbergHalfMoebius, ArithmeticFunction.coe_mk,
    pow_ne_zero _ hp.ne_zero, ite_false, hp.factorization_pow]
  exact Finsupp.prod_single_index (by simp)

/-- Expand one prime-power Dirichlet convolution into the ordinary coefficient
convolution on exponents. -/
private theorem spectralLineJet_dirichlet_prime_power {R : Type*} [CommSemiring R]
    (f g : ArithmeticFunction R) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f * g) (p ^ k) = ∑ ij ∈ Finset.antidiagonal k, f (p ^ ij.1) * g (p ^ ij.2) := by
  let e : ℕ ↪ ℕ := ⟨(p ^ ·), Nat.pow_right_injective hp.one_lt⟩
  have hset : (p ^ k).divisorsAntidiagonal = (Finset.antidiagonal k).map (e.prodMap e) := by
    apply Finset.Subset.antisymm _ (Nat.antidiagonal_map_subset_divisorsAntidiagonal_pow hp.one_lt k)
    rintro ⟨a,b⟩ hab
    have h := (Nat.mem_divisorsAntidiagonal.mp hab).1
    obtain ⟨i,_,rfl⟩ := (Nat.dvd_prime_pow hp).mp (show a ∣ p^k from ⟨b, h.symm⟩)
    obtain ⟨j,_,rfl⟩ := (Nat.dvd_prime_pow hp).mp (show b ∣ p^k from ⟨p^i, by rw [← h, mul_comm]⟩)
    have hij : i+j = k := Nat.pow_right_injective hp.one_lt (by change p^(i+j) = p^k; rwa [pow_add])
    exact Finset.mem_map.mpr ⟨(i,j),Finset.mem_antidiagonal.mpr hij,rfl⟩
  rw [ArithmeticFunction.mul_apply, hset, Finset.sum_map]
  rfl

/-- The inverse-square-root mollifier is normalized, bounded uniformly in every
coefficient, and its Dirichlet convolution square is exactly the Möbius function. -/
theorem spectralLineJet_selbergHalfMoebius_spec :
    spectralLineJet_selbergHalfMoebius 1 = 1 ∧
    (∀ n, |spectralLineJet_selbergHalfMoebius n| ≤ 1) ∧
    spectralLineJet_selbergHalfMoebius * spectralLineJet_selbergHalfMoebius = (μ : ArithmeticFunction ℝ) := by
  have hm := spectralLineJet_selbergHalfMoebius_mult
  refine ⟨hm.1, ?_, ?_⟩
  · intro n
    by_cases h : n = 0
    · simp [h]
    change |if n = 0 then 0 else n.factorization.prod _| ≤ 1
    simp only [h, ite_false, Finsupp.prod, Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ ↦ abs_nonneg _) fun p _ ↦ spectralLineJet_selbergHalfCoeff_bound _
  · apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ (hm.mul hm)
      _ ArithmeticFunction.isMultiplicative_moebius.intCast).mpr
    intro p k hp
    rw [spectralLineJet_dirichlet_prime_power _ _ hp]
    simp_rw [spectralLineJet_selbergHalfMoebius_prime_pow hp]
    rw [spectralLineJet_selbergHalfCoeff_square]
    by_cases hk : k = 0
    · simp [hk]
    simp only [hk, ite_false]
    change _ = ((μ (p^k) : ℤ) : ℝ)
    rw [ArithmeticFunction.moebius_apply_prime_pow hp hk]
    split <;> norm_num

/-- Truncate a real arithmetic coefficient sequence to the positive integers through a cutoff. -/
def spectralLineJet_selbergCut (N : ℕ) (b : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n ∈ Finset.Icc 1 N then b n else 0, by simp⟩

/-- Multiplication of actual finite critical-line Dirichlet polynomials groups the
frequencies by the ordinary Dirichlet convolution of their coefficients. -/
private theorem spectralLineJet_selberg_dirichlet_product (L N : ℕ) (a b : ArithmeticFunction ℝ)
    (ha : ∀ n, L < n → a n = 0) (hb : ∀ n, N < n → b n = 0) (t : ℝ) :
    (∑ k ∈ Finset.Icc 1 L, (a k : ℂ) * mode(k,t)) *
      (∑ d ∈ Finset.Icc 1 N, (b d : ℂ) * mode(d,t)) =
      ∑ m ∈ Finset.Icc 1 (L*N), ((a*b) m : ℂ) * mode(m,t) := by
  classical
  let S := Finset.Icc 1 L ×ˢ Finset.Icc 1 N
  let idx (p : ℕ × ℕ) := p.1 * p.2
  let term (p : ℕ × ℕ) := ((a p.1 * b p.2 : ℝ) : ℂ) * mode(idx p,t)
  have hmap : ∀ p ∈ S, idx p ∈ Finset.Icc 1 (L*N) := by
    intro p hp
    obtain ⟨hk,hd⟩ := Finset.mem_product.mp hp
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hd).1,
      Nat.mul_le_mul (Finset.mem_Icc.mp hk).2 (Finset.mem_Icc.mp hd).2⟩
  have hfib (m : ℕ) (hm : m ∈ Finset.Icc 1 (L*N)) :
      ∑ p ∈ S with idx p = m, term p = ((a*b) m : ℂ) * mode(m,t) := by
    have hm₀ : 0 < m := (Finset.mem_Icc.mp hm).1
    have hsub : S.filter (fun p ↦ idx p = m) ⊆ m.divisorsAntidiagonal := by
      intro p hp
      exact Nat.mem_divisorsAntidiagonal.mpr ⟨(Finset.mem_filter.mp hp).2,hm₀.ne'⟩
    rw [Finset.sum_subset hsub]
    · rw [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      simp only [term,idx,(Nat.mem_divisorsAntidiagonal.mp hp).1]
    · intro p hp hnot
      have hp' := (Nat.mem_divisorsAntidiagonal.mp hp).1
      have hne : p ∉ S := fun h ↦ hnot (Finset.mem_filter.mpr ⟨h,hp'⟩)
      have h₁ : 0 < p.1 := Nat.pos_of_ne_zero fun h ↦ hm₀.ne' (by rw [← hp',h,zero_mul])
      have h₂ : 0 < p.2 := Nat.pos_of_ne_zero fun h ↦ hm₀.ne' (by rw [← hp',h,mul_zero])
      have ho : L < p.1 ∨ N < p.2 := by
        by_contra! H
        exact hne (Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨h₁,H.1⟩,Finset.mem_Icc.mpr ⟨h₂,H.2⟩⟩)
      rcases ho with h | h
      · simp [term, ha _ h]
      · simp [term, hb _ h]
  calc _ = ∑ p ∈ S, term p := by
         rw [Finset.sum_mul_sum]
         simp only [S,Finset.sum_product]
         refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun d _ ↦ ?_
         dsimp only [term,idx]
         rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Complex.ofReal_mul]
         ring
       _ = ∑ m ∈ Finset.Icc 1 (L*N), ∑ p ∈ S with idx p = m, term p :=
         (Finset.sum_fiberwise_of_maps_to hmap term).symm
       _ = _ := Finset.sum_congr rfl hfib

private theorem spectralLineJet_selberg_cut_tail (L N : ℕ) (a b : ArithmeticFunction ℝ)
    (ha : ∀ n, L < n → a n = 0) (hb : ∀ n, N < n → b n = 0) :
    ∀ n, L*N < n → (a*b) n = 0 := by
  intro n hn
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have heq := (Nat.mem_divisorsAntidiagonal.mp hp).1
  by_cases h : L < p.1
  · simp [ha _ h]
  · have h' : N < p.2 := by
      by_contra! h₁
      exact hn.not_ge (heq ▸ Nat.mul_le_mul (le_of_not_gt h) h₁)
    simp [hb _ h']

/-- Dirichlet convolution with a length-`N` cutoff is unaffected by a cofactor
coprime to every integer through `N`, provided its complementary divisor is
itself at most `N`. This also controls indices larger than the mollifier cutoff. -/
private theorem spectralLineJet_selberg_cut_rough {N r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hrN : r ≤ N) (hrough : ∀ d, d ≤ N → 0 < d → d.Coprime s)
    (b g f : ArithmeticFunction ℝ)
    (hgf : ∀ u, u ∣ r → g (u*s) = f u) :
    (spectralLineJet_selbergCut N b * g) (r*s) = (b*f) r := by
  classical
  have hn := Nat.mul_pos hr hs
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply,
    ← Nat.map_div_right_divisors, ← Nat.map_div_right_divisors, Finset.sum_map, Finset.sum_map]
  let S := (r*s).divisors
  let Q (d : ℕ) := spectralLineJet_selbergCut N b d * g (r*s/d)
  change (∑ d ∈ S, Q d) = ∑ d ∈ r.divisors, b d * f (r/d)
  have hsub : r.divisors ⊆ S := Nat.divisors_subset_of_dvd hn.ne' (dvd_mul_right _ _)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun d hd ↦ ?_
    have hdiv := (Nat.mem_divisors.mp hd).1
    have hpos := Nat.pos_of_dvd_of_pos hdiv hr
    have hN := (Nat.le_of_dvd hr hdiv).trans hrN
    have hq : r*s/d = (r/d)*s := by rw [Nat.mul_comm r s, Nat.mul_div_assoc s hdiv, Nat.mul_comm]
    simp only [Q,hq,hgf _ (Nat.div_dvd_of_dvd hdiv)]
    change (if d ∈ Finset.Icc 1 N then b d else 0) * _ = _
    rw [ite_eq_left (Finset.mem_Icc.mpr ⟨hpos,hN⟩)]
  · intro d hd hnot
    have hdv := (Nat.mem_divisors.mp hd).1
    have hd₀ := Nat.pos_of_dvd_of_pos hdv hn
    have hN : ¬d ≤ N := fun h ↦ hnot (Nat.mem_divisors.mpr ⟨(hrough d h hd₀).dvd_of_dvd_mul_right hdv,hr.ne'⟩)
    simp [Q,spectralLineJet_selbergCut,hN]

/-- The coefficient of frequency `m` after grouping the tapered zeta polynomial
and the square of the same inverse-square-root mollifier of length `N`. -/
def spectralLineJet_selbergGroupedCoefficient (L N : ℕ) (t : ℝ) : ArithmeticFunction ℝ :=
  let B := spectralLineJet_selbergCut N spectralLineJet_selbergHalfMoebius
  B * (B * spectralLineJet_selbergCut L (fun k ↦ min 1 (max 0 (3*t/Real.pi - k + 1))))

/-- The grouped coefficients occur in the actual finite model, simultaneously at
every height and for both cutoff parameters. -/
theorem spectralLineJet_selbergGrouped_expansion (L N : ℕ) (t : ℝ) :
    spectralLineJet_selbergFiniteZeta L t *
      (∑ d ∈ Finset.Icc 1 N, (spectralLineJet_selbergHalfMoebius d : ℂ) * mode(d,t))^2 =
      ∑ m ∈ Finset.Icc 1 (N*(N*L)), (spectralLineJet_selbergGroupedCoefficient L N t m : ℂ) * mode(m,t) := by
  let a (k : ℕ) := min 1 (max 0 (3*t/Real.pi - k + 1))
  let A := spectralLineJet_selbergCut L a
  let B := spectralLineJet_selbergCut N spectralLineJet_selbergHalfMoebius
  have cut (K : ℕ) (f : ℕ → ℝ) : ∀ d, K < d → spectralLineJet_selbergCut K f d = 0 := by
    intro d hd
    simp [spectralLineJet_selbergCut, hd.not_ge]
  have hsum (K : ℕ) (f : ℕ → ℝ) :
      (∑ k ∈ Finset.Icc 1 K, (spectralLineJet_selbergCut K f k : ℂ)*mode(k,t)) =
      ∑ k ∈ Finset.Icc 1 K, (f k : ℂ)*mode(k,t) := by
    exact Finset.sum_congr rfl fun k hk ↦ by simp only [spectralLineJet_selbergCut, ArithmeticFunction.coe_mk, ite_eq_left hk]
  rw [spectralLineJet_selbergFiniteZeta]
  change (∑ k ∈ Finset.Icc 1 L, (a k : ℂ)*mode(k,t)) * _^2 = _
  rw [← hsum L a, ← hsum N spectralLineJet_selbergHalfMoebius, sq, mul_comm, mul_assoc]
  rw [spectralLineJet_selberg_dirichlet_product N L B A (cut _ _) (cut _ _) t,
    spectralLineJet_selberg_dirichlet_product N (N*L) B (B*A) (cut _ _)
      (spectralLineJet_selberg_cut_tail N L B A (cut _ _) (cut _ _)) t]
  rfl

/-- In the flat part of the taper, a frequency with smooth part `r ≤ N` and
rough cofactor `s` survives with coefficient one exactly when `r = 1`. -/
theorem spectralLineJet_selbergGrouped_on_rough {L N r s : ℕ} {t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrN : r ≤ N) (hmL : r*s ≤ L)
    (hmt : ((r*s : ℕ) : ℝ) ≤ 3*t/Real.pi) (hrough : ∀ d, d ≤ N → 0 < d → d.Coprime s) :
    spectralLineJet_selbergGroupedCoefficient L N t (r*s) = if r = 1 then 1 else 0 := by
  let A := spectralLineJet_selbergCut L (fun k ↦ min 1 (max 0 (3*t/Real.pi - k + 1)))
  let B := spectralLineJet_selbergCut N spectralLineJet_selbergHalfMoebius
  let Z : ArithmeticFunction ℝ := ζ
  let b := spectralLineJet_selbergHalfMoebius
  have ha (u : ℕ) (hu : u ∣ r) : A (u*s) = Z u := by
    have hp := Nat.pos_of_dvd_of_pos hu hr
    have hul : u*s ≤ r*s := Nat.mul_le_mul_right s (Nat.le_of_dvd hr hu)
    have hit : u*s ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨Nat.mul_pos hp hs,hul.trans hmL⟩
    have hut : ((u*s : ℕ) : ℝ) ≤ 3*t/Real.pi := (Nat.cast_le.mpr hul).trans hmt
    have hlin : (1:ℝ) ≤ 3*t/Real.pi - ↑(u*s) + 1 := by linarith
    change (if u*s ∈ Finset.Icc 1 L then min 1 (max 0 (3*t/Real.pi - ↑(u*s) + 1)) else 0) = _
    rw [ite_eq_left hit, min_eq_left (hlin.trans (le_max_right _ _))]
    simp [Z, ArithmeticFunction.zeta_apply_ne hp.ne']
  have hba (u : ℕ) (hu : u ∣ r) : (B*A) (u*s) = (b*Z) u :=
    spectralLineJet_selberg_cut_rough (Nat.pos_of_dvd_of_pos hu hr) hs ((Nat.le_of_dvd hr hu).trans hrN)
      hrough b A Z fun v hv ↦ ha v (hv.trans hu)
  have he := spectralLineJet_selberg_cut_rough hr hs hrN hrough b (B*A) (b*Z) hba
  change (B*(B*A)) (r*s) = _
  change (B*(B*A)) (r*s) = (b*(b*Z)) r at he
  rw [he, ← mul_assoc, show b*b = (μ : ArithmeticFunction ℝ) from spectralLineJet_selbergHalfMoebius_spec.2.2]
  exact congrArg (fun f : ArithmeticFunction ℝ ↦ f r) ArithmeticFunction.coe_moebius_mul_coe_zeta

/-- The entire low-frequency projection is identically one once the taper
has passed the mollifier cutoff. This includes every cross term in that band. -/
theorem spectralLineJet_selbergGrouped_low {L N : ℕ} (hN : 1 ≤ N) (hL : N ≤ L) {t : ℝ}
    (ht : (N : ℝ) ≤ 3*t/Real.pi) :
    ∑ m ∈ Finset.Icc 1 N, (spectralLineJet_selbergGroupedCoefficient L N t m : ℂ)*mode(m,t) = 1 := by
  have hcoef (m : ℕ) (hm : m ∈ Finset.Icc 1 N) :
      spectralLineJet_selbergGroupedCoefficient L N t m = if m = 1 then 1 else 0 := by
    obtain ⟨hp,hb⟩ := Finset.mem_Icc.mp hm
    simpa using spectralLineJet_selbergGrouped_on_rough (s := 1) hp Nat.zero_lt_one hb
      (by simpa using hb.trans hL) (by simpa using (Nat.cast_le.mpr hb).trans ht) (by simp)
  rw [Finset.sum_eq_single 1]
  · simp [hcoef 1 (Finset.left_mem_Icc.mpr hN)]
  · intro m hm hn
    simp [hcoef _ hm, hn]
  · simp [hN]

/-- The surviving rough frequencies have bounded harmonic mass out to any
fixed power of the mollifier length. Multiplication by any integer up to `N`
gives pairwise disjoint sets of integers. -/
private theorem spectralLineJet_selberg_rough_mass {N X : ℕ} (hN : 0 < N) (R : Finset ℕ)
    (hR : R ⊆ Finset.Icc 1 X) (hrough : ∀ m ∈ R, ∀ d, d ≤ N → 0 < d → d.Coprime m) :
    (∑ m ∈ R, (m : ℝ)⁻¹) ≤ (1 + Real.log (N*X : ℕ)) / Real.log (N+1 : ℕ) := by
  classical
  let S := R ×ˢ Finset.Icc 1 N
  let f (p : ℕ × ℕ) := p.1*p.2
  have inj : Set.InjOn f ↑S := by
    rintro ⟨m,d⟩ hmd ⟨n,e⟩ hne he
    obtain ⟨hm,hd⟩ := Finset.mem_product.mp hmd
    obtain ⟨hn,hen⟩ := Finset.mem_product.mp hne
    obtain ⟨hdp,hdN⟩ := Finset.mem_Icc.mp hd
    obtain ⟨hep,heN⟩ := Finset.mem_Icc.mp hen
    change m*d = n*e at he
    have hdv : d ∣ e := (hrough n hn d hdN hdp).dvd_of_dvd_mul_left (he ▸ dvd_mul_left d m)
    have hev : e ∣ d := (hrough m hm e heN hep).dvd_of_dvd_mul_left (he ▸ dvd_mul_left e n)
    have heq := Nat.dvd_antisymm hdv hev
    subst e
    exact Prod.ext (Nat.mul_right_cancel hdp he) rfl
  have hsub : S.image f ⊆ Finset.Icc 1 (N*X) := by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hm,hd⟩ := Finset.mem_product.mp hp
    obtain ⟨hmp,hmX⟩ := Finset.mem_Icc.mp (hR hm)
    obtain ⟨hdp,hdN⟩ := Finset.mem_Icc.mp hd
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hmp hdp, by simpa [Nat.mul_comm] using Nat.mul_le_mul hmX hdN⟩
  have he : (∑ m ∈ R, (m : ℝ)⁻¹) * (∑ d ∈ Finset.Icc 1 N, (d : ℝ)⁻¹) ≤
      ∑ k ∈ Finset.Icc 1 (N*X), (k : ℝ)⁻¹ := by
    calc _ = ∑ p ∈ S, ((f p : ℕ) : ℝ)⁻¹ := by simp [S, f, Finset.sum_mul_sum, Finset.sum_product, mul_comm]
         _ = ∑ k ∈ S.image f, (k : ℝ)⁻¹ := (Finset.sum_image (f := fun k : ℕ ↦ (k : ℝ)⁻¹) inj).symm
         _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
  have hh (n : ℕ) : (↑(harmonic n) : ℝ) = ∑ k ∈ Finset.Icc 1 n, (k : ℝ)⁻¹ := by
    simp [harmonic_eq_sum_Icc]
  apply (le_div_iff₀ (Real.log_pos (by exact_mod_cast (by omega : 1 < N+1)))).mpr
  calc _ ≤ (∑ m ∈ R, (m : ℝ)⁻¹) * (harmonic N : ℝ) := by gcongr; exact log_add_one_le_harmonic N
       _ ≤ (harmonic (N*X) : ℝ) := by simpa only [hh] using he
       _ ≤ _ := harmonic_le_one_add_log _

/-- Integer logarithmic frequencies through `X` have separation at least `1/X`. -/
private theorem spectralLineJet_selberg_log_gap {X m n : ℕ} (hm : m ∈ Finset.Icc 1 X)
    (hn : n ∈ Finset.Icc 1 X) (hne : m ≠ n) : (X : ℝ)⁻¹ ≤ |Real.log m - Real.log n| := by
  have oneSide {i j : ℕ} (hi : 0 < i) (hj : j ≤ X) (hij : i < j) :
      (X : ℝ)⁻¹ ≤ Real.log j - Real.log i := by
    have hp : 0 < (i : ℝ) := by exact_mod_cast hi
    have hq : 0 < (j : ℝ) := by exact_mod_cast hi.trans hij
    have hx : (j : ℝ) ≤ X := by exact_mod_cast hj
    have hdiff : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hq hp)
    rw [inv_div, Real.log_div hq.ne' hp.ne'] at hlog
    calc (X : ℝ)⁻¹ ≤ (j : ℝ)⁻¹ := inv_anti₀ hq hx
         _ ≤ 1 - i / j := by rw [← one_div, le_sub_iff_add_le, ← add_div, div_le_one hq]; linarith
         _ ≤ _ := hlog
  rcases lt_or_gt_of_ne hne with h | h
  · rw [abs_sub_comm]
    exact (oneSide (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).2 h).trans (le_abs_self _)
  · exact (oneSide (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hm).2 h).trans (le_abs_self _)

/-- Each non-diagonal term of a finite critical-line Dirichlet square has
a bounded primitive, uniformly in the endpoints. -/
private theorem spectralLineJet_selberg_pair_bound {X m n : ℕ} (hm : m ∈ Finset.Icc 1 X)
    (hn : n ∈ Finset.Icc 1 X) (hne : m ≠ n) (a b : ℝ) :
    ‖∫ t in a..b, mode(m,t) * (starRingEnd ℂ) (mode(n,t))‖ ≤
      (2 * X) * (1 / Real.sqrt m) * (1 / Real.sqrt n) := by
  have hmpos := (Finset.mem_Icc.mp hm).1
  have hnpos := (Finset.mem_Icc.mp hn).1
  have hx : 0 < (X : ℝ) := by exact_mod_cast (show 0 < m from hmpos).trans_le (Finset.mem_Icc.mp hm).2
  let l := Real.log m - Real.log n
  let c : ℂ := -Complex.I * (l : ℂ)
  have hgap : (X : ℝ)⁻¹ ≤ |l| := spectralLineJet_selberg_log_gap hm hn hne
  have hl := (inv_pos.mpr hx).trans_le hgap
  have hc : ‖c‖ = |l| := by simp [c]
  have hcne : c ≠ 0 := norm_pos_iff.mp (hc ▸ hl)
  have twist (k : ℕ) (hk : 0 < k) (t : ℝ) :
      mode(k,t) = mode(k,0) * Complex.exp ((-Complex.I * (Real.log k : ℂ)) * t) := by
    rw [cpow_neg_criticalLinePoint_eq_mode hk]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg k)]
  have hmode (t : ℝ) : mode(m,t) * (starRingEnd ℂ) (mode(n,t)) =
      (mode(m,0) * (starRingEnd ℂ) (mode(n,0))) * Complex.exp (c*t) := by
    rw [twist m hmpos t, twist n hnpos t, map_mul, ← Complex.exp_conj]
    rw [show ∀ x y z w : ℂ, x*y*(z*w) = (x*z)*(y*w) from fun _ _ _ _ ↦ by ring, ← Complex.exp_add]
    congr 2
    simp only [c, l, Complex.ofReal_sub, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, neg_neg]
    ring
  rw [intervalIntegral.integral_congr (fun t _ ↦ hmode t)]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hcne, norm_mul, norm_mul,
    norm_div, hc, RCLike.norm_conj, norm_cpow_neg_criticalLinePoint hmpos,
    norm_cpow_neg_criticalLinePoint hnpos]
  have eb (t : ℝ) : ‖Complex.exp (c*t)‖ = 1 := by simp [Complex.norm_exp,c,Complex.mul_re]
  have hnum : ‖Complex.exp (c*b) - Complex.exp (c*a)‖ ≤ 2 := by
    exact (norm_sub_le _ _).trans (by rw [eb,eb]; norm_num)
  have hbound : ‖Complex.exp (c*b) - Complex.exp (c*a)‖ / |l| ≤ 2*X := by
    apply (div_le_iff₀ hl).mpr
    have h' : 1 ≤ (X : ℝ) * |l| := by simpa [hx.ne'] using mul_le_mul_of_nonneg_left hgap hx.le
    linarith
  calc _ ≤ (1 / Real.sqrt m * (1 / Real.sqrt n)) * (2*X) := by gcongr
       _ = _ := by ring

/-- A finite set of modes below `X` has a mean-square bound with its exact
diagonal mass and a uniform `8 X²` off-diagonal remainder. -/
private theorem spectralLineJet_selberg_modes_mean {X : ℕ} (R : Finset ℕ)
    (hR : R ⊆ Finset.Icc 1 X) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ‖∑ m ∈ R, mode(m,t)‖^2) ≤
      (b-a) * (∑ k ∈ R, (k : ℝ)⁻¹) + 8*(X:ℝ)^2 := by
  classical
  let K (p : ℕ × ℕ) (t : ℝ) := mode(p.1,t) * (starRingEnd ℂ) (mode(p.2,t))
  let S := R ×ˢ R
  have hex (t : ℝ) : ((‖∑ m ∈ R, mode(m,t)‖^2 : ℝ) : ℂ) = ∑ p ∈ S, K p t := by
    simp only [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum, S, Finset.sum_product, K]
  have heint : ((∫ t in a..b, ‖∑ m ∈ R, mode(m,t)‖^2 : ℝ) : ℂ) = ∑ p ∈ S, ∫ t in a..b, K p t := by
    rw [← intervalIntegral.integral_ofReal, intervalIntegral.integral_congr fun t _ ↦ hex t,
      intervalIntegral.integral_finsetSum]
    intro p hp
    obtain ⟨hm,hn⟩ := Finset.mem_product.mp hp
    exact ((continuous_cpow_neg_criticalLinePoint (Finset.mem_Icc.mp (hR hm)).1).mul
      (Complex.continuous_conj.comp (continuous_cpow_neg_criticalLinePoint (Finset.mem_Icc.mp (hR hn)).1))).intervalIntegrable ..
  have hpair (p : ℕ × ℕ) (hp : p ∈ S) :
      ‖∫ t in a..b, K p t‖ ≤ (if p.1 = p.2 then (b-a)*(p.1 : ℝ)⁻¹ else 0) +
        2*X * (1 / Real.sqrt p.1) * (1 / Real.sqrt p.2) := by
    obtain ⟨hm, hn⟩ := Finset.mem_product.mp hp
    rcases p with ⟨m,n⟩
    change ‖∫ t in a..b, mode(m,t) * (starRingEnd ℂ) (mode(n,t))‖ ≤ _
    by_cases h : m = n
    · subst n
      have hd (t : ℝ) : mode(m,t) * (starRingEnd ℂ) (mode(m,t)) = (↑((m : ℝ)⁻¹) : ℂ) := by
        rw [Complex.mul_conj', norm_cpow_neg_criticalLinePoint (Finset.mem_Icc.mp (hR hm)).1,
          ← Complex.ofReal_pow, one_div, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp only [hd, intervalIntegral.integral_const, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hab), Complex.norm_real, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (m:ℝ)⁻¹),
        ite_true]
      exact le_add_of_nonneg_right (by positivity)
    · simpa [h] using spectralLineJet_selberg_pair_bound (hR hm) (hR hn) h a b
  have hcoef : ∑ m ∈ R, 1 / Real.sqrt m ≤ 2*Real.sqrt X :=
    (Finset.sum_le_sum_of_subset_of_nonneg hR fun _ _ _ ↦ by positivity).trans (sum_Icc_one_div_sqrt_le_two_mul_sqrt _)
  have hdiag : (∑ p ∈ S, if p.1 = p.2 then (b-a)*(p.1 : ℝ)⁻¹ else 0) =
      (b-a) * (∑ k ∈ R, (k : ℝ)⁻¹) := by
    rw [Finset.mul_sum]
    simp [S,Finset.sum_product]
  have hoff : (∑ p ∈ S, 2*X*(1/Real.sqrt p.1)*(1/Real.sqrt p.2)) ≤ 8*(X:ℝ)^2 := by
    calc _ = 2*X*(∑ m ∈ R, 1 / Real.sqrt m)^2 := by
           rw [sq, Finset.sum_mul_sum]
           simp [S,Finset.sum_product,Finset.mul_sum,mul_assoc]
         _ ≤ 2*X*(2*Real.sqrt X)^2 := by gcongr
         _ = _ := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg X)]; ring
  calc _ ≤ ‖((∫ t in a..b, ‖∑ m ∈ R, mode(m,t)‖^2 : ℝ) : ℂ)‖ := by
         rw [Complex.norm_real,Real.norm_eq_abs]; exact le_abs_self _
       _ ≤ ∑ p ∈ S, ‖∫ t in a..b, K p t‖ := heint ▸ norm_sum_le _ _
       _ ≤ _ := (Finset.sum_le_sum hpair).trans (by rw [Finset.sum_add_distrib,hdiag]; gcongr)

/-- Mean-square control of the rough-frequency projection of the actual
grouped finite model, including all cross terms. For `X ≤ N^A` and
`X² ≤ b-a` its second moment is `O_A(b-a)`, uniformly in the three cutoffs. -/
theorem spectralLineJet_selbergGrouped_rough_mean {L N X : ℕ} (hN : 0 < N)
    (R : Finset ℕ) (hR : R ⊆ Finset.Icc 1 X)
    (hrough : ∀ m ∈ R, ∀ d, d ≤ N → 0 < d → d.Coprime m)
    (hL : X ≤ L) {a b : ℝ} (hab : a ≤ b) (ha : (X : ℝ) ≤ 3*a/Real.pi) :
    (∫ t in a..b, ‖∑ m ∈ R, (spectralLineJet_selbergGroupedCoefficient L N t m : ℂ)*mode(m,t)‖^2) ≤
      (b-a) * ((1 + Real.log (N*X : ℕ)) / Real.log (N+1 : ℕ)) + 8*(X:ℝ)^2 := by
  have he (t : ℝ) (ht : t ∈ uIcc a b) (m : ℕ) (hm : m ∈ R) :
      spectralLineJet_selbergGroupedCoefficient L N t m = 1 := by
    rw [uIcc_of_le hab] at ht
    obtain ⟨hp,hmX⟩ := Finset.mem_Icc.mp (hR hm)
    have hmt : (m:ℝ) ≤ 3*t/Real.pi := (Nat.cast_le.mpr hmX).trans (ha.trans (by gcongr; exact ht.1))
    simpa using spectralLineJet_selbergGrouped_on_rough (r := 1) (s := m) Nat.zero_lt_one hp hN
      (by simpa using hmX.trans hL) (by simpa using hmt) (hrough m hm)
  calc _ = ∫ t in a..b, ‖∑ m ∈ R, mode(m,t)‖^2 := by
         apply intervalIntegral.integral_congr
         intro t ht
         have H : (∑ m ∈ R, (spectralLineJet_selbergGroupedCoefficient L N t m : ℂ)*mode(m,t)) =
             ∑ m ∈ R, mode(m,t) := Finset.sum_congr rfl fun m hm ↦ by rw [he t ht m hm]; simp
         exact congrArg (fun z : ℂ ↦ ‖z‖^2) H
       _ ≤ _ := (spectralLineJet_selberg_modes_mean R hR hab).trans
         (add_le_add_left (mul_le_mul_of_nonneg_left (spectralLineJet_selberg_rough_mass hN R hR hrough)
           (sub_nonneg.mpr hab)) _)

/-- Averaging a continuous function on sliding length-`h` windows costs at
most `h²` times its second moment on the enlarged interval. -/
private theorem spectralLineJet_selberg_window_L2 (f : ℝ → ℝ) (hf : Continuous f)
    {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h) :
    (∫ t in a..b, (∫ u in t..t+h, f u)^2) ≤ h^2 * ∫ u in a..b+h, (f u)^2 := by
  rcases hh.eq_or_lt with rfl | hhpos
  · simp
  let P (u : ℝ) := ∫ v in a..u, (f v)^2
  have hp : Continuous P := intervalIntegral.continuous_primitive (fun _ _ ↦ (hf.pow 2).intervalIntegrable ..) a
  have hps (t : ℝ) : (∫ v in t..t+h, (f v)^2) = P (t+h) - P t :=
    (intervalIntegral.integral_interval_sub_left ((hf.pow 2).intervalIntegrable ..) ((hf.pow 2).intervalIntegrable ..)).symm
  have hcs (t : ℝ) : (∫ v in t..t+h, f v)^2 ≤ h*(P (t+h)-P t) := by
    let J := ∫ v in t..t+h, f v
    have he (v : ℝ) : (h*f v - J)^2 = h^2*(f v)^2 - (2*h*J)*f v + J^2 := by ring
    have hpos : 0 ≤ ∫ v in t..t+h, (h*f v-J)^2 :=
      intervalIntegral.integral_nonneg (by linarith) (fun _ _ ↦ by positivity)
    simp_rw [he] at hpos
    have hs : Continuous (fun v ↦ h^2*(f v)^2) := continuous_const.mul (hf.pow 2)
    have hl : Continuous (fun v ↦ (2*h*J)*f v) := continuous_const.mul hf
    rw [intervalIntegral.integral_add (f := fun v ↦ h^2*(f v)^2 - (2*h*J)*f v) (g := fun _ ↦ J^2)
        ((hs.sub hl).intervalIntegrable ..) intervalIntegrable_const,
      intervalIntegral.integral_sub (hs.intervalIntegrable ..) (hl.intervalIntegrable ..),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      hps t, smul_eq_mul] at hpos
    change J^2 ≤ _
    change 0 ≤ h^2*(P (t+h)-P t) - 2*h*J*J + (t+h-t)*J^2 at hpos
    by_contra! hc
    nlinarith only [hpos, mul_pos hhpos (sub_pos.mpr hc)]
  have hdiff : (∫ t in a..b, P (t+h) - P t) = (∫ u in b..b+h, P u) - ∫ u in a..a+h, P u := by
    have hp' : Continuous (fun t ↦ P (t+h)) := hp.comp (continuous_id.add_const h)
    rw [intervalIntegral.integral_sub (hp'.intervalIntegrable ..) (hp.intervalIntegrable ..),
      intervalIntegral.integral_comp_add_right]
    exact intervalIntegral.integral_interval_sub_interval_comm' (hp.intervalIntegrable ..) (hp.intervalIntegrable ..) (hp.intervalIntegrable ..)
  have hlast : (∫ u in b..b+h, P u) ≤ h * P (b+h) := by
    calc _ ≤ ∫ _ in b..b+h, P (b+h) := by
           apply intervalIntegral.integral_mono_on (by linarith) (hp.intervalIntegrable ..) intervalIntegrable_const
           intro u hu
           exact intervalIntegral.integral_mono_interval le_rfl (hab.trans hu.1) hu.2
             (.of_forall fun _ ↦ sq_nonneg _) ((hf.pow 2).intervalIntegrable ..)
         _ = _ := by simp
  have hfirst : 0 ≤ ∫ u in a..a+h, P u := intervalIntegral.integral_nonneg (by linarith)
    (fun u hu ↦ intervalIntegral.integral_nonneg hu.1 fun _ _ ↦ sq_nonneg _)
  calc _ ≤ ∫ t in a..b, h*(P (t+h)-P t) := intervalIntegral.integral_mono_on hab
         (((spectralLineJet_selberg_continuousWindow hf h).pow 2).intervalIntegrable ..)
         ((continuous_const.mul ((hp.comp (continuous_id.add_const h)).sub hp)).intervalIntegrable ..) fun t _ ↦ hcs t
       _ = h * ((∫ u in b..b+h, P u) - ∫ u in a..a+h, P u) := by rw [intervalIntegral.integral_const_mul,hdiff]
       _ ≤ h*(h*P (b+h)) := mul_le_mul_of_nonneg_left (by linarith) hhpos.le
       _ = _ := by simp [P, sq, mul_assoc]

/-- The gamma-weighted absolute short-window second moment of the rough
frequency projection. All off-diagonal correlations are included. On a dyadic
interval near `H`, the bound is `O_A(h² √H)` for `X ≤ N^A`, `X² ≤ H`
and `0 ≤ h ≤ H`. The constant is uniform in the set of rough frequencies. -/
theorem spectralLineJet_selbergGrouped_rough_window :
    ∃ C > (0:ℝ), ∀ {H a b h : ℝ} (_ : 0 < H) (_ : 0 ≤ a) (_ : a ≤ b) (_ : 0 ≤ h)
      {L N X : ℕ} (_ : 0 < N) (R : Finset ℕ) (_ : R ⊆ Finset.Icc 1 X),
      (∀ m ∈ R, ∀ d, d ≤ N → 0 < d → d.Coprime m) → X ≤ L → (X:ℝ) ≤ 3*a/Real.pi →
      (∫ t in a..b, (∫ u in t..t+h,
        ‖Complex.Gamma (1/4 + ((u/2 : ℝ) : ℂ)*Complex.I)‖ * Real.exp ((Real.pi/4 - 1/(2*H))*u) *
        ‖∑ m ∈ R, (spectralLineJet_selbergGroupedCoefficient L N u m : ℂ)*mode(m,u)‖)^2) ≤
      h^2 * (C/(1+a)^(1/4:ℝ))^2 *
        ((b+h-a)*((1+Real.log (N*X : ℕ))/Real.log (N+1 : ℕ)) + 8*(X:ℝ)^2) := by
  obtain ⟨C,hC,hgamma⟩ := spectralLineJet_selbergGamma_upper
  refine ⟨C,hC,?_⟩
  intro H a b h hH ha hab hh L N X hN R hR hrough hL hX
  let W (u : ℝ) := ‖Complex.Gamma (criticalLineGammaArgument u)‖ * Real.exp ((Real.pi/4-1/(2*H))*u)
  let P (u : ℝ) := ∑ m ∈ R, mode(m,u)
  let D := C/(1+a)^(1/4:ℝ)
  have hW : Continuous W := spectralLineJet_selbergGamma_continuous.norm.mul (by fun_prop)
  have hP : Continuous P := continuous_finsetSum _ fun m hm ↦
    continuous_cpow_neg_criticalLinePoint (Finset.mem_Icc.mp (hR hm)).1
  have hbound (u : ℝ) (hu : a ≤ u) : W u ≤ D := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos (by linarith : 0 < 1+a) _)).mpr
    calc _ ≤ W u * (1+u)^(1/4:ℝ) := by
           apply mul_le_mul_of_nonneg_left _ (by dsimp [W]; positivity)
           exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
         _ ≤ C := hgamma H hH u (ha.trans hu)
  have hmajor (u : ℝ) (hu : a ≤ u) : (W u * ‖P u‖)^2 ≤ D^2 * ‖P u‖^2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by dsimp [W]; positivity) (hbound u hu) 2) (sq_nonneg _)
  have hmodes (u : ℝ) (hu : a ≤ u) :
      ∑ m ∈ R, (spectralLineJet_selbergGroupedCoefficient L N u m : ℂ)*mode(m,u) = P u := by
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    obtain ⟨hmpos,hmX⟩ := Finset.mem_Icc.mp (hR hm)
    have hmt : (m:ℝ) ≤ 3*u/Real.pi := (Nat.cast_le.mpr hmX).trans (hX.trans (by gcongr))
    have hc := spectralLineJet_selbergGrouped_on_rough (r := 1) (s := m) Nat.zero_lt_one hmpos hN
      (by simpa using hmX.trans hL) (by simpa using hmt) (hrough m hm)
    simp only [one_mul,ite_true] at hc
    simp [hc]
  have hb' : a ≤ b+h := by linarith
  calc _ = ∫ t in a..b, (∫ u in t..t+h, W u * ‖P u‖)^2 := by
         apply intervalIntegral.integral_congr
         intro t ht
         rw [uIcc_of_le hab] at ht
         apply congrArg (fun x : ℝ ↦ x^2)
         apply intervalIntegral.integral_congr
         intro u hu
         rw [uIcc_of_le (by linarith : t ≤ t+h)] at hu
         simp only [hmodes u (ht.1.trans hu.1),W,criticalLineGammaArgument]
       _ ≤ h^2 * ∫ u in a..b+h, (W u * ‖P u‖)^2 :=
         spectralLineJet_selberg_window_L2 _ (hW.mul hP.norm) hab hh
       _ ≤ h^2 * ∫ u in a..b+h, D^2 * ‖P u‖^2 := by
         apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
         exact intervalIntegral.integral_mono_on hb' (((hW.mul hP.norm).pow 2).intervalIntegrable ..)
           ((continuous_const.mul (hP.norm.pow 2)).intervalIntegrable ..) fun u hu ↦ hmajor u hu.1
       _ = (h^2*D^2) * ∫ u in a..b+h, ‖P u‖^2 := by rw [intervalIntegral.integral_const_mul, mul_assoc]
       _ ≤ _ := by
         apply mul_le_mul_of_nonneg_left _ (by positivity)
         exact (spectralLineJet_selberg_modes_mean R hR hb').trans (by
           gcongr; exact spectralLineJet_selberg_rough_mass hN R hR hrough)

/-- The real finite Hardy signal times the squared mollifier norm is the real
part of the grouped polynomial times a measurable contraction. Thus the complex
absolute projection bounds the contribution of those same frequencies to the
real signal, also at zeros of the mollifier. -/
theorem spectralLineJet_selbergGrouped_hardy (L N : ℕ) :
    ∃ θ : ℝ → ℂ, Measurable θ ∧ (∀ t, ‖θ t‖ ≤ 1) ∧ ∀ t,
      ‖∑ m ∈ Finset.Icc 1 N, (spectralLineJet_selbergHalfMoebius m : ℂ)*mode(m,t)‖^2 *
        (-hardyPhaseFactor t * spectralLineJet_selbergFiniteZeta L t).re =
        (θ t * ∑ m ∈ Finset.Icc 1 (N*(N*L)), (spectralLineJet_selbergGroupedCoefficient L N t m : ℂ)*mode(m,t)).re := by
  let P (t : ℝ) := ∑ m ∈ Finset.Icc 1 N, (spectralLineJet_selbergHalfMoebius m : ℂ)*mode(m,t)
  have hP : Continuous P := continuous_finsetSum _ fun m hm ↦
    continuous_const.mul (continuous_cpow_neg_criticalLinePoint (Finset.mem_Icc.mp hm).1)
  let θ (t : ℝ) := -hardyPhaseFactor t * ((starRingEnd ℂ) (P t) / P t)
  refine ⟨θ, spectralLineJet_selbergPhase_continuous.neg.measurable.mul
    ((Complex.continuous_conj.comp hP).measurable.div hP.measurable), ?_, ?_⟩
  · intro t
    by_cases hp : P t = 0
    · simp [θ,hp]
    · simp [θ,norm_hardyPhaseFactor,norm_ne_zero_iff.mpr hp]
  · intro t
    rw [← spectralLineJet_selbergGrouped_expansion]
    let D := spectralLineJet_selbergFiniteZeta L t
    change ‖P t‖^2 * (-hardyPhaseFactor t * D).re = (θ t * (D*(P t)^2)).re
    have hp : θ t * (D*(P t)^2) = ((‖P t‖^2 : ℝ) : ℂ) * (-hardyPhaseFactor t * D) := by
      by_cases hz : P t = 0
      · simp [θ,hz]
      · rw [Complex.ofReal_pow, ← Complex.mul_conj']
        dsimp only [θ]
        field_simp
    rw [hp,Complex.re_ofReal_mul]

/-- On a dyadic interval near `T`, the rough-frequency component already
satisfies the uniform `h² √T` second-moment scale needed in the Selberg
argument. Both the number of frequencies and the mollifier length may grow. -/
theorem spectralLineJet_selbergGrouped_rough_dyadic (A : ℕ) :
    ∃ K > (0:ℝ), ∀ {H T h : ℝ} (_ : 0 < H) (_ : 1 ≤ T) (_ : 0 ≤ h) (_ : h ≤ T)
      {L N X : ℕ} (_ : 1 ≤ N) (R : Finset ℕ) (_ : R ⊆ Finset.Icc 1 X),
      (∀ m ∈ R, ∀ d, d ≤ N → 0 < d → d.Coprime m) → X ≤ N^A → (X:ℝ)^2 ≤ T →
      X ≤ L → (X:ℝ) ≤ 3*T/Real.pi →
      (∫ t in T..2*T, (∫ u in t..t+h,
        ‖Complex.Gamma (1/4 + ((u/2 : ℝ) : ℂ)*Complex.I)‖ * Real.exp ((Real.pi/4 - 1/(2*H))*u) *
        ‖∑ m ∈ R, (spectralLineJet_selbergGroupedCoefficient L N u m : ℂ)*mode(m,u)‖)^2) ≤
      K*h^2*Real.sqrt T := by
  obtain ⟨C,hC,hw⟩ := spectralLineJet_selbergGrouped_rough_window
  let M : ℝ := 2*((A:ℝ)+3)+8
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨C^2*M, by positivity, ?_⟩
  intro H T h hH hT hh hhT L N X hN R hR hrough hpow hsquare hL hflat
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  let y : ℝ := ↑(N+1)
  have hy : 2 ≤ y := by dsimp [y]; exact_mod_cast (by omega : 2 ≤ N+1)
  have hypos : 0 < y := by linarith
  have hlog : (1/2 : ℝ) ≤ Real.log y := by
    have hinv : y⁻¹ ≤ (2:ℝ)⁻¹ := inv_anti₀ (by norm_num) hy
    linarith [Real.one_sub_inv_le_log_of_pos hypos]
  have hxLog : Real.log (N*X : ℕ) ≤ (A+1 : ℝ)*Real.log y := by
    rcases Nat.eq_zero_or_pos X with rfl | hxp
    · simp only [mul_zero,Nat.cast_zero,Real.log_zero]
      exact mul_nonneg (by positivity) (by linarith)
    have hnx : N*X ≤ (N+1)^(A+1) := by
      rw [pow_succ, Nat.mul_comm]
      exact Nat.mul_le_mul (hpow.trans (Nat.pow_le_pow_left (by omega) _)) (by omega)
    have hhlog := Real.log_le_log (by exact_mod_cast Nat.mul_pos hN hxp) (Nat.cast_le (α := ℝ).mpr hnx)
    simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_succ, y] using hhlog
  have hmass : (1+Real.log (N*X : ℕ))/Real.log y ≤ (A:ℝ)+3 := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log y)).mpr
    nlinarith only [hxLog,hlog]
  have htotal : (2*T+h-T)*((1+Real.log (N*X : ℕ))/Real.log y) + 8*(X:ℝ)^2 ≤ T*M := by
    calc _ ≤ (2*T)*((A:ℝ)+3) + 8*T := by
           gcongr
           · linarith
         _ = _ := by dsimp [M]; ring
  have hquarter : ((1+T)^(1/4:ℝ))^2 = Real.sqrt (1+T) := by
    rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ 1+T), Real.sqrt_eq_rpow]
    norm_num
  have hweight : (C/(1+T)^(1/4:ℝ))^2*T ≤ C^2*Real.sqrt T := by
    rw [div_pow,hquarter,div_mul_eq_mul_div,div_le_iff₀ (Real.sqrt_pos.mpr (by linarith))]
    calc _ = C^2 * (Real.sqrt T*Real.sqrt T) := by rw [Real.mul_self_sqrt hTpos.le]
         _ ≤ _ := by rw [← mul_assoc]; gcongr; linarith
  calc _ ≤ _ := hw hH hTpos.le (by linarith : T ≤ 2*T) hh hN R hR hrough hL hflat
       _ ≤ h^2*(C/(1+T)^(1/4:ℝ))^2*(T*M) := mul_le_mul_of_nonneg_left htotal (by positivity)
       _ = h^2*((C/(1+T)^(1/4:ℝ))^2*T)*M := by ring
       _ ≤ h^2*(C^2*Real.sqrt T)*M := by gcongr
       _ = _ := by ring

/-- A finite row of the inverse-square integer-gap matrix has uniformly bounded mass. -/
private theorem spectralLineJet_selberg_gap_row (R : Finset ℕ) (m : ℕ) :
    (∑ n ∈ R, 1 / ((m:ℝ) - n)^2) ≤ ∑' k : ℤ, 1 / (k:ℝ)^2 := by
  let e : ℕ ↪ ℤ := ⟨fun n ↦ (m:ℤ)-n, by intro i j hij; exact_mod_cast sub_right_inj.mp hij⟩
  have he : (∑ n ∈ R, 1 / ((m:ℝ)-n)^2) = ∑ k ∈ R.map e, 1/(k:ℝ)^2 := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    change _ = 1/(((m:ℤ)-n : ℤ):ℝ)^2
    push_cast
    rfl
  rw [he]
  exact (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)).sum_le_tsum _ fun _ _ ↦ by positivity

/-- Discrete Schur bound for the off-diagonal terms; the diagonal weight is zero. -/
private theorem spectralLineJet_selberg_gap_quadratic (R : Finset ℕ) (A : ℕ → ℝ) :
    (∑ m ∈ R, ∑ n ∈ R, A m*A n*(1/((m:ℝ)-n)^2)) ≤
      (∑' k : ℤ, 1/(k:ℝ)^2) * (∑ m ∈ R, (A m)^2) := by
  let D := ∑' k : ℤ, 1/(k:ℝ)^2
  let w (m n : ℕ) := 1/((m:ℝ)-n)^2
  have hw (m n : ℕ) : w m n = w n m := by dsimp [w]; ring
  have hleft : (∑ m ∈ R, ∑ n ∈ R, (A m)^2*w m n) ≤ D*∑ m ∈ R, (A m)^2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ ↦ ?_
    rw [← Finset.mul_sum,mul_comm D]
    exact mul_le_mul_of_nonneg_left (spectralLineJet_selberg_gap_row R m) (sq_nonneg _)
  have hright : (∑ m ∈ R, ∑ n ∈ R, (A n)^2*w m n) ≤ D*∑ m ∈ R, (A m)^2 := by
    rw [Finset.sum_comm]
    simpa only [hw] using hleft
  have hp : 2*(∑ m ∈ R, ∑ n ∈ R, A m*A n*w m n) ≤
      (∑ m ∈ R, ∑ n ∈ R, (A m)^2*w m n) + ∑ m ∈ R, ∑ n ∈ R, (A n)^2*w m n := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun m _ ↦ Finset.sum_le_sum fun n _ ↦ ?_
    have h := mul_nonneg (sq_nonneg (A m-A n)) (show 0 ≤ w m n by dsimp [w]; positivity)
    nlinarith only [h]
  change (∑ m ∈ R, ∑ n ∈ R, A m*A n*w m n) ≤ D*∑ m ∈ R, (A m)^2
  linarith only [hp,hleft,hright]

/-- Logarithmic gaps between integer frequencies retain the full integer difference. -/
private theorem spectralLineJet_selberg_log_distance {X m n : ℕ} (hm : m ∈ Finset.Icc 1 X)
    (hn : n ∈ Finset.Icc 1 X) : |(m:ℝ)-n| ≤ X*|Real.log m-Real.log n| := by
  have H {i j : ℕ} (hi : 0 < i) (hj : j ≤ X) (hij : i ≤ j) :
      (j:ℝ)-i ≤ X*(Real.log j-Real.log i) := by
    have hip : 0 < (i:ℝ) := by exact_mod_cast hi
    have hjp : 0 < (j:ℝ) := by exact_mod_cast hi.trans_le hij
    have h := Real.one_sub_inv_le_log_of_pos (div_pos hjp hip)
    rw [inv_div,Real.log_div hjp.ne' hip.ne'] at h
    have hlog := sub_nonneg.mpr (Real.log_le_log hip (Nat.cast_le.mpr hij))
    calc _ = (j:ℝ)*(1-(i:ℝ)/j) := by field_simp
         _ ≤ (j:ℝ)*(Real.log j-Real.log i) := mul_le_mul_of_nonneg_left h hjp.le
         _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) hlog
  rcases le_total n m with h|h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h)),abs_of_nonneg (sub_nonneg.mpr
      (Real.log_le_log (by exact_mod_cast (show 0<n from (Finset.mem_Icc.mp hn).1)) (Nat.cast_le.mpr h)))]
    exact H (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hm).2 h
  · rw [abs_sub_comm (m:ℝ), abs_sub_comm (Real.log m),
      abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h)), abs_of_nonneg (sub_nonneg.mpr
        (Real.log_le_log (by exact_mod_cast (show 0<m from (Finset.mem_Icc.mp hm).1)) (Nat.cast_le.mpr h)))]
    exact H (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).2 h

/-- A nonconstant pure logarithmic phase has a uniformly bounded primitive. -/
private theorem spectralLineJet_selberg_exp_primitive {l : ℝ} (hl : l ≠ 0) (a b : ℝ) :
    ‖∫ v in a..b, Complex.exp ((-Complex.I*(l:ℂ))*v)‖ ≤ 2/|l| := by
  let c : ℂ := -Complex.I*(l:ℂ)
  have hc : ‖c‖ = |l| := by simp [c]
  have hcne : c ≠ 0 := norm_pos_iff.mp (hc ▸ abs_pos.mpr hl)
  change ‖∫ v in a..b, Complex.exp (c*v)‖ ≤ _
  rw [integral_exp_mul_complex hcne, norm_div,hc]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  calc _ ≤ ‖Complex.exp (c*b)‖+‖Complex.exp (c*a)‖ := norm_sub_le _ _
       _ = 2 := by simp [Complex.norm_exp,c,Complex.mul_re]; norm_num

private def spectralLineJet_selbergFourierPair (B : ℕ → ℂ) (m n : ℕ) (u : ℝ) : ℂ :=
  B m * (starRingEnd ℂ) (B n) * Complex.exp ((-Complex.I * ((Real.log m - Real.log n : ℝ) : ℂ)) * u)

/-- Averaging the starting height factors an off-diagonal term into two
oscillatory primitives of the same frequency. -/
private theorem spectralLineJet_selberg_shifted_pair (B : ℕ → ℂ) (m n : ℕ) (a b v : ℝ) :
    (∫ x in a..b, spectralLineJet_selbergFourierPair B m n (x+v)) =
      (B m * (starRingEnd ℂ) (B n) * ∫ x in a..b, Complex.exp ((-Complex.I *
        ((Real.log m - Real.log n : ℝ) : ℂ))*x)) *
      Complex.exp ((-Complex.I * ((Real.log m - Real.log n : ℝ) : ℂ))*v) := by
  let c : ℂ := -Complex.I * ((Real.log m - Real.log n : ℝ) : ℂ)
  have he (x : ℝ) : spectralLineJet_selbergFourierPair B m n (x+v) =
      (B m*(starRingEnd ℂ) (B n)*Complex.exp (c*x))*Complex.exp (c*v) := by
    simp only [spectralLineJet_selbergFourierPair,c,Complex.ofReal_add,mul_add,Complex.exp_add,mul_assoc]
  rw [intervalIntegral.integral_congr (fun x _ ↦ he x), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const_mul]

/-- In the averaged rectangle the diagonal is unchanged and the off-diagonal
kernel decays as the inverse square of the integer separation. -/
private theorem spectralLineJet_selberg_rectangle_pair {X m n : ℕ} (hm : m ∈ Finset.Icc 1 X)
    (hn : n ∈ Finset.Icc 1 X) (B : ℕ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    ‖∫ v in (0:ℝ)..X, ∫ x in a-X..b, spectralLineJet_selbergFourierPair B m n (x+v)‖ ≤
      (if m=n then (X:ℝ)*(b-a+X)*‖B m‖^2 else 0) +
      4*(X:ℝ)^2*(‖B m‖*‖B n‖*(1/((m:ℝ)-n)^2)) := by
  by_cases h : m = n
  · subst n
    simp only [spectralLineJet_selbergFourierPair,sub_self,Complex.ofReal_zero,mul_zero,zero_mul,
      Complex.exp_zero,mul_one,Complex.mul_conj',intervalIntegral.integral_const,sub_zero,norm_smul,
      Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤(X:ℝ)),abs_of_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) X] : 0≤b-(a-X)),
      norm_pow,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _),ite_true]
    ring_nf
    exact le_rfl
  · let l := Real.log m - Real.log n
    let c : ℂ := -Complex.I*(l:ℂ)
    have hx : 0 < (X:ℝ) := by exact_mod_cast (show 0<m from (Finset.mem_Icc.mp hm).1).trans_le (Finset.mem_Icc.mp hm).2
    have hmn : 0 < |(m:ℝ)-n| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast h))
    have hg : |(m:ℝ)-n| ≤ (X:ℝ)*|l| := spectralLineJet_selberg_log_distance hm hn
    have hl : 0 < |l| := (mul_pos_iff_of_pos_left hx).mp (hmn.trans_le hg)
    have hbnd : 2/|l| ≤ 2*X/|(m:ℝ)-n| := by
      rw [div_le_div_iff₀ hl hmn]; linarith
    simp_rw [spectralLineJet_selberg_shifted_pair]
    rw [intervalIntegral.integral_const_mul]
    change ‖B m*(starRingEnd ℂ) (B n)*(∫ x in a-X..b, Complex.exp (c*x))*
      (∫ v in (0:ℝ)..X, Complex.exp (c*v))‖ ≤ _
    simp only [norm_mul,RCLike.norm_conj,ite_eq_right h,zero_add]
    have hfirst := (spectralLineJet_selberg_exp_primitive (abs_pos.mp hl) (a-X) b).trans hbnd
    have hsecond := (spectralLineJet_selberg_exp_primitive (abs_pos.mp hl) 0 X).trans hbnd
    calc _ ≤ ‖B m‖*‖B n‖*(2*X/|(m:ℝ)-n|)*(2*X/|(m:ℝ)-n|) := by gcongr
         _ = _ := by rw [div_eq_mul_inv, ← sq_abs ((m:ℝ)-n)]; ring

/-- An interval mean of a nonnegative continuous function is bounded by its
integral over a rectangle of translated, enlarged intervals. -/
private theorem spectralLineJet_selberg_shift_average (E : ℝ → ℝ) (hc : Continuous E)
    (he : ∀ t, 0 ≤ E t) {a b Y : ℝ} (hab : a ≤ b) (hY : 0 ≤ Y) :
    Y*(∫ u in a..b, E u) ≤ ∫ v in (0:ℝ)..Y, ∫ x in a-Y..b, E (x+v) := by
  let F (v : ℝ) := ∫ t in (0:ℝ)..v, E t
  have hF : Continuous F := intervalIntegral.continuous_primitive (fun _ _ ↦ hc.intervalIntegrable ..) 0
  have hJ (v : ℝ) : (∫ x in a-Y..b, E (x+v)) = F (b+v)-F (a-Y+v) := by
    rw [intervalIntegral.integral_comp_add_right]
    exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable ..) (hc.intervalIntegrable ..)).symm
  calc _ = ∫ _ in (0:ℝ)..Y, ∫ t in a..b, E t := by simp
       _ ≤ ∫ v in (0:ℝ)..Y, F (b+v)-F (a-Y+v) := by
         apply intervalIntegral.integral_mono_on hY intervalIntegrable_const
           (((hF.comp (continuous_const.add continuous_id)).sub (hF.comp (continuous_const.add continuous_id))).intervalIntegrable ..)
         intro v hv
         change _ ≤ F (b+v)-F (a-Y+v)
         rw [← hJ,intervalIntegral.integral_comp_add_right]
         exact intervalIntegral.integral_mono_interval (by linarith [hv.2]) hab (by linarith [hv.1])
           (.of_forall he) (hc.intervalIntegrable ..)
       _ = _ := intervalIntegral.integral_congr fun v _ ↦ (hJ v).symm

/-- A continuous Dirichlet mean-value estimate at full linear length. Double
averaging costs only the exact coefficient diagonal times an absolute multiple
of the frequency cutoff. -/
private theorem spectralLineJet_selberg_fourier_mean {X : ℕ} (hX : 0 < X) (R : Finset ℕ)
    (hR : R ⊆ Finset.Icc 1 X) (B : ℕ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ‖∑ m ∈ R, B m*Complex.exp ((-Complex.I*(Real.log m : ℂ))*t)‖^2) ≤
      (b-a+(1+4*(∑' k : ℤ, 1/(k:ℝ)^2))*X) * (∑ m ∈ R, ‖B m‖^2) := by
  classical
  let S := R ×ˢ R
  let E (t : ℝ) := ‖∑ m ∈ R, B m*Complex.exp ((-Complex.I*(Real.log m : ℂ))*t)‖^2
  let K (p : ℕ × ℕ) (t : ℝ) := spectralLineJet_selbergFourierPair B p.1 p.2 t
  have hE : Continuous E := by dsimp [E]; fun_prop
  have hK (p : ℕ × ℕ) (v : ℝ) : Continuous (fun x : ℝ ↦ K p (x+v)) := by
    dsimp [K,spectralLineJet_selbergFourierPair]; fun_prop
  have hex (t : ℝ) : ((E t : ℝ) : ℂ) = ∑ p ∈ S, K p t := by
    simp only [E,Complex.ofReal_pow, ← Complex.mul_conj',map_sum, Finset.sum_mul_sum,S,Finset.sum_product]
    apply Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun n _ ↦ ?_
    simp only [K,spectralLineJet_selbergFourierPair,map_mul,← Complex.exp_conj]
    rw [show ∀ x y z w : ℂ, x*y*(z*w) = (x*z)*(y*w) from fun _ _ _ _ ↦ by ring,← Complex.exp_add]
    congr 2
    simp only [Complex.ofReal_sub,map_neg,Complex.conj_I,Complex.conj_ofReal,neg_neg]
    ring
  have heinner (v : ℝ) : ((∫ x in a-X..b, E (x+v) : ℝ) : ℂ) =
      ∑ p ∈ S, ∫ x in a-X..b, K p (x+v) := by
    rw [← intervalIntegral.integral_ofReal, intervalIntegral.integral_congr (fun x _ ↦ hex (x+v)),
      intervalIntegral.integral_finsetSum fun p _ ↦ (hK p v).intervalIntegrable ..]
  have houter (p : ℕ × ℕ) : Continuous (fun v : ℝ ↦ ∫ x in a-X..b, K p (x+v)) := by
    simp only [K,spectralLineJet_selberg_shifted_pair]
    fun_prop
  have heint : ((∫ v in (0:ℝ)..X, ∫ x in a-X..b, E (x+v) : ℝ) : ℂ) =
      ∑ p ∈ S, ∫ v in (0:ℝ)..X, ∫ x in a-X..b, K p (x+v) := by
    rw [← intervalIntegral.integral_ofReal,intervalIntegral.integral_congr (fun v _ ↦ heinner v),
      intervalIntegral.integral_finsetSum fun p _ ↦ (houter p).intervalIntegrable ..]
  let M := ∑ m ∈ R, ‖B m‖^2
  let D := ∑' k : ℤ, 1/(k:ℝ)^2
  have hdiag : (∑ p ∈ S, if p.1=p.2 then (X:ℝ)*(b-a+X)*‖B p.1‖^2 else 0) =
      (X:ℝ)*(b-a+X)*M := by simp [S,M,Finset.sum_product,Finset.mul_sum]
  have hoff : (∑ p ∈ S, 4*(X:ℝ)^2*(‖B p.1‖*‖B p.2‖*(1/((p.1:ℝ)-p.2)^2))) ≤ 4*(X:ℝ)^2*(D*M) := by
    simp only [S,Finset.sum_product, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (spectralLineJet_selberg_gap_quadratic R fun m ↦ ‖B m‖) (by positivity)
  have hx : 0 < (X:ℝ) := by exact_mod_cast hX
  apply (le_of_mul_le_mul_left (a := (X:ℝ)) · hx)
  calc (X:ℝ)*(∫ t in a..b, E t) ≤ ∫ v in (0:ℝ)..X, ∫ x in a-X..b, E (x+v) :=
         spectralLineJet_selberg_shift_average E hE (fun _ ↦ sq_nonneg _) hab hx.le
       _ ≤ ‖((∫ v in (0:ℝ)..X, ∫ x in a-X..b, E (x+v) : ℝ) : ℂ)‖ := by
         rw [Complex.norm_real,Real.norm_eq_abs]; exact le_abs_self _
       _ ≤ ∑ p ∈ S, ‖∫ v in (0:ℝ)..X, ∫ x in a-X..b, K p (x+v)‖ := heint ▸ norm_sum_le _ _
       _ ≤ ∑ p ∈ S, ((if p.1=p.2 then (X:ℝ)*(b-a+X)*‖B p.1‖^2 else 0) +
             4*(X:ℝ)^2*(‖B p.1‖*‖B p.2‖*(1/((p.1:ℝ)-p.2)^2))) := by
         apply Finset.sum_le_sum fun p hp ↦ ?_
         exact spectralLineJet_selberg_rectangle_pair (hR (Finset.mem_product.mp hp).1)
           (hR (Finset.mem_product.mp hp).2) B hab
       _ ≤ (X:ℝ)*(b-a+X)*M + 4*(X:ℝ)^2*(D*M) := by rw [Finset.sum_add_distrib,hdiag]; gcongr
       _ = _ := by dsimp only [M,D]; ring

/-- Mean square for any fixed packet of critical-line modes, with its exact
coefficient diagonal and a linear length loss. -/
private theorem spectralLineJet_selberg_critical_mean {X : ℕ} (hX : 0 < X) (R : Finset ℕ)
    (hR : R ⊆ Finset.Icc 1 X) (c : ℕ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, ‖∑ m ∈ R, (c m : ℂ)*mode(m,t)‖^2) ≤
      (b-a+(1+4*(∑' k : ℤ, 1/(k:ℝ)^2))*X) * ∑ m ∈ R, (c m)^2 / m := by
  let B (m : ℕ) := (c m : ℂ)*mode(m,0)
  have he (t : ℝ) (m : ℕ) (hm : m ∈ R) : (c m : ℂ)*mode(m,t) =
      B m*Complex.exp ((-Complex.I*(Real.log m : ℂ))*t) := by
    rw [cpow_neg_criticalLinePoint_eq_mode (Finset.mem_Icc.mp (hR hm)).1, ← mul_assoc]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg m)]
    rfl
  have hd (m : ℕ) (hm : m ∈ R) : ‖B m‖^2 = (c m)^2/m := by
    rw [show B m = (c m : ℂ)*mode(m,0) from rfl,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      norm_cpow_neg_criticalLinePoint (Finset.mem_Icc.mp (hR hm)).1,mul_pow,sq_abs,
      div_pow,one_pow,Real.sq_sqrt (Nat.cast_nonneg m),mul_one_div]
  calc _ = ∫ t in a..b, ‖∑ m ∈ R, B m*Complex.exp ((-Complex.I*(Real.log m : ℂ))*t)‖^2 :=
         intervalIntegral.integral_congr fun t _ ↦ congrArg (fun z : ℂ ↦ ‖z‖^2) (Finset.sum_congr rfl (he t))
       _ ≤ _ := (spectralLineJet_selberg_fourier_mean hX R hR B hab).trans_eq (by rw [Finset.sum_congr rfl hd])

/-- The time-independent arithmetic coefficients of the full packet below the
flat taper cutoff, with both sharp mollifier cutoffs retained. -/
def spectralLineJet_selbergFlatCoefficient (N : ℕ) : ArithmeticFunction ℝ :=
  let B := spectralLineJet_selbergCut N spectralLineJet_selbergHalfMoebius
  B*(B*(ArithmeticFunction.zeta : ArithmeticFunction ℝ))

/-- Below the flat cutoff every divisor in both Dirichlet convolutions has
full zeta weight. This identity holds for all positive indices, including
those whose smooth part exceeds the mollifier cutoff. -/
theorem spectralLineJet_selbergGrouped_eq_flat {L N m : ℕ} {t : ℝ} (hm : 0 < m)
    (hL : m ≤ L) (ht : (m:ℝ) ≤ 3*t/Real.pi) :
    spectralLineJet_selbergGroupedCoefficient L N t m = spectralLineJet_selbergFlatCoefficient N m := by
  let A := spectralLineJet_selbergCut L (fun k ↦ min 1 (max 0 (3*t/Real.pi-k+1)))
  let Z : ArithmeticFunction ℝ := ArithmeticFunction.zeta
  let B := spectralLineJet_selbergCut N spectralLineJet_selbergHalfMoebius
  have hA (d : ℕ) (hd : d ∣ m) : A d = Z d := by
    have hp := Nat.pos_of_dvd_of_pos hd hm
    have hdm := Nat.le_of_dvd hm hd
    have hcut := Finset.mem_Icc.mpr ⟨hp,hdm.trans hL⟩
    have hlin : (1:ℝ) ≤ 3*t/Real.pi-d+1 := by linarith [(Nat.cast_le.mpr hdm).trans ht]
    change (if d ∈ Finset.Icc 1 L then min 1 (max 0 (3*t/Real.pi-d+1)) else 0) = _
    rw [ite_eq_left hcut,min_eq_left (hlin.trans (le_max_right _ _))]
    simp [Z,ArithmeticFunction.zeta_apply_ne hp.ne']
  have hconv {f g : ArithmeticFunction ℝ} {u : ℕ} (hv : ∀ d, d ∣ u → f d = g d) :
      (B*f) u = (B*g) u := by
    simp only [ArithmeticFunction.mul_apply]
    apply Finset.sum_congr rfl fun p hp ↦ ?_
    rw [hv p.2 ⟨p.1, by rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1,mul_comm]⟩]
  change (B*(B*A)) m = (B*(B*Z)) m
  exact hconv (fun u hu ↦ hconv (fun d hd ↦ hA d (hd.trans hu)))

/-- Local gamma damping and sliding-window averaging transfer an unweighted
mean square to the absolute short-window estimate on a dyadic interval. -/
private theorem spectralLineJet_selberg_dyadic_transfer :
    ∃ C > (0:ℝ), ∀ {H T h : ℝ} (_ : 0 < H) (_ : 0 < T) (_ : 0 ≤ h) (P : ℝ → ℂ),
      Continuous P →
      (∫ t in T..2*T, (∫ u in t..t+h, ‖Complex.Gamma (criticalLineGammaArgument u)‖ *
          Real.exp ((Real.pi/4-1/(2*H))*u) * ‖P u‖)^2) ≤
        (C*h^2/Real.sqrt T) * ∫ u in T..2*T+h, ‖P u‖^2 := by
  obtain ⟨c,hc,hgamma⟩ := spectralLineJet_selbergGamma_upper
  refine ⟨c^2, by positivity, ?_⟩
  intro H T h hH hT hh P hp
  let W (u : ℝ) := ‖Complex.Gamma (criticalLineGammaArgument u)‖ *
    Real.exp ((Real.pi/4-1/(2*H))*u)
  have hW : Continuous W := spectralLineJet_selbergGamma_continuous.norm.mul (by fun_prop)
  have hbound (u : ℝ) (hu : T ≤ u) : (W u)^2 ≤ c^2/Real.sqrt T := by
    have hz : W u ≤ c/T^(1/4:ℝ) := by
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hT _)).mpr
      calc _ ≤ W u*(1+u)^(1/4:ℝ) := by
             apply mul_le_mul_of_nonneg_left _ (by dsimp [W]; positivity)
             exact Real.rpow_le_rpow hT.le (by linarith) (by norm_num)
           _ ≤ c := hgamma H hH u (hT.le.trans hu)
    have hpow : (T^(1/4:ℝ))^2 = Real.sqrt T := by
      rw [← Real.rpow_mul_natCast hT.le,Real.sqrt_eq_rpow]; norm_num
    exact (pow_le_pow_left₀ (by dsimp [W]; positivity) hz 2).trans_eq (by rw [div_pow,hpow])
  change (∫ t in T..2*T, (∫ u in t..t+h, W u*‖P u‖)^2) ≤ _
  calc _ ≤ h^2*∫ u in T..2*T+h, (W u*‖P u‖)^2 :=
         spectralLineJet_selberg_window_L2 _ (hW.mul hp.norm) (by linarith) hh
       _ ≤ h^2*∫ u in T..2*T+h, (c^2/Real.sqrt T)*‖P u‖^2 := by
         apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
         apply intervalIntegral.integral_mono_on (by linarith) (((hW.mul hp.norm).pow 2).intervalIntegrable ..)
           ((continuous_const.mul (hp.norm.pow 2)).intervalIntegrable ..)
         intro u hu
         change (W u*‖P u‖)^2 ≤ _
         rw [mul_pow]
         exact mul_le_mul_of_nonneg_right (hbound u hu.1) (sq_nonneg _)
       _ = _ := by rw [intervalIntegral.integral_const_mul]; ring

/-- At all frequencies below the physical flat cutoff, the full gamma-weighted
absolute-window mean square is bounded by the arithmetic coefficient diagonal.
The scale is linear in height and no coprimality restriction is imposed. -/
theorem spectralLineJet_selbergGrouped_flat_dyadic :
    ∃ K > (0:ℝ), ∀ {H T h : ℝ} (_ : 0 < H) (_ : 1 ≤ T) (_ : 0 ≤ h) (_ : h ≤ T)
      {L N X : ℕ} (R : Finset ℕ) (_ : R ⊆ Finset.Icc 1 X), X ≤ L → (X:ℝ) ≤ 3*T/Real.pi →
      (∫ t in T..2*T, (∫ u in t..t+h, ‖Complex.Gamma (1/4 + ((u/2:ℝ):ℂ)*Complex.I)‖ *
          Real.exp ((Real.pi/4-1/(2*H))*u) *
          ‖∑ m ∈ R, (spectralLineJet_selbergGroupedCoefficient L N u m : ℂ)*mode(m,u)‖)^2) ≤
      K*h^2*Real.sqrt T * ∑ m ∈ R, (spectralLineJet_selbergFlatCoefficient N m)^2/m := by
  obtain ⟨C,hC,htransfer⟩ := spectralLineJet_selberg_dyadic_transfer
  let B := 1+4*(∑' k : ℤ, 1/(k:ℝ)^2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨C*(2+B), mul_pos hC (by linarith), ?_⟩
  intro H T h hH hT hh hhT L N X R hR hL hX
  have hTpos := zero_lt_one.trans_le hT
  by_cases hxp : X = 0
  · have hnil : R = ∅ := Finset.eq_empty_of_forall_notMem (fun m hm ↦ by simpa [hxp] using hR hm)
    simp [hnil]
  have hx := Nat.pos_of_ne_zero hxp
  have hxT : (X:ℝ) ≤ T := hX.trans ((div_le_iff₀ Real.pi_pos).mpr (by nlinarith [mul_nonneg hTpos.le (sub_nonneg.mpr Real.pi_gt_three.le)]))
  let c := spectralLineJet_selbergFlatCoefficient N
  let P (u : ℝ) := ∑ m ∈ R, (c m : ℂ)*mode(m,u)
  have hP : Continuous P := continuous_finsetSum _ fun m hm ↦
    continuous_const.mul (continuous_cpow_neg_criticalLinePoint (Finset.mem_Icc.mp (hR hm)).1)
  have he (u : ℝ) (hu : T ≤ u) :
      (∑ m ∈ R, (spectralLineJet_selbergGroupedCoefficient L N u m : ℂ)*mode(m,u)) = P u := by
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    obtain ⟨hm₁,hmX⟩ := Finset.mem_Icc.mp (hR hm)
    rw [spectralLineJet_selbergGrouped_eq_flat hm₁ (hmX.trans hL) ((Nat.cast_le.mpr hmX).trans (hX.trans (by gcongr)))]
  have hmean : (∫ u in T..2*T+h, ‖P u‖^2) ≤ ((2+B)*T) * ∑ m ∈ R, (c m)^2/m := by
    apply (spectralLineJet_selberg_critical_mean hx R hR c (by linarith : T ≤ 2*T+h)).trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ ↦ by positivity)
    change 2*T+h-T+B*X ≤ (2+B)*T
    nlinarith only [hhT, mul_nonneg hB (sub_nonneg.mpr hxT)]
  calc _ = ∫ t in T..2*T, (∫ u in t..t+h, ‖Complex.Gamma (criticalLineGammaArgument u)‖ *
             Real.exp ((Real.pi/4-1/(2*H))*u) * ‖P u‖)^2 := by
         apply intervalIntegral.integral_congr
         intro t ht
         rw [uIcc_of_le (by linarith : T ≤ 2*T)] at ht
         apply congrArg (fun x : ℝ ↦ x^2)
         apply intervalIntegral.integral_congr
         intro u hu
         rw [uIcc_of_le (by linarith : t ≤ t+h)] at hu
         simp only [he u (ht.1.trans hu.1),criticalLineGammaArgument]
       _ ≤ _ := htransfer hH hTpos hh P hP
       _ ≤ (C*h^2/Real.sqrt T)*(((2+B)*T)*∑ m ∈ R, (c m)^2/m) := mul_le_mul_of_nonneg_left hmean (by positivity)
       _ = _ := by
         change _ = C*(2+B)*h^2*Real.sqrt T*(∑ m ∈ R, (c m)^2/m)
         field_simp [Real.sqrt_pos.mpr hTpos]
         ring_nf
         rw [Real.sq_sqrt hTpos.le]
         ring

/-- All rough frequencies through the linear flat cutoff satisfy the window
bound, uniformly in the subset. The logarithmic ratio stays bounded whenever
the height cutoff is a fixed power of the mollifier length. -/
theorem spectralLineJet_selbergGrouped_rough_linear :
    ∃ K > (0:ℝ), ∀ {H T h : ℝ} (_ : 0 < H) (_ : 1 ≤ T) (_ : 0 ≤ h) (_ : h ≤ T)
      {L N X : ℕ} (_ : 0 < N) (R : Finset ℕ) (_ : R ⊆ Finset.Icc 1 X),
      (∀ m ∈ R, ∀ d, d ≤ N → 0 < d → d.Coprime m) → X ≤ L → (X:ℝ) ≤ 3*T/Real.pi →
      (∫ t in T..2*T, (∫ u in t..t+h, ‖Complex.Gamma (1/4 + ((u/2:ℝ):ℂ)*Complex.I)‖ *
          Real.exp ((Real.pi/4-1/(2*H))*u) *
          ‖∑ m ∈ R, (spectralLineJet_selbergGroupedCoefficient L N u m : ℂ)*mode(m,u)‖)^2) ≤
      K*h^2*Real.sqrt T * ((1+Real.log (N*X : ℕ))/Real.log (N+1 : ℕ)) := by
  obtain ⟨K,hK,hmean⟩ := spectralLineJet_selbergGrouped_flat_dyadic
  refine ⟨K,hK,?_⟩
  intro H T h hH hT hh hhT L N X hN R hR hrough hL hX
  apply (hmean hH hT hh hhT R hR hL hX).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply le_trans _ (spectralLineJet_selberg_rough_mass hN R hR hrough)
  apply le_of_eq
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  obtain ⟨hmpos,hmX⟩ := Finset.mem_Icc.mp (hR hm)
  have hflat := (Nat.cast_le.mpr hmX).trans hX
  rw [← spectralLineJet_selbergGrouped_eq_flat (N := N) hmpos (hmX.trans hL) hflat]
  have hcoef := spectralLineJet_selbergGrouped_on_rough (r := 1) (s := m) Nat.zero_lt_one hmpos hN
    (by simpa using hmX.trans hL) (by simpa using hflat) (hrough m hm)
  simp only [one_mul,ite_true] at hcoef
  simp [hcoef,one_div]

/-- At indices up to a fixed multiple of the cutoff, every omitted mollifier
factor has a complementary divisor of bounded size. This gives an absolute
coefficient bound without a smoothness or squarefreeness restriction. -/
theorem spectralLineJet_selbergFlat_cutoff_error {N U m : ℕ} (hm : 0 < m) (hmN : m ≤ U*N) :
    |spectralLineJet_selbergFlatCoefficient N m - (if m=1 then 1 else 0)| ≤ 2*(U:ℝ)^2 := by
  classical
  let b := spectralLineJet_selbergHalfMoebius
  let B := spectralLineJet_selbergCut N b
  let Z : ArithmeticFunction ℝ := ArithmeticFunction.zeta
  let g := (B+b)*Z
  have hbb : b*b*Z = 1 := by
    rw [show b*b = (ArithmeticFunction.moebius : ArithmeticFunction ℝ) from spectralLineJet_selbergHalfMoebius_spec.2.2]
    exact ArithmeticFunction.coe_moebius_mul_coe_zeta
  have heq : spectralLineJet_selbergFlatCoefficient N - 1 = g*(B-b) := by
    change B*(B*Z)-1 = ((B+b)*Z)*(B-b)
    rw [← hbb]; ring
  have he (q : ℕ) (hq : q ≤ N) : (B-b) q = 0 := by
    by_cases hz : q=0
    · simp [hz]
    have hmem := Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hz,hq⟩
    change (if q ∈ Finset.Icc 1 N then b q else 0)-b q = 0
    rw [ite_eq_left hmem,sub_self]
  have hb (q : ℕ) : |B q| ≤ 1 ∧ |(B-b) q| ≤ 1 := by
    change |if q ∈ Finset.Icc 1 N then b q else 0| ≤ 1 ∧ |(if q ∈ Finset.Icc 1 N then b q else 0)-b q| ≤ 1
    split <;> simp [b,spectralLineJet_selbergHalfMoebius_spec.2.1]
  have hg (d : ℕ) : |g d| ≤ 2*(d:ℝ) := by
    change |((B+b)*Z) d| ≤ _
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    calc _ ≤ ∑ q ∈ d.divisors, |(B+b) q| := Finset.abs_sum_le_sum_abs _ _
         _ ≤ ∑ _q ∈ d.divisors, (2:ℝ) := by
           refine Finset.sum_le_sum fun q _ ↦ (abs_add_le (B q) (b q)).trans ?_
           linarith [(hb q).1,spectralLineJet_selbergHalfMoebius_spec.2.1 q]
         _ ≤ _ := by
           simp only [Finset.sum_const,nsmul_eq_mul]
           linarith only [Nat.cast_le (α := ℝ).mpr (Nat.card_divisors_le_self d)]
  have hside := congrArg (fun f : ArithmeticFunction ℝ ↦ f m) heq
  change spectralLineJet_selbergFlatCoefficient N m - (if m=1 then 1 else 0) = (g*(B-b)) m at hside
  rw [hside,ArithmeticFunction.mul_apply,← Nat.map_div_right_divisors,Finset.sum_map]
  let Q (d : ℕ) := g d*(B-b) (m/d)
  let S := m.divisors.filter (· ≤ U)
  have hsmall : ∑ d ∈ S, Q d = ∑ d ∈ m.divisors, Q d := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hout
    have hs : U < d := by simpa [S,hd] using hout
    have hmd : m/d ≤ N := Nat.div_le_of_le_mul (hmN.trans (Nat.mul_le_mul_right N hs.le))
    simp only [Q,he _ hmd,mul_zero]
  change |∑ d ∈ m.divisors, Q d| ≤ _
  rw [← hsmall]
  have hcard : S.card ≤ U := by
    have hsub : S ⊆ Finset.Icc 1 U := fun d hd ↦
      Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1 hm,
        (Finset.mem_filter.mp hd).2⟩
    simpa using Finset.card_le_card hsub
  calc _ ≤ ∑ d ∈ S, |Q d| := Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ _d ∈ S, 2*(U:ℝ) := by
         refine Finset.sum_le_sum fun d hd ↦ ?_
         rw [show |Q d| = |g d| * |(B-b) (m/d)| from abs_mul _ _]
         exact (mul_le_of_le_one_right (abs_nonneg _) (hb _).2).trans ((hg d).trans (by gcongr; exact_mod_cast (Finset.mem_filter.mp hd).2))
       _ ≤ _ := by
         simp only [Finset.sum_const,nsmul_eq_mul]
         calc _ ≤ (U:ℝ)*(2*U) := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (by positivity)
              _ = _ := by ring

/-- Uniform diagonal mass throughout an entire fixed multiplicative enlargement
of the mollifier band, including the indices whose smooth part exceeds `N`. -/
private theorem spectralLineJet_selbergFlat_near_diagonal {N U X : ℕ} (hN : 0 < N)
    (hX : X ≤ U*N) (R : Finset ℕ) (hR : R ⊆ Finset.Icc 1 X) :
    (∑ m ∈ R, (spectralLineJet_selbergFlatCoefficient N m)^2/m) ≤ 1+4*(U:ℝ)^5 := by
  classical
  let c := spectralLineJet_selbergFlatCoefficient N
  let B : ℝ := (2*U^2)^2
  have hN' : 0 < (N:ℝ) := by exact_mod_cast hN
  have hB : 0 ≤ B := sq_nonneg _
  have hone (m : ℕ) (hm : 0 < m) (hle : m ≤ N) : c m = if m=1 then 1 else 0 := by
    let t : ℝ := m*Real.pi
    have hmt : (m:ℝ) ≤ 3*t/Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      dsimp [t]; nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) m) Real.pi_pos.le]
    rw [show c m = spectralLineJet_selbergGroupedCoefficient m N t m from
      (spectralLineJet_selbergGrouped_eq_flat hm le_rfl hmt).symm]
    simpa using spectralLineJet_selbergGrouped_on_rough (s := 1) hm Nat.zero_lt_one hle
      (show m*1 ≤ m by simp) (by simpa using hmt) (by simp)
  have hcoef (m : ℕ) (hm : m ∈ R) : (c m)^2/m ≤ (if m=1 then 1 else 0) + B/N := by
    obtain ⟨hmpos,hmX⟩ := Finset.mem_Icc.mp (hR hm)
    by_cases h : m ≤ N
    · rw [hone m hmpos h]
      split
      · rename_i h1; subst m
        simpa using div_nonneg hB hN'.le
      · simpa using div_nonneg hB hN'.le
    · have hn1 : m ≠ 1 := by omega
      have hb := spectralLineJet_selbergFlat_cutoff_error hmpos (hmX.trans hX)
      simp only [ite_eq_right hn1,sub_zero] at hb
      rw [ite_eq_right hn1,zero_add]
      apply div_le_div₀ hB _ hN' (Nat.cast_le.mpr (le_of_lt (lt_of_not_ge h)))
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hi : (∑ m ∈ R, if m=1 then (1:ℝ) else 0) ≤ 1 := by simp; split <;> norm_num
  have hcard : R.card ≤ U*N := (show R.card ≤ X by simpa using Finset.card_le_card hR).trans hX
  calc _ ≤ ∑ m ∈ R, ((if m=1 then 1 else 0)+B/N) := Finset.sum_le_sum hcoef
       _ ≤ 1+4*(U:ℝ)^5 := by
         rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
         apply add_le_add hi
         calc _ ≤ ((U*N : ℕ):ℝ)*(B/N) := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (div_nonneg hB hN'.le)
              _ = _ := by push_cast; dsimp [B]; field_simp; ring

/-- The complete unsieved frequency band through any fixed multiple of the
mollifier length has the target absolute-window second moment. -/
theorem spectralLineJet_selbergGrouped_near_dyadic (U : ℕ) :
    ∃ K > (0:ℝ), ∀ {H T h : ℝ} (_ : 0 < H) (_ : 1 ≤ T) (_ : 0 ≤ h) (_ : h ≤ T)
      {L N X : ℕ} (_ : 0 < N) (R : Finset ℕ) (_ : R ⊆ Finset.Icc 1 X),
      X ≤ U*N → X ≤ L → (X:ℝ) ≤ 3*T/Real.pi →
      (∫ t in T..2*T, (∫ u in t..t+h, ‖Complex.Gamma (1/4 + ((u/2:ℝ):ℂ)*Complex.I)‖ *
          Real.exp ((Real.pi/4-1/(2*H))*u) *
          ‖∑ m ∈ R, (spectralLineJet_selbergGroupedCoefficient L N u m : ℂ)*mode(m,u)‖)^2) ≤
      K*h^2*Real.sqrt T := by
  obtain ⟨C,hC,hmean⟩ := spectralLineJet_selbergGrouped_flat_dyadic
  refine ⟨C*(1+4*(U:ℝ)^5),by positivity,?_⟩
  intro H T h hH hT hh hhT L N X hN R hR hX hL hflat
  apply (hmean hH hT hh hhT R hR hL hflat).trans
  calc _ ≤ C*h^2*Real.sqrt T*(1+4*(U:ℝ)^5) :=
         mul_le_mul_of_nonneg_left (spectralLineJet_selbergFlat_near_diagonal hN hX R hR) (by positivity)
       _ = _ := by ring

/-- Coefficients of the square of the length-`N` inverse-square-root mollifier,
before convolution with the flat zeta packet. -/
def spectralLineJet_selbergSquareWeight (N : ℕ) : ArithmeticFunction ℝ :=
  let B := spectralLineJet_selbergCut N spectralLineJet_selbergHalfMoebius
  B * B

private theorem spectralLineJet_selberg_weight_mass (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 (N*N), |spectralLineJet_selbergSquareWeight N d| ≤ (N:ℝ)^2 := by
  classical
  let B := spectralLineJet_selbergCut N spectralLineJet_selbergHalfMoebius
  let S := Finset.Icc 1 N ×ˢ Finset.Icc 1 N
  let idx (p : ℕ × ℕ) := p.1*p.2
  have hb (i : ℕ) : |B i| ≤ 1 := by
    change |if i ∈ Finset.Icc 1 N then spectralLineJet_selbergHalfMoebius i else 0| ≤ 1
    split <;> simp [spectralLineJet_selbergHalfMoebius_spec.2.1]
  have hmap (p : ℕ × ℕ) (hp : p ∈ S) : idx p ∈ Finset.Icc 1 (N*N) := by
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1,
      Nat.mul_le_mul (Finset.mem_Icc.mp ha).2 (Finset.mem_Icc.mp hb).2⟩
  have hbound (d : ℕ) (hd : d ∈ Finset.Icc 1 (N*N)) :
      |spectralLineJet_selbergSquareWeight N d| ≤ ∑ _p ∈ S with idx _p=d, (1:ℝ) := by
    let U := S.filter (fun p ↦ idx p=d)
    have hsub : U ⊆ d.divisorsAntidiagonal := fun p hp ↦
      Nat.mem_divisorsAntidiagonal.mpr ⟨(Finset.mem_filter.mp hp).2,by have := (Finset.mem_Icc.mp hd).1; omega⟩
    change |(B*B) d| ≤ _
    rw [ArithmeticFunction.mul_apply, ← Finset.sum_subset hsub]
    · apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro p _
      simpa [abs_mul] using mul_le_mul (hb p.1) (hb p.2) (abs_nonneg _) zero_le_one
    · intro p hp hno
      have hne : p ∉ S := fun hs ↦ hno (Finset.mem_filter.mpr ⟨hs,(Nat.mem_divisorsAntidiagonal.mp hp).1⟩)
      have hf : p.1 ∉ Finset.Icc 1 N ∨ p.2 ∉ Finset.Icc 1 N := not_and_or.mp (fun h ↦ hne (Finset.mem_product.mpr h))
      have hz (i : ℕ) (h : i ∉ Finset.Icc 1 N) : B i = 0 := ite_eq_right h
      rcases hf with h | h
      · rw [hz _ h,zero_mul]
      · rw [hz _ h,mul_zero]
  calc _ ≤ ∑ d ∈ Finset.Icc 1 (N*N), ∑ _p ∈ S with idx _p=d, (1:ℝ) := Finset.sum_le_sum hbound
       _ = _ := by rw [Finset.sum_fiberwise_of_maps_to hmap]; simp [S, sq]

private theorem spectralLineJet_selberg_flat_divisors (N : ℕ) {m : ℕ} (hm : 0 < m) :
    spectralLineJet_selbergFlatCoefficient N m = ∑ d ∈ Finset.Icc 1 (N*N),
      if d ∣ m then spectralLineJet_selbergSquareWeight N d else 0 := by
  let b := spectralLineJet_selbergHalfMoebius
  let B := spectralLineJet_selbergCut N b
  have ht : ∀ i, N < i → B i = 0 := by
    intro i hi
    simp [B,spectralLineJet_selbergCut,show ¬i≤N by omega]
  change (B*(B*(ArithmeticFunction.zeta : ArithmeticFunction ℝ))) m = _
  rw [← mul_assoc, ArithmeticFunction.coe_mul_zeta_apply]
  let S := (Finset.Icc 1 (N*N)).filter (· ∣ m)
  have hsub : S ⊆ m.divisors := fun d hd ↦ Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2,hm.ne'⟩
  rw [← Finset.sum_subset hsub]
  · exact Finset.sum_filter _ _
  · intro d hd hn
    have hdpos := Nat.pos_of_mem_divisors hd
    have hgt : N*N < d := by
      by_contra! hh
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdpos,hh⟩,(Nat.mem_divisors.mp hd).1⟩)
    exact spectralLineJet_selberg_cut_tail N N B B ht ht d hgt

/-- Selberg's quadratic form for the actual squared mollifier weights. Its
kernel is the density of the common multiples of the two divisor indices. -/
def spectralLineJet_selbergSieveEnergy (N : ℕ) : ℝ :=
  let D := Finset.Icc 1 (N*N)
  let a := spectralLineJet_selbergSquareWeight N
  ∑ d ∈ D, ∑ e ∈ D, a d * a e / Nat.lcm d e

private theorem spectralLineJet_selberg_flat_square_count (N X : ℕ) :
    ∑ m ∈ Finset.Ioc 0 X, (spectralLineJet_selbergFlatCoefficient N m)^2 =
      ∑ d ∈ Finset.Icc 1 (N*N), ∑ e ∈ Finset.Icc 1 (N*N),
        spectralLineJet_selbergSquareWeight N d * spectralLineJet_selbergSquareWeight N e *
          (X / Nat.lcm d e : ℕ) := by
  classical
  let D := Finset.Icc 1 (N*N)
  let a := spectralLineJet_selbergSquareWeight N
  let F (m d e : ℕ) := if d.lcm e ∣ m then a d * a e else 0
  calc _ = ∑ m ∈ Finset.Ioc 0 X, ∑ d ∈ D, ∑ e ∈ D, F m d e := by
         refine Finset.sum_congr rfl fun m hm ↦ ?_
         rw [spectralLineJet_selberg_flat_divisors N (Finset.mem_Ioc.mp hm).1, sq, Finset.sum_mul_sum]
         refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
         by_cases hd : d ∣ m <;> by_cases he : e ∣ m <;> simp [F,a,Nat.lcm_dvd_iff,hd,he]
       _ = ∑ d ∈ D, ∑ e ∈ D, ∑ m ∈ Finset.Ioc 0 X, F m d e := by
         rw [Finset.sum_comm]
         exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
       _ = _ := by
         refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
         simp only [F,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,Nat.Ioc_filter_dvd_card_eq_div]
         exact mul_comm _ _

/-- The mean square of every flat coefficient up to `X` is `X` times the
sieve energy, with an absolute discrepancy at most `N⁴`. No restriction on
prime factors or on the relative sizes of the cutoffs is needed. -/
theorem spectralLineJet_selbergFlat_square_discrepancy (N X : ℕ) :
    |(∑ m ∈ Finset.Ioc 0 X, (spectralLineJet_selbergFlatCoefficient N m)^2) -
      X * spectralLineJet_selbergSieveEnergy N| ≤ (N:ℝ)^4 := by
  let D := Finset.Icc 1 (N*N)
  let a := spectralLineJet_selbergSquareWeight N
  let err (k : ℕ) : ℝ := (X/k : ℕ) - (X:ℝ)/k
  have herr (k : ℕ) (hk : 0 < k) : |err k| ≤ 1 := by
    have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
    have hdiv : (k:ℝ)*(X/k : ℕ)+(X%k : ℕ)=X := by exact_mod_cast Nat.div_add_mod X k
    have hmod : ((X%k : ℕ):ℝ) < k := by exact_mod_cast Nat.mod_lt X hk
    dsimp [err]
    rw [abs_of_nonpos (sub_nonpos.mpr Nat.cast_div_le)]
    have h := (div_le_iff₀ hk').mpr (by nlinarith only [hdiv,hmod] : (X:ℝ) ≤ (((X/k : ℕ):ℝ)+1)*k)
    linarith
  have hdiff : (∑ m ∈ Finset.Ioc 0 X, (spectralLineJet_selbergFlatCoefficient N m)^2) -
      X * spectralLineJet_selbergSieveEnergy N = ∑ d ∈ D, ∑ e ∈ D, a d*a e*err (d.lcm e) := by
    rw [spectralLineJet_selberg_flat_square_count]
    simp only [spectralLineJet_selbergSieveEnergy,Finset.mul_sum,← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
    dsimp [a,err]; ring
  rw [hdiff]
  calc _ ≤ ∑ d ∈ D, ∑ e ∈ D, |a d| * |a e| := by
         apply (Finset.abs_sum_le_sum_abs _ _).trans
         refine Finset.sum_le_sum fun d hd ↦ (Finset.abs_sum_le_sum_abs _ _).trans ?_
         refine Finset.sum_le_sum fun e he ↦ ?_
         rw [abs_mul,abs_mul]
         exact mul_le_of_le_one_right (by positivity) (herr _ (Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1))
       _ = (∑ d ∈ D, |a d|)^2 := by rw [sq,Finset.sum_mul_sum]
       _ ≤ _ := by
         calc _ ≤ ((N:ℝ)^2)^2 := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
                   (spectralLineJet_selberg_weight_mass N) 2
              _ = _ := by ring

/-- An absolute bound for the counting discrepancy gives a uniform harmonic
tail bound by summation by parts, including both endpoints of the window. -/
private theorem spectralLineJet_selberg_weighted_discrepancy (f : ℕ → ℝ) {E B : ℝ}
    (hB : 0 ≤ B) (hcount : ∀ x : ℕ, |(∑ m ∈ Finset.Ioc 0 x, f m) - x*E| ≤ B)
    {Y X : ℕ} (hYX : Y ≤ X) :
    |(∑ m ∈ Finset.Ioc Y X, f m/m) -
      E * ∑ m ∈ Finset.Ioc Y X, (m:ℝ)⁻¹| ≤ 2*B/(Y+1) := by
  classical
  let w (i : ℕ) := (i:ℝ)⁻¹
  let g (i : ℕ) := if i=0 then 0 else f i-E
  let P (i : ℕ) := ∑ j ∈ Finset.range (i+1), g j
  have hP (i : ℕ) : |P i| ≤ B := by
    have hi : (Finset.range (i+1)).filter (· ≠ 0) = Finset.Ioc 0 i := by ext j; simp; omega
    have hsum : P i = ∑ j ∈ Finset.Ioc 0 i, (f j-E) := by
      dsimp [P,g]
      rw [← hi,Finset.sum_filter]
      exact Finset.sum_congr rfl fun j _ ↦ by by_cases hj : j=0 <;> simp [hj]
    simpa [hsum,Finset.sum_sub_distrib] using hcount i
  have heq : (∑ m ∈ Finset.Ioc Y X, f m/m)-E*(∑ m ∈ Finset.Ioc Y X, (m:ℝ)⁻¹) =
      ∑ m ∈ Finset.Ioc Y X, w m • g m := by
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    have hm0 : m ≠ 0 := by have := (Finset.mem_Ioc.mp hm).1; omega
    simp [w,g,hm0,div_eq_mul_inv,smul_eq_mul]; ring
  rw [heq]
  rcases hYX.eq_or_lt with rfl | hYX'
  · simp; positivity
  have hpos : 0 < X := by omega
  let I := Finset.Ioc Y (X-1)
  have hI : I = Finset.Ico (Y+1) X := by ext i; simp [I]; omega
  have dec (i : ℕ) (hi : i ∈ I) : w (i+1) ≤ w i := by
    have hip : 0 < i := by have := (Finset.mem_Ioc.mp hi).1; omega
    apply inv_anti₀ (by exact_mod_cast hip)
    exact_mod_cast Nat.le_succ i
  have hsum : (∑ i ∈ I, |w (i+1)-w i|) = w (Y+1)-w X := by
    calc _ = -∑ i ∈ I, (w (i+1)-w i) := by
           rw [← Finset.sum_neg_distrib]
           exact Finset.sum_congr rfl fun i hi ↦ abs_of_nonpos (sub_nonpos.mpr (dec i hi))
         _ = _ := by rw [hI,Finset.sum_Ico_sub w (by omega)]; ring
  have hmid : |∑ i ∈ I, (w (i+1)-w i) * P i| ≤ (w (Y+1)-w X)*B := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [← hsum,Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ ↦ (abs_mul _ _).le.trans (mul_le_mul_of_nonneg_left (hP _) (abs_nonneg _))
  have hend (i j : ℕ) : |w i*P j| ≤ w i*B := by
    rw [abs_mul,abs_of_nonneg (by dsimp [w]; positivity : 0 ≤ w i)]
    exact mul_le_mul_of_nonneg_left (hP j) (by dsimp [w]; positivity)
  rw [Finset.sum_Ioc_by_parts w g hYX']
  change |w X*P X-w (Y+1)*P Y-∑ i ∈ I, (w (i+1)-w i)*P i| ≤ _
  calc _ ≤ |w X*P X| + |w (Y+1)*P Y| + |∑ i ∈ I, (w (i+1)-w i)*P i| :=
         (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
       _ ≤ w X*B+w (Y+1)*B+(w (Y+1)-w X)*B := add_le_add (add_le_add (hend X X) (hend (Y+1) Y)) hmid
       _ = _ := by simp [w,div_eq_mul_inv]; ring

/-- The complete high flat diagonal has one arithmetic leading coefficient,
with a power-saving error once the lower endpoint exceeds the fourth power
of the mollifier length. The estimate includes all smooth frequencies. -/
theorem spectralLineJet_selbergFlat_high_diagonal (N : ℕ) {Y X : ℕ} (hYX : Y ≤ X) :
    |(∑ m ∈ Finset.Ioc Y X, (spectralLineJet_selbergFlatCoefficient N m)^2/m) -
      spectralLineJet_selbergSieveEnergy N * ∑ m ∈ Finset.Ioc Y X, (m:ℝ)⁻¹| ≤
      2*(N:ℝ)^4/(Y+1) :=
  spectralLineJet_selberg_weighted_discrepancy _ (by positivity)
    (spectralLineJet_selbergFlat_square_discrepancy N) hYX

/-- Diagonalizing the common-multiple kernel by the divisor sum for Euler's
totient expresses the leading coefficient as a sum of nonnegative squares. -/
theorem spectralLineJet_selbergSieveEnergy_totient (N : ℕ) :
    spectralLineJet_selbergSieveEnergy N =
      ∑ k ∈ Finset.Icc 1 (N*N), (k.totient:ℝ) *
        (∑ d ∈ Finset.Icc 1 (N*N) with k ∣ d, spectralLineJet_selbergSquareWeight N d/d)^2 := by
  classical
  let D := Finset.Icc 1 (N*N)
  let a := spectralLineJet_selbergSquareWeight N
  let v (k d : ℕ) : ℝ := if k ∣ d then a d/d else 0
  have hterm (d : ℕ) (hd : d ∈ D) (e : ℕ) (he : e ∈ D) :
      a d*a e/d.lcm e = ∑ k ∈ D, (k.totient:ℝ)*v k d*v k e := by
    obtain ⟨hd0,hdN⟩ := Finset.mem_Icc.mp hd
    obtain ⟨he0,_⟩ := Finset.mem_Icc.mp he
    change 0 < d at hd0
    change 0 < e at he0
    have hg : 0 < d.gcd e := Nat.gcd_pos_of_pos_left e hd0
    have hdvs : D.filter (fun k ↦ k ∣ d ∧ k ∣ e) = (d.gcd e).divisors := by
      ext k
      simp only [Finset.mem_filter,Nat.mem_divisors,Nat.dvd_gcd_iff]
      constructor
      · exact fun h ↦ ⟨h.2,hg.ne'⟩
      · exact fun h ↦ ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos h.1.1 hd0,(Nat.le_of_dvd hd0 h.1.1).trans hdN⟩,h.1⟩
    have htot : (∑ k ∈ D, if k ∣ d ∧ k ∣ e then (k.totient:ℝ) else 0) = d.gcd e := by
      rw [← Finset.sum_filter,hdvs]
      exact_mod_cast Nat.sum_totient (d.gcd e)
    symm
    calc _ = (∑ k ∈ D, if k ∣ d ∧ k ∣ e then (k.totient:ℝ) else 0)*(a d/d)*(a e/e) := by
           simp only [Finset.sum_mul]
           exact Finset.sum_congr rfl fun k _ ↦ by by_cases hk : k∣d <;> by_cases hj : k∣e <;> simp [v,hk,hj]
         _ = _ := by
           rw [htot]
           have hl := Nat.lcm_pos hd0 he0
           have hgcd : (d.gcd e:ℝ)*(d.lcm e:ℝ)=d*e := by exact_mod_cast Nat.gcd_mul_lcm d e
           field_simp [show (d:ℝ)≠0 by exact_mod_cast hd0.ne',show (e:ℝ)≠0 by exact_mod_cast he0.ne',
             show ((d.lcm e:ℕ):ℝ)≠0 by exact_mod_cast hl.ne']
           linear_combination (a d*a e)*hgcd
  change (∑ d ∈ D, ∑ e ∈ D, a d*a e/d.lcm e) = _
  calc _ = ∑ d ∈ D, ∑ e ∈ D, ∑ k ∈ D, (k.totient:ℝ)*v k d*v k e :=
         Finset.sum_congr rfl fun d hd ↦ Finset.sum_congr rfl fun e he ↦ hterm d hd e he
       _ = ∑ k ∈ D, ∑ d ∈ D, ∑ e ∈ D, (k.totient:ℝ)*v k d*v k e := by
         rw [Finset.sum_comm (s := D) (t := D) (f := fun k d ↦ ∑ e ∈ D, (k.totient:ℝ)*v k d*v k e)]
         exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
       _ = _ := by
         refine Finset.sum_congr rfl fun k _ ↦ ?_
         rw [Finset.sum_filter,sq,Finset.sum_mul_sum,Finset.mul_sum]
         refine Finset.sum_congr rfl fun d _ ↦ ?_
         rw [Finset.mul_sum]
         exact Finset.sum_congr rfl fun e _ ↦ mul_assoc _ _ _

private theorem spectralLineJet_selbergSieveEnergy_bounds (N : ℕ) :
    0 ≤ spectralLineJet_selbergSieveEnergy N ∧ spectralLineJet_selbergSieveEnergy N ≤ (N:ℝ)^4 := by
  constructor
  · rw [spectralLineJet_selbergSieveEnergy_totient]
    exact Finset.sum_nonneg fun _ _ ↦ by positivity
  · let D := Finset.Icc 1 (N*N)
    let a := spectralLineJet_selbergSquareWeight N
    calc _ ≤ ∑ d ∈ D, ∑ e ∈ D, |a d| * |a e| := by
           refine Finset.sum_le_sum fun d hd ↦ Finset.sum_le_sum fun e he ↦ ?_
           have hl : (1:ℝ) ≤ d.lcm e := by exact_mod_cast
             (Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1 : 0 < d.lcm e)
           calc _ ≤ |a d*a e/(d.lcm e:ℝ)| := le_abs_self _
                _ ≤ _ := by rw [abs_div,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (d.lcm e:ℝ))]
                            exact div_le_self (by positivity) hl
         _ = (∑ d ∈ D, |a d|)^2 := by rw [sq,Finset.sum_mul_sum]
         _ ≤ _ := by
           calc _ ≤ ((N:ℝ)^2)^2 := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
                    (spectralLineJet_selberg_weight_mass N) 2
                _ = _ := by ring

private theorem spectralLineJet_selberg_harmonic_log {Y X : ℕ} (hY : 0 < Y) (hYX : Y ≤ X) :
    |(∑ m ∈ Finset.Ioc Y X, (m:ℝ)⁻¹) - Real.log ((X:ℝ)/Y)| ≤ (Y:ℝ)⁻¹ := by
  let r (n : ℕ) := (harmonic n:ℝ) - Real.log n - Real.eulerMascheroniConstant
  have hr (n : ℕ) (hn : 0 < n) : 0 ≤ r n ∧ r n ≤ (n:ℝ)⁻¹ := by
    have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
    have hlo := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
    simp only [Real.eulerMascheroniSeq',hn.ne',ite_false] at hlo
    have hhi := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
    change (harmonic n:ℝ) - Real.log ((n:ℝ)+1) < _ at hhi
    have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < ((n:ℝ)+1)/n)
    rw [Real.log_div (by positivity) hn'.ne',add_div,div_self hn'.ne',one_div] at hlog
    dsimp [r]
    exact ⟨by linarith,by linarith⟩
  have hh (n : ℕ) : ∑ m ∈ Finset.Ioc 0 n, (m:ℝ)⁻¹ = (harmonic n:ℝ) := by
    simp [harmonic_eq_sum_Icc,← Finset.Icc_succ_left_eq_Ioc]
  have hsum := Finset.sum_Ioc_consecutive (fun m : ℕ ↦ (m:ℝ)⁻¹) (Nat.zero_le Y) hYX
  rw [hh,hh] at hsum
  have hX := hY.trans_le hYX
  have hid : (∑ m ∈ Finset.Ioc Y X, (m:ℝ)⁻¹) - Real.log ((X:ℝ)/Y) = r X-r Y := by
    rw [Real.log_div (by exact_mod_cast hX.ne') (by exact_mod_cast hY.ne')]
    dsimp [r]; linarith
  rw [hid,abs_le]
  have hcomp : (X:ℝ)⁻¹ ≤ (Y:ℝ)⁻¹ := inv_anti₀ (by exact_mod_cast hY) (by exact_mod_cast hYX)
  exact ⟨by linarith [(hr Y hY).2,(hr X hX).1],by linarith [(hr X hX).2,(hr Y hY).1]⟩

/-- On the full unsieved interval `Y < m ≤ X`, the diagonal has the explicit
main term `log (X/Y)` times Selberg's nonnegative sieve energy. In particular
the absolute error tends to zero whenever `N⁴/Y` does. -/
theorem spectralLineJet_selbergFlat_high_log (N : ℕ) {Y X : ℕ} (hY : 0 < Y) (hYX : Y ≤ X) :
    |(∑ m ∈ Finset.Ioc Y X, (spectralLineJet_selbergFlatCoefficient N m)^2/m) -
      spectralLineJet_selbergSieveEnergy N * Real.log ((X:ℝ)/Y)| ≤ 3*(N:ℝ)^4/Y := by
  let E := spectralLineJet_selbergSieveEnergy N
  let H := ∑ m ∈ Finset.Ioc Y X, (m:ℝ)⁻¹
  let D := ∑ m ∈ Finset.Ioc Y X, (spectralLineJet_selbergFlatCoefficient N m)^2/m
  let L := Real.log ((X:ℝ)/Y)
  obtain ⟨hE,he⟩ := spectralLineJet_selbergSieveEnergy_bounds N
  have hY' : 0 < (Y:ℝ) := by exact_mod_cast hY
  have h1 : |D-E*H| ≤ 2*(N:ℝ)^4/Y := (spectralLineJet_selbergFlat_high_diagonal N hYX).trans
    (div_le_div_of_nonneg_left (by positivity) hY' (by linarith))
  have h2 : |E*(H-L)| ≤ (N:ℝ)^4/Y := by
    rw [abs_mul,abs_of_nonneg hE,div_eq_mul_inv]
    exact mul_le_mul he (spectralLineJet_selberg_harmonic_log hY hYX) (abs_nonneg _) (by positivity)
  change |D-E*L| ≤ _
  calc _ = |(D-E*H)+E*(H-L)| := by congr 1; ring
       _ ≤ |D-E*H|+|E*(H-L)| := abs_add_le _ _
       _ ≤ 2*(N:ℝ)^4/Y+(N:ℝ)^4/Y := add_le_add h1 h2
       _ = _ := by ring

/-- Normalize the divisor sums by Möbius inversion. The squared mollifier
has first coefficient one, so these transformed weights cannot all vanish. -/
private theorem spectralLineJet_selberg_sieve_normalization {N : ℕ} (hN : 0 < N) :
    (∑ k ∈ Finset.Icc 1 (N*N), (ArithmeticFunction.moebius k:ℝ) *
      ∑ d ∈ Finset.Icc 1 (N*N) with k ∣ d, spectralLineJet_selbergSquareWeight N d/d) = 1 := by
  classical
  let D := Finset.Icc 1 (N*N)
  let a := spectralLineJet_selbergSquareWeight N
  let M (k : ℕ) : ℝ := ArithmeticFunction.moebius k
  have hdiv (d : ℕ) (hd : d ∈ D) : D.filter (· ∣ d) = d.divisors := by
    obtain ⟨hd0,hdN⟩ := Finset.mem_Icc.mp hd
    change 0 < d at hd0
    ext k
    rw [Finset.mem_filter,Nat.mem_divisors]
    exact ⟨fun h ↦ ⟨h.2,hd0.ne'⟩,fun h ↦
      ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos h.1 hd0,(Nat.le_of_dvd hd0 h.1).trans hdN⟩,h.1⟩⟩
  have hinv (d : ℕ) : (∑ k ∈ d.divisors, M k) = if d=1 then 1 else 0 := by
    have hid := congrArg (fun f : ArithmeticFunction ℝ ↦ f d)
      (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
    change ((ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) d = _ at hid
    rw [ArithmeticFunction.coe_mul_zeta_apply] at hid
    exact hid
  have h1 : 1 ∈ D := Finset.mem_Icc.mpr ⟨le_rfl,Nat.mul_pos hN hN⟩
  have ha : a 1 = 1 := by
    have hcut : spectralLineJet_selbergCut N spectralLineJet_selbergHalfMoebius 1 = 1 := by
      change (if 1 ∈ Finset.Icc 1 N then _ else 0) = 1
      rw [ite_eq_left (Finset.mem_Icc.mpr ⟨le_rfl,hN⟩)]
      exact spectralLineJet_selbergHalfMoebius_spec.1
    simp [a,spectralLineJet_selbergSquareWeight,hcut]
  calc _ = ∑ d ∈ D, ∑ k ∈ D, if k ∣ d then M k*(a d/d) else 0 := by
         rw [Finset.sum_comm]
         refine Finset.sum_congr rfl fun k _ ↦ ?_
         rw [Finset.mul_sum,Finset.sum_filter]
       _ = ∑ d ∈ D, (if d=1 then 1 else 0)*(a d/d) := by
         refine Finset.sum_congr rfl fun d hd ↦ ?_
         rw [← Finset.sum_filter,← Finset.sum_mul,hdiv _ hd,hinv]
       _ = _ := by
         rw [Finset.sum_eq_single_of_mem 1 h1]
         · simp [ha]
         · intro d _ hd; simp [hd]

/-- The normalizing denominator in Selberg's diagonal quadratic form. The
sum stops at the square of the original mollifier length. -/
def spectralLineJet_selbergSieveDenominator (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (N*N), (ArithmeticFunction.moebius k:ℝ)^2/k.totient

/-- The energy of the actual squared mollifier is the Selberg minimum
`1 / G` plus the explicitly measured departure of its divisor sums from
the optimal weights. Every term in this excess is nonnegative. -/
theorem spectralLineJet_selbergSieveEnergy_excess {N : ℕ} (hN : 0 < N) :
    let G := spectralLineJet_selbergSieveDenominator N
    spectralLineJet_selbergSieveEnergy N = G⁻¹ +
      ∑ k ∈ Finset.Icc 1 (N*N), (k.totient:ℝ) *
        ((∑ d ∈ Finset.Icc 1 (N*N) with k ∣ d, spectralLineJet_selbergSquareWeight N d/d) -
          (ArithmeticFunction.moebius k:ℝ)/(k.totient*G))^2 := by
  classical
  let D := Finset.Icc 1 (N*N)
  let M (k : ℕ) : ℝ := ArithmeticFunction.moebius k
  let t (k : ℕ) := ∑ d ∈ D with k ∣ d, spectralLineJet_selbergSquareWeight N d/d
  let G := spectralLineJet_selbergSieveDenominator N
  have h1 : 1 ∈ D := Finset.mem_Icc.mpr ⟨le_rfl,Nat.mul_pos hN hN⟩
  have hG : 0 < G := by
    apply Finset.sum_pos' (fun _ _ ↦ div_nonneg (sq_nonneg _) (by positivity))
    exact ⟨1,h1,by simp⟩
  have heach (k : ℕ) (hk : k ∈ D) :
      (k.totient:ℝ)*(t k-M k/(k.totient*G))^2 =
        k.totient*(t k)^2-2/G*(M k*t k)+1/G^2*((M k)^2/k.totient) := by
    have hp : 0 < (k.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (Finset.mem_Icc.mp hk).1
    field_simp [hp.ne',hG.ne']; ring
  change _ = G⁻¹+∑ k ∈ D, (k.totient:ℝ)*(t k-M k/(k.totient*G))^2
  rw [Finset.sum_congr rfl heach,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum]
  have hnorm : (∑ k ∈ D, M k*t k)=1 := spectralLineJet_selberg_sieve_normalization hN
  have hspec : (∑ k ∈ D, (k.totient:ℝ)*(t k)^2) = spectralLineJet_selbergSieveEnergy N :=
    (spectralLineJet_selbergSieveEnergy_totient N).symm
  rw [hnorm,hspec]
  change _ = _ + ((_ - _ * 1) + (1/G^2)*G)
  field_simp [hG.ne']; ring

/-- Every flat mode above `Y`, with no restriction on its divisors, obeys
the short-window estimate with the single finite sieve energy and an explicit
error. This includes the interval up to the actual linear taper cutoff. -/
theorem spectralLineJet_selbergGrouped_high_dyadic :
    ∃ K > (0:ℝ), ∀ {H T h : ℝ} (_ : 0 < H) (_ : 1 ≤ T) (_ : 0 ≤ h) (_ : h ≤ T)
      {L N Y X : ℕ} (_ : 0 < Y) (_ : Y ≤ X) (_ : X ≤ L) (_ : (X:ℝ) ≤ 3*T/Real.pi),
      (∫ t in T..2*T, (∫ u in t..t+h, ‖Complex.Gamma (1/4 + ((u/2:ℝ):ℂ)*Complex.I)‖ *
          Real.exp ((Real.pi/4-1/(2*H))*u) *
          ‖∑ m ∈ Finset.Ioc Y X, (spectralLineJet_selbergGroupedCoefficient L N u m : ℂ)*mode(m,u)‖)^2) ≤
      K*h^2*Real.sqrt T *
        (spectralLineJet_selbergSieveEnergy N*Real.log ((X:ℝ)/Y)+3*(N:ℝ)^4/Y) := by
  obtain ⟨K,hK,hmean⟩ := spectralLineJet_selbergGrouped_flat_dyadic
  refine ⟨K,hK,?_⟩
  intro H T h hH hT hh hhT L N Y X hY hYX hL hflat
  have hsub : Finset.Ioc Y X ⊆ Finset.Icc 1 X := by
    intro m hm
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ioc.mp hm
    exact Finset.mem_Icc.mpr ⟨by omega,hhi⟩
  apply (hmean hH hT hh hhT _ hsub hL hflat).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hi := (abs_le.mp (spectralLineJet_selbergFlat_high_log N hY hYX)).2
  linarith

private theorem spectralLineJet_selberg_reciprocal_squares (M : ℕ) :
    ∑ i ∈ Finset.Icc 1 M, ((i:ℝ)⁻¹)^2 ≤ 2 := by
  have h (n : ℕ) : (∑ i ∈ Finset.Icc 1 (n+1), ((i:ℝ)⁻¹)^2) ≤ 2-((n+1:ℕ):ℝ)⁻¹ := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ (n+1)+1)]
      have hp : 0 < ((n+1:ℕ):ℝ) := by positivity
      have hq : 0 < ((n+2:ℕ):ℝ) := by positivity
      have hs : (((n+2:ℕ):ℝ)⁻¹)^2 ≤ ((n+1:ℕ):ℝ)⁻¹-((n+2:ℕ):ℝ)⁻¹ := by
        field_simp [hp.ne',hq.ne']
        push_cast
        nlinarith
      linarith
  cases M with
  | zero => simp
  | succ n => exact (h n).trans (sub_le_self _ (by positivity))

/-- The Dirichlet hyperbola for nonnegative functions is contained in the
product of the two full intervals. -/
private theorem spectralLineJet_selberg_divisor_majorant (M : ℕ) (f g : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) :
    (∑ n ∈ Finset.Icc 1 M, ∑ d ∈ n.divisors, f d*g (n/d)) ≤
      (∑ d ∈ Finset.Icc 1 M, f d)*(∑ e ∈ Finset.Icc 1 M, g e) := by
  classical
  let D := Finset.Icc 1 M
  let S := D ×ˢ D
  let idx (p : ℕ × ℕ) := p.1*p.2
  let w (p : ℕ × ℕ) := f p.1*g p.2
  have he (n : ℕ) (hn : n ∈ D) : S.filter (fun p ↦ idx p=n) = n.divisorsAntidiagonal := by
    obtain ⟨hn0,hnM⟩ := Finset.mem_Icc.mp hn
    change 0 < n at hn0
    ext p
    rw [Finset.mem_filter,Nat.mem_divisorsAntidiagonal]
    refine ⟨fun h ↦ ⟨h.2,hn0.ne'⟩,fun h ↦ ⟨?_,h.1⟩⟩
    obtain ⟨heq,_⟩ := h
    have ha : p.1 ∣ n := heq ▸ dvd_mul_right _ _
    have hb : p.2 ∣ n := heq ▸ dvd_mul_left _ _
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos ha hn0,(Nat.le_of_dvd hn0 ha).trans hnM⟩,
       Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hb hn0,(Nat.le_of_dvd hn0 hb).trans hnM⟩⟩
  calc _ = ∑ n ∈ D, ∑ p ∈ S with idx p=n, w p := by
         refine Finset.sum_congr rfl fun n hn ↦ ?_
         rw [he n hn,← Nat.map_div_right_divisors,Finset.sum_map]
         rfl
       _ = ∑ p ∈ S with idx p ∈ D, w p := Finset.sum_fiberwise_eq_sum_filter S D idx w
       _ ≤ ∑ p ∈ S, w p := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
         fun _ _ _ ↦ mul_nonneg (hf _) (hg _)
       _ = _ := by rw [Finset.sum_mul_sum]; simp [S,D,w,Finset.sum_product]

/-- Every positive integer has a squarefree part. Summing its reciprocal over
the resulting square-times-squarefree indices bounds an entire harmonic sum
by twice the squarefree harmonic mass. -/
private theorem spectralLineJet_selberg_squarefree_mass (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, (n:ℝ)⁻¹) ≤
      2*(∑ n ∈ Finset.Icc 1 M with Squarefree n, (n:ℝ)⁻¹) := by
  classical
  choose r s hrs using fun n : ℕ ↦ exists_sq_mul_squarefree n
  let D := Finset.Icc 1 M
  let S := D ×ˢ D.filter Squarefree
  let pair (n : ℕ) := (r n,s n)
  let w (p : ℕ × ℕ) := ((p.1:ℝ)⁻¹)^2*(p.2:ℝ)⁻¹
  have hinj : Set.InjOn pair (↑D : Set ℕ) := by
    intro n _ m _ h
    have hr : r n=r m := congrArg Prod.fst h
    have hs : s n=s m := congrArg Prod.snd h
    rw [← (hrs n).1,hr,hs,(hrs m).1]
  have hsub : D.image pair ⊆ S := by
    rintro p hp
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hn0,hnM⟩ := Finset.mem_Icc.mp hn
    change 0 < n at hn0
    have hr : r n ∣ n := ⟨r n*s n,by calc n = r n^2*s n := (hrs n).1.symm
                                      _ = _ := by ring⟩
    have hs : s n ∣ n := ⟨r n^2,by rw [mul_comm]; exact (hrs n).1.symm⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hr hn0,(Nat.le_of_dvd hn0 hr).trans hnM⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hs hn0,(Nat.le_of_dvd hn0 hs).trans hnM⟩,(hrs n).2⟩⟩
  calc _ = ∑ n ∈ D, w (pair n) := by
         refine Finset.sum_congr rfl fun n _ ↦ ?_
         change (n:ℝ)⁻¹ = ((r n:ℝ)⁻¹)^2 * (s n:ℝ)⁻¹
         conv_lhs => rw [← (hrs n).1]
         simp [mul_comm]
       _ = ∑ p ∈ D.image pair, w p := (Finset.sum_image hinj).symm
       _ ≤ ∑ p ∈ S, w p := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by dsimp [w]; positivity
       _ = (∑ i ∈ D, ((i:ℝ)⁻¹)^2)*(∑ j ∈ D with Squarefree j, (j:ℝ)⁻¹) := by
         rw [Finset.sum_mul_sum]; simp [S,w,Finset.sum_product]
       _ ≤ _ := mul_le_mul_of_nonneg_right (spectralLineJet_selberg_reciprocal_squares M)
         (Finset.sum_nonneg fun _ _ ↦ by positivity)

private theorem spectralLineJet_selberg_reciprocal_totient (n : ℕ) (hn : 0 < n) :
    (n.totient:ℝ)⁻¹ ≤ n.divisors.card/n := by
  have hφ := Nat.totient_pos.mpr hn
  have hcount : n ≤ n.divisors.card*n.totient := by
    calc n = ∑ d ∈ n.divisors, d.totient := (Nat.sum_totient _).symm
         _ ≤ ∑ _d ∈ n.divisors, n.totient := Finset.sum_le_sum fun d hd ↦
           Nat.le_of_dvd hφ (Nat.totient_dvd_of_dvd (Nat.mem_divisors.mp hd).1)
         _ = _ := by simp
  rw [← one_div,div_le_div_iff₀ (by exact_mod_cast hφ) (by exact_mod_cast hn)]
  simpa using (Nat.cast_le (α := ℝ)).mpr hcount

private theorem spectralLineJet_selberg_squarefree_totient (n : ℕ) (hn : Squarefree n) :
    (n.totient:ℝ)⁻¹ = (∑ d ∈ n.divisors, (d.totient:ℝ)⁻¹)/n := by
  have hn0 := Nat.pos_of_ne_zero hn.ne_zero
  have hφ := Nat.totient_pos.mpr hn0
  have htot : (n:ℝ) = ∑ d ∈ n.divisors, ((n/d).totient:ℝ) := by
    rw [Nat.sum_div_divisors n (fun x : ℕ ↦ (x.totient:ℝ))]
    exact_mod_cast (Nat.sum_totient n).symm
  rw [eq_div_iff (by exact_mod_cast hn.ne_zero)]
  conv_lhs => rhs; rw [htot]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdv := (Nat.mem_divisors.mp hd).1
  have hd0 := Nat.pos_of_mem_divisors hd
  have hde : n/d*d=n := Nat.div_mul_cancel hdv
  have hc := Nat.coprime_of_squarefree_mul (show Squarefree (n/d*d) by rw [hde]; exact hn)
  have he : ((n/d).totient:ℝ)*d.totient=n.totient := by exact_mod_cast (Nat.totient_mul hc).symm.trans (congrArg Nat.totient hde)
  field_simp [show (n.totient:ℝ)≠0 by exact_mod_cast hφ.ne',
    show (d.totient:ℝ)≠0 by exact_mod_cast (Nat.totient_pos.mpr hd0).ne']
  linarith

private theorem spectralLineJet_selberg_divisor_series (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, (n.divisors.card:ℝ)/(n:ℝ)^2) ≤ 4 := by
  let v (d : ℕ) := ((d:ℝ)⁻¹)^2
  have h (n : ℕ) : (n.divisors.card:ℝ)/(n:ℝ)^2 = ∑ d ∈ n.divisors, v d*v (n/d) := by
    calc _ = ∑ _d ∈ n.divisors, ((n:ℝ)⁻¹)^2 := by simp [div_eq_mul_inv]
         _ = _ := by
           refine Finset.sum_congr rfl fun d hd ↦ ?_
           have he : n = d*(n/d) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1).symm
           conv_lhs => rw [he]
           simp [v,mul_pow,mul_comm]
  calc _ = ∑ n ∈ Finset.Icc 1 M, ∑ d ∈ n.divisors, v d*v (n/d) := Finset.sum_congr rfl fun n _ ↦ h n
       _ ≤ (∑ d ∈ Finset.Icc 1 M, v d)*(∑ d ∈ Finset.Icc 1 M, v d) :=
         spectralLineJet_selberg_divisor_majorant M v v (fun _ ↦ sq_nonneg _) (fun _ ↦ sq_nonneg _)
       _ ≤ (2:ℝ)*2 := mul_le_mul (spectralLineJet_selberg_reciprocal_squares M) (spectralLineJet_selberg_reciprocal_squares M)
         (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (by norm_num)
       _ = _ := by norm_num

/-- The Selberg denominator for the full interval has logarithmic size with
explicit constants. Thus its reciprocal has exactly the size needed for
polynomially separated endpoints of the high-frequency band. -/
theorem spectralLineJet_selbergSieveDenominator_harmonic (N : ℕ) :
    (harmonic (N*N):ℝ)/2 ≤ spectralLineJet_selbergSieveDenominator N ∧
      spectralLineJet_selbergSieveDenominator N ≤ 4*(harmonic (N*N):ℝ) := by
  classical
  let M := N*N
  let D := Finset.Icc 1 M
  let v (d : ℕ) := (d.divisors.card:ℝ)/(d:ℝ)^2
  have hh : (harmonic (N*N):ℝ) = ∑ n ∈ D, (n:ℝ)⁻¹ := by simp [M,D,harmonic_eq_sum_Icc]
  have hmob (n : ℕ) (hn : Squarefree n) : (ArithmeticFunction.moebius n:ℝ)^2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hn
  constructor
  · have hs : (∑ n ∈ D with Squarefree n, (n:ℝ)⁻¹) ≤ spectralLineJet_selbergSieveDenominator N := by
      calc _ ≤ ∑ n ∈ D with Squarefree n, (ArithmeticFunction.moebius n:ℝ)^2/n.totient := by
             refine Finset.sum_le_sum fun n hn ↦ ?_
             obtain ⟨hd,hfree⟩ := Finset.mem_filter.mp hn
             rw [hmob n hfree,one_div]
             exact inv_anti₀ (by exact_mod_cast Nat.totient_pos.mpr (Finset.mem_Icc.mp hd).1) (by exact_mod_cast n.totient_le)
           _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ ↦ by positivity
    rw [hh]
    linarith only [spectralLineJet_selberg_squarefree_mass M,hs]
  · have hb (n : ℕ) (hn : n ∈ D) :
        (ArithmeticFunction.moebius n:ℝ)^2/n.totient ≤ ∑ d ∈ n.divisors, v d*((n/d:ℕ):ℝ)⁻¹ := by
      by_cases hf : Squarefree n
      · rw [hmob n hf,one_div,spectralLineJet_selberg_squarefree_totient _ hf,Finset.sum_div]
        refine Finset.sum_le_sum fun d hd ↦ ?_
        have hdv := (Nat.mem_divisors.mp hd).1
        have hn0 : 0<n := (Finset.mem_Icc.mp hn).1
        have hd0 := Nat.pos_of_mem_divisors hd
        have he : d*(n/d)=n := Nat.mul_div_cancel' hdv
        calc _ ≤ ((d.divisors.card:ℝ)/d)/n := by
               exact div_le_div_of_nonneg_right (spectralLineJet_selberg_reciprocal_totient d hd0) (by positivity)
             _ = _ := by
               have hcast : (d:ℝ)*(n/d:ℕ)=n := by exact_mod_cast he
               have he0 : (0:ℝ) < (n/d:ℕ) := by exact_mod_cast Nat.div_pos (Nat.le_of_dvd hn0 hdv) hd0
               dsimp [v]
               rw [← hcast]
               field_simp
      · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hf]
        simp only [Int.cast_zero,zero_pow (by decide : 2≠0),zero_div]
        exact Finset.sum_nonneg fun _ _ ↦ by dsimp [v]; positivity
    rw [hh]
    calc _ ≤ ∑ n ∈ D, ∑ d ∈ n.divisors, v d*((n/d:ℕ):ℝ)⁻¹ := Finset.sum_le_sum hb
         _ ≤ (∑ d ∈ D, v d)*(∑ e ∈ D, (e:ℝ)⁻¹) := spectralLineJet_selberg_divisor_majorant M v (fun e : ℕ ↦ (e:ℝ)⁻¹)
           (fun _ ↦ by dsimp [v]; positivity) (fun _ ↦ by positivity)
         _ ≤ _ := mul_le_mul_of_nonneg_right (spectralLineJet_selberg_divisor_series M)
           (Finset.sum_nonneg fun _ _ ↦ by positivity)

private theorem spectralLineJet_selberg_floor_log {N : ℕ} (hN : 0 < N) :
    0 < spectralLineJet_selbergSieveDenominator N ∧
      Real.log N ≤ (harmonic (N*N):ℝ) ∧
      (spectralLineJet_selbergSieveDenominator N)⁻¹*Real.log N ≤ 2 := by
  let G := spectralLineJet_selbergSieveDenominator N
  have hH := log_add_one_le_harmonic (N*N)
  have hpos : 1 < N*N+1 := Nat.succ_lt_succ (Nat.mul_pos hN hN)
  have hp : 0 < Real.log ((N*N+1:ℕ):ℝ) := Real.log_pos (by exact_mod_cast hpos)
  have hG : 0 < G := by
    have h := (spectralLineJet_selbergSieveDenominator_harmonic N).1
    dsimp [G]; linarith
  have hlog : Real.log N ≤ (harmonic (N*N):ℝ) := by
    apply le_trans _ hH
    apply Real.log_le_log (by exact_mod_cast hN)
    have hn : N ≤ N*N+1 := by nlinarith only [Nat.mul_le_mul_left N hN]
    exact_mod_cast hn
  refine ⟨hG,hlog,?_⟩
  have hl : Real.log N ≤ 2*G := by linarith only [hlog,(spectralLineJet_selbergSieveDenominator_harmonic N).1]
  calc _ = Real.log N/G := by change G⁻¹*_ = _; ring
       _ ≤ _ := (div_le_iff₀ hG).mpr hl

/-- On the full polynomial band from `N⁵` to `N⁶`, the departure of the
actual diagonal from the normalized sieve excess is bounded absolutely.
Consequently boundedness of either quantity along a sequence of mollifier
lengths is equivalent to boundedness of the other. -/
theorem spectralLineJet_selbergFlat_power_band_excess {N : ℕ} (hN : 0 < N) :
    |(∑ m ∈ Finset.Ioc (N^5) (N^6), (spectralLineJet_selbergFlatCoefficient N m)^2/m) -
      (spectralLineJet_selbergSieveEnergy N-(spectralLineJet_selbergSieveDenominator N)⁻¹)*Real.log N|
      ≤ 2+3/(N:ℝ) := by
  let D := ∑ m ∈ Finset.Ioc (N^5) (N^6), (spectralLineJet_selbergFlatCoefficient N m)^2/m
  let Q := spectralLineJet_selbergSieveEnergy N
  let G := spectralLineJet_selbergSieveDenominator N
  have hp : (0:ℝ) < N := by exact_mod_cast hN
  obtain ⟨hg,_,hmin⟩ := spectralLineJet_selberg_floor_log hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN : (1:ℝ) ≤ N)
  have hband : |D-Q*Real.log N| ≤ 3/(N:ℝ) := by
    have hpow : N^5 ≤ N^6 := Nat.pow_le_pow_right hN (by decide)
    have h := spectralLineJet_selbergFlat_high_log N (pow_pos hN 5) hpow
    simp only [Nat.cast_pow] at h
    have hr : ((N:ℝ)^6)/(N:ℝ)^5 = N := by field_simp
    have he : 3*(N:ℝ)^4/(N:ℝ)^5 = 3/N := by field_simp
    simpa only [hr,he] using h
  change |D-(Q-G⁻¹)*Real.log N| ≤ _
  calc _ = |(D-Q*Real.log N)+G⁻¹*Real.log N| := by congr 1; ring
       _ ≤ |D-Q*Real.log N| + |G⁻¹*Real.log N| := abs_add_le _ _
       _ ≤ _ := by
         rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hg.le) hlog)]
         linarith only [hband,hmin]

/-- If the actual squared mollifier's sieve excess is of reciprocal harmonic
size, the required absolute short-window scale follows on the complete high
flat band, without any smoothness or roughness condition on its indices. -/
theorem spectralLineJet_selbergGrouped_high_of_sieve_excess (A : ℕ) :
    ∃ K > (0:ℝ), ∀ {H T h C : ℝ} (_ : 0 < H) (_ : 1 ≤ T) (_ : 0 ≤ h) (_ : h ≤ T)
      {L N Y X : ℕ} (_ : 0 < N) (_ : N^4 ≤ Y) (_ : Y ≤ X) (_ : X ≤ N^A)
      (_ : X ≤ L) (_ : (X:ℝ) ≤ 3*T/Real.pi),
      (spectralLineJet_selbergSieveEnergy N-(spectralLineJet_selbergSieveDenominator N)⁻¹)*
        (harmonic (N*N):ℝ) ≤ C →
      (∫ t in T..2*T, (∫ u in t..t+h, ‖Complex.Gamma (1/4 + ((u/2:ℝ):ℂ)*Complex.I)‖ *
          Real.exp ((Real.pi/4-1/(2*H))*u) *
          ‖∑ m ∈ Finset.Ioc Y X, (spectralLineJet_selbergGroupedCoefficient L N u m : ℂ)*mode(m,u)‖)^2) ≤
      K*h^2*Real.sqrt T*((A:ℝ)*(2+C)+3) := by
  obtain ⟨K,hK,hmean⟩ := spectralLineJet_selbergGrouped_high_dyadic
  refine ⟨K,hK,?_⟩
  intro H T h C hH hT hh hhT L N Y X hN hY hYX hX hL hflat hC
  let Q := spectralLineJet_selbergSieveEnergy N
  let G := spectralLineJet_selbergSieveDenominator N
  have hY0 := (pow_pos hN 4).trans_le hY
  have hX0 := hY0.trans_le hYX
  have hQ : 0 ≤ Q := (spectralLineJet_selbergSieveEnergy_bounds N).1
  have hexc : 0 ≤ Q-G⁻¹ := by
    rw [show Q= _ from spectralLineJet_selbergSieveEnergy_excess hN]
    simp only [G,add_sub_cancel_left]
    exact Finset.sum_nonneg fun _ _ ↦ by positivity
  obtain ⟨hG,hlog,hsmall⟩ := spectralLineJet_selberg_floor_log hN
  have hxlog : Real.log ((X:ℝ)/Y) ≤ (A:ℝ)*Real.log N := by
    calc _ ≤ Real.log X := Real.log_le_log (by positivity) (div_le_self (by positivity) (by exact_mod_cast hY0))
         _ ≤ Real.log ((N:ℝ)^A) := Real.log_le_log (by exact_mod_cast hX0) (by exact_mod_cast hX)
         _ = _ := Real.log_pow _ _
  have hmain : Q*Real.log N ≤ 2+C := by
    have hx := (mul_le_mul_of_nonneg_left hlog hexc).trans hC
    change G⁻¹*Real.log N ≤ 2 at hsmall
    nlinarith only [hsmall,hx]
  have hrem : 3*(N:ℝ)^4/Y ≤ 3 := (div_le_iff₀ (by exact_mod_cast hY0)).mpr
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hY) (by norm_num))
  apply (hmean hH hT hh hhT hY0 hYX hL hflat).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc _ ≤ Q*((A:ℝ)*Real.log N)+3 := add_le_add (mul_le_mul_of_nonneg_left hxlog hQ) hrem
       _ = (A:ℝ)*(Q*Real.log N)+3 := by ring
       _ ≤ _ := by gcongr

/-- Positive square root of the zeta coefficients, obtained by convolving
the untruncated inverse-square-root mollifier with the constant-one series. -/
private def spectralLineJet_selbergHalfZeta : ArithmeticFunction ℝ :=
  spectralLineJet_selbergHalfMoebius * ArithmeticFunction.zeta

private theorem spectralLineJet_selberg_half_local_mass (k : ℕ) :
    |spectralLineJet_selbergHalfCoeff k| ≤
      ∑ i ∈ Finset.range (k+1), spectralLineJet_selbergHalfCoeff i := by
  let b := spectralLineJet_selbergHalfCoeff
  let h (n : ℕ) := ∑ i ∈ Finset.range (n+1), b i
  have hrec (i : ℕ) : ((i:ℝ)+1)*b (i+1)=((i:ℝ)-1/2)*b i := by
    have he := Ring.descPochhammer_eq_factorial_smul_choose (1/2 : ℝ) (i+1)
    rw [descPochhammer_succ_right,Polynomial.smeval_mul,Polynomial.smeval_sub,
      Polynomial.smeval_X,Polynomial.smeval_natCast,Ring.descPochhammer_eq_factorial_smul_choose] at he
    simp only [nsmul_eq_mul,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ] at he
    have hc : ((i:ℝ)+1)*Ring.choose (1/2:ℝ) (i+1)=(1/2-i)*Ring.choose (1/2:ℝ) i := by
      apply mul_left_cancel₀ (show (i.factorial:ℝ)≠0 by positivity)
      linear_combination -he
    dsimp [b,spectralLineJet_selbergHalfCoeff]
    rw [pow_succ]
    linear_combination -((-1:ℝ)^i)*hc
  have hs (i : ℕ) : h (i+1)=h i+b (i+1) := Finset.sum_range_succ _ _
  have hid (i : ℕ) : (2*((i:ℝ)+1))*b (i+1)= -h i := by
    induction i with
    | zero => norm_num [h,b,spectralLineJet_selbergHalfCoeff]
    | succ i ih =>
      have hr := hrec (i+1)
      push_cast at hr ⊢
      rw [hs]
      linear_combination 2*hr+ih
  change |b k| ≤ h k
  induction k with
  | zero => norm_num [h,b,spectralLineJet_selbergHalfCoeff]
  | succ i ih =>
    have hh := (abs_nonneg (b i)).trans ih
    have hp : 0 < 2*((i:ℝ)+1) := by positivity
    have hb : b (i+1) ≤ 0 := nonpos_of_mul_nonpos_right ((hid i).trans_le (neg_nonpos.mpr hh)) hp
    rw [abs_of_nonpos hb,hs]
    nlinarith only [hid i,mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (α := ℝ) i) hb]

private theorem spectralLineJet_selbergHalfZeta_spec :
    (∀ n, |spectralLineJet_selbergHalfMoebius n| ≤ spectralLineJet_selbergHalfZeta n) ∧
    spectralLineJet_selbergHalfZeta * spectralLineJet_selbergHalfZeta = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ∧
    spectralLineJet_selbergHalfZeta * spectralLineJet_selbergHalfMoebius = 1 := by
  let b := spectralLineJet_selbergHalfMoebius
  let h := spectralLineJet_selbergHalfZeta
  let Z : ArithmeticFunction ℝ := ArithmeticFunction.zeta
  have hZ : h.IsMultiplicative :=
    spectralLineJet_selbergHalfMoebius_mult.mul ArithmeticFunction.isMultiplicative_zeta.natCast
  have hinv : h*b=1 := by
    change (b*Z)*b = 1
    rw [mul_right_comm,show b*b=(ArithmeticFunction.moebius : ArithmeticFunction ℝ) from spectralLineJet_selbergHalfMoebius_spec.2.2,ArithmeticFunction.coe_moebius_mul_coe_zeta]
  refine ⟨?_,?_,hinv⟩
  · intro n
    change |b n| ≤ h n
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => simp
    | one => simp [b,spectralLineJet_selbergHalfMoebius_spec.1,hZ.1]
    | prime_pow p j hp _ =>
      change |spectralLineJet_selbergHalfMoebius (p^j)| ≤ (spectralLineJet_selbergHalfMoebius*Z) (p^j)
      rw [spectralLineJet_selbergHalfMoebius_prime_pow hp,ArithmeticFunction.coe_mul_zeta_apply,Nat.sum_divisors_prime_pow hp]
      simpa only [spectralLineJet_selbergHalfMoebius_prime_pow hp] using spectralLineJet_selberg_half_local_mass j
    | coprime i j _ _ hij hi hj =>
      rw [hZ.map_mul_of_coprime hij,spectralLineJet_selbergHalfMoebius_mult.map_mul_of_coprime hij,abs_mul]
      exact mul_le_mul hi hj (abs_nonneg _) ((abs_nonneg _).trans hi)
  · change h*(b*Z)=Z
    rw [← mul_assoc,hinv,one_mul]

private theorem spectralLineJet_selberg_hyperbola_sum (X : ℕ) (f g : ArithmeticFunction ℝ) :
    (∑ n ∈ Finset.Icc 1 X, (f*g) n) =
      ∑ d ∈ Finset.Icc 1 X, f d * ∑ j ∈ Finset.Icc 1 (X/d), g j := by
  classical
  let D := Finset.Icc 1 X
  let S := D ×ˢ D
  let idx (p : ℕ × ℕ) := p.1*p.2
  let w (p : ℕ × ℕ) := f p.1*g p.2
  have he (n : ℕ) (hn : n ∈ D) : S.filter (fun p ↦ idx p=n) = n.divisorsAntidiagonal := by
    obtain ⟨hn0,hnX⟩ := Finset.mem_Icc.mp hn
    change 0<n at hn0
    ext p
    rw [Finset.mem_filter,Nat.mem_divisorsAntidiagonal]
    refine ⟨fun h ↦ ⟨h.2,hn0.ne'⟩,fun h ↦ ⟨?_,h.1⟩⟩
    have ha : p.1 ∣ n := h.1 ▸ dvd_mul_right _ _
    have hb : p.2 ∣ n := h.1 ▸ dvd_mul_left _ _
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos ha hn0,(Nat.le_of_dvd hn0 ha).trans hnX⟩,
       Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hb hn0,(Nat.le_of_dvd hn0 hb).trans hnX⟩⟩
  calc _ = ∑ n ∈ D, ∑ p ∈ S with idx p=n, w p := by
         exact Finset.sum_congr rfl fun n hn ↦ by rw [he n hn]; rfl
       _ = ∑ p ∈ S with idx p ∈ D, w p := Finset.sum_fiberwise_eq_sum_filter S D idx w
       _ = _ := by
         rw [Finset.sum_filter,Finset.sum_product]
         refine Finset.sum_congr rfl fun d hd ↦ ?_
         have hd0 : 0<d := (Finset.mem_Icc.mp hd).1
         have heq : D.filter (fun j ↦ idx (d,j)∈D) = Finset.Icc 1 (X/d) := by
           ext j
           simp only [Finset.mem_filter,D,Finset.mem_Icc,idx,Nat.le_div_iff_mul_le hd0]
           constructor
           · exact fun h ↦ ⟨h.1.1,by simpa only [Nat.mul_comm] using h.2.2⟩
           · exact fun h ↦ ⟨⟨h.1,(Nat.le_mul_of_pos_right j hd0).trans h.2⟩,
               ⟨Nat.mul_pos hd0 h.1,by simpa only [Nat.mul_comm] using h.2⟩⟩
         rw [Finset.mul_sum,← heq,Finset.sum_filter]

private theorem spectralLineJet_selberg_half_harmonic (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, spectralLineJet_selbergHalfZeta n/n)^2 ≤ (harmonic (X*X):ℝ) := by
  classical
  let h := spectralLineJet_selbergHalfZeta
  let D := Finset.Icc 1 X
  let S := D ×ˢ D
  let idx (p : ℕ × ℕ) := p.1*p.2
  let w (p : ℕ × ℕ) := h p.1*h p.2/idx p
  have hn (n : ℕ) : 0≤h n := (abs_nonneg _).trans (spectralLineJet_selbergHalfZeta_spec.1 n)
  have hmap (p : ℕ × ℕ) (hp : p∈S) : idx p∈Finset.Icc 1 (X*X) := by
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1,
      Nat.mul_le_mul (Finset.mem_Icc.mp ha).2 (Finset.mem_Icc.mp hb).2⟩
  calc _ = ∑ p ∈ S, w p := by
         rw [sq,Finset.sum_mul_sum,Finset.sum_product]
         exact Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ by simp [w,idx,h,div_mul_div_comm]
       _ = ∑ m ∈ Finset.Icc 1 (X*X), ∑ p ∈ S with idx p=m, w p := (Finset.sum_fiberwise_of_maps_to hmap w).symm
       _ ≤ ∑ m ∈ Finset.Icc 1 (X*X), (m:ℝ)⁻¹ := by
         refine Finset.sum_le_sum fun m hm ↦ ?_
         have hm0 : 0<m := (Finset.mem_Icc.mp hm).1
         have hsub : S.filter (fun p ↦ idx p=m) ⊆ m.divisorsAntidiagonal := fun p hp ↦
           Nat.mem_divisorsAntidiagonal.mpr ⟨(Finset.mem_filter.mp hp).2,hm0.ne'⟩
         apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ ↦ div_nonneg (mul_nonneg (hn _) (hn _)) (Nat.cast_nonneg _))).trans
         calc (∑ p ∈ m.divisorsAntidiagonal, w p) = (h*h) m/m := by
                rw [ArithmeticFunction.mul_apply,Finset.sum_div]
                exact Finset.sum_congr rfl fun p hp ↦ by simp only [w,idx,(Nat.mem_divisorsAntidiagonal.mp hp).1]
              _ ≤ _ := by rw [show h*h= (ArithmeticFunction.zeta:ArithmeticFunction ℝ) from spectralLineJet_selbergHalfZeta_spec.2.1]
                          simp [ArithmeticFunction.zeta_apply_ne hm0.ne',one_div]
       _ = _ := by simp [harmonic_eq_sum_Icc]

private theorem spectralLineJet_selberg_half_logderiv (n : ℕ) :
    2*(spectralLineJet_selbergHalfZeta n * Real.log n) =
      (spectralLineJet_selbergHalfZeta * ArithmeticFunction.vonMangoldt) n := by
  let D (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ := ⟨fun j ↦ f j*Real.log j,by simp⟩
  let h := spectralLineJet_selbergHalfZeta
  let b := spectralLineJet_selbergHalfMoebius
  let Z : ArithmeticFunction ℝ := ArithmeticFunction.zeta
  let Λ := ArithmeticFunction.vonMangoldt
  have hder (f g : ArithmeticFunction ℝ) : D (f*g)= D f*g+f*D g := by
    ext m
    change (f*g) m*Real.log m = (D f*g) m+(f*D g) m
    rw [ArithmeticFunction.mul_apply,Finset.sum_mul,ArithmeticFunction.mul_apply,ArithmeticFunction.mul_apply,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    obtain ⟨he,hm⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have h0 : p.1*p.2≠0 := he ▸ hm
    have hl : Real.log m=Real.log p.1+Real.log p.2 := by
      rw [← he,Nat.cast_mul,Real.log_mul (by exact_mod_cast (left_ne_zero_of_mul h0))
        (by exact_mod_cast (right_ne_zero_of_mul h0))]
    change f p.1*g p.2*Real.log m = f p.1*Real.log p.1*g p.2+f p.1*(g p.2*Real.log p.2)
    rw [hl]; ring
  have hZ : D Z=Λ*Z := by
    rw [ArithmeticFunction.vonMangoldt_mul_zeta]
    ext m
    by_cases hm : m=0
    · simp [hm]
    · change (ArithmeticFunction.zeta m : ℝ)*Real.log m = Real.log m
      simp [ArithmeticFunction.zeta_apply_ne hm]
  have hh : h*h=Z := spectralLineJet_selbergHalfZeta_spec.2.1
  have hi : h*b=1 := spectralLineJet_selbergHalfZeta_spec.2.2
  have he : D h+D h=h*Λ := by
    calc _ = (D h*h+h*D h)*b := by
           rw [add_mul,mul_comm h (D h),mul_assoc,hi,mul_one]
         _ = D Z*b := by rw [← hder,hh]
         _ = _ := by rw [hZ]; change Λ*Z*b=b*Z*Λ; ring
  have hv := congrArg (fun f : ArithmeticFunction ℝ ↦ f n) he
  change h n*Real.log n+h n*Real.log n=(h*Λ) n at hv
  simpa only [two_mul] using hv

private theorem spectralLineJet_selberg_half_le_one (n : ℕ) : spectralLineJet_selbergHalfZeta n ≤ 1 := by
  let h := spectralLineJet_selbergHalfZeta
  by_cases hn : n=0
  · simp [hn]
  have hp : (n,1) ∈ n.divisorsAntidiagonal := Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.mul_one _,hn⟩
  have hpos (i : ℕ) : 0≤h i := (abs_nonneg _).trans (spectralLineJet_selbergHalfZeta_spec.1 i)
  have hone : h 1=1 :=
    (spectralLineJet_selbergHalfMoebius_mult.mul ArithmeticFunction.isMultiplicative_zeta.natCast).1
  have hh : (h*h) n=1 := by
    rw [show h*h= (ArithmeticFunction.zeta:ArithmeticFunction ℝ) from spectralLineJet_selbergHalfZeta_spec.2.1]
    simp [ArithmeticFunction.zeta_apply_ne hn]
  rw [ArithmeticFunction.mul_apply] at hh
  have hbound := Finset.single_le_sum (f := fun p : ℕ×ℕ ↦ h p.1*h p.2) (fun p _ ↦ mul_nonneg (hpos _) (hpos _)) hp
  simpa [hone,hh] using hbound

private theorem spectralLineJet_selberg_half_log_sum {X : ℕ} (hX : 0 < X) :
    2*(∑ n ∈ Finset.Icc 1 X, spectralLineJet_selbergHalfZeta n*Real.log n) ≤
      (Real.log 4+4)*(X:ℝ)*Real.sqrt (harmonic (X*X):ℝ) := by
  let h := spectralLineJet_selbergHalfZeta
  let C := Real.log 4+4
  have hC : 0≤C := by dsimp [C]; positivity
  have hpsi (d : ℕ) : (∑ j ∈ Finset.Icc 1 (X/d), ArithmeticFunction.vonMangoldt j) ≤ C*((X:ℝ)/d) := by
    have hp := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α := ℝ) (X/d))
    simp only [Chebyshev.psi,Nat.floor_natCast,← Finset.Icc_succ_left_eq_Ioc] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left Nat.cast_div_le hC)
  calc _ = ∑ n ∈ Finset.Icc 1 X, (h*ArithmeticFunction.vonMangoldt) n := by
         rw [Finset.mul_sum]
         exact Finset.sum_congr rfl fun n _ ↦ spectralLineJet_selberg_half_logderiv n
       _ = _ := spectralLineJet_selberg_hyperbola_sum _ _ _
       _ ≤ ∑ d ∈ Finset.Icc 1 X, h d*(C*((X:ℝ)/d)) := by
         refine Finset.sum_le_sum fun d _ ↦ mul_le_mul_of_nonneg_left (hpsi d) ?_
         exact (abs_nonneg _).trans (spectralLineJet_selbergHalfZeta_spec.1 d)
       _ = (C*X)*(∑ d ∈ Finset.Icc 1 X, h d/d) := by
         rw [Finset.mul_sum]
         exact Finset.sum_congr rfl fun _ _ ↦ by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le (spectralLineJet_selberg_half_harmonic X)) (by positivity)

/-- Uniform elementary Chebyshev bound for the positive and absolute coefficients
of the square-root Euler series. It gains a square root of a logarithm in the
actual (unweighted) initial interval. -/
private theorem spectralLineJet_selberg_half_sum :
    ∃ C > (0:ℝ), ∀ X : ℕ, 0 < X →
      (∑ n ∈ Finset.Icc 1 X, spectralLineJet_selbergHalfZeta n) ≤ C*X/Real.sqrt (1+Real.log X) := by
  let K := Real.log 4+4
  refine ⟨K+5,by dsimp [K]; positivity,?_⟩
  intro X hX
  let h := spectralLineJet_selbergHalfZeta
  let D := Finset.Icc 1 X
  let H := 1+Real.log X
  have hxp : (0:ℝ)<X := by exact_mod_cast hX
  have hx1 : (1:ℝ)≤X := by exact_mod_cast hX
  have hlog := Real.log_nonneg hx1
  have hH : 1≤H := by dsimp [H]; linarith
  have hroot : 1≤Real.sqrt H := Real.le_sqrt_of_sq_le (by simpa using hH)
  have hs := Real.sq_sqrt (zero_le_one.trans hH)
  have hC : 0≤K := by dsimp [K]; positivity
  have hh (n : ℕ) : 0 ≤ h n := (abs_nonneg _).trans (spectralLineJet_selbergHalfZeta_spec.1 n)
  have hsum : (∑ n ∈ D, h n) ≤ (X:ℝ) := by
    calc _ ≤ ∑ _n ∈ D, (1:ℝ) := Finset.sum_le_sum fun n _ ↦ spectralLineJet_selberg_half_le_one n
         _ = _ := by simp [D]
  have hharm : (harmonic (X*X):ℝ) ≤ 2*H := by
    have h := harmonic_le_one_add_log (X*X)
    rw [Nat.cast_mul,Real.log_mul hxp.ne' hxp.ne'] at h
    dsimp [H]; linarith
  have hr : Real.sqrt (harmonic (X*X):ℝ) ≤ 2*Real.sqrt H := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith only [hharm,hs,hH]⟩
  have hweighted : (∑ n ∈ D, h n*Real.log n) ≤ K*X*Real.sqrt H := by
    have hbound := (spectralLineJet_selberg_half_log_sum hX).trans (mul_le_mul_of_nonneg_left hr (by positivity))
    change 2*(∑ n ∈ D, h n*Real.log n) ≤ K*X*(2*Real.sqrt H) at hbound
    linarith
  have hdiff : (∑ n ∈ D, h n*(Real.log X-Real.log n)) ≤ 4*X := by
    calc _ ≤ ∑ n ∈ D, 2*Real.sqrt X*(1/Real.sqrt n) := by
           refine Finset.sum_le_sum fun n hn ↦ ?_
           have hn0 : (0:ℝ)<n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
           have hratio := Real.log_le_rpow_div (div_nonneg hxp.le hn0.le) (by norm_num : (0:ℝ)<1/2)
           rw [Real.log_div hxp.ne' hn0.ne',← Real.sqrt_eq_rpow,Real.sqrt_div hxp.le] at hratio
           have hpos : 0 ≤ Real.log X-Real.log n := sub_nonneg.mpr (Real.log_le_log hn0 (by exact_mod_cast (Finset.mem_Icc.mp hn).2))
           calc _ ≤ Real.log X-Real.log n := mul_le_of_le_one_left hpos (spectralLineJet_selberg_half_le_one n)
                _ ≤ _ := by convert hratio using 1; ring
         _ = (2*Real.sqrt X)*∑ n ∈ D, 1/Real.sqrt n := (Finset.mul_sum ..).symm
         _ ≤ (2*Real.sqrt X)*(2*Real.sqrt X) := mul_le_mul_of_nonneg_left (sum_Icc_one_div_sqrt_le_two_mul_sqrt X) (by positivity)
         _ = _ := by nlinarith only [Real.sq_sqrt hxp.le]
  have hid : H*(∑ n ∈ D, h n) = (∑ n ∈ D, h n)+(∑ n ∈ D, h n*Real.log n)+(∑ n ∈ D, h n*(Real.log X-Real.log n)) := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun _ _ ↦ ?_; dsimp [H]; ring
  have hprod := mul_le_mul_of_nonneg_left hroot hxp.le
  apply (le_div_iff₀ (by positivity : 0 < Real.sqrt H)).mpr
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < Real.sqrt H)).mp
  change (∑ n ∈ D, h n)*Real.sqrt H*Real.sqrt H ≤ (K+5)*X*Real.sqrt H
  nlinarith only [hid,hsum,hweighted,hdiff,hprod,hs,show (∑ n ∈ D,h n)*Real.sqrt H*Real.sqrt H = H*(∑ n ∈ D,h n) by rw [mul_assoc,← sq,hs,mul_comm]]

/-- Cancellation of the actual sharp inverse-square-root mollifier at the
real point one, uniformly in its length. The divisor identity for the positive
half-zeta coefficients bounds the rounding error as well as the main sum. -/
theorem spectralLineJet_selbergHalfMoebius_reciprocal_sum :
    ∃ C > (0:ℝ), ∀ X : ℕ, 0 < X →
      |∑ n ∈ Finset.Icc 1 X, spectralLineJet_selbergHalfMoebius n/n| ≤ C/Real.sqrt (1+Real.log X) := by
  obtain ⟨C,hC,hmean⟩ := spectralLineJet_selberg_half_sum
  refine ⟨2*C,by positivity,?_⟩
  intro X hX
  let D := Finset.Icc 1 X
  let b := spectralLineJet_selbergHalfMoebius
  let h := spectralLineJet_selbergHalfZeta
  let err (d : ℕ) : ℝ := (X:ℝ)/d-(X/d:ℕ)
  have herr (d : ℕ) (hd : d ∈ D) : |err d| ≤ 1 := by
    have hd0 : 0<d := (Finset.mem_Icc.mp hd).1
    have hd' : 0<(d:ℝ) := by exact_mod_cast hd0
    have he : (d:ℝ)*(X/d:ℕ)+(X%d:ℕ)=X := by exact_mod_cast Nat.div_add_mod X d
    have hm : ((X%d:ℕ):ℝ) < d := by exact_mod_cast Nat.mod_lt X hd0
    dsimp [err]
    rw [abs_of_nonneg (sub_nonneg.mpr Nat.cast_div_le)]
    have := (div_le_iff₀ hd').mpr (by nlinarith only [he,hm] : (X:ℝ) ≤ (((X/d:ℕ):ℝ)+1)*d)
    linarith
  have hsum : (∑ n ∈ D, h n) = ∑ d ∈ D, b d*(X/d:ℕ) := by
    rw [show (∑ n ∈ D, h n) = _ from spectralLineJet_selberg_hyperbola_sum X b (ArithmeticFunction.zeta : ArithmeticFunction ℝ)]
    refine Finset.sum_congr rfl fun d _ ↦ congrArg (b d * ·) ?_
    calc _ = ∑ _j ∈ Finset.Icc 1 (X/d), (1:ℝ) := by
           exact Finset.sum_congr rfl fun j hj ↦ by have hj0 : 0<j := (Finset.mem_Icc.mp hj).1; simp [ArithmeticFunction.zeta_apply_ne hj0.ne']
         _ = _ := by simp
  have heq : (X:ℝ)*(∑ n ∈ D, b n/n) = (∑ n ∈ D, h n)+∑ d ∈ D, b d*err d := by
    rw [Finset.mul_sum,hsum,← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ ↦ ?_; dsimp [err]; ring
  have hxp : 0<(X:ℝ) := by exact_mod_cast hX
  have hh (n : ℕ) : 0≤h n := (abs_nonneg _).trans (spectralLineJet_selbergHalfZeta_spec.1 n)
  apply (mul_le_mul_iff_right₀ hxp).mp
  change (X:ℝ)*|∑ n ∈ D,b n/n| ≤ _
  calc _ = |(X:ℝ)*(∑ n ∈ D, b n/n)| := by rw [abs_mul,abs_of_pos hxp]
       _ ≤ |∑ n ∈ D, h n|+|∑ d ∈ D, b d*err d| := heq ▸ abs_add_le _ _
       _ ≤ (∑ n ∈ D, h n)+(∑ n ∈ D, h n) := by
         rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ hh _)]
         apply add_le_add le_rfl
         apply (Finset.abs_sum_le_sum_abs _ _).trans
         refine Finset.sum_le_sum fun d hd ↦ ?_
         rw [abs_mul]
         exact (mul_le_of_le_one_right (abs_nonneg _) (herr d hd)).trans (spectralLineJet_selbergHalfZeta_spec.1 d)
       _ ≤ C*X/Real.sqrt (1+Real.log X)+C*X/Real.sqrt (1+Real.log X) := add_le_add (hmean X hX) (hmean X hX)
       _ = _ := by ring

private theorem spectralLineJet_selberg_square_fiber (N : ℕ) {d : ℕ} (hd : 0<d) :
    let B := spectralLineJet_selbergCut N spectralLineJet_selbergHalfMoebius
    let D := Finset.Icc 1 N
    spectralLineJet_selbergSquareWeight N d =
      ∑ p ∈ D ×ˢ D with p.1*p.2=d, B p.1*B p.2 := by
  classical
  intro B D
  let S := (D ×ˢ D).filter (fun p : ℕ×ℕ ↦ p.1*p.2=d)
  have hsub : S ⊆ d.divisorsAntidiagonal := fun p hp ↦
    Nat.mem_divisorsAntidiagonal.mpr ⟨(Finset.mem_filter.mp hp).2,hd.ne'⟩
  change (B*B) d= _
  rw [ArithmeticFunction.mul_apply]
  symm
  apply Finset.sum_subset hsub
  intro p hp hno
  have hne : p ∉ D ×ˢ D := fun h ↦ hno (Finset.mem_filter.mpr ⟨h,(Nat.mem_divisorsAntidiagonal.mp hp).1⟩)
  have hz (i : ℕ) (hi : i ∉ D) : B i=0 := ite_eq_right hi
  by_cases hi : p.1 ∈ D
  · rw [hz p.2 (fun he ↦ hne (Finset.mem_product.mpr ⟨hi,he⟩)),mul_zero]
  · rw [hz p.1 hi,zero_mul]

/-- Every coefficient of the actual squared sharp mollifier is bounded by one.
The absolute mollifier is dominated coefficient by coefficient by the positive
square root of the zeta coefficients. -/
theorem spectralLineJet_selbergSquareWeight_abs_le_one (N n : ℕ) :
    |spectralLineJet_selbergSquareWeight N n| ≤ 1 := by
  let h := spectralLineJet_selbergHalfZeta
  let B := spectralLineJet_selbergCut N spectralLineJet_selbergHalfMoebius
  have hh (i : ℕ) : 0≤h i := (abs_nonneg _).trans (spectralLineJet_selbergHalfZeta_spec.1 i)
  have hb (i : ℕ) : |B i| ≤ h i := by
    change |if i ∈ Finset.Icc 1 N then spectralLineJet_selbergHalfMoebius i else 0| ≤ h i
    split
    · exact spectralLineJet_selbergHalfZeta_spec.1 i
    · simpa using hh i
  by_cases hn : n=0
  · simp [hn]
  change |(B*B) n| ≤ _
  calc _ ≤ ∑ p ∈ n.divisorsAntidiagonal, |B p.1*B p.2| := by rw [ArithmeticFunction.mul_apply]; exact Finset.abs_sum_le_sum_abs _ _
       _ ≤ (h*h) n := Finset.sum_le_sum fun p _ ↦ by rw [abs_mul]; exact mul_le_mul (hb _) (hb _) (abs_nonneg _) (hh _)
       _ = _ := by rw [show h*h= (ArithmeticFunction.zeta:ArithmeticFunction ℝ) from spectralLineJet_selbergHalfZeta_spec.2.1]
                   simp [ArithmeticFunction.zeta_apply_ne hn]

/-- The complete absolute coefficient mass of the convolution square gains
a full logarithm, uniformly in the sharp cutoff. -/
theorem spectralLineJet_selbergSquareWeight_mass :
    ∃ C > (0:ℝ), ∀ N : ℕ, 0<N →
      ∑ d ∈ Finset.Icc 1 (N*N), |spectralLineJet_selbergSquareWeight N d| ≤ C*(N:ℝ)^2/(1+Real.log N) := by
  classical
  obtain ⟨C,hC,hmean⟩ := spectralLineJet_selberg_half_sum
  refine ⟨C^2,by positivity,?_⟩
  intro N hN
  let D := Finset.Icc 1 N
  let S := D ×ˢ D
  let h := spectralLineJet_selbergHalfZeta
  let b := spectralLineJet_selbergHalfMoebius
  let B := spectralLineJet_selbergCut N b
  let idx (p : ℕ×ℕ) := p.1*p.2
  let w (p : ℕ×ℕ) := h p.1*h p.2
  have hmap (p : ℕ×ℕ) (hp : p ∈ S) : idx p ∈ Finset.Icc 1 (N*N) := by
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1,
      Nat.mul_le_mul (Finset.mem_Icc.mp ha).2 (Finset.mem_Icc.mp hb).2⟩
  have hh (i : ℕ) : 0≤h i := (abs_nonneg _).trans (spectralLineJet_selbergHalfZeta_spec.1 i)
  calc _ ≤ ∑ d ∈ Finset.Icc 1 (N*N), ∑ p ∈ S with idx p=d, w p := by
         refine Finset.sum_le_sum fun d hd ↦ ?_
         rw [spectralLineJet_selberg_square_fiber N (Finset.mem_Icc.mp hd).1]
         apply (Finset.abs_sum_le_sum_abs _ _).trans
         refine Finset.sum_le_sum fun p hp ↦ ?_
         obtain ⟨ha,hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
         change |B p.1*B p.2| ≤ h p.1*h p.2
         rw [show B p.1=b p.1 from ite_eq_left ha,show B p.2=b p.2 from ite_eq_left hb,abs_mul]
         exact mul_le_mul (spectralLineJet_selbergHalfZeta_spec.1 _) (spectralLineJet_selbergHalfZeta_spec.1 _) (abs_nonneg _) (hh _)
       _ = (∑ d ∈ D, h d)^2 := by rw [Finset.sum_fiberwise_of_maps_to hmap,sq,Finset.sum_mul_sum]; simp [S,w,Finset.sum_product]
       _ ≤ (C*N/Real.sqrt (1+Real.log N))^2 := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ hh _) (hmean N hN) 2
       _ = _ := by
         have hlog := Real.log_nonneg (by exact_mod_cast hN : (1:ℝ)≤N)
         rw [div_pow,Real.sq_sqrt (by linarith),mul_pow]

private theorem spectralLineJet_selberg_square_reciprocal (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 (N*N), spectralLineJet_selbergSquareWeight N d/d) =
      (∑ d ∈ Finset.Icc 1 N, spectralLineJet_selbergHalfMoebius d/d)^2 := by
  classical
  let D := Finset.Icc 1 N
  let S := D ×ˢ D
  let b := spectralLineJet_selbergHalfMoebius
  let B := spectralLineJet_selbergCut N b
  let idx (p : ℕ×ℕ) := p.1*p.2
  let w (p : ℕ×ℕ) := (b p.1/p.1)*(b p.2/p.2)
  have hmap (p : ℕ×ℕ) (hp : p∈S) : idx p ∈ Finset.Icc 1 (N*N) := by
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1,
      Nat.mul_le_mul (Finset.mem_Icc.mp ha).2 (Finset.mem_Icc.mp hb).2⟩
  calc _ = ∑ d ∈ Finset.Icc 1 (N*N), ∑ p ∈ S with idx p=d, w p := by
         refine Finset.sum_congr rfl fun d hd ↦ ?_
         rw [spectralLineJet_selberg_square_fiber N (Finset.mem_Icc.mp hd).1,Finset.sum_div]
         refine Finset.sum_congr rfl fun p hp ↦ ?_
         obtain ⟨ha,hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
         change B p.1*B p.2/d = _
         rw [show B p.1=b p.1 from ite_eq_left ha,show B p.2=b p.2 from ite_eq_left hb]
         have he : p.1*p.2=d := (Finset.mem_filter.mp hp).2
         simp [w,← he,div_mul_div_comm]
       _ = ∑ p ∈ S, w p := Finset.sum_fiberwise_of_maps_to hmap _
       _ = _ := by rw [sq,Finset.sum_mul_sum]; simp [S,D,w,b,Finset.sum_product]

/-- The contribution of modulus one to the actual Selberg energy gains two
logarithms. Here the divisibility row contains every squared-mollifier
coefficient and its cancellation is essential. -/
theorem spectralLineJet_selbergSieveEnergy_first_row :
    ∃ C > (0:ℝ), ∀ N : ℕ, 0<N →
      (∑ d ∈ Finset.Icc 1 (N*N), spectralLineJet_selbergSquareWeight N d/d)^2 ≤
        C/(1+Real.log N)^2 := by
  obtain ⟨C,hC,hb⟩ := spectralLineJet_selbergHalfMoebius_reciprocal_sum
  refine ⟨C^4,by positivity,?_⟩
  intro N hN
  rw [spectralLineJet_selberg_square_reciprocal]
  let x := ∑ d ∈ Finset.Icc 1 N, spectralLineJet_selbergHalfMoebius d/d
  have hlog := Real.log_nonneg (by exact_mod_cast hN : (1:ℝ)≤N)
  have h := pow_le_pow_left₀ (abs_nonneg x) (hb N hN) 4
  calc (x^2)^2 = |x|^4 := by rw [show (4:ℕ)=2*2 by decide,pow_mul,sq_abs]
       _ ≤ _ := h
       _ = _ := by rw [div_pow,show Real.sqrt (1+Real.log N)^4=(1+Real.log N)^2 by rw [show (4:ℕ)=2*2 by decide,pow_mul,Real.sq_sqrt (by linarith)]]

private theorem spectralLineJet_selberg_divisor_row_bound {M k : ℕ} (hk : 0<k)
    (a : ℕ → ℝ) (ha : ∀ d, |a d| ≤ 1) :
    (∑ d ∈ Finset.Icc 1 M with k ∣ d, |a d|/d) ≤ (harmonic (M/k):ℝ)/k := by
  classical
  let S := (Finset.Icc 1 M).filter (k ∣ ·)
  let q (d : ℕ) := d/k
  have hinj : Set.InjOn q (↑S : Set ℕ) := by
    intro d hd e he hq
    have hdv := (Finset.mem_filter.mp hd).2
    have hev := (Finset.mem_filter.mp he).2
    calc d = k*(d/k) := (Nat.mul_div_cancel' hdv).symm
         _ = k*(e/k) := congrArg (k*·) hq
         _ = e := Nat.mul_div_cancel' hev
  have hsub : S.image q ⊆ Finset.Icc 1 (M/k) := by
    rintro j hj
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hdD,hdv⟩ := Finset.mem_filter.mp hd
    have hd0 : 0<d := (Finset.mem_Icc.mp hdD).1
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hd0 hdv) hk,Nat.div_le_div_right (Finset.mem_Icc.mp hdD).2⟩
  calc _ ≤ ∑ d ∈ S, ((q d:ℝ)⁻¹/(k:ℝ)) := by
         refine Finset.sum_le_sum fun d hd ↦ ?_
         have hdv := (Finset.mem_filter.mp hd).2
         calc _ ≤ 1/(d:ℝ) := div_le_div_of_nonneg_right (ha d) (by positivity)
              _ = _ := by
                have he : (k:ℝ)*(q d:ℕ)=d := by exact_mod_cast Nat.mul_div_cancel' hdv
                rw [← he]; simp [div_eq_mul_inv]
       _ = ∑ j ∈ S.image q, (j:ℝ)⁻¹/(k:ℝ) := (Finset.sum_image (f := fun j : ℕ ↦ (j:ℝ)⁻¹/(k:ℝ)) hinj).symm
       _ ≤ ∑ j ∈ Finset.Icc 1 (M/k), (j:ℝ)⁻¹/(k:ℝ) :=
         Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
       _ = _ := by rw [← Finset.sum_div]; simp [harmonic_eq_sum_Icc]

private theorem spectralLineJet_selberg_totient_absolute_rows (M : ℕ) (a : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 M, (k.totient:ℝ)*(∑ d ∈ Finset.Icc 1 M with k ∣ d, |a d|/d)) =
      ∑ d ∈ Finset.Icc 1 M, |a d| := by
  classical
  let D := Finset.Icc 1 M
  calc _ = ∑ d ∈ D, ∑ k ∈ D with k ∣ d, (k.totient:ℝ)*(|a d|/d) := by
         simp_rw [Finset.mul_sum,Finset.sum_filter]
         rw [Finset.sum_comm]
       _ = _ := by
         refine Finset.sum_congr rfl fun d hd ↦ ?_
         obtain ⟨hd0,hdM⟩ := Finset.mem_Icc.mp hd
         change 0<d at hd0
         have he : D.filter (· ∣ d) = d.divisors := by
           ext k
           rw [Finset.mem_filter,Nat.mem_divisors]
           exact ⟨fun h ↦ ⟨h.2,hd0.ne'⟩,fun h ↦ ⟨Finset.mem_Icc.mpr
             ⟨Nat.pos_of_dvd_of_pos h.1 hd0,(Nat.le_of_dvd hd0 h.1).trans hdM⟩,h.1⟩⟩
         rw [← Finset.sum_mul,he,show (∑ k ∈ d.divisors, (k.totient:ℝ))=d by exact_mod_cast Nat.sum_totient d]
         field_simp

/-- The entire top shell of Selberg divisor rows already has the required
reciprocal-logarithmic energy, for the genuine sharp mollifier. The factor
`U H_U` is explicit and the constant is independent of both cutoffs. -/
theorem spectralLineJet_selbergSieveEnergy_upper_rows :
    ∃ C > (0:ℝ), ∀ N U : ℕ, 0<N →
      (∑ k ∈ Finset.Icc 1 (N*N) with N*N ≤ U*k, (k.totient:ℝ) *
        (∑ d ∈ Finset.Icc 1 (N*N) with k ∣ d, spectralLineJet_selbergSquareWeight N d/d)^2) ≤
        C*U*(harmonic U:ℝ)/(1+Real.log N) := by
  classical
  obtain ⟨C,hC,hb⟩ := spectralLineJet_selbergSquareWeight_mass
  refine ⟨C,hC,?_⟩
  intro N U hN
  let M := N*N
  let D := Finset.Icc 1 M
  let S := D.filter (fun k ↦ M ≤ U*k)
  let a := spectralLineJet_selbergSquareWeight N
  let t (k : ℕ) := ∑ d ∈ D with k ∣ d, a d/d
  let s (k : ℕ) := ∑ d ∈ D with k ∣ d, |a d|/d
  let B := (U:ℝ)*(harmonic U:ℝ)/M
  have hM : 0<(M:ℝ) := by exact_mod_cast Nat.mul_pos hN hN
  have hU : (0:ℝ) ≤ (harmonic U:ℝ) := by simp [harmonic_eq_sum_Icc]; exact Finset.sum_nonneg fun _ _ ↦ by positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hle (k : ℕ) : |t k| ≤ s k := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum fun d _ ↦ by simp [abs_div]
  have hsup (k : ℕ) (hk : k ∈ S) : s k ≤ B := by
    obtain ⟨hd,hlarge⟩ := Finset.mem_filter.mp hk
    have hk0 : 0<k := (Finset.mem_Icc.mp hd).1
    have hk' : 0<(k:ℝ) := by exact_mod_cast hk0
    have hdiv : M/k ≤ U := Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hlarge)
    have hh : (harmonic (M/k):ℝ) ≤ (harmonic U:ℝ) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hdiv) fun _ _ _ ↦ by positivity
    apply (spectralLineJet_selberg_divisor_row_bound hk0 a (spectralLineJet_selbergSquareWeight_abs_le_one N)).trans
    apply (div_le_div_of_nonneg_right hh hk'.le).trans
    dsimp [B]
    rw [div_le_div_iff₀ hk' hM]
    calc _ ≤ (harmonic U:ℝ)*(U*k) := mul_le_mul_of_nonneg_left (by exact_mod_cast hlarge) hU
         _ = _ := by ring
  calc _ ≤ B*∑ k ∈ S, (k.totient:ℝ)*s k := by
         rw [Finset.mul_sum]
         refine Finset.sum_le_sum fun k hk ↦ ?_
         change (k.totient:ℝ)*(t k)^2 ≤ _
         have hi : (t k)^2 ≤ B*s k := by
           rw [← sq_abs,sq]
           exact mul_le_mul ((hle k).trans (hsup k hk)) (hle k) (abs_nonneg _) hB
         exact (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _)).trans_eq (by ring)
       _ ≤ B*∑ k ∈ D, (k.totient:ℝ)*s k := by
         apply mul_le_mul_of_nonneg_left _ hB
         exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ ↦ by dsimp [s]; positivity
       _ = B*∑ d ∈ D, |a d| := congrArg (B*·) (spectralLineJet_selberg_totient_absolute_rows M a)
       _ ≤ B*(C*(N:ℝ)^2/(1+Real.log N)) := mul_le_mul_of_nonneg_left (hb N hN) hB
       _ = _ := by dsimp [B,M]; push_cast; field_simp

private theorem spectralLineJet_selberg_prime_divisor_sum {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0<n) :
    |∑ d ∈ n.divisors with p ∣ d, spectralLineJet_selbergHalfMoebius d| ≤
      if p ∣ n then spectralLineJet_selbergHalfZeta (ordCompl[p] n) else 0 := by
  classical
  let h := spectralLineJet_selbergHalfZeta
  let b := spectralLineJet_selbergHalfMoebius
  let m := ordCompl[p] n
  have hm := Nat.ordCompl_pos p hn.ne'
  have hdiv : n.divisors.filter (fun d ↦ ¬p∣d) = m.divisors := by
    ext d
    rw [Finset.mem_filter,Nat.mem_divisors,Nat.mem_divisors]
    exact ⟨fun e ↦ ⟨Nat.dvd_ordCompl_of_dvd_not_dvd e.1.1 e.2,hm.ne'⟩,fun e ↦
      ⟨⟨e.1.trans (Nat.ordCompl_dvd n p),hn.ne'⟩,fun hh ↦ Nat.not_dvd_ordCompl hp hn.ne' (hh.trans e.1)⟩⟩
  have hz (j : ℕ) : (∑ d ∈ j.divisors, b d)=h j := ArithmeticFunction.coe_mul_zeta_apply.symm
  have he := Finset.sum_filter_add_sum_filter_not n.divisors (p ∣ ·) b
  rw [hdiv,hz,hz] at he
  by_cases hd : p ∣ n
  · rw [ite_eq_left hd]
    have hf : h n=h (ordProj[p] n)*h m := by
      calc h n = h (ordProj[p] n * m) := congrArg h (Nat.ordProj_mul_ordCompl_eq_self n p).symm
           _ = _ := (spectralLineJet_selbergHalfMoebius_mult.mul ArithmeticFunction.isMultiplicative_zeta.natCast).map_mul_of_coprime
             ((Nat.coprime_ordCompl hp hn.ne').pow_left (n.factorization p))
    have hpos (i : ℕ) : 0≤h i := (abs_nonneg _).trans (spectralLineJet_selbergHalfZeta_spec.1 i)
    have hle : h n ≤ h m := hf.trans_le (mul_le_of_le_one_left (hpos _) (spectralLineJet_selberg_half_le_one _))
    change |∑ d ∈ n.divisors with p∣d,b d| ≤ h m
    rw [abs_of_nonpos (by linarith : (∑ d ∈ n.divisors with p∣d,b d) ≤ 0)]
    linarith [hpos n]
  · rw [ite_eq_right hd,Finset.sum_eq_zero,abs_zero]
    · intro d hdv
      obtain ⟨h1,h2⟩ := Finset.mem_filter.mp hdv
      exact False.elim (hd (h2.trans (Nat.mem_divisors.mp h1).1))

private theorem spectralLineJet_selberg_prime_rounding {p X : ℕ} (hp : p.Prime) (hX : 0<X) :
    (X:ℝ)*|∑ d ∈ Finset.Icc 1 X with p ∣ d, spectralLineJet_selbergHalfMoebius d/d| ≤
      2*(∑ n ∈ Finset.Icc 1 X with p ∣ n, spectralLineJet_selbergHalfZeta (ordCompl[p] n)) := by
  classical
  let b := spectralLineJet_selbergHalfMoebius
  let h := spectralLineJet_selbergHalfZeta
  let f : ArithmeticFunction ℝ := ⟨fun d ↦ if p ∣ d then b d else 0,by simp⟩
  let Z : ArithmeticFunction ℝ := ArithmeticFunction.zeta
  let D := Finset.Icc 1 X
  let c (d : ℕ) := if p ∣ d then h (ordCompl[p] d) else 0
  have hpos (i : ℕ) : 0≤h i := (abs_nonneg _).trans (spectralLineJet_selbergHalfZeta_spec.1 i)
  have hf (n : ℕ) (hn : 0<n) : |f n| ≤ c n := by
    change |if p ∣ n then b n else 0| ≤ _
    by_cases hpn : p ∣ n
    · simp only [hpn,ite_true,c]
      apply (spectralLineJet_selbergHalfZeta_spec.1 n).trans
      have hc := (Nat.coprime_ordCompl hp hn.ne').pow_left (n.factorization p)
      have eqm := (spectralLineJet_selbergHalfMoebius_mult.mul ArithmeticFunction.isMultiplicative_zeta.natCast).map_mul_of_coprime hc
      change h (ordProj[p] n*ordCompl[p] n)=h (ordProj[p] n)*h (ordCompl[p] n) at eqm
      rw [Nat.ordProj_mul_ordCompl_eq_self] at eqm
      exact eqm.trans_le (mul_le_of_le_one_left (hpos _) (spectralLineJet_selberg_half_le_one _))
    · simp [hpn,c]
  have hcount : (∑ n ∈ D, (f*Z) n)=∑ d ∈ D, f d*(X/d:ℕ) := by
    rw [spectralLineJet_selberg_hyperbola_sum]
    refine Finset.sum_congr rfl fun d _ ↦ congrArg (f d*·) ?_
    calc _ = ∑ _j ∈ Finset.Icc 1 (X/d), (1:ℝ) := by
           refine Finset.sum_congr rfl fun j hj ↦ ?_
           have hj0 : 0<j := (Finset.mem_Icc.mp hj).1
           simp [Z,ArithmeticFunction.zeta_apply_ne hj0.ne']
         _ = _ := by simp
  have hz (n : ℕ) (hn : n ∈ D) : |(f*Z) n| ≤ c n := by
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    change |∑ d ∈ n.divisors, if p∣d then b d else 0| ≤ _
    rw [← Finset.sum_filter]
    exact spectralLineJet_selberg_prime_divisor_sum hp (Finset.mem_Icc.mp hn).1
  have hr (d : ℕ) (hd : d ∈ D) : |(X:ℝ)/d-(X/d:ℕ)| ≤ 1 := by
    have hd0 : 0<d := (Finset.mem_Icc.mp hd).1
    have he : (d:ℝ)*(X/d:ℕ)+(X%d:ℕ)=X := by exact_mod_cast Nat.div_add_mod X d
    have hm : ((X%d:ℕ):ℝ) < d := by exact_mod_cast Nat.mod_lt X hd0
    rw [abs_of_nonneg (sub_nonneg.mpr Nat.cast_div_le)]
    have := (div_le_iff₀ (by exact_mod_cast hd0 : 0<(d:ℝ))).mpr (by nlinarith only [he,hm] : (X:ℝ) ≤ (((X/d:ℕ):ℝ)+1)*d)
    linarith
  have hsplit : (X:ℝ)*(∑ d ∈ D with p∣d,b d/d) =
      (∑ n ∈ D, (f*Z) n)+(∑ d ∈ D, f d*((X:ℝ)/d-(X/d:ℕ))) := by
    rw [Finset.sum_filter,Finset.mul_sum,hcount,← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    by_cases hd : p ∣ d <;> simp [f,hd]; ring
  rw [← abs_of_pos (by exact_mod_cast hX : 0<(X:ℝ)) (a := (X:ℝ)),← abs_mul,hsplit,Finset.sum_filter]
  refine (abs_add_le _ _).trans ?_
  change _ ≤ 2*∑ n ∈ D, c n
  have h1 := (Finset.abs_sum_le_sum_abs (fun n ↦ (f*Z) n) D).trans (Finset.sum_le_sum hz)
  have h2 : |∑ d ∈ D, f d*((X:ℝ)/d-(X/d:ℕ))| ≤ ∑ d ∈ D, c d := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    refine Finset.sum_le_sum fun d hd ↦ ?_
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hr d hd)).trans (hf d (Finset.mem_Icc.mp hd).1)
  linarith

private theorem spectralLineJet_selberg_prime_layers {p X : ℕ} (hp : p.Prime) :
    (∑ n ∈ Finset.Icc 1 X with p ∣ n, spectralLineJet_selbergHalfZeta (ordCompl[p] n)) ≤
      ∑ j ∈ Finset.Icc 1 X with p^j ≤ X, ∑ m ∈ Finset.Icc 1 (X/p^j), spectralLineJet_selbergHalfZeta m := by
  classical
  let R := (Finset.Icc 1 X).filter (p ∣ ·)
  let J := (Finset.Icc 1 X).filter (fun j ↦ p^j≤X)
  let idx (n : ℕ) := n.factorization p
  let f (n : ℕ) := ordCompl[p] n
  let h := spectralLineJet_selbergHalfZeta
  have hmap (n : ℕ) (hn : n∈R) : idx n ∈ J := by
    obtain ⟨hnD,hd⟩ := Finset.mem_filter.mp hn
    have hn0 : 0<n := (Finset.mem_Icc.mp hnD).1
    have hpow := (Nat.ordProj_le p hn0.ne').trans (Finset.mem_Icc.mp hnD).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.factorization_pos_of_dvd hn0.ne' hd,
      (Nat.lt_pow_self hp.one_lt).le.trans hpow⟩,hpow⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun n ↦ h (f n))]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  let S := R.filter (fun n ↦ idx n=j)
  have he (n : ℕ) (hn : n∈S) : p^j*f n=n := by
    have hidx : idx n=j := (Finset.mem_filter.mp hn).2
    rw [← hidx]; exact Nat.ordProj_mul_ordCompl_eq_self n p
  have hinj : Set.InjOn f (↑S : Set ℕ) := by
    intro n hn m hm hnm
    exact (he n hn).symm.trans ((congrArg (p^j*·) hnm).trans (he m hm))
  have hsub : S.image f ⊆ Finset.Icc 1 (X/p^j) := by
    rintro y hy
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hn0,hnX⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
    exact Finset.mem_Icc.mpr ⟨Nat.ordCompl_pos p (by omega),
      (Nat.le_div_iff_mul_le (pow_pos hp.pos _)).mpr (by rw [Nat.mul_comm,he n hn]; exact hnX)⟩
  calc _ = ∑ m ∈ S.image f, h m := (Finset.sum_image (f := h) hinj).symm
       _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦
         (abs_nonneg _).trans (spectralLineJet_selbergHalfZeta_spec.1 _)

private theorem spectralLineJet_selberg_prime_geom (p X : ℕ) (hp : 2 ≤ p) :
    (∑ j ∈ Finset.Icc 1 X, ((j:ℝ)+1)/(p:ℝ)^j) ≤ 6/p := by
  have hp' : 0 < (p:ℝ) := by exact_mod_cast (by omega : 0<p)
  have h (x : ℕ) :
      (p:ℝ)*(∑ j ∈ Finset.Icc 1 x, ((j:ℝ)+1)/(p:ℝ)^j) ≤ 6-(2*x+6)/(2:ℝ)^x := by
    induction x with
    | zero => norm_num
    | succ x ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1≤x+1),mul_add]
      have he : (p:ℝ)*(((x+1:ℕ):ℝ)+1)/(p:ℝ)^(x+1) = ((x:ℝ)+2)/(p:ℝ)^x := by
        rw [pow_succ]; push_cast; field_simp; ring
      have hstep : (p:ℝ)*((((x+1:ℕ):ℝ)+1)/(p:ℝ)^(x+1)) ≤ ((x:ℝ)+2)/(2:ℝ)^x := by
        rw [← mul_div_assoc,he]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hp) x)
      apply (add_le_add ih hstep).trans_eq
      push_cast; rw [pow_succ]; field_simp; ring
  apply (le_div_iff₀ hp').mpr
  rw [mul_comm]
  exact (h X).trans (sub_le_self _ (by positivity))

private theorem spectralLineJet_selberg_prime_layer_scale {X p j : ℕ} (hp : 2 ≤ p) (hj : p^j ≤ X) :
    Real.sqrt (1+Real.log X) ≤
      2*((j:ℝ)+1)*Real.sqrt (1+Real.log p)*Real.sqrt (1+Real.log (X/p^j:ℕ)) := by
  let y := X/p^j
  have hp0 : 0<p := by omega
  have hr := pow_pos hp0 j
  have hy : 0<y := Nat.div_pos hj hr
  have hy' : 0 < (y:ℝ) := by exact_mod_cast hy
  have hp' : 0 < (p:ℝ) := by exact_mod_cast hp0
  have hx' : 0 < (X:ℝ) := by exact_mod_cast hr.trans_le hj
  have hX : X ≤ 2*y*p^j := by
    have he := Nat.div_add_mod X (p^j)
    have hm := Nat.mod_lt X hr
    change p^j*y+X%p^j=X at he
    nlinarith only [he,hm,Nat.mul_le_mul_left (p^j) hy]
  have hxp : Real.log X ≤ Real.log 2+Real.log y+j*Real.log p := by
    have hl := Real.log_le_log hx' (by exact_mod_cast hX : (X:ℝ) ≤ 2*y*(p:ℝ)^j)
    rwa [Real.log_mul (by positivity) (pow_ne_zero _ hp'.ne'),Real.log_mul (by norm_num) hy'.ne',Real.log_pow] at hl
  have hylog : 0≤Real.log y := Real.log_nonneg (by exact_mod_cast hy)
  have hplog : 0≤Real.log p := Real.log_nonneg (by exact_mod_cast (by omega : 1≤p))
  have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have H : 0 ≤ (2*((j:ℝ)+1))^2*(1+Real.log p)*(1+Real.log y)-
      (2+Real.log y+j*Real.log p) := by ring_nf; positivity
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  change 1+Real.log X ≤ (2*((j:ℝ)+1)*Real.sqrt (1+Real.log p)*Real.sqrt (1+Real.log y))^2
  rw [mul_pow,mul_pow,Real.sq_sqrt (by linarith),Real.sq_sqrt (by linarith)]
  linarith

/-- Uniform cancellation survives restriction to the multiples of any prime.
The coefficient loss in the modulus is explicit, and the logarithmic gain
uses the original cutoff `X`, even when the prime grows with it. -/
theorem spectralLineJet_selbergHalfMoebius_prime_sum :
    ∃ C > (0:ℝ), ∀ {p X : ℕ}, p.Prime → 0<X →
      |∑ d ∈ Finset.Icc 1 X with p ∣ d, spectralLineJet_selbergHalfMoebius d/d| ≤
        C*Real.sqrt (1+Real.log p)/(p*Real.sqrt (1+Real.log X)) := by
  classical
  obtain ⟨C,hC,hm⟩ := spectralLineJet_selberg_half_sum
  refine ⟨24*C,by positivity,?_⟩
  intro p X hp hX
  let h := spectralLineJet_selbergHalfZeta
  let A (n : ℕ) := Real.sqrt (1+Real.log n)
  let J := (Finset.Icc 1 X).filter (fun j ↦ p^j≤X)
  let R := (Finset.Icc 1 X).filter (p ∣ ·)
  let s := ∑ d ∈ R, spectralLineJet_selbergHalfMoebius d/d
  have hA (n : ℕ) (hn : 0<n) : 0<A n := by
    dsimp [A]; exact Real.sqrt_pos.mpr (by linarith [Real.log_nonneg (by exact_mod_cast hn : (1:ℝ)≤n)])
  have hx' : 0<(X:ℝ) := by exact_mod_cast hX
  have hp' : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have hxA := hA X hX
  have hpA := hA p hp.pos
  have hrow (j : ℕ) (hj : j∈J) : (∑ m ∈ Finset.Icc 1 (X/p^j), h m)*A X ≤
      (2*C*X*A p)*(((j:ℝ)+1)/(p:ℝ)^j) := by
    let y := X/p^j
    have hpj := pow_pos hp.pos j
    have hpow := (Finset.mem_filter.mp hj).2
    have hy : 0<y := Nat.div_pos hpow hpj
    have hyA := hA y hy
    have hpos : 0 ≤ ∑ m ∈ Finset.Icc 1 y, h m := Finset.sum_nonneg fun _ _ ↦
      (abs_nonneg _).trans (spectralLineJet_selbergHalfZeta_spec.1 _)
    have hscale : A X ≤ 2*((j:ℝ)+1)*A p*A y := spectralLineJet_selberg_prime_layer_scale hp.two_le hpow
    have hdiv : (y:ℝ) ≤ X/(p:ℝ)^j := by simpa using (Nat.cast_div_le (α := ℝ) (m := X) (n := p^j))
    calc _ ≤ (C*y/A y)*(2*((j:ℝ)+1)*A p*A y) := mul_le_mul (hm y hy) hscale hxA.le (by positivity)
         _ = (2*C*((j:ℝ)+1)*A p)*y := by field_simp
         _ ≤ (2*C*((j:ℝ)+1)*A p)*(X/(p:ℝ)^j) := mul_le_mul_of_nonneg_left hdiv (by positivity)
         _ = _ := by ring
  have hs : (∑ n ∈ R, h (ordCompl[p] n))*A X ≤ (2*C*X*A p)*(6/p) := by
    apply (mul_le_mul_of_nonneg_right (spectralLineJet_selberg_prime_layers (X := X) hp) hxA.le).trans
    rw [Finset.sum_mul]
    apply (Finset.sum_le_sum hrow).trans
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply le_trans _ (spectralLineJet_selberg_prime_geom p X hp.two_le)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ ↦ by positivity
  have hbound := mul_le_mul_of_nonneg_right (spectralLineJet_selberg_prime_rounding hp hX) hxA.le
  change (X:ℝ) * |s| * A X ≤ (2*∑ n ∈ R, h (ordCompl[p] n))*A X at hbound
  apply (le_div_iff₀ (mul_pos hp' hxA)).mpr
  change |s| * ((p:ℝ)*A X) ≤ 24*C*A p
  have hfinal : (X:ℝ) * |s| * A X ≤ (24*C*X*A p)/p := by
    calc _ ≤ 2*((2*C*X*A p)*(6/p)) := by linarith only [hbound,hs]
         _ = _ := by ring
  have hx := (le_div_iff₀ hp').mp hfinal
  apply (mul_le_mul_iff_right₀ hx').mp
  nlinarith only [hx]

private theorem spectralLineJet_selberg_square_prime_row {p : ℕ} (hp : p.Prime) (N : ℕ) :
    let D := Finset.Icc 1 N
    let b := spectralLineJet_selbergHalfMoebius
    let V := ∑ d ∈ D, b d/d
    let P := ∑ d ∈ D with p ∣ d, b d/d
    (∑ m ∈ Finset.Icc 1 (N*N) with p ∣ m, spectralLineJet_selbergSquareWeight N m/m) = 2*V*P-P^2 := by
  classical
  intro D b V P
  let B := spectralLineJet_selbergCut N b
  let u (d : ℕ) : ℝ := if p ∣ d then 0 else b d/d
  let S := D ×ˢ D
  let idx (z : ℕ×ℕ) := z.1*z.2
  let M := Finset.Icc 1 (N*N)
  let a (d : ℕ) := spectralLineJet_selbergSquareWeight N d/d
  have hmap (z : ℕ×ℕ) (hz : z∈S) : idx z∈M := by
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hz
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1,
      Nat.mul_le_mul (Finset.mem_Icc.mp ha).2 (Finset.mem_Icc.mp hb).2⟩
  have hcop : (∑ m ∈ M with ¬p∣m, a m)=(∑ d ∈ D, u d)^2 := by
    calc _ = ∑ m ∈ M, ∑ z ∈ S with idx z=m, u z.1*u z.2 := by
           rw [Finset.sum_filter]
           refine Finset.sum_congr rfl fun m hm ↦ ?_
           by_cases hpm : p∣m
           · rw [ite_eq_right (not_not_intro hpm),Finset.sum_eq_zero]
             intro z hz
             have he : z.1*z.2=m := (Finset.mem_filter.mp hz).2
             rcases hp.dvd_mul.mp (he ▸ hpm) with h | h <;> simp [u,h]
           · rw [ite_eq_left hpm]
             change spectralLineJet_selbergSquareWeight N m/m = _
             rw [spectralLineJet_selberg_square_fiber N (Finset.mem_Icc.mp hm).1,Finset.sum_div]
             refine Finset.sum_congr rfl fun z hz ↦ ?_
             obtain ⟨ha,hb⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hz).1
             have he : z.1*z.2=m := (Finset.mem_filter.mp hz).2
             have hn := mt hp.dvd_mul.mpr (show ¬p∣z.1*z.2 by rwa [he])
             change B z.1*B z.2/m = _
             rw [show B z.1=b z.1 from ite_eq_left ha,show B z.2=b z.2 from ite_eq_left hb]
             simp [u,(not_or.mp hn).1,(not_or.mp hn).2,← he,div_mul_div_comm]
         _ = ∑ z ∈ S, u z.1*u z.2 := Finset.sum_fiberwise_of_maps_to hmap _
         _ = _ := by rw [sq,Finset.sum_mul_sum]; simp [S,Finset.sum_product]
  have hu : (∑ d ∈ D,u d)=V-P := by
    have hc := Finset.sum_filter_add_sum_filter_not D (p ∣ ·) (fun d ↦ b d/d)
    have heq : (∑ d ∈ D with ¬p∣d,b d/d)=∑ d ∈ D,u d := by rw [Finset.sum_filter]; simp [u,ite_not]
    rw [heq] at hc; dsimp [V,P]; linarith
  have hc := Finset.sum_filter_add_sum_filter_not M (p ∣ ·) a
  rw [hcop,hu,show (∑ d ∈ M, a d)=V^2 from spectralLineJet_selberg_square_reciprocal N] at hc
  change (∑ m ∈ M with p∣m, a m)=_
  nlinarith only [hc]

private theorem spectralLineJet_selberg_prime_log_mass {N : ℕ} (hN : 0<N) :
    (∑ p ∈ Finset.Icc 1 N with p.Prime, (1+Real.log p)/p) ≤ 3*(1+Real.log N) := by
  classical
  let D := Finset.Icc 1 N
  let P := D.filter Nat.Prime
  let Λ := ArithmeticFunction.vonMangoldt
  let Z : ArithmeticFunction ℝ := ArithmeticFunction.zeta
  have hn' : 0<(N:ℝ) := by exact_mod_cast hN
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hlog := Real.log_nonneg hn1
  have hψ : (∑ d ∈ D, Λ d*(N/d:ℕ)) = ∑ n ∈ D, Real.log n := by
    have he := spectralLineJet_selberg_hyperbola_sum N Λ Z
    rw [ArithmeticFunction.vonMangoldt_mul_zeta] at he
    change (∑ n ∈ D,Real.log n) = _ at he
    rw [he]
    refine Finset.sum_congr rfl fun d _ ↦ congrArg (Λ d*·) ?_
    symm
    calc _ = ∑ _i ∈ Finset.Icc 1 (N/d), (1:ℝ) := by
           exact Finset.sum_congr rfl fun i hi ↦ by have hi0 : 0 < i := (Finset.mem_Icc.mp hi).1; simp [Z,ArithmeticFunction.zeta_apply_ne hi0.ne']
         _ = _ := by simp
  have hpineq : (N:ℝ)*(∑ p ∈ P, Real.log p/p) ≤ 2*(N*Real.log N) := by
    calc _ = ∑ p ∈ P, Real.log p*((N:ℝ)/p) := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
         _ ≤ 2*∑ p ∈ P, Λ p*(N/p:ℕ) := by
           rw [Finset.mul_sum]
           refine Finset.sum_le_sum fun p hp ↦ ?_
           obtain ⟨hd,hprime⟩ := Finset.mem_filter.mp hp
           have hp0 := hprime.pos
           have hpN := (Finset.mem_Icc.mp hd).2
           have hquot := Nat.div_pos hpN hp0
           have hsize : N≤2*(N/p)*p := by
             have he := Nat.div_add_mod N p
             have hr := Nat.mod_lt N hp0
             nlinarith only [he,hr,Nat.mul_le_mul_left p hquot]
           have hreal : (N:ℝ)/p ≤ 2*(N/p:ℕ) := (div_le_iff₀ (by exact_mod_cast hp0)).mpr (by exact_mod_cast hsize)
           rw [show Λ p=Real.log p from ArithmeticFunction.vonMangoldt_apply_prime hprime]
           exact (mul_le_mul_of_nonneg_left hreal (Real.log_nonneg (by exact_mod_cast hp0))).trans_eq (by ring)
         _ ≤ 2*∑ d ∈ D, Λ d*(N/d:ℕ) := by
           apply mul_le_mul_of_nonneg_left _ (by norm_num)
           exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun d _ _ ↦
             mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
         _ ≤ _ := by
           rw [hψ]
           apply mul_le_mul_of_nonneg_left _ (by norm_num)
           calc _ ≤ ∑ _n ∈ D, Real.log N := Finset.sum_le_sum fun n hn ↦
                    Real.log_le_log (by exact_mod_cast (Finset.mem_Icc.mp hn).1) (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
                _ = _ := by simp [D]
  have hL : (∑ p ∈ P, Real.log p/p) ≤ 2*Real.log N := by apply (mul_le_mul_iff_right₀ hn').mp; linarith
  have hh : (∑ p ∈ P, 1/(p:ℝ)) ≤ 1+Real.log N := by
    apply le_trans _ (harmonic_le_one_add_log N)
    have he : (harmonic N:ℝ) = ∑ p ∈ D, 1/(p:ℝ) := by simp [harmonic_eq_sum_Icc,D,one_div]
    rw [he]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ ↦ by positivity
  simp_rw [add_div,Finset.sum_add_distrib]
  change (∑ p ∈ P,1/(p:ℝ))+(∑ p ∈ P,Real.log p/p) ≤ _
  linarith

private theorem spectralLineJet_selberg_prime_row_pointwise :
    ∃ C > (0:ℝ), ∀ {p N : ℕ}, p.Prime → 0<N →
      (p.totient:ℝ)*(∑ d ∈ Finset.Icc 1 (N*N) with p ∣ d, spectralLineJet_selbergSquareWeight N d/d)^2 ≤
        C*((1+Real.log p)/p)/(1+Real.log N)^2 := by
  classical
  obtain ⟨K,hK,hall⟩ := spectralLineJet_selbergHalfMoebius_reciprocal_sum
  obtain ⟨B,hB,hpr⟩ := spectralLineJet_selbergHalfMoebius_prime_sum
  let C := B*(2*K+B)
  refine ⟨C^2,by dsimp [C]; positivity,?_⟩
  intro p N hp hN
  let H (n : ℕ) := 1+Real.log n
  let A (n : ℕ) := Real.sqrt (H n)
  let V := ∑ d ∈ Finset.Icc 1 N, spectralLineJet_selbergHalfMoebius d/d
  let P := ∑ d ∈ Finset.Icc 1 N with p∣d, spectralLineJet_selbergHalfMoebius d/d
  have hHp (n : ℕ) (hn : 0<n) : 0<H n := by dsimp [H]; linarith [Real.log_nonneg (by exact_mod_cast hn : (1:ℝ)≤n)]
  have hA (n : ℕ) (hn : 0<n) : 0<A n := Real.sqrt_pos.mpr (hHp n hn)
  have hN' := hA N hN
  have hpA := hA p hp.pos
  have hp' : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have hple : A p ≤ (p:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨hp'.le,?_⟩
    have hh := Real.log_le_sub_one_of_pos hp'
    change 1+Real.log p ≤ (p:ℝ)^2
    nlinarith only [hh,show (1:ℝ)≤p by exact_mod_cast hp.pos]
  have h1 : |V| ≤ K/A N := hall N hN
  have h2 : |P| ≤ B*A p/(p*A N) := hpr hp hN
  have h3 : |P| ≤ B/A N := h2.trans (by
    rw [div_le_div_iff₀ (mul_pos hp' hN') hN']
    calc _ ≤ B*p*A N := by gcongr
         _ = _ := by ring)
  have ht : |2*V*P-P^2| ≤ C*A p/(p*H N) := by
    calc _ = |P| * |2*V-P| := by rw [← abs_mul]; apply congrArg abs; ring
         _ ≤ |P| * (2*|V|+|P|) := by
           apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
           simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] using abs_sub (2*V) P
         _ ≤ (B*A p/(p*A N))*(2*(K/A N)+B/A N) := by
           apply mul_le_mul h2 _ (by positivity) (by positivity)
           linarith only [h1,h3]
         _ = _ := by
           have he : (A N)^2=H N := Real.sq_sqrt (hHp _ hN).le
           rw [← he]
           dsimp only [C]
           field_simp
  rw [spectralLineJet_selberg_square_prime_row hp]
  change (p.totient:ℝ)*(2*V*P-P^2)^2 ≤ _
  calc _ ≤ (p:ℝ)*(C*A p/(p*H N))^2 := by
         apply mul_le_mul (by exact_mod_cast p.totient_le) _ (sq_nonneg _) hp'.le
         simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ht 2
       _ = _ := by
         have he : (A p)^2=H p := Real.sq_sqrt (hHp _ hp.pos).le
         change _ = C^2*(H p/p)/(H N)^2
         rw [div_pow,mul_pow,mul_pow,he]
         field_simp

/-- The entire prime-modulus portion of Selberg’s actual totient energy is
of reciprocal logarithmic size. This holds simultaneously for all primes,
including those comparable to, or larger than, the mollifier length. -/
theorem spectralLineJet_selbergSieveEnergy_prime_rows :
    ∃ C > (0:ℝ), ∀ N : ℕ, 0<N →
      (∑ p ∈ Finset.Icc 1 (N*N) with p.Prime, (p.totient:ℝ) *
        (∑ d ∈ Finset.Icc 1 (N*N) with p ∣ d, spectralLineJet_selbergSquareWeight N d/d)^2) ≤
        C/(1+Real.log N) := by
  classical
  obtain ⟨C,hC,hrow⟩ := spectralLineJet_selberg_prime_row_pointwise
  refine ⟨3*C,by positivity,?_⟩
  intro N hN
  let P := (Finset.Icc 1 N).filter Nat.Prime
  let t (k : ℕ) := ∑ d ∈ Finset.Icc 1 (N*N) with k ∣ d, spectralLineJet_selbergSquareWeight N d/d
  let F (p : ℕ) := (p.totient:ℝ)*(t p)^2
  let H := 1+Real.log N
  have hH : 0<H := by dsimp [H]; linarith [Real.log_nonneg (by exact_mod_cast hN : (1:ℝ)≤N)]
  have hsub : P ⊆ (Finset.Icc 1 (N*N)).filter Nat.Prime := by
    intro p hp
    obtain ⟨hd,hp⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.Icc_subset_Icc_right (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left N hN) hd,hp⟩
  rw [← Finset.sum_subset (f := F) hsub]
  · calc _ ≤ ∑ p ∈ P, (C/H^2)*((1+Real.log p)/p) := by
           refine Finset.sum_le_sum fun p hp ↦ ?_
           exact (hrow (Finset.mem_filter.mp hp).2 hN).trans_eq (by dsimp [H]; ring)
         _ = (C/H^2)*(∑ p ∈ P,(1+Real.log p)/p) := (Finset.mul_sum ..).symm
         _ ≤ (C/H^2)*(3*H) := mul_le_mul_of_nonneg_left (spectralLineJet_selberg_prime_log_mass hN) (by positivity)
         _ = _ := by change _ = 3*C/H; field_simp
  · intro p hp hnot
    have hprime := (Finset.mem_filter.mp hp).2
    have hgt : N<p := by
      by_contra! hh
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hprime.pos,hh⟩,hprime⟩)
    have hempty : (Finset.Icc 1 N).filter (p ∣ ·) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro d hd
      obtain ⟨hdD,hdv⟩ := Finset.mem_filter.mp hd
      exact hgt.not_ge ((Nat.le_of_dvd (Finset.mem_Icc.mp hdD).1 hdv).trans (Finset.mem_Icc.mp hdD).2)
    have ht : t p=0 := by dsimp [t]; rw [spectralLineJet_selberg_square_prime_row hprime]; simp [hempty]
    simp [F,ht]

/-- Uniform contribution of all rows except the composite moduli below the
top multiplicative shell. The remaining sum uses the actual sharp mollifier
and retains the sign of every coefficient inside each divisor row. -/
theorem spectralLineJet_selbergSieveEnergy_composite_remainder :
    ∃ C > (0:ℝ), ∀ N U : ℕ, 0<N →
      let D := Finset.Icc 1 (N*N)
      let r (k : ℕ) := (k.totient:ℝ) *
        (∑ d ∈ D with k ∣ d, spectralLineJet_selbergSquareWeight N d/d)^2
      let R := D.filter (fun k ↦ 1<k ∧ ¬k.Prime ∧ U*k<N*N)
      0 ≤ spectralLineJet_selbergSieveEnergy N-∑ k ∈ R,r k ∧
      spectralLineJet_selbergSieveEnergy N-∑ k ∈ R,r k ≤
        C*(1+U*(harmonic U:ℝ))/(1+Real.log N) := by
  classical
  obtain ⟨A,hA,hfirst⟩ := spectralLineJet_selbergSieveEnergy_first_row
  obtain ⟨B,hB,hprime⟩ := spectralLineJet_selbergSieveEnergy_prime_rows
  obtain ⟨E,hE,hupper⟩ := spectralLineJet_selbergSieveEnergy_upper_rows
  refine ⟨A+B+E,by positivity,?_⟩
  intro N U hN D r R
  let H := 1+Real.log N
  let W := (U:ℝ)*(harmonic U:ℝ)
  have hH : 1≤H := by dsimp [H]; linarith [Real.log_nonneg (by exact_mod_cast hN : (1:ℝ)≤N)]
  have hH0 : 0<H := zero_lt_one.trans_le hH
  have hW : 0≤W := by dsimp [W]; apply mul_nonneg (Nat.cast_nonneg _); simp [harmonic_eq_sum_Icc]; exact Finset.sum_nonneg fun _ _ ↦ by positivity
  have hr (k : ℕ) : 0≤r k := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have htotal : spectralLineJet_selbergSieveEnergy N=∑ k ∈ D,r k := spectralLineJet_selbergSieveEnergy_totient N
  have h1 : (∑ k ∈ D with k=1,r k) ≤ A/H := by
    have hrow : r 1 ≤ A/H^2 := by simpa [r,D,H] using hfirst N hN
    have hs : (∑ k ∈ D with k=1,r k) ≤ r 1 := by simp [Finset.sum_filter]; split <;> simp [hr]
    exact hs.trans (hrow.trans (div_le_div_of_nonneg_left hA.le hH0 (by nlinarith only [hH,sq_nonneg (H-1)])))
  have h2 : (∑ k ∈ D with k.Prime,r k) ≤ B/H := hprime N hN
  have h3 : (∑ k ∈ D with N*N≤U*k,r k) ≤ E*W/H := by
    apply (hupper N U hN).trans_eq; dsimp [W,H]; ring
  have hpartition := Finset.sum_filter_add_sum_filter_not D (fun k ↦ 1<k ∧ ¬k.Prime ∧ U*k<N*N) r
  rw [htotal]
  constructor
  · exact sub_nonneg.mpr (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ ↦ hr i)
  · have hrem : (∑ k ∈ D with ¬(1<k ∧ ¬k.Prime ∧ U*k<N*N),r k) ≤
        (∑ k ∈ D with k=1,r k)+(∑ k ∈ D with k.Prime,r k)+(∑ k ∈ D with N*N≤U*k,r k) := by
      simp only [Finset.sum_filter,← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun k hk ↦ ?_
      have hk0 : 0<k := (Finset.mem_Icc.mp hk).1
      have hcover : ¬(1<k ∧ ¬k.Prime ∧ U*k<N*N) → k=1 ∨ k.Prime ∨ N*N≤U*k := by
        intro h
        by_contra! e
        exact h ⟨by omega,e.2.1,e.2.2⟩
      split_ifs <;> first | linarith only [hr k] | simp_all
    have hsum : (∑ k ∈ D,r k)-(∑ k ∈ R,r k) ≤ A/H+B/H+E*W/H := by
      change (∑ k ∈ D.filter _,r k)+(∑ k ∈ D.filter _,r k)=∑ k ∈ D,r k at hpartition
      dsimp [R]; linarith only [hpartition,hrem,h1,h2,h3]
    apply hsum.trans
    change _ ≤ (A+B+E)*(1+W)/H
    rw [← add_div,← add_div]
    apply div_le_div_of_nonneg_right _ hH0.le
    nlinarith only [hE,mul_nonneg hA.le hW,mul_nonneg hB.le hW]

private theorem spectralLineJet_selberg_product_dvd {i j k : ℕ} (hk : 0 < k) :
    k ∣ i*j ↔ k/(i.gcd k) ∣ j := by
  let g := i.gcd k
  have hg : 0 < g := Nat.gcd_pos_of_pos_right i hk
  have hi : g*(i/g)=i := Nat.mul_div_cancel' (Nat.gcd_dvd_left i k)
  have he : g*(k/g)=k := Nat.mul_div_cancel' (Nat.gcd_dvd_right i k)
  have hc : (k/g).Coprime (i/g) := (Nat.coprime_div_gcd_div_gcd hg).symm
  change k ∣ i*j ↔ k/g ∣ j
  calc _ ↔ g*(k/g) ∣ g*((i/g)*j) := by rw [← Nat.mul_assoc,hi,he]
       _ ↔ k/g ∣ (i/g)*j := Nat.mul_dvd_mul_iff_left hg
       _ ↔ _ := ⟨hc.dvd_of_dvd_mul_left, fun h ↦ dvd_mul_of_dvd_right h _⟩

private theorem spectralLineJet_selberg_gcd_rows (N : ℕ) {k : ℕ} (hk : 0 < k) :
    let D := Finset.Icc 1 N
    let u (i : ℕ) := spectralLineJet_selbergHalfMoebius i/i
    (∑ m ∈ Finset.Icc 1 (N*N) with k ∣ m, spectralLineJet_selbergSquareWeight N m/m) =
      ∑ d ∈ k.divisors, (∑ i ∈ D with i.gcd k=d, u i)*(∑ j ∈ D with k/d ∣ j, u j) := by
  classical
  intro D u
  let M := Finset.Icc 1 (N*N)
  let S := D ×ˢ D
  let idx (z : ℕ×ℕ) := z.1*z.2
  let f (z : ℕ×ℕ) := if k ∣ idx z then u z.1*u z.2 else 0
  have hmap (z : ℕ×ℕ) (hz : z∈S) : idx z∈M := by
    obtain ⟨h1,h2⟩ := Finset.mem_product.mp hz
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (Finset.mem_Icc.mp h1).1 (Finset.mem_Icc.mp h2).1,
      Nat.mul_le_mul (Finset.mem_Icc.mp h1).2 (Finset.mem_Icc.mp h2).2⟩
  let v (i : ℕ) := u i*(∑ j ∈ D with k/(i.gcd k) ∣ j, u j)
  have hg (i : ℕ) (_ : i∈D) : i.gcd k ∈ k.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right i k,hk.ne'⟩
  calc _ = ∑ m ∈ M, ∑ z ∈ S with idx z=m, f z := by
         rw [Finset.sum_filter]
         refine Finset.sum_congr rfl fun m hm ↦ ?_
         by_cases hkm : k ∣ m
         · simp only [ite_eq_left hkm]
           rw [spectralLineJet_selberg_square_fiber N (Finset.mem_Icc.mp hm).1,Finset.sum_div]
           refine Finset.sum_congr rfl fun z hz ↦ ?_
           have he : idx z=m := (Finset.mem_filter.mp hz).2
           obtain ⟨h1,h2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hz).1
           have hz : k ∣ idx z := he ▸ hkm
           simp only [f,ite_eq_left hz,u]
           change (if z.1 ∈ D then _ else 0)*(if z.2 ∈ D then _ else 0)/_ = _
           rw [ite_eq_left h1,ite_eq_left h2,← he]
           simp [idx,div_mul_div_comm]
         · rw [ite_eq_right hkm,Finset.sum_eq_zero]
           intro z hz
           simp [f,(Finset.mem_filter.mp hz).2,hkm]
       _ = ∑ z ∈ S, f z := Finset.sum_fiberwise_of_maps_to hmap f
       _ = ∑ i ∈ D, v i := by
         rw [Finset.sum_product]
         refine Finset.sum_congr rfl fun i _ ↦ ?_
         simp only [v,Finset.sum_filter,Finset.mul_sum,f,idx,spectralLineJet_selberg_product_dvd hk]
         exact Finset.sum_congr rfl fun j _ ↦ by split <;> simp
       _ = _ := by
         rw [← Finset.sum_fiberwise_of_maps_to hg v]
         refine Finset.sum_congr rfl fun d _ ↦ ?_
         rw [Finset.sum_mul]
         exact Finset.sum_congr rfl fun i hi ↦ by simp [v,(Finset.mem_filter.mp hi).2]

private theorem spectralLineJet_selberg_scale_multiples (N : ℕ) {d : ℕ} (hd : 0<d)
    (f : ℕ → ℝ) :
    (d:ℝ)*(∑ i ∈ Finset.Icc 1 N with d ∣ i, f i/i) =
      ∑ m ∈ Finset.Icc 1 (N/d), f (d*m)/m := by
  classical
  let S := Finset.Icc 1 (N/d)
  have he : (Finset.Icc 1 N).filter (d ∣ ·) = S.image (d*·) := by
    ext i
    constructor
    · intro hi
      obtain ⟨hiD,hdi⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_image.mpr ⟨i/d,Finset.mem_Icc.mpr ⟨Nat.div_pos
        (Nat.le_of_dvd (Finset.mem_Icc.mp hiD).1 hdi) hd,Nat.div_le_div_right (Finset.mem_Icc.mp hiD).2⟩,
        Nat.mul_div_cancel' hdi⟩
    · rintro hi
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hd (Finset.mem_Icc.mp hm).1,
        by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp (Finset.mem_Icc.mp hm).2⟩,dvd_mul_right _ _⟩
  rw [he,Finset.sum_image (fun _ _ _ _ h ↦ Nat.eq_of_mul_eq_mul_left hd h),Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  push_cast
  field_simp [show (d:ℝ)≠0 by exact_mod_cast hd.ne']

private theorem spectralLineJet_selberg_uncoprime_mass (Y : ℕ) {k : ℕ} (hk : 0<k) :
    (∑ m ∈ Finset.Icc 1 Y with ¬m.Coprime k, 1/(m:ℝ)) ≤
      (harmonic Y:ℝ)*∑ p ∈ k.primeFactors, 1/(p:ℝ) := by
  classical
  let D := Finset.Icc 1 Y
  calc _ ≤ ∑ m ∈ D, ∑ p ∈ k.primeFactors with p ∣ m, 1/(m:ℝ) := by
         rw [Finset.sum_filter]
         refine Finset.sum_le_sum fun m _ ↦ ?_
         split
         · rename_i h
           obtain ⟨p,hp,hpm,hpk⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
           apply Finset.single_le_sum (f := fun _ ↦ 1/(m:ℝ)) (fun _ _ ↦ by positivity)
           exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp,hpk,hk.ne'⟩,hpm⟩
         · exact Finset.sum_nonneg fun _ _ ↦ by positivity
       _ = ∑ p ∈ k.primeFactors, ∑ m ∈ D with p ∣ m, 1/(m:ℝ) := by
         simp_rw [Finset.sum_filter]
         rw [Finset.sum_comm]
       _ ≤ _ := by
         rw [Finset.mul_sum]
         refine Finset.sum_le_sum fun p hp ↦ ?_
         have h := spectralLineJet_selberg_divisor_row_bound (M := Y) (Nat.mem_primeFactors.mp hp).1.pos
           (fun _ ↦ 1) (by simp)
         have hh : (harmonic (Y/p):ℝ) ≤ (harmonic Y:ℝ) := by
           simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
           exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (Nat.div_le_self Y p))
             fun _ _ _ ↦ by positivity
         exact (show (∑ m ∈ D with p ∣ m, 1/(m:ℝ)) ≤ (harmonic (Y/p):ℝ)/p by simpa [D] using h).trans
           ((div_le_div_of_nonneg_right hh (Nat.cast_nonneg _)).trans_eq (by ring))

private theorem spectralLineJet_selberg_mask_error (Y : ℕ) {d k : ℕ} (hk : 0<k) (f : ℕ → ℝ)
    (hf : ∀ m, |f m|≤1)
    (hgood : ∀ m, m.Coprime k → f m=spectralLineJet_selbergHalfMoebius d*spectralLineJet_selbergHalfMoebius m) :
    |(∑ m ∈ Finset.Icc 1 Y, f m/m)-spectralLineJet_selbergHalfMoebius d*
      (∑ m ∈ Finset.Icc 1 Y, spectralLineJet_selbergHalfMoebius m/m)| ≤
      2*(harmonic Y:ℝ)*∑ p ∈ k.primeFactors, 1/(p:ℝ) := by
  classical
  let b := spectralLineJet_selbergHalfMoebius
  let D := Finset.Icc 1 Y
  let g (m : ℕ) := f m-b d*b m
  have he : (∑ m ∈ D, f m/m) - b d*(∑ m ∈ D, b m/m) = ∑ m ∈ D, g m/m := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ ↦ by dsimp [g]; ring
  rw [he]
  calc _ ≤ ∑ m ∈ D, |g m/m| := Finset.abs_sum_le_sum_abs _ _
       _ ≤ 2*(∑ m ∈ D with ¬m.Coprime k, 1/(m:ℝ)) := by
         rw [Finset.sum_filter,Finset.mul_sum]
         refine Finset.sum_le_sum fun m _ ↦ ?_
         by_cases h : m.Coprime k
         · simp [g,h,hgood m h,b]
         · simp only [ite_eq_left h,abs_div,Nat.abs_cast]
           have hb := spectralLineJet_selbergHalfMoebius_spec.2.1
           have hbd : |b d*b m|≤1 := by rw [abs_mul]; exact (mul_le_mul (hb d) (hb m) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
           have herr : |g m|≤2 := (abs_sub _ _).trans (by linarith only [hf m,hbd])
           exact (div_le_div_of_nonneg_right herr (Nat.cast_nonneg m)).trans_eq (by ring)
       _ ≤ _ := (mul_le_mul_of_nonneg_left (spectralLineJet_selberg_uncoprime_mass Y hk) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

/-- A divisor slice of the sharp half-Möbius weights differs from a rescaled
unrestricted sum only at integers sharing a prime with the modulus. The same
bound applies when the slice specifies the exact gcd. -/
theorem spectralLineJet_selbergHalfMoebius_divisor_slice (N : ℕ) {k d : ℕ} (hk : 0<k)
    (hd : d ∣ k) (exactGcd : Bool) :
    let b := spectralLineJet_selbergHalfMoebius
    let T := (Finset.Icc 1 N).filter (fun i ↦ d ∣ i ∧ (exactGcd=true → i.gcd k=d))
    |(d:ℝ)*(∑ i ∈ T, b i/i) - b d*(∑ m ∈ Finset.Icc 1 (N/d), b m/m)| ≤
      2*(harmonic (N/d):ℝ)*∑ p ∈ k.primeFactors, 1/(p:ℝ) := by
  classical
  intro b T
  have hd' := Nat.pos_of_dvd_of_pos hd hk
  let f (i : ℕ) := if exactGcd=true → i.gcd k=d then b i else 0
  have he : (∑ i ∈ T,b i/i) = ∑ i ∈ Finset.Icc 1 N with d ∣ i, f i/i := by
    simp only [T,Finset.sum_filter,f]
    exact Finset.sum_congr rfl fun i _ ↦ by
      cases exactGcd <;> by_cases hi : d∣i <;> by_cases hg : i.gcd k=d <;> simp [hi,hg]
  rw [he,spectralLineJet_selberg_scale_multiples N hd']
  apply spectralLineJet_selberg_mask_error _ hk
  · intro m
    dsimp [f]
    split
    · exact spectralLineJet_selbergHalfMoebius_spec.2.1 _
    · norm_num
  · intro m hm
    have hc := Nat.Coprime.coprime_dvd_right hd hm
    have hq : k/d ∣ k := Nat.div_dvd_of_dvd hd
    have hg : (d*m).gcd k=d := by
      conv_lhs => rhs; rw [←Nat.mul_div_cancel' hd]
      rw [Nat.gcd_mul_left,show m.gcd (k/d)=1 from Nat.Coprime.coprime_dvd_right hq hm,mul_one]
    simp [f,hg,b,spectralLineJet_selbergHalfMoebius_mult.map_mul_of_coprime hc.symm]

private theorem spectralLineJet_selberg_rough_divisors {k R L : ℕ} (hk : 0<k) (hR : 0<R)
    (hbound : k ≤ (R+1)^L) (hrough : ∀ d, d ≤ R → 0<d → d.Coprime k) :
    k.divisors.card ≤ 2^L ∧ (∑ p ∈ k.primeFactors, 1/(p:ℝ)) ≤ (2:ℝ)^L/(R+1) := by
  classical
  let P := k.primeFactors
  have hpR (p : ℕ) (hp : p∈P) : R+1≤p := by
    obtain ⟨hprime,hpk,_⟩ := Nat.mem_primeFactors.mp hp
    by_contra! h
    have hc := hrough p (by omega) hprime.pos
    exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,hprime,dvd_rfl,hpk⟩ hc
  let e := ∑ p ∈ P, k.factorization p
  have he : e ≤ L := by
    apply (Nat.pow_le_pow_iff_right (by omega : 1<R+1)).mp
    calc (R+1)^e = ∏ p ∈ P, (R+1)^k.factorization p := (Finset.prod_pow_eq_pow_sum _ _ _).symm
         _ ≤ ∏ p ∈ P, p^k.factorization p :=
           Finset.prod_le_prod fun p hp ↦ Nat.pow_le_pow_left (hpR p hp) _
         _ = k := (Nat.prod_primeFactors_pow_factorization hk.ne').symm
         _ ≤ _ := hbound
  have hdiv : k.divisors.card ≤ 2^L := by
    calc _ = ∏ p ∈ P, (k.factorization p+1) := Nat.card_divisors hk.ne'
         _ ≤ ∏ p ∈ P, 2^k.factorization p := Finset.prod_le_prod fun p _ ↦ (k.factorization p).lt_two_pow_self
         _ = 2^e := Finset.prod_pow_eq_pow_sum _ _ _
         _ ≤ _ := Nat.pow_le_pow_right (by decide) he
  refine ⟨hdiv,?_⟩
  have hcard : P.card ≤ 2^L := (Finset.card_le_card (show P ⊆ k.divisors from fun p hp ↦
    Nat.mem_divisors.mpr ⟨(Nat.mem_primeFactors.mp hp).2.1,hk.ne'⟩)).trans hdiv
  calc _ ≤ ∑ _p ∈ P, 1/((R:ℝ)+1) := Finset.sum_le_sum fun p hp ↦
         one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hpR p hp)
       _ = (P.card:ℝ)/((R:ℝ)+1) := by simp [div_eq_mul_inv]
       _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

private theorem spectralLineJet_selberg_slice_scale {N R A : ℕ} (hN : 0<N)
    (hNR : N≤(R+1)^A) :
    (1+Real.log N)^2 ≤ (1+2*(A:ℝ))^2*((R:ℝ)+1) := by
  let x : ℝ := ↑(R+1)
  have hx : 1≤x := by dsimp [x]; exact_mod_cast Nat.le_add_left 1 R
  have hxp := zero_lt_one.trans_le hx
  have hs : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx
  have hn : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hl : Real.log N ≤ (A:ℝ)*Real.log x := by
    have h := Real.log_le_log (by exact_mod_cast hN) (by dsimp [x]; exact_mod_cast hNR : (N:ℝ)≤x^A)
    rwa [Real.log_pow] at h
  have hv := Real.log_le_rpow_div hxp.le (by norm_num : (0:ℝ)<1/2)
  rw [←Real.sqrt_eq_rpow] at hv
  have hlog : Real.log x ≤ 2*Real.sqrt x := by linarith
  have hle : 1+Real.log N ≤ (1+2*(A:ℝ))*Real.sqrt x := by
    linarith only [hs,hl,mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α := ℝ) A)]
  have h₂ := pow_le_pow_left₀ (by linarith only [hn]) hle 2
  rw [mul_pow,Real.sq_sqrt hxp.le] at h₂
  simpa [x] using h₂

private theorem spectralLineJet_selberg_slice_error_uniform (A : ℕ) :
    ∃ C > (0:ℝ), ∀ {N R k Y : ℕ}, 0<N → 0<R → N≤(R+1)^A → 0<k → k≤N*N →
      (∀ d, d≤R → 0<d → d.Coprime k) → Y≤N →
      (2*(harmonic Y:ℝ)*∑ p ∈ k.primeFactors, 1/(p:ℝ))*Real.sqrt (1+Real.log N) ≤ C := by
  let L := 2*A
  let e := (2:ℝ)^L
  let c := (1+2*(A:ℝ))^2
  refine ⟨2*c*e,by dsimp [c,e]; positivity,?_⟩
  intro N R k Y hN hR hNR hk hkN hr hY
  have hbd : k≤(R+1)^L := by
    apply hkN.trans
    simpa [L,Nat.mul_comm 2 A,pow_mul,pow_two] using Nat.mul_le_mul hNR hNR
  have hmass := (spectralLineJet_selberg_rough_divisors hk hR hbd hr).2
  let H := 1+Real.log N
  have h1 : 1≤H := by dsimp [H]; linarith [Real.log_nonneg (by exact_mod_cast hN : (1:ℝ)≤N)]
  have hH : 0≤H := by linarith
  have hQ : Real.sqrt H ≤ H := Real.sqrt_le_iff.mpr ⟨hH,by nlinarith only [mul_nonneg hH (sub_nonneg.mpr h1)]⟩
  have hh : (harmonic Y:ℝ)≤H := by
    apply le_trans _ (harmonic_le_one_add_log N)
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hY) fun _ _ _ ↦ by positivity
  have hlog : H^2≤c*((R:ℝ)+1) := spectralLineJet_selberg_slice_scale hN hNR
  have hE : 0≤e/((R:ℝ)+1) := by dsimp [e]; positivity
  calc _ ≤ (2*H*(e/((R:ℝ)+1)))*H := by
         apply mul_le_mul _ hQ (Real.sqrt_nonneg _) (by positivity)
         exact mul_le_mul (mul_le_mul_of_nonneg_left hh (by norm_num)) hmass
           (Finset.sum_nonneg fun _ _ ↦ by positivity) (by positivity)
       _ = (2*e)*H^2/((R:ℝ)+1) := by ring
       _ ≤ _ := by
         apply (div_le_iff₀ (by positivity : (0:ℝ)<R+1)).mpr
         calc _ ≤ (2*e)*(c*((R:ℝ)+1)) := mul_le_mul_of_nonneg_left hlog (by dsimp [e]; positivity)
              _ = _ := by ring

private theorem spectralLineJet_selberg_rough_mass_polynomial {X R A : ℕ} (hR : 0<R)
    (hXR : X≤(R+1)^A) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 X)
    (hr : ∀ k ∈ S, ∀ j, j≤R → 0<j → j.Coprime k) :
    (∑ k ∈ S, (k:ℝ)⁻¹) ≤ (A:ℝ)+3 := by
  apply (spectralLineJet_selberg_rough_mass hR S hS hr).trans
  let x : ℝ := ↑(R+1)
  have hx : 2≤x := by dsimp [x]; exact_mod_cast (by omega : 2≤R+1)
  have hxp : 0<x := by linarith
  have hlog : (1/2:ℝ)≤Real.log x := by
    have hinv := inv_anti₀ (by norm_num : (0:ℝ)<2) hx
    linarith [Real.one_sub_inv_le_log_of_pos hxp]
  change (1+Real.log (R*X:ℕ))/Real.log x ≤ _
  apply (div_le_iff₀ (by linarith only [hlog] : 0<Real.log x)).mpr
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp only [mul_zero,Nat.cast_zero,Real.log_zero,add_zero]
    nlinarith only [hlog,mul_nonneg (Nat.cast_nonneg (α := ℝ) A) (show 0≤Real.log x by linarith)]
  have hmax : R*X ≤ (R+1)^(A+1) := by rw [pow_succ,Nat.mul_comm]; exact Nat.mul_le_mul hXR (by omega)
  have hl := Real.log_le_log (by exact_mod_cast Nat.mul_pos hR hX) (Nat.cast_le (α := ℝ).mpr hmax)
  simp only [Nat.cast_pow,Real.log_pow,Nat.cast_add,Nat.cast_one] at hl
  dsimp [x] at *
  push_cast at *
  linarith only [hlog,hl]

private theorem spectralLineJet_selberg_rough_count (A : ℕ) :
    ∃ C > (0:ℝ), ∀ {X R : ℕ}, 0<R → X≤(R+1)^A → ∀ S : Finset ℕ,
      S ⊆ Finset.Icc 2 X → (∀ k ∈ S, ∀ j, j≤R → 0<j → j.Coprime k) →
      (S.card:ℝ)*Real.log (R+1:ℕ) ≤ C*X := by
  classical
  let K := Real.log 4+4
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨K*((A:ℝ)+3),by positivity,?_⟩
  intro X R hR hXR S hS hr
  let f (n : ℕ) := n/n.minFac
  let M := S.image f
  have hp (n : ℕ) (hn : n∈S) : n.minFac.Prime := Nat.minFac_prime (by have := (Finset.mem_Icc.mp (hS hn)).1; omega)
  have hn' (n : ℕ) (hn : n∈S) : 0<n := by have := (Finset.mem_Icc.mp (hS hn)).1; omega
  have hmul (n : ℕ) : f n*n.minFac=n := Nat.div_mul_cancel (Nat.minFac_dvd n)
  have hm (n : ℕ) (hn : n∈S) : 0<f n := Nat.div_pos (Nat.minFac_le (hn' n hn)) (hp n hn).pos
  have hpos (m : ℕ) (hm' : m∈M) : 0<m := by obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm'; exact hm n hn
  have hmS : M ⊆ Finset.Icc 1 X := by
    rintro m hm'
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm'
    exact Finset.mem_Icc.mpr ⟨hm n hn,(Nat.div_le_self ..).trans (Finset.mem_Icc.mp (hS hn)).2⟩
  have hrough (m : ℕ) (hm' : m∈M) (j : ℕ) (hj : j≤R) (hj' : 0<j) : j.Coprime m := by
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm'
    exact Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd (Nat.minFac_dvd _)) (hr n hn j hj hj')
  let Λ := ArithmeticFunction.vonMangoldt
  have hl (n : ℕ) (hn : n∈S) : Real.log (R+1:ℕ)≤Λ n.minFac := by
    have hR' : R+1≤n.minFac := by
      by_contra! hh
      exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨_,hp n hn,dvd_rfl,Nat.minFac_dvd _⟩ (hr n hn _ (by omega) (hp n hn).pos)
    rw [show Λ n.minFac=Real.log n.minFac from ArithmeticFunction.vonMangoldt_apply_prime (hp n hn)]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hR')
  have hbound (m : ℕ) (hm' : m∈M) :
      (∑ n ∈ S with f n=m, Λ n.minFac) ≤ K*((X:ℝ)/m) := by
    let U := S.filter (fun n ↦ f n=m)
    have hkey (n : ℕ) (hn : n∈U) : m*n.minFac=n := (Finset.mem_filter.mp hn).2 ▸ hmul n
    have hinj : Set.InjOn Nat.minFac (↑U : Set ℕ) := by
      intro n hn j hj he; exact (hkey n hn).symm.trans ((congrArg (m*·) he).trans (hkey j hj))
    have hsub : U.image Nat.minFac ⊆ Finset.Icc 1 (X/m) := by
      rintro p hp'
      obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hp'
      exact Finset.mem_Icc.mpr ⟨(hp n (Finset.mem_filter.mp hn).1).pos,
        (Nat.le_div_iff_mul_le (hpos m hm')).mpr (by rw [Nat.mul_comm,hkey n hn]; exact (Finset.mem_Icc.mp (hS (Finset.mem_filter.mp hn).1)).2)⟩
    calc _ = ∑ p ∈ U.image Nat.minFac, Λ p := (Finset.sum_image (f := Λ) hinj).symm
         _ ≤ ∑ p ∈ Finset.Icc 1 (X/m), Λ p :=
           Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg
         _ ≤ K*(X/m:ℕ) := by
           have h := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α := ℝ) (X/m))
           simp only [Chebyshev.psi,Nat.floor_natCast,←Finset.Icc_succ_left_eq_Ioc] at h
           exact h
         _ ≤ _ := mul_le_mul_of_nonneg_left Nat.cast_div_le hK.le
  calc _ = ∑ _n ∈ S, Real.log (R+1:ℕ) := by simp
       _ ≤ ∑ n ∈ S, Λ n.minFac := Finset.sum_le_sum hl
       _ = ∑ m ∈ M, ∑ n ∈ S with f n=m, Λ n.minFac :=
         (Finset.sum_fiberwise_of_maps_to (fun n hn ↦ Finset.mem_image_of_mem f hn) _).symm
       _ ≤ ∑ m ∈ M, K*((X:ℝ)/m) := Finset.sum_le_sum hbound
       _ = (K*X)*(∑ m ∈ M,(m:ℝ)⁻¹) := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
       _ ≤ _ := (mul_le_mul_of_nonneg_left (spectralLineJet_selberg_rough_mass_polynomial hR hXR M hmS hrough)
         (by positivity : 0≤K*X)).trans_eq (by ring)

private theorem spectralLineJet_selberg_sqrt_log_harmonic (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, 1/((m:ℝ)*Real.sqrt (1+Real.log m))) ≤
      2*Real.sqrt (1+Real.log N) := by
  let H (n : ℕ) := (harmonic n:ℝ)
  have hh (n : ℕ) : 0≤H n := by
    simp [H,harmonic_eq_sum_Icc]
    exact Finset.sum_nonneg fun _ _ ↦ by positivity
  have hb (n : ℕ) : (∑ m ∈ Finset.Icc 1 n, 1/((m:ℝ)*Real.sqrt (1+Real.log m))) ≤ 2*Real.sqrt (H n) := by
    induction n with
    | zero => simp [H]
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1≤n+1)]
      let a : ℝ := ↑(n+1:ℕ)
      have ha : 0<a := by dsimp [a]; positivity
      have he : H (n+1)=H n+1/a := by simp [H,harmonic_succ,a,one_div]
      have hp : 0<H (n+1) := he ▸ add_pos_of_nonneg_of_pos (hh n) (by positivity)
      have hs := Real.sq_sqrt (hh n)
      have hs' := Real.sq_sqrt hp.le
      have hroot := Real.sqrt_pos.mpr hp
      have hscale := Real.sqrt_le_sqrt (harmonic_le_one_add_log (n+1))
      have herr : 1/(a*Real.sqrt (1+Real.log (n+1:ℕ))) ≤ 1/(a*Real.sqrt (H (n+1))) :=
        one_div_le_one_div_of_le (mul_pos ha hroot) (mul_le_mul_of_nonneg_left hscale ha.le)
      have he' : 1/(a*Real.sqrt (H (n+1))) ≤ 2*(Real.sqrt (H (n+1))-Real.sqrt (H n)) := by
        rw [←div_div,div_le_iff₀ hroot]
        nlinarith only [hs,hs',he,sq_nonneg (Real.sqrt (H (n+1))-Real.sqrt (H n))]
      change _ + 1/(a*Real.sqrt (1+Real.log (n+1:ℕ))) ≤ _
      linarith only [ih,herr,he']
  exact (hb N).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (harmonic_le_one_add_log N)) (by norm_num))

private theorem spectralLineJet_selberg_rough_weighted_mass (A : ℕ) :
    ∃ C > (0:ℝ), ∀ {N R : ℕ}, 0<N → 0<R → N≤(R+1)^A → ∀ S : Finset ℕ,
      S ⊆ Finset.Icc 1 N → (∀ d ∈ S, ∀ j, j≤R → 0<j → j.Coprime d) →
      (∑ d ∈ S, 1/((d:ℝ)*Real.sqrt (1+Real.log (N/d:ℕ))))*Real.sqrt (1+Real.log N) ≤ C := by
  classical
  obtain ⟨K,hK,hcount⟩ := spectralLineJet_selberg_rough_count A
  refine ⟨1+4*K*((A:ℝ)+2),by positivity,?_⟩
  intro N R hN hR hNR S hS hr
  let H (n : ℕ) := Real.sqrt (1+Real.log n)
  let w (d : ℕ) := 1/((d:ℝ)*H (N/d))
  let L := Real.log (R+1:ℕ)
  let U := S.erase 1
  let D := Finset.Icc 1 N
  have hn : 0<(N:ℝ) := by exact_mod_cast hN
  have hH (m : ℕ) (hm : 0<m) : 0<H m := Real.sqrt_pos.mpr (by linarith [Real.log_nonneg (by exact_mod_cast hm : (1:ℝ)≤m)])
  have hsL : (1/2:ℝ)≤L := by
    have hx : (2:ℝ)≤(R+1:ℕ) := by exact_mod_cast (by omega : 2≤R+1)
    have hinv := inv_anti₀ (by norm_num : (0:ℝ)<2) hx
    dsimp [L]; linarith [Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<(R+1:ℕ) by positivity)]
  have hL : 0<L := by linarith
  have hscale : (H N)^2≤((A:ℝ)+2)*L := by
    rw [show (H N)^2=1+Real.log N from Real.sq_sqrt (by linarith [Real.log_nonneg (by exact_mod_cast hN : (1:ℝ)≤N)])]
    have hl := Real.log_le_log hn (Nat.cast_le (α := ℝ).mpr hNR)
    simp only [Nat.cast_pow,Real.log_pow] at hl
    change Real.log N ≤ (A:ℝ)*L at hl
    linarith only [hl,hsL]
  have hU : U ⊆ Finset.Icc 2 N := by
    intro d hd
    obtain ⟨hne,hS'⟩ := Finset.mem_erase.mp hd
    obtain ⟨hd1,hdN⟩ := Finset.mem_Icc.mp (hS hS')
    exact Finset.mem_Icc.mpr ⟨by omega,hdN⟩
  have hrow (d : ℕ) (hd : d∈U) :
      (N:ℝ)*w d ≤ 2*∑ m ∈ D with m*d≤N, 1/H m := by
    obtain ⟨hd2,hdN⟩ := Finset.mem_Icc.mp (hU hd)
    have hd0 : 0<d := by omega
    have hd' : 0<(d:ℝ) := by exact_mod_cast hd0
    let y := N/d
    have hy : 0<y := Nat.div_pos hdN hd0
    have hcut : D.filter (fun m ↦ m*d≤N)=Finset.Icc 1 y := by
      ext m
      simp only [D,Finset.mem_filter,Finset.mem_Icc]
      exact ⟨fun h ↦ ⟨h.1.1,(Nat.le_div_iff_mul_le hd0).mpr h.2⟩,fun h ↦
        ⟨⟨h.1,h.2.trans (Nat.div_le_self ..)⟩,(Nat.le_div_iff_mul_le hd0).mp h.2⟩⟩
    have hsize : N≤2*y*d := by
      have he := Nat.div_add_mod N d
      change d*y+N%d=N at he
      nlinarith only [he,Nat.mod_lt N hd0,Nat.mul_le_mul_left d hy]
    have hc : (N:ℝ)/d≤2*y := (div_le_iff₀ hd').mpr (by exact_mod_cast hsize)
    rw [hcut]
    calc (N:ℝ)*w d = ((N:ℝ)/d)*(1/H y) := by dsimp [w,y]; ring
         _ ≤ (2*y)*(1/H y) := mul_le_mul_of_nonneg_right hc (by positivity [hH y hy])
         _ = 2*∑ _m ∈ Finset.Icc 1 y, 1/H y := by simp [mul_assoc]
         _ ≤ _ := by
           apply mul_le_mul_of_nonneg_left _ (by norm_num)
           refine Finset.sum_le_sum fun m hm ↦ one_div_le_one_div_of_le (hH m (Finset.mem_Icc.mp hm).1) ?_
           apply Real.sqrt_le_sqrt
           exact add_le_add (le_refl 1) (Real.log_le_log (by exact_mod_cast (Finset.mem_Icc.mp hm).1 : 0<(m:ℝ)) (by exact_mod_cast (Finset.mem_Icc.mp hm).2 : (m:ℝ)≤y))
  have hcount' (m : ℕ) (hm : m∈D) :
      (((U.filter (fun d ↦ m*d≤N)).card:ℝ)*L)*(1/H m) ≤ K*N*(1/((m:ℝ)*H m)) := by
    let W := U.filter (fun d ↦ m*d≤N)
    have hm0 : 0<m := (Finset.mem_Icc.mp hm).1
    have hW : W ⊆ Finset.Icc 2 (N/m) := by
      intro d hd
      obtain ⟨hu,hmul⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hU hu)).1,(Nat.le_div_iff_mul_le hm0).mpr (by simpa [Nat.mul_comm] using hmul)⟩
    have hbd := hcount hR ((Nat.div_le_self N m).trans hNR) W hW
      (fun d hd ↦ hr d (Finset.mem_of_mem_erase (Finset.mem_filter.mp hd).1))
    calc _ ≤ (K*(N/m:ℕ))*(1/H m) := mul_le_mul_of_nonneg_right hbd (by positivity [hH m hm0])
         _ ≤ (K*((N:ℝ)/m))*(1/H m) := by gcongr; exact Nat.cast_div_le
         _ = _ := by ring
  have hall : ((N:ℝ)*∑ d ∈ U,w d)*L ≤ (2*K*N)*(2*H N) := by
    calc _ ≤ (2*∑ d ∈ U, ∑ m ∈ D with m*d≤N, 1/H m)*L := by
           apply mul_le_mul_of_nonneg_right _ hL.le
           rw [Finset.mul_sum,Finset.mul_sum]
           exact Finset.sum_le_sum hrow
         _ = 2*∑ m ∈ D, (((U.filter (fun d ↦ m*d≤N)).card:ℝ)*L)*(1/H m) := by
           simp_rw [Finset.sum_filter]
           rw [Finset.sum_comm]
           rw [mul_assoc,Finset.sum_mul]
           congr 1
           refine Finset.sum_congr rfl fun m _ ↦ ?_
           rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]; ring
         _ ≤ 2*∑ m ∈ D, K*N*(1/((m:ℝ)*H m)) := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcount') (by norm_num)
         _ ≤ _ := by
           rw [←Finset.mul_sum]
           exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (spectralLineJet_selberg_sqrt_log_harmonic N)
             (by positivity : 0≤K*N)) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)
  have hsum : (∑ d ∈ U,w d)*L ≤ 4*K*H N := by
    apply (mul_le_mul_iff_right₀ hn).mp
    linarith only [hall]
  have hfinal : (∑ d ∈ U,w d)*H N ≤ 4*K*((A:ℝ)+2) := by
    apply (mul_le_mul_iff_left₀ hL).mp
    calc _ = ((∑ d ∈ U,w d)*L)*H N := by ring
         _ ≤ (4*K*H N)*H N := mul_le_mul_of_nonneg_right hsum (hH N hN).le
         _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hscale (by positivity : (0:ℝ)≤4*K)]
  have hsub : S ⊆ insert 1 U := by intro d hd; by_cases h : d=1 <;> simp [U,h,hd]
  have he : (∑ d ∈ S,w d) ≤ w 1 + ∑ d ∈ U,w d := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (f := w) (fun d _ _ ↦ by dsimp [w,H]; positivity)).trans_eq
    rw [Finset.sum_insert (by simp [U])]
  change (∑ d ∈ S,w d)*H N ≤ _
  calc _ ≤ (w 1+∑ d ∈ U,w d)*H N := mul_le_mul_of_nonneg_right he (hH N hN).le
       _ = 1+(∑ d ∈ U,w d)*H N := by rw [add_mul]; simp [w,(hH N hN).ne']
       _ ≤ _ := add_le_add le_rfl hfinal

private def spectralLineJet_selbergSliceMajorant (N d : ℕ) : ℝ :=
  if d ∈ Finset.Icc 1 N then 1/((d:ℝ)*Real.sqrt (1+Real.log (N/d:ℕ))) else 0

private theorem spectralLineJet_selberg_slice_majorant_spec (N d : ℕ) :
    0≤spectralLineJet_selbergSliceMajorant N d ∧ (d:ℝ)*spectralLineJet_selbergSliceMajorant N d≤1 := by
  unfold spectralLineJet_selbergSliceMajorant
  split
  · rename_i h
    obtain ⟨hd,hdN⟩ := Finset.mem_Icc.mp h
    have hp : 0<(d:ℝ) := by exact_mod_cast hd
    have hy := Nat.div_pos hdN hd
    have hs : 1≤Real.sqrt (1+Real.log (N/d:ℕ)) := Real.le_sqrt_of_sq_le (by
      linarith [Real.log_nonneg (by exact_mod_cast hy : (1:ℝ)≤(N/d:ℕ))])
    refine ⟨by positivity,?_⟩
    rw [one_div,mul_inv,←mul_assoc,mul_inv_cancel₀ hp.ne',one_mul]
    exact (inv_le_one₀ (by linarith)).mpr hs
  · simp

private theorem spectralLineJet_selberg_slice_majorant (A : ℕ) :
    ∃ C > (0:ℝ), ∀ {N R k d : ℕ}, 0<N → 0<R → N≤(R+1)^A → 0<k → k≤N*N →
      (∀ j, j≤R → 0<j → j.Coprime k) → d∣k → ∀ e : Bool,
        let T := (Finset.Icc 1 N).filter (fun i ↦ d ∣ i ∧ (e=true → i.gcd k=d))
        |∑ i ∈ T,spectralLineJet_selbergHalfMoebius i/i| ≤ C*spectralLineJet_selbergSliceMajorant N d := by
  classical
  obtain ⟨E,hE,herr⟩ := spectralLineJet_selberg_slice_error_uniform A
  obtain ⟨K,hK,hV⟩ := spectralLineJet_selbergHalfMoebius_reciprocal_sum
  refine ⟨K+E,by positivity,?_⟩
  intro N R k d hN hR hNR hk hkN hr hd e T
  let b := spectralLineJet_selbergHalfMoebius
  let s := ∑ i ∈ T,b i/i
  let H (n : ℕ) := Real.sqrt (1+Real.log n)
  have hd' := Nat.pos_of_dvd_of_pos hd hk
  have hd0 : 0<(d:ℝ) := by exact_mod_cast hd'
  by_cases hdN : d≤N
  · let y := N/d
    let V := ∑ m ∈ Finset.Icc 1 y,b m/m
    let err := 2*(harmonic y:ℝ)*∑ p ∈ k.primeFactors, 1/(p:ℝ)
    have hy : 0<y := Nat.div_pos hdN hd'
    have hy' : 0<(y:ℝ) := by exact_mod_cast hy
    have hY : 0<H y := Real.sqrt_pos.mpr (by linarith [Real.log_nonneg (by exact_mod_cast hy : (1:ℝ)≤y)])
    have hYN : H y≤H N := Real.sqrt_le_sqrt (add_le_add le_rfl (Real.log_le_log hy' (by exact_mod_cast Nat.div_le_self N d)))
    have he0 : 0≤err := by
      have hh : (0:ℝ)≤(harmonic y:ℝ) := by simp [harmonic_eq_sum_Icc]; exact Finset.sum_nonneg fun _ _ ↦ by positivity
      dsimp [err]; positivity
    have he : err*H y≤E := (mul_le_mul_of_nonneg_left hYN he0).trans (herr hN hR hNR hk hkN hr (Nat.div_le_self N d))
    have hv : |V| * H y≤K := (le_div_iff₀ hY).mp (hV y hy)
    have hbase : |(d:ℝ)*s-b d*V|≤err := spectralLineJet_selbergHalfMoebius_divisor_slice N hk hd e
    have hb : |b d*V|≤|V| := by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (spectralLineJet_selbergHalfMoebius_spec.2.1 _)
    have hs : |(d:ℝ)*s|≤err+|V| :=
      (by simpa only [sub_add_cancel] using abs_add_le ((d:ℝ)*s-b d*V) (b d*V) : |(d:ℝ)*s|≤_).trans (add_le_add hbase hb)
    rw [abs_mul,abs_of_pos hd0] at hs
    rw [spectralLineJet_selbergSliceMajorant,ite_eq_left (Finset.mem_Icc.mpr ⟨hd',hdN⟩),←div_eq_mul_one_div]
    apply (le_div_iff₀ (mul_pos hd0 hY)).mpr
    calc |s| *((d:ℝ)*H y) = ((d:ℝ)*|s|)*H y := by ring
         _ ≤ (err+|V|)*H y := mul_le_mul_of_nonneg_right hs hY.le
         _ ≤ _ := by linarith only [he,hv]
  · have hempty : T=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨hiD,hdi,_⟩ := Finset.mem_filter.mp hi
      exact hdN ((Nat.le_of_dvd (Finset.mem_Icc.mp hiD).1 hdi).trans (Finset.mem_Icc.mp hiD).2)
    simp [hempty,spectralLineJet_selbergSliceMajorant,hdN]

private theorem spectralLineJet_selberg_rough_row_domination (A : ℕ) :
    ∃ K > (0:ℝ), ∀ {N R k : ℕ}, 0<N → 0<R → N≤(R+1)^A → 0<k → k≤N*N →
      (∀ j, j≤R → 0<j → j.Coprime k) →
      let W := spectralLineJet_selbergSliceMajorant N
      let V := ∑ d ∈ k.divisors,W d*W (k/d)
      (k.totient:ℝ)*(∑ i ∈ Finset.Icc 1 (N*N) with k ∣ i, spectralLineJet_selbergSquareWeight N i/i)^2 ≤ K*V := by
  classical
  obtain ⟨C,hC,hs⟩ := spectralLineJet_selberg_slice_majorant A
  let L := (2:ℝ)^(2*A)
  refine ⟨L*C^4,by dsimp [L]; positivity,?_⟩
  intro N R k hN hR hNR hk hkN hr W V
  let t := ∑ i ∈ Finset.Icc 1 (N*N) with k ∣ i, spectralLineJet_selbergSquareWeight N i/i
  let D := Finset.Icc 1 N
  let u (i : ℕ) := spectralLineJet_selbergHalfMoebius i/i
  have hW := spectralLineJet_selberg_slice_majorant_spec N
  have hbd : |t|≤C^2*V := by
    dsimp [t]; rw [spectralLineJet_selberg_gcd_rows N hk]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd ↦ ?_
    have hdv := (Nat.mem_divisors.mp hd).1
    have hq := Nat.div_dvd_of_dvd hdv
    have hg : D.filter (fun i ↦ d ∣ i ∧ (true=true → i.gcd k=d)) = D.filter (fun i ↦ i.gcd k=d) := by
      ext i; simp only [Finset.mem_filter,true_implies]
      exact and_congr_right fun _ ↦ ⟨And.right,fun h ↦ ⟨h ▸ Nat.gcd_dvd_left i k,h⟩⟩
    have hf : D.filter (fun i ↦ k/d ∣ i ∧ (false=true → i.gcd k=k/d)) = D.filter (k/d ∣ ·) := by ext i; simp
    have he := hs hN hR hNR hk hkN hr hdv true
    have hm := hs hN hR hNR hk hkN hr hq false
    change |∑ i ∈ D.filter _, u i|≤C*W d at he
    change |∑ i ∈ D.filter _, u i|≤C*W (k/d) at hm
    rw [hg] at he
    rw [hf] at hm
    rw [abs_mul]
    exact (mul_le_mul he hm (abs_nonneg _) (mul_nonneg hC.le (hW d).1)).trans_eq (by ring)
  have hb : k≤(R+1)^(2*A) := hkN.trans (by simpa [Nat.mul_comm 2 A,pow_mul,pow_two] using Nat.mul_le_mul hNR hNR)
  have hc := (spectralLineJet_selberg_rough_divisors hk hR hb hr).1
  have hV : (k:ℝ)*V≤L := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ _d ∈ k.divisors,(1:ℝ) := by
           refine Finset.sum_le_sum fun d hd ↦ ?_
           have he : (d:ℝ)*(k/d:ℕ)=k := by exact_mod_cast Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1
           calc _ = ((d:ℝ)*W d)*((k/d:ℕ)*W (k/d)) := by rw [←he]; ring
                _ ≤ 1 := (mul_le_mul (hW d).2 (hW (k/d)).2 (mul_nonneg (Nat.cast_nonneg _) (hW _).1) zero_le_one).trans_eq (by ring)
         _ ≤ _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_one]; dsimp [L]; exact_mod_cast hc
  have hlin : (k:ℝ)*|t|≤L*C^2 := by
    calc _ ≤ (k:ℝ)*(C^2*V) := mul_le_mul_of_nonneg_left hbd (Nat.cast_nonneg _)
         _ = ((k:ℝ)*V)*C^2 := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hV (sq_nonneg _)
  have ht : (k.totient:ℝ)≤k := by exact_mod_cast Nat.totient_le k
  calc (k.totient:ℝ)*t^2 ≤ (k:ℝ)*t^2 := mul_le_mul_of_nonneg_right ht (sq_nonneg _)
       _ = ((k:ℝ)*|t|)*|t| := by rw [mul_assoc,←sq,sq_abs]
       _ ≤ (L*C^2)*(C^2*V) := mul_le_mul hlin hbd (abs_nonneg _) (by dsimp [L]; positivity)
       _ = _ := by ring

private theorem spectralLineJet_selberg_rough_convolution {N R : ℕ} (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 (N*N)) (hr : ∀ k ∈ S, ∀ j, j≤R → 0<j → j.Coprime k) :
    let W := spectralLineJet_selbergSliceMajorant N
    let D := (Finset.Icc 1 N).filter (fun d ↦ ∀ j, j≤R → 0<j → j.Coprime d)
    (∑ k ∈ S, ∑ d ∈ k.divisors,W d*W (k/d)) ≤ (∑ d ∈ D,W d)^2 := by
  classical
  intro W D
  let P := D ×ˢ D
  let idx (z : ℕ×ℕ) := z.1*z.2
  let f (z : ℕ×ℕ) := W z.1*W z.2
  have he (k : ℕ) (hk : k∈S) :
      (∑ d ∈ k.divisors, W d*W (k/d)) = ∑ z ∈ P with idx z=k, f z := by
    rw [← Nat.sum_divisorsAntidiagonal (fun d q ↦ W d*W q)]
    symm
    have hk0 : 0<k := (Finset.mem_Icc.mp (hS hk)).1
    apply Finset.sum_subset (show P.filter (fun z ↦ idx z=k) ⊆ k.divisorsAntidiagonal from fun z hz ↦
      Nat.mem_divisorsAntidiagonal.mpr ⟨(Finset.mem_filter.mp hz).2,hk0.ne'⟩)
    intro z hz hno
    have heq := (Nat.mem_divisorsAntidiagonal.mp hz).1
    have h1 : z.1 ∣ k := heq ▸ dvd_mul_right _ _
    have h2 : z.2 ∣ k := heq ▸ dvd_mul_left _ _
    have hzero (d : ℕ) (hd : d∣k) (hnd : d∉D) : W d=0 := by
      apply ite_eq_right
      exact fun hin ↦ hnd (Finset.mem_filter.mpr ⟨hin,fun j hj hj' ↦ Nat.Coprime.coprime_dvd_right hd (hr k hk j hj hj')⟩)
    change W z.1*W z.2=0
    by_cases h : z.1∈D
    · have hz2 : z.2∉D := fun h₂ ↦ hno (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h,h₂⟩,heq⟩)
      simp [hzero z.2 h2 hz2]
    · simp [hzero z.1 h1 h]
  calc _ = ∑ k ∈ S, ∑ z ∈ P with idx z=k, f z := Finset.sum_congr rfl he
       _ = ∑ z ∈ P with idx z∈S, f z := Finset.sum_fiberwise_eq_sum_filter P S idx f
       _ ≤ ∑ z ∈ P, f z := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun z _ _ ↦
         mul_nonneg (spectralLineJet_selberg_slice_majorant_spec N z.1).1 (spectralLineJet_selberg_slice_majorant_spec N z.2).1
       _ = _ := by rw [sq,Finset.sum_mul_sum,Finset.sum_product]

/-- The total Selberg energy of the sharp squared mollifier on rough moduli
is at most a constant times the reciprocal logarithm of the cutoff. This covers
every row through the square of the cutoff, including repeated prime factors.
The constant depends only on the fixed exponent relating the roughness threshold
to the cutoff. -/
theorem spectralLineJet_selbergSieveEnergy_all_rough_rows (A : ℕ) :
    ∃ C > (0:ℝ), ∀ {N R : ℕ}, 0<N → 0<R → N≤(R+1)^A → ∀ S : Finset ℕ,
      S ⊆ Finset.Icc 1 (N*N) → (∀ k ∈ S, ∀ j, j≤R → 0<j → j.Coprime k) →
      (∑ k ∈ S, (k.totient:ℝ)*
        (∑ d ∈ Finset.Icc 1 (N*N) with k ∣ d, spectralLineJet_selbergSquareWeight N d/d)^2) ≤
        C/(1+Real.log N) := by
  classical
  obtain ⟨K,hK,hrow⟩ := spectralLineJet_selberg_rough_row_domination A
  obtain ⟨C,hC,hweight⟩ := spectralLineJet_selberg_rough_weighted_mass A
  refine ⟨K*C^2,by positivity,?_⟩
  intro N R hN hR hNR S hS hr
  let W := spectralLineJet_selbergSliceMajorant N
  let D := (Finset.Icc 1 N).filter (fun d ↦ ∀ j, j≤R → 0<j → j.Coprime d)
  let H := 1+Real.log N
  have hH : 0<H := by dsimp [H]; linarith [Real.log_nonneg (by exact_mod_cast hN : (1:ℝ)≤N)]
  have hm := hweight hN hR hNR D (Finset.filter_subset _ _) (fun d hd ↦ (Finset.mem_filter.mp hd).2)
  have he : (∑ d ∈ D,W d) = ∑ d ∈ D,1/((d:ℝ)*Real.sqrt (1+Real.log (N/d:ℕ))) :=
    Finset.sum_congr rfl fun d hd ↦ ite_eq_left (Finset.mem_filter.mp hd).1
  rw [← he] at hm
  have hpos : 0≤(∑ d ∈ D,W d)*Real.sqrt H := mul_nonneg
    (Finset.sum_nonneg fun d _ ↦ (spectralLineJet_selberg_slice_majorant_spec N d).1) (Real.sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ hpos hm 2
  rw [mul_pow,Real.sq_sqrt hH.le] at hsq
  calc _ ≤ ∑ k ∈ S, K*∑ d ∈ k.divisors, W d*W (k/d) := Finset.sum_le_sum fun k hk ↦
         hrow hN hR hNR (Finset.mem_Icc.mp (hS hk)).1 (Finset.mem_Icc.mp (hS hk)).2 (hr k hk)
       _ ≤ K*(∑ d ∈ D,W d)^2 := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (spectralLineJet_selberg_rough_convolution S hS hr) hK.le
       _ ≤ _ := (le_div_iff₀ hH).mpr (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hsq hK.le)

end SelbergBulk

/-- A grid of width 1/(k+1) forces two distinct ordinates in the same cell. -/
private theorem spectralLineJet_close_ordinates
    (hcount : ∀ k : ℕ, ∃ T : ℕ, ∃ S : Finset ℝ, (k + 1) * (T + 1) < S.card ∧
      ∀ t ∈ S, t ∈ Ioc (0 : ℝ) T ∧ riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0)
    (k : ℕ) : ∃ t u : ℝ, t ≠ u ∧ |t - u| < 1 / ((k : ℝ) + 1) ∧
      riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 ∧
      riemannZeta (1 / 2 + (u : ℂ) * Complex.I) = 0 := by
  obtain ⟨T, S, hS, hz⟩ := hcount k
  let f (t : ℝ) := ⌊((k : ℝ) + 1) * t⌋₊
  have hk : 0 < (k : ℝ) + 1 := by positivity
  have hmap : MapsTo f S (Finset.range ((k + 1) * (T + 1))) := by
    intro t ht
    apply Finset.mem_range.mpr
    have hle : f t ≤ (k + 1) * T := by
      apply Nat.floor_le_of_le
      exact_mod_cast mul_le_mul_of_nonneg_left (hz t ht).1.2 hk.le
    exact hle.trans_lt (Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self T) (Nat.succ_pos k))
  obtain ⟨t, ht, u, hu, hneq, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (by simpa only [Finset.card_range] using hS) hmap
  refine ⟨t, u, hneq, ?_, (hz t ht).2, (hz u hu).2⟩
  have h₁ := Nat.floor_le (mul_nonneg hk.le (hz t ht).1.1.le)
  have h₂ := Nat.floor_le (mul_nonneg hk.le (hz u hu).1.1.le)
  have h₃ := Nat.lt_floor_add_one (((k : ℝ) + 1) * t)
  have h₄ := Nat.lt_floor_add_one (((k : ℝ) + 1) * u)
  change f t = f u at he
  change (f t : ℝ) ≤ _ at h₁
  change _ < (f t : ℝ) + 1 at h₃
  change (f u : ℝ) ≤ _ at h₂
  change _ < (f u : ℝ) + 1 at h₄
  rw [he] at h₁ h₃
  rw [abs_lt, ← neg_div, div_lt_iff₀ hk, lt_div_iff₀ hk]
  constructor <;> nlinarith

/-- The L² distance of two jets can be estimated by integrating their squared pointwise distance. -/
private theorem spectralLineJet_norm_sq {G : Type*} [MeasurableSpace G] (μ : Measure G)
    (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ g, ‖f g‖ ^ 2 ∂μ := by
  calc
    ‖f‖ ^ 2 = RCLike.re (inner ℂ f f) := by
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), Real.sq_sqrt inner_self_nonneg]
    _ = RCLike.re (∫ g, inner ℂ (f g) (f g) ∂μ) := by rw [L2.inner_def]
    _ = ∫ g, RCLike.re (inner ℂ (f g) (f g)) ∂μ :=
      (integral_re (L2.integrable_inner f f)).symm
    _ = ∫ g, ‖f g‖ ^ 2 ∂μ := by simp_rw [inner_self_eq_norm_sq]

open Filter in
open scoped Topology in
/-- A vanishing ordinate gap gives vanishing L² distance for unit-modulus phases.
The fixed L² representative shows the constant dominator is integrable. -/
private theorem spectralLineJet_dist_tendsto {G : Type*} [MeasurableSpace G] (μ : Measure G)
    (P : ℝ → G → ℂ) (hone : ∀ t g, ‖P t g‖ = 1)
    (hp : ∀ g, ContinuousAt (fun t ↦ P t g) 0) (hp0 : ∀ g, P 0 g = 1)
    (hsub : ∀ t u g, P t g - P u g = (P (t - u) g - 1) * P u g)
    (t u : ℕ → ℝ) (hlim : Tendsto (fun n ↦ t n - u n) atTop (𝓝 0))
    (x y : ℕ → Lp ℂ 2 μ)
    (hx : ∀ n, (x n : G → ℂ) =ᵐ[μ] P (t n))
    (hy : ∀ n, (y n : G → ℂ) =ᵐ[μ] P (u n)) :
    Tendsto (fun n ↦ dist (x n) (y n)) atTop (𝓝 0) := by
  let d (n : ℕ) := x n - y n
  have hd (n : ℕ) : ∀ᵐ g ∂μ, d n g = P (t n) g - P (u n) g := by
    filter_upwards [Lp.coeFn_sub (x n) (y n), hx n, hy n] with g h₁ h₂ h₃
    exact h₁.trans (congrArg₂ (· - ·) h₂ h₃)
  have h4 : Integrable (fun _ : G ↦ (4 : ℝ)) μ := by
    have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (x 0))).mp (Lp.memLp _)
    refine (hi.const_mul 4).congr ?_
    filter_upwards [hx 0] with g hg
    simp only [hg, hone, one_pow, mul_one]
  have he (g : G) : Tendsto (fun n ↦ ‖P (t n) g - P (u n) g‖ ^ 2) atTop (𝓝 0) := by
    have h := (((hp g).tendsto.comp hlim).sub_const 1).norm.pow 2
    simpa only [hsub, norm_mul, hone, mul_one, Function.comp_def, hp0, sub_self, norm_zero,
      zero_pow (by decide : 2 ≠ 0)] using h
  have hs := tendsto_integral_of_dominated_convergence
    (F := fun n g ↦ ‖d n g‖ ^ 2) (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ (4 : ℝ))
    (fun n ↦ (Lp.aestronglyMeasurable (d n)).norm.pow _) h4
    (fun n ↦ (hd n).mono fun g hg ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hg]
      have h := norm_sub_le (P (t n) g) (P (u n) g)
      rw [hone, hone] at h
      exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (by norm_num))
    (by
      filter_upwards [ae_all_iff.mpr hd] with g hg
      simpa only [hg] using he g)
  have hs' : Tendsto (fun n ↦ ‖d n‖ ^ 2) atTop (𝓝 0) := by
    simpa only [spectralLineJet_norm_sq μ, integral_zero] using hs
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero,
    d, dist_eq_norm] using (Real.continuous_sqrt.tendsto _).comp hs'

/-- Choose the trivial lift of the trivial rational norm-one character. -/
private theorem spectralLineJet_rational_basepoint :
    ∃ χ : PontryaginDual C₁(ℚ) → PontryaginDual C𝔽(ℚ), IsSpectralBasepointChoice χ ∧ χ 1 = 1 := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_spectralBasepointChoice ℚ
  refine ⟨Function.update ψ 1 1, ?_, Function.update_self ..⟩
  intro ω
  by_cases h : ω = 1
  · subst ω
    rw [Function.update_self]
    rfl
  · simpa only [Function.update_of_ne h] using hψ ω

/-- Each distinct critical-line zeta zero supplies a zeroth jet at Sobolev exponent two. -/
private theorem spectralLineJet_rational_zero_index
    (χ : PontryaginDual C₁(ℚ) → PontryaginDual C𝔽(ℚ)) (hχ : χ 1 = 1) (t : ℝ)
    (ht : riemannZeta (1/2 + (t : ℂ) * Complex.I) = 0) :
    ∃ j : SpectralLineJetIndex χ (1/2) 2, j.val = (1, t, 0) := by
  let z : ℂ := 1/2 + (t : ℂ) * Complex.I
  have hre : z.re = 1/2 := by simp [z, Complex.mul_re]
  have hne : z ≠ 1 := fun e ↦ by norm_num [e] at hre
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  have hz : 0 < meromorphicOrderAt riemannZeta z := by
    apply (tendsto_zero_iff_meromorphicOrderAt_pos (hm z (mem_univ z))).mp
    change riemannZeta z = 0 at ht
    rw [← ht]
    exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt
  have htwo : meromorphicOrderAt riemannZeta (2 : ℂ) = 0 :=
    (analyticOn_riemannZeta _ (by norm_num : (2 : ℂ) ≠ 1)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have hfin := hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ z) (by rw [htwo]; simp)
  have hnat : 0 < (meromorphicOrderAt riemannZeta z).untop₀.toNat := by
    rw [← WithTop.coe_untop₀_of_ne_top hfin] at hz
    have hint : 0 < (meromorphicOrderAt riemannZeta z).untop₀ := WithTop.coe_lt_coe.mp hz
    omega
  refine ⟨⟨(1, t, 0), ?_⟩, rfl⟩
  apply (lt_spectralBoundaryMultiplicity 2 _ 0).mpr
  refine ⟨?_, by norm_num⟩
  rw [hχ]
  convert hnat using 1
  push_cast
  rw [meromorphicOrderAt_finiteHeckeL_continuation (1 : PontryaginDual C𝔽(ℚ)) hm (fun s ↦
    (dedekindZeta_rat_eq_riemannZeta s.property).symm.trans
      (finiteHeckeL_one_eq_dedekindZeta (K := ℚ) s).symm) (by rw [hre]; norm_num)]

/-- A uniform bound on the diagonal products of a biorthogonal system
with normalized coordinate forms forces the forms to be uniformly separated. -/
private theorem spectralLineJet_separation_of_diagonal_bound
    {ι E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V]
    (x : ι → E) (Λ : ι → StrongDual ℂ E) (hB : IsSpectralMarkushevichBasis x Λ)
    (D : StrongDual ℂ E → V) (hD : Isometry D)
    (hN : IsNormalizedSpectralFamily (fun i ↦ D (Λ i)))
    (C : ℝ) (hC : 0 < C) (hbound : ∀ i, ‖D (Λ i)‖ * ‖x i‖ ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i j, i ≠ j → ε ≤ dist (D (Λ i)) (D (Λ j)) := by
  obtain ⟨c, hc, hlower⟩ := hN.2
  refine ⟨c / C, div_pos hc hC, fun i j hij ↦ ?_⟩
  have heval : 1 ≤ ‖Λ i - Λ j‖ * ‖x i‖ := by
    simpa only [sub_apply, hB.1 i, hB.2.1 i j hij, sub_zero, norm_one]
      using (Λ i - Λ j).le_opNorm (x i)
  have hx : c * ‖x i‖ ≤ C :=
    (mul_le_mul_of_nonneg_right (hlower i) (norm_nonneg _)).trans (hbound i)
  rw [hD.dist_eq, dist_eq_norm, div_le_iff₀ hC]
  calc
    c = c * 1 := (mul_one _).symm
    _ ≤ c * (‖Λ i - Λ j‖ * ‖x i‖) := mul_le_mul_of_nonneg_left heval hc.le
    _ = ‖Λ i - Λ j‖ * (c * ‖x i‖) := by ring
    _ ≤ ‖Λ i - Λ j‖ * C := mul_le_mul_of_nonneg_left hx (norm_nonneg _)

/-- At exponent two the printed and corrected jet cutoffs agree. The printed
bound would therefore separate all the rational jet vectors uniformly in L². -/
private theorem spectralLineJet_separation_of_printed
    (h : Printed.spectralLineJet_uniformBiorthogonalBound)
    (χ : PontryaginDual C₁(ℚ) → PontryaginDual C𝔽(ℚ)) (hχ : IsSpectralBasepointChoice χ) :
    let hs : (1 : ℝ) < 2 := by norm_num
    let jet (j : SpectralLineJetIndex χ (1 / 2) 2) :=
      (spectralLineJet_memLp χ hs j).toLp (spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2)
    ∃ ε : ℝ, 0 < ε ∧ ∀ i j, i ≠ j → ε ≤ dist (jet i) (jet j) := by
  intro hs jet
  obtain ⟨x, Λ, hB, heq, hN⟩ := spectralLineMarkushevichBasis_normalized (a := 1/2) χ hχ hs
  let D := spectralSobolevDualEmbedding ℚ (1/2) (le_rfl (a := (0 : ℝ))) (zero_lt_one.trans hs).le
  have hD : Isometry D := (spectralSobolevDualEmbedding_isometry_range (F := ℚ) (1/2) le_rfl _).1
  have hP := h ℚ χ hχ (1/2) 2 hs
  dsimp only at hP
  have hcut : Nat.floor (((2 : ℝ) - 1) / 2 + 1) = Nat.ceil (((2 : ℝ) - 1) / 2) := by
    exact ((Nat.floor_eq_iff (by norm_num) (n := 1)).mpr (by norm_num)).trans
      ((Nat.ceil_eq_iff (by decide : (1 : ℕ) ≠ 0)).mpr (by norm_num)).symm
  rw [hcut] at hP
  obtain ⟨C, hC, hbound⟩ := hP x Λ hB (fun j ↦ ⟨_, heq j⟩)
  obtain ⟨ε, hε, hsep⟩ := spectralLineJet_separation_of_diagonal_bound x Λ hB D hD hN C hC
    (fun i ↦ hbound i i rfl rfl le_rfl)
  refine ⟨ε, hε, fun i j hij ↦ ?_⟩
  simpa only [D, heq] using hsep i j hij

open Filter in
open scoped Topology in
/-- For the rational trivial character, the order-zero jet at frequency t is the
unitary phase |g|^(it). Its L² distance to the jet at u tends to zero when t-u does. -/
private theorem spectralLineJet_rational_phase_dist
    (χ : PontryaginDual C₁(ℚ) → PontryaginDual C𝔽(ℚ)) (hχ : χ 1 = 1)
    (t u : ℕ → ℝ) (hlim : Tendsto (fun n ↦ t n - u n) atTop (𝓝 0))
    (i j : ℕ → SpectralLineJetIndex χ (1 / 2) 2)
    (hi : ∀ n, (i n).val = (1, t n, 0)) (hj : ∀ n, (j n).val = (1, u n, 0)) :
    let hs : (1 : ℝ) < 2 := by norm_num
    let jet (v : SpectralLineJetIndex χ (1 / 2) 2) :=
      (spectralLineJet_memLp χ hs v).toLp (spectralZeroJet (χ v.val.1) 0 v.val.2.1 v.val.2.2)
    Tendsto (fun n ↦ dist (jet (i n)) (jet (j n))) atTop (𝓝 0) := by
  intro hs jet
  let R (g : C𝔽(ℚ)) : ℝ := ((ideleClassNorm ℚ g).val : ℝ)
  let P (t : ℝ) (g : C𝔽(ℚ)) : ℂ := (R g : ℂ) ^ ((t : ℂ) * Complex.I)
  have hR (g) : 0 < R g := Units.zero_lt (ideleClassNorm ℚ g)
  have hP (t g) : ‖P t g‖ = 1 := by
    dsimp only [P]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hR g)]
    simp [Complex.mul_re]
  have hcont (g) : ContinuousAt (fun r ↦ P r g) 0 :=
    ((continuous_const_cpow' (Complex.ofReal_ne_zero.mpr (hR g).ne')).comp
      (Complex.continuous_ofReal.mul continuous_const)).continuousAt
  have hsub (t u g) : P t g - P u g = (P (t - u) g - 1) * P u g := by
    have he : P t g = P (t - u) g * P u g := by
      dsimp [P]
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hR g).ne')]
      push_cast
      ring_nf
    rw [he, sub_mul, one_mul]
  let ν := (ideleClassTamagawaMeasure ℚ).withDensity fun g : C𝔽(ℚ) ↦
    ENNReal.ofReal (intervalSobolevDensity 0 0 2 (Real.log (R g)))⁻¹
  have hc (v : SpectralLineJetIndex χ (1 / 2) 2) (r : ℝ) (hv : v.val = (1, r, 0)) :
      (jet v : C𝔽(ℚ) → ℂ) =ᵐ[ν] P r := by
    refine (MemLp.coeFn_toLp (spectralLineJet_memLp χ hs v)).trans (ae_of_all _ fun g ↦ ?_)
    rw [hv, hχ, spectralZeroJet, pow_zero, mul_one, Complex.ofReal_zero, zero_add]
    change (1 : ℂ) * _ = _
    exact one_mul _
  exact spectralLineJet_dist_tendsto ν P hP hcont (fun g ↦ by simp [P]) hsub t u hlim
    (fun n ↦ jet (i n)) (fun n ↦ jet (j n)) (fun n ↦ hc _ _ (hi n)) (fun n ↦ hc _ _ (hj n))

section SelbergWindows

private theorem spectralLineJet_window_continuous {f : ℝ → ℝ} (hf : Continuous f) (h : ℝ) :
    Continuous (fun t : ℝ ↦ ∫ u in t..t + h, f u) := by
  let P (t : ℝ) := ∫ u in (0 : ℝ)..t, f u
  have hP : Continuous P := intervalIntegral.continuous_primitive (fun a b ↦ hf.intervalIntegrable a b) 0
  apply ((hP.comp (continuous_id.add_const h)).sub hP).congr
  intro t
  simpa [P] using (eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 t) (hf.intervalIntegrable t (t + h)))).symm

/-- Titchmarsh, Lemma 10.21, p. 278. Each u between h and T occurs for exactly
h units of window starts. This gives the required first moment from a single
ordinary integral of the absolute mollified Hardy function. -/
private theorem spectralLineJet_window_mass {f : ℝ → ℝ} (hf : Continuous f) (hf₀ : ∀ u, 0 ≤ f u)
    {T h : ℝ} (hh : 0 ≤ h) (hT : h ≤ T) :
    h * (∫ u in h..T, f u) ≤ ∫ t in Ioc (0 : ℝ) T, ∫ u in t..t + h, f u := by
  have ht := hh.trans hT
  have hs (a b : ℝ) : (∫ s in (0 : ℝ)..b, f (a + s)) = ∫ s in a..a + b, f s := by
    simpa only [add_zero] using intervalIntegral.integral_comp_add_left (a := 0) (b := b) f a
  have hi : IntegrableOn (fun p : ℝ × ℝ ↦ f (p.1 + p.2)) (uIoc 0 h ×ˢ uIoc 0 T) := by
    apply ((hf.comp (continuous_fst.add continuous_snd)).continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    exact Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  rw [← intervalIntegral.integral_of_le ht]
  calc
    _ = ∫ r in (0 : ℝ)..h, ∫ u in h..T, f u := by simp
    _ ≤ ∫ r in (0 : ℝ)..h, ∫ u in r..r + T, f u := by
      apply intervalIntegral.integral_mono_on hh intervalIntegrable_const
        ((spectralLineJet_window_continuous hf T).intervalIntegrable _ _)
      intro r hr
      exact intervalIntegral.integral_mono_interval hr.2 hT (by linarith [hr.1])
        (Filter.Eventually.of_forall hf₀) (hf.intervalIntegrable _ _)
    _ = ∫ r in (0 : ℝ)..h, ∫ t in (0 : ℝ)..T, f (r + t) := by simp_rw [hs]
    _ = ∫ t in (0 : ℝ)..T, ∫ r in (0 : ℝ)..h, f (r + t) := intervalIntegral_intervalIntegral_swap hi
    _ = _ := intervalIntegral.integral_congr (fun t _ ↦ by simpa only [add_comm t] using hs t h)

/-- A nonnegative mollifier cannot create a sign change. Strict short-interval
cancellation of the mollified Hardy function detects an actual zeta ordinate. -/
private theorem spectralLineJet_zero_of_window_cancellation
    {w : ℝ → ℝ} (hw : ∀ u, 0 ≤ w u) {t h : ℝ} (hh : 0 ≤ h)
    (hc : |∫ u in t..t + h, w u * hardyZ u| < ∫ u in t..t + h, |w u * hardyZ u|) :
    ∃ u ∈ Icc t (t + h), riemannZeta (1 / 2 + (u : ℂ) * Complex.I) = 0 := by
  have ht : t ≤ t + h := by linarith
  by_contra! hn
  have hsign : (∀ u ∈ Icc t (t + h), 0 ≤ hardyZ u) ∨ (∀ u ∈ Icc t (t + h), hardyZ u ≤ 0) := by
    by_contra! h
    obtain ⟨⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩⟩ := h
    obtain ⟨u, hu, hz⟩ := isPreconnected_Icc.intermediate_value hx hy continuous_hardyZ.continuousOn
      (show 0 ∈ Icc (hardyZ x) (hardyZ y) from ⟨hx'.le, hy'.le⟩)
    exact hn u hu ((hardyZ_eq_zero_iff u).mp hz)
  apply hc.not_ge
  rcases hsign with pos | neg
  · have hp (u : ℝ) (hu : u ∈ Icc t (t + h)) : 0 ≤ w u * hardyZ u := mul_nonneg (hw u) (pos u hu)
    have he : (∫ u in t..t + h, |w u * hardyZ u|) = ∫ u in t..t + h, w u * hardyZ u :=
      intervalIntegral.integral_congr (fun u hu ↦ abs_of_nonneg (hp u (uIcc_of_le ht ▸ hu)))
    rw [he, abs_of_nonneg (intervalIntegral.integral_nonneg ht hp)]
  · have hp (u : ℝ) (hu : u ∈ Icc t (t + h)) : w u * hardyZ u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hw u) (neg u hu)
    have he : (∫ u in t..t + h, |w u * hardyZ u|) = ∫ u in t..t + h, -(w u * hardyZ u) :=
      intervalIntegral.integral_congr (fun u hu ↦ abs_of_nonpos (hp u (uIcc_of_le ht ▸ hu)))
    have hi := intervalIntegral.integral_nonneg (μ := volume) ht (fun u hu ↦ neg_nonneg.mpr (hp u hu))
    rw [intervalIntegral.integral_neg] at hi
    rw [he, intervalIntegral.integral_neg, abs_of_nonpos (neg_nonneg.mp hi)]

/-- Cauchy–Schwarz for the cancellation integral localized to a finite-measure
set of starting points. -/
private theorem spectralLineJet_window_cs {μ : Measure ℝ} [IsFiniteMeasure μ]
    {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    (∫ t, f t ∂μ) ^ 2 ≤ μ.real univ * ∫ t, (f t) ^ 2 ∂μ := by
  have hcs := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := fun t ↦ ‖f t‖) (g := fun _ ↦ (1 : ℝ))
    Real.HolderConjugate.two_two (by simpa using hf.norm) (memLp_const _)
  have hle : ‖∫ t, f t ∂μ‖ ≤ Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂μ) * Real.sqrt (μ.real univ) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    simpa [Real.sqrt_eq_rpow] using hcs
  have hs := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _),
    Real.sq_sqrt measureReal_nonneg, mul_comm] at hs
  simpa only [Real.norm_eq_abs, sq_abs] using hs

local notation "absWindow(" w ", " h ", " t ")" =>
  ∫ u in t..t + h, |w u * hardyZ u|
local notation "cancellation(" w ", " h ", " t ")" =>
  absWindow(w, h, t) - |∫ u in t..t + h, w u * hardyZ u|

/-- Titchmarsh, §10.22, pp. 278–279. Each distinct ordinate covers a set of
window starts of length at most h, even when it has arbitrarily high multiplicity.
The last windows may end at T + h. -/
private theorem spectralLineJet_window_count_bound {w : ℝ → ℝ} (hw : Continuous w)
    (hw₀ : ∀ u, 0 ≤ w u) {T h : ℝ} (hh : 0 ≤ h) (S : Finset ℝ)
    (hS : ∀ u ∈ Ioc (0 : ℝ) (T + h), riemannZeta (1 / 2 + (u : ℂ) * Complex.I) = 0 → u ∈ S) :
    (∫ t in Ioc (0 : ℝ) T, cancellation(w, h, t)) ^ 2 ≤
      (S.card : ℝ) * h * ∫ t in Ioc (0 : ℝ) T, absWindow(w, h, t) ^ 2 := by
  classical
  let K := Ioc (0 : ℝ) T
  let C := ⋃ u ∈ S, Icc (u - h) u
  let U := K ∩ C
  let A (t : ℝ) := absWindow(w, h, t)
  let D (t : ℝ) := cancellation(w, h, t)
  have hA : Continuous A := spectralLineJet_window_continuous (hw.mul continuous_hardyZ).abs h
  have hD : Continuous D := hA.sub (spectralLineJet_window_continuous (hw.mul continuous_hardyZ) h).abs
  have hDA (t : ℝ) : 0 ≤ D t ∧ D t ≤ A t :=
    ⟨sub_nonneg.mpr (intervalIntegral.abs_integral_le_integral_abs (by linarith)), sub_le_self _ (abs_nonneg _)⟩
  have hC : IsCompact C := S.finite_toSet.isCompact_biUnion (fun _ _ ↦ isCompact_Icc)
  have hU : MeasurableSet U := measurableSet_Ioc.inter hC.measurableSet
  have hUK : U ⊆ K := inter_subset_left
  have hUcc : U ⊆ Icc (0 : ℝ) T := hUK.trans Ioc_subset_Icc_self
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr
    (measure_ne_top_of_subset hUcc isCompact_Icc.measure_lt_top.ne)
  have hsupport : ∀ t ∈ K, D t ≠ 0 → t ∈ U := by
    intro t ht hn
    have hd := lt_of_le_of_ne (hDA t).1 (Ne.symm hn)
    obtain ⟨u, hu, hz⟩ := spectralLineJet_zero_of_window_cancellation hw₀ hh (sub_pos.mp hd)
    have huS := hS u ⟨lt_of_lt_of_le ht.1 hu.1, (hu.2.trans (add_le_add_left ht.2 h))⟩ hz
    exact ⟨ht, mem_iUnion₂.mpr ⟨u, huS, sub_le_iff_le_add.mpr hu.2, hu.1⟩⟩
  have hloc : (∫ t in K, D t) = ∫ t in U, D t := by
    calc
      _ = ∫ t in K, U.indicator D t := setIntegral_congr_fun measurableSet_Ioc (fun t ht ↦ by
        by_cases hu : t ∈ U
        · rw [indicator_of_mem hu]
        · rw [indicator_of_notMem hu]
          exact not_ne_iff.mp (fun hn ↦ hu (hsupport t ht hn)))
      _ = _ := by rw [integral_indicator hU, Measure.restrict_restrict hU, inter_eq_left.mpr hUK]
  have hs : volume.real U ≤ (S.card : ℝ) * h := calc
    _ ≤ volume.real C := measureReal_mono inter_subset_right hC.measure_lt_top.ne
    _ ≤ ∑ u ∈ S, volume.real (Icc (u - h) u) := measureReal_biUnion_finset_le S _
    _ = _ := by simp [Real.volume_real_Icc_of_le (sub_le_self _ hh)]
  have intK {f : ℝ → ℝ} (hf : Continuous f) : IntegrableOn f K :=
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hcs := spectralLineJet_window_cs (μ := volume.restrict U) (f := D)
    ((memLp_two_iff_integrable_sq hD.aestronglyMeasurable).mpr ((intK (hD.pow 2)).mono_set hUK))
  have hsq : (∫ t in U, D t ^ 2) ≤ ∫ t in K, A t ^ 2 := calc
    _ ≤ ∫ t in U, A t ^ 2 := setIntegral_mono_on ((intK (hD.pow 2)).mono_set hUK)
      ((intK (hA.pow 2)).mono_set hUK) hU (fun t _ ↦ pow_le_pow_left₀ (hDA t).1 (hDA t).2 2)
    _ ≤ _ := setIntegral_mono_set (intK (hA.pow 2)) (Filter.Eventually.of_forall fun t ↦ sq_nonneg _)
      (Filter.Eventually.of_forall fun _ hu ↦ hUK hu)
  change (∫ t in K, D t) ^ 2 ≤ (S.card : ℝ) * h * ∫ t in K, A t ^ 2
  rw [hloc]
  have hcs' : (∫ t in U, D t) ^ 2 ≤ volume.real U * ∫ t in U, D t ^ 2 := by simpa using hcs
  exact hcs'.trans (mul_le_mul hs hsq (integral_nonneg fun _ ↦ sq_nonneg _) (by positivity))

private theorem spectralLineJet_count_of_window_moments {w : ℝ → ℝ} (hw : Continuous w)
    (hw₀ : ∀ u, 0 ≤ w u) (T M : ℕ) {h : ℝ} (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (hm : (M : ℝ) * h * (∫ t in Ioc (0 : ℝ) T, absWindow(w, h, t) ^ 2) <
      (∫ t in Ioc (0 : ℝ) T, cancellation(w, h, t)) ^ 2) :
    ∃ S : Finset ℝ, M < S.card ∧
      ∀ u ∈ S, u ∈ Ioc (0 : ℝ) (T + 1) ∧ riemannZeta (1 / 2 + (u : ℂ) * Complex.I) = 0 := by
  classical
  let Z := {u : ℝ | u ∈ Ioc (0 : ℝ) (T + 1) ∧ riemannZeta (1 / 2 + (u : ℂ) * Complex.I) = 0}
  by_cases hZ : Z.Finite
  · refine ⟨hZ.toFinset, ?_, fun u hu ↦ hZ.mem_toFinset.mp hu⟩
    have hb := spectralLineJet_window_count_bound hw hw₀ hh hZ.toFinset (T := T) (by
      intro u hu hz
      exact hZ.mem_toFinset.mpr ⟨⟨hu.1, by linarith [hu.2]⟩,hz⟩)
    by_contra! hcard
    apply hm.not_ge (hb.trans ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hh)
      (integral_nonneg fun _ ↦ sq_nonneg _)
  · obtain ⟨S, hS, hcard⟩ := (Set.not_finite.mp hZ).exists_subset_card_eq (M + 1)
    exact ⟨S, by omega, fun _ hu ↦ hS hu⟩

/-- The nonnegative weight multiplying Hardy's Z in Selberg's mollification.
The gamma and exponential factors are Titchmarsh §10.10, p. 269, with δ=1/T,
up to an absolute constant. The finite Dirichlet polynomial is evaluated on
the critical line. -/
private def spectralLineJet_selbergWeight (T N : ℕ) (b : ℕ → ℝ) (t : ℝ) : ℝ :=
  ‖Complex.Gamma (1 / 4 + (t : ℂ) / 2 * Complex.I)‖ * Real.exp ((Real.pi / 4 - 1 / (2 * T)) * t) *
    ‖∑ n ∈ Finset.Icc 1 N, ((b n / Real.sqrt n : ℝ) : ℂ) *
      Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ^ 2

private theorem spectralLineJet_selbergWeight_spec (T N : ℕ) (b : ℕ → ℝ) :
    Continuous (spectralLineJet_selbergWeight T N b) ∧ ∀ t, 0 ≤ spectralLineJet_selbergWeight T N b t := by
  have hg : Continuous (fun t : ℝ ↦ Complex.Gamma (1 / 4 + (t : ℂ) / 2 * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply ContinuousAt.comp (g := Complex.Gamma) (f := fun x : ℝ ↦ 1 / 4 + (x : ℂ) / 2 * Complex.I)
    · apply Complex.continuousAt_Gamma
      intro m he
      have h := congrArg Complex.re he
      norm_num [Complex.div_ofNat_re, Complex.div_ofNat_im] at h
      linarith [Nat.cast_nonneg (α := ℝ) m]
    · fun_prop
  constructor
  · unfold spectralLineJet_selbergWeight
    apply (hg.norm.mul (by fun_prop)).mul
    fun_prop
  · intro t
    unfold spectralLineJet_selbergWeight
    positivity

/-- Remaining classical input, Titchmarsh §§10.17, 10.19, 10.21–10.22,
pp. 276–279. A finite mollifier with real coefficients has a positive integral of the absolute mollified Hardy function
over the bulk interval [h,T]. Its signed window second moment is small in comparison, and its absolute
second moment is bounded at the same scale. Selberg takes h proportional to
1/log T, hence arbitrarily small. All integrals are of the mollified Hardy
function, with no zero-count premise. -/
private theorem spectralLineJet_selberg_mollified_window_moments :
    ∃ c > (0 : ℝ), ∀ ε > (0 : ℝ), ∃ (T N : ℕ) (b : ℕ → ℝ) (h : ℝ),
      1 ≤ T ∧ 1 ≤ N ∧ b 1 = 1 ∧ (∀ n ∈ Finset.Icc 1 N, |b n| ≤ 1) ∧
      0 < h ∧ h ≤ 1 ∧ h < ε ∧
      let w := spectralLineJet_selbergWeight T N b
      let M := h * ∫ u in h..(T : ℝ), |w u * hardyZ u|
      0 < M ∧
        4 * T * (∫ t in Ioc (0 : ℝ) T, (∫ u in t..t + h, w u * hardyZ u) ^ 2) ≤ M ^ 2 ∧
        c * T * (∫ t in Ioc (0 : ℝ) T, absWindow(w, h, t) ^ 2) ≤ M ^ 2 := by
  sorry

/-- Classical input: the number of distinct critical-line zeta ordinates up to height T,
divided by T, is unbounded. This follows from a positive proportion of distinct critical-line
zeros (Selberg 1942) and the Riemann–von Mangoldt count. Not a statement of the paper and not
a gap in it: a known theorem of which this project has no formal proof. It is the arithmetic
input for the refutation of (10.3.1.18), p. 451, which is proved from it by name. -/
private theorem spectralLineJet_rational_critical_zero_count (k : ℕ) :
    ∃ T : ℕ, ∃ S : Finset ℝ, (k + 1) * (T + 1) < S.card ∧
      ∀ t ∈ S, t ∈ Ioc (0 : ℝ) T ∧ riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 := by
  obtain ⟨c, hc, hm⟩ := spectralLineJet_selberg_mollified_window_moments
  obtain ⟨T, N, b, h, hT, -,-,-,hh, hh₁, heps, hP, hB₀, hA₀⟩ :=
    hm (c / (16 * (k + 1))) (by positivity)
  let w := spectralLineJet_selbergWeight T N b
  obtain ⟨hw, hw₀⟩ := spectralLineJet_selbergWeight_spec T N b
  let K := Ioc (0 : ℝ) T
  let A (t : ℝ) := absWindow(w, h, t)
  let B (t : ℝ) := ∫ u in t..t + h, w u * hardyZ u
  let M := ∫ t in K, A t
  let V := ∫ t in K, A t ^ 2
  let L := ∫ t in K, |B t|
  let P := h * ∫ u in h..(T : ℝ), |w u * hardyZ u|
  change 0 < P at hP
  have hPM : P ≤ M := spectralLineJet_window_mass (hw.mul continuous_hardyZ).abs
    (fun _ ↦ abs_nonneg _) hh.le (hh₁.trans (by exact_mod_cast hT))
  have hM := hP.trans_le hPM
  have hB : 4 * (T : ℝ) * (∫ t in K, B t ^ 2) ≤ M ^ 2 :=
    hB₀.trans (pow_le_pow_left₀ hP.le hPM 2)
  have hA : c * (T : ℝ) * V ≤ M ^ 2 := hA₀.trans (pow_le_pow_left₀ hP.le hPM 2)
  have hAc : Continuous A := spectralLineJet_window_continuous (hw.mul continuous_hardyZ).abs h
  have hBc : Continuous B := spectralLineJet_window_continuous (hw.mul continuous_hardyZ) h
  have hi {f : ℝ → ℝ} (hf : Continuous f) : IntegrableOn f K :=
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr
    (measure_ne_top_of_subset Ioc_subset_Icc_self isCompact_Icc.measure_lt_top.ne)
  have hcs := spectralLineJet_window_cs (μ := volume.restrict K) (f := fun t ↦ |B t|)
    ((memLp_two_iff_integrable_sq hBc.abs.aestronglyMeasurable).mpr (hi (hBc.abs.pow 2)))
  have hs : L ^ 2 ≤ (T : ℝ) * ∫ t in K, B t ^ 2 := by
    simpa [L, K, sq_abs, Real.volume_real_Ioc_of_le] using hcs
  have hL : 2 * L ≤ M := by nlinarith [sq_nonneg (2 * L - M)]
  have hΔ : (∫ t in K, cancellation(w, h, t)) = M - L :=
    integral_sub (hi hAc) (hi hBc.abs)
  have hV : 0 ≤ V := integral_nonneg fun _ ↦ sq_nonneg _
  have hcoef : ((k + 1 : ℕ) : ℝ) * ((T + 2 : ℕ) : ℝ) * h < c * T / 4 := by
    have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have he := (lt_div_iff₀ (by positivity : (0 : ℝ)<16 * (k + 1))).mp heps
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : (T : ℝ)+2 ≤ 3 * T) (by positivity : 0 ≤ ((k : ℝ)+1) * h),
      mul_lt_mul_of_pos_right he (by linarith : (0 : ℝ)<T), mul_pos hc (by linarith : (0 : ℝ)<T)]
  have hsmall : (↑((k + 1) * (T + 2) : ℕ) : ℝ) * h * V < (M - L) ^ 2 := by
    push_cast at hcoef ⊢
    rcases hV.eq_or_lt with hv | hv
    · rw [← hv, mul_zero]
      exact sq_pos_of_pos (by linarith)
    · have hl := mul_lt_mul_of_pos_right hcoef hv
      nlinarith [sq_nonneg (M - 2 * L), mul_nonneg (by linarith : 0 ≤ M - 2 * L) (by linarith : 0 ≤ 3 * M - 2 * L)]
  obtain ⟨S, hcard, hS⟩ := spectralLineJet_count_of_window_moments hw hw₀ T ((k + 1) * (T + 2))
    hh.le hh₁ (by change _ * h * V < (∫ t in K, cancellation(w, h, t)) ^ 2; rwa [hΔ])
  exact ⟨T + 1, S, hcard, fun t ht ↦ by simpa only [Nat.cast_add, Nat.cast_one] using hS t ht⟩

end SelbergWindows

/-- Paper: (10.3.1.18), p. 451. For F = ℚ use the trivial base character,
a = 1/2 and s = 2. Take pairs of simple critical-line zeta zeros with
ordinates t and u tending arbitrarily close. The two cutoffs agree at s = 2.
The zeroth jets have the same positive norm and their difference tends to
zero by dominated convergence in the reciprocal Sobolev weight. Biorthogonality gives
1 ≤ ‖Λₜ − Λᵤ‖ ‖ψₜ‖, forcing the paired norm products to be unbounded. -/
theorem Printed.spectralLineJet_uniformBiorthogonalBound_false :
    ¬ Printed.spectralLineJet_uniformBiorthogonalBound := by
  classical
  intro h
  obtain ⟨χ, hχ, hχ₁⟩ := spectralLineJet_rational_basepoint
  obtain ⟨ε, hε, hsep⟩ := spectralLineJet_separation_of_printed h χ hχ
  choose t u hne hgap ht hu using spectralLineJet_close_ordinates spectralLineJet_rational_critical_zero_count
  choose i hi using fun n ↦ spectralLineJet_rational_zero_index χ hχ₁ (t n) (ht n)
  choose j hj using fun n ↦ spectralLineJet_rational_zero_index χ hχ₁ (u n) (hu n)
  have hlim : Filter.Tendsto (fun n ↦ t n - u n) Filter.atTop (nhds 0) :=
    squeeze_zero_norm (fun n ↦ (hgap n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have hdist := spectralLineJet_rational_phase_dist χ hχ₁ t u hlim i j hi hj
  obtain ⟨n, hn⟩ := (hdist.eventually (eventually_lt_nhds hε)).exists
  apply (hsep (i n) (j n) ?_).not_gt hn
  intro heq
  have hr := congrArg (fun v : SpectralLineJetIndex χ (1 / 2) 2 ↦ v.val.2.1) heq
  exact hne n (by simpa only [hi, hj] using hr)

/-- Paper: Theorem 10.3.1.1(3), p. 449. A test of left-translation weight
ω⁻¹ is asserted to give an operator valued in the line quotient isotype ω. -/
def Printed.spectralLineConvolution_conjugateWeight_range : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω) →
    ∀ (a s : ℝ) (hs : 1 < s) (ω : PontryaginDual C₁(F)) (φ : BruhatCompactSupport C𝔽(F)),
      (∀ k : C₁(F), ∀ g : C𝔽(F), φ.val (k.val⁻¹ * g) = (ω⁻¹ k : ℂ) * φ.val g) →
      range (spectralConvolution (F := F) a h₀ hs₀(hs) φ) ⊆
        range (fun v : Wω(F, 0, 0, s, h₀, hs₀(hs), ω) ↦
          (globalThetaSobolev F a h₀ hs₀(hs)).mkQ v.val)

section ConjugateWeightCounterexample

open Filter IsDedekindDomain
open scoped NumberField.AdeleRing SchwartzMap Topology

local notation "restrictNormOne(" F ")" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁(F) →ₜ* C𝔽(F))
local notation "logNorm(" F ")" => (logIdeleClassNorm F)
local notation "W(" F ", " s ")" => CompactIntervalSobolev (μ𝔽(F)) logNorm(F) 0 0 s
local notation "ρ(" F ", " hs ")" => hardySobolevTranslation (μ𝔽(F)) m𝔽(F) 0 0 _ h₀ hs
local notation "N(" F ", " a ", " hs ")" => globalThetaSobolev F a h₀ hs

private theorem spectralLine_wrongWeight_log_continuous (F : Type) [Field F] [NumberField F] :
    Continuous logNorm(F) :=
  Real.continuousOn_log.comp_continuous
    (NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous))
    (fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne')

/-- A compact Bruhat cutoff times the inverse of a norm twist has the opposite
translation weight to the twist's restriction, and its pairing is positive. -/
private theorem spectralLine_wrongWeight_test {F : Type} [Field F] [NumberField F]
    (θ : PontryaginDual C𝔽(F)) (t : ℝ) :
    let η := ideleClassNormTwist θ (shift(0, t))
    let γ := θ.comp (restrictNormOne(F))
    ∃ φ : BruhatCompactSupport C𝔽(F), Continuous φ.val ∧
      (∀ k : C₁(F), ∀ g, φ.val (k.val⁻¹ * g) = (γ k : ℂ) * φ.val g) ∧
      (∫ g, φ.val g * η g ∂μ𝔽(F)) ≠ 0 := by
  intro η γ
  let m := m𝔽(F)
  let hm : IsModulation m := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  have hms : Surjective m := by
    intro q
    exact ⟨QuotientGroup.mk (canonicalIdeleNormSection F q),
      canonicalIdeleNormSection_rightInverse F q⟩
  obtain ⟨b, hb⟩ := exists_smoothModulatedCutoff_radius_two m hm hms
  have hbc : HasCompactSupport b := by
    let e := Nonneg.unitsHomeomorphPos ℝ
    have hS : IsCompact ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Icc (2⁻¹ : ℝ) 2) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr]
      · exact isCompact_Icc
      · intro r hr
        exact (by norm_num : (0 : ℝ) < 2⁻¹).trans_le hr.1
    exact (hm.1.isCompact_preimage (e.isCompact_preimage.mpr hS)).of_isClosed_subset
      (isClosed_tsupport b) hb.1.support_subset
  have hbC : HasCompactSupport (fun g ↦ (b g : ℂ)) :=
    hbc.comp_left Complex.ofReal_zero
  let b₀ : BruhatCompactSupport C𝔽(F) :=
    ⟨_, (mem_bruhatSmoothSubmodule_iff _).mpr hb.2, hbC⟩
  let B := bruhatCompactSupportToModulatedExponentialDecay m univ hm hms b₀
  let ηInv := η.comp (ContinuousMonoidHom.inv _)
  obtain ⟨E, hE⟩ := modulatedExponentialDecay_mul_quasiCharacter m hm hms ηInv
  have hEB (g : C𝔽(F)) : (E B).val g = (η g)⁻¹ * (b g : ℂ) :=
    (hE B g).trans (by change η g⁻¹ * (b g : ℂ) = _; rw [map_inv])
  have hBs : HasCompactSupport (E B).val := by
    rw [funext hEB]
    exact hbC.mul_left (f := fun g ↦ (η g)⁻¹)
  let φ : BruhatCompactSupport C𝔽(F) :=
    ⟨_, modulatedExponentialDecay_mem_bruhatSmooth m univ univ_nonempty (E B), hBs⟩
  have hη (k : C₁(F)) : η k.val = (γ k : ℂ) := by
    change (θ k.val : ℂ) * (((ideleClassNorm F k.val).val : ℝ) : ℂ) ^ shift(0, t) = _
    rw [show ideleClassNorm F k.val = 1 from k.property]
    simp [γ]
    rfl
  have hηne (g : C𝔽(F)) : η g ≠ 0 := ((Group.isUnit g).map η).ne_zero
  have hprod (g : C𝔽(F)) : φ.val g * η g = (b g : ℂ) := by
    change (E B).val g * η g = _
    rw [hEB, mul_right_comm, inv_mul_cancel₀ (hηne g), one_mul]
  refine ⟨φ, ?_, ?_, ?_⟩
  · change Continuous (E B).val
    rw [funext hEB]
    exact (η.continuous.inv₀ hηne).mul (Complex.continuous_ofReal.comp hb.continuous)
  · intro k g
    change (E B).val (k.val⁻¹ * g) = (γ k : ℂ) * (E B).val g
    obtain ⟨p, _, hp, _⟩ := hb.1.profile
    rw [hEB, hEB, map_mul, map_inv, mul_inv_rev, inv_inv, hη]
    have hbkg : b (k.val⁻¹ * g) = b g := by
      rw [hp, hp]
      change p (((ideleClassNorm F (k.val⁻¹ * g)).val : ℝ≥0) : ℝ) = _
      rw [map_mul, map_inv, show ideleClassNorm F k.val = 1 from k.property, inv_one, one_mul]
      rfl
    rw [hbkg]
    ring
  · simp_rw [hprod]
    rw [integral_complex_ofReal]
    apply Complex.ofReal_ne_zero.mpr
    exact (hb.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero hbc hb.1.nonneg
      (show b 1 ≠ 0 from (IsModulatedCutoff.apply_one (m := m) (ρ := b) hb.1 (by norm_num) (by norm_num)).trans_ne one_ne_zero)).ne'

/-- A continuous functional given by a character pairing is an eigenfunctional
for left translations, and integrating the orbit yields the test's multiplier. -/
private theorem spectralLine_wrongWeight_convolution {F : Type} [Field F] [NumberField F]
    {s : ℝ} (hs : 0 ≤ s) (η : QuasiCharacter C𝔽(F)) (Λ : StrongDual ℂ W(F, s))
    (hΛ : ∀ f : W(F, s), Λ f = ∫ g, f g * η g ∂μ𝔽(F)) :
    (∀ k : C𝔽(F), ∀ f : W(F, s), Λ (ρ(F, hs) k f) = η k * Λ f) ∧
    ∀ φ : BruhatCompactSupport C𝔽(F), ∀ f : W(F, s),
      Λ (hardySobolevTestAction (μ𝔽(F)) m𝔽(F) 0 0 s h₀ hs φ f) =
        (∫ g, φ.val g * η g ∂μ𝔽(F)) * Λ f := by
  have eig (k : C𝔽(F)) (f : W(F, s)) : Λ (ρ(F, hs) k f) = η k * Λ f := by
    have htr := hardySobolevTranslation_apply (μ𝔽(F)) m𝔽(F) 0 0 s h₀ hs k f
    rw [hΛ, hΛ, integral_congr_ae (htr.mono fun g hg ↦ congrArg (· * η g) hg)]
    calc
      _ = ∫ g, f g * η (k * g) ∂μ𝔽(F) := by
        rw [← integral_mul_left_eq_self (fun g ↦ f (k⁻¹ * g) * η g) k]
        simp only [inv_mul_cancel_left]
      _ = η k * ∫ g, f g * η g ∂μ𝔽(F) := by
        rw [← integral_const_mul]
        congr with g
        rw [map_mul]
        ring
  refine ⟨eig, fun φ f ↦ ?_⟩
  let τ := ρ(F, hs)
  have hτ := (exists_hardySobolevTranslation (μ𝔽(F)) m𝔽(F) 0 0 s h₀ hs).choose_spec.2
  have hp := bruhatRegularizedAction_apply (μ𝔽(F)) τ hτ φ f
  have he := congrArg (fun z : PettisWeakCompletion W(F, s) ↦
    (show Module.Dual ℂ (StrongDual ℂ W(F, s)) from z) Λ) hp.2
  change Λ (hardySobolevTestAction (μ𝔽(F)) m𝔽(F) 0 0 s h₀ hs φ f) =
    ∫ g, Λ (φ.val g • τ g f) ∂μ𝔽(F) at he
  rw [he, ← integral_mul_const]
  refine integral_congr_ae (.of_forall fun g ↦ ?_)
  change Λ (φ.val g • ρ(F, hs) g f) = φ.val g * η g * Λ f
  rw [map_smul, eig]
  simp only [smul_eq_mul, mul_assoc]

/-- A weighted Sobolev class representing a compactly supported Bruhat test. -/
private theorem spectralLine_wrongWeight_test_vector {F : Type} [Field F] [NumberField F]
    (φ : BruhatCompactSupport C𝔽(F)) (hc : Continuous φ.val) :
    ∃ f : W(F, 2), (f : C𝔽(F) → ℂ) =ᵐ[μ𝔽(F)] φ.val := by
  let d : C𝔽(F) → ℝ := fun g ↦ intervalSobolevDensity 0 0 2 (logNorm(F) g)
  let w := (μ𝔽(F)).withDensity (fun g ↦ ENNReal.ofReal (d g))
  have hd_eq (g : C𝔽(F)) : d g = 1 + logNorm(F) g ^ 2 := by
    norm_num [d, intervalSobolevDensity]
  have hd : Continuous d := by
    rw [funext hd_eq]
    exact continuous_const.add ((spectralLine_wrongWeight_log_continuous F).pow 2)
  have hp (g : C𝔽(F)) : 0 < d g := by rw [hd_eq]; positivity
  have hmem : MemLp φ.val 2 w := by
    apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    apply (integrable_withDensity_iff hd.measurable.ennreal_ofReal (ae_of_all _ fun _ ↦
      ENNReal.ofReal_lt_top)).2
    have hcont : Continuous (fun x ↦ ‖φ.val x‖ ^ 2 * d x) := (hc.norm.pow 2).mul hd
    have hpow : HasCompactSupport (fun x ↦ ‖φ.val x‖ ^ 2) :=
      φ.property.2.comp_left (g := fun z : ℂ ↦ ‖z‖ ^ 2) (by simp)
    have hcompact : HasCompactSupport (fun x ↦ ‖φ.val x‖ ^ 2 * d x) :=
      hpow.mul_right (f' := d)
    refine (hcont.integrable_of_hasCompactSupport hcompact).congr (ae_of_all _ fun x ↦ ?_)
    simp only [ENNReal.toReal_ofReal (hp x).le]
  have h_ac : μ𝔽(F) ≪ w := withDensity_absolutelyContinuous' hd.measurable.ennreal_ofReal.aemeasurable
    (ae_of_all _ fun x ↦ ENNReal.ofReal_ne_zero_iff.mpr (hp x))
  exact ⟨hmem.toLp φ.val, h_ac.ae_eq hmem.coeFn_toLp⟩

/-- At a zero of the continued completed L-function, every adelic zeta
transform vanishes on the same nontrivial norm-one component. -/
private theorem spectralLine_wrongWeight_zeta {F : Type} [Field F] [NumberField F]
    (θ : PontryaginDual C𝔽(F)) (k : C₁(F))
    (hk : (θ k.val : ℂ) ≠ (θ k.val : ℂ)⁻¹)
    (z : ℂ) (hz : 0 < meromorphicOrderAt (continuedCompletedHeckeL θ) z)
    (f : SchwartzBruhat (Multiplicative 𝔸[F])) :
    globalIdelicZFunction f (ideleClassNormTwist θ z) = 0 := by
  have hk1 : θ k.val ≠ 1 := by
    intro he
    exact hk (by rw [he]; simp)
  have hθ : θ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 := by
    intro he
    exact hk1 (DFunLike.congr_fun he k)
  have hrestrict (y : ℂ) : ideleClassNormTwist θ y k.val = (θ k.val : ℂ) := by
    change (θ k.val : ℂ) * (((ideleClassNorm F k.val).val : ℝ) : ℂ) ^ y = _
    rw [show ideleClassNorm F k.val = 1 from k.property]
    simp
  have hp₀ : ideleClassNormTwist θ z ≠ 1 := by
    intro he
    apply hk1
    apply Subtype.ext
    rw [← hrestrict, he]
    rfl
  have hp₁ : ideleClassNormTwist θ z ≠ ideleClassNormTwist (1 : PontryaginDual C𝔽(F)) 1 := by
    intro he
    apply hk1
    apply Subtype.ext
    rw [← hrestrict, he]
    change (1 : ℂ) * (((ideleClassNorm F k.val).val : ℝ) : ℂ) ^ (1 : ℂ) = _
    rw [show ideleClassNorm F k.val = 1 from k.property]
    simp
  let G := gaussianCompletedHeckeL θ
  let L := continuedCompletedHeckeL θ
  let c : ℂ := ((Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ : ℝ)
  obtain ⟨hL, hLe⟩ := continuedCompletedHeckeL_spec θ
  have hGdiff : Differentiable ℂ G :=
    globalIdelicZFunction_entire_of_nontrivial (adelicStandardGaussian θ) θ hθ
  have hLdiff : Differentiable ℂ L := completedHeckeL_continuation_entire θ L hL hLe hθ
  have hcL : Differentiable ℂ (fun w ↦ c * L w) :=
    (differentiable_const (c := c)).mul hLdiff
  have hGa : G = fun w ↦ c * L w := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr hGdiff).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hcL) (z₀ := (2 : ℂ))
    have hnhd : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hnhd] with w hw
    exact (gaussianCompletedHeckeL_eq_completedHeckeL θ w hw).trans
      (congrArg (c * ·) (hLe ⟨w, hw⟩).symm)
  have hLz : L z = 0 := by
    by_contra hne
    exact (ne_of_gt hz) ((hL (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mpr hne)
  obtain ⟨D, -, -, hD⟩ := adelicEigendistribution_normalized θ
  rw [hD z hp₀ hp₁ f, show gaussianCompletedHeckeL θ z = c * L z from congrFun hGa z,
    hLz, mul_zero, zero_mul]

/-- The zeroth jet at a zero of the completed L-function kills the closed
weighted theta subspace, by Mellin factorization on the dense polar-free tests. -/
private theorem spectralLine_wrongWeight_kernel {F : Type} [Field F] [NumberField F]
    (θ : PontryaginDual C𝔽(F)) (k : C₁(F))
    (hk : (θ k.val : ℂ) ≠ (θ k.val : ℂ)⁻¹)
    (a t : ℝ) (hz : 0 < meromorphicOrderAt (continuedCompletedHeckeL θ) (shift(a, t)))
    {s : ℝ} (hs : 0 ≤ s) (Λ : StrongDual ℂ W(F, s))
    (hΛ : ∀ f : W(F, s), Λ f = ∫ g, f g * ideleClassNormTwist θ (shift(0, t)) g ∂μ𝔽(F)) :
    ∀ f : W(F, s), f ∈ N(F, a, hs) → Λ f = 0 := by
  let E := (existsUnique_globalThetaSobolevEmbedding (F := F) a 0 0 s h₀ hs).exists.choose
  have hE := (existsUnique_globalThetaSobolevEmbedding (F := F) a 0 0 s h₀ hs).exists.choose_spec.2
  have hN : N(F, a, hs) ≤ Λ.ker := by
    apply Submodule.topologicalClosure_minimal _ _ Λ.isClosed_ker
    rintro v ⟨x, rfl⟩
    obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective
      ((LinearMap.ker (adelicThetaLinearMap F)).comap (adelePolarSubspace F).subtype) x
    have hweight (g : C𝔽(F)) :
        modulationWeight m𝔽(F) a (adelicTheta f.val) g * ideleClassNormTwist θ (shift(0, t)) g =
          adelicTheta f.val g * ideleClassNormTwist θ (shift(a, t)) g := by
      let r : ℝ := ((ideleClassNorm F g).val : ℝ)
      have hr : 0 < r := NNReal.coe_pos.mpr (Units.zero_lt _)
      change ((r ^ a : ℝ) : ℂ) * adelicTheta f.val g * ((θ g : ℂ) * (r : ℂ) ^ shift(0, t)) =
        adelicTheta f.val g * ((θ g : ℂ) * (r : ℂ) ^ shift(a, t))
      simp only [Complex.ofReal_zero, zero_add]
      rw [Complex.ofReal_cpow hr.le,
        Complex.cpow_add (a : ℂ) ((t : ℂ) * Complex.I) (Complex.ofReal_ne_zero.mpr hr.ne')]
      ring
    have hI : (fun g ↦ (E (Submodule.Quotient.mk f)) g * ideleClassNormTwist θ (shift(0, t)) g)
        =ᵐ[μ𝔽(F)] fun g ↦ adelicTheta f.val g * ideleClassNormTwist θ (shift(a, t)) g := by
      exact (hE f).mono fun g hg ↦ (congrArg (· * ideleClassNormTwist θ (shift(0, t)) g) hg).trans
        (hweight g)
    change Λ (E (Submodule.Quotient.mk f)) = 0
    rw [hΛ, integral_congr_ae hI]
    obtain ⟨h₁, h₂⟩ := (mem_adelePolarSubspace f.val).mp f.property
    change globalThetaMellinIntegral f.val (ideleClassNormTwist θ (shift(a, t))) = 0
    rw [globalThetaMellinIntegral_eq_continuation_of_vanishing _ h₁ h₂]
    exact spectralLine_wrongWeight_zeta θ k hk (shift(a, t)) hz _
  exact fun f hf ↦ hN hf

private theorem spectralLine_wrongWeight_range_of_zero {F : Type} [Field F] [NumberField F]
    (θ : PontryaginDual C𝔽(F)) (k : C₁(F))
    (hk : (θ k.val : ℂ) ≠ (θ k.val : ℂ)⁻¹)
    (a t : ℝ) (hz : 0 < (orderAt(F, θ, shift(a, t))).untop₀.toNat) :
    ¬ Printed.spectralLineConvolution_conjugateWeight_range := by
  classical
  intro hprinted
  let γ := θ.comp (restrictNormOne(F))
  let ω : PontryaginDual C₁(F) := γ⁻¹
  obtain ⟨χ₀, hχ₀⟩ := exists_spectralBasepointChoice F
  let χ (δ : PontryaginDual C₁(F)) := if δ = γ then θ else χ₀ δ
  have hχ : IsSpectralBasepointChoice χ := by
    intro δ
    by_cases h : δ = γ
    · subst δ
      rw [show χ γ = θ by exact ite_eq_left rfl]
    · rw [show χ δ = χ₀ δ by simp [χ, h]]
      exact hχ₀ δ
  have hχγ : χ γ = θ := ite_eq_left rfl
  have hs : (1 : ℝ) < 2 := by norm_num
  let j : SpectralLineJetIndex χ a 2 := ⟨(γ, t, 0), by
    rw [lt_spectralBoundaryMultiplicity]
    refine ⟨?_, by norm_num⟩
    change 0 < (orderAt(F, χ γ, shift(a, t))).untop₀.toNat
    rw [hχγ]
    exact hz⟩
  let η := ideleClassNormTwist θ (shift(0, t))
  have hjet (g : C𝔽(F)) : spectralZeroJet (χ j.val.1) 0 j.val.2.1 j.val.2.2 g = η g := by
    change spectralZeroJet (χ γ) 0 t 0 g = η g
    rw [hχγ, spectralZeroJet, pow_zero, mul_one]
  obtain ⟨Λ, hΛ, -⟩ := spectralLineJet_functional χ hs j
  have hΛeval (f : W(F, 2)) : Λ f = ∫ g, f g * η g ∂μ𝔽(F) := by
    simpa only [hjet] using (hΛ f).2
  let N := N(F, a, hs₀(hs))
  have hpos : 0 < orderAt(F, θ, shift(a, t)) := by
    have h := j.order_pos
    change 0 < orderAt(F, χ γ, shift(a, t)) at h
    rwa [hχγ] at h
  have hzero := spectralLine_wrongWeight_kernel θ k hk a t hpos hs₀(hs) Λ hΛeval
  obtain ⟨heig, hmult⟩ := spectralLine_wrongWeight_convolution hs₀(hs) η Λ hΛeval
  obtain ⟨φ, hφcont, hφ, hφne⟩ := spectralLine_wrongWeight_test θ t
  obtain ⟨f, hf⟩ := spectralLine_wrongWeight_test_vector φ hφcont
  have h_f : Λ f ≠ 0 := by
    rw [hΛeval, integral_congr_ae (hf.mono fun g hg ↦ congrArg (· * η g) hg)]
    exact hφne
  let P := spectralConvolution (F := F) a h₀ hs₀(hs) φ
  have hwrong : ∀ k : C₁(F), ∀ g, φ.val (k.val⁻¹ * g) = (ω⁻¹ k : ℂ) * φ.val g := by
    rw [show ω⁻¹ = γ from inv_inv γ]
    exact hφ
  obtain ⟨v, hv⟩ := hprinted F χ hχ a 2 hs ω φ hwrong
    (show P (N.mkQ f) ∈ range P from mem_range_self _)
  let T := hardySobolevTestAction (μ𝔽(F)) m𝔽(F) 0 0 2 h₀ hs₀(hs) φ
  have hpv : N.mkQ v.val = N.mkQ (T f) :=
    hv.trans (spectralConvolution_mkQ (F := F) a h₀ hs₀(hs) φ f)
  have hΛv : Λ v.val = Λ (T f) := by
    have h := hzero _ ((Submodule.Quotient.eq N).mp hpv)
    rwa [map_sub, sub_eq_zero] at h
  have hPv : Λ (T f) ≠ 0 := by
    change Λ (hardySobolevTestAction (μ𝔽(F)) m𝔽(F) 0 0 2 h₀ hs₀(hs) φ f) ≠ 0
    rw [hmult]
    exact mul_ne_zero hφne h_f
  apply hPv
  rw [← hΛv]
  have hinv : ρ(F, hs₀(hs)) k.val v.val = (ω k : ℂ) • v.val :=
    (mem_actionIsotype _ _ _).mp v.property k
  have he := heig k.val v.val
  rw [hinv, map_smul, smul_eq_mul] at he
  have hηk : η k.val = (θ k.val : ℂ) := by
    change (θ k.val : ℂ) * (((ideleClassNorm F k.val).val : ℝ) : ℂ) ^ shift(0, t) = _
    rw [show ideleClassNorm F k.val = 1 from k.property]
    simp
  have hωk : (ω k : ℂ) = (θ k.val : ℂ)⁻¹ := by
    change (((θ k.val)⁻¹ : Circle) : ℂ) = _
    simp
  rw [hηk, hωk] at he
  exact (mul_eq_mul_right_iff.mp he).resolve_left (Ne.symm hk)

-- The local evaluation uses the computation in Ch06_LocalGlobal/Sec2_Printed.lean.
open NumberFieldKB.Chebotarev.RatIdele in
/-- The idelic character of a Dirichlet character modulo 5, at the idele with `2` at the place
over 5 and `1` elsewhere, is the inverse of the character value at `2`. -/
private theorem rational_quartic_local_two
    (χ : DirichletCharacter ℂ 5) (v : Pl) (hv : pr v = 5) (u : (v.adicCompletion ℚ)ˣ)
    (hu : (u : v.adicCompletion ℚ) = ((2 : ℕ) : v.adicCompletion ℚ)) :
    ((ideleChar 5 χ (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) : ℂˣ) : ℂ) =
      (χ (2 : ZMod 5))⁻¹ := by
  have hval : Valued.v (u : v.adicCompletion ℚ) = WithZero.exp (-(0 : ℤ)) := by
    rw [neg_zero, WithZero.exp_zero, hu, ← Rat.cast_natCast, valued_ratCast,
      ← map_natCast (algebraMap (𝓞 ℚ) ℚ) 2,
      IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem, natCast_mem_asIdeal_iff, hv]
    norm_num
  have hq : ratPart (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = 1 := by
    rw [ratPart_ofAdicCompletion v u 0 hval, zpow_zero]
  have hU : unitPart (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) =
      IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u := by
    rw [unitPart_apply, hq, map_one, inv_one, mul_one]
  have hr : resMod 5 (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) = (2 : ZMod 5) := by
    rw [resMod_apply, resModFun, hU]
    refine (ZMod.equivPi 5 (NeZero.ne 5)).symm_apply_eq.mpr (funext fun q ↦ ?_)
    have hq5 : (q : ℕ) = 5 :=
      (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors q.2) Nat.prime_five).mp
        (Nat.dvd_of_mem_primeFactors q.2)
    have hqN : (q : ℕ) ^ (5 : ℕ).factorization q ∣ 5 := Nat.ordProj_dvd 5 q
    have hcomp : ZMod.equivPi 5 (NeZero.ne 5) (2 : ZMod 5) q =
        ZMod.castHom hqN (ZMod ((q : ℕ) ^ (5 : ℕ).factorization q)) (2 : ZMod 5) :=
      RingHom.congr_fun (Subsingleton.elim ((Pi.evalRingHom _ q).comp
        (ZMod.equivPi 5 (NeZero.ne 5)).toRingHom) (ZMod.castHom hqN _)) (2 : ZMod 5)
    rw [hcomp, map_ofNat]
    have hqv : placeP 5 q = v := pr_injective (by rw [placeP, pr_placeOf, hq5, hv])
    subst hqv
    rw [compV_ofAdicCompletion_self]
    erw [hu, redP_natCast]
    rfl
  rw [coe_ideleChar, MulChar.coe_toUnitHom, MonoidHom.coe_toHomUnits, hr]

/-- The rational idele class character induced by a quartic Dirichlet character modulo five
is nonreal on the norm-one class of the local unit two. -/
private theorem exists_ratNormOne_nonselfinverse_zero :
    ∃ (θ : PontryaginDual C𝔽(ℚ)) (k : (ideleClassNorm ℚ).ker),
      (θ k.val : ℂ) ≠ (θ k.val : ℂ)⁻¹ ∧
      ∃ z : ℂ, 0 < (meromorphicOrderAt (continuedCompletedHeckeL θ) z).untop₀.toNat := by
  classical
  let v5 : HeightOneSpectrum (𝓞 ℚ) := NumberFieldKB.Chebotarev.RatIdele.placeOf 5 Nat.prime_five
  have hv5 : NumberFieldKB.Chebotarev.RatIdele.pr v5 = 5 := NumberFieldKB.Chebotarev.RatIdele.pr_placeOf 5 Nat.prime_five
  -- Detecting 4 forces the image of 2 to have order four.
  obtain ⟨χ, hχ4⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (ZMod 5) ℂ
    (a := (4 : ZMod 5)) (by decide)
  obtain ⟨hprim, z, hzr, _, hz⟩ := dirichletFive_positiveOrder χ hχ4
  obtain ⟨ψ, _, hval, hf⟩ := DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq_with_values hprim
  have hψz : 0 < (meromorphicOrderAt (continuedCompletedHeckeL ψ) z).untop₀.toNat := by
    rw [← meromorphicOrderAt_finiteHeckeL_continuation ψ (meromorphic_dirichletLFunction χ)
      (fun s ↦ (_root_.DirichletCharacter.LFunction_eq_LSeries χ s.property).trans (hf s s.property).symm) hzr]
    exact hz
  have hval2 : Valued.v ((2 : ℕ) : v5.adicCompletion ℚ) = 1 := by
    rw [← Rat.cast_natCast, NumberFieldKB.Chebotarev.RatIdele.valued_ratCast,
      ← map_natCast (algebraMap (𝓞 ℚ) ℚ) 2,
      IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem,
      NumberFieldKB.Chebotarev.RatIdele.natCast_mem_asIdeal_iff, hv5]
    norm_num
  have h2ne : ((2 : ℕ) : v5.adicCompletion ℚ) ≠ 0 := fun e ↦ by
    rw [e, map_zero] at hval2
    exact zero_ne_one hval2
  let u2 : (v5.adicCompletion ℚ)ˣ := Units.mk0 _ h2ne
  have hu2v : Valued.v (u2 : v5.adicCompletion ℚ) = 1 := hval2
  let a := IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v5 u2
  have hmem : a ∈ (ideleClassNorm ℚ).ker := by
    rw [MonoidHom.mem_ker, ideleClassNorm_ofAdicCompletion]
    ext
    simpa using (Valued.toNormedField.norm_eq_one_iff.mpr hu2v)
  refine ⟨ψ, ⟨a, hmem⟩, ?_, z, hψz⟩
  have hev : (ψ a : ℂ) = (χ (2 : ZMod 5))⁻¹ :=
    (hval (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v5 u2)).trans
      (rational_quartic_local_two χ v5 hv5 u2 rfl)
  change (ψ a : ℂ) ≠ (ψ a : ℂ)⁻¹
  rw [hev, inv_inv]
  intro h
  have hn : χ (2 : ZMod 5) ≠ 0 := by
    exact (ZMod.isUnit_iff_coprime 2 5 |>.mpr (by decide)).map χ |>.ne_zero
  apply hχ4
  rw [show (4 : ZMod 5) = 2 * 2 by decide, map_mul]
  exact (congrArg (· * χ (2 : ZMod 5)) h.symm).trans (inv_mul_cancel₀ hn)

/-- Paper: Theorem 10.3.1.1(3), p. 449. For F = ℚ let the base character
θ be induced by a quartic Dirichlet character modulo 5.
Take s = 2, a+it a nontrivial zero of its completed L-function and
ω = (θ|C¹)⁻¹. Multiply the conjugate of θ(g)|g|^(it) by a nonzero
nonnegative smooth bump in log |g|. This test has left-translation weight
ω⁻¹. The zeroth jet function has weight ω, and the associated bilinear
functional detects the ω⁻¹-isotype. Its transpose eigenvalue is the positive
integral of the bump, and it annihilates the ω-isotype. See ERRATA.md F177. -/
theorem Printed.spectralLineConvolution_conjugateWeight_range_false :
    ¬ Printed.spectralLineConvolution_conjugateWeight_range := by
  obtain ⟨θ, k, hk, z, hz⟩ := exists_ratNormOne_nonselfinverse_zero
  apply spectralLine_wrongWeight_range_of_zero θ k hk z.re z.im
  rw [Complex.re_add_im]
  exact hz

end ConjugateWeightCounterexample

/-- Paper: Theorem 10.3.2.1(3), p. 454. A test of left-translation weight
ω⁻¹ is asserted to give an operator valued in the strip quotient isotype ω. -/
def Printed.spectralStripConvolution_conjugateWeight_range : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω) →
    ∀ (a α s : ℝ) (hα : 0 ≤ α) (hs : 1 < s)
      (ω : PontryaginDual C₁(F)) (φ : BruhatCompactSupport C𝔽(F)),
      (∀ k : C₁(F), ∀ g : C𝔽(F), φ.val (k.val⁻¹ * g) = (ω⁻¹ k : ℂ) * φ.val g) →
      range (spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ) ⊆
        range (fun v : Wω(F, -α, α, s, hStrip(hα), hs₀(hs), ω) ↦
          (globalThetaSobolev F a hStrip(hα) hs₀(hs)).mkQ v.val)

/-- Paper: Theorem 10.3.2.1(3), p. 454. Take F = ℚ, α = 1, s = 2 and
the primitive quartic character modulo 5 as in the line counterexample.
Choose a+it to be a nontrivial zero of its completed L-function, so the offset
b = 0 is interior. The same bump times the conjugate of θ(g)|g|^(it) acts
nontrivially on that zeroth jet, which annihilates the printed output isotype. -/
theorem Printed.spectralStripConvolution_conjugateWeight_range_false :
    ¬ Printed.spectralStripConvolution_conjugateWeight_range := by
  intro h
  apply Printed.spectralLineConvolution_conjugateWeight_range_false
  intro F _ _ χ hχ a s hs ω φ hφ
  let P (l : ℝ) (hl : l ≤ 0) : Prop :=
    range (spectralConvolution (F := F) a hl hs₀(hs) φ) ⊆
      range (fun v : Wω(F, l, 0, s, hl, hs₀(hs), ω) ↦
        (globalThetaSobolev F a hl hs₀(hs)).mkQ v.val)
  have transport (l : ℝ) (hl : l ≤ 0) (he : l = 0) (hp : P l hl) : P 0 le_rfl := by
    subst l
    exact hp
  exact transport _ _ (neg_zero : -(0 : ℝ) = 0) (h F χ hχ a 0 s le_rfl hs ω φ hφ)

/-- Paper: Theorem 10.3.1.1(3), p. 449. A test of conjugate weight is
claimed to act through the indicated isotype by a strongly nuclear operator.
The full trace is the sum in (10.3.1.5) with the floor in (10.3.1.4). -/
def Printed.spectralLineConvolution_conjugateWeight : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice (F := F) χ →
    ∀ (a s : ℝ) (hs : 1 < s) (ω : PontryaginDual C₁(F)) (φ : BruhatCompactSupport C𝔽(F)),
      (∀ k : C₁(F), ∀ g : C𝔽(F), φ.val (k.val⁻¹ * g) = (ω⁻¹ k : ℂ) * φ.val g) →
      let H := spectralSobolevQuotient F a h₀ hs₀(hs)
      let A := spectralConvolution (F := F) a h₀ hs₀(hs) φ
      let Z := {t : ℝ // 0 < orderAt(F, χ ω, shift(a, t))}
      let term (t : Z) := ((printedMultiplicity(F, χ ω, a, s, t.val) : ℕ) : ℂ) *
        mellinAt(F, φ, χ ω, shift(0, t.val))
      range A ⊆ range (fun v : Wω(F, 0, 0, s, h₀, hs₀(hs), ω) ↦
        (globalThetaSobolev F a h₀ hs₀(hs)).mkQ v.val) ∧
      IsStronglyNuclearBanachOperator (spectralIsotypeConvolution (F := F) a h₀ hs₀(hs) ω φ) ∧
      ∃ T : nuclearEndomorphisms H, T.val = A ∧ HasSum term (hilbertTrace T)

/-- Paper: Theorem 10.3.1.1(3), p. 449. The quartic character modulo five and
the bump in the range counterexample already contradict the first conjunct. -/
theorem Printed.spectralLineConvolution_conjugateWeight_false :
    ¬ Printed.spectralLineConvolution_conjugateWeight := by
  intro h
  apply Printed.spectralLineConvolution_conjugateWeight_range_false
  intro F _ _ χ hχ a s hs ω φ hφ
  exact (h F χ hχ a s hs ω φ hφ).1

/-- Paper: Theorem 10.3.2.1(3), p. 454. A test of conjugate weight is
claimed to act through the indicated isotype by a strongly nuclear operator.
Its full trace is (10.3.2.5), with the printed boundary and interior counts. -/
def Printed.spectralStripConvolution_conjugateWeight : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice (F := F) χ →
    ∀ (a α s : ℝ) (hα : 0 ≤ α) (hs : 1 < s)
      (ω : PontryaginDual C₁(F)) (φ : BruhatCompactSupport C𝔽(F)),
      (∀ k : C₁(F), ∀ g : C𝔽(F), φ.val (k.val⁻¹ * g) = (ω⁻¹ k : ℂ) * φ.val g) →
      let H := spectralSobolevQuotient F a hStrip(hα) hs₀(hs)
      let A := spectralConvolution (F := F) a hStrip(hα) hs₀(hs) φ
      let Z := {z : ℝ × ℝ // z.1 ∈ Icc (-α) α ∧ 0 < orderAt(F, χ ω, shift(a + z.1, z.2))}
      let term (z : Z) :=
        let b := z.val.1
        let t := z.val.2
        let n := (orderAt(F, χ ω, shift(a + b, t))).untop₀.toNat
        let count := if b = -α ∨ b = α then min n (Nat.floor ((s - 1) / 2 + 1)) else n
        (count : ℂ) * mellinAt(F, φ, χ ω, shift(b, t))
      range A ⊆ range (fun v : Wω(F, -α, α, s, hStrip(hα), hs₀(hs), ω) ↦
        (globalThetaSobolev F a hStrip(hα) hs₀(hs)).mkQ v.val) ∧
      IsStronglyNuclearBanachOperator (spectralIsotypeConvolution (F := F) a hStrip(hα) hs₀(hs) ω φ) ∧
      ∃ T : nuclearEndomorphisms H, T.val = A ∧ HasSum term (hilbertTrace T)

/-- Paper: Theorem 10.3.2.1(3), p. 454. At half-width one, the quartic
character modulo five gives the same contradiction at an interior zero. -/
theorem Printed.spectralStripConvolution_conjugateWeight_false :
    ¬ Printed.spectralStripConvolution_conjugateWeight := by
  intro h
  apply Printed.spectralStripConvolution_conjugateWeight_range_false
  intro F _ _ χ hχ a α s hα hs ω φ hφ
  exact (h F χ hχ a α s hα hs ω φ hφ).1

end RiemannMasullo
