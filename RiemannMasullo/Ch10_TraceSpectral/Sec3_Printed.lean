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
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.Real.Pi.Bounds
import RiemannMasullo.External.HardyCriticalLine.LowerIntegralBound
import RiemannMasullo.External.HardyCriticalLine.UpperIntegralBound
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
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

/-- Classical input: the number of distinct critical-line zeta ordinates up to height T,
divided by T, is unbounded. This follows from a positive proportion of distinct critical-line
zeros (Selberg 1942) and the Riemann–von Mangoldt count. Not a statement of the paper and not
a gap in it: a known theorem of which this project has no formal proof. It is the arithmetic
input for the refutation of (10.3.1.18), p. 451, which is proved from it by name. -/
private theorem spectralLineJet_rational_critical_zero_count (k : ℕ) :
    ∃ T : ℕ, ∃ S : Finset ℝ, (k + 1) * (T + 1) < S.card ∧
      ∀ t ∈ S, t ∈ Ioc (0 : ℝ) T ∧ riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 := by sorry

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
