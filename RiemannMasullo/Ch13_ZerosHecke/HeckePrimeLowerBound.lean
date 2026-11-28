module

public import RiemannMasullo.Ch13_ZerosHecke.HeckeRieszMellin
public import RiemannMasullo.Ch13_ZerosHecke.HeckeRieszZeroDetection
public import RiemannMasullo.ForMathlib.Probability.Moments.Landau
public import RiemannMasullo.Ch13_ZerosHecke.OneSidedRieszSampling
public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.PowerGrid

/-!
# Zero exclusion from a one-sided bound for the genuine Hecke first Riesz mean

The centered density may have either sign. Its meromorphic transform can only have
negative residues on the real axis inside the critical strip. Landau's theorem therefore
continues the actual integral as far as an integrable lower bound allows.
-/

@[expose] public noncomputable section

open Complex MeasureTheory NumberField Set Function Filter
open scoped NNReal Classical

namespace RiemannMasullo

variable {K : Type*} [Field K] [NumberField K]
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 K) K)

private theorem centeredRiesz_major_integrable (M b d : ℝ) (hd : b < d) :
    IntegrableOn (fun x : ℝ ↦ (M*x^(b-1)) * Real.exp (-d*Real.log x)) (Ioi 1) := by
  have hi := (integrableOn_Ioi_rpow_of_lt (show b-1-d < -1 by linarith) zero_lt_one).const_mul M
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hpos : 0 < x := zero_lt_one.trans hx
  change M*x^(b-1-d) = M*x^(b-1)*Real.exp (-d*Real.log x)
  rw [sub_eq_add_neg (b-1), Real.rpow_add hpos, Real.rpow_def_of_pos hpos (-d), mul_comm (Real.log x) (-d)]
  ring

private theorem hecke_no_right_zeros_of_density_minorant
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K))
    (χ : U) (hχ : ∀ t, χ (τ t) = 1) {b : ℝ} (hb : 1/2 ≤ b) (hb' : b ≤ 1)
    (g : ℝ → ℝ)
    (hlow : ∀ x : ℝ, 1 < x → -g x ≤ (heckeFirstRieszMean χ x).re/x^2-(if χ=1 then 1 else 0)/2)
    (hmajor : ∀ d > b, IntegrableOn (fun x : ℝ ↦ g x * Real.exp (-d * Real.log x)) (Ioi 1)) :
    ∀ p : ℂ, b < p.re → ¬ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) p := by
  classical
  let L := Classical.choose (finiteHeckeL_exists_continuation χ)
  let c : ℝ := if χ=1 then 1 else 0
  let f (x : ℝ) := (heckeFirstRieszMean χ x).re/x^2-c/2
  let μ := volume.restrict (Ioi (1 : ℝ))
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec
  obtain ⟨G, hG, hEuler, hreal⟩ := hecke_centeredRealRieszLogDeriv_real_germs τ hτ χ hχ
  have hf : Measurable f :=
    (((Complex.continuous_re.comp (continuous_heckeFirstRieszMean χ)).measurable.div
      (continuous_id.pow 2).measurable).sub measurable_const)
  have hT : (0 : ℝ → ℝ) ≤ᵐ[μ] Real.log := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.log_nonneg hx.le
  have hl : ∀ᵐ x ∂μ, -g x ≤ f x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hlow x hx
  have he (z : ℂ) (hz : 1 < z.re) : G z = ∫ x, (f x : ℂ)*Complex.exp (-z*Real.log x) ∂μ := by
    exact (hEuler hz).trans (heckeFirstRieszMean_centered_laplace χ L hL.1 hL.2 c hz).2.symm
  have hstart (d : ℝ) (hd : 1 < d) : Integrable (fun x ↦ f x * Real.exp (-d * Real.log x)) μ := by
    change IntegrableOn (fun x ↦ f x * Real.exp (-d * Real.log x)) (Ioi (1 : ℝ))
    have hi := (heckeFirstRieszMean_centered_laplace χ L hL.1 hL.2 c (s := (d:ℂ)) hd).1.re
    change IntegrableOn (fun x : ℝ ↦ ((f x : ℂ)*Complex.exp (-(d:ℂ)*(Real.log x : ℂ))).re) (Ioi 1) at hi
    simpa only [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_re] using hi
  obtain ⟨_, ha⟩ := landauLaplace_of_lower_bound_and_residues Real.measurable_log hT hf hl hb'
    hmajor hstart (F := G) (fun z _ ↦ hG.meromorphicOn z (mem_univ _)) he
    (fun x hx hx' ↦ hreal x (by linarith) hx')
  have hcrit := (hecke_centeredRealRieszLogDeriv_continuation_iff τ hτ χ hχ
    (a := b-1/2) (by linarith) (by linarith)).mp
  rw [sub_add_cancel] at hcrit
  apply hcrit
  exact ⟨_, ha, fun z hz ↦ (he z hz).symm.trans (hEuler hz)⟩

/-- A one-sided lower bound for the centered ideal sum excludes every zero strictly
to the right of the indicated vertical line, including nonreal zeros. -/
theorem hecke_no_right_zeros_of_firstRieszMean_lower
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K))
    (χ : U) (hχ : ∀ t, χ (τ t) = 1) {b : ℝ} (hb : 1/2 ≤ b) (hb' : b ≤ 1)
    (hlower : ∃ M : ℝ, ∀ x : ℝ, 1 < x →
      -(M*x^(1+b)) ≤ (heckeFirstRieszMean χ x).re - (if χ=1 then 1 else 0)*x^2/2) :
    ∀ p : ℂ, b < p.re → ¬ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) p := by
  classical
  obtain ⟨M, hM⟩ := hlower
  let c : ℝ := if χ=1 then 1 else 0
  apply hecke_no_right_zeros_of_density_minorant τ hτ χ hχ hb hb' (fun x ↦ M*x^(b-1)) _
    (centeredRiesz_major_integrable M b)
  intro x hx
  have hpos : 0 < x := zero_lt_one.trans hx
  have hpow : x^(b-1)*x^2 = x^(1+b) := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_add hpos]
    congr 1
    norm_num
    ring
  have h := hM x hx
  change -(M*x^(1+b)) ≤ (heckeFirstRieszMean χ x).re-c*x^2/2 at h
  change -(M*x^(b-1)) ≤ (heckeFirstRieszMean χ x).re/x^2 - c/2
  rw [le_sub_iff_add_le, le_div_iff₀ (sq_pos_of_pos hpos)]
  calc
    _ = -(M*x^(1+b)) + c*x^2/2 := by rw [← hpow]; ring
    _ ≤ _ := by linarith

private theorem centeredHeckeFirstRieszMean_lower_of_prime_samples (χ : U) {C c : ℝ} (hc : 0 ≤ c)
    (hs : ∀ᶠ j : ℕ in atTop, -(C*(j:ℝ)^6*Real.log (2*(j:ℝ)^4)) ≤
      degreeOnePrimeFirstRieszMean χ ((j:ℝ)^4)-c*((j:ℝ)^4)^2/2)
    {b : ℝ} (hb : 1/2 < b) :
    ∃ M : ℝ, ∀ x : ℝ, 1 < x → -(M*x^(1+b)) ≤ (heckeFirstRieszMean χ x).re - c*x^2/2 := by
  obtain ⟨A, hA, ha⟩ := degreeOnePrimeFirstRieszMean_lower_of_fourth_powers χ hc hs
  obtain ⟨B, _, hW⟩ := firstRieszSamplingWeight_le_rpow hb
  obtain ⟨E, herr⟩ := heckeFirstRieszMean_sub_prime_le
  let D : ℝ := Module.finrank ℚ K
  refine ⟨A*B+D*(abs E), fun x hx ↦ ?_⟩
  have hx' : 0 < x := by linarith
  have hD : 0 ≤ D := Nat.cast_nonneg _
  have he := herr K χ hx'.le
  have hre := (Complex.abs_re_le_norm _).trans he
  simp only [Complex.sub_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] at hre
  change |(heckeFirstRieszMean χ x).re-degreeOnePrimeFirstRieszMean χ x| ≤ D*x*(E*Real.sqrt x) at hre
  have hpow : x*Real.sqrt x ≤ x^(1+b) := by
    calc
      _ = x^((1:ℝ)+1/2) := by rw [Real.rpow_add hx', Real.rpow_one, Real.sqrt_eq_rpow]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
  have hrem : D*x*(E*Real.sqrt x) ≤ D*(abs E)*x^(1+b) := by
    calc
      _ ≤ D*x*((abs E)*Real.sqrt x) := by gcongr; exact le_abs_self E
      _ = (D*(abs E))*(x*Real.sqrt x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (mul_nonneg hD (abs_nonneg _))
  have h₁ := (abs_le.mp (hre.trans hrem)).1
  have h₂ := ha x hx.le
  have h₃ := mul_le_mul_of_nonneg_left (hW x hx.le) hA
  nlinarith only [h₁,h₂,h₃]

/-- A single eventual signed lower bound, sampled on the fourth powers for one
normalized character, puts its entire positive divisor on the critical line. -/
theorem critical_line_of_degreeOnePrimeFirstRieszMean_fourth_powers
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K))
    (χ : U) (hχ : ∀ t, χ (τ t) = 1)
    (hs : ∃ C : ℝ, ∀ᶠ j : ℕ in atTop, -(C*(j:ℝ)^6*Real.log (2*(j:ℝ)^4)) ≤
      degreeOnePrimeFirstRieszMean χ ((j:ℝ)^4)-(if χ=1 then 1 else 0)*((j:ℝ)^4)^2/2) :
    ∀ p : ℂ, 0 < MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ p → p.re = 1/2 := by
  obtain ⟨C, hC⟩ := hs
  apply (hecke_centeredRealRieszLogDeriv_iff_critical_line τ hτ χ hχ).mp
  have he := (hecke_centeredRealRieszLogDeriv_continuation_iff τ hτ χ hχ (a := 0) le_rfl (by norm_num)).mpr
  simp only [zero_add] at he
  apply he
  intro p hp hz
  have hL := (completedHeckeL_exists_continuation χ).choose_spec
  have hup := completedHeckeL_continuation_zeros χ _ hL.1 hL.2 (by linarith : 0 < p.re) hz
  let b := (p.re+1/2)/2
  have hb : 1/2 < b := by dsimp only [b]; linarith
  have hb' : b ≤ 1 := by dsimp only [b]; linarith
  have hc : 0 ≤ (if χ=1 then (1:ℝ) else 0) := by split <;> norm_num
  exact hecke_no_right_zeros_of_firstRieszMean_lower τ hτ χ hχ hb.le hb'
    (centeredHeckeFirstRieszMean_lower_of_prime_samples χ hc hC hb) p (by dsimp only [b]; linarith) hz

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

local notation "ord(" χ ", " p ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := K) χ) univ p

/-- The signed prime lower bound on fourth powers for each character suffices for the
actual exterior sum of Theorem 12.5.1.1 at every positive strip width. -/
theorem hasSum_exteriorZeros_of_degreeOnePrimeFirstRieszMean_fourth_powers
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K))
    (hs : ∀ χ : U, (∀ t, χ (τ t) = 1) → ∃ C : ℝ, ∀ᶠ j : ℕ in atTop,
      -(C*(j:ℝ)^6*Real.log (2*(j:ℝ)^4)) ≤
        degreeOnePrimeFirstRieszMean χ ((j:ℝ)^4)-(if χ=1 then 1 else 0)*((j:ℝ)^4)^2/2) :
    ∀ a : ℝ, 0 < a → ∀ φ : BruhatCompactSupport (IdeleClassGroup (𝓞 K) K),
      (∀ g : (ideleClassNorm K).ker, φ.val g = 0) →
      HasSum (fun z : {p : {χ : U // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
          0 < ord(p.1.val, p.2) ∧ a ≤ |p.2.re - 1/2|} ↦ (ord(z.val.1.val, z.val.2) : ℂ) *
        ∫ g, φ.val g * ideleClassNormTwist z.val.1.val (z.val.2 - 1/2) g
          ∂ideleClassTamagawaMeasure K) 0 := by
  apply (hasSum_exteriorZeros_iff_centeredRealRieszLogDeriv τ hτ).mpr
  exact fun χ hχ ↦ (hecke_centeredRealRieszLogDeriv_iff_critical_line τ hτ χ hχ).mpr
    (critical_line_of_degreeOnePrimeFirstRieszMean_fourth_powers τ hτ χ hχ (hs χ hχ))

/-- Absolute integrability of the negative part of the centered ideal sum excludes
every zero beyond the associated half-plane. Only the negative part is required
on the continuation side of the Euler line. -/
theorem hecke_no_right_zeros_of_firstRieszMean_negPart_integrable
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K))
    (χ : U) (hχ : ∀ t, χ (τ t) = 1) {b : ℝ} (hb : 1/2 ≤ b) (hb' : b ≤ 1)
    (hneg : ∀ d > b, IntegrableOn (fun x : ℝ ↦
      max (-((heckeFirstRieszMean χ x).re-(if χ=1 then 1 else 0)*x^2/2)) 0 * x^(-(d+2))) (Ioi 1)) :
    ∀ p : ℂ, b < p.re → ¬ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) p := by
  let c : ℝ := if χ=1 then 1 else 0
  let T (x : ℝ) := (heckeFirstRieszMean χ x).re-c*x^2/2
  let f (x : ℝ) := (heckeFirstRieszMean χ x).re/x^2-c/2
  apply hecke_no_right_zeros_of_density_minorant τ hτ χ hχ hb hb' (fun x ↦ max (-f x) 0)
    (fun x _ ↦ neg_le.mp (by exact le_max_left (-f x) 0)) _
  intro d hd
  apply (hneg d hd).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : 0 < x := zero_lt_one.trans hx
  have hf : -f x = (-T x)*(x^2)⁻¹ := by dsimp only [f,T]; field_simp
  have hw : Real.exp (-d*Real.log x) = x^(-d) := by rw [Real.rpow_def_of_pos hx', mul_comm]
  have hw' : (x^2)⁻¹*x^(-d) = x^(-(d+2)) := by
    rw [← Real.rpow_two x, ← Real.rpow_neg hx'.le, ← Real.rpow_add hx']
    congr 1
    ring
  change max (-T x) 0 * x^(-(d+2)) = max (-f x) 0 * Real.exp (-d*Real.log x)
  rw [hf, hw, ← hw', ← mul_assoc, max_mul_of_nonneg _ _ (inv_nonneg.mpr (sq_nonneg _)), zero_mul]

/-- The deficit is the negative part of the signed degree-one prime Riesz sum at a
fourth power, after subtraction of the principal main term. -/
def fourthPowerPrimeDeficit (χ : U) (j : ℕ) : ℝ :=
  let x := (j:ℝ)^4
  max (-(degreeOnePrimeFirstRieszMean χ x-(if χ=1 then 1 else 0)*x^2/2)) 0

private theorem heckeFirstRieszMean_negMoment_of_fourthPowerPrimeDeficit
    (χ : U) {d r : ℝ} (hd : 1/2 < d) (hr : 0 ≤ r) (hrt : r < 4*d+5)
    (hsum : (fun n : ℕ ↦ ∑ j ∈ Finset.Icc 1 n, fourthPowerPrimeDeficit χ j) =O[atTop]
      fun n ↦ (n:ℝ)^r) :
    IntegrableOn (fun x : ℝ ↦
      max (-((heckeFirstRieszMean χ x).re-(if χ=1 then 1 else 0)*x^2/2)) 0 * x^(-(d+2))) (Ioi 1) := by
  let c : ℝ := if χ=1 then 1 else 0
  let T (x : ℝ) := (heckeFirstRieszMean χ x).re-c*x^2/2
  let P (x : ℝ) := degreeOnePrimeFirstRieszMean χ x-c*x^2/2
  let q := (d+1/2)/2
  have hq : 1/2 < q := by dsimp only [q]; linarith
  have hqd : q < d := by dsimp only [q]; linarith
  obtain ⟨B, hB, hW⟩ := firstRieszSamplingWeight_le_rpow hq
  obtain ⟨E, herr⟩ := heckeFirstRieszMean_sub_prime_le
  let D : ℝ := Module.finrank ℚ K
  have hD : 0 ≤ D := Nat.cast_nonneg _
  let M := 1125*D*B+D*|E|
  have hInt : IntegrableOn (fun x : ℝ ↦ (M*x^(1+q))*x^(-(d+2))) (Ioi 1) := by
    have h := (integrableOn_Ioi_rpow_of_lt (show (1+q)+(-(d+2)) < -1 by linarith) zero_lt_one).const_mul M
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.rpow_add (zero_lt_one.trans hx)]
    ring
  have hT : Measurable T := (((Complex.continuous_re.comp (continuous_heckeFirstRieszMean χ)).sub
    ((continuous_const.mul (continuous_id.pow 2)).div_const 2)).measurable)
  have hA (j : ℕ) : 0 ≤ fourthPowerPrimeDeficit χ j := le_max_right _ _
  change IntegrableOn (fun x : ℝ ↦ max (-T x) 0 * x^(-(d+2))) (Ioi 1)
  apply integrableOn_Ioi_negPart_mul_rpow_of_powerGrid_sum (m := 4) (by decide) (by linarith) hr (by norm_num; linarith)
    hT (by fun_prop) hA hInt _ hsum
  intro j hj x hx
  have hc : 0 ≤ c := by dsimp [c]; split <;> norm_num
  have hj₁ : (1:ℝ) ≤ j := by exact_mod_cast hj
  have hx₁ : 1 ≤ x := (one_le_pow₀ hj₁ (n := 4)).trans hx.1.le
  have hx' : 0 < x := zero_lt_one.trans_le hx₁
  have hp := degreeOnePrimeFirstRieszMean_neg_le_fourth_endpoints χ hc hj hx.1.le hx.2
  have ha₁ : -P ((j:ℝ)^4) ≤ fourthPowerPrimeDeficit χ j := le_max_left _ _
  have ha₂ : -P (((j:ℝ)+1)^4) ≤ fourthPowerPrimeDeficit χ (j+1) := by
    simpa only [fourthPowerPrimeDeficit, Nat.cast_add, Nat.cast_one, P, c] using
      (le_max_left (-P (((j:ℝ)+1)^4)) 0)
  have ha : max (-P ((j:ℝ)^4)) (-P (((j:ℝ)+1)^4)) ≤
      fourthPowerPrimeDeficit χ j+fourthPowerPrimeDeficit χ (j+1) :=
    max_le (by linarith [hA (j+1)]) (by linarith [hA j])
  change -P x ≤ max (-P ((j:ℝ)^4)) (-P (((j:ℝ)+1)^4)) + 1125*D*((x*Real.sqrt x)*Real.log (2*x)) at hp
  have hrem := (Complex.abs_re_le_norm _).trans (herr K χ hx'.le)
  simp only [Complex.sub_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] at hrem
  change |(heckeFirstRieszMean χ x).re-degreeOnePrimeFirstRieszMean χ x| ≤ D*x*(E*Real.sqrt x) at hrem
  have hpow : x*Real.sqrt x ≤ x^(1+q) := by
    calc
      _ = x^((1:ℝ)+1/2) := by rw [Real.rpow_add hx', Real.rpow_one, Real.sqrt_eq_rpow]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx₁ (by linarith)
  have h₁ : D*x*(E*Real.sqrt x) ≤ D*(abs E)*x^(1+q) := by
    calc
      _ ≤ D*x*((abs E)*Real.sqrt x) := by gcongr; exact le_abs_self E
      _ = (D*(abs E))*(x*Real.sqrt x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (mul_nonneg hD (abs_nonneg _))
  have h₂ := (abs_le.mp (hrem.trans h₁)).1
  have h₃ := mul_le_mul_of_nonneg_left (hW x hx₁) (mul_nonneg (by norm_num : (0:ℝ) ≤ 1125) hD)
  have ht : -T x ≤ -P x+D*(abs E)*x^(1+q) := by dsimp only [T,P]; linarith
  dsimp only [M]
  nlinarith only [hp,ha,ht,h₃]

/-- A growth exponent for the cumulative prime deficits bounds the real parts of
the zeros of the corresponding character. -/
theorem hecke_no_right_zeros_of_fourthPowerPrimeDeficit_growth
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K))
    (χ : U) (hχ : ∀ t, χ (τ t) = 1) {b : ℝ} (hb : 1/2 ≤ b) (hb' : b ≤ 1)
    (h : ∀ ε : ℝ, 0 < ε → (fun n : ℕ ↦ ∑ j ∈ Finset.Icc 1 n, fourthPowerPrimeDeficit χ j) =O[atTop]
      fun n ↦ (n:ℝ)^(4*b+5+ε)) :
    ∀ p : ℂ, b < p.re → ¬ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) p := by
  apply hecke_no_right_zeros_of_firstRieszMean_negPart_integrable τ hτ χ hχ hb hb'
  intro d hd
  let ε := 2*(d-b)
  have hε : 0 < ε := by dsimp only [ε]; linarith
  apply heckeFirstRieszMean_negMoment_of_fourthPowerPrimeDeficit χ (hb.trans_lt hd) _ _ (h ε hε)
  · linarith
  · dsimp only [ε]
    linarith

/-- A cumulative deficit of order `Oε(J^(7+ε))` for every normalized character
implies the complete exterior sum of Theorem 12.5.1.1 for every positive width. -/
theorem hasSum_exteriorZeros_of_fourthPowerPrimeDeficit_growth
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K))
    (h : ∀ χ : U, (∀ t, χ (τ t) = 1) → ∀ ε : ℝ, 0 < ε →
      (fun n : ℕ ↦ ∑ j ∈ Finset.Icc 1 n, fourthPowerPrimeDeficit χ j) =O[atTop]
        fun n ↦ (n:ℝ)^(7+ε)) :
    ∀ a : ℝ, 0 < a → ∀ φ : BruhatCompactSupport (IdeleClassGroup (𝓞 K) K),
      (∀ g : (ideleClassNorm K).ker, φ.val g = 0) →
      HasSum (fun z : {p : {χ : U // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
          0 < ord(p.1.val, p.2) ∧ a ≤ |p.2.re - 1/2|} ↦ (ord(z.val.1.val, z.val.2) : ℂ) *
        ∫ g, φ.val g * ideleClassNormTwist z.val.1.val (z.val.2 - 1/2) g
          ∂ideleClassTamagawaMeasure K) 0 := by
  apply (hasSum_exteriorZeros_iff_centeredRealRieszLogDeriv τ hτ).mpr
  intro χ hχ
  have hcrit := (hecke_centeredRealRieszLogDeriv_continuation_iff τ hτ χ hχ (a := 0) le_rfl (by norm_num)).mpr
  simp only [zero_add] at hcrit
  apply hcrit
  apply hecke_no_right_zeros_of_fourthPowerPrimeDeficit_growth τ hτ χ hχ le_rfl (by norm_num)
  intro ε hε
  norm_num
  exact h χ hχ ε hε

/-- A hypothetical zero strictly to the right of the critical line forces large
cumulative deficits of the genuine prime sums at arbitrarily large fourth-power indices. -/
theorem frequently_fourthPowerPrimeDeficit_sum_gt_of_right_zero
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K))
    (χ : U) (hχ : ∀ t, χ (τ t) = 1) {p : ℂ} (hp : 1/2 < p.re)
    (hz : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) p) {r : ℝ}
    (hr : 0 ≤ r) (hrp : r < 4*p.re+5) (C : ℝ) :
    ∃ᶠ n : ℕ in atTop, C*(n:ℝ)^r < ∑ j ∈ Finset.Icc 1 n, fourthPowerPrimeDeficit χ j := by
  by_contra h
  have he := not_frequently.mp h
  simp only [not_lt] at he
  have ho : (fun n : ℕ ↦ ∑ j ∈ Finset.Icc 1 n, fourthPowerPrimeDeficit χ j) =O[atTop]
        fun n ↦ (n:ℝ)^r := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [he] with n hn
    rw [Real.norm_of_nonneg (show 0 ≤ ∑ j ∈ Finset.Icc 1 n, fourthPowerPrimeDeficit χ j from
      Finset.sum_nonneg (fun j _ ↦ le_max_right _ _)),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    exact hn
  let b := (p.re+max (1/2) ((r-5)/4))/2
  have hmax : max (1/2) ((r-5)/4) < p.re := max_lt hp (by linarith)
  have hb : 1/2 ≤ b := by dsimp only [b]; linarith [le_max_left (1/2 : ℝ) ((r-5)/4)]
  have hbp : b < p.re := by dsimp only [b]; linarith
  have hrb : r < 4*b+5 := by dsimp only [b]; linarith [le_max_right (1/2 : ℝ) ((r-5)/4)]
  have hL := (completedHeckeL_exists_continuation χ).choose_spec
  have hp' := completedHeckeL_continuation_zeros χ _ hL.1 hL.2 (by linarith : 0 < p.re) hz
  apply hecke_no_right_zeros_of_firstRieszMean_negPart_integrable τ hτ χ hχ hb (hbp.le.trans hp'.le) _ p hbp hz
  intro d hd
  exact heckeFirstRieszMean_negMoment_of_fourthPowerPrimeDeficit χ (hb.trans_lt hd) hr (by linarith) ho

end RiemannMasullo
