module

public import RiemannMasullo.Ch13_ZerosHecke.HeckeRieszMellin
public import RiemannMasullo.Ch13_ZerosHecke.HeckeRieszZeroDetection
public import RiemannMasullo.ForMathlib.Probability.Moments.Landau
public import RiemannMasullo.Ch13_ZerosHecke.OneSidedRieszSampling

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
  let L := Classical.choose (finiteHeckeL_exists_continuation χ)
  let c : ℝ := if χ=1 then 1 else 0
  let f (x : ℝ) := (heckeFirstRieszMean χ x).re/x^2-c/2
  let μ := volume.restrict (Ioi (1 : ℝ))
  let g (x : ℝ) := M*x^(b-1)
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec
  obtain ⟨G, hG, hEuler, hreal⟩ := hecke_centeredRealRieszLogDeriv_real_germs τ hτ χ hχ
  have hf : Measurable f :=
    (((Complex.continuous_re.comp (continuous_heckeFirstRieszMean χ)).measurable.div
      (continuous_id.pow 2).measurable).sub measurable_const)
  have hT : (0 : ℝ → ℝ) ≤ᵐ[μ] Real.log := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.log_nonneg hx.le
  have hlow : ∀ᵐ x ∂μ, -g x ≤ f x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
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
  have he (z : ℂ) (hz : 1 < z.re) : G z = ∫ x, (f x : ℂ)*Complex.exp (-z*Real.log x) ∂μ := by
    exact (hEuler hz).trans (heckeFirstRieszMean_centered_laplace χ L hL.1 hL.2 c hz).2.symm
  have hstart (d : ℝ) (hd : 1 < d) : Integrable (fun x ↦ f x * Real.exp (-d * Real.log x)) μ := by
    change IntegrableOn (fun x ↦ f x * Real.exp (-d * Real.log x)) (Ioi (1 : ℝ))
    have hi := (heckeFirstRieszMean_centered_laplace χ L hL.1 hL.2 c (s := (d:ℂ)) hd).1.re
    change IntegrableOn (fun x : ℝ ↦ ((f x : ℂ)*Complex.exp (-(d:ℂ)*(Real.log x : ℂ))).re) (Ioi 1) at hi
    simpa only [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_re] using hi
  obtain ⟨_, ha⟩ := landauLaplace_of_lower_bound_and_residues Real.measurable_log hT hf hlow hb'
    (centeredRiesz_major_integrable M b) hstart (F := G) (fun z _ ↦ hG.meromorphicOn z (mem_univ _)) he
    (fun x hx hx' ↦ hreal x (by linarith) hx')
  have hcrit := (hecke_centeredRealRieszLogDeriv_continuation_iff τ hτ χ hχ
    (a := b-1/2) (by linarith) (by linarith)).mp
  rw [sub_add_cancel] at hcrit
  apply hcrit
  exact ⟨_, ha, fun z hz ↦ (he z hz).symm.trans (hEuler hz)⟩

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

end RiemannMasullo
