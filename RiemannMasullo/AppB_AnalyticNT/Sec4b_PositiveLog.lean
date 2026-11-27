module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b
public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # The explicit formula on the positive logarithmic axis

For a smooth test supported in positive log norm the finite terms of
Theorem B.4.2.2 sample only positive prime powers. Its infinite terms become
ordinary integrals with one kernel per real or complex place. The uncentered
bilateral Laplace transform pairs directly with the signed Hecke divisor.
-/

@[expose] public noncomputable section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NumberField.AdeleRing SchwartzMap Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "V(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "U(" F ")" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "q(" v ")" => (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℝ)
local notation "χ₀(" χ ")" => ideleClassNormTwist χ 0
local notation "tilt(" G ")" => (fun x : ℝ ↦ (G : ℝ → ℂ) x * Complex.exp ((x : ℂ) / 2))

/-- The contribution at a positive power of an unramified prime ideal. -/
def positiveLogPrimeTerm (χ : U(F)) (G : ℝ → ℂ) (j : V(F) × ℕ) : ℂ :=
  if χ₀(χ).IsUnramifiedAt j.1 then
    (Real.log q(j.1) : ℂ) * (χ₀(χ).localValue j.1) ^ (j.2 + 1) *
      G (((j.2 + 1 : ℕ) : ℝ) * Real.log q(j.1))
  else 0

/-- The one-sided gamma integral at scale `k` and local parameter `d`. -/
def positiveLogGammaIntegral (k : ℝ) (d : ℂ) (G : ℝ → ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), G x * Complex.exp (-d * (x : ℂ)) / (1 - (Real.exp (-x / k) : ℂ))

/-- The real or complex positive-log integral for the local component of `χ`. -/
def positiveLogArchTerm (χ : U(F)) (G : ℝ → ℂ) (w : InfinitePlace F) : ℂ :=
  if hw : w.IsReal then
    let p := (realHeckeCharacter_parameters χ w hw).exists.choose
    positiveLogGammaIntegral (1 / 2) (p.1 + p.2.val) G
  else
    let p := (complexHeckeCharacter_parameters χ w
      (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
    positiveLogGammaIntegral 1 (p.1 + (p.2.natAbs : ℂ) / 2) G

private theorem positiveLog_zero {G : ℝ → ℂ} (hs : tsupport G ⊆ Ioi 0) {x : ℝ} (hx : x ≤ 0) :
    G x = 0 := by
  by_contra hn
  exact (not_lt_of_ge hx) (hs (subset_tsupport _ hn))

private theorem positiveLog_mellin (G : ℝ → ℂ) (z : ℂ) :
    mellin (fun r : ℝ ↦ tilt(G) (Real.log r)) (z - 1 / 2) = bilateralLaplace G z := by
  rw [mellin, ← integral_comp_exp, bilateralLaplace]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, Complex.ofReal_exp]
  calc
    _ = G x * (Complex.exp x * Complex.exp ((x : ℂ) * (z - 1 / 2 - 1)) *
        Complex.exp ((x : ℂ) / 2)) := by ring
    _ = _ := by rw [← Complex.exp_add, ← Complex.exp_add]; congr 2; ring

private theorem positiveLog_gamma {G : ℝ → ℂ} (hs : tsupport G ⊆ Ioi 0)
    {k : ℝ} (hk : 0 < k) (d zMinus : ℂ) :
    (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel k ((k : ℂ) * (1 / 2 + d))
      zMinus tilt(G) t) = -positiveLogGammaIntegral k d G := by
  let A (x : ℝ) := G x * Complex.exp (-d * (x : ℂ)) / (1 - (Real.exp (-x / k) : ℂ))
  have he (t : ℝ) : Complex.exp (((k * t : ℝ) : ℂ) / 2) *
      Complex.exp (-((k : ℂ) * (1 / 2 + d)) * (t : ℂ)) =
        Complex.exp (-d * ((k * t : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; push_cast; congr 1; ring
  have h (t : ℝ) (ht : t ∈ Ioi 0) : heckeArchimedeanDigammaKernel k
      ((k : ℂ) * (1 / 2 + d)) zMinus tilt(G) t = -(k • A (k * t)) := by
    have hn := positiveLog_zero hs (neg_nonpos.mpr (mul_pos hk (show 0 < t from ht)).le)
    simp only [heckeArchimedeanDigammaKernel, positiveLog_zero hs (x := 0) le_rfl, hn,
      zero_mul, mul_zero, zero_div, add_zero, zero_sub, mul_assoc, he, A, Complex.real_smul,
      show -(k * t) / k = -t by field_simp]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h, integral_neg, integral_smul,
    integral_comp_mul_left_Ioi' A 0 hk, mul_zero, positiveLogGammaIntegral]

private theorem positiveLog_prime {G : ℝ → ℂ} (hs : tsupport G ⊆ Ioi 0) (χ : U(F))
    (j : V(F) × ℕ) :
    (if χ₀(χ).IsUnramifiedAt j.1 then
      let x := ((j.2 + 1 : ℕ) : ℝ) * Real.log q(j.1)
      (Real.log q(j.1) * Real.exp (-x / 2) : ℝ) *
        (χ₀(χ).localValue j.1 ^ (j.2 + 1) * tilt(G) x +
         χ₀(χ⁻¹).localValue j.1 ^ (j.2 + 1) * tilt(G) (-x))
     else 0) = positiveLogPrimeTerm χ G j := by
  unfold positiveLogPrimeTerm
  split_ifs with hj
  · let x := ((j.2 + 1 : ℕ) : ℝ) * Real.log q(j.1)
    have hx : 0 < x := mul_pos (by positivity) (Real.log_pos (by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm j.1))
    have hn := positiveLog_zero hs (neg_nonpos.mpr hx.le)
    change _ * (_ * (G x * _) + _ * (G (-x) * _)) = _ * _ * G x
    rw [hn, zero_mul, mul_zero, add_zero]
    change ((Real.log q(j.1) * Real.exp (-x / 2) : ℝ) : ℂ) *
      (χ₀(χ).localValue j.1 ^ (j.2 + 1) * (G x * Complex.exp ((x : ℂ) / 2))) = _
    simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
      Complex.ofReal_ofNat]
    have he : Complex.exp (-(x : ℂ) / 2) * Complex.exp ((x : ℂ) / 2) = 1 := by
      rw [← Complex.exp_add, show -(x : ℂ) / 2 + x / 2 = 0 by ring, Complex.exp_zero]
    linear_combination (Real.log q(j.1) : ℂ) * χ₀(χ).localValue j.1 ^ (j.2 + 1) * G x * he
  · rfl

private theorem positiveLog_schwartz (G : ℝ → ℂ) (hG : ContDiff ℝ (∞) G) (hc : HasCompactSupport G) :
    ∃ f : 𝓢(ℝ, ℂ), (f : ℝ → ℂ) = tilt(G) ∧ ExponentialDecay f := by
  have htilt : HasCompactSupport tilt(G) := hc.mul_right
  have hdiff : ContDiff ℝ (∞) tilt(G) := hG.mul
    (Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.div_const _))
  let f := htilt.toSchwartzMap hdiff
  refine ⟨f, rfl, ?_⟩
  have hder (j : ℕ) : iteratedDeriv j (f : ℝ → ℂ) =ᶠ[cocompact ℝ] 0 := by
    have hj := htilt.iteratedFDeriv (𝕜 := ℝ) j
    rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact] at hj
    filter_upwards [hj] with x hx
    rw [iteratedDeriv_eq_iteratedFDeriv]
    change (iteratedFDeriv ℝ j tilt(G) x) _ = _
    rw [hx]
    rfl
  exact ⟨fun j _ _ ↦ ((hder j).filter_mono atTop_le_cocompact).trans_isBigO
    (Asymptotics.isBigO_zero _ _), fun j _ _ ↦ ((hder j).filter_mono atBot_le_cocompact).trans_isBigO
    (Asymptotics.isBigO_zero _ _)⟩

/-- Paper: Proposition B.2.1.9(4), p. 599. A smooth compact positive-log
profile has arbitrarily rapid height decay on any closed left half-plane. -/
theorem bilateralLaplace_positiveLog_heightBound (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H)
    (hc : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0) (b : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∃ K > 0, ∀ z : ℂ, z.re ≤ b → z.im ≠ 0 → ‖bilateralLaplace H z‖ ≤ K / |z.im| ^ n := by
  obtain ⟨f, hf, hdec⟩ := positiveLog_schwartz H hH hc
  have hsup : tsupport (f : ℝ → ℂ) ⊆ Ioi 0 := by
    rw [hf]
    exact tsupport_mul_subset_left.trans hp
  obtain ⟨K, hK, h⟩ := mellin_heightBound_left_of_exponentialDecay f hdec hsup (b - 1 / 2) n hn
  refine ⟨K, hK, fun z hz hy ↦ ?_⟩
  have hv := h (z.re - 1 / 2) (sub_le_sub_right hz _) z.im hy
  have he : ((z.re - 1 / 2 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I = z - 1 / 2 := by
    apply Complex.ext <;> simp
  change ‖mellin (fun r : ℝ ↦ f (Real.log r)) (((z.re - 1 / 2 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I)‖ ≤ _ at hv
  rw [he, hf, positiveLog_mellin] at hv
  exact hv

/-- Paper: Theorem B.4.2.2, p. 616. For a compact smooth profile on the positive
logarithmic axis, the signed Hecke divisor equals minus the uncentered prime-power
sum minus the one-sided gamma integrals. This includes the shifted poles of norm
characters with their signed orders. -/
theorem hasSum_heckeExplicitFormula_positiveLog (χ : U(F)) (G : ℝ → ℂ)
    (hG : ContDiff ℝ (∞) G) (hc : HasCompactSupport G) (hs : tsupport G ⊆ Ioi 0)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (ha : ∀ s : Complex.re ⁻¹' Ioi (1 : ℝ), L s = completedHeckeL χ s) :
    HasSum (fun z : ℂ ↦ (MeromorphicOn.divisor L univ z : ℂ) *
      bilateralLaplace G z)
      (-(∑' j, positiveLogPrimeTerm χ G j) - ∑ w, positiveLogArchTerm χ G w) := by
  obtain ⟨f, hf, hdec⟩ := positiveLog_schwartz G hG hc
  have h := hasSum_heckeExplicitFormula χ f hdec _ hL ha
  rw [hf] at h
  simp only [positiveLog_mellin, positiveLog_zero hs (x := 0) le_rfl, zero_mul, mul_zero,
    zero_sub, sub_zero] at h
  simp_rw [positiveLog_prime hs] at h
  convert h using 1
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  unfold positiveLogArchTerm
  split_ifs with hw
  · let p := (realHeckeCharacter_parameters χ w hw).exists.choose
    have he : (1 / 2 + p.1 + (p.2.val : ℂ)) / 2 =
        (((1 / 2 : ℝ) : ℂ) * (1 / 2 + (p.1 + p.2.val))) := by push_cast; ring
    rw [he, positiveLog_gamma hs (by norm_num : (0 : ℝ) < 1 / 2)]
  · let p := (complexHeckeCharacter_parameters χ w
      (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
    have he : 1 / 2 + p.1 + (p.2.natAbs : ℂ) / 2 =
        (((1 : ℝ) : ℂ) * (1 / 2 + (p.1 + (p.2.natAbs : ℂ) / 2))) := by push_cast; ring
    rw [he, positiveLog_gamma hs zero_lt_one]

end RiemannMasullo
