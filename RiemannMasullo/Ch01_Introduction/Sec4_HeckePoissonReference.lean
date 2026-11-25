module

public import RiemannMasullo.Ch01_Introduction.Sec4_HeckePoissonMass
public import RiemannMasullo.AppB_AnalyticNT.Sec6
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.LogDivSquareTail
import Mathlib.Tactic

/-! # A finite prime-power reference for the completed Hecke mass at two -/

@[expose] public noncomputable section

open Complex Filter NumberField Set Topology

namespace RiemannMasullo.HeckePoisson

variable {F : Type*} [Field F] [NumberField F]
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "H₁" => Complex.re ⁻¹' Ioi (1 : ℝ)

/-- Archimedean, conductor, and principal-pole terms of the reference at two. -/
def referenceConstantTwo (χ : U) : ℝ := by
  classical
  exact heckeLogDiscriminantConductor χ / 2 + (logDeriv (heckeGammaFactor χ) 2).re +
    if χ = 1 then 3 / 2 else 0

/-- The Euler contribution at integral ideal norm `m`. -/
def logDerivativeTermTwo (χ : U) (m : ℕ) : ℝ :=
  (heckeLogDerivCoefficient (ideleClassNormTwist χ 0) m).re / (m : ℝ)^2

/-- A finite arithmetic reference, including the norm-`N` coefficient. -/
def finiteReferenceTwo (χ : U) (N : ℕ) : ℝ :=
  referenceConstantTwo χ - ∑ m ∈ Finset.range (N + 1), logDerivativeTermTwo χ m

private theorem hasSum_logDerivativeCoefficients_two (χ : U) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (he : ∀ s : H₁, L s = finiteHeckeL χ s) :
    HasSum (fun m : ℕ ↦ heckeLogDerivCoefficient (ideleClassNormTwist χ 0) m / (m : ℂ)^2)
      (-logDeriv L 2) := by
  classical
  let J := {I : Ideal (𝓞 F) // I ≠ ⊥}
  have hf : HasSum (fun I : J ↦ heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val /
      (I.val.absNorm : ℂ)^2) (-logDeriv L 2) := by
    have h := (finiteHeckeL_logDeriv_hasSum_ideals χ L hL he ⟨2, by norm_num⟩).2.2.neg
    simpa only [neg_div, neg_neg, cpow_two] using h
  refine (hf.tsum_fiberwise (fun I : J ↦ I.val.absNorm)).congr_fun fun m ↦ ?_
  let S := {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m}
  have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = m}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) m).subset fun _ h ↦ h.2
  have : Finite S := hfin.to_subtype
  let : Fintype S := Fintype.ofFinite _
  let e : ↑((fun I : J ↦ I.val.absNorm) ⁻¹' {m}) ≃ S :=
    { toFun := fun b ↦ ⟨b.val.val, b.val.property, b.property⟩
      invFun := fun I ↦ ⟨⟨I.val, I.property.1⟩, I.property.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [← e.symm.tsum_eq, tsum_fintype, heckeLogDerivCoefficient,
    finsum_eq_sum_of_fintype, Finset.sum_div]
  refine Finset.sum_congr rfl fun I _ ↦ ?_
  change _ = _ / ((I.val.absNorm : ℕ) : ℂ)^2
  rw [I.property.2]
  rfl

/-- The real prime-power series gives the difference between the explicit constant
and the full logarithmic-derivative mass, for every character. -/
theorem hasSum_logDerivativeTermTwo (χ : U) :
    HasSum (logDerivativeTermTwo χ) (referenceConstantTwo χ - logDerivativeMass χ 2 0) := by
  classical
  obtain ⟨L, hL, he⟩ := finiteHeckeL_exists_continuation χ
  have hp : 1 < (2 : ℂ).re := by norm_num
  have hloc : continuedCompletedHeckeL χ =ᶠ[𝓝 (2 : ℂ)] (fun z ↦ heckeGammaFactor χ z * L z) := by
    filter_upwards [(isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hp] with z hz
    rw [(continuedCompletedHeckeL_spec χ).2 ⟨z, hz⟩, he ⟨z, hz⟩]
    rfl
  have hdata := finiteHeckeL_logDeriv_hasSum_ideals χ L hL he ⟨2, hp⟩
  have hd : logDeriv (continuedCompletedHeckeL χ) 2 = logDeriv (heckeGammaFactor χ) 2 + logDeriv L 2 :=
    (logDeriv_congr_nhds hloc).eq_of_nhds.trans (logDeriv_fun_mul _ (heckeGammaFactor_ne_zero_of_re_pos χ
      (zero_lt_one.trans hp)) hdata.2.1 (differentiableAt_heckeGammaFactor_of_re_pos χ (zero_lt_one.trans hp))
      hdata.1.differentiableAt)
  have hr := Complex.hasSum_re (hasSum_logDerivativeCoefficients_two χ L hL he)
  have hv : referenceConstantTwo χ - logDerivativeMass χ 2 0 = -(logDeriv L 2).re := by
    by_cases hχ : χ = 1
    · subst χ
      norm_num [referenceConstantTwo, logDerivativeMass, hd, Complex.add_re]
      ring
    · norm_num [referenceConstantTwo, logDerivativeMass, hχ, hd, Complex.add_re]
  rw [hv]
  apply hr.congr_fun
  intro m
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.div_ofReal_re]
  rfl

/-- An explicit character-uniform coefficient majorant, with the degree of the number
field as its only constant. -/
theorem abs_logDerivativeTermTwo_le (χ : U) (m : ℕ) :
    |logDerivativeTermTwo χ m| ≤ (Module.finrank ℚ F : ℝ) * (Real.log m / (m : ℝ)^2) := by
  rw [logDerivativeTermTwo, abs_div, abs_of_nonneg (sq_nonneg (m : ℝ)), ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  calc
    _ ≤ ‖heckeLogDerivCoefficient (ideleClassNormTwist χ 0) m‖ := Complex.abs_re_le_norm _
    _ ≤ _ := heckeLogDerivCoefficient_le_vonMangoldt χ m
    _ ≤ _ := mul_le_mul_of_nonneg_left ArithmeticFunction.vonMangoldt_le_log (by positivity)

/-- The explicit error for the norm cutoff `N`. -/
def finiteReferenceErrorTwo (F : Type*) [Field F] [NumberField F] (N : ℕ) : ℝ :=
  (Module.finrank ℚ F : ℝ) * ((1 + Real.log N) / N)

/-- Both signs of the omitted Euler part are bounded at every cutoff `N ≥ 2`,
uniformly in the unitary character. -/
theorem abs_finiteReferenceTwo_sub_mass (χ : U) {N : ℕ} (hN : 2 ≤ N) :
    |finiteReferenceTwo χ N - logDerivativeMass χ 2 0| ≤ finiteReferenceErrorTwo F N := by
  have h := abs_sub_sum_range_le_log_div_sq_tail (hasSum_logDerivativeTermTwo χ)
    (Nat.cast_nonneg (Module.finrank ℚ F)) N hN (fun m _ ↦ abs_logDerivativeTermTwo_le χ m)
  simpa only [finiteReferenceTwo, sub_right_comm, finiteReferenceErrorTwo] using h

/-- The lower error endpoint at the finite cutoff is a certified one-sided estimate. -/
theorem finiteReferenceTwo_sub_error_le_mass (χ : U) {N : ℕ} (hN : 2 ≤ N) :
    finiteReferenceTwo χ N - finiteReferenceErrorTwo F N ≤ logDerivativeMass χ 2 0 := by
  have h := (abs_le.mp (abs_finiteReferenceTwo_sub_mass χ hN)).2
  linarith

/-- The finite reference converges as the ideal norm cutoff increases. -/
theorem tendsto_finiteReferenceTwo (χ : U) :
    Tendsto (finiteReferenceTwo χ) atTop (𝓝 (logDerivativeMass χ 2 0)) := by
  have ht := ((hasSum_logDerivativeTermTwo χ).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).const_sub
    (referenceConstantTwo χ)
  change Tendsto (fun N : ℕ ↦ referenceConstantTwo χ - ∑ m ∈ Finset.range (N + 1), logDerivativeTermTwo χ m) _ _
  simpa only [Function.comp_def, sub_sub_cancel] using ht

/-- The certified lower reference converges to the same mass. -/
theorem tendsto_finiteReferenceTwo_sub_error (χ : U) :
    Tendsto (fun N ↦ finiteReferenceTwo χ N - finiteReferenceErrorTwo F N)
      atTop (𝓝 (logDerivativeMass χ 2 0)) := by
  simpa only [finiteReferenceErrorTwo, sub_zero] using
    (tendsto_finiteReferenceTwo χ).sub (tendsto_log_div_sq_tail_radius (Module.finrank ℚ F : ℝ))

end RiemannMasullo.HeckePoisson
