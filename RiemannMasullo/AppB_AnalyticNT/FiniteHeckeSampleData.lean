module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.FiniteTaylor
public import RiemannMasullo.Ch06_LocalGlobal.Sec3
public import RiemannMasullo.AppB_AnalyticNT.Sec4b
import RiemannMasullo.AppB_AnalyticNT.Sec6
import Mathlib.Tactic

/-! A finite ideal-coefficient approximation to the critical-line finite Hecke function. -/

@[expose] public noncomputable section

open Complex Filter Function IsDedekindDomain Metric NumberField Set
open scoped NNReal Topology

namespace RiemannMasullo.FiniteHeckeSamples

open FiniteTaylor

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽
local notation "Hp" => (Complex.re ⁻¹' Ioi (1 : ℝ))
local notation "c(" t ")" => (⟨2, t⟩ : ℂ)
local notation "z(" t ")" => (⟨1 / 2, t⟩ : ℂ)

/-- The Dirichlet polynomial `1 - 2·2^(-s)`. -/
def polarRoot (s : ℂ) : ℂ := 1 - 2 * frequency 2 s

/-- The squared pole filter, whose norm is bounded below on the critical line. -/
def polarFactor (s : ℂ) : ℂ := polarRoot s ^ 2

/-- The two coefficients of the Dirichlet polynomial that vanishes at one. -/
def rootCoefficients : ArithmeticFunction ℂ :=
  ⟨fun n ↦ if n = 1 then 1 else if n = 2 then -2 else 0, by norm_num⟩

/-- Finite Dirichlet convolution of the genuine ideal coefficients with the squared pole filter. -/
def coefficients (χ : U𝔽) : ArithmeticFunction ℂ :=
  (rootCoefficients * rootCoefficients) * (ideleClassNormTwist χ 0).LFunction

private theorem root_convolution_apply (a : ArithmeticFunction ℂ) (m : ℕ) :
    (rootCoefficients * a) m = a m - (if 2 ∣ m then 2 * a (m / 2) else 0) := by
  by_cases hm : m = 0
  · simp [hm]
  have hterm (d : ℕ) : rootCoefficients d * a (m / d) =
      (if d = 1 then a (m / d) else 0) - (if d = 2 then 2 * a (m / d) else 0) := by
    by_cases h₁ : d = 1 <;> by_cases h₂ : d = 2 <;> simp [rootCoefficients, h₁, h₂]
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun x y ↦ rootCoefficients x * a y)]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp [Nat.mem_divisors, hm]

/-- Each coefficient uses only the three indicated finite sums of ideal values at fixed norm. -/
theorem coefficients_eq_ideal_values (χ : U𝔽) (m : ℕ) :
    let a (d : ℕ) := heckeNormCoefficient (ideleClassNormTwist χ 0) (d : ℝ)
    coefficients χ m = a m - (if 2 ∣ m then 4 * a (m / 2) else 0) +
      (if 4 ∣ m then 4 * a (m / 4) else 0) := by
  dsimp only
  simp_rw [heckeNormCoefficient_natCast]
  rw [coefficients, mul_assoc, root_convolution_apply, root_convolution_apply, root_convolution_apply]
  have hn : m / 2 / 2 = m / 4 := by omega
  by_cases h₂ : 2 ∣ m <;> by_cases h₄ : 4 ∣ m <;> by_cases hhalf : 2 ∣ m / 2
  all_goals try omega
  all_goals simp [h₂, h₄, hhalf, hn]
  all_goals ring

private theorem root_hasSum (s : ℂ) : LSeriesHasSum rootCoefficients s (polarRoot s) := by
  have hout (n : ℕ) (hn : n ∉ ({1, 2} : Finset ℕ)) : LSeries.term rootCoefficients s n = 0 := by
    rcases eq_or_ne n 0 with rfl | h
    · simp
    · have hh : n ≠ 1 ∧ n ≠ 2 := by simpa using hn
      simp [LSeries.term_of_ne_zero h, rootCoefficients, hh.1, hh.2]
  have hh : HasSum (LSeries.term rootCoefficients s) (∑ n ∈ ({1, 2} : Finset ℕ),
      LSeries.term rootCoefficients s n) := hasSum_sum_of_ne_finset_zero hout
  change HasSum (LSeries.term rootCoefficients s) (polarRoot s)
  convert hh using 1
  rw [polarRoot, frequency_eq_inv_cpow (by decide : (2 : ℕ) ≠ 0)]
  simp [LSeries.term, rootCoefficients, div_eq_mul_inv]
  ring

theorem coefficients_hasSum (χ : U𝔽) (s : Hp) :
    LSeriesHasSum (coefficients χ) s (polarFactor s * finiteHeckeL χ s) := by
  simpa only [coefficients, polarFactor, pow_two, finiteHeckeL, NumberField.HeckeCharacter.LSeries] using
    ArithmeticFunction.LSeriesHasSum_mul (ArithmeticFunction.LSeriesHasSum_mul (root_hasSum s) (root_hasSum s))
      (finiteHeckeL_seriesSummable χ s).LSeriesHasSum

private theorem root_analytic (w : ℂ) : AnalyticAt ℂ polarRoot w := by
  unfold polarRoot frequency
  fun_prop

private theorem root_one : polarRoot 1 = 0 := by
  rw [polarRoot, frequency_eq_inv_cpow (by decide : (2 : ℕ) ≠ 0)]
  norm_num

/-- The modulus of the dyadic carrier is independent of the critical ordinate. -/
theorem norm_twice_frequency_critical (t : ℝ) : ‖(2 : ℂ) * frequency 2 z(t)‖ = Real.sqrt 2 := by
  rw [frequency_eq_inv_cpow (by decide : (2 : ℕ) ≠ 0), norm_mul, norm_inv]
  rw [norm_natCast_cpow_of_pos (by decide : (0 : ℕ) < 2)]
  norm_num only [Complex.norm_ofNat, Nat.cast_ofNat]
  change 2 * ((2 : ℝ) ^ (1 / 2 : ℝ))⁻¹ = _
  rw [← Real.sqrt_eq_rpow]
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  field_simp
  nlinarith

/-- The denominator has a uniform lower bound at every ordinate. -/
theorem critical_factor_lower (t : ℝ) : (Real.sqrt 2 - 1) ^ 2 ≤ ‖polarFactor z(t)‖ := by
  have hr := norm_sub_norm_le ((2 : ℂ) * frequency 2 z(t)) (1 : ℂ)
  rw [norm_twice_frequency_critical, norm_one, norm_sub_rev] at hr
  rw [polarFactor, norm_pow]
  exact pow_le_pow_left₀ (by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]) hr 2

private theorem finite_order_eq_completed (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (s : ℂ) (hs : 0 < s.re) :
    meromorphicOrderAt L s = meromorphicOrderAt (explicitFormulaCompletedHeckeL χ) s := by
  let Λ := explicitFormulaCompletedHeckeL χ
  let G (z : ℂ) := (heckeGammaFactor χ z)⁻¹
  let H (z : ℂ) := G z * Λ z
  obtain ⟨hΛ, hΛe⟩ := explicitFormulaCompletedHeckeL_spec χ
  have hga := differentiable_inv_heckeGammaFactor χ
  have hH : MeromorphicOn H univ := fun z hz ↦
    (hga.analyticAt z).meromorphicAt.mul (hΛ hz).meromorphicAt
  have hEq := heckeEulerProductOutside_eq_finite_nf_eq L H hL.meromorphicOn hH (fun z hz ↦ by
    rw [he ⟨z, hz⟩]
    dsimp only [H, G, Λ]
    rw [hΛe ⟨z, hz⟩, completedHeckeL, finiteHeckeL,
      inv_mul_cancel_left₀ (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz))])
  have h := congrArg (fun f ↦ meromorphicOrderAt f s) hEq
  rw [meromorphicOrderAt_toMeromorphicNFOn hL.meromorphicOn (mem_univ _),
    meromorphicOrderAt_toMeromorphicNFOn hH (mem_univ _)] at h
  exact h.trans (meromorphicOrderAt_mul_of_ne_zero (hga.analyticAt s)
    (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ hs)))

private theorem finite_poles (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (s : ℂ) (hs : 0 < s.re) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt L s ∧ (s ≠ 1 → AnalyticAt ℂ L s) := by
  by_cases hneg : meromorphicOrderAt L s < 0
  · let Λ := explicitFormulaCompletedHeckeL χ
    have hord : meromorphicOrderAt L s = meromorphicOrderAt Λ s := finite_order_eq_completed χ L hL he _ hs
    have hΛ := (explicitFormulaCompletedHeckeL_spec χ).1
    have hdiv : MeromorphicOn.divisor Λ univ s < 0 := by
      rw [MeromorphicOn.divisor_apply hΛ.meromorphicOn (mem_univ _)]
      rw [hord] at hneg
      generalize meromorphicOrderAt Λ s = m at hneg ⊢
      cases m with
      | top => simp at hneg
      | coe m => exact WithTop.coe_lt_coe.mp hneg
    obtain ⟨htr, hw⟩ := idelicExplicitFormula_chart_poles τ hτ χ hχ s hdiv
    have hw₁ := hw.resolve_left (fun h ↦ by simp [h] at hs)
    subst s
    subst χ
    have htrue := (idelicExplicitFormula_trivial_poles (F := F)).2
    rw [MeromorphicOn.divisor_apply hΛ.meromorphicOn (mem_univ _)] at htrue
    rw [hord] at hneg ⊢
    change (meromorphicOrderAt Λ 1).untop₀ = -1 at htrue
    refine ⟨?_, fun h ↦ (h rfl).elim⟩
    generalize meromorphicOrderAt Λ 1 = m at hneg htrue ⊢
    cases m with
    | top => simp at hneg
    | coe m => exact WithTop.coe_le_coe.mpr htrue.ge
  · have hpos := le_of_not_gt hneg
    exact ⟨(by decide : (-1 : WithTop ℤ) ≤ 0).trans hpos,
      fun _ ↦ (hL (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp hpos⟩

/-- The double zero gives the correct analytic point value at the principal simple pole. -/
theorem analyticAt_polarFactor_mul (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (s : ℂ) (hs : 0 < s.re) :
    AnalyticAt ℂ (fun w ↦ polarFactor w * L w) s := by
  obtain ⟨hl, ha⟩ := finite_poles τ hτ χ hχ L hL he s hs
  by_cases h : s = 1
  · subst s
    apply AnalyticAt.of_meromorphicOrderAt_pos _ (by simp [polarFactor, root_one])
    have hrt := (root_analytic 1).meromorphicNFAt
    have hr : 0 < meromorphicOrderAt polarRoot 1 := lt_of_le_of_ne (root_analytic 1).meromorphicOrderAt_nonneg
      (fun hz ↦ (hrt.meromorphicOrderAt_eq_zero_iff.mp hz.symm) root_one)
    change 0 < meromorphicOrderAt ((polarRoot ^ 2) * L) 1
    rw [meromorphicOrderAt_mul ((root_analytic 1).pow 2).meromorphicAt (hL (mem_univ _)).meromorphicAt,
      meromorphicOrderAt_pow (root_analytic 1).meromorphicAt]
    generalize meromorphicOrderAt polarRoot 1 = r at hr ⊢
    generalize meromorphicOrderAt L 1 = m at hl ⊢
    cases r with
    | top => simp [WithTop.mul_top (by norm_num : (2 : WithTop ℤ) ≠ 0)]
    | coe r =>
      cases m with
      | top => simp
      | coe m =>
        have hr' : 0 < r := WithTop.coe_lt_coe.mp hr
        have hm' : (-1 : ℤ) ≤ m := WithTop.coe_le_coe.mp hl
        exact WithTop.coe_lt_coe.mpr (show (0 : ℤ) < 2 * r + m by omega)
  · exact ((root_analytic s).pow 2).mul (ha h)

/-- The single exponential equal to the inverse dyadic carrier on the critical line. -/
def dyadicFrequency (t : ℝ) : ℂ := (2 : ℂ)⁻¹ * exp ((Real.log 2 : ℂ) * z(t))

theorem dyadicFrequency_eq_inv (t : ℝ) :
    dyadicFrequency t = ((2 : ℂ) * frequency 2 z(t))⁻¹ := by
  simp [dyadicFrequency, frequency, neg_mul, Complex.exp_neg, mul_comm]

theorem norm_dyadicFrequency_pow (t : ℝ) (n : ℕ) :
    ‖dyadicFrequency t ^ (8 * n)‖ = (1 / 16 : ℝ) ^ n := by
  rw [norm_pow, dyadicFrequency_eq_inv, norm_inv, norm_twice_frequency_critical, pow_mul]
  have h8 : (Real.sqrt 2) ^ 8 = 16 := by
    calc
      _ = ((Real.sqrt 2) ^ 2) ^ 4 := by ring
      _ = 16 := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  rw [inv_pow, h8]
  norm_num

/-- A fixed vertical strip bounds the finite critical function at large heights.
Continuity of the normalized continuation supplies the compact height interval. -/
theorem critical_norm_polynomial_bound (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    ∃ A > (0 : ℝ), ∃ p : ℕ, ∀ t : ℝ, ‖L z(t)‖ ≤ A * (1 + |t|) ^ p := by
  obtain ⟨M,hM,hO⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hL he 0 1 (by norm_num)
  obtain ⟨C,hC⟩ := Asymptotics.isBigO_iff.mp hO
  rw [eventually_inf_principal,eventually_comap,eventually_atTop] at hC
  obtain ⟨T,hT⟩ := hC
  have hz : Continuous (fun t : ℝ ↦ z(t)) := by
    have e (t : ℝ) : z(t) = (1 / 2 : ℂ) + (t : ℂ) * I := by
      apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im]
    simp_rw [e]
    fun_prop
  have hc : Continuous (fun t : ℝ ↦ L z(t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hne : z(t) ≠ 1 := by intro h; have heq := congrArg Complex.re h; norm_num at heq
    exact ((finite_poles τ hτ χ hχ L hL he z(t) (by norm_num)).2 hne).continuousAt.comp hz.continuousAt
  obtain ⟨B,hB⟩ := (isCompact_Icc (a := -|T|) (b := |T|)).exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨p,hp⟩ := exists_nat_ge M
  let A := max 1 (max B C)
  have ha : 1 ≤ A := le_max_left _ _
  refine ⟨A,zero_lt_one.trans_le ha,p,fun t ↦ ?_⟩
  by_cases ht : T ≤ |t|
  · have h := hT _ ht z(t) rfl (show (z(t)).re ∈ Icc 0 1 by norm_num)
    change ‖L z(t)‖ ≤ C * ‖|t| ^ M‖ at h
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at h
    refine h.trans ((mul_le_mul_of_nonneg_right ((le_max_right B C).trans (le_max_right 1 _))
      (Real.rpow_nonneg (abs_nonneg _) _)).trans ?_)
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans ha)
    rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow (abs_nonneg _) (by linarith : |t| ≤ 1+|t|) hM.le).trans
      (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) hp)
  · have ht' : |t| ≤ |T| := (le_of_not_ge ht).trans (le_abs_self _)
    exact ((hB t (abs_le.mp ht')).trans ((le_max_left B C).trans (le_max_right 1 _))).trans
      (le_mul_of_one_le_right (zero_le_one.trans ha) (one_le_pow₀ (by linarith [abs_nonneg t])))

end RiemannMasullo.FiniteHeckeSamples
