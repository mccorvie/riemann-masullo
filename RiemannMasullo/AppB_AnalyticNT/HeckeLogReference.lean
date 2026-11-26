module

public import RiemannMasullo.AppB_AnalyticNT.HeckeLogQuadrature
public import RiemannMasullo.AppB_AnalyticNT.Sec7b
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-! # The finite logarithmic reference at two

Summing Euler logarithms by ordinary prime-power norm through `N` computes
the log modulus at two with error at most the field degree divided by `N`.
Together with the arctangent-cell table this gives a fully finite logarithmic
measurement, including the pole correction for the principal character. -/

@[expose] public noncomputable section
open Filter MeasureTheory Set Complex Function IsDedekindDomain NumberField
open scoped Topology NNReal

namespace RiemannMasullo.LogQuadrature

open FiniteHeckeSamples PolynomialIdealSamples FiniteTaylor
variable {F : Type*} [Field F] [NumberField F]
local notation "Cᶠ" => IdeleClassGroup (𝓞 F) F
local notation "Uᶠ" => PontryaginDual Cᶠ
local notation "Vᶠ" => HeightOneSpectrum (𝓞 F)
local notation "Hp" => Complex.re ⁻¹' Ioi (1 : ℝ)
local notation "twoRight" => (⟨(2:ℂ),by norm_num⟩ : Hp)

private theorem primeEuler_factor (χ : Uᶠ) (v : Vᶠ)
    (s : ℂ) (hs : 0 < s.re) :
    ∃ ℓ : ℂ, HasSum (fun k : ℕ ↦ heckePrimePowerLogTerm χ v k s) ℓ ∧
      Complex.exp ℓ = finiteHeckeEulerFactor χ v s := by
  classical
  have hN1 : 1 < v.asIdeal.absNorm := HeightOneSpectrum.one_lt_absNorm v
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = heckeIdealValue (ideleClassNormTwist χ 0) v.asIdeal := ⟨_, rfl⟩
  have ha' : a = if (ideleClassNormTwist χ 0).IsUnramifiedAt v then
      (ideleClassNormTwist χ 0).localValue v else 0 := by
    have h := heckeIdealValue_prime_pow (ideleClassNormTwist χ 0) v (k := 1) one_pos
    rw [pow_one, pow_one] at h
    rw [ha, h]
  have hapow (k : ℕ) :
      heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1)) = a ^ (k + 1) := by
    rw [heckeIdealValue_prime_pow _ v (Nat.succ_pos k), ha']
    split_ifs
    · rfl
    · rw [zero_pow (Nat.succ_ne_zero k)]
  have hanorm : ‖a‖ ≤ 1 := by
    rw [ha']
    split_ifs
    · rw [norm_ideleClassNormTwist_zero_localValue]
    · rw [norm_zero]
      exact zero_le_one
  have hz : ‖a * (v.asIdeal.absNorm : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    have h1 : (v.asIdeal.absNorm : ℝ) ^ (-s).re < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN1) (by simpa using hs)
    have h0 : 0 ≤ (v.asIdeal.absNorm : ℝ) ^ (-s).re := Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc ‖a‖ * (v.asIdeal.absNorm : ℝ) ^ (-s).re
        ≤ 1 * (v.asIdeal.absNorm : ℝ) ^ (-s).re := mul_le_mul_of_nonneg_right hanorm h0
      _ < 1 := by rw [one_mul]; exact h1
  have hterm (k : ℕ) : heckePrimePowerLogTerm χ v k s =
      (a * (v.asIdeal.absNorm : ℂ) ^ (-s)) ^ (k + 1) / ((k + 1 : ℕ) : ℂ) := by
    delta heckePrimePowerLogTerm
    rw [hapow, map_pow, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul,
      Complex.cpow_neg]
    ring
  have hshift := (hasSum_nat_add_iff' 1).mpr (Complex.hasSum_taylorSeries_neg_log hz)
  have h1z : 1 - a * (v.asIdeal.absNorm : ℂ) ^ (-s) ≠ 0 := by
    intro h
    rw [← (sub_eq_zero.mp h), norm_one] at hz
    exact lt_irrefl _ hz
  refine ⟨-Complex.log (1 - a * (v.asIdeal.absNorm : ℂ) ^ (-s)), ?_, ?_⟩
  · convert hshift using 1
    · funext k
      rw [hterm]
    · simp
  · rw [Complex.exp_neg, Complex.exp_log h1z]
    delta finiteHeckeEulerFactor
    rw [ha']
    split_ifs <;> simp

/-- Exponentiating the absolutely convergent prime-power sum recovers the original Euler
product. The abscissa is strictly greater than one. -/
theorem exp_primePowerLogTail_zero (χ : Uᶠ) (s : Hp) :
    Complex.exp (heckePrimePowerLogTail χ 0 s) = finiteHeckeL χ s := by
  let e : {a : Vᶠ × ℕ // (0 : ℝ) ≤ ((a.1.asIdeal.absNorm ^ (a.2+1):ℕ):ℝ)} ≃ Vᶠ × ℕ :=
    { toFun := Subtype.val, invFun := fun a ↦ ⟨a,by positivity⟩,
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }
  have hp : HasSum (fun a : Vᶠ × ℕ ↦ heckePrimePowerLogTerm χ a.1 a.2 s)
      (heckePrimePowerLogTail χ 0 s) := e.hasSum_iff.mp (heckePrimePowerLogTail_hasSum_of_one_lt_re χ 0 s)
  choose l hsum hexp using fun v : Vᶠ ↦ primeEuler_factor χ v s (zero_lt_one.trans s.property)
  have hf := hp.prod_fiberwise hsum
  exact (hf.cexp.congr_fun (fun v ↦ (hexp v).symm)).unique (finiteHeckeL_hasProd χ s)

/-- Each logarithmic prime-power coefficient has norm at most the field degree. -/
private theorem primePowerLogCoefficient_le_degree (χ : Uᶠ) {m : ℕ} (hm : 2 ≤ m) :
    ‖heckePrimePowerLogCoefficient χ m‖ ≤ (Module.finrank ℚ F:ℝ) := by
  have hpos : 0 < Real.log (m:ℝ) := Real.log_pos (by exact_mod_cast hm)
  rw [heckePrimePowerLogCoefficient,norm_div,Complex.norm_real,Real.norm_of_nonneg hpos.le,
    div_le_iff₀ hpos]
  exact (heckeLogDerivCoefficient_le_vonMangoldt χ m).trans
    (mul_le_mul_of_nonneg_left ArithmeticFunction.vonMangoldt_le_log (by positivity))

/-- The norm-grouped Euler logarithm converges absolutely in increasing norm at two. -/
private theorem primePower_hasSum_at_two (χ : Uᶠ) :
    HasSum (heckePrimePowerLogTailTerm χ 0 2) (heckePrimePowerLogTail χ 0 2) := by
  have hsum : Summable (fun m : ℕ ↦ (Module.finrank ℚ F:ℝ) * (1/(m:ℝ)^2)) :=
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left _
  have h : Summable (heckePrimePowerLogTailTerm χ 0 2) := by
    apply hsum.of_norm_bounded
    intro m
    by_cases hm : 2 ≤ m
    · rw [heckePrimePowerLogTailTerm,ite_eq_left (Nat.cast_nonneg m),LSeries.term_of_ne_zero (by omega),
        cpow_two,norm_div,norm_pow,Complex.norm_natCast,← mul_div_assoc,mul_one]
      exact div_le_div_of_nonneg_right (primePowerLogCoefficient_le_degree χ hm) (sq_nonneg _)
    · have hm' : m=0 ∨ m=1 := by omega
      rcases hm' with rfl|rfl <;> simp [heckePrimePowerLogTailTerm,heckePrimePowerLogCoefficient,LSeries.term]
  rw [heckePrimePowerLogTail,tsum_eq_of_summable_unconditional h]
  exact h.hasSum

/-- Ordinary finite prime-power Euler sum for the logarithm of the reference modulus at two. -/
def eulerLogTerm (χ : Uᶠ) (m : ℕ) : ℝ :=
  (heckePrimePowerLogCoefficient χ m).re/(m:ℝ)^2

/-- Sum through all prime-power norms at most `N`. -/
def eulerLogReference (χ : Uᶠ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (N+1), eulerLogTerm χ m

private theorem tailTerm_re_two (χ : Uᶠ) (m : ℕ) :
    (heckePrimePowerLogTailTerm χ 0 2 m).re = eulerLogTerm χ m := by
  by_cases hm : m = 0
  · subst m
    norm_num [heckePrimePowerLogTailTerm,eulerLogTerm,heckePrimePowerLogCoefficient]
  · rw [heckePrimePowerLogTailTerm,ite_eq_left (Nat.cast_nonneg m),LSeries.term_of_ne_zero hm,cpow_two,
      eulerLogTerm,← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.div_ofReal_re]

theorem tendsto_eulerLogReference (χ : Uᶠ) :
    Tendsto (eulerLogReference χ) atTop (𝓝 (Real.log ‖finiteHeckeL χ twoRight‖)) := by
  classical
  rw [← exp_primePowerLogTail_zero χ twoRight,Complex.norm_exp,Real.log_exp]
  have hh := (primePower_hasSum_at_two χ).tendsto_sum_nat
  have product := (Complex.continuous_re.tendsto _).comp (hh.comp (tendsto_add_atTop_nat 1))
  apply product.congr
  intro N
  simp only [Function.comp_apply,Complex.re_sum,tailTerm_re_two,eulerLogReference]

private theorem term_abs_le (χ : Uᶠ) {m : ℕ} (hm : 2 ≤ m) :
    |eulerLogTerm χ m| ≤ (Module.finrank ℚ F:ℝ)/(m:ℝ)^2 := by
  rw [eulerLogTerm,abs_div,abs_of_nonneg (sq_nonneg (m:ℝ))]
  exact div_le_div_of_nonneg_right
    ((Complex.abs_re_le_norm _).trans (primePowerLogCoefficient_le_degree χ hm)) (sq_nonneg _)

private theorem abs_tail_reciprocal_sq {f : ℕ → ℝ} {s D : ℝ} (hD : 0 ≤ D)
    (h : Tendsto (fun N : ℕ ↦ ∑ j ∈ Finset.range (N+1), f j) atTop (𝓝 s))
    (N : ℕ) (hN : 0 < N) (hf : ∀ m, N < m → |f m| ≤ D/(m:ℝ)^2) :
    |s - ∑ j ∈ Finset.range (N+1), f j| ≤ D/N := by
  let t (M : ℕ) := ∑ j ∈ Finset.range M, f (N+1+j)
  have tlim : Tendsto t atTop (𝓝 (s - ∑ j ∈ Finset.range (N+1), f j)) := by
    have ht := (h.comp (tendsto_add_atTop_nat N)).sub_const (∑ j ∈ Finset.range (N+1), f j)
    apply ht.congr
    intro M
    simp only [Function.comp_apply]
    rw [show M+N+1 = (N+1)+M by omega,Finset.sum_range_add,add_sub_cancel_left]
  have hsum (M : ℕ) : |t M| ≤ D/N-D/((N:ℝ)+M) := by
    induction M with
    | zero => simp [t]
    | succ M ih =>
      have hk : 0 < (N:ℝ)+M := by positivity
      have hk' : 0 < (N:ℝ)+M+1 := by positivity
      have hstep : D/((N:ℝ)+M+1)^2 ≤ D/((N:ℝ)+M) - D/((N:ℝ)+M+1) := by
        have hfrac : D/((N:ℝ)+M) - D/((N:ℝ)+M+1) = D/(((N:ℝ)+M)*((N:ℝ)+M+1)) := by
          field_simp
          ring
        rw [hfrac]
        apply div_le_div_of_nonneg_left hD (by positivity)
        nlinarith
      have ht : |f (N+1+M)| ≤ D/((N:ℝ)+M+1)^2 := by
        simpa only [Nat.cast_add,Nat.cast_one,add_right_comm (N:ℝ) 1 _] using hf (N+1+M) (by omega)
      rw [show t (M+1) = t M + f (N+1+M) by simp [t,Finset.sum_range_succ]]
      rw [Nat.cast_add_one,←add_assoc]
      exact (abs_add_le _ _).trans (by linarith)
  apply le_of_tendsto tlim.abs
  exact Eventually.of_forall fun M ↦ (hsum M).trans (sub_le_self _ (div_nonneg hD (by positivity)))

/-- The finite logarithmic reference has error at most the field degree divided by the cutoff. -/
theorem abs_eulerLogReference_sub (χ : Uᶠ) {N : ℕ} (hN : 0 < N) :
    |Real.log ‖finiteHeckeL χ twoRight‖ - eulerLogReference χ N| ≤ (Module.finrank ℚ F : ℝ)/N :=
  abs_tail_reciprocal_sq (by positivity) (tendsto_eulerLogReference χ) N hN
    (fun m hm ↦ term_abs_le χ (by omega))

/-- One fully finite sequence computes the difference between the boundary integral
and the logarithm of the reference modulus. -/
theorem tendsto_heckeLogStatistic_sub_reference (τ : ℝ≥0ˣ →ₜ* Cᶠ) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Uᶠ) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s)
    (hlog : Integrable (fun t ↦ poissonWeight t * Real.log ‖L (point t)‖)) :
    Tendsto (fun n ↦ heckeLogStatistic χ n - eulerLogReference χ n) atTop
      (𝓝 ((∫ t, poissonWeight t * Real.log ‖L (point t)‖) - Real.log ‖L 2‖)) := by
  rw [he twoRight]
  exact (tendsto_heckeLogStatistic τ hτ χ hχ L hL he hlog).sub (tendsto_eulerLogReference χ)

open scoped Classical in
/-- The finite arithmetic difference at two, with the ordinary principal-pole correction. -/
def finiteLogDifference (χ : Uᶠ) (n : ℕ) : ℝ :=
  heckeLogStatistic χ n - eulerLogReference χ n + (if χ = 1 then Real.log 2 else 0)

open scoped Classical in
/-- The signed finite statistic for the canonical ordinary Hecke continuation converges
under absolute integrability of its weighted critical-line log modulus. -/
theorem tendsto_finiteLogDifference (τ : ℝ≥0ˣ →ₜ* Cᶠ) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Uᶠ) (hχ : ∀ t, χ (τ t) = 1)
    (hlog : Integrable (fun t ↦ poissonWeight t *
      Real.log ‖(finiteHeckeL_exists_continuation χ).choose (point t)‖)) :
    let L := (finiteHeckeL_exists_continuation χ).choose
    Tendsto (finiteLogDifference χ) atTop
      (𝓝 ((∫ t, poissonWeight t * Real.log ‖L (point t)‖) - Real.log ‖L 2‖ +
        (if χ = 1 then Real.log 2 else 0))) := by
  intro L
  obtain ⟨hL, he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  exact (tendsto_heckeLogStatistic_sub_reference τ hτ χ hχ L hL he hlog).add_const _

end RiemannMasullo.LogQuadrature
