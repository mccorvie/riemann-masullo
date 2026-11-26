module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b_NormalizedHeckeDisk
public import RiemannMasullo.AppB_AnalyticNT.Sec7b
public import RiemannMasullo.ForMathlib.Analysis.Complex.LaguerreJet
import Mathlib.Tactic

/-! # Finite prime-power measurements of the cleared finite Hecke logarithmic derivative -/

@[expose] public noncomputable section

open Complex Filter Finset Function IsDedekindDomain Metric NumberField Set Topology
namespace RiemannMasullo.HeckeLaguerre

variable {F : Type*} [Field F] [NumberField F]
local notation "U𝔽" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "Hp" => Complex.re ⁻¹' Ioi (1:ℝ)
open HalfPlaneJensen HeckeDiskNormalization LaguerreJet
open scoped Classical

/-- The zero and one coefficients of the logarithmic series vanish, and its
coefficients have norm bounded by the field degree. -/
theorem norm_logCoefficient_le (χ : U𝔽) (m : ℕ) :
    ‖heckePrimePowerLogCoefficient χ m‖ ≤ (Module.finrank ℚ F:ℝ) := by
  have hb := heckeLogDerivCoefficient_le_vonMangoldt χ m
  by_cases hm : 1 < m
  · have hl := Real.log_pos (show (1:ℝ) < m by exact_mod_cast hm)
    rw [heckePrimePowerLogCoefficient, norm_div, Complex.norm_real, Real.norm_of_nonneg hl.le,
      div_le_iff₀ hl]
    exact hb.trans (mul_le_mul_of_nonneg_left ArithmeticFunction.vonMangoldt_le_log (Nat.cast_nonneg _))
  · obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
    all_goals simp [heckePrimePowerLogCoefficient]

private theorem logMul_weight (χ : U𝔽) : LSeries.logMul (heckePrimePowerLogCoefficient χ) =
    heckeLogDerivCoefficient (ideleClassNormTwist χ 0) := by
  funext m
  have hb := heckeLogDerivCoefficient_le_vonMangoldt χ m
  by_cases hm : 1 < m
  · have hl : (Real.log m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.log_pos (show (1:ℝ) < m by exact_mod_cast hm)).ne'
    simp only [LSeries.logMul, ← Complex.natCast_log, heckePrimePowerLogCoefficient]
    field_simp [hl]
  · obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
    all_goals
      simp at hb
      simp [hb, LSeries.logMul]

/-- The ordinary finite-ideal logarithmic derivative grouped by integer norm.
The fibers are genuine finite sets of ideals of a fixed norm. -/
theorem grouped_negLogDeriv_hasSum (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s (-logDeriv L s) := by
  classical
  have H := (finiteHeckeL_negLogDeriv_hasSum_ideals χ L hL he ⟨s,hs⟩).tsum_fiberwise
    (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦ I.val.absNorm)
  refine H.congr_fun fun m ↦ ?_
  rcases eq_or_ne m 0 with rfl | hm
  · have : IsEmpty ↑((fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦ I.val.absNorm) ⁻¹' {0}) :=
      ⟨fun b ↦ b.val.property (Ideal.absNorm_eq_zero_iff.mp b.property)⟩
    rw [tsum_empty, LSeries.term_zero]
  · let S := {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = m}
    have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = m}.Finite :=
      (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) m).subset fun _ h ↦ h.2
    have : Finite S := hfin.to_subtype
    have : Fintype S := Fintype.ofFinite _
    let e : ↑((fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦ I.val.absNorm) ⁻¹' {m}) ≃ S :=
      { toFun := fun b ↦ ⟨b.val.val,b.val.property,b.property⟩
        invFun := fun I ↦ ⟨⟨I.val,I.property.1⟩,I.property.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [← e.symm.tsum_eq, tsum_fintype, LSeries.term_of_ne_zero hm, heckeLogDerivCoefficient,
      finsum_eq_sum_of_fintype, Finset.sum_div]
    refine Finset.sum_congr rfl fun I _ ↦ ?_
    change _ = _ / ((I.val.absNorm : ℕ):ℂ)^s
    rw [I.property.2]
    rfl

private theorem absConv_lt (χ : U𝔽) {s : ℂ} (hs : 1 < s.re) :
    LSeries.abscissaOfAbsConv (heckePrimePowerLogCoefficient χ) < s.re := by
  obtain ⟨r, hr, hrs⟩ := exists_between hs
  have h := LSeriesSummable_of_bounded_of_one_lt_real
    (fun m _ ↦ norm_logCoefficient_le χ m) hr
  exact h.abscissaOfAbsConv_le.trans_lt (by exact_mod_cast hrs)

/-- The norm-grouped logarithmic Euler series is a primitive of the genuine
finite Hecke logarithmic derivative throughout the Euler half-plane. -/
theorem hasDerivAt_logEuler (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (LSeries (heckePrimePowerLogCoefficient χ)) (logDeriv L s) s := by
  have hd := LSeries_hasDerivAt (absConv_lt χ hs)
  have hg : LSeries (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s = -logDeriv L s :=
    (grouped_negLogDeriv_hasSum χ L hL he hs).tsum_eq
  rw [logMul_weight, hg, neg_neg] at hd
  exact hd

/-- Sharp Euler-half-plane bound on the entire closed coefficient circle. -/
theorem re_toHalf_of_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1/5) : 3/2 ≤ (toHalf z).re := by
  have h₂ : z.re^2 + z.im^2 ≤ (1/5:ℝ)^2 := by
    nlinarith [Complex.sq_norm_sub_sq_re z, mul_self_le_mul_self (norm_nonneg z) hz]
  have h₁ : -(1/5:ℝ) ≤ z.re := by
    have h := (Complex.abs_re_le_norm z).trans hz
    exact (abs_le.mp h).1
  have hd : 0 < Complex.normSq (1-z) := Complex.normSq_pos.mpr (half_den (by linarith))
  rw [toHalf, Complex.div_re]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, zero_sub]
  rw [← add_div, le_div_iff₀ hd]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at *
  norm_num at *
  nlinarith

/-- The logarithmic Euler series pulled back to the disk near zero. -/
def eulerDisk (χ : U𝔽) (z : ℂ) : ℂ := LSeries (heckePrimePowerLogCoefficient χ) (toHalf z)

private def polyDisk (χ : U𝔽) (X : ℕ) (z : ℂ) : ℂ :=
  ∑ m ∈ range (X+1), LSeries.term (heckePrimePowerLogCoefficient χ) (toHalf z) m

/-- Logarithmic derivative of the principal pole-clearing factor in disk coordinates. -/
def polar (z : ℂ) : ℂ := 1/(z+1/2) - 1/(z+2)

private theorem euler_analytic (χ : U𝔽) {z : ℂ} (hz : ‖z‖ ≤ 1/5) : AnalyticAt ℂ (eulerDisk χ) z :=
  (LSeries_analyticOnNhd _ _ (absConv_lt χ (by linarith [re_toHalf_of_norm_le hz]))).comp
    (chart_analytic (by linarith))

private theorem poly_analytic (χ : U𝔽) (X : ℕ) {z : ℂ} (hz : ‖z‖ < 1) : AnalyticAt ℂ (polyDisk χ X) z := by
  apply Finset.analyticAt_fun_sum
  intro i _
  have h : Differentiable ℂ (fun s ↦ LSeries.term (heckePrimePowerLogCoefficient χ) s i) :=
    fun s ↦ (LSeries.hasDerivAt_term _ i s).differentiableAt
  exact (h.analyticAt (toHalf z)).comp (chart_analytic hz)

private theorem polar_analytic : AnalyticAt ℂ polar 0 := by
  unfold polar
  fun_prop (disch := norm_num)

private theorem polar_coeff (k : ℕ) :
    coeff polar k = (-1:ℂ)^k*((2:ℂ)^(k+1)-(2:ℂ)⁻¹^(k+1)) := by
  have h₁ : AnalyticAt ℂ (fun z : ℂ ↦ 1/(z+1/2)) 0 := by fun_prop (disch := norm_num)
  have h₂ : AnalyticAt ℂ (fun z : ℂ ↦ 1/(z+2)) 0 := by fun_prop (disch := norm_num)
  have h : coeff polar k = coeff (fun z : ℂ ↦ 1/(z+1/2)) k - coeff (fun z : ℂ ↦ 1/(z+2)) k := by
    unfold polar coeff
    rw [iteratedDeriv_fun_sub h₁.contDiffAt h₂.contDiffAt, sub_div]
  rw [h, coeff_simple _ (by norm_num), coeff_simple _ (by norm_num)]
  rw [show (1/2:ℂ)^(k+1) = ((2:ℂ)^(k+1))⁻¹ by rw [one_div,inv_pow],
    div_inv_eq_mul, div_eq_mul_inv, ← inv_pow]
  ring

private theorem normalized_euler_eq (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {s : ℂ} (hs : 1 < s.re) :
    cleared χ L s = halfFactor χ s * L s := by
  classical
  have ha := (finiteHeckeL_logDeriv_hasSum_ideals χ L hL he ⟨s,hs⟩).1
  have hfac : AnalyticAt ℂ (halfFactor χ) s := by
    change AnalyticAt ℂ (fun z : ℂ ↦ if χ = 1 then (z-1)/z else 1) s
    by_cases hh : χ = 1
    · simp only [hh, ↓reduceIte]
      apply (show AnalyticAt ℂ (fun z : ℂ ↦ z-1) s by fun_prop).div analyticAt_id
      rintro rfl
      norm_num at hs
    · simp only [hh, ↓reduceIte]
      exact analyticAt_const
  rw [cleared, toMeromorphicNFOn_eq_toMeromorphicNFAt (meromorphic_product χ L hL) (mem_univ _),
    toMeromorphicNFAt_eq_self.mpr (hfac.mul ha).meromorphicNFAt]
  rfl

/-- The cleared logarithmic derivative equals the derivative of the logarithmic
Euler series plus the elementary pole correction, as a germ at zero. -/
theorem logDeriv_cleared_germ (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    logDeriv (fun z ↦ cleared χ L (toHalf z)) =ᶠ[𝓝 0]
      (fun z ↦ deriv (eulerDisk χ) z + (if χ = 1 then polar z else 0)) := by
  classical
  let g (z : ℂ) := if χ = 1 then (1+2*z)/(2+z) else 1
  have hball : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < 1/5 := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ)<1/5)] with z hz
    simpa using hz
  have hprod : (fun z ↦ cleared χ L (toHalf z)) =ᶠ[𝓝 0] (fun z ↦ g z * L (toHalf z)) := by
    filter_upwards [hball] with z hz
    have hs : 1 < (toHalf z).re := by linarith [re_toHalf_of_norm_le hz.le]
    rw [normalized_euler_eq χ L hL he hs]
    congr 1
    by_cases h : χ = 1
    · simp only [halfFactor,g,h,↓reduceIte,toHalf]
      have h1 := half_den (show ‖z‖ < 1 by linarith)
      have h2 : 2+z ≠ 0 := by
        intro H
        have hz' : z = -2 := by linear_combination H
        norm_num [hz'] at hz
      field_simp [h1,h2]
      ring
    · simp [g,halfFactor,h]
  filter_upwards [logDeriv_congr_nhds hprod,hball] with z hz hz₁
  have hs : 1 < (toHalf z).re := by linarith [re_toHalf_of_norm_le hz₁.le]
  obtain ⟨hdl,hl,-⟩ := finiteHeckeL_logDeriv_hasSum_ideals χ L hL he ⟨toHalf z,hs⟩
  have hchart := chart_analytic (u := z) (by linarith : ‖z‖ < 1)
  have Hd := ((hasDerivAt_logEuler χ L hL he hs).comp z hchart.differentiableAt.hasDerivAt).deriv
  change deriv (eulerDisk χ) z = _ at Hd
  rw [hz,Hd]
  change AnalyticAt ℂ L (toHalf z) at hdl
  change L (toHalf z) ≠ 0 at hl
  have heq := logDeriv_fun_comp (f := L) (g := toHalf) hdl.differentiableAt hchart.differentiableAt
  by_cases h : χ = 1
  · have h1 : 1+2*z ≠ 0 := by
      intro H
      have hz' : z = -(1/2) := by linear_combination H / 2
      norm_num [hz'] at hz₁
    have h2 : 2+z ≠ 0 := by
      intro H
      have hz' : z = -2 := by linear_combination H
      norm_num [hz'] at hz₁
    have hg : g = (fun u : ℂ ↦ (1+2*u)/(2+u)) := by funext u; simp [g,h]
    rw [logDeriv_fun_mul (f := g) (g := fun u ↦ L (toHalf u)) z (by rw [hg]; exact div_ne_zero h1 h2) hl
      (by rw [hg]; fun_prop (disch := assumption)) (hdl.differentiableAt.comp z hchart.differentiableAt), heq,hg]
    have hd₁ : HasDerivAt (fun u : ℂ ↦ 1+2*u) 2 z := by
      simpa using ((hasDerivAt_id z).const_mul (2:ℂ)).const_add 1
    have hd₂ : HasDerivAt (fun u : ℂ ↦ 2+u) 1 z := (hasDerivAt_id z).const_add 2
    rw [logDeriv_fun_div z h1 h2 hd₁.differentiableAt hd₂.differentiableAt,
      logDeriv_apply, hd₁.deriv, logDeriv_apply, hd₂.deriv]
    simp only [h,↓reduceIte,polar]
    have hn : z+1/2 ≠ 0 := by intro H; apply h1; linear_combination 2*H
    rw [show (2:ℂ)/(1+2*z) = 1/(z+1/2) by apply (div_eq_div_iff h1 hn).mpr; ring,
      show 2+z = z+2 by ring]
    ring
  · simp [g,h,heq]

private theorem term_coeff (w : ℕ → ℂ) (m n : ℕ) :
    coeff (fun z ↦ LSeries.term w (toHalf z) m) n =
      (w m/(m:ℂ)^2)*laguerre (-3*(Real.log m:ℂ)) n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [coeff]
  have hm' : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  let c := -3*(Real.log m:ℂ)
  have hg : (fun z ↦ LSeries.term w (toHalf z) m) =ᶠ[𝓝 0]
      (fun z : ℂ ↦ (w m/(m:ℂ)^2)*Complex.exp (c*((1-z)⁻¹-1))) := by
    filter_upwards [eventually_ne_nhds (zero_ne_one : (0:ℂ) ≠ 1)] with z hz
    have h1 := sub_ne_zero.mpr hz.symm
    have hh : -toHalf z = (-2:ℂ)+(-3)*((1-z)⁻¹-1) := by unfold toHalf; field_simp [h1]; ring
    rw [LSeries.term_of_ne_zero hm, div_eq_mul_inv, ← Complex.cpow_neg, hh,
      Complex.cpow_add _ _ hm', Complex.cpow_neg, show (m:ℂ)^(2:ℂ)=(m:ℂ)^2 by norm_num,
      Complex.cpow_def_of_ne_zero hm', ← Complex.natCast_log]
    dsimp [c]
    rw [show ((Real.log m:ℝ):ℂ)*(-3*((1-z)⁻¹-1))=-3*(Real.log m:ℂ)*((1-z)⁻¹-1) by ring]
    ring
  have hcoef := coeff_exp_coord c n
  unfold coeff at hcoef ⊢
  rw [hg.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, mul_div_assoc, hcoef]

private theorem poly_coeff (χ : U𝔽) (X n : ℕ) :
    coeff (polyDisk χ X) n = ∑ m ∈ range (X+1),
      (heckePrimePowerLogCoefficient χ m/(m:ℂ)^2)*laguerre (-3*(Real.log m:ℂ)) n := by
  have h (m : ℕ) : AnalyticAt ℂ (fun z ↦ LSeries.term (heckePrimePowerLogCoefficient χ) (toHalf z) m) 0 := by
    have hd : Differentiable ℂ (fun s ↦ LSeries.term (heckePrimePowerLogCoefficient χ) s m) :=
      fun s ↦ (LSeries.hasDerivAt_term _ m s).differentiableAt
    exact (hd.analyticAt _).comp (chart_analytic (by norm_num))
  unfold coeff polyDisk
  rw [iteratedDeriv_fun_sum (fun m _ ↦ (h m).contDiffAt), Finset.sum_div]
  exact Finset.sum_congr rfl fun m _ ↦ term_coeff _ m n

private theorem coeff_deriv (f : ℂ → ℂ) (k : ℕ) :
    coeff (deriv f) k = (k+1:ℂ)*coeff f (k+1) := by
  rw [coeff, coeff, ← iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  field_simp [Nat.factorial_ne_zero]

/-- All positive prime-ideal powers of one prescribed absolute norm form a finite type. -/
theorem finite_primePowersAtNorm (F : Type*) [Field F] [NumberField F] (m : ℕ) :
    Finite {a : HeightOneSpectrum (𝓞 F) × ℕ // a.1.asIdeal.absNorm^(a.2+1) = m} := by
  classical
  let I := {v : Ideal (𝓞 F) // v.absNorm = m}
  have : Finite I := (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) m).to_subtype
  let f (a : {a : HeightOneSpectrum (𝓞 F) × ℕ // a.1.asIdeal.absNorm^(a.2+1) = m}) : I :=
    ⟨a.val.1.asIdeal^(a.val.2+1),by rw [map_pow]; exact a.property⟩
  apply Finite.of_injective f
  rintro ⟨⟨v,k⟩,hk⟩ ⟨⟨w,j⟩,hj⟩ H
  have h : v.asIdeal^(k+1) = w.asIdeal^(j+1) := congrArg Subtype.val H
  obtain rfl := HeightOneSpectrum.eq_of_dvd_pow ((dvd_pow_self _ k.succ_ne_zero).trans h.dvd)
  exact Subtype.ext (Prod.ext rfl
    (Nat.succ.inj (pow_injective_of_not_isUnit v.prime.not_isUnit v.ne_bot h)))

/-- Sum the unramified local values at prime powers of one integer norm,
dividing by their positive exponents. Ramified places contribute zero. -/
def rawWeight (χ : U𝔽) (m : ℕ) : ℂ :=
  letI := finite_primePowersAtNorm F m
  letI := Fintype.ofFinite {a : HeightOneSpectrum (𝓞 F) × ℕ // a.1.asIdeal.absNorm^(a.2+1) = m}
  ∑ a : {a : HeightOneSpectrum (𝓞 F) × ℕ // a.1.asIdeal.absNorm^(a.2+1) = m},
    (if (ideleClassNormTwist χ 0).IsUnramifiedAt a.val.1
      then (ideleClassNormTwist χ 0).localValue a.val.1 ^ (a.val.2+1) else 0) /
      ((a.val.2+1:ℕ):ℂ)

theorem rawWeight_eq_logCoefficient (χ : U𝔽) (m : ℕ) :
    rawWeight χ m = heckePrimePowerLogCoefficient χ m := by
  classical
  let := finite_primePowersAtNorm F m
  let := Fintype.ofFinite {a : HeightOneSpectrum (𝓞 F) × ℕ // a.1.asIdeal.absNorm^(a.2+1) = m}
  rw [heckePrimePowerLogCoefficient_eq_sum, finsum_eq_sum_of_fintype]
  unfold rawWeight
  apply Finset.sum_congr rfl
  intro a _
  rw [heckeIdealValue_prime_pow _ _ (Nat.succ_pos _)]

theorem norm_rawWeight_le_degree (χ : U𝔽) (m : ℕ) :
    ‖rawWeight χ m‖ ≤ (Module.finrank ℚ F:ℝ) := by
  rw [rawWeight_eq_logCoefficient]
  exact norm_logCoefficient_le χ m

/-- The raw real measurement at order `n` with last included prime-power norm `X`.
Its inputs are finite prime-ideal sums, field operations and real logarithms. -/
def finiteMoment (χ : U𝔽) (n X : ℕ) : ℝ :=
  ((n:ℂ)*(∑ m ∈ range (X+1), (rawWeight χ m/(m:ℂ)^2)*
    laguerre (-3*(Real.log m:ℂ)) n) +
    (if χ = 1 then (-1:ℂ)^(n-1)*((2:ℂ)^n-(2:ℂ)⁻¹^n) else 0)).re

/-- The real disk logarithmic derivative coefficient for positive order `n`. -/
def actualMoment (χ : U𝔽) (L : ℂ → ℂ) : ℕ → ℝ
  | 0 => 0
  | k+1 => (iteratedDeriv k (logDeriv (fun z ↦ cleared χ L (toHalf z))) 0/(k.factorial:ℂ)).re

theorem actualMoment_eq_of_pos (χ : U𝔽) (L : ℂ → ℂ) {n : ℕ} (hn : 0 < n) :
    actualMoment χ L n =
      (iteratedDeriv (n-1) (logDeriv (fun z ↦ cleared χ L (toHalf z))) 0/((n-1).factorial:ℂ)).re := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rfl

@[simp] theorem finiteMoment_zero (χ : U𝔽) (X : ℕ) : finiteMoment χ 0 X = 0 := by
  simp [finiteMoment]

private theorem actual_succ (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (k : ℕ) :
    actualMoment χ L (k+1) = ((k+1:ℂ)*coeff (eulerDisk χ) (k+1) +
      (if χ = 1 then (-1:ℂ)^k*((2:ℂ)^(k+1)-(2:ℂ)⁻¹^(k+1)) else 0)).re := by
  have hA : AnalyticAt ℂ (eulerDisk χ) 0 := euler_analytic χ (by norm_num)
  have hG := (logDeriv_cleared_germ χ L hL he).iteratedDeriv_eq k
  simp only [actualMoment]
  rw [hG]
  by_cases hc : χ = 1
  · simp only [hc,↓reduceIte] at hA ⊢
    rw [iteratedDeriv_fun_add hA.deriv.contDiffAt polar_analytic.contDiffAt, add_div]
    change (coeff (deriv _) k + coeff polar k).re = _
    rw [coeff_deriv,polar_coeff]
  · simp only [hc,↓reduceIte,add_zero]
    change (coeff (deriv _) k).re = _
    rw [coeff_deriv]

/-- Sharp pointwise error from the actual analytic disk coefficient to the finite
prime-power calculation, including the principal character's pole correction. -/
theorem abs_actualMoment_sub_finiteMoment_le (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {n X : ℕ} (hn : 0 < n) (hX : 0 < X) :
    |actualMoment χ L n - finiteMoment χ n X| ≤
      2 * (Module.finrank ℚ F:ℝ) * n * 5^n / Real.sqrt X := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hB := norm_coeff_sub_le (f := eulerDisk χ) (g := polyDisk χ X)
    (R := (1/5:ℝ)) (C := 2*(Module.finrank ℚ F:ℝ)/Real.sqrt X) (by norm_num)
    (fun z hz ↦ euler_analytic χ (by simpa using hz))
    (fun z hz ↦ poly_analytic χ X (by
      have hh : ‖z‖ ≤ 1/5 := by simpa using hz
      linarith))
    (fun z hz ↦ norm_LSeries_sub_partial (fun m _ ↦ norm_logCoefficient_le χ m)
      (re_toHalf_of_norm_le (by
        have hh : ‖z‖ = 1/5 := by simpa using hz
        exact hh.le)) hX) (k+1)
  rw [actual_succ χ L hL he, finiteMoment]
  simp only [rawWeight_eq_logCoefficient, ← poly_coeff]
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
  rw [← Complex.sub_re, add_sub_add_right_eq_sub, ← mul_sub]
  calc
    _ ≤ _ := Complex.abs_re_le_norm _
    _ = ((k:ℝ)+1)*‖coeff (eulerDisk χ) (k+1)-coeff (polyDisk χ X) (k+1)‖ := by
      rw [norm_mul, ← Nat.cast_one (R:=ℂ), ← Nat.cast_add, Complex.norm_natCast]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)
    _ = _ := by rw [one_div, inv_pow, div_inv_eq_mul]; ring

/-- The explicitly binomial form of the finite ideal calculation at positive order. -/
theorem finiteMoment_succ_eq_sum (χ : U𝔽) (k X : ℕ) :
    finiteMoment χ (k+1) X = ((k+1:ℂ)*(∑ m ∈ range (X+1), (rawWeight χ m/(m:ℂ)^2)*
      (∑ j ∈ range (k+1), (k.choose j:ℂ)*(-3*(Real.log m:ℂ))^(j+1)/((j+1).factorial:ℂ))) +
      (if χ=1 then (-1:ℂ)^k*((2:ℂ)^(k+1)-(2:ℂ)⁻¹^(k+1)) else 0)).re := by
  simp only [finiteMoment,laguerre_succ_eq_sum,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]

private theorem sqrt_square_pow (q n : ℕ) : Real.sqrt ((((q^2)^n:ℕ):ℝ)) = (q:ℝ)^n := by
  push_cast
  rw [pow_right_comm,Real.sqrt_sq (by positivity)]

/-- Norm cutoff `25^n` gives the linear absolute coefficient error. -/
theorem abs_actualMoment_sub_fin25 (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {n : ℕ} (hn : 0 < n) :
    |actualMoment χ L n - finiteMoment χ n (25^n)| ≤ 2*(Module.finrank ℚ F:ℝ)*n := by
  have h := abs_actualMoment_sub_finiteMoment_le χ L hL he hn (X := 25^n) (by positivity)
  have h25 := sqrt_square_pow 5 n
  norm_num only [Nat.reducePow,Nat.cast_ofNat] at h25
  rw [h25,mul_div_cancel_right₀ _ (by positivity)] at h
  exact h

/-- Norm cutoff `100^n` gives a summable absolute coefficient error. -/
theorem abs_actualMoment_sub_fin100 (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {n : ℕ} (hn : 0 < n) :
    |actualMoment χ L n - finiteMoment χ n (100^n)| ≤ 2*(Module.finrank ℚ F:ℝ)*n*(2:ℝ)⁻¹^n := by
  have h := abs_actualMoment_sub_finiteMoment_le χ L hL he hn (X := 100^n) (by positivity)
  have h100 := sqrt_square_pow 10 n
  norm_num only [Nat.reducePow,Nat.cast_ofNat] at h100
  rw [h100,mul_div_assoc,← div_pow,show (5/10:ℝ) = 2⁻¹ by norm_num] at h
  exact h

/-- Enlarging the norm cutoff preserves the linear error bound. -/
theorem abs_actualMoment_sub_of_cutoff (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {n X : ℕ} (hn : 0 < n) (hX : 25^n ≤ X) :
    |actualMoment χ L n - finiteMoment χ n X| ≤ 2*(Module.finrank ℚ F:ℝ)*n := by
  have hX0 : 0 < X := (pow_pos (by decide : 0 < 25) n).trans_le hX
  have hs : Real.sqrt (((25:ℕ)^n:ℕ):ℝ) ≤ Real.sqrt X := Real.sqrt_le_sqrt (by exact_mod_cast hX)
  have h25 := sqrt_square_pow 5 n
  norm_num only [Nat.reducePow,Nat.cast_ofNat] at h25
  rw [h25] at hs
  refine (abs_actualMoment_sub_finiteMoment_le χ L hL he hn hX0).trans ?_
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hX0))).mpr
  exact mul_le_mul_of_nonneg_left hs (by positivity)

private theorem signed_error (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (e : ℝ) (hes : |e| ≤ 1)
    {n X : ℕ} (hn : 0 < n) (hX : 25^n ≤ X) :
    |e*finiteMoment χ n X-e*actualMoment χ L n| ≤ 2*(Module.finrank ℚ F:ℝ)*n := by
  rw [← mul_sub,abs_mul,abs_sub_comm]
  exact (mul_le_of_le_one_left (abs_nonneg _) hes).trans
    (abs_actualMoment_sub_of_cutoff χ L hL he hn hX)

private theorem abs_sum_posPart_sub_le {x y : ℕ → ℝ} {D : ℝ}
    (h : ∀ n, 0 < n → |x n-y n| ≤ 2*D*n) (N : ℕ) :
    |(1+∑ k ∈ range N, max 0 (x (k+1))) - (1+∑ k ∈ range N, max 0 (y (k+1)))| ≤ D*N*(N+1) := by
  let P (f : ℕ → ℝ) (n : ℕ) := 1+∑ k ∈ range n, max 0 (f (k+1))
  have step (f : ℕ → ℝ) (n : ℕ) : P f (n+1) = P f n + max 0 (f (n+1)) := by
    simp only [P,sum_range_succ,add_assoc]
  change |P x N-P y N| ≤ _
  induction N with
  | zero => simp [P]
  | succ N ih =>
    have hd : |max 0 (x (N+1)) - max 0 (y (N+1))| ≤ 2*D*(N+1:ℕ) := by
      rw [max_comm 0 (x (N+1)),max_comm 0 (y (N+1))]
      exact (abs_max_sub_max_le_abs _ _ _).trans (h _ (Nat.succ_pos _))
    rw [step x,step y,add_sub_add_comm]
    exact (abs_add_le _ _).trans ((add_le_add ih hd).trans_eq (by push_cast; ring))

/-- The discrepancy in the two cumulative signed parts is bounded at every endpoint. -/
theorem abs_finite_prefix_sub_le (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (X : ℕ → ℕ) (hX : ∀ n, 0 < n → 25^n ≤ X n)
    (e : ℝ) (hes : |e| ≤ 1) (N : ℕ) :
    |(1+∑ k ∈ range N, max 0 (e*finiteMoment χ (k+1) (X (k+1)))) -
      (1+∑ k ∈ range N, max 0 (e*actualMoment χ L (k+1)))| ≤
        (Module.finrank ℚ F:ℝ)*N*(N+1) :=
  abs_sum_posPart_sub_le
    (x := fun n ↦ e*finiteMoment χ n (X n)) (y := fun n ↦ e*actualMoment χ L n)
    (fun n hn ↦ signed_error χ L hL he e hes hn (hX n hn)) N

/-- Fixing the order and letting the last included ideal norm tend to infinity
recovers the actual coefficient. -/
theorem tendsto_finiteMoment (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {n : ℕ} (hn : 0 < n) :
    Tendsto (finiteMoment χ n) atTop (𝓝 (actualMoment χ L n)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : Tendsto (fun X : ℕ ↦ 2*(Module.finrank ℚ F:ℝ)*n*5^n/Real.sqrt X) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) _ hb
  filter_upwards [eventually_gt_atTop 0] with X hX
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact abs_actualMoment_sub_finiteMoment_le χ L hL he hn hX

/-- For each fixed order, the raw Laguerre contributions are absolutely summable. -/
theorem summable_rawTerms (χ : U𝔽) (n : ℕ) :
    Summable (fun m : ℕ ↦ (rawWeight χ m/(m:ℂ)^2)*laguerre (-3*(Real.log m:ℂ)) n) := by
  let D := (Module.finrank ℚ F:ℝ)
  have hpow := Real.summable_nat_rpow.mpr (by norm_num : (-(3/2):ℝ) < -1)
  apply (hpow.mul_left (5^n*D)).of_norm_bounded
  intro m
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  have hm₁ : (1:ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
  have hm₀ : (0:ℝ) < m := zero_lt_one.trans_le hm₁
  let w := rawWeight χ
  let f (z : ℂ) := LSeries.term w (toHalf z) m
  have hf : AnalyticOnNhd ℂ f (closedBall 0 (1/5)) := by
    intro z hz
    have hz' : ‖z‖ ≤ 1/5 := by simpa using hz
    have hd : Differentiable ℂ (fun s ↦ LSeries.term w s m) :=
      fun s ↦ (LSeries.hasDerivAt_term _ m s).differentiableAt
    exact (hd.analyticAt _).comp (chart_analytic (by linarith))
  have hb (z : ℂ) (hz : z ∈ sphere 0 (1/5)) : ‖f z‖ ≤ D*(m:ℝ)^(-(3/2):ℝ) := by
    have hz' : ‖z‖ = 1/5 := by simpa using hz
    dsimp [f]
    rw [LSeries.term_of_ne_zero hm,norm_div,← Complex.ofReal_natCast m,
      Complex.norm_cpow_eq_rpow_re_of_pos hm₀,div_eq_mul_inv,← Real.rpow_neg hm₀.le]
    exact mul_le_mul (norm_rawWeight_le_degree χ m)
      (Real.rpow_le_rpow_of_exponent_le hm₁ (neg_le_neg (re_toHalf_of_norm_le hz'.le)))
      (Real.rpow_nonneg hm₀.le _) (Nat.cast_nonneg _)
  have hC := norm_coeff_sub_le (f := f) (g := fun _ ↦ 0) (R := 1/5)
    (C := D*(m:ℝ)^(-(3/2):ℝ)) (by norm_num) hf (fun _ _ ↦ analyticAt_const)
    (fun z hz ↦ by simpa using hb z hz) n
  have hzero : coeff (fun _ : ℂ ↦ 0) n = 0 := by
    cases n <;> simp [coeff]
  rw [hzero,sub_zero] at hC
  change ‖coeff (fun z ↦ LSeries.term w (toHalf z) m) n‖ ≤ _ at hC
  rw [term_coeff] at hC
  exact hC.trans_eq (by rw [one_div,inv_pow,div_inv_eq_mul]; ring)

/-- Exact absolutely convergent Euler--Laguerre formula for the genuine disk
coefficient. The principal term is added before taking either signed part. -/
theorem actualMoment_eq_tsum (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {n : ℕ} (hn : 0 < n) :
    actualMoment χ L n = ((n:ℂ)*(∑' m : ℕ, (rawWeight χ m/(m:ℂ)^2)*
      laguerre (-3*(Real.log m:ℂ)) n) +
      (if χ = 1 then (-1:ℂ)^(n-1)*((2:ℂ)^n-(2:ℂ)⁻¹^n) else 0)).re := by
  have h := (summable_rawTerms χ n).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique (tendsto_finiteMoment χ L hL he hn)
    (Complex.continuous_re.continuousAt.tendsto.comp ((h.const_mul (n:ℂ)).add_const _))

/-- A uniform signed estimate at every index for the chosen ordinary continuation.
Both sequences have been padded by zero at index zero. -/
theorem abs_canonical_signed_error (χ : U𝔽) (X : ℕ → ℕ) (hX : ∀ n, 0 < n → 25^n ≤ X n)
    (e : ℝ) (hes : |e| ≤ 1) (n : ℕ) :
    |e*finiteMoment χ n (X n) - e*actualMoment χ (finiteHeckeL_exists_continuation χ).choose n| ≤
      (2*(Module.finrank ℚ F:ℝ))*n := by
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  cases n with
  | zero => simp [actualMoment]
  | succ k => exact signed_error χ _ hL he e hes k.succ_pos (hX _ k.succ_pos)

end RiemannMasullo.HeckeLaguerre
