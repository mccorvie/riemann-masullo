module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b_HalfPlaneJensen
import RiemannMasullo.Ch06_LocalGlobal.Sec3
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.HeckeLFunction
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A bounded disk model of the ordinary finite Hecke L-function

The Cayley chart takes the unit disk to the right of the critical line. For the principal
character, its pole at one becomes a removable point at −1/2 after multiplication by the
disk factor. Normalizing the meromorphic product fills that value. Polynomial growth on
the fixed strip and the absolutely convergent Euler series on its right give a power of
the distance to the exceptional boundary point that bounds the filled function.
-/

@[expose] public noncomputable section

open Complex Filter Function IsDedekindDomain Metric NumberField Set
open scoped Asymptotics NNReal Topology

namespace RiemannMasullo.HeckeDiskNormalization

variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽
local notation "Hp" => (Complex.re ⁻¹' Ioi (1 : ℝ))

open HeckeHalfPlaneJensen HalfPlaneJensen

open scoped Classical in
/-- The rational factor cancelling the possible pole at one. -/
def halfFactor (χ : U𝔽) (s : ℂ) : ℂ := if χ = 1 then (s - 1)/s else 1

/-- The canonical meromorphic normal form of the pole-cleared continuation. -/
def cleared (χ : U𝔽) (L : ℂ → ℂ) : ℂ → ℂ := toMeromorphicNFOn (halfFactor χ * L) univ

theorem meromorphic_factor (χ : U𝔽) : MeromorphicOn (halfFactor χ) univ := by
  classical
  by_cases hc : χ = 1
  · intro s _
    change MeromorphicAt (fun z : ℂ ↦ if χ = 1 then (z-1)/z else 1) s
    simp only [hc, ite_true]
    fun_prop
  · intro s _
    change MeromorphicAt (fun z : ℂ ↦ if χ = 1 then (z-1)/z else 1) s
    simp only [hc, ite_false]
    fun_prop

theorem meromorphic_product (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) :
    MeromorphicOn (halfFactor χ * L) univ :=
  (meromorphic_factor χ).mul hL.meromorphicOn

private theorem factor_analytic (χ : U𝔽) {s : ℂ} (hs : s ≠ 0) : AnalyticAt ℂ (halfFactor χ) s := by
  classical
  by_cases hc : χ = 1
  · change AnalyticAt ℂ (fun z : ℂ ↦ if χ = 1 then (z-1)/z else 1) s
    simp only [hc, ite_true]
    exact (show AnalyticAt ℂ (fun z : ℂ ↦ z-1) s by fun_prop).div analyticAt_id hs
  · change AnalyticAt ℂ (fun z : ℂ ↦ if χ = 1 then (z-1)/z else 1) s
    simp only [hc, ite_false]
    exact analyticAt_const

private theorem finite_analytic_of_regular (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {s : ℂ} (hs : 0 < s.re) (hp : ¬(χ = 1 ∧ s = 1)) :
    AnalyticAt ℂ L s := by
  apply (hL (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_contra hh
  have hneg := lt_of_not_ge hh
  rw [finite_order_eq_completed χ L hL he s hs] at hneg
  have ho : HeckeHalfPlaneJensen.order χ s < 0 := by
    rw [HeckeHalfPlaneJensen.order, MeromorphicOn.divisor_apply (explicitFormulaCompletedHeckeL_spec χ).1.meromorphicOn (mem_univ _)]
    generalize meromorphicOrderAt (explicitFormulaCompletedHeckeL χ) s = m at hneg ⊢
    cases m with
    | top => simp at hneg
    | coe i => exact WithTop.coe_lt_coe.mp hneg
  obtain ⟨htr, hzero | hone⟩ := idelicExplicitFormula_chart_poles τ hτ χ hχ s ho
  · simp [hzero] at hs
  · exact hp ⟨htr, hone⟩

theorem cleared_agrees (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {s : ℂ} (hs : 0 < s.re) (hp : ¬(χ = 1 ∧ s = 1)) :
    cleared χ L s = halfFactor χ s * L s := by
  have hA := finite_analytic_of_regular τ hτ χ hχ L hL he hs hp
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  have hprod := (factor_analytic χ hs0).mul hA
  rw [cleared, toMeromorphicNFOn_eq_toMeromorphicNFAt (meromorphic_product χ L hL) (mem_univ _),
    toMeromorphicNFAt_eq_self.mpr hprod.meromorphicNFAt]
  rfl

private theorem principal_order_one (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL (1 : U𝔽) s) : meromorphicOrderAt L 1 = -1 := by
  rw [finite_order_eq_completed (1 : U𝔽) L hL he 1 (by norm_num)]
  have h := (idelicExplicitFormula_trivial_poles (F := F)).2
  rw [MeromorphicOn.divisor_apply (explicitFormulaCompletedHeckeL_spec (1 : U𝔽)).1.meromorphicOn (mem_univ _)] at h
  generalize meromorphicOrderAt (explicitFormulaCompletedHeckeL (1 : U𝔽)) 1 = o at h ⊢
  cases o with
  | top => norm_num at h
  | coe i => simpa [WithTop.untop₀_coe] using congrArg (fun k : ℤ ↦ (k : WithTop ℤ)) h

theorem cleared_order_one (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL (1 : U𝔽) s) :
    meromorphicOrderAt (cleared (1 : U𝔽) L) 1 = 0 := by
  change meromorphicOrderAt (toMeromorphicNFOn (halfFactor (1 : U𝔽) * L) univ) 1 = 0
  rw [meromorphicOrderAt_toMeromorphicNFOn (meromorphic_product _ L hL) (mem_univ _),
    meromorphicOrderAt_mul ((meromorphic_factor (1 : U𝔽)) _ (mem_univ _)) (hL (mem_univ _)).meromorphicAt,
    principal_order_one L hL he]
  have hfa : halfFactor (1 : U𝔽) = (fun z : ℂ ↦ z-1) / id := by
    funext z
    simp [halfFactor]
  rw [hfa, meromorphicOrderAt_div (f := fun z : ℂ ↦ z-1) (g := id) (by fun_prop) (by fun_prop),
    meromorphicOrderAt_id_sub_const]
  have hid : meromorphicOrderAt (id : ℂ → ℂ) 1 = 0 :=
    (analyticAt_id (𝕜 := ℂ)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr one_ne_zero
  rw [hid]
  norm_num

theorem cleared_principal_nonzero (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL (1 : U𝔽) s) : cleared (1 : U𝔽) L 1 ≠ 0 :=
  (meromorphicNFOn_toMeromorphicNFOn _ _ (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mp (cleared_order_one L hL he)

theorem cleared_analytic (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (cleared χ L) s := by
  have hN : MeromorphicNFOn (cleared χ L) univ := meromorphicNFOn_toMeromorphicNFOn _ _
  apply (hN (mem_univ _)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_cases hp : χ = 1 ∧ s = 1
  · obtain ⟨rfl, rfl⟩ := hp
    exact (cleared_order_one L hL he).ge
  · have hA := finite_analytic_of_regular τ hτ χ hχ L hL he hs hp
    have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
    rw [cleared, meromorphicOrderAt_toMeromorphicNFOn (meromorphic_product _ L hL) (mem_univ _)]
    exact ((factor_analytic χ hs0).mul hA).meromorphicOrderAt_nonneg

theorem norm_halfFactor_le (χ : U𝔽) {s : ℂ} (hs : 1/2 ≤ s.re) : ‖halfFactor χ s‖ ≤ 1 := by
  classical
  by_cases hc : χ = 1
  · have hs0 : s ≠ 0 := fun h ↦ by norm_num [h] at hs
    have h1 : ‖s - 1‖^2 ≤ ‖s‖^2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
        Complex.one_im, sub_zero]
      nlinarith
    rw [halfFactor, ite_eq_left hc, norm_div, div_le_one (norm_pos_iff.mpr hs0)]
    nlinarith [norm_nonneg (s - 1), norm_nonneg s]
  · simp [halfFactor, hc]

private theorem euler_majorant (χ : U𝔽) (L : ℂ → ℂ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {r : ℝ} (hr : 1 < r) :
    ∃ B : ℝ, ∀ s : ℂ, r ≤ s.re → ‖L s‖ ≤ B := by
  let c := (ideleClassNormTwist χ 0).LFunction
  have hsum : Summable (fun n ↦ ‖LSeries.term c (r : ℂ) n‖) :=
    (finiteHeckeL_seriesSummable χ ⟨(r : ℂ), by simpa using hr⟩).norm
  refine ⟨∑' n, ‖LSeries.term c (r : ℂ) n‖, fun s hs ↦ ?_⟩
  have hs' : 1 < s.re := hr.trans_le hs
  rw [show L s = finiteHeckeL χ ⟨s, hs'⟩ from he ⟨s, hs'⟩]
  change ‖∑' n, LSeries.term c s n‖ ≤ _
  have hss : Summable (fun n ↦ ‖LSeries.term c s n‖) :=
    (finiteHeckeL_seriesSummable χ ⟨s, hs'⟩).norm
  exact (norm_tsum_le_tsum_norm hss).trans
    (hss.tsum_le_tsum (LSeries.norm_term_le_of_re_le_re c (by simpa using hs)) hsum)

theorem finiteHeckeL_real_tendsto_one (χ : U𝔽) (L : ℂ → ℂ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    Tendsto (fun t : ℝ ↦ L (t : ℂ)) atTop (𝓝 1) := by
  let ψ := ideleClassNormTwist χ 0
  have hCoeff : ψ.LFunction 1 = 1 := by
    have hLocal (v : HeightOneSpectrum (𝓞 F)) : ψ.localEulerFactor v 1 = 1 := by
      simp [HeckeCharacter.localEulerFactor, HeckeCharacter.localPowerSeries,
        ArithmeticFunction.ofPowerSeries_apply_one, PowerSeries.constantCoeff_invOfUnit]
    obtain ⟨S, hS⟩ := (heckeLocalEulerFactor_eventually_prod_eq ψ 1).exists
    rw [← hS]
    clear hS
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | insert v S hv ih =>
        rw [Finset.prod_insert hv, ArithmeticFunction.mul_apply_one, hLocal, ih, one_mul]
  have hA : LSeries.abscissaOfAbsConv ψ.LFunction < ⊤ :=
    (finiteHeckeL_seriesSummable χ ⟨2, by change 1 < (2:ℂ).re; norm_num⟩).abscissaOfAbsConv_le.trans_lt
      (EReal.coe_lt_top _)
  rw [← hCoeff]
  apply (LSeries.tendsto_atTop hA).congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with t ht
  exact (he ⟨(t:ℂ), by change 1 < (t:ℂ).re; simpa using ht⟩).symm

/-- Clearing the principal pole gives a single polynomial bound on the whole closed half-plane. -/
theorem cleared_polynomial_bound (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    ∃ (N : ℕ) (K : ℝ), 0 < N ∧ 1 ≤ K ∧ ∀ s : ℂ, 1/2 ≤ s.re →
      ‖cleared χ L s‖ ≤ K * ‖s + 1‖ ^ N := by
  let S := Icc (1/2 : ℝ) (3/2)
  let ℓ := comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' S)
  obtain ⟨E, hE, hO⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hL he (1/2) (3/2) (by norm_num)
  have hsmall : cleared χ L =O[ℓ] L := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    have ht : Tendsto (abs ∘ Complex.im) ℓ atTop := tendsto_inf_left tendsto_comap
    have hin : ∀ᶠ s : ℂ in ℓ, s.re∈S := eventually_inf_principal.mpr (Eventually.of_forall fun s hs ↦ hs)
    filter_upwards [ht.eventually_ge_atTop 1, hin] with s ht hs
    have hn : s ≠ 1 := by rintro rfl; norm_num [Function.comp_def] at ht
    rw [cleared_agrees τ hτ χ hχ L hL he (by linarith [hs.1]) (fun h ↦ hn h.2), norm_mul, one_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_halfFactor_le χ hs.1)
  have hcont : ContinuousOn (cleared χ L) (Complex.re ⁻¹' S) :=
    fun s hs ↦ (cleared_analytic τ hτ χ hχ L hL he (by linarith [hs.1])).continuousAt.continuousWithinAt
  obtain ⟨C, hC, hmid⟩ := exists_norm_le_mul_norm_sub_rpow (K:=S) isCompact_Icc hcont hE.le
    (hsmall.trans hO) (x0 := -1) (fun σ hσ ↦ by linarith [hσ.1])
  obtain ⟨B, hB⟩ := euler_majorant χ L he (r:=3/2) (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_ge E
  let K := max 1 (max C B)
  have hCK : C ≤ K := (le_max_left C B).trans (le_max_right _ _)
  have hBK : B ≤ K := (le_max_right C B).trans (le_max_right _ _)
  have hK : 1 ≤ K := le_max_left _ _
  refine ⟨n+1, K, by omega, hK, fun s hs ↦ ?_⟩
  have hx : 1 ≤ ‖s + 1‖ := calc
    1 ≤ (s + 1).re := by simp; linarith
    _ ≤ |(s + 1).re| := le_abs_self _
    _ ≤ ‖s + 1‖ := abs_re_le_norm _
  have hpow : ‖s + 1‖^E ≤ ‖s + 1‖^(n+1) := by
    rw [←Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hx
    push_cast
    linarith
  by_cases hm : s.re ≤ 3/2
  · have hmid' := hmid s ⟨hs, hm⟩
    simp only [ofReal_neg, ofReal_one, sub_neg_eq_add] at hmid'
    exact hmid'.trans (mul_le_mul hCK hpow (Real.rpow_nonneg (norm_nonneg _) _) (by linarith))
  · have hr : 3/2 < s.re := lt_of_not_ge hm
    have hr1 : s ≠ 1 := by rintro rfl; norm_num at hr
    rw [cleared_agrees τ hτ χ hχ L hL he (by linarith) (fun h ↦ hr1 h.2), norm_mul]
    calc ‖halfFactor χ s‖ * ‖L s‖ ≤ ‖L s‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (norm_halfFactor_le χ hs)
      _ ≤ B := hB s hr.le
      _ ≤ K := hBK
      _ ≤ K * ‖s + 1‖^(n+1) := le_mul_of_one_le_right (by linarith) (one_le_pow₀ hx)

theorem chart_add_one {z : ℂ} (hz : 1 - z ≠ 0) : toHalf z + 1 = 3/(1 - z) := by
  unfold toHalf
  field_simp
  ring

theorem chart_analytic_of_ne_one {z : ℂ} (hz : z ≠ 1) : AnalyticAt ℂ toHalf z := by
  exact (show AnalyticAt ℂ (fun z : ℂ ↦ 2 + z) z by fun_prop).div
    (show AnalyticAt ℂ (fun z : ℂ ↦ 1 - z) z by fun_prop) (sub_ne_zero.mpr hz.symm)

theorem closed_chart_re {z : ℂ} (hz : ‖z‖ ≤ 1) (h1 : z ≠ 1) : 1/2 ≤ (toHalf z).re := by
  have hn := sub_ne_zero.mpr h1.symm
  have hd : toHalf z + 1 ≠ 0 := by rw [chart_add_one hn]; exact div_ne_zero (by norm_num) hn
  rw [←toDisk_toHalf hn, toDisk, norm_div, div_le_one (norm_pos_iff.mpr hd)] at hz
  have hs := pow_le_pow_left₀ (norm_nonneg _) hz 2
  norm_num [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im] at hs
  nlinarith

open scoped Classical in
/-- The principal-character rational factor in disk coordinates. -/
def diskFactor (χ : U𝔽) (z : ℂ) : ℂ := ((1 + 2 * z)/(2 + z)) ^ (if χ = 1 then 1 else 0 : ℕ)

theorem factor_chart (χ : U𝔽) {z : ℂ} (hz : ‖z‖ ≤ 1) (h1 : z ≠ 1) :
    halfFactor χ (toHalf z) = diskFactor χ z := by
  classical
  by_cases hχ : χ = 1
  · have hn := sub_ne_zero.mpr h1.symm
    have hs : toHalf z ≠ 0 := fun h ↦ by have hh := closed_chart_re hz h1; norm_num [h] at hh
    have hd : 2 + z ≠ 0 := fun h ↦ hs (by simp [toHalf, h])
    simp only [halfFactor, diskFactor, ite_eq_left hχ, pow_one]
    unfold toHalf
    field_simp
    ring
  · simp [halfFactor, diskFactor, hχ]

/-- At a zero of the rational pole-cancelling factor we take the removable analytic value. -/
def normalized (χ : U𝔽) (L : ℂ → ℂ) (a : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  (a:ℂ) * ((1 - z)/3)^N * cleared χ L (toHalf z)

/-- Pointwise disk formula before filling the removable principal pole. -/
def raw (χ : U𝔽) (L : ℂ → ℂ) (a : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  (a:ℂ) * ((1 - z)/3)^N * diskFactor χ z * L (toHalf z)

theorem normalized_eq_raw (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (a : ℝ) (N : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ 1) (h1 : z ≠ 1) (hp : ¬(χ = 1 ∧ z = -(1/2))) :
    normalized χ L a N z = raw χ L a N z := by
  have hs := closed_chart_re hz h1
  have hreg : ¬(χ = 1 ∧ toHalf z = 1) := by
    rintro ⟨hχ', h⟩
    apply hp
    refine ⟨hχ', ?_⟩
    have heq := toDisk_toHalf (sub_ne_zero.mpr h1.symm)
    simpa [h] using heq.symm
  rw [normalized, raw, cleared_agrees τ hτ χ hχ L hL he (by linarith) hreg, factor_chart χ hz h1]
  ring

/-- The two definitions agree everywhere on the boundary, including the common default at one. -/
theorem normalized_boundary (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (a : ℝ) {N : ℕ} (hN : 0 < N) {z : ℂ} (hz : ‖z‖ = 1) :
    normalized χ L a N z = raw χ L a N z := by
  by_cases h1 : z = 1
  · simp [h1, normalized, raw, zero_pow hN.ne']
  apply normalized_eq_raw τ hτ χ hχ L hL he a N hz.le h1
  rintro ⟨_, rfl⟩
  norm_num [norm_div] at hz

theorem normalized_principal_filled (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL (1 : U𝔽) s) {a : ℝ} (ha : 0 < a) (N : ℕ) :
    normalized (1 : U𝔽) L a N (-(1/2)) ≠ 0 := by
  have h : toHalf (-(1/2))=1 := by norm_num [toHalf]
  rw [normalized, h]
  apply mul_ne_zero _ (cleared_principal_nonzero L hL he)
  apply mul_ne_zero (ofReal_ne_zero.mpr ha.ne')
  exact pow_ne_zero N (by norm_num)

private theorem factor_nonzero_two (χ : U𝔽) : halfFactor χ 2 ≠ 0 := by
  classical
  by_cases h : χ = 1 <;> norm_num [halfFactor, h]

theorem normalized_analytic (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (a : ℝ) (N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) (h1 : z ≠ 1) :
    AnalyticAt ℂ (normalized χ L a N) z := by
  have hs := closed_chart_re hz h1
  exact (show AnalyticAt ℂ (fun u : ℂ ↦ (a:ℂ) * ((1-u)/3)^N) z by fun_prop).mul
    ((cleared_analytic τ hτ χ hχ L hL he (by linarith)).comp (chart_analytic_of_ne_one h1))

theorem normalized_finite_order (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {a : ℝ} (ha : 0 < a) (N : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ 1) (h1 : z ≠ 1) : analyticOrderAt (normalized χ L a N) z ≠ ⊤ := by
  let A := cleared χ L
  have hA : MeromorphicNFOn A univ := meromorphicNFOn_toMeromorphicNFOn _ _
  let s₂ : Hp := ⟨2, by change 1 < (2:ℂ).re; norm_num⟩
  have h2 : L 2 ≠ 0 := (he s₂).trans_ne (finiteHeckeL_ne_zero_of_one_lt_re χ s₂)
  have hA2 : A 2 ≠ 0 := by
    rw [show A 2 = halfFactor χ 2 * L 2 from
      cleared_agrees τ hτ χ hχ L hL he (by norm_num) (by norm_num)]
    exact mul_ne_zero (factor_nonzero_two χ) h2
  have horder2 := (hA (mem_univ (2:ℂ))).meromorphicOrderAt_eq_zero_iff.mpr hA2
  have hfinite := hA.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2:ℂ)) (mem_univ (toHalf z)) (by rw [horder2]; simp)
  let u := fun v : ℂ ↦ (a:ℂ)*((1-v)/3)^N
  have hu : AnalyticAt ℂ u z := by dsimp [u]; fun_prop
  have hn := sub_ne_zero.mpr h1.symm
  have hunit : u z ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr ha.ne') (pow_ne_zero N (div_ne_zero hn (by norm_num)))
  have hd : deriv toHalf z ≠ 0 := by rw [(chart_hasDerivAt hn).deriv]; exact div_ne_zero (by norm_num) (pow_ne_zero 2 hn)
  have hf : meromorphicOrderAt (normalized χ L a N) z ≠ ⊤ := by
    change meromorphicOrderAt (u * (A ∘ toHalf)) z ≠ ⊤
    rwa [meromorphicOrderAt_mul_of_ne_zero hu hunit, meromorphicOrderAt_comp_of_deriv_ne_zero (chart_analytic_of_ne_one h1) hd]
  intro h
  rw [(normalized_analytic τ hτ χ hχ L hL he a N hz h1).meromorphicOrderAt_eq, h] at hf
  exact hf rfl

theorem normalized_bound {χ : U𝔽} {L : ℂ → ℂ} {N : ℕ} (hN : 0 < N) {K : ℝ} (hK : 1 ≤ K)
    (hA : ∀ s : ℂ, 1/2 ≤ s.re → ‖cleared χ L s‖ ≤ K*‖s + 1‖^N) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖normalized χ L K⁻¹ N z‖ ≤ 1 := by
  by_cases h1 : z = 1
  · simp [h1, normalized, zero_pow hN.ne']
  have hn := sub_ne_zero.mpr (Ne.symm h1)
  have hcancel : ‖(1 - z)/3‖ * ‖toHalf z + 1‖ = 1 := by
    rw [←norm_mul, chart_add_one hn]
    have heq : ((1 - z)/3) * (3/(1 - z))=1 := by field_simp
    rw [heq, norm_one]
  have hscale : 0 < K := by linarith
  rw [normalized, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hscale)]
  calc K⁻¹ * ‖(1 - z)/3‖^N * ‖cleared χ L (toHalf z)‖
      ≤ K⁻¹ * ‖(1 - z)/3‖^N * (K*‖toHalf z + 1‖^N) := by
        gcongr
        exact hA _ (closed_chart_re hz h1)
    _ = (K⁻¹*K) * (‖(1 - z)/3‖*‖toHalf z + 1‖)^N := by rw [mul_pow]; ring
    _ = 1 := by rw [hcancel, one_pow, inv_mul_cancel₀ hscale.ne', one_mul]

private theorem radial_distance_tendsto :
    Tendsto (fun q : ℝ ↦ 1 - q) (𝓝[<] 1) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Tendsto (fun q : ℝ ↦ 1 - q) (𝓝[<] 1) (𝓝 (1-1 : ℝ)) :=
      (tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_id.mono_left nhdsWithin_le_nhds)
    simpa using h
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact sub_pos.mpr (show q < 1 from hq)

/-- The pole-cleared actual Euler series tends to one along the radius ending at z = 1. -/
theorem radial_cleared_tendsto_one (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    Tendsto (fun q : ℝ ↦ cleared χ L (toHalf q)) (𝓝[<] 1) (𝓝 1) := by
  let ℓ := 𝓝[<] (1:ℝ)
  let x := fun q : ℝ ↦ 3*(1 - q)⁻¹-1
  have hx : Tendsto x ℓ atTop :=
    (tendsto_atTop_add_const_right _ (-1:ℝ) (radial_distance_tendsto.inv_tendsto_nhdsGT_zero.const_mul_atTop
      (by norm_num : 0<(3:ℝ))))
  have hq : ∀ᶠ q : ℝ in ℓ, q<1 := self_mem_nhdsWithin
  have hp : ∀ᶠ q : ℝ in ℓ, 0<q := (eventually_gt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  have hcast : ∀ᶠ q : ℝ in ℓ, (x q:ℂ)=toHalf q := by
    filter_upwards [hq] with q hq
    have hn : (1:ℂ)-(q:ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hq.ne')
    simp only [x, toHalf, ofReal_sub, ofReal_mul, ofReal_inv, ofReal_ofNat, ofReal_one]
    field_simp
    ring
  have hLlim : Tendsto (fun q : ℝ ↦ L (toHalf q)) ℓ (𝓝 1) :=
    ((finiteHeckeL_real_tendsto_one χ L he).comp hx).congr' (hcast.mono fun q h ↦ congrArg L h)
  have hdisk : ContinuousAt (diskFactor χ) (1:ℂ) := by
    unfold diskFactor
    fun_prop (disch := norm_num)
  have hvalue : diskFactor χ 1 = 1 := by
    norm_num [diskFactor, show (1+2*(1:ℂ))/(2+1)=1 by norm_num]
  have hcomplex : Tendsto (fun q : ℝ ↦ (q:ℂ)) ℓ (𝓝 1) := by
    simpa using (Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds (s:=Iio 1))
  have hdlim := hdisk.tendsto.comp hcomplex
  rw [hvalue] at hdlim
  have hprod := hdlim.mul hLlim
  rw [one_mul] at hprod
  apply hprod.congr'
  filter_upwards [hq, hp, hcast, hx.eventually_gt_atTop 2] with q hq hp hcast hxq
  have hn : ‖(q:ℂ)‖ ≤ 1 := by simpa [Complex.norm_real, abs_of_pos hp] using hq.le
  have hq' : (q:ℂ)≠1 := by exact_mod_cast hq.ne
  have hs1 : toHalf (q:ℂ)≠1 := by rw [←hcast]; exact_mod_cast (by linarith : x q ≠ 1)
  have hs := closed_chart_re hn hq'
  rw [cleared_agrees τ hτ χ hχ L hL he (by linarith) (fun h ↦ hs1 h.2),
    factor_chart χ hn hq']
  rfl

/-- The radial approach loses no logarithmic mass at the exceptional boundary point. -/
theorem radial_normalized (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {a : ℝ} (ha : 0 < a) (N : ℕ) :
    (∀ᶠ q : ℝ in 𝓝[<] 1, normalized χ L a N q ≠ 0) ∧
    Tendsto (fun q : ℝ ↦ (1 - q)*|Real.log ‖normalized χ L a N q‖|) (𝓝[<] 1) (𝓝 0) := by
  let ℓ := 𝓝[<] (1:ℝ)
  let b := (a:ℂ) * (3:ℂ)⁻¹^N
  let U := fun q : ℝ ↦ b * cleared χ L (toHalf q)
  have hb : b ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr ha.ne') (pow_ne_zero _ (inv_ne_zero (by norm_num)))
  have hU : Tendsto U ℓ (𝓝 b) := by
    simpa [U] using (radial_cleared_tendsto_one τ hτ χ hχ L hL he).const_mul b
  have hUne : ∀ᶠ q : ℝ in ℓ, U q ≠ 0 := hU.eventually_ne hb
  have hq : ∀ᶠ q : ℝ in ℓ, q<1 := self_mem_nhdsWithin
  have hx : Tendsto (fun q : ℝ ↦ 1 - q) ℓ (𝓝 0) := radial_distance_tendsto.mono_right nhdsWithin_le_nhds
  have heq (q : ℝ) : normalized χ L a N q = ((↑(1 - q):ℂ)^N) * U q := by
    simp only [normalized, U, b, ofReal_sub, ofReal_one, div_eq_mul_inv, mul_pow]
    ring
  constructor
  · filter_upwards [hq, hUne] with q hq hU
    rw [heq]
    exact mul_ne_zero (pow_ne_zero N (ofReal_ne_zero.mpr (sub_pos.mpr hq).ne')) hU
  have hfixed : Tendsto (fun q : ℝ ↦ (1 - q)*Real.log ‖U q‖) ℓ (𝓝 0) := by
    simpa using hx.mul ((Real.continuousAt_log (norm_ne_zero_iff.mpr hb)).tendsto.comp hU.norm)
  have hw : Tendsto (fun q : ℝ ↦ (1 - q)*Real.log (1 - q)) ℓ (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_mul_log.tendsto 0).comp hx
  have hinner : Tendsto (fun q : ℝ ↦ (1 - q)*Real.log ‖normalized χ L a N q‖) ℓ (𝓝 0) := by
    have hsum := (hw.const_mul (N:ℝ)).add hfixed
    simp only [mul_zero, add_zero] at hsum
    apply hsum.congr'
    filter_upwards [hq, hUne] with q hq hU
    have hpos := sub_pos.mpr hq
    rw [heq, norm_mul (↑(1 - q)^N : ℂ) (U q), norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
      Real.log_mul (pow_ne_zero N hpos.ne') (norm_ne_zero_iff.mpr hU), Real.log_pow]
    ring
  have habs := hinner.abs
  rw [abs_zero] at habs
  apply habs.congr'
  filter_upwards [hq] with q hq
  exact (abs_mul _ _).trans (by rw [abs_of_pos (sub_pos.mpr hq)])

/-- The pole-cancelling rational factor has modulus one on the boundary. -/
theorem diskFactor_norm_boundary (χ : U𝔽) {z : ℂ} (hz : ‖z‖ = 1) : ‖diskFactor χ z‖=1 := by
  have h2 : 2 + z ≠ 0 := by
    intro h
    have he : z = -2 := by linear_combination h
    norm_num [he] at hz
  have hs : z.re*z.re+z.im*z.im=1 := by
    have sq : ‖z‖^2=1 := by rw [hz]; norm_num
    rwa [Complex.sq_norm, Complex.normSq_apply] at sq
  have hp : ‖1 + 2 * z‖^2=‖2 + z‖^2 := by
    norm_num [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im]
    nlinarith
  have he : ‖1 + 2 * z‖=‖2 + z‖ := by nlinarith [norm_nonneg (1 + 2 * z), norm_nonneg (2 + z)]
  rw [diskFactor, norm_pow, norm_div, he, div_self (norm_ne_zero_iff.mpr h2), one_pow]

theorem normalized_boundary_norm (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {a : ℝ} (ha : 0 < a) {N : ℕ} (hN : 0 < N)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖normalized χ L a N z‖ = a * ‖(1 - z)/3‖ ^ N * ‖L (toHalf z)‖ := by
  rw [normalized_boundary τ hτ χ hχ L hL he a hN hz, raw]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha,
    diskFactor_norm_boundary χ hz, mul_one]

theorem normalized_raw_outer (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (a : ℝ) (N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) (h1 : z ≠ 1)
    (ho : 1/2 < ‖z‖) : normalized χ L a N z = raw χ L a N z := by
  apply normalized_eq_raw τ hτ χ hχ L hL he a N hz h1
  rintro ⟨_, h⟩
  norm_num [h, norm_div] at ho

theorem normalized_at_zero (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (a : ℝ) (N : ℕ) :
    normalized χ L a N 0 = (a:ℂ) * (1/3)^N * diskFactor χ 0 * L 2 := by
  rw [normalized_eq_raw τ hτ χ hχ L hL he a N (by simp) zero_ne_one (by norm_num)]
  simp [raw]

theorem normalized_zero_ne (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {a : ℝ} (ha : 0 < a) (N : ℕ) :
    normalized χ L a N 0 ≠ 0 := by
  let s₂ : Hp := ⟨2, by change 1 < (2:ℂ).re; norm_num⟩
  have h2 : L 2 ≠ 0 := (he s₂).trans_ne (finiteHeckeL_ne_zero_of_one_lt_re χ s₂)
  rw [normalized_at_zero τ hτ χ hχ L hL he a N]
  apply mul_ne_zero _ h2
  apply mul_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr ha.ne') (pow_ne_zero _ (by norm_num)))
  exact pow_ne_zero _ (by norm_num)

/-- The full positive radius maps into the absolute Euler half-plane. -/
theorem radial_normalized_ne_zero_of_nonneg (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {a : ℝ} (ha : 0 < a) (N : ℕ) {q : ℝ}
    (h0 : 0 ≤ q) (h1 : q < 1) : normalized χ L a N q ≠ 0 := by
  classical
  have hq : toHalf (q : ℂ) = (((2 + q)/(1 - q) : ℝ) : ℂ) := by simp [toHalf]
  have hs : 1 < (toHalf (q : ℂ)).re := by
    rw [hq, ofReal_re, lt_div_iff₀ (sub_pos.mpr h1)]
    linarith
  have hs1 : toHalf (q : ℂ) ≠ 1 := by intro h; norm_num [h] at hs
  have hs0 : toHalf (q : ℂ) ≠ 0 := by intro h; norm_num [h] at hs
  let s : Hp := ⟨toHalf q, hs⟩
  have heuler : L (toHalf q) ≠ 0 := (he s).trans_ne (finiteHeckeL_ne_zero_of_one_lt_re χ s)
  have hf : halfFactor χ (toHalf q) ≠ 0 := by
    by_cases hc : χ = 1
    · simpa only [halfFactor, ite_eq_left hc] using div_ne_zero (sub_ne_zero.mpr hs1) hs0
    · simp [halfFactor, hc]
  have hn : (1:ℂ) - (q:ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h1.ne')
  rw [normalized, cleared_agrees τ hτ χ hχ L hL he (by linarith) (fun h ↦ hs1 h.2)]
  exact mul_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr ha.ne') (pow_ne_zero N (div_ne_zero hn (by norm_num))))
    (mul_ne_zero hf heuler)

/-- A bounded analytic input for a disk Poisson argument, for any normalized Hecke character
and any normal-form finite continuation agreeing with the actual absolutely convergent series. -/
theorem exists_normalized_input (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    ∃ (N : ℕ) (a : ℝ), 0 < N ∧ 0 < a ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → ‖normalized χ L a N z‖ ≤ 1) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 →
        AnalyticAt ℂ (normalized χ L a N) z ∧ analyticOrderAt (normalized χ L a N) z ≠ ⊤) ∧
      normalized χ L a N 0 ≠ 0 ∧
      (∀ z : ℂ, ‖z‖ = 1 → normalized χ L a N z = raw χ L a N z) ∧
      (∀ q : ℝ, 0 ≤ q → q < 1 → normalized χ L a N q ≠ 0) ∧
      (∀ᶠ q : ℝ in 𝓝[<] 1, normalized χ L a N q ≠ 0) ∧
      Tendsto (fun q : ℝ ↦ (1 - q)*|Real.log ‖normalized χ L a N q‖|) (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨N, K, hN, hK, hAK⟩ := cleared_polynomial_bound τ hτ χ hχ L hL he
  have ha : 0 < K⁻¹ := inv_pos.mpr (by linarith)
  refine ⟨N, K⁻¹, hN, ha, fun z hz ↦ normalized_bound hN hK hAK hz, fun z hz h1 ↦ ?_,
    normalized_zero_ne τ hτ χ hχ L hL he ha N,
    fun z hz ↦ normalized_boundary τ hτ χ hχ L hL he _ hN hz,
    fun _ h0 h1 ↦ radial_normalized_ne_zero_of_nonneg τ hτ χ hχ L hL he ha N h0 h1,
    radial_normalized τ hτ χ hχ L hL he ha N⟩
  exact ⟨normalized_analytic τ hτ χ hχ L hL he _ N hz h1,
    normalized_finite_order τ hτ χ hχ L hL he ha N hz h1⟩

/-- The canonical normal-form continuation supplies the input without a continuation hypothesis. -/
theorem canonical_normalized_input (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) :
    let L := (finiteHeckeL_exists_continuation χ).choose
    ∃ (N : ℕ) (a : ℝ), 0 < N ∧ 0 < a ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → ‖normalized χ L a N z‖ ≤ 1) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 →
        AnalyticAt ℂ (normalized χ L a N) z ∧ analyticOrderAt (normalized χ L a N) z ≠ ⊤) ∧
      normalized χ L a N 0 ≠ 0 ∧
      (∀ z : ℂ, ‖z‖ = 1 → normalized χ L a N z = raw χ L a N z) ∧
      (∀ q : ℝ, 0 ≤ q → q < 1 → normalized χ L a N q ≠ 0) ∧
      (∀ᶠ q : ℝ in 𝓝[<] 1, normalized χ L a N q ≠ 0) ∧
      Tendsto (fun q : ℝ ↦ (1 - q)*|Real.log ‖normalized χ L a N q‖|) (𝓝[<] 1) (𝓝 0) := by
  intro L
  obtain ⟨hL, he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  exact exists_normalized_input τ hτ χ hχ L hL he

end RiemannMasullo.HeckeDiskNormalization
