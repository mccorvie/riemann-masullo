module

import Mathlib.Analysis.Meromorphic.Divisor
public import RiemannMasullo.AppB_AnalyticNT.Sec2
import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics
import RiemannMasullo.ForMathlib.Analysis.Complex.RectangleIntegral
import RiemannMasullo.ForMathlib.Analysis.Meromorphic.PrincipalPart

/-!
# Slow growth near poles and the asymptotic residue theorem

Masullo, §B.3, pp. 604–606. The residue limit uses rectangles whose horizontal
edges lie at selected heights above and below the real axis.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Asymptotics BigOperators Topology

namespace RiemannMasullo

local notation "verticalPoint" =>
  (fun (σ y : ℝ) ↦ (σ : ℂ) + (y : ℂ) * Complex.I)
local notation "verticalTrace" =>
  (fun (f : ℂ → ℂ) (σ : ℝ) (y : ℝ) ↦ f (verticalPoint σ y))
local notation "openStrip" => (fun a b : ℝ ↦ Complex.re ⁻¹' Ioo a b)
local notation "atAbsInfty" => (comap abs atTop)
local notation "twoPiI" => (2 * (Real.pi : ℂ) * Complex.I)

-- TODO(paper-gap): (B.3.1.1) includes k = 0, forcing f to vanish along the
-- entire horizontal line at T 0 and hence to have zero meromorphic germ on the strip.
-- TODO(paper-gap): If both signs in (1)(a) range over all integer step indices,
-- the absolute heights are constant, contradicting (1)(b).

/-- Paper: Definition B.3.1.1, p. 604. A witness is a sequence of heights with
nondecreasing absolute heights on each tail, divergence in absolute value, and
polynomial upper and lower bounds. The function is holomorphic near every selected
line, is polynomially bounded in the nonzero index there, and has continuous,
polynomially bounded traces on two interior vertical lines.
Deviation: The index in (1)(a) counts steps outward on each tail. Part (1)(c)
includes the eventual polynomial lower bound used in Lemma B.3.1.2. The holomorphic
neighborhoods lie in the domain strip, and (B.3.1.1) applies only when `k ≠ 0`. -/
def WitnessesSlowGrowthNearPoles (f : ℂ → ℂ) (a b : ℝ) (T : ℤ → ℝ) : Prop :=
  a < b ∧ MeromorphicOn f (openStrip a b) ∧
    Monotone (fun k : ℕ ↦ |T (k : ℤ)|) ∧ Monotone (fun k : ℕ ↦ |T (-(k : ℤ))|) ∧
    Tendsto (fun k : ℤ ↦ |T k|) atAbsInfty atTop ∧
    (∃ α : ℝ, 0 < α ∧ T =O[atAbsInfty] (fun k : ℤ ↦ |(k : ℝ)| ^ α)) ∧
    (∃ c γ : ℝ, 0 < c ∧ 0 < γ ∧
      ∀ᶠ k : ℤ in atAbsInfty, c * |(k : ℝ)| ^ γ ≤ |T k|) ∧
    (∀ k : ℤ, ∃ δ > (0 : ℝ), DifferentiableOn ℂ f
      (openStrip a b ∩ Complex.im ⁻¹' Ioo (T k - δ) (T k + δ))) ∧
    (∃ β A : ℝ, 0 < β ∧ 0 < A ∧
      ∀ (k : ℤ), k ≠ 0 → ∀ σ ∈ Ioo a b,
        ‖f (verticalPoint σ (T k))‖ ≤ A * |(k : ℝ)| ^ β) ∧
    ∃ ε₁ ε₂ : ℝ, 0 < ε₁ ∧ ε₁ < ε₂ ∧ ε₂ < (b - a) / 2 ∧
      ∀ σ ∈ ({a + ε₁, b - ε₂} : Set ℝ),
        Continuous (verticalTrace f σ) ∧
          ∃ γ > (0 : ℝ), verticalTrace f σ =O[atAbsInfty] (fun y : ℝ ↦ |y| ^ γ)

/-- Paper: Definition B.3.1.1, p. 604. A function has slow growth near its poles
on the strip if there exists a sequence witnessing that condition.
Deviation: Uses the repaired witness condition above. -/
def HasSlowGrowthNearPoles (f : ℂ → ℂ) (a b : ℝ) : Prop :=
  ∃ T : ℤ → ℝ, WitnessesSlowGrowthNearPoles f a b T

/-- Paper: Definition B.3.1.1, p. 604. The integer heights witness slow growth
for the zero function on every nonempty strip.
Deviation: Sanity check for the witness predicate. -/
theorem witnessesSlowGrowthNearPoles_zero {a b : ℝ} (hab : a < b) :
    WitnessesSlowGrowthNearPoles (fun _ ↦ 0) a b (fun k : ℤ ↦ (k : ℝ)) := by
  refine ⟨hab, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ((analyticAt_const (v := (0 : ℂ)) (x := x)) :
      AnalyticAt ℂ (fun _ : ℂ ↦ (0 : ℂ)) x).meromorphicAt
  · intro m n hmn
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    simpa [abs_of_nonneg hm_nonneg, abs_of_nonneg hn_nonneg] using hmn'
  · intro m n hmn
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    simpa [abs_neg, abs_of_nonneg hm_nonneg, abs_of_nonneg hn_nonneg] using hmn'
  · have h₀ := (tendsto_intCast_atTop_atTop (R := ℝ)).comp
      (Filter.tendsto_comap (f := abs) (x := atTop))
    exact h₀.congr' (Filter.Eventually.of_forall (fun k => Int.cast_abs))
  · refine ⟨1, by norm_num, ?_⟩
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards with k
    simp [Real.norm_eq_abs]
  · refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    filter_upwards with k
    simp
  · intro k
    refine ⟨1, by norm_num, ?_⟩
    exact differentiableOn_const (c := (0 : ℂ))
  · refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro k hk σ hσ
    simp
  · refine ⟨(b - a) / 4, (b - a) / 3, ?_, ?_, ?_, ?_⟩
    · positivity
    · nlinarith
    · nlinarith
    · intro σ hσ
      refine ⟨continuous_const, 1, by norm_num, ?_⟩
      change (fun _ : ℝ ↦ (0 : ℂ)) =O[atAbsInfty] (fun y : ℝ ↦ |y| ^ 1)
      exact Asymptotics.isBigO_zero (fun y : ℝ ↦ |y| ^ 1) (comap abs atTop)

/-- Paper: Definition B.3.1.1, p. 604. The reciprocal function has slow growth on
the strip with real parts between −1 and 1, and has a simple pole at zero.
Deviation: Sanity check for the repaired definition, with heights `T k = k + 1/2`. -/
theorem hasSlowGrowthNearPoles_one_div :
    HasSlowGrowthNearPoles (fun z : ℂ ↦ 1 / z) (-1) 1 ∧
      meromorphicOrderAt (fun z : ℂ ↦ 1 / z) 0 = -1 := by
  have hOrder : meromorphicOrderAt (fun z : ℂ ↦ 1 / z) 0 = -1 := by
    have h : meromorphicOrderAt (fun z : ℂ ↦ (z - 0) ^ (-1 : ℤ)) 0 =
        ((-1 : ℤ) : WithTop ℤ) := meromorphicOrderAt_zpow_id_sub_const
    simpa only [sub_zero, zpow_neg_one, one_div, WithTop.LinearOrderedAddCommGroup.coe_neg,
      WithTop.coe_one] using h
  refine ⟨?_, hOrder⟩
  let T (k : ℤ) : ℝ := (k : ℝ) + 1 / 2
  have hHeight (k : ℤ) : (1 / 2 : ℝ) ≤ |T k| := by
    change (1 / 2 : ℝ) ≤ |(k : ℝ) + 1 / 2|
    rcases le_or_gt 0 k with hk | hk
    · have hk' : 0 ≤ (k : ℝ) := by exact_mod_cast hk
      linarith [le_abs_self ((k : ℝ) + 1 / 2)]
    · have hk' : (k : ℝ) ≤ -1 := Int.cast_le_neg_one_of_neg hk
      linarith [neg_le_abs ((k : ℝ) + 1 / 2)]
  have hIndex : Tendsto (fun k : ℤ ↦ |(k : ℝ)|) atAbsInfty atTop := by
    simpa only [Function.comp_def, Int.cast_abs] using
      (tendsto_intCast_atTop_atTop (R := ℝ)).comp
        (tendsto_comap : Tendsto (abs : ℤ → ℤ) atAbsInfty atTop)
  have hLower : ∀ᶠ k : ℤ in atAbsInfty, (1 / 2 : ℝ) * |(k : ℝ)| ≤ |T k| := by
    filter_upwards [hIndex.eventually_ge_atTop 1] with k hk
    have h := abs_sub_abs_le_abs_sub (k : ℝ) (-(1 / 2 : ℝ))
    rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), sub_neg_eq_add] at h
    change (1 / 2 : ℝ) * |(k : ℝ)| ≤ |(k : ℝ) + 1 / 2|
    linarith
  have hReciprocal (σ y : ℝ) {c : ℝ} (hc : 0 < c) (hy : c ≤ |y|) :
      ‖(1 : ℂ) / verticalPoint σ y‖ ≤ c⁻¹ := by
    have hNorm : |y| ≤ ‖verticalPoint σ y‖ := by
      simpa [Complex.add_im, Complex.mul_I_im] using
        Complex.abs_im_le_norm (verticalPoint σ y)
    rw [one_div, norm_inv]
    exact (inv_le_inv₀ (hc.trans_le (hy.trans hNorm)) hc).2 (hy.trans hNorm)
  refine ⟨T, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((Meromorphic.const (1 : ℂ)).div Meromorphic.id).meromorphicOn
  · intro m n hmn
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    simp only [T, Int.cast_natCast, abs_of_nonneg (by positivity : 0 ≤ (m : ℝ) + 1 / 2)]
    exact (add_le_add_left hmn' _).trans (le_abs_self _)
  · intro m n hmn
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    simp only [T, Int.cast_neg, Int.cast_natCast]
    apply abs_le'.2
    refine ⟨?_, ?_⟩
    · have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      have hn : (1 / 2 : ℝ) ≤ |-(n : ℝ) + 1 / 2| := by
        simpa only [T, Int.cast_neg, Int.cast_natCast] using hHeight (-(n : ℤ))
      exact (by linarith : -(m : ℝ) + 1 / 2 ≤ 1 / 2).trans hn
    · exact (by linarith : -(-(m : ℝ) + 1 / 2) ≤ -(-(n : ℝ) + 1 / 2)).trans (neg_le_abs _)
  · refine tendsto_atTop.2 fun r ↦ ?_
    filter_upwards [hIndex.eventually_ge_atTop (2 * r), hLower] with k hk hbound
    linarith
  · refine ⟨1, zero_lt_one, Asymptotics.isBigO_iff.2 ⟨2, ?_⟩⟩
    filter_upwards [hIndex.eventually_ge_atTop 1] with k hk
    simp only [T, Real.rpow_one, Real.norm_eq_abs, abs_abs]
    have h := abs_add_le (k : ℝ) (1 / 2)
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h
    linarith
  · exact ⟨1 / 2, 1, by norm_num, zero_lt_one, by simpa only [Real.rpow_one] using hLower⟩
  · intro k
    refine ⟨1 / 2, by norm_num, fun z hz ↦ ?_⟩
    have hz₀ : z ≠ 0 := by
      rintro rfl
      have him := hz.2
      change T k - 1 / 2 < (0 : ℂ).im ∧ (0 : ℂ).im < T k + 1 / 2 at him
      rw [Complex.zero_im] at him
      exact (not_lt_of_ge (hHeight k))
        (abs_lt.2 ⟨by linarith [him.2], by linarith [him.1]⟩)
    exact ((differentiableAt_const (1 : ℂ)).div differentiableAt_id hz₀).differentiableWithinAt
  · refine ⟨1, 2, zero_lt_one, by norm_num, ?_⟩
    intro k hk σ _
    have hk' : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    rw [Real.rpow_one]
    calc
      ‖(1 : ℂ) / verticalPoint σ (T k)‖ ≤ 2 := by
        simpa only [one_div, inv_inv] using hReciprocal σ (T k) (by norm_num) (hHeight k)
      _ ≤ 2 * |(k : ℝ)| := by linarith
  · refine ⟨1 / 4, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    intro σ hσ
    have hσ₀ : σ ≠ 0 := by
      simp only [mem_insert_iff, mem_singleton_iff] at hσ
      rcases hσ with rfl | rfl <;> norm_num
    refine ⟨?_, 1, zero_lt_one, Asymptotics.isBigO_iff.2 ⟨1, ?_⟩⟩
    · refine continuous_const.div
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)) fun y hz ↦ ?_
      apply hσ₀
      simpa [Complex.add_re, Complex.mul_I_re] using congrArg Complex.re hz
    · have hY : ∀ᶠ y : ℝ in atAbsInfty, 1 ≤ |y| :=
        tendsto_comap.eventually (eventually_ge_atTop 1)
      filter_upwards [hY] with y hy
      simp only [Real.rpow_one, Real.norm_eq_abs, abs_abs, one_mul]
      calc
        ‖(1 : ℂ) / verticalPoint σ y‖ ≤ 1 := by
          simpa only [inv_one] using hReciprocal σ y zero_lt_one hy
        _ ≤ |y| := hy

-- TODO(paper-gap): The proof of (B.3.1.2) needs a polynomial lower bound on
-- |T k|, whereas Definition B.3.1.1 gives an upper bound. The bounds at T k
-- also need not apply at -T k.

/-- Paper: Lemma B.3.1.2, p. 605. At the selected heights the horizontal absolute
integral exists for |k| ≥ 2 and tends to zero as |k| goes to infinity.
Deviation: The limit uses the repaired witness condition and is taken at `T k`
on both index tails. The two strip endpoints have zero measure. -/
theorem tendsto_horizontalIntegral_of_slowGrowthNearPoles
    {f Φ : ℂ → ℂ} {a b : ℝ} {T : ℤ → ℝ}
    (hT : WitnessesSlowGrowthNearPoles f a b T)
    (ε : ℝ) (hε : 0 < ε) (hΦ : UniformlySchwartzOnStrip Φ (a - ε) (b + ε)) :
    let F (k : ℤ) (σ : ℝ) := ‖Φ (verticalPoint σ (T k)) * f (verticalPoint σ (T k))‖
    (∀ k : ℤ, 2 ≤ |k| → IntervalIntegrable (F k) volume a b) ∧
      Tendsto (fun k : ℤ ↦ ∫ σ in a..b, F k σ) atAbsInfty (𝓝 0) := by
  intro F
  obtain ⟨hab, _, _, _, hHeight, _, ⟨c, γ, hc, hγ, hLower⟩, hDiff,
    ⟨β, A, _, hA, hGrowth⟩, _⟩ := hT
  obtain ⟨_, hΦDiff, hDecay⟩ := hΦ
  have hNonneg (k : ℤ) (σ : ℝ) : 0 ≤ F k σ := norm_nonneg _
  have hProduct (k : ℤ) (hk : k ≠ 0) (σ : ℝ) (hσ : σ ∈ Ioo a b) {D : ℝ}
      (hD : ‖Φ (verticalPoint σ (T k))‖ ≤ D) : F k σ ≤ D * (A * |(k : ℝ)| ^ β) := by
    change ‖Φ (verticalPoint σ (T k)) * f (verticalPoint σ (T k))‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul hD (hGrowth k hk σ hσ) (norm_nonneg _) ((norm_nonneg _).trans hD)
  have hInt (k : ℤ) (hk : k ≠ 0) : IntervalIntegrable (F k) volume a b := by
    have hPoint : Continuous (fun σ : ℝ ↦ verticalPoint σ (T k)) := by fun_prop
    have hΦCont : ContinuousOn (fun σ ↦ Φ (verticalPoint σ (T k))) (Icc a b) := by
      apply hΦDiff.continuousOn.comp hPoint.continuousOn
      intro σ hσ
      simpa using (show a - ε < σ ∧ σ < b + ε by
        exact ⟨by linarith [hσ.1], by linarith [hσ.2]⟩)
    obtain ⟨δ, hδ, hfDiff⟩ := hDiff k
    have hfCont : ContinuousOn (fun σ ↦ f (verticalPoint σ (T k))) (Ioo a b) := by
      apply hfDiff.continuousOn.comp hPoint.continuousOn
      intro σ hσ
      simpa using (show σ ∈ Ioo a b ∧ T k - δ < T k ∧ T k < T k + δ from
        ⟨hσ, by linarith, by linarith⟩)
    have hFCont : ContinuousOn (F k) (Ioo a b) :=
      ((hΦCont.mono Ioo_subset_Icc_self).mul hfCont).norm
    obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hΦCont.norm
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le, IntegrableOn,
      ← restrict_Ioo_eq_restrict_Ioc]
    have hConst : IntegrableOn (fun _ : ℝ ↦ M * (A * |(k : ℝ)| ^ β)) (Ioo a b) volume :=
      integrableOn_const measure_Ioo_lt_top.ne
    apply hConst.mono_nonneg (hFCont.aestronglyMeasurable measurableSet_Ioo)
      (Eventually.of_forall (hNonneg k))
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioo (a := a) (b := b))] with σ hσ
    exact hProduct k hk σ hσ (hM (mem_image_of_mem _ (Ioo_subset_Icc_self hσ)))
  refine ⟨fun k hk ↦ hInt k (abs_pos.mp (lt_of_lt_of_le (by norm_num) hk)), ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (β / γ))
  have hN₁ : 1 ≤ N := by
    exact_mod_cast ((le_max_left 1 (β / γ)).trans hN.le)
  have hExponent : β < γ * N := by
    rw [mul_comm]
    exact (div_lt_iff₀ hγ).mp ((le_max_right 1 (β / γ)).trans_lt hN)
  obtain ⟨C, hC, hBound⟩ := hDecay ε hε (by linarith) N hN₁
  have hAbs : Tendsto (fun k : ℤ ↦ |k|) atAbsInfty atTop := tendsto_comap
  have hAbsReal : Tendsto (fun k : ℤ ↦ |(k : ℝ)|) atAbsInfty atTop := by
    simpa only [Function.comp_def, Int.cast_abs] using
      (tendsto_intCast_atTop_atTop (R := ℝ)).comp hAbs
  let B (k : ℤ) := (C * A / c ^ N) * |(k : ℝ)| ^ (β - γ * N)
  have hLimit : Tendsto (fun k : ℤ ↦ (b - a) * B k) atAbsInfty (𝓝 0) := by
    have hPow := (tendsto_rpow_neg_atTop (sub_pos.mpr hExponent)).comp hAbsReal
    simpa only [Function.comp_def, B, neg_sub, mul_zero] using
      (hPow.const_mul (C * A / c ^ N)).const_mul (b - a)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hLimit
  · exact Eventually.of_forall fun k ↦ intervalIntegral.integral_nonneg_of_forall hab.le
      (hNonneg k)
  · have hDecayT : Tendsto T atAbsInfty (comap abs atTop) := tendsto_comap_iff.mpr hHeight
    filter_upwards [hAbs.eventually_gt_atTop 0, hLower, hDecayT.eventually hBound] with k hk hl hd
    have hk₀ := abs_pos.mp hk
    have hkPos : 0 < |(k : ℝ)| := by exact_mod_cast hk
    have hDenom : 0 < (c * |(k : ℝ)| ^ γ) ^ N := by positivity
    have hPowLe : (c * |(k : ℝ)| ^ γ) ^ N ≤ |T k| ^ N := by gcongr
    have hMajor : ∀ σ ∈ Ioo a b, F k σ ≤ B k := by
      intro σ hσ
      have hΦLe : ‖Φ (verticalPoint σ (T k))‖ ≤ C / |T k| ^ N := by
        apply hd σ
        simpa using Ioo_subset_Icc_self hσ
      calc
        F k σ ≤ (C / |T k| ^ N) * (A * |(k : ℝ)| ^ β) := hProduct k hk₀ σ hσ hΦLe
        _ ≤ (C / (c * |(k : ℝ)| ^ γ) ^ N) * (A * |(k : ℝ)| ^ β) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hC.le hDenom hPowLe) (by positivity)
        _ = B k := by
          dsimp only [B]
          rw [mul_pow, ← Real.rpow_mul_natCast (abs_nonneg _) γ N, Real.rpow_sub hkPos]
          ring
    calc
      (∫ σ in a..b, F k σ) ≤ ∫ _ in a..b, B k :=
        intervalIntegral.integral_mono_on_of_le_Ioo hab.le (hInt k hk₀) intervalIntegrable_const hMajor
      _ = (b - a) * B k := by rw [intervalIntegral.integral_const, smul_eq_mul]

-- TODO(paper-gap): Theorem B.3.2.1(1) uses rectangles defined for T > 0,
-- but the nonnegative-indexed witness heights need not be positive.
-- TODO(paper-gap): Theorem B.3.2.1(2) uses Φ(ρ) Res f at arbitrary poles,
-- whereas the contour integral gives Res (Φ * f).
-- TODO(paper-gap): Theorem B.3.2.1(2) uses arbitrary pole-free vertical sides,
-- but the growth condition supplies polynomial bounds only on two existentially chosen lines.
-- TODO(paper-gap): The horizontal terms in (B.3.2.4) have signs opposite to
-- the counterclockwise orientation in Figure 3.

/-- Paper: Theorem B.3.2.1(2), p. 606. The trace of the product is absolutely
integrable on an interior vertical line where the trace of `f` is continuous
and polynomially bounded.
Deviation: The trace assumptions are explicit for each line. -/
theorem verticalIntegrable_mul_of_polynomialGrowth {f Φ : ℂ → ℂ} {a b σ : ℝ}
    (hΦ : UniformlySchwartzOnStrip Φ a b) (hσ : σ ∈ Ioo a b)
    (hContinuous : Continuous (verticalTrace f σ))
    (hGrowth : ∃ γ > (0 : ℝ), verticalTrace f σ =O[atAbsInfty] (fun y : ℝ ↦ |y| ^ γ)) :
    Complex.VerticalIntegrable (fun z ↦ Φ z * f z) σ := by
  have hΦContinuous : Continuous (verticalTrace Φ σ) := by
    apply hΦ.2.1.continuousOn.comp_continuous
    · fun_prop
    · intro y
      simpa using hσ
  obtain ⟨γ, hγ, hGrowth⟩ := hGrowth
  obtain ⟨A, hA, hBound⟩ := Asymptotics.isBigO_iff'.mp hGrowth
  obtain ⟨N, hN⟩ := exists_nat_gt (γ + 2)
  have hN₁ : 1 ≤ N := by
    exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  let ε := min (σ - a) (b - σ) / 2
  have hε : 0 < ε := half_pos (lt_min (sub_pos.mpr hσ.1) (sub_pos.mpr hσ.2))
  have hleft : a + ε < σ := by dsimp [ε]; linarith [min_le_left (σ - a) (b - σ), hσ.1]
  have hright : σ < b - ε := by dsimp [ε]; linarith [min_le_right (σ - a) (b - σ), hσ.2]
  obtain ⟨C, hC, hDecay⟩ := hΦ.2.2 ε hε (hleft.trans hright) N hN₁
  unfold Complex.VerticalIntegrable
  apply (hΦContinuous.mul hContinuous).locallyIntegrable.integrable_of_isBigO_cocompact _
    (integrable_inv_one_add_sq.integrableAtFilter _)
  rw [cocompact_eq_atBot_atTop, ← comap_abs_atTop]
  apply Asymptotics.IsBigO.of_bound (2 * (C * A))
  have hLarge : ∀ᶠ y : ℝ in atAbsInfty, 1 ≤ |y| :=
    tendsto_comap.eventually (eventually_ge_atTop 1)
  filter_upwards [hBound, hDecay, hLarge] with y hy hΦy hy₁
  have hyPos : 0 < |y| := zero_lt_one.trans_le hy₁
  have hySq : 1 ≤ y ^ 2 := by
    rw [← sq_abs]
    exact one_le_pow₀ hy₁
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg y) _)] at hy
  calc
    ‖Φ (verticalPoint σ y) * f (verticalPoint σ y)‖
        ≤ (C / |y| ^ N) * (A * |y| ^ γ) := by
      rw [norm_mul]
      exact mul_le_mul (hΦy σ ⟨hleft.le, hright.le⟩) hy (norm_nonneg _) (by positivity)
    _ = (C * A) * |y| ^ (γ - (N : ℝ)) := by
      rw [Real.rpow_sub hyPos, Real.rpow_natCast]
      ring
    _ ≤ (C * A) * |y| ^ (-2 : ℝ) := by
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hy₁ (by linarith))
        (by positivity)
    _ ≤ 2 * (C * A) * ‖(1 + y ^ 2)⁻¹‖ := by
      rw [Real.rpow_neg (abs_nonneg y), Real.rpow_two, sq_abs,
        Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv, ← div_eq_mul_inv]
      apply (div_le_div_iff₀ (by linarith) (by positivity)).mpr
      nlinarith [mul_nonneg (mul_nonneg hC.le hA.le) (sub_nonneg.mpr hySq)]

/-- Paper: Theorem B.3.2.1, p. 606. For a meromorphic germ, the residue is the
normalized counterclockwise circle integral in the limit of small positive radii.
Deviation: Makes the residue operation in the paper explicit. -/
def complexResidue (f : ℂ → ℂ) (ρ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun r ↦ circleIntegral f ρ r / twoPiI)

/-- Paper: Theorem B.3.2.1, p. 606. Dividing a function holomorphic near `ρ` by
`z - ρ` gives residue equal to the numerator at `ρ`.
Deviation: Sanity check for the residue normalization at a simple pole. -/
theorem complexResidue_div_sub {g : ℂ → ℂ} {ρ : ℂ} (hg : AnalyticAt ℂ g ρ) :
    complexResidue (fun z ↦ g z / (z - ρ)) ρ = g ρ := by
  obtain ⟨R, hR, hgR⟩ := hg.exists_ball_analyticOnNhd
  refine (tendsto_const_nhds.congr' ?_).limUnder_eq
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  have hsub : Metric.closedBall ρ r ⊆ Metric.ball ρ R := Metric.closedBall_subset_ball hr.2
  have hint : circleIntegral (fun z ↦ g z / (z - ρ)) ρ r = twoPiI * g ρ := by
    have h := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      (f := g) Set.countable_empty (Metric.mem_ball_self hr.1)
      (fun z hz ↦ (hgR z (hsub hz)).continuousAt.continuousWithinAt)
      (fun z hz ↦ (hgR z (hsub (Metric.ball_subset_closedBall hz.1))).differentiableAt)
    simpa [div_eq_inv_mul] using h
  rw [hint, mul_div_cancel_left₀]
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

set_option quotPrecheck false in
local notation "rectanglePoles" =>
  (fun (f : ℂ → ℂ) (σ₁ σ₂ t₁ t₂ : ℝ) ↦
    {ρ : ℂ | ρ.re ∈ Ioo σ₁ σ₂ ∧ ρ.im ∈ Ioo t₁ t₂ ∧ meromorphicOrderAt f ρ < 0})

/-- Paper: Theorem B.3.2.1(1), p. 606. An open rectangle whose vertical sides
are interior to the strip contains only finitely many poles.
Deviation: Makes the finiteness implicit in the rectangle sum explicit. -/
theorem finite_rectanglePoles {f : ℂ → ℂ} {a b σ₁ σ₂ t₁ t₂ : ℝ}
    (hf : MeromorphicOn f (openStrip a b)) (hσ₁ : a < σ₁) (hσ₂ : σ₂ < b) :
    (rectanglePoles f σ₁ σ₂ t₁ t₂).Finite := by
  let K := (Icc σ₁ σ₂) ×ℂ (Icc t₁ t₂)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hmer : MeromorphicOn f K := fun z hz ↦ hf z ⟨hσ₁.trans_le hz.1.1, hz.1.2.trans_lt hσ₂⟩
  apply ((MeromorphicOn.divisor f K).finiteSupport hK).subset
  intro z hz
  have hzK : z ∈ K := ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.1.le, hz.2.1.2.le⟩⟩
  change (MeromorphicOn.divisor f K z) ≠ 0
  rw [MeromorphicOn.divisor_apply hmer hzK, Ne, WithTop.untop₀_eq_zero]
  exact not_or.mpr ⟨ne_of_lt hz.2.2, ne_top_of_lt (hz.2.2.trans_le le_top)⟩

local notation "polarPart" =>
  (fun (ρ : ℂ) (n : ℕ) (c : ℕ → ℂ) (z : ℂ) ↦
    ∑ k ∈ Finset.range n, c k * (z - ρ) ^ (-(k : ℤ) - 1))

/-- The term of a polar expansion with exponent `-1` determines its circle
residue. The expression also gives zero for the empty expansion. -/
private theorem complexResidue_eq_polar_coefficient {g H : ℂ → ℂ} {ρ : ℂ} {n : ℕ}
    {c : ℕ → ℂ} (hH : AnalyticAt ℂ H ρ)
    (he : g =ᶠ[𝓝[≠] ρ] (fun z ↦ H z + polarPart ρ n c z)) :
    complexResidue g ρ = ∑ k ∈ Finset.range n, (if k = 0 then c k else 0) := by
  obtain ⟨δ, hδ, hEq⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp he
  obtain ⟨R, hR, hA⟩ := hH.exists_ball_analyticOnNhd
  refine (tendsto_const_nhds.congr' ?_).limUnder_eq
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ hR)] with r hr
  have hrδ := hr.2.trans_le (min_le_left δ R)
  have hrR := hr.2.trans_le (min_le_right δ R)
  have hsne (z : ℂ) (hz : z ∈ Metric.sphere ρ r) : z ≠ ρ := by
    rintro rfl
    exact hr.1.ne (by simpa using hz)
  have hC : ∀ k ∈ Finset.range n,
      ContinuousOn (fun z : ℂ ↦ c k * (z - ρ) ^ (-(k : ℤ) - 1)) (Metric.sphere ρ r) := by
    intro k _
    exact continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).zpow₀ _
      fun z hz ↦ Or.inl (sub_ne_zero.mpr (hsne z hz)))
  have hCi : ∀ k ∈ Finset.range n,
      CircleIntegrable (fun z : ℂ ↦ c k * (z - ρ) ^ (-(k : ℤ) - 1)) ρ r :=
    fun k hk ↦ (hC k hk).circleIntegrable hr.1.le
  have hAi := hA.mono (Metric.closedBall_subset_ball hrR)
  have hA0 : circleIntegral H ρ r = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.1.le countable_empty
      hAi.continuousOn (fun z hz ↦ (hAi z (Metric.ball_subset_closedBall hz.1)).differentiableAt)
  have hCircle : circleIntegral g ρ r =
      twoPiI * ∑ k ∈ Finset.range n, (if k = 0 then c k else 0) := by
    calc
      circleIntegral g ρ r = circleIntegral (fun z ↦ H z + polarPart ρ n c z) ρ r :=
        circleIntegral.integral_congr hr.1.le fun z hz ↦
          hEq ⟨Metric.mem_ball.mpr ((Metric.mem_sphere.mp hz).trans_lt hrδ),
            mem_compl_singleton_iff.mpr (hsne z hz)⟩
      _ = circleIntegral H ρ r + circleIntegral (polarPart ρ n c) ρ r := by
        apply circleIntegral.integral_add
        · exact (hAi.continuousOn.mono Metric.sphere_subset_closedBall).circleIntegrable hr.1.le
        · exact (continuousOn_finsetSum _ hC).circleIntegrable hr.1.le
      _ = twoPiI * ∑ k ∈ Finset.range n, (if k = 0 then c k else 0) := by
        rw [hA0, zero_add, circleIntegral.integral_fun_sum hCi, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [circleIntegral.integral_const_mul]
        by_cases hk : k = 0
        · subst k
          simp only [Nat.cast_zero, neg_zero, zero_sub, zpow_neg_one, ite_true]
          rw [circleIntegral.integral_sub_center_inv ρ hr.1.ne', mul_comm]
        · rw [circleIntegral.integral_sub_zpow_of_ne (by omega), ite_eq_right hk, mul_zero, mul_zero]
  rw [hCircle, mul_div_cancel_left₀]
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- In a rectangle enclosing the center of a polar expansion, the boundary
integral is `2πi` times its coefficient of exponent `-1`. -/
private theorem rectangleIntegral_polarPart {z w ρ : ℂ} {n : ℕ} {c : ℕ → ℂ}
    (hρ : ρ ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) :
    rectangleIntegral (polarPart ρ n c) z w =
      twoPiI * ∑ k ∈ Finset.range n, (if k = 0 then c k else 0) := by
  rw [rectangleIntegral_finsetSum (hρ.1.1.trans hρ.1.2).le (hρ.2.1.trans hρ.2.2).le,
    Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [rectangleIntegral_const_mul]
    by_cases hk : k = 0
    · subst k
      simp only [Nat.cast_zero, neg_zero, zero_sub, zpow_neg_one, ite_true]
      rw [rectangleIntegral_sub_inv hρ, mul_comm]
    · rw [rectangleIntegral_sub_zpow_of_ne hρ (by omega), ite_eq_right hk, mul_zero, mul_zero]
  · intro k _
    exact continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).zpow₀ _
      fun z hz ↦ Or.inl (sub_ne_zero.mpr (ne_of_mem_of_not_mem hρ hz.2 |>.symm)))

/-- Paper: Equation (B.3.2.3), p. 606. The counterclockwise boundary integral
of a meromorphic function on a closed rectangle is `2πi` times the sum of the
residues at its poles.
Deviation: The finite index set may also contain regular interior points,
whose residues vanish. -/
theorem rectangleIntegral_eq_sum_complexResidue {g : ℂ → ℂ} {σ₁ σ₂ t₁ t₂ : ℝ}
    (hσ : σ₁ < σ₂) (ht : t₁ < t₂) (S : Finset ℂ)
    (hg : MeromorphicOn g (Icc σ₁ σ₂ ×ℂ Icc t₁ t₂))
    (hInside : ∀ ρ ∈ S, ρ ∈ Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂)
    (hOutside : ∀ ρ ∈ Icc σ₁ σ₂ ×ℂ Icc t₁ t₂, ρ ∉ S → 0 ≤ meromorphicOrderAt g ρ) :
    (∫ x in σ₁..σ₂, g (verticalPoint x t₁)) -
      (∫ x in σ₁..σ₂, g (verticalPoint x t₂)) +
      Complex.I * (∫ y in t₁..t₂, g (verticalPoint σ₂ y)) -
      Complex.I * (∫ y in t₁..t₂, g (verticalPoint σ₁ y)) =
      twoPiI * ∑ ρ ∈ S, complexResidue g ρ := by
  classical
  let z : ℂ := ⟨σ₁, t₁⟩
  let w : ℂ := ⟨σ₂, t₂⟩
  let K := Icc σ₁ σ₂ ×ℂ Icc t₁ t₂
  let U := Ioo σ₁ σ₂ ×ℂ Ioo t₁ t₂
  have hUK : U ⊆ K := fun _ h ↦ ⟨Ioo_subset_Icc_self h.1, Ioo_subset_Icc_self h.2⟩
  choose! n H c hH he using fun ρ (hρ : ρ ∈ S) ↦
    MeromorphicAt.exists_polar_expansion (hg ρ (hUK (hInside ρ hρ)))
  let P (ρ : ℂ) := polarPart ρ (n ρ) (c ρ)
  let Q (x : ℂ) := ∑ ρ ∈ S, P ρ x
  let D (x : ℂ) := g x - Q x
  let A := toMeromorphicNFOn D K
  have hPan : ∀ ρ x : ℂ, x ≠ ρ → AnalyticAt ℂ (P ρ) x := by
    intro ρ x hx
    exact (Finset.range _).analyticAt_fun_sum fun k _ ↦ analyticAt_const.mul
      (((analyticAt_id.sub analyticAt_const).zpow (sub_ne_zero.mpr hx)))
  have hQmero : MeromorphicOn Q K := by
    apply MeromorphicOn.fun_sum
    intro ρ _
    apply MeromorphicOn.fun_sum
    intro k _ x _
    exact (MeromorphicAt.const (c ρ k) x).mul
      (((analyticAt_id.sub (analyticAt_const (v := ρ))).meromorphicAt).fun_zpow _)
  have hDmero : MeromorphicOn D K := hg.fun_sub hQmero
  -- Subtracting all principal parts makes every point of the rectangle removable.
  have hDorder (x : ℂ) (hx : x ∈ K) : 0 ≤ meromorphicOrderAt D x := by
    apply (hDmero x hx).meromorphicOrderAt_nonneg_iff.mpr
    by_cases hxS : x ∈ S
    · let Q' (y : ℂ) := ∑ ρ ∈ S.erase x, P ρ y
      have hQ' : AnalyticAt ℂ Q' x := (S.erase x).analyticAt_fun_sum fun ρ hρ ↦
        hPan ρ x (Finset.mem_erase.mp hρ).1.symm
      refine ⟨fun y ↦ H x y - Q' y, (hH x hxS).sub hQ', ?_⟩
      filter_upwards [he x hxS] with y hy
      have hsplit : P x y + Q' y = Q y := Finset.add_sum_erase S (fun ρ ↦ P ρ y) hxS
      change g y - Q y = H x y - Q' y
      rw [← hsplit, hy]
      change H x y + P x y - (P x y + Q' y) = _
      abel
    · have hQan : AnalyticAt ℂ Q x := S.analyticAt_fun_sum fun ρ hρ ↦
        hPan ρ x (fun h ↦ hxS (h.symm ▸ hρ))
      obtain ⟨B, hB, hEq⟩ := ((hg x hx).meromorphicOrderAt_nonneg_iff).mp (hOutside x hx hxS)
      refine ⟨fun y ↦ B y - Q y, hB.sub hQan, ?_⟩
      filter_upwards [hEq] with y hy
      simp only [D, hy]
  have hAan : AnalyticOnNhd ℂ A K := by
    intro x hx
    exact (((hDmero x hx).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt).mp
      (hDorder x hx)).congr (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hDmero hx).symm
  have hA0 : rectangleIntegral A z w = 0 := by
    rw [rectangleIntegral_eq]
    have hc : DifferentiableOn ℂ A (uIcc z.re w.re ×ℂ uIcc z.im w.im) := by
      simpa only [z, w, uIcc_of_le hσ.le, uIcc_of_le ht.le] using hAan.differentiableOn
    exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn A z w hc
  have hPbd : ∀ ρ ∈ S, ContinuousOn (P ρ) (K \ U) := fun ρ hρ x hx ↦
    (hPan ρ x (ne_of_mem_of_not_mem (hInside ρ hρ) hx.2).symm).continuousAt.continuousWithinAt
  -- The boundary integrals ignore the finite set where normalization can change a value.
  let E := K \ {x | AnalyticAt ℂ g x}
  have hE : E.Countable :=
    ((isCompact_Icc.reProdIm isCompact_Icc).finite_sdiff_of_mem_codiscreteWithin
      hg.analyticAt_mem_codiscreteWithin).countable
  have hAE : EqOn g (fun x ↦ A x + Q x) ((K \ U) \ E) := by
    intro x hx
    have hxG : AnalyticAt ℂ g x := by
      by_contra hn
      exact hx.2 ⟨hx.1.1, hn⟩
    have hxQ : AnalyticAt ℂ Q x := S.analyticAt_fun_sum fun ρ hρ ↦
      hPan ρ x (ne_of_mem_of_not_mem (hInside ρ hρ) hx.1.2).symm
    have hxD : AnalyticAt ℂ D x := hxG.fun_sub hxQ
    have hDA : A x = D x := by
      change toMeromorphicNFOn D K x = D x
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hDmero hx.1.1,
        toMeromorphicNFAt_eq_self.mpr hxD.meromorphicNFAt]
    change g x = A x + Q x
    rw [hDA]
    exact (sub_add_cancel (g x) (Q x)).symm
  rw [← show rectangleIntegral g z w = _ from rectangleIntegral_eq g z w]
  rw [rectangleIntegral_congr_off_countable (z := z) (w := w) hσ.le ht.le hE hAE,
    rectangleIntegral_add hσ.le ht.le (hAan.continuousOn.mono sdiff_subset)
      (continuousOn_finsetSum S hPbd),
    hA0, zero_add, rectangleIntegral_finsetSum hσ.le ht.le hPbd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [rectangleIntegral_polarPart (hInside ρ hρ),
    complexResidue_eq_polar_coefficient (hH ρ hρ) (he ρ hρ)]

section AsymptoticResidue

variable {f Φ : ℂ → ℂ} {a b a' b' σ₁ σ₂ : ℝ} {T : ℤ → ℝ}
  (hT : WitnessesSlowGrowthNearPoles f a b T)
  (ha : a' < a) (hb : b < b') (hΦ : UniformlySchwartzOnStrip Φ a' b')
  (hσ₁ : a < σ₁) (hσ : σ₁ < σ₂) (hσ₂ : σ₂ < b)
  (hSides : ∀ σ ∈ ({σ₁, σ₂} : Set ℝ), Continuous (verticalTrace f σ) ∧
    ∃ γ > (0 : ℝ), verticalTrace f σ =O[atAbsInfty] (fun y : ℝ ↦ |y| ^ γ))
  (hHeights : ∀ k : ℕ, 0 < k → T (-(k : ℤ)) < 0 ∧ 0 < T (k : ℤ))

include ha hb hΦ hσ hSides hHeights

/-- Paper: Theorem B.3.2.1(1)–(2), p. 606. The finite sums of the residues of
`Φ * f` at poles of `f` converge to the upward integral on the right minus
the upward integral on the left, divided by `2πi`.
Deviation: The vertical sides have continuous, polynomially bounded traces.
The lower and upper edges use the selected heights `T (-k)` and `T k`, assumed
to have opposite signs for positive `k`. The residue is that of the product. -/
theorem tendsto_rectangleResidueSum :
    Tendsto
      (fun k : ℕ ↦
        ∑ ρ ∈ (finite_rectanglePoles (t₁ := T (-(k : ℤ))) (t₂ := T (k : ℤ))
          hT.2.1 hσ₁ hσ₂).toFinset, complexResidue (fun z ↦ Φ z * f z) ρ)
      atTop
      (𝓝 ((verticalLineIntegral (fun z ↦ Φ z * f z) σ₂ -
        verticalLineIntegral (fun z ↦ Φ z * f z) σ₁) / twoPiI)) := by
  let g (z : ℂ) := Φ z * f z
  let lower (k : ℕ) := T (-(k : ℤ))
  let upper (k : ℕ) := T (k : ℤ)
  let horizontal (j : ℤ) := ∫ x in σ₁..σ₂, g (verticalPoint x (T j))
  let vertical (σ : ℝ) (k : ℕ) :=
    Complex.I * (∫ y in lower k..upper k, g (verticalPoint σ y))
  have hk : ∀ᶠ k : ℕ in atTop, 0 < k := eventually_gt_atTop 0
  have hIndex : Tendsto (fun k : ℕ ↦ (k : ℤ)) atTop atAbsInfty := by
    apply tendsto_comap_iff.mpr
    simpa [Function.comp_def, abs_of_nonneg (Int.natCast_nonneg _)] using
      (tendsto_natCast_atTop_atTop (R := ℤ))
  have hNegIndex : Tendsto (fun k : ℕ ↦ -(k : ℤ)) atTop atAbsInfty := by
    apply tendsto_comap_iff.mpr
    simpa only [Function.comp_def, abs_neg] using (tendsto_comap_iff.mp hIndex)
  have hUpper : Tendsto upper atTop atTop :=
    (hT.2.2.2.2.1.comp hIndex).congr' (hk.mono fun k hk ↦
      abs_of_pos (hHeights k hk).2)
  have hLower : Tendsto lower atTop atBot :=
    (tendsto_neg_atTop_atBot.comp (hT.2.2.2.2.1.comp hNegIndex)).congr'
      (hk.mono fun k hk ↦ neg_eq_iff_eq_neg.mpr (abs_of_neg (hHeights k hk).1))
  have hVertical (σ : ℝ) (hσab : σ ∈ Ioo a b) (hσside : σ ∈ ({σ₁, σ₂} : Set ℝ)) :
      Tendsto (vertical σ) atTop (𝓝 (verticalLineIntegral g σ)) := by
    obtain ⟨hcont, hgrowth⟩ := hSides σ hσside
    have hi : Complex.VerticalIntegrable g σ :=
      verticalIntegrable_mul_of_polynomialGrowth hΦ
        ⟨ha.trans hσab.1, hσab.2.trans hb⟩ hcont hgrowth
    exact (intervalIntegral_tendsto_integral hi hLower hUpper).const_mul Complex.I
  have hHorizontal : Tendsto horizontal atAbsInfty (𝓝 0) := by
    let ε := min (a - a') (b' - b) / 2
    have hε : 0 < ε := half_pos (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb))
    have hLeft : a' < a - ε := by dsimp [ε]; linarith [min_le_left (a - a') (b' - b)]
    have hRight : b + ε < b' := by dsimp [ε]; linarith [min_le_right (a - a') (b' - b)]
    have hΦsmall : UniformlySchwartzOnStrip Φ (a - ε) (b + ε) := by
      refine ⟨by linarith [hT.1], hΦ.2.1.mono ?_, ?_⟩
      · exact preimage_mono (Ioo_subset_Ioo hLeft.le hRight.le)
      · intro δ hδ hδ' N hN
        obtain ⟨C, hC, hbound⟩ := hΦ.2.2 δ hδ
          (by linarith : a' + δ < b' - δ) N hN
        exact ⟨C, hC, hbound.mono fun y hy x hx ↦
          hy x ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩
    obtain ⟨hIntegrable, hLimit⟩ :=
      tendsto_horizontalIntegral_of_slowGrowthNearPoles hT ε hε hΦsmall
    apply squeeze_zero_norm' _ hLimit
    have hLarge : ∀ᶠ j : ℤ in atAbsInfty, 2 ≤ |j| :=
      tendsto_comap.eventually (eventually_ge_atTop 2)
    filter_upwards [hLarge] with j hj
    exact (intervalIntegral.norm_integral_le_integral_norm hσ.le).trans
      (intervalIntegral.integral_mono_interval hσ₁.le hσ.le hσ₂.le
        (Eventually.of_forall (fun _ ↦ norm_nonneg _)) (hIntegrable j hj))
  have hVerticalOrder (σ y : ℝ) (hcont : Continuous (verticalTrace f σ)) :
      0 ≤ meromorphicOrderAt f (verticalPoint σ y) := by
    by_contra! hpole
    have hline : Tendsto (verticalPoint σ) (𝓝[≠] y) (𝓝[≠] verticalPoint σ y) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(show Continuous (verticalPoint σ) by fun_prop).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin (s := {y}ᶜ)] with v hv
      exact fun heq ↦ hv (by simpa using congrArg Complex.im heq)
    have hPoleLimit := (tendsto_cobounded_of_meromorphicOrderAt_neg hpole).comp hline
    exact not_tendsto_atTop_of_tendsto_nhds (hcont.continuousAt.continuousWithinAt.tendsto.norm)
      (tendsto_norm_atTop_iff_cobounded.mpr hPoleLimit)
  have hIdentity : ∀ᶠ k : ℕ in atTop,
      (horizontal (-(k : ℤ)) - horizontal (k : ℤ) + vertical σ₂ k - vertical σ₁ k) /
          twoPiI =
        ∑ ρ ∈ (finite_rectanglePoles (t₁ := lower k) (t₂ := upper k)
          hT.2.1 hσ₁ hσ₂).toFinset, complexResidue g ρ := by
    filter_upwards [hk] with k hpos
    let hFinite := finite_rectanglePoles (t₁ := lower k) (t₂ := upper k) hT.2.1 hσ₁ hσ₂
    let S := hFinite.toFinset
    have hgΦ (z : ℂ) (hz : z.re ∈ Icc σ₁ σ₂) : AnalyticAt ℂ Φ z :=
      hΦ.2.1.analyticAt ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds
        ⟨ha.trans (hσ₁.trans_le hz.1), (hz.2.trans_lt hσ₂).trans hb⟩)
    have hf (z : ℂ) (hz : z.re ∈ Icc σ₁ σ₂) : MeromorphicAt f z :=
      hT.2.1 z ⟨hσ₁.trans_le hz.1, hz.2.trans_lt hσ₂⟩
    have hHorizontalOrder (j : ℤ) (z : ℂ) (hz : z.re ∈ Icc σ₁ σ₂) (hy : z.im = T j) :
        0 ≤ meromorphicOrderAt f z := by
      obtain ⟨δ, hδ, hd⟩ := hT.2.2.2.2.2.2.2.1 j
      apply AnalyticAt.meromorphicOrderAt_nonneg
      apply hd.analyticAt
      apply ((isOpen_Ioo.preimage Complex.continuous_re).inter
        (isOpen_Ioo.preimage Complex.continuous_im)).mem_nhds
      exact ⟨⟨hσ₁.trans_le hz.1, hz.2.trans_lt hσ₂⟩, by
        change T j - δ < z.im ∧ z.im < T j + δ
        rw [hy]
        exact ⟨sub_lt_self _ hδ, lt_add_of_pos_right _ hδ⟩⟩
    have ht : lower k < upper k := (hHeights k hpos).1.trans (hHeights k hpos).2
    have hrect := rectangleIntegral_eq_sum_complexResidue (g := g) hσ ht S
      (fun z hz ↦ (hgΦ z hz.1).meromorphicAt.mul (hf z hz.1))
      (fun ρ hρ ↦ ⟨(hFinite.mem_toFinset.mp hρ).1, (hFinite.mem_toFinset.mp hρ).2.1⟩) ?_
    · have htwoPiI : twoPiI ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
      change _ / twoPiI = ∑ ρ ∈ S, complexResidue g ρ
      exact (div_eq_iff htwoPiI).mpr (by simpa only [mul_comm _ twoPiI] using hrect)
    · intro z hz hzS
      rw [show meromorphicOrderAt g z = meromorphicOrderAt Φ z + meromorphicOrderAt f z
        from meromorphicOrderAt_mul (hgΦ z hz.1).meromorphicAt (hf z hz.1)]
      apply add_nonneg (hgΦ z hz.1).meromorphicOrderAt_nonneg
      rcases hz with ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
      rcases h₁.eq_or_lt with h₁ | h₁
      · have hz' : z = verticalPoint σ₁ z.im := by rw [h₁]; exact (Complex.re_add_im z).symm
        rw [hz']
        exact hVerticalOrder σ₁ z.im (hSides σ₁ (by simp)).1
      rcases h₂.eq_or_lt with h₂ | h₂
      · have hz' : z = verticalPoint σ₂ z.im := by rw [← h₂]; exact (Complex.re_add_im z).symm
        rw [hz']
        exact hVerticalOrder σ₂ z.im (hSides σ₂ (by simp)).1
      rcases h₃.eq_or_lt with h₃ | h₃
      · exact hHorizontalOrder (-(k : ℤ)) z ⟨h₁.le, h₂.le⟩ h₃.symm
      rcases h₄.eq_or_lt with h₄ | h₄
      · exact hHorizontalOrder (k : ℤ) z ⟨h₁.le, h₂.le⟩ h₄
      exact le_of_not_gt fun hzOrder ↦ hzS (hFinite.mem_toFinset.mpr
        ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩, hzOrder⟩)
  have hLim := (((hHorizontal.comp hNegIndex).sub (hHorizontal.comp hIndex)).add
    (hVertical σ₂ ⟨hσ₁.trans hσ, hσ₂⟩ (by simp))).sub
    (hVertical σ₁ ⟨hσ₁, hσ.trans hσ₂⟩ (by simp))
  simpa only [zero_sub, neg_zero, zero_add] using (hLim.div_const twoPiI).congr' hIdentity

omit ha hb hΦ hσ hSides hHeights in
/-- The circle residue depends only on the germ on a punctured neighborhood. -/
private theorem complexResidue_congr {f g : ℂ → ℂ} {ρ : ℂ}
    (h : f =ᶠ[𝓝[≠] ρ] g) : complexResidue f ρ = complexResidue g ρ := by
  obtain ⟨R, hR, hEq⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp h
  unfold complexResidue Filter.limUnder
  apply congrArg Filter.lim
  apply Filter.map_congr
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  congr 1
  apply circleIntegral.integral_congr hr.1.le
  intro z hz
  have hdist := Metric.mem_sphere.mp hz
  refine hEq ⟨Metric.mem_ball.mpr (hdist.trans_lt hr.2), mem_compl_singleton_iff.mpr ?_⟩
  rintro rfl
  exact hr.1.ne (by simpa using hdist)

/-- Paper: Theorem B.3.2.1(1)–(2), p. 606. If the poles between the chosen
lines are simple, the finite sums with weights `Φ ρ * complexResidue f ρ`
converge to the normalized difference of vertical integrals.
Deviation: Uses the same trace and signed height hypotheses as the residue
theorem. The simple-pole assumption justifies the printed weight. -/
theorem tendsto_rectangleResidueSum_of_simplePoles
    (hSimple : ∀ ρ : ℂ, ρ.re ∈ Ioo σ₁ σ₂ →
      meromorphicOrderAt f ρ < 0 → meromorphicOrderAt f ρ = -1) :
    Tendsto
      (fun k : ℕ ↦
        ∑ ρ ∈ (finite_rectanglePoles (t₁ := T (-(k : ℤ))) (t₂ := T (k : ℤ))
          hT.2.1 hσ₁ hσ₂).toFinset, Φ ρ * complexResidue f ρ)
      atTop
      (𝓝 ((verticalLineIntegral (fun z ↦ Φ z * f z) σ₂ -
        verticalLineIntegral (fun z ↦ Φ z * f z) σ₁) / twoPiI)) := by
  refine (tendsto_rectangleResidueSum hT ha hb hΦ hσ₁ hσ hσ₂ hSides hHeights).congr ?_
  intro k
  apply Finset.sum_congr rfl
  intro ρ hρ
  let hFinite := finite_rectanglePoles (t₁ := T (-(k : ℤ))) (t₂ := T (k : ℤ))
    hT.2.1 hσ₁ hσ₂
  have hPole := hFinite.mem_toFinset.mp hρ
  have hLeft := hσ₁.trans hPole.1.1
  have hRight := hPole.1.2.trans hσ₂
  have hf : MeromorphicAt f ρ := hT.2.1 ρ ⟨hLeft, hRight⟩
  have hΦρ : AnalyticAt ℂ Φ ρ :=
    hΦ.2.1.analyticAt ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds
      ⟨ha.trans hLeft, hRight.trans hb⟩)
  obtain ⟨g, hg, -, he⟩ := (meromorphicOrderAt_eq_int_iff (n := -1) hf).mp
    (hSimple ρ hPole.1 hPole.2.2)
  have hDiv : f =ᶠ[𝓝[≠] ρ] (fun z ↦ g z / (z - ρ)) := by
    filter_upwards [he] with z hz
    simpa only [zpow_neg_one, smul_eq_mul, div_eq_inv_mul] using hz
  have hMul : (fun z ↦ Φ z * f z) =ᶠ[𝓝[≠] ρ] (fun z ↦ (Φ z * g z) / (z - ρ)) := by
    filter_upwards [hDiv] with z hz
    rw [hz, mul_div_assoc]
  rw [complexResidue_congr hMul,
    complexResidue_div_sub (g := fun z ↦ Φ z * g z) (hΦρ.mul hg),
    complexResidue_congr hDiv, complexResidue_div_sub hg]

end AsymptoticResidue

end RiemannMasullo
