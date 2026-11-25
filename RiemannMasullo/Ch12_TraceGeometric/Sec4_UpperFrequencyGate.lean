module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.PositiveLocalPolar
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-! # Rational upper frequency gates in the log-norm coordinate

Mrshu's rational local comparison for (12.4.1.8) on pp. 516–517 gives a rank-one
defect and a logarithmic shift for a normalized upper frequency gate (#7354,
comment 7152334021). We work directly with those two real integrals. The spatial
scale is fixed in the lower bound and is chosen reciprocally for the sharp step
gates. Mlyle's strip-positive polar-free construction (#7524) underlies the centered
radial profile specialized in §12.5.
-/

open Function MeasureTheory Set Complex
open scoped ContDiff FourierTransform SchwartzMap ComplexConjugate

@[expose] public noncomputable section

namespace RiemannMasullo.RationalUpperGate

/-- Rank-one defect with the normalized upper frequency gate `Q`. -/
def rankOneDefect (H Q : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, H x * Real.exp (-x / 2) * ∫ u in Ioc 0 (min (Real.exp x) 1), Q u

/-- Logarithmic mass lost by the normalized upper frequency gate. -/
def logLoss (Q : ℝ → ℝ) : ℝ := ∫ u in Ioc (0 : ℝ) 1, (1 - Q u) / u

private theorem gateFubini (f q : ℝ → ℝ) (hf : Integrable f)
    (hq : IntegrableOn q (Ioc 0 1)) :
    IntegrableOn (fun u ↦ q u * ∫ x in Ici (Real.log u), f x) (Ioc 0 1) ∧
    (∫ x, f x * ∫ u in Ioc 0 (min (Real.exp x) 1), q u) =
      ∫ u in Ioc 0 1, q u * ∫ x in Ici (Real.log u), f x := by
  let A : Set (ℝ × ℝ) := {p | p.2 ≤ Real.exp p.1}
  let G : ℝ × ℝ → ℝ := A.indicator (fun p ↦ f p.1 * q p.2)
  have hA : MeasurableSet A := measurableSet_le measurable_snd
    (Real.measurable_exp.comp measurable_fst)
  have hG : Integrable G (volume.prod (volume.restrict (Ioc 0 1))) :=
    (hf.mul_prod hq).indicator hA
  have hleft (x : ℝ) : (∫ u in Ioc 0 1, G (x, u)) =
      f x * ∫ u in Ioc 0 (min (Real.exp x) 1), q u := by
    have hsec : (fun u ↦ G (x, u)) = (Iic (Real.exp x)).indicator (fun u ↦ f x * q u) := by
      funext u
      by_cases h : u ≤ Real.exp x <;> simp [G, A, Set.indicator, h]
    have hset : Ioc (0 : ℝ) 1 ∩ Iic (Real.exp x) = Ioc 0 (min (Real.exp x) 1) := by
      ext u
      simp only [mem_inter_iff, mem_Ioc, mem_Iic, le_min_iff]
      tauto
    rw [hsec, setIntegral_indicator measurableSet_Iic, hset, integral_const_mul]
  have hright (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) 1) :
      (∫ x, G (x, u)) = q u * ∫ x in Ici (Real.log u), f x := by
    have hsec : (fun x ↦ G (x, u)) = (Ici (Real.log u)).indicator (fun x ↦ q u * f x) := by
      funext x
      by_cases hx : u ≤ Real.exp x
      · have hl := (Real.log_le_iff_le_exp hu.1).2 hx
        simp [G, A, Set.indicator, hx, hl, mul_comm]
      · have hl := (Real.log_le_iff_le_exp hu.1).not.mpr hx
        simp [G, A, Set.indicator, hx, hl]
    rw [hsec, integral_indicator measurableSet_Ici, integral_const_mul]
  refine ⟨IntegrableOn.congr_fun hG.integral_prod_right hright measurableSet_Ioc, ?_⟩
  calc
    _ = ∫ x, ∫ u in Ioc 0 1, G (x, u) := integral_congr_ae (.of_forall fun x ↦ (hleft x).symm)
    _ = ∫ u in Ioc 0 1, ∫ x, G (x, u) := integral_integral_swap (f := fun x u ↦ G (x, u)) hG
    _ = _ := setIntegral_congr_fun measurableSet_Ioc hright

private theorem halfWeighted_integrable {H : ℝ → ℝ} (hH : Continuous H)
    (hcomp : HasCompactSupport H) : Integrable (fun x ↦ H x * Real.exp (-x / 2)) :=
  (hH.mul (by fun_prop : Continuous (fun x : ℝ ↦ Real.exp (-x / 2)))).integrable_of_hasCompactSupport
    hcomp.mul_right

private theorem halfWeighted_tail {H : ℝ → ℝ} {R : ℝ}
    (hsupp : tsupport H ⊆ Iic R) (a : ℝ) :
    (∫ x in Ici a, H x * Real.exp (-x / 2)) = ∫ x in Ioc a R, H x * Real.exp (-x / 2) := by
  rw [integral_Ici_eq_integral_Ioi]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Ioc a R) measurableSet_Ioi (fun _ hx ↦ hx.1)
  intro x hx
  have hR : ¬x ≤ R := fun h ↦ hx.2 ⟨hx.1, h⟩
  rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hR (hsupp h)), zero_mul]

private theorem integrableOn_gate {Q : ℝ → ℝ} (hQ : Measurable Q)
    (hbound : ∀ u ∈ Ioc (0 : ℝ) 1, Q u ∈ Icc 0 1) : IntegrableOn Q (Ioc 0 1) := by
  apply (integrableOn_const (C := (1 : ℝ)) measure_Ioc_lt_top.ne).mono' hQ.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with u hu
  rw [Real.norm_of_nonneg (hbound u hu).1]
  exact (hbound u hu).2

/-- The genuine gate defect expressed as its tail kernel in the gate variable. -/
theorem rankOneDefect_eq_tail {H Q : ℝ → ℝ} {R : ℝ} (hH : Continuous H)
    (hcomp : HasCompactSupport H) (hsupp : tsupport H ⊆ Iic R) (hQ : IntegrableOn Q (Ioc 0 1)) :
    rankOneDefect H Q = ∫ u in Ioc 0 1, Q u * ∫ x in Ioc (Real.log u) R,
      H x * Real.exp (-x / 2) := by
  exact (gateFubini _ _ (halfWeighted_integrable hH hcomp) hQ).2.trans
    (setIntegral_congr_fun measurableSet_Ioc fun u _ ↦ congrArg (Q u * ·) (halfWeighted_tail hsupp _))

private theorem tail_integrableOn {H Q : ℝ → ℝ} {R : ℝ} (hH : Continuous H)
    (hcomp : HasCompactSupport H) (hsupp : tsupport H ⊆ Iic R)
    (hQ : IntegrableOn Q (Ioc 0 1)) :
    IntegrableOn (fun u ↦ Q u * ∫ x in Ioc (Real.log u) R, H x * Real.exp (-x / 2)) (Ioc 0 1) :=
  (gateFubini _ _ (halfWeighted_integrable hH hcomp) hQ).1.congr_fun
    (fun u _ ↦ congrArg (Q u * ·) (halfWeighted_tail hsupp _)) measurableSet_Ioc

/-- Exact change from the ungated to the gated rank-one defect. -/
theorem rankOneDefect_one_sub_eq {H Q : ℝ → ℝ} {R : ℝ} (hH : Continuous H)
    (hcomp : HasCompactSupport H) (hsupp : tsupport H ⊆ Iic R) (hQ : IntegrableOn Q (Ioc 0 1)) :
    rankOneDefect H (fun _ ↦ 1) - rankOneDefect H Q =
      ∫ u in Ioc 0 1, (1 - Q u) * ∫ x in Ioc (Real.log u) R, H x * Real.exp (-x / 2) := by
  have hone : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Ioc 0 1) :=
    integrableOn_const measure_Ioc_lt_top.ne
  rw [rankOneDefect_eq_tail hH hcomp hsupp hone, rankOneDefect_eq_tail hH hcomp hsupp hQ,
    ← integral_sub (tail_integrableOn hH hcomp hsupp hone) (tail_integrableOn hH hcomp hsupp hQ)]
  exact setIntegral_congr_fun measurableSet_Ioc fun u _ ↦ by simp only [sub_mul]

/-- A plateau at the origin ensures that the real logarithmic loss is integrable. -/
theorem integrableOn_logLoss {Q : ℝ → ℝ} (hQ : Measurable Q)
    (hbound : ∀ u ∈ Ioc (0 : ℝ) 1, Q u ∈ Icc 0 1)
    (hplateau : ∃ δ > 0, ∀ u ∈ Ioc 0 δ, Q u = 1) :
    IntegrableOn (fun u ↦ (1 - Q u) / u) (Ioc 0 1) := by
  obtain ⟨δ, hδ, hplat⟩ := hplateau
  apply (integrableOn_const (C := 1 / δ) measure_Ioc_lt_top.ne).mono'
    ((measurable_const.sub hQ).div measurable_id).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with u hu
  have hb := hbound u hu
  change ‖(1 - Q u) / u‖ ≤ 1 / δ
  rw [Real.norm_of_nonneg (div_nonneg (sub_nonneg.mpr hb.2) hu.1.le)]
  by_cases h : u ≤ δ
  · rw [hplat u ⟨hu.1, h⟩]
    simp [hδ.le]
  · calc
      (1 - Q u) / u ≤ 1 / u := div_le_div_of_nonneg_right (by linarith [hb.1]) hu.1.le
      _ ≤ 1 / δ := one_div_le_one_div_of_le hδ (le_of_not_ge h)

/-- The weighted mass of an interval in the logarithmic coordinate. -/
private theorem gateKernel_integral_eq {u b : ℝ} (hu : 0 < u) (hub : u ≤ b) (M : ℝ) :
    u * (∫ x in Ioc (Real.log u) (Real.log b), M * Real.exp (-x / 2)) =
      2 * M * (Real.sqrt u - u / Real.sqrt b) := by
  have hexp {v : ℝ} (hv : 0 < v) :
      Real.exp (Real.log v * (-(1 / 2) : ℝ)) = (Real.sqrt v)⁻¹ := by
    rw [mul_neg, Real.exp_neg, ← Real.rpow_def_of_pos hv, Real.sqrt_eq_rpow]
  have hscale : (fun x : ℝ ↦ Real.exp (-x / 2)) =
      fun x : ℝ ↦ Real.exp (x * (-(1 / 2) : ℝ)) :=
    funext fun x ↦ congrArg Real.exp (by ring)
  calc
    _ = 2 * M * (u / Real.sqrt u - u / Real.sqrt b) := by
      rw [integral_const_mul, ← intervalIntegral.integral_of_le (Real.log_le_log hu hub),
        hscale, intervalIntegral.integral_comp_mul_right Real.exp
          (by norm_num : (-(1 / 2) : ℝ) ≠ 0), integral_exp, smul_eq_mul,
        hexp (hu.trans_le hub), hexp hu]
      rw [show (-(1 / 2) : ℝ)⁻¹ = -2 by norm_num]
      ring
    _ = _ := by rw [Real.div_sqrt]

/-- Completing the square gives the sharp bound at every upper endpoint. -/
private theorem gateKernel_integral_le {u b M : ℝ} (hu : 0 < u) (hub : u ≤ b) (hM : 0 ≤ M) :
    u * (∫ x in Ioc (Real.log u) (Real.log b), M * Real.exp (-x / 2)) ≤
      M * (Real.sqrt b / 2) := by
  have hb : 0 < Real.sqrt b := Real.sqrt_pos.mpr (hu.trans_le hub)
  have h : 2 * (Real.sqrt u - u / Real.sqrt b) ≤ Real.sqrt b / 2 := by
    apply (mul_le_mul_iff_right₀ hb).mp
    calc
      Real.sqrt b * (2 * (Real.sqrt u - u / Real.sqrt b)) = 2 * Real.sqrt b * Real.sqrt u - 2 * u := by
        field_simp
      _ ≤ Real.sqrt b * (Real.sqrt b / 2) := by
        nlinarith only [sq_nonneg (Real.sqrt b - 2 * Real.sqrt u), Real.sq_sqrt hu.le]
  rw [gateKernel_integral_eq hu hub]
  calc
    _ = M * (2 * (Real.sqrt u - u / Real.sqrt b)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h hM

/-- The half-weighted interval kernel has upper bound `M / √2` on the first prime shell. -/
theorem gateKernel_integral_le_inv_sqrt_two {u M : ℝ} (hu : 0 < u) (hu₁ : u ≤ 1) (hM : 0 ≤ M) :
    u * (∫ x in Ioc (Real.log u) (Real.log 2), M * Real.exp (-x / 2)) ≤ M / Real.sqrt 2 := by
  simpa only [Real.sqrt_div_self', mul_one_div] using
    gateKernel_integral_le hu (hu₁.trans (by norm_num : (1 : ℝ) ≤ 2)) hM

/-- The compensation by the logarithmic loss exceeds the ungated defect by at least
`(1 - 1 / √2) * H 0 * logLoss Q` in the rational log-norm window up to `log 2`.
A compact continuous profile suffices, and only its upper support endpoint is used. -/
theorem compensated_defect_lower_bound {H Q : ℝ → ℝ} (hH : Continuous H)
    (hcomp : HasCompactSupport H) (hsupp : tsupport H ⊆ Iic (Real.log 2))
    (hzero : 0 ≤ H 0) (hcap : ∀ x, H x ≤ H 0) (hQ : Measurable Q)
    (hbound : ∀ u ∈ Ioc (0 : ℝ) 1, Q u ∈ Icc 0 1)
    (hplateau : ∃ δ > 0, ∀ u ∈ Ioc 0 δ, Q u = 1) :
    rankOneDefect H (fun _ ↦ 1) + (1 - 1 / Real.sqrt 2) * H 0 * logLoss Q ≤
      rankOneDefect H Q + H 0 * logLoss Q := by
  have hQi := integrableOn_gate hQ hbound
  have hbase : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Ioc 0 1) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hΔ : IntegrableOn (fun u ↦ 1 - Q u) (Ioc 0 1) := hbase.sub hQi
  have hL := integrableOn_logLoss hQ hbound hplateau
  have hk (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) 1) :
      (1 - Q u) * (∫ x in Ioc (Real.log u) (Real.log 2), H x * Real.exp (-x / 2)) ≤
      (H 0 / Real.sqrt 2) * ((1 - Q u) / u) := by
    have hcont : Continuous (fun x : ℝ ↦ H 0 * Real.exp (-x / 2)) := by fun_prop
    have htail := setIntegral_mono_on
      (s := Ioc (Real.log u) (Real.log 2)) (halfWeighted_integrable hH hcomp).integrableOn
      hcont.integrableOn_Ioc measurableSet_Ioc
      (fun x _ ↦ mul_le_mul_of_nonneg_right (hcap x) (Real.exp_pos _).le)
    have hsum := (mul_le_mul_of_nonneg_left htail hu.1.le).trans
      (gateKernel_integral_le_inv_sqrt_two hu.1 hu.2 hzero)
    have hdiv := (le_div_iff₀ hu.1).2 ((mul_comm _ u) ▸ hsum)
    calc
      _ ≤ (1 - Q u) * ((H 0 / Real.sqrt 2) / u) :=
        mul_le_mul_of_nonneg_left hdiv (sub_nonneg.mpr (hbound u hu).2)
      _ = _ := by ring
  have hcum := setIntegral_mono_on (tail_integrableOn hH hcomp hsupp hΔ)
    (Integrable.const_mul hL (H 0 / Real.sqrt 2)) measurableSet_Ioc hk
  rw [← rankOneDefect_one_sub_eq hH hcomp hsupp hQi, integral_const_mul] at hcum
  change rankOneDefect H (fun _ ↦ 1) - rankOneDefect H Q ≤ H 0 / Real.sqrt 2 * logLoss Q at hcum
  calc
    _ = (rankOneDefect H (fun _ ↦ 1) - rankOneDefect H Q - H 0 / Real.sqrt 2 * logLoss Q) +
          (rankOneDefect H Q + H 0 * logLoss Q) := by ring
    _ ≤ _ := by linarith only [hcum]

/-- In the absence of a gate the rank-one defect is the bilateral exponential pairing. -/
theorem rankOneDefect_one (H : ℝ → ℝ) :
    rankOneDefect H (fun _ ↦ 1) = ∫ x : ℝ, Real.exp (-(1 / 2) * |x|) * H x := by
  unfold rankOneDefect
  apply integral_congr_ae
  filter_upwards with x
  have hlen : (∫ _u in Ioc (0 : ℝ) (min (Real.exp x) 1), (1 : ℝ)) = min (Real.exp x) 1 := by
    rw [← intervalIntegral.integral_of_le (le_min (Real.exp_pos _).le zero_le_one)]
    simp
  rw [hlen]
  by_cases hx : x ≤ 0
  · rw [min_eq_left (by simpa using Real.exp_le_exp.mpr hx), abs_of_nonpos hx,
      mul_assoc, ← Real.exp_add, mul_comm]
    congr 2
    ring
  · rw [min_eq_right (by simpa using Real.exp_le_exp.mpr (le_of_not_ge hx)), mul_one,
      abs_of_nonneg (le_of_not_ge hx), mul_comm]
    congr 2
    ring

/-- The logarithmic loss of an upper gate is nonnegative. -/
theorem logLoss_nonneg {Q : ℝ → ℝ} (hbound : ∀ u ∈ Ioc (0 : ℝ) 1, Q u ≤ 1) :
    0 ≤ logLoss Q := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with u hu
  exact div_nonneg (sub_nonneg.mpr (hbound u hu)) hu.1.le

/-- For a real even compact smooth profile, positivity of its bilateral Laplace transform
on the imaginary axis gives a positive value at zero and bounds the absolute value of
every translate by that value. -/
private theorem abs_le_at_zero_of_bilateralLaplace_re_pos (H : ℝ → ℝ)
    (hc : HasCompactSupport H) (hs : ContDiff ℝ ∞ H) (heven : ∀ x, H (-x) = H x)
    (hpos : ∀ t : ℝ, 0 < (bilateralLaplace (fun x ↦ (H x : ℂ)) (t * I)).re) :
    0 < H 0 ∧ ∀ x, |H x| ≤ H 0 := by
  let u : 𝓢(ℝ, ℂ) :=
    (hc.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hs)
  let F : 𝓢(ℝ, ℂ) := 𝓕 u
  have hu (x : ℝ) : u x = (H x : ℂ) := rfl
  have hfreq (t : ℝ) : F t =
      bilateralLaplace (fun x ↦ (H x : ℂ)) ((-2 * Real.pi * t : ℝ) * I) := by
    change (𝓕 u) t = _
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
    unfold bilateralLaplace
    apply integral_congr_ae
    filter_upwards with x
    rw [smul_eq_mul, hu, mul_comm (H x : ℂ)]
    congr 2
    push_cast
    ring
  have hp (t : ℝ) : 0 < (F t).re := hfreq t ▸ hpos _
  have hreal (t : ℝ) : conj (bilateralLaplace (fun x ↦ (H x : ℂ)) (t * I)) =
      bilateralLaplace (fun x ↦ (H x : ℂ)) (t * I) := by
    let v (x : ℝ) := (H x : ℂ) * Complex.exp (t * I * x)
    change conj (∫ x, v x) = ∫ x, v x
    rw [← integral_conj]
    calc
      (∫ x, conj (v x)) = ∫ x : ℝ, v (-x) := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        simp only [v, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I,
          Complex.ofReal_neg, heven]
        ring_nf
      _ = _ := integral_neg_eq_self v volume
  have hn (t : ℝ) : ‖F t‖ = (F t).re := by
    have h : conj (F t) = F t := hfreq t ▸ hreal _
    calc
      ‖F t‖ = ‖((F t).re : ℂ)‖ := congrArg norm (Complex.conj_eq_iff_re.mp h).symm
      _ = _ := by rw [Complex.norm_real, Real.norm_of_nonneg (hp t).le]
  have hinv (x : ℝ) : 𝓕 (F : ℝ → ℂ) (-x) = (H x : ℂ) := by
    rw [← Real.fourierInv_eq_fourier_neg, ← SchwartzMap.fourierInv_coe]
    exact congrArg (fun v : 𝓢(ℝ, ℂ) ↦ v x) (FourierTransform.fourierInv_fourier_eq u)
  have hint : Integrable (F : ℝ → ℂ) := F.integrable
  have hmass : (∫ t : ℝ, ‖F t‖) = H 0 := by
    have hzero : (∫ t : ℝ, F t) = (H 0 : ℂ) := by
      simpa [Real.fourier_real_eq_integral_exp_smul] using hinv 0
    simp_rw [hn]
    exact (integral_re hint).trans (congrArg Complex.re hzero)
  constructor
  · rw [← hmass]
    exact integral_pos_of_integrable_nonneg_ne_zero F.continuous.norm hint.norm
      (fun t ↦ norm_nonneg _) (x := 0) (hn 0 ▸ (hp 0).ne')
  · intro x
    calc
      |H x| = ‖𝓕 (F : ℝ → ℂ) (-x)‖ := by rw [hinv, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ∫ t : ℝ, ‖F t‖ := Real.norm_fourier_le_integral_norm _ _
      _ = _ := hmass

/-- A positive real Mellin spectrum for an even test supplies both the positive ungated defect
and the maximum at zero needed for the quantitative gate bound. -/
theorem compensated_defect_of_positive_spectrum {H Q : ℝ → ℝ} (hH : ContDiff ℝ ∞ H)
    (hsupp : tsupport H ⊆ Ioo (-Real.log 2) (Real.log 2))
    (heven : ∀ x, H (-x) = H x)
    (hpos : ∀ t : ℝ, 0 < (bilateralLaplace (fun x ↦ (H x : ℂ)) (t * Complex.I)).re)
    (hQ : Measurable Q) (hbound : ∀ u ∈ Ioc (0 : ℝ) 1, Q u ∈ Icc 0 1)
    (hplateau : ∃ δ > 0, ∀ u ∈ Ioc 0 δ, Q u = 1) :
    0 < rankOneDefect H (fun _ ↦ 1) ∧
    rankOneDefect H (fun _ ↦ 1) + (1 - 1 / Real.sqrt 2) * H 0 * logLoss Q ≤
      rankOneDefect H Q + H 0 * logLoss Q ∧
    0 < rankOneDefect H Q + H 0 * logLoss Q := by
  have hcomp : HasCompactSupport H :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport H) (hsupp.trans Ioo_subset_Icc_self)
  obtain ⟨hzero, hmax⟩ := abs_le_at_zero_of_bilateralLaplace_re_pos H hcomp hH heven hpos
  have hD : 0 < rankOneDefect H (fun _ ↦ 1) := by
    rw [rankOneDefect_one]
    exact integral_exp_neg_abs_mul_pos_of_bilateralLaplace H hcomp hH hpos (by norm_num)
  have hineq := compensated_defect_lower_bound hH.continuous hcomp (fun x hx ↦ (hsupp hx).2.le) hzero.le
    (fun x ↦ (le_abs_self _).trans (hmax x)) hQ hbound hplateau
  have hcoef : 0 < 1 - 1 / Real.sqrt 2 :=
    sub_pos.mpr (by simpa using one_div_lt_one_div_of_lt zero_lt_one Real.one_lt_sqrt_two)
  have hL := logLoss_nonneg fun u hu ↦ (hbound u hu).2
  exact ⟨hD, hineq, (add_pos_of_pos_of_nonneg hD (mul_nonneg (mul_pos hcoef hzero).le hL)).trans_le hineq⟩

/-- If the profile starts above a gate supported in `(0,r]`, then the inner gate mass
is constant throughout the support of the profile. -/
theorem rankOneDefect_eq_gateMass_mul {H Q : ℝ → ℝ} {r : ℝ} (hr₁ : r ≤ 1)
    (hH : ∀ x, Real.exp x < r → H x = 0) (hQ : ∀ u ∈ Ioc r 1, Q u = 0) :
    rankOneDefect H Q = (∫ u in Ioc 0 r, Q u) * ∫ x, H x * Real.exp (-x / 2) := by
  rw [rankOneDefect, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : Real.exp x < r
  · simp [hH x hx]
  · have he : (∫ u in Ioc 0 (min (Real.exp x) 1), Q u) = ∫ u in Ioc 0 r, Q u := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Ioc 0 r) measurableSet_Ioc
        (fun u hu ↦ ⟨hu.1, hu.2.trans (le_min (le_of_not_gt hx) hr₁)⟩)
      intro u hu
      exact hQ u ⟨lt_of_not_ge (fun h ↦ hu.2 ⟨hu.1.1, h⟩),
        hu.1.2.trans (min_le_right _ _)⟩
    rw [he]
    ring

/-- The normalized sharp upper frequency gate of relative size `r`. -/
def upperStep (r : ℝ) : ℝ → ℝ := (Icc (0 : ℝ) r).indicator (fun _ ↦ (1 : ℝ))

/-- The sharp upper gate is measurable, bounded between zero and one, and identically
one on the closed interval from norm zero to its cutoff. -/
theorem upperStep_admissible (r : ℝ) : Measurable (upperStep r) ∧
    (∀ u, upperStep r u ∈ Icc (0 : ℝ) 1) ∧ ∀ u ∈ Icc 0 r, upperStep r u = 1 := by
  refine ⟨measurable_const.indicator measurableSet_Icc, ?_, fun u hu ↦ indicator_of_mem hu _⟩
  intro u
  by_cases hu : u ∈ Icc (0 : ℝ) r <;> simp [upperStep, Set.indicator, hu]

/-- The logarithmic loss of the sharp upper gate is exactly the lost logarithmic length. -/
theorem logLoss_upperStep {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1) :
    logLoss (upperStep r) = -Real.log r := by
  let g (u : ℝ) := (1 - upperStep r u) / u
  change (∫ u in Ioc (0 : ℝ) 1, g u) = _
  have hcut : (∫ u in Ioc (0 : ℝ) 1, g u) = ∫ u in Ioc r 1, g u := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (s := Ioc r 1) measurableSet_Ioc
      (fun u hu ↦ ⟨hr.trans hu.1, hu.2⟩)
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) r := ⟨hu.1.1.le, le_of_not_gt fun h ↦ hu.2 ⟨h, hu.1.2⟩⟩
    simp only [g, upperStep, indicator_of_mem hu', sub_self, zero_div]
  have he (u : ℝ) (hu : u ∈ Ioc r 1) : g u = 1 / u := by
    have hu' : u ∉ Icc (0 : ℝ) r := fun h ↦ hu.1.not_ge h.2
    simp only [g, upperStep, indicator_of_notMem hu', sub_zero]
  rw [hcut, setIntegral_congr_fun measurableSet_Ioc he, ← intervalIntegral.integral_of_le hr₁,
    integral_one_div_of_pos hr zero_lt_one, one_div, Real.log_inv]

/-- On profiles supported above the sharp upper gate, the defect is linear in its width. -/
theorem rankOneDefect_upperStep {H : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hH : ∀ x, Real.exp x < r → H x = 0) :
    rankOneDefect H (upperStep r) = r * ∫ x, H x * Real.exp (-x / 2) := by
  have hQ (u : ℝ) (hu : u ∈ Ioc r 1) : upperStep r u = 0 :=
    indicator_of_notMem (fun h : u ∈ Icc (0 : ℝ) r ↦ hu.1.not_ge h.2) _
  have hmass : (∫ u in Ioc 0 r, upperStep r u) = r := by
    calc
      _ = ∫ _u in Ioc 0 r, (1 : ℝ) :=
        setIntegral_congr_fun measurableSet_Ioc fun _ hu ↦ (upperStep_admissible r).2.2 _ ⟨hu.1.le, hu.2⟩
      _ = r := by rw [← intervalIntegral.integral_of_le hr.le]; simp
  rw [rankOneDefect_eq_gateMass_mul hr₁ hH hQ, hmass]

/-- Balancing the spatial cutoff by `1/r` cancels the logarithmic displacement.
The remaining correction is the negative half-Mellin moment times `r`. -/
theorem compensated_upperStep {H : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (hr₁ : r ≤ 1)
    (hH : ∀ x, Real.exp x < r → H x = 0) (P a : ℝ) :
    P + a * (Real.log (1 / r) - logLoss (upperStep r)) - rankOneDefect H (upperStep r) =
      P - r * ∫ x, H x * Real.exp (-x / 2) := by
  rw [one_div, Real.log_inv, logLoss_upperStep hr hr₁, sub_self, mul_zero, add_zero,
    rankOneDefect_upperStep hr hr₁ hH]

/-- Once the translated support lies to the right of norm one, the gate contributes
its full mass and the radial factor is the negative half-Mellin moment. The open
left support endpoint also gives vanishing at norm one when y = R. -/
theorem rankOneDefect_translate_of_le {H : ℝ → ℝ} (Q : ℝ → ℝ) {R y : ℝ}
    (hs : tsupport H ⊆ Ioo (-R) R) (hy : R ≤ y) :
    rankOneDefect (fun x ↦ H (x - y)) Q =
      (∫ u in Ioc (0 : ℝ) 1, Q u) * Real.exp (-y / 2) * (∫ x : ℝ, H x * Real.exp (-x / 2)) ∧
    H (-y) = 0 := by
  have hzero (x : ℝ) (hx : x ≤ 0) : H (x - y) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    linarith [(hs h).1]
  refine ⟨?_, by simpa only [zero_sub] using hzero 0 le_rfl⟩
  rw [rankOneDefect_eq_gateMass_mul (r := 1) le_rfl
    (fun x hx ↦ hzero x (Real.exp_lt_one_iff.mp hx).le) (by simp)]
  let f (x : ℝ) := H x * Real.exp (-x / 2)
  have he (x : ℝ) : H (x - y) * Real.exp (-x / 2) = Real.exp (-y / 2) * f (x - y) := by
    rw [show -x / 2 = -y / 2 + -(x-y) / 2 by ring, Real.exp_add]
    dsimp only [f]
    ring
  simp_rw [he, integral_const_mul, integral_sub_right_eq_self]
  ring

/-- The real half-weight integral is the value of the real profile's bilateral
Laplace transform at the negative half pole, with the logarithmic-coordinate
normalization used in the rational upper gate. -/
theorem halfMoment_eq_re_bilateralLaplace (H : ℝ → ℝ) :
    (∫ x : ℝ, H x * Real.exp (-x / 2)) =
      (bilateralLaplace (fun x ↦ (H x : ℂ)) (-1 / 2 : ℂ)).re := by
  have he (x : ℝ) : ((H x * Real.exp (-x / 2) : ℝ) : ℂ) =
      (H x : ℂ) * Complex.exp ((-1 / 2 : ℂ) * x) := by
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    congr 2
    push_cast
    ring
  calc
    _ = (∫ x : ℝ, ((H x * Real.exp (-x / 2) : ℝ) : ℂ)).re := by
      rw [integral_complex_ofReal, Complex.ofReal_re]
    _ = _ := congrArg Complex.re (integral_congr_ae (.of_forall he))



/-- Both scales can be chosen below the norm support of any compact log profile. -/
theorem exists_two_upperSteps_below_support {E : Type*} [Zero E] (H : ℝ → E) (hc : HasCompactSupport H) :
    ∃ r > 0, 2 * r ≤ 1 ∧ ∀ x, Real.exp x < 2 * r → H x = 0 := by
  obtain ⟨A, hA⟩ := hc.isBounded.exists_norm_le
  refine ⟨min 1 (Real.exp (-A)) / 2, by positivity, ?_, ?_⟩
  · linarith only [min_le_left (1 : ℝ) (Real.exp (-A))]
  · intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have ha := hA x h
    rw [Real.norm_eq_abs] at ha
    have he := Real.exp_le_exp.mpr (abs_le.mp ha).1
    linarith only [hx, he, min_le_right (1 : ℝ) (Real.exp (-A))]

/-- At relative frequency width `1/2`, the opposite polar moment kills the rank-one
term of each profile supported in norms at least `1/2`. Spatial scale two then
cancels the logarithmic loss. -/
theorem upperStep_half_of_polar {H : ℝ → ℝ} (hS : tsupport H ⊆ Ici (-Real.log 2))
    (hpolar : bilateralLaplace (fun x ↦ (H x : ℂ)) (-(1/2) : ℂ) = 0) :
    rankOneDefect H (upperStep (1/2)) = 0 ∧ logLoss (upperStep (1/2)) = Real.log 2 := by
  have hlog : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have hcut (x : ℝ) (hx : Real.exp x < 1 / 2) : H x = 0 := by
    have hl := Real.log_lt_log (Real.exp_pos x) hx
    rw [Real.log_exp, hlog] at hl
    exact image_eq_zero_of_notMem_tsupport (fun h ↦ hl.not_ge (hS h))
  constructor
  · rw [rankOneDefect_upperStep (by norm_num) (by norm_num) hcut, halfMoment_eq_re_bilateralLaplace]
    simp only [neg_div, hpolar, Complex.zero_re, mul_zero]
  · rw [logLoss_upperStep (by norm_num) (by norm_num), hlog, neg_neg]

/-- Below the norm support, the clipped complex rank-one integral in the sharp-gate
formula is the gate width times the negative half-Mellin moment. -/
theorem clipped_halfMoment_eq_bilateralLaplace {H : ℝ → ℂ} {r : ℝ}
    (hH : ∀ x, Real.exp x < r → H x = 0) :
    (∫ x : ℝ, H x * ((Real.exp (-x / 2) * min (Real.exp x) r : ℝ) : ℂ)) =
      (r : ℂ) * bilateralLaplace H (-(1 / 2) : ℂ) := by
  unfold bilateralLaplace
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : Real.exp x < r
  · simp only [hH x hx, zero_mul, mul_zero]
  · rw [min_eq_right (le_of_not_gt hx), Complex.ofReal_mul, Complex.ofReal_exp]
    have he : ((-x / 2 : ℝ) : ℂ) = -(1 / 2 : ℂ) * x := by push_cast; ring
    rw [he]
    ring


/-- Two spatially balanced sharp gates below the shared norm support recover the
principal value and the negative polar moment of a complex profile. The trace law
is needed only at the two fixed radii. -/
theorem upperStep_twoScale_reconstruction {H : ℝ → ℂ} {r : ℝ}
    (hr : 0 < r) (hr₂ : 2 * r ≤ 1) (hH : ∀ x, Real.exp x < 2 * r → H x = 0)
    (T : ℝ → ℂ) (P a : ℂ)
    (hT : ∀ s ∈ ({r, 2 * r} : Set ℝ), T s =
      P + a * ((Real.log (1 / s) - logLoss (upperStep s) : ℝ) : ℂ) -
        ∫ x : ℝ, H x * ((Real.exp (-x / 2) * min (Real.exp x) s : ℝ) : ℂ)) :
    2 * T r - T (2 * r) = P ∧
      (T r - T (2 * r)) / (r : ℂ) = bilateralLaplace H (-(1 / 2) : ℂ) := by
  have hs (s : ℝ) (hm : s ∈ ({r, 2 * r} : Set ℝ)) (hp : 0 < s) (hle : s ≤ 2 * r) :
      T s = P - (s : ℂ) * bilateralLaplace H (-(1 / 2) : ℂ) := by
    rw [hT s hm, one_div, Real.log_inv, logLoss_upperStep hp (hle.trans hr₂),
      sub_self, Complex.ofReal_zero, mul_zero, add_zero,
      clipped_halfMoment_eq_bilateralLaplace (fun x hx ↦ hH x (hx.trans_le hle))]
  rw [hs r (by simp) hr (by linarith), hs (2 * r) (by simp) (by positivity) le_rfl]
  push_cast
  constructor
  · ring
  · apply (div_eq_iff (Complex.ofReal_ne_zero.mpr hr.ne')).2
    ring

/-- The two fixed-scale trace laws recover the two-pole residual for a complex
smooth profile. The trace law is the clipped integral supplied by the weighted rational
local calculation. Both input profiles have support contained in the support of `H`. -/
theorem twoScaleTrace_eq_twoPolarResidual
    (H : ℝ → ℂ) (hHs : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H)
    (T : ℝ → (ℝ → ℂ) → ℂ) (PV : (ℝ → ℂ) → ℂ) {r : ℝ}
    (hr : 0 < r) (hr1 : 2 * r ≤ 1)
    (hbelow : ∀ x, Real.exp x < 2 * r → H x = 0)
    (hPV : ∀ f g : ℝ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
      ContDiff ℝ ∞ g → HasCompactSupport g → PV (f + g) = PV f + PV g)
    (hT : ∀ s : ℝ, (s = r ∨ s = 2 * r) → s ∈ Ioc (0 : ℝ) 1 →
      ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ tsupport H →
      (∀ x, Real.exp x < s → f x = 0) →
      T s f = PV f - ∫ x : ℝ, f x * ((Real.exp (-x / 2) * min (Real.exp x) s : ℝ) : ℂ)) :
    let η := fun x : ℝ ↦ (1 + (Real.exp x : ℂ)) * H x
    let f := fun x : ℝ ↦ 2 * H x - η x / (r : ℂ)
    let g := fun x : ℝ ↦ η x / (r : ℂ) - H x
    T r f + T (2 * r) g =
      PV H - bilateralLaplace H (-(1 / 2) : ℂ) - bilateralLaplace H (1 / 2 : ℂ) := by
  intro η f g
  have hηs : ContDiff ℝ ∞ η :=
    (contDiff_const.add (Complex.ofRealCLM.contDiff.comp Real.contDiff_exp)).mul hHs
  have hdiv : ContDiff ℝ ∞ (fun x ↦ η x / (r : ℂ)) := by
    simpa only [div_eq_mul_inv] using hηs.mul (contDiff_const (c := (r : ℂ)⁻¹))
  have hfs : ContDiff ℝ ∞ f := (contDiff_const.mul hHs).sub hdiv
  have hgs : ContDiff ℝ ∞ g := hdiv.sub hHs
  have hz (x : ℝ) (hx : H x = 0) : f x = 0 ∧ g x = 0 := by
    simp [f, g, η, hx]
  have hsf : tsupport f ⊆ tsupport H :=
    closure_mono (show Function.support f ⊆ Function.support H from
      fun x hfx hHx ↦ hfx (hz x hHx).1)
  have hsg : tsupport g ⊆ tsupport H :=
    closure_mono (show Function.support g ⊆ Function.support H from
      fun x hgx hHx ↦ hgx (hz x hHx).2)
  have hfc : HasCompactSupport f := hHc.of_isClosed_subset (isClosed_tsupport f) hsf
  have hgc : HasCompactSupport g := hHc.of_isClosed_subset (isClosed_tsupport g) hsg
  have hfb (x : ℝ) (hx : Real.exp x < r) : f x = 0 := (hz x (hbelow x (by linarith))).1
  have hgb (x : ℝ) (hx : Real.exp x < 2 * r) : g x = 0 := (hz x (hbelow x hx)).2
  have hTf := hT r (Or.inl rfl) ⟨hr, by linarith⟩ f hfs hfc hsf hfb
  have hTg := hT (2 * r) (Or.inr rfl) ⟨by linarith, hr1⟩ g hgs hgc hsg hgb
  rw [clipped_halfMoment_eq_bilateralLaplace hfb] at hTf
  rw [clipped_halfMoment_eq_bilateralLaplace hgb] at hTg
  have hsum : f + g = H := by
    ext x
    change (2 * H x - η x / (r : ℂ)) + (η x / (r : ℂ) - H x) = H x
    ring
  have hPVsum : PV f + PV g = PV H := (hPV f g hfs hfc hgs hgc).symm.trans (congrArg PV hsum)
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hcoeff (x : ℝ) : (r : ℂ) * f x + ((2 * r : ℝ) : ℂ) * g x = η x := by
    dsimp only [f, g]
    push_cast
    field_simp [hrC]
    ring
  let m := fun x : ℝ ↦ Complex.exp ((-(1 / 2) : ℂ) * x)
  let p := fun x : ℝ ↦ Complex.exp ((1 / 2 : ℂ) * x)
  have hmp (x : ℝ) : (Real.exp x : ℂ) * m x = p x := by
    dsimp only [m, p]
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    ring
  have hInt {v : ℝ → ℂ} (hv : Continuous v) (hvc : HasCompactSupport v) (z : ℂ) :
      Integrable (fun x : ℝ ↦ v x * Complex.exp (z * x)) :=
    (hv.mul (by fun_prop)).integrable_of_hasCompactSupport hvc.mul_right
  have hfint : Integrable (fun x ↦ f x * m x) := hInt hfs.continuous hfc _
  have hgint : Integrable (fun x ↦ g x * m x) := hInt hgs.continuous hgc _
  have hmH : Integrable (fun x ↦ H x * m x) := hInt hHs.continuous hHc _
  have hpH : Integrable (fun x ↦ H x * p x) := hInt hHs.continuous hHc _
  have hmom : (r : ℂ) * bilateralLaplace f (-(1 / 2) : ℂ) +
      ((2 * r : ℝ) : ℂ) * bilateralLaplace g (-(1 / 2) : ℂ) =
      bilateralLaplace H (-(1 / 2) : ℂ) + bilateralLaplace H (1 / 2 : ℂ) := by
    change (r : ℂ) * (∫ x, f x * m x) + ((2 * r : ℝ) : ℂ) * (∫ x, g x * m x) =
      (∫ x, H x * m x) + ∫ x, H x * p x
    calc
      _ = ∫ x, (r : ℂ) * (f x * m x) + ((2 * r : ℝ) : ℂ) * (g x * m x) := by
        rw [integral_add (hfint.const_mul _) (hgint.const_mul _), integral_const_mul,
          integral_const_mul]
      _ = ∫ x, H x * m x + H x * p x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [← mul_assoc, ← mul_assoc _ (g x), ← add_mul, hcoeff, ← hmp]
        dsimp only [η]
        ring
      _ = _ := integral_add hmH hpH
  rw [hTf, hTg]
  calc
    _ = (PV f + PV g) - ((r : ℂ) * bilateralLaplace f (-(1 / 2) : ℂ) +
          ((2 * r : ℝ) : ℂ) * bilateralLaplace g (-(1 / 2) : ℂ)) := by ring
    _ = _ := by
      rw [hPVsum, hmom]
      ring

end RiemannMasullo.RationalUpperGate
