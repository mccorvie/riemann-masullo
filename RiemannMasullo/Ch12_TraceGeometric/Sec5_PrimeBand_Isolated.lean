module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
public import RiemannMasullo.ForMathlib.Analysis.MellinTransform.PositiveLaplace
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.RiemannZetaReal

/-! # The translated prime-power term in the rational trace comparison

A fixed log profile shifted by a real parameter gives the smoothed von Mangoldt
sum. Its Laplace transform is the Mellin transform of the profile times the
negative logarithmic derivative of zeta on the convergence half-plane. -/

@[expose] public noncomputable section

open MeasureTheory Complex Set
open scoped NNReal ENNReal

namespace RiemannMasullo.Isolated

private theorem bilateralLaplace_translate_tsum {ι : Type*} [Countable ι]
    (φ : ℝ → ℂ) (u : ι → ℝ) (c : ι → ℂ) (z : ℂ)
    (hφ : Integrable (fun t : ℝ ↦ φ t * exp (z * t)))
    (hc : Summable (fun n ↦ c n * exp (-z * u n))) :
    Integrable (fun y : ℝ ↦ (∑' n, c n * φ (u n - y)) * exp (-z * (y : ℂ))) ∧
    bilateralLaplace (fun y ↦ ∑' n, c n * φ (u n - y)) (-z) =
      (∑' n, c n * exp (-z * u n)) * bilateralLaplace φ z := by
  let d (n : ι) := c n * exp (-z * u n)
  let p (t : ℝ) := φ t * exp (z * t)
  let g (n : ι) (y : ℝ) := d n * p (u n - y)
  have hg (n : ι) (y : ℝ) : c n * φ (u n - y) * exp (-z * (y : ℂ)) = g n y := by
    dsimp [g, d, p]
    push_cast
    rw [mul_mul_mul_comm, ← exp_add]
    congr 2
    ring
  have hi (n : ι) : Integrable (g n) := by
    have h := (hφ.comp_add_right (u n)).comp_neg
    simpa only [g, p, sub_eq_add_neg, add_comm] using h.const_mul (d n)
  have hnorm (n : ι) : ∫ y, ‖g n y‖ = ‖d n‖ * ∫ t, ‖p t‖ := by
    simp only [g, norm_mul, integral_const_mul]
    exact congrArg (‖d n‖ * ·) (integral_sub_left_eq_self (fun t ↦ ‖p t‖) volume (u n))
  have hsum : Summable (fun n ↦ ∫ y, ‖g n y‖) := by
    simpa only [hnorm, d] using hc.norm.mul_right (∫ t, ‖p t‖)
  have hgmeas (n : ι) : AEMeasurable (fun y ↦ ‖g n y‖ₑ) := (hi n).1.eNorm
  have hmass : (∫⁻ y, ∑' n, ‖g n y‖ₑ) < ∞ := by
    rw [lintegral_tsum hgmeas]
    have hn (n : ι) : (∫⁻ y, ‖g n y‖ₑ) = ENNReal.ofReal (∫ y, ‖g n y‖) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hi n).norm (Filter.Eventually.of_forall
        fun y ↦ norm_nonneg (g n y))]
      simp only [ofReal_norm]
    simp_rw [hn]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) hsum]
    exact ENNReal.ofReal_lt_top
  have hInt : Integrable (fun y ↦ ∑' n, g n y) := by
    refine ⟨aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset ι))
      (fun s ↦ (integrable_finsetSum s fun n _ ↦ hi n).1) ?_, ?_⟩
    · exact (ae_lt_top' (AEMeasurable.tsum hgmeas) hmass.ne).mono fun y hy ↦
        (tsum_eNorm_ne_top_iff_summable_norm.mp hy.ne).of_norm.hasSum
    · rw [hasFiniteIntegral_iff_eNorm]
      exact (lintegral_mono fun _ ↦ eNorm_tsum_le_tsum_eNorm).trans_lt hmass
  have hseries (y : ℝ) : (∑' n, c n * φ (u n - y)) * exp (-z * (y : ℂ)) = ∑' n, g n y := by
    simp_rw [← tsum_mul_right, hg]
  refine ⟨hInt.congr (Filter.Eventually.of_forall fun y ↦ (hseries y).symm), ?_⟩
  have hval (n : ι) : ∫ y, g n y = d n * bilateralLaplace φ z := by
    simp only [g, integral_const_mul, bilateralLaplace]
    exact congrArg (d n * ·) (integral_sub_left_eq_self p volume (u n))
  rw [bilateralLaplace]
  simp_rw [hseries]
  rw [← integral_tsum_of_summable_integral_norm hi hsum]
  simp_rw [hval, tsum_mul_right]
  rfl

/-- The logarithmically translated von Mangoldt sum on the rational log-norm line. -/
def smoothedVonMangoldtBand (φ : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑' n : ℕ, LSeries.term (fun m ↦ (ArithmeticFunction.vonMangoldt m : ℂ)) (1 / 2) n *
    φ (Real.log n - Y)

private theorem integrable_and_bilateralLaplace_smoothedVonMangoldtBand (φ : ℝ → ℂ) (z : ℂ)
    (hφ : Integrable (fun t : ℝ ↦ φ t * exp (z * t))) (hz : 1 / 2 < z.re) :
    Integrable (fun y : ℝ ↦ smoothedVonMangoldtBand φ y * exp (-z * (y : ℂ))) ∧
    bilateralLaplace (smoothedVonMangoldtBand φ) (-z) =
      (-deriv riemannZeta (1 / 2 + z) / riemannZeta (1 / 2 + z)) * bilateralLaplace φ z := by
  let a (n : ℕ) := (ArithmeticFunction.vonMangoldt n : ℂ)
  have hterm (n : ℕ) : LSeries.term a (1 / 2) n * exp (-z * (Real.log n : ℂ)) =
      LSeries.term a (1 / 2 + z) n := by
    by_cases h : n = 0
    · simp [h]
    have hn : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast h
    rw [LSeries.term_of_ne_zero h, LSeries.term_of_ne_zero h, Complex.ofReal_log hn.le,
      Complex.ofReal_natCast, Complex.cpow_def_of_ne_zero hn',
      Complex.cpow_def_of_ne_zero hn']
    simp only [div_eq_mul_inv, ← Complex.exp_neg]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have hs : 1 < (1 / 2 + z).re := by
    rw [Complex.add_re]
    norm_num
    linarith
  have hc : Summable (fun n ↦ LSeries.term a (1 / 2) n * exp (-z * (Real.log n : ℂ))) := by
    simp_rw [hterm]
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  unfold smoothedVonMangoldtBand
  obtain ⟨hi, he⟩ := bilateralLaplace_translate_tsum φ (fun n : ℕ ↦ Real.log n)
    (LSeries.term a (1 / 2)) z hφ hc
  refine ⟨hi, he.trans ?_⟩
  simp_rw [hterm]
  exact congrArg (fun v ↦ v * bilateralLaplace φ z)
    (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs)

/-- The Laplace-weighted smoothed von Mangoldt band is absolutely integrable in the
half-plane of absolute convergence of the weighted prime-power series. -/
theorem integrable_smoothedVonMangoldtBand (φ : ℝ → ℂ) (z : ℂ)
    (hφ : Integrable (fun t : ℝ ↦ φ t * exp (z * t))) (hz : 1 / 2 < z.re) :
    Integrable (fun y : ℝ ↦ smoothedVonMangoldtBand φ y * exp (-z * (y : ℂ))) :=
  (integrable_and_bilateralLaplace_smoothedVonMangoldtBand φ z hφ hz).1

/-- The Laplace transform in the translation parameter is the product of the profile's
Mellin transform and the negative logarithmic derivative of the Riemann zeta function. -/
theorem bilateralLaplace_smoothedVonMangoldtBand (φ : ℝ → ℂ) (z : ℂ)
    (hφ : Integrable (fun t : ℝ ↦ φ t * exp (z * t))) (hz : 1 / 2 < z.re) :
    bilateralLaplace (smoothedVonMangoldtBand φ) (-z) =
      (-deriv riemannZeta (1 / 2 + z) / riemannZeta (1 / 2 + z)) * bilateralLaplace φ z :=
  (integrable_and_bilateralLaplace_smoothedVonMangoldtBand φ z hφ hz).2

private theorem bilateralLaplace_smoothedVonMangoldtBand_factored (φ : ℝ → ℂ)
    (z a : ℂ) (hφ : Integrable (fun t : ℝ ↦ φ t * exp (z * t))) (hz : 1 / 2 < z.re)
    (ha : bilateralLaplace φ z = (z - 1 / 2) * a) :
    bilateralLaplace (smoothedVonMangoldtBand φ) (-z) =
      a - (z - 1 / 2) * a * logDeriv (fun w ↦ riemannZeta₁ (1 / 2 + w)) z := by
  let s := 1 / 2 + z
  have hs : 1 < s.re := by
    change 1 < (1 / 2 + z).re
    rw [Complex.add_re]
    norm_num
    linarith
  have hs₁ : s ≠ 1 := fun h ↦ by rw [h] at hs; norm_num at hs
  have hk : s - 1 = z - 1 / 2 := by dsimp [s]; ring
  have h₁ : riemannZeta₁ s ≠ 0 := by
    intro hzero
    have hζ := riemannZeta_ne_zero_of_one_lt_re hs
    rw [riemannZeta_eq_inv_sub_mul hs₁, hzero, mul_zero] at hζ
    exact hζ rfl
  have hd : deriv (fun w ↦ riemannZeta₁ (1 / 2 + w)) z = deriv riemannZeta₁ s := by
    have hshift : HasDerivAt (fun w : ℂ ↦ 1 / 2 + w) 1 z := (hasDerivAt_id z).const_add _
    simpa only [s, Function.comp_def, mul_one] using
      ((differentiable_riemannZeta₁ s).hasDerivAt.comp z hshift).deriv
  rw [bilateralLaplace_smoothedVonMangoldtBand φ z hφ hz, ha, logDeriv_apply, hd]
  change (-deriv riemannZeta s / riemannZeta s) * ((z - 1 / 2) * a) =
    a - (z - 1 / 2) * a * (deriv riemannZeta₁ s / riemannZeta₁ s)
  rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs₁, riemannZeta_eq_inv_sub_mul hs₁, ← hk]
  field_simp [sub_ne_zero.mpr hs₁, h₁]
  ring

/-- A positive Laplace representation of the centered prime-band transform excludes
a zero detected by the Mellin factor. The term `E` permits analytic corrections to the
transform, such as those from a finite initial interval or an exponential majorant.
The pole at one is canceled by writing the Mellin factor as `(z - 1 / 2) * A z`. -/
private theorem riemannZeta_ne_zero_of_positivePrimeBandExpression {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → ℝ) (hT : Measurable T) (hT₀ : ∀ x, 0 ≤ T x)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hM : Integrable (fun y ↦ Real.exp (-b * T y)) μ)
    {A E : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A {w | a < w.re})
    (hE : AnalyticOnNhd ℂ E {w | a < w.re})
    (heq : EqOn
      (fun z ↦ A z - (z - 1 / 2) * A z * logDeriv (fun w ↦ riemannZeta₁ (1 / 2 + w)) z + E z)
      (fun z ↦ ∫ y, exp (-z * (T y : ℂ)) ∂μ) {w | b < w.re})
    {z : ℂ} (hz : a < z.re) (hz₁ : z ≠ 1 / 2) (hzA : A z ≠ 0) :
    riemannZeta (1 / 2 + z) ≠ 0 := by
  let Z (w : ℂ) := riemannZeta₁ (1 / 2 + w)
  let F (w : ℂ) := (w - 1 / 2) * A w
  let G (w : ℂ) := A w - F w * logDeriv Z w + E w
  have hZ (w : ℂ) : AnalyticAt ℂ Z w := by
    dsimp [Z]
    exact (differentiable_riemannZeta₁.analyticAt (1 / 2 + w)).comp (by fun_prop)
  have hF (w : ℂ) (hw : a < w.re) : AnalyticAt ℂ F w := by
    exact (show AnalyticAt ℂ (fun v : ℂ ↦ v - 1 / 2) w by fun_prop).mul (hA w hw)
  have hG : MeromorphicOn G {w | a < w.re} := fun w hw ↦
    (((hA w hw).meromorphicAt.sub ((hF w hw).meromorphicAt.mul (hZ w).meromorphicAt.logDeriv)).add
      (hE w hw).meromorphicAt)
  have hGR (x : ℝ) (hx : a < x) : AnalyticAt ℂ G (x : ℂ) := by
    let y := 1 / 2 + x
    have hy : 0 < y := by dsimp [y]; linarith
    have h₂ : (1 / 2 : ℂ) + (x : ℂ) = (y : ℂ) := by dsimp [y]; norm_num
    have hZ₀ : Z (x : ℂ) ≠ 0 := by
      change riemannZeta₁ (1 / 2 + (x : ℂ)) ≠ 0
      rw [h₂]
      rcases lt_trichotomy y 1 with hh | hh | hh
      · have hn : (y : ℂ) ≠ 1 := by exact_mod_cast hh.ne
        have hneg := riemannZeta_re_ofReal_neg hy hh
        rw [riemannZeta_eq_inv_sub_mul hn] at hneg
        intro hzero
        simp [hzero] at hneg
      · simp [hh]
      · have hn : (y : ℂ) ≠ 1 := by exact_mod_cast hh.ne'
        have hnonzero := riemannZeta_ne_zero_of_one_lt_re (s := (y : ℂ)) (by simpa using hh)
        rw [riemannZeta_eq_inv_sub_mul hn] at hnonzero
        exact right_ne_zero_of_mul hnonzero
    have hlog : AnalyticAt ℂ (logDeriv Z) (x : ℂ) :=
      (hZ _).deriv.div (hZ _) hZ₀
    exact ((hA _ hx).sub ((hF _ hx).mul hlog)).add (hE _ hx)
  have hGord := meromorphicOrderAt_nonneg_of_positive_laplace_continuation μ T hT hT₀
    hab hM hG hGR heq hz
  intro hzero
  have hs : 1 / 2 + z ≠ 1 := fun h ↦ hz₁ (by linear_combination h)
  have hZzero : Z z = 0 := by
    rw [riemannZeta_eq_inv_sub_mul hs, mul_eq_zero] at hzero
    exact hzero.resolve_left (inv_ne_zero (sub_ne_zero.mpr hs))
  have hZhalford : meromorphicOrderAt Z (1 / 2 : ℂ) = 0 := by
    apply (hZ _).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
    change riemannZeta₁ (1 / 2 + 1 / 2) ≠ 0
    rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, riemannZeta₁_one]
    exact one_ne_zero
  have hZm : MeromorphicOn Z univ := fun w _ ↦ (hZ w).meromorphicAt
  have hZfinite : meromorphicOrderAt Z z ≠ ⊤ :=
    hZm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ (1 / 2 : ℂ))
      (mem_univ z) (by rw [hZhalford]; simp)
  have hZpos : 0 < meromorphicOrderAt Z z := by
    apply (tendsto_zero_iff_meromorphicOrderAt_pos (hZ z).meromorphicAt).mp
    rw [← hZzero]
    exact (hZ z).continuousAt.continuousWithinAt
  have hN : meromorphicOrderAt (fun w ↦ -F w * logDeriv Z w) z = -1 := by
    change meromorphicOrderAt ((-F) * logDeriv Z) z = -1
    rw [meromorphicOrderAt_mul ((hF z hz).neg.meromorphicAt) (hZ z).meromorphicAt.logDeriv,
      (hF z hz).neg.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
        (neg_ne_zero.mpr (mul_ne_zero (sub_ne_zero.mpr hz₁) hzA)), zero_add,
      meromorphicOrderAt_logDeriv_eq_neg_one hZpos.ne' hZfinite]
  have hrest : AnalyticAt ℂ (A + E) z := (hA z hz).add (hE z hz)
  have hG' : G = (fun w ↦ -F w * logDeriv Z w) + (A + E) := by
    funext w
    dsimp [G]
    ring
  rw [hG', meromorphicOrderAt_add_eq_left_of_lt hrest.meromorphicAt
    (hN ▸ (show (-1 : WithTop ℤ) < 0 by decide).trans_le hrest.meromorphicOrderAt_nonneg), hN] at hGord
  exact (by decide : ¬ (0 : WithTop ℤ) ≤ -1) hGord

/-- An analytic, pole-canceled Mellin profile and a positive Laplace representation
of its prime-band observable exclude the detected zeros in the right half-plane.
An analytic correction `E` may include the transform of an exponential majorant
used to obtain the positive measure. -/
theorem riemannZeta_ne_zero_of_positivePrimeBandLaplace {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → ℝ) (hT : Measurable T) (hT₀ : ∀ x, 0 ≤ T x)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : 1 / 2 ≤ b)
    (hM : Integrable (fun y ↦ Real.exp (-b * T y)) μ)
    (φ : ℝ → ℂ) {A E : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A {w | a < w.re})
    (hE : AnalyticOnNhd ℂ E {w | a < w.re})
    (hφ : ∀ w : ℂ, b < w.re → Integrable (fun t : ℝ ↦ φ t * exp (w * t)))
    (hFactor : EqOn (bilateralLaplace φ) (fun w ↦ (w - 1 / 2) * A w) {w | b < w.re})
    (heq : EqOn (fun w ↦ bilateralLaplace (smoothedVonMangoldtBand φ) (-w) + E w)
      (fun w ↦ ∫ y, exp (-w * (T y : ℂ)) ∂μ) {w | b < w.re})
    {z : ℂ} (hz : a < z.re) (hz₁ : z ≠ 1 / 2) (hzA : A z ≠ 0) :
    riemannZeta (1 / 2 + z) ≠ 0 := by
  refine riemannZeta_ne_zero_of_positivePrimeBandExpression μ T hT hT₀ ha hab hM hA hE ?_
    hz hz₁ hzA
  intro w hw
  exact (congrArg (· + E w) (bilateralLaplace_smoothedVonMangoldtBand_factored φ w
    (A w) (hφ w hw) (hb.trans_lt hw) (hFactor hw)).symm).trans (heq hw)

/-- A one-sided exponential bound on a real smoothed prime-power sum rules out
the zeta zeros detected by its pole-canceled Mellin profile. The initial weighted
integrability and the profile factorization are exposed as separate hypotheses. -/
private theorem riemannZeta_ne_zero_of_smoothedVonMangoldtBand_lower_bound_aux
    (φ : ℝ → ℂ) {P : ℝ → ℝ} (hP : Measurable P)
    (hBand : ∀ y, smoothedVonMangoldtBand φ y = (P y : ℂ))
    (hZero : ∀ y ≤ 0, P y = 0) {a b C : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : 1 / 2 ≤ b)
    (hLower : ∀ y > 0, 0 ≤ P y + C * Real.exp (a * y))
    (hInt : IntegrableOn (fun y ↦ P y * Real.exp (-b * y)) (Ioi 0))
    {A : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A {w | a < w.re})
    (hφ : ∀ w : ℂ, b < w.re → Integrable (fun t : ℝ ↦ φ t * exp (w * t)))
    (hFactor : EqOn (bilateralLaplace φ) (fun w ↦ (w - 1 / 2) * A w) {w | b < w.re})
    {z : ℂ} (hz : a < z.re) (hz₁ : z ≠ 1 / 2) (hzA : A z ≠ 0) :
    riemannZeta (1 / 2 + z) ≠ 0 := by
  let d (y : ℝ) : ℝ≥0 := ⟨max 0 (P y + C * Real.exp (a * y)), le_max_left _ _⟩
  have hd : Measurable d := by
    apply Measurable.subtype_mk
    exact measurable_const.max (hP.add ((measurable_const.mul measurable_id).exp.const_mul C))
  let μ := (volume.restrict (Ioi (0 : ℝ))).withDensity (fun y ↦ (d y : ℝ≥0∞))
  let T (y : ℝ) := max 0 y
  have hT : Measurable T := measurable_const.max measurable_id
  have hd_eq {y : ℝ} (hy : 0 < y) : (d y : ℝ) = P y + C * Real.exp (a * y) :=
    max_eq_right (hLower y hy)
  have hT_eq {y : ℝ} (hy : 0 < y) : T y = y := max_eq_right hy.le
  have hM : Integrable (fun y ↦ Real.exp (-b * T y)) μ := by
    rw [integrable_withDensity_iff_integrable_coe_smul hd]
    have hAdd := hInt.add ((integrableOn_exp_mul_Ioi (sub_neg.mpr hab) 0).const_mul C)
    refine hAdd.congr ((ae_restrict_mem measurableSet_Ioi).mono fun y hy ↦ ?_)
    change P y * Real.exp (-b * y) + C * Real.exp ((a - b) * y) =
      (d y : ℝ) * Real.exp (-b * T y)
    rw [hd_eq hy, hT_eq hy, add_mul, mul_assoc, ← Real.exp_add]
    congr 3
    ring
  let E (w : ℂ) := (C : ℂ) / (w - a)
  have hE : AnalyticOnNhd ℂ E {w | a < w.re} := by
    intro w hw
    have hn : w - (a : ℂ) ≠ 0 := sub_ne_zero.mpr fun h ↦
      (ne_of_gt hw) (by simpa using congrArg Complex.re h)
    dsimp [E]
    exact analyticAt_const.div (by fun_prop) hn
  refine riemannZeta_ne_zero_of_positivePrimeBandLaplace μ T hT (fun _ ↦ le_max_left _ _)
    ha hab hb hM φ hA hE hφ hFactor ?_ hz hz₁ hzA
  intro w hw
  have hwb : b < w.re := hw
  have hPint : IntegrableOn (fun y : ℝ ↦ (P y : ℂ) * exp (-w * (y : ℂ))) (Ioi 0) := by
    have hm : Measurable (fun y : ℝ ↦ (P y : ℂ) * exp (-w * (y : ℂ))) :=
      hP.complex_ofReal.mul (Complex.continuous_exp.measurable.comp
        (Complex.continuous_ofReal.measurable.const_mul (-w)))
    refine hInt.norm.mono' hm.aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioi).mono fun y hy ↦ ?_)
    have hy₀ : 0 ≤ y := (show 0 < y from hy).le
    simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_exp, mul_re, neg_re,
      ofReal_re, ofReal_im, mul_zero, sub_zero, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hwb.le) hy₀)) (abs_nonneg _)
  have hwa : ((a : ℂ) - w).re < 0 := by
    rw [sub_re, ofReal_re]
    exact sub_neg.mpr (hab.trans hwb)
  have hEint := (integrableOn_exp_mul_complex_Ioi hwa 0).const_mul (C : ℂ)
  have hval : bilateralLaplace (smoothedVonMangoldtBand φ) (-w) =
      ∫ y : ℝ in Ioi 0, (P y : ℂ) * exp (-w * (y : ℂ)) := by
    rw [bilateralLaplace, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    by_cases hy : 0 < y
    · simp [hy, hBand]
    · simp [hy, hBand, hZero y (le_of_not_gt hy)]
  have hEval : E w = ∫ y : ℝ in Ioi 0, (C : ℂ) * exp (((a : ℂ) - w) * (y : ℂ)) := by
    change (C : ℂ) / (w - a) = _
    rw [integral_const_mul, integral_exp_mul_complex_Ioi hwa]
    simp only [ofReal_zero, mul_zero, exp_zero]
    rw [show (a : ℂ) - w = -(w - a) by ring]
    simp only [div_eq_mul_inv, inv_neg, neg_mul, one_mul, neg_neg]
  change bilateralLaplace (smoothedVonMangoldtBand φ) (-w) + E w =
    ∫ y, exp (-w * (T y : ℂ)) ∂μ
  rw [hval, hEval, ← integral_add hPint hEint, integral_withDensity_eq_integral_smul hd]
  refine integral_congr_ae ((ae_restrict_mem measurableSet_Ioi).mono fun y hy ↦ ?_)
  change (P y : ℂ) * exp (-w * (y : ℂ)) +
    (C : ℂ) * exp (((a : ℂ) - w) * (y : ℂ)) = (d y : ℝ) • exp (-w * (T y : ℂ))
  rw [real_smul, hd_eq hy, hT_eq hy, ofReal_add, ofReal_mul, ofReal_exp, add_mul, mul_assoc,
    ← exp_add]
  congr 3
  push_cast
  ring

/-- A one-sided exponential bound on a real smoothed von Mangoldt band rules out the
zeta zeros detected by its pole-canceled Mellin profile. Integrability of the weighted
profile on the initial half-plane gives the required weighted integrability of the band. -/
theorem riemannZeta_ne_zero_of_smoothedVonMangoldtBand_lower_bound
    (φ : ℝ → ℂ) {P : ℝ → ℝ} (hP : Measurable P)
    (hBand : ∀ y, smoothedVonMangoldtBand φ y = (P y : ℂ))
    (hZero : ∀ y ≤ 0, P y = 0) {a b C : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : 1 / 2 ≤ b)
    (hLower : ∀ y > 0, 0 ≤ P y + C * Real.exp (a * y))
    {A : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A {w | a < w.re})
    (hφ : ∀ w : ℂ, b < w.re → Integrable (fun t : ℝ ↦ φ t * exp (w * t)))
    (hFactor : EqOn (bilateralLaplace φ) (fun w ↦ (w - 1 / 2) * A w) {w | b < w.re})
    {z : ℂ} (hz : a < z.re) (hz₁ : z ≠ 1 / 2) (hzA : A z ≠ 0) :
    riemannZeta (1 / 2 + z) ≠ 0 := by
  let b' := b + 1
  have hbb' : b < b' := lt_add_one _
  have hInt : IntegrableOn (fun y ↦ P y * Real.exp (-b' * y)) (Ioi 0) := by
    have h := integrable_smoothedVonMangoldtBand φ (b' : ℂ)
      (hφ _ (by simpa only [ofReal_re] using hbb')) (by simpa only [ofReal_re] using hb.trans_lt hbb')
    simpa only [hBand, ← ofReal_neg, ← ofReal_mul, ← ofReal_exp, RCLike.re_eq_complex_re, ofReal_re]
      using h.re.integrableOn
  exact riemannZeta_ne_zero_of_smoothedVonMangoldtBand_lower_bound_aux φ hP hBand hZero ha
    (hab.trans hbb') (hb.trans hbb'.le) hLower hInt hA (fun w hw ↦ hφ w (hbb'.trans hw))
    (fun w hw ↦ hFactor (hbb'.trans hw)) hz hz₁ hzA

/-- The real prime-power criterion for a continuous profile vanishing outside
the open log interval between norms one and two. -/
theorem riemannZeta_ne_zero_of_real_compact_smoothedVonMangoldtBand_lower_bound
    (f : ℝ → ℝ) (hf : Continuous f)
    (hSupp : Function.support f ⊆ Ioo 0 (Real.log 2))
    {a C : ℝ} (ha : 0 ≤ a) (ha' : a < 1 / 2)
    (hLower : ∀ y > 0, 0 ≤ (smoothedVonMangoldtBand (fun t ↦ (f t : ℂ)) y).re +
      C * Real.exp (a * y))
    {A : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A {w | a < w.re})
    (hFactor : EqOn (bilateralLaplace (fun t ↦ (f t : ℂ)))
      (fun w ↦ (w - 1 / 2) * A w) {w | 1 / 2 < w.re})
    {z : ℂ} (hz : a < z.re) (hz₁ : z ≠ 1 / 2) (hzA : A z ≠ 0) :
    riemannZeta (1 / 2 + z) ≠ 0 := by
  let P (y : ℝ) : ℝ := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
    (n : ℝ) ^ (1 / 2 : ℝ) * f (Real.log n - y)
  have hP : Measurable P := Measurable.tsum fun n ↦
    measurable_const.mul (hf.measurable.comp (measurable_const.sub measurable_id))
  have hBand (y : ℝ) : smoothedVonMangoldtBand (fun t ↦ (f t : ℂ)) y = (P y : ℂ) := by
    unfold smoothedVonMangoldtBand P
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n ↦ ?_
    by_cases hn : n = 0
    · simp [hn]
    rw [LSeries.term_of_ne_zero hn, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
    norm_num
  have hZero (y : ℝ) (hy : y ≤ 0) : P y = 0 := by
    unfold P
    trans ∑' _ : ℕ, (0 : ℝ)
    · refine tsum_congr fun n ↦ ?_
      by_cases hn : n < 2
      · have h : n = 0 ∨ n = 1 := by omega
        rcases h with rfl | rfl <;> simp [ArithmeticFunction.vonMangoldt_apply_one]
      have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 2 ≤ n by omega)
      have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn'
      have h : f (Real.log n - y) = 0 := by
        by_contra hne
        have hlt := (hSupp (Function.mem_support.mpr hne)).2
        linarith
      simp [h]
    · simp
  have hφ (w : ℂ) : Integrable (fun t : ℝ ↦ (f t : ℂ) * exp (w * t)) := by
    apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    have hSub : Function.support (fun t : ℝ ↦ (f t : ℂ) * exp (w * t)) ⊆
        Icc 0 (Real.log 2) := by
      intro t ht
      have ht' : f t ≠ 0 := by
        intro he
        exact (Function.mem_support.mp ht) (by simp [he])
      have hi := hSupp (Function.mem_support.mpr ht')
      exact ⟨hi.1.le, hi.2.le⟩
    exact isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hSub isClosed_Icc)
  exact riemannZeta_ne_zero_of_smoothedVonMangoldtBand_lower_bound (fun t ↦ (f t : ℂ))
    hP hBand hZero ha ha' le_rfl
    (fun y hy ↦ by simpa only [hBand, Complex.ofReal_re] using hLower y hy)
    hA (fun w _ ↦ hφ w) hFactor hz hz₁ hzA

end RiemannMasullo.Isolated
