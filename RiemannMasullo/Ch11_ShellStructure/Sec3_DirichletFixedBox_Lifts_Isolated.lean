module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_DirichletFixedBox_Rows_Isolated
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Nontrivial primitive Dirichlet characters in fixed Fourier boxes (Lifts)

Annular logarithmic lifts, back-half shift operators, and Fourier multipliers for primitive `χ`.

Nothing outside the `Sec3_DirichletFixedBox*` / `Sec3_RatBridge*` isolated stack imports this module.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField RiemannMasullo Set Topology
open scoped BigOperators ContDiff FourierTransform NNReal Real SchwartzMap

namespace RiemannMasullo.Isolated

/-! ### Section 3: Exact same-box smooth cardinal lifts and exact denominator division -/

section CardinalLiftsAndDivision

open MeasureTheory Filter Topology Real
open scoped InnerProductSpace Convolution

theorem HasDirichletParity.fourierInv {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {f : 𝓢(ℝ, ℂ)} (hf : HasDirichletParity χ f) :
    HasDirichletParity χ (𝓕⁻ f) := by
  intro x
  rw [SchwartzMap.fourierInv_apply_eq]
  change (𝓕 f) (-(-x)) = χ (-1) * (𝓕 f) (-x)
  rw [neg_neg]
  have h1 : (𝓕 f) (-x) = χ (-1) * (𝓕 f) x := hf.fourier x
  calc (𝓕 f) x = 1 * (𝓕 f) x := (one_mul _).symm
    _ = (χ (-1) * χ (-1)) * (𝓕 f) x := by rw [dirichlet_eval_neg_one_sq χ]
    _ = χ (-1) * (χ (-1) * (𝓕 f) x) := mul_assoc _ _ _
    _ = χ (-1) * (𝓕 f) (-x) := by rw [h1]

theorem IsDirichletFixedBoxTest.zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (X : ℝ) : IsDirichletFixedBoxTest χ X 0 := by
  refine ⟨fun x ↦ by simp, ?_⟩
  have hz : (fun x : ℝ ↦ (𝓕 (0 : 𝓢(ℝ, ℂ))) x) = 0 := by
    ext x
    simp
  rw [hz, tsupport_zero]
  exact Set.empty_subset _

theorem IsDirichletFixedBoxTest.add {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {X : ℝ} {f g : 𝓢(ℝ, ℂ)} (hf : IsDirichletFixedBoxTest χ X f)
    (hg : IsDirichletFixedBoxTest χ X g) : IsDirichletFixedBoxTest χ X (f + g) := by
  simpa using hf.sub (hg.smul (-1))

/-- Parity-matched Fourier-side annular lift of a logarithmic bump `ψ` supported away from `0`. -/
def annularLogLiftFun {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (ψ : ℝ → ℂ) (u : ℝ) : ℂ :=
  if 0 < u then ((u : ℂ)⁻¹) * ψ (Real.log u)
  else if u < 0 then χ (-1) * (((-u : ℝ) : ℂ)⁻¹) * ψ (Real.log (-u))
  else 0

private theorem annularLogLiftFun_parity {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (ψ : ℝ → ℂ) (u : ℝ) :
    annularLogLiftFun χ ψ (-u) = χ (-1) * annularLogLiftFun χ ψ u := by
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · have hpos : 0 < -u := neg_pos.mpr hu
    have hnot : ¬ (0 < u) := not_lt_of_gt hu
    simp only [annularLogLiftFun, hpos, ↓reduceIte, hnot, hu]
    calc (((-u : ℝ) : ℂ)⁻¹) * ψ (Real.log (-u))
        = (χ (-1) * χ (-1)) * (((-u : ℝ) : ℂ)⁻¹) * ψ (Real.log (-u)) := by
            rw [dirichlet_eval_neg_one_sq χ, one_mul]
      _ = χ (-1) * (χ (-1) * (((-u : ℝ) : ℂ)⁻¹) * ψ (Real.log (-u))) := by ring
  · simp [annularLogLiftFun]
  · have hnot : ¬ (0 < -u) := not_lt.mpr (neg_nonpos.mpr hu.le)
    have hneg : -u < 0 := neg_lt_zero.mpr hu
    simp only [annularLogLiftFun, hnot, ↓reduceIte, hneg, hu, neg_neg]
    ring

private theorem annularLogLiftFun_eq_zero_of_lt {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ψ : ℝ → ℂ} {a b : ℝ}
    (hsupp : tsupport ψ ⊆ Set.Icc a b) {u : ℝ} (hu : |u| < Real.exp a) :
    annularLogLiftFun χ ψ u = 0 := by
  have hlog_lt : ∀ {v : ℝ}, 0 < v → v < Real.exp a → Real.log v < a := by
    intro v hv hlt
    rw [← Real.exp_log hv] at hlt
    exact Real.exp_lt_exp.mp hlt
  have hzero_of_lt : ∀ {y : ℝ}, y < a → ψ y = 0 := by
    intro y hy
    by_contra hne
    have hmem : y ∈ tsupport ψ := subset_closure hne
    linarith [(hsupp hmem).1]
  rcases lt_trichotomy u 0 with hu_neg | rfl | hu_pos
  · have hpos : 0 < -u := neg_pos.mpr hu_neg
    have hlt : -u < Real.exp a := by simpa [abs_of_neg hu_neg] using hu
    simp only [annularLogLiftFun, not_lt_of_gt hu_neg, ↓reduceIte, hu_neg]
    rw [hzero_of_lt (hlog_lt hpos hlt), mul_zero]
  · simp [annularLogLiftFun]
  · have hlt : u < Real.exp a := by simpa [abs_of_pos hu_pos] using hu
    simp only [annularLogLiftFun, hu_pos, ↓reduceIte]
    rw [hzero_of_lt (hlog_lt hu_pos hlt), mul_zero]

theorem annularLogLiftFun_tsupport_subset {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ψ : ℝ → ℂ} {a b R : ℝ} (hR : 0 < R)
    (hb : b ≤ Real.log R) (hsupp : tsupport ψ ⊆ Set.Icc a b) :
    tsupport (annularLogLiftFun χ ψ) ⊆ Set.Icc (-R) R := by
  refine closure_minimal ?_ isClosed_Icc
  intro u hu
  by_contra hnot
  apply hu
  have hR_le : Real.exp b ≤ R := (Real.exp_le_exp.mpr hb).trans_eq (Real.exp_log hR)
  have hlog_gt : ∀ {v : ℝ}, Real.exp b < v → b < Real.log v := by
    intro v hv
    have hv0 : 0 < v := lt_trans (Real.exp_pos b) hv
    rw [← Real.exp_log hv0] at hv
    exact Real.exp_lt_exp.mp hv
  have hzero_of_gt : ∀ {y : ℝ}, b < y → ψ y = 0 := by
    intro y hy
    by_contra hne
    have hmem : y ∈ tsupport ψ := subset_closure hne
    linarith [(hsupp hmem).2]
  have habs : R < |u| := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hnot
    rcases hnot with h1 | h2
    · have : -u > R := by linarith
      exact this.trans_le (neg_le_abs u)
    · exact h2.trans_le (le_abs_self u)
  rcases lt_trichotomy u 0 with hu_neg | rfl | hu_pos
  · have hpos : 0 < -u := neg_pos.mpr hu_neg
    have hlt : Real.exp b < -u := by
      calc Real.exp b ≤ R := hR_le
        _ < |u| := habs
        _ = -u := abs_of_neg hu_neg
    simp only [annularLogLiftFun, not_lt_of_gt hu_neg, ↓reduceIte, hu_neg]
    rw [hzero_of_gt (hlog_gt hlt), mul_zero]
  · have : (0 : ℝ) < 0 := hR.trans (by simpa using habs)
    exact False.elim (lt_irrefl _ this)
  · have hlt : Real.exp b < u := by
      calc Real.exp b ≤ R := hR_le
        _ < |u| := habs
        _ = u := abs_of_pos hu_pos
    simp only [annularLogLiftFun, hu_pos, ↓reduceIte]
    rw [hzero_of_gt (hlog_gt hlt), mul_zero]

theorem annularLogLiftFun_hasCompactSupport {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ψ : ℝ → ℂ} {a b R : ℝ} (hR : 0 < R)
    (hb : b ≤ Real.log R) (hsupp : tsupport ψ ⊆ Set.Icc a b) :
    HasCompactSupport (annularLogLiftFun χ ψ) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (subset_closure.trans (annularLogLiftFun_tsupport_subset χ hR hb hsupp))

theorem annularLogLiftFun_contDiff {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {ψ : ℝ → ℂ} {a b : ℝ}
    (hsmooth : ContDiff ℝ ∞ ψ) (hsupp : tsupport ψ ⊆ Set.Icc a b) :
    ContDiff ℝ ∞ (annularLogLiftFun χ ψ) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · have hev : annularLogLiftFun χ ψ =ᶠ[𝓝 u]
        fun x : ℝ ↦ χ (-1) * (((-x : ℝ) : ℂ)⁻¹) * ψ (Real.log (-x)) := by
      filter_upwards [isOpen_Iio.mem_nhds hu] with x hx
      have hx' : x < 0 := hx
      simp only [annularLogLiftFun, not_lt_of_gt hx', ↓reduceIte, hx']
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have hneg_pos : 0 < -u := neg_pos.mpr hu
    have hlog : ContDiffAt ℝ ∞ (fun x : ℝ ↦ ψ (Real.log (-x))) u :=
      (hsmooth.contDiffAt).comp u ((Real.contDiffAt_log.mpr hneg_pos.ne').comp u contDiff_neg.contDiffAt)
    have hinv : ContDiffAt ℝ ∞ (fun x : ℝ ↦ (((-x : ℝ) : ℂ)⁻¹)) u :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp _ contDiff_neg.contDiffAt).inv
        (Complex.ofReal_ne_zero.mpr hneg_pos.ne')
    exact (contDiffAt_const.mul hinv).mul hlog
  · have hev : annularLogLiftFun χ ψ =ᶠ[𝓝 0] fun _ : ℝ ↦ (0 : ℂ) := by
      have hopen : IsOpen (Set.Ioo (-Real.exp a) (Real.exp a)) := isOpen_Ioo
      have hmem : (0 : ℝ) ∈ Set.Ioo (-Real.exp a) (Real.exp a) := by
        have hpos : 0 < Real.exp a := Real.exp_pos a
        exact ⟨by linarith, hpos⟩
      filter_upwards [hopen.mem_nhds hmem] with x hx
      refine annularLogLiftFun_eq_zero_of_lt χ hsupp ?_
      exact abs_lt.mpr hx
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hev : annularLogLiftFun χ ψ =ᶠ[𝓝 u]
        fun x : ℝ ↦ ((x : ℂ)⁻¹) * ψ (Real.log x) := by
      filter_upwards [isOpen_Ioi.mem_nhds hu] with x hx
      have hx' : 0 < x := hx
      simp only [annularLogLiftFun, hx', ↓reduceIte]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have hlog : ContDiffAt ℝ ∞ (fun x : ℝ ↦ ψ (Real.log x)) u :=
      (hsmooth.contDiffAt).comp u (Real.contDiffAt_log.mpr hu.ne')
    have hinv : ContDiffAt ℝ ∞ (fun x : ℝ ↦ ((x : ℂ)⁻¹)) u :=
      Complex.ofRealCLM.contDiff.contDiffAt.inv (Complex.ofReal_ne_zero.mpr hu.ne')
    exact hinv.mul hlog

/-- Smooth compactly supported parity-matched Schwartz lift `f` whose Fourier transform equals
`annularLogLiftFun χ ψ`.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
def annularLogLift {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {ψ : ℝ → ℂ} {a b R : ℝ} (hR : 0 < R) (hb : b ≤ Real.log R)
    (hsmooth : ContDiff ℝ ∞ ψ) (hsupp : tsupport ψ ⊆ Set.Icc a b) : 𝓢(ℝ, ℂ) :=
  𝓕⁻ ((annularLogLiftFun_hasCompactSupport χ hR hb hsupp).toSchwartzMap
    (annularLogLiftFun_contDiff χ hsmooth hsupp))

theorem annularLogLift_isFixedBox {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {ψ : ℝ → ℂ} {a b R : ℝ} (hR : 0 < R) (hb : b ≤ Real.log R)
    (hsmooth : ContDiff ℝ ∞ ψ) (hsupp : tsupport ψ ⊆ Set.Icc a b) :
    IsDirichletFixedBoxTest χ R (annularLogLift χ hR hb hsmooth hsupp) := by
  let g : 𝓢(ℝ, ℂ) :=
    (annularLogLiftFun_hasCompactSupport χ hR hb hsupp).toSchwartzMap
      (annularLogLiftFun_contDiff χ hsmooth hsupp)
  have hg_par : HasDirichletParity χ g := fun u ↦ annularLogLiftFun_parity χ ψ u
  refine ⟨hg_par.fourierInv, ?_⟩
  have hF : (fun x : ℝ ↦ (𝓕 (annularLogLift χ hR hb hsmooth hsupp)) x) =
      annularLogLiftFun χ ψ := by
    ext x
    change (𝓕 (𝓕⁻ g)) x = annularLogLiftFun χ ψ x
    rw [FourierTransform.fourier_fourierInv_eq]
    rfl
  rw [hF]
  exact annularLogLiftFun_tsupport_subset χ hR hb hsupp

theorem annularLogLift_logFourier {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {ψ : ℝ → ℂ} {a b R : ℝ} (hR : 0 < R) (hb : b ≤ Real.log R)
    (hsmooth : ContDiff ℝ ∞ ψ) (hsupp : tsupport ψ ⊆ Set.Icc a b) (t : ℝ) :
    logFourierProfile (annularLogLift χ hR hb hsmooth hsupp) ((t : ℂ) * Complex.I) =
      ∫ y : ℝ, ψ y * Complex.exp (-(t : ℂ) * Complex.I * (y : ℂ)) := by
  let g : 𝓢(ℝ, ℂ) :=
    (annularLogLiftFun_hasCompactSupport χ hR hb hsupp).toSchwartzMap
      (annularLogLiftFun_contDiff χ hsmooth hsupp)
  rw [logFourierProfile]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  dsimp only
  have hFg : (𝓕 (annularLogLift χ hR hb hsmooth hsupp)) (Real.exp y) =
      annularLogLiftFun χ ψ (Real.exp y) := by
    change (𝓕 (𝓕⁻ g)) (Real.exp y) = annularLogLiftFun χ ψ (Real.exp y)
    rw [FourierTransform.fourier_fourierInv_eq]
    rfl
  rw [hFg]
  have hy_pos : 0 < Real.exp y := Real.exp_pos y
  simp only [annularLogLiftFun, hy_pos, ↓reduceIte, Real.log_exp]
  have hexp_inv : ((Real.exp y : ℝ) : ℂ)⁻¹ = Complex.exp (-(y : ℂ)) := by
    rw [Complex.ofReal_exp, Complex.exp_neg]
  rw [hexp_inv]
  calc Complex.exp (-(y : ℂ)) * ψ y * Complex.exp ((1 - (t : ℂ) * Complex.I) * (y : ℂ))
      = ψ y * (Complex.exp (-(y : ℂ)) * Complex.exp ((1 - (t : ℂ) * Complex.I) * (y : ℂ))) := by ring
    _ = ψ y * Complex.exp (-(t : ℂ) * Complex.I * (y : ℂ)) := by
        congr 1
        rw [← Complex.exp_add]
        congr 1
        ring

private theorem intervalSobolevDensity_shift_le (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (a y : ℝ) :
    intervalSobolevDensity (-α) α s (y + a) ≤
      Real.exp (2 * α * |a|) * (2 + 2 * a ^ 2) ^ (s / 2) * intervalSobolevDensity (-α) α s y := by
  unfold intervalSobolevDensity
  have hmax : max (Real.exp (2 * (-α) * (y + a))) (Real.exp (2 * α * (y + a))) ≤
      Real.exp (2 * α * |a|) * max (Real.exp (2 * (-α) * y)) (Real.exp (2 * α * y)) := by
    have h1 : Real.exp (2 * (-α) * (y + a)) ≤
        Real.exp (2 * α * |a|) * max (Real.exp (2 * (-α) * y)) (Real.exp (2 * α * y)) := by
      have ha : 2 * (-α) * a ≤ 2 * α * |a| := by
        have hle : -a ≤ |a| := neg_le_abs a
        nlinarith [mul_le_mul_of_nonneg_left hle hα]
      calc Real.exp (2 * (-α) * (y + a))
          ≤ Real.exp (2 * (-α) * y + 2 * α * |a|) := Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp (2 * α * |a|) * Real.exp (2 * (-α) * y) := by rw [Real.exp_add, mul_comm]
        _ ≤ Real.exp (2 * α * |a|) * max (Real.exp (2 * (-α) * y)) (Real.exp (2 * α * y)) := by
            gcongr; exact le_max_left _ _
    have h2 : Real.exp (2 * α * (y + a)) ≤
        Real.exp (2 * α * |a|) * max (Real.exp (2 * (-α) * y)) (Real.exp (2 * α * y)) := by
      have ha : 2 * α * a ≤ 2 * α * |a| := by
        have hle : a ≤ |a| := le_abs_self a
        nlinarith [mul_le_mul_of_nonneg_left hle hα]
      calc Real.exp (2 * α * (y + a))
          ≤ Real.exp (2 * α * y + 2 * α * |a|) := Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp (2 * α * |a|) * Real.exp (2 * α * y) := by rw [Real.exp_add, mul_comm]
        _ ≤ Real.exp (2 * α * |a|) * max (Real.exp (2 * (-α) * y)) (Real.exp (2 * α * y)) := by
            gcongr; exact le_max_right _ _
    exact max_le h1 h2
  have hpoly_base : 1 + (y + a) ^ 2 ≤ (2 + 2 * a ^ 2) * (1 + y ^ 2) := by
    nlinarith [sq_nonneg (y - a), sq_nonneg (y * a)]
  have hpoly : (1 + (y + a) ^ 2) ^ (s / 2) ≤ (2 + 2 * a ^ 2) ^ (s / 2) * (1 + y ^ 2) ^ (s / 2) := by
    have h1 : 0 ≤ 1 + (y + a) ^ 2 := by positivity
    have h2 : 0 ≤ 2 + 2 * a ^ 2 := by positivity
    have h3 : 0 ≤ 1 + y ^ 2 := by positivity
    rw [← Real.mul_rpow h2 h3]
    exact Real.rpow_le_rpow h1 hpoly_base (by positivity)
  have hre_nonneg : 0 ≤ max (Real.exp (2 * (-α) * y)) (Real.exp (2 * α * y)) := by positivity
  have hexp_nonneg : 0 ≤ Real.exp (2 * α * |a|) := (Real.exp_pos _).le
  have hpoly_nonneg : 0 ≤ (1 + (y + a) ^ 2) ^ (s / 2) := Real.rpow_nonneg (by positivity) (s / 2)
  calc max (Real.exp (2 * (-α) * (y + a))) (Real.exp (2 * α * (y + a))) * (1 + (y + a) ^ 2) ^ (s / 2)
      ≤ (Real.exp (2 * α * |a|) * max (Real.exp (2 * (-α) * y)) (Real.exp (2 * α * y))) *
          ((2 + 2 * a ^ 2) ^ (s / 2) * (1 + y ^ 2) ^ (s / 2)) :=
            mul_le_mul hmax hpoly hpoly_nonneg (mul_nonneg hexp_nonneg hre_nonneg)
    _ = Real.exp (2 * α * |a|) * (2 + 2 * a ^ 2) ^ (s / 2) *
          (max (Real.exp (2 * (-α) * y)) (Real.exp (2 * α * y)) * (1 + y ^ 2) ^ (s / 2)) := by ring

theorem halfShift_memLp_and_eLpNorm {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (a : ℝ)
    {U : ℝ → ℂ} (hU : MemLp U 2 (intervalSobolevMeasure volume id (-α) α s false)) :
    let V : ℝ → ℂ := fun x ↦ (Real.exp (a / 2) : ℂ) * U (x - a)
    MemLp V 2 (intervalSobolevMeasure volume id (-α) α s false) ∧
      eLpNorm V 2 (intervalSobolevMeasure volume id (-α) α s false) ≤
        ENNReal.ofReal (Real.exp (a / 2 + α * |a|) * (2 + 2 * a ^ 2) ^ (s / 4)) *
          eLpNorm U 2 (intervalSobolevMeasure volume id (-α) α s false) := by
  intro V
  let μ₀ := intervalSobolevMeasure volume id (-α) α s false
  have hρc := stripDensity_continuous (-α) α s
  have hρp := stripDensity_pos (-α) α s
  have hμ₀_def : intervalSobolevMeasure volume id (-α) α s false =
      volume.withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s x)) := by
    simp [intervalSobolevMeasure]
  have hqmp : QuasiMeasurePreserving (fun x : ℝ ↦ x - a) volume volume := by
    simpa [sub_eq_add_neg] using
      (measurePreserving_add_right (volume : Measure ℝ) (-a)).quasiMeasurePreserving
  have hU_vol : AEStronglyMeasurable U volume :=
    hU.aestronglyMeasurable.mono_ac <|
      withDensity_absolutelyContinuous' hρc.measurable.ennreal_ofReal.aemeasurable
        (Filter.Eventually.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hρp x)).ne')
  have hV_vol : AEStronglyMeasurable V volume :=
    aestronglyMeasurable_const.mul (hU_vol.comp_quasiMeasurePreserving hqmp)
  have hV_m : AEStronglyMeasurable V μ₀ :=
    hV_vol.mono_ac (withDensity_absolutelyContinuous _ _)
  let K : ℝ := Real.exp a * Real.exp (2 * α * |a|) * (2 + 2 * a ^ 2) ^ (s / 2)
  have hK_nn : 0 ≤ K := by positivity
  have hK_sqrt : Real.sqrt K = Real.exp (a / 2 + α * |a|) * (2 + 2 * a ^ 2) ^ (s / 4) := by
    have hsplit : K = (Real.exp (a / 2 + α * |a|) * (2 + 2 * a ^ 2) ^ (s / 4)) ^ 2 := by
      dsimp [K]
      rw [mul_pow, ← Real.exp_nat_mul, ← Real.rpow_natCast ((2 + 2 * a ^ 2) ^ (s / 4)) 2,
        ← Real.rpow_mul (by positivity)]
      congr 1
      · rw [← Real.exp_add]
        congr 1
        ring
      · congr 1
        ring
    rw [hsplit, Real.sqrt_sq (by positivity)]
  have hlint : ∫⁻ x : ℝ, ‖V x‖ₑ ^ (2 : ℕ) ∂μ₀ ≤
      ENNReal.ofReal K * ∫⁻ y : ℝ, ‖U y‖ₑ ^ (2 : ℕ) ∂μ₀ := by
    change ∫⁻ x : ℝ, ‖V x‖ₑ ^ (2 : ℕ) ∂(intervalSobolevMeasure volume id (-α) α s false) ≤
      ENNReal.ofReal K * ∫⁻ y : ℝ, ‖U y‖ₑ ^ (2 : ℕ) ∂(intervalSobolevMeasure volume id (-α) α s false)
    rw [hμ₀_def]
    have hlhs_eq : (∫⁻ x : ℝ, ‖V x‖ₑ ^ (2 : ℕ) ∂volume.withDensity
          (fun x ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s x))) =
        ∫⁻ x : ℝ, ENNReal.ofReal (intervalSobolevDensity (-α) α s x) * ‖V x‖ₑ ^ (2 : ℕ) ∂volume :=
      lintegral_withDensity_eq_lintegral_mul₀
        hρc.measurable.ennreal_ofReal.aemeasurable (hV_vol.eNorm.pow_const 2)
    have hrhs_eq : (∫⁻ y : ℝ, ‖U y‖ₑ ^ (2 : ℕ) ∂volume.withDensity
          (fun y ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s y))) =
        ∫⁻ y : ℝ, ENNReal.ofReal (intervalSobolevDensity (-α) α s y) * ‖U y‖ₑ ^ (2 : ℕ) ∂volume :=
      lintegral_withDensity_eq_lintegral_mul₀
        hρc.measurable.ennreal_ofReal.aemeasurable (hU_vol.eNorm.pow_const 2)
    rw [hlhs_eq, hrhs_eq]
    have hshift : (∫⁻ x : ℝ, ENNReal.ofReal (intervalSobolevDensity (-α) α s x) *
          ‖V x‖ₑ ^ (2 : ℕ) ∂volume) =
        ∫⁻ y : ℝ, ENNReal.ofReal (intervalSobolevDensity (-α) α s (y + a)) *
          ‖V (y + a)‖ₑ ^ (2 : ℕ) ∂volume :=
      (lintegral_add_right_eq_self
        (fun x : ℝ ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s x) * ‖V x‖ₑ ^ (2 : ℕ)) a).symm
    rw [hshift, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y ↦ ?_
    have hVya : ‖V (y + a)‖ₑ ^ (2 : ℕ) = ENNReal.ofReal (Real.exp a) * ‖U y‖ₑ ^ (2 : ℕ) := by
      dsimp [V]
      have hexp_e : ‖((Real.exp a : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (Real.exp a) := by
        rw [eNorm_eq_nnNorm, Complex.nnNorm_real, Real.nnNorm_of_nonneg (Real.exp_pos a).le,
          ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos a).le]
      rw [add_sub_cancel_right, eNorm_mul, mul_pow, ← eNorm_pow,
        show (Real.exp (a / 2) : ℂ) ^ 2 = ((Real.exp a : ℝ) : ℂ) by
          rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]; congr 2; ring,
        hexp_e]
    rw [hVya, ← mul_assoc, ← mul_assoc]
    have hle : ENNReal.ofReal (intervalSobolevDensity (-α) α s (y + a)) * ENNReal.ofReal (Real.exp a) ≤
        ENNReal.ofReal K * ENNReal.ofReal (intervalSobolevDensity (-α) α s y) := by
      have hden := intervalSobolevDensity_shift_le α s hα hs a y
      have hexp_nn : 0 ≤ Real.exp a := (Real.exp_pos a).le
      calc ENNReal.ofReal (intervalSobolevDensity (-α) α s (y + a)) * ENNReal.ofReal (Real.exp a)
          = ENNReal.ofReal (intervalSobolevDensity (-α) α s (y + a) * Real.exp a) :=
              (ENNReal.ofReal_mul (hρp _).le).symm
        _ ≤ ENNReal.ofReal ((Real.exp (2 * α * |a|) * (2 + 2 * a ^ 2) ^ (s / 2) *
              intervalSobolevDensity (-α) α s y) * Real.exp a) :=
              ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hden hexp_nn)
        _ = ENNReal.ofReal (K * intervalSobolevDensity (-α) α s y) := by
              congr 1; dsimp [K]; ring
        _ = ENNReal.ofReal K * ENNReal.ofReal (intervalSobolevDensity (-α) α s y) :=
              ENNReal.ofReal_mul hK_nn
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  have hU_lt : eLpNorm U 2 μ₀ < ⊤ := hU.eLpNorm_lt_top
  have h2_eq : ∀ f : ℝ → ℂ, AEStronglyMeasurable f μ₀ →
      eLpNorm f 2 μ₀ = (∫⁻ x : ℝ, ‖f x‖ₑ ^ (2 : ℕ) ∂μ₀) ^ (1 / 2 : ℝ) := by
    intro f hf
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hf]
    simp [ENNReal.toReal_ofNat]
  have heLp_le : eLpNorm V 2 μ₀ ≤ ENNReal.ofReal (Real.sqrt K) * eLpNorm U 2 μ₀ := by
    rw [h2_eq V hV_m, h2_eq U hU.aestronglyMeasurable]
    have hpow := ENNReal.rpow_le_rpow hlint (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hpow
    have hK_rpow : ENNReal.ofReal K ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt K) := by
      rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hK_nn (by norm_num)]
    rwa [hK_rpow] at hpow
  have hmemV : MemLp V 2 μ₀ :=
    lt_of_le_of_lt heLp_le (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hU_lt)
  refine ⟨hmemV, ?_⟩
  change eLpNorm V 2 μ₀ ≤ ENNReal.ofReal (Real.exp (a / 2 + α * |a|) * (2 + 2 * a ^ 2) ^ (s / 4)) * eLpNorm U 2 μ₀
  rwa [← hK_sqrt]

/-- Continuous linear half-shifted translation `U ↦ (x ↦ exp(a/2) U(x - a))` on
`CompactIntervalSobolev volume id (-α) α s`.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
def backHalfShiftCLM (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (a : ℝ) :
    CompactIntervalSobolev volume id (-α) α s →L[ℂ]
      CompactIntervalSobolev volume id (-α) α s :=
  let μ₀ := intervalSobolevMeasure volume id (-α) α s false
  let M : ℝ := Real.exp (a / 2 + α * |a|) * (2 + 2 * a ^ 2) ^ (s / 4)
  have hstep : ∀ f : CompactIntervalSobolev volume id (-α) α s,
      MemLp (fun x : ℝ ↦ (Real.exp (a / 2) : ℂ) * f (x - a)) 2 μ₀ ∧
        eLpNorm (fun x : ℝ ↦ (Real.exp (a / 2) : ℂ) * f (x - a)) 2 μ₀ ≤
          ENNReal.ofReal M * eLpNorm f 2 μ₀ :=
    fun f ↦ halfShift_memLp_and_eLpNorm hα hs a (Lp.memLp f)
  LinearMap.mkContinuous
    { toFun := fun f ↦ (hstep f).1.toLp _
      map_add' := fun f g ↦ by
        ext
        have hfg := Lp.coeFn_add f g
        have hρc := stripDensity_continuous (-α) α s
        have hρp := stripDensity_pos (-α) α s
        have hvol : (f + g : CompactIntervalSobolev volume id (-α) α s) =ᵐ[volume] ⇑f + ⇑g := by
          have hcoe := (ae_withDensity_iff hρc.measurable.ennreal_ofReal).mp hfg
          filter_upwards [hcoe] with y hy
          exact hy (ENNReal.ofReal_pos.mpr (hρp y)).ne'
        have hqmp : QuasiMeasurePreserving (fun x : ℝ ↦ x - a) volume volume := by
          simpa [sub_eq_add_neg] using
            (measurePreserving_add_right (volume : Measure ℝ) (-a)).quasiMeasurePreserving
        have hvol_shift : (fun x : ℝ ↦ (f + g) (x - a)) =ᵐ[volume]
            fun x : ℝ ↦ f (x - a) + g (x - a) := hqmp.ae hvol
        have h_ae : (fun x : ℝ ↦ (Real.exp (a / 2) : ℂ) * (f + g) (x - a)) =ᵐ[μ₀]
            (fun x : ℝ ↦ (Real.exp (a / 2) : ℂ) * f (x - a)) +
              (fun x : ℝ ↦ (Real.exp (a / 2) : ℂ) * g (x - a)) := by
          refine (withDensity_absolutelyContinuous _ _).ae_le ?_
          filter_upwards [hvol_shift] with y hy
          change (Real.exp (a / 2) : ℂ) * (f + g) (y - a) =
            (Real.exp (a / 2) : ℂ) * f (y - a) + (Real.exp (a / 2) : ℂ) * g (y - a)
          rw [hy, mul_add]
        have heq := (hstep (f + g)).1.coeFn_toLp.trans h_ae
        have heq2 : ((hstep f).1.toLp _ + (hstep g).1.toLp _ :
              CompactIntervalSobolev volume id (-α) α s) =ᵐ[μ₀]
            (fun x : ℝ ↦ (Real.exp (a / 2) : ℂ) * f (x - a)) +
              (fun x : ℝ ↦ (Real.exp (a / 2) : ℂ) * g (x - a)) := by
          filter_upwards [Lp.coeFn_add ((hstep f).1.toLp _) ((hstep g).1.toLp _),
            (hstep f).1.coeFn_toLp, (hstep g).1.coeFn_toLp] with y h1 h2 h3
          rw [h1, Pi.add_apply, h2, h3]
          rfl
        exact heq.trans heq2.symm
      map_smul' := fun c f ↦ by
        ext
        have hcf := Lp.coeFn_smul c f
        have hρc := stripDensity_continuous (-α) α s
        have hρp := stripDensity_pos (-α) α s
        have hvol : (c • f : CompactIntervalSobolev volume id (-α) α s) =ᵐ[volume] c • ⇑f := by
          have hcoe := (ae_withDensity_iff hρc.measurable.ennreal_ofReal).mp hcf
          filter_upwards [hcoe] with y hy
          exact hy (ENNReal.ofReal_pos.mpr (hρp y)).ne'
        have hqmp : QuasiMeasurePreserving (fun x : ℝ ↦ x - a) volume volume := by
          simpa [sub_eq_add_neg] using
            (measurePreserving_add_right (volume : Measure ℝ) (-a)).quasiMeasurePreserving
        have hvol_shift : (fun x : ℝ ↦ (c • f) (x - a)) =ᵐ[volume]
            fun x : ℝ ↦ c * f (x - a) := hqmp.ae hvol
        have h_ae : (fun x : ℝ ↦ (Real.exp (a / 2) : ℂ) * (c • f) (x - a)) =ᵐ[μ₀]
            c • (fun x : ℝ ↦ (Real.exp (a / 2) : ℂ) * f (x - a)) := by
          refine (withDensity_absolutelyContinuous _ _).ae_le ?_
          filter_upwards [hvol_shift] with y hy
          change (Real.exp (a / 2) : ℂ) * (c • f) (y - a) = c * ((Real.exp (a / 2) : ℂ) * f (y - a))
          rw [hy]; ring
        have heq := (hstep (c • f)).1.coeFn_toLp.trans h_ae
        have heq2 : (c • (hstep f).1.toLp _ : CompactIntervalSobolev volume id (-α) α s) =ᵐ[μ₀]
            c • (fun x : ℝ ↦ (Real.exp (a / 2) : ℂ) * f (x - a)) := by
          filter_upwards [Lp.coeFn_smul c ((hstep f).1.toLp _), (hstep f).1.coeFn_toLp] with y h1 h2
          rw [h1, Pi.smul_apply, h2]
          rfl
        exact heq.trans heq2.symm }
    M
    (fun f ↦ by
      change ‖(hstep f).1.toLp _‖ ≤ M * ‖f‖
      rw [Lp.norm_toLp, Lp.norm_def,
        ← ENNReal.toReal_ofReal (by positivity : 0 ≤ M),
        ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.memLp f).eLpNorm_lt_top).ne
        (hstep f).2)

theorem backHalfShiftCLM_apply_toDirichletStrip (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (a : ℝ)
    {U : ℝ → ℂ} (hU : MemLp U 2 (intervalSobolevMeasure volume id (-α) α s false))
    (hV : MemLp (fun x : ℝ ↦ (Real.exp (a / 2) : ℂ) * U (x - a)) 2
      (intervalSobolevMeasure volume id (-α) α s false)) :
    backHalfShiftCLM α s hα hs a (toDirichletStrip α s U hU) =
      toDirichletStrip α s (fun x : ℝ ↦ (Real.exp (a / 2) : ℂ) * U (x - a)) hV := by
  ext
  have hρc := stripDensity_continuous (-α) α s
  have hρp := stripDensity_pos (-α) α s
  have hU_vol : (toDirichletStrip α s U hU : ℝ → ℂ) =ᵐ[volume] U := by
    have hcoe := (ae_withDensity_iff hρc.measurable.ennreal_ofReal).mp hU.coeFn_toLp
    filter_upwards [hcoe] with y hy
    exact hy (ENNReal.ofReal_pos.mpr (hρp y)).ne'
  have hqmp : QuasiMeasurePreserving (fun x : ℝ ↦ x - a) volume volume := by
    simpa [sub_eq_add_neg] using
      (measurePreserving_add_right (volume : Measure ℝ) (-a)).quasiMeasurePreserving
  have hshift : (fun y : ℝ ↦ (Real.exp (a / 2) : ℂ) * (toDirichletStrip α s U hU) (y - a)) =ᵐ[volume]
      (fun y : ℝ ↦ (Real.exp (a / 2) : ℂ) * U (y - a)) := by
    filter_upwards [hqmp.ae hU_vol] with y hy
    rw [hy]
  have h_ae := (withDensity_absolutelyContinuous volume
    (fun x ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s x))).ae_le hshift
  have h1 := (halfShift_memLp_and_eLpNorm hα hs a (Lp.memLp (toDirichletStrip α s U hU))).1.coeFn_toLp
  filter_upwards [h1, h_ae, hV.coeFn_toLp] with y hy1 hy2 hy3
  exact (hy1.trans hy2).trans hy3.symm

theorem norm_backHalfShiftCLM_le (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (a : ℝ) :
    ‖backHalfShiftCLM α s hα hs a‖ ≤ Real.exp (a / 2 + α * |a|) * (2 + 2 * a ^ 2) ^ (s / 4) := by
  dsimp [backHalfShiftCLM]
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

theorem backHalfShiftCLM_zero (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    backHalfShiftCLM α s hα hs 0 = ContinuousLinearMap.id ℂ _ := by
  ext f
  have h1 := (halfShift_memLp_and_eLpNorm hα hs 0 (Lp.memLp f)).1.coeFn_toLp
  filter_upwards [h1] with y hy
  rw [show (backHalfShiftCLM α s hα hs 0 f : ℝ → ℂ) y = _ from hy]
  simp

theorem backHalfShiftCLM_add (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (a b : ℝ) :
    backHalfShiftCLM α s hα hs (a + b) =
      (backHalfShiftCLM α s hα hs a).comp (backHalfShiftCLM α s hα hs b) := by
  ext f
  let μ₀ := intervalSobolevMeasure volume id (-α) α s false
  have hρc := stripDensity_continuous (-α) α s
  have hρp := stripDensity_pos (-α) α s
  have hb_ae : (backHalfShiftCLM α s hα hs b f : ℝ → ℂ) =ᵐ[volume]
      fun y : ℝ ↦ (Real.exp (b / 2) : ℂ) * f (y - b) := by
    have hcoe := (ae_withDensity_iff hρc.measurable.ennreal_ofReal).mp
      (halfShift_memLp_and_eLpNorm hα hs b (Lp.memLp f)).1.coeFn_toLp
    filter_upwards [hcoe] with y hy
    exact hy (ENNReal.ofReal_pos.mpr (hρp y)).ne'
  have hqmp : QuasiMeasurePreserving (fun x : ℝ ↦ x - a) volume volume := by
    simpa [sub_eq_add_neg] using
      (measurePreserving_add_right (volume : Measure ℝ) (-a)).quasiMeasurePreserving
  have hcomp_ae : (fun y : ℝ ↦ (Real.exp (a / 2) : ℂ) * (backHalfShiftCLM α s hα hs b f) (y - a)) =ᵐ[μ₀]
      fun y : ℝ ↦ (Real.exp ((a + b) / 2) : ℂ) * f (y - (a + b)) := by
    refine (withDensity_absolutelyContinuous _ _).ae_le ?_
    filter_upwards [hqmp.ae hb_ae] with y hy
    rw [hy, sub_sub, add_comm a b, add_div, Real.exp_add, Complex.ofReal_mul]
    rw [mul_assoc, ← mul_assoc (Real.exp (b / 2) : ℂ), mul_comm (Real.exp (b / 2) : ℂ)]
    ring_nf
  have hl := (halfShift_memLp_and_eLpNorm hα hs (a + b) (Lp.memLp f)).1.coeFn_toLp
  have hr := (halfShift_memLp_and_eLpNorm hα hs a
    (Lp.memLp (backHalfShiftCLM α s hα hs b f))).1.coeFn_toLp
  filter_upwards [hl, hr, hcomp_ae] with y h1 h2 h3
  exact (h1.trans h3.symm).trans h2.symm

private theorem halfTwistLogDilate_eq_shift {q : ℕ} (hq : 0 < q) (U : ℝ → ℂ) (x : ℝ) :
    halfTwistLogDilate q U x =
      (Real.exp ((-Real.log q) / 2) : ℂ) * U (x - (-Real.log q)) := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [halfTwistLogDilate, hq.ne', ↓reduceIte, LinearMap.coe_mk, AddHom.coe_mk, sub_neg_eq_add]
  congr 1
  rw [← Complex.ofReal_natCast, show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow hqp.le, Real.rpow_def_of_pos hqp]
  congr 2
  ring

/-- Continuous linear depletion step `I - χ(q) S_{-log q}` on `CompactIntervalSobolev`. -/
def stripDepleteStep {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (q : ℕ) :
    CompactIntervalSobolev volume id (-α) α s →L[ℂ]
      CompactIntervalSobolev volume id (-α) α s :=
  if q = 0 then ContinuousLinearMap.id ℂ _
  else ContinuousLinearMap.id ℂ _ -
    χ (q : ZMod N) • backHalfShiftCLM α s hα hs (-Real.log q)

theorem stripDepleteStep_comm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (q r : ℕ) :
    Commute (stripDepleteStep χ α s hα hs q) (stripDepleteStep χ α s hα hs r) := by
  show (stripDepleteStep χ α s hα hs q).comp (stripDepleteStep χ α s hα hs r) =
    (stripDepleteStep χ α s hα hs r).comp (stripDepleteStep χ α s hα hs q)
  by_cases hq : q = 0 <;> by_cases hr : r = 0
  · simp [stripDepleteStep, hq, hr]
  · simp [stripDepleteStep, hq, hr]
  · simp [stripDepleteStep, hq, hr]
  · simp only [stripDepleteStep, eq_false hq, eq_false hr, ↓reduceIte]
    have hcomm : (backHalfShiftCLM α s hα hs (-Real.log q)).comp
          (backHalfShiftCLM α s hα hs (-Real.log r)) =
        (backHalfShiftCLM α s hα hs (-Real.log r)).comp
          (backHalfShiftCLM α s hα hs (-Real.log q)) := by
      rw [← backHalfShiftCLM_add, add_comm, backHalfShiftCLM_add]
    refine ContinuousLinearMap.ext fun f ↦ ?_
    simp only [ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.id_apply,
      smul_apply]
    have hcf : (backHalfShiftCLM α s hα hs (-Real.log q))
          ((backHalfShiftCLM α s hα hs (-Real.log r)) f) =
        (backHalfShiftCLM α s hα hs (-Real.log r))
          ((backHalfShiftCLM α s hα hs (-Real.log q)) f) :=
      DFunLike.congr_fun hcomm f
    simp only [map_sub, map_smul, smul_sub, smul_smul, hcf]
    module

/-- Stage depletion operator `∏_{q ∈ T} stripDepleteStep` on `CompactIntervalSobolev`. -/
def stripDirichletDeplete {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (T : Finset ℕ) (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    CompactIntervalSobolev volume id (-α) α s →L[ℂ]
      CompactIntervalSobolev volume id (-α) α s :=
  T.noncommProd (stripDepleteStep χ α s hα hs) fun q _ r _ _ ↦ stripDepleteStep_comm χ α s hα hs q r

@[simp]
theorem stripDirichletDeplete_empty {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    stripDirichletDeplete χ ∅ α s hα hs = ContinuousLinearMap.id ℂ _ :=
  Finset.noncommProd_empty _ _

theorem stripDirichletDeplete_insert {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) {q : ℕ} {T : Finset ℕ} (hq : q ∉ T) :
    stripDirichletDeplete χ (insert q T) α s hα hs =
      (stripDepleteStep χ α s hα hs q).comp (stripDirichletDeplete χ T α s hα hs) :=
  Finset.noncommProd_insert_of_notMem _ _ _ _ hq

private theorem dirichletDeplete_memLp_of_memLp {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : Finset ℕ) (hT : ∀ q ∈ T, 0 < q)
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) {U : ℝ → ℂ}
    (hU : MemLp U 2 (intervalSobolevMeasure volume id (-α) α s false)) :
    MemLp (dirichletDeplete χ T U) 2 (intervalSobolevMeasure volume id (-α) α s false) := by
  induction T using Finset.induction_on with
  | empty => simpa using hU
  | insert q S hqS ih =>
    have hq0 : 0 < q := hT q (Finset.mem_insert_self q S)
    have hS : MemLp (dirichletDeplete χ S U) 2 (intervalSobolevMeasure volume id (-α) α s false) :=
      ih fun r hr ↦ hT r (Finset.mem_insert_of_mem hr)
    rw [dirichletDeplete_insert χ hqS, LinearMap.comp_apply]
    change MemLp (depleteStepFun χ q (dirichletDeplete χ S U)) 2
      (intervalSobolevMeasure volume id (-α) α s false)
    have hfn : depleteStepFun χ q (dirichletDeplete χ S U) =
        fun x : ℝ ↦ dirichletDeplete χ S U x -
          χ (q : ZMod N) * ((Real.exp ((-Real.log q) / 2) : ℂ) *
            dirichletDeplete χ S U (x - (-Real.log q))) := by
      ext x
      simp only [depleteStepFun, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, halfTwistLogDilate_eq_shift hq0]
    rw [hfn]
    exact hS.sub ((halfShift_memLp_and_eLpNorm hα hs (-Real.log q) hS).1.const_mul _)

private theorem stripDirichletDeplete_apply {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : Finset ℕ) (hT : ∀ q ∈ T, 0 < q)
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) {U : ℝ → ℂ}
    (hU : MemLp U 2 (intervalSobolevMeasure volume id (-α) α s false))
    (hUT : MemLp (dirichletDeplete χ T U) 2 (intervalSobolevMeasure volume id (-α) α s false)) :
    stripDirichletDeplete χ T α s hα hs (toDirichletStrip α s U hU) =
      toDirichletStrip α s (dirichletDeplete χ T U) hUT := by
  revert hUT
  induction T using Finset.induction_on with
  | empty =>
    intro hUT
    ext
    rw [stripDirichletDeplete_empty, ContinuousLinearMap.id_apply]
    filter_upwards [hU.coeFn_toLp, hUT.coeFn_toLp] with y hy1 hy2
    simp only [dirichletDeplete_empty, LinearMap.id_apply] at hy2
    exact hy1.trans hy2.symm
  | insert q S hqS ih =>
    intro hUT
    have hq0 : 0 < q := hT q (Finset.mem_insert_self q S)
    have hS_all : ∀ r ∈ S, 0 < r := fun r hr ↦ hT r (Finset.mem_insert_of_mem hr)
    have hUS : MemLp (dirichletDeplete χ S U) 2 (intervalSobolevMeasure volume id (-α) α s false) :=
      dirichletDeplete_memLp_of_memLp χ S hS_all hα hs hU
    rw [stripDirichletDeplete_insert χ α s hα hs hqS, ContinuousLinearMap.comp_apply,
      ih hS_all hUS]
    have hfn : halfTwistLogDilate q (dirichletDeplete χ S U) =
        fun x ↦ (Real.exp ((-Real.log q) / 2) : ℂ) * dirichletDeplete χ S U (x - (-Real.log q)) :=
      funext (halfTwistLogDilate_eq_shift hq0 _)
    have hV : MemLp (fun x ↦ (Real.exp ((-Real.log q) / 2) : ℂ) *
        dirichletDeplete χ S U (x - (-Real.log q))) 2
        (intervalSobolevMeasure volume id (-α) α s false) :=
      (halfShift_memLp_and_eLpNorm hα hs (-Real.log q) hUS).1
    simp only [stripDepleteStep, eq_false hq0.ne', ↓reduceIte, sub_apply,
      ContinuousLinearMap.id_apply, smul_apply]
    rw [backHalfShiftCLM_apply_toDirichletStrip α s hα hs (-Real.log q) hUS hV]
    ext
    dsimp only [toDirichletStrip]
    have h1 := Lp.coeFn_sub (hUS.toLp _) (χ (q : ZMod N) • hV.toLp _)
    have h2 := Lp.coeFn_smul (χ (q : ZMod N)) (hV.toLp _)
    filter_upwards [h1, h2, hUS.coeFn_toLp, hV.coeFn_toLp, hUT.coeFn_toLp] with y hy1 hy2 hyS hyV hyT
    rw [hy1, Pi.sub_apply, hy2, Pi.smul_apply, smul_eq_mul, hyS, hyV, hyT,
      dirichletDeplete_insert χ hqS, LinearMap.comp_apply]
    simp only [depleteStepFun, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hfn]

private theorem norm_dirichletDeplete_strip_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : Finset ℕ) (hT : ∀ q ∈ T, 0 < q)
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) :
    ∃ C > (0 : ℝ), ∀ {U : ℝ → ℂ} (hU : MemLp U 2 (intervalSobolevMeasure volume id (-α) α s false))
      (hUT : MemLp (dirichletDeplete χ T U) 2 (intervalSobolevMeasure volume id (-α) α s false)),
      ‖toDirichletStrip α s (dirichletDeplete χ T U) hUT‖ ≤ C * ‖toDirichletStrip α s U hU‖ := by
  refine ⟨‖stripDirichletDeplete χ T α s hα hs‖ + 1, by positivity, fun hU hUT ↦ ?_⟩
  rw [← stripDirichletDeplete_apply χ T hT hα hs hU hUT]
  exact ((stripDirichletDeplete χ T α s hα hs).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _))

private noncomputable def logPullbackBump (β : ℝ → ℂ) (u : ℝ) : ℂ :=
  if 0 < u then β (Real.log u) else 0

private theorem logPullbackBump_eq_zero_of_notMem {β : ℝ → ℂ} {a b : ℝ}
    (hsupp : tsupport β ⊆ Set.Icc a b) {u : ℝ} (hu : u ∉ Set.Icc (Real.exp a) (Real.exp b)) :
    logPullbackBump β u = 0 := by
  have hzero_of_not : ∀ {y : ℝ}, y ∉ Set.Icc a b → β y = 0 := by
    intro y hy
    by_contra hne
    exact hy (hsupp (subset_closure hne))
  by_cases hpos : 0 < u
  · simp only [logPullbackBump, eq_true hpos, ↓reduceIte]
    refine hzero_of_not ?_
    intro hlog
    apply hu
    refine ⟨?_, ?_⟩
    · calc Real.exp a ≤ Real.exp (Real.log u) := Real.exp_le_exp.mpr hlog.1
        _ = u := Real.exp_log hpos
    · calc u = Real.exp (Real.log u) := (Real.exp_log hpos).symm
        _ ≤ Real.exp b := Real.exp_le_exp.mpr hlog.2
  · simp only [logPullbackBump, eq_false hpos, ↓reduceIte]

private theorem logPullbackBump_contDiff {β : ℝ → ℂ} {a b : ℝ}
    (hβ_smooth : ContDiff ℝ ∞ β) (hβ_supp : tsupport β ⊆ Set.Icc a b) :
    ContDiff ℝ ∞ (logPullbackBump β) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  rcases lt_or_ge 0 u with hu | hu
  · have hev : logPullbackBump β =ᶠ[𝓝 u] fun v : ℝ ↦ β (Real.log v) := by
      filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
      have hv' : 0 < v := hv
      simp only [logPullbackBump, hv', ↓reduceIte]
    exact ((hβ_smooth.contDiffAt).comp u (Real.contDiffAt_log.mpr hu.ne')).congr_of_eventuallyEq hev
  · have hev : logPullbackBump β =ᶠ[𝓝 u] fun _ : ℝ ↦ (0 : ℂ) := by
      have hopen : IsOpen (Set.Iio (Real.exp a)) := isOpen_Iio
      have hmem : u ∈ Set.Iio (Real.exp a) := lt_of_le_of_lt hu (Real.exp_pos a)
      filter_upwards [hopen.mem_nhds hmem] with v hv
      refine logPullbackBump_eq_zero_of_notMem hβ_supp ?_
      intro hmemIcc
      exact (not_le_of_gt hv) hmemIcc.1
    exact contDiffAt_const.congr_of_eventuallyEq hev

private theorem tsupport_iteratedDeriv_subset {f : ℝ → ℂ} (k : ℕ) :
    tsupport (iteratedDeriv k f) ⊆ tsupport f := by
  induction k generalizing f with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ']
    exact (ih).trans tsupport_deriv_subset

private theorem iteratedDeriv_cexp_mul_log_of_pos (z : ℂ) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv k (fun v : ℝ ↦ Complex.exp (z * (Real.log v : ℂ))) u =
      (∏ j ∈ Finset.range k, (z - (j : ℂ))) * Complex.exp ((z - (k : ℂ)) * (Real.log u : ℂ)) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have hev : deriv (fun v : ℝ ↦ Complex.exp (z * (Real.log v : ℂ))) =ᶠ[𝓝 u]
        fun v : ℝ ↦ z * Complex.exp ((z - 1) * (Real.log v : ℂ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
      have hv0 : (v : ℝ) ≠ 0 := (Set.mem_Ioi.mp hv).ne'
      have hlog : HasDerivAt (fun w : ℝ ↦ (Real.log w : ℂ)) ((v⁻¹ : ℝ) : ℂ) v :=
        (Real.hasDerivAt_log hv0).ofReal_comp
      have hexp : HasDerivAt (fun w : ℝ ↦ Complex.exp (z * (Real.log w : ℂ)))
          (Complex.exp (z * (Real.log v : ℂ)) * (z * ((v⁻¹ : ℝ) : ℂ))) v :=
        (hlog.const_mul z).cexp
      rw [hexp.deriv]
      have hv_exp : ((v⁻¹ : ℝ) : ℂ) = Complex.exp (-(Real.log v : ℂ)) := by
        rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log (Set.mem_Ioi.mp hv), Complex.ofReal_inv]
      rw [hv_exp]
      calc Complex.exp (z * (Real.log v : ℂ)) * (z * Complex.exp (-(Real.log v : ℂ)))
          = z * (Complex.exp (z * (Real.log v : ℂ)) * Complex.exp (-(Real.log v : ℂ))) := by ring
        _ = z * Complex.exp ((z - 1) * (Real.log v : ℂ)) := by
            congr 1; rw [← Complex.exp_add]; congr 1; ring
    rw [Filter.EventuallyEq.iteratedDeriv_eq k hev, iteratedDeriv_const_mul_field, ih (z - 1)]
    have hprod : z * ∏ j ∈ Finset.range k, ((z - 1) - (j : ℂ)) =
        ∏ j ∈ Finset.range (k + 1), (z - (j : ℂ)) := by
      rw [Finset.prod_range_succ']
      simp only [Nat.cast_zero, sub_zero, Nat.cast_add, Nat.cast_one, mul_comm z]
      congr 1
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      ring
    rw [← mul_assoc, hprod]
    congr 2
    push_cast
    ring

private theorem norm_iteratedDeriv_modulated_annularLogLiftFun_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {β : ℝ → ℂ} {a b : ℝ}
    (hβ_smooth : ContDiff ℝ ∞ β) (hβ_supp : tsupport β ⊆ Set.Icc a b) (n : ℕ) :
    ∃ C > (0 : ℝ), ∀ t : ℝ, ∀ u : ℝ,
      ‖iteratedDeriv n (annularLogLiftFun χ
        (fun y : ℝ ↦ Complex.exp ((t : ℂ) * Complex.I * (y : ℂ)) * β y)) u‖ ≤
        C * (1 + |t|) ^ n := by
  have hφ_smooth : ContDiff ℝ ∞ (logPullbackBump β) :=
    logPullbackBump_contDiff hβ_smooth hβ_supp
  let M : ℕ → ℝ := fun i ↦
    sSup ((fun u : ℝ ↦ ‖iteratedDeriv (n - i) (logPullbackBump β) u‖) ''
      Set.Icc (Real.exp a) (Real.exp b)) + 1
  have hM_bd : ∀ i ≤ n, ∀ u ∈ Set.Icc (Real.exp a) (Real.exp b),
      ‖iteratedDeriv (n - i) (logPullbackBump β) u‖ ≤ M i := by
    intro i _ u hu
    have hcont : Continuous (fun v : ℝ ↦ ‖iteratedDeriv (n - i) (logPullbackBump β) v‖) :=
      (hφ_smooth.continuous_iteratedDeriv (m := n - i) (by simp)).norm
    have hle : ‖iteratedDeriv (n - i) (logPullbackBump β) u‖ ≤
        sSup ((fun v : ℝ ↦ ‖iteratedDeriv (n - i) (logPullbackBump β) v‖) ''
          Set.Icc (Real.exp a) (Real.exp b)) :=
      le_csSup (isCompact_Icc.image hcont).bddAbove ⟨u, hu, rfl⟩
    linarith
  have hM_pos : ∀ i, 0 < M i := by
    intro i
    dsimp [M]
    have hnn : 0 ≤ sSup ((fun u : ℝ ↦ ‖iteratedDeriv (n - i) (logPullbackBump β) u‖) ''
        Set.Icc (Real.exp a) (Real.exp b)) := by
      apply Real.sSup_nonneg
      rintro _ ⟨v, _, rfl⟩
      exact norm_nonneg _
    linarith
  let A_pow : ℕ → ℝ := fun i ↦
    (∏ j ∈ Finset.range i, (1 + (j : ℝ))) * Real.exp ((-1 - (i : ℝ)) * a)
  let C : ℝ := ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A_pow i * M i
  have hC_pos : 0 < C := by
    refine Finset.sum_pos' (fun i _ ↦ ?_) ⟨0, Finset.mem_range.mpr (Nat.succ_pos n), ?_⟩
    · have h1 : 0 ≤ A_pow i := by dsimp [A_pow]; positivity
      have h2 : 0 ≤ M i := (hM_pos i).le
      positivity
    · simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, A_pow, Finset.range_zero,
        Finset.prod_empty, Nat.cast_zero, sub_zero]
      exact mul_pos (Real.exp_pos _) (hM_pos 0)
  refine ⟨C, hC_pos, fun t u ↦ ?_⟩
  let ψ_t : ℝ → ℂ := fun y ↦ Complex.exp ((t : ℂ) * Complex.I * (y : ℂ)) * β y
  have hψ_smooth : ContDiff ℝ ∞ ψ_t :=
    (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)).mul hβ_smooth
  have hψ_supp : tsupport ψ_t ⊆ Set.Icc a b :=
    tsupport_mul_subset_right.trans hβ_supp
  have hpos_bound : ∀ v : ℝ, 0 < v →
      ‖iteratedDeriv n (annularLogLiftFun χ ψ_t) v‖ ≤ C * (1 + |t|) ^ n := by
    intro v hv_pos
    by_cases hvIcc : v ∈ Set.Icc (Real.exp a) (Real.exp b)
    · let z : ℂ := (-1 : ℂ) + (t : ℂ) * Complex.I
      let fpow : ℝ → ℂ := fun w ↦ Complex.exp (z * (Real.log w : ℂ))
      have hfpow_smooth : ContDiffAt ℝ n fpow v := by
        have hlog : ContDiffAt ℝ n (fun w : ℝ ↦ (Real.log w : ℂ)) v :=
          Complex.ofRealCLM.contDiff.contDiffAt.comp v (Real.contDiffAt_log.mpr hv_pos.ne')
        exact Complex.contDiff_exp.contDiffAt.comp v (contDiffAt_const.mul hlog)
      have hev : annularLogLiftFun χ ψ_t =ᶠ[𝓝 v] fpow * logPullbackBump β := by
        filter_upwards [isOpen_Ioi.mem_nhds hv_pos] with w hw
        have hw' : 0 < w := hw
        simp only [annularLogLiftFun, hw', ↓reduceIte, Pi.mul_apply, fpow, logPullbackBump, ψ_t]
        have hwinv : ((w : ℂ)⁻¹) = Complex.exp (-(Real.log w : ℂ)) := by
          rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hw']
        rw [hwinv, mul_assoc, ← mul_assoc (Complex.exp (-(Real.log w : ℂ))), ← Complex.exp_add]
        congr 2
        dsimp [z]
        ring
      rw [Filter.EventuallyEq.iteratedDeriv_eq n hev,
        iteratedDeriv_mul hfpow_smooth (hφ_smooth.contDiffAt.of_le (by simp : ((n : ℕ) : ℕ∞ω) ≤ ∞))]
      refine (norm_sum_le _ _).trans ?_
      dsimp [C]
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi ↦ ?_
      have hi_le : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      have h1 : ‖iteratedDeriv i fpow v‖ ≤ A_pow i * (1 + |t|) ^ i := by
        dsimp [fpow]
        rw [iteratedDeriv_cexp_mul_log_of_pos z i hv_pos, norm_mul, norm_prod]
        have hprod_le : (∏ j ∈ Finset.range i, ‖z - (j : ℂ)‖) ≤
            (∏ j ∈ Finset.range i, (1 + (j : ℝ))) * (1 + |t|) ^ i := by
          have hprod_aux : ∀ k : ℕ, (∏ j ∈ Finset.range k, ‖z - (j : ℂ)‖) ≤
              (∏ j ∈ Finset.range k, (1 + (j : ℝ))) * (1 + |t|) ^ k := by
            intro k
            induction k with
            | zero => simp
            | succ m ihm =>
              rw [Finset.prod_range_succ, Finset.prod_range_succ, pow_succ]
              have htri : ‖z - (m : ℂ)‖ ≤ (1 + (m : ℝ)) + |t| := by
                have hdecomp : z - (m : ℂ) = (-((1 + (m : ℝ) : ℝ) : ℂ)) + (t : ℂ) * Complex.I := by
                  dsimp [z]; push_cast; ring
                rw [hdecomp]
                calc ‖(-((1 + (m : ℝ) : ℝ) : ℂ)) + (t : ℂ) * Complex.I‖
                    ≤ ‖(-((1 + (m : ℝ) : ℝ) : ℂ))‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
                  _ = (1 + (m : ℝ)) + |t| := by
                      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs,
                        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + (m : ℝ)),
                        norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
              have hstep : (1 + (m : ℝ)) + |t| ≤ (1 + (m : ℝ)) * (1 + |t|) := by
                have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
                nlinarith [abs_nonneg t]
              calc (∏ j ∈ Finset.range m, ‖z - (j : ℂ)‖) * ‖z - (m : ℂ)‖
                  ≤ ((∏ j ∈ Finset.range m, (1 + (j : ℝ))) * (1 + |t|) ^ m) *
                      ((1 + (m : ℝ)) * (1 + |t|)) :=
                    mul_le_mul ihm (htri.trans hstep) (norm_nonneg _) (by positivity)
                _ = (∏ j ∈ Finset.range m, (1 + (j : ℝ))) * (1 + (m : ℝ)) * ((1 + |t|) ^ m * (1 + |t|)) := by ring
          exact hprod_aux i
        have hexp_le : ‖Complex.exp ((z - (i : ℂ)) * (Real.log v : ℂ))‖ ≤
            Real.exp ((-1 - (i : ℝ)) * a) := by
          rw [Complex.norm_exp]
          apply Real.exp_le_exp.mpr
          have hre : ((z - (i : ℂ)) * (Real.log v : ℂ)).re = (-1 - (i : ℝ)) * Real.log v := by
            dsimp [z]
            simp [mul_re]
          rw [hre]
          have hlog_ge : a ≤ Real.log v := by
            rw [← Real.log_exp a]
            exact Real.log_le_log (Real.exp_pos a) hvIcc.1
          nlinarith [Nat.cast_nonneg (α := ℝ) i]
        calc (∏ j ∈ Finset.range i, ‖z - (j : ℂ)‖) *
              ‖Complex.exp ((z - (i : ℂ)) * (Real.log v : ℂ))‖
            ≤ ((∏ j ∈ Finset.range i, (1 + (j : ℝ))) * (1 + |t|) ^ i) *
                Real.exp ((-1 - (i : ℝ)) * a) := by gcongr
          _ = A_pow i * (1 + |t|) ^ i := by dsimp [A_pow]; ring
      have h2 : ‖iteratedDeriv (n - i) (logPullbackBump β) v‖ ≤ M i := hM_bd i hi_le v hvIcc
      have hpow_le : (1 + |t|) ^ i ≤ (1 + |t|) ^ n :=
        pow_le_pow_right₀ (by linarith [abs_nonneg t]) hi_le
      have hAnn : 0 ≤ A_pow i := by dsimp [A_pow]; positivity
      have hstep_le : (n.choose i : ℝ) * (A_pow i * (1 + |t|) ^ i) * M i ≤
          (n.choose i : ℝ) * (A_pow i * (1 + |t|) ^ n) * M i :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow_le hAnn) (Nat.cast_nonneg _))
          (hM_pos i).le
      calc (n.choose i : ℝ) * ‖iteratedDeriv i fpow v‖ *
            ‖iteratedDeriv (n - i) (logPullbackBump β) v‖
          ≤ (n.choose i : ℝ) * (A_pow i * (1 + |t|) ^ i) * M i := by gcongr
        _ ≤ (n.choose i : ℝ) * (A_pow i * (1 + |t|) ^ n) * M i := hstep_le
        _ = (n.choose i : ℝ) * A_pow i * M i * (1 + |t|) ^ n := by ring
    · have hv_lt_or_gt : v < Real.exp a ∨ Real.exp b < v := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hvIcc
        exact hvIcc
      have hev : annularLogLiftFun χ ψ_t =ᶠ[𝓝 v] fun _ : ℝ ↦ (0 : ℂ) := by
        rcases hv_lt_or_gt with hvlt | hvgt
        · filter_upwards [isOpen_Iio.mem_nhds hvlt, isOpen_Ioi.mem_nhds hv_pos] with w hwa hw0
          refine annularLogLiftFun_eq_zero_of_lt χ hψ_supp ?_
          rw [abs_of_pos hw0]
          exact hwa
        · filter_upwards [isOpen_Ioi.mem_nhds hvgt] with w hwb
          have hw_not : w ∉ Set.Icc (-Real.exp b) (Real.exp b) := by
            intro hm
            exact (not_le_of_gt hwb) hm.2
          have hsub := annularLogLiftFun_tsupport_subset χ (Real.exp_pos b) (by simp) hψ_supp
          by_contra hne
          exact hw_not (hsub (subset_closure hne))
      rw [Filter.EventuallyEq.iteratedDeriv_eq n hev, iteratedDeriv_const]
      split_ifs <;> simp only [norm_zero]
      · exact mul_nonneg hC_pos.le (by positivity)
      · exact mul_nonneg hC_pos.le (by positivity)
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · have hpar_fn : annularLogLiftFun χ ψ_t = fun w : ℝ ↦ χ (-1) * annularLogLiftFun χ ψ_t (-w) := by
      ext w
      have hp := annularLogLiftFun_parity χ ψ_t (-w)
      rw [neg_neg] at hp
      exact hp
    rw [hpar_fn, iteratedDeriv_const_mul_field, iteratedDeriv_comp_neg]
    simp only [norm_mul, norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc ‖χ (-1)‖ * ‖iteratedDeriv n (annularLogLiftFun χ ψ_t) (-u)‖
        ≤ 1 * (C * (1 + |t|) ^ n) :=
          mul_le_mul (norm_dirichletChar_le_one χ (-1)) (hpos_bound (-u) (neg_pos.mpr hu))
            (norm_nonneg _) zero_le_one
      _ = C * (1 + |t|) ^ n := one_mul _
  · have hev : annularLogLiftFun χ ψ_t =ᶠ[𝓝 0] fun _ : ℝ ↦ (0 : ℂ) := by
      have hopen : IsOpen (Set.Ioo (-Real.exp a) (Real.exp a)) := isOpen_Ioo
      have hmem : (0 : ℝ) ∈ Set.Ioo (-Real.exp a) (Real.exp a) :=
        ⟨by linarith [Real.exp_pos a], Real.exp_pos a⟩
      filter_upwards [hopen.mem_nhds hmem] with w hw
      exact annularLogLiftFun_eq_zero_of_lt χ hψ_supp (abs_lt.mpr hw)
    rw [Filter.EventuallyEq.iteratedDeriv_eq n hev, iteratedDeriv_const]
    split_ifs <;> simp only [norm_zero] <;> exact mul_nonneg hC_pos.le (by positivity)
  · exact hpos_bound u hu

theorem annularLogLift_deplete_norm_poly_bound {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    {β : ℝ → ℂ} {a b R : ℝ} (hR : 0 < R) (hb : b ≤ Real.log R)
    (hRX : R ≤ X / ∏ q ∈ T, (q : ℝ))
    (hβ_smooth : ContDiff ℝ ∞ β) (hβ_supp : tsupport β ⊆ Set.Icc a b) :
    let hTpos : ∀ q ∈ T, 0 < q := fun q hq ↦ (hT q hq).1.pos
    ∃ K : ℕ, ∃ C > (0 : ℝ), ∀ t : ℝ,
      let ψ_t : ℝ → ℂ := fun y ↦ Complex.exp ((t : ℂ) * Complex.I * (y : ℂ)) * β y
      let hψ_smooth : ContDiff ℝ ∞ ψ_t :=
        (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)).mul hβ_smooth
      let hψ_supp : tsupport ψ_t ⊆ Set.Icc a b := tsupport_mul_subset_right.trans hβ_supp
      let f_t : 𝓢(ℝ, ℂ) := annularLogLift χ hR hb hψ_smooth hψ_supp
      let hf_box : IsDirichletFixedBoxTest χ (X / ∏ q ∈ T, (q : ℝ)) f_t :=
        (annularLogLift_isFixedBox χ hR hb hψ_smooth hψ_supp).mono hRX
      let hmem : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f_t)) 2
          (intervalSobolevMeasure volume id (-α) α s false) :=
        dirichletDeplete_memLp hχ hN T hTpos
          (div_pos hX (Finset.prod_pos fun q hq ↦ by exact_mod_cast (hT q hq).1.pos)) hα hs hf_box
      ‖toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f_t)) hmem‖ ≤
        C * (1 + |t|) ^ K := by
  intro hTpos
  let n : ℕ := Nat.ceil α + Nat.ceil s + 4
  have hn_ge2 : 2 ≤ n := by dsimp [n]; omega
  obtain ⟨C0, hC0_pos, hbd0⟩ := norm_iteratedDeriv_modulated_annularLogLiftFun_le χ hβ_smooth hβ_supp 0
  obtain ⟨Cn, hCn_pos, hbdn⟩ := norm_iteratedDeriv_modulated_annularLogLiftFun_le χ hβ_smooth hβ_supp n
  let D : ℝ := (2 * R) * C0 + ((2 * Real.pi) ^ n)⁻¹ * ((2 * R) * Cn)
  have hD_pos : 0 < D := by positivity
  have hf_decay : ∀ t : ℝ, ∀ u : ℝ,
      let ψ_t : ℝ → ℂ := fun y ↦ Complex.exp ((t : ℂ) * Complex.I * (y : ℂ)) * β y
      let hψ_smooth : ContDiff ℝ ∞ ψ_t :=
        (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)).mul hβ_smooth
      let hψ_supp : tsupport ψ_t ⊆ Set.Icc a b := tsupport_mul_subset_right.trans hβ_supp
      let f_t : 𝓢(ℝ, ℂ) := annularLogLift χ hR hb hψ_smooth hψ_supp
      (1 + |u| ^ n) * ‖f_t u‖ ≤ D * (1 + |t|) ^ n := by
    intro t u ψ_t hψ_smooth hψ_supp f_t
    let G_t := annularLogLiftFun χ ψ_t
    have hGsmooth : ContDiff ℝ ∞ G_t := annularLogLiftFun_contDiff χ hψ_smooth hψ_supp
    have hGsupp : HasCompactSupport G_t := annularLogLiftFun_hasCompactSupport χ hR hb hψ_supp
    have hGtsupp : tsupport G_t ⊆ Set.Icc (-R) R :=
      annularLogLiftFun_tsupport_subset χ hR hb hψ_supp
    let g_t : 𝓢(ℝ, ℂ) := hGsupp.toSchwartzMap hGsmooth
    have hf_eq : f_t u = (𝓕 (G_t : ℝ → ℂ)) (-u) := by
      change (𝓕⁻ g_t) u = (𝓕 (G_t : ℝ → ℂ)) (-u)
      rw [SchwartzMap.fourierInv_apply_eq]
      change (𝓕 g_t) (-u) = (𝓕 (G_t : ℝ → ℂ)) (-u)
      rw [SchwartzMap.fourier_coe]
      rfl
    have hHint : ∀ k ≤ n, Integrable (iteratedDeriv k G_t) volume := by
      intro k _
      have hck : Continuous (iteratedDeriv k G_t) :=
        hGsmooth.continuous_iteratedDeriv (m := k) (by simp)
      have hsuppk : HasCompactSupport (iteratedDeriv k G_t) :=
        hGsupp.of_isClosed_subset isClosed_closure (tsupport_iteratedDeriv_subset k)
      exact hck.integrable_of_hasCompactSupport hsuppk
    have hfour := Real.one_add_pow_mul_norm_fourier_le (hGsmooth.of_le (by simp)) hHint (-u)
    rw [abs_neg, ← hf_eq] at hfour
    have hint_k : ∀ k : ℕ, k ≤ n → ∀ Ck > (0 : ℝ),
        (∀ w : ℝ, ‖iteratedDeriv k G_t w‖ ≤ Ck * (1 + |t|) ^ k) →
        ∫ w : ℝ, ‖iteratedDeriv k G_t w‖ ≤ (2 * R) * Ck * (1 + |t|) ^ k := by
      intro k hk Ck _ hk_bd
      have hzero_out : ∀ w ∉ Set.Icc (-R) R, ‖iteratedDeriv k G_t w‖ = 0 := by
        intro w hw
        rw [norm_eq_zero]
        by_contra hne
        have hmem : w ∈ tsupport (iteratedDeriv k G_t) := subset_closure hne
        exact hw (hGtsupp (tsupport_iteratedDeriv_subset k hmem))
      have hle_ind : ∀ w : ℝ, ‖iteratedDeriv k G_t w‖ ≤
          Set.indicator (Set.Icc (-R) R) (fun _ ↦ Ck * (1 + |t|) ^ k) w := by
        intro w
        by_cases hw : w ∈ Set.Icc (-R) R
        · rw [Set.indicator_of_mem hw]
          exact hk_bd w
        · rw [hzero_out w hw, Set.indicator_of_notMem hw]
      have hint_lhs : Integrable (fun w : ℝ ↦ ‖iteratedDeriv k G_t w‖) volume :=
        (hHint k hk).norm
      have hint_rhs : Integrable (Set.indicator (Set.Icc (-R) R) (fun _ ↦ Ck * (1 + |t|) ^ k)) volume :=
        IntegrableOn.integrable_indicator
          (continuousOn_const.integrableOn_Icc) measurableSet_Icc
      refine (integral_mono hint_lhs hint_rhs hle_ind).trans_eq ?_
      rw [integral_indicator measurableSet_Icc, MeasureTheory.setIntegral_const,
        Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
      ring
    have hi0 := hint_k 0 (Nat.zero_le n) C0 hC0_pos (fun w ↦ by simpa using hbd0 t w)
    have hin := hint_k n le_rfl Cn hCn_pos (hbdn t)
    have hi0' : ∫ w : ℝ, ‖G_t w‖ ≤ (2 * R) * C0 * (1 + |t|) ^ n := by
      have h1 : (2 * R) * C0 * (1 + |t|) ^ 0 = (2 * R) * C0 := by simp
      have h2 : (1 : ℝ) ≤ (1 + |t|) ^ n := one_le_pow₀ (by linarith [abs_nonneg t])
      have hnn : 0 ≤ (2 * R) * C0 := by positivity
      calc ∫ w : ℝ, ‖G_t w‖ ≤ (2 * R) * C0 * (1 + |t|) ^ 0 := hi0
        _ = (2 * R) * C0 * 1 := by rw [h1, mul_one]
        _ ≤ (2 * R) * C0 * (1 + |t|) ^ n := mul_le_mul_of_nonneg_left h2 hnn
    calc (1 + |u| ^ n) * ‖f_t u‖
        ≤ (∫ w, ‖G_t w‖) + ((2 * Real.pi) ^ n)⁻¹ * ∫ w, ‖iteratedDeriv n G_t w‖ := hfour
      _ ≤ (2 * R) * C0 * (1 + |t|) ^ n + ((2 * Real.pi) ^ n)⁻¹ * ((2 * R) * Cn * (1 + |t|) ^ n) := by
          gcongr
      _ = D * (1 + |t|) ^ n := by dsimp [D]; ring
  have hsum_int : Summable (fun m : ℤ ↦ if m = 0 then (0 : ℝ) else |(m : ℝ)| ^ (-2 : ℝ)) := by
    refine (Real.summable_abs_int_rpow one_lt_two).congr_cofinite ?_
    refine Filter.mem_cofinite.mpr ((Set.finite_singleton (0 : ℤ)).subset fun m hm ↦ ?_)
    by_contra hm0
    have hm0' : m ≠ 0 := by simpa using hm0
    have heq0 : (if m = 0 then (0 : ℝ) else |(m : ℝ)| ^ (-2 : ℝ)) = |(m : ℝ)| ^ (-2 : ℝ) :=
      ite_eq_right_iff.mpr fun h ↦ (hm0' h).elim
    exact absurd heq0.symm hm
  let S2 : ℝ := ∑' m : ℤ, if m = 0 then (0 : ℝ) else |(m : ℝ)| ^ (-2 : ℝ)
  have hS2_nn : 0 ≤ S2 := tsum_nonneg fun m ↦ by split_ifs <;> positivity
  let B : ℝ := -Real.log ((N : ℝ) * (X / ∏ q ∈ T, (q : ℝ)))
  let ρ := intervalSobolevDensity (-α) α s
  have hρc := stripDensity_continuous (-α) α s
  have hρp := stripDensity_pos (-α) α s
  have hρ_int : Integrable (fun x : ℝ ↦ Set.indicator (Set.Ici B)
      (fun x : ℝ ↦ Real.exp ((1 - 2 * (n : ℝ)) * x) * ρ x) x) volume := by
    have hcont_f : Continuous (fun x : ℝ ↦ Real.exp ((1 - 2 * (n : ℝ)) * x) * ρ x) :=
      (Real.continuous_exp.comp (by fun_prop)).mul hρc
    have hIccB : IntegrableOn (fun x : ℝ ↦ Real.exp ((1 - 2 * (n : ℝ)) * x) * ρ x) (Set.Icc B 0) volume :=
      hcont_f.continuousOn.integrableOn_Icc
    have hIci0 : IntegrableOn (fun x : ℝ ↦ Real.exp ((1 - 2 * (n : ℝ)) * x) * ρ x) (Set.Ici 0) volume := by
      let k : ℕ := Nat.ceil s
      have hsn : s / 2 ≤ (k : ℝ) := by linarith [Nat.le_ceil s]
      let K0 : ℝ := (2 : ℝ) ^ k * (1 + ((2 * k).factorial : ℝ))
      have hdom : IntegrableOn (fun x : ℝ ↦ K0 * Real.exp (-x)) (Set.Ici 0) volume :=
        ((integrableOn_Ici_iff_integrableOn_Ioi (f := fun x : ℝ ↦ Real.exp (-x))).mpr
          (integrableOn_exp_neg_Ioi 0)).const_mul K0
      refine hdom.mono' hcont_f.aestronglyMeasurable ?_
      refine ae_restrict_of_forall_mem measurableSet_Ici fun x hx0 ↦ ?_
      have hx_nn : 0 ≤ x := hx0
      rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (hρp x).le)]
      have hmax_pos : max (Real.exp (2 * (-α) * x)) (Real.exp (2 * α * x)) = Real.exp (2 * α * x) := by
        apply max_eq_right
        apply Real.exp_le_exp.mpr
        nlinarith
      have h1x : (1 : ℝ) ≤ 1 + x ^ 2 := by linarith [sq_nonneg x]
      have hpow_k : (1 + x ^ 2) ^ (s / 2) ≤ (2 : ℝ) ^ k * (1 + x ^ (2 * k)) := by
        calc (1 + x ^ 2) ^ (s / 2) ≤ (1 + x ^ 2) ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le h1x hsn
          _ = (1 + x ^ 2) ^ k := Real.rpow_natCast _ _
          _ ≤ (2 * max 1 (x ^ 2)) ^ k := by
              gcongr; linarith [le_max_left 1 (x ^ 2), le_max_right 1 (x ^ 2)]
          _ = (2 : ℝ) ^ k * (max 1 (x ^ 2)) ^ k := mul_pow _ _ _
          _ ≤ (2 : ℝ) ^ k * (1 + x ^ (2 * k)) := by
              gcongr
              rw [pow_mul]
              rcases le_total 1 (x ^ 2) with hmax | hmax
              · rw [max_eq_right hmax]; linarith
              · rw [max_eq_left hmax, one_pow]; linarith [pow_nonneg (sq_nonneg x) k]
      have hfact : 1 + x ^ (2 * k) ≤ (1 + ((2 * k).factorial : ℝ)) * Real.exp x := by
        have hkpos : (0 : ℝ) < ((2 * k).factorial : ℝ) := by positivity
        have h := Real.pow_div_factorial_le_exp x hx_nn (2 * k)
        have hpow_le : x ^ (2 * k) ≤ ((2 * k).factorial : ℝ) * Real.exp x :=
          ((div_le_iff₀ hkpos).mp h).trans_eq (mul_comm _ _)
        nlinarith [Real.exp_pos x, one_le_exp hx_nn]
      have hexp_decay : Real.exp ((1 - 2 * (n : ℝ)) * x) * Real.exp (2 * α * x) * Real.exp x ≤
          Real.exp (-x) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hα_ceil : α ≤ (Nat.ceil α : ℝ) := Nat.le_ceil α
        have hn_ge : α + 4 ≤ (n : ℝ) := by
          have : (Nat.ceil α : ℝ) + 4 ≤ (n : ℝ) := by exact_mod_cast (by dsimp [n]; omega : Nat.ceil α + 4 ≤ n)
          linarith
        have hcoef : (1 - 2 * (n : ℝ)) + 2 * α + 1 ≤ -1 := by linarith
        calc (1 - 2 * (n : ℝ)) * x + 2 * α * x + x
            = ((1 - 2 * (n : ℝ)) + 2 * α + 1) * x := by ring
          _ ≤ (-1) * x := mul_le_mul_of_nonneg_right hcoef hx_nn
          _ = -x := by ring
      calc Real.exp ((1 - 2 * (n : ℝ)) * x) * ρ x
          = Real.exp ((1 - 2 * (n : ℝ)) * x) *
              (Real.exp (2 * α * x) * (1 + x ^ 2) ^ (s / 2)) := by
                dsimp [ρ, intervalSobolevDensity]; rw [hmax_pos]
        _ ≤ Real.exp ((1 - 2 * (n : ℝ)) * x) *
              (Real.exp (2 * α * x) * ((2 : ℝ) ^ k * ((1 + ((2 * k).factorial : ℝ)) * Real.exp x))) := by
                gcongr
                exact hpow_k.trans (mul_le_mul_of_nonneg_left hfact (by positivity))
        _ = K0 * (Real.exp ((1 - 2 * (n : ℝ)) * x) * Real.exp (2 * α * x) * Real.exp x) := by
                dsimp [K0]; ring
        _ ≤ K0 * Real.exp (-x) := by gcongr
    have hsub : Set.Ici B ⊆ Set.Icc B 0 ∪ Set.Ici 0 := by
      intro x hxB
      rcases le_total x 0 with hx0 | hx0
      · exact Or.inl ⟨hxB, hx0⟩
      · exact Or.inr hx0
    exact IntegrableOn.integrable_indicator ((hIccB.union hIci0).mono_set hsub) measurableSet_Ici
  let I₀ : ℝ := ∫ x : ℝ, Set.indicator (Set.Ici B)
    (fun x : ℝ ↦ Real.exp ((1 - 2 * (n : ℝ)) * x) * ρ x) x
  have hI₀_nn : 0 ≤ I₀ := integral_nonneg fun x ↦ by
    by_cases hx : B ≤ x
    · rw [Set.indicator_of_mem hx]; exact mul_nonneg (Real.exp_pos _).le (hρp x).le
    · rw [Set.indicator_of_notMem hx]
      exact le_rfl
  obtain ⟨CT, hCT_pos, hCT⟩ := norm_dirichletDeplete_strip_le χ T hTpos hα hs
  let C_U : ℝ := D * S2 * Real.sqrt I₀ + 1
  have hCU_pos : 0 < C_U := by positivity
  refine ⟨n, CT * C_U, mul_pos hCT_pos hCU_pos, fun t ↦ ?_⟩
  intro ψ_t hψ_smooth hψ_supp f_t hf_box hmem
  have hprod_pos : 0 < ∏ q ∈ T, (q : ℝ) :=
    Finset.prod_pos fun q hq ↦ by exact_mod_cast (hT q hq).1.pos
  have hX' : 0 < X / ∏ q ∈ T, (q : ℝ) := div_pos hX hprod_pos
  have hU₀_mem : MemLp (twistedHalfLogProfile χ f_t) 2
      (intervalSobolevMeasure volume id (-α) α s false) :=
    twistedHalfLogProfile_memLp hχ hN hX' hα hs hf_box
  have hdep_le := hCT hU₀_mem hmem
  have hU₀_norm_le : ‖toDirichletStrip α s (twistedHalfLogProfile χ f_t) hU₀_mem‖ ≤
      C_U * (1 + |t|) ^ n := by
    let U₀ := twistedHalfLogProfile χ f_t
    have hU₀_vol : (toDirichletStrip α s U₀ hU₀_mem : ℝ → ℂ) =ᵐ[volume] U₀ := by
      have hcoe := (ae_withDensity_iff hρc.measurable.ennreal_ofReal).mp hU₀_mem.coeFn_toLp
      filter_upwards [hcoe] with y hy
      exact hy (ENNReal.ofReal_pos.mpr (hρp y)).ne'
    have hμ₀_def : intervalSobolevMeasure volume id (-α) α s false =
        volume.withDensity (fun x ↦ ENNReal.ofReal (ρ x)) := rfl
    have hnorm_sq : ‖toDirichletStrip α s U₀ hU₀_mem‖ ^ 2 = ∫ x : ℝ, ‖U₀ x‖ ^ 2 * ρ x := by
      have hid : ‖toDirichletStrip α s U₀ hU₀_mem‖ ^ 2 =
          (⟪toDirichletStrip α s U₀ hU₀_mem, toDirichletStrip α s U₀ hU₀_mem⟫_ℂ).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) (toDirichletStrip α s U₀ hU₀_mem)).symm
      have hinner_eq : ⟪toDirichletStrip α s U₀ hU₀_mem, toDirichletStrip α s U₀ hU₀_mem⟫_ℂ =
          ∫ x : ℝ, (toDirichletStrip α s U₀ hU₀_mem : ℝ → ℂ) x *
            starRingEnd ℂ ((toDirichletStrip α s U₀ hU₀_mem : ℝ → ℂ) x) ∂
              (volume.withDensity (fun x ↦ ENNReal.ofReal (ρ x))) :=
        L2.inner_def _ _
      rw [hinner_eq] at hid
      have hint_eq : (∫ x : ℝ, (toDirichletStrip α s U₀ hU₀_mem : ℝ → ℂ) x *
            starRingEnd ℂ ((toDirichletStrip α s U₀ hU₀_mem : ℝ → ℂ) x) ∂
              (volume.withDensity (fun x ↦ ENNReal.ofReal (ρ x)))).re =
          ∫ x : ℝ, ‖U₀ x‖ ^ 2 * ρ x := by
        rw [integral_withDensity_eq_integral_toReal_smul₀
          hρc.measurable.ennreal_ofReal.aemeasurable
          (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
        change Complex.reCLM (∫ x : ℝ, (ENNReal.ofReal (ρ x)).toReal •
            ((toDirichletStrip α s U₀ hU₀_mem : ℝ → ℂ) x *
              starRingEnd ℂ ((toDirichletStrip α s U₀ hU₀_mem : ℝ → ℂ) x))) = _
        have hmem_w : MemLp (toDirichletStrip α s U₀ hU₀_mem : ℝ → ℂ) 2
            (volume.withDensity (fun x ↦ ENNReal.ofReal (ρ x))) :=
          Lp.memLp (toDirichletStrip α s U₀ hU₀_mem)
        have hsq_int : Integrable (fun x : ℝ ↦ ((‖(toDirichletStrip α s U₀ hU₀_mem : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ))
            (volume.withDensity (fun x ↦ ENNReal.ofReal (ρ x))) :=
          Complex.ofRealCLM.integrable_comp
            ((memLp_two_iff_integrable_sq_norm hmem_w.aestronglyMeasurable).mp hmem_w)
        have hint_int : Integrable (fun x : ℝ ↦ (toDirichletStrip α s U₀ hU₀_mem : ℝ → ℂ) x *
            starRingEnd ℂ ((toDirichletStrip α s U₀ hU₀_mem : ℝ → ℂ) x))
            (volume.withDensity (fun x ↦ ENNReal.ofReal (ρ x))) := by
          refine hsq_int.congr (Filter.Eventually.of_forall fun x ↦ ?_)
          dsimp only
          symm
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
        have hint_w : Integrable (fun x : ℝ ↦ (ENNReal.ofReal (ρ x)).toReal •
            ((toDirichletStrip α s U₀ hU₀_mem : ℝ → ℂ) x *
              starRingEnd ℂ ((toDirichletStrip α s U₀ hU₀_mem : ℝ → ℂ) x))) volume :=
          (integrable_withDensity_iff_integrable_smul' hρc.measurable.ennreal_ofReal
            (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mp hint_int
        rw [← Complex.reCLM.integral_comp_comm hint_w]
        refine integral_congr_ae ?_
        filter_upwards [hU₀_vol] with x hx
        have hmul : ((toDirichletStrip α s U₀ hU₀_mem : ℝ → ℂ) x) *
              starRingEnd ℂ ((toDirichletStrip α s U₀ hU₀_mem : ℝ → ℂ) x) =
            ((‖U₀ x‖ ^ 2 : ℝ) : ℂ) := by
          rw [hx, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
        rw [Complex.reCLM_apply, Complex.real_smul, ENNReal.toReal_ofReal (hρp x).le,
          hmul, Complex.mul_re]
        simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        ring
      exact hid.trans hint_eq
    have hpt_le : ∀ x : ℝ, ‖U₀ x‖ ^ 2 * ρ x ≤
        (D * S2) ^ 2 * (1 + |t|) ^ (2 * n) *
          Set.indicator (Set.Ici B) (fun x : ℝ ↦ Real.exp ((1 - 2 * (n : ℝ)) * x) * ρ x) x := by
      intro x
      by_cases hx : x < B
      · have hz : U₀ x = 0 := dirichletFixedBox_support_lower_bound hχ hN hX' hf_box hx
        rw [hz, norm_zero, sq, zero_mul, zero_mul]
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith [abs_nonneg t]) _))
          (Set.indicator_nonneg (fun y _ ↦ mul_nonneg (Real.exp_pos _).le (hρp y).le) x)
      · have hxB : B ≤ x := le_of_not_gt hx
        rw [Set.indicator_of_mem hxB]
        have hU_le : ‖U₀ x‖ ≤ D * S2 * (1 + |t|) ^ n * Real.exp ((1 / 2 - (n : ℝ)) * x) := by
          have hsum_terms := summable_twistedRadialTheta χ f_t (Real.exp_pos x).ne'
          have hchi0 : χ ((0 : ℤ) : ZMod N) = 0 := by
            rw [Int.cast_zero, ← inv_inv χ]
            exact dirichletChar_inv_zero_of_one_lt χ⁻¹ hN
          have hterm_le : ∀ m : ℤ, ‖χ (m : ZMod N) * f_t (m * Real.exp x)‖ ≤
              D * (1 + |t|) ^ n * Real.exp (-(n : ℝ) * x) *
                (if m = 0 then (0 : ℝ) else |(m : ℝ)| ^ (-2 : ℝ)) := by
            intro m
            by_cases hm : m = 0
            · subst hm
              rw [Int.cast_zero, show χ 0 = 0 from by simpa using hchi0]
              simp
            · simp only [eq_false hm, ↓reduceIte]
              rw [norm_mul]
              have hm_ge : (1 : ℝ) ≤ |(m : ℝ)| := by
                have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
                exact_mod_cast this
              have hdec := hf_decay t (m * Real.exp x)
              have hden_ge : |(m : ℝ)| ^ 2 * Real.exp ((n : ℝ) * x) ≤
                  1 + |(m : ℝ) * Real.exp x| ^ n := by
                rw [abs_mul, abs_of_pos (Real.exp_pos x), mul_pow, ← Real.exp_nat_mul]
                have hmpow : |(m : ℝ)| ^ 2 ≤ |(m : ℝ)| ^ n :=
                  pow_le_pow_right₀ hm_ge hn_ge2
                have hexp_nn : 0 ≤ Real.exp ((n : ℝ) * x) := (Real.exp_pos _).le
                nlinarith
              have hpos_den : 0 < |(m : ℝ)| ^ 2 * Real.exp ((n : ℝ) * x) := by positivity
              have hf_le : ‖f_t (m * Real.exp x)‖ ≤
                  D * (1 + |t|) ^ n * Real.exp (-(n : ℝ) * x) * |(m : ℝ)| ^ (-2 : ℝ) := by
                have h1 : ‖f_t (m * Real.exp x)‖ * (|(m : ℝ)| ^ 2 * Real.exp ((n : ℝ) * x)) ≤
                    D * (1 + |t|) ^ n := by
                  rw [mul_comm]
                  exact (mul_le_mul_of_nonneg_right hden_ge (norm_nonneg _)).trans hdec
                have h2 : ‖f_t (m * Real.exp x)‖ ≤
                    D * (1 + |t|) ^ n / (|(m : ℝ)| ^ 2 * Real.exp ((n : ℝ) * x)) :=
                  (le_div_iff₀ hpos_den).mpr h1
                have hrpow_inv : (|(m : ℝ)| ^ 2)⁻¹ = |(m : ℝ)| ^ (-2 : ℝ) := by
                  rw [Real.rpow_neg (abs_nonneg _)]
                  norm_cast
                have hpow2_ne : |(m : ℝ)| ^ 2 ≠ 0 :=
                  pow_ne_zero 2 (abs_ne_zero.mpr (Int.cast_ne_zero.mpr hm))
                calc ‖f_t (m * Real.exp x)‖
                    ≤ D * (1 + |t|) ^ n / (|(m : ℝ)| ^ 2 * Real.exp ((n : ℝ) * x)) := h2
                  _ = D * (1 + |t|) ^ n * (Real.exp ((n : ℝ) * x))⁻¹ * (|(m : ℝ)| ^ 2)⁻¹ := by
                      field_simp [(Real.exp_pos _).ne', hpow2_ne]
                  _ = D * (1 + |t|) ^ n * Real.exp (-(n : ℝ) * x) * |(m : ℝ)| ^ (-2 : ℝ) := by
                      rw [← Real.exp_neg, neg_mul, hrpow_inv]
              calc ‖χ (m : ZMod N)‖ * ‖f_t (m * Real.exp x)‖
                  ≤ 1 * (D * (1 + |t|) ^ n * Real.exp (-(n : ℝ) * x) * |(m : ℝ)| ^ (-2 : ℝ)) :=
                    mul_le_mul (norm_dirichletChar_le_one χ m) hf_le (norm_nonneg _) zero_le_one
                _ = D * (1 + |t|) ^ n * Real.exp (-(n : ℝ) * x) * |(m : ℝ)| ^ (-2 : ℝ) := one_mul _
          have htsum := (norm_tsum_le_tsum_norm hsum_terms.norm).trans
            (hsum_terms.norm.tsum_le_tsum hterm_le (hsum_int.mul_left _))
          rw [tsum_mul_left] at htsum
          change ‖(Real.exp (x / 2) : ℂ) * twistedRadialTheta χ f_t (Real.exp x)‖ ≤ _
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
          calc Real.exp (x / 2) * ‖twistedRadialTheta χ f_t (Real.exp x)‖
              ≤ Real.exp (x / 2) * (D * (1 + |t|) ^ n * Real.exp (-(n : ℝ) * x) * S2) :=
                mul_le_mul_of_nonneg_left htsum (Real.exp_pos _).le
            _ = D * S2 * (1 + |t|) ^ n * (Real.exp (x / 2) * Real.exp (-(n : ℝ) * x)) := by ring
            _ = D * S2 * (1 + |t|) ^ n * Real.exp ((1 / 2 - (n : ℝ)) * x) := by
                congr 1; rw [← Real.exp_add]; congr 1; ring
        have hsq : ‖U₀ x‖ ^ 2 ≤ (D * S2) ^ 2 * (1 + |t|) ^ (2 * n) *
            Real.exp ((1 - 2 * (n : ℝ)) * x) := by
          have h1 : ‖U₀ x‖ ^ 2 ≤ (D * S2 * (1 + |t|) ^ n * Real.exp ((1 / 2 - (n : ℝ)) * x)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hU_le 2
          calc ‖U₀ x‖ ^ 2 ≤ (D * S2) ^ 2 * ((1 + |t|) ^ n) ^ 2 * (Real.exp ((1 / 2 - (n : ℝ)) * x)) ^ 2 := by
                simpa [mul_pow] using h1
            _ = (D * S2) ^ 2 * (1 + |t|) ^ (2 * n) * Real.exp ((1 - 2 * (n : ℝ)) * x) := by
                rw [← pow_mul, mul_comm n 2, ← Real.exp_nat_mul]
                congr 1; congr 1; ring
        calc ‖U₀ x‖ ^ 2 * ρ x
            ≤ ((D * S2) ^ 2 * (1 + |t|) ^ (2 * n) * Real.exp ((1 - 2 * (n : ℝ)) * x)) * ρ x := by
              gcongr; exact (hρp x).le
          _ = (D * S2) ^ 2 * (1 + |t|) ^ (2 * n) * (Real.exp ((1 - 2 * (n : ℝ)) * x) * ρ x) := by ring
    have hint_lhs : Integrable (fun x : ℝ ↦ ‖U₀ x‖ ^ 2 * ρ x) volume := by
      have hsq_mem := (memLp_two_iff_integrable_sq_norm hU₀_mem.aestronglyMeasurable).mp hU₀_mem
      have h_w := (integrable_withDensity_iff hρc.measurable.ennreal_ofReal
        (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mp hsq_mem
      refine h_w.congr (Filter.Eventually.of_forall fun x ↦ ?_)
      dsimp only
      rw [ENNReal.toReal_ofReal (hρp x).le]
    have hint_rhs : Integrable (fun x : ℝ ↦ (D * S2) ^ 2 * (1 + |t|) ^ (2 * n) *
        Set.indicator (Set.Ici B) (fun x : ℝ ↦ Real.exp ((1 - 2 * (n : ℝ)) * x) * ρ x) x) volume :=
      hρ_int.const_mul _
    have hnorm_sq_le : ‖toDirichletStrip α s U₀ hU₀_mem‖ ^ 2 ≤
        (D * S2 * Real.sqrt I₀ * (1 + |t|) ^ n) ^ 2 := by
      calc ‖toDirichletStrip α s U₀ hU₀_mem‖ ^ 2
          = ∫ x : ℝ, ‖U₀ x‖ ^ 2 * ρ x := hnorm_sq
        _ ≤ ∫ x : ℝ, (D * S2) ^ 2 * (1 + |t|) ^ (2 * n) *
              Set.indicator (Set.Ici B) (fun x : ℝ ↦ Real.exp ((1 - 2 * (n : ℝ)) * x) * ρ x) x :=
              integral_mono hint_lhs hint_rhs hpt_le
        _ = (D * S2) ^ 2 * (1 + |t|) ^ (2 * n) * I₀ := integral_const_mul _ _
        _ = (D * S2 * Real.sqrt I₀ * (1 + |t|) ^ n) ^ 2 := by
            rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hI₀_nn, ← pow_mul, mul_comm n 2]
            ring
    have hsqrt_le : ‖toDirichletStrip α s U₀ hU₀_mem‖ ≤
        D * S2 * Real.sqrt I₀ * (1 + |t|) ^ n := by
      have hrt := Real.sqrt_le_sqrt hnorm_sq_le
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at hrt
    have h_add : D * S2 * Real.sqrt I₀ * (1 + |t|) ^ n ≤ C_U * (1 + |t|) ^ n := by
      dsimp [C_U]
      have : 1 ≤ (1 + |t|) ^ n := one_le_pow₀ (by linarith [abs_nonneg t])
      nlinarith [mul_nonneg (mul_nonneg hD_pos.le hS2_nn) (Real.sqrt_nonneg I₀)]
    exact hsqrt_le.trans h_add
  calc ‖toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f_t)) hmem‖
      ≤ CT * ‖toDirichletStrip α s (twistedHalfLogProfile χ f_t) hU₀_mem‖ := hdep_le
    _ ≤ CT * (C_U * (1 + |t|) ^ n) := by gcongr
    _ = (CT * C_U) * (1 + |t|) ^ n := by ring


end CardinalLiftsAndDivision

end RiemannMasullo.Isolated
