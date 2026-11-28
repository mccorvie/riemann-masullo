module

public import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Jensen's formula on compact circles in the right half-plane

The disk coordinate is centered at 2 and carries the unit disk onto Re(s)>1/2.
Meromorphic Jensen counts signed intrinsic orders. The clipped disk weights increase to
the Green kernel in the original coordinates.
-/

@[expose] public noncomputable section

open Complex Filter Function Metric Set
open scoped Topology

namespace RiemannMasullo.HalfPlaneJensen

/-- Cayley map taking the disk center to the ordinary Euler point 2. -/
def toHalf (u : ℂ) : ℂ := (2 + u) / (1 - u)

/-- Inverse Cayley coordinate on the open right half-plane. -/
def toDisk (s : ℂ) : ℂ := (s - 2) / (s + 1)

abbrev Disk := {u : ℂ // ‖u‖ < 1}
abbrev Right := {s : ℂ // 1 / 2 < s.re}

theorem half_den {u : ℂ} (hu : ‖u‖ < 1) : 1-u ≠ 0 := by
  intro he
  have := sub_eq_zero.mp he
  simp [← this] at hu

theorem disk_den {s : ℂ} (hs : 1/2 < s.re) : s+1 ≠ 0 := by
  intro he
  have h := congrArg Complex.re he
  simp at h
  linarith

theorem chart_hasDerivAt {u : ℂ} (h : 1-u ≠ 0) :
    HasDerivAt toHalf (3 / (1-u)^2) u := by
  have h₁ : HasDerivAt (fun z : ℂ ↦ 2+z) 1 u := by simpa using (hasDerivAt_id u).const_add (2:ℂ)
  have h₂ : HasDerivAt (fun z : ℂ ↦ 1-z) (-1) u := by simpa using (hasDerivAt_id u).const_sub (1:ℂ)
  unfold toHalf
  convert h₁.div h₂ h using 1
  ring

theorem chart_analytic {u : ℂ} (hu : ‖u‖<1) : AnalyticAt ℂ toHalf u := by
  unfold toHalf
  exact (show AnalyticAt ℂ (fun z : ℂ ↦ 2+z) u by fun_prop).div
    (show AnalyticAt ℂ (fun z : ℂ ↦ 1-z) u by fun_prop) (half_den hu)

theorem chart_deriv_ne {u : ℂ} (hu : ‖u‖<1) : deriv toHalf u ≠ 0 := by
  rw [(chart_hasDerivAt (half_den hu)).deriv]
  exact div_ne_zero (by norm_num) (pow_ne_zero _ (half_den hu))

private theorem norm_gap (s : ℂ) : ‖s+1‖^2 - ‖s-2‖^2 = 6*s.re-3 := by
  norm_num [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.sub_re,
    Complex.add_im, Complex.sub_im]
  ring

theorem toDisk_toHalf {u : ℂ} (hu : 1-u ≠ 0) : toDisk (toHalf u) = u := by
  unfold toDisk toHalf
  have h : (2+u)/(1-u)+1 ≠ 0 := by
    rw [show (2+u)/(1-u)+1 = 3/(1-u) by field_simp [hu]; ring]
    exact div_ne_zero (by norm_num) hu
  field_simp [hu, h]
  ring

theorem toHalf_toDisk {s : ℂ} (hs : s+1 ≠ 0) : toHalf (toDisk s) = s := by
  unfold toDisk toHalf
  have h : 1-(s-2)/(s+1) ≠ 0 := by
    rw [show 1-(s-2)/(s+1) = 3/(s+1) by field_simp [hs]; ring]
    exact div_ne_zero (by norm_num) hs
  field_simp [hs, h]
  ring

theorem toDisk_lt {s : ℂ} (hs : 1/2 < s.re) : ‖toDisk s‖ < 1 := by
  rw [toDisk, norm_div, div_lt_one (norm_pos_iff.mpr (disk_den hs))]
  nlinarith [norm_gap s, norm_nonneg (s-2), norm_nonneg (s+1)]

theorem toHalf_re {u : ℂ} (hu : ‖u‖ < 1) : 1/2 < (toHalf u).re := by
  have hn := half_den hu
  have hd : toHalf u + 1 ≠ 0 := by
    unfold toHalf
    rw [show (2+u)/(1-u)+1 = 3/(1-u) by field_simp [hn]; ring]
    exact div_ne_zero (by norm_num) hn
  have h := hu
  rw [← toDisk_toHalf hn, toDisk, norm_div, div_lt_one (norm_pos_iff.mpr hd)] at h
  nlinarith [norm_gap (toHalf u), norm_nonneg (toHalf u - 2), norm_nonneg (toHalf u + 1),
    sq_lt_sq' (show -‖toHalf u+1‖ < ‖toHalf u-2‖ by linarith [norm_pos_iff.mpr hd, norm_nonneg (toHalf u-2)]) h]

/-- Bijection of the open unit disk with the half-plane to the right of the critical line. -/
def cayley : Disk ≃ Right where
  toFun z := ⟨toHalf z.val, toHalf_re z.property⟩
  invFun s := ⟨toDisk s.val, toDisk_lt s.property⟩
  left_inv z := Subtype.ext (toDisk_toHalf (half_den z.property))
  right_inv s := Subtype.ext (toHalf_toDisk (disk_den s.property))

@[simp] theorem chart_zero : toHalf 0 = 2 := by simp [toHalf]
@[simp] theorem disk_one : toDisk 1 = -(1/2) := by norm_num [toDisk]

/-- The positive truncation appearing on a circle of radius r in the unit disk. -/
def weight (r : ℝ) (s : ℂ) : ℝ := max 0 (Real.log (r / ‖toDisk s‖))

theorem weight_nonneg (r : ℝ) (s : ℂ) : 0 ≤ weight r s := le_max_left _ _

theorem weight_mono {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (s : ℂ) :
    weight r s ≤ weight R s := by
  unfold weight
  by_cases h : ‖toDisk s‖ = 0
  · simp [h]
  · have hp := lt_of_le_of_ne (norm_nonneg (toDisk s)) (Ne.symm h)
    exact max_le_max_left _ (Real.log_le_log (div_pos hr hp) (div_le_div_of_nonneg_right hrR hp.le))

theorem weight_continuousAt_one {s : ℂ} (hs : s ≠ 2) (hd : s+1 ≠ 0) :
    ContinuousAt (fun r ↦ weight r s) 1 := by
  have h : toDisk s ≠ 0 := div_ne_zero (sub_ne_zero.mpr hs) hd
  unfold weight
  exact continuousAt_const.max ((continuousAt_id.div_const _).log (div_ne_zero one_ne_zero (norm_ne_zero_iff.mpr h)))

theorem weight_one_of_right {s : ℂ} (hs : 1/2 < s.re) (hne : s ≠ 2) :
    weight 1 s = Real.log (‖s+1‖ / ‖s-2‖) := by
  have h0 : 0 < ‖toDisk s‖ := norm_pos_iff.mpr (div_ne_zero (sub_ne_zero.mpr hne) (disk_den hs))
  rw [weight, max_eq_right (Real.log_nonneg ((one_le_div h0).mpr (toDisk_lt hs).le)),
    toDisk, norm_div, one_div, inv_div]

/-- The upper bound holds with a summable quadratic weight throughout the right critical half-strip. -/
theorem weight_one_le {s : ℂ} (hs : 1/2 < s.re) (hσ : s.re ≤ 1) :
    weight 1 s ≤ 3 / (1 + |s.im|)^2 := by
  have hn : s ≠ 2 := by rintro rfl; norm_num at hσ
  have hd : 0 < ‖s-2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hn)
  have hp : 0 < ‖s+1‖ := norm_pos_iff.mpr (disk_den hs)
  let R := ‖s+1‖/‖s-2‖
  have hR : 0<R := div_pos hp hd
  have hlog := Real.log_le_sub_one_of_pos (sq_pos_of_pos hR)
  rw [Real.log_pow] at hlog
  have hQ : (1+|s.im|)^2 ≤ 2*‖s-2‖^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num [Complex.sub_re, Complex.sub_im]
    nlinarith [sq_abs s.im, sq_nonneg (|s.im|-1), mul_nonneg (by linarith : 0≤1-s.re) (by linarith : 0≤3-s.re)]
  have hgap := norm_gap s
  have hh : R^2 - 1 ≤ 3 / ‖s-2‖^2 := by
    dsimp [R]
    rw [div_pow, div_sub_one (pow_ne_zero 2 hd.ne')]
    exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
  rw [weight_one_of_right hs hn]
  change Real.log R ≤ _
  have hrec : 3 / ‖s-2‖^2 ≤ 2*(3 / (1+|s.im|)^2) := by
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [hQ]
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

/-- Mean log modulus on the Cayley image of the circle of radius r about zero. -/
def circleMean (L : ℂ → ℂ) (r : ℝ) : ℝ :=
  Real.circleAverage (fun u ↦ Real.log ‖L (toHalf u)‖) 0 r

private theorem norm_le_iff_closed (r : ℝ) (u : ℂ) :
    u ∈ closedBall 0 r ↔ ‖u‖ ≤ r := by simp [Metric.mem_closedBall]

theorem circle_integrable (L : ℂ → ℂ) (hL : MeromorphicOn L univ) {r : ℝ} (hr : 0 < r)
    (hr1 : r < 1) : CircleIntegrable (fun u ↦ Real.log ‖L (toHalf u)‖) 0 r := by
  have hm : MeromorphicOn (L ∘ toHalf) (closedBall 0 |r|) := by
    intro u hu
    rw [abs_of_pos hr, norm_le_iff_closed] at hu
    exact (hL (toHalf u) (mem_univ _)).comp_analyticAt (chart_analytic (hu.trans_lt hr1))
  exact (show MeromorphicOn (L ∘ toHalf) (sphere 0 |r|) from
    fun u hu ↦ hm u (sphere_subset_closedBall hu)).circleIntegrable_log_norm

/-- Jensen's formula transported by the Cayley equivalence, with signed intrinsic orders. -/
theorem right_circle_hasSum (L : ℂ → ℂ) (hL : MeromorphicOn L univ) (hA : AnalyticAt ℂ L 2)
    (h₂ : L 2 ≠ 0) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasSum (fun s : Right ↦ ((meromorphicOrderAt L s.val).untop₀ : ℝ) * weight r s.val)
      (circleMean L r - Real.log ‖L 2‖) := by
  classical
  let g := L ∘ toHalf
  let B := closedBall (0 : ℂ) r
  let d := MeromorphicOn.divisor g B
  let term (u : ℂ) := (d u : ℝ) * Real.log (r * ‖(0:ℂ) - u‖⁻¹)
  have hm : MeromorphicOn g B := by
    intro u hu
    exact (hL (toHalf u) (mem_univ _)).comp_analyticAt
      (chart_analytic (((norm_le_iff_closed _ _).mp hu).trans_lt hr1))
  have hn : g 0 ≠ 0 := by simpa [g] using h₂
  have hA' : AnalyticAt ℂ g 0 := by
    have ha : AnalyticAt ℂ L (toHalf 0) := by simpa using hA
    exact ha.comp (chart_analytic (by simp))
  have hdz : d 0 = 0 := by
    rw [show d 0 = _ from MeromorphicOn.divisor_apply hm (mem_closedBall_self hr.le),
      hA'.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hn]
    rfl
  have J := MeromorphicOn.circleAverage_log_norm (f := g) (c := 0) hr.ne'
    (show MeromorphicOn g (closedBall 0 |r|) by rwa [abs_of_pos hr])
  rw [abs_of_pos hr, hA'.meromorphicTrailingCoeffAt_of_ne_zero hn] at J
  change circleMean L r = (∑ᶠ u, term u) + (d 0 : ℝ) * Real.log r + Real.log ‖g 0‖ at J
  simp only [hdz, Int.cast_zero, zero_mul, add_zero, g, comp_apply,chart_zero] at J
  have hdfin := d.finiteSupport (isCompact_closedBall (0:ℂ) r)
  have hsub : support term ⊆ d.support := by
    intro u hu
    by_contra h
    change ¬ d u ≠ 0 at h
    exact hu (by simp [term, not_not.mp h])
  have hf := hdfin.subset hsub
  have ht : HasSum term (circleMean L r - Real.log ‖L 2‖) := by
    rw [J,add_sub_cancel_right,finsum_eq_sum_of_support_subset (s := hf.toFinset) _ (by simp)]
    apply hasSum_sum_of_ne_finset_zero
    intro x hx
    by_contra hh
    exact hx (hf.mem_toFinset.mpr hh)
  have hU : support term ⊆ {u : ℂ | ‖u‖ < 1} := by
    intro u hu
    exact ((norm_le_iff_closed _ _).mp (d.supportWithinDomain (hsub hu))).trans_lt hr1
  have hres := (hasSum_subtype_iff_of_support_subset hU).mpr ht
  have hre := (cayley.symm.hasSum_iff).mpr hres
  apply hre.congr_fun
  intro s
  symm
  change term (toDisk s.val) = _
  let u := toDisk s.val
  have hsmall := toDisk_lt s.property
  have hmap := toHalf_toDisk (disk_den s.property)
  have hzero (hh : ‖u‖=0) : term u = 0 ∧ weight r s.val = 0 := by
    change (d u : ℝ) * Real.log (r * ‖(0:ℂ) - u‖⁻¹) = 0 ∧ max 0 (Real.log (r / ‖u‖)) = 0
    simp [hh]
  by_cases hu0 : ‖u‖ = 0
  · obtain ⟨h₁,h₂⟩ := hzero hu0
    change term u = _ * _
    rw [h₁,h₂,mul_zero]
  have hpos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu0)
  by_cases hur : ‖u‖ ≤ r
  · have hdu : d u = (meromorphicOrderAt L s.val).untop₀ := by
      rw [show d u = _ from MeromorphicOn.divisor_apply hm ((norm_le_iff_closed _ _).mpr hur)]
      simp only [g, meromorphicOrderAt_comp_of_deriv_ne_zero (chart_analytic hsmall) (chart_deriv_ne hsmall), u, hmap]
    have hlog : 0 ≤ Real.log (r / ‖u‖) := Real.log_nonneg ((one_le_div hpos).mpr hur)
    change term u = _ * max 0 (Real.log (r / ‖u‖))
    rw [max_eq_right hlog]
    simp [term,hdu,div_eq_mul_inv]
  · have hdu : d u = 0 := by
      by_contra h
      exact hur ((norm_le_iff_closed _ _).mp (d.supportWithinDomain h))
    have hlog : Real.log (r / ‖u‖) ≤ 0 :=
      Real.log_nonpos (div_nonneg hr.le hpos.le) ((div_le_one hpos).mpr (le_of_not_ge hur))
    change term u = _ * max 0 (Real.log (r / ‖u‖))
    simp [term, hdu, max_eq_left hlog]

/-- The half-plane Green kernel at 2 in the original real coordinates. -/
def greenKernel (s : ℂ) : ℝ :=
  (1/2:ℝ) * Real.log ((((3/2:ℝ) + (s.re-1/2))^2 + s.im^2) /
                        (((3/2:ℝ) - (s.re-1/2))^2 + s.im^2))

theorem weight_one_eq_green {s : ℂ} (hs : 1/2 < s.re) (hn : s ≠ 2) :
    weight 1 s = greenKernel s := by
  have hnum : ‖s+1‖^2 = ((3/2:ℝ) + (s.re-1/2))^2 + s.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im,add_zero]
    ring
  have hden : ‖s-2‖^2 = ((3/2:ℝ) - (s.re-1/2))^2 + s.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num [Complex.sub_re, Complex.sub_im]
    ring
  rw [weight_one_of_right hs hn, greenKernel, ← hnum, ← hden, ← div_pow, Real.log_pow]
  ring

open MeasureTheory in
private theorem green_coordinates_bounds {x : ℝ} (hx : 0 ≤ x) (hhalf : x ≤ 1/2) (t : ℝ) :
    let g := (Real.log ((3/2+x)^2+t^2) - Real.log ((3/2-x)^2+t^2))/2
    (4/3)*x/(1+t^2) ≤ g ∧ g ≤ 3*x/(1+t^2) := by
  intro g
  let l := 3/2 - x
  let r := 3/2 + x
  have hl : 1 ≤ l := by dsimp [l]; linarith
  have hlr : l ≤ r := by dsimp [l,r]; linarith
  have ht : 0 < 1 + t^2 := by positivity
  let K (u : ℝ) := (1+t^2) * (u / (u^2+t^2))
  have hden (u : ℝ) (hu : l ≤ u) : 0 < u^2+t^2 := by
    have hp : 0 < u := by linarith
    positivity
  have hI : IntervalIntegrable K volume l r := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hlr]
    apply continuousOn_const.mul
    exact continuousOn_id.div ((continuous_id.pow 2).add continuous_const).continuousOn (fun u hu ↦ (hden u hu.1).ne')
  have hright := intervalIntegral.integral_mono_on hlr hI (continuous_id.intervalIntegrable l r)
    (fun u hu ↦ show K u ≤ u from by
      dsimp [K]
      rw [← mul_div_assoc, div_le_iff₀ (hden u hu.1)]
      have h1 : 1 ≤ u := hl.trans hu.1
      nlinarith [mul_nonneg (show 0 ≤ u by linarith) (show 0 ≤ u^2-1 by nlinarith)])
  have hleft := intervalIntegral.integral_mono_on hlr
    ((show Continuous (fun u : ℝ ↦ 4/3-(4/9)*u) by fun_prop).intervalIntegrable l r) hI
    (fun u hu ↦ show 4/3-(4/9)*u ≤ K u from by
      have h1 : 1 ≤ u := hl.trans hu.1
      have hpos : 0 < u := by linarith
      calc
        4/3-(4/9)*u ≤ 1/u := (le_div_iff₀ hpos).2 (by nlinarith [sq_nonneg (2*u-3)])
        _ ≤ K u := by
          dsimp [K]
          rw [← mul_div_assoc, div_le_div_iff₀ hpos (hden u hu.1)]
          nlinarith [mul_nonneg (show 0 ≤ u^2-1 by nlinarith) (sq_nonneg t)])
  have hK : (∫ u in l..r, K u) = (1+t^2) * g := by
    dsimp only [K, g]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    rw [sub_div]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u : ℝ ↦ Real.log (u^2+t^2)/2)
    · intro u hu
      rw [uIcc_of_le hlr] at hu
      have hd := (((hasDerivAt_pow 2 u).add_const (t^2)).log (hden u hu.1).ne').div_const 2
      convert hd using 1
      ring
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hlr]
      exact continuousOn_id.div ((continuous_id.pow 2).add continuous_const).continuousOn (fun u hu ↦ (hden u hu.1).ne')
  simp only [id_eq] at hright
  rw [hK, integral_id] at hright
  rw [hK, intervalIntegral.integral_sub, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, integral_id, smul_eq_mul] at hleft
  · dsimp [l,r] at hleft hright
    exact ⟨(div_le_iff₀ ht).2 (by nlinarith), (le_div_iff₀ ht).2 (by nlinarith)⟩
  · exact continuous_const.intervalIntegrable _ _
  · exact (show Continuous (fun u : ℝ ↦ (4/9)*u) by fun_prop).intervalIntegrable _ _

/-- On the right half of the closed critical strip, the Green logarithm controls the
horizontal displacement divided by the quadratic height weight. -/
theorem greenKernel_bounds {s : ℂ} (h₀ : 1/2 ≤ s.re) (h₁ : s.re ≤ 1) :
    (4/3)*(s.re-1/2)/(1+s.im^2) ≤ greenKernel s ∧
      greenKernel s ≤ 3*(s.re-1/2)/(1+s.im^2) := by
  have hp : 0 < 3/2+(s.re-1/2) := by linarith
  have hm : 0 < 3/2-(s.re-1/2) := by linarith
  rw [greenKernel, Real.log_div
    (by positivity : ((3/2+(s.re-1/2))^2+s.im^2) ≠ 0)
    (by positivity : ((3/2-(s.re-1/2))^2+s.im^2) ≠ 0), one_div, inv_mul_eq_div]
  exact green_coordinates_bounds (by linarith) (by linarith) s.im

end RiemannMasullo.HalfPlaneJensen
