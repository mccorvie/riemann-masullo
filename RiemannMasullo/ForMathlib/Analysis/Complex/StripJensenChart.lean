module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.CayleyCauchy
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! # A disk chart and both harmonic measures of a vertical strip

The exponential maps a strip to the upper half-plane. A Cayley transform then centers the disk
at any prescribed interior point. Rotating the logarithm cut below the real axis extends
the inverse across both finite edges. -/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory Metric Set
open scoped ComplexConjugate Topology

namespace RiemannMasullo.StripJensen

/-- The upper-half-plane Cayley map fixes the choice of the first end at one. -/
def disk (a u : ℂ) : ℂ := (u-a)/(u-conj a)

/-- The inverse Cayley map sending the origin to the prescribed upper-half-plane point. -/
def upper (a v : ℂ) : ℂ := (a-conj a*v)/(1-v)

private theorem one_sub_ne {v : ℂ} (hv : ‖v‖ < 1) : 1-v ≠ 0 := by
  intro h
  have he := sub_eq_zero.mp h
  simp [←he] at hv

private theorem sub_conj_ne {z a : ℂ} (hz : 0 < z.im) (ha : 0 < a.im) : z-conj a ≠ 0 := by
  intro h
  have he := congrArg Complex.im (sub_eq_zero.mp h)
  simp at he
  linarith

theorem disk_norm_lt {z a : ℂ} (hz : 0 < z.im) (ha : 0 < a.im) : ‖disk a z‖ < 1 := by
  rw [disk,norm_div,div_lt_one (norm_pos_iff.mpr (sub_conj_ne hz ha))]
  apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [←Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.conj_re,Complex.conj_im]
  nlinarith [mul_pos hz ha]

private theorem upper_affine {v : ℂ} (hv : 1-v ≠ 0) (a : ℂ) :
    upper a v = (a.re:ℂ) + I*((a.im:ℂ)*((1+v)/(1-v))) := by
  unfold upper
  field_simp
  apply Complex.ext <;> simp [Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
    Complex.mul_re,Complex.mul_im] <;> ring

private theorem upper_im_pos {a v : ℂ} (ha : 0 < a.im) (hv : ‖v‖ < 1) : 0 < (upper a v).im := by
  rw [upper_affine (one_sub_ne hv),Complex.add_im,Complex.ofReal_im,zero_add,Complex.I_mul_im,
    Complex.re_ofReal_mul]
  apply mul_pos ha
  have hgap : 0 < 1 - Complex.normSq v := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg v]
  have hp := Complex.normSq_pos.mpr (one_sub_ne hv)
  have h : ((1+v)/(1-v)).re = (1-Complex.normSq v)/Complex.normSq (1-v) := by
    rw [Complex.div_re,Complex.normSq_apply v]
    simp only [Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,
      zero_add,zero_sub]
    ring
  rw [h]
  exact div_pos hgap hp

private theorem upper_disk {a z : ℂ} (ha : 0 < a.im) (hz : 0 < z.im) : upper a (disk a z) = z := by
  have hn := one_sub_ne (disk_norm_lt hz ha)
  unfold upper
  apply (div_eq_iff hn).2
  rw [disk]
  field_simp [sub_conj_ne hz ha]
  ring

private theorem disk_upper {a v : ℂ} (ha : 0 < a.im) (hv : ‖v‖ < 1) : disk a (upper a v) = v := by
  have hn := sub_conj_ne (upper_im_pos ha hv) ha
  unfold disk
  apply (div_eq_iff hn).2
  rw [upper]
  field_simp [one_sub_ne hv]
  ring

private theorem upper_deriv {a v : ℂ} (hv : ‖v‖ < 1) :
    HasDerivAt (upper a) ((a-conj a)/(1-v)^2) v := by
  have h₁ := ((hasDerivAt_id v).const_mul (conj a)).const_sub a
  have h₂ := (hasDerivAt_id v).const_sub (1:ℂ)
  unfold upper
  convert h₁.div h₂ (one_sub_ne hv) using 1
  · rfl
  · dsimp; ring

private theorem upper_analytic {a v : ℂ} (hv : ‖v‖ < 1) : AnalyticAt ℂ (upper a) v := by
  unfold upper
  exact (show AnalyticAt ℂ (fun u : ℂ ↦ a-conj a*u) v by fun_prop).div
    (by fun_prop) (one_sub_ne hv)

/-- A complex point belongs to the vertical strip when its exponential angle is in (0, pi). -/
def InStrip (c k : ℝ) (z : ℂ) : Prop := 0 < k*(z.re-c) ∧ k*(z.re-c) < Real.pi

theorem inStrip_iff {c w : ℝ} (hw : 0 < w) (z : ℂ) :
    InStrip c (Real.pi/w) z ↔ c < z.re ∧ z.re < c+w := by
  have hk : 0 < Real.pi/w := div_pos Real.pi_pos hw
  have h : (Real.pi/w)*(z.re-c) < Real.pi ↔ z.re < c+w := calc
    _ ↔ (Real.pi/w)*(z.re-c) < (Real.pi/w)*w := by rw [div_mul_cancel₀ _ hw.ne']
    _ ↔ _ := by rw [mul_lt_mul_iff_right₀ hk]; constructor <;> intro h <;> linarith
  simp only [InStrip,h,mul_pos_iff_of_pos_left hk, sub_pos]

/-- Exponential to the upper half-plane. Its positive and negative boundary rays are distinct. -/
def ray (c k : ℝ) (z : ℂ) : ℂ := Complex.exp ((k:ℂ)*I*(z-(c:ℂ)))

/-- Principal holomorphic inverse on the upper half-plane. -/
def unray (c k : ℝ) (u : ℂ) : ℂ := (c:ℂ) + (-I/(k:ℂ))*Complex.log u

private theorem phase_im (c k : ℝ) (z : ℂ) :
    ((k:ℂ)*I*(z-(c:ℂ))).im = k*(z.re-c) := by
  simp [Complex.mul_im,Complex.mul_re,Complex.sub_re]

theorem ray_im_pos {c k : ℝ} {z : ℂ} (hz : InStrip c k z) : 0 < (ray c k z).im := by
  rw [ray,Complex.exp_im,phase_im]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hz.1 hz.2)

private theorem k_cancel {k : ℝ} (hk : 0 < k) : (-I/(k:ℂ))*((k:ℂ)*I) = 1 := by
  field_simp [Complex.ofReal_ne_zero.mpr hk.ne']
  simp

theorem unray_ray {c k : ℝ} (hk : 0 < k) {z : ℂ} (hz : InStrip c k z) :
    unray c k (ray c k z) = z := by
  have hn : (k:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  rw [unray,ray,Complex.log_exp (by rw [phase_im]; linarith [hz.1,Real.pi_pos])
    (by rw [phase_im]; exact hz.2.le)]
  rw [← mul_assoc,k_cancel hk,one_mul]
  ring

private theorem ray_unray {c k : ℝ} (hk : 0 < k) {u : ℂ} (hu : u ≠ 0) :
    ray c k (unray c k u) = u := by
  have hn : (k:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  unfold ray unray
  rw [show (k:ℂ)*I*((c:ℂ)+(-I/(k:ℂ))*Complex.log u-(c:ℂ)) = Complex.log u by
    simp only [add_sub_cancel_left]
    rw [←mul_assoc,mul_comm ((k:ℂ)*I),k_cancel hk,one_mul],Complex.exp_log hu]

private theorem unray_mem {c k : ℝ} (hk : 0 < k) {u : ℂ} (hu : 0 < u.im) :
    InStrip c k (unray c k u) := by
  have hArg : 0 < u.arg := lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hu.le)
    (fun h ↦ hu.ne' (Complex.arg_eq_zero_iff.mp h.symm).2)
  have hArg' : u.arg < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr hu.ne')
  have he : k*((unray c k u).re-c) = u.arg := by
    simp [unray,Complex.mul_re,Complex.div_ofReal_re,Complex.div_ofReal_im,Complex.log_im]
    field_simp
  exact ⟨he ▸ hArg,he ▸ hArg'⟩

/-- Holomorphic disk coordinate centered at any strip point. -/
def toDisk (c k : ℝ) (s z : ℂ) := disk (ray c k s) (ray c k z)

/-- Inverse of the based disk coordinate. -/
def fromDisk (c k : ℝ) (s v : ℂ) := unray c k (upper (ray c k s) v)

theorem fromDisk_mem {c k : ℝ} (hk : 0 < k) {s v : ℂ} (hs : InStrip c k s) (hv : ‖v‖ < 1) :
    InStrip c k (fromDisk c k s v) := unray_mem hk (upper_im_pos (ray_im_pos hs) hv)

theorem toDisk_lt {c k : ℝ} {s z : ℂ} (hs : InStrip c k s) (hz : InStrip c k z) :
    ‖toDisk c k s z‖ < 1 := disk_norm_lt (ray_im_pos hz) (ray_im_pos hs)

theorem fromDisk_toDisk {c k : ℝ} (hk : 0 < k) {s z : ℂ} (hs : InStrip c k s) (hz : InStrip c k z) :
    fromDisk c k s (toDisk c k s z) = z := by
  rw [fromDisk,toDisk,upper_disk (ray_im_pos hs) (ray_im_pos hz),unray_ray hk hz]

theorem toDisk_fromDisk {c k : ℝ} (hk : 0 < k) {s v : ℂ} (hs : InStrip c k s) (hv : ‖v‖ < 1) :
    toDisk c k s (fromDisk c k s v) = v := by
  have hn : upper (ray c k s) v ≠ 0 := by
    intro h
    have := upper_im_pos (ray_im_pos hs) hv
    simp [h] at this
  rw [toDisk,fromDisk,ray_unray hk hn,disk_upper (ray_im_pos hs) hv]

@[simp] theorem fromDisk_zero {c k : ℝ} (hk : 0 < k) {s : ℂ} (hs : InStrip c k s) :
    fromDisk c k s 0 = s := by simpa [fromDisk,upper] using unray_ray hk hs

theorem fromDisk_analytic_deriv {c k : ℝ} (hk : 0 < k) {s v : ℂ} (hs : InStrip c k s) (hv : ‖v‖ < 1) :
    AnalyticAt ℂ (fromDisk c k s) v ∧ deriv (fromDisk c k s) v ≠ 0 := by
  let a := ray c k s
  have ha : 0 < a.im := ray_im_pos hs
  have hU := upper_im_pos ha hv
  have hsl : upper a v ∈ slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr hU.ne')
  have hL := (analyticAt_clog hsl).comp (upper_analytic hv)
  have hd := (((Complex.hasDerivAt_log hsl).comp v (upper_deriv (a:=a) hv)).const_mul
    (-I/(k:ℂ))).const_add (c:ℂ)
  refine ⟨analyticAt_const.add (analyticAt_const.mul hL),?_⟩
  rw [show deriv (fromDisk c k s) v = _ from hd.deriv]
  have hn : upper a v ≠ 0 := by intro h; simp [h] at hU
  exact mul_ne_zero (div_ne_zero (neg_ne_zero.mpr I_ne_zero) (Complex.ofReal_ne_zero.mpr hk.ne'))
    (mul_ne_zero (inv_ne_zero hn) (div_ne_zero (sub_conj_ne ha ha) (pow_ne_zero _ (one_sub_ne hv))))

/-! ## Green weight in coordinates -/

def polarRay (x t : ℝ) : ℂ := ⟨Real.exp (-t)*Real.cos x,Real.exp (-t)*Real.sin x⟩

theorem ray_on_vertical (c k x t : ℝ) :
    ray c k ((c+x:ℝ)+(t:ℂ)*I) = polarRay (k*x) (k*t) := by
  apply Complex.ext <;>
    simp [ray,polarRay,Complex.exp_re,Complex.exp_im,Complex.mul_re,Complex.mul_im,
      Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]

private theorem exp_cosh (t : ℝ) :
    2*Real.exp (-t)*Real.cosh t = (Real.exp (-t))^2+1 := by
  rw [Real.cosh_eq]
  have h : Real.exp (-t)*Real.exp t=1 := by rw [←Real.exp_add]; simp
  nlinarith

private theorem polar_norm_sq (x b t : ℝ) :
    ‖polarRay x t-polarRay b 0‖^2 =
      2*Real.exp (-t)*(Real.cosh t-Real.cos (x-b)) := by
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply,Real.cos_sub]
  simp only [polarRay,Complex.sub_re,Complex.sub_im,neg_zero,Real.exp_zero,one_mul]
  linear_combination (Real.exp (-t))^2*(Real.sin_sq_add_cos_sq x)
    + (Real.sin_sq_add_cos_sq b) - exp_cosh t

private theorem conj_polar (b : ℝ) : conj (polarRay b 0) = polarRay (-b) 0 := by
  apply Complex.ext <;> simp [polarRay]

/-- The logarithm of the inverse disk radius is the positive strip Green function. -/
private theorem polar_green (x b t : ℝ) (h : polarRay x t ≠ polarRay b 0)
    (h' : polarRay x t ≠ conj (polarRay b 0)) :
    -Real.log ‖disk (polarRay b 0) (polarRay x t)‖ =
      Real.log ((Real.cosh t-Real.cos (x+b))/(Real.cosh t-Real.cos (x-b)))/2 := by
  let n := ‖polarRay x t-conj (polarRay b 0)‖
  let d := ‖polarRay x t-polarRay b 0‖
  have hn : 0 < n := norm_pos_iff.mpr (sub_ne_zero.mpr h')
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  have he := Real.exp_pos (-t)
  have hD : d^2 = 2*Real.exp (-t)*(Real.cosh t-Real.cos (x-b)) := polar_norm_sq x b t
  have hN : n^2 = 2*Real.exp (-t)*(Real.cosh t-Real.cos (x+b)) := by
    dsimp [n]
    rw [conj_polar,polar_norm_sq,sub_neg_eq_add]
  have ratio : (Real.cosh t-Real.cos (x+b))/(Real.cosh t-Real.cos (x-b)) = (n/d)^2 := by
    rw [div_pow,hN,hD,mul_div_mul_left _ _ (by positivity : 2*Real.exp (-t) ≠ 0)]
  rw [ratio,Real.log_pow,Real.log_div hn.ne' hd.ne',disk,norm_div]
  change -Real.log (d/n) = _
  rw [Real.log_div hd.ne' hn.ne']
  ring

/-- For a real base on the horizontal line of height zero, the Green kernel in the original units. -/
theorem green_coordinates {c k x b t : ℝ}
    (hs : InStrip c k ((c+b:ℝ):ℂ)) (hz : InStrip c k ((c+x:ℝ)+(t:ℂ)*I))
    (hne : ray c k ((c+x:ℝ)+(t:ℂ)*I) ≠ ray c k ((c+b:ℝ):ℂ)) :
    -Real.log ‖toDisk c k ((c+b:ℝ):ℂ) ((c+x:ℝ)+(t:ℂ)*I)‖ =
      Real.log ((Real.cosh (k*t)-Real.cos (k*x+k*b))/(Real.cosh (k*t)-Real.cos (k*x-k*b)))/2 := by
  have hbase : ray c k ((c+b:ℝ):ℂ) = polarRay (k*b) 0 := by simpa using ray_on_vertical c k b 0
  have hsecond : ray c k ((c+x:ℝ)+(t:ℂ)*I) ≠ conj (ray c k ((c+b:ℝ):ℂ)) := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.conj_im] at hi
    linarith [ray_im_pos hs,ray_im_pos hz]
  rw [ray_on_vertical,hbase] at hne hsecond
  rw [toDisk,ray_on_vertical,hbase]
  exact polar_green _ _ _ hne hsecond

/-- The two strip boundary probability densities use sign 1 for the left edge and -1 for the right. -/
def edge (k side b t : ℝ) : ℝ :=
  k*Real.sin b/(2*Real.pi*(Real.cosh t-side*Real.cos b))

/-- Arclength Jacobian (including the factor 1/pi from harmonic measure on the upper half-plane). -/
private theorem edge_eq_pullback {side : ℝ} (h : side=1 ∨ side = -1) (k b t : ℝ) :
    k*Real.exp (-t)*(Real.sin b)/
      (Real.pi*((side*Real.exp (-t)-Real.cos b)^2+(Real.sin b)^2)) = edge k side b t := by
  have hp : (side*Real.exp (-t)-Real.cos b)^2+(Real.sin b)^2 =
      2*Real.exp (-t)*(Real.cosh t-side*Real.cos b) := by
    rcases h with rfl | rfl <;>
      linear_combination Real.sin_sq_add_cos_sq b - exp_cosh t
  rw [hp,edge]
  by_cases hd : Real.cosh t - side*Real.cos b = 0
  · simp [hd]
  · field_simp [Real.pi_ne_zero,(Real.exp_pos (-t)).ne',hd]

theorem edge_eq_width {w : ℝ} (hw : 0 < w) (side b t : ℝ) :
    edge (Real.pi/w) side (Real.pi/w*b) (Real.pi/w*t) =
      Real.sin (Real.pi*b/w)/(2*w*(Real.cosh (Real.pi*t/w)-side*Real.cos (Real.pi*b/w))) := by
  unfold edge
  rw [show Real.pi/w*b=Real.pi*b/w by ring,show Real.pi/w*t=Real.pi*t/w by ring]
  by_cases h : Real.cosh (Real.pi*t/w)-side*Real.cos (Real.pi*b/w) = 0
  · simp [h]
  · field_simp [Real.pi_ne_zero,hw.ne',h]

/-! ## Two boundary measures -/

/-- This logarithm has its cut on the lower imaginary ray, away from both finite boundary lines. -/
def logUp (u : ℂ) : ℂ := Complex.log (-I*u) + (Real.pi:ℂ)/2*I

private theorem logUp_eq {u : ℂ} (hu : 0 ≤ u.im) (hn : u ≠ 0) : logUp u = Complex.log u := by
  have hx : Complex.arg (-I)+u.arg ∈ Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_neg_I]
    exact ⟨by linarith [Complex.arg_nonneg_iff.mpr hu,Real.pi_pos],by linarith [Complex.arg_le_pi u,Real.pi_pos]⟩
  rw [logUp,(Complex.log_mul_eq_add_log_iff (neg_ne_zero.mpr I_ne_zero) hn).2 hx,Complex.log_neg_I]
  ring

private theorem logUp_analytic {u : ℂ} (hu : 0 ≤ u.im) (hn : u ≠ 0) : AnalyticAt ℂ logUp u := by
  have hsl : -I*u ∈ slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    by_cases hp : 0 < u.im
    · left; simpa [Complex.mul_re] using hp
    · right
      have h0 := le_antisymm (le_of_not_gt hp) hu
      have h₁ : u.re ≠ 0 := fun h ↦ hn (Complex.ext (by simpa using h) (by simpa using h0))
      simpa [Complex.mul_im] using h₁
  unfold logUp
  exact ((analyticAt_const.mul analyticAt_id).clog hsl).add analyticAt_const

def fromDiskAcross (c k : ℝ) (s v : ℂ) : ℂ :=
  (c:ℂ) + (-I/(k:ℂ))*logUp (upper (ray c k s) v)

private theorem fromDiskAcross_eq {c k : ℝ} {s v : ℂ}
    (h : 0 ≤ (upper (ray c k s) v).im) (hn : upper (ray c k s) v ≠ 0) :
    fromDiskAcross c k s v = fromDisk c k s v := by
  rw [fromDiskAcross,logUp_eq h hn,fromDisk,unray]

/-- The repaired inverse chart extends analytically through all finite points of both edges. -/
private theorem fromDiskAcross_analytic {c k : ℝ} {s v : ℂ} (hv : 1-v ≠ 0)
    (hu : 0 ≤ (upper (ray c k s) v).im) (hn : upper (ray c k s) v ≠ 0) :
    AnalyticAt ℂ (fromDiskAcross c k s) v := by
  have hU : AnalyticAt ℂ (upper (ray c k s)) v := by
    unfold upper
    exact (by fun_prop : AnalyticAt ℂ (fun u : ℂ ↦ ray c k s-conj (ray c k s)*u) v).div
      (by fun_prop) hv
  exact analyticAt_const.add (analyticAt_const.mul ((logUp_analytic hu hn).comp hU))

private theorem angle_ne_one {a : ℝ} (t : ℝ) : circleMap 0 1 (CayleyCauchy.inverseAngle a t) ≠ 1 := by
  let θ := CayleyCauchy.inverseAngle a t
  have hθ := CayleyCauchy.inverseAngle_mem a t
  intro he
  apply hθ.1.ne'
  apply eq_of_circleMap_eq (c:=(0:ℂ)) (R:=(1:ℝ)) one_ne_zero
    (by simpa only [sub_zero,abs_of_pos hθ.1] using hθ.2)
  simpa [circleMap] using he

private theorem upper_at_angle {a : ℂ} (ha : 0 < a.im) (t : ℝ) :
    upper a (circleMap 0 1 (CayleyCauchy.inverseAngle a.im t)) = ((a.re-t:ℝ):ℂ) := by
  let v := circleMap 0 1 (CayleyCauchy.inverseAngle a.im t)
  have hv : 1-v ≠ 0 := sub_ne_zero.mpr (angle_ne_one t).symm
  have h := CayleyCauchy.chart_inverseAngle 0 ha t
  change (0:ℂ)+(a.im:ℂ)*((1+v)/(1-v)) = 0+(t:ℂ)*I at h
  simp only [zero_add] at h
  rw [upper_affine hv,h,Complex.ofReal_sub]
  linear_combination (t:ℂ)*Complex.I_sq

/-- The angular probability on the based disk becomes an ordinary translated Cauchy
density in the real coordinate of the upper half-plane. -/
private theorem circle_to_real (c k : ℝ) (s : ℂ) (hs : InStrip c k s) (F : ℂ → ℝ) :
    Real.circleAverage (fun v ↦ F (fromDisk c k s v)) 0 1 =
      ∫ x : ℝ, CayleyCauchy.density (ray c k s).im ((ray c k s).re-x) * F (unray c k (x:ℂ)) := by
  let a := ray c k s
  have ha : 0 < a.im := ray_im_pos hs
  rw [CayleyCauchy.circleAverage_inverseAngle ha]
  let H := fun x : ℝ ↦ CayleyCauchy.density a.im (a.re-x)*F (unray c k (x:ℂ))
  change _ = ∫ x, H x
  rw [← integral_sub_left_eq_self H volume a.re]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only [H]
  rw [sub_sub_cancel,fromDisk,upper_at_angle ha]
  rfl

private theorem circleIntegrable_real_iff (c k : ℝ) (s : ℂ) (hs : InStrip c k s) (F : ℂ → ℝ) :
    CircleIntegrable (fun v ↦ F (fromDisk c k s v)) 0 1 ↔
       Integrable (fun x : ℝ ↦ CayleyCauchy.density (ray c k s).im ((ray c k s).re-x) * F (unray c k (x:ℂ))) := by
  let a := ray c k s
  have ha : 0 < a.im := ray_im_pos hs
  rw [CayleyCauchy.circleIntegrable_inverseAngle_iff ha]
  let H := fun x : ℝ ↦ CayleyCauchy.density a.im (a.re-x)*F (unray c k (x:ℂ))
  change _ ↔ Integrable H
  rw [← (volume.measurePreserving_sub_left a.re).integrable_comp_emb (MeasurableEquiv.subLeft a.re).measurableEmbedding]
  apply integrable_congr
  filter_upwards with t
  change CayleyCauchy.density a.im (a.re-t)*F (fromDisk c k s (circleMap 0 1 (CayleyCauchy.inverseAngle a.im (a.re-t)))) = _
  rw [fromDisk,upper_at_angle ha,sub_sub_cancel]

private theorem unray_positive (c : ℝ) {k : ℝ} (hk : 0 < k) (t : ℝ) :
    unray c k (Real.exp (-(k*t)) : ℂ) = (c:ℂ)+(t:ℂ)*I := by
  rw [unray,← Complex.ofReal_log (Real.exp_pos _).le,Real.log_exp]
  push_cast
  field_simp [show (k:ℂ) ≠ 0 by exact_mod_cast hk.ne']

private theorem unray_negative (c : ℝ) {k : ℝ} (hk : 0 < k) (t : ℝ) :
    unray c k (-(Real.exp (-(k*t)) : ℂ)) = (c+Real.pi/k:ℝ)+(t:ℂ)*I := by
  have hp := Real.exp_pos (-(k*t))
  have hh : Complex.log (-(Real.exp (-(k*t)):ℂ)) = (-(k*t):ℝ)+(Real.pi:ℂ)*I := by
    convert Complex.log_ofReal_mul hp (show (-1:ℂ)≠0 by norm_num) using 1 <;>
      simp only [Complex.log_neg_one,mul_neg_one,Real.log_exp]
  rw [unray,hh]
  push_cast
  field_simp [show (k:ℂ) ≠ 0 by exact_mod_cast hk.ne']
  linear_combination -(Real.pi:ℂ)*Complex.I_sq

private theorem real_rays {k : ℝ} (hk : 0 < k) (H : ℝ → ℝ) (hH : Integrable H) :
    ∫ u, H u = (∫ t : ℝ, k*Real.exp (-(k*t))*H (Real.exp (-(k*t)))) +
      ∫ t : ℝ, k*Real.exp (-(k*t))*H (-Real.exp (-(k*t))) := by
  have half (G : ℝ → ℝ) :
      ∫ u in Ioi (0:ℝ), G u = ∫ t : ℝ, k*Real.exp (-(k*t))*G (Real.exp (-(k*t))) := by
    let H₁ := fun x : ℝ ↦ Real.exp x*G (Real.exp x)
    have h₁ : ∫ u in Ioi (0:ℝ), G u = ∫ x, H₁ x := (integral_comp_exp G).symm
    have h₂ := Measure.integral_comp_mul_left H₁ (-k)
    rw [inv_neg,abs_neg,abs_of_pos (inv_pos.mpr hk),smul_eq_mul] at h₂
    rw [h₁]
    calc (∫ x, H₁ x) = k*(∫ t, H₁ (-k*t)) := by rw [h₂]; field_simp
      _ = _ := by rw [←integral_const_mul]; congr 1; funext t; dsimp [H₁]; rw [neg_mul]; ring
  have h := integral_add_compl (s:=Ioi (0:ℝ)) measurableSet_Ioi hH
  rw [compl_Ioi] at h
  rw [←h,half,← show (∫ x in Ioi (0:ℝ), H (-x)) = ∫ x in Iic (0:ℝ), H x by simp,
    half]

/-- Exact probability mass times arbitrary real boundary data on the two vertical sides. -/
theorem circle_to_edges {c k b : ℝ} (hk : 0 < k) (hs : InStrip c k ((c+b:ℝ):ℂ))
    (F : ℂ → ℝ) (hF : CircleIntegrable (fun v ↦ F (fromDisk c k ((c+b:ℝ):ℂ) v)) 0 1) :
    Real.circleAverage (fun v ↦ F (fromDisk c k ((c+b:ℝ):ℂ) v)) 0 1 =
      (∫ t : ℝ, edge k 1 (k*b) (k*t)*F ((c:ℂ)+(t:ℂ)*I)) +
        ∫ t : ℝ, edge k (-1) (k*b) (k*t)*F ((c+Real.pi/k:ℝ)+(t:ℂ)*I) := by
  let a := ray c k ((c+b:ℝ):ℂ)
  have hi := (circleIntegrable_real_iff c k _ hs F).mp hF
  rw [circle_to_real c k _ hs F,real_rays hk _ hi]
  have hA : a = polarRay (k*b) 0 := by simpa [a] using ray_on_vertical c k b 0
  have haR : a.re = Real.cos (k*b) := by simp [hA,polarRay]
  have haI : a.im = Real.sin (k*b) := by simp [hA,polarRay]
  have one (side : ℝ) (hsign : side=1 ∨ side = -1) (t : ℝ) :
      k*Real.exp (-(k*t))*CayleyCauchy.density a.im (a.re-side*Real.exp (-(k*t))) =
        edge k side (k*b) (k*t) := by
    rw [haI,haR,CayleyCauchy.density,←edge_eq_pullback hsign]
    rw [sub_sq_comm (Real.cos (k*b)),add_comm ((Real.sin (k*b))^2)]
    ring
  congr 1
  · apply integral_congr_ae
    filter_upwards with t
    rw [unray_positive c hk,←mul_assoc,←one 1 (Or.inl rfl),one_mul]
  · apply integral_congr_ae
    filter_upwards with t
    rw [Complex.ofReal_neg,unray_negative c hk,←mul_assoc,←one (-1) (Or.inr rfl),neg_one_mul]

/-! ## Analytic continuation through the finite edges -/

def otherEnd (a : ℂ) := a/conj a

theorem norm_otherEnd {a : ℂ} (ha : 0 < a.im) : ‖otherEnd a‖=1 := by
  have hn : a ≠ 0 := by intro he; simp [he] at ha
  simp [otherEnd,hn]

private theorem upper_im_nonneg {a v : ℂ} (ha : 0 ≤ a.im) (hv : ‖v‖ ≤ 1) : 0 ≤ (upper a v).im := by
  by_cases h : 1-v=0
  · simp [upper,h]
  rw [upper_affine h,Complex.add_im,Complex.ofReal_im,zero_add,Complex.I_mul_im,Complex.re_ofReal_mul]
  apply mul_nonneg ha
  rw [Complex.div_re,←add_div]
  apply div_nonneg _ (Complex.normSq_nonneg _)
  simp only [Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,
    zero_add,zero_sub]
  have hs : Complex.normSq v ≤ 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg v]
  simp only [Complex.normSq_apply] at hs
  nlinarith

private theorem upper_ne_of_ends {a v : ℂ} (ha : 0 < a.im) (h1 : v ≠ 1) (he : v ≠ otherEnd a) : upper a v ≠ 0 := by
  have hn : a ≠ 0 := by intro eq; simp [eq] at ha
  have hc : conj a ≠ 0 := by simpa using hn
  apply div_ne_zero _ (sub_ne_zero.mpr h1.symm)
  intro h
  apply he
  apply (eq_div_iff hc).mpr
  rw [mul_comm,←sub_eq_zero.mp h]

/-- Total inverse agreeing everywhere on the closed disk with the physical principal-argument
chart. Its extension on the exterior uses one logarithm branch regular at both finite edges. -/
def chart (c k : ℝ) (s v : ℂ) : ℂ :=
  if upper (ray c k s) v = 0 then fromDisk c k s v else fromDiskAcross c k s v

theorem chart_closed {c k : ℝ} {s v : ℂ} (hs : InStrip c k s) (hv : ‖v‖ ≤ 1) :
    chart c k s v = fromDisk c k s v := by
  unfold chart
  split_ifs with hn
  · rfl
  · exact fromDiskAcross_eq (upper_im_nonneg (ray_im_pos hs).le hv) hn

private theorem rotated_slit {u : ℂ} (hu : 0 ≤ u.im) (hn : u ≠ 0) : -I*u ∈ slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  by_cases hp : 0 < u.im
  · left; simpa [Complex.mul_re] using hp
  · right
    have h0 := le_antisymm (le_of_not_gt hp) hu
    have hr : u.re ≠ 0 := fun h ↦ hn (Complex.ext (by simpa using h) (by simpa using h0))
    simpa [Complex.mul_im] using hr

private theorem upper_deriv_of_ne {a v : ℂ} (h : 1-v ≠ 0) :
    HasDerivAt (upper a) ((a-conj a)/(1-v)^2) v := by
  have h₁ := ((hasDerivAt_id v).const_mul (conj a)).const_sub a
  have h₂ := (hasDerivAt_id v).const_sub (1:ℂ)
  unfold upper
  convert h₁.div h₂ h using 1
  · rfl
  · dsimp; ring

/-- The extension is a local holomorphic coordinate, with nonzero derivative, on the closed
disk after precisely the two end points have been removed. -/
theorem chart_analytic_deriv {c k : ℝ} (hk : 0 < k) {s v : ℂ} (hs : InStrip c k s) (hv : ‖v‖ ≤ 1)
    (h1 : v ≠ 1) (h2 : v ≠ otherEnd (ray c k s)) :
    AnalyticAt ℂ (chart c k s) v ∧ deriv (chart c k s) v ≠ 0 := by
  let a := ray c k s
  let u := upper a v
  have ha : 0 < a.im := ray_im_pos hs
  have hj : 0 ≤ u.im := upper_im_nonneg ha.le hv
  have hn : u ≠ 0 := upper_ne_of_ends ha h1 h2
  have hden : 1-v ≠ 0 := sub_ne_zero.mpr h1.symm
  have hd := upper_deriv_of_ne (a:=a) hden
  have hag : fromDiskAcross c k s =ᶠ[𝓝 v] chart c k s := by
    filter_upwards [hd.continuousAt.eventually_ne hn] with v' hv'
    simp only [chart,a] at *
    simp only [hv',↓reduceIte]
  have du := (Complex.hasDerivAt_log (rotated_slit hj hn)).comp u ((hasDerivAt_id u).const_mul (-I))
  have dl := du.add_const ((Real.pi:ℂ)/2*I)
  have dl' : HasDerivAt logUp (((-I*u)⁻¹)*(-I)) u := by
    unfold logUp
    simpa only [Function.comp_apply,mul_one] using dl
  have dd := ((dl'.comp v hd).const_mul (-I/(k:ℂ))).const_add (c:ℂ)
  have dd' : HasDerivAt (fromDiskAcross c k s) _ v := dd
  have hgap : a-conj a ≠ 0 := by
    intro eq
    have hi := congrArg Complex.im (sub_eq_zero.mp eq)
    simp only [Complex.conj_im] at hi
    linarith
  have hdc : deriv (chart c k s) v = _ := (dd'.congr_of_eventuallyEq hag.symm).deriv
  refine ⟨(fromDiskAcross_analytic hden hj hn).congr hag,?_⟩
  rw [hdc]
  exact mul_ne_zero (div_ne_zero (neg_ne_zero.mpr I_ne_zero) (Complex.ofReal_ne_zero.mpr hk.ne'))
    (mul_ne_zero (mul_ne_zero (inv_ne_zero (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hn))
      (neg_ne_zero.mpr I_ne_zero)) (div_ne_zero hgap (pow_ne_zero _ hden)))

theorem chart_re_mem {c w : ℝ} (hw : 0 < w) {s v : ℂ} (hs : InStrip c (Real.pi/w) s) (hv : ‖v‖ ≤ 1) :
    c ≤ (chart c (Real.pi/w) s v).re ∧ (chart c (Real.pi/w) s v).re ≤ c+w := by
  let k := Real.pi/w
  let u := upper (ray c k s) v
  have hk : 0 < k := div_pos Real.pi_pos hw
  have hu : 0 ≤ u.im := upper_im_nonneg (ray_im_pos hs).le hv
  rw [chart_closed hs hv]
  have he : k*((unray c k u).re-c) = u.arg := by
    simp [unray,Complex.mul_re,Complex.div_ofReal_re,Complex.div_ofReal_im,Complex.log_im]
    field_simp
  have hl := (Complex.arg_nonneg_iff.mpr hu)
  have hr := Complex.arg_le_pi u
  have hkw : k*w = Real.pi := div_mul_cancel₀ _ hw.ne'
  change c ≤ (unray c k u).re ∧ (unray c k u).re ≤ c+w
  constructor
  · apply sub_nonneg.mp
    apply nonneg_of_mul_nonneg_right _ hk
    rwa [he]
  · have h : k*((unray c k u).re-c) ≤ k*w := by rwa [he,hkw]
    linarith only [(mul_le_mul_iff_right₀ hk).mp h]

/-! ## Physical edge coordinates -/

private theorem on_ray {k : ℝ} (hk : 0 < k) (H : ℝ → ℝ) (hI : Integrable H) :
    Integrable (fun t : ℝ ↦ k*Real.exp (-(k*t))*H (Real.exp (-(k*t)))) := by
  have he := (integrable_comp_exp H).mpr hI.integrableOn
  have hs := (he.comp_mul_left' (R := -k) (neg_ne_zero.mpr hk.ne')).const_mul k
  simpa only [neg_mul,smul_eq_mul,mul_assoc] using hs

/-- Circle integrability in the conformal coordinate implies ordinary absolute integrability
of each signed boundary integrand in its own vertical-height variable. -/
theorem edges_integrable {c k b : ℝ} (hk : 0 < k) (hs : InStrip c k ((c+b:ℝ):ℂ))
    (F : ℂ → ℝ) (hF : CircleIntegrable (fun v ↦ F (fromDisk c k ((c+b:ℝ):ℂ) v)) 0 1) :
    Integrable (fun t : ℝ ↦ edge k 1 (k*b) (k*t)*F ((c:ℂ)+(t:ℂ)*I)) ∧
    Integrable (fun t : ℝ ↦ edge k (-1) (k*b) (k*t)*F ((c+Real.pi/k:ℝ)+(t:ℂ)*I)) := by
  let a := ray c k ((c+b:ℝ):ℂ)
  let H := fun x : ℝ ↦ CayleyCauchy.density a.im (a.re-x)*F (unray c k (x:ℂ))
  have hi : Integrable H := (circleIntegrable_real_iff c k _ hs F).mp hF
  have hneg : Integrable (fun x ↦ H (-x)) := by simpa only [neg_one_mul] using hi.comp_mul_left' (R:=-1) (by norm_num)
  have hA : a = polarRay (k*b) 0 := by simpa [a] using ray_on_vertical c k b 0
  have haR : a.re=Real.cos (k*b) := by simp [hA,polarRay]
  have haI : a.im=Real.sin (k*b) := by simp [hA,polarRay]
  have one (side : ℝ) (h : side=1 ∨ side = -1) (t : ℝ) :
      k*Real.exp (-(k*t))*CayleyCauchy.density a.im (a.re-side*Real.exp (-(k*t))) = edge k side (k*b) (k*t) := by
    rw [haI,haR,CayleyCauchy.density,←edge_eq_pullback h]
    rw [sub_sq_comm (Real.cos (k*b)),add_comm ((Real.sin (k*b))^2)]
    ring
  constructor
  · apply (on_ray hk H hi).congr
    filter_upwards with t
    dsimp only [H]
    rw [unray_positive c hk,←mul_assoc,←one 1 (Or.inl rfl),one_mul]
  · apply (on_ray hk (fun x ↦ H (-x)) hneg).congr
    filter_upwards with t
    dsimp only [H]
    rw [Complex.ofReal_neg,unray_negative c hk,←mul_assoc,←one (-1) (Or.inr rfl),neg_one_mul]

end RiemannMasullo.StripJensen
