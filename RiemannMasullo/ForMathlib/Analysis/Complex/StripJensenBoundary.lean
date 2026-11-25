module

public import RiemannMasullo.ForMathlib.Analysis.Complex.StripJensenChart
public import RiemannMasullo.ForMathlib.Analysis.Complex.LogBoundaryMean
public import Mathlib.Analysis.Complex.Poisson
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Cardinality

/-! # Two exceptional ends in the logarithmic boundary trace

A holomorphic disk function may extend through finite boundary arcs yet lose logarithmic
mass at either of two exceptional points. Nontangential point evaluations at each end bound
this loss. The images of any fixed interior strip vertical give such probes. -/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory Metric Set
open scoped ComplexConjugate Topology

namespace RiemannMasullo.StripJensen

private theorem den_ne {a u : ℂ} (ha : 0 < a.im) (hu : 0 < u.im) : u-conj a ≠ 0 := by
  intro he
  have hi := congrArg Complex.im (sub_eq_zero.mp he)
  simp only [Complex.conj_im] at hi
  linarith

/-- The disk defect, without a trigonometric specialization of the upper-half-plane variable. -/
private theorem disk_gap_sq {a u : ℂ} (ha : 0 < a.im) (hu : 0 < u.im) :
    (1-‖disk a u‖^2)*‖u-conj a‖^2 = 4*u.im*a.im := by
  rw [disk,norm_div,div_pow]
  field_simp [norm_ne_zero_iff.mpr (den_ne ha hu)]
  simp only [←Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.conj_re,Complex.conj_im]
  ring

private theorem norm_bar_sub {a : ℂ} (ha : 0 ≤ a.im) : ‖conj a-a‖=2*a.im := by
  have he : conj a-a = -(2*a.im:ℝ)*I := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
    ring
  rw [he,norm_mul,Complex.norm_I,mul_one]
  simp [abs_of_nonneg ha]

/-- End distances in the disk. The two target points are one and a divided by its conjugate. -/
private theorem disk_end_distances {a u : ℂ} (ha : 0 < a.im) (hu : 0 < u.im) (hunit : ‖a‖=1) :
    ‖disk a u-1‖ = (2*a.im)/‖u-conj a‖ ∧
    ‖disk a u-a/conj a‖ = (2*‖u‖*a.im)/‖u-conj a‖ := by
  have han : a ≠ 0 := by intro h; simp [h] at ha
  have hbar : conj a ≠ 0 := by simpa using han
  have hn := den_ne ha hu
  have h₁ : disk a u-1=(conj a-a)/(u-conj a) := by
    rw [disk]; field_simp; ring
  have h₂ : disk a u-a/conj a=u*(conj a-a)/((u-conj a)*conj a) := by
    rw [disk]; field_simp; ring
  simp only [h₁,h₂,norm_mul,norm_div,Complex.norm_conj,hunit,mul_one,norm_bar_sub ha.le]
  constructor
  · trivial
  · ring

/-- A fixed interior ray makes a uniformly nontangential approach to both strip ends.
For the physical vertical line of angle alpha, use h = sin alpha. -/
private theorem disk_end_aperture {a u : ℂ} (ha : 0 < a.im) (hu : 0 < u.im) (hunit : ‖a‖=1)
    {h : ℝ} (hh : 0 < h) (huim : u.im = ‖u‖*h) :
    (1 ≤ ‖u‖ → ‖disk a u-1‖ ≤ (2/h)*(1-‖disk a u‖)) ∧
    (‖u‖ ≤ 1 → ‖disk a u-a/conj a‖ ≤ (2/h)*(1-‖disk a u‖)) := by
  let v := ‖disk a u‖
  let D := ‖u-conj a‖
  have hD : 0 < D := norm_pos_iff.mpr (den_ne ha hu)
  have hv : 0 ≤ v := norm_nonneg _
  have hv1 : v < 1 := disk_norm_lt hu ha
  have hd : D ≤ ‖u‖+1 := by simpa [D,hunit] using norm_sub_le u (conj a)
  have gap : ((1-v)*(1+v))*D^2 = 4*‖u‖*h*a.im := by
    calc _ = (1-v^2)*D^2 := by ring
      _ = 4*u.im*a.im := disk_gap_sq ha hu
      _ = _ := by rw [huim]; ring
  have main : 2*‖u‖*h*a.im ≤ (1-v)*D^2 := by
    have hle : 0 ≤ (1-v)*D^2*(1-v) := by positivity
    nlinarith only [gap,hle]
  obtain ⟨e₁,e₂⟩ := disk_end_distances ha hu hunit
  constructor
  · intro hU
    rw [e₁]
    change 2*a.im / D ≤ (2/h)*(1-v)
    rw [div_mul_eq_mul_div,div_le_div_iff₀ hD hh]
    have hdu : D ≤ 2*‖u‖ := by linarith
    have hmul := mul_le_mul_of_nonneg_right hdu (mul_nonneg hh.le ha.le)
    have bound : D*(h*a.im) ≤ (1-v)*D^2 := by linarith only [hmul,main]
    have hle := (mul_le_mul_iff_left₀ hD).mp (show h*a.im*D ≤ (1-v)*D*D by nlinarith only [bound])
    linarith
  · intro hU
    rw [e₂]
    change 2*‖u‖*a.im / D ≤ (2/h)*(1-v)
    rw [div_mul_eq_mul_div,div_le_div_iff₀ hD hh]
    have hdu : D ≤ 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hdu (show 0 ≤ ‖u‖*h*a.im by positivity)
    have bound : D*(‖u‖*h*a.im) ≤ (1-v)*D^2 := by linarith only [hmul,main]
    have hle := (mul_le_mul_iff_left₀ hD).mp (show ‖u‖*h*a.im*D ≤ (1-v)*D*D by nlinarith only [bound])
    linarith

/-- A nontangential interior probe controls the Poisson kernel on a whole boundary arc. -/
private theorem poissonKernel_end_arc {z ξ : ℂ} {A r : ℝ} (hA : 0 ≤ A)
    (hq : 1/2 ≤ ‖z‖) (hq1 : ‖z‖ < 1) (hqr : (1+‖z‖)/2 ≤ r) (hr : r ≤ 1)
    (hcone : ‖z-ξ‖ ≤ A*(1-‖z‖)) {θ : ℝ} (harc : ‖circleMap 0 1 θ-ξ‖ ≤ 1-‖z‖) :
    1/(2*(A+2)^2*(1-‖z‖)) ≤ poissonKernel 0 z (circleMap 0 r θ) := by
  let q := ‖z‖
  have hq0 : 0 ≤ q := norm_nonneg _
  have hq' : q < r := by dsimp only [q]; linarith
  have hr0 := hq0.trans hq'.le
  have hn : 0 < ‖circleMap 0 r θ-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr fun he ↦
    hq'.ne (by simpa [q,norm_circleMap_zero,abs_of_nonneg hr0] using (congrArg norm he).symm))
  have hrad : ‖circleMap 0 r θ-circleMap 0 1 θ‖ = 1-r := by
    simp only [circleMap_zero,←sub_mul,←Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      Complex.norm_exp,Complex.mul_I_re,Complex.ofReal_im,neg_zero,Real.exp_zero,mul_one]
    rw [abs_of_nonpos (sub_nonpos.mpr hr)]; ring
  have hd : ‖circleMap 0 r θ-z‖ ≤ (A+2)*(1-q) := calc
    _ ≤ ‖circleMap 0 r θ-circleMap 0 1 θ‖+‖circleMap 0 1 θ-z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (1-r)+(‖circleMap 0 1 θ-ξ‖+‖z-ξ‖) := by rw [hrad,norm_sub_rev z ξ]; gcongr; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (1-r)+((1-q)+A*(1-q)) := by gcongr
    _ ≤ _ := by linarith
  have hnum : (1-q)/2 ≤ r^2-q^2 := calc
    _ ≤ r-q := by dsimp only [q] at *; linarith
    _ ≤ (r-q)*(r+q) := le_mul_of_one_le_right (by linarith) (by dsimp only [q] at *; linarith)
    _ = _ := by ring
  have hg : 0 < 1-q := sub_pos.mpr hq1
  have hC : 0 < 2*(A+2)^2 := by positivity
  have hd2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
  simp only [poissonKernel_def,sub_zero,norm_circleMap_zero,abs_of_nonneg hr0]
  change 1/(2*(A+2)^2*(1-q)) ≤ (r^2-q^2)/‖circleMap 0 r θ-z‖^2
  apply (div_le_div_iff₀ (mul_pos hC hg) (sq_pos_of_pos hn)).mpr
  have hh := mul_le_mul_of_nonneg_right hnum (mul_pos hC hg).le
  nlinarith only [hd2,hh]

/-! ## Approaches along an interior vertical -/

def site (c x t : ℝ) : ℂ := ((c+x:ℝ):ℂ)+(t:ℂ)*I

theorem site_mem {c k x : ℝ} (hx : 0 < k*x ∧ k*x < Real.pi) (t : ℝ) : InStrip c k (site c x t) := by
  simpa [site,InStrip,Complex.add_re] using hx

private theorem norm_polarRay (x t : ℝ) : ‖polarRay x t‖=Real.exp (-t) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  simp only [polarRay]
  linear_combination (Real.exp (-t))^2*Real.sin_sq_add_cos_sq x

private theorem disk_dist_bounds {a u : ℂ} (ha : 0 < a.im) (hu : 0 < u.im) (hunit : ‖a‖=1)
    {h : ℝ} (hh : 0 < h) (huim : u.im=‖u‖*h) :
    ‖disk a u-a/conj a‖ ≤ 2*‖u‖ ∧ ‖disk a u-1‖ ≤ (2*a.im/h)/‖u‖ := by
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr (by intro eq; simp [eq] at hu)
  have he := Complex.abs_im_le_norm (u-conj a)
  rw [Complex.sub_im,Complex.conj_im,sub_neg_eq_add,abs_of_pos (add_pos hu ha)] at he
  have dpos : 0 < ‖u-conj a‖ := (add_pos hu ha).trans_le he
  obtain ⟨one,other⟩ := disk_end_distances ha hu hunit
  constructor
  · rw [other,div_le_iff₀ dpos]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · rw [one,div_div,div_le_div_iff₀ dpos (mul_pos hh hnorm)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [mul_comm,←huim]
    linarith

/-- The two heights on the same vertical are within a constant times exp(-k t) of their
respective distinct ends. The cone aperture is 2/sin(k*x). -/
theorem physical_probes {c k b x : ℝ} (hk : 0 < k)
    (hb : 0 < k*b ∧ k*b < Real.pi) (hx : 0 < k*x ∧ k*x < Real.pi)
    (t : ℝ) (ht : 0 ≤ t) :
    let s : ℂ := ((c+b:ℝ):ℂ)
    let a := ray c k s
    let vp := toDisk c k s (site c x t)
    let vm := toDisk c k s (site c x (-t))
    let ep := a/conj a
    let h := Real.sin (k*x)
    ‖vp‖ < 1 ∧ ‖vm‖ < 1 ∧
    ‖vp-ep‖ ≤ 2*Real.exp (-(k*t)) ∧ ‖vm-1‖ ≤ (2*a.im/h)*Real.exp (-(k*t)) ∧
    ‖vp-ep‖ ≤ (2/h)*(1-‖vp‖) ∧ ‖vm-1‖ ≤ (2/h)*(1-‖vm‖) := by
  intro s a vp vm ep h
  have hs : InStrip c k s := by simpa [s,InStrip] using hb
  have ha : 0 < a.im := ray_im_pos hs
  have he (y : ℝ) : ray c k (site c x y) = polarRay (k*x) (k*y) := ray_on_vertical _ _ _ _
  have hbase : a=polarRay (k*b) 0 := by simpa only [s,a,Complex.ofReal_zero,zero_mul,add_zero,mul_zero] using ray_on_vertical c k b 0
  have hunit : ‖a‖=1 := by rw [hbase,norm_polarRay,neg_zero,Real.exp_zero]
  have hh : 0 < h := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have one (y : ℝ) : (ray c k (site c x y)).im=‖ray c k (site c x y)‖*h := by rw [he,norm_polarRay]; rfl
  have gt (y : ℝ) : 0 < (ray c k (site c x y)).im := ray_im_pos (site_mem hx _)
  have ap (y : ℝ) := disk_end_aperture ha (gt y) hunit hh (one y)
  have ds (y : ℝ) := disk_dist_bounds ha (gt y) hunit hh (one y)
  have plus : ‖ray c k (site c x t)‖=Real.exp (-(k*t)) := by rw [he,norm_polarRay]
  have minus : ‖ray c k (site c x (-t))‖=Real.exp (k*t) := by rw [he,norm_polarRay,mul_neg,neg_neg]
  refine ⟨toDisk_lt hs (site_mem hx _),toDisk_lt hs (site_mem hx _),?_,?_,?_,?_⟩
  · change ‖disk a (ray c k (site c x t))-a/conj a‖ ≤ _
    simpa only [plus] using (ds t).1
  · change ‖disk a (ray c k (site c x (-t)))-1‖ ≤ _
    simpa only [minus,Real.exp_neg,div_eq_mul_inv] using (ds (-t)).2
  · apply (ap t).2
    rw [plus,Real.exp_le_one_iff]
    linarith [mul_nonneg hk.le ht]
  · apply (ap (-t)).1
    rw [minus,Real.one_le_exp_iff]
    exact mul_nonneg hk.le ht

theorem exp_decay_nat {k : ℝ} (hk : 0 < k) : Tendsto (fun n : ℕ ↦ Real.exp (-(k*(n:ℝ)))) atTop (𝓝 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-k)).le
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hk))
  apply h.congr
  intro n
  rw [show -(k*(n:ℝ)) = (n:ℝ)*(-k) by ring,Real.exp_nat_mul]

/-- A positive scale decreasing to zero can fit any prescribed positive sequence of radii. -/
theorem exists_shrinking_scale (D : ℕ → ℝ) (hD : ∀ j, 0 < D j) :
    ∃ d : ℕ → ℝ, (∀ j, 0 < d j) ∧ Antitone d ∧ Tendsto d atTop (𝓝 0) ∧ ∀ j, d j ≤ D j := by
  let d : ℕ → ℝ := fun n ↦ Nat.rec (min 1 (D 0)) (fun j a ↦ min (a/2) (D (j+1))) n
  have zero : d 0 = min 1 (D 0) := rfl
  have succ (j : ℕ) : d (j+1) = min (d j/2) (D (j+1)) := rfl
  have hp (j : ℕ) : 0 < d j := by
    induction j with
    | zero => rw [zero]; exact lt_min zero_lt_one (hD _)
    | succ j ih => rw [succ]; exact lt_min (half_pos ih) (hD _)
  have hqu (j : ℕ) : d (j+1) ≤ d j/2 := succ j ▸ min_le_left _ _
  have ha := antitone_nat_of_succ_le (f:=d) (fun j ↦ (hqu j).trans (by linarith [hp j]))
  have hpow (j : ℕ) : d j ≤ (1/2:ℝ)^j := by
    induction j with
    | zero => rw [zero,pow_zero]; exact min_le_left _ _
    | succ j ih => rw [pow_succ]; linarith [hqu j]
  have hd := squeeze_zero (fun j ↦ (hp j).le) hpow
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num))
  exact ⟨d,hp,ha,hd,fun j ↦ by cases j with
    | zero => rw [zero]; exact min_le_right _ _
    | succ j => rw [succ]; exact min_le_right _ _⟩

/-! ## Logarithmic boundary traces -/

abbrev angleMeasure : Measure ℝ := volume.restrict (Ioc 0 (2*Real.pi))

def away (p q : ℂ) (δ : ℝ) : Set ℝ :=
  {θ | δ < ‖circleMap 0 1 θ-p‖ ∧ δ < ‖circleMap 0 1 θ-q‖}

def loss (f : ℂ → ℂ) (r θ : ℝ) : ℝ := -Real.log ‖f (circleMap 0 r θ)‖

private theorem away_measurable (p q : ℂ) (δ : ℝ) : MeasurableSet (away p q δ) :=
  (isOpen_lt continuous_const (by fun_prop : Continuous (fun θ ↦ ‖circleMap 0 1 θ-p‖))).measurableSet.inter
    (isOpen_lt continuous_const (by fun_prop : Continuous (fun θ ↦ ‖circleMap 0 1 θ-q‖))).measurableSet

private theorem radial_dist (r θ : ℝ) : ‖circleMap 0 r θ-circleMap 0 1 θ‖=|r-1| := by
  simp only [circleMap_zero,←sub_mul,←Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_exp,Complex.mul_I_re,Complex.ofReal_im,neg_zero,Real.exp_zero,mul_one]

/-- On every compact arc avoiding both ends, finite-order analyticity implies angular L1
convergence, allowing ordinary finite-edge zeros. -/
private theorem radial_log_local_two (p q : ℂ) {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ p → z ≠ q → AnalyticAt ℂ f z ∧ meromorphicOrderAt f z ≠ ⊤)
    {r : ℕ → ℝ} (ht : Tendsto r atTop (𝓝 1)) (hmax : ∀ᶠ n in atTop, r n ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (loss f 1) (away p q δ) angleMeasure ∧
      Tendsto (fun n ↦ ∫ θ in away p q δ, |loss f (r n) θ-loss f 1 θ| ∂angleMeasure) atTop (𝓝 0) := by
  let K := (closedBall (0:ℂ) 1 ∩ {z : ℂ | δ/2 ≤ ‖z-p‖}) ∩ {z : ℂ | δ/2 ≤ ‖z-q‖}
  have hK : IsCompact K := ((isCompact_closedBall (0:ℂ) 1).inter_right
    (isClosed_le continuous_const (by fun_prop))).inter_right (isClosed_le continuous_const (by fun_prop))
  have hK1 : K ⊆ closedBall 0 1 := fun _ hz ↦ hz.1.1
  have hne {z e : ℂ} (h : δ/2 ≤ ‖z-e‖) : z ≠ e := by
    rintro rfl
    rw [sub_self,norm_zero] at h
    linarith
  have hA : AnalyticOnNhd ℂ f K := fun z hz ↦ (hf z (mem_closedBall_zero_iff.mp hz.1.1) (hne hz.1.2) (hne hz.2)).1
  have ho (z : K) : meromorphicOrderAt f z ≠ ⊤ :=
    (hf z (mem_closedBall_zero_iff.mp z.property.1.1) (hne z.property.1.2) (hne z.property.2)).2
  obtain ⟨B,hB,henv⟩ := PoissonBoundary.exists_integrableOn_radial_log_envelope hK hK1 hA ho
  let A := away p q δ
  let μ := angleMeasure.restrict A
  have hAm : MeasurableSet A := away_measurable p q δ
  have hAe : ∀ᵐ θ ∂μ, θ ∈ A := ae_restrict_mem hAm
  have hgood (t : ℝ) (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hh : |t-1| ≤ δ/2) :
      MapsTo (circleMap 0 t) A K := by
    intro θ hθ
    have one (e : ℂ) (he : δ < ‖circleMap 0 1 θ-e‖) : δ/2 ≤ ‖circleMap 0 t θ-e‖ := by
      have h := norm_sub_le_norm_sub_add_norm_sub (circleMap 0 1 θ) (circleMap 0 t θ) e
      rw [norm_sub_rev (circleMap 0 1 θ) (circleMap 0 t θ),radial_dist] at h
      linarith
    exact ⟨⟨mem_closedBall_zero_iff.mpr (by rw [norm_circleMap_zero,abs_of_nonneg (by linarith)]; exact ht1),
      one p hθ.1⟩,one q hθ.2⟩
  have good1 := hgood 1 (by norm_num) le_rfl (by simp; positivity)
  have hnear : ∀ᶠ n in atTop, 1/2 ≤ r n ∧ r n ≤ 1 ∧ |r n-1| ≤ δ/2 := by
    have hc := Metric.tendsto_nhds.mp ht (δ/2) (by positivity)
    simp only [Real.dist_eq] at hc
    exact (ht.eventually (le_mem_nhds (by norm_num : (1/2:ℝ)<1))).and (hmax.and (hc.mono fun _ h ↦ h.le))
  have measurable (t : ℝ) (hm : MapsTo (circleMap 0 t) A K) : AEStronglyMeasurable (loss f t) μ :=
    (Real.measurable_log.comp_aemeasurable ((hA.continuousOn.comp
      (continuous_circleMap 0 t).continuousOn hm).aemeasurable hAm).norm).neg.aestronglyMeasurable
  have bound (t : ℝ) (h0 : 1/2 ≤ t) (h1 : t ≤ 1) (hm : MapsTo (circleMap 0 t) A K) :
      ∀ᵐ θ ∂μ, ‖loss f t θ‖ ≤ B θ := by
    filter_upwards [hAe,ae_restrict_of_ae (ae_restrict_of_ae (henv t h0 h1))] with θ hm' hb
    simpa only [loss,Real.norm_eq_abs,abs_neg] using hb (hm hm')
  have hbμ : Integrable B μ := (show Integrable B angleMeasure from hB).restrict
  have hb1 := bound 1 (by norm_num) le_rfl good1
  refine ⟨hbμ.mono' (measurable 1 good1) hb1,?_⟩
  let D := MeromorphicOn.divisor f K
  have hz : ∀ᵐ θ ∂μ, circleMap 0 1 θ ∉ D.support :=
    ae_restrict_of_ae (ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp
      (((D.finiteSupport hK).countable.preimage_circleMap 0 one_ne_zero).measure_zero volume)))
  have htθ : ∀ᵐ θ ∂μ, Tendsto (fun n ↦ |loss f (r n) θ-loss f 1 θ|) atTop (𝓝 0) := by
    filter_upwards [hAe,hz] with θ hθ hD
    have hzK := good1 hθ
    have hzD : D (circleMap 0 1 θ) = 0 := not_ne_iff.mp hD
    change MeromorphicOn.divisor f K (circleMap 0 1 θ) = 0 at hzD
    rw [hA.meromorphicOn.divisor_apply hzK,WithTop.untop₀_eq_zero] at hzD
    have hfn := (hA _ hzK).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp (hzD.resolve_right (ho ⟨_,hzK⟩))
    have hp : Tendsto (fun n ↦ circleMap 0 (r n) θ) atTop (𝓝 (circleMap 0 1 θ)) := by
      simp only [circleMap_zero]
      exact ((Complex.continuous_ofReal.tendsto 1).comp ht).mul tendsto_const_nhds
    have hlog : Tendsto (fun n ↦ loss f (r n) θ) atTop (𝓝 (loss f 1 θ)) :=
      (((hA _ hzK).continuousAt.tendsto.comp hp).norm.log (norm_ne_zero_iff.mpr hfn)).neg
    simpa using (hlog.sub_const (loss f 1 θ)).abs
  have hh := tendsto_integral_filter_of_dominated_convergence (μ:=μ)
    (F:=fun n θ ↦ |loss f (r n) θ-loss f 1 θ|) (f:=fun _ ↦ (0:ℝ)) (fun θ ↦ B θ+B θ)
    (hnear.mono fun n h ↦ ((measurable _ (hgood _ h.1 h.2.1 h.2.2)).sub (measurable 1 good1)).norm)
    (by
      filter_upwards [hnear] with n hn
      filter_upwards [bound _ hn.1 hn.2.1 (hgood _ hn.1 hn.2.1 hn.2.2),hb1] with θ he he'
      simpa only [Real.norm_eq_abs,abs_abs] using (norm_sub_le _ _).trans (add_le_add he he'))
    (hbμ.add hbμ) htθ
  simpa only [integral_zero] using hh

/-- Mass tightness in two shrinking end arcs suffices to recover the full trace, including
the boundary integrability. The holomorphic function may vanish at ordinary boundary points. -/
private theorem two_end_trace (p q : ℂ) {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ p → z ≠ q → AnalyticAt ℂ f z ∧ meromorphicOrderAt f z ≠ ⊤)
    (hb : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f z‖ ≤ 1)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n ∧ r n < 1) (ht : Tendsto r atTop (𝓝 1))
    (δ : ℕ → ℝ) (hd : ∀ j, 0 < δ j) (hanti : Antitone δ) (hd0 : Tendsto δ atTop (𝓝 0))
    (hbound : ∃ B : ℝ, ∀ᶠ n in atTop, Integrable (loss f (r n)) angleMeasure ∧
      (∫ θ, loss f (r n) θ ∂angleMeasure) ≤ B)
    (v : ℕ → ℝ) (hv : Tendsto v atTop (𝓝 0))
    (htail : ∀ j, ∀ᶠ n in atTop, (∫ θ in (away p q (δ j))ᶜ, loss f (r n) θ ∂angleMeasure) ≤ v j) :
    CircleIntegrable (fun z ↦ Real.log ‖f z‖) 0 1 ∧
      Tendsto (fun n ↦ Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 (r n)) atTop
        (𝓝 (Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 1)) := by
  let S := fun j ↦ away p q (δ j)
  have hmono : Monotone S := fun i j hij θ hθ ↦
    ⟨lt_of_le_of_lt (hanti hij) hθ.1,lt_of_le_of_lt (hanti hij) hθ.2⟩
  have hcover : ∀ᵐ θ ∂angleMeasure, θ ∈ ⋃ j, S j := by
    have good (a : ℂ) : ∀ᵐ θ ∂angleMeasure, circleMap 0 1 θ ≠ a :=
      ae_restrict_of_ae (((countable_singleton a).preimage_circleMap 0 (one_ne_zero : (1:ℝ)≠0)).ae_notMem volume)
    filter_upwards [good p,good q] with θ hp hq
    obtain ⟨j,hjp,hjq⟩ := ((hd0.eventually (eventually_lt_nhds (norm_pos_iff.mpr (sub_ne_zero.mpr hp)))).and
      (hd0.eventually (eventually_lt_nhds (norm_pos_iff.mpr (sub_ne_zero.mpr hq))))).exists
    exact mem_iUnion.mpr ⟨j,hjp,hjq⟩
  have hnon (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (θ : ℝ) : 0 ≤ loss f t θ :=
    neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) (hb _ (by rw [norm_circleMap_zero,abs_of_nonneg ht0]; exact ht1)))
  obtain ⟨hI,_,hm⟩ := PoissonBoundary.integrable_tendsto_of_exhaustion angleMeasure S
    (fun j ↦ away_measurable p q _) hmono hcover (fun n ↦ loss f (r n)) (loss f 1)
    (fun n ↦ .of_forall (hnon _ (hr n).1.le (hr n).2.le)) (.of_forall (hnon 1 zero_le_one le_rfl))
    hbound (fun j ↦ radial_log_local_two p q hf ht (.of_forall fun n ↦ (hr n).2.le) (hd j)) v hv htail
  constructor
  · apply (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr
    change Integrable (fun θ ↦ Real.log ‖f (circleMap 0 1 θ)‖) angleMeasure
    simpa only [loss,neg_neg] using (show Integrable (fun θ ↦ -loss f 1 θ) angleMeasure from hI.neg)
  · have hmean (t : ℝ) : Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 t =
         (2*Real.pi)⁻¹ * -(∫ θ, loss f t θ ∂angleMeasure) := by
      simp only [Real.circleAverage_def,intervalIntegral.integral_of_le Real.two_pi_pos.le,smul_eq_mul,loss,
        integral_neg,neg_neg]
    simp_rw [hmean]
    exact hm.neg.const_mul _

/-! ## Defect bounds at the two ends -/

/-- Interior probes for one exceptional boundary point. The normalized logarithmic loss
vanishes along the probes, and each chordal arc of the prescribed scale fits inside its probe. -/
structure EndApproach (f : ℂ → ℂ) (e : ℂ) (δ : ℕ → ℝ) where
  point : ℕ → ℂ
  aperture : ℝ
  aperture_nonneg : 0 ≤ aperture
  lower : ∀ j, 1/2 ≤ ‖point j‖
  inside : ∀ j, ‖point j‖ < 1
  fits : ∀ j, δ j ≤ 1-‖point j‖
  cone : ∀ j, ‖point j-e‖ ≤ aperture*(1-‖point j‖)
  nonzero : ∀ j, f (point j) ≠ 0
  negligible : Tendsto (fun j ↦ (1-‖point j‖)*|Real.log ‖f (point j)‖|) atTop (𝓝 0)

private def radialKernel (r : ℝ) (z : ℂ) (θ : ℝ) := poissonKernel 0 z (circleMap 0 r θ)

private theorem radialKernel_nonneg {z : ℂ} {r : ℝ} (hz : ‖z‖ ≤ r) (θ : ℝ) :
    0 ≤ radialKernel r z θ := by
  simp only [radialKernel,poissonKernel_def,sub_zero,norm_circleMap_zero,abs_of_nonneg ((norm_nonneg z).trans hz)]
  exact div_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) hz 2)) (sq_nonneg _)

private theorem angular_budget {f : ℂ → ℂ} {r : ℝ} {z : ℂ} (hz : ‖z‖ < r)
    (ha : AnalyticOnNhd ℂ f (closedBall 0 r)) (hn : f z ≠ 0) (hs : ∀ v ∈ sphere 0 r, f v ≠ 0) :
    Integrable (fun θ ↦ radialKernel r z θ * loss f r θ) angleMeasure ∧
    (∫ θ, radialKernel r z θ * loss f r θ ∂angleMeasure) ≤ (2*Real.pi)*|Real.log ‖f z‖| := by
  have hqin := mem_ball_zero_iff.mpr hz
  have hr := (norm_nonneg _).trans_lt hz
  have hP : ContinuousOn (poissonKernel 0 z) (sphere 0 r) := by
    change ContinuousOn (fun v : ℂ ↦ poissonKernel 0 z v) _
    simp only [poissonKernel_def,sub_zero]
    apply ((continuous_norm.pow 2).sub continuous_const).continuousOn.div ((continuous_id.sub continuous_const).norm.pow 2).continuousOn
    intro v hv
    apply pow_ne_zero 2
    apply norm_ne_zero_iff.mpr
    apply sub_ne_zero.mpr
    change v ≠ z
    intro he
    exact hz.ne (he ▸ mem_sphere_zero_iff_norm.mp hv)
  have hlog := ((ha.continuousOn.mono sphere_subset_closedBall).norm.log (fun v hv ↦ norm_ne_zero_iff.mpr (hs v hv))).neg
  have hI := (hP.mul hlog).circleIntegrable hr.le
  have hcmp := RiemannMasullo.log_norm_le_circleAverage_poisson_of_boundary_nonzero hqin ha hn hs
  have hpos : Real.circleAverage (fun v ↦ poissonKernel 0 z v * -Real.log ‖f v‖) 0 r =
      -Real.circleAverage (poissonKernel 0 z • (fun v ↦ Real.log ‖f v‖)) 0 r := by
    simp only [Real.circleAverage_def,smul_eq_mul,Pi.mul_apply,mul_neg,intervalIntegral.integral_neg]
  have hh := hpos.le.trans ((neg_le_neg hcmp).trans (neg_le_abs _))
  have hdiv : (∫ θ, radialKernel r z θ*loss f r θ ∂angleMeasure)/(2*Real.pi) ≤ |Real.log ‖f z‖| := by
    simpa only [Real.circleAverage_def,intervalIntegral.integral_of_le Real.two_pi_pos.le,
      smul_eq_mul,radialKernel,loss,div_eq_inv_mul] using hh
  exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hI,
    (div_le_iff₀ Real.two_pi_pos).mp hdiv |>.trans_eq (mul_comm _ _)⟩

private theorem arc_pair_bound {f : ℂ → ℂ} {p q : ℂ} {d : ℕ → ℝ}
    (X : EndApproach f p d) (Y : EndApproach f q d) (j : ℕ) {r : ℝ} (hr : r ≤ 1)
    (hx : (1+‖X.point j‖)/2 ≤ r) (hy : (1+‖Y.point j‖)/2 ≤ r)
    (hi : Integrable (loss f r) angleMeasure) (hn : ∀ θ, 0 ≤ loss f r θ)
    (hX : Integrable (fun θ ↦ radialKernel r (X.point j) θ*loss f r θ) angleMeasure)
    (hY : Integrable (fun θ ↦ radialKernel r (Y.point j) θ*loss f r θ) angleMeasure) :
    let C (A : ℝ) (z : ℂ) := 2*(A+2)^2*(1-‖z‖)
    (∫ θ in (away p q (d j))ᶜ, loss f r θ ∂angleMeasure) ≤
      C X.aperture (X.point j)*(∫ θ, radialKernel r (X.point j) θ*loss f r θ ∂angleMeasure) +
      C Y.aperture (Y.point j)*(∫ θ, radialKernel r (Y.point j) θ*loss f r θ ∂angleMeasure) := by
  intro C
  let W (A : ℝ) (z : ℂ) (θ : ℝ) := C A z*(radialKernel r z θ*loss f r θ)
  have hpos {e : ℂ} (E : EndApproach f e d) : 0 < C E.aperture (E.point j) := by
    dsimp only [C]
    exact mul_pos (by positivity [E.aperture_nonneg]) (sub_pos.mpr (E.inside j))
  have hW {e : ℂ} (E : EndApproach f e d) (he : (1+‖E.point j‖)/2 ≤ r) (θ : ℝ) :
      0 ≤ W E.aperture (E.point j) θ := by
    have hle := E.inside j
    exact mul_nonneg (hpos E).le (mul_nonneg (radialKernel_nonneg (by linarith) θ) (hn θ))
  have hloc {e : ℂ} (E : EndApproach f e d) (he : (1+‖E.point j‖)/2 ≤ r) (θ : ℝ)
      (hθ : ‖circleMap 0 1 θ-e‖ ≤ d j) : loss f r θ ≤ W E.aperture (E.point j) θ := by
    have h := poissonKernel_end_arc E.aperture_nonneg (E.lower j) (E.inside j) he hr (E.cone j)
      (hθ.trans (E.fits j))
    have hh := (div_le_iff₀ (hpos E)).mp h
    change 1 ≤ radialKernel r (E.point j) θ*C E.aperture (E.point j) at hh
    calc loss f r θ = 1*loss f r θ := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hh (hn θ)
      _ = _ := by unfold W; ring
  let H := fun θ ↦ W X.aperture (X.point j) θ+W Y.aperture (Y.point j) θ
  have hW₁ := hX.const_mul (C X.aperture (X.point j))
  have hW₂ := hY.const_mul (C Y.aperture (Y.point j))
  have hHi : Integrable H angleMeasure := hW₁.add hW₂
  let S := (away p q (d j))ᶜ
  have hSm : MeasurableSet S := (away_measurable p q (d j)).compl
  calc (∫ θ in S, loss f r θ ∂angleMeasure) ≤ ∫ θ in S, H θ ∂angleMeasure := by
        apply integral_mono_ae hi.integrableOn hHi.integrableOn
        filter_upwards [ae_restrict_mem hSm] with θ hθ
        have hn' : ¬(d j < ‖circleMap 0 1 θ-p‖ ∧ d j < ‖circleMap 0 1 θ-q‖) := hθ
        by_cases hp : d j < ‖circleMap 0 1 θ-p‖
        · exact (hloc Y hy θ (le_of_not_gt (fun h ↦ hn' ⟨hp,h⟩))).trans (le_add_of_nonneg_left (hW X hx θ))
        · exact (hloc X hx θ (le_of_not_gt hp)).trans (le_add_of_nonneg_right (hW Y hy θ))
       _ ≤ ∫ θ, H θ ∂angleMeasure := setIntegral_le_integral hHi (.of_forall (fun θ ↦ add_nonneg (hW X hx θ) (hW Y hy θ)))
       _ = _ := by dsimp only [H,W]; rw [integral_add hW₁ hW₂,integral_const_mul,integral_const_mul]

/-- A bounded disk function analytic with finite order at all but two boundary points has
the full circle trace if nontangential evaluations lose sublinear logarithmic mass at both. -/
theorem circle_trace_of_endApproaches {f : ℂ → ℂ} {p q : ℂ} (hp : ‖p‖=1) (hq : ‖q‖=1)
    (hf : ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ p → z ≠ q → AnalyticAt ℂ f z ∧ meromorphicOrderAt f z ≠ ⊤)
    (hb : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f z‖ ≤ 1) (h0 : f 0 ≠ 0)
    (d : ℕ → ℝ) (hd : ∀ j, 0 < d j) (hanti : Antitone d) (hd0 : Tendsto d atTop (𝓝 0))
    (X : EndApproach f p d) (Y : EndApproach f q d) :
    CircleIntegrable (fun z ↦ Real.log ‖f z‖) 0 1 ∧
      ∃ r : ℕ → ℝ, (∀ n, 0 < r n ∧ r n < 1) ∧ Tendsto r atTop (𝓝 1) ∧
         Tendsto (fun n ↦ Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 (r n)) atTop
           (𝓝 (Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 1)) := by
  classical
  have hdom {z : ℂ} (hz : z ∈ ball 0 1) := hf z (mem_ball_zero_iff.mp hz).le
    (fun he ↦ (mem_ball_zero_iff.mp hz).ne (he ▸ hp)) (fun he ↦ (mem_ball_zero_iff.mp hz).ne (he ▸ hq))
  have hA : AnalyticOnNhd ℂ f (ball 0 1) := fun _ hz ↦ (hdom hz).1
  let D := MeromorphicOn.divisor f (ball 0 1)
  have hc : D.support.Countable := (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete D.discreteSupport
  obtain ⟨r,_,hr,ht⟩ := ((hc.image fun z : ℂ ↦ ‖z‖).dense_compl ℝ).exists_seq_strictMono_tendsto_of_lt
    (by norm_num : (1/2:ℝ)<1)
  have hr' (n : ℕ) : 0 < r n ∧ r n < 1 := ⟨lt_trans (by norm_num) (hr n).1.1,(hr n).1.2⟩
  have ha (n : ℕ) := hA.mono (closedBall_subset_ball (hr' n).2)
  have hnz (n : ℕ) (z : ℂ) (hz : z ∈ sphere 0 (r n)) : f z ≠ 0 := by
    have hz' := closedBall_subset_ball (hr' n).2 (sphere_subset_closedBall hz)
    have hn : z ∉ D.support := fun h ↦ (hr n).2 ⟨z,h,mem_sphere_zero_iff_norm.mp hz⟩
    have hzero : D z=0 := not_ne_iff.mp hn
    change MeromorphicOn.divisor f (ball 0 1) z=0 at hzero
    rw [hA.meromorphicOn.divisor_apply hz',WithTop.untop₀_eq_zero] at hzero
    exact (hA z hz').meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp (hzero.resolve_right (hdom hz').2)
  have hglob (n : ℕ) : Integrable (loss f (r n)) angleMeasure ∧
      (∫ θ, loss f (r n) θ ∂angleMeasure) ≤ (2*Real.pi)*|Real.log ‖f 0‖| := by
    have h := angular_budget (z:=0) (by simpa using (hr' n).1) (ha n) h0 (hnz n)
    have hk (θ : ℝ) : radialKernel (r n) 0 θ = 1 := by
      simp [radialKernel,poissonKernel_def,norm_circleMap_zero,(hr' n).1.ne']
    simpa only [hk,one_mul] using h
  have hnon (n : ℕ) (θ : ℝ) : 0 ≤ loss f (r n) θ :=
    neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) (hb _ (by rw [norm_circleMap_zero,abs_of_pos (hr' n).1]; exact (hr' n).2.le)))
  let v {e : ℂ} (E : EndApproach f e d) (j : ℕ) :=
    2*(E.aperture+2)^2*(2*Real.pi)*((1-‖E.point j‖)*|Real.log ‖f (E.point j)‖|)
  have hv {e : ℂ} (E : EndApproach f e d) : Tendsto (v E) atTop (𝓝 0) := by
    simpa only [v,mul_zero] using E.negligible.const_mul (2*(E.aperture+2)^2*(2*Real.pi))
  have htail (j : ℕ) : ∀ᶠ n in atTop, (∫ θ in (away p q (d j))ᶜ, loss f (r n) θ ∂angleMeasure) ≤ v X j+v Y j := by
    have late {e : ℂ} (E : EndApproach f e d) : ∀ᶠ n in atTop, (1+‖E.point j‖)/2 ≤ r n :=
      ht.eventually (eventually_ge_nhds (by linarith [E.inside j]))
    filter_upwards [late X,late Y] with n hx hy
    have one {e : ℂ} (E : EndApproach f e d) (he : (1+‖E.point j‖)/2 ≤ r n) :=
      angular_budget (z:=E.point j) (by linarith [E.inside j]) (ha n) (E.nonzero j) (hnz n)
    have pair := arc_pair_bound X Y j (hr' n).2.le hx hy (hglob n).1 (hnon n) (one X hx).1 (one Y hy).1
    apply pair.trans
    have cmp {e : ℂ} (E : EndApproach f e d) (he : (1+‖E.point j‖)/2 ≤ r n) :
        2*(E.aperture+2)^2*(1-‖E.point j‖)*(∫ θ, radialKernel (r n) (E.point j) θ*loss f (r n) θ ∂angleMeasure) ≤ v E j := by
      have hc : 0 ≤ 2*(E.aperture+2)^2*(1-‖E.point j‖) := mul_nonneg (by positivity) (sub_nonneg.mpr (E.inside j).le)
      apply le_trans (mul_le_mul_of_nonneg_left (one E he).2 hc)
      dsimp only [v]
      exact le_of_eq (by ring)
    exact add_le_add (cmp X hx) (cmp Y hy)
  have hh := two_end_trace p q hf hb r hr' ht d hd hanti hd0 ⟨_,.of_forall hglob⟩
    (fun j ↦ v X j+v Y j) (by simpa using (hv X).add (hv Y)) htail
  exact ⟨hh.1,r,hr',ht,hh.2⟩

end RiemannMasullo.StripJensen
