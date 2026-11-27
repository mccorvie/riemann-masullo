module

public import RiemannMasullo.ForMathlib.Analysis.Complex.StripJensenBoundary
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Two-boundary Poisson-Jensen in a vertical strip

A single fixed interior vertical with sufficiently small logarithmic loss controls both
infinite ends. This gives absolutely integrable traces on both physical boundaries and
an unordered sum of the true zero orders times the strip Green kernel.

The rational zeta midpoint formula, including its pole term, appears in S. K. Sekatskii,
S. Beltraminelli and D. Merlini, Ukrainian Math. J. 64 (2012), printed p. 227, (10)-(11).
The arbitrary-base strip Poisson kernels also appear in M. Adamo, K.-H. Neeb and
J. Schober, arXiv:2407.21123, Lemma A.6 (94)-(95). -/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory Metric Set
open scoped ComplexConjugate Topology

namespace RiemannMasullo.StripJensen

abbrev Strip (c k : ℝ) := {z : ℂ // InStrip c k z}

def equivDisk {c k : ℝ} (hk : 0 < k) (s : Strip c k) :
    {v : ℂ // ‖v‖ < 1} ≃ Strip c k where
  toFun v := ⟨fromDisk c k s v, fromDisk_mem hk s.property v.property⟩
  invFun z := ⟨toDisk c k s z, toDisk_lt s.property z.property⟩
  left_inv v := Subtype.ext (toDisk_fromDisk hk s.property v.property)
  right_inv z := Subtype.ext (fromDisk_toDisk hk s.property z.property)

def weight (r : ℝ) (v : ℂ) : ℝ := max 0 (Real.log (r/‖v‖))

def circleMean (F : ℂ → ℂ) (c k : ℝ) (s : ℂ) (r : ℝ) : ℝ :=
  Real.circleAverage (fun v ↦ Real.log ‖F (fromDisk c k s v)‖) 0 r

/-- Compact Jensen for a meromorphic function on the strip centered at a regular, nonzero value.
The signed multiplicities are the genuine meromorphic orders at the original strip points. -/
theorem compact_hasSum {c k : ℝ} (hk : 0 < k) (s : Strip c k) (F : ℂ → ℂ)
    (hF : ∀ z, InStrip c k z → MeromorphicAt F z) (hA : AnalyticAt ℂ F s.val) (hne : F s.val ≠ 0)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasSum (fun z : Strip c k ↦ ((meromorphicOrderAt F z.val).untop₀ : ℝ) *
      weight r (toDisk c k s z)) (circleMean F c k s r-Real.log ‖F s.val‖) := by
  classical
  let D := fromDisk c k s.val
  let f := F ∘ D
  let B := closedBall (0:ℂ) r
  let d := MeromorphicOn.divisor f B
  let term := fun v : ℂ ↦ (d v : ℝ)*Real.log (r*‖(0:ℂ)-v‖⁻¹)
  have hb (v : ℂ) : v ∈ B ↔ ‖v‖ ≤ r := mem_closedBall_zero_iff
  have hm : MeromorphicOn f B := fun v hv ↦
    (hF _ (fromDisk_mem hk s.property (((hb v).mp hv).trans_lt hr1))).comp_analyticAt
      (fromDisk_analytic_deriv hk s.property (((hb v).mp hv).trans_lt hr1)).1
  have hD : D 0 = s.val := fromDisk_zero hk s.property
  have hf0 : f 0 ≠ 0 := by simpa only [f,D,comp_apply,fromDisk_zero hk s.property] using hne
  have ha0 : AnalyticAt ℂ f 0 := (show AnalyticAt ℂ F (D 0) by rwa [hD]).comp
    (fromDisk_analytic_deriv hk s.property (by simp)).1
  have hz : d 0 = 0 := by
    rw [show d 0 = _ from MeromorphicOn.divisor_apply hm (mem_closedBall_self hr.le),
      ha0.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hf0]
    rfl
  have J := MeromorphicOn.circleAverage_log_norm (f:=f) (c:=0) hr.ne'
    (show MeromorphicOn f (closedBall 0 |r|) by rwa [abs_of_pos hr])
  rw [abs_of_pos hr,ha0.meromorphicTrailingCoeffAt_of_ne_zero hf0] at J
  change circleMean F c k s r = (∑ᶠ v, term v)+(d 0 : ℝ)*Real.log r+Real.log ‖f 0‖ at J
  simp only [hz,Int.cast_zero,zero_mul,add_zero,f,comp_apply,hD] at J
  have hsub : support term ⊆ d.support := by
    intro v hv
    by_contra h
    change ¬ d v ≠ 0 at h
    exact hv (by simp [term,not_not.mp h])
  have hfin := (d.finiteSupport (isCompact_closedBall (0:ℂ) r)).subset hsub
  have ht : HasSum term (circleMean F c k s r-Real.log ‖F s.val‖) := by
    rw [J,add_sub_cancel_right,finsum_eq_sum_of_support_subset (s:=hfin.toFinset) _ (by simp)]
    exact hasSum_sum_of_ne_finset_zero (fun x hx ↦ by
      by_contra he; exact hx (hfin.mem_toFinset.mpr he))
  have hres := (hasSum_subtype_iff_of_support_subset (s:={v : ℂ | ‖v‖ < 1})
    (fun v hv ↦ ((hb v).mp (d.supportWithinDomain (hsub hv))).trans_lt hr1)).mpr ht
  have hre := ((equivDisk hk s).symm.hasSum_iff).mpr hres
  apply hre.congr_fun
  intro z
  let v := toDisk c k s z
  have hmD : AnalyticAt ℂ D v ∧ deriv D v ≠ 0 := fromDisk_analytic_deriv hk s.property (toDisk_lt s.property z.property)
  have hDz : D v = z.val := fromDisk_toDisk hk s.property z.property
  change _ = term v
  by_cases hv0 : ‖v‖=0
  · change _ * max 0 (Real.log (r/‖v‖)) = _
    simp [term,hv0]
  have hp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv0)
  by_cases hv : ‖v‖ ≤ r
  · have hd : d v = (meromorphicOrderAt F z.val).untop₀ := by
      rw [show d v = _ from MeromorphicOn.divisor_apply hm ((hb v).mpr hv)]
      simp only [f,meromorphicOrderAt_comp_of_deriv_ne_zero hmD.1 hmD.2,hDz]
    have hh := Real.log_nonneg ((one_le_div hp).mpr hv)
    change _ * max 0 (Real.log (r/‖v‖)) = _
    rw [max_eq_right hh]
    simp [hd,term,div_eq_mul_inv]
  · have hd : d v = 0 := by
      by_contra he; exact hv ((hb v).mp (d.supportWithinDomain he))
    have hh := Real.log_nonpos (div_nonneg hr.le hp.le) ((div_le_one hp).mpr (le_of_not_ge hv))
    change _ * max 0 (Real.log (r/‖v‖)) = _
    simp [term,hd,max_eq_left hh]

/-! ## Increasing radii and the full divisor -/

private theorem hasSum_of_limit {ι : Type*} (a : ℕ → ι → ℝ) (v : ι → ℝ) (M : ℕ → ℝ) (V : ℝ)
    (ha : ∀ n, HasSum (a n) (M n)) (h₀ : ∀ n j, 0 ≤ a n j)
    (h₁ : ∀ n j, a n j ≤ v j) (hv : ∀ j, Tendsto (fun n ↦ a n j) atTop (𝓝 (v j)))
    (hM : Tendsto M atTop (𝓝 V)) : HasSum v V := by
  have hs : Summable v := by
    apply summable_of_sum_le (fun i ↦ (h₀ 0 i).trans (h₁ 0 i))
    intro s
    apply le_of_tendsto_of_tendsto (tendsto_finsetSum _ fun i _ ↦ hv i) hM
    exact Eventually.of_forall fun n ↦ sum_le_hasSum s (fun i _ ↦ h₀ n i) (ha n)
  have ht := tendsto_tsum_of_dominated_convergence hs hv (Eventually.of_forall fun n i ↦
    (Real.norm_of_nonneg (h₀ n i)).le.trans (h₁ n i))
  have hM' : Tendsto (fun n ↦ ∑' i, a n i) atTop (𝓝 V) :=
    hM.congr (fun n ↦ (ha n).tsum_eq.symm)
  exact (tendsto_nhds_unique ht hM') ▸ hs.hasSum

private theorem weight_limit {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1)) (v : ℂ) :
    Tendsto (fun n ↦ weight (r n) v) atTop (𝓝 (weight 1 v)) := by
  by_cases h : v=0
  · simp [weight,h]
  have hp := norm_pos_iff.mpr h
  exact tendsto_const_nhds.max ((Real.continuousAt_log (one_div_pos.mpr hp).ne').tendsto.comp
    (hr.div_const ‖v‖))

private theorem weight_le {r : ℝ} (h : 0 < r) (h' : r ≤ 1) (z : ℂ) : weight r z ≤ weight 1 z := by
  by_cases hz : z=0
  · simp [weight,hz]
  have hp := norm_pos_iff.mpr hz
  exact max_le_max le_rfl (Real.log_le_log (div_pos h hp) (div_le_div_of_nonneg_right h' hp.le))

private theorem weight_one {v : ℂ} (hv : ‖v‖ < 1) : weight 1 v = -Real.log ‖v‖ := by
  by_cases hz : v=0
  · simp [weight,hz]
  have hlt := Real.log_neg (norm_pos_iff.mpr hz) hv
  simp [weight,Real.log_inv,one_div,max_eq_right (neg_nonneg.mpr hlt.le)]

/-- An identified limiting radial logarithm gives the genuine full strip Green sum. -/
private theorem hasSum_green_of_radial {c k : ℝ} (hk : 0 < k) (s : Strip c k) (F : ℂ → ℂ)
    (hF : ∀ z, InStrip c k z → AnalyticAt ℂ F z) (hne : F s.val ≠ 0)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n ∧ r n < 1) (hr1 : Tendsto r atTop (𝓝 1))
    (V : ℝ) (hV : Tendsto (fun n ↦ circleMean F c k s (r n)) atTop (𝓝 V)) :
    HasSum (fun z : Strip c k ↦ ((meromorphicOrderAt F z.val).untop₀ : ℝ) *
      (-Real.log ‖toDisk c k s z‖)) (V-Real.log ‖F s.val‖) := by
  let m := fun z : Strip c k ↦ ((meromorphicOrderAt F z.val).untop₀ : ℝ)
  let u := fun z : Strip c k ↦ toDisk c k s z
  have hm (z) : 0 ≤ m z := by
    dsimp only [m]
    exact_mod_cast WithTop.untop₀_nonneg.mpr (hF _ z.property).meromorphicOrderAt_nonneg
  have hs := hasSum_of_limit (fun n z ↦ m z*weight (r n) (u z))
    (fun z ↦ m z*weight 1 (u z)) (fun n ↦ circleMean F c k s (r n)-Real.log ‖F s.val‖)
    (V-Real.log ‖F s.val‖)
    (fun n ↦ compact_hasSum hk s F (fun z hz ↦ (hF z hz).meromorphicAt) (hF _ s.property) hne
      (hr n).1 (hr n).2)
    (fun n z ↦ mul_nonneg (hm z) (le_max_left _ _))
    (fun n z ↦ mul_le_mul_of_nonneg_left (weight_le (hr n).1 (hr n).2.le _) (hm z))
    (fun z ↦ (weight_limit hr1 (u z)).const_mul (m z)) (hV.sub_const _)
  apply hs.congr_fun
  intro z
  dsimp only [m,u]
  rw [weight_one (toDisk_lt s.property z.property)]

/-! ## Physical Poisson integrals -/

/-- The physical left and right Poisson integrals, with the evaluation height taken as zero. -/
def boundaryMean (F : ℂ → ℂ) (c w b : ℝ) : ℝ :=
  (∫ t : ℝ, Real.sin (Real.pi*b/w)/(2*w*(Real.cosh (Real.pi*t/w)-Real.cos (Real.pi*b/w))) *
      Real.log ‖F ((c:ℂ)+(t:ℂ)*I)‖) +
   ∫ t : ℝ, Real.sin (Real.pi*b/w)/(2*w*(Real.cosh (Real.pi*t/w)+Real.cos (Real.pi*b/w))) *
      Real.log ‖F ((c+w:ℝ)+(t:ℂ)*I)‖

private theorem circleMean_one_eq {c w b : ℝ} (hw : 0 < w) (hb : 0 < b) (hbw : b < w) (F : ℂ → ℂ)
    (htrace : CircleIntegrable (fun v ↦ Real.log ‖F (fromDisk c (Real.pi/w) ((c+b:ℝ):ℂ) v)‖) 0 1) :
    circleMean F c (Real.pi/w) ((c+b:ℝ):ℂ) 1 = boundaryMean F c w b := by
  have hs : InStrip c (Real.pi/w) ((c+b:ℝ):ℂ) := (inStrip_iff hw _).2
    ⟨by simpa using hb,by simpa using hbw⟩
  have hh := circle_to_edges (div_pos Real.pi_pos hw) hs (fun z ↦ Real.log ‖F z‖) htrace
  simpa only [circleMean,boundaryMean,edge_eq_width hw,one_mul,neg_one_mul,sub_neg_eq_add,
    div_div_eq_mul_div,div_self Real.pi_ne_zero,one_mul,
    show Real.pi/(Real.pi/w)=w by field_simp [Real.pi_ne_zero,hw.ne']] using hh

/-- The genuine strip divisor sums to the two boundary integrals minus the central logarithm
provided the compact logarithmic means tend to the edge trace along one sequence of radii. -/
private theorem two_boundary_of_radial {c w b : ℝ} (hw : 0 < w) (hb : 0 < b) (hbw : b < w) (F : ℂ → ℂ)
    (hF : ∀ z, c < z.re → z.re < c+w → AnalyticAt ℂ F z) (hne : F ((c+b:ℝ):ℂ) ≠ 0)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n ∧ r n < 1) (hr1 : Tendsto r atTop (𝓝 1))
    (htrace : CircleIntegrable (fun v ↦ Real.log ‖F (fromDisk c (Real.pi/w) ((c+b:ℝ):ℂ) v)‖) 0 1)
    (hlim : Tendsto (fun n ↦ circleMean F c (Real.pi/w) ((c+b:ℝ):ℂ) (r n)) atTop
      (𝓝 (circleMean F c (Real.pi/w) ((c+b:ℝ):ℂ) 1))) :
    HasSum (fun z : Strip c (Real.pi/w) ↦ ((meromorphicOrderAt F z.val).untop₀ : ℝ) *
      (-Real.log ‖toDisk c (Real.pi/w) ((c+b:ℝ):ℂ) z‖)) (boundaryMean F c w b-Real.log ‖F ((c+b:ℝ):ℂ)‖) := by
  have hs : InStrip c (Real.pi/w) ((c+b:ℝ):ℂ) := (inStrip_iff hw _).2
    ⟨by simpa using hb,by simpa using hbw⟩
  have hh := hasSum_green_of_radial (div_pos Real.pi_pos hw) ⟨_,hs⟩ F
    (fun z hz ↦ hF z ((inStrip_iff hw _).1 hz).1 ((inStrip_iff hw _).1 hz).2)
    hne r hr hr1 _ hlim
  rw [circleMean_one_eq hw hb hbw F htrace] at hh
  exact hh

/-! ## End probes -/

/-- Pointwise nontangential end data are sufficient for the actual physical strip formula.
All ordinary finite boundary zeros are permitted, and no boundary integral or trace limit
is presumed. The two end points are fixed by the strip chart, even for an off-center base. -/
private theorem two_boundary_of_endApproaches {c w b : ℝ} (hw : 0 < w) (hb : 0 < b) (hbw : b < w)
    (F : ℂ → ℂ)
    (ha : ∀ z : ℂ, c ≤ z.re → z.re ≤ c+w → AnalyticAt ℂ F z ∧ meromorphicOrderAt F z ≠ ⊤)
    (hB : ∀ z : ℂ, c ≤ z.re → z.re ≤ c+w → ‖F z‖ ≤ 1) (hne : F ((c+b:ℝ):ℂ) ≠ 0)
    (d : ℕ → ℝ) (hd : ∀ j, 0 < d j) (hanti : Antitone d) (hd0 : Tendsto d atTop (𝓝 0)) :
    let k := Real.pi/w
    let s : ℂ := ((c+b:ℝ):ℂ)
    let g := F ∘ chart c k s
    EndApproach g 1 d → EndApproach g (otherEnd (ray c k s)) d →
    CircleIntegrable (fun v ↦ Real.log ‖F (fromDisk c k s v)‖) 0 1 ∧
    HasSum (fun z : Strip c k ↦ ((meromorphicOrderAt F z.val).untop₀ : ℝ) *
      (-Real.log ‖toDisk c k s z‖)) (boundaryMean F c w b-Real.log ‖F s‖) := by
  intro k s g X Y
  have hk : 0 < k := div_pos Real.pi_pos hw
  have hs : InStrip c k s := (inStrip_iff hw _).mpr ⟨by simpa [s] using hb,by simpa [s] using hbw⟩
  have hf (v : ℂ) (hv : ‖v‖ ≤ 1) (h1 : v ≠ 1) (h2 : v ≠ otherEnd (ray c k s)) :
      AnalyticAt ℂ g v ∧ meromorphicOrderAt g v ≠ ⊤ := by
    have hh := chart_analytic_deriv hk hs hv h1 h2
    have hR := chart_re_mem hw hs hv
    have hF := ha _ hR.1 hR.2
    refine ⟨hF.1.comp hh.1,?_⟩
    change meromorphicOrderAt (F ∘ chart c k s) v ≠ ⊤
    rw [meromorphicOrderAt_comp_of_deriv_ne_zero hh.1 hh.2]
    exact hF.2
  have hbound (v : ℂ) (hv : ‖v‖ ≤ 1) : ‖g v‖ ≤ 1 := by
    have hh := chart_re_mem hw hs hv
    exact hB _ hh.1 hh.2
  have h0 : g 0 ≠ 0 := by simpa only [g,comp_apply,chart_closed hs (by simp : ‖(0:ℂ)‖≤1),fromDisk_zero hk hs] using hne
  obtain ⟨hi,r,hr,ht,hlim⟩ := circle_trace_of_endApproaches (by simp) (norm_otherEnd (ray_im_pos hs))
    hf hbound h0 d hd hanti hd0 X Y
  have heq {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      EqOn (fun v ↦ Real.log ‖g v‖) (fun v ↦ Real.log ‖F (fromDisk c k s v)‖) (sphere 0 |t|) := by
    intro v hv
    have hnorm : ‖v‖ ≤ 1 := calc ‖v‖ = |t| := mem_sphere_zero_iff_norm.mp hv
      _ = t := abs_of_nonneg ht0
      _ ≤ 1 := ht1
    dsimp only [g,comp_apply]
    rw [chart_closed hs hnorm]
  have hi' := (circleIntegrable_congr (heq zero_le_one le_rfl)).mp hi
  have hmean {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      Real.circleAverage (fun v ↦ Real.log ‖g v‖) 0 t = circleMean F c k s t :=
    Real.circleAverage_congr_sphere (heq ht0 ht1)
  rw [hmean zero_le_one le_rfl] at hlim
  have hlim' : Tendsto (fun n ↦ circleMean F c k s (r n)) atTop (𝓝 (circleMean F c k s 1)) :=
    hlim.congr (fun n ↦ hmean (hr n).1.le (hr n).2.le)
  exact ⟨hi',two_boundary_of_radial hw hb hbw F (fun z h₁ h₂ ↦ (ha z h₁.le h₂.le).1) hne r hr ht hi' hlim'⟩

/-! ## Interior Euler line probes -/

private structure Probe (f : ℂ → ℂ) (e : ℂ) where
  point : ℕ → ℂ
  A : ℝ
  hA : 0 ≤ A
  inside : ∀ j, ‖point j‖ < 1
  cone : ∀ j, ‖point j-e‖ ≤ A*(1-‖point j‖)
  late : ∀ᶠ j in atTop, 1/2 ≤ ‖point j‖ ∧ f (point j) ≠ 0
  loss : Tendsto (fun j ↦ (1-‖point j‖)*|Real.log ‖f (point j)‖|) atTop (𝓝 0)

private theorem fit {f : ℂ → ℂ} {p q : ℂ} (X : Probe f p) (Y : Probe f q) :
    ∃ d : ℕ → ℝ, (∀ j, 0 < d j) ∧ Antitone d ∧ Tendsto d atTop (𝓝 0) ∧
       Nonempty (EndApproach f p d) ∧ Nonempty (EndApproach f q d) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (X.late.and Y.late)
  let D (j : ℕ) := min (1-‖X.point (j+N)‖) (1-‖Y.point (j+N)‖)
  obtain ⟨d,hd,ha,ht,hfit⟩ := exists_shrinking_scale D (fun j ↦ lt_min (sub_pos.mpr (X.inside _)) (sub_pos.mpr (Y.inside _)))
  have mk {e : ℂ} (E : Probe f e) (hh : ∀ j, 1/2 ≤ ‖E.point (j+N)‖ ∧ f (E.point (j+N)) ≠ 0)
       (hd' : ∀ j, d j ≤ 1-‖E.point (j+N)‖) : Nonempty (EndApproach f e d) :=
    ⟨⟨fun j ↦ E.point (j+N),E.A,E.hA,fun j ↦ (hh j).1,fun j ↦ E.inside _,hd',
       fun j ↦ E.cone _,fun j ↦ (hh j).2,E.loss.comp (tendsto_add_atTop_nat N)⟩⟩
  exact ⟨d,hd,ha,ht,mk X (fun j ↦ (hN _ (Nat.le_add_left N j)).1) (fun j ↦ (hfit j).trans (min_le_left _ _)),
    mk Y (fun j ↦ (hN _ (Nat.le_add_left N j)).2) (fun j ↦ (hfit j).trans (min_le_right _ _))⟩

private def verticalProbe {f : ℂ → ℂ} {e : ℂ} (he : ‖e‖=1) {k : ℝ} (hk : 0 < k) (z : ℕ → ℂ)
    (A : ℝ) (hA : 0 ≤ A) (C : ℝ) (hi : ∀ n, ‖z n‖ < 1)
    (hc : ∀ n, ‖z n-e‖ ≤ A*(1-‖z n‖)) (hs : ∀ n, ‖z n-e‖ ≤ C*Real.exp (-(k*(n:ℝ))))
    (hn : ∀ᶠ n in atTop, f (z n) ≠ 0)
    (hl : Tendsto (fun n : ℕ ↦ Real.exp (-(k*(n:ℝ)))*|Real.log ‖f (z n)‖|) atTop (𝓝 0)) : Probe f e := by
  have hgap (n : ℕ) : 1-‖z n‖ ≤ ‖z n-e‖ := by
    have hh := norm_sub_norm_le e (z n)
    simpa only [he,norm_sub_rev e] using hh
  have hg0 := fun n ↦ sub_nonneg.mpr (hi n).le
  have hg : Tendsto (fun n ↦ 1-‖z n‖) atTop (𝓝 0) := squeeze_zero hg0
    (fun n ↦ (hgap n).trans (hs n)) (by simpa using (exp_decay_nat hk).const_mul C)
  have hlower : ∀ᶠ n in atTop, 1/2 ≤ ‖z n‖ := by
    filter_upwards [hg.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))] with n hn
    linarith
  refine ⟨z,A,hA,hi,hc,hlower.and hn,?_⟩
  have hb (n : ℕ) : (1-‖z n‖)*|Real.log ‖f (z n)‖| ≤ C*(Real.exp (-(k*(n:ℝ)))*|Real.log ‖f (z n)‖|) :=
    (mul_le_mul_of_nonneg_right ((hgap n).trans (hs n)) (abs_nonneg _)).trans_eq (mul_assoc _ _ _)
  exact squeeze_zero (fun n ↦ mul_nonneg (hg0 n) (abs_nonneg _)) hb (by simpa using hl.const_mul C)

/-- Poisson-Jensen on the two physical lines, evaluated at c+b. The analytic function is
bounded on the strip, extends holomorphically with finite order through its finite edges,
and has subexponential logarithmic loss along the two tails of ONE interior vertical line.
Only its values at integer heights on this line enter the hypothesis. No boundary trace,
summability of zeros, or absence of finite-edge zeros is assumed. -/
theorem two_boundary_of_vertical_line {c w b x : ℝ} (hw : 0 < w) (hb : 0 < b) (hbw : b < w)
    (hx : 0 < x) (hxw : x < w) (F : ℂ → ℂ)
    (ha : ∀ z : ℂ, c ≤ z.re → z.re ≤ c+w → AnalyticAt ℂ F z ∧ meromorphicOrderAt F z ≠ ⊤)
    (hB : ∀ z : ℂ, c ≤ z.re → z.re ≤ c+w → ‖F z‖ ≤ 1) (hne : F ((c+b:ℝ):ℂ) ≠ 0)
    (hn : ∀ᶠ n : ℕ in atTop, F (site c x (n:ℝ)) ≠ 0 ∧ F (site c x (-(n:ℝ))) ≠ 0)
    (hplus : Tendsto (fun n : ℕ ↦ Real.exp (-(Real.pi/w*(n:ℝ)))*|Real.log ‖F (site c x (n:ℝ))‖|) atTop (𝓝 0))
    (hminus : Tendsto (fun n : ℕ ↦ Real.exp (-(Real.pi/w*(n:ℝ)))*|Real.log ‖F (site c x (-(n:ℝ)))‖|) atTop (𝓝 0)) :
    CircleIntegrable (fun v ↦ Real.log ‖F (fromDisk c (Real.pi/w) ((c+b:ℝ):ℂ) v)‖) 0 1 ∧
    HasSum (fun z : Strip c (Real.pi/w) ↦ ((meromorphicOrderAt F z.val).untop₀ : ℝ) *
      (-Real.log ‖toDisk c (Real.pi/w) ((c+b:ℝ):ℂ) z‖))
         (boundaryMean F c w b-Real.log ‖F ((c+b:ℝ):ℂ)‖) := by
  let k := Real.pi/w
  let s : ℂ := ((c+b:ℝ):ℂ)
  let a := ray c k s
  let g := F ∘ chart c k s
  let P (n : ℕ) := toDisk c k s (site c x (n:ℝ))
  let M (n : ℕ) := toDisk c k s (site c x (-(n:ℝ)))
  have hk : 0 < k := div_pos Real.pi_pos hw
  have hs : InStrip c k s := (inStrip_iff hw _).mpr ⟨by simpa [s] using hb,by simpa [s] using hbw⟩
  have angle (u : ℝ) (h0 : 0 < u) (h1 : u < w) : 0 < k*u ∧ k*u < Real.pi := by
    exact ⟨mul_pos hk h0,(mul_lt_mul_of_pos_left h1 hk).trans_eq (div_mul_cancel₀ _ hw.ne')⟩
  have hsin : 0 < Real.sin (k*x) := Real.sin_pos_of_pos_of_lt_pi (angle x hx hxw).1 (angle x hx hxw).2
  have geo (n : ℕ) := physical_probes (c:=c) hk (angle b hb hbw) (angle x hx hxw) (n:ℝ) (Nat.cast_nonneg n)
  have hval (t : ℝ) : g (toDisk c k s (site c x t)) = F (site c x t) := by
    have hsite : InStrip c k (site c x t) := site_mem (angle x hx hxw) t
    change F (chart c k s (toDisk c k s (site c x t)))=_
    rw [chart_closed hs (toDisk_lt hs hsite).le,fromDisk_toDisk hk hs hsite]
  have ep := norm_otherEnd (ray_im_pos hs)
  let X : Probe g 1 := verticalProbe (by simp) hk M (2/Real.sin (k*x)) (by positivity) (2*a.im/Real.sin (k*x))
    (fun n ↦ (geo n).2.1) (fun n ↦ (geo n).2.2.2.2.2) (fun n ↦ (geo n).2.2.2.1)
    (hn.mono fun n h ↦ by change g (toDisk c k s (site c x (-(n:ℝ)))) ≠ 0; rw [hval]; exact h.2)
    (by simpa only [M,hval] using hminus)
  let Y : Probe g (otherEnd a) := verticalProbe ep hk P (2/Real.sin (k*x)) (by positivity) 2
    (fun n ↦ (geo n).1) (fun n ↦ (geo n).2.2.2.2.1) (fun n ↦ (geo n).2.2.1)
    (hn.mono fun n h ↦ by change g (toDisk c k s (site c x (n:ℝ))) ≠ 0; rw [hval]; exact h.1)
    (by simpa only [P,hval] using hplus)
  obtain ⟨d,hd,hanti,hd0,⟨X'⟩,⟨Y'⟩⟩ := fit X Y
  exact two_boundary_of_endApproaches hw hb hbw F ha hB hne d hd hanti hd0 X' Y'

/-! ## Strip Green formula -/

/-- Physical strip Green function for a zero at z and evaluation point c+b. -/
def physicalGreen (c w b : ℝ) (z : ℂ) : ℝ :=
  Real.log ((Real.cosh (Real.pi/w*z.im)-Real.cos (Real.pi/w*(z.re-c)+Real.pi/w*b))/
    (Real.cosh (Real.pi/w*z.im)-Real.cos (Real.pi/w*(z.re-c)-Real.pi/w*b)))/2

private theorem physicalGreen_eq {c w b : ℝ} (hw : 0 < w) {z : ℂ}
    (hs : InStrip c (Real.pi/w) ((c+b:ℝ):ℂ)) (hz : InStrip c (Real.pi/w) z) (hne : z ≠ ((c+b:ℝ):ℂ)) :
    physicalGreen c w b z = -Real.log ‖toDisk c (Real.pi/w) ((c+b:ℝ):ℂ) z‖ := by
  let k := Real.pi/w
  let s : ℂ := ((c+b:ℝ):ℂ)
  have hk : 0 < k := div_pos Real.pi_pos hw
  have he : ((c+(z.re-c):ℝ):ℂ)+(z.im:ℂ)*I=z := by
    apply Complex.ext <;> simp
  have hsite : InStrip c k (((c+(z.re-c):ℝ):ℂ)+(z.im:ℂ)*I) := by rw [he]; exact hz
  have hsep : ray c k (((c+(z.re-c):ℝ):ℂ)+(z.im:ℂ)*I) ≠ ray c k s := by
    rw [he]
    intro eq
    exact hne ((unray_ray hk hz).symm.trans ((congrArg (unray c k) eq).trans (unray_ray hk hs)))
  have hg := green_coordinates hs hsite hsep
  rw [he] at hg
  exact hg.symm

theorem physicalGreen_pos {c w b : ℝ} (hw : 0 < w) {z : ℂ}
    (hs : InStrip c (Real.pi/w) ((c+b:ℝ):ℂ)) (hz : InStrip c (Real.pi/w) z) (hne : z ≠ ((c+b:ℝ):ℂ)) :
    0 < physicalGreen c w b z := by
  have hk := div_pos Real.pi_pos hw
  have hn : toDisk c (Real.pi/w) ((c+b:ℝ):ℂ) z ≠ 0 := by
    intro he
    have hh := fromDisk_toDisk hk hs hz
    rw [he,fromDisk_zero hk hs] at hh
    exact hne hh.symm
  rw [physicalGreen_eq hw hs hz hne]
  exact neg_pos.mpr (Real.log_neg (norm_pos_iff.mpr hn) (toDisk_lt hs hz))

private theorem finite_order_closed {c w : ℝ} {F : ℂ → ℂ}
    (h : ∀ z : ℂ, c ≤ z.re → z.re ≤ c+w → AnalyticAt ℂ F z)
    {s : ℂ} (hs : c ≤ s.re ∧ s.re ≤ c+w) (hn : F s ≠ 0)
    {z : ℂ} (hz : c ≤ z.re ∧ z.re ≤ c+w) : meromorphicOrderAt F z ≠ ⊤ := by
  let S := {u : ℂ | c ≤ u.re} ∩ {u : ℂ | u.re ≤ c+w}
  have hc : IsPreconnected S := ((convex_halfSpace_re_ge c).inter (convex_halfSpace_re_le (c+w))).isPreconnected
  have ha : AnalyticOnNhd ℂ F S := fun u hu ↦ h u hu.1 hu.2
  have hs0 := (h s hs.1 hs.2).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hn
  exact ha.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hc hs hz (by simp [hs0])

private theorem negligible_of_lower {k : ℝ} (hk : 0 < k) (A : ℝ) (v : ℕ → ℝ)
    (hb : ∀ n, v n ≤ 1) (hL : ∀ᶠ n : ℕ in atTop, Real.exp (-(A*((n:ℝ)+1))) ≤ v n) :
    Tendsto (fun n : ℕ ↦ Real.exp (-(k*(n:ℝ)))*|Real.log (v n)|) atTop (𝓝 0) := by
  let q := Real.exp (-k)
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hq' : q < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hk)
  have eql (n : ℕ) : Real.exp (-(k*(n:ℝ)))=q^n := by
    rw [show -(k*(n:ℝ))=(n:ℝ)*(-k) by ring,Real.exp_nat_mul]
  have h₁ := tendsto_self_mul_const_pow_of_lt_one hq hq'
  have h₂ := tendsto_pow_atTop_nhds_zero_of_lt_one hq hq'
  have hlim : Tendsto (fun n : ℕ ↦ A*((n:ℝ)*q^n+q^n)) atTop (𝓝 0) := by simpa using (h₁.add h₂).const_mul A
  apply squeeze_zero' (.of_forall fun n ↦ mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) _ hlim
  filter_upwards [hL] with n hn
  have hv := (Real.exp_pos _).trans_le hn
  have hl := Real.log_le_log (Real.exp_pos _) hn
  rw [Real.log_exp] at hl
  have hh : |Real.log (v n)| ≤ A*((n:ℝ)+1) := by
    rw [abs_of_nonpos (Real.log_nonpos hv.le (hb n))]
    linarith
  rw [eql]
  apply (mul_le_mul_of_nonneg_left hh (pow_nonneg hq n)).trans_eq
  ring

/-- Both boundary logarithms are absolutely integrable. The genuine interior orders, with
the disk Green weight given in physical coordinates by green_coordinates, sum to their two
physical Poisson integrals minus the evaluation logarithm. A single interior line with an
eventual exp(-A(n+1)) norm lower bound at heights ±n suffices. -/
theorem two_boundary_of_exponential_lower {c w b x : ℝ} (hw : 0 < w) (hb : 0 < b) (hbw : b < w)
    (hx : 0 < x) (hxw : x < w) (F : ℂ → ℂ)
    (ha : ∀ z : ℂ, c ≤ z.re → z.re ≤ c+w → AnalyticAt ℂ F z)
    (hB : ∀ z : ℂ, c ≤ z.re → z.re ≤ c+w → ‖F z‖ ≤ 1) (hne : F ((c+b:ℝ):ℂ) ≠ 0)
    (A : ℝ) (hL : ∀ᶠ n : ℕ in atTop, Real.exp (-(A*((n:ℝ)+1))) ≤ ‖F (site c x (n:ℝ))‖ ∧
                                      Real.exp (-(A*((n:ℝ)+1))) ≤ ‖F (site c x (-(n:ℝ)))‖) :
    Integrable (fun t : ℝ ↦ Real.sin (Real.pi*b/w)/(2*w*(Real.cosh (Real.pi*t/w)-Real.cos (Real.pi*b/w))) *
      Real.log ‖F ((c:ℂ)+(t:ℂ)*I)‖) ∧
    Integrable (fun t : ℝ ↦ Real.sin (Real.pi*b/w)/(2*w*(Real.cosh (Real.pi*t/w)+Real.cos (Real.pi*b/w))) *
      Real.log ‖F ((c+w:ℝ)+(t:ℂ)*I)‖) ∧
    HasSum (fun z : Strip c (Real.pi/w) ↦ ((meromorphicOrderAt F z.val).untop₀ : ℝ) *
      physicalGreen c w b z.val)
         (boundaryMean F c w b-Real.log ‖F ((c+b:ℝ):ℂ)‖) := by
  let k := Real.pi/w
  let s : ℂ := ((c+b:ℝ):ℂ)
  have hk : 0 < k := div_pos Real.pi_pos hw
  have hs : InStrip c k s := (inStrip_iff hw _).mpr ⟨by simpa [s] using hb,by simpa [s] using hbw⟩
  have hh := (inStrip_iff hw _).mp hs
  have horder (z : ℂ) (hz : c ≤ z.re) (hz' : z.re ≤ c+w) : AnalyticAt ℂ F z ∧ meromorphicOrderAt F z ≠ ⊤ := ⟨ha z hz hz',
    finite_order_closed ha ⟨hh.1.le,hh.2.le⟩ hne ⟨hz,hz'⟩⟩
  have hsite (t : ℝ) : ‖F (site c x t)‖ ≤ 1 := hB _
    (by simp [site]; linarith) (by simp [site]; linarith)
  have hn : ∀ᶠ n : ℕ in atTop, F (site c x (n:ℝ)) ≠ 0 ∧ F (site c x (-(n:ℝ))) ≠ 0 :=
    hL.mono (fun n h ↦ ⟨norm_pos_iff.mp ((Real.exp_pos _).trans_le h.1),norm_pos_iff.mp ((Real.exp_pos _).trans_le h.2)⟩)
  obtain ⟨hcircle,HG⟩ := two_boundary_of_vertical_line hw hb hbw hx hxw F horder hB hne hn
    (negligible_of_lower hk A _ (fun n ↦ hsite n) (hL.mono fun _ h ↦ h.1))
    (negligible_of_lower hk A _ (fun n ↦ hsite (-(n:ℝ))) (hL.mono fun _ h ↦ h.2))
  have sides := edges_integrable hk hs (fun z ↦ Real.log ‖F z‖) hcircle
  have HG' : HasSum (fun z : Strip c k ↦ ((meromorphicOrderAt F z.val).untop₀ : ℝ) * physicalGreen c w b z.val)
      (boundaryMean F c w b-Real.log ‖F s‖) := by
    apply HG.congr_fun
    intro z
    by_cases eq : z.val = s
    · have hzero := (ha s hh.1.le hh.2.le).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hne
      simp [eq,hzero]
    · rw [physicalGreen_eq hw hs z.property eq]
  have hwidth : Real.pi/(Real.pi/w)=w := by field_simp [Real.pi_ne_zero,hw.ne']
  simpa only [k,edge_eq_width hw,one_mul,neg_one_mul,sub_neg_eq_add,hwidth] using
    And.intro sides.1 (And.intro sides.2 HG')

end RiemannMasullo.StripJensen
