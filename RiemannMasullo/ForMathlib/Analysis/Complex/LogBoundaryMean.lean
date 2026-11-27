module

public import RiemannMasullo.ForMathlib.Analysis.Complex.PoissonLogMajorant
public import RiemannMasullo.ForMathlib.Analysis.Complex.PoissonBoundaryTransport
public import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Logarithmic circle means with one exceptional boundary point

Finite-order boundary zeros have angularly integrable logarithmic singularities. On arcs
near the exceptional point a Poisson estimate controls the lost logarithmic mass. A
subexponential radial approach at that point then recovers the full boundary mean. -/

public noncomputable section

open Complex MeasureTheory Metric Set Filter Function
open scoped Topology
namespace RiemannMasullo.PoissonBoundary

private theorem norm_chord (θ φ : ℝ) :
    ‖circleMap 0 1 θ - circleMap 0 1 φ‖ = 2 * |Real.sin ((θ-φ)/2)| := by
  have h := norm_circleMap_sub_circleMap_sq 0 1 1 θ φ
  have hsin : Real.sin ((θ-φ)/2)^2 = (1-Real.cos (θ-φ))/2 := by
    rw [Real.sin_sq_eq_half_sub, show 2*((θ-φ)/2)=θ-φ by ring]
    ring
  have hd : (2 * |Real.sin ((θ-φ)/2)|)^2 = ‖circleMap 0 1 θ-circleMap 0 1 φ‖^2 := by
    rw [mul_pow,sq_abs,hsin,h]
    ring
  exact ((sq_eq_sq₀ (by positivity) (norm_nonneg _)).1 hd).symm

/-- Uniform angular bound for the log of one linear divisor factor for radii in
the outer half of the disk, including factors centered on the limiting circle. -/
private theorem log_chord_bound {r : ℝ} (hr : 1/2 ≤ r) (hr1 : r ≤ 1)
    {a : ℂ} (ha : ‖a‖ ≤ 1) (θ : ℝ)
    (hne : circleMap 0 1 θ ≠ circleMap 0 1 a.arg) :
    |Real.log ‖circleMap 0 r θ-a‖| ≤
      Real.log 4 + |Real.log ‖circleMap 0 1 θ-circleMap 0 1 a.arg‖| := by
  let u := ‖circleMap 0 r θ-a‖
  let v := ‖circleMap 0 1 θ-circleMap 0 1 a.arg‖
  have hv : 0 < v := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have hlo : v/4 ≤ u := by
    dsimp [u,v]
    rw [norm_chord]
    have h := mul_abs_sin_le_norm_circleMap_zero_sub r θ a
    nlinarith [mul_nonneg (sub_nonneg.2 hr) (abs_nonneg (Real.sin ((θ-a.arg)/2)))]
  have hu : 0 < u := (by positivity : 0 < v/4).trans_le hlo
  have hup : u ≤ 2 := by
    dsimp [u]
    have h := norm_sub_le (circleMap 0 r θ) a
    rw [norm_circleMap_zero,abs_of_nonneg (by linarith)] at h
    linarith
  have hl := Real.log_le_log (by positivity : 0 < v/4) hlo
  rw [Real.log_div hv.ne' (by norm_num)] at hl
  have hh := Real.log_le_log hu (hup.trans (by norm_num : (2:ℝ) ≤ 4))
  exact abs_le.2 ⟨by linarith [neg_abs_le (Real.log v)], by linarith [abs_nonneg (Real.log v)]⟩

local notation "angles" => Ioc (0 : ℝ) (2*Real.pi)

/-- On an arbitrary compact portion of the closed disk without a locally zero
germ, one angularly integrable function bounds the radial logarithms up to the boundary. -/
theorem exists_integrableOn_radial_log_envelope {K : Set ℂ} (hK : IsCompact K)
    (hK1 : K ⊆ closedBall 0 1) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f K)
    (htop : ∀ z : K, meromorphicOrderAt f z ≠ ⊤) :
    ∃ B : ℝ → ℝ, IntegrableOn B angles ∧ ∀ r : ℝ, 1/2 ≤ r → r ≤ 1 →
      ∀ᵐ θ ∂volume, circleMap 0 r θ ∈ K → |Real.log ‖f (circleMap 0 r θ)‖| ≤ B θ := by
  classical
  let D := MeromorphicOn.divisor f K
  have hD : D.support.Finite := D.finiteSupport hK
  let S := hD.toFinset
  have hs (a : ℂ) : a ∈ S ↔ D a ≠ 0 := hD.mem_toFinset
  obtain ⟨g,hg,hg0,hfg⟩ := hf.meromorphicOn.extract_zeros_poles htop hD
  have hcont : ContinuousOn (fun z ↦ Real.log ‖g z‖) K := hg.continuousOn.norm.log
    (fun z hz ↦ norm_ne_zero_iff.mpr (hg0 ⟨z,hz⟩))
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hcont
  let p (a : ℂ) := circleMap 0 1 a.arg
  let v (a : ℂ) (θ : ℝ) := ‖circleMap 0 1 θ-p a‖
  let B (θ : ℝ) := (∑ a ∈ S, |(D a : ℝ)| * (Real.log 4+ |Real.log (v a θ)|))+C
  have hInt (a : ℂ) : IntegrableOn (fun θ ↦ |Real.log (v a θ)|) angles := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp
    exact (circleIntegrable_log_norm_sub_const (c := (0:ℂ)) (a := p a) 1).abs
  have hCB : IntegrableOn B angles := by
    have hA : IntegrableOn (fun θ ↦ ∑ a ∈ S, |(D a : ℝ)| * (Real.log 4+ |Real.log (v a θ)|)) angles := by
      exact integrable_finsetSum S (fun a _ ↦ ((integrable_const _).add (hInt a)).const_mul _)
    exact hA.add (integrable_const C)
  refine ⟨B,hCB,fun r hr hr1 ↦ ?_⟩
  let L (z : ℂ) := (∑ a ∈ S, (D a : ℝ)*Real.log ‖z-a‖) + Real.log ‖g z‖
  have hL : (fun z ↦ Real.log ‖f z‖) =ᶠ[codiscreteWithin K] L := by
    have h := MeromorphicOn.extract_zeros_poles_log hg0 hfg
    have hsupport : Function.support (fun a ↦ (fun z : ℂ ↦ (D a : ℝ)*Real.log ‖z-a‖)) ⊆ (↑S:Set ℂ) := by
      intro a ha
      apply (hs a).2
      intro hz
      exact ha (by funext z; simp [hz])
    filter_upwards [h] with z haz
    rw [haz]
    change (∑ᶠ a, (fun z : ℂ ↦ (D a : ℝ)*Real.log ‖z-a‖)) z + Real.log ‖g z‖ = _
    rw [finsum_eq_sum_of_support_subset _ hsupport]
    simp [L]
  let E := K \ {z | Real.log ‖f z‖ = L z}
  have hE : E.Finite := hK.finite_sdiff_of_mem_codiscreteWithin hL
  have hae : ∀ᵐ θ ∂volume, circleMap 0 r θ ∉ E :=
    measure_eq_zero_iff_ae_notMem.mp ((hE.countable.preimage_circleMap 0 (by linarith : r ≠ 0)).measure_zero volume)
  have hep : ∀ᵐ θ ∂volume, circleMap 0 1 θ ∉ (↑(S.image p) : Set ℂ) :=
    measure_eq_zero_iff_ae_notMem.mp (((S.image p).finite_toSet.countable.preimage_circleMap 0 one_ne_zero).measure_zero volume)
  filter_upwards [hae,hep] with θ hθ hpoints
  intro hKθ
  have heq : Real.log ‖f (circleMap 0 r θ)‖ = L (circleMap 0 r θ) :=
    by_contra (fun hn ↦ hθ ⟨hKθ,hn⟩)
  rw [heq]
  dsimp only [L,B]
  calc |(∑ a ∈ S, (D a : ℝ)*Real.log ‖circleMap 0 r θ-a‖)+Real.log ‖g (circleMap 0 r θ)‖| ≤
       (∑ a ∈ S, |(D a : ℝ)*Real.log ‖circleMap 0 r θ-a‖|)+ |Real.log ‖g (circleMap 0 r θ)‖| :=
       (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl)
       _ ≤ _ := by
         apply add_le_add _ (hC _ hKθ)
         apply Finset.sum_le_sum
         intro a ha
         rw [abs_mul]
         apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
         apply log_chord_bound hr hr1 (mem_closedBall_zero_iff.1 (hK1 (D.supportWithinDomain ((hs a).1 ha)))) θ
         exact fun hh ↦ hpoints (Finset.mem_image.2 ⟨a,ha,hh.symm⟩)

end RiemannMasullo.PoissonBoundary

open Complex MeasureTheory Metric Set Filter Function
open scoped Topology
namespace RiemannMasullo.PoissonBoundary

local notation "Kdisk" => (closedBall (0:ℂ) 1 \ ({1} : Set ℂ) : Set ℂ)
local notation "μθ" => volume.restrict (Ioc (0:ℝ) (2*Real.pi))

private theorem norm_sub_radius (r θ : ℝ) :
    ‖circleMap 0 r θ - circleMap 0 1 θ‖ = |r-1| := by
  simp only [circleMap_zero, ← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_exp, Complex.mul_I_re, Complex.ofReal_im, neg_zero,
    Real.exp_zero, mul_one]

/-- The boundary trace of the logarithm converges in local angular L¹ on every arc
away from the exceptional point at one, even if the trace vanishes on that arc. -/
theorem radial_log_local_L1 {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Kdisk)
    (hord : ∀ z : Kdisk, meromorphicOrderAt f z ≠ ⊤)
    {r : ℕ → ℝ} (ht : Tendsto r atTop (𝓝 1)) (hmax : ∀ᶠ n in atTop, r n ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) :
    let A := {θ : ℝ | δ < ‖circleMap 0 1 θ-1‖}
    let u (t θ : ℝ) := -Real.log ‖f (circleMap 0 t θ)‖
    IntegrableOn (u 1) A μθ ∧
      Tendsto (fun n ↦ ∫ θ in A, |u (r n) θ-u 1 θ| ∂μθ) atTop (𝓝 0) := by
  classical
  intro A u
  let K : Set ℂ := closedBall 0 1 ∩ {z : ℂ | δ/2 ≤ ‖z-1‖}
  have hK : IsCompact K := (isCompact_closedBall (0:ℂ) 1).inter_right (isClosed_le continuous_const (by fun_prop))
  have hKA : K ⊆ Kdisk := by
    rintro z ⟨hz,hd⟩
    refine ⟨hz,?_⟩
    rintro ⟨rfl⟩
    change δ/2 ≤ ‖(1:ℂ)-1‖ at hd
    simp only [sub_self,norm_zero] at hd
    linarith
  have hfK := hf.mono hKA
  have hoK (z : K) : meromorphicOrderAt f z ≠ ⊤ := hord ⟨z,hKA z.property⟩
  obtain ⟨B,hB,hb⟩ := exists_integrableOn_radial_log_envelope hK inter_subset_left hfK hoK
  have hA : MeasurableSet A := (isOpen_lt continuous_const (by fun_prop)).measurableSet
  let μ : Measure ℝ := (μθ).restrict A
  have hAae : ∀ᵐ θ ∂μ, θ ∈ A := ae_restrict_mem hA
  have hgood (t : ℝ) (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hclose : |t-1| ≤ δ/2) :
      MapsTo (circleMap 0 t) A K := by
    intro θ hθ
    refine ⟨mem_closedBall_zero_iff.2 (by rw [norm_circleMap_zero,abs_of_nonneg (by linarith)]; exact ht1), ?_⟩
    have htri := norm_sub_le_norm_sub_add_norm_sub (circleMap 0 1 θ) (circleMap 0 t θ) 1
    rw [norm_sub_rev (circleMap 0 1 θ) (circleMap 0 t θ), norm_sub_radius] at htri
    change δ < ‖circleMap 0 1 θ-1‖ at hθ
    change δ/2 ≤ ‖circleMap 0 t θ-1‖
    linarith
  have good1 := hgood 1 (by norm_num) le_rfl (by simp; positivity)
  have hgt : ∀ᶠ n in atTop, 1/2 ≤ r n ∧ r n ≤ 1 ∧ |r n-1| ≤ δ/2 := by
    have hclose : ∀ᶠ n in atTop, |r n-1| < δ/2 := by
      simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp ht (δ/2) (by positivity))
    exact (ht.eventually (le_mem_nhds (by norm_num : (1/2:ℝ)<1))).and (hmax.and (hclose.mono (fun _ h ↦ h.le)))
  have measurable (t : ℝ) (hm : MapsTo (circleMap 0 t) A K) : AEStronglyMeasurable (u t) μ := by
    have hc := hfK.continuousOn.comp (continuous_circleMap 0 t).continuousOn hm
    exact (Real.measurable_log.comp_aemeasurable (hc.aemeasurable hA).norm).neg.aestronglyMeasurable
  have bound (t : ℝ) (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hm : MapsTo (circleMap 0 t) A K) :
      ∀ᵐ θ ∂μ, ‖u t θ‖ ≤ B θ := by
    filter_upwards [hAae,ae_restrict_of_ae (ae_restrict_of_ae (hb t ht0 ht1))] with θ hθ hl
    simpa only [u,Real.norm_eq_abs,abs_neg] using hl (hm hθ)
  have h1 := bound 1 (by norm_num) le_rfl good1
  have hBμ : Integrable B μ := (show Integrable B μθ from hB).restrict
  refine ⟨hBμ.mono' (measurable 1 good1) h1, ?_⟩
  let D := MeromorphicOn.divisor f K
  have Dfin := D.finiteSupport hK
  have hzAE : ∀ᵐ θ ∂μ, circleMap 0 1 θ ∉ D.support :=
    ae_restrict_of_ae (ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp
      ((Dfin.countable.preimage_circleMap 0 one_ne_zero).measure_zero volume)))
  have hn (z : ℂ) (hz : z ∈ K) (hd : z ∉ D.support) : f z ≠ 0 := by
    apply (hfK z hz).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
    have hzero : D z = 0 := not_ne_iff.mp hd
    change MeromorphicOn.divisor f K z = 0 at hzero
    rw [hfK.meromorphicOn.divisor_apply hz,WithTop.untop₀_eq_zero] at hzero
    exact hzero.resolve_right (hoK ⟨z,hz⟩)
  have hlim (θ : ℝ) (hθ : θ ∈ A) (hd : circleMap 0 1 θ ∉ D.support) :
      Tendsto (fun n ↦ u (r n) θ) atTop (𝓝 (u 1 θ)) := by
    have hp : Tendsto (fun n ↦ circleMap 0 (r n) θ) atTop (𝓝 (circleMap 0 1 θ)) := by
      simp only [circleMap_zero]
      exact ((Complex.continuous_ofReal.tendsto 1).comp ht).mul tendsto_const_nhds
    exact (((hfK _ (good1 hθ)).continuousAt.tendsto.comp hp).norm.log
      (norm_ne_zero_iff.mpr (hn _ (good1 hθ) hd))).neg
  have hlim' : ∀ᵐ θ ∂μ, Tendsto (fun n ↦ |u (r n) θ-u 1 θ|) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [hAae,hzAE] with θ hθ hd
    simpa using ((hlim θ hθ hd).sub_const (u 1 θ)).abs
  have hdct := tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (F := fun n θ ↦ |u (r n) θ-u 1 θ|) (f := fun _ ↦ (0:ℝ)) (fun θ ↦ B θ+B θ)
    (hgt.mono (fun n h ↦ ((measurable _ (hgood _ h.1 h.2.1 h.2.2)).sub (measurable 1 good1)).norm))
    (by
      filter_upwards [hgt] with n hn'
      filter_upwards [bound (r n) hn'.1 hn'.2.1 (hgood _ hn'.1 hn'.2.1 hn'.2.2),h1] with θ hθ hθ1
      simpa only [Real.norm_eq_abs,abs_abs] using
        (norm_sub_le (u (r n) θ) (u 1 θ)).trans (add_le_add hθ hθ1))
    (hBμ.add hBμ) hlim'
  simpa only [integral_zero] using hdct

end RiemannMasullo.PoissonBoundary

open Complex Metric Filter Set MeasureTheory
open scoped Topology
namespace RiemannMasullo.PoissonBoundary

local notation "Kdisk" => (closedBall (0:ℂ) 1 \ ({1} : Set ℂ) : Set ℂ)
local notation "μθ" => volume.restrict (Ioc (0:ℝ) (2*Real.pi))

private theorem circleAverage_negate (g : ℂ → ℝ) (r : ℝ) :
    Real.circleAverage (fun z ↦ -g z) 0 r = -Real.circleAverage g 0 r := by
  simp only [Real.circleAverage_def, intervalIntegral.integral_neg, smul_neg]

private theorem continuousOn_poisson_sphere {q : ℂ} {R : ℝ} (hq : q ∈ ball 0 R) :
    ContinuousOn (poissonKernel 0 q) (sphere 0 R) := by
  change ContinuousOn (fun z ↦ poissonKernel 0 q z) _
  simp only [poissonKernel_def, sub_zero]
  have hn : Continuous (fun z : ℂ ↦ ‖z‖ ^ 2 - ‖q‖ ^ 2) :=
    (continuous_norm.pow 2).sub continuous_const
  have hd : Continuous (fun z : ℂ ↦ ‖z-q‖ ^ 2) :=
    (continuous_id.sub continuous_const).norm.pow 2
  refine hn.continuousOn.div hd.continuousOn (fun z hz ↦ pow_ne_zero 2 (norm_ne_zero_iff.mpr
    (sub_ne_zero.mpr (fun he ↦ ?_))))
  exact (mem_ball_zero_iff.1 hq).ne (he ▸ mem_sphere_zero_iff_norm.1 hz)

/-- A bounded holomorphic function with finite order at each regular boundary
point has its full logarithmic boundary mean when the positive radial approach
to the single exceptional point has zero normalized logarithmic loss. -/
theorem circleIntegrable_log_norm_and_exists_radial_limit {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 → AnalyticAt ℂ f z ∧ analyticOrderAt f z ≠ ⊤)
    (hbound : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f z‖ ≤ 1)
    (hreal : ∀ q : ℝ, 1/2 ≤ q → q < 1 → f q ≠ 0)
    (hgrowth : Tendsto (fun q : ℝ ↦ (1-q) * |Real.log ‖f q‖|) (𝓝[<] 1) (𝓝 0)) :
    CircleIntegrable (fun z ↦ Real.log ‖f z‖) 0 1 ∧
      ∃ r : ℕ → ℝ, (∀ n, 1/2 < r n ∧ r n < 1) ∧ Tendsto r atTop (𝓝 1) ∧
        Tendsto (fun n ↦ Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 (r n)) atTop
          (𝓝 (Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 1)) := by
  classical
  have hK : AnalyticOnNhd ℂ f Kdisk := fun z hz ↦
    (hf z (mem_closedBall_zero_iff.mp hz.1) hz.2).1
  have ho (z : Kdisk) : meromorphicOrderAt f z ≠ ⊤ := by
    have hh := hf z (mem_closedBall_zero_iff.mp z.property.1) z.property.2
    rw [hh.1.meromorphicOrderAt_eq]
    obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp hh.2
    rw [←hn]
    exact WithTop.coe_ne_top
  have hinside : ball (0:ℂ) 1 ⊆ Kdisk := by
    intro z hz
    refine ⟨ball_subset_closedBall hz,?_⟩
    rintro ⟨rfl⟩
    simp at hz
  let D := MeromorphicOn.divisor f (ball (0:ℂ) 1)
  have hd : D.support.Countable :=
    (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete D.discreteSupport
  have hrad := ((hd.image (fun z : ℂ ↦ ‖z‖)).dense_compl ℝ)
  obtain ⟨r,_,hr,ht⟩ := hrad.exists_seq_strictMono_tendsto_of_lt (by norm_num : (1/2:ℝ)<1)
  have hp (n : ℕ) : 0 < r n := lt_trans (by norm_num) (hr n).1.1
  have hclosed (n : ℕ) : closedBall (0:ℂ) (r n) ⊆ ball 0 1 := closedBall_subset_ball (hr n).1.2
  have han (n : ℕ) := hK.mono ((hclosed n).trans hinside)
  have hnz (n : ℕ) (z : ℂ) (hz : z ∈ sphere 0 (r n)) : f z ≠ 0 := by
    have hrz := mem_sphere_zero_iff_norm.mp hz
    have hz' := hclosed n (sphere_subset_closedBall hz)
    have hn : z ∉ D.support := fun h ↦ (hr n).2 ⟨z,h,hrz⟩
    have hzero : D z = 0 := not_ne_iff.mp hn
    change MeromorphicOn.divisor f (ball 0 1) z = 0 at hzero
    rw [(hK.mono hinside).meromorphicOn.divisor_apply hz',WithTop.untop₀_eq_zero] at hzero
    exact (hK z (hinside hz')).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
      (hzero.resolve_right (ho ⟨z,hinside hz'⟩))
  let g (z : ℂ) := -Real.log ‖f z‖
  let u (θ : ℝ) := g (circleMap 0 1 θ)
  let U (q : ℝ) := |Real.log ‖f q‖|
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun θ ↦ g (circleMap 0 (r n) θ)) μθ := by
    have hc : Continuous (fun θ ↦ f (circleMap 0 (r n) θ)) :=
      (han n).continuousOn.comp_continuous (continuous_circleMap 0 (r n))
        (fun θ ↦ sphere_subset_closedBall (circleMap_mem_sphere 0 (hp n).le θ))
    exact (Real.measurable_log.comp hc.norm.measurable).neg.aestronglyMeasurable
  have hnonneg (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (θ : ℝ) : 0 ≤ g (circleMap 0 t θ) := by
    exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) (hbound _
      (by rw [norm_circleMap_zero,abs_of_nonneg ht0]; exact ht1)))
  have hbudget (q : ℝ) (hq : 1/2 ≤ q) (hq1 : q < 1) : ∀ᶠ n in atTop,
      CircleIntegrable (fun z ↦ poissonKernel 0 (q : ℂ) z * g z) 0 (r n) ∧
      Real.circleAverage (fun z ↦ poissonKernel 0 (q : ℂ) z * g z) 0 (r n) ≤ U q := by
    filter_upwards [ht.eventually (lt_mem_nhds hq1)] with n hn
    have hq0 : 0 ≤ q := by linarith
    have hqin : (q:ℂ) ∈ ball 0 (r n) := by simpa [mem_ball_zero_iff,abs_of_nonneg hq0] using hn
    refine ⟨ContinuousOn.circleIntegrable (hp n).le ?_,?_⟩
    · have hc := ((han n).continuousOn.mono sphere_subset_closedBall).norm.log
        (fun z hz ↦ norm_ne_zero_iff.mpr (hnz n z hz))
      exact (continuousOn_poisson_sphere hqin).mul hc.neg
    · have hl := RiemannMasullo.log_norm_le_circleAverage_poisson_of_boundary_nonzero
                   hqin (han n) (hreal q hq hq1) (hnz n)
      calc
        _ = -Real.circleAverage (poissonKernel 0 (q:ℂ) • (fun z ↦ Real.log ‖f z‖)) 0 (r n) := by
          rw [←circleAverage_negate]
          change Real.circleAverage (fun z ↦ poissonKernel 0 (q:ℂ) z * -Real.log ‖f z‖) 0 (r n) =
            Real.circleAverage (fun z ↦ -(poissonKernel 0 (q:ℂ) z * Real.log ‖f z‖)) 0 (r n)
          simp only [mul_neg]
        _ ≤ -Real.log ‖f q‖ := neg_le_neg hl
        _ ≤ U q := neg_le_abs _
  obtain ⟨hint,_,hlim⟩ := circleAverage_tendsto_of_poisson_budget
    r ht (.of_forall (fun n ↦ (hr n).1.2.le)) g u U hmeas
    (fun n ↦ .of_forall (hnonneg _ (hp n).le (hr n).1.2.le))
    (.of_forall (hnonneg 1 zero_le_one le_rfl))
    (fun _ hδ ↦ radial_log_local_L1 hK ho ht (.of_forall (fun n ↦ (hr n).1.2.le)) hδ)
    hbudget hgrowth
  have hmean : (2*Real.pi)⁻¹ * (∫ θ in Ioc (0:ℝ) (2*Real.pi), u θ) =
      Real.circleAverage g 0 1 := by
    simp only [Real.circleAverage_def,smul_eq_mul,intervalIntegral.integral_of_le Real.two_pi_pos.le,u]
  rw [hmean] at hlim
  change Tendsto (fun n ↦ Real.circleAverage (fun z ↦ -Real.log ‖f z‖) 0 (r n)) atTop
    (𝓝 (Real.circleAverage (fun z ↦ -Real.log ‖f z‖) 0 1)) at hlim
  simp_rw [circleAverage_negate] at hlim
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mpr ?_,
    r, fun n ↦ (hr n).1,ht,?_⟩
  · simpa only [u,g,neg_neg] using
      (show IntegrableOn (fun θ ↦ -u θ) (Ioc (0:ℝ) (2*Real.pi)) from hint.neg)
  · simpa only [neg_neg] using hlim.neg

end RiemannMasullo.PoissonBoundary
