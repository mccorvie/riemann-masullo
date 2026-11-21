module

public import RiemannMasullo.AppC_LCTVS.Sec5a
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Thickening
import RiemannMasullo.ForMathlib.Analysis.Calculus.Deriv.Weak
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.HahnBanach
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.Connected
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.WeakSpace
import RiemannMasullo.ForMathlib.MeasureTheory.VectorMeasure.Integral

/-!
# Holomorphic and meromorphic vector-valued functions

Masullo, Appendix C, §§C.5.2–C.5.4. Functions on a subset of the plane are
represented by ambient functions restricted to that subset.
-/

@[expose] public noncomputable section

open Bornology Filter Function MeasureTheory Set Topology
open scoped ContDiff

namespace RiemannMasullo

attribute [local instance] IsTopologicalAddGroup.rightUniformSpace

section Holomorphy

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable {Ω : Set ℂ}

/-- Paper: Definition C.5.2.1(1), p. 737. Weak continuity is continuity after
evaluation by each continuous complex-linear functional. -/
def WeaklyContinuousOn (f : ℂ → E) (Ω : Set ℂ) : Prop :=
  ∀ φ : StrongDual ℂ E, ContinuousOn (φ ∘ f) Ω

/-- Paper: Definition C.5.2.1(2), p. 737. Weak continuous differentiability through
order `k` is continuous differentiability through that order after scalar evaluation.
Deviation: The scalar `C^k` condition uses real derivatives on the complex plane. -/
def WeaklyContDiffOrderOn (k : ℕ) (f : ℂ → E) (Ω : Set ℂ) : Prop :=
  ∀ φ : StrongDual ℂ E, ContDiffOn ℝ k (φ ∘ f) Ω

/-- Paper: Definition C.5.2.1(3), p. 737. Weak holomorphy is weak differentiability
over the complex field as in §C.5.1. -/
abbrev WeaklyHolomorphicOn (f : ℂ → E) (Ω : Set ℂ) : Prop :=
  WeaklyDifferentiableOn ℂ f Ω

/-- Paper: Definition C.5.2.1(1–3), p. 737. Scalar testing on the complex line
recovers ordinary continuity, real smoothness of the specified order, and holomorphy.
Deviation: This is a sanity check for the three weak definitions. -/
theorem weakComplexRegularity_iff (f : ℂ → ℂ) (k : ℕ) :
    (WeaklyContinuousOn f Ω ↔ ContinuousOn f Ω) ∧
      (WeaklyContDiffOrderOn k f Ω ↔ ContDiffOn ℝ k f Ω) ∧
      (WeaklyHolomorphicOn f Ω ↔ DifferentiableOn ℂ f Ω) := by
  refine ⟨⟨fun h ↦ h (ContinuousLinearMap.id ℂ ℂ), ?_⟩,
    ⟨fun h ↦ h (ContinuousLinearMap.id ℂ ℂ), ?_⟩,
    ⟨fun h ↦ h (ContinuousLinearMap.id ℂ ℂ), ?_⟩⟩
  · exact fun hf φ ↦ φ.continuous.comp_continuousOn hf
  · exact fun hf φ ↦ (φ.restrictScalars ℝ).contDiff.comp_contDiffOn hf
  · exact fun hf φ ↦ φ.differentiable.comp_differentiableOn hf

variable [ContinuousSMul ℂ E]

/-- Paper: Definition C.5.2.1(4), p. 737. Holomorphy is differentiability over
the complex field with values in the given topological vector space. -/
abbrev VectorHolomorphicOn (f : ℂ → E) (Ω : Set ℂ) : Prop :=
  DifferentiableOn ℂ f Ω

/-- Paper: (C.5.2.1), p. 737. On an open set, holomorphy means the complex
difference quotients have a limit in the target at every point. -/
theorem vectorHolomorphicOn_iff_tendsto (hΩ : IsOpen Ω) [IsTopologicalAddGroup E]
    (f : ℂ → E) :
    VectorHolomorphicOn f Ω ↔ ∀ z ∈ Ω, ∃ v : E,
      Tendsto (fun w ↦ (w - z)⁻¹ • (f w - f z)) (𝓝[≠] z) (𝓝 v) := by
  have slope_iff (z : ℂ) (v : E) : HasDerivAt f v z ↔
      Tendsto (fun w ↦ (w - z)⁻¹ • (f w - f z)) (𝓝[≠] z) (𝓝 v) := by
    rw [hasDerivAt_iff_hasFDerivAt, ← hasFDerivWithinAt_univ,
      ← hasFDerivWithinAt_sdiff_singleton_self, ← Set.compl_eq_univ_sdiff,
      hasFDerivWithinAt_iff_isLittleOTVS]
    change (fun w ↦ f w - f z - (w - z) • v) =o[ℂ; 𝓝[≠] z] (fun w ↦ w - z) ↔ _
    rw [Asymptotics.isLittleOTVS_iff_tendsto_inv_smul (by
      filter_upwards with w hw
      simp [sub_eq_zero.mp hw])]
    conv_rhs => rw [← tendsto_sub_nhds_zero_iff]
    apply tendsto_congr'
    filter_upwards [eventually_mem_nhdsWithin] with w hw
    simp [smul_sub, inv_smul_smul₀ (sub_ne_zero.mpr hw)]
  constructor
  · intro hf z hz
    obtain ⟨L, hL⟩ := hf z hz
    exact ⟨L 1, (slope_iff z _).mp (hL.hasFDerivAt (hΩ.mem_nhds hz)).hasDerivAt⟩
  · intro hf z hz
    obtain ⟨v, hv⟩ := hf z hz
    exact ⟨_, ((slope_iff z v).mpr hv).hasFDerivAt.hasFDerivWithinAt⟩

omit [ContinuousSMul ℂ E] in
/-- A continuous linear map sends the derivative of a vector-valued holomorphic
function to the derivative of the composite. -/
private theorem VectorHolomorphicOn.hasDerivAt_comp
    [IsTopologicalAddGroup E] {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] {f : ℂ → E}
    (hf : VectorHolomorphicOn f Ω) (hΩ : IsOpen Ω) (j : E →L[ℂ] F) (x : Ω) :
    HasDerivAt (j ∘ f) (j (deriv f x)) (x : ℂ) := by
  have h := hf.hasFDerivAt (hΩ.mem_nhds x.property)
  have hj : HasFDerivAt (j ∘ f) (j.comp (fderiv ℂ f x)) (x : ℂ) := by
    apply HasFDerivAt.of_isLittleOTVS
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
      using j.isBigOTVS_comp.trans_isLittleOTVS h.isLittleOTVS
  exact hj.hasDerivAt

/-- Paper: Remark C.5.2.2, p. 737. On a complex domain, holomorphy agrees with
the strong continuous differential of §C.5.1 in one complex variable. -/
theorem vectorHolomorphicOn_iff_vectorContDiffOn (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    [IsTopologicalAddGroup E] [T2Space E] [PolynormableSpace ℂ E] (f : ℂ → E) :
    VectorHolomorphicOn f Ω ↔ VectorContDiffOn (k := ℂ) Ω f := by
  clear hconn
  have scalar_remainder (x : Ω) (v : E) (φ : StrongDual ℂ E) :
      HasDerivWithinAt (φ ∘ f) (φ v) Ω (x : ℂ) ↔
        Tendsto (fun y : ℂ ↦ ((‖y - (x : ℂ)‖⁻¹ : ℝ) : ℂ) *
          (φ (f y) - φ (f x) - (y - (x : ℂ)) * φ v))
          (𝓝[Ω \ {(x : ℂ)}] (x : ℂ)) (𝓝 0) := by
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← hasFDerivWithinAt_sdiff_singleton_self,
      ← hasDerivWithinAt_iff_hasFDerivWithinAt, hasDerivWithinAt_iff_tendsto]
    conv_rhs => rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Function.comp_apply, smul_eq_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
  let ev (φ : StrongDual ℂ E) : PettisWeakCompletion E →L[ℂ] ℂ := WeakBilin.eval _ φ
  have heval (φ : StrongDual ℂ E) (v : E) : ev φ (toPettisWeakCompletion E v) = φ v := rfl
  let remainder (D : Ω × ℂ → E) (x : Ω) (y : ℂ) : PettisWeakCompletion E :=
    ((‖y - (x : ℂ)‖⁻¹ : ℝ) : ℂ) •
      (toPettisWeakCompletion E (f y) - toPettisWeakCompletion E (f x) -
        (toPettisWeakCompletion E ∘ D) (x, y - (x : ℂ)))
  constructor
  · intro hf
    have hcontinuous : Continuous (fun x : Ω ↦ deriv f x) := by
      rw [continuous_iff_continuousAt]
      intro x
      apply ((PolynormableSpace.withSeminorms ℂ E).tendsto_nhds _ _).2
      intro p ε hε
      -- Put the seminorm topology on a copy of E and pass to its Banach completion.
      let e : ULift.{0} E ≃ₗ[ℂ] E := ULift.moduleEquiv
      let q : Seminorm ℂ (ULift.{0} E) := p.val.comp e.toLinearMap
      let group : SeminormedAddCommGroup (ULift.{0} E) := q.toSeminormedAddCommGroup
      let : UniformSpace (ULift.{0} E) := group.toUniformSpace
      let : TopologicalSpace (ULift.{0} E) := group.toUniformSpace.toTopologicalSpace
      let : NormedSpace ℂ (ULift.{0} E) := ⟨fun c v ↦ (map_smul_eq_mul q c v).le⟩
      let j₀ := UniformSpace.Completion.toComplL (S := ℂ) (α := ULift.{0} E)
      have he : Continuous e.symm := by
        rw [continuous_iff_continuousAt]
        intro v
        apply Metric.tendsto_nhds.mpr
        intro r hr
        have hp : Continuous (fun y : E ↦ p.val (y - v)) :=
          p.property.comp (continuous_id.sub continuous_const)
        simp only [dist_eq_norm, ← map_sub]
        change ∀ᶠ y : E in 𝓝 v, p.val (y - v) < r
        exact (hp.continuousAt (x := v)).eventually_lt continuousAt_const (by simpa using hr)
      let j : E →L[ℂ] UniformSpace.Completion (ULift.{0} E) :=
        ⟨j₀.toLinearMap.comp e.symm.toLinearMap, j₀.continuous.comp he⟩
      have hg : DifferentiableOn ℂ (j ∘ f) Ω := fun y hy ↦
        (hf.hasDerivAt_comp hΩ j ⟨y, hy⟩).differentiableAt.differentiableWithinAt
      have hj (y : Ω) : deriv (j ∘ f) y = j (deriv f y) := (hf.hasDerivAt_comp hΩ j y).deriv
      have ht : Continuous (fun y : Ω ↦ j (deriv f y)) :=
        (continuousOn_iff_continuous_domRestrict.mp (hg.deriv hΩ).continuousOn).congr
          fun y ↦ hj y
      filter_upwards [Metric.tendsto_nhds.mp (ht.continuousAt (x := x)) ε hε] with y hy
      rw [dist_eq_norm, ← map_sub] at hy
      change ‖(↑(e.symm (deriv f y - deriv f x)) : UniformSpace.Completion (ULift.{0} E))‖ < ε at hy
      rwa [UniformSpace.Completion.norm_coe] at hy
    let D : Ω × ℂ → E := fun p ↦ p.2 • deriv f p.1
    have hD : Continuous D := continuous_snd.smul (hcontinuous.comp continuous_fst)
    refine ⟨D, hD, continuous_toPettisWeakCompletion.comp hD, fun x ↦ ?_⟩
    refine ⟨⟨(toPettisWeakCompletion E).comp
      ((LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (deriv f x)), fun _ ↦ rfl⟩, ?_⟩
    apply (WeakBilin.tendsto_iff_forall_eval_tendsto _ injective_id).2
    intro φ
    change Tendsto (fun y ↦ ev φ (remainder D x y)) (𝓝[Ω \ {(x : ℂ)}] (x : ℂ)) (𝓝 (ev φ 0))
    simpa only [remainder, D, Function.comp_apply, map_zero, map_sub, map_smul, heval,
      smul_eq_mul] using (scalar_remainder x _ φ).mp (hf.hasDerivAt_comp hΩ φ x).hasDerivWithinAt
  · rintro ⟨D, hD, _, hweak⟩
    let d : Ω → E := fun x ↦ D (x, 1)
    have hd : Continuous d := hD.comp (continuous_id.prodMk continuous_const)
    have hscalar (φ : StrongDual ℂ E) (x : Ω) :
        HasDerivAt (φ ∘ f) (φ (d x)) (x : ℂ) := by
      obtain ⟨⟨L, hL⟩, hrem⟩ := hweak x
      have hdir (w : ℂ) : ev φ (toPettisWeakCompletion E (D (x, w))) = w * φ (d x) := by
        change ev φ ((toPettisWeakCompletion E ∘ D) (x, w)) = _
        rw [hL w, show L w = w • L 1 by rw [← map_smul, smul_eq_mul, mul_one], ← hL 1,
          map_smul, Function.comp_apply, heval, smul_eq_mul]
      apply HasDerivWithinAt.hasDerivAt _ (hΩ.mem_nhds x.property)
      apply (scalar_remainder x _ φ).mpr
      have h := (WeakBilin.tendsto_iff_forall_eval_tendsto _ injective_id).mp hrem φ
      change Tendsto (fun y ↦ ev φ (remainder D x y)) _ (𝓝 (ev φ 0)) at h
      simpa only [Function.comp_apply, remainder, map_zero, map_smul, map_sub, hdir, heval,
        smul_eq_mul] using h
    apply (vectorHolomorphicOn_iff_tendsto hΩ f).2
    intro z hz
    let x : Ω := ⟨z, hz⟩
    refine ⟨d x, ((PolynormableSpace.withSeminorms ℂ E).tendsto_nhds _ _).2 ?_⟩
    intro p ε hε
    have hnear : ∀ᶠ y : Ω in 𝓝 x, p.val (d y - d x) < ε / 2 :=
      (p.property.comp (hd.sub continuous_const)).continuousAt.eventually_lt
        continuousAt_const (by simpa [d] using half_pos hε)
    obtain ⟨r, hr, hcontrol⟩ := Metric.eventually_nhds_iff.mp hnear
    have hnear' : Ω ∩ Metric.ball z r ∈ 𝓝 z :=
      inter_mem (hΩ.mem_nhds hz) (Metric.ball_mem_nhds z hr)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear'
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hδ),
      self_mem_nhdsWithin] with w hw hwz
    have hwz' : w - z ≠ 0 := sub_ne_zero.mpr hwz
    obtain ⟨φ, hφ, heq⟩ := exists_dual_norm_eq_seminorm p.val p.property
      ((w - z)⁻¹ • (f w - f z) - d x)
    -- Estimate the scalar remainder using a functional attaining its seminorm.
    let g (y : ℂ) := φ (f y) - y * φ (d x)
    have hg (y : ℂ) (hy : y ∈ Metric.ball z δ) :
        HasDerivAt g (φ (d ⟨y, (hball hy).1⟩ - d x)) y := by
      simpa [g, Pi.sub_def, Function.comp_apply, map_sub] using
        (hscalar φ ⟨y, (hball hy).1⟩).sub ((hasDerivAt_id' y).mul_const (φ (d x)))
    have hmean : ‖g w - g z‖ ≤ ε / 2 * ‖w - z‖ :=
      (convex_ball z δ).norm_image_sub_le_of_norm_deriv_le
        (fun y hy ↦ (hg y hy).differentiableAt) (fun y hy ↦ by
          rw [(hg y hy).deriv]
          exact (hφ _).trans (hcontrol (y := ⟨y, (hball hy).1⟩) (hball hy).2).le)
        (Metric.mem_ball_self hδ) hw
    rw [← heq]
    have hquot : φ ((w - z)⁻¹ • (f w - f z) - d x) = (w - z)⁻¹ • (g w - g z) := by
      simp only [g, map_sub, map_smul, smul_eq_mul]
      field_simp [hwz']
      ring
    rw [hquot, norm_smul, norm_inv]
    apply lt_of_le_of_lt _ (half_lt_self hε)
    exact (inv_mul_le_iff₀ (norm_pos_iff.mpr hwz')).2 (by simpa [mul_comm] using hmean)

end Holomorphy

/-- Paper: Arc convention before Theorem C.5.2.4, p. 738. A contour is a closed,
continuous path with finitely many continuously differentiable pieces.
Deviation: The parameter interval is normalized to `[0, 1]` and the parametrization
is extended continuously to the real line. -/
structure ComplexContour where
  toContinuousMap : C(ℝ, ℂ)
  closed : toContinuousMap 1 = toContinuousMap 0
  piecewiseContDiff : ∃ (n : ℕ) (t : Fin (n + 1) → ℝ),
    StrictMono t ∧ t 0 = 0 ∧ t (Fin.last n) = 1 ∧
      ∀ i : Fin n, ContDiffOn ℝ 1 toContinuousMap (Icc (t i.castSucc) (t i.succ))

/-- Paper: Arc convention before Theorem C.5.2.4, p. 738. The trace is the image of
the parameter interval. -/
def ComplexContour.trace (γ : ComplexContour) : Set ℂ :=
  γ.toContinuousMap '' Icc 0 1

/-- Paper: Remark C.5.2.5, p. 738. The contour measure is the pushforward of
Lebesgue measure weighted by the complex velocity on the parameter interval. -/
def ComplexContour.measure (γ : ComplexContour) : ComplexMeasure ℂ :=
  ((volume.restrict (Icc (0 : ℝ) 1)).withDensityᵥ
    (deriv (fun t ↦ γ.toContinuousMap t))).map γ.toContinuousMap

/-- Paper: Winding number notation in Theorem C.5.4.1, p. 741. The winding number
off the trace is expressed by its normalized scalar contour integral.
Deviation: It is represented by its value in `ℂ`. -/
def ComplexContour.index (γ : ComplexContour) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    (PettisMeasure.complex γ.measure).scalarIntegral (fun w ↦ (w - z)⁻¹)

/-- Paper: Contours in Theorem C.5.2.4, p. 738. A positively oriented simple
contour is injective before the repeated endpoint and has index zero or one off its trace. -/
def PositiveSimpleContour :=
  { γ : ComplexContour // InjOn γ.toContinuousMap (Ico 0 1) ∧
    ∀ z ∉ γ.trace, γ.index z = 0 ∨ γ.index z = 1 }

/-- Paper: Contour interior in Theorem C.5.2.4, p. 738. The interior of a positively
oriented simple contour consists of points off the trace with index one. -/
def PositiveSimpleContour.interior (γ : PositiveSimpleContour) : Set ℂ :=
  {z | z ∉ γ.val.trace ∧ γ.val.index z = 1}

/-- Paper: Contours in Theorem C.5.2.4, p. 738. The counterclockwise round circle has
the usual trace and interior, and its velocity measure gives the reciprocal integral.
Deviation: This is a sanity check for the contour, measure, and index definitions. -/
theorem exists_positiveSimpleContour_circle (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ γ : PositiveSimpleContour,
      (∀ t ∈ Icc (0 : ℝ) 1, γ.val.toContinuousMap t = circleMap z r (2 * Real.pi * t)) ∧
      γ.val.trace = Metric.sphere z r ∧ γ.interior = Metric.ball z r ∧ γ.val.index z = 1 ∧
      HasPettisIntegral (.complex γ.val.measure) (fun w ↦ (w - z)⁻¹)
        (2 * (Real.pi : ℂ) * Complex.I) := by
  let p (t : ℝ) := circleMap z r (2 * Real.pi * t)
  have hscale : ContDiff ℝ 1 (fun t : ℝ ↦ 2 * Real.pi * t) := contDiff_const.mul contDiff_id
  have hp : ContDiff ℝ 1 p := (contDiff_circleMap z r).comp hscale
  let γ : ComplexContour :=
    { toContinuousMap := ⟨p, hp.continuous⟩
      closed := by simpa [p] using periodic_circleMap z r 0
      piecewiseContDiff := by
        refine ⟨1, fun i ↦ (i.val : ℝ), ?_, by norm_num, by norm_num, fun _ ↦ hp.contDiffOn⟩
        intro i j hij
        change (i.val : ℝ) < (j.val : ℝ)
        exact_mod_cast (show i.val < j.val from hij) }
  have htrace : γ.trace = Metric.sphere z r := by
    change p '' Icc 0 1 = _
    simp only [p, ← image_image, image_mul_left_Icc' Real.two_pi_pos, mul_zero, mul_one]
    apply le_antisymm
    · rintro _ ⟨θ, _, rfl⟩
      exact circleMap_mem_sphere z hr.le θ
    · rw [← show circleMap z r '' Ioc 0 (2 * Real.pi) = Metric.sphere z r by
        simpa only [abs_of_pos hr] using image_circleMap_Ioc z r]
      exact image_mono Ioc_subset_Icc_self
  have hinj : InjOn γ.toContinuousMap (Ico 0 1) := by
    intro s hs t ht heq
    have hmaps : MapsTo (fun x : ℝ ↦ 2 * Real.pi * x) (Ico 0 1) (Ico 0 (2 * Real.pi)) := by
      intro x hx
      exact ⟨mul_nonneg Real.two_pi_pos.le hx.1, by
        simpa only [mul_one] using mul_lt_mul_of_pos_left hx.2 Real.two_pi_pos⟩
    have hang := (injOn_circleMap_of_abs_sub_le' (c := z) hr.ne'
      (a := 0) (b := 2 * Real.pi) (by simp)) (hmaps hs) (hmaps ht) heq
    exact mul_left_cancel₀ Real.two_pi_pos.ne' hang
  have hvel (t : ℝ) :
      deriv p t = (2 * Real.pi) • deriv (circleMap z r) (2 * Real.pi * t) := by
    rw [deriv_circleMap]
    exact ((hasDerivAt_circleMap z r (2 * Real.pi * t)).scomp t
      (by simpa only [mul_one] using (hasDerivAt_id' t).const_mul (2 * Real.pi))).deriv
  have hcontVel : Continuous (deriv p) := by
    rw [show deriv p = _ from funext hvel]
    simp only [deriv_circleMap]
    fun_prop
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let ν : ComplexMeasure ℝ := μ.withDensityᵥ (deriv p)
  have hvelInt : Integrable (deriv p) μ :=
    hcontVel.continuousOn.integrableOn_compact isCompact_Icc
  have hintegral {f : ℂ → ℂ} (hfm : Measurable f) (hfc : ContinuousOn f (Metric.sphere z r)) :
      Integrable f (PettisMeasure.complex γ.measure).variation ∧
        (PettisMeasure.complex γ.measure).scalarIntegral f = circleIntegral f z r := by
    have hcomp : ContinuousOn (f ∘ p) (Icc 0 1) :=
      hfc.comp hp.continuous.continuousOn (fun t _ ↦ circleMap_mem_sphere z hr.le _)
    have hfi : ν.Integrable (f ∘ p) := by
      change Integrable (f ∘ p) (μ.withDensityᵥ (deriv p)).variation
      rw [Measure.variation_withDensityᵥ hvelInt]
      exact (integrable_withDensity_iff_integrable_smul hcontVel.nnNorm.measurable).2
        ((hcontVel.norm.continuousOn.smul hcomp).integrableOn_compact isCompact_Icc)
    have hfm' := hfm.aestronglyMeasurable (μ := ν.variation.map p)
    refine ⟨hfi.map hfm', ?_⟩
    change (ν.map p).integral f (ContinuousLinearMap.mul ℝ ℂ) = _
    rw [VectorMeasure.integral_map hp.continuous.measurable hfm' hfi]
    change (μ.withDensityᵥ (deriv p)).integral (f ∘ p) (ContinuousLinearMap.mul ℝ ℂ) = _
    rw [VectorMeasure.integral_withDensityᵥ_mul hvelInt hcontVel.measurable hfi]
    change (∫ t in Icc (0 : ℝ) 1, f (p t) * deriv p t) = _
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    simp_rw [hvel, mul_smul_comm, mul_comm (f (p _))]
    let F (θ : ℝ) := deriv (circleMap z r) θ • f (circleMap z r θ)
    change (∫ t in (0 : ℝ)..1, (2 * Real.pi) • F (2 * Real.pi * t)) = _
    rw [intervalIntegral.integral_smul, intervalIntegral.smul_integral_comp_mul_left]
    simp [circleIntegral, F]
  have hkernel (w : ℂ) (hw : w ∉ Metric.sphere z r) :
      Integrable (fun v ↦ (v - w)⁻¹) (PettisMeasure.complex γ.measure).variation ∧
        (PettisMeasure.complex γ.measure).scalarIntegral (fun v ↦ (v - w)⁻¹) =
          circleIntegral (fun v ↦ (v - w)⁻¹) z r := by
    apply hintegral ((measurable_id.sub_const w).inv)
    exact (continuousOn_id.sub continuousOn_const).inv₀ fun v hv ↦
      sub_ne_zero.mpr (ne_of_mem_of_not_mem hv hw)
  have hconst : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hnotSphere {w : ℂ} (hw : w ∈ Metric.ball z r) : w ∉ Metric.sphere z r :=
    fun hs ↦ (Metric.mem_ball.mp hw).ne (Metric.mem_sphere.mp hs)
  have hballIndex (w : ℂ) (hw : w ∈ Metric.ball z r) : γ.index w = 1 := by
    rw [ComplexContour.index, (hkernel w (hnotSphere hw)).2,
      circleIntegral.integral_sub_inv_of_mem_ball hw, inv_mul_cancel₀ hconst]
  have houtIndex (w : ℂ) (hw : w ∉ Metric.closedBall z r) : γ.index w = 0 := by
    have hd : DifferentiableOn ℂ (fun v : ℂ ↦ (v - w)⁻¹) (Metric.closedBall z r) :=
      (differentiableOn_id.sub_const w).inv fun v hv ↦
        sub_ne_zero.mpr (ne_of_mem_of_not_mem hv hw)
    have hc : DiffContOnCl ℂ (fun v : ℂ ↦ (v - w)⁻¹) (Metric.ball z r) :=
      (show DifferentiableOn ℂ _ (closure (Metric.ball z r)) by
        rwa [closure_ball z hr.ne']).diffContOnCl
    rw [ComplexContour.index, (hkernel w (fun hs ↦ hw (Metric.sphere_subset_closedBall hs))).2,
      hc.circleIntegral_eq_zero hr.le, mul_zero]
  have houtside {w : ℂ} (hs : w ∉ Metric.sphere z r) (hb : w ∉ Metric.ball z r) :
      w ∉ Metric.closedBall z r := by
    intro hc
    apply hb
    rw [← Metric.closedBall_sdiff_sphere]
    exact ⟨hc, hs⟩
  let Γ : PositiveSimpleContour := ⟨γ, hinj, fun w hw ↦ by
    rw [htrace] at hw
    by_cases hb : w ∈ Metric.ball z r
    · exact Or.inr (hballIndex w hb)
    · exact Or.inl (houtIndex w (houtside hw hb))⟩
  have hz : z ∈ Metric.ball z r := Metric.mem_ball_self hr
  have hzs := hnotSphere hz
  refine ⟨Γ, fun _ _ ↦ rfl, htrace, ?_, hballIndex z hz, ?_⟩
  · ext w
    change w ∉ γ.trace ∧ γ.index w = 1 ↔ w ∈ Metric.ball z r
    rw [htrace]
    constructor
    · rintro ⟨hs, hi⟩
      by_contra hb
      exact zero_ne_one ((houtIndex w (houtside hs hb)).symm.trans hi)
    · exact fun hw ↦ ⟨hnotSphere hw, hballIndex w hw⟩
  · refine (pettisIntegral_complex_iff _ _ _).2.2.mpr ⟨(hkernel z hzs).1, ?_⟩
    rw [(hkernel z hzs).2, circleIntegral.integral_sub_inv_of_mem_ball hz]

section ContourIntegral

open Complex intervalIntegral Metric

private lemma ComplexContour.partition_nonempty
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht0 : t 0 = 0) (ht1 : t (Fin.last n) = 1) :
    0 < n := by
  cases n with
  | zero =>
    have : (0 : ℝ) = 1 := by simpa [Fin.last_zero, ht0] using ht1
    exact absurd this zero_ne_one
  | succ n => exact Nat.succ_pos n

private lemma ComplexContour.exists_piece
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : StrictMono t) (ht0 : t 0 = 0)
    (ht1 : t (Fin.last n) = 1) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ i : Fin n, s ∈ Icc (t i.castSucc) (t i.succ) := by
  have hn := ComplexContour.partition_nonempty ht0 ht1
  classical
  let S : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => s ≤ t i)
  have hne : S.Nonempty := by
    refine ⟨Fin.last n, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rw [ht1]
    exact hs.2
  have hmem := Finset.min'_mem S hne
  have hle : s ≤ t (S.min' hne) := (Finset.mem_filter.mp hmem).2
  have hpred (j : Fin (n + 1)) (hj : j < S.min' hne) : ¬ s ≤ t j := by
    intro hjs
    have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjs⟩
    exact (Finset.min'_le S j hjS).not_gt hj
  cases hmin : S.min' hne using Fin.cases with
  | zero =>
    have hs0 : s = 0 := le_antisymm (by simpa [hmin, ht0] using hle) hs.1
    refine ⟨⟨0, hn⟩, ?_, ?_⟩
    · simp [hs0, ht0]
    · have : t 0 ≤ t (Fin.succ (⟨0, hn⟩ : Fin n)) :=
        ht.monotone (Fin.zero_le _)
      simpa [hs0, ht0] using this
  | succ k =>
    refine ⟨k, ?_, ?_⟩
    · have hlt : k.castSucc < S.min' hne := by simpa [hmin] using k.castSucc_lt_succ
      exact (lt_of_not_ge (hpred k.castSucc hlt)).le
    · simpa [hmin] using hle

/-- The velocity of a piecewise `C¹` contour is integrable on the parameter interval. -/
lemma ComplexContour.integrable_deriv (g : ComplexContour) :
    Integrable (fun t : ℝ => deriv g.toContinuousMap t) (volume.restrict (Icc (0 : ℝ) 1)) := by
  obtain ⟨n, t, ht, ht0, ht1, hcd⟩ := g.piecewiseContDiff
  have hpiece (i : Fin n) :
      IntegrableOn (fun s : ℝ => deriv g.toContinuousMap s)
        (Icc (t i.castSucc) (t i.succ)) := by
    have hab : t i.castSucc < t i.succ := ht i.castSucc_lt_succ
    have hu : UniqueDiffOn ℝ (Icc (t i.castSucc) (t i.succ)) := uniqueDiffOn_Icc hab
    have hcont : ContinuousOn (derivWithin g.toContinuousMap (Icc (t i.castSucc) (t i.succ)))
        (Icc (t i.castSucc) (t i.succ)) :=
      (hcd i).continuousOn_derivWithin hu le_rfl
    have hint : IntegrableOn (derivWithin g.toContinuousMap (Icc (t i.castSucc) (t i.succ)))
        (Icc (t i.castSucc) (t i.succ)) :=
      hcont.integrableOn_compact isCompact_Icc
    have heq : EqOn (deriv g.toContinuousMap)
        (derivWithin g.toContinuousMap (Icc (t i.castSucc) (t i.succ)))
        (Ioo (t i.castSucc) (t i.succ)) := by
      intro s hs
      exact (derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)).symm
    have hioo : IntegrableOn (deriv g.toContinuousMap) (Ioo (t i.castSucc) (t i.succ)) :=
      (hint.mono_set Ioo_subset_Icc_self).congr_fun heq.symm measurableSet_Ioo
    exact (integrableOn_congr_set_ae (Ioo_ae_eq_Icc (a := t i.castSucc)
      (b := t i.succ))).1 hioo
  have hunion : IntegrableOn (fun s : ℝ => deriv g.toContinuousMap s)
      (⋃ i : Fin n, Icc (t i.castSucc) (t i.succ)) :=
    (integrableOn_finite_iUnion).2 hpiece
  refine hunion.mono_set ?_
  intro s hs
  obtain ⟨i, hi⟩ := ComplexContour.exists_piece ht ht0 ht1 hs
  exact mem_iUnion.2 ⟨i, hi⟩

/-- The contour variation is supported on the trace. -/
lemma ComplexContour.variation_compl_trace (g : ComplexContour) :
    (PettisMeasure.complex g.measure).variation (g.trace)ᶜ = 0 := by
  let p : ℝ → ℂ := g.toContinuousMap
  let m : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let n : ComplexMeasure ℝ := m.withDensityᵥ (deriv p)
  have hvel : Integrable (deriv p) m := g.integrable_deriv
  have hvar : n.variation = m.withDensity (fun t => ‖deriv p t‖ₑ) :=
    Measure.variation_withDensityᵥ hvel
  have htrace : IsClosed g.trace :=
    (isCompact_Icc.image g.toContinuousMap.continuous).isClosed
  let pre : Set ℝ := Set.preimage p (g.traceᶜ)
  have hpre : MeasurableSet pre :=
    g.toContinuousMap.continuous.measurable (htrace.measurableSet.compl)
  have hzero_m : m pre = 0 := by
    rw [Measure.restrict_apply' measurableSet_Icc]
    convert measure_empty (μ := volume)
    ext t
    simp only [pre, mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false,
      not_and]
    intro ht htI
    exact ht ⟨t, htI, rfl⟩
  have hzero_n : n.variation pre = 0 := by
    rw [hvar, withDensity_apply (fun t => ‖deriv p t‖ₑ) hpre]
    exact setLIntegral_measure_zero _ _ hzero_m
  have hmap : (n.variation.map p) (g.traceᶜ) = 0 := by
    rw [Measure.map_apply g.toContinuousMap.continuous.measurable htrace.measurableSet.compl]
    exact hzero_n
  have hle : (n.map p).variation (g.traceᶜ) ≤ (n.variation.map p) (g.traceᶜ) :=
    VectorMeasure.variation_map_le _
  exact le_antisymm (hle.trans_eq hmap) bot_le

/-- A function continuous on the trace is integrable against the contour variation, and its
scalar integral is the parameter integral against the velocity. -/
lemma ComplexContour.scalarIntegral_eq_intervalIntegral (g : ComplexContour) {f : ℂ → ℂ}
    (hf : ContinuousOn f g.trace) :
    Integrable f (PettisMeasure.complex g.measure).variation ∧
      (PettisMeasure.complex g.measure).scalarIntegral f =
        ∫ t in (0 : ℝ)..1, f (g.toContinuousMap t) * deriv g.toContinuousMap t := by
  let p : C(ℝ, ℂ) := g.toContinuousMap
  let m : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let n : ComplexMeasure ℝ := m.withDensityᵥ (deriv (p : ℝ → ℂ))
  have hvel : Integrable (deriv (p : ℝ → ℂ)) m := g.integrable_deriv
  have hclosed : IsClosed g.trace :=
    (isCompact_Icc.image p.continuous).isClosed
  let fRes : C(g.trace, ℂ) :=
    ⟨fun z => f z.1, ContinuousOn.comp_continuous hf continuous_subtype_val (fun z => z.2)⟩
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq hclosed fRes
  have hagree (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : F (p t) = f (p t) := by
    have hw : p t ∈ g.trace := ⟨t, ht, rfl⟩
    have := congrFun (congrArg ContinuousMap.toFun hF) ⟨p t, hw⟩
    simpa [fRes] using this
  have hcomp : ContinuousOn (fun t : ℝ => F (p t)) (Icc (0 : ℝ) 1) :=
    F.continuous.comp_continuousOn p.continuous.continuousOn
  have hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖F (p t)‖ ≤ C := by
    have hne : (Icc (0 : ℝ) 1).Nonempty := nonempty_Icc.2 zero_le_one
    obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcomp.norm
    exact ⟨‖F (p t)‖, norm_nonneg _, fun s hs => hmax hs⟩
  obtain ⟨C, hC0, hC⟩ := hbdd
  have hsmul : Integrable (fun t => ‖deriv (p : ℝ → ℂ) t‖ • F (p t)) m := by
    refine (hvel.norm.const_mul C).mono'
      (((aestronglyMeasurable_deriv (p : ℝ → ℂ) m).norm.smul
        (hcomp.aestronglyMeasurable measurableSet_Icc))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (hC t ht) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hfi : n.Integrable (F ∘ p) := by
    change Integrable (F ∘ p) n.variation
    rw [Measure.variation_withDensityᵥ hvel]
    exact (integrable_withDensity_iff_integrable_smul (measurable_deriv (p : ℝ → ℂ)).nnnorm).2
      hsmul
  have hfm : AEStronglyMeasurable F ((n.variation).map p) :=
    F.continuous.aestronglyMeasurable
  have hmeasure : g.measure = n.map (p : ℝ → ℂ) := rfl
  have hint : (n.map p).integral F (ContinuousLinearMap.mul ℝ ℂ) =
      ∫ t in (0 : ℝ)..1, F (p t) * deriv (p : ℝ → ℂ) t := by
    rw [VectorMeasure.integral_map p.continuous.measurable hfm hfi]
    have hn : n = m.withDensityᵥ (deriv (p : ℝ → ℂ)) := rfl
    have hmul := VectorMeasure.integral_withDensityᵥ_mul (μ := m) (f := F ∘ (p : ℝ → ℂ))
      (g := deriv (p : ℝ → ℂ)) hvel (measurable_deriv _) hfi
    rw [hn]
    change (m.withDensityᵥ (deriv (p : ℝ → ℂ))).integral (F ∘ (p : ℝ → ℂ))
      (ContinuousLinearMap.mul ℝ ℂ) = _
    rw [hmul]
    change (∫ x in Icc (0 : ℝ) 1, (F ∘ (p : ℝ → ℂ)) x * deriv (p : ℝ → ℂ) x) = _
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    rfl
  have hae : f =ᵐ[(PettisMeasure.complex g.measure).variation] (F : ℂ → ℂ) := by
    have hsupp : ∀ᵐ w ∂(PettisMeasure.complex g.measure).variation, w ∈ g.trace := by
      rw [ae_iff]
      exact g.variation_compl_trace
    filter_upwards [hsupp] with w hw
    have := congrFun (congrArg ContinuousMap.toFun hF) ⟨w, hw⟩
    simpa [fRes] using this.symm
  refine ⟨?_, ?_⟩
  · exact (hfi.map hfm).congr hae.symm
  · have hcongr := VectorMeasure.integral_congr_ae (μ := g.measure)
      (B := ContinuousLinearMap.mul ℝ ℂ) hae
    rw [PettisMeasure.scalarIntegral, hcongr, hmeasure, hint]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall ?_)
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le zero_le_one] at ht
      exact Ioc_subset_Icc_self ht
    rw [hagree t ht']

private lemma sub_eq_mul_intervalIntegral_deriv {Ω : Set ℂ} (hΩ : IsOpen Ω) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g Ω) {w z : ℂ}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, w + (t : ℂ) * (z - w) ∈ Ω) :
    g z - g w = (z - w) * ∫ t in (0 : ℝ)..1, deriv g (w + (t : ℂ) * (z - w)) := by
  let p (t : ℝ) : ℂ := w + (t : ℂ) * (z - w)
  have hp (t : ℝ) : HasDerivAt p (z - w) t := by
    have hid : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    simpa [p, one_mul] using (hid.mul_const (z - w)).const_add w
  have hcomp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (g ∘ p) (deriv g (p t) * (z - w)) t := by
    have hgt : HasDerivAt g (deriv g (p t)) (p t) :=
      (hg.differentiableAt (hΩ.mem_nhds (hseg t ht))).hasDerivAt
    simpa using (hgt.complexToReal_fderiv.comp_hasDerivAt t (hp t))
  have hderiv_cont : ContinuousOn (deriv g) Ω :=
    (hg.contDiffOn hΩ).continuousOn_deriv_of_isOpen hΩ le_rfl
  have hpath : ContinuousOn p (Icc (0 : ℝ) 1) := by fun_prop
  have hI : uIcc (0 : ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have hint : IntervalIntegrable (fun t => deriv g (p t) * (z - w)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [hI]
    exact (hderiv_cont.comp hpath fun t ht => hseg t ht).mul continuousOn_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := g ∘ p) (f' := fun t => deriv g (p t) * (z - w))
    (fun t ht => hcomp t (by simpa [hI] using ht)) hint
  have hends : (g ∘ p) 1 - (g ∘ p) 0 = g z - g w := by simp [p]
  rw [← hends, ← hFTC, intervalIntegral.integral_mul_const, mul_comm]

private lemma norm_dslope_le_on {Ω : Set ℂ} (hΩ : IsOpen Ω) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g Ω) {M : Set ℂ} (hM : IsCompact M) (hMΩ : M ⊆ Ω) :
    ∃ C, ∀ w ∈ M, ∀ z ∈ M, ‖dslope g w z‖ ≤ C := by
  obtain ⟨δ, hδ, hthick⟩ := hM.exists_cthickening_subset_open hΩ hMΩ
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hthick2 : cthickening (δ / 2) M ⊆ Ω :=
    (cthickening_mono (half_le_self hδ.le) M).trans hthick
  have hKc : IsCompact (cthickening (δ / 2) M) := hM.cthickening
  have hderiv_cont : ContinuousOn (fun ξ => ‖deriv g ξ‖) (cthickening (δ / 2) M) :=
    ((hg.contDiffOn hΩ).continuousOn_deriv_of_isOpen hΩ le_rfl).norm.mono hthick2
  have hB : ∃ B, ∀ ξ ∈ cthickening (δ / 2) M, ‖deriv g ξ‖ ≤ B := by
    by_cases hne : (cthickening (δ / 2) M).Nonempty
    · obtain ⟨ξ, hξ, hmax⟩ := hKc.exists_isMaxOn hne hderiv_cont
      exact ⟨‖deriv g ξ‖, fun η hη => hmax hη⟩
    · exact ⟨0, fun ξ hξ => (hne ⟨ξ, hξ⟩).elim⟩
  obtain ⟨B, hB⟩ := hB
  have hg_cont : ContinuousOn (fun ξ => ‖g ξ‖) M := hg.continuousOn.norm.mono hMΩ
  have hG : ∃ G, ∀ ξ ∈ M, ‖g ξ‖ ≤ G := by
    by_cases hne : M.Nonempty
    · obtain ⟨ξ, hξ, hmax⟩ := hM.exists_isMaxOn hne hg_cont
      exact ⟨‖g ξ‖, fun η hη => hmax hη⟩
    · exact ⟨0, fun ξ hξ => (hne ⟨ξ, hξ⟩).elim⟩
  obtain ⟨G, hG⟩ := hG
  refine ⟨max B (4 * G / δ), fun w hw z hz => ?_⟩
  have hmem_seg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hclose : ‖z - w‖ < δ / 2) :
      w + (t : ℂ) * (z - w) ∈ cthickening (δ / 2) M := by
    refine (thickening_subset_cthickening (δ / 2) M) ?_
    rw [mem_thickening_iff]
    refine ⟨w, hw, ?_⟩
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
    have ht1' : |t| ≤ 1 := abs_le.mpr ⟨by linarith, ht1⟩
    calc |t| * ‖z - w‖ ≤ 1 * ‖z - w‖ :=
        mul_le_mul_of_nonneg_right ht1' (norm_nonneg _)
      _ = ‖z - w‖ := by ring
      _ < δ / 2 := hclose
  by_cases hclose : ‖z - w‖ < δ / 2
  · have hseg : ∀ t ∈ Icc (0 : ℝ) 1, w + (t : ℂ) * (z - w) ∈ Ω :=
      fun t ht => hthick2 (hmem_seg ht.1 ht.2 hclose)
    by_cases hzw : z = w
    · rw [hzw, dslope_same]
      exact (hB w (self_subset_cthickening M hw)).trans (le_max_left _ _)
    · have hsub := sub_eq_mul_intervalIntegral_deriv hΩ hg hseg
      have heq : dslope g w z =
          ∫ t in (0 : ℝ)..1, deriv g (w + (t : ℂ) * (z - w)) := by
        rw [dslope_of_ne _ hzw]
        simp only [slope, vsub_eq_sub, smul_eq_mul]
        rw [hsub]
        field_simp [sub_ne_zero.mpr hzw]
      rw [heq]
      have hle_int := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (C := B) (f := fun t : ℝ => deriv g (w + (t : ℂ) * (z - w))) (fun t ht => ?_)
      · have hB1 : B * |1 - 0| = B := by simp
        exact (hle_int.trans_eq hB1).trans (le_max_left _ _)
      · rw [uIoc_of_le zero_le_one] at ht
        exact hB _ (hmem_seg (le_of_lt ht.1) ht.2 hclose)
  · have hfar : δ / 2 ≤ ‖z - w‖ := le_of_not_gt hclose
    have hzw : z ≠ w := by
      intro h
      subst h
      simp at hfar
      linarith
    rw [dslope_of_ne _ hzw]
    simp only [slope, vsub_eq_sub, smul_eq_mul, norm_mul, norm_inv]
    rw [← div_eq_inv_mul]
    have hnum : ‖g z - g w‖ ≤ 2 * G := by
      calc ‖g z - g w‖ ≤ ‖g z‖ + ‖g w‖ := norm_sub_le _ _
        _ ≤ G + G := add_le_add (hG z hz) (hG w hw)
        _ = 2 * G := by ring
    have hpos : 0 < ‖z - w‖ := lt_of_lt_of_le hδ2 hfar
    have hG0 : 0 ≤ 2 * G := le_trans (norm_nonneg _) hnum
    calc ‖g z - g w‖ / ‖z - w‖ ≤ (2 * G) / ‖z - w‖ :=
          div_le_div_of_nonneg_right hnum hpos.le
      _ ≤ (2 * G) / (δ / 2) := div_le_div_of_nonneg_left hG0 hδ2 hfar
      _ = 4 * G / δ := by ring
      _ ≤ max B (4 * G / δ) := le_max_right _ _

end ContourIntegral

/-- The velocity is integrable on the parameter interval of a piecewise `C¹` contour. -/
private theorem ComplexContour.integrableOn_deriv (γ : ComplexContour) :
    IntegrableOn (deriv (fun t ↦ γ.toContinuousMap t)) (Icc (0 : ℝ) 1) := by
  obtain ⟨n, t, ht, hstart, hend, hdiff⟩ := γ.piecewiseContDiff
  rw [integrableOn_congr_set_ae Ioo_ae_eq_Icc.symm]
  apply IntegrableOn.mono_set (t := ⋃ i : Fin n, Icc (t i.castSucc) (t i.succ))
  · apply integrableOn_finite_iUnion.mpr
    intro i
    have hi := ht i.castSucc_lt_succ
    have hc := (hdiff i).continuousOn_derivWithin (uniqueDiffOn_Icc hi) le_rfl
    rw [integrableOn_congr_set_ae Ioo_ae_eq_Icc.symm]
    exact ((hc.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self).congr_fun
      (fun _ hx ↦ derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)) measurableSet_Ioo
  · intro x hx
    classical
    let s := Finset.univ.filter (fun j : Fin (n + 1) ↦ x ≤ t j)
    have hlast : Fin.last n ∈ s := by simp [s, hend, hx.2.le]
    let j := s.min' ⟨_, hlast⟩
    have hj : j ∈ s := Finset.min'_mem _ _
    have hjx : x ≤ t j := (Finset.mem_filter.mp hj).2
    have hne : j ≠ 0 := by
      intro h
      rw [h, hstart] at hjx
      exact hx.1.not_ge hjx
    obtain ⟨i, hi⟩ := Fin.eq_succ_of_ne_zero hne
    refine mem_iUnion.mpr ⟨i, le_of_lt (lt_of_not_ge ?_), hi ▸ hjx⟩
    intro hxi
    have himem : i.castSucc ∈ s := by simp [s, hxi]
    exact i.castSucc_lt_succ.not_ge (hi ▸ Finset.min'_le s _ himem)

/-- A function continuous on the trace is integrable against the contour measure, and
its scalar integral is the parameter integral weighted by the contour velocity. -/
private theorem ComplexContour.scalarIntegral_eq_integral (γ : ComplexContour) {g : ℂ → ℂ}
    (hg : ContinuousOn g γ.trace) :
    Integrable g (PettisMeasure.complex γ.measure).variation ∧
      (PettisMeasure.complex γ.measure).scalarIntegral g =
        ∫ t in Icc (0 : ℝ) 1, g (γ.toContinuousMap t) * deriv (fun s ↦ γ.toContinuousMap s) t := by
  classical
  let p : ℝ → ℂ := γ.toContinuousMap
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  let ν : ComplexMeasure ℝ := μ.withDensityᵥ (deriv p)
  have hp : Measurable p := γ.toContinuousMap.continuous.measurable
  have hv : Integrable (deriv p) μ := γ.integrableOn_deriv
  have hvm : Measurable (deriv p) := measurable_deriv _
  have htrace : IsCompact γ.trace :=
    isCompact_Icc.image γ.toContinuousMap.continuous
  have hpre : ∀ᵐ t ∂μ, p t ∈ γ.trace :=
    (ae_restrict_mem measurableSet_Icc).mono fun t ht ↦ mem_image_of_mem p ht
  have hν := Measure.variation_withDensityᵥ hv
  have hνμ : ν.variation ≪ μ := hν ▸ withDensity_absolutelyContinuous _ _
  have htraceAE : ∀ᵐ z ∂ν.variation.map p, z ∈ γ.trace :=
    (ae_map_iff hp.aemeasurable htrace.isClosed.measurableSet).2 (hνμ.ae_le hpre)
  let g₀ := γ.trace.piecewise g 0
  have hg₀ : Measurable g₀ :=
    hg.measurable_piecewise continuousOn_const htrace.isClosed.measurableSet
  have heq : g₀ =ᵐ[ν.variation.map p] g :=
    htraceAE.mono fun z hz ↦ piecewise_eq_of_mem _ _ _ hz
  have hgmap : AEStronglyMeasurable g (ν.variation.map p) :=
    hg₀.aestronglyMeasurable.congr heq
  obtain ⟨C, hC⟩ := (htrace.image_of_continuousOn hg).isBounded.exists_norm_le
  have : IsFiniteMeasure ν.variation := by
    change IsFiniteMeasure (μ.withDensityᵥ (deriv p)).variation
    rw [hν]
    exact isFiniteMeasure_withDensity hv.hasFiniteIntegral.ne
  have hgi : ν.Integrable (g ∘ p) := by
    have hpre' : ∀ᵐ t ∂ν.variation, p t ∈ γ.trace := hνμ.ae_le hpre
    exact Integrable.of_bound (hgmap.comp_measurable hp) C
      (hpre'.mono fun t ht ↦ hC _ (mem_image_of_mem _ ht))
  refine ⟨hgi.map hgmap, ?_⟩
  change (ν.map p).integral g (ContinuousLinearMap.mul ℝ ℂ) = _
  rw [VectorMeasure.integral_map hp hgmap hgi]
  exact VectorMeasure.integral_withDensityᵥ_mul hv hvm hgi

/-- Paper: Theorem C.5.2.4(1–2), p. 738. Scalar Cauchy–Goursat for a simple contour
of index zero outside the open set of holomorphy.
Deviation: The conclusion uses the parameter integral and the hypothesis uses the
index outside the domain. -/
theorem PositiveSimpleContour.integral_eq_zero_of_index_eq_zero (γ : PositiveSimpleContour)
    {U : Set ℂ} (hU : IsOpen U) (htrace : γ.val.trace ⊆ U)
    (hindex : ∀ z ∉ U, γ.val.index z = 0) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) :
    (∫ t in Icc (0 : ℝ) 1, g (γ.val.toContinuousMap t) *
      deriv (fun s ↦ γ.val.toContinuousMap s) t) = 0 := by
  sorry

/-- A nondegenerate rectangle admits a positively oriented simple boundary contour.
Its scalar integral agrees, up to orientation, with the sum of the two wedge
integrals around the rectangle. -/
theorem exists_positiveSimpleContour_rectangle (z w : ℂ) (hre : z.re ≠ w.re) (him : z.im ≠ w.im) :
    ∃ γ : PositiveSimpleContour, γ.val.trace ⊆ Complex.Rectangle z w ∧
      γ.interior ⊆ Complex.Rectangle z w ∧
      ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
        ∀ g : ℂ → ℂ, ContinuousOn g (Complex.Rectangle z w) →
          (PettisMeasure.complex γ.val.measure).scalarIntegral g =
            ε * (Complex.wedgeIntegral z w g + Complex.wedgeIntegral w z g) := by
  sorry

/-- Vanishing scalar integrals on simple contours imply complex differentiability
by the rectangular form of Morera's theorem. -/
private theorem differentiableOn_of_scalarIntegral_eq_zero {U : Set ℂ} (hU : IsOpen U)
    {g : ℂ → ℂ} (hg : ContinuousOn g U)
    (hzero : ∀ γ : PositiveSimpleContour, γ.val.trace ⊆ U → γ.interior ⊆ U →
      (PettisMeasure.complex γ.val.measure).scalarIntegral g = 0) : DifferentiableOn ℂ g U := by
  refine (Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).1 ⟨?_, hg⟩
  intro z w hrect
  rw [← add_eq_zero_iff_eq_neg]
  by_cases hre : z.re = w.re
  · rw [Complex.wedgeIntegral_add_wedgeIntegral_eq]
    simp [hre]
  by_cases him : z.im = w.im
  · rw [Complex.wedgeIntegral_add_wedgeIntegral_eq]
    simp [him]
  obtain ⟨γ, htrace, hinterior, ε, hε, heq⟩ := exists_positiveSimpleContour_rectangle z w hre him
  have h := hzero γ (htrace.trans hrect) (hinterior.trans hrect)
  rw [heq g (hg.mono hrect)] at h
  have hε₀ : ε ≠ 0 := by rcases hε with rfl | rfl <;> simp
  exact (mul_eq_zero.mp h).resolve_left hε₀

section Criteria

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E] [PolynormableSpace ℂ E]
variable {Ω : Set ℂ} (hΩ : IsOpen Ω) (hconn : IsConnected Ω) (f : ℂ → E)
include hΩ hconn

/-- Paper: Theorem C.5.2.4(1–2), p. 738. Weak holomorphy is equivalent to weak
continuity and vanishing weak Pettis integrals around simple contours in the domain. -/
theorem weaklyHolomorphicOn_iff_contourIntegral_eq_zero :
    WeaklyHolomorphicOn f Ω ↔ WeaklyContinuousOn f Ω ∧
      ∀ γ : PositiveSimpleContour, γ.val.trace ⊆ Ω → γ.interior ⊆ Ω →
        ∃ hi : PettisWeaklyIntegrable (.complex γ.val.measure) f,
          pettisWeakIntegral (.complex γ.val.measure) f hi = 0 := by
  constructor
  · intro hf
    have hc : WeaklyContinuousOn f Ω := fun φ ↦ (hf φ).continuousOn
    refine ⟨hc, fun γ htrace hinterior ↦ ?_⟩
    have hscalar (φ : StrongDual ℂ E) := γ.val.scalarIntegral_eq_integral ((hc φ).mono htrace)
    refine ⟨fun φ ↦ (hscalar φ).1, LinearMap.ext fun φ ↦ ?_⟩
    change (PettisMeasure.complex γ.val.measure).scalarIntegral (φ ∘ f) = 0
    rw [(hscalar φ).2]
    apply γ.integral_eq_zero_of_index_eq_zero hΩ htrace _ (hf φ)
    intro z hz
    have hzt : z ∉ γ.val.trace := fun h ↦ hz (htrace h)
    exact (γ.property.2 z hzt).resolve_right fun h ↦ hz (hinterior ⟨hzt, h⟩)
  · rintro ⟨hc, hzero⟩ φ
    apply differentiableOn_of_scalarIntegral_eq_zero hΩ (hc φ)
    intro γ htrace hinterior
    obtain ⟨hi, h⟩ := hzero γ htrace hinterior
    exact congrArg (fun v : PettisWeakCompletion E ↦
      (show Module.Dual ℂ (StrongDual ℂ E) from v) φ) h

section ScalarCauchy

omit hΩ hconn
open Metric Complex

private lemma ComplexContour.compact_trace (γ : ComplexContour) : IsCompact γ.trace :=
  isCompact_Icc.image γ.toContinuousMap.continuous

private lemma ComplexContour.ae_mem_trace (γ : ComplexContour) :
    ∀ᵐ w ∂γ.measure.variation, w ∈ γ.trace := by
  rw [ae_iff]
  exact γ.variation_compl_trace

private lemma ComplexContour.scalarIntegral_const_mul (γ : ComplexContour) (c : ℂ) (g : ℂ → ℂ) :
    (PettisMeasure.complex γ.measure).scalarIntegral (fun w ↦ c * g w) =
      c * (PettisMeasure.complex γ.measure).scalarIntegral g := by
  simp only [PettisMeasure.scalarIntegral, VectorMeasure.integral_eq_setToFun]
  apply setToFun_smul _ _ c g
  intro a s z
  simp [VectorMeasure.transpose, mul_left_comm]

private lemma ComplexContour.scalarIntegral_sub (γ : ComplexContour) {g h : ℂ → ℂ}
    (hg : ContinuousOn g γ.trace) (hh : ContinuousOn h γ.trace) :
    (PettisMeasure.complex γ.measure).scalarIntegral (fun w ↦ g w - h w) =
      (PettisMeasure.complex γ.measure).scalarIntegral g -
        (PettisMeasure.complex γ.measure).scalarIntegral h :=
  VectorMeasure.integral_fun_sub (γ.scalarIntegral_eq_intervalIntegral hg).1
    (γ.scalarIntegral_eq_intervalIntegral hh).1

/-- Bounded convergence for kernels continuous on the contour trace. -/
private lemma ComplexContour.tendsto_scalarIntegral (γ : ComplexContour) {l : Filter ℂ}
    [l.IsCountablyGenerated] {K : ℂ → ℂ → ℂ} {k : ℂ → ℂ}
    (hc : ∀ᶠ z in l, ContinuousOn (K z) γ.trace)
    (hb : ∃ C : ℝ, ∀ᶠ z in l, ∀ w ∈ γ.trace, ‖K z w‖ ≤ C)
    (ht : ∀ w ∈ γ.trace, Tendsto (fun z ↦ K z w) l (𝓝 (k w))) :
    Tendsto (fun z ↦ (PettisMeasure.complex γ.measure).scalarIntegral (K z)) l
      (𝓝 ((PettisMeasure.complex γ.measure).scalarIntegral k)) := by
  have : IsFiniteMeasure γ.measure.variation :=
    (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℂ) ≠ 0)).mp
      (γ.scalarIntegral_eq_intervalIntegral continuousOn_const).1
  apply VectorMeasure.tendsto_integral_filter_of_norm_le_const
  · exact hc.mono fun z hz ↦ (γ.scalarIntegral_eq_intervalIntegral hz).1.aestronglyMeasurable
  · obtain ⟨C, hC⟩ := hb
    exact ⟨C, hC.mono fun z hz ↦ γ.ae_mem_trace.mono (hz ·)⟩
  · exact γ.ae_mem_trace.mono (ht ·)

/-- A locally uniformly bounded family of holomorphic kernels may be differentiated
under the contour integral. Cauchy's estimate bounds the difference quotients. -/
private lemma ComplexContour.differentiableOn_scalarIntegral (γ : ComplexContour) {U : Set ℂ}
    (hU : IsOpen U) {K : ℂ → ℂ → ℂ} (hc : ∀ z ∈ U, ContinuousOn (K z) γ.trace)
    (hd : ∀ w ∈ γ.trace, DifferentiableOn ℂ (fun z ↦ K z w) U)
    (hb : ∀ M : Set ℂ, IsCompact M → M ⊆ U → ∃ C : ℝ, ∀ z ∈ M, ∀ w ∈ γ.trace, ‖K z w‖ ≤ C) :
    DifferentiableOn ℂ (fun z ↦ (PettisMeasure.complex γ.measure).scalarIntegral (K z)) U := by
  intro x hx
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨C, hC⟩ := hb _ (isCompact_closedBall x r) hball
  have hr' := half_pos hr
  have hsmall : ball x (r / 2) ⊆ closedBall x r :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (half_le_self hr.le))
  have hderiv (w : ℂ) (hw : w ∈ γ.trace) (y : ℂ) (hy : y ∈ ball x (r / 2)) :
      ‖deriv (fun z ↦ K z w) y‖ ≤ C / (r / 2) := by
    have hs : closedBall y (r / 2) ⊆ closedBall x r :=
      closedBall_subset_closedBall' (by have := mem_ball.mp hy; linarith)
    apply norm_deriv_le_of_forall_mem_sphere_norm_le hr'
      ((hd w hw).diffContOnCl_ball (hs.trans hball))
    exact fun z hz ↦ hC z (hs (sphere_subset_closedBall hz)) w hw
  let Q (y w : ℂ) := slope (fun z ↦ K z w) x y
  have hnear : ∀ᶠ y in 𝓝[≠] x, y ∈ ball x (r / 2) :=
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr')
  have hQ : Tendsto (fun y ↦ (PettisMeasure.complex γ.measure).scalarIntegral (Q y)) (𝓝[≠] x)
      (𝓝 ((PettisMeasure.complex γ.measure).scalarIntegral (fun w ↦ deriv (fun z ↦ K z w) x))) := by
    apply γ.tendsto_scalarIntegral
    · filter_upwards [hnear] with y hy
      exact continuousOn_const.mul ((hc y (hball (hsmall hy))).sub (hc x hx))
    · refine ⟨C / (r / 2), ?_⟩
      filter_upwards [hnear, self_mem_nhdsWithin] with y hy hyx
      intro w hw
      have hs := (convex_ball x (r / 2)).norm_image_sub_le_of_norm_deriv_le
        (fun z hz ↦ (hd w hw).differentiableAt (hU.mem_nhds (hball (hsmall hz))))
        (hderiv w hw) (mem_ball_self hr') hy
      change ‖slope (fun z ↦ K z w) x y‖ ≤ _
      rw [slope_def_field, norm_div]
      exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hyx))).mpr hs
    · exact fun w hw ↦ ((hd w hw).differentiableAt (hU.mem_nhds hx)).hasDerivAt.tendsto_slope
  apply DifferentiableAt.differentiableWithinAt
  apply HasDerivAt.differentiableAt
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply hQ.congr'
  filter_upwards [hnear] with y hy
  simp only [Q, slope, vsub_eq_sub, smul_eq_mul]
  rw [γ.scalarIntegral_const_mul, γ.scalarIntegral_sub (hc y (hball (hsmall hy))) (hc x hx)]

private lemma ComplexContour.continuousOn_inv_sub (γ : ComplexContour) {z : ℂ} (hz : z ∉ γ.trace) :
    ContinuousOn (fun w ↦ (w - z)⁻¹) γ.trace :=
  (continuousOn_id.sub continuousOn_const).inv₀ fun _ hw ↦ sub_ne_zero.mpr (ne_of_mem_of_not_mem hw hz)

private lemma ComplexContour.differentiableOn_cauchyTransform (γ : ComplexContour) {g : ℂ → ℂ}
    (hg : ContinuousOn g γ.trace) : DifferentiableOn ℂ
      (fun z ↦ (PettisMeasure.complex γ.measure).scalarIntegral (fun w ↦ (w - z)⁻¹ * g w)) γ.traceᶜ := by
  apply γ.differentiableOn_scalarIntegral γ.compact_trace.isClosed.isOpen_compl
  · exact fun z hz ↦ (γ.continuousOn_inv_sub hz).mul hg
  · intro w hw
    exact ((differentiableOn_const w).sub differentiableOn_id |>.inv fun z hz ↦
      sub_ne_zero.mpr (ne_of_mem_of_not_mem hw hz)).mul (differentiableOn_const (g w))
  · intro M hM hs
    have hc : ContinuousOn (fun p : ℂ × ℂ ↦ (p.2 - p.1)⁻¹ * g p.2) (M ×ˢ γ.trace) :=
      (((continuousOn_snd (s := M ×ˢ γ.trace)).sub continuousOn_fst).inv₀ fun p hp ↦
        sub_ne_zero.mpr (ne_of_mem_of_not_mem hp.2 (hs hp.1))).mul
        (hg.comp continuousOn_snd mapsTo_snd_prod)
    obtain ⟨C, hC⟩ := (hM.prod γ.compact_trace).exists_bound_of_continuousOn hc
    exact ⟨C, fun z hz w hw ↦ hC (z, w) ⟨hz, hw⟩⟩

private lemma ComplexContour.tendsto_cauchyTransform (γ : ComplexContour) {g : ℂ → ℂ}
    (hg : ContinuousOn g γ.trace) : Tendsto
      (fun z ↦ (PettisMeasure.complex γ.measure).scalarIntegral (fun w ↦ (w - z)⁻¹ * g w))
      (cocompact ℂ) (𝓝 0) := by
  have hzero : (PettisMeasure.complex γ.measure).scalarIntegral (fun _ ↦ 0) = 0 :=
    VectorMeasure.integral_zero
  have : (cocompact ℂ).IsCountablyGenerated := by
    rw [← cobounded_eq_cocompact]
    infer_instance
  rw [← hzero]
  apply γ.tendsto_scalarIntegral
  · filter_upwards [γ.compact_trace.compl_mem_cocompact] with z hz
    exact (γ.continuousOn_inv_sub hz).mul hg
  · obtain ⟨R, hR⟩ := γ.compact_trace.exists_bound_of_continuousOn (f := id) continuousOn_id
    obtain ⟨C, hC⟩ := γ.compact_trace.exists_bound_of_continuousOn hg
    refine ⟨C, ?_⟩
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (R + 1)] with z hz
    intro w hw
    have hzw := norm_sub_norm_le z w
    rw [norm_sub_rev] at hzw
    have h1 : 1 ≤ ‖w - z‖ := by have := hR w hw; change ‖w‖ ≤ R at this; linarith
    rw [norm_mul, norm_inv]
    exact (mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ h1) (norm_nonneg (g w))).trans
      ((one_mul _).le.trans (hC w hw))
  · intro w _
    rw [← cobounded_eq_cocompact]
    simpa using ((tendsto_inv₀_cobounded.comp (tendsto_const_sub_cobounded w)).mul_const (g w))

private lemma ComplexContour.differentiableOn_dslopeIntegral (γ : ComplexContour) {U : Set ℂ}
    (hU : IsOpen U) (htr : γ.trace ⊆ U) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) :
    DifferentiableOn ℂ (fun z ↦ (PettisMeasure.complex γ.measure).scalarIntegral (dslope g z)) U := by
  have hd := (hg.analyticOnNhd hU).dslope
  apply γ.differentiableOn_scalarIntegral hU
  · exact fun z _ ↦ (hd z).differentiableOn.continuousOn.mono htr
  · intro w _
    apply (hd w).differentiableOn.congr
    intro z _
    rcases eq_or_ne w z with rfl | hne
    · rfl
    · rw [dslope_of_ne _ hne, dslope_of_ne _ hne.symm, slope_comm]
  · intro M hM hs
    obtain ⟨C, hC⟩ := norm_dslope_le_on hU hg (hM.union γ.compact_trace) (union_subset hs htr)
    exact ⟨C, fun z hz w hw ↦ hC z (.inl hz) w (.inr hw)⟩

/-- Dixon's gluing argument: integrate the divided difference on the domain and
use the Cauchy transform on the part of the complement with index zero. -/
private lemma PositiveSimpleContour.scalar_cauchy {U : Set ℂ} (hU : IsOpen U)
    (γ : PositiveSimpleContour) (htr : γ.val.trace ⊆ U) (hint : γ.interior ⊆ U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) {z : ℂ} (hz : z ∈ γ.interior) :
    g z = (2 * (Real.pi : ℂ) * I)⁻¹ *
      (PettisMeasure.complex γ.val.measure).scalarIntegral (fun w ↦ (w - z)⁻¹ * g w) := by
  classical
  let c : ℂ := 2 * (Real.pi : ℂ) * I
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
  let L := (PettisMeasure.complex γ.val.measure).scalarIntegral
  let A (x : ℂ) := L (fun w ↦ (w - x)⁻¹ * g w)
  let B (x : ℂ) := L (dslope g x)
  let J (x : ℂ) := L (fun w ↦ (w - x)⁻¹)
  have hg' := hg.continuousOn.mono htr
  have hdA : DifferentiableOn ℂ A γ.val.traceᶜ := γ.val.differentiableOn_cauchyTransform hg'
  have hdB : DifferentiableOn ℂ B U := γ.val.differentiableOn_dslopeIntegral hU htr hg
  have hdJ : DifferentiableOn ℂ J γ.val.traceᶜ := by
    simpa only [mul_one] using γ.val.differentiableOn_cauchyTransform (continuousOn_const (c := (1 : ℂ)))
  have htJ : Tendsto J (cocompact ℂ) (𝓝 0) := by
    simpa only [mul_one] using γ.val.tendsto_cauchyTransform (continuousOn_const (c := (1 : ℂ)))
  have hB (x : ℂ) (hx : x ∉ γ.val.trace) : B x = A x - g x * J x := by
    have hk := γ.val.continuousOn_inv_sub hx
    calc B x = L (fun w ↦ ((w - x)⁻¹ * g w) - g x * (w - x)⁻¹) := by
          apply VectorMeasure.integral_congr_ae
          filter_upwards [γ.val.ae_mem_trace] with w hw
          rw [dslope_of_ne g (ne_of_mem_of_not_mem hw hx)]
          simp only [slope, vsub_eq_sub, smul_eq_mul]
          ring
      _ = A x - g x * J x := by
          dsimp only [A, J, L]
          rw [γ.val.scalarIntegral_sub (g := fun w ↦ (w - x)⁻¹ * g w)
            (h := fun w ↦ g x * (w - x)⁻¹) (hk.mul hg') (continuousOn_const.mul hk),
            γ.val.scalarIntegral_const_mul]
  have hJ (x : ℂ) (hx : x ∉ γ.val.trace) (hn : J x ≠ c) : J x = 0 := by
    rcases γ.property.2 x hx with h | h
    · exact (mul_eq_zero.mp (show c⁻¹ * J x = 0 from h)).resolve_left (inv_ne_zero hc)
    · exact (hn ((inv_mul_eq_one₀ hc).mp h).symm).elim
  let F (x : ℂ) := if x ∈ U then B x else A x
  have hFA (x : ℂ) (hx : x ∉ γ.val.trace) (hn : J x ≠ c) : F x = A x := by
    simp [F, hB x hx, hJ x hx hn]
  have hdF : Differentiable ℂ F := by
    intro x
    by_cases hx : x ∈ U
    · apply (hdB.differentiableAt (hU.mem_nhds hx)).congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hx] with y hy using ite_eq_left hy
    · have hxtr : x ∉ γ.val.trace := fun h ↦ hx (htr h)
      have hnb := γ.val.compact_trace.isClosed.isOpen_compl.mem_nhds hxtr
      have hn : J x ≠ c := fun h ↦ hx (hint ⟨hxtr, (inv_mul_eq_one₀ hc).mpr h.symm⟩)
      apply (hdA.differentiableAt hnb).congr_of_eventuallyEq
      filter_upwards [hnb, (hdJ.continuousOn.continuousAt hnb).eventually_ne hn] with y hy hn'
      exact hFA y hy hn'
  have htF : Tendsto F (cocompact ℂ) (𝓝 0) := by
    apply (γ.val.tendsto_cauchyTransform hg').congr'
    filter_upwards [γ.val.compact_trace.compl_mem_cocompact, htJ.eventually_ne hc.symm] with x hx hn
    exact (hFA x hx hn).symm
  have he := hdF.apply_eq_of_tendsto_cocompact z htF
  have hJz : c = J z := (inv_mul_eq_one₀ hc).mp hz.2
  change g z = c⁻¹ * A z
  rw [show F z = B z from ite_eq_left (hint hz), hB z hz.1, ← hJz] at he
  rw [sub_eq_zero.mp he, mul_comm (g z) c, inv_mul_cancel_left₀ hc]

end ScalarCauchy

/-- Paper: Theorem C.5.2.4(1,3), p. 738. Weak holomorphy is equivalent to weak
continuity and the Cauchy formula in the algebraic dual of the continuous dual. -/
theorem weaklyHolomorphicOn_iff_weak_cauchyIntegral :
    WeaklyHolomorphicOn f Ω ↔ WeaklyContinuousOn f Ω ∧
      ∀ (γ : PositiveSimpleContour), γ.val.trace ⊆ Ω → γ.interior ⊆ Ω →
        ∀ z ∈ γ.interior,
          ∃ hi : PettisWeaklyIntegrable (.complex γ.val.measure) (fun w ↦ (w - z)⁻¹ • f w),
            toPettisWeakCompletion E (f z) =
              (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
                pettisWeakIntegral (.complex γ.val.measure) (fun w ↦ (w - z)⁻¹ • f w) hi := by
  constructor
  · intro hf
    refine ⟨fun φ ↦ (hf φ).continuousOn, ?_⟩
    intro γ htr hint z hz
    have hi : PettisWeaklyIntegrable (.complex γ.val.measure) (fun w ↦ (w - z)⁻¹ • f w) := by
      intro φ
      simp only [map_smul, smul_eq_mul]
      exact (γ.val.scalarIntegral_eq_intervalIntegral
        ((γ.val.continuousOn_inv_sub hz.1).mul ((hf φ).continuousOn.mono htr))).1
    refine ⟨hi, LinearMap.ext fun φ ↦ ?_⟩
    change φ (f z) = _ * (PettisMeasure.complex γ.val.measure).scalarIntegral
      (fun w ↦ φ ((w - z)⁻¹ • f w))
    simp only [map_smul, smul_eq_mul]
    exact γ.scalar_cauchy hΩ htr hint (hf φ) hz
  · rintro ⟨hc, hformula⟩ φ x hx
    obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hx)
    obtain ⟨γ, _, htrace, hinterior, _, _⟩ := exists_positiveSimpleContour_circle x hr
    have htr : γ.val.trace ⊆ Ω := htrace ▸ Metric.sphere_subset_closedBall.trans hball
    have hint : γ.interior ⊆ Ω := hinterior ▸ Metric.ball_subset_closedBall.trans hball
    have hnb : γ.interior ∈ 𝓝 x := hinterior ▸ Metric.ball_mem_nhds x hr
    have hxtr : x ∉ γ.val.trace := (mem_of_mem_nhds hnb).1
    have hd := (γ.val.differentiableOn_cauchyTransform ((hc φ).mono htr)).differentiableAt
      (γ.val.compact_trace.isClosed.isOpen_compl.mem_nhds hxtr)
    apply DifferentiableAt.differentiableWithinAt
    apply (hd.const_mul (2 * (Real.pi : ℂ) * Complex.I)⁻¹).congr_of_eventuallyEq
    filter_upwards [hnb] with z hz
    obtain ⟨hi, he⟩ := hformula γ htr hint z hz
    have he' := congrArg (fun v : PettisWeakCompletion E ↦
      (show Module.Dual ℂ (StrongDual ℂ E) from v) φ) he
    change φ (f z) = _ * (PettisMeasure.complex γ.val.measure).scalarIntegral
      (fun w ↦ φ ((w - z)⁻¹ • f w)) at he'
    simpa only [Function.comp_apply, map_smul, smul_eq_mul] using he'

variable [QuasiCompleteSpace ℂ E]

-- Retain the domain and target space hypotheses in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Theorem C.5.2.6(1–2), p. 738. Weak holomorphy is equivalent to
continuous complex differentiability of every finite order of each scalar evaluation. -/
theorem weaklyHolomorphicOn_iff_scalar_contDiffOn :
    WeaklyHolomorphicOn f Ω ↔ ∀ (φ : StrongDual ℂ E) (k : ℕ), ContDiffOn ℂ k (φ ∘ f) Ω := by
  constructor
  · intro hf φ k
    exact (hf φ).contDiffOn hΩ
  · intro hf φ
    exact (hf φ 1).differentiableOn_one

omit hconn in
/-- Scalar holomorphy makes the vector difference quotients Cauchy in the target
topology. Quasi-completeness gives their limit in the original space. -/
private theorem differentiableOn_of_weaklyHolomorphicOn (hf : WeaklyHolomorphicOn f Ω) :
    DifferentiableOn ℂ f Ω := by
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  apply (vectorHolomorphicOn_iff_tendsto hΩ f).mpr
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hz)
  let K := Metric.closedBall z r
  let S := K ∩ {z}ᶜ
  let q := slope f z
  -- The slopes of q control the difference between two quotients near z.
  let D := (fun p : ℂ × ℂ ↦ slope q p.1 p.2) '' (S ×ˢ S)
  have hscalar (φ : StrongDual ℂ E) : AnalyticOnNhd ℂ (dslope (φ ∘ f) z) Ω :=
    ((hf φ).analyticOnNhd hΩ).dslope z
  have heval (φ : StrongDual ℂ E) {w : ℂ} (hw : w ∈ S) :
      φ (q w) = dslope (φ ∘ f) z w := by
    rw [dslope_of_ne _ (show w ≠ z from hw.2)]
    exact (φ.toLinearMap.slope_comp f z w).symm
  have hK : IsCompact K := isCompact_closedBall z r
  have hq : IsVonNBounded ℂ (q '' S) := by
    apply (isVonNBounded_iff_dual_image _).mpr
    intro φ
    refine (hK.image_of_continuousOn ((hscalar φ).continuousOn.mono hball)).isBounded.subset ?_
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw.1, (heval φ hw).symm⟩
  have hD : IsVonNBounded ℂ D := by
    apply (isVonNBounded_iff_dual_image _).mpr
    intro φ
    let g := dslope (φ ∘ f) z
    have hderiv : IsBounded (deriv g '' K) :=
      (hK.image_of_continuousOn ((hscalar φ).deriv.continuousOn.mono hball)).isBounded
    obtain ⟨C, hC⟩ := hderiv.exists_norm_le
    refine isBounded_iff_forall_norm_le.mpr ⟨max C 0, ?_⟩
    rintro _ ⟨_, ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩, rfl⟩
    change ‖φ (slope q u v)‖ ≤ max C 0
    rcases eq_or_ne v u with rfl | hne
    · simp
    have hmean := (convex_closedBall z r).norm_image_sub_le_of_norm_deriv_le
      (f := g) (C := max C 0) (fun w hw ↦ (hscalar φ w (hball hw)).differentiableAt)
      (fun w hw ↦ (hC _ ⟨w, hw, rfl⟩).trans (le_max_left _ _)) hu.1 hv.1
    rw [slope_def_module, map_smul, map_sub, heval φ hu, heval φ hv, norm_smul, norm_inv]
    exact (inv_mul_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hne))).mpr
      (by simpa [g, mul_comm] using hmean)
  let l := 𝓝[≠] z
  have hS : ∀ᶠ w in l, w ∈ S :=
    inter_mem (mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds z hr)) self_mem_nhdsWithin
  have hc : Cauchy (map q l) := by
    rw [IsUniformAddGroup.cauchy_map_iff_tendsto_swapped]
    refine ⟨inferInstance, ?_⟩
    have hfst : Tendsto (Prod.fst : ℂ × ℂ → ℂ) (l ×ˢ l) (𝓝 z) :=
      tendsto_fst.mono_right nhdsWithin_le_nhds
    have hsnd : Tendsto (Prod.snd : ℂ × ℂ → ℂ) (l ×ˢ l) (𝓝 z) :=
      tendsto_snd.mono_right nhdsWithin_le_nhds
    have hmem : ∀ᶠ p : ℂ × ℂ in l ×ˢ l, slope q p.1 p.2 ∈ D :=
      (hS.prod_mk hS).mono fun p hp ↦ ⟨p, hp, rfl⟩
    have hsub : Tendsto (fun p : ℂ × ℂ ↦ p.2 - p.1) (l ×ˢ l) (𝓝 0) := by
      simpa only [sub_self] using hsnd.sub hfst
    simpa only [Pi.smul_def', sub_smul_slope, vsub_eq_sub] using
      hD.smul_tendsto_zero hmem hsub
  obtain ⟨v, _, hv⟩ := (QuasiCompleteSpace.quasiComplete hq.closure isClosed_closure)
    (map q l) hc (le_principal_iff.mpr (mem_map.mpr
      (mem_of_superset hS fun w hw ↦ subset_closure (mem_image_of_mem q hw))))
  exact ⟨v, by simpa only [Tendsto, l, q, slope_fun_def, vsub_eq_sub] using hv⟩

/-- Paper: Theorem C.5.2.6(1,3), p. 738. Weak holomorphy is equivalent to the
existence of complex derivatives in the original target of every order. -/
theorem weaklyHolomorphicOn_iff_all_derivatives :
    WeaklyHolomorphicOn f Ω ↔ ∀ k : ℕ, DifferentiableOn ℂ (deriv^[k] f) Ω := by
  clear hconn
  constructor
  · intro hf k
    apply differentiableOn_of_weaklyHolomorphicOn hΩ
    induction k with
    | zero => exact hf
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        intro φ
        refine ((ih φ).deriv hΩ).congr fun z hz ↦ ?_
        exact (VectorHolomorphicOn.hasDerivAt_comp
          (differentiableOn_of_weaklyHolomorphicOn hΩ _ ih) hΩ φ ⟨z, hz⟩).deriv.symm
  · intro hf φ z hz
    exact (VectorHolomorphicOn.hasDerivAt_comp (f := f) (hf 0) hΩ φ
      ⟨z, hz⟩).differentiableAt.differentiableWithinAt

omit hΩ hconn in
/-- A continuous scalar function on the trace gives an integrable velocity-weighted
function on the parameter interval. -/
private theorem ComplexContour.integrableOn_mul_deriv (γ : ComplexContour) {g : ℂ → ℂ}
    (hg : ContinuousOn g γ.trace) :
    IntegrableOn (fun t ↦ g (γ.toContinuousMap t) * deriv (fun s ↦ γ.toContinuousMap s) t)
      (Icc (0 : ℝ) 1) := by
  have hc := hg.comp γ.toContinuousMap.continuous.continuousOn
    (fun t ht ↦ mem_image_of_mem γ.toContinuousMap ht)
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hc).isBounded.exists_norm_le
  exact γ.integrableOn_deriv.bdd_mul (hc.aestronglyMeasurable measurableSet_Icc)
    ((ae_restrict_mem measurableSet_Icc).mono fun t ht ↦ hC _ (mem_image_of_mem _ ht))

omit hΩ hconn in
/-- The scalar contour integral of a derivative vanishes when its primitive is
defined and differentiable near the trace. -/
private theorem ComplexContour.integral_eq_zero_of_hasDerivAt (γ : ComplexContour) {g g' : ℂ → ℂ}
    (hg : ∀ w ∈ γ.trace, HasDerivAt g (g' w) w) (hg' : ContinuousOn g' γ.trace) :
    (∫ t in Icc (0 : ℝ) 1, g' (γ.toContinuousMap t) *
      deriv (fun s ↦ γ.toContinuousMap s) t) = 0 := by
  obtain ⟨n, t, ht, hstart, hend, hdiff⟩ := γ.piecewiseContDiff
  let p : ℝ → ℂ := γ.toContinuousMap
  let v (s : ℝ) := g' (p s) * deriv p s
  let a (k : ℕ) : ℝ := t ⟨min k n, by omega⟩
  have ha₀ : a 0 = 0 := by simpa [a] using hstart
  have han : a n = 1 := by simpa [a, Fin.last] using hend
  have hpiece (k : ℕ) (hk : k < n) :
      IntervalIntegrable v volume (a k) (a (k + 1)) ∧
        (∫ s in a k..a (k + 1), v s) = g (p (a (k + 1))) - g (p (a k)) := by
    let i : Fin n := ⟨k, hk⟩
    have h₀ : a k = t i.castSucc := by simp [a, i, min_eq_left hk.le]
    have h₁ : a (k + 1) = t i.succ := by simp [a, i, min_eq_left (by omega : k + 1 ≤ n)]
    have hle := (ht i.castSucc_lt_succ).le
    have hsub : Icc (t i.castSucc) (t i.succ) ⊆ Icc 0 1 := by
      rw [← hstart, ← hend]
      exact Icc_subset_Icc (ht.monotone (Fin.zero_le _)) (ht.monotone (Fin.le_last _))
    have hmaps : MapsTo p (Icc (t i.castSucc) (t i.succ)) γ.trace :=
      fun _ hs ↦ mem_image_of_mem p (hsub hs)
    rw [h₀, h₁]
    have hint : IntervalIntegrable v volume (t i.castSucc) (t i.succ) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mpr
        ((γ.integrableOn_mul_deriv hg').mono_set hsub)
    refine ⟨hint, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (f := g ∘ p) hle ?_ ?_ hint⟩
    · have hc : ContinuousOn g γ.trace := fun w hw ↦ (hg w hw).continuousAt.continuousWithinAt
      exact hc.comp γ.toContinuousMap.continuous.continuousOn hmaps
    · intro s hs
      have hp := ((hdiff i).differentiableOn (by simp) s (Ioo_subset_Icc_self hs)).differentiableAt
        (Icc_mem_nhds hs.1 hs.2)
      simpa only [v, smul_eq_mul, mul_comm] using
        (hg (p s) (hmaps (Ioo_subset_Icc_self hs))).scomp s hp.hasDerivAt
  change (∫ s in Icc (0 : ℝ) 1, v s) = 0
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    ← ha₀, ← han, ← intervalIntegral.sum_integral_adjacent_intervals (fun k hk ↦ (hpiece k hk).1)]
  calc
    _ = ∑ k ∈ Finset.range n, (g (p (a (k + 1))) - g (p (a k))) :=
      Finset.sum_congr rfl fun k hk ↦ (hpiece k (Finset.mem_range.mp hk)).2
    _ = 0 := by
      rw [Finset.sum_range_sub (fun k ↦ g (p (a k))), ha₀, han]
      exact sub_eq_zero.mpr (congrArg g γ.closed)

omit hΩ hconn in
/-- The scalar Cauchy kernel times a holomorphic function is integrable on the trace.
Its integral is given by Cauchy–Goursat and integration by parts. -/
private theorem PositiveSimpleContour.scalarIntegral_cauchy_derivative (γ : PositiveSimpleContour)
    {U : Set ℂ} (hU : IsOpen U) (htrace : γ.val.trace ⊆ U) (hinterior : γ.interior ⊆ U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) {z : ℂ} (hz : z ∈ γ.interior) (k : ℕ) :
    Integrable (fun w ↦ ((w - z) ^ (k + 1))⁻¹ * g w)
      (PettisMeasure.complex γ.val.measure).variation ∧
    (PettisMeasure.complex γ.val.measure).scalarIntegral (fun w ↦ ((w - z) ^ (k + 1))⁻¹ * g w) =
      (2 * (Real.pi : ℂ) * Complex.I / (k.factorial : ℂ)) * iteratedDeriv k g z := by
  let K (n : ℕ) (w : ℂ) := ((w - z) ^ (n + 1))⁻¹
  let J (q : ℂ → ℂ) := ∫ t in Icc (0 : ℝ) 1,
    q (γ.val.toContinuousMap t) * deriv (fun s ↦ γ.val.toContinuousMap s) t
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hz' : z ∉ γ.val.trace := hz.1
  have hne (w : ℂ) (hw : w ∈ γ.val.trace) : w - z ≠ 0 :=
    sub_ne_zero.mpr (ne_of_mem_of_not_mem hw hz')
  have hK (n : ℕ) : ContinuousOn (K n) γ.val.trace :=
    ((continuousOn_id.sub continuousOn_const).pow _).inv₀ fun w hw ↦ pow_ne_zero _ (hne w hw)
  have hJ_add {q r : ℂ → ℂ} (hq : ContinuousOn q γ.val.trace)
      (hr : ContinuousOn r γ.val.trace) : J (fun w ↦ q w + r w) = J q + J r := by
    simp only [J, add_mul]
    exact integral_add (γ.val.integrableOn_mul_deriv hq) (γ.val.integrableOn_mul_deriv hr)
  have hJ_sub {q r : ℂ → ℂ} (hq : ContinuousOn q γ.val.trace)
      (hr : ContinuousOn r γ.val.trace) : J (fun w ↦ q w - r w) = J q - J r := by
    simp only [J, sub_mul]
    exact integral_sub (γ.val.integrableOn_mul_deriv hq) (γ.val.integrableOn_mul_deriv hr)
  have hJ_mul (b : ℂ) (q : ℂ → ℂ) : J (fun w ↦ b * q w) = b * J q := by
    simp only [J, mul_assoc, integral_const_mul]
  have hindex : ∀ w ∉ U, γ.val.index w = 0 := by
    intro w hw
    have hwt : w ∉ γ.val.trace := fun h ↦ hw (htrace h)
    exact (γ.property.2 w hwt).resolve_right fun h ↦ hw (hinterior ⟨hwt, h⟩)
  have hJ_zero : J (K 0) = c := by
    have hc : c ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    have hi := hz.2
    change c⁻¹ * (PettisMeasure.complex γ.val.measure).scalarIntegral (fun w ↦ (w - z)⁻¹) = 1 at hi
    have hK₀ : K 0 = fun w ↦ (w - z)⁻¹ := by ext w; simp [K]
    rw [← hK₀, (γ.val.scalarIntegral_eq_integral (hK 0)).2] at hi
    exact (inv_mul_eq_iff_eq_mul₀ hc).mp (show c⁻¹ * J (K 0) = 1 from hi) |>.trans (mul_one c)
  have hformula (n : ℕ) (q : ℂ → ℂ) (hq : DifferentiableOn ℂ q U) :
      J (fun w ↦ K n w * q w) = (c / (n.factorial : ℂ)) * iteratedDeriv n q z := by
    induction n generalizing q with
    | zero =>
      have hds := (Complex.differentiableOn_dslope (hU.mem_nhds (hinterior hz))).2 hq
      have heq : J (fun w ↦ K 0 w * q w) =
          J (fun w ↦ dslope q z w + q z * K 0 w) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro t ht
        have hwt : γ.val.toContinuousMap t ∈ γ.val.trace := mem_image_of_mem _ ht
        have hw := ne_of_mem_of_not_mem hwt hz'
        simp only [K, zero_add, pow_one, dslope_of_ne q hw, slope_def_field, div_eq_mul_inv]
        ring
      have hconst : ContinuousOn (fun w ↦ q z * K 0 w) γ.val.trace :=
        continuousOn_const.mul (hK 0)
      rw [heq, hJ_add (hds.continuousOn.mono htrace) hconst, hJ_mul, hJ_zero]
      rw [show J (dslope q z) = 0 from γ.integral_eq_zero_of_index_eq_zero hU htrace hindex hds]
      simp [mul_comm]
    | succ n ih =>
      have hq' := hq.deriv hU
      have hleft : ContinuousOn (fun w ↦ K n w * deriv q w) γ.val.trace :=
        (hK n).mul (hq'.continuousOn.mono htrace)
      have hright : ContinuousOn (fun w ↦ (n + 1 : ℂ) * (K (n + 1) w * q w)) γ.val.trace :=
        continuousOn_const.mul ((hK (n + 1)).mul (hq.continuousOn.mono htrace))
      have hpart : J (fun w ↦ K n w * deriv q w) =
          (n + 1 : ℂ) * J (fun w ↦ K (n + 1) w * q w) := by
        apply sub_eq_zero.mp
        rw [← hJ_mul (n + 1 : ℂ) (fun w ↦ K (n + 1) w * q w), ← hJ_sub hleft hright]
        apply γ.val.integral_eq_zero_of_hasDerivAt (g := fun w ↦ K n w * q w)
          _ (hleft.sub hright)
        intro w hw
        have hker : HasDerivAt (K n) (-(n + 1 : ℂ) * K (n + 1) w) w := by
          have h := (hasDerivAt_zpow (-((n + 1 : ℕ) : ℤ)) (w - z)
            (.inl (hne w hw))).comp_sub_const w z
          have hexp : -((n + 1 : ℕ) : ℤ) - 1 = -((n + 1 + 1 : ℕ) : ℤ) := by omega
          rw [hexp] at h
          simp only [zpow_neg, zpow_natCast, Int.cast_neg, Int.cast_natCast] at h
          simpa only [K, Nat.cast_add, Nat.cast_one] using h
        change HasDerivAt (fun u ↦ K n u * q u)
          (K n w * deriv q w - (n + 1 : ℂ) * (K (n + 1) w * q w)) w
        convert hker.mul (hq.hasDerivAt (hU.mem_nhds (htrace hw))) using 1
        ring
      rw [ih (deriv q) hq', ← iteratedDeriv_succ'] at hpart
      have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      apply (mul_left_cancel₀ hn)
      rw [← hpart, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      have hfact : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      field_simp [hn, hfact]
  obtain ⟨hi, heq⟩ := γ.val.scalarIntegral_eq_integral (g := fun w ↦ K k w * g w)
    ((hK k).mul (hg.continuousOn.mono htrace))
  exact ⟨hi, heq.trans (hformula k g hg)⟩

-- Retain the domain and target space hypotheses in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: (C.5.2.4), p. 738. The higher derivatives are given by Pettis
contour integrals with the Cauchy kernel and the factorial factor. -/
theorem hasPettisIntegral_cauchy_derivative (hf : ∀ k : ℕ, DifferentiableOn ℂ (deriv^[k] f) Ω)
    (γ : PositiveSimpleContour) (htrace : γ.val.trace ⊆ Ω) (hinterior : γ.interior ⊆ Ω)
    {z : ℂ} (hz : z ∈ γ.interior) (k : ℕ) :
    HasPettisIntegral (.complex γ.val.measure) (fun w ↦ ((w - z) ^ (k + 1))⁻¹ • f w)
      ((2 * (Real.pi : ℂ) * Complex.I / (k.factorial : ℂ)) • (deriv^[k] f) z) := by
  have hhol (φ : StrongDual ℂ E) : DifferentiableOn ℂ (φ ∘ f) Ω := fun w hw ↦
    (VectorHolomorphicOn.hasDerivAt_comp (hf 0) hΩ φ ⟨w, hw⟩).differentiableAt.differentiableWithinAt
  have hderiv (φ : StrongDual ℂ E) (n : ℕ) :
      EqOn (iteratedDeriv n (φ ∘ f)) (φ ∘ deriv^[n] f) Ω := by
    induction n with
    | zero => exact fun _ _ ↦ rfl
    | succ n ih =>
      intro w hw
      rw [iteratedDeriv_succ, (ih.eventuallyEq_of_mem (hΩ.mem_nhds hw)).deriv_eq]
      simpa only [Function.comp_apply, Function.iterate_succ_apply'] using
        (VectorHolomorphicOn.hasDerivAt_comp (hf n) hΩ φ ⟨w, hw⟩).deriv
  have hscalar (φ : StrongDual ℂ E) :=
    γ.scalarIntegral_cauchy_derivative hΩ htrace hinterior (hhol φ) hz k
  refine ⟨fun φ ↦ ?_, LinearMap.ext fun φ ↦ ?_⟩
  · simpa only [map_smul, smul_eq_mul, Function.comp_apply] using (hscalar φ).1
  · change φ ((2 * (Real.pi : ℂ) * Complex.I / (k.factorial : ℂ)) • (deriv^[k] f) z) =
      (PettisMeasure.complex γ.val.measure).scalarIntegral
        (fun w ↦ φ (((w - z) ^ (k + 1))⁻¹ • f w))
    simp only [map_smul, smul_eq_mul]
    have h := (hscalar φ).2
    rw [hderiv φ k (hinterior hz)] at h
    exact h.symm

omit [ContinuousSMul ℂ E] [T2Space E] hΩ [QuasiCompleteSpace ℂ E] hconn in
/-- Uniform convergence in a polynormable space is seminorm-smallness of the difference. -/
private theorem tendstoUniformlyOn_of_forall_continuous_seminorm
    {ι : Type*} {l : Filter ι} {F : ι → ℂ → E} {g : ℂ → E} {s : Set ℂ}
    (h : ∀ q : Seminorm ℂ E, Continuous q → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ i in l, ∀ x ∈ s, q (F i x - g x) < ε) :
    TendstoUniformlyOn F g l s := by
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have hbasis := (PolynormableSpace.hasBasis_zero_ball ℂ E).uniformity_of_nhds_zero
  rw [hbasis.tendstoUniformlyOn_iff_of_uniformity]
  intro p hp
  filter_upwards [h p hp 1 zero_lt_one] with i hi x hx
  simpa [Seminorm.mem_ball_zero] using hi x hx

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E] [QuasiCompleteSpace ℂ E] hconn in
/-- Weak holomorphy implies continuity: scalar Cauchy estimates are uniform on seminorm balls. -/
private theorem WeaklyHolomorphicOn.continuousOn_of_open (hf : WeaklyHolomorphicOn f Ω) :
    ContinuousOn f Ω := by
  intro z hz
  rw [continuousWithinAt_iff_continuousAt (hΩ.mem_nhds hz)]
  unfold ContinuousAt
  rw [(PolynormableSpace.withSeminorms ℂ E).tendsto_nhds f (f z)]
  intro q ε hε
  obtain ⟨R, hR, hsub⟩ := (Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hz))
  have hsphere : Metric.sphere z R ⊆ Ω := Metric.sphere_subset_closedBall.trans hsub
  have hbdd : IsVonNBounded ℂ (f '' Metric.sphere z R) := by
    refine isVonNBounded_of_dual_bounded fun φ ↦ ?_
    obtain ⟨C, hC⟩ :=
      ((isCompact_sphere z R).image_of_continuousOn
        ((hf φ).continuousOn.mono hsphere)).isBounded.exists_norm_le
    refine ⟨C, fun y hy ↦ ?_⟩
    obtain ⟨ξ, hξ, rfl⟩ := hy
    exact hC ((φ ∘ f) ξ) ⟨ξ, hξ, rfl⟩
  obtain ⟨M, hM⟩ :=
    ((PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bddAbove.mp hbdd q)
  let C := max M 1
  have hC (w) (hw : w ∈ Metric.sphere z R) : q.1 (f w) ≤ C :=
    le_max_of_le_left (hM (mem_image_of_mem q.1 (mem_image_of_mem f hw)))
  have hCpos : 0 < C := lt_max_of_lt_right zero_lt_one
  let δ := min (R / 2) (ε * R / (2 * C))
  have hδ : 0 < δ := by
    refine lt_min (half_pos hR) (div_pos (mul_pos hε hR) (mul_pos two_pos hCpos))
  filter_upwards [Metric.ball_mem_nhds z hδ] with w hw
  rcases eq_or_ne w z with rfl | hwz
  · simpa using hε
  · have hwR : dist w z < R / 2 := lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_left _ _)
    have hwball : w ∈ Metric.ball z R := Metric.mem_ball.mpr (hwR.trans (half_lt_self hR))
    obtain ⟨φ, hφ, heq⟩ := exists_dual_norm_eq_seminorm q.1 q.2 (f w - f z)
    have hd : DifferentiableOn ℂ (φ ∘ f) (Metric.closedBall z R) := (hf φ).mono hsub
    have hIw := hd.circleIntegral_sub_inv_smul hwball
    have hIz := hd.circleIntegral_sub_inv_smul (Metric.mem_ball_self hR)
    simp only [smul_eq_mul] at hIw hIz
    have hcont (c : ℂ) (hc : c ∈ Metric.ball z R) :
        ContinuousOn (fun ξ : ℂ ↦ (ξ - c)⁻¹ * (φ ∘ f) ξ) (Metric.sphere z R) := by
      refine ContinuousOn.mul ?_ (((hf φ).continuousOn).mono hsphere)
      refine (continuousOn_id.sub continuousOn_const).inv₀ fun ξ hξ hzero ↦ ?_
      have hξeq : ξ = c := sub_eq_zero.mp hzero
      rw [hξeq] at hξ
      exact Metric.sphere_disjoint_ball.notMem_of_mem_left hξ hc
    have hint (c : ℂ) (hc : c ∈ Metric.ball z R) :
        CircleIntegrable (fun ξ : ℂ ↦ (ξ - c)⁻¹ * (φ ∘ f) ξ) z R :=
      (hcont c hc).circleIntegrable hR.le
    have hdiffint := circleIntegral.integral_sub (hint w hwball) (hint z (Metric.mem_ball_self hR))
    have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hval : φ (f w) - φ (f z) =
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∮ ξ in C(z, R), ((ξ - w)⁻¹ - (ξ - z)⁻¹) * (φ ∘ f) ξ := by
      have hker :
          (∮ ξ in C(z, R), ((ξ - w)⁻¹ - (ξ - z)⁻¹) * (φ ∘ f) ξ) =
            (∮ ξ in C(z, R), (ξ - w)⁻¹ * (φ ∘ f) ξ) -
              ∮ ξ in C(z, R), (ξ - z)⁻¹ * (φ ∘ f) ξ := by
        have hfun :
            (fun ξ ↦ ((ξ - w)⁻¹ - (ξ - z)⁻¹) * (φ ∘ f) ξ) =
              fun ξ ↦ (ξ - w)⁻¹ * (φ ∘ f) ξ - (ξ - z)⁻¹ * (φ ∘ f) ξ := by
          funext ξ
          exact sub_mul _ _ _
        rw [circleIntegral.integral_congr hR.le (fun ξ _ ↦ congrFun hfun ξ)]
        exact hdiffint
      rw [hker, hIw, hIz, mul_sub]
      field_simp [h2pi]
      rfl
    set d := dist w z
    have hdpos : 0 < R - d := by linarith [hwR]
    have hbound : ∀ ξ ∈ Metric.sphere z R,
        ‖((ξ - w)⁻¹ - (ξ - z)⁻¹) * φ (f ξ)‖ ≤ d * C / ((R - d) * R) := by
      intro ξ hξ
      have hξz : ‖ξ - z‖ = R := by simpa [Metric.mem_sphere, dist_eq_norm] using hξ
      have hξw : R - d ≤ ‖ξ - w‖ := by
        have : ‖ξ - z‖ - ‖w - z‖ ≤ ‖(ξ - z) - (w - z)‖ := norm_sub_norm_le _ _
        simpa [sub_sub_sub_cancel_left, dist_eq_norm, d, hξz] using this
      have hpos : 0 < ‖ξ - w‖ := hdpos.trans_le hξw
      have hne : ξ - w ≠ 0 := norm_ne_zero_iff.mp hpos.ne'
      have hnez : ξ - z ≠ 0 := norm_ne_zero_iff.mp (hξz.trans_ne hR.ne')
      have halg : (ξ - w)⁻¹ - (ξ - z)⁻¹ = (w - z) / ((ξ - w) * (ξ - z)) := by
        field_simp [hne, hnez]
        ring
      have hwd : ‖w - z‖ = d := by simp [d, dist_eq_norm]
      rw [norm_mul, halg, norm_div, norm_mul, hξz, hwd]
      have hle : ‖φ (f ξ)‖ ≤ C := (hφ _).trans (hC _ hξ)
      calc
        d / (‖ξ - w‖ * R) * ‖φ (f ξ)‖ ≤ d / (‖ξ - w‖ * R) * C := by gcongr
        _ ≤ d / ((R - d) * R) * C := by gcongr
        _ = d * C / ((R - d) * R) := by ring
    have hintle := circleIntegral.norm_integral_le_of_norm_le_const hR.le hbound
    rw [← heq, map_sub, hval, norm_mul]
    have hinv : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ = (2 * Real.pi)⁻¹ := by simp
    rw [hinv]
    calc
      (2 * Real.pi)⁻¹ * ‖∮ ξ in C(z, R), ((ξ - w)⁻¹ - (ξ - z)⁻¹) * (φ ∘ f) ξ‖
          ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * R * (d * C / ((R - d) * R))) := by
            gcongr
            exact hintle
      _ = d * C / (R - d) := by
        field_simp [Real.pi_ne_zero, hR.ne', hdpos.ne']
      _ < ε := by
        rw [div_lt_iff₀ hdpos]
        have hdist : d * (2 * C) < ε * R :=
          (lt_div_iff₀ (mul_pos two_pos hCpos)).mp
            (lt_of_lt_of_le (Metric.mem_ball.mp hw) (min_le_right _ _))
        nlinarith [hdist, hwR, hε]

omit hconn in
/-- Lift a first scalar derivative by restricting to a smooth real curve inside the domain. -/
private theorem WeaklyHolomorphicOn.exists_eval_deriv (hf : WeaklyHolomorphicOn f Ω)
    {z : ℂ} (hz : z ∈ Ω) : ∃ b : E, ∀ φ : StrongDual ℂ E, φ b = deriv (φ ∘ f) z := by
  obtain ⟨R, hR, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hz)
  let c (t : ℝ) : ℂ := z + ((R * Real.sin t : ℝ) : ℂ)
  have hc (t) : c t ∈ Ω := by
    apply hsub
    simp only [c, Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_pos hR]
    exact mul_le_of_le_one_right hR.le (Real.abs_sin_le_one t)
  have hdiff : ContDiff ℝ 2 c := by
    apply contDiff_const.add
    exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul Real.contDiff_sin)
  obtain ⟨v, hv⟩ := exists_hasDerivAt_eval_zero_of_contDiff (F := f ∘ c)
    (fun φ ↦ (((hf φ).contDiffOn hΩ).restrict_scalars ℝ).comp_contDiff hdiff hc) inferInstance
  refine ⟨(R : ℂ)⁻¹ • v, fun φ ↦ ?_⟩
  have hc' : HasDerivAt c (R : ℂ) 0 := by
    simpa [c] using (((Real.hasDerivAt_sin 0).const_mul R).ofReal_comp.const_add z)
  have hd : HasDerivAt (φ ∘ f) (deriv (φ ∘ f) z) (c 0) := by
    simpa [c] using ((hf φ).differentiableAt (hΩ.mem_nhds hz)).hasDerivAt
  have he := (hv φ).unique (hd.scomp 0 hc')
  rw [map_smul, he, inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr hR.ne')]

omit hconn in
/-- Iteration gives vector representatives for all scalar derivatives on the open set. -/
private theorem WeaklyHolomorphicOn.exists_eval_iteratedDeriv (hf : WeaklyHolomorphicOn f Ω)
    (k : ℕ) : ∃ g : ℂ → E, WeaklyHolomorphicOn g Ω ∧
      ∀ φ : StrongDual ℂ E, EqOn (φ ∘ g) (iteratedDeriv k (φ ∘ f)) Ω := by
  classical
  induction k with
  | zero => exact ⟨f, hf, fun φ ↦ by simp [Set.EqOn]⟩
  | succ k ih =>
    obtain ⟨g, hg, he⟩ := ih
    let b (z : ℂ) : E := if hz : z ∈ Ω then (hg.exists_eval_deriv hΩ g hz).choose else 0
    have hb (φ : StrongDual ℂ E) : EqOn (φ ∘ b) (deriv (φ ∘ g)) Ω := by
      intro z hz
      simpa only [comp_apply, b, dite_eq_left hz] using (hg.exists_eval_deriv hΩ g hz).choose_spec φ
    exact ⟨b, fun φ ↦ ((hg φ).deriv hΩ).congr (hb φ), fun φ ↦ by
      rw [iteratedDeriv_succ]
      exact (hb φ).trans ((he φ).deriv hΩ)⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E] [QuasiCompleteSpace ℂ E] hconn in
/-- The Taylor errors on a closed subdisc remain bounded even after multiplication
by the truncation index: this can be tested on each functional separately. -/
private theorem WeaklyHolomorphicOn.bounded_taylorErrors (hf : WeaklyHolomorphicOn f Ω)
    {z : ℂ} {a : ℕ → E}
    (ha : ∀ (φ : StrongDual ℂ E) k, φ (a k) = iteratedDeriv k (φ ∘ f) z / k.factorial)
    {r : ℝ} (hr : 0 < r) (hs : Metric.closedBall z r ⊆ Ω) :
    IsVonNBounded ℂ (range fun x : ℕ × Metric.closedBall z r ↦ (x.1 : ℂ) •
      ((∑ k ∈ Finset.range x.1, ((x.2 : ℂ) - z) ^ k • a k) - f x.2)) := by
  obtain ⟨δ, hδ, hlarge⟩ := (isCompact_closedBall z r).exists_cthickening_subset_open hΩ hs
  rw [cthickening_closedBall hδ.le hr.le] at hlarge
  let R : NNReal := ⟨δ + r, by positivity⟩
  let ρ : NNReal := ⟨δ / 2 + r, by positivity⟩
  have hρ : ρ < R := by change δ / 2 + r < δ + r; linarith
  apply isVonNBounded_of_dual_bounded
  intro φ
  have hd : DifferentiableOn ℂ (φ ∘ f) (Metric.closedBall z R) := (hf φ).mono hlarge
  have hps := hd.hasFPowerSeriesOnBall (show 0 < R by change 0 < δ + r; positivity)
  rw [hps.hasFPowerSeriesAt.eq_formalMultilinearSeries hps.analyticAt.hasFPowerSeriesAt] at hps
  obtain ⟨t, ht, C, hC, hest⟩ := hps.uniform_geometric_approx (ENNReal.coe_lt_coe.mpr hρ)
  obtain ⟨M, hM⟩ := (tendsto_self_mul_const_pow_of_lt_one ht.1.le ht.2).bddAbove_range
  refine ⟨C * M, ?_⟩
  rintro _ ⟨⟨n, w⟩, rfl⟩
  have hw : (w : ℂ) - z ∈ Metric.ball 0 ρ := by
    rw [Metric.mem_ball, dist_zero_right]
    have hle := Metric.mem_closedBall.mp w.property
    rw [dist_eq_norm] at hle
    change _ < δ / 2 + r
    linarith
  have he := hest _ hw n
  simp only [add_sub_cancel, FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.ofScalars_apply_eq, comp_apply, smul_eq_mul] at he
  simp only [map_smul, map_sub, map_sum, ha, smul_eq_mul, norm_mul, Complex.norm_natCast]
  rw [norm_sub_rev]
  calc
    _ ≤ (n : ℝ) * (C * t ^ n) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      simpa only [mul_comm] using he
    _ = C * ((n : ℝ) * t ^ n) := by ring
    _ ≤ C * M := mul_le_mul_of_nonneg_left (hM (mem_range_self n)) hC.le

/-- Paper: Theorem C.5.2.6(1,4), p. 738. Weak holomorphy is equivalent to a
power series at every center that converges uniformly to the function on each closed
disc about that center contained in the domain. -/
theorem weaklyHolomorphicOn_iff_taylor :
    WeaklyHolomorphicOn f Ω ↔ ∀ z ∈ Ω, ∃ a : ℕ → E,
      ∀ r : ℝ, 0 < r → Metric.closedBall z r ⊆ Ω →
        TendstoUniformlyOn (fun n w ↦ ∑ k ∈ Finset.range n, (w - z) ^ k • a k)
          f atTop (Metric.closedBall z r) := by
  classical
  clear hconn
  constructor
  · intro hf z hz
    choose g _ he using hf.exists_eval_iteratedDeriv hΩ f
    let a (k : ℕ) : E := (k.factorial : ℂ)⁻¹ • g k z
    have ha (φ : StrongDual ℂ E) (k : ℕ) : φ (a k) = iteratedDeriv k (φ ∘ f) z / k.factorial := by
      simp only [a, map_smul, smul_eq_mul, div_eq_inv_mul]
      rw [show φ (g k z) = _ from he k φ hz]
    refine ⟨a, fun r hr hs ↦ ?_⟩
    have hb := hf.bounded_taylorErrors hΩ f ha hr hs
    apply tendstoUniformlyOn_of_forall_continuous_seminorm
    intro q hq ε hε
    obtain ⟨M, hM⟩ := (PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bddAbove.mp
      hb ⟨q, hq⟩
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop (M / ε),
      eventually_gt_atTop 0] with n hn hn₀ w hw
    have h := hM (mem_image_of_mem _ (mem_range_self (n, ⟨w, hw⟩)))
    change q ((n : ℂ) • _) ≤ M at h
    rw [map_smul_eq_mul, Complex.norm_natCast] at h
    exact lt_of_mul_lt_mul_left (h.trans_lt ((div_lt_iff₀ hε).mp hn)) (by positivity)
  · intro h φ z hz
    obtain ⟨a, ha⟩ := h z hz
    obtain ⟨r, hr, hs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds hz)
    have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
    have hlim : TendstoUniformlyOn
        (fun n w ↦ ∑ k ∈ Finset.range n, (w - z) ^ k * φ (a k)) (φ ∘ f) atTop
        (Metric.closedBall z r) := by
      simpa only [comp_def, map_sum, map_smul, smul_eq_mul] using
        φ.uniformContinuous.comp_tendstoUniformlyOn (ha r hr hs)
    have hd := (hlim.mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun n ↦ (Differentiable.fun_sum fun i _ ↦
        ((differentiable_id.sub_const z).pow i).mul_const (φ (a i))).differentiableOn) Metric.isOpen_ball
    exact (hd.differentiableAt (Metric.ball_mem_nhds z hr)).differentiableWithinAt

omit hΩ hconn in
/-- The Taylor series of a Banach-valued holomorphic function converges uniformly
on every smaller open disc. -/
private theorem taylor_uniformlyOn_normed {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [CompleteSpace F] {g : ℂ → F} {z : ℂ} {R r : NNReal} (hr : r < R)
    (hg : DifferentiableOn ℂ g (Metric.closedBall z R)) :
    TendstoUniformlyOn
      (fun n w ↦ ∑ k ∈ Finset.range n,
        ((w - z) ^ k / (k.factorial : ℂ)) • iteratedDeriv k g z)
      g atTop (Metric.ball z r) := by
  have hR : 0 < R := lt_of_le_of_lt zero_le hr
  have hs := hg.hasFPowerSeriesOnBall hR
  have hu := hs.tendstoUniformlyOn' (show (r : ENNReal) < R from by exact_mod_cast hr)
  convert hu using 1
  funext n w
  simp only [FormalMultilinearSeries.partialSum]
  apply Finset.sum_congr rfl
  intro k hk
  have he := hs.factorial_smul (w - z) k
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have hm := ((iteratedFDeriv ℂ k g z).map_smul_univ (fun _ ↦ w - z) (fun _ ↦ 1))
  simp only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_fin] at hm
  rw [hm] at he
  have hn : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  apply (smul_right_injective F hn)
  rw [← Nat.cast_smul_eq_nsmul ℂ] at he
  simpa [div_eq_mul_inv, smul_smul, mul_comm, mul_left_comm, mul_assoc, hn] using he.symm

/-- Paper: (C.5.2.5), p. 738. The Taylor coefficients are the vector derivatives
at the center divided by the corresponding factorials. -/
theorem tendstoUniformlyOn_taylor_derivatives (hf : ∀ k : ℕ,
    DifferentiableOn ℂ (deriv^[k] f) Ω) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hdisc : Metric.closedBall z r ⊆ Ω) :
    TendstoUniformlyOn
      (fun n w ↦ ∑ k ∈ Finset.range n,
        ((w - z) ^ k / (k.factorial : ℂ)) • (deriv^[k] f) z)
      f atTop (Metric.closedBall z r) := by
  obtain ⟨δ, hδ, hδsub⟩ := (isCompact_closedBall z r).exists_thickening_subset_open hΩ hdisc
  rw [thickening_closedBall hδ hr.le z] at hδsub
  let R : NNReal := ⟨r + δ / 2, by positivity⟩
  let R' : NNReal := ⟨r + δ / 4, by positivity⟩
  have hRR : R' < R := by change r + δ / 4 < r + δ / 2; linarith
  have hball : Metric.closedBall z (R : ℝ) ⊆ Ω :=
    (Metric.closedBall_subset_ball (by change r + δ / 2 < δ + r; linarith)).trans hδsub
  have hball' : Metric.closedBall z r ⊆ Metric.ball z (R' : ℝ) :=
    Metric.closedBall_subset_ball (by change r < r + δ / 4; linarith)
  rw [IsTopologicalAddGroup.tendstoUniformlyOn_iff _ _ _ _ rfl]
  intro u hu
  obtain ⟨p, hp, hpu⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp hu
  -- Pass to the Banach completion of the seminormed quotient associated to p.
  let e : ULift.{0} E ≃ₗ[ℂ] E := ULift.moduleEquiv
  let q : Seminorm ℂ (ULift.{0} E) := p.comp e.toLinearMap
  let group : SeminormedAddCommGroup (ULift.{0} E) := q.toSeminormedAddCommGroup
  let : UniformSpace (ULift.{0} E) := group.toUniformSpace
  let : TopologicalSpace (ULift.{0} E) := group.toUniformSpace.toTopologicalSpace
  let : NormedSpace ℂ (ULift.{0} E) := ⟨fun c v ↦ (map_smul_eq_mul q c v).le⟩
  let j₀ := UniformSpace.Completion.toComplL (S := ℂ) (α := ULift.{0} E)
  have he : Continuous e.symm := by
    rw [continuous_iff_continuousAt]
    intro v
    apply Metric.tendsto_nhds.mpr
    intro a ha
    have hp' : Continuous (fun y : E ↦ p (y - v)) :=
      hp.comp (continuous_id.sub continuous_const)
    simp only [dist_eq_norm, ← map_sub]
    change ∀ᶠ y : E in 𝓝 v, p (y - v) < a
    exact (hp'.continuousAt (x := v)).eventually_lt continuousAt_const (by simpa using ha)
  let j : E →L[ℂ] UniformSpace.Completion (ULift.{0} E) :=
    ⟨j₀.toLinearMap.comp e.symm.toLinearMap, j₀.continuous.comp he⟩
  have hcomp (k : ℕ) (w : Ω) :
      HasDerivAt (j ∘ deriv^[k] f) (j (deriv (deriv^[k] f) w)) (w : ℂ) := by
    have h := (hf k).hasFDerivAt (hΩ.mem_nhds w.property)
    have hj : HasFDerivAt (j ∘ deriv^[k] f) (j.comp (fderiv ℂ (deriv^[k] f) w)) (w : ℂ) := by
      apply HasFDerivAt.of_isLittleOTVS
      simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
        using j.isBigOTVS_comp.trans_isLittleOTVS h.isLittleOTVS
    exact hj.hasDerivAt
  have hiter (k : ℕ) (w : Ω) : iteratedDeriv k (j ∘ f) w = j ((deriv^[k] f) w) := by
    induction k generalizing w with
    | zero => simp
    | succ k ih =>
      rw [iteratedDeriv_succ, Function.iterate_succ_apply']
      have heq : iteratedDeriv k (j ∘ f) =ᶠ[𝓝 (w : ℂ)] (j ∘ deriv^[k] f) := by
        filter_upwards [hΩ.mem_nhds w.property] with x hx
        exact ih ⟨x, hx⟩
      rw [heq.deriv_eq]
      exact (hcomp k w).deriv
  have hdiff : DifferentiableOn ℂ (j ∘ f) (Metric.closedBall z R) := by
    intro w hw
    exact (hcomp 0 ⟨w, hball hw⟩).differentiableAt.differentiableWithinAt
  have huni := (taylor_uniformlyOn_normed hRR hdiff).mono hball'
  have hmetric := Metric.tendstoUniformlyOn_iff.mp huni 1 zero_lt_one
  filter_upwards [hmetric] with n hn w hw
  apply hpu
  rw [Seminorm.mem_ball_zero]
  have hw' := hn w hw
  rw [dist_comm, dist_eq_norm] at hw'
  have hz : z ∈ Ω := hdisc (Metric.mem_closedBall_self hr.le)
  simp only [hiter _ ⟨z, hz⟩, ← map_smul, ← map_sum, Function.comp_apply, ← map_sub] at hw'
  change ‖(↑(e.symm ((∑ k ∈ Finset.range n, ((w - z) ^ k / (k.factorial : ℂ)) •
    (deriv^[k] f) z) - f w)) : UniformSpace.Completion (ULift.{0} E))‖ < 1 at hw'
  rwa [UniformSpace.Completion.norm_coe] at hw'

/-- Paper: Theorem C.5.2.6, p. 738. In the quasi-complete case weak holomorphy
implies holomorphy in the target topology. -/
theorem WeaklyHolomorphicOn.vectorHolomorphicOn (hf : WeaklyHolomorphicOn f Ω) :
    VectorHolomorphicOn f Ω := by
  exact (weaklyHolomorphicOn_iff_all_derivatives hΩ hconn f).mp hf 0

omit [QuasiCompleteSpace ℂ E] in
/-- Paper: (C.5.2.6), p. 739. The weak derivative evaluates each continuous
linear functional to the corresponding scalar complex derivative. -/
theorem WeaklyHolomorphicOn.existsUnique_weakDerivative (hf : WeaklyHolomorphicOn f Ω)
    {z : ℂ} (hz : z ∈ Ω) (k : ℕ) :
    ∃! v : PettisWeakCompletion E, ∀ φ : StrongDual ℂ E,
      (show Module.Dual ℂ (StrongDual ℂ E) from v) φ = iteratedDeriv k (φ ∘ f) z := by
  clear hconn
  -- (C.5.2.6) defines the weak derivative in (E')* by scalar differentiation.
  let v : Module.Dual ℂ (StrongDual ℂ E) :=
    { toFun := fun φ ↦ iteratedDeriv k (φ ∘ f) z
      map_add' := fun φ ψ ↦ by
        have hφ : ContDiffAt ℂ k (φ ∘ f) z :=
          ((hf φ).contDiffOn hΩ).contDiffAt (hΩ.mem_nhds hz)
        have hψ : ContDiffAt ℂ k (ψ ∘ f) z :=
          ((hf ψ).contDiffOn hΩ).contDiffAt (hΩ.mem_nhds hz)
        have hsum : (φ + ψ) ∘ f = (φ ∘ f) + (ψ ∘ f) := by
          ext w
          simp
        rw [hsum]
        exact iteratedDeriv_add hφ hψ
      map_smul' := fun c φ ↦ by
        have hsmul : (c • φ) ∘ f = c • (φ ∘ f) := by
          ext w
          simp
        rw [hsmul]
        exact iteratedDeriv_const_smul_field c (φ ∘ f) }
  refine ⟨v, fun _ ↦ rfl, fun w hw ↦ ?_⟩
  apply LinearMap.ext
  intro φ
  exact hw φ

end Criteria

section Meromorphy

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
variable {Ω D : Set ℂ} {f : ℂ → E} {z : ℂ}

-- TODO(paper-gap): Definition C.5.3.1 prints k ≥ 0 as the lower Laurent exponent,
-- contradicting its pole-clearing condition and the signed lower exponent in (C.5.3.4).

/-- Paper: Definition C.5.3.1, p. 739. A meromorphic pair is holomorphic off a
discrete exceptional set, and at each exceptional point a power of the local
coordinate times the function extends holomorphically.
Deviation: Uses the paper's parenthetical pole-clearing criterion. The punctured
domain is explicitly open, so the exceptional set is relatively closed. -/
def IsVectorMeromorphicOn (f : ℂ → E) (Ω D : Set ℂ) : Prop :=
  D ⊆ Ω ∧ IsDiscrete D ∧ IsOpen (Ω \ D) ∧ VectorHolomorphicOn f (Ω \ D) ∧
    ∀ z ∈ D, ∃ (n : ℕ) (r : ℝ) (g : ℂ → E),
      0 < r ∧ Metric.ball z r \ {z} ⊆ Ω \ D ∧ VectorHolomorphicOn g (Metric.ball z r) ∧
      EqOn g (fun w ↦ (w - z) ^ n • f w) (Metric.ball z r \ {z})

/-- Paper: (C.5.3.2), p. 739. A local Laurent expansion has an
integer lower bound and its partial sums converge uniformly on compact subsets
of a punctured disc around the center.
Deviation: Uses the signed lower bound displayed in (C.5.3.4), with zero coefficients
below that bound. -/
def HasVectorLaurentSeriesAt (f : ℂ → E) (z : ℂ) (a : ℤ → E) : Prop :=
  ∃ (N : ℤ) (r : ℝ), 0 < r ∧ (∀ k < N, a k = 0) ∧
    ∀ K : Set ℂ, K ⊆ Metric.ball z r \ {z} → IsCompact K →
      TendstoUniformlyOn
        (fun n w ↦ ∑ j ∈ Finset.range n, (w - z) ^ (N + (j : ℤ)) • a (N + (j : ℤ)))
        f atTop K

-- TODO(paper-gap): The zero germ has no finite order. The lower summation bound
-- alone cannot define order because one can always pad the series with initial zeros.

/-- Paper: Definition C.5.3.1(1), p. 739. A finite order is the least Laurent
exponent with nonzero coefficient.
Deviation: This is a relation for finite order. The zero germ has no finite order. -/
def HasVectorMeromorphicOrderAt (f : ℂ → E) (z : ℂ) (k : ℤ) : Prop :=
  ∃ a : ℤ → E, HasVectorLaurentSeriesAt f z a ∧ a k ≠ 0 ∧ ∀ j < k, a j = 0

/-- Paper: Definition C.5.3.1(2), p. 739. A point is a pole if its Laurent order
is strictly negative. -/
def IsVectorPoleAt (f : ℂ → E) (z : ℂ) : Prop :=
  ∃ k : ℤ, k < 0 ∧ HasVectorMeromorphicOrderAt f z k

/-- Paper: Definition C.5.3.1, p. 739. The reciprocal is meromorphic with a simple
pole at zero and Laurent coefficient one at exponent minus one.
Deviation: This is a sanity check for meromorphy, the Laurent expansion, and order. -/
theorem vectorMeromorphic_inv :
    IsVectorMeromorphicOn (fun w : ℂ ↦ w⁻¹) univ {0} ∧
      HasVectorLaurentSeriesAt (fun w : ℂ ↦ w⁻¹) 0 (fun k ↦ if k = -1 then 1 else 0) ∧
      HasVectorMeromorphicOrderAt (fun w : ℂ ↦ w⁻¹) 0 (-1) ∧
      IsVectorPoleAt (fun w : ℂ ↦ w⁻¹) 0 := by
  let a : ℤ → ℂ := fun k ↦ if k = -1 then 1 else 0
  have hsum (n : ℕ) (hn : 1 ≤ n) (w : ℂ) :
      ∑ j ∈ Finset.range n, (w - 0) ^ (-1 + (j : ℤ)) • a (-1 + (j : ℤ)) = w⁻¹ := by
    rw [Finset.sum_eq_single 0]
    · simp [a]
    · intro j _ hj
      have : (-1 + (j : ℤ)) ≠ -1 := by omega
      simp [a, this]
    · intro h
      exact absurd (Finset.mem_range.mpr hn) h
  have hL : HasVectorLaurentSeriesAt (fun w : ℂ ↦ w⁻¹) 0 a := by
    refine ⟨-1, 1, one_pos, fun k hk ↦ ?_, fun K _ _ ↦ ?_⟩
    · simp [a, hk.ne]
    · intro u hu
      filter_upwards [eventually_ge_atTop 1] with n hn x _
      rw [hsum n hn x]
      exact @refl_mem_uniformity ℂ (IsTopologicalAddGroup.rightUniformSpace ℂ) _ _ hu
  have hO : HasVectorMeromorphicOrderAt (fun w : ℂ ↦ w⁻¹) 0 (-1) :=
    ⟨a, hL, by simp [a], fun j hj ↦ by simp [a, hj.ne]⟩
  refine ⟨⟨subset_univ _, Set.subsingleton_singleton.isDiscrete,
    isOpen_univ.sdiff isClosed_singleton, fun w hw ↦ ?_, ?_⟩, hL, hO, ⟨-1, by norm_num, hO⟩⟩
  · have hw0 : w ≠ 0 := hw.2
    exact (differentiableAt_inv (𝕜 := ℂ) hw0).differentiableWithinAt
  · rintro z rfl
    refine ⟨1, 1, fun _ ↦ 1, one_pos, fun w hw ↦ ⟨mem_univ w, hw.2⟩,
      differentiableOn_const 1, fun w hw ↦ ?_⟩
    have hw0 : w ≠ 0 := hw.2
    simp [hw0]

-- TODO(paper-gap): The pairs (f, D) have no specified identification when D
-- changes. Residue linearity below uses the common domain of the representatives.

variable [T2Space E] [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E]
/-! ### Local Laurent expansions -/

/-- Integer powers of the local coordinate are continuous away from the center. -/
private theorem continuousOn_zpow_sub {z : ℂ} {e : ℤ} {s : Set ℂ}
    (hs : ∀ w ∈ s, w - z ≠ 0) : ContinuousOn (fun w ↦ (w - z) ^ e) s := by
  rcases le_or_gt 0 e with hpos | hneg
  · have heq : ∀ w : ℂ, (w - z) ^ e = (w - z) ^ (e.toNat : ℕ) := fun w =>
      (congrArg (fun x : ℤ => (w - z) ^ x) (Int.toNat_of_nonneg hpos).symm).trans
        (zpow_natCast (w - z) e.toNat)
    simp only [heq]
    exact (continuousOn_id.sub continuousOn_const).pow _
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, e = -(((m + 1 : ℕ) : ℕ) : ℤ) :=
      ⟨(-e - 1).toNat, by
        have h1 : (((-e - 1).toNat : ℕ) : ℤ) = -e - 1 :=
          Int.toNat_of_nonneg (show (0 : ℤ) ≤ -e - 1 by omega)
        push_cast
        rw [h1]
        omega⟩
    have heq : ∀ w : ℂ, (w - z) ^ e = ((w - z) ^ (m + 1 : ℕ))⁻¹ := by
      intro w
      rw [hm, zpow_neg, zpow_natCast]
    simp only [heq]
    exact ContinuousOn.inv₀ ((continuousOn_id.sub continuousOn_const).pow _)
      (fun w hw => pow_ne_zero (m + 1) (hs w hw))

omit [ContinuousSMul ℂ E] [T2Space E] [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E] in
/-- A holomorphic function is weakly holomorphic. -/
private theorem vectorHolomorphicOn_weaklyHolomorphic {U : Set ℂ} (hU : IsOpen U)
    {g : ℂ → E} (hg : VectorHolomorphicOn g U) : WeaklyHolomorphicOn g U := by
  intro φ v hv
  have h := VectorHolomorphicOn.hasDerivAt_comp hg hU φ ⟨v, hv⟩
  exact h.differentiableAt.differentiableWithinAt

omit [ContinuousSMul ℂ E] [T2Space E] [QuasiCompleteSpace ℂ E] in
/-- Uniform convergence in the target is preserved by multiplication with a scalar
function bounded on the set. -/
private theorem TendstoUniformlyOn.bounded_smul {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → E} {g : ℂ → E} {s : Set ℂ} (h : TendstoUniformlyOn F g l s)
    (c : ℂ → ℂ) (hB : ∃ B : ℝ, ∀ w ∈ s, ‖c w‖ ≤ B) :
    TendstoUniformlyOn (fun i w ↦ c w • F i w) (fun w ↦ c w • g w) l s := by
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  rw [IsTopologicalAddGroup.tendstoUniformlyOn_iff _ _ _ _ rfl] at h ⊢
  intro u hu
  obtain ⟨B, hB⟩ := hB
  obtain ⟨q, hq, hqu⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp hu
  let δ : ℝ := 1 / (max B 1)
  have hδ : 0 < δ := by positivity
  filter_upwards [h (q.ball 0 δ) (q.ball_mem_nhds hq hδ)] with i hi w hw
  apply hqu
  rw [Seminorm.mem_ball_zero, ← smul_sub]
  have hlt : q (F i w - g w) < δ := by simpa [Seminorm.mem_ball_zero] using hi w hw
  calc q (c w • (F i w - g w))
      = ‖c w‖ * q (F i w - g w) := map_smul_eq_mul q _ _
    _ ≤ max B 1 * q (F i w - g w) :=
        mul_le_mul_of_nonneg_right ((hB w hw).trans (le_max_left _ _)) (apply_nonneg q _)
    _ < max B 1 * δ := mul_lt_mul_of_pos_left hlt (by positivity)
    _ = 1 := by
        simp only [δ]
        exact mul_div_cancel₀ 1 (by positivity)

omit [ContinuousSMul ℂ E] [T2Space E] [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E] in
/-- On a circle in the punctured disc of convergence, integrating a scalar evaluation
of the function against the local coordinate to the power `-k - 1` gives `2πi`
times the scalar evaluation of the Laurent coefficient at `k`. -/
private theorem circleIntegral_dual_laurentCoeff {a : ℤ → E}
    {N : ℤ} {r R : ℝ} (hR : 0 < R) (hRr : R < r) (hzero : ∀ k < N, a k = 0)
    (hconv : ∀ K : Set ℂ, K ⊆ Metric.ball z r \ {z} → IsCompact K →
      TendstoUniformlyOn
        (fun n w ↦ ∑ j ∈ Finset.range n, (w - z) ^ (N + (j : ℤ)) • a (N + (j : ℤ)))
        f atTop K)
    (φ : StrongDual ℂ E) (k : ℤ) :
    circleIntegral (fun w ↦ (w - z) ^ (-k - 1) * φ (f w)) z R =
      (2 * (Real.pi : ℂ) * Complex.I) * φ (a k) := by
  have hne (w : ℂ) (hw : w ∈ Metric.sphere z R) : w - z ≠ 0 :=
    sub_ne_zero.mpr (Metric.ne_of_mem_sphere hw hR.ne')
  have hsub : Metric.sphere z R ⊆ Metric.ball z r \ {z} := by
    intro w hw
    exact ⟨Metric.mem_ball.mpr ((Metric.mem_sphere.mp hw).trans_lt hRr),
      sub_ne_zero.mp (hne w hw)⟩
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : UniformSpace ℂ := PseudoMetricSpace.toUniformSpace
  have hscalar := φ.uniformContinuous.comp_tendstoUniformlyOn
    (hconv _ hsub (isCompact_sphere z R))
  let term (j : ℕ) (w : ℂ) := (w - z) ^ (N + (j : ℤ) - k - 1) • φ (a (N + (j : ℤ)))
  have hterm (j : ℕ) : ContinuousOn (term j) (Metric.sphere z R) :=
    ((continuousOn_id.sub continuousOn_const).zpow₀ _ fun w hw ↦ Or.inl (hne w hw)).smul
      continuousOn_const
  have hweighted : TendstoUniformlyOn (fun n w ↦ ∑ j ∈ Finset.range n, term j w)
      (fun w ↦ (w - z) ^ (-k - 1) * φ (f w)) atTop (Metric.sphere z R) := by
    rw [Metric.tendstoUniformlyOn_iff] at hscalar ⊢
    intro ε hε
    have hbound : 0 < R ^ (-k - 1) := zpow_pos hR _
    filter_upwards [hscalar (ε / R ^ (-k - 1)) (div_pos hε hbound)] with n hn w hw
    have hsum :
        ∑ j ∈ Finset.range n, term j w =
          (w - z) ^ (-k - 1) * φ (∑ j ∈ Finset.range n,
            (w - z) ^ (N + (j : ℤ)) • a (N + (j : ℤ))) := by
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hexp : N + (j : ℤ) - k - 1 = (-k - 1) + (N + (j : ℤ)) := by omega
      simp [term, hexp, zpow_add₀ (hne w hw), smul_eq_mul, mul_assoc]
    have hnorm : ‖w - z‖ = R := by simpa only [dist_eq_norm] using Metric.mem_sphere.mp hw
    rw [hsum, dist_eq_norm, ← mul_sub, norm_mul, norm_zpow, hnorm, ← dist_eq_norm,
      ← lt_div_iff₀' hbound]
    exact hn w hw
  have hlim := hweighted.tendsto_circleIntegral_of_continuousOn hR.le
    (Eventually.of_forall fun n ↦ continuousOn_finsetSum _ fun j _ ↦ hterm j)
  have hintegral (j : ℕ) : circleIntegral (term j) z R =
      if N + (j : ℤ) = k then (2 * (Real.pi : ℂ) * Complex.I) * φ (a k) else 0 := by
    dsimp only [term]
    rw [circleIntegral.integral_smul_const]
    split_ifs with hj
    · rw [hj, show k - k - 1 = (-1 : ℤ) by omega]
      simp only [zpow_neg_one, circleIntegral.integral_sub_center_inv z hR.ne', smul_eq_mul]
    · have hpow : N + (j : ℤ) - k - 1 ≠ -1 := by omega
      rw [circleIntegral.integral_sub_zpow_of_ne hpow, zero_smul]
  -- Only the summand whose shifted exponent is minus one contributes.
  have heventual : ∀ᶠ n : ℕ in atTop, circleIntegral (fun w ↦ ∑ j ∈ Finset.range n, term j w)
      z R = (2 * (Real.pi : ℂ) * Complex.I) * φ (a k) := by
    filter_upwards [eventually_gt_atTop (k - N).toNat] with n hn
    rw [circleIntegral.integral_fun_sum fun j _ ↦ ContinuousOn.circleIntegrable hR.le (hterm j)]
    simp only [hintegral]
    by_cases hk : N ≤ k
    · have hj : N + ((k - N).toNat : ℤ) = k := by omega
      rw [Finset.sum_eq_single (k - N).toNat]
      · rw [ite_eq_left hj]
      · intro j _ hj'
        have : N + (j : ℤ) ≠ k := by omega
        simp [this]
      · exact fun h ↦ (h (Finset.mem_range.mpr hn)).elim
    · have hak : a k = 0 := hzero k (lt_of_not_ge hk)
      have hj (j : ℕ) : N + (j : ℤ) ≠ k := by omega
      simp [hj, hak]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (heventual.mono fun _ hn ↦ hn.symm))

omit [ContinuousSMul ℂ E] [QuasiCompleteSpace ℂ E] in
/-- A vector Laurent series is determined by its scalarizations, each of which is
recovered from a circle integral. -/
private theorem HasVectorLaurentSeriesAt.unique {a b : ℤ → E}
    (ha : HasVectorLaurentSeriesAt f z a) (hb : HasVectorLaurentSeriesAt f z b) : a = b := by
  let _ : SeparatingDual ℂ E := polynormableSpace_separatingDual ℂ E
  obtain ⟨Na, ra, hra, hza, hconva⟩ := ha
  obtain ⟨Nb, rb, hrb, hzb, hconvb⟩ := hb
  have hmin : 0 < min ra rb := lt_min hra hrb
  have hR : 0 < min ra rb / 2 := by positivity
  have hRa : min ra rb / 2 < ra := (half_lt_self hmin).trans_le (min_le_left _ _)
  have hRb : min ra rb / 2 < rb := (half_lt_self hmin).trans_le (min_le_right _ _)
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  ext k
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)]
  intro φ
  exact mul_left_cancel₀ hc
    ((circleIntegral_dual_laurentCoeff hR hRa hza hconva φ k).symm.trans
      (circleIntegral_dual_laurentCoeff hR hRb hzb hconvb φ k))

omit [ContinuousSMul ℂ E] [T2Space E] [QuasiCompleteSpace ℂ E] in
/-- A holomorphic Taylor expansion, divided by a power of the local coordinate,
is a Laurent expansion of the cleared function. -/
private theorem hasVectorLaurentSeriesAt_of_taylor {g : ℂ → E} {b : ℕ → E} {n : ℕ} {r : ℝ}
    (hr : 0 < r)
    (hb : ∀ ρ : ℝ, 0 < ρ → Metric.closedBall z ρ ⊆ Metric.ball z r →
      TendstoUniformlyOn (fun m w ↦ ∑ k ∈ Finset.range m, (w - z) ^ k • b k)
        g atTop (Metric.closedBall z ρ))
    (heq : EqOn g (fun w ↦ (w - z) ^ n • f w) (Metric.ball z r \ {z})) :
    HasVectorLaurentSeriesAt f z
      (fun k : ℤ ↦ if -(n : ℤ) ≤ k then b (k + n).toNat else 0) := by
  let N : ℤ := -(n : ℤ)
  let a : ℤ → E := fun k ↦ if N ≤ k then b (k - N).toNat else 0
  have ha_eq : a = fun k : ℤ ↦ if -(n : ℤ) ≤ k then b (k + n).toNat else 0 := by
    funext k
    simp only [a, N, sub_eq_add_neg, neg_neg]
  rw [← ha_eq]
  refine ⟨N, r, hr, fun k hk ↦ by simp [a, hk.not_ge], fun K hK hKcomp ↦ ?_⟩
  obtain ⟨ρ, hρ0, hρr, hKρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧ K ⊆ Metric.closedBall z ρ := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact ⟨r / 2, by positivity, by linarith, by simp⟩
    · obtain ⟨w, hw, hmax⟩ := hKcomp.exists_isMaxOn hne
        (continuous_id.dist continuous_const).continuousOn
      exact ⟨dist w z, dist_pos.mpr (hK hw).2, Metric.mem_ball.mp (hK hw).1,
        fun x hx ↦ Metric.mem_closedBall.mpr (hmax hx)⟩
  have huni := (hb ρ hρ0 (Metric.closedBall_subset_ball hρr)).mono hKρ
  let c : ℂ → ℂ := fun w ↦ (w - z) ^ N
  have hcne : ∀ w ∈ K, w - z ≠ 0 := fun w hw ↦ sub_ne_zero.mpr (hK hw).2
  have hB : ∃ B : ℝ, ∀ w ∈ K, ‖c w‖ ≤ B :=
    ⟨_, hKcomp.exists_bound_of_continuousOn (continuousOn_zpow_sub hcne) |>.choose_spec⟩
  have hsmul := TendstoUniformlyOn.bounded_smul huni c hB
  have hpartial : ∀ m : ℕ, EqOn
      (fun w ↦ c w • ∑ j ∈ Finset.range m, (w - z) ^ j • b j)
      (fun w ↦ ∑ j ∈ Finset.range m, (w - z) ^ (N + (j : ℤ)) • a (N + (j : ℤ))) K := by
    intro m w hw
    show c w • (∑ j ∈ Finset.range m, (w - z) ^ j • b j) =
      ∑ j ∈ Finset.range m, (w - z) ^ (N + (j : ℤ)) • a (N + (j : ℤ))
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hle : N ≤ N + (j : ℤ) := by omega
    have hidx : (N + (j : ℤ) - N).toNat = j := by
      rw [add_sub_cancel_left, Int.toNat_natCast]
    simp only [a, ite_eq_left hle, hidx, smul_smul]
    rw [← zpow_natCast (w - z) j, zpow_add₀ (hcne w hw)]
  have hlim : EqOn (fun w ↦ c w • g w) f K := by
    intro w hw
    show c w • g w = f w
    have hgw : g w = (w - z) ^ n • f w := heq ⟨(hK hw).1, (hK hw).2⟩
    have hne := hcne w hw
    rw [hgw]
    change (w - z) ^ N • ((w - z) ^ n • f w) = f w
    rw [smul_smul, ← zpow_natCast (w - z) n, ← zpow_add₀ hne]
    have hexp : N + (n : ℤ) = 0 := by simp [N]
    rw [hexp, zpow_zero, one_smul]
  exact TendstoUniformlyOn.congr_right
    (TendstoUniformlyOn.congr hsmul (Eventually.of_forall hpartial)) hlim

/-- Paper: Definition C.5.3.1, p. 739. Every point of the domain of a meromorphic
pair has a unique local Laurent expansion in the original target.
Deviation: Includes the ordinary Taylor expansion at points outside the exceptional set. -/
theorem IsVectorMeromorphicOn.existsUnique_laurentSeries (hΩ : IsOpen Ω)
    (hf : IsVectorMeromorphicOn f Ω D) (hz : z ∈ Ω) :
    ∃! a : ℤ → E, HasVectorLaurentSeriesAt f z a := by
  have : IsOpen Ω := hΩ
  suffices ∃ a : ℤ → E, HasVectorLaurentSeriesAt f z a by
    obtain ⟨a, ha⟩ := this
    exact existsUnique_of_exists_of_unique ⟨a, ha⟩ fun a₁ a₂ ha₁ ha₂ ↦
      HasVectorLaurentSeriesAt.unique ha₁ ha₂
  by_cases hzD : z ∈ D
  · obtain ⟨n, r, g, hr, -, hg, heq⟩ := hf.2.2.2.2 z hzD
    have hweak : WeaklyHolomorphicOn g (Metric.ball z r) :=
      vectorHolomorphicOn_weaklyHolomorphic Metric.isOpen_ball hg
    obtain ⟨b, hb⟩ :=
      (weaklyHolomorphicOn_iff_taylor Metric.isOpen_ball (Metric.isConnected_ball hr) g).mp
      hweak z (Metric.mem_ball_self hr)
    exact ⟨_, hasVectorLaurentSeriesAt_of_taylor hr hb heq⟩
  · have hopen : IsOpen (Ω \ D) := hf.2.2.1
    obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_ball.mem_iff.mp (hopen.mem_nhds ⟨hz, hzD⟩)
    have hg : VectorHolomorphicOn f (Metric.ball z r) := hf.2.2.2.1.mono hsub
    have hweak : WeaklyHolomorphicOn f (Metric.ball z r) :=
      vectorHolomorphicOn_weaklyHolomorphic Metric.isOpen_ball hg
    obtain ⟨b, hb⟩ :=
      (weaklyHolomorphicOn_iff_taylor Metric.isOpen_ball (Metric.isConnected_ball hr) f).mp
      hweak z (Metric.mem_ball_self hr)
    have heq : EqOn f (fun w ↦ (w - z) ^ (0 : ℕ) • f w) (Metric.ball z r \ {z}) := by
      intro w _
      simp
    exact ⟨_, hasVectorLaurentSeriesAt_of_taylor hr hb heq⟩

/-- Paper: Coefficient notation in Lemma C.5.3.2, p. 740. A coefficient is read
from the local Laurent expansion, with existence supplied as evidence. -/
def vectorLaurentCoeff (h : ∃ a : ℤ → E, HasVectorLaurentSeriesAt f z a) (k : ℤ) : E :=
  Classical.choose h k

omit [ContinuousSMul ℂ E] [T2Space E] [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E] in
/-- On a circle in the punctured disc, integrating a scalar evaluation of the
Laurent expansion against the local coordinate to the power `-k - 1` gives
`2πi` times the scalar evaluation of the coefficient at `k`. -/
private theorem HasVectorLaurentSeriesAt.circleIntegral_coeff {a : ℤ → E}
    {N : ℤ} {r R : ℝ} (hR : 0 < R) (hRr : R < r) (hzero : ∀ k < N, a k = 0)
    (hconv : ∀ K : Set ℂ, K ⊆ Metric.ball z r \ {z} → IsCompact K →
      TendstoUniformlyOn
        (fun n w ↦ ∑ j ∈ Finset.range n, (w - z) ^ (N + (j : ℤ)) • a (N + (j : ℤ)))
        f atTop K)
    (φ : StrongDual ℂ E) (k : ℤ) :
    circleIntegral (fun w ↦ (w - z) ^ (-k - 1) * φ (f w)) z R =
      (2 * (Real.pi : ℂ) * Complex.I) * φ (a k) := by
  have hne (w : ℂ) (hw : w ∈ Metric.sphere z R) : w - z ≠ 0 :=
    sub_ne_zero.mpr (Metric.ne_of_mem_sphere hw hR.ne')
  have hsub : Metric.sphere z R ⊆ Metric.ball z r \ {z} := by
    intro w hw
    exact ⟨Metric.mem_ball.mpr ((Metric.mem_sphere.mp hw).trans_lt hRr),
      sub_ne_zero.mp (hne w hw)⟩
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : UniformSpace ℂ := PseudoMetricSpace.toUniformSpace
  have hscalar := φ.uniformContinuous.comp_tendstoUniformlyOn
    (hconv _ hsub (isCompact_sphere z R))
  let term (j : ℕ) (w : ℂ) := (w - z) ^ (N + (j : ℤ) - k - 1) • φ (a (N + (j : ℤ)))
  have hterm (j : ℕ) : ContinuousOn (term j) (Metric.sphere z R) :=
    ((continuousOn_id.sub continuousOn_const).zpow₀ _ fun w hw ↦ Or.inl (hne w hw)).smul
      continuousOn_const
  have hweighted : TendstoUniformlyOn (fun n w ↦ ∑ j ∈ Finset.range n, term j w)
      (fun w ↦ (w - z) ^ (-k - 1) * φ (f w)) atTop (Metric.sphere z R) := by
    rw [Metric.tendstoUniformlyOn_iff] at hscalar ⊢
    intro ε hε
    have hbound : 0 < R ^ (-k - 1) := zpow_pos hR _
    filter_upwards [hscalar (ε / R ^ (-k - 1)) (div_pos hε hbound)] with n hn w hw
    have hsum :
        ∑ j ∈ Finset.range n, term j w =
          (w - z) ^ (-k - 1) * φ (∑ j ∈ Finset.range n,
            (w - z) ^ (N + (j : ℤ)) • a (N + (j : ℤ))) := by
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hexp : N + (j : ℤ) - k - 1 = (-k - 1) + (N + (j : ℤ)) := by omega
      simp [term, hexp, zpow_add₀ (hne w hw), smul_eq_mul, mul_assoc]
    have hnorm : ‖w - z‖ = R := by simpa only [dist_eq_norm] using Metric.mem_sphere.mp hw
    rw [hsum, dist_eq_norm, ← mul_sub, norm_mul, norm_zpow, hnorm, ← dist_eq_norm,
      ← lt_div_iff₀' hbound]
    exact hn w hw
  have hlim := hweighted.tendsto_circleIntegral_of_continuousOn hR.le
    (Eventually.of_forall fun n ↦ continuousOn_finsetSum _ fun j _ ↦ hterm j)
  have hintegral (j : ℕ) : circleIntegral (term j) z R =
      if N + (j : ℤ) = k then (2 * (Real.pi : ℂ) * Complex.I) * φ (a k) else 0 := by
    dsimp only [term]
    rw [circleIntegral.integral_smul_const]
    split_ifs with hj
    · rw [hj, show k - k - 1 = (-1 : ℤ) by omega]
      simp only [zpow_neg_one, circleIntegral.integral_sub_center_inv z hR.ne', smul_eq_mul]
    · have hpow : N + (j : ℤ) - k - 1 ≠ -1 := by omega
      rw [circleIntegral.integral_sub_zpow_of_ne hpow, zero_smul]
  -- Only the summand whose exponent is shifted to minus one contributes.
  have heventual : ∀ᶠ n : ℕ in atTop, circleIntegral (fun w ↦ ∑ j ∈ Finset.range n, term j w)
      z R = (2 * (Real.pi : ℂ) * Complex.I) * φ (a k) := by
    filter_upwards [eventually_gt_atTop (k - N).toNat] with n hn
    rw [circleIntegral.integral_fun_sum fun j _ ↦ ContinuousOn.circleIntegrable hR.le (hterm j)]
    simp only [hintegral]
    by_cases hk : N ≤ k
    · have hj : N + ((k - N).toNat : ℤ) = k := by omega
      rw [Finset.sum_eq_single (k - N).toNat]
      · rw [ite_eq_left hj]
      · intro j _ hj'
        have : N + (j : ℤ) ≠ k := by omega
        simp [this]
      · exact fun h ↦ (h (Finset.mem_range.mpr hn)).elim
    · have hak : a k = 0 := hzero k (lt_of_not_ge hk)
      have hj (j : ℕ) : N + (j : ℤ) ≠ k := by omega
      simp [hj, hak]
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (heventual.mono fun _ hn ↦ hn.symm))

-- Retain the target space hypotheses in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Coefficient notation in Lemma C.5.3.2, p. 740. Reading a coefficient
from a specified expansion reproduces the coefficient at the requested exponent.
Deviation: This is a sanity check for the coefficient operation. -/
theorem vectorLaurentCoeff_eq {a : ℤ → E} (ha : HasVectorLaurentSeriesAt f z a)
    (h : ∃ a : ℤ → E, HasVectorLaurentSeriesAt f z a) (k : ℤ) :
    vectorLaurentCoeff h k = a k := by
  change Classical.choose h k = a k
  obtain ⟨M, s, hs, hbzero, hbconv⟩ := Classical.choose_spec h
  obtain ⟨N, r, hr, hazero, haconv⟩ := ha
  let R := min r s / 2
  have hR : 0 < R := half_pos (lt_min hr hs)
  have hRmin : R < min r s := half_lt_self (lt_min hr hs)
  have hfactor : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  let : SeparatingDual ℂ E := polynormableSpace_separatingDual ℂ E
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr fun φ ↦ ?_
  have hbcoeff := HasVectorLaurentSeriesAt.circleIntegral_coeff hR
    (hRmin.trans_le (min_le_right r s)) hbzero hbconv φ k
  have hacoeff := HasVectorLaurentSeriesAt.circleIntegral_coeff hR
    (hRmin.trans_le (min_le_left r s)) hazero haconv φ k
  exact mul_left_cancel₀ hfactor (hbcoeff.symm.trans hacoeff)

/-- The denominator in the Taylor kernel accounts for the power used to clear the pole. -/
private theorem laurentKernel_mul_pow {x : ℂ} (hx : x ≠ 0) (n j : ℕ) :
    (x ^ (j + 1))⁻¹ * x ^ n = x ^ (-((j : ℤ) - n) - 1) := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hx]
  congr 1
  omega

omit [ContinuousSMul ℂ E] [T2Space E] [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E] in
/-- Clearing a pole shifts the Laurent exponent `j - n` to the Taylor exponent `j`. -/
private theorem HasVectorLaurentSeriesAt.coeff_eq_derivative_of_cleared {a : ℤ → E}
    (ha : HasVectorLaurentSeriesAt f z a) (φ : StrongDual ℂ E) (n j : ℕ)
    {q : ℂ → ℂ} {s : ℝ} (hs : 0 < s) (hq : DifferentiableOn ℂ q (Metric.ball z s))
    (heq : EqOn q (fun w ↦ (w - z) ^ n * φ (f w)) (Metric.ball z s \ {z})) :
    φ (a ((j : ℤ) - n)) = iteratedDeriv j q z / (j.factorial : ℂ) := by
  obtain ⟨N, r, hr, hzero, hconv⟩ := ha
  let R := min r s / 2
  have hR : 0 < R := half_pos (lt_min hr hs)
  have hRr : R < r := (half_lt_self (lt_min hr hs)).trans_le (min_le_left _ _)
  have hRs : R < s := (half_lt_self (lt_min hr hs)).trans_le (min_le_right _ _)
  have hcauchy := DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul hR j
    (hq.mono (Metric.closedBall_subset_ball hRs))
  have hlocal := HasVectorLaurentSeriesAt.circleIntegral_coeff hR hRr hzero hconv φ ((j : ℤ) - n)
  have hkernel := circleIntegral.integral_congr (c := z) hR.le
    (f := fun w ↦ (w - z) ^ (-((j : ℤ) - n) - 1) * φ (f w))
    (g := fun w ↦ (1 / (w - z) ^ (j + 1)) • q w) (by
      intro w hw
      have hwz := Metric.ne_of_mem_sphere hw hR.ne'
      dsimp only
      rw [smul_eq_mul, one_div, heq ⟨Metric.mem_ball.mpr ((Metric.mem_sphere.mp hw).trans_lt hRs), hwz⟩]
      dsimp only
      rw [← mul_assoc, laurentKernel_mul_pow (sub_ne_zero.mpr hwz)])
  rw [← hkernel, hlocal, smul_eq_mul, div_mul_eq_mul_div, mul_div_assoc] at hcauchy
  exact mul_left_cancel₀
    (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero) hcauchy

omit [ContinuousSMul ℂ E] [T2Space E] [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E] in
/-- If the Laurent series has a nonzero negative term, its first nonzero term gives a pole. -/
private theorem HasVectorLaurentSeriesAt.eq_zero_of_not_pole {a : ℤ → E}
    (ha : HasVectorLaurentSeriesAt f z a) (hz : ¬ IsVectorPoleAt f z) {k : ℤ} (hk : k < 0) :
    a k = 0 := by
  classical
  by_contra hne
  obtain ⟨N, _, _, hzero, _⟩ := (show HasVectorLaurentSeriesAt f z a from ha)
  obtain ⟨m, hm, hmin⟩ := Int.exists_least_of_bdd (P := fun j ↦ a j ≠ 0)
    ⟨N, fun j hj ↦ le_of_not_gt fun h ↦ hj (hzero j h)⟩ ⟨k, hne⟩
  exact hz ⟨m, (hmin k hne).trans_lt hk, ⟨a, ha, hm, fun j hj ↦ by
    by_contra hj'
    exact hj.not_ge (hmin j hj')⟩⟩

omit [ContinuousSMul ℂ E] [T2Space E] [PolynormableSpace ℂ E] [QuasiCompleteSpace ℂ E] in
/-- At a removable point, each scalar evaluation extends across the center with
value equal to the scalar evaluation of the Laurent coefficient at zero. -/
private theorem HasVectorLaurentSeriesAt.exists_analyticAt_of_not_pole {a : ℤ → E}
    (ha : HasVectorLaurentSeriesAt f z a) (hz : ¬ IsVectorPoleAt f z)
    {h : ℂ → E} {s : ℝ} (hs : 0 < s) (hh : VectorHolomorphicOn h (Metric.ball z s))
    {n : ℕ} (heq : EqOn h (fun w ↦ (w - z) ^ n • f w) (Metric.ball z s \ {z}))
    (φ : StrongDual ℂ E) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q z ∧ q z = φ (a 0) ∧ q =ᶠ[𝓝[≠] z] φ ∘ f := by
  let b := φ ∘ h
  have hb : DifferentiableOn ℂ b (Metric.ball z s) := fun w hw ↦
    (VectorHolomorphicOn.hasDerivAt_comp hh Metric.isOpen_ball φ ⟨w, hw⟩).differentiableAt.differentiableWithinAt
  have hbe : EqOn b (fun w ↦ (w - z) ^ n * φ (f w)) (Metric.ball z s \ {z}) := by
    intro w hw
    simp [b, heq hw, smul_eq_mul]
  have hbz := hb.analyticAt (Metric.ball_mem_nhds z hs)
  have hord : (n : ENat) ≤ analyticOrderAt b z := by
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hbz).mpr
    intro j hj
    have hj' : (j : ℤ) - n < 0 := by omega
    have hcoeff := ha.coeff_eq_derivative_of_cleared φ n j hs hb hbe
    rw [ha.eq_zero_of_not_pole hz hj', map_zero] at hcoeff
    exact (div_eq_zero_iff.mp hcoeff.symm).resolve_right (by exact_mod_cast Nat.factorial_ne_zero j)
  obtain ⟨q, hq, hqeq⟩ := (natCast_le_analyticOrderAt hbz).mp hord
  obtain ⟨t, ht, hball⟩ := Metric.mem_nhds_iff.mp
    (hq.eventually_analyticAt.and (hqeq.and (Metric.ball_mem_nhds z hs)))
  have hdiff : DifferentiableOn ℂ q (Metric.ball z t) :=
    fun w hw ↦ (hball hw).1.differentiableAt.differentiableWithinAt
  have hqf : EqOn q (φ ∘ f) (Metric.ball z t \ {z}) := by
    intro w hw
    apply mul_left_cancel₀ (pow_ne_zero n (sub_ne_zero.mpr (show w ≠ z from hw.2)))
    exact ((hball hw.1).2.1.symm).trans (hbe ⟨(hball hw.1).2.2, hw.2⟩)
  refine ⟨q, hq, ?_, ?_⟩
  · symm
    simpa using ha.coeff_eq_derivative_of_cleared φ 0 0 ht hdiff (by
      intro w hw
      simpa using hqf hw)
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z ht),
      self_mem_nhdsWithin] with w hw hwz
    exact hqf ⟨hw, hwz⟩

omit [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E] [PolynormableSpace ℂ E]
  [QuasiCompleteSpace ℂ E] in
/-- Every point in the domain has a pole-clearing power on a disc whose puncture
lies in the original domain of holomorphy. -/
private theorem IsVectorMeromorphicOn.exists_cleared (hf : IsVectorMeromorphicOn f Ω D)
    (hz : z ∈ Ω) :
    ∃ (n : ℕ) (r : ℝ) (h : ℂ → E),
      0 < r ∧ Metric.ball z r \ {z} ⊆ Ω \ D ∧ VectorHolomorphicOn h (Metric.ball z r) ∧
      EqOn h (fun w ↦ (w - z) ^ n • f w) (Metric.ball z r \ {z}) := by
  obtain ⟨_, _, hopen, hhol, hclear⟩ := hf
  by_cases hzD : z ∈ D
  · exact hclear z hzD
  · obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds ⟨hz, hzD⟩)
    exact ⟨0, r, f, hr, sdiff_subset.trans hball, hhol.mono hball, fun w _ ↦ by simp⟩

/-- Filling each removable exceptional point with the constant Laurent coefficient
gives a holomorphic representative on the open complement of the exceptional poles. -/
private theorem IsVectorMeromorphicOn.exists_holomorphic_representative (hΩ : IsOpen Ω)
    (hf : IsVectorMeromorphicOn f Ω D) :
    let U := Ω \ (D ∩ {w | IsVectorPoleAt f w})
    IsOpen U ∧ ∃ g : ℂ → E, EqOn g f (Ω \ D) ∧ VectorHolomorphicOn g U := by
  classical
  intro U
  obtain ⟨hDΩ, _, hopen, hhol, hclear⟩ := (show IsVectorMeromorphicOn f Ω D from hf)
  have hsub : Ω \ D ⊆ U := fun _ hw ↦ ⟨hw.1, fun hp ↦ hw.2 hp.1⟩
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr fun w hw ↦ by
    by_cases hwD : w ∈ D
    · obtain ⟨_, r, _, hr, hball, _, _⟩ := hclear w hwD
      apply mem_of_superset (Metric.ball_mem_nhds w hr)
      intro u hu
      rcases eq_or_ne u w with rfl | huw
      · exact hw
      · exact hsub (hball ⟨hu, huw⟩)
    · exact mem_of_superset (hopen.mem_nhds ⟨hw.1, hwD⟩) hsub
  let a (w : ℂ) (hw : w ∈ D) : ℤ → E := (hf.existsUnique_laurentSeries hΩ (hDΩ hw)).exists.choose
  let g (w : ℂ) := if hw : w ∈ D then a w hw 0 else f w
  have hgf : EqOn g f (Ω \ D) := fun w hw ↦ dite_eq_right hw.2
  refine ⟨hU, g, hgf, differentiableOn_of_weaklyHolomorphicOn hU g ?_⟩
  intro φ w hw
  apply DifferentiableAt.differentiableWithinAt
  by_cases hwD : w ∈ D
  · obtain ⟨n, r, h, hr, hball, hh, heq⟩ := hclear w hwD
    have ha : HasVectorLaurentSeriesAt f w (a w hwD) := Classical.choose_spec (ExistsUnique.exists
      (hf.existsUnique_laurentSeries hΩ (hDΩ hwD)))
    obtain ⟨q, hq, hqval, hqf⟩ := ha.exists_analyticAt_of_not_pole
      (fun hp ↦ hw.2 ⟨hwD, hp⟩) hr hh heq φ
    apply hq.differentiableAt.congr_of_eventuallyEq
    filter_upwards [eventually_nhdsWithin_iff.mp hqf, Metric.ball_mem_nhds w hr] with u hu hub
    rcases eq_or_ne u w with rfl | huw
    · simpa [g, hwD] using hqval.symm
    · rw [Function.comp_apply, hgf (hball ⟨hub, huw⟩)]
      exact (hu huw).symm
  · have hw' : w ∈ Ω \ D := ⟨hw.1, hwD⟩
    apply (VectorHolomorphicOn.hasDerivAt_comp hhol hopen φ ⟨w, hw'⟩).differentiableAt.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hw'] with u hu
    exact congrArg φ (hgf hu)

-- TODO(paper-gap): C.5.3.2 omits the interior-containment hypothesis of C.5.2.4.
-- On 1 < |w| < 4, take f(w) = 1/w, z = 2, the circle |w| = 3, and k = -1.

/-- Paper: Lemma C.5.3.2, p. 740. The Laurent coefficient is the normalized
Pettis contour integral against the reciprocal power of the local coordinate.
Deviation: Restores interior containment from the cited Theorem C.5.2.4.
An extension across removable exceptional points supplies the contour values. -/
theorem hasPettisIntegral_laurentCoeff (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    (hf : IsVectorMeromorphicOn f Ω D) (γ : PositiveSimpleContour)
    (htrace : γ.val.trace ⊆ Ω) (hinterior : γ.interior ⊆ Ω) (hz : z ∈ γ.interior)
    (havoid : ∀ w ∈ γ.val.trace, ¬ IsVectorPoleAt f w)
    (honly : ∀ w ∈ γ.interior, IsVectorPoleAt f w → w = z) (k : ℤ) :
    ∃ g : ℂ → E, EqOn g f (Ω \ D) ∧
      VectorHolomorphicOn g (Ω \ {w | IsVectorPoleAt f w}) ∧
      HasPettisIntegral (.complex γ.val.measure) (fun w ↦ ((w - z) ^ (k + 1))⁻¹ • g w)
        ((2 * (Real.pi : ℂ) * Complex.I) •
          vectorLaurentCoeff (hf.existsUnique_laurentSeries hΩ (hinterior hz)).exists k) := by
  classical
  clear hconn
  let U := Ω \ (D ∩ {w | IsVectorPoleAt f w})
  obtain ⟨hU, g, hgf, hg⟩ : IsOpen U ∧ ∃ g, EqOn g f (Ω \ D) ∧ VectorHolomorphicOn g U :=
    hf.exists_holomorphic_representative hΩ
  refine ⟨g, hgf, hg.mono (fun w hw ↦ ⟨hw.1, fun hp ↦ hw.2 hp.2⟩), ?_⟩
  have htraceU : γ.val.trace ⊆ U := fun w hw ↦ ⟨htrace hw, fun hp ↦ havoid w hw hp.2⟩
  obtain ⟨n, r, h, hr, hpunct, hh, hclear⟩ := hf.exists_cleared (hinterior hz)
  let V := U ∪ Metric.ball z r
  have hV : IsOpen V := hU.union Metric.isOpen_ball
  have htr : γ.val.trace ⊆ V := htraceU.trans subset_union_left
  have hint : γ.interior ⊆ V := by
    intro w hw
    rcases eq_or_ne w z with rfl | hwz
    · exact Or.inr (Metric.mem_ball_self hr)
    · exact Or.inl ⟨hinterior hw, fun hp ↦ hwz (honly w hw hp.2)⟩
  let a := (hf.existsUnique_laurentSeries hΩ (hinterior hz)).exists.choose
  have ha : HasVectorLaurentSeriesAt f z a := Classical.choose_spec
    (hf.existsUnique_laurentSeries hΩ (hinterior hz)).exists
  let m := n + k.natAbs
  let j := (k + (m : ℤ)).toNat
  have hj : (j : ℤ) - (m : ℤ) = k := by dsimp [j, m]; omega
  let μ := PettisMeasure.complex γ.val.measure
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hscalar (φ : StrongDual ℂ E) :
      Integrable (fun w ↦ ((w - z) ^ (k + 1))⁻¹ * φ (g w)) μ.variation ∧
      μ.scalarIntegral (fun w ↦ ((w - z) ^ (k + 1))⁻¹ * φ (g w)) = c * φ (a k) := by
    -- The extra power ensures the shifted exponent is a natural number for every `k`.
    let q (w : ℂ) := (w - z) ^ k.natAbs * φ (h w)
    let p (w : ℂ) := (w - z) ^ m * φ (g w)
    let Q := update p z (q z)
    have hQq : EqOn Q q (Metric.ball z r) := by
      intro w hw
      rcases eq_or_ne w z with rfl | hwz
      · exact update_self _ _ _
      · have hw' : w ∈ Metric.ball z r \ {z} := ⟨hw, hwz⟩
        rw [show Q w = p w from update_of_ne hwz _ _]
        simp [p, q, m, pow_add, hclear hw', hgf (hpunct hw'), smul_eq_mul, mul_assoc, mul_left_comm]
    have hdiff (f₀ : ℂ → E) {S : Set ℂ} (hS : IsOpen S) (hf₀ : VectorHolomorphicOn f₀ S)
        (l : ℕ) : DifferentiableOn ℂ (fun w ↦ (w - z) ^ l * φ (f₀ w)) S := by
      apply ((differentiableOn_id.sub_const z).pow l).mul
      intro w hw
      exact (VectorHolomorphicOn.hasDerivAt_comp hf₀ hS φ ⟨w, hw⟩).differentiableAt.differentiableWithinAt
    have hQball : DifferentiableOn ℂ Q (Metric.ball z r) :=
      (hdiff h Metric.isOpen_ball hh _).congr hQq
    have hQV : DifferentiableOn ℂ Q V := by
      intro w hw
      by_cases hwball : w ∈ Metric.ball z r
      · exact (hQball.differentiableAt (Metric.isOpen_ball.mem_nhds hwball)).differentiableWithinAt
      · have hwU : w ∈ U := hw.resolve_right hwball
        have hwz : w ≠ z := fun he ↦ hwball (he ▸ Metric.mem_ball_self hr)
        apply DifferentiableAt.differentiableWithinAt
        apply ((hdiff g hU hg m).differentiableAt (hU.mem_nhds hwU)).congr_of_eventuallyEq
        filter_upwards [isOpen_ne.mem_nhds hwz] with u hu
        exact update_of_ne hu _ _
    have hcoeff := ha.coeff_eq_derivative_of_cleared φ m j hr hQball (by
      intro w hw
      simp only [Q, update_of_ne (show w ≠ z from hw.2), p, hgf (hpunct hw)])
    rw [hj] at hcoeff
    have hker : (fun w ↦ ((w - z) ^ (j + 1))⁻¹ * Q w) =ᵐ[γ.val.measure.variation]
        fun w ↦ ((w - z) ^ (k + 1))⁻¹ * φ (g w) := by
      filter_upwards [γ.val.ae_mem_trace] with w hw
      have hwz := ne_of_mem_of_not_mem hw hz.1
      rw [show Q w = p w from update_of_ne hwz _ _]
      dsimp only [p]
      rw [← mul_assoc, laurentKernel_mul_pow (sub_ne_zero.mpr hwz), hj, ← zpow_neg]
      congr 2
      omega
    obtain ⟨hi, heq⟩ := γ.scalarIntegral_cauchy_derivative hV htr hint hQV hz j
    refine ⟨hi.congr hker, ?_⟩
    have hcongr : μ.scalarIntegral (fun w ↦ ((w - z) ^ (j + 1))⁻¹ * Q w) =
        μ.scalarIntegral (fun w ↦ ((w - z) ^ (k + 1))⁻¹ * φ (g w)) :=
      VectorMeasure.integral_congr_ae hker
    rw [← hcongr, heq, hcoeff]
    simp only [c, div_eq_mul_inv]
    ring
  refine ⟨fun φ ↦ ?_, LinearMap.ext fun φ ↦ ?_⟩
  · simpa only [map_smul, smul_eq_mul, Function.comp_apply] using (hscalar φ).1
  · change φ (c • a k) = μ.scalarIntegral (fun w ↦ φ (((w - z) ^ (k + 1))⁻¹ • g w))
    simpa only [map_smul, smul_eq_mul] using (hscalar φ).2.symm

/-- Paper: (C.5.3.5), p. 740. The residue is the coefficient of exponent minus one. -/
def vectorResidue (h : ∃ a : ℤ → E, HasVectorLaurentSeriesAt f z a) : E :=
  vectorLaurentCoeff h (-1)

/-- Paper: (C.5.3.5), p. 740. The residue of the reciprocal at zero is one.
Deviation: This is a sanity check for the residue operation. -/
theorem vectorResidue_inv
    (h : ∃ a : ℤ → ℂ, HasVectorLaurentSeriesAt (fun w : ℂ ↦ w⁻¹) 0 a) :
    vectorResidue h = 1 := by
  have : @QuasiCompleteSpace ℂ ℂ _ (IsTopologicalAddGroup.rightUniformSpace ℂ) _ _ := by
    convert (inferInstance : @QuasiCompleteSpace ℂ ℂ _ PseudoMetricSpace.toUniformSpace _ _)
    exact IsUniformAddGroup.rightUniformSpace_eq
  exact (vectorLaurentCoeff_eq vectorMeromorphic_inv.2.1 h (-1)).trans (by simp)

/-- Paper: Lemma C.5.3.3(1), p. 740. The residue preserves complex linear
combinations.
Deviation: The linear combination uses the common domain of both representatives. -/
theorem vectorResidue_linear (hΩ : IsOpen Ω) (hconn : IsConnected Ω) (hz : z ∈ Ω)
    {g : ℂ → E} {D' : Set ℂ} (hf : IsVectorMeromorphicOn f Ω D)
    (hg : IsVectorMeromorphicOn g Ω D') (a b : ℂ) :
    ∃ h : IsVectorMeromorphicOn (a • f + b • g) Ω (D ∪ D'),
      vectorResidue (h.existsUnique_laurentSeries hΩ hz).exists =
        a • vectorResidue (hf.existsUnique_laurentSeries hΩ hz).exists +
          b • vectorResidue (hg.existsUnique_laurentSeries hΩ hz).exists := by sorry

-- TODO(paper-gap): The unrestricted wording of C.5.3.3(2) allows an annular hole
-- inside the contour and never explicitly requires z to be inside it.

/-- Paper: Lemma C.5.3.3(2), p. 740. The normalized contour integral around an
enclosed point gives its residue when the only possible interior pole is that point.
Deviation: The point is explicitly enclosed, and the contour and interior
satisfy the conditions of the Laurent coefficient formula above. -/
theorem hasPettisIntegral_vectorResidue (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    (hf : IsVectorMeromorphicOn f Ω D) (γ : PositiveSimpleContour)
    (htrace : γ.val.trace ⊆ Ω) (hinterior : γ.interior ⊆ Ω) (hz : z ∈ γ.interior)
    (havoid : ∀ w ∈ γ.val.trace, ¬ IsVectorPoleAt f w)
    (honly : ∀ w ∈ γ.interior, IsVectorPoleAt f w → w = z) :
    ∃ g : ℂ → E, EqOn g f (Ω \ D) ∧
      VectorHolomorphicOn g (Ω \ {w | IsVectorPoleAt f w}) ∧
      HasPettisIntegral (.complex γ.val.measure) g
        ((2 * (Real.pi : ℂ) * Complex.I) •
          vectorResidue (hf.existsUnique_laurentSeries hΩ (hinterior hz)).exists) := by sorry

-- TODO(paper-gap): C.5.3.3(3) multiplies by (w - z)^(k - 1) at a pole of
-- order k. For f(w) = 1/w at z = 0 the printed limit does not exist.

/-- Paper: Lemma C.5.3.3(4), p. 740. Continuous complex-linear maps preserve
meromorphy and commute with taking residues.
Deviation: The source of the identity is E₁-valued, and both targets satisfy the
local convexity hypotheses of the meromorphic function space. -/
theorem vectorResidue_comp_continuousLinearMap
    {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℂ F] [T2Space F] [PolynormableSpace ℂ F]
    [QuasiCompleteSpace ℂ F] (hΩ : IsOpen Ω) (hconn : IsConnected Ω) (hz : z ∈ Ω)
    (hf : IsVectorMeromorphicOn f Ω D) (T : E →L[ℂ] F) :
    ∃ h : IsVectorMeromorphicOn (T ∘ f) Ω D,
      vectorResidue (h.existsUnique_laurentSeries hΩ hz).exists =
        T (vectorResidue (hf.existsUnique_laurentSeries hΩ hz).exists) := by
  have hcomp : ∀ {U : Set ℂ} {g : ℂ → E}, IsOpen U → VectorHolomorphicOn g U →
      VectorHolomorphicOn (T ∘ g) U := by
    intro U g hU hg x hx
    have h := hg.hasFDerivAt (hU.mem_nhds hx)
    have hj : HasFDerivAt (T ∘ g) (T.comp (fderiv ℂ g x)) x := by
      apply HasFDerivAt.of_isLittleOTVS
      simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
        using T.isBigOTVS_comp.trans_isLittleOTVS h.isLittleOTVS
    exact ⟨_, hj.hasFDerivWithinAt⟩
  obtain ⟨hDΩ, hDd, hopen, hhol, hclear⟩ := id hf
  have hmer : IsVectorMeromorphicOn (T ∘ f) Ω D := by
    refine ⟨hDΩ, hDd, hopen, hcomp hopen hhol, fun w hw ↦ ?_⟩
    obtain ⟨n, r, g, hr, hsub, hg, heq⟩ := hclear w hw
    refine ⟨n, r, T ∘ g, hr, hsub, hcomp Metric.isOpen_ball hg, fun x hx ↦ ?_⟩
    simp only [Function.comp_apply]
    rw [heq hx, map_smul]
  refine ⟨hmer, ?_⟩
  obtain ⟨a, ha⟩ := (hf.existsUnique_laurentSeries hΩ hz).exists
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup
  have hu : UniformContinuous T :=
    uniformContinuous_of_continuousAt_zero T.toAddMonoidHom T.continuous.continuousAt
  have hTa : HasVectorLaurentSeriesAt (T ∘ f) z (T ∘ a) := by
    obtain ⟨N, r, hr, hN, hconv⟩ := ha
    refine ⟨N, r, hr, fun k hk ↦ by simp [hN k hk], fun K hK hKc ↦ ?_⟩
    have := hu.comp_tendstoUniformlyOn (hconv K hK hKc)
    refine this.congr (Eventually.of_forall fun n w _ ↦ ?_)
    simp [map_sum, map_smul]
  have e1 := vectorLaurentCoeff_eq hTa (hmer.existsUnique_laurentSeries hΩ hz).exists (-1)
  have e2 := vectorLaurentCoeff_eq ha (hf.existsUnique_laurentSeries hΩ hz).exists (-1)
  unfold vectorResidue
  rw [e1, e2]
  rfl

end Meromorphy

/-- Paper: Cycle convention before Theorem C.5.4.1, p. 740. A cycle is a finite
formal integer combination of positively oriented simple contours. -/
abbrev ComplexContourCycle := PositiveSimpleContour →₀ ℤ

/-- Paper: Cycle convention before Theorem C.5.4.1, p. 740. The trace of a cycle
is the union of the traces of its terms with nonzero coefficients. -/
def ComplexContourCycle.trace (Γ : ComplexContourCycle) : Set ℂ :=
  ⋃ γ ∈ Γ.support, γ.val.trace

/-- Paper: (C.5.4.1), p. 741. Integration over a cycle uses the integer-weighted
sum of the contour measures. -/
def ComplexContourCycle.measure (Γ : ComplexContourCycle) : ComplexMeasure ℂ :=
  Γ.sum (fun γ n ↦ n • γ.val.measure)

/-- Paper: Winding number in Theorem C.5.4.1, p. 741. The index of a cycle off its
trace is the integer-weighted sum of the indices of its constituent contours. -/
def ComplexContourCycle.index (Γ : ComplexContourCycle) (z : ℂ) : ℂ :=
  Γ.sum (fun γ n ↦ n • γ.val.index z)

/-- Paper: Cycle convention before Theorem C.5.4.1, p. 740. A cycle with one
contour and nonzero multiplicity has its trace and scales its measure and index.
Deviation: This is a sanity check for the cycle operations. -/
theorem complexContourCycle_single (γ : PositiveSimpleContour) {n : ℤ} (hn : n ≠ 0) (z : ℂ) :
    let Γ : ComplexContourCycle := Finsupp.single γ n
    Γ.trace = γ.val.trace ∧ Γ.measure = n • γ.val.measure ∧ Γ.index z = n • γ.val.index z := by
  refine ⟨?_, ?_, ?_⟩
  · simp [ComplexContourCycle.trace, Finsupp.support_single_ne_zero γ hn]
  · simp [ComplexContourCycle.measure, Finsupp.sum_single_index]
  · simp [ComplexContourCycle.index, Finsupp.sum_single_index]

section ResidueTheorem

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E] [PolynormableSpace ℂ E]
  [QuasiCompleteSpace ℂ E]
variable {Ω D : Set ℂ} {f : ℂ → E}

/-- Paper: Theorem C.5.4.1, p. 741. The normalized cycle integral equals the
finite sum of residues weighted by winding numbers.
Deviation: Null homology uses the planar winding-number condition outside Ω.
A representative extending across removable points supplies the contour values.
The identity is pointwise on meromorphic functions satisfying the pole avoidance condition. -/
theorem vectorResidueTheorem (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    (hf : IsVectorMeromorphicOn f Ω D) (Γ : ComplexContourCycle) (htrace : Γ.trace ⊆ Ω)
    (hnull : ∀ z ∉ Ω, Γ.index z = 0)
    (havoid : ∀ z ∈ Γ.trace, ¬ IsVectorPoleAt f z) :
    ∃ (g : ℂ → E) (S : Finset Ω),
      EqOn g f (Ω \ D) ∧ VectorHolomorphicOn g (Ω \ {z | IsVectorPoleAt f z}) ∧
      (∀ z : Ω, z ∈ S ↔ IsVectorPoleAt f z ∧ Γ.index z ≠ 0) ∧
      HasPettisIntegral (.complex Γ.measure) g
        ((2 * (Real.pi : ℂ) * Complex.I) •
          ∑ z ∈ S, Γ.index z • vectorResidue (hf.existsUnique_laurentSeries hΩ z.property).exists) :=
  by sorry

/-- Paper: Lemma C.5.4.2, p. 741. Local boundedness away from the discrete set
gives a holomorphic extension unique on the original domain. -/
theorem existsUnique_vectorHolomorphicOn_extension (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    (hDΩ : D ⊆ Ω) (hD : IsDiscrete D) (hf : VectorHolomorphicOn f (Ω \ D))
    (hb : ∀ z ∈ Ω, ∃ r : ℝ, 0 < r ∧ Metric.ball z r ⊆ Ω ∧
      IsVonNBounded ℂ (f '' (Metric.ball z r \ D))) :
    ∃ g : ℂ → E, VectorHolomorphicOn g Ω ∧ EqOn g f (Ω \ D) ∧
      ∀ g' : ℂ → E, VectorHolomorphicOn g' Ω → EqOn g' f (Ω \ D) → EqOn g' g Ω := by sorry

/-- Paper: Lemma C.5.4.3, p. 741. Two meromorphic functions that agree on a
nonempty disc agree everywhere both representatives are defined. -/
theorem IsVectorMeromorphicOn.eqOn_of_eqOn_ball (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    {g : ℂ → E} {D' : Set ℂ} (hf : IsVectorMeromorphicOn f Ω D)
    (hg : IsVectorMeromorphicOn g Ω D') {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hball : Metric.ball z r ⊆ Ω \ (D ∪ D'))
    (heq : EqOn f g (Metric.ball z r)) :
    EqOn f g (Ω \ (D ∪ D')) := by sorry

end ResidueTheorem


end RiemannMasullo
