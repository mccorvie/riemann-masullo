module

public import RiemannMasullo.AppC_LCTVS.Sec5a
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.Completion
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.HahnBanach
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
  sorry

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

/-- Paper: Theorem C.5.2.6(1,4), p. 738. Weak holomorphy is equivalent to a
power series at every center that converges uniformly to the function on each closed
disc about that center contained in the domain. -/
theorem weaklyHolomorphicOn_iff_taylor :
    WeaklyHolomorphicOn f Ω ↔ ∀ z ∈ Ω, ∃ a : ℕ → E,
      ∀ r : ℝ, 0 < r → Metric.closedBall z r ⊆ Ω →
        TendstoUniformlyOn (fun n w ↦ ∑ k ∈ Finset.range n, (w - z) ^ k • a k)
          f atTop (Metric.closedBall z r) := by sorry

/-- Paper: (C.5.2.5), p. 738. The Taylor coefficients are the vector derivatives
at the center divided by the corresponding factorials. -/
theorem tendstoUniformlyOn_taylor_derivatives (hf : ∀ k : ℕ,
    DifferentiableOn ℂ (deriv^[k] f) Ω) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hdisc : Metric.closedBall z r ⊆ Ω) :
    TendstoUniformlyOn
      (fun n w ↦ ∑ k ∈ Finset.range n,
        ((w - z) ^ k / (k.factorial : ℂ)) • (deriv^[k] f) z)
      f atTop (Metric.closedBall z r) := by sorry

/-- Paper: Theorem C.5.2.6, p. 738. In the quasi-complete case weak holomorphy
implies holomorphy in the target topology. -/
theorem WeaklyHolomorphicOn.vectorHolomorphicOn (hf : WeaklyHolomorphicOn f Ω) :
    VectorHolomorphicOn f Ω := by sorry

omit [QuasiCompleteSpace ℂ E] in
/-- Paper: (C.5.2.6), p. 739. The weak derivative evaluates each continuous
linear functional to the corresponding scalar complex derivative. -/
theorem WeaklyHolomorphicOn.existsUnique_weakDerivative (hf : WeaklyHolomorphicOn f Ω)
    {z : ℂ} (hz : z ∈ Ω) (k : ℕ) :
    ∃! v : PettisWeakCompletion E, ∀ φ : StrongDual ℂ E,
      (show Module.Dual ℂ (StrongDual ℂ E) from v) φ = iteratedDeriv k (φ ∘ f) z := by sorry

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

/-- Paper: Definition C.5.3.1, p. 739. Every point of the domain of a meromorphic
pair has a unique local Laurent expansion in the original target.
Deviation: Includes the ordinary Taylor expansion at points outside the exceptional set. -/
theorem IsVectorMeromorphicOn.existsUnique_laurentSeries (hΩ : IsOpen Ω)
    (hf : IsVectorMeromorphicOn f Ω D) (hz : z ∈ Ω) :
    ∃! a : ℤ → E, HasVectorLaurentSeriesAt f z a := by sorry

/-- Paper: Coefficient notation in Lemma C.5.3.2, p. 740. A coefficient is read
from the local Laurent expansion, with existence supplied as evidence. -/
def vectorLaurentCoeff (h : ∃ a : ℤ → E, HasVectorLaurentSeriesAt f z a) (k : ℤ) : E :=
  Classical.choose h k

/-- Paper: Coefficient notation in Lemma C.5.3.2, p. 740. Reading a coefficient
from a specified expansion reproduces the coefficient at the requested exponent.
Deviation: This is a sanity check for the coefficient operation. -/
theorem vectorLaurentCoeff_eq {a : ℤ → E} (ha : HasVectorLaurentSeriesAt f z a)
    (h : ∃ a : ℤ → E, HasVectorLaurentSeriesAt f z a) (k : ℤ) :
    vectorLaurentCoeff h k = a k := by sorry

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
          vectorLaurentCoeff (hf.existsUnique_laurentSeries hΩ (hinterior hz)).exists k) := by sorry

/-- Paper: (C.5.3.5), p. 740. The residue is the coefficient of exponent minus one. -/
def vectorResidue (h : ∃ a : ℤ → E, HasVectorLaurentSeriesAt f z a) : E :=
  vectorLaurentCoeff h (-1)

/-- Paper: (C.5.3.5), p. 740. The residue of the reciprocal at zero is one.
Deviation: This is a sanity check for the residue operation. -/
theorem vectorResidue_inv
    (h : ∃ a : ℤ → ℂ, HasVectorLaurentSeriesAt (fun w : ℂ ↦ w⁻¹) 0 a) :
    vectorResidue h = 1 := by sorry

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
        T (vectorResidue (hf.existsUnique_laurentSeries hΩ hz).exists) := by sorry

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
