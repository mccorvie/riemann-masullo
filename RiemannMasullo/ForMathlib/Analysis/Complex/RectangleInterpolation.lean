module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import RiemannMasullo.ForMathlib.Analysis.Complex.RectangleIntegral

/-! # Interpolation by a contour integral over a rectangle

For entire functions `Φ` and `θ` and a rectangle on whose boundary `θ` does not vanish, the
function

`m u = (2πi)⁻¹ ∮ Φ w · (θ w - θ u) / ((w - u) θ w) dw`

is entire, agrees with `Φ` modulo `θ` at the points inside the rectangle, and vanishes modulo
`θ` at the points outside. It is the Lagrange–Hermite interpolation of `Φ` at the zeros of `θ`
inside the rectangle, written without residues. The bounds use only the values of `Φ / θ` on the
boundary, never the distance between two zeros.

The contour integral is `rectangleIntegral` of `RectangleIntegral.lean`, with corners
`x₁ + y₁ i` and `x₂ + y₂ i`.
-/

public section

open MeasureTheory Filter Set Complex
open scoped Topology Real Interval

namespace RiemannMasullo

/-- A parametric interval integral of functions that are holomorphic in the parameter and
jointly continuous is holomorphic in the parameter. -/
theorem differentiableOn_intervalIntegral_of_continuousOn {U : Set ℂ} (hU : IsOpen U)
    {F : ℂ → ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn (Function.uncurry F) (U ×ˢ Icc a b))
    (hd : ∀ t ∈ Icc a b, DifferentiableOn ℂ (fun u ↦ F u t) U) :
    DifferentiableOn ℂ (fun u ↦ ∫ t in a..b, F u t) U := by
  intro u₀ hu₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU u₀ hu₀
  set ρ := r / 3 with hρ
  have hρpos : 0 < ρ := by positivity
  have hsub : Metric.closedBall u₀ (2 * ρ) ⊆ U := fun v hv ↦
    hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hv) (by rw [hρ]; linarith))
  have hK : IsCompact (Metric.closedBall u₀ (2 * ρ) ×ˢ Icc a b) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hc.mono (prod_mono hsub subset_rfl))
  have hMF (v : ℂ) (hv : v ∈ Metric.closedBall u₀ (2 * ρ)) (t : ℝ) (ht : t ∈ Icc a b) :
      ‖F v t‖ ≤ M := hM (v, t) ⟨hv, ht⟩
  have hin (v : ℂ) (hv : v ∈ Metric.ball u₀ ρ) : Metric.closedBall v ρ ⊆
      Metric.closedBall u₀ (2 * ρ) := by
    intro w hw
    have h1 := Metric.mem_closedBall.mp hw
    have h2 := Metric.mem_ball.mp hv
    refine Metric.mem_closedBall.mpr ?_
    calc dist w u₀ ≤ dist w v + dist v u₀ := dist_triangle _ _ _
      _ ≤ 2 * ρ := by linarith
  have hvU (v : ℂ) (hv : v ∈ Metric.ball u₀ ρ) : v ∈ U :=
    hsub (hin v hv (Metric.mem_closedBall_self hρpos.le))
  have hderiv_bound (t : ℝ) (ht : t ∈ Icc a b) (v : ℂ) (hv : v ∈ Metric.ball u₀ ρ) :
      ‖deriv (fun w ↦ F w t) v‖ ≤ M / ρ :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρpos
      ((hd t ht).diffContOnCl_ball ((hin v hv).trans hsub))
      fun w hw ↦ hMF w (hin v hv (Metric.sphere_subset_closedBall hw)) t ht
  have hhas (t : ℝ) (ht : t ∈ Icc a b) (v : ℂ) (hv : v ∈ Metric.ball u₀ ρ) :
      HasDerivAt (fun w ↦ F w t) (deriv (fun w ↦ F w t) v) v :=
    ((hd t ht).differentiableAt (hU.mem_nhds (hvU v hv))).hasDerivAt
  have hcont_t (v : ℂ) (hv : v ∈ U) : ContinuousOn (fun t ↦ F v t) (Icc a b) :=
    hc.comp (continuous_const.prodMk continuous_id).continuousOn fun t ht ↦ ⟨hv, ht⟩
  have hIoc : Ι a b ⊆ Icc a b := by
    rw [uIoc_of_le hab]
    exact Ioc_subset_Icc_self
  have hmeas (v : ℂ) (hv : v ∈ U) :
      AEStronglyMeasurable (fun t ↦ F v t) (volume.restrict (Ι a b)) :=
    ((hcont_t v hv).aestronglyMeasurable measurableSet_Icc).mono_measure
      (Measure.restrict_mono hIoc le_rfl)
  -- The derivative in the parameter is measurable in `t`, as a limit of difference quotients.
  let ε (n : ℕ) : ℂ := ((ρ / (n + 2) : ℝ) : ℂ)
  have hεne (n : ℕ) : ε n ≠ 0 := by
    have : (0 : ℝ) < ρ / (n + 2) := by positivity
    exact Complex.ofReal_ne_zero.mpr this.ne'
  have hεball (n : ℕ) : u₀ + ε n ∈ Metric.ball u₀ ρ := by
    have h1 : (0 : ℝ) < ρ / (n + 2) := by positivity
    have h2 : ρ / (n + 2) < ρ := div_lt_self hρpos (by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, ε, Complex.norm_real,
      Real.norm_of_nonneg h1.le]
    exact h2
  have hεtend : Tendsto ε atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ (.of_forall hεne)
    have h1 : Tendsto (fun n : ℕ ↦ ρ / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
    rw [Complex.ofReal_zero] at h2
    exact h2
  have hF'meas : AEStronglyMeasurable (fun t ↦ deriv (fun w ↦ F w t) u₀)
      (volume.restrict (Ι a b)) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (n : ℕ) (t : ℝ) ↦ (ε n)⁻¹ • (F (u₀ + ε n) t - F u₀ t)) (fun n ↦ ?_) ?_
    · have h := ((hmeas _ (hvU _ (hεball n))).sub (hmeas _ hu₀)).const_smul ((ε n)⁻¹)
      exact h
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      have h := (hhas t (hIoc ht) u₀ (Metric.mem_ball_self hρpos)).tendsto_slope_zero
      exact h.comp hεtend
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := a) (b := b) (F := F) (F' := fun v t ↦ deriv (fun w ↦ F w t) v)
    (x₀ := u₀) (s := Metric.ball u₀ ρ) (bound := fun _ ↦ M / ρ)
    (Metric.ball_mem_nhds u₀ hρpos)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds u₀ hρpos) fun v hv ↦ hmeas v (hvU v hv))
    ((hcont_t u₀ hu₀).intervalIntegrable_of_Icc hab) hF'meas
    (.of_forall fun t ht v hv ↦ hderiv_bound t (hIoc ht) v hv) intervalIntegrable_const
    (.of_forall fun t ht v hv ↦ hhas t (hIoc ht) v hv)
  exact key.2.differentiableAt.differentiableWithinAt

/-- The divided difference of an entire function is the mean of its derivative over the
segment. -/
theorem dslope_eq_intervalIntegral_deriv {θ : ℂ → ℂ} (hθ : Differentiable ℂ θ) (w u : ℂ) :
    dslope θ w u = ∫ s in (0 : ℝ)..1, deriv θ (w + s * (u - w)) := by
  have hcd : Continuous (deriv θ) := (hθ.contDiff (n := 1)).continuous_deriv le_rfl
  by_cases h : u = w
  · subst h
    simp [dslope_same]
  · have hsub : u - w ≠ 0 := sub_ne_zero.mpr h
    have hderiv (s : ℝ) : HasDerivAt (fun s : ℝ ↦ θ (w + s * (u - w)))
        (deriv θ (w + s * (u - w)) * (u - w)) s := by
      have h1 : HasDerivAt (fun s : ℝ ↦ w + (s : ℂ) * (u - w)) (u - w) s := by
        simpa using ((hasDerivAt_id s).ofReal_comp.mul_const (u - w)).const_add w
      have h2 := (hθ (w + s * (u - w))).hasDerivAt.scomp s h1
      simpa [mul_comm, Function.comp_def] using h2
    have hint : IntervalIntegrable (fun s : ℝ ↦ deriv θ (w + s * (u - w)) * (u - w)) volume 0 1 :=
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hderiv s) hint
    rw [intervalIntegral.integral_mul_const] at hftc
    rw [dslope_of_ne _ h, slope_def_field]
    have hval : (∫ s in (0 : ℝ)..1, deriv θ (w + s * (u - w))) * (u - w) = θ u - θ w := by
      rw [hftc]
      simp
    rw [← hval, mul_div_assoc, div_self hsub, mul_one]

/-- The divided difference of an entire function is jointly continuous. -/
theorem continuous_dslope_uncurry {θ : ℂ → ℂ} (hθ : Differentiable ℂ θ) :
    Continuous (fun p : ℂ × ℂ ↦ dslope θ p.1 p.2) := by
  have hcd : Continuous (deriv θ) := (hθ.contDiff (n := 1)).continuous_deriv le_rfl
  have h : (fun p : ℂ × ℂ ↦ dslope θ p.1 p.2) = fun p ↦
      ∫ s in (0 : ℝ)..1, deriv θ (p.1 + s * (p.2 - p.1)) :=
    funext fun p ↦ dslope_eq_intervalIntegral_deriv hθ p.1 p.2
  rw [h]
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (p : ℂ × ℂ) (s : ℝ) ↦ deriv θ (p.1 + s * (p.2 - p.1)))
    (hcd.comp (by fun_prop)) 0 1

/-- The divided difference of an entire function is entire in its second argument. -/
theorem differentiable_dslope_of_differentiable {θ : ℂ → ℂ} (hθ : Differentiable ℂ θ) (w : ℂ) :
    Differentiable ℂ (dslope θ w) :=
  differentiableOn_univ.mp ((differentiableOn_dslope (c := w) univ_mem).mpr hθ.differentiableOn)

/-- The norm of a divided difference is at most a bound for the derivative on a convex set
containing both points. -/
theorem norm_dslope_le_of_norm_deriv_le {θ : ℂ → ℂ} (hθ : Differentiable ℂ θ) {s : Set ℂ}
    (hs : Convex ℝ s) {C : ℝ} (hC : ∀ v ∈ s, ‖deriv θ v‖ ≤ C) {w u : ℂ} (hw : w ∈ s)
    (hu : u ∈ s) : ‖dslope θ w u‖ ≤ C := by
  by_cases h : u = w
  · subst h
    rw [dslope_same]
    exact hC u hu
  · rw [dslope_of_ne _ h, slope_def_field, norm_div]
    have hpos : 0 < ‖u - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
    rw [div_le_iff₀ hpos]
    exact hs.norm_image_sub_le_of_norm_deriv_le (fun v _ ↦ (hθ v)) hC hw hu

/-- The boundary of the rectangle `[x₁, x₂] × [y₁, y₂]`. -/
def rectBoundary (x₁ x₂ y₁ y₂ : ℝ) : Set ℂ :=
  {w | (w.re ∈ Icc x₁ x₂ ∧ (w.im = y₁ ∨ w.im = y₂)) ∨
    (w.im ∈ Icc y₁ y₂ ∧ (w.re = x₁ ∨ w.re = x₂))}

/-- The boundary of a rectangle is closed. -/
theorem isClosed_rectBoundary (x₁ x₂ y₁ y₂ : ℝ) : IsClosed (rectBoundary x₁ x₂ y₁ y₂) := by
  have h1 : IsClosed {w : ℂ | w.re ∈ Icc x₁ x₂ ∧ (w.im = y₁ ∨ w.im = y₂)} :=
    (isClosed_Icc.preimage Complex.continuous_re).inter
      ((isClosed_eq Complex.continuous_im continuous_const).union
        (isClosed_eq Complex.continuous_im continuous_const))
  have h2 : IsClosed {w : ℂ | w.im ∈ Icc y₁ y₂ ∧ (w.re = x₁ ∨ w.re = x₂)} :=
    (isClosed_Icc.preimage Complex.continuous_im).inter
      ((isClosed_eq Complex.continuous_re continuous_const).union
        (isClosed_eq Complex.continuous_re continuous_const))
  exact h1.union h2

/-- A point is on the boundary of the rectangle when it is on a horizontal side or on a vertical
side. -/
theorem mem_rectBoundary_iff {x₁ x₂ y₁ y₂ : ℝ} {w : ℂ} :
    w ∈ rectBoundary x₁ x₂ y₁ y₂ ↔ (w.re ∈ Icc x₁ x₂ ∧ (w.im = y₁ ∨ w.im = y₂)) ∨
      (w.im ∈ Icc y₁ y₂ ∧ (w.re = x₁ ∨ w.re = x₂)) :=
  Iff.rfl

/-- A point of a horizontal side is on the boundary of the rectangle. -/
theorem mem_rectBoundary_horizontal {x₁ x₂ y₁ y₂ : ℝ} {x y : ℝ} (hx : x ∈ Icc x₁ x₂)
    (hy : y = y₁ ∨ y = y₂) : (x : ℂ) + y * I ∈ rectBoundary x₁ x₂ y₁ y₂ :=
  Or.inl ⟨by simpa using hx, by simpa using hy⟩

/-- A point of a vertical side is on the boundary of the rectangle. -/
theorem mem_rectBoundary_vertical {x₁ x₂ y₁ y₂ : ℝ} {x y : ℝ} (hy : y ∈ Icc y₁ y₂)
    (hx : x = x₁ ∨ x = x₂) : (x : ℂ) + y * I ∈ rectBoundary x₁ x₂ y₁ y₂ :=
  Or.inr ⟨by simpa using hy, by simpa using hx⟩

/-- The closed rectangle without the open rectangle, which is how the lemmas on
`rectangleIntegral` speak of the boundary, is contained in `rectBoundary`. -/
theorem reProdIm_diff_subset_rectBoundary (x₁ x₂ y₁ y₂ : ℝ) :
    (Icc x₁ x₂ ×ℂ Icc y₁ y₂) \ (Ioo x₁ x₂ ×ℂ Ioo y₁ y₂) ⊆ rectBoundary x₁ x₂ y₁ y₂ := by
  rintro w ⟨⟨hre, him⟩, hnot⟩
  by_cases h : w.re ∈ Ioo x₁ x₂
  · refine Or.inl ⟨hre, ?_⟩
    by_contra hne
    push Not at hne
    exact hnot ⟨h, lt_of_le_of_ne him.1 (Ne.symm hne.1), lt_of_le_of_ne him.2 hne.2⟩
  · refine Or.inr ⟨him, ?_⟩
    by_contra hne
    push Not at hne
    exact h ⟨lt_of_le_of_ne hre.1 (Ne.symm hne.1), lt_of_le_of_ne hre.2 hne.2⟩

/-- The rectangle integral with corners `x₁ + y₁ i` and `x₂ + y₂ i`, as four edge integrals. -/
theorem rectangleIntegral_mk (f : ℂ → ℂ) (x₁ x₂ y₁ y₂ : ℝ) :
    rectangleIntegral f ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ =
      (∫ x : ℝ in x₁..x₂, f (x + y₁ * I)) - (∫ x : ℝ in x₁..x₂, f (x + y₂ * I)) +
        I * (∫ y : ℝ in y₁..y₂, f (x₂ + y * I)) - I * (∫ y : ℝ in y₁..y₂, f (x₁ + y * I)) :=
  rectangleIntegral_eq f ⟨x₁, y₁⟩ ⟨x₂, y₂⟩

/-- Functions that agree on the boundary have the same rectangle integral. -/
theorem rectangleIntegral_congr_of_eqOn_rectBoundary {f g : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ}
    (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) (h : EqOn f g (rectBoundary x₁ x₂ y₁ y₂)) :
    rectangleIntegral f ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ = rectangleIntegral g ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ :=
  rectangleIntegral_congr_off_countable (z := ⟨x₁, y₁⟩) (w := ⟨x₂, y₂⟩) (E := ∅) hx hy
    countable_empty fun _ hs ↦ h (reProdIm_diff_subset_rectBoundary x₁ x₂ y₁ y₂ hs.1)

/-- A bound on the boundary bounds the rectangle integral by the perimeter times the bound. -/
theorem norm_rectangleIntegral_le {f : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂)
    {C : ℝ} (hC : ∀ w ∈ rectBoundary x₁ x₂ y₁ y₂, ‖f w‖ ≤ C) :
    ‖rectangleIntegral f ⟨x₁, y₁⟩ ⟨x₂, y₂⟩‖ ≤ 2 * ((x₂ - x₁) + (y₂ - y₁)) * C := by
  rw [rectangleIntegral_mk]
  have hX (x : ℝ) (hx' : x ∈ Ι x₁ x₂) : x ∈ Icc x₁ x₂ := by
    rw [uIoc_of_le hx] at hx'
    exact Ioc_subset_Icc_self hx'
  have hY (y : ℝ) (hy' : y ∈ Ι y₁ y₂) : y ∈ Icc y₁ y₂ := by
    rw [uIoc_of_le hy] at hy'
    exact Ioc_subset_Icc_self hy'
  have h1 : ‖∫ x : ℝ in x₁..x₂, f (x + y₁ * I)‖ ≤ C * |x₂ - x₁| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx' ↦
      hC _ (mem_rectBoundary_horizontal (hX x hx') (Or.inl rfl))
  have h2 : ‖∫ x : ℝ in x₁..x₂, f (x + y₂ * I)‖ ≤ C * |x₂ - x₁| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x hx' ↦
      hC _ (mem_rectBoundary_horizontal (hX x hx') (Or.inr rfl))
  have h3 : ‖∫ y : ℝ in y₁..y₂, f (x₂ + y * I)‖ ≤ C * |y₂ - y₁| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun y hy' ↦
      hC _ (mem_rectBoundary_vertical (hY y hy') (Or.inr rfl))
  have h4 : ‖∫ y : ℝ in y₁..y₂, f (x₁ + y * I)‖ ≤ C * |y₂ - y₁| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun y hy' ↦
      hC _ (mem_rectBoundary_vertical (hY y hy') (Or.inl rfl))
  rw [abs_of_nonneg (sub_nonneg.mpr hx)] at h1 h2
  rw [abs_of_nonneg (sub_nonneg.mpr hy)] at h3 h4
  have hI (z : ℂ) : ‖I * z‖ = ‖z‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  calc _ ≤ ‖∫ x : ℝ in x₁..x₂, f (x + y₁ * I)‖ + ‖∫ x : ℝ in x₁..x₂, f (x + y₂ * I)‖ +
        ‖I * ∫ y : ℝ in y₁..y₂, f (x₂ + y * I)‖ + ‖I * ∫ y : ℝ in y₁..y₂, f (x₁ + y * I)‖ :=
        (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
    _ ≤ C * (x₂ - x₁) + C * (x₂ - x₁) + C * (y₂ - y₁) + C * (y₂ - y₁) := by
        rw [hI, hI]
        exact add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = 2 * ((x₂ - x₁) + (y₂ - y₁)) * C := by ring

/-- The rectangle integral is linear on functions continuous on the boundary. -/
theorem rectangleIntegral_sub_const_mul {f g : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ x₂)
    (hy : y₁ ≤ y₂) (hf : ContinuousOn f (rectBoundary x₁ x₂ y₁ y₂))
    (hg : ContinuousOn g (rectBoundary x₁ x₂ y₁ y₂)) (c : ℂ) :
    rectangleIntegral (fun w ↦ f w - c * g w) ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ =
      rectangleIntegral f ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ - c * rectangleIntegral g ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := by
  have hsub := reProdIm_diff_subset_rectBoundary x₁ x₂ y₁ y₂
  have hfg : (fun w ↦ f w - c * g w) = fun w ↦ f w + -c * g w := funext fun w ↦ by ring
  rw [hfg, rectangleIntegral_add (f := f) (g := fun s ↦ -c * g s) (z := ⟨x₁, y₁⟩)
    (w := ⟨x₂, y₂⟩) hx hy (hf.mono hsub) ((continuousOn_const.mul hg).mono hsub),
    rectangleIntegral_const_mul]
  ring

/-- Cauchy–Goursat for the rectangle integral of an entire function. -/
theorem rectangleIntegral_eq_zero_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (z w : ℂ) : rectangleIntegral f z w = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hf.differentiableOn
  rw [rectangleIntegral_eq]
  simpa [smul_eq_mul] using h

/-- The rectangle integral of `(w - u)⁻¹` vanishes for `u` outside the closed rectangle. For
`u` inside the open rectangle it is `2πi`, by `rectangleIntegral_sub_inv`. -/
theorem rectangleIntegral_sub_inv_of_notMem {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂)
    {u : ℂ} (hu : ¬(u.re ∈ Icc x₁ x₂ ∧ u.im ∈ Icc y₁ y₂)) :
    rectangleIntegral (fun w ↦ (w - u)⁻¹) ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ = 0 := by
  have hd : DifferentiableOn ℂ (fun w : ℂ ↦ (w - u)⁻¹) ([[x₁, x₂]] ×ℂ [[y₁, y₂]]) := by
    intro w hw
    have hne : w - u ≠ 0 := by
      intro h0
      apply hu
      have hwu : w = u := sub_eq_zero.mp h0
      rw [uIcc_of_le hx, uIcc_of_le hy] at hw
      rw [← hwu]
      exact hw
    exact ((differentiableAt_id.sub_const u).inv hne).differentiableWithinAt
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (fun w : ℂ ↦ (w - u)⁻¹)
    (⟨x₁, y₁⟩ : ℂ) (⟨x₂, y₂⟩ : ℂ) hd
  rw [rectangleIntegral_mk]
  simpa [smul_eq_mul] using h

/-- The Cauchy integral of an entire function over the boundary of a rectangle is its value
times the integral of the Cauchy kernel. -/
theorem rectangleIntegral_div_sub {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {x₁ x₂ y₁ y₂ : ℝ}
    (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) {u : ℂ} (hu : u ∉ rectBoundary x₁ x₂ y₁ y₂) :
    rectangleIntegral (fun w ↦ Φ w / (w - u)) ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ =
      Φ u * rectangleIntegral (fun w ↦ (w - u)⁻¹) ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := by
  have hne (w : ℂ) (hw : w ∈ rectBoundary x₁ x₂ y₁ y₂) : w - u ≠ 0 := fun h0 ↦
    hu (sub_eq_zero.mp h0 ▸ hw)
  have hcongr : EqOn (fun w ↦ Φ w / (w - u)) (fun w ↦ dslope Φ u w - (-Φ u) * (w - u)⁻¹)
      (rectBoundary x₁ x₂ y₁ y₂) := by
    intro w hw
    have h1 : w ≠ u := fun h ↦ hne w hw (sub_eq_zero.mpr h)
    have h2 := hne w hw
    change Φ w / (w - u) = dslope Φ u w - (-Φ u) * (w - u)⁻¹
    rw [dslope_of_ne _ h1, slope_def_field]
    field_simp
    ring
  have hdd := differentiable_dslope_of_differentiable hΦ u
  have hcinv : ContinuousOn (fun w : ℂ ↦ (w - u)⁻¹) (rectBoundary x₁ x₂ y₁ y₂) := fun w hw ↦
    ((continuousAt_id.sub continuousAt_const).inv₀ (hne w hw)).continuousWithinAt
  have hlin := rectangleIntegral_sub_const_mul (f := dslope Φ u)
    (g := fun w : ℂ ↦ (w - u)⁻¹) hx hy hdd.continuous.continuousOn hcinv (-Φ u)
  rw [rectangleIntegral_congr_of_eqOn_rectBoundary hx hy hcongr, hlin,
    rectangleIntegral_eq_zero_of_differentiable hdd]
  ring

/-- The interpolation multiplier of a rectangle:
`(2πi)⁻¹ ∮ Φ w · (θ w - θ u) / ((w - u) θ w) dw`. -/
noncomputable def rectInterpolant (Φ θ : ℂ → ℂ) (x₁ x₂ y₁ y₂ : ℝ) (u : ℂ) : ℂ :=
  (2 * π * I)⁻¹ * rectangleIntegral (fun w ↦ Φ w * dslope θ w u / θ w) ⟨x₁, y₁⟩ ⟨x₂, y₂⟩

/-- The Cauchy-type integral in the remainder of the interpolation multiplier:
`(2πi)⁻¹ ∮ Φ w / (θ w (w - u)) dw`. -/
noncomputable def rectCauchyRemainder (Φ θ : ℂ → ℂ) (x₁ x₂ y₁ y₂ : ℝ) (u : ℂ) : ℂ :=
  (2 * π * I)⁻¹ * rectangleIntegral (fun w ↦ Φ w / (θ w * (w - u))) ⟨x₁, y₁⟩ ⟨x₂, y₂⟩

/-- The interpolation multiplier is entire. -/
theorem differentiable_rectInterpolant {Φ θ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (hθ : Differentiable ℂ θ) {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂)
    (hne : ∀ w ∈ rectBoundary x₁ x₂ y₁ y₂, θ w ≠ 0) :
    Differentiable ℂ (rectInterpolant Φ θ x₁ x₂ y₁ y₂) := by
  have hside (γ : ℝ → ℂ) (hγ : Continuous γ) (a b : ℝ) (hab : a ≤ b)
      (hmem : ∀ t ∈ Icc a b, γ t ∈ rectBoundary x₁ x₂ y₁ y₂) :
      Differentiable ℂ (fun u ↦ ∫ t in a..b, Φ (γ t) * dslope θ (γ t) u / θ (γ t)) := by
    refine differentiableOn_univ.mp (differentiableOn_intervalIntegral_of_continuousOn isOpen_univ
      (F := fun u t ↦ Φ (γ t) * dslope θ (γ t) u / θ (γ t)) hab ?_ fun t _ ↦ ?_)
    · refine ContinuousOn.div (Continuous.continuousOn ?_) (Continuous.continuousOn ?_)
        fun p hp ↦ hne _ (hmem p.2 hp.2)
      · exact (hΦ.continuous.comp (hγ.comp continuous_snd)).mul
          ((continuous_dslope_uncurry hθ).comp ((hγ.comp continuous_snd).prodMk continuous_fst))
      · exact hθ.continuous.comp (hγ.comp continuous_snd)
    · exact (((differentiable_dslope_of_differentiable hθ (γ t)).const_mul _).div_const
        _).differentiableOn
  have h1 := hside (fun x : ℝ ↦ (x : ℂ) + y₁ * I) (by fun_prop) x₁ x₂ hx fun t ht ↦
    mem_rectBoundary_horizontal ht (Or.inl rfl)
  have h2 := hside (fun x : ℝ ↦ (x : ℂ) + y₂ * I) (by fun_prop) x₁ x₂ hx fun t ht ↦
    mem_rectBoundary_horizontal ht (Or.inr rfl)
  have h3 := hside (fun y : ℝ ↦ (x₂ : ℂ) + y * I) (by fun_prop) y₁ y₂ hy fun t ht ↦
    mem_rectBoundary_vertical ht (Or.inr rfl)
  have h4 := hside (fun y : ℝ ↦ (x₁ : ℂ) + y * I) (by fun_prop) y₁ y₂ hy fun t ht ↦
    mem_rectBoundary_vertical ht (Or.inl rfl)
  change Differentiable ℂ (fun u ↦ (2 * π * I)⁻¹ *
    rectangleIntegral (fun w ↦ Φ w * dslope θ w u / θ w) ⟨x₁, y₁⟩ ⟨x₂, y₂⟩)
  simp only [rectangleIntegral_mk]
  exact (((h1.sub h2).add (h3.const_mul I)).sub (h4.const_mul I)).const_mul _

/-- The Cauchy-type remainder is holomorphic off the boundary. -/
theorem differentiableOn_rectCauchyRemainder {Φ θ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (hθ : Differentiable ℂ θ) {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂)
    (hne : ∀ w ∈ rectBoundary x₁ x₂ y₁ y₂, θ w ≠ 0) :
    DifferentiableOn ℂ (rectCauchyRemainder Φ θ x₁ x₂ y₁ y₂) (rectBoundary x₁ x₂ y₁ y₂)ᶜ := by
  have hopen : IsOpen (rectBoundary x₁ x₂ y₁ y₂)ᶜ := (isClosed_rectBoundary _ _ _ _).isOpen_compl
  have hside (γ : ℝ → ℂ) (hγ : Continuous γ) (a b : ℝ) (hab : a ≤ b)
      (hmem : ∀ t ∈ Icc a b, γ t ∈ rectBoundary x₁ x₂ y₁ y₂) :
      DifferentiableOn ℂ (fun u ↦ ∫ t in a..b, Φ (γ t) / (θ (γ t) * (γ t - u)))
        (rectBoundary x₁ x₂ y₁ y₂)ᶜ := by
    refine differentiableOn_intervalIntegral_of_continuousOn hopen
      (F := fun u t ↦ Φ (γ t) / (θ (γ t) * (γ t - u))) hab ?_ fun t ht ↦ ?_
    · refine ContinuousOn.div (Continuous.continuousOn ?_) (Continuous.continuousOn ?_)
        fun p hp ↦ mul_ne_zero (hne _ (hmem p.2 hp.2)) (sub_ne_zero.mpr fun h ↦ hp.1 ?_)
      · exact hΦ.continuous.comp (hγ.comp continuous_snd)
      · exact (hθ.continuous.comp (hγ.comp continuous_snd)).mul
          ((hγ.comp continuous_snd).sub continuous_fst)
      · exact h ▸ hmem p.2 hp.2
    · refine DifferentiableOn.div (differentiableOn_const _)
        ((differentiableOn_const _).mul ((differentiableOn_const _).sub differentiableOn_id))
        fun u hu ↦ mul_ne_zero (hne _ (hmem t ht)) (sub_ne_zero.mpr fun h ↦ hu ?_)
      exact h ▸ hmem t ht
  have h1 := hside (fun x : ℝ ↦ (x : ℂ) + y₁ * I) (by fun_prop) x₁ x₂ hx fun t ht ↦
    mem_rectBoundary_horizontal ht (Or.inl rfl)
  have h2 := hside (fun x : ℝ ↦ (x : ℂ) + y₂ * I) (by fun_prop) x₁ x₂ hx fun t ht ↦
    mem_rectBoundary_horizontal ht (Or.inr rfl)
  have h3 := hside (fun y : ℝ ↦ (x₂ : ℂ) + y * I) (by fun_prop) y₁ y₂ hy fun t ht ↦
    mem_rectBoundary_vertical ht (Or.inr rfl)
  have h4 := hside (fun y : ℝ ↦ (x₁ : ℂ) + y * I) (by fun_prop) y₁ y₂ hy fun t ht ↦
    mem_rectBoundary_vertical ht (Or.inl rfl)
  change DifferentiableOn ℂ (fun u ↦ (2 * π * I)⁻¹ *
    rectangleIntegral (fun w ↦ Φ w / (θ w * (w - u))) ⟨x₁, y₁⟩ ⟨x₂, y₂⟩) _
  simp only [rectangleIntegral_mk]
  exact (((h1.sub h2).add (h3.const_mul I)).sub (h4.const_mul I)).const_mul _

/-- Off the boundary, the interpolation multiplier is the Cauchy integral of `Φ` minus `θ`
times the Cauchy-type remainder. -/
theorem rectInterpolant_eq_of_notMem {Φ θ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (hθ : Differentiable ℂ θ) {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂)
    (hne : ∀ w ∈ rectBoundary x₁ x₂ y₁ y₂, θ w ≠ 0) {u : ℂ}
    (hu : u ∉ rectBoundary x₁ x₂ y₁ y₂) :
    rectInterpolant Φ θ x₁ x₂ y₁ y₂ u =
      (2 * π * I)⁻¹ * (Φ u * rectangleIntegral (fun w ↦ (w - u)⁻¹) ⟨x₁, y₁⟩ ⟨x₂, y₂⟩) -
        θ u * rectCauchyRemainder Φ θ x₁ x₂ y₁ y₂ u := by
  have hwu (w : ℂ) (hw : w ∈ rectBoundary x₁ x₂ y₁ y₂) : w - u ≠ 0 := fun h0 ↦
    hu (sub_eq_zero.mp h0 ▸ hw)
  have hcongr : EqOn (fun w ↦ Φ w * dslope θ w u / θ w)
      (fun w ↦ Φ w / (w - u) - θ u * (Φ w / (θ w * (w - u)))) (rectBoundary x₁ x₂ y₁ y₂) := by
    intro w hw
    have h1 : u ≠ w := fun h ↦ hwu w hw (sub_eq_zero.mpr h.symm)
    have h2 := hwu w hw
    have h3 := hne w hw
    have h4 : u - w ≠ 0 := sub_ne_zero.mpr h1
    change Φ w * dslope θ w u / θ w = Φ w / (w - u) - θ u * (Φ w / (θ w * (w - u)))
    rw [dslope_of_ne _ h1, slope_def_field]
    field_simp
    ring
  have hc1 : ContinuousOn (fun w ↦ Φ w / (w - u)) (rectBoundary x₁ x₂ y₁ y₂) := fun w hw ↦
    (hΦ.continuous.continuousAt.div (continuousAt_id.sub continuousAt_const)
      (hwu w hw)).continuousWithinAt
  have hc2 : ContinuousOn (fun w ↦ Φ w / (θ w * (w - u))) (rectBoundary x₁ x₂ y₁ y₂) :=
    fun w hw ↦ (hΦ.continuous.continuousAt.div (hθ.continuous.continuousAt.mul
      (continuousAt_id.sub continuousAt_const)) (mul_ne_zero (hne w hw)
      (hwu w hw))).continuousWithinAt
  unfold rectInterpolant rectCauchyRemainder
  rw [rectangleIntegral_congr_of_eqOn_rectBoundary hx hy hcongr,
    rectangleIntegral_sub_const_mul hx hy hc1 hc2, rectangleIntegral_div_sub hΦ hx hy hu]
  ring

/-- Where the interpolation multiplier is `c Φ - θ G` near a point, its derivatives below the
order of vanishing of `θ` at that point are `c` times those of `Φ`. -/
private theorem iteratedDeriv_rectInterpolant_aux {Φ θ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (hθ : Differentiable ℂ θ) {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂)
    (hne : ∀ w ∈ rectBoundary x₁ x₂ y₁ y₂, θ w ≠ 0) {u₀ c : ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hu₀ : u₀ ∈ V) (hVb : V ⊆ (rectBoundary x₁ x₂ y₁ y₂)ᶜ)
    (hform : ∀ u ∈ V, rectInterpolant Φ θ x₁ x₂ y₁ y₂ u =
      c * Φ u - θ u * rectCauchyRemainder Φ θ x₁ x₂ y₁ y₂ u)
    {N : ℕ} (hN : (N : ℕ∞) ≤ analyticOrderAt θ u₀) {q : ℕ} (hq : q < N) :
    iteratedDeriv q (rectInterpolant Φ θ x₁ x₂ y₁ y₂) u₀ = c * iteratedDeriv q Φ u₀ := by
  have hG : AnalyticAt ℂ (rectCauchyRemainder Φ θ x₁ x₂ y₁ y₂) u₀ :=
    (differentiableOn_rectCauchyRemainder hΦ hθ hx hy hne).analyticAt
      ((isClosed_rectBoundary _ _ _ _).isOpen_compl.mem_nhds (hVb hu₀))
  have hθa : AnalyticAt ℂ θ u₀ := hθ.analyticAt u₀
  have hΦa : AnalyticAt ℂ Φ u₀ := hΦ.analyticAt u₀
  have hprod : AnalyticAt ℂ (θ * rectCauchyRemainder Φ θ x₁ x₂ y₁ y₂) u₀ := hθa.mul hG
  have hord : (N : ℕ∞) ≤ analyticOrderAt (θ * rectCauchyRemainder Φ θ x₁ x₂ y₁ y₂) u₀ := by
    rw [analyticOrderAt_mul hθa hG]
    exact hN.trans le_self_add
  have hzero := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hprod).mp hord q hq
  have heq : rectInterpolant Φ θ x₁ x₂ y₁ y₂ =ᶠ[𝓝 u₀]
      ((fun u ↦ c * Φ u) - θ * rectCauchyRemainder Φ θ x₁ x₂ y₁ y₂) :=
    Filter.eventually_of_mem (hV.mem_nhds hu₀) hform
  rw [heq.iteratedDeriv_eq q, iteratedDeriv_sub ((contDiffAt_const.mul hΦa.contDiffAt))
    hprod.contDiffAt, hzero, sub_zero, iteratedDeriv_const_mul_field]

/-- At a point inside the rectangle, the derivatives of the interpolation multiplier below the
order of vanishing of `θ` are those of `Φ`. -/
theorem iteratedDeriv_rectInterpolant_of_mem {Φ θ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (hθ : Differentiable ℂ θ) {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂)
    (hne : ∀ w ∈ rectBoundary x₁ x₂ y₁ y₂, θ w ≠ 0) {u₀ : ℂ} (h₁ : x₁ < u₀.re)
    (h₂ : u₀.re < x₂) (h₃ : y₁ < u₀.im) (h₄ : u₀.im < y₂) {N : ℕ}
    (hN : (N : ℕ∞) ≤ analyticOrderAt θ u₀) {q : ℕ} (hq : q < N) :
    iteratedDeriv q (rectInterpolant Φ θ x₁ x₂ y₁ y₂) u₀ = iteratedDeriv q Φ u₀ := by
  let V : Set ℂ := {u | x₁ < u.re ∧ u.re < x₂ ∧ y₁ < u.im ∧ u.im < y₂}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hVb : V ⊆ (rectBoundary x₁ x₂ y₁ y₂)ᶜ := by
    rintro u ⟨a1, a2, a3, a4⟩ (⟨-, h | h⟩ | ⟨-, h | h⟩)
    · exact a3.ne' h
    · exact a4.ne h
    · exact a1.ne' h
    · exact a2.ne h
  have h := iteratedDeriv_rectInterpolant_aux hΦ hθ hx hy hne (c := 1) hV
    (show u₀ ∈ V from ⟨h₁, h₂, h₃, h₄⟩) hVb (fun u hu ↦ by
      rw [rectInterpolant_eq_of_notMem hΦ hθ hx hy hne (hVb hu),
        rectangleIntegral_sub_inv (z := ⟨x₁, y₁⟩) (w := ⟨x₂, y₂⟩) (ρ := u)
          ⟨⟨hu.1, hu.2.1⟩, hu.2.2.1, hu.2.2.2⟩]
      have h2π : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
      field_simp) hN hq
  simpa using h

/-- At a point outside the closed rectangle, the derivatives of the interpolation multiplier
below the order of vanishing of `θ` vanish. -/
theorem iteratedDeriv_rectInterpolant_of_notMem {Φ θ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (hθ : Differentiable ℂ θ) {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂)
    (hne : ∀ w ∈ rectBoundary x₁ x₂ y₁ y₂, θ w ≠ 0) {u₀ : ℂ}
    (hu₀ : ¬(u₀.re ∈ Icc x₁ x₂ ∧ u₀.im ∈ Icc y₁ y₂)) {N : ℕ}
    (hN : (N : ℕ∞) ≤ analyticOrderAt θ u₀) {q : ℕ} (hq : q < N) :
    iteratedDeriv q (rectInterpolant Φ θ x₁ x₂ y₁ y₂) u₀ = 0 := by
  let V : Set ℂ := {u | ¬(u.re ∈ Icc x₁ x₂ ∧ u.im ∈ Icc y₁ y₂)}
  have hV : IsOpen V :=
    ((isClosed_Icc.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im)).isOpen_compl
  have hVb : V ⊆ (rectBoundary x₁ x₂ y₁ y₂)ᶜ := by
    rintro u hu (⟨h1, h | h⟩ | ⟨h1, h | h⟩)
    · exact hu ⟨h1, h.ge, h.le.trans hy⟩
    · exact hu ⟨h1, hy.trans h.ge, h.le⟩
    · exact hu ⟨⟨h.ge, h.le.trans hx⟩, h1⟩
    · exact hu ⟨⟨hx.trans h.ge, h.le⟩, h1⟩
  have h := iteratedDeriv_rectInterpolant_aux hΦ hθ hx hy hne (c := 0) hV
    (show u₀ ∈ V from hu₀) hVb (fun u hu ↦ by
      rw [rectInterpolant_eq_of_notMem hΦ hθ hx hy hne (hVb hu),
        rectangleIntegral_sub_inv_of_notMem hx hy hu]
      ring) hN hq
  simpa using h

/-- A bound for the integrand on the boundary bounds the interpolation multiplier. -/
theorem norm_rectInterpolant_le {Φ θ : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂)
    {u : ℂ} {C : ℝ} (hC : ∀ w ∈ rectBoundary x₁ x₂ y₁ y₂, ‖Φ w * dslope θ w u / θ w‖ ≤ C) :
    ‖rectInterpolant Φ θ x₁ x₂ y₁ y₂ u‖ ≤ ((x₂ - x₁) + (y₂ - y₁)) / π * C := by
  have h := norm_rectangleIntegral_le hx hy hC
  have h2π : ‖(2 * π * I : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
      mul_one, Real.norm_of_nonneg Real.pi_pos.le]
  unfold rectInterpolant
  rw [norm_mul, h2π]
  calc (2 * π)⁻¹ * ‖rectangleIntegral (fun w ↦ Φ w * dslope θ w u / θ w) ⟨x₁, y₁⟩ ⟨x₂, y₂⟩‖
      ≤ (2 * π)⁻¹ * (2 * ((x₂ - x₁) + (y₂ - y₁)) * C) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = ((x₂ - x₁) + (y₂ - y₁)) / π * C := by
        field_simp

/-- A bound for the integrand on the boundary bounds the Cauchy-type remainder. -/
theorem norm_rectCauchyRemainder_le {Φ θ : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ x₂)
    (hy : y₁ ≤ y₂) {u : ℂ} {C : ℝ}
    (hC : ∀ w ∈ rectBoundary x₁ x₂ y₁ y₂, ‖Φ w / (θ w * (w - u))‖ ≤ C) :
    ‖rectCauchyRemainder Φ θ x₁ x₂ y₁ y₂ u‖ ≤ ((x₂ - x₁) + (y₂ - y₁)) / π * C := by
  have h := norm_rectangleIntegral_le hx hy hC
  have h2π : ‖(2 * π * I : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
      mul_one, Real.norm_of_nonneg Real.pi_pos.le]
  unfold rectCauchyRemainder
  rw [norm_mul, h2π]
  calc (2 * π)⁻¹ * ‖rectangleIntegral (fun w ↦ Φ w / (θ w * (w - u))) ⟨x₁, y₁⟩ ⟨x₂, y₂⟩‖
      ≤ (2 * π)⁻¹ * (2 * ((x₂ - x₁) + (y₂ - y₁)) * C) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = ((x₂ - x₁) + (y₂ - y₁)) / π * C := by
        field_simp

/-- The norm of the Gaussian `exp ((u - iτ)²)`. -/
theorem norm_cexp_sub_mul_I_sq (u : ℂ) (τ : ℝ) :
    ‖cexp ((u - τ * I) ^ 2)‖ = Real.exp (u.re ^ 2 - (u.im - τ) ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [sq, Complex.mul_re]

/-- A power of `1 + |t|` times a Gaussian centred at `τ` is at most a constant times the same
power of `1 + |τ|`. -/
theorem one_add_abs_pow_mul_exp_neg_sq_le (n : ℕ) (t τ : ℝ) :
    (1 + |t|) ^ n * Real.exp (-(t - τ) ^ 2) ≤ Real.exp 2 * n.factorial * (1 + |τ|) ^ n := by
  set x := t - τ with hx
  have h1 : 1 + |t| ≤ (1 + |τ|) * (1 + |x|) := by
    have h : |t| ≤ |τ| + |x| := by
      have ht : t = τ + x := by rw [hx]; ring
      rw [ht]
      exact abs_add_le τ x
    nlinarith [abs_nonneg τ, abs_nonneg x, mul_nonneg (abs_nonneg τ) (abs_nonneg x)]
  have h2 : Real.exp (-x ^ 2) ≤ Real.exp (1 - 2 * |x|) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  have h3 : (1 + |x|) ^ n * Real.exp (-(1 + |x|)) ≤ n.factorial := by
    have h := Real.pow_div_factorial_le_exp (x := 1 + |x|) (by positivity) n
    have hfac : (0 : ℝ) < n.factorial := by positivity
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    have h' := (div_le_iff₀ hfac).mp h
    linarith [mul_comm (Real.exp (1 + |x|)) (n.factorial : ℝ)]
  have h4 : Real.exp (2 - |x|) ≤ Real.exp 2 :=
    Real.exp_le_exp.mpr (by linarith [abs_nonneg x])
  have h5 : Real.exp (1 - 2 * |x|) = Real.exp (-(1 + |x|)) * Real.exp (2 - |x|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hτ : (0 : ℝ) ≤ (1 + |τ|) ^ n := by positivity
  calc (1 + |t|) ^ n * Real.exp (-x ^ 2)
      ≤ ((1 + |τ|) * (1 + |x|)) ^ n * Real.exp (1 - 2 * |x|) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) h1 n) h2 (Real.exp_pos _).le (by positivity)
    _ = (1 + |τ|) ^ n * (((1 + |x|) ^ n * Real.exp (-(1 + |x|))) * Real.exp (2 - |x|)) := by
        rw [mul_pow, h5]
        ring
    _ ≤ (1 + |τ|) ^ n * ((n.factorial : ℝ) * Real.exp 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h3 h4 (Real.exp_pos _).le (by positivity)) hτ
    _ = Real.exp 2 * n.factorial * (1 + |τ|) ^ n := by ring

/-- Cauchy's estimate: polynomial growth of an entire function on a vertical strip bounds its
derivative on the strip narrower by one. -/
theorem norm_deriv_le_of_strip_growth {ϑ : ℂ → ℂ} (hϑ : Differentiable ℂ ϑ) {W : ℝ} {A : ℕ}
    (hg : ∀ u : ℂ, |u.re| ≤ W + 1 → ‖ϑ u‖ ≤ (1 + |u.im|) ^ A) {v : ℂ} (hv : |v.re| ≤ W) :
    ‖deriv ϑ v‖ ≤ (2 + |v.im|) ^ A := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := v) (R := 1)
    (C := (2 + |v.im|) ^ A) one_pos hϑ.diffContOnCl fun w hw ↦ ?_
  · simpa using h
  · have hd : ‖w - v‖ = 1 := by simpa [dist_eq_norm] using hw
    have h1 : |w.re - v.re| ≤ 1 := by
      have := Complex.abs_re_le_norm (w - v)
      rwa [Complex.sub_re, hd] at this
    have h2 : |w.im - v.im| ≤ 1 := by
      have := Complex.abs_im_le_norm (w - v)
      rwa [Complex.sub_im, hd] at this
    have hre : |w.re| ≤ W + 1 := by
      have := abs_sub_abs_le_abs_sub w.re v.re
      linarith
    have him : 1 + |w.im| ≤ 2 + |v.im| := by
      have := abs_sub_abs_le_abs_sub w.im v.im
      linarith
    exact (hg w hre).trans (pow_le_pow_left₀ (by positivity) him A)

/-- The constant in the bound for the interpolation multiplier localized by a Gaussian. -/
noncomputable def rectInterpolantGaussianConstant (X β : ℝ) (A : ℕ) : ℝ :=
  (2 * X + 3) / π * Real.exp 9 *
    (Real.exp (β ^ 2) * (Real.exp 2 * (A + 2).factorial) +
      6 ^ A * Real.exp (X ^ 2) * (2 * X + 9) * 17)

/-- The value of the constant in the bound for the interpolation multiplier: importing files
cannot unfold the definition, so they read the constant off this equation. -/
theorem rectInterpolantGaussianConstant_eq (X β : ℝ) (A : ℕ) :
    rectInterpolantGaussianConstant X β A = (2 * X + 3) / π * Real.exp 9 *
      (Real.exp (β ^ 2) * (Real.exp 2 * (A + 2).factorial) +
        6 ^ A * Real.exp (X ^ 2) * (2 * X + 9) * 17) := by
  unfold rectInterpolantGaussianConstant
  rfl

/-- The constant in the bound for the interpolation multiplier is nonnegative. -/
theorem rectInterpolantGaussianConstant_nonneg {X β : ℝ} (hX : 0 ≤ X) (A : ℕ) :
    0 ≤ rectInterpolantGaussianConstant X β A := by
  unfold rectInterpolantGaussianConstant
  positivity

/-- The constant in the bound for the interpolation multiplier is positive. -/
theorem rectInterpolantGaussianConstant_pos {X β : ℝ} (hX : 0 ≤ X) (A : ℕ) :
    0 < rectInterpolantGaussianConstant X β A := by
  unfold rectInterpolantGaussianConstant
  positivity

/-- The interpolation multiplier of the rectangle `[-X, X] × [τ, τ']`, with `θ` an entire
function of polynomial growth times the Gaussian `exp ((u - iτ)²)`, is bounded on a narrower
vertical strip by a constant times `(sup |Φ| / inf |ϑ|)` on the boundary, times a power of
`1 + |τ|`, divided by `1 + (Im u)²`. Only the values of `Φ` and of `ϑ` on the boundary enter. -/
theorem norm_rectInterpolant_gaussian_le {ϑ Φ : ℂ → ℂ} (hϑ : Differentiable ℂ ϑ)
    (hΦ : Differentiable ℂ Φ) {X β τ τ' φb ℓ : ℝ} {A : ℕ} (hβ : 0 < β) (hβX : β < X)
    (hτ₁ : τ + 1 ≤ τ') (hτ₂ : τ' ≤ τ + 3)
    (hg : ∀ u : ℂ, |u.re| ≤ X + 2 → ‖ϑ u‖ ≤ (1 + |u.im|) ^ A) (hℓ : 0 < ℓ)
    (hlow : ∀ w ∈ rectBoundary (-X) X τ τ', ℓ ≤ ‖ϑ w‖)
    (hφ : ∀ w ∈ rectBoundary (-X) X τ τ', ‖Φ w‖ ≤ φb) {u : ℂ} (hu : |u.re| ≤ β) :
    ‖rectInterpolant Φ (fun v ↦ ϑ v * cexp ((v - τ * I) ^ 2)) (-X) X τ τ' u‖ ≤
      rectInterpolantGaussianConstant X β A * (φb / ℓ * (1 + |τ|) ^ (A + 2)) /
        (1 + u.im ^ 2) := by
  set θ : ℂ → ℂ := fun v ↦ ϑ v * cexp ((v - τ * I) ^ 2) with hθdef
  have hX : 0 < X := hβ.trans hβX
  have hx : -X ≤ X := by linarith
  have hy : τ ≤ τ' := by linarith
  have hθ : Differentiable ℂ θ :=
    hϑ.mul (((differentiable_id.sub_const _).pow 2).cexp)
  have hbd (w : ℂ) (hw : w ∈ rectBoundary (-X) X τ τ') : |w.re| ≤ X ∧ τ ≤ w.im ∧ w.im ≤ τ' := by
    rcases hw with ⟨h1, h | h⟩ | ⟨h1, h | h⟩
    · exact ⟨abs_le.mpr h1, h.ge, h.le.trans hy⟩
    · exact ⟨abs_le.mpr h1, hy.trans h.ge, h.le⟩
    · exact ⟨by rw [h, abs_neg, abs_of_pos hX], h1.1, h1.2⟩
    · exact ⟨by rw [h, abs_of_pos hX], h1.1, h1.2⟩
  have hφ0 : 0 ≤ φb :=
    (norm_nonneg _).trans (hφ _ (mem_rectBoundary_horizontal (x := X) (y := τ)
      ⟨hx, le_rfl⟩ (Or.inl rfl)))
  have hElow (w : ℂ) (hw : w ∈ rectBoundary (-X) X τ τ') :
      Real.exp (-9) ≤ ‖cexp ((w - τ * I) ^ 2)‖ := by
    obtain ⟨-, h2, h3⟩ := hbd w hw
    rw [norm_cexp_sub_mul_I_sq]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [sq_nonneg w.re]
  have hθlow (w : ℂ) (hw : w ∈ rectBoundary (-X) X τ τ') : ℓ * Real.exp (-9) ≤ ‖θ w‖ := by
    rw [hθdef, norm_mul]
    exact mul_le_mul (hlow w hw) (hElow w hw) (Real.exp_pos _).le (norm_nonneg _)
  have hpos9 : 0 < ℓ * Real.exp (-9) := mul_pos hℓ (Real.exp_pos _)
  have hne : ∀ w ∈ rectBoundary (-X) X τ τ', θ w ≠ 0 := fun w hw h ↦ by
    have := hθlow w hw
    rw [h, norm_zero] at this
    linarith
  have hper : (X - -X + (τ' - τ)) / π ≤ (2 * X + 3) / π :=
    div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le
  have hperpos : 0 ≤ (X - -X + (τ' - τ)) / π := div_nonneg (by linarith) Real.pi_pos.le
  have hY : 0 ≤ φb / ℓ * (1 + |τ|) ^ (A + 2) := by positivity
  have hden : 0 < 1 + u.im ^ 2 := by positivity
  have he9 : Real.exp 9 * Real.exp (-9) = 1 := by rw [← Real.exp_add]; simp
  rw [le_div_iff₀ hden]
  by_cases hfar : u.im < τ - 1 ∨ τ' + 1 < u.im
  · -- Far from the rectangle: the multiplier is `-θ u` times the Cauchy-type remainder.
    have hout : ¬(u.re ∈ Icc (-X) X ∧ u.im ∈ Icc τ τ') := fun h ↦ by
      rcases hfar with h1 | h1 <;> linarith [h.2.1, h.2.2]
    have hnb : u ∉ rectBoundary (-X) X τ τ' := fun h ↦ by
      obtain ⟨-, h2, h3⟩ := hbd u h
      rcases hfar with h1 | h1 <;> linarith
    have hform : rectInterpolant Φ θ (-X) X τ τ' u =
        -(θ u * rectCauchyRemainder Φ θ (-X) X τ τ' u) := by
      rw [rectInterpolant_eq_of_notMem hΦ hθ hx hy hne hnb,
        rectangleIntegral_sub_inv_of_notMem hx hy hout]
      ring
    have hG : ‖rectCauchyRemainder Φ θ (-X) X τ τ' u‖ ≤
        (X - -X + (τ' - τ)) / π * (φb / (ℓ * Real.exp (-9))) := by
      refine norm_rectCauchyRemainder_le hx hy fun w hw ↦ ?_
      obtain ⟨-, h2, h3⟩ := hbd w hw
      have hdist : 1 ≤ ‖w - u‖ := by
        have h := Complex.abs_im_le_norm (w - u)
        rw [Complex.sub_im] at h
        refine le_trans ?_ h
        rcases hfar with h1 | h1
        · rw [abs_of_nonneg (by linarith)]
          linarith
        · rw [abs_of_nonpos (by linarith)]
          linarith
      rw [norm_div, norm_mul]
      refine div_le_div₀ hφ0 (hφ w hw) hpos9 ?_
      calc ℓ * Real.exp (-9) = ℓ * Real.exp (-9) * 1 := (mul_one _).symm
        _ ≤ ‖θ w‖ * ‖w - u‖ := mul_le_mul (hθlow w hw) hdist zero_le_one (norm_nonneg _)
    have hθu : ‖θ u‖ ≤ (1 + |u.im|) ^ A * (Real.exp (β ^ 2) * Real.exp (-(u.im - τ) ^ 2)) := by
      rw [hθdef, norm_mul, norm_cexp_sub_mul_I_sq]
      refine mul_le_mul (hg u (by linarith)) ?_ (Real.exp_pos _).le (by positivity)
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have : u.re ^ 2 ≤ β ^ 2 := sq_le_sq' (by linarith [(abs_le.mp hu).1]) (abs_le.mp hu).2
      linarith
    have hsq : 1 + u.im ^ 2 ≤ (1 + |u.im|) ^ 2 := by
      nlinarith [abs_nonneg u.im, sq_abs u.im]
    have hgauss := one_add_abs_pow_mul_exp_neg_sq_le (A + 2) u.im τ
    rw [hform, norm_neg, norm_mul]
    have hGnn : 0 ≤ (X - -X + (τ' - τ)) / π * (φb / (ℓ * Real.exp (-9))) :=
      mul_nonneg hperpos (div_nonneg hφ0 hpos9.le)
    calc ‖θ u‖ * ‖rectCauchyRemainder Φ θ (-X) X τ τ' u‖ * (1 + u.im ^ 2)
        ≤ ((1 + |u.im|) ^ A * (Real.exp (β ^ 2) * Real.exp (-(u.im - τ) ^ 2))) *
            ((X - -X + (τ' - τ)) / π * (φb / (ℓ * Real.exp (-9)))) * (1 + |u.im|) ^ 2 :=
          mul_le_mul (mul_le_mul hθu hG (norm_nonneg _) (by positivity)) hsq hden.le
            (mul_nonneg (by positivity) hGnn)
      _ = Real.exp (β ^ 2) * ((1 + |u.im|) ^ (A + 2) * Real.exp (-(u.im - τ) ^ 2)) *
            ((X - -X + (τ' - τ)) / π * (φb / (ℓ * Real.exp (-9)))) := by
          rw [pow_add]
          ring
      _ ≤ Real.exp (β ^ 2) * (Real.exp 2 * (A + 2).factorial * (1 + |τ|) ^ (A + 2)) *
            ((2 * X + 3) / π * (φb / (ℓ * Real.exp (-9)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hgauss (Real.exp_pos _).le)
            (mul_le_mul_of_nonneg_right hper (div_nonneg hφ0 hpos9.le)) hGnn (by positivity)
      _ = (2 * X + 3) / π * Real.exp 9 * (Real.exp (β ^ 2) * (Real.exp 2 * (A + 2).factorial)) *
            (φb / ℓ * (1 + |τ|) ^ (A + 2)) := by
          have h9 : Real.exp (-9) = (Real.exp 9)⁻¹ := Real.exp_neg 9
          rw [h9]
          field_simp
      _ ≤ rectInterpolantGaussianConstant X β A * (φb / ℓ * (1 + |τ|) ^ (A + 2)) := by
          refine mul_le_mul_of_nonneg_right ?_ hY
          unfold rectInterpolantGaussianConstant
          refine mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity)
  · -- Near the rectangle: the mean value bound for the divided difference.
    have hnear : τ - 1 ≤ u.im ∧ u.im ≤ τ' + 1 := by
      constructor
      · by_contra h
        exact hfar (Or.inl (not_le.mp h))
      · by_contra h
        exact hfar (Or.inr (not_le.mp h))
    let S : Set ℂ := (({c : ℂ | -X ≤ c.re} ∩ {c : ℂ | c.re ≤ X}) ∩
      ({c : ℂ | τ - 1 ≤ c.im} ∩ {c : ℂ | c.im ≤ τ' + 1}))
    have hS : Convex ℝ S :=
      ((convex_halfSpace_re_ge (-X)).inter (convex_halfSpace_re_le X)).inter
        ((convex_halfSpace_im_ge (τ - 1)).inter (convex_halfSpace_im_le (τ' + 1)))
    let Δ : ℝ := 6 ^ A * (1 + |τ|) ^ A * Real.exp (X ^ 2) * (2 * X + 9)
    have hderiv (v : ℂ) (hv : v ∈ S) : ‖deriv θ v‖ ≤ Δ := by
      obtain ⟨⟨hv1, hv2⟩, hv3, hv4⟩ := hv
      have hv1' : -X ≤ v.re := hv1
      have hv2' : v.re ≤ X := hv2
      have hv3' : τ - 1 ≤ v.im := hv3
      have hv4' : v.im ≤ τ' + 1 := hv4
      have hvre : |v.re| ≤ X := abs_le.mpr ⟨hv1', hv2'⟩
      have hE : HasDerivAt (fun v : ℂ ↦ cexp ((v - τ * I) ^ 2))
          (cexp ((v - τ * I) ^ 2) * (2 * (v - τ * I))) v := by
        have h0 : HasDerivAt (fun v : ℂ ↦ v - τ * I) 1 v := (hasDerivAt_id v).sub_const _
        have h1 : HasDerivAt (fun v : ℂ ↦ (v - τ * I) ^ 2) (2 * (v - τ * I)) v := by
          have h := h0.mul h0
          have hf : (fun v : ℂ ↦ (v - τ * I) ^ 2) = fun v ↦ (v - τ * I) * (v - τ * I) := by
            funext w
            ring
          rw [hf]
          convert h using 1
          ring
        exact h1.cexp
      have hd : deriv θ v = deriv ϑ v * cexp ((v - τ * I) ^ 2) +
          ϑ v * (cexp ((v - τ * I) ^ 2) * (2 * (v - τ * I))) :=
        ((hϑ v).hasDerivAt.mul hE).deriv
      have hEn : ‖cexp ((v - τ * I) ^ 2)‖ ≤ Real.exp (X ^ 2) := by
        rw [norm_cexp_sub_mul_I_sq]
        refine Real.exp_le_exp.mpr ?_
        have : v.re ^ 2 ≤ X ^ 2 := sq_le_sq' hv1' hv2'
        nlinarith [sq_nonneg (v.im - τ)]
      have hdϑ : ‖deriv ϑ v‖ ≤ (2 + |v.im|) ^ A :=
        norm_deriv_le_of_strip_growth (W := X + 1) hϑ (fun u hu' ↦ hg u (by linarith))
          (by linarith)
      have hϑv : ‖ϑ v‖ ≤ (2 + |v.im|) ^ A :=
        (hg v (by linarith)).trans (pow_le_pow_left₀ (by positivity) (by linarith) A)
      have him : |v.im - τ| ≤ 4 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hlin : ‖(2 : ℂ) * (v - τ * I)‖ ≤ 2 * (X + 4) := by
        rw [norm_mul, Complex.norm_ofNat]
        have h := Complex.norm_le_abs_re_add_abs_im (v - τ * I)
        have hre' : (v - τ * I).re = v.re := by simp
        have him' : (v - τ * I).im = v.im - τ := by simp
        rw [hre', him'] at h
        linarith
      have h6 : 2 + |v.im| ≤ 6 * (1 + |τ|) := by
        have h1 : |v.im| ≤ |τ| + 4 := by
          have := abs_sub_abs_le_abs_sub v.im τ
          linarith
        linarith [abs_nonneg τ]
      have hpow : (2 + |v.im|) ^ A ≤ 6 ^ A * (1 + |τ|) ^ A := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) h6 A
      rw [hd]
      calc ‖deriv ϑ v * cexp ((v - τ * I) ^ 2) +
            ϑ v * (cexp ((v - τ * I) ^ 2) * (2 * (v - τ * I)))‖
          ≤ ‖deriv ϑ v‖ * ‖cexp ((v - τ * I) ^ 2)‖ +
            ‖ϑ v‖ * (‖cexp ((v - τ * I) ^ 2)‖ * ‖(2 : ℂ) * (v - τ * I)‖) := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul, norm_mul]
        _ ≤ (2 + |v.im|) ^ A * Real.exp (X ^ 2) +
            (2 + |v.im|) ^ A * (Real.exp (X ^ 2) * (2 * (X + 4))) :=
            add_le_add (mul_le_mul hdϑ hEn (norm_nonneg _) (by positivity))
              (mul_le_mul hϑv (mul_le_mul hEn hlin (norm_nonneg _) (Real.exp_pos _).le)
                (by positivity) (by positivity))
        _ = (2 + |v.im|) ^ A * (Real.exp (X ^ 2) * (2 * X + 9)) := by ring
        _ ≤ 6 ^ A * (1 + |τ|) ^ A * (Real.exp (X ^ 2) * (2 * X + 9)) :=
            mul_le_mul_of_nonneg_right hpow (by positivity)
        _ = Δ := by
            change _ = 6 ^ A * (1 + |τ|) ^ A * Real.exp (X ^ 2) * (2 * X + 9)
            ring
    have hu1 : -X ≤ u.re := by linarith [(abs_le.mp hu).1]
    have hu2' : u.re ≤ X := by linarith [(abs_le.mp hu).2]
    have huS : u ∈ S := ⟨⟨hu1, hu2'⟩, hnear.1, hnear.2⟩
    have hΔ0 : 0 ≤ Δ := by positivity
    have hm : ‖rectInterpolant Φ θ (-X) X τ τ' u‖ ≤
        (X - -X + (τ' - τ)) / π * (φb * Δ / (ℓ * Real.exp (-9))) := by
      refine norm_rectInterpolant_le hx hy fun w hw ↦ ?_
      obtain ⟨h1, h2, h3⟩ := hbd w hw
      have hwS : w ∈ S :=
        ⟨⟨(abs_le.mp h1).1, (abs_le.mp h1).2⟩, by change τ - 1 ≤ w.im; linarith,
          by change w.im ≤ τ' + 1; linarith⟩
      have hds := norm_dslope_le_of_norm_deriv_le hθ hS hderiv hwS huS
      rw [norm_div, norm_mul]
      exact div_le_div₀ (mul_nonneg hφ0 hΔ0) (mul_le_mul (hφ w hw) hds (norm_nonneg _) hφ0)
        hpos9 (hθlow w hw)
    have hu2 : 1 + u.im ^ 2 ≤ 17 * (1 + |τ|) ^ 2 := by
      have h1 : |u.im| ≤ |τ| + 4 := by
        have h2 : |u.im - τ| ≤ 4 := abs_le.mpr ⟨by linarith [hnear.1], by linarith [hnear.2]⟩
        have := abs_sub_abs_le_abs_sub u.im τ
        linarith
      nlinarith [abs_nonneg u.im, sq_abs u.im, abs_nonneg τ]
    have hmnn : 0 ≤ (X - -X + (τ' - τ)) / π * (φb * Δ / (ℓ * Real.exp (-9))) :=
      mul_nonneg hperpos (div_nonneg (mul_nonneg hφ0 hΔ0) hpos9.le)
    calc ‖rectInterpolant Φ θ (-X) X τ τ' u‖ * (1 + u.im ^ 2)
        ≤ ((X - -X + (τ' - τ)) / π * (φb * Δ / (ℓ * Real.exp (-9)))) *
            (17 * (1 + |τ|) ^ 2) :=
          mul_le_mul hm hu2 hden.le hmnn
      _ ≤ ((2 * X + 3) / π * (φb * Δ / (ℓ * Real.exp (-9)))) * (17 * (1 + |τ|) ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hper
            (div_nonneg (mul_nonneg hφ0 hΔ0) hpos9.le)) (by positivity)
      _ = (2 * X + 3) / π * Real.exp 9 * (6 ^ A * Real.exp (X ^ 2) * (2 * X + 9) * 17) *
            (φb / ℓ * (1 + |τ|) ^ (A + 2)) := by
          have h9 : Real.exp (-9) = (Real.exp 9)⁻¹ := Real.exp_neg 9
          change (2 * X + 3) / π * (φb * (6 ^ A * (1 + |τ|) ^ A * Real.exp (X ^ 2) * (2 * X + 9)) /
            (ℓ * Real.exp (-9))) * (17 * (1 + |τ|) ^ 2) = _
          rw [h9, pow_add]
          field_simp
      _ ≤ rectInterpolantGaussianConstant X β A * (φb / ℓ * (1 + |τ|) ^ (A + 2)) := by
          refine mul_le_mul_of_nonneg_right ?_ hY
          unfold rectInterpolantGaussianConstant
          refine mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)

end RiemannMasullo
