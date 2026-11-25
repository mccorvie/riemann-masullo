module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Green's identity for the Dirichlet integral on a vertical strip, and Carleson's formula at the endpoint

For `h` holomorphic near the closed strip `|Re z| ≤ α`, with `h`, `h'`, `h''` decaying like
`1 / (1 + (Im z)²)`, the Dirichlet integral `∬ ‖h'‖²` over the strip is half the difference of the
integrals of `⟪h, h'⟫ = Re (conj h * h')` over the right and the left edge
(`integral_strip_norm_sq_deriv_eq_boundary`).

Applied to `B g` and to `g`, with `‖B‖ = 1` on the edges, this gives Carleson's formula for the
unweighted Dirichlet integral (`stripCarleson_endpoint`):
`∬ ‖(Bg)'‖² − ∬ ‖g'‖² = ½ ∫ (⟪B, B'⟫ ‖g‖²)(α + it) dt − ½ ∫ (⟪B, B'⟫ ‖g‖²)(−α + it) dt`.
When `‖B‖ ≤ 1` on the strip the right side is the integral of `‖g‖²` against a positive measure
on the boundary (`inner_deriv_nonneg_of_norm_le_one_right`,
`inner_deriv_nonpos_of_norm_le_one_left`).

This is the case `s = 1` of the weighted formula with weight `(α − |Re z|)^{1−s}` used in the
argument posted on issue #7405 (Theorem 10.4.2.1, p. 459, at orders `0 ≤ s ≤ 1`). For `s < 1` the
defect is carried by the line `Re z = 0` and by the interior of the strip; both terms carry the
factor `1 − s`, and at `s = 1` the weight is constant and the defect moves to the boundary.
-/

public section

open Complex MeasureTheory Set Filter Topology

namespace RiemannMasullo

section Lines

variable {h : ℂ → ℂ} {U : Set ℂ}

/-- A holomorphic function along the affine real line `x ↦ a + x * d`. -/
private theorem hasDerivAt_comp_line (hU : IsOpen U) (hh : DifferentiableOn ℂ h U) (a d : ℂ)
    {x : ℝ} (hx : a + x * d ∈ U) :
    HasDerivAt (fun y : ℝ ↦ h (a + y * d)) (d * deriv h (a + x * d)) x := by
  have h1 : HasDerivAt h (deriv h (a + x * d)) (a + x * d) :=
    (hh.differentiableAt (hU.mem_nhds hx)).hasDerivAt
  have h2 : HasDerivAt (fun y : ℝ ↦ a + (y : ℂ) * d) d x := by
    simpa using (((hasDerivAt_id x).ofReal_comp).mul_const d).const_add a
  have h3 := HasDerivAt.scomp x h1 h2
  simpa [Function.comp_def, smul_eq_mul] using h3

/-- The derivative, along the line `x ↦ a + x * d`, of `⟪h, d h'⟫`. -/
private theorem hasDerivAt_inner_line (hU : IsOpen U) (hh : DifferentiableOn ℂ h U) (a d : ℂ)
    {x : ℝ} (hx : a + x * d ∈ U) :
    HasDerivAt (fun y : ℝ ↦ inner ℝ (h (a + y * d)) (d * deriv h (a + y * d)))
      (‖d‖ ^ 2 * ‖deriv h (a + x * d)‖ ^ 2 +
        inner ℝ (h (a + x * d)) (d * (d * deriv (deriv h) (a + x * d)))) x := by
  have h1 := hasDerivAt_comp_line hU hh a d hx
  have h2 := (hasDerivAt_comp_line hU (hh.deriv hU) a d hx).const_mul d
  have h3 := h1.inner ℝ h2
  convert h3 using 1
  rw [real_inner_self_eq_norm_sq, norm_mul, mul_pow, add_comm]

end Lines

section Strip

variable {α : ℝ} {U : Set ℂ}

private theorem tendsto_mul_inv_one_add_sq (K : ℝ) (l : Filter ℝ)
    (hl : Tendsto (fun t : ℝ ↦ |t|) l atTop) :
    Tendsto (fun t : ℝ ↦ K * (1 + t ^ 2)⁻¹) l (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ ↦ 1 + t ^ 2) l atTop := by
    have := tendsto_atTop_add_const_left l (1 : ℝ) ((tendsto_pow_atTop two_ne_zero).comp hl)
    simpa [Function.comp_def, sq_abs] using this
  simpa using (tendsto_inv_atTop_zero.comp h1).const_mul K

private theorem bound_mul_le {M : ℝ} (y u v : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ M / (1 + y ^ 2))
  (hv0 : 0 ≤ v) (hv : v ≤ M / (1 + y ^ 2)) : u * v ≤ M ^ 2 * (1 + y ^ 2)⁻¹ := by
  have hy : 0 < 1 + y ^ 2 := by positivity
  have hi : (1 + y ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg y])
  have hi0 : 0 ≤ (1 + y ^ 2)⁻¹ := (inv_pos.mpr hy).le
  calc u * v ≤ M / (1 + y ^ 2) * (M / (1 + y ^ 2)) :=
        mul_le_mul hu hv hv0 (hu0.trans hu)
    _ = M ^ 2 * ((1 + y ^ 2)⁻¹ * (1 + y ^ 2)⁻¹) := by rw [div_eq_mul_inv]; ring
    _ ≤ M ^ 2 * ((1 + y ^ 2)⁻¹ * 1) := by gcongr
    _ = M ^ 2 * (1 + y ^ 2)⁻¹ := by rw [mul_one]

private theorem strip_integrable {q : ℂ → ℝ} {K : ℝ} (hα : 0 ≤ α)
    (hS : ∀ z : ℂ, |z.re| ≤ α → z ∈ U) (hq : ContinuousOn q U)
    (hb : ∀ z : ℂ, |z.re| ≤ α → |q z| ≤ K * (1 + z.im ^ 2)⁻¹) :
    (∀ σ : ℝ, |σ| ≤ α → Integrable (fun t : ℝ ↦ q (σ + t * I))) ∧
    (∀ t : ℝ, IntervalIntegrable (fun σ : ℝ ↦ q (σ + t * I)) volume (-α) α) ∧
    Integrable (Function.uncurry fun σ t : ℝ ↦ q (σ + t * I))
      ((volume.restrict (Ioc (-α) α)).prod volume) := by
  have hre (σ t : ℝ) : ((σ : ℂ) + t * I).re = σ := by simp
  have him (σ t : ℝ) : ((σ : ℂ) + t * I).im = t := by simp
  have hαα : -α ≤ α := (neg_nonpos.mpr hα).trans hα
  refine ⟨fun σ hσ ↦ ?_, fun t ↦ ?_, ?_⟩
  · have hc : Continuous fun t : ℝ ↦ q (σ + t * I) :=
      hq.comp_continuous (by fun_prop) fun t ↦ hS _ (by rw [hre]; exact hσ)
    refine (integrable_inv_one_add_sq.const_mul K).mono' hc.aestronglyMeasurable
      (ae_of_all _ fun t ↦ ?_)
    have := hb (σ + t * I) (by rw [hre]; exact hσ)
    rwa [him] at this
  · refine ContinuousOn.intervalIntegrable ?_
    refine hq.comp (by fun_prop) fun σ hσ ↦ hS _ ?_
    rw [uIcc_of_le hαα] at hσ
    rw [hre]
    exact abs_le.mpr hσ
  · have hprod : (volume.restrict (Ioc (-α) α)).prod (volume : Measure ℝ) =
        ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (Ioc (-α) α ×ˢ univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    have hmeas : MeasurableSet (Ioc (-α) α ×ˢ (univ : Set ℝ)) :=
      measurableSet_Ioc.prod MeasurableSet.univ
    have hmem (p : ℝ × ℝ) (hp : p ∈ Ioc (-α) α ×ˢ (univ : Set ℝ)) : |p.1| ≤ α :=
      abs_le.mpr ⟨hp.1.1.le, hp.1.2⟩
    have hcont : ContinuousOn (Function.uncurry fun σ t : ℝ ↦ q (σ + t * I))
        (Ioc (-α) α ×ˢ univ) :=
      hq.comp (f := fun p : ℝ × ℝ ↦ ((p.1 : ℂ) + p.2 * I)) (by fun_prop)
        fun p hp ↦ hS _ (by rw [hre]; exact hmem p hp)
    have hc : Integrable (fun _ : ℝ ↦ K) (volume.restrict (Ioc (-α) α)) := by
      have : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc (-α) α)) := ⟨by simp⟩
      exact integrable_const K
    refine (hc.mul_prod integrable_inv_one_add_sq).mono' ?_ ?_
    · rw [hprod]
      exact hcont.aestronglyMeasurable hmeas
    · rw [hprod]
      refine (ae_restrict_mem hmeas).mono fun p hp ↦ ?_
      have := hb (p.1 + p.2 * I) (by rw [hre]; exact hmem p hp)
      rwa [him] at this

/-- **Green's identity for the Dirichlet integral on a vertical strip.** Let `h` be holomorphic
on an open set containing the closed strip `|Re z| ≤ α`, with `h`, `h'`, `h''` bounded by
`M / (1 + (Im z)²)` there. Then the Dirichlet integral of `h` over the strip is half the
difference of the boundary integrals of `⟪h, h'⟫ = Re (conj h * h')` over the two edges. -/
theorem integral_strip_norm_sq_deriv_eq_boundary {h : ℂ → ℂ} {M : ℝ} (hα : 0 ≤ α)
    (hU : IsOpen U) (hS : ∀ z : ℂ, |z.re| ≤ α → z ∈ U) (hh : DifferentiableOn ℂ h U)
    (h0 : ∀ z : ℂ, |z.re| ≤ α → ‖h z‖ ≤ M / (1 + z.im ^ 2))
    (h1 : ∀ z : ℂ, |z.re| ≤ α → ‖deriv h z‖ ≤ M / (1 + z.im ^ 2))
    (h2 : ∀ z : ℂ, |z.re| ≤ α → ‖deriv (deriv h) z‖ ≤ M / (1 + z.im ^ 2)) :
    ∫ σ in (-α)..α, ∫ t : ℝ, ‖deriv h (σ + t * I)‖ ^ 2 =
      1 / 2 * ∫ t : ℝ, (inner ℝ (h (α + t * I)) (deriv h (α + t * I)) -
        inner ℝ (h ((-α : ℝ) + t * I)) (deriv h ((-α : ℝ) + t * I))) := by
  have hre (σ t : ℝ) : ((σ : ℂ) + t * I).re = σ := by simp
  have him (σ t : ℝ) : ((σ : ℂ) + t * I).im = t := by simp
  have hαα : -α ≤ α := (neg_nonpos.mpr hα).trans hα
  -- the product of two of the bounds
  have hbnd := bound_mul_le (M := M)
  obtain ⟨qA, hqA⟩ : ∃ q : ℂ → ℝ, ∀ z, q z = ‖deriv h z‖ ^ 2 := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨qB, hqB⟩ : ∃ q : ℂ → ℝ, ∀ z, q z = inner ℝ (h z) (deriv (deriv h) z) :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨qG, hqG⟩ : ∃ q : ℂ → ℝ, ∀ z, q z = inner ℝ (h z) (deriv h z) := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨qJ, hqJ⟩ : ∃ q : ℂ → ℝ, ∀ z, q z = inner ℝ (h z) (I * deriv h z) :=
    ⟨_, fun _ ↦ rfl⟩
  have hc0 := hh.continuousOn
  have hc1 := (hh.deriv hU).continuousOn
  have hc2 := ((hh.deriv hU).deriv hU).continuousOn
  have hbA (z : ℂ) (hz : |z.re| ≤ α) : |qA z| ≤ M ^ 2 * (1 + z.im ^ 2)⁻¹ := by
    rw [hqA, abs_of_nonneg (by positivity), sq]
    exact hbnd _ _ _ (norm_nonneg _) (h1 z hz) (norm_nonneg _) (h1 z hz)
  have hbB (z : ℂ) (hz : |z.re| ≤ α) : |qB z| ≤ M ^ 2 * (1 + z.im ^ 2)⁻¹ := by
    rw [hqB]
    exact (abs_real_inner_le_norm _ _).trans
      (hbnd _ _ _ (norm_nonneg _) (h0 z hz) (norm_nonneg _) (h2 z hz))
  have hbJ (z : ℂ) (hz : |z.re| ≤ α) : |qJ z| ≤ M ^ 2 * (1 + z.im ^ 2)⁻¹ := by
    rw [hqJ]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_mul, norm_I, one_mul]
    exact hbnd _ _ _ (norm_nonneg _) (h0 z hz) (norm_nonneg _) (h1 z hz)
  have hcA : ContinuousOn qA U := (hc1.norm.pow 2).congr fun z _ ↦ hqA z
  have hcB : ContinuousOn qB U := (hc0.inner hc2).congr fun z _ ↦ hqB z
  obtain ⟨hA1, hA2, hA3⟩ := strip_integrable hα hS hcA hbA
  obtain ⟨hB1, hB2, hB3⟩ := strip_integrable hα hS hcB hbB
  -- derivative in `σ`
  have hdσ (σ t : ℝ) (hσ : |σ| ≤ α) :
      HasDerivAt (fun x : ℝ ↦ qG (x + t * I)) (qA (σ + t * I) + qB (σ + t * I)) σ := by
    have e (x : ℝ) : (t : ℂ) * I + (x : ℂ) * 1 = x + t * I := by ring
    have := hasDerivAt_inner_line hU hh (t * I) 1 (x := σ)
      (by rw [e]; exact hS _ (by rw [hre]; exact hσ))
    simp only [e, one_mul, norm_one, one_pow, ← hqA, ← hqB, ← hqG] at this
    exact this
  -- derivative in `t`
  have hdt (σ t : ℝ) (hσ : |σ| ≤ α) :
      HasDerivAt (fun x : ℝ ↦ qJ (σ + x * I)) (qA (σ + t * I) - qB (σ + t * I)) t := by
    have := hasDerivAt_inner_line hU hh σ I (x := t) (hS _ (by rw [hre]; exact hσ))
    have e (w : ℂ) : I * (I * w) = -w := by rw [← mul_assoc, I_mul_I]; ring
    simp only [e, norm_I, one_pow, one_mul, inner_neg_right, ← sub_eq_add_neg, ← hqA, ← hqB,
      ← hqJ] at this
    exact this
  -- the integral in `t` of the `t`-derivative vanishes
  have hzero (σ : ℝ) (hσ : |σ| ≤ α) :
      ∫ t : ℝ, qA (σ + t * I) = 1 / 2 * ∫ t : ℝ, (qA (σ + t * I) + qB (σ + t * I)) := by
    have hlim (l : Filter ℝ) (hl : Tendsto (fun t : ℝ ↦ |t|) l atTop) :
        Tendsto (fun x : ℝ ↦ qJ (σ + x * I)) l (𝓝 0) := by
      refine squeeze_zero_norm (fun x ↦ ?_) (tendsto_mul_inv_one_add_sq (M ^ 2) l hl)
      have := hbJ (σ + x * I) (by rw [hre]; exact hσ)
      rwa [him] at this
    have h := integral_of_hasDerivAt_of_tendsto (fun t ↦ hdt σ t hσ)
      ((hA1 σ hσ).sub (hB1 σ hσ)) (hlim _ tendsto_abs_atBot_atTop)
      (hlim _ tendsto_abs_atTop_atTop)
    rw [integral_sub (hA1 σ hσ) (hB1 σ hσ), sub_zero] at h
    rw [integral_add (hA1 σ hσ) (hB1 σ hσ)]
    linarith
  have hstep1 : ∫ σ in (-α)..α, ∫ t : ℝ, qA (σ + t * I) =
      ∫ σ in (-α)..α, 1 / 2 * ∫ t : ℝ, (qA (σ + t * I) + qB (σ + t * I)) :=
    intervalIntegral.integral_congr fun σ hσ ↦ by
      rw [uIcc_of_le hαα] at hσ
      exact hzero σ (abs_le.mpr hσ)
  have hswap : ∫ σ in (-α)..α, ∫ t : ℝ, (qA (σ + t * I) + qB (σ + t * I)) =
      ∫ t : ℝ, ∫ σ in (-α)..α, (qA (σ + t * I) + qB (σ + t * I)) := by
    rw [intervalIntegral.integral_of_le hαα]
    simp_rw [intervalIntegral.integral_of_le hαα]
    exact integral_integral_swap (hA3.add hB3)
  have hinner (t : ℝ) : ∫ σ in (-α)..α, (qA (σ + t * I) + qB (σ + t * I)) =
      qG (α + t * I) - qG ((-α : ℝ) + t * I) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun σ hσ ↦ hdσ σ t (by rw [uIcc_of_le hαα] at hσ; exact abs_le.mpr hσ))
      ((hA2 t).add (hB2 t))
  simp_rw [← hqA, ← hqG]
  rw [hstep1, intervalIntegral.integral_const_mul, hswap]
  simp_rw [hinner]

/-- Under the hypotheses of `integral_strip_norm_sq_deriv_eq_boundary`, the boundary density
`⟪h, h'⟫` is integrable on every vertical line of the closed strip. -/
theorem integrable_inner_deriv_strip_line {h : ℂ → ℂ} {M : ℝ} (hα : 0 ≤ α)
    (hU : IsOpen U) (hS : ∀ z : ℂ, |z.re| ≤ α → z ∈ U) (hh : DifferentiableOn ℂ h U)
    (h0 : ∀ z : ℂ, |z.re| ≤ α → ‖h z‖ ≤ M / (1 + z.im ^ 2))
    (h1 : ∀ z : ℂ, |z.re| ≤ α → ‖deriv h z‖ ≤ M / (1 + z.im ^ 2)) {σ : ℝ} (hσ : |σ| ≤ α) :
    Integrable fun t : ℝ ↦ inner ℝ (h (σ + t * I)) (deriv h (σ + t * I)) :=
  (strip_integrable (q := fun z ↦ inner ℝ (h z) (deriv h z)) hα hS
    (hh.continuousOn.inner (hh.deriv hU).continuousOn) fun z hz ↦
      (abs_real_inner_le_norm _ _).trans
        (bound_mul_le _ _ _ (norm_nonneg _) (h0 z hz) (norm_nonneg _) (h1 z hz))).1 σ hσ

private theorem inner_mul_mul_add (a b c d : ℂ) : inner ℝ (a * c) (b * c + a * d) =
    inner ℝ a b * ‖c‖ ^ 2 + ‖a‖ ^ 2 * inner ℝ c d := by
  simp only [Complex.inner, Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- **Carleson's formula on the strip for the unweighted Dirichlet integral** (the endpoint
`s = 1` of the weight `(α − |σ|)^{1−s}`). Let `B` and `g` be holomorphic on an open set containing
the closed strip `|Re z| ≤ α`, with `B`, `B'`, `B''` bounded there, `‖B‖ = 1` on the two edges,
and `g`, `g'`, `g''` bounded by `M / (1 + (Im z)²)`. Then
`∬ ‖(Bg)'‖² − ∬ ‖g'‖² = ½ ∫ (⟪B, B'⟫ ‖g‖²)(α + it) dt − ½ ∫ (⟪B, B'⟫ ‖g‖²)(−α + it) dt`:
the defect is the integral of `‖g‖²` against a measure carried by the boundary. By
`inner_deriv_nonneg_of_norm_le_one_right` and `inner_deriv_nonpos_of_norm_le_one_left` that
measure is positive when `‖B‖ ≤ 1` on the strip. -/
theorem stripCarleson_endpoint {B g : ℂ → ℂ} {C M : ℝ} (hα : 0 ≤ α) (hU : IsOpen U)
    (hS : ∀ z : ℂ, |z.re| ≤ α → z ∈ U) (hB : DifferentiableOn ℂ B U)
    (hg : DifferentiableOn ℂ g U)
    (hB0 : ∀ z : ℂ, |z.re| ≤ α → ‖B z‖ ≤ C) (hB1 : ∀ z : ℂ, |z.re| ≤ α → ‖deriv B z‖ ≤ C)
    (hB2 : ∀ z : ℂ, |z.re| ≤ α → ‖deriv (deriv B) z‖ ≤ C)
    (hBb : ∀ z : ℂ, |z.re| = α → ‖B z‖ = 1)
    (hg0 : ∀ z : ℂ, |z.re| ≤ α → ‖g z‖ ≤ M / (1 + z.im ^ 2))
    (hg1 : ∀ z : ℂ, |z.re| ≤ α → ‖deriv g z‖ ≤ M / (1 + z.im ^ 2))
    (hg2 : ∀ z : ℂ, |z.re| ≤ α → ‖deriv (deriv g) z‖ ≤ M / (1 + z.im ^ 2)) :
    (∫ σ in (-α)..α, ∫ t : ℝ, ‖deriv (fun z ↦ B z * g z) (σ + t * I)‖ ^ 2) -
        ∫ σ in (-α)..α, ∫ t : ℝ, ‖deriv g (σ + t * I)‖ ^ 2 =
      1 / 2 * ∫ t : ℝ, (inner ℝ (B (α + t * I)) (deriv B (α + t * I)) * ‖g (α + t * I)‖ ^ 2 -
        inner ℝ (B ((-α : ℝ) + t * I)) (deriv B ((-α : ℝ) + t * I)) *
          ‖g ((-α : ℝ) + t * I)‖ ^ 2) := by
  have hre (σ t : ℝ) : ((σ : ℂ) + t * I).re = σ := by simp
  obtain ⟨H, hH⟩ : ∃ H : ℂ → ℂ, H = fun z ↦ B z * g z := ⟨_, rfl⟩
  have hC : 0 ≤ C := (norm_nonneg _).trans (hB0 0 (by simpa using hα))
  have hdH (z : ℂ) (hz : z ∈ U) : deriv H z = deriv B z * g z + B z * deriv g z := by
    rw [hH]
    exact ((hB.differentiableAt (hU.mem_nhds hz)).hasDerivAt.mul
      (hg.differentiableAt (hU.mem_nhds hz)).hasDerivAt).deriv
  have hddH (z : ℂ) (hz : z ∈ U) : deriv (deriv H) z =
      deriv (deriv B) z * g z + 2 * (deriv B z * deriv g z) + B z * deriv (deriv g) z := by
    have he : deriv H =ᶠ[𝓝 z] fun w ↦ deriv B w * g w + B w * deriv g w :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hz) hdH
    rw [he.deriv_eq]
    have hB' := (hB.differentiableAt (hU.mem_nhds hz)).hasDerivAt
    have hg' := (hg.differentiableAt (hU.mem_nhds hz)).hasDerivAt
    have hB'' := ((hB.deriv hU).differentiableAt (hU.mem_nhds hz)).hasDerivAt
    have hg'' := ((hg.deriv hU).differentiableAt (hU.mem_nhds hz)).hasDerivAt
    exact (((hB''.mul hg').add (hB'.mul hg'')).congr_deriv (by ring)).deriv
  have hHd : DifferentiableOn ℂ H U := by rw [hH]; exact hB.mul hg
  have key (z : ℂ) (hz : |z.re| ≤ α) :
      ‖H z‖ ≤ 4 * C * M / (1 + z.im ^ 2) ∧ ‖deriv H z‖ ≤ 4 * C * M / (1 + z.im ^ 2) ∧
        ‖deriv (deriv H) z‖ ≤ 4 * C * M / (1 + z.im ^ 2) := by
    have b0 := hB0 z hz
    have b1 := hB1 z hz
    have b2 := hB2 z hz
    have g0 := hg0 z hz
    have g1 := hg1 z hz
    have g2 := hg2 z hz
    obtain ⟨m, hm⟩ : ∃ m : ℝ, m = M / (1 + z.im ^ 2) := ⟨_, rfl⟩
    rw [← hm] at g0 g1 g2
    have hm0 : 0 ≤ m := (norm_nonneg _).trans g0
    have e : 4 * C * M / (1 + z.im ^ 2) = 4 * (C * m) := by rw [hm]; ring
    have hCm : 0 ≤ C * m := mul_nonneg hC hm0
    rw [e, hdH z (hS z hz), hddH z (hS z hz), hH]
    refine ⟨?_, ?_, ?_⟩
    · calc ‖B z * g z‖ = ‖B z‖ * ‖g z‖ := norm_mul _ _
        _ ≤ C * m := by gcongr
        _ ≤ 4 * (C * m) := by linarith
    · calc ‖deriv B z * g z + B z * deriv g z‖
          ≤ ‖deriv B z‖ * ‖g z‖ + ‖B z‖ * ‖deriv g z‖ :=
            (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
        _ ≤ C * m + C * m := by gcongr
        _ ≤ 4 * (C * m) := by linarith
    · calc ‖deriv (deriv B) z * g z + 2 * (deriv B z * deriv g z) + B z * deriv (deriv g) z‖
          ≤ ‖deriv (deriv B) z‖ * ‖g z‖ + 2 * (‖deriv B z‖ * ‖deriv g z‖) +
              ‖B z‖ * ‖deriv (deriv g) z‖ := by
            refine (norm_add_le _ _).trans ?_
            refine add_le_add ((norm_add_le _ _).trans ?_) (norm_mul _ _).le
            simp
        _ ≤ C * m + 2 * (C * m) + C * m := by gcongr
        _ = 4 * (C * m) := by ring
  have EH := integral_strip_norm_sq_deriv_eq_boundary hα hU hS hHd (fun z hz ↦ (key z hz).1)
    (fun z hz ↦ (key z hz).2.1) (fun z hz ↦ (key z hz).2.2)
  have Eg := integral_strip_norm_sq_deriv_eq_boundary hα hU hS hg hg0 hg1 hg2
  have hαabs : |α| ≤ α := (abs_of_nonneg hα).le
  have hαabs' : |-α| ≤ α := by rw [abs_neg]; exact hαabs
  have IH (σ : ℝ) (hσ : |σ| ≤ α) := integrable_inner_deriv_strip_line hα hU hS hHd
    (fun z hz ↦ (key z hz).1) (fun z hz ↦ (key z hz).2.1) hσ
  have Ig (σ : ℝ) (hσ : |σ| ≤ α) := integrable_inner_deriv_strip_line hα hU hS hg hg0 hg1 hσ
  have hsub := integral_sub ((IH α hαabs).sub (IH (-α) hαabs'))
    ((Ig α hαabs).sub (Ig (-α) hαabs'))
  simp only [Pi.sub_apply] at hsub
  rw [← hH, EH, Eg, ← mul_sub, ← hsub]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
  have pt (σ : ℝ) (hσ : |σ| = α) :
      inner ℝ (H (σ + t * I)) (deriv H (σ + t * I)) -
          inner ℝ (g (σ + t * I)) (deriv g (σ + t * I)) =
        inner ℝ (B (σ + t * I)) (deriv B (σ + t * I)) * ‖g (σ + t * I)‖ ^ 2 := by
    have hz : |((σ : ℂ) + t * I).re| = α := by rw [hre]; exact hσ
    rw [hdH _ (hS _ hz.le), hH, inner_mul_mul_add, hBb _ hz]
    ring
  have p1 := pt α (abs_of_nonneg hα)
  have p2 := pt (-α) (by rw [abs_neg, abs_of_nonneg hα])
  simp only [] at p1 p2 ⊢
  linarith

/-- On the right edge of the strip, a function of norm at most one on the strip and of norm one at
a boundary point has `⟪B, B'⟫ ≥ 0` there. -/
theorem inner_deriv_nonneg_of_norm_le_one_right {B : ℂ → ℂ} (hα : 0 < α) (hU : IsOpen U)
    (hS : ∀ z : ℂ, |z.re| ≤ α → z ∈ U) (hB : DifferentiableOn ℂ B U)
    (hle : ∀ z : ℂ, |z.re| ≤ α → ‖B z‖ ≤ 1) (t : ℝ) (h1 : ‖B (α + t * I)‖ = 1) :
    0 ≤ inner ℝ (B (α + t * I)) (deriv B (α + t * I)) := by
  have e (x : ℝ) : (t : ℂ) * I + (x : ℂ) * 1 = x + t * I := by ring
  have hre (σ : ℝ) : ((σ : ℂ) + t * I).re = σ := by simp
  have hd := (hasDerivAt_comp_line hU hB (t * I) 1 (x := α)
    (by rw [e]; exact hS _ (by rw [hre]; exact (abs_of_pos hα).le))).norm_sq
  simp only [e, one_mul] at hd
  have hs := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsLT_le_nhdsNE α)
  have h2 : 0 ≤ 2 * inner ℝ (B (α + t * I)) (deriv B (α + t * I)) := by
    refine ge_of_tendsto hs ?_
    filter_upwards [Ioo_mem_nhdsLT (neg_lt_self hα)] with x hx
    rw [slope_def_field]
    refine div_nonneg_of_nonpos ?_ (by linarith [hx.2])
    have hx1 := hle (x + t * I) (by rw [hre]; exact abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
    simp only [h1]
    nlinarith [norm_nonneg (B (x + t * I))]
  linarith

/-- On the left edge of the strip, a function of norm at most one on the strip and of norm one at
a boundary point has `⟪B, B'⟫ ≤ 0` there. -/
theorem inner_deriv_nonpos_of_norm_le_one_left {B : ℂ → ℂ} (hα : 0 < α) (hU : IsOpen U)
    (hS : ∀ z : ℂ, |z.re| ≤ α → z ∈ U) (hB : DifferentiableOn ℂ B U)
    (hle : ∀ z : ℂ, |z.re| ≤ α → ‖B z‖ ≤ 1) (t : ℝ) (h1 : ‖B ((-α : ℝ) + t * I)‖ = 1) :
    inner ℝ (B ((-α : ℝ) + t * I)) (deriv B ((-α : ℝ) + t * I)) ≤ 0 := by
  have e (x : ℝ) : (t : ℂ) * I + (x : ℂ) * 1 = x + t * I := by ring
  have hre (σ : ℝ) : ((σ : ℂ) + t * I).re = σ := by simp
  have hd := (hasDerivAt_comp_line hU hB (t * I) 1 (x := -α)
    (by rw [e]; exact hS _ (by rw [hre, abs_neg]; exact (abs_of_pos hα).le))).norm_sq
  simp only [e, one_mul] at hd
  have hs := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsGT_le_nhdsNE (-α))
  have h2 : 2 * inner ℝ (B ((-α : ℝ) + t * I)) (deriv B ((-α : ℝ) + t * I)) ≤ 0 := by
    refine le_of_tendsto hs ?_
    filter_upwards [Ioo_mem_nhdsGT (neg_lt_self hα)] with x hx
    rw [slope_def_field]
    refine div_nonpos_of_nonpos_of_nonneg ?_ (by linarith [hx.1])
    have hx1 := hle (x + t * I) (by rw [hre]; exact abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
    simp only [h1]
    nlinarith [norm_nonneg (B (x + t * I))]
  linarith

end Strip

end RiemannMasullo
