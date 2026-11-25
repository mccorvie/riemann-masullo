module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Local interpolation and the radius-six perturbation

Projecting a feasible vector onto the closed span of the Riesz kernels constructs its
unique minimum-norm interpolant. This projection bounds the change of the cardinal under
enlargement of the site set by the defect of any admissible cutoff. Applied to the moment
and multiplier of the local cardinal, the defect yields a relative error in its weak norm.
-/

@[expose] public noncomputable section

open Set
open scoped InnerProductSpace

namespace RiemannMasullo.WeakCardinal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Closed span of the Riesz kernels corresponding to the prescribed sample sites. -/
abbrev interpolationSpan (kernel : ℝ → H) (S : Set ℝ) : Submodule ℂ H :=
  (Submodule.span ℂ (kernel '' S)).topologicalClosure

/-- Kronecker interpolation data on the actual sites. -/
def HasCardinalValues (kernel : ℝ → H) (S : Set ℝ) (w : ℝ) (f : H) : Prop :=
  ∀ x ∈ S, ⟪kernel x, f⟫_ℂ = if x = w then 1 else 0

/-- An interpolant in the closed span of its evaluation kernels. -/
structure IsMinimumCardinal (kernel : ℝ → H) (S : Set ℝ) (w : ℝ) (f : H) : Prop where
  mem : f ∈ interpolationSpan kernel S
  values : HasCardinalValues kernel S w f

private theorem kernel_mem_span {kernel : ℝ → H} {S : Set ℝ} {x : ℝ} (hx : x ∈ S) :
    kernel x ∈ interpolationSpan kernel S :=
  (Submodule.span ℂ (kernel '' S)).le_topologicalClosure
    (Submodule.subset_span (Set.mem_image_of_mem kernel hx))

private theorem span_mono {kernel : ℝ → H} {E Z : Set ℝ} (hEZ : E ⊆ Z) :
    interpolationSpan kernel E ≤ interpolationSpan kernel Z :=
  Submodule.topologicalClosure_mono (Submodule.span_mono (Set.image_mono hEZ))

/-- Orthogonal projection preserves every specified evaluation and constructs the cardinal. -/
theorem isMinimumCardinal_projection {kernel : ℝ → H} {S : Set ℝ} {w : ℝ} {g : H}
    (hg : HasCardinalValues kernel S w g) :
    IsMinimumCardinal kernel S w ((interpolationSpan kernel S).starProjection g) := by
  let K := interpolationSpan kernel S
  refine ⟨K.starProjection_apply_mem g, ?_⟩
  intro x hx
  have h := K.sub_starProjection_mem_orthogonal g (kernel x) (kernel_mem_span hx)
  rw [inner_sub_right, sub_eq_zero] at h
  exact h.symm.trans (hg x hx)

/-- Any vector having the same data projects to the minimum cardinal. -/
theorem IsMinimumCardinal.project_feasible {kernel : ℝ → H} {S : Set ℝ} {w : ℝ} {f g : H}
    (hf : IsMinimumCardinal kernel S w f) (hg : HasCardinalValues kernel S w g) :
    (interpolationSpan kernel S).starProjection g = f := by
  let L := innerSL ℂ (g-f)
  have hL : interpolationSpan kernel S ≤ L.ker := by
    apply Submodule.topologicalClosure_minimal _ _ L.isClosed_ker
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    change ⟪g-f, kernel x⟫_ℂ = 0
    rw [inner_eq_zero_symm, inner_sub_right, hg x hx, hf.values x hx, sub_self]
  apply Submodule.eq_starProjection_of_mem_orthogonal hf.mem
  intro y hy
  exact inner_eq_zero_symm.mp (show ⟪g-f, y⟫_ℂ = 0 from hL hy)

/-- This characterization gives both the usual minimum of the norm and its uniqueness. -/
theorem IsMinimumCardinal.norm_le {kernel : ℝ → H} {S : Set ℝ} {w : ℝ} {f g : H}
    (hf : IsMinimumCardinal kernel S w f) (hg : HasCardinalValues kernel S w g) : ‖f‖ ≤ ‖g‖ := by
  rw [← hf.project_feasible hg]
  exact Submodule.norm_starProjection_apply_le _ _

/-- The site data admit at most one minimum cardinal, even for an infinite set. -/
theorem IsMinimumCardinal.unique {kernel : ℝ → H} {S : Set ℝ} {w : ℝ} {f g : H}
    (hf : IsMinimumCardinal kernel S w f) (hg : IsMinimumCardinal kernel S w g) : f = g :=
  (hf.project_feasible hg.values).symm.trans (Submodule.starProjection_eq_self_iff.mpr hg.mem)

/-- Membership in the Riesz span is equivalent to the variational definition of the
minimum among all vectors with the cardinal data. -/
theorem isMinimumCardinal_iff_norm_le {kernel : ℝ → H} {S : Set ℝ} {w : ℝ} {f : H} :
    IsMinimumCardinal kernel S w f ↔ HasCardinalValues kernel S w f ∧
      ∀ g : H, HasCardinalValues kernel S w g → ‖f‖ ≤ ‖g‖ := by
  refine ⟨fun hf ↦ ⟨hf.values, fun _ hg ↦ hf.norm_le hg⟩, ?_⟩
  rintro ⟨hf, hmin⟩
  let K := interpolationSpan kernel S
  let p := K.starProjection f
  have hp : IsMinimumCardinal kernel S w p := isMinimumCardinal_projection hf
  have horth : ⟪p,f-p⟫_ℂ = 0 := K.sub_starProjection_mem_orthogonal f p hp.mem
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p (f-p) horth
  rw [show p+(f-p)=f by abel] at hpy
  have hle := mul_self_le_mul_self (norm_nonneg f) (hmin p hp.values)
  have heq : ‖f-p‖ = 0 := by nlinarith [sq_nonneg ‖f-p‖]
  have hfp : f = p := sub_eq_zero.mp (norm_eq_zero.mp heq)
  exact hfp ▸ hp

/-- A finite Gram expansion requires only its Kronecker evaluations to certify minimality. -/
theorem isMinimumCardinal_finite_sum {ι : Type*} [Fintype ι]
    (kernel : ℝ → H) (site : ι → ℝ) (w : ℝ) (c : ι → ℂ)
    (hd : ∀ i, ⟪kernel (site i), ∑ j, c j • kernel (site j)⟫_ℂ =
      if site i = w then 1 else 0) :
    IsMinimumCardinal kernel (Set.range site) w (∑ j, c j • kernel (site j)) := by
  refine ⟨Submodule.sum_mem _ (fun i _ ↦ Submodule.smul_mem _ _ (kernel_mem_span ⟨i, rfl⟩)), ?_⟩
  rintro _ ⟨i, rfl⟩
  exact hd i

/-- For nested data, one admissible full competitor bounds the difference of the two minima.
The estimate is independent of the size and spacing of the site sets. -/
theorem nested_cardinal_residual {kernel : ℝ → H} {E Z : Set ℝ} {w : ℝ} {hE hZ g : H}
    (hEZ : E ⊆ Z) (hlocal : IsMinimumCardinal kernel E w hE)
    (hfull : IsMinimumCardinal kernel Z w hZ) (hg : HasCardinalValues kernel Z w g) :
    ‖hZ - hE‖ ≤ ‖g - hE‖ := by
  let K := interpolationSpan kernel Z
  have hp : K.starProjection hE = hE := Submodule.starProjection_eq_self_iff.mpr (span_mono hEZ hlocal.mem)
  have ht := K.norm_starProjection_apply_le (g-hE)
  rwa [map_sub, hfull.project_feasible hg, hp] at ht

/-- All sites in the closed radius-six interval, including both endpoints. -/
def radiusSixSites (Z : Set ℝ) (w : ℝ) : Set ℝ := Z ∩ Icc (w-6) (w+6)

/-- Relative radius-six error measured against the computed local cardinal. -/
def radiusSixError : ℝ := 13 * Real.sqrt 3 / 48

theorem radiusSixError_pos : 0 < radiusSixError := by unfold radiusSixError; positivity

theorem radiusSixError_lt_half : radiusSixError < 1/2 := by
  have h : Real.sqrt 3 < (24:ℝ)/13 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  unfold radiusSixError
  linarith

/-- A multiplier evaluated on the centered first moment gives a feasible full-site cutoff.
Only its exterior formula enters the site argument; no separation of the sites is needed. -/
theorem cutoff_hasCardinalValues {kernel : ℝ → H} {Z : Set ℝ} {w : ℝ} {hE u v : H}
    (hlocal : HasCardinalValues kernel (radiusSixSites Z w) w hE)
    (a : ℝ → ℝ) (hexterior : ∀ x, 6 < |x-w| → a x * (x-w) = 1)
    (hmoment : ∀ x ∈ Z, ⟪kernel x, u⟫_ℂ = ((x-w : ℝ) : ℂ) * ⟪kernel x, hE⟫_ℂ)
    (hmul : ∀ x ∈ Z, ⟪kernel x, v⟫_ℂ = (a x : ℂ) * ⟪kernel x, u⟫_ℂ) :
    HasCardinalValues kernel Z w (hE-v) := by
  intro x hx
  rw [inner_sub_right, hmul x hx, hmoment x hx]
  by_cases hnear : |x-w| ≤ 6
  · obtain ⟨hl, hr⟩ := abs_le.mp hnear
    rw [hlocal x ⟨hx, by constructor <;> linarith⟩]
    by_cases h : x = w
    · subst x; simp
    · simp [h]
  · have h : x ≠ w := fun e ↦ hnear (by simp [e])
    rw [← mul_assoc, ← Complex.ofReal_mul, hexterior x (lt_of_not_ge hnear)]
    simp [h]

/-- A contraction from the strong space to the weak space turns a strong residual estimate into
both sides of the radius-six comparison. -/
theorem weak_bounds_of_radiusSix_residual {G : Type*} [SeminormedAddCommGroup G]
    (J : H → G) (hJ : LipschitzWith 1 J) {hE hZ : H}
    (h : ‖hZ-hE‖ ≤ radiusSixError * ‖J hE‖) :
    (1-radiusSixError) * ‖J hE‖ ≤ ‖J hZ‖ ∧ ‖J hZ‖ ≤ (1+radiusSixError) * ‖J hE‖ := by
  have hc : ‖J hZ - J hE‖ ≤ ‖hZ-hE‖ := by simpa [dist_eq_norm] using hJ.dist_le_mul hZ hE
  have hd := (abs_norm_sub_norm_le (J hZ) (J hE)).trans (hc.trans h)
  obtain ⟨hl, hr⟩ := abs_le.mp hd
  constructor <;> linarith

private theorem firstMomentFactor_le_sqrt_three {θ : ℝ} (hθ : 1 < θ) (hθ' : θ ≤ 3/2) :
    Real.sqrt (θ * (2*θ-1)) ≤ Real.sqrt 3 := by
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg (by linarith : 0 ≤ 3/2-θ) (by linarith : 0 ≤ 2*θ+2)]

/-- Construct the full minimum directly from the cutoff of a finite local cardinal, with the
sharp numerical radius-six bounds. The analytic inputs are the first moment at that vector and
the multiplication bound on that moment. Their site values identify the physical products. -/
theorem exists_fullMinimum_radiusSix {G : Type*} [SeminormedAddCommGroup G]
    {kernel : ℝ → H} {Z : Set ℝ} {w θ : ℝ} (hθ : 1 < θ) (hθ' : θ ≤ 3/2)
    (J : H → G) (hJ : LipschitzWith 1 J) {hE u v : H}
    (hlocal : IsMinimumCardinal kernel (radiusSixSites Z w) w hE)
    (a : ℝ → ℝ) (hexterior : ∀ x, 6 < |x-w| → a x * (x-w) = 1)
    (hmoment : ∀ x ∈ Z, ⟪kernel x, u⟫_ℂ = ((x-w : ℝ) : ℂ) * ⟪kernel x, hE⟫_ℂ)
    (hmul : ∀ x ∈ Z, ⟪kernel x, v⟫_ℂ = (a x : ℂ) * ⟪kernel x, u⟫_ℂ)
    (hfirst : ‖u‖ ≤ Real.sqrt (θ*(2*θ-1)) * ‖J hE‖) (hoperator : ‖v‖ ≤ (13/48) * ‖u‖) :
    ∃ hZ : H, IsMinimumCardinal kernel Z w hZ ∧ ‖hZ-hE‖ ≤ radiusSixError * ‖J hE‖ ∧
      (1-radiusSixError) * ‖J hE‖ ≤ ‖J hZ‖ ∧ ‖J hZ‖ ≤ (1+radiusSixError) * ‖J hE‖ := by
  let g := hE-v
  have hg : HasCardinalValues kernel Z w g :=
    cutoff_hasCardinalValues hlocal.values a hexterior hmoment hmul
  let hZ := (interpolationSpan kernel Z).starProjection g
  have hfull : IsMinimumCardinal kernel Z w hZ := isMinimumCardinal_projection hg
  have hres := nested_cardinal_residual (Set.inter_subset_left (t := Icc (w-6) (w+6))) hlocal hfull hg
  have herr : ‖hZ-hE‖ ≤ radiusSixError * ‖J hE‖ := calc
    ‖hZ-hE‖ ≤ ‖v‖ := by simpa [g] using hres
    _ ≤ (13/48) * ‖u‖ := hoperator
    _ ≤ (13/48) * (Real.sqrt 3 * ‖J hE‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact hfirst.trans (mul_le_mul_of_nonneg_right (firstMomentFactor_le_sqrt_three hθ hθ') (norm_nonneg _))
    _ = _ := by unfold radiusSixError; ring
  exact ⟨hZ, hfull, herr, weak_bounds_of_radiusSix_residual J hJ herr⟩

end RiemannMasullo.WeakCardinal
