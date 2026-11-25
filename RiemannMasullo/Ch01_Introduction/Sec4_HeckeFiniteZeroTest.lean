module

public import RiemannMasullo.ForMathlib.Analysis.Complex.ExpandingTaylorSections
public import RiemannMasullo.AppB_AnalyticNT.FiniteHardyIdealTable
public import RiemannMasullo.Ch01_Introduction.Sec4_HeckeSignedCoefficients

/-! # Finite ideal polynomial sections on expanding disks

The input at stage `n` consists of a single degree-at-most-`n³` polynomial from the finite
ideal row with exponent zero. The ordinary chart and the holomorphic pole-cleared function
have identical germs at the center. The latter retains the correct value at the principal
removable point throughout the open disk.
-/

@[expose] public noncomputable section

open Complex Filter Function Metric NumberField Set
open scoped NNReal Topology

namespace RiemannMasullo.HeckeFiniteZeroTest

open ExpandingTaylor FiniteHardyIdealTable HeckeDiskNormalization HeckeHalfPlaneJensen HeckeLaguerre

variable {F : Type*} [Field F] [NumberField F]
local notation "CF" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual CF
local notation "Hp" => (Complex.re ⁻¹' Ioi (1 : ℝ))

/-- The single polynomial tested at stage `n`, from the actual ordinary finite ideal row. -/
def idealPolynomial (χ : U𝔽) (n : ℕ) : Polynomial ℂ :=
  sectionPoly (row (idealValue χ) (principalIndex χ) (Module.finrank ℚ F) 0) n

/-- Only the ordinary ideal-norm coefficients below the single row's cutoff affect the polynomial. -/
theorem idealPolynomial_eq_of_agree (χ : U𝔽) (n : ℕ) {a : ℕ → ℂ}
    (h : ∀ k < cutoff (Module.finrank ℚ F) (n^3), idealValue χ k = a k) :
    idealPolynomial χ n =
      sectionPoly (row a (principalIndex χ) (Module.finrank ℚ F) 0) n := by
  unfold idealPolynomial sectionPoly
  rw [row_congr (principalIndex χ) (Module.finrank ℚ F) 0 (n^3) h]

private theorem coeff_cleared (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (j : ℕ) :
    DiskFiniteFourier.coeff (clearedDisk χ L) j = DiskFiniteFourier.coeff (ordinaryDisk χ L 0) j := by
  rw [clearedDisk_eq_normalized_zero]
  have hg : normalized χ L 1 0 =ᶠ[𝓝 (0:ℂ)] ordinaryDisk χ L 0 := by
    filter_upwards [closedBall_mem_nhds (0:ℂ) (show 0 < 1/5 by norm_num)] with z hz
    have hz' : ‖z‖ ≤ 1/5 := by simpa using hz
    have h1 : z ≠ 1 := by intro h; norm_num [h] at hz'
    have h2 : ¬(χ = 1 ∧ z = -(1/2)) := by rintro ⟨_, h⟩; norm_num [h] at hz'
    rw [normalized_eq_raw τ hτ χ hχ L hL he 1 0 (by linarith) h1 h2]
    simp only [raw, ordinaryDisk, Complex.ofReal_one, one_mul, diskFactor, principalIndex]
    rfl
  exact congrArg ((j.factorial:ℂ)⁻¹ * ·) (hg.iteratedDeriv_eq j)

private theorem radial_growth (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop, ∀ z, ‖z‖ ≤ outerRadius n → ‖clearedDisk χ L z‖ ≤ C * (n:ℝ)^k := by
  obtain ⟨k, C, _, hC, hb⟩ := cleared_polynomial_bound τ hτ χ hχ L hL he
  refine ⟨C*6^k, k, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn
  intro z hz
  have hx : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hz1 := hz.trans_lt (radius_bounds n hn).2.2.1
  have hgap : 1/(2*(n:ℝ)) ≤ ‖1-z‖ := calc
    _ ≤ 1-‖z‖ := by unfold outerRadius at hz; linarith
    _ ≤ _ := by simpa using norm_sub_norm_le (1:ℂ) z
  have hdr : 0 < ‖1-z‖ := (by positivity : 0<1/(2*(n:ℝ))).trans_le hgap
  have hchart : ‖HalfPlaneJensen.toHalf z + 1‖ ≤ 6*(n:ℝ) := by
    rw [chart_add_one (norm_pos_iff.mp hdr), norm_div]
    norm_num only [Complex.norm_ofNat]
    apply (div_le_iff₀ hdr).mpr
    calc
      (3:ℝ) = 6*(n:ℝ)*(1/(2*(n:ℝ))) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hgap (by positivity)
  calc
    ‖clearedDisk χ L z‖ ≤ C*‖HalfPlaneJensen.toHalf z + 1‖^k :=
      hb _ (HalfPlaneJensen.toHalf_re hz1).le
    _ ≤ C*(6*(n:ℝ))^k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hchart k) (by linarith)
    _ = _ := by rw [mul_pow]; ring

/-- At every sufficiently large stage, or at cofinally many individual stages, zero exclusion
on the entire closed disk is equivalent to absence of positive right divisor sites. -/
theorem isEmpty_rightSite_iff_idealPolynomial_zeroFree
    (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) :
    (IsEmpty (RightSite χ) ↔
      ∀ᶠ n : ℕ in atTop, zeroFreeThrough (idealPolynomial χ n) (radius n)) ∧
    (IsEmpty (RightSite χ) ↔
      ∀ N : ℕ, ∃ n ≥ N, zeroFreeThrough (idealPolynomial χ n) (radius n)) := by
  let L := (finiteHeckeL_exists_continuation χ).choose
  obtain ⟨hL, he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hf := clearedDisk_analytic τ hτ χ hχ L hL he
  have h0 : clearedDisk χ L 0 ≠ 0 := by
    rw [clearedDisk_eq_normalized_zero]
    exact normalized_zero_ne τ hτ χ hχ L hL he (by norm_num) 0
  obtain ⟨C, k, hC, hg⟩ := radial_growth τ hτ χ hχ L hL he
  let u := row (idealValue χ) (principalIndex χ) (Module.finrank ℚ F) 0
  have ha : ∀ᶠ m : ℕ in atTop, ∀ j ≤ m,
      ‖u m j - DiskFiniteFourier.coeff (clearedDisk χ L) j‖ ≤ (1/2:ℝ)^(2*m) := by
    filter_upwards [eventually_row_error τ hτ χ hχ L hL he 0] with m hm
    intro j hj
    rw [coeff_cleared τ hτ χ hχ L hL he j]
    exact hm j hj
  have hsite : IsEmpty (RightSite χ) ↔ ∀ z : ℂ, ‖z‖ < 1 → clearedDisk χ L z ≠ 0 := by
    constructor
    · intro h z hz hzero
      exact h.false ⟨HalfPlaneJensen.toHalf z,
        (clearedDisk_eq_zero_iff τ hτ χ hχ L hL he hz).mp hzero, HalfPlaneJensen.toHalf_re hz⟩
    · intro h
      refine ⟨fun v ↦ h (HalfPlaneJensen.toDisk v.val) (HalfPlaneJensen.toDisk_lt v.property.2) ?_⟩
      apply (clearedDisk_eq_zero_iff τ hτ χ hχ L hL he (HalfPlaneJensen.toDisk_lt v.property.2)).mpr
      rw [HalfPlaneJensen.toHalf_toDisk (HalfPlaneJensen.disk_den v.property.2)]
      exact v.property.1
  obtain ⟨hfull, hcofinal⟩ := zeroFree_iff_sections hf h0 u hC hg ha
  exact ⟨hsite.trans hfull, hsite.trans hcofinal⟩

/-- A positive right site forces a zero on the closed test disk at every sufficiently large stage. -/
theorem eventually_exists_zero_of_rightSite
    (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) (v : RightSite χ) :
    ∀ᶠ n : ℕ in atTop, ∃ z : ℂ, ‖z‖ ≤ radius n ∧ (idealPolynomial χ n).eval z = 0 := by
  have h := (isEmpty_rightSite_iff_idealPolynomial_zeroFree τ hτ χ hχ).2.not.mp
    (fun he ↦ he.false v)
  simp only [zeroFreeThrough, not_forall, not_exists, not_and, not_not, exists_prop] at h
  exact eventually_atTop.2 h

end RiemannMasullo.HeckeFiniteZeroTest
