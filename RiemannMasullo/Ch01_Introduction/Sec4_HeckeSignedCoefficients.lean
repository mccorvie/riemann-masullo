module

public import RiemannMasullo.ForMathlib.Analysis.Complex.NearestZeroGrowth
public import RiemannMasullo.AppB_AnalyticNT.Sec4b_NormalizedHeckeDisk
public import RiemannMasullo.Ch01_Introduction.Sec4_HeckeGreenExterior
import RiemannMasullo.AppB_AnalyticNT.Sec4b
import Mathlib.Tactic

/-! # Signed Taylor measurements of the ordinary Hecke L-function at two

The real Taylor coefficients of the pole-cleared finite Hecke logarithmic derivative detect
the nearest transformed right-hand divisor site. Both signed prefixes yield an ordinary limit.

For the classical Li criterion see J. C. Lagarias, *Li coefficients for automorphic
L-functions*, Theorem 2.4, pp. 1702–1703 (2007). S. Sekatskii, *Generalized Bombieri–Lagarias
theorem and generalized Li criterion*, Theorems 2–3 (arXiv:1304.7895), treats shifted reference
points. A. Voros, *Sharpenings of Li’s criterion for the Riemann hypothesis*, §3
(arXiv:math/0506326), describes the oscillations from the first transformed poles.
The statistics here use the ordinary finite L-function and either accumulated real sign. -/

@[expose] public noncomputable section

open Complex Filter Function Metric NumberField Set
open scoped NNReal Topology

namespace RiemannMasullo.HeckeLaguerre
open HeckeHalfPlaneJensen HalfPlaneJensen HeckeDiskNormalization DiskLogCoefficient SignedFrequency
variable {F : Type*} [Field F] [NumberField F]
local notation "CF" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual CF
local notation "Hp" => (Complex.re ⁻¹' Ioi (1 : ℝ))

/-- The ordinary finite continuation with the principal pole removed in the disk chart. -/
def clearedDisk (χ : U𝔽) (L : ℂ → ℂ) (z : ℂ) : ℂ := cleared χ L (toHalf z)

/-- The disk normalization at exponent zero recovers the cleared function. -/
theorem clearedDisk_eq_normalized_zero (χ : U𝔽) (L : ℂ → ℂ) :
    clearedDisk χ L = normalized χ L 1 0 := by
  ext z
  simp [clearedDisk, normalized]

/-- The principal pole has been removed throughout the open disk. -/
theorem clearedDisk_analytic (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s=finiteHeckeL χ s) :
    AnalyticOnNhd ℂ (clearedDisk χ L) (ball 0 1) := by
  intro z hz
  have hn := mem_ball_zero_iff.mp hz
  exact (cleared_analytic τ hτ χ hχ L hL he (by linarith [toHalf_re hn])).comp (chart_analytic hn)

private theorem pos_order_iff {f : ℂ → ℂ} {s : ℂ} (hf : AnalyticAt ℂ f s)
    (htop : meromorphicOrderAt f s ≠ ⊤) :
    0 < (meromorphicOrderAt f s).untop₀ ↔ f s = 0 := by
  have hp := hf.meromorphicOrderAt_nonneg
  have hzero := hf.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff
  generalize h : meromorphicOrderAt f s=k at htop hp hzero ⊢
  lift k to ℤ using htop with j
  simp only [WithTop.coe_nonneg, WithTop.untop₀_coe, WithTop.coe_eq_zero] at *
  constructor
  · intro hj
    by_contra hn
    have := hzero.mpr hn
    omega
  · intro h0
    have hne : j≠0 := fun hh ↦ (hzero.mp hh) h0
    omega

/-- The ordinary cleared disk zeros are exactly the right-hand positive completed-divisor sites
of the chosen character. In the principal chart the removable point at one is nonzero. -/
theorem clearedDisk_eq_zero_iff (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s=finiteHeckeL χ s) {z : ℂ} (hz : ‖z‖<1) :
    clearedDisk χ L z=0 ↔ 0 < order χ (toHalf z) := by
  classical
  let s := toHalf z
  have hs : 0<s.re := lt_trans (by norm_num : (0:ℝ)<1/2) (toHalf_re hz)
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  change cleared χ L s = 0 ↔ 0 < order χ s
  by_cases h : χ=1 ∧ s=1
  · obtain ⟨rfl,hs1⟩ := h
    rw [hs1]
    have hn := cleared_principal_nonzero L hL he
    have hneg : order (1 : U𝔽) 1 = -1 := (idelicExplicitFormula_trivial_poles (F := F)).2
    simp [hn,hneg]
  have hunit : AnalyticAt ℂ (halfFactor χ) s ∧ halfFactor χ s ≠ 0 := by
    by_cases ht : χ=1
    · have hs1 : s≠1 := fun he ↦ h ⟨ht,he⟩
      rw [show halfFactor χ = (fun w : ℂ ↦ (w-1)/w) by ext w; simp [halfFactor,ht]]
      exact ⟨(show AnalyticAt ℂ (fun w : ℂ ↦ w-1) s by fun_prop).div analyticAt_id hs0,
        div_ne_zero (sub_ne_zero.mpr hs1) hs0⟩
    · rw [show halfFactor χ = (fun _ : ℂ ↦ (1:ℂ)) by ext w; simp [halfFactor,ht]]
      exact ⟨analyticAt_const,one_ne_zero⟩
  have hm := meromorphicNFOn_toMeromorphicNFOn (halfFactor χ * L) univ
  have htwo : cleared χ L 2 ≠ 0 := by
    have h0 := normalized_zero_ne τ hτ χ hχ L hL he (a := 1) (by norm_num) 0
    simpa [normalized, chart_zero, toHalf] using h0
  have ht := hm.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2:ℂ)) (mem_univ s)
    (by rw [(hm (mem_univ (2:ℂ))).meromorphicOrderAt_eq_zero_iff.mpr htwo]; simp)
  have heq : (meromorphicOrderAt (cleared χ L) s).untop₀ = order χ s := by
    rw [cleared, meromorphicOrderAt_toMeromorphicNFOn (meromorphic_product χ L hL) (mem_univ _),
      meromorphicOrderAt_mul_of_ne_zero hunit.1 hunit.2, finite_order_eq_completed χ L hL he s hs,
      order, MeromorphicOn.divisor_apply (explicitFormulaCompletedHeckeL_spec χ).1.meromorphicOn (mem_univ _)]
  exact (pos_order_iff (cleared_analytic τ hτ χ hχ L hL he hs) ht).symm.trans (by rw [heq])

/-- Signed logarithmic Taylor coefficient of the ordinary finite Hecke function in the Euler
germ. The principal pole correction is built into the cleared function. -/
def measuredCoeff (χ : U𝔽) : ℕ → ℝ :=
  signedCoeff (clearedDisk χ (finiteHeckeL_exists_continuation χ).choose)

/-- If a right-hand site exists, both signed prefix rates equal the Green logarithm of the
nearest disk zero, counting the effect of every pole on its radius. -/
theorem signed_rate_measures_nearest (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) (w : RightSite χ) :
    ∃ z : RightSite χ,
      (∀ v : RightSite χ, ‖toDisk z.val‖ ≤ ‖toDisk v.val‖) ∧
      0 < greenKernel z.val ∧
      Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (measuredCoeff χ) N)/(N:ℝ))
        atTop (𝓝 (greenKernel z.val)) ∧
      Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ -measuredCoeff χ n) N)/(N:ℝ))
        atTop (𝓝 (greenKernel z.val)) := by
  let L := (finiteHeckeL_exists_continuation χ).choose
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  let f := clearedDisk χ L
  have ran : f 0 ≠ 0 := by
    rw [show f = normalized χ L 1 0 from clearedDisk_eq_normalized_zero χ L]
    exact normalized_zero_ne τ hτ χ hχ L hL he (by norm_num) 0
  have hreal : ∀ q : ℝ, 0≤q → q<1 → f q ≠ 0 := by
    intro q hq hq1
    rw [show f = normalized χ L 1 0 from clearedDisk_eq_normalized_zero χ L]
    exact radial_normalized_ne_zero_of_nonneg τ hτ χ hχ L hL he (by norm_num) 0 hq hq1
  have hroot (v : RightSite χ) : f (toDisk v.val)=0 :=
    (clearedDisk_eq_zero_iff τ hτ χ hχ L hL he (toDisk_lt v.property.2)).mpr
      (by rw [toHalf_toDisk (disk_den v.property.2)]; exact v.property.1)
  obtain ⟨a,ha0,ha1,hfa,hmin,hp,hn⟩ := exists_nearest_both_prefix_rates
    (clearedDisk_analytic τ hτ χ hχ L hL he) ran hreal _ (toDisk_lt w.property.2) (hroot w)
  let z : RightSite χ := ⟨toHalf a,(clearedDisk_eq_zero_iff τ hτ χ hχ L hL he ha1).mp hfa,toHalf_re ha1⟩
  have hback : toDisk z.val=a := toDisk_toHalf (half_den ha1)
  have hG : greenKernel z.val = Real.log ‖a‖⁻¹ := by
    have hs2 : z.val ≠ 2 := fun h ↦ (ne_of_gt ha0) (by rw [← hback,h]; simp [toDisk])
    rw [← weight_one_eq_green z.property.2 hs2, weight, hback, one_div,
      max_eq_right (Real.log_pos ((one_lt_inv₀ ha0).mpr ha1)).le]
  refine ⟨z,fun v ↦ ?_,hG ▸ Real.log_pos ((one_lt_inv₀ ha0).mpr ha1),hG ▸ hp,hG ▸ hn⟩
  rw [hback]
  exact hmin _ (toDisk_lt v.property.2) (hroot v)

/-- If there are no right-hand divisor sites, both signed prefixes are subexponential. -/
theorem signed_rate_zero_of_empty (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) (hR : IsEmpty (RightSite χ)) :
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (measuredCoeff χ) N)/(N:ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ -measuredCoeff χ n) N)/(N:ℝ))
      atTop (𝓝 0) := by
  let L := (finiteHeckeL_exists_continuation χ).choose
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  apply both_prefix_rate_zero_of_no_roots (clearedDisk_analytic τ hτ χ hχ L hL he)
  intro z hz hzero
  have hzn := mem_ball_zero_iff.mp hz
  exact hR.false ⟨toHalf z,(clearedDisk_eq_zero_iff τ hτ χ hχ L hL he hzn).mp hzero,toHalf_re hzn⟩



/-- A linear error in each ordinary coefficient preserves both signed rates and the cofinal
criterion. The sign can be selected afresh at each cutoff. -/
theorem isEmpty_rightSite_iff_cofinal_signed_of_linear_error
    (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) (y : ℕ → ℝ) {C : ℝ} (hC : 0≤C)
    (herr : ∀ n : ℕ, |y n-measuredCoeff χ n| ≤ C*n) (negative : ℕ → Bool) :
    IsEmpty (RightSite χ) ↔ ∀ ε : ℝ, 0<ε → ∀ J : ℕ, ∃ N ≥ J,
      Real.log (chosenPrefix y negative N)/(N:ℝ) ≤ ε := by
  have hneg (n : ℕ) : |(-y n)-(-measuredCoeff χ n)| ≤ C*n := by
    calc |(-y n)-(-measuredCoeff χ n)| = |-(y n-measuredCoeff χ n)| := by congr 1; ring
         _ = |y n-measuredCoeff χ n| := abs_neg _
         _ ≤ _ := herr n
  have transfer (l : ℝ)
      (hp : Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (measuredCoeff χ) N)/(N:ℝ)) atTop (𝓝 l))
      (hn : Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ -measuredCoeff χ n) N)/(N:ℝ))
        atTop (𝓝 l)) :
      Tendsto (fun N : ℕ ↦ Real.log (chosenPrefix y negative N)/(N:ℝ)) atTop (𝓝 l) :=
    tendsto_chosenPrefix negative (tendsto_log_prefix_of_linear_error hC herr hp)
      (tendsto_log_prefix_of_linear_error hC hneg hn)
  constructor
  · intro hempty
    obtain ⟨hp,hn⟩ := signed_rate_zero_of_empty τ hτ χ hχ hempty
    exact cofinalUpperZero_of_tendsto (transfer 0 hp hn)
  · intro h
    refine ⟨fun w ↦ ?_⟩
    obtain ⟨z,_,hpos,hp,hn⟩ := signed_rate_measures_nearest τ hτ χ hχ w
    exact not_cofinalUpperZero_of_positive_limit hpos (transfer _ hp hn) h

/-- For the exact logarithmic coefficients, subexponential signed prefix growth on one cofinal
set of integer cutoffs characterizes the absence of right-half-plane sites. -/
theorem isEmpty_rightSite_iff_cofinal_signed (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) (negative : ℕ → Bool) :
    IsEmpty (RightSite χ) ↔ ∀ ε : ℝ, 0<ε → ∀ J : ℕ, ∃ N ≥ J,
      Real.log (chosenPrefix (measuredCoeff χ) negative N)/(N:ℝ) ≤ ε :=
  isEmpty_rightSite_iff_cofinal_signed_of_linear_error τ hτ χ hχ _ (C:=0) le_rfl
    (fun _ ↦ by simp) negative

/-- Same-character reflection also excludes sites on the left of the critical line. -/
theorem isEmpty_rightSite_iff_central (χ : U𝔽) :
    IsEmpty (RightSite χ) ↔ ∀ z : HeckePoisson.Site χ, z.val.re=1/2 := by
  constructor
  · intro h
    let _ := h
    apply (HeckePoisson.rightGreenMass_eq_zero_iff χ).mp
    simp [HeckePoisson.rightGreenMass]
  · intro h
    refine ⟨fun w ↦ ?_⟩
    exact (h ⟨w.val,w.property.1⟩ ▸ w.property.2).false



end RiemannMasullo.HeckeLaguerre
