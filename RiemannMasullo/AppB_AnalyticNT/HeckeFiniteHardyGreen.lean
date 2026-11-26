module

public import RiemannMasullo.ForMathlib.Analysis.Complex.SzegoDistance
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.HardyPolynomialGrid
public import RiemannMasullo.ForMathlib.Analysis.Complex.DiskCoefficientEnergy
public import RiemannMasullo.AppB_AnalyticNT.Sec4b_BoundaryHeckeGreen
public import RiemannMasullo.AppB_AnalyticNT.FiniteHardyIdealTable
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RiemannMasullo.AppB_AnalyticNT.Sec1

/-!
# One-sided finite-ideal measurements of the Hecke boundary logarithm

Use the finite ideal Fourier rows for the Cayley disk centered at `s = 2`. The scalar
normalization is one. For every sufficiently large fixed integer exponent the analytic
derivative bound is `16 / 9`, and the logarithmic gap is the pole-corrected boundary
difference. Correcting the finite least-squares residual by its entry error and its
unseen coefficient tail gives an eventual upper bound converging to that difference.

The exponent threshold and the onset of the unit dyadic error bound may depend on the
character. At a specified stage, certified complex entries and any feasible polynomial
give an upper bound with the stated norm error. The assertion for rounded inputs
explicitly includes their extra error.
-/

@[expose] public noncomputable section

open Complex Filter Function IsDedekindDomain Metric NumberField Set
open scoped NNReal Topology Asymptotics

namespace RiemannMasullo.HeckeHardyDisk

variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽
local notation "Hp" => (Complex.re ⁻¹' Ioi (1 : ℝ))

open HalfPlaneJensen HeckeDiskNormalization DiskCoefficientEnergy

private theorem quarter_factor_bound (χ : U𝔽) {s : ℂ} (hs : 1/4 ≤ s.re) : ‖halfFactor χ s‖ ≤ 5 := by
  classical
  have hnorm : 1/4 ≤ ‖s‖ := hs.trans (Complex.re_le_norm _)
  by_cases hc : χ = 1
  · rw [halfFactor, ite_eq_left hc, norm_div, div_le_iff₀ (by linarith : 0 < ‖s‖)]
    have h := norm_sub_le s (1:ℂ)
    rw [norm_one] at h
    linarith
  · simp [halfFactor, hc]

/-- A polynomial growth bound for the pole-cleared continuation on the larger half-plane. -/
theorem quarter_polynomial_bound (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    ∃ (M : ℕ) (K : ℝ), 1 ≤ K ∧ ∀ s : ℂ, 1/4 ≤ s.re → ‖cleared χ L s‖ ≤ K * ‖s + 1‖^M := by
  obtain ⟨m, B, _, hB, hright⟩ := cleared_polynomial_bound τ hτ χ hχ L hL he
  let S := Icc (1/4 : ℝ) (1/2)
  let ℓ := comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' S)
  obtain ⟨E, hE, hO⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hL he (1/4) (1/2) (by norm_num)
  have hsmall : cleared χ L =O[ℓ] L := by
    refine Asymptotics.IsBigO.of_bound 5 ?_
    have hin : ∀ᶠ s : ℂ in ℓ, s.re∈S := eventually_inf_principal.mpr (Eventually.of_forall fun s hs ↦ hs)
    filter_upwards [hin] with s hs
    have hns : s ≠ 1 := by intro h; have := hs.2; norm_num [h] at this
    rw [cleared_agrees τ hτ χ hχ L hL he (by linarith [hs.1]) (fun h ↦ hns h.2), norm_mul]
    exact mul_le_mul_of_nonneg_right (quarter_factor_bound χ hs.1) (norm_nonneg _)
  have hcont : ContinuousOn (cleared χ L) (Complex.re ⁻¹' S) :=
    fun s hs ↦ (cleared_analytic τ hτ χ hχ L hL he (by linarith [hs.1])).continuousAt.continuousWithinAt
  obtain ⟨C, hC, hstrip⟩ := exists_norm_le_mul_norm_sub_rpow (K:=S) isCompact_Icc hcont hE.le
    (hsmall.trans hO) (x0 := -1) (fun σ hσ ↦ by linarith [hσ.1])
  obtain ⟨n, hn⟩ := exists_nat_ge E
  let M := max n m
  let K := max C B
  have hK : 1 ≤ K := hB.trans (le_max_right _ _)
  refine ⟨M, K, hK, fun s hs ↦ ?_⟩
  have hx : 1 ≤ ‖s + 1‖ := calc
    1 ≤ (s + 1).re := by simp; linarith
    _ ≤ ‖s + 1‖ := Complex.re_le_norm _
  by_cases ht : 1/2 ≤ s.re
  · have hm : m ≤ M := le_max_right _ _
    exact (hright s ht).trans (mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hx hm)
      (by positivity) (by linarith))
  · have h := hstrip s ⟨hs, le_of_not_ge ht⟩
    simp only [ofReal_neg, ofReal_one, sub_neg_eq_add] at h
    have hm : n ≤ M := le_max_left _ _
    have hp : ‖s + 1‖^E ≤ ‖s + 1‖^M := by
      rw [←Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hx (hn.trans (by exact_mod_cast hm))
    exact h.trans (mul_le_mul (le_max_left _ _) hp (Real.rpow_nonneg (norm_nonneg _) _) (by linarith))

/-- Divide the pole-cleared continuation by a power of s + 1 in half-plane coordinates. -/
def halfNormalized (χ : U𝔽) (L : ℂ → ℂ) (a : ℝ) (M : ℕ) (s : ℂ) : ℂ :=
  (a:ℂ) * (s + 1)⁻¹^M * cleared χ L s

theorem halfNormalized_analytic (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (a : ℝ) (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (halfNormalized χ L a M) s := by
  have hne : s + 1 ≠ 0 := fun h ↦ by have := congrArg Complex.re h; simp at this; linarith
  have hA : AnalyticAt ℂ (fun s : ℂ ↦ (a:ℂ) * (s + 1)⁻¹^M) s := by fun_prop (disch := assumption)
  exact hA.mul (cleared_analytic τ hτ χ hχ L hL he hs)

theorem halfNormalized_bound {χ : U𝔽} {L : ℂ → ℂ} {K : ℝ} {M : ℕ} (hK : 1 ≤ K)
    (hP : ∀ s : ℂ, 1/4 ≤ s.re → ‖cleared χ L s‖ ≤ K * ‖s + 1‖^M) {s : ℂ} (hs : 1/4 ≤ s.re) :
    ‖halfNormalized χ L K⁻¹ M s‖ ≤ 1 := by
  have hκ : 0 < K := by linarith
  have hne : s + 1 ≠ 0 := fun h ↦ by have := congrArg Complex.re h; simp at this; linarith
  have hin : 0 < ‖s + 1‖ := norm_pos_iff.mpr hne
  rw [halfNormalized, norm_mul, norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hκ)]
  calc K⁻¹ * ‖s + 1‖⁻¹^M * ‖cleared χ L s‖ ≤ K⁻¹ * ‖s + 1‖⁻¹^M * (K*‖s + 1‖^M) := by
         gcongr
         exact hP s hs
     _ = (K⁻¹*K) * (‖s + 1‖⁻¹*‖s + 1‖)^M := by rw [mul_pow]; ring
     _ = 1 := by rw [inv_mul_cancel₀ hκ.ne', inv_mul_cancel₀ hin.ne', one_pow, one_mul]

private theorem quarter_disk {s w : ℂ} (hs : 1/2 ≤ s.re) (hw : w∈closedBall s (1/4)) : 1/4 ≤ w.re := by
  have h : ‖s - w‖ ≤ 1/4 := by simpa [Metric.mem_closedBall, dist_eq_norm'] using hw
  have hh := Complex.re_le_norm (s - w)
  rw [Complex.sub_re] at hh
  linarith

theorem halfNormalized_deriv_bound (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {K : ℝ} {M : ℕ} (hK : 1 ≤ K)
    (hP : ∀ s : ℂ, 1/4 ≤ s.re → ‖cleared χ L s‖ ≤ K * ‖s + 1‖^M) {s : ℂ} (hs : 1/2 ≤ s.re) :
    ‖deriv (halfNormalized χ L K⁻¹ M) s‖ ≤ 4 := by
  have hA : DifferentiableOn ℂ (halfNormalized χ L K⁻¹ M) (closedBall s (1/4)) :=
    fun w hw ↦ (halfNormalized_analytic τ hτ χ hχ L hL he K⁻¹ M (by linarith [quarter_disk hs hw])).differentiableAt.differentiableWithinAt
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f:=halfNormalized χ L K⁻¹ M)
    (C:=(1:ℝ)) (by norm_num : (0:ℝ)<1/4) (hA.diffContOnCl_ball Subset.rfl)
    (fun w hw ↦ halfNormalized_bound hK hP (quarter_disk hs (sphere_subset_closedBall hw)))
  norm_num at h
  exact h

theorem chart_two_powers (χ : U𝔽) (L : ℂ → ℂ) (a : ℝ) (M : ℕ) {z : ℂ} (hz : z ≠ 1) :
    normalized χ L a (M + 2) z = ((1 - z)/3)^2 * halfNormalized χ L a M (toHalf z) := by
  rw [normalized, halfNormalized, chart_add_one (sub_ne_zero.mpr hz.symm), inv_div, pow_add]
  ring

theorem normalized_deriv_bound (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {K : ℝ} {M : ℕ} (hK : 1 ≤ K)
    (hP : ∀ s : ℂ, 1/4 ≤ s.re → ‖cleared χ L s‖ ≤ K * ‖s + 1‖^M)
    {z : ℂ} (hz : ‖z‖ ≤ 1) (h1 : z ≠ 1) : ‖deriv (normalized χ L K⁻¹ (M + 2)) z‖ ≤ 16/9 := by
  let H := halfNormalized χ L K⁻¹ M
  have hs := closed_chart_re hz h1
  have hn := sub_ne_zero.mpr h1.symm
  have hH : HasDerivAt H (deriv H (toHalf z)) (toHalf z) :=
    (halfNormalized_analytic τ hτ χ hχ L hL he _ _ (by linarith)).differentiableAt.hasDerivAt
  have hlin : HasDerivAt (fun u : ℂ ↦ (1 - u)/3) (-(1/3)) z := by
    have h : HasDerivAt (fun u : ℂ ↦ (1 - u)/3) ((0-1)/3) z :=
      ((hasDerivAt_const z (1:ℂ)).sub (hasDerivAt_id z)).div_const 3
    convert h using 1
    norm_num [div_eq_mul_inv]
  have heq : normalized χ L K⁻¹ (M + 2) =ᶠ[𝓝 z] (fun u : ℂ ↦ ((1 - u)/3)^2 * H (toHalf u)) :=
    (eventually_ne_nhds h1).mono fun u hu ↦ chart_two_powers χ L K⁻¹ M hu
  have hder := ((hlin.pow 2).mul (hH.comp z (chart_hasDerivAt hn))).congr_of_eventuallyEq heq
  have hformula : deriv (normalized χ L K⁻¹ (M + 2)) z =
      -(2/9:ℂ)*(1 - z)*H (toHalf z) + (1/3:ℂ)*deriv H (toHalf z) := by
    rw [hder.deriv]
    simp only [Function.comp_apply, Pi.pow_apply]
    field_simp
    ring
  have htop : ‖H (toHalf z)‖ ≤ 1 := halfNormalized_bound hK hP (by linarith)
  have htop' : ‖deriv H (toHalf z)‖ ≤ 4 := halfNormalized_deriv_bound τ hτ χ hχ L hL he hK hP hs
  have hz2 : ‖1 - z‖ ≤ 2 := (norm_sub_le (1:ℂ) z).trans (by rw [norm_one]; linarith)
  rw [hformula]
  calc ‖-(2/9:ℂ)*(1 - z)*H (toHalf z) + (1/3:ℂ)*deriv H (toHalf z)‖
      ≤ ‖-(2/9:ℂ)*(1 - z)*H (toHalf z)‖ + ‖(1/3:ℂ)*deriv H (toHalf z)‖ := norm_add_le _ _
    _ ≤ (2/9)*2*1+(1/3)*4 := by
      simp only [norm_mul, norm_neg, norm_div, Complex.norm_ofNat, norm_one]
      gcongr
    _ = 16/9 := by norm_num

/-- Every actual normalized finite Hecke L-function admits a bounded disk model with bounded derivative. -/
theorem exists_normalized_deriv (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      (∀ z : ℂ, ‖z‖ ≤ 1 → ‖normalized χ L 1 N z‖ ≤ 1) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 → ‖deriv (normalized χ L 1 N) z‖ ≤ 16/9) := by
  obtain ⟨m, K,_, hP⟩ := quarter_polynomial_bound τ hτ χ hχ L hL he
  obtain ⟨j, hj⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (5/4:ℝ))).eventually_gt_atTop K).exists
  have hQ {M : ℕ} (hM : m+j ≤ M) {s : ℂ} (hs : 1/4 ≤ s.re) :
      ‖cleared χ L s‖ ≤ (1:ℝ)*‖s + 1‖^M := by
    have hx : 5/4 ≤ ‖s + 1‖ := calc
      5/4 ≤ (s + 1).re := by simp; linarith
      _ ≤ ‖s + 1‖ := Complex.re_le_norm _
    have hK : K ≤ ‖s + 1‖^j := hj.le.trans (pow_le_pow_left₀ (by norm_num) hx j)
    rw [one_mul]
    calc ‖cleared χ L s‖ ≤ K * ‖s + 1‖^m := hP _ hs
      _ ≤ ‖s + 1‖^j * ‖s + 1‖^m := mul_le_mul_of_nonneg_right hK (by positivity)
      _ ≤ ‖s + 1‖^M := by rw [mul_comm,←pow_add]; exact pow_le_pow_right₀ (by linarith) hM
  refine ⟨m+j+2, by omega, fun N hN ↦ ?_⟩
  constructor
  · intro z hz
    simpa only [inv_one] using normalized_bound (χ:=χ) (L:=L) (N:=N) (K:=1) (by omega)
      le_rfl (fun s hs ↦ hQ (by omega) (by linarith)) hz
  · intro z hz h1
    let M := N-2
    have heq : M + 2=N := by dsimp [M]; omega
    simpa only [inv_one, heq] using normalized_deriv_bound τ hτ χ hχ L hL he (K:=1) (M:=M)
      le_rfl (fun s hs ↦ hQ (by dsimp [M]; omega) hs) hz h1

/-- All estimates refer to the actual holomorphic function and its derivatives at the origin. -/
structure HardyControl (f : ℂ → ℂ) : Prop where
  norm_le : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f z‖ ≤ 1
  deriv_le : ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 → ‖deriv f z‖ ≤ 16/9
  nonzero_center : f 0 ≠ 0
  expansion : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun j ↦ coeff f j * z^j) (f z)
  energy_summable : Summable (fun j : ℕ ↦ (j:ℝ)^2 * ‖coeff f j‖^2)
  energy_le : ∑' j : ℕ, (j:ℝ)^2 * ‖coeff f j‖^2 ≤ (16/9:ℝ)^2

/-- With the scalar fixed at one, every sufficiently large integer exponent gives the same derivative
bound and a matching derivative-weighted Taylor coefficient bound. -/
theorem exists_hardy_control (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, HardyControl (normalized χ L 1 N) := by
  obtain ⟨N₀, hN₀, h⟩ := exists_normalized_deriv τ hτ χ hχ L hL he
  refine ⟨N₀, hN₀, fun N hN ↦ ?_⟩
  let f := normalized χ L 1 N
  have h1 {z : ℂ} (hz : ‖z‖ < 1) : z ≠ 1 := fun e ↦ by simp [e] at hz
  have hA : AnalyticOnNhd ℂ f (ball 0 1) := by
    intro z hz
    have hzn : ‖z‖ < 1 := by simpa using hz
    exact normalized_analytic τ hτ χ hχ L hL he 1 N hzn.le (h1 hzn)
  obtain ⟨hb, hd⟩ := h N hN
  have henergy := derivative_energy (f := f) hA (by norm_num : (0:ℝ)≤16/9)
    (fun z hz ↦ hd z hz.le (h1 hz))
  refine ⟨hb, hd, normalized_zero_ne τ hτ χ hχ L hL he (by norm_num) N,
    fun z hz ↦ hasSum_coeff hA.differentiableOn hz, henergy.1, henergy.2⟩

/-- The canonical finite Hecke continuation has the scalar-one Hardy control without any
arithmetic bound as a hypothesis. -/
theorem canonical_hardy_control (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) :
    let L := (finiteHeckeL_exists_continuation χ).choose
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, HardyControl (normalized χ L 1 N) := by
  intro L
  obtain ⟨hL, he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  exact exists_hardy_control τ hτ χ hχ L hL he

end RiemannMasullo.HeckeHardyDisk

end

@[expose] public noncomputable section

open Complex Filter Function IsDedekindDomain Metric NumberField Set
open scoped NNReal Topology

namespace RiemannMasullo.FiniteHardyIdealTable
open HeckeHardyDisk HeckeDiskNormalization
variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽
local notation "Hp" => Complex.re ⁻¹' Ioi (1 : ℝ)

theorem coeff_normalized_eq (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (N j : ℕ) :
    DiskCoefficientEnergy.coeff (normalized χ L 1 N) j =
      DiskFiniteFourier.coeff (ordinaryDisk χ L N) j := by
  have h : normalized χ L 1 N =ᶠ[𝓝 (0:ℂ)] ordinaryDisk χ L N := by
    filter_upwards [Metric.closedBall_mem_nhds (0:ℂ) (show 0<1/5 by norm_num)] with z hz
    have hz' : ‖z‖≤1/5 := by simpa using hz
    have h1 : z ≠ 1 := by intro e;norm_num [e] at hz'
    have h2 : ¬(χ=1 ∧ z= -(1/2)) := by rintro ⟨_,e⟩;norm_num [e] at hz'
    rw [normalized_eq_raw τ hτ χ hχ L hL he 1 N (by linarith) h1 h2]
    simp only [raw,ordinaryDisk,Complex.ofReal_one,one_mul,diskFactor,principalIndex]
    rfl
  exact congrArg ((j.factorial : ℂ)⁻¹ * ·) (h.iteratedDeriv_eq j)

def linearRow (χ : U𝔽) (N n : ℕ) (j : Fin (HardyTable.linearCut n+1)) : ℂ :=
  row (idealValue χ) (principalIndex χ) (Module.finrank ℚ F) N (HardyTable.linearCut n) j

theorem canonical_polynomial_ideal_HardyTable (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) :
    let L := (finiteHeckeL_exists_continuation χ).choose
    ∃ N₀ : ℕ, 2≤N₀ ∧ ∀ N≥N₀, ∃ c : HardyTable.H,
      (∀ j, c j=DiskCoefficientEnergy.coeff (normalized χ L 1 N) j) ∧
      HardyTable.DerivativeBound c (16/9) ∧
      (∃ C : ℝ, 0≤C ∧ ∀ n (j : Fin (HardyTable.linearCut n+1)),
        ‖linearRow χ N n j-c j‖ ≤ C*(1/2:ℝ)^(2*HardyTable.linearCut n)) ∧
      Tendsto (fun n ↦ HardyTable.leastSquares (HardyTable.linearCut n)
        (HardyTable.extendRow (linearRow χ N n)) (HardyTable.ellipsoid n)) atTop (𝓝 ((HardyTable.distance c)^2)) := by
  intro L
  obtain ⟨N₀,hN₀,h⟩ := canonical_hardy_control τ hτ χ hχ
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  refine ⟨N₀,hN₀,fun N hN ↦ ?_⟩
  let f := normalized χ L 1 N
  let c := HardyTable.ofDerivative (DiskCoefficientEnergy.coeff f) (h N hN).energy_summable
  have hD : HardyTable.DerivativeBound c (16/9) :=
    HardyTable.bound_ofDerivative _ (by norm_num) (h N hN).energy_summable (h N hN).energy_le
  obtain ⟨C,hC,hE⟩ := (canonical_finite_ideal_coefficients τ hτ χ hχ N).2
  have hrow (n : ℕ) (j : Fin (HardyTable.linearCut n+1)) :
      ‖linearRow χ N n j-c j‖ ≤ C*(1/2:ℝ)^(2*HardyTable.linearCut n) := by
    change ‖_ - DiskCoefficientEnergy.coeff f j‖ ≤ _
    rw [show DiskCoefficientEnergy.coeff f j = _ from coeff_normalized_eq τ hτ χ hχ L hL he N j]
    exact hE _ _ (by omega)
  refine ⟨c,fun _ ↦ rfl,hD,⟨C,hC,hrow⟩,?_⟩
  apply HardyTable.linear_finiteRows_tendsto hD hC
  intro n j
  exact (hrow n j).trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hC)

end RiemannMasullo.FiniteHardyIdealTable

end

@[expose] public noncomputable section

open Complex Filter Function IsDedekindDomain MeasureTheory Metric NumberField Set
open scoped NNReal Topology

namespace RiemannMasullo.HeckeHardyGreen

variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽
local notation "Hp" => Complex.re ⁻¹' Ioi (1 : ℝ)
open HeckeDiskNormalization HeckeBoundaryGreen HalfPlaneJensen HeckeHalfPlaneJensen HeckeHardyDisk

open scoped Classical in
private theorem center_log (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {a : ℝ} (ha : 0 < a) (N : ℕ) :
    Real.log ‖normalized χ L a N 0‖ = Real.log a - (N:ℝ)*Real.log 3 +
      Real.log ‖L 2‖ - (if χ = 1 then Real.log 2 else 0) := by
  have h2 : L 2 ≠ 0 := (he ⟨2,by norm_num⟩).trans_ne (finiteHeckeL_ne_zero_of_one_lt_re χ ⟨2,by norm_num⟩)
  have hfac : ‖diskFactor χ 0‖ ≠ 0 := by
    by_cases hh : χ = 1 <;> norm_num [diskFactor,hh]
  have hlog : Real.log ‖diskFactor χ 0‖ = -(if χ = 1 then Real.log 2 else 0) := by
    by_cases hh : χ = 1 <;> simp [diskFactor,hh,one_div,norm_inv,Real.log_inv]
  have h3 : (1/3:ℝ)^N ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [normalized_at_zero τ hτ χ hχ L hL he a N]
  simp only [norm_mul,norm_pow,norm_div,norm_one,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha]
  rw [Real.log_mul (mul_ne_zero (mul_ne_zero ha.ne' h3) hfac) (norm_ne_zero_iff.mpr h2),
    Real.log_mul (mul_ne_zero ha.ne' h3) hfac,Real.log_mul ha.ne' h3,
    Real.log_pow,Real.log_div one_ne_zero (by norm_num : (3:ℝ)≠0),Real.log_one,hlog]
  ring

open scoped Classical in
/-- Positive rescaling and every power of the chart factor leave the logarithmic gap equal to the
physical critical-line integral with its Euler reference and the principal correction at two. -/
theorem normalized_logGap (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {a : ℝ} (ha : 0 < a) (N : ℕ) :
    HardyBoundary.logGap (normalized χ L a N) =
      (∫ t : ℝ, weightedLog L t)-Real.log ‖L 2‖+(if χ=1 then Real.log 2 else 0) := by
  have hline : CircleIntegrable (fun z ↦ Real.log ‖L (toHalf z)‖) 0 1 :=
    (CayleyCauchy.circleIntegrable_two_add_div_one_sub_iff (fun s : ℂ ↦ Real.log ‖L s‖)).mpr
      (integrable_weightedLog_and_green τ hτ χ hχ L hL he).1
  obtain ⟨hcor,_⟩ := correction_mean χ a N (r:=1) (by norm_num) le_rfl
  have hang := normalized_log_ae τ hτ χ hχ L hL he ha N (r:=1) (by norm_num) le_rfl
  have hi : CircleIntegrable (fun z ↦ Real.log ‖normalized χ L a N z‖) 0 1 :=
    IntervalIntegrable.congr_ae (hcor.add hline) (ae_restrict_of_ae (hang.mono fun _ h ↦ h.symm))
  have hmean := (strip_mean τ hτ χ hχ L hL he ha N (r:=1) (by norm_num) le_rfl hi).2
  have hchange : circleMean L 1 = ∫ t : ℝ, weightedLog L t :=
    CayleyCauchy.circleAverage_two_add_div_one_sub (fun s : ℂ ↦ Real.log ‖L s‖)
  simp only [Real.log_one,ite_self,add_zero] at hmean
  rw [HardyBoundary.logGap,center_log τ hτ χ hχ L hL he ha N,←hchange]
  linarith

/-- The exact boundary gap identity on the same canonical scalar-one function used for the
actual factorial-normalized Taylor coefficient row. It holds at every exponent. -/
theorem canonical_logGap (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) (N : ℕ) :
    HardyBoundary.logGap (normalized χ (finiteHeckeL_exists_continuation χ).choose 1 N) =
      criticalLogDifference χ := by
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  exact normalized_logGap τ hτ χ hχ _ hL he (by norm_num) N

/-- One further chart factor turns a bounded model into a disk-algebra function at the point
representing infinity. Its definition already takes the value zero there. -/
theorem normalized_succ_diskAlgebra (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (N : ℕ)
    (hb : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖normalized χ L 1 N z‖ ≤ 1) :
    DiffContOnCl ℂ (normalized χ L 1 (N+1)) (ball 0 1) := by
  have hA z hz h1 := normalized_analytic τ hτ χ hχ L hL he 1 (N+1) (z:=z) hz h1
  constructor
  · intro z hz
    have hn : ‖z‖ < 1 := by simpa using hz
    exact (hA z hn.le (by rintro rfl; simp at hn)).differentiableAt.differentiableWithinAt
  rw [closure_ball _ one_ne_zero]
  intro z hz
  have hn : ‖z‖ ≤ 1 := by simpa using hz
  by_cases h1 : z = 1
  · subst z
    have hzero : normalized χ L 1 (N+1) 1 = 0 := by simp [normalized]
    have hlim : Tendsto (fun z : ℂ ↦ ‖(1-z)/3‖) (𝓝[closedBall 0 1] 1) (𝓝 0) := by
      have hcont : Continuous (fun z : ℂ ↦ ‖(1-z)/3‖) := by fun_prop
      simpa using (hcont.continuousAt (x:=1)).continuousWithinAt (s:=closedBall 0 1) |>.tendsto
    rw [ContinuousWithinAt,hzero,tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) _ hlim
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hfactor : normalized χ L 1 (N+1) w = ((1-w)/3)*normalized χ L 1 N w := by
      simp only [normalized,pow_succ]; ring
    rw [hfactor,norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hb w (by simpa using hw))
  · exact (hA z hn h1).continuousAt.continuousWithinAt

/-- All sufficiently large scalar-one model exponents have both the physical analytic control
and a literal continuous extension to their existing value at the exceptional boundary point. -/
theorem canonical_diskAlgebra_control (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) :
    let L := (finiteHeckeL_exists_continuation χ).choose
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      DiffContOnCl ℂ (normalized χ L 1 N) (ball 0 1) ∧ HardyControl (normalized χ L 1 N) := by
  intro L
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  obtain ⟨N₀,hN₀,h⟩ := canonical_hardy_control τ hτ χ hχ
  refine ⟨N₀+1,by omega,fun N hN ↦ ⟨?_,h N (by omega)⟩⟩
  have heq : N-1+1=N := by omega
  rw [←heq]
  exact normalized_succ_diskAlgebra τ hτ χ hχ L hL he (N-1) (h (N-1) (by omega)).norm_le

end RiemannMasullo.HeckeHardyGreen

end

@[expose] public noncomputable section

open Complex Filter Function IsDedekindDomain MeasureTheory Metric NumberField Set HardyTable
open scoped NNReal Topology

namespace RiemannMasullo.HeckeHardyGreen

variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽
open HeckeDiskNormalization HeckeBoundaryGreen HeckeHardyDisk FiniteHardyIdealTable

/-- Measured squared residual of one finite vector of 2n+2 complex entries. -/
def rowResidual {n : ℕ} (a : Fin (linearCut n+1) → ℂ) : ℝ :=
  leastSquares (linearCut n) (extendRow a) (ellipsoid n)

/-- The squared residual computed from the finite ideal data of χ. -/
def idealResidual (χ : U𝔽) (N n : ℕ) : ℝ := rowResidual (linearRow χ N n)

/-- The visible perturbation from a uniform row error ε, plus the hidden Hardy tail at 16/9. -/
def rowError (n : ℕ) (ε : ℝ) : ℝ :=
  2*Real.sqrt (((n:ℝ)+1)*((linearCut n:ℝ)+1))*ε + 2*(16/9)/Real.sqrt ((n:ℝ)+1)

private theorem distance_le_row {c : H} (hD : DerivativeBound c (16/9)) (n : ℕ)
    (a : Fin (linearCut n+1) → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (ha : ∀ j : Fin (linearCut n+1), ‖a j-c j‖ ≤ ε) :
    (distance c)^2 ≤ (Real.sqrt (rowResidual a)+rowError n ε)^2 := by
  obtain ⟨p,hp,hmin,_⟩ := exists_leastSquares (M:=linearCut n) (extendRow a) (ellipsoid_compact n) (ellipsoid_nonempty n)
  have hhidden := (ellipsoid_errors (C:=0) (a:=fun _ j ↦ c j) hD le_rfl (by simp [Accurate]) n p hp).1
  have hone := (coeffOneNorm_le_weighted p).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hp) (by norm_num))
  have herr0 := visible_perturb_le (M:=linearCut n) (b:=fun j ↦ c j) (a:=extendRow a) hε
    (fun j hj ↦ by simpa only [extendRow,dite_eq_left (Nat.lt_succ_of_le hj)] using ha ⟨j,Nat.lt_succ_of_le hj⟩) p
  have herr : ‖visible (linearCut n) (extendRow a) p-visible (linearCut n) c p‖ ≤
      2*Real.sqrt (((n:ℝ)+1)*((linearCut n:ℝ)+1))*ε := by
    refine herr0.trans ?_
    rw [Real.sqrt_mul (by positivity : 0 ≤ (n:ℝ)+1)]
    calc
      _ ≤ Real.sqrt ((linearCut n:ℝ)+1) * (2*Real.sqrt ((n:ℝ)+1)*ε) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hone hε) (by positivity)
      _ = _ := by ring
  have hdiff := (abs_norm_sub_norm_le (visible (linearCut n) (extendRow a) p) (visible (linearCut n) c p)).trans herr
  rw [visible_eq_head,abs_le] at hdiff
  have hsplit := le_head_add_tail (unitVector-product c p) (linearCut n)
  have hnorm : ‖unitVector-product c p‖ ≤ ‖visible (linearCut n) (extendRow a) p‖+rowError n ε := by
    dsimp [rowError];linarith
  have hm : product c p ∈ closure (multiples c) := subset_closure ⟨n,p,rfl⟩
  have hd : distance c ≤ ‖unitVector-product c p‖ := by
    simpa only [distance,dist_eq_norm] using Metric.infDist_le_dist_of_mem hm (x:=unitVector)
  rw [rowResidual,hmin,Real.sqrt_sq (norm_nonneg _)]
  exact pow_le_pow_left₀ Metric.infDist_nonneg (hd.trans hnorm) 2

/-- A character-dependent choice of a sufficiently large fixed integer exponent.
It uses the two unconditional thresholds for the physical disk and the actual ideal rows. -/
def tableExponent (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) : ℕ :=
  max (canonical_diskAlgebra_control τ hτ χ hχ).choose (canonical_polynomial_ideal_HardyTable τ hτ χ hχ).choose

/-- The finite ideal rows converge to the exact exponential transform of the genuine Hecke
boundary difference. No numerical coefficient hypothesis is required. -/
theorem idealResidual_tendsto (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) {N : ℕ} (hN : tableExponent τ hτ χ hχ ≤ N) :
    Tendsto (idealResidual χ N) atTop (𝓝 (1-Real.exp (-2*criticalLogDifference χ))) := by
  obtain ⟨hf,hc⟩ := (canonical_diskAlgebra_control τ hτ χ hχ).choose_spec.2 N ((le_max_left _ _).trans hN)
  obtain ⟨c,hcoeff,_,_,ht⟩ :=
    (canonical_polynomial_ideal_HardyTable τ hτ χ hχ).choose_spec.2 N ((le_max_right _ _).trans hN)
  have he := HardySzego.distance_sq_of_coefficients hf hc.nonzero_center hcoeff
  rw [canonical_logGap τ hτ χ hχ N] at he
  exact he ▸ ht

/-- A single observed row with a certified uniform entry error bounds the physical Green
mass when its squared residual plus the stated norm error gives an upper bound V below one. -/
theorem measured_row_upper (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) {N : ℕ} (hN : tableExponent τ hτ χ hχ ≤ N)
    (n : ℕ) (a : Fin (linearCut n+1) → ℂ) {ε V : ℝ} (hε : 0 ≤ ε)
    (ha : ∀ j : Fin (linearCut n+1), ‖a j-
      DiskCoefficientEnergy.coeff (normalized χ (finiteHeckeL_exists_continuation χ).choose 1 N) j‖ ≤ ε)
    (hVrow : (Real.sqrt (rowResidual a)+rowError n ε)^2 ≤ V) (hV : V < 1) :
    criticalLogDifference χ ≤ -Real.log (1-V)/2 := by
  obtain ⟨hf,hc⟩ := (canonical_diskAlgebra_control τ hτ χ hχ).choose_spec.2 N ((le_max_left _ _).trans hN)
  let c := ofDerivative _ hc.energy_summable
  have hD : DerivativeBound c (16/9) := bound_ofDerivative _ (by norm_num) hc.energy_summable hc.energy_le
  have hlow := (HardyBoundary.distance_lower_of_coefficients (c:=c) hf hc.nonzero_center hD (fun _ ↦ rfl)).2
  rw [canonical_logGap τ hτ χ hχ N] at hlow
  exact HardyBoundary.logGap_le_log_of_upper ((hlow.trans (distance_le_row hD n a hε ha)).trans hVrow) hV

/-- A feasible polynomial already certifies a finite upper bound. Its visible norm is a
finite sum in the supplied row entries; computing the constrained minimum is optional. -/
theorem measured_trial_upper (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) {N : ℕ} (hN : tableExponent τ hτ χ hχ ≤ N)
    (n : ℕ) (a : Fin (linearCut n + 1) → ℂ) {ε V : ℝ} (hε : 0 ≤ ε)
    (ha : ∀ j : Fin (linearCut n + 1), ‖a j - DiskCoefficientEnergy.coeff
      (normalized χ (finiteHeckeL_exists_continuation χ).choose 1 N) j‖ ≤ ε)
    (p : Coeff n) (hp : p ∈ ellipsoid n)
    (hVrow : (‖visible (linearCut n) (extendRow a) p‖ + rowError n ε) ^ 2 ≤ V)
    (hV : V < 1) : criticalLogDifference χ ≤ -Real.log (1 - V) / 2 := by
  apply measured_row_upper τ hτ χ hχ hN n a hε ha _ hV
  obtain ⟨q, _, hmin, hle⟩ :=
    exists_leastSquares (M := linearCut n) (extendRow a) (ellipsoid_compact n) (ellipsoid_nonempty n)
  have herror : 0 ≤ rowError n ε := by unfold rowError; positivity
  rw [rowResidual, hmin, Real.sqrt_sq (norm_nonneg _)]
  exact (pow_le_pow_left₀ (add_nonneg (norm_nonneg _) herror)
    (add_le_add (hle p hp) le_rfl) 2).trans hVrow

/-- For sufficiently high stages the actual ideal rows have entry error at most 2^(−2M)
with coefficient one, where M=2n+1. No asserted computable threshold is needed for the limit. -/
theorem eventually_ideal_entry_error (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) (N : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ j : Fin (linearCut n+1),
      ‖linearRow χ N n j-DiskCoefficientEnergy.coeff
        (normalized χ (finiteHeckeL_exists_continuation χ).choose 1 N) j‖ ≤ (1/2:ℝ)^(2*linearCut n) := by
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hcut : Tendsto linearCut atTop atTop := tendsto_atTop_mono (fun n ↦ by change n ≤ 2*n+1; omega) tendsto_id
  filter_upwards [hcut.eventually (canonical_finite_ideal_coefficients τ hτ χ hχ N).1] with n hn
  intro j
  rw [coeff_normalized_eq τ hτ χ hχ _ hL he N j]
  exact hn j (Nat.le_of_lt_succ j.isLt)

/-- The actual finite row gives a Green upper certificate at every sufficiently high stage,
using its explicit dyadic envelope. A bound V for the displayed expression must be below one. -/
theorem eventually_ideal_upper (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) {N : ℕ} (hN : tableExponent τ hτ χ hχ ≤ N) :
    ∀ᶠ n : ℕ in atTop, ∀ V : ℝ,
      (Real.sqrt (idealResidual χ N n)+rowError n ((1/2:ℝ)^(2*linearCut n)))^2 ≤ V → V < 1 →
      criticalLogDifference χ ≤ -Real.log (1-V)/2 := by
  filter_upwards [eventually_ideal_entry_error τ hτ χ hχ N] with n hn
  intro V hrow hV
  exact measured_row_upper τ hτ χ hχ hN n (linearRow χ N n) (by positivity) hn hrow hV

/-- Inverting the limiting residual recovers the critical-line logarithmic difference itself. -/
theorem ideal_log_tendsto (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) {N : ℕ} (hN : tableExponent τ hτ χ hχ ≤ N) :
    Tendsto (fun n ↦ -Real.log (1-idealResidual χ N n)/2) atTop (𝓝 (criticalLogDifference χ)) := by
  have h := tendsto_const_nhds (x:=(1:ℝ)) |>.sub (idealResidual_tendsto τ hτ χ hχ hN)
  rw [sub_sub_cancel] at h
  have hlog := (Real.continuousAt_log (Real.exp_pos _).ne').tendsto.comp h
  simpa [Function.comp_def,Real.log_exp] using hlog.neg.div_const 2

/-- Squared norm bound obtained by correcting the measured residual at its eventual dyadic precision. -/
def idealUpperArgument (χ : U𝔽) (N n : ℕ) : ℝ :=
  (Real.sqrt (idealResidual χ N n)+rowError n ((1/2:ℝ)^(2*linearCut n)))^2

private theorem rowError_tendsto_zero :
    Tendsto (fun n : ℕ ↦ rowError n ((1/2:ℝ)^(2*linearCut n))) atTop (𝓝 0) := by
  let q := (1/2:ℝ)^4
  have hq : 0 ≤ q := by norm_num [q]
  have hq1 : q < 1 := by norm_num [q]
  have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 (r:=q) hq hq1
  have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1
  have hlin : Tendsto (fun n : ℕ ↦ ((n:ℝ)+1)*q^n) atTop (𝓝 0) := by
    simpa [add_mul] using h1.add h0
  have hpow n : (1/2:ℝ)^(2*linearCut n) = (1/2:ℝ)^2*q^n := by
    rw [show 2*linearCut n = 2+4*n by unfold linearCut; omega,pow_add,pow_mul]
  have hrad (n : ℕ) : Real.sqrt (((n:ℝ)+1)*((linearCut n:ℝ)+1)) = Real.sqrt 2*((n:ℝ)+1) := by
    rw [show ((n:ℝ)+1)*((linearCut n:ℝ)+1) = 2*((n:ℝ)+1)^2 by unfold linearCut;push_cast;ring,
      Real.sqrt_mul (by norm_num),Real.sqrt_sq (by positivity)]
  have hat : Tendsto (fun n : ℕ ↦ (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by linarith) tendsto_natCast_atTop_atTop
  have htail := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hat)).const_mul (2*(16/9:ℝ))
  have hvis := hlin.const_mul (2*Real.sqrt 2*(1/2:ℝ)^2)
  have hsum := hvis.add htail
  simpa only [mul_zero,add_zero] using hsum.congr (fun n ↦ by
    dsimp [rowError,Function.comp_def]
    rw [hpow,hrad,div_eq_mul_inv]
    ring)

/-- The corrected finite readouts eventually give genuine upper bounds for the Green mass.
Those upper bounds converge to the mass. The onset may depend on the field, character and exponent. -/
theorem ideal_upper_recovers_green (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) {N : ℕ} (hN : tableExponent τ hτ χ hχ ≤ N) :
    (∀ᶠ n : ℕ in atTop, idealUpperArgument χ N n < 1 ∧ criticalLogDifference χ ≤
      -Real.log (1-idealUpperArgument χ N n)/2) ∧
    Tendsto (fun n ↦ -Real.log (1-idealUpperArgument χ N n)/2) atTop (𝓝 (criticalLogDifference χ)) := by
  obtain ⟨hf,hc⟩ := (canonical_diskAlgebra_control τ hτ χ hχ).choose_spec.2 N ((le_max_left _ _).trans hN)
  have hG : 0 ≤ criticalLogDifference χ := by
    rw [← canonical_logGap τ hτ χ hχ N]
    exact (HardyBoundary.disk_boundary_lower hf hc.nonzero_center).1
  have hR : 0 ≤ 1-Real.exp (-2*(criticalLogDifference χ)) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hlim : Tendsto (idealUpperArgument χ N) atTop (𝓝 (1-Real.exp (-2*(criticalLogDifference χ)))) := by
    have hs := (Real.continuous_sqrt.tendsto _).comp (idealResidual_tendsto τ hτ χ hχ hN)
    change Tendsto (fun n : ℕ ↦ (Real.sqrt (idealResidual χ N n)+rowError n ((1/2:ℝ)^(2*linearCut n)))^2) _ _
    simpa only [Function.comp_def,add_zero,Real.sq_sqrt hR] using
      (hs.add rowError_tendsto_zero).pow 2
  constructor
  · filter_upwards [hlim.eventually_lt_const (show 1-Real.exp (-2*(criticalLogDifference χ))<1 by linarith [Real.exp_pos (-2*(criticalLogDifference χ))]),
      eventually_ideal_upper τ hτ χ hχ hN] with n hn hu
    exact ⟨hn,hu _ le_rfl hn⟩
  · have hh := tendsto_const_nhds (x:=(1:ℝ)) |>.sub hlim
    rw [sub_sub_cancel] at hh
    have hl := (Real.continuousAt_log (Real.exp_pos _).ne').tendsto.comp hh
    simpa [Function.comp_def,Real.log_exp] using hl.neg.div_const 2

/-- For every stage, rounded entries within η of the actual finite ideal row give a certificate.
One character- and exponent-dependent arithmetic constant applies to all stages. -/
theorem exists_rounded_ideal_upper (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) {N : ℕ} (hN : tableExponent τ hτ χ hχ ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (a : Fin (linearCut n+1) → ℂ) (η V : ℝ), 0 ≤ η →
      (∀ j, ‖a j-linearRow χ N n j‖ ≤ η) →
      (Real.sqrt (rowResidual a)+rowError n (η+C*(1/2:ℝ)^(2*linearCut n)))^2 ≤ V → V < 1 →
      criticalLogDifference χ ≤ -Real.log (1-V)/2 := by
  obtain ⟨c,hcoeff,_,⟨C,hC,he⟩,_⟩ :=
    (canonical_polynomial_ideal_HardyTable τ hτ χ hχ).choose_spec.2 N ((le_max_right _ _).trans hN)
  refine ⟨C,hC,fun n a η V hη ha hv hV ↦ ?_⟩
  apply measured_row_upper τ hτ χ hχ hN n a (by positivity : 0 ≤ η+C*(1/2:ℝ)^(2*linearCut n)) _ hv hV
  intro j
  rw [← hcoeff]
  have ht := dist_triangle (a j) (linearRow χ N n j) (c j)
  simp only [dist_eq_norm] at ht
  exact ht.trans (add_le_add (ha j) (he n j))

/-- Corrected residual from finitely many rational polynomial candidates and the finite ideal row. -/
def gridUpperArgument (χ : U𝔽) (N n : ℕ) : ℝ :=
  (gridNorm n (extendRow (linearRow χ N n)) + rowError n ((1/2 : ℝ) ^ (2 * linearCut n))) ^ 2

private theorem ideal_grid_bounds (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) {N : ℕ} (hN : tableExponent τ hτ χ hχ ≤ N) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n,
      Real.sqrt (idealResidual χ N n) ≤ gridNorm n (extendRow (linearRow χ N n)) ∧
      gridNorm n (extendRow (linearRow χ N n)) ≤ Real.sqrt (idealResidual χ N n) + 4*A/((n:ℝ)+1) := by
  obtain ⟨c, _, _, ⟨C, hC, he⟩, _⟩ :=
    (canonical_polynomial_ideal_HardyTable τ hτ χ hχ).choose_spec.2 N ((le_max_right _ _).trans hN)
  refine ⟨C + ‖c‖, add_nonneg hC (norm_nonneg _), fun n ↦ gridNorm_bounds n _
    (add_nonneg hC (norm_nonneg _)) (fun j hj ↦ ?_)⟩
  let i : Fin (linearCut n + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  rw [extendRow, dite_eq_left (Nat.lt_succ_of_le hj)]
  change ‖linearRow χ N n i‖ ≤ _
  calc
    _ ≤ ‖linearRow χ N n i - c i‖ + ‖c i‖ := norm_le_norm_sub_add _ _
    _ ≤ C * (1/2 : ℝ) ^ (2 * linearCut n) + ‖c‖ :=
      add_le_add (he n i) (lp.norm_apply_le_norm (by norm_num) c i)
    _ ≤ C + ‖c‖ := add_le_add (mul_le_of_le_one_right hC
      (pow_le_one₀ (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num))) le_rfl

/-- The exhaustive finite grid gives a one-sided sequence converging to the physical logarithmic
difference. Computing a constrained real infimum is unnecessary. The data in this statement
are the exact finite ideal entries. The start of the unit dyadic error bound may depend on χ and N. -/
theorem grid_upper_recovers_green (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) {N : ℕ} (hN : tableExponent τ hτ χ hχ ≤ N) :
    (∀ᶠ n : ℕ in atTop, gridUpperArgument χ N n < 1 ∧ criticalLogDifference χ ≤
      -Real.log (1 - gridUpperArgument χ N n) / 2) ∧
    Tendsto (fun n ↦ -Real.log (1 - gridUpperArgument χ N n) / 2) atTop (𝓝 (criticalLogDifference χ)) := by
  obtain ⟨A, _, hb⟩ := ideal_grid_bounds τ hτ χ hχ hN
  let R := 1 - Real.exp (-2 * criticalLogDifference χ)
  have hr : Tendsto (idealResidual χ N) atTop (𝓝 R) := idealResidual_tendsto τ hτ χ hχ hN
  have hR : 0 ≤ R := ge_of_tendsto hr (Eventually.of_forall fun n ↦
    (leastSquares_mem_Icc (M := linearCut n) (extendRow (linearRow χ N n))
      (ellipsoid_compact n) (show (0 : Coeff n) ∈ ellipsoid n by simp [ellipsoid, weightedEnergy]; positivity)).1)
  have hs := (Real.continuous_sqrt.tendsto R).comp hr
  have hat : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ by linarith) tendsto_natCast_atTop_atTop
  have he : Tendsto (fun n : ℕ ↦ 4*A/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using (tendsto_inv_atTop_zero.comp hat).const_mul (4*A)
  have hg : Tendsto (fun n ↦ gridNorm n (extendRow (linearRow χ N n))) atTop (𝓝 (Real.sqrt R)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hs (by simpa only [Function.comp_def, add_zero] using hs.add he)
      (fun n ↦ (hb n).1) (fun n ↦ (hb n).2)
  have hlim : Tendsto (gridUpperArgument χ N) atTop (𝓝 R) := by
    change Tendsto (fun n : ℕ ↦ (gridNorm n (extendRow (linearRow χ N n)) +
      rowError n ((1/2:ℝ)^(2 * linearCut n)))^2) _ _
    simpa only [add_zero, Real.sq_sqrt hR] using (hg.add rowError_tendsto_zero).pow 2
  constructor
  · filter_upwards [hlim.eventually_lt_const (show R < 1 by dsimp [R]; linarith [Real.exp_pos (-2 * criticalLogDifference χ)]),
      eventually_ideal_upper τ hτ χ hχ hN] with n ht hu
    refine ⟨ht, hu _ ?_ ht⟩
    exact pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) (by unfold rowError; positivity))
      (add_le_add (hb n).1 le_rfl) 2
  · have h := (tendsto_const_nhds (x := (1:ℝ))).sub hlim
    change Tendsto _ _ (𝓝 (1 - (1 - Real.exp (-2 * criticalLogDifference χ)))) at h
    rw [sub_sub_cancel] at h
    have hl := (Real.continuousAt_log (Real.exp_pos _).ne').tendsto.comp h
    simpa [Function.comp_def, Real.log_exp] using hl.neg.div_const 2

/-- A rounded finite row gives a one-sided certificate from the explicit integer grid.
The same arithmetic constant applies at every stage for a fixed character and exponent. -/
theorem exists_rounded_grid_upper (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) {N : ℕ} (hN : tableExponent τ hτ χ hχ ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (a : Fin (linearCut n + 1) → ℂ) (η V : ℝ),
      0 ≤ η → (∀ j, ‖a j - linearRow χ N n j‖ ≤ η) →
      (gridNorm n (extendRow a) + rowError n (η + C * (1/2 : ℝ) ^ (2 * linearCut n))) ^ 2 ≤ V →
      V < 1 → criticalLogDifference χ ≤ -Real.log (1 - V) / 2 := by
  obtain ⟨C, hC, h⟩ := exists_rounded_ideal_upper τ hτ χ hχ hN
  refine ⟨C, hC, fun n a η V hη ha hb hV ↦ h n a η V hη ha ?_ hV⟩
  exact (pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) (by unfold rowError; positivity))
    (add_le_add (sqrt_le_gridNorm n (extendRow a)) le_rfl) 2).trans hb

end RiemannMasullo.HeckeHardyGreen

end
