module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Complex.Basic
public import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

open Bornology Filter Set Topology

namespace RiemannMasullo

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T1Space E]

/-- Scalar slopes of a smooth curve approach its derivative at a rate bounded by a
constant times the step size on the unit interval. -/
private theorem scalar_slope_error {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc (0 : ℝ) 1, ‖slope F 0 t - deriv F 0‖ ≤ C * t := by
  have hD : ContDiff ℝ 1 (deriv F) := hF.deriv'
  have hDD : Continuous (deriv (deriv F)) := hD.continuous_deriv_one
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hDD :
    IsCompact (deriv (deriv F) '' Icc (0 : ℝ) 1)).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun t ht ↦ ?_⟩
  have hbound (s : ℝ) (hs : s ∈ Icc 0 t) : ‖deriv F s - deriv F 0‖ ≤ max C 0 * t := by
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
    calc
      _ ≤ max C 0 * ‖s - 0‖ := (convex_Icc 0 1).norm_image_sub_le_of_norm_deriv_le
        (fun x _ ↦ hD.differentiable (by norm_num) x)
        (fun x hx ↦ (hC _ (mem_image_of_mem _ hx)).trans (le_max_left _ _))
        ⟨le_rfl, zero_le_one⟩ hs'
      _ ≤ _ := by simpa [Real.norm_of_nonneg hs.1] using
        mul_le_mul_of_nonneg_left hs.2 (le_max_right C 0)
  let G (s : ℝ) := F s - s • deriv F 0
  have hG (s : ℝ) : HasDerivAt G (deriv F s - deriv F 0) s :=
    ((hF.differentiable (by norm_num) s).hasDerivAt).sub
      (by simpa using (hasDerivAt_id s).smul_const (deriv F 0))
  have hmean := (convex_Icc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ ↦ (hG s).hasDerivWithinAt) hbound ⟨le_rfl, ht.1.le⟩ ⟨ht.1.le, le_rfl⟩
  have heq : slope F 0 t - deriv F 0 = t⁻¹ • (G t - G 0) := by
    simp only [slope_def_module, G, zero_smul, sub_zero]
    rw [sub_right_comm (F t) (t • deriv F 0)]
    simp only [smul_sub, inv_smul_smul₀ ht.1.ne']
  rw [heq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.1.le),
    inv_mul_le_iff₀ ht.1]
  simpa [Real.norm_of_nonneg ht.1.le, mul_comm, mul_left_comm] using hmean

/-- Quasi-completeness lifts the derivative at zero of a weakly smooth curve.
The difference quotients are Cauchy because the normalized pairwise differences
are bounded under all continuous functionals. -/
theorem exists_hasDerivAt_eval_zero_of_contDiff {F : ℝ → E}
    (hF : ∀ φ : StrongDual ℂ E, ContDiff ℝ 2 (φ ∘ F)) :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    QuasiCompleteSpace ℂ E → ∃ z : E, ∀ φ : StrongDual ℂ E,
      HasDerivAt (φ ∘ F) (φ z) 0 := by
  let := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  intro hqc
  let t (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have ht (n : ℕ) : t n ∈ Ioc (0 : ℝ) 1 :=
    ⟨by dsimp [t]; positivity, (div_le_one (by positivity)).mpr (by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)⟩
  have htlim : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let q (n : ℕ) : E := ((t n : ℂ)⁻¹) • (F (t n) - F 0)
  have hq (φ : StrongDual ℂ E) (n : ℕ) : φ (q n) = slope (φ ∘ F) 0 (t n) := by
    simp [q, slope_def_module, Complex.real_smul]
  let r (mn : ℕ × ℕ) : ℂ := ((t mn.1 + t mn.2 : ℝ) : ℂ)
  have hr (mn : ℕ × ℕ) : 0 < t mn.1 + t mn.2 := add_pos (ht _).1 (ht _).1
  let D (mn : ℕ × ℕ) : E := (r mn)⁻¹ • (q mn.1 - q mn.2)
  have hD : IsVonNBounded ℂ (range D) := by
    apply isVonNBounded_of_dual_bounded
    intro φ
    obtain ⟨C, _, hC⟩ := scalar_slope_error (hF φ)
    refine ⟨C, ?_⟩
    rintro _ ⟨⟨m, n⟩, rfl⟩
    simp only [D, map_smul, map_sub, norm_smul, norm_inv, r, Complex.norm_real]
    rw [Real.norm_of_nonneg (hr (m, n)).le, inv_mul_le_iff₀ (hr (m, n))]
    calc
      ‖φ (q m) - φ (q n)‖ ≤
          ‖φ (q m) - deriv (φ ∘ F) 0‖ + ‖φ (q n) - deriv (φ ∘ F) 0‖ :=
        by simpa only [norm_sub_rev (deriv (φ ∘ F) 0) (φ (q n))] using
          norm_sub_le_norm_sub_add_norm_sub (φ (q m)) (deriv (φ ∘ F) 0) (φ (q n))
      _ ≤ C * (t m + t n) := by
        rw [mul_add, hq, hq]
        exact add_le_add (hC _ (ht m)) (hC _ (ht n))
      _ = _ := mul_comm _ _
  have hrLim : Tendsto r atTop (𝓝 0) := by
    rw [← prod_atTop_atTop_eq]
    have h : Tendsto (fun mn : ℕ × ℕ ↦ t mn.1 + t mn.2) (atTop ×ˢ atTop) (𝓝 0) := by
      simpa only [zero_add, Function.comp_apply] using
        (htlim.comp tendsto_fst).add (htlim.comp tendsto_snd)
    simpa only [r, Function.comp_def, Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).comp h
  have hc : CauchySeq q := by
    rw [cauchySeq_iff_tendsto, uniformity_eq_comap_nhds_zero_swapped, tendsto_comap_iff]
    apply (hD.smul_tendsto_zero (Eventually.of_forall fun mn ↦ mem_range_self mn) hrLim).congr
    intro mn
    exact smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (hr mn).ne') _
  have hb := hc.totallyBounded_range.isVonNBounded ℂ
  obtain ⟨z, _, hz⟩ := hqc.quasiComplete hb.closure isClosed_closure _ hc
    (by
      rw [le_principal_iff, mem_map]
      exact Eventually.of_forall fun n ↦ subset_closure (mem_range_self n))
  refine ⟨z, fun φ ↦ ?_⟩
  have hs : Tendsto t atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨htlim, Eventually.of_forall fun n ↦ (ht n).1.ne'⟩
  have hlim := ((hF φ).differentiable (by norm_num) 0).hasDerivAt.tendsto_slope.comp hs
  have hzφ : Tendsto (fun n ↦ φ (q n)) atTop (𝓝 (φ z)) := (φ.continuous.tendsto z).comp hz
  have heq : φ z = deriv (φ ∘ F) 0 := tendsto_nhds_unique hzφ (hlim.congr (fun n ↦ (hq φ n).symm))
  rw [heq]
  exact ((hF φ).differentiable (by norm_num) 0).hasDerivAt

end RiemannMasullo
