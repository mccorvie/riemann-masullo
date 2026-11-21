module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public noncomputable section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory.L2

/-- The integral of the squared pointwise norm is the square of the L² norm. -/
theorem integral_sq_norm {X E 𝕜 : Type*} [MeasurableSpace X] {μ : Measure X}
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (f : Lp E 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), L2.inner_def]
  change _ = RCLike.reCLM (∫ x, inner 𝕜 (f x) (f x) ∂μ)
  rw [← RCLike.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := 𝕜) f f)]
  simp [inner_self_eq_norm_sq_to_K]

/-- A sequence of scalar L² functions with summable squared L² norms is the coordinate
family of a single square-integrable function with values in ℓ². -/
theorem exists_memLp_coordinates {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u : ℕ → Lp ℂ 2 μ) (hu : Summable fun n ↦ ‖u n‖ ^ 2) :
    ∃ a : X → lp (fun _ : ℕ ↦ ℂ) 2, MemLp a 2 μ ∧
      ∀ᵐ x ∂μ, ∀ n, a x n = u n x := by
  classical
  have he (n : ℕ) : ∫⁻ x, ENNReal.ofReal (‖u n x‖ ^ 2) ∂μ =
      ENNReal.ofReal (‖u n‖ ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((Lp.memLp (u n)).integrable_norm_pow (by decide : 2 ≠ 0))
      (Eventually.of_forall fun _ ↦ sq_nonneg _), integral_sq_norm (𝕜 := ℂ)]
  have hmeas (n : ℕ) : AEMeasurable (fun x ↦ ENNReal.ofReal (‖u n x‖ ^ 2)) μ :=
    ((Lp.aestronglyMeasurable (u n)).norm.aemeasurable.pow_const _).ennreal_ofReal
  have henergy : ∫⁻ x, ∑' n, ENNReal.ofReal (‖u n x‖ ^ 2) ∂μ =
      ENNReal.ofReal (∑' n, ‖u n‖ ^ 2) := by
    rw [lintegral_tsum hmeas, ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ sq_nonneg _) hu]
    simp only [he]
  have hs : ∀ᵐ x ∂μ, Summable fun n ↦ ‖u n x‖ ^ 2 := by
    have hfinite := ae_lt_top' (AEMeasurable.tsum hmeas) (by rw [henergy]; simp)
    filter_upwards [hfinite] with x hx
    have hnorm (n : ℕ) : ENNReal.ofReal (‖u n x‖ ^ 2) = ‖(‖u n x‖ ^ 2 : ℝ)‖ₑ :=
      by rw [← ofReal_norm, Real.norm_of_nonneg (sq_nonneg _)]
    simp_rw [hnorm] at hx
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using
      (tsum_eNorm_ne_top_iff_summable_norm.mp hx.ne)
  let a (x : X) : lp (fun _ : ℕ ↦ ℂ) 2 :=
    if h : Summable (fun n ↦ ‖u n x‖ ^ 2) then
      ⟨fun n ↦ u n x, memℓp_gen (by simpa using h)⟩ else 0
  have hcoords : ∀ᵐ x ∂μ, ∀ n, a x n = u n x := by
    filter_upwards [hs] with x hx n
    simp [a, hx]
  have ha : AEStronglyMeasurable a μ := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (m : ℕ) x ↦ ∑ n ∈ Finset.range m, lp.single 2 n (u n x))
    · intro m
      apply Finset.aestronglyMeasurable_fun_sum
      intro n _
      exact (lp.singleContinuousLinearMap ℂ _ 2 n).continuous.comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable (u n))
    · filter_upwards [hcoords] with x hx
      simpa only [hx] using (lp.hasSum_single (by simp) (a x)).tendsto_sum_nat
  refine ⟨a, (memLp_two_iff_integrable_sq_norm ha).mpr
    ⟨ha.norm.pow _, ?_⟩, hcoords⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ ↦ sq_nonneg _)]
  calc
    (∫⁻ x, ENNReal.ofReal (‖a x‖ ^ 2) ∂μ) =
        ∫⁻ x, ∑' n, ENNReal.ofReal (‖u n x‖ ^ 2) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hs, hcoords] with x hx hc
      have hn : ‖a x‖ ^ 2 = ∑' n, ‖u n x‖ ^ 2 := by
        simpa [hc] using lp.norm_rpow_eq_tsum (p := 2) (by simp) (a x)
      rw [hn, ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ sq_nonneg _) hx]
    _ < ∞ := by rw [henergy]; simp

/-- The outer product of two scalar L² functions has L² norm equal to the product
of their norms. -/
theorem exists_outerProduct {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    (u : Lp ℂ 2 μ) (v : Lp ℂ 2 ν) :
    ∃ K : Lp ℂ 2 (μ.prod ν), (K : X × Y → ℂ) =ᵐ[μ.prod ν]
      (fun p ↦ inner ℂ (v p.2) (u p.1)) ∧ ‖K‖ = ‖u‖ * ‖v‖ := by
  let f (p : X × Y) := inner ℂ (v p.2) (u p.1)
  have hf : AEStronglyMeasurable f (μ.prod ν) :=
    (Lp.aestronglyMeasurable v).comp_snd.inner (Lp.aestronglyMeasurable u).comp_fst
  have hsq : ∀ p, ‖f p‖ ^ 2 = ‖u p.1‖ ^ 2 * ‖v p.2‖ ^ 2 := by
    intro p
    simp [f, RCLike.inner_apply, mul_pow]
  have hLp : MemLp f 2 (μ.prod ν) := by
    apply (memLp_two_iff_integrable_sq_norm hf).mpr
    simpa only [hsq] using
      ((Lp.memLp u).integrable_norm_pow (by decide : 2 ≠ 0)).mul_prod
        ((Lp.memLp v).integrable_norm_pow (by decide : 2 ≠ 0))
  refine ⟨hLp.toLp f, hLp.coeFn_toLp, ?_⟩
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [← integral_sq_norm (𝕜 := ℂ) (hLp.toLp f), mul_pow,
    ← integral_sq_norm (𝕜 := ℂ) u, ← integral_sq_norm (𝕜 := ℂ) v, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [hLp.coeFn_toLp] with p hp
  exact (congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) hp).trans (hsq p)

end MeasureTheory.L2
