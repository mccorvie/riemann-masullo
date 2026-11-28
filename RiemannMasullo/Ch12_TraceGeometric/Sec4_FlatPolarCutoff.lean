module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatPolar
public import RiemannMasullo.ForMathlib.Analysis.Fourier.PositiveRayCosine
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Removing the spatial cutoff in the flat polar trace

Reconstruction: in Step II of Theorem 12.4.1.1, pp. 516–517, the physical cutoff
acts on the output. Its contribution to the rational zero-order polar trace is
controlled by the discarded part of a single physical `L²` vector. For bands `B > 0`,
the cutoff may be removed when `Bh → 0` and `BL → ∞`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped CompactlySupported ComplexInnerProductSpace NNReal Topology

namespace RiemannMasullo.FlatPolar

local notation "ν" => volume.restrict (Ioi (0 : ℝ))
local notation "H" => Lp ℂ 2 ν

/-- Multiplication by the characteristic function of the physical interval `(h, L]`. -/
def spatialCutoff (h L : ℝ) : H →L[ℂ] H :=
  positiveRayMultiplier ((Ioc h L).indicator (fun _ ↦ (1 : ℂ)))
    (measurable_const.indicator measurableSet_Ioc) 1 zero_le_one
    (fun x ↦ by by_cases hx : x ∈ Ioc h L <;> simp [hx]) 1

/-- The actual bounded cutoff agrees with the pointwise indicator on representatives. -/
theorem spatialCutoff_apply (h L : ℝ) (f : H) :
    ⇑(spatialCutoff h L f) =ᵐ[ν] (Ioc h L).indicator f := by
  unfold spatialCutoff
  refine (positiveRayMultiplier_apply _ _ _ _ _ 1 f).trans ?_
  filter_upwards with x
  by_cases hx : x ∈ Ioc h L <;> simp [hx]

/-- Every spatial cutoff is a contraction. -/
theorem norm_spatialCutoff_le (h L : ℝ) : ‖spatialCutoff h L‖ ≤ 1 :=
  positiveRayMultiplier_norm_le _ _ _ _ _ _

/-- The cutoff may be moved to the other entry of the complex inner product. -/
theorem inner_spatialCutoff (h L : ℝ) (f g : H) :
    ⟪spatialCutoff h L f, g⟫ = ⟪f, spatialCutoff h L g⟫ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [spatialCutoff_apply h L f, spatialCutoff_apply h L g] with x hf hg
  by_cases hx : x ∈ Ioc h L <;> simp [hf, hg, hx]

/-- Error in a matrix coefficient after cutting off the output, controlled by the
unmasked output norm and the discarded portion of the fixed testing vector. -/
theorem norm_inner_spatialCutoff_sub_le (h L : ℝ) (u v : H) :
    ‖⟪spatialCutoff h L u, v⟫ - ⟪u, v⟫‖ ≤ ‖u‖ * ‖spatialCutoff h L v - v‖ := by
  rw [inner_spatialCutoff, ← inner_sub_right]
  exact norm_inner_le_norm _ _

/-- The same estimate in the convention that puts the testing vector first. -/
theorem norm_inner_sub_spatialCutoff_right_le (h L : ℝ) (u v : H) :
    ‖⟪v, spatialCutoff h L u⟫ - ⟪v, u⟫‖ ≤ ‖u‖ * ‖spatialCutoff h L v - v‖ := by
  rw [← inner_spatialCutoff, ← inner_sub_left, mul_comm]
  exact norm_inner_le_norm _ _

private theorem ray_norm_sq (f : H) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
  calc
    ‖f‖ ^ 2 = RCLike.re (inner ℂ f f) := by
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), Real.sq_sqrt inner_self_nonneg]
    _ = RCLike.re (∫ x, inner ℂ (f x) (f x) ∂ν) := by rw [L2.inner_def]
    _ = ∫ x, RCLike.re (inner ℂ (f x) (f x)) ∂ν := (integral_re (L2.integrable_inner f f)).symm
    _ = ∫ x, ‖f x‖ ^ 2 ∂ν := by simp_rw [inner_self_eq_norm_sq]

/-- The squared truncation error is exactly the mass of `|f|²` off the spatial interval. -/
theorem norm_spatialCutoff_sub_sq (h L : ℝ) (f : H) :
    ‖spatialCutoff h L f - f‖ ^ 2 =
      ∫ x, (Ioc h L)ᶜ.indicator (fun y ↦ ‖f y‖ ^ 2) x ∂ν := by
  rw [ray_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (spatialCutoff h L f) f, spatialCutoff_apply h L f] with x hs hf
  rw [hs, Pi.sub_apply, hf]
  by_cases hx : x ∈ Ioc h L <;> simp [hx]

private theorem tendsto_spatialCutoff_prod (f : H) :
    Tendsto (fun p : ℝ × ℝ ↦ spatialCutoff p.1 p.2 f) ((𝓝 0) ×ˢ atTop) (𝓝 f) := by
  let l : Filter (ℝ × ℝ) := (𝓝 0) ×ˢ atTop
  let b (x : ℝ) := ‖f x‖ ^ 2
  have hb : Integrable b ν :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have ht : Tendsto (fun p : ℝ × ℝ ↦ ∫ x, (Ioc p.1 p.2)ᶜ.indicator b x ∂ν) l (𝓝 0) := by
    simpa only [integral_zero] using
      (tendsto_integral_filter_of_dominated_convergence (f := fun _ : ℝ ↦ (0 : ℝ)) b
        (.of_forall fun p ↦ (hb.indicator measurableSet_Ioc.compl).aestronglyMeasurable)
        (.of_forall fun p ↦ ae_of_all _ fun x ↦ by
          by_cases hx : x ∈ Ioc p.1 p.2 <;> simp [hx, b, Real.norm_of_nonneg (sq_nonneg _)])
        hb (by
          filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))] with x hx
          have hh : ∀ᶠ p : ℝ × ℝ in l, p.1 < x := tendsto_fst.eventually (gt_mem_nhds hx)
          have hL : ∀ᶠ p : ℝ × ℝ in l, x ≤ p.2 := tendsto_snd.eventually (eventually_ge_atTop x)
          apply tendsto_const_nhds.congr'
          filter_upwards [hh, hL] with p hp hq
          simp [show x ∈ Ioc p.1 p.2 from ⟨hp, hq⟩]) :
        Tendsto (fun p : ℝ × ℝ ↦ ∫ x, (Ioc p.1 p.2)ᶜ.indicator b x ∂ν) l
          (𝓝 (∫ _ : ℝ, (0 : ℝ) ∂ν)))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp ht
  simp only [Real.sqrt_zero] at hs
  refine hs.congr fun p ↦ ?_
  change Real.sqrt (∫ x, (Ioc p.1 p.2)ᶜ.indicator (fun y ↦ ‖f y‖ ^ 2) x ∂ν) = _
  rw [← norm_spatialCutoff_sub_sq, Real.sqrt_sq (norm_nonneg _)]

/-- Strong convergence on the positive-ray `L²` space for independent upper and lower
cutoffs. The endpoints may vary along an arbitrary filter with no monotonicity assumption. -/
theorem tendsto_spatialCutoff {ι : Type*} {l : Filter ι} {h L : ι → ℝ}
    (hh : Tendsto h l (𝓝 0)) (hL : Tendsto L l atTop) (f : H) :
    Tendsto (fun i ↦ spatialCutoff (h i) (L i) f) l (𝓝 f) := by
  have hpair : Tendsto (fun i ↦ (h i, L i)) l ((𝓝 0) ×ˢ atTop) := hh.prodMk hL
  change Tendsto ((fun p : ℝ × ℝ ↦ spatialCutoff p.1 p.2 f) ∘ (fun i ↦ (h i, L i))) l (𝓝 f)
  exact (tendsto_spatialCutoff_prod f).comp hpair

/-- Under unitary dilation by `B`, the physical interval `(h, L]` becomes `(B h, B L]`. -/
theorem spatialCutoff_positiveRayDilation (B : ℝ) (hB : 0 < B) (h L : ℝ) (f : H) :
    spatialCutoff h L (positiveRayDilation B hB f) =
      positiveRayDilation B hB (spatialCutoff (B * h) (B * L) f) := by
  apply Lp.ext
  filter_upwards [spatialCutoff_apply h L (positiveRayDilation B hB f),
    positiveRayDilation_apply B hB f, positiveRayDilation_apply B hB (spatialCutoff (B * h) (B * L) f),
    (positiveRayScale_quasiMeasurePreserving B hB).ae_eq_comp
      (spatialCutoff_apply (B * h) (B * L) f)] with x hc hd hdc hcd
  change spatialCutoff (B * h) (B * L) f (B * x) = (Ioc (B * h) (B * L)).indicator f (B * x) at hcd
  rw [hc, hdc, hcd]
  have hmem : B * x ∈ Ioc (B * h) (B * L) ↔ x ∈ Ioc h L := by
    simp only [mem_Ioc, mul_lt_mul_iff_right₀ hB, mul_le_mul_iff_right₀ hB]
  by_cases hx : x ∈ Ioc h L
  · simp only [indicator_of_mem hx, indicator_of_mem (hmem.mpr hx), hd]
  · simp [hx, mt hmem.mp hx]

/-- The moving-band physical tail norm is exactly the fixed-vector tail norm at the
two scaled endpoints. -/
theorem norm_spatialCutoff_dilation_sub (B : ℝ) (hB : 0 < B) (h L : ℝ) (v : H) :
    ‖spatialCutoff h L (positiveRayDilation B hB v) - positiveRayDilation B hB v‖ =
      ‖spatialCutoff (B * h) (B * L) v - v‖ := by
  rw [spatialCutoff_positiveRayDilation, ← map_sub, LinearIsometryEquiv.norm_map]

/-- Uniform spatial cutoff removal for matrix coefficients of a moving unitary dilation.
The family in the other slot need only be uniformly bounded. -/
theorem uniform_spatialCutoff_dilation {ι α : Type*} {l : Filter ι} {B h L : ι → ℝ}
    (hB : ∀ i, 0 < B i) (hh : Tendsto (fun i ↦ B i * h i) l (𝓝 0))
    (hL : Tendsto (fun i ↦ B i * L i) l atTop)
    (v : H) (u : ι → α → H) (C : ℝ) (hC : ∀ i a, ‖u i a‖ ≤ C) :
    ∀ ε > 0, ∀ᶠ i in l, ∀ a,
      ‖⟪positiveRayDilation (B i) (hB i) v, spatialCutoff (h i) (L i) (u i a)⟫ -
        ⟪positiveRayDilation (B i) (hB i) v, u i a⟫‖ < ε := by
  have ht := tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_spatialCutoff hh hL v)
  have hCt : Tendsto (fun i ↦ C * ‖spatialCutoff (B i * h i) (B i * L i) v - v‖) l (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul ht
  intro ε hε
  filter_upwards [hCt.eventually (Iio_mem_nhds hε)] with i hi
  intro a
  calc
    _ ≤ ‖u i a‖ * ‖spatialCutoff (h i) (L i) (positiveRayDilation (B i) (hB i) v) -
        positiveRayDilation (B i) (hB i) v‖ :=
      norm_inner_sub_spatialCutoff_right_le _ _ _ _
    _ = ‖u i a‖ * ‖spatialCutoff (B i * h i) (B i * L i) v - v‖ := by
      rw [norm_spatialCutoff_dilation_sub]
    _ ≤ C * ‖spatialCutoff (B i * h i) (B i * L i) v - v‖ :=
      mul_le_mul_of_nonneg_right (hC i a) (norm_nonneg _)
    _ < ε := hi

/-- The literal normalized indicator of `(0, B]` is the unitary dilation of the unit band. -/
theorem bandVector_eq_inverse_dilation (B : ℝ) (hB : 0 < B) :
    bandVector B = positiveRayDilation B⁻¹ (inv_pos.mpr hB) (bandVector 1) := by
  apply Lp.ext
  filter_upwards [bandVector_ae_eq B,
    positiveRayDilation_apply B⁻¹ (inv_pos.mpr hB) (bandVector 1),
    (positiveRayScale_quasiMeasurePreserving B⁻¹ (inv_pos.mpr hB)).ae_eq_comp
      (bandVector_ae_eq 1)] with x hb hd hband
  change bandVector 1 (B⁻¹ * x) = bandProfile 1 (B⁻¹ * x) at hband
  rw [hb, hd, hband]
  have hm : B⁻¹ * x ∈ Ioc 0 1 ↔ x ∈ Ioc 0 B := by
    simp only [mem_Ioc, inv_mul_eq_div, div_pos_iff_of_pos_right hB, div_le_iff₀ hB, one_mul]
  by_cases hx : x ∈ Ioc 0 B
  · simp [bandProfile, hx, hm.mpr hx, Real.sqrt_inv]
  · simp [bandProfile, hx, mt hm.mp hx]

/-- A physical unitary chart only needs the inverse-dilation law on the single unit band.
Under this hypothesis the right side bounds the spatial error independently of the
direction of the other vector. -/
theorem norm_inner_spatialCutoff_bandVector_isometry_sub_le
    (V : H →ₗᵢ[ℂ] H) (B : ℝ) (hB : 0 < B)
    (hcov : V (positiveRayDilation B⁻¹ (inv_pos.mpr hB) (bandVector 1)) =
      positiveRayDilation B hB (V (bandVector 1))) (h L : ℝ) (u : H) :
    ‖⟪V (bandVector B), spatialCutoff h L (V u)⟫ - ⟪bandVector B, u⟫‖ ≤
      ‖u‖ * ‖spatialCutoff (B * h) (B * L) (V (bandVector 1)) - V (bandVector 1)‖ := by
  have hv := (congrArg V (bandVector_eq_inverse_dilation B hB)).trans hcov
  calc
    _ = ‖⟪V (bandVector B), spatialCutoff h L (V u)⟫ -
          ⟪V (bandVector B), V u⟫‖ := by rw [V.inner_map_map]
    _ ≤ ‖V u‖ * ‖spatialCutoff h L (V (bandVector B)) - V (bandVector B)‖ :=
      norm_inner_sub_spatialCutoff_right_le _ _ _ _
    _ = _ := by rw [hv, norm_spatialCutoff_dilation_sub, V.norm_map]

/-- On the original band `B`, remove the physical cutoff uniformly for any bounded
family of uncut vectors. Only `Bh → 0` and `BL → ∞` enter this limit. -/
theorem uniform_spatialCutoff_bandVector_isometry {ι α : Type*} {l : Filter ι} {B h L : ι → ℝ}
    (V : H →ₗᵢ[ℂ] H) (hB : ∀ i, 0 < B i)
    (hcov : ∀ i, V (positiveRayDilation (B i)⁻¹ (inv_pos.mpr (hB i)) (bandVector 1)) =
      positiveRayDilation (B i) (hB i) (V (bandVector 1)))
    (hh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hL : Tendsto (fun i ↦ B i * L i) l atTop)
    (u : ι → α → H) (C : ℝ) (hC : ∀ i a, ‖u i a‖ ≤ C) :
    ∀ ε > 0, ∀ᶠ i in l, ∀ a,
      ‖⟪V (bandVector (B i)), spatialCutoff (h i) (L i) (V (u i a))⟫ -
        ⟪bandVector (B i), u i a⟫‖ < ε := by
  have h := uniform_spatialCutoff_dilation hB hh hL (V (bandVector 1))
    (fun i a ↦ V (u i a)) C (fun i a ↦ by simpa using hC i a)
  intro ε hε
  filter_upwards [h ε hε] with i hi
  intro a
  have hv := (congrArg V (bandVector_eq_inverse_dilation (B i) (hB i))).trans (hcov i)
  simpa only [← hv, V.inner_map_map] using hi a

/-- The sharp physical annulus, expressed as a bounded operator on frequency space
through the isometric physical chart. -/
def spatialCutoffInChart (V : H →ₗᵢ[ℂ] H) (h L : ℝ) : H →L[ℂ] H :=
  V.toContinuousLinearMap.adjoint.comp ((spatialCutoff h L).comp V.toContinuousLinearMap)

private theorem hilbertTrace_spatialCutoffInChart (V : H →ₗᵢ[ℂ] H) (h L : ℝ)
    (T : H →L[ℂ] H) (e : H) :
    hilbertTrace (polarRankOne ((spatialCutoffInChart V h L).comp T) e) =
      ⟪V e, spatialCutoff h L (V (T e))⟫ := by
  rw [polarRankOne, hilbertTrace_smulRight]
  exact V.toContinuousLinearMap.adjoint_inner_right e _

/-- With the physical cutoff on the output, the nuclear polar trace has the same compact
dilation limit when the original scaled inner radius tends to zero and the scaled outer
radius tends to infinity. Only the inverse-dilation law on the unit band is needed here. -/
theorem tendsto_hilbertTrace_compactDilation_multiplier_spatial_of_isometry
    {ι : Type*} {l : Filter ι} {B h L : ι → ℝ}
    (V : H →ₗᵢ[ℂ] H) (hB : ∀ i, 0 < B i)
    (hcov : ∀ i, V (positiveRayDilation (B i)⁻¹ (inv_pos.mpr (hB i)) (bandVector 1)) =
      positiveRayDilation (B i) (hB i) (V (bandVector 1)))
    (hh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hL : Tendsto (fun i ↦ B i * L i) l atTop)
    (φ : C_c(ℝ≥0ˣ, ℂ)) (Q : ℝ → ℂ) (hQ : Measurable Q)
    (C : ℝ) (hC : 0 ≤ C) (hQC : ∀ t, ‖Q t‖ ≤ C) :
    Tendsto (fun i ↦ hilbertTrace (polarRankOne ((spatialCutoffInChart V (h i) (L i)).comp
      ((compactDilationAction φ).comp (positiveRayMultiplier Q hQ C hC hQC (B i))))
      (bandVector (B i)))) l (𝓝 (∫ a : ℝ≥0ˣ,
        φ a * ((Real.sqrt a.val : ℂ)⁻¹ * ∫ u in Ioc 0 (min 1 (a.val : ℝ)), Q u)
          ∂positiveRealHaar)) := by
  let M (i : ι) := positiveRayMultiplier Q hQ C hC hQC (B i)
  let T (i : ι) := (compactDilationAction φ).comp (M i)
  let u (i : ι) (_ : Unit) := T i (bandVector (B i))
  have hu (i : ι) (a : Unit) : ‖u i a‖ ≤ ‖compactDilationAction φ‖ * C := by
    calc
      _ ≤ ‖compactDilationAction φ‖ * ‖M i (bandVector (B i))‖ := (compactDilationAction φ).le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_left (by
        simpa only [norm_bandVector (hB i), mul_one] using
          ((M i).le_opNorm (bandVector (B i))).trans
            (mul_le_mul_of_nonneg_right (positiveRayMultiplier_norm_le Q hQ C hC hQC _) (norm_nonneg _)))
          (norm_nonneg _)
  have h := uniform_spatialCutoff_bandVector_isometry V hB hcov hh hL u _ hu
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  filter_upwards [h ε hε] with i hi
  rw [dist_eq_norm, hilbertTrace_spatialCutoffInChart,
    ← hilbertTrace_compactDilation_multiplier_polar φ Q hQ C hC hQC (hB i),
    polarRankOne, hilbertTrace_smulRight]
  exact hi ()

/-- For the normalized even inverse Plancherel chart on the positive ray, the compact
dilation polar trace with spatial cutoff converges to the gated polar integral. -/
theorem tendsto_hilbertTrace_compactDilation_multiplier_spatial
    {ι : Type*} {l : Filter ι} {B h L : ι → ℝ} (hB : ∀ i, 0 < B i)
    (hh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hL : Tendsto (fun i ↦ B i * L i) l atTop)
    (φ : C_c(ℝ≥0ˣ, ℂ)) (Q : ℝ → ℂ) (hQ : Measurable Q)
    (C : ℝ) (hC : 0 ≤ C) (hQC : ∀ t, ‖Q t‖ ≤ C) :
    Tendsto (fun i ↦ hilbertTrace (polarRankOne
      ((spatialCutoffInChart positiveRayInverseCosine (h i) (L i)).comp
        ((compactDilationAction φ).comp (positiveRayMultiplier Q hQ C hC hQC (B i))))
      (bandVector (B i)))) l (𝓝 (∫ a : ℝ≥0ˣ,
        φ a * ((Real.sqrt a.val : ℂ)⁻¹ * ∫ u in Ioc 0 (min 1 (a.val : ℝ)), Q u)
          ∂positiveRealHaar)) := by
  exact tendsto_hilbertTrace_compactDilation_multiplier_spatial_of_isometry
    positiveRayInverseCosine hB (fun i ↦ by
      simpa only [inv_inv] using positiveRayInverseCosine_dilation (B i)⁻¹
        (inv_pos.mpr (hB i)) (bandVector 1)) hh hL φ Q hQ C hC hQC

/-- In the inverse cosine chart, the adjoint used on the physical output is the ordinary
inverse unitary. -/
theorem spatialCutoffInChart_inverseCosine (h L : ℝ) :
    spatialCutoffInChart positiveRayInverseCosine h L =
      (positiveRayInverseCosineEquiv.symm : H →L[ℂ] H).comp
        ((spatialCutoff h L).comp (positiveRayInverseCosineEquiv : H →L[ℂ] H)) := by
  change (positiveRayInverseCosineEquiv : H →L[ℂ] H).adjoint.comp _ = _
  rw [positiveRayInverseCosineEquiv.adjoint_eq_symm]
  rfl

/-- The same limit with its negative sign is the trace of the difference between the
actual two-sided mean-zero and full band compressions of the spatially cut operator. -/
theorem exists_spatialCompressionDifference_tendsto
    {ι : Type*} {l : Filter ι} {B h L : ι → ℝ} (hB : ∀ i, 0 < B i)
    (hh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hL : Tendsto (fun i ↦ B i * L i) l atTop)
    (φ : C_c(ℝ≥0ˣ, ℂ)) (Q : ℝ → ℂ) (hQ : Measurable Q)
    (C : ℝ) (hC : 0 ≤ C) (hQC : ∀ t, ‖Q t‖ ≤ C) :
    let T (i : ι) := (spatialCutoffInChart positiveRayInverseCosine (h i) (L i)).comp
      ((compactDilationAction φ).comp (positiveRayMultiplier Q hQ C hC hQC (B i)))
    let E (i : ι) := (frequencyBand (B i)).starProjection
    let P (i : ι) := (meanZeroFrequencyBand (B i)).starProjection
    ∃ R : ι → nuclearEndomorphisms H,
      (∀ i, (R i).val = (P i).comp ((T i).comp (P i)) - (E i).comp ((T i).comp (E i))) ∧
      Tendsto (fun i ↦ hilbertTrace (R i)) l (𝓝 (-(∫ a : ℝ≥0ˣ,
        φ a * ((Real.sqrt a.val : ℂ)⁻¹ * ∫ u in Ioc 0 (min 1 (a.val : ℝ)), Q u)
          ∂positiveRealHaar))) := by
  let T (i : ι) := (spatialCutoffInChart positiveRayInverseCosine (h i) (L i)).comp
    ((compactDilationAction φ).comp (positiveRayMultiplier Q hQ C hC hQC (B i)))
  choose R hR htr using fun i ↦ polarFree_compression_difference (T i) (frequencyBand (B i))
    (norm_bandVector (hB i)) (bandVector_mem_frequencyBand (B i))
  refine ⟨R, fun i ↦ by simpa only [frequencyBand_starProjection_sub_line] using hR i, ?_⟩
  have heq (i : ι) : hilbertTrace (R i) = -hilbertTrace (polarRankOne (T i) (bandVector (B i))) := by
    rw [htr, polarRankOne, hilbertTrace_smulRight]
    rfl
  simpa only [heq, T] using
    (tendsto_hilbertTrace_compactDilation_multiplier_spatial hB hh hL φ Q hQ C hC hQC).neg

end RiemannMasullo.FlatPolar
