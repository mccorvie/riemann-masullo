module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3_TraceClass
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.ForMathlib.Analysis.Fourier.PaleyWienerStrip

/-! # Zero clusters for Theorem 10.3.2.1: the block of one cluster, with its bound

`Sec3_Clusters` and `Sec3_TraceClass` prove that the trace norms of the cluster blocks of the
spectral convolution are summable, for clusters and bounds that their statements do not name.
This file states the same estimates for one cluster at a time, with the cluster and the bound in
the statement, so that they can be used for several tests with common clusters. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "Q(" a ", " hI ", " hs ")" => spectralSobolevQuotient F a hI hs
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat

variable (a : ℝ)

local notation "Z(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

-- Select the norm topology directly when using the locally convex nuclear ideal, as in `Sec3`.
attribute [local instance] instSpectralQuotientPolynormableSec3

/-- An operator that acts on the jets of a finite set of zeros as the given operator does, and
annihilates the jets of all the other zeros, is the block of that set, and the trace norm of the
block is at most the number of jets of the set times the norm of the operator. -/
theorem spectralClusterBlock_traceNorm_le_of_interpolant
    {H J Z : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x Λ)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (hjet : Bijective (fun j : (z : Z) × Fin (N z) ↦ jet j.1 j.2))
    (K : Finset Z) (Ψ : H →L[ℂ] H)
    (hin : ∀ z ∈ K, ∀ (m : Fin (N z)) (u : H), Λ (jet z m) (Ψ u) = Λ (jet z m) (A u))
    (hout : ∀ z ∉ K, ∀ (m : Fin (N z)) (u : H), Λ (jet z m) (Ψ u) = 0) :
    ∃ R : nuclearEndomorphisms H, R.val = spectralConvolutionFiniteSum A x Λ K N jet ∧
      traceNorm R ≤ ((∑ z ∈ K, N z : ℕ) : ℝ) * ‖Ψ‖ := by
  let R : nuclearEndomorphisms H := ⟨spectralConvolutionFiniteSum A x Λ K N jet,
    (nuclearEndomorphisms H).sum_mem fun z _ ↦ (nuclearEndomorphisms H).sum_mem fun m _ ↦
      smulRight_mem_nuclearEndomorphisms _ _⟩
  refine ⟨R, rfl, ?_⟩
  have h := spectralStripConvolution_summable_clusterTraceNorms_of_summable_clusterNorms_rank R _
    (spectralStripConvolution_summable_clusterTraceNorms_of_summable_clusterNorms_range
      A x Λ K N jet)
  have hR : R.val = Ψ :=
    spectralStripConvolution_summable_clusterTraceNorms_of_kernels_block A x Λ hb N jet hjet K Ψ
      hin hout
  rwa [hR] at h

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. The kernel of one cluster from an entire
multiplier. Let `m` be an entire function bounded by `B / (1 + t²)` on the closed vertical strip
`|Re u| ≤ β`, with `β` larger than the half-width `α` of the strip of the zeros, and `ω` an
angular component. Then there is a kernel on the idele class group whose integral against the
weight of the strip is at most `B / 2` times the integral of `(1 + |y|) ^ (s / 2)` against
`exp (-(β - α) |y|)`, whose logarithmic Mellin moments at the basepoint character of `ω` and an
exponent of the strip are the derivatives of `m` there, and whose moments at the basepoint
characters of all the other components vanish. The kernel is the inverse of the basepoint
character of `ω` times the Paley–Wiener kernel of `m` (`exists_laplaceKernel_of_strip_bound`) of
the logarithm of the norm.
This is the construction inside
`spectralStripConvolution_summable_clusterTraceNorms_of_multipliers` and
`spectralStripConvolution_summable_clusterTraceNorms_of_scalarKernels` of `Sec3_Clusters`, for
one cluster. -/
theorem spectralStripCluster_exists_kernel_of_multiplier
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s β : ℝ} (hα : 0 ≤ α) (hβ : α < β) (ω : PontryaginDual C₁)
    (m : ℂ → ℂ) (hm : Differentiable ℂ m) (B : ℝ)
    (hbound : ∀ u : ℂ, |u.re| ≤ β → ‖m u‖ ≤ B / (1 + u.im ^ 2)) :
    ∃ κ : C𝔽 → ℂ, AEStronglyMeasurable κ μ𝔽 ∧
      Integrable (fun g : C𝔽 ↦ ‖κ g‖ *
        (max (Real.exp (-α * logIdeleClassNorm F g)) (Real.exp (α * logIdeleClassNorm F g)) *
          (1 + |logIdeleClassNorm F g|) ^ (s / 2))) μ𝔽 ∧
      ∫ g : C𝔽, ‖κ g‖ *
        (max (Real.exp (-α * logIdeleClassNorm F g)) (Real.exp (α * logIdeleClassNorm F g)) *
          (1 + |logIdeleClassNorm F g|) ^ (s / 2)) ∂μ𝔽 ≤
        B / 2 * ∫ y : ℝ, (1 + |y|) ^ (s / 2) * Real.exp (-(β - α) * |y|) ∧
      (∀ (η : PontryaginDual C𝔽) (b t : ℝ), |b| ≤ α → ∀ q : ℕ, Integrable (fun g : C𝔽 ↦ κ g *
        ideleClassNormTwist η (shift(b, t)) g * (logIdeleClassNorm F g : ℂ) ^ q) μ𝔽) ∧
      (∀ (b t : ℝ), |b| ≤ α → ∀ q : ℕ,
        ∫ g : C𝔽, κ g * ideleClassNormTwist (χ ω) (shift(b, t)) g *
          (logIdeleClassNorm F g : ℂ) ^ q ∂μ𝔽 = iteratedDeriv q m (shift(b, t))) ∧
      ∀ ω' : PontryaginDual C₁, ω' ≠ ω → ∀ (w : ℂ) (q : ℕ),
        ∫ g : C𝔽, κ g * ideleClassNormTwist (χ ω') w g *
          (logIdeleClassNorm F g : ℂ) ^ q ∂μ𝔽 = 0 := by
  obtain ⟨c, hc0, hc⟩ :=
    spectralStripConvolution_summable_clusterTraceNorms_of_multipliers_map_logNorm (F := F)
  have hcpos : (0 : ℝ) < c := lt_of_le_of_ne c.coe_nonneg (NNReal.coe_ne_zero.mpr hc0).symm
  have hcC : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
  have hβ0 : 0 < β := hα.trans_lt hβ
  obtain ⟨k, hkc, hkb, hkm⟩ := RiemannMasullo.exists_laplaceKernel_of_strip_bound hm hβ0 hbound
  have hB : 0 ≤ B := by
    have h := (norm_nonneg _).trans (hbound 0 (by simpa using hβ0.le))
    simpa using h
  let L : C𝔽 → ℝ := logIdeleClassNorm F
  have hLc : Continuous L :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (isProperMap_ideleClassNorm F).continuous)).log
      fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  let wt (y : ℝ) : ℝ := max (Real.exp (-α * y)) (Real.exp (α * y)) * (1 + |y|) ^ (s / 2)
  have hwtc : Continuous wt :=
    (Continuous.max (by fun_prop) (by fun_prop)).mul
      ((continuous_const.add continuous_abs).rpow_const fun y ↦
        Or.inl (by positivity : (0 : ℝ) < 1 + |y|).ne')
  have hwt0 (y : ℝ) : 0 ≤ wt y := by
    change 0 ≤ max _ _ * _
    positivity
  have hwt (y : ℝ) : wt y = Real.exp (α * |y|) * (1 + |y|) ^ (s / 2) := by
    change max (Real.exp (-α * y)) (Real.exp (α * y)) * _ = _
    congr 1
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy, max_eq_right (Real.exp_le_exp.mpr (by nlinarith))]
    · rw [abs_of_nonpos hy, max_eq_left (Real.exp_le_exp.mpr (by nlinarith))]
      ring_nf
  have hE : Integrable (fun y : ℝ ↦ (1 + |y|) ^ (s / 2) * Real.exp (-(β - α) * |y|)) :=
    RiemannMasullo.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs (sub_pos.mpr hβ) _
  have hexp (y : ℝ) : Real.exp (-β * |y|) * Real.exp (α * |y|) = Real.exp (-(β - α) * |y|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpt (y : ℝ) : ‖k y‖ * wt y ≤
      B / 2 * ((1 + |y|) ^ (s / 2) * Real.exp (-(β - α) * |y|)) := by
    rw [hwt]
    calc ‖k y‖ * (Real.exp (α * |y|) * (1 + |y|) ^ (s / 2))
        ≤ (B / 2 * Real.exp (-β * |y|)) * (Real.exp (α * |y|) * (1 + |y|) ^ (s / 2)) :=
          mul_le_mul_of_nonneg_right (hkb y) (by positivity)
      _ = B / 2 * ((1 + |y|) ^ (s / 2) * (Real.exp (-β * |y|) * Real.exp (α * |y|))) := by ring
      _ = _ := by rw [hexp]
  have hkwt : Integrable (fun y : ℝ ↦ ‖k y‖ * wt y) :=
    (hE.const_mul (B / 2)).mono' (hkc.norm.mul hwtc).aestronglyMeasurable
      (.of_forall fun y ↦ by
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hwt0 y))]
        exact hpt y)
  -- Integrals over the class group of functions of the logarithm of the norm.
  have hpull {f : ℝ → ℝ} (hf : Continuous f) (hfi : Integrable f) :
      Integrable (fun g : C𝔽 ↦ f (L g)) μ𝔽 := by
    have h1 : Integrable f (Measure.map (logIdeleClassNorm F) μ𝔽) := by
      rw [hc]
      exact hfi.smul_measure_nnreal
    exact (integrable_map_measure hf.aestronglyMeasurable hLc.aemeasurable).mp h1
  have hpullR {f : ℝ → ℝ} (hf : Continuous f) :
      ∫ g : C𝔽, f (L g) ∂μ𝔽 = (c : ℝ) * ∫ y : ℝ, f y := by
    rw [← integral_map hLc.aemeasurable hf.aestronglyMeasurable, hc,
      integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  have hpullC {f : ℝ → ℂ} (hf : Continuous f) :
      ∫ g : C𝔽, f (L g) ∂μ𝔽 = ((c : ℝ) : ℂ) * ∫ y : ℝ, f y := by
    rw [← integral_map hLc.aemeasurable hf.aestronglyMeasurable, hc,
      integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  -- The kernel on the class group.
  let κ (g : C𝔽) : ℂ := (((χ ω g)⁻¹ : Circle) : ℂ) * (((c : ℝ) : ℂ)⁻¹ * k (L g))
  have hκnorm (g : C𝔽) : ‖κ g‖ = (c : ℝ)⁻¹ * ‖k (L g)‖ := by
    change ‖(((χ ω g)⁻¹ : Circle) : ℂ) * (((c : ℝ) : ℂ)⁻¹ * k (L g))‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hcpos.le]
  have hκm : AEStronglyMeasurable κ μ𝔽 :=
    ((continuous_subtype_val.comp ((χ ω).continuous.inv)).mul
      (continuous_const.mul (hkc.comp hLc))).aestronglyMeasurable
  have htw (η : PontryaginDual C𝔽) (w : ℂ) (g : C𝔽) :=
    spectralStripConvolution_summable_clusterTraceNorms_of_scalarKernels_twist (F := F) η w g
  refine ⟨κ, hκm, ?_, ?_, fun η b t hbα q ↦ ?_, fun b t hbα q ↦ ?_, fun ω' hω' w q ↦ ?_⟩
  · refine (hpull (f := fun y ↦ (c : ℝ)⁻¹ * (‖k y‖ * wt y))
      (continuous_const.mul (hkc.norm.mul hwtc)) (hkwt.const_mul _)).congr (.of_forall fun g ↦ ?_)
    change (c : ℝ)⁻¹ * (‖k (L g)‖ * wt (L g)) = ‖κ g‖ * wt (L g)
    rw [hκnorm, mul_assoc]
  · have h1 : ∫ g : C𝔽, ‖κ g‖ * wt (L g) ∂μ𝔽 = ∫ y : ℝ, ‖k y‖ * wt y := by
      have h2 := hpullR (f := fun y ↦ (c : ℝ)⁻¹ * (‖k y‖ * wt y))
        (continuous_const.mul (hkc.norm.mul hwtc))
      have h3 : (c : ℝ) * ∫ y : ℝ, (c : ℝ)⁻¹ * (‖k y‖ * wt y) = ∫ y : ℝ, ‖k y‖ * wt y := by
        rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
      rw [← h3, ← h2]
      refine integral_congr_ae (.of_forall fun g ↦ ?_)
      change ‖κ g‖ * wt (L g) = (c : ℝ)⁻¹ * (‖k (L g)‖ * wt (L g))
      rw [hκnorm, mul_assoc]
    change ∫ g : C𝔽, ‖κ g‖ * wt (L g) ∂μ𝔽 ≤ _
    rw [h1, ← integral_const_mul]
    exact integral_mono hkwt (hE.const_mul _) hpt
  · -- The moments are integrable.
    have hdom := hpull (f := fun y ↦ (c : ℝ)⁻¹ * (B / 2) *
      (|y| ^ q * Real.exp (-(β - α) * |y|))) (by fun_prop)
      ((RiemannMasullo.integrable_abs_pow_mul_exp_neg_mul_abs (sub_pos.mpr hβ) q).const_mul _)
    refine hdom.mono' ((hκm.mul
      (ideleClassNormTwist η (shift(b, t))).continuous.aestronglyMeasurable).mul
      ((Complex.continuous_ofReal.comp hLc).pow q).aestronglyMeasurable) (.of_forall fun g ↦ ?_)
    change ‖κ g * ideleClassNormTwist η (shift(b, t)) g * (L g : ℂ) ^ q‖ ≤
      (c : ℝ)⁻¹ * (B / 2) * (|L g| ^ q * Real.exp (-(β - α) * |L g|))
    rw [norm_mul, norm_mul, hκnorm, htw, norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp,
      norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hre : (shift(b, t) * ((L g : ℝ) : ℂ)).re = b * L g := by
      simp [Complex.mul_re]
    rw [hre]
    have hby : Real.exp (b * L g) ≤ Real.exp (α * |L g|) := by
      refine Real.exp_le_exp.mpr ?_
      calc b * L g ≤ |b * L g| := le_abs_self _
        _ = |b| * |L g| := abs_mul _ _
        _ ≤ α * |L g| := mul_le_mul_of_nonneg_right hbα (abs_nonneg _)
    calc (c : ℝ)⁻¹ * ‖k (L g)‖ * Real.exp (b * L g) * |L g| ^ q
        ≤ (c : ℝ)⁻¹ * (B / 2 * Real.exp (-β * |L g|)) * Real.exp (α * |L g|) * |L g| ^ q := by
          have h1 : (c : ℝ)⁻¹ * ‖k (L g)‖ ≤ (c : ℝ)⁻¹ * (B / 2 * Real.exp (-β * |L g|)) :=
            mul_le_mul_of_nonneg_left (hkb (L g)) (inv_nonneg.mpr hcpos.le)
          have h2 : 0 ≤ (c : ℝ)⁻¹ * (B / 2 * Real.exp (-β * |L g|)) :=
            mul_nonneg (inv_nonneg.mpr hcpos.le)
              (mul_nonneg (div_nonneg hB zero_le_two) (Real.exp_pos _).le)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul h1 hby (Real.exp_pos _).le h2) (by positivity)
      _ = (c : ℝ)⁻¹ * (B / 2) *
            (|L g| ^ q * (Real.exp (-β * |L g|) * Real.exp (α * |L g|))) := by ring
      _ = _ := by rw [hexp]
  · -- The moments at the component are the derivatives of the multiplier.
    have hre : |(shift(b, t)).re| < β := by
      have h1 : (shift(b, t)).re = b := by simp
      rw [h1]
      exact hbα.trans_lt hβ
    have h2 := hpullC (f := fun y : ℝ ↦ ((c : ℝ) : ℂ)⁻¹ *
      (k y * (Complex.exp (shift(b, t) * (y : ℂ)) * (y : ℂ) ^ q)))
      (by fun_prop)
    have h3 : ((c : ℝ) : ℂ) * ∫ y : ℝ, ((c : ℝ) : ℂ)⁻¹ *
        (k y * (Complex.exp (shift(b, t) * (y : ℂ)) * (y : ℂ) ^ q)) =
        iteratedDeriv q m (shift(b, t)) := by
      rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hcC, one_mul, hkm _ hre q]
    rw [← h3, ← h2]
    refine integral_congr_ae (.of_forall fun g ↦ ?_)
    change (((χ ω g)⁻¹ : Circle) : ℂ) * (((c : ℝ) : ℂ)⁻¹ * k (L g)) *
      ideleClassNormTwist (χ ω) (shift(b, t)) g * (L g : ℂ) ^ q =
      ((c : ℝ) : ℂ)⁻¹ *
        (k (L g) * (Complex.exp (shift(b, t) * (L g : ℂ)) * (L g : ℂ) ^ q))
    rw [htw]
    have hone : (((χ ω g)⁻¹ : Circle) : ℂ) * (χ ω g : ℂ) = 1 := by
      rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
    linear_combination (((c : ℝ) : ℂ)⁻¹ * k (L g) *
      Complex.exp (shift(b, t) * (L g : ℂ)) * (L g : ℂ) ^ q) * hone
  · -- The moments at the other components vanish.
    have horth := spectralStripConvolution_summable_clusterTraceNorms_of_scalarKernels_orthogonal
      (F := F) χ hχ hω' w (fun y : ℝ ↦ ((c : ℝ) : ℂ)⁻¹ * k y * (y : ℂ) ^ q)
    refine Eq.trans (integral_congr_ae (.of_forall fun g ↦ ?_)) horth
    change (((χ ω g)⁻¹ : Circle) : ℂ) * (((c : ℝ) : ℂ)⁻¹ * k (L g)) *
      ideleClassNormTwist (χ ω') w g * (L g : ℂ) ^ q =
      (((χ ω g)⁻¹ : Circle) : ℂ) * (((c : ℝ) : ℂ)⁻¹ * k (L g) * (L g : ℂ) ^ q) *
        ideleClassNormTwist (χ ω') w g
    ring

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. The block of one cluster from an entire multiplier,
with its bound. Let `K` be a finite set of zeros of the angular component `ω`, and `m` an entire
function, bounded by `B / (1 + t²)` on a closed vertical strip wider than the strip of the
zeros, whose derivatives below the surviving multiplicity agree with the logarithmic Mellin
moments of the test at the zeros of `K` and vanish at the other zeros of the component. Then the
finite section of the spectral convolution over `K` is nuclear, and its trace norm is at most
the number of jets of `K` times `B / 2` times the integral of `(1 + |y|) ^ (s / 2)` against
`exp (-(β - α) |y|)`.
This is the estimate inside `spectralStripConvolution_summable_clusterTraceNorms_of_multipliers`
of `Sec3_Clusters` for one cluster: the kernel of
`spectralStripCluster_exists_kernel_of_multiplier` gives, by
`exists_spectralStripKernelOperator` of `Sec3`, an operator with the jets of the block.
Deviation: Stated for every Sobolev order `s ≥ 0`; §10.3 of the paper assumes `s > 1` (p. 455). -/
theorem spectralStripClusterBlock_traceNorm_le_of_multiplier
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s β : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hβ : α < β) (φ : BruhatCompactSupport C𝔽)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (K : Finset Z(χ, α)) (ω : PontryaginDual C₁) (hK : ∀ z ∈ K, z.val.1 = ω)
    (m : ℂ → ℂ) (hm : Differentiable ℂ m) (B : ℝ)
    (hbound : ∀ u : ℂ, |u.re| ≤ β → ‖m u‖ ≤ B / (1 + u.im ^ 2))
    (hin : ∀ z ∈ K, ∀ q < N(χ, α, s, z),
      iteratedDeriv q m (shift(z.val.2.1, z.val.2.2)) =
      ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ z.val.1) (shift(z.val.2.1, z.val.2.2)) g *
        (logIdeleClassNorm F g : ℂ) ^ q ∂μ𝔽)
    (hout : ∀ z : Z(χ, α), z ∉ K → z.val.1 = ω → ∀ q < N(χ, α, s, z),
      iteratedDeriv q m (shift(z.val.2.1, z.val.2.2)) = 0) :
    ∃ R : nuclearEndomorphisms Q(a, hStrip(hα), hs),
      R.val = spectralConvolutionFiniteSum
        (spectralConvolution (F := F) a hStrip(hα) hs φ) x Λ K
        (fun z ↦ N(χ, α, s, z)) (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩) ∧
      traceNorm R ≤ ((∑ z ∈ K, N(χ, α, s, z) : ℕ) : ℝ) *
        (B / 2 * ∫ y : ℝ, (1 + |y|) ^ (s / 2) * Real.exp (-(β - α) * |y|)) := by
  refine Exists.elim (spectralStripCluster_exists_kernel_of_multiplier (s := s) χ hχ hα hβ ω m hm
    B hbound) fun κ hκ ↦ ?_
  refine Exists.elim (exists_spectralStripKernelOperator a hα hs χ Λ hj φ κ hκ.1 hκ.2.1)
    fun Ψ hΨ ↦ ?_
  have hzα (z : Z(χ, α)) : |z.val.2.1| ≤ α := abs_le.mpr z.property.1
  have hmomInt (z : Z(χ, α)) (q : ℕ) := hκ.2.2.2.1 (χ z.val.1) z.val.2.1 z.val.2.2 (hzα z) q
  let count (z : Z(χ, α)) := N(χ, α, s, z)
  let jet (z : Z(χ, α)) (m : Fin (count z)) : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩
  let index (j : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s) :
      (z : Z(χ, α)) × Fin (count z) :=
    ⟨⟨(j.val.1, j.val.2.1, j.val.2.2.1), SpectralStripJetIndex.mem_strip_order_pos hα j⟩,
      ⟨j.val.2.2.2, j.property⟩⟩
  let equiv : ((z : Z(χ, α)) × Fin (count z)) ≃
      SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s :=
    ⟨fun zm ↦ jet zm.1 zm.2, index, fun _ ↦ rfl, fun _ ↦ rfl⟩
  refine Exists.imp (fun R hR ↦ ⟨hR.1, hR.2.trans
    (mul_le_mul_of_nonneg_left (hΨ.1.trans hκ.2.2.1) (Nat.cast_nonneg _))⟩)
    (spectralClusterBlock_traceNorm_le_of_interpolant
      (spectralConvolution (F := F) a hStrip(hα) hs φ) x Λ hb count jet equiv.bijective K Ψ
      (fun z hz m u ↦ ((hΨ.2 z (fun q _ ↦ hmomInt z q)).1 (fun q hq ↦ ?_)) m u)
      (fun z hz m u ↦ ((hΨ.2 z (fun q _ ↦ hmomInt z q)).2 (fun q hq ↦ ?_)) m u))
  · rw [hK z hz, hκ.2.2.2.2.1 z.val.2.1 z.val.2.2 (hzα z) q, ← hK z hz]
    exact hin z hz q hq
  · by_cases hzc : z.val.1 = ω
    · rw [hzc, hκ.2.2.2.2.1 z.val.2.1 z.val.2.2 (hzα z) q]
      exact hout z hz hzc q hq
    · exact hκ.2.2.2.2.2 z.val.1 hzc _ q

/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. The block of one cluster from data on the boundary
of its rectangle, with its bound. Let `ϑ` be an entire function of polynomial growth on a wide
vertical strip that vanishes at every zero of the angular component `ω` to at least the
surviving multiplicity, and let `K` be the set of the zeros of the component with heights in
`[T₁, T₂)`, where `T₁ + 1 ≤ T₂ ≤ T₁ + 3`. If `ϑ` is at least `ℓ > 0` and the Mellin transform of
the test at the basepoint character of `ω` is at most `b` on the boundary of the rectangle
`[-X, X] × [T₁, T₂]`, then the finite section of the spectral convolution over `K` is nuclear,
with trace norm at most the number of jets of `K` times
`rectInterpolantGaussianConstant X β A * (b / ℓ * (1 + |T₁|) ^ (A + 2)) / 2` times the integral
of `(1 + |y|) ^ (s / 2)` against `exp (-(β - α) |y|)`.
This is the estimate inside
`spectralStripConvolution_summable_clusterTraceNorms_of_boundaryData_on` of `Sec3_Clusters` for
one cluster, with the same multiplier: the contour integral `rectInterpolant` with `ϑ` times a
Gaussian centred at the height `T₁`. The test enters only through `b`.
Deviation: Stated for every Sobolev order `s ≥ 0`; §10.3 of the paper assumes `s > 1` (p. 455). -/
theorem spectralStripClusterBlock_traceNorm_le_of_boundaryData
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    {α s β X : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (hβ : α < β) (hβX : β < X)
    (φ : BruhatCompactSupport C𝔽)
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → StrongDual ℂ Q(a, hStrip(hα), hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (ω : PontryaginDual C₁) (A : ℕ) (ϑ : ℂ → ℂ) (hϑ : Differentiable ℂ ϑ)
    (hgrowth : ∀ u : ℂ, |u.re| ≤ X + 2 → ‖ϑ u‖ ≤ (1 + |u.im|) ^ A)
    (hord : ∀ z : Z(χ, α), z.val.1 = ω → ((N(χ, α, s, z) : ℕ) : ℕ∞) ≤
      analyticOrderAt ϑ (shift(z.val.2.1, z.val.2.2)))
    (T₁ T₂ : ℝ) (hT₁ : T₁ + 1 ≤ T₂) (hT₂ : T₂ ≤ T₁ + 3)
    (b ℓ : ℝ) (hℓ : 0 < ℓ)
    (hlow : ∀ w ∈ rectBoundary (-X) X T₁ T₂, ℓ ≤ ‖ϑ w‖)
    (hφb : ∀ w ∈ rectBoundary (-X) X T₁ T₂,
      ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ ω) w g ∂μ𝔽‖ ≤ b)
    (K : Finset Z(χ, α))
    (hK : ∀ z : Z(χ, α), z ∈ K ↔ z.val.1 = ω ∧ T₁ ≤ z.val.2.2 ∧ z.val.2.2 < T₂) :
    ∃ R : nuclearEndomorphisms Q(a, hStrip(hα), hs),
      R.val = spectralConvolutionFiniteSum
        (spectralConvolution (F := F) a hStrip(hα) hs φ) x Λ K
        (fun z ↦ N(χ, α, s, z)) (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩) ∧
      traceNorm R ≤ ((∑ z ∈ K, N(χ, α, s, z) : ℕ) : ℝ) *
        (rectInterpolantGaussianConstant X β A * (b / ℓ * (1 + |T₁|) ^ (A + 2)) / 2 *
          ∫ y : ℝ, (1 + |y|) ^ (s / 2) * Real.exp (-(β - α) * |y|)) := by
  have hβ0 : 0 < β := hα.trans_lt hβ
  have hX : 0 < X := hβ0.trans hβX
  have hx : -X ≤ X := by linarith
  have hy : T₁ ≤ T₂ := by linarith
  have hΦ := spectralStripTest_mellin_iteratedDeriv (F := F) (χ ω) φ
  let θ (u : ℂ) : ℂ := ϑ u * Complex.exp ((u - T₁ * Complex.I) ^ 2)
  have hθ : Differentiable ℂ θ := hϑ.mul (((differentiable_id.sub_const _).pow 2).cexp)
  have hθne : ∀ w ∈ rectBoundary (-X) X T₁ T₂, θ w ≠ 0 := fun w hw ↦
    mul_ne_zero (fun h0 ↦ by
      have := hlow w hw
      rw [h0, norm_zero] at this
      linarith) (Complex.exp_ne_zero _)
  have hθord (z : Z(χ, α)) (hz : z.val.1 = ω) :
      ((N(χ, α, s, z) : ℕ) : ℕ∞) ≤ analyticOrderAt θ (shift(z.val.2.1, z.val.2.2)) := by
    have h1 := hord z hz
    have hE : AnalyticAt ℂ (fun u : ℂ ↦ Complex.exp ((u - T₁ * Complex.I) ^ 2))
        (shift(z.val.2.1, z.val.2.2)) :=
      (((differentiable_id.sub_const _).pow 2).cexp).analyticAt _
    change _ ≤ analyticOrderAt (ϑ * fun u : ℂ ↦ Complex.exp ((u - T₁ * Complex.I) ^ 2)) _
    rw [analyticOrderAt_mul (hϑ.analyticAt _) hE]
    exact h1.trans le_self_add
  have hzero (z : Z(χ, α)) (hz : z.val.1 = ω) (hN : 0 < N(χ, α, s, z)) :
      θ (shift(z.val.2.1, z.val.2.2)) = 0 := by
    have h1 := hθord z hz
    by_contra hne
    rw [(hθ.analyticAt _).analyticOrderAt_eq_zero.mpr hne] at h1
    have h2 : N(χ, α, s, z) = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp h1
    omega
  have hre (z : Z(χ, α)) : (shift(z.val.2.1, z.val.2.2)).re = z.val.2.1 := by simp
  have him (z : Z(χ, α)) : (shift(z.val.2.1, z.val.2.2)).im = z.val.2.2 := by simp
  have hbX (z : Z(χ, α)) : -X < z.val.2.1 ∧ z.val.2.1 < X :=
    ⟨by linarith [z.property.1.1], by linarith [z.property.1.2]⟩
  let m₀ : ℂ → ℂ :=
    rectInterpolant (fun u ↦ ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ ω) u g ∂μ𝔽)
      θ (-X) X T₁ T₂
  have hm₀ : Differentiable ℂ m₀ := differentiable_rectInterpolant hΦ.1 hθ hx hy hθne
  have hbound₀ (u : ℂ) (hu : |u.re| ≤ β) : ‖m₀ u‖ ≤
      rectInterpolantGaussianConstant X β A * (b / ℓ * (1 + |T₁|) ^ (A + 2)) /
        (1 + u.im ^ 2) :=
    norm_rectInterpolant_gaussian_le hϑ hΦ.1 hβ0 hβX hT₁ hT₂ hgrowth hℓ hlow hφb hu
  have key := spectralStripClusterBlock_traceNorm_le_of_multiplier a χ hχ hα hs hβ φ x Λ hb hj K ω
    (fun z hz ↦ ((hK z).mp hz).1) m₀ hm₀ _ hbound₀ (fun z hz q hq ↦ ?_)
    (fun z hz hzc q hq ↦ ?_)
  · refine Exists.imp (fun R hR ↦ ⟨hR.1, hR.2.trans_eq ?_⟩) key
    ring
  · -- At a zero of the cluster the multiplier has the derivatives of the Mellin transform.
    obtain ⟨hz1, hz2, hz3⟩ := (hK z).mp hz
    have hz0 := hzero z hz1 (Nat.zero_lt_of_lt hq)
    have hstrict : T₁ < z.val.2.2 := by
      rcases hz2.eq_or_lt with heq | hlt
      · exact absurd hz0 (hθne _ (mem_rectBoundary_horizontal (x := z.val.2.1)
          (y := z.val.2.2) ⟨(hbX z).1.le, (hbX z).2.le⟩ (Or.inl heq.symm)))
      · exact hlt
    change iteratedDeriv q
      (rectInterpolant (fun u ↦ ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ ω) u g ∂μ𝔽)
        θ (-X) X T₁ T₂) (shift(z.val.2.1, z.val.2.2)) = _
    rw [iteratedDeriv_rectInterpolant_of_mem hΦ.1 hθ hx hy hθne
      (by rw [hre]; exact (hbX z).1) (by rw [hre]; exact (hbX z).2)
      (by rw [him]; exact hstrict) (by rw [him]; exact hz3) (hθord z hz1) hq,
      hΦ.2 q, hz1]
  · -- At a zero of the same component outside the cluster its derivatives vanish.
    have hz0 := hzero z hzc (Nat.zero_lt_of_lt hq)
    refine iteratedDeriv_rectInterpolant_of_notMem hΦ.1 hθ hx hy hθne (fun hmem ↦ ?_)
      (hθord z hzc) hq
    obtain ⟨-, ht1, ht2⟩ := hmem
    rw [him] at ht1 ht2
    rcases ht2.eq_or_lt with heq | hlt
    · exact hθne _ (mem_rectBoundary_horizontal (x := z.val.2.1) (y := z.val.2.2)
        ⟨(hbX z).1.le, (hbX z).2.le⟩ (Or.inr heq)) hz0
    · exact hz ((hK z).mpr ⟨hzc, ht1, hlt⟩)

/-- Paper: Theorems 10.3.1.1(1)–(2) and 10.3.2.1(1)–(2), pp. 448–455. Common clusters for a
test and every test that it dominates. For every test `φ` there are a choice `χ` of the unitary
extensions of the norm-one characters, a half-width `X`, heights `T ω k`, bounds `φb ω k`, an
exponent `p`, clusters `K (ω, k)` of zeros, pairwise disjoint and covering all the zeros, and a
summable family `bd` of nonnegative numbers, such that:
* on the boundary of the rectangle `[-X, X] × [T ω k, T ω (k + 1)]` the Mellin transform of `φ`
  at the basepoint character of `ω`, with the exponent shifted by `i t`, is at most
  `(1 + |t|) ^ p * φb ω k`;
* for every test `ψ` whose Mellin transform is at most `c * φb ω k` on these boundaries, and
  every Markushevich basis realizing the strip jets, the block of the spectral convolution by
  `ψ` over the cluster `K i` is nuclear with trace norm at most `c * bd i`.
The clusters and the numbers `bd i` do not depend on `ψ`. For `ψ = φ` and `c = 1` this is the
clustered statement `spectralStripConvolution_summable_clusterTraceNorms` of `Sec3_TraceClass`
with its clusters and bounds named.
The data are those of `spectralStripConvolution_exists_clusterBoundaryData_shift`: the cluster
`K (ω, k)` is the set of the zeros of the component `ω` with heights in `[T ω k, T ω (k + 1))`,
and `bd (ω, k)` is its number of jets times the bound of
`spectralStripClusterBlock_traceNorm_le_of_boundaryData`.
Reconstruction: The paper does not state this. It is the form of the trace-class estimate of
Theorem 10.3.2.1 that a family of tests needs: one set of clusters, and a bound that depends on
the test only through the size of its Mellin transform on fixed contours.
Deviation: Stated for every Sobolev order `s ≥ 0`; §10.3 of the paper assumes `s > 1` (p. 455). -/
theorem spectralStripConvolution_exists_commonClusters
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽) :
    ∃ (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (X : ℝ) (T φb : PontryaginDual C₁ → ℤ → ℝ)
      (p : ℕ) (K : PontryaginDual C₁ × ℤ → Finset Z(χ, α)) (bd : PontryaginDual C₁ × ℤ → ℝ),
      IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω) ∧ 0 < X ∧
      (∀ i j, i ≠ j → Disjoint (K i) (K j)) ∧ (∀ z : Z(χ, α), ∃ i, z ∈ K i) ∧
      (∀ i, 0 ≤ bd i) ∧ Summable bd ∧
      (∀ ω k, ∀ w ∈ rectBoundary (-X) X (T ω k) (T ω (k + 1)), ∀ t : ℝ,
        ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ ω) (w + (t : ℂ) * Complex.I) g ∂μ𝔽‖ ≤
          (1 + |t|) ^ p * φb ω k) ∧
      ∀ (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs))
        (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s →
          StrongDual ℂ Q(a, hStrip(hα), hs)),
        IsSpectralMarkushevichBasis x Λ →
        (∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs (Λ j) =
          (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs j).toLp
            (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) →
        ∀ (ψ : BruhatCompactSupport C𝔽) (c : ℝ),
          (∀ ω k, ∀ w ∈ rectBoundary (-X) X (T ω k) (T ω (k + 1)),
            ‖∫ g : C𝔽, ψ.val g * ideleClassNormTwist (χ ω) w g ∂μ𝔽‖ ≤ c * φb ω k) →
          ∀ i, ∃ R : nuclearEndomorphisms Q(a, hStrip(hα), hs),
            R.val = spectralConvolutionFiniteSum
              (spectralConvolution (F := F) a hStrip(hα) hs ψ) x Λ (K i)
              (fun z ↦ N(χ, α, s, z))
              (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩) ∧
            traceNorm R ≤ c * bd i := by
  choose χ β X A ϑ T φb ℓ p hfin hχ hαβ hβX hϑ hgrowth hord hT hℓ hlow hφb hsum using
    spectralStripConvolution_exists_clusterBoundaryData_shift (s := s) a hα φ
  have hX : 0 < X := (hα.trans_lt hαβ).trans hβX
  have hT1 (ω : PontryaginDual C₁) (k : ℤ) : T ω k + 1 ≤ T ω (k + 1) := by
    have h1 := (hT ω k).2
    have h2 := (hT ω (k + 1)).1
    push_cast at h2
    linarith
  have hT3 (ω : PontryaginDual C₁) (k : ℤ) : T ω (k + 1) ≤ T ω k + 3 := by
    have h1 := (hT ω k).1
    have h2 := (hT ω (k + 1)).2
    push_cast at h2
    linarith
  have hTmono (ω : PontryaginDual C₁) {j j' : ℤ} (h : j ≤ j') : T ω j ≤ T ω j' := by
    rcases h.eq_or_lt with rfl | hlt
    · exact le_rfl
    · have h1 := (hT ω j).2
      have h2 := (hT ω j').1
      have h3 : (j : ℝ) + 1 ≤ j' := by exact_mod_cast hlt
      linarith
  let K (i : PontryaginDual C₁ × ℤ) : Finset Z(χ, α) := (hfin i.1 i.2).toFinset
  have hK (i : PontryaginDual C₁ × ℤ) (z : Z(χ, α)) :
      z ∈ K i ↔ z.val.1 = i.1 ∧ T i.1 i.2 ≤ z.val.2.2 ∧ z.val.2.2 < T i.1 (i.2 + 1) :=
    (hfin i.1 i.2).mem_toFinset
  let I₀ : ℝ := ∫ y : ℝ, (1 + |y|) ^ (s / 2) * Real.exp (-(β - α) * |y|)
  have hI₀ : 0 ≤ I₀ := integral_nonneg fun y ↦ by positivity
  let bd (i : PontryaginDual C₁ × ℤ) : ℝ := ((∑ z ∈ K i, N(χ, α, s, z) : ℕ) : ℝ) *
    (rectInterpolantGaussianConstant X β (A i.1) *
      (φb i.1 i.2 / ℓ i.1 i.2 * (1 + |T i.1 i.2|) ^ (A i.1 + 2)) / 2 * I₀)
  have hφb0 (ω : PontryaginDual C₁) (k : ℤ) : 0 ≤ φb ω k := by
    have hmem : ((X : ℝ) : ℂ) + (T ω k : ℝ) * Complex.I ∈
        rectBoundary (-X) X (T ω k) (T ω (k + 1)) :=
      mem_rectBoundary_vertical ⟨le_rfl, by linarith [hT1 ω k]⟩ (Or.inr rfl)
    have h := (norm_nonneg _).trans (hφb ω k _ hmem 0)
    simpa using h
  refine ⟨χ, X, T, φb, p, K, bd, hχ, hX, fun i j hij ↦ ?_, fun z ↦ ?_, fun i ↦ ?_, ?_, hφb,
    fun x Λ hb hj ψ c hψ i ↦ ?_⟩
  · -- Clusters are pairwise disjoint.
    refine Finset.disjoint_left.mpr fun z hz hz' ↦ ?_
    obtain ⟨h1, h2, h3⟩ := (hK i z).mp hz
    obtain ⟨h1', h2', h3'⟩ := (hK j z).mp hz'
    have hω : i.1 = j.1 := h1.symm.trans h1'
    have hk : i.2 ≠ j.2 := fun h ↦ hij (Prod.ext hω h)
    rcases lt_or_gt_of_ne hk with hlt | hlt
    · have := hTmono i.1 (Int.add_one_le_iff.mpr hlt)
      rw [hω] at this h3
      linarith
    · have := hTmono j.1 (Int.add_one_le_iff.mpr hlt)
      rw [← hω] at this h3'
      linarith
  · -- Clusters cover the zeros.
    let j : ℤ := ⌊z.val.2.2 / 2⌋
    have hj1 : (j : ℝ) ≤ z.val.2.2 / 2 := Int.floor_le _
    have hj2 : z.val.2.2 / 2 < (j : ℝ) + 1 := Int.lt_floor_add_one _
    have hlo : T z.val.1 (j - 1) ≤ z.val.2.2 := by
      have h := (hT z.val.1 (j - 1)).2
      push_cast at h
      linarith
    have hhi : z.val.2.2 < T z.val.1 (j + 1) := by
      have h := (hT z.val.1 (j + 1)).1
      push_cast at h
      linarith
    by_cases hmid : z.val.2.2 < T z.val.1 j
    · refine ⟨(z.val.1, j - 1), (hK (z.val.1, j - 1) z).mpr ⟨rfl, hlo, ?_⟩⟩
      change z.val.2.2 < T z.val.1 (j - 1 + 1)
      rwa [sub_add_cancel]
    · exact ⟨(z.val.1, j), (hK (z.val.1, j) z).mpr ⟨rfl, not_lt.mp hmid, hhi⟩⟩
  · exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (div_nonneg (mul_nonneg
      (rectInterpolantGaussianConstant_nonneg hX.le _) (mul_nonneg
        (div_nonneg (hφb0 _ _) (hℓ _ _).le) (by positivity))) zero_le_two) hI₀)
  · refine (hsum.mul_left (I₀ / 2)).congr fun i ↦ ?_
    change I₀ / 2 * (((∑ z ∈ K i, N(χ, α, s, z) : ℕ) : ℝ) *
      (rectInterpolantGaussianConstant X β (A i.1) *
        (φb i.1 i.2 / ℓ i.1 i.2 * (1 + |T i.1 i.2|) ^ (A i.1 + 2)))) = bd i
    change _ = ((∑ z ∈ K i, N(χ, α, s, z) : ℕ) : ℝ) *
      (rectInterpolantGaussianConstant X β (A i.1) *
        (φb i.1 i.2 / ℓ i.1 i.2 * (1 + |T i.1 i.2|) ^ (A i.1 + 2)) / 2 * I₀)
    ring
  · refine Exists.imp (fun R hR ↦ ⟨hR.1, hR.2.trans_eq ?_⟩)
      (spectralStripClusterBlock_traceNorm_le_of_boundaryData a χ hχ hα hs hαβ hβX ψ x Λ hb hj
        i.1 (A i.1) (ϑ i.1) (hϑ i.1) (hgrowth i.1)
        (fun z hz ↦ by
          have h := hord z
          have hϑeq : ϑ z.val.1 = ϑ i.1 := congrArg ϑ hz
          rwa [hϑeq] at h)
        (T i.1 i.2) (T i.1 (i.2 + 1)) (hT1 i.1 i.2) (hT3 i.1 i.2) (c * φb i.1 i.2) (ℓ i.1 i.2)
        (hℓ i.1 i.2) (hlow i.1 i.2) (hψ i.1 i.2) (K i) (hK i))
    change _ = c * (((∑ z ∈ K i, N(χ, α, s, z) : ℕ) : ℝ) *
      (rectInterpolantGaussianConstant X β (A i.1) *
        (φb i.1 i.2 / ℓ i.1 i.2 * (1 + |T i.1 i.2|) ^ (A i.1 + 2)) / 2 * I₀))
    ring

end RiemannMasullo
