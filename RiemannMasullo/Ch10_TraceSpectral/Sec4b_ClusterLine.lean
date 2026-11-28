module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_BinomialRecursion
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_ClusterBounds
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.ForMathlib.Analysis.Fourier.CompactSupportSeries
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.SmoothPartition

/-! # Theorem 10.4.3.5 on the line, with the zeros summed by clusters

Theorem 10.4.3.5(2)–(3), pp. 472–473, needs an estimate for the geometric component of the
ambient kernel tensors, the part in the theta subspace of the convolved lifts. The paper gives
none; for sums over arbitrary finite sets of zeros it is the recorded gap
`spectralStripGeometricKernel_blocks_bddAbove` of `Sec4b_Isolated` (#7406).

This file proves the estimate for sums over finite unions of clusters, for every test, on the
line, width zero: first when the density of the Sobolev space is the polynomial
`(1 + t ^ 2) ^ n` of the logarithm of the norm, the even orders `s = 2 n`
(`spectralStripGeometricBlocks_clusters_bddAbove_of_polynomialDensity`), then for the density
`(1 + t ^ 2) ^ σ` with any real `σ`, which is every order
(`spectralStripGeometricBlocks_clusters_bddAbove_of_rpowDensity`). The two cases differ only in
the recursion for tests of small support, which enters as a hypothesis of
`spectralStripGeometricBlocks_bddAbove_of_commonClusters_of_recursion`.

The proof has three parts.

* `Sec3_ClusterBounds` gives clusters and summable bounds that serve every test whose Mellin
  transform is dominated on fixed contours (`MellinShiftDominated`). Domination survives
  multiplication by characters of the norm, translation, and series of these
  (`MellinShiftDominated.modulate`, `.translate`, `.series`).
* For a dominated test supported close to the norm-one classes, the recursion of
  `Sec4b_ModulatedRecursion`, or of `Sec4b_BinomialRecursion` for a general order, bounds the
  geometric part by the spectral parts of its modulations,
  which are lifts of sums of cluster blocks
  (`traceNorm_spectralPart_jetBlockSum_le`, `traceNorm_jetBlockSum_le_of_dominated_modulated`).
* A test is cut along the logarithm of the norm into finitely many pieces, each a translate of
  such a test (`spectralStripGeometricBlocks_bddAbove_of_commonClusters`).

`Sec4b_Isolated` draws the convergence of the ambient kernel tensors along the clusters from
this bound. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set UniformSpace
open scoped NNReal NumberField.AdeleRing TensorProduct Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

universe u

local notation "Π(" E ", " G ")" => Completion (ProjectiveTensor E G)

section Abstract

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/- Copies of private lemmas of `Sec4b_GeometricRecursion`: the trace norm is a norm. -/
private theorem traceNorm_nonneg₃ (T : nuclearEndomorphisms W) : 0 ≤ traceNorm T := by
  let : Norm (nuclearEndomorphisms W) := ⟨traceNorm⟩
  exact (traceNorm_normedSpaceCore (H := W)).norm_nonneg T

private theorem traceNorm_add_le₃ (S T : nuclearEndomorphisms W) :
    traceNorm (S + T) ≤ traceNorm S + traceNorm T := by
  let : Norm (nuclearEndomorphisms W) := ⟨traceNorm⟩
  exact (traceNorm_normedSpaceCore (H := W)).norm_triangle S T

private theorem traceNorm_sum_le₃ {ι : Type*} (s : Finset ι) (T : ι → nuclearEndomorphisms W) :
    traceNorm (∑ i ∈ s, T i) ≤ ∑ i ∈ s, traceNorm (T i) := by
  let : Norm (nuclearEndomorphisms W) := ⟨traceNorm⟩
  have hc := traceNorm_normedSpaceCore (H := W)
  have hzero : traceNorm (0 : nuclearEndomorphisms W) = 0 := (hc.norm_eq_zero_iff 0).mpr rfl
  exact s.le_sum_of_subadditive traceNorm hzero.le hc.toCore.norm_triangle T

/-- The lifted spectral blocks of a block-diagonal operator on a quotient. Let `q` be a map of
norm at most one onto a Hilbert space `H`, with a lift of norm at most one, and `T` an operator
on `H` without coefficients between distinct zeros in a biorthogonal system. Then the sum over
a finite union of clusters of the rank-one operators `w ↦ f_j (q w) • lift (T x_j)` is the lift
of the finite section of `T` over that union, composed with `q`; so its trace norm is at most
the sum of the trace norms of the cluster blocks of `T`. -/
theorem traceNorm_spectralJetBlockSum_lift_le {H J Z ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (q : W →L[ℂ] H) (lift : H →L[ℂ] W) (hq : ‖q‖ ≤ 1) (hlift : ‖lift‖ ≤ 1)
    (x : J → H) (f : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x f)
    (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (hjet : Bijective (fun p : (z : Z) × Fin (N z) ↦ jet p.1 p.2))
    (T : H →L[ℂ] H)
    (hcross : ∀ z z', z ≠ z' → ∀ m n, f (jet z m) (T (x (jet z' n))) = 0)
    (K : ι → Finset Z) (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (R : ι → nuclearEndomorphisms H)
    (hR : ∀ i, (R i).val = spectralConvolutionFiniteSum T x f (K i) N jet)
    (C : Finset ι) :
    traceNorm (spectralJetBlockSum q N jet f (fun j ↦ lift (T (x j)))
      (C.disjiUnion K fun i _ j _ h ↦ hd i j h)) ≤ ∑ i ∈ C, traceNorm (R i) := by
  classical
  let box := C.disjiUnion K fun i _ j _ h ↦ hd i j h
  let Rsum : nuclearEndomorphisms H := ∑ i ∈ C, R i
  have h1 : Rsum.val = spectralConvolutionFiniteSum T x f box N jet := by
    change (∑ i ∈ C, R i : nuclearEndomorphisms H).val = _
    rw [Submodule.coe_sum]
    simp only [hR]
    unfold spectralConvolutionFiniteSum
    exact (Finset.sum_disjiUnion _ _ _).symm
  have hval : (spectralJetBlockSum q N jet f (fun j ↦ lift (T (x j))) box).val =
      lift.comp (Rsum.val.comp q) := by
    apply ContinuousLinearMap.ext
    intro w
    have h2 := spectralBlockSums_comm x f hb N jet hjet T hcross box (q w)
    have h3 : (spectralJetBlockSum q N jet f (fun j ↦ lift (T (x j))) box).val w =
        lift (∑ z ∈ box, ∑ m, f (jet z m) (q w) • T (x (jet z m))) := by
      simp [spectralJetBlockSum, map_sum, map_smul]
    have h4 : (lift.comp (Rsum.val.comp q)) w =
        lift (∑ z ∈ box, ∑ m, f (jet z m) (T (q w)) • x (jet z m)) := by
      change lift (Rsum.val (q w)) = _
      rw [h1]
      simp [spectralConvolutionFiniteSum]
    rw [h3, h4, h2]
  obtain ⟨hn, hle⟩ := traceNorm_sandwich_le Rsum.val Rsum.property q lift
  have hnorm : ‖lift‖ * ‖q‖ ≤ 1 :=
    (mul_le_mul hlift hq (norm_nonneg _) zero_le_one).trans (one_mul 1).le
  calc traceNorm (spectralJetBlockSum q N jet f (fun j ↦ lift (T (x j))) box)
      = traceNorm ⟨lift.comp (Rsum.val.comp q), hn⟩ := congrArg traceNorm (Subtype.ext hval)
    _ ≤ ‖lift‖ * ‖q‖ * traceNorm Rsum := hle
    _ ≤ 1 * traceNorm Rsum := mul_le_mul_of_nonneg_right hnorm (traceNorm_nonneg₃ _)
    _ = traceNorm Rsum := one_mul _
    _ ≤ ∑ i ∈ C, traceNorm (R i) := traceNorm_sum_le₃ C R

/-- The part of `τ ∘ A ∘ Q` in the range of `G`, for an idempotent splitting `G + P = 1`, is
`G ∘ τ` applied to the two parts of `A ∘ Q`; so its trace norm is at most `‖τ‖` times the sum
of their trace norms. -/
theorem traceNorm_geometricPart_mul_le (G P τ A : W →L[ℂ] W) (hG : ‖G‖ ≤ 1) (hGP : G + P = 1)
    (Q : nuclearEndomorphisms W) :
    traceNorm ⟨(G * (τ * A)) * Q.val, mul_mem_nuclearEndomorphisms_left _ Q⟩ ≤
      ‖τ‖ * (traceNorm ⟨(G * A) * Q.val, mul_mem_nuclearEndomorphisms_left _ Q⟩ +
        traceNorm ⟨(P * A) * Q.val, mul_mem_nuclearEndomorphisms_left _ Q⟩) := by
  let L (X : W →L[ℂ] W) (T : nuclearEndomorphisms W) : nuclearEndomorphisms W :=
    ⟨X * T.val, mul_mem_nuclearEndomorphisms_left X T⟩
  have heq : L (G * (τ * A)) Q = L (G * τ) (L (G * A) Q + L (P * A) Q) := by
    apply Subtype.ext
    change (G * (τ * A)) * Q.val = (G * τ) * ((G * A) * Q.val + (P * A) * Q.val)
    rw [← add_mul, ← add_mul, hGP, one_mul]
    simp only [mul_assoc]
  change traceNorm (L (G * (τ * A)) Q) ≤ _
  rw [heq]
  have h1 := traceNorm_mul_left_le (G * τ) (L (G * A) Q + L (P * A) Q)
  have h2 : ‖G * τ‖ ≤ ‖τ‖ := (norm_mul_le G τ).trans
    ((mul_le_mul_of_nonneg_right hG (norm_nonneg _)).trans (one_mul _).le)
  exact h1.trans (mul_le_mul h2 (traceNorm_add_le₃ _ _) (traceNorm_nonneg₃ _) (norm_nonneg _))

/-- The trace norm of `G ∘ A ∘ Q` for a finite sum `A = ∑ k, A k` is at most the sum of the
trace norms of the `G ∘ A k ∘ Q`. -/
theorem traceNorm_mul_sum_mul_le {κ : Type*} (s : Finset κ) (G A : W →L[ℂ] W)
    (Ak : κ → W →L[ℂ] W) (hA : A = ∑ k ∈ s, Ak k) (Q : nuclearEndomorphisms W) :
    traceNorm ⟨(G * A) * Q.val, mul_mem_nuclearEndomorphisms_left _ Q⟩ ≤
      ∑ k ∈ s, traceNorm ⟨(G * Ak k) * Q.val, mul_mem_nuclearEndomorphisms_left _ Q⟩ := by
  have heq : (⟨(G * A) * Q.val, mul_mem_nuclearEndomorphisms_left _ Q⟩ :
      nuclearEndomorphisms W) =
      ∑ k ∈ s, ⟨(G * Ak k) * Q.val, mul_mem_nuclearEndomorphisms_left _ Q⟩ := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    change (G * A) * Q.val = ∑ k ∈ s, (G * Ak k) * Q.val
    rw [hA, Finset.mul_sum, Finset.sum_mul]
  rw [heq]
  exact traceNorm_sum_le₃ s _

/-- An operator that fixes the output vectors of a sum of jet blocks fixes the sum. -/
theorem mul_spectralJetBlockSum_val_of_fixed {H J Z : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (P : W →L[ℂ] W) (q : W →L[ℂ] H) (N : Z → ℕ)
    (jet : (z : Z) → Fin (N z) → J) (f : J → StrongDual ℂ H) (v : J → W)
    (hv : ∀ j, P (v j) = v j) (K : Finset Z) :
    P * (spectralJetBlockSum q N jet f v K).val = (spectralJetBlockSum q N jet f v K).val := by
  have h := congrArg Subtype.val (mul_spectralJetBlockSum P q N jet f v K)
  rw [show (fun j ↦ P (v j)) = v from funext hv] at h
  exact h

/-- Continuous linear maps on the two factors carry tensor sums that converge along given
clusters to tensor sums that converge along the same clusters. This is
`SpectralClusterKernelsTendsto.map` of `Sec4b_ClusterKernels` with the clusters named. -/
theorem SpectralKernelSumsTendstoAlong.map {J E G X Y : Type*} {Z : Type u}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (d : E →L[ℂ] X) (j : G →L[ℂ] Y) {ι : Type*} {K : ι → Finset Z}
    {hd : ∀ i j, i ≠ j → Disjoint (K i) (K j)} {N : Z → ℕ} {jet : (z : Z) → Fin (N z) → J}
    {u : J → E} {v : J → G} {κ : Π(E, G)}
    (h : SpectralKernelSumsTendstoAlong K hd N jet u v κ) :
    ∃ κ' : Π(X, Y),
      SpectralKernelSumsTendstoAlong K hd N jet (fun z ↦ d (u z)) (fun z ↦ j (v z)) κ' := by
  let L : ProjectiveTensor E G →L[ℂ] ProjectiveTensor X Y :=
    ⟨projectiveTensorMap d.toLinearMap j.toLinearMap, projectiveTensorMap_continuous d j⟩
  refine ⟨L.completion κ,
    (L.completion.continuous.continuousAt.tendsto.comp h).congr fun C ↦ ?_⟩
  unfold Function.comp spectralKernelSum
  rw [ContinuousLinearMap.completion_apply_coe]
  apply congrArg ((↑) : ProjectiveTensor X Y → Π(X, Y))
  change projectiveTensorMap d.toLinearMap j.toLinearMap _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact (map_sum (TensorProduct.map d.toLinearMap j.toLinearMap)
    (fun m : Fin (N z) ↦ u (jet z m) ⊗ₜ[ℂ] v (jet z m)) Finset.univ).trans
    (Finset.sum_congr rfl fun m _ ↦ TensorProduct.map_tmul _ _ _ _)

end Abstract

variable {F : Type u} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (logIdeleClassNorm F)

section MellinDomination

/-- A test is dominated on the contours of a system of rectangles, with shifts: on the boundary
of each rectangle `[-X, X] × [T ω k, T ω (k + 1)]` its Mellin transform at the character `χ ω`,
with the exponent shifted by `i t`, is at most `c (1 + |t|) ^ p φb ω k`. For the data of
`spectralStripConvolution_exists_commonClusters` of `Sec3_ClusterBounds` the test of that
theorem is dominated with `c = 1`, and a dominated test has cluster blocks with trace norms at
most `c` times the summable bounds of that theorem. The class of dominated tests is stable
under multiplication by characters of the norm, under translation, and under series of these. -/
def MellinShiftDominated (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (X : ℝ)
    (T φb : PontryaginDual C₁ → ℤ → ℝ) (p : ℕ) (ψ : BruhatCompactSupport C𝔽) (c : ℝ) : Prop :=
  ∀ ω k, ∀ w ∈ rectBoundary (-X) X (T ω k) (T ω (k + 1)), ∀ t : ℝ,
    ‖∫ g : C𝔽, ψ.val g * ideleClassNormTwist (χ ω) (w + (t : ℂ) * Complex.I) g ∂μ𝔽‖ ≤
      c * ((1 + |t|) ^ p * φb ω k)

/-- Multiplying a test by the character `exp (i t₀ log|·|)` of the norm shifts its Mellin
transform by `i t₀`. -/
theorem mellin_mul_cexp_logNorm (ψ ψ' : BruhatCompactSupport C𝔽) (t₀ : ℝ)
    (h : ∀ g, ψ'.val g = Complex.exp ((t₀ : ℂ) * Complex.I * (logNorm g : ℂ)) * ψ.val g)
    (η : PontryaginDual C𝔽) (w : ℂ) :
    ∫ g : C𝔽, ψ'.val g * ideleClassNormTwist η w g ∂μ𝔽 =
      ∫ g : C𝔽, ψ.val g * ideleClassNormTwist η (w + (t₀ : ℂ) * Complex.I) g ∂μ𝔽 := by
  refine integral_congr_ae (.of_forall fun g ↦ ?_)
  change ψ'.val g * ideleClassNormTwist η w g =
    ψ.val g * ideleClassNormTwist η (w + (t₀ : ℂ) * Complex.I) g
  rw [h, spectralStripConvolution_summable_clusterTraceNorms_of_scalarKernels_twist (F := F) η w g,
    spectralStripConvolution_summable_clusterTraceNorms_of_scalarKernels_twist (F := F) η _ g,
    add_mul, Complex.exp_add]
  ring

/-- The Mellin transform of a translate of a test is the Mellin transform of the test times the
value of the quasi-character at the translating element. -/
theorem mellin_translate (ψ ψ' : BruhatCompactSupport C𝔽) (g₀ : C𝔽)
    (h : ∀ x, ψ'.val x = ψ.val (g₀⁻¹ * x)) (η : PontryaginDual C𝔽) (w : ℂ) :
    ∫ g : C𝔽, ψ'.val g * ideleClassNormTwist η w g ∂μ𝔽 =
      ideleClassNormTwist η w g₀ * ∫ g : C𝔽, ψ.val g * ideleClassNormTwist η w g ∂μ𝔽 := by
  rw [← integral_const_mul,
    ← integral_mul_left_eq_self (fun y ↦ ψ'.val y * ideleClassNormTwist η w y) g₀]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  change ψ'.val (g₀ * y) * ideleClassNormTwist η w (g₀ * y) =
    ideleClassNormTwist η w g₀ * (ψ.val y * ideleClassNormTwist η w y)
  rw [h, inv_mul_cancel_left, map_mul]
  ring

/-- The norm of the quasi-character `η |·|^w` at `g` is `exp (Re w * log|g|)`. -/
theorem norm_ideleClassNormTwist (η : PontryaginDual C𝔽) (w : ℂ) (g : C𝔽) :
    ‖ideleClassNormTwist (F := F) η w g‖ = Real.exp (w.re * logNorm g) := by
  rw [spectralStripConvolution_summable_clusterTraceNorms_of_scalarKernels_twist (F := F) η w g,
    norm_mul, Circle.norm_coe, one_mul, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- A pointwise convergent series of tests, dominated by one test and with absolutely summable
coefficients, has the series of the Mellin transforms as its Mellin transform. -/
theorem hasSum_mellin_of_hasSum {ι : Type*} [Countable ι] (φ Ψ : BruhatCompactSupport C𝔽)
    (ψ : ι → BruhatCompactSupport C𝔽) (a : ι → ℂ) (ha : Summable fun n ↦ ‖a n‖)
    (hdom : ∀ n g, ‖(ψ n).val g‖ ≤ ‖φ.val g‖)
    (hΨ : ∀ g, HasSum (fun n ↦ a n * (ψ n).val g) (Ψ.val g)) (η : PontryaginDual C𝔽) (w : ℂ) :
    HasSum (fun n ↦ a n * ∫ g : C𝔽, (ψ n).val g * ideleClassNormTwist η w g ∂μ𝔽)
      (∫ g : C𝔽, Ψ.val g * ideleClassNormTwist η w g ∂μ𝔽) := by
  have hcont (χ : BruhatCompactSupport C𝔽) : Continuous χ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp χ.property.1)
  have htw : Continuous (fun g : C𝔽 ↦ ideleClassNormTwist (F := F) η w g) :=
    (ideleClassNormTwist (F := F) η w).continuous
  let Fn (n : ι) (g : C𝔽) : ℂ := a n * ((ψ n).val g * ideleClassNormTwist η w g)
  have hFint (n : ι) : Integrable (Fn n) μ𝔽 := by
    have hcs : HasCompactSupport (fun g : C𝔽 ↦ (ψ n).val g * ideleClassNormTwist η w g) :=
      (show HasCompactSupport (ψ n).val from (ψ n).property.2).mul_right
    exact (((hcont (ψ n)).mul htw).integrable_of_hasCompactSupport hcs).const_mul _
  have hφint : Integrable (fun g : C𝔽 ↦ ‖φ.val g‖ * ‖ideleClassNormTwist η w g‖) μ𝔽 := by
    have hcs : HasCompactSupport (fun g : C𝔽 ↦ ‖φ.val g‖ * ‖ideleClassNormTwist η w g‖) :=
      (show HasCompactSupport φ.val from φ.property.2).norm.mul_right
    exact ((hcont φ).norm.mul htw.norm).integrable_of_hasCompactSupport hcs
  have hFsum : Summable fun n ↦ ∫ g, ‖Fn n g‖ ∂μ𝔽 := by
    refine Summable.of_nonneg_of_le (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      (fun n ↦ ?_) (ha.mul_right (∫ g, ‖φ.val g‖ * ‖ideleClassNormTwist η w g‖ ∂μ𝔽))
    rw [← integral_const_mul]
    refine integral_mono (hFint n).norm (hφint.const_mul _) fun g ↦ ?_
    change ‖a n * ((ψ n).val g * ideleClassNormTwist η w g)‖ ≤
      ‖a n‖ * (‖φ.val g‖ * ‖ideleClassNormTwist η w g‖)
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hdom n g) (norm_nonneg _)) (norm_nonneg _)
  have h2 := hasSum_integral_of_summable_integral_norm hFint hFsum
  have h3 : (fun n ↦ ∫ g, Fn n g ∂μ𝔽) =
      fun n ↦ a n * ∫ g : C𝔽, (ψ n).val g * ideleClassNormTwist η w g ∂μ𝔽 :=
    funext fun n ↦ integral_const_mul _ _
  have h4 : ∫ g, ∑' n, Fn n g ∂μ𝔽 = ∫ g : C𝔽, Ψ.val g * ideleClassNormTwist η w g ∂μ𝔽 := by
    refine integral_congr_ae (.of_forall fun g ↦ ?_)
    have h5 : HasSum (fun n ↦ Fn n g) (Ψ.val g * ideleClassNormTwist η w g) := by
      refine ((hΨ g).mul_right (ideleClassNormTwist η w g)).congr_fun fun n ↦ ?_
      change a n * ((ψ n).val g * ideleClassNormTwist η w g) =
        a n * (ψ n).val g * ideleClassNormTwist η w g
      ring
    exact h5.tsum_eq
  rw [h3, h4] at h2
  exact h2

/-- A dominated test times the character `exp (i t₀ log|·|)` of the norm is dominated, with the
constant multiplied by `(1 + |t₀|) ^ p`. -/
theorem MellinShiftDominated.modulate {χ : PontryaginDual C₁ → PontryaginDual C𝔽} {X : ℝ}
    {T φb : PontryaginDual C₁ → ℤ → ℝ} {p : ℕ} {ψ : BruhatCompactSupport C𝔽} {c : ℝ}
    {ψ' : BruhatCompactSupport C𝔽}
    (h : MellinShiftDominated χ X T φb p ψ c) (hc : 0 ≤ c)
    (hφb : ∀ ω k, 0 ≤ φb ω k) (t₀ : ℝ)
    (hψ' : ∀ g, ψ'.val g = Complex.exp ((t₀ : ℂ) * Complex.I * (logNorm g : ℂ)) * ψ.val g) :
    MellinShiftDominated χ X T φb p ψ' (c * (1 + |t₀|) ^ p) := by
  intro ω k w hw t
  rw [mellin_mul_cexp_logNorm ψ ψ' t₀ hψ' (χ ω) (w + (t : ℂ) * Complex.I)]
  have h1 := h ω k w hw (t + t₀)
  have heq : w + (t : ℂ) * Complex.I + (t₀ : ℂ) * Complex.I =
      w + ((t + t₀ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [heq]
  refine h1.trans ?_
  have hpe : (1 + |t + t₀|) ^ p ≤ (1 + |t₀|) ^ p * (1 + |t|) ^ p := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ p
    nlinarith [abs_add_le t t₀, abs_nonneg t, abs_nonneg t₀,
      mul_nonneg (abs_nonneg t) (abs_nonneg t₀)]
  calc c * ((1 + |t + t₀|) ^ p * φb ω k)
      ≤ c * ((1 + |t₀|) ^ p * (1 + |t|) ^ p * φb ω k) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpe (hφb ω k)) hc
    _ = c * (1 + |t₀|) ^ p * ((1 + |t|) ^ p * φb ω k) := by ring

/-- A translate of a dominated test is dominated, with the constant multiplied by
`exp (X |log|g₀||)` for the translating element `g₀`. -/
theorem MellinShiftDominated.translate {χ : PontryaginDual C₁ → PontryaginDual C𝔽} {X : ℝ}
    {T φb : PontryaginDual C₁ → ℤ → ℝ} {p : ℕ} {ψ : BruhatCompactSupport C𝔽} {c : ℝ}
    {ψ' : BruhatCompactSupport C𝔽}
    (h : MellinShiftDominated χ X T φb p ψ c) (hX : 0 ≤ X)
    (g₀ : C𝔽) (hψ' : ∀ x, ψ'.val x = ψ.val (g₀⁻¹ * x)) :
    MellinShiftDominated χ X T φb p ψ' (c * Real.exp (X * |logNorm g₀|)) := by
  intro ω k w hw t
  rw [mellin_translate ψ ψ' g₀ hψ' (χ ω) (w + (t : ℂ) * Complex.I), norm_mul,
    norm_ideleClassNormTwist]
  have hre : |w.re| ≤ X := by
    rcases mem_rectBoundary_iff.mp hw with ⟨h1, -⟩ | ⟨-, h1 | h1⟩
    · exact abs_le.mpr h1
    · rw [h1, abs_neg, abs_of_nonneg hX]
    · rw [h1, abs_of_nonneg hX]
  have hre' : (w + (t : ℂ) * Complex.I).re = w.re := by simp
  have hexp : Real.exp ((w + (t : ℂ) * Complex.I).re * logNorm g₀) ≤
      Real.exp (X * |logNorm g₀|) := by
    rw [hre']
    refine Real.exp_le_exp.mpr ?_
    calc w.re * logNorm g₀ ≤ |w.re * logNorm g₀| := le_abs_self _
      _ = |w.re| * |logNorm g₀| := abs_mul _ _
      _ ≤ X * |logNorm g₀| := mul_le_mul_of_nonneg_right hre (abs_nonneg _)
  have h1 := h ω k w hw t
  calc Real.exp ((w + (t : ℂ) * Complex.I).re * logNorm g₀) *
        ‖∫ g : C𝔽, ψ.val g * ideleClassNormTwist (χ ω) (w + (t : ℂ) * Complex.I) g ∂μ𝔽‖
      ≤ Real.exp (X * |logNorm g₀|) * (c * ((1 + |t|) ^ p * φb ω k)) :=
        mul_le_mul hexp h1 (norm_nonneg _) (Real.exp_pos _).le
    _ = c * Real.exp (X * |logNorm g₀|) * ((1 + |t|) ^ p * φb ω k) := by ring

/-- A series of modulations of a dominated test is dominated: if `Ψ = ∑ n, a n ψ_n` pointwise,
with `ψ_n` the test `ψ` times the character `exp (i s_n log|·|)` of the norm, the constant is
multiplied by `∑ n, ‖a n‖ (1 + |s_n|) ^ p`. -/
theorem MellinShiftDominated.series {ι : Type*} [Countable ι]
    {χ : PontryaginDual C₁ → PontryaginDual C𝔽} {X : ℝ}
    {T φb : PontryaginDual C₁ → ℤ → ℝ} {p : ℕ} {ψ : BruhatCompactSupport C𝔽} {c : ℝ}
    (h : MellinShiftDominated χ X T φb p ψ c) (hc : 0 ≤ c) (hφb : ∀ ω k, 0 ≤ φb ω k)
    (Ψ : BruhatCompactSupport C𝔽) (ψs : ι → BruhatCompactSupport C𝔽) (s : ι → ℝ) (a : ι → ℂ)
    (hψs : ∀ n g, (ψs n).val g =
      Complex.exp ((s n : ℂ) * Complex.I * (logNorm g : ℂ)) * ψ.val g)
    (ha : Summable fun n ↦ ‖a n‖ * (1 + |s n|) ^ p)
    (hΨ : ∀ g, HasSum (fun n ↦ a n * (ψs n).val g) (Ψ.val g)) :
    MellinShiftDominated χ X T φb p Ψ (c * ∑' n, ‖a n‖ * (1 + |s n|) ^ p) := by
  intro ω k w hw t
  have ha0 : Summable fun n ↦ ‖a n‖ :=
    Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ by
      have h1 : (1 : ℝ) ≤ (1 + |s n|) ^ p := one_le_pow₀ (by linarith [abs_nonneg (s n)])
      exact le_mul_of_one_le_right (norm_nonneg _) h1) ha
  have hdom (n : ι) (g : C𝔽) : ‖(ψs n).val g‖ ≤ ‖ψ.val g‖ := by
    rw [hψs n g, norm_mul]
    have h1 : ‖Complex.exp ((s n : ℂ) * Complex.I * (logNorm g : ℂ))‖ = 1 := by
      rw [show ((s n : ℂ) * Complex.I * (logNorm g : ℂ)) =
        ((s n * logNorm g : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [h1, one_mul]
  have hs := hasSum_mellin_of_hasSum ψ Ψ ψs a ha0 hdom hΨ (χ ω) (w + (t : ℂ) * Complex.I)
  have hb : HasSum (fun n ↦ ‖a n‖ * (1 + |s n|) ^ p * (c * ((1 + |t|) ^ p * φb ω k)))
      ((∑' n, ‖a n‖ * (1 + |s n|) ^ p) * (c * ((1 + |t|) ^ p * φb ω k))) :=
    ha.hasSum.mul_right _
  refine (hs.norm_le_of_bounded hb fun n ↦ ?_).trans_eq (by ring)
  have h1 := (h.modulate hc hφb (s n) (hψs n)) ω k w hw t
  rw [norm_mul]
  calc ‖a n‖ * ‖∫ g : C𝔽, (ψs n).val g *
        ideleClassNormTwist (χ ω) (w + (t : ℂ) * Complex.I) g ∂μ𝔽‖
      ≤ ‖a n‖ * (c * (1 + |s n|) ^ p * ((1 + |t|) ^ p * φb ω k)) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖a n‖ * (1 + |s n|) ^ p * (c * ((1 + |t|) ^ p * φb ω k)) := by ring

/-- A dominated test satisfies the hypothesis of
`spectralStripConvolution_exists_commonClusters`: without shift its Mellin transform is at most
`c φb ω k` on the boundary of each rectangle. -/
theorem MellinShiftDominated.unshifted {χ : PontryaginDual C₁ → PontryaginDual C𝔽} {X : ℝ}
    {T φb : PontryaginDual C₁ → ℤ → ℝ} {p : ℕ} {ψ : BruhatCompactSupport C𝔽} {c : ℝ}
    (h : MellinShiftDominated χ X T φb p ψ c) :
    ∀ ω k, ∀ w ∈ rectBoundary (-X) X (T ω k) (T ω (k + 1)),
      ‖∫ g : C𝔽, ψ.val g * ideleClassNormTwist (χ ω) w g ∂μ𝔽‖ ≤ c * φb ω k := by
  intro ω k w hw
  have h1 := h ω k w hw 0
  simpa using h1

end MellinDomination

local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => (le_of_lt (zero_lt_one.trans hs))
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α s
local notation "W'(" α ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α s true
local notation "Θ(" a ", " hα ", " hs ")" => globalThetaSobolev F a (hStrip(hα)) hs
local notation "H(" a ", " hα ", " hs ")" => spectralSobolevQuotient F a (hStrip(hα)) hs
local notation "S(" a ", " hα ", " hs ")" =>
  (fun u : H(a, hα, hs) ↦
    ((Θ(a, hα, hs)).quotientEquivOrthogonal u).val)
local notation "Aq(" a ", " hα ", " hs ", " φ ")" =>
  spectralConvolution (F := F) a (hStrip(hα)) hs φ
local notation "Q(" a ", " hα ", " hs ")" => (Θ(a, hα, hs)).mkQL
local notation "A(" hα ", " hs ", " φ ")" =>
  hardySobolevTestAction μ𝔽 m𝔽 _ _ _ (hStrip(hα)) hs φ
local notation "Pspec(" a ", " hα ", " hs ")" => spectralProjection (F := F) a hα hs
local notation "Pgeom(" a ", " hα ", " hs ")" => geometricProjection (F := F) a hα hs

section Tests

/-- The logarithm of the norm is additive. -/
theorem logIdeleClassNorm_mul (g h : C𝔽) : logNorm (g * h) = logNorm g + logNorm h := by
  change Real.log ((ideleClassNorm F (g * h)).val : ℝ) =
    Real.log ((ideleClassNorm F g).val : ℝ) + Real.log ((ideleClassNorm F h).val : ℝ)
  rw [map_mul, Units.val_mul, NNReal.coe_mul]
  exact Real.log_mul (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'

/-- Every real number is the logarithm of the norm of an idele class. -/
theorem exists_logIdeleClassNorm_eq (t : ℝ) : ∃ g : C𝔽, logNorm g = t := by
  let r : ℝ≥0ˣ := Units.mk0 ⟨Real.exp t, (Real.exp_pos t).le⟩
    (fun h ↦ (Real.exp_pos t).ne' (congrArg NNReal.toReal h))
  refine ⟨QuotientGroup.mk (canonicalIdeleNormSection F r), ?_⟩
  change Real.log ((ideleClassNorm F (QuotientGroup.mk (canonicalIdeleNormSection F r))).val : ℝ)
    = t
  have h : ideleClassNorm F (QuotientGroup.mk (canonicalIdeleNormSection F r)) = r :=
    canonicalIdeleNormSection_rightInverse F r
  rw [h]
  exact Real.log_exp t

/-- A test is supported where the logarithm of the norm is bounded. -/
theorem exists_abs_logIdeleClassNorm_le_of_ne_zero (φ : BruhatCompactSupport C𝔽) :
    ∃ R : ℝ, 0 < R ∧ ∀ g, φ.val g ≠ 0 → |logNorm g| ≤ R := by
  have hLc : Continuous (logIdeleClassNorm F) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (isProperMap_ideleClassNorm F).continuous)).log
      fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  have hK : IsCompact (tsupport φ.val) := φ.property.2
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hLc.continuousOn
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun g hg ↦ ?_⟩
  exact (hC g (subset_tsupport _ hg)).trans (le_max_left _ _)

/-- A translate of a compact Bruhat test on the idele class group is a compact Bruhat test.
A copy of the private `kernelLocalization_exists_translate` of
`Ch12_TraceGeometric/Sec5_Isolated`. -/
theorem exists_bruhatCompactSupport_translate (g : C𝔽) (φ : BruhatCompactSupport C𝔽) :
    ∃ ψ : BruhatCompactSupport C𝔽, ∀ x, ψ.val x = φ.val (g⁻¹ * x) := by
  have hφ := modulationWeight_mem_schwartzBruhat m𝔽 univ ⟨0, mem_univ _⟩
    ⟨φ.val, bruhatCompactSupport_le_modulatedExponentialDecay m𝔽 univ
      ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
      (fun t ↦ ⟨QuotientGroup.mk (canonicalIdeleNormSection F t),
        canonicalIdeleNormSection_rightInverse F t⟩) φ.property⟩
  rw [modulationWeight_zero] at hφ
  let f : SchwartzBruhat C𝔽 := ⟨φ.val, hφ⟩
  have hsm := schwartzBruhat_isBruhatSmooth (schwartzBruhatTranslate g f)
  have hc := (show HasCompactSupport φ.val from φ.property.2).comp_homeomorph
    (Homeomorph.mulLeft g⁻¹)
  exact ⟨⟨_, (mem_bruhatSmoothSubmodule_iff _).mpr hsm, hc⟩, fun _ ↦ rfl⟩

/-- Left translating a test postcomposes its convolution on the weighted space with the same
translation. A copy of `stripTestAction_translate` of `Ch12_TraceGeometric/Sec5_Isolated`,
which no file can import. -/
theorem stripTestAction_eq_translation_comp {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (g : C𝔽) (φ ψ : BruhatCompactSupport C𝔽) (hψ : ∀ x, ψ.val x = φ.val (g⁻¹ * x)) :
    (A(hα, hs, ψ) : W(α, s) →L[ℂ] W(α, s)) =
      (hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs g).comp (A(hα, hs, φ)) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
  have hφ := hardySobolevTestAction_apply μ𝔽 m𝔽 _ _ _ (hStrip(hα)) hs φ u
  have htr := (measurePreserving_mul_left μ𝔽 g⁻¹).quasiMeasurePreserving.ae_eq_comp hφ
  have ht := hardySobolevTranslation_apply μ𝔽 m𝔽 _ _ _ (hStrip(hα)) hs g
    (A(hα, hs, φ) u)
  filter_upwards [hardySobolevTestAction_apply μ𝔽 m𝔽 _ _ _ (hStrip(hα)) hs ψ u,
    htr, ht] with x hx hy hz
  refine hx.trans ((?_ : lcaConvolution μ𝔽 ψ.val u x =
    lcaConvolution μ𝔽 φ.val u (g⁻¹ * x)).trans (hy.symm.trans hz.symm))
  unfold lcaConvolution
  rw [← integral_mul_left_eq_self (fun y ↦ ψ.val y * u (y⁻¹ * x)) g]
  apply integral_congr_ae (.of_forall fun y ↦ ?_)
  rw [hψ, inv_mul_cancel_left, mul_inv_rev, mul_assoc]

/-- The spectral projection of the convolved lift of a class is the lift of the convolved
class. -/
theorem spectralProjection_stripTestAction_lift (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (ψ : BruhatCompactSupport C𝔽) (u : H(a, hα, hs)) :
    Pspec(a, hα, hs) ((A(hα, hs, ψ) : W(α, s) →L[ℂ] W(α, s)) (S(a, hα, hs) u)) =
      S(a, hα, hs) (Aq(a, hα, hs, ψ) u) := by
  let θ := Θ(a, hα, hs)
  let lift := θ.orthogonal.subtypeL.comp
    θ.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  have hsection (v) : θ.mkQL (lift v) = v :=
    (θ.quotientEquivOrthogonal_symm_eq_mk _ (θ.quotientEquivOrthogonal v).property).symm.trans
      (θ.quotientEquivOrthogonal.symm_apply_apply v)
  have hp := DFunLike.congr_fun
    (spectralProjection_convolution_factor (F := F) a hα hs ψ) (lift u)
  change Pspec(a, hα, hs) ((A(hα, hs, ψ) : W(α, s) →L[ℂ] W(α, s)) (lift u)) =
    lift (Aq(a, hα, hs, ψ) (θ.mkQL (lift u))) at hp
  rw [hsection] at hp
  exact hp

end Tests

/-- Paper: Proposition 9.2.1.8, p. 410. On the base interval `{0}` the density of the Sobolev
space of order `s` is the power `(1 + t ^ 2) ^ (s / 2)` of the logarithmic coordinate. -/
theorem intervalSobolevDensity_width_zero {α s : ℝ} (hα0 : α = 0) (t : ℝ) :
    intervalSobolevDensity (-α) α s t = (1 + t ^ 2) ^ (s / 2) := by
  subst hα0
  unfold intervalSobolevDensity
  simp

section Clusters

variable (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)

local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat
local notation "Z(" χ ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))
local notation "jet(" z ", " m ")" => ⟨((z).val.1, (z).val.2.1, (z).val.2.2, (m).val), (m).isLt⟩
local notation "D" => spectralSobolevDualEmbedding F a (hStrip(hα)) hs₀(hs)
local notation "Bases(" χ ", " x ", " f ")" => (IsSpectralMarkushevichBasis x f ∧
  ∀ j, D (f j) = (spectralStripJet_memLp χ hα hs₀(hs) j).toLp
    (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))

/-- Paper: (10.4.2.5), p. 459, and (10.4.3.43), p. 472. The spectral part of the ambient
blocks of a test, summed over a finite union of clusters, has trace norm at most the sum of the
trace norms of the cluster blocks of the quotient convolution: it is the lift of the finite
section of the quotient convolution over the union, composed with the quotient map. -/
theorem traceNorm_spectralPart_jetBlockSum_le
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
    (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (hb : Bases(χ, x, f)) (ψ : BruhatCompactSupport C𝔽)
    {ι : Type*} (K : ι → Finset Z(χ)) (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (R : ι → nuclearEndomorphisms H(a, hα, hs₀(hs)))
    (hR : ∀ i, (R i).val = spectralConvolutionFiniteSum (Aq(a, hα, hs₀(hs), ψ)) x f (K i)
      (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m)))
    (C : Finset ι) :
    traceNorm (spectralJetBlockSum Q(a, hα, hs₀(hs)) (fun z : Z(χ) ↦ N(χ, z))
      (fun z m ↦ jet(z, m)) f
      (fun j ↦ Pspec(a, hα, hs₀(hs))
        ((A(hα, hs₀(hs), ψ) : W(α, s) →L[ℂ] W(α, s)) (S(a, hα, hs₀(hs)) (x j))))
      (C.disjiUnion K fun i _ j _ h ↦ hd i j h)) ≤ ∑ i ∈ C, traceNorm (R i) := by
  let θ := Θ(a, hα, hs₀(hs))
  let lift := θ.orthogonal.subtypeL.comp
    θ.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  let key (z : Z(χ)) (m : Fin N(χ, z)) : SpectralStripJetIndex χ a α s := jet(z, m)
  let index : ((z : Z(χ)) × Fin N(χ, z)) ≃ SpectralStripJetIndex χ a α s :=
    ⟨fun p ↦ key p.1 p.2,
      fun j ↦ ⟨⟨(j.val.1, j.val.2.1, j.val.2.2.1),
        SpectralStripJetIndex.mem_strip_order_pos hα j⟩, ⟨j.val.2.2.2, j.property⟩⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩
  have hcross (z z' : Z(χ)) (hne : z ≠ z') (m : Fin N(χ, z)) (n : Fin N(χ, z')) :
      f (key z m) (Aq(a, hα, hs₀(hs), ψ) (x (key z' n))) = 0 :=
    (spectralStripConvolution_jetCoefficients a hα hs χ x f hb.1 hb.2 ψ).1 z z' hne m n
  have hq : ‖θ.mkQL‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ by
    rw [one_mul]
    exact Submodule.Quotient.norm_mk_le θ v
  have hlift : ‖lift‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u ↦ by
    rw [one_mul]
    exact le_of_eq (θ.quotientEquivOrthogonal.norm_map u)
  have hfun : (fun j ↦ Pspec(a, hα, hs₀(hs))
      ((A(hα, hs₀(hs), ψ) : W(α, s) →L[ℂ] W(α, s)) (S(a, hα, hs₀(hs)) (x j)))) =
      fun j ↦ lift (Aq(a, hα, hs₀(hs), ψ) (x j)) :=
    funext fun j ↦ spectralProjection_stripTestAction_lift a hα hs₀(hs) ψ (x j)
  rw [hfun]
  exact traceNorm_spectralJetBlockSum_lift_le θ.mkQL lift hq hlift x f hb.1
    (fun z : Z(χ) ↦ N(χ, z)) key index.bijective (Aq(a, hα, hs₀(hs), ψ)) hcross K hd R hR C

/-- Paper: Theorem 10.4.3.5(2), pp. 472–473. The printed tensors (10.4.3.43), with convolution
on the input factor, converge along given clusters as soon as the cluster blocks of the
quotient convolution are nuclear with summable bounds for their trace norms: the blocks then
sum to the convolution in trace norm, and the kernels follow.
Reconstruction: The paper does not state this. It is
`spectralStripTransposedKernel_clusters_operator` of `Sec4b_ClusterKernels` for given
clusters. -/
theorem spectralStripTransposedKernel_along_of_blocks
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
    (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (hb : Bases(χ, x, f)) (ψ : BruhatCompactSupport C𝔽)
    {ι : Type u} (K : ι → Finset Z(χ)) (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (hc : ∀ z, ∃ i, z ∈ K i) (bd : ι → ℝ) (hbds : Summable bd)
    (hblk : ∀ i, ∃ R : nuclearEndomorphisms H(a, hα, hs₀(hs)),
      R.val = spectralConvolutionFiniteSum (Aq(a, hα, hs₀(hs), ψ)) x f (K i)
        (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m)) ∧ traceNorm R ≤ bd i) :
    ∃ κT : Π(W'(α, s), W(α, s)),
      SpectralKernelSumsTendstoAlong K hd (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m))
        (fun j ↦ D ((f j).comp (Aq(a, hα, hs₀(hs), ψ)))) (fun j ↦ S(a, hα, hs₀(hs)) (x j))
        κT := by
  choose R hR hRn using hblk
  let θ := Θ(a, hα, hs₀(hs))
  let key (z : Z(χ)) (m : Fin N(χ, z)) : SpectralStripJetIndex χ a α s := jet(z, m)
  let index : ((z : Z(χ)) × Fin N(χ, z)) ≃ SpectralStripJetIndex χ a α s :=
    ⟨fun p ↦ key p.1 p.2,
      fun j ↦ ⟨⟨(j.val.1, j.val.2.1, j.val.2.2.1),
        SpectralStripJetIndex.mem_strip_order_pos hα j⟩, ⟨j.val.2.2.2, j.property⟩⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩
  have hsum : Summable fun i ↦ traceNorm (R i) :=
    Summable.of_nonneg_of_le (fun i ↦ traceNorm_nonneg₃ (R i)) hRn hbds
  have h1 := spectralStripConvolution_nuclear_of_clusters_abstract (Aq(a, hα, hs₀(hs), ψ)) x f
    hb.1 (fun z : Z(χ) ↦ N(χ, z)) key index.bijective K hd hc R hR hsum
  have h2 := spectralConvolutionFiniteSum_clusters_traceNorm_tendsto (Aq(a, hα, hs₀(hs), ψ)) x f
    (fun z : Z(χ) ↦ N(χ, z)) key K hd R hR hsum h1.choose_spec.1
  have h3 := exists_kernel_limit_of_traceNorm_tendsto (Aq(a, hα, hs₀(hs), ψ)) x f
    (fun z : Z(χ) ↦ N(χ, z)) key K hd h2.choose h2.choose_spec.1 h2.choose_spec.2
  let d : StrongDual ℂ H(a, hα, hs₀(hs)) →L[ℂ] W'(α, s) := ⟨D,
    (spectralSobolevDualEmbedding_isometry_range (F := F) a (hStrip(hα))
      hs₀(hs)).1.continuous⟩
  let lift : H(a, hα, hs₀(hs)) →L[ℂ] W(α, s) := θ.orthogonal.subtypeL.comp
    θ.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  exact SpectralKernelSumsTendstoAlong.map d lift h3.choose_spec.1

set_option maxHeartbeats 800000 in
/-- Paper: Theorem 10.4.3.5(2), p. 472, the geometric component for a test supported close to
the norm-one classes, with the zeros summed by clusters. Let `ψ m` be the test `ψ 0` times the
character `exp (2 π i m log|·| / (4 δ))` of the norm, let `ψ 0` be dominated with constant `c`
on the contours of a system of clusters whose blocks are bounded by `c' bd i` for every test
dominated with constant `c'`, and suppose the recursion of
`exists_traceNorm_geometricProjection_stripTestAction_le_of_modulated` holds for the family
`ψ m`. Then over every finite union of clusters the geometric part and the spectral part of the
ambient blocks of `ψ 0` have trace norms at most `c (1 + 2 π / (4 δ)) ^ p ∑ i, bd i`.
The modulated tests are dominated with constants `c (1 + 2 π |m| / (4 δ)) ^ p`, their spectral
parts are lifts of sums of cluster blocks, and the recursion bounds the geometric part by the
spectral parts.
Reconstruction: The paper gives no estimate for the geometric component. -/
theorem traceNorm_jetBlockSum_le_of_dominated_modulated
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
    (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (hb : Bases(χ, x, f)) (X : ℝ) (T φb : PontryaginDual C₁ → ℤ → ℝ) (p : ℕ)
    (hφb : ∀ ω k, 0 ≤ φb ω k)
    {ι : Type*} (K : ι → Finset Z(χ)) (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (bd : ι → ℝ) (hbd0 : ∀ i, 0 ≤ bd i) (hbds : Summable bd)
    (hblocks : ∀ (ψ : BruhatCompactSupport C𝔽) (c : ℝ),
      (∀ ω k, ∀ w ∈ rectBoundary (-X) X (T ω k) (T ω (k + 1)),
        ‖∫ g : C𝔽, ψ.val g * ideleClassNormTwist (χ ω) w g ∂μ𝔽‖ ≤ c * φb ω k) →
      ∀ i, ∃ R : nuclearEndomorphisms H(a, hα, hs₀(hs)),
        R.val = spectralConvolutionFiniteSum (Aq(a, hα, hs₀(hs), ψ)) x f (K i)
          (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m)) ∧ traceNorm R ≤ c * bd i)
    (δ : ℝ) (hδ : 0 < δ) (ψ : ℤ → BruhatCompactSupport C𝔽)
    (hψ : ∀ (m : ℤ) (g : C𝔽), (ψ m).val g =
      Complex.exp (2 * Real.pi * Complex.I * m * (logNorm g / (4 * δ) : ℝ)) * (ψ 0).val g)
    (c : ℝ) (hc : 0 ≤ c) (hdom : MellinShiftDominated χ X T φb p (ψ 0) c)
    (hrec : ∀ (B : ℝ) (Q : nuclearEndomorphisms (W(α, s))),
      Pspec(a, hα, hs₀(hs)) * Q.val = Q.val →
      (∀ m : ℤ, traceNorm ⟨((Pspec(a, hα, hs₀(hs))).comp (A(hα, hs₀(hs), ψ m))) * Q.val,
        mul_mem_nuclearEndomorphisms_left _ Q⟩ ≤ B * (1 + |(m : ℝ)|) ^ p) →
      traceNorm ⟨((Pgeom(a, hα, hs₀(hs))).comp (A(hα, hs₀(hs), ψ 0))) * Q.val,
        mul_mem_nuclearEndomorphisms_left _ Q⟩ ≤ B)
    (C : Finset ι) :
    traceNorm (spectralJetBlockSum Q(a, hα, hs₀(hs)) (fun z : Z(χ) ↦ N(χ, z))
        (fun z m ↦ jet(z, m)) f
        (fun j ↦ Pgeom(a, hα, hs₀(hs))
          ((A(hα, hs₀(hs), ψ 0) : W(α, s) →L[ℂ] W(α, s)) (S(a, hα, hs₀(hs)) (x j))))
        (C.disjiUnion K fun i _ j _ h ↦ hd i j h)) ≤
        c * (1 + 2 * Real.pi / (4 * δ)) ^ p * ∑' i, bd i ∧
      traceNorm (spectralJetBlockSum Q(a, hα, hs₀(hs)) (fun z : Z(χ) ↦ N(χ, z))
        (fun z m ↦ jet(z, m)) f
        (fun j ↦ Pspec(a, hα, hs₀(hs))
          ((A(hα, hs₀(hs), ψ 0) : W(α, s) →L[ℂ] W(α, s)) (S(a, hα, hs₀(hs)) (x j))))
        (C.disjiUnion K fun i _ j _ h ↦ hd i j h)) ≤
        c * (1 + 2 * Real.pi / (4 * δ)) ^ p * ∑' i, bd i := by
  let box := C.disjiUnion K fun i _ j _ h ↦ hd i j h
  let Qb := spectralJetBlockSum Q(a, hα, hs₀(hs)) (fun z : Z(χ) ↦ N(χ, z))
    (fun z m ↦ jet(z, m)) f (fun j ↦ S(a, hα, hs₀(hs)) (x j)) box
  have hPQ : Pspec(a, hα, hs₀(hs)) * Qb.val = Qb.val :=
    mul_spectralJetBlockSum_val_of_fixed (Pspec(a, hα, hs₀(hs))) Q(a, hα, hs₀(hs))
      (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m)) f (fun j ↦ S(a, hα, hs₀(hs)) (x j))
      (fun j ↦ spectralProjection_apply_of_mem a hα hs₀(hs)
        ((Θ(a, hα, hs₀(hs))).quotientEquivOrthogonal (x j)).property) box
  let κ : ℝ := 2 * Real.pi / (4 * δ)
  have hκ0 : 0 ≤ κ := by positivity
  let Btot : ℝ := ∑' i, bd i
  have hBtot : 0 ≤ Btot := tsum_nonneg hbd0
  have hδC : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
  have hmod (m : ℤ) (g : C𝔽) : (ψ m).val g =
      Complex.exp (((κ * m : ℝ) : ℂ) * Complex.I * (logNorm g : ℂ)) * (ψ 0).val g := by
    rw [hψ m g]
    congr 2
    push_cast [κ]
    field_simp
  have hdm (m : ℤ) : MellinShiftDominated χ X T φb p (ψ m) (c * (1 + |κ * m|) ^ p) :=
    hdom.modulate hc hφb (κ * m) (hmod m)
  have hJ (m : ℤ) : traceNorm (spectralJetBlockSum Q(a, hα, hs₀(hs)) (fun z : Z(χ) ↦ N(χ, z))
      (fun z m ↦ jet(z, m)) f
      (fun j ↦ Pspec(a, hα, hs₀(hs))
        ((A(hα, hs₀(hs), ψ m) : W(α, s) →L[ℂ] W(α, s)) (S(a, hα, hs₀(hs)) (x j)))) box) ≤
      c * (1 + |κ * m|) ^ p * Btot := by
    choose R hR hRn using hblocks (ψ m) (c * (1 + |κ * m|) ^ p) (hdm m).unshifted
    refine (traceNorm_spectralPart_jetBlockSum_le a hα hs χ x f hb (ψ m) K hd R hR C).trans ?_
    calc ∑ i ∈ C, traceNorm (R i) ≤ ∑ i ∈ C, c * (1 + |κ * m|) ^ p * bd i :=
          Finset.sum_le_sum fun i _ ↦ hRn i
      _ = c * (1 + |κ * m|) ^ p * ∑ i ∈ C, bd i := by rw [Finset.mul_sum]
      _ ≤ c * (1 + |κ * m|) ^ p * Btot :=
          mul_le_mul_of_nonneg_left (hbds.sum_le_tsum C fun i _ ↦ hbd0 i) (by positivity)
  have hpow (m : ℤ) : (1 + |κ * m|) ^ p ≤ (1 + κ) ^ p * (1 + |(m : ℝ)|) ^ p := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ p
    rw [abs_mul, abs_of_nonneg hκ0]
    nlinarith [abs_nonneg (m : ℝ)]
  have hQ (m : ℤ) : traceNorm ⟨((Pspec(a, hα, hs₀(hs))).comp (A(hα, hs₀(hs), ψ m))) * Qb.val,
      mul_mem_nuclearEndomorphisms_left _ Qb⟩ ≤ c * (1 + κ) ^ p * Btot * (1 + |(m : ℝ)|) ^ p := by
    refine ((le_of_eq (congrArg traceNorm (mul_spectralJetBlockSum
      ((Pspec(a, hα, hs₀(hs))).comp (A(hα, hs₀(hs), ψ m))) Q(a, hα, hs₀(hs))
      (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m)) f (fun j ↦ S(a, hα, hs₀(hs)) (x j))
      box))).trans (hJ m)).trans ?_
    calc c * (1 + |κ * m|) ^ p * Btot
        ≤ c * ((1 + κ) ^ p * (1 + |(m : ℝ)|) ^ p) * Btot :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpow m) hc) hBtot
      _ = c * (1 + κ) ^ p * Btot * (1 + |(m : ℝ)|) ^ p := by ring
  have hG := hrec (c * (1 + κ) ^ p * Btot) Qb hPQ hQ
  have h0 := hJ 0
  refine ⟨(le_of_eq (congrArg traceNorm (mul_spectralJetBlockSum
    ((Pgeom(a, hα, hs₀(hs))).comp (A(hα, hs₀(hs), ψ 0))) Q(a, hα, hs₀(hs))
    (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m)) f (fun j ↦ S(a, hα, hs₀(hs)) (x j))
    box)).symm).trans hG, h0.trans ?_⟩
  have h1 : (1 : ℝ) ≤ (1 + κ) ^ p := one_le_pow₀ (by linarith)
  have h2 : (1 + |κ * ((0 : ℤ) : ℝ)|) ^ p = 1 := by simp
  rw [h2, mul_one]
  exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hc h1) hBtot

set_option maxHeartbeats 1600000 in
/-- Paper: Theorem 10.4.3.5(2), p. 472, the geometric component for every test, with the zeros
summed by clusters, from a recursion for tests of small support. Suppose a system of clusters
with summable bounds `bd i` controls the cluster blocks of every test that is dominated on its
contours, and the test `φ` is dominated with shifts (the two conclusions of
`spectralStripConvolution_exists_commonClusters`). Suppose further that for some `δ₀ > 0` the
geometric part of a test supported where the logarithm of the norm is at most `δ₀` is bounded by
the spectral parts of its modulations, as in
`exists_traceNorm_geometricProjection_stripTestAction_le_of_modulated`. Then the geometric
blocks of `φ`, summed over finite unions of clusters, are bounded in trace norm.
The test is cut along the logarithm of the norm into finitely many pieces of small support
(`exists_smooth_partition_Icc`). Each piece is a translate of a test supported close to the
norm-one classes, which is dominated because the cutoff is a Fourier series in characters of
the norm on the support of `φ` and translation multiplies the Mellin transform by a bounded
factor. For such a test the recursion bounds the geometric part
(`traceNorm_jetBlockSum_le_of_dominated_modulated`), and a translation, which is a bounded
operator, carries the bound back to the piece.
Reconstruction: The paper gives no estimate for the geometric component. -/
theorem spectralStripGeometricBlocks_bddAbove_of_commonClusters_of_recursion
    (φ : BruhatCompactSupport C𝔽)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
    (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (hb : Bases(χ, x, f)) (X : ℝ) (hX : 0 < X) (T φb : PontryaginDual C₁ → ℤ → ℝ) (p : ℕ)
    {ι : Type*} (K : ι → Finset Z(χ)) (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (bd : ι → ℝ) (hbd0 : ∀ i, 0 ≤ bd i) (hbds : Summable bd)
    (hshift : ∀ ω k, ∀ w ∈ rectBoundary (-X) X (T ω k) (T ω (k + 1)), ∀ t : ℝ,
      ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ ω) (w + (t : ℂ) * Complex.I) g ∂μ𝔽‖ ≤
        (1 + |t|) ^ p * φb ω k)
    (hblocks : ∀ (ψ : BruhatCompactSupport C𝔽) (c : ℝ),
      (∀ ω k, ∀ w ∈ rectBoundary (-X) X (T ω k) (T ω (k + 1)),
        ‖∫ g : C𝔽, ψ.val g * ideleClassNormTwist (χ ω) w g ∂μ𝔽‖ ≤ c * φb ω k) →
      ∀ i, ∃ R : nuclearEndomorphisms H(a, hα, hs₀(hs)),
        R.val = spectralConvolutionFiniteSum (Aq(a, hα, hs₀(hs), ψ)) x f (K i)
          (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m)) ∧ traceNorm R ≤ c * bd i)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hrecursion : ∀ ψ : ℤ → BruhatCompactSupport C𝔽,
      (∀ (m : ℤ) (g : C𝔽), (ψ m).val g =
        Complex.exp (2 * Real.pi * Complex.I * m * (logNorm g / (4 * δ₀) : ℝ)) *
          (ψ 0).val g) →
      (∀ g, (ψ 0).val g ≠ 0 → |logNorm g| ≤ δ₀) →
      ∀ (B : ℝ) (Q : nuclearEndomorphisms (W(α, s))),
        Pspec(a, hα, hs₀(hs)) * Q.val = Q.val →
        (∀ m : ℤ, traceNorm ⟨((Pspec(a, hα, hs₀(hs))).comp (A(hα, hs₀(hs), ψ m))) * Q.val,
          mul_mem_nuclearEndomorphisms_left _ Q⟩ ≤ B * (1 + |(m : ℝ)|) ^ p) →
        traceNorm ⟨((Pgeom(a, hα, hs₀(hs))).comp (A(hα, hs₀(hs), ψ 0))) * Q.val,
          mul_mem_nuclearEndomorphisms_left _ Q⟩ ≤ B) :
    BddAbove (range fun C : Finset ι ↦ traceNorm
      (spectralJetBlockSum Q(a, hα, hs₀(hs)) (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m)) f
        (fun j ↦ Pgeom(a, hα, hs₀(hs))
          ((A(hα, hs₀(hs), φ) : W(α, s) →L[ℂ] W(α, s)) (S(a, hα, hs₀(hs)) (x j))))
        (C.disjiUnion K fun i _ j _ h ↦ hd i j h))) := by
  classical
  have hφb : ∀ ω k, 0 ≤ φb ω k := fun ω k ↦ by
    have hmem : ((X : ℝ) : ℂ) + ((T ω k : ℝ) : ℂ) * Complex.I ∈
        rectBoundary (-X) X (T ω k) (T ω (k + 1)) :=
      mem_rectBoundary_horizontal ⟨by linarith, le_rfl⟩ (Or.inl rfl)
    have h := (norm_nonneg _).trans (hshift ω k _ hmem 0)
    simpa using h
  have hdomφ : MellinShiftDominated χ X T φb p φ 1 := fun ω k w hw t ↦ by
    rw [one_mul]
    exact hshift ω k w hw t
  obtain ⟨R₀, hR₀, hsupp⟩ := exists_abs_logIdeleClassNorm_le_of_ne_zero φ
  obtain ⟨J, η, t, hηs, hη1, hηsupp, hηsum⟩ := exists_smooth_partition_Icc hδ₀ R₀
  -- The pieces of the test.
  choose φk hφk using fun k : ℕ ↦ WeightedConvolution.exists_bruhatCompactSupport_logProfile
    m𝔽 φ (h := fun r ↦ ((η k r : ℝ) : ℂ)) (Complex.ofRealCLM.contDiff.comp (hηs k))
  have hφk' (k : ℕ) (g : C𝔽) : (φk k).val g = ((η k (logNorm g) : ℝ) : ℂ) * φ.val g :=
    hφk k g
  -- Each cutoff is a Fourier series in characters of the norm on the support of the test.
  choose aη haη hsumη using fun k : ℕ ↦ exists_fourierSeries_on_Icc
    (h := fun r ↦ ((η k r : ℝ) : ℂ)) (Complex.ofRealCLM.contDiff.comp (hηs k)) hR₀
  let σ (m : ℤ) : ℝ := 2 * Real.pi * m / (4 * R₀)
  choose φs hφs using fun m : ℤ ↦ WeightedConvolution.exists_bruhatCompactSupport_logProfile
    m𝔽 φ (h := fun r ↦ Complex.exp (((σ m : ℝ) : ℂ) * Complex.I * (r : ℂ)))
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp)
  have hφs' (m : ℤ) (g : C𝔽) : (φs m).val g =
      Complex.exp (((σ m : ℝ) : ℂ) * Complex.I * (logNorm g : ℂ)) * φ.val g := hφs m g
  have hR₀C : (R₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR₀.ne'
  have hsumσ (k : ℕ) : Summable fun m : ℤ ↦ ‖aη k m‖ * (1 + |σ m|) ^ p := by
    refine Summable.of_nonneg_of_le (fun m ↦ by positivity) (fun m ↦ ?_)
      ((haη k p).mul_left ((1 + 2 * Real.pi / (4 * R₀)) ^ p))
    have h1 : (1 + |σ m|) ^ p ≤ (1 + 2 * Real.pi / (4 * R₀)) ^ p * (1 + |(m : ℝ)|) ^ p := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ p
      have h2 : |σ m| = 2 * Real.pi / (4 * R₀) * |(m : ℝ)| := by
        change |2 * Real.pi * m / (4 * R₀)| = _
        rw [show 2 * Real.pi * (m : ℝ) / (4 * R₀) = 2 * Real.pi / (4 * R₀) * m by ring, abs_mul,
          abs_of_nonneg (by positivity)]
      rw [h2]
      nlinarith [abs_nonneg (m : ℝ), (by positivity : (0 : ℝ) ≤ 2 * Real.pi / (4 * R₀))]
    calc ‖aη k m‖ * (1 + |σ m|) ^ p
        ≤ ‖aη k m‖ * ((1 + 2 * Real.pi / (4 * R₀)) ^ p * (1 + |(m : ℝ)|) ^ p) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = (1 + 2 * Real.pi / (4 * R₀)) ^ p * (‖aη k m‖ * (1 + |(m : ℝ)|) ^ p) := by ring
  let ck (k : ℕ) : ℝ := 1 * ∑' m : ℤ, ‖aη k m‖ * (1 + |σ m|) ^ p
  have hck (k : ℕ) : 0 ≤ ck k :=
    mul_nonneg zero_le_one (tsum_nonneg fun m ↦ by positivity)
  have hdomk (k : ℕ) : MellinShiftDominated χ X T φb p (φk k) (ck k) :=
    hdomφ.series zero_le_one hφb (φk k) φs σ (aη k) hφs' (hsumσ k) fun g ↦ by
      by_cases hg : φ.val g = 0
      · rw [hφk' k g, hg, mul_zero]
        refine hasSum_zero.congr_fun fun m ↦ ?_
        rw [hφs' m g, hg, mul_zero, mul_zero]
      · have h1 := (hsumη k (logNorm g) (hsupp g hg)).mul_right (φ.val g)
        rw [← hφk' k g] at h1
        refine h1.congr_fun fun m ↦ ?_
        rw [hφs' m g, ← mul_assoc]
        congr 3
        push_cast [σ]
        field_simp
  -- The pieces are translates of tests supported close to the norm-one classes.
  choose gk hgk using fun k : ℕ ↦ exists_logIdeleClassNorm_eq (F := F) (t k)
  choose φ0 hφ0 using fun k : ℕ ↦ exists_bruhatCompactSupport_translate (gk k)⁻¹ (φk k)
  have hφ0' (k : ℕ) (y : C𝔽) : (φ0 k).val y = (φk k).val (gk k * y) := by
    rw [hφ0 k y, inv_inv]
  have hφkt (k : ℕ) (y : C𝔽) : (φk k).val y = (φ0 k).val ((gk k)⁻¹ * y) := by
    rw [hφ0' k, mul_inv_cancel_left]
  let c0 (k : ℕ) : ℝ := ck k * Real.exp (X * |logNorm (gk k)⁻¹|)
  have hc0 (k : ℕ) : 0 ≤ c0 k := mul_nonneg (hck k) (Real.exp_pos _).le
  have hdom0 (k : ℕ) : MellinShiftDominated χ X T φb p (φ0 k) (c0 k) :=
    (hdomk k).translate hX.le (gk k)⁻¹ (hφ0 k)
  have hsupp0 (k : ℕ) (y : C𝔽) (hy : (φ0 k).val y ≠ 0) : |logNorm y| ≤ δ₀ := by
    rw [hφ0' k y, hφk' k] at hy
    have h1 : η k (logNorm (gk k * y)) ≠ 0 := fun h0 ↦ hy (by rw [h0]; simp)
    have h2 := hηsupp k _ h1
    rw [logIdeleClassNorm_mul, hgk k] at h2
    simpa using h2
  -- The modulations of the centred pieces.
  choose ψ hψ using fun (k : ℕ) (m : ℤ) ↦
    WeightedConvolution.exists_bruhatCompactSupport_logProfile m𝔽 (φ0 k)
      (h := fun r ↦ Complex.exp (2 * Real.pi * Complex.I * m * ((r / (4 * δ₀) : ℝ) : ℂ)))
      ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (contDiff_id.div_const _))).cexp)
  have hψ0 (k : ℕ) : ψ k 0 = φ0 k := Subtype.ext (funext fun g ↦ by
    rw [hψ k 0 g]
    simp)
  have hψm (k : ℕ) (m : ℤ) (g : C𝔽) : (ψ k m).val g =
      Complex.exp (2 * Real.pi * Complex.I * m * (logNorm g / (4 * δ₀) : ℝ)) *
        (ψ k 0).val g := by
    rw [hψ k m g, hψ0 k]
    rfl
  let Btot : ℝ := ∑' i, bd i
  let Bk (k : ℕ) : ℝ := c0 k * (1 + 2 * Real.pi / (4 * δ₀)) ^ p * Btot
  have hpiece (k : ℕ) (C : Finset ι) :=
    traceNorm_jetBlockSum_le_of_dominated_modulated a hα hs χ x f hb X T φb p hφb K hd bd hbd0
      hbds hblocks δ₀ hδ₀ (ψ k) (hψm k) (c0 k) (hc0 k) (by rw [hψ0 k]; exact hdom0 k)
      (fun B Q hPQ hsp ↦ hrecursion (ψ k) (hψm k)
        (fun g hg ↦ hsupp0 k g (by rwa [hψ0 k] at hg)) B Q hPQ hsp) C
  -- The test is the sum of its pieces, and each piece acts as a translation after its centred
  -- piece.
  let G : W(α, s) →L[ℂ] W(α, s) := Pgeom(a, hα, hs₀(hs))
  let P : W(α, s) →L[ℂ] W(α, s) := Pspec(a, hα, hs₀(hs))
  let Aφ : W(α, s) →L[ℂ] W(α, s) := A(hα, hs₀(hs), φ)
  let A0 (k : ℕ) : W(α, s) →L[ℂ] W(α, s) := A(hα, hs₀(hs), φ0 k)
  let Ak (k : ℕ) : W(α, s) →L[ℂ] W(α, s) := A(hα, hs₀(hs), φk k)
  let τk (k : ℕ) : W(α, s) →L[ℂ] W(α, s) :=
    hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs₀(hs) (gk k)
  have hG : ‖G‖ ≤ 1 := (Θ(a, hα, hs₀(hs))).starProjection_norm_le
  have hGP : G + P = 1 := by
    apply ContinuousLinearMap.ext
    intro u
    exact (Θ(a, hα, hs₀(hs))).starProjection_add_starProjection_orthogonal u
  have hAk (k : ℕ) : Ak k = τk k * A0 k :=
    stripTestAction_eq_translation_comp hα hs₀(hs) (gk k) (φ0 k) (φk k) (hφkt k)
  have hAsum : Aφ = ∑ k : Fin J, τk k * A0 k := by
    have hs1 : HasSum (fun k : Fin J ↦ (1 : ℂ) • Ak k) Aφ :=
      WeightedConvolution.hasSum_hardySobolevTestAction μ𝔽 m𝔽 (-α) α s (hStrip(hα))
      hs₀(hs) φ φ (fun k : Fin J ↦ φk k) (fun _ ↦ (1 : ℂ)) (hasSum_fintype _).summable
      (fun k g ↦ by
        rw [hφk' k g, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (hη1 k _))
      (fun g ↦ by
        have hval : ∑ k : Fin J, (1 : ℂ) * (φk k).val g = φ.val g := by
          by_cases hg : φ.val g = 0
          · simp [hφk', hg]
          · have h1 := hηsum (logNorm g) (hsupp g hg)
            have h2 : ∑ k : Fin J, ((η k (logNorm g) : ℝ) : ℂ) = 1 := by
              rw [Fin.sum_univ_eq_sum_range (fun k ↦ ((η k (logNorm g) : ℝ) : ℂ)) J,
                ← Complex.ofReal_sum, h1, Complex.ofReal_one]
            simp only [one_mul, hφk', ← Finset.sum_mul, h2]
        exact hval ▸ hasSum_fintype _)
    have hs2 : Aφ = ∑ k : Fin J, (1 : ℂ) • Ak k := hs1.unique (hasSum_fintype _)
    refine hs2.trans (Finset.sum_congr rfl fun k _ ↦ ?_)
    rw [one_smul]
    exact hAk k
  refine ⟨∑ k : Fin J, ‖τk k‖ * (Bk k + Bk k), ?_⟩
  rintro _ ⟨C, rfl⟩
  let box := C.disjiUnion K fun i _ j _ h ↦ hd i j h
  let Qb := spectralJetBlockSum Q(a, hα, hs₀(hs)) (fun z : Z(χ) ↦ N(χ, z))
    (fun z m ↦ jet(z, m)) f (fun j ↦ S(a, hα, hs₀(hs)) (x j)) box
  have h1 := traceNorm_mul_sum_mul_le Finset.univ G Aφ (fun k : Fin J ↦ τk k * A0 k) hAsum Qb
  have h3 (k : ℕ) : traceNorm ⟨(G * A0 k) * Qb.val, mul_mem_nuclearEndomorphisms_left _ Qb⟩ ≤
      Bk k := by
    have h := (hpiece k C).1
    rw [hψ0 k] at h
    exact (le_of_eq (congrArg traceNorm (mul_spectralJetBlockSum (G * A0 k) Q(a, hα, hs₀(hs))
      (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m)) f (fun j ↦ S(a, hα, hs₀(hs)) (x j))
      box))).trans h
  have h4 (k : ℕ) : traceNorm ⟨(P * A0 k) * Qb.val, mul_mem_nuclearEndomorphisms_left _ Qb⟩ ≤
      Bk k := by
    have h := (hpiece k C).2
    rw [hψ0 k] at h
    exact (le_of_eq (congrArg traceNorm (mul_spectralJetBlockSum (P * A0 k) Q(a, hα, hs₀(hs))
      (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m)) f (fun j ↦ S(a, hα, hs₀(hs)) (x j))
      box))).trans h
  calc traceNorm (spectralJetBlockSum Q(a, hα, hs₀(hs)) (fun z : Z(χ) ↦ N(χ, z))
        (fun z m ↦ jet(z, m)) f
        (fun j ↦ Pgeom(a, hα, hs₀(hs))
          ((A(hα, hs₀(hs), φ) : W(α, s) →L[ℂ] W(α, s)) (S(a, hα, hs₀(hs)) (x j)))) box)
      = traceNorm ⟨(G * Aφ) * Qb.val, mul_mem_nuclearEndomorphisms_left _ Qb⟩ :=
        (congrArg traceNorm (mul_spectralJetBlockSum (G * Aφ) Q(a, hα, hs₀(hs))
          (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m)) f (fun j ↦ S(a, hα, hs₀(hs)) (x j))
          box)).symm
    _ ≤ ∑ k : Fin J, traceNorm ⟨(G * (τk k * A0 k)) * Qb.val,
          mul_mem_nuclearEndomorphisms_left _ Qb⟩ := h1
    _ ≤ ∑ k : Fin J, ‖τk k‖ * (Bk k + Bk k) := Finset.sum_le_sum fun k _ ↦
        (traceNorm_geometricPart_mul_le G P (τk k) (A0 k) hG hGP Qb).trans
          (mul_le_mul_of_nonneg_left (add_le_add (h3 k) (h4 k)) (norm_nonneg _))

/-- Paper: Theorem 10.4.3.5(2), p. 472, the geometric component, when the density of the
Sobolev space is the polynomial `(1 + t ^ 2) ^ n`, for every test, with the zeros summed by
clusters. Suppose a system of clusters with summable bounds `bd i` controls the cluster blocks
of every test that is dominated on its contours, and the test `φ` is dominated with shifts
(the two conclusions of `spectralStripConvolution_exists_commonClusters`). Then the geometric
blocks of `φ`, summed over finite unions of clusters, are bounded in trace norm.
This is `spectralStripGeometricBlocks_bddAbove_of_commonClusters_of_recursion` with the
recursion of `exists_traceNorm_geometricProjection_stripTestAction_le_of_modulated`.
Reconstruction: The paper gives no estimate for the geometric component. -/
theorem spectralStripGeometricBlocks_bddAbove_of_commonClusters
    (n : ℕ) (hdens : ∀ t, intervalSobolevDensity (-α) α s t = (1 + t ^ 2) ^ n)
    (φ : BruhatCompactSupport C𝔽)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
    (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (hb : Bases(χ, x, f)) (X : ℝ) (hX : 0 < X) (T φb : PontryaginDual C₁ → ℤ → ℝ) (p : ℕ)
    {ι : Type*} (K : ι → Finset Z(χ)) (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (bd : ι → ℝ) (hbd0 : ∀ i, 0 ≤ bd i) (hbds : Summable bd)
    (hshift : ∀ ω k, ∀ w ∈ rectBoundary (-X) X (T ω k) (T ω (k + 1)), ∀ t : ℝ,
      ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ ω) (w + (t : ℂ) * Complex.I) g ∂μ𝔽‖ ≤
        (1 + |t|) ^ p * φb ω k)
    (hblocks : ∀ (ψ : BruhatCompactSupport C𝔽) (c : ℝ),
      (∀ ω k, ∀ w ∈ rectBoundary (-X) X (T ω k) (T ω (k + 1)),
        ‖∫ g : C𝔽, ψ.val g * ideleClassNormTwist (χ ω) w g ∂μ𝔽‖ ≤ c * φb ω k) →
      ∀ i, ∃ R : nuclearEndomorphisms H(a, hα, hs₀(hs)),
        R.val = spectralConvolutionFiniteSum (Aq(a, hα, hs₀(hs), ψ)) x f (K i)
          (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m)) ∧ traceNorm R ≤ c * bd i) :
    BddAbove (range fun C : Finset ι ↦ traceNorm
      (spectralJetBlockSum Q(a, hα, hs₀(hs)) (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m)) f
        (fun j ↦ Pgeom(a, hα, hs₀(hs))
          ((A(hα, hs₀(hs), φ) : W(α, s) →L[ℂ] W(α, s)) (S(a, hα, hs₀(hs)) (x j))))
        (C.disjiUnion K fun i _ j _ h ↦ hd i j h))) := by
  obtain ⟨δ₀, hδ₀, hrec⟩ :=
    exists_traceNorm_geometricProjection_stripTestAction_le_of_modulated (F := F) n p
  exact spectralStripGeometricBlocks_bddAbove_of_commonClusters_of_recursion a hα hs φ χ x f hb
    X hX T φb p K hd bd hbd0 hbds hshift hblocks δ₀ hδ₀
    fun ψ hψ hsupp B Q hPQ hsp ↦ hrec hα hs₀(hs) a hdens δ₀ hδ₀ le_rfl ψ hψ hsupp B Q hPQ hsp

/-- Paper: Theorem 10.4.3.5(2), p. 472, the geometric component, when the density of the
Sobolev space is `(1 + t ^ 2) ^ σ` for a real `σ`, for every test, with the zeros summed by
clusters. Suppose a system of clusters with summable bounds `bd i` controls the cluster blocks
of every test that is dominated on its contours, and the test `φ` is dominated with shifts
(the two conclusions of `spectralStripConvolution_exists_commonClusters`). Then the geometric
blocks of `φ`, summed over finite unions of clusters, are bounded in trace norm.
This is `spectralStripGeometricBlocks_bddAbove_of_commonClusters_of_recursion` with the
recursion of `exists_traceNorm_geometricProjection_stripTestAction_le_of_modulated_rpow` of
`Sec4b_BinomialRecursion`.
Reconstruction: The paper gives no estimate for the geometric component. -/
theorem spectralStripGeometricBlocks_bddAbove_of_commonClusters_rpow
    (σ : ℝ) (hdens : ∀ t, intervalSobolevDensity (-α) α s t = (1 + t ^ 2) ^ σ)
    (φ : BruhatCompactSupport C𝔽)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
    (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs)))
    (hb : Bases(χ, x, f)) (X : ℝ) (hX : 0 < X) (T φb : PontryaginDual C₁ → ℤ → ℝ) (p : ℕ)
    {ι : Type*} (K : ι → Finset Z(χ)) (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (bd : ι → ℝ) (hbd0 : ∀ i, 0 ≤ bd i) (hbds : Summable bd)
    (hshift : ∀ ω k, ∀ w ∈ rectBoundary (-X) X (T ω k) (T ω (k + 1)), ∀ t : ℝ,
      ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ ω) (w + (t : ℂ) * Complex.I) g ∂μ𝔽‖ ≤
        (1 + |t|) ^ p * φb ω k)
    (hblocks : ∀ (ψ : BruhatCompactSupport C𝔽) (c : ℝ),
      (∀ ω k, ∀ w ∈ rectBoundary (-X) X (T ω k) (T ω (k + 1)),
        ‖∫ g : C𝔽, ψ.val g * ideleClassNormTwist (χ ω) w g ∂μ𝔽‖ ≤ c * φb ω k) →
      ∀ i, ∃ R : nuclearEndomorphisms H(a, hα, hs₀(hs)),
        R.val = spectralConvolutionFiniteSum (Aq(a, hα, hs₀(hs), ψ)) x f (K i)
          (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m)) ∧ traceNorm R ≤ c * bd i) :
    BddAbove (range fun C : Finset ι ↦ traceNorm
      (spectralJetBlockSum Q(a, hα, hs₀(hs)) (fun z : Z(χ) ↦ N(χ, z)) (fun z m ↦ jet(z, m)) f
        (fun j ↦ Pgeom(a, hα, hs₀(hs))
          ((A(hα, hs₀(hs), φ) : W(α, s) →L[ℂ] W(α, s)) (S(a, hα, hs₀(hs)) (x j))))
        (C.disjiUnion K fun i _ j _ h ↦ hd i j h))) := by
  obtain ⟨δ₀, hδ₀, hrec⟩ :=
    exists_traceNorm_geometricProjection_stripTestAction_le_of_modulated_rpow (F := F) σ p
  exact spectralStripGeometricBlocks_bddAbove_of_commonClusters_of_recursion a hα hs φ χ x f hb
    X hX T φb p K hd bd hbd0 hbds hshift hblocks δ₀ hδ₀
    fun ψ hψ hsupp B Q hPQ hsp ↦ hrec hα hs₀(hs) a hdens δ₀ hδ₀ le_rfl ψ hψ hsupp B Q hPQ hsp

set_option maxHeartbeats 800000 in
/-- Paper: Theorem 10.4.3.5(2), pp. 472–473, on the line at even orders, for every test, with
the zeros summed by clusters. Let the density of the Sobolev space be the polynomial
`(1 + t ^ 2) ^ n`; this is the line, width zero, at the even order `s = 2 n`
(`intervalSobolevDensity_zero_even`). For every test `φ` there is a choice of the unitary
extensions of the norm-one characters such that, for every Markushevich basis realizing the
strip jets of that choice, the zeros can be grouped into finite clusters, pairwise disjoint and
covering all the zeros, along which
* the printed tensors (10.4.3.43), with convolution on the input factor, converge in the
  completed projective tensor product, and
* the sums of the geometric blocks `R_z` of `spectralStripGeometricKernel_blocks_bddAbove` of
  `Sec4b_Isolated` over finite unions of clusters are bounded in trace norm.
The second statement is the estimate for the geometric component that Theorem 10.4.3.5(2)
needs and the paper does not give, for unions of whole clusters.
The clusters are those of `spectralStripConvolution_exists_commonClusters`: the zeros of one
angular component between two consecutive heights. The bound is
`spectralStripGeometricBlocks_bddAbove_of_commonClusters`.
Reconstruction: The paper does not state this. Its Theorem 10.4.3.5(2) asserts convergence for
the rectangles of an arbitrary enumeration of the single zeros, for every width and order
`s > 1`; the estimate it would need for the geometric component is the recorded gap #7406.
Deviation: Stated for one choice of the unitary extensions, the one of a norm section, and for
sums over unions of whole clusters. -/
theorem spectralStripGeometricBlocks_clusters_bddAbove_of_polynomialDensity
    (n : ℕ) (hdens : ∀ t, intervalSobolevDensity (-α) α s t = (1 + t ^ 2) ^ n)
    (φ : BruhatCompactSupport C𝔽) :
    ∃ χ : PontryaginDual C₁ → PontryaginDual C𝔽, IsSpectralBasepointChoice χ ∧
      ∀ (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
        (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs))),
        Bases(χ, x, f) →
        ∃ (K : PontryaginDual C₁ × ℤ → Finset Z(χ))
          (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j)),
          (∀ z, ∃ i, z ∈ K i) ∧
          (∃ κT : Π(W'(α, s), W(α, s)),
            SpectralKernelSumsTendstoAlong K hd (fun z : Z(χ) ↦ N(χ, z))
              (fun z m ↦ jet(z, m)) (fun j ↦ D ((f j).comp (Aq(a, hα, hs₀(hs), φ))))
              (fun j ↦ S(a, hα, hs₀(hs)) (x j)) κT) ∧
          BddAbove (range fun C : Finset (PontryaginDual C₁ × ℤ) ↦ traceNorm
            (spectralJetBlockSum Q(a, hα, hs₀(hs)) (fun z : Z(χ) ↦ N(χ, z))
              (fun z m ↦ jet(z, m)) f
              (fun j ↦ Pgeom(a, hα, hs₀(hs))
                ((A(hα, hs₀(hs), φ) : W(α, s) →L[ℂ] W(α, s)) (S(a, hα, hs₀(hs)) (x j))))
              (C.disjiUnion K fun i _ j _ h ↦ hd i j h))) := by
  choose χ X T φb p K bd hχ hX hd hc hbd0 hbds hshift hblocks using
    spectralStripConvolution_exists_commonClusters (s := s) a hα hs₀(hs) φ
  refine ⟨χ, hχ, fun x f hb ↦ ⟨K, hd, hc, ?_, ?_⟩⟩
  · refine spectralStripTransposedKernel_along_of_blocks a hα hs χ x f hb φ K hd hc bd hbds
      fun i ↦ ?_
    have hdomφ : MellinShiftDominated χ X T φb p φ 1 := fun ω k w hw t ↦ by
      rw [one_mul]
      exact hshift ω k w hw t
    refine (hblocks x f hb.1 hb.2 φ 1 hdomφ.unshifted i).imp fun R h ↦ ⟨h.1, ?_⟩
    have h2 := h.2
    rwa [one_mul] at h2
  · exact spectralStripGeometricBlocks_bddAbove_of_commonClusters a hα hs n hdens φ χ x f hb X hX
      T φb p K hd bd hbd0 hbds hshift (hblocks x f hb.1 hb.2)

set_option maxHeartbeats 800000 in
/-- Paper: Theorem 10.4.3.5(2), pp. 472–473, on the line at every order, for every test, with
the zeros summed by clusters. Let the density of the Sobolev space be `(1 + t ^ 2) ^ σ` for a
real `σ`; this is the line, width zero, at the order `s = 2 σ`
(`intervalSobolevDensity_width_zero`). For every test `φ` there is a choice of the unitary
extensions of the norm-one characters such that, for every Markushevich basis realizing the
strip jets of that choice, the zeros can be grouped into finite clusters, pairwise disjoint and
covering all the zeros, along which
* the printed tensors (10.4.3.43), with convolution on the input factor, converge in the
  completed projective tensor product, and
* the sums of the geometric blocks `R_z` of `spectralStripGeometricKernel_blocks_bddAbove` of
  `Sec4b_Isolated` over finite unions of clusters are bounded in trace norm.
This is `spectralStripGeometricBlocks_clusters_bddAbove_of_polynomialDensity` for every real
exponent, with the recursion of `Sec4b_BinomialRecursion`.
Reconstruction: The paper does not state this. For positive widths the estimate of the
geometric component stays open; that is the recorded gap #7406.
Deviation: Stated for one choice of the unitary extensions, the one of a norm section, and for
sums over unions of whole clusters. -/
theorem spectralStripGeometricBlocks_clusters_bddAbove_of_rpowDensity
    (σ : ℝ) (hdens : ∀ t, intervalSobolevDensity (-α) α s t = (1 + t ^ 2) ^ σ)
    (φ : BruhatCompactSupport C𝔽) :
    ∃ χ : PontryaginDual C₁ → PontryaginDual C𝔽, IsSpectralBasepointChoice χ ∧
      ∀ (x : SpectralStripJetIndex χ a α s → H(a, hα, hs₀(hs)))
        (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(a, hα, hs₀(hs))),
        Bases(χ, x, f) →
        ∃ (K : PontryaginDual C₁ × ℤ → Finset Z(χ))
          (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j)),
          (∀ z, ∃ i, z ∈ K i) ∧
          (∃ κT : Π(W'(α, s), W(α, s)),
            SpectralKernelSumsTendstoAlong K hd (fun z : Z(χ) ↦ N(χ, z))
              (fun z m ↦ jet(z, m)) (fun j ↦ D ((f j).comp (Aq(a, hα, hs₀(hs), φ))))
              (fun j ↦ S(a, hα, hs₀(hs)) (x j)) κT) ∧
          BddAbove (range fun C : Finset (PontryaginDual C₁ × ℤ) ↦ traceNorm
            (spectralJetBlockSum Q(a, hα, hs₀(hs)) (fun z : Z(χ) ↦ N(χ, z))
              (fun z m ↦ jet(z, m)) f
              (fun j ↦ Pgeom(a, hα, hs₀(hs))
                ((A(hα, hs₀(hs), φ) : W(α, s) →L[ℂ] W(α, s)) (S(a, hα, hs₀(hs)) (x j))))
              (C.disjiUnion K fun i _ j _ h ↦ hd i j h))) := by
  choose χ X T φb p K bd hχ hX hd hc hbd0 hbds hshift hblocks using
    spectralStripConvolution_exists_commonClusters (s := s) a hα hs₀(hs) φ
  refine ⟨χ, hχ, fun x f hb ↦ ⟨K, hd, hc, ?_, ?_⟩⟩
  · refine spectralStripTransposedKernel_along_of_blocks a hα hs χ x f hb φ K hd hc bd hbds
      fun i ↦ ?_
    have hdomφ : MellinShiftDominated χ X T φb p φ 1 := fun ω k w hw t ↦ by
      rw [one_mul]
      exact hshift ω k w hw t
    refine (hblocks x f hb.1 hb.2 φ 1 hdomφ.unshifted i).imp fun R h ↦ ⟨h.1, ?_⟩
    have h2 := h.2
    rwa [one_mul] at h2
  · exact spectralStripGeometricBlocks_bddAbove_of_commonClusters_rpow a hα hs σ hdens φ χ x f hb X hX
      T φb p K hd bd hbd0 hbds hshift (hblocks x f hb.1 hb.2)

end Clusters

end RiemannMasullo
