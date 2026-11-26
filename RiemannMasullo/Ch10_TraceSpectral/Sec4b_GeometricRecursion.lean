module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_ClusterGeometric
public import RiemannMasullo.Ch09_HardySobolev.Sec3_AdjointPolynomial
import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # The geometric part of Theorem 10.4.3.5 on the line: an exact formula and a recursion

Theorem 10.4.3.5(2)–(3), pp. 472–473, needs the geometric component of the ambient kernel
tensors, the part in the theta subspace of the convolved lifts. As an operator it is the
commutator `P^geom ∘ A(φ) ∘ P^spec` of the convolution with the spectral projection
(`stripTestAction_comp_spectralProjection_sub` of `Sec4b_ClusterGeometric`). The paper gives no
formula or estimate for it.

On the base interval `{0}` at an even Sobolev order `s = 2 n` the density of the Sobolev space
is the polynomial `(1 + t ^ 2) ^ n` of the logarithm of the norm
(`intervalSobolevDensity_zero_even`). Then:

* The commutator is an exact finite sum of convolutions by the test times positive powers of
  minus that logarithm, each followed by multiplication by a function bounded by one and then
  by the geometric projection (`geometricProjection_stripTestAction_spectralProjection_eq_sum`).
  This comes from the formula for the adjoint of a convolution in
  `Ch09_HardySobolev/Sec3_AdjointPolynomial`.
* Hence a recursion (`traceNorm_geometricPart_le_of_recursion`): for a test supported close to
  the norm-one classes, the trace norm of the geometric part of `A(φ) ∘ Q`, for a nuclear `Q`
  with values in the orthogonal complement of the theta subspace, is bounded by the trace norms
  of the spectral parts of `A(φ_j) ∘ Q`, where `φ_j` is `φ` times the `j`-th power of minus the
  logarithm (`traceNorm_geometricProjection_stripTestAction_le_of_logPow`).

`Sec4b_Isolated` applies this to the sums over clusters of zeros. The spectral parts are lifts
of the quotient convolutions of §10.3, so the bound that Theorem 10.4.3.5(2) lacks for the
geometric component is reduced to bounds of the kind of §10.3, for the family `φ_j`. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set UniformSpace
open scoped NNReal NumberField.AdeleRing TensorProduct Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

section TraceNormRecursion

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

private theorem traceNorm_nonneg' (T : nuclearEndomorphisms W) : 0 ≤ traceNorm T := by
  let : Norm (nuclearEndomorphisms W) := ⟨traceNorm⟩
  exact (traceNorm_normedSpaceCore (H := W)).norm_nonneg T

private theorem traceNorm_add_le' (S T : nuclearEndomorphisms W) :
    traceNorm (S + T) ≤ traceNorm S + traceNorm T := by
  let : Norm (nuclearEndomorphisms W) := ⟨traceNorm⟩
  exact (traceNorm_normedSpaceCore (H := W)).norm_triangle S T

private theorem traceNorm_smul' (c : ℂ) (T : nuclearEndomorphisms W) :
    traceNorm (c • T) = ‖c‖ * traceNorm T := by
  let : Norm (nuclearEndomorphisms W) := ⟨traceNorm⟩
  exact (traceNorm_normedSpaceCore (H := W)).norm_smul c T

private theorem traceNorm_sum_le' {ι : Type*} (s : Finset ι) (T : ι → nuclearEndomorphisms W) :
    traceNorm (∑ i ∈ s, T i) ≤ ∑ i ∈ s, traceNorm (T i) := by
  let : Norm (nuclearEndomorphisms W) := ⟨traceNorm⟩
  have hc := traceNorm_normedSpaceCore (H := W)
  have hzero : traceNorm (0 : nuclearEndomorphisms W) = 0 := (hc.norm_eq_zero_iff 0).mpr rfl
  exact s.le_sum_of_subadditive traceNorm hzero.le hc.toCore.norm_triangle T

private theorem traceNorm_neg' (T : nuclearEndomorphisms W) : traceNorm (-T) = traceNorm T := by
  rw [← neg_one_smul ℂ T, traceNorm_smul', norm_neg, norm_one, one_mul]

/-- A recursion for the trace norm of the part of an operator that an idempotent splitting
`G + P = 1` sends from the range of `P` into the range of `G`. Let `A 0, A 1, …` be bounded
operators with `G (A j) P = -∑ i, c i • G (M i) (A (j + e i)) P`, with contractions `M i` and
nonnegative `c i`, and let `Q` be nuclear with `P Q = Q`. If `‖A j‖` and the trace norms of
`P (A j) Q` are at most constants times `δ ^ j`, and `∑ i, c i δ ^ (e i) ≤ θ < 1`, then the trace
norm of `G (A 0) Q` is at most `θ / (1 - θ)` times the constant for `P (A j) Q`. The norms
`‖A j‖` enter only to make the remainder of the iteration tend to zero. -/
theorem traceNorm_geometricPart_le_of_recursion {ι : Type*} (s : Finset ι)
    (G P : W →L[ℂ] W) (hG : ‖G‖ ≤ 1) (hGP : G + P = 1)
    (A : ℕ → W →L[ℂ] W) (M : ι → W →L[ℂ] W) (hM : ∀ i ∈ s, ‖M i‖ ≤ 1)
    (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) (e : ι → ℕ)
    (hrec : ∀ j, G * (A j * P) = -∑ i ∈ s, (c i : ℂ) • (G * (M i * (A (j + e i) * P))))
    (Q : nuclearEndomorphisms W) (hPQ : P * Q.val = Q.val)
    (M₀ δ B θ : ℝ) (hδ : 0 ≤ δ) (hA : ∀ j, ‖A j‖ ≤ M₀ * δ ^ j)
    (hspec : ∀ j, traceNorm ⟨(P * A j) * Q.val, mul_mem_nuclearEndomorphisms_left _ Q⟩ ≤
      B * δ ^ j)
    (hθ : ∑ i ∈ s, c i * δ ^ e i ≤ θ) (hθ1 : θ < 1) :
    traceNorm ⟨(G * A 0) * Q.val, mul_mem_nuclearEndomorphisms_left _ Q⟩ ≤ θ / (1 - θ) * B := by
  let L (X : W →L[ℂ] W) (T : nuclearEndomorphisms W) : nuclearEndomorphisms W :=
    ⟨X * T.val, mul_mem_nuclearEndomorphisms_left X T⟩
  let g (j : ℕ) : ℝ := traceNorm (L (G * A j) Q)
  let τ (j : ℕ) : ℝ := traceNorm (L (P * A j) Q)
  let tQ := traceNorm Q
  have htQ : 0 ≤ tQ := traceNorm_nonneg' Q
  have hθ0 : 0 ≤ θ := (Finset.sum_nonneg fun i hi ↦ mul_nonneg (hc i hi) (pow_nonneg hδ _)).trans hθ
  have hB : 0 ≤ B := by
    have h := (traceNorm_nonneg' _).trans (hspec 0)
    simpa using h
  have hM₀ : 0 ≤ M₀ := by
    have h := (norm_nonneg _).trans (hA 0)
    simpa using h
  -- The operator identity behind one step of the recursion.
  have hstep (j : ℕ) : L (G * A j) Q = -∑ i ∈ s, (c i : ℂ) •
      L (G * M i) (L (G * A (j + e i)) Q + L (P * A (j + e i)) Q) := by
    apply Subtype.ext
    have hsplit (k : ℕ) : A k * Q.val = (G * A k) * Q.val + (P * A k) * Q.val := by
      rw [← add_mul, ← add_mul, hGP, one_mul]
    calc (G * A j) * Q.val = (G * (A j * P)) * Q.val := by
          rw [mul_assoc, mul_assoc, mul_assoc, hPQ]
      _ = -∑ i ∈ s, (c i : ℂ) • ((G * M i) * (A (j + e i) * Q.val)) := by
          rw [hrec j, neg_mul, Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [smul_mul_assoc]
          congr 1
          rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, hPQ]
      _ = _ := by
          simp only [L, Submodule.coe_neg, Submodule.coe_sum, Submodule.coe_smul,
            Submodule.coe_add]
          congr 1
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hsplit (j + e i)]
  have hrecg (j : ℕ) : g j ≤ ∑ i ∈ s, c i * (g (j + e i) + τ (j + e i)) := by
    change traceNorm (L (G * A j) Q) ≤ _
    rw [hstep j, traceNorm_neg']
    refine (traceNorm_sum_le' s _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
    rw [traceNorm_smul', Complex.norm_real, Real.norm_of_nonneg (hc i hi)]
    refine mul_le_mul_of_nonneg_left ?_ (hc i hi)
    have h1 := traceNorm_mul_left_le (G * M i) (L (G * A (j + e i)) Q + L (P * A (j + e i)) Q)
    have h2 : ‖G * M i‖ ≤ 1 := (norm_mul_le G (M i)).trans
      ((mul_le_mul hG (hM i hi) (norm_nonneg _) zero_le_one).trans (one_mul 1).le)
    have h3 := traceNorm_add_le' (L (G * A (j + e i)) Q) (L (P * A (j + e i)) Q)
    exact h1.trans ((mul_le_mul_of_nonneg_right h2 (traceNorm_nonneg' _)).trans
      ((one_mul _).le.trans h3))
  have hprior (j : ℕ) : g j ≤ δ ^ j * (M₀ * tQ) := by
    have h1 := traceNorm_mul_left_le (G * A j) Q
    have h2 : ‖G * A j‖ ≤ M₀ * δ ^ j := (norm_mul_le G (A j)).trans
      ((mul_le_mul hG (hA j) (norm_nonneg _) zero_le_one).trans (one_mul _).le)
    calc g j ≤ ‖G * A j‖ * tQ := h1
      _ ≤ M₀ * δ ^ j * tQ := mul_le_mul_of_nonneg_right h2 htQ
      _ = δ ^ j * (M₀ * tQ) := by ring
  let E (N : ℕ) : ℝ := θ ^ N * (M₀ * tQ) + B * ∑ r ∈ Finset.range N, θ ^ (r + 1)
  have hE0 (N : ℕ) : 0 ≤ E N :=
    add_nonneg (mul_nonneg (pow_nonneg hθ0 _) (mul_nonneg hM₀ htQ))
      (mul_nonneg hB (Finset.sum_nonneg fun r _ ↦ pow_nonneg hθ0 _))
  have hind (N : ℕ) : ∀ j, g j ≤ δ ^ j * E N := by
    induction N with
    | zero =>
      intro j
      simpa [E] using hprior j
    | succ N ih =>
      intro j
      have hτ (k : ℕ) : τ k ≤ B * δ ^ k := hspec k
      calc g j ≤ ∑ i ∈ s, c i * (g (j + e i) + τ (j + e i)) := hrecg j
        _ ≤ ∑ i ∈ s, c i * (δ ^ (j + e i) * E N + B * δ ^ (j + e i)) :=
            Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left
              (add_le_add (ih _) (hτ _)) (hc i hi)
        _ = (∑ i ∈ s, c i * δ ^ e i) * (δ ^ j * (E N + B)) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [pow_add]
            ring
        _ ≤ θ * (δ ^ j * (E N + B)) :=
            mul_le_mul_of_nonneg_right hθ (mul_nonneg (pow_nonneg hδ _) (add_nonneg (hE0 N) hB))
        _ = δ ^ j * E (N + 1) := by
            simp only [E]
            rw [Finset.sum_range_succ' (fun r ↦ θ ^ (r + 1)) N]
            simp only [pow_succ, Finset.mul_sum]
            ring_nf
            simp only [Finset.mul_sum]
            ring_nf
  have hgeom (N : ℕ) : ∑ r ∈ Finset.range N, θ ^ (r + 1) ≤ θ / (1 - θ) := by
    have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
    have h2 : ∑ r ∈ Finset.range N, θ ^ (r + 1) = θ * ∑ r ∈ Finset.range N, θ ^ r := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ ↦ by ring
    rw [h2, geom_sum_eq (by linarith : θ ≠ 1), div_eq_mul_inv]
    have h3 : (θ ^ N - 1) / (θ - 1) ≤ (1 - θ)⁻¹ := by
      rw [show (θ ^ N - 1) / (θ - 1) = (1 - θ ^ N) / (1 - θ) by
        rw [← neg_sub 1 (θ ^ N), ← neg_sub 1 θ, neg_div_neg_eq], div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.mpr (by linarith))
        (by linarith [pow_nonneg hθ0 N])
    exact mul_le_mul_of_nonneg_left h3 hθ0
  have hbound (N : ℕ) : g 0 ≤ θ ^ N * (M₀ * tQ) + θ / (1 - θ) * B := by
    have h := hind N 0
    rw [pow_zero, one_mul] at h
    refine h.trans (add_le_add le_rfl ?_)
    rw [mul_comm B]
    exact mul_le_mul_of_nonneg_right (hgeom N) hB
  have hlim : Tendsto (fun N : ℕ ↦ θ ^ N * (M₀ * tQ) + θ / (1 - θ) * B) atTop
      (𝓝 (0 * (M₀ * tQ) + θ / (1 - θ) * B)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const _).add_const _
  rw [zero_mul, zero_add] at hlim
  exact ge_of_tendsto' hlim hbound

end TraceNormRecursion

section InvariantSubspace

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- Let `K` be a closed subspace of a Hilbert space with orthogonal projection `G`, and `P` the
projection onto its orthogonal complement. If `A'` preserves `K`, its adjoint preserves the
orthogonal complement, so `G ∘ A'† ∘ P = 0`. Hence, for an operator
`A = A'† - ∑ i, c i • T i ∘ B i`, the part `G ∘ A ∘ P` is `-∑ i, c i • G ∘ T i ∘ B i ∘ P`. -/
theorem starProjection_comp_comp_orthogonal_eq_neg_sum (K : Submodule ℂ W)
    [K.HasOrthogonalProjection] {ι : Type*} (s : Finset ι) (A A' : W →L[ℂ] W)
    (hA' : ∀ w ∈ K, A' w ∈ K) (c : ι → ℂ) (T B : ι → W →L[ℂ] W)
    (hA : A = A'.adjoint - ∑ i ∈ s, c i • (T i).comp (B i)) :
    K.starProjection.comp (A.comp Kᗮ.starProjection) =
      -∑ i ∈ s, c i • K.starProjection.comp ((T i).comp ((B i).comp Kᗮ.starProjection)) := by
  have hzero : K.starProjection.comp (A'.adjoint.comp Kᗮ.starProjection) = 0 := by
    apply ContinuousLinearMap.ext
    intro u
    have hv : Kᗮ.starProjection u ∈ Kᗮ := Kᗮ.starProjection_apply_mem u
    have hmem : A'.adjoint (Kᗮ.starProjection u) ∈ Kᗮ := by
      rw [Submodule.mem_orthogonal]
      intro w hw
      rw [ContinuousLinearMap.adjoint_inner_right]
      exact (Submodule.mem_orthogonal _ _).mp hv _ (hA' w hw)
    exact (Submodule.starProjection_apply_eq_zero_iff K).mpr hmem
  rw [hA, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, hzero, zero_sub]
  congr 1
  apply ContinuousLinearMap.ext
  intro u
  simp [map_sum, map_smul]

end InvariantSubspace

section JetBlockSums

variable {W H J Z : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Paper: (10.4.3.43), p. 472, as operators. The sum over a finite set of zeros, and over the
jets kept at each, of the rank-one operators `w ↦ f_j (q w) • v_j` on the ambient space, as a
nuclear endomorphism. With `v_j` the lift of the `j`-th biorthogonal vector this is the lifted
block projection of the set of zeros; with `v_j` the geometric projection of the convolved lift
it is the sum of the geometric blocks of `spectralStripGeometricKernel_blocks_bddAbove`. -/
def spectralJetBlockSum (q : W →L[ℂ] H) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (f : J → StrongDual ℂ H) (v : J → W) (K : Finset Z) : nuclearEndomorphisms W :=
  ∑ z ∈ K, ∑ m : Fin (N z),
    ⟨((f (jet z m)).comp q).smulRight (v (jet z m)), smulRight_mem_nuclearEndomorphisms _ _⟩

/-- A bounded operator composed after a sum of jet blocks acts on the output vectors. -/
theorem mul_spectralJetBlockSum (X : W →L[ℂ] W) (q : W →L[ℂ] H) (N : Z → ℕ)
    (jet : (z : Z) → Fin (N z) → J) (f : J → StrongDual ℂ H) (v : J → W) (K : Finset Z) :
    (⟨X * (spectralJetBlockSum q N jet f v K).val, mul_mem_nuclearEndomorphisms_left X _⟩ :
      nuclearEndomorphisms W) = spectralJetBlockSum q N jet f (fun j ↦ X (v j)) K := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro w
  simp [spectralJetBlockSum, map_sum, map_smul]

end JetBlockSums

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" =>
  (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (logIdeleClassNorm F)
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α s
local notation "Θ(" a ", " hα ", " hs ")" => globalThetaSobolev F a (hStrip(hα)) hs
local notation "A(" hα ", " hs ", " φ ")" =>
  hardySobolevTestAction μ𝔽 m𝔽 _ _ _ (hStrip(hα)) hs φ
local notation "Pspec(" a ", " hα ", " hs ")" => spectralProjection (F := F) a hα hs
local notation "Pgeom(" a ", " hα ", " hs ")" => geometricProjection (F := F) a hα hs

open WeightedConvolution in
/-- Paper: Proposition 9.2.1.8, p. 410. On the base interval `{0}` at the even Sobolev order
`s = 2 n`, the density is the polynomial `(1 + t ^ 2) ^ n` of the logarithmic coordinate. -/
theorem intervalSobolevDensity_zero_even {α s : ℝ} (hα0 : α = 0) (n : ℕ) (hsn : s = 2 * n)
    (t : ℝ) : intervalSobolevDensity (-α) α s t = (1 + t ^ 2) ^ n := by
  subst hα0 hsn
  unfold intervalSobolevDensity
  rw [show (2 * (n : ℝ)) / 2 = n by ring, Real.rpow_natCast]
  simp

section CommutatorFormula

open WeightedConvolution

variable {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)

/-- Paper: Theorem 10.4.3.5(2)–(3), pp. 472–473, the geometric component, when the density of
the Sobolev space is the polynomial `(1 + t ^ 2) ^ n`. The commutator `P^geom ∘ A(φ) ∘ P^spec`
of convolution with the spectral projection is an exact finite sum: over the pairs
`(k, l) ≠ (0, 0)` with `l ≤ k ≤ n`, minus the binomial coefficient times
`P^geom ∘ T ∘ A(φ_{k+l}) ∘ P^spec`, where `φ_e` is the test `φ` times the `e`-th power of minus
the logarithm of the norm and `T` is multiplication by a function of that logarithm bounded by
one. The reason: by `hardySobolevTestAction_adjoint_eq_sum_polyWeight` the sum over all pairs,
with `(0, 0)` giving `A(φ)`, is the adjoint of convolution by the reflected conjugate of `φ`,
and the adjoint of a convolution preserves the orthogonal complement of the theta subspace.
Reconstruction: The paper gives no formula or estimate for the geometric component. -/
theorem geometricProjection_stripTestAction_spectralProjection_eq_sum (a : ℝ) (n : ℕ)
    (hdens : ∀ t, intervalSobolevDensity (-α) α s t = (1 + t ^ 2) ^ n)
    (φ : BruhatCompactSupport C𝔽) (Φ : ℕ → BruhatCompactSupport C𝔽)
    (hΦ : ∀ e g, (Φ e).val g = (((-logNorm g) ^ e : ℝ) : ℂ) * φ.val g)
    (T : (Σ _ : ℕ, ℕ) → (W(α, s) →L[ℂ] W(α, s)))
    (hT : ∀ i u, (T i u : C𝔽 → ℂ) =ᵐ[intervalSobolevMeasure μ𝔽 logNorm (-α) α s]
      fun x ↦ ((polyWeightMask i (logNorm x) : ℝ) : ℂ) * u x) :
    (Pgeom(a, hα, hs)).comp ((A(hα, hs, φ)).comp (Pspec(a, hα, hs))) =
      -∑ i ∈ (polyWeightIndex n).erase ⟨0, 0⟩, ((polyWeightCoeff n i : ℕ) : ℂ) •
        (Pgeom(a, hα, hs)).comp ((T i).comp
          ((A(hα, hs, Φ (i.1 + i.2))).comp (Pspec(a, hα, hs)))) := by
  obtain ⟨φ', hφ'⟩ := exists_bruhatCompactSupport_conjInv φ
  exact starProjection_comp_comp_orthogonal_eq_neg_sum (Θ(a, hα, hs))
    ((polyWeightIndex n).erase ⟨0, 0⟩) (A(hα, hs, φ)) (A(hα, hs, φ'))
    (fun w hw ↦ (Submodule.Quotient.mk_eq_zero _).mp
      (hardySobolevTestAction_preserves_globalTheta (F := F) a (hStrip(hα)) hs φ' hw))
    (fun i ↦ ((polyWeightCoeff n i : ℕ) : ℂ)) T (fun i ↦ A(hα, hs, Φ (i.1 + i.2)))
    (hardySobolevTestAction_eq_adjoint_sub_sum_polyWeight μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs n
      hdens φ φ' hφ' Φ hΦ T hT)

end CommutatorFormula

section GeometricRecursion

open WeightedConvolution

variable {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)

/-- Paper: Theorem 10.4.3.5(2), p. 472, the geometric component, when the density of the
Sobolev space is the polynomial `(1 + t ^ 2) ^ n`. Let the test `φ` be supported where the
logarithm of the norm is at most `δ` in absolute value, with `(1 + δ + δ ^ 2) ^ n < 2`, and let
`φ_j` be `φ` times the `j`-th power of minus that logarithm. Let `Q` be a nuclear operator with
values in the orthogonal complement of the theta subspace. If the spectral parts
`P^spec ∘ A(φ_j) ∘ Q` have trace norms at most `B δ ^ j`, then the geometric part
`P^geom ∘ A(φ) ∘ Q` has trace norm at most `B` times
`((1 + δ + δ ^ 2) ^ n - 1) / (2 - (1 + δ + δ ^ 2) ^ n)`.
So a bound for the spectral parts of the family `φ_j`, which are lifts of the quotient
convolutions of §10.3, bounds the geometric part of `φ`. The proof is the recursion
`traceNorm_geometricPart_le_of_recursion` fed with the exact formula
`geometricProjection_stripTestAction_spectralProjection_eq_sum` for each `φ_j`.
Reconstruction: The paper gives no estimate for the geometric component. -/
theorem traceNorm_geometricProjection_stripTestAction_le_of_logPow (a : ℝ) (n : ℕ)
    (hdens : ∀ t, intervalSobolevDensity (-α) α s t = (1 + t ^ 2) ^ n)
    (φ : BruhatCompactSupport C𝔽) (Φ : ℕ → BruhatCompactSupport C𝔽)
    (hΦ : ∀ e g, (Φ e).val g = (((-logNorm g) ^ e : ℝ) : ℂ) * φ.val g)
    (δ B : ℝ) (hδ : 0 ≤ δ) (hsupp : ∀ g, φ.val g ≠ 0 → |logNorm g| ≤ δ)
    (hθ : (1 + δ + δ ^ 2) ^ n < 2)
    (Q : nuclearEndomorphisms (W(α, s))) (hPQ : Pspec(a, hα, hs) * Q.val = Q.val)
    (hspec : ∀ j, traceNorm ⟨((Pspec(a, hα, hs)).comp (A(hα, hs, Φ j))) * Q.val,
      mul_mem_nuclearEndomorphisms_left _ Q⟩ ≤ B * δ ^ j) :
    traceNorm ⟨((Pgeom(a, hα, hs)).comp (A(hα, hs, φ))) * Q.val,
      mul_mem_nuclearEndomorphisms_left _ Q⟩ ≤
      ((1 + δ + δ ^ 2) ^ n - 1) / (2 - (1 + δ + δ ^ 2) ^ n) * B := by
  have hΦ0 : Φ 0 = φ := Subtype.ext (funext fun g ↦ by rw [hΦ]; simp)
  subst hΦ0
  choose T hTn hT using fun i : (Σ _ : ℕ, ℕ) ↦ exists_polyWeightMask_multiplier μ𝔽 m𝔽 (-α) α s i
  obtain ⟨M₀, hM₀⟩ := exists_hardySobolevTestAction_logPow_norm_le μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs
    (Φ 0) Φ hΦ δ hδ hsupp
  let θ := Θ(a, hα, hs)
  let G := Pgeom(a, hα, hs)
  let P := Pspec(a, hα, hs)
  let Aj (j : ℕ) : W(α, s) →L[ℂ] W(α, s) := A(hα, hs, Φ j)
  have h00 : (⟨0, 0⟩ : Σ _ : ℕ, ℕ) ∈ polyWeightIndex n := by
    simp [polyWeightIndex]
  have hG : ‖G‖ ≤ 1 := θ.starProjection_norm_le
  have hGP : G + P = 1 := by
    apply ContinuousLinearMap.ext
    intro u
    exact θ.starProjection_add_starProjection_orthogonal u
  have hrec (j : ℕ) : G * (Aj j * P) = -∑ i ∈ (polyWeightIndex n).erase ⟨0, 0⟩,
      (((polyWeightCoeff n i : ℝ)) : ℂ) • (G * (T i * (Aj (j + (i.1 + i.2)) * P))) := by
    have hΦj (e : ℕ) (g : C𝔽) :
        (Φ (j + e)).val g = (((-logNorm g) ^ e : ℝ) : ℂ) * (Φ j).val g := by
      rw [hΦ (j + e) g, hΦ j g, pow_add]
      push_cast
      ring
    have h := geometricProjection_stripTestAction_spectralProjection_eq_sum (F := F) hα hs a n
      hdens (Φ j) (fun e ↦ Φ (j + e)) hΦj T hT
    refine h.trans (congrArg Neg.neg (Finset.sum_congr rfl fun i _ ↦ ?_))
    rw [Complex.ofReal_natCast]
    rfl
  have hθsum : ∑ i ∈ (polyWeightIndex n).erase ⟨0, 0⟩,
      (polyWeightCoeff n i : ℝ) * δ ^ (i.1 + i.2) ≤ (1 + δ + δ ^ 2) ^ n - 1 := by
    rw [Finset.sum_erase_eq_sub h00, sum_polyWeightCoeff_mul_pow]
    simp [polyWeightCoeff]
  have hmain := traceNorm_geometricPart_le_of_recursion ((polyWeightIndex n).erase ⟨0, 0⟩) G P hG
    hGP Aj T (fun i _ ↦ hTn i) (fun i ↦ (polyWeightCoeff n i : ℝ)) (fun i _ ↦ Nat.cast_nonneg _)
    (fun i ↦ i.1 + i.2) hrec Q hPQ M₀ δ B ((1 + δ + δ ^ 2) ^ n - 1) hδ hM₀ hspec hθsum
    (by linarith)
  rw [show (1 : ℝ) - ((1 + δ + δ ^ 2) ^ n - 1) = 2 - (1 + δ + δ ^ 2) ^ n by ring] at hmain
  exact hmain

end GeometricRecursion

end RiemannMasullo
