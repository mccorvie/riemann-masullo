module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_GeometricRecursion
public import RiemannMasullo.Ch09_HardySobolev.Sec3_TestSeries
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.ForMathlib.Analysis.Fourier.CompactSupportSeries

/-! # The geometric part of Theorem 10.4.3.5 on the line: a recursion over modulated tests

`Sec4b_GeometricRecursion` bounds the geometric part of `A(φ) ∘ Q` by the spectral parts of the
tests `φ` times powers of minus the logarithm of the norm. Bounds for the spectral parts of
that family are not available with common clusters: the cluster estimates of §10.3 see a test
through the size of its Mellin transform on fixed contours, and multiplying a test by a power
of the logarithm differentiates its Mellin transform.

This file runs the recursion over another family: the test times the characters
`exp (2 π i m log|·| / (4 δ))` of the norm, for the integers `m`. Such a modulation shifts the
Mellin transform along the imaginary axis, which costs a power of `1 + |m|` in the cluster
estimates and nothing else (`spectralStripConvolution_exists_commonClusters` of
`Sec3_ClusterBounds`). On the support of a test that lives where the logarithm of the norm is
at most `δ`, each power of that logarithm is a Fourier series in these characters with rapidly
decreasing coefficients (`exists_fourierSeries_pow`), and convolution turns the series of tests
into a norm convergent series of operators (`hasSum_hardySobolevTestAction` of
`Ch09_HardySobolev/Sec3_TestSeries`).

* `traceNorm_geometricPart_le_of_modulated_recursion` is the recursion, for operators on a
  Hilbert space indexed by the integers, with the polynomial weight `(1 + |m|) ^ p`.
* `exists_traceNorm_geometricProjection_stripTestAction_le_of_modulated` applies it: for a test
  supported close enough to the norm-one classes, the geometric part of `A(φ) ∘ Q` has trace
  norm at most the constant in the bounds `B (1 + |m|) ^ p` for the spectral parts of the
  modulated tests. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set UniformSpace
open scoped NNReal NumberField.AdeleRing TensorProduct Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

section ModulatedRecursion

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/- Copies of four private lemmas of `Sec4b_GeometricRecursion`: the trace norm is a norm. -/
private theorem traceNorm_nonneg'' (T : nuclearEndomorphisms W) : 0 ≤ traceNorm T := by
  let : Norm (nuclearEndomorphisms W) := ⟨traceNorm⟩
  exact (traceNorm_normedSpaceCore (H := W)).norm_nonneg T

private theorem traceNorm_add_le'' (S T : nuclearEndomorphisms W) :
    traceNorm (S + T) ≤ traceNorm S + traceNorm T := by
  let : Norm (nuclearEndomorphisms W) := ⟨traceNorm⟩
  exact (traceNorm_normedSpaceCore (H := W)).norm_triangle S T

private theorem traceNorm_smul'' (c : ℂ) (T : nuclearEndomorphisms W) :
    traceNorm (c • T) = ‖c‖ * traceNorm T := by
  let : Norm (nuclearEndomorphisms W) := ⟨traceNorm⟩
  exact (traceNorm_normedSpaceCore (H := W)).norm_smul c T

private theorem traceNorm_sum_le'' {ι : Type*} (s : Finset ι) (T : ι → nuclearEndomorphisms W) :
    traceNorm (∑ i ∈ s, T i) ≤ ∑ i ∈ s, traceNorm (T i) := by
  let : Norm (nuclearEndomorphisms W) := ⟨traceNorm⟩
  have hc := traceNorm_normedSpaceCore (H := W)
  have hzero : traceNorm (0 : nuclearEndomorphisms W) = 0 := (hc.norm_eq_zero_iff 0).mpr rfl
  exact s.le_sum_of_subadditive traceNorm hzero.le hc.toCore.norm_triangle T

private theorem one_add_abs_add_pow_le (m n : ℤ) (p : ℕ) :
    (1 + |((m + n : ℤ) : ℝ)|) ^ p ≤ (1 + |(m : ℝ)|) ^ p * (1 + |(n : ℝ)|) ^ p := by
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ p
  push_cast
  nlinarith [abs_add_le (m : ℝ) (n : ℝ), abs_nonneg (m : ℝ), abs_nonneg (n : ℝ),
    mul_nonneg (abs_nonneg (m : ℝ)) (abs_nonneg (n : ℝ))]

/-- A recursion for the trace norm of the part of an operator that an idempotent splitting
`G + P = 1` sends from the range of `P` into the range of `G`, over a family of operators
indexed by the integers. Let `A m`, for `m : ℤ`, be uniformly bounded operators with
`G (A m) P = -∑ i, c i • G (M i) (B i m) P`, with contractions `M i` and nonnegative `c i`, where
each `B i m` is the sum of the series `∑ n, a i n • A (m + n)`. Let `Q` be nuclear with
`P Q = Q`. If the trace norms of `P (A m) Q` are at most `Bd (1 + |m|) ^ p`, and
`∑ i, c i ∑ n, ‖a i n‖ (1 + |n|) ^ p ≤ θ < 1`, then the trace norm of `G (A 0) Q` is at most
`θ / (1 - θ) * Bd`.
The weight `(1 + |m|) ^ p` is submultiplicative, so the supremum of the trace norms of
`G (A m) Q` divided by the weight, which is finite because the `A m` are uniformly bounded,
is at most `θ` times itself plus `Bd`. -/
theorem traceNorm_geometricPart_le_of_modulated_recursion {ι : Type*} (s : Finset ι)
    (G P : W →L[ℂ] W) (hG : ‖G‖ ≤ 1) (hGP : G + P = 1)
    (A : ℤ → W →L[ℂ] W) (B : ι → ℤ → W →L[ℂ] W) (M : ι → W →L[ℂ] W)
    (hM : ∀ i ∈ s, ‖M i‖ ≤ 1) (c : ι → ℝ) (hc : ∀ i ∈ s, 0 ≤ c i) (a : ι → ℤ → ℂ)
    (hrec : ∀ m, G * (A m * P) = -∑ i ∈ s, (c i : ℂ) • (G * (M i * (B i m * P))))
    (hB : ∀ i ∈ s, ∀ m, HasSum (fun n : ℤ ↦ a i n • A (m + n)) (B i m))
    (Q : nuclearEndomorphisms W) (hPQ : P * Q.val = Q.val)
    (M₀ Bd θ : ℝ) (p : ℕ) (hA : ∀ m, ‖A m‖ ≤ M₀)
    (hspec : ∀ m, traceNorm ⟨(P * A m) * Q.val, mul_mem_nuclearEndomorphisms_left _ Q⟩ ≤
      Bd * (1 + |(m : ℝ)|) ^ p)
    (ha : ∀ i ∈ s, Summable (fun n : ℤ ↦ ‖a i n‖ * (1 + |(n : ℝ)|) ^ p))
    (hθ : ∑ i ∈ s, c i * ∑' n : ℤ, ‖a i n‖ * (1 + |(n : ℝ)|) ^ p ≤ θ) (hθ1 : θ < 1) :
    traceNorm ⟨(G * A 0) * Q.val, mul_mem_nuclearEndomorphisms_left _ Q⟩ ≤ θ / (1 - θ) * Bd := by
  let L (X : W →L[ℂ] W) (T : nuclearEndomorphisms W) : nuclearEndomorphisms W :=
    ⟨X * T.val, mul_mem_nuclearEndomorphisms_left X T⟩
  let w (m : ℤ) : ℝ := (1 + |(m : ℝ)|) ^ p
  have hw1 (m : ℤ) : 1 ≤ w m := one_le_pow₀ (by linarith [abs_nonneg (m : ℝ)])
  have hw0 (m : ℤ) : 0 < w m := zero_lt_one.trans_le (hw1 m)
  have hwmul (m n : ℤ) : w (m + n) ≤ w m * w n := one_add_abs_add_pow_le m n p
  let g (m : ℤ) : ℝ := traceNorm (L (G * A m) Q)
  let τ (m : ℤ) : ℝ := traceNorm (L (P * A m) Q)
  let tQ := traceNorm Q
  have htQ : 0 ≤ tQ := traceNorm_nonneg'' Q
  have hg0 (m : ℤ) : 0 ≤ g m := traceNorm_nonneg'' _
  have hM₀ : 0 ≤ M₀ := (norm_nonneg _).trans (hA 0)
  have hBd : 0 ≤ Bd := by
    have h := (traceNorm_nonneg'' _).trans (hspec 0)
    simpa using h
  let V (i : ι) : ℝ := ∑' n : ℤ, ‖a i n‖ * (1 + |(n : ℝ)|) ^ p
  have hV0 (i : ι) : 0 ≤ V i := tsum_nonneg fun n ↦ by positivity
  have hθ0 : 0 ≤ θ := (Finset.sum_nonneg fun i hi ↦ mul_nonneg (hc i hi) (hV0 i)).trans hθ
  -- The a priori bound, and the weighted supremum.
  have hprior (m : ℤ) : g m ≤ M₀ * tQ := by
    have h1 := traceNorm_mul_left_le (G * A m) Q
    have h2 : ‖G * A m‖ ≤ M₀ := (norm_mul_le G (A m)).trans
      ((mul_le_mul hG (hA m) (norm_nonneg _) zero_le_one).trans (one_mul _).le)
    exact h1.trans (mul_le_mul_of_nonneg_right h2 htQ)
  have hbdd : BddAbove (range fun m : ℤ ↦ g m / w m) := by
    refine ⟨M₀ * tQ, ?_⟩
    rintro _ ⟨m, rfl⟩
    exact (div_le_self (hg0 m) (hw1 m)).trans (hprior m)
  let γ : ℝ := ⨆ m : ℤ, g m / w m
  have hγ (m : ℤ) : g m ≤ γ * w m := by
    have h := le_ciSup hbdd m
    rwa [div_le_iff₀ (hw0 m)] at h
  have hγ0 : 0 ≤ γ := (div_nonneg (hg0 0) (hw0 0).le).trans (le_ciSup hbdd 0)
  have hτ (m : ℤ) : τ m ≤ Bd * w m := hspec m
  -- The series for the two parts of `B i m * Q`.
  have hpart (X : W →L[ℂ] W) (x : ℤ → ℝ) (C : ℝ) (hC : 0 ≤ C)
      (hx : ∀ m, traceNorm (L (X * A m) Q) ≤ C * w m) (i : ι) (hi : i ∈ s) (m : ℤ) :
      traceNorm (L (X * B i m) Q) ≤ C * w m * V i := by
    have hsum : HasSum (fun n : ℤ ↦ (a i n • L (X * A (m + n)) Q).val) ((X * B i m) * Q.val) := by
      have h1 := ((ContinuousLinearMap.mul ℂ (W →L[ℂ] W) X).hasSum (hB i hi m))
      have h2 := ((ContinuousLinearMap.mul ℂ (W →L[ℂ] W)).flip Q.val).hasSum h1
      refine h2.congr_fun fun n ↦ ?_
      change (a i n • L (X * A (m + n)) Q).val = (X * (a i n • A (m + n))) * Q.val
      simp only [L, Submodule.coe_smul, mul_smul_comm, smul_mul_assoc]
    obtain ⟨hn, hle⟩ := traceNorm_le_of_hasSum (fun n : ℤ ↦ a i n • L (X * A (m + n)) Q)
      ((X * B i m) * Q.val) hsum (fun n ↦ C * w m * (‖a i n‖ * (1 + |(n : ℝ)|) ^ p))
      ((ha i hi).mul_left _) (fun n ↦ by
        rw [traceNorm_smul'']
        calc ‖a i n‖ * traceNorm (L (X * A (m + n)) Q) ≤ ‖a i n‖ * (C * w (m + n)) :=
              mul_le_mul_of_nonneg_left (hx _) (norm_nonneg _)
          _ ≤ ‖a i n‖ * (C * (w m * w n)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hwmul m n) hC) (norm_nonneg _)
          _ = C * w m * (‖a i n‖ * (1 + |(n : ℝ)|) ^ p) := by ring)
    rw [tsum_mul_left] at hle
    exact hle
  -- The operator identity behind one step of the recursion.
  have hstep (m : ℤ) : L (G * A m) Q = -∑ i ∈ s, (c i : ℂ) •
      L (G * M i) (L (G * B i m) Q + L (P * B i m) Q) := by
    apply Subtype.ext
    have hsplit (i : ι) : B i m * Q.val = (G * B i m) * Q.val + (P * B i m) * Q.val := by
      rw [← add_mul, ← add_mul, hGP, one_mul]
    calc (G * A m) * Q.val = (G * (A m * P)) * Q.val := by
          rw [mul_assoc, mul_assoc, mul_assoc, hPQ]
      _ = -∑ i ∈ s, (c i : ℂ) • ((G * M i) * (B i m * Q.val)) := by
          rw [hrec m, neg_mul, Finset.sum_mul]
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
          rw [hsplit i]
  have hrecg (m : ℤ) : g m ≤ θ * (γ + Bd) * w m := by
    have hneg : traceNorm (-∑ i ∈ s, (c i : ℂ) •
        L (G * M i) (L (G * B i m) Q + L (P * B i m) Q)) =
        traceNorm (∑ i ∈ s, (c i : ℂ) •
          L (G * M i) (L (G * B i m) Q + L (P * B i m) Q)) := by
      rw [← neg_one_smul ℂ, traceNorm_smul'', norm_neg, norm_one, one_mul]
    change traceNorm (L (G * A m) Q) ≤ _
    rw [hstep m, hneg]
    calc traceNorm (∑ i ∈ s, (c i : ℂ) • L (G * M i) (L (G * B i m) Q + L (P * B i m) Q))
        ≤ ∑ i ∈ s, c i * ((γ + Bd) * w m * V i) := by
          refine (traceNorm_sum_le'' s _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
          rw [traceNorm_smul'', Complex.norm_real, Real.norm_of_nonneg (hc i hi)]
          refine mul_le_mul_of_nonneg_left ?_ (hc i hi)
          have h1 := traceNorm_mul_left_le (G * M i) (L (G * B i m) Q + L (P * B i m) Q)
          have h2 : ‖G * M i‖ ≤ 1 := (norm_mul_le G (M i)).trans
            ((mul_le_mul hG (hM i hi) (norm_nonneg _) zero_le_one).trans (one_mul 1).le)
          have h3 := traceNorm_add_le'' (L (G * B i m) Q) (L (P * B i m) Q)
          have h4 := hpart G g γ hγ0 hγ i hi m
          have h5 := hpart P τ Bd hBd hτ i hi m
          calc _ ≤ ‖G * M i‖ * traceNorm (L (G * B i m) Q + L (P * B i m) Q) := h1
            _ ≤ 1 * traceNorm (L (G * B i m) Q + L (P * B i m) Q) :=
                mul_le_mul_of_nonneg_right h2 (traceNorm_nonneg'' _)
            _ ≤ γ * w m * V i + Bd * w m * V i := by
                rw [one_mul]
                exact h3.trans (add_le_add h4 h5)
            _ = (γ + Bd) * w m * V i := by ring
      _ = (∑ i ∈ s, c i * V i) * ((γ + Bd) * w m) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ ↦ by ring
      _ ≤ θ * ((γ + Bd) * w m) :=
          mul_le_mul_of_nonneg_right hθ (mul_nonneg (add_nonneg hγ0 hBd) (hw0 m).le)
      _ = θ * (γ + Bd) * w m := by ring
  have hγle : γ ≤ θ * (γ + Bd) := ciSup_le fun m ↦ by
    rw [div_le_iff₀ (hw0 m)]
    exact hrecg m
  have hγfin : γ ≤ θ / (1 - θ) * Bd := by
    have h1 : 0 < 1 - θ := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ h1]
    linarith
  have h0 := hγ 0
  have hw00 : w 0 = 1 := by simp [w]
  rw [hw00, mul_one] at h0
  exact h0.trans hγfin

end ModulatedRecursion

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

section SmallSupport

open WeightedConvolution

/-- Paper: Theorem 10.4.3.5(2), p. 472, the geometric component, when the density of the
Sobolev space is the polynomial `(1 + t ^ 2) ^ n`, for a test supported close to the norm-one
classes. For every `n` and every exponent `p` there is `δ₀ > 0` with the following property.
Let `δ ≤ δ₀`, let the test `ψ 0` be supported where the logarithm of the norm is at most `δ` in
absolute value, and let `ψ m` be `ψ 0` times the character `exp (2 π i m log|·| / (4 δ))` of
the norm. Let `Q` be a nuclear operator with values in the orthogonal complement of the theta
subspace. If the spectral parts `P^spec ∘ A(ψ m) ∘ Q` have trace norms at most
`B (1 + |m|) ^ p`, then the geometric part `P^geom ∘ A(ψ 0) ∘ Q` has trace norm at most `B`.
The spectral parts are lifts of the quotient convolutions of §10.3, and a modulation of the
test shifts its Mellin transform along the imaginary axis, so bounds of this kind hold with
common clusters (`spectralStripConvolution_exists_commonClusters` of `Sec3_ClusterBounds`).
The proof is the recursion `traceNorm_geometricPart_le_of_modulated_recursion`, fed with the
exact formula `geometricProjection_stripTestAction_spectralProjection_eq_sum` for each `ψ m`.
In that formula the test is multiplied by positive powers of minus the logarithm of the norm;
on the support these powers are Fourier series in the characters above
(`exists_fourierSeries_pow`), with coefficients that are small when `δ` is small.
Reconstruction: The paper gives no estimate for the geometric component. -/
theorem exists_traceNorm_geometricProjection_stripTestAction_le_of_modulated (n p : ℕ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (a : ℝ),
      (∀ t, intervalSobolevDensity (-α) α s t = (1 + t ^ 2) ^ n) →
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ ψ : ℤ → BruhatCompactSupport C𝔽,
      (∀ (m : ℤ) (g : C𝔽), (ψ m).val g =
        Complex.exp (2 * Real.pi * Complex.I * m * (logNorm g / (4 * δ) : ℝ)) * (ψ 0).val g) →
      (∀ g, (ψ 0).val g ≠ 0 → |logNorm g| ≤ δ) →
      ∀ (B : ℝ) (Q : nuclearEndomorphisms (W(α, s))), Pspec(a, hα, hs) * Q.val = Q.val →
      (∀ m : ℤ, traceNorm ⟨((Pspec(a, hα, hs)).comp (A(hα, hs, ψ m))) * Q.val,
        mul_mem_nuclearEndomorphisms_left _ Q⟩ ≤ B * (1 + |(m : ℝ)|) ^ p) →
      traceNorm ⟨((Pgeom(a, hα, hs)).comp (A(hα, hs, ψ 0))) * Q.val,
        mul_mem_nuclearEndomorphisms_left _ Q⟩ ≤ B := by
  choose aF haF hsumF using fun e : ℕ ↦ exists_fourierSeries_pow e
  let s₀ : Finset (Σ _ : ℕ, ℕ) := (polyWeightIndex n).erase ⟨0, 0⟩
  let V (e : ℕ) : ℝ := ∑' k : ℤ, ‖aF e k‖ * (1 + |(k : ℝ)|) ^ p
  have hV0 (e : ℕ) : 0 ≤ V e := tsum_nonneg fun k ↦ by positivity
  let Vtot : ℝ := ∑ i ∈ s₀, (polyWeightCoeff n i : ℝ) * V (i.1 + i.2)
  have hVtot : 0 ≤ Vtot :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (Nat.cast_nonneg _) (hV0 _)
  refine ⟨min (1 / 4) (1 / (8 * (Vtot + 1))), lt_min (by norm_num) (by positivity), ?_⟩
  intro α s hα hs a hdens δ hδ hδ₀ ψ hψ hsupp B Q hPQ hspec
  have hδ4 : 4 * δ ≤ 1 := by
    have := hδ₀.trans (min_le_left _ _)
    linarith
  have hδV : 4 * δ * Vtot ≤ 1 / 2 := by
    have h1 := hδ₀.trans (min_le_right _ _)
    have h2 : 0 < 8 * (Vtot + 1) := by positivity
    rw [le_div_iff₀ h2] at h1
    nlinarith
  have he1 (i : Σ _ : ℕ, ℕ) (hi : i ∈ s₀) : 1 ≤ i.1 + i.2 := by
    have hne : i ≠ ⟨0, 0⟩ := (Finset.mem_erase.mp hi).1
    by_contra h
    have h1 : i.1 = 0 := by omega
    have h2 : i.2 = 0 := by omega
    exact hne (Sigma.ext h1 (heq_of_eq h2))
  choose T hTn hT using fun i : (Σ _ : ℕ, ℕ) ↦ exists_polyWeightMask_multiplier μ𝔽 m𝔽 (-α) α s i
  choose Φ hΦ using fun m : ℤ ↦ exists_bruhatCompactSupport_logPow m𝔽 (ψ m)
  obtain ⟨M₀, hM₀, hbound⟩ :=
    exists_hardySobolevTestAction_norm_le_of_dominated μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs (ψ 0)
  have hexp1 (k : ℤ) (g : C𝔽) :
      ‖Complex.exp (2 * Real.pi * Complex.I * k * (logNorm g / (4 * δ) : ℝ))‖ = 1 :=
    norm_cexp_two_pi_I_mul k _
  have hψnorm (m : ℤ) (g : C𝔽) : ‖(ψ m).val g‖ = ‖(ψ 0).val g‖ := by
    rw [hψ m g, norm_mul, hexp1, one_mul]
  have hψadd (m k : ℤ) (g : C𝔽) : (ψ (m + k)).val g =
      Complex.exp (2 * Real.pi * Complex.I * k * (logNorm g / (4 * δ) : ℝ)) * (ψ m).val g := by
    rw [hψ (m + k) g, hψ m g, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  let θ := Θ(a, hα, hs)
  let G := Pgeom(a, hα, hs)
  let P := Pspec(a, hα, hs)
  let Am (m : ℤ) : W(α, s) →L[ℂ] W(α, s) := A(hα, hs, ψ m)
  let Bm (i : Σ _ : ℕ, ℕ) (m : ℤ) : W(α, s) →L[ℂ] W(α, s) := A(hα, hs, Φ m (i.1 + i.2))
  let ac (i : Σ _ : ℕ, ℕ) (k : ℤ) : ℂ := ((-(4 * δ)) ^ (i.1 + i.2) : ℝ) * aF (i.1 + i.2) k
  have hacn (i : Σ _ : ℕ, ℕ) (k : ℤ) : ‖ac i k‖ = (4 * δ) ^ (i.1 + i.2) * ‖aF (i.1 + i.2) k‖ := by
    change ‖(((-(4 * δ)) ^ (i.1 + i.2) : ℝ) : ℂ) * aF (i.1 + i.2) k‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_neg,
      abs_of_pos (by positivity : (0 : ℝ) < 4 * δ)]
  have hG : ‖G‖ ≤ 1 := θ.starProjection_norm_le
  have hGP : G + P = 1 := by
    apply ContinuousLinearMap.ext
    intro u
    exact θ.starProjection_add_starProjection_orthogonal u
  have hrec (m : ℤ) : G * (Am m * P) = -∑ i ∈ s₀,
      (((polyWeightCoeff n i : ℝ)) : ℂ) • (G * (T i * (Bm i m * P))) := by
    have h := geometricProjection_stripTestAction_spectralProjection_eq_sum (F := F) hα hs a n
      hdens (ψ m) (Φ m) (hΦ m) T hT
    refine h.trans (congrArg Neg.neg (Finset.sum_congr rfl fun i _ ↦ ?_))
    rw [Complex.ofReal_natCast]
    rfl
  have hBm (i : Σ _ : ℕ, ℕ) (m : ℤ) : HasSum (fun k : ℤ ↦ ac i k • Am (m + k)) (Bm i m) := by
    refine hasSum_hardySobolevTestAction μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs (ψ 0)
      (Φ m (i.1 + i.2)) (fun k ↦ ψ (m + k)) (ac i) ?_ (fun k g ↦ (hψnorm (m + k) g).le)
      (fun g ↦ ?_)
    · have h := ((haF (i.1 + i.2) 0).mul_left ((4 * δ) ^ (i.1 + i.2)))
      refine h.congr fun k ↦ ?_
      rw [hacn]
      simp
    · by_cases hg : (ψ 0).val g = 0
      · have h0 (k : ℤ) : (ψ k).val g = 0 := by rw [hψ k g, hg, mul_zero]
        have h1 : (Φ m (i.1 + i.2)).val g = 0 := by rw [hΦ m (i.1 + i.2) g, h0 m, mul_zero]
        rw [h1]
        refine hasSum_zero.congr_fun fun k ↦ ?_
        rw [h0 (m + k), mul_zero]
      · have hy : |logNorm g / (4 * δ)| ≤ 1 / 4 := by
          rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * δ), div_le_iff₀ (by positivity)]
          linarith [hsupp g hg]
        have h1 := ((hsumF (i.1 + i.2) _ hy).mul_left
          (((-(4 * δ)) ^ (i.1 + i.2) : ℝ) : ℂ)).mul_right ((ψ m).val g)
        have h2 : (((-(4 * δ)) ^ (i.1 + i.2) : ℝ) : ℂ) *
            ((logNorm g / (4 * δ) : ℝ) : ℂ) ^ (i.1 + i.2) * (ψ m).val g =
            (Φ m (i.1 + i.2)).val g := by
          rw [hΦ m (i.1 + i.2) g]
          congr 1
          rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← mul_pow]
          congr 2
          change -(4 * δ) * (logNorm g / (4 * δ)) = -logNorm g
          have hδne : δ ≠ 0 := hδ.ne'
          field_simp
        rw [h2] at h1
        refine h1.congr_fun fun k ↦ ?_
        change ((((-(4 * δ)) ^ (i.1 + i.2) : ℝ) : ℂ) * aF (i.1 + i.2) k) * (ψ (m + k)).val g = _
        rw [hψadd m k g]
        ring
  have hAm (m : ℤ) : ‖Am m‖ ≤ M₀ := by
    have h := hbound (ψ m) 1 zero_le_one (fun g ↦ by rw [one_mul]; exact (hψnorm m g).le)
    simpa using h
  have hasum (i : Σ _ : ℕ, ℕ) : Summable fun k : ℤ ↦ ‖ac i k‖ * (1 + |(k : ℝ)|) ^ p := by
    refine ((haF (i.1 + i.2) p).mul_left ((4 * δ) ^ (i.1 + i.2))).congr fun k ↦ ?_
    rw [hacn, mul_assoc]
  have hθ : ∑ i ∈ s₀, (polyWeightCoeff n i : ℝ) *
      ∑' k : ℤ, ‖ac i k‖ * (1 + |(k : ℝ)|) ^ p ≤ 1 / 2 := by
    refine le_trans ?_ hδV
    change _ ≤ 4 * δ * ∑ i ∈ s₀, (polyWeightCoeff n i : ℝ) * V (i.1 + i.2)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have h1 : ∑' k : ℤ, ‖ac i k‖ * (1 + |(k : ℝ)|) ^ p =
        (4 * δ) ^ (i.1 + i.2) * V (i.1 + i.2) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun k ↦ ?_
      rw [hacn, mul_assoc]
    have h2 : (4 * δ) ^ (i.1 + i.2) ≤ 4 * δ :=
      pow_le_of_le_one (by positivity) hδ4 (by have := he1 i hi; omega)
    rw [h1]
    calc (polyWeightCoeff n i : ℝ) * ((4 * δ) ^ (i.1 + i.2) * V (i.1 + i.2))
        ≤ (polyWeightCoeff n i : ℝ) * (4 * δ * V (i.1 + i.2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (hV0 _)) (Nat.cast_nonneg _)
      _ = 4 * δ * ((polyWeightCoeff n i : ℝ) * V (i.1 + i.2)) := by ring
  have hmain := traceNorm_geometricPart_le_of_modulated_recursion s₀ G P hG hGP Am Bm T
    (fun i _ ↦ hTn i) (fun i ↦ (polyWeightCoeff n i : ℝ)) (fun i _ ↦ Nat.cast_nonneg _) ac hrec
    (fun i _ m ↦ hBm i m) Q hPQ M₀ B (1 / 2) p hAm hspec (fun i _ ↦ hasum i) hθ (by norm_num)
  have hhalf : (1 / 2 : ℝ) / (1 - 1 / 2) * B = B := by norm_num
  rw [hhalf] at hmain
  exact hmain

end SmallSupport

end RiemannMasullo
