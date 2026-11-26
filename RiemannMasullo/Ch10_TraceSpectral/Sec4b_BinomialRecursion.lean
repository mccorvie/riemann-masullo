module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_ModulatedRecursion
public import RiemannMasullo.Ch09_HardySobolev.Sec3_AdjointBinomial
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.ForMathlib.Analysis.Fourier.CompactSupportSeries

/-! # The geometric part of Theorem 10.4.3.5 on the line at every order

`Sec4b_ModulatedRecursion` bounds the geometric part of `A(φ) ∘ Q` for a test supported close to
the norm-one classes when the density of the Sobolev space is the polynomial `(1 + t ^ 2) ^ n`,
that is on the line at the even orders `s = 2 n`. On the line the density is
`(1 + t ^ 2) ^ (s / 2)` for every order `s`.

This file treats the density `(1 + t ^ 2) ^ σ` for every real `σ`. The exact finite formula for
the commutator `P^geom ∘ A(φ) ∘ P^spec` becomes a norm convergent series with the coefficients
of a binomial series
(`hasSum_geometricProjection_stripTestAction_spectralProjection_binomWeight`, from
`hasSum_hardySobolevTestAction_adjoint_binomWeight` of
`Ch09_HardySobolev/Sec3_AdjointBinomial`). The recursion over modulated tests then runs with
infinitely many terms (`traceNorm_geometricPart_le_of_iterated_recursion`): each further power
of the logarithm of the norm costs one more factor, small when the support is small, so only the
Fourier series of the first power is needed
(`exists_traceNorm_geometricProjection_stripTestAction_le_of_modulated_rpow`). -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set UniformSpace
open scoped NNReal NumberField.AdeleRing TensorProduct Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

section InvariantSubspace

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- If an operator preserves a closed subspace `K`, its adjoint preserves the orthogonal
complement, so the part of the adjoint from the complement into `K` vanishes. This is the first
step of `starProjection_comp_comp_orthogonal_eq_neg_sum` of `Sec4b_GeometricRecursion`. -/
theorem starProjection_mul_adjoint_mul_orthogonal_eq_zero (K : Submodule ℂ W)
    [K.HasOrthogonalProjection] (A' : W →L[ℂ] W) (hA' : ∀ w ∈ K, A' w ∈ K) :
    K.starProjection * (A'.adjoint * Kᗮ.starProjection) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hv : Kᗮ.starProjection u ∈ Kᗮ := Kᗮ.starProjection_apply_mem u
  have hmem : A'.adjoint (Kᗮ.starProjection u) ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact (Submodule.mem_orthogonal _ _).mp hv _ (hA' w hw)
  exact (Submodule.starProjection_apply_eq_zero_iff K).mpr hmem

end InvariantSubspace

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

section CommutatorSeries

open WeightedConvolution

variable {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)

set_option maxHeartbeats 800000 in
/-- Paper: Theorem 10.4.3.5(2)–(3), pp. 472–473, the geometric component, when the density of
the Sobolev space is `(1 + t ^ 2) ^ σ` for a real `σ` and the test is supported where the
logarithm of the norm is at most `δ`, with `δ + δ ^ 2 < 1`. The commutator
`P^geom ∘ A(φ) ∘ P^spec` is minus the sum of a norm convergent series: over the pairs
`(k, l) ≠ (0, 0)` with `l ≤ k`, the coefficient of the binomial series times
`P^geom ∘ T ∘ A(φ_{k+l}) ∘ P^spec`, where `φ_e` is the test `φ` times the `e`-th power of minus
the logarithm of the norm and `T` is multiplication by a function of that logarithm bounded by
one. For a natural number `σ` this is the finite sum of
`geometricProjection_stripTestAction_spectralProjection_eq_sum`.
Reconstruction: The paper gives no formula or estimate for the geometric component. -/
theorem hasSum_geometricProjection_stripTestAction_spectralProjection_binomWeight (a σ : ℝ)
    (hdens : ∀ t, intervalSobolevDensity (-α) α s t = (1 + t ^ 2) ^ σ)
    (Φ : ℕ → BruhatCompactSupport C𝔽)
    (hΦ : ∀ e g, (Φ e).val g = (((-logNorm g) ^ e : ℝ) : ℂ) * (Φ 0).val g)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ + δ ^ 2 < 1)
    (hsupp : ∀ g, (Φ 0).val g ≠ 0 → |logNorm g| ≤ δ)
    (T : (Σ _ : ℕ, ℕ) → (W(α, s) →L[ℂ] W(α, s))) (hTn : ∀ i, ‖T i‖ ≤ 1)
    (hT : ∀ i u, (T i u : C𝔽 → ℂ) =ᵐ[intervalSobolevMeasure μ𝔽 logNorm (-α) α s]
      fun x ↦ ((polyWeightMask i (logNorm x) : ℝ) : ℂ) * u x) :
    HasSum (fun i : Σ k : ℕ, Fin (k + 1) ↦
        (((if i.1 = 0 then 0 else binomWeightCoeff σ i : ℝ)) : ℂ) •
          (Pgeom(a, hα, hs)).comp ((T ⟨i.1, i.2⟩).comp
            ((A(hα, hs, Φ (i.1 + i.2))).comp (Pspec(a, hα, hs)))))
      (-((Pgeom(a, hα, hs)).comp ((A(hα, hs, Φ 0)).comp (Pspec(a, hα, hs))))) := by
  classical
  obtain ⟨φ', hφ'⟩ := exists_bruhatCompactSupport_conjInv (Φ 0)
  let G : W(α, s) →L[ℂ] W(α, s) := Pgeom(a, hα, hs)
  let P : W(α, s) →L[ℂ] W(α, s) := Pspec(a, hα, hs)
  let B (e : ℕ) : W(α, s) →L[ℂ] W(α, s) := A(hα, hs, Φ e)
  let A' : W(α, s) →L[ℂ] W(α, s) := A(hα, hs, φ')
  let Fn (i : Σ k : ℕ, Fin (k + 1)) : W(α, s) →L[ℂ] W(α, s) :=
    ((binomWeightCoeff σ i : ℝ) : ℂ) • (T ⟨i.1, i.2⟩).comp (B (i.1 + i.2))
  have hadj : HasSum Fn A'.adjoint :=
    hasSum_hardySobolevTestAction_adjoint_binomWeight μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs σ hdens
      (Φ 0) φ' hφ' Φ hΦ δ hδ0 hδ hsupp T hTn hT
  let i₀ : Σ k : ℕ, Fin (k + 1) := ⟨0, 0⟩
  -- The term of the pair `(0, 0)` is convolution by the test.
  have hT0 : T ⟨0, 0⟩ = ContinuousLinearMap.id ℂ (W(α, s)) := by
    apply ContinuousLinearMap.ext
    intro u
    apply Lp.ext
    refine (hT ⟨0, 0⟩ u).trans (.of_forall fun x ↦ ?_)
    simp [polyWeightMask]
  have hF0 : Fn i₀ = B 0 := by
    change ((binomWeightCoeff σ ⟨0, 0⟩ : ℝ) : ℂ) • (T ⟨0, 0⟩).comp (B (0 + 0)) = B 0
    rw [hT0]
    simp [binomWeightCoeff]
  have hupd := hadj.update i₀ 0
  rw [hF0] at hupd
  have hzero : G * (A'.adjoint * P) = 0 :=
    starProjection_mul_adjoint_mul_orthogonal_eq_zero (Θ(a, hα, hs)) A'
      (fun w hw ↦ (Submodule.Quotient.mk_eq_zero _).mp
        (hardySobolevTestAction_preserves_globalTheta (F := F) a (hStrip(hα)) hs φ' hw))
  have h1 := ((ContinuousLinearMap.mul ℂ (W(α, s) →L[ℂ] W(α, s))).flip P).hasSum hupd
  have h2 := (ContinuousLinearMap.mul ℂ (W(α, s) →L[ℂ] W(α, s)) G).hasSum h1
  have hval : G * ((0 - B 0 + A'.adjoint) * P) = -(G * (B 0 * P)) := by
    rw [zero_sub, add_mul, mul_add, hzero, add_zero, neg_mul, mul_neg]
  have h3 : HasSum (fun i ↦ G * (Function.update Fn i₀ 0 i * P)) (-(G * (B 0 * P))) :=
    hval ▸ h2
  refine h3.congr_fun fun i ↦ ?_
  change ((((if i.1 = 0 then 0 else binomWeightCoeff σ i : ℝ)) : ℂ) •
    (G * (T ⟨i.1, i.2⟩ * (B (i.1 + i.2) * P)))) = G * (Function.update Fn i₀ 0 i * P)
  by_cases hi : i.1 = 0
  · have hi0 : i = i₀ := by
      obtain ⟨k, l⟩ := i
      change k = 0 at hi
      subst hi
      exact congrArg (Sigma.mk 0) (Fin.fin_one_eq_zero l)
    rw [hi0, Function.update_self]
    simp [i₀]
  · have hne : i ≠ i₀ := fun h ↦ hi (by rw [h])
    rw [Function.update_of_ne hne, ite_eq_right hi]
    change _ = G * ((((binomWeightCoeff σ i : ℝ) : ℂ) • (T ⟨i.1, i.2⟩).comp (B (i.1 + i.2))) * P)
    rw [smul_mul_assoc, mul_smul_comm]
    rfl

end CommutatorSeries

section SmallSupportRpow

open WeightedConvolution

set_option maxHeartbeats 1600000 in
/-- Paper: Theorem 10.4.3.5(2), p. 472, the geometric component, when the density of the
Sobolev space is `(1 + t ^ 2) ^ σ` for a real `σ`, for a test supported close to the norm-one
classes. For every `σ` and every exponent `p` there is `δ₀ > 0` with the following property.
Let `δ ≤ δ₀`, let the test `ψ 0` be supported where the logarithm of the norm is at most `δ` in
absolute value, and let `ψ m` be `ψ 0` times the character `exp (2 π i m log|·| / (4 δ))` of
the norm. Let `Q` be a nuclear operator with values in the orthogonal complement of the theta
subspace. If the spectral parts `P^spec ∘ A(ψ m) ∘ Q` have trace norms at most
`B (1 + |m|) ^ p`, then the geometric part `P^geom ∘ A(ψ 0) ∘ Q` has trace norm at most `B`.
This is `exists_traceNorm_geometricProjection_stripTestAction_le_of_modulated` of
`Sec4b_ModulatedRecursion` for every real exponent in place of a natural number. The proof is
the recursion `traceNorm_geometricPart_le_of_iterated_recursion`, fed with the series
`hasSum_geometricProjection_stripTestAction_spectralProjection_binomWeight` for each `ψ m`.
Multiplying a test by minus the logarithm of the norm is, on the support, a Fourier series in
the characters above (`exists_fourierSeries_pow`), so each power of the logarithm costs one
factor `4 δ` times a constant.
Reconstruction: The paper gives no estimate for the geometric component. -/
theorem exists_traceNorm_geometricProjection_stripTestAction_le_of_modulated_rpow (σ : ℝ)
    (p : ℕ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (a : ℝ),
      (∀ t, intervalSobolevDensity (-α) α s t = (1 + t ^ 2) ^ σ) →
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ ψ : ℤ → BruhatCompactSupport C𝔽,
      (∀ (m : ℤ) (g : C𝔽), (ψ m).val g =
        Complex.exp (2 * Real.pi * Complex.I * m * (logNorm g / (4 * δ) : ℝ)) * (ψ 0).val g) →
      (∀ g, (ψ 0).val g ≠ 0 → |logNorm g| ≤ δ) →
      ∀ (B : ℝ) (Q : nuclearEndomorphisms (W(α, s))), Pspec(a, hα, hs) * Q.val = Q.val →
      (∀ m : ℤ, traceNorm ⟨((Pspec(a, hα, hs)).comp (A(hα, hs, ψ m))) * Q.val,
        mul_mem_nuclearEndomorphisms_left _ Q⟩ ≤ B * (1 + |(m : ℝ)|) ^ p) →
      traceNorm ⟨((Pgeom(a, hα, hs)).comp (A(hα, hs, ψ 0))) * Q.val,
        mul_mem_nuclearEndomorphisms_left _ Q⟩ ≤ B := by
  obtain ⟨a1, ha1, hsum1⟩ := exists_fourierSeries_pow 1
  let V : ℝ := ∑' k : ℤ, ‖a1 k‖ * (1 + |(k : ℝ)|) ^ p
  have hV0 : 0 ≤ V := tsum_nonneg fun k ↦ by positivity
  let Cσ : ℝ := ∑' k : ℕ, |Ring.choose σ (k + 1)| * (1 / 2 : ℝ) ^ k
  have hCσ0 : 0 ≤ Cσ := tsum_nonneg fun k ↦ by positivity
  have hD : 0 < 16 * (V + 1) * (Cσ + 1) := by positivity
  refine ⟨1 / (16 * (V + 1) * (Cσ + 1)), by positivity, ?_⟩
  intro α s hα hs a hdens δ hδ hδ₀ ψ hψ hsupp B Q hPQ hspec
  -- The support is small enough.
  have hδD : δ * (16 * (V + 1) * (Cσ + 1)) ≤ 1 := by
    have h := hδ₀
    rwa [le_div_iff₀ hD] at h
  have hVC : 0 ≤ V * Cσ := mul_nonneg hV0 hCσ0
  have hδ16 : δ ≤ 1 / 16 := by
    nlinarith [mul_nonneg hδ.le hVC, mul_nonneg hδ.le hV0, mul_nonneg hδ.le hCσ0]
  have hδ1 : δ + δ ^ 2 < 1 := by nlinarith
  let x : ℝ := 4 * δ * V
  have hx0 : 0 ≤ x := by positivity
  have hxC : x * (Cσ + 1) ≤ 1 / 4 := by
    change 4 * δ * V * (Cσ + 1) ≤ 1 / 4
    nlinarith [mul_nonneg hδ.le hVC, mul_nonneg hδ.le hV0, mul_nonneg hδ.le hCσ0]
  have hx4 : x ≤ 1 / 4 := by nlinarith [mul_nonneg hx0 hCσ0]
  have hx2 : x ^ 2 ≤ x := by nlinarith
  have hxx : x + x ^ 2 ≤ 1 / 2 := by linarith
  have hθ' : (x + x ^ 2) * Cσ ≤ 1 / 2 := by
    have h1 : (x + x ^ 2) * Cσ ≤ 2 * x * Cσ := mul_le_mul_of_nonneg_right (by linarith) hCσ0
    nlinarith [mul_nonneg hx0 hCσ0]
  have hδC : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
  choose T hTn hT using fun i : (Σ _ : ℕ, ℕ) ↦ exists_polyWeightMask_multiplier μ𝔽 m𝔽 (-α) α s i
  choose Φ hΦ₀ using fun m : ℤ ↦ exists_bruhatCompactSupport_logPow m𝔽 (ψ m)
  have hΦ (m : ℤ) (e : ℕ) (g : C𝔽) :
      (Φ m e).val g = (((-logNorm g) ^ e : ℝ) : ℂ) * (ψ m).val g := hΦ₀ m e g
  have hΦ0 (m : ℤ) : Φ m 0 = ψ m := Subtype.ext (funext fun g ↦ by
    rw [hΦ m 0 g]
    simp)
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
  let G : W(α, s) →L[ℂ] W(α, s) := Pgeom(a, hα, hs)
  let P : W(α, s) →L[ℂ] W(α, s) := Pspec(a, hα, hs)
  let Akm (k : ℕ) (m : ℤ) : W(α, s) →L[ℂ] W(α, s) := A(hα, hs, Φ m k)
  let ac (n : ℤ) : ℂ := ((-(4 * δ) : ℝ) : ℂ) * a1 n
  have hacn (n : ℤ) : ‖ac n‖ = 4 * δ * ‖a1 n‖ := by
    change ‖((-(4 * δ) : ℝ) : ℂ) * a1 n‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by positivity : (0 : ℝ) < 4 * δ)]
  have hG : ‖G‖ ≤ 1 := (Θ(a, hα, hs)).starProjection_norm_le
  have hGP : G + P = 1 := by
    apply ContinuousLinearMap.ext
    intro u
    exact (Θ(a, hα, hs)).starProjection_add_starProjection_orthogonal u
  have hrec (m : ℤ) : HasSum (fun i : Σ k : ℕ, Fin (k + 1) ↦
      (((if i.1 = 0 then 0 else binomWeightCoeff σ i : ℝ)) : ℂ) •
        (G * (T ⟨i.1, i.2⟩ * (Akm (i.1 + i.2) m * P)))) (-(G * (Akm 0 m * P))) :=
    hasSum_geometricProjection_stripTestAction_spectralProjection_binomWeight (F := F) hα hs a σ
      hdens (Φ m)
      (fun e g ↦ (hΦ m e g).trans (congrArg
        (fun z : BruhatCompactSupport C𝔽 ↦ (((-logNorm g) ^ e : ℝ) : ℂ) * z.val g) (hΦ0 m).symm))
      δ hδ.le hδ1
      (fun g hg ↦ hsupp g fun h0 ↦ hg (by rw [hΦ0 m, hψ m g, h0, mul_zero])) T hTn hT
  have hstep (k : ℕ) (m : ℤ) : HasSum (fun n : ℤ ↦ ac n • Akm k (m + n)) (Akm (k + 1) m) := by
    refine hasSum_hardySobolevTestAction μ𝔽 m𝔽 (-α) α s (hStrip(hα)) hs (Φ m k)
      (Φ m (k + 1)) (fun n ↦ Φ (m + n) k) ac ?_ (fun n g ↦ ?_) (fun g ↦ ?_)
    · refine ((ha1 0).mul_left (4 * δ)).congr fun n ↦ ?_
      rw [hacn]
      simp
    · rw [hΦ (m + n) k g, hΦ m k g, norm_mul, norm_mul, hψnorm (m + n) g, hψnorm m g]
    · by_cases hg : (ψ 0).val g = 0
      · have h0 (j : ℤ) : (ψ j).val g = 0 := by rw [hψ j g, hg, mul_zero]
        have h1 : (Φ m (k + 1)).val g = 0 := by rw [hΦ m (k + 1) g, h0 m, mul_zero]
        rw [h1]
        refine hasSum_zero.congr_fun fun n ↦ ?_
        rw [hΦ (m + n) k g, h0 (m + n), mul_zero, mul_zero]
      · have hy : |logNorm g / (4 * δ)| ≤ 1 / 4 := by
          rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * δ), div_le_iff₀ (by positivity)]
          linarith [hsupp g hg]
        have h1 := (hsum1 _ hy).mul_left (((-(4 * δ) : ℝ) : ℂ) * (Φ m k).val g)
        have h2 : ((-(4 * δ) : ℝ) : ℂ) * (Φ m k).val g *
            ((logNorm g / (4 * δ) : ℝ) : ℂ) ^ 1 = (Φ m (k + 1)).val g := by
          rw [hΦ m (k + 1) g, hΦ m k g, pow_one, pow_succ]
          push_cast
          field_simp
        rw [h2] at h1
        refine h1.congr_fun fun n ↦ ?_
        change ((-(4 * δ) : ℝ) : ℂ) * a1 n * (Φ (m + n) k).val g = _
        rw [hΦ (m + n) k g, hΦ m k g, hψadd m n g]
        ring
  have hA (m : ℤ) : ‖Akm 0 m‖ ≤ M₀ := by
    have h := hbound (Φ m 0) 1 zero_le_one (fun g ↦ by
      rw [one_mul, hΦ0 m]
      exact (hψnorm m g).le)
    simpa using h
  have hspec' (m : ℤ) : traceNorm ⟨(P * Akm 0 m) * Q.val,
      mul_mem_nuclearEndomorphisms_left _ Q⟩ ≤ B * (1 + |(m : ℝ)|) ^ p := by
    have h := hspec m
    rw [← hΦ0 m] at h
    exact h
  have ha : Summable fun n : ℤ ↦ ‖ac n‖ * (1 + |(n : ℝ)|) ^ p := by
    refine ((ha1 p).mul_left (4 * δ)).congr fun n ↦ ?_
    rw [hacn]
    ring
  have hv : ∑' n : ℤ, ‖ac n‖ * (1 + |(n : ℝ)|) ^ p = x := by
    change _ = 4 * δ * ∑' k : ℤ, ‖a1 k‖ * (1 + |(k : ℝ)|) ^ p
    rw [← tsum_mul_left]
    exact tsum_congr fun n ↦ by rw [hacn]; ring
  obtain ⟨htail1, htail2⟩ := tsum_abs_binomWeightCoeff_tail_le σ x hx0 hxx
  have hθs : Summable fun i : Σ k : ℕ, Fin (k + 1) ↦
      ‖(((if i.1 = 0 then 0 else binomWeightCoeff σ i : ℝ)) : ℂ)‖ *
        (∑' n : ℤ, ‖ac n‖ * (1 + |(n : ℝ)|) ^ p) ^ (i.1 + i.2) := by
    rw [hv]
    refine htail1.congr fun i ↦ ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hθ : ∑' i : Σ k : ℕ, Fin (k + 1),
      ‖(((if i.1 = 0 then 0 else binomWeightCoeff σ i : ℝ)) : ℂ)‖ *
        (∑' n : ℤ, ‖ac n‖ * (1 + |(n : ℝ)|) ^ p) ^ (i.1 + i.2) ≤ 1 / 2 := by
    rw [hv]
    refine le_trans (le_of_eq (tsum_congr fun i ↦ ?_)) (htail2.trans hθ')
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hmain := traceNorm_geometricPart_le_of_iterated_recursion G P hG hGP Akm
    (fun i : Σ k : ℕ, Fin (k + 1) ↦ T ⟨i.1, i.2⟩) (fun i ↦ hTn _)
    (fun i ↦ (((if i.1 = 0 then 0 else binomWeightCoeff σ i : ℝ)) : ℂ)) (fun i ↦ i.1 + i.2) ac
    hrec hstep Q hPQ M₀ B (1 / 2) p hA hspec' ha hθs hθ (by norm_num)
  have hhalf : (1 / 2 : ℝ) / (1 - 1 / 2) * B = B := by norm_num
  rw [hhalf] at hmain
  have hfin : traceNorm ⟨((Pgeom(a, hα, hs)).comp (A(hα, hs, Φ 0 0))) * Q.val,
      mul_mem_nuclearEndomorphisms_left _ Q⟩ ≤ B := hmain
  rwa [hΦ0 0] at hfin

end SmallSupportRpow

end RiemannMasullo
