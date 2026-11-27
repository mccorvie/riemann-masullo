module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import RiemannMasullo.ForMathlib.Analysis.Distribution.TestFunction.Schwartz
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Complete
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # First Mellin moments of tests with fixed support

On tests supported in `[1, 3]`, pointwise boundedness of weighted first Mellin moments
forces polynomial growth of the weights in the imaginary frequency. Banach–Steinhaus gives
finitely many ordinary derivative seminorms. Modulating a positive bump detects the first
moment at each frequency.

The modulation argument follows mlyle’s quotient-block proof in `research/I314LineGaps.lean`
(commit 094293aeeaf5b58f7b194e1e779aac4c330a6251). -/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions NNReal Topology

namespace RiemannMasullo.FirstMellinMoment

local notation "p" => ContDiffMapSupportedIn.seminorm ℂ ℝ ℂ ⊤

/-- Banach–Steinhaus on one fixed-support test space gives finitely many ordinary derivative
seminorms, uniformly over the entire indexing set. -/
theorem fixedSupport_uniform_bound {I : Type*} (K : Compacts ℝ) (T : I → 𝓓_{K}(ℝ, ℂ) →L[ℂ] ℂ)
    (h : ∀ f, BddAbove (range (fun i ↦ ‖T i f‖))) :
    ∃ J : Finset ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ i f, ‖T i f‖ ≤ (C : ℝ) * (J.sup (fun n ↦ p K n)) f := by
  classical
  let : CompleteSpace (SchwartzMap ℝ ℂ) := completeSpace_schwartzMap
  let e := isClosedEmbedding_supportedToSchwartzCLM K
  let : CompleteSpace 𝓓_{K}(ℝ, ℂ) := (completeSpace_iff_isComplete_range
    (AddMonoidHom.isUniformInducing_of_isInducing e.isInducing)).mpr e.isClosed_range.isComplete
  let : FirstCountableTopology 𝓓_{K}(ℝ, ℂ) :=
    (ContDiffMapSupportedIn.withSeminorms ℂ ℝ ℂ ⊤ K).firstCountableTopology
  let : (uniformity 𝓓_{K}(ℝ, ℂ)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero]
    infer_instance
  let P (i : I) := (normSeminorm ℂ ℂ).comp (T i).toLinearMap
  have hbd : BddAbove (range P) := Seminorm.bddAbove_range_iff.mpr h
  have hc : Continuous (⨆ i, P i : Seminorm ℂ 𝓓_{K}(ℝ, ℂ)) := by
    rw [Seminorm.coe_iSup_eq hbd]
    exact Seminorm.continuous_iSup P (fun i ↦ (T i).continuous.norm) hbd
  obtain ⟨J, C, hC, hbound⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℂ ℝ ℂ ⊤ K) _ hc
  exact ⟨J, C, hC, fun i f ↦ (le_ciSup hbd i f).trans (hbound f)⟩

private def phase (t x : ℝ) : ℂ := Complex.exp (((t : ℂ) * Complex.I) * x)

private theorem contDiff_phase (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (phase t) :=
  Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

private theorem norm_phase (t x : ℝ) : ‖phase t x‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]

private theorem iteratedDeriv_phase (t : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (phase t) x = ((t : ℂ) * Complex.I) ^ n * phase t x := by
  induction n generalizing x with
  | zero => simp
  | succ n h =>
    rw [iteratedDeriv_succ, funext h]
    let c := (t : ℂ) * Complex.I
    have h1 : HasDerivAt (phase t) (c * phase t x) x := by
      have hd := (((Complex.hasDerivAt_exp (c * (x : ℂ))).comp (x : ℂ)
        ((hasDerivAt_id (x : ℂ)).const_mul c)).comp_ofReal)
      change HasDerivAt (fun y : ℝ ↦ Complex.exp (c * (y : ℂ))) (c * Complex.exp (c * (x : ℂ))) x
      simpa [mul_comm] using hd
    change deriv (fun y ↦ c ^ n * phase t y) x = c ^ (n + 1) * phase t x
    rw [(h1.const_mul _).deriv, pow_succ]
    ring

private def modulate {K : Compacts ℝ} (f : 𝓓_{K}(ℝ, ℂ)) (t : ℝ) : 𝓓_{K}(ℝ, ℂ) :=
  .of_support_subset (f.contDiff.mul (contDiff_phase (-t))) (fun x hx ↦
    f.support_subset (fun h ↦ hx (show f x * phase (-t) x = 0 by rw [h, zero_mul])))

private theorem seminorm_modulate_le {K : Compacts ℝ} (f : 𝓓_{K}(ℝ, ℂ)) (n : ℕ) :
    ∃ C ≥ (0 : ℝ), ∀ t : ℝ, p K n (modulate f t) ≤ C * (1 + |t|) ^ n := by
  let B (i : ℕ) := (n.choose i : ℝ) * p K i f
  have hB (i) : 0 ≤ B i := mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)
  refine ⟨∑ i ∈ Finset.range (n + 1), B i, Finset.sum_nonneg (fun i _ ↦ hB i), fun t ↦ ?_⟩
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℂ (mul_nonneg
    (Finset.sum_nonneg fun i _ ↦ hB i) (pow_nonneg (by positivity) _)) n _).mpr
  intro x hx
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change ‖iteratedDeriv n ((f : ℝ → ℂ) * phase (-t)) x‖ ≤ _
  rw [iteratedDeriv_mul (f.contDiff.of_le (by simp)).contDiffAt
    ((contDiff_phase (-t)).of_le (by simp)).contDiffAt]
  refine (norm_sum_le ..).trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [iteratedDeriv_phase, norm_mul, norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_I, mul_one,
    norm_phase, mul_one, Complex.norm_real, norm_neg, Complex.norm_natCast, Real.norm_eq_abs t]
  have hf : ‖iteratedFDeriv ℝ i f x‖ ≤ p K i f :=
    ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hf
  have ht : |t| ^ (n - i) ≤ (1 + |t|) ^ n :=
    (pow_le_pow_left₀ (abs_nonneg _) (by linarith : |t| ≤ 1 + |t|) _).trans
      (pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg _)) (Nat.sub_le _ _))
  exact mul_le_mul (mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg _)) ht (by positivity) (hB i)

private def supportInterval : Compacts ℝ := ⟨Icc 1 3, isCompact_Icc⟩

private def bump : ContDiffBump (2 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

private theorem mem_supportInterval_of_bump_ne_zero {x : ℝ} (hx : bump x ≠ 0) : x ∈ supportInterval := by
  have hs : x ∈ tsupport bump := subset_tsupport _ hx
  rw [bump.tsupport_eq, Metric.mem_closedBall, Real.dist_eq] at hs
  have h : |x - 2| ≤ (1 / 2 : ℝ) := hs
  have ha := abs_le.mp h
  change 1 ≤ x ∧ x ≤ 3
  constructor <;> linarith [ha.1, ha.2]

private def bumpTest : 𝓓_{supportInterval}(ℝ, ℂ) :=
  .of_support_subset (Complex.ofRealCLM.contDiff.comp bump.contDiff) fun x hx ↦
    mem_supportInterval_of_bump_ne_zero fun h ↦ hx (by simpa using congrArg Complex.ofReal h)

private def momentKernel (b t x : ℝ) := ((x * Real.exp (b * x) : ℝ) : ℂ) * phase t x

private theorem continuous_momentKernel (b t : ℝ) : Continuous (momentKernel b t) :=
  (Complex.continuous_ofReal.comp (continuous_id.mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)))).mul (contDiff_phase t).continuous

private def firstMoment (ν : Measure ℝ) (b t : ℝ) : 𝓓_{supportInterval}(ℝ, ℂ) →L[ℂ] ℂ :=
  ContDiffMapSupportedIn.integralAgainstBilinCLM (ContinuousLinearMap.mul ℂ ℂ) ν (momentKernel b t)

private theorem firstMoment_apply (ν : Measure ℝ) [IsLocallyFiniteMeasure ν] (b t : ℝ)
    (f : 𝓓_{supportInterval}(ℝ, ℂ)) :
    firstMoment ν b t f = ∫ x, f x * momentKernel b t x ∂ν :=
  ContDiffMapSupportedIn.integralAgainstBilinCLM_eq_integral
    ((continuous_momentKernel b t).continuousOn.integrableOn_compact supportInterval.isCompact)

private theorem le_norm_firstMoment_modulate (ν : Measure ℝ) [IsLocallyFiniteMeasure ν]
    [ν.IsOpenPosMeasure] {A b : ℝ} (hb : |b| ≤ A) (t : ℝ) :
    Real.exp (-3 * A) * (∫ x, bump x ∂ν) ≤ ‖firstMoment ν b t (modulate bumpTest t)‖ := by
  let v (x : ℝ) := bump x * (x * Real.exp (b * x))
  have he : firstMoment ν b t (modulate bumpTest t) = ((∫ x, v x ∂ν : ℝ) : ℂ) := by
    rw [firstMoment_apply, ← integral_complex_ofReal]
    apply integral_congr_ae (.of_forall fun x ↦ ?_)
    change ((bump x : ℂ) * phase (-t) x) * (((x * Real.exp (b * x) : ℝ) : ℂ) * phase t x) = (v x : ℂ)
    have hp : phase (-t) x * phase t x = 1 := by simp [phase, ← Complex.exp_add]
    simp only [v, Complex.ofReal_mul]
    linear_combination (bump x : ℂ) * (x : ℂ) * (Real.exp (b * x) : ℂ) * hp
  have hlow (x : ℝ) : Real.exp (-3 * A) * bump x ≤ v x := by
    by_cases hx : bump x = 0
    · simp [hx, v]
    obtain ⟨hl, hr⟩ := mem_supportInterval_of_bump_ne_zero hx
    change 1 ≤ x at hl
    change x ≤ 3 at hr
    have hA := (abs_nonneg b).trans hb
    have hbx : -(3 * A) ≤ b * x := by
      have h := mul_le_mul_of_nonneg_right (abs_le.mp hb).1 (by linarith : 0 ≤ x)
      nlinarith [mul_le_mul_of_nonneg_right hr hA]
    have hxexp : Real.exp (-3 * A) ≤ x * Real.exp (b * x) :=
      (Real.exp_le_exp.mpr (by linarith)).trans (le_mul_of_one_le_left (Real.exp_pos _).le hl)
    exact ((mul_comm _ _).le.trans (mul_le_mul_of_nonneg_left hxexp bump.nonneg))
  have hv : Integrable v ν := (bump.continuous.mul (continuous_id.mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)))).integrable_of_hasCompactSupport
      bump.hasCompactSupport.mul_right
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
    (integral_nonneg fun x ↦ (mul_nonneg (Real.exp_pos _).le bump.nonneg).trans (hlow x)),
    ← integral_const_mul]
  exact integral_mono (bump.integrable.const_mul _) hv hlow

/-- Uniform pointwise control of first logarithmic Mellin moments on tests supported in
the fixed interval `[1, 3]` forces a single polynomial height bound for the weights. -/
theorem radialFirstMoment_polynomial {I : Type*} (ν : Measure ℝ)
    [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] {A : ℝ} (b t w : I → ℝ)
    (hb : ∀ i, |b i| ≤ A) (hw : ∀ i, 0 ≤ w i)
    (h : ∀ f : ContDiffMapSupportedIn ℝ ℂ ⊤ ⟨Icc 1 3, isCompact_Icc⟩,
      BddAbove (range fun i ↦ w i * ‖∫ x, f x * (((x * Real.exp (b i * x) : ℝ) : ℂ) *
        Complex.exp (((t i : ℂ) * Complex.I) * x)) ∂ν‖)) :
    ∃ C ≥ (0 : ℝ), ∃ N : ℕ, ∀ i, w i ≤ C * (1 + |t i|) ^ N := by
  classical
  let T (i : I) := (w i : ℂ) • firstMoment ν (b i) (t i)
  have he (i : I) (f : 𝓓_{supportInterval}(ℝ, ℂ)) : ‖T i f‖ = w i * ‖firstMoment ν (b i) (t i) f‖ := by
    simp only [T, smul_apply, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (hw i)]
  have hT (f : 𝓓_{supportInterval}(ℝ, ℂ)) : BddAbove (range fun i ↦ ‖T i f‖) := by
    simp_rw [he, firstMoment_apply]
    exact h f
  obtain ⟨J, D, _, hf⟩ := fixedSupport_uniform_bound supportInterval T hT
  choose B hB hbound using seminorm_modulate_le bumpTest
  let N := J.sup id
  let M := ∑ j ∈ J, B j
  have hM : 0 ≤ M := Finset.sum_nonneg fun j _ ↦ hB j
  have H (i : I) : (J.sup (fun n ↦ p supportInterval n)) (modulate bumpTest (t i)) ≤
      M * (1 + |t i|) ^ N := by
    apply Seminorm.finset_sup_apply_le (mul_nonneg hM (pow_nonneg (by positivity) N))
    intro j hj
    exact (hbound j (t i)).trans (mul_le_mul (Finset.single_le_sum (fun l _ ↦ hB l) hj)
      (pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg _)) (Finset.le_sup (f := id) hj))
      (pow_nonneg (by positivity) _) hM)
  let c := Real.exp (-3 * A) * ∫ x, bump x ∂ν
  have hc : 0 < c := mul_pos (Real.exp_pos _) bump.integral_pos
  refine ⟨(D : ℝ) * M / c, by positivity, N, fun i ↦ ?_⟩
  have h₁ := mul_le_mul_of_nonneg_left (le_norm_firstMoment_modulate ν (hb i) (t i)) (hw i)
  rw [← he] at h₁
  have h₂ := (hf i (modulate bumpTest (t i))).trans (mul_le_mul_of_nonneg_left (H i) D.coe_nonneg)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  exact (h₁.trans h₂).trans_eq (by ring)

end RiemannMasullo.FirstMellinMoment
