module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxFrequencyQuotients
public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxCentralCompact
public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxFiniteTrace
public import RiemannMasullo.ForMathlib.Analysis.Fourier.PrimeMeshCluster

/-! # Logarithmic trace-norm growth for every nonzero positive-time test

In the actual rational unweighted logarithmic theta model associated with
(11.3.1.3)–(11.3.1.4), pp. 494–496, every nonzero positive-time compact test
has singleton-prime trace norm at least c log p for all sufficiently large
primes, uniformly in the positive Fourier box. The scalar trace is then exactly
zero. Every Fourier value also bounds the original-stage action's distance
from compact operators, so every nonzero test acts noncompactly there.

These obstructions concern this unweighted model; they do not address the
paper's positive-width or higher-Sobolev constructions.
-/

public noncomputable section
open Set Function
namespace RiemannMasullo.RationalPacket

open MeasureTheory
open scoped FourierTransform SchwartzMap Topology

private theorem norm_sum_ge_card_mul_of_near {m : ℕ} (z : Fin m → ℂ) (c : ℂ)
    (ε : ℝ) (hz : ∀ i, ‖z i - c‖ ≤ ε) :
    (m : ℝ) * (‖c‖ - ε) ≤ ‖∑ i, z i‖ := by
  have he : ∑ i : Fin m, (z i - c) = (∑ i, z i) - (m : ℂ) * c := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hb : ‖(∑ i, z i) - (m : ℂ) * c‖ ≤ (m : ℝ) * ε := by
    rw [← he]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun i _ ↦ hz i)).trans_eq (by simp))
  have ht := norm_sub_le_norm_sub_add_norm_sub ((m : ℂ) * c) (∑ i, z i) 0
  rw [sub_zero, sub_zero, norm_sub_rev ((m : ℂ) * c), norm_mul, Complex.norm_natCast] at ht
  nlinarith

private theorem frequency_quotient_trace_bound {X : ℝ} (hX : 0 < X)
    (p : ℕ) (hp : p.Prime) (m : ℕ) (n : Fin m → ℤ) (hn : Injective n)
    (f : PositiveTimeTest) (A F : LogL2 →L[ℂ] LogL2) (hF : IsNuclearOperator F)
    (hAL : ∀ x, fixedBoxFrequencyRows X p m n (A x) =
      fixedBoxFrequencyMatrix p m n f (fixedBoxFrequencyRows X p m n x)) :
    ‖∑ i : Fin m, (𝓕 (positiveTestToSchwartz f)) ((n i : ℝ) / Real.log p)‖ ≤
      traceNorm ⟨F,hF⟩ + (m : ℝ) * ‖A-F‖ := by
  have hb := finite_quotient_trace_le_nuclear_approximation m (fixedBoxFrequencyRows X p m n)
    (fixedBoxFrequencyRows_surjective hX p hp m n hn) A F hF
    (fixedBoxFrequencyMatrix p m n f) hAL
  simpa only [fixedBoxFrequencyMatrix_apply, Pi.single_eq_same, mul_one] using hb

/-- Finite sets of actual Fourier samples give lower bounds for the trace norm
of the singleton-prime theta action, uniformly in its total Fourier box. -/
theorem fixedBoxFiniteTestAction_singleton_traceNorm_ge_samples {X : ℝ} (hX : 0 < X)
    (p : ℕ) (hp : p.Prime) (hS1 : ∀ q ∈ ({p} : Finset ℕ), 1 ≤ q)
    (hS : ∀ q ∈ ({p} : Finset ℕ), q.Prime)
    (m : ℕ) (n : Fin m → ℤ) (hn : Injective n) (f : PositiveTimeTest) :
    ‖∑ i : Fin m, (𝓕 (positiveTestToSchwartz f)) ((n i : ℝ) / Real.log p)‖ ≤
      traceNorm ⟨fixedBoxFiniteTestAction (X := X) {p} hS1 f,
        fixedBoxFiniteTestAction_nuclear hX {p} hS1 hS f⟩ := by
  have hb := frequency_quotient_trace_bound hX p hp m n hn f
    (fixedBoxFiniteTestAction (X := X) {p} hS1 f) _
    (fixedBoxFiniteTestAction_nuclear hX {p} hS1 hS f)
    (fixedBoxFrequencyRows_singleton_intertwines hX p hp hS1 m n f)
  simpa only [sub_self, norm_zero, mul_zero, add_zero] using hb

/-- Every Fourier value bounds the distance of the original theta action from
compact operators, including for tests with zero integral. -/
theorem fixedBoxOriginalTestAction_fourier_norm_sub_compact_ge {X : ℝ} (hX : 0 < X)
    (f : PositiveTimeTest) (ξ : ℝ) (K : LogL2 →L[ℂ] LogL2) (hK : IsCompactOperator K) :
    ‖(𝓕 (positiveTestToSchwartz f)) ξ‖ ≤
      ‖(closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection.comp
        ((fixedBoxAmbientTestAction f).comp
          (closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection) - K‖ := by
  let A := (closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection.comp
    ((fixedBoxAmbientTestAction f).comp (closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection)
  let g := 𝓕 (positiveTestToSchwartz f)
  by_contra hb
  have hgap : 0 < ‖g ξ‖ - ‖A-K‖ := by change ¬ _ ≤ ‖A-K‖ at hb; linarith
  let ε := (‖g ξ‖ - ‖A-K‖) / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨F,hF,hKF⟩ := exists_nuclear_opNorm_approximation K hK ε hε
  have hAF : ‖A-F‖ ≤ ‖A-K‖ + ε :=
    (norm_sub_le_norm_sub_add_norm_sub A K F).trans (add_le_add le_rfl hKF)
  obtain ⟨m,hm⟩ := exists_nat_gt (traceNorm ⟨F,hF⟩ / (2*ε))
  obtain ⟨p,hp,_,n,hn,hnear⟩ := exists_prime_mesh_cluster g g.continuous ξ ε hε m 0
  have hlo := norm_sum_ge_card_mul_of_near
    (fun i ↦ g ((n i : ℝ) / Real.log p)) (g ξ) ε (fun i ↦ (hnear i).le)
  have hup := frequency_quotient_trace_bound hX p hp m n hn f A F hF
    (fixedBoxFrequencyRows_original_intertwines hX p hp m n f)
  have hmul := (div_lt_iff₀ (mul_pos (by norm_num) hε)).mp hm
  dsimp only [g] at hlo
  have hεeq : 4*ε = ‖g ξ‖ - ‖A-K‖ := by dsimp [ε]; ring
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

private theorem exists_positiveTest_fourier_ne_zero (f : PositiveTimeTest) (hf : f ≠ 0) :
    ∃ ξ : ℝ, (𝓕 (positiveTestToSchwartz f)) ξ ≠ 0 := by
  by_contra h
  have hz : 𝓕 (positiveTestToSchwartz f) = 0 := by
    ext ξ
    exact not_not.mp (not_exists.mp h ξ)
  have hw : positiveTestToSchwartz f = 0 := by
    simpa using congrArg (fun w : 𝓢(ℝ, ℂ) ↦ 𝓕⁻ w) hz
  apply hf
  apply TestFunction.ext
  intro x
  simpa only [positiveTestToSchwartz_apply, zero_apply] using
    congrArg (fun w : 𝓢(ℝ, ℂ) ↦ w x) hw

/-- Every nonzero positive-time test acts noncompactly on the original theta stage. -/
theorem fixedBoxOriginalTestAction_not_compact_of_ne_zero {X : ℝ} (hX : 0 < X)
    (f : PositiveTimeTest) (hf : f ≠ 0) :
    ¬ IsCompactOperator
      ((closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection.comp
        ((fixedBoxAmbientTestAction f).comp
          (closedStageSubmodule X ∅ (by simp)).toSubmodule.starProjection)) := by
  intro hK
  obtain ⟨ξ,hξ⟩ := exists_positiveTest_fourier_ne_zero f hf
  have hb := fixedBoxOriginalTestAction_fourier_norm_sub_compact_ge hX f ξ _ hK
  rw [sub_self, norm_zero] at hb
  exact (norm_pos_iff.mpr hξ).not_ge hb

/-- For every nonzero positive-time test, singleton-prime trace norms eventually
exceed every bound, uniformly over all positive total Fourier boxes. -/
theorem eventually_fixedBoxSingleton_traceNorm_gt
    (f : PositiveTimeTest) (hf : f ≠ 0) (C : ℝ) :
    ∃ B : ℕ, ∀ (p : ℕ) (hp : p.Prime), B < p →
      ∀ (X : ℝ) (hX : 0 < X) (hS1 : ∀ q ∈ ({p} : Finset ℕ), 1 ≤ q)
        (hS : ∀ q ∈ ({p} : Finset ℕ), q.Prime),
        C < traceNorm ⟨fixedBoxFiniteTestAction (X := X) {p} hS1 f,
          fixedBoxFiniteTestAction_nuclear hX {p} hS1 hS f⟩ := by
  obtain ⟨ξ,hξ⟩ := exists_positiveTest_fourier_ne_zero f hf
  let g := 𝓕 (positiveTestToSchwartz f)
  have hc : 0 < ‖g ξ‖ / 2 := half_pos (norm_pos_iff.mpr hξ)
  obtain ⟨m,hm⟩ := exists_nat_gt (C / (‖g ξ‖ / 2))
  obtain ⟨B,hB⟩ := eventually_prime_mesh_cluster g g.continuous ξ (‖g ξ‖ / 2) hc m
  refine ⟨B,fun p hp hpB X hX hS1 hS ↦ ?_⟩
  obtain ⟨n,hn,hnear⟩ := hB p hp hpB
  have hlo := norm_sum_ge_card_mul_of_near
    (fun i ↦ g ((n i : ℝ) / Real.log p)) (g ξ) (‖g ξ‖ / 2) (fun i ↦ (hnear i).le)
  have hup := fixedBoxFiniteTestAction_singleton_traceNorm_ge_samples hX p hp hS1 hS m n hn f
  have hmul := (div_lt_iff₀ hc).mp hm
  apply lt_of_lt_of_le _ hup
  dsimp only [g] at hlo hmul
  nlinarith



/-- Every nonzero test has a positive logarithmic lower growth rate for the
trace norms of actual singleton-prime levels, uniformly over all positive boxes. -/
theorem fixedBoxSingleton_traceNorm_ge_log_prime
    (f : PositiveTimeTest) (hf : f ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : ℕ, ∀ (p : ℕ) (hp : p.Prime), B < p →
      ∀ (X : ℝ) (hX : 0 < X) (hS1 : ∀ q ∈ ({p} : Finset ℕ), 1 ≤ q)
        (hS : ∀ q ∈ ({p} : Finset ℕ), q.Prime),
        c * Real.log p ≤ traceNorm ⟨fixedBoxFiniteTestAction (X := X) {p} hS1 f,
          fixedBoxFiniteTestAction_nuclear hX {p} hS1 hS f⟩ := by
  obtain ⟨ξ,hξ⟩ := exists_positiveTest_fourier_ne_zero f hf
  let g := 𝓕 (positiveTestToSchwartz f)
  have hc : 0 < ‖g ξ‖ := norm_pos_iff.mpr hξ
  obtain ⟨δ,hδ,hgδ⟩ := (Metric.continuousAt_iff.mp g.continuous.continuousAt) (‖g ξ‖/2) (half_pos hc)
  obtain ⟨B,hB⟩ := exists_nat_gt (Real.exp (4/δ))
  refine ⟨δ * ‖g ξ‖ / 8, by positivity, B, fun p hp hpB X hX hS1 hS ↦ ?_⟩
  have hL : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlog : 4/δ < Real.log (p : ℝ) :=
    (Real.lt_log_iff_exp_lt (by exact_mod_cast hp.pos)).mpr
      (hB.trans (by exact_mod_cast hpB))
  have hwide : 4 < Real.log (p : ℝ) * δ := (div_lt_iff₀ hδ).mp hlog
  let m : ℕ := ⌊δ * Real.log (p : ℝ) / 2⌋₊
  have hmle : (m : ℝ) ≤ δ * Real.log (p : ℝ) / 2 := Nat.floor_le (by positivity)
  have hmlt : δ * Real.log (p : ℝ) / 2 < (m : ℝ)+1 := Nat.lt_floor_add_one _
  obtain ⟨n,hn,hnear⟩ := exists_distinct_mesh_near ξ δ (Real.log p) m hL (by nlinarith)
  have hgnear (i : Fin m) : ‖g ((n i : ℝ) / Real.log p) - g ξ‖ ≤ ‖g ξ‖ / 2 := by
    exact (show ‖g ((n i : ℝ) / Real.log p) - g ξ‖ < ‖g ξ‖ / 2 from
      by simpa only [dist_eq_norm] using hgδ (hnear i)).le
  have hlo := norm_sum_ge_card_mul_of_near
    (fun i ↦ g ((n i : ℝ) / Real.log p)) (g ξ) (‖g ξ‖ / 2) hgnear
  have hup := fixedBoxFiniteTestAction_singleton_traceNorm_ge_samples hX p hp hS1 hS m n hn f
  apply le_trans _ hup
  have hmlo : δ * Real.log (p : ℝ) / 4 ≤ (m : ℝ) := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hmlo (half_pos hc).le
  dsimp only [g] at hlo hprod
  nlinarith



/-- Every nonzero positive-time test eventually has exactly zero singleton-level
trace but a trace norm growing at least logarithmically in the prime, uniformly
in the positive total Fourier box. -/
theorem fixedBoxSingleton_zero_trace_log_growth
    (f : PositiveTimeTest) (hf : f ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : ℕ, ∀ (p : ℕ) (hp : p.Prime), B < p →
      ∀ (X : ℝ) (hX : 0 < X) (hS1 : ∀ q ∈ ({p} : Finset ℕ), 1 ≤ q)
        (hS : ∀ q ∈ ({p} : Finset ℕ), q.Prime),
        hilbertTrace ⟨fixedBoxFiniteTestAction (X := X) {p} hS1 f,
          fixedBoxFiniteTestAction_nuclear hX {p} hS1 hS f⟩ = 0 ∧
        c * Real.log p ≤ traceNorm ⟨fixedBoxFiniteTestAction (X := X) {p} hS1 f,
          fixedBoxFiniteTestAction_nuclear hX {p} hS1 hS f⟩ := by
  obtain ⟨c,hc,B,hB⟩ := fixedBoxSingleton_traceNorm_ge_log_prime f hf
  obtain ⟨S,hS,hzero⟩ := positiveTest_prime_poisson_finite f
  refine ⟨c,hc,max B (S.sup id),fun p hp hpB X hX hS1 hSp ↦ ⟨?_,?_⟩⟩
  · have hpS : p ∉ S := by
      intro hmem
      have hle : p ≤ S.sup id := Finset.le_sup (f := id) hmem
      omega
    rw [fixedBoxFiniteTestAction_poisson_trace hX {p} hS1 hSp f, Finset.sum_singleton]
    exact hzero p hp hpS
  · exact hB p hp (by omega) X hX hS1 hSp



end RiemannMasullo.RationalPacket
