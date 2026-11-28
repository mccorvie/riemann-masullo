module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxAbsoluteBounds
public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxFiniteTrace
public import RiemannMasullo.ForMathlib.Analysis.Fourier.MeshMass

/-! # Uniform logarithmic trace-norm growth in every actual rational packet

For every nonzero Schwartz test the actual unweighted packet norm is at least
c log(p), uniformly over all earlier prime sets and positive common Fourier
boxes. Positive-time compact tests have zero scalar trace at all those late
packets. Thus the zero traces cannot justify aggregating these operators in
trace norm. This formalizes the obstruction described by mrshu in #7351,
comment 7152400629, within the actual unweighted model; it does not address
the signed global-to-local comparison or positive-width strip lifts.
-/

public noncomputable section
open Set Function
open scoped FourierTransform SchwartzMap Topology
namespace RiemannMasullo.RationalPacket

private theorem nuclear_lower_trans {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H) {c M U : ℝ}
    (hc : c ≤ M)
    (hb : ∃ hn : IsNuclearOperator A, M ≤ traceNorm ⟨A,hn⟩ ∧ traceNorm ⟨A,hn⟩ ≤ U) :
    ∃ hn : IsNuclearOperator A, c ≤ traceNorm ⟨A,hn⟩ := by
  obtain ⟨hn,hlo,_⟩ := hb
  exact ⟨hn,hc.trans hlo⟩

private theorem nuclear_trace_lower_combine {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H) {c : ℝ} {z : ℂ}
    (hb : ∃ hn : IsNuclearOperator A, c ≤ traceNorm ⟨A,hn⟩)
    (ht : ∃ hn : IsNuclearOperator A, hilbertTrace ⟨A,hn⟩ = z) (hz : z = 0) :
    ∃ hn : IsNuclearOperator A, hilbertTrace ⟨A,hn⟩ = 0 ∧ c ≤ traceNorm ⟨A,hn⟩ := by
  obtain ⟨hn,hb⟩ := hb
  obtain ⟨hn',ht⟩ := ht
  exact ⟨hn,ht.trans hz,hb⟩

private theorem schwartz_prime_mesh_growth (w : 𝓢(ℝ, ℂ)) (hw : w ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : ℕ, ∀ (p : ℕ) (_hp : p.Prime), B < p →
      c * Real.log p ≤ ∑' n : ℤ, ‖(𝓕 w) ((n : ℝ) / Real.log p)‖ := by
  have hne : ∃ ξ : ℝ, (𝓕 w) ξ ≠ 0 := by
    by_contra h
    have hz : 𝓕 w = 0 := by
      ext ξ
      exact not_not.mp (not_exists.mp h ξ)
    apply hw
    simpa using congrArg (fun v : 𝓢(ℝ, ℂ) ↦ 𝓕⁻ v) hz
  obtain ⟨ξ,hξ⟩ := hne
  obtain ⟨c,hc,B,_,hB⟩ := abs_mesh_sum_ge_linear (fun x ↦ (𝓕 w) x) ξ
    (𝓕 w).continuous.continuousAt hξ
  obtain ⟨N,hN⟩ := exists_nat_gt (Real.exp B)
  refine ⟨c,hc,N,?_⟩
  intro p hp hpN
  have hlog : B < Real.log (p : ℝ) :=
    (Real.lt_log_iff_exp_lt (by exact_mod_cast hp.pos)).mpr
      (hN.trans (by exact_mod_cast hpN))
  exact hB (Real.log p) hlog (summable_fixedBox_test_symbol p hp w)

/-- The actual packet trace norm grows logarithmically with the new prime for
every nonzero Schwartz test, uniformly over all earlier prime sets and positive
Fourier boxes. -/
theorem fixedBoxTestAction_traceNorm_ge_log_prime (w : 𝓢(ℝ, ℂ)) (hw : w ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : ℕ, ∀ (p : ℕ) (hp : p.Prime), B < p →
      ∀ (X : ℝ) (hX : 0 < X) (T : Finset ℕ) (hT1 : ∀ q ∈ T, 1 ≤ q)
        (hTp1 : ∀ q ∈ insert p T, 1 ≤ q) (hpT : p ∉ T) (_hT : ∀ q ∈ T, q.Prime),
        ∃ h : IsNuclearOperator (fixedBoxTestAction T hT1 p hTp1 hX hp hpT w),
          c * Real.log p ≤ traceNorm (H := FixedBoxQuotient[X,T,hT1,p,hTp1])
            ⟨fixedBoxTestAction T hT1 p hTp1 hX hp hpT w,h⟩ := by
  have hm := schwartz_prime_mesh_growth w hw
  let c := hm.choose
  have hc : 0 < c := hm.choose_spec.1
  let B := hm.choose_spec.2.choose
  have hB := hm.choose_spec.2.choose_spec
  refine ⟨c,hc,B,?_⟩
  intro p hp hpB X hX T hT1 hTp1 hpT hT
  exact nuclear_lower_trans (fixedBoxTestAction T hT1 p hTp1 hX hp hpT w)
    (hB p hp hpB)
    (fixedBoxTestAction_traceNorm_symbol_bounds T hT1 p hTp1 hX hp hpT hT w)

/-- The late actual packets have zero scalar trace but logarithmically growing
trace norm, with one threshold and growth constant for every earlier prime set
and every positive common Fourier box. -/
theorem fixedBoxTestAction_zero_trace_log_growth (f : PositiveTimeTest) (hf : f ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : ℕ, ∀ (p : ℕ) (hp : p.Prime), B < p →
      ∀ (X : ℝ) (hX : 0 < X) (T : Finset ℕ) (hT1 : ∀ q ∈ T, 1 ≤ q)
        (hTp1 : ∀ q ∈ insert p T, 1 ≤ q) (hpT : p ∉ T) (_hT : ∀ q ∈ T, q.Prime),
        ∃ h : IsNuclearOperator
          (fixedBoxTestAction T hT1 p hTp1 hX hp hpT (positiveTestToSchwartz f)),
          hilbertTrace (H := FixedBoxQuotient[X,T,hT1,p,hTp1])
            ⟨fixedBoxTestAction T hT1 p hTp1 hX hp hpT (positiveTestToSchwartz f),h⟩ = 0 ∧
          c * Real.log p ≤ traceNorm (H := FixedBoxQuotient[X,T,hT1,p,hTp1])
            ⟨fixedBoxTestAction T hT1 p hTp1 hX hp hpT (positiveTestToSchwartz f),h⟩ := by
  have hw : positiveTestToSchwartz f ≠ 0 := by
    intro hw
    apply hf
    apply TestFunction.ext
    intro x
    simpa only [positiveTestToSchwartz_apply, zero_apply] using
      congrArg (fun w : 𝓢(ℝ, ℂ) ↦ w x) hw
  have hgrowth := fixedBoxTestAction_traceNorm_ge_log_prime (positiveTestToSchwartz f) hw
  let c := hgrowth.choose
  have hc : 0 < c := hgrowth.choose_spec.1
  let B := hgrowth.choose_spec.2.choose
  have hB := hgrowth.choose_spec.2.choose_spec
  have hz := positiveTest_prime_poisson_finite f
  let S := hz.choose
  have hzero := hz.choose_spec.2
  refine ⟨c,hc,max B (S.sup id),?_⟩
  intro p hp hpB X hX T hT1 hTp1 hpT hT
  have hg := hB p hp (by omega) X hX T hT1 hTp1 hpT hT
  have ht := fixedBoxTestAction_poisson_trace T hT1 p hTp1 hX hp hpT hT
    (positiveTestToSchwartz f)
  apply nuclear_trace_lower_combine
    (fixedBoxTestAction T hT1 p hTp1 hX hp hpT (positiveTestToSchwartz f)) hg ht
  have hpS : p ∉ S := by
    intro hmem
    have hle : p ≤ S.sup id := Finset.le_sup (f := id) hmem
    omega
  simpa only [positiveTestToSchwartz_apply] using hzero p hp hpS


end RiemannMasullo.RationalPacket
