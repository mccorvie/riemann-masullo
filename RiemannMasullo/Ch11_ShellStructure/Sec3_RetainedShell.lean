module

public import Mathlib.Analysis.Normed.Module.HahnBanach
public import RiemannMasullo.AppC_LCTVS.Sec3a_part2

/-! # Trace estimates and a test for a retained orbital shell

A frequency band of the rational line quotient contributes a finite-rank operator.
The estimate below makes the sum of such bands trace class under bounds on their
ranks and operator norms. The single-test result applies when the orbital functional has no bounded
representation through the spectral diagonal.
Nothing imports this file.
-/

public section

namespace RiemannMasullo.Isolated

private theorem retainedShell_traceNorm_le_of_rank_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : H →L[ℂ] H) (N : ℕ) (hB : Module.rank ℂ B.toLinearMap.range ≤ (N : Cardinal)) :
    ∃ h : IsNuclearOperator B, traceNorm ⟨B, h⟩ ≤ N * ‖B‖ := by
  have hnonneg (n : ℕ) : 0 ≤ approximationNumber B n :=
    Real.sInf_nonneg (by rintro _ ⟨_, _, rfl⟩; exact norm_nonneg _)
  have happrox (A : H →L[ℂ] H) {n : ℕ}
      (hA : Module.rank ℂ A.toLinearMap.range ≤ (n : Cardinal)) :
      approximationNumber B n ≤ ‖A - B‖ :=
    csInf_le ⟨0, by rintro _ ⟨_, _, rfl⟩; exact norm_nonneg _⟩ ⟨A, hA, rfl⟩
  have hle (n : ℕ) : approximationNumber B n ≤ ‖B‖ := by
    simpa using happrox 0 (n := n) (by simp)
  have hzero (n : ℕ) (hn : n ∉ Finset.range N) : approximationNumber B n = 0 := by
    have hn' : N ≤ n := Nat.le_of_not_gt (fun h ↦ hn (Finset.mem_range.mpr h))
    have hr : Module.rank ℂ B.toLinearMap.range ≤ (n : Cardinal) :=
      hB.trans (by exact_mod_cast hn')
    exact le_antisymm (by simpa using happrox B hr) (hnonneg n)
  have : FiniteDimensional ℂ B.toLinearMap.range :=
    Module.rank_lt_aleph0_iff.mp (hB.trans_lt Cardinal.natCast_lt_aleph0)
  have : ProperSpace B.toLinearMap.range := FiniteDimensional.proper_rclike ℂ _
  have hcompact : IsCompactOperator B :=
    (isCompactOperator_of_locallyCompactSpace_dom B.rangeRestrict).continuous_comp
      continuous_subtype_val
  have hsum : Summable (approximationNumber B) := summable_of_ne_finset_zero hzero
  have hmem : B ∈ traceClassOperators H H :=
    ⟨hcompact, by simpa only [Real.rpow_one] using hsum⟩
  refine ⟨(mem_traceClassOperators_iff_isNuclearOperator B).mp hmem, ?_⟩
  rw [← schattenNorm_one_eq_traceNorm]
  simp only [schattenNorm, Real.rpow_one, div_one]
  rw [tsum_eq_sum hzero]
  exact (Finset.sum_le_sum fun n _ ↦ hle n).trans_eq (by simp)

/-- Paper: (11.3.2.4)–(11.3.2.5), p. 496.
The operator-norm sum of endomorphisms of bounded finite ranks is nuclear if
the products of the rank bounds and operator norms are summable.
Reconstruction: On the rational line the terms can be taken as frequency bands,
with ranks controlled by the number of admitted evaluations in each band. -/
theorem retainedShell_bandSeries_nuclear
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (B : ι → H →L[ℂ] H) (N : ι → ℕ) (A : H →L[ℂ] H)
    (hB : ∀ i, Module.rank ℂ (B i).toLinearMap.range ≤ (N i : Cardinal))
    (hs : HasSum B A) (hcost : Summable (fun i ↦ (N i : ℝ) * ‖B i‖)) :
    ∃ h : IsNuclearOperator A, traceNorm ⟨A, h⟩ ≤ ∑' i, (N i : ℝ) * ‖B i‖ := by
  choose hn hnorm using fun i ↦ retainedShell_traceNorm_le_of_rank_le (B i) (N i) (hB i)
  exact traceNorm_le_of_hasSum (fun i ↦ ⟨B i, hn i⟩) A hs _ hcost hnorm

/-- Paper: (11.3.2.4)–(11.3.2.5), p. 496.
A spectral operator whose trace norm is below half the orbital magnitude
gives a trace below that threshold under every contractive gate.
Reconstruction: For the reversed line kernel the spectral operator is
convolution after spectral projection. The retained geometric shell
is its trace against a contractive multiplier after the sign cancellation. -/
theorem retainedShell_trace_lt_half_orbital
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : nuclearEndomorphisms H) (M : H →L[ℂ] H) (hM : ‖M‖ ≤ 1)
    (orbital : ℂ) (hsmall : traceNorm T * 2 < ‖orbital‖) :
    ‖hilbertTrace ⟨M * T.val, mul_mem_nuclearEndomorphisms_left M T⟩‖ < ‖orbital‖ / 2 := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have hnonneg : 0 ≤ traceNorm T :=
    (traceNorm_normedSpaceCore (H := H)).norm_nonneg T
  calc
    _ ≤ traceNorm ⟨M * T.val, mul_mem_nuclearEndomorphisms_left M T⟩ :=
      norm_hilbertTrace_le _
    _ ≤ ‖M‖ * traceNorm T := traceNorm_mul_left_le M T
    _ ≤ traceNorm T := mul_le_of_le_one_left hnonneg hM
    _ < ‖orbital‖ / 2 := (lt_div_iff₀ zero_lt_two).2 hsmall

/-- Paper: (11.3.2.4)–(11.3.2.5), p. 496.
A strict line trace bound persists under all contractive gates if the trace-norm
change is eventually bounded by a cost smaller than the available margin.
Reconstruction: At positive strip width the change includes extra interior
Mellin derivatives whose evaluations do not survive at width zero. -/
theorem retainedShell_eventually_trace_lt_half_orbital
    {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (l : Filter ι) (T : ι → nuclearEndomorphisms H) (T₀ : nuclearEndomorphisms H)
    (orbital : ℂ) (cost : ℝ) (hmargin : 2 * (traceNorm T₀ + cost) < ‖orbital‖)
    (hchange : ∀ ε > 0, ∀ᶠ i in l, traceNorm (T i - T₀) ≤ cost + ε) :
    ∀ᶠ i in l, ∀ (M : H →L[ℂ] H) (_ : ‖M‖ ≤ 1),
      ‖hilbertTrace ⟨M * (T i).val, mul_mem_nuclearEndomorphisms_left M (T i)⟩‖ <
        ‖orbital‖ / 2 := by
  have hgap : 0 < ‖orbital‖ / 2 - (traceNorm T₀ + cost) := by linarith
  filter_upwards [hchange _ (half_pos hgap)] with i hi M hM
  apply retainedShell_trace_lt_half_orbital (T i) M hM orbital
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  have htriangle : traceNorm (T i) ≤ traceNorm (T i - T₀) + traceNorm T₀ := by
    simpa only [sub_add_cancel] using
      (traceNorm_normedSpaceCore (H := H)).norm_triangle (T i - T₀) T₀
  linarith

/-- Paper: (11.3.2.1), p. 495, and (11.3.2.4)–(11.3.2.5), p. 496.
If the orbital functional has no bounded representation through the spectral
diagonal, one test has orbital magnitude larger than the proposed bound on all
localized shell magnitudes.
Reconstruction: The range of the diagonal map is a subspace of logarithmic
`L¹`. Hahn–Banach extends a bounded representation on that range. -/
theorem retainedShell_exists_test_of_no_bounded_representation
    {Test E : Type*} [AddCommGroup Test] [Module ℂ Test]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (diagonal : Test →ₗ[ℂ] E) (orbital : Test →ₗ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hfail : ¬ ∃ r : E →L[ℂ] ℂ, ‖r‖ ≤ C ∧ ∀ φ, r (diagonal φ) = orbital φ) :
    ∃ φ, C * ‖diagonal φ‖ < ‖orbital φ‖ := by
  by_contra! hbound
  have hker : diagonal.ker ≤ orbital.ker := by
    intro φ hφ
    rw [LinearMap.mem_ker] at hφ ⊢
    have h := hbound φ
    rw [hφ, norm_zero, mul_zero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  let L : diagonal.range →ₗ[ℂ] ℂ :=
    (diagonal.ker.liftQ orbital hker).comp diagonal.quotKerEquivRange.symm.toLinearMap
  have heval (φ : Test) : L ⟨diagonal φ, LinearMap.mem_range_self diagonal φ⟩ = orbital φ := by
    change diagonal.ker.liftQ orbital hker
      (diagonal.quotKerEquivRange.symm ⟨diagonal φ, _⟩) = orbital φ
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hL (v : diagonal.range) : ‖L v‖ ≤ C * ‖v‖ := by
    obtain ⟨φ, hφ⟩ := v.property
    have hv : v = ⟨diagonal φ, LinearMap.mem_range_self diagonal φ⟩ := Subtype.ext hφ.symm
    rw [hv, heval]
    exact hbound φ
  obtain ⟨r, hr, hnorm⟩ := exists_extension_norm_eq diagonal.range (L.mkContinuous C hL)
  exact hfail ⟨r, hnorm.le.trans (L.mkContinuous_norm_le hC hL), fun φ ↦
    (hr ⟨diagonal φ, LinearMap.mem_range_self diagonal φ⟩).trans (heval φ)⟩

end RiemannMasullo.Isolated
