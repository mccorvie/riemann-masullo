module
public import RiemannMasullo.AppC_LCTVS.Sec3a_part2

@[expose] public noncomputable section
open Set
open scoped BigOperators
namespace RiemannMasullo
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A finite-rank Hilbert-space operator is nuclear, and its trace norm is
bounded by its rank times its operator norm. -/
theorem finiteRank_nuclear_traceNorm_le
    (T : H →L[ℂ] H) (hT : FiniteDimensional ℂ T.toLinearMap.range) :
    ∃ hn : IsNuclearOperator T,
      traceNorm ⟨T, hn⟩ ≤ (Module.finrank ℂ T.toLinearMap.range : ℝ) * ‖T‖ := by
  classical
  let d := Module.finrank ℂ T.toLinearMap.range
  have hnonneg (n : ℕ) : 0 ≤ approximationNumber T n :=
    Real.sInf_nonneg fun _ ⟨_, _, h⟩ ↦ h ▸ norm_nonneg _
  have hlow (n : ℕ) : ∀ r ∈ {r | ∃ S : H →L[ℂ] H,
      Module.rank ℂ S.toLinearMap.range ≤ (n : Cardinal) ∧ r = ‖S - T‖}, 0 ≤ r :=
    fun _ ⟨_, _, h⟩ ↦ h ▸ norm_nonneg _
  have hle (n : ℕ) : approximationNumber T n ≤ ‖T‖ := by
    unfold approximationNumber
    apply csInf_le ⟨0, hlow n⟩
    exact ⟨0, by simp, by simp⟩
  have hz (n : ℕ) (hn : d ≤ n) : approximationNumber T n = 0 := by
    apply le_antisymm _ (hnonneg n)
    have hr : Module.rank ℂ T.toLinearMap.range ≤ (n : Cardinal) := by
      rw [← Module.finrank_eq_rank]
      exact_mod_cast hn
    unfold approximationNumber
    apply csInf_le ⟨0, hlow n⟩
    exact ⟨T, hr, by simp⟩
  have hs : Summable (approximationNumber T) := summable_of_ne_finset_zero
    (s := Finset.range d) (fun n hn ↦ hz n (by simpa using hn))
  have hc : IsCompactOperator T := by
    have : ProperSpace T.toLinearMap.range := FiniteDimensional.proper_rclike ℂ _
    let T' := T.codRestrict T.toLinearMap.range (fun x ↦ LinearMap.mem_range_self _ x)
    exact (isCompactOperator_of_locallyCompactSpace_dom T').continuous_comp continuous_subtype_val
  have hn : IsNuclearOperator T := (mem_traceClassOperators_iff_isNuclearOperator T).mp
    ⟨hc, by simpa only [Real.rpow_one] using hs⟩
  refine ⟨hn, ?_⟩
  rw [← schattenNorm_one_eq_traceNorm]
  simp only [schattenNorm, Real.rpow_one, div_one]
  rw [tsum_eq_sum (s := Finset.range d) (fun n hn ↦ hz n (by simpa using hn))]
  calc
    ∑ n ∈ Finset.range d, approximationNumber T n ≤ ∑ _n ∈ Finset.range d, ‖T‖ :=
      Finset.sum_le_sum fun n _ ↦ hle n
    _ = _ := by simp [d]

/-- A norm-convergent series of finite-rank operators is nuclear if the sum
of rank times operator norm is finite. -/
theorem isNuclearOperator_of_hasSum_finiteRank {ι : Type*}
    (A : ι → H →L[ℂ] H) (hA : ∀ i, FiniteDimensional ℂ (A i).toLinearMap.range)
    (T : H →L[ℂ] H) (hs : HasSum A T)
    (hc : Summable (fun i ↦ (Module.finrank ℂ (A i).toLinearMap.range : ℝ) * ‖A i‖)) :
    IsNuclearOperator T := by
  choose hn hb using fun i ↦ finiteRank_nuclear_traceNorm_le (A i) (hA i)
  exact (traceNorm_le_of_hasSum (fun i ↦ ⟨A i, hn i⟩) T hs _ hc hb).choose

end RiemannMasullo
