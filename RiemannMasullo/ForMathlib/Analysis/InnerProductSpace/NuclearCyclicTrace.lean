module

public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.NuclearRetraction

/-! # Cyclicity and triangular additivity of Hilbert nuclear traces -/

public noncomputable section
namespace RiemannMasullo
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem hilbertTrace_add_explicit (A B : H →L[ℂ] H)
    (hA : IsNuclearOperator A) (hB : IsNuclearOperator B) :
    hilbertTrace ⟨A+B, (nuclearEndomorphisms H).add_mem hA hB⟩ =
      hilbertTrace ⟨A,hA⟩ + hilbertTrace ⟨B,hB⟩ := by
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  exact (htr _).symm.trans ((tr.map_add ⟨A,hA⟩ ⟨B,hB⟩).trans (by rw [htr, htr]))

private theorem injective_shift (B : H →L[ℂ] H) :
    Function.Injective (B + (‖B‖ + 1 : ℂ) • ContinuousLinearMap.id ℂ H) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro z hz
  change (B + (‖B‖ + 1 : ℂ) • ContinuousLinearMap.id ℂ H) z = 0 at hz
  have he : B z = -((‖B‖ + 1 : ℂ) • z) := by
    simpa only [add_apply, smul_apply, ContinuousLinearMap.id_apply, eq_neg_iff_add_eq_zero] using hz
  have hn : ‖B z‖ = (‖B‖ + 1) * ‖z‖ := by
    rw [he, norm_neg, norm_smul]
    congr 1
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hb := B.le_opNorm z
  rw [hn] at hb
  have hzero : ‖z‖ = 0 := by nlinarith [norm_nonneg z]
  exact norm_eq_zero.mp hzero

/-- The Hilbert trace is cyclic for one nuclear and one bounded endomorphism. -/
theorem hilbertTrace_comp_comm (A B : H →L[ℂ] H) (hA : IsNuclearOperator A) :
    hilbertTrace ⟨A.comp B, mul_mem_nuclearEndomorphisms_right B ⟨A,hA⟩⟩ =
      hilbertTrace ⟨B.comp A, mul_mem_nuclearEndomorphisms_left B ⟨A,hA⟩⟩ := by
  let c : ℂ := ‖B‖ + 1
  let T := B + c • ContinuousLinearMap.id ℂ H
  have ht : Function.Injective T := injective_shift B
  have hcyc := nuclearTrace_factor_comps (hilbert_approximationProperty (H := H))
    (hilbert_approximationProperty (H := H)) T ht A hA
  have hAT : IsNuclearOperator (A.comp T) := mul_mem_nuclearEndomorphisms_right T ⟨A,hA⟩
  have hTA : IsNuclearOperator (T.comp A) := mul_mem_nuclearEndomorphisms_left T ⟨A,hA⟩
  have htrace : hilbertTrace ⟨A.comp T,hAT⟩ = hilbertTrace ⟨T.comp A,hTA⟩ := by
    simpa only [hilbertTrace_eq_nuclearTrace] using! hcyc
  have hleft : A.comp T = A.comp B + c • A := by
    simp only [T, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.comp_id]
  have hright : T.comp A = B.comp A + c • A := by
    simp only [T, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.id_comp]
  have hAB := mul_mem_nuclearEndomorphisms_right B ⟨A,hA⟩
  have hBA := mul_mem_nuclearEndomorphisms_left B ⟨A,hA⟩
  have hcA := (nuclearEndomorphisms H).smul_mem c hA
  have he : hilbertTrace ⟨A.comp B,hAB⟩ + hilbertTrace ⟨c • A,hcA⟩ =
      hilbertTrace ⟨B.comp A,hBA⟩ + hilbertTrace ⟨c • A,hcA⟩ := by
    have hl := hilbertTrace_add_explicit (A.comp B) (c • A) hAB hcA
    have hr := hilbertTrace_add_explicit (B.comp A) (c • A) hBA hcA
    apply hl.symm.trans
    apply Eq.trans _ hr
    simpa only [hleft, hright] using! htrace
  exact add_right_cancel he


/-- The trace of a nuclear triangular action is the sum of its two diagonal
traces. The hypotheses encode a decomposition of its right support. -/
theorem hilbertTrace_two_block (A P Q R : H →L[ℂ] H) (hA : IsNuclearOperator A)
    (hPQ : P+Q=R) (hAR : A.comp R = A) :
    hilbertTrace ⟨A,hA⟩ =
      hilbertTrace ⟨A.comp P, mul_mem_nuclearEndomorphisms_right P ⟨A,hA⟩⟩ +
      hilbertTrace ⟨Q.comp A, mul_mem_nuclearEndomorphisms_left Q ⟨A,hA⟩⟩ := by
  have he : A = A.comp P + A.comp Q := by
    rw [← ContinuousLinearMap.comp_add, hPQ, hAR]
  have hAP := mul_mem_nuclearEndomorphisms_right P ⟨A,hA⟩
  have hAQ := mul_mem_nuclearEndomorphisms_right Q ⟨A,hA⟩
  have hadd := hilbertTrace_add_explicit (A.comp P) (A.comp Q) hAP hAQ
  have hs : hilbertTrace ⟨A,hA⟩ =
      hilbertTrace ⟨A.comp P,hAP⟩ + hilbertTrace ⟨A.comp Q,hAQ⟩ := by
    simpa only [← he] using! hadd
  exact hs.trans (congrArg (hilbertTrace ⟨A.comp P,hAP⟩ + ·) (hilbertTrace_comp_comm A Q hA))

end RiemannMasullo
