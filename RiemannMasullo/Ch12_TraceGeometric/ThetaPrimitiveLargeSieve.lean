module

public import RiemannMasullo.Ch12_TraceGeometric.ThetaDirichletAverage
import RiemannMasullo.ForMathlib.Analysis.Fourier.LargeSieve

/-!
# A large sieve for primitive Dirichlet theta rows

Summing over all primitive characters of conductor at most Q controls the squared
theta error by the diagonal energy times Q² + π(U−L). The coefficient functions
may be integrated over any common measure space. This includes the visible rational
Möbius error in the comparison for Theorem 12.5.1.1, pp. 519–520.
-/

open Finset Complex MeasureTheory AdditiveLargeSieve
open scoped Classical

public noncomputable section

namespace RiemannMasullo

private theorem additiveRow_eq_fourierSum (m : ℕ) (S : Finset ℕ) (f : ℕ → ℂ) (a : ZMod (m + 1)) :
    dirichletThetaAdditiveRow a S f = fourierSum S f ((a.val : ℝ) / (m + 1)) := by
  unfold dirichletThetaAdditiveRow fourierSum
  apply Finset.sum_congr rfl
  intro n _
  have he : ZMod.stdAddChar ((n : ZMod (m + 1)) * a) =
      Complex.exp ((n : ℂ) * (2 * Real.pi * I) * (((a.val : ℝ) / (m + 1) : ℝ) : ℂ)) := by
    calc
      _ = ZMod.stdAddChar ((((n : ℤ) * (a.val : ℤ)) : ℤ) : ZMod (m + 1)) := by push_cast; rw [ZMod.natCast_zmod_val]
      _ = _ := (ZMod.stdAddChar_coe (N := m + 1) ((n : ℤ) * (a.val : ℤ))).trans (by congr 1; push_cast; ring)
  rw [he, mul_comm]

private theorem sum_units_eq_sum_coprime (m : ℕ) (F : ℕ → ℝ) :
    (∑ a : ZMod (m + 1), if IsUnit a then F a.val else 0) =
      ∑ j ∈ (Finset.range (m + 1)).filter (fun j ↦ j.Coprime (m + 1)), F j := by
  rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_equiv (ZMod.finEquiv (m + 1)).symm.toEquiv
  intro z
  change (if IsUnit z then F z.val else 0) = if z.val.Coprime (m + 1) then F z.val else 0
  have he := ZMod.isUnit_iff_coprime z.val (m + 1)
  rw [ZMod.natCast_zmod_val] at he
  simp only [he]

private def reducedFractionRow (m : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (m + 1)).filter (fun j ↦ j.Coprime (m + 1))).image (fun j ↦ (j, m + 1))

private theorem mem_reducedFractionRow {m : ℕ} {u : ℕ × ℕ} :
    u ∈ reducedFractionRow m ↔ u.1 < m + 1 ∧ u.1.Coprime (m + 1) ∧ u.2 = m + 1 := by
  rcases u with ⟨a, b⟩
  simp [reducedFractionRow, Finset.mem_image, and_assoc, eq_comm]

private theorem sum_reducedFractionRows (Q : ℕ) (F : ℕ × ℕ → ℝ) :
    (∑ u ∈ (Finset.range Q).biUnion reducedFractionRow, F u) =
      ∑ m ∈ Finset.range Q, ∑ j ∈ (Finset.range (m + 1)).filter (fun j ↦ j.Coprime (m + 1)), F (j, m + 1) := by
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro m _
    exact Finset.sum_image (fun i _ j _ he ↦ congrArg Prod.fst he)
  · intro i _ j _ hij
    exact Finset.disjoint_left.mpr fun u hi hj ↦ hij (by
      have h := (mem_reducedFractionRow.mp hi).2.2.symm.trans (mem_reducedFractionRow.mp hj).2.2
      omega)

/-- The large sieve for primitive Dirichlet characters of all conductors through Q. -/
theorem dirichletThetaRow_primitive_large_sieve (Q : ℕ) (hQ : 0 < Q) (S : Finset ℕ) (f : ℕ → ℂ)
    {L U : ℕ} (hLU : L ≤ U) (hs : ∀ n ∈ S, L ≤ n ∧ n ≤ U) :
    (∑ m ∈ Finset.range Q, (((m + 1 : ℕ) : ℝ) / (m + 1).totient) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (m + 1))).filter (·.IsPrimitive),
        ‖dirichletThetaRow χ S f‖ ^ 2) ≤
      ((Q : ℝ) ^ 2 + Real.pi * ((U : ℝ) - L)) * ∑ n ∈ S, ‖f n‖ ^ 2 := by
  let G (u : ℕ × ℕ) := ‖fourierSum S f ((u.1 : ℝ) / u.2)‖ ^ 2
  have hrow (m : ℕ) : (((m + 1 : ℕ) : ℝ) / (m + 1).totient) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (m + 1))).filter (·.IsPrimitive),
        ‖dirichletThetaRow χ S f‖ ^ 2 ≤
      ∑ j ∈ (Finset.range (m + 1)).filter (fun j ↦ j.Coprime (m + 1)), G (j, m + 1) := by
    have h := dirichletThetaRow_primitive_additive_bound S f
      ((Finset.univ : Finset (DirichletCharacter ℂ (m + 1))).filter (·.IsPrimitive))
      (fun _ hχ ↦ (Finset.mem_filter.mp hχ).2)
    simp_rw [additiveRow_eq_fourierSum] at h
    have hu := sum_units_eq_sum_coprime m (fun j ↦ ‖fourierSum S f ((j : ℝ) / (m + 1))‖ ^ 2)
    rw [hu] at h
    dsimp only [G]
    push_cast
    push_cast at h
    rw [div_mul_eq_mul_div, div_le_iff₀ (by exact_mod_cast Nat.totient_pos.mpr (Nat.succ_pos m) : (0 : ℝ) < (m + 1).totient)]
    simpa only [mul_comm] using h
  apply (Finset.sum_le_sum (fun m _ ↦ hrow m)).trans
  rw [← sum_reducedFractionRows]
  apply AdditiveLargeSieve.sum_norm_sq_le_at_reduced_fractions hQ _ _ S f hLU hs
  intro u hu
  obtain ⟨m, hm, he⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨ha, hb, hc⟩ := mem_reducedFractionRow.mp he
  rw [hc]
  exact ⟨ha, Finset.mem_range.mp hm, hb⟩

private theorem integrable_dirichletThetaRow_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {q : ℕ} (χ : DirichletCharacter ℂ q) {S : Finset ℕ} {f : ℕ → α → ℂ}
    (hf : ∀ n ∈ S, MemLp (f n) 2 μ) :
    Integrable (fun y ↦ ‖dirichletThetaRow χ S (fun n ↦ f n y)‖ ^ 2) μ := by
  have h := memLp_finsetSum S (fun n hn ↦ (hf n hn).const_smul (χ (n : ZMod q)))
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

/-- The primitive-character large sieve integrated over a common measure for all coefficient functions. -/
theorem dirichletThetaRow_primitive_large_sieve_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (Q : ℕ) (hQ : 0 < Q) (S : Finset ℕ) {f : ℕ → α → ℂ} (hf : ∀ n ∈ S, MemLp (f n) 2 μ)
    {L U : ℕ} (hLU : L ≤ U) (hs : ∀ n ∈ S, L ≤ n ∧ n ≤ U) :
    (∑ m ∈ Finset.range Q, (((m + 1 : ℕ) : ℝ) / (m + 1).totient) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (m + 1))).filter (·.IsPrimitive),
        ∫ y, ‖dirichletThetaRow χ S (fun n ↦ f n y)‖ ^ 2 ∂μ) ≤
      ((Q : ℝ) ^ 2 + Real.pi * ((U : ℝ) - L)) * ∑ n ∈ S, ∫ y, ‖f n y‖ ^ 2 ∂μ := by
  let P (m : ℕ) := (Finset.univ : Finset (DirichletCharacter ℂ (m + 1))).filter (·.IsPrimitive)
  let w (m : ℕ) := (((m + 1 : ℕ) : ℝ) / (m + 1).totient)
  let E (m : ℕ) (χ : DirichletCharacter ℂ (m + 1)) (y : α) := ‖dirichletThetaRow χ S (fun n ↦ f n y)‖ ^ 2
  have he (m : ℕ) (χ : DirichletCharacter ℂ (m + 1)) : Integrable (E m χ) μ := integrable_dirichletThetaRow_sq χ hf
  have hrow (m : ℕ) : w m * (∑ χ ∈ P m, ∫ y, E m χ y ∂μ) = ∫ y, w m * ∑ χ ∈ P m, E m χ y ∂μ := by
    rw [integral_const_mul, integral_finsetSum (P m) (fun χ _ ↦ he m χ)]
  have hi (n : ℕ) (hn : n ∈ S) := (memLp_two_iff_integrable_sq_norm (hf n hn).aestronglyMeasurable).mp (hf n hn)
  change (∑ m ∈ Finset.range Q, w m * ∑ χ ∈ P m, ∫ y, E m χ y ∂μ) ≤ _
  simp_rw [hrow]
  have hwm (m : ℕ) : Integrable (fun y ↦ w m * ∑ χ ∈ P m, E m χ y) μ :=
    (integrable_finsetSum (P m) (fun χ _ ↦ he m χ)).const_mul _
  rw [← integral_finsetSum _ (fun m _ ↦ hwm m), ← integral_finsetSum S hi, ← integral_const_mul]
  exact integral_mono (integrable_finsetSum _ (fun m _ ↦ hwm m)) ((integrable_finsetSum S hi).const_mul _)
    (fun y ↦ dirichletThetaRow_primitive_large_sieve Q hQ S (fun n ↦ f n y) hLU hs)

/-- Count primitive characters across all conductors through Q for which the integrated squared norm exceeds a threshold. -/
theorem dirichletThetaRow_primitive_large_sieve_exception_count {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (Q : ℕ) (hQ : 0 < Q) (S : Finset ℕ) {f : ℕ → α → ℂ} (hf : ∀ n ∈ S, MemLp (f n) 2 μ)
    {L U : ℕ} (hLU : L ≤ U) (hs : ∀ n ∈ S, L ≤ n ∧ n ≤ U)
    (B : (m : ℕ) → Finset (DirichletCharacter ℂ (m + 1))) (δ : ℝ)
    (hbad : ∀ m ∈ Finset.range Q, ∀ χ ∈ B m, χ.IsPrimitive ∧ δ ≤ ∫ y, ‖dirichletThetaRow χ S (fun n ↦ f n y)‖ ^ 2 ∂μ) :
    ((∑ m ∈ Finset.range Q, (B m).card : ℕ) : ℝ) * δ ≤
      ((Q : ℝ) ^ 2 + Real.pi * ((U : ℝ) - L)) * ∑ n ∈ S, ∫ y, ‖f n y‖ ^ 2 ∂μ := by
  apply le_trans _ (dirichletThetaRow_primitive_large_sieve_integral Q hQ S hf hLU hs)
  rw [Nat.cast_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro m hm
  let E (χ : DirichletCharacter ℂ (m + 1)) := ∫ y, ‖dirichletThetaRow χ S (fun n ↦ f n y)‖ ^ 2 ∂μ
  let P := (Finset.univ : Finset (DirichletCharacter ℂ (m + 1))).filter (·.IsPrimitive)
  have hP : B m ⊆ P := fun χ hχ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hbad m hm χ hχ).1⟩
  have he (χ : DirichletCharacter ℂ (m + 1)) : 0 ≤ E χ := integral_nonneg fun _ ↦ sq_nonneg _
  calc
    _ = ∑ _χ ∈ B m, δ := by simp
    _ ≤ ∑ χ ∈ B m, E χ := Finset.sum_le_sum fun χ hχ ↦ (hbad m hm χ hχ).2
    _ ≤ ∑ χ ∈ P, E χ := Finset.sum_le_sum_of_subset_of_nonneg hP (fun χ _ _ ↦ he χ)
    _ ≤ _ := by
      apply le_mul_of_one_le_left (Finset.sum_nonneg fun χ _ ↦ he χ)
      exact (one_le_div (by exact_mod_cast Nat.totient_pos.mpr (Nat.succ_pos m))).mpr
        (by exact_mod_cast Nat.totient_le (m + 1))

/-- The integrated primitive-character large sieve for the actual visible rational Möbius theta coefficients. -/
theorem thetaMoebius_visible_primitive_large_sieve (Q : ℕ) (hQ : 0 < Q) (S : Finset ℕ) (w : ℕ → ℂ) (h : ℝ → ℂ)
    (μ : Measure ℝ) (hh : ∀ n ∈ S, MemLp (fun y : ℝ ↦ h (n / y)) 2 μ)
    {L U : ℕ} (hLU : L ≤ U) (hs : ∀ n ∈ S, L ≤ n ∧ n ≤ U) :
    (∑ m ∈ Finset.range Q, (((m + 1 : ℕ) : ℝ) / (m + 1).totient) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ (m + 1))).filter (·.IsPrimitive),
        ∫ y : ℝ, ‖∑ n ∈ S, χ (n : ZMod (m + 1)) * (thetaMoebiusErrorCoefficient w n * h (n / y))‖ ^ 2 ∂μ) ≤
      ((Q : ℝ) ^ 2 + Real.pi * ((U : ℝ) - L)) * ∑ n ∈ S, ∫ y : ℝ, ‖thetaMoebiusErrorCoefficient w n * h (n / y)‖ ^ 2 ∂μ :=
  dirichletThetaRow_primitive_large_sieve_integral (f := fun n y ↦ thetaMoebiusErrorCoefficient w n * h (n / y)) Q hQ S
    (fun n hn ↦ (hh n hn).const_smul (thetaMoebiusErrorCoefficient w n)) hLU hs

end RiemannMasullo
