module

public import RiemannMasullo.ForMathlib.Analysis.Analytic.ZeroLatticeCertifiedLimit

/-! Eventual finite enclosures suffice for the asymptotic conservative lattice. -/

public noncomputable section

open Filter Topology

namespace RiemannMasullo.AnalyticLattice

/-- At every sufficiently large mesh the data cover the full finite table, including its
last successor. -/
@[expose] def EventuallyAccurateMagnitudes (f : ℝ → ℂ) (A : ℕ → ℤ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ k ∈ Finset.Icc (-(n : ℤ)^3) ((n : ℤ)^3+1),
    |A n k - ‖f (samplePoint n k)‖| ≤ sampleError n

/-- The full table, including the right endpoint's successor, lies in the height window
on which an arithmetic uniform approximation is needed. -/
theorem abs_samplePoint_le_succ {n : ℕ} (hn : 0 < n) {k : ℤ}
    (hk : k ∈ Finset.Icc (-(n : ℤ)^3) ((n : ℤ)^3+1)) :
    |samplePoint n k| ≤ (n : ℝ)+1 := by
  obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hk
  have hl' : -(n : ℝ)^3 ≤ k := by exact_mod_cast hl
  have hu' : (k : ℝ) ≤ (n : ℝ)^3+1 := by exact_mod_cast hu
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (1 : ℝ) ≤ (n : ℝ)^2 := one_le_pow₀ hn'
  rw [samplePoint_eq_div, abs_div, abs_of_pos (by positivity : 0 < (n : ℝ)^2)]
  apply (div_le_iff₀ (by positivity)).mpr
  rw [abs_le]
  constructor <;> nlinarith

/-- Modify only finitely many rows to obtain an everywhere-accurate table. The repaired
rows are auxiliary to the proof; the observed sequence keeps every original row. -/
theorem EventuallyAccurateMagnitudes.exists_accurate {f : ℝ → ℂ} {A : ℕ → ℤ → ℝ}
    (h : EventuallyAccurateMagnitudes f A) :
    ∃ B : ℕ → ℤ → ℝ, AccurateMagnitudes f B ∧ B =ᶠ[atTop] A := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  let B (n : ℕ) (k : ℤ) := if N ≤ n then A n k else ‖f (samplePoint n k)‖
  refine ⟨B,?_,(eventually_ge_atTop N).mono fun n hn ↦ funext fun k ↦ by simp [B,hn]⟩
  apply accurateMagnitudes_iff.mpr
  intro n hn k hk
  by_cases hLate : N ≤ n
  · simpa [B,hLate] using hN n hLate k hk
  · simp [B,hLate,sampleError_eq_pow]

/-- If the exact nonnegative sums have the stated whole-axis limit and compact limits,
the conservative sums have that limit for any eventually enclosed table. -/
theorem tendsto_certifiedSum_of_eventuallyAccurate {ι : Type*} {f : ℝ → ℂ} {A : ℕ → ℤ → ℝ}
    (h : EventuallyAccurateMagnitudes f A) (hf : ∀ t, AnalyticAt ℝ f t)
    (hmf : ∀ t, analyticOrderAt f t ≠ ⊤) (q m : ι → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hc : ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
      Tendsto (sampleSum f g) atTop (𝓝 (∑' i, m i * g (q i))))
    {g : ℝ → ℝ} (hg : Continuous g) (hgn : ∀ t, 0 ≤ g t)
    (he : Tendsto (sampleSum f g) atTop (𝓝 (∑' i, m i * g (q i)))) :
    (∀ᶠ n : ℕ in atTop, certifiedSum A g n ≤ sampleSum f g n) ∧
    Tendsto (certifiedSum A g) atTop (𝓝 (∑' i, m i * g (q i))) := by
  obtain ⟨B,hB,hBA⟩ := h.exists_accurate
  have hS : certifiedSum B g =ᶠ[atTop] certifiedSum A g := by
    filter_upwards [hBA] with n hn
    rw [certifiedSum_eq_sum,certifiedSum_eq_sum]
    simp only [hn]
  constructor
  · filter_upwards [hS,eventually_gt_atTop (0 : ℕ)] with n hEq hn
    exact hEq ▸ certifiedSum_le hB hgn hn
  · exact (tendsto_certifiedSum_nonnegative_of_exact hB hf hmf q m hm hc hg hgn he).congr' hS

end RiemannMasullo.AnalyticLattice
