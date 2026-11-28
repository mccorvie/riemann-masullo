module

public import RiemannMasullo.ForMathlib.NumberTheory.BinomialZeta
public import RiemannMasullo.ForMathlib.Analysis.Analytic.ZeroLatticeCertified

/-!
# Finite binomial magnitudes on the critical-line lattice

On the mesh of spacing `1/n²` the last comparison uses one node beyond `n`.
The uniform binomial zeta approximation on `[-n-1,n+1]` covers this successor.
-/

public noncomputable section

open Complex
open RiemannMasullo.AnalyticLattice

namespace RiemannMasullo

local notation "line(" t ")" => ((1 / 2 : ℂ) + ((t : ℝ) : ℂ) * I)

/-- Magnitude of the finite binomial approximation at an integer mesh index. -/
@[expose] def binomialZetaLatticeMagnitude (n : ℕ) (k : ℤ) : ℝ :=
  ‖binomialZetaApprox (3 * (n + 1)) line(samplePoint n k)‖

/-- The entries can be evaluated using rational weights and phases at positive integers. -/
theorem binomialZetaLatticeMagnitude_eq_phases (n : ℕ) (k : ℤ) :
    let t := (k : ℝ) / (n : ℝ)^2
    let M := 3 * (n + 1)
    binomialZetaLatticeMagnitude n k =
      ‖(∑ j ∈ Finset.range M, (-1 : ℂ)^j * (binomialZetaWeight M (j+1) : ℂ) *
        Complex.exp (-((t * Real.log (j+1 : ℝ) : ℝ) : ℂ) * I) / (√(j+1 : ℝ) : ℂ)) /
        (1 - (√2 : ℂ) * Complex.exp (-((t * Real.log 2 : ℝ) : ℂ) * I))‖ := by
  dsimp only
  rw [binomialZetaLatticeMagnitude, samplePoint_eq_div, binomialZetaApprox_critical_eq_phases]

/-- All binomial magnitudes needed by a positive mesh have error at most `2⁻ⁿ`,
including the right successor. -/
theorem binomialZetaLatticeMagnitude_accurate :
    AccurateMagnitudes (fun t : ℝ ↦ riemannZeta line(t)) binomialZetaLatticeMagnitude := by
  apply accurateMagnitudes_iff.mpr
  intro n hn k hk
  obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hk
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by positivity
  have hl' : -(n : ℝ)^3 ≤ (k : ℝ) := by exact_mod_cast hl
  have hu' : (k : ℝ) ≤ (n : ℝ)^3+1 := by exact_mod_cast hu
  have hs : 1 ≤ (n : ℝ)^2 := one_le_pow₀ hn₁
  have hh : |samplePoint n k| ≤ (n : ℝ)+1 := by
    rw [samplePoint_eq_div, abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))]
    apply (div_le_iff₀ (sq_pos_of_pos hn₀)).mpr
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have h := (norm_binomialZetaApprox_sub_riemannZeta_lt_dyadic n hh).le
  rw [sampleError_eq_pow, show (1 / 2 : ℝ)^n = (2^n : ℝ)⁻¹ by rw [one_div, inv_pow]]
  exact (abs_norm_sub_norm_le _ _).trans h

/-- The conservative finite weighted sum on the binomial table. -/
@[expose] def binomialZetaLatticeSum (g : ℝ → ℝ) (n : ℕ) : ℝ :=
  certifiedSum binomialZetaLatticeMagnitude g n

/-- Integer nodes and the finite binomial magnitudes determine every comparison. -/
theorem binomialZetaLatticeSum_eq_sum (g : ℝ → ℝ) (n : ℕ) :
    binomialZetaLatticeSum g n =
      (∑ k ∈ (Finset.Icc (-(n : ℤ)^3) ((n : ℤ)^3)).filter (fun k : ℤ ↦
        ((n : ℝ)+1) * (binomialZetaLatticeMagnitude n k + (1 / 2 : ℝ)^n) <
        n * max 0 (binomialZetaLatticeMagnitude n (k+1) - (1 / 2 : ℝ)^n)),
        g ((k : ℝ) / (n : ℝ)^2)) / n := by
  classical
  rw [binomialZetaLatticeSum, certifiedSum_eq_sum]
  simp only [samplePoint_eq_div, sampleError_eq_pow]

/-- For a nonnegative test every finite conservative sum is bounded by the finite
sum obtained by the strict comparison of the true consecutive zeta magnitudes. -/
theorem binomialZetaLatticeSum_le_sampleSum {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t)
    {n : ℕ} (hn : 0 < n) :
    binomialZetaLatticeSum g n ≤ sampleSum (fun t : ℝ ↦ riemannZeta line(t)) g n :=
  certifiedSum_le binomialZetaLatticeMagnitude_accurate hg hn

end RiemannMasullo
