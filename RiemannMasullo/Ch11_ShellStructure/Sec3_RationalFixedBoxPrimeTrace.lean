module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxFiniteTrace
public import RiemannMasullo.ForMathlib.Analysis.Distribution.PositivePrimeTrace

/-! # The von Mangoldt trace of actual finite rational theta levels -/

public noncomputable section
open Set
namespace RiemannMasullo.RationalPacket

private theorem positiveTest_prime_sum_of_support (f : PositiveTimeTest) (S₀ : Finset ℕ)
    (hS₀ : ∀ p ∈ S₀, p.Prime)
    (hz : ∀ p : ℕ, p.Prime → p ∉ S₀ →
      (Real.log (p : ℝ) : ℂ) * ∑' k : ℤ, f (Real.log p * k) = 0) :
    (∑' p : Nat.Primes, (Real.log (p : ℝ) : ℂ) * ∑' k : ℤ, f (Real.log p * k)) =
      ∑ p ∈ S₀, (Real.log (p : ℝ) : ℂ) * ∑' k : ℤ, f (Real.log p * k) := by
  classical
  let P₀ : Finset Nat.Primes := S₀.subtype Nat.Prime
  have ht : (∑' p : Nat.Primes, (Real.log (p : ℝ) : ℂ) * ∑' k : ℤ, f (Real.log p * k)) =
      ∑ p ∈ P₀, (Real.log (p : ℝ) : ℂ) * ∑' k : ℤ, f (Real.log p * k) :=
    tsum_eq_sum (s := P₀) (f := fun p : Nat.Primes ↦
    (Real.log (p : ℝ) : ℂ) * ∑' k : ℤ, f (Real.log p * k)) (fun p hp ↦
      hz p p.property (fun hmem ↦ hp (Finset.mem_subtype.mpr hmem)))
  apply ht.trans
  simpa only [P₀] using! Finset.sum_subtype_of_mem
    (fun p : ℕ ↦ (Real.log (p : ℝ) : ℂ) * ∑' k : ℤ, f (Real.log p * k)) hS₀

/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496. The stabilized trace of the
actual finite relative theta-level actions is the von Mangoldt prime-power sum.
Deviation: The rational trivial-angular unweighted model and compact positive-time
tests are used. This does not identify an infinite-level trace-class operator. -/
theorem fixedBoxFiniteTestAction_vonMangoldt_trace (f : PositiveTimeTest) :
    ∃ S₀ : Finset ℕ, (∀ p ∈ S₀, p.Prime) ∧
      ∀ (X : ℝ) (hX : 0 < X) (S : Finset ℕ) (hS1 : ∀ q ∈ S, 1 ≤ q)
        (hS : ∀ q ∈ S, q.Prime), S₀ ⊆ S →
        hilbertTrace ⟨fixedBoxFiniteTestAction (X := X) S hS1 f,
          fixedBoxFiniteTestAction_nuclear hX S hS1 hS f⟩ =
          ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * f (Real.log n) := by
  obtain ⟨S₀, hS₀, hz⟩ := positiveTest_prime_poisson_finite f
  refine ⟨S₀, hS₀, fun X hX S hS1 hS hsub ↦ ?_⟩
  rw [fixedBoxFiniteTestAction_poisson_trace hX S hS1 hS f,
    ← positiveTest_prime_poisson_eq_vonMangoldt f, positiveTest_prime_sum_of_support f S₀ hS₀ hz]
  exact (Finset.sum_subset hsub (fun p hp hp₀ ↦ hz p (hS p hp) hp₀)).symm

end RiemannMasullo.RationalPacket
