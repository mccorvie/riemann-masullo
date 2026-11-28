module

public import RiemannMasullo.ForMathlib.Analysis.Distribution.PositiveTests
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.NuclearRetraction

/-! # Nuclearity through triangular forward-action extensions

Positive-time convolution factorization controls off-diagonal blocks in a finite tower.
-/

public noncomputable section
namespace RiemannMasullo
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem nuclear_two_block_product (A B P Q R : H →L[ℂ] H)
    (hPQ : P + Q = R) (hAR : A.comp R = A)
    (hAP : IsNuclearOperator (A.comp P)) (hQB : IsNuclearOperator (Q.comp B)) :
    IsNuclearOperator (A.comp B) := by
  have he : A.comp B = (A.comp P).comp B + A.comp (Q.comp B) := by
    calc
      _ = (A.comp R).comp B := by rw [hAR]
      _ = (A.comp (P + Q)).comp B := by rw [hPQ]
      _ = _ := by simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
        ContinuousLinearMap.comp_assoc]
  rw [he]
  apply (nuclearEndomorphisms H).add_mem
  · exact mul_mem_nuclearEndomorphisms_right B ⟨A.comp P, hAP⟩
  · exact mul_mem_nuclearEndomorphisms_left A ⟨Q.comp B, hQB⟩

/-- Nuclearity of positive-time test actions passes through a triangular
extension. Factorization controls the off-diagonal block as well as the diagonal. -/
theorem nuclear_positiveTest_extension (A : PositiveTimeTest → H →L[ℂ] H)
    (hadd : ∀ f g, A (f + g) = A f + A g)
    (hconv : ∀ f g, A (positiveTestConvolution f g) = (A f).comp (A g))
    (P Q R : H →L[ℂ] H) (hPQ : P + Q = R)
    (hright : ∀ f, (A f).comp R = A f)
    (hdeep : ∀ f, IsNuclearOperator ((A f).comp P))
    (hshallow : ∀ f, IsNuclearOperator (Q.comp (A f))) (f : PositiveTimeTest) :
    IsNuclearOperator (A f) := by
  obtain ⟨u, v, r, s, hf⟩ := exists_positiveTest_factorization f
  rw [hf, hadd, hconv, hconv]
  exact (nuclearEndomorphisms H).add_mem
    (nuclear_two_block_product (A u) (A v) P Q R hPQ (hright u) (hdeep u) (hshallow v))
    (nuclear_two_block_product (A r) (A s) P Q R hPQ (hright r) (hdeep r) (hshallow s))

end RiemannMasullo
