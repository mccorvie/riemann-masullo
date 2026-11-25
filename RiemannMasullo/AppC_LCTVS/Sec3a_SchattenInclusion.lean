module

public import RiemannMasullo.AppC_LCTVS.Sec3a_part2

/-! # Trace-class operators are Hilbert–Schmidt

* `traceClassOperators_le_hilbertSchmidtOperators`: the Schatten class of index one lies in the
  Schatten class of index two (`S₁ ⊆ S₂`). The approximation numbers of a trace-class operator
  tend to zero, so their squares are eventually below them.
* `mem_hilbertSchmidtOperators_of_isNuclearOperator`: every nuclear Hilbert endomorphism is
  Hilbert–Schmidt.
-/

@[expose] public noncomputable section

open Filter Topology

namespace RiemannMasullo

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Every trace-class operator is Hilbert–Schmidt: the Schatten class of index one lies in the
Schatten class of index two. -/
theorem traceClassOperators_le_hilbertSchmidtOperators :
    traceClassOperators E F ≤ hilbertSchmidtOperators E F := by
  rintro T ⟨hT, hs⟩
  have hs' : Summable (approximationNumber T) := by simpa using hs
  have hnn (n : ℕ) : 0 ≤ approximationNumber T n :=
    Real.sInf_nonneg fun _ ⟨_, _, h⟩ ↦ h ▸ norm_nonneg _
  refine ⟨hT, Summable.of_norm_bounded_eventually_nat hs' ?_⟩
  filter_upwards [hs'.tendsto_atTop_zero.eventually (ge_mem_nhds zero_lt_one)] with n hn
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (hnn n) _)]
  exact Real.rpow_le_self_of_le_one (hnn n) hn one_le_two

/-- Every nuclear Hilbert endomorphism is Hilbert–Schmidt. -/
theorem mem_hilbertSchmidtOperators_of_isNuclearOperator {T : E →L[ℂ] E}
    (hT : IsNuclearOperator T) : T ∈ hilbertSchmidtOperators E E :=
  traceClassOperators_le_hilbertSchmidtOperators
    ((mem_traceClassOperators_iff_isNuclearOperator T).2 hT)

end RiemannMasullo
