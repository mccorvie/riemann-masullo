module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_LevelPolarComplement
import RiemannMasullo.Ch10_TraceSpectral.Sec4a

/-! # Compression of the trace of a right-supported operator -/

public noncomputable section

namespace RiemannMasullo

/-- A nuclear operator fixed by a right compression has the same trace as
its two-sided compression. -/
theorem hilbertTrace_nuclearCompress_eq_of_right_mul
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : H →L[ℂ] H) (C : nuclearEndomorphisms H) (hRight : C.val * P = C.val) :
    hilbertTrace (Isolated.nuclearCompress P C) = hilbertTrace C := by
  let left : nuclearEndomorphisms H := ⟨P * C.val, mul_mem_nuclearEndomorphisms_left P C⟩
  let right : nuclearEndomorphisms H := ⟨C.val * P, mul_mem_nuclearEndomorphisms_right P C⟩
  have hCompressed : Isolated.nuclearCompress P C = left := by
    apply Subtype.ext
    change P * C.val * P = P * C.val
    rw [mul_assoc, hRight]
  have hFixed : right = C := Subtype.ext hRight
  rw [hCompressed, ← hFixed]
  exact spectralRestriction_cyclic P C

end RiemannMasullo
