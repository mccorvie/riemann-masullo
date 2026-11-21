module

public import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.Finiteness.Basic

public section

open Function

namespace RiemannMasullo

/-- If an algebra projection admits an additive section compatible with multiplication,
the trace of a lifted element projects to its trace in the quotient algebra.
The images of a finite basis of the original algebra span the quotient. -/
theorem trace_of_algebra_projection
    {R A K B ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Field K] [CommRing B] [Algebra K B] [Fintype ι]
    (b : Module.Basis ι R A) (p : R →+* K) (hp : Surjective p)
    (q : A →+* B) (s : B →+ A) (hqs : ∀ z, q (s z) = z)
    (hq : ∀ r, q (algebraMap R A r) = algebraMap K B (p r))
    (hs : ∀ a z, s (q a * z) = a * s z) :
    Module.Finite K B ∧ ∀ x, p (Algebra.trace R A (s x)) = Algebra.trace K B x := by
  classical
  let c (i : ι) : B →ₗ[K] K :=
    { toFun := fun z ↦ p (b.repr (s z) i)
      map_add' := fun z w ↦ by simp
      map_smul' := fun k z ↦ by
        obtain ⟨r, rfl⟩ := hp k
        change p (b.repr (s (p r • z)) i) = p r * p (b.repr (s z) i)
        rw [Algebra.smul_def]
        rw [← hq, hs, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul] }
  have hsum (z : B) : ∑ i, c i z • q (b i) = z := by
    have h := congrArg q (b.sum_repr (s z))
    change ∑ i, p (b.repr (s z) i) • q (b i) = z
    simpa only [hqs, map_sum, Algebra.smul_def, map_mul, hq] using h
  let f : A →ₛₗ[p] B :=
    { toFun := q
      map_add' := map_add q
      map_smul' := fun r z ↦ by simp only [Algebra.smul_def, map_mul, hq] }
  let : RingHomSurjective p := ⟨hp⟩
  let : Module.Finite R A := Module.Finite.of_basis b
  have hfinite : Module.Finite K B := Module.Finite.of_surjective f fun z ↦ ⟨s z, hqs z⟩
  refine ⟨hfinite, fun x ↦ ?_⟩
  have hm : Algebra.lmul K B x =
      ∑ i, (c i).smulRight (x * q (b i)) := by
    ext z
    change x * z = (∑ i, (c i).smulRight (x * q (b i))) z
    simp only [ LinearMap.sum_apply,
      LinearMap.smulRight_apply, ← mul_smul_comm, ← Finset.mul_sum, hsum]
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace, map_sum, Algebra.trace_apply]
  rw [hm, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.trace_smulRight, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  change p (b.repr (s x * b i) i) = p (b.repr (s (x * q (b i))) i)
  rw [mul_comm x, hs, mul_comm (s x)]

end RiemannMasullo
