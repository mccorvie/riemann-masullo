module

public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# Multiplicativity of Gaussian ideal norm counts

For coprime natural numbers `m` and `n`, multiplication is a bijection from
pairs of ideals of norms `m` and `n` to ideals of norm `m * n`. The argument works
for any Dedekind domain finite free over the integers.
-/

public noncomputable section

namespace RiemannMasullo

private theorem idealNorm_relPrime {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I J : Ideal R} (h : I.absNorm.Coprime J.absNorm) : IsRelPrime I J := by
  intro D hI hJ
  apply Ideal.isUnit_iff.mpr (Ideal.absNorm_eq_one_iff.mp (Nat.eq_one_of_dvd_one ?_))
  simpa only [h.gcd_eq_one] using Nat.dvd_gcd (map_dvd Ideal.absNorm hI) (map_dvd Ideal.absNorm hJ)

private theorem idealNorm_factor_unique {R : Type*} [CommRing R] [IsDedekindDomain R]
    {I J K L : Ideal R} (hprod : I * J = K * L)
    (hIL : I.absNorm.Coprime L.absNorm) (hKJ : K.absNorm.Coprime J.absNorm) : I = K := by
  apply le_antisymm
  · apply Ideal.le_of_dvd ((idealNorm_relPrime hKJ).dvd_of_dvd_mul_right ?_)
    rw [hprod]
    exact dvd_mul_right _ _
  · apply Ideal.le_of_dvd ((idealNorm_relPrime hIL).dvd_of_dvd_mul_right ?_)
    rw [← hprod]
    exact dvd_mul_right _ _

private theorem norm_factor_of_coprime {a b m n k : ℕ} (h : m.Coprime n)
    (hab : a * b = m * n) (ha : a ∣ m^k) (hb : b ∣ n^k) : a = m := by
  apply Nat.dvd_antisymm
  · apply ((h.pow_left k).of_dvd_left ha).dvd_of_dvd_mul_right
    rw [← hab]
    exact dvd_mul_right _ _
  · apply ((h.pow_right k).of_dvd_right hb).dvd_of_dvd_mul_right
    rw [hab]
    exact dvd_mul_right _ _

/-- For a Dedekind domain finite free over the integers, the ideal counts at coprime norms
multiply. Each ideal of product norm occurs once as the product of two ideals of the
prescribed norms. -/
theorem idealNorm_card_mul_of_coprime (R : Type*) [CommRing R] [IsDedekindDomain R]
    [Module.Finite ℤ R] [Module.Free ℤ R] {m n : ℕ} (h : m.Coprime n) :
    Nat.card {I : Ideal R // I.absNorm = m * n} =
      Nat.card {I : Ideal R // I.absNorm = m} * Nat.card {I : Ideal R // I.absNorm = n} := by
  let F (x : {I : Ideal R // I.absNorm = m} × {J : Ideal R // J.absNorm = n}) :
      {K : Ideal R // K.absNorm = m * n} := ⟨x.1.1 * x.2.1, by rw [map_mul, x.1.2, x.2.2]⟩
  have hi : Function.Injective F := by
    rintro ⟨⟨I, hI⟩, ⟨J, hJ⟩⟩ ⟨⟨K, hK⟩, ⟨L, hL⟩⟩ heq
    have hab : I * J = K * L := congrArg Subtype.val heq
    apply Prod.ext
    · exact Subtype.ext (idealNorm_factor_unique hab (by rwa [hI, hL]) (by rwa [hK, hJ]))
    · exact Subtype.ext (idealNorm_factor_unique ((mul_comm J I).trans (hab.trans (mul_comm K L)))
        (by simpa only [hJ, hK] using h.symm) (by simpa only [hL, hI] using h.symm))
  have hs : Function.Surjective F := by
    rintro ⟨I, hI⟩
    have hspan : I ∣ (Ideal.span {(m : R)}) * (Ideal.span {(n : R)}) := by
      rw [Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul, ← hI]
      exact Ideal.dvd_iff_le.mpr (Ideal.span_singleton_absNorm_le I)
    obtain ⟨K, L, hK, hL, hKL⟩ := exists_dvd_and_dvd_of_dvd_mul hspan
    have hprod : K.absNorm * L.absNorm = m * n := by rw [← map_mul, ← hKL, hI]
    have hKm : K.absNorm ∣ m ^ Module.finrank ℤ R := by
      simpa only [Ideal.absNorm_span_natCast] using map_dvd Ideal.absNorm hK
    have hLn : L.absNorm ∣ n ^ Module.finrank ℤ R := by
      simpa only [Ideal.absNorm_span_natCast] using map_dvd Ideal.absNorm hL
    have hprod' : L.absNorm * K.absNorm = n * m := by simpa only [mul_comm] using hprod
    exact ⟨(⟨K, norm_factor_of_coprime h hprod hKm hLn⟩,
      ⟨L, norm_factor_of_coprime h.symm hprod' hLn hKm⟩), Subtype.ext hKL.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective F ⟨hi, hs⟩).symm).trans (Nat.card_prod _ _)

/-- Gaussian ideal norm counts multiply at coprime arguments. -/
theorem gaussianIdealNorm_card_mul_of_coprime {m n : ℕ} (h : m.Coprime n) :
    Nat.card {I : Ideal GaussianInt // I.absNorm = m * n} =
      Nat.card {I : Ideal GaussianInt // I.absNorm = m} *
        Nat.card {I : Ideal GaussianInt // I.absNorm = n} := by
  let e : GaussianInt ≃+ ℤ × ℤ :=
    { toFun := fun z ↦ (z.re, z.im), invFun := fun x ↦ ⟨x.1, x.2⟩
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl, map_add' := fun _ _ ↦ rfl }
  let b := (Module.Basis.finTwoProd ℤ).map e.toIntLinearEquiv.symm
  let : Module.Free ℤ GaussianInt := Module.Free.of_basis b
  let : Module.Finite ℤ GaussianInt := Module.Finite.of_basis b
  exact idealNorm_card_mul_of_coprime GaussianInt h

end RiemannMasullo
