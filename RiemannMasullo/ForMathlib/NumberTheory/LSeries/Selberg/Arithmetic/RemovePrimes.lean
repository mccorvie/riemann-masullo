module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.SmoothSplit

public section

open Classical

namespace RiemannMasullo.Selberg

private theorem coprime_of_smooth {r d e : ℕ} (hd : smooth r d) (he : r.Coprime e) :
    d.Coprime e := by
  refine Nat.coprime_of_dvd fun p hp hpd ↦ hp.coprime_iff_not_dvd.mp ?_
  exact he.of_dvd_left (Nat.dvd_of_mem_primeFactors (Nat.mem_factoredNumbers'.mp hd p hp hpd))

/-- Card 5. For r and n positive, restricting the half-Möbius coefficients to integers coprime to
r is Dirichlet convolution with the r-supported positive half-zeta coefficients.
Replacement for Euler factors in Titchmarsh (10.12.2), p. 272. -/
theorem remove_primes (r n : ℕ) (hr : 0 < r) (hn : 0 < n) :
    (if Nat.Coprime r n then alpha n else 0) =
      ∑ d ∈ n.divisors.filter (smooth r), posHalf d * alpha (n/d) := by
  classical
  obtain ⟨⟨s, e⟩, hs, he, hprod⟩ := (smooth_split r n hr hn).exists
  change s * e = n at hprod
  have hsn : s ∣ n := hprod ▸ Nat.dvd_mul_right s e
  have hdiv : n.divisors.filter (smooth r) = s.divisors := by
    ext d
    rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdn, _⟩, hd⟩
      exact ⟨(coprime_of_smooth hd he).dvd_of_dvd_mul_right (hprod ▸ hdn), hs.1⟩
    · rintro ⟨hds, _⟩
      exact ⟨⟨hds.trans hsn, hn.ne'⟩, Nat.mem_factoredNumbers_of_dvd hs hds⟩
  have hcop : r.Coprime n ↔ s = 1 := by
    constructor
    · intro h
      simpa using coprime_of_smooth hs (h.of_dvd_right hsn)
    · rintro rfl
      simpa [← hprod] using he
  have hinv := DFunLike.congr_fun spectralLineJet_selbergHalfZeta_spec.2.2 s
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun d k ↦ spectralLineJet_selbergHalfZeta d * spectralLineJet_selbergHalfMoebius k),
    ArithmeticFunction.one_apply] at hinv
  rw [hdiv]
  symm
  calc
    _ = ∑ d ∈ s.divisors, (posHalf d * alpha (s / d)) * alpha e := by
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      have hds := (Nat.mem_divisors.mp hd).1
      have hquot : n / d = (s / d) * e := by
        rw [← hprod, Nat.mul_comm s e, Nat.mul_div_assoc e hds, Nat.mul_comm]
      have hce := (coprime_of_smooth hs he).of_dvd_left (Nat.div_dvd_of_dvd hds)
      rw [hquot, show alpha (s / d * e) = alpha (s / d) * alpha e from
        spectralLineJet_selbergHalfMoebius_mult.map_mul_of_coprime hce, mul_assoc]
    _ = (if s = 1 then 1 else 0) * alpha e := by
      rw [← Finset.sum_mul]
      exact congrArg (· * alpha e) hinv
    _ = _ := by
      simp only [hcop]
      split_ifs with h
      · simpa [h] using congrArg alpha hprod
      · simp

end RiemannMasullo.Selberg
