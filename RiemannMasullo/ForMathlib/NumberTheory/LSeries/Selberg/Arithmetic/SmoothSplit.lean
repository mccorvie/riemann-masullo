module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

private theorem smooth_dvd_left {r d a b : ℕ} (hd : smooth r d) (hb : r.Coprime b)
    (h : d ∣ a * b) : d ∣ a := by
  apply Nat.Coprime.dvd_of_dvd_mul_right _ h
  refine Nat.coprime_of_dvd fun p hp hpd ↦ hp.coprime_iff_not_dvd.mp ?_
  exact hb.of_dvd_left (Nat.dvd_of_mem_primeFactors (Nat.mem_factoredNumbers'.mp hd p hp hpd))

/-- Card 3. Every positive integer factors uniquely into a part supported on the primes dividing r
and a part coprime to r, for r > 0.
Titchmarsh, §10.11, p. 271, supported and coprime parts. -/
theorem smooth_split (r n : ℕ) (hr : 0 < r) (hn : 0 < n) :
    ∃! de : ℕ × ℕ, smooth r de.1 ∧ Nat.Coprime r de.2 ∧ de.1*de.2=n := by
  let d := (n.primeFactorsList.filter (· ∈ r.primeFactors)).prod
  let e := (n.primeFactorsList.filter (· ∉ r.primeFactors)).prod
  have hd : smooth r d := Nat.prod_mem_factoredNumbers _ _
  have he : r.Coprime e := by
    refine Nat.coprime_list_prod_right_iff.mpr fun p hp ↦ ?_
    obtain ⟨hpn, hpr⟩ := List.mem_filter.mp hp
    have hprime := Nat.prime_of_mem_primeFactorsList hpn
    exact (hprime.coprime_iff_not_dvd.mpr fun h ↦
      (of_decide_eq_true hpr) (hprime.mem_primeFactors h hr.ne')).symm
  have hde : d * e = n := by
    have h := (List.filter_append_perm (· ∈ r.primeFactors) n.primeFactorsList).prod_eq
    simpa only [d, e, decide_not, List.prod_append, Nat.prod_primeFactorsList hn.ne'] using h
  refine ⟨(d, e), ⟨hd, he, hde⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
  have hprod : a * b = d * e := hab.trans hde.symm
  have had : a = d := Nat.dvd_antisymm
    (smooth_dvd_left ha he (hprod ▸ Nat.dvd_mul_right a b))
    (smooth_dvd_left hd hb (hprod.symm ▸ Nat.dvd_mul_right d e))
  exact Prod.ext had (Nat.mul_left_cancel (Nat.pos_of_ne_zero hd.1) (had ▸ hprod))

end RiemannMasullo.Selberg
