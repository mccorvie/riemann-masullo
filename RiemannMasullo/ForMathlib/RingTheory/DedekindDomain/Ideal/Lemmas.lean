module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Height-one primes dividing prime powers
-/

@[expose] public section

namespace RiemannMasullo

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- A height-one prime dividing a power of another height-one prime equals it. -/
theorem HeightOneSpectrum.eq_of_dvd_pow {v w : HeightOneSpectrum R} {k : ℕ}
    (h : w.asIdeal ∣ v.asIdeal ^ k) : w = v :=
  HeightOneSpectrum.asIdeal_injective <| associated_iff_eq.mp <|
    w.prime.associated_of_dvd v.prime (w.prime.dvd_of_dvd_pow h)

end RiemannMasullo
