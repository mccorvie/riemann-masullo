module

public import Mathlib.RingTheory.DedekindDomain.SInteger

/-!
# Expanding S-units at principal primes

For a finite set of principal height-one primes in a Dedekind domain, each S-unit
is an ordinary unit times a product of powers of the chosen prime generators.
The exponent is the usual additive order, the negative logarithm of the
multiplicative valuation.
-/

public section

namespace RiemannMasullo

open IsDedekindDomain
open scoped WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- A generator of a height-one prime ideal is nonzero. -/
theorem primeGenerator_ne_zero (v : HeightOneSpectrum R) (π : R)
    (hπ : v.asIdeal = Ideal.span {π}) : π ≠ 0 := by
  intro h
  exact v.ne_bot (by simpa [h] using hπ)

open scoped Classical in
/-- A principal prime generator has multiplicative valuation `exp (-1)` at its own
prime and valuation one at every other height-one prime. -/
theorem valuation_primeGenerator (w v : HeightOneSpectrum R) (π : R)
    (hπ : v.asIdeal = Ideal.span {π}) :
    w.valuation K (algebraMap R K π) = if w = v then WithZero.exp (-1 : ℤ) else 1 := by
  by_cases hw : w = v
  · subst w
    rw [ite_eq_left rfl, v.valuation_of_algebraMap]
    exact v.intValuation_singleton (primeGenerator_ne_zero v π hπ) hπ
  · rw [ite_eq_right hw, HeightOneSpectrum.valuation_eq_one_iff_notMem]
    intro h
    have hle : v.asIdeal ≤ w.asIdeal := hπ ▸ (Ideal.span_singleton_le_iff_mem _).2 h
    exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm)

open scoped Classical in
/-- The usual additive order of a prime generator is one at its own prime and zero elsewhere. -/
theorem neg_log_valuation_primeGenerator (w v : HeightOneSpectrum R) (π : R)
    (hπ : v.asIdeal = Ideal.span {π}) :
    -WithZero.log (w.valuation K (algebraMap R K π)) = if w = v then (1 : ℤ) else 0 := by
  rw [valuation_primeGenerator K w v π hπ]
  split <;> simp

/-- A chosen generator of a prime in `S` is the image of a unit of the ring of S-integers. -/
theorem exists_sUnit_coe_eq_primeGenerator (S : Set (HeightOneSpectrum R))
    (v : HeightOneSpectrum R) (hv : v ∈ S) (π : R) (hπ : v.asIdeal = Ideal.span {π}) :
    ∃ u : (S.integer K)ˣ, (u.val : K) = algebraMap R K π := by
  classical
  have hπ0 : algebraMap R K π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (primeGenerator_ne_zero v π hπ)
  let u : S.unit K := ⟨Units.mk0 _ hπ0, fun w hw ↦ by
    change w.valuation K (algebraMap R K π) = 1
    rw [valuation_primeGenerator K w v π hπ, ite_eq_right (fun e : w = v ↦ hw (e ▸ hv))]⟩
  exact ⟨S.unitEquivUnitsInteger K u, rfl⟩

open scoped Classical in
/-- The valuation of a product of integral powers of distinct principal prime generators
picks out exactly the exponent belonging to the given prime. -/
theorem valuation_prod_primeGenerator_zpow (S : Finset (HeightOneSpectrum R))
    (π : S → R) (hπ : ∀ v : S, v.val.asIdeal = Ideal.span {π v})
    (a : S → ℤ) (w : HeightOneSpectrum R) :
    w.valuation K (∏ v : S, algebraMap R K (π v) ^ a v) =
      if hw : w ∈ S then WithZero.exp (-a ⟨w, hw⟩) else 1 := by
  rw [map_prod]
  by_cases hw : w ∈ S
  · rw [dite_eq_left hw, Finset.prod_eq_single (⟨w, hw⟩ : S)]
    · rw [map_zpow₀, valuation_primeGenerator K w w _ (hπ ⟨w, hw⟩), ite_eq_left rfl,
        ← WithZero.exp_zsmul, zsmul_eq_mul, Int.cast_id, mul_neg, mul_one]
    · intro b _ hb
      have hwb : w ≠ b.val := fun e ↦ hb (Subtype.ext e.symm)
      rw [map_zpow₀, valuation_primeGenerator K w b.val _ (hπ b), ite_eq_right hwb, one_zpow]
    · simp
  · rw [dite_eq_right hw]
    apply Finset.prod_eq_one
    intro v _
    rw [map_zpow₀, valuation_primeGenerator K w v.val _ (hπ v),
      ite_eq_right (fun e : w = v.val ↦ hw (e ▸ v.property)), one_zpow]

private theorem exists_globalUnit_of_forall_valuation_eq_one (x : K) (hx : x ≠ 0)
    (hv : ∀ v : HeightOneSpectrum R, v.valuation K x = 1) :
    ∃ u : Rˣ, algebraMap R K (u : R) = x := by
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K x (fun v ↦ (hv v).le)
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K x⁻¹
    (fun v ↦ by rw [map_inv₀, hv, inv_one])
  have hab : a * b = 1 := IsFractionRing.injective R K (by
    rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ hx])
  exact ⟨⟨a, b, hab, (mul_comm b a).trans hab⟩, ha⟩

/-- If the primes in a finite set `S` have chosen generators, every S-unit is
a global unit times the product of those generators raised to its additive orders. -/
theorem sUnit_exists_eq_unit_mul_prod_primeGenerator_zpow (S : Finset (HeightOneSpectrum R))
    (π : S → R) (hπ : ∀ v : S, v.val.asIdeal = Ideal.span {π v})
    (x : ((S : Set (HeightOneSpectrum R)).integer K)ˣ) :
    ∃ u : Rˣ, (x.val : K) = algebraMap R K (u : R) *
      ∏ v : S, algebraMap R K (π v) ^ (-WithZero.log (v.val.valuation K (x.val : K))) := by
  classical
  let ord (v : S) := -WithZero.log (v.val.valuation K (x.val : K))
  let P := ∏ v : S, algebraMap R K (π v) ^ ord v
  have hx : (x.val : K) ≠ 0 := fun h ↦ x.ne_zero (Subtype.ext h)
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ ↦ zpow_ne_zero _
    ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (primeGenerator_ne_zero v.val _ (hπ v)))
  have hv (w : HeightOneSpectrum R) : w.valuation K P = w.valuation K (x.val : K) := by
    change w.valuation K (∏ v : S, algebraMap R K (π v) ^ ord v) = _
    rw [valuation_prod_primeGenerator_zpow K S π hπ ord w]
    by_cases hw : w ∈ S
    · rw [dite_eq_left hw]
      simpa only [ord, neg_neg] using WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx :
        w.valuation K (x.val : K) ≠ 0)
    · rw [dite_eq_right hw]
      exact (((S : Set (HeightOneSpectrum R)).unitEquivUnitsInteger K).symm x |>.property w hw).symm
  obtain ⟨u, hu⟩ := exists_globalUnit_of_forall_valuation_eq_one (R := R) K ((x.val : K) / P)
    (div_ne_zero hx hP) (fun w ↦ by rw [map_div₀, hv w, div_self ((Valuation.ne_zero_iff _).2 hx)])
  exact ⟨u, (div_eq_iff hP).1 hu.symm⟩

end RiemannMasullo
