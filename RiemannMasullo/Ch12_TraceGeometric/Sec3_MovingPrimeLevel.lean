module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_RadialPrimeTrace
import RiemannMasullo.Ch01_Introduction.Sec4
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! # Removing the first prime shell by a moving finite-place cutoff

For a positive-log profile supported in `[l,u]` with `u/2 < l`, the finite places
of norm at most `exp (u/2)` contain all contributing prime powers of exponent at
least two. The first prime shell is the entire difference between the two levels.
-/

@[expose] public noncomputable section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instFiniteCompletionUnitsLocallyCompactSec4b instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSIdeleLocallyCompactSec1 instSIdeleT2Sec4

local notation "Pl" => HeightOneSpectrum (𝓞 ℚ)
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "V" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "X" => (1 : PontryaginDual Cℚ)
local notation "q(" v ")" => ((v : Pl).asIdeal.absNorm : ℝ)
local notation "finPV(" v "," b ")" =>
  ((Real.log q(v) / ((finiteLocalMultiplicativeTamagawaMeasure ℚ v)
    (((v : Pl).adicCompletionIntegers ℚ).units : Set _)).toReal : ℝ) : ℂ) *
    finiteConnesWeilPrincipalValue v 1 b
local notation "radial(" φ ", " H ")" => ∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x =
  H (Real.log (((ideleClassNorm ℚ x).val : ℝ)))
local notation "lifts(" S ", " f ", " φ ")" => ∀ g : (SAdeleRing ℚ S)ˣ,
  HasSum (fun ξ : sProjectedDiagonal ℚ S ↦ (f : BruhatCompactSupport (SAdeleRing ℚ S)ˣ).val (ξ.val * g))
    ((φ : BruhatCompactSupport Cℚ).val (QuotientGroup.mk (sIdeleInsertion ℚ S g)))

/-- Finite places of norm at most the square root of the upper support bound. -/
def rationalPrimeLevel (u : ℝ) : Finset Pl :=
  ((Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le (S := 𝓞 ℚ) ⌈Real.exp (u/2)⌉₊).toFinset).filter
    (fun v ↦ Real.log q(v) ≤ u/2)

@[simp] theorem mem_rationalPrimeLevel (u : ℝ) (v : Pl) :
    v ∈ rationalPrimeLevel u ↔ Real.log q(v) ≤ u/2 := by
  rw [rationalPrimeLevel, Finset.mem_filter, and_iff_right_of_imp]
  intro h
  have hq : 0 < q(v) := by rw [rat_absNorm_eq_prime]; exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv v).property.pos
  have he := (Real.log_le_iff_le_exp hq).mp h
  simpa using (show v.asIdeal.absNorm ≤ ⌈Real.exp (u/2)⌉₊ by exact_mod_cast he.trans (Nat.le_ceil _))

/-- The exponent-one prime contribution, including its central square-root twist. -/
def rationalFirstPrimeSum (H : ℝ → ℂ) : ℂ :=
  ∑' p : Nat.Primes, ((Real.log (p.val : ℝ) / Real.sqrt p.val : ℝ) : ℂ) * H (Real.log p.val)

private theorem outside_prime_shell {l u : ℝ} (hl : 0 < l) (H : ℝ → ℂ)
    (hb : tsupport H ⊆ Icc l u) (v : Pl) (hv : v ∉ rationalPrimeLevel u)
    (b : BruhatCompactSupport (v.adicCompletion ℚ)ˣ)
    (hφ : ∀ x, b.val x = introTraceTest X (fun t ↦ H (Real.log t))
      (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v x)) :
    finPV(v,b) = ((Real.log q(v) / Real.sqrt q(v) : ℝ) : ℂ) * H (Real.log q(v)) := by
  have hq : 1 < q(v) := by rw [rat_absNorm_eq_prime]; exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv v).property.one_lt
  have hlog := Real.log_pos hq
  have hcut : u/2 < Real.log q(v) := lt_of_not_ge fun h ↦ hv ((mem_rationalPrimeLevel _ _).mpr h)
  have hlo {x : ℝ} (hx : x < l) : H x = 0 := by
    by_contra hn
    exact hx.not_ge (hb (subset_tsupport H hn)).1
  have hhi {x : ℝ} (hx : u < x) : H x = 0 := by
    by_contra hn
    exact hx.not_ge (hb (subset_tsupport H hn)).2
  rw [introTrace_finite_eq_tsum_primePower X (fun t ↦ H (Real.log t)) (by simpa using hlo hl) v b hφ,
    tsum_eq_single 0, introTracePrimePower_one_first, Real.log_inv, hlo (by linarith : -Real.log q(v) < l), add_zero]
  · have he : ((Real.sqrt q(v) : ℝ) : ℂ) = (q(v) : ℂ)^(1/2 : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by linarith : 0 ≤ q(v))]
      norm_num
    rw [← he, Complex.ofReal_div]
    ring
  · intro k hk
    have hmul : u < ((k+1 : ℕ) : ℝ) * Real.log q(v) := by
      have hn : (2 : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ k+1 by omega)
      linarith [mul_le_mul_of_nonneg_right hn hlog.le]
    have hneg : -(((k+1 : ℕ) : ℝ) * Real.log q(v)) < l := by
      have := mul_nonneg (Nat.cast_nonneg (α := ℝ) (k+1)) hlog.le
      linarith
    simp only [introTracePrimePower, Real.log_pow, Real.log_inv, hhi hmul, hlo hneg, mul_zero, add_zero, zero_div, ite_self]

private theorem rational_unramified (S : Finset Pl) (v : Pl) (h : differentIdeal ℤ (𝓞 ℚ) ≤ v.asIdeal) :
    v ∈ S := by
  have hd : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
    rw [← Ideal.absNorm_eq_one_iff, NumberField.absNorm_differentIdeal ℚ (𝓞 ℚ), NumberField.discr_rat]
    rfl
  exact False.elim (v.isPrime.ne_top (top_unique (hd ▸ h)))

private theorem split_prime_places {l u : ℝ} (hl : 0 < l) (hlu : u/2 < l)
    (H : ℝ → ℂ) (hb : tsupport H ⊆ Icc l u) (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, H))
    (b : ∀ v : Pl, BruhatCompactSupport (v.adicCompletion ℚ)ˣ)
    (bh : ∀ (v : Pl) x, (b v).val x = φ.val (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v x))
    (hs : Summable (fun v : Pl ↦ finPV(v, b v))) :
    (∑' v : Pl, finPV(v,b v)) =
      (∑ v : rationalPrimeLevel u, finPV(v.val, b v.val)) + rationalFirstPrimeSum H := by
  let S := rationalPrimeLevel u
  let term (v : Pl) := ((Real.log q(v) / Real.sqrt q(v) : ℝ) : ℂ) * H (Real.log q(v))
  have hin (v : S) : term v.val = 0 := by
    have hv := (mem_rationalPrimeLevel _ _).mp v.property
    have hz : H (Real.log q(v.val)) = 0 := by
      by_contra hn
      linarith [(hb (subset_tsupport H hn)).1]
    simp [term,hz]
  have hout (v : {v : Pl // v ∉ S}) : finPV(v.val,b v.val) = term v.val := by
    apply outside_prime_shell hl H hb v.val v.property (b v.val)
    intro x
    rw [bh, hφ]
    simp [introTraceTest]
  have he : (∑' v : Pl, term v) = rationalFirstPrimeSum H := by
    rw [rationalFirstPrimeSum, ← (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).tsum_eq]
    exact tsum_congr fun v ↦ by simp only [term, rat_absNorm_eq_prime]
  have hall : (∑' v : {v : Pl // v ∉ S}, term v.val) = ∑' v : Pl, term v := by
    apply tsum_subtype_eq_of_support_subset (s := {v : Pl | v ∉ S}) (f := term)
    intro v hv
    by_contra h
    exact hv (hin ⟨v, by simpa using h⟩)
  rw [← hs.sum_add_tsum_subtype_compl S, ← Finset.sum_coe_sort, ← he, ← hall]
  congr 1
  exact tsum_congr hout

section

variable {l u : ℝ}
local notation "Sᵤ" => rationalPrimeLevel u
local notation "Iₛ" => (SAdeleRing ℚ Sᵤ)ˣ
local notation "μₛ" => sMultiplicativeTamagawaMeasure ℚ Sᵤ
local notation "volS" => (((sLocalNormOneQuotientMeasure ℚ Sᵤ) univ).toReal : ℂ)
local notation "rootS(" g ")" => (Real.sqrt (((sIdeleNorm ℚ Sᵤ g).val : ℝ)) : ℂ)
local notation "P(" f ")" => ((∫ g : Iₛ, (f : BruhatCompactSupport Iₛ).val g * rootS(g) ∂μₛ) +
  ∫ g : Iₛ, (f : BruhatCompactSupport Iₛ).val g / rootS(g) ∂μₛ)

/-- For every positive-log radial window with `u/2 < l`, the sum of the full
explicit formula value and the corrected orbital mass at the square-root
cutoff tends to minus the first-prime sum. The periodization holds on the
actual finite-place ideles. Both Mellin poles are included in the mass. -/
theorem exists_primeLevel_signed_comparison (hl : 0 < l) (hlu : u/2 < l)
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hb : tsupport H ⊆ Icc l u) :
    ∃ (φ : BruhatCompactSupport Cℚ) (f : BruhatCompactSupport Iₛ), radial(φ,H) ∧ lifts(Sᵤ,f,φ) ∧
      Tendsto (fun R : ℝ ↦ V * centeredVonMangoldtValue H + rationalCorrectedSharpMass f R)
        atTop (𝓝 (-V * rationalFirstPrimeSum H)) := by
  have hk : HasCompactSupport H := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hb
  have hp : tsupport H ⊆ Ioi 0 := fun _ h ↦ hl.trans_le (hb h).1
  obtain ⟨φ,hφ⟩ := exists_normTest (F := ℚ) H hH hk
  have hPic := subsingleton_rational_sInteger_pic Sᵤ
  have hOutside := rationalNormTest_outside_invariant (S := Sᵤ) H φ hφ
  obtain ⟨f,hf⟩ := exists_sLocalTraceLift hPic φ hOutside
  refine ⟨φ,f,hφ,hf,?_⟩
  have h0 : H 0 = 0 := by
    by_contra hn
    exact (lt_irrefl (0 : ℝ)) (hp (subset_tsupport H hn))
  have hφ₁ : φ.val 1 = 0 := by simpa [hφ] using h0
  let π : IdeleGroup (𝓞 ℚ) ℚ →ₜ* Cℚ := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ := π.comp ⟨canonicalIdeleNormSection ℚ, canonicalIdeleNormSection_continuous ℚ⟩
  have hτ : RightInverse τ (ideleClassNorm ℚ) := canonicalIdeleNormSection_rightInverse ℚ
  obtain ⟨A,b,hA,hb',hSum,hZ⟩ := traceFormula_of_half_le τ hτ φ (le_refl (1 / 2 : ℝ))
  have hz := hZ.unique (hasSum_rationalNormTest_fullTrace H hH hk hp φ hφ τ hτ)
  obtain ⟨A',b',J,hA',hb'',hJ,hj⟩ := sLocalTraceSharpMass_asymptotic φ hPic
    (rational_unramified Sᵤ) hOutside f hf
  have hArch : A' = A := funext fun w ↦ Subtype.ext (funext fun x ↦ (hA' w x).trans (hA w x).symm)
  subst A'
  have hsplit := split_prime_places hl hlu H hb φ hφ b hb' hSum
  have hfin (v : Sᵤ) : b v.val = b' v := Subtype.ext (funext fun x ↦ (hb' _ x).trans (hb'' v x).symm)
  simp_rw [hfin] at hsplit
  rw [hsplit] at hz
  have hPol := sLocalTraceLift_global_polar_sum hPic φ hOutside f hf
  have hvol : (volS : ℂ) ≠ 0 := by
    let G := (sIdeleQuotientNorm ℚ Sᵤ).ker
    let : CompactSpace G := isCompact_iff_compactSpace.mp
      ((isProperMap_sIdeleQuotientNorm ℚ Sᵤ).isCompact_preimage (isCompact_singleton (x := 1)))
    let μ := sLocalNormOneQuotientMeasure ℚ Sᵤ
    have : μ.IsHaarMeasure := (sLocalNormOneQuotientMeasure_normProduct (F := ℚ) (S := Sᵤ)).1
    exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr
      ⟨isOpen_univ.measure_ne_zero μ univ_nonempty, measure_ne_top μ univ⟩)
  simp only [hφ₁,mul_zero,zero_mul,sub_zero] at hj
  have hlim := hj.congr' (hJ.mono fun R h ↦ h.tsum_eq.symm)
  have h := ((hlim.sub_const P(f)).const_mul (V/volS)).const_add (V * centeredVonMangoldtValue H)
  have he : -V * rationalFirstPrimeSum H =
      V * centeredVonMangoldtValue H + V/volS * (volS *
        ((∑ w : InfinitePlace ℚ, infiniteConnesWeilPrincipalValue w (A w)) +
          ∑ v : Sᵤ, finPV(v.val,b' v)) - P(f)) := by
    field_simp [hvol]
    linear_combination hPol + volS * hz
  rw [he]
  exact h

end
end RiemannMasullo
