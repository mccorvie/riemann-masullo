module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_PrimitiveDirichletFormula
import Mathlib.Tactic

/-! # The signed prime formula for one rational congruence cylinder

At finite conductor the polar correction has the exact principal-character
weight. Sufficiently large prime moduli isolate the prescribed integer for a
fixed compact profile, with zero error on the arithmetic side.
-/

@[expose] public noncomputable section

open Classical Filter Function MeasureTheory Set NumberField
open scoped ComplexConjugate ContDiff NumberField.AdeleRing Topology

namespace RiemannMasullo.ConductorCylinder

open ConductorDensity RationalConductor

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Zstrip" => {z : ℂ // 0 < z.re ∧ z.re < 1}
local notation "G(" a ", " H ")" => shiftedProfile a H

/-- The completed primitive zero sum at a real Mellin shift includes the
principal polar moments and the primitive prime and parity terms. -/
theorem hasSum_shifted_primitive_positiveLog {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a : ℝ)
    (H : ℝ → ℂ) (hd : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0) :
    HasSum (fun z : Zstrip ↦ (completedPrimitiveOrder (χ, z) : ℂ) * bilateralLaplace H (z.val - a))
      ((if χ = 1 then bilateralLaplace H (-a) + bilateralLaplace H (1-a) else 0) +
        primeAndArchRow G(a, H) (archTerm 0 G(a, H)) (archTerm 1 G(a, H)) χ) := by
  have hG : ContDiff ℝ (∞) G(a, H) := (Complex.ofRealCLM.contDiff.comp
    (show ContDiff ℝ (∞) (fun x : ℝ ↦ Real.exp (-a*x)) by fun_prop)).mul hd
  simpa only [bilateralLaplace_shiftedProfile, zero_sub] using
    hasSum_primitiveDirichlet_positiveLog χ G(a, H) hG hc.mul_left (tsupport_mul_subset_right.trans hp)

private theorem principal_average (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (P : ℂ) :
    cylinderAverage q r (fun χ ↦ if χ = 1 then P else 0) = P / q.totient := by
  change (∑ χ : DirichletCharacter ℂ q, conj (χ (r : ZMod q)) * (if χ = 1 then P else 0)) / _ = _
  simp [mul_ite]

/-- Paper: §12.3, p. 514. Finite-conductor explicit formula for the full
positive divisor on a single physical cylinder, with both polar Mellin
terms retained. The coefficients in the finite-place term use the primitive
Euler factors at every prime, including primes dividing the modulus. -/
theorem physicalFull_eq_poles_add_primeAndArchRow (q : ℕ) [NeZero q] (r : (ZMod q)ˣ)
    (a : ℝ) (H : ℝ → ℂ) (hd : ContDiff ℝ (∞) H) (hc : HasCompactSupport H)
    (hp : tsupport H ⊆ Ioi 0) (φ : BruhatCompactSupport Cℚ) (hφ : IsNormalizedCylinder q r H φ) :
    physicalWidthSum q φ a (fun _ _ m ↦ (m : ℂ)) =
      (bilateralLaplace H (-a) + bilateralLaplace H (1-a)) / q.totient +
      cylinderAverage q r (primeAndArchRow G(a, H) (archTerm 0 G(a, H)) (archTerm 1 G(a, H))) := by
  rw [physicalWidthSum_eq q r H hd.continuous φ hφ _ _ (by simp)]
  simp_rw [(hasSum_shifted_primitive_positiveLog _ a H hd hc hp).tsum_eq]
  rw [← principal_average q r, ← map_add]
  rfl

private theorem prime_modulus_sum {G : ℝ → ℂ} (hc : HasCompactSupport G) {b : ℕ} (hb : 2 ≤ b) :
    ∃ L : ℕ, ∀ {q : ℕ} [NeZero q], q.Prime → L ≤ q → ∀ (hbq : b.Coprime q) (A B : ℂ),
      cylinderAverage q (ZMod.unitOfCoprime b hbq) (primeAndArchRow G A B) = -primeSample G b := by
  obtain ⟨N, hN⟩ := (finite_primeSample hc).bddAbove
  refine ⟨max (b+2) (N+1), ?_⟩
  intro q _ hq hL hbq A B
  have hb' : b+1 < q := by omega
  have hr : (b : ZMod q) ≠ 1 := by
    intro h
    have he := (ZMod.natCast_eq_natCast_iff' b 1 q).mp (by simpa using h)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at he
    omega
  have hr' : (b : ZMod q) ≠ -1 := by
    intro h
    have he : ((b+1 : ℕ) : ZMod q) = 0 := by push_cast; rw [h]; ring
    exact (Nat.not_le.mpr hb') (Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff _ _).mp he))
  rw [cylinderAverage_primeAndArchRow _ hc, ZMod.coe_unitOfCoprime, ite_eq_right hr,
    ite_eq_right hr', add_zero, sub_zero, tsum_eq_single b]
  · simp [primeWeight_of_coprime hbq]
  intro n hn
  by_cases hz : primeSample G n = 0
  · simp [hz]
  have hnq : n < q := by have := hN hz; omega
  have hnp : 0 < n := Nat.pos_of_ne_zero (fun h ↦ hz (by simp [h, primeSample]))
  have hcop := (hq.coprime_iff_not_dvd.mpr (fun h ↦ hnq.not_ge (Nat.le_of_dvd hnp h))).symm
  have hneq : (b : ZMod q) ≠ (n : ZMod q) := by
    intro h
    have he := (ZMod.natCast_eq_natCast_iff' b n q).mp h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hnq] at he
    exact hn he.symm
  simp [primeWeight_of_coprime hcop, hneq]

/-- Paper: §12.3, p. 514. An unshrunk compact radial profile at every sufficiently
large prime modulus isolates exactly the selected von Mangoldt sample. The two
moments survive with coefficient 1/φ(q). The identity holds at each such modulus. -/
theorem physicalFull_eq_prime_sample {b : ℕ} (hb : 2 ≤ b) (a : ℝ) (H : ℝ → ℂ)
    (hd : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0) :
    ∃ L : ℕ, ∀ {q : ℕ} [NeZero q], q.Prime → L ≤ q → ∀ (hbq : b.Coprime q)
      (φ : BruhatCompactSupport Cℚ), IsNormalizedCylinder q (ZMod.unitOfCoprime b hbq) H φ →
      physicalWidthSum q φ a (fun _ _ m ↦ (m : ℂ)) =
        (bilateralLaplace H (-a) + bilateralLaplace H (1-a)) / q.totient -
          (((b : ℝ)^(-a) : ℝ) : ℂ) * primeSample H b := by
  obtain ⟨L, hL⟩ := prime_modulus_sum (G := G(a, H)) hc.mul_left hb
  refine ⟨L, ?_⟩
  intro q _ hq hqL hbq φ hφ
  rw [physicalFull_eq_poles_add_primeAndArchRow q _ a H hd hc hp φ hφ,
    hL hq hqL]
  change _ + -primeSample (fun x ↦ (Real.exp (-a*x):ℂ)*H x) b = _
  rw [primeSample_shift H a (by omega)]
  rfl

local notation "ord(" i ")" => completedPrimitiveOrder i
local notation "ret(" a ", " s ", " i ")" => spectralStripMultiplicity a s
  ((i).2.val.re - 1/2) (ord(i))
local notation "miss(" a ", " s ", " i ")" => (ord(i) - ret(a,s,i) : ℕ)
local notation "sample(" H ", " z ")" => bilateralLaplace H ((z : Zstrip).val - 1/2)

private theorem retained_bound (a s x : ℝ) (n : ℕ) : spectralStripMultiplicity a s x n ≤ n := by
  unfold spectralStripMultiplicity spectralBoundaryMultiplicity
  split_ifs <;> first | exact le_rfl | exact min_le_left _ _ | exact Nat.zero_le _

/-- The signed finite-conductor gap is the angular Fourier average of the actual
missing primitive jets. Neither polar moment needs to vanish. -/
theorem physicalFull_sub_retained (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (a s : ℝ)
    (H : ℝ → ℂ) (hd : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0)
    (φ : BruhatCompactSupport Cℚ) (hφ : IsNormalizedCylinder q r H φ) :
    physicalWidthSum q φ (1/2) (fun _ _ m ↦ (m : ℂ)) - physicalCenteredRetained q φ a s =
      cylinderAverage q r (fun χ ↦ ∑' z : Zstrip, (miss(a,s,(χ,z)) : ℂ) * sample(H,z)) := by
  rw [physicalWidthSum_eq q r H hd.continuous φ hφ _ _ (by simp),
    physicalCenteredRetained_eq q r H hd.continuous φ hφ, ← map_sub]
  congr 1
  funext χ
  have hfull := (hasSum_shifted_primitive_positiveLog χ (1/2) H hd hc hp).summable
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hfull ⊢
  have hkeep : Summable (fun z : Zstrip ↦ (ret(a,s,(χ,z)) : ℂ) * sample(H,z)) := by
    apply hfull.norm.of_norm_bounded
    intro z
    rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    gcongr
    exact retained_bound ..
  simp only [Pi.sub_apply, centeredRetainedRow, divisorRow, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  change (∑' z : Zstrip, (ord((χ,z)) : ℂ) * sample(H,z)) -
      (∑' z : Zstrip, (ret(a,s,(χ,z)) : ℂ) * sample(H,z)) = _
  rw [← hfull.tsum_sub hkeep]
  apply tsum_congr fun z ↦ ?_
  rw [Nat.cast_sub (retained_bound ..), sub_mul]

/-- Assuming the single-modulus Montgomery product count, the signed full-to-strip
error of every normalized residue cylinder has power saving in the modulus,
uniformly in the residue, strip width above the specified threshold, and order.
The test may have arbitrary polar terms. -/
theorem norm_physicalFull_sub_retained_le {σ C ε : ℝ} (hσ : 1/2 < σ) (hσ1 : σ < 1)
    (hC : 0 ≤ C) (hn : MontgomeryProductCount σ (montgomeryExponent σ) C) (hε : 0 < ε)
    (H : ℝ → ℂ) (hd : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (a s : ℝ), σ-1/2 ≤ a →
      ∀ (φ : BruhatCompactSupport Cℚ), IsNormalizedCylinder q r H φ →
        ‖physicalWidthSum q φ (1/2) (fun _ _ m ↦ (m : ℂ)) - physicalCenteredRetained q φ a s‖ ≤
          B * (q:ℝ)^(-(1-montgomeryExponent σ)+ε) := by
  obtain ⟨B,hB,hbound⟩ := normalized_omitted_mass hσ hσ1 hC hn.to_count
    (hd.of_le (by simp)) hc |(1/2 : ℝ)| hε
  refine ⟨B,hB,fun q _ r a s ha φ hφ ↦ ?_⟩
  let w (i : Site q) : ℝ := miss(a,s,i)
  have hm (i : Site q) : w i ≤ ord(i) := by
    change ((miss(a,s,i) : ℕ) : ℝ) ≤ _
    exact_mod_cast Nat.sub_le _ _
  have hw (i : Site q) (h : w i ≠ 0) : σ ≤ i.2.val.re ∨ i.2.val.re ≤ 1-σ := by
    by_contra! he
    have hmid : i.2.val.re-1/2 ∈ Ioo (-a) a := ⟨by linarith [he.2], by linarith [he.1]⟩
    exact h (by simp only [w, spectralStripMultiplicity_interior hmid, Nat.sub_self, Nat.cast_zero])
  obtain ⟨hsum,hcount⟩ := hbound q (1/2) le_rfl w (fun i ↦ Nat.cast_nonneg _) hm hw
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hsum hcount
  let v (i : Site q) := w i * ‖sample(H,i.2)‖
  have hnon (i : Site q) : 0 ≤ v i := mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hsrow := ((summable_prod_of_nonneg hnon).mp (show Summable v from hsum)).1
  rw [physicalFull_sub_retained q r a s H hd hc hp φ hφ]
  apply (norm_cylinderAverage_le _ _).trans
  apply le_trans _ hcount
  rw [show (∑' i : Site q, w i * ‖sample(H,i.2)‖) = ∑ χ, ∑' z, v (χ,z) by
    rw [show (fun i : Site q ↦ w i * ‖sample(H,i.2)‖) = v from rfl, hsum.tsum_prod' hsrow, tsum_fintype]]
  apply div_le_div_of_nonneg_right (Finset.sum_le_sum fun χ _ ↦ ?_) (Nat.cast_nonneg _)
  have he (z : Zstrip) : ‖(miss(a,s,(χ,z)) : ℂ) * sample(H,z)‖ = v (χ,z) := by
    simp only [norm_mul, Complex.norm_natCast, v, w]
  exact (norm_tsum_le_tsum_norm ((hsrow χ).congr (fun z ↦ (he z).symm))).trans_eq (tsum_congr he)

end RiemannMasullo.ConductorCylinder
