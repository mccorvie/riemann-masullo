module

public import RiemannMasullo.Ch13_ZerosHecke.QuadraticParityProducts
import RiemannMasullo.Ch13_ZerosHecke.QuadraticPrimeProducts
import RiemannMasullo.ForMathlib.NumberTheory.QuadraticJacobiMoments
import Mathlib.Data.Nat.GCD.BigOperators

/-! # Moments of the opposite quadratic parity for distinct auxiliary primes -/

@[expose] public noncomputable section

open Finset Filter NumberField

namespace RiemannMasullo

private theorem parity_logs {ε : ℝ} (hε : 0 < ε) :
    ∃ L > (0 : ℝ), ∀ x : ℝ, 1 ≤ x →
      Real.log (2*x^12) ≤ L*x^ε ∧ Real.log (2+x^4) ≤ L*x^ε := by
  refine ⟨3 + 12/ε, by positivity, ?_⟩
  intro x hx
  have hp : 0 < x := by linarith
  have hX := Real.one_le_rpow hx hε.le
  have hlog : Real.log x ≤ (1/ε)*x^ε := by
    simpa only [one_div, div_eq_inv_mul, mul_one] using Real.log_le_rpow_div hp.le hε
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))
  have h3 := Real.log_le_sub_one_of_pos (by norm_num : 0 < (3:ℝ))
  have hx4 : 1 ≤ x^4 := one_le_pow₀ hx
  have lh := Real.log_nonneg hx
  have Llog : 3 + 12*Real.log x ≤ (3+12/ε)*x^ε := by
    calc _ ≤ 3*x^ε + 12*((1/ε)*x^ε) := by nlinarith only [hlog,hX]
         _ = _ := by ring
  constructor
  · rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    exact (by nlinarith only [h2] : Real.log 2 + (12:ℝ)*Real.log x ≤ _).trans Llog
  · calc _ ≤ Real.log (3*x^4) := Real.log_le_log (by positivity) (by linarith)
         _ = Real.log 3 + 4*Real.log x := by rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
         _ ≤ _ := (by nlinarith only [h3,lh] : Real.log 3+4*Real.log x ≤ _).trans Llog

private theorem parity_scale (h : ℕ) (hh : 0 < h) {ε : ℝ}
    {C D L V : ℝ} (hC : 0 < C) (hD : 0 < D) (hL : 0 < L) (hV : 0 < V) :
    ∃ K > (0 : ℝ), ∀ (x n E Z : ℝ), 1 ≤ x → 0 ≤ n → 0 ≤ E →
      (x^12)^h ≤ V*n*(L*x^ε)^h → E ≤ D*x^12*x^ε →
      Z ≤ C*((2^h:ℝ)*(x^24)^h)^(ε/12)*((2^h+1)*(x^12)^h)*E^(3*h) →
      Z ≤ n*(K*x^(6+ε))^(6*h) := by
  let A := C*((2^h:ℝ)^(ε/12))*(2^h+1)*V*L^h*D^(3*h)
  have hA : 0 < A := by dsimp [A]; positivity
  let K := A^((6*h:ℕ):ℝ)⁻¹
  have hk : 0 < K := Real.rpow_pos_of_pos hA _
  refine ⟨K, hk, ?_⟩
  intro x n E Z hx hn hE hcount henergy hraw
  have hp : 0 < x := by linarith
  have hroot : K^(6*h) = A := Real.rpow_inv_natCast_pow hA.le (by positivity)
  have hlength : ((x^24)^h)^(ε/12) = ((x^ε)^h)^2 := by
    rw [← pow_mul, ← Real.rpow_natCast_mul hp.le, ← pow_mul, ← Real.rpow_mul_natCast hp.le]
    congr 1
    push_cast
    ring
  have hxpow : x^(6+ε) = x^6*x^ε := by rw [Real.rpow_add hp]; norm_cast
  calc Z ≤ _ := hraw
       _ = C*((2^h:ℝ)^(ε/12)*((x^ε)^h)^2)*((2^h+1)*(x^12)^h)*E^(3*h) := by
         rw [Real.mul_rpow (by positivity) (by positivity), hlength]
       _ ≤ C*((2^h:ℝ)^(ε/12)*((x^ε)^h)^2)*((2^h+1)*(V*n*(L*x^ε)^h))*(D*x^12*x^ε)^(3*h) := by gcongr
       _ = n*A*(x^6*x^ε)^(6*h) := by
         dsimp only [A]
         rw [Nat.mul_comm 3 h, Nat.mul_comm 6 h]
         simp only [pow_mul, mul_pow]
         ring_nf
       _ = _ := by rw [hxpow, ← hroot, mul_pow K]; ring


private theorem parity_product_rows (h Q : ℕ) (P U : Finset ℕ)
    (hp : ∀ q ∈ U, q.Prime) (hodd : ∀ q ∈ U, Odd q) (hQ : ∀ q ∈ U, q ≤ Q)
    (hc : ∀ q ∈ U, ∀ p ∈ P, q.Coprime p) (g : ℕ → ℝ) :
    ∃ V ⊆ oddSquarefreeLE (Q^h), (∀ m ∈ V, ∀ p ∈ P, m.Coprime p) ∧
      (∑ s ∈ U.powersetCard h, g (s.prod id)) = ∑ m ∈ V, g m := by
  let W := U.powersetCard h
  have fac (s : Finset ℕ) (hs : s ∈ W) : (s.prod id).primeFactors = s :=
    Nat.primeFactors_prod (fun p hp' ↦ hp p ((mem_powersetCard.mp hs).1 hp'))
  let V := W.image fun s ↦ s.prod id
  refine ⟨V, ?_, ?_, (sum_image (fun s hs t ht he ↦ (fac s hs).symm.trans
    ((congrArg Nat.primeFactors he).trans (fac t ht)))).symm⟩
  · rintro m hm
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hm
    obtain ⟨hsu, hsc⟩ := mem_powersetCard.mp hs
    have sq : Squarefree (s.prod id) := by
      have ht := Nat.squarefree_prod_primeFactors (s.prod id)
      change Squarefree (∏ q ∈ s, q)
      simpa only [fac s hs] using ht
    have ho : Odd (s.prod id) := prod_induction _ Odd (fun _ _ ↦ Odd.mul) odd_one
      (fun q hq ↦ hodd q (hsu hq))
    have bound : s.prod id ≤ Q^h := hsc ▸ prod_le_pow_card s id Q (fun q hq ↦ hQ q (hsu hq))
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.pos_of_ne_zero sq.ne_zero, bound⟩, ho, sq⟩
  · rintro m hm p hpin
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hm
    exact Nat.coprime_prod_left_iff.mpr fun q hq ↦ hc q ((mem_powersetCard.mp hs).1 hq) p hpin

local notation "parityPrimes(" J ")" =>
  (Nat.primesLE (2*(J:ℕ)^12) \ Nat.primesLE ((J:ℕ)^12))

/-- At a fourth-power cutoff, the single product twist on `h` distinct auxiliary
primes has normalized moment radius `K J^(6+ε)` at order `6h`. The constant depends
only on the field, `h`, and `ε`. The extra prime weights may be any real numbers
of modulus at most one. -/
theorem quadraticParityProduct_fourthPower_sample_moment
    (F : Type*) [Field F] [NumberField F] (h : ℕ) (hh : 0 < h) {ε : ℝ} (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ᶠ J : ℕ in atTop,
      ∀ (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (x : ℝ), x ≤ ((J^4 : ℕ) : ℝ) →
      ∀ u : ℕ → ℝ, (∀ p ∈ Nat.primesLE (J^4), |u p| ≤ 1) →
      ∑ s ∈ parityPrimes(J).powersetCard h, |degreeOnePrimeRieszSumWith χ (J^4) x
        (fun p ↦ u p * (jacobiSym (s.prod id : ℕ) p : ℝ))|^(6*h) ≤
          (parityPrimes(J).powersetCard h).card * (K*(J:ℝ)^(6+ε))^(6*h) := by
  let D : ℝ := Module.finrank ℚ F
  have hD : 0 < D := by dsimp [D]; exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F))
  obtain ⟨C, hC, hsieve⟩ := jacobiPrime_evenMoment (3*h) (ε/12) (by positivity)
  obtain ⟨L, hL, hlogs⟩ := parity_logs hε
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  let D' := D^2*L*Real.log 4
  let Vh := (4:ℝ)^h*h.factorial
  have hd : 0 < D' := by dsimp [D']; positivity
  have hv : 0 < Vh := by dsimp [Vh]; positivity
  obtain ⟨K, hK, hscale⟩ := parity_scale h hh (ε := ε) hC hd hL hv
  refine ⟨K, hK, ?_⟩
  filter_upwards [quadraticPrime_fourthPower_auxiliary_data,
    quadraticPrime_fourthPower_distinctProduct_count h] with J hgeo hsize
  intro χ x hx u hu
  let U := parityPrimes(J)
  let T := J^4
  let M := (2*J^12)^h
  let P := Nat.primesLE T
  let W := U.powersetCard h
  let b (p : ℕ) := (heckeLogDerivCoefficient (ideleClassNormTwist χ 0) p).re * max (x-p) 0 * u p
  let E := ∑ p ∈ P, b p^2
  let g (m : ℕ) := (∑ p ∈ P, b p * (jacobiSym m p : ℝ))^(2*(3*h))
  obtain ⟨hJ, _, hU, hcop, _, _⟩ := hgeo
  have hJ1 : 1 ≤ (J:ℝ) := by exact_mod_cast (show 1 ≤ J by omega)
  have hT : 0 < T := by dsimp [T]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have he : 0 ≤ E := sum_nonneg fun _ _ ↦ sq_nonneg _
  have hQ q (hq : q ∈ U) := Nat.mem_primesLE.mp (mem_sdiff.mp hq).1
  obtain ⟨V, hV, hc, heq⟩ := parity_product_rows h (2*J^12) P U
    (fun q hq ↦ (hQ q hq).2) (fun q hq ↦ (mem_filter.mp (hU hq)).2.1)
    (fun q hq ↦ (hQ q hq).1) hcop g
  have hraw := hsieve T M hT hM P V (fun _ hp ↦ hp) hV hc b
  change (∑ m ∈ V, g m) ≤ C*((M:ℝ)*(T:ℝ)^(3*h))^(ε/12)*((M:ℝ)+(T:ℝ)^(3*h))*E^(3*h) at hraw
  have ht : (T:ℝ)^(3*h) = ((J:ℝ)^12)^h := by
    rw [pow_mul]; dsimp only [T]; push_cast; congr 1; ring
  have hm : (M:ℝ) = (2:ℝ)^h*((J:ℝ)^12)^h := by dsimp only [M]; push_cast; rw [mul_pow]
  have hmn : (M:ℝ)*(T:ℝ)^(3*h) = (2:ℝ)^h*((J:ℝ)^24)^h := by
    rw [ht,hm,mul_assoc,←mul_pow]; congr 2; ring
  have hplus : (M:ℝ)+(T:ℝ)^(3*h) = (2^h+1)*((J:ℝ)^12)^h := by rw [ht,hm]; ring
  rw [hmn,hplus,←heq] at hraw
  have hlog := hlogs J hJ1
  have hcount : ((J:ℝ)^12)^h ≤ Vh*W.card*(L*(J:ℝ)^ε)^h := by
    apply hsize.2.trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ hJ1))) hlog.1 h)
      (by positivity)
  have henergy := quadraticPrime_hecke_energy χ T hx u hu
  change E ≤ D^2*(T:ℝ)^3*Real.log (2+T)*Real.log 4 at henergy
  have ht3 : (T:ℝ)^3 = (J:ℝ)^12 := by dsimp only [T]; push_cast; ring
  have henergy' : E ≤ D'*(J:ℝ)^12*(J:ℝ)^ε := by
    rw [ht3] at henergy
    apply henergy.trans
    calc _ ≤ D^2*(J:ℝ)^12*(L*(J:ℝ)^ε)*Real.log 4 := by
             apply mul_le_mul_of_nonneg_right _ hl4.le
             apply mul_le_mul_of_nonneg_left _ (by positivity)
             simpa only [T, Nat.cast_pow] using hlog.2
         _ = _ := by dsimp only [D']; ring
  have hb := hscale J W.card E (∑ s ∈ W, g (s.prod id)) hJ1 (Nat.cast_nonneg _) he hcount henergy' hraw
  calc _ = ∑ s ∈ W, g (s.prod id) := by
             apply sum_congr rfl
             intro s _
             rw [(show Even (6*h) from ⟨3*h, by omega⟩).pow_abs]
             simp only [g, b, P, T, degreeOnePrimeRieszSumWith, ←mul_assoc,
               show 6*h = 2*(3*h) by omega]
       _ ≤ _ := hb

/-- At all sufficiently large fourth-power cutoffs, one normalized cumulative moment
bound holds simultaneously for every Hecke character. The order is six times the number
of distinct auxiliary primes. -/
theorem quadraticParityProduct_fourthPower_moment
    (F : Type*) [Field F] [NumberField F] (h : ℕ) (hh : 0 < h) {ε : ℝ} (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ᶠ J : ℕ in atTop, ∀ χ : PontryaginDual (IdeleClassGroup (𝓞 F) F),
      QuadraticParityProductFourthPowerMoment χ J (6*h) (parityPrimes(J).powersetCard h)
        (K*(J:ℝ)^(7+ε)) := by
  obtain ⟨K, hK, hsample⟩ := quadraticParityProduct_fourthPower_sample_moment F h hh hε
  refine ⟨K, hK, ?_⟩
  filter_upwards [quadraticPrime_fourthPower_auxiliary_data, hsample] with J hgeom hs
  intro χ
  have hp : 0 < (J:ℝ) := by exact_mod_cast (show 0 < J by have := hgeom.1; omega)
  have he : K*(J:ℝ)^(7+ε) = J*(K*(J:ℝ)^(6+ε)) := by
    rw [show (7:ℝ)+ε = 1+(6+ε) by ring, Real.rpow_add hp, Real.rpow_one]
    ring
  rw [he]
  apply quadraticParityProductFourthPowerMoment_of_samples χ J (6*h) _ _ (by positivity)
  intro j hj
  have hx : (j:ℝ)^4 ≤ ((J^4:ℕ):ℝ) := by exact_mod_cast Nat.pow_le_pow_left (mem_Ioc.mp hj).2 4
  simpa only [one_mul] using hs χ ((j:ℝ)^4) hx (fun _ ↦ 1) (by simp)

/-- On the `h`-element subsets of the dyadic auxiliary primes, any positive fraction
with complete negative-parity deficit at most `H` controls the full prime deficit
at density cost `δ^(-1/(6h))`. The center is arbitrary at every fourth-power sample. -/
theorem quadraticParityPrimePower_fourthPower_deficit_moment
    (F : Type*) [Field F] [NumberField F] (h : ℕ) (hh : 0 < h) {ε : ℝ} (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ᶠ J : ℕ in atTop, ∀ (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
      (c : ℕ → ℝ) (G : Finset (Finset ℕ)), G ⊆ parityPrimes(J).powersetCard h →
      ∀ {δ H : ℝ}, 0 < δ → δ * ((parityPrimes(J).powersetCard h).card : ℝ) ≤ (G.card : ℝ) →
      (∀ s ∈ G, ∑ j ∈ Ioc 0 J, max (c j -
        quadraticParityPrimePowerRieszSum χ (J^4) ((j:ℝ)^4) (s.prod id)) 0 ≤ H) →
      ∑ j ∈ Ioc 0 J, max (c j - degreeOnePrimeRieszSumWith χ (J^4) ((j:ℝ)^4) 1) 0 ≤
        H + 4*(Module.finrank ℚ F : ℝ)*(Real.log 4+4)*(J:ℝ)^(19/3 : ℝ) +
          K*(J:ℝ)^(7+ε) * δ^(-((6*h:ℕ):ℝ)⁻¹) := by
  obtain ⟨K, hK, hm⟩ := quadraticParityProduct_fourthPower_moment F h hh hε
  refine ⟨K, hK, ?_⟩
  filter_upwards [hm, quadraticPrime_fourthPower_auxiliary_data,
    quadraticPrime_fourthPower_distinctProduct_count h] with J hM hg hs
  intro χ c G hG δ H hδ hd hH
  exact (hM χ).powersetCard_complete_deficit_transfer (by have := hg.1; omega)
    (by positivity) hs.1 (by positivity) c G hG hδ hd hg.2.2.2.1 hH

/-- For arbitrary ordered distinct dyadic auxiliary primes, a fraction `δ` of pairs
with bounded complete opposite-parity deficit gives loss `δ^(-1/12)`. Both the
density and the deficit hypothesis use the actual ordered population. -/
theorem quadraticParityPrimePower_fourthPower_ordered_pair_twelfth
    (F : Type*) [Field F] [NumberField F] {ε : ℝ} (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ᶠ J : ℕ in atTop, ∀ (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
      (c : ℕ → ℝ) (G : Finset (ℕ × ℕ)), G ⊆ parityPrimes(J).offDiag →
      ∀ {δ H : ℝ}, 0 < δ → δ * (parityPrimes(J).offDiag.card : ℝ) ≤ (G.card : ℝ) →
      (∀ w ∈ G, ∑ j ∈ Ioc 0 J, max (c j -
        quadraticParityPrimePowerRieszSum χ (J^4) ((j:ℝ)^4) (w.1*w.2)) 0 ≤ H) →
      ∑ j ∈ Ioc 0 J, max (c j - degreeOnePrimeRieszSumWith χ (J^4) ((j:ℝ)^4) 1) 0 ≤
        H + 4*(Module.finrank ℚ F : ℝ)*(Real.log 4+4)*(J:ℝ)^(19/3 : ℝ) +
          K*(J:ℝ)^(7+ε) * δ^(-(12:ℝ)⁻¹) := by
  obtain ⟨K, hK, hm⟩ := quadraticParityProduct_fourthPower_moment F 2 (by decide) hε
  refine ⟨K, hK, ?_⟩
  filter_upwards [hm, quadraticPrime_fourthPower_auxiliary_data,
    quadraticPrime_fourthPower_distinctProduct_count 2] with J hM hg hs
  intro χ c G hG δ H hδ hd hH
  have hmoment : QuadraticParityProductFourthPowerMoment χ J 12 (parityPrimes(J).powersetCard 2)
      (K*(J:ℝ)^(7+ε)) := hM χ
  simpa only [Nat.cast_ofNat] using hmoment.ordered_pair_complete_deficit_transfer
    (by have := hg.1; omega) (by decide) hs.1 (by positivity) c G hG hδ hd hg.2.2.2.1 hH

end RiemannMasullo
