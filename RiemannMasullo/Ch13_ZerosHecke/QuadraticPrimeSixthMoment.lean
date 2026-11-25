module

public import RiemannMasullo.Ch13_ZerosHecke.QuadraticPrimeCellMoments
import RiemannMasullo.ForMathlib.NumberTheory.QuadraticLargeSieve

/-! # The sixth moment of the actual Hecke sums in quadratic sign classes -/

@[expose] public noncomputable section

open Finset Filter NumberField

namespace RiemannMasullo

private theorem sixthMoment_calibrate {n B E R C X Z : ℝ} (hn : 0 ≤ n) (hnB : n ≤ B)
    (hB : 0 < B) (hE : 0 ≤ E) (hC : 0 ≤ C) (hX : 1 ≤ X) (hbase : B*E ≤ n*R^2)
    (hraw : Z ≤ 32*(C*X*B*(15*E^3) + n*E^3)) :
    Z ≤ 32*(1+15*C)*X*n*R^6 := by
  have he : E ≤ R^2 := le_of_mul_le_mul_left (hbase.trans
    (mul_le_mul_of_nonneg_right hnB (sq_nonneg _))) hB
  have h1 : B*E^3 ≤ n*R^6 := by
    calc B*E^3 = (B*E)*E^2 := by ring
         _ ≤ (n*R^2)*(R^2)^2 :=
           mul_le_mul hbase (pow_le_pow_left₀ hE he 2) (sq_nonneg _) (by positivity)
         _ = _ := by ring
  have hn1 : n*E^3 ≤ X*(n*R^6) := by
    calc n*E^3 ≤ n*(R^2)^3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hE he 3) hn
         _ = 1*(n*R^6) := by ring
         _ ≤ X*(n*R^6) := mul_le_mul_of_nonneg_right hX (by positivity)
  calc Z ≤ _ := hraw
       _ = 32*((15*C*X)*(B*E^3)+n*E^3) := by ring
       _ ≤ 32*((15*C*X)*(n*R^6)+X*(n*R^6)) := by gcongr
       _ = _ := by ring

private theorem sixthMoment_absorb {ε : ℝ} (hε : 0 < ε) {C D : ℝ} (hC : 0 < C) (hD : 0 < D) :
    ∃ K > (0:ℝ), ∀ x : ℝ, 1 ≤ x →
      C * (2 * x^24)^(ε/8) * (100*D*x^6*Real.log (2+x))^6 ≤ (K*x^(6+ε))^6 := by
  let e := ε/2
  let θ := ε/8
  have he : 0 < e := by dsimp [e]; positivity
  have ht : 0 < θ := by dsimp [θ]; positivity
  let A := C*2^θ
  let L := (3:ℝ)^e/e
  have hA : 0 < A := by dsimp [A]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  let R := A^(1/(6:ℝ))
  have hR : 0 < R := Real.rpow_pos_of_pos hA _
  refine ⟨R*(100*D)*L, by positivity, ?_⟩
  intro x hx
  have xp : 0 < x := by linarith
  have hlog : Real.log (2+x) ≤ L*x^e := by
    calc _ ≤ (2+x)^e/e := Real.log_le_rpow_div (by linarith) he
         _ ≤ (3*x)^e/e := by gcongr; linarith
         _ = L*x^e := by rw [Real.mul_rpow (by norm_num) xp.le]; dsimp [L]; ring
  have hpow : (x^24)^θ = (x^(4*θ))^6 := by
    rw [← Real.rpow_natCast_mul xp.le, ← Real.rpow_mul_natCast xp.le]
    norm_num
    ring_nf
  have hr6 : R^6 = A := by
    rw [show R = A^(1/(6:ℝ)) from rfl, ← Real.rpow_mul_natCast hA.le]
    norm_num
  have hxexp : x^6 * x^(4*θ) * x^e = x^(6+ε) := by
    rw [← Real.rpow_natCast (x := x) (n := 6), ← Real.rpow_add xp, ← Real.rpow_add xp]
    congr 1
    dsimp [e,θ]
    ring
  calc _ = A*(x^(4*θ))^6 * (100*D*x^6*Real.log (2+x))^6 := by
             rw [show ε/8 = θ from rfl, Real.mul_rpow (by norm_num) (by positivity), hpow]
             dsimp only [A]
             ring
       _ = (R*(x^(4*θ))*(100*D*x^6*Real.log (2+x)))^6 := by rw [← hr6]; ring
       _ ≤ (R*(x^(4*θ))*(100*D*x^6*(L*x^e)))^6 := by
         have hlog0 : 0 ≤ Real.log (2+x) := Real.log_nonneg (by linarith)
         apply pow_le_pow_left₀ (by positivity)
         exact mul_le_mul_of_nonneg_left
           (mul_le_mul_of_nonneg_left hlog (by positivity)) (by positivity)
       _ = _ := by rw [← hxexp]; ring

/-- With bounded extra prime weights, the genuine Hecke Riesz sum at every real cutoff
through `J^4` has normalized sixth-moment radius `K J^(6+ε)` on the dyadic auxiliary
primes. The constant is uniform in the Hecke character and in the extra weights. -/
theorem quadraticPrimeTwist_fourthPower_hecke_sixthMoment (F : Type*) [Field F] [NumberField F]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ᶠ J : ℕ in atTop,
      let U := Nat.primesLE (2*J^12) \ Nat.primesLE (J^12)
      ∀ (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (x : ℝ), x ≤ ((J^4 : ℕ) : ℝ) →
      ∀ u : ℕ → ℝ, (∀ p ∈ Nat.primesLE (J^4), |u p| ≤ 1) →
      ∑ q ∈ U, |degreeOnePrimeRieszSumWith χ (J^4) x (fun p ↦ u p * (jacobiSym q p : ℝ))|^6 ≤
        U.card * (K*(J:ℝ)^(6+ε))^6 := by
  let D : ℝ := Module.finrank ℚ F
  have hD : 0 < D := by dsimp [D]; exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F))
  obtain ⟨C, hC, hsieve⟩ := jacobiPrime_sixthMoment (ε/8) (by positivity)
  obtain ⟨K, hK, hscale⟩ := sixthMoment_absorb hε (show 0 < 32*(1+15*C) by positivity) hD
  refine ⟨K, hK, ?_⟩
  filter_upwards [quadraticPrime_fourthPower_auxiliary_data] with J hgeom
  intro U χ x hx u hu
  obtain ⟨hJ, _, hU, hcop, hcard, hcount⟩ := hgeom
  let T := J^4
  let M := 2*J^12
  let P := Nat.primesLE T
  let b (p : ℕ) := (heckeLogDerivCoefficient (ideleClassNormTwist χ 0) p).re * max (x-p) 0 * u p
  let E := ∑ p ∈ P, b p ^ 2
  let B := (M:ℝ) + (T:ℝ)^3
  let R := 100*D*(J:ℝ)^6*Real.log (2+J)
  have hJ1 : 1 ≤ (J : ℝ) := by exact_mod_cast (show 1 ≤ J by omega)
  have hj : 0 < (J : ℝ) := by linarith
  have hEs : 0 ≤ E := sum_nonneg fun _ _ ↦ sq_nonneg _
  have hM : 0 < M := by dsimp [M]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hcardB : (U.card:ℝ) ≤ B := by
    have hm : (U.card:ℝ) ≤ M := by exact_mod_cast hcard
    exact hm.trans (le_add_of_nonneg_right (by positivity))
  have hE := quadraticPrime_hecke_energy χ T hx u hu
  change E ≤ D^2*T^3*Real.log (2+T)*Real.log 4 at hE
  have hbase : B*E ≤ U.card*R^2 := by
    have hb := quadraticPrime_fourthPower_secondMoment_bound
      (show (2:ℝ) ≤ J by exact_mod_cast hJ) (Nat.cast_nonneg U.card) hD.le hcount
    have hmono : B ≤ 2*(J:ℝ)^12 + 1 + ((J:ℝ)^4)^3 := by dsimp [B,M,T]; push_cast; linarith
    apply (mul_le_mul hmono hE hEs (by positivity)).trans
    simpa only [T, Nat.cast_pow, R] using hb
  have hs := hsieve T M hT hM P U (fun _ h ↦ h) hU hcop b
  let Y := ((M:ℝ)*(T:ℝ)^3)^(ε/8)
  have hY : 1 ≤ Y := by
    apply Real.one_le_rpow
    exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hM)
      (one_le_pow₀ (show (1 : ℝ) ≤ T by exact_mod_cast hT))
    positivity
  have hyEq : Y = (2*(J:ℝ)^24)^(ε/8) := by dsimp [Y,M,T]; push_cast; congr 1; ring
  change ∑ q ∈ U, (∑ p ∈ P, b p * (jacobiSym q p : ℝ))^6 ≤
    32*(C*Y*B*(15*E^3)+U.card*E^3) at hs
  have ht := sixthMoment_calibrate (Nat.cast_nonneg U.card) hcardB hB hEs hC.le hY hbase hs
  calc _ = ∑ q ∈ U, (∑ p ∈ P, b p * (jacobiSym q p : ℝ))^6 := by
             apply sum_congr rfl
             intro q _
             simp only [degreeOnePrimeRieszSumWith, P, T, b, ←mul_assoc,
               (by decide : Even 6).pow_abs]
       _ ≤ _ := ht
       _ = U.card * (32*(1+15*C)*(2*(J:ℝ)^24)^(ε/8)*R^6) := by rw [hyEq]; ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (hscale J hJ1) (Nat.cast_nonneg _)

/-- For every number field and ε>0, one constant controls the cumulative sixth moment
at all sufficiently large cutoffs, simultaneously for every unitary Hecke character and
every choice of a sign cell at each pair and sample. -/
theorem quadraticPrimeCell_fourthPower_sixthMoment (F : Type*) [Field F] [NumberField F]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K > (0:ℝ), ∀ᶠ J : ℕ in atTop, ∀ χ : PontryaginDual (IdeleClassGroup (𝓞 F) F),
      QuadraticPrimeCellFourthPowerMoment χ J 6 (K*(J:ℝ)^(7+ε)) := by
  obtain ⟨K, hK, h⟩ := quadraticPrimeTwist_fourthPower_hecke_sixthMoment F hε
  refine ⟨3*K, by positivity, ?_⟩
  filter_upwards [quadraticPrime_fourthPower_auxiliary_data, h] with J hg hm
  obtain ⟨hJ, _, _, hc, _, _⟩ := hg
  intro χ
  have hr : 0 ≤ K*(J:ℝ)^(6+ε) := by positivity
  have hbound := quadraticPrimeCellFourthPowerMoment_of_oneTwist χ (by omega : 1 ≤ J) hc
    (by decide : 0 < 6) hr (hm χ)
  have hp : 0 < (J:ℝ) := by exact_mod_cast (show 0 < J by omega)
  have he : (J:ℝ)^(7+ε)=(J:ℝ)*(J:ℝ)^(6+ε) := by
    rw [show (7:ℝ)+ε = 1+(6+ε) by ring, Real.rpow_add hp, Real.rpow_one]
  convert hbound using 1
  rw [he]
  ring

/-- If complete negative cells have cumulative deficit at most `H` on a fraction `δ` of
the auxiliary prime pairs, the unrestricted prime deficit satisfies both moment bounds.
The selected cell may vary with the pair and sample. -/
theorem quadraticPrimePowerCell_fourthPower_deficit_second_sixth
    {F : Type*} [Field F] [NumberField F] (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ᶠ J : ℕ in atTop,
      let U := Nat.primesLE (2*J^12) \ Nat.primesLE (J^12)
      ∀ (c : ℕ → ℝ) (e f : ℕ → ℕ → ℕ → ℝ),
      (∀ q d j, |e q d j| = 1) → (∀ q d j, |f q d j| = 1) →
      ∀ G : Finset (ℕ × ℕ), G ⊆ U ×ˢ U → ∀ δ H : ℝ, 0 < δ → δ*(U.card:ℝ)^2 ≤ G.card →
      (∀ w ∈ G, ∀ j ∈ Ioc 0 J, e w.1 w.2 j = -1 ∨ f w.1 w.2 j = -1) →
      (∀ w ∈ G, ∑ j ∈ Ioc 0 J, max (c j - quadraticPrimePowerCellRieszSum χ (J^4) ((j:ℝ)^4)
        w.1 w.2 (e w.1 w.2 j) (f w.1 w.2 j)) 0 ≤ H) →
      ∑ j ∈ Ioc 0 J, max (c j - degreeOnePrimeRieszSumWith χ (J^4) ((j:ℝ)^4) 1) 0 ≤
        H + 8*(Module.finrank ℚ F : ℝ)*(Real.log 4+4)*(J:ℝ)^(19/3:ℝ) +
        min (300*(Module.finrank ℚ F : ℝ)*(J:ℝ)^7*Real.log (2+J)*δ^(-(2:ℝ)⁻¹))
          (K*(J:ℝ)^(7+ε)*δ^(-(6:ℝ)⁻¹)) := by
  obtain ⟨K,hK,h6⟩ := quadraticPrimeCell_fourthPower_sixthMoment F hε
  refine ⟨K,hK,?_⟩
  filter_upwards [quadraticPrime_fourthPower_auxiliary_data,
    quadraticPrimeCell_fourthPower_secondMoment χ, h6] with J hg h2 h6J
  intro U c e f he hf G hG δ H hδ hdensity hneg hgood
  obtain ⟨hJ, hU, _, _, _, _⟩ := hg
  have hj : 1 ≤ J := by omega
  have hlog : 0 ≤ Real.log (2+(J:ℝ)) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) J])
  have h₂ := h2.complete_deficit_transfer hU hj (by decide) (by positivity)
    c e f he hf G hG hδ hdensity hneg hgood
  have h₆ := (h6J χ).complete_deficit_transfer hU hj (by decide) (by positivity)
    c e f he hf G hG hδ hdensity hneg hgood
  rw [add_min]
  exact le_min h₂ h₆

end RiemannMasullo
