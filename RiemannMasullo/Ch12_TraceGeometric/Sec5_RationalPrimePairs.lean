module

public import RiemannMasullo.Ch01_Introduction.Sec4_TranslatedFirstPrimes
public import Mathlib.Data.Nat.Dist
import RiemannMasullo.AppB_AnalyticNT.Sec6
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.Floor

/-! # Ordered pairs in the rational principal first-prime sum

The two primes use the same translated logarithmic window `[2,4]`. The near sum
includes the diagonal and the pairs at the cutoff. Its complementary sum is signed.
An integer count gives subcritical Abel vanishing without a prime distribution estimate.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open scoped BigOperators

/-- For the trivial character over the rationals, the degree-one sum has the ordinary
prime coefficient `log p / √p` on the original translated cutoff. -/
theorem firstPrimeDegreeOneSum_trivial_rat (H : ℝ → ℂ) (y b : ℝ) :
    firstPrimeDegreeOneSum (F := ℚ) 1 H y b =
      ∑ p ∈ Finset.Ioc 0 ⌊Real.exp (y + b)⌋₊ with p.Prime,
        ((Real.log (p : ℝ) / Real.sqrt (p : ℝ) : ℝ) : ℂ) * H (Real.log (p : ℝ) - y) := by
  classical
  unfold firstPrimeDegreeOneSum
  apply Finset.sum_congr rfl
  intro p hp
  have hprime : p.Prime := (Finset.mem_filter.mp hp).2
  rw [← firstPrime_coefficient (F := ℚ) 1 hprime, heckeLogDerivCoefficient_trivial_rat,
    ArithmeticFunction.vonMangoldt_apply_prime hprime, firstPrimeShellWeight, Complex.ofReal_div]
  ring

end RiemannMasullo

namespace RiemannMasullo.RationalPrimePairs

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal Topology

/-- Rational primes in the translated logarithmic support interval `[2,4]`. -/
def window (y : ℝ) : Finset ℕ :=
  (Finset.range (⌊Real.exp (y + 4)⌋₊ + 1)).filter
    (fun p ↦ p.Prime ∧ Real.exp (y + 2) ≤ (p : ℝ))

/-- The rational principal summand in the translated degree-one prime sum. -/
def weight (H : ℝ → ℂ) (y : ℝ) (p : ℕ) : ℂ :=
  (Real.log p / Real.sqrt p) • H (Real.log p - y)

/-- Sum of the absolute products of summands over ordered near pairs, including diagonals. -/
def nearAbs (H : ℝ → ℂ) (y : ℝ) (D : ℕ) : ℝ :=
  ∑ p ∈ window y, ∑ q ∈ (window y).filter (fun q ↦ p.dist q ≤ D),
    ‖weight H y p‖ * ‖weight H y q‖

private theorem count_near (S : Finset ℕ) (p D : ℕ) :
    (S.filter (fun q ↦ p.dist q ≤ D)).card ≤ 2 * D + 1 := by
  have hsub : S.filter (fun q ↦ p.dist q ≤ D) ⊆ Finset.Icc (p-D) (p+D) := by
    intro q hq
    have h := (Finset.mem_filter.mp hq).2
    unfold Nat.dist at h
    exact Finset.mem_Icc.mpr (by omega)
  apply (Finset.card_le_card hsub).trans
  rw [Nat.card_Icc]
  omega

private theorem window_count {y : ℝ} (hy : 0 ≤ y) :
    ((window y).card : ℝ) ≤ (Real.exp 4 + 1) * Real.exp y := by
  have hn : (window y).card ≤ ⌊Real.exp (y+4)⌋₊+1 := by
    simpa only [window, Finset.card_range] using (Finset.card_filter_le (Finset.range (⌊Real.exp (y + 4)⌋₊ + 1))
      (fun p ↦ p.Prime ∧ Real.exp (y + 2) ≤ (p : ℝ)))
  calc
    ((window y).card : ℝ) ≤ (⌊Real.exp (y+4)⌋₊ : ℝ) + 1 := by exact_mod_cast hn
    _ ≤ Real.exp (y+4) + 1 := by gcongr; exact Nat.floor_le (Real.exp_pos _).le
    _ ≤ _ := by rw [Real.exp_add]; nlinarith [Real.one_le_exp hy]

private theorem weight_bound {H : ℝ → ℂ} {B y : ℝ} (hy : 0 ≤ y) (hB : 0 ≤ B)
    (hH : ∀ v ∈ Set.Icc (2 : ℝ) 4, ‖H v‖ ≤ B) {p : ℕ} (hp : p ∈ window y) :
    ‖weight H y p‖ ≤ ((y+4)*B) / Real.sqrt (Real.exp y) := by
  rw [window, Finset.mem_filter, Finset.mem_range] at hp
  have hu : (p : ℝ) ≤ Real.exp (y+4) :=
    (Nat.cast_le.mpr (Nat.le_of_lt_succ hp.1)).trans (Nat.floor_le (Real.exp_pos _).le)
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp.2.1.pos
  have hlog : Real.log p ≤ y+4 := (Real.log_le_iff_le_exp hpp).mpr hu
  have hl : y+2 ≤ Real.log p := (Real.le_log_iff_exp_le hpp).mpr hp.2.2
  have hyx : Real.exp y ≤ (p : ℝ) := (Real.exp_le_exp.mpr (by linarith : y ≤ y+2)).trans hp.2.2
  have hnorm := hH _ (show Real.log p-y ∈ Set.Icc (2:ℝ) 4 from ⟨by linarith, by linarith⟩)
  have hp0 : 0 ≤ Real.log p := by linarith
  have hex : 0 < Real.sqrt (Real.exp y) := Real.sqrt_pos.2 (Real.exp_pos _)
  rw [weight, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hp0 (Real.sqrt_nonneg _)), div_mul_eq_mul_div]
  exact div_le_div₀ (mul_nonneg (by linarith) hB) (mul_le_mul hlog hnorm (norm_nonneg _) (by linarith))
    hex (Real.sqrt_le_sqrt hyx)

/-- Absolute ordered prime-pair mass in an additive window of integral radius `D`.
The explicit bound includes the diagonal and uses no distribution theorem about primes. -/
theorem nearAbs_le (H : ℝ → ℂ) {B y : ℝ} (hy : 0 ≤ y) (hB : 0 ≤ B)
    (hH : ∀ v ∈ Set.Icc (2 : ℝ) 4, ‖H v‖ ≤ B) (D : ℕ) :
    nearAbs H y D ≤ (Real.exp 4+1) * (2*(D:ℝ)+1) * ((y+4)*B)^2 := by
  let A := ((y+4)*B) / Real.sqrt (Real.exp y)
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (by linarith) hB) (Real.sqrt_nonneg _)
  have hweight : ∀ p ∈ window y, ‖weight H y p‖ ≤ A := fun _ hp ↦ weight_bound hy hB hH hp
  have hrow (p : ℕ) (hp : p ∈ window y) :
      (∑ q ∈ (window y).filter (fun q ↦ p.dist q ≤ D), ‖weight H y p‖ * ‖weight H y q‖) ≤
      (2*(D:ℝ)+1) * A^2 := by
    calc
      _ ≤ ∑ _q ∈ (window y).filter (fun q ↦ p.dist q ≤ D), A*A := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul (hweight p hp) (hweight q (Finset.mem_filter.mp hq).1) (norm_nonneg _) hA
      _ = (((window y).filter (fun q ↦ p.dist q ≤ D)).card : ℝ) * A^2 := by simp [pow_two]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast count_near (window y) p D) (sq_nonneg _)
  calc
    nearAbs H y D ≤ ∑ _p ∈ window y, (2*(D:ℝ)+1)*A^2 := Finset.sum_le_sum hrow
    _ = ((window y).card : ℝ) * ((2*(D:ℝ)+1)*A^2) := by simp
    _ ≤ ((Real.exp 4+1)*Real.exp y) * ((2*(D:ℝ)+1)*A^2) :=
      mul_le_mul_of_nonneg_right (window_count hy) (mul_nonneg (by positivity) (sq_nonneg _))
    _ = _ := by
      dsimp only [A]
      rw [div_pow, Real.sq_sqrt (Real.exp_pos _).le]
      field_simp

/-- With `X = exp y`, a radius `X^θ` gives `O((1+y)^2 X^θ)` for `θ ≥ 0`. -/
theorem nearAbs_le_exp (H : ℝ → ℂ) {B y θ : ℝ} (hy : 0 ≤ y) (hθ : 0 ≤ θ) (hB : 0 ≤ B)
    (hH : ∀ v ∈ Set.Icc (2 : ℝ) 4, ‖H v‖ ≤ B) :
    nearAbs H y ⌊Real.exp (θ*y)⌋₊ ≤
      (48 * (Real.exp 4 + 1) * B^2) * (1+y)^2 * Real.exp (θ*y) := by
  have hcut : 2*(⌊Real.exp (θ*y)⌋₊:ℝ)+1 ≤ 3*Real.exp (θ*y) := by
    linarith [Nat.floor_le (Real.exp_pos (θ*y)).le, Real.one_le_exp (mul_nonneg hθ hy)]
  have hpow : ((y+4)*B)^2 ≤ ((4*(1+y))*B)^2 := by gcongr; linarith
  calc
    _ ≤ _ := nearAbs_le H hy hB hH _
    _ ≤ (Real.exp 4+1) * (3*Real.exp (θ*y)) * ((4*(1+y))*B)^2 := by gcongr
    _ = _ := by ring

/-- The hard-window signed sum of the real parts of the ordered Mellin products. -/
def nearReal (H : ℝ → ℂ) (y : ℝ) (D : ℕ) : ℝ :=
  ∑ p ∈ window y, ∑ q ∈ (window y).filter (fun q ↦ p.dist q ≤ D),
    (weight H y p * conj (weight H y q)).re

/-- The rational prime sum with the original upper cutoff equals its common compact window
as soon as the translated profile vanishes below the lower logarithmic endpoint. -/
theorem sum_prime_cutoff_eq_window (H : ℝ → ℂ) (hH : ∀ v < 2, H v = 0) (y : ℝ) :
    (∑ p ∈ Finset.Ioc 0 ⌊Real.exp (y+4)⌋₊ with p.Prime,
      ((Real.log p / Real.sqrt p : ℝ) : ℂ) * H (Real.log p-y)) =
      ∑ p ∈ window y, weight H y p := by
  have sub : window y ⊆ (Finset.Ioc 0 ⌊Real.exp (y+4)⌋₊).filter Nat.Prime := by
    intro p hp
    rw [window, Finset.mem_filter, Finset.mem_range] at hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp.2.1.pos, Nat.le_of_lt_succ hp.1⟩, hp.2.1⟩
  rw [← Finset.sum_subset sub]
  · apply Finset.sum_congr rfl
    intro p _
    simp [weight, Complex.real_smul]
  · intro p hp hn
    obtain ⟨hcut,hprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp0,hu⟩ := Finset.mem_Ioc.mp hcut
    have hl : (p : ℝ) < Real.exp (y+2) := by
      apply lt_of_not_ge
      intro h
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hu), hprime, h⟩)
    have hx := (Real.log_lt_iff_lt_exp (by exact_mod_cast hp0 : (0:ℝ) < p)).mpr hl
    simp [hH _ (by linarith : Real.log p-y < 2)]

/-- The positive absolute-pair majorant also controls the signed near sum. -/
theorem abs_nearReal_le (H : ℝ → ℂ) (y : ℝ) (D : ℕ) : |nearReal H y D| ≤ nearAbs H y D := by
  unfold nearReal nearAbs
  refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun p _ ↦ ?_)
  refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun q _ ↦ ?_)
  exact (Complex.abs_re_le_norm _).trans_eq (by simp)

private theorem nearAbs_mono (H : ℝ → ℂ) (y : ℝ) {a b : ℕ} (hab : a ≤ b) :
    nearAbs H y a ≤ nearAbs H y b := by
  apply Finset.sum_le_sum
  intro p _
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    obtain ⟨hq, hd⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hq, hd.trans hab⟩
  · exact fun q _ _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)

private theorem integrableOn_quadratic_weight {a : ℝ} (ha : 0 < a) (K : ℝ) :
    IntegrableOn (fun y : ℝ ↦ K * (1+y)^2 * Real.exp (-a*y)) (Ici 0) := by
  have moment (n : ℕ) : IntegrableOn (fun y : ℝ ↦ y^n * Real.exp (-a*y)) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    simpa only [Real.rpow_one, Real.rpow_natCast] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := a)
        (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by norm_num) ha)
  have hs := (((moment 0).add ((moment 1).const_mul 2)).add (moment 2)).const_mul K
  apply Integrable.congr hs
  filter_upwards with y
  dsimp
  ring

/-- The positive Abel mean of absolute ordered prime-pair products tends to zero below
the critical radius exponent `2c`. Negative radius exponents retain the diagonal. -/
theorem tendsto_nearAbs_abel_zero (H : ℝ → ℂ) {B θ c : ℝ} (hc : 0 < c) (hθ : θ < 2*c)
    (hB : 0 ≤ B) (hH : ∀ v ∈ Icc (2 : ℝ) 4, ‖H v‖ ≤ B) :
    Tendsto (fun ε : ℝ ↦ ENNReal.ofReal ε * ∫⁻ y in Ici (0 : ℝ), ENNReal.ofReal
      (nearAbs H y ⌊Real.exp (θ*y)⌋₊ * Real.exp (-(ε+2*c)*y))) (𝓝[>] 0) (𝓝 0) := by
  let t := max θ 0
  let a := 2*c-t
  let K := 48*(Real.exp 4+1)*B^2
  let g (y : ℝ) := K*(1+y)^2*Real.exp (-a*y)
  let M := ∫⁻ y in Ici (0 : ℝ), ENNReal.ofReal (g y)
  have ht : 0 ≤ t := le_max_right _ _
  have ha : 0 < a := sub_pos.mpr (max_lt hθ (by linarith))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hg : IntegrableOn g (Ici 0) := integrableOn_quadratic_weight ha _
  have hgn (y : ℝ) : 0 ≤ g y := mul_nonneg (mul_nonneg hK (sq_nonneg _)) (Real.exp_pos _).le
  have hM : M ≠ ∞ := (lintegral_ofReal_ne_top_iff_integrable hg.aestronglyMeasurable
    (ae_of_all _ hgn)).mpr hg
  have hle (ε y : ℝ) (he : 0 ≤ ε) (hy : 0 ≤ y) :
      nearAbs H y ⌊Real.exp (θ*y)⌋₊ * Real.exp (-(ε+2*c)*y) ≤ g y := by
    have hd : ⌊Real.exp (θ*y)⌋₊ ≤ ⌊Real.exp (t*y)⌋₊ :=
      Nat.floor_mono (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hy))
    have hn := (nearAbs_mono H y hd).trans (nearAbs_le_exp H hy ht hB hH)
    calc
      _ ≤ K*(1+y)^2*Real.exp (t*y) * Real.exp (-(ε+2*c)*y) :=
        mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
      _ = K*(1+y)^2*Real.exp (t*y + -(ε+2*c)*y) := by rw [mul_assoc, Real.exp_add]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by dsimp [a]; nlinarith [mul_nonneg he hy]))
        (mul_nonneg hK (sq_nonneg _))
  have hz : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal
      (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))
  have hlim : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal ε * M) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hz (Or.inr hM)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Eventually.of_forall fun _ ↦ bot_le
  · filter_upwards [self_mem_nhdsWithin] with ε (he : 0 < ε)
    exact mul_le_mul_of_nonneg_left (setLIntegral_mono' measurableSet_Ici
      (fun y hy ↦ ENNReal.ofReal_le_ofReal (hle ε y he.le hy))) (by positivity)

/-- Below `2c` the absolute value of the signed near contribution has zero Abel limit. -/
theorem tendsto_abs_nearReal_abel_zero (H : ℝ → ℂ) {B θ c : ℝ} (hc : 0 < c) (hθ : θ < 2*c)
    (hB : 0 ≤ B) (hH : ∀ v ∈ Icc (2 : ℝ) 4, ‖H v‖ ≤ B) :
    Tendsto (fun ε : ℝ ↦ ENNReal.ofReal ε * ∫⁻ y in Ici (0 : ℝ), ENNReal.ofReal
      (|nearReal H y ⌊Real.exp (θ*y)⌋₊| * Real.exp (-(ε+2*c)*y))) (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_nearAbs_abel_zero H hc hθ hB hH) (Eventually.of_forall fun _ ↦ bot_le)
  exact Eventually.of_forall fun ε ↦ mul_le_mul_of_nonneg_left
    (setLIntegral_mono' measurableSet_Ici fun y _ ↦ ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (abs_nearReal_le H y _) (Real.exp_pos _).le)) (by positivity)

/-- The integer cutoff selects exactly the real hard window, including equality. -/
theorem dist_le_floor_iff {p q : ℕ} {h : ℝ} (hh : 0 ≤ h) :
    Nat.dist p q ≤ ⌊h⌋₊ ↔ |(p : ℝ) - q| ≤ h := by
  rw [Nat.le_floor_iff hh]
  rcases le_total p q with hpq | hqp
  · rw [Nat.dist_eq_sub_of_le hpq, Nat.cast_sub hpq,
      abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr hpq)), neg_sub]
  · rw [Nat.dist_eq_sub_of_le_right hqp, Nat.cast_sub hqp,
      abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hqp))]


end RiemannMasullo.RationalPrimePairs

namespace RiemannMasullo.RationalPrimePairs

open Finset
open scoped BigOperators ComplexConjugate

/-- The signed real contribution of ordered prime pairs at gap strictly larger
than the cutoff, with both primes in the common window. -/
def farReal (H : ℝ → ℂ) (y : ℝ) (D : ℕ) : ℝ :=
  ∑ p ∈ window y, ∑ q ∈ (window y).filter (fun q ↦ D < Nat.dist p q),
    (weight H y p * conj (weight H y q)).re

/-- The squared rational prime sum splits exactly into its signed near and distant
parts for each translate and cutoff, before taking any Abel average. -/
theorem norm_sum_weight_sq_eq_nearReal_add_farReal (H : ℝ → ℂ) (y : ℝ) (D : ℕ) :
    ‖∑ p ∈ window y, weight H y p‖ ^ 2 = nearReal H y D + farReal H y D := by
  have hpart (p : ℕ) :=
    sum_filter_add_sum_filter_not (window y) (fun q ↦ Nat.dist p q ≤ D)
      (fun q ↦ (weight H y p * conj (weight H y q)).re)
  simp only [not_le] at hpart
  unfold nearReal farReal
  rw [← sum_add_distrib]
  simp_rw [hpart]
  calc
    _ = ((∑ p ∈ window y, weight H y p) * conj (∑ p ∈ window y, weight H y p)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    _ = _ := by
      rw [map_sum, sum_mul]
      simp only [mul_sum, Complex.re_sum]

end RiemannMasullo.RationalPrimePairs

namespace RiemannMasullo.RationalPrimePairs

open Finset MeasureTheory Set
open scoped BigOperators ComplexConjugate

/-- Membership in the moving prime window is a measurable condition on the translate. -/
private theorem measurable_window : Measurable window := by
  apply measurable_finset_iff.mpr
  intro p
  simp only [window, Finset.mem_filter, Finset.mem_range]
  fun_prop

private theorem measurable_pair_sum {H : ℝ → ℂ} (hH : Measurable H) {D : ℝ → ℕ}
    (hD : Measurable D) (P : ℕ → ℕ → ℕ → Prop) [∀ p q r, Decidable (P p q r)] :
    Measurable fun y ↦ ∑ p ∈ window y, ∑ q ∈ (window y).filter (fun q ↦ P p q (D y)),
      (weight H y p * conj (weight H y q)).re := by
  let F (t : ℝ × (Finset ℕ × ℕ)) : ℝ :=
    ∑ p ∈ t.2.1, ∑ q ∈ t.2.1.filter (fun q ↦ P p q t.2.2),
      (weight H t.1 p * conj (weight H t.1 q)).re
  have hF : Measurable F := by
    apply measurable_from_prod_countable_left
    rintro ⟨s, r⟩
    dsimp only [F]
    apply s.measurable_fun_sum
    intro p _
    apply (s.filter (fun q ↦ P p q r)).measurable_fun_sum
    intro q _
    simp only [weight]
    fun_prop
  change Measurable (F ∘ fun y ↦ (y, window y, D y))
  exact hF.comp <| measurable_id.prodMk (measurable_window.prodMk hD)

/-- The signed near contribution is measurable for any measurable profile and
any measurable integer-valued cutoff. -/
theorem measurable_nearReal {H : ℝ → ℂ} (hH : Measurable H) {D : ℝ → ℕ}
    (hD : Measurable D) : Measurable fun y ↦ nearReal H y (D y) :=
  measurable_pair_sum hH hD (fun p q r ↦ Nat.dist p q ≤ r)

/-- The signed distant contribution is measurable under the same assumptions. -/
theorem measurable_farReal {H : ℝ → ℂ} (hH : Measurable H) {D : ℝ → ℕ}
    (hD : Measurable D) : Measurable fun y ↦ farReal H y (D y) :=
  measurable_pair_sum hH hD (fun p q r ↦ r < Nat.dist p q)

/-- At any real radius exponent, the exponential cutoff preserves measurability. -/
private theorem measurable_nearReal_exp {H : ℝ → ℂ} (hH : Measurable H) (θ : ℝ) :
    Measurable fun y ↦ nearReal H y ⌊Real.exp (θ * y)⌋₊ :=
  measurable_nearReal hH (by fun_prop)

/-- If the damping exponent exceeds the nonnegative radius exponent, the
signed near sum is absolutely integrable on the positive half-line. -/
private theorem integrableOn_nearReal_exp {H : ℝ → ℂ} (hH : Continuous H) {θ b : ℝ}
    (hθ : 0 ≤ θ) (hb : θ < b) :
    IntegrableOn (fun y ↦ nearReal H y ⌊Real.exp (θ * y)⌋₊ * Real.exp (-b * y))
      (Ici (0 : ℝ)) := by
  obtain ⟨B,hB⟩ := (isCompact_Icc (α := ℝ) (a := 2) (b := 4)).exists_bound_of_continuousOn
    hH.continuousOn
  have hB₀ : 0 ≤ B := (norm_nonneg (H 2)).trans (hB 2 ⟨le_rfl, by norm_num⟩)
  let K := 48 * (Real.exp 4 + 1) * B ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let a := b - θ
  have ha : 0 < a := sub_pos.mpr hb
  have hdom := integrableOn_quadratic_weight ha K
  apply hdom.mono' ((measurable_nearReal_exp hH.measurable θ).mul (by fun_prop)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
  have hnear := (abs_nearReal_le H y _).trans (nearAbs_le_exp H hy hθ hB₀ hB)
  have he : Real.exp (θ * y) * Real.exp (-b * y) = Real.exp (-a * y) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [a]
    ring
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ K * (1 + y) ^ 2 * Real.exp (θ * y) * Real.exp (-b * y) :=
      mul_le_mul_of_nonneg_right hnear (Real.exp_pos _).le
    _ = K * (1 + y) ^ 2 * Real.exp (-a * y) := by rw [mul_assoc, he]
/-- At the critical radius, every strictly positive supplemental Abel damping
gives a genuine signed integral. -/
theorem integrableOn_nearReal_critical {H : ℝ → ℂ} (hH : Continuous H) {c ε : ℝ}
    (hc : 0 ≤ c) (hε : 0 < ε) :
    IntegrableOn (fun y ↦ nearReal H y ⌊Real.exp (2*c*y)⌋₊ * Real.exp (-(ε+2*c)*y))
      (Ici (0 : ℝ)) :=
  integrableOn_nearReal_exp hH (by linarith) (by linarith)

/-- At a damping parameter where the full energy is integrable, the distant
contribution is integrable and the Bochner integral has the exact signed split. -/
theorem integrableOn_farReal_and_integral_split {H : ℝ → ℂ} (hH : Continuous H)
    {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    (htotal : IntegrableOn (fun y ↦ ‖∑ p ∈ window y, weight H y p‖ ^ 2 *
      Real.exp (-(ε+2*c)*y)) (Ici (0 : ℝ))) :
    IntegrableOn (fun y ↦ farReal H y ⌊Real.exp (2*c*y)⌋₊ * Real.exp (-(ε+2*c)*y))
        (Ici (0 : ℝ)) ∧
      (∫ y in Ici (0 : ℝ), ‖∑ p ∈ window y, weight H y p‖ ^ 2 * Real.exp (-(ε+2*c)*y)) =
        (∫ y in Ici (0 : ℝ), nearReal H y ⌊Real.exp (2*c*y)⌋₊ * Real.exp (-(ε+2*c)*y)) +
        ∫ y in Ici (0 : ℝ), farReal H y ⌊Real.exp (2*c*y)⌋₊ * Real.exp (-(ε+2*c)*y) := by
  let D (y : ℝ) := ⌊Real.exp (2*c*y)⌋₊
  let k (y : ℝ) := Real.exp (-(ε+2*c)*y)
  let E (y : ℝ) := ‖∑ p ∈ window y, weight H y p‖ ^ 2 * k y
  let N (y : ℝ) := nearReal H y (D y) * k y
  let F (y : ℝ) := farReal H y (D y) * k y
  have hsum (y : ℝ) : E y = N y + F y := by
    dsimp only [E,N,F]
    rw [norm_sum_weight_sq_eq_nearReal_add_farReal H y (D y), add_mul]
  have hn : IntegrableOn N (Ici 0) := integrableOn_nearReal_critical hH hc hε
  have hf : IntegrableOn F (Ici 0) := by
    have heq : F = E - N := by
      funext y
      change F y = E y - N y
      linarith [hsum y]
    rw [heq]
    exact htotal.sub hn
  refine ⟨hf, ?_⟩
  calc
    _ = ∫ y in Ici (0 : ℝ), N y + F y := integral_congr_ae (ae_of_all _ hsum)
    _ = _ := integral_add hn hf

end RiemannMasullo.RationalPrimePairs
