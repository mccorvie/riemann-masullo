module

public import RiemannMasullo.Ch01_Introduction.Sec4
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Causal reconstruction of the finite orbital term

For the prime-power distribution of §1.4.1 (p. 28), integrate the compact
test's derivatives against a one-sided kernel on the logarithmic norm line.
-/

@[expose] public noncomputable section

open IsDedekindDomain MeasureTheory NumberField Set

namespace RiemannMasullo

/-- The causal kernel recovers a complex test at its left endpoint when both
the test and its first derivative vanish at the right endpoint. -/
private theorem introTrace_causal_integral (κ a b : ℝ) (f f' f'' : ℝ → ℂ)
    (h₁ : ∀ t, HasDerivAt f (f' t) t) (h₂ : ∀ t, HasDerivAt f' (f'' t) t)
    (h₃ : Continuous f'') (hb : f b = 0) (hb' : f' b = 0) :
    (∫ t in a..b, (((t - a) * Real.exp (-κ * (t - a)) : ℝ) : ℂ) *
      ((κ : ℂ) ^ 2 * f t - 2 * κ * f' t + f'' t)) = f a := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun t ↦ (h₁ t).continuousAt
  have hc' : Continuous f' := continuous_iff_continuousAt.mpr fun t ↦ (h₂ t).continuousAt
  let F (t : ℝ) := (Real.exp (-κ * (t - a)) : ℂ) *
    (((t - a : ℝ) : ℂ) * f' t - ((κ * (t - a) + 1 : ℝ) : ℂ) * f t)
  have hF (t : ℝ) : HasDerivAt F ((((t - a) * Real.exp (-κ * (t - a)) : ℝ) : ℂ) *
      ((κ : ℂ) ^ 2 * f t - 2 * κ * f' t + f'' t)) t := by
    have hd := (hasDerivAt_id t).sub_const a
    have he := ((hd.const_mul (-κ)).exp).ofReal_comp
    have ha := (hd.ofReal_comp.mul (h₂ t)).sub
      (((hd.const_mul κ).add_const 1).ofReal_comp.mul (h₁ t))
    convert he.mul ha using 1
    all_goals first | rfl | (dsimp [F]; push_cast; ring)
  have hi : IntervalIntegrable (fun t ↦ (((t - a) * Real.exp (-κ * (t - a)) : ℝ) : ℂ) *
      ((κ : ℂ)^2 * f t - 2 * κ * f' t + f'' t)) volume a b :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hF t) hi]
  simp [F, hb, hb']

/-- Extend the one-sided kernel by zero before the prime-power ordinate. -/
private theorem introTrace_causal_integral_max (κ a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (f f' f'' : ℝ → ℂ) (h₁ : ∀ t, HasDerivAt f (f' t) t) (h₂ : ∀ t, HasDerivAt f' (f'' t) t)
    (h₃ : Continuous f'') (hf : ∀ t, b ≤ t → f t = 0) (hf' : f' b = 0) :
    (∫ t in 0..b, ((max (t - a) 0 * Real.exp (-κ * (t - a)) : ℝ) : ℂ) *
      ((κ : ℂ) ^ 2 * f t - 2 * κ * f' t + f'' t)) = f a := by
  let g (t : ℝ) := ((max (t - a) 0 * Real.exp (-κ * (t - a)) : ℝ) : ℂ) *
    ((κ : ℂ) ^ 2 * f t - 2 * κ * f' t + f'' t)
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun t ↦ (h₁ t).continuousAt
  have hc' : Continuous f' := continuous_iff_continuousAt.mpr fun t ↦ (h₂ t).continuousAt
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hz (u : ℝ) (hu : 0 ≤ u) (hua : u ≤ a) : (∫ t in 0..u, g t) = 0 := by
    rw [← intervalIntegral.integral_zero (a := 0) (b := u) (E := ℂ)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hu] at ht
    simp [g, max_eq_right (sub_nonpos.mpr (ht.2.trans hua))]
  change (∫ t in 0..b, g t) = _
  by_cases hab : a ≤ b
  · rw [← intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable 0 a)
      (hg.intervalIntegrable a b), hz a ha le_rfl, zero_add]
    apply Eq.trans _ (introTrace_causal_integral κ a b f f' f'' h₁ h₂ h₃ (hf b le_rfl) hf')
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    simp [g, max_eq_left (sub_nonneg.mpr ht.1)]
  · rw [hz b hb (by linarith), hf a (by linarith)]

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "U𝔽" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
set_option quotPrecheck false

local notation "primePowerNorm(" v ", " k ")" => (((v : V).asIdeal.absNorm : ℝ) ^ ((k : ℕ) + 1))

/-- The positive shell of the actual finite-place orbital distribution acts
by evaluation at the corresponding logarithmic prime-power norm. -/
private theorem introTrace_causal_prime_atom (χ : U𝔽) (v : V) (k : ℕ)
    (f : ℝ → ℂ) (hf : ∀ t ≤ 0, f t = 0) :
    introTracePrimePower χ (fun r ↦ f (Real.log r)) v k =
      introTracePrimePower χ (fun r ↦ if 1 < r then 1 else 0) v k *
        f (Real.log primePowerNorm(v, k)) := by
  classical
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hr : 1 < primePowerNorm(v, k) := one_lt_pow₀ hq (Nat.succ_ne_zero k)
  have hi : primePowerNorm(v, k)⁻¹ ≤ 1 := (inv_le_one_of_one_le₀ hr.le)
  have hl : Real.log primePowerNorm(v, k)⁻¹ ≤ 0 := Real.log_nonpos (inv_nonneg.mpr (by positivity)) hi
  simp only [introTracePrimePower, hf _ hl, ite_eq_left hr, ite_eq_right (not_lt.mpr hi)]
  split <;> ring

/-- Reconstruction for §1.4.1, p. 28. Smooth each positive prime-power atom
causally in the logarithmic norm. An atom at log Q contributes its actual
Hecke orbital coefficient times (t − log Q) exp(−κ(t − log Q)) for Q ≤ exp t. -/
def introTraceCausalPrimeSum (χ : U𝔽) (κ t : ℝ) : ℂ :=
  ∑' p : V × ℕ, introTracePrimePower χ (fun r ↦ if 1 < r then 1 else 0) p.1 p.2 *
    ((max (t - Real.log primePowerNorm(p.1, p.2)) 0 * Real.exp (-κ * (t - Real.log primePowerNorm(p.1, p.2))) : ℝ) : ℂ)

/-- All the causal sums on a bounded integration interval use a common
finite set of prime powers. -/
private theorem introTrace_causal_finite_window (b : ℝ) :
    ∃ S : Finset (V × ℕ), ∀ p ∉ S, b < Real.log primePowerNorm(p.1, p.2) := by
  classical
  obtain ⟨B, hB⟩ := exists_nat_ge (Real.exp b)
  have hfin : {v : V | v.asIdeal.absNorm ≤ B}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_le (S := 𝓞 F) B).preimage
      HeightOneSpectrum.asIdeal_injective.injOn
  refine ⟨hfin.toFinset ×ˢ Finset.range (B + 1), ?_⟩
  rintro ⟨v, k⟩ hnot
  by_contra! h
  have hn := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hr : 0 < primePowerNorm(v, k) := pow_pos (by exact_mod_cast hn.pos) _
  have hpow : v.asIdeal.absNorm ^ (k + 1) ≤ B := by
    exact_mod_cast ((Real.log_le_iff_le_exp hr).mp h).trans hB
  have hq : v.asIdeal.absNorm ≤ v.asIdeal.absNorm ^ (k + 1) := by
    simpa using Nat.pow_le_pow_right hn.le (Nat.succ_pos k)
  have hk : k < 2 ^ k := Nat.lt_two_pow_self
  have ht : 2 ^ k ≤ v.asIdeal.absNorm ^ (k + 1) :=
    (Nat.pow_le_pow_left (by omega : 2 ≤ v.asIdeal.absNorm) k).trans
      (Nat.pow_le_pow_right hn.le (Nat.le_succ k))
  apply hnot
  simp only [Finset.mem_product, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_range]
  exact ⟨hq.trans hpow, by omega⟩

/-- Reconstruction for §1.4.1, p. 28. For a twice continuously differentiable
logarithmic test supported in (0, b), the full finite orbital term is recovered
by integrating its second-order differential expression against the causal
prime-power sum. The identity holds for any number field and unitary character. -/
theorem introTracePrimePower_sum_eq_causalIntegral (χ : U𝔽) (κ : ℝ) {b : ℝ} (hb : 0 ≤ b)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ Ioo 0 b) :
    (∑' p : V × ℕ, introTracePrimePower χ (fun r ↦ f (Real.log r)) p.1 p.2) =
    ∫ t in 0..b, introTraceCausalPrimeSum χ κ t *
      ((κ : ℂ)^2 * f t - 2 * κ * deriv f t + deriv (deriv f) t) := by
  classical
  let a (p : V × ℕ) := Real.log primePowerNorm(p.1, p.2)
  let c (p : V × ℕ) := introTracePrimePower χ (fun r ↦ if 1 < r then 1 else 0) p.1 p.2
  let K (p : V × ℕ) (t : ℝ) : ℂ :=
    ((max (t - a p) 0 * Real.exp (-κ * (t - a p)) : ℝ) : ℂ)
  let L (t : ℝ) := (κ : ℂ)^2 * f t - 2 * κ * deriv f t + deriv (deriv f) t
  have hlow (t : ℝ) (ht : t ≤ 0) : f t = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ (hs h).1.not_ge ht
  have hhigh (t : ℝ) (ht : b ≤ t) : f t = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ (hs h).2.not_ge ht
  have hf' : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hc'' : Continuous (deriv (deriv f)) := hf'.continuous_deriv_one
  have hL : Continuous L := by
    dsimp [L]
    fun_prop (disch := first | exact hf.continuous | exact hf'.continuous | assumption)
  have hK (p : V × ℕ) : Continuous (K p) := by dsimp [K]; fun_prop
  obtain ⟨S, hS⟩ := introTrace_causal_finite_window (F := F) b
  have htrunc (t : ℝ) (ht : t ≤ b) :
      introTraceCausalPrimeSum χ κ t = ∑ p ∈ S, c p * K p t := by
    apply tsum_eq_sum
    intro p hp
    have htp : t ≤ a p := ht.trans (hS p hp).le
    change c p * K p t = 0
    simp [K, max_eq_right (sub_nonpos.mpr htp)]
  have ha (p : V × ℕ) : 0 ≤ a p := by
    apply Real.log_nonneg
    apply one_le_pow₀
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm p.1).le
  calc
    _ = ∑ p ∈ S, c p * f (a p) := by
      simp_rw [introTrace_causal_prime_atom χ _ _ f hlow]
      apply tsum_eq_sum
      intro p hp
      change c p * f (a p) = 0
      rw [hhigh _ (hS p hp).le, mul_zero]
    _ = ∑ p ∈ S, ∫ t in 0..b, (c p * K p t) * L t := by
      apply Finset.sum_congr rfl
      intro p _
      simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
      congr 1
      exact (introTrace_causal_integral_max κ (a p) b (ha p) hb f (deriv f)
        (deriv (deriv f)) (fun t ↦ (hf.differentiable (by norm_num) t).hasDerivAt)
        (fun t ↦ (hf'.differentiable (by norm_num) t).hasDerivAt) hc'' hhigh
        (deriv_of_notMem_tsupport fun h ↦ (hs h).2.false)).symm
    _ = _ := by
      rw [← intervalIntegral.integral_finsetSum (f := fun p t ↦ c p * K p t * L t) (fun p _ ↦
        (((hK p).const_mul (c p)).mul hL).intervalIntegrable 0 b)]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hb] at ht
      change (∑ p ∈ S, c p * K p t * L t) = introTraceCausalPrimeSum χ κ t * L t
      rw [htrunc t ht.2, Finset.sum_mul]


/-- Reconstruction for §1.4.1, p. 28. Every nonnegative log-norm translate
of one positive-shell test is recovered from the same causal prime sum.
Only the compact differential test and the integration endpoint move. -/
theorem introTracePrimePower_translate_eq_causalIntegral (χ : U𝔽) (κ : ℝ) {b y : ℝ}
    (hb : 0 ≤ b) (hy : 0 ≤ y) (H : ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (hs : tsupport H ⊆ Ioo 0 b) :
    (∑' p : V × ℕ, introTracePrimePower χ (fun r ↦ H (Real.log r - y)) p.1 p.2) =
    ∫ t in 0..y+b, introTraceCausalPrimeSum χ κ t *
      ((κ : ℂ)^2 * H (t - y) - 2 * κ * deriv H (t - y) + deriv (deriv H) (t - y)) := by
  have hcomp : tsupport (fun t ↦ H (t - y)) ⊆ Ioo 0 (y + b) := by
    intro t ht
    have hmem := tsupport_comp_subset_preimage H (continuous_id.sub (continuous_const (y := y))) ht
    have htb : t - y ∈ Ioo 0 b := hs hmem
    constructor <;> linarith [htb.1, htb.2]
  have h := introTracePrimePower_sum_eq_causalIntegral χ κ (add_nonneg hy hb)
    (fun t ↦ H (t - y)) (hH.comp (contDiff_id.sub contDiff_const)) hcomp
  simpa only [funext (deriv_comp_sub_const H y), deriv_comp_sub_const] using h


/-- Reconstruction for §1.4.1, p. 28. At decay three halves the causal
statistic is the logarithmically weighted sum of the actual twisted von
Mangoldt coefficients. A prime power of norm Q ≤ exp t has weight
exp(−3t/2) Q (t − log Q), and larger norms contribute zero. -/
theorem introTraceCausalPrimeSum_three_halves (χ : U𝔽) (t : ℝ) :
    introTraceCausalPrimeSum χ (3/2) t = (Real.exp (-(3/2) * t) : ℂ) *
      ∑' p : V × ℕ, heckeIdealVonMangoldt (ideleClassNormTwist χ 0) (p.1.asIdeal ^ (p.2 + 1)) *
        ((primePowerNorm(p.1, p.2) : ℝ) : ℂ) * (max (t - Real.log primePowerNorm(p.1, p.2)) 0 : ℝ) := by
  classical
  rw [introTraceCausalPrimeSum, ← tsum_mul_left]
  apply tsum_congr
  rintro ⟨v, k⟩
  let q : ℝ := v.asIdeal.absNorm
  let Q := q ^ (k + 1)
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hQ : 1 < Q := one_lt_pow₀ hq (Nat.succ_ne_zero k)
  have hden : (q : ℂ) ^ (((k + 1 : ℕ) : ℂ) / 2) =
      (Real.exp (Real.log Q / 2) : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (lt_trans zero_lt_one hq).ne')]
    rw [← Complex.ofReal_log (lt_trans zero_lt_one hq).le, Complex.ofReal_exp]
    congr 1
    dsimp [Q]
    rw [Real.log_pow]
    push_cast
    ring
  have he : Real.exp (-(3/2) * (t - Real.log Q)) =
      Real.exp (-(3/2) * t) * Q * Real.exp (Real.log Q / 2) := by
    calc
      _ = Real.exp ((-(3/2) * t + Real.log Q) + Real.log Q / 2) := by congr 1; ring
      _ = _ := by rw [Real.exp_add, Real.exp_add, Real.exp_log (lt_trans zero_lt_one hQ)]
  have hi : Q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hQ.le
  change introTracePrimePower χ _ v k * ((max (t - Real.log Q) 0 * _ : ℝ) : ℂ) = _
  rw [heckeIdealVonMangoldt, heckeIdealValue_prime_pow _ v (Nat.succ_pos k),
    idealVonMangoldt_prime_pow v (Nat.succ_pos k)]
  unfold introTracePrimePower
  change (if (ideleClassNormTwist χ 0).IsUnramifiedAt v then
    (Real.log q : ℂ) * (_ * (if 1 < Q then 1 else 0) + _ * (if 1 < Q⁻¹ then 1 else 0)) /
      (q : ℂ) ^ (((k + 1 : ℕ) : ℂ) / 2) else 0) *
      ((max (t - Real.log Q) 0 * Real.exp (-(3/2) * (t - Real.log Q)) : ℝ) : ℂ) = _
  rw [ite_eq_left hQ, ite_eq_right (not_lt.mpr hi), hden, he]
  change (if (ideleClassNormTwist χ 0).IsUnramifiedAt v then _ else 0) * _ =
    (Real.exp (-(3/2) * t) : ℂ) * (((if (ideleClassNormTwist χ 0).IsUnramifiedAt v then
      (ideleClassNormTwist χ 0).localValue v ^ (k + 1) else 0) * (Real.log q : ℂ)) *
        (Q : ℂ) * (max (t - Real.log Q) 0 : ℝ))
  split_ifs <;> push_cast <;> field_simp [Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'] <;> ring

end RiemannMasullo
