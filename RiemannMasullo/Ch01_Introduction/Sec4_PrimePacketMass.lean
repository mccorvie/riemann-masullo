module

public import RiemannMasullo.Ch01_Introduction.Sec4
import RiemannMasullo.External.AlgebraicNumberTheoryLean.Chebotarev.DirichletHeckeRat
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.NumberTheory.SumPrimeReciprocals

/-! # Weighted absolute masses of rational finite-place terms

At Masullo §1.4.1, p. 28, sum the powers of each rational prime in the finite
orbital distribution and take its weighted absolute integral over positive
translations. For a nonzero compact radial test supported in a positive log
interval the prime masses are summable exactly for exponential weights above
one half. The signed sum over all places used on pp. 519–520 can have further
cancellation.

marcopetterson studied the first rational orbital packet in
[#7351](https://github.com/mccorvie/riemann-masullo/issues/7351#issuecomment-7147297911).
mlyle bounded the contribution of composite norms in #7436 and gave the
positive-shell formula in #7506. The calculation below formalizes the
argument for `introTracePrimePower` in
[#5571](https://github.com/mccorvie/riemann-masullo/issues/5571#issuecomment-7148947475).
-/

public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set

namespace RiemannMasullo

set_option quotPrecheck false

private theorem ratPrimePowerComb_disjoint {H : ℝ → ℂ} {b : ℝ} (hb : 0 < b)
    (hs : Function.support H ⊆ Ioo 0 b) {L : ℝ} (hL : b < L) (n k : ℕ) (hnk : n < k) (y : ℝ)
    (hn : H (((n : ℝ) + 1) * L - y) ≠ 0) (hk : H (((k : ℝ) + 1) * L - y) ≠ 0) : False := by
  have hl : (n : ℝ) + 1 ≤ k := by exact_mod_cast hnk
  have hgap := mul_le_mul_of_nonneg_right hl (by linarith : 0 ≤ L)
  have ha := (hs hn).1
  have hupper := (hs hk).2
  linarith

/-- For positive translations of a compact radial profile supported in `(0, b)`,
the powers of one prime with log modulus above b have disjoint supports.
The weighted integral of their sum is then a geometric series. -/
private theorem ratPrimePowerComb_weightedMass (H : ℝ → ℂ) (hcont : Continuous H)
    (hc : HasCompactSupport H) {b : ℝ} (hb : 0 < b) (hs : Function.support H ⊆ Ioo 0 b)
    {L ε : ℝ} (hL : b < L) (hε : 0 < ε) :
    let T := fun n : ℕ ↦ ((n : ℝ) + 1) * L
    let S := fun y : ℝ ↦ ∑' n : ℕ, (L : ℂ) * (Real.exp (-(T n) / 2) : ℂ) * H (T n - y)
    (∫ y in Ici 0, ‖S y‖ * Real.exp (-ε * y)) =
      (∫ u : ℝ, ‖H u‖ * Real.exp (ε * u)) * L / (Real.exp ((1 / 2 + ε) * L) - 1) := by
  intro T S
  let G (u : ℝ) := ‖H u‖ * Real.exp (ε * u)
  have hGcont : Continuous G :=
    hcont.norm.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hG : Integrable G := hGcont.integrable_of_hasCompactSupport hc.norm.mul_right
  have hG₀ (u : ℝ) : 0 ≤ G u := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  let r := Real.exp (-(1 / 2 + ε) * L)
  have hL₀ : 0 < L := by linarith
  have hr : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (by linarith) hL₀)
  let B (n : ℕ) := L * r ^ (n + 1)
  have hB (n : ℕ) : 0 ≤ B n := mul_nonneg hL₀.le (pow_nonneg hr.le _)
  have hBi : Summable B := ((summable_geometric_of_lt_one hr.le hr₁).mul_right r).mul_left L |>.congr
    fun n ↦ by simp [B, pow_succ]
  have hfac (n : ℕ) (y : ℝ) :
      ‖(L : ℂ) * (Real.exp (-(T n) / 2) : ℂ) * H (T n - y)‖ * Real.exp (-ε * y) =
        B n * G (T n - y) := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL₀,
      abs_of_pos (Real.exp_pos _)]
    dsimp only [B, G, r]
    rw [← Real.exp_nat_mul]
    calc
      L * Real.exp (-(T n) / 2) * ‖H (T n - y)‖ * Real.exp (-ε * y) =
          L * ‖H (T n - y)‖ * Real.exp (-(T n) / 2 + -ε * y) := by
        rw [Real.exp_add]
        ring
      _ = L * ‖H (T n - y)‖ * Real.exp (((n + 1 : ℕ) : ℝ) * (-(1 / 2 + ε) * L) + ε * (T n - y)) := by
        congr 2
        dsimp only [T]
        push_cast
        ring
      _ = _ := by
        rw [Real.exp_add]
        ring
  have hterm (y : ℝ) : ‖S y‖ * Real.exp (-ε * y) = ∑' n : ℕ, B n * G (T n - y) := by
    by_cases hn : ∃ n : ℕ, H (T n - y) ≠ 0
    · obtain ⟨n, hn⟩ := hn
      have hk (k : ℕ) (hkn : k ≠ n) : H (T k - y) = 0 := by
        by_contra h
        rcases lt_or_gt_of_ne hkn with hl | hl
        · exact ratPrimePowerComb_disjoint hb hs hL k n hl y h hn
        · exact ratPrimePowerComb_disjoint hb hs hL n k hl y hn h
      dsimp only [S]
      rw [tsum_eq_single n (fun k hkn ↦ by rw [hk k hkn, mul_zero]),
        tsum_eq_single n (fun k hkn ↦ by simp [G, hk k hkn])]
      exact hfac n y
    · push Not at hn
      simp [S, G, hn]
  have hsupp (y : ℝ) (hy : y ∉ Ici (0 : ℝ)) : ‖S y‖ * Real.exp (-ε * y) = 0 := by
    have h (k : ℕ) : H (T k - y) = 0 := by
      by_contra h
      have hbound := (hs h).2
      have hk : 0 ≤ (k : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hL₀.le
      have hy₀ := lt_of_not_ge hy
      dsimp only [T] at hbound
      linarith
    simp [S, h]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
  simp_rw [hterm]
  let U (n : ℕ) (y : ℝ) := B n * G (T n - y)
  have hint (n : ℕ) : Integrable (U n) := ((integrable_comp_sub_left G (T n)).mpr hG).const_mul _
  have he (n : ℕ) : (∫ y : ℝ, U n y) = B n * ∫ u : ℝ, G u := by
    dsimp only [U]
    rw [integral_const_mul, integral_sub_left_eq_self]
  have habs (n : ℕ) : (∫ y : ℝ, ‖U n y‖) = B n * ∫ u : ℝ, G u := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hB n) (hG₀ _)), U] using he n
  have hsi : Summable (fun n : ℕ ↦ ∫ y : ℝ, ‖U n y‖) :=
    (hBi.mul_right _).congr fun n ↦ (habs n).symm
  change (∫ y : ℝ, ∑' n : ℕ, U n y) = _
  rw [← integral_tsum_of_summable_integral_norm hint hsi, tsum_congr he, tsum_mul_right]
  have hsB : (∑' n : ℕ, B n) = L * ((1 - r)⁻¹ * r) := by
    simp only [B, pow_succ, tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hr.le hr₁]
  rw [hsB]
  have hrec : Real.exp ((1 / 2 + ε) * L) = r⁻¹ := by
    dsimp only [r]
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hrec]
  change L * ((1 - r)⁻¹ * r) * (∫ y : ℝ, G y) = (∫ y : ℝ, G y) * L / (r⁻¹ - 1)
  field_simp [hr.ne', (sub_pos.mpr hr₁).ne']

/-- The arithmetic weight of a complete prime-power packet has abscissa one. -/
private theorem ratPrimePacket_weight_summable_iff {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun p : Nat.Primes ↦ Real.log (p : ℝ) / ((p : ℝ) ^ σ - 1)) ↔ 1 < σ := by
  have hlog₂ : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h₂ (p : Nat.Primes) : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
  have hp (p : Nat.Primes) : (1 : ℝ) < p := one_lt_two.trans_le (h₂ p)
  have hden (p : Nat.Primes) : 0 < (p : ℝ) ^ σ - 1 := sub_pos.mpr (Real.one_lt_rpow (hp p) hσ)
  constructor
  · intro h
    have hpow : Summable (fun p : Nat.Primes ↦ (p : ℝ) ^ (-σ)) := by
      refine (h.mul_left (Real.log 2)⁻¹).of_nonneg_of_le
        (fun p ↦ (Real.rpow_pos_of_pos (zero_lt_one.trans (hp p)) _).le) ?_
      intro p
      have hlog := Real.log_le_log (by norm_num : 0 < (2 : ℝ)) (h₂ p)
      rw [Real.rpow_neg (zero_lt_one.trans (hp p)).le]
      calc
        ((p : ℝ) ^ σ)⁻¹ ≤ ((p : ℝ) ^ σ - 1)⁻¹ := by
          exact inv_anti₀ (hden p) (by linarith)
        _ = (Real.log 2)⁻¹ * (Real.log 2 / ((p : ℝ) ^ σ - 1)) := by
          field_simp [hlog₂.ne', (hden p).ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog (hden p).le)
          (inv_nonneg.mpr hlog₂.le)
    linarith [Nat.Primes.summable_rpow.mp hpow]
  · intro h
    let δ := (σ - 1) / 2
    have hδ : 0 < δ := by dsimp only [δ]; linarith
    have he : -(σ - δ) < -1 := by dsimp only [δ]; linarith
    refine ((Nat.Primes.summable_rpow.mpr he).mul_left (2 / δ)).of_nonneg_of_le
      (fun p ↦ div_nonneg (Real.log_nonneg (hp p).le) (hden p).le) ?_
    intro p
    let x := (p : ℝ)
    have hx : 0 < x := zero_lt_one.trans (hp p)
    have hxσ : 2 ≤ x ^ σ :=
      (h₂ p).trans (by simpa using Real.rpow_le_rpow_of_exponent_le (hp p).le h.le)
    calc
      Real.log x / (x ^ σ - 1) ≤ (x ^ δ / δ) / (x ^ σ / 2) :=
        div_le_div₀ (div_nonneg (Real.rpow_pos_of_pos hx _).le hδ.le) (Real.log_le_rpow_div hx.le hδ)
          (half_pos (Real.rpow_pos_of_pos hx _)) (by linarith)
      _ = (2 / δ) * x ^ (-(σ - δ)) := by
        rw [neg_sub, Real.rpow_sub hx]
        ring

/-- Every positive prime packet has a genuine integrable weighted absolute
trace on the positive ray, including the small primes whose windows overlap. -/
private theorem ratPrimePowerComb_integrableOn (H : ℝ → ℂ) (hcont : Continuous H)
    (hc : HasCompactSupport H) {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    let T := fun n : ℕ ↦ ((n : ℝ) + 1) * L
    let S := fun y : ℝ ↦ ∑' n : ℕ, (L : ℂ) * (Real.exp (-(T n) / 2) : ℂ) * H (T n - y)
    IntegrableOn (fun y : ℝ ↦ ‖S y‖ * Real.exp (-ε * y)) (Ici 0) := by
  intro T S
  obtain ⟨z, hz⟩ := hcont.norm.exists_forall_ge_of_hasCompactSupport hc.norm
  let K := ‖H z‖
  let r := Real.exp (-L / 2)
  have hr : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  let B (n : ℕ) := L * r ^ (n + 1) * K
  have hB : Summable B :=
    (((summable_geometric_of_lt_one hr.le hr₁).mul_right r).mul_left L |>.mul_right K).congr
      fun n ↦ by simp [B, pow_succ]
  let V (n : ℕ) (y : ℝ) := (L : ℂ) * (Real.exp (-(T n) / 2) : ℂ) * H (T n - y)
  have hV (n : ℕ) (y : ℝ) : ‖V n y‖ ≤ B n := by
    simp only [V, B, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL,
      abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-(T n) / 2) = r ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      dsimp only [T]
      push_cast
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (hz _) (mul_nonneg hL.le (pow_nonneg hr.le _))
  have hv (n : ℕ) : Continuous (V n) :=
    continuous_const.mul (hcont.comp (continuous_const.sub continuous_id))
  have hS : Continuous S := continuous_tsum hv hB hV
  have hbd (y : ℝ) : ‖S y‖ ≤ ∑' n, B n :=
    (norm_tsum_le_tsum_norm ((hB.of_norm_bounded (hV · y)).norm)).trans
      (((hB.of_norm_bounded (hV · y)).norm).tsum_le_tsum (hV · y) hB)
  have he : IntegrableOn (fun y : ℝ ↦ Real.exp (-ε * y)) (Ici 0) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hε) 0)
  apply (he.const_mul (∑' n, B n)).mono'
    (hS.norm.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  filter_upwards with y
  change ‖‖S y‖ * Real.exp (-ε * y)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
  exact mul_le_mul_of_nonneg_right (hbd y) (Real.exp_pos _).le

local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "q(" v ")" => ((v : Vℚ).asIdeal.absNorm : ℝ)
local notation "packet(" H ", " v ", " y ")" =>
  (∑' k : ℕ, introTracePrimePower (F := ℚ) 1 (fun r ↦ H (Real.log r - y)) v k)
local notation "comb(" H ", " L ", " y ")" =>
  (∑' k : ℕ, ((L : ℝ) : ℂ) * (Real.exp (-(((k : ℝ) + 1) * L) / 2) : ℂ) *
    H (((k : ℝ) + 1) * L - y))

private theorem introTracePrimePower_rat_positivePacket (H : ℝ → ℂ) {b : ℝ}
    (hs : Function.support H ⊆ Ioo 0 b) (v : Vℚ) {y : ℝ} (hy : 0 ≤ y) :
    packet(H, v, y) = comb(H, Real.log q(v), y) := by
  classical
  let q := q(v)
  let L := Real.log q
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq₀ := zero_lt_one.trans hq
  have hL : 0 < L := Real.log_pos hq
  have htriv : ideleClassNormTwist (F := ℚ) 1 0 = 1 := by
    ext1 g
    change (1 : ℂ) * _ ^ (0 : ℂ) = 1
    simp
  have hunit (u : (v.adicCompletion ℚ)ˣ) : (1 : HeckeCharacter (𝓞 ℚ) ℚ).restrict v u = 1 := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    rfl
  have hur : (1 : HeckeCharacter (𝓞 ℚ) ℚ).IsUnramifiedAt v :=
    HeckeCharacter.isUnramifiedAt_iff.mpr fun u ↦
      hunit (Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom u)
  let val : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ)) := Valued.v
  have hv : (1 : HeckeCharacter (𝓞 ℚ) ℚ).localValue v = 1 :=
    hunit (Units.mk0 _ val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero)
  apply tsum_congr
  intro k
  let t := ((k : ℝ) + 1) * L
  have hlog : Real.log (q ^ (k + 1)) = t := by
    rw [Real.log_pow]
    push_cast
    rfl
  have hneg : H (Real.log ((q ^ (k + 1))⁻¹) - y) = 0 := by
    by_contra h
    have hu := (hs h).1
    rw [Real.log_inv, hlog] at hu
    have ht : 0 < t := by dsimp only [t]; positivity
    linarith
  have hden : (q : ℂ) ^ (((k + 1 : ℕ) : ℂ) / 2) = (Real.exp (t / 2) : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq₀.ne'),
      ← Complex.ofReal_log hq₀.le, Complex.ofReal_exp]
    congr 1
    dsimp only [t, L]
    push_cast
    ring
  simp only [introTracePrimePower, htriv, ite_eq_left hur, hv, one_pow, star_one, one_mul]
  change (L : ℂ) * (H (Real.log (q ^ (k + 1)) - y) + H (Real.log ((q ^ (k + 1))⁻¹) - y)) /
    (q : ℂ) ^ (((k + 1 : ℕ) : ℂ) / 2) = (L : ℂ) * (Real.exp (-t / 2) : ℂ) * H (t - y)
  rw [hneg, add_zero, hlog, hden, div_eq_mul_inv, ← Complex.ofReal_inv, ← Real.exp_neg,
    neg_div]
  ring

/-- Paper: §1.4.1, p. 28, in the positive-translate comparison of Theorem
12.5.1.1, pp. 519–520. Once the log residue size exceeds the upper endpoint of
the test support, successive powers of one prime contribute on disjoint
translation intervals.
Reconstruction: integrating the absolute value of the complete finite-place
term against the exponential translation weight gives this exact value. -/
theorem introTracePrimePower_rat_weightedMass (H : ℝ → ℂ) (hcont : Continuous H)
    {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) (hs : tsupport H ⊆ Ioo 0 b) (v : Vℚ)
    (hv : b < Real.log q(v)) :
    (∫ y in Ici (0 : ℝ), ‖packet(H, v, y)‖ * Real.exp (-ε * y)) =
      (∫ u : ℝ, ‖H u‖ * Real.exp (ε * u)) * Real.log q(v) / (q(v) ^ (1 / 2 + ε) - 1) := by
  have hs' := (subset_tsupport H).trans hs
  have hc : HasCompactSupport H :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hs.trans Ioo_subset_Icc_self)
  have hp : 0 < q(v) := by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).pos
  rw [Real.rpow_def_of_pos hp, mul_comm (Real.log _) (1 / 2 + ε)]
  refine Eq.trans (integral_congr_ae ?_) (ratPrimePowerComb_weightedMass H hcont hc hb hs' hv hε)
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ici] with y hy
  rw [introTracePrimePower_rat_positivePacket H hs' v hy]

/-- Paper: §1.4.1, p. 28, and the comparison on pp. 519–520.
At every rational finite place, the sum of its prime powers has finite
weighted absolute integral on the positive translation ray. These integrals are
summable over the places exactly for weights above one half.
Reconstruction: this tests a prime-by-prime absolute estimate for the local
expression. The sum over distinct places in the trace formula is signed. -/
theorem introTracePrimePower_rat_weightedMass_summable_iff (H : ℝ → ℂ) (hcont : Continuous H)
    {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) (hs : tsupport H ⊆ Ioo 0 b) (hH : H ≠ 0) :
    (∀ v : Vℚ, IntegrableOn (fun y : ℝ ↦ ‖packet(H, v, y)‖ * Real.exp (-ε * y)) (Ici 0)) ∧
      (Summable (fun v : Vℚ ↦ ∫ y in Ici (0 : ℝ), ‖packet(H, v, y)‖ * Real.exp (-ε * y)) ↔
        1 / 2 < ε) := by
  have hs' := (subset_tsupport H).trans hs
  have hc : HasCompactSupport H :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hs.trans Ioo_subset_Icc_self)
  constructor
  · intro v
    have hL : 0 < Real.log q(v) :=
      Real.log_pos (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v)
    apply (ratPrimePowerComb_integrableOn H hcont hc hL hε).congr
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ici] with y hy
    rw [introTracePrimePower_rat_positivePacket H hs' v hy]
  · let e : Vℚ ≃ Nat.Primes := Rat.HeightOneSpectrum.primesEquiv
    let σ := (1 / 2 : ℝ) + ε
    let G (u : ℝ) := ‖H u‖ * Real.exp (ε * u)
    let C := ∫ u : ℝ, G u
    let f (v : Vℚ) := ∫ y in Ici (0 : ℝ), ‖packet(H, v, y)‖ * Real.exp (-ε * y)
    let g (p : Nat.Primes) := C * (Real.log (p : ℝ) / ((p : ℝ) ^ σ - 1))
    have hG : Continuous G :=
      hcont.norm.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    obtain ⟨u, hu⟩ : ∃ u, H u ≠ 0 := by
      by_contra! h
      exact hH (funext h)
    have hC : 0 < C := hG.integral_pos_of_hasCompactSupport_nonneg_ne_zero hc.norm.mul_right
      (fun x ↦ mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
      (x := u) (mul_ne_zero (norm_ne_zero_iff.mpr hu) (Real.exp_ne_zero _))
    have he (v : Vℚ) : q(v) = ((e v : Nat.Primes) : ℝ) := by
      exact_mod_cast NumberFieldKB.Chebotarev.RatIdele.absNorm_asIdeal v
    have ht : Tendsto (fun v : Vℚ ↦ (e v).val) cofinite atTop := by
      rw [← Nat.cofinite_eq_atTop]
      exact (Subtype.val_injective.comp e.injective).tendsto_cofinite
    have hlarge : ∀ᶠ v : Vℚ in cofinite, b < Real.log ((e v).val : ℝ) :=
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp ht)).eventually_gt_atTop b
    have hf : f =ᶠ[cofinite] g ∘ e := by
      filter_upwards [hlarge] with v hv
      have hv' : b < Real.log q(v) := (he v) ▸ hv
      dsimp only [f, Function.comp_apply, g]
      rw [introTracePrimePower_rat_weightedMass H hcont hb hε hs v hv', he, mul_div_assoc]
    calc
      Summable f ↔ Summable (g ∘ e) := summable_congr_cofinite hf
      _ ↔ Summable g := e.summable_iff
      _ ↔ 1 < σ := (summable_mul_left_iff hC.ne').trans
        (ratPrimePacket_weight_summable_iff (show 0 < σ by dsimp only [σ]; linarith))
      _ ↔ 1 / 2 < ε := by
        dsimp only [σ]
        constructor <;> intro h <;> linarith

end RiemannMasullo
