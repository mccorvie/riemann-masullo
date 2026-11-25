module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Transport of the first-prime orbital statistic

For the rational chart of Theorem 12.5.1.1, pp. 519–520, estimate the change in the
weighted cumulative finite-place first-prime sum when the prime masses are relocated.
The pole subtraction stays fixed and cancels in the difference.
-/

public noncomputable section

open Real Set MeasureTheory Filter
open scoped Topology BigOperators

namespace RiemannMasullo

/-- An atom at log norm x, including its weight and the upper log cutoff L. -/
@[expose] def firstPrimeCutoffRow (s x L : ℝ) : ℝ :=
  if x < L then (1 - Real.cos (x / 2)) * Real.exp (-s * x) else 0

private def atomWeight (s x : ℝ) : ℝ := (1 - Real.cos (x / 2)) * Real.exp (-s * x)

private theorem exp_damping_sub {d x y : ℝ} (hd : 0 ≤ d) (hxy : x ≤ y) :
    0 ≤ Real.exp (-d * x) - Real.exp (-d * y) ∧
    Real.exp (-d * x) - Real.exp (-d * y) ≤ d * (y - x) * Real.exp (-d * x) := by
  have hp : 0 ≤ d * (y - x) := mul_nonneg hd (sub_nonneg.mpr hxy)
  rw [show -d * y = -d * x + -(d * (y - x)) by ring, Real.exp_add]
  constructor
  · exact sub_nonneg.mpr (mul_le_of_le_one_right (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith)))
  · nlinarith [mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-(d * (y - x)))) (Real.exp_pos (-d * x)).le]


private theorem atomWeight_sub {s x y : ℝ} (hs : 0 ≤ s) (hxy : x ≤ y) :
    |atomWeight s x - atomWeight s y| ≤ (2 * s + 1 / 2) * Real.exp (-s * x) * (y - x) := by
  let B := fun v : ℝ ↦ 1 - Real.cos (v / 2)
  have hB : |B x - B y| ≤ (y - x) / 2 := by
    have hc := Real.abs_cos_sub_cos_le (y / 2) (x / 2)
    simpa [B, abs_of_nonneg (by linarith : 0 ≤ y / 2 - x / 2), sub_div] using hc
  have hBy : 0 ≤ B y := sub_nonneg.mpr (Real.cos_le_one _)
  have hBy₂ : B y ≤ 2 := by dsimp [B]; linarith [Real.neg_one_le_cos (y / 2)]
  have hsplit : atomWeight s x - atomWeight s y =
      (B x - B y) * Real.exp (-s * x) + B y * (Real.exp (-s * x) - Real.exp (-s * y)) := by dsimp [B, atomWeight]; ring
  rw [hsplit]
  apply (abs_add_le ..).trans
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hBy,
    abs_of_nonneg (exp_damping_sub hs hxy).1]
  calc
    _ ≤ (y - x) / 2 * Real.exp (-s * x) + 2 * (s * (y - x) * Real.exp (-s * x)) := by
      exact add_le_add (mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le)
        (mul_le_mul hBy₂ (exp_damping_sub hs hxy).2 (exp_damping_sub hs hxy).1 (by norm_num))
    _ = _ := by ring


private theorem dampedRow_integrable (s x : ℝ) {d : ℝ} (hd : 0 < d) :
    Integrable (fun L : ℝ ↦ firstPrimeCutoffRow s x L * Real.exp (-d * L)) := by
  have he : (fun L : ℝ ↦ firstPrimeCutoffRow s x L * Real.exp (-d * L)) =
      (Ioi x).indicator (fun L : ℝ ↦ atomWeight s x * Real.exp (-d * L)) := by
    funext L
    by_cases hx : x < L <;> simp [firstPrimeCutoffRow, atomWeight, hx]
  rw [he, integrable_indicator_iff measurableSet_Ioi]
  exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hd) x).const_mul _


private theorem ordered_row_cost {s d x y : ℝ} (hd : 0 < d) (hxy : x ≤ y) :
    (∫ L : ℝ, |firstPrimeCutoffRow s x L - firstPrimeCutoffRow s y L| * Real.exp (-d * L)) =
      (atomWeight s x * (Real.exp (-d * x) - Real.exp (-d * y)) +
        |atomWeight s x - atomWeight s y| * Real.exp (-d * y)) / d := by
  let e := fun L : ℝ ↦ Real.exp (-d * L)
  have hx := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hd) x
  have hy := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hd) y
  have hmid := hx.mono_set (show Ioc x y ⊆ Ioi x from fun _ h ↦ h.1)
  have he (L : ℝ) :
      |firstPrimeCutoffRow s x L - firstPrimeCutoffRow s y L| * Real.exp (-d * L) =
      ((Ioc x y).indicator (fun l ↦ atomWeight s x * e l) L) +
        ((Ioi y).indicator (fun l ↦ |atomWeight s x - atomWeight s y| * e l) L) := by
    by_cases hyL : y < L
    · have hxL := lt_of_le_of_lt hxy hyL
      simp [firstPrimeCutoffRow, atomWeight, e, hyL, hxL, not_le.mpr hyL]
    by_cases hxL : x < L
    · simp [firstPrimeCutoffRow, atomWeight, e, hxL, hyL, le_of_not_gt hyL, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
    · simp [firstPrimeCutoffRow, hxL, hyL]
  simp_rw [he]
  rw [integral_add ((integrable_indicator_iff measurableSet_Ioc).2 (hmid.const_mul _))
    ((integrable_indicator_iff measurableSet_Ioi).2 (hy.const_mul _)),
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioi, integral_const_mul, integral_const_mul]
  change atomWeight s x * (∫ L in Ioc x y, Real.exp (-d * L)) +
    |atomWeight s x - atomWeight s y| * (∫ L in Ioi y, Real.exp (-d * L)) = _
  rw [← intervalIntegral.integral_of_le hxy, ← intervalIntegral.integral_Ioi_sub_Ioi hx hxy, integral_exp_mul_Ioi (neg_lt_zero.mpr hd),
    integral_exp_mul_Ioi (neg_lt_zero.mpr hd)]
  ring


/-- The weighted cumulative cost of moving a single first-prime atom is bounded by
its displacement in log norm times the damping at the smaller endpoint. -/
theorem firstPrimeCutoffRow_transport_le {s d : ℝ} (hs : 0 ≤ s) (hd : 0 < d) (x y : ℝ) :
    (∫ L : ℝ, |firstPrimeCutoffRow s x L - firstPrimeCutoffRow s y L| * Real.exp (-d * L)) ≤
      (2 + (2 * s + 1 / 2) / d) * Real.exp (-(s + d) * min x y) * |x - y| := by
  wlog hxy : x ≤ y generalizing x y
  · simpa only [abs_sub_comm (firstPrimeCutoffRow s y _) _, min_comm y x, abs_sub_comm y x] using
      this y x (le_of_not_ge hxy)
  rw [ordered_row_cost hd hxy, min_eq_left hxy, abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub,
    div_le_iff₀ hd]
  have hax₂ : atomWeight s x ≤ 2 * Real.exp (-s * x) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    linarith [Real.neg_one_le_cos (x / 2)]
  have h1 := mul_le_mul hax₂ (exp_damping_sub hd.le hxy).2 (exp_damping_sub hd.le hxy).1
    (by positivity : 0 ≤ 2 * Real.exp (-s * x))
  have h2 := mul_le_mul (atomWeight_sub hs hxy) ((exp_damping_sub hd.le hxy).1 |> sub_nonneg.mp)
    (Real.exp_pos (-d * y)).le (by positivity : 0 ≤ (2 * s + 1 / 2) * Real.exp (-s * x) * (y - x))
  have hex : Real.exp (-(s + d) * x) = Real.exp (-s * x) * Real.exp (-d * x) := by
    rw [← Real.exp_add]; congr 1; ring
  refine (add_le_add h1 h2).trans_eq ?_
  rw [hex]
  field_simp


private theorem rowCost_integrable (s x y : ℝ) {d : ℝ} (hd : 0 < d) :
    Integrable (fun L : ℝ ↦ |firstPrimeCutoffRow s x L - firstPrimeCutoffRow s y L| * Real.exp (-d * L)) := by
  have h := ((dampedRow_integrable s x hd).sub (dampedRow_integrable s y hd)).norm
  simpa only [Pi.sub_apply, ← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using h


private def finitePrimeTransport (s : ℝ) (q : ℕ → ℝ) (N : ℕ) (L : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE N, Real.log p *
    (firstPrimeCutoffRow s (Real.log p) L - firstPrimeCutoffRow s (Real.log (q p)) L)

private theorem finitePrimeTransport_integrable (s : ℝ) {d : ℝ} (hd : 0 < d)
    (N : ℕ) (q : ℕ → ℝ) :
    Integrable (fun L : ℝ ↦ finitePrimeTransport s q N L * Real.exp (-d * L)) := by
  simp only [finitePrimeTransport, Finset.sum_mul, mul_assoc (Real.log _) _ _]
  apply integrable_finsetSum
  intro p hp
  simpa only [Pi.sub_apply, ← sub_mul] using (((dampedRow_integrable s (Real.log p) hd).sub
    (dampedRow_integrable s (Real.log (q p)) hd)).const_mul (Real.log p))


/-- For every finite cutoff this bounds the weighted absolute difference of the actual
rational first-prime sum and its relocated sum, including the changed sharp cutoff in
each row. The common continuous pole term cancels. -/
theorem rationalFirstPrime_transport_le {s d : ℝ} (hs : 0 ≤ s) (hd : 0 < d)
    (N : ℕ) (q : ℕ → ℝ) :
    (∫ L : ℝ, |∑ p ∈ Nat.primesLE N, Real.log p *
      (firstPrimeCutoffRow s (Real.log p) L - firstPrimeCutoffRow s (Real.log (q p)) L)| *
        Real.exp (-d * L)) ≤
      (2 + (2 * s + 1 / 2) / d) * ∑ p ∈ Nat.primesLE N, Real.log p *
        (Real.exp (-(s + d) * min (Real.log p) (Real.log (q p))) * |Real.log p - Real.log (q p)|) := by
  let a (p : ℕ) (L : ℝ) := Real.log p *
    (firstPrimeCutoffRow s (Real.log p) L - firstPrimeCutoffRow s (Real.log (q p)) L)
  have hcost (p : ℕ) : Integrable (fun L : ℝ ↦ |a p L| * Real.exp (-d * L)) := by
    simpa only [a, abs_mul, abs_of_nonneg (Real.log_natCast_nonneg p), mul_assoc] using
      (rowCost_integrable s (Real.log p) (Real.log (q p)) hd).const_mul (Real.log p)
  have hsum : Integrable (fun L : ℝ ↦ |∑ p ∈ Nat.primesLE N, a p L| * Real.exp (-d * L)) := by
    simpa only [finitePrimeTransport, a, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      using (finitePrimeTransport_integrable s hd N q).norm
  change (∫ L : ℝ, |∑ p ∈ Nat.primesLE N, a p L| * Real.exp (-d * L)) ≤ _
  calc
    _ ≤ ∫ L : ℝ, ∑ p ∈ Nat.primesLE N, |a p L| * Real.exp (-d * L) := by
      apply integral_mono hsum (integrable_finsetSum _ (fun p _ ↦ hcost p))
      intro L
      dsimp only
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Real.exp_pos _).le
    _ = ∑ p ∈ Nat.primesLE N, ∫ L : ℝ, |a p L| * Real.exp (-d * L) :=
      integral_finsetSum _ (fun p _ ↦ hcost p)
    _ ≤ _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      simp only [a, abs_mul, abs_of_nonneg (Real.log_natCast_nonneg p), mul_assoc, integral_const_mul]
      apply (mul_le_mul_of_nonneg_left (firstPrimeCutoffRow_transport_le hs hd _ _) (Real.log_natCast_nonneg p)).trans_eq
      ring


private theorem abs_log_sub_le {p u : ℝ} (hp : 0 < p) (hu : p / 2 ≤ u) :
    |Real.log p - Real.log u| ≤ (2 / p) * |u - p| := by
  have hu' : 0 < u := by linarith
  by_cases h : p ≤ u
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hp h)), neg_sub,
      abs_of_nonneg (sub_nonneg.mpr h), ← Real.log_div hu'.ne' hp.ne']
    apply (Real.log_le_sub_one_of_pos (div_pos hu' hp)).trans
    field_simp
    linarith
  · have hup := le_of_not_ge h
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hu' hup)),
      abs_of_nonpos (sub_nonpos.mpr hup), neg_sub, ← Real.log_div hp.ne' hu'.ne']
    apply (Real.log_le_sub_one_of_pos (div_pos hp hu')).trans
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hup) (by linarith : 0 ≤ 2 * u - p)]


private theorem firstPrime_transport_power {p u t α ε : ℝ} (hp : 1 ≤ p) (ht : 0 ≤ t)
    (hε : 0 < ε) (hu : p / 2 ≤ u) (hmove : |u - p| ≤ p ^ α) :
    Real.log p * (Real.exp (-t * min (Real.log p) (Real.log u)) * |Real.log p - Real.log u|) ≤
      (2 * (2 : ℝ) ^ t / ε) * p ^ (ε - t + α - 1) := by
  have hp' : 0 < p := by linarith
  have hhalf : 0 < p / 2 := by positivity
  have hmin : Real.log (p / 2) ≤ min (Real.log p) (Real.log u) :=
    le_min (Real.log_le_log hhalf (by linarith)) (Real.log_le_log hhalf hu)
  have he : Real.exp (-t * min (Real.log p) (Real.log u)) ≤ p ^ (-t) * (2 : ℝ) ^ t := by
    calc
      _ ≤ Real.exp (-t * Real.log (p / 2)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hmin (by linarith))
      _ = (p / 2) ^ (-t) := by rw [Real.rpow_def_of_pos hhalf, mul_comm]
      _ = _ := by rw [Real.div_rpow hp'.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
  have hlog := (abs_log_sub_le hp' hu).trans (mul_le_mul_of_nonneg_left hmove (by positivity))
  have hleft := Real.log_le_rpow_div hp'.le hε
  calc
    _ ≤ (p ^ ε / ε) * ((p ^ (-t) * (2 : ℝ) ^ t) * ((2 / p) * p ^ α)) := by
      exact mul_le_mul hleft (mul_le_mul he hlog (abs_nonneg _) (by positivity))
        (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)) (by positivity)
    _ = _ := by
      rw [show ε - t + α - 1 = ε + (-t) + α + (-1) by ring, Real.rpow_add hp', Real.rpow_add hp',
        Real.rpow_add hp', Real.rpow_neg_one]
      ring


/-- Uniform absolute control of rational first-prime transport at every cutoff. A prime
of norm p may move anywhere above p/2 within p^α of p, for α<s+d. The same constant
works for all relocations and cutoffs. -/
theorem rationalFirstPrime_transport_uniform_of_power {s d α : ℝ} (hs : 0 ≤ s) (hd : 0 < d)
    (hα : α < s + d) :
    ∃ C : ℝ, ∀ (N : ℕ) (q : ℕ → ℝ),
      (∀ p ∈ Nat.primesLE N, (p : ℝ) / 2 ≤ q p ∧ |q p - p| ≤ (p : ℝ) ^ α) →
      (∫ L : ℝ, |∑ p ∈ Nat.primesLE N, Real.log p *
        (firstPrimeCutoffRow s (Real.log p) L - firstPrimeCutoffRow s (Real.log (q p)) L)| *
          Real.exp (-d * L)) ≤ C := by
  let ε := (s + d - α) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hsum := Real.summable_nat_rpow.mpr (show ε - (s + d) + α - 1 < -1 by dsimp [ε]; linarith)
  let k := 2 + (2 * s + 1 / 2) / d
  let c := 2 * (2 : ℝ) ^ (s + d) / ε
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨k * (c * ∑' n : ℕ, (n : ℝ) ^ (ε - (s + d) + α - 1)), fun N q hq ↦ ?_⟩
  apply (rationalFirstPrime_transport_le hs hd N q).trans
  apply mul_le_mul_of_nonneg_left _ hk
  calc
    _ ≤ ∑ p ∈ Nat.primesLE N, c * (p : ℝ) ^ (ε - (s + d) + α - 1) := by
      apply Finset.sum_le_sum
      intro p hp
      exact firstPrime_transport_power (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)
        (by linarith) hε (hq p hp).1 (hq p hp).2
    _ = c * ∑ p ∈ Nat.primesLE N, (p : ℝ) ^ (ε - (s + d) + α - 1) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ (fun _ _ ↦ by positivity)) hc


/-- The full difference of the first-prime sums before and after relocation.
For destinations q(p) ≥ p/2 both cutoffs vanish when p > 2 exp L. -/
@[expose] def rationalFirstPrimePacketDifference (s : ℝ) (q : ℕ → ℝ) (L : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌈2 * Real.exp L⌉₊, Real.log p *
    (firstPrimeCutoffRow s (Real.log p) L - firstPrimeCutoffRow s (Real.log (q p)) L)

private theorem finitePrimeTransport_eventually (s : ℝ) (q : ℕ → ℝ)
    (hq : ∀ p, Nat.Prime p → (p : ℝ) / 2 ≤ q p) (L : ℝ) :
    ∀ᶠ N in atTop, finitePrimeTransport s q N L = rationalFirstPrimePacketDifference s q L := by
  filter_upwards [eventually_ge_atTop ⌈2 * Real.exp L⌉₊] with N hN
  symm
  apply Finset.sum_subset (Nat.primesLE_mono hN)
  intro p hp hp'
  have prime := Nat.prime_of_mem_primesLE hp
  have hg : ⌈2 * Real.exp L⌉₊ < p := by
    by_contra! h
    exact hp' (Nat.mem_primesLE.mpr ⟨h, prime⟩)
  have h₂ : 2 * Real.exp L < (p : ℝ) := (Nat.le_ceil _).trans_lt (by exact_mod_cast hg)
  have hq' := hq p prime
  have hp₀ : 0 < (p : ℝ) := by exact_mod_cast prime.pos
  have hu₀ : 0 < q p := by linarith
  have hpL := (Real.le_log_iff_exp_le hp₀).2 (by linarith [Real.exp_pos L])
  have huL := (Real.le_log_iff_exp_le hu₀).2 (by linarith)
  simp [firstPrimeCutoffRow, not_lt.mpr hpL, not_lt.mpr huL]


private theorem packetDifference_uniform {s d α : ℝ} (hs : 0 ≤ s) (hd : 0 < d) (hα : α < s + d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ → ℝ,
      (∀ p, Nat.Prime p → (p : ℝ) / 2 ≤ q p ∧ |q p - p| ≤ (p : ℝ) ^ α) →
      Integrable (fun L : ℝ ↦ rationalFirstPrimePacketDifference s q L * Real.exp (-d * L)) ∧
      (∫ L : ℝ, ‖rationalFirstPrimePacketDifference s q L * Real.exp (-d * L)‖) ≤ C := by
  obtain ⟨C, hC⟩ := rationalFirstPrime_transport_uniform_of_power hs hd hα
  refine ⟨max C 0, le_max_right _ _, fun q hq ↦ ?_⟩
  let F (N : ℕ) (L : ℝ) := finitePrimeTransport s q N L * Real.exp (-d * L)
  let f (L : ℝ) := rationalFirstPrimePacketDifference s q L * Real.exp (-d * L)
  have hi (N : ℕ) : Integrable (F N) := finitePrimeTransport_integrable s hd N q
  have ht : ∀ᵐ L : ℝ, Tendsto (fun N ↦ F N L) atTop (𝓝 (f L)) := by
    apply ae_of_all
    intro L
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [finitePrimeTransport_eventually s q (fun p hp ↦ (hq p hp).1) L] with N h
    simp only [F, f, h]
  have hbound : liminf (fun N ↦ ∫⁻ L : ℝ, ‖F N L‖ₑ) atTop ≤ ENNReal.ofReal (max C 0) := by
    apply liminf_le_of_frequently_le' (Frequently.of_forall _)
    intro N
    rw [← ofReal_integral_norm_eq_lintegral_eNorm (hi N)]
    apply ENNReal.ofReal_le_ofReal
    apply le_trans _ (le_max_left C 0)
    simpa only [F, finitePrimeTransport, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
      hC N q (fun p hp ↦ hq p (Nat.prime_of_mem_primesLE hp))
  have hfi : Integrable f := integrable_of_tendsto ht (fun N ↦ (hi N).1)
    (hbound.trans_lt ENNReal.ofReal_lt_top).ne
  refine ⟨hfi, (ENNReal.ofReal_le_ofReal_iff (le_max_right C 0)).mp ?_⟩
  rw [ofReal_integral_norm_eq_lintegral_eNorm hfi]
  exact (lintegral_eNorm_le_liminf_of_tendsto ht (fun N ↦ (hi N).1.aemeasurable.eNorm)).trans hbound


private theorem packetDifference_measurable {Ω : Type*} [MeasurableSpace Ω]
    (s : ℝ) (q : ℕ → Ω → ℝ) (hm : ∀ p, Nat.Prime p → Measurable (q p))
    (hq : ∀ p, Nat.Prime p → ∀ ω, (p : ℝ) / 2 ≤ q p ω) :
    Measurable (fun z : Ω × ℝ ↦ rationalFirstPrimePacketDifference s (fun p ↦ q p z.1) z.2) := by
  have row {g : Ω × ℝ → ℝ} (hg : Measurable g) :
      Measurable (fun z ↦ firstPrimeCutoffRow s (g z) z.2) := by
    unfold firstPrimeCutoffRow
    exact Measurable.ite (measurableSet_lt hg measurable_snd) (by fun_prop) measurable_const
  apply measurable_of_tendsto_metrizable (f := fun N (z : Ω × ℝ) ↦ finitePrimeTransport s (fun p ↦ q p z.1) N z.2)
  · intro N
    apply Finset.measurable_fun_sum
    intro p hp
    exact measurable_const.mul ((row measurable_const).sub (row ((hm p (Nat.prime_of_mem_primesLE hp)).log.comp measurable_fst)))
  · apply tendsto_pi_nhds.2
    intro z
    exact tendsto_const_nhds.congr' ((finitePrimeTransport_eventually s _ (fun p hp ↦ hq p hp z.1) z.2).mono (fun _ h ↦ h.symm))


/-- Smear the true rational first-prime masses by arbitrary measurable random
relocations of width p^α. For α<s+d, their full expected cumulative error against
the original statistic is absolutely integrable with weight exp(−dL). The bound is
uniform over probability spaces and relocation laws; no independence is assumed. -/
theorem rationalFirstPrimePacket_integral_le {s d α : ℝ} (hs : 0 ≤ s) (hd : 0 < d)
    (hα : α < s + d) :
    ∃ C : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (q : ℕ → Ω → ℝ), (∀ p, Nat.Prime p → Measurable (q p)) →
      (∀ p, Nat.Prime p → ∀ ω, (p : ℝ) / 2 ≤ q p ω ∧ |q p ω - p| ≤ (p : ℝ) ^ α) →
      let E := fun L : ℝ ↦ ∫ ω, rationalFirstPrimePacketDifference s (fun p ↦ q p ω) L ∂μ
      Integrable (fun L ↦ E L * Real.exp (-d * L)) ∧
      (∫ L, |E L| * Real.exp (-d * L)) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := packetDifference_uniform hs hd hα
  refine ⟨C, ?_⟩
  intro Ω _ μ _ q hm hq
  let F (z : Ω × ℝ) := rationalFirstPrimePacketDifference s (fun p ↦ q p z.1) z.2 * Real.exp (-d * z.2)
  have hF : Measurable F := (packetDifference_measurable s q hm (fun p hp ω ↦ (hq p hp ω).1)).mul (by fun_prop)
  have hω (ω : Ω) := hbound (fun p ↦ q p ω) (fun p hp ↦ hq p hp ω)
  have hi : Integrable F (μ.prod volume) := by
    apply (integrable_prod_iff hF.aestronglyMeasurable).2
    refine ⟨ae_of_all _ (fun ω ↦ (hω ω).1), (integrable_const C).mono' hF.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable ?_⟩
    filter_upwards with ω
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
    exact (hω ω).2
  constructor
  · simpa only [F, integral_mul_const] using hi.integral_prod_right
  · calc
      _ = ∫ L : ℝ, ‖∫ ω, F (ω, L) ∂μ‖ := by
        simp only [F, integral_mul_const, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ ∫ L : ℝ, ∫ ω, ‖F (ω, L)‖ ∂μ := by
        exact integral_mono hi.integral_prod_right.norm hi.norm.integral_prod_right
          (fun L ↦ norm_integral_le_integral_norm _)
      _ = ∫ ω, (∫ L : ℝ, ‖F (ω, L)‖) ∂μ := (integral_integral_swap (f := fun ω L ↦ ‖F (ω, L)‖) hi.norm).symm
      _ ≤ ∫ _ : Ω, C ∂μ := integral_mono hi.norm.integral_prod_left (integrable_const C) (fun ω ↦ (hω ω).2)
      _ = C := by simp


private theorem integrable_posPart_add_iff {M E : ℝ → ℝ} (hM : AEStronglyMeasurable M volume)
    (hE : Integrable E) :
    Integrable (fun L ↦ max (M L + E L) 0) ↔ Integrable (fun L ↦ max (M L) 0) := by
  let D (L : ℝ) := max (M L + E L) 0 - max (M L) 0
  have hD : Integrable D := by
    apply hE.norm.mono' (((hM.add hE.1).sup aestronglyMeasurable_const).sub (hM.sup aestronglyMeasurable_const))
    filter_upwards with L
    change |max (M L + E L) 0 - max (M L) 0| ≤ |E L|
    simpa only [add_sub_cancel_left] using
      abs_max_sub_max_le_abs (M L + E L) (M L) 0
  constructor
  · intro h
    apply (h.sub hD).congr
    exact ae_of_all _ (fun L ↦ sub_sub_cancel _ _)
  · intro h
    apply (hD.add h).congr
    exact ae_of_all _ (fun L ↦ sub_add_cancel _ _)


/-- A probability packet of width p^α preserves one-sided weighted integrability
when α<s+d. Use sign −1 to subtract the transport error from the original
first-prime statistic, or sign +1 to compare its negative part. M may include any
common measurable compensator. -/
theorem rationalFirstPrimePacket_posPart_iff {s d α : ℝ} (hs : 0 ≤ s) (hd : 0 < d)
    (hα : α < s + d) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : ℕ → Ω → ℝ) (hm : ∀ p, Nat.Prime p → Measurable (q p))
    (hq : ∀ p, Nat.Prime p → ∀ ω, (p : ℝ) / 2 ≤ q p ω ∧ |q p ω - p| ≤ (p : ℝ) ^ α)
    (M : ℝ → ℝ) (hM : AEStronglyMeasurable M volume) (sign : ℝ) :
    let E := fun L : ℝ ↦ ∫ ω, rationalFirstPrimePacketDifference s (fun p ↦ q p ω) L ∂μ
    Integrable (fun L ↦ max (M L + sign * E L) 0 * Real.exp (-d * L)) ↔
      Integrable (fun L ↦ max (M L) 0 * Real.exp (-d * L)) := by
  obtain ⟨_, h⟩ := rationalFirstPrimePacket_integral_le hs hd hα
  have hi := (h μ q hm hq).1.const_mul sign
  have he : Measurable (fun L : ℝ ↦ Real.exp (-d * L)) := by fun_prop
  have hn := integrable_posPart_add_iff (hM.mul he.aestronglyMeasurable) hi
  simpa only [Pi.mul_apply, max_mul_of_nonneg _ _ (Real.exp_pos _).le, zero_mul, add_mul, mul_assoc] using hn

end RiemannMasullo
