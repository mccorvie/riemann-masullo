module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.SuccPred.IntervalSucc

/-!
# A one-sided cumulative test on consecutive primes

On each interval between rational primes, compare the weighted first-prime error with its
running discrete sum after assigning the continuous mass to the preceding prime. A weighted
second moment of the gaps controls the cumulative error in this comparison.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators Interval

namespace RiemannMasullo

local notation "P" => fun n : ℕ ↦ (Nat.nth Nat.Prime n : ℝ)
local notation "gap" => fun n : ℕ ↦ P (n + 1) - P n
local notation "cell" => fun n : ℕ ↦ Ico (P n) (P (n + 1))

/-- The weighted prime sum through the real cutoff, centered by its continuous mean from two. -/
def firstPrimeDensityError (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (Nat.primeCounting ⌊x⌋₊), Real.log (P j) * f (P j)) - ∫ u in 2..x, f u

/-- Discrete cumulative error through the `n`th prime, with each continuous cell mass at its
left endpoint. The zeroth prime is two. -/
def primeGapRunningError (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (Real.log (P j) - gap j) * f (P j)

private theorem primeEndpoint_mono : Monotone P := by
  intro i j hij
  dsimp only
  exact_mod_cast (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone hij

private theorem primeEndpoint_two_le (n : ℕ) : (2 : ℝ) ≤ P n := by
  dsimp only
  exact_mod_cast (Nat.prime_nth_prime n).two_le

private theorem primeCell_cover : (⋃ n, cell n) = Ici 2 := by
  have hu : ¬ BddAbove (range P) := by
    intro ⟨B, hB⟩
    obtain ⟨n, hn⟩ := exists_nat_gt B
    have hg : (n : ℝ) ≤ P n := by
      dsimp only
      exact_mod_cast (Nat.le_add_right n 2).trans (Nat.add_two_le_nth_prime n)
    exact (hn.trans_le hg).not_ge (hB (mem_range_self n))
  simpa [Nat.nth_prime_zero_eq_two] using
    iUnion_Ico_map_succ_eq_Ici (fun n ↦ primeEndpoint_mono (Nat.zero_le n)) hu

private theorem primeCounting_floor_of_mem_cell {n : ℕ} {x : ℝ} (hx : x ∈ cell n) :
    Nat.primeCounting ⌊x⌋₊ = n + 1 := by
  have hx₀ : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 2).trans ((primeEndpoint_two_le n).trans hx.1)
  have hl := Nat.le_floor hx.1
  have hr := (Nat.floor_lt hx₀).2 hx.2
  change Nat.count Nat.Prime (⌊x⌋₊ + 1) = n + 1
  have hiff (a b : ℕ) := Nat.lt_nth_iff_count_lt (a := a) (b := b) (p := Nat.Prime) Nat.infinite_setOfPred_prime
  apply le_antisymm
  · exact Nat.le_of_not_gt fun h ↦ (Nat.lt_succ_iff.mp ((hiff _ _).mp h)).not_gt hr
  · exact (hiff _ _).mpr (Nat.lt_succ_of_le hl)

private theorem primeCell_weight {d : ℝ} (hd : 0 < d) (n : ℕ) :
    (∫ x in cell n, x ^ (-d - 1)) = ((P n) ^ (-d) - (P (n + 1)) ^ (-d)) / d := by
  have hle := primeEndpoint_mono (Nat.le_succ n)
  have hp : 0 < P n := (by norm_num : (0 : ℝ) < 2).trans_le (primeEndpoint_two_le n)
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
    integral_rpow (.inr ⟨by linarith, by simpa [uIcc_of_le hle] using hp.not_ge⟩)]
  rw [show -d - 1 + 1 = -d by ring, div_neg]
  ring

private theorem summable_weighted_prefix {u a : ℕ → ℝ} (hu : Antitone u) (hu₀ : ∀ n, 0 ≤ u n)
    (ha : ∀ n, 0 ≤ a n) (hs : Summable fun n ↦ u n * a n) :
    Summable fun n ↦ (u n - u (n + 1)) * ∑ j ∈ Finset.range (n + 1), a j := by
  have he (N : ℕ) :
      (∑ n ∈ Finset.range N, (u n - u (n + 1)) * ∑ j ∈ Finset.range (n + 1), a j) +
      u N * ∑ j ∈ Finset.range N, a j = ∑ j ∈ Finset.range N, u j * a j := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ (f := a),
        Finset.sum_range_succ (f := fun j ↦ u j * a j)]
      linarith only [ih, sub_mul (u N) (u (N + 1)) ((∑ j ∈ Finset.range N, a j) + a N),
        mul_add (u N) (∑ j ∈ Finset.range N, a j) (a N)]
  refine summable_of_sum_range_le (fun n ↦ mul_nonneg (sub_nonneg.mpr (hu (Nat.le_succ n)))
    (Finset.sum_nonneg fun j _ ↦ ha j)) (c := ∑' n, u n * a n) fun N ↦ ?_
  apply le_trans _ (hs.sum_le_tsum (Finset.range N) fun j _ ↦ mul_nonneg (hu₀ j) (ha j))
  rw [← he N]
  exact le_add_of_nonneg_right (mul_nonneg (hu₀ N) (Finset.sum_nonneg fun j _ ↦ ha j))

private def primeCellDefect (f : ℝ → ℝ) (j : ℕ) : ℝ :=
  gap j * f (P j) - ∫ u in P j..P (j + 1), f u

private theorem intervalIntegrable_pos_of_continuousOn {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioi 0)) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable f volume a b :=
  (hf.mono (show uIcc a b ⊆ Ioi 0 from fun _ hx ↦ (lt_min ha hb).trans_le hx.1)).intervalIntegrable

private theorem primeDensity_sub_running {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0))
    {n : ℕ} {x : ℝ} (hx : x ∈ cell n) :
    firstPrimeDensityError f x - primeGapRunningError f n =
      (∑ j ∈ Finset.range (n + 1), primeCellDefect f j) + ∫ u in x..P (n + 1), f u := by
  have hp (j : ℕ) : 0 < P j := (by norm_num : (0 : ℝ) < 2).trans_le (primeEndpoint_two_le j)
  have ht := intervalIntegral.sum_integral_adjacent_intervals (n := n + 1) (a := P)
    (fun j _ ↦ intervalIntegrable_pos_of_continuousOn hf (hp j) (hp (j + 1)))
  change (∑ j ∈ Finset.range (n + 1), ∫ u in P j..P (j + 1), f u) = _ at ht
  simp only [Nat.nth_prime_zero_eq_two, Nat.cast_ofNat] at ht
  have hx₀ := (hp n).trans_le hx.1
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_pos_of_continuousOn hf (by norm_num : (0 : ℝ) < 2) hx₀)
    (intervalIntegrable_pos_of_continuousOn hf hx₀ (hp (n + 1)))
  simp only [firstPrimeDensityError, primeCounting_floor_of_mem_cell hx, primeGapRunningError,
    primeCellDefect, sub_mul, Finset.sum_sub_distrib]
  linarith only [ht, ha]

private theorem primeCellDefect_abs_le {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Ioi 0))
    {s D : ℝ} (hs : 0 ≤ s) (hD : 0 ≤ D)
    (hd : ∀ u, 2 ≤ u → |deriv f u| ≤ D * u ^ (-s - 1)) (n : ℕ) :
    |primeCellDefect f n| ≤ D * (gap n) ^ 2 * (P n) ^ (-s - 1) := by
  have hab := primeEndpoint_mono (Nat.le_succ n)
  have hp : 0 < P n := (by norm_num : (0 : ℝ) < 2).trans_le (primeEndpoint_two_le n)
  have hdiff (u : ℝ) (hu : u ∈ Icc (P n) (P (n + 1))) :=
    hf.differentiableAt (isOpen_Ioi.mem_nhds (hp.trans_le hu.1))
  have hseg := norm_image_sub_le_of_norm_deriv_le_segment' (fun u hu ↦
    (hdiff u hu).hasDerivAt.hasDerivWithinAt) (C := D * (P n) ^ (-s - 1))
    (fun u hu ↦ (hd u ((primeEndpoint_two_le n).trans hu.1)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hp hu.1 (by linarith)) hD))
  rw [primeCellDefect, ← smul_eq_mul, ← intervalIntegral.integral_const,
    ← intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegrable_pos_of_continuousOn hf.continuousOn hp (hp.trans_le hab))]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun u : ℝ ↦ f (P n) - f u) (a := P n) (b := P (n + 1))
    (C := D * (P n) ^ (-s - 1) * gap n) (by
      intro u hu
      rw [uIoc_of_le hab] at hu
      rw [norm_sub_rev]
      exact (hseg u ⟨hu.1.le, hu.2⟩).trans (mul_le_mul_of_nonneg_left
        (sub_le_sub_right hu.2 _) (mul_nonneg hD (Real.rpow_nonneg hp.le _))))
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hnorm
  exact hnorm.trans_eq (by dsimp only; ring)

private theorem primeCell_finalIntegral_abs_le {f : ℝ → ℝ} {C s : ℝ}
    (hC : 0 ≤ C) (hs : 0 ≤ s) (hb : ∀ u, 2 ≤ u → |f u| ≤ C * u ^ (-s))
    {n : ℕ} {x : ℝ} (hx : x ∈ cell n) :
    |∫ u in x..P (n + 1), f u| ≤ C * (P n) ^ (-s) * gap n := by
  have hp : 0 < P n := (by norm_num : (0 : ℝ) < 2).trans_le (primeEndpoint_two_le n)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (a := x)
    (b := P (n + 1)) (C := C * (P n) ^ (-s)) (by
      intro u hu
      rw [uIoc_of_le hx.2.le] at hu
      have hpu := hx.1.trans hu.1.le
      exact (hb u ((primeEndpoint_two_le n).trans hpu)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hp hpu (by linarith)) hC))
  rw [abs_of_nonneg (sub_nonneg.mpr hx.2.le)] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left (sub_le_sub_left hx.1 _)
    (mul_nonneg hC (Real.rpow_nonneg hp.le _)))

private theorem primeCell_rpow_integrable (r : ℝ) (n : ℕ) :
    IntegrableOn (fun x : ℝ ↦ x ^ r) (cell n) :=
  (show ContinuousOn (fun x : ℝ ↦ x ^ r) (Icc (P n) (P (n + 1))) from fun x hx ↦
    (Real.continuousAt_rpow_const x r (.inl (by linarith [primeEndpoint_two_le n, hx.1]))).continuousWithinAt).integrableOn_Icc.mono_set Ico_subset_Icc_self

private theorem primeCell_signed_integrable {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0))
    (d e : ℝ) (n : ℕ) : IntegrableOn
      (fun x : ℝ ↦ x ^ (-d - 1) * max (e * firstPrimeDensityError f x) 0) (cell n) := by
  let A := ∑ j ∈ Finset.range (n + 1), Real.log (P j) * f (P j)
  have hle := primeEndpoint_two_le (n + 1)
  have hc : ContinuousOn (fun x : ℝ ↦ ∫ u in 2..x, f u) (Icc 2 (P (n + 1))) := by
    rw [← uIcc_of_le hle]
    exact intervalIntegral.continuousOn_primitive_interval' (intervalIntegrable_pos_of_continuousOn hf
      (by norm_num) ((by norm_num : (0 : ℝ) < 2).trans_le hle)) left_mem_uIcc
  have hp : ContinuousOn (fun x : ℝ ↦ x ^ (-d - 1)) (Icc 2 (P (n + 1))) :=
    fun x hx ↦ (Real.continuousAt_rpow_const x _ (.inl (by linarith [hx.1]))).continuousWithinAt
  have hloc : IntegrableOn (fun x : ℝ ↦ x ^ (-d - 1) * max (e * (A - ∫ u in 2..x, f u)) 0)
      (cell n) :=
    (hp.mul ((continuousOn_const.mul (continuousOn_const.sub hc)).sup continuousOn_const)).integrableOn_Icc.mono_set
      (fun _ hx ↦ ⟨(primeEndpoint_two_le n).trans hx.1, hx.2.le⟩)
  exact hloc.congr_fun (fun x hx ↦ by simp only [firstPrimeDensityError, primeCounting_floor_of_mem_cell hx, A])
    measurableSet_Ico

private theorem integrableOn_iff_summable_primeCells {F : ℝ → ℝ}
    (hF : ∀ x, 2 ≤ x → 0 ≤ F x) (hloc : ∀ n, IntegrableOn F (cell n)) :
    IntegrableOn F (Ici 2) ↔ Summable (fun n ↦ ∫ x in cell n, F x) := by
  rw [← primeCell_cover]
  constructor
  · exact fun h ↦ (hasSum_integral_iUnion (fun _ ↦ measurableSet_Ico)
      primeEndpoint_mono.pairwise_disjoint_on_Ico_succ h).summable
  · intro h
    apply integrableOn_iUnion_of_summable_integral_norm hloc
    refine h.congr fun n ↦ setIntegral_congr_fun measurableSet_Ico fun x hx ↦ ?_
    exact (Real.norm_of_nonneg (hF x ((primeEndpoint_two_le n).trans hx.1))).symm

private theorem primeCell_signed_mass_sub_le {s d C e : ℝ} (hs : 0 ≤ s) (hd : 0 < d)
    (hC : 0 ≤ C) {f : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0))
    (hb : ∀ u, 2 ≤ u → |f u| ≤ C * u ^ (-s)) (n : ℕ) :
    |(∫ x in cell n, x ^ (-d - 1) * max (e * firstPrimeDensityError f x) 0) -
      (((P n) ^ (-d) - (P (n + 1)) ^ (-d)) / d) * max (e * primeGapRunningError f n) 0| ≤
      |e| * ((((P n) ^ (-d) - (P (n + 1)) ^ (-d)) / d) *
        (∑ j ∈ Finset.range (n + 1), |primeCellDefect f j|) +
        C * (gap n) ^ 2 * (P n) ^ (-s - d - 1)) := by
  let p := P n
  let w (x : ℝ) := x ^ (-d - 1)
  let S := ∑ j ∈ Finset.range (n + 1), |primeCellDefect f j|
  let L := C * p ^ (-s) * gap n
  have hp : 0 < p := (by norm_num : (0 : ℝ) < 2).trans_le (primeEndpoint_two_le n)
  have hL : 0 ≤ L := mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hp.le _))
    (sub_nonneg.mpr (primeEndpoint_mono (Nat.le_succ n)))
  have hi := primeCell_rpow_integrable (-d - 1) n
  have hc : IntegrableOn (fun x ↦ w x * (|e| * S) + w p * (|e| * L)) (cell n) :=
    (hi.mul_const _).add (integrableOn_const (by simp [Real.volume_Ico]))
  have est (x : ℝ) (hx : x ∈ cell n) :
      |w x * max (e * firstPrimeDensityError f x) 0 - w x * max (e * primeGapRunningError f n) 0| ≤
      w x * (|e| * S) + w p * (|e| * L) := by
    have hw : 0 ≤ w x := Real.rpow_nonneg (hp.le.trans hx.1) _
    have hxw : w x ≤ w p := Real.rpow_le_rpow_of_nonpos hp hx.1 (by linarith)
    have hgap : |firstPrimeDensityError f x - primeGapRunningError f n| ≤ S + L := by
      rw [primeDensity_sub_running hf hx]
      exact (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _)
        (primeCell_finalIntegral_abs_le hC hs hb hx))
    rw [← mul_sub, abs_mul, abs_of_nonneg hw]
    calc
      _ ≤ w x * |e * firstPrimeDensityError f x - e * primeGapRunningError f n| :=
        mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs _ _ _) hw
      _ ≤ w x * (|e| * (S + L)) := by
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgap (abs_nonneg e)) hw
      _ ≤ _ := by
        rw [mul_add, mul_add]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hxw (mul_nonneg (abs_nonneg e) hL))
  rw [← primeCell_weight hd, ← integral_mul_const, ← integral_sub
    (primeCell_signed_integrable hf d e n) (hi.mul_const _)]
  have hbound := norm_integral_le_of_norm_le (f := fun x ↦ w x * max (e * firstPrimeDensityError f x) 0 -
    w x * max (e * primeGapRunningError f n) 0) hc
    ((ae_restrict_mem measurableSet_Ico).mono (fun x hx ↦ est x hx))
  apply hbound.trans_eq
  rw [integral_add (hi.mul_const _) (integrableOn_const ?_), integral_mul_const, setIntegral_const,
    Real.volume_real_Ico_of_le (primeEndpoint_mono (Nat.le_succ n)), smul_eq_mul]
  · dsimp only [w, S, L, p]
    rw [primeCell_weight hd, show -s - d - 1 = (-d - 1) + (-s) by ring,
      Real.rpow_add hp]
    ring
  · simp [Real.volume_Ico]

private theorem summable_primeCell_prefix {s d D : ℝ} (hs : 0 ≤ s) (hd : 0 < d) (hD : 0 ≤ D)
    {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Ioi 0))
    (hder : ∀ u, 2 ≤ u → |deriv f u| ≤ D * u ^ (-s - 1))
    (hm : Summable fun n ↦ (gap n) ^ 2 * (P n) ^ (-s - d - 1)) :
    Summable fun n ↦ (((P n) ^ (-d) - (P (n + 1)) ^ (-d)) / d) *
      ∑ j ∈ Finset.range (n + 1), |primeCellDefect f j| := by
  let u (n : ℕ) := (P n) ^ (-d)
  have hp (n : ℕ) : 0 < P n := (by norm_num : (0 : ℝ) < 2).trans_le (primeEndpoint_two_le n)
  have hu : Antitone u := fun i j hij ↦ Real.rpow_le_rpow_of_nonpos (hp i)
    (primeEndpoint_mono hij) (by linarith)
  have hsum : Summable fun j ↦ u j * |primeCellDefect f j| := by
    apply Summable.of_nonneg_of_le (fun n ↦ mul_nonneg (Real.rpow_nonneg (hp n).le _) (abs_nonneg _))
      _ (hm.mul_left D)
    intro n
    apply (mul_le_mul_of_nonneg_left (primeCellDefect_abs_le hf hs hD hder n) (Real.rpow_nonneg (hp n).le _)).trans_eq
    dsimp only [u]
    rw [show -s - d - 1 = -d + (-s - 1) by ring, Real.rpow_add (hp n)]
    ring
  have h := (summable_weighted_prefix hu (fun n ↦ Real.rpow_nonneg (hp n).le _)
    (fun n ↦ abs_nonneg (primeCellDefect f n)) hsum).div_const d
  exact h.congr fun n ↦ by dsimp only [u]; ring

/-- For either sign, the continuously centered first-prime error is integrable against
`x ^ (-d-1) dx` exactly when the corresponding sign of the discrete running gap error is
summable against the successive decreases of `p ^ (-d)`. The moment hypothesis uses `s+d`. -/
theorem integrableOn_firstPrimeDensityError_iff_gapRunningSum {s d C D : ℝ}
    (hs : 0 ≤ s) (hd : 0 < d) (hC : 0 ≤ C) (hD : 0 ≤ D)
    {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Ioi 0))
    (hb : ∀ u, 2 ≤ u → |f u| ≤ C * u ^ (-s))
    (hder : ∀ u, 2 ≤ u → |deriv f u| ≤ D * u ^ (-s - 1))
    (hm : Summable fun n ↦ (gap n) ^ 2 * (P n) ^ (-s - d - 1)) (e : ℝ) :
    IntegrableOn (fun x : ℝ ↦ x ^ (-d - 1) * max (e * firstPrimeDensityError f x) 0) (Ici 2) ↔
    Summable (fun n ↦ ((P n) ^ (-d) - (P (n + 1)) ^ (-d)) * max (e * primeGapRunningError f n) 0) := by
  let W (n : ℕ) := (P n) ^ (-d) - (P (n + 1)) ^ (-d)
  let I (n : ℕ) := ∫ x in cell n, x ^ (-d - 1) * max (e * firstPrimeDensityError f x) 0
  let V (n : ℕ) := W n / d * max (e * primeGapRunningError f n) 0
  have hdiff : Summable (fun n ↦ I n - V n) := by
    refine Summable.of_norm_bounded (((summable_primeCell_prefix hs hd hD hf hder hm).add
      (hm.mul_left C)).mul_left |e|) fun n ↦ ?_
    simpa only [Real.norm_eq_abs, mul_assoc] using
      primeCell_signed_mass_sub_le (e := e) hs hd hC hf.continuousOn hb n
  rw [integrableOn_iff_summable_primeCells (fun x hx ↦ mul_nonneg
    (Real.rpow_nonneg (by linarith : 0 ≤ x) _) (le_max_right _ _))
    (primeCell_signed_integrable hf.continuousOn d e)]
  change Summable I ↔ Summable fun n ↦ W n * max (e * primeGapRunningError f n) 0
  have h : Summable I ↔ Summable V := ⟨fun hI ↦ (hI.sub hdiff).congr fun n ↦ by simp,
    fun hV ↦ (hdiff.add hV).congr fun n ↦ by simp⟩
  refine h.trans ⟨fun hV ↦ (hV.mul_right d).congr fun n ↦ ?_,
    fun hV ↦ (hV.div_const d).congr fun n ↦ ?_⟩
  · dsimp only [V]
    field_simp
  · dsimp only [V]
    ring

/-- The single-frequency rational prime weight for a fixed half-strip. -/
def primeCosineWeight (s h x : ℝ) : ℝ := x ^ (-s) * (1 - Real.cos (h * Real.log x))

private theorem hasDerivAt_primeCosineWeight (s h : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (primeCosineWeight s h)
      (x ^ (-s - 1) * (-s * (1 - Real.cos (h * Real.log x)) + h * Real.sin (h * Real.log x))) x := by
  have hp := Real.hasDerivAt_rpow_const (x := x) (p := -s) (Or.inl hx.ne')
  have ht := (((Real.hasDerivAt_log hx.ne').const_mul h).cos).const_sub 1
  convert hp.mul ht using 1
  · rfl
  · rw [Real.rpow_sub_one hx.ne']
    ring

/-- The one-sided rational prime test with weight `1 - cos (h log x)` is equivalent to a single
nonnegative series over the running, locally gap-centered prime sums. Taking `e = 1` or `-1`
selects the positive or negative part independently. -/
theorem integrableOn_primeCosineError_iff_gapRunningSum {s d : ℝ} (hs : 0 ≤ s) (hd : 0 < d)
    (h e : ℝ) (hm : Summable fun n ↦ (gap n) ^ 2 * (P n) ^ (-s - d - 1)) :
    IntegrableOn (fun x : ℝ ↦ x ^ (-d - 1) * max (e * firstPrimeDensityError (primeCosineWeight s h) x) 0)
      (Ici 2) ↔
    Summable (fun n ↦ ((P n) ^ (-d) - (P (n + 1)) ^ (-d)) *
      max (e * primeGapRunningError (primeCosineWeight s h) n) 0) := by
  have hB (t : ℝ) : |1 - Real.cos t| ≤ 2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one t))]
    linarith [Real.neg_one_le_cos t]
  apply integrableOn_firstPrimeDensityError_iff_gapRunningSum hs hd (C := 2) (D := 2 * s + |h|)
    (by norm_num) (by positivity) (fun x hx ↦ (hasDerivAt_primeCosineWeight s h hx).differentiableAt.differentiableWithinAt) _ _ hm
  · intro u hu
    rw [primeCosineWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _), mul_comm (2 : ℝ)]
    exact mul_le_mul_of_nonneg_left (hB _) (Real.rpow_nonneg (by linarith) _)
  · intro u hu
    rw [(hasDerivAt_primeCosineWeight s h (by linarith : 0 < u)).deriv, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _), mul_comm (2 * s + |h|)]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_neg, abs_of_nonneg hs, abs_mul]
    nlinarith only [mul_le_mul_of_nonneg_left (hB (h * Real.log u)) hs,
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (h * Real.log u)) (abs_nonneg h)]

/-- In log coordinates the same running sums detect exponential integrability of either sign
of the continuous first-prime error. The lower cutoff is the first prime. -/
theorem integrableOn_exp_primeCosineError_iff_gapRunningSum {s d : ℝ} (hs : 0 ≤ s) (hd : 0 < d)
    (h e : ℝ) (hm : Summable fun n ↦ (gap n) ^ 2 * (P n) ^ (-s - d - 1)) :
    IntegrableOn (fun L ↦ Real.exp (-d * L) *
      max (e * firstPrimeDensityError (primeCosineWeight s h) (Real.exp L)) 0) (Ici (Real.log 2)) ↔
    Summable (fun n ↦ ((P n) ^ (-d) - (P (n + 1)) ^ (-d)) *
      max (e * primeGapRunningError (primeCosineWeight s h) n) 0) := by
  rw [← integrableOn_primeCosineError_iff_gapRunningSum hs hd h e hm,
    integrableOn_Ici_iff_integrableOn_Ioi, integrableOn_Ici_iff_integrableOn_Ioi]
  have heq (L : ℝ) : Real.exp L * (Real.exp L) ^ (-d - 1) = Real.exp (-d * L) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
    congr 1
    ring
  simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2), smul_eq_mul, ← mul_assoc, heq] using
    integrableOn_comp_exp_Ioi (fun x : ℝ ↦ x ^ (-d - 1) *
      max (e * firstPrimeDensityError (primeCosineWeight s h) x) 0) (Real.log 2)

end RiemannMasullo
