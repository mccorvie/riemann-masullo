module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Moments.Moments
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Weight
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

public section

open MeasureTheory Set

namespace RiemannMasullo

private theorem spectralLineJet_window_continuous {f : ℝ → ℝ} (hf : Continuous f) (h : ℝ) :
    Continuous (fun t : ℝ ↦ ∫ u in t..t + h, f u) := by
  let P (t : ℝ) := ∫ u in (0 : ℝ)..t, f u
  have hP : Continuous P := intervalIntegral.continuous_primitive (fun a b ↦ hf.intervalIntegrable a b) 0
  apply ((hP.comp (continuous_id.add_const h)).sub hP).congr
  intro t
  simpa [P] using (eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 t) (hf.intervalIntegrable t (t + h)))).symm

/-- Titchmarsh, Lemma 10.21, p. 278. Each u between h and T occurs for exactly
h units of window starts. This gives the required first moment from a single
ordinary integral of the absolute mollified Hardy function. -/
private theorem spectralLineJet_window_mass {f : ℝ → ℝ} (hf : Continuous f) (hf₀ : ∀ u, 0 ≤ f u)
    {T h : ℝ} (hh : 0 ≤ h) (hT : h ≤ T) :
    h * (∫ u in h..T, f u) ≤ ∫ t in Ioc (0 : ℝ) T, ∫ u in t..t + h, f u := by
  have ht := hh.trans hT
  have hs (a b : ℝ) : (∫ s in (0 : ℝ)..b, f (a + s)) = ∫ s in a..a + b, f s := by
    simpa only [add_zero] using intervalIntegral.integral_comp_add_left (a := 0) (b := b) f a
  have hi : IntegrableOn (fun p : ℝ × ℝ ↦ f (p.1 + p.2)) (uIoc 0 h ×ˢ uIoc 0 T) := by
    apply ((hf.comp (continuous_fst.add continuous_snd)).continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    exact Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  rw [← intervalIntegral.integral_of_le ht]
  calc
    _ = ∫ r in (0 : ℝ)..h, ∫ u in h..T, f u := by simp
    _ ≤ ∫ r in (0 : ℝ)..h, ∫ u in r..r + T, f u := by
      apply intervalIntegral.integral_mono_on hh intervalIntegrable_const
        ((spectralLineJet_window_continuous hf T).intervalIntegrable _ _)
      intro r hr
      exact intervalIntegral.integral_mono_interval hr.2 hT (by linarith [hr.1])
        (Filter.Eventually.of_forall hf₀) (hf.intervalIntegrable _ _)
    _ = ∫ r in (0 : ℝ)..h, ∫ t in (0 : ℝ)..T, f (r + t) := by simp_rw [hs]
    _ = ∫ t in (0 : ℝ)..T, ∫ r in (0 : ℝ)..h, f (r + t) := intervalIntegral_intervalIntegral_swap hi
    _ = _ := intervalIntegral.integral_congr (fun t _ ↦ by simpa only [add_comm t] using hs t h)

/-- A nonnegative mollifier cannot create a sign change. Strict short-interval
cancellation of the mollified Hardy function detects an actual zeta ordinate. -/
private theorem spectralLineJet_zero_of_window_cancellation
    {w : ℝ → ℝ} (hw : ∀ u, 0 ≤ w u) {t h : ℝ} (hh : 0 ≤ h)
    (hc : |∫ u in t..t + h, w u * hardyZ u| < ∫ u in t..t + h, |w u * hardyZ u|) :
    ∃ u ∈ Icc t (t + h), riemannZeta (1 / 2 + (u : ℂ) * Complex.I) = 0 := by
  have ht : t ≤ t + h := by linarith
  by_contra! hn
  have hsign : (∀ u ∈ Icc t (t + h), 0 ≤ hardyZ u) ∨ (∀ u ∈ Icc t (t + h), hardyZ u ≤ 0) := by
    by_contra! h
    obtain ⟨⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩⟩ := h
    obtain ⟨u, hu, hz⟩ := isPreconnected_Icc.intermediate_value hx hy continuous_hardyZ.continuousOn
      (show 0 ∈ Icc (hardyZ x) (hardyZ y) from ⟨hx'.le, hy'.le⟩)
    exact hn u hu ((hardyZ_eq_zero_iff u).mp hz)
  apply hc.not_ge
  rcases hsign with pos | neg
  · have hp (u : ℝ) (hu : u ∈ Icc t (t + h)) : 0 ≤ w u * hardyZ u := mul_nonneg (hw u) (pos u hu)
    have he : (∫ u in t..t + h, |w u * hardyZ u|) = ∫ u in t..t + h, w u * hardyZ u :=
      intervalIntegral.integral_congr (fun u hu ↦ abs_of_nonneg (hp u (uIcc_of_le ht ▸ hu)))
    rw [he, abs_of_nonneg (intervalIntegral.integral_nonneg ht hp)]
  · have hp (u : ℝ) (hu : u ∈ Icc t (t + h)) : w u * hardyZ u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hw u) (neg u hu)
    have he : (∫ u in t..t + h, |w u * hardyZ u|) = ∫ u in t..t + h, -(w u * hardyZ u) :=
      intervalIntegral.integral_congr (fun u hu ↦ abs_of_nonpos (hp u (uIcc_of_le ht ▸ hu)))
    have hi := intervalIntegral.integral_nonneg (μ := volume) ht (fun u hu ↦ neg_nonneg.mpr (hp u hu))
    rw [intervalIntegral.integral_neg] at hi
    rw [he, intervalIntegral.integral_neg, abs_of_nonpos (neg_nonneg.mp hi)]

/-- Cauchy–Schwarz for the cancellation integral localized to a finite-measure
set of starting points. -/
private theorem spectralLineJet_window_cs {μ : Measure ℝ} [IsFiniteMeasure μ]
    {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    (∫ t, f t ∂μ) ^ 2 ≤ μ.real univ * ∫ t, (f t) ^ 2 ∂μ := by
  have hcs := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (f := fun t ↦ ‖f t‖) (g := fun _ ↦ (1 : ℝ))
    Real.HolderConjugate.two_two (by simpa using hf.norm) (memLp_const _)
  have hle : ‖∫ t, f t ∂μ‖ ≤ Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂μ) * Real.sqrt (μ.real univ) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    simpa [Real.sqrt_eq_rpow] using hcs
  have hs := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _),
    Real.sq_sqrt measureReal_nonneg, mul_comm] at hs
  simpa only [Real.norm_eq_abs, sq_abs] using hs

local notation "absWindow(" w ", " h ", " t ")" =>
  ∫ u in t..t + h, |w u * hardyZ u|
local notation "cancellation(" w ", " h ", " t ")" =>
  absWindow(w, h, t) - |∫ u in t..t + h, w u * hardyZ u|

/-- Titchmarsh, §10.22, pp. 278–279. Each distinct ordinate covers a set of
window starts of length at most h, even when it has arbitrarily high multiplicity.
The last windows may end at T + h. -/
private theorem spectralLineJet_window_count_bound {w : ℝ → ℝ} (hw : Continuous w)
    (hw₀ : ∀ u, 0 ≤ w u) {T h : ℝ} (hh : 0 ≤ h) (S : Finset ℝ)
    (hS : ∀ u ∈ Ioc (0 : ℝ) (T + h), riemannZeta (1 / 2 + (u : ℂ) * Complex.I) = 0 → u ∈ S) :
    (∫ t in Ioc (0 : ℝ) T, cancellation(w, h, t)) ^ 2 ≤
      (S.card : ℝ) * h * ∫ t in Ioc (0 : ℝ) T, absWindow(w, h, t) ^ 2 := by
  classical
  let K := Ioc (0 : ℝ) T
  let C := ⋃ u ∈ S, Icc (u - h) u
  let U := K ∩ C
  let A (t : ℝ) := absWindow(w, h, t)
  let D (t : ℝ) := cancellation(w, h, t)
  have hA : Continuous A := spectralLineJet_window_continuous (hw.mul continuous_hardyZ).abs h
  have hD : Continuous D := hA.sub (spectralLineJet_window_continuous (hw.mul continuous_hardyZ) h).abs
  have hDA (t : ℝ) : 0 ≤ D t ∧ D t ≤ A t :=
    ⟨sub_nonneg.mpr (intervalIntegral.abs_integral_le_integral_abs (by linarith)), sub_le_self _ (abs_nonneg _)⟩
  have hC : IsCompact C := S.finite_toSet.isCompact_biUnion (fun _ _ ↦ isCompact_Icc)
  have hU : MeasurableSet U := measurableSet_Ioc.inter hC.measurableSet
  have hUK : U ⊆ K := inter_subset_left
  have hUcc : U ⊆ Icc (0 : ℝ) T := hUK.trans Ioc_subset_Icc_self
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr
    (measure_ne_top_of_subset hUcc isCompact_Icc.measure_lt_top.ne)
  have hsupport : ∀ t ∈ K, D t ≠ 0 → t ∈ U := by
    intro t ht hn
    have hd := lt_of_le_of_ne (hDA t).1 (Ne.symm hn)
    obtain ⟨u, hu, hz⟩ := spectralLineJet_zero_of_window_cancellation hw₀ hh (sub_pos.mp hd)
    have huS := hS u ⟨lt_of_lt_of_le ht.1 hu.1, (hu.2.trans (add_le_add_left ht.2 h))⟩ hz
    exact ⟨ht, mem_iUnion₂.mpr ⟨u, huS, sub_le_iff_le_add.mpr hu.2, hu.1⟩⟩
  have hloc : (∫ t in K, D t) = ∫ t in U, D t := by
    calc
      _ = ∫ t in K, U.indicator D t := setIntegral_congr_fun measurableSet_Ioc (fun t ht ↦ by
        by_cases hu : t ∈ U
        · rw [indicator_of_mem hu]
        · rw [indicator_of_notMem hu]
          exact not_ne_iff.mp (fun hn ↦ hu (hsupport t ht hn)))
      _ = _ := by rw [integral_indicator hU, Measure.restrict_restrict hU, inter_eq_left.mpr hUK]
  have hs : volume.real U ≤ (S.card : ℝ) * h := calc
    _ ≤ volume.real C := measureReal_mono inter_subset_right hC.measure_lt_top.ne
    _ ≤ ∑ u ∈ S, volume.real (Icc (u - h) u) := measureReal_biUnion_finset_le S _
    _ = _ := by simp [Real.volume_real_Icc_of_le (sub_le_self _ hh)]
  have intK {f : ℝ → ℝ} (hf : Continuous f) : IntegrableOn f K :=
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hcs := spectralLineJet_window_cs (μ := volume.restrict U) (f := D)
    ((memLp_two_iff_integrable_sq hD.aestronglyMeasurable).mpr ((intK (hD.pow 2)).mono_set hUK))
  have hsq : (∫ t in U, D t ^ 2) ≤ ∫ t in K, A t ^ 2 := calc
    _ ≤ ∫ t in U, A t ^ 2 := setIntegral_mono_on ((intK (hD.pow 2)).mono_set hUK)
      ((intK (hA.pow 2)).mono_set hUK) hU (fun t _ ↦ pow_le_pow_left₀ (hDA t).1 (hDA t).2 2)
    _ ≤ _ := setIntegral_mono_set (intK (hA.pow 2)) (Filter.Eventually.of_forall fun t ↦ sq_nonneg _)
      (Filter.Eventually.of_forall fun _ hu ↦ hUK hu)
  change (∫ t in K, D t) ^ 2 ≤ (S.card : ℝ) * h * ∫ t in K, A t ^ 2
  rw [hloc]
  have hcs' : (∫ t in U, D t) ^ 2 ≤ volume.real U * ∫ t in U, D t ^ 2 := by simpa using hcs
  exact hcs'.trans (mul_le_mul hs hsq (integral_nonneg fun _ ↦ sq_nonneg _) (by positivity))

private theorem spectralLineJet_count_of_window_moments {w : ℝ → ℝ} (hw : Continuous w)
    (hw₀ : ∀ u, 0 ≤ w u) (T M : ℕ) {h : ℝ} (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (hm : (M : ℝ) * h * (∫ t in Ioc (0 : ℝ) T, absWindow(w, h, t) ^ 2) <
      (∫ t in Ioc (0 : ℝ) T, cancellation(w, h, t)) ^ 2) :
    ∃ S : Finset ℝ, M < S.card ∧
      ∀ u ∈ S, u ∈ Ioc (0 : ℝ) (T + 1) ∧ riemannZeta (1 / 2 + (u : ℂ) * Complex.I) = 0 := by
  classical
  let Z := {u : ℝ | u ∈ Ioc (0 : ℝ) (T + 1) ∧ riemannZeta (1 / 2 + (u : ℂ) * Complex.I) = 0}
  by_cases hZ : Z.Finite
  · refine ⟨hZ.toFinset, ?_, fun u hu ↦ hZ.mem_toFinset.mp hu⟩
    have hb := spectralLineJet_window_count_bound hw hw₀ hh hZ.toFinset (T := T) (by
      intro u hu hz
      exact hZ.mem_toFinset.mpr ⟨⟨hu.1, by linarith [hu.2]⟩,hz⟩)
    by_contra! hcard
    apply hm.not_ge (hb.trans ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hh)
      (integral_nonneg fun _ ↦ sq_nonneg _)
  · obtain ⟨S, hS, hcard⟩ := (Set.not_finite.mp hZ).exists_subset_card_eq (M + 1)
    exact ⟨S, by omega, fun _ hu ↦ hS hu⟩


/-- Remaining classical input, Titchmarsh §§10.17, 10.19, 10.21–10.22,
pp. 276–279. A finite mollifier with real coefficients has a positive integral of the absolute mollified Hardy function
over the bulk interval [h,T]. Its signed window second moment is small in comparison, and its absolute
second moment is bounded at the same scale. Selberg takes h proportional to
1/log T, hence arbitrarily small. All integrals are of the mollified Hardy
function, with no zero-count premise. -/
private theorem spectralLineJet_selberg_mollified_window_moments :
    ∃ c > (0 : ℝ), ∀ ε > (0 : ℝ), ∃ (T N : ℕ) (b : ℕ → ℝ) (h : ℝ),
      1 ≤ T ∧ 1 ≤ N ∧ b 1 = 1 ∧ (∀ n ∈ Finset.Icc 1 N, |b n| ≤ 1) ∧
      0 < h ∧ h ≤ 1 ∧ h < ε ∧
      let w := spectralLineJet_selbergWeight T N b
      let M := h * ∫ u in h..(T : ℝ), |w u * hardyZ u|
      0 < M ∧
        4 * T * (∫ t in Ioc (0 : ℝ) T, (∫ u in t..t + h, w u * hardyZ u) ^ 2) ≤ M ^ 2 ∧
        c * T * (∫ t in Ioc (0 : ℝ) T, absWindow(w, h, t) ^ 2) ≤ M ^ 2 := Selberg.moments

/-- Selberg's theorem in the form used to refute (10.3.1.18), p. 451. For every `k`, some
height `T` has more than `(k + 1) * (T + 1)` distinct positive critical-line zeta ordinates
at most `T`. See Titchmarsh, §10.22, pp. 278–279. -/
theorem spectralLineJet_rational_critical_zero_count (k : ℕ) :
    ∃ T : ℕ, ∃ S : Finset ℝ, (k + 1) * (T + 1) < S.card ∧
      ∀ t ∈ S, t ∈ Ioc (0 : ℝ) T ∧ riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 := by
  obtain ⟨c, hc, hm⟩ := spectralLineJet_selberg_mollified_window_moments
  obtain ⟨T, N, b, h, hT, -,-,-,hh, hh₁, heps, hP, hB₀, hA₀⟩ :=
    hm (c / (16 * (k + 1))) (by positivity)
  let w := spectralLineJet_selbergWeight T N b
  obtain ⟨hw, hw₀⟩ := spectralLineJet_selbergWeight_spec T N b
  let K := Ioc (0 : ℝ) T
  let A (t : ℝ) := absWindow(w, h, t)
  let B (t : ℝ) := ∫ u in t..t + h, w u * hardyZ u
  let M := ∫ t in K, A t
  let V := ∫ t in K, A t ^ 2
  let L := ∫ t in K, |B t|
  let P := h * ∫ u in h..(T : ℝ), |w u * hardyZ u|
  change 0 < P at hP
  have hPM : P ≤ M := spectralLineJet_window_mass (hw.mul continuous_hardyZ).abs
    (fun _ ↦ abs_nonneg _) hh.le (hh₁.trans (by exact_mod_cast hT))
  have hM := hP.trans_le hPM
  have hB : 4 * (T : ℝ) * (∫ t in K, B t ^ 2) ≤ M ^ 2 :=
    hB₀.trans (pow_le_pow_left₀ hP.le hPM 2)
  have hA : c * (T : ℝ) * V ≤ M ^ 2 := hA₀.trans (pow_le_pow_left₀ hP.le hPM 2)
  have hAc : Continuous A := spectralLineJet_window_continuous (hw.mul continuous_hardyZ).abs h
  have hBc : Continuous B := spectralLineJet_window_continuous (hw.mul continuous_hardyZ) h
  have hi {f : ℝ → ℝ} (hf : Continuous f) : IntegrableOn f K :=
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr
    (measure_ne_top_of_subset Ioc_subset_Icc_self isCompact_Icc.measure_lt_top.ne)
  have hcs := spectralLineJet_window_cs (μ := volume.restrict K) (f := fun t ↦ |B t|)
    ((memLp_two_iff_integrable_sq hBc.abs.aestronglyMeasurable).mpr (hi (hBc.abs.pow 2)))
  have hs : L ^ 2 ≤ (T : ℝ) * ∫ t in K, B t ^ 2 := by
    simpa [L, K, sq_abs, Real.volume_real_Ioc_of_le] using hcs
  have hL : 2 * L ≤ M := by nlinarith [sq_nonneg (2 * L - M)]
  have hΔ : (∫ t in K, cancellation(w, h, t)) = M - L :=
    integral_sub (hi hAc) (hi hBc.abs)
  have hV : 0 ≤ V := integral_nonneg fun _ ↦ sq_nonneg _
  have hcoef : ((k + 1 : ℕ) : ℝ) * ((T + 2 : ℕ) : ℝ) * h < c * T / 4 := by
    have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
    have he := (lt_div_iff₀ (by positivity : (0 : ℝ)<16 * (k + 1))).mp heps
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : (T : ℝ)+2 ≤ 3 * T) (by positivity : 0 ≤ ((k : ℝ)+1) * h),
      mul_lt_mul_of_pos_right he (by linarith : (0 : ℝ)<T), mul_pos hc (by linarith : (0 : ℝ)<T)]
  have hsmall : (↑((k + 1) * (T + 2) : ℕ) : ℝ) * h * V < (M - L) ^ 2 := by
    push_cast at hcoef ⊢
    rcases hV.eq_or_lt with hv | hv
    · rw [← hv, mul_zero]
      exact sq_pos_of_pos (by linarith)
    · have hl := mul_lt_mul_of_pos_right hcoef hv
      nlinarith [sq_nonneg (M - 2 * L), mul_nonneg (by linarith : 0 ≤ M - 2 * L) (by linarith : 0 ≤ 3 * M - 2 * L)]
  obtain ⟨S, hcard, hS⟩ := spectralLineJet_count_of_window_moments hw hw₀ T ((k + 1) * (T + 2))
    hh.le hh₁ (by change _ * h * V < (∫ t in K, cancellation(w, h, t)) ^ 2; rwa [hΔ])
  exact ⟨T + 1, S, hcard, fun t ht ↦ by simpa only [Nat.cast_add, Nat.cast_one] using hS t ht⟩

end RiemannMasullo
