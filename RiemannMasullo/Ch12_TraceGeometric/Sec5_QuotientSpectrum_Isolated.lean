module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import RiemannMasullo.Ch10_TraceSpectral.Sec2
public import RiemannMasullo.ForMathlib.Analysis.Normed.Operator.QuotientSpectrum
import RiemannMasullo.ForMathlib.Analysis.Complex.Blaschke
import RiemannMasullo.ForMathlib.Analysis.Complex.ClusteredZeros
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Spectrum of translation on the rational order-zero theta quotient

Heights differing by an integral multiple of $2\pi$ give the same eigenvalue of
translation by log norm one. The distinct critical-line zero count of §10.3 supplies
arbitrarily many zeros in one period. The strip-to-disk chart then gives small
restrictions of Mellin evaluations to theta at each target point in the strip.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Metric NumberField Set
open scoped NNReal Topology

namespace RiemannMasullo.Isolated

/-- The classical counting input in §10.3 gives arbitrarily many distinct critical-line
zeros in a single interval of length $2\pi$ whose left endpoint is a multiple of $2\pi$. -/
theorem rational_critical_zeros_in_periodic_windows
    (hcount : ∀ k : ℕ, ∃ T : ℕ, ∃ S : Finset ℝ, (k + 1) * (T + 1) < S.card ∧
      ∀ t ∈ S, t ∈ Ioc (0 : ℝ) T ∧ riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0)
    (k : ℕ) :
    ∃ m : ℕ, ∃ Z : Finset ℝ, k < Z.card ∧ ∀ t ∈ Z,
      t - 2 * Real.pi * m ∈ Ico (0 : ℝ) (2 * Real.pi) ∧
        riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 := by
  classical
  obtain ⟨T, S, hcard, hS⟩ := hcount k
  let P := 2 * Real.pi
  have hP : 1 ≤ P := by dsimp [P]; linarith [Real.pi_gt_three]
  have hpos : 0 < P := zero_lt_one.trans_le hP
  let bin (t : ℝ) := ⌊t / P⌋₊
  have hmap (t) (ht : t ∈ S) : bin t ∈ Finset.range (T + 1) := by
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    exact Nat.floor_le_of_le ((div_le_self (hS t ht).1.1.le hP).trans (hS t ht).1.2)
  have hmany : (Finset.range (T + 1)).card * k < S.card := by
    rw [Finset.card_range]
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_succ k)) (by rwa [Nat.mul_comm])
  obtain ⟨m, _, hm⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmap hmany
  refine ⟨m, S.filter (fun t ↦ bin t = m), hm, fun t ht ↦ ?_⟩
  obtain ⟨ht, hbin⟩ := Finset.mem_filter.mp ht
  refine ⟨?_, (hS t ht).2⟩
  have hlo : (bin t : ℝ) ≤ t / P := Nat.floor_le (div_nonneg (hS t ht).1.1.le hpos.le)
  have hhi : t / P < (bin t : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [hbin] at hlo hhi
  change 0 ≤ t - P * m ∧ t - P * m < P
  constructor <;> nlinarith [(le_div_iff₀ hpos).mp hlo, (div_lt_iff₀ hpos).mp hhi]

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "μ𝔽" => ideleClassTamagawaMeasure ℚ
local notation "m𝔽" => (continuousIdeleClassNorm ℚ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "half" => (1 / 2 : ℝ)
local notation "W" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm ℚ) (-half) half 0
local notation "hI" => (show -half ≤ half by norm_num)
local notation "Θ" => globalThetaSobolev ℚ half hI (le_refl (0 : ℝ))
local notation "trans" => hardySobolevTranslation μ𝔽 m𝔽 (-half) half 0 hI (le_refl (0 : ℝ))
local notation "Q" => spectralSobolevQuotient ℚ half hI (le_refl (0 : ℝ))

/-- The left translation induced on the rational order-zero theta quotient. -/
def rationalThetaQuotientTranslation (g : C𝔽) : Q →L[ℂ] Q :=
  (Θ).liftQL ((Θ).mkQL.comp (trans g)) (by
    intro x hx
    change (Θ).mkQ (trans g x) = 0
    apply (Submodule.Quotient.mk_eq_zero (Θ)).mpr
    obtain ⟨ρ, hρ, _⟩ := exists_globalThetaSobolevAction (F := ℚ) half hI (le_refl (0 : ℝ))
    exact (hρ g ⟨x, hx⟩) ▸ (ρ g ⟨x, hx⟩).property)

/-- On quotient representatives the induced operator is ambient left translation. -/
@[simp] theorem rationalThetaQuotientTranslation_mkQ (g : C𝔽) (x : W) :
    rationalThetaQuotientTranslation g ((Θ).mkQ x) = (Θ).mkQ (trans g x) := rfl

/-- For the rational order-zero quotient in Theorem 12.5.1.1, pp. 519–520, pack the
critical-line zeros into periodic windows and apply the disk estimate to normalized Mellin
evaluations. The hypotheses state the zero count and the properties of the disk-coordinate
evaluations: their norms at the target, translation law, uniform analytic bound on theta,
and vanishing at the recentered zeta zeros. -/
private theorem spectrum_of_disk_evaluations
    (g : C𝔽)
    (z w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) (K : Set ℂ) (hcompact : IsCompact K)
    (hK : K ⊆ ball 0 1) (φ : ℝ → ℂ) (hφ : MapsTo φ (Ico 0 (2 * Real.pi)) K)
    (hinj : InjOn φ (Ico 0 (2 * Real.pi)))
    (L : ℕ → ℂ → W →L[ℂ] ℂ) (hnorm : ∀ m, ‖L m w‖ = 1)
    (heigen : ∀ m (x : W), L m w (trans g x) = z * L m w x)
    (han : ∀ m (x : Θ), AnalyticOnNhd ℂ (fun u ↦ L m u x.val) (ball 0 1))
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ m (x : Θ), ∀ u ∈ ball (0 : ℂ) 1, ‖L m u x.val‖ ≤ C * ‖x‖)
    (hzero : ∀ (m : ℕ) (t : ℝ), t - 2 * Real.pi * m ∈ Ico 0 (2 * Real.pi) →
      riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 →
      ∀ x : Θ, L m (φ (t - 2 * Real.pi * m)) x.val = 0)
    (hcount : ∀ k : ℕ, ∃ T : ℕ, ∃ S : Finset ℝ, (k + 1) * (T + 1) < S.card ∧
      ∀ t ∈ S, t ∈ Ioc (0 : ℝ) T ∧ riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) :
    z ∈ spectrum ℂ (rationalThetaQuotientTranslation g) := by
  classical
  obtain ⟨q, hq₀, hq₁, hdecay⟩ :=
    Complex.exists_geometric_bound_of_zeros_in_compact hcompact hK hw
  apply mem_spectrum_quotient_of_small_restrictions (Θ) (trans g) _
    (rationalThetaQuotientTranslation_mkQ g)
  intro ε hε
  have hlim : Tendsto (fun n : ℕ ↦ C * q ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁).const_mul C
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hε).exists
  obtain ⟨m, Z, hZ, hwin⟩ := rational_critical_zeros_in_periodic_windows hcount n
  let P (t : ℝ) := φ (t - 2 * Real.pi * m)
  let S := Z.image P
  have hin : InjOn P (↑Z) := by
    intro t ht u hu he
    exact sub_left_inj.mp (hinj (hwin t ht).1 (hwin u hu).1 he)
  have hcard : S.card = Z.card := Finset.card_image_of_injOn hin
  have hSK : (↑S : Set ℂ) ⊆ K := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    exact hφ (hwin t ht).1
  refine ⟨L m w, hnorm m, heigen m, lt_of_le_of_lt ?_ hn⟩
  apply ((L m w).comp (Θ).subtypeL).opNorm_le_bound (by positivity)
  intro x
  have hv := hdecay S hSK (fun u ↦ L m u x.val) (C * ‖x‖) (han m x) (hb m x)
    (fun u hu ↦ by
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
      exact hzero m t (hwin t ht).1 (hwin t ht).2 x)
  calc
    ‖L m w x.val‖ ≤ (C * ‖x‖) * q ^ S.card := hv
    _ ≤ (C * ‖x‖) * q ^ n := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq₀ hq₁.le (hcard ▸ hZ.le))
        (mul_nonneg hC (norm_nonneg x))
    _ = (C * q ^ n) * ‖x‖ := by ring

/-- For the translation of §12.5, pp. 519–520, a normalized Mellin evaluation family on
an open substrip puts `exp s` in the spectrum of the rational order-zero quotient. The
arithmetic input is the distinct critical-line zero count used in §10.3. -/
theorem exp_mem_rationalThetaQuotientTranslation_spectrum (g : C𝔽) (s : ℂ)
    {a : ℝ} (hs : |s.re| < a) (L : ℂ → W →L[ℂ] ℂ)
    (hnorm : ∀ t : ℝ, ‖L (s + t * Complex.I)‖ = 1)
    (heigen : ∀ v : ℂ, |v.re| < a → ∀ x : W, L v (trans g x) = Complex.exp v * L v x)
    (han : ∀ x : Θ, AnalyticOnNhd ℂ (fun v ↦ L v x.val) {v : ℂ | |v.re| < a})
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ (x : Θ) (v : ℂ), |v.re| < a → ‖L v x.val‖ ≤ C * ‖x‖)
    (hzero : ∀ t : ℝ, riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0 →
      ∀ x : Θ, L (t * Complex.I) x.val = 0)
    (hcount : ∀ k : ℕ, ∃ H : ℕ, ∃ S : Finset ℝ, (k + 1) * (H + 1) < S.card ∧
      ∀ t ∈ S, t ∈ Ioc (0 : ℝ) H ∧ riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) :
    Complex.exp s ∈ spectrum ℂ (rationalThetaQuotientTranslation g) := by
  let k := (Real.pi / 2) / a
  have ha : 0 < a := (abs_nonneg _).trans_lt hs
  have hk : 0 < k := div_pos (by positivity) ha
  have hwidth : (Real.pi / 2) / k = a := by dsimp [k]; field_simp
  let D := stripBlaschkeFromDisk 0 k
  let B := stripBlaschkeToDisk 0 k
  have hB {v : ℂ} (hv : |v.re| < a) : B v ∈ ball 0 1 :=
    stripBlaschkeToDisk_mem hk (by simpa [hwidth] using hv)
  have hD {u : ℂ} (hu : u ∈ ball 0 1) : |(D u).re| < a := by
    simpa [D, hwidth] using stripBlaschkeFromDisk_mem_strip (w₀ := 0) hk hu
  have hDB {v : ℂ} (hv : |v.re| < a) : D (B v) = v :=
    stripBlaschkeFromDisk_toDisk hk (by simpa [hwidth] using hv)
  let axis (t : ℝ) : ℂ := t * Complex.I
  have haxis (t : ℝ) : |(axis t).re| < a := by simpa [axis] using ha
  let φ := B ∘ axis
  let K := φ '' Icc 0 (2 * Real.pi)
  have hcont : Continuous φ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (stripBlaschkeToDisk_analytic (w₀ := 0) hk (by simpa [hwidth] using haxis t)).continuousAt.comp
      (by dsimp [axis]; fun_prop : ContinuousAt axis t)
  have hK : K ⊆ ball 0 1 := by rintro _ ⟨t, _, rfl⟩; exact hB (haxis t)
  have hcompact : IsCompact K := isCompact_Icc.image hcont
  let p (m : ℕ) : ℝ := 2 * Real.pi * m
  have hshift (m : ℕ) (v : ℂ) : (v + axis (p m)).re = v.re := by simp [axis]
  refine spectrum_of_disk_evaluations g (Complex.exp s) (B s) (hB hs) K hcompact hK φ
    (fun t ht ↦ ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩) ?_ (fun m u ↦ L (D u + axis (p m))) ?_ ?_ ?_ hC ?_ ?_
    hcount
  · intro t _ u _ he
    have he' : axis t = axis u := (hDB (haxis t)).symm.trans ((congrArg D he).trans (hDB (haxis u)))
    simpa [axis] using congrArg Complex.im he'
  · intro m
    rw [hDB hs]
    exact hnorm _
  · intro m x
    rw [hDB hs, heigen _ (by rwa [hshift]), Complex.exp_add]
    have hperiod : axis (p m) = (m : ℂ) * (2 * Real.pi * Complex.I) := by push_cast [axis, p]; ring
    rw [hperiod, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  · intro m x u hu
    exact (han x _ (by rw [Set.mem_ofPred_eq, hshift]; exact hD hu)).comp
      ((stripBlaschkeFromDisk_analyticAt_deriv_ne_zero (w₀ := 0) hk hu).1.add analyticAt_const)
  · intro m x u hu
    exact hb x _ (by rw [hshift]; exact hD hu)
  · intro m t _ ht x
    change L (D (B (axis (t - p m))) + axis (p m)) x.val = 0
    rw [hDB (haxis _), show axis (t - p m) + axis (p m) = axis t by dsimp [axis]; push_cast; ring]
    exact hzero t ht x

end RiemannMasullo.Isolated
