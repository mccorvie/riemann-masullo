module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import RiemannMasullo.Ch10_TraceSpectral.Sec2
public import RiemannMasullo.Ch12_TraceGeometric.Sec5_MellinEvaluation
public import RiemannMasullo.ForMathlib.Analysis.Normed.Operator.QuotientSpectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.ForMathlib.Analysis.Complex.Blaschke
import RiemannMasullo.ForMathlib.Analysis.Complex.ClusteredZeros
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Spectrum of translation on the rational order-zero theta quotient

Heights differing by an integral multiple of $2\pi$ give the same eigenvalue of
translation by log norm one. The distinct critical-line zero count of §10.3 supplies
arbitrarily many zeros in one period. The strip-to-disk chart then gives small
restrictions of Mellin evaluations to theta at each target point in the strip. This fills
the closed annulus and gives the exact norms of all positive and negative translation powers.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Metric NumberField Set
open scoped NNReal Topology

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

-- The classical counting statement in §10.3 (Sec3_Printed).
local notation "CriticalZeroCount" => ∀ k : ℕ, ∃ H : ℕ, ∃ S : Finset ℝ,
  (k + 1) * (H + 1) < S.card ∧ ∀ t ∈ S, t ∈ Ioc (0 : ℝ) H ∧
    riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0

/-- The classical counting input in §10.3 gives arbitrarily many distinct critical-line
zeros in a single interval of length $2\pi$ whose left endpoint is a multiple of $2\pi$. -/
theorem rational_critical_zeros_in_periodic_windows
    (hcount : CriticalZeroCount)
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
    (hcount : CriticalZeroCount) :
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
    (hcount : CriticalZeroCount) :
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

/-- At each critical-line Riemann zeta zero, its Mellin evaluation vanishes
on the rational theta subspace of the order-zero critical strip. -/
theorem rationalTheta_mellin_eq_zero_of_riemannZeta_zero (t : ℝ)
    (ht : riemannZeta (1 / 2 + (t : ℂ) * Complex.I) = 0) (x : Θ) :
    (∫ y : C𝔽, x.val y * Complex.exp (t * Complex.I * logIdeleClassNorm ℚ y) ∂μ𝔽) = 0 := by
  let z : ℂ := 1 / 2 + (t : ℂ) * Complex.I
  have hre : z.re = 1 / 2 := by simp [z, Complex.mul_re]
  have hne : z ≠ 1 := fun e ↦ by norm_num [e] at hre
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  have hz : 0 < meromorphicOrderAt riemannZeta z := by
    apply (tendsto_zero_iff_meromorphicOrderAt_pos (hm z (mem_univ z))).mp
    change riemannZeta z = 0 at ht
    rw [← ht]
    exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt
  have htwo : meromorphicOrderAt riemannZeta (2 : ℂ) = 0 :=
    (analyticOn_riemannZeta _ (by norm_num : (2 : ℂ) ≠ 1)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have hfin := hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ z) (by rw [htwo]; simp)
  have hnat : 0 < (meromorphicOrderAt riemannZeta z).untop₀.toNat := by
    rw [← WithTop.coe_untop₀_of_ne_top hfin] at hz
    have hint : 0 < (meromorphicOrderAt riemannZeta z).untop₀ := WithTop.coe_lt_coe.mp hz
    omega
  let χ : PontryaginDual (ideleClassNorm ℚ).ker → PontryaginDual C𝔽 := fun _ ↦ 1
  let j : SpectralStripJetIndex χ half half 0 :=
    ⟨(1, 0, t, 0), by
      change 0 < spectralStripMultiplicity half 0 0 _
      rw [spectralStripMultiplicity_interior (by norm_num : (0 : ℝ) ∈ Ioo (-half) half)]
      change 0 < (meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽))
        (((half + 0 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).untop₀.toNat
      convert hnat using 1
      push_cast
      rw [meromorphicOrderAt_finiteHeckeL_continuation (1 : PontryaginDual C𝔽) hm (fun s ↦
        (dedekindZeta_rat_eq_riemannZeta s.property).symm.trans
          (finiteHeckeL_one_eq_dedekindZeta (K := ℚ) s).symm) (by rw [hre]; norm_num)]
      simp [z]⟩
  have hLp := spectralStripJet_memLp χ (by norm_num : 0 ≤ half) (le_refl (0 : ℝ)) j
  let u := hLp.toLp _
  have he := spectralStripJet_commonKernel_forward χ (by norm_num : 0 ≤ half) (le_refl 0) x.val x.property j
  change (∫ y : C𝔽, x.val y * u y ∂μ𝔽) = 0 at he
  refine (integral_congr_ae ?_).trans he
  filter_upwards [(tamagawa_absolutelyContinuous_orderZeroDualMeasure (F := ℚ)).ae_le (MemLp.coeFn_toLp hLp)] with y hy
  apply congrArg (x.val y * ·)
  refine (Eq.trans ?_ hy.symm)
  simp only [j, χ, spectralZeroJet, Complex.ofReal_zero, zero_add, pow_zero, mul_one]
  have hpos : 0 < ((ideleClassNorm ℚ y).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  change Complex.exp _ = (1 : ℂ) * (((ideleClassNorm ℚ y).val : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)
  rw [one_mul, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'), ← Complex.ofReal_log hpos.le]
  exact congrArg Complex.exp (mul_comm _ _)

/-- For the actual Tamagawa Mellin integral, the distinct critical-line zero count of
§10.3 places every exponential from the open strip in the rational quotient spectrum. -/
theorem exp_mem_rationalThetaQuotientTranslation_spectrum_of_zero_count (g : C𝔽)
    (hg : logIdeleClassNorm ℚ g = 1) (s : ℂ) (hstrip : |s.re| < half)
    (hcount : CriticalZeroCount) :
    Complex.exp s ∈ spectrum ℂ (rationalThetaQuotientTranslation g) := by
  obtain ⟨a, hs, ha⟩ := exists_between hstrip
  let d := ‖orderZeroMellinEvaluation (F := ℚ) s (hs.trans ha)‖
  have hd : 0 < d := orderZeroMellinEvaluation_norm_pos s (hs.trans ha)
  let c : ℂ := (d⁻¹ : ℝ)
  let L (v : ℂ) : W →L[ℂ] ℂ := if hv : |v.re| < half then
    c • orderZeroMellinEvaluation v hv else 0
  have hL {v : ℂ} (hv : |v.re| < half) : L v = c • orderZeroMellinEvaluation v hv := dite_eq_left hv
  have hLx {v : ℂ} (hv : |v.re| < half) (x : W) :
      L v x = c * ∫ y : C𝔽, x y * Complex.exp (v * logIdeleClassNorm ℚ y) ∂μ𝔽 := by
    rw [hL hv, smul_apply, smul_eq_mul, (orderZeroMellinEvaluation_apply v hv x).2]
  have ha₀ := (abs_nonneg _).trans_lt hs
  have ha' : |(a : ℂ).re| < half := by simpa [abs_of_pos ha₀] using ha
  refine exp_mem_rationalThetaQuotientTranslation_spectrum g s hs L ?_ ?_ ?_
    (C := ‖c‖ * ‖orderZeroMellinEvaluation (F := ℚ) (a : ℂ) ha'‖) (by positivity) ?_ ?_ hcount
  · intro t
    let v := s + (t : ℂ) * Complex.I
    have hvs : |v.re| = |s.re| := by simp [v]
    have hn := le_antisymm (orderZeroMellinEvaluation_norm_le (F := ℚ) hvs.le (hs.trans ha))
      (orderZeroMellinEvaluation_norm_le (F := ℚ) hvs.ge (show |v.re| < half from hvs.le.trans_lt (hs.trans ha)))
    change ‖L v‖ = 1
    rw [hL (hvs.le.trans_lt (hs.trans ha)), norm_smul, hn]
    change ‖((d⁻¹ : ℝ) : ℂ)‖ * d = 1
    simp [abs_of_pos hd, hd.ne']
  · intro v hv x
    rw [hL (hv.trans ha), smul_apply, smul_apply,
      smul_eq_mul, smul_eq_mul, orderZeroMellinEvaluation_translate, hg, Complex.ofReal_one, mul_one]
    ring
  · intro x
    have hx := (analyticOnNhd_orderZeroMellinIntegral x.val).mono
      (show {v : ℂ | |v.re| < a} ⊆ {v : ℂ | |v.re| < half} from fun _ hv ↦ lt_trans hv ha)
    apply (analyticOnNhd_const.mul hx).congr (isOpen_lt Complex.continuous_re.abs continuous_const)
    intro v hv
    exact (hLx (lt_trans hv ha) x.val).symm
  · intro x v hv
    have hva : |v.re| ≤ |(a : ℂ).re| := by simpa [abs_of_pos ha₀] using hv.le
    apply ((L v).le_opNorm x.val).trans
    rw [hL (hv.trans ha), norm_smul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (orderZeroMellinEvaluation_norm_le (F := ℚ) hva ha') (norm_nonneg _)) (norm_nonneg _)
  · intro t ht x
    rw [hLx (by simp), rationalTheta_mellin_eq_zero_of_riemannZeta_zero t ht x, mul_zero]

local notation "A" => rationalThetaQuotientTranslation

private theorem quotientTranslation_norm_le (g : C𝔽) :
    ‖A g‖ ≤ Real.exp (half * |logIdeleClassNorm ℚ g|) := by
  let C := Real.exp (half * |logIdeleClassNorm ℚ g|)
  have hC : 0 < C := Real.exp_pos _
  have hT := norm_hardySobolevTranslation_le μ𝔽 m𝔽 (-half) half 0 hI le_rfl g
  have hB : ‖trans g‖ ≤ C := by
    change ‖trans g‖ ≤ max (Real.exp (-half * logIdeleClassNorm ℚ g))
      (Real.exp (half * logIdeleClassNorm ℚ g)) * (1 + |logIdeleClassNorm ℚ g|) ^ ((0:ℝ)/2) at hT
    rw [zero_div, Real.rpow_zero, mul_one] at hT
    apply hT.trans (max_le (Real.exp_le_exp.mpr ?_) (Real.exp_le_exp.mpr ?_))
    · linarith [neg_le_abs (logIdeleClassNorm ℚ g)]
    · linarith [le_abs_self (logIdeleClassNorm ℚ g)]
  apply (A g).opNorm_le_bound hC.le
  intro q
  rw [mul_comm]
  apply (div_le_iff₀ hC).mp
  apply (QuotientAddGroup.le_norm_iff (S := (Θ).toAddSubgroup)).mpr
  intro x hx
  change (Θ).mkQ x = q at hx
  rw [← hx, rationalThetaQuotientTranslation_mkQ, div_le_iff₀ hC, mul_comm]
  exact (Submodule.Quotient.norm_mk_le (Θ) _).trans (((trans g).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hB (norm_nonneg _)))

private theorem quotientTranslation_mul (g h : C𝔽) : A g * A h = A (g*h) := by
  apply ContinuousLinearMap.ext
  intro q
  obtain ⟨x,rfl⟩ := (Θ).mkQ_surjective q
  simp only [mul_apply_eq_comp, rationalThetaQuotientTranslation_mkQ, map_mul]

private theorem quotientTranslation_one : A (1:C𝔽) = 1 := by
  apply ContinuousLinearMap.ext
  intro q
  obtain ⟨x,rfl⟩ := (Θ).mkQ_surjective q
  simp only [rationalThetaQuotientTranslation_mkQ, map_one, one_apply_eq_self]

private def quotientTranslationUnit (g : C𝔽) : (Q →L[ℂ] Q)ˣ :=
  ⟨A g, A g⁻¹, by rw [quotientTranslation_mul, mul_inv_cancel, quotientTranslation_one],
    by rw [quotientTranslation_mul, inv_mul_cancel, quotientTranslation_one]⟩

private theorem norm_le_of_mem_op_spectrum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (a : E →L[ℂ] E) {z : ℂ} (h : z ∈ spectrum ℂ a) :
    ‖z‖ ≤ ‖a‖ := by
  have hn : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  exact (spectrum.norm_le_norm_mul_of_mem (𝕜 := ℂ) (a := a) h).trans (mul_le_of_le_one_right (norm_nonneg a) hn)

private theorem quotientSpectrum_contains_closed_strip (g : C𝔽)
    (h : ∀ s : ℂ, |s.re| < half → Complex.exp s ∈ spectrum ℂ (A g)) :
    ∀ s : ℂ, |s.re| ≤ half → Complex.exp s ∈ spectrum ℂ (A g) := by
  intro s hs
  let f (r : ℝ) := Complex.exp ((r : ℂ) + (s.im : ℂ) * Complex.I)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hclosed := (spectrum.isClosed (𝕜 := ℂ) (A g)).preimage hf
  have ho : Ioo (-half) half ⊆ f ⁻¹' spectrum ℂ (A g) := by
    intro r hr
    apply h
    simpa using abs_lt.mpr hr
  have hc := closure_minimal ho hclosed
  rw [closure_Ioo (by norm_num : -half ≠ half)] at hc
  have hout := hc (abs_le.mp hs)
  simpa only [mem_preimage, f, Complex.re_add_im] using hout

/-- The spectrum of the rational order-zero quotient translation at log norm one is the
closed annulus of radii `exp (-1/2)` and `exp (1/2)`, given the classical zero count. -/
theorem rationalThetaQuotientTranslation_spectrum_eq_annulus (g : C𝔽)
    (hg : logIdeleClassNorm ℚ g = 1)
    (hcount : CriticalZeroCount) :
    spectrum ℂ (A g) = {z : ℂ | Real.exp (-half) ≤ ‖z‖ ∧ ‖z‖ ≤ Real.exp half} := by
  have h := fun s hs ↦ exp_mem_rationalThetaQuotientTranslation_spectrum_of_zero_count g hg s hs hcount
  ext z
  constructor
  · intro hz
    let U := quotientTranslationUnit g
    have hz' : z ≠ 0 := by
      intro hzero
      exact (spectrum.zero_notMem (R := ℂ) U.isUnit) (hzero ▸ hz)
    have hzunit := (spectrum.inv_mem_iff (r := Units.mk0 z hz') (a := U)).mp hz
    have hzinv : ‖z⁻¹‖ ≤ ‖A g⁻¹‖ := norm_le_of_mem_op_spectrum _ hzunit
    have hginv : logIdeleClassNorm ℚ g⁻¹ = -1 := by
      change Real.log ((m𝔽 g⁻¹).val : ℝ) = _
      change Real.log ((m𝔽 g).val : ℝ) = 1 at hg
      rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv, hg]
    have hi : ‖z‖⁻¹ ≤ Real.exp half := by
      simpa only [norm_inv, hginv, abs_neg, abs_one, mul_one] using hzinv.trans (quotientTranslation_norm_le g⁻¹)
    refine ⟨?_, ?_⟩
    · simpa only [Real.exp_neg, inv_inv] using inv_anti₀ (inv_pos.mpr (norm_pos_iff.mpr hz')) hi
    · simpa only [hg, abs_one, mul_one] using (norm_le_of_mem_op_spectrum _ hz).trans (quotientTranslation_norm_le g)
  · rintro ⟨hlo,hhi⟩
    have hz : z ≠ 0 := norm_pos_iff.mp ((Real.exp_pos _).trans_le hlo)
    rw [← Complex.exp_log hz]
    apply quotientSpectrum_contains_closed_strip g h
    rw [Complex.log_re, abs_le]
    exact ⟨(Real.le_log_iff_exp_le (norm_pos_iff.mpr hz)).mpr hlo,
      (Real.log_le_iff_le_exp (norm_pos_iff.mpr hz)).mpr hhi⟩

private theorem quotientTranslation_norm_pow_le (g : C𝔽) (hg : |logIdeleClassNorm ℚ g| = 1) (n : ℕ) :
    ‖A g ^ n‖ ≤ Real.exp (n * half) := by
  have hrep (j : ℕ) : A g ^ j = A (g ^ j) := by
    induction j with
    | zero => simp only [pow_zero, quotientTranslation_one]
    | succ j ih => rw [pow_succ, ih, quotientTranslation_mul, pow_succ]
  rw [hrep]
  have hlog : logIdeleClassNorm ℚ (g ^ n) = n * logIdeleClassNorm ℚ g := by
    change Real.log ((m𝔽 (g ^ n)).val : ℝ) = _
    rw [map_pow, Units.val_pow_eq_pow_val, NNReal.coe_pow, Real.log_pow]
    rfl
  simpa only [hlog, abs_mul, hg, mul_one, abs_of_nonneg (Nat.cast_nonneg n (α := ℝ)), mul_comm half] using quotientTranslation_norm_le (g ^ n)

/-- The norm of every nonnegative power attains the ambient upper bound. -/
theorem rationalThetaQuotientTranslation_norm_pow (g : C𝔽) (hg : logIdeleClassNorm ℚ g = 1)
    (hcount : CriticalZeroCount) (n : ℕ) :
    ‖A g ^ n‖ = Real.exp (n * half) := by
  have h := fun s hs ↦ exp_mem_rationalThetaQuotientTranslation_spectrum_of_zero_count g hg s hs hcount
  have hb := quotientSpectrum_contains_closed_strip g h (half : ℂ) (by norm_num)
  have hp := norm_le_of_mem_op_spectrum _ (spectrum.pow_mem_pow (A g) n hb)
  rw [norm_pow, Complex.norm_exp, Complex.ofReal_re, ← Real.exp_nat_mul] at hp
  apply le_antisymm _ hp
  exact quotientTranslation_norm_pow_le g (by simp only [hg, abs_one]) n

/-- The inverse translator has the same sharp power norms, using the inner
boundary of the original spectrum. -/
theorem rationalThetaQuotientTranslation_norm_inv_pow (g : C𝔽) (hg : logIdeleClassNorm ℚ g = 1)
    (hcount : CriticalZeroCount) (n : ℕ) :
    ‖A g⁻¹ ^ n‖ = Real.exp (n * half) := by
  have h := fun s hs ↦ exp_mem_rationalThetaQuotientTranslation_spectrum_of_zero_count g hg s hs hcount
  let U := quotientTranslationUnit g
  let z := Complex.exp (-(half : ℂ))
  have hz : z ∈ spectrum ℂ (A g) := quotientSpectrum_contains_closed_strip g h _ (by norm_num)
  have hu := (spectrum.inv_mem_iff (r := Units.mk0 z (Complex.exp_ne_zero _)) (a := U)).mp hz
  have hi : Complex.exp (half : ℂ) ∈ spectrum ℂ (A g⁻¹) := by
    change z⁻¹ ∈ spectrum ℂ (A g⁻¹) at hu
    simpa only [z, Complex.exp_neg, inv_inv] using hu
  have hp := norm_le_of_mem_op_spectrum _ (spectrum.pow_mem_pow (A g⁻¹) n hi)
  rw [norm_pow, Complex.norm_exp, Complex.ofReal_re, ← Real.exp_nat_mul] at hp
  refine le_antisymm (quotientTranslation_norm_pow_le _ ?_ n) hp
  change |Real.log ((m𝔽 g⁻¹).val : ℝ)| = 1
  change Real.log ((m𝔽 g).val : ℝ) = 1 at hg
  rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv, hg, abs_neg, abs_one]

/-- Every rate strictly below `1/2` leaves some rescaled positive orbit unbounded. -/
theorem exists_unbounded_rationalThetaQuotientTranslation_orbit (g : C𝔽)
    (hg : logIdeleClassNorm ℚ g = 1) (hcount : CriticalZeroCount)
    {α : ℝ} (hα : α < half) : ∃ x : Q, ∀ C : ℝ, ∃ n : ℕ,
      C < Real.exp (-(α * n)) * ‖(A g ^ n) x‖ := by
  have hz : (Real.exp half : ℂ) ∈ spectrum ℂ (A g) := by
    rw [rationalThetaQuotientTranslation_spectrum_eq_annulus g hg hcount]
    simp only [mem_ofPred_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact ⟨Real.exp_le_exp.mpr (by norm_num), le_rfl⟩
  obtain ⟨x, hx⟩ := exists_unbounded_rescaled_orbit_of_mem_spectrum (A g) hz (Real.exp_pos α)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      Real.exp_lt_exp.mpr hα)
  refine ⟨x, fun C ↦ ?_⟩
  obtain ⟨n, hn⟩ := hx C
  refine ⟨n, ?_⟩
  simpa only [mul_comm α (n : ℝ), Real.exp_neg, Real.exp_nat_mul, div_eq_inv_mul] using hn

end RiemannMasullo.Isolated
