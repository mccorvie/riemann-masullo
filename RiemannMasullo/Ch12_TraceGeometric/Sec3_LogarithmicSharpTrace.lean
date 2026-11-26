module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_RadialPrimeTrace
import RiemannMasullo.AppB_AnalyticNT.Sec6
import RiemannMasullo.Ch13_ZerosHecke.Targets

/-! # Quantitative signed trace comparison from the classical zero-free region

A strip narrower than the full critical strip retains every zero through a
prescribed height. With a positive-log test the remaining Mellin samples have
arbitrary power decay in that height, uniformly in the Sobolev order.
-/

@[expose] public noncomputable section

open Classical Filter MeasureTheory Set NumberField
open scoped ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instFiniteCompletionUnitsLocallyCompactSec4b instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSIdeleLocallyCompactSec1 instSIdeleT2Sec4

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Pl" => IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)
local notation "X" => (1 : PontryaginDual Cℚ)
local notation "L₀" => continuedCompletedHeckeL X
local notation "D₀" => MeromorphicOn.divisor L₀ univ
local notation "D" => MeromorphicOn.divisor completedRiemannZeta univ
local notation "Z" => {z : ℂ // 0 < D z}
local notation "r(" z ")" => (D (z : Z).val).toNat
local notation "keep(" a ", " s ", " z ")" => spectralStripMultiplicity a s ((z : Z).val.re - 1 / 2) (r(z))
local notation "w(" A ", " B ", " Y ")" => ((1 / 2 : ℝ) - A / Real.log (B * (Y + 3)))
local notation "V" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "band(" ha ")" => (neg_nonpos.mpr ha |>.trans ha)
local notation "Q(" ha ", " hs ")" => spectralSobolevQuotient ℚ (1 / 2) (band(ha)) (zero_lt_one.trans hs).le
local notation "radial(" φ ", " H ")" => ∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x =
  (H : ℝ → ℂ) (Real.log ((ideleClassNorm ℚ x : ℝ≥0) : ℝ))
local notation "rep(" T ", " φ ", " ha ", " hs ")" =>
  (T : nuclearEndomorphisms Q(ha, hs)).val =
    spectralConvolution (F := ℚ) (1 / 2) (band(ha)) (zero_lt_one.trans hs).le φ

private theorem reflected_site (ρ : Z) : 0 < D (1 - ρ.val) := by
  obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec X
  obtain ⟨ε, hε, hn, he⟩ := completedHeckeL_continuation_functionalEquation X L₀ L₀
    hL heq hL (by simpa using heq)
  let f := fun z : ℂ ↦ 1 - z
  have hc := meromorphicOrderAt_comp_of_deriv_ne_zero (f := L₀)
    (show AnalyticAt ℂ f ρ.val by dsimp [f]; fun_prop) (show deriv f ρ.val ≠ 0 by simp [f])
  rw [show L₀ ∘ f = ε * L₀ from funext he,
    meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt ρ.val) (hn ρ.val)] at hc
  change 0 < D (1 - ρ.val)
  rw [← DFunLike.congr_fun divisor_rat_principal_eq_zeta (1 - ρ.val)]
  have hp : 0 < D₀ ρ.val := by rw [divisor_rat_principal_eq_zeta]; exact ρ.property
  rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _)] at hp ⊢
  exact (congrArg WithTop.untop₀ hc ▸ hp)

/-- Paper: Proposition B.6.1.1, p. 636. Every principal zero up to height Y is strictly inside a centered strip
whose half-width is smaller than one half by an inverse logarithm. Both edges are open. -/
theorem exists_completedZeta_logWidth_interior :
    ∃ A > 0, ∃ B : ℝ, 1 / 3 < B ∧ ∀ Y : ℝ, 0 ≤ Y → ∀ ρ : Z,
      |ρ.val.im| ≤ Y → |ρ.val.re - 1 / 2| < w(A, B, Y) := by
  obtain ⟨A, hA, hF⟩ := finiteHeckeL_zeroFreeRegion
  obtain ⟨B, hB, h⟩ := hF ℚ X
  obtain ⟨L, hL, hSeries⟩ := finiteHeckeL_exists_continuation X
  have hb : 0 < B := by linarith
  have hr (ρ : Z) : ρ.val.re < 1 - A / Real.log (B * (|ρ.val.im| + 3)) := by
    by_contra! hz
    have hdim : (Module.finrank ℚ ℚ : ℝ) ^ 4 = 1 := by simp
    have hne := h L hL hSeries ρ.val (by simpa only [hdim, one_mul] using hz)
    have hpos : 0 < ρ.val.re := by linarith [(abs_lt.mp (completedZetaZero_mem_centeredCriticalStrip ρ)).1]
    rw [meromorphicOrderAt_finiteHeckeL_continuation X hL.meromorphicOn hSeries hpos] at hne
    have hp : 0 < D₀ ρ.val := by rw [divisor_rat_principal_eq_zeta]; exact ρ.property
    rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec X).1.meromorphicOn (mem_univ _)] at hp
    cases hh : meromorphicOrderAt L₀ ρ.val with
    | top => simp [hh] at hne
    | coe n => rw [hh, WithTop.untop₀_coe] at hp; exact (not_le_of_gt hp) (by exact_mod_cast (hh ▸ hne))
  refine ⟨A, hA, B, hB, ?_⟩
  intro Y hY ρ hρ
  have pos : 0 < Real.log (B * (|ρ.val.im| + 3)) :=
    Real.log_pos (by nlinarith [mul_nonneg hb.le (abs_nonneg ρ.val.im)])
  have hlog : Real.log (B * (|ρ.val.im| + 3)) ≤ Real.log (B * (Y + 3)) :=
    Real.log_le_log (mul_pos hb (by positivity)) (mul_le_mul_of_nonneg_left (add_le_add_left hρ 3) hb.le)
  have hw := div_le_div_of_nonneg_left hA.le pos hlog
  have h₁ := hr ρ
  have h₂ := hr ⟨1 - ρ.val, reflected_site ρ⟩
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at h₂
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

private theorem siteWeights_summable : Summable (fun z : Z ↦ (r(z) : ℝ) / (1 + |z.val.im|) ^ 2) := by
  have h : Summable (fun z : {z : ℂ // 0 < D₀ z} ↦ (D₀ z.val : ℝ) / (1 + |z.val.im|) ^ 2) :=
    explicitFormulaCompletedHeckeL_summable_divisor_div_sq X
  rw [divisor_rat_principal_eq_zeta] at h
  apply h.congr
  intro z
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg z.property.le).symm

/-- The sum of the full zeta multiplicities against the integrable quadratic height weight. -/
def completedZetaQuadraticMass : ℝ := ∑' z : Z, (r(z) : ℝ) / (1 + |z.val.im|) ^ 2

/-- Positivity of the quadratic majorant for the omitted jets. -/
theorem completedZetaQuadraticMass_nonneg : 0 ≤ completedZetaQuadraticMass :=
  tsum_nonneg fun _ ↦ by positivity

/-- Paper: §12.3, p. 514. If all zeros through height Y are interior to the strip,
a quadratic Mellin bound above Y controls the full complex difference between the
sharp prime value and the Hilbert trace. The estimate includes the Sobolev edge. -/
theorem norm_centeredVonMangoldt_sub_radialStripTrace_le_of_height (H : ℝ → ℂ)
    (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ, H)) {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s)
    (T : nuclearEndomorphisms Q(ha, hs)) (hT : rep(T, φ, ha, hs)) {Y d : ℝ} (hd : 0 ≤ d)
    (hLow : ∀ z : Z, |z.val.im| ≤ Y → |z.val.re - 1 / 2| < a)
    (hHigh : ∀ z : Z, Y < |z.val.im| → ‖bilateralLaplace H (z.val - 1 / 2)‖ ≤ d / (1 + |z.val.im|) ^ 2) :
    ‖V * centeredVonMangoldtValue H - hilbertTrace T‖ ≤ ‖V‖ * d * completedZetaQuadraticMass := by
  let weight (z : Z) := (r(z) : ℝ) / (1 + |z.val.im|) ^ 2
  let f (z : Z) := ((r(z) - keep(a, s, z) : ℕ) : ℂ) * bilateralLaplace H (z.val - 1 / 2)
  have hpoint (z : Z) : ‖f z‖ ≤ d * weight z := by
    rcases le_or_gt |z.val.im| Y with hlo |hhi
    · have h := spectralStripMultiplicity_interior (abs_lt.mp (hLow z hlo)) s (r(z))
      simp only [f, h, Nat.sub_self, Nat.cast_zero, zero_mul, norm_zero]
      dsimp [weight]; positivity
    · have hn : r(z) - keep(a, s, z) ≤ r(z) := Nat.sub_le _ _
      simp only [f, norm_mul, Complex.norm_natCast]
      calc
        _ ≤ (r(z) : ℝ) * (d / (1 + |z.val.im|) ^ 2) :=
          mul_le_mul (by exact_mod_cast hn) (hHigh z hhi) (norm_nonneg _) (Nat.cast_nonneg _)
        _ = _ := by dsimp [weight]; ring
  have hsum : Summable (fun z ↦ d * weight z) := siteWeights_summable.mul_left d
  have habs := hsum.of_nonneg_of_le (fun z ↦ norm_nonneg (f z)) hpoint
  have h := (norm_tsum_le_tsum_norm habs).trans (habs.tsum_le_tsum hpoint hsum)
  rw [tsum_mul_left] at h
  rw [← (hasSum_centeredVonMangoldt_sub_radialStripTrace H hH hc hp φ hφ ha hs T hT).tsum_eq]
  change ‖∑' z, V * f z‖ ≤ _
  rw [tsum_mul_left, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

private theorem inverse_height_split (N : ℕ) {Y y : ℝ} (hY : 1 ≤ Y) (hy : Y ≤ y) :
    1 / y ^ (N + 2) ≤ (4 / Y ^ N) / (1 + y) ^ 2 := by
  have hY₀ : 0 < Y := by linarith
  have hy₀ := hY₀.trans_le hy
  have hden := mul_le_mul (pow_le_pow_left₀ hY₀.le hy N)
    (pow_le_pow_left₀ (by positivity : 0 ≤ 1 + y) (by linarith : 1 + y ≤ 2 * y) 2)
    (by positivity) (by positivity)
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, pow_add]
  nlinarith only [hden]

set_option maxHeartbeats 700000 in
/-- Paper: §12.3, p. 514. For one fixed radial test and every natural power N,
the signed trace error is bounded by K/Y^N. The same constant works for all
half-widths above the logarithmic boundary and every Sobolev order s > 1. -/
theorem exists_logWidth_radialStripTrace_bound :
    ∃ A > 0, ∃ B : ℝ, 1 / 3 < B ∧
      ∀ (H : ℝ → ℂ), ContDiff ℝ (∞) H → HasCompactSupport H → tsupport H ⊆ Ioi 0 →
      ∀ N : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (Y : ℝ), 1 ≤ Y →
      ∀ (φ : BruhatCompactSupport Cℚ), radial(φ, H) → ∀ {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s),
        w(A, B, Y) ≤ a → ∀ T : nuclearEndomorphisms Q(ha, hs), rep(T, φ, ha, hs) →
          ‖V * centeredVonMangoldtValue H - hilbertTrace T‖ ≤ K / Y ^ N := by
  obtain ⟨A, hA, B, hB, hlow⟩ := exists_completedZeta_logWidth_interior
  refine ⟨A, hA, B, hB, ?_⟩
  intro H hH hc hp N
  obtain ⟨C, hC, hrapid⟩ := bilateralLaplace_positiveLog_heightBound H hH hc hp (1 / 2) (N + 2) (by omega)
  refine ⟨‖V‖ * (4 * C) * completedZetaQuadraticMass,
    mul_nonneg (mul_nonneg (norm_nonneg _) (by positivity)) completedZetaQuadraticMass_nonneg, ?_⟩
  intro Y hY φ hφ a s ha hs hw T hT
  have hY₀ : 0 < Y := by linarith
  let d := (4 * C) / Y ^ N
  have high (z : Z) (hz : Y < |z.val.im|) :
      ‖bilateralLaplace H (z.val - 1 / 2)‖ ≤ d / (1 + |z.val.im|) ^ 2 := by
    have hrez := (abs_lt.mp (completedZetaZero_mem_centeredCriticalStrip z)).2
    have hi : z.val.im ≠ 0 := abs_pos.mp (hY₀.trans hz)
    have h := hrapid (z.val - 1 / 2) (by simpa using hrez.le) (by simpa using hi)
    simp only [Complex.sub_im, Complex.div_ofNat_im, Complex.one_im, zero_div, sub_zero] at h
    calc
      _ ≤ C / |z.val.im| ^ (N + 2) := h
      _ = C * (1 / |z.val.im| ^ (N + 2)) := by ring
      _ ≤ C * ((4 / Y ^ N) / (1 + |z.val.im|) ^ 2) :=
        mul_le_mul_of_nonneg_left (inverse_height_split N hY hz.le) hC.le
      _ = _ := by dsimp [d]; ring
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hh := norm_centeredVonMangoldt_sub_radialStripTrace_le_of_height H hH hc hp φ hφ ha hs T hT hd
    (fun z hz ↦ (hlow Y hY₀.le z hz).trans_le hw) high
  exact hh.trans_eq (by dsimp [d]; ring)

/-- Paper: §12.3, p. 514. A finite cutoff estimate for the signed local mass minus
the actual quotient trace. One finite level covers the support interval. For each
required height the large-cutoff threshold is uniform over all admitted strip
widths, Sobolev orders and nuclear representatives. -/
theorem exists_logWidth_sharpMass_stripTrace :
    ∃ A > 0, ∃ B : ℝ, 1 / 3 < B ∧
      ∀ l u : ℝ, ∃ S : Finset Pl, ∀ (H : ℝ → ℂ), ContDiff ℝ (∞) H → HasCompactSupport H →
        tsupport H ⊆ Ioi 0 → tsupport H ⊆ Icc l u →
        ∃ (φ : BruhatCompactSupport Cℚ) (f : BruhatCompactSupport (SAdeleRing ℚ S)ˣ),
          radial(φ, H) ∧
          (∀ g : (SAdeleRing ℚ S)ˣ, HasSum (fun ξ : sProjectedDiagonal ℚ S ↦ f.val (ξ.val * g))
            (φ.val (QuotientGroup.mk (sIdeleInsertion ℚ S g)))) ∧
          ∀ N : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 1 ≤ Y → ∀ᶠ R : ℝ in atTop,
            ∀ {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s), w(A, B, Y) ≤ a →
            ∀ T : nuclearEndomorphisms Q(ha, hs), rep(T, φ, ha, hs) →
              ‖-rationalCorrectedSharpMass f R - hilbertTrace T‖ ≤ K / Y ^ N := by
  apply exists_logWidth_radialStripTrace_bound.elim
  intro A hA
  obtain ⟨hA, B, hB, hbound⟩ := hA
  refine ⟨A, hA, B, hB, ?_⟩
  intro l u
  apply (exists_radialSharpMass_stripTrace_comparison l u).elim
  intro S hS
  refine ⟨S, ?_⟩
  intro H hH hc hp hj
  apply (hS H hH hc hp hj).elim
  intro φ hφ
  apply hφ.elim
  intro f hf
  obtain ⟨hφ, hLift, hlim, _⟩ := hf
  refine ⟨φ, f, hφ, hLift, ?_⟩
  intro N
  obtain ⟨K, hK, h⟩ := hbound H hH hc hp N
  refine ⟨1 + K, by linarith, ?_⟩
  intro Y hY
  have hY₀ : 0 < Y := by linarith
  have he := (Metric.tendsto_nhds.mp hlim) (1 / Y ^ N) (by positivity)
  filter_upwards [he] with R hR
  intro a s ha hs hw T hT
  have hh := h Y hY φ hφ ha hs hw T hT
  rw [← dist_eq_norm]
  exact (dist_triangle _ (V * centeredVonMangoldtValue H) _).trans
    ((add_le_add hR.le (by simpa only [dist_eq_norm] using hh)).trans_eq (add_div _ _ _).symm)

end RiemannMasullo
