module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_LogarithmicSharpTrace
public import RiemannMasullo.Ch12_TraceGeometric.Sec3_ShrinkingPrimePower
import RiemannMasullo.Ch12_TraceGeometric.Sec3_RationalDensityComparison

/-! # The signed local and quotient traces near an individual rational prime power

We work in the chart centered at one half. A single finite set of places suffices
as the physical support shrinks. The local limit detects the signed prime atom
with an unconditional linear error. A right-hand density estimate controls the
difference with the quotient Hilbert trace, uniformly in strip width and Sobolev
order above the stated thresholds.
-/

@[expose] public noncomputable section

open Classical Filter MeasureTheory Set NumberField
open scoped ArithmeticFunction ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.PrimeShrink

/-- The positive-axis input for shrinking profiles follows from Theorem B.4.2.2. -/
theorem positiveAxisExplicitFormula : PositiveAxisExplicitFormula := by
  intro H hH hc hs
  let G (x : ℝ) : ℂ := H x
  have hG : ContDiff ℝ (∞) G := Complex.ofRealCLM.contDiff.comp hH
  have hcG : HasCompactSupport G := hc.comp_left Complex.ofReal_zero
  have hsG : tsupport G ⊆ Ioi 0 := (tsupport_comp_subset Complex.ofReal_zero H).trans hs
  have h := hasSum_zetaZeros_positiveLog G hG hcG hsG
  change HasSum _ (bilateralLaplace G 1 + ((-primeSeries H - archIntegral H : ℝ) : ℂ))
  change HasSum (fun z : {z : ℂ // 0 < MeromorphicOn.divisor completedRiemannZeta univ z} ↦
    (MeromorphicOn.divisor completedRiemannZeta univ z.val : ℂ) * bilateralLaplace G z.val) _
  convert h using 1
  simp only [primeSeries, archIntegral, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_tsum,
    Complex.ofReal_mul, ← integral_complex_ofReal, Complex.ofReal_div, Complex.ofReal_one, G]
  ring

end RiemannMasullo.PrimeShrink

namespace RiemannMasullo.RationalWidthLoss

set_option quotPrecheck false
open PrimeShrink

local notation "L(" H ", " z ")" => bilateralLaplace (fun x : ℝ ↦ ((H : ℝ → ℝ) x : ℂ)) z
private def halfShift (H : ℝ → ℝ) (x : ℝ) := Real.exp (-x / 2) * H x

private theorem transform_halfShift (H : ℝ → ℝ) (z : ℂ) :
    L(halfShift H, z) = L(H, z - 1 / 2) := by
  unfold bilateralLaplace
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [halfShift, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_ofNat]
  calc
    _ = (H x : ℂ) * (Complex.exp (-(x : ℂ) / 2) * Complex.exp (z * x)) := by ring
    _ = _ := by rw [← Complex.exp_add]; congr 2; ring

private theorem full_centered_atom
    {g : ℝ → ℝ} (hg : ContDiff ℝ (∞) g) (hs : tsupport g ⊆ Icc (-1) 1)
    {c T : ℝ} (hc : 0 < c) (hT : 0 ≤ T) :
    ∃ δ > 0, ∃ K : ℝ, ∀ η, 0 < η → η ≤ δ → ∀ t ∈ Icc (-T) T,
      Summable (zeroTerm (halfShift (profile g η c t))) ∧
        ‖(∑' ρ : zetaZeros, zeroTerm (halfShift (profile g η c t)) ρ) +
          ((atomWeight c * (Real.exp (-c / 2) * iteratedDeriv 4 g (-t)) : ℝ) : ℂ)‖ ≤ K * η := by
  have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  obtain ⟨A, E, hA, hE, hb⟩ := profile_physical_bounds hg hgc
  apply fullZeroSum_local_atom (R := T + 1) (A := Real.exp ((T + 1) / 2) * A)
    (E := Real.exp (-c / 2) * E) positiveAxisExplicitFormula hc (by linarith)
    (fun η t ↦ halfShift (profile g η c t)) (fun t ↦ Real.exp (-c / 2) * iteratedDeriv 4 g (-t))
    (Icc (-T) T)
  · intro η hη _ t _
    obtain ⟨hd, hk⟩ := profile_smooth_compact hg hs hη c t
    exact ⟨(by fun_prop : ContDiff ℝ (∞) (fun x : ℝ ↦ Real.exp (-x / 2))).mul hd, hk.mul_left⟩
  · intro η hη _ t _
    rw [transform_halfShift, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num]
    exact profile_four_moments hg hgc hη c t _ (Or.inr (Or.inr (Or.inl rfl)))
  · intro η hη _ t ht x hx
    exact profile_dist_le_of_ne_zero hs hη (abs_le.mpr ht) (fun h ↦ hx (by simp [halfShift, h]))
  · intro η hη h1 t ht x
    by_cases hz : profile g η c t x = 0
    · simp only [halfShift, hz, mul_zero, abs_zero]; positivity
    have hd := (abs_le.mp (profile_dist_le_of_ne_zero hs hη (abs_le.mpr ht) hz)).1
    have hdist : (T + 1) * η ≤ T + 1 := mul_le_of_le_one_right (by linarith) h1
    simp only [halfShift, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) ((hb η hη h1 c t).1 x) (abs_nonneg _) (Real.exp_pos _).le
  · intro η hη h1 t _
    simp only [halfShift, ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _), mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb η hη h1 c t).2 (Real.exp_pos _).le

private theorem lost_le_exterior (a s : ℝ) (ρ : zeroSites) :
    multiplicity ρ - spectralStripMultiplicity a s (ρ.val.re - 1 / 2) (multiplicity ρ) ≤
      exteriorWeight a ρ := by
  unfold exteriorWeight
  split_ifs with he
  · exact Nat.sub_le _ _
  · have hi := abs_lt.mp (lt_of_not_ge he)
    rw [spectralStripMultiplicity_interior hi, Nat.sub_self]

private def principalZeroEquiv : zeroSites ≃ zetaZeros :=
  Equiv.subtypeEquivRight fun z ↦ by
    change (0 < MeromorphicOn.divisor (continuedCompletedHeckeL (F := ℚ) 1) univ z) ↔ _
    rw [principal_divisor_eq_completedRiemannZeta]
    rfl

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instFiniteCompletionUnitsLocallyCompactSec4b instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSIdeleLocallyCompactSec1 instSIdeleT2Sec4

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Pl" => IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)
local notation "V" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "band(" ha ")" => (neg_nonpos.mpr ha |>.trans ha)
local notation "Q(" ha ", " hs ")" => spectralSobolevQuotient ℚ (1 / 2) (band(ha)) (zero_lt_one.trans hs).le
local notation "HC(" H ")" => fun x : ℝ ↦ ((H : ℝ → ℝ) x : ℂ)
local notation "loss(" a ", " s ", " z ")" =>
  ((MeromorphicOn.divisor completedRiemannZeta univ (z : zetaZeros).val).toNat -
    spectralStripMultiplicity a s ((z : zetaZeros).val.re - 1 / 2)
      (MeromorphicOn.divisor completedRiemannZeta univ (z : zetaZeros).val).toNat : ℕ)
local notation "target(" c ", " g ", " t ")" =>
  ((atomWeight c * (Real.exp (-c / 2) * iteratedDeriv 4 (g : ℝ → ℝ) (-t)) : ℝ) : ℂ)

private theorem local_value_eq (H : ℝ → ℝ) (hH : ContDiff ℝ (∞) H)
    (hc : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0) :
    (∑' z : zetaZeros, zeroTerm (halfShift H) z) = centeredVonMangoldtValue (HC(H)) := by
  have h := hasSum_zetaZeros_centeredVonMangoldt (HC(H)) (Complex.ofRealCLM.contDiff.comp hH)
    (hc.comp_left Complex.ofReal_zero) ((tsupport_comp_subset Complex.ofReal_zero H).trans hp)
  apply HasSum.tsum_eq
  apply h.congr_fun
  intro z
  unfold zeroTerm
  rw [transform_halfShift]
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg z.property.le).symm

private theorem omitted_mass_le {σ q C ν : ℝ} (hq : 0 ≤ q) (hν : 0 < ν)
    (hqν : ν < 1 - q) (hC : 0 ≤ C) (hd : HasRightDensity σ q C)
    {g : ℝ → ℝ} (hg : ContDiff ℝ (∞) g) (hgc : HasCompactSupport g) (c T : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ η, 0 < η → η ≤ 1 → ∀ t : ℝ, |t| ≤ T →
      ∀ a s : ℝ, σ - 1 / 2 ≤ a →
        ‖∑' z : zetaZeros, V * ((loss(a, s, z) : ℂ) * L(profile g η c t, z.val - 1 / 2))‖ ≤
          D * η ^ ν := by
  let d := σ - 1 / 2
  obtain ⟨D, hD, htail⟩ := profile_exterior_mass_le (δ := d) le_rfl hq hν hqν hC hd hg hgc c T (1 / 2)
  refine ⟨‖V‖ * D, mul_nonneg (norm_nonneg _) hD, ?_⟩
  intro η hη h1 t ht a s ha
  let H := profile g η c t
  let f (z : zetaZeros) := (loss(a, s, z) : ℂ) * L(H, z.val - 1 / 2)
  obtain ⟨habs, herr⟩ := htail η hη h1 t ht
  have hm (ρ : zeroSites) : ‖f (principalZeroEquiv ρ)‖ ≤
      (exteriorWeight d ρ : ℝ) * ‖L(H, ρ.val - ((1 / 2 : ℝ) : ℂ))‖ := by
    have hw : multiplicity ρ - spectralStripMultiplicity a s (ρ.val.re - 1 / 2) (multiplicity ρ) ≤
        exteriorWeight d ρ := (lost_le_exterior a s ρ).trans (by
      unfold exteriorWeight
      split_ifs <;> first | exact le_rfl | exact Nat.zero_le _ | grind)
    change ‖((loss(a, s, principalZeroEquiv ρ) : ℕ) : ℂ) * L(H, ρ.val - 1 / 2)‖ ≤ _
    simp only [norm_mul, Complex.norm_natCast, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    change (((MeromorphicOn.divisor completedRiemannZeta univ ρ.val).toNat -
      spectralStripMultiplicity a s (ρ.val.re - 1 / 2)
        (MeromorphicOn.divisor completedRiemannZeta univ ρ.val).toNat : ℕ) : ℝ) ≤ _
    rw [← principal_divisor_eq_completedRiemannZeta]
    exact_mod_cast hw
  have hs := habs.of_nonneg_of_le (fun ρ ↦ norm_nonneg (f (principalZeroEquiv ρ))) hm
  have hv := (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum hm habs).trans herr)
  rw [principalZeroEquiv.tsum_eq f] at hv
  change ‖∑' z, V * f z‖ ≤ _
  rw [tsum_mul_left, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left hv (norm_nonneg _)

private theorem profile_window {g : ℝ → ℝ} (hs : tsupport g ⊆ Icc (-1) 1)
    {η c T t : ℝ} (hη : 0 < η) (h1 : η ≤ 1) (hηc : (T + 1) * η ≤ c / 2)
    (ht : |t| ≤ T) : tsupport (profile g η c t) ⊆ Icc (c / 2) (c + (T + 1)) := by
  have hT : 0 ≤ T := (abs_nonneg t).trans ht
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have h := abs_le.mp (profile_dist_le_of_ne_zero hs hη ht hx)
  have hu := mul_le_of_le_one_right (by linarith : 0 ≤ T + 1) h1
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

local notation "radial(" φ ", " H ")" => ∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x =
  (H : ℝ → ℂ) (Real.log ((ideleClassNorm ℚ x : ℝ≥0) : ℝ))
local notation "lifts(" S ", " f ", " φ ")" => ∀ g : (SAdeleRing ℚ S)ˣ,
  HasSum (fun ξ : sProjectedDiagonal ℚ S ↦ (f : BruhatCompactSupport (SAdeleRing ℚ S)ˣ).val (ξ.val * g))
    ((φ : BruhatCompactSupport Cℚ).val (QuotientGroup.mk (sIdeleInsertion ℚ S g)))
local notation "rep(" T ", " φ ", " ha ", " hs ")" =>
  (T : nuclearEndomorphisms Q(ha, hs)).val =
    spectralConvolution (F := ℚ) (1 / 2) (band(ha)) (zero_lt_one.trans hs).le φ

/-- Uniform comparison, over translated profiles at physical scale η, between the
negative corrected local mass and the nuclear quotient trace. The common finite
set of places and the constants precede the scale and translation. The predicate
selects the admitted strip widths. The positive-log prime atom carries the half twist. -/
def HasShrinkingSharpTraceEstimate (g : ℝ → ℝ) (c U : ℝ)
    (admissible : ℝ → ℝ → Prop) (rate : ℝ → ℝ) : Prop :=
    ∃ (S : Finset Pl) (δ : ℝ), 0 < δ ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ η, 0 < η → η ≤ δ → ∀ t ∈ Icc (-U) U,
      let H := HC(profile g η c t)
      ∃ (φ : BruhatCompactSupport Cℚ) (f : BruhatCompactSupport (SAdeleRing ℚ S)ˣ),
        radial(φ, H) ∧ lifts(S, f, φ) ∧
        Tendsto (fun R : ℝ ↦ -rationalCorrectedSharpMass f R) atTop (𝓝 (V * centeredVonMangoldtValue H)) ∧
        ‖V * centeredVonMangoldtValue H + V * target(c, g, t)‖ ≤ B * η ∧
        ∀ {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s), admissible η a →
          ∀ T : nuclearEndomorphisms Q(ha, hs), rep(T, φ, ha, hs) →
            ‖V * centeredVonMangoldtValue H - hilbertTrace T‖ ≤ B * rate η

set_option maxHeartbeats 700000 in
private theorem shrinking_comparison_of_trace_bound
    {g : ℝ → ℝ} (hg : ContDiff ℝ (∞) g) (hgS : tsupport g ⊆ Icc (-1) 1)
    {c U : ℝ} (hc : 0 < c) (hU : 0 ≤ U) {admissible : ℝ → ℝ → Prop} {rate : ℝ → ℝ}
    (hrate : ∀ η, 0 < η → 0 ≤ rate η)
    (hbound : ∃ D : ℝ, 0 ≤ D ∧ ∀ η, 0 < η → η ≤ 1 → ∀ t : ℝ, |t| ≤ U →
      let H := HC(profile g η c t)
      tsupport H ⊆ Ioi 0 → ∀ (φ : BruhatCompactSupport Cℚ), radial(φ, H) →
        ∀ {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s), admissible η a →
        ∀ T : nuclearEndomorphisms Q(ha, hs), rep(T, φ, ha, hs) →
          ‖V * centeredVonMangoldtValue H - hilbertTrace T‖ ≤ D * rate η) :
    HasShrinkingSharpTraceEstimate g c U admissible rate := by
  obtain ⟨D, hD, hd'⟩ := hbound
  obtain ⟨d, hδ, K, hatom⟩ := full_centered_atom hg hgS hc hU
  apply (exists_radialSharpMass_stripTrace_comparison (c / 2) (c + (U + 1))).elim
  intro S hS
  let R := U + 1
  have hR : 0 < R := by dsimp [R]; linarith
  let δ := min d (min 1 (c / 2 / R))
  let B := max D (‖V‖ * max K 0)
  refine ⟨S, δ, lt_min hδ (lt_min zero_lt_one (div_pos (half_pos hc) hR)), B, hD.trans (le_max_left _ _), ?_⟩
  intro η hη hsmall t ht
  let G := profile g η c t
  have h1 := (hsmall.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hr := (le_div_iff₀ hR).mp ((hsmall.trans (min_le_right _ _)).trans (min_le_right _ _))
  have hJ := profile_window hgS hη h1 (mul_comm η R ▸ hr) (abs_le.mpr ht)
  have hp : tsupport G ⊆ Ioi 0 := fun x hx ↦ (half_pos hc).trans_le (hJ hx).1
  obtain ⟨hG, hk⟩ := profile_smooth_compact hg hgS hη c t
  have hdG := Complex.ofRealCLM.contDiff.comp hG
  have hcG := hk.comp_left Complex.ofReal_zero
  have hsG := tsupport_comp_subset Complex.ofReal_zero G
  apply (hS (HC(G)) hdG hcG (hsG.trans hp) (hsG.trans hJ)).elim
  intro φ hrest
  apply hrest.elim
  intro f hrest
  obtain ⟨hφ, hf, hlim, _⟩ := hrest
  refine ⟨φ, f, hφ, hf, hlim, ?_, ?_⟩
  · obtain ⟨_, h⟩ := hatom η hη (hsmall.trans (min_le_left _ _)) t ht
    rw [local_value_eq G hG hk hp] at h
    rw [← mul_add, norm_mul]
    calc
      _ ≤ ‖V‖ * (K * η) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ ≤ B * η := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)).trans (le_max_right _ _)) hη.le
  · intro a s ha hs hband T hT
    have he := hd' η hη h1 t (abs_le.mpr ht) (hsG.trans hp) φ hφ ha hs hband T hT
    exact he.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hrate η hη))

set_option maxHeartbeats 700000 in
/-- Paper: §12.3, p. 514. At fixed thin widths the right-side density estimate
controls the difference with the local prime value at rate η^ν, uniformly across
all widths above the threshold and all Sobolev orders. -/
theorem exists_shrinkingSharpMass_stripTrace {σ q C ν : ℝ} (hq : 0 ≤ q) (hν : 0 < ν)
    (hqν : ν < 1 - q) (hC : 0 ≤ C) (hd : HasRightDensity σ q C)
    {g : ℝ → ℝ} (hg : ContDiff ℝ (∞) g) (hgS : tsupport g ⊆ Icc (-1) 1)
    {c U : ℝ} (hc : 0 < c) (hU : 0 ≤ U) :
    HasShrinkingSharpTraceEstimate g c U (fun _ a ↦ σ - 1 / 2 ≤ a) (fun η ↦ η ^ ν) := by
  apply shrinking_comparison_of_trace_bound hg hgS hc hU (fun η hη ↦ Real.rpow_nonneg hη.le _)
  have hgc := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hgS
  obtain ⟨D, hD, hd'⟩ := omitted_mass_le hq hν hqν hC hd hg hgc c U
  refine ⟨D, hD, ?_⟩
  intro η hη h1 t ht H hp φ hφ a s ha hs hw T hT
  obtain ⟨hG, hk⟩ := profile_smooth_compact hg hgS hη c t
  have he := (hasSum_centeredVonMangoldt_sub_radialStripTrace _ (Complex.ofRealCLM.contDiff.comp hG)
    (hk.comp_left Complex.ofReal_zero) hp φ hφ ha hs T hT).tsum_eq
  change _ = V * centeredVonMangoldtValue H - hilbertTrace T at he
  rw [← he]
  exact hd' η hη h1 t ht a s hw

/-- Paper: §12.3, p. 514. A prescribed smooth shrinking profile measures its
signed prime-power atom unconditionally at every fixed positive lower strip width.
At half-width `δ`, every exponent below `δ²/16` is available for the discrepancy. -/
theorem fixedWidth_shrinkingSharpMass_stripTrace {δ ν : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1/2)
    (hν : 0 < ν) (hν' : ν < δ^2/16)
    {g : ℝ → ℝ} (hg : ContDiff ℝ (∞) g) (hgS : tsupport g ⊆ Icc (-1) 1)
    {c U : ℝ} (hc : 0 < c) (hU : 0 ≤ U) :
    HasShrinkingSharpTraceEstimate g c U (fun _ a ↦ δ ≤ a) (fun η ↦ η^ν) := by
  obtain ⟨C,hC,h⟩ := exists_rightDensity_power hδ hδ'
  have hq : 0 ≤ 1-δ^2/16 := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ')]
  have hs := exists_shrinkingSharpMass_stripTrace hq hν (by linarith) hC h hg hgS hc hU
  simpa only [add_sub_cancel_left] using hs

/-- Under the stated Ingham zero-density input, the local comparison at half-width
one quarter has every remainder exponent below two fifths. -/
theorem quarterWidth_shrinkingSharpMass_stripTrace (hI : InghamDensity)
    {g : ℝ → ℝ} (hg : ContDiff ℝ (∞) g) (hgS : tsupport g ⊆ Icc (-1) 1)
    {c U ν : ℝ} (hc : 0 < c) (hU : 0 ≤ U) (hν : 0 < ν) (hν' : ν < 2 / 5) :
    HasShrinkingSharpTraceEstimate g c U (fun _ a ↦ 1 / 4 ≤ a) (fun η ↦ η ^ ν) := by
  obtain ⟨C₀, hC₀, h₀⟩ := hI (3 / 4) (by norm_num) le_rfl
  norm_num at h₀
  obtain ⟨C, hC, hd⟩ := hasRightDensity_of_positiveHeight (by norm_num : 0 ≤ (3 / 5 : ℝ)) hC₀ h₀
  convert exists_shrinkingSharpMass_stripTrace (by norm_num) hν (by linarith) hC hd hg hgS hc hU using 1
  norm_num

private theorem scaled_height_tail (k : ℕ) {η y : ℝ} (hη : 0 < η) (h1 : η ≤ 1)
    (hy : 0 ≤ y) (hlarge : η⁻¹ ^ 2 ≤ y) :
    η / (1 + η * y) ^ (2 + (k + 1)) ≤ η ^ k / (1 + y) ^ 2 := by
  have hden : 0 < 1 + η * y := by positivity
  have hlow : η * (1 + y) ≤ 1 + η * y := by linarith
  have hhigh : η⁻¹ ≤ 1 + η * y := by
    have h := mul_le_mul_of_nonneg_left hlarge hη.le
    have he : η * η⁻¹ ^ 2 = η⁻¹ := by field_simp
    linarith [he]
  have hd := mul_le_mul (pow_le_pow_left₀ (by positivity : 0 ≤ η * (1 + y)) hlow 2)
    (pow_le_pow_left₀ (inv_nonneg.mpr hη.le) hhigh (k + 1)) (by positivity) (by positivity)
  rw [← pow_add] at hd
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    η * (1 + y) ^ 2 = η ^ k * ((η * (1 + y)) ^ 2 * (η⁻¹) ^ (k + 1)) := by
      rw [inv_pow, pow_succ]; field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)

set_option maxHeartbeats 700000 in
/-- Paper: §12.3, p. 514. The classical zero-free region gives a genuinely
thin logarithmic schedule with an unconditional error of every natural power in
the shrinking physical width. One finite level covers the whole family. -/
theorem logWidth_shrinkingSharpMass_stripTrace :
    ∃ A > 0, ∃ B : ℝ, 1 / 3 < B ∧
      ∀ {g : ℝ → ℝ}, ContDiff ℝ (∞) g → tsupport g ⊆ Icc (-1) 1 →
      ∀ {c U : ℝ}, 0 < c → 0 ≤ U → ∀ k : ℕ,
        HasShrinkingSharpTraceEstimate g c U
          (fun η a ↦ 1 / 2 - A / Real.log (B * (η⁻¹ ^ 2 + 3)) ≤ a) (fun η ↦ η ^ k) := by
  obtain ⟨A, hA, B, hB, hlow⟩ := exists_completedZeta_logWidth_interior
  refine ⟨A, hA, B, hB, ?_⟩
  intro g hg hgS c U hc hU k
  apply shrinking_comparison_of_trace_bound hg hgS hc hU (fun η hη ↦ pow_nonneg hη.le _)
  have hgc := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hgS
  obtain ⟨K, hK, hrapid⟩ := profile_laplace_decay hg hgc c U (1 / 2) (2 + (k + 1))
  refine ⟨‖V‖ * K * completedZetaQuadraticMass,
    mul_nonneg (mul_nonneg (norm_nonneg _) hK) completedZetaQuadraticMass_nonneg, ?_⟩
  intro η hη h1 t ht H hp φ hφ a s ha hs hw T hT
  obtain ⟨hG, hk⟩ := profile_smooth_compact hg hgS hη c t
  let Y := η⁻¹ ^ 2
  have high (z : zetaZeros) (hz : Y < |z.val.im|) :
      ‖L(profile g η c t, z.val - 1 / 2)‖ ≤ (K * η ^ k) / (1 + |z.val.im|) ^ 2 := by
    have hre : |(z.val - 1 / 2).re| ≤ (1 / 2 : ℝ) := by
      simpa using (completedZetaZero_mem_centeredCriticalStrip z).le
    have h := hrapid η hη h1 t ht _ hre
    simp only [Complex.sub_im, Complex.div_ofNat_im, Complex.one_im, zero_div, sub_zero] at h
    calc
      _ ≤ K * η / (1 + η * |z.val.im|) ^ (2 + (k + 1)) := h
      _ = K * (η / (1 + η * |z.val.im|) ^ (2 + (k + 1))) := mul_div_assoc _ _ _
      _ ≤ K * (η ^ k / (1 + |z.val.im|) ^ 2) :=
        mul_le_mul_of_nonneg_left (scaled_height_tail k hη h1 (abs_nonneg _) hz.le) hK
      _ = _ := (mul_div_assoc _ _ _).symm
  have hh := norm_centeredVonMangoldt_sub_radialStripTrace_le_of_height _ (Complex.ofRealCLM.contDiff.comp hG)
    (hk.comp_left Complex.ofReal_zero) hp φ hφ ha hs T hT (mul_nonneg hK (pow_nonneg hη.le k))
    (fun z hz ↦ (hlow Y (sq_nonneg _) z hz).trans_le hw) high
  exact hh.trans_eq (by ring)

private theorem norm_add_via (x y z : ℂ) : ‖x + z‖ ≤ ‖x - y‖ + ‖y + z‖ := by
  calc
    ‖x + z‖ = ‖(x - y) + (y + z)‖ := by congr 1; abel
    _ ≤ _ := norm_add_le _ _

set_option maxHeartbeats 700000 in
/-- For every prime power, the actual finite-cutoff local trace recovers the
coefficient minus log(p)/sqrt(p^j) times the fourth derivative at the translated
point. Its distance from the quotient trace is controlled at the spectral rate.
The threshold for the physical cutoff precedes all widths and Sobolev orders. -/
theorem HasShrinkingSharpTraceEstimate.at_prime_power {g : ℝ → ℝ} {U : ℝ}
    {admissible : ℝ → ℝ → Prop} {rate : ℝ → ℝ} (hrate : ∀ η, 0 < η → 0 < rate η)
    {p j : ℕ} (hp : p.Prime) (hj : j ≠ 0)
    (h : HasShrinkingSharpTraceEstimate g (Real.log ((p ^ j : ℕ) : ℝ)) U admissible rate) :
    let c := Real.log ((p ^ j : ℕ) : ℝ)
    ∃ (S : Finset Pl) (δ : ℝ), 0 < δ ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ η, 0 < η → η ≤ δ → ∀ t ∈ Icc (-U) U,
      let H := HC(profile g η c t)
      let atom := V * ((Real.log p / Real.sqrt ((p ^ j : ℕ) : ℝ) * iteratedDeriv 4 g (-t) : ℝ) : ℂ)
      ∃ (φ : BruhatCompactSupport Cℚ) (f : BruhatCompactSupport (SAdeleRing ℚ S)ˣ),
        radial(φ, H) ∧ lifts(S, f, φ) ∧ ∀ᶠ R : ℝ in atTop,
          ‖-rationalCorrectedSharpMass f R + atom‖ ≤ K * η ∧
          ∀ {a s : ℝ} (ha : 0 ≤ a) (hs : 1 < s), admissible η a →
            ∀ T : nuclearEndomorphisms Q(ha, hs), rep(T, φ, ha, hs) →
              ‖-rationalCorrectedSharpMass f R - hilbertTrace T‖ ≤ K * rate η ∧
              ‖hilbertTrace T + atom‖ ≤ K * (η + rate η) := by
  intro c
  obtain ⟨S, δ, hδ, B, hB, h⟩ := h
  refine ⟨S, δ, hδ, B + 1, by positivity, ?_⟩
  intro η hη hsmall t ht H atom
  apply (h η hη hsmall t ht).elim
  intro φ hφ
  apply hφ.elim
  intro f hf
  obtain ⟨hφ, hLift, hlim, hprime, hdiff⟩ := hf
  have hN : 0 < ((p ^ j : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos j
  have hc : Real.exp (-c / 2) = (Real.sqrt ((p ^ j : ℕ) : ℝ))⁻¹ := by
    rw [neg_div, Real.exp_neg, Real.exp_half, Real.exp_log hN]
  have heq : V * target(c, g, t) = atom := by
    rw [show atomWeight c = Real.log p from atomWeight_log_prime_pow hp hj, hc]
    dsimp [atom]
    push_cast
    ring
  change ‖V * centeredVonMangoldtValue H + V * target(c, g, t)‖ ≤ _ at hprime
  rw [heq] at hprime
  refine ⟨φ, f, hφ, hLift, ?_⟩
  have hr := hrate η hη
  have hclos := (Metric.tendsto_nhds.mp hlim) (min η (rate η)) (lt_min hη hr)
  filter_upwards [hclos] with R hR
  let P := V * centeredVonMangoldtValue H
  have hL : ‖-rationalCorrectedSharpMass f R - P‖ ≤ min η (rate η) := by
    rw [← dist_eq_norm]; exact hR.le
  have hP : ‖P + atom‖ ≤ B * η := hprime
  constructor
  · calc
      _ ≤ ‖-rationalCorrectedSharpMass f R - P‖ + ‖P + atom‖ := norm_add_via _ _ _
      _ ≤ η + B * η := add_le_add (hL.trans (min_le_left _ _)) hP
      _ = _ := by ring
  · intro a s ha hs hw T hT
    have ht' : ‖P - hilbertTrace T‖ ≤ B * rate η := hdiff ha hs hw T hT
    constructor
    · calc
        _ ≤ ‖-rationalCorrectedSharpMass f R - P‖ + ‖P - hilbertTrace T‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ rate η + B * rate η := add_le_add (hL.trans (min_le_right _ _)) ht'
        _ = _ := by ring
    · calc
        _ ≤ ‖hilbertTrace T - P‖ + ‖P + atom‖ := norm_add_via _ _ _
        _ ≤ B * rate η + B * η := add_le_add (by rw [norm_sub_rev (hilbertTrace T) P]; exact ht') hP
        _ ≤ _ := by nlinarith [hη.le, hr.le]

end RiemannMasullo.RationalWidthLoss
