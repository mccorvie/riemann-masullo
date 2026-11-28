module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedOrbitKernel
import RiemannMasullo.Ch09_HardySobolev.Sec3
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Diagonal continuity and ambient nuclearity at a fixed annulus -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField
open scoped ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Jₛ" => SIdeleQuotient F S
local notation "Q" => continuousSIdeleQuotientNorm F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "ℓ" => logSIdeleQuotientNorm F S

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1
  instSIdeleQuotientLocallyCompactSec1 instSIdeleQuotientSecondCountableSec1
  instSIdeleQuotientHaarMeasureSec1

/-- Paper: Proposition 12.2.2.2(2), p. 508, and Theorem 12.4.1.1, pp. 515–517.
The weighted half-density factors preserve diagonal continuity at each
point where the spatial mask is continuous. -/
theorem ae_continuousAt_sLocalTrace_maskedHalfDensity
    (κ₀ : Jₛ → Jₛ → ℂ) (hκ₀ : Continuous (Function.uncurry κ₀))
    {ρ : Jₛ → ℝ} (hρ : ∀ᵐ x ∂μJ, ContinuousAt ρ x) (s : ℝ) :
    let N (q : Jₛ) : ℝ := (Q q).val
    let ν := intervalSobolevMeasure μJ ℓ 0 0 s
    let K (p : Jₛ × Jₛ) : ℂ :=
      (Real.sqrt (N p.1 * N p.2) : ℂ) * ((ρ p.1 : ℂ) * κ₀ p.1 p.2) /
        ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 s (ℓ p.2) : ℂ))
    ∀ᵐ x ∂ν, ContinuousAt K (x, x) := by
  intro N ν K
  have hνμ : ν ≪ μJ := withDensity_absolutelyContinuous _ _
  have hρν : ∀ᵐ x ∂ν, ContinuousAt ρ x := hνμ.ae_le hρ
  have hN : Continuous N := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (Q).continuous)
  have hℓ : Continuous (ℓ) := hN.log fun x ↦ (NNReal.coe_pos.mpr (Units.zero_lt (Q x))).ne'
  let w (x : Jₛ) := intervalSobolevDensity 0 0 s (ℓ x)
  have hWeight : Continuous (intervalSobolevDensity 0 0 s) := by
    unfold intervalSobolevDensity
    refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun _ ↦ Or.inl ?_)
    positivity
  have hw : Continuous w := hWeight.comp hℓ
  have hw₀ (x : Jₛ) : 0 < w x := by
    unfold w intervalSobolevDensity
    exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  have hc : (sLocalTraceMeasureFactor S : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    unfold sLocalTraceMeasureFactor
    refine ne_of_gt (Finset.prod_pos fun v _ ↦ ?_)
    have hv : 1 < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    exact div_pos (zero_lt_one.trans hv) (sub_pos.mpr hv)
  let d (p : Jₛ × Jₛ) : ℂ := (sLocalTraceMeasureFactor S : ℂ) * (w p.2 : ℂ)
  have hd : Continuous d := continuous_const.mul
    (Complex.continuous_ofReal.comp (hw.comp continuous_snd))
  have hroot : Continuous (fun p : Jₛ × Jₛ ↦ (Real.sqrt (N p.1 * N p.2) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      ((hN.comp continuous_fst).mul (hN.comp continuous_snd)))
  filter_upwards [hρν] with x hx
  have hmask : ContinuousAt (fun p : Jₛ × Jₛ ↦ (ρ p.1 : ℂ)) (x, x) :=
    Complex.continuous_ofReal.continuousAt.comp (hx.comp continuous_fst.continuousAt)
  have hkernel : ContinuousAt (fun p : Jₛ × Jₛ ↦ κ₀ p.1 p.2) (x, x) := hκ₀.continuousAt
  change ContinuousAt (fun p : Jₛ × Jₛ ↦
    (Real.sqrt (N p.1 * N p.2) : ℂ) * ((ρ p.1 : ℂ) * κ₀ p.1 p.2) / d p) (x, x)
  exact (hroot.continuousAt.mul (hmask.mul hkernel)).div hd.continuousAt
    (mul_ne_zero hc (Complex.ofReal_ne_zero.mpr (hw₀ x).ne'))

/-- Paper: Theorem 12.4.1.1, p. 515. The strict annular spatial cutoff of
the quotient test action is nuclear after any bounded input operator.
Deviation: The construction gives ambient nuclearity for an annulus with
a strict inner band. -/
theorem isNuclearOperator_sLocalTrace_fixedAnnulus_testAction_comp
    {s Λ ε : ℝ} (hs : 0 ≤ s) (Φ : BruhatCompactSupport Jₛ)
    {ρ : Jₛ → ℝ} (hρ : IsModulatedCutoff Q Λ ε ρ)
    (hBand : 0 < Λ⁻¹ + ε ∧ Λ⁻¹ + ε < Λ - ε) :
    let ν := intervalSobolevMeasure μJ ℓ 0 0 s
    let W := CompactIntervalSobolev μJ ℓ 0 0 s
    let C : W →L[ℂ] W := (lpCutoffMultiplier ν ρ hρ.measurable hρ.abs_le_one).comp
      (hardySobolevTestAction μJ Q 0 0 s le_rfl hs Φ)
    ∀ Bdd : W →L[ℂ] W, IsNuclearOperator (C.comp Bdd) := by
  intro ν W C Bdd
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  have hSection : RightInverse σ Q := hσ
  obtain ⟨t₀, ht₀⟩ := exists_ne (1 : ℝ≥0ˣ)
  have hm : IsModulation Q :=
    ⟨isProperMap_sIdeleQuotientNorm F S, σ t₀, (hSection t₀).trans_ne ht₀⟩
  have hΦs : IsBruhatSmooth Φ.val := (mem_bruhatSmoothSubmodule_iff _).mp Φ.property.1
  have hΦc := continuous_of_bruhatSmooth hΦs
  have hΦb := hΦc.bounded_above_of_compact_support (show HasCompactSupport Φ.val from Φ.property.2)
  obtain ⟨hNuc, _, _⟩ :=
    truncatedHardySobolevConvolution_trace μJ Q 0 0 s le_rfl hs Φ.val
      hΦc.aemeasurable Φ.property.2 hΦb hm hSection.surjective hΦs hρ hBand
  rw [hardySobolevConvolution_eq_testAction μJ Q 0 0 s le_rfl hs Φ
    hΦc.aemeasurable hΦb] at hNuc
  have hC : IsNuclearOperator C := hNuc
  exact mul_mem_nuclearEndomorphisms_right Bdd (⟨C, hC⟩ : nuclearEndomorphisms W)

end RiemannMasullo
