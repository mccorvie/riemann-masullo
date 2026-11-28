module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ActualFixedBandTraceClass
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedCompactProfiles
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedMomentClosure

/-! # The exact order-zero reflected band -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "η" => sLocalNormOneQuotientMeasure F S
local notation "Zₛ" => sAdelePolarSubspace F S
local notation "W₀" => CompactIntervalSobolev μJ (logSIdeleQuotientNorm F S) 0 0 0
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)
local notation "include₁" =>
  (ContinuousMonoidHom.mk (Subgroup.subtype (MonoidHom.ker (sIdeleQuotientNorm F S)))
    continuous_subtype_val : J₁ →ₜ* Jₛ)

/-- Paper: (11.2.1.6), p. 488, and Theorem 12.4.1.1, pp. 515–518.
At order zero the closed half-density band is isometric to the supported
reflected half-line. In the trivial norm-one type its range is the kernel
of the exponential moment on that half-line. -/
theorem exists_sLocalInvariantPW_reflectedLogInput_range_orderZero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) {B : ℝ} (hB : 0 < B) :
    let V : Submodule ℂ W₀ := sLocalInvariantPWSobolev (F := F) (S := S) (s := 0) le_rfl halfPos ω B
    ∃ (χ : PontryaginDual Jₛ) (T : W₀ →L[ℂ] FlatL2),
      χ.comp include₁ = ω ∧ (∀ t, χ (QuotientGroup.mk (τ t)) = 1) ∧ ‖T‖ ≤ 1 ∧
      (∀ f : Zₛ,
        (T (sLocalPWThetaSobolevMap (F := F) (S := S) (s := 0) halfPos ω f) : ℝ → ℂ)
          =ᵐ[volume] fun y ↦ (Real.sqrt (Measure.real η univ) : ℂ) *
            sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f.val) (-y)) ∧
      (∀ u ∈ V, ‖T u‖ = ‖u‖) ∧
      Set.range (fun u : V ↦ T u.val) =
        {r : FlatL2 | (∀ᵐ y : ℝ ∂volume, y < -Real.log B → r y = 0) ∧
          (ω = 1 → (∫ y, (Real.exp (-y / 2) : ℂ) * r y) = 0)} := by
  intro V
  obtain ⟨χ, T, hχ, hsec, hT, hgen, hsupp, hnorm, hmoment⟩ :=
    exists_sLocalInvariantPW_reflectedLogInput_orderZero τ hτ ω hB
  have hV : IsClosed (V : Set W₀) := Submodule.isClosed_topologicalClosure _
  refine ⟨χ, T, hχ, hsec, hT, hgen, hnorm, ?_⟩
  refine range_reflectedInput_eq_of_smoothCore V hV T (-Real.log B) (ω = 1)
    hnorm hsupp (fun u hu hω ↦ (hmoment hω u hu).2) ?_
  intro r hrc hrd hrs hrm
  obtain ⟨f, hfpolar, hfband, hf⟩ := exists_sLocalPolarPW_reflectedSmoothGenerator
    τ hτ χ hsec r hrd hrc hB hrs (fun h ↦ hrm (hχ.symm.trans h))
  let z : Zₛ := ⟨f, hfpolar⟩
  refine ⟨sLocalPWThetaSobolevMap (F := F) (S := S) (s := 0) halfPos ω z, ?_, ?_⟩
  · exact sLocalInvariantPWSobolev_mem (F := F) (S := S) (s := 0) le_rfl halfPos ω B z hfband
  · exact (hgen z).trans (ae_of_all _ hf)

end RiemannMasullo
