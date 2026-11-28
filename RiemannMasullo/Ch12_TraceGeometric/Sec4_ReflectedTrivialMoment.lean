module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_CriticalLineFourierPhase
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedMomentClosure
import RiemannMasullo.Ch05_ThetaZSpaces.Sec4
import RiemannMasullo.Ch12_TraceGeometric.Sec4
import Mathlib.Tactic.Ring

/-! # The trivial-character reflected moment -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "N" => sIdeleQuotientNorm F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "η" => sLocalNormOneQuotientMeasure F S
local notation "Zₛ" => sAdelePolarSubspace F S
local notation "W(" s ")" => CompactIntervalSobolev μJ (logSIdeleQuotientNorm F S) 0 0 s
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)
local notation "expUnit" => fun x : ℝ ↦ Units.mk0 (Real.toNNReal (Real.exp x)) (by positivity)
local notation "include₁" =>
  (ContinuousMonoidHom.mk (Subgroup.subtype (MonoidHom.ker (sIdeleQuotientNorm F S)))
    continuous_subtype_val : J₁ →ₜ* Jₛ)

private theorem trivialNormOneRestriction :
    (1 : PontryaginDual Jₛ).comp include₁ = (1 : PontryaginDual J₁) := by
  apply PontryaginDual.ext
  intro h
  rfl

private theorem trivialReflectedGenerator_exponentialMoment_eq_zero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) (f : Zₛ) :
    let d : ℂ := Real.sqrt (Measure.real η univ)
    (∫ y : ℝ, (Real.exp (-y / 2) : ℂ) *
      (d * sLocalRadialThetaHalfDensity τ 1 (sAdeleSchwartzFourier f.val) (-y))) = 0 := by
  intro d
  let p (y : ℝ) : ℂ := sLocalHomogeneousAdelicThetaLinearMap F S 1 (sAdeleSchwartzFourier f.val)
    (QuotientGroup.mk (τ (expUnit (-y)))) * (Real.exp (-y) : ℂ)
  have hraw : (∫ y, p y) = (sLocalTraceMeasureFactor S : ℂ) * f.val (Multiplicative.ofAdd 0) :=
    sLocalTrace_reflectedFourier_exponentialMoment (F := F) (S := S) τ hτ f.val
  have hf : f.val (Multiplicative.ofAdd 0) = 0 := ((mem_sAdelePolarSubspace f.val).mp f.property).1
  have hmul (y : ℝ) :
      (Real.exp (-y / 2) : ℂ) *
        (d * sLocalRadialThetaHalfDensity τ 1 (sAdeleSchwartzFourier f.val) (-y)) = d * p y := by
    have he : (Real.exp (-y) : ℂ) = (Real.exp (-y / 2) : ℂ) * (Real.exp (-y / 2) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add, show -y / 2 + -y / 2 = -y from by ring]
    simp only [p, sLocalRadialThetaHalfDensity, trivialNormOneRestriction,
      PontryaginDual.one_apply, Circle.coe_one, mul_one, he]
    ring
  calc
    _ = ∫ y, d * p y := integral_congr_ae (ae_of_all _ hmul)
    _ = d * ∫ y, p y := integral_const_mul _ _
    _ = 0 := by simp only [hraw, hf, mul_zero]

/-- The reflected image of the closed half-density band for the trivial
norm-one character has zero exponential moment. -/
theorem sLocalInvariantPWSobolev_reflectedTrivialMoment_of_representatives
    {s : ℝ} (hs : 0 ≤ s) (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (B : ℝ) (χ : PontryaginDual Jₛ) (T : W(s) →L[ℂ] FlatL2)
    (hχ : χ.comp include₁ = 1) (hsec : ∀ t, χ (QuotientGroup.mk (τ t)) = 1)
    (hgen : ∀ f : Zₛ,
      (T (sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) halfPos 1 f) : ℝ → ℂ)
        =ᵐ[volume] fun y ↦ (Real.sqrt (Measure.real η univ) : ℂ) *
          sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f.val) (-y))
    (hsupport : ∀ u ∈ sLocalInvariantPWSobolev (F := F) (S := S) hs halfPos 1 B,
      ∀ᵐ y : ℝ ∂volume, y < -Real.log B → T u y = 0)
    (u : W(s)) (hu : u ∈ sLocalInvariantPWSobolev (F := F) (S := S) hs halfPos 1 B) :
    Integrable (fun y ↦ (Real.exp (-y / 2) : ℂ) * T u y) ∧
      (∫ y, (Real.exp (-y / 2) : ℂ) * T u y) = 0 := by
  let σ : ℝ≥0ˣ →ₜ* Jₛ :=
    ⟨(QuotientGroup.mk' (sProjectedDiagonal F S)).comp τ.toMonoidHom,
      QuotientGroup.continuous_mk.comp τ.continuous⟩
  have hσ : RightInverse σ N := fun t ↦ (sIdeleQuotientNorm_mk F S (τ t)).trans (hτ t)
  have hχone : χ = 1 := (existsUnique_sLocalNormSectionCharacter σ hσ (1 : PontryaginDual J₁)).unique
    ⟨hχ, hsec⟩ ⟨trivialNormOneRestriction, fun t ↦ PontryaginDual.one_apply (σ t)⟩
  let r (f : Zₛ) (y : ℝ) : ℂ := (Real.sqrt (Measure.real η univ) : ℂ) *
    sLocalRadialThetaHalfDensity τ 1 (sAdeleSchwartzFourier f.val) (-y)
  have hRep (f : Zₛ) :
      (T (sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) halfPos 1 f) : ℝ → ℂ)
        =ᵐ[volume] r f := by
    simpa only [r, hχone, inv_one] using hgen f
  exact sLocalInvariantPWSobolev_reflectedExponentialMoment_eq_zero_of_generators
    (F := F) (S := S) hs halfPos 1 B (-Real.log B) T r hRep
    (fun f ↦ trivialReflectedGenerator_exponentialMoment_eq_zero τ hτ f.val) hsupport u hu

end RiemannMasullo
