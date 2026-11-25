module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2_WidthRestriction
public import RiemannMasullo.Ch10_TraceSpectral.Sec3

/-! # Compatibility of spectral convolution with width restriction -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped Topology NNReal ENNReal NumberField.AdeleRing

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => NumberField.IdeleClassGroup (NumberField.RingOfIntegers F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "x𝔽" => logIdeleClassNorm F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "W(" b ", " s ")" => CompactIntervalSobolev μ𝔽 x𝔽 (-b) b s
local notation "ν(" b ", " s ")" => intervalSobolevMeasure μ𝔽 x𝔽 (-b) b s
local notation "Θ(" a ", " h ", " hs ")" => globalThetaSobolev F a (neg_le_self h) hs
local notation "Q(" a ", " h ", " hs ")" => spectralSobolevQuotient F a (neg_le_self h) hs
local notation "τ(" b ", " s ", " h ", " hs ")" => hardySobolevTranslation μ𝔽 m𝔽 (-b) b s (neg_le_self h) hs
local notation "A(" b ", " s ", " h ", " hs ")" => hardySobolevTestAction μ𝔽 m𝔽 (-b) b s (neg_le_self h) hs

private theorem haar_ac_widthMeasure (b s : ℝ) : μ𝔽 ≪ ν(b,s) := by
  have hlog : Continuous x𝔽 := (NNReal.continuous_coe.comp (Units.continuous_val.comp
    (isProperMap_ideleClassNorm F).continuous)).log fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  have hd : Continuous (intervalSobolevDensity (-b) b s) := by
    unfold intervalSobolevDensity
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).max
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
      ((continuous_const.add (continuous_id.pow 2)).rpow_const (p := s/2) (fun _ ↦ Or.inl (by dsimp; positivity)))
  have hp (g : C𝔽) : 0 < intervalSobolevDensity (-b) b s (x𝔽 g) :=
    mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  exact withDensity_absolutelyContinuous' (hd.comp hlog).measurable.ennreal_ofReal.aemeasurable
    (.of_forall fun g ↦ ENNReal.ofReal_ne_zero_iff.mpr (hp g))

/-- Restriction preserving physical representatives commutes with left translation. -/
theorem hardySobolevTranslation_width_intertwines {α β s : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hs : 0 ≤ s) (I : W(β,s) →L[ℂ] W(α,s)) (hrep : ∀ q, (I q : C𝔽 → ℂ) =ᵐ[ν(α,s)] q)
    (g : C𝔽) (q : W(β,s)) : I (τ(β,s,hβ,hs) g q) = τ(α,s,hα,hs) g (I q) := by
  have hμ (v : W(β,s)) := (haar_ac_widthMeasure (F := F) α s).ae_eq (hrep v)
  apply Lp.ext
  apply (withDensity_absolutelyContinuous μ𝔽 _).ae_eq
  exact (hμ _).trans <| (hardySobolevTranslation_apply μ𝔽 m𝔽 (-β) β s (neg_le_self hβ) hs g q).trans <|
    ((measurePreserving_mul_left μ𝔽 g⁻¹).quasiMeasurePreserving.ae_eq_comp (hμ q)).symm.trans
      (hardySobolevTranslation_apply μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs g (I q)).symm

private theorem eval_positive_pettis {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : C𝔽 → V} {v : V} (h : HasPettisIntegral (.positive μ𝔽) f v) (ℓ : StrongDual ℂ V) :
    ℓ v = ∫ g, ℓ (f g) ∂μ𝔽 :=
  congrArg (fun z : PettisWeakCompletion V ↦ (show Module.Dual ℂ (StrongDual ℂ V) from z) ℓ) h.2

/-- Integrating translates against the same test preserves width compatibility. -/
theorem hardySobolevTestAction_width_intertwines {α β s : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hs : 0 ≤ s) (I : W(β,s) →L[ℂ] W(α,s)) (hrep : ∀ q, (I q : C𝔽 → ℂ) =ᵐ[ν(α,s)] q)
    (φ : BruhatCompactSupport C𝔽) (q : W(β,s)) : I (A(β,s,hβ,hs) φ q) = A(α,s,hα,hs) φ (I q) := by
  have hw := bruhatRegularizedAction_apply μ𝔽 (τ(β,s,hβ,hs))
    (exists_hardySobolevTranslation μ𝔽 m𝔽 (-β) β s (neg_le_self hβ) hs).choose_spec.2 φ q
  have hn := bruhatRegularizedAction_apply μ𝔽 (τ(α,s,hα,hs))
    (exists_hardySobolevTranslation μ𝔽 m𝔽 (-α) α s (neg_le_self hα) hs).choose_spec.2 φ (I q)
  have he (ℓ : StrongDual ℂ W(α,s)) : ℓ (I (A(β,s,hβ,hs) φ q)) = ℓ (A(α,s,hα,hs) φ (I q)) := by
    refine (eval_positive_pettis hw (ℓ.comp I)).trans <| Eq.trans ?_ (eval_positive_pettis hn ℓ).symm
    apply integral_congr_ae
    exact .of_forall fun g ↦ by
      simp only [ContinuousLinearMap.comp_apply, map_smul,
        hardySobolevTranslation_width_intertwines hα hβ hs I hrep g q]
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [inner_sub_right, sub_eq_zero]
  exact he (innerSL ℂ _)

/-- Convolution on the genuine spectral quotients commutes with the wide-to-narrow map. -/
theorem spectralConvolution_width_intertwines (a : ℝ) {α β s : ℝ} (hα : 0 ≤ α)
    (hab : α ≤ β) (hs : 0 ≤ s) (I : W(β,s) →L[ℂ] W(α,s))
    (hrep : ∀ q, (I q : C𝔽 → ℂ) =ᵐ[ν(α,s)] q)
    (J : Q(a,hα.trans hab,hs) →L[ℂ] Q(a,hα,hs))
    (hJ : ∀ q, J ((Θ(a,hα.trans hab,hs)).mkQ q) = (Θ(a,hα,hs)).mkQ (I q))
    (φ : BruhatCompactSupport C𝔽) :
    J.comp (spectralConvolution (F := F) a (neg_le_self (hα.trans hab)) hs φ) =
      (spectralConvolution (F := F) a (neg_le_self hα) hs φ).comp J := by
  apply ContinuousLinearMap.ext
  intro u
  obtain ⟨q, rfl⟩ := (Θ(a,hα.trans hab,hs)).mkQ_surjective u
  simp only [ContinuousLinearMap.comp_apply, spectralConvolution_mkQ, hJ,
    hardySobolevTestAction_width_intertwines hα (hα.trans hab) hs I hrep]

end RiemannMasullo
