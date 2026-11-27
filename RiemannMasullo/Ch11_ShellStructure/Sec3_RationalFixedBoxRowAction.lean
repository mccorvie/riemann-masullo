module
public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxRows
public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxCircle
public import Mathlib.Analysis.Fourier.AddCircle

/-! # Equivariant rows on the actual rational fixed-box packet

Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496. The bounded normalized coordinates
of the completed packet intertwine the circle action on the actual quotient.
The zero coordinate uses the first nonvanishing earlier-stage Mellin jet.
The circle and closed-stage constructions come from PRs #7652 and #7661;
the coordinate normalization follows fpet19's written construction in #7351.
-/

public noncomputable section
open Filter MeasureTheory Set Function FourierTransform
open scoped FourierTransform SchwartzMap Topology NNReal
namespace RiemannMasullo.RationalPacket

private theorem dampedStage_dilate_exp (h : ℝ) (T : Finset ℕ) (f : 𝓢(ℝ, ℂ)) :
    dampedStage T (dilate (Real.exp (-h)) (Real.exp_pos _) f) =
      (dampedStage T f) ∘ (fun x : ℝ ↦ x + -h) := by
  ext x
  simp only [dampedStage_apply, stage_dilate_real, Real.log_exp, neg_neg, Function.comp_apply]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  rw [show -x/2 + h/2 = -(x + -h)/2 by ring]

/-- Fourier samples of the actual damped stage transform by the exact dilation character. -/
theorem fourier_dampedStage_dilate_exp (h : ℝ) (T : Finset ℕ) (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (dampedStage T (dilate (Real.exp (-h)) (Real.exp_pos _) f)) ξ =
      (Real.fourierChar (-h * ξ) : ℂ) * 𝓕 (dampedStage T f) ξ := by
  rw [dampedStage_dilate_exp]
  simpa only [Fourier.fourierIntegral_def, Real.fourier_real_eq, Circle.smul_def, smul_eq_mul] using
    congrFun (Fourier.fourierIntegral_comp_add_right Real.fourierChar volume (dampedStage T f) (-h)) ξ

/-- Forward logarithmic translation of a stage is the stage of its physical source dilation. -/
theorem halfShift_stage_ae (h : ℝ) (T : Finset ℕ) (f : 𝓢(ℝ, ℂ))
    (F : ℝ →₂[volume] ℂ) (hF : F =ᵐ[volume] stage T f) :
    halfShift h F =ᵐ[volume] stage T (dilate (Real.exp (-h)) (Real.exp_pos _) f) := by
  have hs := (measurePreserving_add_right (volume : Measure ℝ) (-h)).quasiMeasurePreserving.ae_eq_comp hF
  filter_upwards [halfShift_ae h F, hs] with x hx hsx
  rw [hx, stage_dilate_real, Real.log_exp, neg_neg]
  simpa only [Function.comp_def, sub_eq_add_neg] using congrArg
    (fun z : ℂ ↦ (Real.exp (h/2) : ℂ) * z) hsx

/-- Every normalized row on the genuine completed earlier stage intertwines the
positive dilation character, including the top-jet normalized zero row. -/
theorem packetRow_halfShift {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ q ∈ T, q.Prime) {p : ℕ} (hp : p.Prime) (hpT : p ∉ T)
    {h : ℝ} (hh : 0 ≤ h) {F : (ℝ →₂[volume] ℂ)} (hF : F ∈ closure (stageGenerators X T)) (n : ℤ) :
    packetRow X T p n (halfShift h F) =
      (Real.fourierChar (-h * ((n : ℝ) / Real.log p)) : ℂ) * packetRow X T p n F := by
  apply closure_minimal (s := stageGenerators X T)
    (t := {G | packetRow X T p n (halfShift h G) =
      (Real.fourierChar (-h * ((n : ℝ) / Real.log p)) : ℂ) * packetRow X T p n G}) ?_ ?_ hF
  · intro G hG
    obtain ⟨f, hf, h0, hb, hG⟩ := (mem_stageGenerators_iff X T G).mp hG
    let r := Real.exp (-h)
    have hr : 0 < r := Real.exp_pos _
    have hr1 : r ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hh)
    let g := dilate r hr f
    have hg : g 0 = 0 := by simp [g, dilate_apply, hf]
    have hg0 : (𝓕 g) 0 = 0 := by simp [g, fourier_dilate hr, h0]
    have hgb : ∀ y : ℝ, X / (∏ q ∈ T, (q : ℝ)) < |y| → (𝓕 g) y = 0 := by
      intro y hy
      rw [show g = dilate r hr f from rfl, fourier_dilate hr, hb, smul_zero]
      rw [abs_div, abs_of_pos hr]
      exact hy.trans_le (le_div_self (abs_nonneg y) hr hr1)
    change packetRow X T p n (halfShift h G) = _
    rw [packetRow_stage hX T hT hp hpT g hg hg0 hgb _ (halfShift_stage_ae h T f G hG),
      packetRow_stage hX T hT hp hpT f hf h0 hb G hG]
    exact fourier_dampedStage_dilate_exp h ∅ f _
  · exact isClosed_eq ((packetRow X T p n).continuous.comp (halfShift h).continuous)
      (continuous_const.mul (packetRow X T p n).continuous)

/-- The normalized coordinate descended through the actual next closed stage. -/
def fixedBoxPacketRow {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT1 : ∀ q ∈ T, 1 ≤ q) (p : ℕ) (hTp1 : ∀ q ∈ insert p T, 1 ≤ q)
    (hT : ∀ q ∈ T, q.Prime) (hp : p.Prime) (hpT : p ∉ T) (n : ℤ) :
    FixedBoxQuotient[X,T,hT1,p,hTp1] →L[ℂ] ℂ :=
  (fixedBoxDenominator X T hT1 p hTp1).toSubmodule.liftQL
    ((packetRow X T p n).comp (closedStageSubmodule X T hT1).toSubmodule.subtypeL) (by
      intro F hF
      change packetRow X T p n (F : ℝ →₂[volume] ℂ) = 0
      exact packetRow_eq_zero_of_mem_next hX T hT hp hpT
        ((mem_closedStageSubmodule_iff X (insert p T) hTp1 (F : ℝ →₂[volume] ℂ)).mp
          ((mem_fixedBoxDenominator_iff X T hT1 p hTp1 F).mp hF)) n)

/-- Evaluation of a quotient coordinate on an actual representative. -/
theorem fixedBoxPacketRow_mk {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT1 : ∀ q ∈ T, 1 ≤ q) (p : ℕ) (hTp1 : ∀ q ∈ insert p T, 1 ≤ q)
    (hT : ∀ q ∈ T, q.Prime) (hp : p.Prime) (hpT : p ∉ T) (n : ℤ)
    (u : closedStageSubmodule X T hT1) :
    fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT n
      ((fixedBoxDenominator X T hT1 p hTp1).toSubmodule.mkQL u) =
        packetRow X T p n (u : ℝ →₂[volume] ℂ) := by rfl

/-- The actual quotient coordinates intertwine every forward dilation. -/
theorem fixedBoxPacketRow_forwardShift {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT1 : ∀ q ∈ T, 1 ≤ q) (p : ℕ) (hTp1 : ∀ q ∈ insert p T, 1 ≤ q)
    (hT : ∀ q ∈ T, q.Prime) (hp : p.Prime) (hpT : p ∉ T) (n : ℤ)
    (h : ℝ≥0) (u : FixedBoxQuotient[X,T,hT1,p,hTp1]) :
    fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT n
      (fixedBoxForwardShift T hT1 p hTp1 hX h u) =
      (Real.fourierChar (-(h : ℝ) * ((n : ℝ) / Real.log p)) : ℂ) *
        fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT n u := by
  obtain ⟨v, rfl⟩ := (fixedBoxDenominator X T hT1 p hTp1).toSubmodule.mkQ_surjective u
  change fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT n
    (fixedBoxForwardShift T hT1 p hTp1 hX h
      ((fixedBoxDenominator X T hT1 p hTp1).toSubmodule.mkQL v)) = _
  rw [fixedBoxForwardShift_mk, fixedBoxPacketRow_mk]
  change packetRow X T p n (halfShift (h : ℝ) (v : ℝ →₂[volume] ℂ)) =
    (Real.fourierChar (-(h : ℝ) * ((n : ℝ) / Real.log p)) : ℂ) *
      packetRow X T p n (v : ℝ →₂[volume] ℂ)
  exact packetRow_halfShift hX T hT hp hpT h.property
    ((mem_closedStageSubmodule_iff X T hT1 (v : ℝ →₂[volume] ℂ)).mp v.property) n

private theorem dilation_character_eq_circle (p : ℕ) (n : ℤ) (h : ℝ) :
    (Real.fourierChar (-h * ((n : ℝ) / Real.log p)) : ℂ) =
      _root_.fourier (-n) (h : AddCircle (Real.log p)) := by
  rw [Real.fourierChar_apply, _root_.fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- Every bounded normalized coordinate of the completed fixed-box packet is
an equivariant functional for its genuine circle action. The Fourier convention
assigns row `n` the circle character `-n`. -/
theorem fixedBoxPacketRow_circleAction {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT1 : ∀ q ∈ T, 1 ≤ q) (p : ℕ) (hTp1 : ∀ q ∈ insert p T, 1 ≤ q)
    (hT : ∀ q ∈ T, q.Prime) (hp : p.Prime) (hpT : p ∉ T) (n : ℤ)
    (s : AddCircle (Real.log p)) (u : FixedBoxQuotient[X,T,hT1,p,hTp1]) :
    fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT n
      (fixedBoxCircleAction T hT1 p hTp1 hX hp.one_lt s u) =
      _root_.fourier (-n) s * fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT n u := by
  let : Fact (0 < Real.log (p : ℝ)) := ⟨Real.log_pos (by exact_mod_cast hp.one_lt)⟩
  obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico s
  rw [fixedBoxCircleAction_coe_of_mem T hT1 p hTp1 hX hp.one_lt ht,
    fixedBoxPacketRow_forwardShift, Real.coe_toNNReal _ ht.1, dilation_character_eq_circle]

end RiemannMasullo.RationalPacket
