module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4
import RiemannMasullo.Ch03_IdelicZeta.Sec3

/-! # Linearity in the compact lift of the radial cutoff kernel -/

public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Hₛ" => sProjectedDiagonal F S
local notation "νₛ" => sAdditiveTamagawaMeasure F S
local notation "ψₛ" => sAdeleStandardCharacter F S
local notation "fourierₛ" => tamagawaFourier νₛ ψₛ
set_option quotPrecheck false in
local notation "normS(" x ")" => (((sIdeleNorm F S x).val : ℝ))
local notation "modS(" z ")" => ((∏ w : InfinitePlace F, ‖(z : Aₛ).1 w‖ ^ InfinitePlace.mult w) *
  ∏ v : S, ‖(z : Aₛ).2 v‖)
local notation "testₛ" => SchwartzBruhat (Multiplicative Aₛ)
local notation "testAt(" f "," x ")" => (f : testₛ) (Multiplicative.ofAdd x)

attribute [local instance] instSAdeleMeasurableSpaceSec1 instSIdeleLocallyCompactSec1
local instance : T2Space Iₛ := (sIdeleGroup_description F S).2.1

section RadialKernelLiftLinearity

private theorem sLocalTraceEta_add_lift
    (f g : BruhatCompactSupport Iₛ) (ξ : Hₛ) (z : Aₛ) :
    sLocalTraceEta (f + g) ξ z = sLocalTraceEta f ξ z + sLocalTraceEta g ξ z := by
  unfold sLocalTraceEta
  by_cases hz : 1 + z ∈ range (Units.val : Iₛ → Aₛ)
  · obtain ⟨u, hu⟩ := hz
    rw [← hu]
    simp only [Units.val_injective.extend_apply]
    change (f.val ((ξ.val⁻¹ * u)⁻¹) + g.val ((ξ.val⁻¹ * u)⁻¹)) /
        (Real.sqrt (normS(ξ.val⁻¹ * u)) : ℂ) = _
    exact add_div _ _ _
  · rw [Function.extend_apply' _ _ _ hz, Function.extend_apply' _ _ _ hz,
      Function.extend_apply' _ _ _ hz, zero_add]

private theorem sLocalTraceEta_smul_lift
    (c : ℂ) (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (z : Aₛ) :
    sLocalTraceEta (c • f) ξ z = c * sLocalTraceEta f ξ z := by
  unfold sLocalTraceEta
  by_cases hz : 1 + z ∈ range (Units.val : Iₛ → Aₛ)
  · obtain ⟨u, hu⟩ := hz
    rw [← hu]
    simp only [Units.val_injective.extend_apply]
    change (c * f.val ((ξ.val⁻¹ * u)⁻¹)) / (Real.sqrt (normS(ξ.val⁻¹ * u)) : ℂ) = _
    exact mul_div_assoc _ _ _
  · rw [Function.extend_apply' _ _ _ hz, Function.extend_apply' _ _ _ hz, mul_zero]

/-- Paper: (12.4.1.4), p. 515, and (12.4.1.20)–(12.4.1.21), p. 518. The
cutoff kernel at fixed input and output is complex-linear in the compact lift.
Deviation: This uses a bounded continuous radial frequency profile. -/
theorem sLocalTraceCutoffKernel_radial_lift_isLinear
    (ρ : Iₛ → ℂ) (b : ℝ → ℂ) (hb : Continuous b)
    {B : ℝ} (hB : ∀ t, 0 ≤ t → ‖b t‖ ≤ B) (x : Iₛ) (y : Aₛ) :
    IsLinearMap ℂ (fun f : BruhatCompactSupport Iₛ =>
      sLocalTraceCutoffKernel f ρ (fun v ↦ b (modS(v))) x y) := by
  classical
  let : BorelSpace Aₛ := sAdeleRing_borelSpace
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aₛ := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace F) → w.Completion) × ((v : S) → v.val.adicCompletion F)))
  let E (f : BruhatCompactSupport Iₛ) : testₛ :=
    (SLocalTraceEta.eta_test f (1 : Hₛ)).choose
  have hE (f : BruhatCompactSupport Iₛ) (z : Aₛ) :
      testAt(E f,z) = sLocalTraceEta f 1 z :=
    (SLocalTraceEta.eta_test f (1 : Hₛ)).choose_spec z
  have hEadd (f g : BruhatCompactSupport Iₛ) : E (f + g) = E f + E g := by
    apply SchwartzBruhat.ext
    intro z
    change testAt(E (f + g),z.toAdd) = testAt(E f,z.toAdd) + testAt(E g,z.toAdd)
    rw [hE (f + g), hE f, hE g, sLocalTraceEta_add_lift]
  have hEsmul (c : ℂ) (f : BruhatCompactSupport Iₛ) : E (c • f) = c • E f := by
    apply SchwartzBruhat.ext
    intro z
    change testAt(E (c • f),z.toAdd) = c * testAt(E f,z.toAdd)
    rw [hE (c • f), hE f, sLocalTraceEta_smul_lift]
  obtain ⟨T, hT⟩ := sLocal_fourier_continuousLinear (F := F) (S := S)
  have hFT (f : BruhatCompactSupport Iₛ) (w : Aₛ) :
      testAt(T (E f),w) = fourierₛ (sLocalTraceEta f 1) w := by
    rw [hT (E f)]
    change fourierₛ (fun z : Aₛ => testAt(E f,z)) w = _
    rw [funext (hE f)]
  have hFTadd (f g : BruhatCompactSupport Iₛ) (w : Aₛ) :
      fourierₛ (sLocalTraceEta (f + g) 1) w =
        fourierₛ (sLocalTraceEta f 1) w + fourierₛ (sLocalTraceEta g 1) w := by
    rw [← hFT (f + g) w, ← hFT f w, ← hFT g w, hEadd]
    exact congrArg (fun v : testₛ => testAt(v,w)) (T.map_add (E f) (E g))
  have hFTsmul (c : ℂ) (f : BruhatCompactSupport Iₛ) (w : Aₛ) :
      fourierₛ (sLocalTraceEta (c • f) 1) w = c * fourierₛ (sLocalTraceEta f 1) w := by
    rw [← hFT (c • f) w, ← hFT f w, hEsmul]
    exact congrArg (fun v : testₛ => testAt(v,w)) (T.map_smul c (E f))

  let bₓ (w : Aₛ) : ℂ := b (modS(w) / normS(x))
  let p (w : Aₛ) : ℂ := ψₛ (w * ((x⁻¹).val * y - 1))
  let G (f : BruhatCompactSupport Iₛ) (w : Aₛ) : ℂ :=
    bₓ w * fourierₛ (sLocalTraceEta f 1) w * p w
  let C : ℂ := ρ x * (sLocalTraceMeasureFactor S : ℂ) / (normS(x) : ℂ)
  have hm : Continuous (fun w : Aₛ ↦ modS(w)) :=
    (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_fst).norm.pow _).mul
      (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  have hbₓ : Continuous bₓ := hb.comp (hm.div_const _)
  obtain ⟨e, he, -⟩ := sAdditiveTamagawaMeasure_selfDual F S
  let χ := e (Multiplicative.ofAdd (1 : Aₛ))
  have hchar (w : Aₛ) : χ (Multiplicative.ofAdd w) = ψₛ w := by
    simpa only [one_mul] using he 1 w
  have hχ : Continuous (fun w : Aₛ ↦ (ψₛ w : ℂ)) :=
    ((continuous_subtype_val.comp χ.continuous).comp continuous_ofAdd).congr
      (fun w ↦ congrArg (fun z : Circle ↦ (z : ℂ)) (hchar w))
  have hp : Continuous p := hχ.comp (continuous_id.mul_const _)
  have hG (f : BruhatCompactSupport Iₛ) : Integrable (G f) νₛ := by
    have hProfile : ∀ᵐ w ∂νₛ, ‖bₓ w‖ ≤ B :=
      ae_of_all _ fun w ↦ hB _ (div_nonneg (by positivity : 0 ≤ modS(w))
        (NNReal.coe_nonneg _))
    have hPhase : ∀ᵐ w ∂νₛ, ‖p w‖ ≤ 1 :=
      ae_of_all _ fun w ↦ (Circle.norm_coe (ψₛ (w * ((x⁻¹).val * y - 1)))).le
    exact ((sLocalTraceEta_fourier_integrable f 1).bdd_mul
      hbₓ.aestronglyMeasurable hProfile).mul_bdd hp.aestronglyMeasurable hPhase
  have hK (f : BruhatCompactSupport Iₛ) :
      sLocalTraceCutoffKernel f ρ (fun v ↦ b (modS(v))) x y =
        C * ∫ w, G f w ∂νₛ :=
    sLocalTraceCutoffKernel_scaled_radial_fourier f ρ b x y
  constructor
  · intro f g
    change sLocalTraceCutoffKernel (f + g) ρ (fun v ↦ b (modS(v))) x y = _
    rw [hK (f + g), hK f, hK g]
    have hAdd : G (f + g) = fun w ↦ G f w + G g w := by
      funext w
      simp only [G, hFTadd, mul_add, add_mul]
    rw [hAdd, integral_add (hG f) (hG g), mul_add]
  · intro c f
    change sLocalTraceCutoffKernel (c • f) ρ (fun v ↦ b (modS(v))) x y =
      c * sLocalTraceCutoffKernel f ρ (fun v ↦ b (modS(v))) x y
    rw [hK (c • f), hK f]
    have hSmul : G (c • f) = fun w ↦ c * G f w := by
      funext w
      dsimp only [G]
      rw [hFTsmul]
      ring
    rw [hSmul, integral_const_mul]
    exact mul_left_comm _ _ _

end RadialKernelLiftLinearity

end RiemannMasullo
