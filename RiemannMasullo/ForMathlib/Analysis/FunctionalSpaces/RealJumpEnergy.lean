module

public import RiemannMasullo.ForMathlib.Analysis.FunctionalSpaces.NonlocalEnergy
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

/-! # Translation jump measures and bounded Lipschitz multipliers

The pair measure records `(x + r, x)` for a jump of size `r`. A finite second jump moment
makes bounded Lipschitz multiplication preserve the energy domain; this justifies the
products in the cardinal-interpolant cancellation identity.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace RiemannMasullo

/-- The measure on pairs of points obtained by applying a translation jump to Lebesgue measure. -/
def realJumpPairMeasure (κ : Measure ℝ) : Measure (ℝ × ℝ) :=
  (κ.prod volume).map (fun p : ℝ × ℝ ↦ (p.2 + p.1, p.2))

instance (κ : Measure ℝ) [SFinite κ] : SFinite (realJumpPairMeasure κ) := by
  unfold realJumpPairMeasure
  infer_instance

/-- Integration against the pair measure is integration over jump size and starting point. -/
theorem lintegral_realJumpPairMeasure (κ : Measure ℝ) [SFinite κ]
    (g : ℝ × ℝ → ENNReal) (hg : Measurable g) :
    (∫⁻ p, g p ∂realJumpPairMeasure κ) = ∫⁻ r, ∫⁻ x, g (x + r, x) ∂volume ∂κ := by
  unfold realJumpPairMeasure
  rw [lintegral_map hg (by fun_prop), lintegral_prod _ (by fun_prop)]

/-- Integrability against the pair measure can be checked in jump coordinates. -/
theorem integrable_realJumpPairMeasure_iff (κ : Measure ℝ)
    (g : ℝ × ℝ → ℝ) (hg : Measurable g) :
    Integrable g (realJumpPairMeasure κ) ↔
      Integrable (fun p : ℝ × ℝ ↦ g (p.2 + p.1, p.2)) (κ.prod volume) := by
  exact integrable_map_measure hg.aestronglyMeasurable (by fun_prop)

private theorem norm_multiplier_difference_sq_le {b h : ℝ → ℂ} {B : ℝ}
    {L : NNReal} (hB : ∀ x, ‖b x‖ ≤ B) (hb : LipschitzWith L b) (x y : ℝ) :
    ‖b x * h x - b y * h y‖ ^ 2 ≤
      2 * B ^ 2 * ‖h x - h y‖ ^ 2 + 2 * (L : ℝ) ^ 2 * (x - y) ^ 2 * ‖h y‖ ^ 2 := by
  have hB₀ : 0 ≤ B := (norm_nonneg (b 0)).trans (hB 0)
  have he : b x * h x - b y * h y = b x * (h x - h y) + (b x - b y) * h y := by ring
  have hn : ‖b x * h x - b y * h y‖ ≤ B * ‖h x - h y‖ + (L : ℝ) * |x - y| * ‖h y‖ := by
    rw [he]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hb.norm_sub_le x y)
        (norm_nonneg _))
  have hn' := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  have hsq := sq_nonneg (B * ‖h x - h y‖ - (L : ℝ) * |x - y| * ‖h y‖)
  calc
    _ ≤ (B * ‖h x - h y‖ + (L : ℝ) * |x - y| * ‖h y‖) ^ 2 := hn'
    _ ≤ 2 * (B * ‖h x - h y‖) ^ 2 + 2 * ((L : ℝ) * |x - y| * ‖h y‖) ^ 2 := by
      nlinarith [hsq]
    _ = _ := by simp only [mul_pow, sq_abs]; ring

/-- A bounded Lipschitz multiplier preserves square-integrable jumps whenever the jump
measure has a finite second moment. -/
theorem integrable_jump_sq_mul_of_lipschitz (κ : Measure ℝ) {b h : ℝ → ℂ}
    (hh : Measurable h) (hh₂ : MemLp h 2) {B : ℝ} {L : NNReal}
    (hB : ∀ x, ‖b x‖ ≤ B) (hb : LipschitzWith L b)
    (hκ : Integrable (fun r : ℝ ↦ r ^ 2) κ)
    (hj : Integrable (fun p : ℝ × ℝ ↦ ‖h p.1 - h p.2‖ ^ 2) (realJumpPairMeasure κ)) :
    Integrable (fun p : ℝ × ℝ ↦ ‖b p.1 * h p.1 - b p.2 * h p.2‖ ^ 2)
      (realJumpPairMeasure κ) := by
  have hbc := hb.continuous
  rw [integrable_realJumpPairMeasure_iff _ _ (by fun_prop)] at hj ⊢
  have hlocal : Integrable (fun x : ℝ ↦ ‖h x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hh₂.aestronglyMeasurable).mp hh₂
  have hprod := hκ.mul_prod hlocal
  have hbound := (hj.const_mul (2 * B ^ 2)).add (hprod.const_mul (2 * (L : ℝ) ^ 2))
  apply hbound.mono' (by apply Measurable.aestronglyMeasurable; fun_prop)
  exact .of_forall fun p ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hle := norm_multiplier_difference_sq_le hB hb (p.2 + p.1) p.2 (h := h)
    simpa only [add_sub_cancel_left, mul_assoc, Pi.add_def] using hle


/-- Changing a measurable function on a Lebesgue null set changes neither endpoint of
a translation jump at almost every pair. -/
theorem ae_eq_realJumpPair_endpoints (κ : Measure ℝ) [SFinite κ]
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [T2Space E] {f g : ℝ → E}
    (hf : Measurable f) (hg : Measurable g) (hfg : f =ᵐ[volume] g) :
    ∀ᵐ p : ℝ × ℝ ∂realJumpPairMeasure κ, f p.1 = g p.1 ∧ f p.2 = g p.2 := by
  unfold realJumpPairMeasure
  rw [ae_map_iff (by fun_prop) (by measurability), Measure.ae_prod_iff_ae_ae (by measurability)]
  exact .of_forall fun r ↦ by
    have hs := (measurePreserving_add_right (volume : Measure ℝ) r).quasiMeasurePreserving.ae hfg
    filter_upwards [hs, hfg] with x hx hx'
    exact ⟨hx, hx'⟩

end RiemannMasullo
