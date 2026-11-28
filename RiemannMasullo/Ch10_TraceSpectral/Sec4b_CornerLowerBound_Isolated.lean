module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_CornerScalar_Isolated
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_CornerRiesz_Isolated
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_CornerOrbit_Isolated
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch10_TraceSpectral.Sec2
import RiemannMasullo.Ch09_HardySobolev.Sec2
import RiemannMasullo.Ch09_HardySobolev.Sec3

/-!
# Sharp Sobolev corner lower bound on `G_a ∘ A(φ) ∘ P_a` (`#7406`)

This module combines the scalar corner asymptotics (`Sec4b_CornerScalar_Isolated`) with the
adelic norm-flow factorization (`Sec4b_CornerRiesz_Isolated`, `Sec4b_CornerOrbit_Isolated`) to
prove the structural corner lower bound on `W(α, s) = CompactIntervalSobolev μ𝔽 logNorm (-α) α s`:

1. `rieszZeroJet` & `rieszZeroJet_mem_orthogonal`: the explicit Riesz representer for a
   depth-zero strip jet lies in `Θ₀ᗮ = range P_a`.
2. `spectralStrip_riesz_convolution_inner_asymptotic`: when `α > 0`, `s > 1`, and
   `σ ∈ [-α, α]`, `⟪A(φ) r_{σ, T}, u⟫ = (tamagawaNormFactor F) * (4 α) * G(0) / (T + τ)^2 + O(1/|T + τ|^3)`.
3. `spectralStrip_geometricCommutator_riesz_lower_bound`: when `u ∈ Θ₀` has nonzero corner
   pairing `G(0) ≠ 0` and `r_{σ, T} ∈ Θ₀ᗮ`, `‖(G_a ∘ A(φ) ∘ P_a)(r_{σ, T} / ‖r_{σ, T}‖)‖ ≥ c / (T + τ)^2`.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.Isolated

section RieszAndCornerLowerBound

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => logIdeleClassNorm F
local notation "W(" α ", " s ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α s

def lpEquivOfMeasureEq {α : Type*} [MeasurableSpace α] {μ₁ μ₂ : Measure α} (h : μ₁ = μ₂) :
    Lp ℂ 2 μ₁ ≃ₗᵢ[ℂ] Lp ℂ 2 μ₂ := by
  subst h
  exact LinearIsometryEquiv.refl ℂ (Lp ℂ 2 μ₁)

lemma weightedSobolevMeasure_eq_interval (a b s : ℝ) :
    weightedSobolevMeasure F (intervalSobolevDensity a b s) =
      intervalSobolevMeasure μ𝔽 logNorm a b s false := by
  unfold weightedSobolevMeasure intervalSobolevMeasure
  simp only [Bool.false_eq_true, ↓reduceIte]

/-- Isometric identification `CompactIntervalSobolev μ𝔽 logNorm a b s ≃ₗᵢ[ℂ] Lp ℂ 2 (weightedSobolevMeasure F (intervalSobolevDensity a b s))`. -/
def intervalToWeightedEquiv (a b s : ℝ) :
    CompactIntervalSobolev μ𝔽 logNorm a b s ≃ₗᵢ[ℂ]
      Lp ℂ 2 (weightedSobolevMeasure F (intervalSobolevDensity a b s)) :=
  lpEquivOfMeasureEq (weightedSobolevMeasure_eq_interval (F := F) a b s).symm

private lemma intervalToWeightedEquiv_ae {a b s : ℝ} (u : CompactIntervalSobolev μ𝔽 logNorm a b s) :
    (intervalToWeightedEquiv (F := F) a b s u : C𝔽 → ℂ) =ᵐ[μ𝔽] (u : C𝔽 → ℂ) := by
  change (lpEquivOfMeasureEq (weightedSobolevMeasure_eq_interval (F := F) a b s).symm u : C𝔽 → ℂ) =ᵐ[μ𝔽] u
  generalize (weightedSobolevMeasure_eq_interval (F := F) a b s).symm = h
  cases h
  exact Filter.EventuallyEq.refl _ _

private lemma intervalToWeightedEquiv_symm_ae {a b s : ℝ}
    (v : Lp ℂ 2 (weightedSobolevMeasure F (intervalSobolevDensity a b s))) :
    ((intervalToWeightedEquiv (F := F) a b s).symm v : C𝔽 → ℂ) =ᵐ[μ𝔽] (v : C𝔽 → ℂ) := by
  change ((lpEquivOfMeasureEq (weightedSobolevMeasure_eq_interval (F := F) a b s).symm).symm v : C𝔽 → ℂ) =ᵐ[μ𝔽] v
  generalize (weightedSobolevMeasure_eq_interval (F := F) a b s).symm = h
  cases h
  exact Filter.EventuallyEq.refl _ _

/-- Explicit Riesz representer of the depth-zero evaluation `f ↦ ∫ f * χ |·|^{σ + iT} dμ𝔽`
in the sharp Sobolev strip space `CompactIntervalSobolev μ𝔽 logNorm (-α) α s`. -/
def rieszZeroJet {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) {σ : ℝ} (hσ : σ ∈ Icc (-α) α)
    (ψ : PontryaginDual C𝔽) (T : ℝ) : W(α, s) :=
  (intervalToWeightedEquiv (-α) α s).symm
    (weightedRieszJet (F := F) (continuous_intervalSobolevDensity (-α) α s)
      (intervalSobolevDensity_pos (-α) α s) hs (exp_div_intervalSobolevDensity_dom hα hσ) ψ T)

lemma rieszZeroJet_inner {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) {σ : ℝ} (hσ : σ ∈ Icc (-α) α)
    (ψ : PontryaginDual C𝔽) (T : ℝ) (u : W(α, s)) :
    Integrable (fun g : C𝔽 ↦ u g * ideleClassNormTwist ψ (↑σ + ↑T * Complex.I) g) μ𝔽 ∧
      @inner ℂ W(α, s) _ (rieszZeroJet hα hs hσ ψ T) u =
        ∫ g : C𝔽, u g * ideleClassNormTwist ψ (↑σ + ↑T * Complex.I) g ∂μ𝔽 := by
  let E := intervalToWeightedEquiv (F := F) (-α) α s
  let rW := weightedRieszJet (F := F) (continuous_intervalSobolevDensity (-α) α s)
    (intervalSobolevDensity_pos (-α) α s) hs (exp_div_intervalSobolevDensity_dom hα hσ) ψ T
  have hw := weightedRieszJet_inner (continuous_intervalSobolevDensity (-α) α s)
    (intervalSobolevDensity_pos (-α) α s) hs (exp_div_intervalSobolevDensity_dom hα hσ) ψ T (E u)
  have heq_f : (fun g : C𝔽 ↦ E u g * ideleClassNormTwist ψ (↑σ + ↑T * Complex.I) g) =ᵐ[μ𝔽]
      fun g : C𝔽 ↦ u g * ideleClassNormTwist ψ (↑σ + ↑T * Complex.I) g :=
    (intervalToWeightedEquiv_ae u).mono fun g hg ↦ by dsimp only; rw [hg]
  refine ⟨hw.1.congr heq_f, ?_⟩
  calc @inner ℂ W(α, s) _ (rieszZeroJet hα hs hσ ψ T) u
      = @inner ℂ _ _ (E (E.symm rW)) (E u) := (E.inner_map_map _ _).symm
    _ = @inner ℂ _ _ rW (E u) := by rw [E.apply_symm_apply]
    _ = ∫ g : C𝔽, E u g * ideleClassNormTwist ψ (↑σ + ↑T * Complex.I) g ∂μ𝔽 := hw.2
    _ = ∫ g : C𝔽, u g * ideleClassNormTwist ψ (↑σ + ↑T * Complex.I) g ∂μ𝔽 := integral_congr_ae heq_f

lemma rieszZeroJet_norm_sq {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) {σ : ℝ} (hσ : σ ∈ Icc (-α) α)
    (ψ : PontryaginDual C𝔽) (T : ℝ) :
    0 < ‖rieszZeroJet (F := F) hα hs hσ ψ T‖ ^ 2 ∧
      ‖rieszZeroJet (F := F) hα hs hσ ψ T‖ ^ 2 =
        tamagawaNormFactor F * ∫ x : ℝ, Real.exp (2 * σ * x) / intervalSobolevDensity (-α) α s x := by
  have hnorm : ‖rieszZeroJet (F := F) hα hs hσ ψ T‖ =
      ‖weightedRieszJet (F := F) (continuous_intervalSobolevDensity (-α) α s)
        (intervalSobolevDensity_pos (-α) α s) hs (exp_div_intervalSobolevDensity_dom hα hσ) ψ T‖ :=
    (intervalToWeightedEquiv (-α) α s).symm.norm_map _
  rw [hnorm]
  exact weightedRieszJet_norm_sq (continuous_intervalSobolevDensity (-α) α s)
    (intervalSobolevDensity_pos (-α) α s) hs (exp_div_intervalSobolevDensity_dom hα hσ) ψ T

/-- Every depth-zero Riesz representer at a strip zero `(ω, σ, T)` lies in `Θ₀ᗮ`. -/
theorem rieszZeroJet_mem_orthogonal (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (j : SpectralStripJetIndex (F := F) χ a α s) (hj0 : j.val.2.2.2 = 0) :
    let hI : -α ≤ α := (neg_nonpos.mpr hα).trans hα
    let hs₀ : 0 ≤ s := zero_le_one.trans hs.le
    let hσ : j.val.2.1 ∈ Icc (-α) α := (j.mem_strip_order_pos hα).1
    rieszZeroJet (F := F) hα hs hσ (χ j.val.1) j.val.2.2.1 ∈
      (globalThetaSobolev F a hI hs₀).orthogonal := by
  intro hI hs₀ hσ y hy
  have hfwd := spectralStripJet_commonKernel_forward (F := F) χ hα hs₀ y hy j
  have hdual_abs : μ𝔽 ≪ intervalSobolevMeasure μ𝔽 logNorm (-α) α s true := by
    refine withDensity_absolutelyContinuous' ?_ ?_
    · exact (((continuous_intervalSobolevDensity (-α) α s).inv₀ fun x ↦
        (intervalSobolevDensity_pos (-α) α s x).ne').measurable.comp measurable_logNorm).ennreal_ofReal.aemeasurable
    · refine ae_of_all _ fun g ↦ (ENNReal.ofReal_pos.mpr ?_).ne'
      exact inv_pos.mpr (intervalSobolevDensity_pos (-α) α s _)
  let ujet : CompactIntervalSobolev μ𝔽 logNorm (-α) α s true :=
    (spectralStripJet_memLp (F := F) χ hα hs₀ j).toLp
      (spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)
  have hrep : (ujet : C𝔽 → ℂ) =ᵐ[μ𝔽]
      spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2 :=
    hdual_abs.ae_le (MemLp.coeFn_toLp _)
  have hpair_eq : spectralSobolevPairing y ujet =
      @inner ℂ W(α, s) _ (rieszZeroJet hα hs hσ (χ j.val.1) j.val.2.2.1) y := by
    rw [(rieszZeroJet_inner hα hs hσ (χ j.val.1) j.val.2.2.1 y).2]
    change ∫ g : C𝔽, y g * ujet g ∂μ𝔽 = _
    refine integral_congr_ae ?_
    filter_upwards [hrep] with g hg
    rw [hg]
    simp only [spectralZeroJet, hj0, pow_zero, mul_one]
  rw [hpair_eq] at hfwd
  exact inner_eq_zero_symm.mp hfwd

lemma memLp_two_one_add_sq_neg_quarter {s : ℝ} (hs : 1 < s) :
    MemLp (fun x : ℝ ↦ (1 + x ^ 2) ^ (-s / 4)) 2 volume := by
  have hcont : Continuous (fun x : ℝ ↦ (1 + x ^ 2) ^ (-s / 4)) :=
    (continuous_const.add (continuous_id.pow 2)).rpow_const fun x ↦
      Or.inl (by positivity : (1 : ℝ) + x ^ 2 ≠ 0)
  refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr ?_
  refine (integrable_one_add_sq_neg_rpow hs).congr (ae_of_all _ fun x ↦ ?_)
  dsimp only
  rw [Real.norm_of_nonneg (by positivity)]
  conv_rhs => rw [← Real.rpow_two, ← Real.rpow_mul (by positivity)]
  congr 1; ring

private lemma sharp_sqrt_exp_pos_le {α s σ : ℝ} (_hα : 0 ≤ α) (hσ : σ ≤ α) {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (intervalSobolevDensity (-α) α s x) * Real.exp ((σ - 2 * α) * x) * (1 + x ^ 2) ^ (-s / 2) ≤
      (1 + x ^ 2) ^ (-s / 4) := by
  have hw : intervalSobolevDensity (-α) α s x = Real.exp (2 * α * x) * (1 + x ^ 2) ^ (s / 2) := by
    unfold intervalSobolevDensity
    rw [max_eq_right (Real.exp_le_exp.mpr (by nlinarith))]
  have hsqrt : Real.sqrt (intervalSobolevDensity (-α) α s x) =
      Real.exp (α * x) * (1 + x ^ 2) ^ (s / 4) := by
    rw [hw, Real.sqrt_mul (Real.exp_pos _).le, show 2 * α * x = α * x + α * x by ring,
      Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le,
      Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + x ^ 2) (s / 2) (1 / 2)]
    congr 2; ring
  have hexp : Real.exp (α * x) * Real.exp ((σ - 2 * α) * x) ≤ 1 := by
    rw [← Real.exp_add]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hrpow : (1 + x ^ 2) ^ (s / 4) * (1 + x ^ 2) ^ (-s / 2) = (1 + x ^ 2) ^ (-s / 4) := by
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < 1 + x ^ 2)]
    congr 1; ring
  rw [hsqrt]
  calc Real.exp (α * x) * (1 + x ^ 2) ^ (s / 4) * Real.exp ((σ - 2 * α) * x) * (1 + x ^ 2) ^ (-s / 2)
      = (Real.exp (α * x) * Real.exp ((σ - 2 * α) * x)) * ((1 + x ^ 2) ^ (s / 4) * (1 + x ^ 2) ^ (-s / 2)) := by
        ring
    _ ≤ 1 * (1 + x ^ 2) ^ (-s / 4) := by
        rw [hrpow]
        exact mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = (1 + x ^ 2) ^ (-s / 4) := one_mul _

private lemma sharp_sqrt_exp_neg_le {α s σ : ℝ} (_hα : 0 ≤ α) (hσ : -α ≤ σ) {x : ℝ} (hx : x ≤ 0) :
    Real.sqrt (intervalSobolevDensity (-α) α s x) * Real.exp ((2 * α + σ) * x) * (1 + x ^ 2) ^ (-s / 2) ≤
      (1 + x ^ 2) ^ (-s / 4) := by
  have hw : intervalSobolevDensity (-α) α s x = Real.exp (-2 * α * x) * (1 + x ^ 2) ^ (s / 2) := by
    unfold intervalSobolevDensity
    rw [max_eq_left (Real.exp_le_exp.mpr (by nlinarith))]
    ring_nf
  have hsqrt : Real.sqrt (intervalSobolevDensity (-α) α s x) =
      Real.exp (-α * x) * (1 + x ^ 2) ^ (s / 4) := by
    rw [hw, Real.sqrt_mul (Real.exp_pos _).le, show -2 * α * x = (-α * x) + (-α * x) by ring,
      Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le,
      Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + x ^ 2) (s / 2) (1 / 2)]
    congr 2; ring
  have hexp : Real.exp (-α * x) * Real.exp ((2 * α + σ) * x) ≤ 1 := by
    rw [← Real.exp_add]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hrpow : (1 + x ^ 2) ^ (s / 4) * (1 + x ^ 2) ^ (-s / 2) = (1 + x ^ 2) ^ (-s / 4) := by
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < 1 + x ^ 2)]
    congr 1; ring
  rw [hsqrt]
  calc Real.exp (-α * x) * (1 + x ^ 2) ^ (s / 4) * Real.exp ((2 * α + σ) * x) * (1 + x ^ 2) ^ (-s / 2)
      = (Real.exp (-α * x) * Real.exp ((2 * α + σ) * x)) * ((1 + x ^ 2) ^ (s / 4) * (1 + x ^ 2) ^ (-s / 2)) := by
        ring
    _ ≤ 1 * (1 + x ^ 2) ^ (-s / 4) := by
        rw [hrpow]
        exact mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = (1 + x ^ 2) ^ (-s / 4) := one_mul _

lemma integrable_smooth_orbit_mul_poly_piece {w : ℝ → ℝ} (hw_cont : Continuous w) (hw_pos : ∀ x, 0 < w x)
    {s : ℝ} (hs : 1 < s) (u : Lp ℂ 2 (weightedSobolevMeasure F w))
    (ω : PontryaginDual (ideleClassNorm F).ker) (φ : BruhatCompactSupport C𝔽)
    {R : ℝ} (hR : 0 ≤ R) (hsupp : ∀ y ∈ tsupport φ.val, |logNorm y| ≤ R)
    {CR CR₁ : ℝ} (hCR : 0 < CR) (hCR₁ : 0 < CR₁)
    (hshift : ∀ x y : ℝ, |x - y| ≤ R → w x ≤ CR * w y)
    (hshift1 : ∀ x y : ℝ, |x - y| ≤ R + 1 → w x ≤ CR₁ * w y)
    {q : ℝ → ℝ} (hq_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) q)
    {S : Set ℝ} (hS : MeasurableSet S)
    (hq_dom : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S,
      Real.sqrt (w x) * |iteratedDeriv k q x| ≤ C * (1 + x ^ 2) ^ (-s / 4))
    (m : ℕ) :
    IntegrableOn (fun x : ℝ ↦
      iteratedDeriv m (fun t ↦ cornerOrbitProfile w ω φ u t * (q t : ℂ)) x) S volume := by
  let G : ℝ → ℂ := cornerOrbitProfile w ω φ u
  have hG_cd := cornerOrbitProfile_contDiff hw_cont hw_pos u ω φ hR hsupp hCR₁ hshift1
  have hG0_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) G := (hG_cd 0).1
  have hL2_h := memLp_localL2Energy hw_cont hw_pos u hR
  have hL2_r := memLp_two_one_add_sq_neg_quarter hs
  have hL1_hr : Integrable (fun x : ℝ ↦ localL2Energy w u R x * (1 + x ^ 2) ^ (-s / 4)) volume :=
    hL2_h.integrable_mul hL2_r
  have hqC_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t : ℝ ↦ (q t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hq_cd
  have hderiv_eq : (fun x : ℝ ↦ iteratedDeriv m (fun t ↦ G t * (q t : ℂ)) x) =
      fun x : ℝ ↦ ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℂ) * iteratedDeriv i G x * Complex.ofReal (iteratedDeriv (m - i) q x) := by
    funext x
    change iteratedDeriv m (G * fun t ↦ (q t : ℂ)) x = _
    rw [iteratedDeriv_mul (hG0_cd.contDiffAt.of_le (by exact mod_cast le_top))
      (hqC_cd.contDiffAt.of_le (by exact mod_cast le_top))]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [iteratedDeriv_ofReal hq_cd]
  rw [IntegrableOn, hderiv_eq]
  have hterm_int : ∀ i ∈ Finset.range (m + 1), Integrable
      (fun x : ℝ ↦ (m.choose i : ℂ) * iteratedDeriv i G x * Complex.ofReal (iteratedDeriv (m - i) q x))
      (volume.restrict S) := by
    intro i _
    obtain ⟨Ci, _hCi, hqi⟩ := hq_dom (m - i)
    have hGi_meas : Continuous (fun x : ℝ ↦ iteratedDeriv i G x) :=
      ((hG_cd i).1.continuous).congr fun x ↦ ((hG_cd i).2 x).symm
    have hterm_cont : Continuous (fun x : ℝ ↦
        (m.choose i : ℂ) * iteratedDeriv i G x * Complex.ofReal (iteratedDeriv (m - i) q x)) :=
      ((continuous_const.mul hGi_meas).mul
        (Complex.continuous_ofReal.comp (hq_cd.continuous_iteratedDeriv (m - i) (by simp))))
    let Mi : ℝ := ⨆ y : C𝔽, ‖(normFlowIterDeriv i φ).val y‖
    let K : ℝ := (m.choose i : ℝ) * (Mi * Real.sqrt (CR * tamagawaNormFactor F * (2 * R))) * Ci
    have hMi_nonneg : 0 ≤ Mi := Real.iSup_nonneg fun _ ↦ norm_nonneg _
    refine (hL1_hr.const_mul K).restrict.mono' hterm_cont.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem hS] with x hxS
    rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      (hG_cd i).2 x]
    have hGb := (cornerOrbitProfile_bound_and_integrable hw_cont hw_pos u ω (normFlowIterDeriv i φ) hR
      (fun y hy ↦ hsupp y (tsupport_normFlowIterDeriv_subset i φ hy)) hCR hshift x).2
    have hqbx := hqi x hxS
    calc (m.choose i : ℝ) * ‖cornerOrbitProfile w ω (normFlowIterDeriv i φ) u x‖ * |iteratedDeriv (m - i) q x|
        ≤ (m.choose i : ℝ) * (Mi * Real.sqrt (CR * tamagawaNormFactor F * (2 * R)) *
              Real.sqrt (w x) * localL2Energy w u R x) * |iteratedDeriv (m - i) q x| := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hGb (Nat.cast_nonneg _)) (abs_nonneg _)
      _ = (m.choose i : ℝ) * (Mi * Real.sqrt (CR * tamagawaNormFactor F * (2 * R))) *
            localL2Energy w u R x * (Real.sqrt (w x) * |iteratedDeriv (m - i) q x|) := by ring
      _ ≤ (m.choose i : ℝ) * (Mi * Real.sqrt (CR * tamagawaNormFactor F * (2 * R))) *
            localL2Energy w u R x * (Ci * (1 + x ^ 2) ^ (-s / 4)) := by
          exact mul_le_mul_of_nonneg_left hqbx (by
            refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hMi_nonneg (Real.sqrt_nonneg _))) ?_
            exact Real.sqrt_nonneg _)
      _ = K * (localL2Energy w u R x * (1 + x ^ 2) ^ (-s / 4)) := by dsimp only [K]; ring
  have hsum_int : ∀ t : Finset ℕ,
      (∀ i ∈ t, Integrable (fun x : ℝ ↦ (m.choose i : ℂ) * iteratedDeriv i G x *
        Complex.ofReal (iteratedDeriv (m - i) q x)) (volume.restrict S)) →
      Integrable (fun x : ℝ ↦ ∑ i ∈ t, (m.choose i : ℂ) * iteratedDeriv i G x *
        Complex.ofReal (iteratedDeriv (m - i) q x)) (volume.restrict S) := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro hs_all
      have ha_int := hs_all a (Finset.mem_insert_self a s)
      have hs_int := ih fun i hi ↦ hs_all i (Finset.mem_insert_of_mem hi)
      refine (ha_int.add hs_int).congr (ae_of_all _ fun x ↦ ?_)
      simp [Finset.sum_insert ha]
  exact hsum_int (Finset.range (m + 1)) hterm_int

private lemma exp_rpow_piece_dom {w : ℝ → ℝ} {s c : ℝ} {S : Set ℝ}
    (hdom_base : ∀ x ∈ S, Real.sqrt (w x) * Real.exp (c * x) * (1 + x ^ 2) ^ (-s / 2) ≤ (1 + x ^ 2) ^ (-s / 4))
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S,
      Real.sqrt (w x) * |iteratedDeriv k (fun t : ℝ ↦ Real.exp (c * t) * (1 + t ^ 2) ^ (-s / 2)) x| ≤
        C * (1 + x ^ 2) ^ (-s / 4) := by
  have hrpow_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t : ℝ ↦ (1 + t ^ 2) ^ (-s / 2)) :=
    (contDiff_const.add (contDiff_id.pow 2)).rpow_const_of_ne fun x ↦ by positivity
  have hexp_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t : ℝ ↦ Real.exp (c * t)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  choose Ck hCk0 hCk using fun i ↦ iteratedDeriv_one_add_sq_rpow_le s (k - i)
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * |c| ^ i * Ck i,
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (abs_nonneg _) _)) (hCk0 i),
    fun x hxS ↦ ?_⟩
  have hmul_id : iteratedDeriv k (fun t : ℝ ↦ Real.exp (c * t) * (1 + t ^ 2) ^ (-s / 2)) x =
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (c ^ i * Real.exp (c * x)) *
        iteratedDeriv (k - i) (fun t : ℝ ↦ (1 + t ^ 2) ^ (-s / 2)) x := by
    change iteratedDeriv k ((fun t ↦ Real.exp (c * t)) * fun t ↦ (1 + t ^ 2) ^ (-s / 2)) x = _
    rw [iteratedDeriv_mul (hexp_cd.contDiffAt.of_le (by exact mod_cast le_top))
      (hrpow_cd.contDiffAt.of_le (by exact mod_cast le_top))]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [congrFun (iteratedDeriv_exp_const_mul i c) x]
  rw [hmul_id]
  have habs_le : |∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (c ^ i * Real.exp (c * x)) *
        iteratedDeriv (k - i) (fun t : ℝ ↦ (1 + t ^ 2) ^ (-s / 2)) x| ≤
      (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * |c| ^ i * Ck i) *
        (Real.exp (c * x) * (1 + x ^ 2) ^ (-s / 2)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _), abs_of_nonneg (Nat.cast_nonneg _)]
    calc (k.choose i : ℝ) * (|c| ^ i * Real.exp (c * x)) *
          |iteratedDeriv (k - i) (fun t : ℝ ↦ (1 + t ^ 2) ^ (-s / 2)) x|
        ≤ (k.choose i : ℝ) * (|c| ^ i * Real.exp (c * x)) * (Ck i * (1 + x ^ 2) ^ (-s / 2)) :=
          mul_le_mul_of_nonneg_left (hCk i x) (by positivity)
      _ = (k.choose i : ℝ) * |c| ^ i * Ck i * (Real.exp (c * x) * (1 + x ^ 2) ^ (-s / 2)) := by ring
  calc Real.sqrt (w x) * |∑ i ∈ Finset.range (k + 1), _|
      ≤ Real.sqrt (w x) * ((∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * |c| ^ i * Ck i) *
          (Real.exp (c * x) * (1 + x ^ 2) ^ (-s / 2))) :=
        mul_le_mul_of_nonneg_left habs_le (Real.sqrt_nonneg _)
    _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * |c| ^ i * Ck i) *
          (Real.sqrt (w x) * Real.exp (c * x) * (1 + x ^ 2) ^ (-s / 2)) := by ring
    _ ≤ (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * |c| ^ i * Ck i) * (1 + x ^ 2) ^ (-s / 4) :=
        mul_le_mul_of_nonneg_left (hdom_base x hxS)
          (Finset.sum_nonneg fun i _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (abs_nonneg _) _)) (hCk0 i))

/-- Corner asymptotic formula for `⟪A(φ) r_{σ, T}, u⟫` on `W(α, s)`:
`⟪A(φ) r_{σ, T}, u⟫ = tamagawaNormFactor F * (4 * α) * G(0) / (T + τ)^2 + O(1 / |T + τ|^3)`. -/
theorem spectralStrip_riesz_convolution_inner_asymptotic (_a : ℝ) {α s σ : ℝ}
    (hα : 0 < α) (hs : 1 < s) (hσ : σ ∈ Icc (-α) α)
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    (ω : PontryaginDual (ideleClassNorm F).ker) (τ : ℝ)
    (hτ : ∀ x : ℝ, (χ ω (canonicalNormFlow F (Multiplicative.ofAdd x)) : ℂ) =
      Complex.exp (Complex.I * (τ : ℂ) * (x : ℂ)))
    (φ : BruhatCompactSupport C𝔽) (u : W(α, s)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, T + τ ≠ 0 →
      ‖@inner ℂ W(α, s) _
          (hardySobolevTestAction μ𝔽 m𝔽 (-α) α s ((neg_nonpos.mpr hα.le).trans hα.le)
            (zero_le_one.trans hs.le) φ (rieszZeroJet hα.le hs hσ (χ ω) T)) u -
          (tamagawaNormFactor F : ℂ) * ((4 * α : ℝ) : ℂ) *
            cornerOrbitProfile (intervalSobolevDensity (-α) α s) ω φ
              (intervalToWeightedEquiv (-α) α s u) 0 /
            ((T + τ : ℝ) : ℂ) ^ 2‖ ≤ C / |T + τ| ^ 3 := by
  let w := intervalSobolevDensity (-α) α s
  have hw_cont := continuous_intervalSobolevDensity (-α) α s
  have hw_pos := intervalSobolevDensity_pos (-α) α s
  obtain ⟨R, hR, hsupp⟩ := exists_logNorm_bound_tsupport (F := F) φ
  obtain ⟨CR, hCR, hshift⟩ := intervalSobolevDensity_shift_bound (α := α) (s := s) hα.le
    (zero_le_one.trans hs.le) hR
  obtain ⟨CR₁, hCR₁, hshift1⟩ := intervalSobolevDensity_shift_bound (α := α) (s := s) hα.le
    (zero_le_one.trans hs.le) (by linarith : 0 ≤ R + 1)
  let E := intervalToWeightedEquiv (F := F) (-α) α s
  let A_sh : W(α, s) →L[ℂ] W(α, s) :=
    hardySobolevTestAction μ𝔽 m𝔽 (-α) α s ((neg_nonpos.mpr hα.le).trans hα.le)
      (zero_le_one.trans hs.le) φ
  let A : Lp ℂ 2 (weightedSobolevMeasure F w) →L[ℂ] Lp ℂ 2 (weightedSobolevMeasure F w) :=
    E.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (A_sh.comp E.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have hA : ∀ v : Lp ℂ 2 (weightedSobolevMeasure F w), (A v : C𝔽 → ℂ) =ᵐ[μ𝔽] lcaConvolution μ𝔽 φ.val v := by
    intro v
    have h1 := intervalToWeightedEquiv_ae (F := F) (A_sh (E.symm v))
    have h2 := hardySobolevTestAction_apply μ𝔽 m𝔽 (-α) α s ((neg_nonpos.mpr hα.le).trans hα.le)
      (zero_le_one.trans hs.le) φ (E.symm v)
    have h3 := intervalToWeightedEquiv_symm_ae (F := F) v
    have hconv : lcaConvolution μ𝔽 φ.val (E.symm v) =ᵐ[μ𝔽] lcaConvolution μ𝔽 φ.val v := by
      refine ae_of_all _ fun g ↦ integral_congr_ae ?_
      have h_isHaar : (μ𝔽).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
      let mp : MeasurePreserving (fun y : C𝔽 ↦ y⁻¹ * g) μ𝔽 μ𝔽 :=
        (measurePreserving_mul_right μ𝔽 g).comp (Measure.measurePreserving_inv μ𝔽)
      filter_upwards [mp.quasiMeasurePreserving.ae h3] with y hy
      rw [hy]
    exact h1.trans (h2.trans hconv)
  let uW := E u
  let G : ℝ → ℂ := cornerOrbitProfile w ω φ uW
  let cp : ℝ := σ - 2 * α
  let cm : ℝ := 2 * α + σ
  let gp : ℝ → ℝ := fun t ↦ Real.exp (cp * t) * (1 + t ^ 2) ^ (-s / 2)
  let gm : ℝ → ℝ := fun t ↦ Real.exp (cm * t) * (1 + t ^ 2) ^ (-s / 2)
  have hrpow_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t : ℝ ↦ (1 + t ^ 2) ^ (-s / 2)) :=
    (contDiff_const.add (contDiff_id.pow 2)).rpow_const_of_ne fun x ↦ by positivity
  have hgp_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) gp :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul hrpow_cd
  have hgm_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) gm :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul hrpow_cd
  have hG_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) G :=
    (cornerOrbitProfile_contDiff hw_cont hw_pos uW ω φ hR hsupp hCR₁ hshift1 0).1
  let H : ℝ → ℂ := fun t ↦ G t * ((Real.exp (σ * t) / w t : ℝ) : ℂ)
  let Hp : ℝ → ℂ := fun t ↦ G t * (gp t : ℂ)
  let Hm : ℝ → ℂ := fun t ↦ G t * (gm t : ℂ)
  have hHp_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) Hp := hG_cd.mul (Complex.ofRealCLM.contDiff.comp hgp_cd)
  have hHm_cd : ContDiff ℝ (↑(⊤ : ℕ∞)) Hm := hG_cd.mul (Complex.ofRealCLM.contDiff.comp hgm_cd)
  let Hp1 := iteratedDeriv 1 Hp
  let Hp2 := iteratedDeriv 2 Hp
  let Hp3 := iteratedDeriv 3 Hp
  let Hm1 := iteratedDeriv 1 Hm
  let Hm2 := iteratedDeriv 2 Hm
  let Hm3 := iteratedDeriv 3 Hm
  have hHp_eq : ∀ x ∈ Ici (0 : ℝ), Hp x = H x := by
    intro x (hx : 0 ≤ x)
    dsimp only [Hp, H, gp, w, intervalSobolevDensity]
    rw [max_eq_right (Real.exp_le_exp.mpr (by nlinarith))]
    congr 2
    rw [show (-s / 2 : ℝ) = -(s / 2) by ring, Real.rpow_neg (by positivity),
      div_mul_eq_div_mul_one_div, one_div,
      show cp * x = σ * x - 2 * α * x by dsimp only [cp]; ring, Real.exp_sub, div_eq_mul_inv]
  have hHm_eq : ∀ x ∈ Iic (0 : ℝ), Hm x = H x := by
    intro x (hx : x ≤ 0)
    dsimp only [Hm, H, gm, w, intervalSobolevDensity]
    rw [max_eq_left (Real.exp_le_exp.mpr (by nlinarith))]
    congr 2
    rw [show (-s / 2 : ℝ) = -(s / 2) by ring, Real.rpow_neg (by positivity),
      div_mul_eq_div_mul_one_div, one_div,
      show cm * x = σ * x - 2 * (-α) * x by dsimp only [cm]; ring, Real.exp_sub, div_eq_mul_inv]
  have hip (m : ℕ) : IntegrableOn (iteratedDeriv m Hp) (Ioi 0) :=
    (integrable_smooth_orbit_mul_poly_piece hw_cont hw_pos hs uW ω φ hR hsupp hCR hCR₁
      hshift hshift1 hgp_cd measurableSet_Ici
      (exp_rpow_piece_dom (fun _ hx ↦ sharp_sqrt_exp_pos_le hα.le hσ.2 hx)) m).mono_set Ioi_subset_Ici_self
  have him (m : ℕ) : IntegrableOn (iteratedDeriv m Hm) (Iio 0) :=
    (integrable_smooth_orbit_mul_poly_piece hw_cont hw_pos hs uW ω φ hR hsupp hCR hCR₁
      hshift hshift1 hgm_cd measurableSet_Iic
      (exp_rpow_piece_dom (fun _ hx ↦ sharp_sqrt_exp_neg_le hα.le hσ.1 hx)) m).mono_set Iio_subset_Iic_self
  have hdiff_p (m : ℕ) (x : ℝ) : HasDerivAt (iteratedDeriv m Hp) (iteratedDeriv (m + 1) Hp x) x := by
    rw [iteratedDeriv_succ]
    exact (hHp_cd.differentiable_iteratedDeriv m (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top m)) x).hasDerivAt
  have hdiff_m (m : ℕ) (x : ℝ) : HasDerivAt (iteratedDeriv m Hm) (iteratedDeriv (m + 1) Hm x) x := by
    rw [iteratedDeriv_succ]
    exact (hHm_cd.differentiable_iteratedDeriv m (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top m)) x).hasDerivAt
  have hjump : -(Hp1 0 - Hm1 0) = ((4 * α : ℝ) : ℂ) * G 0 := by
    have hgp0 : gp 0 = 1 := by simp [gp]
    have hgm0 : gm 0 = 1 := by simp [gm]
    have hrpow_0 : HasDerivAt (fun t : ℝ ↦ (1 + t ^ 2) ^ (-s / 2)) 0 0 := by
      have hbase : HasDerivAt (fun t : ℝ ↦ 1 + t ^ 2) 0 0 := by
        simpa using ((hasDerivAt_pow 2 (0 : ℝ)).const_add (1 : ℝ))
      simpa using (hbase.rpow_const (Or.inl (by positivity : (1 : ℝ) + 0 ^ 2 ≠ 0)))
    have hgp0' : HasDerivAt gp cp 0 := by
      have h1 : HasDerivAt (fun t : ℝ ↦ Real.exp (cp * t)) cp 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul cp).exp
      have hmul : HasDerivAt (fun t : ℝ ↦ Real.exp (cp * t) * (1 + t ^ 2) ^ (-s / 2))
          (cp * (1 + 0 ^ 2) ^ (-s / 2) + Real.exp (cp * 0) * 0) 0 := h1.mul hrpow_0
      simpa [gp] using hmul
    have hgm0' : HasDerivAt gm cm 0 := by
      have h1 : HasDerivAt (fun t : ℝ ↦ Real.exp (cm * t)) cm 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul cm).exp
      have hmul : HasDerivAt (fun t : ℝ ↦ Real.exp (cm * t) * (1 + t ^ 2) ^ (-s / 2))
          (cm * (1 + 0 ^ 2) ^ (-s / 2) + Real.exp (cm * 0) * 0) 0 := h1.mul hrpow_0
      simpa [gm] using hmul
    have hp1 : Hp1 0 = deriv G 0 * (gp 0 : ℂ) + G 0 * (cp : ℂ) := by
      have hd : HasDerivAt (fun t : ℝ ↦ G t * (gp t : ℂ))
          (deriv G 0 * (gp 0 : ℂ) + G 0 * (cp : ℂ)) 0 :=
        (hG_cd.differentiable (by simp) 0).hasDerivAt.mul
          (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hgp0')
      simpa [Hp1, iteratedDeriv_one, Hp] using hd.deriv
    have hm1 : Hm1 0 = deriv G 0 * (gm 0 : ℂ) + G 0 * (cm : ℂ) := by
      have hd : HasDerivAt (fun t : ℝ ↦ G t * (gm t : ℂ))
          (deriv G 0 * (gm 0 : ℂ) + G 0 * (cm : ℂ)) 0 :=
        (hG_cd.differentiable (by simp) 0).hasDerivAt.mul
          (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hgm0')
      simpa [Hm1, iteratedDeriv_one, Hm] using hd.deriv
    rw [hp1, hm1, hgp0, hgm0]
    dsimp only [cp, cm]
    push_cast
    ring
  have hG0_eq : G 0 = cornerOrbitProfile w ω φ uW 0 := rfl
  let C_rem : ℝ := tamagawaNormFactor F *
    (‖Hp2 0 - Hm2 0‖ + (∫ x in Ioi (0 : ℝ), ‖Hp3 x‖) + ∫ x in Iio (0 : ℝ), ‖Hm3 x‖)
  refine ⟨C_rem, mul_nonneg (tamagawaNormFactor_pos (F := F)).le
    (add_nonneg (add_nonneg (norm_nonneg _) (integral_nonneg fun _ ↦ norm_nonneg _))
      (integral_nonneg fun _ ↦ norm_nonneg _)), fun T hTτ ↦ ?_⟩
  have hη : -(T + τ) ≠ 0 := neg_ne_zero.mpr hTτ
  have hfibp := fourier_corner_three_ibp (H := H) (Hp := Hp) (Hm := Hm)
    (Hp1 := Hp1) (Hm1 := Hm1) (Hp2 := Hp2) (Hm2 := Hm2) (Hp3 := Hp3) (Hm3 := Hm3) hη
    hHp_eq hHm_eq (hHp_cd.continuous.continuousWithinAt) (hHm_cd.continuous.continuousWithinAt)
    ((hHp_cd.continuous_iteratedDeriv 1 (by simp)).continuousWithinAt)
    ((hHm_cd.continuous_iteratedDeriv 1 (by simp)).continuousWithinAt)
    ((hHp_cd.continuous_iteratedDeriv 2 (by simp)).continuousWithinAt)
    ((hHm_cd.continuous_iteratedDeriv 2 (by simp)).continuousWithinAt)
    (fun x _ ↦ hdiff_p 0 x) (fun x _ ↦ hdiff_m 0 x)
    (fun x _ ↦ hdiff_p 1 x) (fun x _ ↦ hdiff_m 1 x)
    (fun x _ ↦ hdiff_p 2 x) (fun x _ ↦ hdiff_m 2 x)
    (hip 0) (him 0) (hip 1) (him 1) (hip 2) (him 2) (hip 3) (him 3)
  have hfac := weightedRieszJet_convolution_inner_eq_fourier (F := F) hw_cont hw_pos hs
    (exp_div_intervalSobolevDensity_dom hα.le hσ) hR hCR hshift χ hχ ω τ hτ φ hsupp T A hA uW
  have hinner_eq : @inner ℂ W(α, s) _ (A_sh (rieszZeroJet hα.le hs hσ (χ ω) T)) u =
      @inner ℂ (Lp ℂ 2 (weightedSobolevMeasure F w)) _
        (A (weightedRieszJet hw_cont hw_pos hs (exp_div_intervalSobolevDensity_dom hα.le hσ) (χ ω) T)) uW := by
    rw [← E.inner_map_map]
    rfl
  change ‖@inner ℂ W(α, s) _ (A_sh (rieszZeroJet hα.le hs hσ (χ ω) T)) u -
      (tamagawaNormFactor F : ℂ) * ((4 * α : ℝ) : ℂ) *
        cornerOrbitProfile (intervalSobolevDensity (-α) α s) ω φ
          (intervalToWeightedEquiv (-α) α s u) 0 / ((T + τ : ℝ) : ℂ) ^ 2‖ ≤ _
  rw [hinner_eq, hfac]
  rw [hjump, hG0_eq,
    show ((-(T + τ) : ℝ) : ℂ) ^ 2 = ((T + τ : ℝ) : ℂ) ^ 2 by push_cast; ring] at hfibp
  have hm := mul_le_mul_of_nonneg_left hfibp (tamagawaNormFactor_pos (F := F)).le
  rw [← Real.norm_of_nonneg (tamagawaNormFactor_pos (F := F)).le, ← Complex.norm_real, ← norm_mul,
    mul_sub, ← mul_div_assoc, ← mul_assoc (tamagawaNormFactor F : ℂ) ((4 * α : ℝ) : ℂ),
    Complex.norm_real, Real.norm_of_nonneg (tamagawaNormFactor_pos (F := F)).le,
    show |-(T + τ)| ^ 3 = |T + τ| ^ 3 by rw [abs_neg]] at hm
  exact hm.trans_eq (by dsimp only [C_rem]; ring)

/-- Normalized operator lower bound on the geometric commutator `G_a ∘ A(φ) ∘ P_a`:
when `u ∈ Θ₀` has nonzero corner pairing and `r_{σ, T} ∈ Θ₀ᗮ` is a depth-zero Riesz jet,
`‖(G_a ∘ A(φ) ∘ P_a)(r_{σ, T} / ‖r_{σ, T}‖)‖ ≥ c / (T + τ)^2` for `|T + τ| ≥ M`. -/
theorem spectralStrip_geometricCommutator_riesz_lower_bound (a : ℝ) {α s σ : ℝ}
    (hα : 0 < α) (hs : 1 < s) (hσ : σ ∈ Icc (-α) α)
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    (ω : PontryaginDual (ideleClassNorm F).ker) (τ : ℝ)
    (hτ : ∀ x : ℝ, (χ ω (canonicalNormFlow F (Multiplicative.ofAdd x)) : ℂ) =
      Complex.exp (Complex.I * (τ : ℂ) * (x : ℂ)))
    (φ : BruhatCompactSupport C𝔽) (u : W(α, s))
    (hu_mem : u ∈ globalThetaSobolev F a ((neg_nonpos.mpr hα.le).trans hα.le) (zero_le_one.trans hs.le))
    (hcorner : cornerOrbitProfile (intervalSobolevDensity (-α) α s) ω φ
      (intervalToWeightedEquiv (-α) α s u) 0 ≠ 0) :
    ∃ M : ℝ, 0 < M ∧ ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, M ≤ |T + τ| →
      (∀ _ : rieszZeroJet (F := F) hα.le hs hσ (χ ω) T ∈
        (globalThetaSobolev F a ((neg_nonpos.mpr hα.le).trans hα.le) (zero_le_one.trans hs.le)).orthogonal,
        c / (T + τ) ^ 2 ≤
          ‖((geometricProjection (F := F) a hα.le (zero_le_one.trans hs.le)).comp
              ((hardySobolevTestAction μ𝔽 m𝔽 (-α) α s ((neg_nonpos.mpr hα.le).trans hα.le)
                (zero_le_one.trans hs.le) φ).comp
              (spectralProjection (F := F) a hα.le (zero_le_one.trans hs.le))))
            ((‖rieszZeroJet (F := F) hα.le hs hσ (χ ω) T‖⁻¹ : ℂ) •
              rieszZeroJet (F := F) hα.le hs hσ (χ ω) T)‖) := by
  let hI : -α ≤ α := (neg_nonpos.mpr hα.le).trans hα.le
  let hs₀ : 0 ≤ s := zero_le_one.trans hs.le
  let Θ₀ := globalThetaSobolev F a hI hs₀
  let G_a : W(α, s) →L[ℂ] W(α, s) := geometricProjection (F := F) a hα.le hs₀
  let P_a : W(α, s) →L[ℂ] W(α, s) := spectralProjection (F := F) a hα.le hs₀
  let A_φ : W(α, s) →L[ℂ] W(α, s) := hardySobolevTestAction μ𝔽 m𝔽 (-α) α s hI hs₀ φ
  obtain ⟨C, _hC0, hC⟩ := spectralStrip_riesz_convolution_inner_asymptotic a hα hs hσ χ hχ ω τ hτ φ u
  let lead : ℝ := tamagawaNormFactor F * (4 * α) *
    ‖cornerOrbitProfile (intervalSobolevDensity (-α) α s) ω φ
      (intervalToWeightedEquiv (-α) α s u) 0‖
  have hlead_pos : 0 < lead :=
    mul_pos (mul_pos (tamagawaNormFactor_pos (F := F)) (by linarith)) (norm_pos_iff.mpr hcorner)
  have hu_pos : 0 < ‖u‖ := by
    refine norm_pos_iff.mpr fun hu0 ↦ hcorner ?_
    rw [hu0, map_zero]
    simp only [cornerOrbitProfile]
    have habs := tamagawa_absCont_weightedSobolevMeasure (F := F)
      (continuous_intervalSobolevDensity (-α) α s) (intervalSobolevDensity_pos (-α) α s)
    refine integral_eq_zero_of_ae ?_
    filter_upwards [(Measure.quasiMeasurePreserving_snd.ae (habs.ae_le (Lp.coeFn_zero ℂ 2 _)))] with p hp
    rw [hp]
    simp
  let nr0 : ℝ := Real.sqrt (tamagawaNormFactor F *
    ∫ x : ℝ, Real.exp (2 * σ * x) / intervalSobolevDensity (-α) α s x)
  have hnr0_pos : 0 < nr0 := Real.sqrt_pos.mpr <| by
    have hns := rieszZeroJet_norm_sq (F := F) hα.le hs hσ (χ ω) 0
    rw [hns.2] at hns
    exact hns.1
  let M : ℝ := max 1 (2 * C / lead)
  refine ⟨M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), (lead / 2) / (nr0 * ‖u‖), by positivity,
    fun T hT horth ↦ ?_⟩
  have hTτ0 : T + τ ≠ 0 := by
    intro h0
    have h1 : (1 : ℝ) ≤ |T + τ| := (le_max_left _ _).trans hT
    rw [h0, abs_zero] at h1
    linarith
  have hasymp : ‖@inner ℂ W(α, s) _ (A_φ (rieszZeroJet hα.le hs hσ (χ ω) T)) u -
      (tamagawaNormFactor F : ℂ) * ((4 * α : ℝ) : ℂ) *
        cornerOrbitProfile (intervalSobolevDensity (-α) α s) ω φ
          (intervalToWeightedEquiv (-α) α s u) 0 / ((T + τ : ℝ) : ℂ) ^ 2‖ ≤ C / |T + τ| ^ 3 :=
    hC T hTτ0
  have hlead_norm :
      ‖(tamagawaNormFactor F : ℂ) * ((4 * α : ℝ) : ℂ) *
          cornerOrbitProfile (intervalSobolevDensity (-α) α s) ω φ
            (intervalToWeightedEquiv (-α) α s u) 0 /
          ((T + τ : ℝ) : ℂ) ^ 2‖ = lead / (T + τ) ^ 2 := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg (tamagawaNormFactor_pos (F := F)).le,
      Real.norm_of_nonneg (by positivity : 0 ≤ 4 * α), Real.norm_eq_abs, sq_abs]
  have hrem_le : C / |T + τ| ^ 3 ≤ (lead / 2) / (T + τ) ^ 2 := by
    have hM2 : 2 * C / lead ≤ |T + τ| := (le_max_right _ _).trans hT
    have hC_le : C ≤ (lead / 2) * |T + τ| := by
      rw [div_le_iff₀ hlead_pos] at hM2
      linarith
    calc C / |T + τ| ^ 3
        ≤ ((lead / 2) * |T + τ|) / |T + τ| ^ 3 :=
          div_le_div_of_nonneg_right hC_le (pow_nonneg (abs_nonneg _) 3)
      _ = (lead / 2) / |T + τ| ^ 2 := by
          have habs0 : |T + τ| ≠ 0 := abs_ne_zero.mpr hTτ0
          field_simp [habs0]
      _ = (lead / 2) / (T + τ) ^ 2 := by rw [sq_abs]
  have hlow_inner : lead / (T + τ) ^ 2 - (lead / 2) / (T + τ) ^ 2 ≤
      ‖@inner ℂ W(α, s) _ (A_φ (rieszZeroJet hα.le hs hσ (χ ω) T)) u‖ := by
    have hrev := norm_sub_rev
      (@inner ℂ W(α, s) _ (A_φ (rieszZeroJet hα.le hs hσ (χ ω) T)) u)
      ((tamagawaNormFactor F : ℂ) * ((4 * α : ℝ) : ℂ) *
          cornerOrbitProfile (intervalSobolevDensity (-α) α s) ω φ
            (intervalToWeightedEquiv (-α) α s u) 0 / ((T + τ : ℝ) : ℂ) ^ 2)
    have hsub := norm_sub_norm_le
      ((tamagawaNormFactor F : ℂ) * ((4 * α : ℝ) : ℂ) *
          cornerOrbitProfile (intervalSobolevDensity (-α) α s) ω φ
            (intervalToWeightedEquiv (-α) α s u) 0 / ((T + τ : ℝ) : ℂ) ^ 2)
      (@inner ℂ W(α, s) _ (A_φ (rieszZeroJet hα.le hs hσ (χ ω) T)) u)
    rw [hlead_norm, ← hrev] at hsub
    linarith [hasymp, hrem_le, hsub]
  have hproj_r : P_a (rieszZeroJet hα.le hs hσ (χ ω) T) = rieszZeroJet hα.le hs hσ (χ ω) T :=
    Submodule.starProjection_eq_self_iff.mpr horth
  have hproj_u : G_a u = u := Submodule.starProjection_eq_self_iff.mpr hu_mem
  have hsa_G : IsSelfAdjoint G_a := isSelfAdjoint_starProjection Θ₀
  have hinner_comm : @inner ℂ W(α, s) _ (G_a (A_φ (P_a (rieszZeroJet hα.le hs hσ (χ ω) T)))) u =
      @inner ℂ W(α, s) _ (A_φ (rieszZeroJet hα.le hs hσ (χ ω) T)) u := by
    rw [hproj_r]
    calc @inner ℂ W(α, s) _ (G_a (A_φ (rieszZeroJet hα.le hs hσ (χ ω) T))) u
        = @inner ℂ W(α, s) _ (A_φ (rieszZeroJet hα.le hs hσ (χ ω) T)) (G_a.adjoint u) :=
          (ContinuousLinearMap.adjoint_inner_right G_a _ u).symm
      _ = @inner ℂ W(α, s) _ (A_φ (rieszZeroJet hα.le hs hσ (χ ω) T)) u := by
          rw [hsa_G.adjoint_eq, hproj_u]
  have hnr_T : ‖rieszZeroJet (F := F) hα.le hs hσ (χ ω) T‖ = nr0 := by
    have hsq := (rieszZeroJet_norm_sq (F := F) hα.le hs hσ (χ ω) T).2
    rw [← Real.sqrt_sq (norm_nonneg _), hsq]
  have hcs : ‖@inner ℂ W(α, s) _ (A_φ (rieszZeroJet hα.le hs hσ (χ ω) T)) u‖ ≤
      nr0 * ‖(G_a.comp (A_φ.comp P_a))
        ((‖rieszZeroJet (F := F) hα.le hs hσ (χ ω) T‖⁻¹ : ℂ) •
          rieszZeroJet (F := F) hα.le hs hσ (χ ω) T)‖ * ‖u‖ := by
    rw [← hinner_comm]
    have hlin : G_a (A_φ (P_a (rieszZeroJet hα.le hs hσ (χ ω) T))) =
        (nr0 : ℂ) • (G_a.comp (A_φ.comp P_a))
          ((‖rieszZeroJet (F := F) hα.le hs hσ (χ ω) T‖⁻¹ : ℂ) •
            rieszZeroJet (F := F) hα.le hs hσ (χ ω) T) := by
      simp only [ContinuousLinearMap.comp_apply, map_smul, smul_smul, hnr_T]
      have hn0 : (nr0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnr0_pos.ne'
      rw [mul_inv_cancel₀ hn0, one_smul]
    rw [hlin, inner_smul_left, Complex.conj_ofReal, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hnr0_pos.le, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ u) hnr0_pos.le
  have hlow2 : (lead / 2) / (T + τ) ^ 2 ≤
      (nr0 * ‖u‖) * ‖(G_a.comp (A_φ.comp P_a))
        ((‖rieszZeroJet (F := F) hα.le hs hσ (χ ω) T‖⁻¹ : ℂ) •
          rieszZeroJet (F := F) hα.le hs hσ (χ ω) T)‖ := by
    calc (lead / 2) / (T + τ) ^ 2
        = lead / (T + τ) ^ 2 - (lead / 2) / (T + τ) ^ 2 := by ring
      _ ≤ ‖@inner ℂ W(α, s) _ (A_φ (rieszZeroJet hα.le hs hσ (χ ω) T)) u‖ := hlow_inner
      _ ≤ nr0 * ‖(G_a.comp (A_φ.comp P_a)) _‖ * ‖u‖ := hcs
      _ = (nr0 * ‖u‖) * ‖(G_a.comp (A_φ.comp P_a)) _‖ := by ring
  change (lead / 2) / (nr0 * ‖u‖) / (T + τ) ^ 2 ≤
      ‖(G_a.comp (A_φ.comp P_a))
        ((‖rieszZeroJet (F := F) hα.le hs hσ (χ ω) T‖⁻¹ : ℂ) •
          rieszZeroJet (F := F) hα.le hs hσ (χ ω) T)‖
  rw [div_div, mul_comm (nr0 * ‖u‖) ((T + τ) ^ 2), ← div_div]
  exact (div_le_iff₀' (mul_pos hnr0_pos hu_pos)).mpr hlow2

end RieszAndCornerLowerBound

end RiemannMasullo.Isolated
