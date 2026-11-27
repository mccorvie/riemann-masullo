module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_RationalCylinder
public import RiemannMasullo.Ch12_TraceGeometric.Sec3_ConductorLimits
import Mathlib.Tactic

/-! # Physical divisor sums on rational congruence cylinders

For the rational field, the actual Mellin samples on all positive sites of the
completed idelic divisor recover an individual prime-power atom as the conductor grows.
The named analytic inputs are Montgomery’s one-modulus estimate and the classical
primitive Dirichlet explicit formula for compactly supported positive-log profiles.
-/

@[expose] public noncomputable section

open NumberFieldKB.Chebotarev.RatIdele NumberField
open Filter Function MeasureTheory Set
open scoped ComplexConjugate ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.ConductorCylinder

open ConductorDensity RationalConductor

set_option quotPrecheck false

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "V" => ((normOneIdeleClassTamagawaMeasure ℚ).real univ : ℂ)
local notation "mℚ" => (continuousIdeleClassNorm ℚ : Cℚ →ₜ* ℝ≥0ˣ)
local notation "hmℚ" => (⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩ : IsModulation mℚ)
local notation "μℚ" => ideleClassTamagawaMeasure ℚ
local notation "logN(" g ")" => Real.log ((ideleClassNorm ℚ g : ℝ≥0) : ℝ)
local notation "Strip" => {z : ℂ // 0 < z.re ∧ z.re < 1}

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

/-- The actual finite-order idelic character realizing the primitive row under a level character. -/
def packetRow {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : PontryaginDual Cℚ :=
  (exists_primitive_row q χ).choose

theorem packetRow_isOfFinOrder {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    IsOfFinOrder (packetRow χ) :=
  (exists_primitive_row q χ).choose_spec.1

theorem packetRow_value {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : Cℚ) :
    (packetRow χ x : ℂ) = ((ratDirichletChar q χ x : ℂˣ) : ℂ) :=
  (exists_primitive_row q χ).choose_spec.2.1 x

/-- The idelic divisor equals the completed primitive Dirichlet multiplicity on the open strip. -/
theorem packetRow_divisor_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : Strip) :
    (MeromorphicOn.divisor (continuedCompletedHeckeL (packetRow χ)) univ z.val).toNat =
      completedPrimitiveOrder (χ, z) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec (packetRow χ)).1.meromorphicOn
    (mem_univ _)]
  exact congrArg (fun o : WithTop ℤ ↦ o.untop₀.toNat)
    (((exists_primitive_row q χ).choose_spec.2.2.2.1 z.val z.property.1).trans
      (ConductorDensity.order_completion χ.primitiveCharacter z.property.1))

/-- All positive divisor sites of the completed idelic row, without an imposed strip. -/
def rowZeroSites (ψ : PontryaginDual Cℚ) : Set ℂ :=
  {z | 0 < MeromorphicOn.divisor (continuedCompletedHeckeL ψ) univ z}

private theorem row_site_in_strip (ψ : PontryaginDual Cℚ) (z : rowZeroSites ψ) :
    z.val.re ∈ Ioo (0 : ℝ) 1 := by
  have hlt (χ : PontryaginDual Cℚ) (w : ℂ) (hw : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) w) :
      w.re < 1 := by
    rcases le_or_gt w.re 0 with h | h
    · exact h.trans_lt zero_lt_one
    · obtain ⟨hm, he⟩ := continuedCompletedHeckeL_spec χ
      exact completedHeckeL_continuation_zeros χ _ hm he h hw
  obtain ⟨hL, he⟩ := continuedCompletedHeckeL_spec ψ
  obtain ⟨hD, hd⟩ := continuedCompletedHeckeL_spec ψ⁻¹
  have h := z.property
  change 0 < MeromorphicOn.divisor _ univ z.val at h
  rw [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _)] at h
  have hp : 0 < meromorphicOrderAt (continuedCompletedHeckeL ψ) z.val := by
    cases ho : meromorphicOrderAt (continuedCompletedHeckeL ψ) z.val with
    | top => simp
    | coe n => rw [ho, WithTop.untop₀_coe] at h; exact_mod_cast h
  obtain ⟨ε, hε, hn, hfe⟩ :=
    completedHeckeL_continuation_functionalEquation ψ _ _ hL he hD hd
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL ψ⁻¹)
    (show AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) z.val by fun_prop)
    (show deriv (fun s : ℂ ↦ 1 - s) z.val ≠ 0 by simp)
  rw [show continuedCompletedHeckeL ψ⁻¹ ∘ (fun s : ℂ ↦ 1 - s) =
      ε * continuedCompletedHeckeL ψ from funext hfe,
    meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt z.val) (hn z.val)] at hcomp
  have hl := hlt ψ⁻¹ (1 - z.val) (hcomp ▸ hp)
  rw [Complex.sub_re, Complex.one_re] at hl
  exact ⟨by linarith, hlt ψ z.val hp⟩

/-- The genuine Mellin functional of one test is evaluated on all distinct positive
divisor sites of each idelic row. The third argument of the weight is its zero order. -/
def physicalWidthSum (q : ℕ) [NeZero q] (φ : BruhatCompactSupport Cℚ) (a : ℝ)
    (W : DirichletCharacter ℂ q → ℂ → ℕ → ℂ) : ℂ :=
  ∑ χ : DirichletCharacter ℂ q, ∑' ρ : rowZeroSites (packetRow χ),
    W χ ρ.val (MeromorphicOn.divisor (continuedCompletedHeckeL (packetRow χ)) univ ρ.val).toNat *
      modulatedFourierMellin mℚ univ hmℚ μℚ φ.val (ideleClassNormTwist (packetRow χ) (ρ.val - a))

/-- Pointwise normalization of a single congruence cylinder on the rational idele class group. -/
def IsNormalizedCylinder (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (H : ℝ → ℂ)
    (φ : BruhatCompactSupport Cℚ) : Prop :=
  ∀ x : Cℚ, φ.val x = if classResidue q x = r then V⁻¹ * H logN(x) else 0

/-- The Mellin coefficient of one physical cylinder times the local prime-power
coefficient, summed over the actual idelic rows. This also covers primes dividing the level. -/
theorem cylinder_mellin_localPrimeValue_pow (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (H : ℝ → ℂ)
    (hH : Continuous H) (φ : BruhatCompactSupport Cℚ) (hφ : IsNormalizedCylinder q r H φ)
    (v : Pl) (z : ℂ) {e m k : ℕ} (hk : k ≠ 0) (hq : q = pr v ^ e * m) (hpm : ¬ pr v ∣ m) :
    (∑ χ : DirichletCharacter ℂ q,
      modulatedFourierMellin mℚ univ hmℚ μℚ φ.val (ideleClassNormTwist (packetRow χ) z) *
        localPrimeValue (packetRow χ) v ^ k) =
      bilateralLaplace H z * (if (ZMod.cast (r : ZMod q) : ZMod m) = (pr v ^ k : ℕ)
        then ((pr v ^ e).totient : ℂ)⁻¹ else 0) := by
  rw [← cylinderAverage_localPrimeValue_pow q r packetRow packetRow_value v hk hq hpm]
  change _ = bilateralLaplace H z * ((∑ χ, conj (χ r.val) * localPrimeValue (packetRow χ) v ^ k) / q.totient)
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun χ _ ↦ ?_
  rw [normalized_cylinder_mellin q r H hH φ hφ χ _ (packetRow_value χ)]
  ring

/-- A physical test with its specified cylinder indicator and radial profile. -/
def selectedCylinder (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (H : ℝ → ℂ)
    (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) : BruhatCompactSupport Cℚ :=
  (exists_normalized_cylinder_test q r H hH hc).choose

theorem selectedCylinder_spec (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (H : ℝ → ℂ)
    (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) :
    IsNormalizedCylinder q r H (selectedCylinder q r H hH hc) :=
  (exists_normalized_cylinder_test q r H hH hc).choose_spec

/-- Zero-order points may be inserted into each unordered sum for any weight vanishing
at order zero. The coefficient and its normalization come from the Mellin integral. -/
theorem physicalWidthSum_eq (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (H : ℝ → ℂ)
    (hH : Continuous H) (φ : BruhatCompactSupport Cℚ) (hφ : IsNormalizedCylinder q r H φ)
    (a : ℝ) (W : DirichletCharacter ℂ q → ℂ → ℕ → ℂ) (hW : ∀ χ z, W χ z 0 = 0) :
    physicalWidthSum q φ a W = cylinderAverage q r (fun χ ↦ ∑' z : Strip,
      W χ z.val (completedPrimitiveOrder (χ, z)) * bilateralLaplace H (z.val - a)) := by
  classical
  let f (χ : DirichletCharacter ℂ q) (z : Strip) :=
    W χ z.val (completedPrimitiveOrder (χ, z)) * bilateralLaplace H (z.val - a)
  change (∑ χ : DirichletCharacter ℂ q, _) =
    (∑ χ : DirichletCharacter ℂ q, conj (χ r.val) * ∑' z, f χ z) / (q.totient : ℂ)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun χ _ ↦ ?_
  let e (ρ : rowZeroSites (packetRow χ)) : Strip := ⟨ρ.val, row_site_in_strip _ ρ⟩
  have hi : Injective e := fun _ _ he ↦ Subtype.ext (congrArg (fun z : Strip ↦ z.val) he)
  have hcover : Function.support (f χ) ⊆ range e := by
    intro z hz
    have ho : 0 < completedPrimitiveOrder (χ, z) := Nat.pos_of_ne_zero fun h0 ↦
      hz (by simp [f, h0, hW])
    have hn : 0 < (MeromorphicOn.divisor (continuedCompletedHeckeL (packetRow χ)) univ z.val).toNat := by
      rwa [packetRow_divisor_eq]
    exact ⟨⟨z.val, Int.pos_iff_toNat_pos.mpr hn⟩, Subtype.ext rfl⟩
  let c := conj (χ r.val) / (q.totient : ℂ)
  calc
    _ = ∑' ρ : rowZeroSites (packetRow χ), c * f χ (e ρ) := by
      apply tsum_congr
      intro ρ
      rw [normalized_cylinder_mellin q r H hH φ hφ χ _ (packetRow_value χ)]
      change W χ ρ.val _ * (c * bilateralLaplace H (ρ.val - a)) =
        c * (W χ ρ.val (completedPrimitiveOrder (χ, e ρ)) * bilateralLaplace H (ρ.val - a))
      rw [← packetRow_divisor_eq χ (e ρ)]
      ring
    _ = c * ∑' z, f χ z := by rw [tsum_mul_left, hi.tsum_eq hcover]
    _ = _ := by dsimp [c]; ring

/-- Absolute convergence of a primitive width row transfers to the actual Mellin
samples on the entire positive idelic divisor. -/
theorem physicalWidthRow_norm_summable (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (H : ℝ → ℂ)
    (hH : Continuous H) (φ : BruhatCompactSupport Cℚ) (hφ : IsNormalizedCylinder q r H φ)
    (a : ℝ) (χ : DirichletCharacter ℂ q) (W : ℂ → ℕ → ℂ)
    (hs : Summable (fun z : Strip ↦ W z.val (completedPrimitiveOrder (χ, z)) *
      bilateralLaplace H (z.val - a))) :
    Summable (fun ρ : rowZeroSites (packetRow χ) ↦
      ‖W ρ.val (MeromorphicOn.divisor (continuedCompletedHeckeL (packetRow χ)) univ ρ.val).toNat *
        modulatedFourierMellin mℚ univ hmℚ μℚ φ.val (ideleClassNormTwist (packetRow χ) (ρ.val - a))‖) := by
  let e (ρ : rowZeroSites (packetRow χ)) : Strip := ⟨ρ.val, row_site_in_strip _ ρ⟩
  have hi : Injective e := fun _ _ he ↦ Subtype.ext (congrArg (fun z : Strip ↦ z.val) he)
  let c := conj (χ r.val) / (q.totient : ℂ)
  apply (Summable.congr ((hs.comp_injective hi).mul_left c) ?_).norm
  intro ρ
  rw [normalized_cylinder_mellin q r H hH φ hφ χ _ (packetRow_value χ)]
  change c * (W ρ.val (completedPrimitiveOrder (χ, e ρ)) * bilateralLaplace H (ρ.val - a)) =
    W ρ.val _ * (c * bilateralLaplace H (ρ.val - a))
  rw [← packetRow_divisor_eq χ (e ρ)]
  ring

private theorem stripMultiplicity_zero (a s x : ℝ) : spectralStripMultiplicity a s x 0 = 0 := by
  simp [spectralStripMultiplicity, spectralBoundaryMultiplicity]

/-- The wide-minus-narrow sum over the actual idelic divisor at spectral center zero. -/
def physicalSignedLost (q : ℕ) [NeZero q] (φ : BruhatCompactSupport Cℚ) (α β s : ℝ) : ℂ :=
  physicalWidthSum q φ 0 fun _ z m ↦
    (spectralStripMultiplicity β s z.re m : ℂ) - spectralStripMultiplicity α s z.re m

/-- The actual retained idelic zero sum at spectral center one half. -/
def physicalCenteredRetained (q : ℕ) [NeZero q] (φ : BruhatCompactSupport Cℚ) (α s : ℝ) : ℂ :=
  physicalWidthSum q φ (1 / 2) fun _ z m ↦ (spectralStripMultiplicity α s (z.re - 1 / 2) m : ℂ)

theorem physicalSignedLost_eq (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (H : ℝ → ℂ)
    (hH : Continuous H) (φ : BruhatCompactSupport Cℚ) (hφ : IsNormalizedCylinder q r H φ)
    (α β s : ℝ) :
    physicalSignedLost q φ α β s = cylinderAverage q r (signedLostRow α β s H) := by
  unfold physicalSignedLost
  rw [physicalWidthSum_eq q r H hH φ hφ _ _ (fun _ _ ↦ by simp [stripMultiplicity_zero])]
  simp only [Complex.ofReal_zero, sub_zero]
  rfl

theorem physicalCenteredRetained_eq (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (H : ℝ → ℂ)
    (hH : Continuous H) (φ : BruhatCompactSupport Cℚ) (hφ : IsNormalizedCylinder q r H φ)
    (α s : ℝ) :
    physicalCenteredRetained q φ α s = cylinderAverage q r (centeredRetainedRow α s H) := by
  unfold physicalCenteredRetained
  exact physicalWidthSum_eq q r H hH φ hφ _ _ (fun _ _ ↦ by simp [stripMultiplicity_zero])

/-- The off-center signed physical divisor of single congruence cylinders recovers the
negative von Mangoldt sample as the coprime modulus tends to infinity. -/
theorem physicalSignedLost_tendsto {ι : Type*} {l : Filter ι} {q : ι → ℕ} [∀ i, NeZero (q i)]
    (hq : Tendsto q l atTop) {b : ℕ} (hb : 2 ≤ b) (hbq : ∀ i, b.Coprime (q i))
    {α β s : ℝ} (hα : 0 ≤ α) (hn : α < 1 / 2) (hw : 1 / 2 < β)
    (hM : HistoricalMontgomeryDensity) (hef : PositiveLogDirichletFormula) {H : ℝ → ℂ}
    (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (hpos : tsupport H ⊆ Ioi 0)
    (hm₀ : bilateralLaplace H 0 = 0) (hm₁ : bilateralLaplace H 1 = 0) :
    Tendsto (fun i ↦ physicalSignedLost (q i)
      (selectedCylinder (q i) (ZMod.unitOfCoprime b (hbq i)) H hH hc) α β s)
      l (𝓝 (-primeSample H b)) := by
  apply (signedLostRow_tendsto (s := s) hq hb hbq hα hn hw hM hef hH hc hpos hm₀ hm₁).congr'
  exact .of_forall fun i ↦ (physicalSignedLost_eq _ _ _ hH.continuous _
    (selectedCylinder_spec _ _ H hH hc) α β s).symm

/-- The centered retained physical divisor recovers the same atom with its half-power weight. -/
theorem physicalCenteredRetained_tendsto {ι : Type*} {l : Filter ι} {q : ι → ℕ} [∀ i, NeZero (q i)]
    (hq : Tendsto q l atTop) {b : ℕ} (hb : 2 ≤ b) (hbq : ∀ i, b.Coprime (q i))
    {α s : ℝ} (hw : 0 < α) (hM : HistoricalMontgomeryDensity) (hef : PositiveLogDirichletFormula)
    {H : ℝ → ℂ} (hH : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (hpos : tsupport H ⊆ Ioi 0)
    (hmMinus : bilateralLaplace H (-1 / 2) = 0) (hmPlus : bilateralLaplace H (1 / 2) = 0) :
    Tendsto (fun i ↦ physicalCenteredRetained (q i)
      (selectedCylinder (q i) (ZMod.unitOfCoprime b (hbq i)) H hH hc) α s)
      l (𝓝 (-((((b : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * primeSample H b))) := by
  apply (centeredRetainedRow_tendsto (s := s) hq hb hbq hw hM hef hH hc hpos hmMinus hmPlus).congr'
  exact .of_forall fun i ↦ (physicalCenteredRetained_eq _ _ _ hH.continuous _
    (selectedCylinder_spec _ _ H hH hc) α s).symm

end RiemannMasullo.ConductorCylinder
