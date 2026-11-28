module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxQuotient
import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Exact leakage through the first physical prefix of the rational box

A scalar Möbius transform of an isometric forward period takes the preceding
completed stage isometrically onto the next. Before the first actual delay its
only contribution is the negative attenuation scalar. -/

noncomputable section

open Filter MeasureTheory Set
open scoped NNReal

namespace RiemannMasullo.ShiftMobius

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : H →ₗᵢ[ℂ] H) (β : ℝ) (h₀ : 0 ≤ β) (h₁ : β < 1)

/-- The invertible denominator, including when the Hilbert space is trivial. -/
def denominator : (H →L[ℂ] H)ˣ :=
  Units.oneSub ((β : ℂ) • S.toContinuousLinearMap) (by
    have h : ‖S.toContinuousLinearMap‖ ≤ 1 :=
      S.toContinuousLinearMap.opNorm_le_bound zero_le_one (fun x => by simp)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h₀]
    exact lt_of_le_of_lt ((mul_le_mul_of_nonneg_left h h₀).trans_eq (mul_one β)) h₁)

@[simp] theorem denominator_apply (x : H) :
    (denominator S β h₀ h₁).val x = x - (β : ℂ) • S x := rfl

private theorem norm_balance (x : H) :
    ‖S x - (β : ℂ) • x‖ = ‖x - (β : ℂ) • S x‖ := by
  have h : ‖S x - (β : ℂ) • x‖ ^ 2 = ‖x - (β : ℂ) • S x‖ ^ 2 := by
    simp only [norm_sub_sq (𝕜 := ℂ), norm_smul, S.norm_map, inner_smul_right,
      Complex.re_ofReal_mul, RCLike.re_to_complex]
    have hc : (inner ℂ (S x) x).re = (inner ℂ x (S x)).re :=
      inner_re_symm (𝕜 := ℂ) (S x) x
    rw [hc]
  nlinarith [norm_nonneg (S x - (β : ℂ) • x), norm_nonneg (x - (β : ℂ) • S x)]

/-- The forward Möbius transform, formed with the actual Neumann inverse. -/
def isometry : H →ₗᵢ[ℂ] H where
  toLinearMap := (S.toLinearMap - (β : ℂ) • LinearMap.id).comp
    (denominator S β h₀ h₁)⁻¹.val.toLinearMap
  norm_map' x := by
    let U := denominator S β h₀ h₁
    change ‖S (U⁻¹.val x) - (β : ℂ) • U⁻¹.val x‖ = ‖x‖
    rw [norm_balance S β]
    change ‖U.val (U⁻¹.val x)‖ = ‖x‖
    rw [← mul_apply_eq_comp, Units.mul_inv, one_apply_eq_self]

@[simp] theorem isometry_denominator (x : H) :
    isometry S β h₀ h₁ ((denominator S β h₀ h₁).val x) = S x - (β : ℂ) • x := by
  let U := denominator S β h₀ h₁
  change S (U⁻¹.val (U.val x)) - (β : ℂ) • U⁻¹.val (U.val x) = _
  rw [← mul_apply_eq_comp, Units.inv_mul, one_apply_eq_self]

theorem range_isometry : LinearMap.range (isometry S β h₀ h₁).toLinearMap =
    LinearMap.range (S.toLinearMap - (β : ℂ) • LinearMap.id) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(denominator S β h₀ h₁)⁻¹.val x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨(denominator S β h₀ h₁).val x, isometry_denominator S β h₀ h₁ x⟩

theorem isometry_add_mem_shift (x : H) :
    ∃ y, isometry S β h₀ h₁ x + (β : ℂ) • x = S y := by
  let U := denominator S β h₀ h₁
  obtain ⟨w, rfl⟩ := (ContinuousLinearMap.homeomorphOfUnit U).surjective x
  change ∃ y, isometry S β h₀ h₁ ((denominator S β h₀ h₁).val w) +
    (β : ℂ) • (denominator S β h₀ h₁).val w = S y
  refine ⟨w - (β : ℂ) • ((β : ℂ) • w), ?_⟩
  rw [isometry_denominator, denominator_apply, smul_sub, map_sub, map_smul, map_smul]
  abel

end RiemannMasullo.ShiftMobius

namespace RiemannMasullo.RationalPacket

/-- A stage readout which kills `V + c • id` has exactly the indicated
attenuation on the range of the norm-preserving endomorphism `V`. -/
theorem norm_comp_subtypeL_of_isometric_range
    {𝕜 E Y : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (B : E →L[𝕜] Y) (V : E →L[𝕜] E) (N : Submodule 𝕜 E)
    (hN : N = LinearMap.range V.toLinearMap) (hV : ∀ x, ‖V x‖ = ‖x‖)
    (c : 𝕜) (hkill : ∀ x, B (V x + c • x) = 0) :
    ‖B.comp N.subtypeL‖ = ‖c‖ * ‖B‖ := by
  have hpoint (x : E) : B (V x) = ((-c) • B) x := by
    have h := hkill x
    rw [map_add, map_smul] at h
    change B (V x) = (-c) • B x
    simpa only [neg_smul] using eq_neg_of_add_eq_zero_left h
  calc
    ‖B.comp N.subtypeL‖ = ‖(-c) • B‖ := by
      apply le_antisymm
      · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
        intro y
        have hy : (y : E) ∈ LinearMap.range V.toLinearMap :=
          (congrArg (fun P : Submodule 𝕜 E => (y : E) ∈ P) hN).mp y.property
        obtain ⟨x, hx⟩ := hy
        change V x = (y : E) at hx
        change ‖B (y : E)‖ ≤ ‖(-c) • B‖ * ‖(y : E)‖
        rw [← hx, hpoint, hV]
        exact ((-c) • B).le_opNorm x
      · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
        intro x
        have hx : V x ∈ N := by rw [hN]; exact ⟨x, rfl⟩
        have h := (B.comp N.subtypeL).le_opNorm (⟨V x, hx⟩ : N)
        change ‖B (V x)‖ ≤ ‖B.comp N.subtypeL‖ * ‖V x‖ at h
        rwa [hpoint, hV] at h
    _ = ‖c‖ * ‖B‖ := by rw [norm_smul, norm_neg]

/-- Real nonnegative attenuation for complex stage readouts. -/
theorem norm_comp_subtypeL_of_prefix_kill
    {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (B : E →L[ℂ] Y) (V : E →L[ℂ] E) (N : Submodule ℂ E)
    (hN : N = LinearMap.range V.toLinearMap) (hV : ∀ x, ‖V x‖ = ‖x‖)
    (β : ℝ) (hβ : 0 ≤ β) (hkill : ∀ x, B (V x + (β : ℂ) • x) = 0) :
    ‖B.comp N.subtypeL‖ = β * ‖B‖ := by
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ] using
    norm_comp_subtypeL_of_isometric_range B V N hN hV (β : ℂ) hkill

/-- The identity on compressed orthogonal projections, not just on readout norms. -/
private theorem comp_adjoint_subtypeL_of_prefix_kill
    {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (B : E →L[ℂ] Y) (V : E →ₗᵢ[ℂ] E) (N : Submodule ℂ E) [CompleteSpace N]
    (hN : N = LinearMap.range V.toLinearMap)
    (β : ℝ) (hkill : ∀ x, B (V x + (β : ℂ) • x) = 0) :
    (B.comp N.subtypeL).comp (B.comp N.subtypeL).adjoint =
      ((β ^ 2 : ℝ) : ℂ) • (B.comp B.adjoint) := by
  have hmem (x : E) : V x ∈ N := hN ▸ ⟨x, rfl⟩
  let W : E →ₗᵢ[ℂ] N :=
    { toLinearMap := V.toLinearMap.codRestrict N hmem
      norm_map' := V.norm_map }
  have hsur : Function.Surjective W := by
    intro y
    have hy : (y : E) ∈ LinearMap.range V.toLinearMap := hN ▸ y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  let U := LinearIsometryEquiv.ofSurjective W hsur
  let D := (U : E →L[ℂ] N)
  let C := B.comp N.subtypeL
  have hD (y : N) : D (D.adjoint y) = y := by
    change U (ContinuousLinearMap.adjoint (U : E →L[ℂ] N) y) = y
    rw [U.adjoint_eq_symm]
    exact U.apply_symm_apply y
  have hC : C.comp D = (-(β : ℂ)) • B := by
    ext x
    have h := hkill x
    rw [map_add, map_smul] at h
    change B (V x) = (-(β : ℂ)) • B x
    simpa only [neg_smul] using eq_neg_of_add_eq_zero_left h
  have hscalar : starRingEnd ℂ (-(β : ℂ)) = -(β : ℂ) := by simp
  calc
    C.comp C.adjoint = (C.comp D).comp (C.comp D).adjoint := by
      rw [show (C.comp D).adjoint = D.adjoint.comp C.adjoint from
        ContinuousLinearMap.adjoint_comp C D]
      apply ContinuousLinearMap.ext
      intro y
      exact congrArg C (hD (C.adjoint y)).symm
    _ = ((β ^ 2 : ℝ) : ℂ) • (B.comp B.adjoint) := by
      rw [hC, map_smulₛₗ, hscalar]
      ext y
      simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul, smul_smul]
      congr 1
      push_cast
      ring

private theorem comp_starProjection_of_prefix_kill
    {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (B : E →L[ℂ] Y) (V : E →ₗᵢ[ℂ] E) (N : Submodule ℂ E) [CompleteSpace N]
    (hN : N = LinearMap.range V.toLinearMap)
    (β : ℝ) (hkill : ∀ x, B (V x + (β : ℂ) • x) = 0) :
    B.comp (N.starProjection.comp B.adjoint) =
      ((β ^ 2 : ℝ) : ℂ) • (B.comp B.adjoint) := by
  calc
    _ = (B.comp N.subtypeL).comp (B.comp N.subtypeL).adjoint := by
      rw [ContinuousLinearMap.adjoint_comp, N.adjoint_subtypeL]
      apply ContinuousLinearMap.ext
      intro y
      change B (N.starProjection (B.adjoint y)) = B (↑(N.orthogonalProjectionOnto (B.adjoint y)))
      rw [Submodule.starProjection_apply]
    _ = _ := comp_adjoint_subtypeL_of_prefix_kill B V N hN β hkill

section StagePeriod

variable {X : ℝ} (hX : 0 < X) (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q)
variable (p : ℕ) (hp : 1 < p)

local notation "E" => closedStageSubmodule X T hT

def stagePeriodBeta (p : ℕ) : ℝ := (Real.exp (Real.log (p : ℝ) / 2))⁻¹

theorem stagePeriodBeta_pos : 0 < stagePeriodBeta p := inv_pos.mpr (Real.exp_pos _)

include hp in
theorem stagePeriodBeta_lt_one : stagePeriodBeta p < 1 := by
  change (Real.exp _)⁻¹ < 1
  exact inv_lt_one_of_one_lt₀ (Real.one_lt_exp_iff.mpr (half_pos (Real.log_pos (by exact_mod_cast hp))))

private def stagePeriodNNReal (q : ℕ) (hq : 1 < q) : ℝ≥0 :=
  ⟨Real.log (q : ℝ), Real.log_nonneg (by exact_mod_cast hq.le)⟩

local notation "L" => stagePeriodNNReal p hp
local notation "R" => closedStageForwardShift T hT hX L
local notation "β" => (stagePeriodBeta p : ℂ)

/-- Ordinary (untwisted) right translation through one period on the stage. -/
def stageUnitPeriod : E →ₗᵢ[ℂ] E where
  toLinearMap := (β • R).toLinearMap
  norm_map' u := by
    change ‖β • R u‖ = ‖u‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (stagePeriodBeta_pos p)]
    change stagePeriodBeta p * ‖(R u : ℝ →₂[volume] ℂ)‖ = ‖(u : ℝ →₂[volume] ℂ)‖
    rw [closedStageForwardShift_apply, norm_halfShift,
      show (L : ℝ) = Real.log (p : ℝ) from rfl]
    change (Real.exp _)⁻¹ * (Real.exp _ * _) = _
    rw [← mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul]

local notation "S" => stageUnitPeriod hX T hT p hp

/-- Subtraction of the attenuation scalar gives exactly the next denominator. -/
theorem range_stageUnitPeriod_sub_beta (hmem : p ∉ T) (hTp : ∀ q ∈ insert p T, 1 ≤ q) :
    range (LinearIsometry.toContinuousLinearMap S - β • ContinuousLinearMap.id ℂ E) =
      (fixedBoxDenominator X T hT p hTp : Set E) := by
  let D := LinearIsometry.toContinuousLinearMap S - β • ContinuousLinearMap.id ℂ E
  have hD (u : E) : (D u : ℝ →₂[volume] ℂ) = stagePeriodDifference p (β • (u : ℝ →₂[volume] ℂ)) := by
    rw [map_smul, stagePeriodDifference_apply, smul_sub]
    change β • (R u : ℝ →₂[volume] ℂ) - β • (u : ℝ →₂[volume] ℂ) = _
    rw [closedStageForwardShift_apply, show (L : ℝ) = Real.log (p : ℝ) from rfl]
  have hr := range_stagePeriodDifference_closedStage hX T hT hp hmem hTp
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    rw [mem_fixedBoxDenominator_iff, ← hr]
    exact ⟨β • u, (hD u).symm⟩
  · intro hy
    rw [mem_fixedBoxDenominator_iff, ← hr] at hy
    obtain ⟨u, hu⟩ := hy
    refine ⟨β⁻¹ • u, Subtype.ext ?_⟩
    change (D (β⁻¹ • u) : ℝ →₂[volume] ℂ) = (y : ℝ →₂[volume] ℂ)
    rw [hD]
    change stagePeriodDifference p (β • (β⁻¹ • (u : ℝ →₂[volume] ℂ))) = _
    have hn : β ≠ 0 := Complex.ofReal_ne_zero.mpr (stagePeriodBeta_pos p).ne'
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
    exact hu

/-- The normalized shift vanishes throughout the physical prefix, endpoint included. -/
theorem stageUnitPeriod_vanishes_prefix {b : ℝ} (hb : b ≤ -Real.log X + Real.log p) (u : E) :
    ∀ᵐ x ∂volume, x ≤ b → (S u : ℝ →₂[volume] ℂ) x = 0 := by
  change ∀ᵐ x ∂volume, x ≤ b → (β • (R u : ℝ →₂[volume] ℂ) : ℝ →₂[volume] ℂ) x = 0
  rw [closedStageForwardShift_apply, show (L : ℝ) = Real.log (p : ℝ) from rfl]
  have hs := (measurePreserving_add_right volume (-Real.log (p : ℝ))).quasiMeasurePreserving.ae
    (closedStageSubmodule_supported hX T hT u.property)
  filter_upwards [Lp.coeFn_smul β (halfShift (Real.log p) (u : ℝ →₂[volume] ℂ)),
    halfShift_ae (Real.log p) (u : ℝ →₂[volume] ℂ), hs, Measure.ae_ne volume b] with x hx hh hzero hne hxb
  change x - Real.log p < -Real.log X → (u : ℝ →₂[volume] ℂ) (x - Real.log p) = 0 at hzero
  have hlt := lt_of_le_of_ne hxb hne
  rw [hx]
  change β * (halfShift (Real.log p) (u : ℝ →₂[volume] ℂ)) x = 0
  rw [hh, hzero (by linarith), mul_zero, mul_zero]

end StagePeriod

/-- Before the first delay, every physical readout loses exactly the factor
`exp (-(log p)/2)` on restriction to the actual next Hilbert stage. -/
public theorem norm_fixedBox_prefix_leakage {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 1 ≤ q) (p : ℕ) (hp : 1 < p) (hmem : p ∉ T)
    (hTp : ∀ q ∈ insert p T, 1 ≤ q) {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (B : closedStageSubmodule X T hT →L[ℂ] Y) {b : ℝ} (hb : b ≤ -Real.log X + Real.log p)
    (hwindow : ∀ v : closedStageSubmodule X T hT,
      (∀ᵐ x ∂volume, x ≤ b → (v : ℝ →₂[volume] ℂ) x = 0) → B v = 0) :
    ‖B.comp (fixedBoxDenominator X T hT p hTp).toSubmodule.subtypeL‖ =
      (Real.exp (Real.log (p : ℝ) / 2))⁻¹ * ‖B‖ := by
  let N := (fixedBoxDenominator X T hT p hTp).toSubmodule
  let S := stageUnitPeriod hX T hT p hp
  let β := stagePeriodBeta p
  have hp0 : 0 ≤ β := (stagePeriodBeta_pos p).le
  have hp1 : β < 1 := stagePeriodBeta_lt_one p hp
  let V := ShiftMobius.isometry S β hp0 hp1
  have hr : N = LinearMap.range V.toContinuousLinearMap.toLinearMap := by
    change N = LinearMap.range (ShiftMobius.isometry S β hp0 hp1).toLinearMap
    rw [ShiftMobius.range_isometry]
    apply SetLike.coe_injective
    exact (range_stageUnitPeriod_sub_beta hX T hT p hp hmem hTp).symm
  refine norm_comp_subtypeL_of_prefix_kill B V.toContinuousLinearMap N hr V.norm_map β hp0 ?_
  intro w
  change B (V w + (β : ℂ) • w) = 0
  obtain ⟨y, hy⟩ := ShiftMobius.isometry_add_mem_shift S β hp0 hp1 w
  rw [hy]
  exact hwindow _ (stageUnitPeriod_vanishes_prefix hX T hT p hp hb y)

/-- The physical readout compression of the orthogonal projector loses the
square of the first-delay attenuation. This includes the sharp endpoint. -/
public theorem comp_adjoint_fixedBox_prefix_leakage {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 1 ≤ q) (p : ℕ) (hp : 1 < p) (hmem : p ∉ T)
    (hTp : ∀ q ∈ insert p T, 1 ≤ q) {Y : Type*} [NormedAddCommGroup Y]
    [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (B : closedStageSubmodule X T hT →L[ℂ] Y) {b : ℝ} (hb : b ≤ -Real.log X + Real.log p)
    (hwindow : ∀ v : closedStageSubmodule X T hT,
      (∀ᵐ x ∂volume, x ≤ b → (v : ℝ →₂[volume] ℂ) x = 0) → B v = 0) :
    let N := (fixedBoxDenominator X T hT p hTp).toSubmodule
    B.comp (N.starProjection.comp B.adjoint) =
      ((p : ℂ)⁻¹) • (B.comp B.adjoint) := by
  let N := (fixedBoxDenominator X T hT p hTp).toSubmodule
  let S := stageUnitPeriod hX T hT p hp
  let β := stagePeriodBeta p
  have hp0 : 0 ≤ β := (stagePeriodBeta_pos p).le
  have hp1 : β < 1 := stagePeriodBeta_lt_one p hp
  let V := ShiftMobius.isometry S β hp0 hp1
  have hr : N = LinearMap.range V.toLinearMap := by
    dsimp [V]
    rw [ShiftMobius.range_isometry]
    apply SetLike.coe_injective
    exact (range_stageUnitPeriod_sub_beta hX T hT p hp hmem hTp).symm
  have hβ : β ^ 2 = (p : ℝ)⁻¹ := by
    change (Real.exp (Real.log (p : ℝ) / 2))⁻¹ ^ 2 = (p : ℝ)⁻¹
    rw [inv_pow, sq, ← Real.exp_add, add_halves, Real.exp_log (by positivity)]
  change B.comp (N.starProjection.comp B.adjoint) = _
  have hout := comp_starProjection_of_prefix_kill B V N hr β (by
    intro w
    obtain ⟨y, hy⟩ := ShiftMobius.isometry_add_mem_shift S β hp0 hp1 w
    rw [hy]
    exact hwindow _ (stageUnitPeriod_vanishes_prefix hX T hT p hp hb y))
  rw [hβ] at hout
  push_cast at hout
  exact hout

end RiemannMasullo.RationalPacket
