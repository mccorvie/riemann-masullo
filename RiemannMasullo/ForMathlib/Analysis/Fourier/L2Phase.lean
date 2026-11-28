module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.Integrable
import Mathlib.MeasureTheory.Function.Holder

/-! # Unitary Fourier phase correction on L² -/

open Filter MeasureTheory
open scoped ENNReal FourierTransform

namespace RiemannMasullo

public noncomputable section

private theorem mul_star_eq_one_of_norm_eq_one (z : ℂ) (hz : ‖z‖ = 1) :
    z * star z = 1 := by
  change z * (starRingEnd ℂ) z = 1
  simpa [Complex.normSq_eq_norm_sq, hz] using Complex.mul_conj z

/-- Multiplication by a measurable unit-modulus symbol is unitary on L²,
with inverse given by multiplication by the conjugate symbol. -/
theorem exists_L2_unitModulusMultiplier {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (m : X → ℂ) (hm : AEStronglyMeasurable m ν)
    (hunit : ∀ᵐ x ∂ν, ‖m x‖ = 1) :
    ∃ M : Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 ν,
      (∀ v, (M v : X → ℂ) =ᵐ[ν] fun x ↦ m x * v x) ∧
      ∀ v, (M.symm v : X → ℂ) =ᵐ[ν] fun x ↦ star (m x) * v x := by
  have hb : MemLp m ∞ ν := memLp_top_of_bound hm 1 (hunit.mono fun x hx ↦ hx.le)
  let mult := ContinuousLinearMap.mul ℂ ℂ
  let A := mult.holderL ν (⊤ : ENNReal) 2 2 (hb.toLp m)
  let B := mult.holderL ν (⊤ : ENNReal) 2 2 (hb.star.toLp (star m))
  have hA (v : Lp ℂ 2 ν) : (A v : X → ℂ) =ᵐ[ν] fun x ↦ m x * v x :=
    (mult.coeFn_holder (r := 2) (hb.toLp m) v).trans
      (hb.coeFn_toLp.mono fun x hx ↦ congrArg (· * v x) hx)
  have hB (v : Lp ℂ 2 ν) : (B v : X → ℂ) =ᵐ[ν] fun x ↦ star (m x) * v x :=
    (mult.coeFn_holder (r := 2) (hb.star.toLp (star m)) v).trans
      (hb.star.coeFn_toLp.mono fun x hx ↦ congrArg (· * v x) hx)
  have hnorm (v : Lp ℂ 2 ν) : ‖A v‖ = ‖v‖ := by
    have h : ∀ᵐ x ∂ν, ‖A v x‖ = ‖v x‖ := by
      filter_upwards [hA v, hunit] with x hx hu
      rw [hx, norm_mul, hu, one_mul]
    exact le_antisymm (Lp.norm_le_norm_of_ae_le (h.mono fun x hx ↦ hx.le))
      (Lp.norm_le_norm_of_ae_le (h.mono fun x hx ↦ hx.ge))
  have hAB (v : Lp ℂ 2 ν) : A (B v) = v := by
    apply Lp.ext
    filter_upwards [hA (B v), hB v, hunit] with x hx hy hu
    rw [hx, hy, ← mul_assoc, mul_star_eq_one_of_norm_eq_one _ hu, one_mul]
  let A₁ : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 ν :=
    ⟨A.toLinearMap, hnorm⟩
  let M := LinearIsometryEquiv.ofSurjective A₁ fun v ↦ ⟨B v, hAB v⟩
  have hInv (v : Lp ℂ 2 ν) : M.symm v = B v := by
    apply M.injective
    exact (M.apply_symm_apply v).trans (hAB v).symm
  refine ⟨M, hA, fun v ↦ ?_⟩
  rw [hInv v]
  exact hB v

local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "fourierL2" => Lp.fourierTransformₗᵢ ℝ ℂ

private theorem flatL2_fourier_ae_of_integrable_rep (v : FlatL2) {p : ℝ → ℂ}
    (hp : Integrable p) (hv : (v : ℝ → ℂ) =ᵐ[volume] p) :
    (fourierL2 v : ℝ → ℂ) =ᵐ[volume] 𝓕 p :=
  (fourier_L2_coeFn_of_integrable v (hp.congr hv.symm)).trans
    (ae_of_all _ fun ξ ↦ Real.fourier_congr_ae hv ξ)

/-- Conjugate phase multiplication by the real Plancherel transform. If
integrable representatives satisfy the Fourier phase identity, the operator
recovers the phase-free L² class exactly. -/
theorem exists_L2FourierInversePhase (m : ℝ → ℂ) (hm : AEStronglyMeasurable m volume)
    (hunit : ∀ᵐ ξ ∂volume, ‖m ξ‖ = 1) :
    ∃ U : FlatL2 ≃ₗᵢ[ℂ] FlatL2,
      (∀ v, (fourierL2 (U v) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦ star (m ξ) * (fourierL2 v : FlatL2) ξ) ∧
      (∀ v, (fourierL2 (U.symm v) : ℝ → ℂ) =ᵐ[volume] fun ξ ↦ m ξ * (fourierL2 v : FlatL2) ξ) ∧
      ∀ (v w : FlatL2) (p r : ℝ → ℂ), Integrable p → Integrable r →
        (v : ℝ → ℂ) =ᵐ[volume] p → (w : ℝ → ℂ) =ᵐ[volume] r →
        (∀ᵐ ξ ∂volume, 𝓕 p ξ = m ξ * 𝓕 r ξ) → U v = w := by
  obtain ⟨M, hM, hMinv⟩ := exists_L2_unitModulusMultiplier volume m hm hunit
  let F := Lp.fourierTransformₗᵢ ℝ ℂ
  let U := (F.trans M.symm).trans F.symm
  have hU (v : FlatL2) : fourierL2 (U v) = M.symm (fourierL2 v) := by
    change F (F.symm (M.symm (F v))) = M.symm (F v)
    exact F.apply_symm_apply _
  have hUinv (v : FlatL2) : fourierL2 (U.symm v) = M (fourierL2 v) := by
    change F (F.symm (M (F v))) = M (F v)
    exact F.apply_symm_apply _
  refine ⟨U, fun v ↦ (hU v).symm ▸ hMinv (fourierL2 v),
    fun v ↦ (hUinv v).symm ▸ hM (fourierL2 v), ?_⟩
  intro v w p r hp hr hv hw hphase
  apply F.injective
  change fourierL2 (U v) = fourierL2 w
  apply Lp.ext
  rw [hU v]
  filter_upwards [hMinv (fourierL2 v), flatL2_fourier_ae_of_integrable_rep v hp hv,
    flatL2_fourier_ae_of_integrable_rep w hr hw, hphase, hunit]
    with ξ h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₂, h₃, h₄, ← mul_assoc, mul_comm (star (m ξ)) (m ξ),
    mul_star_eq_one_of_norm_eq_one _ h₅, one_mul]

end

end RiemannMasullo
