module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedPolarVector

/-! # The fixed upper-cutoff coefficient on the polar vector -/

public noncomputable section

open Filter MeasureTheory Set
open scoped InnerProductSpace

namespace RiemannMasullo

local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)

/-- Recovering one vector by the angular lift is enough to compare its
cutoff coefficient with the corresponding coefficient in real coordinates. -/
theorem inner_cutoffFactor_eq_of_reflected_preimage
    {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (V : Submodule ℂ H) (Q : H →L[ℂ] G) (U : G ≃ₗᵢ[ℂ] G) (L : G →ₗᵢ[ℂ] H)
    (K : V →L[ℂ] G) (Acut : V →L[ℂ] H) (hAcut : Acut = L.toContinuousLinearMap.comp K)
    (u : V) (e : G) (hRecover : L (Q u.val) = u.val) (hTU : U (Q u.val) = e) :
    ⟪u.val, Acut u⟫_ℂ = ⟪U.symm e, K u⟫_ℂ := by
  have hAct : Acut u = L (K u) := congrArg (fun A : V →L[ℂ] H ↦ A u) hAcut
  have hQ : U.symm e = Q u.val := by rw [← hTU, U.symm_apply_apply]
  calc
    _ = ⟪L (Q u.val), L (K u)⟫_ℂ := by rw [hRecover, hAct]
    _ = ⟪Q u.val, K u⟫_ℂ := L.inner_map_map _ _
    _ = _ := by rw [hQ]

/-- In the trivial norm-one type the polar cutoff coefficient is the
pairing of the physical profile with the masked real convolution of the
unit exponential. The expression retains the fixed spatial cutoff. -/
theorem inner_cutoffFactor_eq_integral_of_exponential_preimage
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (V : Submodule ℂ H) (Q T : H →L[ℂ] FlatL2) (U : FlatL2 ≃ₗᵢ[ℂ] FlatL2)
    (L : FlatL2 →ₗᵢ[ℂ] H) (K : V →L[ℂ] FlatL2)
    (Acut : V →L[ℂ] H) (hAcut : Acut = L.toContinuousLinearMap.comp K)
    (u : V) (a : ℝ) (hRecover : L (Q u.val) = u.val)
    (hTQ : T u.val = U (Q u.val)) (huT : T u.val = normalizedHalflineExponentialL2 a)
    (ρ : ℝ → ℝ) (q : ℝ → ℂ)
    (hKrow : ∀ᵐ x : ℝ ∂volume,
      K u x = (ρ x : ℂ) * ∫ y, q (x - y) * T u.val y) :
    let integrand (x : ℝ) := (starRingEnd ℂ) (U.symm (normalizedHalflineExponentialL2 a) x) *
      ((ρ x : ℂ) * ∫ y in Ici a, q (x - y) * (Real.exp ((a - y) / 2) : ℂ))
    ⟪u.val, Acut u⟫_ℂ = (∫ x, integrand x) ∧ Integrable integrand := by
  intro integrand
  let e := normalizedHalflineExponentialL2 a
  have hCoord : U (Q u.val) = e := hTQ.symm.trans huT
  have hInnerEq := inner_cutoffFactor_eq_of_reflected_preimage V Q U L K Acut hAcut u e
    hRecover hCoord
  let row (x : ℝ) := (ρ x : ℂ) * ∫ y in Ici a, q (x - y) * (Real.exp ((a - y) / 2) : ℂ)
  have hRow : (K u : ℝ → ℂ) =ᵐ[volume] row := by
    filter_upwards [hKrow] with x hx
    change K u x = (ρ x : ℂ) * ∫ y in Ici a, q (x - y) * (Real.exp ((a - y) / 2) : ℂ)
    rw [hx, huT]
    apply congrArg ((ρ x : ℂ) * ·)
    rw [← integral_indicator measurableSet_Ici]
    apply integral_congr_ae
    filter_upwards [normalizedHalflineExponentialL2_ae_eq a] with y hy
    rw [hy]
    by_cases h : y ∈ Ici a
    · simp only [indicator_of_mem h]
    · simp only [indicator_of_notMem h, Complex.ofReal_zero, mul_zero]
  have hPair : (fun x ↦ inner ℂ (U.symm e x) (K u x)) =ᵐ[volume] integrand := by
    filter_upwards [hRow] with x hx
    calc
      _ = (starRingEnd ℂ) (U.symm e x) * K u x := RCLike.inner_apply' _ _
      _ = _ := congrArg (fun z ↦ (starRingEnd ℂ) (U.symm e x) * z) hx
  exact ⟨hInnerEq.trans ((L2.inner_def (U.symm e) (K u)).trans (integral_congr_ae hPair)),
    (L2.integrable_inner (𝕜 := ℂ) (U.symm e) (K u)).congr hPair⟩

end RiemannMasullo
