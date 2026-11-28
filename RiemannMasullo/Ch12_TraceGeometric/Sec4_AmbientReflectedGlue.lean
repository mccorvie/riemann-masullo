module

public import RiemannMasullo.AppC_LCTVS.Sec3b
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Ambient equality from agreement on a lifted angular space -/

public noncomputable section

open Filter Function MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace RiemannMasullo

section

variable {X H : Type*}
  [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [Measure.InnerRegular μ]

local notation "W" => Lp ℂ 2 μ

private theorem ae_integralKernelOperator_apply_rawAngularRow
    {k : X × X → ℂ} (hk : MemLp k 2 (μ.prod μ)) (u : W) :
    ∀ᵐ x ∂μ, (integralKernelOperator μ (hk.toLp k)).val u x =
      ∫ y, k (x, y) * u y ∂μ := by
  filter_upwards [integralKernelOperator_apply μ (hk.toLp k) u,
    Measure.ae_ae_of_ae_prod hk.coeFn_toLp] with x hx hkx
  refine hx.2.trans (integral_congr_ae ?_)
  filter_upwards [hkx] with y hy
  exact congrArg (· * u y) hy

/-- If the conjugated rows of a kernel lie in the angular lift, it
suffices to compare the kernel operator with the reflected action on a
dense span in that lift. -/
theorem integralKernelOperator_eq_reflectedAction_of_eqOn_angularClosure
    {k : X × X → ℂ} (hk : MemLp k 2 (μ.prod μ))
    (Q : W →L[ℂ] H) (L : H →ₗᵢ[ℂ] W) (U : H ≃ₗᵢ[ℂ] H)
    (M : H →L[ℂ] H) (C : W →L[ℂ] W)
    (hQL : LeftInverse Q L) (hQadj : Q.adjoint = L.toContinuousLinearMap)
    (V : Submodule ℂ W) (hV : V.topologicalClosure = LinearMap.range L.toLinearMap)
    (hRows : ∀ᵐ x ∂μ, ∃ r : H, (L r : X → ℂ) =ᵐ[μ] fun y ↦ star (k (x, y))) :
    let T := U.toLinearIsometry.toContinuousLinearMap.comp Q
    let B := (integralKernelOperator μ (hk.toLp k)).val
    let D := C.comp (T.adjoint.comp (M.comp T))
    EqOn B D (closure (V : Set W)) → B = D := by
  intro T B D hEq
  let P := L.toContinuousLinearMap.comp Q
  have hLadj : L.toContinuousLinearMap.adjoint = Q := by
    rw [← hQadj, ContinuousLinearMap.adjoint_adjoint]
  have hPadj : P.adjoint = P := by
    dsimp only [P]
    rw [ContinuousLinearMap.adjoint_comp, hQadj, hLadj]
  ext u : 1
  have hPu : P u ∈ closure (V : Set W) := by
    rw [← Submodule.topologicalClosure_coe, hV]
    exact LinearMap.mem_range.mpr ⟨Q u, rfl⟩
  have hBP : B (P u) = B u := by
    apply Lp.ext
    filter_upwards [hRows, ae_integralKernelOperator_apply_rawAngularRow μ hk (P u),
      ae_integralKernelOperator_apply_rawAngularRow μ hk u] with x hx hP hU
    obtain ⟨r, hr⟩ := hx
    change B (P u) x = B u x
    rw [hP, hU]
    have hinner (v : W) :
        (∫ y, k (x, y) * v y ∂μ) = ⟪L r, v⟫_ℂ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hr] with y hy
      simp [RCLike.inner_apply, hy, mul_comm]
    have hfix : P.adjoint (L r) = L r := by
      rw [hPadj]
      change L (Q (L r)) = L r
      rw [hQL r]
    calc
      _ = ⟪L r, P u⟫_ℂ := hinner _
      _ = ⟪P.adjoint (L r), u⟫_ℂ := (P.adjoint_inner_left u (L r)).symm
      _ = ⟪L r, u⟫_ℂ := by rw [hfix]
      _ = _ := (hinner _).symm
  have hTP : T (P u) = T u := by
    change U (Q (L (Q u))) = U (Q u)
    rw [hQL (Q u)]
  calc
    B u = B (P u) := hBP.symm
    _ = D (P u) := hEq hPu
    _ = D u := by
      change C (T.adjoint (M (T (P u)))) = C (T.adjoint (M (T u)))
      rw [hTP]

end

end RiemannMasullo
