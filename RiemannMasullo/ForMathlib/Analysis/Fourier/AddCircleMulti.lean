module
public import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongBidual
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.Fourier.AddCircleMulti
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SeparatingDual

/-! # Fourier coefficients of continuous maps from the torus to Montel spaces -/

public section

open Bornology Filter Function MeasureTheory Metric Set Topology

namespace RiemannMasullo

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E] [MontelSpace ℂ E]

/-- A continuous family on a compact probability space has a barycentre in a Montel space.
Continuous linear functionals evaluate it by integrating the scalar evaluations. -/
theorem exists_dual_apply_eq_integral_of_montel {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsProbabilityMeasure μ]
    {u : K → E} (hu : Continuous u) :
    ∃ x : E, ∀ L : StrongDual ℂ E, L x = ∫ t, L (u t) ∂μ := by
  let T : StrongDual ℂ E →ₗ[ℂ] ℂ :=
    { toFun := fun L ↦ ∫ t, L (u t) ∂μ
      map_add' := fun L M ↦ integral_add ((L.continuous.comp hu).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
        ((M.continuous.comp hu).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c L ↦ integral_const_mul c _ }
  have hcont : Continuous T := by
    apply continuous_of_continuousAt_zero T
    rw [ContinuousAt, map_zero]
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hB := (isCompact_range hu).isVonNBounded ℂ
    filter_upwards [ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) hB
      (ball_mem_nhds (0 : ℂ) (half_pos hε))] with L hL
    rw [dist_zero_right]
    apply lt_of_le_of_lt _ (half_lt_self hε)
    exact norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all _ fun t ↦
      (mem_ball_zero_iff.mp (hL (mem_range_self t))).le) |>.trans_eq (by simp)
  obtain ⟨x, hx⟩ := surjective_strongBidual_eval (⟨T, hcont⟩ : StrongDual ℂ (StrongDual ℂ E))
  exact ⟨x, fun L ↦ DFunLike.congr_fun hx L⟩

/-- A continuous torus orbit in a Montel space lies at the identity in the closed
span of its Fourier coefficients, characterized by scalar integration. -/
theorem torus_mem_closedSpan_fourier {d : Type*} [Fintype d] {u : UnitAddTorus d → E}
    (hu : Continuous u) (S : Submodule ℂ E) (hS : IsClosed (S : Set E))
    (hcoeff : ∀ (k : d → ℤ) (v : E), (∀ L : StrongDual ℂ E,
      L v = UnitAddTorus.mFourierCoeff (fun t ↦ L (u t)) k) → v ∈ S) : u 0 ∈ S := by
  by_contra hn
  let : Module ℝ E := Module.restrictScalars ℝ ℂ E
  let : IsScalarTower ℝ ℂ E := IsScalarTower.restrictScalars ℝ ℂ E
  let : LocallyConvexSpace ℝ E := (PolynormableSpace.withSeminorms ℂ E).toLocallyConvexSpace
  obtain ⟨L, hne, hzero⟩ := exists_dual_eq_zero_on_submodule_of_notMem S hS hn
  let g : C(UnitAddTorus d, ℂ) := ⟨fun t ↦ L (u t), L.continuous.comp hu⟩
  have hz (k : d → ℤ) : UnitAddTorus.mFourierCoeff g k = 0 := by
    let V (t : UnitAddTorus d) := UnitAddTorus.mFourier (-k) t • u t
    obtain ⟨v, hv⟩ := exists_dual_apply_eq_integral_of_montel (u := V) (Measure.pi fun _ : d ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle))
      ((UnitAddTorus.mFourier (-k)).continuous.smul hu)
    have hv' (M : StrongDual ℂ E) : M v = UnitAddTorus.mFourierCoeff (fun t ↦ M (u t)) k := by
      change M v = ∫ t, UnitAddTorus.mFourier (-k) t • M (u t)
        ∂(Measure.pi fun _ : d ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle))
      simpa only [V, map_smul] using hv M
    exact (hv' L).symm.trans (hzero v (hcoeff k v hv'))
  have hsum : Summable (UnitAddTorus.mFourierCoeff g) := by simp [funext hz]
  have hh := UnitAddTorus.hasSum_mFourier_series_apply_of_summable (f := g) hsum 0
  apply hne
  change g 0 = 0
  simpa only [hz, zero_smul, tsum_zero] using hh.tsum_eq.symm

open UnitAddTorus in
/-- Translating the argument of a scalar torus function multiplies its Fourier coefficient
by the corresponding character. -/
theorem mFourierCoeff_add_left {d : Type*} [Fintype d] (k : d → ℤ)
    (g : UnitAddTorus d → ℂ) (z : UnitAddTorus d) :
    mFourierCoeff (fun t ↦ g (z + t)) k = mFourier k z * mFourierCoeff g k := by
  let μ := Measure.pi fun _ : d ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle)
  have hmul (t : UnitAddTorus d) : mFourier (-k) (z + t) = mFourier (-k) z * mFourier (-k) t := by
    simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, zsmul_add,
      AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]
  have hinv : mFourier k z * mFourier (-k) z = 1 := by rw [← mFourier_add, add_neg_cancel, mFourier_zero]; rfl
  change (∫ t, mFourier (-k) t * g (z + t) ∂μ) = mFourier k z * ∫ t, mFourier (-k) t * g t ∂μ
  rw [← integral_add_left_eq_self (μ := μ) (fun t ↦ mFourier (-k) t * g t) z, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [hmul, ← mul_assoc, ← mul_assoc, hinv, one_mul]

end RiemannMasullo
