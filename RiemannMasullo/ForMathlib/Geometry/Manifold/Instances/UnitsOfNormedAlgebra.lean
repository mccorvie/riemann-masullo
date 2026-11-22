module

public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex

noncomputable section

open Filter Topology
open scoped ContDiff Manifold NNReal

namespace RiemannMasullo

local notation "valueℝ" => fun (t : ℝ≥0ˣ) ↦ ((t : ℝ≥0) : ℝ)
local notation "expUnit" => fun s : ℝ ↦ Homeomorph.symm (Nonneg.unitsHomeomorphPos ℝ) (Real.expOrderIso s)

/-- A continuous multiplicative function on the additive group of a finite-dimensional
real vector space is smooth. In a basis it is a product of one-dimensional exponentials. -/
private theorem contDiff_additive_character {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V → ℂ) (hA : Continuous A) (h0 : A 0 = 1)
    (hadd : ∀ x y, A (x + y) = A x * A y) : ContDiff ℝ (∞ : ℕ∞ω) A := by
  classical
  let b := Module.finBasis ℝ V
  have hline (v : V) : ContDiff ℝ (∞ : ℕ∞ω) (fun t : ℝ ↦ A (t • v)) := by
    let c : ℝ≥0ˣ →ₜ* ℂ :=
      { toFun := fun t ↦ A (Real.log (valueℝ t) • v)
        map_one' := by simpa only [Units.val_one, NNReal.coe_one, Real.log_one, zero_smul] using h0
        map_mul' := fun t u ↦ by
          change A (Real.log ((t.val : ℝ) * u.val) • v) = _
          rw [Real.log_mul (NNReal.coe_ne_zero.mpr t.ne_zero) (NNReal.coe_ne_zero.mpr u.ne_zero),
            add_smul, hadd]
        continuous_toFun := hA.comp (((NNReal.continuous_coe.comp Units.continuous_val).log fun t ↦
          NNReal.coe_ne_zero.mpr t.ne_zero).smul continuous_const) }
    obtain ⟨z, hz, -⟩ := existsUnique_complexPower c
    have heq (s : ℝ) : A (s • v) = Complex.exp ((s : ℂ) * z) := by
      have h := hz (expUnit s)
      change A (Real.log (Real.exp s) • v) = (Real.exp s : ℂ) ^ z at h
      rw [Real.log_exp, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos s).ne'),
        ← Complex.ofReal_log (Real.exp_pos s).le, Real.log_exp] at h
      exact h
    rw [funext heq]
    exact Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have hsum (S : Finset (Fin (Module.finrank ℝ V))) (w : Fin (Module.finrank ℝ V) → V) :
      A (∑ i ∈ S, w i) = ∏ i ∈ S, A (w i) := by
    induction S using Finset.induction_on with
    | empty => simpa using h0
    | insert i S hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, hadd, ih]
  have hcoord (i) : ContDiff ℝ (∞ : ℕ∞ω) (fun x : V ↦ A ((b.equivFun x i) • b i)) :=
    (hline (b i)).comp ((contDiff_apply ℝ _ i).comp b.equivFun.toContinuousLinearEquiv.contDiff)
  have heq (x : V) : A x = ∏ i, A ((b.equivFun x i) • b i) := by
    rw [← hsum, b.sum_equivFun]
  rw [funext heq]
  exact contDiff_prod (t := Finset.univ) fun i _ ↦ hcoord i

/-- Characters of the units of a commutative real Banach algebra are smooth in the units charts. -/
public theorem contMDiff_units_character {V : Type*} [NormedCommRing V] [NormedAlgebra ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] (χ : Vˣ →* ℂ) (hχ : Continuous χ) :
    ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, ℂ) (∞ : ℕ∞ω) χ := by
  let +nondep : NormedAlgebra ℚ V := .restrictScalars ℚ ℝ V
  let U (v : V) : Vˣ := ⟨NormedSpace.exp v, NormedSpace.exp (-v),
    by rw [← NormedSpace.exp_add, add_neg_cancel, NormedSpace.exp_zero],
    by rw [← NormedSpace.exp_add, neg_add_cancel, NormedSpace.exp_zero]⟩
  have hv (v : V) : (U v).val = NormedSpace.exp v := rfl
  have hU : Continuous U := Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr
    NormedSpace.exp_continuous
  have hU0 : U 0 = 1 := Units.ext NormedSpace.exp_zero
  have hUadd (x y : V) : U (x + y) = U x * U y := Units.ext NormedSpace.exp_add
  have hF : ContDiff ℝ (∞ : ℕ∞ω) (fun v ↦ χ (U v)) := contDiff_additive_character _ (hχ.comp hU)
    ((congrArg χ hU0).trans (map_one _)) (fun x y ↦ (congrArg χ (hUadd x y)).trans (map_mul χ _ _))
  have hExp : ContDiffAt ℝ (∞ : ℕ∞ω) (NormedSpace.exp : V → V) 0 :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) (x := (0 : V))).contDiffAt
  let L := ContinuousLinearEquiv.refl ℝ V
  have hD : HasFDerivAt NormedSpace.exp (L : V →L[ℝ] V) (0 : V) := hasFDerivAt_exp_zero
  let log := hExp.localInverse (f' := L) hD (by simp)
  have hlog : ContDiffAt ℝ (∞ : ℕ∞ω) log 1 := by
    simpa only [NormedSpace.exp_zero] using hExp.to_localInverse (f' := L) hD (by simp)
  have hright : ∀ᶠ x : V in 𝓝 1, NormedSpace.exp (log x) = x := by
    unfold log ContDiffAt.localInverse
    simpa only [NormedSpace.exp_zero] using (hExp.hasStrictFDerivAt (f' := L) hD (by simp)).eventually_right_inverse
  intro a
  let p (x : Vˣ) : V := (x * a⁻¹).val
  have hp : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V) (∞ : ℕ∞ω) p :=
    Units.contMDiff_val.comp (contMDiff_id.mul contMDiff_const)
  have hp0 : p a = 1 := by simp [p]
  have hloc : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, ℂ) (∞ : ℕ∞ω) (fun x ↦ χ (U (log (p x))) * χ a) a := by
    have hl : ContDiffAt ℝ (∞ : ℕ∞ω) log (p a) := hp0 ▸ hlog
    exact ((contDiff_id.mul (contDiff_const (c := χ a))).contMDiff.contMDiffAt.comp _
      (hF.contMDiff.contMDiffAt.comp _ (hl.contMDiffAt.comp a (hp a))))
  apply hloc.congr_of_eventuallyEq
  have hnear : Tendsto p (𝓝 a) (𝓝 1) := hp0 ▸ hp.continuous.continuousAt
  filter_upwards [hnear.eventually hright] with x hx
  have hu : U (log (p x)) = x * a⁻¹ := Units.ext hx
  rw [hu, ← map_mul, inv_mul_cancel_right]

end RiemannMasullo
