module

public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! Banach–Steinhaus on a fixed test space and the polynomial cost of moving probes.
The normed output space may depend on the probe index. -/

@[expose] public noncomputable section

open Set
open scoped NNReal ENNReal

namespace RiemannMasullo.WeakCardinal

variable {E J κ : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
  [IsUniformAddGroup E] [ContinuousSMul ℂ E] [BarrelledSpace ℂ E]
  {H : J → Type*} [∀ j, NormedAddCommGroup (H j)] [∀ j, NormedSpace ℂ (H j)]

/-- Pointwise bounded linear readouts on a barrelled stage have one common finite input
seminorm bound. Each target embeds isometrically in one coordinate of the `ℓ²` direct sum. -/
theorem finiteSeminorm_bound_of_pointwise (p : κ → Seminorm ℂ E) (hp : WithSeminorms p)
    (L : (j : J) → E →L[ℂ] H j)
    (hpoint : ∀ x, ∃ B : ℝ, ∀ j, ‖L j x‖ ≤ B) :
    ∃ S : Finset κ, ∃ A : ℝ≥0, ∀ j x, ‖L j x‖ ≤ (A : ℝ) * (S.sup p) x := by
  classical
  let T (j : J) : E →L[ℂ] lp H 2 := (lp.singleContinuousLinearMap ℂ H 2 j).comp (L j)
  have hnorm (j : J) (x : E) : ‖T j x‖ = ‖L j x‖ := lp.norm_single (by norm_num) j _
  have he := (norm_withSeminorms ℂ (lp H 2)).banach_steinhaus (𝓕 := T) (fun _ x ↦ by
    obtain ⟨B, hB⟩ := hpoint x
    refine ⟨B, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact (hnorm j x).le.trans (hB j))
  obtain ⟨q, hq, hT⟩ := ((norm_withSeminorms ℂ (lp H 2)).uniformEquicontinuous_iff_exists_continuous_seminorm
    (fun j ↦ (T j).toLinearMap)).mp he ()
  obtain ⟨S, A, _, hA⟩ := Seminorm.bound_of_continuous hp q hq
  exact ⟨S, A, fun j x ↦ (hnorm j x).symm.le.trans ((hT j x).trans (hA x))⟩

/-- For the usual increasing sequence of stage seminorms, all the bounded singleton
readouts have one common input order, independent of both the site and the test. -/
theorem oneSeminorm_bound_of_pointwise (p : ℕ → Seminorm ℂ E) (hp : WithSeminorms p)
    (hmono : Monotone p) (L : (j : J) → E →L[ℂ] H j)
    (hpoint : ∀ x, ∃ B : ℝ, ∀ j, ‖L j x‖ ≤ B) :
    ∃ m : ℕ, ∃ A : ℝ≥0, ∀ j x, ‖L j x‖ ≤ (A : ℝ) * p m x := by
  obtain ⟨S, A, hA⟩ := finiteSeminorm_bound_of_pointwise p hp L hpoint
  have hS : S.sup p ≤ p (S.sup id) :=
    Finset.sup_le fun i hi ↦ hmono (Finset.le_sup (f := id) hi)
  exact ⟨S.sup id, A, fun j x ↦ (hA j x).trans
    (mul_le_mul_of_nonneg_left (hS x) A.coe_nonneg)⟩

/-- If every fixed test has uniformly bounded readouts and each individual stage seminorm
grows polynomially on the moving probes, their diagonal readouts have one polynomial bound.
The choice of growth exponent may initially vary with each seminorm. -/
theorem polynomial_probe_bound_of_pointwise (p : κ → Seminorm ℂ E) (hp : WithSeminorms p)
    (L : (j : J) → E →L[ℂ] H j) (hpoint : ∀ x, ∃ B : ℝ, ∀ j, ‖L j x‖ ≤ B)
    (probe : J → E) (height : J → ℝ) (hheight : ∀ j, 0 ≤ height j)
    (hprobe : ∀ k, ∃ C : ℝ≥0, ∃ N : ℕ, ∀ j, p k (probe j) ≤ (C : ℝ) * (1 + height j)^N) :
    ∃ C : ℝ≥0, ∃ N : ℕ, ∀ j, ‖L j (probe j)‖ ≤ (C : ℝ) * (1 + height j)^N := by
  classical
  obtain ⟨S, A, hA⟩ := finiteSeminorm_bound_of_pointwise p hp L hpoint
  choose C N h using hprobe
  refine ⟨A * S.sup C, S.sup N, fun j ↦ ?_⟩
  have hbase : 1 ≤ 1 + height j := by linarith [hheight j]
  have hs : (S.sup p) (probe j) ≤ (S.sup C : ℝ≥0) * (1 + height j)^(S.sup N) := by
    obtain hz | ⟨k, hk, he⟩ := Seminorm.zero_or_exists_apply_eq_finset_sup p S (probe j)
    · rw [hz]
      positivity
    · rw [he]
      have hC : (C k : ℝ) ≤ (S.sup C : ℝ≥0) := by exact_mod_cast (Finset.le_sup hk : C k ≤ S.sup C)
      exact (h k j).trans (mul_le_mul hC (pow_le_pow_right₀ hbase (Finset.le_sup hk))
        (pow_nonneg (zero_le_one.trans hbase) _) (NNReal.coe_nonneg _))
  exact (hA j _).trans ((mul_le_mul_of_nonneg_left hs A.coe_nonneg).trans_eq
    (by push_cast; ring))

end RiemannMasullo.WeakCardinal
