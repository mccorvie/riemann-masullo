module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Hilbert-space factorization of absolutely summing operators -/

public noncomputable section
open Set Filter Topology MeasureTheory
open scoped BigOperators ComplexConjugate CompactlySupported

namespace RiemannMasullo
namespace AbsolutelySumming

universe u

variable {X : Type u} {Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- The absolute summability estimate for finite families, tested against the dual unit ball. -/
abbrev HasBound (T : X →L[ℂ] Y) (C : ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → X) (M : ℝ), 0 ≤ M →
    (∀ φ : StrongDual ℂ X, ‖φ‖ ≤ 1 → ∑ i, ‖φ (x i)‖ ≤ M) →
    ∑ i, ‖T (x i)‖ ≤ C * M

/-- The quadratic summability estimate, with its constant given in squared units. -/
abbrev HasQuadraticBound (T : X →L[ℂ] Y) (D : ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → X) (M : ℝ), 0 ≤ M →
    (∀ φ : StrongDual ℂ X, ‖φ‖ ≤ 1 → ∑ i, ‖φ (x i)‖ ^ 2 ≤ M) →
    ∑ i, ‖T (x i)‖ ^ 2 ≤ D * M

/-- The absolute summability estimate on finite families implies its quadratic version. -/
theorem sum_sq_le (T : X →L[ℂ] Y) {C : ℝ} (hC : 0 ≤ C)
    (hT : HasBound T C)
    {n : ℕ} (x : Fin n → X) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ φ : StrongDual ℂ X, ‖φ‖ ≤ 1 → ∑ i, ‖φ (x i)‖ ^ 2 ≤ M) :
    ∑ i, ‖T (x i)‖ ^ 2 ≤ C ^ 2 * M := by
  let L := ∑ i, ‖T (x i)‖ ^ 2
  have hL : 0 ≤ L := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have bound := hT n (fun i ↦ (‖T (x i)‖ : ℂ) • x i) (√(L * M)) (Real.sqrt_nonneg _) (by
    intro φ hφ
    simp only [map_smul, norm_smul, Complex.norm_real, norm_norm]
    exact Real.le_sqrt_of_sq_le ((Finset.univ.sum_mul_sq_le_sq_mul_sq _ _).trans
      (mul_le_mul_of_nonneg_left (h φ hφ) hL)))
  simp only [map_smul, norm_smul, Complex.norm_real, norm_norm, ← pow_two] at bound
  change L ≤ _ at bound ⊢
  by_cases hz : L = 0
  · rw [hz]; positivity
  have hsq := (sq_le_sq₀ hL (mul_nonneg hC (Real.sqrt_nonneg _))).mpr bound
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hL hM)] at hsq
  exact (mul_le_mul_iff_right₀ (lt_of_le_of_ne hL (Ne.symm hz))).mp (by nlinarith only [hsq])

private abbrev Ball (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] :=
  (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ X) 1 : Set (WeakDual ℂ X))

private instance : CompactSpace (Ball X) :=
  isCompact_iff_compactSpace.mp (WeakDual.isCompact_closedBall 0 1)

private def pt : Ball X := ⟨0, by simp [Ball, Metric.mem_closedBall]⟩

private theorem unitBound (k : Ball X) : ‖k.val.toStrongDual‖ ≤ 1 := by
  exact (mem_closedBall_zero_iff.mp k.property)

private def cost (T : X →L[ℂ] Y) (C : ℝ) (x : X) (k : Ball X) :=
  C ^ 2 * ‖k.val x‖ ^ 2 - ‖T x‖ ^ 2

/-- The cone consists of continuous functions dominating a finite sum of the pointwise
quadratic errors. Scaling the test vectors by a square root scales the errors. -/
private def cone (T : X →L[ℂ] Y) (C : ℝ) : PointedCone ℝ C_c(Ball X, ℝ) where
  carrier := {f | ∃ (n : ℕ) (x : Fin n → X), ∀ k, ∑ i, cost T C (x i) k ≤ f k}
  zero_mem' := ⟨0, Fin.elim0, by simp⟩
  add_mem' := by
    rintro f g ⟨n, x, hx⟩ ⟨m, y, hy⟩
    refine ⟨n + m, Fin.append x y, fun k ↦ ?_⟩
    simpa [Fin.sum_univ_add] using add_le_add (hx k) (hy k)
  smul_mem' := by
    rintro ⟨r, hr⟩ f ⟨n, x, hx⟩
    refine ⟨n, fun i ↦ (√r : ℂ) • x i, fun k ↦ ?_⟩
    have hc (i : Fin n) : cost T C ((√r : ℂ) • x i) k = r * cost T C (x i) k := by
      simp only [cost, map_smul, norm_smul, Complex.norm_of_nonneg (Real.sqrt_nonneg _),
        mul_pow, Real.sq_sqrt hr]; ring
    simpa only [hc, ← Finset.mul_sum] using! mul_le_mul_of_nonneg_left (hx k) hr

private theorem cone_nonneg (T : X →L[ℂ] Y) (C : ℝ) (f : C_c(Ball X, ℝ))
    (hf : ∀ k, 0 ≤ f k) : f ∈ cone T C :=
  ⟨0, Fin.elim0, fun k ↦ by simpa using hf k⟩

private theorem exists_nonneg_of_mem (T : X →L[ℂ] Y) {C : ℝ}
    (hT : HasQuadraticBound T (C ^ 2))
    (f : C_c(Ball X, ℝ)) (hf : f ∈ cone T C) : ∃ k, 0 ≤ f k := by
  obtain ⟨n, x, hx⟩ := hf
  let F (k : Ball X) := ∑ i, ‖k.val (x i)‖ ^ 2
  have hF : Continuous F := continuous_finsetSum _ fun i _ ↦
    (((WeakDual.eval_continuous (x i)).comp continuous_subtype_val).norm.pow 2)
  obtain ⟨k, _, hk⟩ := isCompact_univ.exists_isMaxOn ⟨pt, trivial⟩ hF.continuousOn
  have h := hT n x (F k) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) fun φ hφ ↦ by
    let t : Ball X := ⟨φ.toWeakDual, by simpa [Ball, Metric.mem_closedBall] using hφ⟩
    exact hk (show t ∈ univ from trivial)
  refine ⟨k, le_trans ?_ (hx k)⟩
  simpa [cost, Finset.sum_sub_distrib, ← Finset.mul_sum, F] using sub_nonneg.mpr h

/-- A probability measure on the weak-star dual ball dominates an absolutely summing operator. -/
private theorem domination (T : X →L[ℂ] Y) {C : ℝ} (hC : 0 ≤ C)
    (hT : HasBound T C) :
    letI : MeasurableSpace (Ball X) := borel _
    ∃ μ : Measure (Ball X), IsProbabilityMeasure μ ∧
      ∀ x, ‖T x‖ ^ 2 ≤ C ^ 2 * ∫ k, ‖k.val x‖ ^ 2 ∂μ := by
  classical
  let : MeasurableSpace (Ball X) := borel _
  let : BorelSpace (Ball X) := ⟨rfl⟩
  let V := C_c(Ball X, ℝ)
  let o : V := ⟨1, HasCompactSupport.of_compactSpace _⟩
  let ev : V →ₗ[ℝ] ℝ :=
    { toFun f := f pt, map_add' _ _ := rfl, map_smul' _ _ := rfl }
  let p := ev.toPMap (Submodule.span ℝ {o})
  have hpos (f : p.domain) (hf : (f : V) ∈ cone T C) : 0 ≤ p f := by
    obtain ⟨k, hk⟩ := exists_nonneg_of_mem T (fun _ _ _ ↦ sum_sq_le T hC hT _) _ hf
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp f.property
    change 0 ≤ f.val pt
    rw [← hr] at hk ⊢
    exact hk
  have hmajor (f : V) : ∃ g : p.domain, (g : V) + f ∈ cone T C := by
    let r := ‖f.toContinuousMap‖
    refine ⟨⟨r • o, Submodule.mem_span_singleton.mpr ⟨r, rfl⟩⟩, cone_nonneg T C _ fun k ↦ ?_⟩
    change 0 ≤ r * 1 + f k
    have h := (f.toContinuousMap.norm_coe_le_norm k)
    have h' := neg_le_abs (f k)
    change |f k| ≤ r at h
    linarith
  obtain ⟨g, hg, hcone⟩ := riesz_extension (cone T C) p hpos hmajor
  let Λ := PositiveLinearMap.mk₀ g (fun f hf ↦ hcone _ (cone_nonneg T C f hf))
  let μ := RealRMK.rieszMeasure Λ
  have hone : g o = 1 := hg ⟨o, Submodule.mem_span_singleton_self _⟩
  have hprob : IsProbabilityMeasure μ := by
    constructor
    apply (ENNReal.toReal_eq_one_iff _).mp
    have h := (RealRMK.integral_rieszMeasure Λ o).trans hone
    simpa only [o, CompactlySupportedContinuousMap.coe_mk, ContinuousMap.one_apply,
      integral_const, smul_eq_mul, mul_one, measureReal_def, μ] using h
  refine ⟨μ, hprob, fun x ↦ ?_⟩
  let f : V := ⟨⟨fun k ↦ ‖k.val x‖ ^ 2,
    (((WeakDual.eval_continuous x).comp continuous_subtype_val).norm.pow 2)⟩,
    HasCompactSupport.of_compactSpace _⟩
  have hmem : C ^ 2 • f - ‖T x‖ ^ 2 • o ∈ cone T C :=
    ⟨1, fun _ ↦ x, fun k ↦ by
      rw [Fin.sum_univ_one]
      change _ ≤ C ^ 2 * ‖k.val x‖ ^ 2 - ‖T x‖ ^ 2 * 1
      rw [mul_one]; rfl⟩
  have h := hcone _ hmem
  rw [map_sub, map_smul, map_smul, hone, smul_eq_mul, smul_eq_mul, mul_one, sub_nonneg] at h
  exact h.trans_eq (congrArg (C ^ 2 * ·) (RealRMK.integral_rieszMeasure Λ f).symm)

/-- Pietsch factorization, with the quadratic finite-family estimate on the first factor. -/
theorem factor [CompleteSpace Y] (T : X →L[ℂ] Y) {C : ℝ} (hC : 0 ≤ C)
    (hT : HasBound T C) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (a : X →L[ℂ] H) (d : H →L[ℂ] Y), (∀ x, d (a x) = T x) ∧
        ∀ (n : ℕ) (x : Fin n → X) (M : ℝ),
          (∀ φ : StrongDual ℂ X, ‖φ‖ ≤ 1 → ∑ i, ‖φ (x i)‖ ^ 2 ≤ M) →
          ∑ i, ‖a (x i)‖ ^ 2 ≤ M := by
  let : MeasurableSpace (Ball X) := borel _
  let : BorelSpace (Ball X) := ⟨rfl⟩
  obtain ⟨μ, hμ, hdom⟩ := domination T hC hT
  let V : Type u := Lp ℂ 2 μ
  let f : X →ₗ[ℂ] C(Ball X, ℂ) :=
    { toFun x := ⟨fun k ↦ k.val x, (WeakDual.eval_continuous x).comp continuous_subtype_val⟩
      map_add' x y := ContinuousMap.ext fun k ↦ map_add k.val x y
      map_smul' c x := ContinuousMap.ext fun k ↦ map_smul k.val c x }
  let F := f.mkContinuous 1 fun x ↦ (ContinuousMap.norm_le _ (norm_nonneg x)).mpr
    (fun k ↦ (k.val.toStrongDual.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) (unitBound k)))
    |>.trans_eq (one_mul _).symm
  let A := (ContinuousMap.toLp 2 μ ℂ).comp F
  have hnorm (x : X) : ‖A x‖ ^ 2 = ∫ k, ‖k.val x‖ ^ 2 ∂μ := by
    calc
      _ = ∫ k, ‖A x k‖ ^ 2 ∂μ := by
        rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ, L2.inner_def]
        simp_rw [inner_self_eq_norm_sq_to_K]
        norm_cast
      _ = _ := integral_congr_ae ((ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (F x)).fun_comp
        (fun c ↦ ‖c‖ ^ 2))
  let R := LinearMap.range A.toLinearMap
  let a := A.codRestrict R.topologicalClosure fun x ↦ R.le_topologicalClosure ⟨x, rfl⟩
  let : CompleteSpace R.topologicalClosure := R.isClosed_topologicalClosure.completeSpace_coe
  have hd : DenseRange a := by
    change DenseRange (Set.inclusion (s := (R : Set V))
      (R.le_topologicalClosure : (R : Set V) ⊆ R.topologicalClosure) ∘ Set.rangeFactorization A)
    exact ((denseRange_inclusion_iff _).mpr subset_rfl).comp
      Set.rangeFactorization_surjective.denseRange (continuous_inclusion _)
  have hb (x : X) : ‖T x‖ ≤ C * ‖a x‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
    rw [mul_pow]
    change _ ≤ C ^ 2 * ‖A x‖ ^ 2
    rw [hnorm]
    exact hdom x
  refine ⟨_, inferInstance, inferInstance, inferInstance, a, T.toLinearMap.extendOfNorm a.toLinearMap,
    LinearMap.extendOfNorm_eq hd ⟨C, hb⟩, fun n x M hx ↦ ?_⟩
  change ∑ i, ‖A (x i)‖ ^ 2 ≤ M
  simp only [hnorm]
  have hint (i : Fin n) : Integrable (fun k : Ball X ↦ ‖k.val (x i)‖ ^ 2) μ :=
    (((WeakDual.eval_continuous (x i)).comp continuous_subtype_val).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← integral_finsetSum _ fun i _ ↦ hint i]
  simpa using integral_mono (integrable_finsetSum _ fun i _ ↦ hint i)
    (integrable_const (μ := μ) M) (fun k ↦ hx k.val.toStrongDual (unitBound k))

end AbsolutelySumming
end RiemannMasullo
