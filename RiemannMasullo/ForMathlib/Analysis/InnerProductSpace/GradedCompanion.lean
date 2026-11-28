module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Traces of inverse triangular operators and finite Hilbert–Schmidt bounds

A coercive finite-dimensional operator with strictly order-lowering off-diagonal
entries has an inverse with known trace. This controls the column sum of a test
operator which factors through that inverse.
-/

@[expose] public noncomputable section

open Complex
open scoped InnerProductSpace

namespace RiemannMasullo

/-- The inverse of a finite operator with strictly degree-lowering off-diagonal
entries has the reciprocal eigenvalues on its diagonal, also with repeated degrees. -/
private theorem trace_symm_of_graded_triangular {ι E : Type*} [Fintype ι]
    [AddCommGroup E] [Module ℂ E] (b : Module.Basis ι ℂ E) (A : E ≃ₗ[ℂ] E)
    (degree : ι → ℕ) (d : ι → ℂ)
    (hdiag : ∀ i, b.repr (A (b i)) i = d i)
    (htri : ∀ i j, i ≠ j → degree j ≤ degree i → b.repr (A (b j)) i = 0) :
    LinearMap.trace ℂ E A.symm.toLinearMap = ∑ i, (d i)⁻¹ := by
  classical
  let M := LinearMap.toMatrix b b A.toLinearMap
  let N := LinearMap.toMatrix b b A.symm.toLinearMap
  have hNM : N*M = 1 := by
    dsimp only [M,N]
    rw [← LinearMap.toMatrix_comp]
    simp
  let : Invertible M := invertibleOfLeftInverse M N hNM
  have hM : Matrix.BlockTriangular M degree := by
    intro i j hji
    simpa [M, LinearMap.toMatrix_apply] using htri i j (by rintro rfl; exact (lt_irrefl _ hji)) hji.le
  have hN : Matrix.BlockTriangular N degree := by
    rw [← Matrix.inv_eq_left_inv hNM]
    exact Matrix.blockTriangular_inv_of_blockTriangular hM
  have hd (i : ι) : N i i * d i = 1 := by
    calc
      _ = N i i * M i i := by rw [show M i i = d i by simpa [M, LinearMap.toMatrix_apply] using hdiag i]
      _ = (N*M) i i := by
        rw [Matrix.mul_apply, Finset.sum_eq_single i]
        · intro j _ hji
          rcases lt_or_ge (degree j) (degree i) with h | h
          · rw [hN h, zero_mul]
          · rw [show M j i = 0 by simpa [M, LinearMap.toMatrix_apply] using htri j i hji h, mul_zero]
        · simp
      _ = 1 := by rw [hNM]; simp
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  change ∑ i, N i i = _
  apply Fintype.sum_congr; intro i
  have hne : d i ≠ 0 := by intro h; have hh := hd i; simp [h] at hh
  calc
    _ = (N i i * d i) * (d i)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
    _ = _ := by rw [hd, one_mul]

/-- Numerical coercivity of a finite triangular generator and one bounded companion
control the squared Hilbert--Schmidt norm in any orthonormal basis. -/
private theorem finite_graded_companion_column_bound {ι κ E H : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (b : Module.Basis ι ℂ E) (e : OrthonormalBasis κ ℂ E) (Y : E →ₗ[ℂ] E)
    (degree : ι → ℕ) (d : ι → ℂ)
    (hdiag : ∀ i, b.repr (Y (b i)) i = d i)
    (htri : ∀ i j, i ≠ j → degree j ≤ degree i → b.repr (Y (b j)) i = 0)
    {c : ℝ} (hc : 0 < c) (hY : ∀ x, c*‖x‖^2 ≤ (⟪x,Y x⟫_ℂ).re)
    (T U : E →L[ℂ] H) (hU : ∀ x, U x = T (Y x)) :
    c * ∑ k, ‖T (e k)‖^2 ≤ ‖U‖^2 * ∑ i, ((d i)⁻¹).re := by
  classical
  let : FiniteDimensional ℂ E := Module.Finite.of_basis b
  have hker : ∀ x, Y x = 0 → x = 0 := by
    intro x hx
    by_contra h
    have hpos := mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr h))
    have hz := hY x
    rw [hx, inner_zero_right, Complex.zero_re] at hz
    linarith
  have hinj : Function.Injective Y := by
    intro x y hxy
    exact sub_eq_zero.mp (hker (x-y) (by rw [map_sub, hxy, sub_self]))
  let A := LinearEquiv.ofBijective Y ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  have htr := trace_symm_of_graded_triangular b A degree d hdiag htri
  rw [A.symm.toLinearMap.trace_eq_sum_inner e] at htr
  have hre := congrArg Complex.re htr
  simp only [Complex.re_sum] at hre
  have hbound (x : E) : c*‖T x‖^2 ≤ ‖U‖^2*(⟪x,A.symm x⟫_ℂ).re := by
    have hleft : Y (A.symm x) = x := A.apply_symm_apply x
    have hU' : U (A.symm x) = T x := (hU (A.symm x)).trans (congrArg T hleft)
    have h := hY (A.symm x)
    rw [hleft, show (⟪A.symm x,x⟫_ℂ).re = (⟪x,A.symm x⟫_ℂ).re from inner_re_symm (𝕜 := ℂ) _ _] at h
    calc
      _ ≤ c*(‖U‖*‖A.symm x‖)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hU' ▸ U.le_opNorm _) 2) hc.le
      _ = ‖U‖^2*(c*‖A.symm x‖^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h (sq_nonneg _)
  calc
    _ = ∑ k, c*‖T (e k)‖^2 := Finset.mul_sum _ _ _
    _ ≤ ∑ k, ‖U‖^2*(⟪e k,A.symm (e k)⟫_ℂ).re := Finset.sum_le_sum fun k _ ↦ hbound _
    _ = _ := by rw [← Finset.mul_sum]; exact congrArg (‖U‖^2 * ·) hre

/-- Uniform finite-column estimate for a family of Jordan chains with an explicitly
coercive generator. The numerical inequality is needed on coefficient sums in the
ambient space; the conclusion is in an arbitrary orthonormal basis of their span. -/
theorem finite_jetFamily_companion_column_bound {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : ι → E) (hv : LinearIndependent ℂ v) (d : ι → ℂ) (degree : ι → ℕ) (pred : ι → ι)
    (hpred : ∀ i, degree i ≠ 0 → degree (pred i) < degree i)
    (hd : ∀ i, 0 ≤ ((d i)⁻¹).re) {c : ℝ} (hc : 0 < c)
    (hform : ∀ a : ι → ℂ, c*‖∑ i, a i • v i‖^2 ≤
      (⟪∑ i, a i • v i, ∑ i, a i • (d i • v i - (degree i : ℂ) • v (pred i))⟫_ℂ).re)
    (T U : E →L[ℂ] E) (hU : ∀ i, U (v i) = T (d i • v i - (degree i : ℂ) • v (pred i)))
    (V : Submodule ℂ E) (hvV : ∀ i, v i ∈ V)
    (e : OrthonormalBasis ι ℂ (Submodule.span ℂ (Set.range v))) :
    c * ∑ k, ‖T (e k : E)‖^2 ≤ ‖U.comp V.subtypeL‖^2 * ∑ i, ((d i)⁻¹).re := by
  classical
  let H := Submodule.span ℂ (Set.range v)
  let b : Module.Basis ι ℂ H := Module.Basis.span hv
  have hb (i : ι) : (b i : E) = v i := Module.Basis.coe_span_apply _ _
  let Y : H →ₗ[ℂ] H := b.constr ℂ fun i ↦ d i • b i - (degree i : ℂ) • b (pred i)
  have hYb (i : ι) : Y (b i) = d i • b i - (degree i : ℂ) • b (pred i) :=
    b.constr_basis ℂ _ i
  have hcoords (i j : ι) : b.repr (Y (b j)) i =
      d j * (if j = i then 1 else 0) - (degree j : ℂ) * (if pred j = i then 1 else 0) := by
    rw [hYb, map_sub, map_smul, map_smul]
    simp [Finsupp.single_apply]
  have hdiag (i : ι) : b.repr (Y (b i)) i = d i := by
    rw [hcoords]
    by_cases hi : degree i = 0
    · simp [hi]
    · have hne : pred i ≠ i := by
        intro he
        have h := hpred i hi
        rw [he] at h
        exact (lt_irrefl _ h)
      simp [hne]
  have htri (i j : ι) (hij : i ≠ j) (hle : degree j ≤ degree i) :
      b.repr (Y (b j)) i = 0 := by
    rw [hcoords]
    by_cases hj : degree j = 0
    · simp [hij.symm,hj]
    · have hne : pred j ≠ i := by
        intro he
        have h := hpred j hj
        rw [he] at h
        omega
      simp [hij.symm,hne]
  have hY (x : H) : c*‖x‖^2 ≤ (⟪x,Y x⟫_ℂ).re := by
    let a (i : ι) := b.repr x i
    have hx : ∑ i, a i • v i = (x : E) := by
      have h := congrArg H.subtype (b.sum_repr x)
      simpa only [map_sum, map_smul, Submodule.subtype_apply, hb, a] using h
    have hYx : ∑ i, a i • (d i • v i - (degree i : ℂ) • v (pred i)) = (Y x : E) := by
      have h := congrArg (H.subtype.comp Y) (b.sum_repr x)
      simpa only [map_sum, map_smul, LinearMap.comp_apply, Submodule.subtype_apply, hYb,
        Submodule.coe_sub, Submodule.coe_smul, hb, a] using h
    have h := hform a
    rw [hx,hYx] at h
    exact h
  have hmatch (x : H) : (U.comp H.subtypeL) x = (T.comp H.subtypeL) (Y x) := by
    have heq : (U.comp H.subtypeL).toLinearMap = (T.comp H.subtypeL).toLinearMap.comp Y := by
      apply b.ext; intro i
      change U (b i : E) = T (Y (b i) : E)
      rw [hYb, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul, hb, hb]
      exact hU i
    exact DFunLike.congr_fun heq x
  have h := finite_graded_companion_column_bound b e Y degree d hdiag htri hc hY
    (T.comp H.subtypeL) (U.comp H.subtypeL) hmatch
  have hHV : H ≤ V := Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hvV i)
  have hop : ‖U.comp H.subtypeL‖ ≤ ‖U.comp V.subtypeL‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _); intro x
    exact (U.comp V.subtypeL).le_opNorm ⟨x.val,hHV x.property⟩
  exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hop 2)
    (Finset.sum_nonneg fun i _ ↦ hd i))

end RiemannMasullo
