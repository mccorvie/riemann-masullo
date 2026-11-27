module

public import RiemannMasullo.AppC_LCTVS.Sec3a
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.TriangularDiagonal
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecificLimits.Normed

/-! # The Hilbert trace of a triangular operator

Independent continuous linear functionals with common kernel zero yield a Hilbert basis by
applying Gram–Schmidt to their Riesz vectors. This computes the trace of a nuclear operator
whose action on the successive kernels prescribes its diagonal.
-/

@[expose] public noncomputable section

open InnerProductSpace Submodule
open scoped InnerProductSpace

namespace RiemannMasullo

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

/-- A nuclear operator which acts triangularly on a linearly independent family of bounded
functionals with common kernel zero has trace equal to the sum of its diagonal entries. -/
theorem hilbertTrace_eq_tsum_of_triangular (T : nuclearEndomorphisms H)
    (ℓ : ι → H →L[ℂ] ℂ) (hℓ : LinearIndependent ℂ ℓ)
    (hsep : ∀ x, (∀ i, ℓ i x = 0) → x = 0) (d : ι → ℂ)
    (htri : ∀ i x, (∀ j < i, ℓ j x = 0) → ℓ i (T.val x) = d i * ℓ i x) :
    hilbertTrace T = ∑' i, d i := by
  let e := (toDual ℂ H).symm
  let v (i : ι) : H := e (ℓ i)
  have hv : LinearIndependent ℂ v := by
    refine hℓ.map_of_injective_injectiveₛ (starRingEnd ℂ) e.toAddEquiv.toAddMonoidHom
      ?_ e.injective ?_
    · intro a b hab
      simpa using congrArg (starRingEnd ℂ) hab
    · intro a φ
      change e (starRingEnd ℂ a • φ) = a • e φ
      calc
        e (starRingEnd ℂ a • φ) = starRingEnd ℂ (starRingEnd ℂ a) • e φ :=
          e.toLinearIsometry.toLinearMap.map_smulₛₗ _ _
        _ = a • e φ := by simp only [starRingEnd_apply, star_star]
  have hpair (i : ι) (x : H) : ⟪v i, x⟫_ℂ = ℓ i x := toDual_symm_apply
  have hperp : (span ℂ (Set.range v))ᗮ = ⊥ := by
    refine le_bot_iff.mp fun x hx ↦ ?_
    rw [Submodule.mem_bot]
    refine hsep x fun i ↦ ?_
    exact (hpair i x).symm.trans ((Submodule.mem_orthogonal _ _).mp hx _
      (subset_span (Set.mem_range_self i)))
  let u := gramSchmidtNormed ℂ v
  have hu : (span ℂ (Set.range u))ᗮ = ⊥ := by
    change (span ℂ (Set.range (gramSchmidtNormed ℂ v)))ᗮ = ⊥
    rwa [span_gramSchmidtNormed_range, span_gramSchmidt]
  let b : HilbertBasis ι ℂ H := HilbertBasis.mkOfOrthogonalEqBot
    (gramSchmidtNormed_orthonormal hv) hu
  have hb : (b : ι → H) = u := HilbertBasis.coe_mkOfOrthogonalEqBot _ _
  let b₀ := (exists_hilbertBasis (𝕜 := ℂ) (E := H)).choose_spec.choose
  calc
    hilbertTrace T = ∑' i, ⟪b₀ i, T.val (b₀ i)⟫_ℂ := rfl
    _ = ∑' i, ⟪b i, T.val (b i)⟫_ℂ := tsum_hilbertDiagonal_eq b₀ b T.val T.property
    _ = ∑' i, d i := by
      simp only [hb]
      refine tsum_congr fun i ↦ inner_gramSchmidtNormed_map_of_triangular v T.val d ?_ ?_
      · simpa only [hpair] using htri
      · exact (gramSchmidtNormed_orthonormal hv).ne_zero i

/-- When the diagonal of a triangular nuclear operator is geometric, the Hilbert trace is its
first term divided by one minus the ratio. The functionals can be shifted Taylor coefficients
when the first few Taylor coefficients vanish identically. -/
theorem hilbertTrace_eq_of_triangular_geometric (T : nuclearEndomorphisms H)
    (ℓ : ℕ → H →L[ℂ] ℂ) (hℓ : LinearIndependent ℂ ℓ)
    (hsep : ∀ x, (∀ i, ℓ i x = 0) → x = 0) (a q : ℂ) (hq : ‖q‖ < 1)
    (htri : ∀ i x, (∀ j < i, ℓ j x = 0) → ℓ i (T.val x) = (a * q ^ i) * ℓ i x) :
    hilbertTrace T = a / (1 - q) := by
  rw [hilbertTrace_eq_tsum_of_triangular T ℓ hℓ hsep _ htri]
  exact ((hasSum_geometric_of_norm_lt_one hq).mul_left a).tsum_eq.trans
    (div_eq_mul_inv a (1 - q)).symm

/-- An odd derivative of an even scalar function vanishes at the origin. -/
private theorem iteratedDeriv_odd_at_zero_of_even (f : ℝ → ℂ)
    (hf : ∀ z, f (-z) = f z) (j : ℕ) : iteratedDeriv (2 * j + 1) f 0 = 0 := by
  have he : (fun z ↦ f (-z)) = f := funext hf
  have h := iteratedDeriv_comp_neg (2 * j + 1) f 0
  rw [he, neg_zero, pow_add, pow_mul] at h
  norm_num [neg_smul] at h
  linear_combination h / 2

/-- The first potentially nonzero derivative of a multiplied dilate changes by the
multiplier at zero and by the corresponding power of the dilation factor. -/
private theorem iteratedDeriv_mul_dilation_at_zero (m f : ℝ → ℂ) (q : ℝ) (k : ℕ)
    (hm : ∀ j : ℕ, ContDiff ℝ j m) (hf : ∀ j : ℕ, ContDiff ℝ j f)
    (hzero : ∀ j < k, iteratedDeriv j f 0 = 0) :
    iteratedDeriv k (fun z ↦ m z * f (q * z)) 0 =
      m 0 * (q : ℂ) ^ k * iteratedDeriv k f 0 := by
  have hc : ContDiff ℝ k (fun z : ℝ ↦ q * z) := contDiff_const.mul contDiff_id
  have hscaled (j : ℕ) : iteratedDeriv j (fun z ↦ f (q * z)) 0 =
      (q : ℂ) ^ j * iteratedDeriv j f 0 := by
    simpa only [mul_zero, Complex.real_smul, Complex.ofReal_pow] using
      congrFun (iteratedDeriv_comp_const_smul (hf j) q) 0
  rw [iteratedDeriv_fun_mul (hm k).contDiffAt ((hf k).fun_comp hc).contDiffAt]
  rw [Finset.sum_eq_single 0]
  · simp [hscaled, mul_assoc]
  · intro j hj hj₀
    rw [hscaled, hzero (k - j) (by simp only [Finset.mem_range] at hj; omega)]
    simp
  · simp

/-- A smooth even realization of a nuclear multiplier-dilation has a geometric trace. The
realization has identically zero jets below order `2 * n`. The even jets from order `2 * n` on
are independent bounded functionals that separate points. -/
theorem hilbertTrace_eq_of_even_multiplier_dilation (T : nuclearEndomorphisms H)
    (f : H → ℝ → ℂ) (m : ℝ → ℂ) (q : ℝ) (hq : ‖q‖ < 1) (n : ℕ)
    (hf : ∀ x (k : ℕ), ContDiff ℝ k (f x)) (hm : ∀ k : ℕ, ContDiff ℝ k m)
    (heven : ∀ x z, f x (-z) = f x z)
    (hzero : ∀ x k, k < 2 * n → iteratedDeriv k (f x) 0 = 0)
    (hT : ∀ x z, f (T.val x) z = m z * f x (q * z))
    (ℓ : ℕ → H →L[ℂ] ℂ) (hℓ : LinearIndependent ℂ ℓ)
    (hsep : ∀ x, (∀ i, ℓ i x = 0) → x = 0)
    (hjet : ∀ i x, ℓ i x = iteratedDeriv (2 * (n + i)) (f x) 0) :
    hilbertTrace T = m 0 * (q : ℂ) ^ (2 * n) / (1 - (q : ℂ) ^ 2) := by
  refine hilbertTrace_eq_of_triangular_geometric T ℓ hℓ hsep _ _ ?_ ?_
  · rw [norm_pow, Complex.norm_real]
    exact pow_lt_one₀ (norm_nonneg _) hq (by decide)
  intro i x hlow
  have hlower : ∀ k < 2 * (n + i), iteratedDeriv k (f x) 0 = 0 := by
    intro k hk
    by_cases hn : k < 2 * n
    · exact hzero x k hn
    have hmod := Nat.mod_add_div k 2
    by_cases hodd : k % 2 = 1
    · rw [show k = 2 * (k / 2) + 1 by omega]
      exact iteratedDeriv_odd_at_zero_of_even (f x) (heven x) _
    · have h₁ : k = 2 * (n + (k / 2 - n)) := by omega
      have h₂ : k / 2 - n < i := by omega
      exact (congrArg (fun j ↦ iteratedDeriv j (f x) 0) h₁).trans
        ((hjet _ x).symm.trans (hlow _ h₂))
  rw [hjet, show f (T.val x) = (fun z ↦ m z * f x (q * z)) by exact funext (hT x),
    iteratedDeriv_mul_dilation_at_zero m (f x) q _ hm (hf x) hlower, hjet]
  simp only [Nat.mul_add, pow_add, pow_mul, mul_assoc]

end RiemannMasullo
