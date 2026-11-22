module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import RiemannMasullo.ForMathlib.Analysis.Normed.Operator.AbsolutelySumming.Factorization
import Mathlib.Analysis.InnerProductSpace.Dual
import RiemannMasullo.ForMathlib.Topology.Algebra.InfiniteSum.Real

/-! # Nuclear series for a composite of three absolutely summing operators -/

public noncomputable section
open Set Filter Topology

namespace RiemannMasullo
namespace AbsolutelySumming

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Precomposing a 2-summing map with a Hilbert-space operator sends Hilbert bases
to square-summable families. -/
private theorem summable_basis {ι : Type*} (b : HilbertBasis ι ℂ H)
    (T : X →L[ℂ] Y) (d : H →L[ℂ] X) {C : ℝ}
    (h : HasQuadraticBound T C) : Summable (fun i ↦ ‖T (d (b i))‖ ^ 2) := by
  classical
  apply summable_of_sum_le (c := C * ‖d‖ ^ 2) (fun i ↦ sq_nonneg _)
  intro s
  let e := Fintype.equivFin ↥s
  have hweak (φ : StrongDual ℂ X) (hφ : ‖φ‖ ≤ 1) :
      ∑ i ∈ s, ‖φ (d (b i))‖ ^ 2 ≤ ‖d‖ ^ 2 := by
    let y := (InnerProductSpace.toDual ℂ H).symm (φ.comp d)
    have hy : ‖y‖ ≤ ‖d‖ := ((InnerProductSpace.toDual ℂ H).symm.norm_map _).trans_le
      ((φ.opNorm_comp_le d).trans (mul_le_of_le_one_left (norm_nonneg _) hφ))
    have heq (i : ι) : ‖φ (d (b i))‖ = ‖inner ℂ (b i) y‖ := by
      change ‖(φ.comp d) (b i)‖ = _
      rw [← InnerProductSpace.toDual_symm_apply, norm_inner_symm]
    simp only [heq]
    exact (b.orthonormal.sum_inner_products_le y).trans ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hy)
  have hf (f : ι → ℝ) : ∑ i, f (e.symm i) = ∑ i ∈ s, f i :=
    (e.symm.sum_comp (fun i : s ↦ f i)).trans (Finset.sum_subtype s (fun _ ↦ Iff.rfl) f).symm
  have h' := h _ (fun i ↦ d (b (e.symm i))) _ (sq_nonneg ‖d‖)
    (fun φ hφ ↦ (hf (fun i ↦ ‖φ (d (b i))‖ ^ 2)).trans_le (hweak φ hφ))
  rwa [hf (fun i ↦ ‖T (d (b i))‖ ^ 2)] at h'

/-- Parseval and Bessel transfer the square-summability bound to the adjoint. -/
private theorem summable_adjoint_basis {ι κ : Type*} (b : HilbertBasis ι ℂ H)
    (c : HilbertBasis κ ℂ K) (T : H →L[ℂ] K) (h : Summable (fun j ↦ ‖T (b j)‖ ^ 2)) :
    Summable (fun i ↦ ‖T.adjoint (c i)‖ ^ 2) := by
  classical
  let a (i : κ) (j : ι) := ‖inner ℂ (b j) (T.adjoint (c i))‖ ^ 2
  have row (i : κ) : HasSum (a i) (‖T.adjoint (c i)‖ ^ 2) := by
    have h := lp.hasSum_norm (p := 2) (by norm_num) (b.repr (T.adjoint (c i)))
    simpa [a, b.repr_apply_apply] using h
  apply summable_of_sum_le (c := ∑' j, ‖T (b j)‖ ^ 2) (fun i ↦ sq_nonneg _)
  intro s
  have hs := hasSum_sum (s := s) (fun i _ ↦ row i)
  rw [← hs.tsum_eq]
  apply hs.summable.tsum_le_tsum _ h
  intro j
  simpa only [a, T.adjoint_inner_right, norm_inner_symm (T (b j))] using
    (c.orthonormal.sum_inner_products_le (s := s) (T (b j)))

/-- Scale each vector in a sequence to norm at most a prescribed positive null sequence. -/
private theorem tendsto_scaled {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : ℕ → V) {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n) (hlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n ↦ ((r n : ℂ) / (‖f n‖ : ℂ)) • f n) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ norm_nonneg _) fun n ↦ ?_
  by_cases h : f n = 0
  · simpa [h] using hr n
  · simp only [norm_smul, norm_div, Complex.norm_of_nonneg (hr n),
      Complex.norm_real, norm_norm, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr h), le_refl]

private theorem rescale_nat_series (φ : ℕ → StrongDual ℂ X) (y : ℕ → Y)
    (T : X → Y) (h : Summable (fun n ↦ ‖φ n‖ * ‖y n‖))
    (hT : ∀ x, HasSum (fun n ↦ φ n x • y n) (T x)) :
    ∃ (c : ℕ → ℂ) (ψ : ℕ → StrongDual ℂ X) (v : ℕ → Y),
      Summable (fun n ↦ ‖c n‖) ∧ Tendsto ψ atTop (𝓝 0) ∧ Tendsto v atTop (𝓝 0) ∧
        ∀ x, HasSum (fun n ↦ (c n * ψ n x) • v n) (T x) := by
  obtain ⟨d, hd, hlim, hsum⟩ := exists_pos_tendsto_zero_summable_div h fun n ↦ by positivity
  let r (n : ℕ) := √(d n)
  have hr (n : ℕ) : 0 ≤ r n := Real.sqrt_nonneg _
  have hrlim : Tendsto r atTop (𝓝 0) := by simpa [r] using hlim.sqrt
  let c (n : ℕ) : ℂ := (‖φ n‖ * ‖y n‖ / d n : ℝ)
  refine ⟨c, _, _, ?_, tendsto_scaled φ hr hrlim, tendsto_scaled y hr hrlim, fun x ↦ ?_⟩
  · apply hsum.congr
    intro n
    exact (Complex.norm_of_nonneg (div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hd n).le)).symm
  · apply (hT x).congr_fun
    intro n
    by_cases hφ : φ n = 0
    · simp [hφ]
    by_cases hy : y n = 0
    · simp [hy]
    simp only [smul_apply, smul_eq_mul, smul_smul]
    congr 1
    have hφ' : (‖φ n‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hφ)
    have hy' : (‖y n‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)
    have hd' : (d n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hd n).ne'
    have hr' : (r n : ℂ) ^ 2 = (d n : ℂ) := by exact_mod_cast Real.sq_sqrt (hd n).le
    simp only [c, Complex.ofReal_div, Complex.ofReal_mul]
    field_simp
    linear_combination (φ n x) * hr'

/-- A summable family of rank-one terms can be enumerated on its countable support
and rescaled to have two norm-null vector factors. -/
private theorem rescale_series {ι : Type*} (φ : ι → StrongDual ℂ X) (y : ι → Y)
    (T : X → Y) (h : Summable (fun i ↦ ‖φ i‖ * ‖y i‖))
    (hT : ∀ x, HasSum (fun i ↦ φ i x • y i) (T x)) :
    ∃ (c : ℕ → ℂ) (ψ : ℕ → StrongDual ℂ X) (v : ℕ → Y),
      Summable (fun n ↦ ‖c n‖) ∧ Tendsto ψ atTop (𝓝 0) ∧ Tendsto v atTop (𝓝 0) ∧
        ∀ x, HasSum (fun n ↦ (c n * ψ n x) • v n) (T x) := by
  classical
  let S := Function.support (fun i ↦ ‖φ i‖ * ‖y i‖)
  let e : S ↪ ℕ := h.countable_support.toEncodable.encode'
  let ψ := Function.extend e (fun i : S ↦ φ i) 0
  let v := Function.extend e (fun i : S ↦ y i) 0
  apply rescale_nat_series ψ v T
  · apply (e.injective.summable_iff (f := fun n ↦ ‖ψ n‖ * ‖v n‖) (fun n hn ↦ ?_)).mp
    · simpa only [ψ, v, Function.comp_def, e.injective.extend_apply] using h.subtype (fun i ↦ i ∈ S)
    · simp [ψ, Function.extend_apply' _ _ n hn]
  · intro x
    apply (e.injective.hasSum_iff (f := fun n ↦ ψ n x • v n) (fun n hn ↦ ?_)).mp
    · simp only [ψ, v, Function.comp_def, e.injective.extend_apply]
      apply (hasSum_subtype_iff_of_support_subset (s := S) ?_).mpr (hT x)
      intro i hi
      change ‖φ i‖ * ‖y i‖ ≠ 0
      intro hzero
      apply hi
      rcases mul_eq_zero.mp hzero with hz | hz
      · simp [norm_eq_zero.mp hz]
      · simp [norm_eq_zero.mp hz]
    · simp [ψ, Function.extend_apply' _ _ n hn]

/-- The composite of three absolutely summing Banach-space maps admits a nuclear
series with summable coefficients and norm-null functionals and vectors. -/
theorem exists_series_comp_three {X₂ X₃ : Type*}
    [NormedAddCommGroup X₂] [NormedSpace ℂ X₂] [CompleteSpace X₂]
    [NormedAddCommGroup X₃] [NormedSpace ℂ X₃] [CompleteSpace X]
    (T₁ : X →L[ℂ] Y) (T₂ : X₂ →L[ℂ] X) (T₃ : X₃ →L[ℂ] X₂)
    (s₁ : ∃ C, 0 ≤ C ∧ HasBound T₁ C) (s₂ : ∃ C, 0 ≤ C ∧ HasBound T₂ C)
    (s₃ : ∃ C, 0 ≤ C ∧ HasBound T₃ C) :
    ∃ (c : ℕ → ℂ) (φ : ℕ → StrongDual ℂ X₃) (y : ℕ → Y),
      Summable (fun n ↦ ‖c n‖) ∧ Tendsto φ atTop (𝓝 0) ∧ Tendsto y atTop (𝓝 0) ∧
        ∀ x, HasSum (fun n ↦ (c n * φ n x) • y n) (T₁ (T₂ (T₃ x))) := by
  obtain ⟨C₁, hC₁, h₁⟩ := s₁
  obtain ⟨C₂, hC₂, h₂⟩ := s₂
  obtain ⟨C₃, hC₃, h₃⟩ := s₃
  obtain ⟨H₂, _, _, _, a₂, d₂, hd₂, ha₂⟩ := factor T₂ hC₂ h₂
  obtain ⟨H₃, _, _, _, a₃, d₃, hd₃, _⟩ := factor T₃ hC₃ h₃
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H₂)
  obtain ⟨κ, c, _⟩ := exists_hilbertBasis (𝕜 := ℂ) (E := H₃)
  let U := a₂.comp d₃
  let V := T₁.comp d₂
  have hU : Summable (fun j ↦ ‖U (c j)‖ ^ 2) :=
    summable_basis c a₂ d₃ (C := 1) fun n x M _ hx ↦ (ha₂ n x M hx).trans_eq (one_mul M).symm
  have hV : Summable (fun i ↦ ‖V (b i)‖ ^ 2) :=
    summable_basis b T₁ d₂ (C := C₁ ^ 2) fun _ x _ ↦ sum_sq_le T₁ hC₁ h₁ x
  let φ (i : ι) := (innerSL ℂ (U.adjoint (b i))).comp a₃
  have hφ (i : ι) : ‖φ i‖ ≤ ‖U.adjoint (b i)‖ * ‖a₃‖ := by
    simpa only [innerSL_apply_norm] using (innerSL ℂ (U.adjoint (b i))).opNorm_comp_le a₃
  apply rescale_series φ (fun i ↦ V (b i))
  · have hA := summable_adjoint_basis c b U hU
    refine ((hA.add hV).mul_right ‖a₃‖).of_nonneg_of_le (fun i ↦ by positivity) fun i ↦ ?_
    refine (mul_le_mul_of_nonneg_right (hφ i) (norm_nonneg _)).trans ?_
    have hsq := sq_nonneg (‖U.adjoint (b i)‖ - ‖V (b i)‖)
    have hprod := mul_nonneg (norm_nonneg (U.adjoint (b i))) (norm_nonneg (V (b i)))
    calc
      _ = (‖U.adjoint (b i)‖ * ‖V (b i)‖) * ‖a₃‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith only [hsq, hprod]) (norm_nonneg _)
  · intro x
    have heq : V (U (a₃ x)) = T₁ (T₂ (T₃ x)) := by
      change T₁ (d₂ (a₂ (d₃ (a₃ x)))) = _
      rw [hd₂, hd₃]
    rw [← heq]
    refine (V.hasSum (b.hasSum_repr (U (a₃ x)))).congr_fun fun i ↦ ?_
    rw [map_smul, b.repr_apply_apply]
    change inner ℂ (U.adjoint (b i)) (a₃ x) • _ = _
    rw [U.adjoint_inner_left]

end AbsolutelySumming
end RiemannMasullo
