module

public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.FiniteGramCardinal
public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Finite interpolation by the Riesz representatives of a total family of coordinates. -/

@[expose] public noncomputable section

open Filter Set
open scoped InnerProductSpace Matrix Topology

namespace RiemannMasullo.WeakCardinal

variable {J H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The minimum-norm vector with the same finite coordinate data as the cardinal at `j`. -/
def finiteRieszCardinal (f : J → StrongDual ℂ H) (j : J) (E : Finset J) : H := by
  classical
  exact if hj : j ∈ E then finiteGramCardinal
    (fun i : E ↦ (InnerProductSpace.toDual ℂ H).symm (f i.val)) ⟨j, hj⟩ else 0

private theorem riesz_linearIndependent (x : J → H) (f : J → StrongDual ℂ H)
    (hb : IsSpectralMarkushevichBasis x f) :
    LinearIndependent ℂ (fun k ↦ (InnerProductSpace.toDual ℂ H).symm (f k)) := by
  classical
  let u (k : J) := (InnerProductSpace.toDual ℂ H).symm (f k)
  have hval (i k : J) : ⟪u i, x k⟫_ℂ = if i = k then 1 else 0 := by
    rw [InnerProductSpace.toDual_symm_apply]
    split
    · rename_i h
      subst i
      exact hb.1 k
    · rename_i h
      exact hb.2.1 k i (Ne.symm h)
  have hu : LinearIndependent ℂ u := by
    apply LinearIndependent.of_pairwise_dual_eq_zero_one u
      (fun k ↦ (InnerProductSpace.toDual ℂ H (x k)).toLinearMap)
    · intro i k hik
      change ⟪x i, u k⟫_ℂ = 0
      rw [inner_eq_zero_symm, hval, ite_eq_right (Ne.symm hik)]
    · intro i
      change ⟪x i, u i⟫_ℂ = 1
      rw [← inner_conj_symm, hval, ite_eq_left rfl]
      simp
  exact hu

open scoped Classical in
/-- The finite inverse column interpolates the specified quotient coordinates. -/
theorem finiteRieszCardinal_apply (x : J → H) (f : J → StrongDual ℂ H)
    (hb : IsSpectralMarkushevichBasis x f) {j i : J} {E : Finset J} (hj : j ∈ E) (hi : i ∈ E) :
    f i (finiteRieszCardinal f j E) = if i = j then 1 else 0 := by
  let u (k : E) := (InnerProductSpace.toDual ℂ H).symm (f k.val)
  let iE : E := ⟨i, hi⟩
  let jE : E := ⟨j, hj⟩
  calc
    f i (finiteRieszCardinal f j E) = ⟪u iE, finiteGramCardinal u jE⟫_ℂ := by
      rw [finiteRieszCardinal, dite_eq_left hj]
      exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (y := f i) (x := finiteGramCardinal u jE)).symm
    _ = if iE = jE then 1 else 0 :=
      inner_finiteGramCardinal u ((riesz_linearIndependent x f hb).comp _ Subtype.val_injective) _ _
    _ = _ := by by_cases h : i = j <;> simp [iE, jE, h]

/-- A coordinate orthogonal to the chosen rows vanishes on the finite cardinal. -/
theorem finiteRieszCardinal_apply_eq_zero (f : J → StrongDual ℂ H) {j i : J} {E : Finset J}
    (hoff : ∀ k ∈ E, f i ((InnerProductSpace.toDual ℂ H).symm (f k)) = 0) :
    f i (finiteRieszCardinal f j E) = 0 := by
  classical
  by_cases hj : j ∈ E
  · rw [finiteRieszCardinal, dite_eq_left hj, finiteGramCardinal, map_sum]
    exact Finset.sum_eq_zero fun k _ ↦ by simp [hoff k.val k.property]
  · simp [finiteRieszCardinal, hj]

/-- In a total biorthogonal system these finite Gram solves recover the full cardinal in norm.
No ordering, separation bound, or basis expansion is required. -/
theorem tendsto_finiteRieszCardinal (x : J → H) (f : J → StrongDual ℂ H)
    (hb : IsSpectralMarkushevichBasis x f) (j : J) :
    Tendsto (finiteRieszCardinal f j) atTop (𝓝 (x j)) := by
  classical
  let u (k : J) := (InnerProductSpace.toDual ℂ H).symm (f k)
  let V (E : Finset J) := Submodule.span ℂ (u '' (E : Set J))
  let dim (E : Finset J) : FiniteDimensional ℂ (V E) :=
    FiniteDimensional.span_of_finite ℂ (E.finite_toSet.image u)
  have hval (i k : J) : ⟪u i, x k⟫_ℂ = if i = k then 1 else 0 := by
    rw [InnerProductSpace.toDual_symm_apply]
    split
    · rename_i h
      subst i
      exact hb.1 k
    · rename_i h
      exact hb.2.1 k i (Ne.symm h)
  have hu : LinearIndependent ℂ u := riesz_linearIndependent x f hb
  have hd : ⊤ ≤ (⨆ E, V E).topologicalClosure := by
    apply (Submodule.topologicalClosure_eq_top_iff.mpr ?_).ge
    rw [Submodule.eq_bot_iff]
    intro y hy
    have he : ContinuousLinearMap.apply ℂ ℂ y = 0 := by
      apply ContinuousLinearMap.ext_on hb.2.2.2
      rintro _ ⟨i, rfl⟩
      have hi : u i ∈ V {i} := Submodule.subset_span ⟨i, Finset.mem_singleton_self i, rfl⟩
      change f i y = 0
      exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℂ)).symm.trans
        ((Submodule.mem_orthogonal _ _).mp hy _ (le_iSup V {i} hi))
    exact inner_self_eq_zero.mp (DFunLike.congr_fun he (InnerProductSpace.toDual ℂ H y))
  have hmono : Monotone V := fun _ _ h ↦ Submodule.span_mono (image_mono h)
  apply (Submodule.starProjection_tendsto_self V hmono (x j) hd).congr'
  filter_upwards [eventually_ge_atTop ({j} : Finset J)] with E hE
  have hj : j ∈ E := hE (Finset.mem_singleton_self j)
  rw [finiteRieszCardinal, dite_eq_left hj]
  let uE (i : E) := u i.val
  let k : E := ⟨j, hj⟩
  change (V E).starProjection (x j) = finiteGramCardinal uE k
  have hmem (i : E) : uE i ∈ V E := Submodule.subset_span ⟨i.val, i.property, rfl⟩
  apply (V E).eq_starProjection_of_mem_orthogonal
  · exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (hmem i)
  · rw [Submodule.mem_orthogonal]
    intro y hy
    change y ∈ Submodule.span ℂ (u '' (E : Set J)) at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      rw [inner_sub_right, hval]
      have h := inner_finiteGramCardinal uE (hu.comp _ Subtype.val_injective) (⟨i, hi⟩ : E) k
      change (if i = j then (1 : ℂ) else 0) - ⟪uE ⟨i, hi⟩, finiteGramCardinal uE k⟫_ℂ = 0
      rw [h]
      simp [k]
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
    | smul a y _ hy => rw [inner_smul_left, hy, mul_zero]

/-- Removing rows orthogonal to all retained rows leaves the minimum unchanged when their
target coordinates vanish. The finite vector is compared inside the span of the larger system. -/
theorem finiteRieszCardinal_eq_of_subset_orthogonal (x : J → H) (f : J → StrongDual ℂ H)
    (hb : IsSpectralMarkushevichBasis x f) {j : J} {E S : Finset J} (hES : E ⊆ S) (hj : j ∈ E)
    (hoff : ∀ i ∈ S, i ∉ E → ∀ k ∈ E, f i ((InnerProductSpace.toDual ℂ H).symm (f k)) = 0) :
    finiteRieszCardinal f j E = finiteRieszCardinal f j S := by
  classical
  let v := finiteRieszCardinal f j E - finiteRieszCardinal f j S
  have hz (i : J) (hi : i ∈ S) : f i v = 0 := by
    change f i (_ - _) = 0
    rw [map_sub, finiteRieszCardinal_apply x f hb (hES hj) hi]
    by_cases he : i ∈ E
    · rw [finiteRieszCardinal_apply x f hb hj he, sub_self]
    · have hij : i ≠ j := fun h ↦ he (h ▸ hj)
      rw [ite_eq_right hij, finiteRieszCardinal_apply_eq_zero f (hoff i hi he), sub_zero]
  have horth (T : Finset J) (hjT : j ∈ T) (hTS : T ⊆ S) :
      ⟪finiteRieszCardinal f j T, v⟫_ℂ = 0 := by
    rw [finiteRieszCardinal, dite_eq_left hjT, finiteGramCardinal, sum_inner]
    exact Finset.sum_eq_zero fun k _ ↦ by rw [inner_smul_left, InnerProductSpace.toDual_symm_apply, hz k (hTS k.property), mul_zero]
  have hv : ⟪v, v⟫_ℂ = 0 := by
    change ⟪_ - _, v⟫_ℂ = 0
    rw [inner_sub_left, horth E hj hES, horth S (hES hj) Subset.rfl, sub_zero]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hv)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The positive finite quadratic form for the image of a cardinal. The inverse Gram is
formed before applying `L`; the middle Gram uses the images of the same Riesz vectors. -/
def finiteRieszGramEnergy (L : H →L[ℂ] V) (f : J → StrongDual ℂ H) (j : J) (E : Finset J) : ℝ := by
  classical
  let u (i : E) := (InnerProductSpace.toDual ℂ H).symm (f i.val)
  exact if hj : j ∈ E then
    let c (i : E) := (Matrix.gram ℂ u)⁻¹ i ⟨j, hj⟩
    (star c ⬝ᵥ (Matrix.gram ℂ (L ∘ u)) *ᵥ c).re
  else 0

/-- Each finite energy is the squared norm of the image of the finite interpolant. -/
theorem finiteRieszGramEnergy_eq (L : H →L[ℂ] V) (f : J → StrongDual ℂ H) (j : J) (E : Finset J) :
    finiteRieszGramEnergy L f j E = ‖L (finiteRieszCardinal f j E)‖ ^ 2 := by
  classical
  by_cases h : j ∈ E
  · simpa only [finiteRieszGramEnergy, finiteRieszCardinal, dite_eq_left h] using
      (norm_sq_map_finiteGramCardinal L (fun i : E ↦ (InnerProductSpace.toDual ℂ H).symm (f i.val)) ⟨j, h⟩).symm
  · simp [finiteRieszGramEnergy, finiteRieszCardinal, h]

/-- Cofinal finite Gram tests converge for every bounded readout, including readouts into a
weaker Hilbert norm. No monotonicity of the quadratic forms is assumed. -/
theorem tendsto_finiteRieszGramEnergy (x : J → H) (f : J → StrongDual ℂ H)
    (hb : IsSpectralMarkushevichBasis x f) (L : H →L[ℂ] V) (j : J) :
    Tendsto (finiteRieszGramEnergy L f j) atTop (𝓝 (‖L (x j)‖ ^ 2)) := by
  change Tendsto (fun E ↦ finiteRieszGramEnergy L f j E) _ _
  simpa only [finiteRieszGramEnergy_eq, Function.comp_apply] using
    ((L.continuous.tendsto (x j)).comp (tendsto_finiteRieszCardinal x f hb j)).norm.pow 2

end RiemannMasullo.WeakCardinal
