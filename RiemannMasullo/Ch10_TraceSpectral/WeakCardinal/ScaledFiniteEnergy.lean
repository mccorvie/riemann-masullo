module

public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.FiniteInterpolation
public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.GramScale
import Mathlib.Tactic

/-! A common Haar rescaling of two finite Grams gives a reciprocal factor in the energy. -/

@[expose] public noncomputable section
open scoped InnerProductSpace Matrix
namespace RiemannMasullo.WeakCardinal

open Classical in
theorem finiteRieszGramEnergy_of_scaledGrams {J H V : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (L : H →L[ℂ] V) (f : J → StrongDual ℂ H)
    (j : J) (E : Finset J) (hj : j ∈ E) (a : ℝ) (ha : 0 < a) (A B : Matrix E E ℂ)
    (hA : IsUnit A.det)
    (hG : Matrix.gram ℂ (fun i : E ↦ (InnerProductSpace.toDual ℂ H).symm (f i.val)) = (a:ℂ) • A)
    (hW : Matrix.gram ℂ (fun i : E ↦ L ((InnerProductSpace.toDual ℂ H).symm (f i.val))) = (a:ℂ) • B) :
    let c (i : E) := A⁻¹ i ⟨j,hj⟩
    finiteRieszGramEnergy L f j E = a⁻¹ * (star c ⬝ᵥ B *ᵥ c).re := by
  classical
  intro c
  let u (i : E) := (InnerProductSpace.toDual ℂ H).symm (f i.val)
  let : Invertible (a:ℂ) := invertibleOfNonzero (Complex.ofReal_ne_zero.mpr ha.ne')
  have hinv : (Matrix.gram ℂ u)⁻¹ = (a:ℂ)⁻¹ • A⁻¹ := by
    rw [hG,Matrix.inv_smul _ _ hA,invOf_eq_inv]
  have hc : (fun i : E ↦ (Matrix.gram ℂ u)⁻¹ i ⟨j,hj⟩) = (a:ℂ)⁻¹ • c := by
    rw [hinv]
    rfl
  simp only [finiteRieszGramEnergy,dite_eq_left hj]
  change (star (fun i : E ↦ (Matrix.gram ℂ u)⁻¹ i ⟨j,hj⟩) ⬝ᵥ
    Matrix.gram ℂ (L ∘ u) *ᵥ (fun i : E ↦ (Matrix.gram ℂ u)⁻¹ i ⟨j,hj⟩)).re = _
  rw [hc,show Matrix.gram ℂ (L ∘ u) = (a:ℂ) • B from hW]
  exact weakForm_haarScale B c a ha

private def subsetDecEq {J : Type*} (E : Finset J) : DecidableEq E := by
  classical
  exact inferInstance

open Classical in
theorem finiteRieszGramEnergy_of_scaledGrams_withDecEq {J H V : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (L : H →L[ℂ] V) (f : J → StrongDual ℂ H)
    (j : J) (E : Finset J) [dE : DecidableEq E] (hj : j ∈ E) (a : ℝ) (ha : 0 < a) (A B : Matrix E E ℂ)
    (hA : IsUnit A.det)
    (hG : Matrix.gram ℂ (fun i : E ↦ (InnerProductSpace.toDual ℂ H).symm (f i.val)) = (a:ℂ) • A)
    (hW : Matrix.gram ℂ (fun i : E ↦ L ((InnerProductSpace.toDual ℂ H).symm (f i.val))) = (a:ℂ) • B) :
    let c (i : E) := A⁻¹ i ⟨j,hj⟩
    finiteRieszGramEnergy L f j E = a⁻¹ * (star c ⬝ᵥ B *ᵥ c).re := by
  have hed : dE = subsetDecEq E := Subsingleton.elim _ _
  subst dE
  exact finiteRieszGramEnergy_of_scaledGrams L f j E hj a ha A B hA hG hW

end RiemannMasullo.WeakCardinal
