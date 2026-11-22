module
public import Mathlib.MeasureTheory.Integral.Pi

open Set MeasurableSpace
namespace MeasurableEquiv

variable {ι : Type*} [DecidableEq ι] (B : ι → Type*) [∀ v, MeasurableSpace (B v)]
  {S T : Finset ι} (h : Disjoint S T) {x : (v : S) → B v} {y : (v : T) → B v} {v : ι}

public theorem piFinsetUnion_left (hv : v ∈ S) (hR : v ∈ S ∪ T) :
    piFinsetUnion B h (x, y) ⟨v, hR⟩ = x ⟨v, hv⟩ :=
  Equiv.piFinsetUnion_left B h hv hR

public theorem piFinsetUnion_right (hv : v ∈ T) (hR : v ∈ S ∪ T) :
    piFinsetUnion B h (x, y) ⟨v, hR⟩ = y ⟨v, hv⟩ :=
  Equiv.piFinsetUnion_right B h hv hR

end MeasurableEquiv

namespace MeasureTheory

/-- A product of two finite product measures is determined by its coordinate rectangles. -/
public theorem Measure.prod_pi_eq {ι κ : Type*} [Fintype ι] [Fintype κ] {A : ι → Type*} {B : κ → Type*}
    [∀ i, MeasurableSpace (A i)] [∀ j, MeasurableSpace (B j)]
    (μ : ∀ i, Measure (A i)) (ν : ∀ j, Measure (B j))
    [∀ i, SigmaFinite (μ i)] [∀ j, SigmaFinite (ν j)]
    {ρ : Measure (((i : ι) → A i) × ((j : κ) → B j))}
    (h : ∀ (U : ∀ i, Set (A i)) (V : ∀ j, Set (B j)), (∀ i, MeasurableSet (U i)) →
      (∀ j, MeasurableSet (V j)) → ρ (univ.pi U ×ˢ univ.pi V) = (∏ i, μ i (U i)) * ∏ j, ν j (V j)) :
    (Measure.pi μ).prod (Measure.pi ν) = ρ := by
  apply Measure.prod_eq_generateFrom
    (generateFrom_eq_pi (fun _ ↦ generateFrom_measurableSet) (fun i ↦ (μ i).toFiniteSpanningSetsIn.isCountablySpanning))
    (generateFrom_eq_pi (fun _ ↦ generateFrom_measurableSet) (fun j ↦ (ν j).toFiniteSpanningSetsIn.isCountablySpanning))
    (IsPiSystem.pi fun _ ↦ isPiSystem_measurableSet) (IsPiSystem.pi fun _ ↦ isPiSystem_measurableSet)
    (Measure.FiniteSpanningSetsIn.pi fun i ↦ (μ i).toFiniteSpanningSetsIn)
    (Measure.FiniteSpanningSetsIn.pi fun j ↦ (ν j).toFiniteSpanningSetsIn)
  rintro _ ⟨U, hU, rfl⟩ _ ⟨V, hV, rfl⟩
  rw [Measure.pi_pi, Measure.pi_pi]
  exact h U V (mem_univ_pi.mp hU) (mem_univ_pi.mp hV)

/-- Splitting a finite set of integration variables into two disjoint parts separates
a function on one block from a product of functions on the other block. -/
public theorem integral_prod_piFinsetUnion {ι A : Type*} [DecidableEq ι] {B : ι → Type*}
    [MeasurableSpace A] [∀ i, MeasurableSpace (B i)] (μ : Measure A) (ν : ∀ i, Measure (B i))
    [SigmaFinite μ] [∀ i, SigmaFinite (ν i)] {S T : Finset ι} (hST : Disjoint S T)
    (H : A × ((v : S) → B v) → ℂ) (b : (v : T) → B v → ℂ)
    (f : A × ((v : ↥(S ∪ T)) → B v) → ℂ)
    (hf : ∀ a (x : (v : S) → B v) (y : (v : T) → B v),
      f (a, MeasurableEquiv.piFinsetUnion B hST (x, y)) = H (a, x) * ∏ v, b v (y v)) :
    (∫ p, f p ∂μ.prod (Measure.pi fun v : ↥(S ∪ T) ↦ ν v)) =
      (∫ p, H p ∂μ.prod (Measure.pi fun v : S ↦ ν v)) * ∏ v : T, ∫ x, b v x ∂ν v := by
  let e := (MeasurableEquiv.prodAssoc (α := A) (β := (v : S) → B v) (γ := (v : T) → B v)).trans
    ((MeasurableEquiv.refl A).prodCongr (MeasurableEquiv.piFinsetUnion B hST))
  let μS := Measure.pi fun v : S ↦ ν v
  let μT := Measure.pi fun v : T ↦ ν v
  have he : MeasurePreserving e ((μ.prod μS).prod μT) (μ.prod (Measure.pi fun v : ↥(S ∪ T) ↦ ν v)) :=
    ((MeasurePreserving.id μ).prod (measurePreserving_piFinsetUnion hST ν)).comp
      (measurePreserving_prodAssoc μ μS μT)
  rw [← he.integral_comp' f]
  change (∫ p : (A × _) × _, f (p.1.1, MeasurableEquiv.piFinsetUnion B hST (p.1.2, p.2))
    ∂(μ.prod μS).prod μT) = _
  simp_rw [hf]
  rw [integral_prod_mul (μ := μ.prod μS) (ν := μT) H (fun y ↦ ∏ v, b v (y v))]
  exact congrArg (_ * ·) (integral_fintype_prod_eq_prod b)

end MeasureTheory
