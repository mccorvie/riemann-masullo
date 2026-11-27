module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Star.Unitary
import Mathlib.Tactic.Group

/-!
# Transport of the unweighted semilocal cutoff

In the rational unit-invariant model, periodization is the product of the resolvents
`(1 - p⁻¹ᐟ² Dₚ)⁻¹`, where `Dₚ` is the normalized dilation by `p`. The real Fourier
transform reverses the dilations. The lemmas take the corresponding commutation and
reversal identities as hypotheses for any finite list of local factors.
-/

@[expose] public section

namespace RiemannMasullo.Isolated

private theorem star_list_prod_of_commute {G : Type*} [Group G] [StarMul G]
    (factors : List G) (h : ∀ x ∈ factors, ∀ y ∈ factors, Commute x y) :
    star factors.prod = (factors.map star).prod := by
  induction factors with
  | nil => simp
  | cons a factors ih =>
    have htail (x : G) (hx : x ∈ factors) (y : G) (hy : y ∈ factors) :=
      h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
    rw [List.prod_cons, star_mul, ih htail, List.map_cons, List.prod_cons]
    apply (Commute.list_prod_left _ _ ?_).eq
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    simpa only [Commute, SemiconjBy, star_mul] using congrArg star
      (h a (by simp) y (List.mem_cons_of_mem _ hy)).eq

/-- Paper: Theorem 12.4.1.1, pp. 515–517. The conjugating operator `U` for the sharp
frequency cutoff is unitary when periodization is a product of commuting invertible
operators and Fourier conjugation sends each factor to its adjoint.
Reconstruction: This is the operator identity behind the rational unit-invariant chart of
Connes–Consani–Moscovici, *Zeta zeros and prolate wave operators*, §4.2, (44)–(47) and (iii). -/
theorem semilocalCutoff_unitary_transport {R : Type*} [Monoid R] [StarMul R]
    (factors : List Rˣ) (F : Rˣ) (M : R)
    (hcomm : ∀ x ∈ factors, ∀ y ∈ factors, Commute x y)
    (hstar : ∀ x ∈ factors, ∀ y ∈ factors, Commute x (star y))
    (hF : ∀ x ∈ factors, F * x * F⁻¹ = star x) :
    let G := factors.prod
    let U := G * (star G)⁻¹
    let Fₛ := G * F * G⁻¹
    (U : R) ∈ unitary R ∧ Fₛ = U * F ∧
      (Fₛ : R) * M * ↑Fₛ⁻¹ = (U : R) * ((F : R) * M * ↑F⁻¹) * ↑U⁻¹ := by
  dsimp only
  let G := factors.prod
  have hGstar := star_list_prod_of_commute factors hcomm
  have hnormal : Commute G (star G) := by
    change Commute factors.prod (star factors.prod)
    rw [hGstar]
    apply Commute.list_prod_left
    intro x hx
    apply Commute.list_prod_right
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    exact hstar x hx z hz
  have hconj : F * G * F⁻¹ = star G := by
    change F * factors.prod * F⁻¹ = star factors.prod
    rw [hGstar]
    have hprod (xs : List Rˣ) (hx : ∀ x ∈ xs, F * x * F⁻¹ = star x) :
        F * xs.prod * F⁻¹ = (xs.map star).prod := by
      induction xs with
      | nil => simp
      | cons a xs ih =>
        simp only [List.prod_cons, List.map_cons]
        calc
          F * (a * xs.prod) * F⁻¹ = (F * a * F⁻¹) * (F * xs.prod * F⁻¹) := by group
          _ = star a * (xs.map star).prod := by
            rw [hx a (by simp), ih fun x h => hx x (List.mem_cons_of_mem _ h)]
    exact hprod factors hF
  let U := G * (star G)⁻¹
  have hunit : U ∈ unitary Rˣ :=
    (Unitary.mul_inv_mem_iff G (star G)).2 (by simpa only [star_star] using hnormal.eq.symm)
  have hU : G * F * G⁻¹ = U * F := by
    calc
      G * F * G⁻¹ = G * (F * G * F⁻¹)⁻¹ * F := by group
      _ = U * F := by rw [hconj]
  change (U : R) ∈ unitary R ∧ G * F * G⁻¹ = U * F ∧ _
  refine ⟨⟨?_, ?_⟩, hU, ?_⟩
  · exact congrArg Units.val hunit.1
  · exact congrArg Units.val hunit.2
  · change ((G * F * G⁻¹ : Rˣ) : R) * M * ↑(G * F * G⁻¹)⁻¹ =
      (U : R) * ((F : R) * M * ↑F⁻¹) * ↑U⁻¹
    rw [hU, mul_inv_rev]
    simp only [Units.val_mul, mul_assoc]

/-- Paper: Theorem 12.4.1.1, pp. 515–517. If the flat band projection is `Q` and the
semilocal band is its conjugate by the invertible transport `U`, the compression is carried to
the flat band by putting the inverse transport and transport around the position cutoff `M`.
This applies also to a flat band projection with the origin evaluation removed. -/
theorem semilocalCutoff_compression_transport {R : Type*} [Monoid R]
    (U : Rˣ) (Q M A : R) (hA : Commute (U : R) A) :
    let P := (U : R) * Q * ↑U⁻¹
    (↑U⁻¹ : R) * (P * M * A * P) * (U : R) = Q * ↑U⁻¹ * M * (U : R) * A * Q := by
  dsimp only
  calc
    (↑U⁻¹ : R) * ((↑U * Q * ↑U⁻¹) * M * A * (↑U * Q * ↑U⁻¹)) * ↑U =
        Q * ↑U⁻¹ * M * (A * ↑U) * Q := by
      simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]
    _ = Q * ↑U⁻¹ * M * ↑U * A * Q := by
      rw [← hA.eq]
      simp only [mul_assoc]

end RiemannMasullo.Isolated
