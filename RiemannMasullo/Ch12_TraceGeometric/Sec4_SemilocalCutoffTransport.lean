module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Star.Unitary
import Mathlib.Tactic.Group

/-!
# Algebraic conjugation identities

These monoid lemmas are motivated by the sharp cutoff in Masullo, Theorem 12.4.1.1,
pp. 515–517. In the rational unit-invariant model, the periodization factors are
`(1 - p⁻¹ᐟ² Dₚ)⁻¹`, where `Dₚ` is the normalized dilation by `p`, and Fourier conjugation
reverses the dilations. See Connes–Consani–Moscovici, *Zeta zeros and prolate wave operators*,
§4.2, (44)–(47) and (iii).
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

/-- Let `G` be the product of a list of units that commute with each other and with
each other's adjoints. If conjugation by `F` sends each factor to its adjoint, then
`U = G * (star G)⁻¹` is unitary and `G * F * G⁻¹ = U * F`. Conjugation of any `M`
by `G * F * G⁻¹` thus factors through conjugation by `F` and then by `U`. -/
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

/-- If `P = U * Q * U⁻¹` and `A` commutes with `U`, conjugation of `P * M * A * P`
by `U⁻¹` gives `Q * (U⁻¹ * M * U) * A * Q`. -/
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
