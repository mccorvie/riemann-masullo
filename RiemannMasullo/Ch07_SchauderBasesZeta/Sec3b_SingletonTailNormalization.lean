module

public import RiemannMasullo.Ch02_AdelicTheta.Sec2a
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion

/-! # Normalizing one-prime valuation-ball terms

A unit translate of the integer indicator gives the required finite ball.
Rescaling the archimedean coefficient by the same unit restores the original
ball term while returning the unshifted coefficient to the target radius.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain NumberField Set
open scoped NumberField.AdeleRing

namespace RiemannMasullo

/-- A multiplicative translate of the integer-tail insertion has the prescribed finite ball.
The inverse translation of the old coordinate is explicit in the evaluation formula. -/
private theorem singleton_translate_standardTail_apply
    (v : HeightOneSpectrum (𝓞 ℚ)) (j : ℤ)
    (d : (SAdeleRing ℚ {v})ˣ)
    (hd : Valued.v (d.val.2 ⟨v, Finset.mem_singleton_self v⟩) = WithZero.exp (-j))
    (b : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅))) (x : SAdeleRing ℚ {v}) :
    schwartzBruhatUnitTranslate d
        (sAdeleSchwartzTransition ℚ (Finset.empty_subset {v}) b) (Multiplicative.ofAdd x) =
      if Valued.v (x.2 ⟨v, Finset.mem_singleton_self v⟩) ≤ WithZero.exp (-j) then
        b (Multiplicative.ofAdd (d.inv.1 * x.1, fun w ↦ (Finset.notMem_empty w.val w.property).elim))
      else 0 := by
  classical
  let w : ({v} : Finset (HeightOneSpectrum (𝓞 ℚ))) := ⟨v, Finset.mem_singleton_self v⟩
  let : Subsingleton ({v} : Finset (HeightOneSpectrum (𝓞 ℚ))) :=
    Finset.card_le_one_iff_subsingleton_coe.mp (by simp)
  rw [schwartzBruhatUnitTranslate_apply, sAdeleSchwartzTransition_apply]
  have hball : (∀ i : ({v} : Finset (HeightOneSpectrum (𝓞 ℚ))), i.val ∉ (∅ : Finset _) →
      (d.inv * x).2 i ∈ i.val.adicCompletionIntegers ℚ) ↔
      Valued.v (x.2 w) ≤ WithZero.exp (-j) := by
    have hlocal : (d.inv * x).2 w ∈ v.adicCompletionIntegers ℚ ↔
        Valued.v (x.2 w) ≤ WithZero.exp (-j) := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have hinv : d.inv.2 w = (d.val.2 w)⁻¹ := eq_inv_of_mul_eq_one_left
        (congrArg (fun z : SAdeleRing ℚ {v} ↦ z.2 w) d.inv_val)
      change Valued.v (d.inv.2 w * x.2 w) ≤ 1 ↔ _
      rw [hinv, map_mul, map_inv₀, hd, inv_mul_le_iff₀ WithZero.exp_pos, mul_one]
    exact ⟨fun h ↦ hlocal.mp (h w (by simp)), fun h i _ ↦ (Subsingleton.elim w i) ▸ hlocal.mpr h⟩
  refine if_congr hball ?_ rfl
  apply congrArg (fun z : SAdeleRing ℚ ∅ ↦ b (Multiplicative.ofAdd z))
  exact Prod.ext rfl (Subsingleton.elim _ _)

/-- Paper: Definition 7.3.2.3(1), pp. 354–355, and (11.2.1.6), p. 488.
A single valuation-ball term of the product band is a translate of an
integer-tail insertion with its archimedean coefficient at radius `B`.
Deviation: Work over the rationals at one finite place and state the
rescaling on test representatives. -/
theorem singleton_normalize_standardTail
    (v : HeightOneSpectrum (𝓞 ℚ)) (j : ℤ) (B r : ℝ) (hr : 0 < r)
    (d : (SAdeleRing ℚ {v})ˣ)
    (hval : Valued.v (d.val.2 ⟨v, Finset.mem_singleton_self v⟩) = WithZero.exp (-j))
    (hnorm : ‖d.val.1 Rat.infinitePlace‖ = r)
    (a : SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ)))
    (ha : tsupport a.val ⊆ {x | ‖x.toAdd Rat.infinitePlace‖ ≤ B * r}) :
    ∃ b : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)),
      (∀ x : SAdeleRing ℚ {v}, schwartzBruhatUnitTranslate d
          (sAdeleSchwartzTransition ℚ (Finset.empty_subset {v}) b) (Multiplicative.ofAdd x) =
        if Valued.v (x.2 ⟨v, Finset.mem_singleton_self v⟩) ≤ WithZero.exp (-j) then
          a (Multiplicative.ofAdd x.1) else 0) ∧
      tsupport b.val ⊆ {x | ‖x.toAdd.1 Rat.infinitePlace‖ ≤ B} := by
  classical
  let A := InfiniteAdeleRing ℚ
  let D := (i : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) → i.val.adicCompletion ℚ
  let : Unique D := uniqueOfSubsingleton 0
  let e₀ : SAdeleRing ℚ ∅ ≃ₜ A := Homeomorph.prodUnique A D
  have hd : d.val.1 * d.inv.1 = (1 : A) := congrArg Prod.fst d.val_inv
  have hi : d.inv.1 * d.val.1 = (1 : A) := congrArg Prod.fst d.inv_val
  let e₁ : A ≃ₜ A :=
    { toFun := (d.val.1 * ·)
      invFun := (d.inv.1 * ·)
      left_inv := fun x ↦ by
        change d.inv.1 * (d.val.1 * x) = x
        rw [← mul_assoc, hi, one_mul]
      right_inv := fun x ↦ by
        change d.val.1 * (d.inv.1 * x) = x
        rw [← mul_assoc, hd, one_mul]
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  let e : Multiplicative (SAdeleRing ℚ ∅) ≃ₜ* Multiplicative A :=
    ContinuousMulEquiv.mk' (e₀.trans e₁) fun x y ↦ by
      change Multiplicative.ofAdd (d.val.1 * (x.toAdd.1 + y.toAdd.1)) = _
      exact congrArg Multiplicative.ofAdd (mul_add _ _ _)
  let : T2Space (Multiplicative A) := inferInstanceAs (T2Space ((u : InfinitePlace ℚ) → u.Completion))
  let : LocallyCompactSpace (Multiplicative A) := InfiniteAdeleRing.locallyCompactSpace ℚ
  let : T2Space (Multiplicative (SAdeleRing ℚ ∅)) := e.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative (SAdeleRing ℚ ∅)) :=
    e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  obtain ⟨P, hP⟩ := exists_schwartzBruhat_comp_equivCLM e
  refine ⟨P a, ?_, ?_⟩
  · intro x
    rw [singleton_translate_standardTail_apply v j d hval, hP]
    congr 1
    change a (Multiplicative.ofAdd (d.val.1 * (d.inv.1 * x.1))) = _
    rw [← mul_assoc, hd, one_mul]
  · have hclosed : IsClosed {x : Multiplicative (SAdeleRing ℚ ∅) |
        ‖x.toAdd.1 Rat.infinitePlace‖ ≤ B} :=
      isClosed_le ((continuous_apply Rat.infinitePlace).comp
        (continuous_fst.comp continuous_toAdd)).norm continuous_const
    apply closure_minimal _ hclosed
    intro x hx
    have hax : e x ∈ support a.val := by
      intro hzero
      exact hx ((hP a x).trans hzero)
    have hbound := ha (subset_tsupport a.val hax)
    change ‖d.val.1 Rat.infinitePlace * x.toAdd.1 Rat.infinitePlace‖ ≤ B * r at hbound
    rw [norm_mul, hnorm, mul_comm r] at hbound
    exact le_of_mul_le_mul_right hbound hr

end RiemannMasullo
