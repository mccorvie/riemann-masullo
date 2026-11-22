module

public import RiemannMasullo.AppA_AlgebraicNT.Sec1

/-! # Appendix A.1: the printed restricted-product openness claim -/

@[expose] public noncomputable section

namespace RiemannMasullo

open scoped Classical RestrictedProduct

/-- Paper: Lemma A.1.1.2(5), p. 540. As printed: for any finite part of the index set,
an open box on that part times the distinguished subgroups on its complement is open in the
restricted product. `restrictedProduct_topology` requires open distinguished subgroups on the
complement. See ERRATA F1.
Deviation: The indexing preamble on p. 539 uses a Cartesian product where its conditions
require a partition into exceptional and ordinary indices. The partition on p. 540 is explicit. -/
def Printed.restrictedProduct_openBox : Prop :=
  ∀ (ι : Type) (G : ι → Type) [∀ i, CommGroup (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)] [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)]
    (K : (i : ι) → Subgroup (G i)) (I₀ : Finset ι),
    (∀ i ∈ I₀, K i = ⊥) →
    (∀ i ∉ I₀, IsCompact (K i : Set (G i)) ∧ IsOpen (K i : Set (G i))) →
    ∀ (J : Finset ι) (U : (i : ι) → Set (G i)), (∀ i ∈ J, IsOpen (U i)) →
      IsOpen {x : Πʳ i, [G i, K i] | (∀ i ∈ J, x i ∈ U i) ∧ ∀ i ∉ J, x i ∈ K i}

/-- Helper: in the restricted product over `Unit` with respect to the bottom filter, the
box `{x | ∀ i, x i ∈ ⊥}` is not open. -/
private lemma restrictedProduct_openBox_false_aux (𝓕 : Filter Unit) (h𝓕 : 𝓕 = ⊥) :
    ¬ IsOpen {x : Πʳ _ : Unit, [Multiplicative ℝ, ((⊥ : Subgroup (Multiplicative ℝ)) : Set _)]_[𝓕] |
      ∀ i, x i ∈ (⊥ : Subgroup (Multiplicative ℝ))} := by
  subst h𝓕
  intro hO
  let f : ℝ → Πʳ _ : Unit, [Multiplicative ℝ, ((⊥ : Subgroup (Multiplicative ℝ)) : Set _)]_[⊥] :=
    fun t ↦ ⟨fun _ ↦ Multiplicative.ofAdd t, by simp⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_bot.mpr
    (continuous_pi fun _ ↦ continuous_ofAdd)
  have h0 := hO.preimage hf
  have hpre : f ⁻¹' {x : Πʳ _ : Unit, [Multiplicative ℝ,
      ((⊥ : Subgroup (Multiplicative ℝ)) : Set _)]_[⊥] |
      ∀ i, x i ∈ (⊥ : Subgroup (Multiplicative ℝ))} = ({0} : Set ℝ) := by
    ext t
    change (∀ _ : Unit, Multiplicative.ofAdd t ∈ (⊥ : Subgroup (Multiplicative ℝ))) ↔ t = 0
    simp [Subgroup.mem_bot]
  rw [hpre] at h0
  exact not_isOpen_singleton (0 : ℝ) h0

/-- Paper: Lemma A.1.1.2(5), p. 540. Take a single factor `Multiplicative ℝ`, with
that index in I₀ and its distinguished subgroup trivial. Take J empty. The restricted
product is homeomorphic to ℝ and the box corresponds to the non-open singleton `{0}`. -/
theorem Printed.restrictedProduct_openBox_false : ¬ Printed.restrictedProduct_openBox := by
  intro h
  have := h Unit (fun _ ↦ Multiplicative ℝ) (fun _ ↦ ⊥) {()} (fun _ _ ↦ rfl)
    (fun i hi ↦ absurd (Finset.mem_singleton.mpr rfl) hi) ∅ (fun _ ↦ Set.univ) (by simp)
  apply restrictedProduct_openBox_false_aux _ Filter.cofinite_eq_bot
  simpa using this

end RiemannMasullo
