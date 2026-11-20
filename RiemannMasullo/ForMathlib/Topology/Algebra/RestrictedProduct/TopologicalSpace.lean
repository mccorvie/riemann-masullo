module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.RestrictedProduct.Units

/-!
# Finite changes and compact subsets of restricted products

The distinguished sets need only be compact and open away from finitely many indices.
-/

@[expose] public section

namespace RiemannMasullo

open Filter Function Set Topology RestrictedProduct
open scoped RestrictedProduct

variable {ι : Type*} {G : ι → Type*} [∀ i, TopologicalSpace (G i)]

/-- A coordinatewise continuous map into a restricted product is continuous if its
values lie in the distinguished sets on a fixed cofinite set of indices. -/
theorem continuous_restrictedProduct_of_uniform {X : Type*} [TopologicalSpace X]
    {A : (i : ι) → Set (G i)} {f : X → Πʳ i, [G i, A i]}
    (hc : ∀ i, Continuous (fun x ↦ f x i)) (hA : ∀ᶠ i in cofinite, ∀ x, f x i ∈ A i) :
    Continuous f := by
  let S := {i | ∀ x, f x i ∈ A i}
  let lift (x : X) : Πʳ i, [G i, A i]_[𝓟 S] := ⟨f x, fun _ hi ↦ hi x⟩
  exact (continuous_inclusion (le_principal_iff.mpr hA)).comp
    ((continuous_rng_of_principal_iff_forall (f := lift)).mpr hc)

/-- Imposing membership in distinguished open sets at any collection of coordinates
gives an open subset of the restricted product. -/
theorem isOpen_restrictedProduct_forall_mem {A : (i : ι) → Set (G i)} (t : Set ι)
    (ht : ∀ i ∈ t, IsOpen (A i)) :
    IsOpen {x : Πʳ i, [G i, A i] | ∀ i ∈ t, x i ∈ A i} := by
  classical
  simp_rw +instances [topologicalSpace_eq_iSup cofinite, isOpen_iSup_iff, isOpen_coinduced]
  intro S hS
  rw [le_principal_iff] at hS
  have h := (isOpen_set_pi (hS.inter_of_left t) (fun i hi ↦ ht i hi.2)).preimage
    (continuous_coe (R := G) (A := A) (𝓕 := 𝓟 S))
  convert h using 1
  ext x
  exact ⟨fun hx i hi ↦ hx i hi.2, fun hx i hi ↦
    if h : i ∈ S then x.2 h else hx i ⟨h, hi⟩⟩

/-- The units of a restricted product with open distinguished submonoids are
homeomorphic, coordinate by coordinate, to the restricted product of local units. -/
def restrictedProductUnitsEquiv [∀ i, Monoid (G i)] {S : ι → Type*}
    [∀ i, SetLike (S i) (G i)] [∀ i, SubmonoidClass (S i) (G i)]
    (B : (i : ι) → S i) (hB : ∀ i, IsOpen (B i : Set (G i))) :
    (Πʳ i, [G i, B i])ˣ ≃ₜ* (Πʳ i, [(G i)ˣ, (Submonoid.ofClass (B i)).units]) where
  __ := RestrictedProduct.unitsEquiv G (B := B)
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro x
    let s := {i | x.val i ∈ B i ∧ x.inv i ∈ B i}
    let V := {y : (Πʳ i, [G i, B i])ˣ | ∀ i ∈ s, y.val i ∈ B i ∧ y.inv i ∈ B i}
    have hs := isOpen_restrictedProduct_forall_mem s (fun i _ ↦ hB i)
    have hV : IsOpen V := by
      convert (hs.preimage Units.continuous_val).inter
        (hs.preimage Units.continuous_coe_inv) using 1
      ext y
      exact ⟨fun h ↦ ⟨fun i hi ↦ (h i hi).1, fun i hi ↦ (h i hi).2⟩,
        fun h i hi ↦ ⟨h.1 i hi, h.2 i hi⟩⟩
    apply ContinuousOn.continuousAt (s := V) _ (hV.mem_nhds fun _ hi ↦ hi)
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply continuous_restrictedProduct_of_uniform
    · intro i
      exact Units.continuous_iff.mpr
        ⟨(continuous_eval i).comp (Units.continuous_val.comp continuous_subtype_val),
          (continuous_eval i).comp (Units.continuous_coe_inv.comp continuous_subtype_val)⟩
    · exact (x.val.2.and x.inv.2).mono fun i hi y ↦ y.2 i hi
  continuous_invFun := by
    apply Units.continuous_iff.mpr
    exact ⟨mapAlong_continuous (fun i ↦ (G i)ˣ) G id tendsto_id
        (A₁ := fun i ↦ (Submonoid.ofClass (B i)).units) (A₂ := fun i ↦ B i) (fun _ ↦ Units.val)
        (.of_forall fun _ _ hx ↦ hx.1) (fun _ ↦ Units.continuous_val),
      mapAlong_continuous (fun i ↦ (G i)ˣ) G id tendsto_id
        (A₁ := fun i ↦ (Submonoid.ofClass (B i)).units) (A₂ := fun i ↦ B i) (fun _ ↦ Units.inv)
        (.of_forall fun _ _ hx ↦ hx.2) (fun _ ↦ Units.continuous_coe_inv)⟩

/-- Paper: Lemma A.1.1.2(3), p. 539. A subset of the restricted product has compact closure
exactly when it fits in a compact box whose factors eventually equal the distinguished sets.
Deviation: The proof works for Hausdorff spaces with eventually compact open distinguished sets. -/
theorem isCompact_closure_restrictedProduct_iff {A : (i : ι) → Set (G i)} [∀ i, T2Space (G i)]
    (hA : ∀ᶠ i in cofinite, IsCompact (A i) ∧ IsOpen (A i)) (H : Set (Πʳ i, [G i, A i])) :
    IsCompact (closure H) ↔ ∃ B : (i : ι) → Set (G i), (∀ i, IsCompact (B i)) ∧
      (∀ᶠ i in cofinite, B i = A i) ∧ ∀ x ∈ H, ∀ i, x i ∈ B i := by
  classical
  constructor
  · intro hc
    let U (J : Finset ι) := {x : Πʳ i, [G i, A i] | ∀ i ∈ {i | i ∉ J ∧ IsOpen (A i)}, x i ∈ A i}
    have hmono : Monotone U := fun _ _ h _ hx i hi ↦ hx i ⟨fun hj ↦ hi.1 (h hj), hi.2⟩
    obtain ⟨J, hJ⟩ := hc.elim_directed_cover U
      (fun _ ↦ isOpen_restrictedProduct_forall_mem _ (fun _ hi ↦ hi.2))
      (fun x _ ↦ mem_iUnion.mpr ⟨(eventually_cofinite.mp x.2).toFinset,
        fun i hi ↦ by
          by_contra h
          exact hi.1 ((eventually_cofinite.mp x.2).mem_toFinset.mpr h)⟩) hmono.directed_le
    let B (i : ι) := if i ∉ J ∧ IsCompact (A i) ∧ IsOpen (A i) then A i
      else (fun x : Πʳ i, [G i, A i] ↦ x i) '' closure H
    refine ⟨B, fun i ↦ ?_, ?_, fun x hx i ↦ ?_⟩
    · dsimp only [B]
      split_ifs with hi
      · exact hi.2.1
      · exact hc.image (continuous_eval i)
    · filter_upwards [J.eventually_cofinite_notMem, hA] with i hi hci using ite_eq_left ⟨hi, hci⟩
    · dsimp only [B]
      split_ifs with hi
      · exact hJ (subset_closure hx) i ⟨hi.1, hi.2.2⟩
      · exact mem_image_of_mem _ (subset_closure hx)
  · rintro ⟨B, hBc, hBA, hH⟩
    let (i : ι) : CompactSpace (B i) := isCompact_iff_compactSpace.mp (hBc i)
    have hbox : ∀ᶠ i in cofinite, ∀ x : (j : ι) → B j, (x i).val ∈ A i :=
      hBA.mono fun i hi x ↦ hi ▸ (x i).2
    let box (x : (i : ι) → B i) : Πʳ i, [G i, A i] :=
      ⟨fun i ↦ x i, hbox.mono fun _ hi ↦ hi x⟩
    have hc : Continuous box := continuous_restrictedProduct_of_uniform
      (fun i ↦ continuous_subtype_val.comp (continuous_apply i)) hbox
    apply (isCompact_range hc).closure_of_subset
    exact fun x hx ↦ ⟨fun i ↦ ⟨x i, hH x hx i⟩, rfl⟩

variable [∀ i, Group (G i)] {K L : (i : ι) → Subgroup (G i)}

/-- Paper: Lemma A.1.1.2(2), p. 539. Changing finitely many distinguished subgroups gives a
continuous multiplicative equivalence acting as the identity on coordinates.
Deviation: This construction needs no compactness or openness hypotheses. -/
def restrictedProductCongr (h : ∀ᶠ i in cofinite, K i = L i) :
    (Πʳ i, [G i, K i]) ≃ₜ* (Πʳ i, [G i, L i]) where
  toFun := map (fun _ ↦ id) (h.mono fun _ hi ↦ hi ▸ mapsTo_id _)
  invFun := map (fun _ ↦ id) (h.mono fun _ hi ↦ hi ▸ mapsTo_id _)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := mapAlong_continuous G G id tendsto_id _
    (h.mono fun _ hi ↦ hi ▸ mapsTo_id _) (fun _ ↦ continuous_id)
  continuous_invFun := mapAlong_continuous G G id tendsto_id _
    (h.mono fun _ hi ↦ hi ▸ mapsTo_id _) (fun _ ↦ continuous_id)

/-- Paper: Lemma A.1.1.2(4), p. 539. Split the restricted product at a finite set of indices
by restricting each tuple to that set and its complement.
Deviation: Only eventual openness of the distinguished subgroups is needed. -/
noncomputable def restrictedProductSplitFinset (hK : ∀ᶠ i in cofinite, IsOpen (K i : Set (G i)))
    (J : Finset ι) :
    (Πʳ i, [G i, K i]) ≃ₜ* (((j : J) → G j) × (Πʳ j : {i // i ∉ J}, [G j, K j])) := by
  classical
  let F := (j : J) → G j
  let T := Πʳ j : {i // i ∉ J}, [G j, K j]
  let P := Πʳ i, [G i, K i]
  have extend {p : ι → Prop} (hp : ∀ᶠ j : {i // i ∉ J} in cofinite, p j) :
      ∀ᶠ i in cofinite, p i := by
    filter_upwards [J.eventually_cofinite_notMem,
      eventually_comap.mp (hp.filter_mono (comap_cofinite_le Subtype.val))] with i hi h
    exact h ⟨i, hi⟩ rfl
  let glue (z : F × T) (i : ι) : G i := if hi : i ∈ J then z.1 ⟨i, hi⟩ else z.2 ⟨i, hi⟩
  let join (z : F × T) : P := ⟨glue z, extend (by
    filter_upwards [z.2.2] with j hj
    change glue z j ∈ K j
    simp only [glue, dite_eq_right j.2]
    exact hj)⟩
  let tail : P → T := mapAlong G _ Subtype.val Subtype.val_injective.tendsto_cofinite
    (fun _ ↦ id) (.of_forall fun _ ↦ mapsTo_id _)
  have htail : Continuous tail := mapAlong_continuous G _ Subtype.val
    Subtype.val_injective.tendsto_cofinite _ (.of_forall fun _ ↦ mapsTo_id _)
    (fun _ ↦ continuous_id)
  refine {
    toFun := fun x ↦ (fun j ↦ x j, tail x)
    invFun := join
    left_inv := ?_
    right_inv := ?_
    map_mul' := fun _ _ ↦ rfl
    continuous_toFun := (continuous_pi fun j ↦ continuous_eval j.val).prodMk htail
    continuous_invFun := ?_ }
  · intro x
    apply RestrictedProduct.ext
    intro i
    change glue _ i = x i
    by_cases hi : i ∈ J <;> simp [glue, hi]
    rfl
  · intro z
    apply Prod.ext
    · funext j
      simp [join, glue, j.2]
    · apply RestrictedProduct.ext
      intro j
      change glue z j = z.2 j
      simp [glue, j.2]
  · apply continuous_iff_continuousAt.mpr
    intro z
    -- Around z, the complementary factor lies uniformly in K on this cofinite set.
    let s := {j : {i // i ∉ J} | IsOpen (K j : Set (G j)) ∧ z.2 j ∈ K j}
    let V := {w : F × T | ∀ j ∈ s, w.2 j ∈ K j}
    have hV : IsOpen V := (isOpen_restrictedProduct_forall_mem s (fun j hj ↦ hj.1)).preimage
      continuous_snd
    apply ContinuousOn.continuousAt (s := V) _ (hV.mem_nhds fun j hj ↦ hj.2)
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply continuous_restrictedProduct_of_uniform
    · intro i
      change Continuous (fun w : V ↦ glue w.val i)
      by_cases hi : i ∈ J
      · simp only [glue, dite_eq_left hi]
        exact (continuous_apply (⟨i, hi⟩ : J)).comp (continuous_fst.comp continuous_subtype_val)
      · simp only [glue, dite_eq_right hi]
        exact (continuous_eval (⟨i, hi⟩ : {i // i ∉ J})).comp
          (continuous_snd.comp continuous_subtype_val)
    · apply extend
      filter_upwards [Subtype.val_injective.tendsto_cofinite.eventually hK, z.2.2] with j ho hz w
      simpa [domRestrict, join, glue, j.2] using w.2 j ⟨ho, hz⟩

end RiemannMasullo
