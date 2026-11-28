module

public import RiemannMasullo.AppA_AlgebraicNT.Sec3
public import RiemannMasullo.AppA_AlgebraicNT.Sec5a

import RiemannMasullo.AppA_AlgebraicNT.Sec1

/-! # Differentiation sequences in local quotient charts -/

public noncomputable section

open Filter MeasureTheory NumberField Set Topology
open scoped ENNReal Pointwise

namespace RiemannMasullo

section Quotient

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [secondCountable : SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) [discrete : DiscreteTopology H] (hH : IsClosed (H : Set G))

local instance instMeasurableSpaceLocalQuotient : MeasurableSpace (G ⧸ H) := borel _
local notation "q" => QuotientGroup.mk' H

variable {μ : Measure G} [haar : μ.IsHaarMeasure] [sigmaFinite : SigmaFinite μ] (hregular : μ.Regular)
  {ν : Measure (G ⧸ H)} (hν : IsWeilQuotientMeasure H μ Measure.count ν)

include secondCountable discrete hH haar sigmaFinite hregular hν in
/-- Under the counting normalization of Weil measure, the quotient preserves the
mass of a measurable set on which the quotient map is injective. -/
theorem weilQuotientMeasure_image_eq_of_injOn {A : Set G} (hA : MeasurableSet A)
    (hqA : MeasurableSet (q '' A)) (hinj : InjOn q A) : ν (q '' A) = μ A := by
  classical
  let : μ.Regular := hregular
  let : IsClosed (H : Set G) := hH
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : (Measure.count : Measure H).IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  let tr (y : G ⧸ H) (h : H) : G := y.out * (h : G)
  let κ (y : G ⧸ H) : Measure G := Measure.count.map (tr y)
  obtain ⟨hκ, hbind⟩ : Measurable κ ∧ ν.bind κ = μ :=
    weilMeasure_eq_bind H hH μ Measure.count ν hν
  rw [← hbind, Measure.bind_apply hA hκ.aemeasurable, ← lintegral_indicator_one hqA]
  apply lintegral_congr
  intro y
  have htr : Measurable (tr y) := (continuous_const.mul continuous_subtype_val).measurable
  have hqy (h : H) : q (tr y h) = y :=
    (QuotientGroup.mk_mul_of_mem y.out h.property).trans (Quotient.out_eq' y)
  change (q '' A).indicator 1 y = Measure.count.map (tr y) A
  rw [Measure.map_apply htr hA]
  by_cases hy : y ∈ q '' A
  · obtain ⟨x, hx, hxy⟩ := hy
    let k : H := ⟨y.out⁻¹ * x, QuotientGroup.eq.mp ((Quotient.out_eq' y).trans hxy.symm)⟩
    have hk : tr y k = x := mul_inv_cancel_left _ _
    have hpre : tr y ⁻¹' A = {k} := by
      ext h
      change tr y h ∈ A ↔ h = k
      constructor
      · intro hh
        have heq : tr y h = x := hinj hh hx ((hqy h).trans hxy.symm)
        exact Subtype.ext (mul_left_cancel (heq.trans hk.symm))
      · rintro rfl
        rwa [hk]
    rw [hpre, Measure.count_singleton, indicator_of_mem (show y ∈ q '' A from ⟨x, hx, hxy⟩), Pi.one_apply]
  · have hpre : tr y ⁻¹' A = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro h hh
      exact hy ⟨tr y h, hh, hqy h⟩
    rw [hpre, measure_empty, indicator_of_notMem hy]

include secondCountable discrete hH haar sigmaFinite hregular hν in
/-- An open D′-sequence and its difference sets descend through a single
injective quotient chart with the same doubling constant. -/
theorem IsDPrimeSequence.quotient_image_of_injOn {U : ℕ → Set G} (hU : IsDPrimeSequence μ U)
    (hOpen : ∀ n, IsOpen (U n)) {V : Set G} (hinj : InjOn q V)
    (hSub : ∀ n, U n * (U n)⁻¹ ⊆ V) :
    IsDPrimeSequence ν (fun n ↦ q '' (U n)) ∧ ∀ n, IsOpen (q '' (U n)) := by
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  have hqOpen : IsOpenMap q := QuotientGroup.isOpenMap_coe
  have hopen (n : ℕ) : IsOpen (q '' U n) := hqOpen _ (hOpen n)
  have hmass (n : ℕ) : ν (q '' U n) = μ (U n) :=
    weilQuotientMeasure_image_eq_of_injOn H hH hregular hν (hOpen n).measurableSet
      (hopen n).measurableSet (hinj.mono (fun x hx ↦ hSub n (Set.mem_mul.mpr
        ⟨x, hx, 1, by simpa using (hU.1.1 n).1, mul_one x⟩)))
  have hdiff (n : ℕ) : ν ((q '' U n) * (q '' U n)⁻¹) = μ (U n * (U n)⁻¹) := by
    rw [← Set.image_inv, ← Set.image_mul]
    have hD : IsOpen (U n * (U n)⁻¹) := (hOpen n).mul_right
    exact weilQuotientMeasure_image_eq_of_injOn H hH hregular hν hD.measurableSet
      (hqOpen _ hD).measurableSet (hinj.mono (hSub n))
  obtain ⟨⟨hb, hanti, C, hC, hdouble⟩, hcofinal⟩ := hU
  refine ⟨⟨⟨fun n ↦ ?_, fun _ _ hij ↦ Set.image_mono (hanti hij), C, hC, fun n ↦ ?_⟩, ?_⟩, hopen⟩
  · refine ⟨⟨1, (hb n).1, map_one q⟩, (hopen n).measurableSet.nullMeasurableSet, ?_⟩
    rw [hmass]
    exact (hb n).2.2
  · rw [hdiff, hmass]
    exact hdouble n
  · intro W hW
    have hq : Continuous q := QuotientGroup.continuous_mk
    have hp : q ⁻¹' W ∈ 𝓝 (1 : G) :=
      hq.continuousAt.preimage_mem_nhds (by simpa only [map_one] using hW)
    obtain ⟨n, hn⟩ := hcofinal _ hp
    exact ⟨n, Set.image_subset_iff.mpr hn⟩

include secondCountable discrete hH haar sigmaFinite hregular hν in
/-- A counting-normalized quotient by a closed discrete subgroup inherits an
open D′-sequence from the ambient group. A tail of the sequence stays in one
injective chart, including its difference sets. -/
theorem IsDPrimeSequence.exists_open_quotient_sequence {U : ℕ → Set G}
    (hU : IsDPrimeSequence μ U) (hOpen : ∀ n, IsOpen (U n)) :
    ∃ V : ℕ → Set (G ⧸ H), IsDPrimeSequence ν V ∧ ∀ n, IsOpen (V n) := by
  have hsing : IsOpen ({1} : Set H) := isOpen_discrete _
  obtain ⟨O, hO, hpre⟩ := isOpen_induced_iff.mp hsing
  have hone : (1 : G) ∈ O := by
    have h : (1 : H) ∈ ({1} : Set H) := mem_singleton _
    simpa only [← hpre, mem_preimage, Subgroup.coe_one] using h
  obtain ⟨V, hV, _, hVinv, hVV⟩ := exists_closed_nhds_one_inv_eq_mul_subset (hO.mem_nhds hone)
  have hinj : InjOn q V := by
    intro x hx y hy hxy
    have hHxy : x⁻¹ * y ∈ H := QuotientGroup.eq.mp hxy
    have hInv : x⁻¹ ∈ V := by rw [← hVinv]; exact Set.inv_mem_inv.mpr hx
    have hOxy : x⁻¹ * y ∈ O := hVV (Set.mem_mul.mpr ⟨x⁻¹, hInv, y, hy, rfl⟩)
    have hOne : (⟨x⁻¹ * y, hHxy⟩ : H) ∈ ({1} : Set H) := by
      rw [← hpre]
      exact hOxy
    exact inv_mul_eq_one.mp (congrArg Subtype.val (mem_singleton_iff.mp hOne))
  obtain ⟨W, hW, _, hWinv, hWW⟩ := exists_closed_nhds_one_inv_eq_mul_subset hV
  obtain ⟨n₀, h₀⟩ := hU.2 _ hW
  let U' (n : ℕ) := U (n + n₀)
  have hU' : IsDPrimeSequence μ U' := by
    obtain ⟨⟨hb, hanti, C, hC, hdouble⟩, hcofinal⟩ := hU
    refine ⟨⟨fun n ↦ hb (n + n₀), fun _ _ h ↦ hanti (Nat.add_le_add_right h n₀),
      C, hC, fun n ↦ hdouble (n + n₀)⟩, ?_⟩
    intro Z hZ
    obtain ⟨n, hn⟩ := hcofinal _ hZ
    exact ⟨n, (hanti (Nat.le_add_right n n₀)).trans hn⟩
  have hsub (n : ℕ) : U' n * (U' n)⁻¹ ⊆ V := by
    have hB : U' n ⊆ W := (hU.1.2.1 (Nat.le_add_left n₀ n)).trans h₀
    have hBinv : (U' n)⁻¹ ⊆ W := by
      rw [← hWinv]
      exact Set.inv_subset_inv.mpr hB
    exact (Set.mul_subset_mul hB hBinv).trans hWW
  exact ⟨fun n ↦ q '' U' n,
    hU'.quotient_image_of_injOn H hH hregular hν (fun n ↦ hOpen (n + n₀)) hinj hsub⟩

end Quotient

section Ideles

variable (F : Type*) [Field F] [NumberField F]

local instance instIdeleMeasurableSpaceLocalQuotient :
    MeasurableSpace (IdeleGroup (𝓞 F) F) := borel _
local instance instIdeleClassMeasurableSpaceLocalQuotient :
    MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _

/-- An open idelic D′-sequence gives an open D′-sequence for the
counting-normalized Tamagawa measure on the idèle class group. -/
theorem exists_open_DPrimeSequence_ideleClass_of_idele
    (F : Type*) [Field F] [NumberField F]
    {U : ℕ → Set (IdeleGroup (𝓞 F) F)}
    (hU : IsDPrimeSequence (multiplicativeTamagawaMeasure F) U)
    (hOpen : ∀ n, IsOpen (U n)) :
    ∃ V : ℕ → Set (IdeleClassGroup (𝓞 F) F),
      IsDPrimeSequence (ideleClassTamagawaMeasure F) V ∧ ∀ n, IsOpen (V n) := by
  let I := IdeleGroup (𝓞 F) F
  let P := IdeleGroup.principalSubgroup (𝓞 F) F
  obtain ⟨h₂, hlc, _⟩ := ideleGroup_topology F
  obtain ⟨_, hP, hPd, _⟩ := ideleGroup_quotient.{_, 0} F
  let : T2Space I := h₂
  let : LocallyCompactSpace I := hlc
  let : SecondCountableTopology I := idele_secondCountable F
  let : BorelSpace I := ⟨rfl⟩
  let : DiscreteTopology P := isDiscrete_iff_discreteTopology.mp hPd
  obtain ⟨hhaar, hregular, _⟩ := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec
  let : (multiplicativeTamagawaMeasure F).IsHaarMeasure := hhaar
  exact hU.exists_open_quotient_sequence P hP hregular (ideleClassTamagawaMeasure_isWeil F) hOpen

end Ideles

end RiemannMasullo
