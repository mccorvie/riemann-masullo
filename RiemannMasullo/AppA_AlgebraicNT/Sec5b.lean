module

public import RiemannMasullo.AppA_AlgebraicNT.Sec5a
public import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Maximal theorems and Lebesgue differentiation on locally compact abelian groups

Masullo, §§A.5.3–A.5.4, pp. 578–586.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal Pointwise

namespace RiemannMasullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} {U : ℕ → Set G} {C : ℝ}

-- TODO(paper-gap): Theorem A.5.3.1 claims strictness even for B = ∅, when both sides are zero.

-- Retain the existing hypotheses. The argument uses outer measure on the center set
-- and considers only the members of F given by the covering hypothesis.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Paper: Theorem A.5.3.1, p. 578. If each point of `B` centers an allowed translate,
one can select finitely many disjoint translates centered in `B` whose total mass
exceeds the mass of `B` divided by the structural constant.
Deviation: The strict comparison requires `B` to be nonempty. The finiteness condition
on `B * U 0` uses outer measure, as in Remark A.5.3.2. -/
theorem exists_disjoint_dSequence_translates [μ.IsHaarMeasure] (hU : IsDSequence μ U)
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {F : Set (Set G)} (hF : F ⊆ {V | ∃ (x : G) (k : ℕ), V = x • U k})
    {s : Set G} (hs : NullMeasurableSet s μ) (hsne : s.Nonempty) (hsU : μ (s * U 0) < ∞)
    (hcover : ∀ x ∈ s, ∃ k, x • U k ∈ F) :
    ∃ (n : ℕ) (x : Fin n → G) (k : Fin n → ℕ),
      (∀ i, x i ∈ s ∧ x i • U (k i) ∈ F) ∧
      Pairwise (fun i j ↦ Disjoint (x i • U (k i)) (x j • U (k j))) ∧
      μ s / ENNReal.ofReal C < ∑ i, μ (U (k i)) := by
  classical
  let translate (a : G × ℕ) := a.1 • U a.2
  let t : Set (G × ℕ) := {a | a.1 ∈ s ∧ translate a ∈ F}
  -- The geometric spacing forces the selected index to be at most the candidate index.
  let priority (a : G × ℕ) : ℝ := (1 / 2) ^ a.2
  obtain ⟨u, hut, hud, hmatch⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement translate t priority (3 / 2)
      (by norm_num) (fun _ _ ↦ by dsimp [priority]; positivity) 1
      (fun _ _ ↦ pow_le_one₀ (by norm_num) (by norm_num))
      (fun a _ ↦ ⟨a.1, Set.mem_smul_set.mpr ⟨1, (hU.1 a.2).1, mul_one _⟩⟩)
  let enlarged (a : u) := a.val.1 • (U a.val.2 * (U a.val.2)⁻¹)
  have hcenters (x : G) (hx : x ∈ s) : ∃ a : u, x ∈ enlarged a := by
    obtain ⟨k, hk⟩ := hcover x hx
    obtain ⟨a, hau, ⟨z, hz₁, hz₂⟩, hpriority⟩ := hmatch (x, k) ⟨hx, hk⟩
    have ha : a.2 ≤ k := by
      by_contra! h
      have hpow : (1 / 2 : ℝ) ^ a.2 ≤ (1 / 2) ^ k * (1 / 2) := by
        rw [← pow_succ]
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h
      change (1 / 2 : ℝ) ^ k ≤ (3 / 2) * (1 / 2) ^ a.2 at hpriority
      have hp : 0 < (1 / 2 : ℝ) ^ k := by positivity
      linarith
    obtain ⟨w, hwU, hw⟩ := Set.mem_smul_set.mp hz₁
    obtain ⟨v, hvU, hv⟩ := Set.mem_smul_set.mp hz₂
    change x * w = z at hw
    change a.1 * v = z at hv
    refine ⟨⟨a, hau⟩, Set.mem_smul_set.mpr ⟨v * w⁻¹, ?_, ?_⟩⟩
    · exact Set.mul_mem_mul hvU (Set.mem_inv.mpr (by simpa using hU.2.1 ha hwU))
    · change a.1 * (v * w⁻¹) = x
      rw [← mul_assoc, hv, ← hw, mul_assoc, mul_inv_cancel, mul_one]
  have hdisjoint : Pairwise (fun i j : u ↦ Disjoint (translate i) (translate j)) :=
    hud.on_injective Subtype.val_injective Subtype.property
  let mass (a : u) := μ (U a.val.2)
  have hmass : (∑' a : u, mass a) < ∞ := by
    calc
      (∑' a : u, mass a) = ∑' a : u, μ (translate a) := by
        simp only [mass, translate, measure_smul]
      _ ≤ μ (⋃ a : u, translate a) :=
        tsum_meas_le_meas_iUnion_of_disjoint₀ μ
          (fun a ↦ (hU.1 a.val.2).2.1.smul a.val.1)
          (fun _ _ hij ↦ (hdisjoint hij).aedisjoint)
      _ ≤ μ (s * U 0) := by
        apply measure_mono (iUnion_subset fun a ↦ ?_)
        rintro y ⟨w, hw, rfl⟩
        exact Set.mul_mem_mul (hut a.property).1 (hU.2.1 (Nat.zero_le _) hw)
      _ < ∞ := hsU
  -- Finite total mass and positive mass for every translate give countability.
  have : Countable u := by
    have hsupp : Function.support mass = univ :=
      Set.eq_univ_of_forall fun a ↦ (hU.1 a.val.2).2.2.1.ne'
    exact countable_univ_iff.mp (hsupp ▸ Summable.countable_support_ennreal hmass.ne)
  have hlt (a : u) : μ (enlarged a) < ENNReal.ofReal C * mass a := by
    simpa only [enlarged, mass, measure_smul] using hbound a.val.2
  have hscaled_fin : (∑' a : u, ENNReal.ofReal C * mass a) < ∞ := by
    rw [ENNReal.tsum_mul_left]
    exact (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmass.ne).lt_top
  have hsum_fin : (∑' a : u, μ (enlarged a)) ≠ ∞ :=
    ((tsum_le_tsum fun a ↦ (hlt a).le).trans_lt hscaled_fin).ne
  obtain ⟨x₀, hx₀⟩ := hsne
  obtain ⟨a₀, _⟩ := hcenters x₀ hx₀
  have hstrict : μ s < ENNReal.ofReal C * ∑' a : u, mass a := by
    calc
      μ s ≤ μ (⋃ a : u, enlarged a) := measure_mono fun x hx ↦ mem_iUnion.mpr (hcenters x hx)
      _ ≤ ∑' a : u, μ (enlarged a) := measure_iUnion_le _
      _ < ∑' a : u, ENNReal.ofReal C * mass a :=
        ENNReal.tsum_lt_tsum hsum_fin (fun a ↦ (hlt a).le) (hlt a₀)
      _ = ENNReal.ofReal C * ∑' a : u, mass a := ENNReal.tsum_mul_left
  have hfinite : μ s / ENNReal.ofReal C < ∑' a : u, mass a :=
    (ENNReal.div_lt_iff (Or.inl (ENNReal.ofReal_pos.mpr hC).ne') (Or.inl ENNReal.ofReal_ne_top)).mpr
      (by simpa only [mul_comm] using hstrict)
  rw [tsum_eq_iSup_sum, lt_iSup_iff] at hfinite
  obtain ⟨v, hv⟩ := hfinite
  let e := (Fintype.equivFin (↑v : Type _)).symm
  refine ⟨_, fun i ↦ (e i).val.val.1, fun i ↦ (e i).val.val.2,
    fun i ↦ hut (e i).val.property, fun i j hij ↦ ?_, ?_⟩
  · exact hdisjoint (Subtype.val_injective.ne (e.injective.ne hij))
  · change μ s / ENNReal.ofReal C < ∑ i, mass (e i).val
    rw [← Fintype.sum_equiv e.symm (fun a ↦ mass a.val) _ (by simp)]
    rwa [← Finset.sum_attach, Finset.attach_eq_univ] at hv

variable [SecondCountableTopology G]

-- Retain the original hypotheses for the countable-subcover argument.
set_option linter.unusedSectionVars false in
/-- Paper: Lemma A.5.3.3, p. 579. A set that is negligible on a neighborhood of
every point is negligible and measurable for the completed Haar measure. -/
theorem measure_zero_of_locally_negligible [μ.IsHaarMeasure] {A : Set G}
    (hA : ∀ x : G, ∃ V ∈ 𝓝 x, μ (A ∩ V) = 0) :
    μ A = 0 ∧ NullMeasurableSet A μ := by
  choose V hV hnull using hA
  obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover V hV
  have hzero : μ A = 0 := by
    rw [← inter_univ A, ← hcover]
    simp only [inter_iUnion]
    exact (measure_biUnion_null_iff ht).2 fun x _ ↦ hnull x
  exact ⟨hzero, NullMeasurableSet.of_null hzero⟩

/-- Paper: (A.5.3.2), p. 579. Take the limit superior of the masses of the
translates under `ν`, normalized by the Haar masses of the sequence members. -/
def dSequenceMeasureMaximal (μ ν : Measure G) (U : ℕ → Set G) (x : G) : ℝ≥0∞ :=
  limsup (fun k ↦ ν (x • U k) / μ (U k)) atTop

-- Preserve the existing section hypotheses.
set_option linter.unusedSectionVars false in
/-- Paper: (A.5.3.2), p. 579. Taking the same Haar measure in both positions
gives the constant maximal function one. -/
theorem dSequenceMeasureMaximal_haar [μ.IsHaarMeasure] (hU : IsDSequence μ U) (x : G) :
    dSequenceMeasureMaximal μ μ U x = 1 := by
  have hratio (k : ℕ) : μ (x • U k) / μ (U k) = 1 := by
    obtain ⟨_, _, hpos, hfin⟩ := hU.1 k
    rw [measure_smul, ENNReal.div_self hpos.ne' hfin.ne]
  simp only [dSequenceMeasureMaximal, hratio, limsup_const]

/-- Paper: Theorem A.5.3.4(1), p. 579. The localized weak bound is strict whenever
the strict level set meets `B`.
Deviation: Products of sets are measured by outer measure. -/
private theorem dSequenceMeasureMaximal_weak_strict [μ.IsHaarMeasure] {ν : Measure G} [ν.Regular]
    (hU : IsDSequence μ U) (hBorel : ∀ k, MeasurableSet (U k))
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {B : Set G} (hB : NullMeasurableSet B μ) (hBU : μ (B * U 0) < ∞)
    {α : ℝ} (hα : 0 < α) :
    let E := B ∩ {x | ENNReal.ofReal α < dSequenceMeasureMaximal μ ν U x}
    E.Nonempty → μ E < ENNReal.ofReal (C / α) * ν (E * U 0) := by
  classical
  intro E hE
  have htranslate (x : G) (k : ℕ) :
      x • U k = (fun y : G ↦ y * x⁻¹) ⁻¹' U k := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_preimage]
    simp only [smul_eq_mul, mul_comm]
  have hmax : Measurable (dSequenceMeasureMaximal μ ν U) := by
    apply Measurable.limsup
    intro k
    simp only [htranslate]
    exact ((measurable_measure_mul_right ν (hBorel k)).comp measurable_inv).div_const _
  have hEm : NullMeasurableSet E μ :=
    hB.inter (measurableSet_lt measurable_const hmax).nullMeasurableSet
  have hEsub : E ⊆ B := inter_subset_left
  let F : Set (Set G) :=
    {V | (∃ (x : G) (k : ℕ), V = x • U k) ∧ ENNReal.ofReal α * μ V < ν V}
  have hcover (x : G) (hx : x ∈ E) : ∃ k, x • U k ∈ F := by
    have hlevel : ENNReal.ofReal α < dSequenceMeasureMaximal μ ν U x := hx.2
    obtain ⟨k, hk⟩ := (frequently_lt_of_lt_limsup (h := hlevel)).exists
    refine ⟨k, ⟨⟨x, k, rfl⟩, ?_⟩⟩
    rw [measure_smul]
    exact lt_of_not_ge fun h ↦ hk.not_ge
      ((ENNReal.div_le_iff (hU.1 k).2.2.1.ne' (hU.1 k).2.2.2.ne).mpr
        (by simpa only [mul_comm] using h))
  obtain ⟨n, x, k, hx, hdisjoint, hmass⟩ :=
    exists_disjoint_dSequence_translates hU hC hbound (F := F) (fun _ hV ↦ hV.1) hEm hE
      ((measure_mono (Set.mul_subset_mul hEsub Subset.rfl)).trans_lt hBU) hcover
  have hunion : (⋃ i, x i • U (k i)) ⊆ E * U 0 := by
    refine iUnion_subset fun i ↦ ?_
    rintro y ⟨w, hw, rfl⟩
    exact Set.mul_mem_mul (hx i).1 (hU.2.1 (Nat.zero_le _) hw)
  have hsum : ∑ i, ENNReal.ofReal α * μ (U (k i)) ≤ ν (E * U 0) := by
    calc
      _ ≤ ∑ i, ν (x i • U (k i)) := Finset.sum_le_sum fun i _ ↦ by
        simpa only [measure_smul] using (hx i).2.2.le
      _ = ν (⋃ i, x i • U (k i)) := by
        rw [measure_iUnion hdisjoint, tsum_fintype]
        intro i
        rw [htranslate]
        exact (hBorel (k i)).preimage (measurable_mul_const _)
      _ ≤ ν (E * U 0) := measure_mono hunion
  calc
    μ E < ENNReal.ofReal C * ∑ i, μ (U (k i)) := by
      rw [mul_comm, ← ENNReal.div_lt_iff (Or.inl (ENNReal.ofReal_pos.mpr hC).ne')
        (Or.inl ENNReal.ofReal_ne_top)]
      exact hmass
    _ ≤ ENNReal.ofReal C * (ν (E * U 0) / ENNReal.ofReal α) := by
      refine mul_le_mul' le_rfl ?_
      apply (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hα).ne')
        (Or.inl ENNReal.ofReal_ne_top)).mpr
      simpa only [mul_comm _ (ENNReal.ofReal α), Finset.mul_sum] using hsum
    _ = ENNReal.ofReal (C / α) * ν (E * U 0) := by
      rw [ENNReal.ofReal_div_of_pos hα, ENNReal.div_eq_inv_mul, ← mul_assoc, div_eq_mul_inv]

/-- Paper: Theorem A.5.3.4(1), p. 579. On `B` the measure maximal function satisfies
the localized weak bound, with the mass on the right measured by `ν`.
Deviation: Products of sets are measured by outer measure. -/
theorem dSequenceMeasureMaximal_weak [μ.IsHaarMeasure] {ν : Measure G} [ν.Regular]
    (hU : IsDSequence μ U) (hBorel : ∀ k, MeasurableSet (U k))
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {B : Set G} (hB : NullMeasurableSet B μ) (hBU : μ (B * U 0) < ∞)
    {α : ℝ} (hα : 0 < α) :
    let E := B ∩ {x | ENNReal.ofReal α < dSequenceMeasureMaximal μ ν U x}
    μ E ≤ ENNReal.ofReal (C / α) * ν (E * U 0) := by
  intro E
  obtain hE | hE := E.eq_empty_or_nonempty
  · simp [hE]
  · exact (dSequenceMeasureMaximal_weak_strict hU hBorel hC hbound hB hBU hα hE).le

/-- Paper: Theorem A.5.3.4(1), p. 579. Equality in the localized weak bound
holds exactly when the part of the strict level set in `B` is empty.
Deviation: Products of sets are measured by outer measure. -/
theorem dSequenceMeasureMaximal_weak_eq_iff [μ.IsHaarMeasure] {ν : Measure G} [ν.Regular]
    (hU : IsDSequence μ U) (hBorel : ∀ k, MeasurableSet (U k))
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {B : Set G} (hB : NullMeasurableSet B μ) (hBU : μ (B * U 0) < ∞)
    {α : ℝ} (hα : 0 < α) :
    let E := B ∩ {x | ENNReal.ofReal α < dSequenceMeasureMaximal μ ν U x}
    μ E = ENNReal.ofReal (C / α) * ν (E * U 0) ↔ E = ∅ := by
  intro E
  obtain hE | hE := E.eq_empty_or_nonempty
  · simp [hE]
  · exact iff_of_false (dSequenceMeasureMaximal_weak_strict hU hBorel hC hbound hB hBU hα hE).ne
      hE.ne_empty

/-- Paper: Theorem A.5.3.4(2), p. 580. A Borel D-sequence with relatively
compact first member gives an almost everywhere finite measure maximal function. -/
theorem ae_dSequenceMeasureMaximal_lt_top [μ.IsHaarMeasure] {ν : Measure G} [ν.Regular]
    (hU : IsDSequence μ U) (hBorel : ∀ k, MeasurableSet (U k))
    (hcompact : IsCompact (closure (U 0))) :
    ∀ᵐ x ∂μ, dSequenceMeasureMaximal μ ν U x < ∞ := by
  rw [ae_iff]
  simp only [not_lt, top_le_iff]
  let A : Set G := {x | dSequenceMeasureMaximal μ ν U x = ∞}
  change μ A = 0
  obtain ⟨C, hC, hbound⟩ := hU.2.2
  have hnull {K : Set G} (hK : IsCompact K) : μ (K ∩ A) = 0 := by
    have hprod := hK.mul hcompact
    have hμ : μ (K * U 0) < ∞ :=
      (measure_mono (Set.mul_subset_mul Subset.rfl subset_closure)).trans_lt hprod.measure_lt_top
    have hν : ν (K * closure (U 0)) < ∞ := hprod.measure_lt_top
    have hlim : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (C / n) * ν (K * closure (U 0)))
        atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero, zero_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat C))
          (Or.inr hν.ne)
    refine le_antisymm (ge_of_tendsto hlim ?_) bot_le
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    let E := K ∩ {x | ENNReal.ofReal (n : ℝ) < dSequenceMeasureMaximal μ ν U x}
    calc
      μ (K ∩ A) ≤ μ E := measure_mono fun x hx ↦
        ⟨hx.1, by
          rw [mem_ofPred_eq, show dSequenceMeasureMaximal μ ν U x = ∞ from hx.2]
          exact ENNReal.ofReal_lt_top⟩
      _ ≤ ENNReal.ofReal (C / n) * ν (E * U 0) :=
        dSequenceMeasureMaximal_weak hU hBorel hC (fun k ↦ (hbound k).2)
          hK.isClosed.measurableSet.nullMeasurableSet hμ (Nat.cast_pos.mpr hn)
      _ ≤ ENNReal.ofReal (C / n) * ν (K * closure (U 0)) :=
        mul_le_mul' le_rfl (measure_mono (Set.mul_subset_mul inter_subset_left subset_closure))
  rw [← inter_univ A, ← iUnion_compactCovering G, inter_iUnion, measure_iUnion_null_iff]
  intro n
  rw [inter_comm]
  exact hnull (isCompact_compactCovering G n)

/-- Paper: Theorem A.5.3.5, p. 580. For a D′-sequence the weak bound on a
compact set can use the `ν`-mass of that compact set itself.
Deviation: Formula (A.5.3.5) is identical to (A.5.3.2) and uses the same operator. -/
theorem dSequenceMeasureMaximal_weak_compact [μ.IsHaarMeasure] {ν : Measure G} [ν.Regular]
    (hU : IsDPrimeSequence μ U)
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {K : Set G} (hK : IsCompact K) {α : ℝ} (hα : 0 < α) :
    μ (K ∩ {x | ENNReal.ofReal α < dSequenceMeasureMaximal μ ν U x}) ≤
      ENNReal.ofReal (C / α) * ν K := by sorry

/-- Paper: (A.5.3.8), p. 581. Take the limit superior of the averages of the
absolute value over the translates of the sequence members. The averages and
the limit superior take values in the extended nonnegative reals. -/
def dSequenceMaximal (μ : Measure G) (U : ℕ → Set G) (f : G → ℂ) (x : G) : ℝ≥0∞ :=
  limsup (fun k ↦ ⨍⁻ y in x • U k, ‖f y‖ₑ ∂μ) atTop

/-- Paper: (A.5.3.8), p. 581. When the sequence is eventually the identity
singleton of positive finite mass, the maximal function is the pointwise norm. -/
theorem dSequenceMaximal_eventually_singleton [μ.IsHaarMeasure]
    (h₀ : 0 < μ {1}) (hfin : μ {1} < ∞) (hU : ∀ᶠ k in atTop, U k = {1})
    (f : G → ℂ) (x : G) : dSequenceMaximal μ U f x = ‖f x‖ₑ := by
  have hx : μ {x} = μ {1} := by
    rw [← measure_smul μ x ({1} : Set G), Set.smul_set_singleton, smul_eq_mul, mul_one]
  have hev : ∀ᶠ k in atTop, ⨍⁻ y in x • U k, ‖f y‖ₑ ∂μ = ‖f x‖ₑ := by
    filter_upwards [hU] with k hk
    rw [hk, Set.smul_set_singleton, smul_eq_mul, mul_one, setLAverage_eq, lintegral_singleton,
      hx, ENNReal.mul_div_cancel_right h₀.ne' hfin.ne]
  rw [dSequenceMaximal, limsup_congr hev, limsup_const]

set_option linter.unusedSectionVars false in
/-- Multiplication on the left by a fixed element preserves equality of sets
up to a null set for an invariant measure. -/
private theorem smul_ae_eq_mul_left [μ.IsHaarMeasure] (x : G) {s t : Set G}
    (h : s =ᵐ[μ] t) :
    x • s =ᵐ[μ] x • t := by
  rw [ae_eq_set, ← Set.smul_set_sdiff, ← Set.smul_set_sdiff]
  obtain ⟨h1, h2⟩ := ae_eq_set.mp h
  rw [measure_smul μ x, measure_smul μ x]
  exact ⟨h1, h2⟩

-- The proof only needs measurability, so some automatic section variables stay unused.
set_option linter.unusedSectionVars false in
/-- Paper: Theorem A.5.3.6, p. 581. The local function maximal operator gives
a function measurable for the completed Haar measure. -/
theorem dSequenceMaximal_aemeasurable [μ.IsHaarMeasure] (hU : IsDSequence μ U)
    (hcompact : IsCompact (closure (U 0))) {f : G → ℂ} (hf : LocallyIntegrable f μ) :
    AEMeasurable (dSequenceMaximal μ U f) μ := by
  classical
  -- A measurable representative of the norm of `f`.
  obtain ⟨g, hg, hfg⟩ := hf.aestronglyMeasurable.aemeasurable
  have hF : Measurable fun y ↦ ‖g y‖ₑ := hg.stronglyMeasurable.eNorm
  have hnorm : (fun y ↦ ‖f y‖ₑ) =ᵐ[μ] (fun y ↦ ‖g y‖ₑ) := by
    filter_upwards [hfg] with y hy
    rw [hy]
  -- Borel representatives of the sequence members.
  have hVmeas : ∀ k, MeasurableSet (toMeasurable μ (U k)) :=
    fun k ↦ measurableSet_toMeasurable μ _
  have hVae : ∀ k, toMeasurable μ (U k) =ᵐ[μ] U k :=
    fun k ↦ (hU.1 k).2.1.toMeasurable_ae_eq
  -- Each translated averaged norm is measurable.
  have hmeas : ∀ k : ℕ, Measurable (fun x : G ↦
      ⨍⁻ y in x • toMeasurable μ (U k), ‖g y‖ₑ ∂μ) := by
    intro k
    have hpre : ∀ x : G, x • toMeasurable μ (U k)
        = (fun y : G ↦ y * x⁻¹) ⁻¹' toMeasurable μ (U k) := by
      intro x
      ext y
      rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_preimage]
      simp only [smul_eq_mul, mul_comm]
    have hC : Measurable (fun _ : G ↦ (1 : ℝ≥0∞)) := measurable_const
    have hW : Measurable (Function.uncurry
        (fun (x y : G) ↦ ‖g y‖ₑ * ((toMeasurable μ (U k)).indicator 1 (y * x⁻¹)))) := by
      have h1 : Measurable fun p : G × G ↦ ‖g p.2‖ₑ := hF.comp measurable_snd
      have h2 : Measurable fun p : G × G ↦ p.2 * p.1⁻¹ :=
        (measurable_snd).mul (Measurable.inv measurable_fst)
      have h3 : Measurable fun p : G × G ↦
          (toMeasurable μ (U k)).indicator 1 (p.2 * p.1⁻¹) :=
        hC.indicator (hVmeas k) |>.comp h2
      exact h1.mul h3
    have hint : ∀ x : G, ⨍⁻ y in x • toMeasurable μ (U k), ‖g y‖ₑ ∂μ
        = (∫⁻ y, ‖g y‖ₑ * ((toMeasurable μ (U k)).indicator 1 (y * x⁻¹)) ∂μ)
            / μ (toMeasurable μ (U k)) := by
      intro x
      have hfun : ((fun z : G ↦ z * x⁻¹) ⁻¹' toMeasurable μ (U k)).indicator
          (fun y ↦ ‖g y‖ₑ)
          = fun y ↦ ‖g y‖ₑ * ((toMeasurable μ (U k)).indicator 1 (y * x⁻¹)) := by
        funext y
        have hmem : y ∈ (fun z : G ↦ z * x⁻¹) ⁻¹' toMeasurable μ (U k)
            ↔ y * x⁻¹ ∈ toMeasurable μ (U k) := Set.mem_preimage
        by_cases hy : y * x⁻¹ ∈ toMeasurable μ (U k)
        · rw [Set.indicator_of_mem (hmem.mpr hy), Set.indicator_of_mem hy (1 : G → ℝ≥0∞),
            Pi.one_apply, mul_one]
        · rw [Set.indicator_of_notMem (fun hc ↦ hy (hmem.mp hc)),
            Set.indicator_of_notMem hy (1 : G → ℝ≥0∞), mul_zero]
      rw [setLAverage_eq μ (fun y ↦ ‖g y‖ₑ) _, measure_smul μ x, hpre x,
        ← lintegral_indicator ((hVmeas k).preimage (measurable_mul_const (x⁻¹))), hfun]
    rw [funext hint]
    exact hW.lintegral_prod_right.div_const _
  -- The maximal function coincides with the measurable limsup everywhere.
  have hterm : ∀ (k : ℕ) (x : G),
      ⨍⁻ y in x • U k, ‖f y‖ₑ ∂μ
        = ⨍⁻ y in x • toMeasurable μ (U k), ‖g y‖ₑ ∂μ := by
    intro k x
    have hpre : x • toMeasurable μ (U k)
        = (fun y : G ↦ y * x⁻¹) ⁻¹' toMeasurable μ (U k) := by
      ext y
      rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_preimage]
      simp only [smul_eq_mul, mul_comm]
    rw [setLAverage_congr (smul_ae_eq_mul_left x (hVae k)).symm, hpre]
    exact setLAverage_congr_fun_ae ((hVmeas k).preimage (measurable_mul_const (x⁻¹)))
      (by filter_upwards [hnorm] with y hy _; exact hy)
  refine ⟨fun x ↦ limsup (fun k ↦ ⨍⁻ y in x • toMeasurable μ (U k), ‖g y‖ₑ ∂μ) atTop,
    Measurable.limsup (fun k ↦ hmeas k), ?_⟩
  filter_upwards with x
  simp only [dSequenceMaximal]
  exact limsup_congr (Filter.eventually_atTop.mpr ⟨0, fun k _ ↦ hterm k x⟩)

-- TODO(paper-gap): The auxiliary bound (A.5.3.11) fails for f = 1 on any compact
-- set of positive Haar mass, since the log term vanishes and the left side is μ(K).

omit [IsTopologicalGroup G] [LocallyCompactSpace G] in
/-- Every D-sequence has a Borel D-sequence contained in it and agreeing with it
almost everywhere at each index. -/
private theorem exists_borel_dSequence [μ.IsHaarMeasure] (hU : IsDSequence μ U) :
    ∃ V : ℕ → Set G, IsDSequence μ V ∧
      (∀ k, MeasurableSet (V k)) ∧ (∀ k, V k ⊆ U k) ∧ (∀ k, V k =ᵐ[μ] U k) := by
  choose W hsub hmeas hae using fun k ↦ ((hU.1 k).2.1).exists_measurable_subset_ae_eq
  let V (k : ℕ) := ⋂ i ≤ k, ({1} ∪ W i)
  have hVone (k : ℕ) : (1 : G) ∈ V k :=
    mem_iInter.mpr fun i ↦ mem_iInter.mpr fun _ ↦ Or.inl rfl
  have hVmeas (k : ℕ) : MeasurableSet (V k) :=
    MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun _ ↦
      (measurableSet_singleton (1 : G)).union (hmeas i)
  have hVsub (k : ℕ) : V k ⊆ U k := by
    intro x hx
    have hx' := mem_iInter.mp (mem_iInter.mp hx k) le_rfl
    exact hx'.elim (fun hx₁ ↦ (mem_singleton_iff.mp hx₁).symm ▸ (hU.1 k).1) (fun h ↦ hsub k h)
  have hVae (k : ℕ) : V k =ᵐ[μ] U k := by
    filter_upwards [ae_all_iff.mpr hae] with x hx
    refine ⟨fun h ↦ hVsub k h, fun hxU ↦ ?_⟩
    exact mem_iInter.mpr fun i ↦ mem_iInter.mpr fun hi ↦ Or.inr ((hx i).mpr (hU.2.1 hi hxU))
  refine ⟨V, ⟨fun k ↦ ⟨hVone k, (hVmeas k).nullMeasurableSet, ?_⟩, ?_, ?_⟩, hVmeas, hVsub, hVae⟩
  · rw [measure_congr (hVae k)]
    exact (hU.1 k).2.2
  · intro j k hjk x hx
    exact mem_iInter.mpr fun i ↦ mem_iInter.mpr fun hi ↦
      mem_iInter.mp (mem_iInter.mp hx i) (hi.trans hjk)
  · obtain ⟨C, hC, hbound⟩ := hU.2.2
    refine ⟨C, hC, fun k ↦ ⟨?_, ?_⟩⟩
    · calc
        0 < μ (V k) := by simpa only [measure_congr (hVae k)] using (hU.1 k).2.2.1
        _ ≤ μ (V k * (V k)⁻¹) := measure_mono (Set.subset_mul_left _ (by simpa using hVone k))
    · rw [measure_congr (hVae k)]
      exact (measure_mono (Set.mul_subset_mul (hVsub k) (Set.inv_subset_inv.mpr (hVsub k)))).trans_lt
        (hbound k).2

omit [T2Space G] in
/-- For Borel D-sequence members the function maximal operator is Borel measurable. -/
private theorem measurable_dSequenceMaximal_of_borel [μ.IsHaarMeasure]
    (hBorel : ∀ k, MeasurableSet (U k)) (f : G → ℂ) :
    Measurable (dSequenceMaximal μ U f) := by
  let ν := μ.withDensity (fun x ↦ ‖f x‖ₑ)
  apply Measurable.limsup
  intro k
  have htranslate (x : G) : x • U k = (fun y : G ↦ y * x⁻¹) ⁻¹' U k := by
    simpa only [smul_eq_mul, mul_comm x⁻¹] using (Set.preimage_smul_inv x (U k)).symm
  have heq (x : G) : (⨍⁻ y in x • U k, ‖f y‖ₑ ∂μ) = ν (x • U k) / μ (U k) := by
    rw [setLAverage_eq, measure_smul, withDensity_apply _ ((hBorel k).const_smul x)]
  simp_rw [heq, htranslate]
  exact ((measurable_measure_mul_right ν (hBorel k)).comp measurable_inv).div_const _

/-- Paper: Theorem A.5.3.6, p. 582. A truncation at level `t` controls the
maximal function above `3 * t` on a compact set by the weighted mass of the input
above `t` on the compact enlargement.
Deviation: This uses the input level set as in (A.5.3.15), with a margin between
the maximal function threshold and the cutoff. -/
private theorem dSequenceMaximal_tail_bound [μ.IsHaarMeasure] (hU : IsDSequence μ U)
    (hBorel : ∀ k, MeasurableSet (U k)) (hcompact : IsCompact (closure (U 0)))
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {K : Set G} (hK : IsCompact K) {f : G → ℂ} (hfm : Measurable f)
    (hf : IntegrableOn f (K * closure (U 0)) μ) {t : ℝ} (ht : 0 < t) :
    let ν := (μ.restrict (K * closure (U 0))).withDensity (fun x ↦ ‖f x‖ₑ)
    μ (K ∩ {x | ENNReal.ofReal (3 * t) < dSequenceMaximal μ U f x}) ≤
      ENNReal.ofReal (C / t) * ν {x | t < ‖f x‖} := by
  let L := K * closure (U 0)
  let ν := (μ.restrict L).withDensity (fun x ↦ ‖f x‖ₑ)
  let A : Set G := {x | t < ‖f x‖}
  let νt := ν.restrict A
  have hL : IsCompact L := hK.mul hcompact
  have hAm : MeasurableSet A := measurableSet_lt measurable_const hfm.norm
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity hf.hasFiniteIntegral.ne
  have hsub : K ∩ {x | ENNReal.ofReal (3 * t) < dSequenceMaximal μ U f x} ⊆
      K ∩ {x | ENNReal.ofReal t < dSequenceMeasureMaximal μ νt U x} := by
    rintro x ⟨hxK, hx⟩
    refine ⟨hxK, ?_⟩
    have havg (k : ℕ) : (⨍⁻ y in x • U k, ‖f y‖ₑ ∂μ) ≤
        ENNReal.ofReal t + νt (x • U k) / μ (U k) := by
      let S := x • U k
      have hSm : MeasurableSet S := MeasurableSet.const_smul (hBorel k) x
      have hSL : S ⊆ L := by
        rintro y ⟨z, hz, rfl⟩
        exact Set.mul_mem_mul hxK (subset_closure (hU.2.1 (Nat.zero_le _) hz))
      have hνt : νt S = ∫⁻ y in S, A.indicator (fun y ↦ ‖f y‖ₑ) y ∂μ := by
        rw [Measure.restrict_apply hSm, withDensity_apply _ (hSm.inter hAm),
          Measure.restrict_restrict (hSm.inter hAm), inter_eq_left.mpr (inter_subset_left.trans hSL),
          lintegral_indicator hAm, Measure.restrict_restrict hAm, inter_comm A S]
      have hpoint (y : G) : ‖f y‖ₑ ≤ ENNReal.ofReal t + A.indicator (fun y ↦ ‖f y‖ₑ) y := by
        by_cases hy : y ∈ A
        · rw [indicator_of_mem hy]
          exact le_add_self
        · rw [indicator_of_notMem hy, add_zero, eNorm_eq_nnNorm, ← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal (le_of_not_gt hy)
      change (⨍⁻ y in S, ‖f y‖ₑ ∂μ) ≤ _
      rw [setLAverage_eq, show μ S = μ (U k) from measure_smul _ _ _]
      calc
        (∫⁻ y in S, ‖f y‖ₑ ∂μ) / μ (U k) ≤
            (∫⁻ y in S, ENNReal.ofReal t + A.indicator (fun y ↦ ‖f y‖ₑ) y ∂μ) / μ (U k) :=
          ENNReal.div_le_div_right (lintegral_mono hpoint) _
        _ = _ := by
          rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ,
            hνt.symm, show μ S = μ (U k) from measure_smul _ _ _, ENNReal.add_div,
            ENNReal.mul_div_cancel_right (hU.1 k).2.2.1.ne' (hU.1 k).2.2.2.ne]
    change ENNReal.ofReal (3 * t) < limsup (fun k ↦ ⨍⁻ y in x • U k, ‖f y‖ₑ ∂μ) atTop at hx
    have hfreq := frequently_lt_of_lt_limsup (h := hx)
    have hlim : ENNReal.ofReal (2 * t) ≤ dSequenceMeasureMaximal μ νt U x := by
      refine le_limsup_of_frequently_le ?_ (isBoundedUnder_of ⟨⊤, fun _ ↦ le_top⟩)
      apply hfreq.mono
      intro k hk
      have hsum : ENNReal.ofReal t + ENNReal.ofReal (2 * t) = ENNReal.ofReal (3 * t) := by
        rw [← ENNReal.ofReal_add ht.le (by positivity)]
        congr 1
        ring
      have hlt := hk.trans_le (havg k)
      rw [← hsum, ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top] at hlt
      exact hlt.le
    exact ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith : t < 2 * t)).trans_le hlim
  have hBU : μ (K * U 0) < ∞ :=
    (measure_mono (Set.mul_subset_mul Subset.rfl subset_closure)).trans_lt hL.measure_lt_top
  refine (measure_mono hsub).trans ((dSequenceMeasureMaximal_weak hU hBorel hC hbound
    hK.isClosed.measurableSet.nullMeasurableSet hBU ht).trans ?_)
  exact mul_le_mul' le_rfl ((measure_mono (subset_univ _)).trans_eq (Measure.restrict_apply_univ A))

/-- Paper: Theorem A.5.3.6, p. 581. If `f log⁺ |f|` is also locally
integrable, the extended-valued maximal function is locally integrable. -/
theorem dSequenceMaximal_locallyIntegrable [μ.IsHaarMeasure] (hU : IsDSequence μ U)
    (hcompact : IsCompact (closure (U 0))) {f : G → ℂ} (hf : LocallyIntegrable f μ)
    (hlog : LocallyIntegrable (fun x ↦ max (Real.log ‖f x‖) 0 • f x) μ) :
    LocallyIntegrable (dSequenceMaximal μ U f) μ := by
  obtain ⟨V, hV, hVm, hVU, hVae⟩ := exists_borel_dSequence hU
  obtain ⟨g, hgm, hfg⟩ := hf.aestronglyMeasurable.aemeasurable
  have hg := hf.congr hfg
  have hglog : LocallyIntegrable (fun x ↦ max (Real.log ‖g x‖) 0 • g x) μ :=
    hlog.congr (hfg.fun_comp fun z : ℂ ↦ max (Real.log ‖z‖) 0 • z)
  have hmax : dSequenceMaximal μ U f = dSequenceMaximal μ V g := by
    funext x
    unfold dSequenceMaximal
    congr 1
    funext k
    have htranslate := (smul_set_ae_eq x).mpr (hVae k)
    have hfgk : f =ᵐ[μ.restrict (x • U k)] g := ae_mono Measure.restrict_le_self hfg
    have hnorm : (fun y ↦ ‖f y‖ₑ) =ᵐ[μ.restrict (x • U k)] (fun y ↦ ‖g y‖ₑ) :=
      hfgk.fun_comp (fun z : ℂ ↦ ‖z‖ₑ)
    rw [setLAverage_eq, setLAverage_eq, Measure.restrict_congr_set htranslate,
      measure_congr htranslate, lintegral_congr_ae hnorm]
  have hVcompact : IsCompact (closure (V 0)) :=
    hcompact.of_isClosed_subset isClosed_closure (closure_mono (hVU 0))
  obtain ⟨C, hC, hbound⟩ := hV.2.2
  rw [hmax, locallyIntegrable_iff]
  intro K hK
  let M := dSequenceMaximal μ V g
  have hM : Measurable M := measurable_dSequenceMaximal_of_borel hVm g
  refine ⟨hM.aestronglyMeasurable, ?_⟩
  change (∫⁻ x in K, M x ∂μ) < ∞
  let L := K * closure (V 0)
  have hL : IsCompact L := hK.mul hVcompact
  let ν := (μ.restrict L).withDensity (fun x ↦ ‖g x‖ₑ)
  let tail (x : G) := max (‖g x‖ - 1) 0
  let weight (t : ℝ) := (t + 1)⁻¹
  have hweight (b : ℝ) (hb : 0 < b) : IntervalIntegrable weight volume 0 b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hb.le]
    refine (continuous_id.add continuous_const).continuousOn.inv₀ fun t ht ↦ ?_
    exact (show 0 < t + 1 by linarith [ht.1]).ne'
  have hweight_nonneg : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ weight t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact inv_nonneg.mpr (by linarith [show 0 < t from ht])
  have hlog_eq (x : G) :
      (∫ t in 0..tail x, weight t) = max (Real.log ‖g x‖) 0 := by
    change (∫ t in 0..tail x, (t + 1)⁻¹) = _
    rw [intervalIntegral.integral_comp_add_right (f := fun t : ℝ ↦ t⁻¹), zero_add,
      integral_inv_of_pos zero_lt_one (by dsimp [tail]; positivity), div_one]
    rcases le_or_gt ‖g x‖ 1 with hx | hx
    · simp [tail, max_eq_right (sub_nonpos.mpr hx), max_eq_right (Real.log_nonpos (norm_nonneg _) hx)]
    · rw [max_eq_left (Real.log_nonneg hx.le)]
      have htail : tail x + 1 = ‖g x‖ := by
        dsimp [tail]
        rw [max_eq_left (sub_nonneg.mpr hx.le), sub_add_cancel]
      rw [htail]
  have htail_integral :
      (∫⁻ t in Ioi (0 : ℝ), ν {x | t < tail x} * ENNReal.ofReal (weight t)) < ∞ := by
    have htailm : Measurable tail := (hgm.norm.sub_const 1).max measurable_const
    rw [← lintegral_comp_eq_lintegral_meas_lt_mul ν (f := tail)
      (.of_forall fun x ↦ le_max_right _ _) htailm.aemeasurable hweight hweight_nonneg]
    simp_rw [hlog_eq]
    rw [lintegral_withDensity_eq_lintegral_mul _ hgm.eNorm (by fun_prop)]
    have hfin := (hglog.integrableOn_isCompact hL).hasFiniteIntegral
    change (∫⁻ x in L, ‖max (Real.log ‖g x‖) 0 • g x‖ₑ ∂μ) < ∞ at hfin
    simpa only [Pi.mul_apply, eNorm_smul, Real.eNorm_eq_ofReal (le_max_right _ _), mul_comm]
      using hfin
  -- Subtracting one from the scaled maximal function leaves the small levels
  -- bounded by a constant and lets the weighted layer-cake formula start at zero.
  let Q (x : G) := M x / 4 - 1
  have hQ : Measurable Q := (hM.div_const 4).sub_const 1
  have hQfin : (∫⁻ x in K, Q x ∂μ) < ∞ := by
    rw [lintegral_eq_lintegral_measure_ofReal_le _ hQ.aemeasurable]
    calc
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal C * (ν {x | t < tail x} * ENNReal.ofReal (weight t)) := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro t ht
        have ht₀ : 0 < t := ht
        have ht₁ : 0 < t + 1 := by positivity
        rw [Measure.restrict_apply (measurableSet_le measurable_const hQ), inter_comm]
        calc
          _ ≤ μ (K ∩ {x | ENNReal.ofReal (3 * (t + 1)) < M x}) := by
            apply measure_mono
            rintro x ⟨hxK, hx⟩
            refine ⟨hxK, ?_⟩
            have hx' : ENNReal.ofReal t ≤ M x / 4 - 1 := hx
            have hxpos : 1 ≤ M x / 4 := by
              by_contra! h
              rw [tsub_eq_zero_of_le h.le] at hx'
              exact (ENNReal.ofReal_pos.mpr ht₀).not_ge hx'
            have hx4 : ENNReal.ofReal (t + 1) ≤ M x / 4 := by
              rw [ENNReal.ofReal_add ht₀.le zero_le_one, ENNReal.ofReal_one,
                ← tsub_add_cancel_of_le hxpos]
              exact add_le_add_left hx' _
            have hprod := (ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).mp hx4
            have hscale : ENNReal.ofReal (4 * (t + 1)) ≤ M x := by
              rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat, mul_comm]
              exact hprod
            exact ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
              (by linarith : 3 * (t + 1) < 4 * (t + 1))).trans_le hscale
          _ ≤ ENNReal.ofReal (C / (t + 1)) * ν {x | t + 1 < ‖g x‖} :=
            dSequenceMaximal_tail_bound hV hVm hVcompact hC (fun k ↦ (hbound k).2) hK hgm
              (hg.integrableOn_isCompact hL) ht₁
          _ = _ := by
            have heq : {x | t + 1 < ‖g x‖} = {x | t < tail x} := by
              ext x
              simp only [mem_ofPred_eq, tail, lt_max_iff, ht₀.not_gt, or_false]
              exact lt_sub_iff_add_lt.symm
            rw [heq, ENNReal.ofReal_div_of_pos ht₁, div_eq_mul_inv,
              show weight t = (t + 1)⁻¹ from rfl, ENNReal.ofReal_inv_of_pos ht₁]
            ac_rfl
      _ < ∞ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top htail_integral
  have hpoint (x : G) : M x ≤ 4 * (Q x + 1) := by
    calc
      M x = 4 * (M x / 4) := by
        rw [mul_comm, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
      _ ≤ _ := mul_le_mul' le_rfl le_tsub_add
  calc
    _ ≤ ∫⁻ x in K, 4 * (Q x + 1) ∂μ := lintegral_mono hpoint
    _ < ∞ := by
      rw [lintegral_const_mul _ (hQ.add_const 1), lintegral_add_right _ measurable_const,
        lintegral_const, one_mul, Measure.restrict_apply_univ]
      exact ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨hQfin, hK.measure_lt_top⟩)

/-- Paper: Theorem A.5.3.6, p. 581. Under the local `L log L` hypothesis,
the function maximal operator is finite almost everywhere. -/
theorem ae_dSequenceMaximal_lt_top [μ.IsHaarMeasure] (hU : IsDSequence μ U)
    (hcompact : IsCompact (closure (U 0))) {f : G → ℂ} (hf : LocallyIntegrable f μ)
    (hlog : LocallyIntegrable (fun x ↦ max (Real.log ‖f x‖) 0 • f x) μ) :
    ∀ᵐ x ∂μ, dSequenceMaximal μ U f x < ∞ := by
  have hloc := dSequenceMaximal_locallyIntegrable hU hcompact hf hlog
  suffices h : ∀ᵐ x ∂μ.restrict (⋃ n, compactCovering G n), dSequenceMaximal μ U f x < ∞ by
    simpa only [iUnion_compactCovering, Measure.restrict_univ] using h
  rw [ae_restrict_iUnion_iff]
  intro n
  have hint := hloc.integrableOn_isCompact (isCompact_compactCovering G n)
  refine ae_lt_top' hint.aestronglyMeasurable.aemeasurable ?_
  exact hint.hasFiniteIntegral.ne

/-- A compact set on which the input norm uniformly exceeds the maximal function
by a positive gap has zero mass. The weak measure bound controls the part of
small translates outside the compact set by the mass of an open enlargement. -/
private theorem measure_compact_zero_of_dSequenceMaximal_gap [μ.IsHaarMeasure]
    (hU : IsDPrimeSequence μ U) (hBorel : ∀ k, MeasurableSet (U k))
    (hcompact : IsCompact (closure (U 0))) {K : Set G} (hK : IsCompact K)
    {f : G → ℂ} {t s : ℝ} (ht : 0 ≤ t) (hts : t < s)
    (hmax : ∀ x ∈ K, dSequenceMaximal μ U f x ≤ ENNReal.ofReal t)
    (hnorm : ∀ x ∈ K, ENNReal.ofReal s ≤ ‖f x‖ₑ) : μ K = 0 := by
  obtain ⟨C, hC, hbound⟩ := hU.1.2.2
  let m := (t + s) / 2
  let p := (s - m) / s
  let q := p / 2
  have hs : 0 < s := ht.trans_lt hts
  have htm : t < m := by dsimp [m]; linarith
  have hms : m < s := by dsimp [m]; linarith
  have hp : 0 < p := div_pos (sub_pos.mpr hms) hs
  have hq : 0 < q := half_pos hp
  have hsplit : ENNReal.ofReal m + ENNReal.ofReal s * ENNReal.ofReal p = ENNReal.ofReal s := by
    rw [← ENNReal.ofReal_mul hs.le, ← ENNReal.ofReal_add (ht.trans htm.le) (mul_nonneg hs.le hp.le)]
    congr 1
    dsimp only [p]
    rw [mul_div_cancel₀ _ hs.ne', add_sub_cancel]
  by_contra hnull
  let c := ENNReal.ofReal (C / q)
  have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr (div_pos hC hq)).ne'
  have hcfin : c ≠ ∞ := ENNReal.ofReal_ne_top
  obtain ⟨O, hKO, hO, _, hsmall⟩ := hK.isClosed.measurableSet.exists_isOpen_sdiff_lt
    (μ := μ) hK.measure_lt_top.ne (ENNReal.div_ne_zero.mpr ⟨hnull, hcfin⟩)
  let ν := μ.restrict (O \ K)
  have hsub : K ⊆ K ∩ {x | ENNReal.ofReal q < dSequenceMeasureMaximal μ ν U x} := by
    intro x hx
    have hnear : ∀ᶠ k in atTop, x • U k ⊆ O := by
      obtain ⟨n, hn⟩ := hU.2 ((fun z ↦ x * z) ⁻¹' O)
        ((hO.preimage (continuous_const.mul continuous_id)).mem_nhds
          (show x * 1 ∈ O by simpa using hKO hx))
      filter_upwards [eventually_ge_atTop n] with k hk
      rintro y ⟨z, hz, rfl⟩
      exact hn (hU.1.2.1 hk hz)
    have havg : ∀ᶠ k in atTop, (⨍⁻ y in x • U k, ‖f y‖ₑ ∂μ) < ENNReal.ofReal m :=
      eventually_lt_of_limsup_lt ((hmax x hx).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff (ht.trans_lt htm)).mpr htm))
    have hlarge : ∀ᶠ k in atTop, ENNReal.ofReal p ≤ ν (x • U k) / μ (U k) := by
      filter_upwards [hnear, havg] with k hk hlt
      let S := x • U k
      have hSm : MeasurableSet S := (hBorel k).const_smul x
      have hν : ν S = μ (S \ K) := by
        rw [Measure.restrict_apply hSm, ← inter_sdiff_assoc, inter_eq_left.mpr hk]
      have hpart : ENNReal.ofReal s * μ (S ∩ K) ≤ ∫⁻ y in S, ‖f y‖ₑ ∂μ := by
        rw [← setLIntegral_const]
        exact (setLIntegral_mono' (hSm.inter hK.isClosed.measurableSet)
          (fun y hy ↦ hnorm y hy.2)).trans
          (lintegral_mono' (Measure.restrict_mono inter_subset_left le_rfl) le_rfl)
      have hmass : μ S = μ (U k) := measure_smul _ _ _
      have hsum : ENNReal.ofReal s ≤ (⨍⁻ y in S, ‖f y‖ₑ ∂μ) +
          ENNReal.ofReal s * (ν S / μ (U k)) := by
        rw [setLAverage_eq, hmass, hν, ← mul_div_assoc, ← ENNReal.add_div]
        apply le_trans ?_ (ENNReal.div_le_div_right (add_le_add_left hpart _) _)
        rw [← mul_add, measure_inter_add_sdiff S hK.isClosed.measurableSet, hmass,
          ENNReal.mul_div_cancel_right (hU.1.1 k).2.2.1.ne' (hU.1.1 k).2.2.2.ne]
      refine le_of_not_gt fun h ↦ (not_lt_of_ge hsum) ?_
      have hmul : ENNReal.ofReal s * (ν S / μ (U k)) < ENNReal.ofReal s * ENNReal.ofReal p := by
        simpa only [mul_comm (ENNReal.ofReal s)] using
          ENNReal.mul_lt_mul_left (ENNReal.ofReal_pos.mpr hs).ne' ENNReal.ofReal_ne_top h
      calc
        _ ≤ ENNReal.ofReal m + ENNReal.ofReal s * (ν S / μ (U k)) := add_le_add_left hlt.le _
        _ < ENNReal.ofReal m + ENNReal.ofReal s * ENNReal.ofReal p :=
          (ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top).mpr hmul
        _ = ENNReal.ofReal s := hsplit
    refine ⟨hx, ?_⟩
    exact ((ENNReal.ofReal_lt_ofReal_iff hp).mpr (half_lt_self hp)).trans_le
      (le_limsup_of_frequently_le hlarge.frequently)
  have hfin : μ (K * U 0) < ∞ :=
    (measure_mono (Set.mul_subset_mul Subset.rfl subset_closure)).trans_lt
      (hK.mul hcompact).measure_lt_top
  have hweak := dSequenceMeasureMaximal_weak (ν := ν) hU.1 hBorel hC
    (fun k ↦ (hbound k).2) hK.isClosed.measurableSet.nullMeasurableSet hfin hq
  have hmass : μ K ≤ c * μ (O \ K) :=
    (measure_mono hsub).trans (hweak.trans (mul_le_mul' le_rfl
      ((measure_mono (subset_univ _)).trans_eq (Measure.restrict_apply_univ _))))
  exact (not_lt_of_ge hmass) (by
    simpa only [mul_comm c, ENNReal.div_mul_cancel hc hcfin] using
      ENNReal.mul_lt_mul_left hc hcfin hsmall)

/-- On a Borel D′-sequence the strict input level set is contained almost
everywhere in the corresponding strict maximal-function level set. -/
private theorem ae_dSequenceMaximal_level_of_borel [μ.IsHaarMeasure]
    (hU : IsDPrimeSequence μ U) (hBorel : ∀ k, MeasurableSet (U k))
    (hcompact : IsCompact (closure (U 0))) {f : G → ℂ} (hf : Measurable f)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x ∂μ, ENNReal.ofReal t < ‖f x‖ₑ → ENNReal.ofReal t < dSequenceMaximal μ U f x := by
  have hnull (q : ℚ) (htq : t < (q : ℝ)) :
      μ {x | dSequenceMaximal μ U f x ≤ ENNReal.ofReal t ∧ ENNReal.ofReal (q : ℝ) ≤ ‖f x‖ₑ} = 0 := by
    have hm : MeasurableSet
        {x | dSequenceMaximal μ U f x ≤ ENNReal.ofReal t ∧ ENNReal.ofReal (q : ℝ) ≤ ‖f x‖ₑ} :=
      (measurableSet_le (measurable_dSequenceMaximal_of_borel hBorel f) measurable_const).inter
        (measurableSet_le measurable_const hf.eNorm)
    rw [hm.measure_eq_iSup_isCompact μ]
    refine le_antisymm (iSup_le fun K ↦ iSup_le fun hsub ↦ iSup_le fun hK ↦ ?_) bot_le
    exact
      (measure_compact_zero_of_dSequenceMaximal_gap hU hBorel hcompact hK ht htq
        (fun x hx ↦ (hsub hx).1) (fun x hx ↦ (hsub hx).2)).le
  have hae (q : ℚ) : ∀ᵐ x ∂μ, t < (q : ℝ) →
      ¬(dSequenceMaximal μ U f x ≤ ENNReal.ofReal t ∧ ENNReal.ofReal (q : ℝ) ≤ ‖f x‖ₑ) := by
    by_cases h : t < (q : ℝ)
    · simp only [h, true_implies, ae_iff, not_not]
      exact hnull q h
    · simp [h]
  filter_upwards [ae_all_iff.mpr hae] with x hx hnorm
  obtain ⟨q, _, hq₁, hq₂⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hnorm
  change ENNReal.ofReal t < ENNReal.ofReal (q : ℝ) at hq₁
  change ENNReal.ofReal (q : ℝ) < ‖f x‖ₑ at hq₂
  exact lt_of_not_ge fun h ↦ hx q (lt_of_not_ge fun htq ↦
    hq₁.not_ge (ENNReal.ofReal_le_ofReal htq)) ⟨h, hq₂.le⟩

/-- Paper: Theorem A.5.3.6(1), p. 581. The mass of the strict level set on `B`
is bounded by the integral of `|f|` over the lower maximal-function level set in `B * U 0`,
with the factor in (A.5.3.9). -/
theorem dSequenceMaximal_weak_local [μ.IsHaarMeasure] (hU : IsDPrimeSequence μ U)
    (hcompact : IsCompact (closure (U 0)))
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {f : G → ℂ} (hf : LocallyIntegrable f μ) {B : Set G} (hB : NullMeasurableSet B μ)
    (hBU : NullMeasurableSet (B * U 0) μ) (hfin : μ (B * U 0) < ∞)
    {α δ : ℝ} (hα : 0 < α) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    μ (B ∩ {x | ENNReal.ofReal α < dSequenceMaximal μ U f x}) ≤
      ENNReal.ofReal (C / ((1 - δ) * α)) *
        ∫⁻ x in (B * U 0) ∩ {x | ENNReal.ofReal (δ * α) < dSequenceMaximal μ U f x},
          ‖f x‖ₑ ∂μ := by
  obtain ⟨V, hV, hVm, hVU, hVae⟩ := exists_borel_dSequence hU.1
  obtain ⟨g, hgm, hfg⟩ := hf.aestronglyMeasurable.aemeasurable
  have hg := hf.congr hfg
  have hnorm : (fun y ↦ ‖f y‖ₑ) =ᵐ[μ] (fun y ↦ ‖g y‖ₑ) :=
    hfg.fun_comp (fun z : ℂ ↦ ‖z‖ₑ)
  have hmax : dSequenceMaximal μ U f = dSequenceMaximal μ V g := by
    funext x
    unfold dSequenceMaximal
    congr 1
    funext k
    have htranslate := (smul_set_ae_eq x).mpr (hVae k)
    rw [setLAverage_eq, setLAverage_eq, Measure.restrict_congr_set htranslate,
      measure_congr htranslate, lintegral_congr_ae (ae_restrict_of_ae hnorm)]
  rw [hmax, lintegral_congr_ae (ae_restrict_of_ae hnorm)]
  have hV' : IsDPrimeSequence μ V := ⟨hV, fun W hW ↦ by
    obtain ⟨k, hk⟩ := hU.2 W hW
    exact ⟨k, (hVU k).trans hk⟩⟩
  have hVcompact := hcompact.of_isClosed_subset isClosed_closure (closure_mono (hVU 0))
  have hVbound (k : ℕ) : μ (V k * (V k)⁻¹) < ENNReal.ofReal C * μ (V k) := by
    rw [measure_congr (hVae k)]
    exact (measure_mono (Set.mul_subset_mul (hVU k) (Set.inv_subset_inv.mpr (hVU k)))).trans_lt
      (hbound k)
  let t := δ * α
  let a := (1 - δ) * α
  have ht : 0 ≤ t := mul_nonneg hδ₀.le hα.le
  have ha : 0 < a := mul_pos (sub_pos.mpr hδ₁) hα
  have hsum : ENNReal.ofReal t + ENNReal.ofReal a = ENNReal.ofReal α := by
    rw [← ENNReal.ofReal_add ht ha.le]
    congr 1
    dsimp [t, a]
    ring
  let A := {x | ENNReal.ofReal t < dSequenceMaximal μ V g x}
  have hAm : MeasurableSet A :=
    measurableSet_lt measurable_const (measurable_dSequenceMaximal_of_borel hVm g)
  let w := A.indicator (fun x ↦ ‖g x‖ₑ)
  let ν := μ.withDensity w
  have hpoint : ∀ᵐ x ∂μ, ‖g x‖ₑ ≤ ENNReal.ofReal t + w x := by
    filter_upwards [ae_dSequenceMaximal_level_of_borel hV' hVm hVcompact hgm ht] with x hx
    by_cases h : x ∈ A
    · rw [show w x = ‖g x‖ₑ from indicator_of_mem h _]
      exact le_add_self
    · exact (le_of_not_gt fun hlt ↦ h (hx hlt)).trans le_self_add
  have : IsFiniteMeasureOnCompacts ν := ⟨fun K hK ↦ by
    rw [withDensity_apply w hK.isClosed.measurableSet]
    exact (lintegral_mono (indicator_le_self' (fun _ _ ↦ zero_le) (s := A))).trans_lt
      (hg.integrableOn_isCompact hK).hasFiniteIntegral⟩
  have hcompare (x : G) :
      dSequenceMaximal μ V g x ≤ ENNReal.ofReal t + dSequenceMeasureMaximal μ ν V x := by
    have havg (k : ℕ) : (⨍⁻ y in x • V k, ‖g y‖ₑ ∂μ) ≤
        ENNReal.ofReal t + ν (x • V k) / μ (V k) := by
      rw [setLAverage_eq, measure_smul]
      calc
        _ ≤ (∫⁻ y in x • V k, ENNReal.ofReal t + w y ∂μ) / μ (V k) :=
          ENNReal.div_le_div_right (lintegral_mono_ae (ae_restrict_of_ae hpoint)) _
        _ = _ := by
          rw [lintegral_add_left measurable_const, setLIntegral_const,
            ← withDensity_apply w ((hVm k).const_smul x), measure_smul, ENNReal.add_div,
            ENNReal.mul_div_cancel_right (hV.1 k).2.2.1.ne' (hV.1 k).2.2.2.ne]
    rw [add_comm, ← tsub_le_iff_right, dSequenceMaximal, ← ENNReal.limsup_sub_const,
      dSequenceMeasureMaximal]
    exact limsup_le_limsup (Eventually.of_forall fun k ↦ tsub_le_iff_right.mpr (by
      simpa only [add_comm] using havg k))
  have hsub : B ∩ {x | ENNReal.ofReal α < dSequenceMaximal μ V g x} ⊆
      B ∩ {x | ENNReal.ofReal a < dSequenceMeasureMaximal μ ν V x} := by
    rintro x ⟨hxB, hx⟩
    have hlt := hx.trans_le (hcompare x)
    rw [← hsum] at hlt
    exact ⟨hxB, (ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top).mp hlt⟩
  have hprod : B * V 0 ⊆ B * U 0 := Set.mul_subset_mul Subset.rfl (hVU 0)
  have hweak := dSequenceMeasureMaximal_weak (ν := ν) hV hVm hC hVbound hB
    ((measure_mono hprod).trans_lt hfin) ha
  refine (measure_mono hsub).trans (hweak.trans (mul_le_mul' le_rfl ?_))
  refine (measure_mono ((Set.mul_subset_mul inter_subset_left Subset.rfl).trans hprod)).trans_eq ?_
  rw [withDensity_apply₀ w hBU, lintegral_indicator hAm, Measure.restrict_restrict hAm, inter_comm]

/-- Paper: Theorem A.5.3.6(2), p. 581. The `p`-th moment on `B` of the maximal
function is bounded by the `p`-th moment of `|f|` on `B * U 0`, with the factor in (A.5.3.10).
Deviation: The conditions on `B` from part (1) are read as applying to part (2) as well. -/
theorem dSequenceMaximal_strong_local [μ.IsHaarMeasure] (hU : IsDPrimeSequence μ U)
    (hcompact : IsCompact (closure (U 0)))
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {f : G → ℂ} (hf : LocallyIntegrable f μ) {B : Set G} (hB : NullMeasurableSet B μ)
    (hBU : NullMeasurableSet (B * U 0) μ) (hfin : μ (B * U 0) < ∞)
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ x in B, dSequenceMaximal μ U f x ^ p ∂μ) ≤
      ENNReal.ofReal (C * p ^ (p + 1) / (p - 1) ^ p) *
        ∫⁻ x in B * U 0, ‖f x‖ₑ ^ p ∂μ := by sorry

/-- Paper: Theorem A.5.3.7(1), p. 582. The mass of the global strict level
set is bounded by the `L¹` norm times `2 * C / α`. -/
theorem dSequenceMaximal_weak_global [μ.IsHaarMeasure] (hU : IsDPrimeSequence μ U)
    (hcompact : IsCompact (closure (U 0)))
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {f : G → ℂ} (hf : Integrable f μ) {α : ℝ} (hα : 0 < α) :
    μ {x | ENNReal.ofReal α < dSequenceMaximal μ U f x} ≤
      ENNReal.ofReal (2 * C / α) * eLpNorm f 1 μ := by sorry

/-- Paper: Theorem A.5.3.7(2), p. 582. An `Lᵖ` input with `p > 1`
has an `Lᵖ` maximal function. -/
theorem dSequenceMaximal_memLp [μ.IsHaarMeasure] (hU : IsDPrimeSequence μ U)
    (hcompact : IsCompact (closure (U 0)))
    {f : G → ℂ} {p : ℝ} (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (dSequenceMaximal μ U f) (ENNReal.ofReal p) μ := by sorry

/-- Paper: Theorem A.5.3.7(2), p. 582. On the entire group the `p`-th moment
of the maximal function is bounded by the `p`-th power of the `Lᵖ` norm times the printed factor. -/
theorem dSequenceMaximal_strong_global [μ.IsHaarMeasure] (hU : IsDPrimeSequence μ U)
    (hcompact : IsCompact (closure (U 0)))
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {f : G → ℂ} {p : ℝ} (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    (∫⁻ x, dSequenceMaximal μ U f x ^ p ∂μ) ≤
      ENNReal.ofReal (C * p ^ (p + 1) / (p - 1) ^ p) *
        eLpNorm f (ENNReal.ofReal p) μ ^ p := by sorry

/-- Paper: (A.5.4.1), p. 582. Average a complex-valued function over the
left translate of a sequence member. Haar invariance equates the mass of the
translate used by the set average with the mass of the original member. -/
def dSequenceAverage (μ : Measure G) (V : Set G) (f : G → ℂ) (x : G) : ℂ :=
  ⨍ y in x • V, f y ∂μ

-- Retain the stated hypotheses; the proof needs only Haar invariance.
set_option linter.unusedSectionVars false in
/-- Paper: (A.5.4.1), p. 582. Averaging a constant over any sequence member
recovers the constant at every point. -/
theorem dSequenceAverage_const [μ.IsHaarMeasure] (hU : IsDSequence μ U)
    (c : ℂ) (k : ℕ) (x : G) : dSequenceAverage μ (U k) (fun _ ↦ c) x = c := by
  -- The translate `x • U k` has the positive finite mass of `U k` by Haar invariance.
  obtain ⟨-, -, hpos, hfin⟩ := hU.1 k
  rw [dSequenceAverage, setAverage_const] <;> rw [measure_smul]
  exacts [hpos.ne', hfin.ne]

-- TODO(paper-gap): The uniform continuity in Theorem A.5.4.1(1) fails for f(t) = t²
-- on the additive real line with U k = [−2⁻ᵏ, 2⁻ᵏ]. The average is x² + 2⁻²ᵏ / 3.

/-- Paper: Theorem A.5.4.1(3), p. 582. A point is regular when the sequence of
averages at that point has a complex limit. -/
def dSequenceRegularSet (μ : Measure G) (U : ℕ → Set G) (f : G → ℂ) : Set G :=
  {x | ∃ l : ℂ, Tendsto (fun k ↦ dSequenceAverage μ (U k) f x) atTop (𝓝 l)}

/-- Paper: Theorem A.5.4.1(3), p. 582. Every point is regular for a constant
function. -/
theorem dSequenceRegularSet_const [μ.IsHaarMeasure] (hU : IsDSequence μ U) (c : ℂ) :
    dSequenceRegularSet μ U (fun _ ↦ c) = univ := by
  refine eq_univ_of_forall fun x ↦ ⟨c, ?_⟩
  simp only [dSequenceAverage_const hU, tendsto_const_nhds]

-- TODO(paper-gap): In the proof of Theorem A.5.4.1(2), the boundary of a relatively compact
-- open set can have positive Haar mass, and an indicator's averages can diverge at a point.

/-- Paper: Theorem A.5.4.1(2)–(3), p. 582. The complement of the regular set
is negligible, equivalently the averages converge almost everywhere. -/
theorem measure_compl_dSequenceRegularSet [μ.IsHaarMeasure] (hU : IsDPrimeSequence μ U)
    {f : G → ℂ} (hf : LocallyIntegrable f μ) :
    μ (dSequenceRegularSet μ U f)ᶜ = 0 := by sorry

-- TODO(paper-gap): In the proof of Theorem A.5.4.1(3), compact support does not imply Lᵖ
-- integrability, and the Lᑫ norm of the normalized kernel is μ(U k)^(1/q - 1).

/-- Paper: Theorem A.5.4.1(3), p. 583. The averages tend to the value of the
function almost everywhere, which also gives the identity almost everywhere on the regular set. -/
theorem ae_tendsto_dSequenceAverage [μ.IsHaarMeasure] (hU : IsDPrimeSequence μ U)
    {f : G → ℂ} (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun k ↦ dSequenceAverage μ (U k) f x) atTop (𝓝 (f x)) := by sorry

/-- Paper: Terminology A.5.4.1, p. 583. The smoothening at a regular point
is the complex limit of the sequence of averages. -/
def dSequenceSmoothening (μ : Measure G) (U : ℕ → Set G) (f : G → ℂ)
    (x : dSequenceRegularSet μ U f) : ℂ :=
  limUnder atTop (fun k ↦ dSequenceAverage μ (U k) f x)

/-- Paper: Terminology A.5.4.1, p. 583. A constant function smoothens to that
same constant on its regular set. -/
theorem dSequenceSmoothening_const [μ.IsHaarMeasure] (hU : IsDSequence μ U) (c : ℂ)
    (x : dSequenceRegularSet μ U (fun _ ↦ c)) :
    dSequenceSmoothening μ U (fun _ ↦ c) x = c := by
  simp only [dSequenceSmoothening, dSequenceAverage_const hU]
  exact tendsto_const_nhds.limUnder_eq

-- TODO(paper-gap): Remark A.5.4.2 refers to D_f without specifying it.

-- TODO(paper-gap): Corollary A.5.4.3 fails at x = 0 for symmetric intervals on ℝ.
-- Use f(t) = sgn(t) |t|⁻¹ᐟ² and a compactly supported continuous φ with
-- φ(t) = sgn(t) |t|¹ᐟ⁴ near zero. The averages of f vanish, while those of φ · f diverge.

end RiemannMasullo
