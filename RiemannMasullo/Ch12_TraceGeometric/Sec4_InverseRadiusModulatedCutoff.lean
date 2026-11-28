module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_InverseRadiusLaw

/-! # Modulated cutoffs from reciprocal radius laws -/

public noncomputable section

open Function MeasureTheory Set
open scoped ContDiff NNReal Topology

namespace RiemannMasullo

/-- The difference of a smooth upper-radius survival function and its
reciprocal-radius survival function is a modulated annular cutoff.
The left plateau margin is bounded by the width of the upper transition. -/
theorem isModulatedCutoff_avgCutoff_sub_inverseRadiusLaw
    {G : Type*} [CommGroup G] [TopologicalSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (σ : Measure ℝ) [IsProbabilityMeasure σ] [NullSingletonClass σ]
    {L ε : ℝ} (hε : 0 < ε) (hεinv : ε < L⁻¹) (hCore : 1 ≤ L - ε)
    (hSupp : σ (Icc (L - ε) L)ᶜ = 0)
    (hSmooth : ContDiff ℝ (∞ : ℕ∞ω) (Isolated.avgCutoff σ)) :
    IsModulatedCutoff m L ε (fun x ↦ Isolated.avgCutoff σ ((m x).val : ℝ) -
      Isolated.avgCutoff (σ.map (Inv.inv : ℝ → ℝ)) ((m x).val : ℝ)) := by
  let a := L - ε
  let S := Isolated.avgCutoff σ
  let N (x : G) : ℝ := (m x).val
  let P (t : ℝ) : ℝ := S t + S t⁻¹ - 1
  let ρ (x : G) := S (N x) - Isolated.avgCutoff (σ.map (Inv.inv : ℝ → ℝ)) (N x)
  change IsModulatedCutoff m L ε ρ
  have ha1 : 1 ≤ a := hCore
  have ha : 0 < a := zero_lt_one.trans_le ha1
  have hL1 : 1 < L := by linarith
  have hL : 0 < L := zero_lt_one.trans hL1
  have hN : Continuous N := NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
  have hNp (x : G) : 0 < N x := NNReal.coe_pos.mpr (Units.zero_lt (m x))
  have hNinv (x : G) : N x⁻¹ = (N x)⁻¹ := by
    dsimp only [N]
    rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv]
  have hρ (x : G) : ρ x = P (N x) := by
    dsimp only [ρ, P, S]
    rw [avgCutoff_inverseRadiusLaw σ ha hSupp (hNp x)]
    ring
  have hOne (t : ℝ) (ht : t ≤ a) : S t = 1 :=
    Isolated.avgCutoff_eq_one σ hSupp ht
  have hZero (t : ℝ) (ht : L < t) : S t = 0 :=
    Isolated.avgCutoff_eq_zero σ hSupp ht
  have hGe (t : ℝ) (ht : 1 ≤ t) : P t = S t := by
    have ht' : t⁻¹ ≤ a := ((inv_le_one₀ (zero_lt_one.trans_le ht)).mpr ht).trans ha1
    dsimp only [P]
    rw [hOne _ ht', add_sub_cancel_right]
  have hLe (t : ℝ) (ht : t ≤ 1) : P t = S t⁻¹ := by
    dsimp only [P]
    rw [hOne _ (ht.trans ha1), add_comm (1 : ℝ), add_sub_cancel_right]
  have hPN (t : ℝ) : P t ∈ Icc (0 : ℝ) 1 := by
    rcases le_total (1 : ℝ) t with ht | ht
    · rw [hGe _ ht]
      exact ⟨Isolated.avgCutoff_nonneg σ _, Isolated.avgCutoff_le_one σ _⟩
    · rw [hLe _ ht]
      exact ⟨Isolated.avgCutoff_nonneg σ _, Isolated.avgCutoff_le_one σ _⟩
  have hPzero (t : ℝ) (ht : 0 < t) (htOut : t ∉ Icc L⁻¹ L) : P t = 0 := by
    by_cases htL : t ≤ L
    · have hlo : t < L⁻¹ := lt_of_not_ge fun h ↦ htOut ⟨h, htL⟩
      have hti : L < t⁻¹ := (lt_inv_comm₀ ht hL).mp hlo
      rw [hLe _ (hlo.le.trans ((inv_le_one₀ hL).mpr hL1.le)), hZero _ hti]
    · have hhi : L < t := lt_of_not_ge htL
      rw [hGe _ (hL1.le.trans hhi.le), hZero _ hhi]
  have hPone (t : ℝ) (ht : 0 < t) (hlo : a⁻¹ ≤ t) (hhi : t ≤ a) : P t = 1 := by
    have htInv : t⁻¹ ≤ a := by
      simpa only [inv_inv] using (inv_le_inv₀ ht (inv_pos.mpr ha)).mpr hlo
    dsimp only [P]
    rw [hOne _ hhi, hOne _ htInv]
    norm_num
  have hMargin : a⁻¹ ≤ L⁻¹ + ε := by
    have hprod : 1 ≤ a * L := by
      simpa only [one_mul] using (mul_le_mul ha1 hL1.le zero_le_one ha.le)
    have hdiff : a⁻¹ - L⁻¹ = ε / (a * L) := by
      field_simp [ha.ne', hL.ne']
      dsimp only [a]
      ring
    have hle : a⁻¹ - L⁻¹ ≤ ε := hdiff.trans_le (div_le_self hε.le hprod)
    linarith
  refine {
    radius_pos := hL
    width_pos := hε
    outer_left_sub_width_pos := sub_pos.mpr hεinv
    outer_left_sub_width_lt :=
      sub_lt_sub_right (((inv_le_one₀ hL).mpr hL1.le).trans_lt hL1) ε
    nonneg := ?_
    abs_le_one := ?_
    sup_eq_one := ?_
    profile := ?_
    inv_eq := ?_
    support_subset := ?_
    eq_one := ?_ }
  · intro x
    rw [hρ]
    exact (hPN _).1
  · intro x
    rw [hρ, abs_of_nonneg (hPN _).1]
    exact (hPN _).2
  · have hx : ρ 1 = 1 := by
      rw [hρ, show N (1 : G) = 1 by simp [N], hGe 1 le_rfl, hOne 1 ha1]
    have hm : (1 : ℝ) ∈ range ρ := ⟨1, hx⟩
    have hu : ∀ t ∈ range ρ, t ≤ (1 : ℝ) := by
      rintro _ ⟨x, rfl⟩
      rw [hρ]
      exact (hPN _).2
    exact le_antisymm (csSup_le ⟨1, hm⟩ hu) (le_csSup ⟨1, hu⟩ hm)
  · have hInv : ContDiffOn ℝ (∞ : ℕ∞ω) (Inv.inv : ℝ → ℝ) (Ioi 0) :=
      (contDiffOn_id : ContDiffOn ℝ (∞ : ℕ∞ω) (id : ℝ → ℝ) (Ioi 0)).inv
        (fun t ht ↦ (show 0 < t from ht).ne')
    have hSinv : ContDiffOn ℝ (∞ : ℕ∞ω) (fun t ↦ S t⁻¹) (Ioi 0) :=
      hSmooth.comp_contDiffOn hInv
    have hPS : ContDiffOn ℝ (∞ : ℕ∞ω) P (Ioi 0) :=
      (hSmooth.contDiffOn.add hSinv).sub contDiffOn_const
    refine ⟨P, ∅, hρ, by simp, ?_, ?_⟩
    · simpa using hPS
    · simp
  · intro x
    rw [hρ x, hρ x⁻¹, hNinv x]
    dsimp only [P]
    rw [inv_inv, add_comm (S (N x)) (S (N x)⁻¹)]
  · change closure (support ρ) ⊆ N ⁻¹' Icc L⁻¹ L
    apply closure_minimal _ (isClosed_Icc.preimage hN)
    intro x hx
    by_contra h
    exact (mem_support.mp hx) ((hρ x).trans (hPzero _ (hNp x) h))
  · intro x hx
    change N x ∈ Icc (L⁻¹ + ε) (L - ε) at hx
    change ρ x = 1
    rw [hρ]
    exact hPone _ (hNp x) (hMargin.trans hx.1) hx.2

end RiemannMasullo
