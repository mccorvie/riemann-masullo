module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxProjections

/-! # Raw Mellin jet criteria for actual finite-prime theta descents

A finite prime column imposes its noncentral meshes and a consecutive block of
central jets. The half-density makes forward translation act by the binomial
formula on the raw zero-frequency jets. -/

public noncomputable section

open MeasureTheory Set
open scoped Topology
namespace RiemannMasullo.RationalPacket

/-- The closed stage obtained by adjoining a finite set of fresh primes is cut
out inside the old stage by their noncentral meshes and a consecutive block
of zero-frequency jets. The empty column imposes no conditions. -/
theorem mem_closedStageSubmodule_union_iff {X : ℝ} (hX : 0 < X)
    (T K : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) (hK : ∀ q ∈ K, q.Prime)
    (hd : Disjoint T K) (F : LogL2) :
    F ∈ closedStageSubmodule X (T ∪ K) (by
      intro q hq
      exact (Finset.mem_union.mp hq).elim (fun h ↦ (hT q h).one_lt.le)
        (fun h ↦ (hK q h).one_lt.le)) ↔
    F ∈ closedStageSubmodule X T (fun q hq ↦ (hT q hq).one_lt.le) ∧
      (∀ p ∈ K, ∀ n : ℤ, n ≠ 0 →
        halfLineMellinJet (-Real.log X) ((n : ℝ) / Real.log p) 0 F = 0) ∧
      (∀ d : ℕ, T.card ≤ d → d < T.card + K.card →
        halfLineMellinJet (-Real.log X) 0 d F = 0) := by
  classical
  simp only [mem_closedStageSubmodule_iff]
  revert hK hd
  induction K using Finset.induction_on with
  | empty =>
    intro _ _
    rw [Finset.union_empty, Finset.card_empty, Nat.add_zero]
    constructor
    · intro hF
      exact ⟨hF, by simp, fun _ hle hlt ↦ ((not_lt_of_ge hle) hlt).elim⟩
    · exact fun h ↦ h.1
  | @insert p K hpK ih =>
    intro hK' hd'
    have hK : ∀ q ∈ K, q.Prime := fun q hq ↦ hK' q (Finset.mem_insert_of_mem hq)
    have hp : p.Prime := hK' p (Finset.mem_insert_self ..)
    have hd : Disjoint T K := Finset.disjoint_left.mpr fun _ ht hk ↦
      Finset.disjoint_left.mp hd' ht (Finset.mem_insert_of_mem hk)
    have hpU : p ∉ T ∪ K := fun h ↦ (Finset.mem_union.mp h).elim
      (fun ht ↦ Finset.disjoint_left.mp hd' ht (Finset.mem_insert_self ..)) hpK
    have hU : ∀ q ∈ T ∪ K, q.Prime := fun q hq ↦
      (Finset.mem_union.mp hq).elim (hT q) (hK q)
    have hV : ∀ q ∈ insert p (T ∪ K), q.Prime := by
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hp
      · exact hU q hq
    have hc := Finset.card_union_of_disjoint hd
    rw [Finset.union_insert, Finset.card_insert_of_notMem hpK]
    constructor
    · intro hF
      have hprev := closure_mono (stageGenerators_insert_subset hX (T ∪ K)
        (fun q hq ↦ (hU q hq).one_lt.le) hp.one_lt.le) hF
      refine ⟨((ih hK hd).mp hprev).1, ?_, ?_⟩
      · intro q hq n _
        apply halfLineMellinJet_stage_closure_mesh hX _ hV _ n hF
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact Finset.mem_insert_self ..
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hq)
      · intro d _ hlt
        exact halfLineMellinJet_stage_closure_zero hX _ hV d (by
          rw [Finset.card_insert_of_notMem hpU, hc]; omega) hF
    · rintro ⟨hF, hm, hj⟩
      have hprev := (ih hK hd).mpr ⟨hF,
        fun q hq ↦ hm q (Finset.mem_insert_of_mem hq),
        fun d hle hlt ↦ hj d hle (by omega)⟩
      apply (mem_closedStageSubmodule_iff X (insert p (T ∪ K))
        (fun q hq ↦ (hV q hq).one_lt.le) F).mp
      apply (mem_nextClosedStage_iff_packetRows_zero (T ∪ K)
        (fun q hq ↦ (hU q hq).one_lt.le) p (fun q hq ↦ (hV q hq).one_lt.le)
        hX hp hpU hU F ((mem_closedStageSubmodule_iff X (T ∪ K)
          (fun q hq ↦ (hU q hq).one_lt.le) F).mpr hprev)).mpr
      intro n
      rw [packetRow_apply]
      by_cases hn : n = 0
      · rw [ite_eq_left hn, hj _ (by omega) (by omega), zero_div]
      · rw [ite_eq_right hn, hm p (Finset.mem_insert_self ..) n hn, zero_div]

/-- Membership in every `j`-column stage uses all meshes, but only `j`
additional central jets. The lower bound on `j` lets every prime appear in
some tested subset; the upper bound ensures that there is such a subset. -/
theorem mem_all_card_closedStageSubmodule_union_iff {X : ℝ} (hX : 0 < X)
    (T K : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) (hK : ∀ q ∈ K, q.Prime)
    (hd : Disjoint T K) {j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K.card) (F : LogL2) :
    (∀ A : Finset ℕ, ∀ hA : A ⊆ K, A.card = j →
      F ∈ closedStageSubmodule X (T ∪ A) (by
        intro q hq
        exact (Finset.mem_union.mp hq).elim (fun h ↦ (hT q h).one_lt.le)
          (fun h ↦ (hK q (hA h)).one_lt.le))) ↔
    F ∈ closedStageSubmodule X T (fun q hq ↦ (hT q hq).one_lt.le) ∧
      (∀ p ∈ K, ∀ n : ℤ, n ≠ 0 →
        halfLineMellinJet (-Real.log X) ((n : ℝ) / Real.log p) 0 F = 0) ∧
      (∀ d : ℕ, T.card ≤ d → d < T.card + j →
        halfLineMellinJet (-Real.log X) 0 d F = 0) := by
  have stage (A : Finset ℕ) (hA : A ⊆ K) := mem_closedStageSubmodule_union_iff hX T A hT
    (fun q hq ↦ hK q (hA hq)) (hd.mono_right hA) F
  constructor
  · intro hall
    obtain ⟨A, hA, hc⟩ := Finset.exists_subset_card_eq hjK
    obtain ⟨ht, _, hz⟩ := (stage A hA).mp (hall A hA hc)
    refine ⟨ht, ?_, by simpa only [hc] using hz⟩
    intro p hp
    obtain ⟨B, hpb, hb, hbc⟩ := Finset.exists_subsuperset_card_eq
      (Finset.singleton_subset_iff.mpr hp) (by simpa only [Finset.card_singleton] using hj) hjK
    exact ((stage B hb).mp (hall B hb hbc)).2.1 p (hpb (Finset.mem_singleton_self _))
  · rintro ⟨ht, hm, hz⟩ A hA hc
    exact (stage A hA).mpr ⟨ht, fun p hp ↦ hm p (hA hp), by simpa only [hc] using hz⟩

end RiemannMasullo.RationalPacket

open MeasureTheory Filter
open scoped FourierTransform

namespace RiemannMasullo.RationalPacket

/-- Nonnegative half-shifts preserve a fixed lower support edge. -/
theorem halfShift_ae_zero_below {a h : ℝ} (hh : 0 ≤ h) {F : LogL2}
    (hF : ∀ᵐ x ∂volume, x < a → F x = 0) :
    ∀ᵐ x ∂volume, x < a → halfShift h F x = 0 := by
  filter_upwards [halfShift_ae h F,
    (measurePreserving_add_right volume (-h)).quasiMeasurePreserving.ae hF] with x hx hback
  change x - h < a → F (x - h) = 0 at hback
  intro hxa
  rw [hx, hback (by linarith), mul_zero]

private theorem halfLineMellinJet_zero_integral {a : ℝ} {F : LogL2}
    (hF : ∀ᵐ x ∂volume, x < a → F x = 0) (d : ℕ) :
    halfLineMellinJet a 0 d F = ∫ x : ℝ, (x : ℂ)^d * (Real.exp (-x/2) : ℂ) * F x := by
  rw [halfLineMellinJet_apply a 0 d F hF, Real.fourier_real_eq]
  simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul]

/-- Raw Mellin jets at zero transform as ordinary moments: translation of the
polynomial is the only factor left after the two half-density weights cancel. -/
theorem halfLineMellinJet_halfShift {a h : ℝ} (hh : 0 ≤ h) {F : LogL2}
    (hF : ∀ᵐ x ∂volume, x < a → F x = 0) (d : ℕ) :
    halfLineMellinJet a 0 d (halfShift h F) = ∑ i ∈ Finset.range (d + 1),
      (d.choose i : ℂ) * (h : ℂ)^(d-i) * halfLineMellinJet a 0 i F := by
  let M (i : ℕ) (x : ℝ) : ℂ := (x : ℂ)^i * (Real.exp (-x/2) : ℂ) * F x
  let c (i : ℕ) : ℂ := (d.choose i : ℂ) * (h : ℂ)^(d-i)
  let G (x : ℝ) : ℂ := (x : ℂ)^d * (Real.exp (-x/2) : ℂ) *
    ((Real.exp (h/2) : ℂ) * F (x-h))
  have hsum (x : ℝ) : G (x+h) = ∑ i ∈ Finset.range (d+1), c i * M i x := by
    have he : (Real.exp (-(x+h)/2) : ℂ) * (Real.exp (h/2) : ℂ) = Real.exp (-x/2) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      congr 2; ring
    dsimp only [G]
    rw [add_sub_cancel_right, Complex.ofReal_add, add_pow]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    dsimp only [c, M]
    rw [← he]
    ring
  calc
    _ = ∫ x, G x := by
      rw [halfLineMellinJet_zero_integral (halfShift_ae_zero_below hh hF)]
      apply integral_congr_ae
      filter_upwards [halfShift_ae h F] with x hx
      simp only [G, hx]
    _ = ∫ x, G (x+h) := (integral_add_right_eq_self G h).symm
    _ = ∑ i ∈ Finset.range (d+1), c i * ∫ x, M i x := by
      simp_rw [hsum]
      rw [integral_finsetSum _ fun i _ ↦ (halfLineMellin_moment_integrable a i F hF).const_mul (c i)]
      simp_rw [integral_const_mul]
      rfl
    _ = _ := by simp only [halfLineMellinJet_zero_integral hF, c, M]

/-- Subtracting the unshifted vector cancels the top diagonal exactly. -/
theorem halfLineMellinJet_halfShift_sub {a h : ℝ} (hh : 0 ≤ h) {F : LogL2}
    (hF : ∀ᵐ x ∂volume, x < a → F x = 0) (d : ℕ) :
    halfLineMellinJet a 0 d (halfShift h F - F) = ∑ i ∈ Finset.range d,
      (d.choose i : ℂ) * (h : ℂ)^(d-i) * halfLineMellinJet a 0 i F := by
  rw [map_sub, halfLineMellinJet_halfShift hh hF, Finset.sum_range_succ]
  simp

/-- A first nonvanishing jet of order `r` moves up to order `r+1` under a
positive half-shift difference; the new leading coefficient is explicit. -/
theorem halfLineMellinJet_halfShift_sub_leading {a h : ℝ} (hh : 0 ≤ h) {F : LogL2}
    (hF : ∀ᵐ x ∂volume, x < a → F x = 0) {r : ℕ}
    (hj : ∀ i < r, halfLineMellinJet a 0 i F = 0) :
    (∀ j ≤ r, halfLineMellinJet a 0 j (halfShift h F - F) = 0) ∧
      halfLineMellinJet a 0 (r+1) (halfShift h F - F) =
        ((r+1 : ℕ) : ℂ) * (h : ℂ) * halfLineMellinJet a 0 r F := by
  constructor
  · intro j hjr
    rw [halfLineMellinJet_halfShift_sub hh hF]
    exact Finset.sum_eq_zero fun i hi ↦ by simp [hj i ((Finset.mem_range.mp hi).trans_le hjr)]
  · rw [halfLineMellinJet_halfShift_sub hh hF, Finset.sum_range_succ,
      Finset.sum_eq_zero (fun i hi ↦ by rw [hj i (Finset.mem_range.mp hi), mul_zero])]
    simp [Nat.choose_succ_self_right]

end RiemannMasullo.RationalPacket
