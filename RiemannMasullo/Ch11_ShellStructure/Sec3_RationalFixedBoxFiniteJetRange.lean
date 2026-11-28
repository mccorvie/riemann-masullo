module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxFiniteJets
public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxBasis

/-! # Actual central jet range for finite-prime stage intersections

Successive normalized period averages annihilate the noncentral meshes of a
genuine fixed-box source and preserve its first central jet. Shift differences
then build a triangular jet family and realize every admissible jet tuple. -/

public noncomputable section
open MeasureTheory Set
open scoped Topology NNReal
namespace RiemannMasullo.RationalPacket

/-- A genuine even source in the unchanged Fourier box kills all fresh
noncentral meshes simultaneously without losing its leading central jet. -/
theorem exists_fixedBox_mesh_zero_leading_jet_ne_zero {X : ℝ} (hX : 0 < X)
    (T K : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) (hK : ∀ q ∈ K, q.Prime)
    (hd : Disjoint T K) (hne : K.Nonempty) :
    ∃ f : (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule,
      let F := fixedBoxSourceStage hX T (fun q hq ↦ (hT q hq).one_lt.le) f
      (∀ p ∈ K, ∀ n : ℤ, n ≠ 0 →
        halfLineMellinJet (-Real.log X) ((n : ℝ) / Real.log p) 0 F = 0) ∧
      halfLineMellinJet (-Real.log X) 0 T.card F ≠ 0 := by
  classical
  let hT1 := fun q (hq : q ∈ T) ↦ (hT q hq).one_lt.le
  let B := (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule
  let A := fixedBoxSourceStage hX T hT1
  let E := closedStageSubmodule X T hT1
  let S := fixedBoxSourceClosedStage T hT1 hX
  have hcoe (f : B) : (S f : LogL2) = A f := fixedBoxSourceClosedStage_coe T hT1 hX f
  let J := halfLineMellinJet (-Real.log X) 0 T.card
  have fresh (p : ℕ) (hp : p ∈ K) : p ∉ T := fun ht ↦ Finset.disjoint_left.mp hd ht hp
  have ins (p : ℕ) (hp : p ∈ K) : ∀ q ∈ insert p T, 1 ≤ q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact (hK q hp).one_lt.le
    · exact hT1 q hq
  obtain ⟨p₀, hp₀⟩ := hne
  obtain ⟨v, hv⟩ := exists_fixedBox_source_cardinals T hT1 p₀ (ins p₀ hp₀) hX
    (hK p₀ hp₀) (fresh p₀ hp₀) hT
  have hj₀ : J (A (v 0)) ≠ 0 := by
    intro hz
    have he := hv 0 0
    rw [fixedBoxSourceQuotient_apply, fixedBoxPacketRow_mk, fixedBoxSourceClosedStage_coe,
      packetRow_apply] at he
    change halfLineMellinJet (-Real.log X) 0 T.card (fixedBoxSourceStage hX T hT1 (v 0)) = 0 at hz
    simp [hz] at he
  have build (M : Finset ℕ) (hM : M ⊆ K) : ∃ f : B,
      (∀ p ∈ M, ∀ n : ℤ, n ≠ 0 → packetRow X T p n (A f) = 0) ∧ J (A f) ≠ 0 := by
    induction M using Finset.induction_on with
    | empty => exact ⟨v 0, by simp, hj₀⟩
    | @insert p M hpM ih =>
      have hp := hM (Finset.mem_insert_self p M)
      obtain ⟨f, hm, hj⟩ := ih (fun q hq ↦ hM (Finset.mem_insert_of_mem hq))
      let L := Real.log (p : ℝ)
      let c : ℂ := ((L⁻¹ : ℝ) : ℂ)
      have hL : 0 < L := Real.log_pos (by exact_mod_cast (hK p hp).one_lt)
      obtain ⟨g, hg⟩ := exists_fixedBox_stage_average hX T hT1 L (fun _ ↦ c) continuous_const f
      have hi : IntegrableOn (fun t : ℝ ↦ c • halfShift t (A f)) (Icc 0 L) :=
        ((continuous_halfShift (A f)).const_smul c).integrableOn_Icc
      have hcl := (mem_closedStageSubmodule_iff X T hT1 _).mp (S f).property
      have hs := closedStageSubmodule_supported hX T hT1 (S f).property
      have avg (ℓ : LogL2 →L[ℂ] ℂ) : ℓ (A g) = ∫ t in Icc 0 L, c * ℓ (halfShift t (A f)) := by
        change ℓ (fixedBoxSourceStage hX T hT1 g) = _
        rw [hg, ← ℓ.integral_comp_comm hi]; simp only [map_smul, smul_eq_mul]
      refine ⟨g, ?_, ?_⟩
      · intro q hq n hn
        rcases Finset.mem_insert.mp hq with heq | hq
        · subst q
          let D := (fixedBoxDenominator X T hT1 p (ins p hp)).toSubmodule
          let a (t : ℝ) : E := c • closedStageForwardShift T hT1 hX t.toNNReal (S f)
          let : IsClosed (E.toSubmodule : Set LogL2) := E.isClosed
          have ha : Continuous a :=
            (show Continuous (fun _ : ℝ ↦ c) from continuous_const).smul
              (((continuous_halfShift (S f : LogL2)).comp
                (NNReal.continuous_coe.comp continuous_real_toNNReal)).subtype_mk _)
          have hai : IntegrableOn a (Icc 0 L) := ha.integrableOn_Icc
          have he : S g = ∫ t in Icc 0 L, a t := by
            apply Subtype.ext
            rw [hcoe g]
            change fixedBoxSourceStage hX T hT1 g = E.toSubmodule.subtypeL (∫ t in Icc 0 L, a t)
            rw [hg, ← E.toSubmodule.subtypeL.integral_comp_comm hai]
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
            change c • halfShift t (A f) = c • halfShift (t.toNNReal : ℝ) (S f : LogL2)
            rw [Real.coe_toNNReal _ ht.1, fixedBoxSourceClosedStage_coe]
          have hproj : fixedBoxSourceQuotient T hT1 p (ins p hp) hX g =
              fixedBoxFourierProjection T hT1 p (ins p hp) hX (hK p hp) (fresh p hp) 0
                (fixedBoxSourceQuotient T hT1 p (ins p hp) hX f) := by
            rw [fixedBoxFourierProjection_eq_interval, fixedBoxSourceQuotient_apply]
            change D.mkQL (S g) = _
            rw [he, ← D.mkQL.integral_comp_comm hai]
            apply integral_congr_ae
            filter_upwards with t
            simp only [a, map_smul, fixedBoxSourceQuotient_apply, fixedBoxForwardShift_mk,
              _root_.fourier_zero, mul_one]
            rfl
          have hr := fixedBoxPacketRow_fourierProjection T hT1 p (ins p hp) hX (hK p hp)
            (fresh p hp) hT n 0 (fixedBoxSourceQuotient T hT1 p (ins p hp) hX f)
          rw [← hproj, ite_eq_right hn, fixedBoxSourceQuotient_apply, fixedBoxPacketRow_mk] at hr
          simpa only [fixedBoxSourceClosedStage_coe] using hr
        · rw [avg]
          apply integral_eq_zero_of_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          change c * packetRow X T q n (halfShift t (A f)) = 0
          rw [← hcoe f]
          rw [packetRow_halfShift hX T hT (hK q (hM (Finset.mem_insert_of_mem hq)))
            (fresh q (hM (Finset.mem_insert_of_mem hq))) ht.1 hcl,
            show packetRow X T q n (S f : LogL2) = 0 by rw [hcoe f]; exact hm q hq n hn,
            mul_zero, mul_zero]
      · rw [avg]
        have hjt (t : ℝ) (ht : 0 ≤ t) : J (halfShift t (A f)) = J (A f) := by
          dsimp only [J]
          rw [← hcoe f]
          rw [halfLineMellinJet_halfShift ht hs, Finset.sum_range_succ,
            Finset.sum_eq_zero (fun i hi ↦ by rw [halfLineMellinJet_stage_closure_zero hX T hT i
              (Finset.mem_range.mp hi) hcl, mul_zero])]
          simp
        have he : (∫ t in Icc 0 L, c * J (halfShift t (A f))) = ∫ _ in Icc 0 L, c * J (A f) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          rw [hjt t ht.1]
        rw [he, setIntegral_const, Real.volume_real_Icc_of_le hL.le, sub_zero,
          Complex.real_smul, ← mul_assoc]
        simpa [c, hL.ne'] using hj
  obtain ⟨f, hf, hj⟩ := build K (Finset.Subset.refl _)
  refine ⟨f, fun p hp n hn ↦ ?_, hj⟩
  have hr := hf p hp n hn
  rw [packetRow_apply, ite_eq_right hn, div_eq_zero_iff] at hr
  exact hr.resolve_right (prime_mesh_euler_prod_ne_zero T (hK p hp) (fresh p hp) hT hn)

/-- A triangular family in a submodule realizes arbitrary finite row data. -/
theorem exists_of_triangular_rows {V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Submodule ℂ V) (L : ℕ → V →ₗ[ℂ] ℂ) (N : ℕ)
    (h : ∀ n < N, ∃ w ∈ S, (∀ i < n, L i w = 0) ∧ L n w ≠ 0)
    (y : Fin N → ℂ) : ∃ u ∈ S, ∀ i : Fin N, L i.val u = y i := by
  classical
  have build (n : ℕ) (hn : n ≤ N) : ∃ u ∈ S, ∀ (i : Fin N), i.val < n → L i.val u = y i := by
    induction n with
    | zero => exact ⟨0, S.zero_mem, fun i hi ↦ (Nat.not_lt_zero _ hi).elim⟩
    | succ n ih =>
      obtain ⟨u, hu, hprev⟩ := ih (by omega)
      obtain ⟨w, hw, hlow, hdiag⟩ := h n (by omega)
      let c := (y ⟨n, by omega⟩ - L n u) / L n w
      refine ⟨u + c • w, S.add_mem hu (S.smul_mem c hw), ?_⟩
      intro i hi
      rw [map_add, map_smul, smul_eq_mul]
      by_cases hil : i.val < n
      · simp [hlow _ hil, hprev i hil]
      · obtain ⟨i, hiN⟩ := i
        change i < n + 1 at hi
        change ¬i < n at hil
        obtain rfl : i = n := by omega
        dsimp only [c, Fin.val_mk]
        rw [div_mul_cancel₀ _ hdiag]
        ring
  obtain ⟨u, hu, huv⟩ := build N le_rfl
  exact ⟨u, hu, fun i ↦ huv i i.isLt⟩

/-- Within the actual earlier stage, the noncentral meshes remain zero under
successive shift differences, while the first nonzero central jet rises by one. -/
theorem exists_mesh_zero_with_first_jet {X : ℝ} (hX : 0 < X)
    (T K : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) (hK : ∀ p ∈ K, p.Prime)
    (hd : Disjoint T K) {F : LogL2}
    (hF : F ∈ closedStageSubmodule X T (fun q hq ↦ (hT q hq).one_lt.le))
    (hm : ∀ p ∈ K, ∀ n : ℤ, n ≠ 0 →
      halfLineMellinJet (-Real.log X) ((n : ℝ) / Real.log p) 0 F = 0)
    (ht : halfLineMellinJet (-Real.log X) 0 T.card F ≠ 0) (r : ℕ) :
    ∃ w ∈ closedStageSubmodule X T (fun q hq ↦ (hT q hq).one_lt.le),
      (∀ p ∈ K, ∀ n : ℤ, n ≠ 0 →
        halfLineMellinJet (-Real.log X) ((n : ℝ) / Real.log p) 0 w = 0) ∧
      (∀ d < T.card + r, halfLineMellinJet (-Real.log X) 0 d w = 0) ∧
      halfLineMellinJet (-Real.log X) 0 (T.card + r) w ≠ 0 := by
  have hT' : ∀ q ∈ T, 1 ≤ q := fun q hq ↦ (hT q hq).one_lt.le
  induction r with
  | zero =>
    simp only [Nat.add_zero]
    exact ⟨F, hF, hm, fun d hd' ↦ halfLineMellinJet_stage_closure_zero hX T hT d hd'
      ((mem_closedStageSubmodule_iff X T hT' F).mp hF), ht⟩
  | succ r ih =>
    obtain ⟨w, hw, hm', hz, hnz⟩ := ih
    have h1 : (0 : ℝ) ≤ 1 := zero_le_one
    obtain ⟨hlow, hlead⟩ := halfLineMellinJet_halfShift_sub_leading h1
      (closedStageSubmodule_supported hX T hT' hw) hz
    refine ⟨halfShift 1 w - w, (closedStageSubmodule X T hT').sub_mem
      (halfShift_mem_closedStage hX T hT' h1 hw) hw, ?_, fun d h ↦ hlow d (by omega), ?_⟩
    · intro p hp n hn
      have hpT : p ∉ T := fun hp' ↦ Finset.disjoint_left.mp hd hp' hp
      have ha := packetRow_halfShift hX T hT (hK p hp) hpT h1
        ((mem_closedStageSubmodule_iff X T hT' w).mp hw) n
      simp only [packetRow_apply, ite_eq_right hn, hm' p hp n hn, zero_div, mul_zero] at ha
      rw [map_sub, hm' p hp n hn, sub_zero]
      exact (div_eq_zero_iff.mp ha).resolve_right (prime_mesh_euler_prod_ne_zero T (hK p hp) hpT hT hn)
    · rw [Nat.add_succ, hlead]
      exact mul_ne_zero (mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero (T.card + r))
        (by norm_num)) hnz

/-- Every prescribed finite central jet block occurs on an actual vector
belonging to every `j`-column stage. -/
theorem exists_all_card_stage_with_jets {X : ℝ} (hX : 0 < X)
    (T K : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) (hK : ∀ p ∈ K, p.Prime)
    (hd : Disjoint T K) {j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K.card) {F : LogL2}
    (hF : F ∈ closedStageSubmodule X T (fun q hq ↦ (hT q hq).one_lt.le))
    (hm : ∀ p ∈ K, ∀ n : ℤ, n ≠ 0 →
      halfLineMellinJet (-Real.log X) ((n : ℝ) / Real.log p) 0 F = 0)
    (ht : halfLineMellinJet (-Real.log X) 0 T.card F ≠ 0) (y : Fin (K.card-j) → ℂ) :
    ∃ u : LogL2, (∀ A : Finset ℕ, ∀ hA : A ⊆ K, A.card = j →
      u ∈ closedStageSubmodule X (T ∪ A) (by
        intro q hq
        exact (Finset.mem_union.mp hq).elim (fun h ↦ (hT q h).one_lt.le)
          (fun h ↦ (hK q (hA h)).one_lt.le))) ∧
      ∀ i : Fin (K.card-j), halfLineMellinJet (-Real.log X) 0 (T.card+j+i.val) u = y i := by
  let S : Submodule ℂ LogL2 := ⨅ (A : Finset ℕ) (hA : A ⊆ K) (_ : A.card = j),
    (closedStageSubmodule X (T ∪ A) (by
      intro q hq
      exact (Finset.mem_union.mp hq).elim (fun h ↦ (hT q h).one_lt.le)
        (fun h ↦ (hK q (hA h)).one_lt.le))).toSubmodule
  let L (n : ℕ) := (halfLineMellinJet (-Real.log X) 0 (T.card+j+n)).toLinearMap
  obtain ⟨u, hu, hy⟩ := exists_of_triangular_rows S L (K.card-j) (by
    intro n _
    obtain ⟨w, hw, hmesh, hlow, hdiag⟩ := exists_mesh_zero_with_first_jet hX T K hT hK hd hF hm ht (j+n)
    refine ⟨w, ?_, fun i hi ↦ hlow _ (by omega), ?_⟩
    · simp only [S, Submodule.mem_iInf]
      exact (mem_all_card_closedStageSubmodule_union_iff hX T K hT hK hd hj hjK w).mpr
        ⟨hw, hmesh, fun d _ hd' ↦ hlow d (by omega)⟩
    · simpa only [L, ContinuousLinearMap.coe_coe, Nat.add_assoc] using hdiag) y
  simp only [S, Submodule.mem_iInf] at hu
  exact ⟨u, fun A hA hAj ↦ hu A hA hAj, hy⟩

/-- Every allowed jet tuple is attained in the actual finite-column intersection. -/
theorem exists_all_card_stage_with_jets_unconditional {X : ℝ} (hX : 0 < X)
    (T K : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) (hK : ∀ p ∈ K, p.Prime)
    (hd : Disjoint T K) {j : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K.card)
    (y : Fin (K.card - j) → ℂ) :
    ∃ u : LogL2, (∀ A : Finset ℕ, ∀ hA : A ⊆ K, A.card = j →
      u ∈ closedStageSubmodule X (T ∪ A) (by
        intro q hq
        exact (Finset.mem_union.mp hq).elim (fun h ↦ (hT q h).one_lt.le)
          (fun h ↦ (hK q (hA h)).one_lt.le))) ∧
      ∀ i : Fin (K.card - j), halfLineMellinJet (-Real.log X) 0 (T.card + j + i.val) u = y i := by
  let hT1 := fun q (hq : q ∈ T) ↦ (hT q hq).one_lt.le
  have hn : K.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one (hj.trans hjK))
  obtain ⟨f, hm, ht⟩ := exists_fixedBox_mesh_zero_leading_jet_ne_zero hX T K hT hK hd hn
  have hs : fixedBoxSourceStage hX T hT1 f ∈ closedStageSubmodule X T hT1 := by
    rw [← fixedBoxSourceClosedStage_coe T hT1 hX f]
    exact (fixedBoxSourceClosedStage T hT1 hX f).property
  exact exists_all_card_stage_with_jets hX T K hT hK hd hj hjK hs hm ht y

end RiemannMasullo.RationalPacket
