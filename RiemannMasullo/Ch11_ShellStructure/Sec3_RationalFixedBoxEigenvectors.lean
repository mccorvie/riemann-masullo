module
public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxRowAction

/-! # Actual cardinal eigenvectors in completed rational packets

Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496. Exact smooth fixed-box division
identifies every cardinal class as an eigenvector of the actual quotient circle
action. Continuous quotient rows separate these classes and prove independence.
This does not yet assert density of their span or a Schauder basis theorem.
-/

public noncomputable section
open Filter MeasureTheory Set Function FourierTransform
open scoped FourierTransform SchwartzMap Topology NNReal
namespace RiemannMasullo.RationalPacket

/-- A smooth even source whose normalized rows are concentrated at one integer
mode is an eigenvector modulo a genuine next-stage source, before completion. -/
theorem halfShift_mode_sub_mem_stageGenerators {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) {p : ℕ} (hp : p.Prime) (hpT : p ∉ T)
    (f : 𝓢(ℝ, ℂ)) (hf : f 0 = 0) (h0 : (𝓕 f) 0 = 0)
    (he : ∀ r, (𝓕 f) (-r) = (𝓕 f) r)
    (hb : ∀ r, X / (∏ q ∈ T, (q : ℝ)) < |r| → (𝓕 f) r = 0)
    (F : ℝ →₂[volume] ℂ) (hF : F =ᵐ[volume] stage T f) (n : ℤ)
    (hrows : ∀ j : ℤ, j ≠ n → packetRow X T p j F = 0) {h : ℝ} (hh : 0 ≤ h) :
    halfShift h F - (Real.fourierChar (-h * ((n : ℝ) / Real.log p)) : ℂ) • F ∈
      stageGenerators X (insert p T) := by
  let r := Real.exp (-h)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hh)
  let c : ℂ := Real.fourierChar (-h * ((n : ℝ) / Real.log p))
  let g := dilate r hr f - c • f
  have hfour (y : ℝ) : (𝓕 g) y = (r⁻¹ : ℝ) • (𝓕 f) (y/r) - c * (𝓕 f) y := by
    simp only [g, fourier_sub, fourier_smul, sub_apply, smul_apply,
      fourier_dilate hr, smul_eq_mul]
  have hg : g 0 = 0 := by simp [g, dilate_apply, hf]
  have hg0 : (𝓕 g) 0 = 0 := by simp [hfour, h0]
  have hge (y : ℝ) : (𝓕 g) (-y) = (𝓕 g) y := by
    rw [hfour, hfour, neg_div, he, he]
  have hgb : ∀ y : ℝ, X / (∏ q ∈ T, (q : ℝ)) < |y| → (𝓕 g) y = 0 := by
    intro y hy
    rw [hfour, hb y hy, hb (y/r), smul_zero, mul_zero, sub_self]
    rw [abs_div, abs_of_pos hr]
    exact hy.trans_le (le_div_self (abs_nonneg y) hr hr1)
  have hstage (x : ℝ) : stage T g x =
      stage T (dilate r hr f) x - c * stage T f x := by
    rw [show g = dilate r hr f - c • f from rfl, sub_eq_add_neg, ← neg_smul]
    rw [stage_add T (fun q hq ↦ (hT q hq).one_lt.le) _ _ (by simp [dilate_apply, hf]) (by simp [hf]),
      stage_smul]
    simp only [smul_eq_mul, neg_mul, sub_eq_add_neg]
  have hae : halfShift h F - c • F =ᵐ[volume] stage T g := by
    filter_upwards [Lp.coeFn_sub (halfShift h F) (c • F), Lp.coeFn_smul c F,
      halfShift_stage_ae h T f F hF, hF] with x hs hc ht hx
    rw [hs, Pi.sub_apply, hc, Pi.smul_apply, ht, hx, hstage, smul_eq_mul]
  apply (stageGenerators_insert_iff_packetRows_zero hX T hT hp hpT g hg hg0 hge hgb _ hae).mpr
  intro j
  rw [map_sub, map_smul, packetRow_halfShift hX T hT hp hpT hh
    (subset_closure ((mem_stageGenerators_iff X T F).mpr ⟨f, hf, h0, hb, hF⟩)) j]
  by_cases hj : j = n
  · subst j
    simp only [c, smul_eq_mul, sub_self]
  · rw [hrows j hj, mul_zero, smul_zero, sub_self]

/-- All cardinal modes survive as nonzero circle eigenvectors in the original
completed rational fixed-box quotient, with its actual continuous row maps. -/
theorem exists_fixedBox_eigen_cardinals {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT1 : ∀ q ∈ T, 1 ≤ q) (p : ℕ)
    (hTp1 : ∀ q ∈ insert p T, 1 ≤ q) (hT : ∀ q ∈ T, q.Prime)
    (hp : p.Prime) (hpT : p ∉ T) :
    ∃ v : ℤ → FixedBoxQuotient[X,T,hT1,p,hTp1],
      (∀ j n : ℤ, fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT j (v n) =
        if j = n then 1 else 0) ∧
      (∀ (s : AddCircle (Real.log p)) (n : ℤ),
        fixedBoxCircleAction T hT1 p hTp1 hX hp.one_lt s (v n) = _root_.fourier (-n) s • v n) ∧
      (∀ n, v n ≠ 0) ∧ LinearIndependent ℂ v := by
  classical
  let E := closedStageSubmodule X T hT1
  let D := (fixedBoxDenominator X T hT1 p hTp1).toSubmodule
  obtain ⟨V, hV, hrow⟩ := exists_fixedBox_biorthogonal_even_stage hX T hT hp hpT
  have hgen (n : ℤ) : V n ∈ stageGenerators X T := by
    obtain ⟨f, hf, h0, _, hb, hF⟩ := hV n
    exact (mem_stageGenerators_iff X T (V n)).mpr ⟨f, hf, h0, hb, hF⟩
  let w (n : ℤ) : E := ⟨V n, (mem_closedStageSubmodule_iff X T hT1 (V n)).mpr (subset_closure (hgen n))⟩
  let v (n : ℤ) := D.mkQL (w n)
  have hpair (j n : ℤ) : fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT j (v n) =
      if j = n then 1 else 0 := by
    rw [show v n = D.mkQL (w n) from rfl, fixedBoxPacketRow_mk]
    exact hrow j n
  refine ⟨v, hpair, ?_, ?_, ?_⟩
  · intro s n
    let : Fact (0 < Real.log (p : ℝ)) := ⟨Real.log_pos (by exact_mod_cast hp.one_lt)⟩
    obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico s
    rw [fixedBoxCircleAction_coe_of_mem T hT1 p hTp1 hX hp.one_lt ht]
    change fixedBoxForwardShift T hT1 p hTp1 hX t.toNNReal (D.mkQL (w n)) = _
    rw [fixedBoxForwardShift_mk, ← map_smul]
    apply (Submodule.Quotient.eq D).mpr
    apply (mem_fixedBoxDenominator_iff X T hT1 p hTp1 _).mpr
    apply (mem_closedStageSubmodule_iff X (insert p T) hTp1 _).mpr
    obtain ⟨f, hf, h0, he, hb, hF⟩ := hV n
    have hd := halfShift_mode_sub_mem_stageGenerators hX T hT hp hpT f hf h0 he hb (V n) hF n
      (fun j hj ↦ by simp only [hrow, ite_eq_right hj]) ht.1
    have hc : (Real.fourierChar (-t * ((n : ℝ) / Real.log p)) : ℂ) =
        _root_.fourier (-n) (t : AddCircle (Real.log p)) := by
      rw [Real.fourierChar_apply, _root_.fourier_coe_apply]
      congr 1
      push_cast
      ring
    rw [hc] at hd
    change halfShift (t.toNNReal : ℝ) (V n) -
      _root_.fourier (-n) (t : AddCircle (Real.log p)) • V n ∈
        closure (stageGenerators X (insert p T))
    rw [Real.coe_toNNReal _ ht.1]
    exact subset_closure hd
  · intro n hn
    have hz := hpair n n
    rw [hn, map_zero, ite_eq_left rfl] at hz
    exact zero_ne_one hz
  · apply LinearIndependent.of_pairwise_dual_eq_zero_one v
      (fun j ↦ (fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT j).toLinearMap)
    · intro i j hij
      simp only [ContinuousLinearMap.coe_coe, hpair, ite_eq_right hij]
    · intro i
      simp only [ContinuousLinearMap.coe_coe, hpair, ite_true]

end RiemannMasullo.RationalPacket
