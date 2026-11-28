module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxSourceAverages

/-! # Rank-one circle projections and totality in completed rational packets

Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496. Following fpet19's written
periodization construction (#7351, comment 7149080501), this proves completeness
of the actual cardinal modes in the original closed-stage quotient. Source-preserving
averages and exact smooth division identify the circle Fourier projections as rank
one; scalar Fourier uniqueness then gives totality and the exact completed row kernel.
No auxiliary coordinate quotient or backwards fixed-box invariance is assumed.
-/

public noncomputable section
open Filter MeasureTheory Set Function FourierTransform
open scoped FourierTransform SchwartzMap Topology NNReal
namespace RiemannMasullo.RationalPacket

variable {X : ℝ} (T : Finset ℕ) (hT1 : ∀ q ∈ T, 1 ≤ q)
variable (p : ℕ) (hTp1 : ∀ q ∈ insert p T, 1 ≤ q) (hX : 0 < X)
variable (hp : p.Prime) (hpT : p ∉ T)
local notation "L" => Real.log (p : ℝ)
local notation "Q" => FixedBoxQuotient[X,T,hT1,p,hTp1]
local notation "ρ" => fixedBoxCircleAction T hT1 p hTp1 hX hp.one_lt

include hpT in
private theorem packetOrbit_integrable (u : Q) :
    letI : Fact (0 < L) := ⟨Real.log_pos (by exact_mod_cast hp.one_lt)⟩
    Integrable (fun s : AddCircle L ↦ ρ s u) AddCircle.haarAddCircle := by
  let : Fact (0 < L) := ⟨Real.log_pos (by exact_mod_cast hp.one_lt)⟩
  exact (continuous_fixedBoxCircleAction T hT1 p hTp1 hX hp.one_lt hpT u).integrable_of_hasCompactSupport
    (.of_compactSpace _)

/-- Fourier projection onto the character indexed by normalized row `n`. -/
def fixedBoxFourierProjection (hpT : p ∉ T) (n : ℤ) : Q →L[ℂ] Q := by
  let : Fact (0 < L) := ⟨Real.log_pos (by exact_mod_cast hp.one_lt)⟩
  let A : Q →ₗ[ℂ] Q := {
    toFun := fun u ↦ _root_.fourierCoeff (fun s : AddCircle L ↦ ρ s u) (-n)
    map_add' := by
      intro u v
      simpa only [map_add, Pi.add_def] using congrFun (_root_.fourierCoeff.add (packetOrbit_integrable T hT1 p hTp1 hX hp hpT u)
        (packetOrbit_integrable T hT1 p hTp1 hX hp hpT v)) (-n)
    map_smul' := by
      intro c u
      simpa only [map_smul, RingHom.id_apply, Pi.smul_def] using _root_.fourierCoeff.const_smul (fun s : AddCircle L ↦ ρ s u) c (-n) }
  refine A.mkContinuous (Real.sqrt p) (fun u ↦ ?_)
  change ‖∫ s : AddCircle L, _root_.fourier (- -n) s • ρ s u ∂AddCircle.haarAddCircle‖ ≤ _
  have hb : ∀ᵐ s : AddCircle L ∂AddCircle.haarAddCircle,
      ‖_root_.fourier (- -n) s • ρ s u‖ ≤ Real.sqrt p * ‖u‖ := by
    filter_upwards with s
    rw [norm_smul, _root_.fourier_apply, Circle.norm_coe, one_mul]
    exact ((ρ s).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (norm_fixedBoxCircleAction_le T hT1 p hTp1 hX hp.one_lt s) (norm_nonneg u))
  simpa using norm_integral_le_of_norm_le_const hb

/-- The projection uses the actual strongly continuous circle orbit. -/
theorem fixedBoxFourierProjection_apply (n : ℤ) (u : Q) :
    fixedBoxFourierProjection T hT1 p hTp1 hX hp hpT n u =
      letI : Fact (0 < L) := ⟨Real.log_pos (by exact_mod_cast hp.one_lt)⟩
      _root_.fourierCoeff (fun s : AddCircle L ↦ ρ s u) (-n) := by rfl

/-- In a period cell the same projection averages actual forward shifts. -/
theorem fixedBoxFourierProjection_eq_interval (n : ℤ) (u : Q) :
    fixedBoxFourierProjection T hT1 p hTp1 hX hp hpT n u =
      ∫ t in Icc 0 L, (((L⁻¹ : ℝ) : ℂ) * _root_.fourier n (t : AddCircle L)) •
        fixedBoxForwardShift T hT1 p hTp1 hX t.toNNReal u := by
  let : Fact (0 < L) := ⟨Real.log_pos (by exact_mod_cast hp.one_lt)⟩
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [fixedBoxFourierProjection_apply, _root_.fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [zero_add, neg_neg, one_div]
  rw [intervalIntegral.integral_of_le hL.le, ← integral_Icc_eq_integral_Ioc]
  trans ∫ t in Icc 0 L, (L⁻¹ : ℝ) • (_root_.fourier n (t : AddCircle L) • ρ (t : AddCircle L) u)
  · convert! (integral_smul (μ := volume.restrict (Icc 0 L)) (L⁻¹)
      (fun t : ℝ ↦ _root_.fourier n (t : AddCircle L) • ρ (t : AddCircle L) u)).symm
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [fixedBoxCircleAction_coe T hT1 p hTp1 hX hp.one_lt hpT ht.1]
  simp only [← smul_assoc, Complex.real_smul]

/-- A circle projection keeps precisely its own normalized coordinate. -/
theorem fixedBoxPacketRow_fourierProjection (hT : ∀ q ∈ T, q.Prime)
    (j n : ℤ) (u : Q) :
    fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT j
      (fixedBoxFourierProjection T hT1 p hTp1 hX hp hpT n u) =
        if j = n then fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT j u else 0 := by
  classical
  let : Fact (0 < L) := ⟨Real.log_pos (by exact_mod_cast hp.one_lt)⟩
  let ℓ := fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT j
  rw [fixedBoxFourierProjection_apply, _root_.fourierCoeff]
  change ℓ (∫ s : AddCircle L, _root_.fourier (- -n) s • ρ s u ∂AddCircle.haarAddCircle) = _
  rw [← ℓ.integral_comp_comm ((packetOrbit_integrable T hT1 p hTp1 hX hp hpT u).fourier_smul (- -n))]
  simp_rw [map_smul]
  dsimp only [ℓ]
  simp_rw [fixedBoxPacketRow_circleAction, smul_eq_mul]
  have he : (fun s : AddCircle L ↦ _root_.fourier (- -n) s *
      (_root_.fourier (-j) s * ℓ u)) =
      (fun s ↦ ℓ u * (_root_.fourier (- -n) s * _root_.fourier (-j) s)) := by
    funext s
    ring
  rw [he, integral_const_mul]
  change ℓ u * _root_.fourierCoeff (_root_.fourier (-j)) (-n) = _
  rw [_root_.fourierCoeff_fourier]
  by_cases hj : j = n
  · subst j
    simp [ℓ]
  · simp [hj, Ne.symm hj]

/-- The continuous source-stage map with its genuine closed-stage codomain. -/
def fixedBoxSourceClosedStage :
    (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule →L[ℂ]
      closedStageSubmodule X T hT1 :=
  (fixedBoxSourceStage hX T hT1).codRestrict (closedStageSubmodule X T hT1).toSubmodule (by
    intro f
    obtain ⟨hf, h0, _, hb⟩ := (mem_fixedBoxEvenSources _ f).mp f.property
    apply (mem_closedStageSubmodule_iff X T hT1 _).mpr
    exact subset_closure ((mem_stageGenerators_iff X T _).mpr
      ⟨f, hf, h0, hb, fixedBoxSourceStage_ae hX T hT1 f⟩))

theorem fixedBoxSourceClosedStage_coe
    (f : (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule) :
    (fixedBoxSourceClosedStage T hT1 hX f : LogL2) = fixedBoxSourceStage hX T hT1 f := by rfl

/-- The actual source map into the completed relative packet. -/
def fixedBoxSourceQuotient :
    (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule →L[ℂ] Q :=
  (fixedBoxDenominator X T hT1 p hTp1).toSubmodule.mkQL.comp
    (fixedBoxSourceClosedStage T hT1 hX)

theorem fixedBoxSourceQuotient_apply
    (f : (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule) :
    fixedBoxSourceQuotient T hT1 p hTp1 hX f =
      (fixedBoxDenominator X T hT1 p hTp1).toSubmodule.mkQL
        (fixedBoxSourceClosedStage T hT1 hX f) := by rfl

/-- Averaging in the quotient is represented by averaging genuine sources in
exactly the original polar even Fourier box. -/
theorem exists_fixedBox_quotient_average (b : ℝ) (w : ℝ → ℂ) (hw : Continuous w)
    (f : (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule) :
    ∃ g : (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule,
      fixedBoxSourceQuotient T hT1 p hTp1 hX g = ∫ t in Icc 0 b,
        w t • fixedBoxForwardShift T hT1 p hTp1 hX t.toNNReal
          (fixedBoxSourceQuotient T hT1 p hTp1 hX f) := by
  let E := closedStageSubmodule X T hT1
  let D := (fixedBoxDenominator X T hT1 p hTp1).toSubmodule
  let A := fixedBoxSourceClosedStage T hT1 hX
  let : IsClosed (E.toSubmodule : Set LogL2) := E.isClosed
  let a (t : ℝ) : E := w t • closedStageForwardShift T hT1 hX t.toNNReal (A f)
  have ha : Continuous a := hw.smul
    (((continuous_halfShift (A f : LogL2)).comp
      (NNReal.continuous_coe.comp continuous_real_toNNReal)).subtype_mk _)
  have hi : IntegrableOn a (Icc 0 b) := ha.integrableOn_Icc
  obtain ⟨g, hg⟩ := exists_fixedBox_stage_average hX T hT1 b w hw f
  have he : A g = ∫ t in Icc 0 b, a t := by
    apply Subtype.ext
    change fixedBoxSourceStage hX T hT1 g = E.toSubmodule.subtypeL (∫ t in Icc 0 b, a t)
    rw [hg, ← E.toSubmodule.subtypeL.integral_comp_comm hi]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    change w t • halfShift t (fixedBoxSourceStage hX T hT1 f) =
      w t • halfShift (t.toNNReal : ℝ) (A f : LogL2)
    rw [Real.coe_toNNReal _ ht.1, fixedBoxSourceClosedStage_coe]
  refine ⟨g, ?_⟩
  rw [fixedBoxSourceQuotient_apply]
  change D.mkQL (A g) = _
  rw [he, ← D.mkQL.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards with t
  simp only [a, map_smul, fixedBoxSourceQuotient_apply, fixedBoxForwardShift_mk]
  rfl

/-- Every Fourier projection of a genuine smooth source has a genuine smooth
source representative in the same box. -/
theorem exists_fixedBox_projection_source (n : ℤ)
    (f : (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule) :
    ∃ g : (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule,
      fixedBoxSourceQuotient T hT1 p hTp1 hX g =
        fixedBoxFourierProjection T hT1 p hTp1 hX hp hpT n
          (fixedBoxSourceQuotient T hT1 p hTp1 hX f) := by
  obtain ⟨g, hg⟩ := exists_fixedBox_quotient_average T hT1 p hTp1 hX L
    (fun t : ℝ ↦ ((L⁻¹ : ℝ) : ℂ) * _root_.fourier n (t : AddCircle L))
    (continuous_const.mul ((map_continuous (_root_.fourier n)).comp (AddCircle.continuous_mk' L))) f
  exact ⟨g, hg.trans (fixedBoxFourierProjection_eq_interval T hT1 p hTp1 hX hp hpT n _).symm⟩

/-- Evenization loses no theta-stage vectors; the source map has dense range
in the actual closed preceding stage. -/
theorem fixedBoxSourceClosedStage_denseRange :
    DenseRange (fixedBoxSourceClosedStage T hT1 hX) := by
  intro u
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  change (u : LogL2) ∈ closure
    (Subtype.val '' range (fixedBoxSourceClosedStage T hT1 hX))
  apply closure_mono ?_ ((mem_closedStageSubmodule_iff X T hT1 _).mp u.property)
  intro F hF
  obtain ⟨f, hf, h0, hb, hae⟩ := (mem_stageGenerators_iff X T F).mp hF
  obtain ⟨g, hg, hg0, hge, hgb, hgs⟩ := exists_even_source_same_stage T hT1
    (X / (∏ q ∈ T, (q : ℝ))) f hf h0 hb
  let b : (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule :=
    ⟨g, (mem_fixedBoxEvenSources _ g).mpr ⟨hg, hg0, hge, hgb⟩⟩
  refine ⟨fixedBoxSourceClosedStage T hT1 hX b, ⟨b, rfl⟩, ?_⟩
  rw [fixedBoxSourceClosedStage_coe]
  apply Lp.ext
  filter_upwards [fixedBoxSourceStage_ae hX T hT1 b, hae] with x hx hy
  exact hx.trans ((hgs x).trans hy.symm)

/-- Genuine polar even sources are dense in the completed relative quotient. -/
theorem fixedBoxSourceQuotient_denseRange :
    DenseRange (fixedBoxSourceQuotient T hT1 p hTp1 hX) := by
  let D := (fixedBoxDenominator X T hT1 p hTp1).toSubmodule
  have hq : DenseRange D.mkQL := D.mkQ_surjective.denseRange
  have hd := hq.comp (fixedBoxSourceClosedStage_denseRange T hT1 hX) D.mkQL.continuous
  intro u
  have heq : (fixedBoxSourceQuotient T hT1 p hTp1 hX : _ → Q) =
      D.mkQL ∘ fixedBoxSourceClosedStage T hT1 hX :=
    funext (fixedBoxSourceQuotient_apply T hT1 p hTp1 hX)
  rw [heq]
  exact hd u

/-- Exact division already separates smooth source classes by their normalized
coordinates, before any assertion of completeness for the coordinate family. -/
theorem fixedBoxSourceQuotient_eq_zero_of_rows (hT : ∀ q ∈ T, q.Prime)
    (f : (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule)
    (hf : ∀ j : ℤ, fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT j
      (fixedBoxSourceQuotient T hT1 p hTp1 hX f) = 0) :
    fixedBoxSourceQuotient T hT1 p hTp1 hX f = 0 := by
  rw [fixedBoxSourceQuotient_apply]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (mem_fixedBoxDenominator_iff X T hT1 p hTp1 _).mpr
  apply (mem_closedStageSubmodule_iff X (insert p T) hTp1 _).mpr
  obtain ⟨hf0, h0, he, hb⟩ := (mem_fixedBoxEvenSources _ f).mp f.property
  apply subset_closure
  rw [fixedBoxSourceClosedStage_coe]
  apply (stageGenerators_insert_iff_packetRows_zero hX T hT hp hpT f hf0 h0 he hb
    _ (fixedBoxSourceStage_ae hX T hT1 f)).mpr
  intro j
  have hj := hf j
  rw [fixedBoxSourceQuotient_apply, fixedBoxPacketRow_mk, fixedBoxSourceClosedStage_coe] at hj
  exact hj

/-- Cardinal classes can be chosen from the same complete even source space. -/
theorem exists_fixedBox_source_cardinals (hT : ∀ q ∈ T, q.Prime) :
    ∃ f : ℤ → (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule,
      ∀ j n : ℤ, fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT j
        (fixedBoxSourceQuotient T hT1 p hTp1 hX (f n)) = if j = n then 1 else 0 := by
  classical
  obtain ⟨V, hV, hrow⟩ := exists_fixedBox_biorthogonal_even_stage hX T hT hp hpT
  choose f hf h0 he hb hae using hV
  let b (n : ℤ) : (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule :=
    ⟨f n, (mem_fixedBoxEvenSources _ _).mpr ⟨hf n, h0 n, he n, hb n⟩⟩
  refine ⟨b, fun j n ↦ ?_⟩
  rw [fixedBoxSourceQuotient_apply, fixedBoxPacketRow_mk, fixedBoxSourceClosedStage_coe]
  have heq : fixedBoxSourceStage hX T hT1 (b n) = V n := by
    apply Lp.ext
    exact (fixedBoxSourceStage_ae hX T hT1 (b n)).trans (hae n).symm
  rw [heq, hrow]

/-- Every circle Fourier projection has rank one in the *completed* packet,
with the actual normalized Mellin row as its coefficient functional. -/
theorem exists_fixedBox_rankOne_projections (hT : ∀ q ∈ T, q.Prime) :
    ∃ v : ℤ → Q,
      (∀ j n : ℤ, fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT j (v n) =
        if j = n then 1 else 0) ∧
      ∀ (n : ℤ) (u : Q), fixedBoxFourierProjection T hT1 p hTp1 hX hp hpT n u =
        fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT n u • v n := by
  classical
  obtain ⟨b, hb⟩ := exists_fixedBox_source_cardinals T hT1 p hTp1 hX hp hpT hT
  let A := fixedBoxSourceQuotient T hT1 p hTp1 hX
  let v (n : ℤ) := A (b n)
  refine ⟨v, hb, fun n u ↦ ?_⟩
  let P := fixedBoxFourierProjection T hT1 p hTp1 hX hp hpT n
  let ℓ := fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT n
  have hs (f : (fixedBoxEvenSources (X / (∏ q ∈ T, (q : ℝ)))).toSubmodule) :
      P (A f) = ℓ (A f) • v n := by
    obtain ⟨g, hg⟩ := exists_fixedBox_projection_source T hT1 p hTp1 hX hp hpT n f
    have hz : A (g - ℓ (A f) • b n) = 0 := by
      apply fixedBoxSourceQuotient_eq_zero_of_rows T hT1 p hTp1 hX hp hpT hT
      intro j
      simp only [map_sub, map_smul]
      rw [hg, fixedBoxPacketRow_fourierProjection, hb]
      by_cases hj : j = n
      · subst j
        simp only [ite_true, smul_eq_mul, mul_one]
        exact sub_self _
      · simp only [hj, ite_false, smul_zero, sub_self]
    rw [map_sub, map_smul] at hz
    exact hg.symm.trans (sub_eq_zero.mp hz)
  have heq : (P : Q → Q) = fun u ↦ ℓ u • v n :=
    (fixedBoxSourceQuotient_denseRange T hT1 p hTp1 hX).equalizer P.continuous
      (by fun_prop) (funext hs)
  exact congrFun heq u

/-- Uniqueness of scalar Fourier coefficients along an actual packet orbit. -/
theorem fixedBox_dual_eq_zero_of_projections (φ : Q →L[ℂ] ℂ) (u : Q)
    (hu : ∀ n : ℤ, φ (fixedBoxFourierProjection T hT1 p hTp1 hX hp hpT n u) = 0) :
    φ u = 0 := by
  let : Fact (0 < L) := ⟨Real.log_pos (by exact_mod_cast hp.one_lt)⟩
  let f : C(AddCircle L, ℂ) := ⟨fun s ↦ φ (ρ s u),
    φ.continuous.comp (continuous_fixedBoxCircleAction T hT1 p hTp1 hX hp.one_lt hpT u)⟩
  have hc (k : ℤ) : _root_.fourierCoeff f k = 0 := by
    have hi := (packetOrbit_integrable T hT1 p hTp1 hX hp hpT u).fourier_smul (-k)
    have he : _root_.fourierCoeff f k = φ (_root_.fourierCoeff (fun s : AddCircle L ↦ ρ s u) k) := by
      simpa only [_root_.fourierCoeff, f, ContinuousMap.coe_mk, map_smul] using! φ.integral_comp_comm hi
    apply he.trans
    simpa only [fixedBoxFourierProjection_apply, neg_neg] using hu (-k)
  have hs : Summable (_root_.fourierCoeff f) := by
    simpa only [funext hc] using (summable_zero : Summable (fun _ : ℤ ↦ (0 : ℂ)))
  have hz := _root_.has_pointwise_sum_fourier_series_of_summable hs (0 : AddCircle L)
  simp only [hc, zero_smul] at hz
  have hzero : f 0 = 0 := hz.unique hasSum_zero
  simpa only [f, ContinuousMap.coe_mk, fixedBoxCircleAction_zero,
    ContinuousLinearMap.id_apply] using hzero

/-- No nonzero completed packet vector has all normalized coordinates zero. -/
theorem fixedBox_eq_zero_iff_rows (hT : ∀ q ∈ T, q.Prime) (u : Q) :
    u = 0 ↔ ∀ n : ℤ, fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT n u = 0 := by
  constructor
  · rintro rfl n
    exact map_zero _
  · intro hu
    obtain ⟨v, _, hv⟩ := exists_fixedBox_rankOne_projections T hT1 p hTp1 hX hp hpT hT
    apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
    intro φ
    apply fixedBox_dual_eq_zero_of_projections T hT1 p hTp1 hX hp hpT φ u
    intro n
    rw [hv, hu, zero_smul, map_zero]

/-- The rank-one circle modes span a dense subspace of the original completed
relative packet, not merely of an auxiliary coordinate model. -/
theorem exists_fixedBox_total_cardinals (hT : ∀ q ∈ T, q.Prime) :
    ∃ v : ℤ → Q,
      (∀ j n : ℤ, fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT j (v n) =
        if j = n then 1 else 0) ∧
      (∀ (n : ℤ) (u : Q), fixedBoxFourierProjection T hT1 p hTp1 hX hp hpT n u =
        fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT n u • v n) ∧
      (Submodule.span ℂ (range v)).topologicalClosure = ⊤ := by
  obtain ⟨v, hrow, hv⟩ := exists_fixedBox_rankOne_projections T hT1 p hTp1 hX hp hpT hT
  refine ⟨v, hrow, hv, ?_⟩
  let M := (Submodule.span ℂ (range v)).topologicalClosure
  let : IsClosed (M : Set Q) := Submodule.isClosed_topologicalClosure _
  apply top_unique
  intro u _
  change u ∈ M
  apply (Submodule.Quotient.mk_eq_zero M).mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ)
  intro φ
  change (φ.comp M.mkQL) u = 0
  apply fixedBox_dual_eq_zero_of_projections T hT1 p hTp1 hX hp hpT (φ.comp M.mkQL) u
  intro n
  have hmem : v n ∈ M := Submodule.le_topologicalClosure _
    (Submodule.subset_span (mem_range_self n))
  have hz : M.mkQL (v n) = 0 := (Submodule.Quotient.mk_eq_zero M).mpr hmem
  rw [hv, map_smul, ContinuousLinearMap.comp_apply, hz, map_zero, smul_zero]

include hX hp hpT in
/-- Exact kernel identification survives completion: the common kernel of the
actual normalized rows is precisely the next *closed theta stage*. -/
theorem mem_nextClosedStage_iff_packetRows_zero (hT : ∀ q ∈ T, q.Prime)
    (F : LogL2) (hF : F ∈ closedStageSubmodule X T hT1) :
    F ∈ closedStageSubmodule X (insert p T) hTp1 ↔
      ∀ n : ℤ, packetRow X T p n F = 0 := by
  let D := (fixedBoxDenominator X T hT1 p hTp1).toSubmodule
  let u : closedStageSubmodule X T hT1 := ⟨F, hF⟩
  have he := fixedBox_eq_zero_iff_rows T hT1 p hTp1 hX hp hpT hT (D.mkQL u)
  have hr (n : ℤ) : fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT n (D.mkQL u) =
      packetRow X T p n F := fixedBoxPacketRow_mk hX T hT1 p hTp1 hT hp hpT n u
  constructor
  · intro h n
    have hm : u ∈ D := (mem_fixedBoxDenominator_iff X T hT1 p hTp1 u).mpr h
    exact (hr n).symm.trans ((he.mp ((Submodule.Quotient.mk_eq_zero D).mpr hm)) n)
  · intro h
    have hz := he.mpr (fun n ↦ (hr n).trans (h n))
    exact (mem_fixedBoxDenominator_iff X T hT1 p hTp1 u).mp
      ((Submodule.Quotient.mk_eq_zero D).mp hz)

/-- The dense cardinal system consists of eigenvectors for the genuine circle
action, with its genuine continuous coordinate functionals. -/
theorem exists_fixedBox_total_eigen_cardinals (hT : ∀ q ∈ T, q.Prime) :
    ∃ v : ℤ → Q,
      (∀ j n : ℤ, fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT j (v n) =
        if j = n then 1 else 0) ∧
      (∀ (s : AddCircle L) (n : ℤ), ρ s (v n) = _root_.fourier (-n) s • v n) ∧
      (∀ (n : ℤ) (u : Q), fixedBoxFourierProjection T hT1 p hTp1 hX hp hpT n u =
        fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT n u • v n) ∧
      (Submodule.span ℂ (range v)).topologicalClosure = ⊤ ∧ LinearIndependent ℂ v := by
  classical
  obtain ⟨v, hrow, hv, hd⟩ := exists_fixedBox_total_cardinals T hT1 p hTp1 hX hp hpT hT
  refine ⟨v, hrow, ?_, hv, hd, ?_⟩
  · intro s n
    apply sub_eq_zero.mp
    apply (fixedBox_eq_zero_iff_rows T hT1 p hTp1 hX hp hpT hT _).mpr
    intro j
    rw [map_sub, map_smul, fixedBoxPacketRow_circleAction, hrow]
    by_cases hj : j = n
    · subst j
      simp only [ite_true, smul_eq_mul, mul_one, sub_self]
    · simp only [hj, ite_false, mul_zero, smul_zero, sub_self]
  · apply LinearIndependent.of_pairwise_dual_eq_zero_one v
      (fun j ↦ (fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT j).toLinearMap)
    · intro i j hij
      simp only [ContinuousLinearMap.coe_coe, hrow, ite_eq_right hij]
    · intro i
      simp only [ContinuousLinearMap.coe_coe, hrow, ite_true]

end RiemannMasullo.RationalPacket
