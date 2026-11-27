module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxQuotient

/-! # Bounded right input windows on the rational fixed-box quotient

The window hypothesis is imposed on the operator, not inferred from an output
cutoff or from a cutoff on finite components.
-/

public noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace RiemannMasullo.RationalPacket

variable {X : ℝ} (hX : 0 < X) (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q)
variable (p : ℕ) (hTp : ∀ q ∈ insert p T, 1 ≤ q) (hp : 1 < p) (hmem : p ∉ T)

local notation "E" => closedStageSubmodule X T hT
local notation "N" => ClosedSubmodule.toSubmodule (fixedBoxDenominator X T hT p hTp)
local notation "Q" => FixedBoxQuotient[X,T,hT,p,hTp]

include hX hp hmem in
/-- The forward lift through `n` actual periods has known norm, support and class. -/
theorem exists_fixedBox_period_lift (n : ℕ) (u : E) :
    ∃ v : E, (N).mkQL v = (N).mkQL u ∧
      ‖v‖ = Real.exp ((n : ℝ) * Real.log p / 2) * ‖u‖ ∧
      ∀ᵐ x ∂volume, x < -Real.log X + (n : ℝ) * Real.log p → (v : LogL2) x = 0 := by
  let L : ℝ≥0 := ⟨Real.log p, Real.log_nonneg (by exact_mod_cast hp.le)⟩
  let S := fixedBoxForwardShift T hT p hTp hX
  have hid (m : ℕ) : S (m • L) = ContinuousLinearMap.id ℂ Q := by
    induction m with
    | zero => simpa only [zero_smul] using fixedBoxForwardShift_zero T hT p hTp hX
    | succ m ih =>
      rw [succ_nsmul, show S (m • L + L) = (S (m • L)).comp (S L) from
        fixedBoxForwardShift_add T hT p hTp hX _ _, ih,
        show S L = ContinuousLinearMap.id ℂ Q from
          fixedBoxForwardShift_period T hT p hTp hX hp hmem]
      rfl
  let t := n • L
  have ht : (t : ℝ) = (n : ℝ) * Real.log p := by
    change ((n • L : ℝ≥0) : ℝ) = _
    rw [nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast]
    rfl
  let v := closedStageForwardShift T hT hX t u
  refine ⟨v, ?_, ?_, ?_⟩
  · have hclass := DFunLike.congr_fun (hid n) ((N).mkQL u : Q)
    exact (fixedBoxForwardShift_mk T hT p hTp hX t u).symm.trans hclass
  · change ‖(closedStageForwardShift T hT hX t u : LogL2)‖ = _
    rw [closedStageForwardShift_apply, norm_halfShift, ht]
    rfl
  · dsimp only [v]
    rw [closedStageForwardShift_apply]
    have hs := (measurePreserving_add_right volume (-(t : ℝ))).quasiMeasurePreserving.ae
      (closedStageSubmodule_supported hX T hT u.property)
    filter_upwards [halfShift_ae (t : ℝ) (u : LogL2), hs] with x hx hsx hcut
    change x - (t : ℝ) < -Real.log X → (u : LogL2) (x - (t : ℝ)) = 0 at hsx
    rw [hx, hsx (by rw [ht]; linarith), mul_zero]

include hp in
private theorem exists_fixedBox_period_past (b : ℝ) :
    ∃ n : ℕ, b < -Real.log X + (n : ℝ) * Real.log p := by
  have hL : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp)
  obtain ⟨n, hn⟩ := exists_nat_gt ((b + Real.log X) / Real.log p)
  exact ⟨n, by linarith [(div_lt_iff₀ hL).mp hn]⟩

include hX hp hmem

/-- Every quotient class has a representative vanishing on the entire given
left half-line, including its endpoint. -/
theorem exists_fixedBox_lift_past (b : ℝ) (z : Q) :
    ∃ v : E, (N).mkQL v = z ∧ ∀ᵐ x ∂volume, x ≤ b → (v : LogL2) x = 0 := by
  obtain ⟨u, rfl⟩ := (N).mkQ_surjective z
  obtain ⟨n, hn⟩ := exists_fixedBox_period_past (X := X) p hp b
  obtain ⟨v, hv, -, hfloor⟩ := exists_fixedBox_period_lift hX T hT p hTp hp hmem n u
  refine ⟨v, hv, ?_⟩
  filter_upwards [hfloor] with x hx hxb using hx (hxb.trans_lt hn)

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- A bounded-right-input-window operator annihilating the actual denominator is zero. -/
theorem fixedBox_window_eq_zero (B : E →L[ℂ] Y) (b : ℝ)
    (hwindow : ∀ v : E, (∀ᵐ x ∂volume, x ≤ b → (v : LogL2) x = 0) → B v = 0)
    (hden : N ≤ LinearMap.ker B.toLinearMap) : B = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  obtain ⟨v, hv, hs⟩ := exists_fixedBox_lift_past hX T hT p hTp hp hmem b ((N).mkQL u)
  have hdiff : u - v ∈ N := (Submodule.Quotient.eq N).mp hv.symm
  have hz : B (u - v) = 0 := hden hdiff
  change B u = (0 : Y)
  simpa only [map_sub, hwindow v hs, sub_zero] using hz

/-- Without exact descent there is quantitative leakage on the denominator.
The estimate degenerates as the required number of periods grows. -/
theorem fixedBox_window_leakage (B : E →L[ℂ] Y) (b : ℝ)
    (hwindow : ∀ v : E, (∀ᵐ x ∂volume, x ≤ b → (v : LogL2) x = 0) → B v = 0)
    (n : ℕ) (hn : b < -Real.log X + (n : ℝ) * Real.log p) :
    ‖B‖ / (1 + Real.exp ((n : ℝ) * Real.log p / 2)) ≤ ‖B.comp (N).subtypeL‖ := by
  let c := Real.exp ((n : ℝ) * Real.log p / 2)
  have hc : 0 < c := Real.exp_pos _
  apply (div_le_iff₀ (show 0 < 1 + c by positivity)).mpr
  apply B.opNorm_le_bound
    (mul_nonneg (norm_nonneg (B.comp (N).subtypeL)) (show 0 ≤ 1 + c by positivity))
  intro u
  obtain ⟨v, hv, hvnorm, hs⟩ := exists_fixedBox_period_lift hX T hT p hTp hp hmem n u
  have hvzero : B v = 0 := hwindow v (by
    filter_upwards [hs] with x hx hxb using hx (hxb.trans_lt hn))
  let w : N := ⟨u - v, (Submodule.Quotient.eq N).mp hv.symm⟩
  have hw : ‖w‖ ≤ (1 + c) * ‖u‖ := calc
    ‖w‖ = ‖u - v‖ := rfl
    _ ≤ ‖u‖ + ‖v‖ := norm_sub_le ..
    _ = (1 + c) * ‖u‖ := by rw [hvnorm, add_mul, one_mul]
  calc
    ‖B u‖ = ‖(B.comp (N).subtypeL) w‖ := by
      change ‖B u‖ = ‖B (u - v)‖
      rw [map_sub, hvzero, sub_zero]
    _ ≤ ‖B.comp (N).subtypeL‖ * ‖w‖ := (B.comp (N).subtypeL).le_opNorm w
    _ ≤ ‖B.comp (N).subtypeL‖ * ((1 + c) * ‖u‖) :=
      mul_le_mul_of_nonneg_left hw (norm_nonneg (B.comp (N).subtypeL))
    _ = _ := (mul_assoc ..).symm

end RiemannMasullo.RationalPacket
