module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxQuotient
public import Mathlib.Topology.Instances.AddCircle.Defs

/-! # The logarithmic circle on the completed rational relative box

Following fpet19's written periodization construction (#7351, comment 7149080501),
we act on the actual submodule quotient. Only forward shifts are used upstairs;
the inverse on the quotient comes from the complementary circle parameter.
-/

public noncomputable section

open Set
open scoped NNReal

namespace RiemannMasullo.RationalPacket

variable {X : ℝ} (T : Finset ℕ) (hT : ∀ q ∈ T, 1 ≤ q)
variable (p : ℕ) (hTp : ∀ q ∈ insert p T, 1 ≤ q) (hX : 0 < X)
variable (hp : 1 < p) (hmem : p ∉ T)

local notation "L" => Real.log (p : ℝ)
local notation "Q" => FixedBoxQuotient[X,T,hT,p,hTp]
local notation "S" => fixedBoxForwardShift T hT p hTp hX

include hp in
private theorem fixedBox_log_pos : 0 < L := Real.log_pos (by exact_mod_cast hp)

/-- On the fundamental interval the circle operator is precisely the forward shift.
`Real.toNNReal` extends its time argument by `max t 0` outside the interval. -/
def fixedBoxCircleAction : AddCircle L → (Q →L[ℂ] Q) := by
  letI : Fact (0 < L) := ⟨fixedBox_log_pos p hp⟩
  exact AddCircle.liftIco L 0 (fun t : ℝ ↦ S t.toNNReal)

local notation "ρ" => fixedBoxCircleAction T hT p hTp hX hp

theorem fixedBoxCircleAction_coe_of_mem {t : ℝ} (ht : t ∈ Ico 0 L) :
    ρ (t : AddCircle L) = S t.toNNReal := by
  let : Fact (0 < L) := ⟨fixedBox_log_pos p hp⟩
  exact AddCircle.liftIco_zero_coe_apply ht

include hp hmem in
private theorem fixedBoxForwardShift_toNNReal_period :
    S (Real.toNNReal L) = ContinuousLinearMap.id ℂ Q := by
  have ht : Real.toNNReal L = ⟨L, (fixedBox_log_pos p hp).le⟩ :=
    Subtype.ext (Real.coe_toNNReal _ (fixedBox_log_pos p hp).le)
  rw [ht]
  exact fixedBoxForwardShift_period T hT p hTp hX hp hmem

include hmem in
/-- All nonnegative times factor through the circle, not just fundamental representatives.
Each wrap removes one period using the semigroup law. -/
theorem fixedBoxCircleAction_coe {t : ℝ} (ht : 0 ≤ t) :
    ρ (t : AddCircle L) = S t.toNNReal := by
  have hL := fixedBox_log_pos p hp
  obtain ⟨n, hn⟩ := exists_nat_gt (t / L)
  have hb : t < (n : ℝ) * L := (div_lt_iff₀ hL).mp hn
  clear hn
  induction n generalizing t with
  | zero => simp only [Nat.cast_zero, zero_mul] at hb; exact (not_lt_of_ge ht hb).elim
  | succ n ih =>
    by_cases h : t < L
    · exact fixedBoxCircleAction_coe_of_mem T hT p hTp hX hp ⟨ht, h⟩
    · have hk : 0 ≤ t - L := sub_nonneg.mpr (le_of_not_gt h)
      have hk' : t - L < (n : ℝ) * L := by
        rw [Nat.cast_succ, add_mul, one_mul] at hb
        linarith
      calc
        ρ (t : AddCircle L) = ρ ((t - L : ℝ) : AddCircle L) := by
          rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
        _ = S (t - L).toNNReal := ih (t := t - L) hk hk'
        _ = S ((t - L).toNNReal + Real.toNNReal L) := by
          rw [fixedBoxForwardShift_add, fixedBoxForwardShift_toNNReal_period T hT p hTp hX hp hmem,
            ContinuousLinearMap.comp_id]
        _ = S t.toNNReal := by rw [← Real.toNNReal_add hk hL.le, sub_add_cancel]

@[simp] theorem fixedBoxCircleAction_zero : ρ 0 = ContinuousLinearMap.id ℂ Q := by
  have h := fixedBoxCircleAction_coe_of_mem T hT p hTp hX hp (t := 0)
    ⟨le_rfl, fixedBox_log_pos p hp⟩
  simpa only [AddCircle.coe_zero, Real.toNNReal_zero, fixedBoxForwardShift_zero] using h

include hmem in
/-- The sum of two fundamental representatives wraps at most once. -/
theorem fixedBoxCircleAction_add (s t : AddCircle L) : ρ (s + t) = (ρ s).comp (ρ t) := by
  let : Fact (0 < L) := ⟨fixedBox_log_pos p hp⟩
  obtain ⟨a, ha, rfl⟩ := AddCircle.eq_coe_Ico s
  obtain ⟨b, hb, rfl⟩ := AddCircle.eq_coe_Ico t
  rw [← AddCircle.coe_add, fixedBoxCircleAction_coe T hT p hTp hX hp hmem (add_nonneg ha.1 hb.1),
    Real.toNNReal_add ha.1 hb.1, fixedBoxForwardShift_add,
    fixedBoxCircleAction_coe_of_mem T hT p hTp hX hp ha,
    fixedBoxCircleAction_coe_of_mem T hT p hTp hX hp hb]

include hmem in
theorem fixedBoxCircleAction_neg_comp (s : AddCircle L) :
    (ρ (-s)).comp (ρ s) = ContinuousLinearMap.id ℂ Q := by
  rw [← fixedBoxCircleAction_add T hT p hTp hX hp hmem, neg_add_cancel, fixedBoxCircleAction_zero]

include hmem in
/-- Endpoint agreement suffices for strong continuity; no operator-norm continuity is used. -/
theorem continuous_fixedBoxCircleAction (x : Q) : Continuous fun s : AddCircle L ↦ ρ s x := by
  let : Fact (0 < L) := ⟨fixedBox_log_pos p hp⟩
  change Continuous (AddCircle.liftIco L 0 (fun t : ℝ ↦ S t.toNNReal x))
  apply AddCircle.liftIco_zero_continuous
  · simp only [Real.toNNReal_zero, fixedBoxForwardShift_zero,
      fixedBoxForwardShift_toNNReal_period T hT p hTp hX hp hmem]
  · exact ((continuous_fixedBoxForwardShift T hT p hTp hX x).comp
      continuous_real_toNNReal).continuousOn

/-- Uniform bound in the original quotient norm. -/
theorem norm_fixedBoxCircleAction_le (s : AddCircle L) : ‖ρ s‖ ≤ Real.sqrt p := by
  let : Fact (0 < L) := ⟨fixedBox_log_pos p hp⟩
  obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ico s
  rw [fixedBoxCircleAction_coe_of_mem T hT p hTp hX hp ht]
  calc
    ‖S t.toNNReal‖ ≤ Real.exp ((t.toNNReal : ℝ) / 2) := norm_fixedBoxForwardShift_le _ _ _ _ _ _
    _ ≤ Real.exp (L / 2) := by
      rw [Real.coe_toNNReal _ ht.1]
      exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right ht.2.le (by norm_num))
    _ = Real.sqrt p := by rw [Real.exp_half, Real.exp_log (by exact_mod_cast (Nat.zero_lt_of_lt hp))]

end RiemannMasullo.RationalPacket
