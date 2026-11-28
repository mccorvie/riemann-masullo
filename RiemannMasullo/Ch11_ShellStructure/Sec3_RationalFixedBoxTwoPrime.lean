module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxBasis

/-! # The shared zero row of two actual finite-prime descents

In a single fixed total box, two distinct new primes give incommensurate
circle rotations. The intersection of their one-prime stages is not the
two-prime stage: the shared zero mode gives exactly one missing line. -/

public noncomputable section

namespace RiemannMasullo.RationalPacket

private theorem distinctPrime_logRatio_irrational {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hne : q ≠ p) : Irrational (Real.log q / Real.log p) := by
  intro ⟨r, hr⟩
  have hqlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hplog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hrpos : 0 < (r : ℝ) := hr ▸ div_pos hqlog hplog
  have hd : 0 < (r.den : ℝ) := by exact_mod_cast r.den_pos
  have hn : 0 ≤ r.num := by
    rw [Rat.cast_def] at hrpos
    have h : 0 < (r.num : ℝ) := by simpa using (lt_div_iff₀ hd).mp hrpos
    exact_mod_cast h.le
  let m := r.num.toNat
  have hm : (m : ℝ) = (r.num : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
  rw [Rat.cast_def, ← hm] at hr
  have hlogs : (r.den : ℝ) * Real.log q = (m : ℝ) * Real.log p := by
    have h := (div_eq_div_iff hd.ne' hplog.ne').mp hr
    linarith
  have hpow := congrArg Real.exp hlogs
  rw [Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hq.pos),
    Real.exp_log (by exact_mod_cast hp.pos)] at hpow
  have hnat : q ^ r.den = p ^ m := by exact_mod_cast hpow
  have hdiv : q ∣ p ^ m := hnat ▸ dvd_pow_self q r.den_pos.ne'
  exact hne ((hp.eq_one_or_self_of_dvd q (hq.dvd_of_dvd_pow hdiv)).resolve_left hq.ne_one)

private theorem int_of_fourierChar_one {x : ℝ} (h : (Real.fourierChar x : ℂ) = 1) :
    ∃ k : ℤ, x = k := by
  rw [Real.fourierChar_apply] at h
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
  have he : 2 * Real.pi * x = (k : ℝ) * (2 * Real.pi) := by
    have hc : ((2 * Real.pi * x : ℝ) : ℂ) = (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
      apply mul_right_cancel₀ Complex.I_ne_zero
      push_cast at hk ⊢
      linear_combination hk
    exact_mod_cast hc
  exact ⟨k, mul_left_cancel₀ (mul_ne_zero (show (2 : ℝ) ≠ 0 by norm_num) Real.pi_ne_zero)
    (he.trans (mul_comm (k : ℝ) (2 * Real.pi)))⟩

private theorem exists_fixedBox_distinctPrime_fixed_line {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT1 : ∀ q ∈ T, 1 ≤ q) (p : ℕ)
    (hTp1 : ∀ q ∈ insert p T, 1 ≤ q) (hT : ∀ q ∈ T, q.Prime)
    (hp : p.Prime) (hpT : p ∉ T) (q : ℕ) (hq : q.Prime) (hne : q ≠ p) :
    ∃ v : FixedBoxQuotient[X,T,hT1,p,hTp1],
      fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT 0 v = 1 ∧
      ∀ u : FixedBoxQuotient[X,T,hT1,p,hTp1],
        fixedBoxForwardShift T hT1 p hTp1 hX (Real.log q).toNNReal u = u ↔
          u = fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT 0 u • v := by
  classical
  let row := fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT
  let S := fixedBoxForwardShift T hT1 p hTp1 hX (Real.log q).toNNReal
  obtain ⟨v, hv, _, _, hs, _⟩ := exists_fixedBox_unconditional_cardinals hX T hT1 p hTp1 hT hp hpT
  have hqlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
  have act (n : ℤ) (u : FixedBoxQuotient[X,T,hT1,p,hTp1]) : row n (S u) =
      (Real.fourierChar (-Real.log q * ((n : ℝ) / Real.log p)) : ℂ) * row n u := by
    simpa only [row, S, Real.coe_toNNReal _ hqlog.le] using
      fixedBoxPacketRow_forwardShift hX T hT1 p hTp1 hT hp hpT n (Real.log q).toNNReal u
  have extrow {a b : FixedBoxQuotient[X,T,hT1,p,hTp1]} (h : ∀ n, row n a = row n b) : a = b := by
    have ha : HasSum (fun n ↦ row n a • v n) a := hs a
    have hb : HasSum (fun n ↦ row n b • v n) b := hs b
    apply ha.unique
    simpa only [h] using hb
  have hfix : S (v 0) = v 0 := by
    apply extrow
    intro n
    rw [act]
    simp only [row, hv]
    split_ifs with hn
    · subst n; simp
    · simp
  refine ⟨v 0, by simpa using hv 0 0, fun u ↦ ⟨fun hu ↦ ?_, fun hu ↦ ?_⟩⟩
  · change S u = u at hu
    refine (hs u).tsum_eq.symm.trans ?_
    apply tsum_eq_single 0
    intro n hn
    suffices hz : row n u = 0 by exact (congrArg (fun c : ℂ ↦ c • v n) hz).trans (zero_smul _ _)
    by_contra hnz
    have hphase := act n u
    rw [hu] at hphase
    have hone := mul_right_cancel₀ hnz (hphase.symm.trans (one_mul (row n u)).symm)
    obtain ⟨k, hk⟩ := int_of_fourierChar_one hone
    apply distinctPrime_logRatio_irrational hp hq hne
    refine ⟨-(k : ℚ) / n, ?_⟩
    push_cast
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hp' : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    field_simp [hp', hn'] at hk ⊢
    linarith
  · change S u = u
    calc S u = S (row 0 u • v 0) := congrArg S hu
         _ = row 0 u • v 0 := by rw [map_smul, hfix]
         _ = u := hu.symm

end RiemannMasullo.RationalPacket

open scoped NNReal
namespace RiemannMasullo.RationalPacket

variable {X : ℝ} (hX : 0 < X) (T : Finset ℕ) (hT1 : ∀ r ∈ T, 1 ≤ r)
variable (p q : ℕ) (hTp : ∀ r ∈ insert p T, 1 ≤ r)
variable (hTq : ∀ r ∈ insert q T, 1 ≤ r) (hTpq : ∀ r ∈ insert q (insert p T), 1 ≤ r)
variable (hT : ∀ r ∈ T, r.Prime) (hp : p.Prime) (hpT : p ∉ T)
variable (hq : q.Prime) (hqTp : q ∉ insert p T)

local notation "E" => closedStageSubmodule X T hT1
local notation "P" => closedStageSubmodule X (insert p T) hTp
local notation "B" => closedStageSubmodule X (insert q T) hTq
local notation "D" => closedStageSubmodule X (insert q (insert p T)) hTpq
local notation "N" => ClosedSubmodule.toSubmodule (fixedBoxDenominator X T hT1 p hTp)
local notation "Q" => FixedBoxQuotient[X,T,hT1,p,hTp]
local notation "A" => stagePeriodDifference (q : ℝ)
local notation "L" => Real.toNNReal (Real.log (q : ℝ))
local notation "S" => fixedBoxForwardShift T hT1 p hTp hX L
local notation "R₀" => fixedBoxPacketRow hX T hT1 p hTp hT hp hpT 0

include hq
private theorem twoPrimeDifference_injective : Function.Injective A := by
  intro a b hab
  have hz : A (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hb := mul_norm_le_stagePeriodDifference (q : ℝ) (a - b)
  rw [hz, norm_zero] at hb
  have hc : 0 < Real.exp (Real.log (q : ℝ) / 2) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (half_pos (Real.log_pos (by exact_mod_cast hq.one_lt))))
  by_contra hn
  exact (not_lt_of_ge hb) (mul_pos hc (norm_pos_iff.mpr (sub_ne_zero.mpr hn)))

include hX hqTp in
private theorem twoPrimeDifference_mem_deep_iff (u : LogL2) : A u ∈ D ↔ u ∈ P := by
  change A u ∈ (D : Set LogL2) ↔ _
  rw [← range_stagePeriodDifference_closedStage hX (insert p T) hTp hq.one_lt hqTp hTpq]
  constructor
  · rintro ⟨y, hy⟩
    change A (y : LogL2) = A u at hy
    exact (twoPrimeDifference_injective q hq hy) ▸ y.property
  · intro hu
    exact ⟨⟨u, hu⟩, rfl⟩

include hq in
private theorem twoPrimeDifference_mem_p_iff (e : E) :
    A (e : LogL2) ∈ P ↔ S ((N).mkQL e) = (N).mkQL e := by
  rw [fixedBoxForwardShift_mk]
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq.one_le)
  change _ ↔ (Submodule.Quotient.mk (closedStageForwardShift T hT1 hX L e) : Q) =
    Submodule.Quotient.mk e
  rw [Submodule.Quotient.eq N]
  change _ ↔ closedStageForwardShift T hT1 hX L e - e ∈
    fixedBoxDenominator X T hT1 p hTp
  rw [mem_fixedBoxDenominator_iff X T hT1 p hTp]
  have hcoe : ((closedStageForwardShift T hT1 hX L e - e : E) : LogL2) =
      (closedStageForwardShift T hT1 hX L e : LogL2) - (e : LogL2) := rfl
  rw [hcoe, closedStageForwardShift_apply]
  rw [Real.coe_toNNReal _ hlog]
  rfl

include hqTp

/-- A normalized fixed packet class has an actual lift whose q-difference is in
both one-prime ranges, but not in the two-prime range. -/
private theorem exists_twoPrime_normalized_lift (v : Q) (hv : S v = v) (hv0 : R₀ v = 1) :
    ∃ e : E, (N).mkQL e = v ∧ A (e : LogL2) ∈ P ∧ A (e : LogL2) ∈ B ∧ A (e : LogL2) ∉ D := by
  obtain ⟨e, he⟩ := (N).mkQ_surjective v
  change (N).mkQL e = v at he
  refine ⟨e, he, (twoPrimeDifference_mem_p_iff hX T hT1 p q hTp hq e).mpr (by rwa [he]), ?_, ?_⟩
  · change A (e : LogL2) ∈ (B : Set LogL2)
    rw [← range_stagePeriodDifference_closedStage hX T hT1 hq.one_lt
      (fun h ↦ hqTp (Finset.mem_insert_of_mem h)) hTq]
    exact ⟨e, rfl⟩
  · intro hd
    have hep := (twoPrimeDifference_mem_deep_iff hX T p q hTp hTpq hq hqTp _).mp hd
    have he0 : (N).mkQL e = 0 := (Submodule.Quotient.mk_eq_zero N).mpr
      ((mem_fixedBoxDenominator_iff X T hT1 p hTp e).mpr hep)
    rw [← he, he0, map_zero] at hv0
    exact zero_ne_one hv0

/-- Against any actual lift of the normalized fixed class, each element of the
intersection has exactly one scalar remainder modulo the genuine deeper stage. -/
private theorem existsUnique_twoPrime_intersection_scalar (v : Q) (hv0 : R₀ v = 1)
    (hfixed : ∀ x : Q, S x = x ↔ x = R₀ x • v) (e : E) (he : (N).mkQL e = v)
    (z : LogL2) (hzp : z ∈ P) (hzq : z ∈ B) :
    ∃! c : ℂ, z - c • A (e : LogL2) ∈ D := by
  obtain ⟨u, ⟨hu, huz, -⟩, -⟩ := existsUnique_stagePeriodDifference_preimage hX T hT1 hq.one_lt
    (fun h ↦ hqTp (Finset.mem_insert_of_mem h)) hTq hzq
  let f : E := ⟨u, hu⟩
  have hf : A (f : LogL2) = z := huz
  have hclass : (N).mkQL f = R₀ ((N).mkQL f) • v := (hfixed _).mp
    ((twoPrimeDifference_mem_p_iff hX T hT1 p q hTp hq f).mp (hf.symm ▸ hzp))
  have hrem (c : ℂ) : z - c • A (e : LogL2) ∈ D ↔ (N).mkQL f = c • v := by
    rw [← hf, ← map_smul A, ← map_sub A, twoPrimeDifference_mem_deep_iff hX T p q hTp hTpq hq hqTp]
    have hcoe : ((f - c • e : E) : LogL2) = (f : LogL2) - c • (e : LogL2) := rfl
    rw [← hcoe, ← mem_fixedBoxDenominator_iff X T hT1 p hTp]
    change (f - c • e : E) ∈ N ↔ _
    have hzero : (f - c • e : E) ∈ N ↔ (N).mkQL (f - c • e) = 0 :=
      (Submodule.Quotient.mk_eq_zero N).symm
    rw [hzero, map_sub, map_smul, he, sub_eq_zero]
  refine ⟨R₀ ((N).mkQL f), (hrem _).mpr hclass, ?_⟩
  intro c hc
  have h := congrArg (fun x : Q ↦ R₀ x) ((hrem c).mp hc)
  simpa only [map_smul, hv0, smul_eq_mul, mul_one] using h.symm

include hX hT1 hT hp hpT in
/-- Intersecting the two genuine one-prime stages leaves exactly one extra
complex line modulo the genuine two-prime stage. The witness is the q-period
difference of a representative of the normalized zero p-packet cardinal. -/
theorem exists_fixedBox_twoPrime_intersection_line :
    ∃ w : LogL2, w ∈ P ∧ w ∈ B ∧ w ∉ D ∧
      ∀ z : LogL2, z ∈ P → z ∈ B → ∃! c : ℂ, z - c • w ∈ D := by
  have hne : q ≠ p := by
    intro he
    subst q
    exact hqTp (Finset.mem_insert_self p T)
  obtain ⟨v, hzero, hfixed⟩ :=
    exists_fixedBox_distinctPrime_fixed_line hX T hT1 p hTp hT hp hpT q hq hne
  have hv : S v = v := (hfixed v).mpr (by rw [hzero, one_smul])
  obtain ⟨e, he, hep, heq, hen⟩ :=
    exists_twoPrime_normalized_lift hX T hT1 p q hTp hTq hTpq hT hp hpT hq hqTp v hv hzero
  refine ⟨A (e : LogL2), hep, heq, hen, fun z hzp hzq ↦ ?_⟩
  exact existsUnique_twoPrime_intersection_scalar hX T hT1 p q hTp hTq hTpq hT hp hpT hq hqTp
    v hzero hfixed e he z hzp hzq

end RiemannMasullo.RationalPacket
