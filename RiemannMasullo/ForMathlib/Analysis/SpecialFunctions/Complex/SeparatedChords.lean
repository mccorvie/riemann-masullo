module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Reciprocal chords of separated points on the unit circle

The points within half the separation in angle of the target account for at most one index.
On either side, ordering the remaining angles bounds the reciprocal chords by a harmonic sum.
-/

public noncomputable section

open scoped BigOperators
open Finset Real

namespace Circle

private theorem chord_le_arg_difference (z w : Circle) :
    ‖(z : ℂ) - w‖ ≤ |(z : ℂ).arg - (w : ℂ).arg| := by
  have he := Complex.norm_sub_sq_eq_norm_sub_norm_sq_add (z : ℂ) (w : ℂ)
  rw [Circle.norm_coe, Circle.norm_coe] at he
  have hs := Real.sin_sq_le_sq (x := ((z : ℂ).arg - (w : ℂ).arg) / 2)
  exact (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp (by rw [sq_abs]; nlinarith)

private theorem arg_le_chord (z : Circle) :
    |(z : ℂ).arg| ≤ Real.pi / 2 * ‖(z : ℂ) - 1‖ := by
  have he : Complex.exp (Complex.I * ((z : ℂ).arg : ℂ)) = z := by
    simpa only [Circle.coe_exp, mul_comm] using congrArg ((↑) : Circle → ℂ) (Circle.exp_arg z)
  have hchord : ‖(z : ℂ) - 1‖ = 2 * |Real.sin ((z : ℂ).arg / 2)| := by
    conv_lhs => rw [← he, Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have harg : |(z : ℂ).arg / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [Complex.abs_arg_le_pi (z : ℂ)]
  have hs := Real.mul_abs_le_abs_sin harg
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hs
  rw [hchord]
  field_simp [Real.pi_ne_zero] at hs
  nlinarith

private theorem reciprocal_sum_separated (S : Finset ℝ) {h : ℝ} (hh : 0 < h)
    (hl : ∀ x ∈ S, h / 2 ≤ x)
    (hs : ∀ x ∈ S, ∀ y ∈ S, x < y → h ≤ y - x) :
    ∑ x ∈ S, x⁻¹ ≤ (2 / h) * (harmonic S.card : ℝ) := by
  classical
  let e := S.orderEmbOfFin rfl
  have hval (i : ℕ) (hi : i < S.card) : h / 2 + i * h ≤ e ⟨i, hi⟩ := by
    induction i with
    | zero => simpa using hl _ (S.orderEmbOfFin_mem rfl ⟨0, hi⟩)
    | succ i ih =>
      have hi' : i < S.card := Nat.lt_of_succ_lt hi
      have hlt : e ⟨i, hi'⟩ < e ⟨i + 1, hi⟩ := e.strictMono (by exact Nat.lt_succ_self i)
      have hw := hs _ (S.orderEmbOfFin_mem rfl ⟨i, hi'⟩) _ (S.orderEmbOfFin_mem rfl ⟨i + 1, hi⟩) hlt
      push_cast
      linarith [ih hi']
  have heq : (∑ x ∈ S, x⁻¹) = ∑ i : Fin S.card, (e i)⁻¹ := by
    calc
      _ = ∑ x ∈ (Finset.univ.map e.toEmbedding), x⁻¹ := by rw [Finset.map_orderEmbOfFin_univ]
      _ = _ := Finset.sum_map ..
  rw [heq]
  calc
    _ ≤ ∑ i : Fin S.card, (2 / h) * (((i.val + 1 : ℕ) : ℝ)⁻¹) := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hepos : 0 < e i := lt_of_lt_of_le (half_pos hh) (hl _ (S.orderEmbOfFin_mem rfl i))
      have hbound := hval i.val i.isLt
      push_cast
      have hi : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
      have hi' : (0 : ℝ) < i.val + 1 := by positivity
      rw [← div_eq_mul_inv, div_div, inv_eq_one_div, div_le_div_iff₀ hepos (mul_pos hh hi')]
      nlinarith [mul_nonneg hi hh.le]
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ ((i + 1 : ℕ) : ℝ)⁻¹)]
      simp [harmonic]

private theorem sum_reciprocal_chord_side {ι : Type*} (S : Finset ι) (z : ι → Circle)
    (x : ι → ℝ) {h : ℝ} (hh : 0 < h)
    (hx : ∀ i ∈ S, x i = |(z i : ℂ).arg|) (hl : ∀ i ∈ S, h / 2 ≤ x i)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → h ≤ |x i - x j|) :
    ∑ i ∈ S, ‖(z i : ℂ) - 1‖⁻¹ ≤ (Real.pi / h) * (harmonic S.card : ℝ) := by
  classical
  have hinj : Set.InjOn x S := by
    intro i hi j hj hij
    by_contra hne
    have hg := hsep i hi j hj hne
    rw [hij, sub_self, abs_zero] at hg
    linarith
  have hp := reciprocal_sum_separated (S.image x) hh
    (by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact hl i hi)
    (by
      intro v hv w hw hvw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
      have hne : i ≠ j := fun hij ↦ hvw.ne (congrArg x hij)
      simpa only [abs_of_neg (sub_neg.mpr hvw), neg_sub] using hsep i hi j hj hne)
  rw [Finset.card_image_of_injOn hinj, Finset.sum_image hinj] at hp
  calc
    _ ≤ ∑ i ∈ S, (Real.pi / 2) * (x i)⁻¹ := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      have hxi : 0 < x i := (half_pos hh).trans_le (hl i hi)
      have hc := arg_le_chord (z i)
      rw [← hx i hi] at hc
      have hch : 0 < ‖(z i : ℂ) - 1‖ := by
        by_contra! hn
        nlinarith [Real.pi_pos, mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le hn]
      rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hch hxi]
      linarith
    _ = (Real.pi / 2) * ∑ i ∈ S, (x i)⁻¹ := (Finset.mul_sum ..).symm
    _ ≤ (Real.pi / 2) * ((2 / h) * (harmonic S.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- For separated points on the circle, at most one index must be discarded to
bound the sum of reciprocal chords to one by a harmonic number. Every exact hit belongs
to the discarded set. -/
theorem exists_card_le_one_sum_inv_chord_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (z : ι → Circle) {h : ℝ} (hh : 0 < h)
    (hs : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → h ≤ ‖(z i : ℂ) - z j‖) :
    ∃ E ⊆ S, E.card ≤ 1 ∧ (∀ i ∈ S, (z i : ℂ) = 1 → i ∈ E) ∧
      ∑ i ∈ S \ E, ‖(z i : ℂ) - 1‖⁻¹ ≤ (2 * Real.pi / h) * (harmonic S.card : ℝ) := by
  classical
  let arg (i : ι) := (z i : ℂ).arg
  let E := S.filter fun i ↦ |arg i| < h / 2
  have hang i (hi : i ∈ S) j (hj : j ∈ S) (hne : i ≠ j) : h ≤ |arg i - arg j| :=
    (hs i hi j hj hne).trans (chord_le_arg_difference _ _)
  refine ⟨E, Finset.filter_subset _ _, Finset.card_le_one.mpr ?_, ?_, ?_⟩
  · intro i hi j hj
    obtain ⟨hi, hi'⟩ := Finset.mem_filter.mp hi
    obtain ⟨hj, hj'⟩ := Finset.mem_filter.mp hj
    by_contra hne
    linarith [hang i hi j hj hne, abs_sub (arg i) (arg j)]
  · intro i hi hone
    refine Finset.mem_filter.mpr ⟨hi, ?_⟩
    change |(z i : ℂ).arg| < h / 2
    simpa only [hone, Complex.arg_one, abs_zero] using half_pos hh
  let T := S \ E
  have hlarge i (hi : i ∈ T) : h / 2 ≤ |arg i| := by
    obtain ⟨hiS, hiE⟩ := Finset.mem_sdiff.mp hi
    exact le_of_not_gt (fun hlt ↦ hiE (Finset.mem_filter.mpr ⟨hiS, hlt⟩))
  have hmono {U : Finset ι} (hU : U ⊆ T) : (harmonic U.card : ℝ) ≤ harmonic S.card := by
    have hcard := Finset.card_le_card (hU.trans (Finset.sdiff_subset : T ⊆ S))
    exact_mod_cast (show harmonic U.card ≤ harmonic S.card from
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hcard) (by intros; positivity))
  have hside {U : Finset ι} (hU : U ⊆ T)
      (hdist : ∀ i ∈ U, ∀ j ∈ U, |(|arg i| - |arg j|)| = |arg i - arg j|) :
      ∑ i ∈ U, ‖(z i : ℂ) - 1‖⁻¹ ≤ Real.pi / h * (harmonic S.card : ℝ) := by
    refine (sum_reciprocal_chord_side U z (fun i ↦ |arg i|) hh (fun _ _ ↦ rfl)
      (fun i hi ↦ hlarge i (hU hi)) ?_).trans (mul_le_mul_of_nonneg_left (hmono hU) (by positivity))
    intro i hi j hj hne
    rw [hdist i hi j hj]
    exact hang i (Finset.mem_sdiff.mp (hU hi)).1 j (Finset.mem_sdiff.mp (hU hj)).1 hne
  have hp := hside (U := T.filter (fun i ↦ 0 ≤ arg i)) (Finset.filter_subset _ _) (by
    intro i hi j hj
    rw [abs_of_nonneg (Finset.mem_filter.mp hi).2, abs_of_nonneg (Finset.mem_filter.mp hj).2])
  have hn := hside (U := T.filter (fun i ↦ ¬ 0 ≤ arg i)) (Finset.filter_subset _ _) (by
    intro i hi j hj
    rw [abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hi).2),
      abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hj).2), neg_sub_neg, abs_sub_comm])
  rw [← Finset.sum_filter_add_sum_filter_not T (fun i ↦ 0 ≤ arg i)]
  calc
    _ ≤ _ := add_le_add hp hn
    _ = _ := by ring

end Circle
