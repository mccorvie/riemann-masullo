module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sharp height cutoffs for completed Hecke zeros

The joint zero count in the proof of Lemma B.4.4.9 gives polynomial clearance at every integer
height, uniformly over the angular characters of a fixed Bruhat quotient. These
cutoffs can be used to group the spectral blocks in §10.3. Each character is
normalized on the chosen norm section, so its physical height is the imaginary
part of its zero.
-/

public noncomputable section

open Set Function NumberField
open scoped BigOperators NNReal NumberField.AdeleRing

namespace RiemannMasullo

private theorem exists_clear_grid_point (s : Finset ℝ) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ i : Fin (s.card + 1), ∀ x ∈ s, r ≤ |a + (2 * (i.val : ℝ) + 1) * r - x| := by
  classical
  by_contra! h
  choose x hx hclose using h
  let f : Fin (s.card + 1) → ↥s := fun i ↦ ⟨x i, hx i⟩
  have distinct {i j : Fin (s.card + 1)} (hij : i < j) : f i ≠ f j := by
    intro heq
    have hxij : x i = x j := congrArg Subtype.val heq
    have hstep : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
      exact_mod_cast (show i.val + 1 ≤ j.val from hij)
    have hi := (abs_lt.mp (hclose i)).1
    have hj := (abs_lt.mp (hclose j)).2
    rw [hxij] at hi
    nlinarith [mul_nonneg (sub_nonneg.mpr hstep) hr.le]
  have hinj : Function.Injective f := by
    intro i j heq
    rcases lt_trichotomy i j with h | h | h
    · exact (distinct h heq).elim
    · exact h
    · exact (distinct h heq.symm).elim
  have hc := Fintype.card_le_of_injective f hinj
  simp at hc

/-- A cutoff can be kept away from all sites of an arbitrary divisor by a distance
depending only on the width and the number of sites in the interval. -/
private theorem exists_cutoff_clearance (T : Set ℝ) (s : Finset ℝ) {a b : ℝ} (hab : a < b)
    (hs : ∀ x ∈ T, x ∈ Set.Icc a b → x ∈ s) :
    let r := (b - a) / (2 * ((s.card : ℝ) + 1))
    ∃ c : ℝ, a + r ≤ c ∧ c ≤ b - r ∧ ∀ x ∈ T, r ≤ |c - x| := by
  let r := (b - a) / (2 * ((s.card : ℝ) + 1))
  change ∃ c : ℝ, a + r ≤ c ∧ c ≤ b - r ∧ _
  have hr : 0 < r := div_pos (sub_pos.mpr hab) (by positivity)
  have hmul : r * (2 * ((s.card : ℝ) + 1)) = b - a :=
    div_mul_cancel₀ _ (by positivity)
  obtain ⟨i, hi⟩ := exists_clear_grid_point s a hr
  let c := a + (2 * (i.val : ℝ) + 1) * r
  have hlower : a + r ≤ c := by
    dsimp [c]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) i.val) hr.le]
  have hindex : (i.val : ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hupper : c ≤ b - r := by
    dsimp [c]
    nlinarith [mul_nonneg (sub_nonneg.mpr hindex) hr.le]
  refine ⟨c, hlower, hupper, fun x hx ↦ ?_⟩
  by_cases left : a ≤ x
  · by_cases right : x ≤ b
    · exact hi x (hs x hx ⟨left, right⟩)
    · exact le_trans (by linarith : r ≤ -(c - x)) (neg_le_abs _)
  · exact le_trans (by linarith : r ≤ c - x) (le_abs_self _)

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "K𝔽" => (ideleClassNorm F).ker
local notation "Chars(" τ ")" => {χ : PontryaginDual C𝔽 // ∀ u : ℝ≥0ˣ, χ (τ u) = 1}
local notation "StageChars(" τ ", " k ")" => {χ : Chars(τ) // ∀ u : k, χ.val u.val = 1}
local notation "Order(" χ ", " s ")" =>
  MeromorphicOn.divisor (explicitFormulaCompletedHeckeL χ) Set.univ s
local notation "Zeros(" τ ")" => {z : Chars(τ) × ℂ // 0 < Order(z.1.val, z.2)}
local notation "angular(" Y ", " χ ", " i ")" =>
  ‖bruhatDirectionalDeriv (Y i) (fun u : K𝔽 ↦ (χ (u : C𝔽) : ℂ)) 1‖
local notation "angularSize(" Y ", " χ ")" => (∑ i, ⌈angular(Y, χ, i)⌉₊ : ℕ)
local notation "clearCutoffs(" χ ", " j ", " δ ")" =>
  {c : ℝ | c ∈ Icc ((j : ℝ) + 1 / 4) ((j : ℝ) + 3 / 4) ∧
    ∀ s : ℂ, 0 < Order(χ, s) → δ ≤ |c - s.im|}

private theorem angular_le_size {r : ℕ} (Y : Fin r → LCATopologicalLie K𝔽)
    (χ : PontryaginDual C𝔽) (i : Fin r) :
    angular(Y, χ, i) ≤ (angularSize(Y, χ) : ℝ) := by
  refine (Nat.le_ceil _).trans ?_
  exact_mod_cast (Finset.single_le_sum (f := fun j ↦ ⌈angular(Y, χ, j)⌉₊)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i))

private theorem finite_of_card_bound {Z : Type*} (X : Set Z) (B : ℝ)
    (h : ∀ S : Finset Z, (↑S : Set Z) ⊆ X → (S.card : ℝ) ≤ B) : X.Finite := by
  by_contra hinf
  obtain ⟨n, hn⟩ := exists_nat_gt B
  obtain ⟨S, hS, hc⟩ := (show X.Infinite from hinf).exists_subset_card_eq n
  have hbad := h S hS
  rw [hc] at hbad
  exact (not_lt_of_ge hbad) hn

/-- A nonempty set of cutoffs with a prescribed clearance in a closed window has a
least member. This selects one reproducible boundary from the simultaneous interval bound. -/
private theorem exists_least_clearance {ι : Type*} (admit : ι → Prop) (v : ι → ℝ) (l u δ : ℝ)
    (h : ∃ c ∈ Icc l u, ∀ i, admit i → δ ≤ |c - v i|) :
    ∃ c, IsLeast {c : ℝ | c ∈ Icc l u ∧ ∀ i, admit i → δ ≤ |c - v i|} c := by
  let S : Set ℝ := {c | c ∈ Icc l u ∧ ∀ i, admit i → δ ≤ |c - v i|}
  have hset : S = Icc l u ∩ ⋂ i : {i : ι // admit i}, {c : ℝ | δ ≤ |c - v i.val|} := by
    ext c
    change (_ ∧ _) ↔ (_ ∧ _)
    simp only [mem_iInter, mem_ofPred_eq, Subtype.forall]
  have hclosed : IsClosed S := by
    rw [hset]
    exact isClosed_Icc.inter (isClosed_iInter (fun i ↦
      isClosed_le continuous_const ((continuous_id.sub continuous_const).abs)))
  exact (isCompact_Icc.of_isClosed_subset hclosed (fun _ hc ↦ hc.1)).exists_isLeast h

/-- For each character of a fixed Bruhat quotient and each integer height, take the least
boundary in the middle half of the unit interval with the displayed clearance from
every zero of the completed Hecke function. The coefficient and exponent are shared by
all characters and heights. The angular term is the sum of rounded frequencies along
the finite family of flows provided by the joint divisor count of Lemma B.4.4.9. -/
theorem exists_least_clear_hecke_zero_cutoffs (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (k : Subgroup C𝔽) (hk : IsBruhatGoodSubgroup k) :
    ∃ (r : ℕ) (Y : Fin r → LCATopologicalLie K𝔽) (B : ℝ) (d : ℕ), 0 < B ∧
      ∃ cut : StageChars(τ, k) → ℤ → ℝ,
        ∀ χ (j : ℤ), IsLeast (clearCutoffs(χ.val.val, j,
          1 / (B * (2 + |(j : ℝ)| + (angularSize(Y, χ.val.val) : ℝ)) ^ d))) (cut χ j) := by
  classical
  obtain ⟨r, Y, C, d, hcount⟩ :=
    idelicExplicitFormula_summable_spectral_characters_polynomialCount τ hτ k hk
  let B := 4 * (max C 0 + 1)
  have hB : 0 < B := by dsimp [B]; linarith [le_max_right C 0]
  refine ⟨r, Y, B, d, hB, ?_⟩
  let δ (χ : StageChars(τ, k)) (j : ℤ) :=
    1 / (B * (2 + |(j : ℝ)| + (angularSize(Y, χ.val.val) : ℝ)) ^ d)
  suffices h : ∀ (χ : StageChars(τ, k)) (j : ℤ),
      ∃ c, IsLeast (clearCutoffs(χ.val.val, j, δ χ j)) c by
    choose cut hcut using h
    exact ⟨cut, hcut⟩
  intro χ j
  refine exists_least_clearance (fun s : ℂ ↦ 0 < Order(χ.val.val, s)) Complex.im _ _ _ ?_
  let T : ℕ := j.natAbs + angularSize(Y, χ.val.val) + 1
  let W : ℝ := 2 + |(j : ℝ)| + (angularSize(Y, χ.val.val) : ℝ)
  have hTW : (T : ℝ) + 1 = W := by
    simp only [T, W, Nat.cast_add, Nat.cast_one, Nat.cast_natAbs, Int.cast_abs]
    ring
  have hW : 1 ≤ W := by
    dsimp [W]
    linarith [abs_nonneg (j : ℝ), Nat.cast_nonneg (α := ℝ) (angularSize(Y, χ.val.val))]
  let a : ℝ := (j : ℝ) + 1 / 4
  let b : ℝ := (j : ℝ) + 3 / 4
  let X : Set (Zeros(τ)) := {z | z.val.1 = χ.val ∧ z.val.2.im ∈ Icc a b}
  have hc (S : Finset (Zeros(τ))) (hS : (↑S : Set (Zeros(τ))) ⊆ X) :
      (S.card : ℝ) ≤ C * W ^ d := by
    have hh := hcount T S (by
      intro z hz
      obtain ⟨hχ, hloc⟩ := hS hz
      rw [hχ, hTW]
      refine ⟨χ.property, ?_, fun i ↦ ?_⟩
      · obtain ⟨hl, hu⟩ := hloc
        dsimp [a, b] at hl hu
        rw [abs_lt]
        dsimp [W]
        constructor <;> linarith [le_abs_self (j : ℝ), neg_le_abs (j : ℝ),
          Nat.cast_nonneg (α := ℝ) (angularSize(Y, χ.val.val))]
      · have hi := angular_le_size Y χ.val.val i
        dsimp [W]
        linarith [abs_nonneg (j : ℝ)])
    rw [hTW] at hh
    refine le_trans ?_ hh
    calc
      (S.card : ℝ) = ∑ _z ∈ S, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun z _ ↦ by
        rw [Complex.norm_intCast, abs_of_pos (by exact_mod_cast z.property)]
        exact_mod_cast (show (1 : ℤ) ≤ Order(z.val.1.val, z.val.2) from z.property)
  have hX := finite_of_card_bound X _ hc
  let S := hX.toFinset
  let pts : Finset ℝ := S.image (fun z ↦ z.val.2.im)
  have hcard : (pts.card : ℝ) ≤ C * W ^ d := by
    have hi : (pts.card : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast (Finset.card_image_le (s := S) (f := fun z : Zeros(τ) ↦ z.val.2.im))
    exact hi.trans (hc S (fun z hz ↦ hX.mem_toFinset.mp hz))
  let ordinates : Set ℝ := {v | ∃ z : Zeros(τ), z.val.1 = χ.val ∧ z.val.2.im = v}
  have cover (v : ℝ) (hv : v ∈ ordinates) (hloc : v ∈ Icc a b) : v ∈ pts := by
    obtain ⟨z, hχ, rfl⟩ := hv
    exact Finset.mem_image.mpr ⟨z, hX.mem_toFinset.mpr ⟨hχ, hloc⟩, rfl⟩
  have hab : a < b := by dsimp [a, b]; linarith
  obtain ⟨c, hl, hu, hc⟩ := exists_cutoff_clearance ordinates pts hab cover
  let ρ := (b - a) / (2 * ((pts.card : ℝ) + 1))
  have hρ : 0 ≤ ρ := div_nonneg (sub_nonneg.mpr hab.le) (by positivity)
  change a + ρ ≤ c at hl
  change c ≤ b - ρ at hu
  refine ⟨c, ⟨by change a ≤ c; linarith, by change c ≤ b; linarith⟩, ?_⟩
  intro s hs
  apply le_trans _ (hc _ ⟨⟨(χ.val, s), hs⟩, rfl, rfl⟩)
  change 1 / (B * W ^ d) ≤ (b - a) / (2 * ((pts.card : ℝ) + 1))
  have hp : 1 ≤ W ^ d := one_le_pow₀ hW
  have hC : C * W ^ d ≤ max C 0 * W ^ d :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (le_trans zero_le_one hp)
  apply (div_le_div_iff₀ (mul_pos hB (lt_of_lt_of_le zero_lt_one hp)) (by positivity)).mpr
  have hwidth : b - a = 1 / 2 := by dsimp [a, b]; ring
  rw [hwidth]
  dsimp [B]
  nlinarith [hcard.trans hC]

end RiemannMasullo
