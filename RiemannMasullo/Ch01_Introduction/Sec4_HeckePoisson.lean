module

public import RiemannMasullo.Ch01_Introduction.Sec4
import all RiemannMasullo.Ch01_Introduction.Sec4
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Round

/-! # Positive translated Poisson weights of completed Hecke zero divisors

At the point `2 + t i`, the real Cauchy kernel is positive over every zero
of the continued completed Hecke function. Reflection for one character
preserves both the ordinate and the integer multiplicity. Compare
Hiary, Ireland and Kyi, *A method for verifying the generalized Riemann
hypothesis* (2024), §5, Theorem 11 and Lemma 3.
-/

@[expose] public noncomputable section

open NumberField Set
open scoped ComplexConjugate

namespace RiemannMasullo.HeckePoisson

/-- Real part of the Cauchy kernel at `2 + τ i` evaluated on a complex zero. -/
noncomputable def weight (τ : ℝ) (z : ℂ) : ℝ :=
  (2 - z.re) / ((2 - z.re) ^ 2 + (τ - z.im) ^ 2)

/-- Uniform lower Cauchy weight for an ordinate in the closed interval `[a,b]`
on the central line. -/
noncomputable def bracketLowerBound (τ a b : ℝ) : ℝ :=
  (3 / 2) / ((3 / 2) ^ 2 + (max |τ - a| |τ - b|) ^ 2)

/-- Every point in the closed critical strip has nonnegative weight. -/
theorem weight_nonneg (τ : ℝ) (z : ℂ) (hstrip : z.re ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ weight τ z := by
  exact div_nonneg (by linarith [hstrip.2]) (add_nonneg (sq_nonneg _) (sq_nonneg _))

private theorem cell_tangent {x t : ℝ} (hx : 1 ≤ x) (ht : |t| ≤ 1 / 2) :
    (27 - 8 * x) / 25 ≤ x / (x ^ 2 + t ^ 2) := by
  have hx₀ : 0 < x := by linarith
  have ht₂ : t ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) ht 2
  calc
    _ ≤ x / (x ^ 2 + (1 / 2) ^ 2) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [mul_nonneg (sq_nonneg (x - 3 / 2)) (show 0 ≤ 8 * x - 3 by linarith)]
    _ ≤ _ := div_le_div_of_nonneg_left hx₀.le (by positivity) (add_le_add le_rfl ht₂)

/-- A central-line zero in the closed unit cell centered at `τ` contributes at least `3/5`. -/
theorem weight_central_cell (τ : ℝ) (z : ℂ) (hre : z.re = 1 / 2)
    (hcell : |z.im - τ| ≤ 1 / 2) : 3 / 5 ≤ weight τ z := by
  have h := cell_tangent (x := 3 / 2) (t := τ - z.im) (by norm_num)
    (by rwa [abs_sub_comm])
  norm_num [weight, hre] at h ⊢
  exact h

/-- The two reflected points have the same ordinate. Their total weight on the
closed unit cell is at least `6/5`, uniformly over the closed critical strip. -/
theorem weight_reflected_cell (τ : ℝ) (z : ℂ) (hstrip : z.re ∈ Set.Icc (0 : ℝ) 1)
    (hcell : |z.im - τ| ≤ 1 / 2) : 6 / 5 ≤ weight τ z + weight τ (1 - conj z) := by
  have ht : |τ - z.im| ≤ 1 / 2 := by rwa [abs_sub_comm]
  have h₁ := cell_tangent (x := 2 - z.re) (by linarith [hstrip.2]) ht
  have h₂ := cell_tangent (x := 1 + z.re) (by linarith [hstrip.1]) ht
  simp only [weight, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.conj_re, Complex.conj_im, zero_sub, neg_neg,
    show (2 : ℝ) - (1 - z.re) = 1 + z.re by ring]
  linarith only [h₁, h₂]

/-- A genuine central zero with an ordinate in `[a,b]` contributes at least
the endpoint cost `bracketLowerBound τ a b`. -/
theorem weight_central_bracket (τ a b : ℝ) (z : ℂ) (hre : z.re = 1 / 2)
    (hord : z.im ∈ Set.Icc a b) : bracketLowerBound τ a b ≤ weight τ z := by
  have hdist : |τ - z.im| ≤ max |τ - a| |τ - b| := by
    apply abs_le.mpr
    constructor
    · linarith [le_max_right |τ - a| |τ - b|, neg_abs_le (τ - b), hord.2]
    · linarith [le_max_left |τ - a| |τ - b|, le_abs_self (τ - a), hord.1]
  have hsq : (τ - z.im) ^ 2 ≤ (max |τ - a| |τ - b|) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hdist 2
  simp only [bracketLowerBound, weight, hre, show (2 : ℝ) - 1 / 2 = 3 / 2 by norm_num]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (add_le_add le_rfl hsq)

/-- An off-central reflected pair costs strictly more than `6/5`, including
at the top and bottom edges of the closed unit cell. -/
theorem weight_reflected_cell_lt (τ : ℝ) (z : ℂ) (hstrip : z.re ∈ Set.Icc (0 : ℝ) 1)
    (hcell : |z.im - τ| ≤ 1 / 2) (hoff : z.re ≠ 1 / 2) :
    6 / 5 < weight τ z + weight τ (1 - conj z) := by
  have ht : |τ - z.im| ≤ 1 / 2 := by rwa [abs_sub_comm]
  let x := 2 - z.re
  have hx : 1 ≤ x := by dsimp [x]; linarith [hstrip.2]
  have hx₀ : 0 < x := by linarith
  have hxoff : x - 3 / 2 ≠ 0 := by
    intro heq
    apply hoff
    dsimp [x] at heq
    linarith
  have h₁ : (27 - 8 * x) / 25 < x / (x ^ 2 + (τ - z.im) ^ 2) := by
    have ht₂ : (τ - z.im) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ht 2
    calc
      _ < x / (x ^ 2 + (1 / 2) ^ 2) := by
        apply (lt_div_iff₀ (by positivity)).mpr
        nlinarith [mul_pos (sq_pos_of_ne_zero hxoff) (show 0 < 8 * x - 3 by linarith)]
      _ ≤ _ := div_le_div_of_nonneg_left hx₀.le (by positivity) (add_le_add le_rfl ht₂)
  have h₂ := cell_tangent (x := 1 + z.re) (by linarith [hstrip.1]) ht
  simp only [weight, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.conj_re, Complex.conj_im, zero_sub, neg_neg,
    show (2 : ℝ) - (1 - z.re) = 1 + z.re by ring]
  dsimp only [x] at h₁
  linarith only [h₁, h₂]

/-- Closed unit cells centered at integers cover every real ordinate. -/
theorem exists_int_cell (y : ℝ) : ∃ k : ℤ, |y - (k : ℝ)| ≤ 1 / 2 :=
  ⟨round y, abs_sub_round y⟩

variable {F : Type*} [Field F] [NumberField F]
local notation "U𝔽" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "ord(" χ ", " z ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z

/-- A positive divisor site of the continued completed Hecke function. -/
abbrev Site (χ : U𝔽) := {z : ℂ // 0 < ord(χ, z)}

/-- The multiplicity of the zero, as recorded by the meromorphic divisor. -/
def multiplicity {χ : U𝔽} (z : Site χ) : ℕ := (ord(χ, z.val)).toNat

/-- The full contribution of one site, counting every copy. -/
def siteWeight {χ : U𝔽} (t : ℝ) (z : Site χ) : ℝ := (multiplicity z : ℝ) * weight t z.val

/-- Reflection across the critical line preserves the divisor of each individual
completed unitary Hecke function at every point, including poles. -/
theorem divisor_reflection (χ : U𝔽) (z : ℂ) : ord(χ, 1 - conj z) = ord(χ, z) := by
  have horder : meromorphicOrderAt (continuedCompletedHeckeL χ) (1 - conj z) =
      meromorphicOrderAt (continuedCompletedHeckeL χ) z := by
    by_cases hz : z.re < 1
    · exact introTrace_single_character_reflected_order χ z hz
    · have hr : (1 - conj z).re < 1 := by simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
      simpa only [map_sub, map_one, Complex.conj_conj, sub_sub_cancel] using
        (introTrace_single_character_reflected_order χ (1 - conj z) hr).symm
  have hL := (continuedCompletedHeckeL_spec χ).1.meromorphicOn
  rw [MeromorphicOn.divisor_apply hL (mem_univ _), MeromorphicOn.divisor_apply hL (mem_univ _), horder]

/-- Every positive divisor point belongs to the open critical strip. -/
theorem positive_divisor_re_mem_Ioo (χ : U𝔽) {z : ℂ} (hz : 0 < ord(χ, z)) :
    z.re ∈ Ioo (0 : ℝ) 1 := by
  have h := abs_lt.mp (introTrace_positive_divisor_in_critical_strip χ z hz)
  constructor <;> linarith [h.1, h.2]

/-- The strip bound for a zero already indexed by its positive divisor. -/
theorem siteStrip {χ : U𝔽} (z : Site χ) : z.val.re ∈ Icc (0 : ℝ) 1 :=
  Ioo_subset_Icc_self (positive_divisor_re_mem_Ioo χ z.property)

/-- Reflection is an involutive permutation of the positive divisor sites of a fixed
unitary character. -/
def positiveSiteReflection (χ : U𝔽) :
    Site χ ≃ Site χ where
  toFun z := ⟨1 - conj z.val, (divisor_reflection χ z.val).symm ▸ z.property⟩
  invFun z := ⟨1 - conj z.val, (divisor_reflection χ z.val).symm ▸ z.property⟩
  left_inv z := Subtype.ext (by simp)
  right_inv z := Subtype.ext (by simp)

/-- Reflection of an actual zero site keeps its original imaginary coordinate. -/
@[simp] theorem positiveSiteReflection_im (χ : U𝔽) (z : Site χ) :
    ((positiveSiteReflection χ z).val).im = z.val.im := by
  change (1 - conj z.val).im = z.val.im
  simp

/-- Reflection identifies the multiplicities of the two actual sites. -/
@[simp] theorem multiplicity_reflection {χ : U𝔽} (z : Site χ) :
    multiplicity (positiveSiteReflection χ z) = multiplicity z :=
  congrArg Int.toNat (divisor_reflection χ z.val)

/-- A positive site accounts for at least one copy. -/
theorem one_le_multiplicity {χ : U𝔽} (z : Site χ) : 1 ≤ multiplicity z := by
  change 1 ≤ (ord(χ, z.val)).toNat
  have := z.property
  omega

/-- Removing the multiplicity factor can only lower a site contribution. -/
theorem weight_le_siteWeight {χ : U𝔽} (t : ℝ) (z : Site χ) :
    weight t z.val ≤ siteWeight t z := by
  have hr : (1 : ℝ) ≤ (multiplicity z : ℝ) := by exact_mod_cast one_le_multiplicity z
  simpa [siteWeight] using mul_le_mul_of_nonneg_right hr (weight_nonneg t z.val (siteStrip z))

/-- Multiplicity-weighted contributions are nonnegative at every center. -/
theorem siteWeight_nonneg {χ : U𝔽} (t : ℝ) (z : Site χ) : 0 ≤ siteWeight t z :=
  (weight_nonneg t z.val (siteStrip z)).trans (weight_le_siteWeight t z)

local notation "window(" χ ")" => {z : ℂ // 0 < ord(χ, z) ∧ |Complex.re z - 1/2| < (1/2 : ℝ)}

private theorem weight_le_two_mul_reciprocal_sq (τ : ℝ) (z : ℂ) (hz : 0 ≤ z.re) :
    weight τ z ≤ 2 * ‖((⟨3/2, τ⟩ : ℂ) - (z - 1/2))⁻¹‖ ^ 2 := by
  let d := (2 - z.re) ^ 2 + (τ - z.im) ^ 2
  have hnorm : ‖(⟨3/2, τ⟩ : ℂ) - (z - 1/2)‖ ^ 2 = d := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
      Complex.one_re, Complex.one_im, zero_div, sub_zero]
    dsimp only [d]
    ring
  rw [norm_inv, inv_pow, hnorm, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right (by linarith) (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- At every translate, the Cauchy weights of all positive divisor sites of the
continued completed Hecke L-function are summable with their actual multiplicities. -/
theorem summable_siteWeight (χ : U𝔽) (τ : ℝ) :
    Summable (siteWeight (χ := χ) τ) := by
  change Summable (fun z : Site χ ↦ ((ord(χ, z.val)).toNat : ℝ) * weight τ z.val)
  let b : ℂ := ⟨3/2, τ⟩
  let i : Site χ → window(χ) := fun z ↦
    ⟨z.val, z.property, introTrace_positive_divisor_in_critical_strip χ z.val z.property⟩
  have hi : Function.Injective i := fun _ _ h ↦
    Subtype.ext (congrArg (fun r : window(χ) ↦ r.val) h)
  have hsep (r : window(χ)) : b ≠ r.val - 1/2 := by
    intro h
    have he := congrArg Complex.re h
    simp only [b, Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at he
    linarith [(abs_lt.mp r.property.2).2]
  have hwindow := introTrace_canonical_reciprocal_squares χ (1/2) b hsep
  have hs := hwindow.comp_injective (i := i) hi
  change Summable (fun z : Site χ ↦ (ord(χ, z.val) : ℝ) * ‖(b - (z.val-1/2))⁻¹‖ ^ 2) at hs
  apply (hs.mul_left 2).of_norm_bounded
  intro z
  have hz := siteStrip z
  have hm : 0 ≤ (ord(χ, z.val) : ℝ) := (Int.cast_pos.mpr z.property).le
  have hn : ((ord(χ, z.val)).toNat : ℝ) = (ord(χ, z.val) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg z.property.le
  rw [Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (weight_nonneg τ z.val hz)), hn]
  calc
    _ ≤ (ord(χ, z.val) : ℝ) * (2 * ‖(b - (z.val-1/2))⁻¹‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (weight_le_two_mul_reciprocal_sq τ z.val hz.1) hm
    _ = _ := by ring

end RiemannMasullo.HeckePoisson
