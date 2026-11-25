module

public import RiemannMasullo.Ch01_Introduction.Sec4_HeckePoisson
public import RiemannMasullo.Ch12_TraceGeometric.Sec5
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Expanding Poisson mass of off-line completed Hecke zeros

Masullo, Theorem 12.5.1.1, pp. 519–520. Hiary, Ireland and Kyi (2024),
§§4–5, use the real logarithmic derivative, positivity and reflected pairs to
test finite height intervals. Here the abscissa tends to infinity on the real
axis. The scaled deficit from the true central contribution recovers the full
off-line multiplicity, including an infinite count.
-/

@[expose] public noncomputable section

open Filter NumberField Set Topology
open scoped ComplexConjugate ENNReal

namespace RiemannMasullo.HeckePoisson

/-- A single zero contributes one copy in the expanding real-width limit. -/
theorem tendsto_scaledPoissonWeight (x y : ℝ) :
    Tendsto (fun a : ℝ ↦ a * (a + 1 / 2 - x) / ((a + 1 / 2 - x) ^ 2 + y ^ 2))
      atTop (𝓝 1) := by
  have h := (tendsto_inv_atTop_zero : Tendsto (fun a : ℝ ↦ a⁻¹) atTop (𝓝 0))
  have hp : Tendsto (fun a : ℝ ↦ 1 + (1 / 2 - x) * a⁻¹) atTop (𝓝 1) := by
    simpa using (h.const_mul (1 / 2 - x)).const_add 1
  have hq : Tendsto (fun a : ℝ ↦ y * a⁻¹) atTop (𝓝 0) := by
    simpa using h.const_mul y
  have hh := hp.div ((hp.pow 2).add (hq.pow 2)) (by norm_num)
  simp only [one_pow, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    add_zero, div_one] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  have hp' : 1 + (1 / 2 - x) * a⁻¹ = (a + 1 / 2 - x) / a := by
    field_simp
    ring
  change (1 + (1 / 2 - x) * a⁻¹) / ((1 + (1 / 2 - x) * a⁻¹) ^ 2 + (y * a⁻¹) ^ 2) = _
  rw [hp', ← div_eq_mul_inv, div_pow, div_pow, ← add_div, div_div_eq_mul_div,
    pow_two a, ← mul_assoc, div_mul_cancel₀ _ ha.ne', mul_comm]

/-- On a family with positive integral multiplicities, any nonnegative weights that tend
pointwise to those multiplicities converge in total to their extended sum. In the infinite
case finite subsums alone force the total to tend to infinity. -/
theorem tendsto_tsum_of_positive_nat_limits {ι α : Type*} {l : Filter α}
    (m : ι → ℕ) (hm : ∀ i, 0 < m i) (f : α → ι → ℝ≥0∞)
    (hf : ∀ i, Tendsto (fun a ↦ f a i) l (𝓝 (m i : ℝ≥0∞))) :
    Tendsto (fun a ↦ ∑' i, f a i) l (𝓝 (∑' i, (m i : ℝ≥0∞))) := by
  classical
  cases finite_or_infinite ι with
  | inl h =>
    let _ := Fintype.ofFinite ι
    simp only [tsum_fintype]
    exact tendsto_finsetSum _ (fun i _ ↦ hf i)
  | inr h =>
    have ho (i : ι) : 1 ≤ (m i : ℝ≥0∞) := by exact_mod_cast hm i
    have ht : (∑' i, (m i : ℝ≥0∞)) = ⊤ := by
      apply top_unique
      rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ι) (c := 1) one_ne_zero]
      exact tsum_le_tsum ho
    rw [ht]
    apply ENNReal.tendsto_nhds_top
    intro n
    obtain ⟨s, hs⟩ := Finset.exists_card_eq (α := ι) (n + 1)
    have hn : (n : ℝ≥0∞) < ∑ i ∈ s, (m i : ℝ≥0∞) := calc
      (n : ℝ≥0∞) < (s.card : ℝ≥0∞) := by rw [hs]; exact_mod_cast Nat.lt_succ_self n
      _ = ∑ _i ∈ s, (1 : ℝ≥0∞) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ ↦ ho i)
    filter_upwards [(tendsto_finsetSum s (fun i _ ↦ hf i)).eventually (eventually_gt_nhds hn)] with a ha
    exact ha.trans_le (sum_le_tsum s)

/-- The scaled Poisson sum detects the full multiplicity, including an infinite total.
Only positivity of the integer multiplicities is needed. -/
theorem tendsto_tsum_scaledPoissonWeight {ι : Type*}
    (m : ι → ℕ) (hm : ∀ i, 0 < m i) (x y : ι → ℝ) :
    Tendsto (fun a : ℝ ↦ ∑' i, ENNReal.ofReal ((m i : ℝ) *
      (a * (a + 1 / 2 - x i) / ((a + 1 / 2 - x i) ^ 2 + (y i) ^ 2))))
      atTop (𝓝 (∑' i, (m i : ℝ≥0∞))) := by
  apply tendsto_tsum_of_positive_nat_limits m hm
  intro i
  simpa using ENNReal.tendsto_ofReal ((tendsto_scaledPoissonWeight (x i) (y i)).const_mul (m i : ℝ))

/-! ## Multiplicities of completed Hecke zeros -/

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
local notation "U𝔽" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "ord(" χ ", " z ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "Off(" χ ")" => {z : Site χ // z.val.re ≠ 1 / 2}
local notation "Central(" χ ")" => {z : Site χ // z.val.re = 1 / 2}

/-- The actual number of zeros off the critical line of one completed Hecke function,
counted with their positive divisor multiplicities. An infinite count has value infinity. -/
def offLineCount (χ : U𝔽) : ℝ≥0∞ := ∑' z : Off(χ), (multiplicity z.val : ℝ≥0∞)

/-- Sum of the scaled Cauchy weights over precisely the critical-line zeros, with multiplicity. -/
def centralSoftCount (χ : U𝔽) (a : ℝ) : ℝ :=
  ∑' z : Central(χ), (multiplicity z.val : ℝ) * a ^ 2 / (a ^ 2 + z.val.val.im ^ 2)

private def unscaledWeight {χ : U𝔽} (a : ℝ) (z : Site χ) : ℝ :=
  (multiplicity z : ℝ) * ((a + 1 / 2 - z.val.re) /
    ((a + 1 / 2 - z.val.re) ^ 2 + z.val.im ^ 2))

private def scaledWeight {χ : U𝔽} (a : ℝ) (z : Site χ) : ℝ :=
  (multiplicity z : ℝ) * (a * (a + 1 / 2 - z.val.re) /
    ((a + 1 / 2 - z.val.re) ^ 2 + z.val.im ^ 2))

private theorem scaledWeight_nonneg {χ : U𝔽} {a : ℝ} (ha : 1 / 2 < a) (z : Site χ) :
    0 ≤ scaledWeight a z := by
  have hb := (positive_divisor_re_mem_Ioo χ z.property).2
  have ha₀ : 0 ≤ a := by linarith
  have hδ : 0 ≤ a + 1 / 2 - z.val.re := by linarith
  unfold scaledWeight
  positivity

/-- In the expanding-width limit, each off-line divisor site contributes exactly its multiplicity. -/
theorem tendsto_offLineSoftCount (χ : U𝔽) :
    Tendsto (fun a : ℝ ↦ ∑' z : Off(χ), ENNReal.ofReal ((multiplicity z.val : ℝ) *
      (a * (a + 1 / 2 - z.val.val.re) / ((a + 1 / 2 - z.val.val.re) ^ 2 + z.val.val.im ^ 2))))
      atTop (𝓝 (offLineCount χ)) :=
  tendsto_tsum_scaledPoissonWeight (fun z : Off(χ) ↦ multiplicity z.val)
    (fun z ↦ one_le_multiplicity z.val) (fun z ↦ z.val.val.re) (fun z ↦ z.val.val.im)

/-- A zero away from the central line and its distinct reflection contribute twice the actual
multiplicity to the off-line count for the same character. -/
theorem two_mul_multiplicity_le_offLineCount {χ : U𝔽} (z : Site χ) (hz : z.val.re ≠ 1 / 2) :
    2 * (multiplicity z : ℝ≥0∞) ≤ offLineCount χ := by
  classical
  let r := positiveSiteReflection χ z
  have hre : r.val.re = 1 - z.val.re := by
    change (1 - conj z.val).re = _
    simp
  have hr : r.val.re ≠ 1 / 2 := fun h ↦ hz (by linarith)
  let u : Off(χ) := ⟨z, hz⟩
  let v : Off(χ) := ⟨r, hr⟩
  have hne : u ≠ v := fun he ↦ hz (by
    have he' : z.val.re = r.val.re := congrArg (fun x : Off(χ) ↦ x.val.val.re) he
    linarith)
  have hs := sum_le_tsum (f := fun w : Off(χ) ↦ (multiplicity w.val : ℝ≥0∞))
    ({u, v} : Finset Off(χ))
  simp only [Finset.mem_singleton, hne, not_false_eq_true, Finset.sum_insert,
    Finset.sum_singleton] at hs
  change (multiplicity z : ℝ≥0∞) + (multiplicity r : ℝ≥0∞) ≤ offLineCount χ at hs
  rw [show multiplicity r = multiplicity z from multiplicity_reflection z] at hs
  rwa [two_mul]

private theorem hasSum_scaledWeight {χ : U𝔽} {a d : ℝ}
    (hd : HasSum (unscaledWeight (χ := χ) a) d) :
    HasSum (scaledWeight (χ := χ) a) (a * d) := (hd.mul_left a).congr_fun <| by
  intro z
  dsimp [unscaledWeight, scaledWeight]
  ring

private theorem deficit_eq_tsum {χ : U𝔽} {a d : ℝ}
    (hs : HasSum (scaledWeight (χ := χ) a) (a * d)) :
    a * d - centralSoftCount χ a = ∑' z : Off(χ), scaledWeight a z.val := by
  have hc : (∑' z : Central(χ), scaledWeight a z.val) = centralSoftCount χ a := by
    unfold centralSoftCount
    apply tsum_congr
    intro z
    simp only [scaledWeight, z.property, add_sub_cancel_right]
    ring
  have hsplit := hs.summable.tsum_subtype_add_tsum_subtype_compl {z : Site χ | z.val.re = 1 / 2}
  change (∑' z : Central(χ), scaledWeight a z.val) + (∑' z : Off(χ), scaledWeight a z.val) =
    ∑' z, scaledWeight a z at hsplit
  rw [hc, hs.tsum_eq] at hsplit
  linarith

private theorem ofReal_deficit_eq {χ : U𝔽} {a d : ℝ} (ha : 1 / 2 < a)
    (hd : HasSum (unscaledWeight (χ := χ) a) d) :
    ENNReal.ofReal (a * d - centralSoftCount χ a) =
      ∑' z : Off(χ), ENNReal.ofReal (scaledWeight a z.val) := by
  have hs := hasSum_scaledWeight hd
  rw [deficit_eq_tsum hs]
  exact ENNReal.ofReal_tsum_of_nonneg (fun z ↦ scaledWeight_nonneg ha z.val) (hs.summable.subtype _)


/-- The Cauchy weight of all completed zeros at a real abscissa, with the scale factored out. -/
def zeroPoissonMass (χ : U𝔽) (a : ℝ) : ℝ :=
  ∑' z : Site χ, (multiplicity z : ℝ) * ((a + 1 / 2 - z.val.re) /
    ((a + 1 / 2 - z.val.re) ^ 2 + z.val.im ^ 2))

private theorem summable_unscaledWeight (χ : U𝔽) {a : ℝ} (ha : 1 / 2 < a) :
    Summable (unscaledWeight (χ := χ) a) := by
  have h0 : Summable (fun z : Site χ ↦ (multiplicity z : ℝ) / (1 + |z.val.im|) ^ 2) := by
    have h : Summable (fun z : Site χ ↦ (ord(χ, z.val) : ℝ) / (1 + |z.val.im|) ^ 2) :=
      explicitFormulaCompletedHeckeL_summable_divisor_div_sq χ
    apply h.congr
    intro z
    have hm : (multiplicity z : ℝ) = (ord(χ, z.val) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg z.property.le
    rw [hm]
  let δ := a - 1 / 2
  let k := max 1 (δ^2)⁻¹
  have hδ : 0 < δ := sub_pos.mpr ha
  have hk : 1 ≤ k := le_max_left _ _
  apply (h0.mul_left (2 * k * (a + 1 / 2))).of_norm_bounded
  intro z
  let b := a + 1 / 2 - z.val.re
  let y := z.val.im
  have hstrip := siteStrip z
  have hb : δ ≤ b := by dsimp [δ, b]; linarith [hstrip.2]
  have hu : b ≤ a + 1 / 2 := by dsimp [b]; linarith [hstrip.1]
  have hD : 0 < b^2 + y^2 := by have := hδ.trans_le hb; positivity
  have hH : 0 < (1+|y|)^2 := by positivity
  have hone : 1 ≤ k*b^2 := calc
    1 = (δ^2)⁻¹ * δ^2 := (inv_mul_cancel₀ (pow_ne_zero 2 hδ.ne')).symm
    _ ≤ k * b^2 := mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ hδ.le hb 2)
      (sq_nonneg δ) (by linarith)
  have hy : y^2 ≤ k * y^2 := le_mul_of_one_le_left (sq_nonneg _) hk
  have hscale : (1+|y|)^2 ≤ 2*k*(b^2+y^2) := by nlinarith [sq_nonneg (1-|y|), sq_abs y]
  have hw : b / (b^2+y^2) ≤ (2*k*(a+1/2)) / (1+|y|)^2 := by
    apply (div_le_div_iff₀ hD hH).mpr
    calc
      b * (1+|y|)^2 ≤ (a+1/2) * (1+|y|)^2 := mul_le_mul_of_nonneg_right hu hH.le
      _ ≤ (a+1/2) * (2*k*(b^2+y^2)) := mul_le_mul_of_nonneg_left hscale (by linarith)
      _ = _ := by ring
  change ‖(multiplicity z : ℝ) * (b/(b^2+y^2))‖ ≤
    (2*k*(a+1/2)) * ((multiplicity z : ℝ)/(1+|y|)^2)
  rw [Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (hδ.le.trans hb) hD.le))]
  exact (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)).trans_eq (by ring)

/-- At every real abscissa right of one, subtracting the true critical-line count from
the scaled full Poisson mass gives a convergent sum over precisely the off-line sites. -/
theorem zeroPoissonMass_deficit_eq (χ : U𝔽) {a : ℝ} (ha : 1 / 2 < a) :
    a * zeroPoissonMass χ a - centralSoftCount χ a =
      ∑' z : Off(χ), (multiplicity z.val : ℝ) * (a * (a + 1 / 2 - z.val.val.re) /
        ((a + 1 / 2 - z.val.val.re) ^ 2 + z.val.val.im ^ 2)) :=
  deficit_eq_tsum (hasSum_scaledWeight (summable_unscaledWeight χ ha).hasSum)

/-- If the ordinate-zero Poisson sum equals a real mass eventually, its scaled deficit from
the actual central soft count tends to the entire off-line multiplicity, including infinity. -/
theorem tendsto_expanding_deficit (χ : U𝔽) (D : ℝ → ℝ)
    (hD : ∀ᶠ a in atTop, HasSum (fun z : Site χ ↦ (multiplicity z : ℝ) *
      ((a + 1 / 2 - z.val.re) / ((a + 1 / 2 - z.val.re) ^ 2 + z.val.im ^ 2))) (D a)) :
    Tendsto (fun a : ℝ ↦ ENNReal.ofReal (a * D a - centralSoftCount χ a)) atTop
      (𝓝 (offLineCount χ)) := by
  apply (tendsto_offLineSoftCount χ).congr'
  filter_upwards [eventually_gt_atTop (1 / 2 : ℝ), hD] with a ha hd
  exact (ofReal_deficit_eq ha hd).symm

/-- For the full zero mass the limiting multiplicity requires no identity with an arithmetic
logarithmic derivative. The known inverse-square height bound supplies summability. -/
theorem tendsto_zeroPoissonMass_deficit (χ : U𝔽) :
    Tendsto (fun a : ℝ ↦ ENNReal.ofReal (a * zeroPoissonMass χ a - centralSoftCount χ a))
      atTop (𝓝 (offLineCount χ)) :=
  tendsto_expanding_deficit χ _ <| (eventually_gt_atTop (1 / 2 : ℝ)).mono
    fun _ ha ↦ (summable_unscaledWeight χ ha).hasSum

private theorem offLineCount_eq_zero {χ : U𝔽} (h : ∀ z : Site χ, z.val.re = 1 / 2) :
    offLineCount χ = 0 := by
  have : IsEmpty Off(χ) := ⟨fun z ↦ z.property (h z.val)⟩
  exact tsum_empty

private theorem central_iff_frequently_deficit {χ : U𝔽} (d : ℝ → ℝ)
    (hd : Tendsto (fun a ↦ ENNReal.ofReal (d a)) atTop (𝓝 (offLineCount χ))) :
    (∀ z : Site χ, z.val.re = 1 / 2) ↔
      ∃ B : ℝ, B < 2 ∧ ∃ᶠ a in atTop, d a ≤ B := by
  constructor
  · intro h
    rw [offLineCount_eq_zero h] at hd
    have hr := hd.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
    refine ⟨1, by norm_num, (hr.mono fun a ha ↦ ?_).frequently⟩
    by_contra! hbig
    have hge : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (d a) := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hbig.le
    exact (not_lt_of_ge hge) ha
  · rintro ⟨B, hB, hfre⟩ z
    by_contra hz
    have hB' : ENNReal.ofReal B < offLineCount χ :=
      lt_of_lt_of_le (by simpa using (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<2)).2 hB)
        ((show (2 : ℝ≥0∞) ≤ 2 * (multiplicity z : ℝ≥0∞) by
          exact le_mul_of_one_le_right zero_le_two (by exact_mod_cast one_le_multiplicity z)).trans
          (two_mul_multiplicity_le_offLineCount z hz))
    have hev := hd.eventually (eventually_gt_nhds hB')
    obtain ⟨a, hda, hBa⟩ := (hfre.and_eventually hev).exists
    exact (not_lt_of_ge (ENNReal.ofReal_le_ofReal hda)) hBa

/-- For one character, the central-line assertion is equivalent to a fixed positive margin
below two along arbitrarily large real widths in its full zero mass. -/
theorem criticalLine_iff_cofinal_zeroPoissonMass (χ : U𝔽) :
    (∀ z : Site χ, z.val.re = 1 / 2) ↔ ∃ B : ℝ, B < 2 ∧
      ∃ᶠ a in atTop, a * zeroPoissonMass χ a - centralSoftCount χ a ≤ B :=
  central_iff_frequently_deficit _ (tendsto_zeroPoissonMass_deficit χ)

private theorem tendsto_ofReal_of_sub_tendsto {p q : ℝ → ℝ} {t : ℝ≥0∞}
    (hq : Tendsto (fun a ↦ ENNReal.ofReal (q a)) atTop (𝓝 t))
    (h : Tendsto (fun a ↦ p a - q a) atTop (𝓝 0)) :
    Tendsto (fun a ↦ ENNReal.ofReal (p a)) atTop (𝓝 t) := by
  let e := fun a ↦ ENNReal.ofReal |p a - q a|
  have he : Tendsto e atTop (𝓝 0) := by simpa [e] using ENNReal.tendsto_ofReal h.abs
  have hu (x y : ℝ) : ENNReal.ofReal x ≤ ENNReal.ofReal y + ENNReal.ofReal |x - y| :=
    (ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (x-y)] : x ≤ y + |x-y|)).trans
      ENNReal.ofReal_add_le
  have hlo := ENNReal.Tendsto.sub hq he (Or.inr ENNReal.zero_ne_top)
  have hhi := hq.add he
  rw [tsub_zero] at hlo
  rw [add_zero] at hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
  · intro a
    apply tsub_le_iff_right.mpr
    simpa only [e, abs_sub_comm (p a) (q a)] using hu (q a) (p a)
  · exact fun a ↦ hu (p a) (q a)

/-- An additive error tending to zero preserves the recovered off-line multiplicity even when
that multiplicity is infinite. -/
theorem tendsto_approximate_deficit (χ : U𝔽) (M : ℝ → ℝ)
    (hM : Tendsto (fun a ↦ M a - a * zeroPoissonMass χ a) atTop (𝓝 0)) :
    Tendsto (fun a ↦ ENNReal.ofReal (M a - centralSoftCount χ a))
      atTop (𝓝 (offLineCount χ)) := by
  apply tendsto_ofReal_of_sub_tendsto (tendsto_zeroPoissonMass_deficit χ)
  simpa only [sub_sub_sub_cancel_right] using hM

/-- Any approximation to the scaled complete Poisson mass with error tending to zero gives
the same fixed-gap, cofinal criterion. -/
theorem criticalLine_iff_cofinal_approximation (χ : U𝔽) (M : ℝ → ℝ)
    (hM : Tendsto (fun a ↦ M a - a * zeroPoissonMass χ a) atTop (𝓝 0)) :
    (∀ z : Site χ, z.val.re = 1 / 2) ↔ ∃ B : ℝ, B < 2 ∧
      ∃ᶠ a in atTop, M a - centralSoftCount χ a ≤ B := by
  exact central_iff_frequently_deficit _ (tendsto_approximate_deficit χ M hM)

open MeasureTheory
open scoped NNReal NumberField.AdeleRing

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Ext(" τ ", " α ")" =>
  {p : {χ : U𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
    0 < ord(p.1.val, p.2) ∧ α ≤ |p.2.re - 1 / 2|}
local notation "Cancellation(" τ ")" =>
  ∀ α : ℝ, 0 < α → ∀ φ : BruhatCompactSupport C𝔽,
    (∀ g : (ideleClassNorm F).ker, φ.val g = 0) →
    HasSum (fun p : Ext(τ, α) ↦ (ord(p.val.1.val, p.val.2) : ℂ) *
      ∫ g, φ.val g * ideleClassNormTwist p.val.1.val (p.val.2 - 1 / 2) g
        ∂ideleClassTamagawaMeasure F) 0

private theorem exteriorCancellation_iff_normalized_central
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : Function.RightInverse τ (ideleClassNorm F)) :
    Cancellation(τ) ↔ ∀ χ : U𝔽, (∀ t, χ (τ t) = 1) → ∀ z : Site χ, z.val.re = 1 / 2 := by
  have hsplit (a : ℝ) :
      (∀ φ : BruhatCompactSupport C𝔽, (∀ g : (ideleClassNorm F).ker, φ.val g = 0) →
        HasSum (fun p : Ext(τ, a) ↦ (ord(p.val.1.val, p.val.2) : ℂ) *
          ∫ g, φ.val g * ideleClassNormTwist p.val.1.val (p.val.2 - 1 / 2) g
            ∂ideleClassTamagawaMeasure F) 0) ↔ IsEmpty Ext(τ, a) := by
    simpa only [modulatedFourierMellin, relativeVerticalStrip, Set.preimage_univ,
      Set.indicator_univ] using hasSum_exteriorZeros_iff_isEmpty τ hτ a
  constructor
  · intro h χ hχ z
    by_contra hz
    have hα := abs_pos.mpr (sub_ne_zero.mpr hz)
    exact ((hsplit _).mp (h _ hα)).false ⟨(⟨χ, hχ⟩, z.val), z.property, le_rfl⟩
  · intro h α hα
    apply (hsplit α).mpr
    refine ⟨fun z ↦ ?_⟩
    have he := h z.val.1.val z.val.1.property ⟨z.val.2, z.property.1⟩
    have hle := z.property.2
    change z.val.2.re = 1 / 2 at he
    rw [he, sub_self, abs_zero] at hle
    exact (not_le_of_gt hα) hle

/-- Paper: Theorem 12.5.1.1, pp. 519–520. Any additive approximation to each scaled
complete mass with error tending to zero gives an equivalent statement of exterior-zero
cancellation for every positive strip width. Both the margin below two and the cofinal
widths may depend on the section-normalized character. -/
theorem exteriorCancellation_iff_cofinal_approximation
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : Function.RightInverse τ (ideleClassNorm F)) (M : U𝔽 → ℝ → ℝ)
    (hM : ∀ χ : U𝔽, (∀ t, χ (τ t) = 1) →
      Tendsto (fun a ↦ M χ a - a * zeroPoissonMass χ a) atTop (𝓝 0)) :
    Cancellation(τ) ↔ ∀ χ : U𝔽, (∀ t, χ (τ t) = 1) → ∃ B : ℝ, B < 2 ∧
      ∃ᶠ a in atTop, M χ a - centralSoftCount χ a ≤ B := by
  rw [exteriorCancellation_iff_normalized_central τ hτ]
  exact forall_congr' fun χ ↦ forall_congr' fun hχ ↦ criticalLine_iff_cofinal_approximation χ _ (hM χ hχ)

/-- Paper: Theorem 12.5.1.1, pp. 519–520. For all positive strip half-widths, the omitted
zero sums cancel for every test exactly when each section-normalized character has arbitrarily
large real widths with its scaled zero-mass deficit bounded by a fixed number below two. -/
theorem exteriorCancellation_iff_cofinal_zeroPoissonMass
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : Function.RightInverse τ (ideleClassNorm F)) :
    Cancellation(τ) ↔ ∀ χ : U𝔽, (∀ t, χ (τ t) = 1) → ∃ B : ℝ, B < 2 ∧
      ∃ᶠ a in atTop, a * zeroPoissonMass χ a - centralSoftCount χ a ≤ B := by
  rw [exteriorCancellation_iff_normalized_central τ hτ]
  exact forall_congr' fun χ ↦ forall_congr' fun _ ↦ criticalLine_iff_cofinal_zeroPoissonMass χ

end RiemannMasullo.HeckePoisson
