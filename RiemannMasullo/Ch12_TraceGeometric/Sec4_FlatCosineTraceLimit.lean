module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatCosineTrace
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Trigonometric.SincIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Removing the two cutoffs for a single nonidentity dilation

Reconstruction: Theorem 12.4.1.1, Step II, in the unpolarized rational
real-even model. The cutoff estimate uses thierryaaron's sine-integral bound from
#7602. The dilation is normalized by `D_a f(t) = √a f(at)`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

namespace RiemannMasullo.FlatPolar

/-- One of the two frequencies arising from the cosine product. -/
private def cosineAtom (h L B k : ℝ) :=
  B * ∫ x in h..L, sinc ((k * B) * x)

private theorem integral_cos_scale_band {B : ℝ} (hB : 0 < B) (c : ℝ) :
    (∫ s in Ioc (0 : ℝ) B, cos (c * s)) = B * sinc (c * B) := by
  rw [← intervalIntegral.integral_of_le hB.le]
  by_cases hc : c = 0
  · simp [hc]
  have h := intervalIntegral.mul_integral_comp_mul_left (a := 0) (b := B) (f := cos) c
  rw [mul_zero, integral_cos, sin_zero, sub_zero] at h
  rw [sinc_of_ne_zero (mul_ne_zero hc hB.ne')]
  apply mul_left_cancel₀ hc
  rw [h]
  field_simp

private theorem cos_abs_mul (u v : ℝ) : cos (|u| * v) = cos (u * v) := by
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_neg hu, neg_mul, cos_neg]

private theorem integral_cos_mul_cos_band {B : ℝ} (hB : 0 < B) (a x : ℝ) :
    (∫ s in Ioc (0 : ℝ) B, cos (2 * π * (x * s)) * cos (2 * π * (x * s / a))) =
      (B * sinc (((2 * π * |1 - a⁻¹|) * B) * x) +
        B * sinc (((2 * π * (1 + a⁻¹)) * B) * x)) / 2 := by
  let k := 2 * π * |1 - a⁻¹|
  let m := 2 * π * (1 + a⁻¹)
  have hp (s : ℝ) : cos (2 * π * (x * s)) * cos (2 * π * (x * s / a)) =
      (cos ((k * x) * s) + cos ((m * x) * s)) / 2 := by
    have hm : cos ((k * x) * s) = cos (2 * π * (x * s) - 2 * π * (x * s / a)) := by
      rw [show (k * x) * s = |1 - a⁻¹| * (2 * π * (x * s)) by dsimp [k]; ring, cos_abs_mul]
      congr 1
      ring
    have hq : (m * x) * s = 2 * π * (x * s) + 2 * π * (x * s / a) := by
      dsimp [m]; ring
    rw [hm, hq, ← two_mul_cos_mul_cos]
    ring
  have hi (d : ℝ) : IntegrableOn (fun s : ℝ ↦ cos ((d * x) * s)) (Ioc 0 B) :=
    ((by fun_prop : Continuous (fun s : ℝ ↦ cos ((d * x) * s))).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  simp_rw [hp]
  rw [integral_div, integral_add (hi k) (hi m), integral_cos_scale_band hB, integral_cos_scale_band hB]
  simp only [show (k * x) * B = (k * B) * x by ring, show (m * x) * B = (m * B) * x by ring, k, m]

private theorem cosineAtom_error {h L B k : ℝ} (hh : 0 ≤ h) (hL : 0 < L) (hB : 0 < B)
    (hk : 0 < k) :
    |cosineAtom h L B k - π / (2 * k)| ≤ B * h + 2 / (k ^ 2 * (B * L)) := by
  let c := k * B
  have hc : 0 < c := mul_pos hk hB
  have hs := intervalIntegral.mul_integral_comp_mul_left (a := h) (b := L) (f := sinc) c
  have hrep : cosineAtom h L B k = (∫ t in c*h..c*L, sinc t) / k := by
    apply (eq_div_iff hk.ne').2
    simpa only [cosineAtom, c, mul_comm _ k, ← mul_assoc] using hs
  have hl := abs_integral_sinc_sub_le (mul_pos hc hL)
  have hb : |∫ t in (0 : ℝ)..c*h, sinc t| ≤ c*h := by
    simpa only [Real.norm_eq_abs, sub_zero, one_mul, abs_of_nonneg (mul_nonneg hc.le hh)] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := c*h) (C := 1) (f := sinc)
        (fun t _ ↦ by simpa only [Real.norm_eq_abs] using abs_sinc_le_one t))
  have he := intervalIntegral.integral_add_adjacent_intervals
    (continuous_sinc.intervalIntegrable (μ := volume) 0 (c*h))
    (continuous_sinc.intervalIntegrable (μ := volume) (c*h) (c*L))
  have he' : |(∫ t in c*h..c*L, sinc t) - π / 2| ≤ 2 / (c*L) + c*h := by
    rw [show (∫ t in c*h..c*L, sinc t) - π/2 =
      ((∫ t in (0 : ℝ)..c*L, sinc t) - π/2) + -(∫ t in (0 : ℝ)..c*h, sinc t) by linarith [he]]
    exact (abs_add_le _ _).trans (add_le_add hl (by simpa only [abs_neg] using hb))
  rw [hrep, show π / (2*k) = (π/2)/k by ring, ← sub_div, abs_div, abs_of_pos hk]
  refine (div_le_div_of_nonneg_right he' hk.le).trans_eq ?_
  dsimp [c]
  field_simp
  ring


private theorem hilbertTrace_frequencyBand_eq_atoms {h L B a : ℝ} (hh : 0 ≤ h)
    (hL : h ≤ L) (hB : 0 < B) :
    hilbertTrace (finiteCosineTraceOperator 0 B h L a) =
      (((2 / sqrt a) * (cosineAtom h L B (2 * π * |1 - a⁻¹|) +
        cosineAtom h L B (2 * π * (1 + a⁻¹))) : ℝ) : ℂ) := by
  rw [hilbertTrace_finiteCosine_frequencyBand _ _ _ _ hh]
  apply congrArg Complex.ofReal
  simp_rw [integral_cos_mul_cos_band hB]
  rw [← intervalIntegral.integral_of_le hL, intervalIntegral.integral_div,
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [intervalIntegral.integral_const_mul, cosineAtom]
  ring

/-- The full real-even orbital value of a single nonidentity positive dilation. -/
def finiteCosineDilationValue (a : ℝ) :=
  (1 / (2 * sqrt a)) * (|1 - a⁻¹|⁻¹ + (1 + a⁻¹)⁻¹)

/-- The finite-band trace remainder is uniform when `a` stays bounded below and
`|1−a⁻¹|` stays bounded away from zero. Both band errors are explicit.

Reconstruction: apply the finite real-even trace formula to the two sine integrals
associated to the dilation and its reflection. -/
theorem norm_hilbertTrace_frequencyBand_sub_le {h L B a : ℝ}
    (ha : 0 < a) (ha₁ : a ≠ 1) (hh : 0 ≤ h) (hL : 0 < L) (hhL : h ≤ L) (hB : 0 < B) :
    ‖hilbertTrace (finiteCosineTraceOperator 0 B h L a) - (finiteCosineDilationValue a : ℂ)‖ ≤
      4 / sqrt a * (B * h + (((2 * π * |1 - a⁻¹|)^2)⁻¹ +
        ((2 * π * (1 + a⁻¹))^2)⁻¹) / (B * L)) := by
  let k := 2 * π * |1 - a⁻¹|
  let m := 2 * π * (1 + a⁻¹)
  have hd : 1 - a⁻¹ ≠ 0 := by
    intro he
    apply ha₁
    have hi : a⁻¹ = 1 := by linarith
    simpa using congrArg Inv.inv hi
  have he : 0 < 1 + a⁻¹ := by positivity
  have hk : 0 < k := mul_pos (by positivity) (abs_pos.mpr hd)
  have hm : 0 < m := mul_pos (by positivity) he
  have scale (q : ℝ) (hq : q ≠ 0) : π / (2 * (2 * π * q)) = (1 / 4) * q⁻¹ := by
    field_simp [Real.pi_ne_zero, hq]
    ring
  have hv : finiteCosineDilationValue a = 2 / sqrt a * (π / (2*k) + π / (2*m)) := by
    dsimp only [k, m, finiteCosineDilationValue]
    rw [scale _ (abs_ne_zero.mpr hd), scale _ he.ne']
    ring
  rw [hilbertTrace_frequencyBand_eq_atoms hh hhL hB, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, hv]
  change |2 / sqrt a * (cosineAtom h L B k + cosineAtom h L B m) -
      2 / sqrt a * (π / (2*k) + π / (2*m))| ≤ _
  rw [← mul_sub, show cosineAtom h L B k + cosineAtom h L B m - (π/(2*k) + π/(2*m)) =
    (cosineAtom h L B k - π/(2*k)) + (cosineAtom h L B m - π/(2*m)) by ring, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 2 / sqrt a)]
  refine (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add (cosineAtom_error hh hL hB hk)
    (cosineAtom_error hh hL hB hm))) (by positivity)).trans_eq ?_
  change 2 / sqrt a * ((B*h + 2/(k^2*(B*L))) + (B*h + 2/(m^2*(B*L)))) =
    4 / sqrt a * (B*h + ((k^2)⁻¹ + (m^2)⁻¹) / (B*L))
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring


/-- A single constant controls every dilation in a compact subset of the positive
nonidentity parameters. -/
theorem exists_hilbertTrace_frequencyBand_error_const {K : Set ℝ} (hK : IsCompact K)
    (hpar : ∀ a ∈ K, 0 < a ∧ a ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ K, ∀ {h L B : ℝ}, 0 ≤ h → 0 < L → h ≤ L → 0 < B →
      ‖hilbertTrace (finiteCosineTraceOperator 0 B h L a) - (finiteCosineDilationValue a : ℂ)‖ ≤
        C * (B * h + (B * L)⁻¹) := by
  let U (a : ℝ) := 4 / sqrt a
  let V (a : ℝ) := U a * ((((2 * π * |1 - a⁻¹|)^2)⁻¹) + (((2 * π * (1 + a⁻¹))^2)⁻¹))
  have hu : ContinuousOn U K := by
    intro a hak
    have ha := (hpar a hak).1
    exact (show ContinuousAt U a by dsimp [U]; fun_prop (disch := positivity)).continuousWithinAt
  have hv : ContinuousOn V K := by
    intro a hak
    obtain ⟨ha, ha₁⟩ := hpar a hak
    have hd : 1 - a⁻¹ ≠ 0 := by
      intro he; apply ha₁
      have hi : a⁻¹ = 1 := by linarith
      simpa using congrArg Inv.inv hi
    exact (show ContinuousAt V a by dsimp [V, U]; fun_prop (disch := positivity)).continuousWithinAt
  obtain ⟨u, hu'⟩ := hK.bddAbove_image hu
  obtain ⟨v, hv'⟩ := hK.bddAbove_image hv
  let C := max 0 (max u v)
  refine ⟨C, le_max_left _ _, ?_⟩
  intro a hak h L B hh hL hhL hB
  have hUc : U a ≤ C :=
    (hu' (mem_image_of_mem U hak)).trans ((le_max_left u v).trans (le_max_right _ _))
  have hVc : V a ≤ C :=
    (hv' (mem_image_of_mem V hak)).trans ((le_max_right u v).trans (le_max_right _ _))
  refine (norm_hilbertTrace_frequencyBand_sub_le (hpar a hak).1 (hpar a hak).2 hh hL hhL hB).trans ?_
  calc
    _ = U a * (B*h) + V a * (B*L)⁻¹ := by dsimp [V, U]; ring
    _ ≤ C * (B*h) + C * (B*L)⁻¹ := add_le_add (mul_le_mul_of_nonneg_right hUc (by positivity))
        (mul_le_mul_of_nonneg_right hVc (by positivity))
    _ = _ := by ring

/-- Removing the two cutoffs converges uniformly for positive dilations in any compact
set avoiding the identity. Only the products `Bh` and `BL` enter.

Reconstruction: removal of the sharp upper cutoffs in the rational real-even
local calculation of Theorem 12.4.1.1, pp. 516–517. -/
theorem tendstoUniformlyOn_hilbertTrace_finiteCosine_frequencyBand {ι : Type*} {l : Filter ι}
    {h L B : ι → ℝ} {K : Set ℝ} (hK : IsCompact K) (hpar : ∀ a ∈ K, 0 < a ∧ a ≠ 1)
    (hbox : ∀ᶠ i in l, 0 ≤ h i ∧ 0 < B i)
    (hBh : Tendsto (fun i ↦ B i * h i) l (𝓝 0))
    (hBL : Tendsto (fun i ↦ B i * L i) l atTop) :
    TendstoUniformlyOn (fun i a ↦ hilbertTrace (finiteCosineTraceOperator 0 (B i) (h i) (L i) a))
      (fun a ↦ (finiteCosineDilationValue a : ℂ)) l K := by
  obtain ⟨C, -, hC⟩ := exists_hilbertTrace_frequencyBand_error_const hK hpar
  have hlim : Tendsto (fun i ↦ C * (B i * h i + (B i * L i)⁻¹)) l (𝓝 0) := by
    simpa using (hBh.add (tendsto_inv_atTop_zero.comp hBL)).const_mul C
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hbox, hBh.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    hBL.eventually_gt_atTop 1, hlim.eventually (gt_mem_nhds hε)] with i hi hb₁ hb₂ hiε
  intro a hak
  have hL : 0 < L i := pos_of_mul_pos_right (by linarith : 0 < B i * L i) hi.2.le
  have hhL : h i ≤ L i := (lt_of_mul_lt_mul_left (hb₁.trans hb₂) hi.2.le).le
  rw [dist_comm, dist_eq_norm]
  exact (hC a hak hi.1 hL hhL hi.2).trans_lt hiε

/-- The corresponding pointwise limit holds at every positive dilation except one. -/
theorem tendsto_hilbertTrace_finiteCosine_frequencyBand {ι : Type*} {l : Filter ι}
    {h L B : ι → ℝ} {a : ℝ} (ha : 0 < a) (ha₁ : a ≠ 1)
    (hbox : ∀ᶠ i in l, 0 ≤ h i ∧ 0 < B i)
    (hBh : Tendsto (fun i ↦ B i * h i) l (𝓝 0))
    (hBL : Tendsto (fun i ↦ B i * L i) l atTop) :
    Tendsto (fun i ↦ hilbertTrace (finiteCosineTraceOperator 0 (B i) (h i) (L i) a))
      l (𝓝 (finiteCosineDilationValue a : ℂ)) := by
  exact (tendstoUniformlyOn_hilbertTrace_finiteCosine_frequencyBand (K := {a}) isCompact_singleton
    (by intro b hb; obtain rfl := Set.mem_singleton_iff.mp hb; exact ⟨ha, ha₁⟩) hbox hBh hBL
    ).tendsto_at (mem_singleton a)


/-- On the expanding-dilation side the real-even orbital value is `a√a/(a²−1)`. -/
theorem finiteCosineDilationValue_of_one_lt {a : ℝ} (ha : 1 < a) :
    finiteCosineDilationValue a = a * sqrt a / (a^2 - 1) := by
  have ha₀ : 0 < a := zero_lt_one.trans ha
  have hs : 0 < sqrt a := sqrt_pos.mpr ha₀
  have hn : 0 < 1 - a⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ ha)
  have hplus : 0 < a + 1 := by positivity
  have hminus : 0 < a - 1 := by linarith
  have hprod : a^2 - 1 ≠ 0 := by nlinarith [mul_pos hminus hplus]
  have hroot : 1 / sqrt a = sqrt a / a := by
    field_simp [hs.ne', ha₀.ne']
    exact (sq_sqrt ha₀.le).symm
  have hn₁ : 1 - a⁻¹ = (a - 1)/a := by field_simp
  have hn₂ : 1 + a⁻¹ = (a + 1)/a := by field_simp
  rw [finiteCosineDilationValue, abs_of_pos hn, hn₁, hn₂, inv_div, inv_div,
    show 1 / (2 * sqrt a) = (1 / 2) * (1 / sqrt a) by ring, hroot]
  field_simp [ha₀.ne', hminus.ne', hplus.ne', hprod]
  ring

/-- On the contracting-dilation side the real-even orbital value is `√a/(1−a²)`. -/
theorem finiteCosineDilationValue_of_lt_one {a : ℝ} (ha₀ : 0 < a) (ha : a < 1) :
    finiteCosineDilationValue a = sqrt a / (1 - a^2) := by
  have hs : 0 < sqrt a := sqrt_pos.mpr ha₀
  have hneg : 1 - a⁻¹ < 0 := sub_neg.mpr ((one_lt_inv₀ ha₀).2 ha)
  have hplus : 0 < 1 + a := by positivity
  have hminus : 0 < 1 - a := sub_pos.mpr ha
  have hprod : 1 - a^2 ≠ 0 := by nlinarith [mul_pos hminus hplus]
  have hroot : 1 / sqrt a = sqrt a / a := by
    field_simp [hs.ne', ha₀.ne']
    exact (sq_sqrt ha₀.le).symm
  have hn₁ : -(1 - a⁻¹) = (1 - a)/a := by
    field_simp
    ring
  have hn₂ : 1 + a⁻¹ = (1 + a)/a := by
    field_simp
    ring
  rw [finiteCosineDilationValue, abs_of_neg hneg, hn₁, hn₂, inv_div, inv_div,
    show 1 / (2 * sqrt a) = (1 / 2) * (1 / sqrt a) by ring, hroot]
  field_simp [ha₀.ne', hminus.ne', hplus.ne', hprod]
  ring

end RiemannMasullo.FlatPolar
