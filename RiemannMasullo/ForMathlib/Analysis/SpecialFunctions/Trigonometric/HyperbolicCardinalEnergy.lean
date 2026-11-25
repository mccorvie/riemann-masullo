module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.CausalEvaluation
public import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Trigonometric.HyperbolicCardinal
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Whole-line energy of a hyperbolic cardinal

The cardinal centered at `z` has one side for each neighbouring site. A finite side
uses the hyperbolic sine profile up to that neighbour and vanishes beyond it. A side
without a neighbour is the decaying exponential.

For a bounded continuously differentiable multiplier `b` with bounded derivative
and `b z = 0`, let `p = h • b`. The ordinary complex L² representative `p + deriv p`
has squared norm exactly `∫ t, ‖deriv b t‖ ^ 2 * h t ^ 2`. The scalar flux is continuous
at every join and tends to zero at both infinities.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval InnerProductSpace

namespace RiemannMasullo.LineGeometricFourier

/-- The causal first-order representative of a multiplier times a real cardinal profile. -/
def cardinalCausal (b : ℝ → ℂ) (h : ℝ → ℝ) (x : ℝ) : ℂ :=
  h x • b x + deriv (fun t ↦ h t • b t) x

/-- Adding the derivative of the squared residual to the hyperbolic flux gives
the exact norm of the first-order causal representative. -/
def cardinalFlux (b : ℝ → ℂ) (h q : ℝ → ℝ) (x : ℝ) : ℝ :=
  ‖b x‖ ^ 2 * h x * q x + ‖h x • b x‖ ^ 2

private theorem hasDerivAt_cardinalFlux {b : ℝ → ℂ} {h q : ℝ → ℝ} {x : ℝ}
    (hb : HasDerivAt b (deriv b x) x) (hh : HasDerivAt h (q x) x) (hq : HasDerivAt q (h x) x) :
    HasDerivAt (cardinalFlux b h q)
      (‖cardinalCausal b h x‖ ^ 2 - ‖deriv b x‖ ^ 2 * h x ^ 2) x := by
  let p := fun t ↦ h t • b t
  have hp : HasDerivAt p (deriv p x) x := (hh.smul hb).differentiableAt.hasDerivAt
  have hf := (GeometricHat.energy_flux_derivative hb hh hq).add hp.norm_sq
  change HasDerivAt (cardinalFlux b h q) _ x at hf
  convert hf using 1
  rw [cardinalCausal, norm_add_sq_real]
  dsimp only [p]
  ring

/-- The actual scalar calculation on the whole line. A real cardinal satisfies
`h''=h` away from its at most three junctions. Vanishing of the multiplier at the
central site and of the profile at each finite adjacent site makes this flux continuous.
The explicit endpoint flux hypotheses also allow exterior half-lines. -/
theorem whole_line_cardinal_energy (b : ℝ → ℂ) (h q : ℝ → ℝ) (s : Finset ℝ)
    (hb : Differentiable ℝ b)
    (hh : ∀ x ∉ s, HasDerivAt h (q x) x) (hq : ∀ x ∉ s, HasDerivAt q (h x) x)
    (cf : Continuous (cardinalFlux b h q))
    (bot : Tendsto (cardinalFlux b h q) atBot (𝓝 0))
    (top : Tendsto (cardinalFlux b h q) atTop (𝓝 0))
    (eg : Integrable fun x ↦ ‖cardinalCausal b h x‖ ^ 2)
    (ew : Integrable fun x ↦ ‖deriv b x‖ ^ 2 * h x ^ 2) :
    (∫ x, ‖cardinalCausal b h x‖ ^ 2) = ∫ x, ‖deriv b x‖ ^ 2 * h x ^ 2 := by
  let y := fun x ↦ ‖cardinalCausal b h x‖ ^ 2 - ‖deriv b x‖ ^ 2 * h x ^ 2
  let f := cardinalFlux b h q
  have hy : Integrable y := eg.sub ew
  have hd (x : ℝ) (hx : x ∉ s) : HasDerivAt f (y x) x :=
    hasDerivAt_cardinalFlux (hb x).hasDerivAt (hh x hx) (hq x hx)
  have he : (fun r : ℝ ↦ ∫ x in -r..r, y x) =ᶠ[atTop] fun r ↦ f r - f (-r) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    exact integral_sub_of_finite_joins f y s cf (by linarith) hy.intervalIntegrable (fun x _ ↦ hd x)
  have ht := tendsto_nhds_unique (intervalIntegral_tendsto_integral hy tendsto_neg_atTop_atBot tendsto_id)
    ((top.sub (bot.comp tendsto_neg_atTop_atBot)).congr' he.symm)
  change (∫ x, ‖cardinalCausal b h x‖ ^ 2 - ‖deriv b x‖ ^ 2 * h x ^ 2) = _ at ht
  rw [integral_sub eg ew, sub_zero] at ht
  exact sub_eq_zero.mp ht

/-- The hat on one side, in the distance coordinate. -/
def hatSide (gap : Option (Ioi (0 : ℝ))) (r : ℝ) : ℝ :=
  match gap with
  | none => Real.exp (-r)
  | some d => if r ≤ d.1 then GeometricHat.profile d.1 r else 0

private def sideSlope (gap : Option (Ioi (0 : ℝ))) (r : ℝ) : ℝ :=
  match gap with
  | none => -Real.exp (-r)
  | some d => if r ≤ d.1 then deriv (GeometricHat.profile d.1) r else 0

/-- Distance of the optional endpoint, using zero for the center when absent. -/
def endpointDistance (gap : Option (Ioi (0 : ℝ))) : ℝ :=
  gap.elim 0 Subtype.val

/-- Real cardinal, obtained by reflecting the left distance coordinate. -/
def twoSidedHat (z : ℝ) (left right : Option (Ioi (0 : ℝ))) (t : ℝ) : ℝ :=
  if t ≤ z then hatSide left (z - t) else hatSide right (t - z)

private def hatSlope (z : ℝ) (left right : Option (Ioi (0 : ℝ))) (t : ℝ) : ℝ :=
  if t ≤ z then -sideSlope left (z - t) else sideSlope right (t - z)

/-- The center and the two optional endpoints. An absent endpoint repeats the center. -/
def hatJoins (z : ℝ) (left right : Option (Ioi (0 : ℝ))) : Finset ℝ :=
  {z, z - endpointDistance left, z + endpointDistance right}

/-- The center and two optional endpoints give at most three joins. -/
theorem hatJoins_card_le (z : ℝ) (left right : Option (Ioi (0 : ℝ))) :
    (hatJoins z left right).card ≤ 3 := by
  unfold hatJoins
  grw [Finset.card_insert_le, Finset.card_insert_le]
  simp

/-- Each side takes the value one at the central site. -/
@[simp] theorem hatSide_zero (gap : Option (Ioi (0 : ℝ))) : hatSide gap 0 = 1 := by
  cases gap with
  | none => simp [hatSide]
  | some d =>
    have hd : 0 < d.1 := d.2
    simp [hatSide, hd.le, GeometricHat.profile, (Real.sinh_pos_iff.mpr hd).ne']

/-- The left half of the cardinal in its distance coordinate. -/
theorem twoSidedHat_left (z : ℝ) (left right : Option (Ioi (0 : ℝ))) {r : ℝ} (hr : 0 ≤ r) :
    twoSidedHat z left right (z - r) = hatSide left r := by
  simp [twoSidedHat, sub_le_self z hr]

/-- The right half of the cardinal in its distance coordinate. -/
theorem twoSidedHat_right (z : ℝ) (left right : Option (Ioi (0 : ℝ))) {r : ℝ} (hr : 0 ≤ r) :
    twoSidedHat z left right (z + r) = hatSide right r := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [twoSidedHat]
  · simp [twoSidedHat, not_le.mpr (lt_add_of_pos_right z hr)]

/-- A description by the two side formulas uniquely determines the glued profile. -/
theorem eq_twoSidedHat_of_sides {h : ℝ → ℝ} (z : ℝ) (left right : Option (Ioi (0 : ℝ)))
    (hl : ∀ r : ℝ, 0 ≤ r → h (z - r) = hatSide left r)
    (hr : ∀ r : ℝ, 0 ≤ r → h (z + r) = hatSide right r) :
    h = twoSidedHat z left right := by
  funext t
  by_cases ht : t ≤ z
  · have hdist := sub_nonneg.mpr ht
    simpa using (hl (z - t) hdist).trans (twoSidedHat_left z left right hdist).symm
  · have hdist := sub_nonneg.mpr (le_of_not_ge ht)
    simpa using (hr (t - z) hdist).trans (twoSidedHat_right z left right hdist).symm

private theorem continuous_hatSide (gap : Option (Ioi (0 : ℝ))) : Continuous (hatSide gap) := by
  cases gap with
  | none => unfold hatSide; fun_prop
  | some d =>
    have hp : Continuous (GeometricHat.profile d.1) := continuous_iff_continuousAt.mpr fun r ↦
      (GeometricHat.hasDerivAt_profile d.1 r).continuousAt
    exact hp.if_le continuous_const continuous_id continuous_const
      (fun x hx ↦ by simp only [hx, GeometricHat.profile, sub_self, Real.sinh_zero, zero_div])

private theorem continuous_side_flux (gap : Option (Ioi (0 : ℝ))) :
    Continuous (fun r ↦ hatSide gap r * sideSlope gap r) := by
  cases gap with
  | none => dsimp [hatSide, sideSlope]; fun_prop
  | some d =>
    have hp : Continuous (GeometricHat.profile d.1) := continuous_iff_continuousAt.mpr fun r ↦
      (GeometricHat.hasDerivAt_profile d.1 r).continuousAt
    have hq : Continuous (deriv (GeometricHat.profile d.1)) := continuous_iff_continuousAt.mpr fun r ↦
      (GeometricHat.hasDerivAt_deriv_profile d.1 r).continuousAt
    have e : (fun r ↦ hatSide (some d) r * sideSlope (some d) r) =
        fun r ↦ if r ≤ d.1 then GeometricHat.profile d.1 r * deriv (GeometricHat.profile d.1) r
                                  else 0 := by
      funext r
      by_cases hr : r ≤ d.1 <;> simp [hatSide, sideSlope, hr]
    rw [e]
    exact (hp.mul hq).if_le continuous_const continuous_id continuous_const
      (fun x hx ↦ by simp [hx, GeometricHat.profile])

/-- The two sides glue continuously at the site and at each finite endpoint. -/
theorem continuous_twoSidedHat (z : ℝ) (left right : Option (Ioi (0 : ℝ))) :
    Continuous (twoSidedHat z left right) := by
  apply ((continuous_hatSide left).comp (continuous_const.sub continuous_id)).if_le
    ((continuous_hatSide right).comp (continuous_id.sub continuous_const)) continuous_id continuous_const
  intro t (ht : t = z)
  simp [ht]

private theorem side_regular (gap : Option (Ioi (0 : ℝ))) {r : ℝ} (hr : r ≠ endpointDistance gap) :
    HasDerivAt (hatSide gap) (sideSlope gap r) r ∧
      HasDerivAt (sideSlope gap) (hatSide gap r) r := by
  cases gap with
  | none =>
    have h := (hasDerivAt_neg r).exp
    change HasDerivAt (fun t : ℝ ↦ Real.exp (-t)) (-Real.exp (-r)) r ∧
      HasDerivAt (fun t : ℝ ↦ -Real.exp (-t)) (Real.exp (-r)) r
    exact ⟨by simpa using h, by simpa using! h.neg⟩
  | some d =>
    change r ≠ d.1 at hr
    rcases lt_or_gt_of_ne hr with h | h
    · have eh : hatSide (some d) =ᶠ[𝓝 r] GeometricHat.profile d.1 := by
        filter_upwards [gt_mem_nhds h] with y hy using ite_eq_left (le_of_lt hy)
      have eq : sideSlope (some d) =ᶠ[𝓝 r] deriv (GeometricHat.profile d.1) := by
        filter_upwards [gt_mem_nhds h] with y hy using ite_eq_left (le_of_lt hy)
      exact ⟨by simpa [sideSlope, h.le] using
          ((GeometricHat.hasDerivAt_profile d.1 r).differentiableAt.hasDerivAt.congr_of_eventuallyEq eh),
        by simpa [hatSide, h.le] using
          ((GeometricHat.hasDerivAt_deriv_profile d.1 r).congr_of_eventuallyEq eq)⟩
    · have eh : hatSide (some d) =ᶠ[𝓝 r] fun _ ↦ 0 := by
        filter_upwards [lt_mem_nhds h] with y hy using ite_eq_right (not_le.mpr hy)
      have eq : sideSlope (some d) =ᶠ[𝓝 r] fun _ ↦ 0 := by
        filter_upwards [lt_mem_nhds h] with y hy using ite_eq_right (not_le.mpr hy)
      exact ⟨by simpa [sideSlope, not_le.mpr h] using
          (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq eh,
        by simpa [hatSide, not_le.mpr h] using
          (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq eq⟩

private theorem hat_regular (z : ℝ) (left right : Option (Ioi (0 : ℝ))) {x : ℝ}
    (hx : x ∉ hatJoins z left right) :
    HasDerivAt (twoSidedHat z left right) (hatSlope z left right x) x ∧
      HasDerivAt (hatSlope z left right) (twoSidedHat z left right x) x := by
  simp only [hatJoins, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  rcases lt_or_gt_of_ne hx.1 with h | h
  · have rne : z - x ≠ endpointDistance left := fun he ↦ hx.2.1 (by linarith)
    obtain ⟨hv, hq⟩ := side_regular left rne
    have eh : twoSidedHat z left right =ᶠ[𝓝 x] fun t ↦ hatSide left (z - t) := by
      filter_upwards [gt_mem_nhds h] with t ht using ite_eq_left (le_of_lt ht)
    have eq : hatSlope z left right =ᶠ[𝓝 x] fun t ↦ -sideSlope left (z - t) := by
      filter_upwards [gt_mem_nhds h] with t ht using ite_eq_left (le_of_lt ht)
    have id' := (hasDerivAt_id x).const_sub z
    exact ⟨by simpa [hatSlope, h.le] using (hv.comp x id').congr_of_eventuallyEq eh,
      by simpa [twoSidedHat, h.le] using (hq.comp x id').neg.congr_of_eventuallyEq eq⟩
  · have rne : x - z ≠ endpointDistance right := fun he ↦ hx.2.2 (by linarith)
    obtain ⟨hv, hq⟩ := side_regular right rne
    have eh : twoSidedHat z left right =ᶠ[𝓝 x] fun t ↦ hatSide right (t - z) := by
      filter_upwards [lt_mem_nhds h] with t ht using ite_eq_right (not_le.mpr ht)
    have eq : hatSlope z left right =ᶠ[𝓝 x] fun t ↦ sideSlope right (t - z) := by
      filter_upwards [lt_mem_nhds h] with t ht using ite_eq_right (not_le.mpr ht)
    have id' := (hasDerivAt_id x).sub_const z
    exact ⟨by simpa [hatSlope, not_le.mpr h] using (hv.comp x id').congr_of_eventuallyEq eh,
      by simpa [twoSidedHat, not_le.mpr h] using (hq.comp x id').congr_of_eventuallyEq eq⟩

private theorem hatSide_bounds (gap : Option (Ioi (0 : ℝ))) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ hatSide gap r ∧ hatSide gap r ≤ Real.exp (-r) := by
  cases gap with
  | none => exact ⟨(Real.exp_pos _).le, le_rfl⟩
  | some d =>
    by_cases h : r ≤ d.1
    · simpa [hatSide, h] using GeometricHat.profile_bounds d.2 hr h
    · simp [hatSide, h, (Real.exp_pos (-r)).le]

private theorem sideSlope_bound (gap : Option (Ioi (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ‖sideSlope gap r‖ ≤ C * Real.exp (-r) := by
  cases gap with
  | none =>
    refine ⟨1, zero_le_one, fun r _ ↦ ?_⟩
    simp [sideSlope, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  | some d =>
    have hd : 0 < d.1 := d.2
    have hs := Real.sinh_pos_iff.mpr hd
    let K := Real.cosh d.1 / Real.sinh d.1
    have hK : 0 ≤ K := div_nonneg (Real.cosh_pos _).le hs.le
    refine ⟨K * Real.exp d.1, mul_nonneg hK (Real.exp_pos _).le, fun r hr ↦ ?_⟩
    by_cases h : r ≤ d.1
    · have hc : Real.cosh (d.1 - r) ≤ Real.cosh d.1 := by
        rw [Real.cosh_le_cosh, abs_of_nonneg (sub_nonneg.mpr h), abs_of_pos hd]
        linarith only [hr]
      have he : 1 ≤ Real.exp d.1 * Real.exp (-r) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]
        linarith only [h]
      calc
        ‖sideSlope (some d) r‖ = Real.cosh (d.1 - r) / Real.sinh d.1 := by
          simp only [sideSlope, h, ↓reduceIte, (GeometricHat.hasDerivAt_profile d.1 r).deriv,
            Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos (Real.cosh_pos _), abs_of_pos hs]
        _ ≤ K := div_le_div_of_nonneg_right hc hs.le
        _ ≤ K * (Real.exp d.1 * Real.exp (-r)) := le_mul_of_one_le_right hK he
        _ = _ := by ring
    · simp only [sideSlope, h, ↓reduceIte, norm_zero]
      exact mul_nonneg (mul_nonneg hK (Real.exp_pos _).le) (Real.exp_pos _).le

/-- The full hat is nonnegative and bounded by the unsplit exponential kernel. -/
theorem twoSidedHat_bounds (z : ℝ) (left right : Option (Ioi (0 : ℝ))) (t : ℝ) :
    0 ≤ twoSidedHat z left right t ∧ twoSidedHat z left right t ≤ Real.exp (-|t - z|) := by
  by_cases ht : t ≤ z
  · simpa only [twoSidedHat, ht, ↓reduceIte, abs_sub_comm t z, abs_of_nonneg (sub_nonneg.mpr ht)]
      using hatSide_bounds left (sub_nonneg.mpr ht)
  · have ht' := sub_nonneg.mpr (le_of_not_ge ht)
    simpa only [twoSidedHat, ht, ↓reduceIte, abs_of_nonneg ht'] using hatSide_bounds right ht'

private theorem hatSlope_bound (z : ℝ) (left right : Option (Ioi (0 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖hatSlope z left right t‖ ≤ C * Real.exp (-|t-z|) := by
  obtain ⟨A, hA, ha⟩ := sideSlope_bound left
  obtain ⟨B, _, hb⟩ := sideSlope_bound right
  refine ⟨max A B, hA.trans (le_max_left A B), fun t ↦ ?_⟩
  by_cases ht : t ≤ z
  · rw [hatSlope, ite_eq_left ht, norm_neg, abs_sub_comm t z, abs_of_nonneg (sub_nonneg.mpr ht)]
    exact (ha _ (sub_nonneg.mpr ht)).trans
      (mul_le_mul_of_nonneg_right (le_max_left A B) (Real.exp_pos _).le)
  · have ht' := sub_nonneg.mpr (le_of_not_ge ht)
    rw [hatSlope, ite_eq_right ht, abs_of_nonneg ht']
    exact (hb _ ht').trans
      (mul_le_mul_of_nonneg_right (le_max_right A B) (Real.exp_pos _).le)

private theorem continuous_hat_flux (z : ℝ) (left right : Option (Ioi (0 : ℝ)))
    {b : ℝ → ℂ} (hb : Continuous b) (hz : b z = 0) :
    Continuous (cardinalFlux b (twoSidedHat z left right) (hatSlope z left right)) := by
  let f := fun t : ℝ ↦ ‖b t‖ ^ 2 * twoSidedHat z left right t * hatSlope z left right t
  have e : f = fun t ↦ if t ≤ z then
        -(‖b t‖ ^ 2 * (hatSide left (z - t) * sideSlope left (z - t))) else
        ‖b t‖ ^ 2 * (hatSide right (t - z) * sideSlope right (t - z)) := by
    funext t
    by_cases ht : t ≤ z <;> simp [f, twoSidedHat, hatSlope, ht, mul_assoc]
  have cf : Continuous f := by
    rw [e]
    apply (((hb.norm.pow 2).mul ((continuous_side_flux left).comp
        (continuous_const.sub continuous_id))).neg).if_le
      ((hb.norm.pow 2).mul ((continuous_side_flux right).comp (continuous_id.sub continuous_const)))
      continuous_id continuous_const
    intro t (ht : t = z)
    simp [ht, hz]
  exact cf.add (((continuous_twoSidedHat z left right).smul hb).norm.pow 2)

private theorem integrable_hat_weight_sq (z : ℝ) :
    Integrable (fun t : ℝ ↦ Real.exp (-|t-z|) ^ 2) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := z), integrableOn_union]
  constructor
  · have hi := (integrableOn_exp_mul_Iic (a := 2) (by norm_num) z).mul_const (Real.exp (-2*z))
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    rw [abs_of_nonpos (sub_nonpos.mpr ht), sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  · have hi := (integrableOn_exp_mul_Ioi (a := -2) (by norm_num) z).mul_const (Real.exp (2*z))
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt ht)), sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring

private theorem tendsto_hat_weight_atBot (z : ℝ) :
    Tendsto (fun t : ℝ ↦ Real.exp (-|t-z|)) atBot (𝓝 0) := by
  have hl := Real.tendsto_exp_atBot.mul_const (Real.exp (-z))
  rw [zero_mul] at hl
  apply hl.congr'
  filter_upwards [eventually_le_atBot z] with t ht
  rw [← Real.exp_add, abs_of_nonpos (sub_nonpos.mpr ht)]
  congr 1
  ring

private theorem tendsto_hat_weight_atTop (z : ℝ) :
    Tendsto (fun t : ℝ ↦ Real.exp (-|t-z|)) atTop (𝓝 0) := by
  have hl := (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).mul_const (Real.exp z)
  rw [zero_mul] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop z] with t ht
  change Real.exp (-t) * Real.exp z = Real.exp (-|t-z|)
  rw [← Real.exp_add, abs_of_nonneg (sub_nonneg.mpr ht)]
  congr 1
  ring

private theorem norm_causal_le {b : ℝ → ℂ} {h q : ℝ → ℝ} {x B L C w : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ C) (hb : HasDerivAt b (deriv b x) x) (hh : HasDerivAt h (q x) x)
    (hB : ‖b x‖ ≤ B) (hL : ‖deriv b x‖ ≤ L) (hv : ‖h x‖ ≤ w) (hq : ‖q x‖ ≤ C * w) :
    ‖cardinalCausal b h x‖ ≤ (B + L + C*B) * w := by
  have hp := hh.smul hb
  change HasDerivAt (fun t ↦ h t • b t) _ x at hp
  rw [cardinalCausal, hp.deriv]
  calc
    _ ≤ ‖h x • b x‖ + (‖h x • deriv b x‖ + ‖q x • b x‖) :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ w * B + (w * L + (C*w) * B) := by
      simp only [norm_smul]
      exact add_le_add (mul_le_mul hv hB (norm_nonneg _) hw)
        (add_le_add (mul_le_mul hv hL (norm_nonneg _) hw)
          (mul_le_mul hq hB (norm_nonneg _) (mul_nonneg hc hw)))
    _ = _ := by ring

private theorem norm_flux_le {b : ℝ → ℂ} {h q : ℝ → ℝ} {x B C w : ℝ}
    (hw : 0 ≤ w) (hB : ‖b x‖ ≤ B)
    (hv : ‖h x‖ ≤ w) (hq : ‖q x‖ ≤ C*w) :
    ‖cardinalFlux b h q x‖ ≤ (B ^ 2 * C + B ^ 2) * w ^ 2 := by
  have hbb := pow_le_pow_left₀ (norm_nonneg _) hB 2
  calc
    _ ≤ ‖‖b x‖ ^ 2 * h x * q x‖ + ‖‖h x • b x‖ ^ 2‖ := norm_add_le _ _
    _ = ‖b x‖ ^ 2 * ‖h x‖ * ‖q x‖ + (‖h x‖ * ‖b x‖) ^ 2 := by
      simp only [norm_mul, norm_pow, norm_norm, norm_smul]
    _ ≤ B ^ 2 * w * (C*w) + (w*B) ^ 2 := by
      exact add_le_add
        (mul_le_mul (mul_le_mul hbb hv (norm_nonneg _) (sq_nonneg _))
          hq (norm_nonneg _) (mul_nonneg (sq_nonneg _) hw))
        (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul hv hB (norm_nonneg _) hw) 2)
    _ = _ := by ring

private theorem integrable_sq_of_hat_bound {z C : ℝ} {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g volume) (hb : ∀ᵐ t : ℝ, ‖g t‖ ≤ C * Real.exp (-|t-z|)) :
    Integrable (fun t ↦ ‖g t‖ ^ 2) := by
  apply ((integrable_hat_weight_sq z).const_mul (C^2)).mono' (hg.norm.pow 2)
  filter_upwards [hb] with t ht
  change ‖‖g t‖ ^ 2‖ ≤ C^2 * Real.exp (-|t-z|)^2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) ht 2

private theorem integrable_mul_hat_sq {z L : ℝ} {v a : ℝ → ℝ}
    (cv : Continuous v) (ca : Continuous a) (hv : ∀ t, 0 ≤ v t ∧ v t ≤ L)
    (ha : ∀ t, 0 ≤ a t ∧ a t ≤ Real.exp (-|t-z|)) :
    Integrable (fun t : ℝ ↦ v t ^ 2 * a t ^ 2) := by
  apply ((integrable_hat_weight_sq z).const_mul (L^2)).mono'
    (((cv.pow 2).mul (ca.pow 2)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro t
  change ‖v t ^ 2 * a t ^ 2‖ ≤ L^2 * Real.exp (-|t-z|)^2
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact mul_le_mul (pow_le_pow_left₀ (hv t).1 (hv t).2 2)
    (pow_le_pow_left₀ (ha t).1 (ha t).2 2) (sq_nonneg _) (sq_nonneg _)

/-- A bounded continuously differentiable multiplier vanishing at the central node
produces an ordinary complex L² causal representative. The derivative holds off three
specified joins. Its exact energy uses the squared hat, and its upper bound has constant one. -/
theorem twoSidedHat_causal_energy (z : ℝ) (left right : Option (Ioi (0 : ℝ)))
    (b : ℝ → ℂ) {B L : ℝ} (hb : ContDiff ℝ 1 b) (hz : b z = 0)
    (hB : ∀ t, ‖b t‖ ≤ B) (hL : ∀ t, ‖deriv b t‖ ≤ L) :
    let h := twoSidedHat z left right
    let p := fun t ↦ h t • b t
    let g := cardinalCausal b h
    Continuous p ∧ MemLp g 2 volume ∧
      (∀ t ∉ hatJoins z left right, HasDerivAt p (g t - p t) t) ∧
      Tendsto (fun t : ℝ ↦ (Real.exp t : ℂ) * p t) atBot (𝓝 0) ∧
      ((∫ t, ‖g t‖ ^ 2) = ∫ t, ‖deriv b t‖ ^ 2 * h t ^ 2) ∧
      (∫ t, ‖g t‖ ^ 2) ≤ ∫ t, ‖deriv b t‖ ^ 2 * Real.exp (-2 * |t-z|) := by
  let h := twoSidedHat z left right
  let q := hatSlope z left right
  let s := hatJoins z left right
  let p := fun t ↦ h t • b t
  let g := cardinalCausal b h
  let w := fun t : ℝ ↦ Real.exp (-|t-z|)
  have ch : Continuous h := continuous_twoSidedHat z left right
  have cp : Continuous p := ch.smul hb.continuous
  have hc : Continuous (cardinalFlux b h q) := continuous_hat_flux z left right hb.continuous hz
  have hbw (t : ℝ) : 0 ≤ h t ∧ h t ≤ w t := twoSidedHat_bounds z left right t
  have hn (t : ℝ) : ‖h t‖ ≤ w t := by simpa only [Real.norm_of_nonneg (hbw t).1] using (hbw t).2
  obtain ⟨C, hC, hq⟩ := hatSlope_bound z left right
  have reg (t : ℝ) (ht : t ∉ s) : HasDerivAt h (q t) t ∧ HasDerivAt q (h t) t :=
    hat_regular z left right ht
  have hmeas : AEStronglyMeasurable g volume := cp.aestronglyMeasurable.add (aestronglyMeasurable_deriv p _)
  have aeReg : ∀ᵐ t : ℝ, t ∉ s := s.finite_toSet.countable.ae_notMem volume
  have eg : Integrable (fun t ↦ ‖g t‖ ^ 2) := by
    apply integrable_sq_of_hat_bound (z := z) (C := B + L + C*B) hmeas
    filter_upwards [aeReg] with t ht
    exact norm_causal_le (Real.exp_pos _).le hC (hb.differentiable_one t).hasDerivAt
      (reg t ht).1 (hB t) (hL t) (hn t) (hq t)
  have hg : MemLp g 2 volume := (memLp_two_iff_integrable_sq_norm hmeas).mpr eg
  have ew : Integrable (fun t ↦ ‖deriv b t‖ ^ 2 * h t ^ 2) :=
    integrable_mul_hat_sq hb.continuous_deriv_one.norm ch (fun t ↦ ⟨norm_nonneg _, hL t⟩) hbw
  have wpos (t : ℝ) : 0 ≤ w t := (Real.exp_pos _).le
  have eww : Integrable (fun t ↦ ‖deriv b t‖ ^ 2 * w t ^ 2) :=
    integrable_mul_hat_sq hb.continuous_deriv_one.norm (by dsimp [w]; fun_prop)
      (fun t ↦ ⟨norm_nonneg _, hL t⟩) (fun t ↦ ⟨wpos t, le_rfl⟩)
  have flux_limit {l : Filter ℝ} (hw : Tendsto w l (𝓝 0)) :
      Tendsto (cardinalFlux b h q) l (𝓝 0) := by
    apply squeeze_zero_norm (fun t ↦ norm_flux_le (wpos t) (hB t) (hn t) (hq t))
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using (hw.pow 2).const_mul (B^2*C + B^2)
  have eqn := whole_line_cardinal_energy b h q s hb.differentiable_one
    (fun t ht ↦ (reg t ht).1) (fun t ht ↦ (reg t ht).2) hc
    (flux_limit (tendsto_hat_weight_atBot z)) (flux_limit (tendsto_hat_weight_atTop z)) eg ew
  refine ⟨cp, hg, ?_, ?_, eqn, ?_⟩
  · intro t ht
    have hp : HasDerivAt p (deriv p t) t :=
      ((reg t ht).1.smul (hb.differentiable_one t).hasDerivAt).differentiableAt.hasDerivAt
    simpa only [g, cardinalCausal, p, add_sub_cancel_left] using hp
  · apply squeeze_zero_norm (a := fun t : ℝ ↦ Real.exp t * B)
    · intro t
      have hw1 : w t ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
      have hsmall : ‖p t‖ ≤ B := by
        change ‖h t • b t‖ ≤ B
        rw [norm_smul]
        calc
          _ ≤ 1 * B := mul_le_mul ((hn t).trans hw1) (hB t) (norm_nonneg _) zero_le_one
          _ = B := one_mul _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_left hsmall (Real.exp_pos _).le
    · simpa only [zero_mul] using Real.tendsto_exp_atBot.mul_const B
  · have hle : (∫ t, ‖deriv b t‖ ^ 2 * h t ^ 2) ≤ ∫ t, ‖deriv b t‖ ^ 2 * w t ^ 2 := by
      apply integral_mono ew eww
      intro t
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hbw t).1 (hbw t).2 2) (sq_nonneg _)
    have hw2 (t : ℝ) : w t ^ 2 = Real.exp (-2 * |t - z|) := by
      change (Real.exp (-|t-z|))^2 = _
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    simpa only [hw2] using eqn.le.trans hle

end RiemannMasullo.LineGeometricFourier
