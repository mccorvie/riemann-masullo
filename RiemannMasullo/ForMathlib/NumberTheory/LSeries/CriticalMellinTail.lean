module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
public import RiemannMasullo.ForMathlib.MeasureTheory.Integral.CayleyCauchy
public import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic

/-! # Effective vertical tails from bounded Dirichlet partial sums

An Abel remainder supported above a cutoff has a quantitative Mellin–Plancherel bound.
The finite Dirichlet polynomial is bounded separately on the high-frequency set. -/

@[expose] public noncomputable section

open MeasureTheory Complex Set Filter Asymptotics
open scoped Topology ENNReal NNReal

namespace RiemannMasullo.CriticalMellinTail

/-- The ordinary critical line in the conventional ordinate. -/
def line (t : ℝ) : ℂ := 1/2 + (t : ℂ)*I

@[simp] theorem line_re (t : ℝ) : (line t).re = 1/2 := by simp [line]
@[simp] theorem line_im (t : ℝ) : (line t).im = t := by simp [line]

private theorem line_ne (t : ℝ) : line t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

/-- Abel integral divided by its Mellin parameter, with a partial-sum sequence as input. -/
def transform (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∫ x : ℝ in Ioi 1, a ⌊x⌋₊ * (x : ℂ) ^ (-(line t + 1))

private def physical (a : ℕ → ℂ) : ℝ → ℂ :=
  (Ioi 0).indicator (fun u : ℝ ↦ a ⌊Real.exp u⌋₊ * (Real.exp (-(u/2)) : ℂ))

private theorem physical_measurable (a : ℕ → ℂ) : Measurable (physical a) := by
  have h := (measurable_of_countable a).comp (Nat.measurable_floor.comp Real.measurable_exp)
  exact (h.mul (by fun_prop)).indicator measurableSet_Ioi

private theorem physical_norm (a : ℕ → ℂ) {u : ℝ} (hu : 0 < u) :
    ‖physical a u‖ = ‖a ⌊Real.exp u⌋₊‖ * Real.exp (-(u/2)) := by
  rw [physical, Set.indicator_of_mem (Set.mem_Ioi.mpr hu), norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

private theorem transform_eq_bilateral (a : ℕ → ℂ) (t : ℝ) :
    transform a t = bilateralLaplace (physical a) (0 + ((-t : ℝ) : ℂ) * I) := by
  unfold transform bilateralLaplace
  have h := integral_comp_exp_Ioi
    (fun x : ℝ ↦ a ⌊x⌋₊ * (x : ℂ) ^ (-(line t + 1))) 0
  rw [Real.exp_zero] at h
  rw [← h, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ Ioi (0 : ℝ)
  swap
  · rw [Set.indicator_of_notMem hu, physical, Set.indicator_of_notMem hu, zero_mul]
  rw [Set.indicator_of_mem hu, physical, Set.indicator_of_mem hu]
  rw [Complex.real_smul, Complex.cpow_def_of_ne_zero
    (ofReal_ne_zero.mpr (Real.exp_pos u).ne'), ← Complex.ofReal_log (Real.exp_pos u).le,
    Real.log_exp, Complex.ofReal_exp, Complex.ofReal_exp]
  simp only [zero_add, ofReal_neg, ofReal_div, ofReal_ofNat]
  unfold line
  calc
    _ = a ⌊Real.exp u⌋₊ * (cexp (u : ℂ) * cexp ((u : ℂ) * -(1/2 + t*I + 1))) := by ring
    _ = a ⌊Real.exp u⌋₊ * (cexp (-(u/2 : ℂ)) * cexp ((- (t : ℂ) * I) * u)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 2
      ring
    _ = _ := by ring

private theorem weighted_memLp {a : ℕ → ℂ} {D : ℝ} (ha : ∀ n, ‖a n‖ ≤ D) :
    MemLp (fun u : ℝ ↦ Real.exp ((1/4)*|u|) • physical a u) 2 := by
  have hm : AEStronglyMeasurable (fun u : ℝ ↦ Real.exp ((1/4)*|u|) • physical a u) :=
    (by fun_prop : Measurable (fun u : ℝ ↦ Real.exp ((1/4)*|u|))).smul
      (physical_measurable a) |>.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).2
  have hdom : Integrable ((Ioi (0 : ℝ)).indicator (fun u ↦ D^2 * Real.exp ((-1/2)*u))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr
      ((integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 0).const_mul (D^2))
  refine hdom.mono' (hm.norm.pow 2) (.of_forall (fun u ↦ ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  by_cases hu : 0 < u
  · rw [Set.indicator_of_mem hu, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      physical_norm a hu, abs_of_pos hu]
    have he : (Real.exp ((1/4)*u)*Real.exp (-(u/2)))^2 = Real.exp ((-1/2)*u) := by
      rw [← Real.exp_add, sq, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = ‖a ⌊Real.exp u⌋₊‖^2 * (Real.exp ((1/4)*u)*Real.exp (-(u/2)))^2 := by ring
      _ ≤ _ := by rw [he]; gcongr; exact ha _
  · simp [physical, Set.mem_Ioi, hu]

private theorem transform_plancherel {a : ℕ → ℂ} {D : ℝ} (ha : ∀ n, ‖a n‖ ≤ D) :
    Integrable (fun t : ℝ ↦ ‖transform a t‖^2) ∧
      ∫ t : ℝ, ‖transform a t‖^2 = 2*Real.pi * ∫ u : ℝ, ‖physical a u‖^2 := by
  have h := weighted_memLp ha
  have hz : |(0 : ℝ)| < 1/4 := by norm_num
  have hi := integrable_norm_sq_bilateralLaplace h hz
  have he := integral_norm_sq_bilateralLaplace h hz
  let F : ℝ → ℝ := fun t ↦ ‖bilateralLaplace (physical a) (0 + (t : ℂ)*I)‖^2
  change Integrable F at hi
  change ∫ t, F t = _ at he
  have ht : (fun t : ℝ ↦ ‖transform a t‖^2) = fun t ↦ F (-t) := by
    funext t; rw [transform_eq_bilateral]
  rw [ht]
  refine ⟨hi.comp_neg, ?_⟩
  rw [integral_neg_eq_self F, he]
  simp

/-- A bounded Abel remainder vanishing through the integer cutoff has total angular
frequency energy at most `2π D²/X`. -/
theorem transform_energy_le {a : ℕ → ℂ} {D X : ℝ} (hX : 1 ≤ X)
    (ha : ∀ n, ‖a n‖ ≤ D) (hzero : ∀ n ≤ ⌊X⌋₊, a n = 0) :
    Integrable (fun t : ℝ ↦ ‖transform a t‖^2) ∧
      ∫ t : ℝ, ‖transform a t‖^2 ≤ 2*Real.pi*(D^2/X) := by
  obtain ⟨hi, hp⟩ := transform_plancherel ha
  refine ⟨hi, hp.trans_le (mul_le_mul_of_nonneg_left ?_ (by positivity))⟩
  let major : ℝ → ℝ := (Ioi (Real.log X)).indicator (fun u ↦ D^2*Real.exp (-u))
  have hm : Integrable major :=
    (integrable_indicator_iff measurableSet_Ioi).mpr
      ((integrableOn_exp_neg_Ioi (Real.log X)).const_mul (D^2))
  have hb (u : ℝ) : ‖physical a u‖^2 ≤ major u := by
    by_cases hu : Real.log X < u
    · have hu0 := (Real.log_nonneg hX).trans_lt hu
      rw [physical_norm a hu0, mul_pow]
      change _ ≤ (Ioi (Real.log X)).indicator _ u
      rw [Set.indicator_of_mem hu]
      have he : Real.exp (-(u/2))^2 = Real.exp (-u) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      rw [he]
      gcongr
      exact ha _
    · have hx : Real.exp u ≤ X := (Real.exp_le_exp.mpr (le_of_not_gt hu)).trans_eq
        (Real.exp_log (zero_lt_one.trans_le hX))
      have hz := hzero _ (Nat.floor_le_floor hx)
      rw [show major u = 0 by exact Set.indicator_of_notMem (show u ∉ Ioi (Real.log X) from hu) _]
      by_cases hu0 : 0 < u <;> simp [physical, Set.mem_Ioi, hu0, hz]
  have hi' : Integrable (fun u ↦ ‖physical a u‖^2) :=
    hm.mono' ((physical_measurable a).norm.pow_const 2).aestronglyMeasurable
      (.of_forall (fun u ↦ by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖physical a u‖)] using hb u))
  calc
    _ ≤ ∫ u : ℝ, major u := integral_mono hi' hm hb
    _ = D^2/X := by
      rw [show (∫ u : ℝ, major u) = ∫ u in Ioi (Real.log X), D^2*Real.exp (-u) from
        integral_indicator measurableSet_Ioi, integral_const_mul, integral_exp_neg_Ioi, Real.exp_neg,
        Real.exp_log (zero_lt_one.trans_le hX), div_eq_mul_inv]

private theorem inv_sqrt_sum (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, (Real.sqrt k)⁻¹) ≤ 2*Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N+1)]
    set a := Real.sqrt ((N+1 : ℕ) : ℝ) with ha
    set b := Real.sqrt (N : ℝ) with hb
    have hapos : 0 < a := Real.sqrt_pos.mpr (by positivity)
    have hA := Real.sq_sqrt (show 0 ≤ ((N+1 : ℕ) : ℝ) by positivity)
    have hB := Real.sq_sqrt (show 0 ≤ (N : ℝ) by positivity)
    change a^2 = _ at hA
    change b^2 = _ at hB
    have hu : a⁻¹ ≤ 2*(a-b) := by
      rw [← one_div]
      apply (div_le_iff₀ hapos).mpr
      push_cast at hA
      nlinarith [sq_nonneg (a-b)]
    change _ ≤ 2*a
    change _ ≤ 2*b at ih
    linarith

/-- The classical finite Dirichlet sum on the critical line. -/
def polynomial (c : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 N, c k / (k : ℂ)^(line t)

private theorem polynomial_bound {c : ℕ → ℂ} (hc : ∀ k, ‖c k‖ ≤ 1) (N : ℕ) (t : ℝ) :
    ‖polynomial c N t‖ ≤ 2*Real.sqrt N := by
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun k hk ↦ ?_)).trans (inv_sqrt_sum N))
  have hpos : 0 < (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  rw [norm_div, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hpos,
    line_re, ← Real.sqrt_eq_rpow, ← one_div]
  gcongr
  exact hc k

private def truncated (c : ℕ → ℂ) (N : ℕ) (k : ℕ) : ℂ := if k ≤ N then c k else 0

private theorem truncated_sum (c : ℕ → ℂ) (N n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, truncated c N k) = ∑ k ∈ Finset.Icc 1 (min n N), c k := by
  classical
  rw [show (∑ k ∈ Finset.Icc 1 n, truncated c N k) =
    ∑ k ∈ (Finset.Icc 1 n).filter (· ≤ N), c k by simp [truncated, Finset.sum_filter]]
  congr 1
  ext k
  simp [le_min_iff, and_assoc]

private theorem polynomial_abel (c : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    polynomial c N t = line t * transform (fun n ↦ ∑ k ∈ Finset.Icc 1 (min n N), c k) t := by
  let f := truncated c N
  have hsum : LSeries f (line t) = polynomial c N t := by
    change ∑' k, LSeries.term f (line t) k = _
    rw [tsum_eq_sum (s := Finset.Icc 1 N)]
    · apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_Icc.mp hk
      rw [LSeries.term_of_ne_zero (Nat.ne_of_gt hk'.1), show f k = c k by simp [f, truncated, hk'.2]]
    · intro k hk
      by_cases hk0 : k = 0
      · simp [hk0]
      · have hkN : ¬k ≤ N := fun h ↦ hk (Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hk0,h⟩)
        simp [LSeries.term_of_ne_zero hk0, f, truncated, hkN]
  have hbig : (fun n ↦ ∑ k ∈ Finset.Icc 1 n, ‖f k‖) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ)^(0 : ℝ)) := by
    apply isBigO_iff.mpr
    refine ⟨∑ k ∈ Finset.Icc 1 N, ‖c k‖, .of_forall (fun n ↦ ?_)⟩
    simp only [Real.rpow_zero, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))]
    have hf' : (∑ k ∈ Finset.Icc 1 n, ‖f k‖) =
        ∑ k ∈ Finset.Icc 1 (min n N), ‖c k‖ := by
      simp only [f, truncated, apply_ite norm, norm_zero, ← Finset.sum_filter]
      congr 1
      ext k
      simp [le_min_iff, and_assoc]
    rw [hf']
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (min_le_right _ _))
      (fun i _ _ ↦ norm_nonneg _)
  rw [← hsum, LSeries_eq_mul_integral' f (r:=0) le_rfl (by simp) hbig]
  simp only [f, truncated_sum, transform]

/-- The tail outside the symmetric closed interval of height `T`. -/
def far (T : ℝ) : Set ℝ := {t | T < |t|}

theorem measurableSet_far (T : ℝ) : MeasurableSet (far T) :=
  isOpen_lt continuous_const continuous_abs |>.measurableSet

private theorem inv_sq_tail {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun t : ℝ ↦ 1/t^2) (far T) ∧
      (∫ t : ℝ in far T, 1/t^2) = 2/T := by
  let f : ℝ → ℝ := fun t ↦ 1/t^2
  have hp : IntegrableOn f (Ioi T) := by
    refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hT).congr_fun
      (fun x hx ↦ ?_) measurableSet_Ioi
    change x^(-(2 : ℝ)) = 1/x^2
    rw [Real.rpow_neg (hT.trans hx).le, Real.rpow_two, one_div]
  have hi : ∫ t in Ioi T, f t = 1/T := by
    calc
      _ = ∫ t in Ioi T, t^(-2 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change 1/t^2 = t^(-(2 : ℝ))
        rw [Real.rpow_neg (hT.trans ht).le, Real.rpow_two, one_div]
      _ = _ := by
        rw [integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hT]
        norm_num [Real.rpow_neg_one, one_div]
  have hm : IntegrableOn f (Iio (-T)) := by
    have hq : IntegrableOn f (Ioi (-(-T))) := by simpa using hp
    simpa [f, neg_sq] using hq.comp_neg_Iio
  have he : (∫ t in Iio (-T), f t) = 1/T := by
    rw [setIntegral_congr_set (μ := volume) (Iio_ae_eq_Iic (a := -T)), ← integral_comp_neg_Ioi T f]
    simpa [f, neg_sq] using hi
  have hz : far T = Iio (-T) ∪ Ioi T := by
    ext t
    change T < |t| ↔ t < -T ∨ T < t
    rw [lt_abs]
    constructor <;> rintro (h | h)
    · exact Or.inr h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl h
  rw [hz]
  refine ⟨hm.union hp, ?_⟩
  change ∫ t in Iio (-T) ∪ Ioi T, f t = _
  have hdis : Disjoint (Iio (-T)) (Ioi T) := Set.disjoint_left.mpr (by
    intro t ht₁ ht₂
    exact (lt_irrefl t) (ht₁.trans ((by linarith : -T < T).trans ht₂)))
  rw [setIntegral_union hdis measurableSet_Ioi hm hp, he, hi]
  ring

private theorem integrable_abel {a : ℕ → ℂ} {D : ℝ} (ha : ∀ n, ‖a n‖ ≤ D) (t : ℝ) :
    IntegrableOn (fun x : ℝ ↦ a ⌊x⌋₊ * (x : ℂ)^(-(line t+1))) (Ioi 1) := by
  have hp := integrableOn_Ioi_rpow_of_lt (by norm_num : -(1/2+1 : ℝ) < -1) zero_lt_one
  have hm : Measurable (fun x : ℝ ↦ a ⌊x⌋₊) :=
    (measurable_of_countable a).comp Nat.measurable_floor
  refine (hp.const_mul D).mono' ((hm.mul (by fun_prop)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with x hx
  have hx' : 0 < x := zero_lt_one.trans hx
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx']
  simp only [neg_re, add_re, line_re, one_re]
  gcongr
  exact ha _

private def partialSum (c : ℕ → ℂ) (n : ℕ) : ℂ := ∑ k ∈ Finset.Icc 1 n, c k

private def remainder (c : ℕ → ℂ) (N n : ℕ) : ℂ :=
  partialSum c n - partialSum c (min n N)

private theorem split {c : ℕ → ℂ} {D : ℝ}
    (hD : ∀ m n, ‖partialSum c m - partialSum c n‖ ≤ D) (N : ℕ) (t : ℝ) :
    line t * transform (partialSum c) t =
      polynomial c N t + line t * transform (remainder c N) t := by
  have hb (n) : ‖partialSum c n‖ ≤ D := by simpa [partialSum] using hD n 0
  rw [polynomial_abel]
  change _ = line t * transform (fun n ↦ partialSum c (min n N)) t + _
  rw [← mul_add]
  congr 1
  unfold transform remainder
  simp_rw [sub_mul]
  rw [integral_sub (integrable_abel hb t) (integrable_abel (fun n ↦ hb (min n N)) t)]
  abel

private theorem center_ratio (t : ℝ) (v : ℂ) :
    CayleyCauchy.density (3/2) t * ‖v‖^2 ≤ (3/2/Real.pi) * ‖v/line t‖^2 := by
  have hq : ‖line t‖^2 = (1/2 : ℝ)^2+t^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, line_re, line_im]; ring
  have h2 : 0 < ‖line t‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (line_ne t))
  have hle : ‖line t‖^2 ≤ (3/2:ℝ)^2+t^2 := by rw [hq]; linarith
  rw [CayleyCauchy.density, norm_div, div_pow]
  calc
    _ ≤ ((3/2)/(Real.pi*‖line t‖^2))*‖v‖^2 := by
      gcongr
      simpa only [div_pow] using hle
    _ = _ := by ring

private theorem polynomial_ratio {c : ℕ → ℂ} (hc : ∀ k, ‖c k‖ ≤ 1) {X t : ℝ}
    (hX : 0 ≤ X) (ht : t ≠ 0) :
    ‖polynomial c ⌊X⌋₊ t / line t‖^2 ≤ 4*X*(1/t^2) := by
  have hP := (polynomial_bound hc ⌊X⌋₊ t).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.floor_le hX)) (by norm_num))
  have ht' : 0 < t^2 := sq_pos_of_ne_zero ht
  have hI : |t| ≤ ‖line t‖ := by simpa using Complex.abs_im_le_norm (line t)
  have hs : t^2 ≤ ‖line t‖^2 := by simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg t) (norm_nonneg _)).mpr hI
  rw [norm_div, div_pow]
  calc
    _ ≤ (2*Real.sqrt X)^2/t^2 := by gcongr
    _ = _ := by rw [mul_pow, Real.sq_sqrt hX]; ring

/-- An effective upper bound for the actual critical-line tail of any Abel sum with
coefficients bounded by one and partial sums of diameter `D`. -/
theorem tail_energy {c : ℕ → ℂ} {F : ℝ → ℂ} {D T X : ℝ} (hF : Measurable F)
    (hc : ∀ k, ‖c k‖ ≤ 1)
    (hD : ∀ m n, ‖(∑ k ∈ Finset.Icc 1 m, c k) - ∑ k ∈ Finset.Icc 1 n, c k‖ ≤ D)
    (hAbel : ∀ t, F t = line t * transform (fun n ↦ ∑ k ∈ Finset.Icc 1 n, c k) t)
    (hT : 0 < T) (hX : 1 ≤ X) :
    IntegrableOn (fun t ↦ CayleyCauchy.density (3/2) t * ‖F t‖^2) (far T) ∧
    ∫ t in far T, CayleyCauchy.density (3/2) t * ‖F t‖^2 ≤
      24/Real.pi*(X/T) + 6*(D^2/X) := by
  let R : ℝ → ℂ := transform (remainder c ⌊X⌋₊)
  have hr : (∀ n, ‖remainder c ⌊X⌋₊ n‖ ≤ D) := fun n ↦ hD n (min n ⌊X⌋₊)
  have hz (n) (h : n ≤ ⌊X⌋₊) : remainder c ⌊X⌋₊ n = 0 := by simp [remainder, min_eq_left h]
  obtain ⟨hri,hre⟩ := transform_energy_le hX hr hz
  change Integrable (fun t ↦ ‖R t‖^2) at hri
  change (∫ t, ‖R t‖^2) ≤ _ at hre
  obtain ⟨hit,het⟩ := inv_sq_tail hT
  let M (t : ℝ) := (3/Real.pi)*(4*X*(1/t^2) + ‖R t‖^2)
  have hm : IntegrableOn M (far T) := ((hit.const_mul (4*X)).add hri.integrableOn).const_mul _
  have hb (t : ℝ) (ht : t ∈ far T) : CayleyCauchy.density (3/2) t * ‖F t‖^2 ≤ M t := by
    have hn : t ≠ 0 := by intro h; subst t; simp [far, hT.not_gt] at ht
    have he : F t/line t = polynomial c ⌊X⌋₊ t/line t + R t := by
      rw [hAbel]
      change (line t * transform (partialSum c) t) / line t = _
      rw [split hD ⌊X⌋₊ t]
      change (_+line t*R t)/line t = _
      field_simp [line_ne t]
    refine (center_ratio t (F t)).trans ?_
    rw [he]
    have hp := polynomial_ratio hc (zero_le_one.trans hX) hn
    have hu := norm_add_le (polynomial c ⌊X⌋₊ t/line t) (R t)
    have hsq := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hu
    have hsum : ‖polynomial c ⌊X⌋₊ t /line t + R t‖^2 ≤
        2 * (4*X*(1/t^2) + ‖R t‖^2) := by
      nlinarith [sq_nonneg (‖polynomial c ⌊X⌋₊ t/line t‖ - ‖R t‖)]
    calc
      _ ≤ (3/2/Real.pi)*(2 * (4*X*(1/t^2) + ‖R t‖^2)) := by gcongr
      _ = _ := by unfold M; ring
  have hi : IntegrableOn (fun t ↦ CayleyCauchy.density (3/2) t * ‖F t‖^2) (far T) := by
    apply hm.mono'
    · exact ((by unfold CayleyCauchy.density; fun_prop : Measurable (CayleyCauchy.density (3/2))).mul
        (hF.norm.pow_const 2)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_far T)] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by unfold CayleyCauchy.density; positivity)]
      exact hb t ht
  refine ⟨hi, (setIntegral_mono_on hi hm (measurableSet_far T) hb).trans ?_⟩
  unfold M
  rw [integral_const_mul, integral_add (hit.const_mul _) hri.integrableOn, integral_const_mul, het]
  have hrr := (setIntegral_le_integral (s := far T) hri (.of_forall (fun t ↦ sq_nonneg ‖R t‖))).trans hre
  calc
    _ ≤ (3/Real.pi)*(4*X*(2/T)+2*Real.pi*(D^2/X)) := by gcongr
    _ = _ := by field_simp; ring

/-- The actual Cauchy probability measure on critical-line ordinates as seen from two. -/
def criticalMeasure : Measure ℝ := ProbabilityTheory.cauchyMeasure 0 (3/2)

/-- Convert an energy bound for the literal density into the `L²` norm of the frequency
cutoff with respect to Mathlib's Cauchy probability measure. -/
theorem indicator_eLpNorm_le_of_energy {F : ℝ → ℂ} {S : Set ℝ} (hS : MeasurableSet S)
    (hF : Measurable F) {K : ℝ}
    (hi : IntegrableOn (fun t ↦ CayleyCauchy.density (3/2) t * ‖F t‖^2) S)
    (he : ∫ t in S, CayleyCauchy.density (3/2) t * ‖F t‖^2 ≤ K) :
    MemLp (S.indicator F) 2 criticalMeasure ∧
      eLpNorm (S.indicator F) 2 criticalMeasure ≤ ENNReal.ofReal (Real.sqrt K) := by
  let pdf := ProbabilityTheory.cauchyPDF 0 (3/2)
  have hp : Measurable pdf := ProbabilityTheory.measurable_cauchyPDF _ _
  have htop : ∀ᵐ t ∂(volume : Measure ℝ), pdf t < ∞ :=
    .of_forall (fun _ ↦ ENNReal.ofReal_lt_top)
  have hm : criticalMeasure = volume.withDensity pdf :=
    ProbabilityTheory.cauchyMeasure_of_scale_ne_zero _ (by norm_num)
  have hd (t) : (pdf t).toReal = CayleyCauchy.density (3/2) t := by
    rw [show pdf t = ENNReal.ofReal (ProbabilityTheory.cauchyPDFReal 0 (3/2) t) from rfl,
      ENNReal.toReal_ofReal (ProbabilityTheory.cauchyPDF_pos _ (by norm_num : (3/2 : ℝ≥0) ≠ 0) t).le,
      CayleyCauchy.cauchyPDFReal_zero]
    norm_num
  have hw : (fun t ↦ (pdf t).toReal • ‖S.indicator F t‖^2) =
      S.indicator (fun t ↦ CayleyCauchy.density (3/2) t * ‖F t‖^2) := by
    funext t
    by_cases ht : t ∈ S <;> simp [Set.indicator, ht, hd, smul_eq_mul]
  have hmem : MemLp (S.indicator F) 2 criticalMeasure := by
    apply (memLp_two_iff_integrable_sq_norm (hF.indicator hS).aestronglyMeasurable).mpr
    rw [hm, integrable_withDensity_iff_integrable_smul' hp htop, hw]
    exact (integrable_indicator_iff hS).mpr hi
  have heq : ∫ t, ‖S.indicator F t‖^2 ∂criticalMeasure =
      ∫ t in S, CayleyCauchy.density (3/2) t * ‖F t‖^2 := by
    rw [hm, integral_withDensity_eq_integral_toReal_smul hp htop, hw, integral_indicator hS]
  refine ⟨hmem, ?_⟩
  rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, heq, ← one_div, ← Real.sqrt_eq_rpow]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt he)

end RiemannMasullo.CriticalMellinTail
