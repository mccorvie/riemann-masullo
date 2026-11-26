module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import RiemannMasullo.ForMathlib.Analysis.Complex.HalfPlaneJensen
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic

/-! # Abel bounds for the primitive quartic character modulo five -/

@[expose] public noncomputable section

open Complex Asymptotics Filter Function Finset MeasureTheory Set
open scoped Topology

namespace RiemannMasullo.QuarticFive
open HalfPlaneJensen

/-- Values on the five residues, with the generator two mapped to the imaginary unit. -/
def raw (t : ZMod 5) : ℂ :=
  if t=0 then 0 else if t=1 then 1 else if t=2 then I else if t=3 then -I else -1

/-- The primitive odd quartic character modulo five with the chosen value `χ(2)=i`. -/
def character : DirichletCharacter ℂ 5 where
  toFun := raw
  map_one' := rfl
  map_mul' a b := by
    fin_cases a <;> fin_cases b
    · change (0 : ℂ) = 0 * 0; simp
    · change (0 : ℂ) = 0 * 1; simp
    · change (0 : ℂ) = 0 * I; simp
    · change (0 : ℂ) = 0 * (-I); simp
    · change (0 : ℂ) = 0 * (-1); simp
    · change (0 : ℂ) = 1 * 0; simp
    · change (1 : ℂ) = 1 * 1; simp
    · change (I : ℂ) = 1 * I; simp
    · change ((-I) : ℂ) = 1 * (-I); simp
    · change ((-1) : ℂ) = 1 * (-1); simp
    · change (0 : ℂ) = I * 0; simp
    · change (I : ℂ) = I * 1; simp
    · change ((-1) : ℂ) = I * I; simp [I_mul_I]
    · change (1 : ℂ) = I * (-I); simp [I_mul_I]
    · change ((-I) : ℂ) = I * (-1); simp
    · change (0 : ℂ) = (-I) * 0; simp
    · change ((-I) : ℂ) = (-I) * 1; simp
    · change (1 : ℂ) = (-I) * I; simp [I_mul_I]
    · change ((-1) : ℂ) = (-I) * (-I); simp [I_mul_I]
    · change (I : ℂ) = (-I) * (-1); simp
    · change (0 : ℂ) = (-1) * 0; simp
    · change ((-1) : ℂ) = (-1) * 1; simp
    · change ((-I) : ℂ) = (-1) * I; simp
    · change (I : ℂ) = (-1) * (-I); simp
    · change (1 : ℂ) = (-1) * (-1); simp
  map_nonunit' a ha := by
    fin_cases a
    · rfl
    · exact (ha (show IsUnit (1:ZMod 5) from by decide)).elim
    · exact (ha (show IsUnit (2:ZMod 5) from by decide)).elim
    · exact (ha (show IsUnit (3:ZMod 5) from by decide)).elim
    · exact (ha (show IsUnit (4:ZMod 5) from by decide)).elim

@[simp] theorem character_two : character 2=I := rfl

/-- The value at two separates this character from the principal character. -/
theorem ne_one (χ : DirichletCharacter ℂ 5) (hχ : χ 2=I) : χ ≠ 1 := by
  intro h
  rw [h, MulChar.one_apply (by decide : IsUnit (2:ZMod 5))] at hχ
  simpa using congrArg Complex.re hχ

/-- A nonprincipal character of prime modulus is primitive. -/
theorem primitive (χ : DirichletCharacter ℂ 5) (hχ : χ 2=I) : χ.IsPrimitive :=
  ((Nat.prime_five.eq_one_or_self_of_dvd _ χ.conductor_dvd_level).resolve_left
    fun h ↦ ne_one χ hχ ((χ.eq_one_iff_conductor_eq_one).mpr h))

private def part (χ : DirichletCharacter ℂ 5) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod 5)

private def v (k : ZMod 5) : ℂ :=
  if k=1 ∨ k=3 then 1 else if k=2 then 1+I else 0

private theorem part_table (χ : DirichletCharacter ℂ 5) (hχ : χ 2=I) (n : ℕ) :
    part χ n = v (n : ZMod 5) := by
  have h4 : χ 4 = -1 := by
    rw [show (4 : ZMod 5)=2*2 by decide, map_mul, hχ, I_mul_I]
  have h3 : χ 3 = -I := by
    rw [show (3 : ZMod 5)=4*2 by decide, map_mul, h4, hχ, neg_one_mul]
  have h0 : χ 0=0 := χ.map_nonunit (by decide)
  have step (k : ZMod 5) : v k + χ (k+1) = v (k+1) := by
    fin_cases k
    · change 0+χ 1=1; simp
    · change 1+χ 2=1+I; rw [hχ]
    · change (1+I)+χ 3=1; rw [h3]; ring
    · change 1+χ 4=0; rw [h4]; ring
    · change 0+χ 0=0; rw [h0]; ring
  induction n with
  | zero => change part χ 0=0; simp [part]
  | succ n ih =>
    rw [part, Finset.sum_Icc_succ_top (by omega), ← part, ih, Nat.cast_succ]
    exact step _

private def center : ℂ := (1+I)/2

private theorem norm_center : ‖center‖ = Real.sqrt 2/2 := by
  have h : ‖center‖^2 = 1/2 := by
    rw [Complex.sq_norm]
    norm_num [center, Complex.normSq_apply, div_ofNat_re, div_ofNat_im]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2), Real.sqrt_nonneg 2, norm_nonneg center]

private theorem norm_part_sub (χ : DirichletCharacter ℂ 5) (hχ : χ 2=I) (n : ℕ) :
    ‖part χ n-center‖ = Real.sqrt 2/2 := by
  rw [part_table χ hχ]
  suffices h : ‖v n - center‖^2 = 1/2 by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2), Real.sqrt_nonneg 2, norm_nonneg (v n-center)]
  rw [Complex.sq_norm, Complex.normSq_apply]
  unfold v
  split_ifs <;> norm_num [center, div_ofNat_re, div_ofNat_im]

private theorem norm_part_le_two (χ : DirichletCharacter ℂ 5) (hχ : χ 2=I) (n : ℕ) :
    ‖part χ n‖ ≤ 2 := by
  have h := norm_add_le (part χ n-center) center
  rw [sub_add_cancel, norm_part_sub χ hχ, norm_center] at h
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

private def stepFn (χ : DirichletCharacter ℂ 5) (t : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator (fun u ↦ part χ ⌊u⌋₊) t

private theorem step_measurable (χ : DirichletCharacter ℂ 5) : Measurable (stepFn χ) :=
  ((measurable_of_countable (part χ)).comp Nat.measurable_floor).indicator measurableSet_Ioi

private theorem abel_eq_mellin (χ : DirichletCharacter ℂ 5) (s : ℂ) :
    mellin (stepFn χ) (-s) = ∫ t in Ioi (1:ℝ), part χ ⌊t⌋₊ * (t:ℂ)^(-(s+1)) := by
  unfold mellin
  have heq : (fun t : ℝ ↦ (t:ℂ)^(-s-1) • stepFn χ t) = (Ioi (1:ℝ)).indicator
      (fun t : ℝ ↦ part χ ⌊t⌋₊ * (t:ℂ)^(-(s+1))) := by
    funext t
    by_cases ht : t ∈ Ioi (1:ℝ) <;> simp [stepFn, ht, smul_eq_mul, neg_add_rev, sub_eq_add_neg, mul_comm, add_comm]
  rw [heq, setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))]

/-- The ordinary Dirichlet continuation equals the Abel integral throughout the right half-plane,
including the part where the Dirichlet series is conditionally convergent. -/
private theorem LFunction_abel_of_partial (χ : DirichletCharacter ℂ 5) (hn : χ ≠ 1)
    (hpart : ∀ n, ‖part χ n‖ ≤ 2) {s : ℂ} (hs : 0<s.re) :
    χ.LFunction s = s * ∫ t in Ioi (1:ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k:ZMod 5)) *
      (t:ℂ)^(-(s+1)) := by
  have hb (t : ℝ) : ‖stepFn χ t‖ ≤ 2 := by
    by_cases ht : t ∈ Ioi (1:ℝ)
    · simpa [stepFn,ht] using hpart ⌊t⌋₊
    · simp [stepFn,ht]
  have hi : LocallyIntegrableOn (stepFn χ) (Ioi 0) := by
    apply (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).mpr
    intro K _ hK
    exact IntegrableOn.of_bound hK.measure_lt_top (step_measurable χ).aestronglyMeasurable 2
      (Eventually.of_forall hb)
  have htop : stepFn χ =O[atTop] (fun t : ℝ ↦ t^(-(0:ℝ))) := by
    apply isBigO_iff.mpr
    exact ⟨2, Eventually.of_forall (fun t ↦ by simpa using hb t)⟩
  have hdiff (z : ℂ) (hz : 0<z.re) : DifferentiableAt ℂ (mellin (stepFn χ)) (-z) := by
    apply mellin_differentiableAt_of_isBigO_rpow (a:=0) (b:=(-z).re-1) hi htop (by simpa)
    · apply isBigO_iff.mpr
      refine ⟨0, ?_⟩
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ)<1 by norm_num))] with t ht
      simp [stepFn, show t ∉ Ioi (1:ℝ) by exact not_lt.mpr (le_of_lt ht)]
    · linarith
  let S := {z : ℂ | 0<z.re}
  have hS : IsOpen S := isOpen_lt continuous_const continuous_re
  have hd : DifferentiableOn ℂ (fun z : ℂ ↦ z * mellin (stepFn χ) (-z)) S :=
    fun z hz ↦ (differentiableAt_id.mul ((hdiff z hz).comp z differentiableAt_id.neg)).differentiableWithinAt
  have hsum : (fun n ↦ part χ n) =O[atTop] (fun n : ℕ ↦ (n:ℝ)^(0:ℝ)) := by
    exact isBigO_iff.mpr ⟨2, Eventually.of_forall (fun n ↦ by simpa using hpart n)⟩
  have hg : χ.LFunction =ᶠ[𝓝 (2:ℂ)] (fun z : ℂ ↦ z * mellin (stepFn χ) (-z)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (show (1:ℝ)<(2:ℂ).re by norm_num)] with z hz
    change 1<z.re at hz
    rw [χ.LFunction_eq_LSeries hz, abel_eq_mellin]
    exact LSeries_eq_mul_integral _ (r:=0) le_rfl (lt_trans zero_lt_one hz)
      (χ.LSeriesSummable_of_one_lt_re hz) hsum
  have heq := ((DirichletCharacter.differentiable_LFunction hn).differentiableOn.analyticOnNhd hS).eqOn_of_preconnected_of_eventuallyEq
    (hd.analyticOnNhd hS) (convex_halfSpace_re_gt 0).isPreconnected (show (2:ℂ)∈S by dsimp [S]; norm_num) hg
  simpa only [abel_eq_mellin, part] using heq (show s∈S from hs)

/-- Abel summation for the actual conductor-five quartic character. -/
theorem LFunction_abel (χ : DirichletCharacter ℂ 5) (hχ : χ 2=I) {s : ℂ} (hs : 0<s.re) :
    χ.LFunction s = s * ∫ t in Ioi (1:ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k:ZMod 5)) *
      (t:ℂ)^(-(s+1)) := LFunction_abel_of_partial χ (ne_one χ hχ) (norm_part_le_two χ hχ) hs

private def kern (s : ℂ) (t : ℝ) : ℂ := (t:ℂ)^(-(s+1))

private theorem kern_norm {s : ℂ} {t : ℝ} (ht : 0<t) : ‖kern s t‖ = t^(-(s.re+1)) := by
  rw [kern, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp

private theorem part_integrable (χ : DirichletCharacter ℂ 5) (hχ : χ 2=I)
    {s : ℂ} (hs : 0<s.re) (c : ℂ) :
    IntegrableOn (fun t : ℝ ↦ (part χ ⌊t⌋₊-c)*kern s t) (Ioi 1) := by
  have hpow := integrableOn_Ioi_rpow_of_lt (by linarith : -(s.re+1)< -1) (by norm_num : (0:ℝ)<1)
  refine (hpow.const_mul (2+‖c‖)).mono' ?_ ?_
  · have hm : Measurable (fun t : ℝ ↦ part χ ⌊t⌋₊) := (measurable_of_countable (part χ)).comp Nat.measurable_floor
    have hmk : Measurable (kern s) := by unfold kern; fun_prop
    exact ((hm.sub measurable_const).mul hmk).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
    change ‖(part χ ⌊t⌋₊-c)*kern s t‖ ≤ (2+‖c‖)*t^(-(s.re+1))
    rw [norm_mul, kern_norm (zero_lt_one.trans ht)]
    exact mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans
      (add_le_add (norm_part_le_two χ hχ _) le_rfl)) (Real.rpow_nonneg (zero_le_one.trans ht.le) _)

private theorem centered_integral_bound (χ : DirichletCharacter ℂ 5) (hχ : χ 2=I)
    {s : ℂ} (hs : 0<s.re) :
    ‖∫ t in Ioi (1:ℝ), (part χ ⌊t⌋₊-center)*kern s t‖ ≤ (Real.sqrt 2/2)/s.re := by
  calc
    _ ≤ ∫ t in Ioi (1:ℝ), ‖(part χ ⌊t⌋₊-center)*kern s t‖ := norm_integral_le_integral_norm _
    _ = ∫ t in Ioi (1:ℝ), (Real.sqrt 2/2)*t^(-(s.re+1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change ‖(part χ ⌊t⌋₊-center)*kern s t‖ = _
      rw [norm_mul, norm_part_sub χ hχ, kern_norm (zero_lt_one.trans ht)]
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
      rw [show -(s.re+1)+1= -s.re by ring]
      field_simp [hs.ne']

private theorem centered_rep (χ : DirichletCharacter ℂ 5) (hχ : χ 2=I) {s : ℂ} (hs : 0<s.re) :
    χ.LFunction s = center + s * ∫ t in Ioi (1:ℝ), (part χ ⌊t⌋₊-center)*kern s t := by
  have hcp : (-(s+1)).re < -1 := by simp; linarith
  have hs0 : s≠0 := fun h ↦ by simp [h] at hs
  have hk : IntegrableOn (kern s) (Ioi 1) := integrableOn_Ioi_cpow_of_lt hcp zero_lt_one
  have he : ∫ t in Ioi (1:ℝ), center*kern s t = center/s := by
    rw [integral_const_mul]
    change center * (∫ t in Ioi (1:ℝ), (t:ℂ)^(-(s+1)))=center/s
    rw [integral_Ioi_cpow_of_lt hcp zero_lt_one]
    simp only [ofReal_one, one_cpow]
    rw [show -(s+1)+1= -s by ring]
    field_simp
  rw [LFunction_abel χ hχ hs]
  change s*(∫ t in Ioi (1:ℝ), part χ ⌊t⌋₊*kern s t) = _
  have hh : (fun t : ℝ ↦ part χ ⌊t⌋₊*kern s t) =
      (fun t : ℝ ↦ center*kern s t + (part χ ⌊t⌋₊-center)*kern s t) := by funext; ring
  rw [hh, integral_add (hk.const_mul _) (part_integrable χ hχ hs _), he]
  field_simp

private theorem chart_norm_bound {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (Real.sqrt 2/2)*(‖1-z‖ + 2*‖2+z‖) ≤ 9/2 := by
  have h1 : 2*‖1-z‖^2+‖2+z‖^2=6+3*‖z‖^2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, add_re, add_im,
      one_re, one_im, show (2:ℂ).re=2 by rfl, show (2:ℂ).im=0 by rfl]
    ring
  have h2 : ‖z‖^2 ≤ 1 := by simpa using pow_le_pow_left₀ (norm_nonneg z) hz 2
  have h3 : (‖1-z‖+2*‖2+z‖)^2 ≤ 81/2 := by nlinarith [sq_nonneg (4*‖1-z‖-‖2+z‖)]
  have h4 : ((Real.sqrt 2/2)*(‖1-z‖+2*‖2+z‖))^2 ≤ (9/2:ℝ)^2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num)]
    nlinarith
  nlinarith [sq_nonneg ((Real.sqrt 2/2)*(‖1-z‖+2*‖2+z‖)-9/2)]

/-- The actual conductor-five ordinary Dirichlet function obeys the normalized disk
bound `9/2` from its centered periodic partial sums. -/
theorem norm_one_sub_mul_LFunction_le (χ : DirichletCharacter ℂ 5) (hχ : χ 2=I)
    {z : ℂ} (hz : ‖z‖<1) : ‖(1-z)*χ.LFunction (toHalf z)‖ ≤ 9/2 := by
  let s := toHalf z
  have hσ : 1/2 < s.re := toHalf_re hz
  have hs : 0<s.re := by linarith
  let J := ∫ t in Ioi (1:ℝ), (part χ ⌊t⌋₊-center)*kern s t
  have hj : ‖J‖ ≤ Real.sqrt 2/2/s.re := centered_integral_bound χ hχ hs
  have hj' : ‖J‖ ≤ 2*(Real.sqrt 2/2) := hj.trans ((div_le_iff₀ hs).mpr
    (by nlinarith [Real.sqrt_nonneg 2, mul_nonneg (Real.sqrt_nonneg 2) (sub_nonneg.mpr hσ.le)]))
  have hid : (1-z)*s = 2+z := by dsimp [s,toHalf]; field_simp [half_den hz]
  have hr : (1-z)*χ.LFunction (toHalf z) = (1-z)*center + (2+z)*J := by
    change (1-z)*χ.LFunction s=_
    rw [centered_rep χ hχ hs, mul_add, ← mul_assoc, hid]
  rw [hr]
  calc
    _ ≤ ‖(1-z)*center‖+‖(2+z)*J‖ := norm_add_le _ _
    _ ≤ (Real.sqrt 2/2)*(‖1-z‖+2*‖2+z‖) := by
      rw [norm_mul, norm_mul, norm_center]
      nlinarith [mul_le_mul_of_nonneg_left hj' (norm_nonneg (2+z))]
    _ ≤ _ := chart_norm_bound hz.le

private theorem part_re_nonneg (χ : DirichletCharacter ℂ 5) (hχ : χ 2=I) (n : ℕ) :
    0 ≤ (part χ n).re := by
  rw [part_table χ hχ]
  unfold v
  split_ifs <;> norm_num

private theorem part_re_one (χ : DirichletCharacter ℂ 5) (hχ : χ 2=I) (t : ℝ)
    (ht : t ∈ Ioo (1:ℝ) 4) : (part χ ⌊t⌋₊).re=1 := by
  rw [part_table χ hχ]
  have ht1 : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by simpa using ht.1.le)
  have ht4 : ⌊t⌋₊ < 4 := (Nat.floor_lt (by linarith [ht.1])).mpr (by simpa using ht.2)
  generalize h : ⌊t⌋₊=n at *
  interval_cases n
  · change (1:ℂ).re=1; rfl
  · change (1+I).re=1; simp
  · change (1:ℂ).re=1; rfl

/-- Every positive real argument has a strictly positive real part. The initial interval on
which the real partial sums equal one gives the explicit lower bound `1-4^(-r)`. -/
theorem real_part_lower (χ : DirichletCharacter ℂ 5) (hχ : χ 2=I) {r : ℝ} (hr : 0<r) :
    1-(4:ℝ)^(-r) ≤ (χ.LFunction (r:ℂ)).re := by
  let k (t : ℝ) := (part χ ⌊t⌋₊ * kern r t).re
  have hi : IntegrableOn (fun t : ℝ ↦ part χ ⌊t⌋₊ * kern r t) (Ioi 1) := by
    simpa using part_integrable χ hχ (s:=(r:ℂ)) hr 0
  have hRe : (χ.LFunction (r:ℂ)).re = r*∫ t in Ioi (1:ℝ), k t := by
    rw [LFunction_abel χ hχ (s:=(r:ℂ)) hr]
    change ((r:ℂ)*(∫ t in Ioi (1:ℝ), part χ ⌊t⌋₊ * kern r t)).re=_
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    congr 1
    exact (integral_re hi).symm
  have hk (t : ℝ) (ht : 0<t) : k t = (part χ ⌊t⌋₊).re*t^(-(r+1)) := by
    have hpow : kern r t = ((t^(-(r+1)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow ht.le]
      simp [kern]
    simp only [k, hpow, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  have hpos : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 1), 0 ≤ k t := by
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with t ht
    rw [hk t (zero_lt_one.trans ht)]
    exact mul_nonneg (part_re_nonneg χ hχ _) (Real.rpow_nonneg (zero_le_one.trans ht.le) _)
  have hbound := setIntegral_mono_set (f:=k) (s:=Ioo (1:ℝ) 4) (t:=Ioi 1) hi.re hpos
    (Eventually.of_forall fun x hx ↦ hx.1)
  have heq : ∫ t in Ioo (1:ℝ) 4, k t = (1-(4:ℝ)^(-r))/r := by
    calc
      _ = ∫ t in Ioo (1:ℝ) 4, t^(-(r+1)) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro t ht
        rw [hk t (zero_lt_one.trans ht.1), part_re_one χ hχ t ht, one_mul]
      _ = _ := by
        rw [← integral_Ioc_eq_integral_Ioo' (by simp),
          ← intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤4),
          integral_rpow (Or.inr ⟨by linarith, by norm_num [Set.uIcc]⟩),
          show -(r+1)+1 = -r by ring, Real.one_rpow]
        ring
  rw [heq] at hbound
  rw [hRe, mul_comm]
  exact (div_le_iff₀ hr).mp hbound

theorem real_part_pos (χ : DirichletCharacter ℂ 5) (hχ : χ 2=I) {r : ℝ} (hr : 0<r) :
    0 < (χ.LFunction (r:ℂ)).re :=
  (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ)<4) (neg_lt_zero.mpr hr))).trans_le
    (real_part_lower χ hχ hr)

theorem center_lower (χ : DirichletCharacter ℂ 5) (hχ : χ 2=I) :
    15/16 ≤ ‖χ.LFunction 2‖ := by
  have h := real_part_lower χ hχ (by norm_num : (0:ℝ)<2)
  norm_num at h
  exact h.trans (Complex.re_le_norm _)

/-- Reflection to the inverse character for the actual ordinary Dirichlet continuation on
the whole right half-plane. This permits a positive-height result for each character to
control both signs for one fixed nonreal character. -/
theorem inverse_LFunction_conj (χ : DirichletCharacter ℂ 5) (hχ : χ 2=I)
    {s : ℂ} (hs : 0<s.re) : (χ⁻¹).LFunction ((starRingEnd ℂ) s) = (starRingEnd ℂ) (χ.LFunction s) := by
  classical
  have hp (n : ℕ) : part χ⁻¹ n = (starRingEnd ℂ) (part χ n) := by
    rw [part, part, map_sum]
    exact sum_congr rfl (fun i _ ↦ (MulChar.star_apply' χ (i : ZMod 5)).symm)
  have ha : ∀ n, ‖part χ⁻¹ n‖ ≤ 2 := fun n ↦ by simpa [hp] using norm_part_le_two χ hχ n
  have hi : χ⁻¹ ≠ 1 := fun h ↦ ne_one χ hχ (inv_eq_one.mp h)
  rw [LFunction_abel_of_partial χ⁻¹ hi ha (show 0<((starRingEnd ℂ) s).re from hs),
    LFunction_abel χ hχ hs, map_mul, ← integral_conj]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change part χ⁻¹ ⌊t⌋₊ * (t:ℂ)^(-((starRingEnd ℂ) s+1)) =
    (starRingEnd ℂ) (part χ ⌊t⌋₊ * (t:ℂ)^(-(s+1)))
  rw [hp, map_mul]
  congr 1
  have harg : (t:ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (zero_le_one.trans ht.le)]
    exact Real.pi_ne_zero.symm
  have h := (Complex.cpow_conj (t:ℂ) (-(s+1)) harg)
  simpa only [map_neg, map_add, map_one, Complex.conj_ofReal] using h

end RiemannMasullo.QuarticFive
