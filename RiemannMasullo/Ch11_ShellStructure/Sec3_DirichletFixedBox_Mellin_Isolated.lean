module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_DirichletFixedBox_Bounds_Isolated
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Nontrivial primitive Dirichlet characters in fixed Fourier boxes (Mellin)

Twisted half-logarithmic profiles and Mellin transforms for primitive `χ`.

Nothing outside the `Sec3_DirichletFixedBox*` / `Sec3_RatBridge*` isolated stack imports this module.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField RiemannMasullo Set Topology
open scoped BigOperators ContDiff FourierTransform NNReal Real SchwartzMap

namespace RiemannMasullo.Isolated

section MellinAndStripRows

private theorem dirichletChar_zero_of_one_lt {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hN : 1 < N) : χ (0 : ZMod N) = 0 := by
  apply MulChar.map_nonunit
  rintro ⟨u, hu⟩
  have h1 : (u : ZMod N) * (u⁻¹ : (ZMod N)ˣ) = 1 := u.mul_inv
  have hne : (1 : ZMod N) ≠ 0 := by
    have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.mpr (by omega)
    exact one_ne_zero
  rw [hu, zero_mul] at h1
  exact hne h1.symm

theorem twistedRadialTheta_term_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hN : 1 < N) (f : 𝓢(ℝ, ℂ)) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C₀ > (0 : ℝ), ∀ (m : ℤ) (x : ℝ),
      ‖χ (m : ZMod N) * f (m * Real.exp x)‖ ≤
        C₀ * |(m : ℝ)| ^ (-(k : ℝ)) * Real.exp (-(k : ℝ) * x) := by
  obtain ⟨C₀, hC₀, hdec⟩ := f.decay k 0
  refine ⟨C₀, hC₀, fun m x ↦ ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [Int.cast_zero, zero_mul, abs_zero, dirichletChar_zero_of_one_lt χ hN,
      norm_zero, zero_mul]
    rw [Real.zero_rpow (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega)))]
    simp
  · have hm_pos : (0 : ℝ) < |(m : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hm)
    have hexp_pos : 0 < Real.exp x := Real.exp_pos x
    have hprod_pos : (0 : ℝ) < |(m : ℝ)| * Real.exp x := mul_pos hm_pos hexp_pos
    have hpow_pos : (0 : ℝ) < (|(m : ℝ)| * Real.exp x) ^ k := pow_pos hprod_pos k
    have hdec_mx := hdec ((m : ℝ) * Real.exp x)
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_mul, abs_of_pos hexp_pos] at hdec_mx
    have hf_le : ‖f ((m : ℝ) * Real.exp x)‖ ≤ C₀ * ((|(m : ℝ)| * Real.exp x) ^ k)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpow_pos]
      linarith
    have hpow_eq : ((|(m : ℝ)| * Real.exp x) ^ k)⁻¹ =
        |(m : ℝ)| ^ (-(k : ℝ)) * Real.exp (-(k : ℝ) * x) := by
      rw [mul_pow, mul_inv, ← Real.rpow_natCast |(m : ℝ)| k,
        ← Real.rpow_neg hm_pos.le (k : ℝ), ← Real.exp_nat_mul, ← Real.exp_neg, neg_mul]
    calc ‖χ (m : ZMod N) * f ((m : ℝ) * Real.exp x)‖
        = ‖χ (m : ZMod N)‖ * ‖f ((m : ℝ) * Real.exp x)‖ := norm_mul _ _
      _ ≤ 1 * ‖f ((m : ℝ) * Real.exp x)‖ :=
          mul_le_mul_of_nonneg_right (norm_dirichletChar_le_one χ m) (norm_nonneg _)
      _ = ‖f ((m : ℝ) * Real.exp x)‖ := one_mul _
      _ ≤ C₀ * ((|(m : ℝ)| * Real.exp x) ^ k)⁻¹ := hf_le
      _ = C₀ * |(m : ℝ)| ^ (-(k : ℝ)) * Real.exp (-(k : ℝ) * x) := by
          rw [hpow_eq, mul_assoc]

/-- For a nontrivial character (`1 < N`), `twistedHalfLogProfile χ f` is continuous on `ℝ`. -/
theorem twistedHalfLogProfile_continuous {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hN : 1 < N) (f : 𝓢(ℝ, ℂ)) :
    Continuous (twistedHalfLogProfile χ f) := by
  refine continuous_iff_continuousAt.mpr fun x₀ ↦ ?_
  let B : ℝ := x₀ - 1
  have hBmem : Set.Ici B ∈ 𝓝 x₀ := Ici_mem_nhds (by linarith)
  obtain ⟨C₀, hC₀, hbd⟩ := twistedRadialTheta_term_bound χ hN f 2 (by decide)
  have hu : Summable (fun m : ℤ ↦ C₀ * |(m : ℝ)| ^ (-(2 : ℝ)) * Real.exp (-(2 : ℝ) * B)) :=
    ((Real.summable_abs_int_rpow one_lt_two).mul_left C₀).mul_right _
  have hcont_on : ContinuousOn
      (fun x : ℝ ↦ ∑' m : ℤ, χ (m : ZMod N) * f (m * Real.exp x)) (Set.Ici B) := by
    refine continuousOn_tsum (u := fun m : ℤ ↦ C₀ * |(m : ℝ)| ^ (-(2 : ℝ)) * Real.exp (-(2 : ℝ) * B))
      (fun m ↦ Continuous.continuousOn ?_) hu fun m x hx ↦ ?_
    · exact continuous_const.mul (f.continuous.comp (continuous_const.mul Real.continuous_exp))
    · refine (hbd m x).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      simp only [Nat.cast_ofNat]
      exact Real.exp_le_exp.mpr (by linarith [Set.mem_Ici.mp hx])
  have hcont_at : ContinuousAt
      (fun x : ℝ ↦ ∑' m : ℤ, χ (m : ZMod N) * f (m * Real.exp x)) x₀ :=
    hcont_on.continuousAt hBmem
  have hexp : ContinuousAt (fun x : ℝ ↦ (Real.exp (x / 2) : ℂ)) x₀ :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_id.div_const 2))).continuousAt
  exact hexp.mul hcont_at

/-- For any Schwartz function `f` and `1 < N`, `twistedHalfLogProfile χ f` decays faster than
any exponential `exp (-M * x)` on `[B, ∞)`.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem twistedHalfLogProfile_decay {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hN : 1 < N) (f : 𝓢(ℝ, ℂ)) (B M : ℝ) :
    ∃ C ≥ (0 : ℝ), ∀ x ≥ B, ‖twistedHalfLogProfile χ f x‖ ≤ C * Real.exp (-M * x) := by
  let k : ℕ := max 2 (Nat.ceil (|M| + 1))
  have hk2 : 2 ≤ k := le_max_left _ _
  have hk1 : 1 ≤ k := le_trans (by decide) hk2
  have hkM : |M| + 1 ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 2 (Nat.ceil (|M| + 1)))
  have hslope : 1 / 2 - (k : ℝ) + M ≤ 0 := by linarith [le_abs_self M]
  obtain ⟨C₀, hC₀, hbd⟩ := twistedRadialTheta_term_bound χ hN f k hk1
  have hsum_k : Summable (fun m : ℤ ↦ |(m : ℝ)| ^ (-(k : ℝ))) :=
    Real.summable_abs_int_rpow (one_lt_two.trans_le (by exact_mod_cast hk2))
  let S : ℝ := ∑' m : ℤ, |(m : ℝ)| ^ (-(k : ℝ))
  have hS0 : 0 ≤ S := tsum_nonneg fun m ↦ Real.rpow_nonneg (abs_nonneg _) _
  refine ⟨C₀ * S * Real.exp ((1 / 2 - (k : ℝ) + M) * B), by positivity, fun x hx ↦ ?_⟩
  have htsum_bd : ‖∑' m : ℤ, χ (m : ZMod N) * f (m * Real.exp x)‖ ≤
      C₀ * S * Real.exp (-(k : ℝ) * x) := by
    have hsum_bd : Summable (fun m : ℤ ↦ C₀ * |(m : ℝ)| ^ (-(k : ℝ)) * Real.exp (-(k : ℝ) * x)) :=
      (hsum_k.mul_left C₀).mul_right _
    calc ‖∑' m : ℤ, χ (m : ZMod N) * f (m * Real.exp x)‖
        ≤ ∑' m : ℤ, ‖χ (m : ZMod N) * f (m * Real.exp x)‖ :=
          norm_tsum_le_tsum_norm (hsum_bd.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun m ↦ hbd m x))
      _ ≤ ∑' m : ℤ, C₀ * |(m : ℝ)| ^ (-(k : ℝ)) * Real.exp (-(k : ℝ) * x) :=
          Summable.tsum_le_tsum (fun m ↦ hbd m x)
            (hsum_bd.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun m ↦ hbd m x)) hsum_bd
      _ = C₀ * S * Real.exp (-(k : ℝ) * x) := by
          rw [tsum_mul_right, tsum_mul_left]
  calc ‖twistedHalfLogProfile χ f x‖
      = Real.exp (x / 2) * ‖∑' m : ℤ, χ (m : ZMod N) * f (m * Real.exp x)‖ := by
        rw [twistedHalfLogProfile, twistedRadialTheta, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    _ ≤ Real.exp (x / 2) * (C₀ * S * Real.exp (-(k : ℝ) * x)) :=
        mul_le_mul_of_nonneg_left htsum_bd (Real.exp_pos _).le
    _ = C₀ * S * (Real.exp ((1 / 2 - (k : ℝ) + M) * x) * Real.exp (-M * x)) := by
        rw [← Real.exp_add, show (1 / 2 - (k : ℝ) + M) * x + (-M * x) = x / 2 + -(k : ℝ) * x by ring,
          Real.exp_add]
        ring
    _ ≤ C₀ * S * (Real.exp ((1 / 2 - (k : ℝ) + M) * B) * Real.exp (-M * x)) := by
        have hexp_le : Real.exp ((1 / 2 - (k : ℝ) + M) * x) ≤ Real.exp ((1 / 2 - (k : ℝ) + M) * B) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hx hslope)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp_le (Real.exp_pos _).le) (by positivity)
    _ = (C₀ * S * Real.exp ((1 / 2 - (k : ℝ) + M) * B)) * Real.exp (-M * x) := by ring

/-- Rapidly decaying continuous functions supported on `[B, ∞)`. -/
def IsHalfLineRapid (U : ℝ → ℂ) : Prop :=
  Continuous U ∧ ∃ B : ℝ, (∀ x < B, U x = 0) ∧
    ∀ M : ℝ, ∃ C ≥ (0 : ℝ), ∀ x ≥ B, ‖U x‖ ≤ C * Real.exp (-M * x)

theorem isHalfLineRapid_twistedHalfLogProfile {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    {X : ℝ} (hX : 0 < X) {f : 𝓢(ℝ, ℂ)} (hf : IsDirichletFixedBoxTest χ X f) :
    IsHalfLineRapid (twistedHalfLogProfile χ f) :=
  ⟨twistedHalfLogProfile_continuous χ hN f, -Real.log ((N : ℝ) * X),
    fun _ hx ↦ dirichletFixedBox_support_lower_bound hχ hN hX hf hx,
    fun M ↦ twistedHalfLogProfile_decay χ hN f (-Real.log ((N : ℝ) * X)) M⟩

private theorem isHalfLineRapid_halfTwistLogDilate {q : ℕ} (hq : 0 < q)
    {U : ℝ → ℂ} (hU : IsHalfLineRapid U) :
    IsHalfLineRapid (halfTwistLogDilate q U) := by
  obtain ⟨hcont, B, hsupp, hdec⟩ := hU
  have hcont' : Continuous (halfTwistLogDilate q U) := by
    have : (halfTwistLogDilate q U : ℝ → ℂ) =
        fun x ↦ ((q : ℂ) ^ (-(1 / 2 : ℂ))) * U (x + Real.log q) := by
      ext x
      simp [halfTwistLogDilate, hq.ne']
    rw [this]
    exact continuous_const.mul (hcont.comp (continuous_id.add continuous_const))
  refine ⟨hcont', B - Real.log q, fun x hx ↦ ?_, fun M ↦ ?_⟩
  · simp only [halfTwistLogDilate, hq.ne', ↓reduceIte, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hsupp (x + Real.log q) (by linarith), mul_zero]
  · obtain ⟨C, hC, hbd⟩ := hdec M
    refine ⟨‖(q : ℂ) ^ (-(1 / 2 : ℂ))‖ * C * Real.exp (-M * Real.log q), by positivity, fun x hx ↦ ?_⟩
    simp only [halfTwistLogDilate, hq.ne', ↓reduceIte, LinearMap.coe_mk, AddHom.coe_mk, norm_mul]
    calc ‖(q : ℂ) ^ (-(1 / 2 : ℂ))‖ * ‖U (x + Real.log q)‖
        ≤ ‖(q : ℂ) ^ (-(1 / 2 : ℂ))‖ * (C * Real.exp (-M * (x + Real.log q))) :=
          mul_le_mul_of_nonneg_left (hbd (x + Real.log q) (by linarith)) (norm_nonneg _)
      _ = (‖(q : ℂ) ^ (-(1 / 2 : ℂ))‖ * C * Real.exp (-M * Real.log q)) * Real.exp (-M * x) := by
          rw [mul_add, Real.exp_add]
          ring

private theorem isHalfLineRapid_sub {U V : ℝ → ℂ}
    (hU : IsHalfLineRapid U) (hV : IsHalfLineRapid V) :
    IsHalfLineRapid (U - V) := by
  obtain ⟨hcU, BU, hsU, hdU⟩ := hU
  obtain ⟨hcV, BV, hsV, hdV⟩ := hV
  refine ⟨hcU.sub hcV, min BU BV, fun x hx ↦ ?_, fun M ↦ ?_⟩
  · simp [hsU x (lt_of_lt_of_le hx (min_le_left _ _)),
      hsV x (lt_of_lt_of_le hx (min_le_right _ _))]
  · obtain ⟨CU, hCU, hbdU⟩ := hdU M
    obtain ⟨CV, hCV, hbdV⟩ := hdV M
    let CminU : ℝ := ∑ x ∈ ∅, x -- dummy avoided below
    -- On `[min BU BV, BU)`, `U = 0`; on `[min BU BV, BV)`, `V = 0`!
    refine ⟨CU + CV, by positivity, fun x _ ↦ ?_⟩
    have hUx : ‖U x‖ ≤ CU * Real.exp (-M * x) := by
      by_cases hxU : x < BU
      · rw [hsU x hxU, norm_zero]
        positivity
      · exact hbdU x (le_of_not_gt hxU)
    have hVx : ‖V x‖ ≤ CV * Real.exp (-M * x) := by
      by_cases hxV : x < BV
      · rw [hsV x hxV, norm_zero]
        positivity
      · exact hbdV x (le_of_not_gt hxV)
    calc ‖(U - V) x‖ = ‖U x - V x‖ := rfl
      _ ≤ ‖U x‖ + ‖V x‖ := norm_sub_le _ _
      _ ≤ CU * Real.exp (-M * x) + CV * Real.exp (-M * x) := add_le_add hUx hVx
      _ = (CU + CV) * Real.exp (-M * x) := (add_mul _ _ _).symm

private theorem isHalfLineRapid_smul (c : ℂ) {U : ℝ → ℂ} (hU : IsHalfLineRapid U) :
    IsHalfLineRapid (c • U) := by
  obtain ⟨hcU, B, hs, hd⟩ := hU
  refine ⟨continuous_const.mul hcU, B, fun x hx ↦ ?_, fun M ↦ ?_⟩
  · simp [hs x hx]
  · obtain ⟨C, hC, hbd⟩ := hd M
    refine ⟨‖c‖ * C, by positivity, fun x hx ↦ ?_⟩
    calc ‖(c • U) x‖ = ‖c‖ * ‖U x‖ := norm_mul c (U x)
      _ ≤ ‖c‖ * (C * Real.exp (-M * x)) := mul_le_mul_of_nonneg_left (hbd x hx) (norm_nonneg _)
      _ = (‖c‖ * C) * Real.exp (-M * x) := (mul_assoc _ _ _).symm

private theorem isHalfLineRapid_depleteStepFun {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {q : ℕ} (hq : 0 < q)
    {U : ℝ → ℂ} (hU : IsHalfLineRapid U) :
    IsHalfLineRapid (depleteStepFun χ q U) :=
  isHalfLineRapid_sub hU (isHalfLineRapid_smul _ (isHalfLineRapid_halfTwistLogDilate hq hU))

theorem isHalfLineRapid_dirichletDeplete {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : Finset ℕ) (hT : ∀ q ∈ T, 0 < q)
    {U : ℝ → ℂ} (hU : IsHalfLineRapid U) :
    IsHalfLineRapid (dirichletDeplete χ T U) := by
  induction T using Finset.induction_on with
  | empty => simpa using hU
  | insert q S hqS ih =>
    rw [dirichletDeplete_insert χ hqS, LinearMap.comp_apply]
    exact isHalfLineRapid_depleteStepFun χ (hT q (Finset.mem_insert_self q S))
      (ih fun r hr ↦ hT r (Finset.mem_insert_of_mem hr))

private theorem integrable_poly_mul_isHalfLineRapid {U : ℝ → ℂ} (hU : IsHalfLineRapid U)
    (k : ℕ) (w : ℂ) :
    Integrable (fun x : ℝ ↦ (x : ℂ) ^ k * U x * Complex.exp (w * (x : ℂ))) volume := by
  obtain ⟨hcont, B, hsupp, hdec⟩ := hU
  let M : ℝ := w.re + 3
  obtain ⟨C, hC, hbd⟩ := hdec M
  let C' : ℝ := C * (k.factorial : ℝ) * Real.exp (2 * |B| - B)
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ ↦ (x : ℂ) ^ k * U x * Complex.exp (w * (x : ℂ))) volume :=
    ((continuous_ofReal.pow k).mul hcont |>.mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
  have hbound_int : Integrable (fun x : ℝ ↦ Set.indicator (Set.Ici B) (fun x : ℝ ↦ C' * Real.exp (-x)) x) volume :=
    IntegrableOn.integrable_indicator
      ((integrableOn_Ici_iff_integrableOn_Ioi (f := fun x : ℝ ↦ Real.exp (-x))).mpr
        (integrableOn_exp_neg_Ioi B) |>.const_mul C')
      measurableSet_Ici
  refine hbound_int.mono' hmeas (Filter.Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x < B
  · rw [hsupp x hx]
    simp only [mul_zero, zero_mul, norm_zero]
    exact Set.indicator_nonneg (fun _ _ ↦ by positivity) x
  · have hxB : B ≤ x := le_of_not_gt hx
    rw [Set.indicator_of_mem hxB, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp, mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hpow_exp : |x| ^ k ≤ (k.factorial : ℝ) * Real.exp |x| := by
      have hkpos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
      have h := Real.pow_div_factorial_le_exp |x| (abs_nonneg x) k
      exact ((div_le_iff₀ hkpos).mp h).trans_eq (mul_comm _ _)
    have hexp_abs : |x| ≤ x + 2 * |B| := by
      rcases le_total 0 x with hx0 | hx0
      · rw [abs_of_nonneg hx0]
        linarith [abs_nonneg B]
      · rw [abs_of_nonpos hx0]
        linarith [neg_le_abs B]
    have hexp_tail : Real.exp ((1 - M + w.re) * x) ≤ Real.exp (-B) * Real.exp (-x) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      dsimp [M]
      linarith
    have hexp_split : Real.exp (x + 2 * |B|) * Real.exp (-M * x) * Real.exp (w.re * x) =
        Real.exp (2 * |B|) * Real.exp ((1 - M + w.re) * x) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc |x| ^ k * ‖U x‖ * Real.exp (w.re * x)
        ≤ ((k.factorial : ℝ) * Real.exp |x|) * (C * Real.exp (-M * x)) * Real.exp (w.re * x) := by
          gcongr
          exact hbd x hxB
      _ ≤ ((k.factorial : ℝ) * Real.exp (x + 2 * |B|)) * (C * Real.exp (-M * x)) * Real.exp (w.re * x) := by
          gcongr
      _ = C * (k.factorial : ℝ) * (Real.exp (x + 2 * |B|) * Real.exp (-M * x) * Real.exp (w.re * x)) := by
          ring
      _ = C * (k.factorial : ℝ) * Real.exp (2 * |B|) * Real.exp ((1 - M + w.re) * x) := by
          rw [hexp_split]
          ring
      _ ≤ C * (k.factorial : ℝ) * Real.exp (2 * |B|) * (Real.exp (-B) * Real.exp (-x)) := by
          gcongr
      _ = C' * Real.exp (-x) := by
          dsimp [C']
          rw [sub_eq_add_neg (2 * |B|) B, Real.exp_add]
          ring

/-- Logarithmic Fourier profile `M(f̂)(z) = ∫ y, (𝓕 f)(exp y) * exp ((1 - z) * y) dy`.
At imaginary axis points `z = i t`, this is `∫ y, (𝓕 f)(exp y) * exp ((1 - i t) * y) dy`. -/
def logFourierProfile (f : 𝓢(ℝ, ℂ)) (z : ℂ) : ℂ :=
  ∫ y : ℝ, (𝓕 f) (Real.exp y) * Complex.exp ((1 - z) * (y : ℂ))

/-- Half-twisted Mellin transform `M_{1/2}(U)(z) = ∫ x, U x * exp ((z - 1 / 2) * x) dx`. -/
def halfTwistMellin (U : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, U x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))

private theorem halfTwistMellin_halfTwistLogDilate {q : ℕ} (hq : 0 < q)
    (U : ℝ → ℂ) (z : ℂ) :
    halfTwistMellin (halfTwistLogDilate q U) z = (q : ℂ) ^ (-z) * halfTwistMellin U z := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  rw [halfTwistMellin, halfTwistMellin]
  have hfun : (fun x : ℝ ↦ halfTwistLogDilate q U x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))) =
      fun x : ℝ ↦ ((q : ℂ) ^ (-z)) *
        (U (x + Real.log q) * Complex.exp ((z - 1 / 2 : ℂ) * ((x + Real.log q : ℝ) : ℂ))) := by
    ext x
    simp only [halfTwistLogDilate, hq.ne', ↓reduceIte, LinearMap.coe_mk, AddHom.coe_mk]
    have hlogq : Complex.exp ((z - 1 / 2 : ℂ) * ((Real.log q : ℝ) : ℂ)) = (q : ℂ) ^ (z - 1 / 2) := by
      rw [← Complex.ofReal_natCast q, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hqp.ne'),
        ← Complex.ofReal_log hqp.le, mul_comm]
    have hsub : (x : ℂ) = ((x + Real.log q : ℝ) : ℂ) - (Real.log q : ℂ) := by push_cast; ring
    have hexp_split : Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ)) =
        (q : ℂ) ^ (-(z - 1 / 2)) * Complex.exp ((z - 1 / 2 : ℂ) * ((x + Real.log q : ℝ) : ℂ)) := by
      rw [hsub, mul_sub, Complex.exp_sub, hlogq, div_eq_mul_inv, Complex.cpow_neg, mul_comm]
    have hcpow : (q : ℂ) ^ (-(1 / 2 : ℂ)) * (q : ℂ) ^ (-(z - 1 / 2)) = (q : ℂ) ^ (-z) := by
      rw [← Complex.cpow_add _ _ hq0]
      congr 1
      ring
    rw [hexp_split]
    calc (q : ℂ) ^ (-(1 / 2 : ℂ)) * U (x + Real.log q) *
          ((q : ℂ) ^ (-(z - 1 / 2)) * Complex.exp ((z - 1 / 2 : ℂ) * ↑(x + Real.log q)))
        = ((q : ℂ) ^ (-(1 / 2 : ℂ)) * (q : ℂ) ^ (-(z - 1 / 2))) *
            (U (x + Real.log q) * Complex.exp ((z - 1 / 2 : ℂ) * ↑(x + Real.log q))) := by ring
      _ = _ := by rw [hcpow]
  rw [hfun, integral_const_mul]
  congr 1
  exact integral_add_right_eq_self
    (fun u : ℝ ↦ U u * Complex.exp ((z - 1 / 2 : ℂ) * (u : ℂ))) (Real.log q)

private theorem halfTwistMellin_depleteStepFun {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {q : ℕ} (hq : 0 < q)
    {U : ℝ → ℂ} (hU : IsHalfLineRapid U) (z : ℂ) :
    halfTwistMellin (depleteStepFun χ q U) z =
      (1 - χ q * (q : ℂ) ^ (-z)) * halfTwistMellin U z := by
  have h1 : Integrable (fun x : ℝ ↦ U x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))) volume := by
    simpa using integrable_poly_mul_isHalfLineRapid hU 0 (z - 1 / 2)
  have h2 : Integrable
      (fun x : ℝ ↦ (χ q • halfTwistLogDilate q U) x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ)))
      volume := by
    simpa using integrable_poly_mul_isHalfLineRapid
      (isHalfLineRapid_smul (χ q) (isHalfLineRapid_halfTwistLogDilate hq hU)) 0 (z - 1 / 2)
  have hsplit : halfTwistMellin (depleteStepFun χ q U) z =
      halfTwistMellin U z - χ q * halfTwistMellin (halfTwistLogDilate q U) z := by
    rw [halfTwistMellin]
    have hfun : (fun x : ℝ ↦ depleteStepFun χ q U x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))) =
        fun x : ℝ ↦ U x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ)) -
          (χ q • halfTwistLogDilate q U) x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ)) := by
      ext x
      simp [depleteStepFun, sub_mul]
    rw [hfun, integral_sub h1 h2, halfTwistMellin]
    have hsm : (fun x : ℝ ↦ (χ q • halfTwistLogDilate q U) x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))) =
        fun x : ℝ ↦ χ q * (halfTwistLogDilate q U x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))) := by
      ext x; simp [mul_assoc]
    rw [hsm, integral_const_mul, halfTwistMellin]
  rw [hsplit, halfTwistMellin_halfTwistLogDilate hq U z]
  ring

/-- `halfTwistMellin` turns `dirichletDeplete χ T` into multiplication by the Euler factor
`dirichletStageMultiplier χ T z`.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem halfTwistMellin_dirichletDeplete {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hN : 1 < N) (T : Finset ℕ) (hT : ∀ q ∈ T, 0 < q)
    {X : ℝ} (hX : 0 < X) {f : 𝓢(ℝ, ℂ)} (hf : IsDirichletFixedBoxTest χ X f)
    (hχ : χ.IsPrimitive) (z : ℂ) :
    halfTwistMellin (dirichletDeplete χ T (twistedHalfLogProfile χ f)) z =
      dirichletStageMultiplier χ T z * halfTwistMellin (twistedHalfLogProfile χ f) z := by
  have hU := isHalfLineRapid_twistedHalfLogProfile hχ hN hX hf
  clear hf hX hχ hN
  induction T using Finset.induction_on with
  | empty => simp [dirichletStageMultiplier]
  | insert q S hqS ih =>
    have hq0 : 0 < q := hT q (Finset.mem_insert_self q S)
    have hS : ∀ r ∈ S, 0 < r := fun r hr ↦ hT r (Finset.mem_insert_of_mem hr)
    have hUS := isHalfLineRapid_dirichletDeplete χ S hS hU
    rw [dirichletDeplete_insert χ hqS, LinearMap.comp_apply,
      halfTwistMellin_depleteStepFun χ hq0 hUS z, ih hS]
    change (1 - χ q * (q : ℂ) ^ (-z)) * (dirichletStageMultiplier χ S z * _) = _
    rw [dirichletStageMultiplier, dirichletStageMultiplier, Finset.prod_insert hqS]
    ring

private theorem dirichletFixedBox_integral_even_fold {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hN : 1 < N) {f : 𝓢(ℝ, ℂ)} (hpar : HasDirichletParity χ f)
    (w : ℝ) :
    (∑' m : ℤ, χ⁻¹ (m : ZMod N) * (𝓕 f) ((m : ℝ) * Real.exp w)) =
      2 * ∑' n : ℕ, χ⁻¹ ((n + 1 : ℕ) : ZMod N) * (𝓕 f) (((n + 1 : ℕ) : ℝ) * Real.exp w) := by
  have hsum_int : Summable (fun m : ℤ ↦ χ⁻¹ (m : ZMod N) * (𝓕 f) ((m : ℝ) * Real.exp w)) := by
    have hr_ne : Real.exp w ≠ 0 := (Real.exp_pos w).ne'
    let g := schwartzScale (Real.exp w) hr_ne (𝓕 f)
    have hg₀ := (g.isBigO_cocompact_rpow (-2)).norm_left.comp_tendsto Int.tendsto_coe_cofinite
    have hg : (fun m : ℤ ↦ ‖g (m : ℝ)‖) =O[cofinite] (fun m : ℤ ↦ |(m : ℝ)| ^ (-2 : ℝ)) :=
      hg₀.congr (fun _ ↦ rfl) (fun m ↦ by simp [Real.norm_eq_abs])
    refine (summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) ?_).of_norm
    refine Asymptotics.IsBigO.trans ?_ hg
    refine Asymptotics.isBigO_of_le _ fun m ↦ ?_
    rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg (norm_nonneg _), norm_mul]
    calc ‖χ⁻¹ (m : ZMod N)‖ * ‖(𝓕 f) ((m : ℝ) * Real.exp w)‖
        ≤ 1 * ‖(𝓕 f) ((m : ℝ) * Real.exp w)‖ :=
          mul_le_mul_of_nonneg_right (norm_dirichletChar_le_one χ⁻¹ m) (norm_nonneg _)
      _ = ‖g (m : ℝ)‖ := by simp [g, schwartzScale_apply, mul_comm]
  let g_term : ℤ → ℂ := fun m ↦ χ⁻¹ (m : ZMod N) * (𝓕 f) ((m : ℝ) * Real.exp w)
  have heven : g_term.Even := fun m ↦ by
    dsimp [g_term]
    have hm1 : ((-m : ℤ) : ZMod N) = (-1 : ZMod N) * (m : ZMod N) := by push_cast; ring
    have hm2 : ((-m : ℤ) : ℝ) * Real.exp w = -((m : ℝ) * Real.exp w) := by push_cast; ring
    rw [hm1, map_mul, dirichlet_inv_eval_neg_one, hm2, hpar.fourier]
    calc χ (-1) * χ⁻¹ (m : ZMod N) * (χ (-1) * (𝓕 f) ((m : ℝ) * Real.exp w))
        = (χ (-1) * χ (-1)) * (χ⁻¹ (m : ZMod N) * (𝓕 f) ((m : ℝ) * Real.exp w)) := by ring
      _ = χ⁻¹ (m : ZMod N) * (𝓕 f) ((m : ℝ) * Real.exp w) := by
          rw [dirichlet_eval_neg_one_sq, one_mul]
  change ∑' m : ℤ, g_term m = _
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsum_int, two_smul]
  have h0 : g_term 0 = 0 := by simp [g_term, dirichletChar_inv_zero_of_one_lt χ hN]
  rw [h0, zero_add, ← two_mul]
  congr 1
  rw [← Equiv.pnatEquivNat.symm.tsum_eq (fun p : ℕ+ ↦ g_term (p : ℤ))]
  refine tsum_congr fun n ↦ ?_
  simp only [Equiv.pnatEquivNat_symm_apply, g_term]
  congr 2
  simp [Nat.succPNat]

private theorem dirichletFixedBox_mellin_eq_lt {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    {X : ℝ} (hX : 0 < X) {f : 𝓢(ℝ, ℂ)} (hf : IsDirichletFixedBoxTest χ X f)
    {z : ℂ} (hz : z.re < 0) :
    halfTwistMellin (twistedHalfLogProfile χ f) z =
      2 * gaussSum χ ZMod.stdAddChar * (N : ℂ) ^ (-z) *
        DirichletCharacter.LFunction χ⁻¹ (1 - z) * logFourierProfile f z := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hre1 : 1 < (1 - z).re := by simp only [sub_re, one_re]; linarith
  have hsub_pos : 0 < 1 - z.re := by linarith
  have hw_step : halfTwistMellin (twistedHalfLogProfile χ f) z =
      2 * gaussSum χ ZMod.stdAddChar * (N : ℂ) ^ (-z) *
        ∫ w : ℝ, ∑' n : ℕ,
          (χ⁻¹ ((n + 1 : ℕ) : ZMod N) * (𝓕 f) (((n + 1 : ℕ) : ℝ) * Real.exp w) *
            Complex.exp ((1 - z) * (w : ℂ))) := by
    rw [halfTwistMellin]
    have hrew : (fun x : ℝ ↦ twistedHalfLogProfile χ f x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))) =
        fun x : ℝ ↦ gaussSum χ ZMod.stdAddChar *
          ((N : ℂ)⁻¹ * Complex.exp ((z - 1 : ℂ) * (x : ℂ)) *
            ∑' m : ℤ, χ⁻¹ (m : ZMod N) * (𝓕 f) ((m : ℝ) / ((N : ℝ) * Real.exp x))) := by
      ext x
      rw [twistedHalfLogProfile, twisted_poisson_summation hχ f (Real.exp_pos x)]
      have hexp1 : (Real.exp (x / 2) : ℂ) * (1 / ((N : ℂ) * (Real.exp x : ℂ))) *
          Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ)) = (N : ℂ)⁻¹ * Complex.exp ((z - 1 : ℂ) * (x : ℂ)) := by
        have hhalf : (Real.exp (x / 2) : ℂ) = Complex.exp (((1 / 2 : ℝ) : ℂ) * (x : ℂ)) := by
          rw [Complex.ofReal_exp]
          congr 1; push_cast; ring
        have hinv : ((Real.exp x : ℂ))⁻¹ = Complex.exp (-(1 : ℂ) * (x : ℂ)) := by
          rw [Complex.ofReal_exp, ← Complex.exp_neg]
          congr 1; ring
        rw [one_div, mul_inv, hhalf, hinv, mul_comm ((N : ℂ)⁻¹)]
        have hmul : Complex.exp (((1 / 2 : ℝ) : ℂ) * (x : ℂ)) * Complex.exp (-(1 : ℂ) * (x : ℂ)) *
            Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ)) = Complex.exp ((z - 1 : ℂ) * (x : ℂ)) := by
          rw [← Complex.exp_add, ← Complex.exp_add]
          congr 1; push_cast; ring
        calc Complex.exp (((1 / 2 : ℝ) : ℂ) * (x : ℂ)) * (Complex.exp (-(1 : ℂ) * (x : ℂ)) * (N : ℂ)⁻¹) *
              Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))
            = (N : ℂ)⁻¹ * (Complex.exp (((1 / 2 : ℝ) : ℂ) * (x : ℂ)) *
                Complex.exp (-(1 : ℂ) * (x : ℂ)) * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))) := by ring
          _ = _ := by rw [hmul]
      calc (Real.exp (x / 2) : ℂ) * (gaussSum χ ZMod.stdAddChar / ((N : ℂ) * (Real.exp x : ℂ)) *
              ∑' m : ℤ, χ⁻¹ (m : ZMod N) * (𝓕 f) ((m : ℝ) / ((N : ℝ) * Real.exp x))) *
            Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))
          = gaussSum χ ZMod.stdAddChar *
              (((Real.exp (x / 2) : ℂ) * (1 / ((N : ℂ) * (Real.exp x : ℂ))) *
                Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))) *
                ∑' m : ℤ, χ⁻¹ (m : ZMod N) * (𝓕 f) ((m : ℝ) / ((N : ℝ) * Real.exp x))) := by ring
        _ = _ := by rw [hexp1]
    rw [hrew, integral_const_mul]
    rw [← integral_neg_eq_self, ← integral_add_right_eq_self _ (Real.log N)]
    have hsub : (fun w : ℝ ↦ (N : ℂ)⁻¹ * Complex.exp ((z - 1 : ℂ) * ((-w - Real.log N : ℝ) : ℂ)) *
          ∑' m : ℤ, χ⁻¹ (m : ZMod N) * (𝓕 f) ((m : ℝ) / ((N : ℝ) * Real.exp (-w - Real.log N)))) =
        fun w : ℝ ↦ 2 * (N : ℂ) ^ (-z) * ∑' n : ℕ,
          (χ⁻¹ ((n + 1 : ℕ) : ZMod N) * (𝓕 f) (((n + 1 : ℕ) : ℝ) * Real.exp w) *
            Complex.exp ((1 - z) * (w : ℂ))) := by
      ext w
      have harg : ((N : ℝ) * Real.exp (-w - Real.log N))⁻¹ = Real.exp w := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hNpos]
        field_simp [hNpos.ne', (Real.exp_pos w).ne']
      have hdiv_arg : ∀ m : ℤ, (m : ℝ) / ((N : ℝ) * Real.exp (-w - Real.log N)) = (m : ℝ) * Real.exp w := by
        intro m; rw [div_eq_mul_inv, harg]
      simp_rw [hdiv_arg]
      rw [dirichletFixedBox_integral_even_fold χ hN hf.1 w]
      have hNpow : (N : ℂ)⁻¹ * Complex.exp ((z - 1 : ℂ) * ((-w - Real.log N : ℝ) : ℂ)) =
          (N : ℂ) ^ (-z) * Complex.exp ((1 - z) * (w : ℂ)) := by
        have hcpN : (N : ℂ) ^ (-z) = (N : ℂ)⁻¹ * Complex.exp (-(z - 1) * (Real.log N : ℂ)) := by
          have hN_exp : (N : ℂ)⁻¹ = Complex.exp (-(Real.log N : ℂ)) := by
            rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hNpos, Complex.ofReal_natCast]
          rw [← Complex.ofReal_natCast N, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hNpos.ne'),
            ← Complex.ofReal_log hNpos.le, Complex.ofReal_natCast, hN_exp, ← Complex.exp_add]
          congr 1; ring
        rw [hcpN]
        have hexp_eq : Complex.exp ((z - 1 : ℂ) * ((-w - Real.log N : ℝ) : ℂ)) =
            Complex.exp (-(z - 1) * (Real.log N : ℂ)) * Complex.exp ((1 - z) * (w : ℂ)) := by
          rw [← Complex.exp_add]
          congr 1; push_cast; ring
        rw [hexp_eq]
        ring
      calc (N : ℂ)⁻¹ * Complex.exp ((z - 1 : ℂ) * ((-w - Real.log N : ℝ) : ℂ)) *
            (2 * ∑' n : ℕ, χ⁻¹ ((n + 1 : ℕ) : ZMod N) * (𝓕 f) (((n + 1 : ℕ) : ℝ) * Real.exp w))
          = 2 * (N : ℂ) ^ (-z) * (Complex.exp ((1 - z) * (w : ℂ)) *
              ∑' n : ℕ, χ⁻¹ ((n + 1 : ℕ) : ZMod N) * (𝓕 f) (((n + 1 : ℕ) : ℝ) * Real.exp w)) := by
            rw [hNpow]; ring
        _ = 2 * (N : ℂ) ^ (-z) * ∑' n : ℕ,
              (χ⁻¹ ((n + 1 : ℕ) : ZMod N) * (𝓕 f) (((n + 1 : ℕ) : ℝ) * Real.exp w) *
                Complex.exp ((1 - z) * (w : ℂ))) := by
            rw [← tsum_mul_left]
            congr 2
            ext n
            ring
    have hneg_add : (fun w : ℝ ↦ (N : ℂ)⁻¹ * Complex.exp ((z - 1 : ℂ) * ((-(w + Real.log N) : ℝ) : ℂ)) *
          ∑' m : ℤ, χ⁻¹ (m : ZMod N) * (𝓕 f) ((m : ℝ) / ((N : ℝ) * Real.exp (-(w + Real.log N))))) =
        fun w : ℝ ↦ (N : ℂ)⁻¹ * Complex.exp ((z - 1 : ℂ) * ((-w - Real.log N : ℝ) : ℂ)) *
          ∑' m : ℤ, χ⁻¹ (m : ZMod N) * (𝓕 f) ((m : ℝ) / ((N : ℝ) * Real.exp (-w - Real.log N))) := by
      ext w
      rw [show -(w + Real.log N) = -w - Real.log N by ring]
    rw [hneg_add, hsub, integral_const_mul]
    ring
  rw [hw_step]
  obtain ⟨Cf, hCf, hf_bd⟩ := (𝓕 f).decay 0 0
  have hCf_bd : ∀ u : ℝ, ‖(𝓕 f) u‖ ≤ Cf := fun u ↦ by
    simpa [norm_iteratedFDeriv_zero] using hf_bd u
  let F : ℕ → ℝ → ℂ := fun n w ↦
    χ⁻¹ ((n + 1 : ℕ) : ZMod N) * (𝓕 f) (((n + 1 : ℕ) : ℝ) * Real.exp w) *
      Complex.exp ((1 - z) * (w : ℂ))
  have hF_shift : ∀ n : ℕ, (fun w : ℝ ↦ F n (w - Real.log ((n + 1 : ℕ) : ℝ))) =
      fun y : ℝ ↦ χ⁻¹ ((n + 1 : ℕ) : ZMod N) * ((n + 1 : ℕ) : ℂ) ^ (-(1 - z)) *
        ((𝓕 f) (Real.exp y) * Complex.exp ((1 - z) * (y : ℂ))) := by
    intro n
    ext y
    have hn_pos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hexp_shift : ((n + 1 : ℕ) : ℝ) * Real.exp (y - Real.log ((n + 1 : ℕ) : ℝ)) = Real.exp y := by
      rw [Real.exp_sub, Real.exp_log hn_pos, mul_div_cancel₀ _ hn_pos.ne']
    have hcexp_shift : Complex.exp ((1 - z) * ((y - Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ)) =
        ((n + 1 : ℕ) : ℂ) ^ (-(1 - z)) * Complex.exp ((1 - z) * (y : ℂ)) := by
      have hcp : ((n + 1 : ℕ) : ℂ) ^ (-(1 - z)) =
          Complex.exp ((1 - z) * (-(Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ)) := by
        rw [← Complex.ofReal_natCast, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn_pos.ne'),
          ← Complex.ofReal_log hn_pos.le]
        congr 1; push_cast; ring
      rw [hcp, ← Complex.exp_add]
      congr 1; push_cast; ring
    dsimp [F]
    rw [hexp_shift, hcexp_shift]
    ring
  have hlog_int : Integrable (fun y : ℝ ↦ (𝓕 f) (Real.exp y) * Complex.exp ((1 - z) * (y : ℂ))) volume := by
    have hmeas : AEStronglyMeasurable
        (fun y : ℝ ↦ (𝓕 f) (Real.exp y) * Complex.exp ((1 - z) * (y : ℂ))) volume :=
      (((𝓕 f).continuous.comp Real.continuous_exp).mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
    have hdom_int : Integrable
        (fun y : ℝ ↦ Set.indicator (Set.Iic (Real.log X))
          (fun y : ℝ ↦ Cf * Real.exp ((1 - z.re) * y)) y) volume := by
      have hi : IntegrableOn (fun y : ℝ ↦ Cf * Complex.exp (((1 - z.re : ℝ) : ℂ) * (y : ℂ)))
          (Set.Iic (Real.log X)) volume :=
        (integrableOn_exp_mul_complex_Iic (by simpa using hsub_pos) (Real.log X)).const_mul _
      have hi' : IntegrableOn (fun y : ℝ ↦ Cf * Real.exp ((1 - z.re) * y))
          (Set.Iic (Real.log X)) volume := by
        refine IntegrableOn.congr_fun hi.norm (fun y _ ↦ ?_) measurableSet_Iic
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hCf.le, Complex.norm_exp]
        simp [Complex.mul_re]
      exact IntegrableOn.integrable_indicator hi' measurableSet_Iic
    refine hdom_int.mono' hmeas (Filter.Eventually.of_forall fun y ↦ ?_)
    by_cases hy : y ≤ Real.log X
    · rw [Set.indicator_of_mem hy, norm_mul, Complex.norm_exp]
      have hre_eq : ((1 - z) * (y : ℂ)).re = (1 - z.re) * y := by
        simp [mul_re]
      rw [hre_eq]
      exact mul_le_mul_of_nonneg_right (hCf_bd _) (Real.exp_pos _).le
    · have hXlt : X < Real.exp y := by
        rw [← Real.exp_log hX]
        exact Real.exp_lt_exp.mpr (lt_of_not_ge hy)
      have hnot : Real.exp y ∉ tsupport (fun u : ℝ ↦ (𝓕 f) u) := fun hmem ↦
        hXlt.not_ge (hf.2 hmem).2
      have hval0 : (𝓕 f) (Real.exp y) = 0 := by
        by_contra hne
        exact hnot (subset_tsupport _ hne)
      rw [hval0, zero_mul, norm_zero]
      exact Set.indicator_nonneg (fun _ _ ↦ by positivity) y
  have hF_int : ∀ n : ℕ, Integrable (F n) volume := fun n ↦ by
    have hi_sub : Integrable (fun y : ℝ ↦ F n (y - Real.log ((n + 1 : ℕ) : ℝ))) volume := by
      have hfun : (fun y : ℝ ↦ F n (y - Real.log ((n + 1 : ℕ) : ℝ))) =
          fun y : ℝ ↦ (χ⁻¹ ((n + 1 : ℕ) : ZMod N) * ((n + 1 : ℕ) : ℂ) ^ (-(1 - z))) *
            ((𝓕 f) (Real.exp y) * Complex.exp ((1 - z) * (y : ℂ))) := funext (congrFun (hF_shift n))
      rw [hfun]
      exact hlog_int.const_mul _
    simpa [sub_add_cancel] using hi_sub.comp_add_right (Real.log ((n + 1 : ℕ) : ℝ))
  have hF_norm_sum : Summable (fun n : ℕ ↦ ∫ w : ℝ, ‖F n w‖) := by
    let I0 : ℝ := ∫ y : ℝ, ‖(𝓕 f) (Real.exp y) * Complex.exp ((1 - z) * (y : ℂ))‖
    have hterm_n (n : ℕ) : ∫ w : ℝ, ‖F n w‖ ≤ ((n + 1 : ℕ) : ℝ) ^ (-(1 - z.re)) * I0 := by
      rw [← integral_sub_right_eq_self (fun w : ℝ ↦ ‖F n w‖) (Real.log ((n + 1 : ℕ) : ℝ))]
      have hrew : (fun y : ℝ ↦ ‖F n (y - Real.log ((n + 1 : ℕ) : ℝ))‖) =
          fun y : ℝ ↦ ‖χ⁻¹ ((n + 1 : ℕ) : ZMod N)‖ * ‖((n + 1 : ℕ) : ℂ) ^ (-(1 - z))‖ *
            ‖(𝓕 f) (Real.exp y) * Complex.exp ((1 - z) * (y : ℂ))‖ := by
        ext y
        have h := congrFun (hF_shift n) y
        simp only [h, norm_mul, mul_assoc]
      rw [hrew, integral_const_mul]
      have hn_pos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
      have hcpow_norm : ‖((n + 1 : ℕ) : ℂ) ^ (-(1 - z))‖ = ((n + 1 : ℕ) : ℝ) ^ (-(1 - z.re)) := by
        rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn_pos]
        simp
      have hI0_nn : 0 ≤ I0 := integral_nonneg fun _ ↦ norm_nonneg _
      have hcoef_le : ‖χ⁻¹ ((n + 1 : ℕ) : ZMod N)‖ * ‖((n + 1 : ℕ) : ℂ) ^ (-(1 - z))‖ ≤
          ((n + 1 : ℕ) : ℝ) ^ (-(1 - z.re)) := by
        rw [hcpow_norm]
        exact mul_le_of_le_one_left (by positivity) (norm_dirichletChar_le_one χ⁻¹ _)
      exact mul_le_mul_of_nonneg_right hcoef_le hI0_nn
    have hp : Summable (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ (-(1 - z.re)) * I0) := by
      have hs := (Real.summable_nat_rpow_inv.mpr hre1).comp_injective Nat.succ_injective
      have hs' : Summable (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ (-(1 - z.re))) := by
        refine hs.congr fun n ↦ ?_
        change (((n + 1 : ℕ) : ℝ) ^ (1 - z.re))⁻¹ = ((n + 1 : ℕ) : ℝ) ^ (-(1 - z.re))
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
      exact hs'.mul_right I0
    exact hp.of_nonneg_of_le (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) hterm_n
  have htsum_eq : (∫ w : ℝ, ∑' n : ℕ, F n w) = ∑' n : ℕ, ∫ w : ℝ, F n w :=
    (integral_tsum_of_summable_integral_norm hF_int hF_norm_sum).symm
  rw [htsum_eq]
  have hterm_int (n : ℕ) :
      ∫ w : ℝ, F n w =
        (χ⁻¹ ((n + 1 : ℕ) : ZMod N) * ((n + 1 : ℕ) : ℂ) ^ (-(1 - z))) * logFourierProfile f z := by
    rw [← integral_sub_right_eq_self (F n) (Real.log ((n + 1 : ℕ) : ℝ))]
    have hrew : (fun y : ℝ ↦ F n (y - Real.log ((n + 1 : ℕ) : ℝ))) =
        fun y : ℝ ↦ (χ⁻¹ ((n + 1 : ℕ) : ZMod N) * ((n + 1 : ℕ) : ℂ) ^ (-(1 - z))) *
          ((𝓕 f) (Real.exp y) * Complex.exp ((1 - z) * (y : ℂ))) := funext (congrFun (hF_shift n))
    rw [hrew, integral_const_mul, logFourierProfile]
  simp_rw [hterm_int]
  rw [tsum_mul_right]
  have hL : (∑' n : ℕ, χ⁻¹ ((n + 1 : ℕ) : ZMod N) * ((n + 1 : ℕ) : ℂ) ^ (-(1 - z))) =
      DirichletCharacter.LFunction χ⁻¹ (1 - z) := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ⁻¹ hre1, LSeries]
    have h0 : LSeries.term (fun m : ℕ ↦ χ⁻¹ m) (1 - z) 0 = 0 := LSeries.term_zero _ _
    have hsumL : Summable (LSeries.term (fun m : ℕ ↦ χ⁻¹ m) (1 - z)) :=
      DirichletCharacter.LSeriesSummable_of_one_lt_re χ⁻¹ hre1
    rw [hsumL.tsum_eq_zero_add, h0, zero_add]
    refine tsum_congr fun n ↦ ?_
    rw [LSeries.term_of_ne_zero (Nat.add_one_ne_zero n)]
    simp only [Nat.cast_add, Nat.cast_one, Complex.cpow_neg, div_eq_mul_inv]
  rw [hL]
  ring

/-- Paper: (11.3.1.3), p. 494.
For a primitive nontrivial Dirichlet character `χ` (`1 < N`) and a fixed-box test `f`
(`IsDirichletFixedBoxTest χ X f`), on the closed left half-plane `Re z ≤ 0` the half-twisted
Mellin transform `halfTwistMellin (twistedHalfLogProfile χ f) z` factors through `L(1 - z, χ⁻¹)`
and `logFourierProfile f z`.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem dirichletFixedBox_mellin_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    {X : ℝ} (hX : 0 < X) {f : 𝓢(ℝ, ℂ)} (hf : IsDirichletFixedBoxTest χ X f)
    {z : ℂ} (hz : z.re ≤ 0) :
    halfTwistMellin (twistedHalfLogProfile χ f) z =
      2 * gaussSum χ ZMod.stdAddChar * (N : ℂ) ^ (-z) *
        DirichletCharacter.LFunction χ⁻¹ (1 - z) * logFourierProfile f z := by
  rcases lt_or_eq_of_le hz with hz_lt | hz_eq
  · exact dirichletFixedBox_mellin_eq_lt hχ hN hX hf hz_lt
  · let zseq : ℕ → ℂ := fun k ↦ z - Complex.ofReal (((k + 1 : ℕ) : ℝ)⁻¹)
    have hseq_lt : ∀ k : ℕ, (zseq k).re < 0 := fun k ↦ by
      simp only [zseq, sub_re, Complex.ofReal_re]
      have hk : (0 : ℝ) < (((k + 1 : ℕ) : ℝ)⁻¹) := by positivity
      linarith [hz_eq]
    have hseq_eq : ∀ k : ℕ,
        halfTwistMellin (twistedHalfLogProfile χ f) (zseq k) =
          2 * gaussSum χ ZMod.stdAddChar * (N : ℂ) ^ (-(zseq k)) *
            DirichletCharacter.LFunction χ⁻¹ (1 - zseq k) * logFourierProfile f (zseq k) :=
      fun k ↦ dirichletFixedBox_mellin_eq_lt hχ hN hX hf (hseq_lt k)
    have htend : Tendsto zseq atTop (𝓝 z) := by
      have hinvR : Tendsto (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
      have hinv : Tendsto (fun k : ℕ ↦ Complex.ofReal (((k + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 (0 : ℂ)) :=
        (Complex.continuous_ofReal.continuousAt.tendsto.comp hinvR).trans_eq (congrArg 𝓝 Complex.ofReal_zero)
      simpa [zseq] using tendsto_const_nhds.sub hinv
    let U : ℝ → ℂ := twistedHalfLogProfile χ f
    have hU := isHalfLineRapid_twistedHalfLogProfile hχ hN hX hf
    obtain ⟨hU_cont, B, hU_supp, hU_dec⟩ := hU
    have hlhs_tend : Tendsto (fun k : ℕ ↦ halfTwistMellin U (zseq k))
        atTop (𝓝 (halfTwistMellin U z)) := by
      have hbd1 : Integrable (fun x : ℝ ↦ ‖U x‖ *
          max (Real.exp ((z.re - 1 / 2) * x)) (Real.exp ((z.re - 3 / 2) * x))) volume := by
        have hi1 := (integrable_poly_mul_isHalfLineRapid ⟨hU_cont, B, hU_supp, hU_dec⟩ 0
          ((z.re - 1 / 2 : ℝ) : ℂ)).norm
        have hi2 := (integrable_poly_mul_isHalfLineRapid ⟨hU_cont, B, hU_supp, hU_dec⟩ 0
          ((z.re - 3 / 2 : ℝ) : ℂ)).norm
        have hi_sum : Integrable (fun x : ℝ ↦
            ‖U x * Complex.exp (((z.re - 1 / 2 : ℝ) : ℂ) * (x : ℂ))‖ +
            ‖U x * Complex.exp (((z.re - 3 / 2 : ℝ) : ℂ) * (x : ℂ))‖) volume := by
          refine (hi1.add hi2).congr (Filter.Eventually.of_forall fun x ↦ ?_)
          simp [U]
        have hm1 : Continuous (fun x : ℝ ↦ Real.exp ((z.re - 1 / 2) * x)) := by fun_prop
        have hm2 : Continuous (fun x : ℝ ↦ Real.exp ((z.re - 3 / 2) * x)) := by fun_prop
        refine hi_sum.mono' (hU_cont.norm.mul (hm1.max hm2)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun x ↦ ?_)
        have hnn : 0 ≤ ‖U x‖ * max (Real.exp ((z.re - 1 / 2) * x)) (Real.exp ((z.re - 3 / 2) * x)) :=
          by positivity
        rw [Real.norm_of_nonneg hnn, mul_max_of_nonneg _ _ (norm_nonneg _)]
        simp only [norm_mul, Complex.norm_exp, mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero]
        exact max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left (by positivity))
      refine tendsto_integral_of_dominated_convergence
        (fun x ↦ ‖U x‖ * max (Real.exp ((z.re - 1 / 2) * x)) (Real.exp ((z.re - 3 / 2) * x)))
        (fun k ↦ (hU_cont.mul (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable)
        hbd1 (fun k ↦ Filter.Eventually.of_forall fun x ↦ ?_)
        (Filter.Eventually.of_forall fun x ↦ ?_)
      · rw [norm_mul, Complex.norm_exp]
        have hre : ((zseq k - 1 / 2 : ℂ) * (x : ℂ)).re = ((zseq k).re - 1 / 2) * x := by
          simp [mul_re]
        rw [hre]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hk0 : z.re - 1 ≤ (zseq k).re ∧ (zseq k).re ≤ z.re := by
          simp only [zseq, sub_re, Complex.ofReal_re]
          have h1 : (((k + 1 : ℕ) : ℝ)⁻¹) ≤ 1 :=
            inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (Nat.succ_pos k))
          have h2 : (0 : ℝ) ≤ (((k + 1 : ℕ) : ℝ)⁻¹) := by positivity
          exact ⟨by linarith, by linarith⟩
        rcases le_total 0 x with hx | hx
        · exact le_max_of_le_left (Real.exp_le_exp.mpr (by nlinarith))
        · exact le_max_of_le_right (Real.exp_le_exp.mpr (by nlinarith))
      · exact (continuous_const.mul (Complex.continuous_exp.comp
          ((continuous_id.sub continuous_const).mul continuous_const))).continuousAt.tendsto.comp htend
    obtain ⟨Cf, hCf, hf_bd⟩ := (𝓕 f).decay 0 0
    have hCf_bd : ∀ u : ℝ, ‖(𝓕 f) u‖ ≤ Cf := fun u ↦ by
      simpa [norm_iteratedFDeriv_zero] using hf_bd u
    have hlog_tend : Tendsto (fun k : ℕ ↦ logFourierProfile f (zseq k))
        atTop (𝓝 (logFourierProfile f z)) := by
      let bound : ℝ → ℝ := fun y ↦ Set.indicator (Set.Iic (Real.log X))
        (fun y : ℝ ↦ Cf * Real.exp y + Cf * Real.exp ((2 - z.re) * y)) y
      have hbound_int : Integrable bound volume := by
        have hi1 : IntegrableOn (fun y : ℝ ↦ Cf * Real.exp y) (Set.Iic (Real.log X)) volume :=
          (integrableOn_exp_Iic (Real.log X)).const_mul Cf
        have hi2 : IntegrableOn (fun y : ℝ ↦ Cf * Complex.exp (((2 - z.re : ℝ) : ℂ) * (y : ℂ)))
            (Set.Iic (Real.log X)) volume :=
          (integrableOn_exp_mul_complex_Iic (by simp only [Complex.ofReal_re]; linarith)
            (Real.log X)).const_mul Cf
        have hi2' : IntegrableOn (fun y : ℝ ↦ Cf * Real.exp ((2 - z.re) * y))
            (Set.Iic (Real.log X)) volume := by
          refine IntegrableOn.congr_fun hi2.norm (fun y _ ↦ ?_) measurableSet_Iic
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hCf.le, Complex.norm_exp]
          simp [mul_re]
        exact IntegrableOn.integrable_indicator (hi1.add hi2') measurableSet_Iic
      refine tendsto_integral_of_dominated_convergence bound
        (fun k ↦ (((𝓕 f).continuous.comp Real.continuous_exp).mul
          (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable)
        hbound_int (fun k ↦ Filter.Eventually.of_forall fun y ↦ ?_)
        (Filter.Eventually.of_forall fun y ↦ ?_)
      · by_cases hy : y ≤ Real.log X
        · dsimp only [bound]
          rw [Set.indicator_of_mem hy, norm_mul, Complex.norm_exp]
          have hre_eq : ((1 - zseq k) * (y : ℂ)).re = (1 - (zseq k).re) * y := by
            simp [mul_re]
          rw [hre_eq]
          have h1re : 1 ≤ 1 - (zseq k).re ∧ 1 - (zseq k).re ≤ 2 - z.re := by
            have hk0 : z.re - 1 ≤ (zseq k).re ∧ (zseq k).re ≤ 0 := by
              simp only [zseq, sub_re, Complex.ofReal_re]
              have h1 : (((k + 1 : ℕ) : ℝ)⁻¹) ≤ 1 :=
                inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (Nat.succ_pos k))
              have h2 : (0 : ℝ) ≤ (((k + 1 : ℕ) : ℝ)⁻¹) := by positivity
              exact ⟨by linarith [hz_eq], by linarith [hz_eq]⟩
            exact ⟨by linarith, by linarith⟩
          have hexp_le : Real.exp ((1 - (zseq k).re) * y) ≤ Real.exp y + Real.exp ((2 - z.re) * y) := by
            rcases le_total 0 y with hy0 | hy0
            · exact le_add_of_nonneg_of_le (Real.exp_pos _).le
                (Real.exp_le_exp.mpr (by nlinarith [h1re.1, h1re.2]))
            · exact le_add_of_le_of_nonneg (Real.exp_le_exp.mpr (by nlinarith [h1re.1, h1re.2]))
                (Real.exp_pos _).le
          calc ‖(𝓕 f) (Real.exp y)‖ * Real.exp ((1 - (zseq k).re) * y)
              ≤ Cf * (Real.exp y + Real.exp ((2 - z.re) * y)) :=
                mul_le_mul (hCf_bd _) hexp_le (Real.exp_pos _).le hCf.le
            _ = Cf * Real.exp y + Cf * Real.exp ((2 - z.re) * y) := mul_add _ _ _
        · have hXlt : X < Real.exp y := by
            rw [← Real.exp_log hX]
            exact Real.exp_lt_exp.mpr (lt_of_not_ge hy)
          have hnot : Real.exp y ∉ tsupport (fun u : ℝ ↦ (𝓕 f) u) := fun hmem ↦
            hXlt.not_ge (hf.2 hmem).2
          have hval0 : (𝓕 f) (Real.exp y) = 0 := by
            by_contra hne
            exact hnot (subset_tsupport _ hne)
          rw [hval0, zero_mul, norm_zero]
          exact Set.indicator_nonneg (fun _ _ ↦ by positivity) y
      · exact (continuous_const.mul (Complex.continuous_exp.comp
          ((continuous_const.sub continuous_id).mul continuous_const))).continuousAt.tendsto.comp htend
    have hrhs_tend : Tendsto (fun k : ℕ ↦
          2 * gaussSum χ ZMod.stdAddChar * (N : ℂ) ^ (-(zseq k)) *
            DirichletCharacter.LFunction χ⁻¹ (1 - zseq k) * logFourierProfile f (zseq k))
        atTop (𝓝 (2 * gaussSum χ ZMod.stdAddChar * (N : ℂ) ^ (-z) *
            DirichletCharacter.LFunction χ⁻¹ (1 - z) * logFourierProfile f z)) := by
      have hNpow_cont : Continuous (fun w : ℂ ↦ (N : ℂ) ^ (-w)) := by
        have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
        have hfun : (fun w : ℂ ↦ (N : ℂ) ^ (-w)) = fun w : ℂ ↦ Complex.exp (Complex.log (N : ℂ) * (-w)) :=
          funext fun w ↦ Complex.cpow_def_of_ne_zero hNne (-w)
        rw [hfun]
        exact Complex.continuous_exp.comp (continuous_const.mul continuous_neg)
      have hL_cont : Continuous (fun w : ℂ ↦ DirichletCharacter.LFunction χ⁻¹ (1 - w)) :=
        (DirichletCharacter.differentiable_LFunction
          (dirichlet_inv_isPrimitive_ne_one hχ hN).2).continuous.comp (continuous_const.sub continuous_id)
      exact ((((tendsto_const_nhds.mul (hNpow_cont.continuousAt.tendsto.comp htend)).mul
        (hL_cont.continuousAt.tendsto.comp htend)).mul hlog_tend))
    exact tendsto_nhds_unique (hlhs_tend.congr' (Filter.Eventually.of_forall fun k ↦ hseq_eq k)) hrhs_tend

private theorem hasDerivAt_halfLineMoment {U : ℝ → ℂ} (hU : IsHalfLineRapid U)
    (k : ℕ) (z₀ : ℂ) :
    HasDerivAt (fun z : ℂ ↦ ∫ x : ℝ, (x : ℂ) ^ k * U x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ)))
      (∫ x : ℝ, (x : ℂ) ^ (k + 1) * U x * Complex.exp ((z₀ - 1 / 2 : ℂ) * (x : ℂ))) z₀ := by
  let F : ℂ → ℝ → ℂ := fun z x ↦ (x : ℂ) ^ k * U x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))
  let F' : ℂ → ℝ → ℂ := fun z x ↦ (x : ℂ) ^ (k + 1) * U x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))
  let s : Set ℂ := Metric.ball z₀ 1
  have hs : s ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ zero_lt_one
  have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) volume :=
    Filter.Eventually.of_forall fun z ↦ (integrable_poly_mul_isHalfLineRapid hU k (z - 1 / 2)).1
  have hF_int : Integrable (F z₀) volume := integrable_poly_mul_isHalfLineRapid hU k (z₀ - 1 / 2)
  have hF'_meas : AEStronglyMeasurable (F' z₀) volume :=
    (integrable_poly_mul_isHalfLineRapid hU (k + 1) (z₀ - 1 / 2)).1
  let bound : ℝ → ℝ := fun x ↦
    ‖(x : ℂ) ^ (k + 1) * U x * Complex.exp (((z₀.re + 1 - 1 / 2 : ℝ) : ℂ) * (x : ℂ))‖ +
    ‖(x : ℂ) ^ (k + 1) * U x * Complex.exp (((z₀.re - 1 - 1 / 2 : ℝ) : ℂ) * (x : ℂ))‖
  have bound_integrable : Integrable bound volume :=
    (integrable_poly_mul_isHalfLineRapid hU (k + 1) ((z₀.re + 1 - 1 / 2 : ℝ) : ℂ)).norm.add
      (integrable_poly_mul_isHalfLineRapid hU (k + 1) ((z₀.re - 1 - 1 / 2 : ℝ) : ℂ)).norm
  have h_bound : ∀ᵐ x ∂volume, ∀ z ∈ s, ‖F' z x‖ ≤ bound x := by
    refine Filter.Eventually.of_forall fun x z hz ↦ ?_
    have hz_re : z₀.re - 1 ≤ z.re ∧ z.re ≤ z₀.re + 1 := by
      have hdist : ‖z - z₀‖ < 1 := by simpa only [dist_eq_norm] using Metric.mem_ball.mp hz
      have hre_abs : |z.re - z₀.re| ≤ ‖z - z₀‖ := Complex.abs_re_le_norm (z - z₀)
      have h1 : |z.re - z₀.re| < 1 := hre_abs.trans_lt hdist
      rw [abs_lt] at h1
      exact ⟨by linarith, by linarith⟩
    dsimp [F', bound]
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hre0 : ((z - 1 / 2 : ℂ) * (x : ℂ)).re = (z.re - 1 / 2) * x := by simp [mul_re]
    have hre1 : (((z₀.re + 1 - 1 / 2 : ℝ) : ℂ) * (x : ℂ)).re = (z₀.re + 1 - 1 / 2) * x := by
      simp [mul_re]
    have hre2 : (((z₀.re - 1 - 1 / 2 : ℝ) : ℂ) * (x : ℂ)).re = (z₀.re - 1 - 1 / 2) * x := by
      simp [mul_re]
    rw [hre0, hre1, hre2]
    rcases le_total 0 x with hx | hx
    · refine le_add_of_le_of_nonneg ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
    · refine le_add_of_nonneg_of_le (by positivity) ?_
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
  have h_diff : ∀ᵐ x ∂volume, ∀ z ∈ s, HasDerivAt (F · x) (F' z x) z := by
    refine Filter.Eventually.of_forall fun x z _ ↦ ?_
    have hd1 : HasDerivAt (fun w : ℂ ↦ (w - 1 / 2 : ℂ) * (x : ℂ)) (x : ℂ) z := by
      simpa using ((hasDerivAt_id z).sub_const (1 / 2 : ℂ)).mul_const (x : ℂ)
    have hd2 := (Complex.hasDerivAt_exp _).comp z hd1
    have hd3 := hd2.const_mul ((x : ℂ) ^ k * U x)
    have hd_eq : (x : ℂ) ^ k * U x * (Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ)) * (x : ℂ)) = F' z x := by
      dsimp [F']
      rw [pow_succ]
      ring
    rw [← hd_eq]
    exact hd3
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas
    h_bound bound_integrable h_diff).2

theorem differentiable_halfLineMoment {U : ℝ → ℂ} (hU : IsHalfLineRapid U) (k : ℕ) :
    Differentiable ℂ (fun z : ℂ ↦ ∫ x : ℝ, (x : ℂ) ^ k * U x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))) :=
  fun z ↦ (hasDerivAt_halfLineMoment hU k z).differentiableAt

private theorem iteratedDeriv_halfTwistMellin_of_rapid {U : ℝ → ℂ} (hU : IsHalfLineRapid U)
    (k : ℕ) (z : ℂ) :
    iteratedDeriv k (halfTwistMellin U) z =
      ∫ x : ℝ, (x : ℂ) ^ k * U x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ)) := by
  induction k generalizing z with
  | zero => simp [halfTwistMellin]
  | succ k ih =>
    have hfun : iteratedDeriv k (halfTwistMellin U) =
        fun w : ℂ ↦ ∫ x : ℝ, (x : ℂ) ^ k * U x * Complex.exp ((w - 1 / 2 : ℂ) * (x : ℂ)) :=
      funext ih
    rw [iteratedDeriv_succ, hfun]
    exact (hasDerivAt_halfLineMoment hU k z).deriv

/-- For any depleted fixed-box profile `dirichletDeplete χ T (twistedHalfLogProfile χ f)`,
`halfTwistMellin` is entire and its `k`-th complex derivative is the `x^k`-weighted Mellin integral. -/
theorem iteratedDeriv_halfTwistMellin_depleted {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, 0 < q)
    {X : ℝ} (hX : 0 < X) {f : 𝓢(ℝ, ℂ)} (hf : IsDirichletFixedBoxTest χ X f)
    (k : ℕ) (z : ℂ) :
    iteratedDeriv k (halfTwistMellin (dirichletDeplete χ T (twistedHalfLogProfile χ f))) z =
      ∫ x : ℝ, (x : ℂ) ^ k * dirichletDeplete χ T (twistedHalfLogProfile χ f) x *
        Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ)) :=
  iteratedDeriv_halfTwistMellin_of_rapid
    (isHalfLineRapid_dirichletDeplete χ T hT (isHalfLineRapid_twistedHalfLogProfile hχ hN hX hf)) k z

/-- Specialization of `dirichletFixedBox_mellin_eq` to `z = i t` on the imaginary axis. -/
theorem dirichletFixedBox_mellin_eq_imagAxis {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    {X : ℝ} (hX : 0 < X) {f : 𝓢(ℝ, ℂ)} (hf : IsDirichletFixedBoxTest χ X f) (t : ℝ) :
    halfTwistMellin (twistedHalfLogProfile χ f) ((t : ℂ) * Complex.I) =
      2 * gaussSum χ ZMod.stdAddChar * (N : ℂ) ^ (-(t : ℂ) * Complex.I) *
        DirichletCharacter.LFunction χ⁻¹ (1 - (t : ℂ) * Complex.I) *
        logFourierProfile f ((t : ℂ) * Complex.I) := by
  simpa [neg_mul] using dirichletFixedBox_mellin_eq hχ hN hX hf (by simp : ((t : ℂ) * Complex.I).re ≤ 0)

/-- Specialization of `dirichletFixedBox_mellin_eq` to `z = 0`. -/
theorem dirichletFixedBox_mellin_eq_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    {X : ℝ} (hX : 0 < X) {f : 𝓢(ℝ, ℂ)} (hf : IsDirichletFixedBoxTest χ X f) :
    halfTwistMellin (twistedHalfLogProfile χ f) 0 =
      2 * gaussSum χ ZMod.stdAddChar * DirichletCharacter.LFunction χ⁻¹ 1 *
        logFourierProfile f 0 := by
  simpa using dirichletFixedBox_mellin_eq hχ hN hX hf (by simp : (0 : ℂ).re ≤ 0)


end MellinAndStripRows

end RiemannMasullo.Isolated
