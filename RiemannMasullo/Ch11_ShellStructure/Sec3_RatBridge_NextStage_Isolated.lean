module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_DirichletFixedBox_Isolated

/-!
# The next stage through the full-line Mellin transform

Workstream B for #7351, stage 4. For a primitive `χ` of conductor `N > 1`:

* `twistedHalfLogProfile_functional_eq`: twisted Poisson summation as a functional equation of the
  half-logarithmic profile, `U_{χ,g}(x) = τ(χ) N^{-1/2} U_{χ⁻¹, 𝓕 g}(-x - log N)`.
* `isFullLineRapid_dirichletDeplete`: every depleted profile of a Schwartz test (no box) decays
  faster than every exponential on the whole line; its full-line Mellin transform converges
  everywhere, is continuous, and `halfTwistMellin_dirichletDeplete_insert` gives the factor
  `1 - χ(p) p^{-z}`; `halfTwistMellin_nextStage_primeFreq` gives its zeros at `z_j = i t_j`
  (deliverable 1).
* `dirichletNormalizedRow_eq_fullLine`: on a box test the normalized row is the row scalar inverse
  times the full-line Mellin integral (deliverable 2).
* `ratBridge_nextStage_rows_zero`, `ratBridge_nextStage_mem_stageSpace`: a box test whose depleted
  profile equals that of an element of the unrestricted next stage has all rows zero and lies in
  `dirichletStageSpace χ (insert p T) X` (deliverable 3).

Nothing imports this module; all declarations live in `namespace RiemannMasullo.Isolated`.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory Set Topology
open scoped NNReal SchwartzMap FourierTransform

namespace RiemannMasullo.Isolated

/-! ### Two-sided rapid decay -/

section Rapid

/-- Continuous functions on `ℝ` decaying faster than every exponential at both ends. -/
def IsFullLineRapid (U : ℝ → ℂ) : Prop :=
  Continuous U ∧ ∀ M : ℝ, ∃ C ≥ (0 : ℝ), ∀ x, ‖U x‖ ≤ C * Real.exp (-M * |x|)

private theorem exp_neg_two_abs_le (x : ℝ) : Real.exp (-2 * |x|) ≤ (1 + x ^ 2)⁻¹ := by
  rw [le_inv_comm₀ (Real.exp_pos _) (by positivity), ← Real.exp_neg, neg_mul, neg_neg]
  have h := Real.add_one_le_exp |x|
  have h2 : Real.exp (2 * |x|) = Real.exp |x| ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2]
  have h3 := pow_le_pow_left₀ (by positivity) h 2
  nlinarith [abs_nonneg x, sq_abs x]

private theorem norm_exp_mellin (z : ℂ) (x : ℝ) :
    ‖Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))‖ ≤ Real.exp (|z.re - 1 / 2| * |x|) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have : ((z - 1 / 2 : ℂ) * (x : ℂ)).re = (z.re - 1 / 2) * x := by simp
  rw [this, ← abs_mul]
  exact le_abs_self _

private theorem rapid_bound_mellin {U : ℝ → ℂ} (hU : IsFullLineRapid U) (R : ℝ) :
    ∃ C ≥ (0 : ℝ), ∀ z : ℂ, |z.re - 1 / 2| ≤ R → ∀ x : ℝ,
      ‖U x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))‖ ≤ C * (1 + x ^ 2)⁻¹ := by
  obtain ⟨C, hC, hb⟩ := hU.2 (R + 2)
  refine ⟨C, hC, fun z hz x ↦ ?_⟩
  rw [norm_mul]
  calc ‖U x‖ * ‖Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))‖
      ≤ (C * Real.exp (-(R + 2) * |x|)) * Real.exp (R * |x|) :=
        mul_le_mul (hb x) ((norm_exp_mellin z x).trans
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hz (abs_nonneg x))))
          (norm_nonneg _) (by positivity)
    _ = C * Real.exp (-2 * |x|) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ C * (1 + x ^ 2)⁻¹ := mul_le_mul_of_nonneg_left (exp_neg_two_abs_le x) hC

/-- The full-line Mellin integrand of a two-sided rapid function is integrable for every `z`. -/
theorem IsFullLineRapid.integrable_mellin {U : ℝ → ℂ} (hU : IsFullLineRapid U) (z : ℂ) :
    Integrable (fun x : ℝ ↦ U x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))) := by
  obtain ⟨C, -, hb⟩ := rapid_bound_mellin hU |z.re - 1 / 2|
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C) ?_
    (.of_forall fun x ↦ hb z le_rfl x)
  exact (hU.1.mul (Complex.continuous_exp.comp (continuous_const.mul
    Complex.continuous_ofReal))).aestronglyMeasurable

/-- The full-line Mellin transform of a two-sided rapid function is continuous. -/
theorem IsFullLineRapid.continuous_mellin {U : ℝ → ℂ} (hU : IsFullLineRapid U) :
    Continuous (halfTwistMellin U) := by
  refine continuous_iff_continuousAt.mpr fun z₀ ↦ ?_
  obtain ⟨C, -, hb⟩ := rapid_bound_mellin hU (|z₀.re - 1 / 2| + 1)
  have hcont (x : ℝ) : Continuous fun z : ℂ ↦ U x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ)) :=
    continuous_const.mul (Complex.continuous_exp.comp
      ((continuous_id.sub continuous_const).mul continuous_const))
  refine continuousAt_of_dominated (bound := fun x ↦ C * (1 + x ^ 2)⁻¹) ?_ ?_
    (integrable_inv_one_add_sq.const_mul C) (.of_forall fun x ↦ (hcont x).continuousAt)
  · exact .of_forall fun z ↦ (hU.1.mul (Complex.continuous_exp.comp (continuous_const.mul
      Complex.continuous_ofReal))).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds z₀ one_pos] with z hz
    refine .of_forall fun x ↦ hb z ?_ x
    have h1 : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
      rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
    have h2 : ‖z - z₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
    calc |z.re - 1 / 2| = |(z.re - z₀.re) + (z₀.re - 1 / 2)| := by ring_nf
      _ ≤ |z.re - z₀.re| + |z₀.re - 1 / 2| := abs_add_le _ _
      _ ≤ |z₀.re - 1 / 2| + 1 := by linarith

private theorem isFullLineRapid_sub {U V : ℝ → ℂ} (hU : IsFullLineRapid U)
    (hV : IsFullLineRapid V) :
    IsFullLineRapid (U - V) := by
  refine ⟨hU.1.sub hV.1, fun M ↦ ?_⟩
  obtain ⟨C₁, hC₁, h₁⟩ := hU.2 M
  obtain ⟨C₂, hC₂, h₂⟩ := hV.2 M
  refine ⟨C₁ + C₂, by positivity, fun x ↦ ?_⟩
  rw [Pi.sub_apply]
  calc ‖U x - V x‖ ≤ ‖U x‖ + ‖V x‖ := norm_sub_le _ _
    _ ≤ C₁ * Real.exp (-M * |x|) + C₂ * Real.exp (-M * |x|) := add_le_add (h₁ x) (h₂ x)
    _ = (C₁ + C₂) * Real.exp (-M * |x|) := by ring

private theorem isFullLineRapid_smul (c : ℂ) {U : ℝ → ℂ} (hU : IsFullLineRapid U) :
    IsFullLineRapid (c • U) := by
  refine ⟨continuous_const.mul hU.1, fun M ↦ ?_⟩
  obtain ⟨C, hC, h⟩ := hU.2 M
  refine ⟨‖c‖ * C, by positivity, fun x ↦ ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h x) (norm_nonneg _)

private theorem isFullLineRapid_halfTwistLogDilate {q : ℕ} (hq : 0 < q) {U : ℝ → ℂ}
    (hU : IsFullLineRapid U) : IsFullLineRapid (halfTwistLogDilate q U) := by
  have hfun : halfTwistLogDilate q U = fun x ↦ (q : ℂ) ^ (-(1 / 2 : ℂ)) * U (x + Real.log q) := by
    funext x
    simp only [halfTwistLogDilate, hq.ne', ↓reduceIte, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hfun]
  refine ⟨continuous_const.mul (hU.1.comp (continuous_id.add continuous_const)), fun M ↦ ?_⟩
  obtain ⟨C, hC, h⟩ := hU.2 M
  refine ⟨‖(q : ℂ) ^ (-(1 / 2 : ℂ))‖ * (C * Real.exp (|M| * |Real.log q|)), by positivity,
    fun x ↦ ?_⟩
  rw [norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ((h (x + Real.log q)).trans ?_)
    (norm_nonneg ((q : ℂ) ^ (-(1 / 2 : ℂ))))
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 : |(|x + Real.log q| - |x|)| ≤ |Real.log q| := by
    simpa using abs_abs_sub_abs_le_abs_sub (x + Real.log q) x
  have h2 : -M * |x + Real.log q| ≤ -M * |x| + |M| * |Real.log q| := by
    have : -M * (|x + Real.log q| - |x|) ≤ |M| * |Real.log q| :=
      (le_abs_self _).trans (by
        rw [abs_mul, abs_neg]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
    linarith
  linarith

private theorem isFullLineRapid_depleteStepFun {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {q : ℕ} (hq : 0 < q) {U : ℝ → ℂ} (hU : IsFullLineRapid U) :
    IsFullLineRapid (depleteStepFun χ q U) :=
  isFullLineRapid_sub hU (isFullLineRapid_smul _ (isFullLineRapid_halfTwistLogDilate hq hU))

private theorem isFullLineRapid_dirichletDeplete' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, 0 < q) {U : ℝ → ℂ} (hU : IsFullLineRapid U) :
    IsFullLineRapid (dirichletDeplete χ T U) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using hU
  | insert q S hqS ih =>
    rw [dirichletDeplete_insert χ hqS, LinearMap.comp_apply]
    exact isFullLineRapid_depleteStepFun χ (hT q (Finset.mem_insert_self q S))
      (ih fun r hr ↦ hT r (Finset.mem_insert_of_mem hr))

end Rapid

/-! ### The functional equation and two-sided decay of the profile -/

section Profile

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- Paper: (11.3.1.3), p. 494, via twisted Poisson summation (`twisted_poisson_summation`).
**Functional equation of the half-logarithmic profile.**
`U_{χ,g}(x) = τ(χ) · N^{-1/2} · U_{χ⁻¹, 𝓕 g}(-x - log N)` for every Schwartz `g`. -/
theorem twistedHalfLogProfile_functional_eq (hχ : χ.IsPrimitive) (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    twistedHalfLogProfile χ g x =
      gaussSum χ ZMod.stdAddChar * (Real.exp (-(Real.log N) / 2) : ℂ) *
        twistedHalfLogProfile χ⁻¹ (𝓕 g) (-x - Real.log N) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hP := twisted_poisson_summation hχ g (Real.exp_pos x)
  rw [twistedHalfLogProfile, twistedHalfLogProfile, hP, twistedRadialTheta]
  have harg (m : ℤ) : (m : ℝ) / ((N : ℝ) * Real.exp x) = (m : ℝ) * Real.exp (-x - Real.log N) := by
    rw [Real.exp_sub, Real.exp_neg, Real.exp_log hNpos]; field_simp
  simp only [harg]
  have hreal : Real.exp (x / 2) / ((N : ℝ) * Real.exp x) =
      Real.exp (-(Real.log N) / 2) * Real.exp ((-x - Real.log N) / 2) := by
    rw [← Real.exp_add]
    rw [show -(Real.log N) / 2 + (-x - Real.log N) / 2 = x / 2 - (x + Real.log N) by ring,
      Real.exp_sub, Real.exp_add, Real.exp_log hNpos]
    ring
  have hc : (Real.exp (x / 2) : ℂ) * (gaussSum χ ZMod.stdAddChar / ((N : ℂ) * (Real.exp x : ℂ))) =
      gaussSum χ ZMod.stdAddChar * (Real.exp (-(Real.log N) / 2) : ℂ) *
        (Real.exp ((-x - Real.log N) / 2) : ℂ) := by
    have h := congrArg (fun r : ℝ ↦ (r : ℂ)) hreal
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast] at h
    rw [show (Real.exp (x / 2) : ℂ) * (gaussSum χ ZMod.stdAddChar / ((N : ℂ) * (Real.exp x : ℂ))) =
      gaussSum χ ZMod.stdAddChar * ((Real.exp (x / 2) : ℂ) / ((N : ℂ) * (Real.exp x : ℂ))) by
        ring, h]
    ring
  rw [← mul_assoc, hc]
  ring

private theorem isFullLineRapid_twistedHalfLogProfile (hχ : χ.IsPrimitive) (hN : 1 < N)
    (g : 𝓢(ℝ, ℂ)) : IsFullLineRapid (twistedHalfLogProfile χ g) := by
  refine ⟨twistedHalfLogProfile_continuous χ hN g, fun M ↦ ?_⟩
  obtain ⟨C₁, hC₁, h₁⟩ := twistedHalfLogProfile_decay χ hN g 0 M
  obtain ⟨C₂, hC₂, h₂⟩ := twistedHalfLogProfile_decay χ⁻¹ hN (𝓕 g) (-Real.log N) M
  let K : ℝ := ‖gaussSum χ ZMod.stdAddChar‖ * Real.exp (-(Real.log N) / 2) * C₂ *
    Real.exp (M * Real.log N)
  refine ⟨max C₁ K, by positivity, fun x ↦ ?_⟩
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact (h₁ x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · rw [twistedHalfLogProfile_functional_eq hχ g x, abs_of_neg hx, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hy := h₂ (-x - Real.log N) (by linarith)
    calc ‖gaussSum χ ZMod.stdAddChar‖ * Real.exp (-(Real.log N) / 2) *
          ‖twistedHalfLogProfile χ⁻¹ (𝓕 g) (-x - Real.log N)‖
        ≤ ‖gaussSum χ ZMod.stdAddChar‖ * Real.exp (-(Real.log N) / 2) *
            (C₂ * Real.exp (-M * (-x - Real.log N))) :=
          mul_le_mul_of_nonneg_left hy (by positivity)
      _ = K * Real.exp (-M * -x) := by
          simp only [K]
          rw [show -M * (-x - Real.log N) = M * Real.log N + -M * -x by ring, Real.exp_add]
          ring
      _ ≤ max C₁ K * Real.exp (-M * -x) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- **Two-sided rapid decay of depleted profiles.** For every Schwartz test `g` (no box, no
polarity needed: `χ(0) = 0`), every depleted profile `dirichletDeplete χ T U_χ(g)` decays faster
than every exponential at both ends. -/
theorem isFullLineRapid_dirichletDeplete (hχ : χ.IsPrimitive) (hN : 1 < N) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 0 < q) (g : 𝓢(ℝ, ℂ)) :
    IsFullLineRapid (dirichletDeplete χ T (twistedHalfLogProfile χ g)) :=
  isFullLineRapid_dirichletDeplete' χ T hT (isFullLineRapid_twistedHalfLogProfile hχ hN g)

private theorem halfTwistMellin_halfTwistLogDilate' {q : ℕ} (hq : 0 < q) (U : ℝ → ℂ) (z : ℂ) :
    halfTwistMellin (halfTwistLogDilate q U) z = (q : ℂ) ^ (-z) * halfTwistMellin U z := by
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  rw [halfTwistMellin, halfTwistMellin]
  have hfun : (fun x : ℝ ↦ halfTwistLogDilate q U x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))) =
      fun x : ℝ ↦ ((q : ℂ) ^ (-z)) *
        (U (x + Real.log q) * Complex.exp ((z - 1 / 2 : ℂ) * ((x + Real.log q : ℝ) : ℂ))) := by
    ext x
    simp only [halfTwistLogDilate, hq.ne', ↓reduceIte, LinearMap.coe_mk, AddHom.coe_mk]
    have hlogq : Complex.exp ((z - 1 / 2 : ℂ) * ((Real.log q : ℝ) : ℂ)) =
        (q : ℂ) ^ (z - 1 / 2) := by
      rw [← Complex.ofReal_natCast q,
        Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hqp.ne'),
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

private theorem halfTwistMellin_depleteStepFun' (χ : DirichletCharacter ℂ N) {q : ℕ} (hq : 0 < q)
    {U : ℝ → ℂ} (hU : IsFullLineRapid U) (z : ℂ) :
    halfTwistMellin (depleteStepFun χ q U) z =
      (1 - χ q * (q : ℂ) ^ (-z)) * halfTwistMellin U z := by
  have h1 := hU.integrable_mellin z
  have h2 :=
    (isFullLineRapid_smul (χ q) (isFullLineRapid_halfTwistLogDilate hq hU)).integrable_mellin z
  have hsplit : halfTwistMellin (depleteStepFun χ q U) z =
      halfTwistMellin U z - χ q * halfTwistMellin (halfTwistLogDilate q U) z := by
    rw [halfTwistMellin]
    have hfun : (fun x : ℝ ↦ depleteStepFun χ q U x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))) =
        fun x : ℝ ↦ U x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ)) -
          (χ q • halfTwistLogDilate q U) x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ)) := by
      ext x
      simp [depleteStepFun, sub_mul]
    rw [hfun, integral_sub h1 h2, halfTwistMellin]
    have hsm : (fun x : ℝ ↦
        (χ q • halfTwistLogDilate q U) x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))) =
        fun x : ℝ ↦ χ q * (halfTwistLogDilate q U x * Complex.exp ((z - 1 / 2 : ℂ) * (x : ℂ))) := by
      ext x; simp [mul_assoc]
    rw [hsm, integral_const_mul, halfTwistMellin]
  rw [hsplit, halfTwistMellin_halfTwistLogDilate' hq U z]
  ring

/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496, without a box.
**The Euler factor of the next prime.** For every Schwartz `g`, the full-line Mellin transform of
the depleted profile at the stage `insert p T` is `1 - χ(p) p^{-z}` times that at stage `T`. -/
theorem halfTwistMellin_dirichletDeplete_insert (hχ : χ.IsPrimitive) (hN : 1 < N) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 0 < q) {p : ℕ} (hp : 0 < p) (hpT : p ∉ T) (g : 𝓢(ℝ, ℂ)) (z : ℂ) :
    halfTwistMellin (dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g)) z =
      (1 - χ p * (p : ℂ) ^ (-z)) *
        halfTwistMellin (dirichletDeplete χ T (twistedHalfLogProfile χ g)) z := by
  rw [dirichletDeplete_insert χ hpT, LinearMap.comp_apply,
    halfTwistMellin_depleteStepFun' χ hp (isFullLineRapid_dirichletDeplete hχ hN T hT g) z]

/-- **Full-line Mellin factorization without a box**: the full-line Mellin transform of
`dirichletDeplete χ T U_χ(g)` is `dirichletStageMultiplier χ T z` times that of `U_χ(g)`. -/
theorem halfTwistMellin_dirichletDeplete_full (hχ : χ.IsPrimitive) (hN : 1 < N) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 0 < q) (g : 𝓢(ℝ, ℂ)) (z : ℂ) :
    halfTwistMellin (dirichletDeplete χ T (twistedHalfLogProfile χ g)) z =
      dirichletStageMultiplier χ T z * halfTwistMellin (twistedHalfLogProfile χ g) z := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [dirichletStageMultiplier]
  | insert q S hqS ih =>
    have hS : ∀ r ∈ S, 0 < r := fun r hr ↦ hT r (Finset.mem_insert_of_mem hr)
    rw [halfTwistMellin_dirichletDeplete_insert hχ hN S hS (hT q (Finset.mem_insert_self q S)) hqS,
      ih hS, dirichletStageMultiplier, dirichletStageMultiplier, Finset.prod_insert hqS]
    ring

/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
**Deliverable 1.** For every Schwartz `g` and a prime `p ∤ N` outside `T`, the full-line Mellin
transform of the depleted profile at stage `insert p T` converges on the imaginary axis and
vanishes at every point `z_j = i · dirichletPrimeFreq χ p j`. -/
theorem halfTwistMellin_nextStage_primeFreq (hχ : χ.IsPrimitive) (hN : 1 < N) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 0 < q) {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    (g : 𝓢(ℝ, ℂ)) (j : ℤ) :
    Integrable (fun x : ℝ ↦ dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g) x *
        Complex.exp (((dirichletPrimeFreq χ p j : ℂ) * Complex.I - 1 / 2 : ℂ) * (x : ℂ))) ∧
      halfTwistMellin (dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g))
        ((dirichletPrimeFreq χ p j : ℂ) * Complex.I) = 0 := by
  have hT' : ∀ q ∈ insert p T, 0 < q := fun q hq ↦ by
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp.pos
    · exact hT q hq
  refine ⟨(isFullLineRapid_dirichletDeplete hχ hN _ hT' g).integrable_mellin _, ?_⟩
  rw [halfTwistMellin_dirichletDeplete_insert hχ hN T hT hp.pos hpT,
    show -((dirichletPrimeFreq χ p j : ℂ) * Complex.I) = -(dirichletPrimeFreq χ p j : ℂ) * Complex.I
      from (neg_mul _ _).symm, dirichlet_mul_cpow_primeFreq_eq_one χ hp hpN j, sub_self, zero_mul]

end Profile


/-! ### Rows of box tests and the next stage -/

section Rows

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

private theorem depleted_box_support (hχ : χ.IsPrimitive) (hN : 1 < N) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 0 < q) {X : ℝ} (hX : 0 < X) {f₀ : 𝓢(ℝ, ℂ)}
    (hf₀ : IsDirichletFixedBoxTest χ (X / ∏ q ∈ T, (q : ℝ)) f₀) (x : ℝ)
    (hx : x < -Real.log ((N : ℝ) * X)) :
    dirichletDeplete χ T (twistedHalfLogProfile χ f₀) x = 0 := by
  rw [← twistedHalfLogProfile_dirichletTestDeplete χ T hT f₀]
  exact dirichletFixedBox_support_lower_bound hχ hN hX
    (isDirichletFixedBoxTest_dirichletTestDeplete T hT hX.le hf₀) hx

/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
**Deliverable 2.** On the `T`-depleted profile of a box test (outer box `X`, profile supported on
`[B, ∞)`, `B = -log (N X)`), the normalized row is the inverse row scalar times the full-line
(`k`-th moment) Mellin integral at `i t_j`. -/
theorem dirichletNormalizedRow_eq_fullLine (hχ : χ.IsPrimitive) (hN : 1 < N) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 0 < q) (p : ℕ) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    {f₀ : 𝓢(ℝ, ℂ)} (hf₀ : IsDirichletFixedBoxTest χ (X / ∏ q ∈ T, (q : ℝ)) f₀)
    (hmem : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) 2
      (intervalSobolevMeasure volume id (-α) α s false)) (j : ℤ) :
    dirichletNormalizedRow χ T p X α s hα hs j (toDirichletStrip α s _ hmem) =
      (dirichletRowScalar χ T p j)⁻¹ *
        ∫ x : ℝ,
          (x : ℂ) ^ (if dirichletPrimeFreq χ p j = 0 then dirichletStageZeroOrder χ T else 0) *
          dirichletDeplete χ T (twistedHalfLogProfile χ f₀) x *
            Complex.exp (((dirichletPrimeFreq χ p j : ℂ) * Complex.I - 1 / 2 : ℂ) * (x : ℂ)) := by
  change ((dirichletRowScalar χ T p j)⁻¹ • halfLineMellinJet α s (-Real.log ((N : ℝ) * X)) hα hs
    (if dirichletPrimeFreq χ p j = 0 then dirichletStageZeroOrder χ T else 0)
    (dirichletPrimeFreq χ p j)) (toDirichletStrip α s _ hmem) = _
  rw [smul_apply, smul_eq_mul,
    halfLineMellinJet_apply α s _ hα hs _ _ (depleted_box_support hχ hN T hT hX hf₀) hmem]

/-- At a nonzero frequency the row is the inverse row scalar times the full-line Mellin
transform. -/
theorem dirichletNormalizedRow_eq_halfTwistMellin (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, 0 < q) (p : ℕ) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α)
    (hs : 0 ≤ s) {f₀ : 𝓢(ℝ, ℂ)} (hf₀ : IsDirichletFixedBoxTest χ (X / ∏ q ∈ T, (q : ℝ)) f₀)
    (hmem : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) 2
      (intervalSobolevMeasure volume id (-α) α s false)) (j : ℤ)
    (hj : dirichletPrimeFreq χ p j ≠ 0) :
    dirichletNormalizedRow χ T p X α s hα hs j (toDirichletStrip α s _ hmem) =
      (dirichletRowScalar χ T p j)⁻¹ *
        halfTwistMellin (dirichletDeplete χ T (twistedHalfLogProfile χ f₀))
          ((dirichletPrimeFreq χ p j : ℂ) * Complex.I) := by
  rw [dirichletNormalizedRow_eq_fullLine hχ hN T hT p hX hα hs hf₀ hmem j,
    ite_eq_right_of_eq_false _ _ (eq_false hj), halfTwistMellin]
  simp only [pow_zero, one_mul]

private theorem stageMultiplier_ne_zero_of_re_pos (χ : DirichletCharacter ℂ N) (T : Finset ℕ)
    (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N) {z : ℂ} (hz : 0 < z.re) :
    dirichletStageMultiplier χ T z ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun q hq ↦ sub_ne_zero.mpr fun h ↦ ?_
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (hT q hq).1.one_lt
  have hn := congrArg norm h
  rw [norm_one, norm_mul, dirichlet_norm_apply_eq_one_of_coprime χ (hT q hq).2, one_mul,
    Complex.norm_natCast_cpow_of_pos (hT q hq).1.pos, Complex.neg_re] at hn
  have : (q : ℝ) ^ (-z.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  linarith

/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
**Deliverable 3: rows vanish on the next stage.** If the `T`-depleted profile of a box test `f₀`
equals the `insert p T`-depleted profile of some Schwartz test `g` (an element of the
unrestricted next stage), then every normalized row of `f₀` at the prime `p` vanishes.
(The cut-off row need not vanish on profiles without a box; this is not claimed.) -/
theorem ratBridge_nextStage_rows_zero (hχ : χ.IsPrimitive) (hN : 1 < N) (T : Finset ℕ)
    (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N) {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N)
    (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) {f₀ : 𝓢(ℝ, ℂ)}
    (hf₀ : IsDirichletFixedBoxTest χ (X / ∏ q ∈ T, (q : ℝ)) f₀) (g : 𝓢(ℝ, ℂ))
    (hfg : ∀ x, dirichletDeplete χ T (twistedHalfLogProfile χ f₀) x =
      dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g) x)
    (hmem : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) 2
      (intervalSobolevMeasure volume id (-α) α s false)) (j : ℤ) :
    dirichletNormalizedRow χ T p X α s hα hs j (toDirichletStrip α s _ hmem) = 0 := by
  have hTpos : ∀ q ∈ T, 0 < q := fun q hq ↦ (hT q hq).1.pos
  have hX' : 0 < X / ∏ q ∈ T, (q : ℝ) :=
    div_pos hX (Finset.prod_pos fun q hq ↦ by exact_mod_cast (hT q hq).1.pos)
  have hrow := dirichletNormalizedRow_apply_depleted hχ hN T hT hp hpN hpT hX hα hs hf₀ j
  refine hrow.trans ?_
  set t := dirichletPrimeFreq χ p j
  -- the Mellin identity off the imaginary axis
  let F : ℂ → ℂ := fun z ↦ halfTwistMellin (twistedHalfLogProfile χ f₀) z -
    (1 - χ p * (p : ℂ) ^ (-z)) * halfTwistMellin (twistedHalfLogProfile χ g) z
  have hFc : Continuous F := by
    refine ((isFullLineRapid_twistedHalfLogProfile hχ hN f₀).continuous_mellin).sub
      ((continuous_const.sub (continuous_const.mul ?_)).mul
        (isFullLineRapid_twistedHalfLogProfile hχ hN g).continuous_mellin)
    exact continuous_neg.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hp.ne_zero))
  have hzero (ε : ℝ) (hε : 0 < ε) : F ((t : ℂ) * Complex.I + ε) = 0 := by
    set z : ℂ := (t : ℂ) * Complex.I + ε
    have hzre : 0 < z.re := by simp [z, hε]
    have hB := stageMultiplier_ne_zero_of_re_pos χ T hT hzre
    have h1 := halfTwistMellin_dirichletDeplete χ hN T hTpos hX' hf₀ hχ z
    have h2 : halfTwistMellin (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) z =
        halfTwistMellin (dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g)) z := by
      rw [show dirichletDeplete χ T (twistedHalfLogProfile χ f₀) =
        dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g) from funext hfg]
    rw [halfTwistMellin_dirichletDeplete_insert hχ hN T hTpos hp.pos hpT,
      halfTwistMellin_dirichletDeplete_full hχ hN T hTpos g z] at h2
    rw [h1] at h2
    have h3 : dirichletStageMultiplier χ T z * F z = 0 := by
      simp only [F]
      rw [mul_sub, h2]
      ring
    exact (mul_eq_zero.mp h3).resolve_left hB
  have hFt : F ((t : ℂ) * Complex.I) = 0 := by
    have hlim : Tendsto (fun ε : ℝ ↦ F ((t : ℂ) * Complex.I + ε)) (𝓝[>] 0)
        (𝓝 (F ((t : ℂ) * Complex.I + ((0 : ℝ) : ℂ)))) :=
      ((hFc.comp (continuous_const.add Complex.continuous_ofReal)).tendsto 0).mono_left
        nhdsWithin_le_nhds
    have hev : (fun ε : ℝ ↦ F ((t : ℂ) * Complex.I + ε)) =ᶠ[𝓝[>] 0] fun _ ↦ 0 :=
      eventually_nhdsWithin_of_forall fun ε hε ↦ hzero ε hε
    have h := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hev.symm)
    rwa [Complex.ofReal_zero, add_zero] at h
  have hM : halfTwistMellin (twistedHalfLogProfile χ f₀) ((t : ℂ) * Complex.I) = 0 := by
    have h := hFt
    simp only [F] at h
    rw [show -((t : ℂ) * Complex.I) = -(t : ℂ) * Complex.I from (neg_mul _ _).symm,
      dirichlet_mul_cpow_primeFreq_eq_one χ hp hpN j, sub_self, zero_mul, sub_zero] at h
    exact h
  rw [dirichletFixedBox_mellin_eq_imagAxis hχ hN hX' hf₀ t] at hM
  have hχinv_ne : χ⁻¹ ≠ 1 := (dirichlet_inv_isPrimitive_ne_one hχ hN).2
  have hgauss : gaussSum χ ZMod.stdAddChar ≠ 0 := by
    intro h0
    have hnorm := DirichletCharacter.norm_gaussSum_stdAddChar hχ
    rw [h0, norm_zero] at hnorm
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
    linarith [Real.sqrt_pos.mpr hNpos]
  have hNpow : (N : ℂ) ^ (-(t : ℂ) * Complex.I) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne N)))
  have hL : DirichletCharacter.LFunction χ⁻¹ (1 - (t : ℂ) * Complex.I) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχinv_ne)
      (by simp [Complex.sub_re, Complex.mul_re])
  exact (mul_eq_zero.mp hM).resolve_left
    (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hgauss) hNpow) hL)

private theorem toDirichletStrip_congr {α s : ℝ} {U V : ℝ → ℂ} (h : U = V)
    (hU : MemLp U 2 (intervalSobolevMeasure volume id (-α) α s false))
    (hV : MemLp V 2 (intervalSobolevMeasure volume id (-α) α s false)) :
    toDirichletStrip α s U hU = toDirichletStrip α s V hV := by
  subst h
  rfl

/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
**Deliverable 3, membership.** Under the hypotheses of `ratBridge_nextStage_rows_zero`, the
`T`-depleted profile of the box test lies in the stage space `dirichletStageSpace χ (insert p T) X`
(by `dirichletFixedBox_stage_exact_division`). -/
theorem ratBridge_nextStage_mem_stageSpace (hχ : χ.IsPrimitive) (hN : 1 < N) (T : Finset ℕ)
    (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N) {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N)
    (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) {f₀ : 𝓢(ℝ, ℂ)}
    (hf₀ : IsDirichletFixedBoxTest χ (X / ∏ q ∈ T, (q : ℝ)) f₀) (g : 𝓢(ℝ, ℂ))
    (hfg : ∀ x, dirichletDeplete χ T (twistedHalfLogProfile χ f₀) x =
      dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g) x)
    (hmem : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) 2
      (intervalSobolevMeasure volume id (-α) α s false)) :
    toDirichletStrip α s _ hmem ∈ dirichletStageSpace χ (insert p T) X α s hα hs := by
  have hTpos : ∀ q ∈ T, 0 < q := fun q hq ↦ (hT q hq).1.pos
  have hdiv := dirichletFixedBox_stage_exact_division hχ hN T hT hp hpN hpT hX hα hs hf₀
  obtain ⟨g₀, hg₀, hstep⟩ := hdiv.mpr fun j ↦
    ratBridge_nextStage_rows_zero hχ hN T hT hp hpN hpT hX hα hs hf₀ g hfg _ j
  have hbox : IsDirichletFixedBoxTest χ (X / ∏ q ∈ insert p T, (q : ℝ)) g₀ := by
    rwa [Finset.prod_insert hpT]
  -- the profile of `f₀ = (I - χ(p) D_p) g₀`
  have hstepU : twistedHalfLogProfile χ f₀ = depleteStepFun χ p (twistedHalfLogProfile χ g₀) := by
    rw [← hstep]
    have h1 := twistedHalfLogProfile_dirichletTestDeplete χ {p} (fun q hq ↦ by
      rw [Finset.mem_singleton.mp hq]; exact hp.pos) g₀
    rw [show dirichletTestDeplete χ {p} = testDepleteStep χ p from
      Finset.noncommProd_singleton _ _] at h1
    rw [h1, show ({p} : Finset ℕ) = insert p ∅ from rfl, dirichletDeplete_insert χ
      (Finset.notMem_empty p), dirichletDeplete_empty, LinearMap.comp_id]
  have hcomm : Commute (depleteStepFun χ p) (dirichletDeplete χ T) :=
    Finset.noncommProd_commute _ _ _ _ fun q _ ↦ depleteStepFun_comm χ p q
  have heq : dirichletDeplete χ T (twistedHalfLogProfile χ f₀) =
      dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g₀) := by
    rw [hstepU, dirichletDeplete_insert χ hpT, LinearMap.comp_apply, ← mul_apply_eq_comp,
      ← hcomm.eq, mul_apply_eq_comp]
  have hmem' : MemLp (dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g₀)) 2
      (intervalSobolevMeasure volume id (-α) α s false) := heq ▸ hmem
  rw [toDirichletStrip_congr heq hmem hmem']
  exact mem_dirichletStageSpace_of_test (insert p T) hα hs hbox hmem'

end Rows

end RiemannMasullo.Isolated
