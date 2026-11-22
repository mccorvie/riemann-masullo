module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3b
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # §5.3.3: the printed logarithmic change of exponent interval -/

@[expose] public noncomputable section

open Set
open scoped NNReal

namespace RiemannMasullo

/-- Paper: Example 5.3.3.1, p. 249. The change of variable t = exp x is
claimed to identify the log(I)-decay space on ℝ with the I-decay space on
the positive multiplicative reals as topological complex vector spaces.
Deviation: The page allows any nonempty connected real interval. We record
the coordinate-change assertion where its real logarithm is defined on all
of I. The repaired statement is `positiveRealExponentialDecay_log_equiv`.
See ERRATA F176. -/
def Printed.positiveRealExponentialDecay_log_equiv : Prop :=
  ∀ (I : Set ℝ), OrdConnected I → I.Nonempty → I ⊆ Ioi 0 →
    ∃ e : PositiveRealExponentialDecay (Real.log '' I) ≃L[ℂ]
        ModulatedExponentialDecay (ContinuousMonoidHom.id ℝ≥0ˣ) I,
      ∀ f t, (e f).val t = f.val (Real.log (t.val : ℝ))

/-- For `c > 0`, the profile `exp(cx − eˣ)` decays polynomially at both ends of the line. -/
private theorem positiveRealExponentialDecay_log_equiv_false_bound (c : ℝ) (hc : 0 < c) (k : ℕ) :
    ∃ C, ∀ x : ℝ, |x| ^ k * Real.exp (c * x - Real.exp x) ≤ C := by
  obtain ⟨m, hm⟩ := exists_nat_gt (c + 1)
  have h1 : (0 : ℝ) ≤ k.factorial / c ^ k := by positivity
  have h2 : (0 : ℝ) ≤ m.factorial * k.factorial := by positivity
  refine ⟨k.factorial / c ^ k + m.factorial * k.factorial, fun x ↦ ?_⟩
  rcases le_total x 0 with hx | hx
  · have hexp := Real.pow_div_factorial_le_exp _ (mul_nonneg hc.le (neg_nonneg.2 hx)) k
    rw [div_le_iff₀ (by positivity)] at hexp
    have hle : |x| ^ k * Real.exp (c * x - Real.exp x) ≤ k.factorial / c ^ k := by
      rw [abs_of_nonpos hx, le_div_iff₀ (by positivity)]
      calc (-x) ^ k * Real.exp (c * x - Real.exp x) * c ^ k
          ≤ (-x) ^ k * Real.exp (c * x) * c ^ k := by
            gcongr
            · exact pow_nonneg (neg_nonneg.2 hx) k
            · linarith [Real.exp_pos x]
        _ = (c * -x) ^ k * Real.exp (c * x) := by ring
        _ ≤ (Real.exp (c * -x) * k.factorial) * Real.exp (c * x) := by gcongr
        _ = k.factorial := by
            rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]
            simp
    linarith
  · have hA : x ^ k ≤ k.factorial * Real.exp x := by
      have := Real.pow_div_factorial_le_exp _ hx k
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have hB : Real.exp (m * x) ≤ m.factorial * Real.exp (Real.exp x) := by
      have := Real.pow_div_factorial_le_exp _ (Real.exp_pos x).le m
      rw [div_le_iff₀ (by positivity), ← Real.exp_nat_mul] at this
      linarith
    have hC : Real.exp (c * x - Real.exp x) ≤
        Real.exp (m * x) * Real.exp (-x) * Real.exp (-Real.exp x) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith
    have hle : |x| ^ k * Real.exp (c * x - Real.exp x) ≤ m.factorial * k.factorial := by
      rw [abs_of_nonneg hx]
      calc x ^ k * Real.exp (c * x - Real.exp x)
          ≤ (k.factorial * Real.exp x) *
              (Real.exp (m * x) * Real.exp (-x) * Real.exp (-Real.exp x)) := by gcongr
        _ ≤ (k.factorial * Real.exp x) *
              ((m.factorial * Real.exp (Real.exp x)) * Real.exp (-x) * Real.exp (-Real.exp x)) := by
            gcongr
        _ = m.factorial * k.factorial *
              (Real.exp (x + -x) * Real.exp (Real.exp x + -Real.exp x)) := by
            rw [Real.exp_add, Real.exp_add]; ring
        _ = m.factorial * k.factorial := by simp
    linarith

/-- The derivative of `exp(cx − eˣ)` is `c exp(cx − eˣ) − exp((c + 1)x − eˣ)`. -/
private theorem positiveRealExponentialDecay_log_equiv_false_hasDerivAt (c x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (Real.exp (c * y - Real.exp y) : ℂ))
      ((c : ℂ) * Real.exp (c * x - Real.exp x) - Real.exp ((c + 1) * x - Real.exp x)) x := by
  have h := (((hasDerivAt_id x).const_mul c).sub (Real.hasDerivAt_exp x)).exp.ofReal_comp
  refine h.congr_deriv ?_
  show ((Real.exp (c * x - Real.exp x) * (c * 1 - Real.exp x) : ℝ) : ℂ) = _
  rw [show (c + 1) * x - Real.exp x = (c * x - Real.exp x) + x by ring, Real.exp_add]
  push_cast
  ring

private theorem positiveRealExponentialDecay_log_equiv_false_contDiff (c : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun y : ℝ ↦ (Real.exp (c * y - Real.exp y) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul contDiff_id).sub Real.contDiff_exp).exp

/-- Every derivative of `exp(cx − eˣ)`, for `c > 0`, decays polynomially. -/
private theorem positiveRealExponentialDecay_log_equiv_false_iteratedDeriv (n : ℕ) :
    ∀ c : ℝ, 0 < c → ∀ k : ℕ, ∃ C, ∀ x : ℝ,
      |x| ^ k * ‖iteratedDeriv n (fun y : ℝ ↦ (Real.exp (c * y - Real.exp y) : ℂ)) x‖ ≤ C := by
  induction n with
  | zero =>
    intro c hc k
    obtain ⟨C, hC⟩ := positiveRealExponentialDecay_log_equiv_false_bound c hc k
    refine ⟨C, fun x ↦ ?_⟩
    rw [iteratedDeriv_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hC x
  | succ n ih =>
    intro c hc k
    obtain ⟨C₁, hC₁⟩ := ih c hc k
    obtain ⟨C₂, hC₂⟩ := ih (c + 1) (by linarith) k
    refine ⟨|c| * C₁ + C₂, fun x ↦ ?_⟩
    have hd : deriv (fun y : ℝ ↦ (Real.exp (c * y - Real.exp y) : ℂ)) =
        fun y : ℝ ↦ (c : ℂ) • (Real.exp (c * y - Real.exp y) : ℂ) -
          (Real.exp ((c + 1) * y - Real.exp y) : ℂ) := by
      funext y
      rw [(positiveRealExponentialDecay_log_equiv_false_hasDerivAt c y).deriv]
      simp
    rw [iteratedDeriv_succ', hd,
      iteratedDeriv_fun_sub
        (ContDiff.const_smul (c : ℂ)
          (positiveRealExponentialDecay_log_equiv_false_contDiff c)).contDiffAt
        (positiveRealExponentialDecay_log_equiv_false_contDiff (c + 1)).contDiffAt,
      iteratedDeriv_fun_const_smul
        (positiveRealExponentialDecay_log_equiv_false_contDiff c).contDiffAt]
    have hn : ‖(c : ℂ)‖ = |c| := Complex.norm_real c
    calc |x| ^ k * ‖(c : ℂ) • iteratedDeriv n (fun y : ℝ ↦ (Real.exp (c * y - Real.exp y) : ℂ)) x -
          iteratedDeriv n (fun y : ℝ ↦ (Real.exp ((c + 1) * y - Real.exp y) : ℂ)) x‖
        ≤ |x| ^ k * (|c| * ‖iteratedDeriv n (fun y : ℝ ↦ (Real.exp (c * y - Real.exp y) : ℂ)) x‖ +
          ‖iteratedDeriv n (fun y : ℝ ↦ (Real.exp ((c + 1) * y - Real.exp y) : ℂ)) x‖) := by
          gcongr
          refine (norm_sub_le _ _).trans ?_
          rw [norm_smul, hn]
      _ = |c| * (|x| ^ k * ‖iteratedDeriv n (fun y : ℝ ↦ (Real.exp (c * y - Real.exp y) : ℂ)) x‖) +
          |x| ^ k * ‖iteratedDeriv n (fun y : ℝ ↦ (Real.exp ((c + 1) * y - Real.exp y) : ℂ)) x‖ := by
          ring
      _ ≤ |c| * C₁ + C₂ := by gcongr; exacts [hC₁ x, hC₂ x]

/-- For `c > 0`, the profile `exp(cx − eˣ)` is a Schwartz function on the line. -/
private theorem positiveRealExponentialDecay_log_equiv_false_schwartz (c : ℝ) (hc : 0 < c) :
    ∃ S : SchwartzMap ℝ ℂ, ∀ x, S x = (Real.exp (c * x - Real.exp x) : ℂ) :=
  ⟨⟨fun y : ℝ ↦ (Real.exp (c * y - Real.exp y) : ℂ),
    positiveRealExponentialDecay_log_equiv_false_contDiff c, fun k n ↦ by
      obtain ⟨C, hC⟩ := positiveRealExponentialDecay_log_equiv_false_iteratedDeriv n c hc k
      exact ⟨C, fun x ↦ by
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
        exact hC x⟩⟩, fun _ ↦ rfl⟩

/-- The profile `exp(−x − eˣ)`, i.e. `t⁻¹ exp(−t)` in `t = eˣ`, decays at every
exponent above `1`. -/
private theorem positiveRealExponentialDecay_log_equiv_false_mem :
    (fun x : ℝ ↦ (Real.exp (-1 * x - Real.exp x) : ℂ)) ∈
      logExponentialDecaySubmodule (Ioo 1 2) := by
  refine (Submodule.mem_iInf _).2 fun a ↦ Submodule.mem_comap.2 ?_
  obtain ⟨S, hS⟩ := positiveRealExponentialDecay_log_equiv_false_schwartz ((a : ℝ) - 1)
    (by linarith [a.2.1])
  refine ⟨S, funext fun x ↦ ?_⟩
  rw [realSchwartzCoe_apply, hS, logExponentialWeight, LinearMap.mulLeft_apply, Pi.mul_apply]
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

/-- At the exponent `1/2` the profile `exp(−x − eˣ)` has the weighted profile
`exp(−x/2 − eˣ)`, which is unbounded as `x → −∞` and so is not a Schwartz function. -/
private theorem positiveRealExponentialDecay_log_equiv_false_unbounded (S : SchwartzMap ℝ ℂ)
    (F : ℝ → ℂ) (hF : ∀ x, F x = (Real.exp (-1 * x - Real.exp x) : ℂ))
    (hS' : realSchwartzCoe S = logExponentialWeight (1 / 2) F) : False := by
  obtain ⟨C, -, hC⟩ := S.decay 0 0
  have hx := hC (-2 * (|C| + 2))
  have hSx := congrFun hS' (-2 * (|C| + 2))
  rw [realSchwartzCoe_apply] at hSx
  rw [pow_zero, one_mul, norm_iteratedFDeriv_zero, hSx, logExponentialWeight,
    LinearMap.mulLeft_apply, Pi.mul_apply, hF, ← Complex.ofReal_mul, ← Real.exp_add, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hx
  have hle : Real.exp (-2 * (|C| + 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [abs_nonneg C])
  have h3 : |C| + 1 ≤ (1 / 2 : ℝ) * (-2 * (|C| + 2)) + (-1 * (-2 * (|C| + 2)) -
      Real.exp (-2 * (|C| + 2))) := by linarith
  have h5 := Real.add_one_le_exp (|C| + 1)
  have h6 := Real.exp_le_exp.2 h3
  linarith [le_abs_self C]


/-- Transport along a map with a right inverse, stated for bare functions so that no
instance of the decay spaces has to be unified. -/
private theorem positiveRealExponentialDecay_log_equiv_false_transfer {A B : Type*}
    (φ : A → B) (ψ : B → A) (hφψ : ∀ b, φ (ψ b) = b) (vA : A → ℝ → ℂ) (vB : B → ℝ≥0ˣ → ℂ)
    (hφ : ∀ a t, vB (φ a) t = vA a (Real.log (t.val : ℝ))) (b : B) (t : ℝ≥0ˣ) (x : ℝ)
    (hx : Real.log (t.val : ℝ) = x) : vA (ψ b) x = vB b t := by
  rw [← hx, ← hφ, hφψ]

/-- Paper: Example 5.3.3.1, p. 249. Take I = (1, 2) and f(x) = η(x) exp(−x),
where η is smooth, zero on x ≤ 0 and one on x ≥ 1. For each a in (0, log 2),
the twist exp(ax)f(x) is Schwartz. For a = 3/2 the target twist of f(log t)
equals t^(1/2) for t ≥ exp 1 and fails even the order-zero Schwartz bound. -/
theorem Printed.positiveRealExponentialDecay_log_equiv_false :
    ¬ Printed.positiveRealExponentialDecay_log_equiv := by
  intro h
  have hne : (Ioo (1 : ℝ) 2).Nonempty := ⟨3 / 2, by norm_num, by norm_num⟩
  obtain ⟨e, he⟩ := h (Ioo 1 2) ordConnected_Ioo hne fun x hx ↦ lt_trans one_pos hx.1
  obtain ⟨e₂, he₂⟩ := identityModulationExponentialDecay_equiv (Ioo 1 2) ordConnected_Ioo hne
  let g : PositiveRealExponentialDecay (Ioo 1 2) :=
    ⟨_, positiveRealExponentialDecay_log_equiv_false_mem⟩
  let u : ℝ → ℝ≥0ˣ := fun x ↦ Units.mk0 (Real.exp x).toNNReal (by positivity)
  have hu (x : ℝ) : Real.log ((u x).val : ℝ) = x := by
    simp [u, Real.coe_toNNReal _ (Real.exp_pos x).le]
  -- The printed equivalence sends `e.symm (e₂ g)` to the same profile as `g`.
  have hval (x : ℝ) : (e.symm (e₂ g)).val x = (Real.exp (-1 * x - Real.exp x) : ℂ) := by
    have h1 := positiveRealExponentialDecay_log_equiv_false_transfer (⇑e) (⇑e.symm)
      e.apply_symm_apply
      (fun f : PositiveRealExponentialDecay (Real.log '' Ioo 1 2) ↦ (f.val : ℝ → ℂ))
      (fun f : ModulatedExponentialDecay (ContinuousMonoidHom.id ℝ≥0ˣ) (Ioo 1 2) ↦
        (f.val : ℝ≥0ˣ → ℂ)) he (e₂ g) (u x) x (hu x)
    refine h1.trans ((he₂ g (u x)).trans ?_)
    rw [hu]
  -- Hence this profile decays at the exponent `1/2 ∈ log (1, 2)`, which it does not.
  have hhalf : (1 / 2 : ℝ) ∈ Real.log '' Ioo 1 2 := by
    refine ⟨Real.exp (1 / 2), ⟨by simp, ?_⟩, Real.log_exp _⟩
    have h4 : Real.exp (1 / 2) * Real.exp (1 / 2) < 2 * 2 := by
      rw [← Real.exp_add]; norm_num; linarith [Real.exp_one_lt_d9]
    nlinarith [Real.exp_pos (1 / 2)]
  obtain ⟨S, hS⟩ := logExponentialDecay_weight_mem_range _ ⟨1 / 2, hhalf⟩ (e.symm (e₂ g))
  exact positiveRealExponentialDecay_log_equiv_false_unbounded S _ hval hS

end RiemannMasullo
