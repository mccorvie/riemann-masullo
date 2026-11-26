module

public import RiemannMasullo.Ch13_ZerosHecke.DirichletZeroDisplacement
import RiemannMasullo.ForMathlib.NumberTheory.PolyaVinogradov

/-!
# Conductor-sharpened displacement bounds for Dirichlet L-function zeros

Inserting the Pólya–Vinogradov bound `‖∑_{j=1}^n χ₀ j‖ ≤ √f * log f` for the associated primitive
character `χ₀` of conductor `f = χ.conductor` into `dirichletLFunction_finite_zero_product` cuts
the leading conductor dependence of `dirichletLFunction_right_zero_displacement` in half (from
`2 * log q` to `log χ.conductor + O(log log χ.conductor)`), while replacing the ambient modulus `q`
by `χ.conductor` for every nonprincipal character `χ` modulo `q` (including imprimitive ones).

Combining this with the sharp Euler-product lower bound `π² / 15 ≤ ‖χ₀.LFunction c‖` on `Re c = 2`
improves `dirichletLFunction_right_zero_displacement_at_height` from `2 * log (4 * q * ‖c‖)` to
`log χ.conductor + 2 * log (30 / π² * log χ.conductor * ‖c‖)`.
-/

open Set Filter Function MeasureTheory Metric
open scoped Topology BigOperators ComplexConjugate

public noncomputable section

namespace RiemannMasullo

local notation "Lprim(" χ ")" =>
  @DirichletCharacter.LFunction _ (NeZero.mk (DirichletCharacter.conductor_ne_zero χ))
    (DirichletCharacter.primitiveCharacter χ)

private theorem dirichletConductor_euler_factor_ne_zero {f : ℕ} (χ₀ : DirichletCharacter ℂ f)
    (q : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ∏ p ∈ q.primeFactors, (1 - χ₀ p * (p : ℂ) ^ (-s)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hlt : ‖χ₀ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hpr.pos, Complex.neg_re]
    have h1 : ‖χ₀ p‖ ≤ 1 := χ₀.norm_le_one p
    have h2 : (p : ℝ) ^ (-s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpr.one_lt) (neg_lt_zero.mpr hs)
    have h20 : 0 ≤ (p : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    exact (mul_le_of_le_one_left h20 h1).trans_lt h2
  exact sub_ne_zero.mpr fun heq ↦ hlt.ne (by rw [← heq, norm_one])

private theorem dirichletConductor_euler_analyticAt {f : ℕ} (χ₀ : DirichletCharacter ℂ f)
    (q : ℕ) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ ↦ ∏ p ∈ q.primeFactors, (1 - χ₀ p * (p : ℂ) ^ (-z))) s := by
  have hprod : ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime) →
      AnalyticAt ℂ (fun z : ℂ ↦ ∏ p ∈ T, (1 - χ₀ p * (p : ℂ) ^ (-z))) s := by
    intro T hT
    induction T using Finset.induction_on with
    | empty => simpa using analyticAt_const (v := (1 : ℂ))
    | insert p T hpnot ih =>
      have hp : p.Prime := hT p (Finset.mem_insert_self p T)
      have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      have hfactor : AnalyticAt ℂ (fun z : ℂ ↦ 1 - χ₀ p * (p : ℂ) ^ (-z)) s := by
        have hcpow : AnalyticAt ℂ (fun z : ℂ ↦ Complex.exp (Complex.log (p : ℂ) * (-z))) s :=
          (analyticAt_const.fun_mul analyticAt_id.neg).cexp
        have heq : (fun z : ℂ ↦ 1 - χ₀ p * (p : ℂ) ^ (-z)) =
            fun z : ℂ ↦ 1 - χ₀ p * Complex.exp (Complex.log (p : ℂ) * (-z)) := by
          funext z
          rw [Complex.cpow_def_of_ne_zero hp0 (-z)]
        rw [heq]
        exact analyticAt_const.sub (analyticAt_const.fun_mul hcpow)
      have hrest := ih fun r hr ↦ hT r (Finset.mem_insert_of_mem hr)
      simpa only [Finset.prod_insert hpnot] using hfactor.fun_mul hrest
  exact hprod q.primeFactors fun p hp ↦ Nat.prime_of_mem_primeFactors hp

/-- A nonprincipal Dirichlet character and its associated primitive character have identical zeros
and analytic multiplicities everywhere in the open right half-plane `Re s > 0`. -/
theorem dirichletLFunction_zero_order_eq_primitive {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    (χ.LFunction s = 0 ↔ Lprim(χ) s = 0) ∧
      analyticOrderNatAt χ.LFunction s = analyticOrderNatAt Lprim(χ) s := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set χ₀ := χ.primitiveCharacter with hχ₀_def
  have hχ₀_ne : χ₀ ≠ 1 := by
    intro h1
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, ← hχ₀_def, h1, DirichletCharacter.changeLevel_one]
  by_cases hs1 : s = 1
  · subst hs1
    have hL1 : χ.LFunction 1 ≠ 0 := DirichletCharacter.LFunction_apply_one_ne_zero hχ
    have hL01 : χ₀.LFunction 1 ≠ 0 := DirichletCharacter.LFunction_apply_one_ne_zero hχ₀_ne
    have ha1 : AnalyticAt ℂ χ.LFunction 1 :=
      (DirichletCharacter.differentiable_LFunction hχ).analyticAt 1
    have ha01 : AnalyticAt ℂ χ₀.LFunction 1 :=
      (DirichletCharacter.differentiable_LFunction hχ₀_ne).analyticAt 1
    have ho1 : analyticOrderNatAt χ.LFunction 1 = 0 := by
      simp [analyticOrderNatAt, ha1.analyticOrderAt_eq_zero.mpr hL1]
    have ho01 : analyticOrderNatAt χ₀.LFunction 1 = 0 := by
      simp [analyticOrderNatAt, ha01.analyticOrderAt_eq_zero.mpr hL01]
    exact ⟨⟨fun h ↦ absurd h hL1, fun h ↦ absurd h hL01⟩, ho1.trans ho01.symm⟩
  · let E : ℂ → ℂ := fun z ↦ ∏ p ∈ q.primeFactors, (1 - χ₀ p * (p : ℂ) ^ (-z))
    have hE_ne : E s ≠ 0 := dirichletConductor_euler_factor_ne_zero χ₀ q hs
    have hEa : AnalyticAt ℂ E s := dirichletConductor_euler_analyticAt χ₀ q s
    have hLa : AnalyticAt ℂ χ.LFunction s :=
      (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
    have hL0a : AnalyticAt ℂ χ₀.LFunction s :=
      (DirichletCharacter.differentiable_LFunction hχ₀_ne).analyticAt s
    have hev : χ.LFunction =ᶠ[𝓝 s] fun z ↦ χ₀.LFunction z * E z := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
      have hcl := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ₀ (.inr hz)
      rwa [χ.changeLevel_primitiveCharacter] at hcl
    have hpt : χ.LFunction s = χ₀.LFunction s * E s := hev.self_of_nhds
    have hiff : χ.LFunction s = 0 ↔ χ₀.LFunction s = 0 := by
      rw [hpt, mul_eq_zero]
      exact ⟨fun h ↦ h.resolve_right hE_ne, fun h ↦ Or.inl h⟩
    have hord : analyticOrderAt χ.LFunction s = analyticOrderAt χ₀.LFunction s := by
      rw [analyticOrderAt_congr hev, analyticOrderAt_fun_mul hL0a hEa,
        hEa.analyticOrderAt_eq_zero.mpr hE_ne, add_zero]
    exact ⟨hiff, congrArg ENat.toNat hord⟩

/-- **Pólya–Vinogradov zero-displacement bound for primitive characters.**
For a nonprincipal primitive character modulo `q` and any interior anchor `Re c > 1/2` with
`χ.LFunction c ≠ 0`, the weighted displacements of right-hand zeros sum to at most
`log q + 2 * log (2 * log q / ‖χ.LFunction c / c‖)`. -/
theorem dirichletLFunction_primitive_right_zero_displacement {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (c : ℂ) (hc : 1 / 2 < c.re) (hv : χ.LFunction c ≠ 0) :
    let Z := {ρ : ℂ // 1 / 2 < ρ.re ∧ χ.LFunction ρ = 0}
    let w (ρ : Z) := (analyticOrderNatAt χ.LFunction ρ.val : ℝ) *
      ((2 * ρ.val.re - 1) * (2 * c.re - 1) / ‖ρ.val + conj c - 1‖ ^ 2)
    Summable w ∧
      ∑' ρ, w ρ ≤ Real.log q + 2 * Real.log (2 * Real.log q / ‖χ.LFunction c / c‖) := by
  intro Z w
  let b (ρ : Z) := ‖ρ.val - c‖ / ‖ρ.val + conj c - 1‖
  let m (ρ : Z) := analyticOrderNatAt χ.LFunction ρ.val
  have hq3 : 3 ≤ q := DirichletCharacter.three_le_of_ne_one hχ
  have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hsqrt_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq_pos
  have hlog_pos : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hc₀ : c ≠ 0 := fun e ↦ by norm_num [e] at hc
  have hv₀ : 0 < ‖χ.LFunction c / c‖ := norm_pos_iff.mpr (div_ne_zero hv hc₀)
  have hd (ρ : Z) : 0 < ‖ρ.val + conj c - 1‖ := by
    apply norm_pos_iff.mpr
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re,
      Complex.zero_re] at he
    linarith [ρ.property.1]
  have hb (ρ : Z) : 0 < b ρ := by
    refine div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr ?_)) (hd ρ)
    intro e
    exact hv (e ▸ ρ.property.2)
  have hn (ρ : Z) : 0 ≤ w ρ := by
    dsimp only [w]
    exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg
      (mul_nonneg (by linarith [ρ.property.1]) (by linarith)) (sq_nonneg _))
  have hweight (ρ : Z) : w ρ = (m ρ : ℝ) * (1 - b ρ ^ 2) := by
    dsimp only [w, m, b]
    have hsq : ‖ρ.val + conj c - 1‖ ^ 2 - ‖ρ.val - c‖ ^ 2 =
        (2 * ρ.val.re - 1) * (2 * c.re - 1) := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.add_re,
        Complex.conj_re, Complex.one_re, Complex.sub_im, Complex.add_im, Complex.conj_im,
        Complex.one_im]
      ring
    rw [← hsq, div_pow, sub_div, div_self (pow_ne_zero _ (hd ρ).ne')]
  set K := Real.log q + 2 * Real.log (2 * Real.log q / ‖χ.LFunction c / c‖)
  have hK_eq : K = 2 * Real.log (2 * (Real.sqrt q * Real.log q) / ‖χ.LFunction c / c‖) := by
    dsimp [K]
    have hnum_pos : 0 < 2 * Real.log q / ‖χ.LFunction c / c‖ := by positivity
    rw [show 2 * (Real.sqrt q * Real.log q) / ‖χ.LFunction c / c‖ =
      Real.sqrt q * (2 * Real.log q / ‖χ.LFunction c / c‖) by ring,
      Real.log_mul hsqrt_pos.ne' hnum_pos.ne', Real.log_sqrt hq_pos.le]
    ring
  have hf (S : Finset Z) : ∑ ρ ∈ S, w ρ ≤ K := by
    rw [hK_eq]
    have hp := dirichletLFunction_finite_zero_product χ hχ
      (DirichletCharacter.polyaVinogradov_primitive χ hprim hχ) c hc hv S
    change ‖χ.LFunction c / c‖ ≤
      (2 * (Real.sqrt q * Real.log q)) * ∏ ρ ∈ S, b ρ ^ m ρ at hp
    have hB2_pos : 0 < 2 * (Real.sqrt q * Real.log q) := by positivity
    have hpn (ρ : Z) (_ : ρ ∈ S) := pow_ne_zero (m ρ) (hb ρ).ne'
    have hlog := Real.log_le_log hv₀ hp
    rw [Real.log_mul hB2_pos.ne' (Finset.prod_ne_zero_iff.mpr hpn), Real.log_prod hpn] at hlog
    simp only [Real.log_pow] at hlog
    have hcomp : ∑ ρ ∈ S, w ρ ≤ ∑ ρ ∈ S, (-2) * ((m ρ : ℝ) * Real.log (b ρ)) := by
      apply Finset.sum_le_sum
      intro ρ _
      have h := Real.log_le_sub_one_of_pos (sq_pos_of_pos (hb ρ))
      rw [Real.log_pow, Nat.cast_ofNat] at h
      rw [hweight]
      calc (m ρ : ℝ) * (1 - b ρ ^ 2)
          ≤ (m ρ : ℝ) * (-(2 * Real.log (b ρ))) :=
            mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
        _ = (-2) * ((m ρ : ℝ) * Real.log (b ρ)) := by ring
    rw [← Finset.mul_sum] at hcomp
    rw [Real.log_div hB2_pos.ne' hv₀.ne']
    linarith
  exact ⟨summable_of_sum_le hn hf, Real.tsum_le_of_sum_le hn hf⟩

/-- **Conductor-sharpened zero-displacement bound for arbitrary nonprincipal characters.**
For any nonprincipal Dirichlet character `χ` modulo `q` (primitive or imprimitive) and any
anchor `Re c > 1/2` where `χ.primitiveCharacter.LFunction c ≠ 0` (in particular whenever
`χ.LFunction c ≠ 0`), the weighted right-hand zero sum is bounded in terms of `χ.conductor` alone,
with leading coefficient `1` on `log χ.conductor`. -/
theorem dirichletLFunction_right_zero_displacement_conductor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (c : ℂ) (hc : 1 / 2 < c.re)
    (hv : Lprim(χ) c ≠ 0) :
    let Z := {ρ : ℂ // 1 / 2 < ρ.re ∧ χ.LFunction ρ = 0}
    let w (ρ : Z) := (analyticOrderNatAt χ.LFunction ρ.val : ℝ) *
      ((2 * ρ.val.re - 1) * (2 * c.re - 1) / ‖ρ.val + conj c - 1‖ ^ 2)
    Summable w ∧
      ∑' ρ, w ρ ≤ Real.log χ.conductor +
        2 * Real.log (2 * Real.log χ.conductor / ‖Lprim(χ) c / c‖) := by
  intro Z w
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set χ₀ := χ.primitiveCharacter with hχ₀_def
  have hχ₀_ne : χ₀ ≠ 1 := by
    intro h1
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, ← hχ₀_def, h1, DirichletCharacter.changeLevel_one]
  let Z₀ := {ρ : ℂ // 1 / 2 < ρ.re ∧ χ₀.LFunction ρ = 0}
  let w₀ (ρ : Z₀) := (analyticOrderNatAt χ₀.LFunction ρ.val : ℝ) *
    ((2 * ρ.val.re - 1) * (2 * c.re - 1) / ‖ρ.val + conj c - 1‖ ^ 2)
  obtain ⟨hs₀, hb₀⟩ := dirichletLFunction_primitive_right_zero_displacement χ₀
    χ.primitiveCharacter_isPrimitive hχ₀_ne c hc hv
  let e : Z ≃ Z₀ :=
    { toFun := fun ρ ↦ ⟨ρ.val, ρ.property.1,
        (dirichletLFunction_zero_order_eq_primitive χ hχ (by linarith [ρ.property.1])).1.mp
          ρ.property.2⟩
      invFun := fun ρ ↦ ⟨ρ.val, ρ.property.1,
        (dirichletLFunction_zero_order_eq_primitive χ hχ (by linarith [ρ.property.1])).1.mpr
          ρ.property.2⟩
      left_inv := fun _ ↦ Subtype.ext rfl
      right_inv := fun _ ↦ Subtype.ext rfl }
  have hw_eq : w = w₀ ∘ e := by
    funext ρ
    dsimp [w, w₀, e]
    rw [(dirichletLFunction_zero_order_eq_primitive χ hχ (by linarith [ρ.property.1])).2]
  rw [hw_eq]
  exact ⟨e.summable_iff.mpr hs₀, (e.tsum_eq w₀).trans_le hb₀⟩

/-- **Conductor-sharpened displacement bound at the anchor `1`**, valid unconditionally for every
nonprincipal character modulo `q` (including imprimitive characters). -/
theorem dirichletLFunction_right_zero_displacement_conductor_at_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    let Z := {ρ : ℂ // 1 / 2 < ρ.re ∧ χ.LFunction ρ = 0}
    let w (ρ : Z) := (analyticOrderNatAt χ.LFunction ρ.val : ℝ) *
      ((2 * ρ.val.re - 1) / ‖ρ.val‖ ^ 2)
    Summable w ∧
      ∑' ρ, w ρ ≤ Real.log χ.conductor +
        2 * Real.log (2 * Real.log χ.conductor / ‖Lprim(χ) 1‖) := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hχ₀_ne : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h1, DirichletCharacter.changeLevel_one]
  simpa [show (2 : ℝ) - 1 = 1 by norm_num] using
    dirichletLFunction_right_zero_displacement_conductor χ hχ 1 (by norm_num)
      (DirichletCharacter.LFunction_apply_one_ne_zero hχ₀_ne)

/-- **Conductor-sharpened and Euler-sharpened displacement bound on `Re c = 2`.**
Uniformly for every nonprincipal character `χ` modulo `q` (primitive or imprimitive) and every `c`
with `Re c = 2`, the weighted right-hand zero sum is at most
`log χ.conductor + 2 * log (30 / π² * log χ.conductor * ‖c‖)` (improving both `2 * log q` to
`log χ.conductor` and `4` to `30 / π² ≈ 3.0396`). -/
theorem dirichletLFunction_right_zero_displacement_conductor_at_height {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (c : ℂ) (hc : c.re = 2) :
    let Z := {ρ : ℂ // 1 / 2 < ρ.re ∧ χ.LFunction ρ = 0}
    let w (ρ : Z) := (analyticOrderNatAt χ.LFunction ρ.val : ℝ) *
      ((2 * ρ.val.re - 1) * 3 / ‖ρ.val + conj c - 1‖ ^ 2)
    Summable w ∧
      ∑' ρ, w ρ ≤ Real.log χ.conductor +
        2 * Real.log (30 / Real.pi ^ 2 * Real.log χ.conductor * ‖c‖) := by
  intro Z w
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hlb := pi_sq_div_fifteen_le_norm_LFunction_of_re_eq_two χ.primitiveCharacter hc
  have hlb_pos : 0 < Real.pi ^ 2 / 15 := by positivity
  have hv : χ.primitiveCharacter.LFunction c ≠ 0 := norm_pos_iff.mp (hlb_pos.trans_le hlb)
  have hc₀ : c ≠ 0 := fun e ↦ by simp [e] at hc
  have hc_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc₀
  have hf3 : 3 ≤ χ.conductor := DirichletCharacter.three_le_conductor_of_ne_one hχ
  have hlog_pos : 0 < Real.log χ.conductor := Real.log_pos (by exact_mod_cast (by omega : 1 < χ.conductor))
  obtain ⟨hs, hb⟩ := dirichletLFunction_right_zero_displacement_conductor χ hχ c (by linarith) hv
  have he : 2 * c.re - 1 = 3 := by rw [hc]; norm_num
  rw [he] at hs hb
  refine ⟨hs, hb.trans (add_le_add_right (mul_le_mul_of_nonneg_left (Real.log_le_log ?_ ?_)
    (by positivity : (0 : ℝ) ≤ 2)) _)⟩
  · exact div_pos (by positivity) (norm_pos_iff.mpr (div_ne_zero hv hc₀))
  · rw [norm_div, div_div_eq_mul_div, div_le_iff₀ (hlb_pos.trans_le hlb)]
    have hmul := mul_le_mul_of_nonneg_left hlb
      (by positivity : 0 ≤ 30 / Real.pi ^ 2 * Real.log χ.conductor * ‖c‖)
    have hcancel : 30 / Real.pi ^ 2 * Real.log χ.conductor * ‖c‖ * (Real.pi ^ 2 / 15) =
        2 * Real.log χ.conductor * ‖c‖ := by
      field_simp [Real.pi_ne_zero]
      ring
    linarith

end RiemannMasullo
