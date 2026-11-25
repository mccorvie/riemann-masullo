module

public import Mathlib.NumberTheory.LSeries.Injectivity
public import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Rigidity of a rational shift difference of an ordinary Dirichlet series

An absolutely convergent ordinary Dirichlet series with vanishing coefficient at one decays
exponentially along the real ray. If its difference under translation by two is rational there,
the difference is zero, and iteration followed by Dirichlet-series uniqueness kills all coefficients.
-/

@[expose] public noncomputable section

open Filter Complex Polynomial
open scoped Topology

namespace RiemannMasullo.DirichletShift

private theorem polynomial_zero_of_tendsto {p : ℂ[X]}
    (h : Tendsto (fun x : ℝ ↦ p.eval (x : ℂ)) atTop (𝓝 0)) : p = 0 := by
  by_cases hd : 0 < p.degree
  · have hlarge := p.tendsto_norm_atTop hd (z := fun x : ℝ ↦ (x : ℂ)) (by
      simpa using tendsto_abs_atTop_atTop)
    have hsmall := h.norm
    rw [norm_zero] at hsmall
    obtain ⟨x, hx, hy⟩ := ((hlarge.eventually_gt_atTop 2).and
      (hsmall.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))).exists
    linarith
  · have he := Polynomial.eq_C_of_degree_le_zero (le_of_not_gt hd)
    rw [he] at h
    have hc : p.coeff 0 = 0 := by simpa using h
    rw [he, hc, map_zero]

private theorem polynomial_mul_exp_neg {b : ℝ} (hb : 0 < b) (p : ℂ[X]) :
    Tendsto (fun x : ℝ ↦ p.eval (x : ℂ) * (Real.exp (-b * x) : ℂ)) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | monomial n c =>
    have hl := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) b hb).ofReal
    simp only [Real.rpow_natCast, Complex.ofReal_zero, Complex.ofReal_mul, Complex.ofReal_pow] at hl
    simpa [Polynomial.eval_monomial, mul_assoc] using hl.const_mul c
  | add p q hp hq => simpa [add_mul] using hp.add hq

/-- Multiplication by any polynomial preserves decay of a Dirichlet series with vanishing
constant coefficient and some half-plane of absolute convergence. -/
private theorem polynomial_mul_lseries_tendsto_zero {a : ℕ → ℂ}
    (ha : LSeries.abscissaOfAbsConv a < ⊤) (h0 : a 0 = 0) (h1 : a 1 = 0) (p : ℂ[X]) :
    Tendsto (fun x : ℝ ↦ p.eval (x : ℂ) * LSeries a x) atTop (𝓝 0) := by
  have ht := LSeries.tendsto_cpow_mul_atTop (n := 1) (f := a) (by
    intro m hm
    interval_cases m <;> assumption) ha
  have he (x : ℝ) : (2 : ℂ) ^ (x : ℂ) = (Real.exp (Real.log 2 * x) : ℂ) := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_cpow (by norm_num : 0 ≤ (2 : ℝ)),
      Real.rpow_def_of_pos (by norm_num)]
  norm_num only [Nat.cast_one, one_add_one_eq_two] at ht
  simp_rw [he] at ht
  have h := (polynomial_mul_exp_neg (Real.log_pos (by norm_num : 1 < (2 : ℝ))) p).mul ht
  rw [zero_mul] at h
  apply h.congr
  intro x
  simp only [neg_mul, Real.exp_neg, Complex.ofReal_inv]
  field_simp

/-- Equality to a rational function for all sufficiently large real arguments. -/
def RayRational (f : ℝ → ℂ) : Prop :=
  ∃ p q : ℂ[X], q ≠ 0 ∧ ∀ᶠ x : ℝ in atTop, f x * q.eval (x : ℂ) = p.eval (x : ℂ)

namespace RayRational

theorem congr {f g : ℝ → ℂ} (hf : RayRational f) (h : f =ᶠ[atTop] g) : RayRational g := by
  obtain ⟨p,q,hq,he⟩ := hf
  exact ⟨p,q,hq,he.mp (h.mono fun x hx h ↦ hx ▸ h)⟩

theorem const (c : ℂ) : RayRational (fun _ : ℝ ↦ c) :=
  ⟨C c, 1, one_ne_zero, by simp⟩

theorem add {f g : ℝ → ℂ} (hf : RayRational f) (hg : RayRational g) :
    RayRational (fun x ↦ f x + g x) := by
  obtain ⟨p,q,hq,he⟩ := hf
  obtain ⟨r,t,ht,hd⟩ := hg
  refine ⟨p*t + r*q, q*t, mul_ne_zero hq ht, ?_⟩
  filter_upwards [he,hd] with x hx hy
  simp only [eval_mul, eval_add, ← hx, ← hy]
  ring

theorem const_mul (c : ℂ) {f : ℝ → ℂ} (hf : RayRational f) :
    RayRational (fun x ↦ c * f x) := by
  obtain ⟨p,q,hq,he⟩ := hf
  refine ⟨C c * p,q,hq,?_⟩
  filter_upwards [he] with x hx
  simp [mul_assoc, hx]

theorem sub {f g : ℝ → ℂ} (hf : RayRational f) (hg : RayRational g) :
    RayRational (fun x ↦ f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add (const_mul (-1) hg)

theorem sum {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ S, RayRational (f i)) : RayRational (fun x ↦ ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using const 0
  | insert i S hi ih =>
    simpa [hi] using (hf i (by simp)).add (ih fun j hj ↦ hf j (by simp [hj]))

/-- A simple pole may be anywhere in the complex plane. -/
theorem inv_sub (w : ℂ) : RayRational (fun x : ℝ ↦ 1 / ((x : ℂ) - w)) := by
  refine ⟨1, X-C w, X_sub_C_ne_zero w, ?_⟩
  filter_upwards [eventually_gt_atTop w.re] with x hx
  have hn : (x : ℂ) - w ≠ 0 := fun he ↦ hx.ne' (congrArg Complex.re (sub_eq_zero.mp he))
  simp [hn]

end RayRational

private theorem eventually_eval_ne_zero {q : ℂ[X]} (hq : q ≠ 0) :
    ∀ᶠ x : ℝ in atTop, q.eval (x : ℂ) ≠ 0 := by
  by_cases hd : 0 < q.degree
  · have ht := q.tendsto_norm_atTop hd (z := fun x : ℝ ↦ (x : ℂ)) (by simpa using tendsto_abs_atTop_atTop)
    exact (ht.eventually_gt_atTop 0).mono fun _ h ↦ norm_pos_iff.mp h
  · have he := Polynomial.eq_C_of_degree_le_zero (le_of_not_gt hd)
    have hcoef : q.coeff 0 ≠ 0 := fun h ↦ hq (he.trans (by simp [h]))
    filter_upwards with x
    rw [he, eval_C]
    exact hcoef

/-- A shift difference of an absolutely convergent ordinary Dirichlet series with
zero constant coefficient can be rational on the real ray only when every coefficient vanishes.
All possible poles and their coincidences are allowed. -/
theorem lseries_shift_rational_rigidity (a : ℕ → ℂ) (ha : LSeries.abscissaOfAbsConv a < ⊤)
    (h0 : a 0 = 0) (h1 : a 1 = 0)
    (hid : RayRational (fun x : ℝ ↦ LSeries a x - LSeries a ((x : ℂ) + 2))) :
    ∀ n, a n = 0 := by
  obtain ⟨p,q,hq,hid⟩ := hid
  have hf := polynomial_mul_lseries_tendsto_zero ha h0 h1
  have hplus : Tendsto (fun x : ℝ ↦ x + 2) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have htrans := (hf (q.comp (X - C 2))).comp hplus
  have ht : Tendsto (fun x : ℝ ↦ q.eval (x : ℂ) * LSeries a ((x : ℂ) + 2)) atTop (𝓝 0) := by
    simpa [Function.comp_def, Polynomial.eval_comp] using htrans
  have hn : Tendsto (fun x : ℝ ↦ p.eval (x : ℂ)) atTop (𝓝 0) := by
    have hg := (hf q).sub ht
    rw [sub_zero] at hg
    apply hg.congr'
    filter_upwards [hid] with x hx
    rw [← hx]
    ring
  have hp := polynomial_zero_of_tendsto hn
  have hper : ∀ᶠ x : ℝ in atTop, LSeries a ((x : ℂ) + 2) = LSeries a (x : ℂ) := by
    filter_upwards [hid, eventually_eval_ne_zero hq] with x hx hxq
    rw [hp, eval_zero] at hx
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_right hxq)).symm
  obtain ⟨M, hM⟩ := eventually_atTop.1 hper
  have hlim := LSeries.tendsto_atTop ha
  rw [h1] at hlim
  have hzero : (fun x : ℝ ↦ LSeries a x) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_ge_atTop M] with x hx
    have hconst (n : ℕ) : LSeries a ((x + 2 * n : ℝ) : ℂ) = LSeries a x := by
      induction n with
      | zero => simp
      | succ n h =>
        have hstep := hM (x + 2 * n) (by linarith [show (0 : ℝ) ≤ n by positivity])
        rw [← h]
        convert hstep using 2
        push_cast
        ring
    have hgo : Tendsto (fun n : ℕ ↦ x + 2 * (n : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ _ ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    exact tendsto_nhds_unique tendsto_const_nhds ((hlim.comp hgo).congr hconst)
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · exact h0
  · exact (LSeries_eventually_eq_zero_iff'.1 hzero).resolve_right ha.ne n hn

end RiemannMasullo.DirichletShift
