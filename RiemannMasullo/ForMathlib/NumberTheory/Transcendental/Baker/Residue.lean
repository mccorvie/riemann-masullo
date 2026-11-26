module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.OfScalars

/-! # Taylor expansion, residues on circles and the interpolation bound

Ported from HOL Light, Baker/residue.ml (jrh13/hol-light, commit 1a0c0e6). -/

@[expose] public section

namespace RiemannMasullo.Baker

open Finset Metric Function
open scoped Nat Real Topology

/-! ### Taylor expansion with holomorphic remainder -/

private theorem residue_iterate_dslope_expansion (f : ℂ → ℂ) (a : ℂ) (k : ℕ) (z : ℂ) :
    f z = ∑ j ∈ range k, ((swap dslope a)^[j] f) a * (z - a) ^ j +
      (z - a) ^ k * ((swap dslope a)^[k] f) z := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := sub_smul_dslope ((swap dslope a)^[k] f) a z
    rw [smul_eq_mul] at h
    rw [Finset.sum_range_succ, Function.iterate_succ_apply', pow_succ]
    change f z = _ + (z - a) ^ k * (z - a) * dslope ((swap dslope a)^[k] f) a z
    rw [ih]
    linear_combination -(z - a) ^ k * h

private theorem residue_iterate_dslope_self (f : ℂ → ℂ) (a : ℂ) (hf : AnalyticAt ℂ f a) (j : ℕ) :
    ((swap dslope a)^[j] f) a = iteratedDeriv j f a / (j ! : ℂ) := by
  have hp := hf.hasFPowerSeriesAt
  have h := (hp.has_fpower_series_iterate_dslope_fslope j).coeff_zero 1
  rw [← h, ← FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope,
    zero_add, FormalMultilinearSeries.coeff_ofScalars]

private theorem residue_iterate_dslope_differentiableOn (f : ℂ → ℂ) (s : Set ℂ) (a : ℂ)
    (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) (ha : a ∈ s) (k : ℕ) :
    DifferentiableOn ℂ ((swap dslope a)^[k] f) s := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (Complex.differentiableOn_dslope (hs.mem_nhds ha)).2 ih

/-- HOL Light: Baker/residue.ml, HOLOMORPHIC_TAYLOR_EXPANSION. A function holomorphic on an open
set is its Taylor polynomial of degree `n` at `a` plus `(z - a) ^ (n + 1)` times a function
holomorphic on the same set. -/
theorem holomorphic_taylor_expansion (f : ℂ → ℂ) (s : Set ℂ) (a : ℂ) (n : ℕ)
    (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) (ha : a ∈ s) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g s ∧
      ∀ z ∈ s, f z = ∑ j ∈ Finset.range (n + 1),
          iteratedDeriv j f a / (j ! : ℂ) * (z - a) ^ j +
        (z - a) ^ (n + 1) * g z := by
  refine ⟨(swap dslope a)^[n + 1] f,
    residue_iterate_dslope_differentiableOn f s a hs hf ha _, fun z _ => ?_⟩
  have hfa : AnalyticAt ℂ f a := hf.analyticAt (hs.mem_nhds ha)
  rw [residue_iterate_dslope_expansion f a (n + 1) z]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [residue_iterate_dslope_self f a hfa j]

/-! ### Residues of principal parts on a circle -/

private theorem residue_not_mem_of_mem_sphere {s : Finset ℂ} {c : ℂ} {r : ℝ}
    (hs : ∀ a ∈ s, ‖a - c‖ < r) {z : ℂ} (hz : z ∈ sphere c r) : z ∉ s := by
  intro hzs
  have := hs z hzs
  rw [mem_sphere_iff_norm] at hz
  linarith

private theorem residue_singular_parts_circlepath (h : ℂ → ℂ) (R : ℂ → ℂ → ℂ) (i : ℂ → ℂ)
    (s : Finset ℂ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hs : ∀ a ∈ s, ‖a - c‖ < r)
    (hR : ∀ a ∈ s, DifferentiableOn ℂ (R a) {a}ᶜ ∧ (∮ z in C(c, r), R a z) = i a)
    (hg : ∀ a ∈ s, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (↑(s.erase a) : Set ℂ)ᶜ ∧
      ∀ z, z ∉ s → h z = R a z + g z)
    (hh : DifferentiableOn ℂ h (↑s : Set ℂ)ᶜ) :
    (∮ z in C(c, r), h z) = ∑ a ∈ s, i a := by
  choose! g hg using hg
  let E : ℂ → ℂ := fun z =>
    if z ∈ s then g z z - ∑ b ∈ s.erase z, R b z else h z - ∑ b ∈ s, R b z
  have hE : Differentiable ℂ E := by
    intro z0
    by_cases hz : z0 ∈ s
    · have hopen : IsOpen ((↑(s.erase z0) : Set ℂ)ᶜ) :=
        (s.erase z0).finite_toSet.isClosed.isOpen_compl
      have hmem : z0 ∈ ((↑(s.erase z0) : Set ℂ)ᶜ) := by simp
      have hd : DifferentiableOn ℂ (fun z => g z0 z - ∑ b ∈ s.erase z0, R b z)
          ((↑(s.erase z0) : Set ℂ)ᶜ) := by
        refine (hg z0 hz).1.sub (DifferentiableOn.fun_sum fun b hb => ?_)
        refine (hR b (Finset.mem_of_mem_erase hb)).1.mono fun z hz' => ?_
        rintro rfl
        exact hz' hb
      refine (hd.differentiableAt (hopen.mem_nhds hmem)).congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hmem] with z hz'
      by_cases hzs : z ∈ s
      · have hzz : z = z0 := by
          by_contra hne
          exact hz' (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hne, hzs⟩))
        subst hzz
        simp [E, hzs]
      · simp only [E, hzs, ite_false]
        rw [(hg z0 hz).2 z hzs, ← Finset.add_sum_erase s _ hz]
        ring
    · have hopen : IsOpen ((↑s : Set ℂ)ᶜ) := s.finite_toSet.isClosed.isOpen_compl
      have hmem : z0 ∈ ((↑s : Set ℂ)ᶜ) := by simpa using hz
      have hd : DifferentiableOn ℂ (fun z => h z - ∑ b ∈ s, R b z) ((↑s : Set ℂ)ᶜ) := by
        refine hh.sub (DifferentiableOn.fun_sum fun b hb => ?_)
        refine (hR b hb).1.mono fun z hz' => ?_
        rintro rfl
        exact hz' hb
      refine (hd.differentiableAt (hopen.mem_nhds hmem)).congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hmem] with z hz'
      have hzs : z ∉ s := by simpa using hz'
      simp [E, hzs]
  have hRint : ∀ b ∈ s, CircleIntegrable (R b) c r := fun b hb =>
    ContinuousOn.circleIntegrable hr.le ((hR b hb).1.continuousOn.mono fun z hz => by
      rintro rfl
      exact residue_not_mem_of_mem_sphere hs hz hb)
  have hEint : CircleIntegrable E c r := hE.continuous.continuousOn.circleIntegrable hr.le
  have hcongr : (∮ z in C(c, r), h z) = ∮ z in C(c, r), E z + ∑ b ∈ s, R b z := by
    refine circleIntegral.integral_congr hr.le fun z hz => ?_
    have hzs : z ∉ s := residue_not_mem_of_mem_sphere hs hz
    simp [E, hzs]
  have hsum : CircleIntegrable (fun z => ∑ b ∈ s, R b z) c r := by
    have := CircleIntegrable.sum s hRint
    convert this using 1
    funext z
    simp
  rw [hcongr, circleIntegral.integral_add hEint hsum, circleIntegral.integral_fun_sum hRint,
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le
      Set.countable_empty hE.continuous.continuousOn (fun z _ => hE z), zero_add]
  exact Finset.sum_congr rfl fun b hb => (hR b hb).2

private theorem residue_principal_part_integral (q : ℕ → ℂ) (m : ℕ) (hm : 1 ≤ m) (a c : ℂ)
    (r : ℝ) (hr : 0 < r) (ha : ‖a - c‖ < r) :
    (∮ z in C(c, r), ∑ j ∈ Finset.range (m - 1 + 1), q j * ((z - a)⁻¹) ^ (m - j)) =
      2 * π * Complex.I * q (m - 1) := by
  have hball : a ∈ ball c r := mem_ball_iff_norm.2 ha
  have hne : ∀ z ∈ sphere c r, z - a ≠ 0 := fun z hz h0 => by
    rw [sub_eq_zero] at h0
    subst h0
    rw [mem_sphere_iff_norm] at hz
    linarith
  have hint : ∀ j ∈ Finset.range (m - 1 + 1),
      CircleIntegrable (fun z => q j * ((z - a)⁻¹) ^ (m - j)) c r := fun j _ =>
    ContinuousOn.circleIntegrable hr.le (continuousOn_const.mul
      (((continuousOn_id.sub continuousOn_const).inv₀ hne).pow _))
  rw [circleIntegral.integral_fun_sum hint]
  have hterm : ∀ j ∈ Finset.range (m - 1 + 1),
      (∮ z in C(c, r), q j * ((z - a)⁻¹) ^ (m - j)) =
        if j = m - 1 then 2 * π * Complex.I * q (m - 1) else 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [circleIntegral.integral_const_mul]
    split_ifs with hjm
    · subst hjm
      have h1 : m - (m - 1) = 1 := by omega
      simp only [h1, pow_one]
      rw [circleIntegral.integral_sub_inv_of_mem_ball hball]
      ring
    · have hfun : (fun z : ℂ => ((z - a)⁻¹) ^ (m - j)) =
          fun z : ℂ => (z - a) ^ (-((m - j : ℕ) : ℤ)) := by
        funext z
        rw [zpow_neg, zpow_natCast, inv_pow]
      have hn : (-((m - j : ℕ) : ℤ)) ≠ -1 := by omega
      have h0 := circleIntegral.integral_sub_zpow_of_ne hn c a r
      rw [show (∮ z in C(c, r), ((z - a)⁻¹) ^ (m - j)) =
        ∮ z in C(c, r), (z - a) ^ (-((m - j : ℕ) : ℤ)) from by rw [hfun], h0, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (m - 1 + 1)) (m - 1)]
  simp

/-- HOL Light: Baker/residue.ml, RESIDUE_PRINCIPAL_PARTS_CIRCLEPATH. If `h` is holomorphic off
the finite set `s` inside the circle and near each `a ∈ s` is a principal part
`∑ j, q a j * (z - a)⁻¹ ^ (m a - j)` plus a function holomorphic at `a`, then the integral of `h`
over the circle is `2 π i` times the sum of the residues `q a (m a - 1)`.

Deviation: HOL's `has_path_integral` (integrability together with the value) is stated as the
value of Mathlib's `circleIntegral`; the hypothesis `0 < r` is added (HOL's `circlepath` needs no
sign condition, but it follows from the other hypotheses as soon as `s` is nonempty). -/
theorem residue_principal_parts_circlepath (h : ℂ → ℂ) (s : Finset ℂ) (m : ℂ → ℕ)
    (q : ℂ → ℕ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hs : ∀ a ∈ s, ‖a - c‖ < r ∧ 1 ≤ m a)
    (hh : DifferentiableOn ℂ h (↑s : Set ℂ)ᶜ)
    (hg : ∀ a ∈ s, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (↑(s.erase a) : Set ℂ)ᶜ ∧
      ∀ z, z ∉ s → h z = ∑ j ∈ Finset.range (m a - 1 + 1),
        q a j * ((z - a)⁻¹) ^ (m a - j) + g z) :
    (∮ z in C(c, r), h z) = 2 * π * Complex.I * ∑ a ∈ s, q a (m a - 1) := by
  rw [Finset.mul_sum]
  refine residue_singular_parts_circlepath h
    (fun a z => ∑ j ∈ Finset.range (m a - 1 + 1), q a j * ((z - a)⁻¹) ^ (m a - j)) _ s c r hr
    (fun a ha => (hs a ha).1) (fun a ha => ⟨?_, ?_⟩) hg hh
  · refine DifferentiableOn.fun_sum fun j _ => ?_
    refine (differentiableOn_const _).mul (DifferentiableOn.pow ?_ _)
    exact (differentiableOn_id.sub (differentiableOn_const _)).inv fun z hz => sub_ne_zero.2 hz
  · exact residue_principal_part_integral (q a) (m a) (hs a ha).2 a c r hr (hs a ha).1

/-! ### The residue theorem for an entire function over a product of powers -/

private theorem residue_prod_pow_ne_zero (u : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) (hz : z ∉ u) :
    ∏ b ∈ u, (z - b) ^ m b ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ hb => pow_ne_zero _ (sub_ne_zero.2 fun h => hz (h ▸ hb))

private theorem residue_differentiableOn_inv_linear_prod (u : Finset ℂ) (t : ℕ) (w : ℂ) :
    DifferentiableOn ℂ (fun z => ((z - w) * ∏ b ∈ u, (z - b) ^ (t + 1))⁻¹)
      ((↑(insert w u) : Set ℂ)ᶜ) := by
  refine DifferentiableOn.inv ?_ fun z hz => ?_
  · exact (differentiableOn_id.sub (differentiableOn_const _)).mul
      (DifferentiableOn.fun_finsetProd fun b _ =>
        (differentiableOn_id.sub (differentiableOn_const _)).pow _)
  · have hzw : z ≠ w := fun h => hz (Finset.mem_coe.2 (h ▸ Finset.mem_insert_self _ _))
    have hzu : z ∉ u := fun h => hz (Finset.mem_coe.2 (Finset.mem_insert_of_mem h))
    exact mul_ne_zero (sub_ne_zero.2 hzw) (residue_prod_pow_ne_zero u (fun _ => t + 1) z hzu)

private theorem residue_differentiableOn_div_prod_pow (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (u : Finset ℂ) (m : ℂ → ℕ) :
    DifferentiableOn ℂ (fun z => f z / ∏ b ∈ u, (z - b) ^ m b) (↑u : Set ℂ)ᶜ := by
  refine hf.differentiableOn.div (DifferentiableOn.fun_finsetProd fun _ _ => ?_) fun z hz => ?_
  · exact ((differentiableOn_id.sub (differentiableOn_const _)).pow _)
  · exact residue_prod_pow_ne_zero u m z (by simpa using hz)

/-- HOL Light: Baker/residue.ml, RESIDUE_CPRODUCT_CIRCLEPATH. The integral over a circle of an
entire function divided by `∏ a ∈ s, (z - a) ^ m a`, all `a ∈ s` inside the circle, is `2 π i`
times the sum of the residues, written as normalized derivatives.

Deviation: HOL's `has_path_integral` is stated as the value of Mathlib's `circleIntegral`, and
the hypothesis `0 < r` is added (it follows from the others when `s` is nonempty). -/
theorem residue_cproduct_circlepath (f : ℂ → ℂ) (s : Finset ℂ) (m : ℂ → ℕ) (c : ℂ) (r : ℝ)
    (hr : 0 < r) (hf : Differentiable ℂ f) (hs : ∀ a ∈ s, ‖a - c‖ < r ∧ 1 ≤ m a) :
    (∮ z in C(c, r), f z / ∏ a ∈ s, (z - a) ^ m a) =
      2 * π * Complex.I * ∑ a ∈ s,
        iteratedDeriv (m a - 1) (fun z => f z / ∏ b ∈ s.erase a, (z - b) ^ m b) a /
          ((m a - 1) ! : ℂ) := by
  refine residue_principal_parts_circlepath (fun z => f z / ∏ a ∈ s, (z - a) ^ m a) s m
    (fun a j => iteratedDeriv j (fun z => f z / ∏ b ∈ s.erase a, (z - b) ^ m b) a / (j ! : ℂ))
    c r hr hs (residue_differentiableOn_div_prod_pow f hf s m) fun a ha => ?_
  have hopen : IsOpen ((↑(s.erase a) : Set ℂ)ᶜ) :=
    (s.erase a).finite_toSet.isClosed.isOpen_compl
  obtain ⟨g, hgd, hg⟩ := holomorphic_taylor_expansion
    (fun z => f z / ∏ b ∈ s.erase a, (z - b) ^ m b) _ a (m a - 1) hopen
    (residue_differentiableOn_div_prod_pow f hf (s.erase a) m) (by simp)
  refine ⟨g, hgd, fun z hz => ?_⟩
  have hza : z - a ≠ 0 := sub_ne_zero.2 fun h => hz (h ▸ ha)
  have hm : m a - 1 + 1 = m a := Nat.sub_add_cancel (hs a ha).2
  have hzmem : z ∈ ((↑(s.erase a) : Set ℂ)ᶜ) := fun h =>
    hz (Finset.mem_of_mem_erase (Finset.mem_coe.1 h))
  have hz' := hg z hzmem
  rw [hm] at hz'
  have hprod : ∏ b ∈ s, (z - b) ^ m b = (z - a) ^ m a * ∏ b ∈ s.erase a, (z - b) ^ m b :=
    (Finset.mul_prod_erase s (fun b => (z - b) ^ m b) ha).symm
  have hpne : (z - a) ^ m a ≠ 0 := pow_ne_zero _ hza
  have hstep : f z / ∏ b ∈ s, (z - b) ^ m b =
      (f z / ∏ b ∈ s.erase a, (z - b) ^ m b) / (z - a) ^ m a := by
    rw [hprod, div_div, mul_comm]
  rw [hstep, hz', hm, add_div, mul_div_cancel_left₀ _ hpne, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ m a := (Finset.mem_range.1 hj).le
  rw [inv_pow, pow_sub₀ _ hza hj']
  field_simp

/-- HOL Light: Baker/residue.ml, HIGHER_COMPLEX_DERIVATIVE_MUL_DIV_FACT. The Leibniz rule for the
normalized derivatives `f⁽ⁿ⁾ / n!` of a product of two holomorphic functions. -/
theorem higher_complex_derivative_mul_div_fact (f g : ℂ → ℂ) (s : Set ℂ) (n : ℕ) (z : ℂ)
    (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) (hg : DifferentiableOn ℂ g s) (hz : z ∈ s) :
    iteratedDeriv n (fun x => f x * g x) z / (n ! : ℂ) =
      ∑ j ∈ Finset.range (n + 1), iteratedDeriv j f z / (j ! : ℂ) *
        iteratedDeriv (n - j) g z / ((n - j) ! : ℂ) := by
  have hf' : ContDiffAt ℂ n f z := (hf.contDiffOn hs).contDiffAt (hs.mem_nhds hz)
  have hg' : ContDiffAt ℂ n g z := (hg.contDiffOn hs).contDiffAt (hs.mem_nhds hz)
  rw [iteratedDeriv_fun_mul hf' hg', Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hc : (n.choose j : ℂ) = (n ! : ℂ) / ((j ! : ℂ) * ((n - j) ! : ℂ)) := by
    rw [Nat.choose_eq_factorial_div_factorial hj',
      Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial hj')
        (by exact_mod_cast (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)).ne')]
    push_cast
    ring
  have h1 : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have h2 : (j ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have h3 : ((n - j) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [hc]
  field_simp

/-! ### The interpolation identity and the bound -/

/-- HOL Light: Baker/residue.ml, INTERPOLATION_RESIDUE_CIRCLEPATH. Baker's interpolation identity
(Transcendental Number Theory, Ch. 3, eq. (8)): the integral of
`f z / ((z - w) * ∏ a ∈ s, (z - a) ^ (t + 1))` over a circle containing `w` and `s`, as `2 π i`
times the residue at `w` plus the residues at the nodes.

Deviation: HOL's `has_path_integral` is stated as the value of Mathlib's `circleIntegral`. -/
theorem interpolation_residue_circlepath (f : ℂ → ℂ) (s : Finset ℂ) (t : ℕ) (w c : ℂ) (r : ℝ)
    (hf : Differentiable ℂ f) (hw : w ∉ s) (hwc : ‖w - c‖ < r) (hs : ∀ a ∈ s, ‖a - c‖ < r) :
    (∮ z in C(c, r), f z / ((z - w) * ∏ a ∈ s, (z - a) ^ (t + 1))) =
      2 * π * Complex.I *
        (f w / ∏ a ∈ s, (w - a) ^ (t + 1) +
          ∑ a ∈ s, ∑ j ∈ Finset.range (t + 1),
            iteratedDeriv j f a / (j ! : ℂ) *
              iteratedDeriv (t - j)
                (fun z => ((z - w) * ∏ b ∈ s.erase a, (z - b) ^ (t + 1))⁻¹) a /
              ((t - j) ! : ℂ)) := by
  have hr : 0 < r := (norm_nonneg _).trans_lt hwc
  set m : ℂ → ℕ := fun a => if a = w then 1 else t + 1 with hm
  have hmw : m w = 1 := by simp [hm]
  have hms : ∀ a ∈ s, m a = t + 1 := fun a ha => by
    have : a ≠ w := fun h => hw (h ▸ ha)
    simp [hm, this]
  have hprod : ∀ (u : Finset ℂ), u ⊆ s → ∀ z : ℂ,
      ∏ b ∈ u, (z - b) ^ m b = ∏ b ∈ u, (z - b) ^ (t + 1) := fun u hu z =>
    Finset.prod_congr rfl fun b hb => by rw [hms b (hu hb)]
  have key := residue_cproduct_circlepath f (insert w s) m c r hr hf (fun a ha => by
    rcases Finset.mem_insert.1 ha with rfl | ha
    · exact ⟨hwc, by rw [hmw]⟩
    · exact ⟨hs a ha, by rw [hms a ha]; omega⟩)
  have hL : ∀ z : ℂ, ∏ a ∈ insert w s, (z - a) ^ m a =
      (z - w) * ∏ a ∈ s, (z - a) ^ (t + 1) := fun z => by
    rw [Finset.prod_insert hw, hmw, pow_one, hprod s subset_rfl z]
  simp only [hL] at key
  rw [key, Finset.sum_insert hw, Finset.erase_insert hw, hmw]
  congr 2
  · simp [hprod s subset_rfl]
  · refine Finset.sum_congr rfl fun a ha => ?_
    have haw : a ≠ w := fun h => hw (h ▸ ha)
    have hwa : w ∉ s.erase a := fun h => hw (Finset.mem_of_mem_erase h)
    have hfun : (fun z => f z / ∏ b ∈ (insert w s).erase a, (z - b) ^ m b) =
        fun z => f z * ((z - w) * ∏ b ∈ s.erase a, (z - b) ^ (t + 1))⁻¹ := by
      funext z
      rw [Finset.erase_insert_of_ne haw.symm, Finset.prod_insert hwa, hmw, pow_one,
        hprod (s.erase a) (Finset.erase_subset _ _) z, div_eq_mul_inv]
    rw [hfun, hms a ha, Nat.add_sub_cancel]
    have hopen : IsOpen ((↑(insert w (s.erase a)) : Set ℂ)ᶜ) :=
      (insert w (s.erase a)).finite_toSet.isClosed.isOpen_compl
    refine higher_complex_derivative_mul_div_fact f _ _ t a hopen hf.differentiableOn
      (residue_differentiableOn_inv_linear_prod (s.erase a) t w) ?_
    simp [haw]

/-- HOL Light: Baker/residue.ml, INTERPOLATION_RESIDUE_SUM_BOUND. Cauchy's inequalities on circles
of radius `d` around the nodes bound the sum of the residues at the nodes. -/
theorem interpolation_residue_sum_bound (f : ℂ → ℂ) (s : Finset ℂ) (t : ℕ) (w : ℂ) (d : ℝ)
    (U : ℂ → ℝ) (_hw : w ∉ s) (hd : 0 < d)
    (hsep : ∀ a ∈ s, d < ‖w - a‖ ∧ ∀ b ∈ s, b ≠ a → d < ‖b - a‖)
    (hU : ∀ a z, a ∈ s → ‖z - a‖ = d →
      ‖((z - w) * ∏ b ∈ s.erase a, (z - b) ^ (t + 1))⁻¹‖ ≤ U a) :
    ‖∑ a ∈ s, ∑ j ∈ Finset.range (t + 1),
        iteratedDeriv j f a / (j ! : ℂ) *
          iteratedDeriv (t - j)
            (fun z => ((z - w) * ∏ b ∈ s.erase a, (z - b) ^ (t + 1))⁻¹) a /
          ((t - j) ! : ℂ)‖ ≤
      ∑ a ∈ s, ∑ j ∈ Finset.range (t + 1),
        ‖iteratedDeriv j f a‖ / (j ! : ℝ) * U a / d ^ (t - j) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a ha => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  obtain ⟨hwa, hba⟩ := hsep a ha
  have hsub : closedBall a d ⊆ ((↑(insert w (s.erase a)) : Set ℂ)ᶜ) := by
    intro z hz hmem
    rw [mem_closedBall_iff_norm] at hz
    rcases Finset.mem_insert.1 (Finset.mem_coe.1 hmem) with rfl | hb
    · linarith
    · have := hba z (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)
      linarith
  have hdiff : DifferentiableOn ℂ
      (fun z => ((z - w) * ∏ b ∈ s.erase a, (z - b) ^ (t + 1))⁻¹)
      ((↑(insert w (s.erase a)) : Set ℂ)ᶜ) :=
    residue_differentiableOn_inv_linear_prod (s.erase a) t w
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (t - j) hd
    (hdiff.diffContOnCl_ball hsub) (C := U a)
    (fun z hz => hU a z ha (mem_sphere_iff_norm.1 hz))
  have hk : (0 : ℝ) < ((t - j) ! : ℝ) := by positivity
  have hj : (0 : ℝ) < (j ! : ℝ) := by positivity
  have hdk : (0 : ℝ) < d ^ (t - j) := pow_pos hd _
  rw [norm_div, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  have h2 : ‖iteratedDeriv (t - j)
      (fun z => ((z - w) * ∏ b ∈ s.erase a, (z - b) ^ (t + 1))⁻¹) a‖ / ((t - j) ! : ℝ) ≤
      U a / d ^ (t - j) := by
    rw [div_le_iff₀ hk]
    calc _ ≤ _ := hcauchy
      _ = U a / d ^ (t - j) * ((t - j) ! : ℝ) := by ring
  calc ‖iteratedDeriv j f a‖ / (j ! : ℝ) * ‖iteratedDeriv (t - j)
          (fun z => ((z - w) * ∏ b ∈ s.erase a, (z - b) ^ (t + 1))⁻¹) a‖ / ((t - j) ! : ℝ)
      = ‖iteratedDeriv j f a‖ / (j ! : ℝ) * (‖iteratedDeriv (t - j)
          (fun z => ((z - w) * ∏ b ∈ s.erase a, (z - b) ^ (t + 1))⁻¹) a‖ / ((t - j) ! : ℝ)) := by
        ring
    _ ≤ ‖iteratedDeriv j f a‖ / (j ! : ℝ) * (U a / d ^ (t - j)) := by gcongr
    _ = ‖iteratedDeriv j f a‖ / (j ! : ℝ) * U a / d ^ (t - j) := by ring

/-- HOL Light: Baker/residue.ml, INTERPOLATION_RESIDUE_BOUND. The upper bound for `‖f w‖` in terms
of the supremum `M` of an entire `f` on a big circle and of its derivatives up to order `t` at the
nodes `s` (Baker, Transcendental Number Theory, Ch. 3, eq. (8)): length bound on the big circle,
Cauchy's inequalities on circles of radius `d` around the nodes. -/
theorem interpolation_residue_bound (f : ℂ → ℂ) (s : Finset ℂ) (t : ℕ) (w c : ℂ) (r d M mu : ℝ)
    (U : ℂ → ℝ) (hf : Differentiable ℂ f) (hw : w ∉ s) (hwc : ‖w - c‖ < r)
    (hs : ∀ a ∈ s, ‖a - c‖ < r) (hd : 0 < d)
    (hsep : ∀ a ∈ s, d < ‖w - a‖ ∧ ∀ b ∈ s, b ≠ a → d < ‖b - a‖)
    (hmu : 0 < mu)
    (hR : ∀ z, ‖z - c‖ = r →
      ‖f z‖ ≤ M ∧ mu ≤ ‖(z - w) * ∏ a ∈ s, (z - a) ^ (t + 1)‖)
    (hU : ∀ a z, a ∈ s → ‖z - a‖ = d →
      ‖((z - w) * ∏ b ∈ s.erase a, (z - b) ^ (t + 1))⁻¹‖ ≤ U a) :
    ‖f w‖ ≤ ‖∏ a ∈ s, (w - a) ^ (t + 1)‖ *
      (r * M / mu +
        ∑ a ∈ s, ∑ j ∈ Finset.range (t + 1),
          ‖iteratedDeriv j f a‖ / (j ! : ℝ) * U a / d ^ (t - j)) := by
  have hr : 0 < r := (norm_nonneg _).trans_lt hwc
  have hM : 0 ≤ M := by
    have h := (hR (c + r) (by simp [abs_of_pos hr])).1
    exact (norm_nonneg _).trans h
  have hid := interpolation_residue_circlepath f s t w c r hf hw hwc hs
  have hsum := interpolation_residue_sum_bound f s t w d U hw hd hsep hU
  have hint : ‖∮ z in C(c, r), f z / ((z - w) * ∏ a ∈ s, (z - a) ^ (t + 1))‖ ≤
      2 * π * r * (M / mu) := by
    refine circleIntegral.norm_integral_le_of_norm_le_const hr.le fun z hz => ?_
    obtain ⟨h1, h2⟩ := hR z (mem_sphere_iff_norm.1 hz)
    rw [norm_div]
    exact div_le_div₀ hM h1 hmu h2
  set P := ∏ a ∈ s, (w - a) ^ (t + 1) with hP
  set Y := ∑ a ∈ s, ∑ j ∈ Finset.range (t + 1),
      iteratedDeriv j f a / (j ! : ℂ) *
        iteratedDeriv (t - j)
          (fun z => ((z - w) * ∏ b ∈ s.erase a, (z - b) ^ (t + 1))⁻¹) a /
        ((t - j) ! : ℂ) with hY
  have hPne : P ≠ 0 := residue_prod_pow_ne_zero s (fun _ => t + 1) w hw
  have hA : ‖f w / P + Y‖ ≤ r * M / mu := by
    rw [hid, norm_mul] at hint
    have h2pi : ‖(2 * π * Complex.I : ℂ)‖ = 2 * π := by
      simp [abs_of_pos Real.pi_pos]
    rw [h2pi] at hint
    have hpos : (0 : ℝ) < 2 * π := by positivity
    have : 2 * π * ‖f w / P + Y‖ ≤ 2 * π * (r * M / mu) := by
      calc _ ≤ _ := hint
        _ = _ := by ring
    exact le_of_mul_le_mul_left this hpos
  have hx : ‖f w / P‖ ≤ r * M / mu + ‖Y‖ := by
    have : f w / P = (f w / P + Y) - Y := by ring
    rw [this]
    exact (norm_sub_le _ _).trans (by linarith)
  have hfw : ‖f w‖ = ‖P‖ * ‖f w / P‖ := by
    rw [norm_div, mul_div_cancel₀ _ (norm_ne_zero_iff.2 hPne)]
  rw [hfw]
  exact mul_le_mul_of_nonneg_left (hx.trans (by linarith)) (norm_nonneg _)

end RiemannMasullo.Baker
