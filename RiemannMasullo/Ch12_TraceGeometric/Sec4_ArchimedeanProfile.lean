module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Archimedean differences of radial cutoff profiles -/

@[expose] public noncomputable section

open Filter Function Set
open scoped InnerProductSpace Topology

namespace RiemannMasullo

/-- The forward difference of order `n` is bounded by the `n`-th derivative
on the interval spanned by its evaluation points. -/
private theorem norm_fwdDiff_iter_le_of_iteratedDeriv_bound {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ℕ) {f : ℝ → V}
    (hf : ContDiff ℝ n f) {h x A : ℝ} (hh : 0 ≤ h)
    (hA : ∀ t ∈ Icc x (x + (n : ℝ) * h), ‖iteratedDeriv n f t‖ ≤ A) :
    ‖((fwdDiff h)^[n] f) x‖ ≤ A * h ^ n := by
  induction n generalizing f A with
  | zero =>
      have hx : x ∈ Icc x (x + ((0 : ℕ) : ℝ) * h) := by simp
      simpa only [Function.iterate_zero_apply, iteratedDeriv_zero, pow_zero, mul_one] using hA x hx
  | succ n ih =>
      let g := fwdDiff h f
      have hfₙ : ContDiff ℝ n f := hf.of_le (by exact_mod_cast Nat.le_succ n)
      have hshift : ContDiff ℝ n (fun t : ℝ ↦ f (t + h)) :=
        hfₙ.comp (contDiff_id.add contDiff_const)
      have hg : ContDiff ℝ n g := hshift.sub hfₙ
      have hD : Differentiable ℝ (iteratedDeriv n f) :=
        hf.differentiable_iteratedDeriv n (Nat.cast_lt.mpr n.lt_succ_self)
      have hDeriv (u : ℝ) : HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f u) u := by
        rw [iteratedDeriv_succ]
        exact (hD u).hasDerivAt
      have hB (t : ℝ) (ht : t ∈ Icc x (x + (n : ℝ) * h)) :
          ‖iteratedDeriv n g t‖ ≤ A * h := by
        have hdiff : iteratedDeriv n g t =
            iteratedDeriv n f (t + h) - iteratedDeriv n f t := by
          change iteratedDeriv n ((fun z : ℝ ↦ f (z + h)) - f) t = _
          rw [iteratedDeriv_sub hshift.contDiffAt hfₙ.contDiffAt, iteratedDeriv_comp_add_const]
        have hend : t + h ≤ x + ((n + 1 : ℕ) : ℝ) * h := by
          calc
            t + h ≤ (x + (n : ℝ) * h) + h := add_le_add ht.2 (le_refl h)
            _ = _ := by rw [Nat.cast_succ]; ring
        have hderiv (u : ℝ) (_ : u ∈ Icc t (t + h)) :
            HasDerivWithinAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f u) (Icc t (t + h)) u :=
          (hDeriv u).hasDerivWithinAt
        have hBound (u : ℝ) (hu : u ∈ Ico t (t + h)) : ‖iteratedDeriv (n + 1) f u‖ ≤ A :=
          hA u ⟨ht.1.trans hu.1, hu.2.le.trans hend⟩
        rw [hdiff]
        simpa only [add_sub_cancel_left] using norm_image_sub_le_of_norm_deriv_le_segment'
          hderiv hBound (t + h) (right_mem_Icc.2 (le_add_of_nonneg_right hh))
      rw [Function.iterate_succ_apply, pow_succ]
      calc
        _ ≤ (A * h) * h ^ n := ih (f := g) (A := A * h) hg hB
        _ = _ := by ring

private theorem realProfile_abs_contDiff_iteratedDeriv_bound (n d : ℕ) {b : ℝ → ℂ}
    {ε C : ℝ} (hε : 0 < ε) (hb : ContDiffOn ℝ n b (Ioi 0))
    (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 ε))
    (hB : ∀ x, 0 ≤ x → ‖iteratedDeriv n b x‖ ≤ C * (1 + x) ^ d) :
    ContDiff ℝ n (fun x ↦ b |x|) ∧
      ∀ x : ℝ, ‖iteratedDeriv n (fun y ↦ b |y|) x‖ ≤ C * (1 + |x|) ^ d := by
  have hC : 0 ≤ C := (norm_nonneg (iteratedDeriv n b 0)).trans
    (by simpa only [add_zero, one_pow, mul_one] using hB 0 le_rfl)
  let g (x : ℝ) := b |x|
  have hlocal (x : ℝ) : ContDiffAt ℝ n g x ∧
      ‖iteratedDeriv n g x‖ ≤ C * (1 + |x|) ^ d := by
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · have heq : g =ᶠ[𝓝 x] (fun y : ℝ ↦ b (-y)) := by
        filter_upwards [Iio_mem_nhds hx] with y hy
        exact congrArg b (abs_of_neg hy)
      have hneg : ContDiffAt ℝ n (fun y : ℝ ↦ -y) x := contDiff_neg.contDiffAt
      have hb' : ContDiffAt ℝ n b (-x) := hb.contDiffAt (Ioi_mem_nhds (neg_pos.mpr hx))
      refine ⟨(hb'.comp x hneg).congr_of_eventuallyEq heq, ?_⟩
      rw [Filter.EventuallyEq.iteratedDeriv_eq n heq, iteratedDeriv_comp_neg,
        norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul, abs_of_neg hx]
      exact hB (-x) (neg_nonneg.mpr hx.le)
    · have habs : Tendsto (fun y : ℝ ↦ |y|) (𝓝 0) (𝓝 0) :=
        continuous_abs.tendsto' 0 0 abs_zero
      have heq : g =ᶠ[𝓝 0] (fun _ : ℝ ↦ b 0) := by
        filter_upwards [habs.eventually (Iio_mem_nhds hε)] with y hy
        exact hplateau ⟨abs_nonneg y, (show |y| < ε from hy).le⟩
      have hconst : ContDiffAt ℝ n (fun _ : ℝ ↦ b 0) 0 := contDiffAt_const
      refine ⟨hconst.congr_of_eventuallyEq heq, ?_⟩
      rw [Filter.EventuallyEq.iteratedDeriv_eq n heq, iteratedDeriv_const,
        abs_zero, add_zero, one_pow, mul_one]
      by_cases hn : n = 0
      · rw [ite_eq_left hn]
        simpa only [hn, iteratedDeriv_zero, add_zero, one_pow, mul_one] using hB 0 le_rfl
      · simpa only [ite_eq_right hn, norm_zero] using hC
    · have heq : g =ᶠ[𝓝 x] b := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        exact congrArg b (abs_of_pos hy)
      refine ⟨(hb.contDiffAt (Ioi_mem_nhds hx)).congr_of_eventuallyEq heq, ?_⟩
      rw [Filter.EventuallyEq.iteratedDeriv_eq n heq, abs_of_pos hx]
      exact hB x hx.le
  exact ⟨contDiff_iff_contDiffAt.mpr (fun x ↦ (hlocal x).1), fun x ↦ (hlocal x).2⟩

/-- A radial profile constant near zero has a uniform polynomial derivative
bound along a line through one real place. The nonnegative coefficient `a`
absorbs the other coordinate moduli and the reciprocal cutoff scale. -/
theorem realProfile_line_contDiff_iteratedDeriv_bound (n d : ℕ) {b : ℝ → ℂ}
    {ε C : ℝ} (hε : 0 < ε) (hb : ContDiffOn ℝ n b (Ioi 0))
    (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 ε))
    (hB : ∀ x, 0 ≤ x → ‖iteratedDeriv n b x‖ ≤ C * (1 + x) ^ d)
    {a : ℝ} (ha : 0 ≤ a) (z v T : ℝ) :
    ContDiff ℝ n (fun t ↦ b (a * |z + t * v|)) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        ‖iteratedDeriv n (fun s ↦ b (a * |z + s * v|)) t‖ ≤
          C * (a * |v|) ^ n * (1 + a * (|z| + T * |v|)) ^ d := by
  have hC : 0 ≤ C := (norm_nonneg (iteratedDeriv n b 0)).trans
    (by simpa only [add_zero, one_pow, mul_one] using hB 0 le_rfl)
  obtain ⟨hg, hG⟩ := realProfile_abs_contDiff_iteratedDeriv_bound n d hε hb hplateau hB
  let g (x : ℝ) := b |x|
  let p (x : ℝ) := g (a * z + x)
  have hp : ContDiff ℝ n p := hg.comp (contDiff_const.add contDiff_id)
  have hpd (t : ℝ) : iteratedDeriv n p t = iteratedDeriv n g (a * z + t) :=
    congrFun (iteratedDeriv_comp_const_add n g (a * z)) t
  have harg (t : ℝ) : a * z + (a * v) * t = a * (z + t * v) := by ring
  have hcurve : (fun t : ℝ ↦ b (a * |z + t * v|)) = fun t ↦ p ((a * v) * t) := by
    funext t
    change b (a * |z + t * v|) = b |a * z + (a * v) * t|
    rw [harg t, abs_mul, abs_of_nonneg ha]
  rw [hcurve]
  refine ⟨hp.comp (contDiff_const.mul contDiff_id), fun t ht ↦ ?_⟩
  have ht₁ : 0 ≤ t := ht.1
  have ht₂ : t ≤ T := ht.2
  have hprod : t * |v| ≤ T * |v| := mul_le_mul_of_nonneg_right ht₂ (abs_nonneg v)
  have hlin : |z + t * v| ≤ |z| + T * |v| := by
    calc
      _ ≤ |z| + |t * v| := abs_add_le _ _
      _ = |z| + t * |v| := by rw [abs_mul, abs_of_nonneg ht₁]
      _ ≤ _ := add_le_add (le_refl |z|) hprod
  rw [iteratedDeriv_comp_const_smul hp (a * v), norm_smul, norm_pow, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg ha, hpd, harg]
  calc
    _ ≤ (a * |v|) ^ n * (C * (1 + |a * (z + t * v)|) ^ d) :=
      mul_le_mul_of_nonneg_left (hG (a * (z + t * v))) (by positivity)
    _ = C * (a * |v|) ^ n * (1 + a * |z + t * v|) ^ d := by
      rw [abs_mul, abs_of_nonneg ha]
      ring
    _ ≤ _ := by
      have hbase : 1 + a * |z + t * v| ≤ 1 + a * (|z| + T * |v|) :=
        add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left hlin ha)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase _) (by positivity)


/-- Paper: Theorem 12.4.1.1, Step II, p. 517.
At one real place, a radial profile flat near zero has a forward difference of
order `n` bounded by the `n`-th power of the local displacement. The scalar
`a` absorbs the fixed moduli at the other places and the reciprocal scale. -/
theorem norm_fwdDiff_iter_realProfile_le (n d : ℕ) {b : ℝ → ℂ}
    {ε C : ℝ} (hε : 0 < ε) (hb : ContDiffOn ℝ n b (Ioi 0))
    (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 ε))
    (hB : ∀ x, 0 ≤ x → ‖iteratedDeriv n b x‖ ≤ C * (1 + x) ^ d)
    {a : ℝ} (ha : 0 ≤ a) (z v : ℝ) :
    ‖((fwdDiff (1 : ℝ))^[n] (fun t ↦ b (a * |z + t * v|))) 0‖ ≤
      C * (a * |v|) ^ n * (1 + a * (|z| + (n : ℝ) * |v|)) ^ d := by
  obtain ⟨hs, hd⟩ := realProfile_line_contDiff_iteratedDeriv_bound n d hε hb hplateau hB
    ha z v n
  have h := norm_fwdDiff_iter_le_of_iteratedDeriv_bound n hs
    (h := (1 : ℝ)) (x := 0) zero_le_one
    (fun t ht ↦ hd t (by simpa only [mul_one, zero_add] using ht))
  simpa only [one_pow, mul_one] using h

private theorem normSqProfile_inner_iteratedDeriv_zero {Z : Type*}
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (a : ℝ) (w v : Z) {i : ℕ} (hi : 0 < i) :
    iteratedDeriv i (fun s : ℝ ↦ a * ‖w + s • v‖ ^ 2) 0 =
      (if i = 1 then 2 * a * ⟪w, v⟫_ℝ else 0) +
        (if i = 2 then 2 * (a * ‖v‖ ^ 2) else 0) := by
  let B := 2 * a * ⟪w, v⟫_ℝ
  let D := a * ‖v‖ ^ 2
  have hpoly : (fun s : ℝ ↦ a * ‖w + s • v‖ ^ 2) =
      fun s ↦ a * ‖w‖ ^ 2 + (B * s + D * s ^ 2) := by
    funext s
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    dsimp only [B, D]
    ring
  have h₁ : ContDiffAt ℝ i (fun s : ℝ ↦ B * s) 0 :=
    (show ContDiff ℝ i (fun s : ℝ ↦ B * s) from contDiff_const.mul contDiff_id).contDiffAt
  have h₂ : ContDiffAt ℝ i (fun s : ℝ ↦ D * s ^ 2) 0 :=
    (show ContDiff ℝ i (fun s : ℝ ↦ D * s ^ 2) from
      contDiff_const.mul (contDiff_id.pow 2)).contDiffAt
  rw [hpoly, iteratedDeriv_const_add hi, iteratedDeriv_fun_add h₁ h₂]
  simp only [iteratedDeriv_const_mul_field B (fun s : ℝ ↦ s),
    iteratedDeriv_const_mul_field D (fun s : ℝ ↦ s ^ 2),
    iteratedDeriv_fun_id_zero, iteratedDeriv_fun_pow_zero]
  split_ifs <;> norm_num [B, D, Nat.factorial] <;> ring

/-- The cutoff profile through a complex place has a polynomial bound for its
derivatives on bounded real parameter intervals. The estimate uses only the
real inner product and retains the full order of the direction norm. -/
theorem normSqProfile_line_contDiff_iteratedDeriv_bound {Z : Type*}
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (n d : ℕ) {b : ℝ → ℂ} {C a : ℝ} (hb : ContDiff ℝ n b) (ha : 0 ≤ a)
    (hB : ∀ i ≤ n, ∀ x, 0 ≤ x → ‖iteratedDeriv i b x‖ ≤ C * (1 + x) ^ d)
    (z v : Z) (T : ℝ) :
    let R := ‖z‖ + T * ‖v‖
    ContDiff ℝ n (fun t : ℝ ↦ b (a * ‖z + t • v‖ ^ 2)) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        ‖iteratedDeriv n (fun s : ℝ ↦ b (a * ‖z + s • v‖ ^ 2)) t‖ ≤
          (n.factorial : ℝ) * (C * (1 + a * R ^ 2) ^ d) *
            ((1 + 2 * a * (1 + R)) * ‖v‖) ^ n := by
  intro R
  have hsmooth (w : Z) : ContDiff ℝ n (fun t : ℝ ↦ a * ‖w + t • v‖ ^ 2) := by
    have hline : ContDiff ℝ n (fun t : ℝ ↦ w + t • v) :=
      contDiff_const.add (contDiff_id.smul_const v)
    exact contDiff_const.mul (hline.norm_sq ℝ)
  refine ⟨hb.comp (hsmooth z), fun t ht ↦ ?_⟩
  let w := z + t • v
  let q (s : ℝ) := a * ‖w + s • v‖ ^ 2
  let D := 1 + 2 * a * (1 + R)
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hw : ‖w‖ ≤ R := by
    calc
      _ ≤ ‖z‖ + ‖t • v‖ := norm_add_le _ _
      _ = ‖z‖ + t * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ ≤ R := add_le_add (le_refl ‖z‖) (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v))
  have hD₁ : 1 ≤ D := le_add_of_nonneg_right (by positivity)
  have hDw : 2 * a * ‖w‖ ≤ D :=
    (mul_le_mul_of_nonneg_left (hw.trans (le_add_of_nonneg_left zero_le_one))
      (by positivity)).trans (le_add_of_nonneg_left zero_le_one)
  have hDa : 2 * a ≤ D := by
    calc
      _ = 2 * a * 1 := by ring
      _ ≤ 2 * a * (1 + R) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hR) (by positivity)
      _ ≤ _ := le_add_of_nonneg_left zero_le_one
  have hD₂ : D ≤ D ^ (2 : ℕ) := by
    simpa only [pow_two] using le_mul_of_one_le_right (zero_le_one.trans hD₁) hD₁
  have hinner (i : ℕ) (hi : 1 ≤ i) (_ : i ≤ n) :
      ‖iteratedFDeriv ℝ i q 0‖ ≤ (D * ‖v‖) ^ i := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    change ‖iteratedDeriv i (fun s : ℝ ↦ a * ‖w + s • v‖ ^ 2) 0‖ ≤ _
    rw [normSqProfile_inner_iteratedDeriv_zero a w v (zero_lt_one.trans_le hi)]
    by_cases h₁ : i = 1
    · subst i
      rw [ite_eq_left rfl, ite_eq_right (by decide : (1 : ℕ) ≠ 2), add_zero, pow_one,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ 2 * a by positivity)]
      calc
        _ ≤ (2 * a) * (‖w‖ * ‖v‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
        _ = 2 * a * ‖w‖ * ‖v‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hDw (norm_nonneg _)
    by_cases h₂ : i = 2
    · subst i
      rw [ite_eq_right (by decide : (2 : ℕ) ≠ 1), ite_eq_left rfl, zero_add, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ 2 * (a * ‖v‖ ^ 2) by positivity), mul_pow]
      calc
        _ = (2 * a) * ‖v‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hDa.trans hD₂) (by positivity)
    · rw [ite_eq_right h₁, ite_eq_right h₂, add_zero, norm_zero]
      positivity
  have hC : 0 ≤ C := (norm_nonneg (iteratedDeriv 0 b 0)).trans
    (by simpa only [add_zero, one_pow, mul_one] using hB 0 (Nat.zero_le n) 0 le_rfl)
  have hq₀ : q 0 = a * ‖w‖ ^ 2 := by simp only [q, zero_smul, add_zero]
  have houter (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i b (q 0)‖ ≤ C * (1 + a * R ^ 2) ^ d := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hq₀]
    refine (hB i hi _ (by positivity)).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact pow_le_pow_left₀ (by positivity) (add_le_add (le_refl 1)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw 2) ha)) _
  have hshift : (fun s : ℝ ↦ b (a * ‖z + (t + s) • v‖ ^ 2)) = b ∘ q := by
    funext s
    simp only [Function.comp_apply, q, w, add_smul, add_assoc]
  have hderiv : iteratedDeriv n (fun s : ℝ ↦ b (a * ‖z + s • v‖ ^ 2)) t =
      iteratedDeriv n (b ∘ q) 0 := by
    rw [← hshift, iteratedDeriv_comp_const_add n (fun s ↦ b (a * ‖z + s • v‖ ^ 2)) t]
    simp only [add_zero]
  rw [hderiv, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact norm_iteratedFDeriv_comp_le (n := n) (C := C * (1 + a * R ^ 2) ^ d)
    (D := D * ‖v‖) hb (hsmooth w) le_rfl 0 houter hinner

/-- Paper: Theorem 12.4.1.1, Step II, p. 517.
The squared local norm at a complex place gives a forward-difference estimate
of any prescribed order, with the full power of the local displacement. -/
theorem norm_fwdDiff_iter_normSqProfile_le {Z : Type*}
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (n d : ℕ) {b : ℝ → ℂ} {C a : ℝ} (hb : ContDiff ℝ n b) (ha : 0 ≤ a)
    (hB : ∀ i ≤ n, ∀ x, 0 ≤ x → ‖iteratedDeriv i b x‖ ≤ C * (1 + x) ^ d)
    (z v : Z) :
    let R := ‖z‖ + (n : ℝ) * ‖v‖
    ‖((fwdDiff (1 : ℝ))^[n] (fun t ↦ b (a * ‖z + t • v‖ ^ 2))) 0‖ ≤
      (n.factorial : ℝ) * (C * (1 + a * R ^ 2) ^ d) *
        ((1 + 2 * a * (1 + R)) * ‖v‖) ^ n := by
  intro R
  obtain ⟨hs, hd⟩ := normSqProfile_line_contDiff_iteratedDeriv_bound n d hb ha hB z v n
  have h := norm_fwdDiff_iter_le_of_iteratedDeriv_bound n hs
    (h := (1 : ℝ)) (x := 0) zero_le_one
    (fun t ht ↦ hd t (by simpa only [mul_one, zero_add] using ht))
  simpa only [one_pow, mul_one] using h

end RiemannMasullo
