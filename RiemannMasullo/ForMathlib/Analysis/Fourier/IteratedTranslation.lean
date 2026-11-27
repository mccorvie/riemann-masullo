module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Group.Integral
public import RiemannMasullo.ForMathlib.Analysis.Fourier.Translation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Iterated differences and Fourier integrals -/

@[expose] public noncomputable section

open Function MeasureTheory Set

namespace RiemannMasullo

/-- Uniform difference bounds for one factor and weighted difference bounds for
the other give a weighted bound for the product. The weight may grow by a
fixed factor on each translation. -/
private theorem norm_fwdDiff_iter_mul_le_of_bounds {E : Type*} [AddCommGroup E]
    (h : E) (n : ℕ) (W : E → ℝ) {C r A B : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hshift : ∀ x, W (x + h) ≤ C * W x)
    (f g : E → ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ j ≤ n, ∀ x, ‖((fwdDiff h)^[j] f) x‖ ≤ A * r ^ j)
    (hg : ∀ j ≤ n, ∀ x, ‖((fwdDiff h)^[j] g) x‖ ≤ B * r ^ j * W x) :
    ∀ x, ‖((fwdDiff h)^[n] (fun x ↦ f x * g x)) x‖ ≤
      (C + 1) ^ n * A * B * r ^ n * W x := by
  induction n generalizing f g A B with
  | zero =>
    intro x
    have hfx : ‖f x‖ ≤ A := by simpa only [iterate_zero_apply, pow_zero, mul_one] using hf 0 le_rfl x
    have hgx : ‖g x‖ ≤ B * W x := by simpa only [iterate_zero_apply, pow_zero, mul_one] using hg 0 le_rfl x
    simpa only [iterate_zero_apply, pow_zero, one_mul, mul_one, mul_assoc, norm_mul] using
      mul_le_mul hfx hgx (norm_nonneg _) hA
  | succ n ih =>
    intro x
    have hfs (j : ℕ) (hj : j ≤ n) (y : E) :
        ‖((fwdDiff h)^[j] (fwdDiff h f)) y‖ ≤ (A * r) * r ^ j := by
      calc
        _ ≤ A * r ^ (j + 1) := by
          rw [← Function.iterate_succ_apply]
          exact hf (j + 1) (Nat.succ_le_succ hj) y
        _ = _ := by rw [pow_succ]; ring
    have hgs (j : ℕ) (hj : j ≤ n) (y : E) :
        ‖((fwdDiff h)^[j] (fwdDiff h g)) y‖ ≤ (B * r) * r ^ j * W y := by
      calc
        _ ≤ B * r ^ (j + 1) * W y := by
          rw [← Function.iterate_succ_apply]
          exact hg (j + 1) (Nat.succ_le_succ hj) y
        _ = _ := by rw [pow_succ]; ring
    have hgshift (j : ℕ) (hj : j ≤ n) (y : E) :
        ‖((fwdDiff h)^[j] (fun z ↦ g (z + h))) y‖ ≤ (C * B) * r ^ j * W y := by
      rw [fwdDiff_iter_comp_add]
      calc
        _ ≤ B * r ^ j * W (y + h) := hg j (hj.trans (Nat.le_succ n)) (y + h)
        _ ≤ B * r ^ j * (C * W y) :=
          mul_le_mul_of_nonneg_left (hshift y) (mul_nonneg hB (pow_nonneg hr j))
        _ = _ := by ring
    have hleft := ih (f := fwdDiff h f) (g := fun y ↦ g (y + h))
      (A := A * r) (B := C * B) (mul_nonneg hA hr) (mul_nonneg hC hB) hfs hgshift x
    have hright := ih (f := f) (g := fwdDiff h g) (A := A) (B := B * r)
      hA (mul_nonneg hB hr) (fun j hj y ↦ hf j (hj.trans (Nat.le_succ n)) y) hgs x
    have hprod : fwdDiff h (fun y ↦ f y * g y) =
        (fun y ↦ (fwdDiff h f) y * g (y + h)) + (fun y ↦ f y * (fwdDiff h g) y) := by
      funext y
      simp only [fwdDiff, Pi.add_apply]
      ring
    rw [Function.iterate_succ_apply, hprod, fwdDiff_iter_add]
    change ‖((fwdDiff h)^[n] (fun y ↦ (fwdDiff h f) y * g (y + h))) x +
      ((fwdDiff h)^[n] (fun y ↦ f y * (fwdDiff h g) y)) x‖ ≤ _
    apply (norm_add_le _ _).trans
    calc
      _ ≤ (C + 1) ^ n * (A * r) * (C * B) * r ^ n * W x +
          (C + 1) ^ n * A * (B * r) * r ^ n * W x := add_le_add hleft hright
      _ = _ := by simp only [pow_succ]; ring

private theorem sqrt_add_le_sum_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  nlinarith only [Real.sq_sqrt ha, Real.sq_sqrt hb,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- Interpolates a pointwise bound on a forward difference with a weighted
square-root moment. The moment of each difference grows by at most `C + 1`,
using the triangle inequality and additive invariance of the measure. -/
private theorem integral_norm_fwdDiff_iter_le_of_sq_weighted_bound {E V : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup V]
    (μ : Measure E) [μ.IsAddLeftInvariant] (m : ℕ) (h : E) (k : E → V)
    (hk : Integrable k μ) (P : E → ℝ) (hPc : Continuous P) (hP : ∀ x, 0 ≤ P x)
    (hmom : Integrable (fun x ↦ P x * Real.sqrt ‖k x‖) μ)
    {C A : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hshift : ∀ x, P x ≤ C * P (x + h))
    (hpoint : ∀ x, ‖((fwdDiff h)^[m] k) x‖ ≤ (A * P x) ^ 2) :
    (∫ x, ‖((fwdDiff h)^[m] k) x‖ ∂μ) ≤
      A * (C + 1) ^ m * ∫ x, P x * Real.sqrt ‖k x‖ ∂μ := by
  let Q (f : E → V) (x : E) : ℝ := P x * Real.sqrt ‖f x‖
  have hQ0 (f : E → V) (x : E) : 0 ≤ Q f x :=
    mul_nonneg (hP x) (Real.sqrt_nonneg _)
  have hQmeas (f : E → V) (hf : Integrable f μ) : AEStronglyMeasurable (Q f) μ :=
    hPc.aestronglyMeasurable.mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable.norm)
  have hstep (f : E → V) (x : E) : Q (fwdDiff h f) x ≤ C * Q f (x + h) + Q f x := by
    change P x * Real.sqrt ‖f (x + h) - f x‖ ≤ _
    have htri := (Real.sqrt_le_sqrt (norm_sub_le (f (x + h)) (f x))).trans
      (sqrt_add_le_sum_sqrt (norm_nonneg _) (norm_nonneg _))
    calc
      _ ≤ P x * (Real.sqrt ‖f (x + h)‖ + Real.sqrt ‖f x‖) :=
        mul_le_mul_of_nonneg_left htri (hP x)
      _ = P x * Real.sqrt ‖f (x + h)‖ + Q f x := mul_add ..
      _ ≤ _ := add_le_add
        ((mul_le_mul_of_nonneg_right (hshift x) (Real.sqrt_nonneg _)).trans_eq (mul_assoc ..)) le_rfl
  let D (j : ℕ) := (fwdDiff h)^[j] k
  have hDs (j : ℕ) : D (j + 1) = fwdDiff h (D j) := by
    dsimp only [D]
    rw [Function.iterate_succ_apply']
  have hiter (j : ℕ) : Integrable (D j) μ ∧ Integrable (Q (D j)) μ ∧
      (∫ x, Q (D j) x ∂μ) ≤ (C + 1) ^ j * ∫ x, Q k x ∂μ := by
    induction j with
    | zero =>
      simpa only [D, Function.iterate_zero_apply, pow_zero, one_mul] using
        And.intro hk (And.intro hmom (le_refl (∫ x, Q k x ∂μ)))
    | succ j ih =>
      obtain ⟨hf, hQf, hb⟩ := ih
      rw [hDs]
      have hfd : Integrable (fwdDiff h (D j)) μ :=
        ((measurePreserving_add_right μ h).integrable_comp_of_integrable hf).sub hf
      have hQs : Integrable (fun x ↦ Q (D j) (x + h)) μ :=
        (measurePreserving_add_right μ h).integrable_comp_of_integrable hQf
      have hmajor := (hQs.const_mul C).add hQf
      have hQd := hmajor.mono' (hQmeas _ hfd) (ae_of_all _ fun x ↦ by
        rw [Real.norm_of_nonneg (hQ0 _ x)]
        exact hstep _ x)
      refine ⟨hfd, hQd, ?_⟩
      calc
        _ ≤ ∫ x, C * Q (D j) (x + h) + Q (D j) x ∂μ :=
          integral_mono hQd hmajor (hstep _)
        _ = (C + 1) * ∫ x, Q (D j) x ∂μ := by
          rw [integral_add (hQs.const_mul C) hQf, integral_const_mul, integral_add_right_eq_self]
          ring
        _ ≤ (C + 1) * ((C + 1) ^ j * ∫ x, Q k x ∂μ) :=
          mul_le_mul_of_nonneg_left hb (add_nonneg hC zero_le_one)
        _ = _ := by rw [pow_succ]; ring
  obtain ⟨hf, hQf, hlast⟩ := hiter m
  change (∫ x, ‖D m x‖ ∂μ) ≤ A * (C + 1) ^ m * ∫ x, Q k x ∂μ
  calc
    _ ≤ ∫ x, A * Q (D m) x ∂μ := by
      refine integral_mono hf.norm (hQf.const_mul A) fun x ↦ ?_
      have hr : Real.sqrt ‖D m x‖ ≤ A * P x := Real.sqrt_le_iff.mpr
        ⟨mul_nonneg hA (hP x), hpoint x⟩
      calc
        ‖D m x‖ = Real.sqrt ‖D m x‖ * Real.sqrt ‖D m x‖ :=
          (Real.mul_self_sqrt (norm_nonneg _)).symm
        _ ≤ (A * P x) * Real.sqrt ‖D m x‖ :=
          mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg _)
        _ = _ := mul_assoc ..
    _ = A * ∫ x, Q (D m) x ∂μ := by rw [integral_const_mul]
    _ ≤ A * ((C + 1) ^ m * ∫ x, Q k x ∂μ) := mul_le_mul_of_nonneg_left hlast hA
    _ = _ := by rw [mul_assoc]

/-- Along an additive map, iterating unit differences on a real line agrees
with iterating the corresponding shift in the target group. -/
theorem fwdDiff_iter_along_addMonoidHom {E L V : Type*}
    [AddCommMonoid E] [AddCommGroup L] [Module ℝ L] [AddCommGroup V]
    (n : ℕ) (j : L →+ E) (v : L) (k : E → V) (x : E) :
    (fwdDiff (1 : ℝ))^[n] (fun t ↦ k (x + j (t • v))) =
      fun t ↦ ((fwdDiff (j v))^[n] k) (x + j (t • v)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        _ = fwdDiff (1 : ℝ) (fun t ↦ ((fwdDiff (j v))^[n] k) (x + j (t • v))) := by
          rw [Function.iterate_succ_apply', ih]
        _ = _ := by
          rw [Function.iterate_succ_apply']
          funext t
          simp only [fwdDiff, add_smul, one_smul, map_add, add_assoc]

/-- Each forward difference multiplies the Fourier integral by the inverse phase
minus one. The differences remain integrable. -/
private theorem fourierIntegral_circleCharacter_iteratedTranslation {E : Type*} [NormedCommRing E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddLeftInvariant]
    (χ : Multiplicative E →ₜ* Circle) (k : E → ℂ) (hk : Integrable k μ) (r h : E) (n : ℕ) :
    Integrable ((fwdDiff h)^[n] k) μ ∧
      (∫ x, ((fwdDiff h)^[n] k) x * (χ (Multiplicative.ofAdd (x * r)) : ℂ) ∂μ) =
        (∫ x, k x * (χ (Multiplicative.ofAdd (x * r)) : ℂ) ∂μ) *
          ((χ (Multiplicative.ofAdd ((-h) * r)) : ℂ) - 1) ^ n := by
  let p (x : E) : ℂ := χ (Multiplicative.ofAdd (x * r))
  have hp : Continuous p := continuous_subtype_val.comp
    (χ.continuous.comp (continuous_ofAdd.comp (continuous_id.mul continuous_const)))
  have hn (x : E) : ‖p x‖ = 1 := Circle.norm_coe _
  have hadd (x y : E) : p (x + y) = p x * p y := by
    simp only [p, add_mul, ofAdd_add, map_mul, Circle.coe_mul]
  let I (f : E → ℂ) := ∫ x, f x * p x ∂μ
  have hshift (f : E → ℂ) (hf : Integrable f μ) : Integrable (fun x ↦ f (x + h)) μ :=
    (measurePreserving_add_right μ h).integrable_comp_of_integrable hf
  have hone (f : E → ℂ) (hf : Integrable f μ) : I (fwdDiff h f) = I f * (p (-h) - 1) := by
    have hi (g : E → ℂ) (hg : Integrable g μ) : Integrable (fun x ↦ g x * p x) μ :=
      hg.mul_bdd hp.aestronglyMeasurable (ae_of_all _ fun x ↦ (hn x).le)
    have hs : (∫ x, f (x + h) * p x ∂μ) = I f * p (-h) := by
      calc
        _ = ∫ x, f (x + h) * p (x + h + -h) ∂μ := by simp only [add_neg_cancel_right]
        _ = ∫ x, f x * p (x + -h) ∂μ := integral_add_right_eq_self (fun x ↦ f x * p (x + -h)) h
        _ = _ := by simp_rw [hadd, ← mul_assoc, integral_mul_const, I]
    change (∫ x, (f (x + h) - f x) * p x ∂μ) = _
    simp_rw [sub_mul]
    rw [integral_sub (hi _ (hshift f hf)) (hi _ hf), hs, mul_sub, mul_one]
  change Integrable ((fwdDiff h)^[n] k) μ ∧
    I ((fwdDiff h)^[n] k) = I k * (p (-h) - 1) ^ n
  induction n with
  | zero => simp [hk]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨(hshift _ ih.1).sub ih.1, ?_⟩
    rw [hone _ ih.1, ih.2, pow_succ, mul_assoc]

/-- Iterating additive translations bounds a Fourier coefficient by the L¹ norm
of the corresponding forward difference, with one character factor per step. -/
theorem fourierIntegral_circleCharacter_iteratedTranslation_bound {E : Type*} [NormedCommRing E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddLeftInvariant]
    (χ : Multiplicative E →ₜ* Circle) (k : E → ℂ) (hk : Integrable k μ) (r h : E) (n : ℕ) :
    ‖∫ x, k x * (χ (Multiplicative.ofAdd (x * r)) : ℂ) ∂μ‖ *
        ‖(χ (Multiplicative.ofAdd (r * h)) : ℂ) - 1‖ ^ n ≤
      ∫ x, ‖((fwdDiff h)^[n] k) x‖ ∂μ := by
  obtain ⟨hi, he⟩ := fourierIntegral_circleCharacter_iteratedTranslation μ χ k hk r h n
  let p (x : E) : ℂ := χ (Multiplicative.ofAdd (x * r))
  have hn (x : E) : ‖p x‖ = 1 := Circle.norm_coe _
  have hadd (x y : E) : p (x + y) = p x * p y := by
    simp only [p, add_mul, ofAdd_add, map_mul, Circle.coe_mul]
  have hp0 : p 0 = 1 := by simp [p]
  have hphase : ‖p (-h) - 1‖ = ‖p h - 1‖ := calc
    _ = ‖(p (-h) - 1) * p h‖ := by rw [norm_mul, hn, mul_one]
    _ = ‖1 - p h‖ := by rw [sub_mul, ← hadd, neg_add_cancel, hp0, one_mul]
    _ = _ := norm_sub_rev _ _
  rw [mul_comm r h]
  change ‖∫ x, k x * p x ∂μ‖ * ‖p h - 1‖ ^ n ≤ _
  rw [← hphase, ← norm_pow, ← norm_mul, ← he]
  exact norm_integral_le_of_norm_le hi.norm
    (ae_of_all _ fun x ↦ by simp only [norm_mul, Circle.norm_coe, mul_one, le_refl])

/-- A polynomial weight in the norm changes by a bounded factor in either
direction under a shift of norm at most one. -/
theorem one_add_norm_pow_shift_bounds {E : Type*} [NormedAddCommGroup E]
    (d : ℕ) (x h : E) (hh : ‖h‖ ≤ 1) :
    (1 + ‖x + h‖) ^ d ≤ (2 : ℝ) ^ d * (1 + ‖x‖) ^ d ∧
      (1 + ‖x‖) ^ d ≤ (2 : ℝ) ^ d * (1 + ‖x + h‖) ^ d := by
  have hforward (y z : E) (hz : ‖z‖ ≤ 1) :
      (1 + ‖y + z‖) ^ d ≤ (2 : ℝ) ^ d * (1 + ‖y‖) ^ d := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    linarith [norm_add_le y z, norm_nonneg y]
  refine ⟨hforward x h hh, ?_⟩
  simpa only [add_neg_cancel_right] using (hforward (x + h) (-h) (by simpa only [norm_neg] using hh))

/-- Uniform pointwise difference bounds for an amplitude and a bounded profile,
combined with a weighted square-root moment of the amplitude, bound the
`2 * n`th difference of the product in L¹ by the `n`th power of the shift norm. -/
theorem integral_norm_fwdDiff_iter_profileProduct_le {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddLeftInvariant]
    (n : ℕ) (H : Set E) (W : E → ℝ) (hWc : Continuous W) (hW : ∀ x, 1 ≤ W x)
    (g : E → ℂ) (hg : Integrable g μ)
    (hmom : Integrable (fun x ↦ W x * Real.sqrt ‖g x‖) μ)
    (q : ℝ → E → ℂ) {δ A B C M : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hq : ∀ t : ℝ, δ ≤ t → AEStronglyMeasurable (q t) μ)
    (hqbd : ∀ t : ℝ, δ ≤ t → ∀ x, ‖q t x‖ ≤ M)
    (hshift : ∀ h ∈ H, ‖h‖ ≤ 1 → ∀ x, W (x + h) ≤ C * W x ∧ W x ≤ C * W (x + h))
    (hgdiff : ∀ h ∈ H, ‖h‖ ≤ 1 → ∀ j ≤ 2 * n, ∀ x,
      ‖((fwdDiff h)^[j] g) x‖ ≤ A * ‖h‖ ^ j)
    (hqdiff : ∀ t : ℝ, δ ≤ t → ∀ h ∈ H, ‖h‖ ≤ 1 → ∀ j ≤ 2 * n, ∀ x,
      ‖((fwdDiff h)^[j] (q t)) x‖ ≤ B * ‖h‖ ^ j * W x) :
    let k (t : ℝ) (x : E) := g x * q t x
    ∃ K ≥ 0, ∀ t : ℝ, δ ≤ t →
      Integrable (k t) μ ∧ (∫ x, ‖k t x‖ ∂μ) ≤ M * (∫ x, ‖g x‖ ∂μ) ∧
        ∀ h ∈ H, ‖h‖ ≤ 1 → (∫ x, ‖((fwdDiff h)^[2 * n] (k t)) x‖ ∂μ) ≤ K * ‖h‖ ^ n := by
  intro k
  let U (x : E) := W x * Real.sqrt ‖g x‖
  let L := (C + 1) ^ (2 * n) * A * B
  let K := Real.sqrt L * (C + 1) ^ (2 * n) * Real.sqrt M * (∫ x, U x ∂μ)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hW0 (x : E) : 0 ≤ W x := zero_le_one.trans (hW x)
  have hU0 : 0 ≤ ∫ x, U x ∂μ := integral_nonneg fun x ↦ mul_nonneg (hW0 x) (Real.sqrt_nonneg _)
  refine ⟨K, by dsimp only [K]; positivity, fun t ht ↦ ?_⟩
  have hkt : Integrable (k t) μ := hg.mul_bdd (hq t ht) (ae_of_all _ (hqbd t ht))
  have hsize : (∫ x, ‖k t x‖ ∂μ) ≤ M * (∫ x, ‖g x‖ ∂μ) := by
    calc
      _ ≤ ∫ x, M * ‖g x‖ ∂μ := by
        refine integral_mono hkt.norm (hg.norm.const_mul M) fun x ↦ ?_
        change ‖g x * q t x‖ ≤ M * ‖g x‖
        rw [norm_mul, mul_comm M]
        exact mul_le_mul_of_nonneg_left (hqbd t ht x) (norm_nonneg _)
      _ = _ := integral_const_mul _ _
  let V (x : E) := W x * Real.sqrt ‖k t x‖
  have hVbd (x : E) : V x ≤ Real.sqrt M * U x := by
    change W x * Real.sqrt ‖g x * q t x‖ ≤ _
    rw [norm_mul, Real.sqrt_mul (norm_nonneg _)]
    calc
      _ ≤ W x * (Real.sqrt ‖g x‖ * Real.sqrt M) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hqbd t ht x)) (Real.sqrt_nonneg _)) (hW0 x)
      _ = _ := by dsimp only [U]; ring
  have hVi : Integrable V μ := by
    refine (hmom.const_mul (Real.sqrt M)).mono' ?_ (ae_of_all _ fun x ↦ ?_)
    · exact hWc.aestronglyMeasurable.mul
        (Real.continuous_sqrt.comp_aestronglyMeasurable hkt.aestronglyMeasurable.norm)
    · rw [Real.norm_of_nonneg (show 0 ≤ V x from mul_nonneg (hW0 x) (Real.sqrt_nonneg _))]
      exact hVbd x
  have hVint : (∫ x, V x ∂μ) ≤ Real.sqrt M * (∫ x, U x ∂μ) := by
    calc
      _ ≤ ∫ x, Real.sqrt M * U x ∂μ :=
        integral_mono hVi (hmom.const_mul (Real.sqrt M)) hVbd
      _ = _ := integral_const_mul _ _
  refine ⟨hkt, hsize, fun h hH hh ↦ ?_⟩
  have hp := norm_fwdDiff_iter_mul_le_of_bounds h (2 * n) W hC (norm_nonneg h)
    (fun x ↦ (hshift h hH hh x).1) g (q t) hA hB (hgdiff h hH hh) (hqdiff t ht h hH hh)
  have hpoint (x : E) :
      ‖((fwdDiff h)^[2 * n] (k t)) x‖ ≤ (Real.sqrt L * ‖h‖ ^ n * W x) ^ 2 := by
    have hWs : W x ≤ W x ^ 2 := by
      rw [pow_two]
      exact le_mul_of_one_le_right (hW0 x) (hW x)
    calc
      _ ≤ L * ‖h‖ ^ (2 * n) * W x := hp x
      _ ≤ L * ‖h‖ ^ (2 * n) * W x ^ 2 := mul_le_mul_of_nonneg_left hWs (by positivity)
      _ = _ := by simp only [mul_pow, ← pow_mul, Real.sq_sqrt hL, Nat.mul_comm n 2]
  calc
    _ ≤ (Real.sqrt L * ‖h‖ ^ n) * (C + 1) ^ (2 * n) * (∫ x, V x ∂μ) :=
      integral_norm_fwdDiff_iter_le_of_sq_weighted_bound μ (2 * n) h (k t) hkt W hWc hW0 hVi
        hC (by positivity) (fun x ↦ (hshift h hH hh x).2) hpoint
    _ ≤ (Real.sqrt L * ‖h‖ ^ n) * (C + 1) ^ (2 * n) * (Real.sqrt M * (∫ x, U x ∂μ)) :=
      mul_le_mul_of_nonneg_left hVint (by positivity)
    _ = _ := by dsimp only [K]; ring

end RiemannMasullo
