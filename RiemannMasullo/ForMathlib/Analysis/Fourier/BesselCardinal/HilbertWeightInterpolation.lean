module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Hadamard interpolation of unbounded weighted L² graph estimates

The interpolation family acts on the Hilbert space itself. Two independent clipped logarithms
permit the strong limit on inputs and Fatou’s lemma on outputs for an arbitrary continuous
nonnegative log weight. The endpoint constant is preserved on the closed interval.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace RiemannMasullo.WeakCardinal

private abbrev H (μ : Measure ℝ) := Lp ℂ 2 μ
private abbrev BC := ℝ →ᵇ ℂ

private theorem mulBound_mem (μ : Measure ℝ) (b : BC) (f : H μ) :
    MemLp (fun x ↦ b x * f x) 2 μ := by
  apply (Lp.memLp f).of_le_mul (b.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (c := ‖b‖)
  exact ae_of_all _ fun x ↦ by
    change ‖b x * f x‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (b.norm_coe_le_norm x) (norm_nonneg _)

private def mulBound (μ : Measure ℝ) (b : BC) (f : H μ) : H μ :=
  (mulBound_mem μ b f).toLp _

private theorem mulBound_ae (μ : Measure ℝ) (b : BC) (f : H μ) :
    (mulBound μ b f : ℝ → ℂ) =ᵐ[μ] fun x ↦ b x * f x :=
  (mulBound_mem μ b f).coeFn_toLp

/-- The continuous bilinear action of bounded continuous complex coefficients on angular L². -/
@[no_expose] def boundedMultiplierAction (μ : Measure ℝ) : (ℝ →ᵇ ℂ) →L[ℂ] Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous₂ (LinearMap.mk₂ ℂ (mulBound μ)
    (fun b c f ↦ by
      apply Lp.ext
      filter_upwards [mulBound_ae μ (b+c) f, mulBound_ae μ b f, mulBound_ae μ c f,
        Lp.coeFn_add (mulBound μ b f) (mulBound μ c f)] with x h₁ h₂ h₃ h₄
      rw [h₁, h₄, Pi.add_apply, h₂, h₃]
      exact add_mul _ _ _)
    (fun r b f ↦ by
      apply Lp.ext
      filter_upwards [mulBound_ae μ (r • b) f, mulBound_ae μ b f,
        Lp.coeFn_smul r (mulBound μ b f)] with x h₁ h₂ h₃
      simp [h₁,h₂,h₃,mul_assoc])
    (fun b f g ↦ by
      apply Lp.ext
      filter_upwards [mulBound_ae μ b (f+g), mulBound_ae μ b f, mulBound_ae μ b g,
        Lp.coeFn_add f g, Lp.coeFn_add (mulBound μ b f) (mulBound μ b g)] with x h₁ h₂ h₃ h₄ h₅
      rw [h₁, h₄, h₅, Pi.add_apply, Pi.add_apply, h₂, h₃]
      exact mul_add _ _ _)
    (fun r b f ↦ by
      apply Lp.ext
      filter_upwards [mulBound_ae μ b (r • f), mulBound_ae μ b f, Lp.coeFn_smul r f,
        Lp.coeFn_smul r (mulBound μ b f)] with x h₁ h₂ h₃ h₄
      simp [h₁,h₂,h₃,h₄,mul_left_comm])) 1 (fun b f ↦ by
        rw [one_mul]
        apply Lp.norm_le_mul_norm_of_ae_le_mul
        filter_upwards [mulBound_ae μ b f] with x hx
        change ‖mulBound μ b f x‖ ≤ _
        rw [hx, norm_mul]
        gcongr
        exact b.norm_coe_le_norm x)

theorem boundedMultiplierAction_ae (μ : Measure ℝ) (b : ℝ →ᵇ ℂ) (f : Lp ℂ 2 μ) :
    (boundedMultiplierAction μ b f : ℝ → ℂ) =ᵐ[μ] fun x ↦ b x * f x :=
  mulBound_ae μ b f

private def tilt (b : BC) (z : ℂ) : BC := NormedSpace.exp (z • b)

private theorem tilt_apply (b : BC) (z : ℂ) (x : ℝ) :
    tilt b z x = Complex.exp (z * b x) := by
  let ev : BC →+* ℂ :=
    { toFun := fun g ↦ g x, map_one' := rfl, map_mul' := fun _ _ ↦ rfl,
      map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  have he : Continuous ev := (BoundedContinuousFunction.lipschitz_eval_const x).continuous
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.map_exp ev he (z • b)

private theorem differentiable_tilt (b : BC) : Differentiable ℂ (tilt b) :=
  differentiable_exp_smul_const ℂ b

private def clippedLog (l : ℝ → ℝ) (hl : Continuous l) (hl₀ : ∀ x, 0 ≤ l x) (n : ℕ) : BC :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ ((min (n : ℝ) (l x) : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (continuous_const.min hl)) n fun x ↦ by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_min (Nat.cast_nonneg n) (hl₀ x))]
      exact min_le_left _ _

private def boundedTilt (μ : Measure ℝ) {l : ℝ → ℝ} (hl : Continuous l)
    (hl₀ : ∀ x, 0 ≤ l x) (n : ℕ) (z : ℂ) : H μ →L[ℂ] H μ :=
  boundedMultiplierAction μ (tilt (clippedLog l hl hl₀ n) z)

private theorem boundedTilt_ae (μ : Measure ℝ) {l : ℝ → ℝ} (hl : Continuous l)
    (hl₀ : ∀ x, 0 ≤ l x) (n : ℕ) (z : ℂ) (f : H μ) :
    (boundedTilt μ hl hl₀ n z f : ℝ → ℂ) =ᵐ[μ]
      fun x ↦ Complex.exp (z * (min (n : ℝ) (l x) : ℝ)) * f x := by
  filter_upwards [boundedMultiplierAction_ae μ (tilt (clippedLog l hl hl₀ n) z) f] with x hx
  exact hx.trans (congrArg (· * f x) (tilt_apply _ _ _))

private theorem boundedTilt_norm_ae (μ : Measure ℝ) {l : ℝ → ℝ} (hl : Continuous l)
    (hl₀ : ∀ x, 0 ≤ l x) (n : ℕ) (z : ℂ) (f : H μ) :
    ∀ᵐ x ∂μ, ‖boundedTilt μ hl hl₀ n z f x‖ =
      Real.exp (z.re * min (n : ℝ) (l x)) * ‖f x‖ := by
  filter_upwards [boundedTilt_ae μ hl hl₀ n z f] with x hx
  simp [hx, Complex.norm_exp, Complex.mul_re]

private theorem differentiable_boundedTilt (μ : Measure ℝ) {l : ℝ → ℝ} (hl : Continuous l)
    (hl₀ : ∀ x, 0 ≤ l x) (n : ℕ) : Differentiable ℂ (boundedTilt μ hl hl₀ n) :=
  (boundedMultiplierAction μ).differentiable.comp (differentiable_tilt _)

/-- A compatible order-two graph estimate for the weight exp(l).
Both endpoint vectors are represented in the same unweighted L². -/
def WeightGraphBound {μ : Measure ℝ} (l : ℝ → ℝ) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (C : ℝ) : Prop :=
  ∀ f j : Lp ℂ 2 μ, (j : ℝ → ℂ) =ᵐ[μ] (fun x ↦ (Real.exp (l x) : ℂ) * f x) →
    ∃ k : Lp ℂ 2 μ, (k : ℝ → ℂ) =ᵐ[μ] (fun x ↦ (Real.exp (l x) : ℂ) * T f x) ∧ ‖k‖ ≤ C * ‖j‖

private theorem clipped_threeLines {μ : Measure ℝ} {l : ℝ → ℝ} (hl : Continuous l)
    (hl₀ : ∀ x, 0 ≤ l x) (T : H μ →L[ℂ] H μ) {C : ℝ} (hC : 0 ≤ C)
    (h₀ : ‖T‖ ≤ C) (h₁ : WeightGraphBound l T C) (g j : H μ)
    (hj : (j : ℝ → ℂ) =ᵐ[μ] fun x ↦ (Real.exp (l x) : ℂ) * g x) (m n : ℕ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖boundedTilt μ hl hl₀ n (t : ℂ) (T (boundedTilt μ hl hl₀ m (1-(t : ℂ)) g))‖ ≤ C * ‖j‖ := by
  let A := boundedTilt μ hl hl₀
  let F (z : ℂ) := A n z (T (A m (1-z) g))
  have hd : Differentiable ℂ F :=
    (differentiable_boundedTilt μ hl hl₀ n).clm_apply (T.differentiable.comp
      (((differentiable_boundedTilt μ hl hl₀ m).comp
        ((differentiable_const (1 : ℂ)).sub differentiable_id)).clm_apply (differentiable_const _)))
  have hi (z : ℂ) (hz : 0 ≤ z.re) : ‖A m (1-z) g‖ ≤ ‖j‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [boundedTilt_norm_ae μ hl hl₀ m (1-z) g, hj] with x hx h
    rw [hx, h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    simp only [Complex.sub_re, Complex.one_re]
    have ha := le_min (Nat.cast_nonneg m) (hl₀ x)
    have hb := min_le_right (m : ℝ) (l x)
    nlinarith [mul_nonneg hz ha]
  have hT (f : H μ) : ‖T f‖ ≤ C * ‖f‖ :=
    (T.le_opNorm f).trans (mul_le_mul_of_nonneg_right h₀ (norm_nonneg _))
  have hstrip (z : ℂ) (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1) :
       ‖F z‖ ≤ Real.exp n * (C * ‖j‖) := by
    have hG : ‖F z‖ ≤ Real.exp n * ‖T (A m (1-z) g)‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [boundedTilt_norm_ae μ hl hl₀ n z (T (A m (1-z) g))] with x hx
      rw [hx]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_right hz.2 (le_min (Nat.cast_nonneg n) (hl₀ x))).trans
        (by simp)
    exact hG.trans (mul_le_mul_of_nonneg_left ((hT _).trans
      (mul_le_mul_of_nonneg_left (hi z hz.1) hC)) (Real.exp_pos _).le)
  have hleft (z : ℂ) (hz : z ∈ Complex.re ⁻¹' {0}) : ‖F z‖ ≤ C * ‖j‖ := by
    have hz' : z.re = 0 := hz
    have hG : ‖F z‖ ≤ ‖T (A m (1-z) g)‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [boundedTilt_norm_ae μ hl hl₀ n z (T (A m (1-z) g))] with x hx
      exact (by simpa [hz'] using hx : ‖F z x‖ = _).le
    exact hG.trans ((hT _).trans (mul_le_mul_of_nonneg_left (hi z hz'.ge) hC))
  have hright (z : ℂ) (hz : z ∈ Complex.re ⁻¹' {1}) : ‖F z‖ ≤ C * ‖j‖ := by
    have hz' : z.re = 1 := hz
    let k₀ := A m (1-z) j
    have hk₀ : (k₀ : ℝ → ℂ) =ᵐ[μ] fun x ↦
        (Real.exp (l x) : ℂ) * (A m (1-z) g) x := by
      filter_upwards [boundedTilt_ae μ hl hl₀ m (1-z) g,
        boundedTilt_ae μ hl hl₀ m (1-z) j, hj] with x hx hy h
      change (boundedTilt μ hl hl₀ m (1-z) j) x = _ * (boundedTilt μ hl hl₀ m (1-z) g) x
      rw [hx,hy,h,mul_left_comm]
    have hk₀norm : ‖k₀‖ ≤ ‖j‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [boundedTilt_norm_ae μ hl hl₀ m (1-z) j] with x hx
      exact (by simpa [hz'] using hx : ‖k₀ x‖ = _).le
    obtain ⟨k, hk, hkn⟩ := h₁ _ k₀ hk₀
    have hG : ‖F z‖ ≤ ‖k‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [boundedTilt_norm_ae μ hl hl₀ n z (T (A m (1-z) g)), hk] with x hx h
      rw [hx, h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        hz',one_mul]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (min_le_right _ _)) (norm_nonneg _)
    exact hG.trans (hkn.trans (mul_le_mul_of_nonneg_left hk₀norm hC))
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' F
    (z := (t : ℂ)) ht hd.diffContOnCl ⟨_, fun _ ⟨z,hz,he⟩ ↦ he.ge.trans (hstrip z hz)⟩ hleft hright
  simpa only [Complex.ofReal_re, ← Real.rpow_add_of_nonneg (mul_nonneg hC (norm_nonneg _))
    (sub_nonneg.mpr ht.2) ht.1, sub_add_cancel, Real.rpow_one] using h

/-- The squared Hilbert norm equals the integral of the squared representative. -/
theorem complexLp_norm_sq_integral {μ : Measure ℝ} (f : Lp ℂ 2 μ) :
    ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  apply Complex.ofReal_injective
  have h : ((‖f‖^2 : ℝ) : ℂ) = inner ℂ f f := by
    simpa only [Complex.ofReal_pow, RCLike.ofReal_eq_complex_ofReal] using
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f).symm
  rw [h, L2.inner_def, ← integral_complex_ofReal]
  simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow]

private theorem tendsto_L2_of_dominated_eventual {μ : Measure ℝ} {f : H μ}
    {v : ℕ → H μ} (hdom : ∀ n, ∀ᵐ x ∂μ, ‖v n x‖ ≤ ‖f x‖)
    (heq : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, v n x = f x) : Tendsto v atTop (𝓝 f) := by
  have hm (n : ℕ) : AEStronglyMeasurable (fun x ↦ ‖(v n - f) x‖ ^ 2) μ :=
    (Lp.aestronglyMeasurable _).norm.pow 2
  have hb : Integrable (fun x ↦ 4 * ‖f x‖^2) μ :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)).const_mul 4
  have hbnd (n : ℕ) : ∀ᵐ x ∂μ, ‖‖(v n - f) x‖^2‖ ≤ 4 * ‖f x‖^2 := by
    filter_upwards [hdom n, Lp.coeFn_sub (v n) f] with x hx hy
    rw [hy, Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (_ : ℝ))]
    have ha := (norm_sub_le (v n x) (f x)).trans (add_le_add_left hx _)
    nlinarith [sq_nonneg ‖f x‖, mul_self_le_mul_self (norm_nonneg _) ha]
  have hpt : ∀ᵐ x ∂μ, Tendsto (fun n ↦ ‖(v n - f) x‖^2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [heq, ae_all_iff.2 (fun n ↦ Lp.coeFn_sub (v n) f)] with x hx hy
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hx] with n hn
    rw [hy n, Pi.sub_apply, hn, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  have hconv := tendsto_integral_of_dominated_convergence _ hm hb hbnd hpt
  simp only [integral_zero, ← complexLp_norm_sq_integral] at hconv
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    (Real.continuous_sqrt.continuousAt.tendsto.comp hconv)

private def inverseExponential (l : ℝ → ℝ) (hl : Continuous l) (hl₀ : ∀ x, 0 ≤ l x) : BC :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ (Real.exp (-l x) : ℂ))
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp hl.neg)) 1 fun x ↦ by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hl₀ x))

private theorem boundedTilt_real_ae (μ : Measure ℝ) {l : ℝ → ℝ} (hl : Continuous l)
    (hl₀ : ∀ x, 0 ≤ l x) (n : ℕ) (t : ℝ) (f : H μ) :
    (boundedTilt μ hl hl₀ n (t : ℂ) f : ℝ → ℂ) =ᵐ[μ]
      fun x ↦ (Real.exp (t * min (n : ℝ) (l x)) : ℂ) * f x := by
  simpa only [Complex.ofReal_exp, Complex.ofReal_mul] using boundedTilt_ae μ hl hl₀ n (t : ℂ) f

private theorem eventual_clip_eq (l : ℝ → ℝ) (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, min (n : ℝ) (l x) = l x := by
  obtain ⟨k, hk⟩ := exists_nat_ge (l x)
  filter_upwards [eventually_ge_atTop k] with n hn
  exact min_eq_right (hk.trans (by exact_mod_cast hn))

/-- Hadamard interpolation of the actual graph of a weighted L² operator. The upper endpoint
uses multiplication by exp(l), and the result uses multiplication by exp(t·l) for every
t in the closed unit interval. The same constant holds without truncating either vector. -/
theorem interpolateWeightGraph {μ : Measure ℝ} {l : ℝ → ℝ} (hl : Continuous l)
    (hl₀ : ∀ x, 0 ≤ l x) (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (h₀ : ‖T‖ ≤ C) (h₁ : WeightGraphBound l T C) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    WeightGraphBound (fun x ↦ t * l x) T C := by
  intro u j hj
  let g := boundedMultiplierAction μ (inverseExponential l hl hl₀) j
  have hg : (g : ℝ → ℂ) =ᵐ[μ] fun x ↦ (Real.exp (-l x) : ℂ) * j x :=
    boundedMultiplierAction_ae _ _ _
  have hgj : (j : ℝ → ℂ) =ᵐ[μ] fun x ↦ (Real.exp (l x) : ℂ) * g x := by
    filter_upwards [hg] with x hx
    rw [hx, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, Complex.ofReal_one, one_mul]
  let V (n : ℕ) := boundedTilt μ hl hl₀ n ((1-t : ℝ) : ℂ) g
  have hV (n : ℕ) : (V n : ℝ → ℂ) =ᵐ[μ] fun x ↦
      (Real.exp ((1-t) * (min (n : ℝ) (l x) - l x)) : ℂ) * u x := by
    filter_upwards [boundedTilt_real_ae μ hl hl₀ n (1-t) g, hg, hj] with x h₁ h₂ h₃
    rw [h₁,h₂,h₃, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, ← mul_assoc,
      ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring
  have hVlim : Tendsto V atTop (𝓝 u) := by
    apply tendsto_L2_of_dominated_eventual
    · intro n
      filter_upwards [hV n] with x hx
      rw [hx,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht.2) (sub_nonpos.mpr (min_le_right _ _))))
    · filter_upwards [ae_all_iff.2 hV] with x hx
      filter_upwards [eventual_clip_eq l x] with n hn
      simp [hx n, hn]
  let O (n : ℕ) := boundedTilt μ hl hl₀ n (t : ℂ) (T u)
  have hb (n : ℕ) : ‖O n‖ ≤ C * ‖j‖ := by
    apply le_of_tendsto' (((boundedTilt μ hl hl₀ n (t:ℂ)).continuous.continuousAt.tendsto.comp
      (T.continuous.continuousAt.tendsto.comp hVlim)).norm)
    intro m
    simpa only [Function.comp_apply, V, Complex.ofReal_sub, Complex.ofReal_one] using
      clipped_threeLines hl hl₀ T hC h₀ h₁ g j hgj m n ht
  let out (x : ℝ) := (Real.exp (t*l x) : ℂ) * T u x
  have hm : AEStronglyMeasurable out μ :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hl))).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable _)
  have hpt : ∀ᵐ x ∂μ, Tendsto (fun n ↦ O n x) atTop (𝓝 (out x)) := by
    filter_upwards [ae_all_iff.2 (fun n ↦ boundedTilt_real_ae μ hl hl₀ n t (T u))] with x hx
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [eventual_clip_eq l x] with n hn
    simpa only [hn, out] using (hx n).symm
  have hfat := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2)
    (fun n ↦ Lp.aestronglyMeasurable (O n)) out hm hpt
  have he : eLpNorm out 2 μ ≤ ENNReal.ofReal (C * ‖j‖) := by
    apply hfat.trans
    refine Filter.liminf_le_of_frequently_le ?_ ⟨0, .of_forall fun _ ↦ bot_le⟩
    apply Filter.Eventually.frequently
    exact .of_forall fun n ↦ by
      rw [← Lp.eNorm_def, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hb n)
  have mem : MemLp out 2 μ := he.trans_lt ENNReal.ofReal_lt_top
  refine ⟨mem.toLp out, mem.coeFn_toLp, ?_⟩
  rw [Lp.norm_toLp]
  simpa only [ENNReal.toReal_ofReal (mul_nonneg hC (norm_nonneg _))] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top he

end RiemannMasullo.WeakCardinal
