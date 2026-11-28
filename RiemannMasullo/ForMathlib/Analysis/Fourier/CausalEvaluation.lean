module

public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Causal realization of the exponential evaluation kernel

The functions `1_{(-∞,t]}(r) exp(r-t)` are a total family in complex `L²(ℝ)`.
Their Gram is one half of the exponential kernel. A separated family of Hilbert
space observations with this Gram therefore determines the norm of a vector
from its scalar Volterra primitive on a single component.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set
open scoped InnerProductSpace Interval Topology

namespace RiemannMasullo.LineGeometricFourier

/-- The scalar causal kernel at the sample time, before its global normalization. -/
def causalRaw (t : ℝ) : ℝ → ℂ := (Iic t).indicator fun x ↦ (Real.exp (x - t) : ℂ)

/-- The causal kernel is square-integrable at every real sample time. -/
theorem causalRaw_memLp (t : ℝ) : MemLp (causalRaw t) 2 volume := by
  rw [causalRaw, memLp_indicator_iff_restrict measurableSet_Iic.nullMeasurableSet]
  apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).2
  have hi := (integrableOn_exp_mul_Iic (a := 2) (by norm_num) t).mul_const (Real.exp (-2 * t))
  apply hi.congr (.of_forall fun x ↦ ?_)
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), sq]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- An unnormalized causal evaluation vector in ordinary complex L² of the real line. -/
def causal (t : ℝ) : Lp ℂ 2 (volume : Measure ℝ) := (causalRaw_memLp t).toLp (causalRaw t)

/-- Its observed value on an L² vector is a truncated ordinary integral. -/
theorem causal_inner (t : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ⟪causal t, g⟫_ℂ = ∫ x in Iic t, (Real.exp (x - t) : ℂ) * g x := by
  rw [← integral_indicator measurableSet_Iic, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(causalRaw_memLp t).coeFn_toLp] with x hx
  change ((causal t) x) = causalRaw t x at hx
  rw [hx]
  by_cases ht : x ∈ Iic t
  · rw [causalRaw, indicator_of_mem ht, indicator_of_mem ht]
    change g x * (starRingEnd ℂ) (↑(Real.exp (x-t))) = (↑(Real.exp (x-t))) * g x
    rw [show (starRingEnd ℂ) (↑(Real.exp (x-t))) = ↑(Real.exp (x-t)) from Complex.conj_ofReal _,
      mul_comm]
  · simp [causalRaw, ht]

/-- The exponential Gram has its exact factor one half on the full continuum. -/
theorem causal_gram (t u : ℝ) :
    ⟪causal t, causal u⟫_ℂ = (((1 / 2 : ℝ) * Real.exp (-|t-u|) : ℝ) : ℂ) := by
  rw [causal_inner, ← integral_indicator measurableSet_Iic]
  have he : ∀ᵐ x : ℝ, (Iic t).indicator (fun y ↦ (Real.exp (y-t) : ℂ) * causal u y) x =
      (Iic (min t u)).indicator (fun y ↦ ((Real.exp (2 * y) * Real.exp (-t-u) : ℝ) : ℂ)) x := by
    filter_upwards [(causalRaw_memLp u).coeFn_toLp] with x hx
    change causal u x = causalRaw u x at hx
    by_cases hxt : x ≤ t <;> by_cases hxu : x ≤ u
    · have hxm := le_min hxt hxu
      simp only [mem_Iic, hxt, hxu, hxm, indicator_of_mem, hx, causalRaw]
      norm_cast
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    · simp [causalRaw, mem_Iic, hxt, hxu, hx, le_min_iff]
    · simp [mem_Iic, hxt, le_min_iff]
    · simp [mem_Iic, hxt, le_min_iff]
  rw [integral_congr_ae he, integral_indicator measurableSet_Iic, integral_complex_ofReal,
    integral_mul_const, integral_exp_mul_Iic (a := 2) (by norm_num)]
  congr 1
  rw [div_mul_eq_mul_div, ← Real.exp_add]
  have he' : 2 * min t u + (-t - u) = -|t-u| := by
    rcases le_total t u with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  rw [he']
  ring

/-- If a scalar residual has a piecewise integrable first derivative, the only
additional identity needed to reproduce it is the integrated first-order ODE. -/
theorem causal_realizes {g : ℝ → ℂ} (hg : MemLp g 2 volume) (f : ℝ → ℂ)
    (hprimitive : ∀ t, ∫ x in Iic t, (Real.exp (x - t) : ℂ) * g x = f t) (t : ℝ) :
    ⟪causal t, hg.toLp g⟫_ℂ = f t := by
  rw [causal_inner, ← hprimitive]
  exact integral_congr_ae ((ae_restrict_of_ae hg.coeFn_toLp).mono fun x hx ↦ congrArg (_ * ·) hx)

/-- If the Volterra exponential integral is zero at every real time, the L²
function vanishes. Its exponentially weighted indefinite integral is locally
absolutely continuous, and Lebesgue differentiation recovers the integrand. -/
theorem causal_separates (g : Lp ℂ 2 (volume : Measure ℝ)) (hz : ∀ t, ⟪causal t, g⟫_ℂ = 0) : g = 0 := by
  let f := fun x : ℝ ↦ (Real.exp x : ℂ) * g x
  have he (t : ℝ) : f = fun x ↦ (Real.exp t : ℂ) * ((Real.exp (x-t) : ℂ) * g x) := by
    funext x
    dsimp only [f]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, show t+(x-t) = x by ring]
  have hi (t : ℝ) : IntegrableOn f (Iic t) := by
    rw [he t]
    apply Integrable.const_mul
    refine ((causalRaw_memLp t).integrable_mul (Lp.memLp g)).integrableOn.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    simp only [Pi.mul_apply, causalRaw, indicator_of_mem hx]
  have hzero (t : ℝ) : ∫ x in Iic t, f x = 0 := by
    rw [he t, integral_const_mul, ← causal_inner, hz, mul_zero]
  have hl : LocallyIntegrable f volume := fun x ↦
    ⟨Iic (x+1), Iic_mem_nhds (by linarith), hi _⟩
  have hprim : (fun t ↦ ∫ x in (0 : ℝ)..t, f x) = fun _ ↦ 0 := by
    funext t
    rw [← intervalIntegral.integral_Iic_sub_Iic (hi 0) (hi t), hzero, hzero, sub_zero]
  apply Lp.ext
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hl,
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℝ))] with x hx h0
  have h := hx 0
  rw [hprim] at h
  have heq := h.unique (hasDerivAt_const x (0 : ℂ))
  change (Real.exp x : ℂ) * g x = 0 at heq
  rw [h0]
  exact (mul_eq_zero.mp heq).resolve_left (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne')

/-- The integrated derivative of a continuous piecewise differentiable function has
no contribution from its finite set of exceptional points. -/
theorem integral_sub_of_finite_joins {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f v : ℝ → E) (s : Finset ℝ) (hf : Continuous f)
    {a b : ℝ} (hab : a ≤ b) (hv : IntervalIntegrable v volume a b)
    (hd : ∀ x ∈ Ioo a b, x ∉ s → HasDerivAt f (v x) x) :
    ∫ x in a..b, v x = f b - f a := by
  classical
  induction s using Finset.induction_on generalizing a b with
  | empty =>
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hf.continuousOn
        (fun x hx ↦ hd x hx (by simp)) hv
  | @insert c s hcs ih =>
      by_cases hc : c ∈ Ioo a b
      · have hint := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hv
        have hl : IntervalIntegrable v volume a c :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le hc.1.le).mpr
            (hint.mono_set fun x hx ↦ ⟨hx.1, hx.2.trans hc.2.le⟩)
        have hr : IntervalIntegrable v volume c b :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le hc.2.le).mpr
            (hint.mono_set fun x hx ↦ ⟨hc.1.trans hx.1, hx.2⟩)
        have left := ih hc.1.le hl fun x hx hxs ↦ hd x ⟨hx.1, hx.2.trans hc.2⟩
          (by simpa only [Finset.mem_insert, not_or] using And.intro hx.2.ne hxs)
        have right := ih hc.2.le hr fun x hx hxs ↦ hd x ⟨hc.1.trans hx.1, hx.2⟩
          (by simpa only [Finset.mem_insert, not_or] using And.intro hx.1.ne' hxs)
        rw [← intervalIntegral.integral_add_adjacent_intervals hl hr, left, right]
        abel
      · exact ih hab hv fun x hx hxs ↦ hd x hx (by
          simpa only [Finset.mem_insert, not_or] using
            And.intro (fun h : x = c ↦ hc (h ▸ hx)) hxs)

/-- If the ordinary derivative of `p` equals `g-p` except at a finite set and
the boundary term vanishes at minus infinity, then the exact primitive required
by the physical row bound follows. Every truncation is covered, including a sample
at one of the joins. -/
theorem causal_primitive_of_finite_joins (p g : ℝ → ℂ) (s : Finset ℝ)
    (hp : Continuous p) (hg : MemLp g 2 volume)
    (hder : ∀ x ∉ s, HasDerivAt p (g x - p x) x)
    (hbot : Tendsto (fun x : ℝ ↦ (Real.exp x : ℂ) * p x) atBot (𝓝 0)) (t : ℝ) :
    ∫ x in Iic t, (Real.exp (x-t) : ℂ) * g x = p t := by
  let u := fun x : ℝ ↦ (Real.exp (x-t) : ℂ) * p x
  let v := fun x : ℝ ↦ (Real.exp (x-t) : ℂ) * g x
  have hu : Continuous u := by dsimp [u]; fun_prop
  have hi : IntegrableOn v (Iic t) := by
    apply ((causalRaw_memLp t).integrable_mul hg).integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    simp only [Pi.mul_apply, causalRaw, indicator_of_mem hx, v]
  have hd (x : ℝ) (hx : x ∉ s) : HasDerivAt u (v x) x := by
    have ht : HasDerivAt (fun y : ℝ ↦ (Real.exp (y-t) : ℂ)) (Real.exp (x-t) : ℂ) x := by
      simpa using! (((hasDerivAt_id x).sub_const t).exp).ofReal_comp
    convert ht.mul (hder x hx) using 1
    dsimp [v]
    ring
  have hlim : Tendsto u atBot (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (Real.exp (-t) : ℂ))).mul hbot
    rw [mul_zero] at h
    apply h.congr
    intro x
    dsimp [u]
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, sub_eq_add_neg, add_comm (-t)]
  have hf : (fun a ↦ ∫ x in a..t, v x) =ᶠ[atBot] fun a ↦ u t - u a := by
    filter_upwards [eventually_le_atBot t] with a ha
    exact integral_sub_of_finite_joins u v s hu ha
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha).mpr (hi.mono_set fun x hx ↦ hx.2))
      (fun x _ hxs ↦ hd x hxs)
  have he := tendsto_nhds_unique (intervalIntegral_tendsto_integral_Iic t hi tendsto_id)
    ((tendsto_const_nhds.sub hlim).congr' hf.symm)
  simpa [u, v] using he

section Hilbert

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Equality of the full evaluation kernels and of all observations transfers a
model vector norm to an upper bound on the physical vector norm. Only the physical
probes have to separate points. -/
private theorem norm_le_of_probe_gram {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (E : ι → StrongDual ℂ H) (p : ι → K)
    (hsep : ∀ w, (∀ i, E i w = 0) → w = 0)
    (hgram : ∀ i j, ⟪(InnerProductSpace.toDual ℂ H).symm (E i),
      (InnerProductSpace.toDual ℂ H).symm (E j)⟫_ℂ = ⟪p i, p j⟫_ℂ)
    {w : H} {v : K} (hvalue : ∀ i, E i w = ⟪p i, v⟫_ℂ) : ‖w‖ ≤ ‖v‖ := by
  let k (i : ι) := (InnerProductSpace.toDual ℂ H).symm (E i)
  let S := Submodule.span ℂ (range k)
  have htop : S.topologicalClosure = ⊤ := by
    apply Submodule.orthogonal_eq_bot_iff.mp ((Submodule.eq_bot_iff _).mpr ?_)
    intro u hu
    apply hsep u
    intro i
    rw [← InnerProductSpace.toDual_symm_apply]
    exact Submodule.inner_right_of_mem_orthogonal
      (S.le_topologicalClosure (Submodule.subset_span (mem_range_self i))) hu
  have hbound (g : H) (hg : g ∈ S) : ‖⟪g, w⟫_ℂ‖ ≤ ‖g‖ * ‖v‖ := by
    obtain ⟨c, rfl⟩ : g ∈ LinearMap.range (Finsupp.linearCombination ℂ k) := by
      rwa [Finsupp.range_linearCombination]
    let q := Finsupp.linearCombination ℂ p c
    have hpair : ⟪Finsupp.linearCombination ℂ k c, w⟫_ℂ = ⟪q, v⟫_ℂ := by
      simp only [q, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_smul_left,
        k, InnerProductSpace.toDual_symm_apply, hvalue]
    have hsq : ⟪Finsupp.linearCombination ℂ k c, Finsupp.linearCombination ℂ k c⟫_ℂ = ⟪q, q⟫_ℂ := by
      simp only [q, Finsupp.linearCombination_apply, Finsupp.sum, inner_sum, sum_inner,
        inner_smul_left, inner_smul_right, k, hgram]
    have hnorm : ‖Finsupp.linearCombination ℂ k c‖ = ‖q‖ := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      exact ((inner_self_eq_norm_sq (𝕜 := ℂ) _).symm.trans (congrArg Complex.re hsq)).trans
        (inner_self_eq_norm_sq (𝕜 := ℂ) q)
    rw [hpair, hnorm]
    exact norm_inner_le_norm q v
  have hall : ∀ g : H, ‖⟪g, w⟫_ℂ‖ ≤ ‖g‖ * ‖v‖ := by
    intro g
    apply (isClosed_le (continuous_id.inner continuous_const).norm (continuous_norm.mul continuous_const)).closure_subset_iff.mpr
      (fun g hg ↦ hbound g hg)
    change g ∈ S.topologicalClosure
    rw [htop]
    trivial
  have hf : ‖w‖ * ‖w‖ ≤ ‖w‖ * ‖v‖ := calc
    _ = (⟪w, w⟫_ℂ).re := by rw [← sq]; exact (inner_self_eq_norm_sq (𝕜 := ℂ) w).symm
    _ ≤ _ := (Complex.re_le_norm _).trans (hall w)
  rcases (norm_nonneg w).eq_or_lt with hw | hw
  · rw [← hw]
    exact norm_nonneg _
  · exact (le_of_mul_le_mul_left hf hw)

end Hilbert

local notation "L₂" => Lp ℂ 2 (volume : Measure ℝ)

private theorem norm_toLp_sq_integral (g : ℝ → ℂ) (hg : MemLp g 2 volume) :
    ‖hg.toLp g‖ ^ 2 = ∫ r, ‖g r‖ ^ 2 := by
  let w := hg.toLp g
  calc
    ‖w‖ ^ 2 = (⟪w, w⟫_ℂ).re := (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
    _ = ∫ r, (⟪w r, w r⟫_ℂ).re := by
      rw [L2.inner_def]
      exact (Complex.reCLM.integral_comp_comm (L2.integrable_inner (𝕜 := ℂ) w w)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hg.coeFn_toLp] with x hx
      change w x = g x at hx
      rw [hx]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) _

/-- A total family of probes with the exponential block Gram transfers the norm
of a scalar Volterra primitive into its ambient Hilbert space. -/
theorem norm_of_causal_probes {I H : Type*} [DecidableEq I] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (d : ℝ) (hd : 0 < d)
    (ell : I → ℝ → StrongDual ℂ H) (ω : I) (u : H) (g : ℝ → ℂ) (hg : MemLp g 2 volume)
    (hsep : ∀ w : H, (∀ ξ t, ell ξ t w = 0) → w = 0)
    (hk : ∀ ξ ζ s t, ⟪(InnerProductSpace.toDual ℂ H).symm (ell ξ s),
        (InnerProductSpace.toDual ℂ H).symm (ell ζ t)⟫_ℂ =
      if ξ = ζ then ((d * Real.exp (-|s-t|) : ℝ) : ℂ) else 0)
    (hown : ∀ t, ell ω t u = ∫ r in Iic t, (Real.exp (r-t) : ℂ) * g r)
    (hoff : ∀ ξ, ξ ≠ ω → ∀ t, ell ξ t u = 0) :
    (2 * d) * ‖u‖ ^ 2 = ∫ r, ‖g r‖ ^ 2 := by
  classical
  let q := Real.sqrt (2 * d)
  have hq : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have hq2 : q ^ 2 = 2 * d := Real.sq_sqrt (by positivity)
  have hqstar : (starRingEnd ℂ) (q : ℂ) = (q : ℂ) := Complex.conj_ofReal _
  have hqc : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  let E (i : I × ℝ) := ell i.1 i.2
  let p (i : I × ℝ) : lp (fun _ : I ↦ L₂) 2 := lp.single 2 i.1 ((q : ℂ) • causal i.2)
  let v : lp (fun _ : I ↦ L₂) 2 := lp.single 2 ω ((q : ℂ)⁻¹ • hg.toLp g)
  have hgram (i j : I × ℝ) : ⟪(InnerProductSpace.toDual ℂ H).symm (E i),
      (InnerProductSpace.toDual ℂ H).symm (E j)⟫_ℂ = ⟪p i, p j⟫_ℂ := by
    obtain ⟨ξ, s⟩ := i
    obtain ⟨ζ, t⟩ := j
    by_cases h : ξ = ζ
    · subst ζ
      dsimp only [p, E]
      rw [hk, ite_eq_left rfl, lp.inner_single_left, lp.single_apply_self,
        inner_smul_left, inner_smul_right, hqstar, causal_gram]
      norm_cast
      nlinarith [congrArg (· * Real.exp (-|s-t|)) hq2]
    · dsimp only [p, E]
      rw [hk, ite_eq_right h, lp.inner_single_left,
        lp.single_apply_ne _ _ _ h, inner_zero_right]
  have hval (i : I × ℝ) : E i u = ⟪p i, v⟫_ℂ := by
    obtain ⟨ξ, t⟩ := i
    by_cases h : ξ = ω
    · subst ξ
      change ell ω t u = _
      dsimp only [p, v]
      rw [lp.inner_single_left, lp.single_apply_self, inner_smul_left, inner_smul_right,
        hqstar, ← mul_assoc, mul_inv_cancel₀ hqc, one_mul]
      exact (causal_realizes hg (fun y ↦ ell ω y u) (fun y ↦ (hown y).symm) t).symm
    · change ell ξ t u = _
      dsimp only [p, v]
      rw [hoff ξ h t, lp.inner_single_left, lp.single_apply_ne _ _ _ h, inner_zero_right]
  have hb_le := norm_le_of_probe_gram E p (fun w hw ↦ hsep w fun ξ t ↦ hw (ξ,t)) hgram hval
  let M := lp (fun _ : I ↦ L₂) 2
  let obs (i : I × ℝ) := InnerProductSpace.toDual ℂ M (p i)
  let k (i : I × ℝ) := (InnerProductSpace.toDual ℂ H).symm (E i)
  have msep (w : M) (hw : ∀ i, obs i w = 0) : w = 0 := by
    apply Subtype.ext
    funext ξ
    change w ξ = (0 : L₂)
    apply causal_separates
    intro t
    have h := hw (ξ, t)
    change ⟪lp.single (E := fun _ : I ↦ L₂) 2 ξ ((q : ℂ) • causal t), w⟫_ℂ = 0 at h
    rw [lp.inner_single_left, inner_smul_left, hqstar] at h
    exact (mul_eq_zero.mp h).resolve_left hqc
  have mgram (i j : I × ℝ) : ⟪(InnerProductSpace.toDual ℂ M).symm (obs i),
      (InnerProductSpace.toDual ℂ M).symm (obs j)⟫_ℂ = ⟪k i, k j⟫_ℂ := by
    simpa only [obs, k, LinearIsometryEquiv.symm_apply_apply] using (hgram i j).symm
  have mval (i : I × ℝ) : obs i v = ⟪k i,u⟫_ℂ := by
    dsimp only [k]
    rw [InnerProductSpace.toDual_symm_apply]
    exact (hval i).symm
  have hb := le_antisymm hb_le (norm_le_of_probe_gram obs k msep mgram mval)
  change ‖u‖ = ‖lp.single (E := fun _ : I ↦ L₂) 2 ω ((q : ℂ)⁻¹ • hg.toLp g)‖ at hb
  rw [lp.norm_single (by norm_num), norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hq] at hb
  have hb' : q * ‖u‖ = ‖hg.toLp g‖ := by rw [hb, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]
  have hdone := congrArg (· ^ 2) hb'
  change (q * ‖u‖) ^ 2 = ‖hg.toLp g‖ ^ 2 at hdone
  rwa [mul_pow, hq2, norm_toLp_sq_integral] at hdone

end RiemannMasullo.LineGeometricFourier
