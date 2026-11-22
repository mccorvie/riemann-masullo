module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import RiemannMasullo.Ch03_IdelicZeta.Sec2
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.Convex.Measure

/-!
# §B.5 Recurrence and equidistribution

Continuous-time torus equidistribution, vertical self-approximation, and recurrence of
reciprocal finite Euler products.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open Complex.HadamardThreeLines (verticalStrip)
open scoped ENNReal NNReal Topology

namespace RiemannMasullo

section Torus

variable {N : ℕ}

/-- Paper: Definition B.5.1.1(1), p. 626.
The product torus, represented by Mathlib's `UnitAddTorus (Fin N)`, is compact Hausdorff. -/
theorem unitAddTorus_compactHausdorff (N : ℕ) :
    CompactSpace (UnitAddTorus (Fin N)) ∧ T2Space (UnitAddTorus (Fin N)) :=
  ⟨inferInstance, inferInstance⟩

/-- Paper: Definition B.5.1.1(2), p. 626.
The torus quotient reduces each real coordinate modulo one. -/
def torusQuotient (N : ℕ) : (Fin N → ℝ) →ₜ+ UnitAddTorus (Fin N) where
  toAddMonoidHom := AddMonoidHom.pi fun i ↦
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp (Pi.evalAddMonoidHom _ i)
  continuous_toFun := continuous_pi fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
    (continuous_apply i)

/-- Two real vectors have the same image in the torus precisely when their coordinate
differences are integers. -/
theorem torusQuotient_eq_iff (x y : Fin N → ℝ) :
    torusQuotient N x = torusQuotient N y ↔ ∀ i, ∃ m : ℤ, x i - y i = (m : ℝ) := by
  rw [funext_iff]
  refine forall_congr' fun i ↦ ?_
  change ((x i : ℝ) : AddCircle (1 : ℝ)) = (y i : AddCircle (1 : ℝ)) ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  exact exists_congr fun k ↦ by rw [zsmul_eq_mul, mul_one, eq_comm]

/-- Paper: Definition B.5.1.1(2), p. 626.
The hitting times are the times in the given interval when the projected curve belongs
to the image of the target set modulo one. -/
def torusHittingTimes (γ : ℝ → Fin N → ℝ) (J : Set ℝ) (U : Set (Fin N → ℝ)) : Set ℝ :=
  J ∩ (torusQuotient N ∘ γ) ⁻¹' (torusQuotient N '' U)

/-- The constant zero curve hits a singleton integer vector modulo one at every time. -/
theorem torusHittingTimes_zero_singleton_int (J : Set ℝ) (m : Fin N → ℤ) :
    torusHittingTimes (fun _ ↦ 0) J {fun i ↦ (m i : ℝ)} = J := by
  have h : torusQuotient N (fun i ↦ (m i : ℝ)) = torusQuotient N 0 :=
    (torusQuotient_eq_iff _ _).mpr fun i ↦ ⟨m i, sub_zero _⟩
  exact inter_eq_left.mpr fun t _ ↦ ⟨_, rfl, h⟩

/-- Paper: §B.5.1, p. 627.
The one-parameter torus subgroup of a frequency vector is the projection of its real line. -/
def torusFlow (τ : Fin N → ℝ) : ℝ →ₜ+ UnitAddTorus (Fin N) :=
  (torusQuotient N).comp (↑((ContinuousLinearMap.id ℝ ℝ).smulRight τ))

/-- At time one the flow has the phase given by the frequency vector modulo one. -/
theorem torusFlow_one (τ : Fin N → ℝ) : torusFlow τ 1 = torusQuotient N τ := by
  change torusQuotient N ((1 : ℝ) • τ) = torusQuotient N τ
  rw [one_smul]

-- TODO(paper-gap): The sentence before §B.5.2 claims injectivity also in dimension one.
-- For N = 1 and τ₁ = 1, times zero and one have the same image.

section Kronecker

open Real UnitAddTorus

/-- Each exponential monomial is a character of the torus. -/
private theorem mFourier_add_apply (n : Fin N → ℤ) (x y : UnitAddTorus (Fin N)) :
    mFourier n (x + y) = mFourier n x * mFourier n y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, smul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

/-- Along the flow, an exponential monomial is the exponential of the paired frequency. -/
private theorem mFourier_torusFlow (τ : Fin N → ℝ) (n : Fin N → ℤ) (t : ℝ) :
    mFourier n (torusFlow τ t) =
      Complex.exp (2 * π * Complex.I * ((∑ i, (n i : ℝ) * τ i : ℝ) : ℂ) * t) := by
  have h (i : Fin N) : (torusFlow τ t) i = ((t * τ i : ℝ) : AddCircle (1 : ℝ)) := rfl
  simp only [mFourier, ContinuousMap.coe_mk, h, fourier_coe_apply, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The time averages of a nonconstant imaginary exponential tend to zero. -/
private theorem tendsto_average_exp {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun T : ℝ ↦ (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, Complex.exp (2 * π * Complex.I * c * t))
      atTop (𝓝 0) := by
  have ha : (2 * π * Complex.I * c : ℂ) ≠ 0 := by
    simp [hc, Real.pi_ne_zero, Complex.I_ne_zero]
  have hint (T : ℝ) : ∫ t in (0 : ℝ)..T, Complex.exp (2 * π * Complex.I * c * t) =
      (Complex.exp (2 * π * Complex.I * c * T) - 1) / (2 * π * Complex.I * c) := by
    rw [integral_exp_mul_complex ha]; simp
  have hb (T : ℝ) : ‖Complex.exp (2 * π * Complex.I * c * T) - 1‖ ≤ 2 := by
    calc _ ≤ ‖Complex.exp (2 * π * Complex.I * c * T)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [show (2 * π * Complex.I * c * T : ℂ) = ((2 * π * c * T : ℝ) : ℂ) * Complex.I by
          push_cast; ring, Complex.norm_exp_ofReal_mul_I]
        norm_num
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (by simpa using tendsto_inv_atTop_zero.const_mul (2 / ‖(2 * π * Complex.I * c : ℂ)‖))
  refine (eventually_gt_atTop 0).mono fun T hT ↦ ?_
  rw [hint, norm_mul, norm_div, norm_inv, Complex.norm_real, Real.norm_of_nonneg hT.le,
    mul_comm]
  gcongr
  all_goals first
    | exact hb T
    | simp [abs_of_pos Real.pi_pos]

/-- Paper: §B.5.1, p. 627. Rationally independent frequencies give a dense
one-parameter subgroup of the ambient torus. -/
theorem torusFlow_denseRange_of_linearIndependent [NeZero N] {τ : Fin N → ℝ}
    (hτ : LinearIndependent ℚ τ) : DenseRange (torusFlow τ) := by
  -- Weyl's argument: time averages along the flow converge to the Haar integral, first for
  -- exponential monomials, then for all continuous functions by density and equicontinuity.
  classical
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨by simp [AddCircle.measure_univ]⟩
  let A : ℝ → C(UnitAddTorus (Fin N), ℂ) → ℂ :=
    fun T φ ↦ (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, φ (torusFlow τ t)
  have hII (φ : C(UnitAddTorus (Fin N), ℂ)) (T : ℝ) :
      IntervalIntegrable (fun t ↦ φ (torusFlow τ t)) volume 0 T :=
    (φ.continuous.comp (torusFlow τ).continuous).intervalIntegrable _ _
  have hInt (φ : C(UnitAddTorus (Fin N), ℂ)) : Integrable φ :=
    integrableOn_univ.mp (φ.continuous.continuousOn.integrableOn_compact isCompact_univ)
  -- Nonzero integer vectors pair with the frequencies to a nonzero number.
  have hc (n : Fin N → ℤ) (hn : n ≠ 0) : (∑ i, (n i : ℝ) * τ i) ≠ 0 := by
    intro h
    apply hn
    have h0 := Fintype.linearIndependent_iff.mp hτ (fun i ↦ (n i : ℚ)) (by
      simpa [Rat.smul_def] using h)
    funext i
    exact_mod_cast h0 i
  -- Integrals of the monomials.
  have hint (n : Fin N → ℤ) : ∫ x, mFourier n x = if n = 0 then 1 else 0 := by
    split_ifs with hn
    · subst hn; simp [mFourier_zero]
    · set c := ∑ i, (n i : ℝ) * τ i
      have hw : mFourier n (torusFlow τ (1 / (2 * c))) = -1 := by
        rw [mFourier_torusFlow, show 2 * (π : ℂ) * Complex.I * (c : ℂ) * ((1 / (2 * c) : ℝ) : ℂ) =
          π * Complex.I by
          push_cast; field_simp [hc n hn]; exact div_self (Complex.ofReal_ne_zero.mpr (hc n hn))]
        exact Complex.exp_pi_mul_I
      have h1 := integral_add_right_eq_self (μ := volume) (fun x ↦ mFourier n x)
        (torusFlow τ (1 / (2 * c)))
      simp only [mFourier_add_apply, hw, integral_mul_const] at h1
      linear_combination (-1 / 2 : ℂ) * h1
  -- Averages of the monomials converge to their integrals.
  have hF (n : Fin N → ℤ) : Tendsto (fun T ↦ A T (mFourier n)) atTop (𝓝 (∫ x, mFourier n x)) := by
    rw [hint]
    split_ifs with hn
    · subst hn
      refine tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun T hT ↦ ?_)
      simp [A, mFourier_zero, hT]
    · simp only [A, mFourier_torusFlow]
      exact tendsto_average_exp (hc n hn)
  -- Linearity of the averages.
  have hAsub (T : ℝ) (φ ψ : C(UnitAddTorus (Fin N), ℂ)) : A T φ - A T ψ = A T (φ - ψ) := by
    simp only [A, ContinuousMap.sub_apply, intervalIntegral.integral_sub (hII φ T) (hII ψ T),
      mul_sub]
  have hAadd (T : ℝ) (φ ψ : C(UnitAddTorus (Fin N), ℂ)) : A T (φ + ψ) = A T φ + A T ψ := by
    simp only [A, ContinuousMap.add_apply, intervalIntegral.integral_add (hII φ T) (hII ψ T),
      mul_add]
  have hAsmul (T : ℝ) (a : ℂ) (φ : C(UnitAddTorus (Fin N), ℂ)) : A T (a • φ) = a * A T φ := by
    simp only [A, ContinuousMap.smul_apply, smul_eq_mul, intervalIntegral.integral_const_mul]
    ring
  -- The averages are uniformly 1-Lipschitz.
  have hAnorm (T : ℝ) (φ : C(UnitAddTorus (Fin N), ℂ)) : ‖A T φ‖ ≤ ‖φ‖ := by
    rcases eq_or_ne T 0 with rfl | hT
    · simp [A]
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    calc |T|⁻¹ * ‖∫ t in (0 : ℝ)..T, φ (torusFlow τ t)‖ ≤ |T|⁻¹ * (‖φ‖ * |T - 0|) := by
          gcongr
          exact intervalIntegral.norm_integral_le_of_norm_le_const fun t _ ↦ φ.norm_coe_le_norm _
      _ = ‖φ‖ := by rw [sub_zero]; field_simp [abs_ne_zero.mpr hT]
  have hLip (T : ℝ) : LipschitzWith 1 (A T) := LipschitzWith.of_dist_le_mul fun φ ψ ↦ by
    rw [dist_eq_norm, dist_eq_norm, hAsub, NNReal.coe_one, one_mul]
    exact hAnorm T _
  have hIcont : Continuous fun φ : C(UnitAddTorus (Fin N), ℂ) ↦ ∫ x, φ x := by
    refine (LipschitzWith.of_dist_le_mul fun φ ψ ↦ ?_ : LipschitzWith 1 _).continuous
    rw [dist_eq_norm, dist_eq_norm, ← integral_sub (hInt φ) (hInt ψ), NNReal.coe_one, one_mul]
    calc ‖∫ x, (φ x - ψ x)‖ ≤ ‖φ - ψ‖ * (volume (univ : Set (UnitAddTorus (Fin N)))).toReal :=
          norm_integral_le_of_norm_le_const (Eventually.of_forall fun x ↦
            (φ - ψ).norm_coe_le_norm x)
      _ = ‖φ - ψ‖ := by simp
  let V : Set C(UnitAddTorus (Fin N), ℂ) :=
    {φ | Tendsto (fun T ↦ A T φ) atTop (𝓝 (∫ x, φ x))}
  have hVclosed : IsClosed V :=
    ((LipschitzWith.uniformEquicontinuous A 1 hLip).equicontinuous).isClosed_setOfPred_tendsto
      hIcont
  have hspan : ((Submodule.span ℂ (range (mFourier (d := Fin N))) :
      Set C(UnitAddTorus (Fin N), ℂ))) ⊆ V := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => obtain ⟨n, rfl⟩ := hx; exact hF n
    | zero => simp [V, A]
    | add φ ψ _ _ hφ hψ =>
      change Tendsto _ _ _
      simp only [hAadd, ContinuousMap.add_apply, integral_add (hInt φ) (hInt ψ)]
      exact hφ.add hψ
    | smul a φ _ hφ =>
      change Tendsto _ _ _
      simp only [hAsmul, ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]
      exact hφ.const_mul a
  have hall (φ : C(UnitAddTorus (Fin N), ℂ)) : φ ∈ V := by
    have hmem : φ ∈ (Submodule.span ℂ (range (mFourier (d := Fin N)))).topologicalClosure := by
      rw [span_mFourier_closure_eq_top]; trivial
    exact closure_minimal hspan hVclosed hmem
  -- A bump function away from the orbit closure has zero averages but positive integral.
  by_contra hd
  obtain ⟨p, hp⟩ : ∃ p, p ∉ closure (range (torusFlow τ)) :=
    not_forall.mp fun h ↦ hd (dense_iff_closure_eq.mpr (eq_univ_of_forall h))
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed isClosed_closure
    isClosed_singleton (disjoint_singleton_right.mpr hp)
  let φ : C(UnitAddTorus (Fin N), ℂ) := ⟨fun x ↦ (f x : ℂ), by fun_prop⟩
  have hA (T : ℝ) : A T φ = 0 := by
    have : ∀ t, φ (torusFlow τ t) = 0 := fun t ↦ by
      change ((f (torusFlow τ t) : ℝ) : ℂ) = 0
      rw [hf0 (subset_closure (mem_range_self t))]
      simp
    simp [A, this]
  have hzero : ∫ x, φ x = 0 :=
    tendsto_nhds_unique (hall φ) (by simp only [hA]; exact tendsto_const_nhds)
  have hpos : 0 < ∫ x, f x :=
    f.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero
      (HasCompactSupport.of_compactSpace _) (fun x ↦ (hf01 x).1) (x := p)
      (by rw [hf1 rfl]; norm_num)
  have : ∫ x, φ x = ((∫ x, f x : ℝ) : ℂ) := integral_ofReal
  rw [this] at hzero
  exact hpos.ne' (Complex.ofReal_eq_zero.mp hzero)

end Kronecker

/-- Paper: §B.5.1, p. 627. For at least two rationally independent frequencies,
distinct times give distinct phases.
Deviation: Adds the dimension hypothesis used in the proof on p. 628. -/
theorem torusFlow_injective_of_linearIndependent (hN : 2 ≤ N) {τ : Fin N → ℝ}
    (hτ : LinearIndependent ℚ τ) : Injective (torusFlow τ) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  have hint (i : Fin N) : ∃ m : ℤ, t * τ i = (m : ℝ) := by
    have h : torusQuotient N (t • τ) = torusQuotient N 0 := by
      rw [map_zero]
      exact ht
    obtain ⟨m, hm⟩ := (torusQuotient_eq_iff _ _).mp h i
    exact ⟨m, by simpa using hm⟩
  by_contra ht0
  let i₀ : Fin N := ⟨0, by omega⟩
  let i₁ : Fin N := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp [i₀, i₁])
  obtain ⟨m₀, h₀⟩ := hint i₀
  obtain ⟨m₁, h₁⟩ := hint i₁
  have hrel : (m₁ : ℚ) • τ i₀ + (-(m₀ : ℚ)) • τ i₁ = 0 := by
    have hmul : t * ((m₁ : ℝ) * τ i₀ - (m₀ : ℝ) * τ i₁) = 0 := by
      have h : t * ((m₁ : ℝ) * τ i₀ - (m₀ : ℝ) * τ i₁) =
          (m₁ : ℝ) * (t * τ i₀) - (m₀ : ℝ) * (t * τ i₁) := by ring
      rw [h, h₀, h₁]
      ring
    have hzero := (mul_eq_zero.mp hmul).resolve_left ht0
    rw [Rat.smul_def, Rat.smul_def]
    push_cast
    linarith
  have hm₁ : (m₁ : ℚ) = 0 :=
    ((LinearIndepOn.pair_iff τ hne).mp (hτ.comp _ Subtype.val_injective) _ _ hrel).1
  have hτ₁ : τ i₁ = 0 := by
    have hm₁' : (m₁ : ℝ) = 0 := by exact_mod_cast hm₁
    have h : t * τ i₁ = 0 := by rw [h₁, hm₁']
    exact (mul_eq_zero.mp h).resolve_left ht0
  exact hτ.ne_zero i₁ hτ₁

/-- Paper: Theorem B.5.2.1(1), p. 627.
The orbit closure is the closed additive subgroup obtained by closing the range of the flow. -/
def torusFlowClosure (τ : Fin N → ℝ) : AddSubgroup (UnitAddTorus (Fin N)) :=
  (torusFlow τ).toAddMonoidHom.range.topologicalClosure

/-- The zero frequency vector has the trivial orbit closure. -/
theorem torusFlowClosure_zero : torusFlowClosure (0 : Fin N → ℝ) = ⊥ := by
  have hrange : (torusFlow (0 : Fin N → ℝ)).toAddMonoidHom.range = ⊥ := by
    rw [AddMonoidHom.range_eq_bot_iff]
    refine AddMonoidHom.ext fun t ↦ ?_
    change torusQuotient N (t • (0 : Fin N → ℝ)) = 0
    rw [smul_zero, map_zero]
  refine SetLike.coe_injective ?_
  rw [torusFlowClosure, hrange, AddSubgroup.topologicalClosure_coe, AddSubgroup.coe_bot,
    closure_singleton]

/-- Paper: Theorem B.5.2.1(2), p. 627.
The torus flow takes values in its orbit closure when used in time averages. -/
def torusFlowInClosure (τ : Fin N → ℝ) (t : ℝ) : torusFlowClosure τ :=
  ⟨torusFlow τ t, AddSubgroup.le_topologicalClosure (torusFlow τ).toAddMonoidHom.range
    ⟨t, rfl⟩⟩

/-- In the ambient torus the restricted flow at time one gives the original phases. -/
theorem coe_torusFlowInClosure_one (τ : Fin N → ℝ) :
    (torusFlowInClosure τ 1 : UnitAddTorus (Fin N)) = torusQuotient N τ :=
  torusFlow_one τ

/-- Paper: §B.5.2.1, p. 627.
The fundamental domain for the torus quotient is the product of the half-open unit intervals. -/
def unitHalfOpenCube (N : ℕ) : Set (Fin N → ℝ) :=
  {x | ∀ i, x i ∈ Ico (0 : ℝ) 1}

/-- The one-dimensional cube includes the lower endpoint and excludes the upper endpoint. -/
theorem mem_unitHalfOpenCube_one (x : Fin 1 → ℝ) :
    x ∈ unitHalfOpenCube 1 ↔ 0 ≤ x 0 ∧ x 0 < 1 :=
  Fin.forall_fin_one

/-- Paper: §B.5.2.1, p. 627.
The torus volume is the pushforward of Lebesgue measure on the half-open unit cube. -/
theorem map_volume_unitHalfOpenCube (N : ℕ) :
    (volume.restrict (unitHalfOpenCube N)).map (torusQuotient N) =
      (volume : Measure (UnitAddTorus (Fin N))) := by
  have hcube : unitHalfOpenCube N = Set.pi univ fun _ ↦ Ico (0 : ℝ) 1 := by
    ext x; simp [unitHalfOpenCube]
  have hf : (torusQuotient N : (Fin N → ℝ) → UnitAddTorus (Fin N)) =
      fun x i ↦ ((x i : ℝ) : UnitAddCircle) := rfl
  rw [hcube, volume_pi, Measure.restrict_pi_pi, hf]
  have hmk : MeasurePreserving ((↑) : ℝ → UnitAddCircle) (volume.restrict (Ico 0 1)) := by
    rw [Measure.restrict_congr_set Ico_ae_eq_Ioc]
    simpa using UnitAddCircle.measurePreserving_mk 0
  exact (measurePreserving_pi _ (fun _ ↦ volume) fun _ ↦ hmk).map_eq

/-- Paper: §B.5.2.1, p. 627.
Riemann integrability on a torus with Haar probability is expressed by boundedness and
continuity almost everywhere.
Deviation: Uses the Lebesgue criterion for Riemann integrability on the fundamental cube. -/
def TorusRiemannIntegrable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (u : X → ℂ) : Prop :=
  (∃ C : ℝ, ∀ x, ‖u x‖ ≤ C) ∧ ∀ᵐ x ∂μ, ContinuousAt u x

/-- The indicator of the identity on the unit circle is Riemann integrable. -/
theorem torusRiemannIntegrable_indicator_zero :
    TorusRiemannIntegrable (volume : Measure UnitAddCircle)
      (({0} : Set UnitAddCircle).indicator (fun _ ↦ (1 : ℂ))) := by
  refine ⟨⟨1, fun x ↦ ?_⟩, ?_⟩
  · by_cases hx : x ∈ ({0} : Set UnitAddCircle) <;> simp [hx]
  · have h0 : (volume : Measure UnitAddCircle) {0} = 0 := measure_singleton 0
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with x hx
    refine continuousAt_const.congr (f := fun _ ↦ (0 : ℂ)) ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact (indicator_of_notMem hy _).symm

/-- Paper: Theorem B.5.2.1(1), p. 627.
The closed orbit subgroup is topologically isomorphic to the torus of dimension the rational
rank of the frequencies. -/
theorem torusFlowClosure_equiv_torus [NeZero N] (τ : Fin N → ℝ) :
    Nonempty (torusFlowClosure τ ≃ₜ+
      UnitAddTorus (Fin (Module.finrank ℚ (Submodule.span ℚ (range τ))))) := by sorry

-- TODO(paper-gap): Theorem B.5.2.1(2) for arbitrary Riemann-integrable observables.
-- A function supported on a Haar-null orbit arc can pull back to a nonmeasurable time function.
-- TODO(paper-gap): The bound in (B.5.2.14) needs an absolute value around the frequency.

/-- Paper: Theorem B.5.2.1(2), p. 627. Symmetric time averages of a
Riemann-integrable observable converge to its Haar probability integral.
Deviation: Requires Lebesgue measurability up to null sets along the orbit for the time integral. -/
theorem kroneckerWeyl_riemannIntegrable_symmetric [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : torusFlowClosure τ → ℂ) (hu : TorusRiemannIntegrable μ u)
    (ht : AEStronglyMeasurable (fun t ↦ u (torusFlowInClosure τ t)) volume) :
    Tendsto (fun T : ℝ ↦ (2 * T)⁻¹ • ∫ t in -T..T, u (torusFlowInClosure τ t))
      atTop (𝓝 (∫ x, u x ∂μ)) := by sorry

/-- Paper: Theorem B.5.2.1(2), p. 627. Forward time averages of a
Riemann-integrable observable converge to its Haar probability integral.
Deviation: Requires Lebesgue measurability up to null sets on the forward orbit. -/
theorem kroneckerWeyl_riemannIntegrable_forward [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : torusFlowClosure τ → ℂ) (hu : TorusRiemannIntegrable μ u)
    (ht : AEStronglyMeasurable (fun t ↦ u (torusFlowInClosure τ t))
      (volume.restrict (Ici (0 : ℝ)))) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in 0..T, u (torusFlowInClosure τ t))
      atTop (𝓝 (∫ x, u x ∂μ)) := by sorry

section KroneckerWeyl

open Real UnitAddTorus

/-- On the orbit closure, an exponential monomial integrates against a Haar probability
measure to one when it is trivial along the flow, and to zero otherwise. -/
private theorem integral_mFourier_torusFlowClosure (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (n : Fin N → ℤ) :
    ∫ x, mFourier n (x : UnitAddTorus (Fin N)) ∂μ =
      if (∑ i, (n i : ℝ) * τ i) = 0 then 1 else 0 := by
  set c := ∑ i, (n i : ℝ) * τ i
  split_ifs with hc
  · have hone : ∀ x ∈ (torusFlowClosure τ : Set (UnitAddTorus (Fin N))), mFourier n x = 1 := by
      have hsub : range (torusFlow τ) ⊆ {x | mFourier n x = 1} := by
        rintro _ ⟨t, rfl⟩
        change mFourier n (torusFlow τ t) = 1
        rw [mFourier_torusFlow]
        simp [show (∑ i, (n i : ℝ) * τ i) = 0 from hc]
      have := closure_minimal hsub (isClosed_eq (mFourier n).continuous continuous_const)
      intro x hx
      rw [torusFlowClosure, AddSubgroup.topologicalClosure_coe] at hx
      exact this (by simpa using hx)
    simp [fun x : torusFlowClosure τ ↦ hone x x.2]
  · let h₀ : torusFlowClosure τ := torusFlowInClosure τ (1 / (2 * c))
    have hw : mFourier n (h₀ : UnitAddTorus (Fin N)) = -1 := by
      change mFourier n (torusFlow τ (1 / (2 * c))) = -1
      rw [mFourier_torusFlow, show 2 * (π : ℂ) * Complex.I * (c : ℂ) * ((1 / (2 * c) : ℝ) : ℂ) =
        π * Complex.I by
          push_cast; field_simp [hc]]
      exact Complex.exp_pi_mul_I
    have h1 := integral_add_right_eq_self (μ := μ)
      (fun x : torusFlowClosure τ ↦ mFourier n (x : UnitAddTorus (Fin N))) h₀
    simp only [AddSubgroup.coe_add, mFourier_add_apply, hw, integral_mul_const] at h1
    linear_combination (-1 / 2 : ℂ) * h1

/-- Uniformly bounded linear time averages on the torus that converge to the orbit-closure
integral on every exponential monomial converge to it on every continuous function. -/
private theorem tendsto_of_mFourier (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [IsProbabilityMeasure μ]
    (A : ℝ → C(UnitAddTorus (Fin N), ℂ) → ℂ)
    (hadd : ∀ T φ ψ, A T (φ + ψ) = A T φ + A T ψ) (hsmul : ∀ T (a : ℂ) φ, A T (a • φ) = a * A T φ)
    (hnorm : ∀ T φ, ‖A T φ‖ ≤ ‖φ‖)
    (hF : ∀ n, Tendsto (fun T ↦ A T (mFourier n)) atTop
      (𝓝 (∫ x, mFourier n (x : UnitAddTorus (Fin N)) ∂μ)))
    (φ : C(UnitAddTorus (Fin N), ℂ)) :
    Tendsto (fun T ↦ A T φ) atTop (𝓝 (∫ x, φ (x : UnitAddTorus (Fin N)) ∂μ)) := by
  have : CompactSpace (torusFlowClosure τ) := isCompact_iff_compactSpace.mp
    (AddSubgroup.isClosed_topologicalClosure _).isCompact
  have hInt (φ : C(UnitAddTorus (Fin N), ℂ)) :
      Integrable (fun x : torusFlowClosure τ ↦ φ (x : UnitAddTorus (Fin N))) μ :=
    integrableOn_univ.mp
      ((φ.continuous.comp continuous_subtype_val).continuousOn.integrableOn_compact isCompact_univ)
  have hsub (T : ℝ) (φ ψ : C(UnitAddTorus (Fin N), ℂ)) : A T φ - A T ψ = A T (φ - ψ) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, hadd, ← neg_one_smul ℂ ψ, hsmul]
    ring
  have hLip (T : ℝ) : LipschitzWith 1 (A T) := LipschitzWith.of_dist_le_mul fun φ ψ ↦ by
    rw [dist_eq_norm, dist_eq_norm, hsub, NNReal.coe_one, one_mul]
    exact hnorm T _
  have hIcont : Continuous fun φ : C(UnitAddTorus (Fin N), ℂ) ↦
      ∫ x, φ (x : UnitAddTorus (Fin N)) ∂μ := by
    refine (LipschitzWith.of_dist_le_mul fun φ ψ ↦ ?_ : LipschitzWith 1 _).continuous
    rw [dist_eq_norm, dist_eq_norm, ← integral_sub (hInt φ) (hInt ψ), NNReal.coe_one, one_mul]
    calc ‖∫ x, (φ (x : UnitAddTorus (Fin N)) - ψ x) ∂μ‖ ≤ ‖φ - ψ‖ * (μ univ).toReal :=
          norm_integral_le_of_norm_le_const (Eventually.of_forall fun x ↦
            (φ - ψ).norm_coe_le_norm (x : UnitAddTorus (Fin N)))
      _ = ‖φ - ψ‖ := by simp
  let V : Set C(UnitAddTorus (Fin N), ℂ) :=
    {φ | Tendsto (fun T ↦ A T φ) atTop (𝓝 (∫ x, φ (x : UnitAddTorus (Fin N)) ∂μ))}
  have hVclosed : IsClosed V :=
    ((LipschitzWith.uniformEquicontinuous A 1 hLip).equicontinuous).isClosed_setOfPred_tendsto
      hIcont
  have hzero (T : ℝ) : A T 0 = 0 := by simpa using hsmul T 0 0
  have hspan : ((Submodule.span ℂ (range (mFourier (d := Fin N))) :
      Set C(UnitAddTorus (Fin N), ℂ))) ⊆ V := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => obtain ⟨n, rfl⟩ := hx; exact hF n
    | zero => simp [V, hzero]
    | add φ ψ _ _ hφ hψ =>
      change Tendsto _ _ _
      simp only [hadd, ContinuousMap.add_apply, integral_add (hInt φ) (hInt ψ)]
      exact hφ.add hψ
    | smul a φ _ hφ =>
      change Tendsto _ _ _
      simp only [hsmul, ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]
      exact hφ.const_mul a
  have hmem : φ ∈ (Submodule.span ℂ (range (mFourier (d := Fin N)))).topologicalClosure := by
    rw [span_mFourier_closure_eq_top]; trivial
  exact closure_minimal hspan hVclosed hmem

/-- The symmetric time averages of a nonconstant imaginary exponential tend to zero. -/
private theorem tendsto_symmAverage_exp {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun T : ℝ ↦ (2 * T : ℂ)⁻¹ * ∫ t in -T..T, Complex.exp (2 * π * Complex.I * c * t))
      atTop (𝓝 0) := by
  have ha : (2 * π * Complex.I * c : ℂ) ≠ 0 := by
    simp [hc, Real.pi_ne_zero, Complex.I_ne_zero]
  have hb (T : ℝ) : ‖Complex.exp (2 * π * Complex.I * c * T)‖ = 1 := by
    rw [show (2 * π * Complex.I * c * T : ℂ) = ((2 * π * c * T : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  have hint (T : ℝ) : ‖∫ t in -T..T, Complex.exp (2 * π * Complex.I * c * t)‖ ≤
      2 / ‖(2 * π * Complex.I * c : ℂ)‖ := by
    rw [integral_exp_mul_complex ha, norm_div]
    gcongr
    calc _ ≤ ‖Complex.exp (2 * π * Complex.I * c * T)‖ +
          ‖Complex.exp (2 * π * Complex.I * c * ((-T : ℝ) : ℂ))‖ := norm_sub_le _ _
      _ = 2 := by rw [hb, hb]; norm_num
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (by simpa using (tendsto_inv_atTop_zero.const_mul (1 / ‖(2 * π * Complex.I * c : ℂ)‖)))
  refine (eventually_gt_atTop 0).mono fun T hT ↦ ?_
  rw [norm_mul, norm_inv, show (2 * T : ℂ) = ((2 * T : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  calc (2 * T)⁻¹ * ‖∫ t in -T..T, Complex.exp (2 * π * Complex.I * c * t)‖
      ≤ (2 * T)⁻¹ * (2 / ‖(2 * π * Complex.I * c : ℂ)‖) := by gcongr; exact hint T
    _ = |c|⁻¹ * (π⁻¹ * 2⁻¹) * T⁻¹ := by
      have hna : ‖(2 * π * Complex.I * c : ℂ)‖ = 2 * π * |c| := by
        simp [abs_of_pos Real.pi_pos]
      rw [hna]
      field_simp

end KroneckerWeyl

/-- Paper: Theorem B.5.2.1(2), p. 627.
Symmetric time averages of a continuous observable converge to its Haar probability integral.
Deviation: This is the continuous case singled out in the paper. -/
theorem kroneckerWeyl_continuous_symmetric [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : C(torusFlowClosure τ, ℂ)) :
    Tendsto (fun T : ℝ ↦ (2 * T)⁻¹ • ∫ t in -T..T, u (torusFlowInClosure τ t))
      atTop (𝓝 (∫ x, u x ∂μ)) := by
  classical
  have hce : Topology.IsClosedEmbedding ((↑) : torusFlowClosure τ → UnitAddTorus (Fin N)) :=
    (AddSubgroup.isClosed_topologicalClosure _).isClosedEmbedding_subtypeVal
  obtain ⟨φ, hφ⟩ := u.exists_extension' hce
  have hu (x : torusFlowClosure τ) : u x = φ x := (congrFun hφ x).symm
  have hII (φ : C(UnitAddTorus (Fin N), ℂ)) (a b : ℝ) :
      IntervalIntegrable (fun t ↦ φ (torusFlow τ t)) volume a b :=
    (φ.continuous.comp (torusFlow τ).continuous).intervalIntegrable _ _
  let A : ℝ → C(UnitAddTorus (Fin N), ℂ) → ℂ :=
    fun T φ ↦ (2 * T : ℂ)⁻¹ * ∫ t in -T..T, φ (torusFlow τ t)
  have key := tendsto_of_mFourier τ μ A
    (fun T φ ψ ↦ by
      simp only [A, ContinuousMap.add_apply, intervalIntegral.integral_add (hII φ (-T) T)
        (hII ψ (-T) T), mul_add])
    (fun T a φ ↦ by
      simp only [A, ContinuousMap.smul_apply, smul_eq_mul, intervalIntegral.integral_const_mul]
      ring)
    (fun T φ ↦ by
      rcases eq_or_ne T 0 with rfl | hT
      · simp [A]
      simp only [A]
      rw [show (2 * T : ℂ) = ((2 * T : ℝ) : ℂ) by push_cast; ring, norm_mul, norm_inv,
        Complex.norm_real, Real.norm_eq_abs]
      calc |2 * T|⁻¹ * ‖∫ t in -T..T, φ (torusFlow τ t)‖ ≤ |2 * T|⁻¹ * (‖φ‖ * |T - -T|) := by
            gcongr
            exact intervalIntegral.norm_integral_le_of_norm_le_const fun t _ ↦
              φ.norm_coe_le_norm _
        _ = ‖φ‖ := by
          rw [show T - -T = 2 * T by ring]
          field_simp [abs_ne_zero.mpr (mul_ne_zero two_ne_zero hT)])
    (fun n ↦ by
      rw [integral_mFourier_torusFlowClosure]
      split_ifs with hc
      · refine tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun T hT ↦ ?_)
        have hT' : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT
        simp [A, mFourier_torusFlow, hc]
        field_simp
        ring
      · simp only [A, mFourier_torusFlow]
        exact tendsto_symmAverage_exp hc) φ
  simp only [hu]
  convert key using 2 with T
  simp only [A, Complex.real_smul]
  push_cast
  rfl

/-- Paper: Theorem B.5.2.1(2), p. 627.
Forward time averages of a continuous observable converge to its Haar probability integral.
Deviation: This is the continuous case singled out in the paper. -/
theorem kroneckerWeyl_continuous_forward [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : C(torusFlowClosure τ, ℂ)) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in 0..T, u (torusFlowInClosure τ t))
      atTop (𝓝 (∫ x, u x ∂μ)) := by
  classical
  have hce : Topology.IsClosedEmbedding ((↑) : torusFlowClosure τ → UnitAddTorus (Fin N)) :=
    (AddSubgroup.isClosed_topologicalClosure _).isClosedEmbedding_subtypeVal
  obtain ⟨φ, hφ⟩ := u.exists_extension' hce
  have hu (x : torusFlowClosure τ) : u x = φ x := (congrFun hφ x).symm
  have hII (φ : C(UnitAddTorus (Fin N), ℂ)) (a b : ℝ) :
      IntervalIntegrable (fun t ↦ φ (torusFlow τ t)) volume a b :=
    (φ.continuous.comp (torusFlow τ).continuous).intervalIntegrable _ _
  let A : ℝ → C(UnitAddTorus (Fin N), ℂ) → ℂ :=
    fun T φ ↦ (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, φ (torusFlow τ t)
  have key := tendsto_of_mFourier τ μ A
    (fun T φ ψ ↦ by
      simp only [A, ContinuousMap.add_apply, intervalIntegral.integral_add (hII φ 0 T)
        (hII ψ 0 T), mul_add])
    (fun T a φ ↦ by
      simp only [A, ContinuousMap.smul_apply, smul_eq_mul, intervalIntegral.integral_const_mul]
      ring)
    (fun T φ ↦ by
      rcases eq_or_ne T 0 with rfl | hT
      · simp [A]
      simp only [A, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
      calc |T|⁻¹ * ‖∫ t in (0 : ℝ)..T, φ (torusFlow τ t)‖ ≤ |T|⁻¹ * (‖φ‖ * |T - 0|) := by
            gcongr
            exact intervalIntegral.norm_integral_le_of_norm_le_const fun t _ ↦
              φ.norm_coe_le_norm _
        _ = ‖φ‖ := by rw [sub_zero]; field_simp [abs_ne_zero.mpr hT])
    (fun n ↦ by
      rw [integral_mFourier_torusFlowClosure]
      split_ifs with hc
      · refine tendsto_const_nhds.congr' ((eventually_ne_atTop 0).mono fun T hT ↦ ?_)
        simp [A, mFourier_torusFlow, hc, hT]
      · simp only [A, mFourier_torusFlow]
        exact tendsto_average_exp hc) φ
  simp only [hu]
  convert key using 2 with T
  simp only [A, Complex.real_smul, Complex.ofReal_inv]
  rfl

/-- Paper: Lemma B.5.2.2, p. 627.
The indicator of an open set with null boundary can be sandwiched between continuous
functions into the unit interval whose integrated difference is arbitrarily small. -/
theorem exists_continuous_sandwich_indicator {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.Regular]
    {U : Set X} (hU : IsOpen U) (hfront : μ (frontier U) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ lower upper : C(X, Icc (0 : ℝ) 1),
      (∀ x, (lower x : ℝ) ≤ U.indicator (fun _ ↦ (1 : ℝ)) x ∧
        U.indicator (fun _ ↦ (1 : ℝ)) x ≤ (upper x : ℝ)) ∧
      (∫ x, ((upper x : ℝ) - (lower x : ℝ)) ∂μ) < ε := by
  have : IsFiniteMeasure μ := ⟨isCompact_univ.measure_lt_top⟩
  have hδ : ENNReal.ofReal (ε / 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
  -- A compact set inside `U` and an open set around its closure, both of nearly the same mass.
  obtain ⟨K, hKU, hK, hKμ⟩ := hU.measurableSet.exists_isCompact_lt_add (measure_ne_top μ U) hδ
  obtain ⟨V, hV, hVo, hVμ⟩ := (closure U).exists_isOpen_lt_add (measure_ne_top μ _) hδ
  have hcl : μ (closure U) ≤ μ U := by
    rw [closure_eq_self_union_frontier]
    exact (measure_union_le _ _).trans (by rw [hfront, add_zero])
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed hU.isClosed_compl
    hK.isClosed (disjoint_compl_left_iff_subset.mpr hKU)
  obtain ⟨g, hg0, hg1, hg01⟩ := exists_continuous_zero_one_of_isClosed hVo.isClosed_compl
    isClosed_closure (disjoint_compl_left_iff_subset.mpr hV)
  refine ⟨⟨fun x ↦ ⟨f x, hf01 x⟩, f.continuous.subtype_mk _⟩,
    ⟨fun x ↦ ⟨g x, hg01 x⟩, g.continuous.subtype_mk _⟩, fun x ↦ ?_, ?_⟩
  · change f x ≤ U.indicator (fun _ ↦ (1 : ℝ)) x ∧ U.indicator (fun _ ↦ (1 : ℝ)) x ≤ g x
    by_cases hx : x ∈ U
    · have hgx : g x = 1 := hg1 (subset_closure hx)
      rw [indicator_of_mem hx, hgx]
      exact ⟨(hf01 x).2, le_rfl⟩
    · have hfx : f x = 0 := hf0 hx
      rw [indicator_of_notMem hx, hfx]
      exact ⟨le_rfl, (hg01 x).1⟩
  · change (∫ x, (g x - f x) ∂μ) < ε
    have hKV : K ⊆ V := hKU.trans (subset_closure.trans hV)
    have hmeas : MeasurableSet (V \ K) := hVo.measurableSet.diff hK.measurableSet
    have hpt (x : X) : g x - f x ≤ (V \ K).indicator (fun _ ↦ (1 : ℝ)) x := by
      by_cases hxK : x ∈ K
      · have hfx : f x = 1 := hf1 hxK
        rw [indicator_of_notMem (show x ∉ V \ K from fun h ↦ h.2 hxK), hfx]
        linarith [(hg01 x).2]
      · by_cases hxV : x ∈ V
        · rw [indicator_of_mem (show x ∈ V \ K from ⟨hxV, hxK⟩)]
          linarith [(hg01 x).2, (hf01 x).1]
        · have hgx : g x = 0 := hg0 hxV
          have hfx : f x = 0 := hf0 fun h ↦ hxV (hV (subset_closure h))
          rw [indicator_of_notMem (show x ∉ V \ K from fun h ↦ hxV h.1), hgx, hfx, sub_zero]
    have hint : Integrable (fun x ↦ g x - f x) μ :=
      (g.continuous.sub f.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hmass : μ (V \ K) < ENNReal.ofReal ε := by
      rw [measure_sdiff hKV hK.measurableSet.nullMeasurableSet (measure_ne_top μ K)]
      refine ENNReal.sub_lt_of_lt_add (measure_mono hKV) ?_
      calc μ V < μ (closure U) + ENNReal.ofReal (ε / 2) := hVμ
        _ ≤ μ K + ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
          add_le_add (hcl.trans hKμ.le) le_rfl
        _ = ENNReal.ofReal ε + μ K := by
          rw [add_assoc, ← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le, add_halves,
            add_comm]
    calc ∫ x, (g x - f x) ∂μ ≤ ∫ x, (V \ K).indicator (fun _ ↦ (1 : ℝ)) x ∂μ :=
          integral_mono hint ((integrable_const 1).indicator hmeas) hpt
      _ = μ.real (V \ K) := by rw [integral_indicator_const _ hmeas, smul_eq_mul, mul_one]
      _ < ε := ENNReal.toReal_lt_of_lt_ofReal hmass

-- TODO(paper-gap): Neither inclusion in the asserted frontier identity holds in general.
-- Away from the coordinate seams the cube projection is a local homeomorphism, so the
-- torus frontier lies in the image of the relative frontier together with the null seams.

/-- Inside the window, a preimage of the image frontier lies on either the relative frontier or the window boundary. -/
private theorem preimage_frontier_image_inter_subset {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {q : X → Y} (hq : IsOpenMap q)
    (hcont : Continuous q) {C D : Set X} (hinj : InjOn q C) (hDC : interior D ⊆ C)
    (U : Set C) :
    q ⁻¹' frontier (q '' (Subtype.val '' U)) ∩ D ⊆ Subtype.val '' frontier U ∪ frontier D := by
  let S : Set X := Subtype.val '' U
  have hSC : S ⊆ C := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hlocal : (q ⁻¹' (q '' S)) ∩ interior D = S ∩ interior D := calc
    _ = ((q ⁻¹' (q '' S)) ∩ C) ∩ interior D := by
      rw [inter_assoc, inter_eq_self_of_subset_right hDC]
    _ = _ := congrArg (· ∩ interior D) (hinj.preimage_image_inter hSC)
  have hfront : frontier (q ⁻¹' (q '' S)) ∩ interior D = frontier S ∩ interior D := by
    rw [← frontier_inter_open_inter (s := q ⁻¹' (q '' S)) isOpen_interior,
      hlocal, frontier_inter_open_inter isOpen_interior]
  intro x hx
  by_cases hi : x ∈ interior D
  · left
    have hxS : x ∈ frontier S ∩ interior D := by
      rw [← hfront, ← hq.preimage_frontier_eq_frontier_preimage hcont]
      exact ⟨hx.1, hi⟩
    rw [frontier_eq_closure_inter_closure] at hxS
    refine ⟨⟨x, hDC hi⟩, ?_, rfl⟩
    rw [frontier_eq_closure_inter_closure]
    constructor
    · rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
      exact hxS.1.1
    · rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
      refine closure_mono ?_ (isOpen_interior.closure_inter ⟨hxS.1.2, hi⟩)
      intro y hy
      refine ⟨⟨y, hDC hy.2⟩, ?_, rfl⟩
      intro hyU
      exact hy.1 ⟨_, hyU, rfl⟩
  · exact Or.inr ⟨subset_closure hx.2, hi⟩

/-- Torus volume is measured on the preimage in a product of right-closed fundamental intervals. -/
private theorem volume_torusQuotient_preimage_Ioc (a : Fin N → ℝ)
    (V : Set (UnitAddTorus (Fin N))) (hV : MeasurableSet V) :
    volume V = volume ((torusQuotient N ⁻¹' V) ∩ univ.pi (fun i ↦ Ioc (a i) (a i + 1))) := by
  let I : Fin N → Set ℝ := fun i ↦ Ioc (a i) (a i + 1)
  have hmp : MeasurePreserving (torusQuotient N) (Measure.pi fun i ↦ volume.restrict (I i))
      (volume : Measure (UnitAddTorus (Fin N))) :=
    measurePreserving_pi (fun i : Fin N ↦ (volume : Measure ℝ).restrict (I i))
      (fun _ : Fin N ↦ (volume : Measure UnitAddCircle))
      (f := fun _ ↦ ((↑) : ℝ → UnitAddCircle))
      (fun i ↦ AddCircle.measurePreserving_mk 1 (a i))
  have hmap : (volume.restrict (univ.pi I)).map (torusQuotient N) = volume := by
    rw [show (volume : Measure (Fin N → ℝ)) = Measure.pi (fun _ ↦ volume) from rfl,
      Measure.restrict_pi_pi]
    exact hmp.map_eq
  rw [← hmap, Measure.map_apply hmp.measurable hV, Measure.restrict_apply (hV.preimage hmp.measurable)]

/-- Paper: Remark B.5.2.3(1), p. 628.
A subset of the half-open cube with a null relative frontier has a torus image with null
frontier. The restricted Lebesgue measure identifies relative null sets via their images
in the ambient real vector space. -/
theorem volume_frontier_torusQuotient_image [NeZero N] (U : Set (unitHalfOpenCube N))
    (hU : volume (Subtype.val '' frontier U) = 0) :
    volume (frontier (torusQuotient N '' (Subtype.val '' U))) = 0 := by
  let q : (Fin N → ℝ) → UnitAddTorus (Fin N) := torusQuotient N
  have hqcont : Continuous q := (torusQuotient N).continuous
  let C := unitHalfOpenCube N
  let D : Set (Fin N → ℝ) := univ.pi fun _ ↦ Icc (0 : ℝ) 1
  have hq : IsOpenMap q := by
    change IsOpenMap (Pi.map (fun _ : Fin N ↦ ((↑) : ℝ → AddCircle (1 : ℝ))))
    exact (IsOpenQuotientMap.piMap fun _ : Fin N ↦
      QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples (1 : ℝ))).isOpenMap
  have hinj : InjOn q C := by
    intro x hx y hy hxy
    funext i
    exact AddCircle.injOn_coe_Ico (p := (1 : ℝ)) 0
      (by simpa only [zero_add] using hx i) (by simpa only [zero_add] using hy i)
      (congrFun hxy i)
  have hDC : interior D ⊆ C := by
    rw [show interior D = univ.pi (fun _ : Fin N ↦ Ioo (0 : ℝ) 1) by
      simp only [D, interior_pi_set finite_univ, interior_Icc]]
    intro x hx i
    exact ⟨(hx i (mem_univ i)).1.le, (hx i (mem_univ i)).2⟩
  have hD : volume (frontier D) = 0 :=
    Convex.addHaar_frontier volume (convex_pi (fun _ _ ↦ convex_Icc _ _) : Convex ℝ D)
  let a : Fin N → ℝ := 0
  let B : Set (Fin N → ℝ) := univ.pi fun i ↦ Ioc (a i) (a i + 1)
  have hBD : B ⊆ D := by
    intro x hx i _
    have hi : x i ∈ Ioc (0 : ℝ) 1 := by simpa [a] using hx i (mem_univ i)
    exact ⟨hi.1.le, hi.2⟩
  rw [volume_torusQuotient_preimage_Ioc a _ isClosed_frontier.measurableSet]
  refine measure_mono_null ?_ (measure_union_null hU hD)
  intro x hx
  exact preimage_frontier_image_inter_subset hq hqcont hinj hDC U ⟨hx.1, hBD hx.2⟩

/-- Paper: Remark B.5.2.3(2), p. 628.
For a Jordan-measurable subset of the cube, its torus image and the interior of that
image have the same volume. Jordan measurability is expressed by the null relative frontier. -/
theorem volume_interior_torusQuotient_image [NeZero N] (U : Set (unitHalfOpenCube N))
    (hU : volume (Subtype.val '' frontier U) = 0) :
    volume (interior (torusQuotient N '' (Subtype.val '' U))) =
      volume (torusQuotient N '' (Subtype.val '' U)) :=
  measure_interior_of_null_frontier (volume_frontier_torusQuotient_image U hU)

/-- Paper: Remark B.5.2.3(2), p. 628.
The interior of the torus image of a Jordan-measurable set has null frontier. -/
theorem volume_frontier_interior_torusQuotient_image [NeZero N] (U : Set (unitHalfOpenCube N))
    (hU : volume (Subtype.val '' frontier U) = 0) :
    volume (frontier (interior (torusQuotient N '' (Subtype.val '' U)))) = 0 :=
  measure_mono_null frontier_interior_subset (volume_frontier_torusQuotient_image U hU)

/-- Paper: Corollary B.5.2.4, p. 631.
For a relatively open subset of the unit cube, the symmetric frequency of visits converges
to Haar probability on the orbit closure when the target has null relative frontier. -/
theorem torusHittingTimes_tendsto_symmetric [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (U : Set (unitHalfOpenCube N)) (hU : IsOpen U) :
    let V : Set (torusFlowClosure τ) := Subtype.val ⁻¹' (torusQuotient N '' (Subtype.val '' U))
    μ (frontier V) = 0 →
      Tendsto (fun T : ℝ ↦
        volume.real (torusHittingTimes (fun t ↦ t • τ) (Icc (-T) T) (Subtype.val '' U)) /
          (2 * T)) atTop (𝓝 (μ.real V)) := by
  intro V hfront
  let q : (Fin N → ℝ) → UnitAddTorus (Fin N) := torusQuotient N
  have hq : Continuous q := (torusQuotient N).continuous
  have hV : MeasurableSet V := by
    have hC : MeasurableSet (unitHalfOpenCube N) :=
      MeasurableSet.univ_pi' fun _ ↦ measurableSet_Ico
    have hinj : InjOn q (unitHalfOpenCube N) := by
      intro x hx y hy hxy
      funext i
      exact AddCircle.injOn_coe_Ico (p := (1 : ℝ)) 0
        (by simpa only [zero_add] using hx i) (by simpa only [zero_add] using hy i)
        (congrFun hxy i)
    have hCU : MeasurableSet (Subtype.val '' U) :=
      (MeasurableEmbedding.subtype_coe hC).measurableSet_image.2 hU.measurableSet
    exact (hCU.image_of_measurable_injOn hq.measurable
      (hinj.mono (Subtype.coe_image_subset _ _))).preimage measurable_subtype_coe
  let F : ℝ → torusFlowClosure τ := torusFlowInClosure τ
  have hF : Continuous F := (torusFlow τ).continuous.subtype_mk _
  let u : torusFlowClosure τ → ℂ := V.indicator (fun _ ↦ 1)
  have hu : TorusRiemannIntegrable μ u := by
    refine ⟨⟨1, fun x ↦ ?_⟩, ?_⟩
    · by_cases hx : x ∈ V <;> simp [u, hx]
    · have hn : ∀ᵐ x ∂μ, x ∉ frontier V := by
        simpa only [ae_iff, not_not, setOf_mem_eq] using hfront
      filter_upwards [hn] with x hx
      exact continuousOn_const.continuousAt_indicator hx
  have hlim : Tendsto (fun T : ℝ ↦ (2 * T)⁻¹ • ∫ t in -T..T, u (F t))
      atTop (𝓝 (∫ x, u x ∂μ)) :=
    kroneckerWeyl_riemannIntegrable_symmetric τ μ u hu
      ((measurable_const.indicator hV).comp hF.measurable).aestronglyMeasurable
  have hmean : (∫ x, u x ∂μ) = (μ.real V : ℂ) := by
    change (∫ x, V.indicator (fun _ ↦ (1 : ℂ)) x ∂μ) = _
    rw [integral_indicator_const _ hV, Complex.real_smul, mul_one]
  rw [hmean] at hlim
  have hlimRe : Tendsto (fun T : ℝ ↦ ((2 * T)⁻¹ • ∫ t in -T..T, u (F t)).re)
      atTop (𝓝 (μ.real V)) := by
    simpa only [Function.comp_def, Complex.ofReal_re] using
      (Complex.continuous_re.continuousAt (x := (μ.real V : ℂ))).tendsto.comp hlim
  let W : Set ℝ := F ⁻¹' V
  have hW : MeasurableSet W := hV.preimage hF.measurable
  have hIndicator : (fun t ↦ u (F t)) = W.indicator (fun _ ↦ (1 : ℂ)) :=
    funext fun t ↦ (Set.indicator_comp_right F (s := V) (g := fun _ ↦ (1 : ℂ)) (x := t)).symm
  refine hlimRe.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  have hHits : torusHittingTimes (fun t ↦ t • τ) (Icc (-T) T) (Subtype.val '' U) =
      W ∩ Icc (-T) T := inter_comm _ _
  rw [intervalIntegral.integral_of_le ((neg_nonpos.mpr hT).trans hT), ← integral_Icc_eq_integral_Ioc,
    hIndicator, integral_indicator_const _ hW, measureReal_restrict_apply hW, ← hHits]
  rw [Complex.real_smul, Complex.real_smul, mul_one, ← Complex.ofReal_mul, Complex.ofReal_re,
    div_eq_mul_inv, mul_comm]

/-- Paper: Corollary B.5.2.4, p. 631.
For a relatively open subset of the unit cube, the forward frequency of visits converges
to Haar probability on the orbit closure when the target has null relative frontier. -/
theorem torusHittingTimes_tendsto_forward [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (U : Set (unitHalfOpenCube N)) (hU : IsOpen U) :
    let V : Set (torusFlowClosure τ) := Subtype.val ⁻¹' (torusQuotient N '' (Subtype.val '' U))
    μ (frontier V) = 0 →
      Tendsto (fun T : ℝ ↦
        volume.real (torusHittingTimes (fun t ↦ t • τ) (Icc 0 T) (Subtype.val '' U)) /
          T) atTop (𝓝 (μ.real V)) := by
  intro V hfront
  let q : (Fin N → ℝ) → UnitAddTorus (Fin N) := torusQuotient N
  have hq : Continuous q := (torusQuotient N).continuous
  have hV : MeasurableSet V := by
    have hC : MeasurableSet (unitHalfOpenCube N) :=
      MeasurableSet.univ_pi' fun _ ↦ measurableSet_Ico
    have hinj : InjOn q (unitHalfOpenCube N) := by
      intro x hx y hy hxy
      funext i
      exact AddCircle.injOn_coe_Ico (p := (1 : ℝ)) 0
        (by simpa only [zero_add] using hx i) (by simpa only [zero_add] using hy i)
        (congrFun hxy i)
    have hCU : MeasurableSet (Subtype.val '' U) :=
      (MeasurableEmbedding.subtype_coe hC).measurableSet_image.2 hU.measurableSet
    exact (hCU.image_of_measurable_injOn hq.measurable
      (hinj.mono (Subtype.coe_image_subset _ _))).preimage measurable_subtype_coe
  let F : ℝ → torusFlowClosure τ := torusFlowInClosure τ
  have hF : Continuous F := (torusFlow τ).continuous.subtype_mk _
  let u : torusFlowClosure τ → ℂ := V.indicator (fun _ ↦ 1)
  have hu : TorusRiemannIntegrable μ u := by
    refine ⟨⟨1, fun x ↦ ?_⟩, ?_⟩
    · by_cases hx : x ∈ V <;> simp [u, hx]
    · have hn : ∀ᵐ x ∂μ, x ∉ frontier V := by
        simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hfront
      filter_upwards [hn] with x hx
      exact continuousOn_const.continuousAt_indicator hx
  have hlim : Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in 0..T, u (F t))
      atTop (𝓝 (∫ x, u x ∂μ)) :=
    kroneckerWeyl_riemannIntegrable_forward τ μ u hu
      ((measurable_const.indicator hV).comp hF.measurable).aestronglyMeasurable
  have hmean : (∫ x, u x ∂μ) = (μ.real V : ℂ) := by
    change (∫ x, V.indicator (fun _ ↦ (1 : ℂ)) x ∂μ) = _
    rw [integral_indicator_const _ hV, Complex.real_smul, mul_one]
  rw [hmean] at hlim
  have hlimRe : Tendsto (fun T : ℝ ↦ (T⁻¹ • ∫ t in 0..T, u (F t)).re)
      atTop (𝓝 (μ.real V)) := by
    simpa only [Function.comp_def, Complex.ofReal_re] using
      (Complex.continuous_re.continuousAt (x := (μ.real V : ℂ))).tendsto.comp hlim
  let W : Set ℝ := F ⁻¹' V
  have hW : MeasurableSet W := hV.preimage hF.measurable
  have hIndicator : (fun t ↦ u (F t)) = W.indicator (fun _ ↦ (1 : ℂ)) :=
    funext fun t ↦ (Set.indicator_comp_right F (s := V) (g := fun _ ↦ (1 : ℂ)) (x := t)).symm
  refine hlimRe.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  have hHits : torusHittingTimes (fun t ↦ t • τ) (Icc 0 T) (Subtype.val '' U) =
      W ∩ Icc 0 T := inter_comm _ _
  rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc,
    hIndicator, integral_indicator_const _ hW, measureReal_restrict_apply hW, ← hHits]
  rw [Complex.real_smul, Complex.real_smul, mul_one, ← Complex.ofReal_mul, Complex.ofReal_re,
    div_eq_mul_inv, mul_comm]

-- TODO(paper-gap): Remark B.5.2.5 does not state the discrete versions. The discrete orbit
-- closure can be disconnected, so the continuous-time dimension claim cannot be reused verbatim.

end Torus

section Recurrence

/-- Paper: Definition B.5.3.1(1), p. 632.
The upper density is the limsup of the fraction of a symmetric interval occupied by the set.
Deviation: For arbitrary subsets the numerator is Lebesgue outer measure. -/
def upperDensity (X : Set ℝ) : ℝ :=
  limsup (fun T : ℝ ↦ volume.real (Icc (-T) T ∩ X) / (2 * T)) atTop

/-- Every right half-line has symmetric upper density one half. -/
theorem upperDensity_Ici (a : ℝ) : upperDensity (Ici a) = 1 / 2 := by
  have hev : (fun T : ℝ ↦ 1 / 2 - a / 2 * T⁻¹) =ᶠ[atTop]
      fun T ↦ volume.real (Icc (-T) T ∩ Ici a) / (2 * T) := by
    filter_upwards [eventually_ge_atTop (max |a| 1)] with T hT
    have hT0 : T ≠ 0 := (zero_lt_one.trans_le ((le_max_right _ _).trans hT)).ne'
    have haT : |a| ≤ T := (le_max_left _ _).trans hT
    have hset : Icc (-T) T ∩ Ici a = Icc a T := by
      ext x
      simp only [mem_inter_iff, mem_Icc, mem_Ici]
      exact ⟨fun h ↦ ⟨h.2, h.1.2⟩,
        fun h ↦ ⟨⟨(neg_le.mp ((neg_le_abs a).trans haT)).trans h.1, h.2⟩, h.1⟩⟩
    rw [hset, Real.volume_real_Icc_of_le ((le_abs_self a).trans haT),
      eq_div_iff (mul_ne_zero two_ne_zero hT0)]
    have h : (1 / 2 - a / 2 * T⁻¹) * (2 * T) = T - a * (T⁻¹ * T) := by ring
    rw [h, inv_mul_cancel₀ hT0, mul_one]
  have hlim : Tendsto (fun T : ℝ ↦ 1 / 2 - a / 2 * T⁻¹) atTop (𝓝 (1 / 2)) := by
    have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub
      ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (a / 2))
    rwa [mul_zero, sub_zero] at h
  exact (hlim.congr' hev).limsup_eq

/-- Paper: Definition B.5.3.1(2), p. 632.
The vertical return times are the shifts whose uniform approximation error on the specified set
is less than the tolerance. -/
def verticalReturnTimes (f : ℂ → ℂ) (K : Set ℂ) (ε : ℝ) : Set ℝ :=
  {t | (⨆ z : K, (‖f ((z : ℂ) + (t : ℂ) * Complex.I) - f z‖₊ : ℝ≥0∞)) < ENNReal.ofReal ε}

/-- The return times of the identity on a singleton are the shifts of absolute value
less than the tolerance. -/
theorem verticalReturnTimes_id_singleton (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    verticalReturnTimes id {z} ε = Ioo (-ε) ε := by
  ext t
  have : Nonempty ({z} : Set ℂ) := ⟨⟨z, rfl⟩⟩
  have hconst (w : ({z} : Set ℂ)) :
      (‖id ((w : ℂ) + (t : ℂ) * Complex.I) - id (w : ℂ)‖₊ : ℝ≥0∞) =
        (‖(t : ℂ) * Complex.I‖₊ : ℝ≥0∞) := by
    simp only [id_eq, add_sub_cancel_left]
  change (⨆ w : ({z} : Set ℂ),
    (‖id ((w : ℂ) + (t : ℂ) * Complex.I) - id (w : ℂ)‖₊ : ℝ≥0∞)) < ENNReal.ofReal ε ↔ _
  rw [iSup_congr hconst, iSup_const, ← ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_lt_ofReal_iff hε, coe_nnNorm, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_lt, mem_Ioo]

/-- Paper: Definition B.5.3.1(2), p. 632.
Strong recurrence means positive upper density of vertical return times for every positive
tolerance.
Deviation: The domain is represented by a complex function with holomorphy on the strip
and compact containment imposed at use sites. The printed `C_{>R}` is read as `C_I`. -/
def StronglyRecurrentOn (f : ℂ → ℂ) (K : Set ℂ) : Prop :=
  ∀ ε > 0, 0 < upperDensity (verticalReturnTimes f K ε)

open Real in
/-- On compact sets, the complex exponential is strongly recurrent by its imaginary period. -/
theorem stronglyRecurrentOn_exp {K : Set ℂ} (hK : IsCompact K) :
    StronglyRecurrentOn Complex.exp K := by
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := (hK.image Complex.continuous_exp).isBounded.exists_norm_le
  set M := max M₀ 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  set δ := min 1 (ε / (2 * M)) with hδdef
  have hδ : 0 < δ := lt_min one_pos (div_pos hε (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδM : M * δ < ε := by
    calc M * δ ≤ M * (ε / (2 * M)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hM.le
      _ = ε / 2 := by field_simp
      _ < ε := half_lt_self hε
  let I (n : ℕ) : Set ℝ := Ioo (2 * π * n - δ) (2 * π * n + δ)
  have hsub (n : ℕ) : I n ⊆ verticalReturnTimes Complex.exp K ε := by
    intro t ht
    have hs : |t - 2 * π * n| < δ := abs_sub_lt_iff.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hz (z : K) : ‖Complex.exp ((z : ℂ) + (t : ℂ) * Complex.I) - Complex.exp z‖ ≤ M * δ := by
      have he : Complex.exp ((z : ℂ) + (t : ℂ) * Complex.I) =
          Complex.exp z * Complex.exp (Complex.I * ((t - 2 * π * n : ℝ) : ℂ)) := by
        have : (z : ℂ) + (t : ℂ) * Complex.I =
            ((z : ℂ) + Complex.I * ((t - 2 * π * n : ℝ) : ℂ)) + n * (2 * π * Complex.I) := by
          push_cast; ring
        rw [this, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one, Complex.exp_add]
      have hzM : ‖Complex.exp z‖ ≤ M := (hM₀ _ ⟨z, z.2, rfl⟩).trans (le_max_left _ _)
      have h1 : ‖Complex.exp (Complex.I * ((t - 2 * π * n : ℝ) : ℂ)) - 1‖ ≤ |t - 2 * π * n| := by
        simpa [Real.norm_eq_abs] using
          (norm_exp_I_mul_ofReal_sub_one_le (x := t - 2 * π * n))
      calc ‖Complex.exp ((z : ℂ) + (t : ℂ) * Complex.I) - Complex.exp z‖
          = ‖Complex.exp z‖ * ‖Complex.exp (Complex.I * ((t - 2 * π * n : ℝ) : ℂ)) - 1‖ := by
            rw [he, ← norm_mul, mul_sub, mul_one]
        _ ≤ M * |t - 2 * π * n| := mul_le_mul hzM h1 (norm_nonneg _) hM.le
        _ ≤ M * δ := mul_le_mul_of_nonneg_left hs.le hM.le
    show (⨆ z : K, (‖Complex.exp ((z : ℂ) + (t : ℂ) * Complex.I) - Complex.exp z‖₊ : ℝ≥0∞)) <
      ENNReal.ofReal ε
    calc (⨆ z : K, (‖Complex.exp ((z : ℂ) + (t : ℂ) * Complex.I) - Complex.exp z‖₊ : ℝ≥0∞))
        ≤ ENNReal.ofReal (M * δ) := iSup_le fun z ↦ by
          have h := ENNReal.ofReal_le_ofReal (hz z)
          rw [ofReal_norm] at h
          exact h
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr hδM
  set X := verticalReturnTimes Complex.exp K ε
  have hbound : IsBoundedUnder (· ≤ ·) atTop
      (fun T : ℝ ↦ volume.real (Icc (-T) T ∩ X) / (2 * T)) := by
    refine ⟨1, eventually_map.mpr ((eventually_gt_atTop (0 : ℝ)).mono fun T hT ↦ ?_)⟩
    show volume.real (Icc (-T) T ∩ X) / (2 * T) ≤ 1
    rw [div_le_one (by positivity : (0 : ℝ) < 2 * T)]
    calc volume.real (Icc (-T) T ∩ X) ≤ volume.real (Icc (-T) T) :=
          measureReal_mono inter_subset_left measure_Icc_lt_top.ne
      _ = 2 * T := by rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  have hπ : 0 < 2 * π := by positivity
  refine lt_of_lt_of_le (div_pos hδ hπ) (le_limsup_of_frequently_le ?_ hbound)
  refine frequently_atTop.mpr fun T₀ ↦ ⟨2 * π * ((⌈T₀⌉₊ + 1 : ℕ) : ℝ), ?_, ?_⟩
  · have h1 : T₀ ≤ ((⌈T₀⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil T₀]
    have h2 : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
    nlinarith
  · set N := ⌈T₀⌉₊ + 1
    have hN : (0 : ℝ) < N := by positivity
    have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.succ_pos _)
    have hdisj : PairwiseDisjoint (↑(Finset.range N)) I := by
      intro n _ m _ hnm
      refine Set.disjoint_left.mpr fun t htn htm ↦ ?_
      rcases lt_or_gt_of_ne hnm with h | h
      · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
        have := htn.2; have := htm.1; nlinarith [Real.pi_gt_three]
      · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
        have := htn.1; have := htm.2; nlinarith [Real.pi_gt_three]
    have hU : (⋃ n ∈ Finset.range N, I n) ⊆ Icc (-(2 * π * N)) (2 * π * N) ∩ X := by
      intro t ht
      simp only [Set.mem_iUnion, Finset.mem_range] at ht
      obtain ⟨n, hn, htn⟩ := ht
      refine ⟨⟨?_, ?_⟩, hsub n htn⟩
      · have := htn.1; have : (0 : ℝ) ≤ n := n.cast_nonneg; nlinarith [Real.pi_gt_three]
      · have := htn.2; have : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
        nlinarith [Real.pi_gt_three]
    have hvol : volume.real (⋃ n ∈ Finset.range N, I n) = N * (2 * δ) := by
      rw [measureReal_biUnion_finset hdisj (fun n _ ↦ measurableSet_Ioo)
        (fun n _ ↦ measure_Ioo_lt_top.ne)]
      rw [Finset.sum_congr rfl fun n _ ↦ show volume.real (I n) = _ from
        Real.volume_real_Ioo_of_le (by linarith : 2 * π * n - δ ≤ 2 * π * n + δ)]
      have hc (n : ℕ) : 2 * π * n + δ - (2 * π * n - δ) = 2 * δ := by ring
      simp only [hc, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [le_div_iff₀ (by positivity)]
    calc δ / (2 * π) * (2 * (2 * π * N)) = N * (2 * δ) := by field_simp
      _ = volume.real (⋃ n ∈ Finset.range N, I n) := hvol.symm
      _ ≤ volume.real (Icc (-(2 * π * N)) (2 * π * N) ∩ X) := measureReal_mono hU
          ((measure_mono inter_subset_left).trans_lt measure_Icc_lt_top).ne

-- TODO(paper-gap): Proposition B.5.3.2 forces T₀ = 0. Over ℚ with the trivial character
-- and a finite place above 2, the denominator at T₀ vanishes.

open IsDedekindDomain NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- Paper: Proposition B.5.3.3, p. 632.
The reciprocal partial Euler product multiplies the reciprocals of the finite Euler factors
from §3.2. At a zero of the local Euler polynomial this gives its holomorphic value zero. -/
def reciprocalPartialHeckeEulerProduct (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (s : ℂ) : ℂ :=
  ∏ v ∈ S, (finiteHeckeEulerFactor χ v s)⁻¹

/-- For a singleton unramified place the product is the linear factor with coefficient
given by the value of the character on a local uniformizer. -/
theorem reciprocalPartialHeckeEulerProduct_singleton
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F))
    (hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v) (s : ℂ) :
    reciprocalPartialHeckeEulerProduct χ {v} s =
      1 - (ideleClassNormTwist χ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-s) := by
  classical
  simp [reciprocalPartialHeckeEulerProduct, finiteHeckeEulerFactor, hv]

/-- Every initial phase vector admits a shift in `(0, 1)` at which the finite Euler
product has norm at least a common positive constant. -/
private theorem exists_eulerPhase_shift {ι : Type*} [Fintype ι] (a : ι → ℂ)
    (ω : ι → ℝ) (hω : ∀ i, ω i ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ι → Circle, ∃ t ∈ Ioo (0 : ℝ) 1,
      c ≤ ‖∏ i, (1 - a i * (x i : ℂ) * (Circle.exp (t * ω i) : ℂ))‖ := by
  classical
  let P (t : ℝ) (x : ι → Circle) := ∏ i, (1 - a i * (x i : ℂ) * (Circle.exp (t * ω i) : ℂ))
  have hP (t : ℝ) : Continuous (P t) := by
    dsimp [P]
    fun_prop
  -- A factor that vanishes at zero becomes nonzero for all sufficiently small positive shifts.
  have hfactor (i : ι) (z : ℂ) : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      1 - z * (Circle.exp (t * ω i) : ℂ) ≠ 0 := by
    by_cases hz : z = 1
    · subst z
      have ht : Tendsto (fun t : ℝ ↦ t * ω i) (𝓝[>] 0) (𝓝 0) := by
        simpa using ((continuous_id.mul_const (ω i)).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
      obtain ⟨U, hU, h0, hinj⟩ := isLocalHomeomorph_circleExp.isLocallyInjective 0
      filter_upwards [ht (hU.mem_nhds h0), self_mem_nhdsWithin] with t hsmall hpos
      intro h
      have he : Circle.exp (t * ω i) = Circle.exp 0 := by
        apply Subtype.ext
        simpa using (sub_eq_zero.mp h).symm
      exact (mul_ne_zero (ne_of_gt hpos) (hω i)) (hinj hsmall h0 he)
    · have h : Continuous (fun t : ℝ ↦ 1 - z * (Circle.exp (t * ω i) : ℂ)) := by fun_prop
      exact ((h.tendsto 0).mono_left nhdsWithin_le_nhds).eventually_ne
        (by simpa using sub_ne_zero.mpr (Ne.symm hz))
  have hshift (x : ι → Circle) : ∃ t ∈ Ioo (0 : ℝ) 1, 0 < ‖P t x‖ := by
    have hI : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
    obtain ⟨t, ht, hf⟩ := (hI.and
      (eventually_all.mpr fun i ↦ hfactor i (a i * x i))).exists
    exact ⟨t, ht, norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hf i)⟩
  -- Keep half the value at each chosen shift, then take the minimum on a finite subcover.
  choose t ht hpos using hshift
  let d (x : ι → Circle) := ‖P (t x) x‖ / 2
  let U (x : ι → Circle) := {y | d x < ‖P (t x) y‖}
  have hU (x) : U x ∈ 𝓝 x :=
    (isOpen_lt continuous_const (hP (t x)).norm).mem_nhds (half_lt_self (hpos x))
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover U hU
  have cover (y : ι → Circle) : ∃ x ∈ s, y ∈ U x := by
    have : y ∈ ⋃ x ∈ s, U x := hs ▸ mem_univ y
    simpa only [mem_iUnion, exists_prop] using this
  obtain ⟨x, hx, _⟩ := cover 1
  obtain ⟨z, _, hz⟩ := s.exists_min_image d ⟨x, hx⟩
  refine ⟨d z, half_pos (hpos z), fun y ↦ ?_⟩
  obtain ⟨x, hx, hy⟩ := cover y
  exact ⟨t x, ht x, (hz x hx).trans (le_of_lt hy)⟩

/-- Paper: Proposition B.5.3.2, p. 632. There is a nondecreasing sequence
escaping to infinity on both tails on which the reciprocal product is bounded away from zero.
Deviation: Uses the negative sign condition for strictly negative indices. The height at
index zero may then be chosen away from all poles of the Euler factors. -/
theorem exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) :
    ∃ (c : ℝ) (T : ℤ → ℝ), 0 < c ∧ Monotone T ∧
      (∀ k, 0 ≤ k → 0 ≤ T k) ∧ (∀ k, k < 0 → T k ≤ 0) ∧
      Tendsto (fun k ↦ |T k|) (comap (abs : ℤ → ℤ) atTop) atTop ∧
      ∀ k, c ≤ ‖reciprocalPartialHeckeEulerProduct χ S ((T k : ℂ) * Complex.I)‖ := by
  classical
  let a (v : S) := (ideleClassNormTwist χ 0).localValue v.val
  let ω (v : S) := -Real.log (v.val.asIdeal.absNorm : ℝ)
  let phase (r : ℝ) (v : S) := Circle.exp (r * ω v)
  have hω (v : S) : ω v ≠ 0 :=
    neg_ne_zero.mpr (Real.log_pos (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val)).ne'
  have hpow (r : ℝ) (v : S) :
      (v.val.asIdeal.absNorm : ℂ) ^ (-((r : ℂ) * Complex.I)) = (phase r v : ℂ) := by
    have hq : (v.val.asIdeal.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v.val)).ne'
    change _ = Complex.exp (((r * ω v : ℝ) : ℂ) * Complex.I)
    rw [Complex.cpow_def_of_ne_zero hq, ← Complex.natCast_log]
    congr 1
    dsimp [ω]
    push_cast
    ring
  have hprod (r t : ℝ) : reciprocalPartialHeckeEulerProduct χ S (((r + t : ℝ) : ℂ) * Complex.I) =
      ∏ v : S, (1 - a v * (phase r v : ℂ) * (Circle.exp (t * ω v) : ℂ)) := by
    rw [reciprocalPartialHeckeEulerProduct, ← Finset.prod_coe_sort]
    refine Finset.prod_congr rfl fun v _ ↦ ?_
    rw [finiteHeckeEulerFactor, ite_eq_left (hχ v.val v.property), inv_inv, hpow]
    simp only [phase, add_mul, Circle.exp_add, Circle.coe_mul, a, mul_assoc]
  obtain ⟨c, hc, hshift⟩ := exists_eulerPhase_shift a ω hω
  choose t ht hbound using fun k : ℤ ↦ hshift (phase k)
  let T (k : ℤ) : ℝ := k + t k
  have hI (k : ℤ) : T k ∈ Ioo (k : ℝ) ((k : ℝ) + 1) :=
    ⟨lt_add_of_pos_right _ (ht k).1, add_lt_add_right (ht k).2 _⟩
  refine ⟨c, T, hc, ?_, ?_, ?_, ?_, fun k ↦ ?_⟩
  · apply monotone_int_of_le_succ
    intro k
    exact ((hI k).2.trans (by simpa only [Int.cast_add, Int.cast_one] using (hI (k + 1)).1)).le
  · intro k hk
    exact (show 0 ≤ (k : ℝ) by exact_mod_cast hk).trans (hI k).1.le
  · intro k hk
    have h : (k : ℝ) + 1 ≤ 0 := by exact_mod_cast (show k + 1 ≤ 0 by omega)
    exact (hI k).2.le.trans h
  · have hlim : Tendsto (fun k : ℤ ↦ ((|k| : ℤ) : ℝ)) (comap (abs : ℤ → ℤ) atTop) atTop :=
      tendsto_intCast_atTop_atTop.comp tendsto_comap
    refine tendsto_atTop_mono (fun k ↦ ?_) (tendsto_atTop_add_const_right _ (-1) hlim)
    rw [Int.cast_abs]
    have h := abs_sub_abs_le_abs_sub (k : ℝ) (T k)
    rw [abs_of_nonpos (sub_nonpos.mpr (hI k).1.le)] at h
    linarith [(hI k).2]
  · simpa only [T, hprod] using hbound k

/-- Returns of a torus flow to a neighbourhood of zero fill a positive proportion of both
`[0, T]` and `[-T, 0]` for all large `T`. This is the equidistribution input of
Proposition B.5.3.3, taken from the continuous Kronecker–Weyl theorems on the orbit closure. -/
private theorem reciprocalPartialHeckeEulerProduct_upperDensity_flowReturns (N : ℕ)
    (τ : Fin N → ℝ) {W : Set (UnitAddTorus (Fin N))} (hW : W ∈ 𝓝 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop,
      c * T ≤ volume.real (Icc 0 T ∩ {t | torusFlow τ t ∈ W}) ∧
      c * T ≤ volume.real (Icc (-T) 0 ∩ {t | torusFlow τ t ∈ W}) := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · -- In dimension zero the torus is a point, so every time is a return.
    have hall : {t : ℝ | torusFlow τ t ∈ W} = univ := by
      ext t
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      rw [Subsingleton.elim (torusFlow τ t) 0]
      exact mem_of_mem_nhds hW
    refine ⟨1, one_pos, (eventually_ge_atTop 0).mono fun T hT ↦ ?_⟩
    rw [hall, inter_univ, inter_univ, Real.volume_real_Icc_of_le hT,
      Real.volume_real_Icc_of_le (by linarith)]
    constructor <;> linarith
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨O, hOW, hO, h0O⟩ := mem_nhds_iff.mp hW
  obtain ⟨φ, hφ0, hφ1, hφ01⟩ := exists_continuous_zero_one_of_isClosed hO.isClosed_compl
    (isClosed_singleton (x := (0 : UnitAddTorus (Fin N))))
    (disjoint_singleton_right.mpr fun h ↦ h h0O)
  have : CompactSpace (torusFlowClosure τ) := isCompact_iff_compactSpace.mp
    (AddSubgroup.isClosed_topologicalClosure _).isCompact
  let μ : Measure (torusFlowClosure τ) := Measure.addHaarMeasure ⊤
  have : IsProbabilityMeasure μ := ⟨Measure.addHaarMeasure_self⟩
  let u : C(torusFlowClosure τ, ℂ) :=
    ⟨fun x ↦ (φ x : ℂ), Complex.continuous_ofReal.comp (φ.continuous.comp continuous_subtype_val)⟩
  -- The mean of the bump over the orbit closure is positive.
  set c₀ : ℝ := ∫ x, φ (x : UnitAddTorus (Fin N)) ∂μ with hc₀
  have hc₀pos : 0 < c₀ :=
    (φ.continuous.comp continuous_subtype_val).integral_pos_of_hasCompactSupport_nonneg_ne_zero
      (x := (0 : torusFlowClosure τ)) (HasCompactSupport.of_compactSpace _)
      (fun x ↦ (hφ01 _).1) (by simp [hφ1 (mem_singleton (0 : UnitAddTorus (Fin N)))])
  have hmean : (∫ x, u x ∂μ) = (c₀ : ℂ) := integral_ofReal
  let g : ℝ → ℝ := fun t ↦ φ (torusFlow τ t)
  have hg : Continuous g := φ.continuous.comp (torusFlow τ).continuous
  have hcoe (a b : ℝ) : (∫ t in a..b, u (torusFlowInClosure τ t)) = ((∫ t in a..b, g t : ℝ) : ℂ) :=
    intervalIntegral.integral_ofReal
  have hre {f : ℝ → ℝ} {l : ℝ} (h : Tendsto (fun T : ℝ ↦ ((f T : ℝ) : ℂ)) atTop (𝓝 (l : ℂ))) :
      Tendsto f atTop (𝓝 l) := by
    simpa [Function.comp_def] using (Complex.continuous_re.tendsto _).comp h
  have hfwd : Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in (0 : ℝ)..T, g t) atTop (𝓝 c₀) := by
    refine hre ?_
    have h := kroneckerWeyl_continuous_forward τ μ u
    rw [hmean] at h
    refine h.congr fun T ↦ ?_
    rw [hcoe, Complex.real_smul, Complex.ofReal_mul]
  have hsym : Tendsto (fun T : ℝ ↦ (2 * T)⁻¹ * ∫ t in -T..T, g t) atTop (𝓝 c₀) := by
    refine hre ?_
    have h := kroneckerWeyl_continuous_symmetric τ μ u
    rw [hmean] at h
    refine h.congr fun T ↦ ?_
    rw [hcoe, Complex.real_smul, Complex.ofReal_mul]
  have hII (a b : ℝ) : IntervalIntegrable g volume a b := hg.intervalIntegrable a b
  have hbwd : Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ t in -T..0, g t) atTop (𝓝 c₀) := by
    have h := (hsym.const_mul 2).sub hfwd
    rw [show 2 * c₀ - c₀ = c₀ by ring] at h
    refine h.congr' ((eventually_ne_atTop 0).mono fun T hT ↦ ?_)
    rw [← intervalIntegral.integral_add_adjacent_intervals (hII (-T) 0) (hII 0 T)]
    field_simp
    ring
  -- Along the flow the bump is at most the indicator of the returns.
  let P : Set ℝ := {t | torusFlow τ t ∈ O}
  have hPmeas : MeasurableSet P := (hO.preimage (torusFlow τ).continuous).measurableSet
  have hgP : ∀ t, g t ≤ P.indicator (fun _ ↦ (1 : ℝ)) t := by
    intro t
    by_cases ht : t ∈ P
    · rw [indicator_of_mem ht]
      exact (hφ01 _).2
    · rw [indicator_of_notMem ht]
      exact (hφ0 ht).le
  have hbound {a b : ℝ} (hab : a ≤ b) :
      ∫ t in a..b, g t ≤ volume.real (Icc a b ∩ {t | torusFlow τ t ∈ W}) := by
    have : IsFiniteMeasure (volume.restrict (Ioc a b)) :=
      isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
    rw [intervalIntegral.integral_of_le hab]
    calc ∫ t in Ioc a b, g t ≤ ∫ t in Ioc a b, P.indicator (fun _ ↦ (1 : ℝ)) t :=
          integral_mono (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
            ((integrable_const (1 : ℝ)).indicator hPmeas) hgP
      _ = volume.real (P ∩ Ioc a b) := by
          rw [integral_indicator_const _ hPmeas, smul_eq_mul, mul_one,
            measureReal_restrict_apply hPmeas]
      _ ≤ volume.real (Icc a b ∩ {t | torusFlow τ t ∈ W}) :=
          measureReal_mono (fun t ht ↦ ⟨Ioc_subset_Icc_self ht.2, hOW ht.1⟩)
            ((measure_mono inter_subset_left).trans_lt measure_Icc_lt_top).ne
  refine ⟨c₀ / 2, half_pos hc₀pos, ?_⟩
  filter_upwards [hfwd.eventually (lt_mem_nhds (half_lt_self hc₀pos)),
    hbwd.eventually (lt_mem_nhds (half_lt_self hc₀pos)), eventually_gt_atTop 0] with T h₁ h₂ hT
  rw [inv_mul_eq_div, lt_div_iff₀ hT] at h₁ h₂
  exact ⟨h₁.le.trans (hbound hT.le), h₂.le.trans (hbound (by linarith))⟩

/-- Vertical shifts whose phases at the primes of `S` are close to one uniformly approximate
the reciprocal partial Euler product on a compact set, and such shifts fill a positive
proportion of both `[0, T]` and `[-T, 0]` for all large `T`. -/
private theorem reciprocalPartialHeckeEulerProduct_upperDensity_returns
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop,
      c * T ≤ volume.real
        (Icc 0 T ∩ verticalReturnTimes (reciprocalPartialHeckeEulerProduct χ S) K ε) ∧
      c * T ≤ volume.real
        (Icc (-T) 0 ∩ verticalReturnTimes (reciprocalPartialHeckeEulerProduct χ S) K ε) := by
  classical
  let e := S.equivFin
  let q (i : Fin S.card) : ℕ := (e.symm i).val.asIdeal.absNorm
  have hq (i : Fin S.card) : (q i : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm (e.symm i).val)).ne'
  let a (i : Fin S.card) : ℂ := (ideleClassNormTwist χ 0).localValue (e.symm i).val
  let τ (i : Fin S.card) : ℝ := -Real.log (q i) / (2 * Real.pi)
  let Φ (z : ℂ) (x : UnitAddTorus (Fin S.card)) : ℂ :=
    ∏ i, (1 - a i * (q i : ℂ) ^ (-z) * fourier 1 (x i))
  have hphase (i : Fin S.card) (t : ℝ) :
      (fourier 1 ((torusFlow τ t) i) : ℂ) = (q i : ℂ) ^ (-((t : ℂ) * Complex.I)) := by
    change (fourier 1 (((t * τ i : ℝ)) : AddCircle (1 : ℝ)) : ℂ) = _
    rw [fourier_coe_apply, Complex.cpow_def_of_ne_zero (hq i), ← Complex.natCast_log]
    congr 1
    simp only [τ]
    push_cast
    field_simp
  have hΦ (z : ℂ) (t : ℝ) :
      reciprocalPartialHeckeEulerProduct χ S (z + (t : ℂ) * Complex.I) = Φ z (torusFlow τ t) := by
    rw [reciprocalPartialHeckeEulerProduct, ← Finset.prod_coe_sort, ← e.symm.prod_comp]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [finiteHeckeEulerFactor, ite_eq_left (hχ _ (e.symm i).property), inv_inv, hphase,
      neg_add, Complex.cpow_add _ _ (hq i)]
    ring
  have hΦ0 (z : ℂ) : reciprocalPartialHeckeEulerProduct χ S z = Φ z 0 := by
    simpa [map_zero] using hΦ z 0
  have hcont : Continuous fun p : UnitAddTorus (Fin S.card) × ℂ ↦ ‖Φ p.2 p.1 - Φ p.2 0‖ := by
    have hpow (i : Fin S.card) : Continuous fun z : ℂ ↦ (q i : ℂ) ^ (-z) :=
      continuous_neg.const_cpow (Or.inl (hq i))
    have hΦc : Continuous fun p : UnitAddTorus (Fin S.card) × ℂ ↦ Φ p.2 p.1 := by
      refine continuous_finsetProd _ fun i _ ↦ ?_
      exact continuous_const.sub ((continuous_const.mul ((hpow i).comp continuous_snd)).mul
        ((fourier 1).continuous.comp ((continuous_apply i).comp continuous_fst)))
    have hΦc0 : Continuous fun p : UnitAddTorus (Fin S.card) × ℂ ↦ Φ p.2 0 :=
      hΦc.comp (continuous_const.prodMk continuous_snd)
    exact (hΦc.sub hΦc0).norm
  have hW : ∀ᶠ x in 𝓝 (0 : UnitAddTorus (Fin S.card)), ∀ z ∈ K, ‖Φ z x - Φ z 0‖ < ε / 2 :=
    hK.eventually_forall_of_forall_eventually fun z _ ↦
      (hcont.tendsto (0, z)).eventually (gt_mem_nhds (by simpa using half_pos hε))
  have hsub : {t | torusFlow τ t ∈ {x | ∀ z ∈ K, ‖Φ z x - Φ z 0‖ < ε / 2}} ⊆
      verticalReturnTimes (reciprocalPartialHeckeEulerProduct χ S) K ε := by
    intro t ht
    refine lt_of_le_of_lt (iSup_le fun z ↦ ?_)
      ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (half_lt_self hε))
    rw [hΦ, hΦ0, ← eNorm_eq_nnNorm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (ht z z.2).le
  obtain ⟨c, hc, hev⟩ := reciprocalPartialHeckeEulerProduct_upperDensity_flowReturns _ τ hW
  have hfin (A B : Set ℝ) (a b : ℝ) (h : A ⊆ B) :
      volume.real (Icc a b ∩ A) ≤ volume.real (Icc a b ∩ B) :=
    measureReal_mono (inter_subset_inter_right _ h)
      ((measure_mono inter_subset_left).trans_lt measure_Icc_lt_top).ne
  exact ⟨c, hc, hev.mono fun T hT ↦ ⟨hT.1.trans (hfin _ _ _ _ hsub),
    hT.2.trans (hfin _ _ _ _ hsub)⟩⟩

/-- A set that fills a proportion `c` of `[0, T]` or of `[-T, 0]` for all large `T` has
upper density at least `c / 2`. -/
private theorem reciprocalPartialHeckeEulerProduct_upperDensity_of_le {X : Set ℝ} {c : ℝ}
    (h : ∀ᶠ T : ℝ in atTop, c * T ≤ volume.real (Icc (-T) T ∩ X)) :
    c / 2 ≤ upperDensity X := by
  have hle : ∀ᶠ T : ℝ in atTop, volume.real (Icc (-T) T ∩ X) / (2 * T) ≤ 1 := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [div_le_one (by positivity)]
    refine (measureReal_mono inter_subset_left measure_Icc_lt_top.ne).trans ?_
    rw [Real.volume_real_Icc_of_le (by linarith)]
    linarith
  refine le_limsup_of_frequently_le ?_ (isBoundedUnder_of_eventually_le hle)
  refine (h.and (eventually_gt_atTop 0)).frequently.mono fun T ⟨hT, hT0⟩ ↦ ?_
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- Paper: Proposition B.5.3.3, p. 632.
The nonnegative vertical shifts that uniformly approximate the reciprocal partial Euler
product on the compact set have positive symmetric upper density. -/
theorem reciprocalPartialHeckeEulerProduct_upperDensity_nonneg
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    {a b : ℝ} (hI : (0 : ℝ) ∈ Ioo a b) {K : Set ℂ} (hK : IsCompact K)
    (hKI : K ⊆ verticalStrip a b) (hKint : (interior K).Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    0 < upperDensity (Ici 0 ∩ verticalReturnTimes (reciprocalPartialHeckeEulerProduct χ S) K ε) := by
  obtain ⟨c, hc, hev⟩ := reciprocalPartialHeckeEulerProduct_upperDensity_returns χ S hχ hK hε
  refine (half_pos hc).trans_le (reciprocalPartialHeckeEulerProduct_upperDensity_of_le ?_)
  filter_upwards [hev, eventually_ge_atTop 0] with T hT hT0
  exact hT.1.trans (measureReal_mono (fun t ht ↦ ⟨⟨by linarith [ht.1.1], ht.1.2⟩, ht.1.1, ht.2⟩)
    ((measure_mono inter_subset_left).trans_lt measure_Icc_lt_top).ne)

/-- Paper: Proposition B.5.3.3, p. 632.
The nonpositive vertical shifts that uniformly approximate the reciprocal partial Euler
product on the compact set have positive symmetric upper density. -/
theorem reciprocalPartialHeckeEulerProduct_upperDensity_nonpos
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    {a b : ℝ} (hI : (0 : ℝ) ∈ Ioo a b) {K : Set ℂ} (hK : IsCompact K)
    (hKI : K ⊆ verticalStrip a b) (hKint : (interior K).Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    0 < upperDensity (Iic 0 ∩ verticalReturnTimes (reciprocalPartialHeckeEulerProduct χ S) K ε) := by
  obtain ⟨c, hc, hev⟩ := reciprocalPartialHeckeEulerProduct_upperDensity_returns χ S hχ hK hε
  refine (half_pos hc).trans_le (reciprocalPartialHeckeEulerProduct_upperDensity_of_le ?_)
  filter_upwards [hev, eventually_ge_atTop 0] with T hT hT0
  exact hT.2.trans (measureReal_mono (fun t ht ↦ ⟨⟨ht.1.1, by linarith [ht.1.2]⟩, ht.1.2, ht.2⟩)
    ((measure_mono inter_subset_left).trans_lt measure_Icc_lt_top).ne)

-- TODO(paper-gap): The proof of Proposition B.5.3.3 uses the ambient cube to infer Haar
-- nullity on a possibly lower-dimensional orbit closure. The level set must be treated
-- intrinsically on that closure. To apply the area estimate, integrate on an open
-- neighbourhood of the target compact set.

/-- Upper density is monotone in the set. -/
private theorem upperDensity_mono {X Y : Set ℝ} (h : X ⊆ Y) :
    upperDensity X ≤ upperDensity Y := by
  have hfin (T : ℝ) (Z : Set ℝ) : volume (Icc (-T) T ∩ Z) ≠ ∞ :=
    ((measure_mono inter_subset_left).trans_lt measure_Icc_lt_top).ne
  have hle (Z : Set ℝ) : ∀ᶠ T : ℝ in atTop, volume.real (Icc (-T) T ∩ Z) / (2 * T) ≤ 1 := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [div_le_one (by positivity)]
    refine (measureReal_mono inter_subset_left measure_Icc_lt_top.ne).trans ?_
    rw [Real.volume_real_Icc_of_le (by linarith)]
    linarith
  have hge (Z : Set ℝ) : ∀ᶠ T : ℝ in atTop, 0 ≤ volume.real (Icc (-T) T ∩ Z) / (2 * T) := by
    filter_upwards [eventually_ge_atTop 0] with T hT
    exact div_nonneg measureReal_nonneg (by positivity)
  refine limsup_le_limsup ?_ (isCoboundedUnder_le_of_eventually_le _ (hge X))
    (isBoundedUnder_of_eventually_le (hle Y))
  filter_upwards [eventually_ge_atTop 0] with T hT
  exact div_le_div_of_nonneg_right
    (measureReal_mono (inter_subset_inter_right _ h) (hfin T Y)) (by positivity)

/-- Paper: Lemma B.5.3.4(1), p. 633.
For a holomorphic function on a bounded open strip, strong recurrence on a compact subset
descends to every compact subset of that subset. -/
theorem stronglyRecurrentOn_of_subset {a b : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (verticalStrip a b)) {K K' : Set ℂ}
    (hK : IsCompact K) (hKI : K ⊆ verticalStrip a b) (hK' : IsCompact K') (hsub : K' ⊆ K)
    (hrec : StronglyRecurrentOn f K) : StronglyRecurrentOn f K' := by
  intro ε hε
  refine (hrec ε hε).trans_le (upperDensity_mono fun t ht ↦ ?_)
  exact lt_of_le_of_lt (iSup_le fun z : K' ↦ le_iSup
    (fun w : K ↦ (‖f ((w : ℂ) + (t : ℂ) * Complex.I) - f w‖₊ : ℝ≥0∞)) ⟨z.1, hsub z.2⟩) ht

-- TODO(paper-gap): Lemma B.5.3.4(2) fails. A compact vertical segment need not fit inside
-- any disc contained in the strip, and disc-by-disc recurrence need not give simultaneous return
-- times on that segment. The report gives a Runge approximation counterexample.

open Metric Real in
/-- The square of the norm at the centre is at most the circle average of the squared norm. -/
private theorem sq_norm_le_circleAverage_sq_norm {g : ℂ → ℂ} {c : ℂ} {r ρ : ℝ}
    (hg : DifferentiableOn ℂ g (ball c r)) (hρ : ρ ∈ Ioo 0 r) :
    ‖g c‖ ^ 2 ≤ circleAverage (fun z ↦ ‖g z‖ ^ 2) c ρ := by
  have hd : DiffContOnCl ℂ (fun z ↦ g z ^ 2) (ball c |ρ|) := by
    rw [abs_of_pos hρ.1]
    exact (hg.pow 2).diffContOnCl_ball (closedBall_subset_ball hρ.2)
  have h := norm_circleAverage_le_circleAverage_norm (f := fun z ↦ g z ^ 2) (c := c) (R := ρ)
  rw [hd.circleAverage] at h
  simpa only [norm_pow] using h

open Metric Real in
/-- On a circle inside the disc, the angular integral of the squared norm over `(-π, π)` is at
least `2π` times the squared norm at the centre. -/
private theorem integral_Ioo_sq_norm_circleMap_ge {g : ℂ → ℂ} {c : ℂ} {r ρ : ℝ}
    (hg : DifferentiableOn ℂ g (ball c r)) (hρ : ρ ∈ Ioo 0 r) :
    2 * π * ‖g c‖ ^ 2 ≤ ∫ θ in Ioo (-π) π, ‖g (circleMap c ρ θ)‖ ^ 2 := by
  set F : ℝ → ℝ := fun θ ↦ ‖g (circleMap c ρ θ)‖ ^ 2
  have hper : F.Periodic (2 * π) := fun θ ↦ by simp only [F, periodic_circleMap c ρ θ]
  have hint := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at hint
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos]),
    hint]
  have h := sq_norm_le_circleAverage_sq_norm hg hρ
  rw [circleAverage_def, smul_eq_mul] at h
  have h2π : 0 < 2 * π := two_pi_pos
  calc 2 * π * ‖g c‖ ^ 2 ≤ 2 * π * ((2 * π)⁻¹ * ∫ θ in 0..2 * π, F θ) := by gcongr
    _ = ∫ θ in 0..2 * π, F θ := by field_simp

open Metric Real in
/-- On the open disc, the squared norm of a holomorphic function has integral at least
`π r²` times its squared norm at the centre. -/
private theorem lintegral_ball_sq_norm_ge {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c r)) :
    ENNReal.ofReal (π * r ^ 2 * ‖g c‖ ^ 2) ≤
      ∫⁻ z in ball c r, ENNReal.ofReal (‖g z‖ ^ 2) := by
  set G : ℂ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (‖g z‖ ^ 2)
  set A : Set ℝ := Ioo 0 r
  set B : Set ℝ := Ioo (-π) π
  have hpolar (p : ℝ × ℝ) : c + Complex.polarCoord.symm p = circleMap c p.1 p.2 := by
    simp only [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hmem {ρ : ℝ} (hρ : ρ ∈ A) (θ : ℝ) : circleMap c ρ θ ∈ ball c r := by
    rw [mem_ball, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ.1]
    exact hρ.2
  have hcirc : Continuous (fun p : ℝ × ℝ ↦ circleMap c p.1 p.2) := by
    unfold circleMap; fun_prop
  have hcont : ContinuousOn (fun p : ℝ × ℝ ↦ p.1 * ‖g (circleMap c p.1 p.2)‖ ^ 2) (A ×ˢ B) :=
    continuous_fst.continuousOn.mul ((hg.continuousOn.norm.pow 2).comp hcirc.continuousOn
      fun p hp ↦ hmem hp.1 p.2)
  have hAB : MeasurableSet (A ×ˢ B) := measurableSet_Ioo.prod measurableSet_Ioo
  calc ENNReal.ofReal (π * r ^ 2 * ‖g c‖ ^ 2)
      = ∫⁻ ρ in A, ENNReal.ofReal (ρ * (2 * π * ‖g c‖ ^ 2)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal]
        · congr 1
          rw [integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
            ← intervalIntegral.integral_of_le hr.le, integral_id]
          ring
        · exact (continuous_id.mul continuous_const).integrableOn_Icc.mono_set Ioo_subset_Icc_self
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
          have := hρ.1.le
          positivity
    _ ≤ ∫⁻ ρ in A, ∫⁻ θ in B, ENNReal.ofReal (ρ * ‖g (circleMap c ρ θ)‖ ^ 2) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with ρ hρ
        have hF : Continuous fun θ ↦ ρ * ‖g (circleMap c ρ θ)‖ ^ 2 :=
          continuous_const.mul ((hg.continuousOn.norm.pow 2).comp_continuous
            (continuous_circleMap c ρ) (hmem hρ))
        rw [← ofReal_integral_eq_lintegral_ofReal
          (hF.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
          (Eventually.of_forall fun θ ↦ by have := hρ.1.le; positivity),
          integral_const_mul]
        exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (integral_Ioo_sq_norm_circleMap_ge hg hρ) hρ.1.le)
    _ = ∫⁻ p in A ×ˢ B, ENNReal.ofReal (p.1 * ‖g (circleMap c p.1 p.2)‖ ^ 2) := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod]
        rw [Measure.prod_restrict]
        exact ENNReal.measurable_ofReal.comp_aemeasurable (hcont.aemeasurable hAB)
    _ = ∫⁻ p in A ×ˢ B, ENNReal.ofReal p.1 • (ball c r).indicator G
          (c + Complex.polarCoord.symm p) := by
        refine setLIntegral_congr_fun hAB fun p hp ↦ ?_
        rw [hpolar, indicator_of_mem (hmem hp.1 p.2), smul_eq_mul, ← ENNReal.ofReal_mul hp.1.1.le]
    _ ≤ ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • (ball c r).indicator G
          (c + Complex.polarCoord.symm p) := by
        refine lintegral_mono_set ?_
        exact prod_mono Ioo_subset_Ioi_self subset_rfl
    _ = ∫⁻ z in ball c r, G z := by
        rw [Complex.lintegral_comp_polarCoord_symm (fun w ↦ (ball c r).indicator G (c + w)),
          lintegral_add_left_eq_self, lintegral_indicator measurableSet_ball]

-- Retain the hypotheses of the existing signature that the proof does not use.
set_option linter.unusedVariables false in
/-- Paper: Lemma B.5.3.5, p. 633.
If the squared area error integrated over the closure of the open set is below
`π * δ² * X²`, the uniform error on the compact set is below `X`.
Deviation: The subscript `r` in (B.5.3.6) is read as `2`, as in (B.5.3.8). -/
theorem areaApproximation_subset_verticalReturnTimes {a b : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (verticalStrip a b)) {K U : Set ℂ}
    (hK : IsCompact K) (hKne : K.Nonempty) (hKI : K ⊆ verticalStrip a b)
    (hU : IsOpen U) (hUcompact : IsCompact (closure U)) (hUI : closure U ⊆ verticalStrip a b)
    (hKU : K ⊆ U) {δ : ℝ} (hδ : δ = ⨅ z : K, Metric.infDist (z : ℂ) Uᶜ)
    (hδpos : 0 < δ) {T X : ℝ} (hT : 0 < T) (hX : 0 < X) :
    {t ∈ Icc (-T) T | (∫ z in closure U, ‖f (z + (t : ℂ) * Complex.I) - f z‖ ^ 2) <
      Real.pi * δ ^ 2 * X ^ 2} ⊆ Icc (-T) T ∩ verticalReturnTimes f K X := by
  rintro t ⟨htT, hI⟩
  refine ⟨htT, ?_⟩
  set g : ℂ → ℂ := fun z ↦ f (z + (t : ℂ) * Complex.I) - f z
  set I := ∫ z in closure U, ‖g z‖ ^ 2
  have hshift : MapsTo (fun z : ℂ ↦ z + (t : ℂ) * Complex.I) (verticalStrip a b)
      (verticalStrip a b) := fun z hz ↦ by
    simpa [Complex.HadamardThreeLines.verticalStrip] using hz
  have hgd : DifferentiableOn ℂ g (verticalStrip a b) :=
    (hf.comp (differentiableOn_id.add_const _) hshift).sub hf
  have hUs : U ⊆ verticalStrip a b := subset_closure.trans hUI
  have hgint : IntegrableOn (fun z ↦ ‖g z‖ ^ 2) (closure U) :=
    ((hgd.continuousOn.mono hUI).norm.pow 2).integrableOn_compact hUcompact
  have hπδ : 0 < Real.pi * δ ^ 2 := by positivity
  have hbound (z : ℂ) (hz : z ∈ K) : ‖g z‖ ^ 2 * (Real.pi * δ ^ 2) ≤ I := by
    have hball : Metric.ball z δ ⊆ U := by
      intro w hw
      by_contra hwU
      have h1 : δ ≤ Metric.infDist z Uᶜ := hδ ▸
        ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact Metric.infDist_nonneg⟩ (⟨z, hz⟩ : K)
      have h2 := Metric.infDist_le_dist_of_mem (x := z) (show w ∈ Uᶜ from hwU)
      rw [Metric.mem_ball, dist_comm] at hw
      linarith
    have hsub : Metric.ball z δ ⊆ closure U := hball.trans subset_closure
    have harea := lintegral_ball_sq_norm_ge hδpos (hgd.mono (hball.trans hUs))
    rw [← ofReal_integral_eq_lintegral_ofReal (hgint.mono_set hsub)
      (Eventually.of_forall fun _ ↦ by positivity),
      ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ ↦ by positivity)] at harea
    calc ‖g z‖ ^ 2 * (Real.pi * δ ^ 2) = Real.pi * δ ^ 2 * ‖g z‖ ^ 2 := by ring
      _ ≤ ∫ w in Metric.ball z δ, ‖g w‖ ^ 2 := harea
      _ ≤ I := setIntegral_mono_set hgint (Eventually.of_forall fun _ ↦ by positivity)
          (Eventually.of_forall hsub)
  have hM : √(I / (Real.pi * δ ^ 2)) < X := by
    rw [Real.sqrt_lt' hX, div_lt_iff₀ hπδ]
    linarith
  show (⨆ z : K, (‖g z‖₊ : ℝ≥0∞)) < ENNReal.ofReal X
  refine lt_of_le_of_lt (iSup_le fun z ↦ ?_) ((ENNReal.ofReal_lt_ofReal_iff hX).mpr hM)
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnNorm]
  exact ENNReal.ofReal_le_ofReal (Real.le_sqrt_of_sq_le ((le_div_iff₀ hπδ).mpr (hbound z z.2)))

end Recurrence

end RiemannMasullo
