module

public import RiemannMasullo.Ch10_TraceSpectral.Sec1
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.AccretiveJets
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.LaplaceSemigroup
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.LaplaceUnitaryGroup
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! # Translations along a section on the unweighted `L²` space of the idele classes

Masullo, §10.4.2, pp. 459–464. This file belongs to the open statement
`Isolated.spectralStripConvolution_hilbertSchmidt_of_le_one` (#7405). It formalizes the
positivity step of the real-variable argument posted there, on the objects of the library.
Nothing imports it, and nothing in it depends on an unproved statement.

The positivity step of that argument does not live on the weighted space of the strip but on
the unweighted space `L²(C_F)` for the Tamagawa measure, where translations are unitary. Let
`τ` be a continuous homomorphism from the positive reals to the idele classes, for instance a
section of the idele class norm. In the logarithmic coordinate `x` the translations
`U x g = (y ↦ g ((τ (exp x))⁻¹ * y))` form a strongly continuous unitary group of `L²(C_F)`
(`sectionL2Translation`). For a rate `c > 0` its one-sided Laplace transforms

* `P g = ∫ x in Ioi 0, exp (-c x) • U x g` (`sectionL2ForwardLaplace`),
* `Q g = ∫ x in Ioi 0, exp (-c x) • U (-x) g` (`sectionL2BackwardLaplace`)

are bounded operators of norm at most `c⁻¹`. In the notation of the argument, `P` is convolution
along the section with `p_c`, and `Q` is convolution with the reflection of `p_c`.

## Main statements

* `sectionL2Translation_apply`, `sectionL2Translation_zero`, `sectionL2Translation_add`,
  `norm_sectionL2Translation`, `continuous_sectionL2Translation`: the translations along the
  section are a strongly continuous unitary group.
* `sectionL2ForwardLaplace_apply`, `norm_sectionL2ForwardLaplace_apply_le` and the same for the
  backward transform: the transforms are the integrals of the damped orbits and are bounded by
  `c⁻¹`.
* `mul_norm_sq_sectionL2ForwardLaplace_le_re_inner`,
  `mul_norm_sq_sectionL2BackwardLaplace_le_re_inner`: both are accretive,
  `c * ‖P g‖ ^ 2 ≤ re ⟪g, P g⟫`.
* `adjoint_sectionL2ForwardLaplace`, `adjoint_sectionL2BackwardLaplace`: each is the adjoint of
  the other at the same rate.
* `sectionL2ForwardLaplace_comm_backwardLaplace`, `norm_sectionL2BackwardLaplace_apply`: they
  commute, at any two rates, and at the same rate they have the same norm on every vector.
* `sectionL2Laplace_accretive`: the four hypotheses of
  `two_thirds_mul_sum_le_re_sum_inner_jet_add` for a forward transform at one rate and a
  backward transform at another, and
  `two_thirds_mul_sum_le_re_sum_inner_jet_sectionL2Laplace`: its conclusion for them.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology InnerProductSpace

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

local notation "𝓛(" μ ", " a ")" =>
  (Lp.compMeasurePreservingₗᵢ ℂ (fun y ↦ a⁻¹ * y)
    (measurePreserving_mul_left μ a⁻¹)).toContinuousLinearMap

/-- The left translate of a vector of `L²` of a group with a Haar measure is represented by
the translated function. -/
private theorem coeFn_leftTranslationL2 (μ : Measure G) [μ.IsHaarMeasure] (a : G)
    (u : Lp ℂ 2 μ) : (𝓛(μ, a) u : G → ℂ) =ᵐ[μ] fun y ↦ u (a⁻¹ * y) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_mul_left μ a⁻¹)

/-- Left translation of `L²` by the unit of the group is the identity. -/
private theorem leftTranslationL2_one (μ : Measure G) [μ.IsHaarMeasure] (a : G) (ha : a = 1)
    (u : Lp ℂ 2 μ) : 𝓛(μ, a) u = u := by
  subst ha
  refine Lp.ext ((coeFn_leftTranslationL2 μ 1 u).trans (.of_forall fun y ↦ ?_))
  beta_reduce
  rw [inv_one, one_mul]

/-- Left translation of `L²` by a product is the composition of the translations. -/
private theorem leftTranslationL2_mul (μ : Measure G) [μ.IsHaarMeasure] (a b c : G)
    (hc : c = a * b) (u : Lp ℂ 2 μ) : 𝓛(μ, c) u = 𝓛(μ, a) (𝓛(μ, b) u) := by
  subst hc
  refine Lp.ext ?_
  filter_upwards [coeFn_leftTranslationL2 μ (a * b) u,
    coeFn_leftTranslationL2 μ a (𝓛(μ, b) u),
    (measurePreserving_mul_left μ a⁻¹).quasiMeasurePreserving.ae_eq_comp
      (coeFn_leftTranslationL2 μ b u)] with y h₁ h₂ h₃
  have h₄ : (𝓛(μ, b) u : G → ℂ) (a⁻¹ * y) = u (b⁻¹ * (a⁻¹ * y)) := h₃
  rw [h₁, h₂, h₄, mul_inv_rev, mul_assoc]

/-- Left translation of `L²` of a group with a Haar measure preserves the norm. -/
private theorem norm_leftTranslationL2 (μ : Measure G) [μ.IsHaarMeasure] (a : G)
    (u : Lp ℂ 2 μ) : ‖𝓛(μ, a) u‖ = ‖u‖ :=
  Lp.norm_compMeasurePreserving u (measurePreserving_mul_left μ a⁻¹)

/-- The left translates of a vector of `L²` of a locally compact second countable group along
a continuous path in the group depend continuously on the parameter. -/
private theorem continuous_leftTranslationL2 (μ : Measure G) [μ.IsHaarMeasure] (σ : ℝ → G)
    (hσ : Continuous σ) (u : Lp ℂ 2 μ) : Continuous fun x : ℝ ↦ 𝓛(μ, σ x) u := by
  let g : C(ℝ × G, G) := ⟨fun p ↦ (σ p.1)⁻¹ * p.2, by fun_prop⟩
  have hg : Continuous fun x : ℝ ↦ (g.curry x : C(G, G)) := g.curry.continuous
  exact Continuous.compMeasurePreservingLp (f := fun _ : ℝ ↦ u) continuous_const hg
    (fun x ↦ measurePreserving_mul_left μ (σ x)⁻¹) ENNReal.ofNat_ne_top

end Abstract

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "H𝔽" => Lp ℂ 2 μ𝔽
local notation "expU(" x ")" =>
  (Units.mk0 (Real.exp x).toNNReal (Real.toNNReal_pos.mpr (Real.exp_pos x)).ne' : ℝ≥0ˣ)

section Translation

/-- The exponential is continuous into the positive real units. -/
private theorem continuous_expUnits_sectionL2 : Continuous fun x : ℝ ↦ expU(x) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact continuous_real_toNNReal.comp Real.continuous_exp
  · have h : (fun x : ℝ ↦ ((expU(x)⁻¹ : ℝ≥0ˣ) : ℝ≥0)) = fun x : ℝ ↦ (Real.exp (-x)).toNNReal := by
      funext x
      rw [Units.val_inv_eq_inv_val, Units.val_mk0, Real.exp_neg, Real.toNNReal_inv]
    rw [h]
    exact continuous_real_toNNReal.comp (Real.continuous_exp.comp continuous_neg)

/-- The exponential into the positive real units is additive-to-multiplicative. -/
private theorem expUnits_add_sectionL2 (x y : ℝ) : expU(x + y) = expU(x) * expU(y) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, Real.exp_add,
    Real.toNNReal_mul (Real.exp_pos x).le]

/-- The exponential into the positive real units sends zero to one. -/
private theorem expUnits_zero_sectionL2 : expU((0 : ℝ)) = 1 := by
  apply Units.ext
  rw [Units.val_mk0, Real.exp_zero, Real.toNNReal_one, Units.val_one]

/-- Reconstruction: the translation of the unweighted space `L²(C_F)` for the Tamagawa measure
by the point of a one-parameter subgroup `τ` of the idele classes at logarithmic coordinate
`x`, that is, `g ↦ (y ↦ g ((τ (exp x))⁻¹ * y))`. It is not in the paper. It is the unitary
model of the translations along a section of the idele class norm on which the positivity step
of the argument for Theorem 10.4.2.1 posted on #7405 takes place; the paper's translations
(Definition 9.3.1.1, p. 419) act on the weighted spaces, where they are not isometries. -/
def sectionL2Translation (τ : ℝ≥0ˣ →ₜ* C𝔽) (x : ℝ) : H𝔽 →L[ℂ] H𝔽 :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun y : C𝔽 ↦ (τ expU(x))⁻¹ * y)
    (measurePreserving_mul_left μ𝔽 (τ expU(x))⁻¹)).toContinuousLinearMap

/-- The translate of a vector of `L²(C_F)` along the section is represented by the translated
function. -/
theorem sectionL2Translation_apply (τ : ℝ≥0ˣ →ₜ* C𝔽) (x : ℝ) (g : H𝔽) :
    (sectionL2Translation τ x g : C𝔽 → ℂ) =ᵐ[μ𝔽] fun y ↦ g ((τ expU(x))⁻¹ * y) :=
  coeFn_leftTranslationL2 μ𝔽 (τ expU(x)) g

/-- The translation of `L²(C_F)` at the logarithmic coordinate zero is the identity. -/
theorem sectionL2Translation_zero (τ : ℝ≥0ˣ →ₜ* C𝔽) (g : H𝔽) :
    sectionL2Translation τ 0 g = g :=
  leftTranslationL2_one μ𝔽 (τ expU((0 : ℝ))) (by rw [expUnits_zero_sectionL2, map_one]) g

/-- The translations of `L²(C_F)` along the section form a one-parameter group. -/
theorem sectionL2Translation_add (τ : ℝ≥0ˣ →ₜ* C𝔽) (x y : ℝ) (g : H𝔽) :
    sectionL2Translation τ (x + y) g = sectionL2Translation τ x (sectionL2Translation τ y g) :=
  leftTranslationL2_mul μ𝔽 (τ expU(x)) (τ expU(y)) (τ expU(x + y))
    (by rw [expUnits_add_sectionL2, map_mul]) g

/-- The translations of `L²(C_F)` along the section preserve the norm. -/
theorem norm_sectionL2Translation (τ : ℝ≥0ˣ →ₜ* C𝔽) (x : ℝ) (g : H𝔽) :
    ‖sectionL2Translation τ x g‖ = ‖g‖ :=
  norm_leftTranslationL2 μ𝔽 (τ expU(x)) g

/-- The translates of a vector of `L²(C_F)` along the section depend continuously on the
logarithmic coordinate. -/
theorem continuous_sectionL2Translation (τ : ℝ≥0ˣ →ₜ* C𝔽) (g : H𝔽) :
    Continuous fun x : ℝ ↦ sectionL2Translation τ x g :=
  continuous_leftTranslationL2 μ𝔽 (fun x ↦ τ expU(x))
    (τ.continuous.comp continuous_expUnits_sectionL2) g

/-- The translations of `L²(C_F)` along the section are unitary: the adjoint of the translation
at `x` is the translation at `-x`. -/
theorem inner_sectionL2Translation_left (τ : ℝ≥0ˣ →ₜ* C𝔽) (x : ℝ) (f g : H𝔽) :
    ⟪sectionL2Translation τ x f, g⟫_ℂ = ⟪f, sectionL2Translation τ (-x) g⟫_ℂ :=
  inner_unitary_group_apply_left (fun x ↦ sectionL2Translation τ x)
    (sectionL2Translation_zero τ) (sectionL2Translation_add τ) (norm_sectionL2Translation τ)
    x f g

end Translation

section Laplace

/-- For a rate `c > 0` the Laplace transform of the translations of `L²(C_F)` along the section
in the forward direction is a bounded operator: it is the integral of the damped forward orbit,
and its norm is at most `c⁻¹`. -/
theorem exists_sectionL2ForwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽) {c : ℝ} (hc : 0 < c) :
    ∃ P : H𝔽 →L[ℂ] H𝔽,
      (∀ g, P g = ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • sectionL2Translation τ x g) ∧
      ∀ g, ‖P g‖ ≤ c⁻¹ * ‖g‖ :=
  exists_laplace_clm_of_contraction (fun x ↦ sectionL2Translation τ x)
    (fun x _ g ↦ (norm_sectionL2Translation τ x g).le) (continuous_sectionL2Translation τ) hc

/-- For a rate `c > 0` the Laplace transform of the translations of `L²(C_F)` along the section
in the backward direction is a bounded operator: it is the integral of the damped backward
orbit, and its norm is at most `c⁻¹`. -/
theorem exists_sectionL2BackwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽) {c : ℝ} (hc : 0 < c) :
    ∃ Q : H𝔽 →L[ℂ] H𝔽,
      (∀ g, Q g = ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • sectionL2Translation τ (-x) g) ∧
      ∀ g, ‖Q g‖ ≤ c⁻¹ * ‖g‖ :=
  exists_laplace_clm_of_contraction (fun x ↦ sectionL2Translation τ (-x))
    (fun x _ g ↦ (norm_sectionL2Translation τ (-x) g).le)
    (fun g ↦ (continuous_sectionL2Translation τ g).comp continuous_neg) hc

/-- Reconstruction: the forward Laplace transform at the rate `c` of the translations of the
unweighted space `L²(C_F)` along a one-parameter subgroup of the idele classes,
`g ↦ ∫ x in Ioi 0, exp (-c x) • U x g`. It is not in the paper. It is the operator `P_c` of the
positivity step of the argument for Theorem 10.4.2.1 posted on #7405, convolution along the
section with the one-sided exponential, on the space where the translations are unitary. -/
def sectionL2ForwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽) {c : ℝ} (hc : 0 < c) : H𝔽 →L[ℂ] H𝔽 :=
  (exists_sectionL2ForwardLaplace τ hc).choose

/-- Reconstruction: the backward Laplace transform at the rate `c` of the translations of the
unweighted space `L²(C_F)` along a one-parameter subgroup of the idele classes,
`g ↦ ∫ x in Ioi 0, exp (-c x) • U (-x) g`. It is not in the paper. It is convolution along the
section with the reflection of the one-sided exponential, the adjoint of
`sectionL2ForwardLaplace`, in the positivity step of the argument for Theorem 10.4.2.1 posted
on #7405. -/
def sectionL2BackwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽) {c : ℝ} (hc : 0 < c) : H𝔽 →L[ℂ] H𝔽 :=
  (exists_sectionL2BackwardLaplace τ hc).choose

/-- The forward Laplace transform on `L²(C_F)` is the integral of the damped forward orbit. -/
theorem sectionL2ForwardLaplace_apply (τ : ℝ≥0ˣ →ₜ* C𝔽) {c : ℝ} (hc : 0 < c) (g : H𝔽) :
    sectionL2ForwardLaplace τ hc g =
      ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • sectionL2Translation τ x g :=
  (exists_sectionL2ForwardLaplace τ hc).choose_spec.1 g

/-- The backward Laplace transform on `L²(C_F)` is the integral of the damped backward
orbit. -/
theorem sectionL2BackwardLaplace_apply (τ : ℝ≥0ˣ →ₜ* C𝔽) {c : ℝ} (hc : 0 < c) (g : H𝔽) :
    sectionL2BackwardLaplace τ hc g =
      ∫ x in Ioi (0 : ℝ), Real.exp (-c * x) • sectionL2Translation τ (-x) g :=
  (exists_sectionL2BackwardLaplace τ hc).choose_spec.1 g

/-- The damped forward orbit of a vector of `L²(C_F)` is integrable. -/
theorem integrableOn_sectionL2ForwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽) {c : ℝ} (hc : 0 < c) (g : H𝔽) :
    IntegrableOn (fun x ↦ Real.exp (-c * x) • sectionL2Translation τ x g) (Ioi 0) :=
  integrableOn_exp_smul_orbit (fun x ↦ sectionL2Translation τ x)
    (fun x _ g ↦ (norm_sectionL2Translation τ x g).le) (continuous_sectionL2Translation τ) hc
    g 0 le_rfl

/-- The damped backward orbit of a vector of `L²(C_F)` is integrable. -/
theorem integrableOn_sectionL2BackwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽) {c : ℝ} (hc : 0 < c)
    (g : H𝔽) :
    IntegrableOn (fun x ↦ Real.exp (-c * x) • sectionL2Translation τ (-x) g) (Ioi 0) :=
  integrableOn_exp_smul_orbit (fun x ↦ sectionL2Translation τ (-x))
    (fun x _ g ↦ (norm_sectionL2Translation τ (-x) g).le)
    (fun g ↦ (continuous_sectionL2Translation τ g).comp continuous_neg) hc g 0 le_rfl

/-- The forward Laplace transform on `L²(C_F)` at the rate `c` is bounded by `c⁻¹` on every
vector. -/
theorem norm_sectionL2ForwardLaplace_apply_le (τ : ℝ≥0ˣ →ₜ* C𝔽) {c : ℝ} (hc : 0 < c)
    (g : H𝔽) : ‖sectionL2ForwardLaplace τ hc g‖ ≤ c⁻¹ * ‖g‖ :=
  (exists_sectionL2ForwardLaplace τ hc).choose_spec.2 g

/-- The backward Laplace transform on `L²(C_F)` at the rate `c` is bounded by `c⁻¹` on every
vector. -/
theorem norm_sectionL2BackwardLaplace_apply_le (τ : ℝ≥0ˣ →ₜ* C𝔽) {c : ℝ} (hc : 0 < c)
    (g : H𝔽) : ‖sectionL2BackwardLaplace τ hc g‖ ≤ c⁻¹ * ‖g‖ :=
  (exists_sectionL2BackwardLaplace τ hc).choose_spec.2 g

/-- The forward Laplace transform on `L²(C_F)` at the rate `c` has operator norm at most
`c⁻¹`. -/
theorem norm_sectionL2ForwardLaplace_le (τ : ℝ≥0ˣ →ₜ* C𝔽) {c : ℝ} (hc : 0 < c) :
    ‖sectionL2ForwardLaplace τ hc‖ ≤ c⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le)
    (norm_sectionL2ForwardLaplace_apply_le τ hc)

/-- The backward Laplace transform on `L²(C_F)` at the rate `c` has operator norm at most
`c⁻¹`. -/
theorem norm_sectionL2BackwardLaplace_le (τ : ℝ≥0ˣ →ₜ* C𝔽) {c : ℝ} (hc : 0 < c) :
    ‖sectionL2BackwardLaplace τ hc‖ ≤ c⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hc.le)
    (norm_sectionL2BackwardLaplace_apply_le τ hc)

end Laplace

section Accretive

/-- The forward Laplace transform `P` on `L²(C_F)` at the rate `c` is accretive:
`c * ‖P g‖ ^ 2 ≤ re ⟪g, P g⟫`. -/
theorem mul_norm_sq_sectionL2ForwardLaplace_le_re_inner (τ : ℝ≥0ˣ →ₜ* C𝔽) {c : ℝ}
    (hc : 0 < c) (g : H𝔽) :
    c * ‖sectionL2ForwardLaplace τ hc g‖ ^ 2 ≤ (⟪g, sectionL2ForwardLaplace τ hc g⟫_ℂ).re := by
  rw [sectionL2ForwardLaplace_apply]
  exact mul_norm_sq_laplace_semigroup_le_re_inner (fun x ↦ sectionL2Translation τ x)
    (sectionL2Translation_zero τ) (fun x y _ _ w ↦ sectionL2Translation_add τ x y w)
    (fun x _ w ↦ (norm_sectionL2Translation τ x w).le) (continuous_sectionL2Translation τ) hc g

/-- The backward Laplace transform `Q` on `L²(C_F)` at the rate `c` is accretive:
`c * ‖Q g‖ ^ 2 ≤ re ⟪g, Q g⟫`. -/
theorem mul_norm_sq_sectionL2BackwardLaplace_le_re_inner (τ : ℝ≥0ˣ →ₜ* C𝔽) {c : ℝ}
    (hc : 0 < c) (g : H𝔽) :
    c * ‖sectionL2BackwardLaplace τ hc g‖ ^ 2 ≤
      (⟪g, sectionL2BackwardLaplace τ hc g⟫_ℂ).re := by
  rw [sectionL2BackwardLaplace_apply]
  exact mul_norm_sq_backward_laplace_unitary_group_le_re_inner
    (fun x ↦ sectionL2Translation τ x) (sectionL2Translation_zero τ)
    (sectionL2Translation_add τ) (norm_sectionL2Translation τ)
    (continuous_sectionL2Translation τ) hc g

/-- The adjoint of the forward Laplace transform on `L²(C_F)` is the backward Laplace transform
at the same rate. -/
theorem adjoint_sectionL2ForwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽) {c : ℝ} (hc : 0 < c) :
    ContinuousLinearMap.adjoint (sectionL2ForwardLaplace τ hc) = sectionL2BackwardLaplace τ hc :=
  adjoint_laplace_unitary_group (fun x ↦ sectionL2Translation τ x)
    (sectionL2Translation_zero τ) (sectionL2Translation_add τ) (norm_sectionL2Translation τ)
    (continuous_sectionL2Translation τ) hc _ _ (sectionL2ForwardLaplace_apply τ hc)
    (sectionL2BackwardLaplace_apply τ hc)

/-- The adjoint of the backward Laplace transform on `L²(C_F)` is the forward Laplace transform
at the same rate. -/
theorem adjoint_sectionL2BackwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽) {c : ℝ} (hc : 0 < c) :
    ContinuousLinearMap.adjoint (sectionL2BackwardLaplace τ hc) = sectionL2ForwardLaplace τ hc :=
  adjoint_backward_laplace_unitary_group (fun x ↦ sectionL2Translation τ x)
    (sectionL2Translation_zero τ) (sectionL2Translation_add τ) (norm_sectionL2Translation τ)
    (continuous_sectionL2Translation τ) hc _ _ (sectionL2ForwardLaplace_apply τ hc)
    (sectionL2BackwardLaplace_apply τ hc)

/-- The forward Laplace transform on `L²(C_F)` at one rate commutes with the backward Laplace
transform at another rate. -/
theorem sectionL2ForwardLaplace_comm_backwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽) {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (g : H𝔽) :
    sectionL2ForwardLaplace τ hc₁ (sectionL2BackwardLaplace τ hc₂ g) =
      sectionL2BackwardLaplace τ hc₂ (sectionL2ForwardLaplace τ hc₁ g) :=
  laplace_unitary_group_comm (fun x ↦ sectionL2Translation τ x) (sectionL2Translation_add τ)
    (norm_sectionL2Translation τ) (continuous_sectionL2Translation τ) hc₁ hc₂ _ _
    (sectionL2ForwardLaplace_apply τ hc₁) (sectionL2BackwardLaplace_apply τ hc₂) g

/-- The backward and the forward Laplace transform on `L²(C_F)` at the same rate have the same
norm on every vector. -/
theorem norm_sectionL2BackwardLaplace_apply (τ : ℝ≥0ˣ →ₜ* C𝔽) {c : ℝ} (hc : 0 < c) (g : H𝔽) :
    ‖sectionL2BackwardLaplace τ hc g‖ = ‖sectionL2ForwardLaplace τ hc g‖ :=
  norm_backward_laplace_unitary_group (fun x ↦ sectionL2Translation τ x)
    (sectionL2Translation_zero τ) (sectionL2Translation_add τ) (norm_sectionL2Translation τ)
    (continuous_sectionL2Translation τ) hc _ _ (sectionL2ForwardLaplace_apply τ hc)
    (sectionL2BackwardLaplace_apply τ hc) g

/-- The adjoint of the forward Laplace transform on `L²(C_F)` is no larger than the transform
on any vector. -/
theorem norm_adjoint_sectionL2ForwardLaplace_apply_le (τ : ℝ≥0ˣ →ₜ* C𝔽) {c : ℝ} (hc : 0 < c)
    (g : H𝔽) :
    ‖ContinuousLinearMap.adjoint (sectionL2ForwardLaplace τ hc) g‖ ≤
      ‖sectionL2ForwardLaplace τ hc g‖ := by
  rw [adjoint_sectionL2ForwardLaplace]
  exact (norm_sectionL2BackwardLaplace_apply τ hc g).le

/-- The adjoint of the backward Laplace transform on `L²(C_F)` is no larger than the transform
on any vector. -/
theorem norm_adjoint_sectionL2BackwardLaplace_apply_le (τ : ℝ≥0ˣ →ₜ* C𝔽) {c : ℝ} (hc : 0 < c)
    (g : H𝔽) :
    ‖ContinuousLinearMap.adjoint (sectionL2BackwardLaplace τ hc) g‖ ≤
      ‖sectionL2BackwardLaplace τ hc g‖ := by
  rw [adjoint_sectionL2BackwardLaplace]
  exact (norm_sectionL2BackwardLaplace_apply τ hc g).ge

/-- The forward Laplace transform `P` on `L²(C_F)` at a rate `c₁` and the backward Laplace
transform `Q` at a rate `c₂` satisfy the four hypotheses of
`two_thirds_mul_sum_le_re_sum_inner_jet_add`: both are accretive, with the constants `c₁` and
`c₂`, and the adjoint of each is no larger than the operator on any vector. -/
theorem sectionL2Laplace_accretive (τ : ℝ≥0ˣ →ₜ* C𝔽) {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂) :
    (∀ g, c₁ * ‖sectionL2ForwardLaplace τ hc₁ g‖ ^ 2 ≤
      (⟪g, sectionL2ForwardLaplace τ hc₁ g⟫_ℂ).re) ∧
    (∀ g, c₂ * ‖sectionL2BackwardLaplace τ hc₂ g‖ ^ 2 ≤
      (⟪g, sectionL2BackwardLaplace τ hc₂ g⟫_ℂ).re) ∧
    (∀ g, ‖ContinuousLinearMap.adjoint (sectionL2ForwardLaplace τ hc₁) g‖ ≤
      ‖sectionL2ForwardLaplace τ hc₁ g‖) ∧
    ∀ g, ‖ContinuousLinearMap.adjoint (sectionL2BackwardLaplace τ hc₂) g‖ ≤
      ‖sectionL2BackwardLaplace τ hc₂ g‖ :=
  ⟨mul_norm_sq_sectionL2ForwardLaplace_le_re_inner τ hc₁,
    mul_norm_sq_sectionL2BackwardLaplace_le_re_inner τ hc₂,
    norm_adjoint_sectionL2ForwardLaplace_apply_le τ hc₁,
    norm_adjoint_sectionL2BackwardLaplace_apply_le τ hc₂⟩

/-- Accretivity on jets of the forward and backward Laplace transforms `P` and `Q` on
`L²(C_F)`, at rates `c₁` and `c₂` that are at least four times the highest order `k`: for
vectors `g 0, …, g k`, two thirds of `∑ j, (c₁ * ‖P (g j)‖ ^ 2 + c₂ * ‖Q (g j)‖ ^ 2)` is at most
the real part of the triangular form with the entries `j ! / i ! • P ^ (j - i + 1)` and
`(-1) ^ (j - i) j ! / i ! • Q ^ (j - i + 1)`. This is
`two_thirds_mul_sum_le_re_sum_inner_jet_add` for these two operators. -/
theorem two_thirds_mul_sum_le_re_sum_inner_jet_sectionL2Laplace (τ : ℝ≥0ˣ →ₜ* C𝔽)
    {c₁ c₂ : ℝ} (k : ℕ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hk₁ : 4 * (k : ℝ) ≤ c₁)
    (hk₂ : 4 * (k : ℝ) ≤ c₂) (g : ℕ → H𝔽) :
    2 / 3 * ∑ j ∈ Finset.range (k + 1), (c₁ * ‖sectionL2ForwardLaplace τ hc₁ (g j)‖ ^ 2 +
        c₂ * ‖sectionL2BackwardLaplace τ hc₂ (g j)‖ ^ 2) ≤
      (∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (j + 1), (j.descFactorial (j - i) : ℂ) *
        (⟪g j, (sectionL2ForwardLaplace τ hc₁ ^ (j - i + 1)) (g i)⟫_ℂ +
          (-1) ^ (j - i) * ⟪g j, (sectionL2BackwardLaplace τ hc₂ ^ (j - i + 1)) (g i)⟫_ℂ)).re :=
  two_thirds_mul_sum_le_re_sum_inner_jet_add (sectionL2ForwardLaplace τ hc₁)
    (sectionL2BackwardLaplace τ hc₂) k hc₁ hc₂ hk₁ hk₂
    (mul_norm_sq_sectionL2ForwardLaplace_le_re_inner τ hc₁)
    (mul_norm_sq_sectionL2BackwardLaplace_le_re_inner τ hc₂)
    (norm_adjoint_sectionL2ForwardLaplace_apply_le τ hc₁)
    (norm_adjoint_sectionL2BackwardLaplace_apply_le τ hc₂) g

end Accretive

end RiemannMasullo.Isolated
