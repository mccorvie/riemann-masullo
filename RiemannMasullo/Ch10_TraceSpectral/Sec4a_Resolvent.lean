module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppC_LCTVS.Sec3b_HilbertSchmidtProduct
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Real
import Mathlib.MeasureTheory.Integral.ExpDecay

/-! # Laplace transforms of the translations along a norm section on the strip space

Masullo, §10.4.2, pp. 459–464. This file belongs to the open statement
`Isolated.spectralStripConvolution_hilbertSchmidt_of_le_one` (#7405). It formalizes step 2 of the
real-variable argument posted there, on the objects of the library. Nothing imports it, and
nothing in it depends on the two unproved statements of `Sec4a_Isolated.lean`.

Let `τ` be a continuous section of the idele class norm, `W` the weighted space of the strip of
half-width `α` at order `s ≥ 0`, and `T` its translations. Along the section the translations
grow at most like `exp (α |x|) (1 + |x|) ^ (s / 2)` in the logarithmic coordinate `x`, so for a
rate `L > α` their one-sided Laplace transforms

* `P⁺ u = ∫ x in Ioi 0, exp (-L x) • T (τ (exp x)) u` (`spectralStripForwardLaplace`),
* `P⁻ u = ∫ x in Ioi 0, exp (-L x) • T (τ (exp (-x))) u` (`spectralStripBackwardLaplace`)

are bounded operators of `W`. In the notation of the argument, `P⁺` is `P_L`, convolution along
the section with `p_L`, and `P⁻` is convolution with the reflection of `p_L`. Their sum is
convolution with `exp (-L |x|)`, the operator `R`. None of the three is the action of a
compactly supported test.

## Main statements

* `norm_hardySobolevTranslation_section_le`, `continuous_hardySobolevTranslation_section`: the
  growth bound and the strong continuity of the translations along the section.
* `exists_spectralStripForwardLaplace`, `exists_spectralStripBackwardLaplace`: the transforms
  are bounded, with norm at most `∫ x in Ioi 0, exp (-(L - α) x) (1 + x) ^ (s / 2)`.
* `spectralSobolevPairing_translation_zeroJet`: the translated moments. The pairing of a
  translate with a jet of order `k` is a binomial combination of the pairings with the jets of
  orders at most `k` at the same point.
* `spectralStripJet_pairing_forwardLaplace`, `spectralStripJet_pairing_backwardLaplace`:
  triangularity on the strip jets. If `u` pairs to zero with the jets of lower order at the
  point of a jet, the transforms multiply its pairing with that jet by `(L - z)⁻¹` and
  `(L + z)⁻¹`. Here `z = b + (t + θ) i` for a jet with real offset `b` and ordinate `t`, and `θ`
  is the frequency of the base character of the jet along the section
  (`exists_section_character_frequency`); `θ = 0` when the base character is trivial on the
  section, and `exists_spectralBasepointChoice_section` gives such base characters.
* `spectralStripJet_pairing_forwardLaplace_add_backwardLaplace`: the diagonal
  `2 L / (L ^ 2 - z ^ 2)` of `R`.
* `spectralStripForwardLaplace_mem_globalThetaSobolev`,
  `spectralStripBackwardLaplace_mem_globalThetaSobolev`: both transforms preserve the closed
  theta subspace, so they act on the strip quotient.
* `exists_bruhatCompactSupport_section_laplace`: every compactly supported Bruhat test `φ` is
  the convolution along the section of `exp (-L x)`, `x > 0`, with a test, namely `L φ` minus
  the derivative of `φ` along the section. This is `φ = (φ' + L φ) ∗ p_L` of step 6.
* `exists_hardySobolevTestAction_eq_forwardLaplace_comp`,
  `exists_spectralConvolution_eq_forwardLaplace_comp`: hence the action of every test, on `W`
  and on the strip quotient, is `P⁺` after the action of another test. The descended `P⁺` is
  bounded but not Hilbert–Schmidt on the whole quotient in general, so this gives a product of
  two Hilbert–Schmidt operators only on each component of the norm-one group.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
variable {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hI" => (neg_nonpos.mpr hα).trans hα
local notation "W" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s
local notation "T(" g ")" => hardySobolevTranslation μ𝔽 m𝔽 (-α) α s hI hs g
local notation "expU(" x ")" =>
  (Units.mk0 (Real.exp x).toNNReal (Real.toNNReal_pos.mpr (Real.exp_pos x)).ne' : ℝ≥0ˣ)

section Section

/-- The exponential is continuous into the positive real units. -/
private theorem continuous_expUnits : Continuous fun x : ℝ ↦ expU(x) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact continuous_real_toNNReal.comp Real.continuous_exp
  · have h : (fun x : ℝ ↦ ((expU(x)⁻¹ : ℝ≥0ˣ) : ℝ≥0)) = fun x : ℝ ↦ (Real.exp (-x)).toNNReal := by
      funext x
      rw [Units.val_inv_eq_inv_val, Units.val_mk0, Real.exp_neg, Real.toNNReal_inv]
    rw [h]
    exact continuous_real_toNNReal.comp (Real.continuous_exp.comp continuous_neg)

/-- The exponential into the positive real units is additive-to-multiplicative. -/
private theorem expUnits_add (x y : ℝ) : expU(x + y) = expU(x) * expU(y) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, Real.exp_add,
    Real.toNNReal_mul (Real.exp_pos x).le]

/-- The exponential into the positive real units sends zero to one. -/
private theorem expUnits_zero : expU((0 : ℝ)) = 1 := by
  apply Units.ext
  rw [Units.val_mk0, Real.exp_zero, Real.toNNReal_one, Units.val_one]

/-- The logarithm of the norm along a norm section is the logarithmic coordinate. -/
private theorem logIdeleClassNorm_section (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) (x : ℝ) :
    logIdeleClassNorm F (τ expU(x)) = x := by
  change Real.log ((ideleClassNorm F (τ expU(x))).val : ℝ) = x
  rw [hτ expU(x), Units.val_mk0, Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]

/-- Paper: Lemma 9.3.1.5, p. 421, along a section of the idele class norm. The translation of
the strip space by the point of the section at logarithmic coordinate `x` has operator norm at
most `exp (α |x|) (1 + |x|) ^ (s / 2)`.
Deviation: The paper does not single out a section; this is the bound of the lemma in the
coordinate of the section. -/
theorem norm_hardySobolevTranslation_section_le (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) (x : ℝ) :
    ‖T(τ expU(x))‖ ≤ Real.exp (α * |x|) * (1 + |x|) ^ (s / 2) := by
  have h := norm_hardySobolevTranslation_le μ𝔽 m𝔽 (-α) α s hI hs (τ expU(x))
  have hlog : Real.log ((m𝔽 (τ expU(x))).val : ℝ) = x := logIdeleClassNorm_section τ hτ x
  beta_reduce at h
  rw [hlog] at h
  refine h.trans_eq ?_
  congr 1
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, max_eq_right]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · rw [abs_of_nonpos hx, max_eq_left]
    · congr 1
      ring
    · exact Real.exp_le_exp.mpr (by nlinarith)

/-- Paper: Lemma 9.3.1.5, p. 421, along a section of the idele class norm. The translate of a
vector of the strip space by the point of the section at logarithmic coordinate `x` has norm at
most `exp (α |x|) (1 + |x|) ^ (s / 2)` times the norm of the vector. -/
theorem norm_hardySobolevTranslation_section_apply_le (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) (x : ℝ) (u : W) :
    ‖T(τ expU(x)) u‖ ≤ Real.exp (α * |x|) * (1 + |x|) ^ (s / 2) * ‖u‖ :=
  ((T(τ expU(x))).le_opNorm u).trans (mul_le_mul_of_nonneg_right
    (norm_hardySobolevTranslation_section_le hα hs τ hτ x) (norm_nonneg u))

/-- Paper: Definition 9.3.1.1, p. 419, along a section of the idele class norm. The translates
of a vector of the strip space along the section depend continuously on the logarithmic
coordinate. -/
theorem continuous_hardySobolevTranslation_section (τ : ℝ≥0ˣ →ₜ* C𝔽) (u : W) :
    Continuous fun x : ℝ ↦ T(τ expU(x)) u :=
  (exists_hardySobolevTranslation μ𝔽 m𝔽 (-α) α s hI hs).choose_spec.2.comp
    ((τ.continuous.comp continuous_expUnits).prodMk continuous_const)

end Section

section Abstract

/-- A real power of `1 + x` times a decaying exponential is integrable on the positive
half-line. -/
private theorem integrableOn_exp_neg_mul_one_add_rpow {c : ℝ} (hc : 0 < c) (p : ℝ) :
    IntegrableOn (fun x : ℝ ↦ Real.exp (-c * x) * (1 + x) ^ p) (Ioi 0) := by
  have hc2 : 0 < c / 2 := by positivity
  refine integrable_of_isBigO_exp_neg hc2 ?_ ?_
  · refine ContinuousOn.mul (by fun_prop)
      (ContinuousOn.rpow_const (by fun_prop) fun x hx ↦ Or.inl ?_)
    have h0 : (0 : ℝ) ≤ x := hx
    positivity
  · have h0 : Tendsto
        (fun x : ℝ ↦ Real.exp (c / 2) * ((1 + x) ^ p * Real.exp (-(c / 2) * (1 + x))))
        atTop (𝓝 (Real.exp (c / 2) * 0)) :=
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p (c / 2) hc2).comp
        (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)).const_mul _
    have h1 : (fun x : ℝ ↦ Real.exp (-c * x) * (1 + x) ^ p) = fun x ↦
        (Real.exp (c / 2) * ((1 + x) ^ p * Real.exp (-(c / 2) * (1 + x)))) *
          Real.exp (-(c / 2) * x) := by
      funext x
      have h : Real.exp (-c * x) =
          Real.exp (c / 2) * Real.exp (-(c / 2) * (1 + x)) * Real.exp (-(c / 2) * x) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [h]
      ring
    rw [h1]
    simpa using (h0.isBigO_one ℝ).mul
      (Asymptotics.isBigO_refl (fun x : ℝ ↦ Real.exp (-(c / 2) * x)) atTop)

/-- The one-sided Laplace transform of a strongly continuous family of operators of a Banach
space that grows at most like `exp (a x) (1 + x) ^ p` is, at every rate `L > a`, a bounded
operator, with the integral of the majorant as a bound for its norm. -/
private theorem exists_laplace_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (U : ℝ → E →L[ℂ] E) (hcont : ∀ w, Continuous fun x ↦ U x w)
    {a p L : ℝ} (hL : a < L) (hU : ∀ x, 0 ≤ x → ‖U x‖ ≤ Real.exp (a * x) * (1 + x) ^ p) :
    ∃ P : E →L[ℂ] E,
      (∀ w, IntegrableOn (fun x ↦ Real.exp (-L * x) • U x w) (Ioi 0) ∧
        P w = ∫ x in Ioi 0, Real.exp (-L * x) • U x w) ∧
      ‖P‖ ≤ ∫ x in Ioi 0, Real.exp (-(L - a) * x) * (1 + x) ^ p := by
  have hmaj := integrableOn_exp_neg_mul_one_add_rpow (sub_pos.mpr hL) p
  have hbound (w : E) (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      ‖Real.exp (-L * x) • U x w‖ ≤ Real.exp (-(L - a) * x) * (1 + x) ^ p * ‖w‖ := by
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-L * x) * ‖U x w‖
        ≤ Real.exp (-L * x) * (Real.exp (a * x) * (1 + x) ^ p * ‖w‖) :=
          mul_le_mul_of_nonneg_left (((U x).le_opNorm w).trans
            (mul_le_mul_of_nonneg_right (hU x (le_of_lt hx)) (norm_nonneg w))) (Real.exp_pos _).le
      _ = Real.exp (-(L - a) * x) * (1 + x) ^ p * ‖w‖ := by
          rw [← mul_assoc, ← mul_assoc, ← Real.exp_add]
          congr 3
          ring
  have hint (w : E) : IntegrableOn (fun x ↦ Real.exp (-L * x) • U x w) (Ioi 0) :=
    Integrable.mono' (hmaj.mul_const ‖w‖)
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
        (hcont w)).aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ hbound w x hx)
  let P₀ : E →ₗ[ℂ] E :=
    { toFun := fun w ↦ ∫ x in Ioi 0, Real.exp (-L * x) • U x w
      map_add' := fun v w ↦ by
        simp only [map_add, smul_add]
        exact integral_add (hint v) (hint w)
      map_smul' := fun c w ↦ by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        exact integral_congr_ae (.of_forall fun x ↦ smul_comm _ _ _) }
  refine ⟨P₀.mkContinuous (∫ x in Ioi 0, Real.exp (-(L - a) * x) * (1 + x) ^ p) fun w ↦ ?_,
    fun w ↦ ⟨hint w, rfl⟩, LinearMap.mkContinuous_norm_le _ ?_ _⟩
  · calc ‖∫ x in Ioi 0, Real.exp (-L * x) • U x w‖
        ≤ ∫ x in Ioi 0, Real.exp (-(L - a) * x) * (1 + x) ^ p * ‖w‖ :=
          norm_integral_le_of_norm_le (hmaj.mul_const ‖w‖)
            ((ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ hbound w x hx)
      _ = (∫ x in Ioi 0, Real.exp (-(L - a) * x) * (1 + x) ^ p) * ‖w‖ := integral_mul_const _ _
  · exact setIntegral_nonneg measurableSet_Ioi fun x hx ↦
      mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith [mem_Ioi.mp hx]) _)

/-- A continuous functional that is multiplied by `exp (z x)` along a family of vectors takes
the value `(L - z)⁻¹` times the constant on its Laplace transform at a rate `L > re z`. -/
private theorem laplace_apply_of_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (Λ : E →L[ℂ] ℂ) (f : ℝ → E) {L : ℝ} {z c : ℂ} (hz : z.re < L)
    (hf : IntegrableOn (fun x ↦ Real.exp (-L * x) • f x) (Ioi 0))
    (hΛ : ∀ x : ℝ, Λ (f x) = Complex.exp (z * x) * c) :
    Λ (∫ x in Ioi 0, Real.exp (-L * x) • f x) = ((L : ℂ) - z)⁻¹ * c := by
  rw [← Λ.integral_comp_comm hf]
  have h (x : ℝ) : Λ (Real.exp (-L * x) • f x) = Complex.exp ((z - L) * x) * c := by
    rw [Λ.map_smul_of_tower, hΛ, Complex.real_smul, Complex.ofReal_exp, ← mul_assoc,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [h]
  have hre : (z - (L : ℂ)).re < 0 := by simpa using hz
  rw [integral_mul_const, integral_exp_mul_complex_Ioi hre 0, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, neg_div, ← div_neg, neg_sub, one_div]

/-- On a group with a left-invariant measure, the product integral of a left translate with a
second function moves the translation to the second function. -/
private theorem integral_translate_mul {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (h : G) (a b f J : G → ℂ)
    (ha : a =ᵐ[μ] fun x ↦ f (h⁻¹ * x)) (hb : b =ᵐ[μ] J) :
    ∫ x, a x * b x ∂μ = ∫ y, f y * J (h * y) ∂μ := by
  have h1 : (fun x ↦ a x * b x) =ᵐ[μ] fun x ↦ f (h⁻¹ * x) * J x := by
    filter_upwards [ha, hb] with x hx hy
    rw [hx, hy]
  rw [integral_congr_ae h1, ← integral_mul_left_eq_self (μ := μ) (fun x ↦ f (h⁻¹ * x) * J x) h]
  simp only [inv_mul_cancel_left]

/-- The Laplace transform along a path of an integrated action. Let `ρ` be a strongly
continuous action of a group with a left-invariant measure, `γ` a continuous path whose
operators are dominated by `M`, and `φ`, `ψ` continuous compactly supported kernels such that
`φ` is the convolution of `ψ` along the path with `exp (-L x)`, `x > 0`. Then the Laplace
transform along the path of the vector integrated against `ψ` is the vector integrated against
`φ`. The proof pairs with a continuous functional and exchanges two scalar integrals. -/
private theorem laplace_integral_smul_orbit {G E : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (ρ : G →* (E →L[ℂ] E)) (hρ : ∀ w, Continuous fun g ↦ ρ g w)
    (γ : ℝ → G) (hγ : Continuous γ) {φ ψ : G → ℂ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) {L : ℝ}
    {M : ℝ → ℝ} (hM : ∀ x, 0 < x → ‖ρ (γ x)‖ ≤ M x)
    (hMint : IntegrableOn (fun x ↦ Real.exp (-L * x) * M x) (Ioi 0))
    (hconv : ∀ g, ∫ x in Ioi 0, Real.exp (-L * x) • ψ ((γ x)⁻¹ * g) = φ g) (u : E) :
    ∫ x in Ioi 0, Real.exp (-L * x) • ρ (γ x) (∫ g, ψ g • ρ g u ∂μ) =
      ∫ g, φ g • ρ g u ∂μ := by
  have hψu : Integrable (fun g ↦ ψ g • ρ g u) μ :=
    (hψ.smul (hρ u)).integrable_of_hasCompactSupport hψc.smul_right
  have hφu : Integrable (fun g ↦ φ g • ρ g u) μ :=
    (hφ.smul (hρ u)).integrable_of_hasCompactSupport hφc.smul_right
  have hψi : Integrable ψ μ := hψ.integrable_of_hasCompactSupport hψc
  set v : E := ∫ g, ψ g • ρ g u ∂μ with hv
  have hxv : IntegrableOn (fun x ↦ Real.exp (-L * x) • ρ (γ x) v) (Ioi 0) := by
    refine Integrable.mono' (hMint.mul_const ‖v‖) ?_ ?_
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
        ((hρ v).comp hγ)).aestronglyMeasurable
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ ?_
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_assoc]
      exact mul_le_mul_of_nonneg_left (((ρ (γ x)).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg v))) (Real.exp_pos _).le
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr fun Λ ↦ ?_
  rw [← Λ.integral_comp_comm hxv, ← Λ.integral_comp_comm hφu]
  obtain ⟨Cu, hCu⟩ := hψc.exists_bound_of_continuousOn (hρ u).continuousOn
  have hC' : ∀ k ∈ tsupport ψ, ‖ρ k u‖ ≤ max Cu 0 := fun k hk ↦
    (hCu k hk).trans (le_max_left _ _)
  let K : ℝ → G → ℂ := fun x g ↦ (Real.exp (-L * x) • ψ ((γ x)⁻¹ * g)) * Λ (ρ g u)
  have hKc : Continuous (Function.uncurry K) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).smul
      (hψ.comp ((hγ.comp continuous_fst).inv.mul continuous_snd))).mul
      (Λ.continuous.comp ((hρ u).comp continuous_snd))
  -- A pointwise bound for the kernel.
  have hKb (x : ℝ) (g : G) : ‖K x g‖ ≤
      Real.exp (-L * x) * ‖ρ (γ x)‖ * (‖Λ‖ * max Cu 0) * ‖ψ ((γ x)⁻¹ * g)‖ := by
    by_cases h0 : ψ ((γ x)⁻¹ * g) = 0
    · simp [K, h0]
    · have hg : ρ g u = ρ (γ x) (ρ ((γ x)⁻¹ * g) u) := by
        conv_lhs => rw [← mul_inv_cancel_left (γ x) g, map_mul, mul_apply_eq_comp]
      have h1 : ‖Λ (ρ g u)‖ ≤ ‖Λ‖ * (‖ρ (γ x)‖ * max Cu 0) := by
        refine (Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        rw [hg]
        exact ((ρ (γ x)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (hC' _ (subset_tsupport _ h0)) (norm_nonneg _))
      calc ‖K x g‖ = Real.exp (-L * x) * ‖ψ ((γ x)⁻¹ * g)‖ * ‖Λ (ρ g u)‖ := by
            simp only [K, norm_mul, norm_smul, Real.norm_eq_abs, Real.abs_exp]
        _ ≤ Real.exp (-L * x) * ‖ψ ((γ x)⁻¹ * g)‖ * (‖Λ‖ * (‖ρ (γ x)‖ * max Cu 0)) :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
        _ = _ := by ring
  have hKx (x : ℝ) : Integrable (fun g ↦ K x g) μ :=
    Integrable.mono' ((hψi.norm.comp_mul_left (γ x)⁻¹).const_mul
        (Real.exp (-L * x) * ‖ρ (γ x)‖ * (‖Λ‖ * max Cu 0)))
      (hKc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (.of_forall fun g ↦ hKb x g)
  have hshift (x : ℝ) : ∫ g, ‖ψ ((γ x)⁻¹ * g)‖ ∂μ = ∫ g, ‖ψ g‖ ∂μ :=
    integral_mul_left_eq_self (fun g ↦ ‖ψ g‖) (γ x)⁻¹
  have hKint : Integrable (Function.uncurry K) ((volume.restrict (Ioi (0 : ℝ))).prod μ) := by
    refine (integrable_prod_iff hKc.aestronglyMeasurable).mpr ⟨.of_forall hKx, ?_⟩
    refine Integrable.mono' (hMint.mul_const ((‖Λ‖ * max Cu 0) * ∫ g, ‖ψ g‖ ∂μ))
      hKc.aestronglyMeasurable.norm.integral_prod_right' ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ ?_
    rw [Real.norm_of_nonneg (integral_nonneg fun g ↦ norm_nonneg _)]
    calc ∫ g, ‖Function.uncurry K (x, g)‖ ∂μ
        ≤ ∫ g, Real.exp (-L * x) * ‖ρ (γ x)‖ * (‖Λ‖ * max Cu 0) * ‖ψ ((γ x)⁻¹ * g)‖ ∂μ :=
          integral_mono (hKx x).norm ((hψi.norm.comp_mul_left (γ x)⁻¹).const_mul _)
            fun g ↦ hKb x g
      _ = Real.exp (-L * x) * ‖ρ (γ x)‖ * ((‖Λ‖ * max Cu 0) * ∫ g, ‖ψ g‖ ∂μ) := by
          rw [integral_const_mul, hshift, mul_assoc]
      _ ≤ Real.exp (-L * x) * M x * ((‖Λ‖ * max Cu 0) * ∫ g, ‖ψ g‖ ∂μ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hM x hx) (Real.exp_pos _).le)
            (mul_nonneg (mul_nonneg (norm_nonneg _) (le_max_right _ _))
              (integral_nonneg fun g ↦ norm_nonneg _))
  -- The functional of the damped orbit is an integral of the kernel.
  have hA (x : ℝ) : Λ (Real.exp (-L * x) • ρ (γ x) v) = ∫ g, K x g ∂μ := by
    have h1 : Λ (ρ (γ x) v) = ∫ g, ψ g * Λ (ρ (γ x * g) u) ∂μ :=
      calc Λ (ρ (γ x) v) = (Λ.comp (ρ (γ x))) (∫ g, ψ g • ρ g u ∂μ) := rfl
        _ = ∫ g, (Λ.comp (ρ (γ x))) (ψ g • ρ g u) ∂μ :=
            ((Λ.comp (ρ (γ x))).integral_comp_comm hψu).symm
        _ = ∫ g, ψ g * Λ (ρ (γ x * g) u) ∂μ := integral_congr_ae (.of_forall fun g ↦ by
            change Λ (ρ (γ x) (ψ g • ρ g u)) = ψ g * Λ (ρ (γ x * g) u)
            rw [map_smul, map_smul, smul_eq_mul, map_mul, mul_apply_eq_comp])
    have h2 : ∫ g, ψ g * Λ (ρ (γ x * g) u) ∂μ = ∫ g, ψ ((γ x)⁻¹ * g) * Λ (ρ g u) ∂μ := by
      rw [← integral_mul_left_eq_self (μ := μ) (fun g ↦ ψ ((γ x)⁻¹ * g) * Λ (ρ g u)) (γ x)]
      simp only [inv_mul_cancel_left]
    rw [Λ.map_smul_of_tower, h1, h2, ← integral_smul]
    exact integral_congr_ae (.of_forall fun g ↦ (smul_mul_assoc _ _ _).symm)
  calc ∫ x in Ioi 0, Λ (Real.exp (-L * x) • ρ (γ x) v)
      = ∫ x in Ioi 0, ∫ g, K x g ∂μ := integral_congr_ae (.of_forall hA)
    _ = ∫ g, (∫ x in Ioi 0, K x g) ∂μ := integral_integral_swap hKint
    _ = ∫ g, Λ (φ g • ρ g u) ∂μ := integral_congr_ae (.of_forall fun g ↦ by
        change ∫ x in Ioi 0, (Real.exp (-L * x) • ψ ((γ x)⁻¹ * g)) * Λ (ρ g u) =
          Λ (φ g • ρ g u)
        rw [integral_mul_const, hconv g, map_smul, smul_eq_mul])

end Abstract

section Laplace

/-- For a rate `L` above the half-width of the strip, the Laplace transform of the translations
along a norm section in the direction of increasing norm is a bounded operator of the strip
space. The integral of each orbit converges, and the operator norm is at most the integral of
`exp (-(L - α) x) (1 + x) ^ (s / 2)` over the positive half-line. -/
theorem exists_spectralStripForwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) :
    ∃ P : W →L[ℂ] W,
      (∀ u, IntegrableOn (fun x ↦ Real.exp (-L * x) • T(τ expU(x)) u) (Ioi 0) ∧
        P u = ∫ x in Ioi 0, Real.exp (-L * x) • T(τ expU(x)) u) ∧
      ‖P‖ ≤ ∫ x in Ioi 0, Real.exp (-(L - α) * x) * (1 + x) ^ (s / 2) :=
  exists_laplace_clm (fun x ↦ T(τ expU(x)))
    (continuous_hardySobolevTranslation_section hα hs τ) hL fun x hx ↦ by
      simpa only [abs_of_nonneg hx] using norm_hardySobolevTranslation_section_le hα hs τ hτ x

/-- For a rate `L` above the half-width of the strip, the Laplace transform of the translations
along a norm section in the direction of decreasing norm is a bounded operator of the strip
space, with the same bound as the forward transform. -/
theorem exists_spectralStripBackwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) :
    ∃ P : W →L[ℂ] W,
      (∀ u, IntegrableOn (fun x ↦ Real.exp (-L * x) • T(τ expU(-x)) u) (Ioi 0) ∧
        P u = ∫ x in Ioi 0, Real.exp (-L * x) • T(τ expU(-x)) u) ∧
      ‖P‖ ≤ ∫ x in Ioi 0, Real.exp (-(L - α) * x) * (1 + x) ^ (s / 2) :=
  exists_laplace_clm (fun x ↦ T(τ expU(-x)))
    (fun u ↦ (continuous_hardySobolevTranslation_section hα hs τ u).comp continuous_neg) hL
    fun x hx ↦ by
      simpa only [abs_neg, abs_of_nonneg hx] using
        norm_hardySobolevTranslation_section_le hα hs τ hτ (-x)

/-- Reconstruction: the forward half of the operator `R` of step 2 of the argument for
Theorem 10.4.2.1 posted on #7405; it is not in the paper. It is the Laplace transform at the
rate `L` of the translations of the strip space along a section of the idele class norm, in the
direction of increasing norm: `u ↦ ∫ x in Ioi 0, exp (-L x) • T (τ (exp x)) u`. The sum with
`spectralStripBackwardLaplace` is convolution along the section with `exp (-L |x|)`. -/
def spectralStripForwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) : W →L[ℂ] W :=
  (exists_spectralStripForwardLaplace hα hs τ hτ hL).choose

/-- Reconstruction: the backward half of the operator `R` of step 2 of the argument for
Theorem 10.4.2.1 posted on #7405; it is not in the paper. It is the Laplace transform at the
rate `L` of the translations of the strip space along a section of the idele class norm, in the
direction of decreasing norm: `u ↦ ∫ x in Ioi 0, exp (-L x) • T (τ (exp (-x))) u`. -/
def spectralStripBackwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) : W →L[ℂ] W :=
  (exists_spectralStripBackwardLaplace hα hs τ hτ hL).choose

/-- The forward Laplace transform is the integral of the damped forward orbit. -/
theorem spectralStripForwardLaplace_apply (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) (u : W) :
    spectralStripForwardLaplace hα hs τ hτ hL u =
      ∫ x in Ioi 0, Real.exp (-L * x) • T(τ expU(x)) u :=
  ((exists_spectralStripForwardLaplace hα hs τ hτ hL).choose_spec.1 u).2

/-- The damped forward orbit of a vector of the strip space is integrable. -/
theorem integrableOn_spectralStripForwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) (u : W) :
    IntegrableOn (fun x ↦ Real.exp (-L * x) • T(τ expU(x)) u) (Ioi 0) :=
  ((exists_spectralStripForwardLaplace hα hs τ hτ hL).choose_spec.1 u).1

/-- The forward Laplace transform has operator norm at most the integral of
`exp (-(L - α) x) (1 + x) ^ (s / 2)` over the positive half-line. -/
theorem norm_spectralStripForwardLaplace_le (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) :
    ‖spectralStripForwardLaplace hα hs τ hτ hL‖ ≤
      ∫ x in Ioi 0, Real.exp (-(L - α) * x) * (1 + x) ^ (s / 2) :=
  (exists_spectralStripForwardLaplace hα hs τ hτ hL).choose_spec.2

/-- The backward Laplace transform is the integral of the damped backward orbit. -/
theorem spectralStripBackwardLaplace_apply (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) (u : W) :
    spectralStripBackwardLaplace hα hs τ hτ hL u =
      ∫ x in Ioi 0, Real.exp (-L * x) • T(τ expU(-x)) u :=
  ((exists_spectralStripBackwardLaplace hα hs τ hτ hL).choose_spec.1 u).2

/-- The damped backward orbit of a vector of the strip space is integrable. -/
theorem integrableOn_spectralStripBackwardLaplace (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) (u : W) :
    IntegrableOn (fun x ↦ Real.exp (-L * x) • T(τ expU(-x)) u) (Ioi 0) :=
  ((exists_spectralStripBackwardLaplace hα hs τ hτ hL).choose_spec.1 u).1

/-- The backward Laplace transform has operator norm at most the integral of
`exp (-(L - α) x) (1 + x) ^ (s / 2)` over the positive half-line. -/
theorem norm_spectralStripBackwardLaplace_le (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) :
    ‖spectralStripBackwardLaplace hα hs τ hτ hL‖ ≤
      ∫ x in Ioi 0, Real.exp (-(L - α) * x) * (1 + x) ^ (s / 2) :=
  (exists_spectralStripBackwardLaplace hα hs τ hτ hL).choose_spec.2

end Laplace

section Triangular

local notation "W'" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s true
local notation "C₁" => (ideleClassNorm F).ker

/-- The Tamagawa measure is absolutely continuous for the measure of the reciprocal strip
weight, so representatives in the reciprocal-weight space are determined almost everywhere
for the Tamagawa measure. -/
private theorem ideleClassTamagawaMeasure_absolutelyContinuous_dual (α s : ℝ) :
    μ𝔽 ≪ (μ𝔽).withDensity fun g ↦
      ENNReal.ofReal (intervalSobolevDensity (-α) α s (logIdeleClassNorm F g))⁻¹ := by
  have hD : Measurable fun t : ℝ ↦ intervalSobolevDensity (-α) α s t := by
    unfold intervalSobolevDensity
    fun_prop
  have hlog : Measurable (logIdeleClassNorm F) :=
    Real.measurable_log.comp (NNReal.continuous_coe.comp
      (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).measurable
  refine withDensity_absolutelyContinuous' (hD.comp hlog).inv.ennreal_ofReal.aemeasurable
    (.of_forall fun g ↦ ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr ?_))
  unfold intervalSobolevDensity
  exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)

include hα hs in
/-- Pairing with a vector of the reciprocal-weight space is a continuous functional on the
strip space, and the product of the representatives is integrable. -/
private theorem exists_spectralSobolevPairing_clm (v : W') :
    ∃ Λ : W →L[ℂ] ℂ, ∀ f : W, Integrable (fun g ↦ f g * v g) μ𝔽 ∧
      Λ f = spectralSobolevPairing (F := F) f v := by
  let D := (modulatedIntervalSobolev_dual m𝔽
    (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
    μ𝔽 (-α) α s hI hs).exists.choose
  refine ⟨D.symm v, fun f ↦ ?_⟩
  have hf : Integrable (fun g ↦ f g * D (D.symm v) g) μ𝔽 ∧
      (D.symm v) f = spectralSobolevPairing (F := F) f (D (D.symm v)) :=
    spectralSobolevPairing_dual (F := F) hI hs (D.symm v) f
  rwa [D.apply_symm_apply v] at hf

/-- A zero jet at a product is the zeroth jet of the first factor times a binomial combination
of the jets of at most the same order at the second factor. -/
private theorem spectralZeroJet_mul (χ₀ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) (h y : C𝔽) :
    spectralZeroJet χ₀ b t k (h * y) = spectralZeroJet χ₀ b t 0 h *
      ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℂ) * (logIdeleClassNorm F h : ℂ) ^ (k - i)) *
        spectralZeroJet χ₀ b t i y := by
  have hlog : logIdeleClassNorm F (h * y) = logIdeleClassNorm F h + logIdeleClassNorm F y := by
    change Real.log ((ideleClassNorm F (h * y)).val : ℝ) =
      Real.log ((ideleClassNorm F h).val : ℝ) + Real.log ((ideleClassNorm F y).val : ℝ)
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.2 (ideleClassNorm F h).ne_zero)
      (NNReal.coe_ne_zero.2 (ideleClassNorm F y).ne_zero)]
  unfold spectralZeroJet
  rw [map_mul, hlog, Complex.ofReal_add, add_comm (logIdeleClassNorm F h : ℂ), add_pow, pow_zero,
    mul_one, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- The translated moments. Let `v i` represent the jets of orders `i ≤ k` at one point in the
reciprocal-weight space. The pairing of a translate of `u` with the jet of order `k` is the
zeroth jet at the translating element times the binomial combination of the pairings of `u`
with the jets of orders `i ≤ k`, with the powers of the logarithm of the norm of the
translating element as coefficients. -/
theorem spectralSobolevPairing_translation_zeroJet (χ₀ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ)
    (v : ℕ → W') (hv : ∀ i ≤ k, (v i : C𝔽 → ℂ) =ᵐ[μ𝔽] spectralZeroJet χ₀ b t i)
    (h : C𝔽) (u : W) :
    spectralSobolevPairing (F := F) (T(h) u) (v k) = spectralZeroJet χ₀ b t 0 h *
      ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℂ) * (logIdeleClassNorm F h : ℂ) ^ (k - i)) *
        spectralSobolevPairing (F := F) u (v i) := by
  have hle (i : ℕ) (hi : i ∈ Finset.range (k + 1)) : i ≤ k :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hae (i : ℕ) (hi : i ≤ k) : (fun y ↦ u y * v i y) =ᵐ[μ𝔽]
      fun y ↦ u y * spectralZeroJet χ₀ b t i y := by
    filter_upwards [hv i hi] with y hy
    rw [hy]
  have hint (i : ℕ) (hi : i ≤ k) :
      Integrable (fun y ↦ u y * spectralZeroJet χ₀ b t i y) μ𝔽 := by
    obtain ⟨Λ, hΛ⟩ := exists_spectralSobolevPairing_clm hα hs (v i)
    exact (hΛ u).1.congr (hae i hi)
  have hpair (i : ℕ) (hi : i ≤ k) : spectralSobolevPairing (F := F) u (v i) =
      ∫ y, u y * spectralZeroJet χ₀ b t i y ∂μ𝔽 := integral_congr_ae (hae i hi)
  have h1 : spectralSobolevPairing (F := F) (T(h) u) (v k) =
      ∫ y, u y * spectralZeroJet χ₀ b t k (h * y) ∂μ𝔽 :=
    integral_translate_mul μ𝔽 h _ _ _ _
      (hardySobolevTranslation_apply μ𝔽 m𝔽 (-α) α s hI hs h u) (hv k le_rfl)
  have h2 : (fun y ↦ u y * spectralZeroJet χ₀ b t k (h * y)) = fun y ↦
      ∑ i ∈ Finset.range (k + 1), (spectralZeroJet χ₀ b t 0 h *
        ((k.choose i : ℂ) * (logIdeleClassNorm F h : ℂ) ^ (k - i))) *
          (u y * spectralZeroJet χ₀ b t i y) := by
    funext y
    rw [spectralZeroJet_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  rw [h1, h2, integral_finsetSum _ fun i hi ↦ (hint i (hle i hi)).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [integral_const_mul, hpair i (hle i hi), mul_assoc]

/-- A unitary character of the idele class group is an exponential of an imaginary multiple of
the logarithmic coordinate along a continuous one-parameter section. -/
theorem exists_section_character_frequency (χ₀ : PontryaginDual C𝔽) (τ : ℝ≥0ˣ →ₜ* C𝔽) :
    ∃ θ : ℝ, ∀ x : ℝ, (χ₀ (τ expU(x)) : ℂ) = Complex.exp (θ * x * Complex.I) := by
  obtain ⟨e, he⟩ := exists_realPontryaginDualEquiv
  let c : PontryaginDual (Multiplicative ℝ) :=
    { toFun := fun y ↦ χ₀ (τ expU(y.toAdd))
      map_one' := by
        change χ₀ (τ expU((0 : ℝ))) = 1
        rw [expUnits_zero, map_one, map_one]
      map_mul' := fun y y' ↦ by
        change χ₀ (τ expU(y.toAdd + y'.toAdd)) = _
        rw [expUnits_add, map_mul, map_mul]
      continuous_toFun := χ₀.continuous.comp
        (τ.continuous.comp (continuous_expUnits.comp continuous_toAdd)) }
  obtain ⟨x₀, hx₀⟩ := e.surjective c
  refine ⟨2 * Real.pi * x₀.toAdd, fun x ↦ ?_⟩
  have h : c (Multiplicative.ofAdd x) = Circle.exp (2 * Real.pi * (x₀.toAdd * x)) := by
    rw [← hx₀, ← he]
    rfl
  change ((c (Multiplicative.ofAdd x) : Circle) : ℂ) = _
  rw [h, Circle.coe_exp]
  congr 1
  push_cast
  ring

/-- Paper: Notation 10.2.1.1, p. 440. For every norm section there is a choice of unitary
extensions of the norm-one characters that are trivial on the section. For such a choice the
frequency `θ` of `exists_section_character_frequency` is zero.
Deviation: The paper does not relate its choice of extensions to a section. This is the
construction of `exists_spectralBasepointChoice` for an arbitrary section. -/
theorem exists_spectralBasepointChoice_section (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) :
    ∃ χ : PontryaginDual C₁ → PontryaginDual C𝔽,
      IsSpectralBasepointChoice χ ∧ ∀ (ω : PontryaginDual C₁) (r : ℝ≥0ˣ), χ ω (τ r) = 1 := by
  let P : C𝔽 →ₜ* C𝔽 := ContinuousMonoidHom.id C𝔽 / τ.comp m𝔽
  have hP (x : C𝔽) : P x ∈ (ideleClassNorm F).ker := by
    change ideleClassNorm F (x / τ (ideleClassNorm F x)) = 1
    rw [map_div, hτ, div_self']
  let p : C𝔽 →ₜ* (ideleClassNorm F).ker :=
    ⟨P.toMonoidHom.codRestrict _ hP, P.continuous.subtype_mk _⟩
  refine ⟨fun ω ↦ ω.comp p, fun ω ↦ ?_, fun ω r ↦ ?_⟩
  · ext x : 1
    change ω (p (x : C𝔽)) = ω x
    apply congrArg ω
    apply Subtype.ext
    change (x : C𝔽) / τ (ideleClassNorm F x) = x
    rw [show ideleClassNorm F (x : C𝔽) = 1 from x.property, map_one, div_one]
  · have h1 : p (τ r) = 1 := by
      apply Subtype.ext
      change τ r / τ (ideleClassNorm F (τ r)) = 1
      rw [hτ, div_self']
    change ω (p (τ r)) = 1
    rw [h1, map_one]

/-- Along a norm section, the zeroth jet with real offset `b` and ordinate `t` is the
exponential `exp ((b + (t + θ) i) x)` of the logarithmic coordinate, where `θ` is the frequency
of the base character along the section. -/
theorem spectralZeroJet_section (χ₀ : PontryaginDual C𝔽) (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {θ : ℝ}
    (hθ : ∀ x : ℝ, (χ₀ (τ expU(x)) : ℂ) = Complex.exp (θ * x * Complex.I)) (b t x : ℝ) :
    spectralZeroJet χ₀ b t 0 (τ expU(x)) =
      Complex.exp (((b : ℂ) + ((t + θ : ℝ) : ℂ) * Complex.I) * x) := by
  have hnorm : ((ideleClassNorm F (τ expU(x))).val : ℝ) = Real.exp x := by
    rw [hτ expU(x), Units.val_mk0, Real.coe_toNNReal _ (Real.exp_pos x).le]
  unfold spectralZeroJet
  rw [pow_zero, mul_one]
  change (χ₀ (τ expU(x)) : ℂ) * (((ideleClassNorm F (τ expU(x))).val : ℝ) : ℂ) ^
    ((b : ℂ) + (t : ℂ) * Complex.I) = _
  rw [hθ, hnorm, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Triangularity of a Laplace transform of translations on the jets at one point, for an
arbitrary path of translating elements along which the zeroth jet is `exp (z x)`. -/
private theorem spectralSobolevPairing_laplace_zeroJet (γ : ℝ → C𝔽) {L : ℝ}
    (χ₀ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) (v : ℕ → W')
    (hv : ∀ i ≤ k, (v i : C𝔽 → ℂ) =ᵐ[μ𝔽] spectralZeroJet χ₀ b t i) {z : ℂ}
    (hz : ∀ x : ℝ, spectralZeroJet χ₀ b t 0 (γ x) = Complex.exp (z * x)) (hzL : z.re < L)
    (u : W) (hint : IntegrableOn (fun x ↦ Real.exp (-L * x) • T(γ x) u) (Ioi 0))
    (hlow : ∀ i < k, spectralSobolevPairing (F := F) u (v i) = 0) :
    spectralSobolevPairing (F := F) (∫ x in Ioi 0, Real.exp (-L * x) • T(γ x) u) (v k) =
      ((L : ℂ) - z)⁻¹ * spectralSobolevPairing (F := F) u (v k) := by
  obtain ⟨Λ, hΛ⟩ := exists_spectralSobolevPairing_clm hα hs (v k)
  have hΛ' (f : W) : spectralSobolevPairing (F := F) f (v k) = Λ f := (hΛ f).2.symm
  rw [hΛ', hΛ' u]
  refine laplace_apply_of_exp Λ (fun x ↦ T(γ x) u) hzL hint fun x ↦ ?_
  change Λ (T(γ x) u) = _
  rw [← hΛ', ← hΛ' u, spectralSobolevPairing_translation_zeroJet hα hs χ₀ b t k v hv (γ x) u,
    hz x, Finset.sum_eq_single k, Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, mul_one,
    one_mul]
  · intro i hi hik
    rw [hlow i (lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hik), mul_zero]
  · intro hk
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) hk

/-- Triangularity of the forward Laplace transform on the jets at one point. Let `v i`
represent the jets of orders `i ≤ k` with real offset `b` and ordinate `t` in the
reciprocal-weight space, and let the zeroth jet be `exp (z x)` along the section, with
`re z < L`. If `u` pairs to zero with the jets of orders below `k`, then the pairing of the
forward transform of `u` with the jet of order `k` is `(L - z)⁻¹` times that of `u`. -/
theorem spectralSobolevPairing_forwardLaplace_zeroJet (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L)
    (χ₀ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) (v : ℕ → W')
    (hv : ∀ i ≤ k, (v i : C𝔽 → ℂ) =ᵐ[μ𝔽] spectralZeroJet χ₀ b t i) {z : ℂ}
    (hz : ∀ x : ℝ, spectralZeroJet χ₀ b t 0 (τ expU(x)) = Complex.exp (z * x))
    (hzL : z.re < L) (u : W)
    (hlow : ∀ i < k, spectralSobolevPairing (F := F) u (v i) = 0) :
    spectralSobolevPairing (F := F) (spectralStripForwardLaplace hα hs τ hτ hL u) (v k) =
      ((L : ℂ) - z)⁻¹ * spectralSobolevPairing (F := F) u (v k) := by
  rw [spectralStripForwardLaplace_apply]
  exact spectralSobolevPairing_laplace_zeroJet hα hs (fun x ↦ τ expU(x)) χ₀ b t k v hv hz hzL u
    (integrableOn_spectralStripForwardLaplace hα hs τ hτ hL u) hlow

/-- Triangularity of the backward Laplace transform on the jets at one point. Under the
hypotheses of `spectralSobolevPairing_forwardLaplace_zeroJet` with `-L < re z`, the pairing of
the backward transform of `u` with the jet of order `k` is `(L + z)⁻¹` times that of `u`. -/
theorem spectralSobolevPairing_backwardLaplace_zeroJet (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L)
    (χ₀ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) (v : ℕ → W')
    (hv : ∀ i ≤ k, (v i : C𝔽 → ℂ) =ᵐ[μ𝔽] spectralZeroJet χ₀ b t i) {z : ℂ}
    (hz : ∀ x : ℝ, spectralZeroJet χ₀ b t 0 (τ expU(x)) = Complex.exp (z * x))
    (hzL : -L < z.re) (u : W)
    (hlow : ∀ i < k, spectralSobolevPairing (F := F) u (v i) = 0) :
    spectralSobolevPairing (F := F) (spectralStripBackwardLaplace hα hs τ hτ hL u) (v k) =
      ((L : ℂ) + z)⁻¹ * spectralSobolevPairing (F := F) u (v k) := by
  have hz' (x : ℝ) : spectralZeroJet χ₀ b t 0 (τ expU(-x)) = Complex.exp (-z * x) := by
    rw [hz (-x)]
    congr 1
    push_cast
    ring
  have hzL' : (-z).re < L := by
    rw [Complex.neg_re]
    linarith
  rw [spectralStripBackwardLaplace_apply, ← sub_neg_eq_add]
  exact spectralSobolevPairing_laplace_zeroJet hα hs (fun x ↦ τ expU(-x)) χ₀ b t k v hv hz' hzL' u
    (integrableOn_spectralStripBackwardLaplace hα hs τ hτ hL u) hlow

local notation "stripU(" χ ", " j ")" => (spectralStripJet_memLp χ hα hs j).toLp
  (spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2)

/-- The jets of orders at most that of an admitted strip jet, at the same point, are
represented in the reciprocal-weight space, and those of lower order are admitted strip jets. -/
private theorem exists_stripJet_family (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a : ℝ}
    (j : SpectralStripJetIndex χ a α s) :
    ∃ v : ℕ → W',
      v j.val.2.2.2 = stripU(χ, j) ∧
      (∀ i ≤ j.val.2.2.2, (v i : C𝔽 → ℂ) =ᵐ[μ𝔽]
        spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 i) ∧
      ∀ i < j.val.2.2.2, ∃ j' : SpectralStripJetIndex χ a α s,
        j'.val = (j.val.1, j.val.2.1, j.val.2.2.1, i) ∧ v i = stripU(χ, j') := by
  let idx (i : ℕ) (hi : i ≤ j.val.2.2.2) : SpectralStripJetIndex χ a α s :=
    ⟨(j.val.1, j.val.2.1, j.val.2.2.1, i), lt_of_le_of_lt hi j.property⟩
  let v (i : ℕ) : W' := if hi : i ≤ j.val.2.2.2 then
    (spectralStripJet_memLp χ hα hs (idx i hi)).toLp
      (spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 i) else 0
  have hvi (i : ℕ) (hi : i ≤ j.val.2.2.2) :
      v i = (spectralStripJet_memLp χ hα hs (idx i hi)).toLp
        (spectralZeroJet (χ j.val.1) j.val.2.1 j.val.2.2.1 i) := dite_eq_left hi
  refine ⟨v, hvi _ le_rfl, fun i hi ↦ ?_, fun i hi ↦ ⟨idx i hi.le, rfl, hvi i hi.le⟩⟩
  rw [hvi i hi]
  exact (ideleClassTamagawaMeasure_absolutelyContinuous_dual α s).ae_le (MemLp.coeFn_toLp _)

/-- Triangularity of the forward Laplace transform on the strip jets. Let `j` be an admitted
strip jet with real offset `b`, ordinate `t` and order `k`, and let `θ` be the frequency of its
base character along the section. If `u` pairs to zero with the admitted strip jets of lower
order at the same point, then the pairing of the forward transform of `u` with the jet `j` is
`(L - z)⁻¹` times that of `u`, where `z = b + (t + θ) i` is the exponent of the jet along the
section. For an enumeration of the strip jets that lists the lower orders at a point first,
this is the triangularity that puts the values `(L - z)⁻¹` on the diagonal of the transform
for the Gram–Schmidt vectors of the jets. -/
theorem spectralStripJet_pairing_forwardLaplace (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a : ℝ} (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ}
    (hL : α < L) (j : SpectralStripJetIndex χ a α s) {θ : ℝ}
    (hθ : ∀ x : ℝ, (χ j.val.1 (τ expU(x)) : ℂ) = Complex.exp (θ * x * Complex.I)) (u : W)
    (hlow : ∀ i : SpectralStripJetIndex χ a α s, i.val.1 = j.val.1 → i.val.2.1 = j.val.2.1 →
      i.val.2.2.1 = j.val.2.2.1 → i.val.2.2.2 < j.val.2.2.2 →
      spectralSobolevPairing (F := F) u (stripU(χ, i)) = 0) :
    spectralSobolevPairing (F := F) (spectralStripForwardLaplace hα hs τ hτ hL u) (stripU(χ, j)) =
      ((L : ℂ) - ((j.val.2.1 : ℂ) + ((j.val.2.2.1 + θ : ℝ) : ℂ) * Complex.I))⁻¹ *
        spectralSobolevPairing (F := F) u (stripU(χ, j)) := by
  obtain ⟨v, hvk, hv, hvlow⟩ := exists_stripJet_family hα hs χ j
  rw [← hvk]
  refine spectralSobolevPairing_forwardLaplace_zeroJet hα hs τ hτ hL (χ j.val.1) j.val.2.1
    j.val.2.2.1 j.val.2.2.2 v hv
    (spectralZeroJet_section (χ j.val.1) τ hτ hθ j.val.2.1 j.val.2.2.1) ?_ u fun i hi ↦ ?_
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    exact (j.mem_strip_order_pos hα).1.2.trans_lt hL
  · obtain ⟨j', hj', hvi⟩ := hvlow i hi
    rw [hvi]
    exact hlow j' (by rw [hj']) (by rw [hj']) (by rw [hj']) (by rw [hj']; exact hi)

/-- Triangularity of the backward Laplace transform on the strip jets. Under the hypotheses of
`spectralStripJet_pairing_forwardLaplace`, the pairing of the backward transform of `u` with the
jet `j` is `(L + z)⁻¹` times that of `u`, with the same exponent `z = b + (t + θ) i`. -/
theorem spectralStripJet_pairing_backwardLaplace (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a : ℝ} (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ}
    (hL : α < L) (j : SpectralStripJetIndex χ a α s) {θ : ℝ}
    (hθ : ∀ x : ℝ, (χ j.val.1 (τ expU(x)) : ℂ) = Complex.exp (θ * x * Complex.I)) (u : W)
    (hlow : ∀ i : SpectralStripJetIndex χ a α s, i.val.1 = j.val.1 → i.val.2.1 = j.val.2.1 →
      i.val.2.2.1 = j.val.2.2.1 → i.val.2.2.2 < j.val.2.2.2 →
      spectralSobolevPairing (F := F) u (stripU(χ, i)) = 0) :
    spectralSobolevPairing (F := F) (spectralStripBackwardLaplace hα hs τ hτ hL u)
        (stripU(χ, j)) =
      ((L : ℂ) + ((j.val.2.1 : ℂ) + ((j.val.2.2.1 + θ : ℝ) : ℂ) * Complex.I))⁻¹ *
        spectralSobolevPairing (F := F) u (stripU(χ, j)) := by
  obtain ⟨v, hvk, hv, hvlow⟩ := exists_stripJet_family hα hs χ j
  rw [← hvk]
  refine spectralSobolevPairing_backwardLaplace_zeroJet hα hs τ hτ hL (χ j.val.1) j.val.2.1
    j.val.2.2.1 j.val.2.2.2 v hv
    (spectralZeroJet_section (χ j.val.1) τ hτ hθ j.val.2.1 j.val.2.2.1) ?_ u fun i hi ↦ ?_
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    exact (neg_lt_neg hL).trans_le (j.mem_strip_order_pos hα).1.1
  · obtain ⟨j', hj', hvi⟩ := hvlow i hi
    rw [hvi]
    exact hlow j' (by rw [hj']) (by rw [hj']) (by rw [hj']) (by rw [hj']; exact hi)

/-- The diagonal of the operator `R` of step 2 of the argument on #7405. Under the hypotheses of
`spectralStripJet_pairing_forwardLaplace`, the sum of the forward and backward Laplace
transforms, which is convolution along the section with `exp (-L |x|)`, multiplies the pairing
with the jet `j` by `2 L / (L ^ 2 - z ^ 2)`, with `z = b + (t + θ) i`. -/
theorem spectralStripJet_pairing_forwardLaplace_add_backwardLaplace
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a : ℝ} (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ}
    (hL : α < L) (j : SpectralStripJetIndex χ a α s) {θ : ℝ}
    (hθ : ∀ x : ℝ, (χ j.val.1 (τ expU(x)) : ℂ) = Complex.exp (θ * x * Complex.I)) (u : W)
    (hlow : ∀ i : SpectralStripJetIndex χ a α s, i.val.1 = j.val.1 → i.val.2.1 = j.val.2.1 →
      i.val.2.2.1 = j.val.2.2.1 → i.val.2.2.2 < j.val.2.2.2 →
      spectralSobolevPairing (F := F) u (stripU(χ, i)) = 0) :
    spectralSobolevPairing (F := F)
        ((spectralStripForwardLaplace hα hs τ hτ hL +
          spectralStripBackwardLaplace hα hs τ hτ hL) u) (stripU(χ, j)) =
      2 * (L : ℂ) / ((L : ℂ) ^ 2 -
          ((j.val.2.1 : ℂ) + ((j.val.2.2.1 + θ : ℝ) : ℂ) * Complex.I) ^ 2) *
        spectralSobolevPairing (F := F) u (stripU(χ, j)) := by
  have hb := (j.mem_strip_order_pos hα).1
  have hF := spectralStripJet_pairing_forwardLaplace hα hs χ τ hτ hL j hθ u hlow
  have hB := spectralStripJet_pairing_backwardLaplace hα hs χ τ hτ hL j hθ u hlow
  generalize hzdef : (j.val.2.1 : ℂ) + ((j.val.2.2.1 + θ : ℝ) : ℂ) * Complex.I = z at hF hB ⊢
  have hzre : z.re = j.val.2.1 := by
    rw [← hzdef]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  have h1 : (L : ℂ) - z ≠ 0 := fun h ↦ by
    have h' := congrArg Complex.re h
    rw [Complex.sub_re, Complex.ofReal_re, hzre, Complex.zero_re] at h'
    linarith [hb.2]
  have h2 : (L : ℂ) + z ≠ 0 := fun h ↦ by
    have h' := congrArg Complex.re h
    rw [Complex.add_re, Complex.ofReal_re, hzre, Complex.zero_re] at h'
    linarith [hb.1]
  obtain ⟨Λ, hΛ⟩ := exists_spectralSobolevPairing_clm hα hs (stripU(χ, j))
  have hΛ' (f : W) : spectralSobolevPairing (F := F) f (stripU(χ, j)) = Λ f := (hΛ f).2.symm
  rw [add_apply, hΛ', map_add, ← hΛ', ← hΛ', hF, hB, ← add_mul]
  congr 1
  rw [show (L : ℂ) ^ 2 - z ^ 2 = ((L : ℂ) - z) * ((L : ℂ) + z) by ring]
  field_simp
  ring

/-- The forward Laplace transform maps the closed theta subspace of the strip space into
itself: by `spectralStripJet_commonKernel` that subspace is the common kernel of the strip
jets, and the transform is triangular on them. -/
theorem spectralStripForwardLaplace_mem_globalThetaSobolev (a : ℝ) (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) (u : W)
    (hu : u ∈ globalThetaSobolev F a hI hs) :
    spectralStripForwardLaplace hα hs τ hτ hL u ∈ globalThetaSobolev F a hI hs := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice F
  have hK : ∀ f : W, f ∈ globalThetaSobolev F a hI hs ↔
      ∀ j : SpectralStripJetIndex χ a α s, spectralSobolevPairing (F := F) f (stripU(χ, j)) = 0 :=
    spectralStripJet_commonKernel χ hχ hα hs
  have h0 := (hK u).mp hu
  refine (hK _).mpr fun j ↦ ?_
  obtain ⟨θ, hθ⟩ := exists_section_character_frequency (χ j.val.1) τ
  rw [spectralStripJet_pairing_forwardLaplace hα hs χ τ hτ hL j hθ u fun i _ _ _ _ ↦ h0 i, h0 j,
    mul_zero]

/-- The backward Laplace transform maps the closed theta subspace of the strip space into
itself. -/
theorem spectralStripBackwardLaplace_mem_globalThetaSobolev (a : ℝ) (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) (u : W)
    (hu : u ∈ globalThetaSobolev F a hI hs) :
    spectralStripBackwardLaplace hα hs τ hτ hL u ∈ globalThetaSobolev F a hI hs := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice F
  have hK : ∀ f : W, f ∈ globalThetaSobolev F a hI hs ↔
      ∀ j : SpectralStripJetIndex χ a α s, spectralSobolevPairing (F := F) f (stripU(χ, j)) = 0 :=
    spectralStripJet_commonKernel χ hχ hα hs
  have h0 := (hK u).mp hu
  refine (hK _).mpr fun j ↦ ?_
  obtain ⟨θ, hθ⟩ := exists_section_character_frequency (χ j.val.1) τ
  rw [spectralStripJet_pairing_backwardLaplace hα hs χ τ hτ hL j hθ u fun i _ _ _ _ ↦ h0 i, h0 j,
    mul_zero]

end Triangular

section Factorization

/-- The section, run in the direction of decreasing norm, is a one-parameter subgroup of the
idele class group. -/
private theorem exists_section_oneParameter (τ : ℝ≥0ˣ →ₜ* C𝔽) :
    ∃ a : LCATopologicalLie C𝔽, ∀ t : ℝ, a (Multiplicative.ofAdd t) = (τ expU(t))⁻¹ := by
  refine ⟨{ toFun := fun y ↦ (τ expU(y.toAdd))⁻¹
            map_one' := ?_
            map_mul' := ?_
            continuous_toFun := ?_ }, fun t ↦ rfl⟩
  · change (τ expU((0 : ℝ)))⁻¹ = 1
    rw [expUnits_zero, map_one, inv_one]
  · intro y y'
    change (τ expU(y.toAdd + y'.toAdd))⁻¹ = (τ expU(y.toAdd))⁻¹ * (τ expU(y'.toAdd))⁻¹
    rw [expUnits_add, map_mul, mul_inv]
  · exact (τ.continuous.comp (continuous_expUnits.comp continuous_toAdd)).inv

/-- The derivative of a compactly supported function along a one-parameter subgroup vanishes
off the closed support of the function. -/
private theorem hasCompactSupport_bruhatDirectionalDeriv (a : LCATopologicalLie C𝔽)
    {f : C𝔽 → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (bruhatDirectionalDeriv a f) := by
  refine HasCompactSupport.intro hf.isCompact fun x hx ↦ ?_
  have hcont : Continuous fun t : ℝ ↦ x * a (Multiplicative.ofAdd t) :=
    continuous_const.mul (a.continuous.comp continuous_ofAdd)
  have hx0 : x * a (Multiplicative.ofAdd (0 : ℝ)) ∈ (tsupport f)ᶜ := by
    rw [ofAdd_zero, map_one, mul_one]
    exact hx
  have hev : (fun t : ℝ ↦ f (x * a (Multiplicative.ofAdd t))) =ᶠ[𝓝 0] fun _ ↦ (0 : ℂ) := by
    filter_upwards [hcont.continuousAt.preimage_mem_nhds
      ((isClosed_tsupport f).isOpen_compl.mem_nhds hx0)] with t ht
    exact image_eq_zero_of_notMem_tsupport ht
  change deriv (fun t : ℝ ↦ f (x * a (Multiplicative.ofAdd t))) 0 = 0
  rw [hev.deriv_eq, deriv_const]

/-- Every test is the convolution along the section of the one-sided exponential
`exp (-L x)`, `x > 0`, with a test: namely with `L φ` minus the derivative of `φ` along the
section in the direction of decreasing norm. This is the identity `φ = (φ' + L φ) ∗ p_L` of
step 6 of the argument on #7405, with the derivative taken by `bruhatDirectionalDeriv`. -/
theorem exists_bruhatCompactSupport_section_laplace (τ : ℝ≥0ˣ →ₜ* C𝔽) {L : ℝ} (hL : 0 < L)
    (φ : BruhatCompactSupport C𝔽) :
    ∃ ψ : BruhatCompactSupport C𝔽, ∀ g : C𝔽,
      ∫ x in Ioi 0, Real.exp (-L * x) • ψ.val ((τ expU(x))⁻¹ * g) = φ.val g := by
  obtain ⟨a, ha⟩ := exists_section_oneParameter τ
  have hφs : IsBruhatSmooth φ.val := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hφc : Continuous φ.val := continuous_of_bruhatSmooth hφs
  let D : C𝔽 → ℂ := bruhatDirectionalDeriv a φ.val
  have hDs : D ∈ bruhatSmoothSubmodule :=
    bruhatDirectionalDeriv_mem_smooth a ⟨φ.val, φ.property.1⟩
  have hDc : HasCompactSupport D := hasCompactSupport_bruhatDirectionalDeriv a φ.property.2
  have hmem : (L : ℂ) • φ.val - D ∈ bruhatCompactSupportSubmodule C𝔽 :=
    Submodule.sub_mem _ (Submodule.smul_mem _ (L : ℂ) φ.property) ⟨hDs, hDc⟩
  let ψ : BruhatCompactSupport C𝔽 :=
    (⟨(L : ℂ) • φ.val - D, hmem⟩ : bruhatCompactSupportSubmodule C𝔽)
  have hψ (g : C𝔽) : ψ.val g = (L : ℂ) * φ.val g - D g := rfl
  have hψc : Continuous ψ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp ψ.property.1)
  refine ⟨ψ, fun g ↦ ?_⟩
  obtain ⟨Cφ, hCφ⟩ := φ.property.2.exists_bound_of_continuous hφc
  obtain ⟨Cψ, hCψ⟩ := ψ.property.2.exists_bound_of_continuous hψc
  have hpt (x : ℝ) : (τ expU(x))⁻¹ * g = g * a (Multiplicative.ofAdd x) := by
    rw [ha, mul_comm]
  -- The orbit of `φ` through `g` is differentiable at every time.
  have horbit (x : ℝ) : HasDerivAt (fun y : ℝ ↦ φ.val (g * a (Multiplicative.ofAdd y)))
      (D (g * a (Multiplicative.ofAdd x))) x := by
    have h0 : HasDerivAt (fun t : ℝ ↦
        φ.val (g * a (Multiplicative.ofAdd x) * a (Multiplicative.ofAdd t)))
        (D (g * a (Multiplicative.ofAdd x))) (x - x) := by
      rw [sub_self]
      exact hasDerivAt_bruhatDirectionalDeriv a (hφs 1) (g * a (Multiplicative.ofAdd x))
    refine (HasDerivAt.comp_sub_const x x h0).congr_of_eventuallyEq (.of_forall fun y ↦ ?_)
    change φ.val (g * a (Multiplicative.ofAdd y)) =
      φ.val (g * a (Multiplicative.ofAdd x) * a (Multiplicative.ofAdd (y - x)))
    rw [mul_assoc, ← map_mul, ← ofAdd_add, add_sub_cancel]
  have hexp (x : ℝ) : HasDerivAt (fun y : ℝ ↦ ((Real.exp (-L * y) : ℝ) : ℂ))
      ((Real.exp (-L * x) * (-L * 1) : ℝ) : ℂ) x :=
    ((Real.hasDerivAt_exp (-L * x)).comp x ((hasDerivAt_id x).const_mul (-L))).ofReal_comp
  -- A primitive of the damped orbit of `ψ`.
  have hF (x : ℝ) : HasDerivAt
      (fun y : ℝ ↦ -((Real.exp (-L * y) : ℝ) : ℂ) * φ.val (g * a (Multiplicative.ofAdd y)))
      (Real.exp (-L * x) • ψ.val ((τ expU(x))⁻¹ * g)) x := by
    convert (hexp x).neg.mul (horbit x) using 1
    rw [hpt, hψ, Complex.real_smul]
    simp only [Pi.neg_apply]
    push_cast
    ring
  have hint : IntegrableOn (fun x : ℝ ↦ Real.exp (-L * x) • ψ.val ((τ expU(x))⁻¹ * g))
      (Ioi 0) := by
    refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hL).mul_const Cψ) ?_
      (.of_forall fun x ↦ ?_)
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
        (hψc.comp (((τ.continuous.comp continuous_expUnits).inv).mul
          continuous_const))).aestronglyMeasurable
    · rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_left (hCψ _) (Real.exp_pos _).le
  have hlim : Tendsto
      (fun y : ℝ ↦ -((Real.exp (-L * y) : ℝ) : ℂ) * φ.val (g * a (Multiplicative.ofAdd y)))
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun y : ℝ ↦ Real.exp (-L * y) * Cφ) atTop (𝓝 (0 * Cφ)) :=
      (Real.tendsto_exp_comp_nhds_zero.mpr
        (tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.2 hL))).mul_const Cφ
    rw [zero_mul] at h0
    refine squeeze_zero_norm (fun y ↦ ?_) h0
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (hCφ _) (Real.exp_pos _).le
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hF 0).continuousAt.continuousWithinAt
    (fun x _ ↦ hF x) hint hlim]
  simp only [mul_zero, Real.exp_zero, Complex.ofReal_one, ofAdd_zero, map_one, mul_one,
    neg_mul, one_mul, zero_sub, neg_neg]

local notation "A(" φ ")" => hardySobolevTestAction μ𝔽 m𝔽 (-α) α s hI hs φ

/-- The forward Laplace transform after the action of a test `ψ` is the action of the test
`φ` that is the convolution of `ψ` along the section with the one-sided exponential. -/
theorem spectralStripForwardLaplace_testAction (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L)
    (φ ψ : BruhatCompactSupport C𝔽)
    (hconv : ∀ g : C𝔽,
      ∫ x in Ioi 0, Real.exp (-L * x) • ψ.val ((τ expU(x))⁻¹ * g) = φ.val g) (u : W) :
    spectralStripForwardLaplace hα hs τ hτ hL (A(ψ) u) = A(φ) u := by
  have hφc : Continuous φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have hψc : Continuous ψ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp ψ.property.1)
  have hAφ : A(φ) u = ∫ g, φ.val g • T(g) u ∂μ𝔽 :=
    hardySobolev_eq_integral_translation_of_convolution μ𝔽 m𝔽 (-α) α s hI hs
      (hφc.integrable_of_hasCompactSupport φ.property.2) φ.property.2 (A(φ))
      (hardySobolevTestAction_apply μ𝔽 m𝔽 (-α) α s hI hs φ) u
  have hAψ : A(ψ) u = ∫ g, ψ.val g • T(g) u ∂μ𝔽 :=
    hardySobolev_eq_integral_translation_of_convolution μ𝔽 m𝔽 (-α) α s hI hs
      (hψc.integrable_of_hasCompactSupport ψ.property.2) ψ.property.2 (A(ψ))
      (hardySobolevTestAction_apply μ𝔽 m𝔽 (-α) α s hI hs ψ) u
  have hMint : IntegrableOn
      (fun x : ℝ ↦ Real.exp (-L * x) * (Real.exp (α * x) * (1 + x) ^ (s / 2))) (Ioi 0) := by
    refine (integrableOn_exp_neg_mul_one_add_rpow (sub_pos.mpr hL) (s / 2)).congr
      (.of_forall fun x ↦ ?_)
    change Real.exp (-(L - α) * x) * (1 + x) ^ (s / 2) =
      Real.exp (-L * x) * (Real.exp (α * x) * (1 + x) ^ (s / 2))
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [spectralStripForwardLaplace_apply, hAφ, hAψ]
  exact laplace_integral_smul_orbit μ𝔽 (hardySobolevTranslation μ𝔽 m𝔽 (-α) α s hI hs)
    (fun w ↦ (exists_hardySobolevTranslation μ𝔽 m𝔽 (-α) α s hI hs).choose_spec.2.comp
      (continuous_id.prodMk continuous_const))
    (fun x ↦ τ expU(x)) (τ.continuous.comp continuous_expUnits) hφc φ.property.2 hψc
    ψ.property.2
    (fun x hx ↦ by
      simpa only [abs_of_pos hx] using norm_hardySobolevTranslation_section_le hα hs τ hτ x)
    hMint hconv u

/-- Every test acts on the strip space as the forward Laplace transform after the action of
another test. This is the factorization of step 6 of the argument on #7405. -/
theorem exists_hardySobolevTestAction_eq_forwardLaplace_comp (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L)
    (φ : BruhatCompactSupport C𝔽) :
    ∃ ψ : BruhatCompactSupport C𝔽, ∀ u : W,
      A(φ) u = spectralStripForwardLaplace hα hs τ hτ hL (A(ψ) u) := by
  obtain ⟨ψ, hψ⟩ := exists_bruhatCompactSupport_section_laplace τ (hα.trans_lt hL) φ
  exact ⟨ψ, fun u ↦ (spectralStripForwardLaplace_testAction hα hs τ hτ hL φ ψ hψ u).symm⟩

local notation "H₀(" a ")" => spectralSobolevQuotient F a hI hs
local notation "Θ₀(" a ")" => globalThetaSobolev F a hI hs
local notation "Aq(" a ", " φ ")" => spectralConvolution (F := F) a hI hs φ

/-- The forward Laplace transform descends to the strip quotient, because it preserves the
closed theta subspace. The descended operator is bounded. It should not be expected to be
Hilbert–Schmidt on the whole quotient: its diagonal entries `(L - z)⁻¹` on the strip jets do not
tend to zero along the components of the norm-one group. The argument on #7405 uses it on one
component at a time. -/
theorem exists_spectralStripForwardLaplace_quotient (a : ℝ) (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L) :
    ∃ Pq : H₀(a) →L[ℂ] H₀(a), ∀ u : W,
      Pq ((Θ₀(a)).mkQ u) = (Θ₀(a)).mkQ (spectralStripForwardLaplace hα hs τ hτ hL u) := by
  have hker : Θ₀(a) ≤
      ((Θ₀(a)).mkQL.comp (spectralStripForwardLaplace hα hs τ hτ hL)).ker := by
    intro v hv
    exact (Submodule.Quotient.mk_eq_zero (Θ₀(a))).mpr
      (spectralStripForwardLaplace_mem_globalThetaSobolev hα hs a τ hτ hL v hv)
  refine ⟨(Θ₀(a)).liftQL _ hker, fun u ↦ ?_⟩
  have h : (Θ₀(a)).liftQL _ hker ((Θ₀(a)).mkQ u) =
      ((Θ₀(a)).mkQL.comp (spectralStripForwardLaplace hα hs τ hτ hL)) u := by
    rw [Submodule.liftQL_apply]
    rfl
  with_reducible_and_instances exact h.trans (Submodule.mkQL_apply _ _)

/-- On the strip quotient, the action of every test is the descended forward Laplace transform
after the action of another test. On one component of the norm-one group this is the product
of two operators of step 6 of the argument on #7405; no factorization of the test as a
convolution of two tests is used. -/
theorem exists_spectralConvolution_eq_forwardLaplace_comp (a : ℝ) (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : Function.RightInverse τ (ideleClassNorm F)) {L : ℝ} (hL : α < L)
    (Pq : H₀(a) →L[ℂ] H₀(a))
    (hPq : ∀ u : W,
      Pq ((Θ₀(a)).mkQ u) = (Θ₀(a)).mkQ (spectralStripForwardLaplace hα hs τ hτ hL u))
    (φ : BruhatCompactSupport C𝔽) :
    ∃ ψ : BruhatCompactSupport C𝔽, Aq(a, φ) = Pq.comp (Aq(a, ψ)) := by
  obtain ⟨ψ, hψ⟩ := exists_hardySobolevTestAction_eq_forwardLaplace_comp hα hs τ hτ hL φ
  refine ⟨ψ, ?_⟩
  ext q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change Aq(a, φ) ((Θ₀(a)).mkQ x) = Pq (Aq(a, ψ) ((Θ₀(a)).mkQ x))
  rw [spectralConvolution_mkQ, spectralConvolution_mkQ, hPq]
  exact congrArg _ (hψ x)

end Factorization

end RiemannMasullo.Isolated
