module

public import RiemannMasullo.Ch09_HardySobolev.Sec2
public import RiemannMasullo.AppC_LCTVS.Sec3b
public import RiemannMasullo.AppC_LCTVS.Sec4

/-!
# Module structures over test functions and approximate units

Masullo, §9.3, pp. 419–432.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ContDiff ENNReal NNReal UniformConvergenceCLM

namespace RiemannMasullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

section RegularizedAction

-- TODO(paper-gap): On I = [0,∞) a log-coordinate bump supported in (−2,−1)
-- has finite intervalSobolevENorm. Its translate by 3 has infinite norm.
-- Full left translation therefore fails on the finite-norm domain of §9.2.

variable [SecondCountableTopology G]
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (m : G →ₜ* ℝ≥0ˣ)

set_option quotPrecheck false in
local notation "logMod" => (fun x ↦ Real.log ((m x).val : ℝ))
local notation "W" => (fun a b s ↦ CompactIntervalSobolev μ logMod a b s)
set_option quotPrecheck false in
local notation "Lβ" E => E →Lᵤ[ℂ, {s : Set E | Bornology.IsVonNBounded ℂ s}] E

/-- Paper: Definition 9.3.1.1, p. 419. Left translation acts jointly continuously
on the compact-interval Hardy–Sobolev Hilbert space, with the translated function
as its almost-everywhere representative.
Deviation: This records the regular representation used in the definition, in the
weighted L² model of §9.2. -/
theorem exists_hardySobolevTranslation (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s) :
    ∃ ρ : G →* (W a b s →L[ℂ] W a b s),
      (∀ g u, (ρ g u : G → ℂ) =ᵐ[μ] fun x ↦ u (g⁻¹ * x)) ∧
      Continuous (fun p : G × W a b s ↦ ρ p.1 p.2) := by sorry

/-- Paper: Definition 9.3.1.1, p. 419. Choose the regular representation characterized
by the left-translation formula. -/
def hardySobolevTranslation (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s) :
    G →* (W a b s →L[ℂ] W a b s) :=
  (exists_hardySobolevTranslation μ m a b s hab hs).choose

/-- Paper: Definition 9.3.1.1, p. 419. The action has the left-translation formula
on representatives almost everywhere. -/
theorem hardySobolevTranslation_apply (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (g : G) (u : W a b s) :
    (hardySobolevTranslation μ m a b s hab hs g u : G → ℂ) =ᵐ[μ]
      fun x ↦ u (g⁻¹ * x) :=
  (exists_hardySobolevTranslation μ m a b s hab hs).choose_spec.1 g u

section Pettis

-- TODO(paper-gap): Norm-continuous functionals on the bounded operators need
-- not be measurable on translations. The Pettis formula below tests each orbit
-- in the representation space, as in Lemma C.4.3.11.

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
  [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E]
variable (ρ : G →* (E →L[ℂ] E))

/-- Paper: Remark 9.3.1.2, p. 419. Integrating a test function against continuous
left translation gives a continuous endomorphism and is linear in the test function.
Deviation: The operator integral is taken on each vector, as in (9.3.2.2) and §C.4.3.
The complete representation space is a parameter. -/
theorem exists_bruhatRegularizedAction [CompleteSpace E]
    (_hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) :
    ∃ A : BruhatCompactSupport G →ₗ[ℂ] Lβ E,
      ∀ φ u, HasPettisIntegral (.positive μ) (fun g ↦ φ.val g • ρ g u) (A φ u) := by sorry

/-- Paper: Definition 9.3.1.1, p. 419. A test function acts by integrating
its scalar multiples of left translations against Haar measure.
Deviation: The Pettis integral is specified on each input vector. Instantiate the
representation with the action on the decay space or the Hardy–Sobolev space. -/
def bruhatRegularizedAction [CompleteSpace E]
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) :
    BruhatCompactSupport G →ₗ[ℂ] Lβ E :=
  (exists_bruhatRegularizedAction μ ρ hρ).choose

/-- Paper: Definition 9.3.1.1, p. 419. The action on each vector represents
the Pettis integral of the test function times its orbit. -/
theorem bruhatRegularizedAction_apply [CompleteSpace E]
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) (φ : BruhatCompactSupport G) (u : E) :
    HasPettisIntegral (.positive μ) (fun g ↦ φ.val g • ρ g u)
      (bruhatRegularizedAction μ ρ hρ φ u) :=
  (exists_bruhatRegularizedAction μ ρ hρ).choose_spec φ u

/-- Paper: Definition 9.3.1.1, p. 419. Convolution of test kernels acts as
composition of their integrated endomorphisms.
Deviation: The convolution is represented by its pointwise formula in the test space. -/
theorem bruhatRegularizedAction_convolution [CompleteSpace E]
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) (φ ψ : BruhatCompactSupport G) :
    ∃ θ : BruhatCompactSupport G, θ.val = lcaConvolution μ φ.val ψ.val ∧
      ∀ u, bruhatRegularizedAction μ ρ hρ θ u =
        bruhatRegularizedAction μ ρ hρ φ (bruhatRegularizedAction μ ρ hρ ψ u) := by sorry

end Pettis

/-- Paper: Definition 9.3.1.1, p. 419. The regularized action on the
Hardy–Sobolev space integrates the left translation of its square-integrable classes.
Deviation: Use the compact-interval weighted model of §9.2. -/
def hardySobolevTestAction (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s) :
    BruhatCompactSupport G →ₗ[ℂ] Lβ (W a b s) :=
  bruhatRegularizedAction μ (hardySobolevTranslation μ m a b s hab hs)
    (exists_hardySobolevTranslation μ m a b s hab hs).choose_spec.2

/-- Paper: (9.3.1.2), p. 419. The test action on the weighted Hilbert space
acts by the Haar convolution formula almost everywhere. -/
theorem hardySobolevTestAction_apply (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport G) (u : W a b s) :
    (hardySobolevTestAction μ m a b s hab hs φ u : G → ℂ) =ᵐ[μ]
      lcaConvolution μ φ.val u := by sorry

/-- Paper: Remark 9.3.1.2, p. 419. Convolution by a test function defines
a continuous endomorphism of the exponential-decay space and depends linearly on the test.
Deviation: Evaluating the Pettis integral at each group element gives this pointwise formula. -/
theorem exists_modulatedExponentialDecayTestAction
    (_hm : IsModulation m) (_hms : Surjective m)
    (I : Set ℝ) (_hInt : OrdConnected I) (_hne : I.Nonempty) :
    ∃ A : BruhatCompactSupport G →ₗ[ℂ] Lβ (ModulatedExponentialDecay m I),
      ∀ φ u, (A φ u).val = lcaConvolution μ φ.val u.val := by sorry

/-- Paper: Definition 9.3.1.1, p. 419. The regularized action on the
exponential-decay space acts by convolution of the test function with the input. -/
def modulatedExponentialDecayTestAction (hm : IsModulation m) (hms : Surjective m)
    (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty) :
    BruhatCompactSupport G →ₗ[ℂ] Lβ (ModulatedExponentialDecay m I) :=
  (exists_modulatedExponentialDecayTestAction μ m hm hms I hInt hne).choose

/-- Paper: (9.3.1.2), p. 419. The test action on the exponential-decay space
has the usual pointwise Haar convolution formula. -/
theorem modulatedExponentialDecayTestAction_apply (hm : IsModulation m) (hms : Surjective m)
    (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty)
    (φ : BruhatCompactSupport G) (u : ModulatedExponentialDecay m I) :
    (modulatedExponentialDecayTestAction μ m hm hms I hInt hne φ u).val =
      lcaConvolution μ φ.val u.val := by sorry

/-- Paper: Definition 9.3.1.1, p. 419. The decay-space convolution integrates
the orbits of the left-translation representation of Proposition D.3.3.12. -/
theorem modulatedExponentialDecayTestAction_pettis (hm : IsModulation m) (hms : Surjective m)
    (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty)
    (φ : BruhatCompactSupport G) (u : ModulatedExponentialDecay m I) :
    let τ := (exists_modulatedExponentialDecay_translationAction m I hm hms hInt hne).choose
    HasPettisIntegral (.positive μ) (fun g ↦ φ.val g • τ g u)
      (modulatedExponentialDecayTestAction μ m hm hms I hInt hne φ u) := by sorry

/-- Paper: Lemma 9.3.1.3, p. 419. The test action on the Hardy–Sobolev
space is continuous into the topology of uniform convergence on bounded sets.
Deviation: The weighted Hilbert model is for a compact base interval. -/
theorem continuous_hardySobolevTestAction (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s) :
    Continuous (hardySobolevTestAction μ m a b s hab hs) := by sorry

/-- Paper: Lemma 9.3.1.3, p. 419. The test action on the exponential-decay
space is continuous into the topology of uniform convergence on bounded sets. -/
theorem continuous_modulatedExponentialDecayTestAction (hm : IsModulation m) (hms : Surjective m)
    (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty) :
    Continuous (modulatedExponentialDecayTestAction μ m hm hms I hInt hne) := by sorry

-- TODO(later): Remark 9.3.1.4, p. 420, restricts the regularized action to
-- the global theta closure of §10.1 and to the S-local theta action of §5.4.

-- TODO(paper-gap): Lemma 9.3.1.5's bound is zero at the identity for s > 0.
-- The singleton polynomial-growth claim also omits the exponential twist for b ≠ 0.
-- Borel measurability need not hold for arbitrary continuous operator seminorms.

/-- The compact-interval density of a shifted logarithmic coordinate is at most the square of
the endpoint twist times the polynomial factor of the shift, times the density. -/
private theorem intervalSobolevDensity_add_le (a b s : ℝ) (hs : 0 ≤ s) (L t : ℝ) :
    intervalSobolevDensity a b s (L + t) ≤
      (max (Real.exp (a * L)) (Real.exp (b * L)) * (1 + |L|) ^ (s / 2)) ^ 2 *
        intervalSobolevDensity a b s t := by
  unfold intervalSobolevDensity
  have key : ∀ c : ℝ,
      Real.exp (2 * c * (L + t)) = Real.exp (c * L) ^ 2 * Real.exp (2 * c * t) := fun c ↦ by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hM : ∀ c : ℝ, Real.exp (c * L) ≤ max (Real.exp (a * L)) (Real.exp (b * L)) →
      Real.exp (2 * c * t) ≤ max (Real.exp (2 * a * t)) (Real.exp (2 * b * t)) →
      Real.exp (2 * c * (L + t)) ≤ max (Real.exp (a * L)) (Real.exp (b * L)) ^ 2 *
        max (Real.exp (2 * a * t)) (Real.exp (2 * b * t)) := fun c h1 h2 ↦ by
    rw [key]
    exact mul_le_mul (pow_le_pow_left₀ (Real.exp_pos _).le h1 2) h2 (Real.exp_pos _).le
      (sq_nonneg _)
  have h1 : max (Real.exp (2 * a * (L + t))) (Real.exp (2 * b * (L + t))) ≤
      max (Real.exp (a * L)) (Real.exp (b * L)) ^ 2 *
        max (Real.exp (2 * a * t)) (Real.exp (2 * b * t)) :=
    max_le (hM a (le_max_left _ _) (le_max_left _ _))
      (hM b (le_max_right _ _) (le_max_right _ _))
  have hL0 : 0 ≤ 1 + |L| := by positivity
  have hbase : 1 + (L + t) ^ 2 ≤ (1 + |L|) ^ 2 * (1 + t ^ 2) := by
    rcases le_total 0 L with hL | hL
    · rw [abs_of_nonneg hL]
      nlinarith [mul_nonneg hL (sq_nonneg (t - 1)), mul_nonneg hL (sq_nonneg t),
        sq_nonneg (L * t)]
    · rw [abs_of_nonpos hL]
      nlinarith [mul_nonneg (neg_nonneg.2 hL) (sq_nonneg (t + 1)),
        mul_nonneg (neg_nonneg.2 hL) (sq_nonneg t), sq_nonneg (L * t)]
  have hpow : ((1 + |L|) ^ 2) ^ (s / 2) = ((1 + |L|) ^ (s / 2)) ^ 2 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hL0,
      ← Real.rpow_mul hL0, mul_comm]
  have h2 : (1 + (L + t) ^ 2) ^ (s / 2) ≤
      ((1 + |L|) ^ (s / 2)) ^ 2 * (1 + t ^ 2) ^ (s / 2) :=
    calc (1 + (L + t) ^ 2) ^ (s / 2) ≤ ((1 + |L|) ^ 2 * (1 + t ^ 2)) ^ (s / 2) :=
          Real.rpow_le_rpow (by positivity) hbase (by linarith)
      _ = ((1 + |L|) ^ 2) ^ (s / 2) * (1 + t ^ 2) ^ (s / 2) :=
          Real.mul_rpow (by positivity) (by positivity)
      _ = ((1 + |L|) ^ (s / 2)) ^ 2 * (1 + t ^ 2) ^ (s / 2) := by rw [hpow]
  have hmax : 0 ≤ max (Real.exp (a * L)) (Real.exp (b * L)) ^ 2 *
      max (Real.exp (2 * a * t)) (Real.exp (2 * b * t)) :=
    mul_nonneg (sq_nonneg _) (le_max_of_le_left (Real.exp_pos _).le)
  calc max (Real.exp (2 * a * (L + t))) (Real.exp (2 * b * (L + t))) *
        (1 + (L + t) ^ 2) ^ (s / 2)
      ≤ max (Real.exp (a * L)) (Real.exp (b * L)) ^ 2 *
          max (Real.exp (2 * a * t)) (Real.exp (2 * b * t)) *
        (((1 + |L|) ^ (s / 2)) ^ 2 * (1 + t ^ 2) ^ (s / 2)) :=
        mul_le_mul h1 h2 (by positivity) hmax
    _ = _ := by ring

/-- A continuous endomorphism of a weighted L² space of a left-invariant measure that acts
by left translation on representatives has norm at most `C` when the translated density is
at most `C ^ 2` times the density. -/
private theorem opNorm_le_of_translate_density {H : Type*} [Group H] [MeasurableSpace H]
    [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] {d : H → ℝ≥0∞}
    (hd : Measurable d) (hd' : ∀ x, d x < ⊤) (g : H) {C : ℝ} (hC : 0 ≤ C)
    (hle : ∀ x, d (g * x) ≤ ENNReal.ofReal C ^ 2 * d x)
    (T : Lp ℂ 2 (ν.withDensity d) →L[ℂ] Lp ℂ 2 (ν.withDensity d))
    (hT : ∀ u, (T u : H → ℂ) =ᵐ[ν] fun x ↦ u (g⁻¹ * x)) : ‖T‖ ≤ C := by
  refine T.opNorm_le_bound hC fun u ↦ ?_
  have hae : (T u : H → ℂ) =ᵐ[ν.withDensity d] fun x ↦ u (g⁻¹ * x) :=
    (withDensity_absolutelyContinuous ν d).ae_eq (hT u)
  have hI : ∀ v : H → ℂ, ∫⁻ x, ‖v x‖ₑ ^ (2 : ℝ) ∂(ν.withDensity d) =
      ∫⁻ x, d x * ‖v x‖ₑ ^ (2 : ℝ) ∂ν := fun v ↦
    lintegral_withDensity_eq_lintegral_mul_non_measurable ν hd (ae_of_all _ hd') _
  have hmain : ∫⁻ x, ‖u (g⁻¹ * x)‖ₑ ^ (2 : ℝ) ∂(ν.withDensity d) ≤
      ENNReal.ofReal C ^ 2 * ∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂(ν.withDensity d) :=
    calc ∫⁻ x, ‖u (g⁻¹ * x)‖ₑ ^ (2 : ℝ) ∂(ν.withDensity d)
        = ∫⁻ x, d x * ‖u (g⁻¹ * x)‖ₑ ^ (2 : ℝ) ∂ν := hI fun x ↦ u (g⁻¹ * x)
      _ = ∫⁻ x, d (g * x) * ‖u (g⁻¹ * (g * x))‖ₑ ^ (2 : ℝ) ∂ν :=
          (lintegral_mul_left_eq_self (fun x ↦ d x * ‖u (g⁻¹ * x)‖ₑ ^ (2 : ℝ)) g).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal C ^ 2 * (d x * ‖u x‖ₑ ^ (2 : ℝ)) ∂ν :=
          lintegral_mono fun x ↦ by
            show d (g * x) * ‖u (g⁻¹ * (g * x))‖ₑ ^ (2 : ℝ) ≤
              ENNReal.ofReal C ^ 2 * (d x * ‖u x‖ₑ ^ (2 : ℝ))
            rw [inv_mul_cancel_left, ← mul_assoc]
            exact mul_le_mul' (hle x) le_rfl
      _ = ENNReal.ofReal C ^ 2 * ∫⁻ x, d x * ‖u x‖ₑ ^ (2 : ℝ) ∂ν :=
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      _ = ENNReal.ofReal C ^ 2 * ∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂(ν.withDensity d) := by rw [hI u]
  have h2 : ((2 : ℕ) : ℝ) * (1 / 2) = 1 := by norm_num
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hnorm : eLpNorm (T u) 2 (ν.withDensity d) ≤
      ENNReal.ofReal C * eLpNorm u 2 (ν.withDensity d) := by
    rw [eLpNorm_congr_ae hae, eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero
      ENNReal.ofNat_ne_top ((Lp.aestronglyMeasurable (T u)).congr hae),
      eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (Lp.aestronglyMeasurable u), ENNReal.toReal_ofNat]
    calc (∫⁻ x, ‖u (g⁻¹ * x)‖ₑ ^ (2 : ℝ) ∂(ν.withDensity d)) ^ (1 / (2 : ℝ))
        ≤ (ENNReal.ofReal C ^ 2 *
            ∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂(ν.withDensity d)) ^ (1 / (2 : ℝ)) :=
          ENNReal.rpow_le_rpow hmain hhalf
      _ = ENNReal.ofReal C *
            (∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂(ν.withDensity d)) ^ (1 / (2 : ℝ)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hhalf, ← ENNReal.rpow_natCast,
            ← ENNReal.rpow_mul, h2, ENNReal.rpow_one]
  rw [Lp.norm_def, Lp.norm_def]
  calc (eLpNorm (T u) 2 (ν.withDensity d)).toReal
      ≤ (ENNReal.ofReal C * eLpNorm u 2 (ν.withDensity d)).toReal :=
        ENNReal.toReal_mono
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top u)) hnorm
    _ = C * (eLpNorm u 2 (ν.withDensity d)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]

/-- Paper: Lemma 9.3.1.5, p. 421. Left translation is bounded by the maximum
endpoint twist times a polynomial in the absolute log-module.
Deviation: The factor at the identity is one. On a nonzero singleton base
the endpoint twist still occurs. -/
theorem norm_hardySobolevTranslation_le (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s) (g : G) :
    ‖hardySobolevTranslation μ m a b s hab hs g‖ ≤
      max (Real.exp (a * logMod g)) (Real.exp (b * logMod g)) *
        (1 + |logMod g|) ^ (s / 2) := by
  have hD : Measurable fun t : ℝ ↦ intervalSobolevDensity a b s t := by
    unfold intervalSobolevDensity
    fun_prop
  have hmeas : Measurable fun x : G ↦ Real.log ((m x).val : ℝ) :=
    Real.measurable_log.comp
      (NNReal.continuous_coe.comp (Units.continuous_val.comp (map_continuous m))).measurable
  have hlog : ∀ x : G, Real.log ((m (g * x)).val : ℝ) =
      Real.log ((m g).val : ℝ) + Real.log ((m x).val : ℝ) := fun x ↦ by
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.2 (m g).ne_zero) (NNReal.coe_ne_zero.2 (m x).ne_zero)]
  have hC : 0 ≤ max (Real.exp (a * Real.log ((m g).val : ℝ)))
      (Real.exp (b * Real.log ((m g).val : ℝ))) *
      (1 + |Real.log ((m g).val : ℝ)|) ^ (s / 2) :=
    mul_nonneg (le_max_of_le_left (Real.exp_pos _).le) (Real.rpow_nonneg (by positivity) _)
  have key := opNorm_le_of_translate_density μ
    (d := fun x ↦ ENNReal.ofReal (intervalSobolevDensity a b s (Real.log ((m x).val : ℝ))))
    (hD.comp hmeas).ennreal_ofReal (fun _ ↦ ENNReal.ofReal_lt_top) g hC fun x ↦ by
      show ENNReal.ofReal (intervalSobolevDensity a b s (Real.log ((m (g * x)).val : ℝ))) ≤
        ENNReal.ofReal _ ^ 2 * ENNReal.ofReal _
      rw [hlog x, ← ENNReal.ofReal_pow hC, ← ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (intervalSobolevDensity_add_le a b s hs _ _)
  exact key (hardySobolevTranslation μ m a b s hab hs g)
    (hardySobolevTranslation_apply μ m a b s hab hs g)

/-- Paper: Lemma 9.3.1.5, p. 421. The operator norm of left translation is a
measurable function of the translating element.
Deviation: This retains the measurable operator-norm case established on p. 422. -/
theorem measurable_hardySobolevTranslation_norm (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s) :
    Measurable (fun g ↦ ‖hardySobolevTranslation μ m a b s hab hs g‖) := by
  have hcont (u : W a b s) : Continuous (fun g ↦ hardySobolevTranslation μ m a b s hab hs g u) :=
    (exists_hardySobolevTranslation μ m a b s hab hs).choose_spec.2.comp
      (Continuous.prodMk_left u)
  have hEq : (fun g ↦ ‖hardySobolevTranslation μ m a b s hab hs g‖) =
      fun g ↦ ⨆ u : Metric.closedBall (0 : W a b s) 1,
        ‖hardySobolevTranslation μ m a b s hab hs g u‖ := by
    funext g
    rw [← ContinuousLinearMap.sSup_unitClosedBall_eq_norm, sSup_image', iSup]
  rw [hEq]
  refine LowerSemicontinuous.measurable (lowerSemicontinuous_ciSup (fun g ↦ ?_) fun u ↦ ?_)
  · refine ⟨‖hardySobolevTranslation μ m a b s hab hs g‖, ?_⟩
    rintro _ ⟨u, rfl⟩
    exact ((hardySobolevTranslation μ m a b s hab hs g).le_opNorm_of_le
      (mem_closedBall_zero_iff.mp u.2)).trans_eq (mul_one _)
  · exact ((hcont u).norm).lowerSemicontinuous

end RegularizedAction

section ApproximateUnits

variable [SecondCountableTopology G]
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (m : G →ₜ* ℝ≥0ˣ)

-- TODO(paper-gap): Lemma 9.3.2.1 does not extend from ordinary Schwartz–Bruhat kernels for
-- b ≠ 0. Its single-isotype family cannot converge strongly to the identity on two isotypes.

/-- Paper: Lemma 9.3.2.1, p. 422. On the zero line there is a unique
operator-norm-continuous extension from test functions to Schwartz–Bruhat kernels,
given on each vector by integration of its left translates.
Deviation: This is the separately stated zero-line case of (9.3.2.2) in the proof on
pp. 422–423. The test-space restriction is specified by the same Pettis formula as (9.3.1.2). -/
theorem existsUnique_schwartzBruhat_zeroLineAction (s : ℝ) (hs : 0 ≤ s) :
    let W := CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) 0 0 s
    ∃! A : SchwartzBruhat G →L[ℂ] (W →L[ℂ] W),
      ∀ φ u, HasPettisIntegral (.positive μ)
        (fun g ↦ φ.val g • hardySobolevTranslation μ m 0 0 s le_rfl hs g u) (A φ u) := by sorry

/-- Paper: Lemma 9.3.2.1, p. 422. On the b-line, kernels whose b-twist is
Schwartz act continuously and extend the test action.
Deviation: The source is the singleton decay space from Example D.3.3.5,
as required by the conjugation in the proof on p. 422. -/
theorem existsUnique_singletonDecay_lineAction (hm : IsModulation m) (hms : Surjective m)
    (b s : ℝ) (hs : 0 ≤ s) :
    let W := CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) b b s
    ∃! A : ModulatedExponentialDecay m {b} →L[ℂ] (W →L[ℂ] W),
      (∀ φ u, HasPettisIntegral (.positive μ)
        (fun g ↦ φ.val g • hardySobolevTranslation μ m b b s le_rfl hs g u) (A φ u)) ∧
      ∀ (φ : BruhatCompactSupport G) u,
        A (bruhatCompactSupportToModulatedExponentialDecay m {b} hm hms φ) u =
          hardySobolevTestAction μ m b b s le_rfl hs φ u := by sorry

-- Remark 9.3.2.2, p. 422, distinguishes the integral approximations from
-- the metric approximation property of a Hilbert space.

/-- Paper: Corollary 9.3.2.3(1), p. 425. The frequency band attached to a character
consists of its twists by imaginary powers of the module with exponents in the given interval.
Deviation: The band is a subset of the full dual, as in the construction in the proof. -/
def modulatedFrequencyBand (m : G →ₜ* ℝ≥0ˣ) (χ : PontryaginDual G) (α β : ℝ) :
    Set (PontryaginDual G) :=
  {ψ | ∃ t ∈ Icc α β, ∀ g, ψ g = χ g * Circle.exp (t * Real.log ((m g).val : ℝ))}

/-- Paper: Corollary 9.3.2.3(1), p. 425. A band consisting of exponent zero
contains exactly its starting character.
Deviation: Sanity check on the frequency band. -/
theorem modulatedFrequencyBand_zero (χ : PontryaginDual G) :
    modulatedFrequencyBand m χ 0 0 = {χ} := by
  ext ψ
  simp only [modulatedFrequencyBand, Icc_self, mem_singleton_iff, mem_ofPred_eq,
    exists_eq_left, zero_mul, Circle.exp_zero, mul_one]
  exact ⟨fun h ↦ ContinuousMonoidHom.ext h, fun h ↦ h ▸ fun _ ↦ rfl⟩

/-- Paper: Corollary 9.3.2.3(1), p. 425. Inclusion of circle characters
into complex quasi-characters identifies the band with the imaginary
norm twists of §3.1.1. -/
theorem mem_modulatedFrequencyBand_iff_normTwist (χ ψ : PontryaginDual G) (α β : ℝ) :
    let j : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
    ψ ∈ modulatedFrequencyBand m χ α β ↔ ∃ t ∈ Icc α β,
      j.comp ψ = quasiCharacterNormTwist m.toMonoidHom m.continuous (j.comp χ) ((t : ℂ) * Complex.I) :=
  by
  intro j
  have key : ∀ (g : G) (t : ℝ), ((((m g).val : ℝ≥0) : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) =
      ((Circle.exp (t * Real.log ((m g).val : ℝ)) : Circle) : ℂ) := by
    intro g t
    have hpos : (0 : ℝ) < (((m g).val : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
      ← Complex.ofReal_log hpos.le, Circle.coe_exp]
    congr 1
    push_cast
    ring
  have hv : ∀ (c : QuasiCharacter G) (z : ℂ) (g : G),
      (quasiCharacterNormTwist m.toMonoidHom m.continuous c z) g =
        c g * ((((m g).val : ℝ≥0) : ℝ) : ℂ) ^ z := fun _ _ _ => rfl
  have hg : ∀ (t : ℝ), j.comp ψ = quasiCharacterNormTwist m.toMonoidHom m.continuous (j.comp χ)
      ((t : ℂ) * Complex.I) ↔ ∀ g, ψ g = χ g * Circle.exp (t * Real.log ((m g).val : ℝ)) := by
    intro t
    constructor
    · intro h g
      have := DFunLike.congr_fun h g
      rw [hv, key] at this
      apply Subtype.ext
      rw [Circle.coe_mul]
      exact this
    · intro h
      ext g
      rw [hv, key]
      have := congrArg (fun z : Circle => (z : ℂ)) (h g)
      rw [Circle.coe_mul] at this
      exact this
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, (hg t).2 h⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, (hg t).1 h⟩

/-- Paper: Lemma 9.3.2.1(1)–(4), pp. 422–424. On each fixed kernel isotype
there is a uniformly bounded sequence of convolutions converging strongly to
the identity there, with band-limited twisted kernels.
Deviation: A single homogeneous kernel kills the other isotypes. The
left-translation eigencharacter is inverse to the Fourier frequency on the kernel. -/
theorem exists_singletonDecay_isotype_approximation (hm : IsModulation m) (hms : Surjective m)
    (b s : ℝ) (hs : 0 ≤ s) (χ : PontryaginDual G) :
    let τ := hardySobolevTranslation μ m b b s le_rfl hs
    let A := (existsUnique_singletonDecay_lineAction μ m hm hms b s hs).exists.choose
    let Eχ := actionIsotype (τ.comp m.toMonoidHom.ker.subtype)
      ((χ⁻¹).comp ⟨m.toMonoidHom.ker.subtype, continuous_subtype_val⟩)
    ∃ φ : ℕ → ModulatedExponentialDecay m {b},
      (∀ n, ‖A (φ n)‖ ≤ 2) ∧
      (∀ (n : ℕ) (k : m.toMonoidHom.ker) x,
        (φ n).val ((k : G)⁻¹ * x) = star (χ (k : G) : ℂ) * (φ n).val x) ∧
      (∀ n, tsupport (lcaFourier μ (modulationWeight m b (φ n).val)) ⊆
        modulatedFrequencyBand m χ (-(n : ℝ)) n) ∧
      ∀ u : Eχ, Tendsto (fun n ↦ A (φ n) u.val) atTop (𝓝 u.val) := by sorry

/-- Paper: Lemma 9.3.2.1(4), p. 422. Band-limited convolutions approximate
the identity on the full b-line space with a uniform operator norm bound.
Deviation: The kernels may combine finitely many compact-group frequencies,
as needed for inputs with components in several isotypes. -/
theorem exists_singletonDecay_approximation (hm : IsModulation m) (hms : Surjective m)
    (b s : ℝ) (hs : 0 ≤ s) :
    let A := (existsUnique_singletonDecay_lineAction μ m hm hms b s hs).exists.choose
    ∃ φ : ℕ → ModulatedExponentialDecay m {b},
      (∀ n, ‖A (φ n)‖ ≤ 2 ∧ HasCompactSupport (lcaFourier μ (modulationWeight m b (φ n).val))) ∧
      ∀ u, Tendsto (fun n ↦ A (φ n) u) atTop (𝓝 u) := by sorry

local instance instDualMeasurableSpaceSec3 : MeasurableSpace (PontryaginDual G) := borel _

variable (ν : Measure (PontryaginDual G)) (hν : IsLCAPlancherelMeasure μ ν)

set_option quotPrecheck false in
local notation "Fourier" => (lcaFourier_unitary μ ν hν).exists.choose

/-- Paper: Corollary 9.3.2.3(1), p. 425. There is a Sobolev function whose
Fourier transform has a smooth representative supported in the outer frequency band
and equal to one in the inner band.
Deviation: The proof uses the full dual rather than the printed norm-one dual for
the support. The transform is the Plancherel transform and the support condition
is on a representative. -/
theorem exists_modulatedSobolev_fourierCutoff
    (_hm : IsModulation m) (_hms : Surjective m)
    (s : ℝ) (_hs : 0 ≤ s) (χ : PontryaginDual G) (α β ε : ℝ)
    (_hαβ : α < β) (_hε : 0 < ε) (_hband : α + ε < β - ε) :
    ∃ (u : Lp ℂ 2 μ) (v : PontryaginDual G → ℂ),
      MemLp (u : G → ℂ) 2 (sobolevMeasure μ (modulatedSobolevWeight m) s) ∧
      (Fourier u : PontryaginDual G → ℂ) =ᵐ[ν] v ∧
      IsBruhatSmooth v ∧ tsupport v ⊆ modulatedFrequencyBand m χ α β ∧
      EqOn v 1 (modulatedFrequencyBand m χ (α + ε) (β - ε)) := by sorry

/-- Paper: Corollary 9.3.2.3(2), p. 425. Functions whose Plancherel transform has
a compactly supported representative are dense in the logarithmically weighted Sobolev norm.
Deviation: A Haar L² class sharing the weighted class's representative is made explicit. -/
theorem dense_modulatedSobolev_fourierCompactSupport
    (_hm : IsModulation m) (_hms : Surjective m) (s : ℝ) (_hs : 0 ≤ s) :
    Dense {f : ModulatedSobolev m μ s | ∃ (u : Lp ℂ 2 μ) (v : PontryaginDual G → ℂ),
      (u : G → ℂ) =ᵐ[μ] (f : G → ℂ) ∧
      (Fourier u : PontryaginDual G → ℂ) =ᵐ[ν] v ∧ HasCompactSupport v} := by sorry

-- TODO(paper-gap): Lemma 9.3.2.4 includes identically zero Mellin components and
-- also fails for nonzero components, e.g. exp(z²) sin(z²) on the positive reals.

-- TODO(paper-gap): Lemma 9.3.2.5 gives an empty coefficient family for a Gaussian
-- with nowhere-zero Mellin transform, although the algebraic convolution ideal is proper.

-- TODO(paper-gap): Theorem 9.3.2.6 leaves φ and χ unbound. The kernels in (9.3.2.10)
-- become more restrictive as T increases. With a zero at the origin the projectors
-- all kill the same nonzero vector normal to the evaluation kernel.

end ApproximateUnits

section Trace

variable [SecondCountableTopology G]
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (m : G →ₜ* ℝ≥0ˣ)

set_option quotPrecheck false in
local notation "weightDensity" => (fun a b s x ↦
  intervalSobolevDensity a b s (Real.log ((m x).val : ℝ)))
local notation "weightedMeasure" => (fun a b s ↦
  μ.withDensity (fun x ↦ ENNReal.ofReal (weightDensity a b s x)))
set_option quotPrecheck false in
local notation "W" => (fun a b s ↦
  CompactIntervalSobolev μ (fun x ↦ Real.log ((m x).val : ℝ)) a b s)

/-- Paper: §9.3.3.1, p. 426. A bounded measurable compactly supported kernel
acts by convolution on the Hardy–Sobolev space.
Deviation: Haar measurability is explicit. The existing weighted L² model
is available for compact base intervals. -/
theorem exists_hardySobolevConvolution (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s)
    (φ : G → ℂ) (_hφ : AEMeasurable φ μ) (_hc : HasCompactSupport φ)
    (_hb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C) :
    ∃ A : W a b s →L[ℂ] W a b s, ∀ u,
      ∀ᵐ x ∂μ, Integrable (fun g ↦ φ g * u (g⁻¹ * x)) μ ∧
        A u x = lcaConvolution μ φ u x := by sorry

/-- Paper: §9.3.3.1, p. 426. The integrated regular representation for a bounded
measurable compactly supported symbol is the operator given by convolution. -/
def hardySobolevConvolution (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (φ : G → ℂ) (hφ : AEMeasurable φ μ) (hc : HasCompactSupport φ)
    (hb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C) :
    W a b s →L[ℂ] W a b s :=
  (exists_hardySobolevConvolution μ m a b s hab hs φ hφ hc hb).choose

/-- Paper: §9.3.3.1, p. 426. Applying the integrated operator gives the stated
convolution integral almost everywhere, with integrability of the integrand. -/
theorem hardySobolevConvolution_apply (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (φ : G → ℂ) (hφ : AEMeasurable φ μ) (hc : HasCompactSupport φ)
    (hb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C) (u : W a b s) :
    ∀ᵐ x ∂μ, Integrable (fun g ↦ φ g * u (g⁻¹ * x)) μ ∧
      hardySobolevConvolution μ m a b s hab hs φ hφ hc hb u x = lcaConvolution μ φ u x :=
  (exists_hardySobolevConvolution μ m a b s hab hs φ hφ hc hb).choose_spec u

/-- Paper: §9.3.3.1, p. 426. On a test function the operator used for the
trace is the regularized action of Definition 9.3.1.1. -/
theorem hardySobolevConvolution_eq_testAction (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport G) (hφ : AEMeasurable φ.val μ)
    (hb : ∃ C : ℝ, ∀ x, ‖φ.val x‖ ≤ C) :
    hardySobolevConvolution μ m a b s hab hs φ.val hφ φ.property.2 hb =
      hardySobolevTestAction μ m a b s hab hs φ := by sorry

section Cutoffs

set_option quotPrecheck false in
local notation "moduleValue" => (fun x ↦ ((m x).val : ℝ))

/-- Paper: Definition 9.3.3.1, p. 427. A cutoff is an inversion-symmetric
nonnegative function of the module with supremum one. Its profile is smooth off a
finite set with finite one-sided limits of every derivative, and it vanishes
outside the larger annulus and equals one on the smaller annulus.
Deviation: The symbol is real-valued, and the uniform norm requirement is expressed
by a supremum over its range. The interval of smoothness of the profile is the positive axis. -/
structure IsModulatedCutoff (Λ ε : ℝ) (ρ : G → ℝ) : Prop where
  radius_pos : 0 < Λ
  width_pos : 0 < ε
  outer_left_sub_width_pos : 0 < Λ⁻¹ - ε
  outer_left_sub_width_lt : Λ⁻¹ - ε < Λ - ε
  nonneg : ∀ x, 0 ≤ ρ x
  abs_le_one : ∀ x, |ρ x| ≤ 1
  sup_eq_one : sSup (range ρ) = 1
  profile : ∃ (q : ℝ → ℝ) (jumps : Finset ℝ),
    (∀ x, ρ x = q (moduleValue x)) ∧ (↑jumps : Set ℝ) ⊆ Ioi 0 ∧
    ContDiffOn ℝ ∞ q (Ioi 0 \ (↑jumps : Set ℝ)) ∧
    ∀ c ∈ jumps, ∀ n : ℕ, ∃ l r : ℝ,
      Tendsto (iteratedDeriv n q) (𝓝[<] c) (𝓝 l) ∧
      Tendsto (iteratedDeriv n q) (𝓝[>] c) (𝓝 r)
  inv_eq : ∀ x, ρ x = ρ x⁻¹
  support_subset : tsupport ρ ⊆ moduleValue ⁻¹' Icc Λ⁻¹ Λ
  eq_one : EqOn ρ 1 (moduleValue ⁻¹' Icc (Λ⁻¹ + ε) (Λ - ε))

/-- Paper: Definition 9.3.3.1, p. 427. A cutoff equals one at the identity
whenever the inner module band contains one.
Deviation: Sanity check on the plateau condition. -/
theorem IsModulatedCutoff.apply_one {Λ ε : ℝ} {ρ : G → ℝ}
    (hρ : IsModulatedCutoff m Λ ε ρ) (_h₁ : Λ⁻¹ + ε ≤ 1) (_h₂ : 1 ≤ Λ - ε) :
    ρ 1 = 1 :=
  hρ.eq_one (by
    change ((m 1).val : ℝ) ∈ Icc (Λ⁻¹ + ε) (Λ - ε)
    rw [map_one, Units.val_one, NNReal.coe_one]
    exact ⟨_h₁, _h₂⟩)

/-- Paper: Definition 9.3.3.1, p. 427. The piecewise smooth profile gives a
measurable function on the group.
Deviation: This is the measurability needed to act on weighted L². -/
theorem IsModulatedCutoff.measurable {Λ ε : ℝ} {ρ : G → ℝ}
    (hρ : IsModulatedCutoff m Λ ε ρ) :
    Measurable ρ := by
  obtain ⟨q, jumps, hfactor, _, hq, _⟩ := hρ.profile
  have hmeas : Measurable (fun t : Ioi (0 : ℝ) ↦ q t.val) := by
    apply ContinuousOn.measurable_of_countable_compl (s := (Subtype.val ⁻¹' (jumps : Set ℝ))ᶜ)
    · exact hq.continuousOn.comp continuous_subtype_val.continuousOn
        fun t ht ↦ ⟨t.property, ht⟩
    · rw [compl_compl]
      exact jumps.finite_toSet.countable.preimage Subtype.val_injective
  let modulePos (x : G) : Ioi (0 : ℝ) := ⟨(m x).val, NNReal.coe_pos.mpr (Units.zero_lt _)⟩
  have hmodule : Continuous modulePos :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).subtype_mk _
  rw [funext hfactor]
  exact hmeas.comp hmodule.measurable

/-- Paper: Definition 9.3.3.1, p. 427. A smooth cutoff is a cutoff whose
complex-valued realization on the group is Bruhat smooth. -/
def IsSmoothModulatedCutoff (Λ ε : ℝ) (ρ : G → ℝ) : Prop :=
  IsModulatedCutoff m Λ ε ρ ∧ IsBruhatSmooth (fun x ↦ (ρ x : ℂ))

/-- Paper: Definition 9.3.3.1, p. 427. A smooth cutoff is continuous on the
group, including at module values where the piecewise smooth definition permits jumps.
Deviation: Sanity check on the smoothness requirement. -/
theorem IsSmoothModulatedCutoff.continuous {Λ ε : ℝ} {ρ : G → ℝ}
    (hρ : IsSmoothModulatedCutoff m Λ ε ρ) :
    Continuous ρ := by
  obtain ⟨k, hk, _, hDescend⟩ := hρ.2 0
  have hkCompact : IsCompact (k : Set G) := by
    let A : OpenCompactlyGeneratedSubgroups (PontryaginDual G) := ⟨lcaAnnihilator k, hk.2⟩
    obtain ⟨_, _, _, hker, hCompact⟩ := lca_dualSubgroup_quotient A
    rwa [hker, show lcaDualAnnihilator A.val = k from lcaDualAnnihilator_annihilator k hk.1]
      at hCompact
  rw [continuous_iff_continuousAt]
  intro x
  -- Use a compact generating set containing the point, a neighborhood, and the good subgroup.
  obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds (1 : G)
  let L := insert x (U ∪ (k : Set G))
  let H := Subgroup.closure L
  have hLH : L ⊆ (H : Set G) := Subgroup.subset_closure
  have hL : L ∈ 𝓝 (1 : G) :=
    mem_of_superset hU (subset_union_left.trans (subset_insert _ _))
  have hH : IsOpen (H : Set G) := H.isOpen_of_mem_nhds (mem_of_superset hL hLH)
  have hGen : IsCompactlyGeneratedGroup H :=
    ⟨Subtype.val ⁻¹' L, continuous_subtype_val.continuousAt.preimage_mem_nhds hL,
      (H.isClosed_of_isOpen hH).isClosedEmbedding_subtypeVal.isCompact_preimage
        ((hUc.union hkCompact).insert x), Subgroup.closure_preimage_eq_top L⟩
  let p : BruhatStructuralPair G :=
    ⟨(H, OrderDual.toDual k), hH, hGen, hk,
      subset_union_right.trans ((subset_insert _ _).trans hLH)⟩
  obtain ⟨e⟩ := p.elementary
  obtain ⟨f₀, hf₀, hSmooth⟩ := hDescend p rfl
  let RealCoords := EuclideanSpace ℝ (Fin e.realDim)
  let TorusCover := EuclideanSpace ℝ (Fin e.torusDim)
  let DiscreteCoords := (Fin e.latticeRank → ℤ) × e.finiteFactor
  let Elementary := ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor
  let cover : (RealCoords × TorusCover) × DiscreteCoords → Elementary := fun u ↦ elementaryCover u.1 u.2.1 u.2.2
  have hq : IsOpenQuotientMap (fun u : TorusCover ↦ fun i ↦ (u i : AddCircle (1 : ℝ))) :=
    (IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk).comp
      (PiLp.homeomorph 2 (fun _ : Fin e.torusDim ↦ ℝ)).isOpenQuotientMap
  have hCover : IsOpenQuotientMap cover :=
    (Homeomorph.prodAssoc RealCoords (Fin e.torusDim → AddCircle (1 : ℝ)) DiscreteCoords).isOpenQuotientMap.comp
      ((IsOpenQuotientMap.id.prodMap hq).prodMap IsOpenQuotientMap.id)
  let g : Elementary → ℂ := fun y ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd y))
  have hg : Continuous g := by
    apply hCover.continuous_comp_iff.mp
    exact continuous_prod_of_discrete_right.mpr fun d ↦ (hSmooth e d.1 d.2).continuous
  have hf₀c : Continuous f₀ := by
    have hc : Continuous (fun y : p.quotient ↦ g (e.equiv y).toAdd) := hg.comp e.equiv.continuous
    simpa only [g, ofAdd_toAdd, e.equiv.symm_apply_apply] using hc
  have hlocal : Continuous (fun y : H ↦ ρ y.val) := by
    have hc : Continuous (fun y : H ↦ (f₀ (QuotientGroup.mk y)).re) :=
      Complex.continuous_re.comp (hf₀c.comp QuotientGroup.continuous_mk)
    simpa only [hf₀, Complex.ofReal_re] using hc
  exact hH.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
    (hlocal.continuousAt (x := (⟨x, hLH (mem_insert _ _)⟩ : H)))

/-- Paper: Definition 9.3.3.1, p. 427. A positive real modulation admits a
smooth cutoff with outer radius two and width one quarter.
Deviation: Sanity check that both cutoff predicates are inhabited. -/
theorem exists_smoothModulatedCutoff_radius_two (_hm : IsModulation m) (_hms : Surjective m) :
    ∃ ρ : G → ℝ, IsSmoothModulatedCutoff m 2 (1 / 4) ρ := by sorry

/-- Paper: Remark 9.3.3.2, pp. 427–428. Multiplication by a measurable symbol
bounded in absolute value by one defines a contractive endomorphism.
Deviation: This uses an arbitrary L² measure so the same construction applies to each
Hardy–Sobolev weight. -/
theorem exists_lpCutoffMultiplier (ν : Measure G) (ρ : G → ℝ) (_hm : Measurable ρ)
    (_hb : ∀ x, |ρ x| ≤ 1) :
    ∃ T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν, ‖T‖ ≤ 1 ∧
      ∀ u, (T u : G → ℂ) =ᵐ[ν] fun x ↦ (ρ x : ℂ) * u x := by
  let symbol (x : G) : ℂ := ρ x
  have hbound (x : G) : ‖symbol x‖ ≤ 1 := by
    simpa only [symbol, Complex.norm_real, Real.norm_eq_abs] using _hb x
  have hsymbol : MemLp symbol ∞ ν :=
    memLp_top_of_bound (Complex.measurable_ofReal.comp _hm).aestronglyMeasurable
      1 (.of_forall hbound)
  let multiply := ContinuousLinearMap.mul ℂ ℂ
  let T := multiply.holderL ν ∞ 2 2 (hsymbol.toLp symbol)
  have hT (u : Lp ℂ 2 ν) : (T u : G → ℂ) =ᵐ[ν] fun x ↦ symbol x * u x :=
    (multiply.coeFn_holder (r := 2) (hsymbol.toLp symbol) u).trans <|
      hsymbol.coeFn_toLp.mono fun x hx ↦ congrArg (· * u x) hx
  refine ⟨T, T.opNorm_le_bound zero_le_one (fun u ↦ ?_), hT⟩
  rw [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hT u] with x hx
  rw [hx, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hbound x)

/-- Paper: Definition 9.3.3.1, p. 427. The cutoff operator is pointwise multiplication
on the space of square-integrable classes.
Deviation: Its measure is a parameter. Applying the operator to the weighted
measure gives the Hardy–Sobolev cutoff. -/
def lpCutoffMultiplier (ν : Measure G) (ρ : G → ℝ) (hm : Measurable ρ)
    (hb : ∀ x, |ρ x| ≤ 1) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  (exists_lpCutoffMultiplier ν ρ hm hb).choose

/-- Paper: (9.3.3.2), p. 427. Representatives of the cutoff operator agree
almost everywhere with the product by the symbol. -/
theorem lpCutoffMultiplier_apply (ν : Measure G) (ρ : G → ℝ) (hm : Measurable ρ)
    (hb : ∀ x, |ρ x| ≤ 1) (u : Lp ℂ 2 ν) :
    (lpCutoffMultiplier ν ρ hm hb u : G → ℂ) =ᵐ[ν] fun x ↦ (ρ x : ℂ) * u x :=
  (exists_lpCutoffMultiplier ν ρ hm hb).choose_spec.2 u

/-- Paper: Definition 9.3.3.1, p. 427. A cutoff gives a truncation operator
on square-integrable classes for the chosen measure. -/
def modulatedCutoffOperator (ν : Measure G) {Λ ε : ℝ} {ρ : G → ℝ}
    (hρ : IsModulatedCutoff m Λ ε ρ) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  lpCutoffMultiplier ν ρ hρ.measurable hρ.abs_le_one

/-- Paper: (9.3.3.2), p. 427. The truncation multiplies by the cutoff on almost
every representative value. -/
theorem modulatedCutoffOperator_apply (ν : Measure G) {Λ ε : ℝ} {ρ : G → ℝ}
    (hρ : IsModulatedCutoff m Λ ε ρ) (u : Lp ℂ 2 ν) :
    (modulatedCutoffOperator m ν hρ u : G → ℂ) =ᵐ[ν]
      fun x ↦ (ρ x : ℂ) * u x :=
  lpCutoffMultiplier_apply ν ρ hρ.measurable hρ.abs_le_one u

/-- Paper: Remark 9.3.3.2, pp. 427–428. A nonnegative cutoff acts by a
positive self-adjoint operator on weighted L². -/
theorem modulatedCutoffOperator_isPositive (ν : Measure G) {Λ ε : ℝ} {ρ : G → ℝ}
    (hρ : IsModulatedCutoff m Λ ε ρ) :
    (modulatedCutoffOperator m ν hρ).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).2
  intro u
  have hinner : inner ℂ (modulatedCutoffOperator m ν hρ u) u =
      ((∫ x, ρ x * ‖u x‖ ^ 2 ∂ν : ℝ) : ℂ) := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [modulatedCutoffOperator_apply m ν hρ u] with x hx
    rw [hx, ← smul_eq_mul, inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp
  rw [hinner]
  exact ⟨rfl, integral_nonneg fun x ↦ mul_nonneg (hρ.nonneg x) (sq_nonneg _)⟩

/-- Paper: Remark 9.3.3.2, p. 428. The multiplier norm is the essential
supremum of its symbol for a sigma-finite measure.
Deviation: A pointwise supremum of one can be attained only on a null set
when the inner band is empty. -/
theorem modulatedCutoffOperator_norm (ν : Measure G) [SigmaFinite ν] {Λ ε : ℝ} {ρ : G → ℝ}
    (hρ : IsModulatedCutoff m Λ ε ρ) :
    ‖modulatedCutoffOperator m ν hρ‖ = (eLpNorm ρ ∞ ν).toReal := by
  let T := modulatedCutoffOperator m ν hρ
  change ‖T‖ = _
  have hmul (u : Lp ℂ 2 ν) : ∀ᵐ x ∂ν, ‖(T u) x‖ = ‖ρ x‖ * ‖u x‖ := by
    filter_upwards [modulatedCutoffOperator_apply m ν hρ u] with x hx
    rw [hx, norm_mul, Complex.norm_real]
  have htop : MemLp ρ ∞ ν :=
    memLp_top_of_bound hρ.measurable.aestronglyMeasurable 1 (.of_forall hρ.abs_le_one)
  apply le_antisymm
  · apply T.opNorm_le_bound ENNReal.toReal_nonneg
    intro u
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hmul u, ae_le_lpNorm_exponent_top htop] with x hTu hx
    exact hTu.trans_le (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  · refine le_of_forall_gt_imp_ge_of_dense fun c hc ↦ ?_
    have hc₀ : 0 ≤ c := (norm_nonneg T).trans hc.le
    apply ENNReal.toReal_le_of_le_ofReal hc₀
    rw [eLpNorm_exponent_top htop.aestronglyMeasurable]
    apply eLpNormEssSup_le_of_ae_bound
    rw [ae_iff]
    simp only [not_le]
    by_contra hnonzero
    -- Test the operator on a finite-measure subset where the cutoff exceeds c.
    obtain ⟨s, hs, hsub, hpos, hfin⟩ := Measure.exists_subset_measure_lt_top
      (measurableSet_lt measurable_const hρ.measurable.norm) (pos_iff_ne_zero.mpr hnonzero)
    let u : Lp ℂ 2 ν := indicatorConstLp 2 hs hfin.ne 1
    have hu : 0 < ‖u‖ := by
      dsimp only [u]
      rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul]
      exact Real.rpow_pos_of_pos (ENNReal.toReal_pos hpos.ne' hfin.ne) _
    have hlow : c * ‖u‖ ≤ ‖T u‖ := by
      rw [← Real.norm_of_nonneg hc₀, ← norm_smul]
      apply Lp.norm_le_norm_of_ae_le
      have hout : ∀ᵐ x ∂ν, x ∉ s → u x = 0 := indicatorConstLp_coeFn_notMem
      filter_upwards [Lp.coeFn_smul c u, hmul u, hout] with x hcu hTu hxout
      rw [hcu, Pi.smul_apply, norm_smul, Real.norm_of_nonneg hc₀, hTu]
      by_cases hx : x ∈ s
      · exact mul_le_mul_of_nonneg_right (hsub hx).le (norm_nonneg _)
      · simp [hxout hx]
    exact (mul_lt_mul_of_pos_right hc hu).not_ge (hlow.trans (T.le_opNorm u))

/-- Reflecting the logarithmic coordinate exchanges the base interval with its negative. -/
private theorem intervalSobolevDensity_neg (a b s t : ℝ) :
    intervalSobolevDensity a b s (-t) = intervalSobolevDensity (-b) (-a) s t := by
  have ha : 2 * a * -t = 2 * -a * t := by ring
  have hb : 2 * b * -t = 2 * -b * t := by ring
  unfold intervalSobolevDensity
  rw [max_comm, neg_sq, ha, hb]

/-- Inversion carries the measure with the reflected density to the measure with the
original density, for an inversion-invariant base measure. -/
private theorem measurePreserving_inv_withDensity {H : Type*} [Group H] [MeasurableSpace H]
    [MeasurableInv H] (ν : Measure H) [ν.IsInvInvariant] {f : H → ℝ≥0∞} (hf : Measurable f) :
    MeasurePreserving Inv.inv (ν.withDensity fun x ↦ f x⁻¹) (ν.withDensity f) := by
  refine ⟨measurable_inv, Measure.ext fun t ht ↦ ?_⟩
  rw [Measure.map_apply measurable_inv ht, withDensity_apply _ (measurable_inv ht),
    withDensity_apply _ ht]
  exact (Measure.measurePreserving_inv ν).setLIntegral_comp_preimage ht hf

/-- Composition with inversion is an isometric isomorphism between the square-integrable
classes of two measures that inversion exchanges. -/
private theorem exists_lpInversion {H : Type*} [InvolutiveInv H] [MeasurableSpace H]
    {ν₁ ν₂ : Measure H} (h₁ : MeasurePreserving Inv.inv ν₂ ν₁)
    (h₂ : MeasurePreserving Inv.inv ν₁ ν₂) :
    ∃ J : Lp ℂ 2 ν₁ ≃ₗᵢ[ℂ] Lp ℂ 2 ν₂, ∀ u, (J u : H → ℂ) =ᵐ[ν₂] fun x ↦ u x⁻¹ := by
  let F : Lp ℂ 2 ν₁ →ₗᵢ[ℂ] Lp ℂ 2 ν₂ := Lp.compMeasurePreservingₗᵢ ℂ Inv.inv h₁
  let B : Lp ℂ 2 ν₂ →ₗᵢ[ℂ] Lp ℂ 2 ν₁ := Lp.compMeasurePreservingₗᵢ ℂ Inv.inv h₂
  have hF (u : Lp ℂ 2 ν₁) : (F u : H → ℂ) =ᵐ[ν₂] fun x ↦ u x⁻¹ :=
    Lp.coeFn_compMeasurePreserving u h₁
  have hB (v : Lp ℂ 2 ν₂) : (B v : H → ℂ) =ᵐ[ν₁] fun x ↦ v x⁻¹ :=
    Lp.coeFn_compMeasurePreserving v h₂
  have hBF (u : Lp ℂ 2 ν₁) : B (F u) = u := by
    apply Lp.ext
    filter_upwards [hB (F u), h₂.quasiMeasurePreserving.ae_eq_comp (hF u)] with x hx hx'
    rw [hx]
    simpa only [comp_apply, inv_inv] using hx'
  have hFB (v : Lp ℂ 2 ν₂) : F (B v) = v := by
    apply Lp.ext
    filter_upwards [hF (B v), h₁.quasiMeasurePreserving.ae_eq_comp (hB v)] with x hx hx'
    rw [hx]
    simpa only [comp_apply, inv_inv] using hx'
  exact ⟨{ toLinearEquiv := LinearEquiv.ofLinearMap F.toLinearMap B.toLinearMap
            (LinearMap.ext hFB) (LinearMap.ext hBF)
           norm_map' := F.norm_map }, hF⟩

/-- An isometry acting by inversion on representatives intertwines the multipliers
of an inversion-invariant symbol. -/
private theorem lpCutoffMultiplier_inversion {ν₁ ν₂ : Measure G}
    (h₁ : MeasurePreserving Inv.inv ν₂ ν₁) (J : Lp ℂ 2 ν₁ ≃ₗᵢ[ℂ] Lp ℂ 2 ν₂)
    (hJ : ∀ u, (J u : G → ℂ) =ᵐ[ν₂] fun x ↦ u x⁻¹) (ρ : G → ℝ) (hm : Measurable ρ)
    (hb : ∀ x, |ρ x| ≤ 1) (hinv : ∀ x, ρ x = ρ x⁻¹) (u : Lp ℂ 2 ν₁) :
    J (lpCutoffMultiplier ν₁ ρ hm hb u) = lpCutoffMultiplier ν₂ ρ hm hb (J u) := by
  apply Lp.ext
  filter_upwards [hJ (lpCutoffMultiplier ν₁ ρ hm hb u),
    h₁.quasiMeasurePreserving.ae_eq_comp (lpCutoffMultiplier_apply ν₁ ρ hm hb u),
    lpCutoffMultiplier_apply ν₂ ρ hm hb (J u), hJ u] with x hx₁ hx₂ hx₃ hx₄
  rw [hx₁, hx₃, hx₄, hinv x]
  exact hx₂

/-- Paper: (9.3.3.3), p. 427. Inversion interchanges the two reflected
interval spaces and intertwines their cutoff multipliers. -/
theorem modulatedCutoffOperator_inversion (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s)
    {Λ ε : ℝ} {ρ : G → ℝ} (hρ : IsModulatedCutoff m Λ ε ρ) :
    ∃ J : W a b s ≃ₗᵢ[ℂ] W (-b) (-a) s,
      (∀ u, (J u : G → ℂ) =ᵐ[μ] fun x ↦ u x⁻¹) ∧
      ∀ u, J (modulatedCutoffOperator m (weightedMeasure a b s) hρ u) =
        modulatedCutoffOperator m (weightedMeasure (-b) (-a) s) hρ (J u) := by
  have hmeas (a b : ℝ) : Measurable fun x : G ↦
      ENNReal.ofReal (intervalSobolevDensity a b s (Real.log ((m x).val : ℝ))) := by
    have hlog : Measurable fun x : G ↦ Real.log ((m x).val : ℝ) :=
      Real.measurable_log.comp
        (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable
    have hdensity : Measurable (intervalSobolevDensity a b s) := by
      unfold intervalSobolevDensity
      fun_prop
    exact (hdensity.comp hlog).ennreal_ofReal
  have hpres (a b : ℝ) : MeasurePreserving Inv.inv
      (μ.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity (-b) (-a) s (Real.log ((m x).val : ℝ))))
      (μ.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b s (Real.log ((m x).val : ℝ)))) := by
    have hreflect : (fun x : G ↦
        ENNReal.ofReal (intervalSobolevDensity (-b) (-a) s (Real.log ((m x).val : ℝ)))) =
        fun x ↦ ENNReal.ofReal (intervalSobolevDensity a b s (Real.log ((m x⁻¹).val : ℝ))) := by
      funext x
      rw [map_inv, Units.val_inv_eq_inv_val, NNReal.coe_inv, Real.log_inv,
        intervalSobolevDensity_neg]
    have h := measurePreserving_inv_withDensity μ (hmeas a b)
    rw [hreflect]
    exact h
  have h₁ := hpres a b
  have h₂ := hpres (-b) (-a)
  rw [neg_neg, neg_neg] at h₂
  obtain ⟨J, hJ⟩ := exists_lpInversion h₁ h₂
  refine ⟨J, fun u ↦ ?_, fun u ↦ ?_⟩
  · refine (withDensity_absolutelyContinuous' (hmeas (-b) (-a)).aemeasurable
      (.of_forall fun x ↦ ?_)).ae_eq (hJ u)
    have hpos : 0 < intervalSobolevDensity (-b) (-a) s (Real.log ((m x).val : ℝ)) := by
      unfold intervalSobolevDensity
      exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
    exact (ENNReal.ofReal_pos.mpr hpos).ne'
  · exact lpCutoffMultiplier_inversion h₁ J hJ ρ hρ.measurable hρ.abs_le_one hρ.inv_eq u

/-- Paper: Definition 9.3.3.3, p. 428. The absolute cutoff associated to a set
of module values is the indicator of its inverse image.
Deviation: Use the same formula for the positive, negative and two-sided cutoffs
with `Ici Λ⁻¹`, `Iic Λ`, and `Icc Λ⁻¹ Λ`, respectively. -/
def modulatedAbsoluteCutoff (J : Set ℝ) : G → ℝ :=
  (moduleValue ⁻¹' J).indicator 1

/-- Paper: (9.3.3.4)–(9.3.3.5), p. 428. The two-sided absolute cutoff is the
product of the two one-sided cutoffs. -/
theorem modulatedAbsoluteCutoff_Icc (Λ : ℝ) :
    modulatedAbsoluteCutoff m (Icc Λ⁻¹ Λ) =
      modulatedAbsoluteCutoff m (Ici Λ⁻¹) * modulatedAbsoluteCutoff m (Iic Λ) := by
  ext x
  simp only [modulatedAbsoluteCutoff, Pi.mul_apply, indicator, mem_preimage, mem_Icc, mem_Ici,
    mem_Iic, Pi.one_apply]
  split_ifs <;> simp_all

/-- Paper: Definition 9.3.3.3, p. 428. The two-sided cutoff of radius two
takes value one at the identity.
Deviation: Sanity check at a point inside the band. -/
theorem modulatedAbsoluteCutoff_radius_two_apply_one :
    modulatedAbsoluteCutoff m (Icc (1 / 2) 2) 1 = 1 := by
  simp only [modulatedAbsoluteCutoff, map_one, Units.val_one]
  exact indicator_of_mem (by norm_num) _

/-- Paper: Definition 9.3.3.3, p. 428. Each measurable module band has a
measurable indicator with values bounded in absolute value by one.
Deviation: These are the side conditions for applying the common multiplier. -/
theorem modulatedAbsoluteCutoff_measurable_bounded (J : Set ℝ) (_hJ : MeasurableSet J) :
    Measurable (modulatedAbsoluteCutoff m J) ∧ ∀ x, |modulatedAbsoluteCutoff m J x| ≤ 1 := by
  refine ⟨measurable_const.indicator
    (_hJ.preimage (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable),
    fun x ↦ ?_⟩
  simp only [modulatedAbsoluteCutoff, indicator]
  split_ifs <;> simp

/-- Paper: Definition 9.3.3.3, p. 428. The absolute cutoff operator is
multiplication by the indicator of the chosen set of module values. -/
def modulatedAbsoluteCutoffOperator (ν : Measure G) (J : Set ℝ) (hJ : MeasurableSet J) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  (hardySobolevCutoff_spec (μ := ν) (U := moduleValue ⁻¹' J)
    (hJ.preimage (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable)).choose

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] in
/-- Paper: Definition 9.3.3.3, p. 428. The band operator agrees with
the measurable-set projection used in §9.2 on every input. -/
theorem modulatedAbsoluteCutoffOperator_eq_hardySobolevCutoff (ν : Measure G)
    (J : Set ℝ) (hJ : MeasurableSet J) (u : Lp ℂ 2 ν) :
    modulatedAbsoluteCutoffOperator m ν J hJ u =
      hardySobolevCutoff (U := moduleValue ⁻¹' J)
        (hJ.preimage (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable) u :=
  (((hardySobolevCutoff_spec (μ := ν) _).choose_spec.2) u).2.1

/-- Paper: (9.3.3.6)–(9.3.3.7), p. 428. The absolute cutoff retains the input
on the chosen band and vanishes outside it, as an identity of L² representatives. -/
theorem modulatedAbsoluteCutoffOperator_apply (ν : Measure G) (J : Set ℝ)
    (hJ : MeasurableSet J) (u : Lp ℂ 2 ν) :
    (modulatedAbsoluteCutoffOperator m ν J hJ u : G → ℂ) =ᵐ[ν]
      fun x ↦ (modulatedAbsoluteCutoff m J x : ℂ) * u x := by
  have h := (((hardySobolevCutoff_spec (μ := ν) (U := moduleValue ⁻¹' J)
    (hJ.preimage (NNReal.continuous_coe.comp
      (Units.continuous_val.comp m.continuous)).measurable)).choose_spec.2) u).2.2
  refine h.trans (Eventually.of_forall fun x ↦ ?_)
  simp only [modulatedAbsoluteCutoff, indicator]
  split_ifs <;> simp

-- TODO(paper-gap): Remark 9.3.3.4 calls the projectors injective and their symbols
-- bounded below away from zero almost everywhere. Each one-sided cutoff kills
-- functions supported on its excluded half of the module axis.
-- The two-sided cutoff is zero almost everywhere for Λ ≤ 1 on the positive reals.

/-- Paper: Remark 9.3.3.4, p. 428. Every absolute band cutoff is an
orthogonal projection with closed range, including the zero projection. -/
theorem modulatedAbsoluteCutoffOperator_projection (ν : Measure G) (J : Set ℝ)
    (hJ : MeasurableSet J) :
    IsStarProjection (modulatedAbsoluteCutoffOperator m ν J hJ) ∧
      IsClosed (range (modulatedAbsoluteCutoffOperator m ν J hJ)) := by
  have hU : MeasurableSet (moduleValue ⁻¹' J) :=
    hJ.preimage (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable
  obtain ⟨hclosed, hP⟩ := (hardySobolevCutoff_spec (μ := ν) hU).choose_spec
  refine ⟨⟨ContinuousLinearMap.ext fun u ↦ (hP u).1, ?_⟩, hclosed⟩
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2
  intro u v
  rw [ContinuousLinearMap.coe_coe, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [modulatedAbsoluteCutoffOperator_apply m ν J hJ u,
    modulatedAbsoluteCutoffOperator_apply m ν J hJ v] with x hu hv
  rw [hu, hv]
  simp only [modulatedAbsoluteCutoff, indicator]
  split_ifs <;> simp

end Cutoffs

variable (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
variable (φ : G → ℂ) (hφ : AEMeasurable φ μ) (hc : HasCompactSupport φ)
  (hb : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C)
variable {Λ ε : ℝ} {ρ : G → ℝ}

local notation "A" => hardySobolevConvolution μ m a b s hab hs φ hφ hc hb
local notation "truncation" => modulatedCutoffOperator m (weightedMeasure a b s)

-- TODO(paper-gap): Theorem 9.3.3.5(1) assumes neither measurability of φ nor
-- existence of a differentiation limit at the identity. The diagonal smoothening
-- can fail for a bounded Borel φ oscillating on sufficiently separated annuli.

/-- The Hardy–Sobolev density on a compact base interval is positive. -/
private theorem intervalSobolevDensity_pos' (a b s t : ℝ) : 0 < intervalSobolevDensity a b s t := by
  unfold intervalSobolevDensity
  exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)

/-- The Hardy–Sobolev density on a compact base interval is continuous. -/
private theorem continuous_intervalSobolevDensity (a b s : ℝ) :
    Continuous (intervalSobolevDensity a b s) := by
  unfold intervalSobolevDensity
  refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun t ↦ Or.inl ?_)
  positivity

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] in
/-- The logarithm of the module is continuous. -/
private theorem continuous_logModule' (m : G →ₜ* ℝ≥0ˣ) :
    Continuous (fun x ↦ Real.log ((m x).val : ℝ)) :=
  Real.continuousOn_log.comp_continuous
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous))
    fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] in
/-- A modulated cutoff has compact support when the modulation is proper. -/
private theorem IsModulatedCutoff.isCompact_tsupport' (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)
    {Λ ε : ℝ} {ρ : G → ℝ} (hρ : IsModulatedCutoff m Λ ε ρ) : IsCompact (tsupport ρ) := by
  have hΛ : 0 < Λ⁻¹ := inv_pos.mpr hρ.radius_pos
  let e := Nonneg.unitsHomeomorphPos ℝ
  have hS : IsCompact ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Icc Λ⁻¹ Λ) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
      inter_eq_right.mpr fun t (ht : t ∈ Icc Λ⁻¹ Λ) ↦ mem_Ioi.mpr (hΛ.trans_le ht.1)]
    exact isCompact_Icc
  have hT := hm.1.isCompact_preimage (e.isCompact_preimage.mpr hS)
  refine hT.of_isClosed_subset (isClosed_tsupport ρ) (hρ.support_subset.trans ?_)
  intro x hx
  exact hx

/-- Paper: Theorem 9.3.3.5(1), p. 429. Truncated convolution is Hilbert–Schmidt
and is represented by the displayed square-integrable kernel.
Deviation: This retains the Hilbert–Schmidt conclusion for measurable symbols
on compact base intervals. The source density in the denominator accounts for
integration against the weighted measure. -/
theorem truncatedHardySobolevConvolution_hilbertSchmidt
    (_hm : IsModulation m) (_hms : Surjective m)
    (hρ : IsModulatedCutoff m Λ ε ρ) (_hband : 0 < Λ⁻¹ + ε ∧ Λ⁻¹ + ε < Λ - ε) :
    let ν := weightedMeasure a b s
    let k : G × G → ℂ := fun p ↦
      (ρ p.1 : ℂ) * φ (p.1 * p.2⁻¹) / (weightDensity a b s p.2 : ℂ)
    (truncation hρ).comp A ∈ hilbertSchmidtOperators (W a b s) (W a b s) ∧
      MemLp k 2 (ν.prod ν) ∧
      ∀ u : W a b s, ∀ᵐ x ∂ν,
        Integrable (fun y ↦ k (x, y) * u y) ν ∧
          (truncation hρ).comp A u x = ∫ y, k (x, y) * u y ∂ν := by
  intro ν k
  -- The weight is a continuous positive density.
  let w : G → ℝ := fun x ↦ weightDensity a b s x
  have hwpos (x : G) : 0 < w x := intervalSobolevDensity_pos' a b s _
  have hwcont : Continuous w :=
    (continuous_intervalSobolevDensity a b s).comp (continuous_logModule' m)
  let wN : G → ℝ≥0 := fun x ↦ (w x).toNNReal
  have hwN : Measurable wN := hwcont.measurable.real_toNNReal
  have hνdef : ν = μ.withDensity fun x ↦ (wN x : ℝ≥0∞) := rfl
  have hwN_smul (x : G) (z : ℂ) : wN x • z = (w x : ℂ) * z := by
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hwpos x).le, Complex.real_smul]
  have : IsLocallyFiniteMeasure ν := IsLocallyFiniteMeasure.withDensity_ofReal hwcont
  have hνμ : ν ≪ μ := withDensity_absolutelyContinuous μ _
  -- The kernel is supported in a compact set.
  have hρc : IsCompact (tsupport ρ) := IsModulatedCutoff.isCompact_tsupport' m _hm hρ
  let K₃ : Set G := (fun p : G × G ↦ p.1⁻¹ * p.2) '' (tsupport φ ×ˢ tsupport ρ)
  have hK₃ : IsCompact K₃ := (hc.prod hρc).image (by fun_prop)
  have hsupp (p : G × G) (hp : k p ≠ 0) : p ∈ tsupport ρ ×ˢ K₃ := by
    have h1 : ρ p.1 ≠ 0 := fun h ↦ hp (by simp [k, h])
    have h2 : φ (p.1 * p.2⁻¹) ≠ 0 := fun h ↦ hp (by simp [k, h])
    refine ⟨subset_tsupport _ h1, ⟨(p.1 * p.2⁻¹, p.1), ⟨subset_tsupport _ h2, subset_tsupport _ h1⟩, ?_⟩⟩
    simp
  obtain ⟨B, hB⟩ := hK₃.exists_bound_of_continuousOn
    (f := fun y ↦ (w y)⁻¹) (hwcont.inv₀ fun y ↦ (hwpos y).ne').continuousOn
  have ⟨C, hC⟩ := hb
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  have hbound (p : G × G) : ‖k p‖ ≤ C * max B 0 := by
    by_cases hp : k p = 0
    · rw [hp, norm_zero]; exact mul_nonneg hC0 (le_max_right _ _)
    obtain ⟨-, hy⟩ := hsupp p hp
    have hρ1 : ‖(ρ p.1 : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hρ.abs_le_one _
    have hw1 : ‖((w p.2 : ℂ))⁻¹‖ ≤ max B 0 := by
      rw [norm_inv, Complex.norm_real]; exact (norm_inv (w p.2) ▸ hB _ hy).trans (le_max_left _ _)
    change ‖(ρ p.1 : ℂ) * φ (p.1 * p.2⁻¹) / (w p.2 : ℂ)‖ ≤ _
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    calc ‖(ρ p.1 : ℂ)‖ * ‖φ (p.1 * p.2⁻¹)‖ * ‖((w p.2 : ℂ))⁻¹‖ ≤ 1 * C * max B 0 := by
          gcongr
          exact hC _
      _ = C * max B 0 := by ring
  -- Measurability of the kernel.
  have hkmeas : AEStronglyMeasurable k (ν.prod ν) := by
    have hdiv : AEMeasurable (fun p : G × G ↦ φ (p.1 * p.2⁻¹)) (μ.prod μ) := by
      simp_rw [← div_eq_mul_inv]
      exact hφ.comp_quasiMeasurePreserving (quasiMeasurePreserving_div μ μ)
    have hk : AEMeasurable k (μ.prod μ) :=
      ((Complex.measurable_ofReal.comp (hρ.measurable.comp measurable_fst)).aemeasurable.mul
        hdiv).div (Complex.measurable_ofReal.comp (hwcont.measurable.comp measurable_snd)).aemeasurable
    exact (hk.mono_ac (hνμ.prod hνμ)).aestronglyMeasurable
  have hkL2 : MemLp k 2 (ν.prod ν) :=
    (memLp_top_of_bound hkmeas _ (.of_forall hbound)).mono_exponent_of_measure_support_ne_top
      (fun p hp ↦ by_contra fun h ↦ hp (hsupp p h)) ((hρc.prod hK₃).measure_lt_top).ne le_top
  -- The action of the truncated convolution.
  have happly : ∀ u : W a b s, ∀ᵐ x ∂ν, Integrable (fun y ↦ k (x, y) * u y) ν ∧
      (truncation hρ).comp A u x = ∫ y, k (x, y) * u y ∂ν := by
    intro u
    filter_upwards [modulatedCutoffOperator_apply m ν hρ (A u),
      hνμ.ae_le (hardySobolevConvolution_apply μ m a b s hab hs φ hφ hc hb u)]
      with x hx ⟨hint, hconv⟩
    let F : G → ℂ := fun g ↦ φ g * u (g⁻¹ * x)
    have hFx (y : G) : F (x / y) = φ (x * y⁻¹) * u y := by
      simp [F, div_eq_mul_inv]
    have hsmul (y : G) : wN y • (k (x, y) * u y) = (ρ x : ℂ) * (φ (x * y⁻¹) * u y) := by
      rw [hwN_smul]
      change (w y : ℂ) * ((ρ x : ℂ) * φ (x * y⁻¹) / (w y : ℂ) * u y) = _
      have : (w y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hwpos y).ne'
      field_simp
    have hint' : Integrable (fun y ↦ φ (x * y⁻¹) * u y) μ := by
      have := ((Measure.measurePreserving_div_left μ x).integrable_comp_emb
        (MeasurableEquiv.divLeft x).measurableEmbedding).mpr hint
      exact this.congr (.of_forall fun y ↦ hFx y)
    refine ⟨?_, ?_⟩
    · rw [hνdef, integrable_withDensity_iff_integrable_smul hwN]
      exact (hint'.const_mul (ρ x : ℂ)).congr (.of_forall fun y ↦ (hsmul y).symm)
    · rw [ContinuousLinearMap.comp_apply, hx, hconv, hνdef,
        integral_withDensity_eq_integral_smul hwN]
      simp_rw [hsmul]
      rw [integral_const_mul, lcaConvolution, ← integral_div_left_eq_self F μ x]
      simp_rw [hFx]
  refine ⟨?_, hkL2, happly⟩
  -- Identify the operator with the integral operator of the kernel.
  let op := integralKernelOperator ν (hkL2.toLp k)
  have hop : (truncation hρ).comp A = op.val := by
    refine ContinuousLinearMap.ext fun u ↦ Lp.ext ?_
    have hk' := Measure.ae_ae_of_ae_prod hkL2.coeFn_toLp
    filter_upwards [happly u, integralKernelOperator_apply ν (hkL2.toLp k) u, hk']
      with x hx hopx hkx
    rw [hx.2, hopx.2]
    exact integral_congr_ae (hkx.mono fun y hy ↦ by simp only [hy])
  rw [hop]
  exact op.property

/-- Paper: Theorem 9.3.3.5(2), p. 429. For smooth compactly supported symbols
and piecewise smooth cutoffs, the truncated convolution operator is nuclear, and its trace
equals the integral over the diagonal.
Deviation: A smooth multiplier equal to one on the compact cutoff support gives
the factorization through the smooth case. The diagonal uses Haar measure after the weighted L²
density cancels. The base interval is compact, as in the available Hilbert model. -/
theorem truncatedHardySobolevConvolution_trace
    (_hm : IsModulation m) (_hms : Surjective m)
    (hφsmooth : IsBruhatSmooth φ) (hρ : IsModulatedCutoff m Λ ε ρ)
    (_hband : 0 < Λ⁻¹ + ε ∧ Λ⁻¹ + ε < Λ - ε) :
    let T := (truncation hρ).comp A
    ∃ hT : IsNuclearOperator T,
      Integrable (fun x ↦ (ρ x : ℂ) * φ 1) μ ∧
      hilbertTrace ⟨T, hT⟩ = ∫ x, (ρ x : ℂ) * φ 1 ∂μ := by sorry

-- TODO(paper-gap): Theorem 9.3.3.5(3) uses a point value and the nuclear trace.
-- For general bounded symbols the point value can change without affecting convolution.

/-- Paper: Theorem 9.3.3.5(3), p. 429. For a smooth convolution symbol, the
difference from twice the logarithmic radius times the kernel Haar mass and φ(1)
tends to zero if εΛ tends to zero.
Deviation: The convolution symbol is smooth and the cutoff may have jumps.
A Haar splitting makes the normalization of the kernel Haar measure explicit. The
base interval is compact. -/
theorem truncatedHardySobolevConvolution_trace_tendsto
    (_hm : IsModulation m)
    (_hφsmooth : IsBruhatSmooth φ)
    (τ : ℝ≥0ˣ →ₜ* G) (_hτ : RightInverse τ m)
    [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
    (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]
    (_hμ : μ = (μ₁.prod positiveRealHaar).map
      (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2))
    (ε : ℝ → ℝ) (ρ : ℝ → G → ℝ)
    (_hε : Tendsto (fun Λ ↦ ε Λ * Λ) atTop (𝓝 0))
    (_hρlim : ∀ x, Tendsto (fun Λ ↦ ρ Λ x) atTop (𝓝 1))
    (_hcutoff : ∀ᶠ Λ in atTop, IsModulatedCutoff m Λ (ε Λ) (ρ Λ) ∧
      0 < Λ⁻¹ + ε Λ ∧ Λ⁻¹ + ε Λ < Λ - ε Λ) :
    ∃ traces : ℝ → ℂ,
      (∀ᶠ Λ in atTop, ∃ (hρ : IsModulatedCutoff m Λ (ε Λ) (ρ Λ)),
        let T := (truncation hρ).comp A
        ∃ hT : IsNuclearOperator T, traces Λ = hilbertTrace ⟨T, hT⟩) ∧
      Tendsto (fun Λ ↦ traces Λ - (2 * Real.log Λ * μ₁.real univ : ℝ) * φ 1)
        atTop (𝓝 0) := by sorry

end Trace

end RiemannMasullo
