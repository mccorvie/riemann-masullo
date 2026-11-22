module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3a
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.IsOpenUnits

/-! # Extensions by zero and holomorphic S-idelic zeta functions

Masullo, §5.3.3–5.3.4, pp. 249–265.
-/

@[expose] public noncomputable section

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set TopologicalSpace Topology
open scoped ContDiff Distributions FourierTransform NNReal NumberField.AdeleRing SchwartzMap TensorProduct Topology

namespace RiemannMasullo

set_option quotPrecheck false

section PuncturedLine

-- TODO(paper-gap): The logarithmic argument substitution leaves the exponent interval I fixed.

/-- Paper: Example 5.3.3.1, p. 249.
Logarithmic coordinates give a linear homeomorphism between the weighted spaces on
the real line and the positive multiplicative reals.
Deviation: The exponents are unchanged under the logarithmic change of the argument. -/
theorem positiveRealExponentialDecay_log_equiv (I : Set ℝ) (hI : OrdConnected I)
    (hne : I.Nonempty) :
    ∃ e : PositiveRealExponentialDecay I ≃L[ℂ]
        ModulatedExponentialDecay (ContinuousMonoidHom.id ℝ≥0ˣ) I,
      ∀ f t, (e f).val t = f.val (Real.log (t.val : ℝ)) :=
  identityModulationExponentialDecay_equiv I hI hne

local notation "normPower(" K ", " d ")" =>
  (Units.map nnNormHom.toMonoidHom ^ d : Kˣ →* ℝ≥0ˣ)

/-- Paper: Proposition 5.3.3.2, p. 249.
Natural powers of the norm on the multiplicative group are continuous as
maps to the positive reals. -/
theorem continuous_archimedeanUnitModulation (K : Type*) [NormedField K] (d : ℕ) :
    Continuous (normPower(K, d)) := by
  rw [Units.continuous_iff]
  have h1 : Continuous fun x : Kˣ ↦ (‖(x : K)‖₊ : ℝ≥0) ^ d :=
    (continuous_nnnorm.comp Units.continuous_val).pow d
  have h2 : Continuous fun x : Kˣ ↦ (‖((x⁻¹ : Kˣ) : K)‖₊ : ℝ≥0) ^ d :=
    (continuous_nnnorm.comp Units.continuous_val |>.comp continuous_inv).pow d
  refine ⟨?_, ?_⟩
  · convert h1 using 2 with x
    simp
  · convert h2 using 2 with x
    simp [map_inv₀]

/-- Paper: Proposition 5.3.3.2, p. 249.
The real multiplicative group uses the norm, and the complex multiplicative group
uses the squared norm. -/
def archimedeanUnitModulation (K : Type*) [NormedField K] (d : ℕ) : Kˣ →ₜ* ℝ≥0ˣ :=
  ⟨normPower(K, d), continuous_archimedeanUnitModulation K d⟩

/-- Paper: Proposition 5.3.3.2, p. 249.
At a nonzero argument the module evaluates to the indicated power of its norm. -/
theorem archimedeanUnitModulation_apply (K : Type*) [NormedField K] (d : ℕ) (u : Kˣ) :
    ((archimedeanUnitModulation K d u).val : ℝ) = ‖(u : K)‖ ^ d := by
  show (((((Units.map nnNormHom.toMonoidHom ^ d : Kˣ →* ℝ≥0ˣ) u) : ℝ≥0ˣ).val : ℝ≥0) : ℝ) = _
  rw [MonoidHom.pow_apply]
  simp [nnNormHom]

local notation "𝓔(" K ", " d ", " I ")" => ModulatedExponentialDecay (archimedeanUnitModulation K d) I
local notation "punctured(" K ")" => (⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩ : Opens K)
local notation "𝒟₀(" K ")" => 𝓓(punctured(K), ℂ)
local notation "zeroExtension(" f ")" =>
  (fun x ↦ if hx : x ≠ 0 then f (Units.mk0 x hx) else (0 : ℂ))
local notation "complexCoordinate(" conjugate ")" =>
  (fun z : ℂ ↦ if conjugate then star z else z)
local notation "wirtinger(" conjugate ")" =>
  (if conjugate then wirtingerConjDeriv else wirtingerDeriv)

/-- Paper: §5.3.3, p. 249.
Restriction gives a continuous linear injection of additive real Schwartz functions into
the space with all positive weights. -/
theorem realSchwartz_restrict_positiveDecay :
    ∃ R : 𝓢(ℝ, ℂ) →L[ℂ] 𝓔(ℝ, 1, Ioi 0), Injective R ∧
      ∀ (f : 𝓢(ℝ, ℂ)) (u : ℝˣ), (R f).val u = f u.val := by sorry

/-- Paper: §5.3.3, p. 249.
Restriction of an additive complex Schwartz function to the units gives a continuous
linear injection into the space with all positive squared-norm weights. -/
theorem complexSchwartz_restrict_positiveDecay :
    ∃ R : 𝓢(ℂ, ℂ) →L[ℂ] 𝓔(ℂ, 2, Ioi 0), Injective R ∧
      ∀ (f : 𝓢(ℂ, ℂ)) (u : ℂˣ), (R f).val u = f u.val := by sorry

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by the real coordinate is a linear homeomorphism on compactly supported
smooth tests on the punctured real line. -/
theorem realCoordinate_mul_puncturedTest :
    ∃ M : 𝒟₀(ℝ) ≃L[ℂ] 𝒟₀(ℝ), ∀ f x, M f x = (x : ℂ) * f x := by sorry

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by either complex coordinate, z or its conjugate, is a linear homeomorphism
on compactly supported smooth tests on the punctured complex plane. -/
theorem complexCoordinate_mul_puncturedTest (conjugate : Bool) :
    ∃ M : 𝒟₀(ℂ) ≃L[ℂ] 𝒟₀(ℂ), ∀ f z, M f z = complexCoordinate(conjugate) z * f z := by sorry

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by the real coordinate is continuous for decay on a closed upper half-line. -/
theorem realCoordinate_mul_exponentialDecay (a : ℝ) :
    ∃ M : 𝓔(ℝ, 1, Ici a) →L[ℂ] 𝓔(ℝ, 1, Ici a),
      ∀ f x, (M f).val x = ((x : ℝ) : ℂ) * f.val x := by sorry

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by z or its conjugate is continuous for decay on a closed upper half-line. -/
theorem complexCoordinate_mul_exponentialDecay (conjugate : Bool) (a : ℝ) :
    ∃ M : 𝓔(ℂ, 2, Ici a) →L[ℂ] 𝓔(ℂ, 2, Ici a),
      ∀ f z, (M f).val z = complexCoordinate(conjugate) z.val * f.val z := by sorry

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by the real coordinate is continuously invertible for decay at all exponents. -/
theorem realCoordinate_mul_allExponentialDecay :
    ∃ M : 𝓔(ℝ, 1, univ) ≃L[ℂ] 𝓔(ℝ, 1, univ),
      ∀ f x, (M f).val x = ((x : ℝ) : ℂ) * f.val x := by sorry

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by z or its conjugate is continuously invertible for decay at all exponents. -/
theorem complexCoordinate_mul_allExponentialDecay (conjugate : Bool) :
    ∃ M : 𝓔(ℂ, 2, univ) ≃L[ℂ] 𝓔(ℂ, 2, univ),
      ∀ f z, (M f).val z = complexCoordinate(conjugate) z.val * f.val z := by sorry

-- TODO(paper-gap): Footnote 8 flags the closed-range argument. A convergent net in the LF
-- space of tests need not eventually be bounded and a directed set need not have countable cofinality.

/-- Paper: Proposition 5.3.3.2(2)(1), p. 249.
Each ordinary derivative is a continuous operator of closed range on punctured real tests. -/
theorem iteratedDeriv_puncturedTest_closedRange (m : ℕ) :
    ∃ D : 𝒟₀(ℝ) →L[ℂ] 𝒟₀(ℝ), IsClosed (range D) ∧
      ∀ f x, D f x = iteratedDeriv m (f : ℝ → ℂ) x := by sorry

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250.
Both first Wirtinger operators have closed range on punctured complex tests. -/
theorem wirtinger_puncturedTest_closedRange (conjugate : Bool) :
    ∃ D : 𝒟₀(ℂ) →L[ℂ] 𝒟₀(ℂ), IsClosed (range D) ∧
      ∀ f z, D f z = wirtinger(conjugate) f z := by sorry

/-- Paper: Proposition 5.3.3.2(2)(1), p. 249.
An ordinary derivative of order m shifts the lower endpoint of the decay interval by m. -/
theorem iteratedDeriv_exponentialDecay (m : ℕ) (a : ℝ) :
    ∃ D : 𝓔(ℝ, 1, Ioi a) →L[ℂ] 𝓔(ℝ, 1, Ioi (a + m)),
      ∀ f x, (D f).val x = iteratedDeriv m zeroExtension(f.val) x.val := by sorry

-- TODO(paper-gap): The first Wirtinger operator in the printed weighted shift is
-- missing the exponent m. The proof uses m derivatives for both operators.

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250.
Either iterated Wirtinger derivative gives a continuous operator into the indicated decay space.
Deviation: Both derivatives have order m, as in the proof. The stated target with shift m is
retained, although the squared norm permits a shift of m/2. -/
theorem iteratedWirtinger_exponentialDecay (conjugate : Bool) (m : ℕ) {a : ℝ} (_ha : a < 0) :
    ∃ D : 𝓔(ℂ, 2, Ioi a) →L[ℂ] 𝓔(ℂ, 2, Ioi (a + m)),
      ∀ f z, (D f).val z = ((wirtinger(conjugate))^[m] zeroExtension(f.val)) z.val := by sorry

/-- Paper: Proposition 5.3.3.2(2)(1), p. 249.
Ordinary derivatives act continuously on the punctured real space with decay at all exponents. -/
theorem iteratedDeriv_allExponentialDecay (m : ℕ) :
    ∃ D : 𝓔(ℝ, 1, univ) →L[ℂ] 𝓔(ℝ, 1, univ),
      ∀ f x, (D f).val x = iteratedDeriv m zeroExtension(f.val) x.val := by sorry

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250.
Both iterated Wirtinger operators preserve the punctured complex space with decay at all
exponents and act continuously there. -/
theorem iteratedWirtinger_allExponentialDecay (conjugate : Bool) (m : ℕ) :
    ∃ D : 𝓔(ℂ, 2, univ) →L[ℂ] 𝓔(ℂ, 2, univ),
      ∀ f z, (D f).val z = ((wirtinger(conjugate))^[m] zeroExtension(f.val)) z.val := by sorry

/-- Paper: Proposition 5.3.3.2(2)(1), p. 250.
Weighted Schwartz–Bruhat functions are smooth on the punctured real line. -/
theorem realExponentialDecay_contDiffOn (f : 𝓔(ℝ, 1, Ioi 0)) :
    ContDiffOn ℝ (∞ : ℕ∞ω) zeroExtension(f.val) ({0}ᶜ : Set ℝ) := by sorry

/-- In exponential coordinates, the realization of a Schwartz–Bruhat stage is
smooth along every translate of a continuous homomorphism from a real vector space. -/
private theorem complexExponentialDecay_contDiffOn_alongTranslate {K G : Type*}
    [NormedAddCommGroup K] [NormedSpace ℝ K] [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (U : Multiplicative K →ₜ* G) (f : SchwartzBruhat G) (u : G) :
    ContDiff ℝ (∞ : ℕ∞ω) (fun t : K ↦ f (U (Multiplicative.ofAdd t) * u)) := by
  obtain ⟨p, e, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff f.val).mp f.property
  let H := p.val.1
  have hU : Continuous (fun t : K ↦ U (Multiplicative.ofAdd t)) := U.continuous
  have hpre : IsClopen ((fun t : K ↦ U (Multiplicative.ofAdd t)) ⁻¹' (H : Set G)) :=
    (show IsClopen (H : Set G) from ⟨H.isClosed_of_isOpen p.property.1, p.property.1⟩).preimage hU
  have hfull := hpre.eq_univ ⟨0, by change U 1 ∈ H; simp⟩
  have hmem (t : Multiplicative K) : U t ∈ H := by
    change t.toAdd ∈ (fun v : K ↦ U (Multiplicative.ofAdd v)) ⁻¹' (H : Set G)
    rw [hfull]
    exact mem_univ _
  let UH : Multiplicative K →* H := U.toMonoidHom.codRestrict H hmem
  by_cases hu : u ∈ H
  · let q : H →* p.quotient := QuotientGroup.mk' _
    let a := AddMonoidHom.toMultiplicative.symm
      (e.equiv.toMulEquiv.toMonoidHom.comp (q.comp UH))
    let c := Multiplicative.toAdd (e.equiv (q ⟨u, hu⟩))
    have ha : Continuous a := e.equiv.continuous.comp
      (QuotientGroup.continuous_mk.comp (hU.subtype_mk _))
    have heq (t : K) : f (U (Multiplicative.ofAdd t) * u) = s (a t + c) := by
      rw [← show schwartzBruhatStageRealization p e s = f.val from hs,
        schwartzBruhatStageRealization_apply, dite_eq_left (H.mul_mem (hmem _) hu)]
      change s (Multiplicative.toAdd (e.equiv (q (UH (Multiplicative.ofAdd t) * ⟨u, hu⟩)))) = _
      rw [map_mul, map_mul]
      rfl
    rw [funext heq]
    exact contDiff_comp_affine_elementary a ha c s.property.1
  · have heq (t : K) : f (U (Multiplicative.ofAdd t) * u) = 0 := by
      have hnot : U (Multiplicative.ofAdd t) * u ∉ H := by
        intro h
        exact hu (H.mul_mem_cancel_left (hmem _) |>.mp h)
      rw [← show schwartzBruhatStageRealization p e s = f.val from hs,
        schwartzBruhatStageRealization_apply, dite_eq_right hnot]
    rw [funext heq]
    exact contDiff_const

/-- The local inverse of the Banach-algebra exponential transfers smoothness in
multiplicative coordinates to smoothness in the punctured field. -/
private theorem complexExponentialDecay_contDiffOn_unitsChart {K : Type*} [NormedField K] [NormedAlgebra ℝ K]
    [CompleteSpace K] [LocallyCompactSpace K] [DecidableEq K] (f : SchwartzBruhat Kˣ) :
    ContDiffOn ℝ (∞ : ℕ∞ω) zeroExtension(f.val) ({0}ᶜ : Set K) := by
  let +nondep : NormedAlgebra ℚ K := .restrictScalars ℚ ℝ K
  let U : Multiplicative K →ₜ* Kˣ :=
    { toFun := fun v ↦ ⟨NormedSpace.exp v.toAdd, NormedSpace.exp (-v.toAdd),
        by rw [← NormedSpace.exp_add, add_neg_cancel, NormedSpace.exp_zero],
        by rw [← NormedSpace.exp_add, neg_add_cancel, NormedSpace.exp_zero]⟩
      map_one' := Units.ext NormedSpace.exp_zero
      map_mul' := fun x y ↦ Units.ext NormedSpace.exp_add
      continuous_toFun := Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr
        ((show Continuous (NormedSpace.exp : K → K) from NormedSpace.exp_continuous).comp
          (show Continuous (Multiplicative.toAdd : Multiplicative K → K) from continuous_id)) }
  let : LocallyCompactSpace Kˣ := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).locallyCompactSpace
  have hExp : ContDiffAt ℝ (∞ : ℕ∞ω) (NormedSpace.exp : K → K) 0 :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) (x := (0 : K))).contDiffAt
  let L := ContinuousLinearEquiv.refl ℝ K
  have hD : HasFDerivAt NormedSpace.exp (L : K →L[ℝ] K) 0 := hasFDerivAt_exp_zero
  let log := hExp.localInverse (f' := L) hD (by simp)
  have hlog : ContDiffAt ℝ (∞ : ℕ∞ω) log 1 := by
    simpa only [NormedSpace.exp_zero] using hExp.to_localInverse (f' := L) hD (by simp)
  have hright : ∀ᶠ y : K in 𝓝 1, NormedSpace.exp (log y) = y := by
    unfold log ContDiffAt.localInverse
    simpa only [NormedSpace.exp_zero] using
      (hExp.hasStrictFDerivAt (f' := L) hD (by simp)).eventually_right_inverse
  intro x hx
  have hx0 : x ≠ 0 := hx
  let u := Units.mk0 x hx0
  have hp : ContDiff ℝ (∞ : ℕ∞ω) (fun y : K ↦ y / x) := contDiff_id.div_const x
  have hp0 : x / x = 1 := div_self hx0
  have hlogx : ContDiffAt ℝ (∞ : ℕ∞ω) log (x / x) := by rw [hp0]; exact hlog
  have hg := complexExponentialDecay_contDiffOn_alongTranslate U f u
  have hc : ContDiffAt ℝ (∞ : ℕ∞ω)
      (fun y : K ↦ f (U (Multiplicative.ofAdd (log (y / x))) * u)) x :=
    hg.contDiffAt.comp x (hlogx.comp (f := fun y : K ↦ y / x) (g := log) x hp.contDiffAt)
  apply ContDiffAt.contDiffWithinAt
  apply hc.congr_of_eventuallyEq
  have hnear : Tendsto (fun y : K ↦ y / x) (𝓝 x) (𝓝 1) :=
    hp0 ▸ hp.continuous.continuousAt
  filter_upwards [hnear.eventually hright, isOpen_compl_singleton.mem_nhds hx] with y hy hy0
  have hunit : U (Multiplicative.ofAdd (log (y / x))) * u = Units.mk0 y hy0 := by
    apply Units.ext
    change NormedSpace.exp (log (y / x)) * x = y
    rw [hy, div_mul_cancel₀ _ hx0]
  have hy0' : y ≠ 0 := hy0
  simp only [hunit, dite_eq_left hy0']

/-- Dividing a positive weighted Schwartz–Bruhat twist by its smooth nonzero
weight recovers the original function on the punctured field. -/
private theorem complexExponentialDecay_contDiffOn_of_weight {K : Type*} [NormedField K]
    [NormedAlgebra ℝ K] [CompleteSpace K] [LocallyCompactSpace K] [DecidableEq K]
    (m : Kˣ →ₜ* ℝ≥0ˣ) (a : ℝ) (ha : a ∈ Ioi (0 : ℝ))
    (f : ModulatedExponentialDecay m (Ioi (0 : ℝ)))
    (w : K → ℂ) (hw : ContDiff ℝ (∞ : ℕ∞ω) w)
    (hwu : ∀ u : Kˣ, w u.val = (((m u).val : ℝ) ^ a : ℝ)) :
    ContDiffOn ℝ (∞ : ℕ∞ω) zeroExtension(f.val) ({0}ᶜ : Set K) := by
  let g := modulatedExponentialDecayTwist m (Ioi (0 : ℝ)) ⟨a, ha⟩ f
  have hn (x : K) (hx : x ≠ 0) : w x ≠ 0 := by
    change w (Units.mk0 x hx).val ≠ 0
    rw [hwu]
    exact Complex.ofReal_ne_zero.mpr
      (Real.rpow_pos_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)) _).ne'
  have h := (complexExponentialDecay_contDiffOn_unitsChart g).mul (hw.contDiffOn.inv fun x hx ↦ hn x hx)
  apply h.congr
  intro x hx
  have hx0 : x ≠ 0 := hx
  let u := Units.mk0 x hx0
  simp only [dite_eq_left hx0, Pi.inv_apply]
  have hg : g.val u = w x * f.val u :=
    (modulatedExponentialDecayTwist_apply m _ _ f u).trans (by rw [← hwu]; rfl)
  change f.val u = g.val u * (w x)⁻¹
  rw [hg, mul_right_comm, mul_inv_cancel₀ (hn x hx0), one_mul]

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250.
Weighted Schwartz–Bruhat functions are smooth on the punctured complex plane
as functions of two real variables. -/
theorem complexExponentialDecay_contDiffOn (f : 𝓔(ℂ, 2, Ioi 0)) :
    ContDiffOn ℝ (∞ : ℕ∞ω) zeroExtension(f.val) ({0}ᶜ : Set ℂ) := by
  have hRe : ContDiff ℝ (∞ : ℕ∞ω) Complex.re := Complex.reCLM.contDiff
  have hIm : ContDiff ℝ (∞ : ℕ∞ω) Complex.im := Complex.imCLM.contDiff
  have hn : ContDiff ℝ (∞ : ℕ∞ω) (fun z : ℂ ↦ Complex.normSq z) := by
    simp only [Complex.normSq_apply]
    exact (hRe.mul hRe).add (hIm.mul hIm)
  apply complexExponentialDecay_contDiffOn_of_weight (archimedeanUnitModulation ℂ 2) 1
    (by norm_num : (1 : ℝ) ∈ Ioi 0) f (fun z ↦ (Complex.normSq z : ℂ))
    (Complex.ofRealCLM.contDiff.comp hn)
  intro u
  rw [archimedeanUnitModulation_apply, Real.rpow_one, Complex.normSq_eq_norm_sq]

end PuncturedLine

section ArchimedeanProduct

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

local notation "archAdd(" ι ", " κ ")" => ((ι → ℝ) × (κ → ℂ))
local notation "archMul(" ι ", " κ ")" => ((ι → ℝˣ) × (κ → ℂˣ))
local notation "archVal" => fun u ↦ (fun i ↦ (u.1 i).val, fun j ↦ (u.2 j).val)
local notation "meetsWall(" x ")" => ((∃ i, x.1 i = 0) ∨ (∃ j, x.2 j = 0))
local notation "weights(" ι ", " κ ", " I ")" =>
  ((ι → (insert 0 I : Set ℝ)) × (κ → (insert 0 I : Set ℝ)))

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

local notation "weightMap(" a ")" => LinearMap.mulLeft ℂ
  (fun u : archMul(ι, κ) ↦
    ((∏ i, ‖(u.1 i).val‖ ^ (a.1 i : ℝ)) : ℝ) *
    ((∏ j, (‖(u.2 j).val‖ ^ (2 : ℕ)) ^ (a.2 j : ℝ)) : ℝ) : archMul(ι, κ) → ℂ)

/-- Paper: Lemma 5.3.3.3, p. 252.
Every partial coordinate weight with exponents in I must yield a Schwartz–Bruhat function.
Deviation: A zero exponent encodes an omitted coordinate in (5.3.3.5), including the
unweighted condition when every coordinate is omitted. -/
def archimedeanWeightedSchwartzSubmodule (I : Set ℝ) :
    Submodule ℂ (archMul(ι, κ) → ℂ) :=
  ⨅ a : weights(ι, κ, I), (schwartzBruhatSubmodule _).comap (weightMap(a))

/-- Paper: Lemma 5.3.3.3, p. 252.
The map for a family of exponents applies its weight and returns a Schwartz–Bruhat function. -/
def archimedeanSchwartzTwist (I : Set ℝ) (a : weights(ι, κ, I)) :
    archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I →ₗ[ℂ]
      SchwartzBruhat (archMul(ι, κ)) :=
  ((weightMap(a)).comp (archimedeanWeightedSchwartzSubmodule I).subtype).codRestrict
    (schwartzBruhatSubmodule _) (fun f ↦
      Submodule.mem_comap.1 ((Submodule.mem_iInf _).1 f.property a))

/-- Paper: Lemma 5.3.3.3, p. 252.
The twist uses one power of the real norm and the corresponding power of the squared
complex norm in each coordinate. -/
theorem archimedeanSchwartzTwist_apply (I : Set ℝ) (a : weights(ι, κ, I))
    (f : archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I)
    (u : archMul(ι, κ)) :
    archimedeanSchwartzTwist I a f u =
      (↑(∏ i, ‖(u.1 i).val‖ ^ (a.1 i : ℝ)) : ℂ) *
      (↑(∏ j, (‖(u.2 j).val‖ ^ (2 : ℕ)) ^ (a.2 j : ℝ)) : ℂ) * f.val u := by
  rfl

/-- Paper: Lemma 5.3.3.3, p. 252.
On both the real and complex coordinates, choosing only zero exponents gives the
unweighted Schwartz–Bruhat space. -/
theorem archimedeanWeightedSchwartzSubmodule_singleton_zero :
    archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) {0} =
      schwartzBruhatSubmodule (archMul(ι, κ)) := by
  have hw : ∀ a : weights(ι, κ, ({0} : Set ℝ)), ∀ f : archMul(ι, κ) → ℂ, weightMap(a) f = f := by
    intro a f
    have h1 : ∀ i, (a.1 i : ℝ) = 0 := fun i ↦ by simpa using (a.1 i).property
    have h2 : ∀ j, (a.2 j : ℝ) = 0 := fun j ↦ by simpa using (a.2 j).property
    funext u
    simp [h1, h2]
  ext f
  simp only [archimedeanWeightedSchwartzSubmodule, Submodule.mem_iInf, Submodule.mem_comap]
  constructor
  · intro h
    have := h (fun _ ↦ ⟨0, by simp⟩, fun _ ↦ ⟨0, by simp⟩)
    rwa [hw] at this
  · intro h a
    rwa [hw]

/-- Paper: Lemma 5.3.3.3, p. 252.
The topology is the initial locally convex topology for all the partial weight maps into
the Schwartz–Bruhat space in (5.3.3.8). -/
abbrev ArchimedeanWeightedSchwartz (I : Set ℝ) :=
  WithGeneratingSeminorms (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I)
    (fun i : weights(ι, κ, I) ×
      {p : Seminorm ℂ (SchwartzBruhat (archMul(ι, κ))) // Continuous p} ↦
      i.2.val.comp (archimedeanSchwartzTwist I i.1))

local notation "𝓦(" I ")" => ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I

/-- Paper: Lemma 5.3.3.3, p. 252.
When there are no coordinates, the weighted Schwartz space is the scalar field. -/
theorem archimedeanWeightedSchwartz_empty_equiv (I : Set ℝ) :
    ∃ e : ArchimedeanWeightedSchwartz (ι := Empty) (κ := Empty) I ≃L[ℂ] ℂ,
      ∀ f, e f = f.val (1 : archMul(Empty, Empty)) := by sorry

-- TODO(paper-gap): The proof's integer exponents need not meet I. Use a countable
-- family of exponents in I bracketing each exponent in I, together with zero.

/-- Paper: Lemma 5.3.3.3(1), p. 252.
For an open nonempty interval the topology from the partial weight maps is Fréchet. -/
theorem archimedeanWeightedSchwartz_frechet {I : Set ℝ} (_ho : IsOpen I)
    (_hi : OrdConnected I) (_hne : I.Nonempty) : IsFrechetTVS 𝓦(I) := by sorry

/-- Paper: Lemma 5.3.3.3(1), p. 252.
For an open nonempty interval the weighted Schwartz–Bruhat space is separable. -/
theorem archimedeanWeightedSchwartz_separable {I : Set ℝ} (_ho : IsOpen I)
    (_hi : OrdConnected I) (_hne : I.Nonempty) : SeparableSpace 𝓦(I) := by sorry

/-- Paper: Lemma 5.3.3.3(1), p. 252.
For an open nonempty interval the weighted Schwartz–Bruhat space is nuclear. -/
theorem archimedeanWeightedSchwartz_nuclear {I : Set ℝ} (_ho : IsOpen I)
    (_hi : OrdConnected I) (_hne : I.Nonempty) : IsNuclearTVS 𝓦(I) := by sorry

/-- Paper: Lemma 5.3.3.3(2), p. 252.
The finite projective tensor topology is generated by seminorms with jointly continuous
pullback along the pure tensor map, as for the binary projective tensor product of §C.2.3. -/
abbrev FiniteProjectiveTensor {ι : Type*} [Fintype ι] (E : ι → Type*)
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] [∀ i, TopologicalSpace (E i)] :=
  WithGeneratingSeminorms (⨂[ℂ] i, E i)
    (fun p : {p : Seminorm ℂ (⨂[ℂ] i, E i) //
      Continuous (fun f : ∀ i, E i ↦ p (⨂ₜ[ℂ] i, f i))} ↦ p.val)

/-- Paper: Lemma 5.3.3.3(2), p. 252.
With no factors the projective tensor product identifies topologically with the scalars
and the empty pure tensor maps to one. -/
theorem finiteProjectiveTensor_empty_equiv :
    ∃ e : FiniteProjectiveTensor (fun _ : Empty ↦ ℂ) ≃L[ℂ] ℂ,
      e (⨂ₜ[ℂ] i : Empty, (0 : ℂ)) = 1 := by
  let X := ⨂[ℂ] _i : Empty, ℂ
  let P : SeminormFamily ℂ X
      {p : Seminorm ℂ X // Continuous (fun f : Empty → ℂ ↦ p (⨂ₜ[ℂ] i, f i))} := fun p ↦ p.val
  let l : WithGeneratingSeminorms X P ≃ₗ[ℂ] ℂ := PiTensorProduct.isEmptyEquiv Empty
  have hP := withGeneratingSeminorms_spec X P
  have : ContinuousSMul ℂ (WithGeneratingSeminorms X P) := hP.continuousSMul
  -- The norm of the scalar coordinate is one of the generating seminorms.
  have hl : Continuous l := by
    let q : Seminorm ℂ X := (normSeminorm ℂ ℂ).comp (PiTensorProduct.isEmptyEquiv Empty).toLinearMap
    have hq : Continuous (fun f : Empty → ℂ ↦ q (⨂ₜ[ℂ] i, f i)) := continuous_of_discreteTopology
    refine WithSeminorms.continuous_normedSpace_rng ℂ hP l.toLinearMap
      ⟨{⟨q, hq⟩}, 1, Seminorm.le_def.mpr fun x ↦ ?_⟩
    have hx : (({⟨q, hq⟩} : Finset _).sup P) x = q x :=
      congrArg (fun p : Seminorm ℂ X ↦ p x) Finset.sup_singleton
    exact le_of_eq (hx.symm.trans (one_smul ℝ≥0 _).symm)
  have hl' : Continuous l.symm := by
    have hsymm : (l.symm : ℂ → WithGeneratingSeminorms X P) = fun c ↦ c • l.symm 1 := by
      funext c
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [hsymm]
    fun_prop
  exact ⟨⟨l, hl, hl'⟩, PiTensorProduct.isEmptyEquiv_apply_tprod Empty _⟩

-- TODO(paper-gap): If 0 ∉ I the factors S_I need not be unweighted Schwartz–Bruhat,
-- whereas (5.3.3.6) requires this. Include the unweighted twist on each factor.

set_option maxHeartbeats 600000 in
/-- Paper: Lemma 5.3.3.3(2), p. 252.
The canonical map multiplies pure factors evaluated in their own coordinates and
extends to a linear homeomorphism on the completion.
Deviation: The factors include weight zero for the unweighted condition in (5.3.3.6).
When zero already belongs to I these are the factors printed in the paper. -/
theorem archimedeanWeightedSchwartz_tensor {I : Set ℝ} (_ho : IsOpen I)
    (_hi : OrdConnected I) (_hne : I.Nonempty) :
    let J := insert 0 I
    let R := ModulatedExponentialDecay (archimedeanUnitModulation ℝ 1) J
    let C := ModulatedExponentialDecay (archimedeanUnitModulation ℂ 2) J
    let T := ProjectiveTensor (FiniteProjectiveTensor (fun _ : ι ↦ R))
      (FiniteProjectiveTensor (fun _ : κ ↦ C))
    ∃ L : T →L[ℂ] 𝓦(I), IsEmbedding L ∧
      (∀ (f : ι → R) (g : κ → C) (u : archMul(ι, κ)),
        (L ((⨂ₜ[ℂ] i, f i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, g j))).val u =
          (∏ i, (f i).val (u.1 i)) * ∏ j, (g j).val (u.2 j)) ∧
      ∃ e : UniformSpace.Completion T ≃L[ℂ] 𝓦(I), ∀ z : T, e z = L z := by sorry

local notation "jet(" n ", " x ", " v ")" =>
  (fun f : 𝓢(archAdd(ι, κ), ℂ) ↦ iteratedFDeriv ℝ n (f : archAdd(ι, κ) → ℂ) x v)

/-- Paper: Lemma 5.3.3.3(3), p. 252.
Evaluation of the real derivative of order n at a point and a tuple of directions
is complex-linear in the Schwartz function. -/
theorem archimedeanSchwartzJet_isLinear (n : ℕ) (x : archAdd(ι, κ))
    (v : Fin n → archAdd(ι, κ)) : IsLinearMap ℂ (jet(n, x, v)) := by
  constructor
  · intro f g
    change iteratedFDeriv ℝ n ((f : _ → ℂ) + (g : _ → ℂ)) x v = _
    rw [iteratedFDeriv_add_apply (f.smooth n).contDiffAt (g.smooth n).contDiffAt,
      ContinuousMultilinearMap.add_apply]
  · intro a f
    change iteratedFDeriv ℝ n (a • (f : _ → ℂ)) x v = _
    rw [iteratedFDeriv_const_smul_apply (f.smooth n).contDiffAt, ContinuousMultilinearMap.smul_apply]

/-- Paper: Lemma 5.3.3.3(3), p. 252.
The flat Schwartz subspace is the intersection of the kernels of all jets on the
union of the coordinate hyperplanes.
Deviation: Full real Fréchet derivatives express the equivalent vanishing of the
mixed ordinary and Wirtinger derivatives. The coordinates are the product field coordinates. -/
def archimedeanFlatSchwartz : Submodule ℂ 𝓢(archAdd(ι, κ), ℂ) :=
  ⨅ x : {x : archAdd(ι, κ) // meetsWall(x)}, ⨅ n : ℕ, ⨅ v : Fin n → archAdd(ι, κ),
    LinearMap.ker ((archimedeanSchwartzJet_isLinear n x.val v).mk' _)

/-- Paper: Lemma 5.3.3.3(3), p. 252.
For one real factor the jet conditions recover the real flat subspace of §5.3.2. -/
theorem archimedeanFlatSchwartz_one_real :
    ∃ e : ↥(archimedeanFlatSchwartz (ι := Unit) (κ := Empty)) ≃L[ℂ] ↥realSchwartzFlatAtOrigin,
      ∀ f (x : ℝ), (e f).val x = f.val (fun _ ↦ x, fun j ↦ Empty.elim j) := by sorry

/-- Paper: Lemma 5.3.3.3(3), p. 252.
For one complex factor the real jet conditions recover the mixed Wirtinger conditions of §5.3.2. -/
theorem archimedeanFlatSchwartz_one_complex :
    ∃ e : ↥(archimedeanFlatSchwartz (ι := Empty) (κ := Unit)) ≃L[ℂ] ↥complexSchwartzFlatAtOrigin,
      ∀ f (z : ℂ), (e f).val z = f.val (fun i ↦ Empty.elim i, fun _ ↦ z) := by sorry

/-- Paper: Lemma 5.3.3.3(3), p. 252.
Schwartz functions supported away from every coordinate hyperplane are flat along them. -/
theorem mem_archimedeanFlatSchwartz_of_tsupport (f : 𝓢(archAdd(ι, κ), ℂ))
    (_hf : Disjoint (tsupport f) {x : archAdd(ι, κ) | meetsWall(x)}) :
    f ∈ archimedeanFlatSchwartz := by
  simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x n v
  have hx : x.val ∉ tsupport f := fun h ↦ Set.disjoint_left.mp _hf h x.2
  have hev : (f : archAdd(ι, κ) → ℂ) =ᶠ[nhds x.val] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  have h0 : iteratedFDeriv ℝ n (f : archAdd(ι, κ) → ℂ) x.val =
      iteratedFDeriv ℝ n (0 : archAdd(ι, κ) → ℂ) x.val :=
    (hev.iteratedFDeriv ℝ n).self_of_nhds
  simp [IsLinearMap.mk', h0]

/-- Paper: Lemma 5.3.3.3(3), p. 252.
The subspace of Schwartz functions with all jets zero on the coordinate hyperplanes is closed. -/
theorem archimedeanFlatSchwartz_isClosed :
    IsClosed (↑(archimedeanFlatSchwartz (ι := ι) (κ := κ)) : Set 𝓢(archAdd(ι, κ), ℂ)) := by
  simp only [archimedeanFlatSchwartz, Submodule.coe_iInf]
  refine isClosed_iInter fun x ↦ isClosed_iInter fun n ↦ isClosed_iInter fun v ↦ ?_
  let J := (TemperedDistribution.delta x.val).comp
    (LineDeriv.iteratedLineDerivOpCLM ℂ 𝓢(archAdd(ι, κ), ℂ) v)
  have hJ : (archimedeanSchwartzJet_isLinear n x.val v).mk' _ = J.toLinearMap := by
    ext f
    exact SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv.symm
  rw [hJ]
  exact J.isClosed_ker

-- TODO(paper-gap): The estimates (5.3.3.21)–(5.3.3.23) fail for bumps
-- supported close to, but away from, the origin.

/-- Paper: Lemma 5.3.3.3(3), p. 253.
Restriction to the product of the punctured lines identifies flat Schwartz functions
with the all-exponent weighted space. The inverse extends by zero. -/
theorem archimedeanFlatSchwartz_restrict_equiv :
    ∃ e : ↥(archimedeanFlatSchwartz (ι := ι) (κ := κ)) ≃L[ℂ] 𝓦(univ),
      ∀ (f : archimedeanFlatSchwartz) (u : archMul(ι, κ)), (e f).val u = f.val (archVal u) :=
  by sorry

/-- Paper: Lemma 5.3.3.3(3), p. 253.
A continuous quasi-character on the product of punctured fields acts by multiplication
through a unique linear homeomorphism of the flat Schwartz space. -/
theorem archimedeanFlatSchwartz_quasiCharacter_mul (c : QuasiCharacter (archMul(ι, κ))) :
    ∃! M : ↥(archimedeanFlatSchwartz (ι := ι) (κ := κ)) ≃L[ℂ]
        ↥(archimedeanFlatSchwartz (ι := ι) (κ := κ)),
      ∀ (f : archimedeanFlatSchwartz) (u : archMul(ι, κ)),
        (M f).val (archVal u) = c u * f.val (archVal u) := by sorry

end ArchimedeanProduct

section ArchimedeanMellin

local notation "realProfile(" f ", " ε ")" =>
  (fun t : ℝ ↦ f t + (-1 : ℂ) ^ (ε).val * f (-t))
local notation "unitAngle(" θ ")" => Complex.exp ((θ : ℂ) * Complex.I)
local notation "complexProfile(" f ", " n ")" =>
  (fun t : ℝ ↦ ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (unitAngle(θ)) ^ n * f ((Real.sqrt t : ℂ) * unitAngle(θ)))

/-- Paper: Proposition 5.3.3.4, p. 258.
The real Mellin integral converges on the right half-plane and has a unique
meromorphic continuation for each sign parity. -/
theorem realArchimedeanMellin_existsUnique (f : 𝓢(ℝ, ℂ)) (ε : Fin 2) :
    ∃! L : ℂ → ℂ, MeromorphicNFOn L univ ∧
      ∀ s : ℂ, 0 < s.re → HasMellin (realProfile(f, ε)) s (L s) := by sorry

/-- Paper: Proposition 5.3.3.4, p. 258.
The real local Mellin transform is the meromorphic continuation of the weighted
integral over the two signs in (5.3.3.26). -/
def realArchimedeanMellin (f : 𝓢(ℝ, ℂ)) (ε : Fin 2) : ℂ → ℂ :=
  (realArchimedeanMellin_existsUnique f ε).exists.choose

/-- Paper: Proposition 5.3.3.4, p. 258.
The positive half-plane gives the defining integral for the real Mellin transform. -/
theorem realArchimedeanMellin_eq_integral (f : 𝓢(ℝ, ℂ)) (ε : Fin 2)
    (s : ℂ) (_hs : 0 < s.re) :
    realArchimedeanMellin f ε s = mellin (realProfile(f, ε)) s :=
  ((realArchimedeanMellin_existsUnique f ε).exists.choose_spec.2 s _hs).2.symm

/-- Paper: Proposition 5.3.3.4, p. 258.
The complex Mellin integral converges on the right half-plane and has a unique
meromorphic continuation for each integral angular weight.
Deviation: The angular measure is dθ in the norm coordinate t = |z|², as in §3.3.
The printed 2 dθ would double the Tamagawa integral. -/
theorem complexArchimedeanMellin_existsUnique (f : 𝓢(ℂ, ℂ)) (n : ℤ) :
    ∃! L : ℂ → ℂ, MeromorphicNFOn L univ ∧
      ∀ s : ℂ, 0 < s.re → HasMellin (complexProfile(f, n)) s (L s) := by sorry

/-- Paper: Proposition 5.3.3.4, p. 258.
The complex local Mellin transform is the meromorphic continuation of the angular
and radial integral in (5.3.3.26).
Deviation: The angular measure is normalized as in §3.3. -/
def complexArchimedeanMellin (f : 𝓢(ℂ, ℂ)) (n : ℤ) : ℂ → ℂ :=
  (complexArchimedeanMellin_existsUnique f n).exists.choose

/-- Paper: Proposition 5.3.3.4, p. 258.
The positive half-plane gives the defining integral for the complex Mellin transform.
Deviation: The angular measure is normalized as in §3.3. -/
theorem complexArchimedeanMellin_eq_integral (f : 𝓢(ℂ, ℂ)) (n : ℤ)
    (s : ℂ) (_hs : 0 < s.re) :
    complexArchimedeanMellin f n s = mellin (complexProfile(f, n)) s :=
  ((complexArchimedeanMellin_existsUnique f n).exists.choose_spec.2 s _hs).2.symm

/-- Paper: Proposition 5.3.3.4, p. 258.
In the real field model the local zeta function of §3.3 is the two-sign Mellin transform
at the radial exponent and parity of the given quasi-character. -/
theorem realArchimedeanMellin_eq_infiniteLocalIdelicZFunction
    {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (f : SchwartzBruhat (Multiplicative w.Completion)) :
    ∃ g : 𝓢(ℝ, ℂ), (∀ x : w.Completion,
      g (InfinitePlace.Completion.ringEquivRealOfIsReal hw x) = f (Multiplicative.ofAdd x)) ∧
      ∀ c : QuasiCharacter w.Completionˣ,
        let p := (realLocalEulerParameters w hw c).exists.choose
        infiniteLocalIdelicZFunction w f c = realArchimedeanMellin g p.2 p.1 := by sorry

/-- Paper: Proposition 5.3.3.4, p. 258.
In the complex field model the local zeta function of §3.3 is the angular Mellin transform
at the squared-norm exponent and angular weight of the given quasi-character. -/
theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction
    {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (f : SchwartzBruhat (Multiplicative w.Completion)) :
    ∃ g : 𝓢(ℂ, ℂ), (∀ x : w.Completion,
      g (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw x) = f (Multiplicative.ofAdd x)) ∧
      ∀ c : QuasiCharacter w.Completionˣ,
        let p := (complexLocalEulerParameters w hw c).exists.choose
        infiniteLocalIdelicZFunction w f c = complexArchimedeanMellin g p.2 p.1 := by sorry

local notation "realMonomial(" n ")" => SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ n)
local notation "complexMonomial(" p ", " q ")" =>
  SchwartzMap.smulLeftCLM ℂ (fun z : ℂ ↦ z ^ p * star z ^ q)
local notation "shiftParity(" ε ", " n ")" => Fin.ofNat 2 ((ε).val + n)
local notation "rhoReal(" ε ", " s ")" =>
  ((Complex.I ^ (ε).val) *
    (Complex.Gammaℝ (s + (ε).val) / Complex.Gammaℝ (1 - s + (ε).val)))
local notation "rhoComplex(" n ", " s ")" =>
  ((Complex.I ^ (n).natAbs) *
    (Complex.Gammaℂ (s + ((n).natAbs : ℂ) / 2) / Complex.Gammaℂ (1 - s + ((n).natAbs : ℂ) / 2)))

/-- Translating the argument preserves meromorphic normal form on the whole plane. -/
private theorem archimedeanMellin_meromorphicNFOn_comp_add_const {L : ℂ → ℂ}
    (hL : MeromorphicNFOn L univ) (d : ℂ) : MeromorphicNFOn (fun s ↦ L (s + d)) univ := fun _ _ ↦
  (meromorphicNFAt_comp_add_const_iff_meromorphicNFAt (f := L)).mpr (hL (mem_univ _))

-- TODO(paper-gap): (5.3.3.28) drops M_{x^n} on the left. Its proof supplies the multiplier.

/-- Paper: Proposition 5.3.3.4(1), p. 258.
Multiplying by xⁿ shifts the real Mellin exponent by n and shifts the sign character by
the parity of n.
Deviation: The multiplier on the left is restored from (5.3.3.32)–(5.3.3.34). -/
theorem realArchimedeanMellin_monomial (n : ℕ) (ε : Fin 2) (f : 𝓢(ℝ, ℂ)) :
    realArchimedeanMellin (realMonomial(n) f) ε =
      fun s ↦ realArchimedeanMellin f shiftParity(ε, n) (s + n) := by
  have hspec := (realArchimedeanMellin_existsUnique f shiftParity(ε, n)).exists.choose_spec
  have hg : (fun x : ℝ ↦ (x : ℂ) ^ n).HasTemperateGrowth := Complex.hasTemperateGrowth_ofReal.pow n
  -- On the profiles, the monomial is the Mellin shift by n with the parity moved by n.
  have hprofile : realProfile(realMonomial(n) f, ε) =
      fun t : ℝ ↦ (t : ℂ) ^ (n : ℂ) • realProfile(f, shiftParity(ε, n)) t := by
    funext t
    have hsign : (-1 : ℂ) ^ (shiftParity(ε, n)).val = (-1) ^ ε.val * (-1) ^ n := by
      rw [Fin.val_ofNat, ← neg_one_pow_eq_pow_mod_two, pow_add]
    change SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ n) f t +
        (-1 : ℂ) ^ ε.val * SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ n) f (-t) =
      (t : ℂ) ^ (n : ℂ) • (f t + (-1 : ℂ) ^ (shiftParity(ε, n)).val * f (-t))
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.smulLeftCLM_apply_apply hg, hsign,
      Complex.cpow_natCast, Complex.ofReal_neg, neg_pow]
    simp only [smul_eq_mul]
    ring
  refine (realArchimedeanMellin_existsUnique (realMonomial(n) f) ε).unique
    (realArchimedeanMellin_existsUnique (realMonomial(n) f) ε).exists.choose_spec
    ⟨archimedeanMellin_meromorphicNFOn_comp_add_const hspec.1 n, fun s hs ↦ ?_⟩
  have hsn : 0 < (s + (n : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    positivity
  have h := hspec.2 (s + n) hsn
  rw [hprofile]
  exact ⟨MellinConvergent.cpow_smul.mpr h.1, (mellin_cpow_smul _ s n).trans h.2⟩

/-- Paper: Proposition 5.3.3.4(1), p. 258.
The real monomial Mellin transform satisfies the Fourier relation at the shifted
exponent and parity. The product is understood as a meromorphic identity. -/
theorem realArchimedeanMellin_monomial_functionalEquation (n : ℕ) (ε : Fin 2) (f : 𝓢(ℝ, ℂ)) :
    ∀ᶠ s : ℂ in codiscrete ℂ,
      let a := shiftParity(ε, n)
      let t := s + (n : ℂ)
      realArchimedeanMellin (realMonomial(n) f) ε s =
        rhoReal(a, t) * realArchimedeanMellin (𝓕 f) a (1 - t) := by sorry

/-- Paper: Proposition 5.3.3.4(2), p. 258.
Multiplying by zᵖ times the qth power of its conjugate shifts the Mellin exponent
by (p+q)/2 and the angular weight by p−q. -/
theorem complexArchimedeanMellin_monomial (p q : ℕ) (n : ℤ) (f : 𝓢(ℂ, ℂ)) :
    complexArchimedeanMellin (complexMonomial(p, q) f) n =
      fun s ↦ complexArchimedeanMellin f (n + (p : ℤ) - q) (s + ((p : ℂ) + q) / 2) := by
  have hspec := (complexArchimedeanMellin_existsUnique f (n + (p : ℤ) - q)).exists.choose_spec
  have hg : (fun z : ℂ ↦ z ^ p * star z ^ q).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.id'.pow p).mul (Complex.conjCLE.hasTemperateGrowth.pow q)
  have hE (θ : ℝ) : unitAngle(θ) ≠ 0 := Complex.exp_ne_zero _
  have hstar (θ : ℝ) : star (unitAngle(θ)) = (unitAngle(θ))⁻¹ := by
    rw [← Complex.exp_neg, Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp
  -- For positive t the monomial contributes the radial power t^((p+q)/2) and the angular
  -- weight p - q.
  have hprofile : EqOn (complexProfile(complexMonomial(p, q) f, n))
      (fun t : ℝ ↦ (t : ℂ) ^ (((p : ℂ) + q) / 2) • complexProfile(f, n + (p : ℤ) - q) t)
      (Ioi 0) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hroot : (Real.sqrt t : ℂ) ^ (p + q) = (t : ℂ) ^ (((p : ℂ) + q) / 2) := by
      have hr : Real.sqrt t ^ (p + q) = t ^ (((p : ℝ) + q) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
        congr 1
        push_cast
        ring
      rw [← Complex.ofReal_pow, hr, Complex.ofReal_cpow ht0.le]
      congr 1
      push_cast
      ring
    change (∫ θ in (0 : ℝ)..(2 * Real.pi), unitAngle(θ) ^ n *
        SchwartzMap.smulLeftCLM ℂ (fun z : ℂ ↦ z ^ p * star z ^ q) f
          ((Real.sqrt t : ℂ) * unitAngle(θ))) =
      (t : ℂ) ^ (((p : ℂ) + q) / 2) • ∫ θ in (0 : ℝ)..(2 * Real.pi),
        unitAngle(θ) ^ (n + (p : ℤ) - q) * f ((Real.sqrt t : ℂ) * unitAngle(θ))
    rw [smul_eq_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ ↦ ?_
    have hz : star ((Real.sqrt t : ℂ) * unitAngle(θ)) = (Real.sqrt t : ℂ) * (unitAngle(θ))⁻¹ := by
      rw [star_mul', hstar]
      congr 1
      exact Complex.conj_ofReal _
    change unitAngle(θ) ^ n *
        SchwartzMap.smulLeftCLM ℂ (fun z : ℂ ↦ z ^ p * star z ^ q) f
          ((Real.sqrt t : ℂ) * unitAngle(θ)) =
      (t : ℂ) ^ (((p : ℂ) + q) / 2) *
        (unitAngle(θ) ^ (n + (p : ℤ) - q) * f ((Real.sqrt t : ℂ) * unitAngle(θ)))
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul, hz, ← hroot, mul_pow, mul_pow,
      pow_add, zpow_sub₀ (hE θ), zpow_add₀ (hE θ), zpow_natCast, zpow_natCast, inv_pow]
    ring
  refine (complexArchimedeanMellin_existsUnique (complexMonomial(p, q) f) n).unique
    (complexArchimedeanMellin_existsUnique (complexMonomial(p, q) f) n).exists.choose_spec
    ⟨archimedeanMellin_meromorphicNFOn_comp_add_const hspec.1 _, fun s hs ↦ ?_⟩
  have hsa : 0 < (s + ((p : ℂ) + q) / 2).re := by
    have hre : (((p : ℂ) + q) / 2).re = ((p : ℝ) + q) / 2 := by
      rw [show ((p : ℂ) + q) / 2 = ((((p : ℝ) + q) / 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
    rw [Complex.add_re, hre]
    positivity
  have h := hspec.2 _ hsa
  have hmul : EqOn
      (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • complexProfile(complexMonomial(p, q) f, n) t)
      (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) •
        ((t : ℂ) ^ (((p : ℂ) + q) / 2) • complexProfile(f, n + (p : ℤ) - q) t)) (Ioi 0) :=
    fun t ht ↦ congrArg (fun w : ℂ ↦ (t : ℂ) ^ (s - 1) • w) (hprofile ht)
  exact ⟨IntegrableOn.congr_fun (MellinConvergent.cpow_smul.mpr h.1) hmul.symm measurableSet_Ioi,
    (setIntegral_congr_fun measurableSet_Ioi hmul).trans
      ((mellin_cpow_smul _ s (((p : ℂ) + q) / 2)).trans h.2)⟩

-- TODO(paper-gap): The complex phase in (5.3.3.25) disagrees with the trace-pairing Fourier
-- transform for nontrivial angular weights. Use the phase from §3.3, per ERRATA I91.

/-- Paper: Proposition 5.3.3.4(2), p. 258.
The complex monomial Mellin transform satisfies the Fourier relation at the shifted
exponent and angular weight. The trace-pairing transform is the Euclidean Fourier
transform evaluated at twice the conjugate argument and multiplied by the self-dual mass factor.
Deviation: The phase is i to the absolute angular weight, as in ERRATA I91. -/
theorem complexArchimedeanMellin_monomial_functionalEquation (p q : ℕ) (n : ℤ)
    (f : 𝓢(ℂ, ℂ)) :
    ∃ fHat : 𝓢(ℂ, ℂ), (∀ z : ℂ, fHat z = 2 * (𝓕 f) (2 * star z)) ∧
      ∀ᶠ s : ℂ in codiscrete ℂ,
        let k := n + (p : ℤ) - q
        let t := s + ((p : ℂ) + q) / 2
        complexArchimedeanMellin (complexMonomial(p, q) f) n s =
          rhoComplex(k, t) * complexArchimedeanMellin fHat (-k) (1 - t) := by sorry

end ArchimedeanMellin

section SAdele

open Classical

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "Aₛ" => SAdeleRing F S
local notation "ℬₛ" => ℬ(Aₛ)
local notation "Jₛ" => SIdeleQuotient F S
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "J₁" => (mₛ).ker
local notation "Xₛ" => QuasiCharacter Jₛ
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "chartₛ(" χ ")" =>
  quasiCharacterNormTwist (G := Jₛ) mₛ (isProperMap_sIdeleQuotientNorm F S).continuous
    ((circleToComplex).comp (χ))
local notation "χ₁(" χ ")" =>
  ((χ : Jₛ →ₜ* Circle).comp
    (⟨((mₛ).ker).subtype, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ) : PontryaginDual J₁)
local notation "thetaAt(" χ ")" => sLocalHomogeneousAdelicThetaLinearMap F S (χ)
local notation "A∞" => InfiniteAdeleRing F
local notation "RealPlaces" => {w : InfinitePlace F // w.IsReal}
local notation "ComplexPlaces" => {w : InfinitePlace F // w.IsComplex}
local notation "ArchCoordinates" => ((RealPlaces → ℝ) × (ComplexPlaces → ℂ))
local notation "RealModels" => ((w : RealPlaces) →
  {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
local notation "ComplexModels" => ((w : ComplexPlaces) →
  {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)})
local notation "assemble(" r ", " c ", " x ")" =>
  (show A∞ from fun w ↦ if h : w.IsReal then ((r ⟨w, h⟩).val.symm) ((x).1 ⟨w, h⟩)
    else ((c ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp h⟩).val.symm)
      ((x).2 ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp h⟩))

-- TODO(paper-gap): In (5.3.4.1), (5.3.4.7) and (5.3.4.15), the finite
-- zero-extension factors must be compactly supported locally constant tests on the
-- units. Remark 2.1.2.1 distinguishes these from the full multiplicative Schwartz
-- space. On Q_p, the sequence p^(-k) on shells of valuation k ≥ 0 is Schwartz on Z,
-- but its zero extension is not locally constant at zero.

/-- Paper: Definition 5.3.4.1, p. 259.
A function on the unit group has an additive Schwartz extension vanishing at zero
exactly when it is locally constant and compactly supported there.
Deviation: The finite punctured test space in (5.3.4.1) is interpreted as
compactly supported locally constant tests, consistently with Remark 2.1.2.1. -/
theorem exists_finitePlaceSchwartz_zeroExtension_iff (v : V) (h : (v.adicCompletion F)ˣ → ℂ) :
    (∃ f : ℬ(v.adicCompletion F), f (Multiplicative.ofAdd 0) = 0 ∧
      ∀ u : (v.adicCompletion F)ˣ, f (Multiplicative.ofAdd u.val) = h u) ↔
      IsLocallyConstant h ∧ HasCompactSupport h := by
  classical
  let K := v.adicCompletion F
  let j : Kˣ → K := Units.val
  have hj : IsOpenEmbedding j := Units.isOpenEmbedding_val
  have hn : (0 : K) ∉ Set.range j := by
    rintro ⟨u, hu⟩
    exact u.ne_zero hu
  constructor
  · rintro ⟨f, hzero, hh⟩
    let g : K → ℂ := fun x ↦ f (Multiplicative.ofAdd x)
    have hg := (mem_finitePlaceSchwartz_iff F v g).mp ⟨f, fun _ ↦ rfl⟩
    have he : h = g ∘ j := funext fun u ↦ (hh u).symm
    refine ⟨he.symm ▸ hg.1.comp_continuous hj.continuous, ?_⟩
    have hc : IsCompact (Function.support g) := by
      have hs : IsClosed (Function.support g) := (hg.1.isOpen_fiber 0).isClosed_compl
      simpa only [tsupport, hs.closure_eq] using (show IsCompact (tsupport g) from hg.2)
    have hr : Function.support g ⊆ Set.range j := by
      intro x hx
      have hx0 : x ≠ 0 := fun h ↦ hx (h ▸ hzero)
      exact ⟨Units.mk0 x hx0, rfl⟩
    apply HasCompactSupport.of_support_subset_isCompact
      ((hj.isEmbedding.isInducing.isCompact_preimage_iff hr).2 hc)
    intro u hu
    exact fun hz ↦ hu ((hh u).symm.trans hz)
  · rintro ⟨hl, hc⟩
    let g : K → ℂ := Function.extend j h (fun _ ↦ 0)
    have he (u : Kˣ) : g (j u) = h u := hj.injective.extend_apply _ _ _
    have hz {x : K} (hx : x ∉ Set.range j) : g x = 0 :=
      Function.extend_apply' _ _ _ hx
    have hk : IsCompact (j '' tsupport h) := hc.image hj.continuous
    have hs : Function.support g ⊆ j '' tsupport h := by
      intro x hx
      by_cases hr : x ∈ Set.range j
      · obtain ⟨u, rfl⟩ := hr
        exact ⟨u, subset_tsupport h (fun hu ↦ hx ((he u).trans hu)), rfl⟩
      · exact False.elim (hx (hz hr))
    have hl' : IsLocallyConstant g := by
      rw [IsLocallyConstant.iff_exists_open]
      intro x
      by_cases hr : x ∈ Set.range j
      · obtain ⟨u, rfl⟩ := hr
        refine ⟨j '' {w | h w = h u}, hj.isOpenMap _ (hl.isOpen_fiber _), ⟨u, rfl, rfl⟩, ?_⟩
        rintro _ ⟨w, hw, rfl⟩
        exact (he w).trans (hw.trans (he u).symm)
      · refine ⟨(j '' tsupport h)ᶜ, hk.isClosed.isOpen_compl, ?_, ?_⟩
        · rintro ⟨u, _, hu⟩
          exact hr ⟨u, hu⟩
        · intro y hy
          exact (not_not.mp (fun hy' ↦ hy (hs hy'))).trans (hz hr).symm
    obtain ⟨f, hf⟩ :=
      (mem_finitePlaceSchwartz_iff F v g).mpr ⟨hl', HasCompactSupport.of_support_subset_isCompact hk hs⟩
    exact ⟨f, (hf 0).trans (hz hn), fun u ↦ (hf (j u)).trans (he u)⟩

/-- Paper: Definition 5.3.4.1, p. 259.
The finite-place conditions are the kernels of evaluation at adeles with a zero
coordinate at one of the selected finite places. -/
def sAdeleFiniteZeroSchwartz (S T : Finset V) : Submodule ℂ ℬ(SAdeleRing F S) :=
  ⨅ x : {x : SAdeleRing F S // ∃ v : S, v.val ∈ T ∧ x.2 v = 0},
    LinearMap.ker ((LinearMap.proj (Multiplicative.ofAdd x.val)).comp
      (schwartzBruhatSubmodule (Multiplicative (SAdeleRing F S))).subtype)

/-- Paper: Definition 5.3.4.1, p. 259.
Passing from a Schwartz function in archimedean coordinates to its underlying
function is complex-linear. -/
theorem archimedeanSchwartz_coe_isLinear :
    IsLinearMap ℂ (fun f : 𝓢(ArchCoordinates, ℂ) ↦ (f : ArchCoordinates → ℂ)) :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- Paper: Definition 5.3.4.1, p. 259.
The polar-free subspace imposes flatness on every archimedean slice and vanishing
at a zero coordinate at every finite place.
Deviation: The finite punctured factors in (5.3.4.1) are compactly supported tests on
the units. The subspace has the topology inherited from the S-adelic Schwartz space
of Proposition 2.1.4.1, which uses the inductive archimedean–finite tensor topology.
The span identity below is algebraic. The projective topology in print is generally coarser. -/
def sAdelePolarFree (S : Finset V) (r : RealModels) (c : ComplexModels) :
    Submodule ℂ ℬ(SAdeleRing F S) :=
  sAdeleFiniteZeroSchwartz S S ⊓
    ⨅ y : (v : S) → v.val.adicCompletion F,
      let flat := (archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)).map
        ((archimedeanSchwartz_coe_isLinear (F := F)).mk' _)
      let slice := LinearMap.funLeft ℂ ℂ (fun x : ArchCoordinates ↦
        Multiplicative.ofAdd (assemble(r, c, x), y))
      flat.comap (slice.comp (schwartzBruhatSubmodule (Multiplicative (SAdeleRing F S))).subtype)

/-- Paper: Definition 5.3.4.1, p. 259.
For a pure tensor with nonzero factors, finite-coordinate vanishing is exactly
vanishing at zero of each factor selected by T. -/
theorem sAdeleFiniteZeroSchwartz_tmul_iff (T : Finset V)
    (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)) (_hf : f ≠ 0)
    (_hg : ∀ v, g v ≠ 0) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v)) ∈ sAdeleFiniteZeroSchwartz S T ↔
      ∀ v : S, v.val ∈ T → g v (Multiplicative.ofAdd 0) = 0 := by sorry

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The selected finite zero-coordinate conditions cut out the span in (5.3.4.15).
Deviation: At the selected places its factors are the zero extensions of compactly
supported locally constant tests on the unit group. -/
theorem sAdeleFiniteZeroSchwartz_eq_span_tmul (T : Finset V) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    sAdeleFiniteZeroSchwartz S T = Submodule.span ℂ {h : ℬₛ |
      ∃ (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)),
        (∀ v : S, v.val ∈ T → g v (Multiplicative.ofAdd 0) = 0) ∧
        e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v)) = h} := by sorry

/-- Paper: Definition 5.3.4.1, p. 259.
The slice definition equals the span of the corrected pure tensors in (5.3.4.1). Their
archimedean factor is flat and their finite factors vanish at zero. -/
theorem sAdelePolarFree_eq_span_tmul (r : RealModels) (c : ComplexModels) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    sAdelePolarFree S r c = Submodule.span ℂ {h : ℬₛ |
      ∃ (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)),
        (∃ f₀ : archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces),
          ∀ x : ArchCoordinates, f₀.val x = f (Multiplicative.ofAdd (assemble(r, c, x)))) ∧
        (∀ v : S, g v (Multiplicative.ofAdd 0) = 0) ∧
        e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v)) = h} := by sorry

/-- Paper: Lemma 5.3.4.2(1), p. 260.
The polar-free functions form a closed subspace in the S-adelic Schwartz–Bruhat topology. -/
theorem sAdelePolarFree_isClosed (r : RealModels) (c : ComplexModels) :
    IsClosed (↑(sAdelePolarFree S r c) : Set ℬₛ) := by sorry

/-- Paper: Lemma 5.3.4.2(1), p. 260.
Inverse left translation by an S-idele preserves the polar-free subspace. -/
theorem sAdelePolarFree_translate (r : RealModels) (c : ComplexModels)
    (g : Aₛˣ) (f : ℬₛ) (_hf : f ∈ sAdelePolarFree S r c) :
    schwartzBruhatUnitTranslate g f ∈ sAdelePolarFree S r c := by sorry

/-- Paper: Lemma 5.3.4.2(1), p. 260.
The polar-free subspace is independent of the archimedean field identifications. -/
theorem sAdelePolarFree_eq_of_models (r r' : RealModels) (c c' : ComplexModels) :
    sAdelePolarFree S r c = sAdelePolarFree S r' c' := by sorry

-- TODO(paper-gap): The proof of (2) starts from entireness and concludes local vanishing.
-- Restricted local characters are coupled by the S-units, and a pole can cancel against
-- a zero of a different factor. The stated implication goes in the other direction.

/-- Paper: Lemma 5.3.4.2(2), p. 260.
The zeta transform of a polar-free test is entire on every norm-twist component. -/
theorem sLocalIdelicZFunction_entire_of_polarFree (r : RealModels) (c : ComplexModels)
    (f : ℬₛ) (_hf : f ∈ sAdelePolarFree S r c) (χ : PontryaginDual Jₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalIdelicZFunction f (chartₛ(χ) s)) univ := by sorry

/-- Paper: Lemma 5.3.4.2(3), p. 260.
A continuous quasi-character of the S-ideles trivial on S-units acts on polar-free
functions by pointwise multiplication and defines a linear homeomorphism.
The character is given on the S-idele quotient. -/
theorem sAdelePolarFree_quasiCharacter_mul (r : RealModels) (c : ComplexModels) (b : Xₛ) :
    ∃ M : ↥(sAdelePolarFree S r c) ≃L[ℂ] ↥(sAdelePolarFree S r c),
      ∀ f (g : Aₛˣ), (M f).val (Multiplicative.ofAdd g.val) =
        b (QuotientGroup.mk g) * f.val (Multiplicative.ofAdd g.val) := by sorry

-- TODO(paper-gap): In (5.3.4.9), the summation index m_v does not occur in the summand.
-- Norm-one class representatives with archimedean component one need not exist.

/-- Paper: Lemma 5.3.4.3, p. 261.
Every log-Schwartz function decaying at all real exponents lifts to a polar-free test
whose trivial homogeneous theta function is the given radial function. -/
theorem sLocalHomogeneousTheta_trivial_exists_polarFree (r : RealModels) (c : ComplexModels)
    (φ : PositiveRealExponentialDecay univ) :
    ∃ f : sAdelePolarFree S r c, ∀ g : Jₛ,
      thetaAt(1) f.val g = φ.val (Real.log ((mₛ g).val : ℝ)) := by sorry

/-- Paper: Proposition 5.3.4.4(1)–(2), p. 264.
On the component of χ, a zeta transform is entire exactly when it agrees there
with the transform of a polar-free test. -/
theorem sLocalIdelicZFunction_entire_iff_eq_polarFree (r : RealModels) (c : ComplexModels)
    (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalIdelicZFunction f (chartₛ(χ) s)) univ ↔
      ∃ f₀ : sAdelePolarFree S r c, ∀ s : ℂ,
        sLocalIdelicZFunction f (chartₛ(χ) s) = sLocalIdelicZFunction f₀.val (chartₛ(χ) s) := by sorry

/-- Paper: Proposition 5.3.4.4(1) and (3), p. 264.
On the component of χ, a zeta transform is entire exactly when the homogeneous theta
function has exponential decay at every real exponent. Its covariance is the
norm-one isotype property already supplied by §2.3. -/
theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalIdelicZFunction f (chartₛ(χ) s)) univ ↔
      (⇑(thetaAt(χ₁(χ)) f) : Jₛ → ℂ) ∈ modulatedExponentialDecaySubmodule
        ⟨mₛ, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ univ := by sorry

/-- Paper: Proposition 5.3.4.5(1), p. 264.
Applying the principal value at selected finite places divides the zeta function
by their Euler factors as a meromorphic identity. -/
theorem sLocalIdelicZFunction_principalValue (T : Finset V) (hT : T ⊆ S)
    (f : ℬₛ) (χ : PontryaginDual Jₛ) :
    ∀ᶠ s : ℂ in codiscrete ℂ,
      let c := chartₛ(χ) s
      sLocalIdelicZFunction (sAdelePrincipalValue F hT f) c =
        sLocalIdelicZFunction f c /
          ∏ v : S, if v.val ∈ T then finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c)
            else 1 := by sorry

-- TODO(paper-gap): (5.3.4.14) gives the allowed pole multiplicity, which can exceed
-- the actual order. A local gamma factor contributes a positive multiplicity at a pole.

/-- Paper: Proposition 5.3.4.5(2), p. 264.
The archimedean pole bound counts the local Euler factors with a pole on the
given norm-twist line at the given exponent. Each such pole is simple. -/
def sLocalArchimedeanPoleMultiplicity (χ : PontryaginDual Jₛ) (s : ℂ) : ℕ :=
  (Finset.univ.filter (fun w : InfinitePlace F ↦
    meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
      (sLocalInfiniteRestriction w (chartₛ(χ) z))) s < 0)).card

/-- Paper: Proposition 5.3.4.5(2), p. 264.
The pole multiplicity is positive exactly at a pole of some pulled-back
archimedean Euler factor. -/
theorem sLocalArchimedeanPoleMultiplicity_pos_iff (χ : PontryaginDual Jₛ) (s : ℂ) :
    0 < sLocalArchimedeanPoleMultiplicity χ s ↔
      ∃ w : InfinitePlace F, meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
        (sLocalInfiniteRestriction w (chartₛ(χ) z))) s < 0 := by
  rw [sLocalArchimedeanPoleMultiplicity, Finset.card_pos]
  simp [Finset.Nonempty]

/-- The reciprocal Gamma function satisfies the order recursion coming from
`1 / Γ(u) = u / Γ(u + 1)`. -/
private theorem meromorphicOrderAt_inv_Gamma_step (x : ℂ) :
    meromorphicOrderAt (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) x =
      meromorphicOrderAt (id : ℂ → ℂ) x +
        meromorphicOrderAt (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) (x + 1) := by
  have hg : ∀ y, AnalyticAt ℂ (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) y := fun y ↦
    Complex.differentiable_one_div_Gamma.analyticAt y
  have heq : (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) =
      (id : ℂ → ℂ) * ((fun u : ℂ ↦ (Complex.Gamma u)⁻¹) ∘ (· + 1)) := by
    funext u
    exact Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one u
  have hcomp : MeromorphicAt ((fun u : ℂ ↦ (Complex.Gamma u)⁻¹) ∘ (· + 1)) x :=
    ((hg (x + 1)).comp (f := fun u : ℂ ↦ u + 1) (by fun_prop)).meromorphicAt
  calc meromorphicOrderAt (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) x
      = meromorphicOrderAt ((id : ℂ → ℂ) *
          ((fun u : ℂ ↦ (Complex.Gamma u)⁻¹) ∘ (· + 1))) x := by rw [← heq]
    _ = _ := by
      rw [meromorphicOrderAt_mul analyticAt_id.meromorphicAt hcomp,
        meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]

/-- The reciprocal Gamma function has at most a simple zero at each point. -/
private theorem meromorphicOrderAt_inv_Gamma_le_one (x : ℂ) :
    meromorphicOrderAt (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) x ≤ 1 := by
  have hg : ∀ y, AnalyticAt ℂ (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) y := fun y ↦
    Complex.differentiable_one_div_Gamma.analyticAt y
  have hzero : ∀ {f : ℂ → ℂ} {y : ℂ}, AnalyticAt ℂ f y → f y ≠ 0 →
      meromorphicOrderAt f y = 0 := by
    intro f y hf hy
    rw [hf.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hy), ENat.map_zero,
      CharP.cast_eq_zero, WithTop.coe_zero]
  by_cases hx : ∃ m : ℕ, x = -(m : ℂ)
  · obtain ⟨m, rfl⟩ := hx
    refine le_of_eq ?_
    induction m with
    | zero =>
      rw [meromorphicOrderAt_inv_Gamma_step, Nat.cast_zero, neg_zero, zero_add,
        meromorphicOrderAt_id,
        hzero (hg 1) (by simp [Complex.Gamma_one]), add_zero]
    | succ m ih =>
      rw [meromorphicOrderAt_inv_Gamma_step,
        hzero analyticAt_id (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.add_one_ne_zero m))),
        zero_add, show -((m + 1 : ℕ) : ℂ) + 1 = -(m : ℂ) by push_cast; ring]
      exact ih
  · rw [hzero (hg x) (inv_ne_zero (Complex.Gamma_ne_zero fun m hm ↦ hx ⟨m, hm⟩))]
    exact zero_le_one

/-- Every pole of the Gamma function is simple. -/
private theorem neg_one_le_meromorphicOrderAt_Gamma (x : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt Complex.Gamma x := by
  have h := meromorphicOrderAt_inv_Gamma_le_one x
  have hinv : meromorphicOrderAt (fun u : ℂ ↦ (Complex.Gamma u)⁻¹) x =
      -meromorphicOrderAt Complex.Gamma x := meromorphicOrderAt_inv
  rw [hinv] at h
  cases hn : meromorphicOrderAt Complex.Gamma x with
  | top => exact le_top
  | coe n =>
    rw [hn] at h
    have h1 : -n ≤ 1 := by exact_mod_cast h
    exact_mod_cast (by omega : (-1 : ℤ) ≤ n)

/-- Every pole of the real Gamma factor is simple. -/
private theorem neg_one_le_meromorphicOrderAt_Gammaℝ (x : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt Complex.Gammaℝ x := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have heq : Complex.Gammaℝ = (fun s : ℂ ↦ (Real.pi : ℂ) ^ (-s / 2)) *
      (Complex.Gamma ∘ fun s : ℂ ↦ s / 2) := by
    funext s
    exact Complex.Gammaℝ_def s
  have han : AnalyticAt ℂ (fun s : ℂ ↦ (Real.pi : ℂ) ^ (-s / 2)) x :=
    ((differentiable_id.neg.div_const 2).const_cpow (Or.inl hpi)).analyticAt x
  rw [heq, meromorphicOrderAt_mul_of_ne_zero han (by simp [hpi]),
    meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)]
  exact neg_one_le_meromorphicOrderAt_Gamma _

/-- Every pole of the complex Gamma factor is simple. -/
private theorem neg_one_le_meromorphicOrderAt_Gammaℂ (x : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt Complex.Gammaℂ x := by
  have hpi : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have heq : Complex.Gammaℂ = (fun s : ℂ ↦ 2 * (2 * Real.pi : ℂ) ^ (-s)) * Complex.Gamma := by
    funext s
    exact Complex.Gammaℂ_def s
  have han : AnalyticAt ℂ (fun s : ℂ ↦ 2 * (2 * Real.pi : ℂ) ^ (-s)) x :=
    ((differentiable_id.neg.const_cpow (Or.inl hpi)).const_mul 2).analyticAt x
  rw [heq, meromorphicOrderAt_mul_of_ne_zero han (by simp [hpi])]
  exact neg_one_le_meromorphicOrderAt_Gamma _

/-- Along a norm-twist chart, the restriction to an archimedean place is the restriction
at exponent zero times the complex power of the local module. -/
private theorem sLocalInfiniteRestriction_chart_apply (χ : PontryaginDual Jₛ)
    (w : InfinitePlace F) (z : ℂ) (g : w.Completionˣ) :
    sLocalInfiniteRestriction w (chartₛ(χ) z) g =
      sLocalInfiniteRestriction w (chartₛ(χ) 0) g *
        ((((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ) g : ℝ≥0) : ℝ) :
          ℂ) ^ z := by
  obtain ⟨x, hx⟩ : ∃ x : Jₛ, ∀ c : Xₛ, sLocalInfiniteRestriction w c g = c x :=
    ⟨_, fun _ ↦ rfl⟩
  have hN : ((((mₛ) x : ℝ≥0) : ℝ) : ℂ) =
      ((((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ) g : ℝ≥0) : ℝ) :
        ℂ) := by
    have he := sLocalInfiniteRestriction_norm (S := S) w g
    rw [hx] at he
    change ((1 : PontryaginDual Jₛ) x : ℂ) * ((((mₛ) x : ℝ≥0) : ℝ) : ℂ) ^ (1 : ℂ) = _ at he
    simpa only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one] using he
  rw [hx, hx, ← hN]
  change (χ x : ℂ) * ((((mₛ) x : ℝ≥0) : ℝ) : ℂ) ^ z =
    ((χ x : ℂ) * ((((mₛ) x : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ)) * ((((mₛ) x : ℝ≥0) : ℝ) : ℂ) ^ z
  rw [Complex.cpow_zero, mul_one]

/-- Along a norm-twist chart, the Euler factor at a real place is a translate of the real
Gamma factor. -/
private theorem infiniteLocalEulerFactor_chart_real (χ : PontryaginDual Jₛ)
    (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ b : ℂ, ∀ z : ℂ, infiniteLocalEulerFactor w
      (sLocalInfiniteRestriction w (chartₛ(χ) z)) = Complex.Gammaℝ (z + b) := by
  let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
  have hp := (realLocalEulerParameters w hw
    (sLocalInfiniteRestriction w (chartₛ(χ) 0))).exists.choose_spec
  obtain ⟨p, hpdef⟩ : ∃ p : ℂ × Fin 2, p = (realLocalEulerParameters w hw
    (sLocalInfiniteRestriction w (chartₛ(χ) 0))).exists.choose := ⟨_, rfl⟩
  rw [← hpdef] at hp
  refine ⟨p.1 + (p.2.val : ℂ), fun z ↦ ?_⟩
  have hshape : ∀ x : ℝˣ, sLocalInfiniteRestriction w (chartₛ(χ) z)
      (Units.map e.toMonoidHom x) =
        (‖(x : ℝ)‖ : ℂ) ^ (z + p.1) * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ p.2.val := by
    intro x
    have hn : ‖(e (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
        (map_zero e) (x : ℝ)
    have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
        (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℝ)‖ := by
      simp [InfinitePlace.mult, hw, hn]
    rw [sLocalInfiniteRestriction_chart_apply, hp x, hm,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero))]
    ring
  have hq := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (chartₛ(χ) z))).unique
    (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (chartₛ(χ) z))).exists.choose_spec
    (y₂ := (z + p.1, p.2)) hshape
  simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hq, add_assoc]

/-- Along a norm-twist chart, the Euler factor at a complex place is half a translate of the
complex Gamma factor. -/
private theorem infiniteLocalEulerFactor_chart_complex (χ : PontryaginDual Jₛ)
    (w : InfinitePlace F) (hw : w.IsComplex) :
    ∃ b : ℂ, ∀ z : ℂ, infiniteLocalEulerFactor w
      (sLocalInfiniteRestriction w (chartₛ(χ) z)) = Complex.Gammaℂ (z + b) / 2 := by
  let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm
  have hp := (complexLocalEulerParameters w hw
    (sLocalInfiniteRestriction w (chartₛ(χ) 0))).exists.choose_spec
  obtain ⟨p, hpdef⟩ : ∃ p : ℂ × ℤ, p = (complexLocalEulerParameters w hw
    (sLocalInfiniteRestriction w (chartₛ(χ) 0))).exists.choose := ⟨_, rfl⟩
  rw [← hpdef] at hp
  refine ⟨p.1 + (p.2.natAbs : ℂ) / 2, fun z ↦ ?_⟩
  have hshape : ∀ x : ℂˣ, sLocalInfiniteRestriction w (chartₛ(χ) z)
      (Units.map e.toMonoidHom x) =
        ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (z + p.1) * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ p.2 := by
    intro x
    have hn : ‖(e (x : ℂ) : w.Completion)‖ = ‖(x : ℂ)‖ :=
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        hw).symm.isometry.norm_map_of_map_zero (map_zero e) (x : ℂ)
    have hm : (((Units.map nnNormHom.toMonoidHom ^ w.mult : w.Completionˣ →* ℝ≥0ˣ)
        (Units.map e.toMonoidHom x) : ℝ≥0) : ℝ) = ‖(x : ℂ)‖ ^ 2 := by
      simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.mpr hw, hn]
    rw [sLocalInfiniteRestriction_chart_apply, hp x, hm,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
        (pow_ne_zero _ (norm_ne_zero_iff.mpr x.ne_zero)))]
    ring
  have hq := (complexLocalEulerParameters w hw
      (sLocalInfiniteRestriction w (chartₛ(χ) z))).unique
    (complexLocalEulerParameters w hw
      (sLocalInfiniteRestriction w (chartₛ(χ) z))).exists.choose_spec
    (y₂ := (z + p.1, p.2)) hshape
  simp only [infiniteLocalEulerFactor, InfinitePlace.not_isReal_iff_isComplex.mpr hw,
    ↓reduceDIte, hq, add_assoc]

/-- For orders bounded below by minus one, the negative parts sum to minus the number of
negative orders. -/
private theorem neg_card_filter_eq_sum_min {ι : Type*} [Fintype ι] (ord : ι → WithTop ℤ)
    [DecidablePred fun i ↦ ord i < 0] (h : ∀ i, ((-1 : ℤ) : WithTop ℤ) ≤ ord i) :
    ((-((Finset.univ.filter fun i ↦ ord i < 0).card : ℤ) : ℤ) : WithTop ℤ) =
      ∑ i, min 0 (ord i) := by
  have hneg : ∀ i ∈ Finset.univ.filter (fun i ↦ ord i < 0),
      min 0 (ord i) = ((-1 : ℤ) : WithTop ℤ) := by
    intro i hi
    have hi' : ord i < 0 := (Finset.mem_filter.mp hi).2
    rw [min_eq_right hi'.le]
    refine le_antisymm ?_ (h i)
    cases hn : ord i with
    | top =>
      rw [hn] at hi'
      exact absurd hi' not_top_lt
    | coe n =>
      rw [hn] at hi'
      have h0 : n < 0 := by exact_mod_cast hi'
      exact_mod_cast (by omega : n ≤ -1)
  have hpos : ∀ i ∈ Finset.univ.filter (fun i ↦ ¬ ord i < 0), min 0 (ord i) = 0 := fun i hi ↦
    min_eq_left (not_lt.mp (Finset.mem_filter.mp hi).2)
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i ↦ ord i < 0),
    Finset.sum_congr rfl hneg, Finset.sum_eq_zero hpos, add_zero, Finset.sum_const,
    ← WithTop.coe_nsmul]
  congr 1
  simp

/-- Along a norm-twist chart, every pole of an archimedean Euler factor is simple. -/
private theorem neg_one_le_meromorphicOrderAt_infiniteLocalEulerFactor_chart
    (χ : PontryaginDual Jₛ) (w : InfinitePlace F) (s : ℂ) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
      (sLocalInfiniteRestriction w (chartₛ(χ) z))) s := by
  by_cases hw : w.IsReal
  · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_real χ w hw
    have hfun : (fun z ↦ infiniteLocalEulerFactor w
        (sLocalInfiniteRestriction w (chartₛ(χ) z))) = Complex.Gammaℝ ∘ (· + b) := funext hb
    rw [hfun, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
    exact neg_one_le_meromorphicOrderAt_Gammaℝ _
  · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_complex χ w
      (InfinitePlace.not_isReal_iff_isComplex.mp hw)
    have hfun : (fun z ↦ infiniteLocalEulerFactor w
        (sLocalInfiniteRestriction w (chartₛ(χ) z))) =
        (fun _ : ℂ ↦ (2 : ℂ)⁻¹) * (Complex.Gammaℂ ∘ (· + b)) :=
      funext fun z ↦ (hb z).trans (div_eq_inv_mul _ _)
    rw [hfun, meromorphicOrderAt_mul_of_ne_zero analyticAt_const (inv_ne_zero two_ne_zero),
      meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
    exact neg_one_le_meromorphicOrderAt_Gammaℂ _

/-- Paper: Proposition 5.3.4.5(2), p. 264.
The negative of the allowed pole multiplicity is the sum of the negative parts
of the meromorphic orders of the local archimedean Euler factors. -/
theorem sLocalArchimedeanPoleMultiplicity_eq_sum (χ : PontryaginDual Jₛ) (s : ℂ) :
    (↑(-(sLocalArchimedeanPoleMultiplicity χ s : ℤ)) : WithTop ℤ) =
      ∑ w : InfinitePlace F, min 0
        (meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
          (sLocalInfiniteRestriction w (chartₛ(χ) z))) s) := by
  rw [sLocalArchimedeanPoleMultiplicity]
  exact neg_card_filter_eq_sum_min _ fun w ↦
    neg_one_le_meromorphicOrderAt_infiniteLocalEulerFactor_chart χ w s

/-- Paper: Proposition 5.3.4.5(2), p. 264.
After all finite principal values, the zeta pole order is bounded by the total
archimedean Euler pole multiplicity.
Deviation: The assertion gives an upper bound since the input can cancel poles.
The multiplicity counts positive pole orders. -/
theorem sLocalIdelicZFunction_principalValue_pole_bound (f : ℬₛ)
    (χ : PontryaginDual Jₛ) (s : ℂ) :
    (↑(-(sLocalArchimedeanPoleMultiplicity χ s : ℤ)) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction
        (sAdelePrincipalValue F (Finset.Subset.refl S) f) (chartₛ(χ) z)) s := by sorry

/-- Paper: Proposition 5.3.4.5(2), p. 264.
On each component a choice of test realizes the full allowed archimedean pole divisor.
Deviation: Attainment is an existence assertion. The input can cancel any allowed pole. -/
theorem exists_sLocalIdelicZFunction_principalValue_attaining_poles (χ : PontryaginDual Jₛ) :
    ∃ f : ℬₛ, ∀ s : ℂ,
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction
        (sAdelePrincipalValue F (Finset.Subset.refl S) f) (chartₛ(χ) z)) s =
        (↑(-(sLocalArchimedeanPoleMultiplicity χ s : ℤ)) : WithTop ℤ) := by sorry

private theorem continuous_schwartzBruhat_pointEval {G : Type*} [CommGroup G]
    [TopologicalSpace G] (x : G) : Continuous (fun f : SchwartzBruhat G ↦ f x) := by
  classical
  let L : SchwartzBruhat G →ₗ[ℂ] ℂ :=
    (LinearMap.proj x).comp (schwartzBruhatSubmodule G).subtype
  let p := (normSeminorm ℂ ℂ).comp L
  have hstage (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
      Continuous (p ∘ schwartzBruhatStageInclusion a e) := by
    let _ := e.finiteGroup
    let q : Seminorm ℂ (SchwartzBruhatStage e) := elementarySchwartzSeminorm (0, 0, 0, 0)
    have hq : Continuous q := elementarySchwartz_withSeminorms.continuous_seminorm (0, 0, 0, 0)
    change Continuous (p.comp (schwartzBruhatStageInclusion a e))
    refine Seminorm.continuous_of_le hq ?_
    intro f
    change ‖schwartzBruhatStageRealization a e f x‖ ≤ q f
    rw [schwartzBruhatStageRealization_apply]
    split_ifs with hx
    · let y := Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩))
      change (↑‖f y‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal
      refine ENNReal.toReal_mono (f.property.2 (0, 0, 0, 0)).ne ?_
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun z ↦ (↑‖f z‖₊ : ENNReal)) y
    · simpa only [norm_zero] using apply_nonneg q f
  exact (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L fun _ ↦
    (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm ⟨p, hstage⟩

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The subspace cut out by the selected finite zero-coordinate conditions is closed. -/
theorem sAdeleFiniteZeroSchwartz_isClosed (T : Finset V) :
    IsClosed (↑(sAdeleFiniteZeroSchwartz S T) : Set ℬₛ) := by
  let X := {x : SAdeleRing F S // ∃ v : S, v.val ∈ T ∧ x.2 v = 0}
  have h : IsClosed (⋂ x : X, {f : ℬₛ | f (Multiplicative.ofAdd x.val) = 0}) :=
    isClosed_iInter fun x : X ↦
      isClosed_eq (continuous_schwartzBruhat_pointEval (Multiplicative.ofAdd x.val)) continuous_const
  have heq : (⋂ x : X, {f : ℬₛ | f (Multiplicative.ofAdd x.val) = 0}) =
      (↑(sAdeleFiniteZeroSchwartz S T) : Set ℬₛ) :=
    Set.ext fun f ↦ by
      refine Set.mem_iInter.trans ?_
      let K (x : X) : Submodule ℂ ℬₛ :=
        LinearMap.ker ((LinearMap.proj (Multiplicative.ofAdd x.val)).comp
          (schwartzBruhatSubmodule (Multiplicative (SAdeleRing F S))).subtype)
      change (∀ x : X, f ∈ K x) ↔ f ∈ ⨅ x : X, K x
      exact (Submodule.mem_iInf K).symm
  exact (congrArg (fun s : Set ℬₛ ↦ IsClosed s) heq).mp h

local notation "thetaQuotient(" χ ")" => (LinearMap.ker (thetaAt(χ))).mkQ

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The principal value preserves the kernel of each homogeneous theta transform. -/
theorem sAdelePrincipalValue_preserves_homogeneousThetaKernel {T : Finset V} (hT : T ⊆ S)
    (ψ : PontryaginDual J₁) :
    LinearMap.ker (thetaAt(ψ)) ≤
      (LinearMap.ker (thetaAt(ψ))).comap (sAdelePrincipalValue F hT) := by sorry

/-- Paper: Proposition 5.3.4.5(3), p. 264.
Weil's operator on homogeneous theta classes is induced by its action on tests. -/
def sLocalHomogeneousThetaPrincipalValue {T : Finset V} (hT : T ⊆ S) (ψ : PontryaginDual J₁) :
    SLocalHomogeneousThetaSpace F S ψ →ₗ[ℂ] SLocalHomogeneousThetaSpace F S ψ :=
  (LinearMap.ker (thetaAt(ψ))).mapQ (LinearMap.ker (thetaAt(ψ))) (sAdelePrincipalValue F hT)
    (sAdelePrincipalValue_preserves_homogeneousThetaKernel hT ψ)

/-- Paper: Proposition 5.3.4.5(3), p. 264.
On a homogeneous theta class the operator sends the representative to its principal value. -/
theorem sLocalHomogeneousThetaPrincipalValue_mk {T : Finset V} (hT : T ⊆ S)
    (ψ : PontryaginDual J₁) (f : ℬₛ) :
    sLocalHomogeneousThetaPrincipalValue hT ψ (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (sAdelePrincipalValue F hT f) := rfl

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The closed embedding of Lemma 5.3.1.5 restricts to the homogeneous theta quotient,
identified with its isotype by §5.2. -/
theorem sLocalHomogeneousThetaPrincipalValue_isClosedEmbedding {T : Finset V} (hT : T ⊆ S)
    (ψ : PontryaginDual J₁) : IsClosedEmbedding (sLocalHomogeneousThetaPrincipalValue hT ψ) :=
  by sorry

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The principal value range in the homogeneous theta quotient is the image of tests
vanishing at the finite zero-coordinate hyperplanes. -/
theorem sLocalPrincipalValue_homogeneousTheta_range (χ : PontryaginDual Jₛ) :
    LinearMap.range (sLocalHomogeneousThetaPrincipalValue (Finset.Subset.refl S) χ₁(χ)) =
      (sAdeleFiniteZeroSchwartz S S).map (thetaQuotient(χ₁(χ))) := by sorry

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The same homogeneous theta image is obtained by imposing finite zero-coordinate
vanishing only at the unramified places of χ. -/
theorem sLocalPrincipalValue_homogeneousTheta_range_unramified (χ : PontryaginDual Jₛ)
    (T : Finset V) (_hT : T ⊆ S)
    (_hχ : ∀ v : S, v.val ∈ T ↔ ∀ u : (v.val.adicCompletionIntegers F)ˣ,
      sLocalFiniteRestriction v (chartₛ(χ) 0)
        (Units.map (HeightOneSpectrum.adicCompletionIntegers F v.val).subtype.toMonoidHom u) = 1) :
    LinearMap.range (sLocalHomogeneousThetaPrincipalValue (Finset.Subset.refl S) χ₁(χ)) =
      (sAdeleFiniteZeroSchwartz S T).map (thetaQuotient(χ₁(χ))) := by sorry

end SAdele

end RiemannMasullo
