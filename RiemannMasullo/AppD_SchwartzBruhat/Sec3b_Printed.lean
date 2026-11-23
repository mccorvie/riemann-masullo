module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec3b
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-! # Appendix D.3.5: the printed Poisson summation formula -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter Function MeasureTheory Set
open scoped ContDiff NNReal Topology

universe u

/-- The unitary character given by the imaginary power `i r` of the module. -/
def Printed.modulationFrequency {G : Type*} [CommGroup G] [TopologicalSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (r : ℝ) : PontryaginDual G where
  toFun x := Circle.exp (r * Real.log ((m x).val : ℝ))
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul m, Units.val_mul, NNReal.coe_mul,
      Real.log_mul (NNReal.coe_pos.mpr (Units.zero_lt (m x))).ne'
        (NNReal.coe_pos.mpr (Units.zero_lt (m y))).ne',
      mul_add, Circle.exp_add]
  continuous_toFun := by
    have h : Continuous (fun x : G ↦ ((m x).val : ℝ)) :=
      NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
    exact Circle.exp.continuous.comp
      ((h.log fun x ↦ (NNReal.coe_pos.mpr (Units.zero_lt (m x))).ne').const_mul r)

/-- Paper: Proposition D.3.5.1(1)–(3), p. 818. Bounds, radial regularity and
left-translation homogeneity assumed in both (D.3.5.3) and its proof. -/
structure Printed.ModulatedPoissonHypotheses {G : Type*} [CommGroup G] [TopologicalSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (χ₀ : PontryaginDual G) (τ : ℝ≥0ˣ →ₜ* G)
    (f : G → ℂ) (S : Finset ℝ≥0ˣ) : Prop where
  bounded : ∃ C : ℝ, ∀ x : G, ‖f x‖ ≤ C
  decay : ∀ N : ℕ, 1 ≤ N → ∃ T C : ℝ, 0 < T ∧ 0 < C ∧
    ∀ x : G,
      let s := Real.log ((m x).val : ℝ)
      T < |s| → ‖f x‖ ≤ C * Real.exp (-(N : ℝ) * |s|)
  regularity :
    let K := m.toMonoidHom.ker
    let expUnit (s : ℝ) := (Nonneg.unitsHomeomorphPos ℝ).symm (Real.expOrderIso s)
    let profile (g : K) (s : ℝ) := f (τ (expUnit s) * g.val)
    let U := {s : ℝ | expUnit s ∉ S}
    (∀ g : K, Continuous (profile g) ∧ ContDiffOn ℝ ∞ (profile g) U) ∧
      ∀ k : ℕ, ContinuousOn (fun p : ℝ × K ↦ iteratedDeriv k (profile p.2) p.1)
        (U ×ˢ (univ : Set K))
  leftLimit : ∀ (t : S) (g : m.toMonoidHom.ker),
    ∃ a, Tendsto (fun s ↦ f (τ s * g.val)) (𝓝[<] t.val) (𝓝 a)
  rightLimit : ∀ (t : S) (g : m.toMonoidHom.ker),
    ∃ a, Tendsto (fun s ↦ f (τ s * g.val)) (𝓝[>] t.val) (𝓝 a)
  homogeneous : ∀ (g : m.toMonoidHom.ker) (x : G), f (g.val⁻¹ * x) = (χ₀ g.val : ℂ) * f x

/-- Paper: Proposition D.3.5.1, p. 818. As printed: for a bounded, rapidly decaying
function with the stated smoothness, one-sided limits and homogeneity, the cyclic
periodization of the character times the midpoint-redefined function agrees
everywhere with the Fourier series (D.3.5.3), with its printed frequency signs and
phase shift. The Fourier series is read as symmetric partial sums as in the cited
Proposition B.4.1.2. See `modulatedJumpMidpointProfile`,
`existsUnique_modulatedCharacterPhase` and ERRATA F232. -/
def Printed.modulatedPoissonSummation : Prop :=
  ∀ (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (γ : G), 1 < (m γ).val →
    ∀ (χ₀ : PontryaginDual G) (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
      (f : G → ℂ) (S : Finset ℝ≥0ˣ) (h : Printed.ModulatedPoissonHypotheses m χ₀ τ f S),
      let logModule (x : G) := Real.log ((m x).val : ℝ)
      let L := logModule γ
      let frequency (n : ℤ) := 2 * Real.pi * (n : ℝ) / L
      let fMid (x : G) :=
        modulatedJumpMidpointProfile m τ f S h.leftLimit h.rightLimit (m x)
          ⟨(τ (m x))⁻¹ * x, by
            change m ((τ (m x))⁻¹ * x) = 1
            rw [map_mul, map_inv, hτ, inv_mul_cancel]⟩
      ∀ t₀ : ℝ, t₀ ∈ Ico 0 (2 * Real.pi / L) → Circle.exp (t₀ * L) = χ₀ γ →
        ∀ x : G, ∃ periodized : ℂ,
          HasSum (fun n : ℤ ↦ (χ₀ (γ ^ n * x) : ℂ) * fMid (γ ^ n * x)) periodized ∧
          Tendsto (fun N : ℕ ↦ (L : ℂ)⁻¹ * ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            lcaFourier (canonicalModulatedHaar m hm) fMid
              (χ₀⁻¹ * Printed.modulationFrequency m (-frequency n + t₀)) *
            (Circle.exp (frequency n * logModule x) : ℂ)) atTop (𝓝 periodized)

/-- Paper: Proposition D.3.5.1, p. 818. Take G = ℝ₊ˣ with identity module and
section, γ = exp(1), χ₀ = 1, t₀ = 0, and no designated jump points.
Take f to be a smooth bump in the log coordinate, supported in (1/8, 3/8) and
equal to one at 1/4. At x = exp(1/4) the left series equals one. The transform
conjugates its character, so the frequency signs in (D.3.5.3) make the right
series sample the periodization at −1/4 in the log coordinate, where it is zero. -/
theorem Printed.modulatedPoissonSummation_false : ¬ Printed.modulatedPoissonSummation := by
  sorry

/-- Paper: (D.3.5.5), p. 819. The last equality in the proof of Proposition
D.3.5.1 identifies the radial integral of ψ = χ₀φ against the conjugate character
with the integral of that conjugate character over the kernel with its probability
Haar measure. Here φ has the prescribed midpoint values. See ERRATA F232. -/
def Printed.modulatedPoisson_radialIntegral_eq_kernelIntegral : Prop :=
  ∀ (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ), IsModulation m → ∀ (γ : G), 1 < (m γ).val →
    ∀ (χ₀ : PontryaginDual G) (τ : ℝ≥0ˣ →ₜ* G), RightInverse τ m →
    ∀ (f : G → ℂ) (S : Finset ℝ≥0ˣ) (h : Printed.ModulatedPoissonHypotheses m χ₀ τ f S)
      (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] [IsProbabilityMeasure μ₁]
      (χ : PontryaginDual G),
      let ψτ (t : ℝ≥0ˣ) := (χ₀ (τ t) : ℂ) *
        modulatedJumpMidpointProfile m τ f S h.leftLimit h.rightLimit t 1
      (∫ t, ψτ t * star (χ (τ t) : ℂ) ∂positiveRealHaar) =
        ∫ g : m.toMonoidHom.ker, star (χ g.val : ℂ) ∂μ₁

/-- On a subsingleton topological group, the Dirac measure at the identity is a Haar
measure. -/
private theorem Printed.modulatedPoisson_radialIntegral_eq_kernelIntegral_false_dirac
    {K : Type*} [Group K] [TopologicalSpace K] [MeasurableSpace K] [Subsingleton K] :
    (Measure.dirac (1 : K)).IsHaarMeasure := by
  have hsub : ∀ U : Set K, U.Nonempty → U = univ := fun U ⟨x, hx⟩ ↦
    eq_univ_of_forall fun y ↦ Subsingleton.elim x y ▸ hx
  refine { toIsFiniteMeasureOnCompacts := ⟨fun _ _ ↦ measure_lt_top _ _⟩
           toIsMulLeftInvariant := ⟨fun g ↦ ?_⟩
           toIsOpenPosMeasure := ⟨fun U _ hne ↦ by
             rw [hsub U hne, measure_univ]; exact one_ne_zero⟩ }
  have hg : (g * ·) = id := funext fun _ ↦ Subsingleton.elim _ _
  rw [hg, Measure.map_id]

/-- The printed identity fails at every type level: lift the positive reals with `ULift`,
and take the zero test, the empty jump set and trivial characters. -/
private theorem Printed.modulatedPoisson_radialIntegral_eq_kernelIntegral_false_of
    (h : Printed.modulatedPoisson_radialIntegral_eq_kernelIntegral.{u}) : False := by
  have : LocallyCompactSpace {x : ℝ // 0 < x} := isOpen_Ioi.locallyCompactSpace
  have : LocallyCompactSpace ℝ≥0ˣ :=
    (Nonneg.unitsHomeomorphPos ℝ).isOpenEmbedding.locallyCompactSpace
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : LocallyCompactSpace (ULift.{u} ℝ≥0ˣ) :=
    Homeomorph.ulift.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (ULift.{u} ℝ≥0ˣ) :=
    Homeomorph.ulift.isEmbedding.secondCountableTopology
  let m : ULift.{u} ℝ≥0ˣ →ₜ* ℝ≥0ˣ := ⟨MulEquiv.ulift.toMonoidHom, continuous_uliftDown⟩
  let τ : ℝ≥0ˣ →ₜ* ULift.{u} ℝ≥0ˣ := ⟨(MulEquiv.ulift (α := ℝ≥0ˣ)).symm.toMonoidHom, continuous_uliftUp⟩
  let two : ℝ≥0ˣ := Units.mk0 2 two_ne_zero
  have htwo : two ≠ 1 := fun h2 ↦ by
    have := congrArg Units.val h2
    norm_num [two] at this
  have hm : IsModulation m := ⟨Homeomorph.ulift.isProperMap, ⟨ULift.up two, htwo⟩⟩
  have hγ : 1 < (m (ULift.up two)).val := by
    change (1 : ℝ≥0) < 2
    norm_num
  let f : ULift.{u} ℝ≥0ˣ → ℂ := fun _ ↦ 0
  have hyp : Printed.ModulatedPoissonHypotheses m 1 τ f ∅ :=
    { bounded := ⟨0, fun _ ↦ by simp [f]⟩
      decay := fun _ _ ↦ ⟨1, 1, one_pos, one_pos, fun _ _ ↦ by simp only [f, norm_zero]; positivity⟩
      regularity := ⟨fun _ ↦ ⟨continuous_const, contDiffOn_const⟩, fun _ ↦ by
        simp only [f, iteratedDeriv_const]
        exact continuousOn_const⟩
      leftLimit := fun t ↦ (Finset.notMem_empty _ t.2).elim
      rightLimit := fun t ↦ (Finset.notMem_empty _ t.2).elim
      homogeneous := fun _ _ ↦ (mul_zero _).symm }
  have : Subsingleton m.toMonoidHom.ker := ⟨fun x y ↦ Subtype.ext
    (MulEquiv.ulift.injective ((MonoidHom.mem_ker.mp x.2).trans (MonoidHom.mem_ker.mp y.2).symm))⟩
  have := Printed.modulatedPoisson_radialIntegral_eq_kernelIntegral_false_dirac
    (K := m.toMonoidHom.ker)
  have hEq := h (ULift.{u} ℝ≥0ˣ) m hm (ULift.up two) hγ 1 τ (fun _ ↦ rfl) f ∅ hyp
    (Measure.dirac 1) 1
  simp [modulatedJumpMidpointProfile, f] at hEq

/-- Paper: (D.3.5.5), p. 819. Take the identity modulation and section on the
positive reals, γ = exp(1), both characters trivial, S empty and φ identically
zero. The radial integral is zero and the probability Haar integral of one is one. -/
theorem Printed.modulatedPoisson_radialIntegral_eq_kernelIntegral_false :
    ¬ Printed.modulatedPoisson_radialIntegral_eq_kernelIntegral :=
  fun h ↦ Printed.modulatedPoisson_radialIntegral_eq_kernelIntegral_false_of h

end RiemannMasullo
