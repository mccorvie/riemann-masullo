module

public import RiemannMasullo.Ch09_HardySobolev.Sec1
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3b
public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec1
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# Hardy–Sobolev spaces and Paley–Wiener conditions

Masullo, §9.2, pp. 403–419. Scalar functions on the positive reals are represented
in the coordinate `x = log t`, so multiplicative Haar measure becomes Lebesgue measure.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology TensorProduct

namespace RiemannMasullo

-- TODO(paper-gap): The coordinate integrals on pp. 403 and 416 omit the
-- kernel character. Use the intrinsic transform from §D.3.3.

open NumberField in
open scoped NumberField.AdeleRing in
/-- Paper: Remark 9.2.0.1, p. 403. When a test and its Fourier transform vanish at zero,
the global idelic Mellin transform is the canonical Mellin transform of its theta function
times the Tamagawa mass of the norm-one classes.
Deviation: The operator called L in the remark is Z in (5.1.1.1). The equality uses regular
values of the bundled target. On the theta quotient use `globalThetaMellin_mk`. -/
theorem globalIdelicMellin_eq_canonical_of_vanishing {F : Type*} [Field F] [NumberField F]
    [SecondCountableTopology (IdeleClassGroup (𝓞 F) F)]
    (f : SchwartzBruhat (Multiplicative 𝔸[F]))
    (hf : f (Multiplicative.ofAdd 0) = 0)
    (hFourier : adeleSchwartzFourier (F := F) f (Multiplicative.ofAdd 0) = 0)
    (c : {c : QuasiCharacter (IdeleClassGroup (𝓞 F) F) // 0 ≤ globalIdelicOrderBound (F := F) c}) :
    let hClass := ideleGroup_quotient.{_, 0} F
    letI : T2Space (IdeleClassGroup (𝓞 F) F) := hClass.2.2.2.2.2.1
    letI : LocallyCompactSpace (IdeleClassGroup (𝓞 F) F) := hClass.2.2.2.2.2.2.1
    letI : MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _
    letI : BorelSpace (IdeleClassGroup (𝓞 F) F) := ⟨rfl⟩
    let m : IdeleClassGroup (𝓞 F) F →ₜ* ℝ≥0ˣ :=
      ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
    let hm : IsModulation m := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
    let μ := canonicalModulatedHaar m hm
    let V := (normOneIdeleClassTamagawaMeasure F).real univ
    Integrable (fun g ↦ adelicTheta (F := F) f g * c.val g) μ ∧
      (globalIdelicMellin (F := F) f).val c =
        (V : ℂ) * modulatedFourierMellin m univ hm μ (adelicTheta (F := F) f) c.val := by sorry

local notation "verticalPoint" => (fun (b y : ℝ) ↦ (b : ℂ) + (y : ℂ) * Complex.I)
set_option quotPrecheck false in
local notation "logModule" =>
  (fun (m : _ →ₜ* ℝ≥0ˣ) g ↦ Real.log ((m g).val : ℝ))

/-- Paper: Definition 9.2.1.1(1), p. 404. The logarithmic weight is the sum of the
squared moment multipliers from order zero through order N, times the squared twist.
Deviation: N is the largest order included. The scalar source in (9.2.1.2) uses N − 1. -/
def lineSobolevDensity (b : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  Real.exp (2 * b * x) * ∑ k ∈ Finset.range (N + 1), x ^ (2 * k)

/-- Paper: Definition 9.2.1.1(1), p. 404. With order zero only, the density
is just the squared twist.
Deviation: Sanity check in logarithmic coordinates. -/
theorem lineSobolevDensity_order_zero (b x : ℝ) :
    lineSobolevDensity b 0 x = Real.exp (2 * b * x) := by sorry

/-- Paper: Definition 9.2.1.1(1), p. 404. The completion is realized as weighted L².
Deviation: The norm combines the squared norms in (9.2.1.2) by summing them. The
maximum order is an explicit parameter and the scalar case uses Lebesgue measure and `id`. -/
abbrev LineSobolev {A : Type*} [MeasurableSpace A] (μ : Measure A) (logNorm : A → ℝ)
    (b : ℝ) (N : ℕ) :=
  Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (lineSobolevDensity b N (logNorm x)))

/-- Paper: Definition 9.2.1.1(1), p. 404. The scalar b-line Sobolev space uses the
moments of order zero through N.
Deviation: (9.2.1.2) prints 0 ≤ k ≤ N − 1. The proof of Theorem 9.2.1.2(1) on p. 405, the
target in Definition 9.2.1.1(2) and Theorem 9.2.1.5, which is the same space for a general
group, all use 0 ≤ k ≤ N. -/
abbrev ScalarLineSobolev (b : ℝ) (N : ℕ) :=
  LineSobolev volume id b N

/-- Paper: Definition 9.2.1.1(1), p. 404. In the scalar model the weighted integral
gives the norm, and the exponential-decay test profiles have dense image.
Deviation: The largest order is N, see `ScalarLineSobolev`. -/
theorem scalarLineSobolev_dense (b : ℝ) (N : ℕ) :
    ∃ j : PositiveRealExponentialDecay univ →L[ℂ] ScalarLineSobolev b N,
      Injective j ∧ DenseRange j ∧
      ∀ f, (j f : ℝ → ℂ) =ᵐ[volume] f.val ∧
        Integrable (fun x ↦ ‖f.val x‖ ^ 2 * lineSobolevDensity b N x) volume ∧
        ‖j f‖ = Real.sqrt (∫ x, ‖f.val x‖ ^ 2 * lineSobolevDensity b N x) := by
  sorry

/-- Paper: Definition 9.2.1.1(2), p. 404. Complete the entire Schwartz–Bergman
space by taking the closure of its derivative traces in a finite product of vertical L² spaces.
Deviation: The abscissas and largest derivative order are explicit. For one abscissa
this is (9.2.1.3) applied directly to the analytic function. The vertical measure is
a parameter, so either the printed or the Plancherel normalization can be used. -/
def hardySobolevTraceClosure {ι : Type*} [Fintype ι] (σ : ι → ℝ) (N : ℕ) (ν : Measure ℝ) :
    Submodule ℂ (PiLp 2 (fun _ : ι ↦ PiLp 2 (fun _ : Fin (N + 1) ↦ Lp ℂ 2 ν))) :=
  (Submodule.span ℂ {u : PiLp 2 (fun _ : ι ↦ PiLp 2 (fun _ : Fin (N + 1) ↦ Lp ℂ 2 ν)) |
    ∃ F : SchwartzBergman (univ : Set ℝ),
    ∀ i (k : Fin (N + 1)), (u i k : ℝ → ℂ) =ᵐ[ν]
      fun y ↦ iteratedDeriv (k : ℕ) F.val (verticalPoint (σ i) y)}).topologicalClosure

/-- Paper: Definition 9.2.1.1(2), p. 404. The model contains the Gaussian's
vertical derivative traces at any selected abscissas.
Deviation: Sanity check for the trace closure, using Lebesgue measure. -/
theorem gaussian_mem_hardySobolevTraceClosure {ι : Type*} [Fintype ι] (σ : ι → ℝ) (N : ℕ) :
    ∃ u : hardySobolevTraceClosure σ N volume,
      ∀ i (k : Fin (N + 1)), (u.val i k : ℝ → ℂ) =ᵐ[volume]
        fun y ↦ iteratedDeriv (k : ℕ) (fun z : ℂ ↦ Complex.exp (z ^ 2))
          (verticalPoint (σ i) y) := by sorry

/-- Paper: Definition 9.2.1.1(2), p. 404. The scalar analytic space uses
one line and derivatives of order zero through N, with the Plancherel measure `dy/(2π)`.
Deviation: (9.2.1.3) prints the factor `1/(2π)` outside the square root. The proof of
Theorem 9.2.1.2(2) uses the Plancherel measure `dx/(2π)`, which is what makes the Mellin
transform isometric. The derivative is taken directly on the analytic input. The norm squares
and sums the component norms. -/
abbrev ScalarLineHardySobolev (b : ℝ) (N : ℕ) :=
  hardySobolevTraceClosure (fun _ : Unit ↦ b) N
    (ENNReal.ofReal (1 / (2 * Real.pi)) • volume)

/-- Paper: Definition 9.2.1.1(2), p. 404. The zeroth trace of the Gaussian
has the L² norm in (9.2.1.3) with the Plancherel normalization.
Deviation: Sanity check on the space and its vertical measure. -/
theorem scalarLineHardySobolev_gaussian (b : ℝ) (N : ℕ) :
    let F := fun y : ℝ ↦ Complex.exp (verticalPoint b y ^ 2)
    ∃ u : ScalarLineHardySobolev b N,
      (u.val () 0 : ℝ → ℂ) =ᵐ[volume] F ∧
      ‖u.val () 0‖ = Real.sqrt ((1 / (2 * Real.pi)) * ∫ y, ‖F y‖ ^ 2) := by sorry

/-- Paper: Theorem 9.2.1.2(1), p. 404. On L² the cutoff by a measurable set
is the class of the product with its indicator. -/
def hardySobolevCutoff {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {U : Set A} (hU : MeasurableSet U) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ((Lp.memLp f).indicator hU.nullMeasurableSet).toLp (U.indicator (f : A → ℂ))

/-- Paper: Theorem 9.2.1.2(1), p. 404. The cutoff is a continuous linear
idempotent with closed range, and its representative agrees with the pointwise cutoff.
Deviation: State the operator properties for any measurable set in the weighted L² model. -/
theorem hardySobolevCutoff_spec {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {U : Set A} (hU : MeasurableSet U) :
    ∃ P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ, IsClosed (range P) ∧
      ∀ f, P (P f) = P f ∧ P f = hardySobolevCutoff hU f ∧
        (P f : A → ℂ) =ᵐ[μ] U.indicator f := by sorry

/-- Paper: Theorem 9.2.1.2(1), p. 404. The closure of exponential-decay tests
supported strictly above the cutoff is the range of the cutoff projection.
Deviation: Use logarithmic coordinates. -/
theorem scalarLineSobolev_cutoff_closure (a b : ℝ) (_ha : 1 < a) (N : ℕ) :
    closure {u : ScalarLineSobolev b N | ∃ f : PositiveRealExponentialDecay univ,
      tsupport f.val ⊆ Ioi (-Real.log a) ∧ (u : ℝ → ℂ) =ᵐ[volume] f.val} =
    range (hardySobolevCutoff (μ := volume.withDensity fun x ↦
      ENNReal.ofReal (lineSobolevDensity b N x))
      (U := Ici (-Real.log a)) measurableSet_Ici) := by sorry

/-- Paper: Theorem 9.2.1.2(2), p. 404. The Mellin transform extends to an isometric
isomorphism from the b-line Sobolev space onto the b-line Hardy–Sobolev space.
Deviation: Orders 0 through N on both sides and the Plancherel measure `dy/(2π)`, see
`ScalarLineSobolev` and `ScalarLineHardySobolev`. -/
theorem scalarLineSobolev_mellin (b : ℝ) (N : ℕ) :
    ∃ M : ScalarLineSobolev b N ≃ₗᵢ[ℂ] ScalarLineHardySobolev b N,
      ∀ (f : PositiveRealExponentialDecay univ) (u : ScalarLineSobolev b N),
        (u : ℝ → ℂ) =ᵐ[volume] f.val →
        ∀ k : Fin (N + 1), ((M u).val () k : ℝ → ℂ) =ᵐ[volume]
          fun y ↦ iteratedDeriv (k : ℕ) (mellin (fun t ↦ f.val (Real.log t)))
            (verticalPoint b y) := by sorry

-- TODO(paper-gap): (9.2.1.2) prints orders up to N − 1 and (9.2.1.3) prints 1/(2π)
-- outside the square root; with either as printed Theorem 9.2.1.2(2) is not an isometry.
-- In Theorem 9.2.1.2(3) the Paley–Wiener bound has no stated limiting regime and the
-- printed split square roots fail at nonpositive real parts.

/-- Paper: Theorem 9.2.1.2(3), p. 405. The top row splits a supported L²
class into its bounded-interval part and its right-hand part.
Deviation: State the top row alone for a measurable logarithmic coordinate with no
mass on the splitting level. The analytic row has the gaps noted above. -/
theorem hardySobolevCutoff_exact {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (x : A → ℝ) (hx : Measurable x) (c : ℝ) (_hc : c ≤ 0)
    (_hzero : μ (x ⁻¹' {0}) = 0) :
    let E := Lp ℂ 2 μ
    let S := fun (U : Set ℝ) ↦ {f : E | (f : A → ℂ) =ᵐ[μ] (x ⁻¹' U).indicator (f : A → ℂ)}
    ∃ (L M R : Submodule ℂ E) (i : L →L[ℂ] M) (p : M →L[ℂ] R),
      (L : Set E) = S (Icc c 0) ∧ (M : Set E) = S (Ici c) ∧ (R : Set E) = S (Ici 0) ∧
      (∀ f, (i f).val = f.val) ∧
      (∀ f, (p f).val = hardySobolevCutoff
        (μ := μ) (hx measurableSet_Ici : MeasurableSet (x ⁻¹' Ici 0)) f.val) ∧
      Injective i ∧ IsClosed (range i) ∧ Exact i p ∧ Surjective p ∧ IsOpenMap p := by sorry

-- TODO(paper-gap): Corollary 9.2.1.3 omits the one-sided support hypothesis used
-- in its proof. The uniform Hardy bound at order N also exceeds the printed
-- source order.

/-- Paper: Corollary 9.2.1.4, p. 407. In the left half-plane each indicated derivative
evaluation is bounded on the part supported above the cutoff and is given by the moment integral.
Deviation: State the continuous functional on the supported source, where it extends the
derivative of the test Mellin transform. The printed target identification in 9.2.1.2(2) fails. -/
theorem scalarLineSobolev_cutoff_eval (a b : ℝ) (_ha : 1 < a)
    (N k : ℕ) (_hk : k < N) (z : ℂ) (_hz : z.re < b) :
    ∃ Λ : ScalarLineSobolev b N →L[ℂ] ℂ,
      (∀ (f : ScalarLineSobolev b N), Integrable (fun x : ℝ ↦ (Ici (-Real.log a)).indicator (⇑f) x *
          (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) volume ∧
        Λ f = ∫ x : ℝ, (Ici (-Real.log a)).indicator (⇑f) x *
          (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) ∧
      ∀ (f : PositiveRealExponentialDecay univ) (u : ScalarLineSobolev b N),
        tsupport f.val ⊆ Ioi (-Real.log a) → (u : ℝ → ℂ) =ᵐ[volume] f.val →
        Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z := by sorry

section ModulatedLine

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* ℝ≥0ˣ)

/-- Paper: Theorem 9.2.1.5(1), p. 408. With canonical Haar measure, the
exponential-decay tests complete to the weighted L² on the group.
Deviation: The squared norm sums the squared moments through order N in (9.2.1.19). -/
theorem modulatedLineSobolev_dense (hm : IsModulation m) (_hms : Surjective m)
    (b : ℝ) (N : ℕ) :
    let μ := canonicalModulatedHaar m hm
    ∃ j : ModulatedExponentialDecay m univ →L[ℂ] LineSobolev μ (logModule m) b N,
      Injective j ∧ DenseRange j ∧ ∀ f, (j f : G → ℂ) =ᵐ[μ] f.val := by sorry

/-- Paper: Theorem 9.2.1.5(1), p. 408. On a split modulated group the closed
cutoff range is the closure of the tests with support strictly above the cutoff.
Deviation: The section to all positive reals in the paper entails surjectivity. -/
theorem modulatedLineSobolev_cutoff_closure (hm : IsModulation m) (_hms : Surjective m)
    (a b : ℝ) (_ha : 1 < a) (N : ℕ) :
    let μ := canonicalModulatedHaar m hm
    closure {u : LineSobolev μ (logModule m) b N |
      ∃ f : ModulatedExponentialDecay m univ,
        tsupport f.val ⊆ (logModule m) ⁻¹' Ioi (-Real.log a) ∧
          (u : G → ℂ) =ᵐ[μ] f.val} =
      {u : LineSobolev μ (logModule m) b N |
        (u : G → ℂ) =ᵐ[μ] ((logModule m) ⁻¹' Ici (-Real.log a)).indicator (u : G → ℂ)} := by sorry

/-- Paper: Theorem 9.2.1.5(2), p. 408. In split coordinates the Hilbert tensor
extension takes an elementary product to the kernel factor tensored with its scalar
vertical derivative traces.
Deviation: The kernel L² stays in the physical coordinates of the displayed target.
The source includes order N as printed in (9.2.1.19). The vertical measure is
`dy/(2π)` and both Hilbert norms sum the squared norms through order N. -/
theorem modulatedLineSobolev_mellin (hm : IsModulation m)
    (τ : ℝ≥0ˣ →ₜ* G) (_hτ : RightInverse τ m)
    [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
    (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] (_hμ₁ : μ₁ univ = 1)
    (a b : ℝ) (_ha : 1 < a) (N : ℕ) :
    let μ := canonicalModulatedHaar m hm
    let ν : Measure ℝ := ENNReal.ofReal (1 / (2 * Real.pi)) • volume
    let H := ScalarLineHardySobolev b N
    ∃ M : LineSobolev μ (logModule m) b N ≃ₗᵢ[ℂ]
        UniformSpace.Completion (Lp ℂ 2 μ₁ ⊗[ℂ] H),
      ∀ (g : Lp ℂ 2 μ₁) (f : PositiveRealExponentialDecay univ)
        (u : LineSobolev μ (logModule m) b N),
        (fun p : m.toMonoidHom.ker × ℝ≥0ˣ ↦ u ((p.1 : G) * τ p.2)) =ᵐ[
          μ₁.prod positiveRealHaar] (fun p ↦ g p.1 * f.val (Real.log (p.2.val : ℝ))) →
        ∃ v : H, (∀ k : Fin (N + 1), (v.val () k : ℝ → ℂ) =ᵐ[ν]
            fun y ↦ iteratedDeriv (k : ℕ) (mellin (fun t ↦ f.val (Real.log t)))
              (verticalPoint b y)) ∧ M u = ↑(g ⊗ₜ[ℂ] v) := by sorry

/-- Paper: Theorem 9.2.1.5(2), p. 408, and Equation (9.2.1.25), p. 409.
Taking the isotype coefficient of a line Mellin tensor multiplies the scalar trace
by the kernel Fourier coefficient at the inverse character, as in (D.3.3.14). -/
theorem modulatedLineSobolev_mellin_isotype
    [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
    (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] (_hμ₁ : μ₁ univ = 1)
    (b : ℝ) (N : ℕ) (ω : PontryaginDual m.toMonoidHom.ker) :
    let H := ScalarLineHardySobolev b N
    ∃ coefficient : UniformSpace.Completion (Lp ℂ 2 μ₁ ⊗[ℂ] H) →L[ℂ] H,
      ∀ (g : Lp ℂ 2 μ₁) (v : H),
        coefficient ↑(g ⊗ₜ[ℂ] v) = lcaFourier μ₁ g ω⁻¹ • v := by sorry

-- TODO(paper-gap): Theorem 9.2.1.5(3) switches from the Hilbert tensor product
-- to the projective tensor product in the middle of the bottom row.
-- TODO(paper-gap): Corollary 9.2.1.6 also omits the one-sided support condition.

/-- Paper: Corollary 9.2.1.7, p. 409. Each quasi-character of abscissa below b
gives a continuous moment functional after the cutoff.
Deviation: Use the canonical Haar measure and the intrinsic quasi-character in the
product integral on the supported source. In split coordinates this gives
(9.2.1.25). A change of section changes the coordinates of the same quasi-character. -/
theorem modulatedLineSobolev_cutoff_eval (hm : IsModulation m) (_hms : Surjective m)
    (a b : ℝ) (_ha : 1 < a) (N k : ℕ) (_hk : k < N) (z : ℂ) (_hz : z.re < b)
    (χ : QuasiCharacter G) (_hχ : ∀ g, ‖χ g‖ = 1) :
    let μ := canonicalModulatedHaar m hm
    let E := LineSobolev μ (logModule m) b N
    let U := (logModule m) ⁻¹' Ici (-Real.log a)
    let c := quasiCharacterNormTwist m.toMonoidHom m.continuous χ
    ∃! Λ : E →L[ℂ] ℂ,
      (∀ f : E, Integrable (fun g ↦ U.indicator (⇑f) g *
          (logModule m g : ℂ) ^ k * c z g) μ ∧
        Λ f = ∫ g, U.indicator (⇑f) g * (logModule m g : ℂ) ^ k * c z g ∂μ) ∧
      ∀ (f : ModulatedExponentialDecay m univ) (u : E),
        tsupport f.val ⊆ (logModule m) ⁻¹' Ioi (-Real.log a) →
        (u : G → ℂ) =ᵐ[μ] f.val →
        Λ u = iteratedDeriv k (fun w ↦ modulatedFourierMellin m univ hm μ f.val (c w)) z :=
  by sorry

end ModulatedLine

section Interval

/-- Paper: Proposition 9.2.1.8, p. 410. The density on a compact base interval
uses the larger of the squared endpoint weights and the logarithmic Sobolev factor.
Deviation: The argument is in logarithmic coordinates. -/
def intervalSobolevDensity (a b s x : ℝ) : ℝ :=
  max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) * (1 + x ^ 2) ^ (s / 2)

/-- Paper: Proposition 9.2.1.8, p. 410. At the unit of the positive reals the
density is one for every base interval and degree.
Deviation: Sanity check at logarithmic coordinate zero. -/
theorem intervalSobolevDensity_at_unit (a b s : ℝ) :
    intervalSobolevDensity a b s 0 = 1 := by sorry

/-- Paper: Proposition 9.2.1.8, p. 410. The compact-interval space has the positive
endpoint density, and its dual model uses the reciprocal density.
Deviation: Both spaces are realized as weighted L². The measure and logarithmic
coordinate are explicit, and `dual = true` selects the reciprocal density. -/
abbrev CompactIntervalSobolev {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (logNorm : A → ℝ) (a b s : ℝ) (dual : Bool := false) :=
  Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal
    (if dual then (intervalSobolevDensity a b s (logNorm x))⁻¹
     else intervalSobolevDensity a b s (logNorm x)))

/-- Paper: Definition 9.2.2.9, p. 416, with §10.2.1, p. 439. For the base interval {0} the
weighted measure is the Sobolev measure of Definition 9.1.2.1, so the space is W^{s,2}(G).
Deviation: Sanity check tying the density to §9.1. -/
theorem intervalSobolev_zero_eq_sobolevMeasure {G : Type*} [CommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] (m : G →ₜ* ℝ≥0ˣ) (μ : Measure G) (s : ℝ) :
    (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logModule m x))) =
      sobolevMeasure μ (modulatedSobolevWeight m) s := by sorry

/-- Paper: Proposition 9.2.2.11, p. 417, with Corollary 10.2.2.3, p. 447. For the base interval
{0} the reciprocal-density measure is the Sobolev measure of degree −s of Proposition 9.1.2.5.
Deviation: Sanity check tying the dual density to §9.1. -/
theorem intervalSobolev_zero_dual_eq_sobolevMeasure {G : Type*} [CommGroup G]
    [TopologicalSpace G] [MeasurableSpace G] (m : G →ₜ* ℝ≥0ˣ) (μ : Measure G) (s : ℝ) :
    (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logModule m x))⁻¹) =
      sobolevMeasure μ (modulatedSobolevWeight m) (-s) := by sorry

/-- Paper: Definition 9.2.1.1, p. 404. The b-line density and the density of the base
interval {b} in degree 2N bound each other, so the two spaces have the same elements and
topology.
Deviation: Sanity check comparing the two norms the paper uses for W_b^{2N,2}. -/
theorem lineSobolevDensity_le_interval (b : ℝ) (N : ℕ) (x : ℝ) :
    lineSobolevDensity b N x ≤ intervalSobolevDensity b b (2 * (N : ℝ)) x ∧
      intervalSobolevDensity b b (2 * (N : ℝ)) x ≤ 2 ^ N * lineSobolevDensity b N x := by sorry

-- TODO(paper-gap): The proposed test pairing on all of S_J × S_J can
-- diverge, and S_J need not be contained in the reciprocal-density space.

/-- Paper: Proposition 9.2.1.8, p. 409. The strong dual of the scalar compact-interval
space is represented isometrically by integration against the reciprocal-density space.
Deviation: The duality is stated on the weighted L² spaces. The pairing on all of
S_J × S_J in (9.2.1.27) can diverge. The paper assumes a < b, but §10.2–10.4 apply the
duality to I = [−α, α] with α ≥ 0, so the one-point base is included. -/
theorem scalarIntervalSobolev_dual (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s) :
    ∃! T : StrongDual ℂ (CompactIntervalSobolev volume id a b s) ≃ₗᵢ[ℂ]
        CompactIntervalSobolev volume id a b s true,
      ∀ Λ f, Integrable (fun x ↦ f x * T Λ x) volume ∧
        Λ f = ∫ x, f x * T Λ x := by sorry

-- TODO(paper-gap): The topology generated by individual interior line norms in
-- (9.2.2.2) is strictly coarser than the uniform Hardy norm in (9.2.2.1).

/-- Paper: Definition 9.2.2.1, p. 412. Take the supremum of the endpoint weighted
L² norms over pairs of abscissas in the base interval.
Deviation: The supremum is extended-valued. It can be infinite on the paper's test
space for unbounded I. For an interval, every pair determines a subinterval. -/
def intervalSobolevENorm {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (logNorm : A → ℝ) (I : Set ℝ) (s : ℝ) (f : A → ℂ) : ℝ≥0∞ :=
  ⨆ (a : I) (b : I), eLpNorm f 2
    (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity a b s (logNorm x)))

/-- Paper: Lemma 9.2.2.2(1), p. 412. On a compact base interval the exponential-decay
test space and every open-interval test space containing the base have the same completion.
Deviation: This states the compact case by identifying each dense continuous
inclusion into weighted L², with agreement on function representatives. -/
theorem scalarIntervalSobolev_dense (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s)
    (J : Set ℝ) (_hJ : IsOpen J) (_hInt : OrdConnected J) (_hsub : Icc a b ⊆ J) :
    ∃ j : PositiveRealExponentialDecay J →L[ℂ] CompactIntervalSobolev volume id a b s,
      Injective j ∧ DenseRange j ∧ ∀ f, (j f : ℝ → ℂ) =ᵐ[volume] f.val := by sorry

/-- Paper: Lemma 9.2.2.2(2), p. 412. For a compact base interval the supremum
is attained at the two extreme abscissas and yields the stated weighted integral.
Deviation: Use the logarithmic coordinate and record finiteness before taking the real norm. -/
theorem scalarIntervalSobolev_norm (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s)
    (f : PositiveRealExponentialDecay univ) :
    Integrable (fun x ↦ ‖f.val x‖ ^ 2 * intervalSobolevDensity a b s x) volume ∧
      intervalSobolevENorm volume id (Icc a b) s f.val =
        ENNReal.ofReal (Real.sqrt (∫ x, ‖f.val x‖ ^ 2 * intervalSobolevDensity a b s x)) := by sorry

/-- Paper: Lemma 9.2.2.2(2), p. 412. For even order the endpoint derivative
traces and the compact-interval weighted norm induce the same topology on the tests.
Deviation: Express equivalence by two-sided comparison with the sum of the finitely
many norms in (9.2.2.5). -/
theorem scalarIntervalSobolev_mellin_norm_bounds (a b : ℝ) (_hab : a ≤ b) (N : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ f : PositiveRealExponentialDecay univ,
      let F := mellin (fun t ↦ f.val (Real.log t))
      let w := (intervalSobolevENorm volume id (Icc a b) (2 * (N : ℝ)) f.val).toReal
      let q := fun σ : ℝ ↦ ∑ k ∈ Finset.range (N + 1),
        (eLpNorm (fun y : ℝ ↦ iteratedDeriv k F (verticalPoint σ y)) 2 volume).toReal
      (∀ σ ∈ ({a, b} : Set ℝ), ∀ k ≤ N,
        MemLp (fun y : ℝ ↦ iteratedDeriv k F (verticalPoint σ y)) 2 volume) ∧
        w ≤ C * (q a + q b) ∧ q a + q b ≤ D * w := by sorry

/-- Paper: Lemma 9.2.2.2(3)(a), p. 412. For a right half-line the endpoint
supremum uses the left endpoint and an arbitrary point in the interval.
Deviation: The identity is extended-valued, since the supremum can be infinite. -/
theorem scalarIntervalSobolev_enorm_Ici (a s : ℝ) (_hs : 0 ≤ s)
    (f : PositiveRealExponentialDecay univ) :
    intervalSobolevENorm volume id (Ici a) s f.val =
      ⨆ σ : Ici a, eLpNorm f.val 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a σ s x)) := by sorry

/-- Paper: Lemma 9.2.2.2(3)(b), p. 412. For a left half-line the endpoint
supremum uses an arbitrary point in the interval and the right endpoint.
Deviation: The identity is extended-valued, since the supremum can be infinite. -/
theorem scalarIntervalSobolev_enorm_Iic (b s : ℝ) (_hs : 0 ≤ s)
    (f : PositiveRealExponentialDecay univ) :
    intervalSobolevENorm volume id (Iic b) s f.val =
      ⨆ σ : Iic b, eLpNorm f.val 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity σ b s x)) := by sorry

/-- Paper: Definition 9.2.2.1, p. 412. A nonzero smooth test supported on a
compact subset of the positive logarithmic axis has infinite norm for a right half-line.
Deviation: This is a counterexample to the finiteness of the proposed norm. -/
theorem scalarIntervalSobolev_enorm_Ici_eq_top (a s : ℝ) (_hs : 0 ≤ s)
    (f : PositiveRealExponentialDecay univ) (_hf : f.val ≠ 0)
    (_hcompact : HasCompactSupport f.val) (_hsupport : tsupport f.val ⊆ Ioi 0) :
    intervalSobolevENorm volume id (Ici a) s f.val = ∞ := by sorry

-- TODO(paper-gap): Lemma 9.2.2.2(3) treats the infinite supremum as a finite
-- norm and identifies it with the topology of individual line norms.
-- TODO(paper-gap): Definition 9.2.2.3 does not specify how the derivative index k
-- should depend on s or restrict the sampled abscissas to I. The boundary
-- accumulation requirement alone does not determine the topology in 9.2.2.4(1).
-- TODO(paper-gap): Proposition 9.2.2.4(2) does not supply an interior from which
-- to take boundary values for a singleton interval.

/-- Paper: Proposition 9.2.2.4(2), p. 414. A weighted L² class on a nondegenerate
compact base interval gives a holomorphic Mellin transform on its open strip.
Deviation: State the compact-base assertion in the weighted source model. -/
theorem scalarIntervalSobolev_mellin_holomorphic (a b s : ℝ) (_hab : a < b) (_hs : 0 ≤ s) :
    let E := CompactIntervalSobolev volume id a b s
    let strip := Complex.re ⁻¹' Ioo a b
    let M := fun (f : E) z ↦ ∫ x : ℝ, f x * Complex.exp (z * (x : ℂ))
    (∀ f : E, (∀ z ∈ strip, Integrable (fun x : ℝ ↦ f x * Complex.exp (z * (x : ℂ)))) ∧
      DifferentiableOn ℂ (M f) strip) ∧ Injective (fun f ↦ fun z : strip ↦ M f z.val) := by
  sorry

/-- Paper: Proposition 9.2.2.4(2), p. 414. On either endpoint line of a
nondegenerate compact base interval, the interior Mellin integral has an almost-everywhere
limit, whose inverse Fourier transform has the required Sobolev weight.
Deviation: State the compact-base assertion using the weighted source model. -/
theorem scalarIntervalSobolev_boundary_values (a b s : ℝ) (_hab : a < b) (_hs : 0 ≤ s)
    (c : ℝ) (_hc : c ∈ ({a, b} : Set ℝ)) (f : CompactIntervalSobolev volume id a b s) :
    ∃ u : Lp ℂ 2 (volume : Measure ℝ),
      (∀ᵐ y : ℝ ∂volume, Tendsto
        (fun σ : ℝ ↦ ∫ x : ℝ, f x * Complex.exp (verticalPoint σ y * (x : ℂ)))
        (𝓝[Ioo a b] c) (𝓝 (u y))) ∧
      MemLp ((Lp.fourierTransformₗᵢ ℝ ℂ).symm u : ℝ → ℂ) 2
        (volume.withDensity fun x : ℝ ↦ ENNReal.ofReal ((1 + x ^ 2) ^ (s / 2))) := by sorry

/-- Paper: Proposition 9.2.2.4(2), p. 414. At even degree the almost-everywhere endpoint
limits of the moments from order zero through N are the traces of one element of the
Hardy–Sobolev space on that line.
Deviation: State the compact nondegenerate case in the weighted source model. -/
theorem scalarIntervalSobolev_boundary_traces (a b : ℝ) (_hab : a < b) (N : ℕ)
    (c : ℝ) (_hc : c ∈ ({a, b} : Set ℝ))
    (f : CompactIntervalSobolev volume id a b (2 * (N : ℝ))) :
    ∃ u : ScalarLineHardySobolev c N,
      ∀ k : Fin (N + 1), ∀ᵐ y : ℝ ∂volume, Tendsto
        (fun σ : ℝ ↦ ∫ x : ℝ, f x * (x : ℂ) ^ (k : ℕ) *
          Complex.exp (verticalPoint σ y * (x : ℂ)))
        (𝓝[Ioo a b] c) (𝓝 (u.val () k y)) := by sorry

/-- Paper: Proposition 9.2.2.4(3), p. 414. For even degree and compact base,
Mellin gives a topological linear equivalence with the closure of the two endpoint traces.
Deviation: Use the endpoint topology of Lemma 9.2.2.2(2). The sampling rule of
Definition 9.2.2.3 does not define a sequence-independent topology as stated. -/
theorem scalarIntervalSobolev_mellin_endpoints (a b : ℝ) (_hab : a ≤ b) (N : ℕ)
    (J : Set ℝ) (_hJ : IsOpen J) (_hInt : OrdConnected J) (_hsub : Icc a b ⊆ J) :
    let E := CompactIntervalSobolev volume id a b (2 * (N : ℝ))
    let σ : Bool → ℝ := fun i ↦ if i then b else a
    ∃ M : E ≃L[ℂ] hardySobolevTraceClosure σ N volume,
      ∀ (f : PositiveRealExponentialDecay J) (u : E),
        (u : ℝ → ℂ) =ᵐ[volume] f.val →
        ∀ i (k : Fin (N + 1)), ((M u).val i k : ℝ → ℂ) =ᵐ[volume]
          fun y ↦ iteratedDeriv (k : ℕ) (mellin (fun t ↦ f.val (Real.log t)))
            (verticalPoint (σ i) y) := by sorry

/-- Paper: Corollary 9.2.2.5(1), p. 414. On a compact base interval, every
interior derivative evaluation has a continuous extension given by the Mellin moment.
Deviation: State it in the weighted source model, which also allows nonintegral degree. -/
theorem scalarIntervalSobolev_eval_interior (a b s : ℝ) (_hs : 0 ≤ s)
    (z : ℂ) (_hz : z.re ∈ Ioo a b) (k : ℕ) :
    ∃ Λ : CompactIntervalSobolev volume id a b s →L[ℂ] ℂ,
      ∀ f, Integrable (fun x : ℝ ↦ f x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) volume ∧
        Λ f = ∫ x : ℝ, f x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) := by sorry

/-- Paper: Corollary 9.2.2.5(1), p. 414. The kth complex derivative of the
Mellin integral on the open strip equals the absolutely convergent kth moment.
Deviation: State the compact-base assertion in logarithmic coordinates. -/
theorem scalarIntervalSobolev_iteratedDeriv_mellin (a b s : ℝ) (_hs : 0 ≤ s)
    (f : CompactIntervalSobolev volume id a b s) (k : ℕ) (z : ℂ) (_hz : z.re ∈ Ioo a b) :
    Integrable (fun x : ℝ ↦ f x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) ∧
      iteratedDeriv k (fun w : ℂ ↦ ∫ x : ℝ, f x * Complex.exp (w * (x : ℂ))) z =
        ∫ x : ℝ, f x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) := by sorry

-- TODO(paper-gap): Corollary 9.2.2.5(2) includes the divergent critical case s = 2k + 1.

/-- Paper: Corollary 9.2.2.5(2), p. 414. At either endpoint, a Mellin derivative
evaluation on the unrestricted tests extends continuously exactly when the degree
exceeds twice the derivative order plus one.
Deviation: The compact weighted model includes a singleton base. The critical
equality in the printed bound is excluded. -/
theorem scalarIntervalSobolev_eval_boundary_iff (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s)
    (k : ℕ) (z : ℂ) (_hz : z.re ∈ ({a, b} : Set ℝ)) :
    let E := CompactIntervalSobolev volume id a b s
    (∃ Λ : E →L[ℂ] ℂ, ∀ (f : PositiveRealExponentialDecay univ) (u : E),
      (u : ℝ → ℂ) =ᵐ[volume] f.val →
        Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z) ↔ 2 * (k : ℝ) + 1 < s :=
  by sorry

/-- Paper: Theorem 9.2.2.6(1), p. 415. On a compact base interval of even
degree the supported test closure is the same as the indicator range.
Deviation: Restrict the base to the case where the printed norm is finite on the tests. -/
theorem scalarIntervalSobolev_cutoff_closure (a b A : ℝ) (_hab : a ≤ b) (_hA : 1 < A)
    (N : ℕ) (J : Set ℝ) (_hJ : IsOpen J) (_hInt : OrdConnected J) (_hsub : Icc a b ⊆ J) :
    closure {u : CompactIntervalSobolev volume id a b (2 * (N : ℝ)) |
      ∃ f : PositiveRealExponentialDecay J,
        tsupport f.val ⊆ Ioi (-Real.log A) ∧ (u : ℝ → ℂ) =ᵐ[volume] f.val} =
      {u : CompactIntervalSobolev volume id a b (2 * (N : ℝ)) |
        (u : ℝ → ℂ) =ᵐ[volume] (Ici (-Real.log A)).indicator (u : ℝ → ℂ)} := by sorry

-- TODO(paper-gap): Theorem 9.2.2.6(2) uses the undefined absolute spaces and
-- (9.2.2.28) has the same unspecified growth condition as (9.2.1.7).
-- TODO(paper-gap): Definition 9.2.2.7 refers back to that growth condition.

/-- Paper: Corollary 9.2.2.8(1), p. 415. In the supported space, derivative
evaluations have continuous extensions to all fixed abscissas below the upper endpoint.
Deviation: Use the compact-interval source model and the extension by the indicator. -/
theorem scalarIntervalSobolev_cutoff_eval (a b A : ℝ) (_hab : a ≤ b) (_hA : 1 < A)
    (N k : ℕ) (z : ℂ) (_hz : z.re < b) :
    ∃ Λ : CompactIntervalSobolev volume id a b (2 * (N : ℝ)) →L[ℂ] ℂ,
      ∀ (f : CompactIntervalSobolev volume id a b (2 * (N : ℝ))),
        Integrable (fun x : ℝ ↦ (Ici (-Real.log A)).indicator (⇑f) x *
        (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) volume ∧
        Λ f = ∫ x : ℝ, (Ici (-Real.log A)).indicator (⇑f) x *
          (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) := by sorry

/-- Paper: Corollary 9.2.2.8(1), p. 415. On the open half-plane below the upper
endpoint, the kth derivative of the supported Mellin integral is its kth moment.
Deviation: Use the cutoff in logarithmic coordinates on the compact-base source. -/
theorem scalarIntervalSobolev_cutoff_iteratedDeriv_mellin
    (a b A : ℝ) (_hab : a ≤ b) (_hA : 1 < A) (N k : ℕ)
    (f : CompactIntervalSobolev volume id a b (2 * (N : ℝ))) (z : ℂ) (_hz : z.re < b) :
    let g := (Ici (-Real.log A)).indicator (f : ℝ → ℂ)
    Integrable (fun x : ℝ ↦ g x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) ∧
      iteratedDeriv k (fun w : ℂ ↦ ∫ x : ℝ, g x * Complex.exp (w * (x : ℂ))) z =
        ∫ x : ℝ, g x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) := by sorry

/-- Paper: Corollary 9.2.2.8(2), p. 416. At the upper endpoint a derivative
evaluation of an even-degree supported space is bounded exactly below order N.
Deviation: State bounded extendibility of the evaluation on supported tests in the
compact-interval source model. Here the degree is 2N, so there is no critical equality. -/
theorem scalarIntervalSobolev_cutoff_eval_boundary_iff (a b A : ℝ)
    (_hab : a ≤ b) (_hA : 1 < A) (N k : ℕ) (z : ℂ) (_hz : z.re = b) :
    (∃ Λ : CompactIntervalSobolev volume id a b (2 * (N : ℝ)) →L[ℂ] ℂ,
      ∀ (f : PositiveRealExponentialDecay univ) (u : CompactIntervalSobolev volume id a b (2 * (N : ℝ))),
        tsupport f.val ⊆ Ioi (-Real.log A) → (u : ℝ → ℂ) =ᵐ[volume] f.val →
        Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z) ↔ k < N := by sorry

/-- Paper: Corollary 9.2.2.8(1)–(2), p. 415. On supported scalar tests every order
extends at a distinct lower endpoint. At the upper endpoint the degree must exceed
twice the derivative order plus one.
Deviation: State the endpoint criterion in the compact weighted model for all nonnegative
degrees. The corollary states the even-degree case, with part (2) on p. 416. -/
theorem scalarIntervalSobolev_cutoff_eval_endpoints_iff (a b A s : ℝ)
    (_hab : a ≤ b) (_hA : 1 < A) (_hs : 0 ≤ s) (k : ℕ) (z : ℂ)
    (_hz : z.re ∈ ({a, b} : Set ℝ)) :
    let E := CompactIntervalSobolev volume id a b s
    (∃ Λ : E →L[ℂ] ℂ, ∀ (f : PositiveRealExponentialDecay univ) (u : E),
      tsupport f.val ⊆ Ioi (-Real.log A) → (u : ℝ → ℂ) =ᵐ[volume] f.val →
        Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z) ↔
      z.re < b ∨ 2 * (k : ℝ) + 1 < s := by sorry

end Interval

section ModulatedInterval

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)

local notation "K" => m.toMonoidHom.ker

local instance instMeasurableSpaceDualKerSec2 : MeasurableSpace (PontryaginDual K) := borel _

/-- Paper: Definition 9.2.2.9, p. 416. For a compact base interval the
canonical group-side Sobolev space is weighted L² for the canonical Haar measure.
Deviation: Only compact base intervals give a finite norm on all the stated tests.
Use `intervalSobolevENorm` for the supremum expression on other intervals. -/
abbrev ModulatedIntervalSobolev (a b s : ℝ) :=
  CompactIntervalSobolev (canonicalModulatedHaar m hm) (logModule m) a b s

/-- Paper: Lemma 9.2.2.10(1), p. 416. On a compact base interval each open-interval
test space containing the base embeds continuously and densely in the weighted space.
Deviation: This states the compact case, with the canonical choice of Haar measure. -/
theorem modulatedIntervalSobolev_dense
    (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s) (J : Set ℝ)
    (_hJ : IsOpen J) (_hInt : OrdConnected J) (_hsub : Icc a b ⊆ J) :
    ∃ j : ModulatedExponentialDecay m J →L[ℂ] ModulatedIntervalSobolev m hm a b s,
      Injective j ∧ DenseRange j ∧
      ∀ f, (j f : G → ℂ) =ᵐ[canonicalModulatedHaar m hm] f.val := by sorry

/-- Paper: Lemma 9.2.2.10(1), p. 416. For a compact base interval and an even degree,
pullback to split coordinates followed by the unitary kernel Fourier transform and dual inversion
identifies the space with the completed Hilbert tensor product.
Deviation: The pullback in (9.2.2.32) lands in physical kernel coordinates
before applying the compact Fourier transform at the inverse character, as in (9.2.1.25).
Use the weighted norm of (9.2.2.34). -/
theorem modulatedIntervalSobolev_tensor (τ : ℝ≥0ˣ →ₜ* G) (_hτ : RightInverse τ m)
    [MeasurableSpace K] [BorelSpace K] (μ₁ : Measure K) [μ₁.IsHaarMeasure] (_hμ₁ : μ₁ univ = 1)
    (ν₁ : Measure (PontryaginDual K)) (hν₁ : IsLCAPlancherelMeasure μ₁ ν₁)
    (a b : ℝ) (_hab : a ≤ b) (N : ℕ) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
    letI : BorelSpace (PontryaginDual K) := ⟨rfl⟩
    letI : ν₁.IsHaarMeasure := hν₁.1
    letI : ν₁.Regular := hν₁.2.1
    let U := Classical.choose (lcaFourier_unitary μ₁ ν₁ hν₁).exists
    let invert := Lp.compMeasurePreserving (E := ℂ) (p := 2) Inv.inv
      (Measure.measurePreserving_inv ν₁)
    let E := ModulatedIntervalSobolev m hm a b (2 * (N : ℝ))
    let E₀ := CompactIntervalSobolev volume id a b (2 * (N : ℝ))
    ∃ P : E ≃ₗᵢ[ℂ] UniformSpace.Completion (E₀ ⊗[ℂ] Lp ℂ 2 ν₁),
      ∀ (f : E₀) (g : Lp ℂ 2 μ₁) (u : E),
        (fun p : K × ℝ≥0ˣ ↦ u ((p.1 : G) * τ p.2)) =ᵐ[μ₁.prod positiveRealHaar]
          (fun p ↦ f (Real.log (p.2.val : ℝ)) * g p.1) →
        P u = ↑(f ⊗ₜ[ℂ] invert (U g)) := by sorry

/-- Paper: Lemma 9.2.2.10(1), p. 416. For compact bases and even degrees,
the scalar Mellin transform on split elementary tensors acts by vertical derivative
traces and the Fourier transform acts on the kernel factor.
Deviation: Use the two endpoint traces of Lemma 9.2.2.2(2) and the Hilbert norm
which sums their squared norms. The compact Fourier transform follows the positive
character convention of (9.2.1.25), so the character in `lcaFourier` is inverted. -/
theorem modulatedIntervalSobolev_mellin_endpoints (τ : ℝ≥0ˣ →ₜ* G) (_hτ : RightInverse τ m)
    [MeasurableSpace K] [BorelSpace K] (μ₁ : Measure K) [μ₁.IsHaarMeasure] (_hμ₁ : μ₁ univ = 1)
    (ν₁ : Measure (PontryaginDual K)) (_hν₁ : IsLCAPlancherelMeasure μ₁ ν₁)
    (a b : ℝ) (_hab : a ≤ b) (N : ℕ) :
    let E := ModulatedIntervalSobolev m hm a b (2 * (N : ℝ))
    let σ : Bool → ℝ := fun i ↦ if i then b else a
    let H := hardySobolevTraceClosure σ N volume
    ∃ M : E ≃L[ℂ] UniformSpace.Completion (H ⊗[ℂ] Lp ℂ 2 ν₁),
      ∀ (f : PositiveRealExponentialDecay univ) (g : Lp ℂ 2 μ₁) (u : E),
        Integrable (g : K → ℂ) μ₁ →
        (fun p : K × ℝ≥0ˣ ↦ u ((p.1 : G) * τ p.2)) =ᵐ[μ₁.prod positiveRealHaar]
          (fun p ↦ f.val (Real.log (p.2.val : ℝ)) * g p.1) →
        ∃ (v : H) (w : Lp ℂ 2 ν₁),
          (∀ i (k : Fin (N + 1)), (v.val i k : ℝ → ℂ) =ᵐ[volume]
            fun y ↦ iteratedDeriv (k : ℕ) (mellin (fun t ↦ f.val (Real.log t)))
              (verticalPoint (σ i) y)) ∧
          (w : PontryaginDual K → ℂ) =ᵐ[ν₁] (fun χ ↦ lcaFourier μ₁ g χ⁻¹) ∧
          M u = ↑(v ⊗ₜ[ℂ] w) := by sorry

/-- Paper: Lemma 9.2.2.10(2), p. 417. For a compact base the norm of a completed
element is the square root of the integral with the maximum endpoint weight.
Deviation: The formula holds for the L² representative in the completed space. -/
theorem modulatedIntervalSobolev_norm (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s)
    (f : ModulatedIntervalSobolev m hm a b s) :
    let μ := canonicalModulatedHaar m hm
    let integrand := fun g ↦ ‖f g‖ ^ 2 * intervalSobolevDensity a b s (logModule m g)
    Integrable integrand μ ∧ ‖f‖ = Real.sqrt (∫ g, integrand g ∂μ) ∧
      intervalSobolevENorm μ (logModule m) (Icc a b) s (⇑f) = ENNReal.ofReal ‖f‖ := by sorry

/-- Paper: Lemma 9.2.2.10(3)(a), p. 417. The right half-line supremum can
be indexed using the left endpoint and one varying abscissa.
Deviation: Use extended values and read `t` in (9.2.2.35) as the module of g. -/
theorem modulatedIntervalSobolev_enorm_Ici (a s : ℝ) (_hs : 0 ≤ s)
    (f : ModulatedExponentialDecay m univ) :
    let μ := canonicalModulatedHaar m hm
    intervalSobolevENorm μ (logModule m) (Ici a) s f.val =
      ⨆ σ : Ici a, eLpNorm f.val 2 (μ.withDensity fun g ↦
        ENNReal.ofReal (intervalSobolevDensity a σ s (logModule m g))) := by sorry

/-- Paper: Lemma 9.2.2.10(3)(b), p. 417. The left half-line supremum can
be indexed using one varying abscissa and the right endpoint.
Deviation: Use extended values for the supremum in (9.2.2.36). -/
theorem modulatedIntervalSobolev_enorm_Iic (b s : ℝ) (_hs : 0 ≤ s)
    (f : ModulatedExponentialDecay m univ) :
    let μ := canonicalModulatedHaar m hm
    intervalSobolevENorm μ (logModule m) (Iic b) s f.val =
      ⨆ σ : Iic b, eLpNorm f.val 2 (μ.withDensity fun g ↦
        ENNReal.ofReal (intervalSobolevDensity σ b s (logModule m g))) := by sorry

-- TODO(paper-gap): As in Proposition 9.2.1.8, the test pairing and the
-- reciprocal-density norm are not defined on all the stated inputs.

/-- Paper: Proposition 9.2.2.11, p. 417. The weighted space pairs with the
reciprocal-density space via the unweighted integral and represents its strong dual.
Deviation: Use the Haar measure from the proposition on both sides. The test pairing
on all of S_J × S_J and the reciprocal-norm completion of all of S_J can fail. The paper
assumes a < b, but §10.2–10.4 apply (9.2.2.42) to I = [−α, α] with α ≥ 0, so the one-point
base is included. -/
theorem modulatedIntervalSobolev_dual (_hm : IsModulation m)
    (μ : Measure G) [μ.IsHaarMeasure] (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s) :
    ∃! T : StrongDual ℂ (CompactIntervalSobolev μ (logModule m) a b s) ≃ₗᵢ[ℂ]
        CompactIntervalSobolev μ (logModule m) a b s true,
      ∀ Λ f, Integrable (fun g ↦ f g * T Λ g) μ ∧
        Λ f = ∫ g, f g * T Λ g ∂μ := by sorry

-- TODO(paper-gap): Corollary 9.2.2.12(1) omits the kernel character in the integral
-- for a general isotype and uses m rather than k for the power of the logarithm.

/-- Paper: Corollary 9.2.2.12(1), p. 418. Each isotype has a bounded
interior derivative evaluation on the supported compact-interval space.
Deviation: Use the weighted source model and the intrinsic quasi-character for
the chosen isotype. The printed formula corresponds to the trivial character. -/
theorem modulatedIntervalSobolev_cutoff_eval (a b A s : ℝ)
    (_hA : 1 < A) (_hs : 0 ≤ s) (z : ℂ) (_hz : z.re ∈ Ioo a b) (k : ℕ)
    (χ : QuasiCharacter G) (_hχ : ∀ g, ‖χ g‖ = 1) :
    let μ := canonicalModulatedHaar m hm
    let E := ModulatedIntervalSobolev m hm a b s
    let U := (logModule m) ⁻¹' Ici (-Real.log A)
    let c := quasiCharacterNormTwist m.toMonoidHom m.continuous χ z
    ∃! Λ : E →L[ℂ] ℂ,
      ∀ f : E, Integrable (fun g ↦ U.indicator (⇑f) g * (logModule m g : ℂ) ^ k * c g) μ ∧
        Λ f = ∫ g, U.indicator (⇑f) g * (logModule m g : ℂ) ^ k * c g ∂μ := by sorry

/-- Paper: Corollary 9.2.2.12(1), p. 418. In the norm-twist coordinate of a unitary
quasi-character, the kth derivative of the cutoff Mellin integral equals its kth moment.
Deviation: The intrinsic quasi-character includes the character missing in (9.2.2.43),
and the cutoff gives convergence throughout the open half-plane below the upper endpoint. -/
theorem modulatedIntervalSobolev_cutoff_iteratedDeriv_mellin (a b A s : ℝ)
    (_hab : a ≤ b) (_hA : 1 < A) (_hs : 0 ≤ s) (k : ℕ)
    (f : ModulatedIntervalSobolev m hm a b s) (z : ℂ) (_hz : z.re < b)
    (χ : QuasiCharacter G) (_hχ : ∀ g, ‖χ g‖ = 1) :
    let μ := canonicalModulatedHaar m hm
    let u := ((logModule m) ⁻¹' Ici (-Real.log A)).indicator (f : G → ℂ)
    let c := quasiCharacterNormTwist m.toMonoidHom m.continuous χ
    Integrable (fun g ↦ u g * (logModule m g : ℂ) ^ k * c z g) μ ∧
      iteratedDeriv k (fun w : ℂ ↦ ∫ g, u g * c w g ∂μ) z =
        ∫ g, u g * (logModule m g : ℂ) ^ k * c z g ∂μ := by sorry

-- TODO(paper-gap): Corollary 9.2.2.12(2) includes the divergent critical case
-- s = 2k + 1 at the upper endpoint, even for the trivial kernel character.

/-- Paper: Corollary 9.2.2.12(2), p. 418. A Mellin derivative evaluation in any
isotype extends from supported tests at the endpoints of the compact base.
Deviation: At the upper endpoint the condition is strict. At a distinct lower
endpoint the cutoff allows all orders. The modulation is onto as in §9.2. -/
theorem modulatedIntervalSobolev_cutoff_eval_endpoints_iff (_hms : Surjective m)
    (a b A s : ℝ) (_hab : a ≤ b) (_hA : 1 < A) (_hs : 0 ≤ s) (k : ℕ)
    (z : ℂ) (_hz : z.re ∈ ({a, b} : Set ℝ))
    (χ : QuasiCharacter G) (_hχ : ∀ g, ‖χ g‖ = 1) :
    let μ := canonicalModulatedHaar m hm
    let E := ModulatedIntervalSobolev m hm a b s
    let c := quasiCharacterNormTwist m.toMonoidHom m.continuous χ
    (∃ Λ : E →L[ℂ] ℂ, ∀ (f : ModulatedExponentialDecay m univ) (u : E),
      tsupport f.val ⊆ (logModule m) ⁻¹' Ioi (-Real.log A) → (u : G → ℂ) =ᵐ[μ] f.val →
        Λ u = iteratedDeriv k (fun w ↦ modulatedFourierMellin m univ hm μ f.val (c w)) z) ↔
      z.re < b ∨ 2 * (k : ℝ) + 1 < s := by sorry

/-- Paper: Theorem 9.2.2.13(1), p. 418. For compact bases and surjective module,
the support-restricted tests are dense in the indicator range.
Deviation: State the range as the fixed points of the cutoff on representatives.
A discrete modulation can have positive Haar mass at the cutoff itself. -/
theorem modulatedIntervalSobolev_cutoff_closure (_hms : Surjective m) (a b A s : ℝ)
    (_hab : a ≤ b) (_hA : 1 < A) (_hs : 0 ≤ s) :
    let μ := canonicalModulatedHaar m hm
    let E := ModulatedIntervalSobolev m hm a b s
    closure {u : E | ∃ f : ModulatedExponentialDecay m univ,
      tsupport f.val ⊆ (logModule m) ⁻¹' Ioi (-Real.log A) ∧
        (u : G → ℂ) =ᵐ[μ] f.val} =
      {u : E | (u : G → ℂ) =ᵐ[μ] ((logModule m) ⁻¹' Ici (-Real.log A)).indicator (u : G → ℂ)} :=
  by sorry

-- TODO(paper-gap): Theorem 9.2.2.13(2) uses the unspecified analytic space of
-- Definition 9.2.2.3. The cited Lemma 9.2.2.10(1) treats only even degrees.
-- TODO(paper-gap): Theorem 9.2.2.13(3) gives the unrestricted tensor space as
-- right target even though the induced Mellin map on that arrow has one-sided source.

end ModulatedInterval

end RiemannMasullo
