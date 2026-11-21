module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3a
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Sobolev spaces on locally compact abelian groups

Masullo, §9.1, pp. 395–403.
-/

@[expose] public noncomputable section

open MeasureTheory Set Topology TopologicalSpace
open scoped CompactlySupported ENNReal NNReal ZeroAtInfty

namespace RiemannMasullo

local instance sobolevDualMeasurableSpace {A : Type*} [CommGroup A] [TopologicalSpace A] :
    MeasurableSpace (PontryaginDual A) := borel _

section Weighted

variable {A : Type*}

/-- Paper: Definition 9.1.1.1, p. 396. On the group where the weight is evaluated,
a Sobolev weight is nonnegative, continuous, and subadditive up to one positive constant.
Deviation: The argument group is explicit. For the paper's weight on G it is the dual of G. -/
def IsSobolevWeight [Mul A] [TopologicalSpace A] (w : A → ℝ≥0) : Prop :=
  Continuous w ∧ ∃ C : ℝ≥0, 0 < C ∧ ∀ x y, w (x * y) ≤ C * (w x + w y)

/-- Paper: Definition 9.1.1.1, p. 396. Every constant nonnegative weight is a Sobolev weight.
Deviation: Sanity check on the weight condition. -/
theorem isSobolevWeight_const [Mul A] [TopologicalSpace A] (c : ℝ≥0) :
    IsSobolevWeight (fun _ : A ↦ c) := by sorry

/-- Paper: Definition 9.1.1.1, p. 396. The measure for degree s has density
`(1 + w²)^(s/2)` with respect to the measure on the group carrying the weight. -/
def sobolevMeasure [MeasurableSpace A] (ν : Measure A) (w : A → ℝ≥0) (s : ℝ) : Measure A :=
  ν.withDensity fun x ↦ ENNReal.ofReal ((1 + (w x : ℝ) ^ 2) ^ (s / 2))

/-- Paper: Definition 9.1.1.1, p. 396. At degree zero, the weighted measure is the original
measure.
Deviation: Sanity check on the normalization in (9.1.1.3). -/
theorem sobolevMeasure_zero [MeasurableSpace A] (ν : Measure A) (w : A → ℝ≥0) :
    sobolevMeasure ν w 0 = ν := by sorry

-- TODO(paper-gap): The input to the completion is written C_c(Ĝ) but its norm takes a
-- Fourier transform and still evaluates on Ĝ. Use the Fourier-side interpretation below.

/-- Paper: Definition 9.1.1.1, p. 396. The Sobolev space consists of square-integrable
classes for the weighted measure. Use the dual group and the Plancherel measure for H^s_w(G).
Deviation: The completed space is realized directly as the weighted L² from Lemma 9.1.1.2.
An element in this model already represents the Fourier-side function. -/
abbrev WeightedSobolev [MeasurableSpace A] (ν : Measure A) (w : A → ℝ≥0) (s : ℝ) :=
  Lp ℂ 2 (sobolevMeasure ν w s)

/-- Paper: Definition 9.1.1.1, p. 396. In the weighted L² model the norm is the square root
of the integral of the squared modulus times the prescribed density.
Deviation: Sanity check on (9.1.1.3), written directly for Fourier-side representatives. -/
theorem weightedSobolev_norm [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A]
    (ν : Measure A) {w : A → ℝ≥0} (hw : Continuous w) (s : ℝ)
    (f : WeightedSobolev ν w s) :
    Integrable (fun x ↦ ‖f x‖ ^ 2 * (1 + (w x : ℝ) ^ 2) ^ (s / 2)) ν ∧
    ‖f‖ = Real.sqrt (∫ x, ‖f x‖ ^ 2 * (1 + (w x : ℝ) ^ 2) ^ (s / 2) ∂ν) := by sorry

end Weighted

section LCA

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
  (ν : Measure (PontryaginDual G)) {w : PontryaginDual G → ℝ≥0} {s : ℝ}

/-- Paper: Definition 9.1.1.1, p. 396. Continuous compactly supported functions embed as a
dense complex-linear subspace of the Fourier-side Sobolev space.
Deviation: The norm in (9.1.1.3) is applied to the test functions as Fourier-side data. -/
theorem weightedSobolev_compactSupport_dense (_hν : IsLCAPlancherelMeasure μ ν)
    (_hw : IsSobolevWeight w) :
    ∃ J : (PontryaginDual G →C_c ℂ) →ₗ[ℂ] WeightedSobolev ν w s,
      DenseRange J ∧ Function.Injective J ∧
        ∀ f, (J f : PontryaginDual G → ℂ) =ᵐ[ν] (f : PontryaginDual G → ℂ) := by sorry

/-- Paper: Lemma 9.1.1.2, p. 396. The weighted L² space is complete with its
Mathlib L² inner product. -/
theorem weightedSobolev_complete (_hν : IsLCAPlancherelMeasure μ ν) (_hw : IsSobolevWeight w) :
    CompleteSpace (WeightedSobolev ν w s) := by sorry

omit [μ.Regular] in
/-- Paper: Lemma 9.1.1.2, p. 396. For a second-countable group, the Sobolev Hilbert
space is separable. -/
theorem weightedSobolev_separable [SecondCountableTopology G]
    (_hν : IsLCAPlancherelMeasure μ ν) (_hw : IsSobolevWeight w) :
    SeparableSpace (WeightedSobolev ν w s) := by sorry

/-- Paper: Proposition 9.1.1.3(1), p. 396. In nonnegative degree the Sobolev space
includes continuously and contractively into Haar L² via inverse Plancherel. -/
theorem weightedSobolev_toL2 (hν : IsLCAPlancherelMeasure μ ν)
    (_hw : IsSobolevWeight w) (_hs : 0 ≤ s) :
    let U := Classical.choose (lcaFourier_unitary μ ν hν).exists
    ∃ J : WeightedSobolev ν w s →L[ℂ] Lp ℂ 2 μ,
      Function.Injective J ∧ ‖J‖ ≤ 1 ∧
        ∀ f, (U (J f) : PontryaginDual G → ℂ) =ᵐ[ν] (f : PontryaginDual G → ℂ) := by sorry

-- TODO(paper-gap): In (9.1.1.6) the lower-degree input is printed where the inclusion
-- requires a higher-degree input. Elements of the lower-degree space can have infinite
-- higher-degree weighted integral.

/-- Paper: Proposition 9.1.1.3(2), p. 397. For s' > s ≥ 0, the inclusion from
degree s' to degree s is contractive and preserves the Fourier-side representative.
Deviation: The variable in (9.1.1.6) ranges over the source of the displayed inclusion. -/
theorem weightedSobolev_ofHigherDegree (_hν : IsLCAPlancherelMeasure μ ν)
    (_hw : IsSobolevWeight w) (_hs : 0 ≤ s) {s' : ℝ} (_hss' : s < s') :
    ∃ J : WeightedSobolev ν w s' →L[ℂ] WeightedSobolev ν w s,
      Function.Injective J ∧ ‖J‖ ≤ 1 ∧
        ∀ f, (J f : PontryaginDual G → ℂ) =ᵐ[ν] (f : PontryaginDual G → ℂ) := by sorry

/-- Paper: Proposition 9.1.1.3(3), p. 397. When the reciprocal density is integrable,
the inverse Plancherel class of each Sobolev element has a unique representative
vanishing at infinity. The representative map is a bounded linear injection. -/
theorem weightedSobolev_toZeroAtInfty (hν : IsLCAPlancherelMeasure μ ν)
    (_hw : IsSobolevWeight w) (_hs : 0 ≤ s)
    (_h : Integrable (fun χ ↦ (1 + (w χ : ℝ) ^ 2) ^ (-s / 2)) ν) :
    let U := Classical.choose (lcaFourier_unitary μ ν hν).exists
    ∃ (J : WeightedSobolev ν w s →L[ℂ] Lp ℂ 2 μ)
      (E : WeightedSobolev ν w s →L[ℂ] C₀(G, ℂ)) (C : ℝ),
      (∀ f, (U (J f) : PontryaginDual G → ℂ) =ᵐ[ν] (f : PontryaginDual G → ℂ)) ∧
      Function.Injective E ∧ 0 < C ∧ ‖E‖ ≤ C ∧
      ∀ f g, g = E f ↔ (g : G → ℂ) =ᵐ[μ] (J f : G → ℂ) := by sorry

-- TODO(paper-gap): The bound (9.1.1.15) places an extra square root on each L² norm.

/-- Paper: Lemma 9.1.1.5, p. 397. The unweighted integral of the pointwise product
pairs opposite degrees. It represents every continuous linear functional uniquely and
isometrically by an element in the opposite degree. -/
theorem weightedSobolev_dual (_hν : IsLCAPlancherelMeasure μ ν)
    (_hw : IsSobolevWeight w) (_hs : 0 ≤ s) :
    ∃! T : StrongDual ℂ (WeightedSobolev ν w s) ≃ₗᵢ[ℂ] WeightedSobolev ν w (-s),
      ∀ Λ f, Integrable (fun χ ↦ f χ * T Λ χ) ν ∧ Λ f = ∫ χ, f χ * T Λ χ ∂ν := by sorry

end LCA

section Modulated

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
  (m : G →ₜ* ℝ≥0ˣ)

/-- Paper: (9.1.2.1), p. 399. The logarithmic Sobolev weight is the absolute
value of the logarithm of the module. -/
def modulatedSobolevWeight (x : G) : ℝ≥0 :=
  ⟨|Real.log ((m x).val : ℝ)|, abs_nonneg _⟩

/-- Paper: (9.1.2.1), p. 399. At an element of module exp(t), the weight is |t|.
Deviation: Sanity check in logarithmic coordinates. -/
theorem modulatedSobolevWeight_of_exp {x : G} (t : ℝ)
    (hx : ((m x).val : ℝ) = Real.exp t) :
    (modulatedSobolevWeight m x : ℝ) = |t| := by sorry

/-- Paper: (9.1.2.1), p. 399. The logarithmic weight satisfies the Sobolev
weight condition with subadditivity constant one. -/
theorem modulatedSobolevWeight_subadditive :
    Continuous (modulatedSobolevWeight m) ∧
      ∀ x y, modulatedSobolevWeight m (x * y) ≤
        modulatedSobolevWeight m x + modulatedSobolevWeight m y := by
  have hne (x : G) : ((m x).val : ℝ) ≠ 0 :=
    NNReal.coe_ne_zero.mpr (m x).ne_zero
  constructor
  · have hm : Continuous (fun x ↦ ((m x).val : ℝ)) :=
      NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
    exact ((hm.log hne).abs).subtype_mk _
  · intro x y
    change |Real.log ((m (x * y)).val : ℝ)| ≤
      |Real.log ((m x).val : ℝ)| + |Real.log ((m y).val : ℝ)|
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul (hne x) (hne y)]
    exact abs_add_le _ _

variable [MeasurableSpace G] (μ : Measure G)

/-- Paper: Definition 9.1.2.1, p. 399. The modulated Sobolev space is square-integrable
with the logarithmic weight on the original group, as in (9.1.2.3).
Deviation: Use the direct weighted L² realization in every real degree. The paper introduces
nonnegative degrees here and uses negative degrees in Proposition 9.1.2.5. -/
abbrev ModulatedSobolev (s : ℝ) :=
  WeightedSobolev μ (modulatedSobolevWeight m) s

/-- Paper: Definition 9.1.2.1, p. 399. The norm on the modulated Sobolev space is the weighted
integral norm on the original group.
Deviation: Sanity check for the direct model and its extension to real degrees. -/
theorem modulatedSobolev_norm [BorelSpace G] (s : ℝ) (f : ModulatedSobolev m μ s) :
    Integrable (fun x ↦ ‖f x‖ ^ 2 * (1 + |Real.log ((m x).val : ℝ)| ^ 2) ^ (s / 2)) μ ∧
    ‖f‖ = Real.sqrt (∫ x, ‖f x‖ ^ 2 * (1 + |Real.log ((m x).val : ℝ)| ^ 2) ^ (s / 2) ∂μ) :=
  by sorry

-- Definition D.2.1.1, p. 793, defines modulated groups for second-countable `G`, and the
-- structure lemmas for `IsModulation` assume it; the recall on p. 399 omits the word.
variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace G] [μ.IsHaarMeasure]

variable (ν : Measure (PontryaginDual G))

/-- Paper: Definition 9.1.2.1, p. 399. Evaluation into the bidual identifies the
group-side Sobolev space with H^s_w of the dual group. The pushed-forward Haar measure
on the bidual is the Plancherel measure of the dual group. -/
theorem modulatedSobolev_bidual (_hm : IsModulation m) (_hsurj : Function.Surjective m)
    (_hν : IsLCAPlancherelMeasure μ ν) (s : ℝ) :
    ∃ b : G ≃ₜ* PontryaginDual (PontryaginDual G),
      (∀ x χ, b x χ = χ x) ∧
      IsLCAPlancherelMeasure ν (μ.map b) ∧
      ∃ e : ModulatedSobolev m μ s ≃ₗᵢ[ℂ]
          WeightedSobolev (μ.map b) (modulatedSobolevWeight m ∘ b.symm) s,
        ∀ f, (e f : PontryaginDual (PontryaginDual G) → ℂ) =ᵐ[μ.map b] fun χ ↦ f (b.symm χ) :=
  by sorry

-- TODO(paper-gap): (9.1.2.9) compares a squared norm on the left with homogeneous
-- expressions of degree one on the right. In (9.1.2.11) the sign of the exponent
-- for the character and the sign for its conjugate are printed the same way.

/-- Paper: Lemma 9.1.2.2, p. 400. At degree 2N the norms of the Fourier derivatives
up to order N for any algebra generator induce the Sobolev topology.
Deviation: The displayed C_F is read as G, as in the lemma's hypotheses. On completion
the derivatives are continuous L²-valued extensions from smooth compactly supported functions. -/
theorem modulatedSobolev_fourierDeriv_topology (_hm : IsModulation m)
    (_hsurj : Function.Surjective m) (_hν : IsLCAPlancherelMeasure μ ν) (N : ℕ)
    (D : bruhatDiffAlgebra (PontryaginDual G)) (_hD : Algebra.adjoin ℂ {D} = ⊤) :
    let E := ModulatedSobolev m μ (2 * (N : ℝ))
    ∃ A : Fin (N + 1) → (E →L[ℂ] Lp ℂ 2 ν),
      (∀ (f : G →C_c ℂ), IsBruhatSmooth (f : G → ℂ) →
        ∃ (u : E) (F : bruhatSmoothSubmodule (G := PontryaginDual G)),
          (u : G → ℂ) =ᵐ[μ] (f : G → ℂ) ∧ F.val = lcaFourier μ f ∧
          ∀ k, (A k u : PontryaginDual G → ℂ) =ᵐ[ν] ((D ^ (k : ℕ)).val F).val) ∧
      IsEmbedding (fun f : E ↦ fun k ↦ A k f) := by sorry

-- TODO(paper-gap): In Remark 9.1.2.3 the ordinary derivatives are on the Fourier side.
-- The stated generalization to all locally compact abelian groups also needs a weight.

/-- Paper: Lemma 9.1.2.4, p. 402. The reciprocal logarithmic Sobolev
density is integrable exactly above degree one. -/
theorem modulatedSobolev_reciprocal_integrable_iff (_hm : IsModulation m)
    (_hsurj : Function.Surjective m) {s : ℝ} (_hs : 0 ≤ s) :
    Integrable (fun x ↦ (1 + |Real.log ((m x).val : ℝ)| ^ 2) ^ (-s / 2)) μ ↔ 1 < s :=
  by sorry

/-- Paper: Proposition 9.1.2.5, p. 402. The unweighted product pairing on the group
identifies the strong dual isometrically with the space of opposite degree. -/
theorem modulatedSobolev_dual (_hm : IsModulation m) (_hsurj : Function.Surjective m)
    {s : ℝ} (_hs : 0 ≤ s) :
    ∃! T : StrongDual ℂ (ModulatedSobolev m μ s) ≃ₗᵢ[ℂ] ModulatedSobolev m μ (-s),
      ∀ Λ f, Integrable (fun x ↦ f x * T Λ x) μ ∧ Λ f = ∫ x, f x * T Λ x ∂μ := by sorry

-- TODO(paper-gap): The simultaneous invariance described in the proof uses opposite
-- parameters for left and right translations under the transpose convention.

/-- Paper: Proposition 9.1.2.5, p. 402. The dual isometry intertwines the transpose
of left translation with right translation. Both translations are jointly continuous.
The transpose is precomposition as in (4.3.3.3). -/
theorem modulatedSobolev_dual_equivariant (hm : IsModulation m)
    (hsurj : Function.Surjective m) {s : ℝ} (hs : 0 ≤ s) :
    let E := ModulatedSobolev m μ s
    let F := ModulatedSobolev m μ (-s)
    let T := Classical.choose (modulatedSobolev_dual m μ hm hsurj hs).exists
    ∃ (L : G →* (E →L[ℂ] E)) (R : G →* (F →L[ℂ] F)),
      Continuous (fun p : G × E ↦ L p.1 p.2) ∧
      Continuous (fun p : G × F ↦ R p.1 p.2) ∧
      (∀ g f, (L g f : G → ℂ) =ᵐ[μ] fun x ↦ f (g⁻¹ * x)) ∧
      (∀ g u, (R g u : G → ℂ) =ᵐ[μ] fun x ↦ u (x * g)) ∧
      ∀ g Λ, T (Λ.comp (L g)) = R g (T Λ) := by sorry

-- TODO(paper-gap): In (9.1.2.15) the range of m is unspecified. For nonintegral
-- orders the signed logarithm can be negative and no convention for its power is given.

/-- Paper: Proposition 9.1.2.5, p. 402. A unitary module character times a natural
power of the logarithm lies in degree −s exactly when the power is less than (s−1)/2.
Deviation: The exponent in (9.1.2.15) is interpreted as a natural number, as for the
logarithmic derivatives in (9.2.1.16). -/
theorem modulatedSobolev_logPower_mem_iff (_hm : IsModulation m) (_hsurj : Function.Surjective m)
    {s : ℝ} (_hs : 1 < s) (t : ℝ) (k : ℕ) :
    MemLp (fun x ↦
      Complex.exp (Complex.I * (t : ℂ) * (Real.log ((m x).val : ℝ) : ℂ)) *
        (Real.log ((m x).val : ℝ) : ℂ) ^ k) 2
      (sobolevMeasure μ (modulatedSobolevWeight m) (-s)) ↔ (k : ℝ) < (s - 1) / 2 := by sorry

/-- Paper: Proposition 9.1.2.6, p. 403. Above degree one, each modulated Sobolev class
is absolutely integrable and the canonical inclusion into Haar L¹ is bounded. -/
theorem modulatedSobolev_toL1 (_hm : IsModulation m) (_hsurj : Function.Surjective m)
    {s : ℝ} (_hs : 1 < s) :
    ∃ (J : ModulatedSobolev m μ s →L[ℂ] Lp ℂ 1 μ) (C : ℝ),
      Function.Injective J ∧ 0 < C ∧ ‖J‖ ≤ C ∧
      ∀ f : ModulatedSobolev m μ s,
        Integrable (f : G → ℂ) μ ∧ (J f : G → ℂ) =ᵐ[μ] (f : G → ℂ) := by sorry

end Modulated

end RiemannMasullo
